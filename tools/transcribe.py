#!/usr/bin/env python3
"""Transcribe photographed proof templates into pipe format.

    export ANTHROPIC_API_KEY=sk-...
    python3 tools/transcribe.py --images eval/images --out eval/pred
    stack exec eval-score -- eval/truth eval/pred

Reads each image, asks a vision model to read the table, and writes
<out>/<stem>.pipe. Whole-page transcription is deliberate: measurement on this
corpus showed a vision model reading the full photograph scores 100% on the
dependency, line-number and formula columns, including deeply nested formulas
over eighteen rows, so cropping the table into cells would be machinery aimed
at a problem we do not have. The errors are concentrated in the justification
column, which is why that column is pinned to a closed vocabulary in the
prompt below.

No API key is needed to exercise the plumbing:

    python3 tools/transcribe.py --images eval/images --out /tmp/p --mock resp.txt

which feeds a canned model reply through the same parsing and writing path.
"""

import argparse
import base64
import io
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

API_URL = "https://api.anthropic.com/v1/messages"
API_VERSION = "2023-06-01"
DEFAULT_MODEL = "claude-sonnet-5"

# Anthropic resizes anything larger; doing it here keeps the request small.
MAX_EDGE = 1568

# The closed vocabulary the justification column is allowed to use. Keep in
# step with ruleAliases in src/PipeParse.hs.
RULE_FORMS = """\
  A
  <m>,<n> MP        <m>,<n> MT        <m> DN            <m>,<n> CP
  <m>,<n> ∧I        <m> ∧E            <m> ∨I            <d>,<a1>,<c1>,<a2>,<c2> ∨E
  <m>,<n> RAA       <m> ∀E            <m> ∀I            <m> ∃I
  <m>,<a>,<n> ∃E    <m>,<n> ↔I        <m>,<n> ↔E        <m> QN
  =I                <m>,<n> =E        LEM               prop taut"""

PROMPT = f"""\
This is a photograph of a handwritten natural-deduction proof on a printed \
template. The page may be rotated by 90 degrees.

The template is a four-column table: Depends | (Line) | Formula | \
Justification. The line numbers (1) to (19) are pre-printed, so most rows are \
blank. Transcribe only the rows the student has written in.

Output one line per filled row, in exactly this format:

  <depends>|<line>|<formula>|<justification>

depends
    Comma-separated line numbers, e.g. 1,2 — or empty if the cell is blank.
    An empty dependency cell is meaningful; leave the field empty, do not omit it.

line
    The pre-printed line number, digits only.

formula
    Use the symbols ¬ ∧ ∨ → ↔ ∀ ∃ =. Predicates are capital letters and their
    terms are lower-case letters written straight after them: Fa, Fx, Rab.
    Reproduce the parentheses as written.

justification
    Exactly one of these forms, where <m>, <n> are line numbers:

{RULE_FORMS}

    The page may use variant spellings — cP for CP, UI or uI for ∀I, EI for
    ∃I, ANDI for ∧I, v for ∨. Map those to the canonical forms above. That is
    the only normalising you should do.

TRANSCRIBE EXACTLY WHAT IS WRITTEN, INCLUDING MISTAKES. This transcription is
fed to a proof checker that reports errors back to the student. If a
justification looks wrong for the formula on that row, or a dependency set
looks incorrect, write down what is on the page regardless. Do not correct,
complete, or tidy up the proof. A transcription that silently repairs an error
is worse than useless, because the student is then told their mistake is fine.

If a cell is genuinely illegible, write ??? in it rather than guessing.

Output only the pipe lines. No commentary, no code fence, no header row.
"""


def encode_image(path: Path) -> tuple[str, str]:
    """Downscale and base64-encode, returning (media_type, data)."""
    try:
        from PIL import Image
    except ImportError:
        # No Pillow: send the original bytes and let the API resize.
        data = path.read_bytes()
        suffix = path.suffix.lower()
        media = "image/png" if suffix == ".png" else "image/jpeg"
        return media, base64.b64encode(data).decode()

    with Image.open(path) as im:
        im = im.convert("RGB")
        if max(im.size) > MAX_EDGE:
            im.thumbnail((MAX_EDGE, MAX_EDGE))
        buf = io.BytesIO()
        im.save(buf, format="JPEG", quality=90)
    return "image/jpeg", base64.b64encode(buf.getvalue()).decode()


def build_request(media_type: str, b64: str, model: str) -> dict:
    return {
        "model": model,
        "max_tokens": 2048,
        "messages": [
            {
                "role": "user",
                "content": [
                    {
                        "type": "image",
                        "source": {
                            "type": "base64",
                            "media_type": media_type,
                            "data": b64,
                        },
                    },
                    {"type": "text", "text": PROMPT},
                ],
            }
        ],
    }


def call_api(payload: dict, api_key: str, retries: int = 3) -> str:
    body = json.dumps(payload).encode()
    headers = {
        "content-type": "application/json",
        "x-api-key": api_key,
        "anthropic-version": API_VERSION,
    }
    last = None
    for attempt in range(retries):
        req = urllib.request.Request(API_URL, data=body, headers=headers)
        try:
            with urllib.request.urlopen(req, timeout=120) as resp:
                data = json.load(resp)
            return "".join(
                blk.get("text", "") for blk in data.get("content", [])
                if blk.get("type") == "text"
            )
        except urllib.error.HTTPError as e:
            detail = e.read().decode("utf-8", "replace")[:300]
            last = f"HTTP {e.code}: {detail}"
            # Retry only on rate limit and server errors.
            if e.code not in (429, 500, 502, 503, 529):
                break
        except Exception as e:  # noqa: BLE001 - network errors vary
            last = str(e)
        if attempt < retries - 1:
            time.sleep(2 ** attempt)
    raise RuntimeError(last or "request failed")


PIPE_RE = re.compile(r"^[^|]*\|[^|]*\|[^|]*\|[^|]*$")


def extract_pipe(reply: str) -> str:
    """Pull pipe rows out of a model reply, tolerating fences and stray prose."""
    text = reply.strip()
    # Strip a surrounding code fence if the model added one anyway.
    fence = re.match(r"^```[a-zA-Z]*\n(.*?)\n?```$", text, re.S)
    if fence:
        text = fence.group(1)
    rows = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.upper() == "PROOF":
            continue
        if not PIPE_RE.match(line):
            continue
        # Drop a header row if one slipped through.
        if re.search(r"depends", line, re.I) and re.search(r"justif", line, re.I):
            continue
        rows.append(line)
    return "\n".join(rows) + ("\n" if rows else "")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--images", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--model", default=DEFAULT_MODEL)
    ap.add_argument("--only", default="", help="comma-separated stems, e.g. 000,015")
    ap.add_argument("--mock", type=Path, help="canned reply file; skips the API")
    ap.add_argument("--overwrite", action="store_true",
                    help="re-transcribe images that already have output")
    args = ap.parse_args()

    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not args.mock and not api_key:
        print("ANTHROPIC_API_KEY is not set (or pass --mock to test offline)",
              file=sys.stderr)
        return 2

    if not args.images.is_dir():
        print(f"not a directory: {args.images}", file=sys.stderr)
        return 2
    images = sorted(
        p for p in args.images.iterdir()
        if p.suffix.lower() in (".jpg", ".jpeg", ".png")
    )
    if args.only:
        wanted = {s.strip() for s in args.only.split(",")}
        images = [p for p in images if p.stem in wanted]
    if not images:
        print(f"no images found in {args.images}", file=sys.stderr)
        return 2

    args.out.mkdir(parents=True, exist_ok=True)
    mock_reply = args.mock.read_text() if args.mock else None

    failures = 0
    for path in images:
        dest = args.out / f"{path.stem}.pipe"
        if dest.exists() and not args.overwrite:
            print(f"{path.stem}: skipped (exists)")
            continue
        try:
            if mock_reply is not None:
                reply = mock_reply
            else:
                media, b64 = encode_image(path)
                reply = call_api(build_request(media, b64, args.model), api_key)
            pipe = extract_pipe(reply)
            if not pipe:
                raise RuntimeError("no pipe rows in reply")
            dest.write_text(pipe)
            print(f"{path.stem}: {len(pipe.splitlines())} lines")
        except Exception as e:  # noqa: BLE001
            failures += 1
            print(f"{path.stem}: FAILED - {e}", file=sys.stderr)

    if failures:
        print(f"\n{failures} image(s) failed", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
