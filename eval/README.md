# Evaluation corpus

Ground truth for the handwriting → proof-checker pipeline.

    images/NNN.jpg    photograph of a completed proof template
    truth/NNN.pipe    the transcription that photograph should produce
    pred/             recogniser output, scored against truth/ (gitignored)

Run the recogniser, then score it:

    export ANTHROPIC_API_KEY=sk-...
    python3 tools/transcribe.py --images eval/images --out eval/pred
    stack build && stack exec eval-score -- eval/truth eval/pred

`transcribe.py` skips images that already have output, so a failed run can be
resumed; pass `--overwrite` to redo them, `--only 000,015` to work on a subset,
and `--model` to compare models. `--mock <file>` feeds a canned reply through
the parsing path without touching the API.

Two numbers come out. **Cell accuracy** — per column, comparing parsed values
so `P->Q` and `P→Q` count as equal — diagnoses the recogniser and says where
the errors are. **Verdict agreement** asks whether the checker reaches the same
conclusion from the transcription as from the truth; that is the error a
student actually experiences, and it is the number to optimise.

## Provenance

`000`–`015` come from `donut-data/train`, whose JSON ground truth was written
alongside the photographs. `016` is `proof.jpeg`, transcribed by hand.

## The corpus is not all valid proofs

`009` is annotated "Invalid!" on the page: it generalises on `a` in only some
of its occurrences, inferring `∀y(Fa→Fy)` from `Fa→Fa`. The checker rejects it,
correctly. Transcription must be faithful to what was written, mistakes
included, so `eval-score` takes each truth file's expected verdict from the
checker rather than assuming validity.

`013` cites modus ponens as `1,2 MP` with the antecedent first and the
conditional second, which the checker rejects — it requires the conditional to
be cited first. The transcription is faithful to the page; it is the citation
convention that is in tension. Worth revisiting if this turns out to be common
in student work.
