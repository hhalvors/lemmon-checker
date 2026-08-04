# Prompt variants

Kept as the record of an experiment, not as live configuration.
`prompts/transcribe.txt` is what actually runs.

Three variants were each run three times over the sixteen-image corpus,
scored with `eval-score`:

    baseline        98%  98%  98%     mean 98.0, spread 0
    erasure-only    96%  98%  95%     mean 96.3, spread 3
    baseline+deps+erasure (then current)
                    97%  97%  97%     mean 97.0, spread 0

`baseline` is the plain prompt. `erasure-only` adds guidance about
incompletely rubbed-out pencil. The third adds, on top of that, a paragraph
insisting the dependency column be read rather than inferred.

Both additions were written in response to a single observed failure, and both
made things worse. The erasure paragraph also tripled the run-to-run spread.
The lesson worth keeping: a prompt change justified by one bad transcription is
not evidence of anything. Run it three times and compare means before believing
it.
