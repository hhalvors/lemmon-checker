# Sequents for the open problems

Proofs to write in Lemmon style, chosen to put pressure on the three
conjectures in the paper. Most are also perfectly ordinary practice.

The loop: prove the sequent at `/proof`, press **Show this as a Fitch proof**,
and look at what comes back. Three things are worth noticing each time —
whether the translation was direct or unfolded; where each line ended up
relative to the boxes; and, for group A, whether any `∀I` sits inside a box
whose assumption mentions the name being generalised upon.

---

## A. The eigenvariable problem (Problem 6.1)

What a counterexample needs. Lemmon licenses `∀I` on a name *a* at line *n*
when *a* occurs in no assumption in Γ(*n*). Fitch licenses it when *a* occurs
in no assumption **in scope**. Scope can be strictly larger than Γ. So we want
a proof in which

* `∀I` is applied on *a*,
* the `∀I` line does **not** depend on some assumption *b*,
* *b*'s formula **does** contain *a*,
* and the construction nevertheless places the `∀I` line inside *b*'s box.

The last condition is the one to engineer: in the unfolding, a line lands
inside *b*'s box exactly when the discharge of *b* is an ancestor of it in the
derivation — which does not require it to depend on *b*.

### A1. ∀x G(x) ⊢ F(a) → (F(a) ∧ ∀y G(y))

This is my candidate. A proof:

```
1|1|∀xG(x)|A
2|2|F(a)|A
1|3|G(a)|1 ∀E
1|4|∀yG(y)|3 ∀I
1,2|5|F(a)∧∀yG(y)|2,4 ∧I
1|6|F(a)→(F(a)∧∀yG(y))|2,5 CP
```

Line 4 generalises on *a*, and depends only on line 1, whose formula `∀xG(x)`
contains no *a*. So the Lemmon side condition is satisfied. But line 4 is
written between assumption 2 and its discharge, so in the Fitch image it lies
inside the box assuming `F(a)` — and *a* occurs there. If the translation
produces

```
1   ∀x G(x)                   Premise
2 │ F(a)                      Assume
3 │ G(a)                      ∀E 1
4 │ ∀y G(y)                   ∀I 3
5 │ F(a) ∧ ∀y G(y)            ∧I 2,4
6   F(a) → (F(a) ∧ ∀y G(y))   CP 2-5
```

then line 4 violates the eigenvariable condition of every Fitch system I know
of, and Conjecture 5.10 is **false as stated** — not merely unproved, since
the output is not a correct Fitch proof.

Two things to check before believing that. First, that the checker accepts the
Lemmon proof: if it rejects line 4, my reading of the side condition is wrong
and there is nothing here. Second, that the translation really does place line
4 inside the box rather than hoisting it — the direct route should, and the
tree route should too, since line 4's derivation sits inside the `CP` node's
subtree.

If it is a counterexample, note that hoisting repairs it: line 4 depends only
on line 1, so it could have been derived before the box opened. That is the
repair suggested in §6.2, and it ties this problem to Conjecture 6.3.

### A2. ∀x G(x), F(a) ⊢ ¬H(a) → (∀y G(y) ∧ ¬H(a))

The same shape with `RAA` in place of `CP`, to check whether the discharging
rule matters. It should not.

### A3. ∀x G(x) ⊢ (F(a) ∨ H(a)) → ∀y G(y)

Via `∨E`, so the `∀I` sits inside one of two case boxes rather than a single
`CP` box. Worth doing because `∨E`'s boxes are siblings, and the placement
rules there were the last thing I got wrong in the implementation.

### A4. ∃x F(x), ∀y G(y) ⊢ ∃x (F(x) ∧ ∀z G(z))

Here the box is opened by `∃E`, whose assumption names a fresh witness. Try
generalising on a name *other* than the witness inside that box, then try
generalising on the witness itself. The second should fail in both systems —
if it fails in only one, that is a second discrepancy worth knowing about.

### A5. ⊢ F(a) → ∀y (G(y) → G(y))

Degenerate but instructive: the `∀I` line depends on nothing at all, and so is
trapped by any box it happens to be written inside. If A1 works, this should
too, and more sharply.

---

## B. Duplication (Conjecture 6.3)

A counterexample needs a line cited from two places that no nesting can bring
under one roof. The argument in §6.3 suggests this is impossible — if L is
cited by M then Γ(L) ⊆ Γ(M) — so these are attempts to break that argument
rather than likely successes.

### B1. P → Q, P → R ⊢ (S → (Q ∧ S)) ∧ (T → (R ∧ T))

Two sibling boxes, each using material from outside. Everything shared here is
a premise, so it should translate directly. A warm-up that establishes the
baseline.

### B2. P, P → Q ⊢ (S → (Q ∧ S)) ∧ (T → (Q ∧ T))

Now the shared line — `Q`, derived by `MP` — is not a premise but still
depends only on premises. Still expected to translate directly, because `Q`
can sit at the top level.

### B3. A ⊢ (S → ((A ∧ S) ∧ B)) ∧ (T → ((A ∧ T) ∧ B)) where B is derived from A

Push it: make the shared lemma depend on an assumption that is itself
discharged. If the shared line depends on assumption *k*, then so does
everything citing it, which forces those users into *k*'s box — which is why I
expect no counterexample. Finding one would mean that argument has a hole.

---

## C. Discharge order (Conjecture 6.2)

### C1. ⊢ Q → (P → (P ∧ Q))

Prove it by assuming `P` first, then `Q`, and discharging `P` first. That is
Example 4.3 and should unfold. Then prove the same sequent assuming `Q` first,
and confirm the second version translates directly — the point of the
conjecture is that some permutation always works.

### C2. P → Q, Q → R ⊢ (P → R) ∧ (P → Q)

Two conditionals proved from overlapping material, with the assumption of `P`
made once and used twice. Try discharging in both orders.

---

## D. Ordinary practice

Nothing pointed about these; they exercise the rules that the corpus covers
only once each.

* **D1.** `∀x (F(x) → G(x)), ∃x F(x) ⊢ ∃x G(x)`
* **D2.** `¬∃x F(x) ⊢ ∀x ¬F(x)`
* **D3.** `∀x (F(x) ↔ G(x)) ⊢ ∀x F(x) ↔ ∀x G(x)`
* **D4.** `a = b, F(a) ⊢ ∃x (F(x) ∧ x = b)`
* **D5.** `⊢ (P → Q) ∨ (Q → P)`

D5 needs excluded middle and is the one most likely to produce an interesting
box structure.

---

## Recording results

If a proof produces a Fitch image that looks wrong, it belongs in
`test/Tests.hs` under "Fitch obstructions" with a note saying what it probes —
that is how the premise-inside-a-subproof case got pinned. A counterexample to
A1 would additionally want the eigenvariable check described in §6.2 added to
`fitchWellFormed`, so that the next one is caught by machine rather than by
eye.
