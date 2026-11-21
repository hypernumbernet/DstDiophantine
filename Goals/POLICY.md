# Goals library policy

The `Goals/` Lean library holds **target statements** for the dual spacetime
programme. It is isolated from the main library: nothing under
`DstDiophantine/` may import `Goals`.

## Lifecycle

1. Each target is a `theorem` with a complete statement and `sorry` as proof.
2. When a target is proved without `sorry`, move the proof into the main
   library (under `DstDiophantine/`), delete the corresponding goal, and update
   `Goals/README.md` in the same pull request.
3. Changes to a target's **statement** must be visible in the PR diff and
   noted in `Goals/README.md` (including the reason for the change).

## Vocabulary

- Reuse definitions from the main library; do not add new axioms in `Goals/`.
- If a paper claim cannot yet be expressed, record it in the index as
  *not yet stateable* and name the missing definition rather than inventing one.

## Shape of a target

- The `sorry` sits on an irreducible open `Prop`. If the main library proves
  `P` from open props `Q₁, …, Qₙ`, then `Goals` proves `P` by that theorem
  and puts `sorry` only on the `Qᵢ` that are still open.
- A statement that is `True`, or an existence claim whose witness does not
  use a definition from the main library, is not a target.
- A bridge the main library marks diagnostic, demoted, legacy, or false is
  not a target. `AbcAdmissibleBridge` is false (`AbcAdmissibleBridge_false`).

## CI

- `lake build` on the default targets must remain sorry-free (main library).
- `lake build Goals` is allowed to contain `sorry`; CI reports the open count.