# Historical targets retained for comparison

These are unproved statements from the earlier repository proposal. They are
not asserted as theorems, and they are not used as axioms in the repaired route.
The original paper's compact marked main theorem remains the final target.

## Borel-selector-only front closure

Before the source audit, `Solutions/Sol_StickyKakeya4_selector_closure.lean`
contained the following stronger signature, with a proof using obsolete APIs:

```lean
theorem solution (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3) :
    dimH (unitFront selector) = 4
```

Status: unresolved as stated. The original manuscript selects a Borel graph but
its literal closure theorem is worded for compact selectors. The current
auxiliary Solution keeps the original compact ambient family and concludes
dimension four for that ambient front. This preserves the main theorem and
makes no claim to solve the stronger signature above. See the source and support
audit in `ORIGINAL_PAPER_TARGETS.md`.

The pre-edit code is retained in baseline commit
`d208ddf4544cbb9ed05e4c848a83b07985b28e26`.

## Arbitrary-shading hereditary overlap estimate

The original wording remains in `PROVE2ME_TARGETS.md`, clearly marked as a
historical proposal. Its arbitrary-shading quantifier is stronger than the
paper's explicit occurrence-measure interface. The common-shading obstruction
shows why it cannot be treated as a missing tactic proof. No replacement axiom
or silently altered definition has been introduced.
