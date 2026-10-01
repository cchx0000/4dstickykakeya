import Theorems.Thm_StickyKakeya4_conditioned_boundary_packet_mass

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

universe u v

/-- A finite mass-conserving stopping certificate.  At a terminal node every
still-unremoved event obeys its relative cap bound.  A removal node records an
actual strict violation for the current remainder and continues with the
measure restricted to the complement of that event.  Thus packet disjointness
and exact conservation are consequences of measurable restriction, not extra
fields of the certificate. -/
inductive FiniteMassConservingStoppingRun
    {X : Type u} [MeasurableSpace X]
    {I : Type v} [DecidableEq I]
    (event : I → Set X) (cost : I → ENNReal) (C : ENNReal) :
    Measure X → Finset I → Type (max u v)
  | terminal {nu : Measure X} {remaining : Finset I}
      (good : ∀ i ∈ remaining,
        nu (event i) ≤ C * nu Set.univ * cost i) :
      FiniteMassConservingStoppingRun event cost C nu remaining
  | remove {nu : Measure X} {remaining : Finset I}
      (i : I) (hi : i ∈ remaining)
      (eventMeasurable : MeasurableSet (event i))
      (large : C * nu Set.univ * cost i < nu (event i))
      (tail : FiniteMassConservingStoppingRun event cost C
        (nu.restrict (event i)ᶜ) (remaining.erase i)) :
      FiniteMassConservingStoppingRun event cost C nu remaining

/-- Every finite measurable event family admits a stopping certificate.  The
proof is strong induction on the number of still-available events: if the
relative cap bounds are not all valid, remove one genuine violating event and
continue on its complement. -/
theorem exists_finiteMassConservingStoppingRun
    {X : Type u} [MeasurableSpace X]
    {I : Type v} [DecidableEq I]
    (nu : Measure X) (event : I → Set X) (cost : I → ENNReal)
    (C : ENNReal) (eventsMeasurable : ∀ i, MeasurableSet (event i))
    (remaining : Finset I) :
    Nonempty (FiniteMassConservingStoppingRun event cost C nu remaining) := by
  classical
  induction remaining using Finset.strongInductionOn generalizing nu
  rename_i remaining ih
  by_cases hgood : ∀ i ∈ remaining,
      nu (event i) ≤ C * nu Set.univ * cost i
  · exact ⟨FiniteMassConservingStoppingRun.terminal hgood⟩
  · push Not at hgood
    obtain ⟨i, hi, hlarge⟩ := hgood
    obtain ⟨tail⟩ := ih (remaining.erase i)
      (Finset.erase_ssubset hi) (nu.restrict (event i)ᶜ)
    exact ⟨FiniteMassConservingStoppingRun.remove i hi
      (eventsMeasurable i) hlarge tail⟩

namespace FiniteMassConservingStoppingRun

variable {X : Type u} [MeasurableSpace X]
variable {I : Type v} [DecidableEq I]
variable {event : I → Set X} {cost : I → ENNReal} {C : ENNReal}

/-- The terminal remainder measure carried by a finite stopping run. -/
def terminalMeasure {nu : Measure X} {remaining : Finset I}
    (run : FiniteMassConservingStoppingRun event cost C nu remaining) :
    Measure X :=
  match run with
  | .terminal _ => nu
  | .remove _ _ _ _ tail => terminalMeasure tail

/-- Sum of the actual masses removed by a finite stopping run. -/
def removedMass {nu : Measure X} {remaining : Finset I}
    (run : FiniteMassConservingStoppingRun event cost C nu remaining) :
    ENNReal :=
  match run with
  | .terminal _ => 0
  | .remove i _ _ _ tail => nu (event i) + removedMass tail

/-- Sum of the relative cap charges at the moments when their packets are
removed. -/
def chargedMass {nu : Measure X} {remaining : Finset I}
    (run : FiniteMassConservingStoppingRun event cost C nu remaining) :
    ENNReal :=
  match run with
  | .terminal _ => 0
  | .remove i _ _ _ tail =>
      C * nu Set.univ * cost i + chargedMass tail

/-- Measurable restriction gives exact mass conservation through the whole
finite stopping run. -/
theorem mass_conservation {nu : Measure X} {remaining : Finset I}
    (run : FiniteMassConservingStoppingRun event cost C nu remaining) :
    nu Set.univ = run.terminalMeasure Set.univ + run.removedMass := by
  induction run with
  | terminal good =>
      simp [terminalMeasure, removedMass]
  | @remove nu remaining i hi hmeasurable hlarge tail ih =>
      have hsplit :
          nu Set.univ = nu (event i) +
            (nu.restrict (event i)ᶜ) Set.univ := by
        calc
          nu Set.univ =
              (nu.restrict (event i) + nu.restrict (event i)ᶜ) Set.univ := by
            rw [Measure.restrict_add_restrict_compl hmeasurable]
          _ = nu (event i) +
              (nu.restrict (event i)ᶜ) Set.univ := by
            simp [Measure.add_apply, Measure.restrict_apply]
      simp only [terminalMeasure, removedMass]
      calc
        nu Set.univ = nu (event i) +
            (nu.restrict (event i)ᶜ) Set.univ := hsplit
        _ = nu (event i) +
            (tail.terminalMeasure Set.univ + tail.removedMass) := by rw [ih]
        _ = tail.terminalMeasure Set.univ +
            (nu (event i) + tail.removedMass) := by ac_rfl

/-- Every relative cap charge is paid by its actual removed mass, so the total
finite charge is bounded with coefficient one. -/
theorem chargedMass_le_removedMass
    {nu : Measure X} {remaining : Finset I}
    (run : FiniteMassConservingStoppingRun event cost C nu remaining) :
    run.chargedMass ≤ run.removedMass := by
  induction run with
  | terminal good =>
      simp [chargedMass, removedMass]
  | remove i hi hmeasurable hlarge tail ih =>
      simp only [chargedMass, removedMass]
      exact add_le_add hlarge.le ih

/-- The terminal remainder is a submeasure of the starting measure. -/
theorem terminalMeasure_le_start
    {nu : Measure X} {remaining : Finset I}
    (run : FiniteMassConservingStoppingRun event cost C nu remaining) :
    run.terminalMeasure ≤ nu := by
  induction run with
  | terminal good => exact le_rfl
  | remove i hi hmeasurable hlarge tail ih =>
      exact ih.trans Measure.restrict_le_self

/-- The terminal cap bounds hold for the entire initial finite event family.
Previously removed events have zero terminal mass; unremoved events inherit the
terminal certificate. -/
theorem terminal_good_on_initial_events
    {nu : Measure X} {remaining : Finset I}
    (run : FiniteMassConservingStoppingRun event cost C nu remaining) :
    ∀ i ∈ remaining,
      run.terminalMeasure (event i) ≤
        C * run.terminalMeasure Set.univ * cost i := by
  induction run with
  | terminal good => exact good
  | @remove nu remaining selected hselected hmeasurable hlarge tail ih =>
      intro i hi
      by_cases hisel : i = selected
      · subst i
        have hle : tail.terminalMeasure (event selected) ≤
            (nu.restrict (event selected)ᶜ) (event selected) :=
          terminalMeasure_le_start tail (event selected)
        have hzero :
            (nu.restrict (event selected)ᶜ) (event selected) = 0 := by
          rw [Measure.restrict_apply hmeasurable]
          simp
        have hterminalZero : tail.terminalMeasure (event selected) = 0 :=
          le_antisymm (hle.trans_eq hzero) bot_le
        simp [terminalMeasure, hterminalZero]
      · have hiErase : i ∈ remaining.erase selected :=
          Finset.mem_erase.mpr ⟨hisel, hi⟩
        simpa only [terminalMeasure] using ih i hiErase

/-- Exact conservation forces a half-mass dichotomy: either at least half of
the starting mass survives in the good terminal remainder, or at least half
has been removed by paid packets. -/
theorem half_mass_terminal_or_removed
    {nu : Measure X} {remaining : Finset I}
    (run : FiniteMassConservingStoppingRun event cost C nu remaining) :
    nu Set.univ / 2 ≤ run.terminalMeasure Set.univ ∨
      nu Set.univ / 2 ≤ run.removedMass := by
  by_cases hterminal :
      nu Set.univ / 2 ≤ run.terminalMeasure Set.univ
  · exact Or.inl hterminal
  · right
    by_contra hremoved
    have hterminalLt :
        run.terminalMeasure Set.univ < nu Set.univ / 2 :=
      lt_of_not_ge hterminal
    have hremovedLt : run.removedMass < nu Set.univ / 2 :=
      lt_of_not_ge hremoved
    have hcontradiction :
        run.terminalMeasure Set.univ + run.removedMass < nu Set.univ := by
      calc
        run.terminalMeasure Set.univ + run.removedMass <
            nu Set.univ / 2 + nu Set.univ / 2 :=
          ENNReal.add_lt_add hterminalLt hremovedLt
        _ = nu Set.univ := ENNReal.add_halves (nu Set.univ)
    rw [← run.mass_conservation] at hcontradiction
    exact (lt_irrefl _) hcontradiction

/-- Finite mass-conserving vector stopping in the exact good-or-paid form.
The paid alternative includes coefficient-one charge control. -/
theorem good_half_or_paid_half
    {nu : Measure X} {remaining : Finset I}
    (run : FiniteMassConservingStoppingRun event cost C nu remaining) :
    (nu Set.univ / 2 ≤ run.terminalMeasure Set.univ ∧
      ∀ i ∈ remaining,
        run.terminalMeasure (event i) ≤
          C * run.terminalMeasure Set.univ * cost i) ∨
    (nu Set.univ / 2 ≤ run.removedMass ∧
      run.chargedMass ≤ run.removedMass ∧
      nu Set.univ = run.terminalMeasure Set.univ + run.removedMass) := by
  rcases run.half_mass_terminal_or_removed with hterminal | hremoved
  · exact Or.inl ⟨hterminal, run.terminal_good_on_initial_events⟩
  · exact Or.inr ⟨hremoved, run.chargedMass_le_removedMass,
      run.mass_conservation⟩

end FiniteMassConservingStoppingRun

end StickyKakeya4
