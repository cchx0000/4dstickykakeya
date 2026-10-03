import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Zorn

/-!
Positive local extraction gives an exhaustive source-disjoint family even
when quantitative eligibility is not preserved by arbitrary restrictions.
The proof retains whole eligible sets; it never disjointifies an overlapping
cover by deleting uncontrolled parts.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.DisjointPositiveExhaustion

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Positive measurable eligibility on every positive remainder gives a countable
pairwise-disjoint exhaustive family. No closure of eligibility under restriction
is assumed. -/
theorem exists_countable_disjoint_positive_exhaustion
    (μ : Measure Ω) [SFinite μ] (P : Set Ω → Prop)
    (hlocal : ∀ s : Set Ω, MeasurableSet s → μ s ≠ 0 →
      ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ P t ∧ μ t ≠ 0) :
    ∃ D : Set (Set Ω),
      (∀ t ∈ D, MeasurableSet t ∧ P t ∧ μ t ≠ 0) ∧
      D.Countable ∧ D.PairwiseDisjoint id ∧ μ (⋃₀ D)ᶜ = 0 := by
  classical
  let C : Set (Set (Set Ω)) := {D |
    (∀ t ∈ D, MeasurableSet t ∧ P t ∧ μ t ≠ 0) ∧ D.PairwiseDisjoint id}
  obtain ⟨D, hDmax⟩ : ∃ D, Maximal (· ∈ C) D := by
    refine zorn_subset C fun c hc hchain => ?_
    refine ⟨⋃₀ c, ?_, fun d hd => subset_sUnion_of_mem hd⟩
    refine ⟨?_, (pairwiseDisjoint_sUnion hchain.directedOn).2 fun d hd => (hc hd).2⟩
    intro t ht
    obtain ⟨d, hd, htd⟩ := mem_sUnion.mp ht
    exact (hc hd).1 t htd
  have hD := hDmax.prop
  have hcount : D.Countable := by
    have hc := Measure.countable_meas_pos_of_disjoint_iUnion
      (μ := μ) (As := fun t : D => (t : Set Ω))
      (fun t => (hD.1 t t.2).1) hD.2.subtype
    have hpos : {t : D | 0 < μ (t : Set Ω)} = univ := by
      ext t
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact bot_lt_iff_ne_bot.mpr (hD.1 t t.2).2.2
    rw [hpos] at hc
    exact countable_coe_iff.mp (countable_univ_iff.mp hc)
  refine ⟨D, hD.1, hcount, hD.2, ?_⟩
  have hU : MeasurableSet (⋃₀ D) :=
    MeasurableSet.sUnion hcount (fun t ht => (hD.1 t ht).1)
  by_contra hnonzero
  obtain ⟨t, htU, htm, htP, htpos⟩ := hlocal (⋃₀ D)ᶜ hU.compl hnonzero
  have hdisj (s : Set Ω) (hs : s ∈ D) : Disjoint t s := by
    apply disjoint_left.mpr
    intro x hxt hxs
    exact htU hxt (mem_sUnion.mpr ⟨s, hs, hxs⟩)
  have hinsert : insert t D ∈ C := by
    refine ⟨?_, hD.2.insert (fun s hs _ => hdisj s hs)⟩
    intro s hs
    rcases mem_insert_iff.mp hs with rfl | hs
    · exact ⟨htm, htP, htpos⟩
    · exact hD.1 s hs
  have htD : t ∈ D := hDmax.2 hinsert (subset_insert t D) (mem_insert t D)
  have htempty : t = ∅ := disjoint_self.mp (hdisj t htD)
  exact htpos (by rw [htempty, measure_empty])

/-- A countable disjoint cover up to null sets has a finite subfamily of mass
strictly above every threshold below the total mass. Whole sets are retained. -/
theorem exists_finite_subfamily_mass_gt
    (μ : Measure Ω) (D : Set (Set Ω))
    (hm : ∀ t ∈ D, MeasurableSet t) (hcount : D.Countable)
    (hdisj : D.PairwiseDisjoint id) (hcover : μ (⋃₀ D)ᶜ = 0)
    (a : ℝ≥0∞) (ha : a < μ univ) :
    ∃ E : Set (Set Ω), E ⊆ D ∧ E.Finite ∧ a < μ (⋃₀ E) := by
  classical
  have hmass : μ (⋃₀ D) = μ univ := by
    simpa only [hcover, add_zero] using
      (measure_add_measure_compl (μ := μ) (MeasurableSet.sUnion hcount hm))
  have hsum : a < ∑' t : D, μ (t : Set Ω) := by
    rw [← measure_sUnion hcount hdisj hm, hmass]
    exact ha
  rw [ENNReal.tsum_eq_iSup_sum] at hsum
  obtain ⟨F, hF⟩ := lt_iSup_iff.mp hsum
  let E : Set (Set Ω) := (Subtype.val : D → Set Ω) '' (F : Set D)
  have hED : E ⊆ D := by
    rintro t ⟨s, hs, rfl⟩
    exact s.property
  have heq : ⋃₀ E = ⋃ t ∈ F, (t : Set Ω) := by
    ext x
    simp only [E, mem_sUnion, mem_image, Finset.mem_coe, exists_exists_and_eq_and,
      mem_iUnion, exists_prop]
  refine ⟨E, hED, F.finite_toSet.image _, ?_⟩
  have hFD : (F : Set D).PairwiseDisjoint (fun t : D => (t : Set Ω)) :=
    hdisj.subtype.set_pairwise F
  rw [heq, measure_biUnion_finset hFD (fun t _ => hm t t.property)]
  exact hF

/-- Finite retention for arbitrary eligibility, with every retained set still
positive and eligible; there is no bound on the number of selected sets. -/
theorem exists_finite_disjoint_positive_retention
    (μ : Measure Ω) [SFinite μ] (P : Set Ω → Prop)
    (hlocal : ∀ s : Set Ω, MeasurableSet s → μ s ≠ 0 →
      ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ P t ∧ μ t ≠ 0)
    (a : ℝ≥0∞) (ha : a < μ univ) :
    ∃ E : Set (Set Ω),
      (∀ t ∈ E, MeasurableSet t ∧ P t ∧ μ t ≠ 0) ∧
      E.Finite ∧ E.PairwiseDisjoint id ∧ a < μ (⋃₀ E) := by
  obtain ⟨D, hD, hcount, hdisj, hcover⟩ :=
    exists_countable_disjoint_positive_exhaustion μ P hlocal
  obtain ⟨E, hED, hfinite, hmass⟩ := exists_finite_subfamily_mass_gt μ D
    (fun t ht => (hD t ht).1) hcount hdisj hcover a ha
  exact ⟨E, fun t ht => hD t (hED ht), hfinite, fun _ hs _ ht hne => hdisj (hED hs) (hED ht) hne, hmass⟩

end StickyKakeya4.DisjointPositiveExhaustion
