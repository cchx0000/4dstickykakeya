/- UNVERIFIED source consumer. No compiler was run for this draft.

The only phase population estimate used below is
NativeActualPhaseHeightPopulation.actual_full_phase_card, applied to the
same original HB, Rfull, Eref, and admitted source hS as the fine graph.
The selected key is exactly relativeLabel at c, so its fixed factor is
373248. There is no current-parent intercept projection in this key.

The mass selection uses an image-cover inequality, not disjointness of
geometric images. The separate graph-fiber readback uses the unchanged
baseline b0 tube index. No configuration property of cfg is assumed.
-/
import Theorems.Thm_StickyKakeya4_native_same_Q_fine_graph
import Theorems.Thm_StickyKakeya4_native_actual_phase_height_population

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeActualMassiveOldPhase
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeRelativeParentLabels NativeConfiguredIncidenceFibers
open NativeSameQSourceRestriction NativeSameQFineGraph NativeActualPhaseHeightPopulation
open scoped BigOperators

/-- Images of all original key fibers cover the whole image. The images
may overlap; the estimate does not charge or assume any disjointness. -/
theorem image_card_le_sum_fiber_images {alpha beta gamma : Type*}
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq gamma]
    (T : Finset alpha) (pair : alpha → beta) (key : alpha → gamma) :
    (T.image pair).card ≤
      ∑ q ∈ T.image key, ((T.filter (fun z => key z = q)).image pair).card := by
  have hcover : T.image pair ⊆ (T.image key).biUnion
      (fun q => (T.filter (fun z => key z = q)).image pair) := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hv
    exact mem_biUnion.mpr ⟨key z, mem_image_of_mem _ hz,
      mem_image_of_mem _ (mem_filter.mpr ⟨hz, rfl⟩)⟩
  exact (card_le_card hcover).trans card_biUnion_le

/-- Filtering original occurrences by one relative c-phase gives the
literal c-phase fiber in the fine graph with its baseline b0 index. -/
theorem graph_filter_relative_phase {n : ℕ} {D : FiniteScaleSource n}
    {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (Rfull : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m b0 c : ℕ)
    (hc : c ≤ b0) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h Rfull Eref a m p) etaS)
    (cfg : Index → E4) (qOld : Parent)
    (hParent : ∀ z ∈ T, z.1 ∈ parentLabels D Rfull a (2 ^ m) p) :
    graph h Rfull Eref a m b0 p hS cfg
        (T.filter (fun z => relativeLabel D a (2 ^ m) p (2 ^ c) z.1 = qOld)) =
      (graph h Rfull Eref a m b0 p hS cfg T).filter
        (fun v => phase h Rfull Eref a m b0 c p v.2 = qOld) := by
  simpa only [restrict, mem_singleton] using
    graph_restrict h Rfull Eref T a m b0 c hc p hS cfg {qOld} hParent

/-- Select an actual massive old phase inside the already chosen SAME Q.

Positive mass is the sum of the actual same-Q fine-pair weights. Original
HB and the same admitted Eref-native source supply the full c-phase count;
neither a phase-count certificate nor a final-density certificate is an
input. The current shading T is only required to retain original support
and original parent membership. Every graph below uses the original cfg
and the same b0 outputTube index, including after both restrictions.
-/
theorem from_original_reference_same_Q {n : ℕ} {D : FiniteScaleSource n}
    {eta etaS a zeta profile : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (Rfull : Finset (Fin n))
    (level : ℕ) (hzeta : 0 ≤ zeta)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original Rfull a level zeta)
    (Eref T : Finset (Fin n × Index)) (m b0 b c : ℕ)
    (hm : m ≤ level) (hb0 : b0 ≤ level - m + 6)
    (hcb : c ≤ b) (hbb0 : b ≤ b0) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h Rfull Eref a m p) etaS)
    (hbudget : (64 : ℝ) ^ 3 * (source h Rfull Eref a m p).thickness ^ profile ≤
      D.thickness ^ zeta)
    (hsupport : T ⊆ NativeCubicalIncidenceCounts.incidences original)
    (hParent : ∀ z ∈ T, z.1 ∈ parentLabels D Rfull a (2 ^ m) p)
    (cfg : Index → E4) (Q : Finset Parent)
    (hmassPos : 0 < ∑ q ∈ Q, weight h Rfull Eref a m b0 b p hS cfg T q) :
    let Gfine := fun U : Finset (Fin n × Index) =>
      graph h Rfull Eref a m b0 p hS cfg U
    let TQ := restrict D a m b p Q T
    let allParents :=
      (univ : Finset (Fin (parentLabels D Rfull a (2 ^ m) p).card)).image
        (parentLabel (source h Rfull Eref a m p) 0 (2 ^ c))
    let phaseCap := 373248 * (source h Rfull Eref a m p).thickness ^ (-profile) *
      (((2 ^ c : ℕ) : ℝ)) ^ 3
    ∃ qOld ∈ allParents,
      let A := TQ.filter
        (fun z => relativeLabel D a (2 ^ m) p (2 ^ c) z.1 = qOld)
      A.Nonempty ∧ A ⊆ TQ ∧ A ⊆ T ∧
      A ⊆ NativeCubicalIncidenceCounts.incidences original ∧
      (∀ z ∈ A,
        relativeLabel D a (2 ^ m) p (2 ^ b) z.1 ∈ Q ∧
        relativeLabel D a (2 ^ m) p (2 ^ c) z.1 = qOld) ∧
      (Gfine A).Nonempty ∧
      Gfine A = (Gfine TQ).filter
        (fun v => phase h Rfull Eref a m b0 c p v.2 = qOld) ∧
      (∀ v ∈ Gfine A,
        phase h Rfull Eref a m b0 b p v.2 ∈ Q ∧
        phase h Rfull Eref a m b0 c p v.2 = qOld) ∧
      ((Gfine TQ).card : ℝ) ≤ phaseCap * ((Gfine A).card : ℝ) ∧
      (∑ q ∈ Q, weight h Rfull Eref a m b0 b p hS cfg T q) ≤
        phaseCap * ((Gfine A).card : ℝ) := by
  intro Gfine TQ allParents phaseCap
  let old : Fin n × Index → Parent :=
    fun z => relativeLabel D a (2 ^ m) p (2 ^ c) z.1
  let oldPhases := TQ.image old
  let oldFiber := fun q : Parent => TQ.filter (fun z => old z = q)
  have hc0 : c ≤ b0 := hcb.trans hbb0
  have hcLevel : c ≤ level - m + 6 := hc0.trans hb0
  have hTQT : TQ ⊆ T := filter_subset _ _
  have hParentQ : ∀ z ∈ TQ, z.1 ∈ parentLabels D Rfull a (2 ^ m) p :=
    fun z hz => hParent z (hTQT hz)
  have hFull : (allParents.card : ℝ) ≤ phaseCap :=
    actual_full_phase_card h original Rfull level hzeta HB Eref m c hm hcLevel p hS hbudget
  have hphaseSub : oldPhases ⊆ allParents := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hq
    exact relative_parent_mem_full h Rfull Eref a m c p z.1 (hParentQ z hz)
  have hphaseCard : (oldPhases.card : ℝ) ≤ phaseCap :=
    (Nat.cast_le.mpr (card_le_card hphaseSub)).trans hFull
  have hmass :
      (∑ q ∈ Q, weight h Rfull Eref a m b0 b p hS cfg T q) =
        ((Gfine TQ).card : ℝ) :=
    sum_weight_eq_graph h Rfull Eref T a m b0 b hbb0 p hS cfg Q hParent
  have hGposR : (0 : ℝ) < (Gfine TQ).card := by
    rw [← hmass]
    exact hmassPos
  have hGpos : 0 < (Gfine TQ).card := by exact_mod_cast hGposR
  have hTQn : TQ.Nonempty := by
    obtain ⟨v, hv⟩ := card_pos.mp hGpos
    obtain ⟨z, hz, _he⟩ := mem_image.mp hv
    exact ⟨z, hz⟩
  have hphaseN : oldPhases.Nonempty := hTQn.image old
  obtain ⟨qOld, hqOld, hmax⟩ := exists_max_image oldPhases
    (fun q => (Gfine (oldFiber q)).card) hphaseN
  let A := oldFiber qOld
  have hAn : A.Nonempty := by
    obtain ⟨z, hz, he⟩ := mem_image.mp hqOld
    exact ⟨z, mem_filter.mpr ⟨hz, he⟩⟩
  have hATQ : A ⊆ TQ := filter_subset _ _
  have hAT : A ⊆ T := hATQ.trans hTQT
  have hAsupport : A ⊆ NativeCubicalIncidenceCounts.incidences original :=
    hAT.trans hsupport
  have hOriginal : ∀ z ∈ A,
      relativeLabel D a (2 ^ m) p (2 ^ b) z.1 ∈ Q ∧
      relativeLabel D a (2 ^ m) p (2 ^ c) z.1 = qOld := by
    intro z hz
    exact ⟨(mem_filter.mp (hATQ hz)).2, (mem_filter.mp hz).2⟩
  have hGAn : (Gfine A).Nonempty := hAn.image _
  have hGraphFiber : Gfine A = (Gfine TQ).filter
      (fun v => phase h Rfull Eref a m b0 c p v.2 = qOld) :=
    graph_filter_relative_phase h Rfull Eref TQ a m b0 c hc0 p hS cfg qOld hParentQ
  have hSameQ : Gfine TQ = (Gfine T).filter
      (fun v => phase h Rfull Eref a m b0 b p v.2 ∈ Q) :=
    graph_restrict h Rfull Eref T a m b0 b hbb0 p hS cfg Q hParent
  have hGraphSub : Gfine A ⊆ Gfine TQ := image_subset_image hATQ
  have hGraphPhase : ∀ v ∈ Gfine A,
      phase h Rfull Eref a m b0 b p v.2 ∈ Q ∧
      phase h Rfull Eref a m b0 c p v.2 = qOld := by
    intro v hv
    have hvQ := hGraphSub hv
    have hvOld := hv
    rw [hSameQ] at hvQ
    rw [hGraphFiber] at hvOld
    exact ⟨(mem_filter.mp hvQ).2, (mem_filter.mp hvOld).2⟩
  have hcover : (Gfine TQ).card ≤
      ∑ q ∈ oldPhases, (Gfine (oldFiber q)).card :=
    image_card_le_sum_fiber_images TQ
      (fun z => (cfg z.2, outputTube h Rfull Eref a m b0 p hS z.1)) old
  have hNatCard : (Gfine TQ).card ≤ oldPhases.card * (Gfine A).card := by
    calc
      _ ≤ ∑ q ∈ oldPhases, (Gfine (oldFiber q)).card := hcover
      _ ≤ ∑ _q ∈ oldPhases, (Gfine A).card :=
        sum_le_sum (fun q hq => hmax q hq)
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have hCard : ((Gfine TQ).card : ℝ) ≤ phaseCap * ((Gfine A).card : ℝ) := by
    have hNatCardR : ((Gfine TQ).card : ℝ) ≤
        (oldPhases.card : ℝ) * ((Gfine A).card : ℝ) := by exact_mod_cast hNatCard
    exact hNatCardR.trans
      (mul_le_mul_of_nonneg_right hphaseCard (Nat.cast_nonneg _))
  refine ⟨qOld, hphaseSub hqOld, hAn, hATQ, hAT, hAsupport, hOriginal,
    hGAn, hGraphFiber, hGraphPhase, hCard, ?_⟩
  rw [hmass]
  exact hCard

end NativeActualMassiveOldPhase
