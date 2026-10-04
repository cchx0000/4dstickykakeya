import Theorems.Thm_StickyKakeya4_native_dyadic_pruning_cutoff
import Theorems.Thm_StickyKakeya4_native_pruning_mass_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeCompactDyadicSource
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeOriginalParentPhysicalData NativeCompactAncestorBudget NativeOriginalPrunedMass
open NativePruningMassBudget NativeDyadicPruningCutoff
open scoped ENNReal

/-- One original retained tube set simultaneously has every genuine dyadic
ancestor lower bound, half the source tube count, half the source shading
mass, the inherited shading density, and inherited convex-Wolff counts.
All cutoffs are constructed before the original finite source is chosen. -/
theorem compact_original_dyadic_source (K : Set MarkedLine) (hK : IsCompact K)
    {zeta : ℝ} (hzeta : 0<zeta) :
    ∃ delta0 : ℝ, 0<delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i,D.line i∈K) →
      D.thickness≤delta0 → eta≤zeta/16 →
      ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
        D.thickness=(2:ℝ)⁻¹^level ∧
        (∀ i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
        R.Nonempty ∧ n≤2*R.card ∧
        wzTotalShadingVolume D≤2*shadingMass D R ∧
        (ENNReal.ofReal D.thickness).rpow eta*tubeMass D R≤2*shadingMass D R ∧
        (∀ U : Set E4,Convex ℝ U →
          ((R.filter (fun i=>markedUnitTube (D.line i) D.thickness⊆U)).card:ℝ≥0∞)≤
            2*(ENNReal.ofReal D.thickness).rpow (-eta)*volume U*R.card) ∧
        ∀ (ell : Fin (level+1)) (p : Parent),
          (R.filter (fun i=>parentLabel D a (2^ell.val) i=p)).Nonempty →
            target D.thickness zeta (2^ell.val)≤
              ((R.filter (fun i=>parentLabel D a (2^ell.val) i=p)).card:ℝ) := by
  obtain ⟨C,L,hC,hL,hprune⟩ := compact_original_ancestor_pruning K hK
  obtain ⟨dp,hdp,_hdp1,hcut⟩ := exists_dyadic_pruning_cutoff hC (by linarith : 0<L) hzeta
  obtain ⟨dt,hdt,htube⟩ := exists_markedUnitTube_admissible_scale (show 0<zeta/16 by positivity)
  refine ⟨min dp dt,lt_min hdp hdt,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,ha⟩ := exists_common_height h
  obtain ⟨level,hdy⟩ := h.1.2.2.2.1
  have hc := hcut D.thickness eta level h.1.2.1 (hsmall.trans (min_le_left _ _)) hdy heta
  obtain ⟨R,hret,hterminal⟩ := hprune n (level+1) D eta zeta a
    (fun ell : Fin (level+1)=>2^ell.val) h hDK ha
    (fun _=>by positivity) hc.1
  have hret' : (n:ℝ)≤R.card+2*C*((level:ℝ)+1)*D.thickness^(zeta-2*eta-3) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hret
  have hhalf := half_card_of_loss_budget h R hret' hc.2.1
  have hsmallmass := removed_mass_small h R hret' hc.2.2 (fun i=>
    htube (D.line i) (h.1.2.2.2.2.1 i) D.thickness h.1.2.1
      (hsmall.trans (min_le_right _ _)))
  have hshade := retained_shading_density h R hsmallmass
  have hR : R.Nonempty := card_pos.mp (by have hn:=h.1.1; omega)
  exact ⟨a,level,R,hdy,ha,hR,hhalf,hshade.1,hshade.2,
    fun U hU=>retained_convexWolff h R hhalf U hU,hterminal⟩

end NativeCompactDyadicSource
