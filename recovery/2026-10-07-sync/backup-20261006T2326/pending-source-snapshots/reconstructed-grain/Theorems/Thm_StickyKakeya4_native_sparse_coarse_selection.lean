/- RECONSTRUCTED 2026-10-06 from visible conversation context. UNVERIFIED.
Latest remembered version: Oct 5 attempt 03 was queued; no result was observed.
Includes the explicit local-parent-scales import and the hpow reduction fix. -/
import Theorems.Thm_StickyKakeya4_native_same_source_coarse_admission
import Theorems.Thm_StickyKakeya4_native_local_parent_scales
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeSparseCoarseSelection
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeCoarseShadingCapacity NativeCoarseDyadicShading NativeCoarseShadingPruning
open NativeCoarseDirectionThinning NativeCoarseMassBudget NativeDyadicParentCells
open NativeSameSourceCoarseSelection NativeUnitParentNormalization
open scoped BigOperators

/-- Reparameterize the existing pruning powers at the actual coarse scale.
The exponent may depend on the scales; no new finite family is introduced. -/
lemma power_at_coarse_scale {eps mu : ℝ} (heps : 0 < eps) (hne : eps≠1)
    (hmu : 0 < mu) (e a : ℝ) :
    eps^(a*(Real.logb eps mu*e/8))=mu^(a*e/8) := by
  calc
    _ = eps^(Real.logb eps mu*(a*e/8)) := by congr 1; ring
    _ = (eps^(Real.logb eps mu))^(a*e/8) := Real.rpow_mul heps.le _ _
    _ = _ := by rw [Real.rpow_logb heps hne hmu]

/-- Sparse current incidences are colored by their actual coarse shading
weight and pruned on the native reference backbone. The entry cost is the
literal selected-cell mass; it is not native admission of that shading.
The logarithmic deletion charge uses only the requested coarse depth. -/
theorem sparse_coarse_selection {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (hR : R.Nonempty) (E : Finset (Fin n × Index))
    (hE : E⊆retained original R) (level b : ℕ)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hb : b≤level) (h6 : 6≤b)
    (H : ∀j : Fin (level+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^j.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^j.val) i=p)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^j.val) i=p)).card:ℝ) ≤
          D.thickness^(-zeta)*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3)
    (hselected : (43*colorCost)*D.thickness^(2*zeta) ≤ (E.card:ℝ)*(D.thickness/2)^4)
    (hlog : 2*pruneCost*((b:ℝ)+1) ≤ D.thickness^(-zeta))
    (hsmall : 2*D.thickness^zeta ≤ 1) :
    ∃Q⊆R.image (parentLabel D a (2^b)),Q.Nonempty ∧
      (∀p∈Q,representative h R a (2^b) p∈R ∧
        parentLabel D a (2^b) (representative h R a (2^b) p)=p) ∧
      (∀p∈Q,∀q∈Q,p≠q → 64/((2^b:ℕ):ℝ) ≤
        dist (direction (D.line (representative h R a (2^b) p)))
          (direction (D.line (representative h R a (2^b) q)))) ∧
      D.thickness^(5*zeta) ≤ ∑p∈Q,weight D a level b (representative h R a (2^b)) E p ∧
      (∀j : Fin (b+1),∀p : Parent,
        (Q.filter (fun q => ancestor b j.val q=p)).Nonempty →
          D.thickness^(8*zeta)*(((2^b:ℕ):ℝ)/((2^j.val:ℕ):ℝ))^3 ≤
            ((Q.filter (fun q => ancestor b j.val q=p)).card:ℝ)) := by
  have hd := h.1.2.1
  have hscale : ((2^b:ℕ):ℝ)*D.thickness≤1 := by
    rw [NativeLocalParentScales.relative_scale hdy hb]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  let P := R.image (parentLabel D a (2^b))
  let rep := representative h R a (2^b)
  let W := weight D a level b rep E
  have hEorig : ∀z∈E,z.2∈original z.1 := fun z hz => ((retained_spec original R z).mp (hE hz)).2
  have hcoarse := selected_dyadic_shading_transfer h original horiginal ha R E hE level b hdy hb
    (fun p hp => (H ⟨b,by omega⟩ p hp).2) rep
  have hfull : 0 < ∑p∈P,W p := by
    have hpos : 0 < (43*colorCost)*D.thickness^(2*zeta) := by
      exact mul_pos (mul_pos (by norm_num) colorCost_pos) (Real.rpow_pos_of_pos hd _)
    have hmass := hpos.trans_le (hselected.trans hcoarse)
    exact pos_of_mul_pos_right hmass (by positivity)
  have hTube : 0 < ∑_p∈P,(1:ℝ) := by
    simpa using (show (0:ℝ)<P.card by exact_mod_cast card_pos.mpr (hR.image _))
  obtain ⟨Q,hQP,_hQne,_hQpos,_hQrep,hsep,hret,_hden⟩ :=
    exists_dense_direction_thinning h hzeta R (2^b) (by positivity) hscale
      (fun p hp => (H ⟨b,by omega⟩ p hp).1) W (fun _ => 1)
      (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => by norm_num) hfull hTube
  have hcolor : D.thickness^(4*zeta) ≤ ∑p∈Q,W p := by
    have hh := hselected.trans (hcoarse.trans
      (mul_le_mul_of_nonneg_left hret (by positivity)))
    have hcoeff : 0 < 43*colorCost*D.thickness^(-zeta)*D.thickness^(-zeta) := by
      have hc := colorCost_pos
      positivity
    have hpow : D.thickness^(-zeta)*D.thickness^(-zeta)*D.thickness^(4*zeta)=
        D.thickness^(2*zeta) := by
      rw [←Real.rpow_add hd,←Real.rpow_add hd]
      congr 1
      ring
    apply (mul_le_mul_iff_right₀ hcoeff).mp
    calc
      _ = (43*colorCost)*(D.thickness^(-zeta)*D.thickness^(-zeta)*D.thickness^(4*zeta)) := by ring
      _ = (43*colorCost)*D.thickness^(2*zeta) := by rw [hpow]
      _ ≤ 43*D.thickness^(-zeta)*
          (((23328*512^3:ℝ)*D.thickness^(-zeta))*(∑p∈Q,W p)) := hh
      _ = _ := by dsimp [colorCost]; ring
  obtain ⟨S,hSQ,hprune,hterminal⟩ := actual_shading_pruning (t:=8*zeta) h original horiginal ha
    R level b hdy hb h6 (fun j p hp => (H ⟨j.val,by omega⟩ p hp).1) Q hQP rep E hEorig
  have hprune' : (∑p∈Q,W p) ≤ (∑p∈S,W p)+pruneCost*((b:ℝ)+1)*D.thickness^(7*zeta) := by
    simpa only [W,pruneCost,show 8*zeta-zeta=7*zeta by ring] using hprune
  have hmass := (pruned_color_mass hd h.1.2.2.1 hzeta (le_refl b) hcolor hprune' hlog hsmall).2
  have hSne : S.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn,sum_empty] at hmass
    exact (not_le_of_gt (Real.rpow_pos_of_pos hd _)) hmass
  have hSP := hSQ.trans hQP
  exact ⟨S,hSP,hSne,fun p hp => representative_spec h R a (2^b) (hSP hp),
    fun p hp q hq hne => hsep p (hSQ hp) q (hSQ hq) hne,hmass,hterminal⟩

end NativeSparseCoarseSelection
