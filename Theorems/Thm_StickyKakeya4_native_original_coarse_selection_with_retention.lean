import Theorems.Thm_StickyKakeya4_native_coarse_mass_budget
import Theorems.Thm_StickyKakeya4_native_coarse_cell_source
import Theorems.Thm_StickyKakeya4_native_coarse_direction_thinning
import Theorems.Thm_StickyKakeya4_native_dense_retained_unit_parent
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000
noncomputable section
namespace NativeOriginalCoarseSelectionWithRetention
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeUnitParentNormalization NativeCoarseShadingCapacity NativeCoarseDyadicShading
open NativeCoarseShadingPruning NativeCoarseMassBudget NativeCoarseDirectionThinning
open NativeDyadicParentCells NativeCoarseAncestorCounts NativeOriginalPrunedMass
open scoped BigOperators ENNReal

/-- From one actual original fixed-K0 native source, construct a direction
color and a shading-retaining pruned subset at EVERY intermediate dyadic
scale. The same original representatives, actual cube shadings and true
ancestor populations are retained together. No new-scale profile is assumed. -/
theorem original_coarse_selection_with_retention {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃delta0 : ℝ,0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta), (∀i,D.line i∈fixedCompactClass) →
      D.thickness ≤ delta0 → eta ≤ zeta/16 →
      ∃ (original : Fin n → Finset Index) (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
        (∀i,D.shading i=wzCellShading (mesh D) original i) ∧
        D.thickness=(2:ℝ)⁻¹^level ∧
        (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
        R.Nonempty ∧ wzTotalShadingVolume D ≤ 2*shadingMass D R ∧
        (∀ell : Fin (level+1),∀p : Parent,
          (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
            D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
            ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
              D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) ∧
        ∀m : ℕ,6 ≤ m → m ≤ level →
          ∃S : Finset Parent,S⊆R.image (parentLabel D a (2^m)) ∧ S.Nonempty ∧
            let rep := representative h R a (2^m)
            (∀p∈S,rep p∈R ∧ parentLabel D a (2^m) (rep p)=p) ∧
            (∀p∈S,∀q∈S,p≠q → 64/((2^m:ℕ):ℝ) ≤
              dist (direction (D.line (rep p))) (direction (D.line (rep q)))) ∧
            D.thickness^(5*zeta) ≤ ∑p∈S,weight D a level m rep (retained original R) p ∧
            (∀ell : Fin (m+1),∀p : Parent,
              (S.filter (fun q => ancestor m ell.val q=p)).Nonempty →
                D.thickness^(8*zeta)*(((2^m:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
                  ((S.filter (fun q => ancestor m ell.val q=p)).card:ℝ) ∧
                ((S.filter (fun q => ancestor m ell.val q=p)).card:ℝ) ≤
                  D.thickness^(-2*zeta)*(((2^m:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3) := by
  obtain ⟨dr,hdr,hregular⟩ := compact_original_coarse_ancestor_counts
    fixedCompactClass fixedCompactClass_compact hzeta
  obtain ⟨dm,hdm,_hdmSmall,hbudget,hmass⟩ := exists_mass_cutoff hzeta
  refine ⟨min dr dm,lt_min hdr hdm,?_⟩
  intro n D eta h hK hsmall heta
  obtain ⟨original,horiginal⟩ := input_exists_common_cells h
  obtain ⟨a,level,R,hdy,ha,hR,_hhalf,hshade,_hden,H,_hSlope,hAncestor⟩ :=
    hregular n D eta h hK (hsmall.trans (min_le_left _ _)) heta
  refine ⟨original,a,level,R,horiginal,hdy,ha,hR,hshade,H,?_⟩
  intro m h6 hm
  have hd := h.1.2.1
  have hN : 0 < 2^m := by positivity
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    have hh : ((2^m:ℕ):ℝ) ≤ ((2^level:ℕ):ℝ) := by
      simp only [Nat.cast_pow,Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num) hm
    exact (mul_le_mul_of_nonneg_right hh hd.le).trans_eq (dyadic_fine_scale hdy)
  let P := R.image (parentLabel D a (2^m))
  let rep := representative h R a (2^m)
  let W := weight D a level m rep (retained original R)
  have hE : ∀e∈retained original R,e.2∈original e.1 :=
    fun e he => ((retained_spec original R e).mp he).2
  have hW : ∀p∈P,0 ≤ W p := fun _ _ => ENNReal.toReal_nonneg
  have hsource := hmass n D eta h (hsmall.trans (min_le_right _ _)) heta
  have hret : (wzTotalShadingVolume D).toReal ≤ 2*∑i∈R,(volume (D.shading i)).toReal := by
    have hf : (2:ℝ≥0∞)*shadingMass D R≠⊤ := by
      exact ENNReal.mul_ne_top (by norm_num) (shadingMass_ne_top h R)
    have hh := ENNReal.toReal_mono hf hshade
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat] at hh
    rw [←NativeDenseRetainedUnitParent.realShadingMass_eq_toReal h R] at hh
    exact hh
  have hcoarse := original_dyadic_shading_transfer h original horiginal ha R level hdy
    (fun ell p hp => (H ell p hp).2) m hm rep
  rw [block_mesh hdy hm] at hcoarse
  change (∑i∈R,(volume (D.shading i)).toReal) ≤ 43*D.thickness^(-zeta)*(∑p∈P,W p) at hcoarse
  have hfull : 0 < ∑p∈P,W p := by
    have hp := Real.rpow_pos_of_pos hd zeta
    have hf := Real.rpow_pos_of_pos hd (-zeta)
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 43) hf.le) (le_of_not_gt hn)
    linarith
  have hP : P.Nonempty := hR.image _
  have hTube : 0 < ∑_p∈P,(1:ℝ) := by simpa using (show (0:ℝ)<P.card by exact_mod_cast card_pos.mpr hP)
  obtain ⟨Q,hQP,_hQ,_hQpos,_hQrep,hQsep,hQret,_hQden⟩ := exists_dense_direction_thinning h hzeta.le R (2^m) hN hscale
    (fun p hp => (H ⟨m,by omega⟩ p hp).1) W (fun _ => 1) hW (fun _ _ => by norm_num) hfull hTube
  have hc := hbudget D.thickness level hd (hsmall.trans (min_le_right _ _)) hdy
  have hQmass : D.thickness^(4*zeta) ≤ ∑p∈Q,W p :=
    chosen_color_mass hd hret hsource hcoarse hQret hc.1
  obtain ⟨S,hSQ,hSret,hTerminal⟩ := actual_shading_pruning (t:=8*zeta) h original horiginal ha R level m hdy hm h6
    (fun ell p hp => (H ⟨ell.val,by omega⟩ p hp).1) Q hQP rep (retained original R) hE
  have hSret' : (∑p∈Q,W p) ≤ (∑p∈S,W p)+pruneCost*((m:ℝ)+1)*D.thickness^(7*zeta) := by
    simpa only [W,pruneCost,show 8*zeta-zeta=7*zeta by ring] using hSret
  have hMass := pruned_color_mass hd h.1.2.2.1 hzeta.le hm hQmass hSret' hc.2.2 hc.2.1
  have hSnonempty : S.Nonempty := by
    by_contra hn
    have hs0 := not_nonempty_iff_eq_empty.mp hn
    have hh := hMass.2
    rw [hs0,sum_empty] at hh
    exact (not_le_of_gt (Real.rpow_pos_of_pos hd _)) hh
  have hSP : S⊆P := hSQ.trans hQP
  refine ⟨S,hSP,hSnonempty,fun p hp => representative_spec h R a (2^m) (hSP hp),
    fun p hp q hq hneq => hQsep p (hSQ hp) q (hSQ hq) hneq,hMass.2,?_⟩
  intro ell p hp
  refine ⟨hTerminal ell p hp,?_⟩
  have hsub : S.filter (fun q => ancestor m ell.val q=p)⊆descendants D R a m ell.val p :=
    filter_subset_filter _ hSP
  exact (show ((S.filter (fun q => ancestor m ell.val q=p)).card:ℝ) ≤
      (descendants D R a m ell.val p).card by exact_mod_cast card_le_card hsub).trans
    (hAncestor ell.val m (by omega) hm p (hp.mono hsub)).2

end NativeOriginalCoarseSelectionWithRetention
