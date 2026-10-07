import Theorems.Thm_StickyKakeya4_native_variable_retention_coarse_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeTruncatedRetentionCoarseSelection
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeUnitParentNormalization NativeCoarseShadingCapacity
open NativeCoarseDyadicShading NativeCoarseShadingPruning NativeCoarseMassBudget
open NativeCoarseDirectionThinning NativeDyadicParentCells NativeCoarseAncestorCounts
open NativeOriginalPrunedMass NativeSameSourceCoarseSelection
open scoped BigOperators ENNReal

open NativeVariableRetentionCoarseSelection

/-- Only reference populations through the selected coarse depth are used.
The original fine shading depth stays level throughout. One cutoff is fixed from zetaMin BEFORE the source. The effective
pruning exponent and the actual retention factor may then vary with the
output scale. The same original R and E are used by coloring and pruning;
no native hypothesis is placed on the source shaded only by E. The only
retention payment is the displayed scalar inequality, which the output-
scale caller must derive from its actual mass loss. -/
theorem same_reference_coarse_selection_through {zetaMin : ℝ} (hzMin : 0 < zetaMin) :
    ∃delta0 : ℝ,0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        D.thickness ≤ delta0 → eta ≤ zetaMin/16 →
      ∀zeta F : ℝ,zetaMin ≤ zeta → 0 < F →
        (43*F*colorCost)*D.thickness^zeta ≤ 1 →
        ∀ (original : Fin n → Finset Index) (a : ℝ) (level : ℕ)
          (R : Finset (Fin n)) (E : Finset (Fin n × Index)),
        (∀i,D.shading i=wzCellShading (mesh D) original i) →
        D.thickness=(2:ℝ)⁻¹^level →
        (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
        R.Nonempty → E ⊆ retained original R →
        ((incidences original).card:ℝ) ≤ F*(E.card:ℝ) →
        ∀m : ℕ,6 ≤ m → m ≤ level →
        (∀ell : Fin (m+1),∀p : Parent,
          (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
            D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
            ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
              D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) →
          ∃S : Finset Parent,S⊆R.image (parentLabel D a (2^m)) ∧ S.Nonempty ∧
          let rep := representative h R a (2^m)
          (∀p∈S,rep p∈R ∧ parentLabel D a (2^m) (rep p)=p) ∧
          (∀p∈S,∀q∈S,p≠q → 64/((2^m:ℕ):ℝ) ≤
            dist (direction (D.line (rep p))) (direction (D.line (rep q)))) ∧
          D.thickness^(5*zeta) ≤ ∑p∈S,weight D a level m rep E p ∧
          (∀ell : Fin (m+1),∀p : Parent,
            (S.filter (fun q => ancestor m ell.val q=p)).Nonempty →
              D.thickness^(8*zeta)*(((2^m:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
                ((S.filter (fun q => ancestor m ell.val q=p)).card:ℝ) ∧
              ((S.filter (fun q => ancestor m ell.val q=p)).card:ℝ) ≤
                D.thickness^(-2*zeta)*(((2^m:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3) := by
  obtain ⟨delta0,hd0,_hd01,hbudget,hmass⟩ := exists_mass_cutoff hzMin
  refine ⟨delta0,hd0,?_⟩
  intro n D eta h hsmall heta zeta F hz hF habsorb original a level R E
    horiginal hdy ha hR hE hret m h6 hm H
  have hzeta : 0 < zeta := hzMin.trans_le hz
  have hd := h.1.2.1
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    have hh : ((2^m:ℕ):ℝ) ≤ ((2^level:ℕ):ℝ) := by
      simp only [Nat.cast_pow,Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num) hm
    exact (mul_le_mul_of_nonneg_right hh hd.le).trans_eq (dyadic_fine_scale hdy)
  let P := R.image (parentLabel D a (2^m))
  let rep := representative h R a (2^m)
  let W := weight D a level m rep E
  have hEorig : ∀x∈E,x.2∈original x.1 :=
    fun x hx => ((retained_spec original R x).mp (hE hx)).2
  have hW : ∀p∈P,0 ≤ W p := fun _ _ => ENNReal.toReal_nonneg
  have hsource0 := hmass n D eta h hsmall heta
  have hsource : D.thickness^zeta ≤ (wzTotalShadingVolume D).toReal :=
    (Real.rpow_le_rpow_of_exponent_ge hd h.1.2.2.1 hz).trans hsource0
  have hmassret := original_mass_le_selected_real h original horiginal E F hret
  have hcoarse := selected_dyadic_shading_transfer h original horiginal ha R E hE level m hdy hm
    (fun p hp => (H ⟨m,by omega⟩ p hp).2) rep
  change (E.card:ℝ)*(D.thickness/2)^4 ≤ 43*D.thickness^(-zeta)*(∑p∈P,W p) at hcoarse
  have hfull : 0 < ∑p∈P,W p := by
    have hp := Real.rpow_pos_of_pos hd zeta
    have hpositive : 0 < (E.card:ℝ)*(D.thickness/2)^4 := by nlinarith
    have hf := Real.rpow_pos_of_pos hd (-zeta)
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 43) hf.le) (le_of_not_gt hn)
    linarith
  have hP : P.Nonempty := hR.image _
  have hTube : 0 < ∑_p∈P,(1:ℝ) := by
    simpa using (show (0:ℝ)<P.card by exact_mod_cast card_pos.mpr hP)
  obtain ⟨Q,hQP,_hQ,_hQpos,_hQrep,hQsep,hQret,_hQden⟩ :=
    exists_dense_direction_thinning h hzeta.le R (2^m) (by positivity) hscale
      (fun p hp => (H ⟨m,by omega⟩ p hp).1) W (fun _ => 1) hW
      (fun _ _ => by norm_num) hfull hTube
  have hc := hbudget D.thickness level hd hsmall hdy
  have hlog : 2*pruneCost*((level:ℝ)+1) ≤ D.thickness^(-zeta) :=
    hc.2.2.trans (Real.rpow_le_rpow_of_exponent_ge hd h.1.2.2.1 (neg_le_neg hz))
  have htwo : 2*D.thickness^zeta ≤ 1 :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hd h.1.2.2.1 hz) (by norm_num)).trans hc.2.1
  have hQmass : D.thickness^(4*zeta) ≤ ∑p∈Q,W p :=
    selected_color_mass hd hF hmassret hsource hcoarse hQret habsorb
  obtain ⟨S,hSQ,hSret,hTerminal⟩ := actual_shading_pruning (t:=8*zeta) h original horiginal ha R level m hdy hm h6
    (fun ell p hp => (H ⟨ell.val,by omega⟩ p hp).1) Q hQP rep E hEorig
  have hSret' : (∑p∈Q,W p) ≤ (∑p∈S,W p)+pruneCost*((m:ℝ)+1)*D.thickness^(7*zeta) := by
    simpa only [W,pruneCost,show 8*zeta-zeta=7*zeta by ring] using hSret
  have hMass := pruned_color_mass hd h.1.2.2.1 hzeta.le hm hQmass hSret' hlog htwo
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
    (coarse_ancestor_AD h R a zeta m H (by omega) le_rfl p (hp.mono hsub)).2

end NativeTruncatedRetentionCoarseSelection
