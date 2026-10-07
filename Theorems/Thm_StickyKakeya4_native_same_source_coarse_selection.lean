import Theorems.Thm_StickyKakeya4_native_coarse_mass_budget
import Theorems.Thm_StickyKakeya4_native_coarse_direction_thinning

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeSameSourceCoarseSelection
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeUnitParentNormalization NativeCoarseShadingCapacity
open NativeCoarseDyadicShading NativeCoarseShadingPruning NativeCoarseMassBudget
open NativeCoarseDirectionThinning NativeDyadicParentCells NativeCoarseAncestorCounts
open NativeOriginalPrunedMass
open scoped BigOperators ENNReal

/-- The coarse shading consists of the image of the literal selected incidences E.
Its mass follows from original parent populations and cell-fiber capacity. -/
theorem selected_dyadic_shading_transfer {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index))
    (hE : E ⊆ retained original R) (level m : ℕ)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level)
    (H : ∀p : Parent,(R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty →
      ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ) ≤
        D.thickness^(-zeta)*((1/((2^m:ℕ):ℝ))/D.thickness)^3)
    (rep : Parent → Fin n) :
    (E.card:ℝ)*(D.thickness/2)^4 ≤ 43*D.thickness^(-zeta)*
      ∑p∈R.image (parentLabel D a (2^m)),weight D a level m rep E p := by
  have hER : ∀x∈E,x.1∈R ∧ x.2∈original x.1 :=
    fun x hx => (retained_spec original R x).mp (hE hx)
  have hP : ∀x∈E,parentLabel D a (2^m) x.1∈R.image (parentLabel D a (2^m)) :=
    fun x hx => mem_image_of_mem _ (hER x hx).1
  have hM : ∀p∈R.image (parentLabel D a (2^m)),
      ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ) ≤
        D.thickness^(-zeta)*((1/((2^m:ℕ):ℝ))/D.thickness)^3 := by
    intro p hp
    obtain ⟨i,hi,hip⟩ := mem_image.mp hp
    exact H p ⟨i,mem_filter.mpr ⟨hi,hip⟩⟩
  have hc := cell_mass_scale_cancellation h.1.2.1
    (by positivity : (0:ℝ)<1/((2^m:ℕ):ℝ)) (Real.rpow_pos_of_pos h.1.2.1 (-zeta)).le
    (by positivity : (0:ℝ)≤(coarse D a (2^m) (block level m) rep E).card)
    (block_scale hdy hm)
    (total_incidence_capacity h original horiginal ha R (2^m) (block level m)
      (block_pos level m) rep E hER hM)
  rw [←coarse_shading_real h.1.2.1 a (2^m) (block level m) (block_pos level m) rep E _ hP,
    block_mesh hdy hm] at hc
  exact hc

/-- Global cardinal retention is exactly global shading-mass retention on
one original cubical mesh. No output density premise enters this identity. -/
theorem original_mass_le_selected {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (E : Finset (Fin n × Index)) (F : ℕ)
    (hret : (incidences original).card ≤ F*E.card) :
    (wzTotalShadingVolume D).toReal ≤ (F:ℝ)*((E.card:ℝ)*(D.thickness/2)^4) := by
  rw [total_shading_eq_incidence_volume D (half_pos h.1.2.1) original horiginal]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (half_pos h.1.2.1).le]
  have hh : ((incidences original).card:ℝ) ≤ (F:ℝ)*(E.card:ℝ) := by exact_mod_cast hret
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh
    (pow_nonneg (half_pos h.1.2.1).le 4)

/-- A fixed finite-menu incidence loss is absorbed into the cutoff, with
no change to the original-delta exponent of the selected coarse color. -/
lemma selected_color_mass {delta zeta old selected full chosen F : ℝ}
    (hd : 0 < delta) (hF : 0 < F) (hret : old ≤ F*selected)
    (hsource : delta^zeta ≤ old)
    (hcoarse : selected ≤ 43*delta^(-zeta)*full)
    (hcolor : full ≤ colorCost*delta^(-zeta)*chosen)
    (hsmall : (43*F*colorCost)*delta^zeta ≤ 1) : delta^(4*zeta) ≤ chosen := by
  let C := 43*F*colorCost
  have hcross : delta^zeta ≤ (C*delta^(-2*zeta))*chosen := by
    calc
      _ ≤ old := hsource
      _ ≤ F*selected := hret
      _ ≤ F*(43*delta^(-zeta)*full) := mul_le_mul_of_nonneg_left hcoarse hF.le
      _ ≤ F*(43*delta^(-zeta)*(colorCost*delta^(-zeta)*chosen)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcolor (by positivity)) hF.le
      _ = _ := by
        rw [show -2*zeta=(-zeta)+(-zeta) by ring,Real.rpow_add hd]
        dsimp [C]
        ring
  have hbase : (C*delta^(-2*zeta))*delta^(4*zeta) ≤ delta^zeta := by
    calc
      _ = (C*delta^zeta)*delta^zeta := by
        rw [mul_assoc,←Real.rpow_add hd,show -2*zeta+4*zeta=zeta+zeta by ring,Real.rpow_add hd]
        ring
      _ ≤ 1*delta^zeta := mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hd _).le
      _ = _ := one_mul _
  have hp : 0 < C*delta^(-2*zeta) := by
    have hc := colorCost_pos
    dsimp [C]
    positivity
  exact (mul_le_mul_iff_right₀ hp).mp (hbase.trans hcross)

/-- Deterministic coarse selection on prescribed original labels R and
prescribed selected incidences E. Only original native input, original
ancestor counts, and the global E-card retention are required. In particular,
this theorem never invokes a constructor that might replace R or E. -/
theorem same_source_coarse_selection {zeta : ℝ} (hzeta : 0 < zeta)
    (F : ℕ) (hF : 0 < F) :
    ∃delta0 : ℝ,0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        D.thickness ≤ delta0 → eta ≤ zeta/16 →
        ∀ (original : Fin n → Finset Index) (a : ℝ) (level : ℕ)
          (R : Finset (Fin n)) (E : Finset (Fin n × Index)),
          (∀i,D.shading i=wzCellShading (mesh D) original i) →
          D.thickness=(2:ℝ)⁻¹^level →
          (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
          R.Nonempty → E ⊆ retained original R →
          (incidences original).card ≤ F*E.card →
          (∀ell : Fin (level+1),∀p : Parent,
            (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
              D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
                ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
                D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) →
          ∀m : ℕ,6 ≤ m → m ≤ level →
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
  obtain ⟨dm,hdm,_hdmSmall,hbudget,hmass⟩ := exists_mass_cutoff hzeta
  have hFr : (0:ℝ)<F := by exact_mod_cast hF
  obtain ⟨df,hdf,_hdf1,hfactor⟩ := exists_positive_rpow_absorption_threshold hzeta
    (show 0 ≤ 43*(F:ℝ)*colorCost by exact (mul_pos (mul_pos (by norm_num) hFr) colorCost_pos).le)
    (by norm_num : (0:ℝ)<1)
  refine ⟨min dm df,lt_min hdm hdf,?_⟩
  intro n D eta h hsmall heta original a level R E horiginal hdy ha hR hE hret H m h6 hm
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
  have hsource := hmass n D eta h (hsmall.trans (min_le_left _ _)) heta
  have hmassret := original_mass_le_selected h original horiginal E F hret
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
  have hc := hbudget D.thickness level hd (hsmall.trans (min_le_left _ _)) hdy
  have hQmass : D.thickness^(4*zeta) ≤ ∑p∈Q,W p :=
    selected_color_mass hd hFr hmassret hsource hcoarse hQret
      (hfactor D.thickness hd (hsmall.trans (min_le_right _ _)))
  obtain ⟨S,hSQ,hSret,hTerminal⟩ := actual_shading_pruning (t:=8*zeta) h original horiginal ha R level m hdy hm h6
    (fun ell p hp => (H ⟨ell.val,by omega⟩ p hp).1) Q hQP rep E hEorig
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
    (coarse_ancestor_AD h R a zeta level H (by omega) hm p (hp.mono hsub)).2

end NativeSameSourceCoarseSelection
