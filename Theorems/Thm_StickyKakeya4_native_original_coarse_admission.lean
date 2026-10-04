import Theorems.Thm_StickyKakeya4_native_original_coarse_selection
import Theorems.Thm_StickyKakeya4_native_coarse_native_admissibility
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeOriginalCoarseAdmission
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeUnitParentNormalization NativeCoarseDirectionThinning NativeCoarseCellSource
open NativeCoarseShadingCapacity NativeCoarseShadingPruning NativeCoarsePowerWindow
open NativeCoarseNativeAdmissibility NativeDyadicParentCells
open scoped BigOperators ENNReal

/-- Closed global coarse admission in the SAME fixed compact native class.
All original data and the source exponent precede scale selection. Both sides
of the power window are explicit. Coarse separation, genuine ancestor lower
counts, CW and aggregate density are derived on one actual retained family. -/
theorem original_coarse_admission {e window : ℝ} (he : 0 < e) (hw : 0 < window) :
    ∃delta0 : ℝ,0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta),
      (∀i,D.line i∈fixedCompactClass) → D.thickness ≤ delta0 → eta ≤ window*e/512 →
      ∃ (original : Fin n → Finset Index) (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
        (∀i,D.shading i=wzCellShading (mesh D) original i) ∧
        D.thickness=(2:ℝ)⁻¹^level ∧
        (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
        ∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^window →
          D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^window →
          let rep := representative h R a (2^m)
          ∃ (Q : Finset Parent)
            (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤
              dist (direction (D.line (rep p))) (direction (D.line (rep q)))),
            Q⊆R.image (parentLabel D a (2^m)) ∧ Q.Nonempty ∧
            (∀p∈Q,rep p∈R ∧ parentLabel D a (2^m) (rep p)=p) ∧
            let S := source h a level m Q rep (retained original R) hsep
            IsWangZakharovNativeFiniteInput S e ∧
              S.thickness=64/((2^m:ℕ):ℝ) ∧ (∀i,S.line i∈fixedCompactClass) ∧
              (∀i,S.line i=NativeContractedUnitParent.line D a (0,0) (rep (parentIndex Q i))) ∧
              (∀i,S.shading i=wzCellShading (32/((2^m:ℕ):ℝ))
                (fun _ : Fin 1 => rows D a (2^m) (NativeCoarseDyadicShading.block level m)
                  rep (retained original R) (parentIndex Q i)) 0) ∧
              D.thickness^(5*(window*e/32)) ≤ (wzTotalShadingVolume S).toReal := by
  let zeta := window*e/32
  have hz : 0 < zeta := by dsimp [zeta]; positivity
  obtain ⟨dr,hdr,hselection⟩ := NativeOriginalCoarseSelection.original_coarse_selection hz
  obtain ⟨dp,hdp,_hdp1,hpower⟩ := exists_power_window_cutoff he hw
  refine ⟨min dr dp,lt_min hdr hdp,?_⟩
  intro n D eta h hK hsmall heta
  have hetaz : eta ≤ zeta/16 := by dsimp [zeta]; linarith
  obtain ⟨original,a,level,R,horiginal,hdy,ha,_hR,Horiginal,hselect⟩ :=
    hselection n D eta h hK (hsmall.trans (min_le_left _ _)) hetaz
  refine ⟨original,a,level,R,horiginal,hdy,ha,?_⟩
  intro m hcoarse hfine
  let rho := 1/((2^m:ℕ):ℝ)
  have hr : 0 < rho := by dsimp [rho]; positivity
  have hd := h.1.2.1
  have hb := hpower D.thickness rho eta hd (hsmall.trans (min_le_right _ _)) hr hcoarse hfine hetaz
  have h6 : 6 ≤ m := by
    have hpow : (64:ℝ) ≤ ((2^m:ℕ):ℝ) := by
      have hh := hb.2.1
      dsimp [rho] at hh
      rw [mul_one_div] at hh
      exact (div_le_one (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mp hh
    by_contra hn
    have hm5 : m ≤ 5 := by omega
    have hu : ((2^m:ℕ):ℝ) ≤ 32 := by
      simp only [Nat.cast_pow,Nat.cast_ofNat]
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hm5).trans_eq (by norm_num)
    linarith
  have hm : m ≤ level := by
    have hh : (1/2:ℝ)^level ≤ (1/2:ℝ)^m := by
      simpa only [hdy,rho,one_div,inv_pow,Nat.cast_pow,Nat.cast_ofNat] using hb.1
    exact (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).mp hh
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mp hb.1
    simpa only [mul_comm] using hh
  obtain ⟨Q,hQP,hQne,hQrep,hsep,hshade,Hpruned⟩ := hselect m h6 hm
  let rep := representative h R a (2^m)
  let S := source h a level m Q rep (retained original R) hsep
  have hE : ∀x∈retained original R,x.2∈original x.1 :=
    fun x hx => ((retained_spec original R x).mp hx).2
  have hpowS : (64/((2^m:ℕ):ℝ))^e ≤ D.thickness^(8*zeta) := by
    simpa only [rho,mul_one_div] using hb.2.2.1
  have hnative : IsWangZakharovNativeFiniteInput S e :=
    native_input h hK hz.le original horiginal ha R level m hdy hm h6 hscale Q hQP hQne
      rep (fun p hp => (hQrep p hp).2) (retained original R) hE hsep
      (fun p hp => (Horiginal ⟨m,by omega⟩ p hp).1)
      (fun ell p hp => (Hpruned ell p hp).1) hshade hpowS hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  refine ⟨Q,hsep,hQP,hQne,hQrep,hnative,rfl,?_,fun i => rfl,fun i => rfl,?_⟩
  · intro i
    exact NativeCoarseRepresentativeGeometry.zero_parent_mem_fixedCompactClass h hK ha (rep (parentIndex Q i))
  · rw [NativeCoarseSourceMass.source_total_shading_real]
    exact hshade

end NativeOriginalCoarseAdmission
