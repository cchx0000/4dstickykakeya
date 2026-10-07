import Theorems.Thm_StickyKakeya4_native_same_source_coarse_selection
import Theorems.Thm_StickyKakeya4_native_coarse_native_admissibility
import Theorems.Thm_StickyKakeya4_native_full_coarse_shadow
import Theorems.Thm_StickyKakeya4_native_fixed_compact_multiplicity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeSameSourceCoarseAdmission
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeUnitParentNormalization NativeCoarseDirectionThinning
open NativeCoarseCellSource NativeCoarseShadingCapacity NativeCoarseShadingPruning NativeCoarsePowerWindow
open NativeCoarseNativeAdmissibility NativeDyadicParentCells NativeFullCoarseShadow
open scoped BigOperators ENNReal

/-- On prescribed original R and selected E, admit a literal coarse source
and transfer its multiplicity bound to the complete same-E coarse shadow.
Original H and global incidence retention are the only extra source premises. -/
theorem same_source_coarse_admission {e window : ℝ} (he : 0 < e) (hw : 0 < window)
    (F : ℕ) (hF : 0 < F) :
    ∃delta0 : ℝ,0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta),
      (∀i,D.line i∈fixedCompactClass) → D.thickness ≤ delta0 → eta ≤ window*e/512 →
      ∀ (original : Fin n → Finset Index) (a : ℝ) (level : ℕ)
        (R : Finset (Fin n)) (E : Finset (Fin n × Index)),
        (∀i,D.shading i=wzCellShading (mesh D) original i) →
        D.thickness=(2:ℝ)⁻¹^level →
        (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
        R.Nonempty → E ⊆ retained original R →
        (incidences original).card ≤ F*E.card →
        (∀ell : Fin (level+1),∀p : Parent,
          (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
            D.thickness^(window*e/32)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
            ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
              D.thickness^(-(window*e/32))*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) →
        ∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^window →
          D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^window →
          let rep := representative h R a (2^m)
          ∃ (Q : Finset Parent)
            (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤
              dist (direction (D.line (rep p))) (direction (D.line (rep q)))),
            Q⊆R.image (parentLabel D a (2^m)) ∧ Q.Nonempty ∧
            let S := source h a level m Q rep E hsep
            IsWangZakharovNativeFiniteInput S e ∧ (∀i,S.line i∈fixedCompactClass) ∧
              (ENNReal.ofReal D.thickness).rpow (7*(window*e/32))*
                NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E) ≤
                  NativeFiniteKakeyaCounts.multiplicity S ∧
              D.thickness^(5*(window*e/32)) ≤ (wzTotalShadingVolume S).toReal := by
  let zeta := window*e/32
  have hz : 0 < zeta := by dsimp [zeta]; positivity
  obtain ⟨dr,hdr,hselection⟩ := NativeSameSourceCoarseSelection.same_source_coarse_selection hz F hF
  obtain ⟨dp,hdp,_hdp1,hpower⟩ := exists_power_window_cutoff he hw
  refine ⟨min dr dp,lt_min hdr hdp,?_⟩
  intro n D eta h hK hsmall heta original a level R E horiginal hdy ha hR hE hret Horiginal m hcoarse hfine
  have hetaz : eta ≤ zeta/16 := by dsimp [zeta]; linarith
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
  obtain ⟨Q,hQP,hQne,hQrep,hsep,hshade,Hpruned⟩ :=
    hselection n D eta h (hsmall.trans (min_le_left _ _)) hetaz
      original a level R E horiginal hdy ha hR hE hret Horiginal m h6 hm
  let rep := representative h R a (2^m)
  let S := source h a level m Q rep E hsep
  have hEorig : ∀x∈E,x.2∈original x.1 :=
    fun x hx => ((retained_spec original R x).mp (hE hx)).2
  have hpowS : (64/((2^m:ℕ):ℝ))^e ≤ D.thickness^(8*zeta) := by
    simpa only [rho,mul_one_div] using hb.2.2.1
  have hnative : IsWangZakharovNativeFiniteInput S e :=
    native_input h hK hz.le original horiginal ha R level m hdy hm h6 hscale Q hQP hQne
      rep (fun p hp => (hQrep p hp).2) E hEorig hsep
      (fun p hp => (Horiginal ⟨m,by omega⟩ p hp).1)
      (fun ell p hp => (Hpruned ell p hp).1) hshade hpowS hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  refine ⟨Q,hsep,hQP,hQne,hnative,?_,?_,?_⟩
  · intro i
    exact NativeCoarseRepresentativeGeometry.zero_parent_mem_fixedCompactClass h hK ha (rep (parentIndex Q i))
  · exact full_multiplicity_le_core h original horiginal ha R level m hdy hm h6 E hEorig
      (fun p hp => (Horiginal ⟨m,by omega⟩ p hp).1) Q hQP hsep hshade hb.2.2.2.2.1
  · rw [NativeCoarseSourceMass.source_total_shading_real]
    exact hshade

/-- Fixed-compact extremality bounds the full coarse shadow of prescribed
R and E, uniformly at every scale in the power window. The family and selected
incidences may come from the joint local core: neither is chosen again here. -/
theorem same_source_full_coarse_upper {epsilon window : ℝ} (heps : 0 < epsilon)
    (hw : 0 < window) (F : ℕ) (hF : 0 < F) :
    ∃ e eta0 delta0 : ℝ,0 < e ∧ 0 < eta0 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → D.thickness ≤ delta0 → eta ≤ eta0 →
        ∀ (original : Fin n → Finset Index) (a : ℝ) (level : ℕ)
          (R : Finset (Fin n)) (E : Finset (Fin n × Index)),
          (∀i,D.shading i=wzCellShading (mesh D) original i) →
          D.thickness=(2:ℝ)⁻¹^level →
          (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
          R.Nonempty → E ⊆ retained original R →
          (incidences original).card ≤ F*E.card →
          (∀ell : Fin (level+1),∀p : Parent,
            (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
              D.thickness^(window*e/32)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
                ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
                D.thickness^(-(window*e/32))*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) →
          ∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^window →
            D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^window →
            (ENNReal.ofReal D.thickness).rpow (7*(window*e/32))*
              NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E) ≤
                (ENNReal.ofReal (64/((2^m:ℕ):ℝ))).rpow
                  (-NativeFixedCompactKakeyaExponent.extremalExponent-epsilon) := by
  obtain ⟨e,he,dv,hdv,hupper⟩ := NativeFixedCompactMultiplicity.fixed_compact_multiplicity_upper heps
  obtain ⟨da,hda,hadmit⟩ := same_source_coarse_admission he hw F hF
  obtain ⟨ds,hds,_hds1,hscale⟩ := exists_positive_rpow_absorption_threshold hw
    (show 0 ≤ 64/dv by positivity) (by norm_num : (0:ℝ)<1)
  refine ⟨e,window*e/512,min da ds,he,by positivity,lt_min hda hds,?_⟩
  intro n D eta h hK hsmall heta original a level R E horiginal hdy ha hR hE hret H m hcoarse hfine
  obtain ⟨Q,hsep,_hQP,_hQne,hS,hSK,hfull,_hshade⟩ :=
    hadmit n D eta h hK (hsmall.trans (min_le_left _ _)) heta
      original a level R E horiginal hdy ha hR hE hret H m hcoarse hfine
  let rep := representative h R a (2^m)
  let S := source h a level m Q rep E hsep
  have hsmallS : S.thickness ≤ dv := by
    have hh := hscale D.thickness h.1.2.1 (hsmall.trans (min_le_right _ _))
    have heq : (64/dv)*D.thickness^window=(64*D.thickness^window)/dv := by ring
    rw [heq] at hh
    change 64/((2^m:ℕ):ℝ) ≤ dv
    calc
      _ = 64*(1/((2^m:ℕ):ℝ)) := by ring
      _ ≤ 64*D.thickness^window := mul_le_mul_of_nonneg_left hcoarse (by norm_num)
      _ ≤ _ := (div_le_one hdv).mp hh
  exact hfull.trans (by simpa only [S,source_thickness] using hupper Q.card S hsmallS hS hSK)

end NativeSameSourceCoarseAdmission
