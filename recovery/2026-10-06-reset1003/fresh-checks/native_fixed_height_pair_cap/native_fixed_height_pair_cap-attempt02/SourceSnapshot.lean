import Theorems.Thm_StickyKakeya4_native_configured_slice_occupancy
import Theorems.Thm_StickyKakeya4_native_capped_old_ancestors
import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds
import Theorems.Thm_StickyKakeya4_native_packed_frame_isometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeFixedHeightPairCap
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeFullCoarseShadow OriginalWWitnessCounts
open NativeConfiguredSliceOccupancy NativeFullReferenceSlopeCap NativeCappedOldAncestors
open NativeCoarseDirectionThinning NativeCoarseCellSource

/-- At one literal height, each distinct geometric pair is counted once by
its actual tube. No number of height bins enters this estimate. -/
theorem same_height_card_le {P T H : Type*} [DecidableEq P] [DecidableEq T]
    [DecidableEq H] (I : Finset (P × T)) (height : P → H) (z : H) {C : ℝ}
    (hheight : ∀p t, (p,t)∈I → height p=z)
    (hpoints : ∀t, ((pointsAt I height t z).card:ℝ) ≤ C) :
    (I.card:ℝ) ≤ C*(TwoTubePathCollisionCount.tubes I).card := by
  have hf (t : T) : ((I.filter (fun e => e.2=t)).card:ℝ) ≤ C := by
    have hc : (I.filter (fun e => e.2=t)).card ≤ (pointsAt I height t z).card := by
      apply card_le_card_of_injOn Prod.fst
      · intro e he
        obtain ⟨heI,het⟩ := mem_filter.mp he
        apply (mem_pointsAt I height t z e.1).mpr
        exact ⟨by simpa only [het] using (show (e.1,e.2)∈I from heI),
          hheight e.1 e.2 heI⟩
      · intro e he f hf hef
        exact Prod.ext hef ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm)
    exact (show ((I.filter (fun e => e.2=t)).card:ℝ) ≤ (pointsAt I height t z).card by
      exact_mod_cast hc).trans (hpoints t)
  calc
    _ = ∑t∈I.image Prod.snd, ((I.filter (fun e => e.2=t)).card:ℝ) := by
      exact_mod_cast card_eq_sum_card_image Prod.snd I
    _ ≤ ∑_t∈I.image Prod.snd, C := sum_le_sum (fun t _ht => hf t)
    _ = _ := by simp only [sum_const,TwoTubePathCollisionCount.tubes]; ring

/-- The fixed-height inverse-pair bound comes from the actual point
separation and the same-reference angular population. The complete coarse
family is used only for an upper bound on the actual subset of tube labels. -/
theorem full_source_old_slope_cube {n : ℕ} {D : FiniteScaleSource n} {eta e a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (level b : ℕ) (hb : 8 ≤ b) (E : Finset (Fin n × Index))
    (hscale : ((2^b:ℕ):ℝ)*D.thickness ≤ 1)
    (H : ∀p : Parent, (R.filter (fun i => parentLabel D a (2^b) i=p)).Nonempty →
      D.thickness^e*((1/((2^b:ℕ):ℝ))/D.thickness)^3 ≤
        ((R.filter (fun i => parentLabel D a (2^b) i=p)).card:ℝ))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4, O x (3:Fin 4)=x 3)
    (I : Finset (E4 × Fin (R.image (parentLabel D a (2^b))).card))
    (hI : ∀x i, (x,i)∈I → x∈markedUnitTube
      (MarkedIsometricChart.line O 0 ((fullSource h R a level b E).line i))
      (64/((2^b:ℕ):ℝ)))
    (hsep : ∀x∈I.image Prod.fst, ∀y∈I.image Prod.fst, x≠y →
      64/((2^b:ℕ):ℝ) ≤ dist x y)
    (z : ℝ) (hheight : ∀x i, (x,i)∈I → x 3=z)
    {rho : ℝ} (hrho : 64/((2^b:ℕ):ℝ) ≤ rho) (corner : Fin 3 → ℝ)
    (hbox : ∀i∈I.image Prod.snd, ∀j : Fin 3,
      corner j ≤ slope ((fullSource h R a level b E).line i) j ∧
      slope ((fullSource h R a level b E).line i) j ≤ corner j+rho) :
    (I.card:ℝ) ≤ (130^3*5832*66^3:ℝ)*D.thickness^(-e)*
      (rho/(64/((2^b:ℕ):ℝ)))^3 := by
  have hdref : 0 < D.thickness := h.1.2.1
  have hp := same_height_card_le I (fun x => x 3) z hheight
    (fun i => full_source_pointsAt h R a level b hb E O hO I hI hsep i z)
  have hN : (0:ℝ) < ((2^b:ℕ):ℝ) := by positivity
  have hd : (0:ℝ) < 64/((2^b:ℕ):ℝ) := by positivity
  have ht := full_subset_cube_card h R level b E hscale H (I.image Prod.snd)
    (hd.le.trans hrho) corner hbox
  have hratio : 1 ≤ rho/(64/((2^b:ℕ):ℝ)) :=
    (le_div_iff₀ hd).mpr (by simpa only [one_mul] using hrho)
  have he : ((2^b:ℕ):ℝ)*rho=64*(rho/(64/((2^b:ℕ):ℝ))) := by
    field_simp [hN.ne']
  have hside : ((2^b:ℕ):ℝ)*rho+2 ≤ 66*(rho/(64/((2^b:ℕ):ℝ))) := by
    nlinarith only [hratio,he]
  have hpow := pow_le_pow_left₀ (show 0 ≤ ((2^b:ℕ):ℝ)*rho+2 by
    have := hd.le.trans hrho; positivity) hside 3
  have hcount : ((I.image Prod.snd).card:ℝ) ≤
      (5832*66^3:ℝ)*D.thickness^(-e)*(rho/(64/((2^b:ℕ):ℝ)))^3 := by
    calc
      _ ≤ 5832*D.thickness^(-e)*(((2^b:ℕ):ℝ)*rho+2)^3 := ht
      _ ≤ 5832*D.thickness^(-e)*(66*(rho/(64/((2^b:ℕ):ℝ))))^3 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (130^3:ℝ)*(TwoTubePathCollisionCount.tubes I).card := hp
    _ ≤ (130^3:ℝ)*((5832*66^3:ℝ)*D.thickness^(-e)*
        (rho/(64/((2^b:ℕ):ℝ)))^3) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

/-- The literal old representative's parent floor label supplies the angular
cube. This bounds the entire fixed-height parent fiber; any further coarse
point restriction is a subset and introduces no additional factor. -/
theorem full_source_old_parent_height_fiber {n : ℕ} {D : FiniteScaleSource n} {eta e a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (level b : ℕ) (hb : 8 ≤ b) (E : Finset (Fin n × Index))
    (hscale : ((2^b:ℕ):ℝ)*D.thickness ≤ 1)
    (H : ∀p : Parent, (R.filter (fun i => parentLabel D a (2^b) i=p)).Nonempty →
      D.thickness^e*((1/((2^b:ℕ):ℝ))/D.thickness)^3 ≤
        ((R.filter (fun i => parentLabel D a (2^b) i=p)).card:ℝ))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4, O x (3:Fin 4)=x 3)
    (I : Finset (E4 × Fin (R.image (parentLabel D a (2^b))).card))
    (hI : ∀x i, (x,i)∈I → x∈markedUnitTube
      (MarkedIsometricChart.line O 0 ((fullSource h R a level b E).line i))
      (64/((2^b:ℕ):ℝ)))
    (hsep : ∀x∈I.image Prod.fst, ∀y∈I.image Prod.fst, x≠y →
      64/((2^b:ℕ):ℝ) ≤ dist x y)
    (c : ℕ) (hc : c ≤ b) {rho : ℝ}
    (hrho : 64/((2^b:ℕ):ℝ) ≤ rho) (hstep : 1/((2^c:ℕ):ℝ) ≤ rho)
    (z : ℝ) (q : Parent) :
    ((I.filter (fun v => v.1 3=z ∧ oldAncestor D R a b c v.2=q)).card:ℝ) ≤
        (130^3*5832*66^3:ℝ)*D.thickness^(-e)*(rho/(64/((2^b:ℕ):ℝ)))^3 := by
  let A := I.filter (fun v => v.1 3=z ∧ oldAncestor D R a b c v.2=q)
  have hAI : A⊆I := filter_subset _ _
  have hNr : (0:ℝ) < ((2^c:ℕ):ℝ) := by positivity
  apply full_source_old_slope_cube h R level b hb E hscale H O hO A
    (fun x i hi => hI x i (hAI hi))
    (fun x hx y hy hxy => hsep x (image_subset_image hAI hx) y (image_subset_image hAI hy) hxy)
    z (fun x i hi => (mem_filter.mp hi).2.1) hrho (fun j => (q.1 j:ℝ)/((2^c:ℕ):ℝ))
  intro i hi j
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
  let rep := representative h R a (2^b) (parentIndex (R.image (parentLabel D a (2^b))) v.2)
  have he : parentLabel D a (2^c) rep=q :=
    (representative_readback h R a b c hc v.2).trans (mem_filter.mp hv).2.2
  have hf : ⌊((2^c:ℕ):ℝ)*slope (D.line rep) j⌋=q.1 j := congrFun (congrArg Prod.fst he) j
  have hlo := Int.floor_le (((2^c:ℕ):ℝ)*slope (D.line rep) j)
  have hhi := Int.lt_floor_add_one (((2^c:ℕ):ℝ)*slope (D.line rep) j)
  rw [hf] at hlo hhi
  simp only [full_slope]
  constructor
  · exact (div_le_iff₀ hNr).mpr (by simpa only [mul_comm] using hlo)
  · have hupper : slope (D.line rep) j < ((q.1 j:ℝ)+1)/((2^c:ℕ):ℝ) :=
      (lt_div_iff₀ hNr).mpr (by simpa only [mul_comm] using hhi)
    calc
      _ ≤ ((q.1 j:ℝ)+1)/((2^c:ℕ):ℝ) := hupper.le
      _ = (q.1 j:ℝ)/((2^c:ℕ):ℝ)+1/((2^c:ℕ):ℝ) := by ring
      _ ≤ (q.1 j:ℝ)/((2^c:ℕ):ℝ)+rho := by linarith only [hstep]

/-- The original backbone supplies the complete reference population in
the actual retained parent source. Neither native admission of the coarse
output nor a post-chart occupied-cell lower bound is a premise. -/
theorem same_reference_old_parent_height_fiber {n : ℕ} {D : FiniteScaleSource n}
    {eta localEta a zeta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original R a level zeta)
    (Eref : Finset (Fin n × Index)) (m b : ℕ) (hb : 8 ≤ b) (hmb : m+b ≤ level)
    (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput
      (NativeLocalParentSource.source h R Eref a m p) localEta)
    (hbudget : (64:ℝ)^3*(NativeLocalParentSource.source h R Eref a m p).thickness^e ≤
      D.thickness^zeta)
    (selected : Finset (Fin (NativeLocalParentSource.parentLabels D R a (2^m) p).card × Index))
    (s : CanonicalConfiguredE4Bridge.Split) (P : Submodule ℝ E4)
    (hP : P ≤ NativeHorizontalGrainSlice.heightKernel)
    (hdim : Module.finrank ℝ P = CanonicalConfiguredE4Bridge.tangentDim s)
    (I : Finset (E4 × Fin (((univ : Finset
      (Fin (NativeLocalParentSource.parentLabels D R a (2^m) p).card)).image
      (parentLabel (NativeLocalParentSource.source h R Eref a m p) 0 (2^b))).card)))
    (hI : ∀x i, (x,i)∈I → x∈markedUnitTube
      (MarkedIsometricChart.line (NativePackedFrameIsometry.frame s P hP hdim) 0
        ((fullSource hReferenceNative univ 0 (level-m+6) b selected).line i))
      (64/((2^b:ℕ):ℝ)))
    (hsep : ∀x∈I.image Prod.fst, ∀y∈I.image Prod.fst, x≠y →
      64/((2^b:ℕ):ℝ) ≤ dist x y)
    (c : ℕ) (hc : c ≤ b) {rho : ℝ}
    (hrho : 64/((2^b:ℕ):ℝ) ≤ rho) (hstep : 1/((2^c:ℕ):ℝ) ≤ rho)
    (z : ℝ) (q : Parent) :
    ((I.filter (fun v => v.1 3=z ∧
      oldAncestor (NativeLocalParentSource.source h R Eref a m p) univ 0 b c v.2=q)).card:ℝ) ≤
        (130^3*5832*66^3:ℝ)*(NativeLocalParentSource.source h R Eref a m p).thickness^(-e)*
          (rho/(64/((2^b:ℕ):ℝ)))^3 := by
  have H := NativeSameReferenceChartBounds.population_through h original R level HB Eref m b hmb p hbudget
  have hscale := NativeSameReferenceChartBounds.source_scale_guard (a := a)
    h R Eref level m b p HB.2.1 hmb
  exact full_source_old_parent_height_fiber (a := 0) (e := e) hReferenceNative univ
    (level-m+6) b hb selected hscale (fun q hq => (H ⟨b,by omega⟩ q hq).1)
    (NativePackedFrameIsometry.frame s P hP hdim)
    (NativePackedFrameIsometry.frame_height s P hP hdim) I hI hsep c hc hrho hstep z q

end NativeFixedHeightPairCap
