import Theorems.Thm_StickyKakeya4_native_coarse_physical_containment
import Theorems.Thm_StickyKakeya4_native_padded_source_count_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
noncomputable section
namespace NativeCoarseCWTransfer
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCoarsePhysicalContainment NativePaddedSourceTransport NativeContractedUnitParent
open NativePaddedSourceCountBudget
open scoped BigOperators ENNReal

/-- Original full-parent populations, including all their original tubes,
are charged to the actual common physical preimage of the convex set. -/
theorem contained_count_cross {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (S : Finset Parent) (_hS : S⊆R.image (parentLabel D a N)) (rep : Parent → Fin n)
    (hrep : ∀p∈S,parentLabel D a N (rep p)=p)
    (H : ∀p∈S,D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3 ≤
      ((R.filter (fun i => parentLabel D a N i=p)).card:ℝ)) (U : Set E4) :
    ((S.filter (fun p => markedUnitTube (NativeContractedUnitParent.line D a (0,0) (rep p))
      (64/(N:ℝ))⊆U)).card:ℝ)*
      (D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3) ≤
        (wzContainedTubeCount D (physicalMap D a (0,0) ⁻¹' U):ℝ) := by
  let T := S.filter (fun p => markedUnitTube (NativeContractedUnitParent.line D a (0,0) (rep p))
    (64/(N:ℝ))⊆U)
  let V := R.filter (fun i => parentLabel D a N i∈T)
  have hsum : V.card=∑p∈T,(R.filter (fun i => parentLabel D a N i=p)).card := by
    rw [card_eq_sum_card_fiberwise (f:=parentLabel D a N) (s:=V) (t:=T)
      (fun i hi => (mem_filter.mp hi).2)]
    apply sum_congr rfl
    intro p hp
    congr 1
    ext i
    simp only [V,mem_filter]
    constructor
    · rintro ⟨⟨hi,_hit⟩,hip⟩
      exact ⟨hi,hip⟩
    · rintro ⟨hi,hip⟩
      exact ⟨⟨hi,hip ▸ hp⟩,hip⟩
  have hcard : V.card ≤ wzContainedTubeCount D (physicalMap D a (0,0) ⁻¹' U) := by
    apply card_le_card
    intro i hi
    obtain ⟨_hiR,hiT⟩ := mem_filter.mp hi
    obtain ⟨hip,hiU⟩ := mem_filter.mp hiT
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro x hx
    exact hiU (original_tube_in_representative h ha N hN hscale i
      (rep (parentLabel D a N i)) (hrep _ hip).symm (Set.mem_image_of_mem _ hx))
  have hs : (∑p∈T,((R.filter (fun i => parentLabel D a N i=p)).card:ℝ))=(V.card:ℝ) := by
    exact_mod_cast hsum.symm
  change (T.card:ℝ)*_ ≤ _
  calc
    _ = ∑_p∈T,D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3 := by simp
    _ ≤ ∑p∈T,((R.filter (fun i => parentLabel D a N i=p)).card:ℝ) :=
      sum_le_sum (fun p hp => H p (mem_filter.mp hp).1)
    _ = (V.card:ℝ) := hs
    _ ≤ _ := by exact_mod_cast hcard

/-- Native original CW and actual direction packing yield the absolute
coarse contained-tube bound. The later retained coarse count supplies the
relative normalization; no new CW profile is assumed. -/
theorem original_coarse_CW_real {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (S : Finset Parent) (hS : S⊆R.image (parentLabel D a N)) (rep : Parent → Fin n)
    (hrep : ∀p∈S,parentLabel D a N (rep p)=p)
    (H : ∀p∈S,D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3 ≤
      ((R.filter (fun i => parentLabel D a N i=p)).card:ℝ))
    (U : Set E4) (hU : Convex ℝ U) (hfin : volume U≠⊤) :
    ((S.filter (fun p => markedUnitTube (NativeContractedUnitParent.line D a (0,0) (rep p))
      (64/(N:ℝ))⊆U)).card:ℝ) ≤
        (373248*512^4:ℝ)*D.thickness^(-eta-zeta)*(N:ℝ)^3*(volume U).toReal := by
  have hd:=h.1.2.1
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hcross := contained_count_cross h ha R N hN hscale S hS rep hrep H U
  have hw := h.1.2.2.2.2.2.2.2.2.2.2.2.1
    (physicalMap D a (0,0) ⁻¹' U) (convex_physicalMap_preimage D a (0,0) hU)
  rw [volume_physicalMap_preimage] at hw
  have hd0 : ENNReal.ofReal D.thickness≠0 := by positivity
  have hpow : (ENNReal.ofReal D.thickness).rpow (-eta)≠⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.ofReal_ne_top
  have hf : (ENNReal.ofReal D.thickness).rpow (-eta)*((512:ℝ≥0∞)^4*volume U)*n≠⊤ := by finiteness
  have hr := ENNReal.toReal_mono hf hw
  simp only [ENNReal.rpow_eq_pow] at hr
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal hd.le] at hr
  have hraw : ((S.filter (fun p => markedUnitTube (NativeContractedUnitParent.line D a (0,0) (rep p))
      (64/(N:ℝ))⊆U)).card:ℝ)*(D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3) ≤
        D.thickness^(-eta)*((512:ℝ)^4*(volume U).toReal)*(373248*(1/D.thickness)^3) := by
    exact hcross.trans (hr.trans (mul_le_mul_of_nonneg_left (original_card_upper h) (by positivity)))
  have he : ((373248*512^4:ℝ)*D.thickness^(-eta-zeta)*(N:ℝ)^3*(volume U).toReal)*
      (D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3)=
        D.thickness^(-eta)*((512:ℝ)^4*(volume U).toReal)*(373248*(1/D.thickness)^3) := by
    rw [Real.rpow_sub hd]
    field_simp [hd.ne',hNr.ne',(Real.rpow_pos_of_pos hd zeta).ne']
  apply (mul_le_mul_iff_left₀ (show 0 < D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3 by positivity)).mp
  rw [he]
  exact hraw

end NativeCoarseCWTransfer
