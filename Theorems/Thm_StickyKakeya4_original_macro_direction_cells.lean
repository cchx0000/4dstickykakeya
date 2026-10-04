import Theorems.Thm_StickyKakeya4_original_scalar_literal_cover_count
import Theorems.Thm_StickyKakeya4_native_coarse_original_geometry
import Theorems.Thm_StickyKakeya4_spine_column_counting
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace OriginalMacroDirectionCells
open Classical Finset NativeTangentGridCoarsening
variable {T : Type*}
def directionCell (tau : ℝ) (u : T → ℝ) (v : T → ℝ × ℝ) (t : T) : ℤ × (ℤ × ℤ) :=
  (⌊u t/tau⌋,(⌊(v t).1/tau⌋,⌊(v t).2/tau⌋))
def directionCells (S : Finset T) (tau : ℝ) (u : T → ℝ) (v : T → ℝ × ℝ) :=
  S.image (directionCell tau u v)
def directionVector (u : T → ℝ) (v : T → ℝ × ℝ) (t : T) : Fin 3 → ℝ :=
  ![u t,(v t).1,(v t).2]
/-- Actual three-coordinate direction cells in an original coordinate box. -/
theorem direction_cells_box_bound (S : Finset T) (u : T → ℝ) (v : T → ℝ × ℝ)
    (a : ℝ) (b : ℝ × ℝ) {tau C : ℝ} (ht : 0 < tau) (hC : 0 ≤ C)
    (hu : ∀ t ∈ S, |u t-a| ≤ C*tau) (hv : ∀ t ∈ S, ‖v t-b‖ ≤ C*tau) :
    ((directionCells S tau u v).card:ℝ) ≤ (2*C+2)^3 := by
  have hs := scalar_interval_grid_card S u (c := a-C*tau) ht
    (show 0 ≤ 2*C*tau by positivity) (fun t htS => by
      have hh := abs_le.mp (hu t htS)
      exact ⟨by linarith only [hh.1],by linarith only [hh.2]⟩)
  have hs' : ((scalarCells S u tau).card:ℝ) ≤ 2*C+2 := by
    have he : 2*C*tau/tau+2=2*C+2 := by field_simp
    simpa only [he] using hs
  have hv' := planar_centered_grid_card S v b ht hC (fun t htS => max_le_iff.mp (hv t htS))
  have hsub : directionCells S tau u v ⊆ scalarCells S u tau ×ˢ planarCells S v tau := by
    intro k hk
    obtain ⟨t,htS,rfl⟩ := mem_image.mp hk
    exact mem_product.mpr ⟨mem_image_of_mem _ htS,mem_image_of_mem _ htS⟩
  have hc : ((directionCells S tau u v).card:ℝ) ≤
      ((scalarCells S u tau).card:ℝ)*((planarCells S v tau).card:ℝ) := by
    have hh := card_le_card hsub
    rw [card_product] at hh
    exact_mod_cast hh
  exact hc.trans ((mul_le_mul hs' hv' (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring))
/-- Original coarse reference angles are grouped by THEIR occupied cells.
 The covering alphabet need not be separated, and its raw cardinality is
 never substituted for its literal cover count. -/
theorem original_reference_cell_count (S : Finset T) (u : T → ℝ) (v : T → ℝ × ℝ)
    (Phi : Finset ℝ) (F : ℝ →L[ℝ] ℝ × ℝ) (xi : ℝ × ℝ) {q tau C A : ℝ}
    (hq : 0 < q) (ht : 0 < tau) (hC : 0 ≤ C) (hA : 0 ≤ A) (hF : ‖F‖ ≤ A)
    (hcover : ∀ t ∈ S, ∃ a ∈ Phi, |u t-a| ≤ C*q ∧ ‖v t-xi-F a‖ ≤ C*q) :
    ((directionCells S tau u v).card:ℝ) ≤
      (2*((C+A+1)*q/tau)+2)^3*((Phi.image (NativeScalarCoverAD.cell q)).card:ℝ) := by
  let R := C+A+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let mid : ℤ → ℝ := fun k => q*((k:ℝ)+1/2)
  let fiber : ℤ → Finset T := fun k => S.filter (fun t =>
    |u t-mid k| ≤ R*q ∧ ‖v t-(xi+F (mid k))‖ ≤ R*q)
  have hsub : directionCells S tau u v ⊆
      (Phi.image (NativeScalarCoverAD.cell q)).biUnion (fun k => directionCells (fiber k) tau u v) := by
    intro d hd
    obtain ⟨t,htS,rfl⟩ := mem_image.mp hd
    obtain ⟨a,ha,hua,hva⟩ := hcover t htS
    let k := NativeScalarCoverAD.cell q a
    have ham : |a-mid k| ≤ q/2 := by
      have hh := NativeCoarseOriginalGeometry.scalar_floor_center_error hq a
      simpa only [mid,k,NativeScalarCoverAD.cell,abs_sub_comm] using hh
    have hu : |u t-mid k| ≤ R*q := by
      have hh := (abs_sub_le (u t) a (mid k)).trans (add_le_add hua ham)
      dsimp [R]
      nlinarith only [hh,mul_nonneg hA hq.le,hq.le]
    have hfm : ‖F (a-mid k)‖ ≤ A*(q/2) :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hF ham (norm_nonneg _) hA)
    have hid : v t-(xi+F (mid k))=(v t-xi-F a)+F (a-mid k) := by
      rw [map_sub]
      abel
    have hv : ‖v t-(xi+F (mid k))‖ ≤ R*q := by
      rw [hid]
      have hh := (norm_add_le _ _).trans (add_le_add hva hfm)
      dsimp [R]
      nlinarith only [hh,mul_nonneg hA hq.le,hq.le]
    exact mem_biUnion.mpr ⟨k,mem_image_of_mem _ ha,
      mem_image_of_mem _ (mem_filter.mpr ⟨htS,hu,hv⟩)⟩
  have hf : ∀ k ∈ Phi.image (NativeScalarCoverAD.cell q),
      ((directionCells (fiber k) tau u v).card:ℝ) ≤ (2*(R*q/tau)+2)^3 := by
    intro k _hk
    apply direction_cells_box_bound (fiber k) u v (mid k) (xi+F (mid k)) ht (by positivity : 0 ≤ R*q/tau)
    · intro t htS
      rw [div_mul_cancel₀ _ ht.ne']
      exact (mem_filter.mp htS).2.1
    · intro t htS
      rw [div_mul_cancel₀ _ ht.ne']
      exact (mem_filter.mp htS).2.2
  have hb := OriginalWWitnessCounts.card_biUnion_le_real
    (Phi.image (NativeScalarCoverAD.cell q)) (fun k => directionCells (fiber k) tau u v)
    (show 0 ≤ (2*(R*q/tau)+2)^3 by positivity) (le_refl _) hf
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans (by simpa only [mul_comm] using hb)
/-- The literal original scalar cover law gives the full direction alphabet
 at mesh q/8, with all field and angle-error losses explicit. -/
theorem literal_original_direction_mass (S : Finset T) (u : T → ℝ) (v : T → ℝ × ℝ)
    (Phi : Finset ℝ) (F : ℝ →L[ℝ] ℝ × ℝ) (xi : ℝ × ℝ) {q C A K kappa : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hC : 0 ≤ C) (hA : 0 ≤ A) (hK : 0 ≤ K) (hF : ‖F‖ ≤ A)
    (H : NativeScalarCoverAD.CoverADBounds Phi q K kappa) (hbox : ∀ a ∈ Phi, |a| ≤ 1)
    (hcover : ∀ t ∈ S, ∃ a ∈ Phi, |u t-a| ≤ C*q ∧ ‖v t-xi-F a‖ ≤ C*q) :
    q^kappa*((directionCells S (q/8) u v).card:ℝ) ≤ 2*K*(16*(C+A+1)+2)^3 := by
  have hc := original_reference_cell_count S u v Phi F xi hq (by positivity : 0 < q/8) hC hA hF hcover
  have he : 2*((C+A+1)*q/(q/8))+2=16*(C+A+1)+2 := by field_simp; ring
  rw [he] at hc
  have hp := OriginalScalarLiteralCoverCount.boxed_cover_grid_upper Phi hq hq1 hK H hbox
  have hcancel : q^kappa*(1/q)^kappa=1 := by
    rw [←Real.mul_rpow hq.le (one_div_nonneg.mpr hq.le)]
    simp [hq.ne']
  have hh := mul_le_mul_of_nonneg_left
    (hc.trans (mul_le_mul_of_nonneg_left hp (by positivity))) (Real.rpow_pos_of_pos hq kappa).le
  calc
    _ ≤ q^kappa*((16*(C+A+1)+2)^3*(2*K*(1/q)^kappa)) := hh
    _ = 2*K*(16*(C+A+1)+2)^3*(q^kappa*(1/q)^kappa) := by ring
    _ = _ := by rw [hcancel,mul_one]
/-- A collision of actual direction cells controls ALL direction coordinates. -/
theorem direction_cell_gap (u : T → ℝ) (v : T → ℝ × ℝ) {tau : ℝ} (ht : 0 < tau)
    (s t : T) (he : directionCell tau u v s=directionCell tau u v t) :
    |u s-u t| ≤ tau ∧ ‖v s-v t‖ ≤ tau := by
  have h0 : ⌊u s/tau⌋=⌊u t/tau⌋ := congrArg Prod.fst he
  have h1 : ⌊(v s).1/tau⌋=⌊(v t).1/tau⌋ := congrArg (fun k : ℤ × (ℤ × ℤ) => k.2.1) he
  have h2 : ⌊(v s).2/tau⌋=⌊(v t).2/tau⌋ := congrArg (fun k : ℤ × (ℤ × ℤ) => k.2.2) he
  exact ⟨(SpineColumnCounting.same_floor_scaled_close ht h0).le,
    max_le (SpineColumnCounting.same_floor_scaled_close ht h1).le
      (SpineColumnCounting.same_floor_scaled_close ht h2).le⟩
/-- The q/8 label gives the printed full Euclidean direction restriction. -/
theorem full_direction_collision (u : T → ℝ) (v : T → ℝ × ℝ) {q : ℝ} (hq : 0 < q)
    (s t : T) (he : directionCell (q/8) u v s=directionCell (q/8) u v t) :
    dist (EuclideanAlignmentPatches.euclidean (directionVector u v s))
      (EuclideanAlignmentPatches.euclidean (directionVector u v t)) ≤ q := by
  have hg := direction_cell_gap u v (by positivity : 0 < q/8) s t he
  have hn := max_le_iff.mp hg.2
  have hh := EuclideanAlignmentPatches.euclidean_dist_le_card_mul
    (directionVector u v s) (directionVector u v t) (q/8) (by positivity) (fun i => by
      fin_cases i
      · exact hg.1
      · exact hn.1
      · exact hn.2)
  norm_num only [Nat.cast_ofNat] at hh
  linarith
end OriginalMacroDirectionCells
