import Theorems.Thm_StickyKakeya4_native_ad_fixed_contraction
import Theorems.Thm_StickyKakeya4_native_literal_grid_overlap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeGridCenterContraction
open Classical Finset NativeLiteralGridOverlap NativeADFixedContraction
open FiniteVoronoiRealADCoarsening

/-- A fixed positive dilation of actual grid centers, retaining the source
global count. C=512 includes the final large-radius interval explicitly. -/
theorem contracted_grid_AD {l : ℕ} (P : Finset (Fin l → ℤ))
    {mu C K G s : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hC : 1 ≤ C)
    (hK : 0 < K) (hs : 0 ≤ s)
    (H : ADBounds (P.image (center mu)) mu K s)
    (Hglobal : (P.card:ℝ) ≤ G*mu^(-s)) :
    ADBounds (P.image (center (mu/C))) (mu/C) (C^s*max K G) s := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let f : (Fin l → ℝ) → (Fin l → ℝ) := fun x => (1/C:ℝ) • x
  have hf : Function.Injective f := by
    intro x y hxy
    funext j
    have hh := congrFun hxy j
    exact mul_left_cancel₀ (one_div_ne_zero hCp.ne') hh
  have hd : ∀x y,dist (f x) (f y)=dist x y/C := by
    intro x y
    dsimp only [f]
    rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hCp)]
    ring
  have hg : ((P.image (center mu)).card:ℝ) ≤ G*mu^(-s) := by
    rw [card_image_of_injective _ (center_injective hmu)]
    exact Hglobal
  have hh := contract_AD (P.image (center mu)) f hf hmu hmu1 hC hK hs hd H hg
  convert hh using 1
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨center mu x,⟨x,hx,rfl⟩,?_⟩
    funext j
    dsimp [f,center]
    ring
  · rintro ⟨u,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨x,hx,?_⟩
    funext j
    dsimp [f,center]
    ring

/-- At original mesh at least one, the final mesh is in [1/C,1]. Its
whole point population is bounded by the actual coarsest source count. -/
theorem coarsest_grid_AD {l : ℕ} (P : Finset (Fin l → ℤ))
    {mu C G s : ℝ} (hmu : 1 ≤ mu) (hC : 1 ≤ C) (hs : 0 ≤ s)
    (Hglobal : (P.card:ℝ) ≤ G) :
    ADBounds (P.image (center (mu/C))) (mu/C) (C^s*max 1 G) s := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  apply coarse_mesh_AD _ hC (div_le_div_of_nonneg_right hmu hCp.le) hs
  have hh := (Nat.cast_le.mpr (card_image_le (s:=P) (f:=center (mu/C))) :
    ((P.image (center (mu/C))).card:ℝ) ≤ P.card)
  exact hh.trans Hglobal

end NativeGridCenterContraction
