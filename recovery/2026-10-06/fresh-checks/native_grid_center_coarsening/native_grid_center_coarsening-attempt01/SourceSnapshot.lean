import Theorems.Thm_StickyKakeya4_native_recoded_grid_ad

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeGridCenterCoarsening
open Classical Finset NativeLiteralGridOverlap NativeRecodedGridAD
open FiniteVoronoiRealADCoarsening

def divide {l : ℕ} (D : ℕ) (y : Fin l → ℤ) : Fin l → ℤ := fun i => y i/(D:ℤ)

/-- Literal integer coarsening moves an original grid center by at most
the target mesh. The estimate includes negative labels and boundary cells. -/
theorem center_displacement {l : ℕ} {mu : ℝ} (hmu : 0 < mu)
    (D : ℕ) (hD : 0 < D) (y : Fin l → ℤ) :
    dist (center (mu*(D:ℝ)) (divide D y)) (center mu y) ≤ mu*(D:ℝ) := by
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hDZ : (0:ℤ) < D := by exact_mod_cast hD
  apply (dist_pi_le_iff (by positivity : (0:ℝ) ≤ mu*(D:ℝ))).mpr
  intro i
  have hb := (Int.ediv_eq_iff_of_pos hDZ).mp (rfl : y i/(D:ℤ)=y i/(D:ℤ))
  have hlo : ((y i/(D:ℤ):ℤ):ℝ)*(D:ℝ) ≤ (y i:ℝ) := by exact_mod_cast hb.1
  have hhi : (y i:ℝ) ≤ ((y i/(D:ℤ):ℤ):ℝ)*(D:ℝ)+(D:ℝ) := by
    exact_mod_cast hb.2.le
  have hmullo := mul_le_mul_of_nonneg_left hlo hmu.le
  have hmulhi := mul_le_mul_of_nonneg_left hhi hmu.le
  have hmesh := le_mul_of_one_le_right hmu.le hD1
  rw [Real.dist_eq]
  dsimp [center,divide]
  apply abs_le.mpr
  constructor <;> nlinarith only [hmullo,hmulhi,hmesh,hmu,hDr]

/-- An exact integer-grid image inherits full-radius AD from the same
original fine grid set. The global source count remains explicit. -/
theorem coarsened_ADBounds {l : ℕ} (P : Finset (Fin l → ℤ)) (D : ℕ) (hD : 0 < D)
    {mu K s : ℝ} (hmu : 0 < mu) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (H : ADBounds (P.image (center mu)) mu K s)
    (Hglobal : (P.card:ℝ) ≤ K*mu^(-s)) :
    ADBounds ((P.image (divide D)).image (center (mu*(D:ℝ)))) (mu*(D:ℝ))
      ((((9:ℕ)^l:ℕ):ℝ)*K^2*(12:ℝ)^s) s := by
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hscale : mu ≤ mu*(D:ℝ) := le_mul_of_one_le_right hmu.le hD1
  have hglobal : ((P.image (center mu)).card:ℝ) ≤ K*mu^(-s) := by
    rw [Finset.card_image_of_injective _ (center_injective hmu)]
    exact Hglobal
  have hf : ∀a∈P.image (center mu), ∃k∈P.image (divide D),
      dist (center (mu*(D:ℝ)) k) a ≤ (1:ℝ)*(mu*(D:ℝ)) := by
    intro a ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨divide D y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,
      by simpa only [one_mul] using center_displacement hmu D hD y⟩
  have hb : ∀k∈P.image (divide D), ∃a∈P.image (center mu),
      dist (center (mu*(D:ℝ)) k) a ≤ (1:ℝ)*(mu*(D:ℝ)) := by
    intro k hk
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hk
    exact ⟨center mu y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,
      by simpa only [one_mul] using center_displacement hmu D hD y⟩
  have hh := two_way_grid_cover_ADBounds (P.image (center mu)) (P.image (divide D))
    hmu hscale (by norm_num : (1:ℝ) ≤ 1) hK hs H hglobal hf hb
  norm_num at hh
  exact hh

end NativeGridCenterCoarsening
