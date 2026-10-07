import Theorems.Thm_StickyKakeya4_canonical_configured_E4_bridge

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace CanonicalRecodingHomogeneity
open Classical Finset StickyKakeya4 CanonicalGridRecoding CanonicalConfiguredPointRounding
open CanonicalConfiguredE4Bridge
open scoped BigOperators

variable {k l : ℕ}

theorem grid_scale (a : ℝ) (ha : a≠0) (mu : ℝ) (x : Fin k → ℝ) :
    grid (a*mu) (a • x)=grid mu x := by
  funext j
  change ⌊(a*x j)/(a*mu)⌋=⌊x j/mu⌋
  rw [mul_div_mul_left _ _ ha]

theorem center_scale (a mu : ℝ) (u : Grid k) :
    center (a*mu) u=a • center mu u := by
  funext j
  change a*mu*((u j:ℝ)+1/2)=a*(mu*((u j:ℝ)+1/2))
  ring

theorem graphPoint_scale (a : ℝ) (F : Matrix (Fin l) (Fin k) ℝ)
    (x : Fin k → ℝ) (y : Fin l → ℝ) :
    graphPoint F (a • x) (a • y)=a • graphPoint F x y := by
  funext i
  change a*y i+(∑j,F i j*(a*x j))=a*(y i+∑j,F i j*x j)
  rw [mul_add,mul_sum]
  congr 1
  apply sum_congr rfl
  intro j _hj
  ring

theorem quotient_scale (a : ℝ) (F : Matrix (Fin l) (Fin k) ℝ)
    (x : Fin k → ℝ) (n : Fin l → ℝ) :
    quotient F (a • x) (a • n)=a • quotient F x n := by
  funext i
  change a*n i-(∑j,F i j*(a*x j))=a*(n i-∑j,F i j*x j)
  rw [mul_sub,mul_sum]
  congr 1
  apply sum_congr rfl
  intro j _hj
  ring

theorem coarseGrid_scale (a : ℝ) (ha : a≠0) (mu : ℝ) (R : ℕ) (u : Grid k) :
    coarseGrid (a*mu) R u=coarseGrid mu R u := by
  change grid ((a*mu)*(R:ℝ)) (center (a*mu) u)=grid (mu*(R:ℝ)) (center mu u)
  rw [mul_assoc,center_scale,grid_scale a ha]

theorem recodedY_scale (a : ℝ) (ha : a≠0) (mu : ℝ) (R : ℕ)
    (F : Matrix (Fin l) (Fin k) ℝ) (u : Grid k) (v : Grid l) :
    recodedY (a*mu) R F u v=recodedY mu R F u v := by
  change grid ((a*mu)*(R:ℝ)) (graphPoint F (center (a*mu) u) (center (a*mu) v))=
    grid (mu*(R:ℝ)) (graphPoint F (center mu u) (center mu v))
  rw [mul_assoc,center_scale,center_scale,graphPoint_scale,grid_scale a ha]

theorem coarseX_scale (a : ℝ) (ha : a≠0) (mu : ℝ) (R : ℕ) (u : Grid k) :
    coarseX (a*mu) R u=a • coarseX mu R u := by
  unfold coarseX
  rw [coarseGrid_scale a ha,mul_assoc,center_scale]

theorem configuredNormal_scale (a : ℝ) (ha : a≠0) (mu : ℝ) (R : ℕ)
    (Fold Fcfg : Matrix (Fin l) (Fin k) ℝ) (u : Grid k) (v : Grid l) :
    configuredNormal (a*mu) R Fold Fcfg u v=a • configuredNormal mu R Fold Fcfg u v := by
  unfold configuredNormal
  rw [coarseX_scale a ha,recodedY_scale a ha,mul_assoc,center_scale,graphPoint_scale]

theorem tangent_scale (s : Split) (a : ℝ) (z : E4) :
    tangent s (a • z)=a • tangent s z := by
  funext j
  cases s <;> fin_cases j <;> rfl

theorem normal_scale (s : Split) (a : ℝ) (z : E4) :
    normal s (a • z)=a • normal s z := by
  funext i
  cases s <;> fin_cases i <;> rfl

theorem assemble_scale (s : Split) (a : ℝ) (x : Fin (tangentDim s) → ℝ)
    (n : Fin (normalDim s) → ℝ) (t : ℝ) :
    assemble s (a • x) (a • n) (a*t)=a • assemble s x n t := by
  ext j
  cases s <;> fin_cases j <;> rfl

theorem rounded_height_scale (a : ℝ) (ha : a≠0) (mu : ℝ) (R : ℕ) (t : ℝ) :
    ((a*mu)*(R:ℝ))*((⌊(a*t)/((a*mu)*(R:ℝ))⌋:ℝ)+1/2)=
      a*((mu*(R:ℝ))*((⌊t/(mu*(R:ℝ))⌋:ℝ)+1/2)) := by
  have hratio : (a*t)/((a*mu)*(R:ℝ))=t/(mu*(R:ℝ)) := by
    rw [show (a*mu)*(R:ℝ)=a*(mu*(R:ℝ)) by ring,mul_div_mul_left _ _ ha]
  rw [hratio]
  ring

/-- Both original grid labels and corrected coarse quotient labels are
unchanged when all physical positions and meshes are rescaled together. -/
theorem configuredChart_scale (s : Split) (a : ℝ) (ha : a≠0) (mu : ℝ) (R : ℕ)
    (Fold Fcfg : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) (z : E4) :
    configuredChart s (a*mu) R Fold Fcfg (a • z)=a • configuredChart s mu R Fold Fcfg z := by
  unfold configuredChart
  rw [tangent_scale,normal_scale,quotient_scale,grid_scale a ha,grid_scale a ha,
    coarseX_scale a ha,configuredNormal_scale a ha]
  change assemble s _ _ (((a*mu)*(R:ℝ))*((⌊(a*z 3)/((a*mu)*(R:ℝ))⌋:ℝ)+1/2))=_
  rw [rounded_height_scale a ha,assemble_scale]

/-- The chart center must scale with the original physical point. -/
theorem configuredPoint_scale (s : Split) (a : ℝ) (ha : a≠0) (mu : ℝ) (R : ℕ)
    (Fold Fcfg : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c p : E4) :
    configuredPoint s (a*mu) R Fold Fcfg O (a • c) (a • p)=
      a • configuredPoint s mu R Fold Fcfg O c p := by
  unfold configuredPoint
  rw [←smul_sub,map_smul,configuredChart_scale s a ha]

/-- Exact specialization for the full local reference family's second
zero-parent normalization. No isometry is used to hide the factor512. -/
theorem configuredPoint_div512 (s : Split) (mu : ℝ) (R : ℕ)
    (Fold Fcfg : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c p : E4) :
    configuredPoint s (mu/512) R Fold Fcfg O ((1/512:ℝ) • c) ((1/512:ℝ) • p)=
      (1/512:ℝ) • configuredPoint s mu R Fold Fcfg O c p := by
  have he : (1/512:ℝ)*mu=mu/512 := by ring
  simpa only [he] using configuredPoint_scale s (1/512:ℝ) (by norm_num) mu R Fold Fcfg O c p

end CanonicalRecodingHomogeneity
