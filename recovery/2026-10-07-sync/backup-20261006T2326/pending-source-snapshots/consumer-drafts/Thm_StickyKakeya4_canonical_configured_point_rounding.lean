/- New draft, 2026-10-06. No source-geometry identity is assumed from missing files. -/
import Theorems.Thm_StickyKakeya4_canonical_grid_recoding

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace CanonicalConfiguredPointRounding
open Classical Finset CanonicalGridRecoding
open scoped BigOperators

variable {k l : ℕ}

def grid (delta : ℝ) (x : Fin k → ℝ) : Grid k := fun j => ⌊x j/delta⌋

def graphPoint (F : Matrix (Fin l) (Fin k) ℝ) (x : Fin k → ℝ) (y : Fin l → ℝ) : Fin l → ℝ :=
  fun i => y i+∑j : Fin k,F i j*x j

def quotient (F : Matrix (Fin l) (Fin k) ℝ) (x : Fin k → ℝ) (n : Fin l → ℝ) : Fin l → ℝ :=
  fun i => n i-∑j : Fin k,F i j*x j

/-- Exact scalar midpoint rounding, with its physical mesh factor. -/
theorem midpoint_error (delta a : ℝ) (hd : 0 < delta) :
    |delta*((⌊a/delta⌋:ℝ)+1/2)-a|≤delta/2 := by
  have hlo := (le_div_iff₀ hd).mp (Int.floor_le (a/delta))
  have hhi := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (a/delta))
  apply abs_le.mpr
  constructor <;> nlinarith

theorem center_grid_error (delta : ℝ) (hd : 0 < delta) (x : Fin k → ℝ) (j : Fin k) :
    |center delta (grid delta x) j-x j|≤delta/2 :=
  midpoint_error delta (x j) hd

/-- Propagation of two literal coordinate errors through a bounded graph.
This is pure finite-coordinate algebra and uses no source certificate. -/
theorem graph_perturbation (F : Matrix (Fin l) (Fin k) ℝ)
    (hF : ∀i j,|F i j|≤1/4) (x x' : Fin k → ℝ) (y y' : Fin l → ℝ)
    (eX eY : ℝ) (hX : ∀j,|x j-x' j|≤eX) (hY : ∀i,|y i-y' i|≤eY) (i : Fin l) :
    |graphPoint F x y i-graphPoint F x' y' i|≤eY+(k:ℝ)*eX/4 := by
  have he : graphPoint F x y i-graphPoint F x' y' i=
      (y i-y' i)+∑j : Fin k,F i j*(x j-x' j) := by
    simp only [graphPoint,mul_sub,sum_sub_distrib]
    ring
  have hsum : |∑j : Fin k,F i j*(x j-x' j)|≤(k:ℝ)*eX/4 := by
    calc
      _ ≤ ∑j : Fin k,|F i j*(x j-x' j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑_j : Fin k,(1/4:ℝ)*eX := by
        apply sum_le_sum
        intro j _hj
        rw [abs_mul]
        exact mul_le_mul (hF i j) (hX j) (abs_nonneg _) (by norm_num)
      _ = _ := by simp; ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (hY i) hsum)

/-- Rewriting the old quotient coordinate cancels the matrix change
exactly. No smallness of F_old-F_cfg is needed for this identity. -/
theorem graph_recode_identity (Fold Fcfg : Matrix (Fin l) (Fin k) ℝ)
    (x : Fin k → ℝ) (y : Fin l → ℝ) :
    graphPoint Fcfg x (graphPoint (Fold-Fcfg) x y)=graphPoint Fold x y := by
  funext i
  simp only [graphPoint,Matrix.sub_apply,sub_mul,sum_sub_distrib]
  ring

def coarseX (mu : ℝ) (R : ℕ) (u : Grid k) : Fin k → ℝ :=
  center (mu*(R:ℝ)) (coarseGrid mu R u)

def configuredNormal (mu : ℝ) (R : ℕ)
    (Fold Fcfg : Matrix (Fin l) (Fin k) ℝ) (u : Grid k) (v : Grid l) : Fin l → ℝ :=
  graphPoint Fcfg (coarseX mu R u)
    (center (mu*(R:ℝ)) (recodedY mu R (Fold-Fcfg) u v))

theorem coarseX_error (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (hR : 0 < R)
    (u : Grid k) (j : Fin k) :
    |coarseX mu R u j-center mu u j|≤(mu*(R:ℝ))/2 := by
  exact midpoint_error (mu*(R:ℝ)) (center mu u j)
    (mul_pos hmu (by exact_mod_cast hR))

/-- The actual new normal coordinate differs from the OLD fine physical
graph point by at most 3rho/4. Matrix coherence is needed for menu counts,
not for this cancellation and rounding estimate. -/
theorem configuredNormal_error (hk : k≤2) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R) (Fold Fcfg : Matrix (Fin l) (Fin k) ℝ)
    (hCfg : ∀i j,|Fcfg i j|≤1/4) (u : Grid k) (v : Grid l) (i : Fin l) :
    |configuredNormal mu R Fold Fcfg u v i-graphPoint Fold (center mu u) (center mu v) i|≤
      (3/4:ℝ)*(mu*(R:ℝ)) := by
  let rho := mu*(R:ℝ)
  let shifted := graphPoint (Fold-Fcfg) (center mu u) (center mu v)
  have hrho : 0 < rho := mul_pos hmu (by exact_mod_cast hR)
  have hY : ∀i,|center rho (recodedY mu R (Fold-Fcfg) u v) i-shifted i|≤rho/2 := by
    intro i
    exact midpoint_error rho (shifted i) hrho
  have hX : ∀j,|coarseX mu R u j-center mu u j|≤rho/2 :=
    coarseX_error mu R hmu hR u
  have h := graph_perturbation Fcfg hCfg (coarseX mu R u) (center mu u)
    (center rho (recodedY mu R (Fold-Fcfg) u v)) shifted (rho/2) (rho/2) hX hY i
  have hid := congrFun (graph_recode_identity Fold Fcfg (center mu u) (center mu v)) i
  change graphPoint Fcfg (center mu u) shifted i=graphPoint Fold (center mu u) (center mu v) i at hid
  rw [hid] at h
  have hkr : (k:ℝ)≤2 := by exact_mod_cast hk
  change |configuredNormal mu R Fold Fcfg u v i-graphPoint Fold (center mu u) (center mu v) i|≤_
  exact h.trans (by nlinarith only [hkr,hrho])

/-- Fine quotient-grid rounding from literal raw tangent/normal coordinates.
The old Y index is floor((normal-F_old*tangent)/mu), not an unrelated label. -/
theorem fine_graph_error (hk : k≤2) (mu : ℝ) (hmu : 0 < mu)
    (Fold : Matrix (Fin l) (Fin k) ℝ) (hOld : ∀i j,|Fold i j|≤1/4)
    (x : Fin k → ℝ) (n : Fin l → ℝ) (i : Fin l) :
    |graphPoint Fold (center mu (grid mu x)) (center mu (grid mu (quotient Fold x n))) i-n i|≤
      (3/4:ℝ)*mu := by
  have h := graph_perturbation Fold hOld (center mu (grid mu x)) x
    (center mu (grid mu (quotient Fold x n))) (quotient Fold x n)
    (mu/2) (mu/2) (center_grid_error mu hmu x)
    (center_grid_error mu hmu (quotient Fold x n)) i
  have he : graphPoint Fold x (quotient Fold x n) i=n i := by
    simp only [graphPoint,quotient,sub_add_cancel]
  rw [he] at h
  have hkr : (k:ℝ)≤2 := by exact_mod_cast hk
  exact h.trans (by nlinarith only [hkr,hmu])

/-- Complete coordinate readback, including the original fine rounding.
All matrices and maps are literal; there is no final-configuration premise.
The physical height is rounded in the same rho grid, with its own error. -/
theorem actual_coordinate_errors (hk : k≤2) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R) (Fold Fcfg : Matrix (Fin l) (Fin k) ℝ)
    (hOld : ∀i j,|Fold i j|≤1/4) (hCfg : ∀i j,|Fcfg i j|≤1/4)
    (x : Fin k → ℝ) (n : Fin l → ℝ) (t : ℝ) :
    (∀j,|coarseX mu R (grid mu x) j-x j|≤mu*(R:ℝ)) ∧
    (∀i,|configuredNormal mu R Fold Fcfg (grid mu x) (grid mu (quotient Fold x n)) i-n i|≤
      (3/2:ℝ)*(mu*(R:ℝ))) ∧
    |(mu*(R:ℝ))*((⌊t/(mu*(R:ℝ))⌋:ℝ)+1/2)-t|≤(mu*(R:ℝ))/2 := by
  have hR1 : (1:ℝ)≤R := by exact_mod_cast (show 1≤R by omega)
  have hmuR : mu≤mu*(R:ℝ) := by nlinarith only [hR1,hmu]
  refine ⟨?_,?_,midpoint_error (mu*(R:ℝ)) t (mul_pos hmu (by exact_mod_cast hR))⟩
  · intro j
    have hc := coarseX_error mu R hmu hR (grid mu x) j
    have hf := center_grid_error mu hmu x j
    have ht := abs_add_le (coarseX mu R (grid mu x) j-center mu (grid mu x) j)
      (center mu (grid mu x) j-x j)
    rw [sub_add_sub_cancel] at ht
    linarith
  · intro i
    have hc := configuredNormal_error hk mu R hmu hR Fold Fcfg hCfg (grid mu x)
      (grid mu (quotient Fold x n)) i
    have hf := fine_graph_error hk mu hmu Fold hOld x n i
    have ht := abs_add_le
      (configuredNormal mu R Fold Fcfg (grid mu x) (grid mu (quotient Fold x n)) i-
        graphPoint Fold (center mu (grid mu x)) (center mu (grid mu (quotient Fold x n))) i)
      (graphPoint Fold (center mu (grid mu x)) (center mu (grid mu (quotient Fold x n))) i-n i)
    rw [sub_add_sub_cancel] at ht
    linarith

end CanonicalConfiguredPointRounding
