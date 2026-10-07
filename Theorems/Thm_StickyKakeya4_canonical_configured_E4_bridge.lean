import Theorems.Thm_StickyKakeya4_canonical_configured_point_rounding
import Theorems.Thm_StickyKakeya4_native_rounded_rotated_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace CanonicalConfiguredE4Bridge
open Classical Finset StickyKakeya4 CanonicalGridRecoding CanonicalConfiguredPointRounding
open NativeMatrixHeightWholePoint NativeRoundedRotatedSelection
open scoped BigOperators

/-- The two actual tangent/normal splits of four-dimensional spacetime. -/
inductive Split where
  | oneTwo
  | twoOne

@[reducible] def tangentDim : Split → ℕ | .oneTwo => 1 | .twoOne => 2
@[reducible] def normalDim : Split → ℕ | .oneTwo => 2 | .twoOne => 1

def tangent : (s : Split) → E4 → (Fin (tangentDim s) → ℝ)
  | .oneTwo,z => ![z 0]
  | .twoOne,z => ![z 0,z 1]

def normal : (s : Split) → E4 → (Fin (normalDim s) → ℝ)
  | .oneTwo,z => ![z 1,z 2]
  | .twoOne,z => ![z 2]

def assemble : (s : Split) → (Fin (tangentDim s) → ℝ) →
    (Fin (normalDim s) → ℝ) → ℝ → E4
  | .oneTwo,x,n,t => WithLp.toLp 2 ![x 0,n 0,n 1,t]
  | .twoOne,x,n,t => WithLp.toLp 2 ![x 0,x 1,n 0,t]

def configuredChart (s : Split) (mu : ℝ) (R : ℕ)
    (Fold Fcfg : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) (z : E4) : E4 :=
  assemble s
    (coarseX mu R (grid mu (tangent s z)))
    (configuredNormal mu R Fold Fcfg (grid mu (tangent s z))
      (grid mu (quotient Fold (tangent s z) (normal s z))))
    ((mu*(R:ℝ))*((⌊z 3/(mu*(R:ℝ))⌋:ℝ)+1/2))

/-- Every coordinate of the literal configured point is controlled.
The height is coordinate3 in both orthonormal-chart layouts. -/
theorem configured_coordinate_error (s : Split) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R)
    (Fold Fcfg : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hOld : ∀i j,|Fold i j|≤1/4) (hCfg : ∀i j,|Fcfg i j|≤1/4) (z : E4) :
    ∀j : Fin 4,|configuredChart s mu R Fold Fcfg z j-z j|≤(3/2:ℝ)*(mu*(R:ℝ)) := by
  have hrho : 0 < mu*(R:ℝ) := mul_pos hmu (by exact_mod_cast hR)
  cases s with
  | oneTwo =>
      obtain ⟨hX,hN,hT⟩ := actual_coordinate_errors (by decide : tangentDim .oneTwo≤2)
        mu R hmu hR Fold Fcfg hOld hCfg (tangent .oneTwo z) (normal .oneTwo z) (z 3)
      intro j
      fin_cases j
      · exact (hX 0).trans (by linarith)
      · exact hN 0
      · exact hN 1
      · exact hT.trans (by linarith)
  | twoOne =>
      obtain ⟨hX,hN,hT⟩ := actual_coordinate_errors (by decide : tangentDim .twoOne≤2)
        mu R hmu hR Fold Fcfg hOld hCfg (tangent .twoOne z) (normal .twoOne z) (z 3)
      intro j
      fin_cases j
      · exact (hX 0).trans (by linarith)
      · exact (hX 1).trans (by linarith)
      · exact hN 0
      · exact hT.trans (by linarith)

lemma dist_le_three_of_coordinate_error (rho : ℝ) (hrho : 0≤rho) (a b : E4)
    (H : ∀j : Fin 4,|a j-b j|≤(3/2:ℝ)*rho) : dist a b≤3*rho := by
  have hs : dist a b^2≤(3*rho)^2 := by
    rw [PiLp.dist_sq_eq_of_L2]
    calc
      _ ≤ ∑_j : Fin 4,((3/2:ℝ)*rho)^2 := by
        apply sum_le_sum
        intro j _hj
        have hj : dist (a j) (b j)≤(3/2:ℝ)*rho := by
          simpa only [Real.dist_eq] using H j
        nlinarith [show 0≤dist (a j) (b j) from dist_nonneg]
      _ = _ := by simp; ring
  nlinarith [show 0≤dist a b from dist_nonneg]

theorem configuredChart_distance (s : Split) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R)
    (Fold Fcfg : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hOld : ∀i j,|Fold i j|≤1/4) (hCfg : ∀i j,|Fcfg i j|≤1/4) (z : E4) :
    dist (configuredChart s mu R Fold Fcfg z) z≤3*(mu*(R:ℝ)) :=
  dist_le_three_of_coordinate_error (mu*(R:ℝ))
    (mul_pos hmu (by exact_mod_cast hR)).le _ _
    (configured_coordinate_error s mu R hmu hR Fold Fcfg hOld hCfg z)

/-- Configured coordinates of the SAME physical point in its fixed
orthonormal chart. No point representative or new source is chosen. -/
def configuredPoint (s : Split) (mu : ℝ) (R : ℕ)
    (Fold Fcfg : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c p : E4) : E4 :=
  configuredChart s mu R Fold Fcfg (O (p-c))

/-- This discharges the geometric hround premise with C=3. -/
theorem configuredPoint_distance (s : Split) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R)
    (Fold Fcfg : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hOld : ∀i j,|Fold i j|≤1/4) (hCfg : ∀i j,|Fcfg i j|≤1/4)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c p : E4) :
    dist (configuredPoint s mu R Fold Fcfg O c p) (O (p-c))≤3*(mu*(R:ℝ)) :=
  configuredChart_distance s mu R hmu hR Fold Fcfg hOld hCfg (O (p-c))

theorem actual_rounding_modulus : roundingModulus (3:ℝ)=17 := by
  norm_num [roundingModulus]

theorem actual_rounding_cost (K : ℕ) : (roundingModulus (3:ℝ))^(4*K)=83521^K := by
  rw [actual_rounding_modulus,pow_mul]
  norm_num

/-- Whole original-edge selection for the literal recoding. Its rounding
bound is proved internally. Original point positions and every surviving
point's entire old incidence fiber stay fixed. -/
theorem select_actual_original_edges {E P : Type*} [DecidableEq P]
    (s : Split) (K : ℕ) (A : Finset E) (point : E → P) (position : P → E4)
    (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (hR : 0 < R)
    (Fold Fcfg : Fin K → P → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hOld : ∀i,∀p∈A.image point,∀a b,|Fold i p a b|≤1/4)
    (hCfg : ∀i,∀p∈A.image point,∀a b,|Fcfg i p a b|≤1/4)
    (O : Fin K → E4 ≃ₗᵢ[ℝ] E4) (c : Fin K → E4) (rho : Fin K → ℝ)
    (hscale : ∀i,mu*(R:ℝ)≤rho i) :
    ∃B⊆A.image point,let T := edgeLift A point B
      T⊆A ∧ A.card≤83521^K*T.card ∧
      (∀p∈B,T.filter (fun x => point x=p)=A.filter (fun x => point x=p)) ∧
      ∀i,∀x∈T,∀y∈T,
        wzDyadicCellIndex (rho i)
          (configuredPoint s mu R (Fold i (point x)) (Fcfg i (point x)) (O i) (c i) (position (point x)))=
        wzDyadicCellIndex (rho i)
          (configuredPoint s mu R (Fold i (point y)) (Fcfg i (point y)) (O i) (c i) (position (point y))) →
        wzDyadicCellIndex (rho i) (position (point x))=
          wzDyadicCellIndex (rho i) (position (point y)) := by
  let configured := fun i p => configuredPoint s mu R (Fold i p) (Fcfg i p) (O i) (c i) (position p)
  have hround : ∀i,∀p∈A.image point,
      dist (configured i p) (O i (position p-c i))≤(3:ℝ)*(mu*(R:ℝ)) := by
    intro i p hp
    exact configuredPoint_distance s mu R hmu hR (Fold i p) (Fcfg i p)
      (hOld i p hp) (hCfg i p hp) (O i) (c i) (position p)
  obtain ⟨B,hB,hTA,hret,hfiber,hcell⟩ := NativeRoundedRotatedSelection.select_original_edges K A point position
    configured O c 3 (mu*(R:ℝ)) rho (by norm_num) (mul_pos hmu (by exact_mod_cast hR)) hscale hround
  rw [actual_rounding_cost] at hret
  exact ⟨B,hB,hTA,hret,hfiber,hcell⟩

end CanonicalConfiguredE4Bridge
