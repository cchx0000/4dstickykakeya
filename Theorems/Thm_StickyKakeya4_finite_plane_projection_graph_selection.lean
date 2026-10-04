import Theorems.Thm_StickyKakeya4_finite_plane_projection_graph_core
import Theorems.Thm_StickyKakeya4_finite_plane_projection_allscale
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
open Finset
noncomputable section
open Classical
namespace FinitePlaneProjectionGraph
open FinitePlaneProjectionGrid

def graphLoss (J : ℕ) (rho K beta : ℝ) : ℝ := 4 * allscaleLoss J rho K / beta
def graphRetained {X : Type*} (P : Finset X) (p : X → Point3)
    (J : ℕ) (uv : ℝ × ℝ) (rho K beta : ℝ) : Finset X :=
  retainedScales P p (dyadicScales J rho) uv rho (graphLoss J rho K beta)
lemma graphLoss_pos (J : ℕ) (rho : ℝ) {K beta : ℝ} (hK : 0 < K) (hb : 0 < beta) :
    0 < graphLoss J rho K beta := by
  have hL := allscaleLoss_pos J rho hK
  unfold graphLoss
  positivity
lemma graphLoss_ge (J : ℕ) (rho : ℝ) {K beta : ℝ}
    (hK : 0 < K) (hb : 0 < beta) (hb1 : beta ≤ 1) : K ≤ graphLoss J rho K beta := by
  have hL := allscaleLoss_pos J rho hK
  have hKL := allscaleLoss_ge J rho hK.le
  unfold graphLoss
  apply (le_div_iff₀ hb).2
  nlinarith
lemma graphRetained_subset {X : Type*} (P : Finset X) (p : X → Point3)
    (J : ℕ) (uv : ℝ × ℝ) (rho K beta : ℝ) : graphRetained P p J uv rho K beta ⊆ P :=
  retainedScales_subset P p _ uv rho _
lemma graphRetained_deleted_mass {X : Type*} (P : Finset X) (p : X → Point3)
    (J : ℕ) (uv : ℝ × ℝ) {rho K beta : ℝ} (hrho : 0 < rho) (hK : 0 < K) (hb : 0 < beta)
    (henergy : scaleEnergy P p (dyadicScales J rho) uv rho ≤ allscaleLoss J rho K / 2 * P.card) :
    ((P \ graphRetained P p J uv rho K beta).card : ℝ) ≤ beta / 8 * P.card := by
  have hD := graphLoss_pos J rho hK hb
  have he : P \ graphRetained P p J uv rho K beta =
      badScales P p (dyadicScales J rho) uv rho (graphLoss J rho K beta) := by
    ext i
    simp only [graphRetained, retainedScales, Finset.mem_sdiff]
    constructor
    · rintro ⟨hiP, hiNot⟩
      by_contra hiBad
      exact hiNot ⟨hiP, hiBad⟩
    · intro hiBad
      exact ⟨badScales_subset P p _ uv rho _ hiBad, fun hi => hi.2 hiBad⟩
  rw [he]
  have hmass := (badScales_mass P p (dyadicScales J rho) uv hrho hD.le
    (fun r hr => hrho.trans_le (dyadicScales_ge_base J hrho.le hr))).trans henergy
  have hcancel : graphLoss J rho K beta * beta = 4 * allscaleLoss J rho K := by
    unfold graphLoss
    field_simp
  nlinarith
lemma graphRetained_cell_bound {X : Type*} (P : Finset X) (p : X → Point3)
    (J : ℕ) (uv : ℝ × ℝ) {rho K beta : ℝ} (hrho : 0 < rho)
    {i : X} (hi : i ∈ graphRetained P p J uv rho K beta) :
    (((graphRetained P p J uv rho K beta).filter (fun k =>
      projectedCell uv rho (p k) = projectedCell uv rho (p i))).card : ℝ) ≤
      graphLoss J rho K beta := by
  have hsub := Finset.filter_subset_filter
    (fun k => projectedCell uv rho (p k) = projectedCell uv rho (p i))
    (graphRetained_subset P p J uv rho K beta)
  have hh := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (retainedScales_cell_bound P p (dyadicScales J rho) uv rho (graphLoss J rho K beta)
      (base_mem_dyadicScales J rho) hi)
  simpa only [mul_div_cancel_right₀ _ hrho.ne'] using hh
lemma graphRetained_ball_bound {X : Type*} (P Q : Finset X) (p : X → Point3)
    (J : ℕ) (uv c : ℝ × ℝ) {rho K beta R : ℝ}
    (hP : P.Nonempty) (hrho : 0 < rho) (hK : 0 < K) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hR : rho ≤ R) (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (hQ : Q ⊆ graphRetained P p J uv rho K beta)
    (htop : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (hKT : ∀ i ∈ P, ∀ r : ℝ, rho ≤ r →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ r)).card : ℝ) ≤ K * r / rho) :
    ((projectedBall Q p uv c R).card : ℝ) ≤ 50 * graphLoss J rho K beta * R / rho := by
  by_cases hR2 : R ≤ 2
  · exact retainedScales_allscale_ball_bound P Q p J uv c hrho (graphLoss_pos J rho hK hb).le
      hR hR2 hJ hQ
  · exact projectedBall_wide_bound P Q p uv c hP
      (hQ.trans (graphRetained_subset P p J uv rho K beta)) hrho hK.le
      (graphLoss_ge J rho hK hb hb1) hR (le_of_not_ge hR2) htop hKT

theorem exists_dense_colored_quotient {X Y Z : Type*}
    (P : Finset X) (p : X → Point3) (B : Finset Y) (b : Y → Point3) (C : Finset Z)
    (G : Finset (X × (Y × Z))) (n J : ℕ) {rho KP KB beta r A : ℝ}
    (hP : P.Nonempty) (hB : B.Nonempty) (hmesh : mesh n ≤ rho)
    (hKP : 0 < KP) (hKB : 0 < KB) (hb : 0 < beta) (hr : 0 ≤ r) (hA : 0 < A)
    (hG : G ⊆ P ×ˢ (B ×ˢ C))
    (hdense : beta * P.card * B.card * C.card ≤ (G.card : ℝ))
    (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htopP : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (htopB : ∀ i ∈ B, ∀ k ∈ B, dist3 (b i) (b k) ≤ 2)
    (hKTP : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ KP * R / rho)
    (hKTB : ∀ i ∈ B, ∀ R : ℝ, rho ≤ R →
      ((B.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ KB * R / rho) :
    ∃ uv ∈ parameters n, ∃ ca ∈ nineColors, ∃ cb ∈ nineColors,
      ∃ H : Finset ((ℤ × ℤ) × ((ℤ × ℤ) × Z)),
        H ⊆ quotientEdges (goodEdges G (graphRetained P p J uv rho KP beta)
          (graphRetained B b J uv rho KB beta))
          (fun i => projectedCell uv rho (p i)) (fun j => projectedCell uv rho (b j)) ∧
        (G.card : ℝ) ≤ (108 * graphLoss J rho KP beta * graphLoss J rho KB beta) * H.card ∧
        (∀ e ∈ H, cellColor e.1 = ca ∧ cellColor e.2.1 = cb) ∧
        ((smallProjectedTriples B b uv r).card : ℝ) ≤
          3 * (((degenerateTriples B b A).card : ℝ) +
            (8 * r / A + 2 * mesh n) * (B.card : ℝ) ^ 3) := by
  have hrho := (mesh_pos n).trans_le hmesh
  have hDP := graphLoss_pos J rho hKP hb
  have hDB := graphLoss_pos J rho hKB hb
  obtain ⟨uv, huv, hEP, hEB, htri⟩ := exists_common_scale_energies P p B b n J
    hP hB hmesh hKP hKB hr hA hJ htopP htopB hKTP hKTB
  let U := graphRetained P p J uv rho KP beta
  let V := graphRetained B b J uv rho KB beta
  let f := fun i => projectedCell uv rho (p i)
  let g := fun j => projectedCell uv rho (b j)
  let E := goodEdges G U V
  let Q := quotientEdges E f g
  have hbadP := graphRetained_deleted_mass P p J uv hrho hKP hb hEP
  have hbadB := graphRetained_deleted_mass B b J uv hrho hKB hb hEB
  have hgood : 3 * (G.card : ℝ) / 4 ≤ E.card :=
    goodEdges_three_quarters_of_density P B C G U V hG hdense hbadP hbadB
  have hquot : (E.card : ℝ) ≤
      (graphLoss J rho KP beta * graphLoss J rho KB beta) * Q.card :=
    quotientEdges_card_bound U V C E f g hDP.le hDB.le (goodEdges_product P B C G U V hG)
      (fun i hi => by simpa only [U, f] using graphRetained_cell_bound P p J uv hrho hi)
      (fun j hj => by simpa only [V, g] using graphRetained_cell_bound B b J uv hrho hj)
  obtain ⟨ca, hca, cb, hcb, H, hHQ, hQcard, hcolor⟩ := exists_edge_color Q
  have hQr : (Q.card : ℝ) ≤ 81 * H.card := by exact_mod_cast hQcard
  have hmul := mul_le_mul_of_nonneg_left hQr
    (show 0 ≤ graphLoss J rho KP beta * graphLoss J rho KB beta by positivity)
  refine ⟨uv, huv, ca, hca, cb, hcb, H, hHQ, ?_, hcolor, htri⟩
  nlinarith
end FinitePlaneProjectionGraph
