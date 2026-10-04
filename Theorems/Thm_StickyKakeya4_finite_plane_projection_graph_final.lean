import Theorems.Thm_StickyKakeya4_finite_plane_projection_graph_selection
import Theorems.Thm_StickyKakeya4_finite_plane_projection_graph_lift
import Theorems.Thm_StickyKakeya4_finite_plane_projection_graph_density
import Theorems.Thm_StickyKakeya4_finite_plane_projection_graph_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
open Finset
noncomputable section
open Classical
namespace FinitePlaneProjectionGraph
open FinitePlaneProjectionGrid

def graphMassLoss (J : ℕ) (rho KP KB beta : ℝ) : ℝ :=
  108 * graphLoss J rho KP beta * graphLoss J rho KB beta
lemma graphMassLoss_pos (J : ℕ) (rho : ℝ) {KP KB beta : ℝ}
    (hKP : 0 < KP) (hKB : 0 < KB) (hb : 0 < beta) : 0 < graphMassLoss J rho KP KB beta := by
  have hP := graphLoss_pos J rho hKP hb
  have hB := graphLoss_pos J rho hKB hb
  unfold graphMassLoss
  positivity

theorem exists_graph_aware_projection {X Y Z : Type*}
    (P : Finset X) (p : X → Point3) (B : Finset Y) (b : Y → Point3) (C : Finset Z)
    (G : Finset (X × (Y × Z))) (n J : ℕ)
    {rho KP KB beta r0 w0 w kappa epsilon theta : ℝ}
    (hP : P.Nonempty) (hBnon : B.Nonempty) (hC : C.Nonempty) (hmesh : mesh n ≤ rho)
    (hKP : 0 < KP) (hKB : 0 < KB) (hb : 0 < beta)
    (hr0 : 0 < r0) (hw0 : 0 < w0) (hw : 0 ≤ w) (hepsilon : 0 ≤ epsilon) (htheta : 0 ≤ theta)
    (hscalar : 3 * (kappa + epsilon + 128 * w / (r0 * w0) + 2 * mesh n) ≤ theta ^ 3)
    (hG : G ⊆ P ×ˢ (B ×ˢ C))
    (hdense : beta * P.card * B.card * C.card ≤ (G.card : ℝ))
    (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htopP : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (htopB : ∀ i ∈ B, ∀ k ∈ B, dist3 (b i) (b k) ≤ 2)
    (hKTP : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ KP * R / rho)
    (hKTB : ∀ i ∈ B, ∀ R : ℝ, rho ≤ R →
      ((B.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ KB * R / rho)
    (hB : ∀ i ∈ B, |(b i).1| ≤ 1 ∧ |(b i).2.1| ≤ 1 ∧ |(b i).2.2| ≤ 1)
    (hclose : ∀ i ∈ B,
      ((B.filter (fun j => dist3 (b i) (b j) ≤ r0)).card : ℝ) ≤ kappa * B.card)
    (hline : ∀ i ∈ B, ∀ j ∈ B, r0 < dist3 (b i) (b j) →
      ((originalCrossTube B b i j w0).card : ℝ) ≤ epsilon * B.card) :
    ∃ uv ∈ parameters n, ∃ S : Finset X, ∃ T : Finset Y, ∃ E : Finset (X × (Y × Z)),
      S ⊆ P ∧ T ⊆ B ∧ E ⊆ S ×ˢ (T ×ˢ C) ∧
      (G.card : ℝ) ≤ graphMassLoss J rho KP KB beta * E.card ∧
      beta * P.card ≤ graphMassLoss J rho KP KB beta * S.card ∧
      beta * B.card ≤ graphMassLoss J rho KP KB beta * T.card ∧
      beta * S.card * T.card * C.card ≤ graphMassLoss J rho KP KB beta * E.card ∧
      Set.InjOn (fun i => projectedCell uv rho (p i)) (↑S) ∧
      Set.InjOn (fun i => projectedCell uv rho (b i)) (↑T) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        2 * rho < ‖projectionLinear uv (p i) - projectionLinear uv (p j)‖) ∧
      (∀ i ∈ T, ∀ j ∈ T, i ≠ j →
        2 * rho < ‖projectionLinear uv (b i) - projectionLinear uv (b j)‖) ∧
      (∀ c : ℝ × ℝ, ∀ R : ℝ, rho ≤ R →
        ((S.filter (fun i => ‖projectionLinear uv (p i) - c‖ ≤ R)).card : ℝ) ≤
          50 * graphLoss J rho KP beta * R / rho) ∧
      (∀ c : ℝ × ℝ, ∀ R : ℝ, rho ≤ R →
        ((T.filter (fun i => ‖projectionLinear uv (b i) - c‖ ≤ R)).card : ℝ) ≤
          50 * graphLoss J rho KB beta * R / rho) ∧
      (∀ a d c : ℝ, max |a| |d| = 1 →
        ((projectedLineStrip T b uv a d c w).card : ℝ) ≤
          (graphMassLoss J rho KP KB beta / beta * theta) * T.card) ∧
      ∀ e ∈ E, ∃ old ∈ G,
        projectedCell uv rho (p old.1) = projectedCell uv rho (p e.1) ∧
        projectedCell uv rho (b old.2.1) = projectedCell uv rho (b e.2.1) ∧ old.2.2 = e.2.2 := by
  have hrho := (mesh_pos n).trans_le hmesh
  have hb1 := original_density_le_one P B C G hP hBnon hC hG hdense
  have hL := graphMassLoss_pos J rho hKP hKB hb
  obtain ⟨uv, huv, ca, _hca, cb, _hcb, H, hHQ, hmassH, hcolorH, htri⟩ :=
    exists_dense_colored_quotient P p B b C G n J hP hBnon hmesh hKP hKB hb
      (by positivity : 0 ≤ 16 * w) (mul_pos hr0 hw0) hG hdense hJ htopP htopB hKTP hKTB
  let U := graphRetained P p J uv rho KP beta
  let V := graphRetained B b J uv rho KB beta
  let f := fun i => projectedCell uv rho (p i)
  let g := fun j => projectedCell uv rho (b j)
  obtain ⟨S, T, E, hSU, hTV, hSinj, hTinj, hSim, hTim, _hEdef, hE, hEcard,
      _hEsupport, _hEtsupport, hwitness⟩ := exists_selected_graph_lift U V C (goodEdges G U V)
        f g H (goodEdges_product P B C G U V hG) hHQ
  have hSP : S ⊆ P := hSU.trans (graphRetained_subset P p J uv rho KP beta)
  have hTB : T ⊆ B := hTV.trans (graphRetained_subset B b J uv rho KB beta)
  have hmass : (G.card : ℝ) ≤ graphMassLoss J rho KP KB beta * E.card := by
    simpa only [hEcard, graphMassLoss] using hmassH
  obtain ⟨hSret, hTret, hEdense⟩ := original_vertex_retention_from_graph_mass
    P S B T C G E hP hBnon hC hb.le hL.le hSP hTB hE hdense hmass
  have hSim' : S.image f = H.image Prod.fst := by
    ext k
    simpa only [Finset.mem_image] using Finset.ext_iff.mp hSim k
  have hTim' : T.image g = H.image (fun q => q.2.1) := by
    ext k
    simpa only [Finset.mem_image] using Finset.ext_iff.mp hTim k
  obtain ⟨hScolor, hTcolor⟩ := selected_graph_lift_colors S T f g H ca cb hSim' hTim' hcolorH
  have hSsep := fixed_color_projection_separation S p uv hrho ca hSinj hScolor
  have hTsep := fixed_color_projection_separation T b uv hrho cb hTinj hTcolor
  refine ⟨uv, huv, S, T, E, hSP, hTB, hE, hmass, hSret, hTret, hEdense,
    hSinj, hTinj, hSsep, hTsep, ?_, ?_, ?_, ?_⟩
  · intro c R hR
    rw [← projectedBall_eq_native_ball]
    exact graphRetained_ball_bound P S p J uv c hP hrho hKP hb hb1 hR hJ hSU htopP hKTP
  · intro c R hR
    rw [← projectedBall_eq_native_ball]
    exact graphRetained_ball_bound B T b J uv c hBnon hrho hKB hb hb1 hR hJ hTV htopB hKTB
  · intro a d c hnormal
    have hdeg := original_degenerate_triple_count B b hw0.le hepsilon hclose hline
    have hcube := projected_line_strip_cube B b (c := c) huv hw hnormal hB
    have hsmall : ((projectedLineStrip B b uv a d c w).card : ℝ) ^ 3 ≤
        (3 * (kappa + epsilon + 128 * w / (r0 * w0) + 2 * mesh n)) * (B.card : ℝ) ^ 3 := by
      calc
        _ ≤ 3 * (((degenerateTriples B b (r0 * w0)).card : ℝ) +
            (8 * (16 * w) / (r0 * w0) + 2 * mesh n) * (B.card : ℝ) ^ 3) := hcube.trans htri
        _ ≤ 3 * ((kappa + epsilon) * (B.card : ℝ) ^ 3 +
            (8 * (16 * w) / (r0 * w0) + 2 * mesh n) * (B.card : ℝ) ^ 3) := by linarith
        _ = _ := by ring
    have hfrac := line_strip_fraction_of_cube B b uv a d c w theta _ htheta hscalar hsmall
    have hBmass := reciprocal_population_bound _ _ _ _ hb hTret
    have hh := line_fraction_to_original_subset B T b uv hTB htheta hBmass hfrac
    convert hh using 1
    ring
  · intro e he
    obtain ⟨old, hold, hfa, hgb, hc⟩ := hwitness e he
    exact ⟨old, goodEdges_subset G U V hold, hfa, hgb, hc⟩

theorem retained_edges_original_error {X Y Z : Type*}
    (G E : Finset (X × (Y × Z))) (p : X → Point3) (b : Y → Point3)
    (target : X × (Y × Z) → Point3) (scalar : Z → ℝ) (anchor : Point3)
    {n : ℕ} {uv : ℝ × ℝ} {rho error : ℝ} (huv : uv ∈ parameters n) (hrho : 0 < rho)
    (hOriginal : ∀ old ∈ G, ‖target old - p old.1 - scalar old.2.2 • (b old.2.1 - anchor)‖ ≤ error)
    (hWitness : ∀ e ∈ E, ∃ old ∈ G,
      projectedCell uv rho (p old.1) = projectedCell uv rho (p e.1) ∧
      projectedCell uv rho (b old.2.1) = projectedCell uv rho (b e.2.1) ∧ old.2.2 = e.2.2) :
    ∀ e ∈ E, ∃ old ∈ G, old.2.2 = e.2.2 ∧
      ‖projectionLinear uv (target old) - projectionLinear uv (p e.1) -
        scalar e.2.2 • (projectionLinear uv (b e.2.1) - projectionLinear uv anchor)‖ ≤
          2 * error + (1 + |scalar e.2.2|) * rho := by
  intro e he
  obtain ⟨old, hold, hp, hb, hc⟩ := hWitness e he
  refine ⟨old, hold, hc, ?_⟩
  have hh := original_edge_same_cell_transport huv hrho (hOriginal old hold) hp hb
  simpa only [hc] using hh
end FinitePlaneProjectionGraph
