import Theorems.Thm_StickyKakeya4_native_weak_radial_pair_graph
import Theorems.Thm_StickyKakeya4_four_unit_tube_band_cover
import Theorems.Thm_StickyKakeya4_planar_frostman_ball_conversion

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace PhysicalWeakRadialPairGraph
open OriginalPairStripGeometry NativeRichPairTubeFamily NativeRichStripRepresentatives
open PlanarStripIntersection FourUnitTubeBandCover PlanarFrostmanBallConversion

/-- The finite A.2 graph from ORIGINAL Euclidean ball counts and ORIGINAL
physical unit-tube two-ends counts. Every intermediate geometry/profile input
is derived, and all source query-radius bounds are explicit. -/
theorem original_physical_weak_radial_graph
    (Pts : Finset Point) (delta K t w rho lam theta width eta : ℝ)
    (hPts : Pts.Nonempty) (hdelta : 0≤delta) (hdelta1 : delta≤1)
    (hK : 0≤K) (ht : t≤2) (hw : 0≤w) (hrho : 0<rho)
    (hlam : 0<lam) (htheta : 0<theta) (heta : 0≤eta)
    (hqueryRhoLow : delta≤2*rho) (hqueryRhoHigh : 2*rho≤1)
    (hqueryRLow : delta≤2*(4*(11*w/rho)/theta))
    (hqueryRHigh : 2*(4*(11*w/rho)/theta)≤1)
    (hsmall : 4*K*rho^t≤lam^2/2)
    (hband : 3*(11*w/rho)+2*theta≤width/2)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hfrostman : ∀ p∈Pts, ∀ r : ℝ, delta≤r → r≤1 →
      ((Pts.filter (fun q => euclideanDistance p q≤r)).card : ℝ)≤K*r^t*Pts.card)
    (htwoends : ∀ nx ny c h : ℝ, nx^2+ny^2=1 →
      ((unitTube Pts nx ny c h width).card : ℝ)≤eta*Pts.card) :
    let R := 4*(11*w/rho)/theta
    ∃ G : Finset Pair, G⊆Pts.product Pts ∧
      (∀ z∈G, z.1≠z.2 ∧ ((pairSupport Pts w z).card : ℝ)<lam*Pts.card) ∧
      lam^2*((Pts.card : ℝ)^2-G.card)≤
        (4*lam^2*eta+16*K*R^t+lam^2*K*delta^t)*(Pts.card : ℝ)^2 := by
  classical
  let R := 4*(11*w/rho)/theta
  have hR : 0≤R := by dsimp [R]; positivity
  have hrho1 : rho≤1 := by linarith
  have hrootBalls (p : Point) (hp : p∈Pts) :
      ((Pts.filter (fun q => boxDistance p q≤rho)).card : ℝ)≤
        (4*K*rho^t)*Pts.card :=
    box_frostman_bound Pts p K t rho hK hrho.le ht
      (hfrostman p hp (2*rho) hqueryRhoLow hqueryRhoHigh)
  have hwideBalls (p : Point) (hp : p∈Pts) :
      ((Pts.filter (fun q => boxDistance p q≤R)).card : ℝ)≤
        (4*K*R^t)*Pts.card :=
    box_frostman_bound Pts p K t R hK hR ht
      (hfrostman p hp (2*R) hqueryRLow hqueryRHigh)
  have hbandCounts (z : Pair) (hz : z∈candidates Pts) :
      ((pairSupport Pts (3*(11*w/rho)+2*theta) z).card : ℝ)≤(4*eta)*Pts.card := by
    have hn := original_pair_normalized z (Finset.mem_filter.mp hz).2
    have h := band_card_le_four Pts (normalX z) (normalY z) (offset z)
      (3*(11*w/rho)+2*theta) width eta hn.2.2 hband hbox htwoends
    exact h
  obtain ⟨G,hGP,hGood,hcount⟩ := NativeWeakRadialPairGraph.finite_weak_radial_graph
    Pts w rho lam (4*K*rho^t) theta (4*K*R^t) (4*eta) hPts hw hrho hrho1 hlam
    (by positivity) hsmall htheta (by positivity) (by positivity)
    hbox hrootBalls hwideBalls hbandCounts
  have hdiag := diagonal_charge Pts hPts delta K t hdelta
    (fun p hp => hfrostman p hp delta le_rfl hdelta1)
  have hdiag' := mul_le_mul_of_nonneg_left hdiag (sq_nonneg lam)
  refine ⟨G,hGP,hGood,?_⟩
  nlinarith only [hcount,hdiag']

end PhysicalWeakRadialPairGraph
