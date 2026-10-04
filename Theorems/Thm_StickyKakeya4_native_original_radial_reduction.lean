import Theorems.Thm_StickyKakeya4_native_original_annular_row_bound
import Theorems.Thm_StickyKakeya4_native_radial_densest_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeOriginalRadialReduction
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl OriginalDensestWideExtension
open NativeRadialDensestGraph OriginalAnnularRowCover NativeOriginalAnnularRowBound

/-- A closed original-input Step1-to-Step2 caller. It constructs the actual
dyadic mesh, densest original graph bin, and every annular row bound from
original physical violations and original point Frostman data. No selected
graph profile, ball cap, representative family, or row-count certificate is
an assumption. All original graph properties survive by literal inclusion. -/
theorem exists_original_densest_graph_with_annular_control
    (Pts : Finset Point) (G1 : Finset Pair)
    (delta eta eta' t sigma s zeta r : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (ht2 : t≤2)
    (hsigma : 0≤sigma) (hsigma1 : sigma≤1) (hsgap : sigma≤s) (hgap : s-sigma≤zeta)
    (hr : 0<r) (hr1 : r≤1)
    (hG1 : G1.Nonempty) (hG1P : G1⊆Pts.product Pts)
    (hbox : ∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1)
    (hdistinct : ∀ z∈G1, z.1≠z.2)
    (hviol : ∀ z∈G1, ∃ R : ℝ, delta≤R ∧ R≤1 ∧
      delta^(-zeta)*R^s*Pts.card≤(physicalPairTube Pts R z).card)
    (hfrostman : ∀ q∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤R)).card : ℝ)≤delta^(-eta)*R^t*Pts.card) :
    ∃ n : ℕ, ∃ rho : ℝ, ∃ j : ℕ, ∃ G2 : Finset Pair,
      delta≤dyadicRadius n ∧ dyadicRadius n≤2*delta ∧
      rho∈scaleMenu n ∧ delta≤rho ∧ rho≤1 ∧ j<Nat.log 2 Pts.card+1 ∧
      G2⊆G1 ∧ G2.Nonempty ∧ G1.card≤(n+1)*(Nat.log 2 Pts.card+1)*G2.card ∧
      delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*(2^j:ℕ) ∧
      delta^(s-sigma-zeta)*rho^sigma≤2^sigma ∧
      (∀ z∈G2, 2^j≤(physicalPairTube Pts rho z).card ∧
        (physicalPairTube Pts rho z).card<2^(j+1) ∧
        ∀ R : ℝ, rho≤R → R≤1 → ((physicalPairTube Pts R z).card : ℝ)≤
          2^(sigma+1)*(R/rho)^sigma*(2^j:ℕ)) ∧
      ∀ p∈Pts, ∀ tau : ℝ, 0<tau → tau≤1/2 → delta≤2*tau →
        ((badPartners Pts G2 p (r^(-3:ℝ)*rho) tau
          (delta^(-eta')*tau^(t-sigma)*(2^j:ℕ))).card : ℝ)≤
          608*r^(-3*sigma)*delta^(eta'-eta)*Pts.card := by
  obtain ⟨n,hmesh,hbottom⟩ := exists_original_dyadic_mesh delta hd hd1
  obtain ⟨rho,hrho,hdrho,j,hj,G2,hG2G1,hG2,hmass,hgain,hscale,hdata⟩ :=
    exists_native_densest_original_graph Pts G1 n delta sigma s zeta hd hmesh hbottom
      hsigma hsgap hG1 hG1P hviol
  have hbounds := (scale_menu_bounds n).2.2 rho hrho
  have hsource : rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*(2^j:ℕ) :=
    original_source_density_of_native_gain Pts delta sigma s zeta rho (2^j:ℕ)
      hd hd1 hbounds.1.le hgap hgain
  refine ⟨n,rho,j,G2,hmesh,hbottom,hrho,hdrho,hbounds.2.2,hj,hG2G1,hG2,hmass,
    hgain,hscale,hdata,?_⟩
  intro p hp tau htau htauhalf hquery
  exact native_original_annular_bad_row Pts G2 p n delta eta eta' t sigma rho (2^j:ℕ) r tau
    hd ht2 hsigma hsigma1 (by positivity) hr hr1 htau htauhalf hquery hrho hp hbox
    (fun z hz => hdistinct z (hG2G1 hz)) (fun z hz => (hdata z hz).2.2)
    hsource hfrostman

end NativeOriginalRadialReduction
