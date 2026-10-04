import Theorems.Thm_StickyKakeya4_physical_weak_radial_pair_graph
import Theorems.Thm_StickyKakeya4_original_physical_pair_tube
import Theorems.Thm_StickyKakeya4_native_a2_power_budget
import Theorems.Thm_StickyKakeya4_native_a2_dilated_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeA2DilatedCaller
open OriginalPairStripGeometry NativeRichPairTubeFamily FourUnitTubeBandCover
open PlanarFrostmanBallConversion OriginalPhysicalPairTube
open NativeA2PowerBudget NativeA2ParameterIdentities NativeA2DilatedParameters

/-- The fixed-dilation native weak radial graph, derived from the ORIGINAL Euclidean
Frostman profile and ORIGINAL physical unit-tube two-ends profile. Every
point queried belongs to P, and all query radii lie in [delta,1]. -/
theorem dilated_native_weak_radial_graph
    (Pts : Finset Point) (delta t eps1 eps2 chi C : ℝ)
    (hPts : Pts.Nonempty) (hd : 0<delta) (hd1 : delta≤1/2)
    (ht : 0<t) (ht2 : t≤2) (_he1 : 0<eps1) (he1small : eps1<1/8)
    (_he2 : 0<eps2) (hC : 1≤C) (_hchi : 0<chi) (hchismall : chi≤t*eps1/12)
    (hscale : delta^eps1≤1/(1408*C))
    (hoverlap : delta^(7*t*eps1/4)≤1/8)
    (htransverse : delta^(t*eps1/4)≤1/(48*(704*C)^2))
    (hends : delta^(eps2/2)≤1/12) (hdiag : delta^(t/2)≤1/12)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hfrostman : ∀ p∈Pts, ∀ r : ℝ, delta≤r → r≤1 →
      ((Pts.filter (fun q => euclideanDistance p q≤r)).card : ℝ)≤
        delta^(-chi)*r^t*Pts.card)
    (htwoends : ∀ nx ny c h : ℝ, nx^2+ny^2=1 →
      ((unitTube Pts nx ny c h (delta^eps1)).card : ℝ)≤delta^eps2*Pts.card) :
    ∃ G : Finset Pair, G⊆Pts.product Pts ∧
      (∀ z∈G, z.1≠z.2 ∧
        ((physicalPairTube Pts (C*delta^(4*eps1)) z).card : ℝ)<delta^chi*Pts.card) ∧
      (1-delta^(min (t*eps1/2) (eps2/2)))*(Pts.card : ℝ)^2≤G.card := by
  classical
  let theta := delta^eps1
  let lam := delta^chi
  have htheta : 0<theta := Real.rpow_pos_of_pos hd _
  have hlam : 0<lam := Real.rpow_pos_of_pos hd _
  have hdunit : delta≤1 := by linarith
  have hCpos : 0<C := zero_lt_one.trans_le hC
  obtain ⟨hW,hR,hRhoLow,hRhoHigh,hRLow,hRHigh,hband⟩ :=
    dilated_geometric_scales delta eps1 C hd hdunit he1small hC hscale
  change 11*(2*C*theta^4)/(theta^2)=22*C*theta^2 at hW
  change 4*(11*(2*C*theta^4)/(theta^2))/(theta/8)=704*C*theta at hR
  have hoverlap' : 8*delta^(2*t*eps1-3*chi)≤1 := by
    have hp := Real.rpow_le_rpow_of_exponent_ge hd hdunit
      (show 7*t*eps1/4≤2*t*eps1-3*chi by nlinarith only [hchismall])
    nlinarith only [hp,hoverlap]
  have hbudget := dilated_power_budget delta t eps1 eps2 chi C
    hd hdunit ht he1small hC hchismall htransverse hends hdiag
  have habsorb : 4*delta^(-chi)*(theta^2)^t≤lam^2/2 := by
    have hid := overlap_power_identity delta eps1 t chi hd
    have hm := mul_le_mul_of_nonneg_left hoverlap' (sq_nonneg lam)
    dsimp [theta,lam] at *
    nlinarith only [hid,hm]
  obtain ⟨G,hGP,hgood,hcount⟩ :=
    PhysicalWeakRadialPairGraph.original_physical_weak_radial_graph
      Pts delta (delta^(-chi)) t (2*C*theta^4) (theta^2) lam (theta/8) theta (delta^eps2)
      hPts hd.le hdunit (Real.rpow_nonneg hd.le _) ht2 (by positivity) (by positivity)
      hlam (by positivity) (Real.rpow_nonneg hd.le _) hRhoLow hRhoHigh
      (by simpa only [hR] using hRLow) (by simpa only [hR] using hRHigh)
      habsorb (by simpa only [hW] using hband) hbox hfrostman htwoends
  have hcount' : lam^2*((Pts.card : ℝ)^2-G.card)≤
      (4*lam^2*delta^eps2+16*delta^(-chi)*(704*C*theta)^t+
        lam^2*delta^(-chi)*delta^t)*(Pts.card : ℝ)^2 := by
    simpa only [hR] using hcount
  have htrans := transverse_constant_power_identity delta eps1 t chi (704*C) hd (by positivity)
  have hdiagonal := diagonal_power_identity delta t chi hd
  have hcoefficient :
      4*lam^2*delta^eps2+16*delta^(-chi)*(704*C*theta)^t+
        lam^2*delta^(-chi)*delta^t =
      lam^2*(4*delta^eps2+16*(704*C)^t*delta^(t*eps1-3*chi)+delta^(t-chi)) := by
    calc
      _ = 4*lam^2*delta^eps2+16*(delta^(-chi)*(704*C*theta)^t)+
        lam^2*(delta^(-chi)*delta^t) := by ring
      _ = _ := by rw [htrans,hdiagonal]; ring
  rw [hcoefficient] at hcount'
  have h704 : (704*C)^t≤(704*C)^2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by nlinarith only [hC] : (1:ℝ)≤704*C) ht2
    simpa only [Real.rpow_two] using h
  have h704term := mul_le_mul_of_nonneg_right h704
    (Real.rpow_nonneg hd.le (t*eps1-3*chi))
  have hdiagpos := Real.rpow_nonneg hd.le (t-chi)
  have hcoefle : 4*delta^eps2+16*(704*C)^t*delta^(t*eps1-3*chi)+delta^(t-chi)≤
      delta^(min (t*eps1/2) (eps2/2)) := by
    nlinarith only [h704term,hdiagpos,hbudget]
  have hweighted := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoefle (sq_nonneg lam)) (sq_nonneg (Pts.card : ℝ))
  have hdeficit : (Pts.card : ℝ)^2-G.card≤
      delta^(min (t*eps1/2) (eps2/2))*(Pts.card : ℝ)^2 := by
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hlam)).mp
    nlinarith only [hcount',hweighted]
  refine ⟨G,hGP,?_,?_⟩
  · intro z hz
    obtain ⟨hne,hzgood⟩ := hgood z hz
    refine ⟨hne,?_⟩
    have hwidth : delta^(4*eps1)=theta^4 := by
      rw [mul_comm (4:ℝ) eps1,Real.rpow_mul hd.le,Real.rpow_ofNat]
    rw [hwidth]
    have hcard : (physicalPairTube Pts (C*theta^4) z).card≤
        (pairSupport Pts (2*C*theta^4) z).card := by
      simpa only [mul_assoc] using physical_pair_tube_card Pts (C*theta^4) z hne
    exact (Nat.cast_le.mpr hcard).trans_lt hzgood
  · nlinarith only [hdeficit]

/-- The fixed C0 dilation requested in the native A.1 application (214),
with the original Appendix A.2 quantifier order: t,eps1,eps2 determine a
single positive delta threshold depending on C; EVERY smaller positive chi works below it.
No ball-cap, representative-family, incidence, or output-graph certificate
is supplied as an assumption. -/
theorem exists_uniform_dilated_native_weak_radial_graph_threshold
    (t eps1 eps2 C : ℝ) (ht : 0<t) (ht2 : t≤2)
    (he1 : 0<eps1) (he1small : eps1<1/8) (he2 : 0<eps2) (hC : 1≤C) :
    ∃ d : ℝ, 0<d ∧ ∀ delta chi : ℝ, 0<delta → delta≤d →
      0<chi → chi≤t*eps1/12 → ∀ Pts : Finset Point, Pts.Nonempty →
      (∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1) →
      (∀ p∈Pts, ∀ r : ℝ, delta≤r → r≤1 →
        ((Pts.filter (fun q => euclideanDistance p q≤r)).card : ℝ)≤
          delta^(-chi)*r^t*Pts.card) →
      (∀ nx ny c h : ℝ, nx^2+ny^2=1 →
        ((unitTube Pts nx ny c h (delta^eps1)).card : ℝ)≤delta^eps2*Pts.card) →
      ∃ G : Finset Pair, G⊆Pts.product Pts ∧
        (∀ z∈G, z.1≠z.2 ∧
          ((physicalPairTube Pts (C*delta^(4*eps1)) z).card : ℝ)<delta^chi*Pts.card) ∧
        (1-delta^(min (t*eps1/2) (eps2/2)))*(Pts.card : ℝ)^2≤G.card := by
  obtain ⟨d,hd,hdhalf,hsmall⟩ := exists_dilated_native_threshold t eps1 eps2 C ht he1 he2 hC
  refine ⟨d,hd,?_⟩
  intro delta chi hdelta hdd hchi hchismall Pts hPts hbox hfrostman htwoends
  obtain ⟨hscale,hoverlap,htransverse,hends,hdiag⟩ := hsmall delta hdelta hdd
  exact dilated_native_weak_radial_graph Pts delta t eps1 eps2 chi C hPts hdelta (hdd.trans hdhalf)
    ht ht2 he1 he1small he2 hC hchi hchismall hscale hoverlap htransverse hends hdiag
    hbox hfrostman htwoends

end NativeA2DilatedCaller
