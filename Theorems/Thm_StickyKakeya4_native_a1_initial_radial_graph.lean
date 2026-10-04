import Theorems.Thm_StickyKakeya4_native_a2_dilated_caller

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

noncomputable section
namespace NativeA1InitialRadialGraph
open OriginalPairStripGeometry FourUnitTubeBandCover PlanarFrostmanBallConversion
open OriginalPhysicalPairTube

/-- The actual initial A.1 graph at (213)-(214): the fixed C0 dilation is
controlled using the ORIGINAL eta-Frostman profile. Its weakening from eta
to chi is proved, and the delta threshold is independent of both exponents
once eta<=chi<=t*eps1/12. -/
theorem exists_original_eta_dilated_radial_threshold
    (t eps1 eps2 C : ℝ) (ht : 0<t) (ht2 : t≤2)
    (he1 : 0<eps1) (he1small : eps1<1/8) (he2 : 0<eps2) (hC : 1≤C) :
    ∃ d : ℝ, 0<d ∧ ∀ delta chi eta : ℝ, 0<delta → delta≤d →
      eta≤chi → 0<chi → chi≤t*eps1/12 → ∀ Pts : Finset Point, Pts.Nonempty →
      (∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1) →
      (∀ p∈Pts, ∀ r : ℝ, delta≤r → r≤1 →
        ((Pts.filter (fun q => euclideanDistance p q≤r)).card : ℝ)≤
          delta^(-eta)*r^t*Pts.card) →
      (∀ nx ny c h : ℝ, nx^2+ny^2=1 →
        ((unitTube Pts nx ny c h (delta^eps1)).card : ℝ)≤delta^eps2*Pts.card) →
      ∃ G : Finset Pair, G⊆Pts.product Pts ∧
        (∀ z∈G, z.1≠z.2 ∧
          ((physicalPairTube Pts (C*delta^(4*eps1)) z).card : ℝ)<delta^chi*Pts.card) ∧
        (1-delta^(min (t*eps1/2) (eps2/2)))*(Pts.card : ℝ)^2≤G.card := by
  obtain ⟨d,hd,hcaller⟩ :=
    NativeA2DilatedCaller.exists_uniform_dilated_native_weak_radial_graph_threshold
      t eps1 eps2 C ht ht2 he1 he1small he2 hC
  refine ⟨min d 1,lt_min hd zero_lt_one,?_⟩
  intro delta chi eta hdelta hdd hetachi hchi hchismall Pts hPts hbox hfrostman htwoends
  have hd1 : delta≤1 := hdd.trans (min_le_right _ _)
  have hcoef : delta^(-eta)≤delta^(-chi) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta hd1 (by linarith only [hetachi])
  apply hcaller delta chi hdelta (hdd.trans (min_le_left _ _)) hchi hchismall
    Pts hPts hbox ?_ htwoends
  intro p hp r hrlow hrhigh
  have hr : 0≤r := hdelta.le.trans hrlow
  exact (hfrostman p hp r hrlow hrhigh).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hr t))
      (Nat.cast_nonneg Pts.card))

end NativeA1InitialRadialGraph
