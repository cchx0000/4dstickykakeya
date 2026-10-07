/- NEW UNVERIFIED DRAFT, 2026-10-06.
   Sharp coarse lower counts from literal source AD and displacement.
   No coarse population or ambient-dimensional fiber bound is assumed. -/
import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening
import Theorems.Thm_StickyKakeya4_fine_point_slab_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeDisplacedADLower
open Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

/-- Exact cancellation of the fine mesh. The exponent remains s. -/
lemma power_ratio_identity {mu rho alpha r s : ℝ}
    (hmu : 0 < mu) (hrho : 0 < rho) (halpha : 0 < alpha) (hr : 0 < r) :
    ((r/2)/mu)^s / (2*alpha*rho/mu)^s = (r/rho)^s/(4*alpha)^s := by
  rw [←Real.div_rpow (by positivity : 0 ≤ (r/2)/mu)
    (by positivity : 0 ≤ 2*alpha*rho/mu)]
  have heq : ((r/2)/mu)/(2*alpha*rho/mu) = (r/rho)/(4*alpha) := by
    field_simp [ne_of_gt hmu, ne_of_gt hrho, ne_of_gt halpha] <;> ring
  rw [heq, Real.div_rpow (div_nonneg hr.le hrho.le) (by positivity : 0 ≤ 4*alpha)]

variable {X : Type*} [PseudoMetricSpace X]
local instance : DecidableEq X := Classical.decEq X

/-- Every fiber is contained in a source ball about an actual fine point
of that fiber. The source AD upper bound supplies its real cardinal cap. -/
theorem fiber_card_upper (A S : Finset X) (f : X → X)
    {mu rho alpha K s : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho)
    (halpha : 1 ≤ alpha) (hK : 0 < K) (hscale : 2*alpha*rho ≤ 1)
    (hAD : ADBounds A mu K s) (hSA : S ⊆ A)
    (hdisplace : ∀a∈A, dist (f a) a ≤ alpha*rho) (y : X) :
    ((S.filter (fun a => f a=y)).card:ℝ) ≤ K*(2*alpha*rho/mu)^s := by
  classical
  have hrho : 0 < rho := hmu.trans_le hmurho
  have halpha0 : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  have hbase : rho ≤ alpha*rho := le_mul_of_one_le_left hrho.le halpha
  have htest : mu ≤ 2*alpha*rho := by nlinarith only [hmurho, hbase, hrho]
  by_cases hnonempty : (S.filter (fun a => f a=y)).Nonempty
  · obtain ⟨a0, ha0⟩ := hnonempty
    obtain ⟨ha0S, hfa0⟩ := Finset.mem_filter.mp ha0
    have ha0A := hSA ha0S
    have hya0 : dist y a0 ≤ alpha*rho := by
      simpa only [hfa0] using hdisplace a0 ha0A
    have hsub : S.filter (fun a => f a=y) ⊆ carrierBall A a0 (2*alpha*rho) := by
      intro a ha
      obtain ⟨haS, hfa⟩ := Finset.mem_filter.mp ha
      have haA := hSA haS
      have hay : dist a y ≤ alpha*rho := by
        rw [←hfa, dist_comm]
        exact hdisplace a haA
      apply (mem_carrierBall A a a0 (2*alpha*rho)).mpr
      refine ⟨haA, ?_⟩
      have ht := dist_triangle a y a0
      linarith only [ht, hay, hya0]
    have hcard : ((S.filter (fun a => f a=y)).card:ℝ) ≤
        (carrierBall A a0 (2*alpha*rho)).card :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    exact hcard.trans (hAD a0 ha0A (2*alpha*rho) htest hscale).2
  · have hempty : S.filter (fun a => f a=y) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- An arbitrary displaced image inherits the sharp source-dimensional
lower count. B may contain additional points and need not be separated.
The only source hypotheses are its actual AD bounds and the actual map.

For r>=4*alpha*rho, the fine r/2-ball maps into the target r-ball and each
fiber is paid by source AD at2*alpha*rho. Both fine tests are within[mu,1].
For smaller r, the literal point f(a0) already supplies the bound. -/
theorem displaced_ball_lower (A B : Finset X) (f : X → X)
    {mu rho alpha K s : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho)
    (halpha : 1 ≤ alpha) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ADBounds A mu K s)
    (hdisplace : ∀a∈A, dist (f a) a ≤ alpha*rho)
    (hmaps : ∀a∈A, f a∈B) (a0 : X) (ha0 : a0∈A)
    (r : ℝ) (hrhor : rho ≤ r) (hr1 : r ≤ 1) :
    (r/rho)^s/(K^2*(4*alpha)^s) ≤ ((carrierBall B (f a0) r).card:ℝ) := by
  classical
  have hrho : 0 < rho := hmu.trans_le hmurho
  have hr : 0 < r := hrho.trans_le hrhor
  have halpha0 : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hbase : rho ≤ alpha*rho := le_mul_of_one_le_left hrho.le halpha
  have hpower : 0 < (4*alpha)^s := Real.rpow_pos_of_pos (by positivity) _
  have hden : 0 < K^2*(4*alpha)^s := mul_pos (sq_pos_of_pos hK0) hpower
  by_cases hlarge : 4*alpha*rho ≤ r
  · have hhalf : mu ≤ r/2 := by nlinarith only [hmurho, hbase, hlarge, hrho]
    have hhalf1 : r/2 ≤ 1 := by linarith only [hr1]
    have hfibscale : 2*alpha*rho ≤ 1 := by nlinarith only [hlarge, hr1, hbase, hrho]
    let S := carrierBall A a0 (r/2)
    let Q := carrierBall B (f a0) r
    have hSA : S ⊆ A := by
      intro a ha
      exact ((mem_carrierBall A a a0 (r/2)).mp ha).1
    have hmapQ : ∀a∈S, f a∈Q := by
      intro a ha
      have haA := hSA ha
      have haa0 := ((mem_carrierBall A a a0 (r/2)).mp ha).2
      have hfa := hdisplace a haA
      have ha0f : dist a0 (f a0) ≤ alpha*rho := by
        simpa only [dist_comm] using hdisplace a0 ha0
      apply (mem_carrierBall B (f a) (f a0) r).mpr
      refine ⟨hmaps a haA, ?_⟩
      have ht1 := dist_triangle (f a) a (f a0)
      have ht2 := dist_triangle a a0 (f a0)
      linarith only [ht1, ht2, hfa, haa0, ha0f, hlarge]
    have hcard : (S.card:ℝ) ≤ (Q.card:ℝ)*(K*(2*alpha*rho/mu)^s) :=
      FinePointSlabGeometry.card_le_real_mul_of_fibers S Q f (K*(2*alpha*rho/mu)^s)
        hmapQ (fun y _hy => fiber_card_upper A S f hmu hmurho halpha hK0 hfibscale hAD hSA hdisplace y)
    have hfine := (hAD a0 ha0 (r/2) hhalf hhalf1).1
    have hmass := (div_le_iff₀ hK0).mp (hfine.trans hcard)
    have hcap : 0 < (2*alpha*rho/mu)^s := Real.rpow_pos_of_pos (by positivity) _
    have hdiv : ((r/2)/mu)^s/(2*alpha*rho/mu)^s ≤ K^2*(Q.card:ℝ) := by
      apply (div_le_iff₀ hcap).mpr
      nlinarith only [hmass]
    rw [power_ratio_identity hmu hrho halpha0 hr] at hdiv
    have hcancel := (div_le_iff₀ hpower).mp hdiv
    change (r/rho)^s/(K^2*(4*alpha)^s) ≤ (Q.card:ℝ)
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hcancel]
  · have hrsmall : r ≤ 4*alpha*rho := le_of_lt (lt_of_not_ge hlarge)
    have hratio : r/rho ≤ 4*alpha := (div_le_iff₀ hrho).mpr hrsmall
    have hp := Real.rpow_le_rpow (div_nonneg hr.le hrho.le) hratio hs
    have hKsq : (1:ℝ) ≤ K^2 := one_le_pow₀ hK
    have hleone : (r/rho)^s/(K^2*(4*alpha)^s) ≤ 1 := by
      apply (div_le_iff₀ hden).mpr
      simpa only [one_mul] using hp.trans (le_mul_of_one_le_left hpower.le hKsq)
    have hpoint : f a0∈carrierBall B (f a0) r :=
      (mem_carrierBall B (f a0) (f a0) r).mpr
        ⟨hmaps a0 ha0, by simpa only [dist_self] using hr.le⟩
    have hcardone : (1:ℝ) ≤ (carrierBall B (f a0) r).card :=
      Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨f a0, hpoint⟩)
    exact hleone.trans hcardone

/-- Literal image specialization; no coarse count certificate is needed. -/
theorem image_ball_lower (A : Finset X) (f : X → X)
    {mu rho alpha K s : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho)
    (halpha : 1 ≤ alpha) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ADBounds A mu K s) (hdisplace : ∀a∈A, dist (f a) a ≤ alpha*rho)
    (a0 : X) (ha0 : a0∈A) (r : ℝ) (hrhor : rho ≤ r) (hr1 : r ≤ 1) :
    (r/rho)^s/(K^2*(4*alpha)^s) ≤ ((carrierBall (A.image f) (f a0) r).card:ℝ) := by
  classical
  exact displaced_ball_lower A (A.image f) f hmu hmurho halpha hK hs hAD hdisplace
    (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩) a0 ha0 r hrhor hr1

end NativeDisplacedADLower
