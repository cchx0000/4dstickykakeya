import Theorems.Thm_StickyKakeya4_native_recoded_grid_upper
import Theorems.Thm_StickyKakeya4_native_displaced_ad_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeRecodedGridAD
open Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open NativeLiteralGridOverlap NativeRecodedGridUpper NativeDisplacedADLower
attribute [local instance] Classical.propDecidable

/-- A genuine backward witness suffices for a coarse center. Override the
forward map only at that witness; its displacement and target remain valid. -/
theorem near_center_ball_lower {X : Type*} [PseudoMetricSpace X]
    (A B : Finset X) (f : X → X) {mu rho alpha K s : ℝ}
    (hmu : 0 < mu) (hmurho : mu ≤ rho) (halpha : 1 ≤ alpha) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ADBounds A mu K s) (hdisplace : ∀a∈A, dist (f a) a ≤ alpha*rho)
    (hmaps : ∀a∈A, f a∈B) (a0 b0 : X) (ha0 : a0∈A) (hb0 : b0∈B)
    (hnear : dist b0 a0 ≤ alpha*rho) (r : ℝ) (hrhor : rho ≤ r) (hr1 : r ≤ 1) :
    (r/rho)^s/(K^2*(4*alpha)^s) ≤ ((carrierBall B b0 r).card:ℝ) := by
  classical
  let g : X → X := fun a => if a=a0 then b0 else f a
  have hgmap : ∀a∈A, g a∈B := by
    intro a ha
    by_cases he : a=a0
    · simpa only [g,if_pos he] using hb0
    · simpa only [g,if_neg he] using hmaps a ha
  have hgdist : ∀a∈A, dist (g a) a ≤ alpha*rho := by
    intro a ha
    by_cases he : a=a0
    · subst a
      simpa [g] using hnear
    · simpa only [g,if_neg he] using hdisplace a ha
  have hga : g a0=b0 := by simp [g]
  have hh := displaced_ball_lower A B g hmu hmurho halpha hK hs hAD hgdist hgmap a0 ha0 r hrhor hr1
  simpa only [hga] using hh

/-- Actual two-way recoding onto literal rho-grid centers. Source AD and
its separately proved global count produce both coarse bounds. No AD
or local population assertion for the recoded set is an input. -/
theorem two_way_grid_ADBounds {l : ℕ}
    (A : Finset (Fin l → ℝ)) (B : Finset (Fin l → ℤ))
    (f : (Fin l → ℝ) → (Fin l → ℝ))
    {mu rho alpha K s : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho)
    (halpha : 1 ≤ alpha) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ADBounds A mu K s) (hglobal : (A.card:ℝ) ≤ K*mu^(-s))
    (hdisplace : ∀a∈A, dist (f a) a ≤ alpha*rho)
    (hmaps : ∀a∈A, f a∈B.image (center rho))
    (hnear : ∀k∈B, ∃a∈A, dist (center rho k) a ≤ alpha*rho) :
    ADBounds (B.image (center rho)) rho
      ((((4*⌈alpha⌉₊+5)^l:ℕ):ℝ)*K^2*(4*((⌈alpha⌉₊:ℝ)+2))^s) s := by
  classical
  let N := ⌈alpha⌉₊
  let M : ℝ := (((4*N+5)^l:ℕ):ℝ)
  have hMone : (1:ℝ) ≤ M := by
    have hp : 0 < (4*N+5)^l := by positivity
    have hn : 1 ≤ (4*N+5)^l := hp
    dsimp only [M]
    exact_mod_cast hn
  have hM : 0 ≤ M := (by norm_num : (0:ℝ) ≤ 1).trans hMone
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have halpha0 : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  have haN : alpha ≤ (N:ℝ) := Nat.le_ceil alpha
  have hbase : 4*alpha ≤ 4*((N:ℝ)+2) := by linarith only [haN]
  have hlowerC : K^2*(4*alpha)^s ≤ M*K^2*(4*((N:ℝ)+2))^s := by
    calc
      _ ≤ K^2*(4*((N:ℝ)+2))^s := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hbase hs) (sq_nonneg K)
      _ ≤ M*(K^2*(4*((N:ℝ)+2))^s) := le_mul_of_one_le_left (by positivity) hMone
      _ = _ := by ring
  have hupperC : M*K^2*(2*((N:ℝ)+2))^s ≤ M*K^2*(4*((N:ℝ)+2))^s := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM (sq_nonneg K))
    apply Real.rpow_le_rpow (by positivity) _ hs
    have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
    linarith only [hN]
  intro b hb r hrhor hr1
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨a0,ha0,hka0⟩ := hnear k hk
  have hrho : 0 < rho := hmu.trans_le hmurho
  have hr : 0 < r := hrho.trans_le hrhor
  constructor
  · have hlo := near_center_ball_lower A (B.image (center rho)) f hmu hmurho halpha hK hs
      hAD hdisplace hmaps a0 (center rho k) ha0 (Finset.mem_image.mpr ⟨k,hk,rfl⟩) hka0 r hrhor hr1
    exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (div_nonneg hr.le hrho.le) _)
      (by positivity : 0 < K^2*(4*alpha)^s) hlowerC).trans hlo
  · have hup := actual_grid_ball_upper A B hmu hmurho hK hs hAD hglobal hnear
      (center rho k) r hrhor hr1
    exact hup.trans (mul_le_mul_of_nonneg_right hupperC
      (Real.rpow_nonneg (div_nonneg hr.le hrho.le) _))

/-- The forward map is constructed from literal two-way support witnesses
when the source provides a cover relation instead of a chosen map. -/
theorem two_way_grid_cover_ADBounds {l : ℕ}
    (A : Finset (Fin l → ℝ)) (B : Finset (Fin l → ℤ))
    {mu rho alpha K s : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho)
    (halpha : 1 ≤ alpha) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ADBounds A mu K s) (hglobal : (A.card:ℝ) ≤ K*mu^(-s))
    (hforward : ∀a∈A, ∃k∈B, dist (center rho k) a ≤ alpha*rho)
    (hbackward : ∀k∈B, ∃a∈A, dist (center rho k) a ≤ alpha*rho) :
    ADBounds (B.image (center rho)) rho
      ((((4*⌈alpha⌉₊+5)^l:ℕ):ℝ)*K^2*(4*((⌈alpha⌉₊:ℝ)+2))^s) s := by
  classical
  let f : (Fin l → ℝ) → (Fin l → ℝ) :=
    fun a => if ha : a∈A then center rho (Classical.choose (hforward a ha)) else a
  have hmaps : ∀a∈A, f a∈B.image (center rho) := by
    intro a ha
    dsimp [f]
    rw [dif_pos ha]
    exact Finset.mem_image.mpr
      ⟨Classical.choose (hforward a ha),(Classical.choose_spec (hforward a ha)).1,rfl⟩
  have hdisplace : ∀a∈A, dist (f a) a ≤ alpha*rho := by
    intro a ha
    dsimp [f]
    rw [dif_pos ha]
    exact (Classical.choose_spec (hforward a ha)).2
  exact two_way_grid_ADBounds A B f hmu hmurho halpha hK hs hAD hglobal hdisplace hmaps hbackward

end NativeRecodedGridAD
