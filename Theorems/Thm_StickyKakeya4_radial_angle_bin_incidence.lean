import Theorems.Thm_StickyKakeya4_radial_angle_periodic_cover
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

noncomputable section
namespace RadialAngleBinIncidence
open Classical RadialAnglePeriodicCover NativeTangentGridCoarsening
open scoped BigOperators

/-- Count ORIGINAL angle-bin representatives by the literal five-interval
sine sublevel cover. No bounded angular overlap is assumed. -/
theorem separated_bins_small_sine_card {X : Type*} (I : Finset X) (angle : X → ℝ)
    {rho e phi : ℝ} (hrho : 0<rho) (he : 0≤e) (hphi : |phi|≤Real.pi)
    (hangle : ∀ i∈I, |angle i|≤Real.pi)
    (hinj : Set.InjOn (fun i => ⌊angle i/rho⌋) (↑I))
    (hsine : ∀ i∈I, |Real.sin (angle i-phi)|≤e) :
    (I.card : ℝ) ≤ 5*(Real.pi*e/rho+2) := by
  let Ks := Finset.Icc (-2:ℤ) 2
  let F := fun k : ℤ => I.filter (fun i => |angle i-phi-(k:ℝ)*Real.pi|≤Real.pi/2*e)
  have hK : Ks.card=5 := by norm_num [Ks]; rfl
  have hcover : I.image (fun i => ⌊angle i/rho⌋) ⊆
      Ks.biUnion (fun k => scalarCells (F k) angle rho) := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    have hd : |angle i-phi|≤2*Real.pi :=
      (abs_sub (angle i) phi).trans (by linarith only [hangle i hi,hphi])
    obtain ⟨k,hk,hbound⟩ := small_sine_five_intervals hd (hsine i hi)
    exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr
      ⟨i,Finset.mem_filter.mpr ⟨hi,hbound⟩,rfl⟩⟩
  have hf : ∀ k∈Ks, ((scalarCells (F k) angle rho).card : ℝ) ≤Real.pi*e/rho+2 := by
    intro k _hk
    apply scalar_interval_grid_card (F k) angle hrho (mul_nonneg Real.pi_pos.le he)
      (c:=phi+(k:ℝ)*Real.pi-Real.pi/2*e)
    intro i hi
    have hb := abs_le.mp (Finset.mem_filter.mp hi).2
    constructor <;> linarith only [hb.1,hb.2]
  calc
    (I.card : ℝ) = (I.image (fun i => ⌊angle i/rho⌋)).card := by
      rw [Finset.card_image_iff.mpr hinj]
    _ ≤ (Ks.biUnion (fun k => scalarCells (F k) angle rho)).card :=
      Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ k∈Ks, ((scalarCells (F k) angle rho).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le :
        (Ks.biUnion (fun k => scalarCells (F k) angle rho)).card ≤
          ∑ k∈Ks, (scalarCells (F k) angle rho).card)
    _ ≤ ∑ _k∈Ks, (Real.pi*e/rho+2) := Finset.sum_le_sum hf
    _ = 5*(Real.pi*e/rho+2) := by simp [hK]; ring

/-- At distance at least tau, one original point can meet at most50/tau
actual rho-angle-bin representatives of rho-tubes through one fixed root. -/
theorem native_small_sine_bin_card {X : Type*} (I : Finset X) (angle : X → ℝ)
    {rho tau phi : ℝ} (hrho : 0<rho) (htau : 0<tau) (htau1 : tau≤1)
    (hphi : |phi|≤Real.pi) (hangle : ∀ i∈I, |angle i|≤Real.pi)
    (hinj : Set.InjOn (fun i => ⌊angle i/rho⌋) (↑I))
    (hsine : ∀ i∈I, |Real.sin (angle i-phi)|≤2*rho/tau) :
    (I.card : ℝ) ≤50/tau := by
  have h := separated_bins_small_sine_card I angle hrho (by positivity) hphi hangle hinj hsine
  have heq : 5*(Real.pi*(2*rho/tau)/rho+2)=(10*Real.pi+10*tau)/tau := by
    field_simp
    ring
  rw [heq] at h
  apply h.trans
  exact div_le_div_of_nonneg_right (by linarith [Real.pi_lt_four]) htau.le

end RadialAngleBinIncidence
