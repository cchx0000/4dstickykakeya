import Theorems.Thm_StickyKakeya4_original_tensor_projection_pairs
import Theorems.Thm_StickyKakeya4_original_tensor_quadratic_caps
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalHighDimensionalProjectionEnergy
open OriginalTensorProjectionPairs OriginalTensorQuadraticCaps

/-- Native quadratic spatial caps bound the COMPLETE parameter collision
count for one original point. The dyadic annuli form a geometric sum. -/
theorem original_point_projection_energy {n : ℕ}
    (P : Finset (Fin (n+1) → ℝ)) (M k : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hmesh : FinitePlaneProjectionGrid.mesh M ≤ ProjectionAnnulusEnergy.mesh k)
    (htop : ∀ x∈P, ∀ y∈P, ∀ i, |y i-x i| ≤ 2)
    (hcap : ∀ x∈P, ∀ r : ℝ, ProjectionAnnulusEnergy.mesh k ≤ r →
      ((P.filter (close r x)).card:ℝ) ≤ K*r^2*P.card)
    (x : Fin (n+1) → ℝ) (hx : x∈P) :
    (∑ y∈P, ((pairParameters n M x y (ProjectionAnnulusEnergy.mesh k)).card:ℝ)) ≤
      128*K*ProjectionAnnulusEnergy.mesh k*P.card*(parameters n M).card := by
  let delta := ProjectionAnnulusEnergy.mesh k
  let F := fun y => ((pairParameters n M x y delta).card:ℝ)
  let G : ℝ := (parameters n M).card
  have hd : 0 < delta := ProjectionAnnulusEnergy.mesh_pos k
  have hd1 : delta ≤ 1 := by
    dsimp [delta,ProjectionAnnulusEnergy.mesh]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hG : 0 ≤ G := Nat.cast_nonneg _
  have hnear : (∑ y∈P.filter (close delta x), F y) ≤ K*delta*P.card*G := by
    have hs : (∑ y∈P.filter (close delta x), F y) ≤
        ((P.filter (close delta x)).card:ℝ)*G := by
      calc
        _ ≤ ∑ _y∈P.filter (close delta x), G := Finset.sum_le_sum (fun _y _hy =>
          Nat.cast_le.mpr (Finset.card_filter_le _ _))
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
    have hc := mul_le_mul_of_nonneg_right (hcap x hx delta le_rfl) hG
    have hdd : delta^2 ≤ delta := by nlinarith only [hd,hd1]
    have hm := mul_le_mul_of_nonneg_left hdd
      (show 0 ≤ K*(P.card:ℝ)*G by positivity)
    nlinarith only [hs,hc,hm]
  have hshell : ∀ j∈Finset.range (k+1),
      (∑ y∈P.filter (annulus j delta x), F y) ≤
        32*K*delta*dyadicScale k j*P.card*G := by
    intro j hj
    have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    let r := dyadicScale k j
    have hr : delta ≤ r := (dyadicScale_bounds k j hjk).1
    have hrpos : 0 < r := hd.trans_le hr
    have hradius : 2^(j+1)*delta=2*r := by
      dsimp [r,dyadicScale,delta]
      rw [pow_succ]
      ring
    have hsub : P.filter (annulus j delta x) ⊆ P.filter (close (2*r) x) := by
      intro y hy
      obtain ⟨hyP,hann⟩ := Finset.mem_filter.mp hy
      have hh := hann.1
      rw [hradius] at hh
      exact Finset.mem_filter.mpr ⟨hyP,hh⟩
    have hcard : ((P.filter (annulus j delta x)).card:ℝ) ≤ K*(2*r)^2*P.card :=
      (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (hcap x hx (2*r) (by linarith only [hr,hrpos]))
    have hparam : ∀ y∈P.filter (annulus j delta x), F y ≤ (8*delta/r)*G := by
      intro y hy
      obtain ⟨hyP,hann⟩ := Finset.mem_filter.mp hy
      obtain ⟨i,hfar⟩ := hann.2
      change r < |y i-x i| at hfar
      exact original_pair_scale_count n M x y i hd.le hrpos hfar.le
        (htop x hx y hyP i) hmesh
    have hs : (∑ y∈P.filter (annulus j delta x), F y) ≤
        ((P.filter (annulus j delta x)).card:ℝ)*((8*delta/r)*G) := by
      calc
        _ ≤ ∑ _y∈P.filter (annulus j delta x), (8*delta/r)*G := Finset.sum_le_sum hparam
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
    have hm := mul_le_mul_of_nonneg_right hcard (show 0 ≤ (8*delta/r)*G by positivity)
    have he : (K*(2*r)^2*(P.card:ℝ))*((8*delta/r)*G)=32*K*delta*r*P.card*G := by
      calc
        _ = (32*K*delta*r*P.card*G)*(r/r) := by ring
        _ = _ := by rw [div_self (ne_of_gt hrpos),mul_one]
    rw [he] at hm
    exact hs.trans hm
  have hsum : (∑ j∈Finset.range (k+1), ∑ y∈P.filter (annulus j delta x), F y) ≤
      64*K*delta*P.card*G := by
    have hs := Finset.sum_le_sum hshell
    have he : (∑ j∈Finset.range (k+1), 32*K*delta*dyadicScale k j*P.card*G)=
        (32*K*delta*P.card*G)*(∑ j∈Finset.range (k+1), dyadicScale k j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    rw [he] at hs
    have hm := mul_le_mul_of_nonneg_left (dyadicScale_sum k)
      (show 0 ≤ 32*K*delta*P.card*G by positivity)
    nlinarith only [hs,hm]
  have htopscale : (2:ℝ)^(k+1)*delta=2 := by
    have hh : (2:ℝ)^k*delta=1 := FinitePlaneProjectionGrid.two_pow_reciprocal k
    rw [pow_succ]
    nlinarith only [hh]
  have hcover : ∀ y∈P, close delta x y ∨ ∃ j∈Finset.range (k+1), annulus j delta x y := by
    intro y hy
    by_cases hnear : close delta x y
    · exact Or.inl hnear
    · right
      apply original_exists_annulus k x y hnear
      rw [htopscale]
      exact htop x hx y hy
  have hh := FinitePlaneProjectionGrid.sum_le_near_add_shells P (Finset.range (k+1)) F
    (close delta x) (fun j => annulus j delta x) (fun _y _hy => Nat.cast_nonneg _) hcover
  change (∑ y∈P, F y) ≤ 128*K*delta*P.card*G
  have hnon : 0 ≤ K*delta*P.card*G := by positivity
  nlinarith only [hh,hnear,hsum,hnon]

/-- Original quadratic spatial caps yield the full finite parameter-energy
bound, with every original tuple pair counted before any image collapse. -/
theorem original_quadratic_projection_energy {n : ℕ}
    (P : Finset (Fin (n+1) → ℝ)) (M k : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hmesh : FinitePlaneProjectionGrid.mesh M ≤ ProjectionAnnulusEnergy.mesh k)
    (htop : ∀ x∈P, ∀ y∈P, ∀ i, |y i-x i| ≤ 2)
    (hcap : ∀ x∈P, ∀ r : ℝ, ProjectionAnnulusEnergy.mesh k ≤ r →
      ((P.filter (close r x)).card:ℝ) ≤ K*r^2*P.card) :
    (∑ v∈parameters n M,
      ((labelCollisions P v (ProjectionAnnulusEnergy.mesh k)).card:ℝ)) ≤
      128*K*ProjectionAnnulusEnergy.mesh k*(P.card:ℝ)^2*(parameters n M).card := by
  rw [original_collision_fubini]
  have hs := Finset.sum_le_sum (fun x hx =>
    original_point_projection_energy P M k hK hmesh htop hcap x hx)
  simpa only [Finset.sum_const,nsmul_eq_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hs

end OriginalHighDimensionalProjectionEnergy
