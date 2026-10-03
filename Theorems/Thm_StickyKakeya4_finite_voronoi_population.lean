import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option warningAsError true

namespace FiniteVoronoiPopulation

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

local instance : DecidableEq X := Classical.decEq X

/-- Separation is imposed only on distinct members. -/
def Separated (C : Finset X) (R : ℝ) : Prop :=
  ∀ c ∈ C, ∀ d ∈ C, c ≠ d → R ≤ dist c d

/-- A maximal separated subfamily is a strict-radius net. Both the centers
and the covering property are constructed from the original finite carrier. -/
theorem exists_separated_net (P : Finset X) {R : ℝ} (hR : 0 < R) :
    ∃ C : Finset X, C ⊆ P ∧ Separated C R ∧
      ∀ p ∈ P, ∃ c ∈ C, dist p c < R := by
  classical
  let families : Finset (Finset X) := P.powerset.filter (fun C => Separated C R)
  have hempty : (∅ : Finset X) ∈ families := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.empty_subset P), ?_⟩
    intro c hc
    exact (Finset.notMem_empty c hc).elim
  obtain ⟨C, hC, hmax⟩ :=
    Finset.exists_max_image families (fun C => C.card) ⟨∅, hempty⟩
  have hdata := Finset.mem_filter.mp hC
  have hCP : C ⊆ P := Finset.mem_powerset.mp hdata.1
  have hsep : Separated C R := hdata.2
  refine ⟨C, hCP, hsep, ?_⟩
  intro p hp
  by_contra hnot
  have hfar : ∀ c ∈ C, R ≤ dist p c := by
    intro c hc
    exact le_of_not_gt (fun h => hnot ⟨c, hc, h⟩)
  have hpnot : p ∉ C := by
    intro hpC
    have hzero := hfar p hpC
    simp only [dist_self] at hzero
    exact (not_le_of_gt hR) hzero
  have hinsert : insert p C ∈ families := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hp hCP), ?_⟩
    intro x hx y hy hxy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact hfar y hy
    · rcases hy with rfl | hy
      · simpa only [dist_comm] using hfar x hx
      · exact hsep x hx y hy hxy
  have hmax' := hmax (insert p C) hinsert
  have hstrict : C.card < (insert p C).card := by simp [hpnot]
  exact (not_lt_of_ge hmax') hstrict

/-- An actual nearest center; ties may be resolved by classical choice. -/
def owner (C : Finset X) (hC : C.Nonempty) (p : X) : X :=
  Classical.choose (Finset.exists_min_image C (fun c => dist p c) hC)

theorem owner_mem (C : Finset X) (hC : C.Nonempty) (p : X) :
    owner C hC p ∈ C :=
  (Classical.choose_spec (Finset.exists_min_image C (fun c => dist p c) hC)).1

theorem owner_min (C : Finset X) (hC : C.Nonempty) (p c : X) (hc : c ∈ C) :
    dist p (owner C hC p) ≤ dist p c :=
  (Classical.choose_spec (Finset.exists_min_image C (fun c => dist p c) hC)).2 c hc

/-- The cluster is a genuine fiber of the selected nearest-center map. -/
def cluster (P C : Finset X) (hC : C.Nonempty) (c : X) : Finset X := by
  classical
  exact P.filter (fun p => owner C hC p = c)

/-- Actual carrier population in a closed metric ball. -/
def carrierBall (P : Finset X) (c : X) (r : ℝ) : Finset X := by
  classical
  exact P.filter (fun p => dist p c ≤ r)

@[simp] theorem mem_cluster (P C : Finset X) (hC : C.Nonempty) (p c : X) :
    p ∈ cluster P C hC c ↔ p ∈ P ∧ owner C hC p = c := by
  classical
  simp only [cluster, Finset.mem_filter]

@[simp] theorem mem_carrierBall (P : Finset X) (p c : X) (r : ℝ) :
    p ∈ carrierBall P c r ↔ p ∈ P ∧ dist p c ≤ r := by
  classical
  simp only [carrierBall, Finset.mem_filter]

theorem carrierBall_coe (P : Finset X) (c : X) (r : ℝ) :
    (↑(carrierBall P c r) : Set X) = (↑P : Set X) ∩ Metric.closedBall c r := by
  ext p
  simp only [Finset.mem_coe, mem_carrierBall, Set.mem_inter_iff, Metric.mem_closedBall]

/-- Distinct owners give disjoint clusters, irrespective of tie-breaking. -/
theorem clusters_disjoint (P C : Finset X) (hC : C.Nonempty)
    {c d : X} (hcd : c ≠ d) :
    Disjoint (cluster P C hC c) (cluster P C hC d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hpc hpd
  exact hcd (((mem_cluster P C hC p c).mp hpc).2.symm.trans
    ((mem_cluster P C hC p d).mp hpd).2)

/-- The selected clusters cover exactly the original carrier. -/
theorem clusters_biUnion (P C : Finset X) (hC : C.Nonempty) :
    C.biUnion (cluster P C hC) = P := by
  classical
  ext p
  simp only [Finset.mem_biUnion, mem_cluster]
  constructor
  · rintro ⟨c, _hc, hp, _heq⟩
    exact hp
  · intro hp
    exact ⟨owner C hC p, owner_mem C hC p, hp, rfl⟩

/-- Exact mass conservation for these actual nearest-center fibers. -/
theorem sum_cluster_card (P C : Finset X) (hC : C.Nonempty) :
    ∑ c ∈ C, (cluster P C hC c).card = P.card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise
    (s := P) (t := C) (f := owner C hC) (fun p _hp => owner_mem C hC p)).symm

theorem owner_dist_lt (P C : Finset X) (hC : C.Nonempty) {R : ℝ}
    (hcover : ∀ p ∈ P, ∃ c ∈ C, dist p c < R) {p : X} (hp : p ∈ P) :
    dist p (owner C hC p) < R := by
  obtain ⟨c, hc, hpc⟩ := hcover p hp
  exact (owner_min C hC p c hc).trans_lt hpc

/-- The one-third inner ball has a unique nearest center by separation.
The strict gap removes every boundary/tie issue from the lower population bound. -/
theorem carrierBall_third_subset_cluster (P C : Finset X) (hC : C.Nonempty)
    {R : ℝ} (hR : 0 < R) (hsep : Separated C R) {c : X} (hc : c ∈ C) :
    carrierBall P c (R / 3) ⊆ cluster P C hC c := by
  intro p hp
  rcases (mem_carrierBall P p c (R / 3)).mp hp with ⟨hpP, hdist⟩
  apply (mem_cluster P C hC p c).mpr
  refine ⟨hpP, ?_⟩
  by_contra hne
  have hsep' := hsep c hc (owner C hC p) (owner_mem C hC p) (Ne.symm hne)
  have hmin := owner_min C hC p c hc
  have htri := dist_triangle c p (owner C hC p)
  rw [dist_comm c p] at htri
  linarith

/-- The covering net controls the outer radius of every nearest-center fiber. -/
theorem cluster_subset_carrierBall (P C : Finset X) (hC : C.Nonempty) {R : ℝ}
    (hcover : ∀ p ∈ P, ∃ c ∈ C, dist p c < R) (c : X) :
    cluster P C hC c ⊆ carrierBall P c R := by
  intro p hp
  rcases (mem_cluster P C hC p c).mp hp with ⟨hpP, heq⟩
  have hnear := owner_dist_lt P C hC hcover hpP
  rw [heq] at hnear
  exact (mem_carrierBall P p c R).mpr ⟨hpP, hnear.le⟩

/-- Two-sided population bounds come directly from carrier-ball counts. -/
theorem cluster_card_sandwich (P C : Finset X) (hC : C.Nonempty)
    {R : ℝ} (hR : 0 < R) (hsep : Separated C R)
    (hcover : ∀ p ∈ P, ∃ c ∈ C, dist p c < R) {c : X} (hc : c ∈ C) :
    (carrierBall P c (R / 3)).card ≤ (cluster P C hC c).card ∧
      (cluster P C hC c).card ≤ (carrierBall P c R).card :=
  ⟨Finset.card_le_card (carrierBall_third_subset_cluster P C hC hR hsep hc),
    Finset.card_le_card (cluster_subset_carrierBall P C hC hcover c)⟩

/-- Each selected center belongs to its own cluster. This is the lower bound
available without evaluating a lower-AD hypothesis below its cutoff scale. -/
theorem center_mem_cluster (P C : Finset X) (hC : C.Nonempty) (hCP : C ⊆ P)
    {R : ℝ} (hR : 0 < R) (hsep : Separated C R) {c : X} (hc : c ∈ C) :
    c ∈ cluster P C hC c := by
  apply carrierBall_third_subset_cluster P C hC hR hsep hc
  apply (mem_carrierBall P c c (R / 3)).mpr
  exact ⟨hCP hc, by simpa only [dist_self] using (div_nonneg hR.le (by norm_num : (0 : ℝ) ≤ 3))⟩

/-- The full constructed Voronoi partition, including exact mass conservation
and the genuine closed-ball sandwich. No partition or coverage certificate is
assumed: the only inputs are a nonempty finite carrier and a positive radius. -/
theorem exists_voronoi_partition (P : Finset X) (hP : P.Nonempty)
    {R : ℝ} (hR : 0 < R) :
    ∃ (C : Finset X) (hC : C.Nonempty),
      C ⊆ P ∧ Separated C R ∧
      (∀ p ∈ P, ∃ c ∈ C, dist p c < R) ∧
      (∀ p ∈ P, dist p (owner C hC p) < R) ∧
      (∀ c ∈ C, ∀ d ∈ C, c ≠ d →
        Disjoint (cluster P C hC c) (cluster P C hC d)) ∧
      C.biUnion (cluster P C hC) = P ∧
      (∑ c ∈ C, (cluster P C hC c).card) = P.card ∧
      (∀ c ∈ C, carrierBall P c (R / 3) ⊆ cluster P C hC c ∧
        cluster P C hC c ⊆ carrierBall P c R) ∧
      (∀ c ∈ C, c ∈ cluster P C hC c) := by
  classical
  obtain ⟨C, hCP, hsep, hcover⟩ := exists_separated_net P hR
  have hC : C.Nonempty := by
    obtain ⟨p, hp⟩ := hP
    obtain ⟨c, hc, _hdist⟩ := hcover p hp
    exact ⟨c, hc⟩
  refine ⟨C, hC, hCP, hsep, hcover, ?_, ?_,
    clusters_biUnion P C hC, sum_cluster_card P C hC, ?_, ?_⟩
  · intro p hp
    exact owner_dist_lt P C hC hcover hp
  · intro c _hc d _hd hcd
    exact clusters_disjoint P C hC hcd
  · intro c hc
    exact ⟨carrierBall_third_subset_cluster P C hC hR hsep hc,
      cluster_subset_carrierBall P C hC hcover c⟩
  · intro c hc
    exact center_mem_cluster P C hC hCP hR hsep hc

/-- Any lower bound on these cluster populations controls the number of centers. -/
theorem card_centers_mul_le_of_cluster_lower (P C : Finset X) (hC : C.Nonempty)
    (L : ℕ) (hL : ∀ c ∈ C, L ≤ (cluster P C hC c).card) :
    C.card * L ≤ P.card := by
  calc
    C.card * L = ∑ _c ∈ C, L := by simp
    _ ≤ ∑ c ∈ C, (cluster P C hC c).card := Finset.sum_le_sum hL
    _ = P.card := sum_cluster_card P C hC

/-- Lower actual-ball populations imply packing for any separated center family;
this statement requires neither a net nor an assumed partition. -/
theorem card_centers_mul_le_of_ball_lower (P C : Finset X) (hC : C.Nonempty)
    {R : ℝ} (hR : 0 < R) (hsep : Separated C R) (L : ℕ)
    (hL : ∀ c ∈ C, L ≤ (carrierBall P c (R / 3)).card) :
    C.card * L ≤ P.card := by
  apply card_centers_mul_le_of_cluster_lower P C hC L
  intro c hc
  exact (hL c hc).trans
    (Finset.card_le_card (carrierBall_third_subset_cluster P C hC hR hsep hc))

/-- The sandwich as inclusions of subsets of the ambient metric space. -/
theorem cluster_set_sandwich (P C : Finset X) (hC : C.Nonempty)
    {R : ℝ} (hR : 0 < R) (hsep : Separated C R)
    (hcover : ∀ p ∈ P, ∃ c ∈ C, dist p c < R) {c : X} (hc : c ∈ C) :
    (↑P : Set X) ∩ Metric.closedBall c (R / 3) ⊆ (↑(cluster P C hC c) : Set X) ∧
      (↑(cluster P C hC c) : Set X) ⊆ (↑P : Set X) ∩ Metric.closedBall c R := by
  rw [← carrierBall_coe P c (R / 3), ← carrierBall_coe P c R]
  exact ⟨carrierBall_third_subset_cluster P C hC hR hsep hc,
    cluster_subset_carrierBall P C hC hcover c⟩

/-- Real-valued AD bounds on actual balls transfer to cluster populations. -/
theorem cluster_population_bounds (P C : Finset X) (hC : C.Nonempty)
    {R : ℝ} (hR : 0 < R) (hsep : Separated C R)
    (hcover : ∀ p ∈ P, ∃ c ∈ C, dist p c < R) {c : X} (hc : c ∈ C)
    {L U : ℝ} (hlower : L ≤ ((carrierBall P c (R / 3)).card : ℝ))
    (hupper : ((carrierBall P c R).card : ℝ) ≤ U) :
    L ≤ ((cluster P C hC c).card : ℝ) ∧ ((cluster P C hC c).card : ℝ) ≤ U := by
  have hsandwich := cluster_card_sandwich P C hC hR hsep hcover hc
  exact ⟨hlower.trans (Nat.cast_le.mpr hsandwich.1),
    (Nat.cast_le.mpr hsandwich.2).trans hupper⟩

/-- The singleton-center lower bound covers scales below the lower-AD cutoff. -/
theorem one_le_cluster_card (P C : Finset X) (hC : C.Nonempty) (hCP : C ⊆ P)
    {R : ℝ} (hR : 0 < R) (hsep : Separated C R) {c : X} (hc : c ∈ C) :
    1 ≤ (cluster P C hC c).card :=
  Finset.card_pos.mpr ⟨c, center_mem_cluster P C hC hCP hR hsep hc⟩

/-- Empty separated families are allowed in the packing consequence. -/
theorem card_separated_family_mul_le (P C : Finset X)
    {R : ℝ} (hR : 0 < R) (hsep : Separated C R) (L : ℕ)
    (hL : ∀ c ∈ C, L ≤ (carrierBall P c (R / 3)).card) :
    C.card * L ≤ P.card := by
  by_cases hC : C.Nonempty
  · exact card_centers_mul_le_of_ball_lower P C hC hR hsep L hL
  · have hzero : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [hzero, Finset.card_empty, zero_mul, Nat.zero_le]

/-- Real-valued form of exact mass conservation. -/
theorem sum_cluster_card_real (P C : Finset X) (hC : C.Nonempty) :
    ∑ c ∈ C, ((cluster P C hC c).card : ℝ) = (P.card : ℝ) := by
  rw [← Nat.cast_sum, sum_cluster_card P C hC]

/-- Real lower populations give real packing bounds without rounding losses. -/
theorem card_centers_mul_le_of_cluster_lower_real (P C : Finset X) (hC : C.Nonempty)
    (L : ℝ) (hL : ∀ c ∈ C, L ≤ ((cluster P C hC c).card : ℝ)) :
    (C.card : ℝ) * L ≤ (P.card : ℝ) := by
  calc
    (C.card : ℝ) * L = ∑ _c ∈ C, L := by simp
    _ ≤ ∑ c ∈ C, ((cluster P C hC c).card : ℝ) := Finset.sum_le_sum hL
    _ = (P.card : ℝ) := sum_cluster_card_real P C hC

/-- Packing from real AD lower bounds on actual carrier balls, for every
separated family, including the empty family. -/
theorem card_separated_family_mul_le_real (P C : Finset X)
    {R : ℝ} (hR : 0 < R) (hsep : Separated C R) (L : ℝ)
    (hL : ∀ c ∈ C, L ≤ ((carrierBall P c (R / 3)).card : ℝ)) :
    (C.card : ℝ) * L ≤ (P.card : ℝ) := by
  by_cases hC : C.Nonempty
  · apply card_centers_mul_le_of_cluster_lower_real P C hC L
    intro c hc
    exact (hL c hc).trans (Nat.cast_le.mpr
      (Finset.card_le_card (carrierBall_third_subset_cluster P C hC hR hsep hc)))
  · have hzero : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [hzero, Finset.card_empty, Nat.cast_zero, zero_mul, Nat.cast_nonneg]

end
end FiniteVoronoiPopulation
