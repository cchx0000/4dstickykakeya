import Theorems.Thm_StickyKakeya4_native_graph_tube_cell_visits
import Theorems.Thm_StickyKakeya4_native_graph_point_cuts
import Theorems.Thm_StickyKakeya4_original_weighted_macro_selection
import Theorems.Thm_StickyKakeya4_original_scalar_collision_mass

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeGraphPhysicalLocalization
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalScalarCollisionMass
open OriginalWeightedMacroSelection NativeGraphTubeCellVisits

variable {P T Cell H : Type*} [DecidableEq P] [DecidableEq T]
  [DecidableEq Cell] [DecidableEq H]

/-- Height/tube vertices may occur in several physical cells. The correct
comparison is an inequality, not a claimed disjoint partition. -/
lemma vertices_le_sum_local (I : Finset (P × T)) (height : P → H) (cell : P → Cell) :
    ((vertices I height).card:ℝ) ≤
      ∑c∈I.image (fun e => cell e.1), ((vertices (cut I cell c) height).card:ℝ) := by
  have hu : (I.image (fun e => cell e.1)).biUnion
      (fun c => vertices (cut I cell c) height)=vertices I height := by
    ext v
    constructor
    · intro hv
      obtain ⟨c,_hc,hv⟩ := mem_biUnion.mp hv
      rw [vertices_eq_original_incidence_image] at hv ⊢
      obtain ⟨e,he,hev⟩ := mem_image.mp hv
      exact mem_image.mpr ⟨e,(mem_filter.mp he).1,hev⟩
    · intro hv
      rw [vertices_eq_original_incidence_image] at hv
      obtain ⟨e,he,hev⟩ := mem_image.mp hv
      apply mem_biUnion.mpr
      refine ⟨cell e.1,mem_image_of_mem _ he,?_⟩
      rw [vertices_eq_original_incidence_image]
      exact mem_image.mpr ⟨e,mem_filter.mpr ⟨he,rfl⟩,hev⟩
  have hh : ((I.image (fun e => cell e.1)).biUnion
      (fun c => vertices (cut I cell c) height)).card ≤
      ∑c∈I.image (fun e => cell e.1), (vertices (cut I cell c) height).card := card_biUnion_le
  rw [hu] at hh
  exact_mod_cast hh

omit [DecidableEq P] in
/-- The denominator double-counts actual tube/cell pairs. Its multiplicity
is exactly the number of cells visited by each active geometric tube. -/
lemma sum_local_tubes_le (I : Finset (P × T)) (cell : P → Cell) (N : ℕ)
    (hvisit : ∀t∈I.image Prod.snd,
      ((I.filter (fun e => e.2=t)).image (fun e => cell e.1)).card ≤ N) :
    (∑c∈I.image (fun e => cell e.1),
      ((TwoTubePathCollisionCount.tubes (cut I cell c)).card:ℝ)) ≤
      (N:ℝ)*(TwoTubePathCollisionCount.tubes I).card := by
  have hid := sum_local_heights_eq_height_cells I (fun e => cell e.1) Prod.snd
  have hsum : (∑c∈I.image (fun e => cell e.1),
      (TwoTubePathCollisionCount.tubes (cut I cell c)).card) ≤
      N*(TwoTubePathCollisionCount.tubes I).card := by
    change (∑c∈I.image (fun e => cell e.1), ((cut I cell c).image Prod.snd).card) ≤ _
    rw [show (∑c∈I.image (fun e => cell e.1), ((cut I cell c).image Prod.snd).card)=
      ∑t∈I.image Prod.snd, ((I.filter (fun e => e.2=t)).image (fun e => cell e.1)).card by
        simpa only [localHeights,localPoints,cut] using hid]
    exact (sum_le_sum hvisit).trans_eq (by simp only [sum_const,smul_eq_mul]; exact Nat.mul_comm _ _)
  exact_mod_cast hsum

/-- The weighted physical-cell choice retains height density with its
computed tube-visit loss and preserves all tubes at every surviving point. -/
theorem exists_cell_with_height_density (I : Finset (P × T)) (hI : I.Nonempty)
    (height : P → H) (Z : Finset H) (cell : P → Cell) (N : ℕ) {lambda : ℝ}
    (hlambda : 0 ≤ lambda)
    (hmass : lambda*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤ (vertices I height).card)
    (hvisit : ∀t∈I.image Prod.snd,
      ((I.filter (fun e => e.2=t)).image (fun e => cell e.1)).card ≤ N) :
    ∃c∈I.image (fun e => cell e.1),
      (cut I cell c).Nonempty ∧ cut I cell c⊆I ∧
      (∀p∈TwoTubePathCollisionCount.points (cut I cell c),
        tubesAt (cut I cell c) p=tubesAt I p) ∧
      lambda*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes (cut I cell c)).card ≤
        (N:ℝ)*(vertices (cut I cell c) height).card := by
  have hden := sum_local_tubes_le I cell N hvisit
  have hnum := vertices_le_sum_local I height cell
  have hsum : (∑c∈I.image (fun e => cell e.1),
      lambda*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes (cut I cell c)).card) ≤
      ∑c∈I.image (fun e => cell e.1), (N:ℝ)*(vertices (cut I cell c) height).card := by
    calc
      _ = (lambda*(Z.card:ℝ))*∑c∈I.image (fun e => cell e.1),
          ((TwoTubePathCollisionCount.tubes (cut I cell c)).card:ℝ) := by rw [mul_sum]
      _ ≤ (lambda*(Z.card:ℝ))*((N:ℝ)*(TwoTubePathCollisionCount.tubes I).card) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ = (N:ℝ)*(lambda*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card) := by ring
      _ ≤ (N:ℝ)*(vertices I height).card := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg N)
      _ ≤ (N:ℝ)*∑c∈I.image (fun e => cell e.1), ((vertices (cut I cell c) height).card:ℝ) :=
        mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg N)
      _ = _ := by rw [mul_sum]
  obtain ⟨c,hc,hden⟩ := exists_le_of_sum_le (hI.image (fun e => cell e.1)) hsum
  exact ⟨c,hc,cut_nonempty I cell c hc,cut_subset I cell c,
    fun p hp => cut_full_tube_fiber I cell c p (cut_point_cell I cell c p hp),hden⟩

/-- Actual bounded-slope incidences supply the visit count internally.
Thus the physical-cell choice adds only the fixed factor17^4 to lambda. -/
theorem actual_physical_cell {T : Type*} [DecidableEq T]
    (I : Finset (E4 × T)) (hI : I.Nonempty) (base slope : T → E4) (Z : Finset ℝ)
    {rho delta Delta lambda : ℝ}
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hdscale : delta ≤ rho^2)
    (hDelta : rho/2 ≤ Delta) (hlambda : 0 ≤ lambda)
    (hinc : ∀p t, (p,t)∈I → ∀j, |p j-base t j-p 3*slope t j| ≤ delta)
    (hslope : ∀t∈I.image Prod.snd, ∀j, |slope t j| ≤ 2)
    (hdiam : ∀p∈I.image Prod.fst, ∀q∈I.image Prod.fst, |p 3-q 3| ≤ rho)
    (hmass : lambda*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤
      (vertices I (fun p => p 3)).card) :
    ∃c∈I.image (fun e => wzDyadicCellIndex Delta e.1),
      (cut I (wzDyadicCellIndex Delta) c).Nonempty ∧ cut I (wzDyadicCellIndex Delta) c⊆I ∧
      (∀p∈TwoTubePathCollisionCount.points (cut I (wzDyadicCellIndex Delta) c),
        tubesAt (cut I (wzDyadicCellIndex Delta) c) p=tubesAt I p) ∧
      lambda*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes (cut I (wzDyadicCellIndex Delta) c)).card ≤
        (17^4:ℝ)*(vertices (cut I (wzDyadicCellIndex Delta) c) (fun p => p 3)).card := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using
    exists_cell_with_height_density I hI (fun p => p 3) Z (wzDyadicCellIndex Delta) (17^4)
      hlambda hmass (fun t ht => visited_card_le I base slope hrho hrho1 hdscale hDelta
        hinc hslope hdiam t ht)

end NativeGraphPhysicalLocalization
