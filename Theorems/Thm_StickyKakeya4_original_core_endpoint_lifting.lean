import Theorems.Thm_StickyKakeya4_original_ancestor_counting
import Theorems.Thm_StickyKakeya4_original_w_physical_growth
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalCoreEndpointLifting
open Classical OriginalWCoreDynamics OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open OriginalWPhysicalDisplacement

variable {P T K A : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K] [DecidableEq A]

def oneStates (I : Finset (P × T)) (height : P → ℝ) (cell : T → K) (angle : T → A)
    (S : Finset (ℝ × T)) (root : Core S) : Finset (Core S) :=
  insert root ((M I height cell angle S root).image (next I height cell angle S root))

def twoStates (I : Finset (P × T)) (height : P → ℝ) (cell : T → K) (angle : T → A)
    (S : Finset (ℝ × T)) (root : Core S) : Finset (Core S) :=
  insert root (((M I height cell angle S root).image (next I height cell angle S root)) ∪
    ((TwoStepMenuPaths.paths (M I height cell angle S root)
      (fun g => M I height cell angle S (next I height cell angle S root g))).image
      (fun gs => next I height cell angle S (next I height cell angle S root gs.1) gs.2)))

theorem one_state_height (I : Finset (P × T)) (height : P → ℝ) (cell : T → K) (angle : T → A)
    (S : Finset (ℝ × T)) (root state : Core S)
    (hs : state ∈ oneStates I height cell angle S root) : state.val.1=root.val.1 := by
  rcases Finset.mem_insert.mp hs with rfl | hs
  · rfl
  · obtain ⟨g,_hg,rfl⟩ := Finset.mem_image.mp hs
    exact next_preserves_height I height cell angle S root g

theorem two_state_height (I : Finset (P × T)) (height : P → ℝ) (cell : T → K) (angle : T → A)
    (S : Finset (ℝ × T)) (root state : Core S)
    (hs : state ∈ twoStates I height cell angle S root) : state.val.1=root.val.1 := by
  rcases Finset.mem_insert.mp hs with rfl | hs
  · rfl
  · rcases Finset.mem_union.mp hs with hs | hs
    · obtain ⟨g,_hg,rfl⟩ := Finset.mem_image.mp hs
      exact next_preserves_height I height cell angle S root g
    · obtain ⟨gs,_hgs,rfl⟩ := Finset.mem_image.mp hs
      exact (next_preserves_height I height cell angle S _ gs.2).trans
        (next_preserves_height I height cell angle S root gs.1)

/-- A finite selection in the occupied endpoint cells lifts to ACTUAL original
 points. Repeated core states at the same point never multiply its population. -/
theorem select_original_endpoint_points {X G : Type*} [DecidableEq X] [DecidableEq G]
    (states : Finset X) (representative : X → P) (pointCell : P → G) :
    ∃ selected : Finset X, ∃ points : Finset P,
      selected ⊆ states ∧ points=selected.image representative ∧
      Set.InjOn representative (↑selected) ∧ Set.InjOn pointCell (↑points) ∧
      points.image pointCell=states.image (pointCell ∘ representative) ∧
      points.card=(states.image (pointCell ∘ representative)).card := by
  obtain ⟨selected,hsub,himage,hinj,hcard⟩ :=
    OriginalAncestorCounting.exists_original_cell_representatives states (pointCell ∘ representative)
  let points := selected.image representative
  have hrep : Set.InjOn representative (↑selected) := by
    intro a ha b hb heq
    exact hinj ha hb (congrArg pointCell heq)
  have hpgrid : Set.InjOn pointCell (↑points) := by
    intro p hp q hq heq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    exact congrArg representative (hinj ha hb heq)
  refine ⟨selected,points,hsub,rfl,hrep,hpgrid,?_,?_⟩
  · simpa only [points,Finset.image_image] using himage
  · simpa only [points,Finset.card_image_of_injOn hrep] using hcard

/-- Every selected point remains a genuine original incidence, at the original
 root height, and retains an actual endpoint-state witness. -/
theorem selected_core_points_are_original (I : Finset (P × T)) (height : P → ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height) (root : Core S)
    (states selected : Finset (Core S)) (hsub : selected ⊆ states)
    (hheight : ∀ state ∈ states, state.val.1=root.val.1) :
    ∀ p ∈ selected.image (rep I height S hSV),
      p ∈ TwoTubePathCollisionCount.points I ∧ height p=root.val.1 ∧
      ∃ state ∈ states, rep I height S hSV state=p ∧ (p,state.val.2) ∈ I := by
  intro p hp
  obtain ⟨state,hs,rfl⟩ := Finset.mem_image.mp hp
  have hspec := rep_spec I height S hSV state
  exact ⟨Finset.mem_image_of_mem Prod.fst hspec.1,hspec.2.trans (hheight state (hsub hs)),
    state,hsub hs,rfl,hspec.1⟩


/-- These are exactly the occupied scalar endpoint cells used by native growth. -/
theorem scalar_cells_eq_endpoint_image
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ)
    (theta : T → Fin 3 → ℝ) (q rho : ℝ) (S : Finset (ℝ × T))
    (hSV : S ⊆ vertices I height) (root : Core S) :
    OriginalWPhysicalGrowth.scalarCells I height position theta q rho S hSV root =
      NativeTangentGridCoarsening.scalarCells
        (oneStates I height (terminalGrid q theta) (scalarAngle q theta) S root)
        (fun state => position (rep I height S hSV state)) (rho^2) := by
  rfl

/-- These are exactly the occupied planar endpoint cells used by native growth. -/
theorem planar_cells_eq_endpoint_image
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ × ℝ)
    (theta : T → Fin 3 → ℝ) (q rho : ℝ) (S : Finset (ℝ × T))
    (hSV : S ⊆ vertices I height) (root : Core S) :
    OriginalWPhysicalGrowth.planarCells I height position theta q rho S hSV root =
      NativeTangentGridCoarsening.planarCells
        (twoStates I height (terminalGrid q theta) (planarAngle q theta) S root)
        (fun state => position (rep I height S hSV state)) (rho^2) := by
  rfl

/-- Scalar growth endpoints lift to actual original points at the root's old
height. One original point per occupied sigma cell removes all state multiplicity,
and literal grid coarsening gives the original endpoint-cell population bound. -/
theorem exists_scalar_original_endpoint_points
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ)
    (theta : T → Fin 3 → ℝ) (q rho sigma : ℝ) (S : Finset (ℝ × T))
    (hSV : S ⊆ vertices I height) (root : Core S)
    (hrho : 0 < rho) (hscale : rho^2 ≤ sigma) :
    ∃ Epoints : Finset P,
      Epoints ⊆ TwoTubePathCollisionCount.points I ∧
      (∀ p ∈ Epoints, height p=root.val.1) ∧
      Set.InjOn (fun p => ⌊position p / sigma⌋) (↑Epoints) ∧
      Epoints.image (fun p => ⌊position p / sigma⌋) =
        (oneStates I height (terminalGrid q theta) (scalarAngle q theta) S root).image
          (fun state => ⌊position (rep I height S hSV state) / sigma⌋) ∧
      (∀ p ∈ Epoints,
        ∃ state ∈ oneStates I height (terminalGrid q theta) (scalarAngle q theta) S root,
          rep I height S hSV state=p ∧ (p,state.val.2) ∈ I) ∧
      ((OriginalWPhysicalGrowth.scalarCells I height position theta q rho S hSV root).card : ℝ)
          * rho^2 ≤ 3*sigma*(Epoints.card : ℝ) := by
  let states := oneStates I height (terminalGrid q theta) (scalarAngle q theta) S root
  let pointCell : P → ℤ := fun p => ⌊position p / sigma⌋
  obtain ⟨selected,points,hsub,hpoints,_hrep,hgrid,himage,hcard⟩ :=
    select_original_endpoint_points states (rep I height S hSV) pointCell
  have horiginal : ∀ p ∈ points,
      p ∈ TwoTubePathCollisionCount.points I ∧ height p=root.val.1 ∧
      ∃ state ∈ states, rep I height S hSV state=p ∧ (p,state.val.2) ∈ I := by
    rw [hpoints]
    exact selected_core_points_are_original I height S hSV root states selected hsub
      (fun state hs => one_state_height I height _ _ S root state hs)
  refine ⟨points,fun p hp => (horiginal p hp).1,
    fun p hp => (horiginal p hp).2.1,hgrid,?_,fun p hp => (horiginal p hp).2.2,?_⟩
  · exact himage
  · have hcoarse := NativeTangentGridCoarsening.scalar_grid_coarsening
      states (fun state => position (rep I height S hSV state)) (sq_pos_of_pos hrho) hscale
    have hcoarsecard :
        (NativeTangentGridCoarsening.scalarCells states
          (fun state => position (rep I height S hSV state)) sigma).card = points.card := by
      exact hcard.symm
    rw [hcoarsecard] at hcoarse
    rw [scalar_cells_eq_endpoint_image]
    apply (le_div_iff₀ (sq_pos_of_pos hrho)).mp
    calc
      _ ≤ (3*sigma/rho^2)*(points.card : ℝ) := hcoarse
      _ = (3*sigma*(points.card : ℝ))/rho^2 := by ring

/-- Native planar growth endpoints lift to actual original points, retaining
both coordinate identities and a genuine state/tube witness. The sigma-grid is
the literal product grid on ℝ × ℝ, and no endpoint multiplicity is postulated. -/
theorem exists_planar_original_endpoint_points
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ × ℝ)
    (theta : T → Fin 3 → ℝ) (q rho sigma : ℝ) (S : Finset (ℝ × T))
    (hSV : S ⊆ vertices I height) (root : Core S)
    (hrho : 0 < rho) (hscale : rho^2 ≤ sigma) :
    ∃ Epoints : Finset P,
      Epoints ⊆ TwoTubePathCollisionCount.points I ∧
      (∀ p ∈ Epoints, height p=root.val.1) ∧
      Set.InjOn (fun p => (⌊(position p).1 / sigma⌋,⌊(position p).2 / sigma⌋)) (↑Epoints) ∧
      Epoints.image (fun p => (⌊(position p).1 / sigma⌋,⌊(position p).2 / sigma⌋)) =
        (twoStates I height (terminalGrid q theta) (planarAngle q theta) S root).image
          (fun state => (⌊(position (rep I height S hSV state)).1 / sigma⌋,
            ⌊(position (rep I height S hSV state)).2 / sigma⌋)) ∧
      (∀ p ∈ Epoints,
        ∃ state ∈ twoStates I height (terminalGrid q theta) (planarAngle q theta) S root,
          rep I height S hSV state=p ∧ (p,state.val.2) ∈ I) ∧
      ((OriginalWPhysicalGrowth.planarCells I height position theta q rho S hSV root).card : ℝ)
          * rho^4 ≤ 9*sigma^2*(Epoints.card : ℝ) := by
  let states := twoStates I height (terminalGrid q theta) (planarAngle q theta) S root
  let pointCell : P → ℤ × ℤ := fun p => (⌊(position p).1 / sigma⌋,⌊(position p).2 / sigma⌋)
  obtain ⟨selected,points,hsub,hpoints,_hrep,hgrid,himage,hcard⟩ :=
    select_original_endpoint_points states (rep I height S hSV) pointCell
  have horiginal : ∀ p ∈ points,
      p ∈ TwoTubePathCollisionCount.points I ∧ height p=root.val.1 ∧
      ∃ state ∈ states, rep I height S hSV state=p ∧ (p,state.val.2) ∈ I := by
    rw [hpoints]
    exact selected_core_points_are_original I height S hSV root states selected hsub
      (fun state hs => two_state_height I height _ _ S root state hs)
  refine ⟨points,fun p hp => (horiginal p hp).1,
    fun p hp => (horiginal p hp).2.1,hgrid,?_,fun p hp => (horiginal p hp).2.2,?_⟩
  · exact himage
  · have hcoarse := NativeTangentGridCoarsening.planar_grid_coarsening
      states (fun state => position (rep I height S hSV state)) (sq_pos_of_pos hrho) hscale
    have hcoarsecard :
        (NativeTangentGridCoarsening.planarCells states
          (fun state => position (rep I height S hSV state)) sigma).card = points.card := by
      exact hcard.symm
    rw [hcoarsecard] at hcoarse
    rw [planar_cells_eq_endpoint_image]
    apply (le_div_iff₀ (pow_pos hrho 4)).mp
    calc
      _ ≤ (3*sigma/rho^2)^2*(points.card : ℝ) := hcoarse
      _ = (9*sigma^2*(points.card : ℝ))/rho^4 := by
        field_simp [ne_of_gt hrho]
        ring

end OriginalCoreEndpointLifting
