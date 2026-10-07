import Theorems.Thm_StickyKakeya4_native_core_physical_displacement
import Theorems.Thm_StickyKakeya4_native_localized_phase_alphabet
import Theorems.Thm_StickyKakeya4_original_reference_angle_geometry
import Theorems.Thm_StickyKakeya4_original_terminal_scalar_collision_geometry
import Theorems.Thm_StickyKakeya4_native_original_phase_window_graph
import Theorems.Thm_StickyKakeya4_native_quantized_line_packets

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeCoreSpatialWindow
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalDiameterCount
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWCoreDynamics
open OriginalWPhysicalDisplacement OriginalWGrainDrift OriginalPhaseWindowGraph
open NativeOriginalPhaseWindowGraph OriginalReferenceAngleGeometry
open OriginalTerminalScalarCollisionGeometry NativeCorePhysicalDisplacement
open NativeLocalizedPhaseAlphabet

def jointNeighbors (c : GrainLabel × Index) : Finset (GrainLabel × Index) :=
  neighborCells c.1 ×ˢ indexBox c.2 41

lemma jointNeighbors_card (c : GrainLabel × Index) :
    (jointNeighbors c).card = 9*83^4 := by
  simp only [jointNeighbors,card_product,neighborCells_card,indexBox_card]
  norm_num

lemma jointNeighbors_self (c : GrainLabel × Index) : c∈jointNeighbors c := by
  refine mem_product.mpr ⟨self_mem_neighborCells c.1,?_⟩
  apply Fintype.mem_piFinset.mpr
  intro j
  exact mem_Icc.mpr ⟨by omega,by omega⟩

lemma physical_neighbor {rho Delta : ℝ} (hrho : 0 < rho) (hD : rho/2 ≤ Delta)
    (x y : E4) (hxy : ∀j, |x j-y j| ≤ 20*rho) :
    wzDyadicCellIndex Delta x∈indexBox (wzDyadicCellIndex Delta y) 41 := by
  have hDelta : 0 < Delta := (half_pos hrho).trans_le hD
  apply Fintype.mem_piFinset.mpr
  intro j
  apply NativeQuantizedLinePackets.floor_mem_interval 41
  rw [←sub_div,abs_div,abs_of_pos hDelta]
  apply (div_le_iff₀ hDelta).mpr
  have hj := hxy j
  norm_num
  linarith only [hj,hD,hrho]

/-- The same original rich core is localized jointly in a grain cell and a
coarse physical cell. Full menus are retained. The physical neighborhood is
derived from the actual incidences and bounded packed slopes, and the grain
neighborhood from the actual direction graph and field variation. -/
theorem from_prescribed_rich_core {T : Type*} [DecidableEq T]
    (I : Finset (E4 × T)) (base slope : T → E4) (offset : E4 → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (Z Phi : Finset ℝ) (angle : T → ℝ)
    (S : Finset (ℝ × T)) (hSV : S⊆vertices I (fun p => p 3)) (hS : S.Nonempty)
    (r tau x₀ : ℝ) (xi₀ : ℝ × ℝ)
    {beta delta rho q Lip Delta : ℝ}
    (hbeta : 0 ≤ beta) (hd : 0 ≤ delta) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hdscale : delta ≤ rho^2) (hq : 0 < q) (hqrho : q ≤ rho)
    (hLip : 1 ≤ Lip) (hDelta : rho/2 ≤ Delta)
    (hinc : ∀p t, (p,t)∈I → ∀j,
      |p j-base t j-p 3*slope t j| ≤ delta)
    (hslope : ∀t∈TwoTubePathCollisionCount.tubes I, ∀j, |slope t j| ≤ 2)
    (hdir : ∀p t, (p,t)∈I →
      ‖(slope t 1,slope t 2)-offset p-F (p 3) (slope t 0)‖ ≤ 512*delta)
    (hF : ∀z∈Z, ‖F z‖ ≤ 1)
    (hcluster : ∀s∈Z, ∀t∈Z, ‖F s-F t‖ ≤ Lip*rho)
    (hheight : ∀p∈TwoTubePathCollisionCount.points I, p 3∈Z)
    (hdiam : ∀s∈Z, ∀t∈Z, |s-t| ≤ rho)
    (hrich : ∀s∈S,
      beta*(Z.card:ℝ)^2*(Phi.card:ℝ)^2 ≤
        ((coarseMenus I (fun p => p 3) (scalarTerminalCell q (fun t => slope t 0)) angle S s).card:ℝ) ∧
      coarseMenus I (fun p => p 3) (scalarTerminalCell q (fun t => slope t 0)) angle S s ⊆
        (Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi)) :
    let height := fun p : E4 => p 3
    let terminal := scalarTerminalCell q (fun t => slope t 0)
    let width := (9*Lip+8193)*rho^2
    let representative := rep I height S hSV
    let grain := fun s : Core S => grainCell width
      (grainCoordinate height (fun p => p 0) (fun p => (p 1,p 2)) F (representative s))
    let cell := fun s : Core S => (grain s,wzDyadicCellIndex Delta (representative s))
    let phase := fun s : Core S => phaseLabel r tau x₀ xi₀ (fun p => p 0) offset (representative s)
    ∃z∈Z, ∃c : GrainLabel × Index, ∃pick : OriginalPhaseGridPopulation.Label → Core S,
      IsLocalizedGraph (heightSlice S z) cell phase jointNeighbors (9*83^4)
        ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi)) (M I height terminal angle S)
        (next I height terminal angle S) (beta*(Z.card:ℝ)^2*(Phi.card:ℝ)^2) c pick := by
  intro height terminal width representative grain cell phase
  obtain ⟨s,hs⟩ := hS
  let s₀ : Core S := ⟨s,hs⟩
  let z := s.1
  let E := heightSlice S z
  have hE : E.Nonempty := ⟨s₀,mem_filter.mpr ⟨mem_attach S s₀,rfl⟩⟩
  have hz : z∈Z := by
    have hp := rep_spec I height S hSV s₀
    simpa only [hp.2] using hheight _ (mem_image_of_mem Prod.fst hp.1)
  have hIncU : ∀p t, (p,t)∈I →
      ‖incidenceResidual height (fun p => p 0) (fun t => base t 0) (fun t => slope t 0) p t‖ ≤ 1*delta := by
    intro p t hp
    simpa only [incidenceResidual,smul_eq_mul,Real.norm_eq_abs,one_mul] using hinc p t hp 0
  have hIncV : ∀p t, (p,t)∈I →
      ‖incidenceResidual height (fun p => (p 1,p 2))
        (fun t => (base t 1,base t 2)) (fun t => (slope t 1,slope t 2)) p t‖ ≤ 1*delta := by
    intro p t hp
    exact max_le (by simpa only [one_mul] using hinc p t hp 1)
      (by simpa only [one_mul] using hinc p t hp 2)
  have hnext : ∀v∈E, ∀j∈M I height terminal angle S v,
      next I height terminal angle S v j∈E ∧
      cell (next I height terminal angle S v j)∈jointNeighbors (cell v) := by
    intro v hv j hj
    refine ⟨mem_filter.mpr ⟨mem_attach S _,
      (next_preserves_height I height terminal angle S v j).trans (mem_filter.mp hv).2⟩,?_⟩
    apply mem_product.mpr
    constructor
    · apply grainCell_neighbor (show 0 < width by dsimp [width]; positivity)
      have hh := constructed_reference_grain_drift I height (fun p => p 0) (fun p => (p 1,p 2))
        offset (fun t => base t 0) (fun t => slope t 0)
        (fun t => (base t 1,base t 2)) (fun t => (slope t 1,slope t 2)) F Z terminal angle S hSV
        (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤2)
        (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤512) (by linarith only [hLip])
        hd hrho.le hrho1 hdscale hIncU hIncV hdir
        (fun t ht => by simpa only [Real.norm_eq_abs] using hslope t ht 0)
        hF hcluster hheight hdiam
        (fun t u he => (scalar_terminal_gap (fun t => slope t 0) hq t u he).trans hqrho) v j hj
      apply hh.trans
      dsimp [width]
      norm_num
      nlinarith only [sq_nonneg rho]
    · apply physical_neighbor hrho hDelta
      intro k
      have hh := constructed_successor_bound I height terminal angle
        (fun p => p k) (fun t => base t k) (fun t => slope t k) Z S hSV hrho.le
        (fun p t hp => by simpa only [incidenceResidual,smul_eq_mul,Real.norm_eq_abs] using hinc p t hp k)
        (fun t ht => by simpa only [Real.norm_eq_abs] using hslope t ht k)
        hheight hdiam v j hj
      exact hh.trans (configured_radius_bound hrho.le hrho1 hdscale)
  obtain ⟨c,pick,hGraph⟩ := exists_localized_graph E hE cell phase jointNeighbors (9*83^4)
    jointNeighbors_self (fun c => (jointNeighbors_card c).le)
    ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi)) (M I height terminal angle S) (next I height terminal angle S)
    (show 0 ≤ beta*(Z.card:ℝ)^2*(Phi.card:ℝ)^2 by positivity)
    (fun v _hv => (hrich v.val v.property).2)
    (fun v _hv => (hrich v.val v.property).1) hnext
  exact ⟨z,hz,c,pick,hGraph⟩

end NativeCoreSpatialWindow
