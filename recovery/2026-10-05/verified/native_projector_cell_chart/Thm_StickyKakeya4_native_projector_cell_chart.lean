import Theorems.Thm_StickyKakeya4_native_equal_rank_plane_transfer
import Theorems.Thm_StickyKakeya4_compatible_tuple_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeProjectorCellChart
open Classical Finset StickyKakeya4 NativeEqualRankPlaneTransfer SelfUniform
open scoped BigOperators

def basis : OrthonormalBasis (Fin 4) ℝ E4 := EuclideanSpace.basisFun (Fin 4) ℝ

lemma basis_norm (j : Fin 4) : ‖basis j‖=1 := basis.orthonormal.norm_eq_one j

lemma basis_expansion (v : E4) : ∑j : Fin 4,v j • basis j=v := basis.sum_repr v

lemma norm_le_coordinate_sum (v : E4) : ‖v‖ ≤ ∑i : Fin 4,|v i| := by
  calc
    ‖v‖ = ‖∑j : Fin 4,v j • basis j‖ := by rw [basis_expansion]
    _ ≤ ∑j : Fin 4,‖v j • basis j‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul,Real.norm_eq_abs,basis_norm,mul_one]

/-- A matrix entry of the actual orthogonal projection in fixed Euclidean coordinates. -/
def entry (P : Submodule ℝ E4) (ij : Fin 4 × Fin 4) : ℝ := (P.starProjection (basis ij.2)) ij.1

lemma entry_abs_le_one (P : Submodule ℝ E4) (ij : Fin 4 × Fin 4) : |entry P ij| ≤ 1 := by
  have hh := (PiLp.norm_apply_le (P.starProjection (basis ij.2)) ij.1).trans
    (P.norm_starProjection_apply_le (basis ij.2))
  simpa only [entry,Real.norm_eq_abs,basis_norm] using hh

abbrev Cell := (Fin 4 × Fin 4) → Fin 257

def chartCount : ℕ := 257^16

/-- A fixed finite grid of width1/128 in each of the sixteen projector entries. -/
def cell (P : Submodule ℝ E4) : Cell := fun ij =>
  ⟨⌊128*(entry P ij+1)⌋₊,by
    have hh := (abs_le.mp (entry_abs_le_one P ij)).2
    have hfloor : ⌊128*(entry P ij+1)⌋₊ ≤ 256 := Nat.floor_le_of_le (by norm_num; linarith)
    omega⟩

lemma card_cell : Fintype.card Cell=chartCount := by
  norm_num [Cell,chartCount]

lemma same_cell_entry (P Q : Submodule ℝ E4) (H : cell P=cell Q) (ij : Fin 4 × Fin 4) :
    |entry P ij-entry Q ij| ≤ 1/128 := by
  have hfloor : ⌊128*(entry P ij+1)⌋₊=⌊128*(entry Q ij+1)⌋₊ :=
    congrArg Fin.val (congrFun H ij)
  have hP0 : 0 ≤ 128*(entry P ij+1) := by
    have hh := (abs_le.mp (entry_abs_le_one P ij)).1
    linarith
  have hQ0 : 0 ≤ 128*(entry Q ij+1) := by
    have hh := (abs_le.mp (entry_abs_le_one Q ij)).1
    linarith
  have hPl := Nat.floor_le hP0
  have hQl := Nat.floor_le hQ0
  have hPu := Nat.lt_floor_add_one (128*(entry P ij+1))
  have hQu := Nat.lt_floor_add_one (128*(entry Q ij+1))
  rw [hfloor] at hPl hPu
  apply abs_le.mpr
  constructor <;> linarith

lemma same_cell_column (P Q : Submodule ℝ E4) (H : cell P=cell Q) (j : Fin 4) :
    ‖P.starProjection (basis j)-Q.starProjection (basis j)‖ ≤ 1/32 := by
  calc
    _ ≤ ∑i : Fin 4,|(P.starProjection (basis j)-Q.starProjection (basis j)) i| := norm_le_coordinate_sum _
    _ ≤ ∑_i : Fin 4,(1/128:ℝ) := sum_le_sum (fun i _ => same_cell_entry P Q H (i,j))
    _ = _ := by norm_num

/-- Entrywise quantization controls the full operator on every vector. -/
theorem same_cell_projection_difference (P Q : Submodule ℝ E4) (H : cell P=cell Q) (v : E4) :
    ‖P.starProjection v-Q.starProjection v‖ ≤ (1/8:ℝ)*‖v‖ := by
  have hexpand : P.starProjection v-Q.starProjection v=
      ∑j : Fin 4,v j • (P.starProjection (basis j)-Q.starProjection (basis j)) := by
    conv_lhs => rw [←basis_expansion v]
    rw [map_sum,map_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [map_smul,map_smul,smul_sub]
  calc
    _ = ‖∑j : Fin 4,v j • (P.starProjection (basis j)-Q.starProjection (basis j))‖ := by rw [hexpand]
    _ ≤ ∑j : Fin 4,‖v j • (P.starProjection (basis j)-Q.starProjection (basis j))‖ := norm_sum_le _ _
    _ ≤ ∑_j : Fin 4,‖v‖*(1/32:ℝ) := by
      apply sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v j) (same_cell_column P Q H j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

lemma same_cell_operator_norm (P Q : Submodule ℝ E4) (H : cell P=cell Q) :
    ‖P.starProjection-Q.starProjection‖ ≤ (1/8:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  exact same_cell_projection_difference P Q H

lemma same_cell_forward_gap (P Q : Submodule ℝ E4) (H : cell P=cell Q) :
    ∀v∈Q,Metric.infDist v (P:Set E4) ≤ (1/8:ℝ)*‖v‖ := by
  intro v hv
  rw [←projection_residual_eq_infDist]
  have he : Q.starProjection v=v := Q.starProjection_eq_self_iff.mpr hv
  calc
    _ = ‖Q.starProjection v-P.starProjection v‖ := by rw [he]
    _ ≤ _ := same_cell_projection_difference Q P H.symm v

/-- The controlled inverse is derived from equal rank and the actual cells. -/
theorem same_cell_projection_lift (P Q : Submodule ℝ E4) (hdim : Module.finrank ℝ P=Module.finrank ℝ Q)
    (H : cell P=cell Q) :
    ∀p : P,∃v : Q,P.orthogonalProjectionOnto (v:E4)=p ∧ ‖v‖ ≤ 2*‖p‖ :=
  controlled_projection_lift P Q (1/8) hdim (by norm_num) (same_cell_forward_gap P Q H)

/-- Keep whole node preimages, with original integer weights. The reference
plane is the plane of an actual retained occurrence, not a grid surrogate. -/
theorem select_whole_nodes {A N : Type*} [DecidableEq A] [DecidableEq N]
    (S : Finset A) (hS : S.Nonempty) (w : A → ℕ) (node : A → N) (plane : N → Submodule ℝ E4) :
    ∃x0∈S,∃T : Finset A,
      T=S.filter (fun x => cell (plane (node x))=cell (plane (node x0))) ∧
      x0∈T ∧ T⊆S ∧ mass w S ≤ chartCount*mass w T ∧
      (∀x y,x∈S → y∈T → node x=node y → x∈T) ∧
      (∀x∈T,‖(plane (node x)).starProjection-(plane (node x0)).starProjection‖ ≤ (1/8:ℝ)) ∧
      (∀x∈T,∀v∈plane (node x),Metric.infDist v (plane (node x0):Set E4) ≤ (1/8:ℝ)*‖v‖) := by
  let f := fun x => cell (plane (node x))
  obtain ⟨t,ht,hmax⟩ := exists_max_image (S.image f)
    (fun t => mass w (S.filter (fun x => f x=t))) (hS.image f)
  obtain ⟨x0,hx0,hft⟩ := mem_image.mp ht
  let T := S.filter (fun x => f x=f x0)
  have hcard : (S.image f).card ≤ chartCount := by
    exact (card_le_univ _).trans_eq card_cell
  have hmass : mass w S ≤ chartCount*mass w T := by
    calc
      _ = ∑u∈S.image f,mass w (S.filter (fun x => f x=u)) := CompatibleTupleSelection.mass_eq_sum_partition w S f
      _ ≤ ∑_u∈S.image f,mass w T := by
        apply sum_le_sum
        intro u hu
        simpa only [T,hft] using hmax u hu
      _ = (S.image f).card*mass w T := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hcard
  refine ⟨x0,hx0,T,rfl,mem_filter.mpr ⟨hx0,rfl⟩,filter_subset _ _,hmass,?_,?_,?_⟩
  · intro x y hx hy hnode
    exact mem_filter.mpr ⟨hx,(show f x=f y by dsimp [f]; rw [hnode]).trans (mem_filter.mp hy).2⟩
  · intro x hx
    exact same_cell_operator_norm _ _ (mem_filter.mp hx).2
  · intro x hx
    exact same_cell_forward_gap _ _ (mem_filter.mp hx).2.symm

/-- Equal-dimensional actual node planes in the retained whole-node set
have controlled projection lifts to its actual reference plane. -/
theorem select_whole_nodes_with_lifts {A N : Type*} [DecidableEq A] [DecidableEq N]
    (S : Finset A) (hS : S.Nonempty) (w : A → ℕ) (node : A → N)
    (plane : N → Submodule ℝ E4) (k : ℕ) (hrank : ∀x∈S,Module.finrank ℝ (plane (node x))=k) :
    ∃x0∈S,∃T : Finset A,
      T=S.filter (fun x => cell (plane (node x))=cell (plane (node x0))) ∧
      x0∈T ∧ T⊆S ∧ mass w S ≤ chartCount*mass w T ∧
      (∀x y,x∈S → y∈T → node x=node y → x∈T) ∧
      (∀x∈T,‖(plane (node x)).starProjection-(plane (node x0)).starProjection‖ ≤ (1/8:ℝ)) ∧
      (∀x∈T,∀p : plane (node x0),∃v : plane (node x),
        (plane (node x0)).orthogonalProjectionOnto (v:E4)=p ∧ ‖v‖ ≤ 2*‖p‖) := by
  obtain ⟨x0,hx0,T,hT,hxT,hTS,hmass,hsat,hgap,_hforward⟩ := select_whole_nodes S hS w node plane
  refine ⟨x0,hx0,T,hT,hxT,hTS,hmass,hsat,hgap,?_⟩
  intro x hx
  have hcell : cell (plane (node x0))=cell (plane (node x)) := by
    rw [hT] at hx
    exact (mem_filter.mp hx).2.symm
  exact same_cell_projection_lift _ _ ((hrank x0 hx0).trans (hrank x (hTS hx)).symm) hcell

end NativeProjectorCellChart
