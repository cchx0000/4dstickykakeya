import Theorems.Thm_StickyKakeya4_native_actual_configured_point
import Theorems.Thm_StickyKakeya4_height_graph_residue_separation
import Theorems.Thm_StickyKakeya4_exact_height_no_deletion_recoding

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeActualConfiguredResidue
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open CanonicalConfiguredE4Bridge CanonicalConfiguredPointRounding CanonicalGridRecoding
open NativeMatrixHeightWholePoint NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open scoped BigOperators Matrix.Norms.Elementwise

/-- The actual four INTEGER parameters of the configured point. They are
computed from its unchanged pxy label and its already frozen fields. -/
def parameter (s : Split) (mu : ℝ) (R : ℕ)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z : Label ℤ (tangentDim s) (normalDim s)) : HeightGraphResidueSeparation.Parameter := by
  let ht:=z.1/((8*R:ℕ):ℤ)
  let x:=coarseGrid mu R z.2.1
  let y:=recodedY mu R (F z.1-Fcfg ht) z.2.1 z.2.2
  cases s with
  | oneTwo => exact ![x 0,y 0,y 1,ht]
  | twoOne => exact ![x 0,x 1,y 0,ht]

lemma parameter_height (s : Split) (mu : ℝ) (R : ℕ)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z : Label ℤ (tangentDim s) (normalDim s)) :
    parameter s mu R F Fcfg z 3=z.1/((8*R:ℕ):ℤ) := by
  cases s <;> rfl

lemma parameterX_eq_coarse (s : Split) (mu : ℝ) (R : ℕ)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z : Label ℤ (tangentDim s) (normalDim s)) :
    HeightGraphResidueSeparation.parameterX s (parameter s mu R F Fcfg z)=coarseGrid mu R z.2.1 := by
  cases s <;> funext i <;> fin_cases i <;> rfl

lemma parameterY_eq_recoded (s : Split) (mu : ℝ) (R : ℕ)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z : Label ℤ (tangentDim s) (normalDim s)) :
    HeightGraphResidueSeparation.parameterY s (parameter s mu R F Fcfg z)=
      recodedY mu R (F z.1-Fcfg (z.1/((8*R:ℕ):ℤ))) z.2.1 z.2.2 := by
  cases s <;> funext i <;> fin_cases i <;> rfl

/-- After the actual single-height freeze there is no matrix translation
of the normal grid: it is the aligned recoding of the SAME original Y label. -/
lemma parameterY_of_frozen (s : Split) (mu : ℝ) (R : ℕ) (hmu : 0< mu)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z : Label ℤ (tangentDim s) (normalDim s))
    (hfreeze : F z.1=Fcfg (z.1/((8*R:ℕ):ℤ))) :
    HeightGraphResidueSeparation.parameterY s (parameter s mu R F Fcfg z)=
      fun i => z.2.2 i/(R:ℤ) := by
  rw [parameterY_eq_recoded,hfreeze,sub_self,ExactHeightNoDeletionRecoding.recodedY_zero,
    coarseGrid_eq_ediv mu R hmu]

/-- Both realizations are literally the same point, including the second
factor1/512. No new point, grid, graph field, or representative is chosen. -/
theorem graphGrid_eq (s : Split) (mu : ℝ) (R : ℕ)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z : Label ℤ (tangentDim s) (normalDim s)) :
    NativeActualConfiguredPoint.graphGrid s mu R F Fcfg z=
      HeightGraphResidueSeparation.graphGrid s ((mu*(R:ℝ))/512) Fcfg (parameter s mu R F Fcfg z) := by
  cases s <;> ext j <;> fin_cases j
  all_goals
    simp [NativeActualConfiguredPoint.graphGrid,parameter,HeightGraphResidueSeparation.graphGrid,
      HeightGraphResidueSeparation.parameterX,HeightGraphResidueSeparation.parameterY,
      CanonicalAngularOffsetGeometry.tangentIndex,CanonicalAngularOffsetGeometry.normalIndex,assemble,coarseX,configuredNormal,graphPoint,center,
      PiLp.smul_apply,smul_eq_mul,Fin.sum_univ_two]
    <;> ring

/-- Deduplicating actual configured points is exactly deduplicating their
four integer graph parameters. -/
theorem graphGrid_eq_iff_parameter (s : Split) (mu : ℝ) (R : ℕ) (hmu : 0< mu) (hR : 0< R)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z w : Label ℤ (tangentDim s) (normalDim s)) :
    NativeActualConfiguredPoint.graphGrid s mu R F Fcfg z=
        NativeActualConfiguredPoint.graphGrid s mu R F Fcfg w ↔
      parameter s mu R F Fcfg z=parameter s mu R F Fcfg w := by
  rw [graphGrid_eq,graphGrid_eq]
  exact (HeightGraphResidueSeparation.graphGrid_injective s ((mu*(R:ℝ))/512)
    (by positivity) Fcfg).eq_iff

/-- The literal coarse-height, coarse-X and recoded-Y triple is the exact
configured-point key; the recoded-Y part becomes aligned Y/R under freezing. -/
theorem graphGrid_eq_iff_keys (s : Split) (mu : ℝ) (R : ℕ) (hmu : 0< mu) (hR : 0< R)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z w : Label ℤ (tangentDim s) (normalDim s)) :
    NativeActualConfiguredPoint.graphGrid s mu R F Fcfg z=
        NativeActualConfiguredPoint.graphGrid s mu R F Fcfg w ↔
      z.1/((8*R:ℕ):ℤ)=w.1/((8*R:ℕ):ℤ) ∧
      (fun j => z.2.1 j/(R:ℤ))=(fun j => w.2.1 j/(R:ℤ)) ∧
      recodedY mu R (F z.1-Fcfg (z.1/((8*R:ℕ):ℤ))) z.2.1 z.2.2=
        recodedY mu R (F w.1-Fcfg (w.1/((8*R:ℕ):ℤ))) w.2.1 w.2.2 := by
  rw [graphGrid_eq_iff_parameter s mu R hmu hR F Fcfg z w]
  constructor
  · intro he
    have hh:=congrFun he (3:Fin 4)
    have hx:=congrArg (HeightGraphResidueSeparation.parameterX s) he
    have hy:=congrArg (HeightGraphResidueSeparation.parameterY s) he
    rw [parameter_height,parameter_height] at hh
    rw [parameterX_eq_coarse,parameterX_eq_coarse,coarseGrid_eq_ediv mu R hmu,
      coarseGrid_eq_ediv mu R hmu] at hx
    rw [parameterY_eq_recoded,parameterY_eq_recoded] at hy
    exact ⟨hh,hx,hy⟩
  · rintro ⟨hh,hx,hy⟩
    apply HeightGraphResidueSeparation.parameter_ext s
    · simpa only [parameter_height] using hh
    · simpa only [parameterX_eq_coarse,coarseGrid_eq_ediv mu R hmu] using hx
    · simpa only [parameterY_eq_recoded] using hy

/-- The actual source's last GLOBAL parameter residue cut, performed before
its sole third core. The fixed8^4 charge upgrades the geometric image from
base deltaCfg/512 to the requested deltaOut=deltaCfg/64 separation. -/
theorem select_actual_edges {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (A : Finset (Fin n × Index)) (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (hR : 0< R) :
    ∃color : Fin 4 → Fin 8,∃B⊆A.image Prod.snd,let T:=edgeLift A Prod.snd B
      T⊆A ∧ A.card≤ 8^4*T.card ∧
      (∀k∈B,T.filter (fun z => z.2=k)=A.filter (fun z => z.2=k)) ∧
      (∀k∈B,SeparatedAlignmentPatches.color 8 (by norm_num)
        (parameter s (mu m) R F Fcfg (NativeActualConfiguredPoint.sourceLabel D a m p s P hP hd F k))=color) ∧
      (∀x∈T.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2),
        ∀y∈T.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2),
        x≠y → (mu m*(R:ℝ))/64≤ dist x y) ∧
      (∀z∈T,∀u∈T,
        NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2 (3:Fin 4)≠
          NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R u.2 (3:Fin 4) →
        (mu m*(R:ℝ))/64≤ dist
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2 (3:Fin 4))
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R u.2 (3:Fin 4))) := by
  let par := fun k => parameter s (mu m) R F Fcfg
    (NativeActualConfiguredPoint.sourceLabel D a m p s P hP hd F k)
  let paint := fun k => SeparatedAlignmentPatches.color 8 (by norm_num) (par k)
  let weight := fun k => (A.filter (fun z => z.2=k)).card
  obtain ⟨color,hret⟩:=SeparatedAlignmentPatches.maximum_weight_color (A.image Prod.snd) weight paint
  let B:=(A.image Prod.snd).filter (fun k => paint k=color)
  have hB : B⊆A.image Prod.snd := filter_subset _ _
  have hmass : mass (A.image Prod.snd) weight=A.card := (card_eq_sum_card_image Prod.snd A).symm
  have hret' : mass (A.image Prod.snd) weight≤ 8^4*mass B weight := by
    simpa only [mass,Fintype.card_fun,Fintype.card_fin] using hret
  rw [hmass,←edgeLift_card A Prod.snd B] at hret'
  have hcolor (k : Index) (hk : k∈B) : paint k=color := (mem_filter.mp hk).2
  have hbase : 0< (mu m*(R:ℝ))/512 := by have hp:=mu_pos m; positivity
  have hscale : ((mu m*(R:ℝ))/512)*(8:ℝ)=(mu m*(R:ℝ))/64 := by ring
  have hmap (k : Index) : NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R k=
      HeightGraphResidueSeparation.graphGrid s ((mu m*(R:ℝ))/512) Fcfg (par k) :=
    graphGrid_eq s (mu m) R F Fcfg _
  refine ⟨color,B,hB,filter_subset _ _,hret',(fun k hk => edgeLift_fiber A Prod.snd B k hk),hcolor,?_,?_⟩
  · intro x hx y hy hxy
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hx
    obtain ⟨u,hu,rfl⟩:=mem_image.mp hy
    have hc := (hcolor z.2 (mem_filter.mp hz).2).trans (hcolor u.2 (mem_filter.mp hu).2).symm
    have hne : par z.2≠par u.2 := by
      intro he
      apply hxy
      rw [hmap z.2,hmap u.2,he]
    have hs:=HeightGraphResidueSeparation.graphGrid_residue_separation s _ hbase Fcfg 8
      (by norm_num) hc hne
    rw [Nat.cast_ofNat,hscale] at hs
    simpa only [hmap] using hs
  · intro z hz u hu hzu
    have hc := (hcolor z.2 (mem_filter.mp hz).2).trans (hcolor u.2 (mem_filter.mp hu).2).symm
    have hne : par z.2 3≠par u.2 3 := by
      intro he
      apply hzu
      rw [hmap z.2,hmap u.2,HeightGraphResidueSeparation.graphGrid_height,
        HeightGraphResidueSeparation.graphGrid_height,he]
    have hs:=HeightGraphResidueSeparation.colored_coordinate_gap _ hbase 8
      (by norm_num) hc 3 hne
    rw [Nat.cast_ofNat,hscale] at hs
    simpa only [hmap,HeightGraphResidueSeparation.graphGrid_height] using hs

end NativeActualConfiguredResidue
