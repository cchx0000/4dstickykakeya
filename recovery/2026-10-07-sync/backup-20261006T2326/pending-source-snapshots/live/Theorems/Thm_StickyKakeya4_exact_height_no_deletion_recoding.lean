import Theorems.Thm_StickyKakeya4_weighted_canonical_recoding
import Theorems.Thm_StickyKakeya4_native_exact_height_fields

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace ExactHeightNoDeletionRecoding
open Classical Finset CanonicalGridRecoding WeightedCanonicalRecoding
open scoped BigOperators

variable {k l : ℕ}

/-- The exact integer recoding of all old labels. Time may have its own
coarsening factor; the supplied coarse-height map is kept literally. -/
def coarsenLabel {H Z : Type*} (R : ℕ) (height : H → Z) (a : Label H k l) : Label Z k l :=
  (height a.1,((fun j => a.2.1 j/(R:ℤ)),(fun i => a.2.2 i/(R:ℤ))))

def actualLabel {H Z : Type*} (mu : ℝ) (R : ℕ) (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (a : Label H k l) : Label Z k l :=
  ((newY mu R height F Fcfg a).1,(newX mu R a,(newY mu R height F Fcfg a).2))

theorem recodedY_zero (mu : ℝ) (R : ℕ) (u : Grid k) (v : Grid l) :
    recodedY mu R (0 : Matrix (Fin l) (Fin k) ℝ) u v=coarseGrid mu R v := by
  funext i
  simp only [recodedY,Matrix.zero_apply,zero_mul,sum_const_zero,add_zero,coarseGrid]

/-- NativeExactHeightFields.select_two_exact_fields constructs this exact
field equality before the third refinement; restriction preserves it. -/
theorem newY_eq_oldY {H Z : Type*} (mu : ℝ) (R : ℕ) (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (a : Label H k l) (H : F a.1=Fcfg (height a.1)) :
    newY mu R height F Fcfg a=oldY mu R height (oldIndex a) := by
  unfold newY errorMatrix
  rw [H,sub_self,recodedY_zero]
  rfl

theorem actualLabel_eq_coarsenLabel {H Z : Type*} (mu : ℝ) (R : ℕ) (hmu : 0 < mu)
    (height : H → Z) (F : H → Matrix (Fin l) (Fin k) ℝ)
    (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ) (a : Label H k l)
    (H : F a.1=Fcfg (height a.1)) :
    actualLabel mu R height F Fcfg a=coarsenLabel R height a := by
  unfold actualLabel
  rw [newY_eq_oldY mu R height F Fcfg a H]
  simp only [oldY,oldIndex,newX,coarsenLabel,coarseGrid_eq_ediv mu R hmu]

/-- Every full old height/Y fiber maps into ONE new Y label. -/
theorem old_fiber_maps_into_one_Y {H Z : Type*} [DecidableEq H]
    (L : Finset (Label H k l)) (mu : ℝ) (R : ℕ) (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (hField : ∀a∈L,F a.1=Fcfg (height a.1)) (b : H × Grid l) :
    ∀a∈FiniteCoarseYThresholdSelection.oldFiber L oldIndex b,
      newY mu R height F Fcfg a=oldY mu R height b := by
  intro a ha
  obtain ⟨haL,hab⟩ := mem_filter.mp ha
  rw [newY_eq_oldY mu R height F Fcfg a (hField a haL),hab]

/-- All fine X labels in an old fiber are retained. The only loss is the
proved exact R^k capacity of a coarse-X cell. -/
theorem old_fiber_coarseX_lower {H : Type*} [DecidableEq H]
    (L : Finset (Label H k l)) (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (hR : 0 < R)
    (b : H × Grid l) (Dmin : ℝ)
    (H : Dmin≤((FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).card:ℝ)) :
    Dmin/((R:ℝ)^k)≤
      (((FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).image (newX mu R)).card:ℝ) := by
  let S := FiniteCoarseYThresholdSelection.oldFiber L oldIndex b
  have hcap : (S.card:ℝ)≤((S.image (newX mu R)).card:ℝ)*((R:ℝ)^k) := by
    apply FinePointSlabGeometry.card_le_real_mul_of_fibers S (S.image (newX mu R)) (newX mu R)
      ((R:ℝ)^k) (fun a ha => mem_image_of_mem _ ha)
    intro q _hq
    exact_mod_cast old_fiber_capacity L mu R hmu hR b q
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(R:ℝ)^k)).2
  exact H.trans hcap

/-- No deletion: old and new supports are related by literal equality. -/
theorem exact_support {H Z : Type*} [DecidableEq H] [DecidableEq Z]
    (L : Finset (Label H k l)) (mu : ℝ) (R : ℕ) (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (H : ∀a∈L,F a.1=Fcfg (height a.1)) :
    (∀b∈L.image oldIndex,oldY mu R height b∈L.image (newY mu R height F Fcfg)) ∧
    (∀q∈L.image (newY mu R height F Fcfg),∃b∈L.image oldIndex,q=oldY mu R height b) := by
  constructor
  · intro b hb
    obtain ⟨a,ha,hab⟩ := mem_image.mp hb
    refine mem_image.mpr ⟨a,ha,?_⟩
    rw [newY_eq_oldY mu R height F Fcfg a (H a ha),hab]
  · intro q hq
    obtain ⟨a,ha,haq⟩ := mem_image.mp hq
    exact ⟨oldIndex a,mem_image_of_mem _ ha,haq.symm.trans (newY_eq_oldY mu R height F Fcfg a (H a ha))⟩

/-- Every occupied new Y contains the whole coarse-X image of one actual
old fiber. Distinct old heights need not have disjoint coarse-X images. -/
theorem newY_coarseX_lower {H Z : Type*} [DecidableEq H] [DecidableEq Z]
    (L : Finset (Label H k l)) (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (hR : 0 < R)
    (height : H → Z) (F : H → Matrix (Fin l) (Fin k) ℝ)
    (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (H : ∀a∈L,F a.1=Fcfg (height a.1)) (Dmin : ℝ)
    (hDense : ∀b∈L.image oldIndex,Dmin≤((FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).card:ℝ)) :
    ∀q∈L.image (newY mu R height F Fcfg),
      ∃b∈L.image oldIndex,q=oldY mu R height b ∧
        (∀a∈FiniteCoarseYThresholdSelection.oldFiber L oldIndex b,newY mu R height F Fcfg a=q) ∧
        Dmin/((R:ℝ)^k)≤(((L.filter (fun a => newY mu R height F Fcfg a=q)).image (newX mu R)).card:ℝ) := by
  intro q hq
  obtain ⟨b,hb,hqb⟩ := (exact_support L mu R height F Fcfg H).2 q hq
  have hwhole : ∀a∈FiniteCoarseYThresholdSelection.oldFiber L oldIndex b,
      newY mu R height F Fcfg a=q := by
    intro a ha
    exact (old_fiber_maps_into_one_Y L mu R height F Fcfg H b a ha).trans hqb.symm
  refine ⟨b,hb,hqb,hwhole,?_⟩
  have hsub : FiniteCoarseYThresholdSelection.oldFiber L oldIndex b⊆
      L.filter (fun a => newY mu R height F Fcfg a=q) := by
    intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp ha).1,hwhole a ha⟩
  exact (old_fiber_coarseX_lower L mu R hmu hR b Dmin (hDense b hb)).trans
    (Nat.cast_le.mpr (card_le_card (image_subset_image hsub)))

/-- The original edge itself is stored as witness; the entire I is tagged,
without filtering, uniformity assumptions, or a replacement incidence set. -/
def taggedEdges {E A : Type*} [DecidableEq E] [DecidableEq A]
    (I : Finset E) (label : E → A) : Finset (E × A) := I.image (fun e => (e,label e))

theorem taggedEdges_card {E A : Type*} [DecidableEq E] [DecidableEq A]
    (I : Finset E) (label : E → A) : (taggedEdges I label).card=I.card := by
  apply card_image_of_injective
  intro e f hef
  exact congrArg (fun z : E × A => z.1) hef

theorem taggedEdges_projection {E A : Type*} [DecidableEq E] [DecidableEq A]
    (I : Finset E) (label : E → A) : (taggedEdges I label).image Prod.fst=I := by
  simp [taggedEdges,image_image,Function.comp_def]

theorem tagged_point_fiber {E P A : Type*} [DecidableEq E] [DecidableEq P] [DecidableEq A]
    (I : Finset E) (point : E → P) (label : E → A) (p : P) :
    ((taggedEdges I label).filter (fun z => point z.1=p)).image Prod.fst=
      I.filter (fun e => point e=p) := by
  simp [taggedEdges,filter_image,image_image,Function.comp_def]

/-- Full unchanged-original-incidence endpoint. The input density is the
same old original-point fiber's DISTINCT fine-X image. Exact field values
are supplied by NativeExactHeightFields.select_two_exact_fields upstream;
no Q comparison, branch menu, or threshold selection is used here. -/
theorem actual_no_deletion_recoding {E P H Z : Type*}
    [DecidableEq E] [DecidableEq P] [DecidableEq H] [DecidableEq Z]
    (I : Finset E) (point : E → P) (fineHeight : P → H)
    (fineX : P → Grid k) (fineY : P → Grid l)
    (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (hR : 0 < R) (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (hExact : ∀p∈I.image point,F (fineHeight p)=Fcfg (height (fineHeight p)))
    (Dmin : ℝ)
    (hDense : ∀b∈(I.image ((pointLabel fineHeight fineX fineY)∘point)).image oldIndex,
      Dmin≤((fineXCells I point fineHeight fineX fineY b).card:ℝ)) :
    let label := (pointLabel fineHeight fineX fineY)∘point
    let L := I.image label
    let recode := fun e => actualLabel mu R height F Fcfg (label e)
    (∀e∈I,recode e=coarsenLabel R height (label e)) ∧
    (taggedEdges I recode).card=I.card ∧
    (taggedEdges I recode).image Prod.fst=I ∧
    (∀p,((taggedEdges I recode).filter (fun z => point z.1=p)).image Prod.fst=I.filter (fun e => point e=p)) ∧
    (∀b∈L.image oldIndex,oldY mu R height b∈L.image (newY mu R height F Fcfg)) ∧
    (∀q∈L.image (newY mu R height F Fcfg),∃b∈L.image oldIndex,q=oldY mu R height b ∧
      (∀a∈FiniteCoarseYThresholdSelection.oldFiber L oldIndex b,newY mu R height F Fcfg a=q) ∧
      Dmin/((R:ℝ)^k)≤(((L.filter (fun a => newY mu R height F Fcfg a=q)).image (newX mu R)).card:ℝ)) := by
  intro label L recode
  have hExactL : ∀a∈L,F a.1=Fcfg (height a.1) := by
    intro a ha
    obtain ⟨e,he,rfl⟩ := mem_image.mp ha
    exact hExact (point e) (mem_image_of_mem _ he)
  have hDenseL : ∀b∈L.image oldIndex,Dmin≤((FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).card:ℝ) := by
    intro b hb
    change Dmin≤((FiniteCoarseYThresholdSelection.oldFiber
      (I.image ((pointLabel fineHeight fineX fineY)∘point)) oldIndex b).card:ℝ)
    rw [old_label_fiber_card]
    exact hDense b hb
  refine ⟨?_,taggedEdges_card I recode,taggedEdges_projection I recode,
    tagged_point_fiber I point recode,(exact_support L mu R height F Fcfg hExactL).1,
    newY_coarseX_lower L mu R hmu hR height F Fcfg hExactL Dmin hDenseL⟩
  intro e he
  exact actualLabel_eq_coarsenLabel mu R hmu height F Fcfg (label e)
    (hExact (point e) (mem_image_of_mem _ he))

end ExactHeightNoDeletionRecoding
