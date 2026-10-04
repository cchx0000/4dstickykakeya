import Theorems.Thm_StickyKakeya4_native_unit_parent_normalization
import Theorems.Thm_StickyKakeya4_native_dyadic_parent_cells
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeUnitParentDyadic
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeUnitParentNormalization NativeDyadicParentCells
open scoped BigOperators

def projection (p : Parent) (N : ℕ) (z : Parent) : Parent :=
  (fun j => z.1 j-(N:ℤ)*p.1 j,fun j => (z.2 j-(N:ℤ)*p.2 j)/4)
def parameterLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent) (N : ℕ)
    (i : Fin n) : Parent :=
  (fun j => ⌊(N:ℝ)*newSlope (D.line i) p j⌋,
    fun j => ⌊(N:ℝ)*newIntercept (D.line i) (mesh D) (shift D a) p j⌋)
def projectionBox (p : Parent) (N : ℕ) (q : Parent) : Finset Parent :=
  {fun j => q.1 j+(N:ℤ)*p.1 j} ×ˢ
    Fintype.piFinset (fun j => Icc (4*q.2 j+(N:ℤ)*p.2 j) (4*q.2 j+(N:ℤ)*p.2 j+3))

lemma floor_sub_integer_mul (x : ℝ) (N : ℕ) (k : ℤ) :
    ⌊(N:ℝ)*(x-k)⌋=⌊(N:ℝ)*x⌋-(N:ℤ)*k := by
  have he : (N:ℝ)*(x-k)=(N:ℝ)*x-((N:ℤ)*k:ℤ) := by push_cast; ring
  rw [he,Int.floor_sub_intCast]

/-- Exact integer shear and dilation formula, valid at EVERY dyadic level,
including the unit and half-unit ancestors. -/
lemma parameterLabel_eq_projection {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (p : Parent) (N : ℕ) (i : Fin n) :
    parameterLabel D a p N i=projection p N (parentLabel D a N i) := by
  apply Prod.ext
  · funext j
    exact floor_sub_integer_mul _ _ _
  · funext j
    change ⌊(N:ℝ)*((shiftedIntercept (D.line i) (mesh D) (shift D a) j-(p.2 j:ℝ))/4)⌋ = _
    rw [←mul_div_assoc]
    have hh := Int.floor_div_natCast ((N:ℝ)*(shiftedIntercept (D.line i) (mesh D) (shift D a) j-(p.2 j:ℝ))) 4
    norm_num only [Nat.cast_ofNat] at hh
    rw [hh,floor_sub_integer_mul]
    rfl

lemma projection_mem_box (p : Parent) (N : ℕ) (z q : Parent) (h : projection p N z=q) :
    z ∈ projectionBox p N q := by
  apply mem_product.mpr
  constructor
  · apply mem_singleton.mpr
    funext j
    have hh := congrFun (congrArg Prod.fst h) j
    dsimp [projection] at hh
    omega
  · apply Fintype.mem_piFinset.mpr
    intro j
    have hh := congrFun (congrArg Prod.snd h) j
    dsimp [projection] at hh
    apply mem_Icc.mpr
    omega

lemma projectionBox_card (p : Parent) (N : ℕ) (q : Parent) : (projectionBox p N q).card=64 := by
  have hi (j : Fin 3) : (Icc (4*q.2 j+(N:ℤ)*p.2 j) (4*q.2 j+(N:ℤ)*p.2 j+3)).card=4 := by
    have hh : ((Icc (4*q.2 j+(N:ℤ)*p.2 j) (4*q.2 j+(N:ℤ)*p.2 j+3)).card:ℤ)=4 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp [projectionBox,Fintype.card_piFinset,hi]

/-- The actual new parameter cube is a union of at most64 original parameter
cubes. Every occupied new cube contains an entire occupied original cube. -/
theorem parameter_fiber_bounds {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (p : Parent) (N : ℕ) {L U : ℝ} (hU : 0 ≤ U)
    (H : ∀z, (R.filter (fun i=>parentLabel D a N i=z)).Nonempty →
      L ≤ ((R.filter (fun i=>parentLabel D a N i=z)).card:ℝ) ∧
      ((R.filter (fun i=>parentLabel D a N i=z)).card:ℝ) ≤ U)
    (q : Parent) (hq : (R.filter (fun i=>parameterLabel D a p N i=q)).Nonempty) :
    L ≤ ((R.filter (fun i=>parameterLabel D a p N i=q)).card:ℝ) ∧
      ((R.filter (fun i=>parameterLabel D a p N i=q)).card:ℝ) ≤ 64*U := by
  let S := R.filter (fun i=>parameterLabel D a p N i=q)
  obtain ⟨i,hi⟩ := hq
  have hip : projection p N (parentLabel D a N i)=q := by
    rw [←parameterLabel_eq_projection]
    exact (mem_filter.mp hi).2
  have hold : R.filter (fun k=>parentLabel D a N k=parentLabel D a N i) ⊆ S := by
    intro k hk
    refine mem_filter.mpr ⟨(mem_filter.mp hk).1,?_⟩
    rw [parameterLabel_eq_projection,(mem_filter.mp hk).2]
    exact hip
  have hlow := (H _ ⟨i,mem_filter.mpr ⟨(mem_filter.mp hi).1,rfl⟩⟩).1
  have hbox : S.image (parentLabel D a N) ⊆ projectionBox p N q := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    apply projection_mem_box
    rw [←parameterLabel_eq_projection]
    exact (mem_filter.mp hk).2
  have hc : ((S.image (parentLabel D a N)).card:ℝ) ≤ 64 := by
    exact_mod_cast (card_le_card hbox).trans_eq (projectionBox_card p N q)
  refine ⟨hlow.trans (by exact_mod_cast card_le_card hold),?_⟩
  have hs : (S.card:ℝ)=∑z∈S.image (parentLabel D a N),
      ((S.filter (fun i=>parentLabel D a N i=z)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image (parentLabel D a N) S
  change (S.card:ℝ) ≤ 64*U
  rw [hs]
  calc
    _ ≤ ∑_z∈S.image (parentLabel D a N),U := by
      apply sum_le_sum
      intro z hz
      obtain ⟨k,hk,hkz⟩ := mem_image.mp hz
      have hu := (H z ⟨k,mem_filter.mpr ⟨(mem_filter.mp hk).1,hkz⟩⟩).2
      exact (show ((S.filter (fun i=>parentLabel D a N i=z)).card:ℝ) ≤ 
        (R.filter (fun i=>parentLabel D a N i=z)).card by
          exact_mod_cast card_le_card (filter_subset_filter _ (filter_subset _ _))).trans hu
    _ = ((S.image (parentLabel D a N)).card:ℝ)*U := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hU

/-- Restriction to an entire original unit parent preserves every occupied
finer original ancestor, exactly, on the same original labels. -/
lemma unit_parent_fiber_eq {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (p : Parent) (ell : ℕ) (q : Parent)
    (hne : ((R.filter (fun i=>parentLabel D a 1 i=p)).filter
      (fun i=>parentLabel D a (2^ell) i=q)).Nonempty) :
    (R.filter (fun i=>parentLabel D a 1 i=p)).filter (fun i=>parentLabel D a (2^ell) i=q)=
      R.filter (fun i=>parentLabel D a (2^ell) i=q) := by
  obtain ⟨i,hi⟩ := hne
  have hqp : ancestor ell 0 q=p := by
    rw [←(mem_filter.mp hi).2,parent_ancestor_eq D a (Nat.zero_le ell) i]
    simpa only [pow_zero] using (mem_filter.mp (mem_filter.mp hi).1).2
  ext k
  constructor
  · intro hk
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hk).1).1,(mem_filter.mp hk).2⟩
  · intro hk
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hk).1,?_⟩,(mem_filter.mp hk).2⟩
    have he := parent_ancestor_eq D a (Nat.zero_le ell) k
    rw [(mem_filter.mp hk).2,hqp] at he
    simpa only [pow_zero] using he.symm
end NativeUnitParentDyadic
