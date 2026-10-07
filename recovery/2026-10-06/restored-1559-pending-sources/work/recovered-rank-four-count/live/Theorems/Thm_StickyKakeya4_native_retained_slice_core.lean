import Theorems.Thm_StickyKakeya4_native_retained_slice_count_transfer
import Theorems.Thm_StickyKakeya4_native_local_pair_uniform_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeRetainedSliceCore
open Classical Finset SelfUniform NativeJointUniformCoarseRelations
open NativeRetainedSliceCountTransfer NativeLocalPairUniformCore

/-- Extra grain/quotient relations share the same original-incidence core
with finest point equality and the finite horizontal class equalities. -/
def relations {A X Y : Type*} {d K : ℕ}
    (point : A  →  X) (classes : Fin K  →  X  →  Y) (Rel : Fin d  →  A  →  A  →  Prop) :
    Fin (d+(1+K))  →  A  →  A  →  Prop :=
  Fin.addCases Rel (Fin.addCases (fun _ : Fin 1 => fun x y => point x=point y)
    (fun j x y => classes j (point x)=classes j (point y)))

def refinementCost (d K L : ℕ) : ℕ := retentionCost (d+(1+K)) 0 L

lemma refinementCost_pos (d K L : ℕ) : 0<refinementCost d K L := by
  unfold refinementCost retentionCost
  positivity

lemma relations_refl {A X Y : Type*} {d K : ℕ}
    (point : A  →  X) (classes : Fin K  →  X  →  Y) (Rel : Fin d  →  A  →  A  →  Prop)
    (hrefl : ∀j x,Rel j x x) : ∀j x,relations point classes Rel j x x := by
  intro j x
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa only [relations,Fin.addCases_left] using hrefl i x
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simp only [relations,Fin.addCases_right,Fin.addCases_left]
    · intro k
      simp only [relations,Fin.addCases_right]

lemma relations_symm {A X Y : Type*} {d K : ℕ}
    (point : A  →  X) (classes : Fin K  →  X  →  Y) (Rel : Fin d  →  A  →  A  →  Prop)
    (hsym : ∀j x y,Rel j x y → Rel j y x) :
    ∀j x y,relations point classes Rel j x y → relations point classes Rel j y x := by
  intro j x y
  refine Fin.addCases ?_ ?_ j
  · intro i hh
    simp only [relations,Fin.addCases_left] at hh ⊢
    exact hsym i x y hh
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro k hh
      simp only [relations,Fin.addCases_right,Fin.addCases_left] at hh ⊢
      exact hh.symm
    · intro k hh
      simp only [relations,Fin.addCases_right] at hh ⊢
      exact hh.symm

/-- Construct a genuine third incidence refinement of the already cleaned
set. The weight of every original label is still one; points are never
uniformized after forgetting their original incidence weights. -/
theorem exists_retained_slice_core {A X Y : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y] {d K : ℕ}
    (H : Finset A) (hHn : H.Nonempty) (point : A  →  X) (classes : Fin K  →  X  →  Y)
    (Rel : Fin d  →  A  →  A  →  Prop) (hrefl : ∀j x,Rel j x x)
    (hsym : ∀j x y,Rel j x y → Rel j y x) (L : ℕ) (hL : 0<L) :
    let Q := NativeSourceSizeBounds.radix H.card L
    ∃T⊆H,T.Nonempty ∧ H.card ≤ refinementCost d K L*T.card ∧
      (∀j x y,x∈T → y∈T → degree (fun _ : A => 1) (Rel j) T x ≤
        Q^2*degree (fun _ : A => 1) (Rel j) T y) ∧
      HasUniformFibers T Q point ∧
      ∀j,HasUniformFibers T Q (fun z => classes j (point z)) := by
  intro Q
  have hQ4 : 4 ≤ Q := NativeSourceSizeBounds.radix_four_le _ _
  have hheight : mass (fun _ : A => 1) H ≤ Q^L := by
    simpa only [mass,sum_const,nsmul_eq_mul,mul_one,Nat.cast_id,Q] using
      NativeSourceSizeBounds.card_le_radix_pow H.card hL
  obtain ⟨T,hTH,hTn,hret,hUniform⟩ := weighted_self_uniform_refinement
    (by omega : 0<d+(1+K)) hQ4 (fun _ : A => 1) (relations point classes Rel)
    (relations_refl point classes Rel hrefl) (relations_symm point classes Rel hsym)
    H hHn (fun _ _ => by norm_num) hheight
  refine ⟨T,hTH,hTn,?_,?_,?_,?_⟩
  · simpa only [mass,sum_const,nsmul_eq_mul,mul_one,refinementCost,retentionCost,Nat.add_zero,Nat.cast_id] using hret
  · intro j x y hx hy
    simpa only [relations,Fin.addCases_left] using hUniform (Fin.castAdd (1+K) j) x y hx hy
  · intro x hx y hy
    simpa only [relations,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using
      hUniform (Fin.natAdd d (Fin.castAdd K (0:Fin 1))) x y hx hy
  · intro j x hx y hy
    simpa only [relations,Fin.addCases_right,unit_degree_eq_fiber] using
      hUniform (Fin.natAdd d (Fin.natAdd 1 j)) x y hx hy

/-- Reference fine/coarse count ratios become lower bounds in every occupied
class of the constructed post-cut set. Original incidence retention is paid
explicitly, and reference local upper bounds pass through literal inclusion. -/
theorem exists_retained_slice_counts {A X Y : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y] {d K : ℕ}
    (I H : Finset A) (hHI : H⊆I) (hHn : H.Nonempty)
    (point : A  →  X) (classes : Fin K  →  X  →  Y) (Qref : ℕ)
    (HRef : HasUniformFibers I Qref point)
    (lambda G : ℝ) (hlambda : 0 ≤ lambda) (hG : 0 ≤ G)
    (hret : lambda*(I.card:ℝ) ≤ G*H.card)
    (lower : Fin K  →  ℝ)
    (hRatio : ∀j,lower j*((I.image point).image (classes j)).card ≤ (I.image point).card)
    (Rel : Fin d  →  A  →  A  →  Prop) (hrefl : ∀j x,Rel j x x)
    (hsym : ∀j x y,Rel j x y → Rel j y x) (L : ℕ) (hL : 0<L) :
    let Q := NativeSourceSizeBounds.radix H.card L
    ∃T⊆H,T.Nonempty ∧ H.card ≤ refinementCost d K L*T.card ∧
      (∀j x y,x∈T → y∈T → degree (fun _ : A => 1) (Rel j) T x ≤
        Q^2*degree (fun _ : A => 1) (Rel j) T y) ∧
      HasUniformFibers T Q point ∧
      (∀j,HasUniformFibers T Q (fun z => classes j (point z))) ∧
      lambda*(I.image point).card ≤
        G*(refinementCost d K L:ℝ)*(Qref:ℝ)^2*(T.image point).card ∧
      ∀j t,t∈(T.image point).image (classes j)  → 
        lambda*lower j ≤ G*(refinementCost d K L:ℝ)*(Qref:ℝ)^2*(Q:ℝ)^4*
          ((T.image point).filter (fun z => classes j z=t)).card ∧
        ((T.image point).filter (fun z => classes j z=t)).card ≤
          ((I.image point).filter (fun z => classes j z=t)).card := by
  intro Q
  obtain ⟨T,hTH,hTn,hcost,hRel,hPoint,hClass⟩ :=
    exists_retained_slice_core H hHn point classes Rel hrefl hsym L hL
  have hTI := hTH.trans hHI
  have hIn := hHn.mono hHI
  have hcostR : (H.card:ℝ) ≤ (refinementCost d K L:ℝ)*T.card := by exact_mod_cast hcost
  have hretT : lambda*(I.card:ℝ) ≤ (G*(refinementCost d K L:ℝ))*T.card := by
    exact hret.trans ((mul_le_mul_of_nonneg_left hcostR hG).trans_eq (by ring))
  have hGC : 0 ≤ G*(refinementCost d K L:ℝ) := mul_nonneg hG (Nat.cast_nonneg _)
  refine ⟨T,hTH,hTn,hcost,hRel,hPoint,hClass,?_,?_⟩
  · exact point_image_retention I T hTI hIn point Qref HRef lambda _ hGC hretT
  · intro j t ht
    exact ⟨retained_class_count_lower I T hTI hIn point (classes j) Qref Q HRef hPoint (hClass j)
        lambda _ (lower j) hlambda hGC hretT (hRatio j) t ht,
      (retained_class_count_cross I T hTI hIn point (classes j) Qref Q HRef hPoint (hClass j)
        lambda _ hGC hretT t ht).2⟩

end NativeRetainedSliceCore
