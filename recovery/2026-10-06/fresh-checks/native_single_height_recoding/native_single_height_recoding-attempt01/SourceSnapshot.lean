import Theorems.Thm_StickyKakeya4_native_frozen_time_field
import Theorems.Thm_StickyKakeya4_native_matrix_height_interface

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeSingleHeightRecoding
open Classical Finset NativeMatrixHeightWholePoint NativeFrozenTimeField

/-- The true old-height residue in one coarse time bin. -/
def heightColor (N : ℕ) (hN : 0<N) (z : ℤ) : Fin N :=
  ⟨(z%(N:ℤ)).toNat,by omega⟩

/-- Keep one ORIGINAL fine height in every retained coarse bin. This is a
weighted source selection, not the creation of a new time or point. -/
theorem select_one_old_height {P : Type*} (S : Finset P) (w : P → ℕ)
    (height : P → ℤ) (N : ℕ) (hN : 0<N) :
    ∃T⊆S,mass S w≤N*mass T w ∧
      ∀p∈T,∀q∈T,height p/(N:ℤ)=height q/(N:ℤ) → height p=height q := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  obtain ⟨chi,hsub,_hlocal,hret,hcoh⟩ := select_color_per_cell S w
    (fun p => height p/(N:ℤ)) (fun p => heightColor N hN (height p))
  refine ⟨S.filter (fun p => heightColor N hN (height p)=chi (height p/(N:ℤ))),hsub,?_,?_⟩
  · simpa only [Fintype.card_fin] using hret
  · intro p hp q hq he
    have hc := congrArg Fin.val (hcoh p hp q hq he)
    dsimp only [heightColor] at hc
    have hh := Int.emod_add_mul_ediv (height p) (N:ℤ)
    have hk := Int.emod_add_mul_ediv (height q) (N:ℤ)
    omega

/-- Literal midpoint time-grid readback; negative original heights are
included. The physical grid spacing is a caller-supplied source coordinate. -/
lemma coarse_height_readback (mu : ℝ) (hmu : 0<mu) (N : ℕ) (z : ℤ) :
    ⌊(mu*((z:ℝ)+1/2))/(mu*(N:ℝ))⌋=z/(N:ℤ) := by
  rw [mul_div_mul_left _ _ hmu.ne',Int.floor_div_natCast,Int.floor_intCast_add]
  norm_num

/-- The height cut is realized on the unchanged old edge set. Both lower
and higher fields factoring through old height are constant in every new bin,
without imposing Lipschitz continuity on the higher field. -/
theorem select_original_edges {E P U V : Type*} [DecidableEq P]
    (A : Finset E) (point : E → P) (height : P → ℤ)
    (F : ℤ → U) (G : ℤ → V) (N : ℕ) (hN : 0<N) :
    ∃B⊆A.image point,let T:=edgeLift A point B
      T⊆A ∧ A.card≤N*T.card ∧
      (∀p∈B,T.filter (fun e => point e=p)=A.filter (fun e => point e=p)) ∧
      ∀e∈T,∀f∈T,height (point e)/(N:ℤ)=height (point f)/(N:ℤ) →
        height (point e)=height (point f) ∧
        F (height (point e))=F (height (point f)) ∧
        G (height (point e))=G (height (point f)) := by
  let w := fun p => (A.filter (fun e => point e=p)).card
  obtain ⟨B,hB,hret,hheight⟩ := select_one_old_height (A.image point) w height N hN
  have hmass : mass (A.image point) w=A.card := by
    exact (edgeLift_card A point (A.image point) (Subset.refl _)).symm.trans (by
      congr 1
      ext e
      simp only [edgeLift,mem_filter,mem_image]
      aesop)
  have hmassB := edgeLift_card A point B hB
  refine ⟨B,hB,filter_subset _ _,?_,fun p hp => edgeLift_fiber A point B hp,?_⟩
  · rw [←hmass,←hmassB]
    exact hret
  · intro e he f hf hab
    have hh := hheight (point e) (mem_filter.mp he).2 (point f) (mem_filter.mp hf).2 hab
    exact ⟨hh,congrArg F hh,congrArg G hh⟩

/-- All sampled fields use the SAME pre-refinement representative.
Pointwise matrix consistency is therefore preserved on every occupied bin. -/
theorem frozen_matrix_consistency {P : Type*} {a b c : ℕ}
    (S : Finset P) (height : P → ℝ) (delta : ℝ)
    (F1 : P → Matrix (Fin b) (Fin a) ℝ)
    (F2 G1 : P → Matrix (Fin c) (Fin a) ℝ)
    (G2 : P → Matrix (Fin c) (Fin b) ℝ)
    (H : ∀p∈S,F2 p=G1 p+G2 p*F1 p)
    {z : ℤ} (hz : ∃p∈S,⌊height p/delta⌋=z) :
    field S height F2 delta z=field S height G1 delta z+
      field S height G2 delta z*field S height F1 delta z := by
  simp only [field,dif_pos hz]
  exact H (Classical.choose hz) (Classical.choose_spec hz).1

end NativeSingleHeightRecoding
