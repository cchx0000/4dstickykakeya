import Theorems.Thm_StickyKakeya4_native_incidence_multiplicity_tower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

noncomputable section
namespace NativeParentAverageUniformity
open Classical Finset NativeIncidenceMultiplicityTower
open scoped BigOperators

/-- Uniform point-fiber counts compare their exact incidence/support means. -/
lemma multiplicity_le_of_fiber_comparison {T X : Type*} [DecidableEq X]
    (A B : Finset (T × X)) (hA : A.Nonempty) (hB : B.Nonempty) (K : ℕ)
    (H : ∀x∈A.image Prod.snd,∀y∈B.image Prod.snd,
      (A.filter (fun z => z.2=x)).card ≤ K*(B.filter (fun z => z.2=y)).card) :
    multiplicity A ≤ (K:ℝ)*multiplicity B := by
  have hAc := card_eq_sum_card_image Prod.snd A
  have hBc := card_eq_sum_card_image Prod.snd B
  have hx : ∀x∈A.image Prod.snd,
      (A.filter (fun z => z.2=x)).card*(B.image Prod.snd).card ≤ K*B.card := by
    intro x hxm
    calc
      _ = ∑_y∈B.image Prod.snd,(A.filter (fun z => z.2=x)).card := by simp [Nat.mul_comm]
      _ ≤ ∑y∈B.image Prod.snd,K*(B.filter (fun z => z.2=y)).card :=
        sum_le_sum (fun y hy => H x hxm y hy)
      _ = _ := by rw [←mul_sum,←hBc]
  have hcross : A.card*(B.image Prod.snd).card ≤ K*B.card*(A.image Prod.snd).card := by
    calc
      _ = ∑x∈A.image Prod.snd,(A.filter (fun z => z.2=x)).card*(B.image Prod.snd).card := by
        rw [←sum_mul,←hAc]
      _ ≤ ∑_x∈A.image Prod.snd,K*B.card := sum_le_sum hx
      _ = _ := by simp [Nat.mul_comm]
  have hAr : (0:ℝ)<(A.image Prod.snd).card := by exact_mod_cast card_pos.mpr (hA.image Prod.snd)
  have hBr : (0:ℝ)<(B.image Prod.snd).card := by exact_mod_cast card_pos.mpr (hB.image Prod.snd)
  have hcrossR : (A.card:ℝ)*(B.image Prod.snd).card ≤ (K:ℝ)*B.card*(A.image Prod.snd).card := by
    exact_mod_cast hcross
  unfold NativeIncidenceMultiplicityTower.multiplicity
  rw [←mul_div_assoc]
  exact (div_le_div_iff₀ hAr hBr).mpr hcrossR

/-- Equality of the formal parent/fine-point label is exactly the corresponding
point fiber inside its original parent. -/
lemma formal_pair_fiber {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (E : Finset (T × X)) (f : T → P) (p : P) (x : T × X)
    (hx : x∈parent E f p) :
    E.filter (fun z => (f z.1,z.2)=(f x.1,x.2)) =
      (parent E f p).filter (fun z => z.2=x.2) := by
  have hp : f x.1=p := (mem_filter.mp hx).2
  ext z
  simp only [mem_filter,parent,Prod.mk.injEq,hp,and_assoc]

/-- Appending the original formal parent-point equality relation before the
single uniformization makes every active parent average comparable. R and E
remain unchanged, and no parent-average certificate is assumed. -/
theorem parent_multiplicity_le {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (E : Finset (T × X)) (f : T → P) (rad : ℕ)
    (H : ∀x∈E,∀y∈E,
      (E.filter (fun z => (f z.1,z.2)=(f x.1,x.2))).card ≤
        rad^2*(E.filter (fun z => (f z.1,z.2)=(f y.1,y.2))).card)
    (p : P) (hp : (parent E f p).Nonempty)
    (q : P) (hq : (parent E f q).Nonempty) :
    multiplicity (parent E f p) ≤ (rad:ℝ)^2*multiplicity (parent E f q) := by
  have hh := multiplicity_le_of_fiber_comparison (parent E f p) (parent E f q) hp hq (rad^2)
  apply (by simpa only [Nat.cast_pow] using hh)
  intro x hx y hy
  obtain ⟨e,he,rfl⟩ := mem_image.mp hx
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hy
  have h := H e (mem_filter.mp he).1 w (mem_filter.mp hw).1
  rwa [formal_pair_fiber E f p e he,formal_pair_fiber E f q w hw] at h

end NativeParentAverageUniformity
