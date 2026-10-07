import Theorems.Thm_StickyKakeya4_native_grain_quotient_bins

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeOffsetMenuCount
open Classical Finset NativeGrainQuotientBins
open scoped BigOperators

/-- The actual distinct offset/angular incidence image. Counting this image
never counts a repeated source incidence as a new angular direction. -/
def pairImage {A B C : Type*} [DecidableEq B] [DecidableEq C]
    (S : Finset A) (off : A → B) (angle : A → C) : Finset (B × C) :=
  S.image (fun z => (off z,angle z))

lemma right_fiber_card {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (S : Finset A) (off : A → B) (angle : A → C) (c : C) :
    ((pairImage S off angle).filter (fun z => z.2=c)).card=
      ((S.filter (fun z => angle z=c)).image off).card := by
  have hinj : Set.InjOn (fun z : B × C => z.1) ((pairImage S off angle).filter (fun z => z.2=c)) := by
    intro x hx y hy hxy
    exact Prod.ext hxy ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  rw [←card_image_of_injOn hinj]
  congr 1
  ext b
  simp only [mem_image,mem_filter,pairImage]
  constructor
  · rintro ⟨v,⟨⟨z,hz,rfl⟩,hc⟩,rfl⟩
    exact ⟨z,⟨hz,hc⟩,rfl⟩
  · rintro ⟨z,⟨hz,hc⟩,rfl⟩
    exact ⟨(off z,angle z),⟨⟨z,hz,rfl⟩,hc⟩,rfl⟩

/-- Each occupied offset has a point with d actual angular choices. If one
angular label supports at most C offsets, d times the number of offsets is
bounded by C times the total angular union. -/
theorem offset_count_from_point_menus {A X B C : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq B] [DecidableEq C]
    (S : Finset A) (point : A → X) (offset : X → B) (angle : A → C)
    (d cap : ℝ)
    (hlower : ∀x∈S.image point,d ≤ ((S.filter (fun z => point z=x)).image angle).card)
    (hupper : ∀c,(((S.filter (fun z => angle z=c)).image (fun z => offset (point z))).card:ℝ) ≤ cap) :
    d*((S.image (fun z => offset (point z))).card:ℝ) ≤ cap*(S.image angle).card := by
  let off := fun z => offset (point z)
  let J := pairImage S off angle
  have hleft (b : B) (hb : b∈S.image off) :
      d ≤ ((J.filter (fun z => z.1=b)).card:ℝ) := by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hb
    have hlo := hlower (point z) (mem_image_of_mem _ hz)
    let V := (S.filter (fun t => point t=point z)).image angle
    have hV : V.image (fun c => (off z,c))⊆J.filter (fun t => t.1=off z) := by
      intro v hv
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hv
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hc
      obtain ⟨ht,hpt⟩ := mem_filter.mp ht
      have ho : off t=off z := congrArg offset hpt
      exact mem_filter.mpr ⟨mem_image.mpr ⟨t,ht,Prod.ext ho rfl⟩,rfl⟩
    have hi : Set.InjOn (fun c : C => (off z,c)) V := by
      intro x _ y _ hxy
      exact congrArg Prod.snd hxy
    have hh := card_le_card hV
    rw [card_image_of_injOn hi] at hh
    exact hlo.trans (Nat.cast_le.mpr hh)
  have hJL : J.image Prod.fst=S.image off := by
    simp only [J,pairImage,image_image,Function.comp_def]
  have hJR : J.image Prod.snd=S.image angle := by
    simp only [J,pairImage,image_image,Function.comp_def]
  have hsumL : (J.card:ℝ)=∑b∈S.image off,((J.filter (fun z => z.1=b)).card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image Prod.fst J).trans (by rw [hJL])
  have hsumR : (J.card:ℝ)=∑c∈S.image angle,((J.filter (fun z => z.2=c)).card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image Prod.snd J).trans (by rw [hJR])
  calc
    _ = ∑_b∈S.image off,d := by simp; ring
    _ ≤ J.card := by rw [hsumL]; exact sum_le_sum hleft
    _ = ∑c∈S.image angle,((J.filter (fun z => z.2=c)).card:ℝ) := hsumR
    _ ≤ ∑_c∈S.image angle,cap := by
      apply sum_le_sum
      intro c _
      simpa only [J,right_fiber_card] using hupper c
    _ = _ := by simp; ring

/-- Geometric overlap supplies the cap in the preceding double count.
For bins at their actual diameter H, each angular label meets at most4^d
anchor bins. The original point fibers, not normalized witness laws, are used. -/
theorem geometric_offset_count {A X C : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq C]
    {dim : ℕ} (S : Finset A) (point : A → X) (xi : X → EuclideanSpace ℝ (Fin dim))
    (angle : A → C) (H : ℝ) (hH : 0 < H) (d : ℝ)
    (hlower : ∀x∈S.image point,d ≤ ((S.filter (fun z => point z=x)).image angle).card)
    (hclose : ∀z∈S,∀w∈S,angle z=angle w → ‖xi (point z)-xi (point w)‖ ≤ H) :
    d*((S.image (fun z => label H (xi (point z)))).card:ℝ) ≤
      (4:ℝ)^dim*(S.image angle).card := by
  apply offset_count_from_point_menus S point (fun x => label H (xi x)) angle d ((4:ℝ)^dim) hlower
  intro c
  by_cases hc : (S.filter (fun z => angle z=c)).Nonempty
  · obtain ⟨z,hz⟩ := hc
    have hbound := occupied_card (S.filter (fun z => angle z=c)) (fun w => xi (point w))
      hH hH.le (xi (point z)) (fun w hw => hclose w (mem_filter.mp hw).1 z (mem_filter.mp hz).1
        ((mem_filter.mp hw).2.trans (mem_filter.mp hz).2.symm))
    simpa only [mul_div_cancel_right₀ _ hH.ne',show (2:ℝ)+2=4 by norm_num] using hbound
  · rw [not_nonempty_iff_eq_empty.mp hc]
    simp only [image_empty,card_empty,Nat.cast_zero]
    positivity

/-- A whole-point-fiber selection with the exact original-edge retention.
Consequently every surviving point retains its full angular menu. -/
theorem exists_coherent_offset_core {A X C : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq C]
    {dim : ℕ} (S : Finset A) (hS : S.Nonempty) (point : A → X)
    (xi : X → EuclideanSpace ℝ (Fin dim)) (angle : A → C) (H : ℝ) (hH : 0 < H)
    (d : ℝ) (hd : 0 < d)
    (hlower : ∀x∈S.image point,d ≤ ((S.filter (fun z => point z=x)).image angle).card)
    (hclose : ∀z∈S,∀w∈S,angle z=angle w → ‖xi (point z)-xi (point w)‖ ≤ H) :
    ∃z∈S,let T := S.filter (fun w => label H (xi (point w))=label H (xi (point z)))
      T.Nonempty ∧ d*S.card ≤ (4:ℝ)^dim*(S.image angle).card*T.card ∧
      (∀w∈T,∀u∈S,point u=point w → u∈T) := by
  have hc := geometric_offset_count S point xi angle H hH d hlower hclose
  obtain ⟨z,hz,hT,hcard⟩ := exists_dense_fiber S hS (fun z => label H (xi (point z)))
    (((4:ℝ)^dim*(S.image angle).card)/d) ((le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hc))
  refine ⟨z,hz,hT,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hcard hd.le
    field_simp at hh
    nlinarith only [hh]
  · intro w hw u hu he
    apply mem_filter.mpr
    refine ⟨hu,?_⟩
    rw [he]
    exact (mem_filter.mp hw).2

end NativeOffsetMenuCount
