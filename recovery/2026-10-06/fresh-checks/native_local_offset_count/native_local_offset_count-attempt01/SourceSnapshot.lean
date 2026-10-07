import Theorems.Thm_StickyKakeya4_native_local_offset_geometry
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
noncomputable section

namespace NativeLocalOffsetCount
open Classical Finset NativeLocalOffsetGeometry
open scoped BigOperators

def offsetCell {ell : ℕ} (w : ℝ) (xi : Fin ell → ℝ) : Fin ell → ℤ :=
  fun i => ⌊xi i/w⌋

def neighbors {ell : ℕ} (c : Fin ell → ℤ) : Finset (Fin ell → ℤ) :=
  Fintype.piFinset (fun i => Icc (c i-1) (c i+1))

lemma neighbors_card {ell : ℕ} (c : Fin ell → ℤ) : (neighbors c).card=3^ell := by
  have hi (i : Fin ell) : (Icc (c i-1) (c i+1)).card=3 := by
    have hh : ((Icc (c i-1) (c i+1)).card:ℤ)=3 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp [neighbors,Fintype.card_piFinset,hi]

lemma floor_difference_le_one {w x y : ℝ} (hw : 0 < w) (h : |x-y| ≤ w) :
    ⌊y/w⌋-1 ≤ ⌊x/w⌋ ∧ ⌊x/w⌋ ≤ ⌊y/w⌋+1 := by
  have hd : |x/w-y/w| ≤ 1 := by
    rw [←sub_div,abs_div,abs_of_pos hw]
    exact (div_le_one hw).mpr h
  have hlo := Int.floor_mono (show y/w-1 ≤ x/w by have hh := abs_le.mp hd; linarith)
  have hhi := Int.floor_mono (show x/w ≤ y/w+1 by have hh := abs_le.mp hd; linarith)
  rw [Int.floor_sub_one] at hlo
  rw [Int.floor_add_one] at hhi
  exact ⟨hlo,hhi⟩

/-- Exact finite readback for the actual image of a pair of labels. -/
lemma joint_fiber_card {Z X Y : Type*} (S : Finset Z) (f : Z → X) (g : Z → Y) (c : X) :
    ((S.image (fun z => (f z,g z))).filter (fun v => v.1=c)).card=
      ((S.filter (fun z => f z=c)).image g).card := by
  apply card_bij (fun v _ => v.2)
  · intro v hv
    obtain ⟨hvS,hvc⟩ := mem_filter.mp hv
    obtain ⟨z,hz,hzv⟩ := mem_image.mp hvS
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,(congrArg Prod.fst hzv).trans hvc⟩,
      congrArg Prod.snd hzv⟩
  · intro v hv u hu heq
    exact Prod.ext ((mem_filter.mp hv).2.trans (mem_filter.mp hu).2.symm) heq
  · intro y hy
    obtain ⟨z,hz,hzy⟩ := mem_image.mp hy
    obtain ⟨hzS,hzc⟩ := mem_filter.mp hz
    refine ⟨(c,y),mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
    exact mem_image.mpr ⟨z,hzS,Prod.ext hzc hzy⟩

lemma sum_fiber_image_card {Z X Y : Type*} (S : Finset Z) (f : Z → X) (g : Z → Y) :
    (∑c∈S.image f,((S.filter (fun z => f z=c)).image g).card)=
      (S.image (fun z => (f z,g z))).card := by
  have himage : (S.image (fun z => (f z,g z))).image Prod.fst=S.image f := by
    rw [image_image]
    rfl
  calc
    _ = ∑c∈S.image f,((S.image (fun z => (f z,g z))).filter (fun v => v.1=c)).card :=
      sum_congr rfl (fun c _ => (joint_fiber_card S f g c).symm)
    _ = _ := by
      rw [←himage]
      exact (card_eq_sum_card_image Prod.fst _).symm

/-- Count the same literal offset/angle incidences in either order. -/
lemma double_count_fiber_images {Z X Y : Type*} (S : Finset Z) (f : Z → X) (g : Z → Y) :
    (∑c∈S.image f,((S.filter (fun z => f z=c)).image g).card)=
      ∑a∈S.image g,((S.filter (fun z => g z=a)).image f).card := by
  rw [sum_fiber_image_card,sum_fiber_image_card]
  have hswap : (S.image (fun z => (f z,g z))).image Prod.swap=S.image (fun z => (g z,f z)) := by
    rw [image_image]
    rfl
  rw [←hswap,card_image_of_injective _ Prod.swap_injective]

/-- Each actual angular label meets at most 3^ell offset grid cells.
The reference point is chosen from that angular label's genuine incidence fiber. -/
theorem angle_offset_cap {P T Angle : Type*} {ell : ℕ}
    (S : Finset (P × T)) (angle : T → Angle) (xi : P → Fin ell → ℝ)
    (w : ℝ) (hw : 0 < w)
    (hClose : ∀z∈S,∀u∈S,angle z.2=angle u.2 → ∀i,|xi z.1 i-xi u.1 i| ≤ w)
    (a : Angle) :
    (((S.filter (fun z => angle z.2=a)).image (fun z => offsetCell w (xi z.1))).card) ≤ 3^ell := by
  by_cases hne : (S.filter (fun z => angle z.2=a)).Nonempty
  · obtain ⟨u,hu⟩ := hne
    obtain ⟨huS,hua⟩ := mem_filter.mp hu
    have hsub : (S.filter (fun z => angle z.2=a)).image (fun z => offsetCell w (xi z.1))⊆
        neighbors (offsetCell w (xi u.1)) := by
      intro c hc
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hc
      obtain ⟨hzS,hza⟩ := mem_filter.mp hz
      apply Fintype.mem_piFinset.mpr
      intro i
      apply mem_Icc.mpr
      exact floor_difference_le_one hw (hClose z hzS u huS (hza.trans hua.symm) i)
    exact (card_le_card hsub).trans_eq (neighbors_card _)
  · simp only [not_nonempty_iff_eq_empty.mp hne,image_empty,card_empty,Nat.zero_le]

/-- Local field oscillation, genuine incident-direction witnesses, and
the actual pointwise angular lower bound produce the offset-menu estimate.
The angular union is the literal image of S, not a supplied menu certificate. -/
theorem actual_offset_count {P T Angle : Type*} {k ell : ℕ}
    (S : Finset (P × T)) (angle : T → Angle)
    (tangent : T → Fin k → ℝ) (normal : T → Fin ell → ℝ)
    (field : P → Fin ell → Fin k → ℝ) (xi : P → Fin ell → ℝ)
    (E M v A B lower : ℝ) (hk : k ≤ 2)
    (hE : 0 ≤ E) (hM : 0 < M) (hv : 0 ≤ v) (hA : 0 < A) (hB : 0 ≤ B)
    (hT : ∀z∈S,∀j,|tangent z.2 j| ≤ B)
    (hF : ∀p∈S.image Prod.fst,∀i j,|field p i j| ≤ (1/4:ℝ))
    (hVar : ∀p∈S.image Prod.fst,∀q∈S.image Prod.fst,∀i j,|field p i j-field q i j| ≤ v)
    (hAngle : ∀z∈S,∀u∈S,angle z.2=angle u.2 →
      (∀j,|tangent z.2 j-tangent u.2 j| ≤ A/M) ∧
      (∀i,|normal z.2 i-normal u.2 i| ≤ A/M))
    (hRes : ∀z∈S,∀i,|normal z.2 i-(∑j,field z.1 i j*tangent z.2 j)-xi z.1 i| ≤ E)
    (hLower : ∀p∈S.image Prod.fst,
      lower ≤ (((S.filter (fun z => z.1=p)).image (fun z => angle z.2)).card:ℝ)) :
    let w := 2*E+2*A/M+2*B*v
    (((S.image (fun z => offsetCell w (xi z.1))).card):ℝ)*lower ≤
      (3:ℝ)^ell*((S.image (fun z => angle z.2)).card:ℝ) := by
  intro w
  have hw : 0 < w := by dsimp [w]; positivity
  let f := fun z : P × T => offsetCell w (xi z.1)
  let g := fun z : P × T => angle z.2
  have hClose : ∀z∈S,∀u∈S,angle z.2=angle u.2 → ∀i,|xi z.1 i-xi u.1 i| ≤ w := by
    intro z hz u hu ha
    exact shared_angle_offsets S angle tangent normal field xi E M v A B hk hM hv hA.le hB
      hT hF hVar hAngle hRes hz hu ha
  have hcap (a : Angle) : ((S.filter (fun z => g z=a)).image f).card ≤ 3^ell :=
    angle_offset_cap S angle xi w hw hClose a
  have hlower (c : Fin ell → ℤ) (hc : c∈S.image f) :
      lower ≤ (((S.filter (fun z => f z=c)).image g).card:ℝ) := by
    obtain ⟨z,hz,hzc⟩ := mem_image.mp hc
    have hsub : (S.filter (fun u => u.1=z.1)).image g⊆(S.filter (fun u => f u=c)).image g := by
      intro a ha
      obtain ⟨u,hu,hua⟩ := mem_image.mp ha
      obtain ⟨huS,huz⟩ := mem_filter.mp hu
      refine mem_image.mpr ⟨u,mem_filter.mpr ⟨huS,?_⟩,hua⟩
      simpa only [f,huz] using hzc
    exact (hLower z.1 (mem_image_of_mem Prod.fst hz)).trans (Nat.cast_le.mpr (card_le_card hsub))
  have hdouble : (∑c∈S.image f,((((S.filter (fun z => f z=c)).image g).card):ℝ))=
      ∑a∈S.image g,((((S.filter (fun z => g z=a)).image f).card):ℝ) := by
    exact_mod_cast double_count_fiber_images S f g
  change ((S.image f).card:ℝ)*lower ≤ (3:ℝ)^ell*(S.image g).card
  calc
    _ = ∑_c∈S.image f,lower := by simp
    _ ≤ ∑c∈S.image f,((((S.filter (fun z => f z=c)).image g).card):ℝ) := sum_le_sum hlower
    _ = ∑a∈S.image g,((((S.filter (fun z => g z=a)).image f).card):ℝ) := hdouble
    _ ≤ ∑_a∈S.image g,(3:ℝ)^ell := sum_le_sum (fun a _ => by exact_mod_cast hcap a)
    _ = _ := by simp [mul_comm]

end NativeLocalOffsetCount
