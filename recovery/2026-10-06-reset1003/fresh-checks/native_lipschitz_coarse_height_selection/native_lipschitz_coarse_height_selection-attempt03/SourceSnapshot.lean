import Theorems.Thm_StickyKakeya4_native_frozen_time_field

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeLipschitzCoarseHeightSelection
open Classical Finset NativeMatrixHeightWholePoint SeparatedAlignmentPatches

/-- This count depends on the actual Lipschitz bound, not the old height mesh. -/
def subdivisions (L : ℝ) : ℕ := ⌈max 1 L⌉₊

lemma subdivisions_bounds (L : ℝ) :
    0 < subdivisions L ∧ L ≤ (subdivisions L:ℝ) ∧
      ((8*subdivisions L:ℕ):ℝ) ≤ 16*max 1 L := by
  have h1 : (1:ℝ) ≤ max 1 L := le_max_left _ _
  have hc : max 1 L ≤ (subdivisions L:ℝ) := Nat.le_ceil _
  have hu := Nat.ceil_lt_add_one (show 0 ≤ max 1 L by linarith only [h1])
  have hp : 0 < subdivisions L := by
    have hh : (0:ℝ) < (subdivisions L:ℝ) := by linarith only [h1,hc]
    exact_mod_cast hh
  refine ⟨hp,(le_max_right _ _).trans hc,?_⟩
  change ((8*⌈max 1 L⌉₊:ℕ):ℝ) ≤ _
  push_cast
  linarith only [hu,h1]

def coarse (R origin t : ℝ) : ℤ := heightCell R origin t

def fine (R origin : ℝ) (q : ℕ) (t : ℝ) : ℤ := heightCell (R/(q:ℝ)) origin t

def center (R origin : ℝ) (c : ℤ) : ℝ := origin+R*((c:ℝ)+1/2)

/-- Exact floor nesting, including negative and shifted heights. -/
lemma coarse_eq_fine_div (R origin t : ℝ) (q : ℕ) (hq : 0 < q) :
    coarse R origin t=fine R origin q t/(q:ℤ) := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hh := NativeFrozenTimeField.nested_height_readback (R/(q:ℝ)) (t-origin) q
  rw [div_mul_cancel₀ _ hqR] at hh
  exact hh

/-- The mixed-radix palette has precisely eight times q colors. -/
def paint (R origin : ℝ) (q : ℕ) (hq : 0 < q) (t : ℝ) : Fin 8 × Fin q :=
  (residue 8 (by decide) (coarse R origin t),residue q hq (fine R origin q t))

lemma same_coarse_same_fine {R origin x y : ℝ} {q : ℕ} (hq : 0 < q)
    (hc : coarse R origin x=coarse R origin y)
    (hp : paint R origin q hq x=paint R origin q hq y) :
    fine R origin q x=fine R origin q y := by
  have he := residue_eq_emod (hL:=hq) (congrArg Prod.snd hp)
  have hx := Int.emod_add_mul_ediv (fine R origin q x) (q:ℤ)
  have hy := Int.emod_add_mul_ediv (fine R origin q y) (q:ℤ)
  rw [←coarse_eq_fine_div R origin x q hq] at hx
  rw [←coarse_eq_fine_div R origin y q hq] at hy
  rw [he,hc] at hx
  exact hx.symm.trans hy

lemma coarse_color_eq {R origin x y : ℝ} {q : ℕ} (hq : 0 < q)
    (hp : paint R origin q hq x=paint R origin q hq y) :
    coarse R origin x % 8=coarse R origin y % 8 :=
  residue_eq_emod (hL:=by decide) (congrArg Prod.fst hp)

lemma center_close {R origin t : ℝ} (hR : 0 < R) :
    |t-center R origin (coarse R origin t)| ≤ R/2 := by
  have h0 := (le_div_iff₀ hR).mp (Int.floor_le ((t-origin)/R))
  have h1 := (div_lt_iff₀ hR).mp (Int.lt_floor_add_one ((t-origin)/R))
  dsimp [center,coarse,heightCell]
  exact abs_le.mpr ⟨by linarith only [h0],by linarith only [h1]⟩

lemma center_distance {R origin : ℝ} (hR : 0 < R) (c d : ℤ) :
    dist (center R origin c) (center R origin d)=R*|(c:ℝ)-(d:ℝ)| := by
  rw [Real.dist_eq]
  have he : center R origin c-center R origin d=R*((c:ℝ)-(d:ℝ)) := by
    dsimp [center]
    ring
  rw [he,abs_mul,abs_of_pos hR]

/-- Representatives in different retained coarse cells are compared at
actual coarse centers. Their old times need not equal either center. -/
lemma colored_height_distance {R origin x y : ℝ} (hR : 0 < R)
    (hc : coarse R origin x ≠ coarse R origin y)
    (hp : coarse R origin x % 8=coarse R origin y % 8) :
    |x-y| ≤ (9/8:ℝ)*dist (center R origin (coarse R origin x))
      (center R origin (coarse R origin y)) := by
  have hx := center_close (origin:=origin) (t:=x) hR
  have hy := center_close (origin:=origin) (t:=y) hR
  have hg := real_residue_spacing (by decide : 0 < (8:ℕ)) hp hc
  have hgap : 8*R ≤ dist (center R origin (coarse R origin x))
      (center R origin (coarse R origin y)) := by
    rw [center_distance hR]
    have hh := mul_le_mul_of_nonneg_left hg hR.le
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith only [hh]
  have h1 := abs_sub_le x (center R origin (coarse R origin x)) y
  have h2 := abs_sub_le (center R origin (coarse R origin x))
    (center R origin (coarse R origin y)) y
  rw [abs_sub_comm (center R origin (coarse R origin y)) y] at h2
  rw [Real.dist_eq] at hgap ⊢
  linarith only [hx,hy,hgap,h1,h2]

def selectedField {A V : Type*} [Zero V] (T : Finset A)
    (height : A → ℝ) (F : A → V) (R origin : ℝ) : ℤ → V :=
  NativeFrozenTimeField.field T (fun x => height x-origin) F R

/-- A full color fiber of the original weighted points, followed by a
field chosen from its actual old witnesses. The field is kept fixed on all
later restrictions. No local shading or Y-density premise is used. -/
theorem select_weighted_coarse_field {A V : Type*} [NormedAddCommGroup V]
    (S : Finset A) (w : A → ℕ) (height : A → ℝ) (F : A → V)
    (L R origin B : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hB : 0 ≤ B)
    (hF : ∀x∈S,‖F x‖ ≤ B)
    (hLip : ∀x∈S,∀y∈S,dist (F x) (F y) ≤ L*|height x-height y|) :
    let q:=subdivisions L
    let hq:0 < q:=(subdivisions_bounds L).1
    ∃color : Fin 8 × Fin q,
      let T:=S.filter (fun x => paint R origin q hq (height x)=color)
      T⊆S ∧ mass S w ≤ (8*q)*mass T w ∧
      (mass S w:ℝ) ≤ (16*max 1 L)*(mass T w:ℝ) ∧
      (∀x∈T,∀y∈T,coarse R origin (height x)=coarse R origin (height y) →
        fine R origin q (height x)=fine R origin q (height y)) ∧
      (∀c,‖selectedField T height F R origin c‖ ≤ B) ∧
      (∀U⊆T,∀x∈U,
        dist (selectedField T height F R origin (coarse R origin (height x))) (F x) ≤ R) ∧
      ∀U⊆T,∀x∈U,∀y∈U,
        dist (selectedField T height F R origin (coarse R origin (height x)))
          (selectedField T height F R origin (coarse R origin (height y))) ≤
        ((9/8:ℝ)*L)*dist (center R origin (coarse R origin (height x)))
          (center R origin (coarse R origin (height y))) := by
  intro q hq
  let : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  obtain ⟨color,hret⟩ := maximum_weight_color S w (fun x => paint R origin q hq (height x))
  let T:=S.filter (fun x => paint R origin q hq (height x)=color)
  have hTS : T⊆S := filter_subset _ _
  have hretN : mass S w ≤ (8*q)*mass T w := by
    simpa only [Fintype.card_prod,Fintype.card_fin,mass] using hret
  have hpaint (x : A) (hx : x∈T) (y : A) (hy : y∈T) :
      paint R origin q hq (height x)=paint R origin q hq (height y) :=
    (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
  have hfine (x : A) (hx : x∈T) (y : A) (hy : y∈T)
      (hc : coarse R origin (height x)=coarse R origin (height y)) :=
    same_coarse_same_fine hq hc (hpaint x hx y hy)
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have hsmall : L*(R/(q:ℝ)) ≤ R := by
    have hh := mul_le_mul_of_nonneg_right (subdivisions_bounds L).2.1
      (div_nonneg hR.le hqR.le)
    have he : (q:ℝ)*(R/(q:ℝ))=R := by field_simp
    rw [he] at hh
    exact hh
  refine ⟨color,hTS,hretN,?_,hfine,?_,?_,?_⟩
  · have hn : (mass S w:ℝ) ≤ ((8*q:ℕ):ℝ)*(mass T w:ℝ) := by exact_mod_cast hretN
    exact hn.trans (mul_le_mul_of_nonneg_right (subdivisions_bounds L).2.2 (Nat.cast_nonneg _))
  · exact NativeFrozenTimeField.field_norm_le T (fun x => height x-origin) F R B hB
      (fun x hx => hF x (hTS hx))
  · intro U hUT x hx
    apply NativeFrozenTimeField.field_close_to_original T (fun x => height x-origin) F R R ?_ (hUT hx)
    intro y hy z hz he
    have hh := same_height_cell_close (div_pos hR hqR) (hfine y hy z hz he)
    exact (hLip y (hTS hy) z (hTS hz)).trans
      ((mul_le_mul_of_nonneg_left hh.le hL).trans hsmall)
  · intro U hUT x hx y hy
    have hxT:=hUT hx
    have hyT:=hUT hy
    obtain ⟨v,hv,hvheight,hvF⟩ := NativeFrozenTimeField.field_realization T
      (fun z => height z-origin) F R ⟨x,hxT,rfl⟩
    obtain ⟨z,hz,hzheight,hzF⟩ := NativeFrozenTimeField.field_realization T
      (fun z => height z-origin) F R ⟨y,hyT,rfl⟩
    change coarse R origin (height v)=coarse R origin (height x) at hvheight
    change coarse R origin (height z)=coarse R origin (height y) at hzheight
    change selectedField T height F R origin (coarse R origin (height x))=F v at hvF
    change selectedField T height F R origin (coarse R origin (height y))=F z at hzF
    change dist (selectedField T height F R origin _) (selectedField T height F R origin _) ≤ _
    by_cases he : coarse R origin (height x)=coarse R origin (height y)
    · rw [he,dist_self]
      positivity
    · rw [hvF,hzF]
      have hd := colored_height_distance hR
        (show coarse R origin (height v) ≠ coarse R origin (height z) by rwa [hvheight,hzheight])
        (coarse_color_eq hq (hpaint v hv z hz))
      rw [hvheight,hzheight] at hd
      have hh := (hLip v (hTS hv) z (hTS hz)).trans (mul_le_mul_of_nonneg_left hd hL)
      simpa only [mul_assoc,mul_left_comm L (9/8:ℝ)] using hh

end NativeLipschitzCoarseHeightSelection
