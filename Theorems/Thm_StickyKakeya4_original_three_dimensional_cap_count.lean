import Theorems.Thm_StickyKakeya4_original_three_dimensional_cap_coordinates
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalCapCount
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalUnitNormals
open OriginalThreeDimensionalCapCoordinates

lemma integer_interval_mass (S : Finset ℤ) (rho R a : ℝ)
    (hrho : 0<rho) (hR : 0≤R)
    (hS : ∀ k∈S, |rho*(k:ℝ)-a|≤R) :
    (S.card : ℝ)*rho≤2*R+2*rho := by
  let lo : ℤ := ⌊(a-R)/rho⌋
  let hi : ℤ := ⌊(a+R)/rho⌋
  have hlohi : lo≤hi := Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hrho.le)
  have hsub : S⊆Finset.Icc lo hi := by
    intro k hk
    obtain ⟨hkl,hku⟩ := abs_le.mp (hS k hk)
    have hkl' : (a-R)/rho≤(k:ℝ) := (div_le_iff₀ hrho).mpr (by nlinarith only [hkl])
    have hku' : (k:ℝ)≤(a+R)/rho := (le_div_iff₀ hrho).mpr (by nlinarith only [hku])
    exact Finset.mem_Icc.mpr ⟨by simpa only [Int.floor_intCast] using Int.floor_mono hkl', Int.le_floor.mpr hku'⟩
  have hc : ((Finset.Icc lo hi).card : ℝ)=(hi:ℝ)+1-(lo:ℝ) := by
    exact_mod_cast Int.card_Icc_of_le lo hi (by omega : lo≤hi+1)
  have hcard : (S.card : ℝ)≤(hi:ℝ)+1-(lo:ℝ) := by
    rw [← hc]
    exact_mod_cast Finset.card_le_card hsub
  have hhi : (hi:ℝ)*rho≤a+R := (le_div_iff₀ hrho).mp (Int.floor_le _)
  have hlo : a-R<((lo:ℝ)+1)*rho := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one _)
  have hm := mul_le_mul_of_nonneg_right hcard hrho.le
  nlinarith only [hm,hhi,hlo]

lemma weighted_fiber_count {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (S : Finset X) (f : X→Y) (T M : ℝ)
    (hf : ∀ y∈S.image f, ((S.filter (fun x => f x=y)).card : ℝ)*T≤M) :
    (S.card : ℝ)*T≤M*(S.image f).card := by
  calc
    _ = ∑ y∈S.image f, ((S.filter (fun x => f x=y)).card : ℝ)*T := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Finset.card_eq_sum_card_image f S
    _ ≤ ∑ _y∈S.image f, M := Finset.sum_le_sum hf
    _ = _ := by simp [mul_comm]

lemma rectangle_mass (S : Finset (ℤ×ℤ)) (rho w a b : ℝ)
    (hrho : 0<rho) (hrhow : rho≤w)
    (hS : ∀ z∈S, |rho*(z.1:ℝ)-a|≤100*w ∧ |rho*(z.2:ℝ)-b|≤100*w) :
    (S.card : ℝ)*rho^2≤40804*w^2 := by
  have hw : 0≤w := hrho.le.trans hrhow
  have hfirst := integer_interval_mass (S.image Prod.fst) rho (100*w) a hrho (by positivity)
    (by rintro k hk; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk; exact (hS z hz).1)
  have hsecond := integer_interval_mass (S.image Prod.snd) rho (100*w) b hrho (by positivity)
    (by rintro k hk; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk; exact (hS z hz).2)
  have hfirst' : ((S.image Prod.fst).card : ℝ)*rho≤202*w := by linarith only [hfirst,hrhow]
  have hsecond' : ((S.image Prod.snd).card : ℝ)*rho≤202*w := by linarith only [hsecond,hrhow]
  have hsub : S⊆(S.image Prod.fst).product (S.image Prod.snd) := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hz,Finset.mem_image_of_mem _ hz⟩
  have hc : (S.card : ℝ)≤((S.image Prod.fst).card : ℝ)*(S.image Prod.snd).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product _ _)
  have hm := mul_le_mul hfirst' hsecond' (by positivity : (0:ℝ)≤(S.image Prod.snd).card*rho) (by positivity : 0≤202*w)
  have hn := mul_le_mul_of_nonneg_right hc (sq_nonneg rho)
  nlinarith only [hm,hn]

lemma band_integer_mass (S : Finset ℤ) (rho A c : ℝ) (hrho : 0<rho) (hA : A≠0)
    (hA2 : |A|≤2) (hS : ∀ k∈S, |rho*(k:ℝ)*A+c|≤3*rho) :
    (S.card : ℝ)*|A|≤10 := by
  have hAp : 0< |A| := abs_pos.mpr hA
  have hS' : ∀ k∈S, |rho*(k:ℝ)-(-c/A)|≤3*rho/|A| := by
    intro k hk
    have he : rho*(k:ℝ)-(-c/A)=(rho*(k:ℝ)*A+c)/A := by field_simp; ring
    rw [he,abs_div]
    exact div_le_div_of_nonneg_right (hS k hk) hAp.le
  have hc := integer_interval_mass S rho (3*rho/|A|) (-c/A) hrho (by positivity) hS'
  have hm := mul_le_mul_of_nonneg_right hc hAp.le
  have he : (2*(3*rho/|A|)+2*rho)*|A|=6*rho+2*rho*|A| := by field_simp; ring
  rw [he] at hm
  have hh : ((S.card : ℝ)*|A|)*rho≤10*rho := by nlinarith only [hm,hA2,hrho]
  exact (mul_le_mul_iff_left₀ hrho).mp (by nlinarith only [hh])

lemma first_coefficient_count (S : Finset (ℤ×ℤ)) (rho w A B C D b : ℝ)
    (hrho : 0<rho) (hrhow : rho≤w) (hD : 0<D) (hDA : D≤14*|A|)
    (hA2 : |A|≤2)
    (hband : ∀ z∈S, |rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B+C|≤3*rho)
    (hcap : ∀ z∈S, |rho*(z.2:ℝ)-b|≤100*w) :
    (S.card : ℝ)*rho*D≤28280*w := by
  have hA : A≠0 := by intro hz; rw [hz,abs_zero,mul_zero] at hDA; linarith only [hDA,hD]
  have hw : 0≤w := hrho.le.trans hrhow
  have hf : ∀ l∈S.image Prod.snd, ((S.filter (fun z => z.2=l)).card : ℝ)*D≤140 := by
    intro l _hl
    let F := S.filter (fun z => z.2=l)
    have hi : Set.InjOn Prod.fst (↑F : Set (ℤ×ℤ)) := by
      intro z hz z' hz' he
      exact Prod.ext he ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm)
    have hc : (F.image Prod.fst).card=F.card := Finset.card_image_of_injOn hi
    have hb : ∀ k∈F.image Prod.fst, |rho*(k:ℝ)*A+(rho*(l:ℝ)*B+C)|≤3*rho := by
      intro k hk
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hzS,hzl⟩ := Finset.mem_filter.mp hz
      simpa only [hzl,add_assoc] using hband z hzS
    have hm := band_integer_mass (F.image Prod.fst) rho A (rho*(l:ℝ)*B+C) hrho hA hA2 hb
    rw [hc] at hm
    have hd := mul_le_mul_of_nonneg_left hDA (show (0:ℝ)≤F.card by positivity)
    change (F.card : ℝ)*D≤140
    nlinarith only [hm,hd]
  have hcount := weighted_fiber_count S Prod.snd D 140 hf
  have himage := integer_interval_mass (S.image Prod.snd) rho (100*w) b hrho (by positivity)
    (by rintro k hk; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk; exact hcap z hz)
  have hcount' := mul_le_mul_of_nonneg_right hcount hrho.le
  nlinarith only [hcount',himage,hrhow]

lemma rectangle_band_count (S : Finset (ℤ×ℤ)) (rho w A B C D a b : ℝ)
    (hrho : 0<rho) (hrhow : rho≤w) (hwsmall : w≤1/10)
    (hDsum : D≤|A|+|B|+|C|)
    (hA2 : |A|≤2) (hB2 : |B|≤2)
    (hgrid : ∀ z∈S, |rho*(z.1:ℝ)|≤4 ∧ |rho*(z.2:ℝ)|≤1)
    (hband : ∀ z∈S, |rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B+C|≤3*rho)
    (hcap : ∀ z∈S, |rho*(z.1:ℝ)-a|≤100*w ∧ |rho*(z.2:ℝ)-b|≤100*w) :
    (S.card : ℝ)*rho*max D rho≤30000*w := by
  have hw : 0≤w := hrho.le.trans hrhow
  by_cases hsmall : D≤6*rho
  · have hm : max D rho≤6*rho := max_le hsmall (by linarith only [hrho])
    have hrect := rectangle_mass S rho w a b hrho hrhow hcap
    have hh := mul_le_mul_of_nonneg_left hm (show (0:ℝ)≤S.card*rho by positivity)
    have hww := mul_le_mul_of_nonneg_right hwsmall hw
    nlinarith only [hrect,hh,hww,hw]
  · have hD : 0<D := by linarith only [hrho,hsmall]
    have hrD : rho≤D := by linarith only [hrho,hsmall]
    rw [max_eq_left hrD]
    by_cases hne : S.Nonempty
    · obtain ⟨z,hz⟩ := hne
      have hgb := hgrid z hz
      have hb := hband z hz
      have htri := abs_sub (rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B+C)
        (rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B)
      have ht2 := abs_add_le (rho*(z.1:ℝ)*A) (rho*(z.2:ℝ)*B)
      rw [abs_mul (rho*(z.1:ℝ)) A,abs_mul (rho*(z.2:ℝ)) B] at ht2
      have hid : rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B+C-
          (rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B)=C := by ring
      rw [hid] at htri
      have ha := mul_le_mul_of_nonneg_right hgb.1 (abs_nonneg A)
      have hb' := mul_le_mul_of_nonneg_right hgb.2 (abs_nonneg B)
      have hC : |C|≤4*|A|+|B|+3*rho := by nlinarith only [htri,ht2,ha,hb',hb]
      have hchoice : D≤14*|A| ∨ D≤14*|B| := by
        by_contra hn
        push Not at hn
        linarith only [hn.1,hn.2,hC,hDsum,hsmall]
      rcases hchoice with hDA | hDB
      · have hh := first_coefficient_count S rho w A B C D b hrho hrhow hD hDA hA2 hband
          (fun z hz => (hcap z hz).2)
        linarith only [hh,hw]
      · let T := S.image Prod.swap
        have hc : T.card=S.card := Finset.card_image_of_injective _ Prod.swap_injective
        have hbandT : ∀ z∈T, |rho*(z.1:ℝ)*B+rho*(z.2:ℝ)*A+C|≤3*rho := by
          rintro z hz
          change z∈S.image Prod.swap at hz
          obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hz
          rw [← hvz]
          simpa only [Prod.fst_swap,Prod.snd_swap,add_comm (rho*(v.2:ℝ)*B)] using hband v hv
        have hcapT : ∀ z∈T, |rho*(z.2:ℝ)-a|≤100*w := by
          rintro z hz
          change z∈S.image Prod.swap at hz
          obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hz
          rw [← hvz]
          exact (hcap v hv).1
        have hh := first_coefficient_count T rho w B A C D a hrho hrhow hD hDB hB2 hbandT hcapT
        rw [hc] at hh
        linarith only [hh,hw]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.card_empty,Nat.cast_zero,zero_mul]
      positivity

/-- Maximum coordinate displacement of the original endpoints. -/
def pointGap (p q : Point3) : ℝ := max |q 0-p 0| (max |q 1-p 1| |q 2-p 2|)

lemma point_gap_nonneg (p q : Point3) : 0≤pointGap p q :=
  (abs_nonneg _).trans (le_max_left _ _)

lemma point_gap_chart_sum (p q : Point3) (e : Equiv.Perm (Fin 3)) :
    pointGap p q≤|q (e 0)-p (e 0)|+|q (e 1)-p (e 1)|+|q (e 2)-p (e 2)| := by
  let M := |q (e 0)-p (e 0)|+|q (e 1)-p (e 1)|+|q (e 2)-p (e 2)|
  have hj : ∀ j : Fin 3, |q (e j)-p (e j)|≤M := by
    intro j
    fin_cases j <;> dsimp [M] <;> linarith only [abs_nonneg (q (e 0)-p (e 0)),
      abs_nonneg (q (e 1)-p (e 1)),abs_nonneg (q (e 2)-p (e 2))]
  have hi : ∀ i : Fin 3, |q i-p i|≤M := by
    intro i
    simpa only [Equiv.apply_symm_apply] using hj (e.symm i)
  exact max_le (hi 0) (max_le (hi 1) (hi 2))

/-- An actual original-label cap and near-orthogonal band have the correct
one-dimensional cap count. Every finite-grid and coefficient estimate is
derived from the original endpoints and literal direction labels. -/
theorem original_normal_cap_count (S : Finset DirectionLabel) (rho w : ℝ)
    (p q n : Point3) (hrho : 0<rho) (hrhow : rho≤w) (hwsmall : w≤1/10)
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) (hn : ∀ i, |n i|≤1)
    (hS : S⊆normalGrid rho)
    (hband : ∀ d∈S, |value rho d q-value rho d p|≤3*rho)
    (hcap : ∀ d∈S, ∀ i, |unitNormal rho d i-n i|≤w) :
    (S.card : ℝ)*rho*max (pointGap p q) rho≤180000*w := by
  have hw : 0≤w := hrho.le.trans hrhow
  have hrho1 : rho≤1 := by linarith only [hrhow,hwsmall]
  have hd2 : ∀ i, |q i-p i|≤2 := by
    intro i
    have hh := abs_sub (q i) (p i)
    linarith only [hh,hp i,hq i]
  have hf : ∀ e∈S.image Prod.fst,
      ((S.filter (fun d => d.1=e)).card : ℝ)*(rho*max (pointGap p q) rho)≤30000*w := by
    intro e _he
    let F := S.filter (fun d => d.1=e)
    let T := F.image Prod.snd
    have hi : Set.InjOn Prod.snd (↑F : Set DirectionLabel) := by
      intro z hz z' hz' hzz
      exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm) hzz
    have hc : T.card=F.card := Finset.card_image_of_injOn hi
    have hmem : ∀ z∈T, (e,z)∈S := by
      intro z hz
      change z∈F.image Prod.snd at hz
      obtain ⟨d,hd,hz⟩ := Finset.mem_image.mp hz
      obtain ⟨hdS,hde⟩ := Finset.mem_filter.mp hd
      have heq : d=(e,z) := Prod.ext hde hz
      simpa only [← heq] using hdS
    have hg : ∀ z∈T, |rho*(z.1:ℝ)|≤4 ∧ |rho*(z.2:ℝ)|≤1 := by
      intro z hz
      exact actual_grid_coefficients rho (e,z) hrho hrho1 (hS (hmem z hz))
    have hb : ∀ z∈T,
        |rho*(z.1:ℝ)*(q (e 0)-p (e 0))+rho*(z.2:ℝ)*(q (e 1)-p (e 1))+
          (q (e 2)-p (e 2))|≤3*rho := by
      intro z hz
      have hh := hband (e,z) (hmem z hz)
      have hid : value rho (e,z) q-value rho (e,z) p=
          rho*(z.1:ℝ)*(q (e 0)-p (e 0))+rho*(z.2:ℝ)*(q (e 1)-p (e 1))+
            (q (e 2)-p (e 2)) := by dsimp [value,projection]; ring
      rwa [hid] at hh
    have hcp : ∀ z∈T,
        |rho*(z.1:ℝ)-n (e 0)/n (e 2)|≤100*w ∧
          |rho*(z.2:ℝ)-n (e 1)/n (e 2)|≤100*w := by
      intro z hz
      exact (original_normal_cap_coordinates rho w (e,z) n hrho hrho1
        (hS (hmem z hz)) hw hwsmall hn (hcap (e,z) (hmem z hz))).2
    have hh := rectangle_band_count T rho w (q (e 0)-p (e 0)) (q (e 1)-p (e 1))
      (q (e 2)-p (e 2)) (pointGap p q) (n (e 0)/n (e 2)) (n (e 1)/n (e 2))
      hrho hrhow hwsmall (point_gap_chart_sum p q e)
      (hd2 _) (hd2 _) hg hb hcp
    rw [hc] at hh
    change (F.card : ℝ)*(rho*max (pointGap p q) rho)≤30000*w
    nlinarith only [hh]
  have hh := weighted_fiber_count S Prod.fst (rho*max (pointGap p q) rho) (30000*w) hf
  have he : (S.image Prod.fst).card≤6 := by
    have hb := Finset.card_le_univ (S.image Prod.fst)
    simpa only [Fintype.card_perm,Fintype.card_fin,show Nat.factorial 3=6 by decide] using hb
  have heR : ((S.image Prod.fst).card : ℝ)≤6 := by exact_mod_cast he
  have hm := mul_le_mul_of_nonneg_left heR (show 0≤30000*w by positivity)
  nlinarith only [hh,hm]

/-- The literal set of original direction labels in an actual unit-normal cap
and in the original displacement's width-3rho band. -/
def capBand (rho w : ℝ) (p q n : Point3) : Finset DirectionLabel :=
  (normalGrid rho).filter (fun d => |value rho d q-value rho d p|≤3*rho ∧
    ∀ i, |unitNormal rho d i-n i|≤w)

theorem original_cap_band_count (rho w : ℝ) (p q n : Point3)
    (hrho : 0<rho) (hrhow : rho≤w) (hwsmall : w≤1/10)
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) (hn : ∀ i, |n i|≤1) :
    ((capBand rho w p q n).card : ℝ)*rho*max (pointGap p q) rho≤180000*w := by
  exact original_normal_cap_count (capBand rho w p q n) rho w p q n hrho hrhow hwsmall hp hq hn
    (Finset.filter_subset _ _) (fun d hd => (Finset.mem_filter.mp hd).2.1)
    (fun d hd => (Finset.mem_filter.mp hd).2.2)

lemma unit_center_components (n : Point3) (hunit : ∑ i, (n i)^2=1) :
    ∀ i, |n i|≤1 := by
  intro i
  have hs : (n i)^2≤1 := by
    rw [← hunit]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (n j)) (Finset.mem_univ i)
  nlinarith only [hs,sq_abs (n i),abs_nonneg (n i)]

/-- Divided form for a genuine Euclidean unit cap center. -/
theorem original_unit_cap_band_card (rho w : ℝ) (p q n : Point3)
    (hrho : 0<rho) (hrhow : rho≤w) (hwsmall : w≤1/10)
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) (hunit : ∑ i, (n i)^2=1) :
    ((capBand rho w p q n).card : ℝ)≤180000*w/(rho*max (pointGap p q) rho) := by
  have hm : 0< max (pointGap p q) rho := hrho.trans_le (le_max_right _ _)
  apply (le_div_iff₀ (mul_pos hrho hm)).mpr
  have hh := original_cap_band_count rho w p q n hrho hrhow hwsmall hp hq
    (unit_center_components n hunit)
  nlinarith only [hh]

end OriginalThreeDimensionalCapCount
