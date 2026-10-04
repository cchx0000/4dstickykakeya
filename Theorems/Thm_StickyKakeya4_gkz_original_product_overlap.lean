import Theorems.Thm_StickyKakeya4_gkz_original_ratio_gap
import Theorems.Thm_StickyKakeya4_original_common_scalar_fibers

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace GKZOriginalProductOverlap
open ActualRoundedAdditiveEnergy OriginalCommonScalarFibers

def dilateCells (delta : ℝ) (A : Finset ℝ) (a : ℝ) : Finset ℤ :=
  A.image (fun x => rounded delta (a*x))
def productCells (delta : ℝ) (A : Finset ℝ) : Finset ℤ :=
  (A.product A).image (fun p => rounded delta (p.1*p.2))
def dilateIncidence (delta : ℝ) (A : Finset ℝ) : Finset (ℝ × ℤ) :=
  (A.product A).image (fun p => (p.1, rounded delta (p.1*p.2)))

lemma product_code_injective (A : Finset ℝ) {delta a : ℝ} (hd : 0 < delta)
    (ha : 1 ≤ a)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x≠y → delta ≤ |x-y|) :
    Set.InjOn (fun x => rounded delta (a*x)) A := by
  intro x hx y hy hxy
  by_contra hne
  have hlarge := hsep x hx y hy hne
  have hsmall := ProjectionHeavyCells.same_floor_difference hd hxy
  have habs : |a*x-a*y|=a*|x-y| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : 0 ≤ a)]
  rw [habs] at hsmall
  have hm := mul_le_mul_of_nonneg_right ha (abs_nonneg (x-y))
  nlinarith

lemma mem_dilateIncidence (A : Finset ℝ) (delta a : ℝ) (z : ℤ) :
    (a,z)∈dilateIncidence delta A ↔ a∈A ∧ z∈dilateCells delta A a := by
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp h
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have he1 : p.1=a := congrArg Prod.fst he
    have he2 : rounded delta (p.1*p.2)=z := congrArg Prod.snd he
    rw [he1] at he2 hp1
    exact ⟨hp1, Finset.mem_image.mpr ⟨p.2, hp2, he2⟩⟩
  · rintro ⟨ha, hz⟩
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨(a,x), Finset.mem_product.mpr ⟨ha,hx⟩,
      Prod.ext rfl he⟩

lemma dilateCells_subset_productCells (A : Finset ℝ) (delta : ℝ) {a : ℝ} (ha : a∈A) :
    dilateCells delta A a ⊆ productCells delta A := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨(a,x), Finset.mem_product.mpr ⟨ha,hx⟩, rfl⟩

theorem original_product_incidence_mass (A : Finset ℝ) {delta : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta)
    (hbox : ∀ a∈A, 1 ≤ a)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|) :
    dilateIncidence delta A ⊆ A.product (productCells delta A) ∧
    (dilateIncidence delta A).card=A.card^2 ∧
    A.card ≤ (productCells delta A).card := by
  have hinj : Set.InjOn (fun p : ℝ × ℝ => (p.1, rounded delta (p.1*p.2))) (A.product A) := by
    intro p hp q hq he
    have he1 : p.1=q.1 := congrArg (fun z : ℝ × ℤ => z.1) he
    have he2 : rounded delta (p.1*p.2)=rounded delta (q.1*q.2) :=
      congrArg (fun z : ℝ × ℤ => z.2) he
    rw [← he1] at he2
    exact Prod.ext he1 (product_code_injective A hd
      (hbox _ (Finset.mem_product.mp hp).1) hsep
      (Finset.mem_product.mp hp).2 (Finset.mem_product.mp hq).2 he2)
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hq).1,
      Finset.mem_image_of_mem _ hq⟩
  · rw [dilateIncidence, Finset.card_image_of_injOn hinj]
    simp only [Finset.product_eq_sprod, Finset.card_product, pow_two]
  · obtain ⟨a, ha⟩ := hA
    have hc : (dilateCells delta A a).card=A.card :=
      Finset.card_image_of_injOn (product_code_injective A hd (hbox _ ha) hsep)
    rw [← hc]
    exact Finset.card_le_card (dilateCells_subset_productCells A delta ha)

lemma commonFiber_eq_actual_overlap (A : Finset ℝ) (delta : ℝ)
    {a b : ℝ} (ha : a∈A) (hb : b∈A) :
    commonFiber (dilateIncidence delta A) (productCells delta A) a b =
      dilateCells delta A a ∩ dilateCells delta A b := by
  ext z
  constructor
  · intro hz
    obtain ⟨_, hza, hzb⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_inter.mpr ⟨((mem_dilateIncidence A delta a z).mp hza).2,
      ((mem_dilateIncidence A delta b z).mp hzb).2⟩
  · intro hz
    obtain ⟨hza, hzb⟩ := Finset.mem_inter.mp hz
    exact Finset.mem_filter.mpr ⟨dilateCells_subset_productCells A delta ha hza,
      (mem_dilateIncidence A delta a z).mpr ⟨ha,hza⟩,
      (mem_dilateIncidence A delta b z).mpr ⟨hb,hzb⟩⟩

/-- Small actual product cover produces a popular original multiplier and a
dense original multiplier set with large literal overlaps of rounded dilates. -/
theorem exists_original_popular_multiplier (A : Finset ℝ) {delta K : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hK : 0 < K)
    (hbox : ∀ a∈A, 1 ≤ a)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hcover : ((productCells delta A).card : ℝ) ≤ K*A.card) :
    ∃ b∈A, ∃ V : Finset ℝ, V ⊆ A ∧
      ((1/K)^2/2)*(A.card : ℝ) ≤ V.card ∧
      ∀ a∈V, ((1/K)^2/2)*(A.card : ℝ) ≤
        (dilateCells delta A b ∩ dilateCells delta A a).card := by
  obtain ⟨hF, hFcard, hCcard⟩ := original_product_incidence_mass A hA hd hbox hsep
  let C := productCells delta A
  let F := dilateIncidence delta A
  let q : ℝ := (1/K)^2/2
  let R := richPairs A C F q
  have hAc : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hC : C.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hA.card_pos hCcard)
  have hmass : (1/K)*(A.card : ℝ)*C.card ≤ (F.card : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hcover
      (show 0 ≤ (1/K)*(A.card : ℝ) by positivity)
    have hFcardR : (F.card : ℝ) = (A.card : ℝ)^2 := by exact_mod_cast hFcard
    rw [hFcardR]
    have hid : (1/K)*(A.card : ℝ)*(K*(A.card : ℝ))=(A.card : ℝ)^2 := by field_simp
    exact hm.trans_eq hid
  have hR : q*(A.card : ℝ)^2 ≤ R.card :=
    richPairs_card_lower A C F hC (by positivity) hF hmass
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image A
    (fun b => (R.filter (fun p => p.1=b)).card) hA
  let T := R.filter (fun p => p.1=b)
  let V := T.image Prod.snd
  have hsum : R.card = ∑ a∈A, (R.filter (fun p => p.1=a)).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun p hp =>
      (Finset.mem_product.mp (richPairs_subset A C F q hp)).1)
  have hrows : R.card ≤ A.card*T.card := by
    calc
      _ = ∑ a∈A, (R.filter (fun p => p.1=a)).card := hsum
      _ ≤ ∑ _a∈A, T.card := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hinj : Set.InjOn (Prod.snd : ℝ × ℝ → ℝ) (T : Set (ℝ × ℝ)) := by
    intro p hp r hr he
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm) he
  have hVcard : V.card=T.card := Finset.card_image_of_injOn hinj
  have hmember {a : ℝ} (ha : a∈V) : (b,a)∈R := by
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp ha
    obtain ⟨hpR, hp1⟩ := Finset.mem_filter.mp hp
    have hpba : p=(b,a) := Prod.ext hp1 he
    simpa only [hpba] using hpR
  refine ⟨b, hb, V, ?_, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_product.mp (richPairs_subset A C F q (hmember ha))).2
  · have hrowsR : (R.card : ℝ) ≤ (A.card : ℝ)*T.card := by exact_mod_cast hrows
    change q*(A.card : ℝ) ≤ V.card
    rw [hVcard]
    apply (mul_le_mul_iff_left₀ hAc).mp
    nlinarith only [hR, hrowsR]
  · intro a ha
    have hba := hmember ha
    have haA := (Finset.mem_product.mp (richPairs_subset A C F q hba)).2
    have hcommon := richPairs_common_lower A C F q hba
    rw [commonFiber_eq_actual_overlap A delta hb haA] at hcommon
    have hc : (A.card : ℝ) ≤ C.card := Nat.cast_le.mpr hCcard
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans hcommon

end GKZOriginalProductOverlap
