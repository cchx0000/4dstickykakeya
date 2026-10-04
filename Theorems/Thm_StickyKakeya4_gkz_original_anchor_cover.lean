import Theorems.Thm_StickyKakeya4_gkz_original_dense_ratio_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZOriginalAnchorCover
open ActualRoundedAdditiveEnergy OriginalSeparatedPacking

/-- Original anchor mass recovers the fine cover of a bounded target set from
the cover of its translated sum. Every original anchor is counted. -/
theorem original_anchor_cover_recovery (A S : Finset ℝ) {delta b c R M : ℝ}
    (hd : 0 < delta) (hb : 1 ≤ b) (hM : 0 ≤ M)
    (hS : ∀ x ∈ S, |x-c| ≤ R)
    (hcap : ∀ z : ℝ, ((A.filter (fun a => |a-z| ≤ R+delta)).card : ℝ) ≤ M) :
    ((S.image (rounded delta)).card : ℝ)*A.card ≤ 4*M*
      ((A.product S).image (fun p => rounded delta (b*p.1+p.2))).card := by
  let C := S.image (rounded delta)
  have hw : ∀ z ∈ C, ∃ x ∈ S, rounded delta x=z := fun z hz => Finset.mem_image.mp hz
  let rep : ℤ → ℝ := fun z => if hz : z∈C then Classical.choose (hw z hz) else 0
  have hrep (z : ℤ) (hz : z∈C) : rep z ∈ S ∧ rounded delta (rep z)=z := by
    dsimp [rep]
    rw [dif_pos hz]
    exact Classical.choose_spec (hw z hz)
  let P := C.product A
  let code : ℤ × ℝ → ℤ := fun p => rounded delta (b*p.2+rep p.1)
  have herr (j : ℤ) {p : ℤ × ℝ} (_hp : p∈P) (hc : code p=j) :
      |b*p.2+rep p.1-delta*(j:ℝ)| ≤ delta := by
    have h := round_error hd (b*p.2+rep p.1)
    change rounded delta (b*p.2+rep p.1)=j at hc
    rw [hc] at h
    exact (abs_of_nonneg h.1).le.trans h.2.le
  have hsingle (j : ℤ) (a : ℝ) :
      (((P.filter (fun p => code p=j)).filter (fun p => p.2=a)).card : ℝ) ≤ 4 := by
    let D := C.filter (fun z => |rep z-(delta*(j:ℝ)-b*a)| ≤ delta)
    have hsub : ((P.filter (fun p => code p=j)).filter (fun p => p.2=a)).card ≤ D.card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        obtain ⟨hp, hpa⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hp).1, ?_⟩
        have he := herr j hp hc
        rw [hpa] at he
        convert he using 1
        congr 1
        ring
      · intro p hp q hq hpq
        exact Prod.ext hpq ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
    apply (Nat.cast_le.mpr hsub).trans
    apply (NativeTangentGridCoarsening.scalar_injective_grid_centered_card D rep
      (r := delta) (R := 1) (c := delta*(j:ℝ)-b*a) hd (by norm_num) ?_ ?_).trans (by norm_num)
    · intro z hz w hw hzw
      have hz' := (hrep z (Finset.mem_filter.mp hz).1).2
      have hw' := (hrep w (Finset.mem_filter.mp hw).1).2
      change rounded delta (rep z)=rounded delta (rep w) at hzw
      simpa only [hz', hw'] using hzw
    · intro z hz
      simpa only [one_mul] using (Finset.mem_filter.mp hz).2
  have hanchor (j : ℤ) :
      (P.filter (fun p => code p=j)).image Prod.snd ⊆
        A.filter (fun a => |a-(delta*(j:ℝ)-c)/b| ≤ R+delta) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpC, hpA⟩ := Finset.mem_product.mp hp
    refine Finset.mem_filter.mpr ⟨hpA, ?_⟩
    have hnear := herr j hp hc
    have ht := hS (rep p.1) (hrep p.1 hpC).1
    have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
    have hid : b*(p.2-(delta*(j:ℝ)-c)/b)=
        (b*p.2+rep p.1-delta*(j:ℝ))-(rep p.1-c) := by
      field_simp
      ring
    have hmult : b*|p.2-(delta*(j:ℝ)-c)/b| ≤ delta+R := by
      calc
        _ = |b*(p.2-(delta*(j:ℝ)-c)/b)| := by rw [abs_mul, abs_of_pos hbpos]
        _ = |(b*p.2+rep p.1-delta*(j:ℝ))-(rep p.1-c)| := by rw [hid]
        _ ≤ delta+R := (abs_sub _ _).trans (add_le_add hnear ht)
    have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (p.2-(delta*(j:ℝ)-c)/b))
    nlinarith
  have hfiber : ∀ j ∈ P.image code,
      ((P.filter (fun p => code p=j)).card : ℝ) ≤ 4*M := by
    intro j _
    have hmass := card_le_real_mul_image (P.filter (fun p => code p=j)) Prod.snd
      (fun a _ => hsingle j a)
    have hanchors : (((P.filter (fun p => code p=j)).image Prod.snd).card : ℝ) ≤ M :=
      (Nat.cast_le.mpr (Finset.card_le_card (hanchor j))).trans (hcap _)
    exact hmass.trans (mul_le_mul_of_nonneg_left hanchors (by norm_num))
  have hmass := card_le_real_mul_image P code hfiber
  have himage : P.image code ⊆
      (A.product S).image (fun p => rounded delta (b*p.1+p.2)) := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hpC, hpA⟩ := Finset.mem_product.mp hp
    exact Finset.mem_image.mpr ⟨(p.2, rep p.1),
      Finset.mem_product.mpr ⟨hpA, (hrep p.1 hpC).1⟩, rfl⟩
  have hout : ((P.image code).card : ℝ) ≤
      ((A.product S).image (fun p => rounded delta (b*p.1+p.2))).card :=
    Nat.cast_le.mpr (Finset.card_le_card himage)
  have hp : (P.card : ℝ) = (C.card : ℝ)*A.card := by
    simp only [P, Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
  rw [hp] at hmass
  exact hmass.trans (mul_le_mul_of_nonneg_left hout (by positivity))

end GKZOriginalAnchorCover
