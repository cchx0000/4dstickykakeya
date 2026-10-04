import Theorems.Thm_StickyKakeya4_finite_plane_projection_original_b

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

lemma exists_three_averages {T : Type*} (S : Finset T) (f g h : T → ℝ) {F G H : ℝ}
    (hS : S.Nonempty) (hF : 0 < F) (hG : 0 < G) (hH : 0 < H)
    (hf0 : ∀ t ∈ S, 0 ≤ f t) (hg0 : ∀ t ∈ S, 0 ≤ g t) (hh0 : ∀ t ∈ S, 0 ≤ h t)
    (hf : (∑ t ∈ S, f t) ≤ F * S.card)
    (hg : (∑ t ∈ S, g t) ≤ G * S.card)
    (hh : (∑ t ∈ S, h t) ≤ H * S.card) :
    ∃ t ∈ S, f t ≤ 3 * F ∧ g t ≤ 3 * G ∧ h t ≤ 3 * H := by
  have havg (f : T → ℝ) (C : ℝ) (hC : 0 < C)
      (hf : (∑ t ∈ S, f t) ≤ C * S.card) :
      (∑ t ∈ S, f t / C) ≤ S.card := by
    rw [← Finset.sum_div]
    have hdiv := div_le_div_of_nonneg_right hf hC.le
    have he : C * (S.card : ℝ) / C = S.card := by field_simp
    rwa [he] at hdiv
  have hbudget : (∑ t ∈ S, (f t / F + g t / G + h t / H)) ≤ 3 * S.card := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 := havg f F hF hf
    have h2 := havg g G hG hg
    have h3 := havg h H hH hh
    linarith
  obtain ⟨t, ht, hsum⟩ := exists_le_average S (fun t => f t / F + g t / G + h t / H)
    3 hS hbudget
  have hfn := div_nonneg (hf0 t ht) hF.le
  have hgn := div_nonneg (hg0 t ht) hG.le
  have hhn := div_nonneg (hh0 t ht) hH.le
  exact ⟨t, ht, (div_le_iff₀ hF).mp (by linarith),
    (div_le_iff₀ hG).mp (by linarith), (div_le_iff₀ hH).mp (by linarith)⟩

lemma image_lower_of_collision_bound {X : Type*} (P : Finset X) (p : X → Point3)
    (uv : ℝ × ℝ) {rho C : ℝ} (hP : P.Nonempty) (hrho : 0 < rho) (hC : 0 < C)
    (hcoll : ((labelCollisions P p uv rho).card : ℝ) ≤ C * P.card) :
    (P.card : ℝ) / C ≤ ((P.image (fun i => projectedCell uv rho (p i))).card : ℝ) := by
  have hCS := projected_cell_energy P p uv hrho
  have hN : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hprod := mul_le_mul_of_nonneg_left hcoll
    (show 0 ≤ ((P.image (fun i => projectedCell uv rho (p i))).card : ℝ) by positivity)
  apply (div_le_iff₀ hC).2
  nlinarith

/-- A single explicit finite-grid projection preserves occupied-cell
populations of BOTH original families while controlling B's line triples. -/
theorem exists_common_two_images {X Y : Type*} (P : Finset X) (p : X → Point3)
    (B : Finset Y) (b : Y → Point3) (n J : ℕ) {rho KP KB r A : ℝ}
    (hP : P.Nonempty) (hB : B.Nonempty) (hmesh : mesh n ≤ rho)
    (hKP : 0 < KP) (hKB : 0 < KB) (hr : 0 ≤ r) (hA : 0 < A)
    (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htopP : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (htopB : ∀ i ∈ B, ∀ k ∈ B, dist3 (b i) (b k) ≤ 2)
    (hKTP : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ KP * R / rho)
    (hKTB : ∀ i ∈ B, ∀ R : ℝ, rho ≤ R →
      ((B.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ KB * R / rho) :
    ∃ uv ∈ parameters n,
      (P.card : ℝ) / (771 * KP) ≤ ((P.image (fun i => projectedCell uv rho (p i))).card : ℝ) ∧
      (B.card : ℝ) / (771 * KB) ≤ ((B.image (fun i => projectedCell uv rho (b i))).card : ℝ) ∧
      ((smallProjectedTriples B b uv r).card : ℝ) ≤
        3 * (((degenerateTriples B b A).card : ℝ) +
          (8 * r / A + 2 * mesh n) * (B.card : ℝ) ^ 3) := by
  let F := 257 * KP * (P.card : ℝ)
  let G := 257 * KB * (B.card : ℝ)
  let H := ((degenerateTriples B b A).card : ℝ) +
    (8 * r / A + 2 * mesh n) * (B.card : ℝ) ^ 3
  have hNp : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hNb : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hm := mesh_pos n
  have hF : 0 < F := by dsimp [F]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨uv, huv, hcollP, hcollB, htri⟩ := exists_three_averages (parameters n)
    (fun uv => ((labelCollisions P p uv rho).card : ℝ))
    (fun uv => ((labelCollisions B b uv rho).card : ℝ))
    (fun uv => ((smallProjectedTriples B b uv r).card : ℝ)) (parameters_nonempty n) hF hG hH
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (actual_KT1_collision_energy P p n J hmesh hKP.le hJ htopP hKTP)
    (actual_KT1_collision_energy B b n J hmesh hKB.le hJ htopB hKTB)
    (original_triangle_projection_budget B b n hr hA)
  have hcP : ((labelCollisions P p uv rho).card : ℝ) ≤ (771 * KP) * P.card := by
    dsimp [F] at hcollP
    nlinarith
  have hcB : ((labelCollisions B b uv rho).card : ℝ) ≤ (771 * KB) * B.card := by
    dsimp [G] at hcollB
    nlinarith
  exact ⟨uv, huv,
    image_lower_of_collision_bound P p uv hP (hm.trans_le hmesh) (by positivity) hcP,
    image_lower_of_collision_bound B b uv hB (hm.trans_le hmesh) (by positivity) hcB, htri⟩

/-- One ACTUAL original label per occupied projected cell, with no new
points and no independent resampling. -/
lemma exists_cell_representatives {X Z : Type*} [DecidableEq Z]
    (P : Finset X) (cell : X → Z) :
    ∃ S : Finset X, S ⊆ P ∧ S.image cell = P.image cell ∧
      Set.InjOn cell (↑S) ∧ S.card = (P.image cell).card := by
  let lift : {z // z ∈ P.image cell} → X := fun z => Classical.choose (Finset.mem_image.mp z.property)
  have hlift : ∀ z, lift z ∈ P ∧ cell (lift z) = z.val :=
    fun z => Classical.choose_spec (Finset.mem_image.mp z.property)
  let S := (P.image cell).attach.image lift
  have hS : S ⊆ P := by
    intro x hx
    obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hx
    exact (hlift z).1
  have himage : S.image cell = P.image cell := by
    apply Finset.Subset.antisymm (Finset.image_subset_image hS)
    intro z hz
    exact Finset.mem_image.mpr ⟨lift ⟨z, hz⟩,
      Finset.mem_image_of_mem lift (Finset.mem_attach _ _), (hlift _).2⟩
  have hinj : Set.InjOn cell (↑S) := by
    intro x hx y hy heq
    obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hy
    have hzt : z = t := Subtype.ext (by simpa only [(hlift z).2, (hlift t).2] using heq)
    rw [hzt]
  exact ⟨S, hS, himage, hinj, by rw [← himage, Finset.card_image_iff.mpr hinj]⟩

/-- Line-tube nonconcentration passes to an original-label subset with the
explicit reciprocal population loss. -/
lemma line_fraction_to_original_subset {X : Type*} (B S : Finset X) (b : X → Point3)
    (uv : ℝ × ℝ) {a d c w theta L : ℝ} (hSB : S ⊆ B) (htheta : 0 ≤ theta)
    (hmass : (B.card : ℝ) ≤ L * S.card)
    (hline : ((projectedLineStrip B b uv a d c w).card : ℝ) ≤ theta * B.card) :
    ((projectedLineStrip S b uv a d c w).card : ℝ) ≤ (theta * L) * S.card := by
  have hsub : projectedLineStrip S b uv a d c w ⊆ projectedLineStrip B b uv a d c w :=
    Finset.filter_subset_filter _ hSB
  calc
    _ ≤ ((projectedLineStrip B b uv a d c w).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ theta * B.card := hline
    _ ≤ theta * (L * S.card) := mul_le_mul_of_nonneg_left hmass htheta
    _ = _ := by ring


/-- Complete finite labelled projection selection. Both retained families
consist of actual original labels, use the SAME projection, and have injective
projected cell labels. The retained B line-tube loss is fully explicit. -/
theorem exists_common_original_subsets {X Y : Type*}
    (P : Finset X) (p : X → Point3) (B : Finset Y) (b : Y → Point3)
    (n J : ℕ) {rho KP KB r0 w0 w kappa epsilon theta : ℝ}
    (hP : P.Nonempty) (hBnon : B.Nonempty) (hmesh : mesh n ≤ rho)
    (hKP : 0 < KP) (hKB : 0 < KB) (hr0 : 0 < r0) (hw0 : 0 < w0)
    (hw : 0 ≤ w) (hepsilon : 0 ≤ epsilon) (htheta : 0 ≤ theta)
    (hscalar : 3 * (kappa + epsilon + 128 * w / (r0 * w0) + 2 * mesh n) ≤ theta ^ 3)
    (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htopP : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (htopB : ∀ i ∈ B, ∀ k ∈ B, dist3 (b i) (b k) ≤ 2)
    (hKTP : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ KP * R / rho)
    (hKTB : ∀ i ∈ B, ∀ R : ℝ, rho ≤ R →
      ((B.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ KB * R / rho)
    (hB : ∀ i ∈ B, |(b i).1| ≤ 1 ∧ |(b i).2.1| ≤ 1 ∧ |(b i).2.2| ≤ 1)
    (hclose : ∀ i ∈ B,
      ((B.filter (fun j => dist3 (b i) (b j) ≤ r0)).card : ℝ) ≤ kappa * B.card)
    (hline : ∀ i ∈ B, ∀ j ∈ B, r0 < dist3 (b i) (b j) →
      ((originalCrossTube B b i j w0).card : ℝ) ≤ epsilon * B.card) :
    ∃ uv ∈ parameters n, ∃ S : Finset X, ∃ T : Finset Y,
      S ⊆ P ∧ T ⊆ B ∧
      (P.card : ℝ) / (771 * KP) ≤ S.card ∧
      (B.card : ℝ) / (771 * KB) ≤ T.card ∧
      Set.InjOn (fun i => projectedCell uv rho (p i)) (↑S) ∧
      Set.InjOn (fun i => projectedCell uv rho (b i)) (↑T) ∧
      ∀ a d c : ℝ, max |a| |d| = 1 →
        ((projectedLineStrip T b uv a d c w).card : ℝ) ≤
          (771 * KB * theta) * T.card := by
  obtain ⟨uv, huv, hPimage, hBimage, htri⟩ := exists_common_two_images P p B b n J
    hP hBnon hmesh hKP hKB (by positivity : 0 ≤ 16 * w) (mul_pos hr0 hw0)
    hJ htopP htopB hKTP hKTB
  obtain ⟨S, hSP, _hSim, hSinj, hScard⟩ := exists_cell_representatives P
    (fun i => projectedCell uv rho (p i))
  obtain ⟨T, hTB, _hTim, hTinj, hTcard⟩ := exists_cell_representatives B
    (fun i => projectedCell uv rho (b i))
  have hSsize : (P.card : ℝ) / (771 * KP) ≤ S.card := by rwa [hScard]
  have hTsize : (B.card : ℝ) / (771 * KB) ≤ T.card := by rwa [hTcard]
  have hmass : (B.card : ℝ) ≤ (771 * KB) * T.card := by
    have hh := (div_le_iff₀ (show 0 < 771 * KB by positivity)).mp hTsize
    nlinarith
  have hdeg := original_degenerate_triple_count B b hw0.le hepsilon hclose hline
  refine ⟨uv, huv, S, T, hSP, hTB, hSsize, hTsize, hSinj, hTinj, ?_⟩
  intro a d c hnormal
  have hcube := projected_line_strip_cube B b (c := c) huv hw hnormal hB
  have hsmall : ((projectedLineStrip B b uv a d c w).card : ℝ) ^ 3 ≤
      (3 * (kappa + epsilon + 128 * w / (r0 * w0) + 2 * mesh n)) * (B.card : ℝ) ^ 3 := by
    calc
      _ ≤ 3 * (((degenerateTriples B b (r0 * w0)).card : ℝ) +
          (8 * (16 * w) / (r0 * w0) + 2 * mesh n) * (B.card : ℝ) ^ 3) := hcube.trans htri
      _ ≤ 3 * ((kappa + epsilon) * (B.card : ℝ) ^ 3 +
          (8 * (16 * w) / (r0 * w0) + 2 * mesh n) * (B.card : ℝ) ^ 3) := by linarith
      _ = _ := by ring
  have hfrac := line_strip_fraction_of_cube B b uv a d c w theta _ htheta hscalar hsmall
  have hsubfrac := line_fraction_to_original_subset B T b uv hTB htheta hmass hfrac
  convert hsubfrac using 1
  ring

end FinitePlaneProjectionGrid
