import Theorems.Thm_StickyKakeya4_small_fiber_alignment

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 2200000

namespace FractionalFiberAlignment

open SelfUniform SmallFiberAlignment

noncomputable def spatialBall {ℓ : ℕ} (P : Finset (Grid ℓ)) (R : ℕ) (p : Grid ℓ) :
    Finset (Grid ℓ) := by
  classical
  exact P.filter (fun q => |q.1 - p.1| ≤ (R : ℤ) ∧ normalClose R q.2 p.2)

noncomputable def fiber {ℓ : ℕ} (P : Finset (Grid ℓ)) (y : Normal ℓ) : Finset (Grid ℓ) := by
  classical
  exact P.filter (fun p => p.2 = y)

noncomputable def fiberBall {ℓ : ℕ} (P : Finset (Grid ℓ)) (R : ℕ) (p : Grid ℓ) :
    Finset (Grid ℓ) := by
  classical
  exact P.filter (fun q => q.2 = p.2 ∧ |q.1 - p.1| ≤ (R : ℤ))

noncomputable def normalBall {ℓ : ℕ} (P : Finset (Grid ℓ)) (R : ℕ) (y : Normal ℓ) :
    Finset (Normal ℓ) := by
  classical
  exact (P.image Prod.snd).filter (fun z => normalClose R z y)

def columnTime {ℓ : ℕ} (R : ℕ) (p : Grid ℓ) : Normal ℓ × ℤ := (p.2, p.1 / (R : ℤ))

noncomputable def timeBins {ℓ : ℕ} (P : Finset (Grid ℓ)) (R : ℕ) (y : Normal ℓ) :
    Finset ℤ := by
  classical
  exact (fiber P y).image (fun p => p.1 / (R : ℤ))

/-- Actual finite summation over the image partition of a geometric region. -/
lemma card_le_cells_mul_real_capacity {α β : Type*} [DecidableEq β]
    (S P : Finset α) (f : α → β) (hSP : S ⊆ P) (C : ℝ)
    (hC : ∀ c, ((P.filter (fun p => f p = c)).card : ℝ) ≤ C) :
    (S.card : ℝ) ≤ ((S.image f).card : ℝ) * C := by
  classical
  calc
    (S.card : ℝ) = ∑ c ∈ S.image f, ((S.filter (fun p => f p = c)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image f S
    _ ≤ ∑ _c ∈ S.image f, C := by
      apply Finset.sum_le_sum
      intro c _hc
      apply le_trans ?_ (hC c)
      exact_mod_cast Finset.card_le_card (show S.filter (fun p => f p = c) ⊆
        P.filter (fun p => f p = c) from fun p hp =>
          Finset.mem_filter.mpr ⟨hSP (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩)
    _ = ((S.image f).card : ℝ) * C := by simp

/-- The total longitudinal-bin menu is counted by the actual normal columns
and their conditional bin menus, not by an assumed global product certificate. -/
lemma columnTime_card_le {ℓ : ℕ} (P : Finset (Grid ℓ)) (R : ℕ) (B : ℝ)
    (hB : ∀ y, ((timeBins P R y).card : ℝ) ≤ B) :
    ((P.image (columnTime R)).card : ℝ) ≤ ((P.image Prod.snd).card : ℝ) * B := by
  classical
  let S := ((P.image Prod.snd).sigma (timeBins P R)).map
    (Equiv.sigmaEquivProd (Normal ℓ) ℤ).toEmbedding
  have hsub : P.image (columnTime R) ⊆ S := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_map.mpr
    refine ⟨⟨p.2, p.1 / (R : ℤ)⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem Prod.snd hp,
      Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩⟩
  calc
    ((P.image (columnTime R)).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = ∑ y ∈ P.image Prod.snd, ((timeBins P R y).card : ℝ) := by
      simp only [S, Finset.card_map, Finset.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _y ∈ P.image Prod.snd, B := Finset.sum_le_sum (fun y _hy => hB y)
    _ = ((P.image Prod.snd).card : ℝ) * B := by simp

lemma nearby_floors {R : ℕ} (hR : 0 < R) {x y : ℤ}
    (hxy : |x - y| ≤ (R : ℤ)) : |x / (R : ℤ) - y / (R : ℤ)| ≤ 1 := by
  have hR' : (0 : ℤ) < R := by exact_mod_cast hR
  have h₁ : x ≤ y + R := by have := abs_le.mp hxy; omega
  have h₂ : y ≤ x + R := by have := abs_le.mp hxy; omega
  have hq₁ := Int.ediv_le_ediv hR' h₁
  have hq₂ := Int.ediv_le_ediv hR' h₂
  have hadd (a : ℤ) : (a + R) / (R : ℤ) = a / (R : ℤ) + 1 := by
    simpa using Int.add_mul_ediv_right a 1 (ne_of_gt hR')
  rw [hadd] at hq₁ hq₂
  exact abs_le.mpr ⟨by omega, by omega⟩

noncomputable def neighborCells {ℓ : ℕ} (c : Grid ℓ) : Finset (Grid ℓ) := by
  classical
  exact (Finset.Icc (c.1 - 1) (c.1 + 1)).product
    (Fintype.piFinset (fun i => Finset.Icc (c.2 i - 1) (c.2 i + 1)))

lemma card_neighborCells {ℓ : ℕ} (c : Grid ℓ) : (neighborCells c).card = 3 ^ (ℓ + 1) := by
  classical
  have hicc (z : ℤ) : (Finset.Icc (z - 1) (z + 1)).card = 3 := by
    rw [Int.card_Icc]
    omega
  simp [neighborCells, Finset.product_eq_sprod, hicc, pow_succ, Nat.mul_comm]

lemma spatialBall_cell_count {ℓ R : ℕ} (P : Finset (Grid ℓ)) (hR : 0 < R) (p : Grid ℓ) :
    ((spatialBall P R p).image (spatialCell R)).card ≤ 3 ^ (ℓ + 1) := by
  classical
  rw [← card_neighborCells (spatialCell R p)]
  apply Finset.card_le_card
  intro c hc
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨_hqP, htime, hnormal⟩ := Finset.mem_filter.mp hq
  apply Finset.mem_product.mpr
  constructor
  · have h := abs_le.mp (nearby_floors hR htime)
    exact Finset.mem_Icc.mpr ⟨by dsimp [spatialCell]; omega, by dsimp [spatialCell]; omega⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    have h := abs_le.mp (nearby_floors hR (hnormal i))
    exact Finset.mem_Icc.mpr ⟨by dsimp [spatialCell]; omega, by dsimp [spatialCell]; omega⟩

lemma spatialBall_upper {ℓ R : ℕ} (P E : Finset (Grid ℓ)) (hEP : E ⊆ P)
    (hR : 0 < R) (p : Grid ℓ) (C : ℝ) (hC : 0 ≤ C)
    (hcell : ∀ c, ((P.filter (fun q => spatialCell R q = c)).card : ℝ) ≤ C) :
    ((spatialBall E R p).card : ℝ) ≤ (3 : ℝ) ^ (ℓ + 1) * C := by
  classical
  apply (card_le_cells_mul_real_capacity (spatialBall E R p) P (spatialCell R)
    ((Finset.filter_subset _ _).trans hEP) C hcell).trans
  apply mul_le_mul_of_nonneg_right _ hC
  exact_mod_cast spatialBall_cell_count E hR p

lemma fiberBall_upper {ℓ : ℕ} (P E : Finset (Grid ℓ)) (hEP : E ⊆ P)
    (R : ℕ) (p : Grid ℓ) : (fiberBall E R p).card ≤ (fiberBall P R p).card := by
  classical
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqE, hq⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hEP hqE, hq⟩

/-- Decompose an actual spatial ball into normal fibers; every summand is
bounded by the original narrow-column segment population. -/
lemma spatialBall_le_quotient_times_fiber {ℓ : ℕ} (P E : Finset (Grid ℓ))
    (hEP : E ⊆ P) (R : ℕ) (p : Grid ℓ) (B : ℝ) (hB : 0 ≤ B)
    (hsegment : ∀ q, ((fiberBall P R q).card : ℝ) ≤ B) :
    ((spatialBall E R p).card : ℝ) ≤ ((normalBall E R p.2).card : ℝ) * B := by
  classical
  have hcap : ∀ y, (((spatialBall E R p).filter (fun q => q.2 = y)).card : ℝ) ≤ B := by
    intro y
    apply le_trans ?_ (hsegment (p.1, y))
    exact_mod_cast Finset.card_le_card (show (spatialBall E R p).filter (fun q => q.2 = y) ⊆
      fiberBall P R (p.1, y) from by
        intro q hq
        obtain ⟨hqball, hqy⟩ := Finset.mem_filter.mp hq
        obtain ⟨hqE, htime, _hnormal⟩ := Finset.mem_filter.mp hqball
        exact Finset.mem_filter.mpr ⟨hEP hqE, hqy, htime⟩)
  have hsub : (spatialBall E R p).image Prod.snd ⊆ normalBall E R p.2 := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hqE, _htime, hnormal⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem Prod.snd hqE, hnormal⟩
  exact (card_le_cells_mul_real_capacity (spatialBall E R p) (spatialBall E R p) Prod.snd
    (Finset.Subset.refl _) B hcap).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hB)

/-- The full strip is the disjoint union of all full occupied normal fibers
whose normal labels lie in the quotient ball. -/
lemma sum_fiber_card_eq_strip {ℓ : ℕ} (P : Finset (Grid ℓ)) (R : ℕ) (y : Normal ℓ) :
    (∑ z ∈ normalBall P R y, (fiber P z).card) = (strip P R y).card := by
  classical
  have hset : P.filter (fun p => p.2 ∈ normalBall P R y) = strip P R y := by
    ext p
    simp only [Finset.mem_filter, normalBall, strip]
    constructor
    · rintro ⟨hp, _himage, hclose⟩
      exact ⟨hp, hclose⟩
    · rintro ⟨hp, hclose⟩
      exact ⟨hp, Finset.mem_image_of_mem Prod.snd hp, hclose⟩
  simpa only [fiber, hset] using
    Finset.sum_card_fiberwise_eq_card_filter P (normalBall P R y) Prod.snd

lemma strip_lower_from_fibers {ℓ : ℕ} (P : Finset (Grid ℓ)) (R : ℕ) (y : Normal ℓ)
    (a K : ℝ) (h : ∀ z ∈ P.image Prod.snd, a ≤ K * ((fiber P z).card : ℝ)) :
    a * ((normalBall P R y).card : ℝ) ≤ K * ((strip P R y).card : ℝ) := by
  classical
  calc
    a * ((normalBall P R y).card : ℝ) = ∑ _z ∈ normalBall P R y, a := by simp [mul_comm]
    _ ≤ ∑ z ∈ normalBall P R y, K * ((fiber P z).card : ℝ) :=
      Finset.sum_le_sum (fun z hz => h z (Finset.mem_filter.mp hz).1)
    _ = K * ((strip P R y).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast sum_fiber_card_eq_strip P R y

/-- Original-label mass to an actual geometric region, using the constructed
partition self-uniformity and the original inverse-image weight cap. -/
lemma original_mass_le_region {α β : Type*} [DecidableEq β] {ℓ Q : ℕ}
    (w : α → ℕ) (v : α → Grid ℓ) {A E : Finset α} (hEA : E ⊆ A)
    (U D : ℕ) (hvertex : ∀ p, mass w (A.filter (fun a => v a = p)) ≤ U)
    (hret : mass w A ≤ D * mass w E) (f : Grid ℓ → β)
    (huniform : ∀ a b, a ∈ E → b ∈ E →
      degree w (fun x y => f (v x) = f (v y)) E a ≤
        Q ^ 2 * degree w (fun x y => f (v x) = f (v y)) E b)
    (a : α) (ha : a ∈ E) (S : Finset (Grid ℓ))
    (hS : ∀ b ∈ E, f (v b) = f (v a) → v b ∈ S) :
    mass w A ≤ D * Q ^ 2 * (A.image (fun b => f (v b))).card * U * S.card := by
  classical
  let B := E.filter (fun b => f (v b) = f (v a))
  have hBE : B ⊆ E := Finset.filter_subset _ _
  have hdeg : degree w (fun x y => f (v x) = f (v y)) E a = mass w B := by
    simp only [degree, mass, B, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _hb
    exact ite_congr (propext eq_comm) (fun _ => rfl) (fun _ => rfl)
  have hsub : B.image v ⊆ S := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
    exact hS b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2
  have hmassB : mass w B ≤ U * S.card :=
    (mass_le_vertex_cap_mul_card w v (hBE.trans hEA) U hvertex).trans
      (Nat.mul_le_mul_left U (Finset.card_le_card hsub))
  have hrich := partition_richness_of_self_uniform w (fun b => f (v b)) Q hEA huniform ha
  rw [hdeg] at hrich
  calc
    mass w A ≤ D * mass w E := hret
    _ ≤ D * (Q ^ 2 * (A.image (fun b => f (v b))).card * mass w B) := Nat.mul_le_mul_left D hrich
    _ ≤ D * (Q ^ 2 * (A.image (fun b => f (v b))).card * (U * S.card)) :=
      Nat.mul_le_mul_left D (Nat.mul_le_mul_left _ hmassB)
    _ = D * Q ^ 2 * (A.image (fun b => f (v b))).card * U * S.card := by ring

/-- The common numerical cancellation used for spatial, local fiber, and full
fiber lower counts. Both the original vertex cap and global scale cancel. -/
lemma scale_lower {W density U X Y K m B n : ℝ}
    (hU : 0 < U) (hX : 0 < X) (hY : 0 ≤ Y) (hK : 0 ≤ K) (hn : 0 ≤ n)
    (hmass : density * U * X ≤ W) (hcount : W ≤ K * m * U * n)
    (hmenu : m * Y ≤ B * X) : density * Y ≤ K * B * n := by
  apply (mul_le_mul_iff_right₀ (mul_pos hU hX)).mp
  calc
    (U * X) * (density * Y) = (density * U * X) * Y := by ring
    _ ≤ (K * m * U * n) * Y := mul_le_mul_of_nonneg_right (hmass.trans hcount) hY
    _ = (K * U * n) * (m * Y) := by ring
    _ ≤ (K * U * n) * (B * X) := mul_le_mul_of_nonneg_left hmenu (by positivity)
    _ = (U * X) * (K * B * n) := by ring

def comparisonCost (d L Q : ℕ) : ℝ :=
  (retentionCost (d + (d + 1)) L : ℝ) * (Q : ℝ) ^ 2

/-- Finite fractional-column alignment, constructed on unchanged original
weighted labels. One self-uniform refinement treats the spatial, column-time,
and column partitions simultaneously. Its same output has spatial `t` counts,
local fiber `s` counts, full-fiber richness, and quotient `t-s` counts.

Every menu and population hypothesis is directly measured on the ORIGINAL
geometric image. In particular the genuine normal-column menu bound is an
explicit input; it is not asserted to follow from ambient AD. The quotient
upper bound uses the FULL original strip profile and sums whole final fibers.
The conclusions concern the supplied finite working radii and do not assert
that arbitrary later restrictions retain lower AD bounds. -/
theorem fractional_column_alignment {α : Type*} {ℓ d Q L : ℕ}
    (hQ : 4 ≤ Q) (w : α → ℕ) (A : Finset α) (v : α → Grid ℓ)
    (R : Fin d → ℕ) (U N : ℕ) (t s density B₀ B₁ B₂ B₃ B₄ B₅ : ℝ)
    (hne : A.Nonempty) (hw : ∀ a ∈ A, 0 < w a)
    (hheight : mass w A ≤ Q ^ L) (hR : ∀ j, 0 < R j ∧ R j ≤ N)
    (hU : 0 < U) (hN : 0 < N) (_hdensity : 0 < density)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hB₃ : 0 ≤ B₃) (hB₄ : 0 ≤ B₄) (_hB₅ : 0 ≤ B₅)
    (hvertex : ∀ p, mass w (A.filter (fun a => v a = p)) ≤ U)
    (hmass : density * (U : ℝ) * (N : ℝ) ^ t ≤ (mass w A : ℝ))
    (hspace : ∀ j, ((A.image (fun a => spatialCell (R j) (v a))).card : ℝ) ≤
      B₀ * ((N : ℝ) / (R j : ℝ)) ^ t)
    (hcolumns : ((A.image (fun a => (v a).2)).card : ℝ) ≤ B₁ * (N : ℝ) ^ (t - s))
    (hbins : ∀ j y, ((timeBins (A.image v) (R j) y).card : ℝ) ≤
      B₂ * ((N : ℝ) / (R j : ℝ)) ^ s)
    (hcell : ∀ j c, (((A.image v).filter (fun p => spatialCell (R j) p = c)).card : ℝ) ≤
      B₃ * (R j : ℝ) ^ t)
    (hsegment : ∀ j p, ((fiberBall (A.image v) (R j) p).card : ℝ) ≤ B₄ * (R j : ℝ) ^ s)
    (hstrip : ∀ j y,
      (((strip (A.image v) (R j) y).image (spatialCell (R j))).card : ℝ) ≤
        B₅ * ((N : ℝ) / (R j : ℝ)) ^ s) :
    ∃ E ⊆ A, E.Nonempty ∧
      mass w A ≤ retentionCost (d + (d + 1)) L * mass w E ∧
      ∀ p ∈ E.image v,
        (density * (N : ℝ) ^ s ≤ comparisonCost d L Q * B₁ * ((fiber (E.image v) p.2).card : ℝ)) ∧
        ∀ j,
          (density * (R j : ℝ) ^ t ≤
            comparisonCost d L Q * B₀ * ((spatialBall (E.image v) (R j) p).card : ℝ)) ∧
          (((spatialBall (E.image v) (R j) p).card : ℝ) ≤
            (3 : ℝ) ^ (ℓ + 1) * B₃ * (R j : ℝ) ^ t) ∧
          (density * (R j : ℝ) ^ s ≤
            comparisonCost d L Q * B₁ * B₂ * ((fiberBall (E.image v) (R j) p).card : ℝ)) ∧
          (((fiberBall (E.image v) (R j) p).card : ℝ) ≤ B₄ * (R j : ℝ) ^ s) ∧
          (density * (R j : ℝ) ^ (t - s) ≤
            comparisonCost d L Q * B₀ * B₄ * ((normalBall (E.image v) (R j) p.2).card : ℝ)) ∧
          (density * ((normalBall (E.image v) (R j) p.2).card : ℝ) ≤
            comparisonCost d L Q * B₁ * B₃ * B₅ * (R j : ℝ) ^ (t - s)) := by
  classical
  let rel : Fin (d + (d + 1)) → α → α → Prop :=
    Fin.addCases (fun j a b => spatialCell (R j) (v a) = spatialCell (R j) (v b))
      (Fin.addCases (fun j a b => columnTime (R j) (v a) = columnTime (R j) (v b))
        (fun (_ : Fin 1) a b => (v a).2 = (v b).2))
  have hrefl : ∀ i a, rel i a a := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j a
      simp only [rel, Fin.addCases_left]
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro j a
        simp only [rel, Fin.addCases_right, Fin.addCases_left]
      · intro j a
        simp only [rel, Fin.addCases_right]
  have hsym : ∀ i a b, rel i a b → rel i b a := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j a b
      simpa only [rel, Fin.addCases_left] using
        (fun h : spatialCell (R j) (v a) = spatialCell (R j) (v b) => h.symm)
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro j a b
        simpa only [rel, Fin.addCases_right, Fin.addCases_left] using
          (fun h : columnTime (R j) (v a) = columnTime (R j) (v b) => h.symm)
      · intro j a b
        simpa only [rel, Fin.addCases_right] using (fun h : (v a).2 = (v b).2 => h.symm)
  obtain ⟨E, hEA, hEne, hret, huniform⟩ :=
    weighted_self_uniform_refinement (by omega : 0 < d + (d + 1)) hQ w rel hrefl hsym A hne hw hheight
  let D := retentionCost (d + (d + 1)) L
  let K := comparisonCost d L Q
  have hretD : mass w A ≤ D * mass w E := hret
  have hK : 0 ≤ K := by dsimp [K, comparisonCost]; positivity
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNt := Real.rpow_pos_of_pos hN' t
  have hNs := Real.rpow_pos_of_pos hN' s
  have hNfactor : (N : ℝ) ^ (t - s) * (N : ℝ) ^ s = (N : ℝ) ^ t := by
    rw [← Real.rpow_add hN']
    congr 1
    ring
  have hEP : E.image v ⊆ A.image v := Finset.image_subset_image hEA
  have hCu : ∀ a b, a ∈ E → b ∈ E →
      degree w (fun x y => (v x).2 = (v y).2) E a ≤
        Q ^ 2 * degree w (fun x y => (v x).2 = (v y).2) E b := by
    intro a b ha hb
    simpa only [rel, Fin.addCases_right] using
      huniform (Fin.natAdd d (Fin.natAdd d (0 : Fin 1))) a b ha hb
  have hSu : ∀ j a b, a ∈ E → b ∈ E →
      degree w (fun x y => spatialCell (R j) (v x) = spatialCell (R j) (v y)) E a ≤
        Q ^ 2 * degree w (fun x y => spatialCell (R j) (v x) = spatialCell (R j) (v y)) E b := by
    intro j a b ha hb
    simpa only [rel, Fin.addCases_left] using huniform (Fin.castAdd (d + 1) j) a b ha hb
  have hTu : ∀ j a b, a ∈ E → b ∈ E →
      degree w (fun x y => columnTime (R j) (v x) = columnTime (R j) (v y)) E a ≤
        Q ^ 2 * degree w (fun x y => columnTime (R j) (v x) = columnTime (R j) (v y)) E b := by
    intro j a b ha hb
    simpa only [rel, Fin.addCases_right, Fin.addCases_left] using
      huniform (Fin.natAdd d (Fin.castAdd 1 j)) a b ha hb
  have hwholePoint : ∀ a ∈ E,
      density * (N : ℝ) ^ s ≤ K * B₁ * ((fiber (E.image v) (v a).2).card : ℝ) := by
    intro a ha
    have hc := original_mass_le_region w v hEA U D hvertex hretD Prod.snd hCu a ha
      (fiber (E.image v) (v a).2)
      (fun b hb hba => Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem v hb, hba⟩)
    have hc' : (mass w A : ℝ) ≤ K * ((A.image (fun b => (v b).2)).card : ℝ) * (U : ℝ) *
        ((fiber (E.image v) (v a).2).card : ℝ) := by
      dsimp [K, comparisonCost]
      exact_mod_cast hc
    have hm : ((A.image (fun b => (v b).2)).card : ℝ) * (N : ℝ) ^ s ≤ B₁ * (N : ℝ) ^ t := by
      calc
        _ ≤ (B₁ * (N : ℝ) ^ (t - s)) * (N : ℝ) ^ s :=
          mul_le_mul_of_nonneg_right hcolumns hNs.le
        _ = B₁ * (N : ℝ) ^ t := by rw [mul_assoc, hNfactor]
    exact scale_lower hU' hNt hNs.le hK (by positivity) hmass hc' hm
  have hwhole : ∀ y ∈ (E.image v).image Prod.snd,
      density * (N : ℝ) ^ s ≤ K * B₁ * ((fiber (E.image v) y).card : ℝ) := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact hwholePoint a ha
  refine ⟨E, hEA, hEne, hretD, ?_⟩
  intro p hp
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  refine ⟨hwholePoint a ha, ?_⟩
  intro j
  have hR' : (0 : ℝ) < R j := by exact_mod_cast (hR j).1
  have hRt := Real.rpow_pos_of_pos hR' t
  have hRs := Real.rpow_pos_of_pos hR' s
  have hRfactor : (R j : ℝ) ^ (t - s) * (R j : ℝ) ^ s = (R j : ℝ) ^ t := by
    rw [← Real.rpow_add hR']
    congr 1
    ring
  have hratio (u : ℝ) : ((N : ℝ) / (R j : ℝ)) ^ u * (R j : ℝ) ^ u = (N : ℝ) ^ u := by
    rw [Real.div_rpow hN'.le hR'.le]
    exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hR' u))
  have hratioST : ((N : ℝ) / (R j : ℝ)) ^ s * (R j : ℝ) ^ t =
      (N : ℝ) ^ s * (R j : ℝ) ^ (t - s) := by
    calc
      _ = (((N : ℝ) / (R j : ℝ)) ^ s * (R j : ℝ) ^ s) * (R j : ℝ) ^ (t - s) := by
        rw [← hRfactor]
        ring
      _ = _ := by rw [hratio s]
  have hSpatialLower : density * (R j : ℝ) ^ t ≤
      K * B₀ * ((spatialBall (E.image v) (R j) (v a)).card : ℝ) := by
    have hc := original_mass_le_region w v hEA U D hvertex hretD (spatialCell (R j)) (hSu j) a ha
      (spatialBall (E.image v) (R j) (v a)) (fun b hb hba =>
        Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem v hb, same_spatialCell_close (hR j).1 hba⟩)
    have hc' : (mass w A : ℝ) ≤ K * ((A.image (fun b => spatialCell (R j) (v b))).card : ℝ) *
        (U : ℝ) * ((spatialBall (E.image v) (R j) (v a)).card : ℝ) := by
      dsimp [K, comparisonCost]
      exact_mod_cast hc
    have hm : ((A.image (fun b => spatialCell (R j) (v b))).card : ℝ) * (R j : ℝ) ^ t ≤
        B₀ * (N : ℝ) ^ t := by
      calc
        _ ≤ (B₀ * ((N : ℝ) / (R j : ℝ)) ^ t) * (R j : ℝ) ^ t :=
          mul_le_mul_of_nonneg_right (hspace j) hRt.le
        _ = _ := by rw [mul_assoc, hratio t]
    exact scale_lower hU' hNt hRt.le hK (by positivity) hmass hc' hm
  have hSpatialUpper : ((spatialBall (E.image v) (R j) (v a)).card : ℝ) ≤
      (3 : ℝ) ^ (ℓ + 1) * B₃ * (R j : ℝ) ^ t := by
    simpa only [mul_assoc] using spatialBall_upper (A.image v) (E.image v) hEP (hR j).1
      (v a) (B₃ * (R j : ℝ) ^ t) (mul_nonneg hB₃ hRt.le) (hcell j)
  have hFiberLower : density * (R j : ℝ) ^ s ≤
      K * B₁ * B₂ * ((fiberBall (E.image v) (R j) (v a)).card : ℝ) := by
    have hc := original_mass_le_region w v hEA U D hvertex hretD (columnTime (R j)) (hTu j) a ha
      (fiberBall (E.image v) (R j) (v a)) (fun b hb hba =>
        Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem v hb, congrArg Prod.fst hba,
          same_floor_close (hR j).1 (congrArg Prod.snd hba)⟩)
    have hc' : (mass w A : ℝ) ≤ K * ((A.image (fun b => columnTime (R j) (v b))).card : ℝ) *
        (U : ℝ) * ((fiberBall (E.image v) (R j) (v a)).card : ℝ) := by
      dsimp [K, comparisonCost]
      exact_mod_cast hc
    have hm₀ : ((A.image (fun b => columnTime (R j) (v b))).card : ℝ) ≤
        ((A.image (fun b => (v b).2)).card : ℝ) * (B₂ * ((N : ℝ) / (R j : ℝ)) ^ s) := by
      simpa only [Finset.image_image, Function.comp_def] using
        columnTime_card_le (A.image v) (R j) (B₂ * ((N : ℝ) / (R j : ℝ)) ^ s) (hbins j)
    have hm₁ : ((A.image (fun b => columnTime (R j) (v b))).card : ℝ) ≤
        (B₁ * (N : ℝ) ^ (t - s)) * (B₂ * ((N : ℝ) / (R j : ℝ)) ^ s) :=
      hm₀.trans (mul_le_mul_of_nonneg_right hcolumns (mul_nonneg hB₂ (by positivity)))
    have hm : ((A.image (fun b => columnTime (R j) (v b))).card : ℝ) * (R j : ℝ) ^ s ≤
        (B₁ * B₂) * (N : ℝ) ^ t := by
      calc
        _ ≤ ((B₁ * (N : ℝ) ^ (t - s)) * (B₂ * ((N : ℝ) / (R j : ℝ)) ^ s)) * (R j : ℝ) ^ s :=
          mul_le_mul_of_nonneg_right hm₁ hRs.le
        _ = (B₁ * B₂) * ((N : ℝ) ^ (t - s) *
            (((N : ℝ) / (R j : ℝ)) ^ s * (R j : ℝ) ^ s)) := by ring
        _ = _ := by rw [hratio s, hNfactor]
    simpa only [mul_assoc] using scale_lower hU' hNt hRs.le hK (by positivity) hmass hc' hm
  have hFiberUpper : ((fiberBall (E.image v) (R j) (v a)).card : ℝ) ≤ B₄ * (R j : ℝ) ^ s := by
    apply le_trans ?_ (hsegment j (v a))
    exact_mod_cast fiberBall_upper (A.image v) (E.image v) hEP (R j) (v a)
  have hQuotLower : density * (R j : ℝ) ^ (t - s) ≤
      K * B₀ * B₄ * ((normalBall (E.image v) (R j) (v a).2).card : ℝ) := by
    have hdecomp := spatialBall_le_quotient_times_fiber (A.image v) (E.image v) hEP (R j) (v a)
      (B₄ * (R j : ℝ) ^ s) (mul_nonneg hB₄ hRs.le) (hsegment j)
    apply (mul_le_mul_iff_left₀ hRs).mp
    calc
      (density * (R j : ℝ) ^ (t - s)) * (R j : ℝ) ^ s = density * (R j : ℝ) ^ t := by
        rw [mul_assoc, hRfactor]
      _ ≤ K * B₀ * ((spatialBall (E.image v) (R j) (v a)).card : ℝ) := hSpatialLower
      _ ≤ K * B₀ * (((normalBall (E.image v) (R j) (v a).2).card : ℝ) * (B₄ * (R j : ℝ) ^ s)) :=
        mul_le_mul_of_nonneg_left hdecomp (mul_nonneg hK hB₀)
      _ = (K * B₀ * B₄ * ((normalBall (E.image v) (R j) (v a).2).card : ℝ)) * (R j : ℝ) ^ s := by ring
  have hStripUpper : ((strip (E.image v) (R j) (v a).2).card : ℝ) ≤
      B₃ * B₅ * (N : ℝ) ^ s * (R j : ℝ) ^ (t - s) := by
    have hstripSub : strip (E.image v) (R j) (v a).2 ⊆ strip (A.image v) (R j) (v a).2 := by
      intro q hq
      obtain ⟨hqE, hqclose⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hEP hqE, hqclose⟩
    calc
      ((strip (E.image v) (R j) (v a).2).card : ℝ) ≤
          ((strip (A.image v) (R j) (v a).2).card : ℝ) := by exact_mod_cast Finset.card_le_card hstripSub
      _ ≤ (((strip (A.image v) (R j) (v a).2).image (spatialCell (R j))).card : ℝ) *
          (B₃ * (R j : ℝ) ^ t) :=
        card_le_cells_mul_real_capacity _ _ (spatialCell (R j)) (Finset.filter_subset _ _) _ (hcell j)
      _ ≤ (B₅ * ((N : ℝ) / (R j : ℝ)) ^ s) * (B₃ * (R j : ℝ) ^ t) :=
        mul_le_mul_of_nonneg_right (hstrip j (v a).2) (mul_nonneg hB₃ hRt.le)
      _ = B₃ * B₅ * (((N : ℝ) / (R j : ℝ)) ^ s * (R j : ℝ) ^ t) := by ring
      _ = B₃ * B₅ * (N : ℝ) ^ s * (R j : ℝ) ^ (t - s) := by rw [hratioST]; ring
  have hQuotUpper : density * ((normalBall (E.image v) (R j) (v a).2).card : ℝ) ≤
      K * B₁ * B₃ * B₅ * (R j : ℝ) ^ (t - s) := by
    have hsum := strip_lower_from_fibers (E.image v) (R j) (v a).2
      (density * (N : ℝ) ^ s) (K * B₁) hwhole
    apply (mul_le_mul_iff_left₀ hNs).mp
    calc
      (density * ((normalBall (E.image v) (R j) (v a).2).card : ℝ)) * (N : ℝ) ^ s =
          (density * (N : ℝ) ^ s) * ((normalBall (E.image v) (R j) (v a).2).card : ℝ) := by ring
      _ ≤ K * B₁ * ((strip (E.image v) (R j) (v a).2).card : ℝ) := hsum
      _ ≤ K * B₁ * (B₃ * B₅ * (N : ℝ) ^ s * (R j : ℝ) ^ (t - s)) :=
        mul_le_mul_of_nonneg_left hStripUpper (mul_nonneg hK hB₁)
      _ = (K * B₁ * B₃ * B₅ * (R j : ℝ) ^ (t - s)) * (N : ℝ) ^ s := by ring
  exact ⟨hSpatialLower, hSpatialUpper, hFiberLower, hFiberUpper, hQuotLower, hQuotUpper⟩

end FractionalFiberAlignment
