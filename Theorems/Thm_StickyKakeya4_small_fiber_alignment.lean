import Theorems.Thm_StickyKakeya4_compatible_tuple_selection
import Theorems.Thm_StickyKakeya4_uniform_grain_partitions

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1800000

namespace SmallFiberAlignment

open SelfUniform

abbrev Normal (ℓ : ℕ) := Fin ℓ → ℤ
abbrev Grid (ℓ : ℕ) := ℤ × Normal ℓ

/-- The literal coordinatewise integer floor partition, also at negative coordinates. -/
def spatialCell {ℓ : ℕ} (R : ℕ) (p : Grid ℓ) : Grid ℓ :=
  (p.1 / (R : ℤ), fun i => p.2 i / (R : ℤ))

def normalClose {ℓ : ℕ} (R : ℕ) (y z : Normal ℓ) : Prop :=
  ∀ i, |y i - z i| ≤ (R : ℤ)

/-- The full reference strip: no restriction in the longitudinal coordinate. -/
noncomputable def strip {ℓ : ℕ} (P : Finset (Grid ℓ)) (R : ℕ) (y : Normal ℓ) :
    Finset (Grid ℓ) := by
  classical
  exact P.filter (fun p => normalClose R p.2 y)

noncomputable def quotientBall {α : Type*} {ℓ : ℕ}
    (A : Finset α) (v : α → Grid ℓ) (R : ℕ) (y : Normal ℓ) : Finset (Normal ℓ) := by
  classical
  exact (A.image (fun a => (v a).2)).filter (fun z => normalClose R z y)

def retentionCost (d L : ℕ) : ℕ := 2 * (4 * d) ^ (d * L)

lemma same_floor_close {R : ℕ} (hR : 0 < R) {x y : ℤ}
    (h : x / (R : ℤ) = y / (R : ℤ)) : |x - y| ≤ (R : ℤ) := by
  have hR' : (0 : ℤ) < R := by exact_mod_cast hR
  have hx := (Int.ediv_eq_iff_of_pos hR').mp h
  have hy := (Int.ediv_eq_iff_of_pos hR').mp (rfl : y / (R : ℤ) = y / (R : ℤ))
  apply abs_le.mpr
  constructor <;> omega

lemma same_spatialCell_close {ℓ R : ℕ} (hR : 0 < R) {p q : Grid ℓ}
    (h : spatialCell R p = spatialCell R q) :
    |p.1 - q.1| ≤ (R : ℤ) ∧ normalClose R p.2 q.2 := by
  constructor
  · exact same_floor_close hR (congrArg Prod.fst h)
  · intro i
    exact same_floor_close hR (congrFun (congrArg Prod.snd h) i)

/-- Convert retained ORIGINAL-label mass to distinct geometric vertices using
an upper bound on the whole original inverse-image mass of each vertex. -/
lemma mass_le_vertex_cap_mul_card {α : Type*} {ℓ : ℕ}
    (w : α → ℕ) (v : α → Grid ℓ) {A S : Finset α} (hSA : S ⊆ A) (U : ℕ)
    (hcap : ∀ p, mass w (A.filter (fun a => v a = p)) ≤ U) :
    mass w S ≤ U * (S.image v).card := by
  classical
  calc
    mass w S = ∑ p ∈ S.image v, mass w (S.filter (fun a => v a = p)) :=
      CompatibleTupleSelection.mass_eq_sum_partition w S v
    _ ≤ ∑ _p ∈ S.image v, U := by
      apply Finset.sum_le_sum
      intro p _hp
      apply (mass_mono w ?_).trans (hcap p)
      intro a ha
      obtain ⟨haS, hap⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hSA haS, hap⟩
    _ = U * (S.image v).card := by simp [Nat.mul_comm]

/-- Actual strip counting: sum the populations of its occupied spatial floor
cells. This counts full reference-strip vertices, not just a selected graph. -/
lemma strip_card_le_cells_mul_capacity {ℓ : ℕ} (P : Finset (Grid ℓ))
    (R C : ℕ) (y : Normal ℓ)
    (hcap : ∀ c, (P.filter (fun p => spatialCell R p = c)).card ≤ C) :
    (strip P R y).card ≤ ((strip P R y).image (spatialCell R)).card * C := by
  classical
  calc
    (strip P R y).card =
        ∑ c ∈ (strip P R y).image (spatialCell R),
          ((strip P R y).filter (fun p => spatialCell R p = c)).card :=
      Finset.card_eq_sum_card_image (spatialCell R) (strip P R y)
    _ ≤ ∑ _c ∈ (strip P R y).image (spatialCell R), C := by
      apply Finset.sum_le_sum
      intro c _hc
      apply (Finset.card_le_card ?_).trans (hcap c)
      intro p hp
      obtain ⟨hpstrip, hpc⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpstrip).1, hpc⟩
    _ = ((strip P R y).image (spatialCell R)).card * C := by simp

lemma quotient_card_le_reference_strip {α : Type*} {ℓ : ℕ}
    (v : α → Grid ℓ) {A E : Finset α} (hEA : E ⊆ A) (R C : ℕ) (y : Normal ℓ)
    (hcap : ∀ c, ((A.image v).filter (fun p => spatialCell R p = c)).card ≤ C) :
    (quotientBall E v R y).card ≤
      ((strip (A.image v) R y).image (spatialCell R)).card * C := by
  classical
  have hsub : quotientBall E v R y ⊆ (strip (A.image v) R y).image Prod.snd := by
    intro z hz
    obtain ⟨hzE, hzclose⟩ := Finset.mem_filter.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzE
    exact Finset.mem_image.mpr ⟨v a,
      Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem v (hEA ha), hzclose⟩, rfl⟩
  exact ((Finset.card_le_card hsub).trans (Finset.card_image_le)).trans
    (strip_card_le_cells_mul_capacity (A.image v) R C y hcap)

/-- A rich final spatial class gives many DISTINCT quotient vertices: its
floor cell lies in the centered quotient ball, and singleton normal fibers
make projection injective on the geometric image. -/
lemma spatial_degree_le_quotient_card {α : Type*} {ℓ R : ℕ}
    (w : α → ℕ) (v : α → Grid ℓ) {A E : Finset α} (hEA : E ⊆ A)
    (hinj : Set.InjOn Prod.snd (↑(E.image v) : Set (Grid ℓ))) (hR : 0 < R) (U : ℕ)
    (hcap : ∀ p, mass w (A.filter (fun a => v a = p)) ≤ U) (a : α) :
    degree w (fun x y => spatialCell R (v x) = spatialCell R (v y)) E a ≤
      U * (quotientBall E v R (v a).2).card := by
  classical
  let S := E.filter (fun b => spatialCell R (v b) = spatialCell R (v a))
  have hSE : S ⊆ E := Finset.filter_subset _ _
  have hdegree : degree w (fun x y => spatialCell R (v x) = spatialCell R (v y)) E a =
      mass w S := by
    simp only [degree, mass, S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _hb
    exact ite_congr (propext eq_comm) (fun _ => rfl) (fun _ => rfl)
  have hcard : (S.image v).card ≤ (quotientBall E v R (v a).2).card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hbE, hbc⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem (fun b => (v b).2) hbE, (same_spatialCell_close hR hbc).2⟩
    · intro p hp q hq hpq
      exact hinj ((Finset.image_subset_image hSE) hp) ((Finset.image_subset_image hSE) hq) hpq
  rw [hdegree]
  exact (mass_le_vertex_cap_mul_card w v (hSE.trans hEA) U hcap).trans
    (Nat.mul_le_mul_left U hcard)

/-- Singleton normal fibers are actual singleton sets of geometric vertices. -/
lemma normal_fiber_eq_singleton {ℓ : ℕ} (P : Finset (Grid ℓ))
    (hinj : Set.InjOn Prod.snd (↑P : Set (Grid ℓ))) {p : Grid ℓ} (hp : p ∈ P) :
    P.filter (fun q => q.2 = p.2) = {p} := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨hqP, hqp⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_singleton.mpr (hinj hqP hp hqp)
  · intro hq
    rw [Finset.mem_singleton.mp hq]
    exact Finset.mem_filter.mpr ⟨hp, rfl⟩

/-- Construct the small-fiber alignment set on a literal lattice. The existing
weighted selector chooses one geometric vertex per normal column, retaining
original-label mass with loss `F`; one final self-uniform refinement supplies
all spatial lower counts. Full reference strips supply the upper counts.

All menus, capacities, and inverse-image masses refer to the original set.
No aligned set, quotient AD assertion, or point-line shadow is an input. -/
theorem construct_singleton_quotient {α : Type*} {ℓ d Q L : ℕ}
    (hd : 0 < d) (hQ : 4 ≤ Q) (w : α → ℕ) (A : Finset α)
    (v : α → Grid ℓ) (R C : Fin d → ℕ) (F U : ℕ)
    (hne : A.Nonempty) (hw : ∀ a ∈ A, 0 < w a)
    (hheight : mass w A ≤ Q ^ L) (hR : ∀ j, 0 < R j)
    (hvertex : ∀ p, mass w (A.filter (fun a => v a = p)) ≤ U)
    (hcolumn : ∀ y, ((A.filter (fun a => (v a).2 = y)).image v).card ≤ F)
    (hcell : ∀ j c, ((A.image v).filter (fun p => spatialCell (R j) p = c)).card ≤ C j) :
    ∃ E ⊆ A, E.Nonempty ∧
      Set.InjOn Prod.snd (↑(E.image v) : Set (Grid ℓ)) ∧
      mass w A ≤ F * retentionCost d L * mass w E ∧
      ∀ j a, a ∈ E →
        (mass w A ≤ F * retentionCost d L * Q ^ 2 *
          (A.image (fun b => spatialCell (R j) (v b))).card * U *
          (quotientBall E v (R j) (v a).2).card) ∧
        ((quotientBall E v (R j) (v a).2).card ≤
          ((strip (A.image v) (R j) (v a).2).image (spatialCell (R j))).card * C j) := by
  classical
  obtain ⟨B, hBA, hBmass, hBsingle⟩ :=
    CompatibleTupleSelection.weighted_spatial_selection w A (fun a => (v a).2) v F hcolumn
  have hBpos : 0 < mass w B := by
    have hApos := mass_pos w hne hw
    by_contra h
    have hz : mass w B = 0 := by omega
    rw [hz, Nat.mul_zero] at hBmass
    omega
  let rel : Fin d → α → α → Prop := fun j x y => spatialCell (R j) (v x) = spatialCell (R j) (v y)
  obtain ⟨E, hEB, hEne, hEmass, hEuniform⟩ :=
    weighted_self_uniform_refinement hd hQ w rel (fun _ _ => rfl) (fun _ _ _ h => h.symm)
      B (nonempty_of_mass_pos w hBpos) (fun a ha => hw a (hBA ha))
      ((mass_mono w hBA).trans hheight)
  have hEA : E ⊆ A := hEB.trans hBA
  have hinj : Set.InjOn Prod.snd (↑(E.image v) : Set (Grid ℓ)) := by
    intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    exact hBsingle a b (hEB ha) (hEB hb) hpq
  have hret : mass w A ≤ F * retentionCost d L * mass w E := by
    calc
      mass w A ≤ F * mass w B := hBmass
      _ ≤ F * (retentionCost d L * mass w E) := Nat.mul_le_mul_left F hEmass
      _ = F * retentionCost d L * mass w E := by ring
  refine ⟨E, hEA, hEne, hinj, hret, ?_⟩
  intro j a ha
  constructor
  · have hrich := partition_richness_of_self_uniform w (fun b => spatialCell (R j) (v b)) Q
      hEA (hEuniform j) ha
    have hdegree := spatial_degree_le_quotient_card w v hEA hinj (hR j) U hvertex a
    calc
      mass w A ≤ F * retentionCost d L * mass w E := hret
      _ ≤ F * retentionCost d L *
          (Q ^ 2 * (A.image (fun b => spatialCell (R j) (v b))).card *
            degree w (rel j) E a) := Nat.mul_le_mul_left _ hrich
      _ ≤ F * retentionCost d L *
          (Q ^ 2 * (A.image (fun b => spatialCell (R j) (v b))).card *
            (U * (quotientBall E v (R j) (v a).2).card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hdegree)
      _ = F * retentionCost d L * Q ^ 2 *
          (A.image (fun b => spatialCell (R j) (v b))).card * U *
          (quotientBall E v (R j) (v a).2).card := by ring
  · exact quotient_card_le_reference_strip v hEA (R j) (C j) (v a).2 (hcell j)

/-- The small-`s` lattice alignment estimate with actual real power profiles.
The quotient consists of the normal projections of unchanged original labels,
and its geometric fibers are literal singletons. The loss contains the
explicit factor `H * N^s`; `retentionCost d L` is the one uniform-refinement
loss and `Q^2` is its comparison factor.

The lower quotient AD bound and the original-mass retention are stated by
cross multiplication. Spatial menus and full-strip menus are directly counted
on the original reference image. The column and spatial-cell populations are bounded directly by the real
tube/AD profiles; natural-number bounds are constructed by taking floors. -/
theorem small_fiber_quotient_AD {α : Type*} {ℓ d Q L : ℕ}
    (hd : 0 < d) (hQ : 4 ≤ Q) (w : α → ℕ) (A : Finset α)
    (v : α → Grid ℓ) (R : Fin d → ℕ) (U N : ℕ)
    (t s density H B₀ B₃ : ℝ)
    (hne : A.Nonempty) (hw : ∀ a ∈ A, 0 < w a)
    (hheight : mass w A ≤ Q ^ L) (hR : ∀ j, 0 < R j ∧ R j ≤ N)
    (hU : 0 < U) (hN : 0 < N) (_hdensity : 0 < density)
    (hs : 0 ≤ s) (hH : 0 ≤ H) (_hB₀ : 0 ≤ B₀) (hB₃ : 0 ≤ B₃)
    (hvertex : ∀ p, mass w (A.filter (fun a => v a = p)) ≤ U)
    (hcolumn : ∀ y, (((A.filter (fun a => (v a).2 = y)).image v).card : ℝ) ≤ H * (N : ℝ) ^ s)
    (hcell : ∀ j c, (((A.image v).filter (fun p => spatialCell (R j) p = c)).card : ℝ) ≤
      B₃ * (R j : ℝ) ^ t)
    (hmass : density * (U : ℝ) * (N : ℝ) ^ t ≤ (mass w A : ℝ))
    (hmenu : ∀ j, ((A.image (fun a => spatialCell (R j) (v a))).card : ℝ) ≤
      B₀ * ((N : ℝ) / (R j : ℝ)) ^ t)
    (hstrip : ∀ j y,
      (((strip (A.image v) (R j) y).image (spatialCell (R j))).card : ℝ) ≤
        H * ((N : ℝ) / (R j : ℝ)) ^ s) :
    ∃ E ⊆ A, E.Nonempty ∧
      Set.InjOn Prod.snd (↑(E.image v) : Set (Grid ℓ)) ∧
      (mass w A : ℝ) ≤ H * (N : ℝ) ^ s * (retentionCost d L : ℝ) * (mass w E : ℝ) ∧
      ∀ j y, y ∈ E.image (fun a => (v a).2) →
        (density * (R j : ℝ) ^ t ≤
          H * (N : ℝ) ^ s * (retentionCost d L : ℝ) * (Q : ℝ) ^ 2 * B₀ *
            ((quotientBall E v (R j) y).card : ℝ)) ∧
        (((quotientBall E v (R j) y).card : ℝ) ≤ H * B₃ * (N : ℝ) ^ s * (R j : ℝ) ^ t) := by
  classical
  let F : ℕ := ⌊H * (N : ℝ) ^ s⌋₊
  let C : Fin d → ℕ := fun j => ⌊B₃ * (R j : ℝ) ^ t⌋₊
  have hF : (F : ℝ) ≤ H * (N : ℝ) ^ s := Nat.floor_le (by positivity)
  have hcapacity : ∀ j, (C j : ℝ) ≤ B₃ * (R j : ℝ) ^ t := fun _ => Nat.floor_le (by positivity)
  have hcolumnNat : ∀ y, ((A.filter (fun a => (v a).2 = y)).image v).card ≤ F :=
    fun y => Nat.le_floor (hcolumn y)
  have hcellNat : ∀ j c, ((A.image v).filter (fun p => spatialCell (R j) p = c)).card ≤ C j :=
    fun j c => Nat.le_floor (hcell j c)
  obtain ⟨E, hEA, hEne, hinj, hret, hlocal⟩ :=
    construct_singleton_quotient hd hQ w A v R C F U hne hw hheight
      (fun j => (hR j).1) hvertex hcolumnNat hcellNat
  refine ⟨E, hEA, hEne, hinj, ?_, ?_⟩
  · have hret' : (mass w A : ℝ) ≤
        (F : ℝ) * (retentionCost d L : ℝ) * (mass w E : ℝ) := by exact_mod_cast hret
    apply hret'.trans
    gcongr
  · intro j y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hlower, hupper⟩ := hlocal j a ha
    have hU' : (0 : ℝ) < U := by exact_mod_cast hU
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hR' : (0 : ℝ) < R j := by exact_mod_cast (hR j).1
    have hRt := Real.rpow_pos_of_pos hR' t
    have hNt := Real.rpow_pos_of_pos hN' t
    have hNs := Real.rpow_pos_of_pos hN' s
    have hratio : ((N : ℝ) / (R j : ℝ)) ^ t * (R j : ℝ) ^ t = (N : ℝ) ^ t := by
      rw [Real.div_rpow hN'.le hR'.le]
      exact div_mul_cancel₀ _ (ne_of_gt hRt)
    constructor
    · have hlower' : (mass w A : ℝ) ≤
          (F : ℝ) * (retentionCost d L : ℝ) * (Q : ℝ) ^ 2 *
            ((A.image (fun b => spatialCell (R j) (v b))).card : ℝ) * (U : ℝ) *
              ((quotientBall E v (R j) (v a).2).card : ℝ) := by exact_mod_cast hlower
      have hchain : density * (U : ℝ) * (N : ℝ) ^ t ≤
          (H * (N : ℝ) ^ s) * (retentionCost d L : ℝ) * (Q : ℝ) ^ 2 *
            (B₀ * ((N : ℝ) / (R j : ℝ)) ^ t) * (U : ℝ) *
              ((quotientBall E v (R j) (v a).2).card : ℝ) := by
        apply hmass.trans (hlower'.trans ?_)
        gcongr
        exact hmenu j
      have hscaled : ((U : ℝ) * (N : ℝ) ^ t) * (density * (R j : ℝ) ^ t) ≤
          ((U : ℝ) * (N : ℝ) ^ t) *
            (H * (N : ℝ) ^ s * (retentionCost d L : ℝ) * (Q : ℝ) ^ 2 * B₀ *
              ((quotientBall E v (R j) (v a).2).card : ℝ)) := by
        calc
          ((U : ℝ) * (N : ℝ) ^ t) * (density * (R j : ℝ) ^ t) =
              (density * (U : ℝ) * (N : ℝ) ^ t) * (R j : ℝ) ^ t := by ring
          _ ≤ ((H * (N : ℝ) ^ s) * (retentionCost d L : ℝ) * (Q : ℝ) ^ 2 *
              (B₀ * ((N : ℝ) / (R j : ℝ)) ^ t) * (U : ℝ) *
                ((quotientBall E v (R j) (v a).2).card : ℝ)) * (R j : ℝ) ^ t :=
            mul_le_mul_of_nonneg_right hchain hRt.le
          _ = ((U : ℝ) * (((N : ℝ) / (R j : ℝ)) ^ t * (R j : ℝ) ^ t)) *
              (H * (N : ℝ) ^ s * (retentionCost d L : ℝ) * (Q : ℝ) ^ 2 * B₀ *
                ((quotientBall E v (R j) (v a).2).card : ℝ)) := by ring
          _ = ((U : ℝ) * (N : ℝ) ^ t) *
              (H * (N : ℝ) ^ s * (retentionCost d L : ℝ) * (Q : ℝ) ^ 2 * B₀ *
                ((quotientBall E v (R j) (v a).2).card : ℝ)) := by rw [hratio]
      exact (mul_le_mul_iff_right₀ (mul_pos hU' hNt)).mp hscaled
    · have hupper' : ((quotientBall E v (R j) (v a).2).card : ℝ) ≤
          (((strip (A.image v) (R j) (v a).2).image (spatialCell (R j))).card : ℝ) * (C j : ℝ) :=
        by exact_mod_cast hupper
      have hRone : (1 : ℝ) ≤ R j := by exact_mod_cast (Nat.succ_le_of_lt (hR j).1)
      have hratioS : ((N : ℝ) / (R j : ℝ)) ^ s ≤ (N : ℝ) ^ s :=
        Real.rpow_le_rpow (by positivity) (div_le_self hN'.le hRone) hs
      calc
        ((quotientBall E v (R j) (v a).2).card : ℝ) ≤
            (((strip (A.image v) (R j) (v a).2).image (spatialCell (R j))).card : ℝ) * (C j : ℝ) := hupper'
        _ ≤ (H * ((N : ℝ) / (R j : ℝ)) ^ s) * (B₃ * (R j : ℝ) ^ t) := by
          gcongr
          · exact hstrip j (v a).2
          · exact hcapacity j
        _ ≤ (H * (N : ℝ) ^ s) * (B₃ * (R j : ℝ) ^ t) := by gcongr
        _ = H * B₃ * (N : ℝ) ^ s * (R j : ℝ) ^ t := by ring

end SmallFiberAlignment
