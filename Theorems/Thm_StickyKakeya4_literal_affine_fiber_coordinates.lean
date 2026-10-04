import Theorems.Thm_StickyKakeya4_normalized_quantized_patches

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace LiteralAffineFiberCoordinates

open NativeDyadicTubeStopping ShearedGridADReference SmallFiberAlignment FractionalFiberAlignment
open NativeFractionalReferenceComposition NormalizedQuantizedPatches
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

def timeCoord (μ shift L : ℝ) (k : ℤ) : ℝ := (μ * (k : ℝ) - shift) / L

def normalCoord (μ angle L : ℝ) (c : Plane) (y : Normal 1) : ℝ :=
  (μ * (y 0 : ℝ) - c 1 + angle * c 0) / L

def fiberCoordinates (P : Finset Vertex) (μ L : ℝ) (c : Plane) (y : Normal 1) : Finset ℝ :=
  (fiber P y).image (fun k => timeCoord μ (c 0) L k.1)

def quotientCoordinates (P : Finset Vertex) (μ angle L : ℝ) (c : Plane) : Finset ℝ :=
  (P.image Prod.snd).image (normalCoord μ angle L c)

lemma actual_affine_graph (μ angle L : ℝ) (c : Plane) (k : Vertex) :
    affine c L (realized μ angle k) =
      ![timeCoord μ (c 0) L k.1, angle * timeCoord μ (c 0) L k.1 + normalCoord μ angle L c k.2] := by
  funext i
  fin_cases i
  · rfl
  · change (μ * (k.2 0 : ℝ) + angle * (μ * (k.1 : ℝ)) - c 1) / L =
      angle * ((μ * (k.1 : ℝ) - c 0) / L) + (μ * (k.2 0 : ℝ) - c 1 + angle * c 0) / L
    ring

lemma timeCoord_dist (μ shift L : ℝ) (hμ : 0 < μ) (hL : 0 < L) (k l : ℤ) :
    dist (timeCoord μ shift L k) (timeCoord μ shift L l) = (μ / L) * (|k - l| : ℤ) := by
  rw [Real.dist_eq]
  have he : timeCoord μ shift L k - timeCoord μ shift L l = (μ / L) * ((k : ℝ) - (l : ℝ)) := by
    unfold timeCoord
    ring
  rw [he, abs_mul, abs_of_pos (div_pos hμ hL)]
  norm_cast

lemma timeCoord_injective (μ shift L : ℝ) (hμ : 0 < μ) (hL : 0 < L) :
    Function.Injective (timeCoord μ shift L) := by
  intro k l he
  have hd := timeCoord_dist μ shift L hμ hL k l
  rw [he, dist_self] at hd
  have hzero : (|k - l| : ℤ) = 0 := by
    have hh : ((|k - l| : ℤ) : ℝ) = 0 := (mul_eq_zero.mp hd.symm).resolve_left (div_pos hμ hL).ne'
    exact_mod_cast hh
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

lemma normalCoord_as_time (μ angle L : ℝ) (c : Plane) (y : Normal 1) :
    normalCoord μ angle L c y = timeCoord μ (c 1 - angle * c 0) L (y 0) := by
  unfold normalCoord timeCoord
  ring

lemma normalCoord_injective (μ angle L : ℝ) (c : Plane) (hμ : 0 < μ) (hL : 0 < L) :
    Function.Injective (normalCoord μ angle L c) := by
  intro y z he
  rw [normalCoord_as_time, normalCoord_as_time] at he
  have hh := timeCoord_injective μ _ L hμ hL he
  funext i
  fin_cases i
  exact hh

lemma timeCoord_close_iff (μ shift L : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (k l : ℤ) (R : ℕ) :
    dist (timeCoord μ shift L k) (timeCoord μ shift L l) ≤ (μ / L) * (R : ℝ) ↔
      |k - l| ≤ (R : ℤ) := by
  rw [timeCoord_dist μ shift L hμ hL, mul_le_mul_iff_right₀ (div_pos hμ hL)]
  exact_mod_cast (Iff.rfl : |k - l| ≤ (R : ℤ) ↔ |k - l| ≤ (R : ℤ))

lemma normalCoord_close_iff (μ angle L : ℝ) (c : Plane) (hμ : 0 < μ) (hL : 0 < L)
    (y z : Normal 1) (R : ℕ) :
    dist (normalCoord μ angle L c y) (normalCoord μ angle L c z) ≤ (μ / L) * (R : ℝ) ↔
      normalClose R y z := by
  rw [normalCoord_as_time, normalCoord_as_time, timeCoord_close_iff μ _ L hμ hL]
  constructor
  · intro h i
    fin_cases i
    exact h
  · intro h
    exact h 0

lemma fiber_time_injOn (P : Finset Vertex) (μ L : ℝ) (c : Plane) (y : Normal 1)
    (hμ : 0 < μ) (hL : 0 < L) :
    Set.InjOn (fun k : Vertex => timeCoord μ (c 0) L k.1) (fiber P y) := by
  intro k hk l hl he
  have hnormal : k.2 = l.2 :=
    (Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hl).2.symm
  exact Prod.ext (timeCoord_injective μ _ L hμ hL he) hnormal

lemma fiberCoordinates_card (P : Finset Vertex) (μ L : ℝ) (c : Plane) (y : Normal 1)
    (hμ : 0 < μ) (hL : 0 < L) :
    (fiberCoordinates P μ L c y).card = (fiber P y).card :=
  Finset.card_image_iff.mpr (fiber_time_injOn P μ L c y hμ hL)

lemma quotientCoordinates_card (P : Finset Vertex) (μ angle L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) :
    (quotientCoordinates P μ angle L c).card = (P.image Prod.snd).card :=
  Finset.card_image_of_injective _ (normalCoord_injective μ angle L c hμ hL)

/-- Exact physical closed balls at the working radii, on the actual scalar
fiber coordinate image. Injectivity is used only for DISTINCT vertex labels. -/
theorem fiberCoordinates_ball_card (P : Finset Vertex) (μ L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) (p : Vertex) (R : ℕ) :
    ((fiberCoordinates P μ L c p.2).filter
      (fun x => dist x (timeCoord μ (c 0) L p.1) ≤ (μ / L) * (R : ℝ))).card =
      (fiberBall P R p).card := by
  classical
  have he : (fiberCoordinates P μ L c p.2).filter
      (fun x => dist x (timeCoord μ (c 0) L p.1) ≤ (μ / L) * (R : ℝ)) =
      (fiberBall P R p).image (fun k => timeCoord μ (c 0) L k.1) := by
    ext x
    simp only [fiberCoordinates, fiber, fiberBall, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨k, ⟨hk, hy⟩, rfl⟩, hd⟩
      exact ⟨k, ⟨hk, hy, (timeCoord_close_iff μ _ L hμ hL k.1 p.1 R).mp hd⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hy, hd⟩, rfl⟩
      exact ⟨⟨k, ⟨hk, hy⟩, rfl⟩, (timeCoord_close_iff μ _ L hμ hL k.1 p.1 R).mpr hd⟩
  rw [he]
  apply Finset.card_image_iff.mpr
  intro k hk l hl heq
  exact fiber_time_injOn P μ L c p.2 hμ hL
    (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2.1⟩)
    (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hl).1, (Finset.mem_filter.mp hl).2.1⟩) heq

theorem quotientCoordinates_ball_card (P : Finset Vertex) (μ angle L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) (y : Normal 1) (R : ℕ) :
    ((quotientCoordinates P μ angle L c).filter
      (fun z => dist z (normalCoord μ angle L c y) ≤ (μ / L) * (R : ℝ))).card =
      (normalBall P R y).card := by
  classical
  have he : (quotientCoordinates P μ angle L c).filter
      (fun z => dist z (normalCoord μ angle L c y) ≤ (μ / L) * (R : ℝ)) =
      (normalBall P R y).image (normalCoord μ angle L c) := by
    ext x
    simp only [quotientCoordinates, normalBall, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨y', hy', rfl⟩, hd⟩
      exact ⟨y', ⟨hy', (normalCoord_close_iff μ angle L c hμ hL y' y R).mp hd⟩, rfl⟩
    · rintro ⟨y', ⟨hy', hd⟩, rfl⟩
      exact ⟨⟨y', hy', rfl⟩, (normalCoord_close_iff μ angle L c hμ hL y' y R).mpr hd⟩
  rw [he, Finset.card_image_of_injective _ (normalCoord_injective μ angle L c hμ hL)]

/-- The native fractional conclusion is read on its literal scalar X and Y,
with the physical radius μR/L. No original-point injectivity is used. -/
theorem actual_working_ball_bounds {d : ℕ} (P : Finset Vertex) (R : Fin d → ℕ)
    (N Q H : ℕ) (t s dens Bad Bcolumn Btube μ angle L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L)
    (hcounts : RefinedCounts P R N Q H t s dens Bad Bcolumn Btube) :
    ∀ p ∈ P,
      (dens * (N : ℝ) ^ s ≤ comparisonCost d H Q * Bcolumn * (fiberCoordinates P μ L c p.2).card) ∧
      ∀ j,
        let X := (fiberCoordinates P μ L c p.2).filter
          (fun x => dist x (timeCoord μ (c 0) L p.1) ≤ (μ / L) * (R j : ℝ))
        let Y := (quotientCoordinates P μ angle L c).filter
          (fun y => dist y (normalCoord μ angle L c p.2) ≤ (μ / L) * (R j : ℝ))
        (dens * (R j : ℝ) ^ s ≤ comparisonCost d H Q * Bcolumn * Btube * X.card) ∧
        ((X.card : ℝ) ≤ Btube * (R j : ℝ) ^ s) ∧
        (dens * (R j : ℝ) ^ (t - s) ≤ comparisonCost d H Q * Bad * Btube * Y.card) ∧
        (dens * (Y.card : ℝ) ≤ comparisonCost d H Q * Bcolumn * Bad * Btube * (R j : ℝ) ^ (t - s)) := by
  intro p hp
  have hh := hcounts p hp
  constructor
  · rw [fiberCoordinates_card P μ L c p.2 hμ hL]
    exact hh.1
  · intro j
    dsimp only
    rw [fiberCoordinates_ball_card P μ L c hμ hL, quotientCoordinates_ball_card P μ angle L c hμ hL]
    exact ⟨(hh.2 j).2.2.1, (hh.2 j).2.2.2.1, (hh.2 j).2.2.2.2.1, (hh.2 j).2.2.2.2.2⟩

/-- Original AD controls the ENTIRE vertex image of one parent directly.
This supplies large-radius upper bounds without claiming a radius-N normal
ball contains every column. -/
theorem actual_global_vertex_card (A Ω : Finset Plane) (hΩ : Ω ⊆ A)
    {δ μ b angle K t : ℝ} {N : ℕ} (hδ : 0 < δ) (hμ : 0 < μ)
    (hδa : δ ≤ 64 * μ) (hab : 64 * μ ≤ b) (hb : b ≤ 1)
    (hangle : |angle| ≤ 1) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t)
    (hparent : ∀ p ∈ Ω, ∀ q ∈ Ω, dist p q ≤ b) (hNscale : μ * (N : ℝ) = b) :
    ((Ω.image (vertex μ angle)).card : ℝ) ≤ adConstant K t * (N : ℝ) ^ t := by
  have hg := ADGridCoverMenus.diameter_subset_occupied_grid_cells_le A Ω
    hδ hδa (hab.trans hb) hab hK ht ht2 hdiam hAD hΩ hparent
  have hq : ((Ω.image (vertex μ angle)).card : ℝ) ≤
      ((Ω.image (ADGridCoverMenus.gridLabel (64 * μ))).card : ℝ) * 513 ^ 2 := by
    exact_mod_cast vertex_image_card_le_grid μ angle hμ hangle Ω
  have hratio : b / (64 * μ) ≤ (N : ℝ) := by
    rw [← hNscale]
    apply (div_le_iff₀ (by positivity : 0 < 64 * μ)).mpr
    have hNN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith only [mul_nonneg hμ.le hNN]
  have hbpos : 0 < b := (by positivity : 0 < 64 * μ).trans_le hab
  have hp := Real.rpow_le_rpow (div_nonneg hbpos.le (by positivity : 0 ≤ 64 * μ)) hratio ht
  have hcoeff : 0 ≤ adConstant K t := by unfold adConstant referenceFactor; positivity
  calc
    _ ≤ (((9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2) * (b / (64 * μ)) ^ t) * 513 ^ 2 :=
      hq.trans (mul_le_mul_of_nonneg_right hg (by norm_num))
    _ = adConstant K t * (b / (64 * μ)) ^ t := by unfold adConstant referenceFactor; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hcoeff

theorem global_quotient_from_fibers (P : Finset Vertex) {N : ℕ} (hN : 0 < N)
    (s t dens C Bad : ℝ) (hC : 0 ≤ C)
    (hglobal : (P.card : ℝ) ≤ Bad * (N : ℝ) ^ t)
    (hfibers : ∀ p ∈ P, dens * (N : ℝ) ^ s ≤ C * ((fiber P p.2).card : ℝ)) :
    dens * ((P.image Prod.snd).card : ℝ) ≤ C * Bad * (N : ℝ) ^ (t - s) := by
  classical
  have hsum : ∑ y ∈ P.image Prod.snd, ((fiber P y).card : ℝ) = (P.card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image Prod.snd P).symm
  have hh : ((P.image Prod.snd).card : ℝ) * (dens * (N : ℝ) ^ s) ≤ C * (P.card : ℝ) := by
    calc
      _ = ∑ _y ∈ P.image Prod.snd, dens * (N : ℝ) ^ s := by simp
      _ ≤ ∑ y ∈ P.image Prod.snd, C * ((fiber P y).card : ℝ) := by
        apply Finset.sum_le_sum
        intro y hy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
        exact hfibers p hp
      _ = _ := by rw [← Finset.mul_sum, hsum]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (t - s) * (N : ℝ) ^ s = (N : ℝ) ^ t := by
    rw [← Real.rpow_add hNR]
    congr 1
    ring
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hNR s)).mp
  calc
    _ = ((P.image Prod.snd).card : ℝ) * (dens * (N : ℝ) ^ s) := by ring
    _ ≤ C * (P.card : ℝ) := hh
    _ ≤ C * (Bad * (N : ℝ) ^ t) := mul_le_mul_of_nonneg_left hglobal hC
    _ = _ := by rw [← hpow]; ring

def fiberAt (P : Finset Vertex) (μ angle L : ℝ) (c : Plane) (y : ℝ) : Finset ℝ :=
  (P.filter (fun k => normalCoord μ angle L c k.2 = y)).image (fun k => timeCoord μ (c 0) L k.1)

lemma fiberAt_normalCoord (P : Finset Vertex) (μ angle L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) (y : Normal 1) :
    fiberAt P μ angle L c (normalCoord μ angle L c y) = fiberCoordinates P μ L c y := by
  have he : P.filter (fun k => normalCoord μ angle L c k.2 = normalCoord μ angle L c y) = fiber P y := by
    ext k
    simp only [Finset.mem_filter, fiber, (normalCoord_injective μ angle L c hμ hL).eq_iff]
  exact congrArg (fun F : Finset Vertex => F.image (fun k => timeCoord μ (c 0) L k.1)) he

/-- The normalized point set is LITERALLY the union of its scalar graph
fibers over its scalar normal-coordinate image. -/
theorem actual_image_eq_graph_fibers (P : Finset Vertex) (μ angle L : ℝ) (c : Plane) :
    P.image (fun k => affine c L (realized μ angle k)) =
      (quotientCoordinates P μ angle L c).biUnion
        (fun y => (fiberAt P μ angle L c y).image (fun x => ![x, angle * x + y])) := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_biUnion, quotientCoordinates, fiberAt, Finset.mem_filter]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨normalCoord μ angle L c k.2, ⟨k.2, ⟨k, hk, rfl⟩, rfl⟩,
      timeCoord μ (c 0) L k.1, ⟨k, ⟨hk, rfl⟩, rfl⟩, ?_⟩
    exact (actual_affine_graph μ angle L c k).symm
  · rintro ⟨y, _hy, x, ⟨k, ⟨hk, hky⟩, hkx⟩, hz⟩
    refine ⟨k, hk, ?_⟩
    rw [actual_affine_graph, hky, hkx]
    exact hz

end
end LiteralAffineFiberCoordinates
