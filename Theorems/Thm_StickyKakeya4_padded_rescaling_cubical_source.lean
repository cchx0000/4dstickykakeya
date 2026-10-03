import Theorems.Thm_StickyKakeya4_physical_rescaling_backbone_density
import Theorems.Thm_StickyKakeya4_padded_physical_cell_witness
import Theorems.Thm_StickyKakeya4_native_graph_marked_line
import Theorems.Thm_StickyKakeya4_wz_carrier_pruning

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

noncomputable section
open Classical Finset Set MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace StickyKakeya4.PaddedRescalingCubicalSource

abbrev Cell := PhysicalRescalingIncidenceTransfer.Cell
abbrev Index := Fin 4 → ℤ

local instance : DecidableEq Index := Classical.decEq _

/-- Spatial coordinates first, actual time last. -/
def encode (c : Cell) : Index := Fin.lastCases c.2 c.1

def decode (d : Index) : Cell := (fun j => d j.castSucc, d (Fin.last 3))

@[simp] theorem decode_encode (c : Cell) : decode (encode c) = c := by
  apply Prod.ext
  · funext j
    simp [decode, encode]
  · change Fin.lastCases c.2 c.1 (Fin.last 3) = c.2
    exact Fin.lastCases_last (motive := fun _ : Fin 4 => ℤ) (last := c.2) (cast := c.1)

theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

variable {n : ℕ} (P : PhysicalRescalingIncidenceTransfer.Data (Fin n))

local instance : DecidableEq (Fin n) := Classical.decEq _

def point (c : Cell) : E4 :=
  ActualSlopeSource.heightPoint (WithLp.toLp 2 (P.center c).1) (P.center c).2

def fine (c : Cell) : Index := encode (P.cellBin c)

def fineBins : Finset Index := P.keptIncidences.image (fun p => fine P p.2)
def binWeight (d : Index) : ℕ := (P.keptIncidences.filter (fun p => fine P p.2 = d)).card

def retained (G : Finset Index) : Finset (Fin n × Cell) :=
  P.keptIncidences.filter (fun p => fine P p.2 ∈ G)

def coarse (R q : ℕ) (c : Cell) : Index := fun j => (fine P c j + q) / (64 * R : ℕ)
def mesh (R : ℕ) : ℝ := ((64 * R : ℕ) : ℝ) * P.σ / 8

def cells (R q : ℕ) (G : Finset Index) (i : Fin n) : Finset Index :=
  ((retained P G).filter (fun p => p.1 = i)).image (fun p => coarse P R q p.2)

def shading (R q : ℕ) (G : Finset Index) (i : Fin n) : Set E4 :=
  wzCellShading (mesh P R) (cells P R q G) i

def graphSlope (i : Fin n) : E3 := WithLp.toLp 2 (P.slope i)

def graphIntercept (q : ℕ) (i : Fin n) : E3 :=
  WithLp.toLp 2 (fun j => (P.offset i j + (q : ℝ) * P.σ - P.slope i j * ((q : ℝ) * P.σ)) / 8)

def centerHeight (q : ℕ) : ℝ := (q : ℝ) * P.σ / 8

def line (q : ℕ) (i : Fin n) : MarkedLine :=
  NativeGraphMarkedLine.ofGraph (graphSlope P i) (graphIntercept P q i) (centerHeight P q)

@[simp] theorem fine_apply (c : Cell) (j : Fin 4) :
    fine P c j = ⌊point P c j / P.σ⌋ := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [fine, encode, Fin.lastCases_last, point, ActualSlopeSource.heightPoint_last]
    rfl
  · simp only [fine, encode, Fin.lastCases_castSucc, point, ActualSlopeSource.heightPoint_castSucc]
    rfl

theorem retained_subset (G : Finset Index) : retained P G ⊆ P.incidences := by
  intro p hp
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1

/-- A finite cyclic translation selects entire global fine bins by their original incidence counts. -/
theorem exists_padding (R : ℕ) (hR : 0 < R) :
    ∃ q : Fin (64 * R), ∃ G : Finset Index, G ⊆ fineBins P ∧
      P.keptIncidences.card ≤ 2 * (retained P G).card ∧
      ∀ d ∈ G, ∀ j, 4 * (R : ℤ) ≤ (d j + (q.val : ℤ)) % (64 * R : ℕ) ∧
        (d j + (q.val : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ) := by
  obtain ⟨q, G, hG, hw, hpad⟩ := FiniteCyclicGridPadding.cyclic_translation
    (τ := Fin 4) (64 * R) 64 (by omega) (by norm_num)
    (fineBins P) (binWeight P) (fun d j => d j) (fun _ => R)
    (fun _ => hR) (fun _ => dvd_refl _) (by norm_num)
  have htotal : (∑ d ∈ fineBins P, binWeight P d) = P.keptIncidences.card := by
    simpa only [fineBins, binWeight] using
      (Finset.card_eq_sum_card_image (fun p => fine P p.2) P.keptIncidences).symm
  have hselected : (∑ d ∈ G, binWeight P d) = (retained P G).card := by
    simpa only [binWeight, retained] using
      Finset.sum_card_fiberwise_eq_card_filter P.keptIncidences G (fun p => fine P p.2)
  have hkeep : P.keptIncidences.card ≤ 2 * (retained P G).card := calc
    P.keptIncidences.card = ∑ d ∈ fineBins P, binWeight P d := htotal.symm
    _ ≤ 2 * ∑ d ∈ G, binWeight P d := hw
    _ = 2 * (retained P G).card := congrArg (fun v : ℕ => 2 * v) hselected
  exact ⟨q, G, hG, hkeep, fun d hd j => by simpa using hpad d hd j⟩

/-- Native graph parameters can be recovered from the native marked line. -/
theorem ofGraph_parameters_injective (a b a' b' : E3) (s₀ : ℝ)
    (h : NativeGraphMarkedLine.ofGraph a b s₀ = NativeGraphMarkedLine.ofGraph a' b' s₀) :
    a = a' ∧ b = b' := by
  have hzero := congrArg (fun l => wzGraphPoint l 0) h
  have hone := congrArg (fun l => wzGraphPoint l 1) h
  rw [NativeGraphMarkedLine.wzGraphPoint_eq_heightPoint,
    NativeGraphMarkedLine.wzGraphPoint_eq_heightPoint] at hzero hone
  have hb : b = b' := by
    ext j
    have hj := congrArg (fun x : E4 => x j.castSucc) hzero
    simpa using hj
  refine ⟨?_, hb⟩
  ext j
  have hj := congrArg (fun x : E4 => x j.castSucc) hone
  simp only [ActualSlopeSource.heightPoint_castSucc, one_smul, PiLp.add_apply, hb] at hj
  linarith

/-- Original affine-parameter injectivity survives the actual rescaling, translation, and marking. -/
theorem line_injective (hN : 0 < P.N)
    (hinj : Function.Injective (fun i => (P.tubeSlope i, P.tubeOffset i))) (q : ℕ) :
    Function.Injective (line P q) := by
  intro i k hik
  obtain ⟨ha, hb⟩ := ofGraph_parameters_injective
    (graphSlope P i) (graphIntercept P q i) (graphSlope P k) (graphIntercept P q k)
    (centerHeight P q) hik
  have hrho : P.ρ ≠ 0 := by
    dsimp [PhysicalRescalingIncidenceTransfer.Data.ρ]
    exact one_div_ne_zero (by exact_mod_cast Nat.ne_zero_of_lt hN)
  apply hinj
  apply Prod.ext
  · funext j
    have hs : P.slope i j = P.slope k j := congrArg (fun a : E3 => a j) ha
    have hs' := (div_left_inj' hrho).mp hs
    linarith
  · funext j
    have hs : P.slope i j = P.slope k j := congrArg (fun a : E3 => a j) ha
    have hi : P.offset i j = P.offset k j := by
      have hi' := congrArg (fun b : E3 => b j) hb
      change (P.offset i j + (q : ℝ) * P.σ - P.slope i j * ((q : ℝ) * P.σ)) / 8 =
        (P.offset k j + (q : ℝ) * P.σ - P.slope k j * ((q : ℝ) * P.σ)) / 8 at hi'
      rw [hs] at hi'
      linarith
    have hi' := (div_left_inj' hrho).mp hi
    linarith

/-- The complete original `Fin n` backbone, including empty shading rows. -/
def source (R q : ℕ) (G : Finset Index) (hN : 0 < P.N)
    (hinj : Function.Injective (fun i => (P.tubeSlope i, P.tubeOffset i))) : FiniteScaleSource n :=
  unweightedMarkedShadingSource (2 * mesh P R) (line P q) (line_injective P hN hinj q)
    (shading P R q G)

def axis (i : Fin n) (c : Cell) : E4 :=
  ActualSlopeSource.heightPoint
    (WithLp.toLp 2 (fun j => P.offset i j + P.slope i j * (P.center c).2)) (P.center c).2

def contract (q : ℕ) (x : E4) : E4 := WithLp.toLp 2 (fun j => (x j + (q : ℝ) * P.σ) / 8)

theorem mesh_pos (h : P.Hypotheses) (R : ℕ) (hR : 0 < R) : 0 < mesh P R := by
  have hσ := P.scale_pos h
  dsimp [mesh]
  positivity

theorem axis_near (h : P.Hypotheses) {p : Fin n × Cell} (hp : p ∈ P.incidences) :
    ∀ j, |axis P p.1 p.2 j - point P p.2 j| ≤ (P.E : ℝ) * P.σ := by
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [axis, point, ActualSlopeSource.heightPoint_last, sub_self, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (P.scale_pos h).le
  · have hh := h.physical_bound p hp k
    simp only [axis, point, ActualSlopeSource.heightPoint_castSucc]
    change |P.offset p.1 k + P.slope p.1 k * (P.center p.2).2 - (P.center p.2).1 k| ≤ _
    have he : P.offset p.1 k + P.slope p.1 k * (P.center p.2).2 - (P.center p.2).1 k =
        -P.residual p.1 p.2 k := by
      dsimp [PhysicalRescalingIncidenceTransfer.Data.residual]
      ring
    rw [he, abs_neg]
    exact hh

/-- The same physical axis point after the one global translation and contraction. -/
theorem contract_axis_eq_graph (q : ℕ) (i : Fin n) (c : Cell) :
    contract P q (axis P i c) =
      ActualSlopeSource.heightPoint
        (graphIntercept P q i + (((P.center c).2 + (q : ℝ) * P.σ) / 8) • graphSlope P i)
        (((P.center c).2 + (q : ℝ) * P.σ) / 8) := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [contract, PiLp.toLp_apply, axis, ActualSlopeSource.heightPoint_last]
  · simp only [contract, PiLp.toLp_apply, axis, ActualSlopeSource.heightPoint_castSucc,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, graphIntercept, graphSlope]
    ring

theorem contract_time_buffer (h : P.Hypotheses) (q : ℕ) {p : Fin n × Cell}
    (hp : p ∈ P.incidences) :
    |((P.center p.2).2 + (q : ℝ) * P.σ) / 8 - centerHeight P q| ≤ 1 / 8 := by
  have he : ((P.center p.2).2 + (q : ℝ) * P.σ) / 8 - centerHeight P q =
      (P.center p.2).2 / 8 := by dsimp [centerHeight]; ring
  rw [he, abs_div]
  norm_num
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 8)).mpr (h.time_bound p hp)

/-- Padding is used on the actual old center, then transfers to its actual graph-axis point. -/
theorem coarse_near_mem (h : P.Hypotheses) (R q : ℕ)
    (hR : (P.E : ℝ) + 1 ≤ (R : ℝ)) (G : Finset Index)
    (hpad : ∀ d ∈ G, ∀ j, 4 * (R : ℤ) ≤ (d j + (q : ℤ)) % (64 * R : ℕ) ∧
      (d j + (q : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ))
    {p : Fin n × Cell} (hp : p ∈ retained P G) (z : E4)
    (hz : ∀ j, |z j - point P p.2 j| ≤ (P.E : ℝ) * P.σ) :
    contract P q z ∈ wzDyadicCell (mesh P R) (coarse P R q p.2) := by
  have hpG : fine P p.2 ∈ G := (Finset.mem_filter.mp hp).2
  have hpadding : ∀ j, 4 * (R : ℤ) ≤ (⌊point P p.2 j / P.σ⌋ + (q : ℤ)) % (64 * R : ℕ) ∧
      (⌊point P p.2 j / P.σ⌋ + (q : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ) := by
    intro j
    simpa only [fine_apply] using hpad (fine P p.2) hpG j
  have hm := (PaddedPhysicalCellWitness.nearby_mem_same_halfOpenCell
    P.σ (P.E : ℝ) R q (fun j => point P p.2 j) (fun j => z j)
    (P.scale_pos h) (Nat.cast_nonneg _) hR hpadding hz).2
  have hbin : PaddedPhysicalCellWitness.bin ((64 * R : ℕ) * P.σ)
      (PaddedPhysicalCellWitness.translate P.σ q (fun j => point P p.2 j)) =
      coarse P R q p.2 := by
    funext j
    change ⌊(point P p.2 j + (q : ℝ) * P.σ) / ((64 * R : ℕ) * P.σ)⌋ = _
    rw [coarse, fine_apply]
    exact PaddedPhysicalCellWitness.nearby_floor_eq_quotient P.σ (P.E : ℝ)
      (point P p.2 j) (point P p.2 j) R q (P.scale_pos h) (Nat.cast_nonneg _) hR
      (hpadding j) (by simpa using mul_nonneg (Nat.cast_nonneg P.E) (P.scale_pos h).le)
  rw [hbin] at hm
  intro j
  have hj := hm j
  change ((coarse P R q p.2 j : ℝ) * mesh P R ≤
      (z j + (q : ℝ) * P.σ) / 8) ∧
    (z j + (q : ℝ) * P.σ) / 8 <
      ((coarse P R q p.2 j : ℝ) + 1) * mesh P R
  dsimp [PaddedPhysicalCellWitness.translate] at hj
  dsimp [mesh]
  constructor <;> nlinarith [hj.1, hj.2]

theorem coarse_axis_mem (h : P.Hypotheses) (R q : ℕ)
    (hR : (P.E : ℝ) + 1 ≤ (R : ℝ)) (G : Finset Index)
    (hpad : ∀ d ∈ G, ∀ j, 4 * (R : ℤ) ≤ (d j + (q : ℤ)) % (64 * R : ℕ) ∧
      (d j + (q : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ))
    {p : Fin n × Cell} (hp : p ∈ retained P G) :
    contract P q (axis P p.1 p.2) ∈ wzDyadicCell (mesh P R) (coarse P R q p.2) :=
  coarse_near_mem P h R q hR G hpad hp (axis P p.1 p.2)
    (axis_near P h (retained_subset P G hp))

/-- The actual retained old center is also covered by its unchanged global coarse cell. -/
theorem coarse_point_mem (h : P.Hypotheses) (R q : ℕ)
    (hR : (P.E : ℝ) + 1 ≤ (R : ℝ)) (G : Finset Index)
    (hpad : ∀ d ∈ G, ∀ j, 4 * (R : ℤ) ≤ (d j + (q : ℤ)) % (64 * R : ℕ) ∧
      (d j + (q : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ))
    {p : Fin n × Cell} (hp : p ∈ retained P G) :
    contract P q (point P p.2) ∈ wzDyadicCell (mesh P R) (coarse P R q p.2) := by
  apply coarse_near_mem P h R q hR G hpad hp (point P p.2)
  intro j
  simp only [sub_self, abs_zero]
  exact mul_nonneg (Nat.cast_nonneg _) (P.scale_pos h).le

/-- Every actual selected coarse cube has a buffered witness on its actual native unit segment. -/
theorem cell_has_marked_witness (h : P.Hypotheses)
    (hslope : ∀ i j, |P.slope i j| ≤ 1) (R q : ℕ)
    (hR : (P.E : ℝ) + 1 ≤ (R : ℝ)) (G : Finset Index)
    (hpad : ∀ d ∈ G, ∀ j, 4 * (R : ℤ) ≤ (d j + (q : ℤ)) % (64 * R : ℕ) ∧
      (d j + (q : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ))
    (i : Fin n) (k : Index) (hk : k ∈ cells P R q G i) :
    ∃ u : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      |(u : ℝ)| ≤ 1 / 4 ∧ rawFrontParam (line P q i, (u : ℝ)) ∈ wzDyadicCell (mesh P R) k := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hp, hpi⟩ := Finset.mem_filter.mp hp
  obtain ⟨u, hu, he⟩ := NativeGraphMarkedLine.graphPoint_has_buffered_parameter
    (graphSlope P i) (graphIntercept P q i) (centerHeight P q)
    (((P.center p.2).2 + (q : ℝ) * P.σ) / 8) (hslope i)
    (contract_time_buffer P h q (retained_subset P G hp))
  refine ⟨u, hu, ?_⟩
  change rawFrontParam
    (NativeGraphMarkedLine.ofGraph (graphSlope P i) (graphIntercept P q i) (centerHeight P q), ↑u) ∈ _
  rw [he, ← contract_axis_eq_graph]
  simpa only [hpi] using coarse_axis_mem P h R q hR G hpad hp

/-- Literal cubical and measurable shadings on every original row. -/
theorem source_cubical_measurable (R q : ℕ) (G : Finset Index) (hN : 0 < P.N)
    (hinj : Function.Injective (fun i => (P.tubeSlope i, P.tubeOffset i))) (i : Fin n) :
    IsWZCubicalShading (mesh P R) ((source P R q G hN hinj).shading i) ∧
    MeasurableSet ((source P R q G hN hinj).shading i) :=
  ⟨isWZCubicalShading_wzCellShading _ _ _, measurableSet_wzCellShading _ _ _⟩

/-- The actual occurrence, not a containment certificate, proves the factor-two tube inclusion. -/
theorem source_shading_subset (h : P.Hypotheses)
    (hslope : ∀ i j, |P.slope i j| ≤ 1) (R q : ℕ)
    (hR : (P.E : ℝ) + 1 ≤ (R : ℝ)) (G : Finset Index)
    (hpad : ∀ d ∈ G, ∀ j, 4 * (R : ℤ) ≤ (d j + (q : ℤ)) % (64 * R : ℕ) ∧
      (d j + (q : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ))
    (hinj : Function.Injective (fun i => (P.tubeSlope i, P.tubeOffset i))) (i : Fin n) :
    (source P R q G h.N_pos hinj).shading i ⊆
      markedUnitTube ((source P R q G h.N_pos hinj).line i)
        (source P R q G h.N_pos hinj).thickness := by
  have hRpos : 0 < R := by exact_mod_cast (show 0 < (R : ℝ) by linarith [(show (0 : ℝ) ≤ P.E from Nat.cast_nonneg _)])
  apply wzDyadicCells_meeting_markedLine_subset_two_mul_tube
    (line P q i) (mesh_pos P h R hRpos) (cells P R q G i)
  intro k hk
  obtain ⟨u, _, hu⟩ := cell_has_marked_witness P h hslope R q hR G hpad i k hk
  exact ⟨u, hu⟩

theorem source_normalization (R q : ℕ) (G : Finset Index) (hN : 0 < P.N)
    (hinj : Function.Injective (fun i => (P.tubeSlope i, P.tubeOffset i)))
    (hslope : ∀ i j, |P.slope i j| ≤ 1) :
    HasNormalizedWZGraphSlab (source P R q G hN hinj) ∧
    HasFixedWZGraphNormalization (source P R q G hN hinj) := by
  constructor
  · exact NativeGraphMarkedLine.family_hasNormalizedWZGraphSlab
      (source P R q G hN hinj) (graphSlope P) (graphIntercept P q) (centerHeight P q)
      (fun _ => rfl) hslope
  · exact NativeGraphMarkedLine.family_hasFixedWZGraphNormalization
      (source P R q G hN hinj) (graphSlope P) (graphIntercept P q) (centerHeight P q)
      (fun _ => rfl) hslope

/-- Explicit finite integer preimage box for one coarse global spatial cell. -/
def indexBox (C q : ℕ) (k : Index) : Finset Index :=
  Fintype.piFinset (fun j => Finset.Icc ((C : ℤ) * k j - q) ((C : ℤ) * k j - q + C - 1))

theorem card_indexBox (C q : ℕ) (k : Index) : (indexBox C q k).card = C ^ 4 := by
  have hc (j : Fin 4) :
      (Finset.Icc ((C : ℤ) * k j - q) ((C : ℤ) * k j - q + C - 1)).card = C := by
    rw [Int.card_Icc]
    omega
  simp [indexBox, Fintype.card_piFinset, hc]

theorem mem_indexBox_of_quotient (C q : ℕ) (hC : 0 < C) (d k : Index)
    (he : ∀ j, (d j + (q : ℤ)) / C = k j) : d ∈ indexBox C q k := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have hCz : (0 : ℤ) < C := by exact_mod_cast hC
  have hlo := Int.emod_nonneg (d j + q) (ne_of_gt hCz)
  have hhi := Int.emod_lt_of_pos (d j + q) hCz
  have hd := Int.emod_add_mul_ediv (d j + q) (C : ℤ)
  rw [he j] at hd
  exact Finset.mem_Icc.mpr (by constructor <;> omega)

def newPairs (R q : ℕ) (G : Finset Index) : Finset (Fin n × Index) :=
  (retained P G).image (fun p => (p.1, coarse P R q p.2))

/-- The actual composed global map has capacity C^4 N; no fiber certificate is assumed. -/
theorem coarse_incidence_capacity (h : P.Hypotheses) (R q : ℕ) (hR : 0 < R)
    (G : Finset Index) (b : Fin n × Index) :
    (IncidenceBinTransfer.binFiber (retained P G) (coarse P R q) b).card ≤
      (64 * R) ^ 4 * P.N := by
  let S := IncidenceBinTransfer.binFiber (retained P G) (coarse P R q) b
  have hbox : (S.image (fun p => fine P p.2)).card ≤ (64 * R) ^ 4 := by
    calc
      (S.image (fun p => fine P p.2)).card ≤ (indexBox (64 * R) q b.2).card := by
        apply Finset.card_le_card
        intro d hd
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
        have he : coarse P R q p.2 = b.2 :=
          congrArg (fun x : Fin n × Index => x.2) (IncidenceBinTransfer.mem_binFiber.mp hp).2
        apply mem_indexBox_of_quotient (64 * R) q (by omega) (fine P p.2) b.2
        intro j
        exact congrFun he j
      _ = (64 * R) ^ 4 := card_indexBox _ _ _
  have hsmall : ∀ d ∈ S.image (fun p => fine P p.2),
      (S.filter (fun p => fine P p.2 = d)).card ≤ P.N := by
    intro d _hd
    have hsub : S.filter (fun p => fine P p.2 = d) ⊆
        IncidenceBinTransfer.binFiber P.incidences P.cellBin (b.1, decode d) := by
      intro p hp
      obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpR, hpb⟩ := IncidenceBinTransfer.mem_binFiber.mp hpS
      have hfirst : p.1 = b.1 := congrArg (fun x : Fin n × Index => x.1) hpb
      have hcell : P.cellBin p.2 = decode d := by
        simpa only [fine, decode_encode] using congrArg decode hpd
      exact IncidenceBinTransfer.mem_binFiber.mpr
        ⟨retained_subset P G hpR, Prod.ext hfirst hcell⟩
    exact (Finset.card_le_card hsub).trans (P.incidence_fiber_bound h (b.1, decode d))
  calc
    S.card = ∑ d ∈ S.image (fun p => fine P p.2),
        (S.filter (fun p => fine P p.2 = d)).card :=
      Finset.card_eq_sum_card_image (fun p : Fin n × Cell => fine P p.2) S
    _ ≤ ∑ _d ∈ S.image (fun p => fine P p.2), P.N := Finset.sum_le_sum hsmall
    _ = P.N * (S.image (fun p => fine P p.2)).card := by simp [Nat.mul_comm]
    _ ≤ P.N * (64 * R) ^ 4 := Nat.mul_le_mul_left _ hbox
    _ = (64 * R) ^ 4 * P.N := Nat.mul_comm _ _

theorem retained_card_le_newPairs (h : P.Hypotheses) (R q : ℕ) (hR : 0 < R)
    (G : Finset Index) :
    (retained P G).card ≤ ((64 * R) ^ 4 * P.N) * (newPairs P R q G).card := by
  have hfiber (b : Fin n × Index) :
      (retained P G).filter (fun p => (p.1, coarse P R q p.2) = b) =
        IncidenceBinTransfer.binFiber (retained P G) (coarse P R q) b := by
    ext p
    simp only [Finset.mem_filter, IncidenceBinTransfer.mem_binFiber, IncidenceBinTransfer.binLabel]
  calc
    (retained P G).card = ∑ b ∈ newPairs P R q G,
        ((retained P G).filter (fun p => (p.1, coarse P R q p.2) = b)).card :=
      Finset.card_eq_sum_card_image (fun p : Fin n × Cell => (p.1, coarse P R q p.2)) (retained P G)
    _ = ∑ b ∈ newPairs P R q G,
        (IncidenceBinTransfer.binFiber (retained P G) (coarse P R q) b).card := by
      apply Finset.sum_congr rfl
      intro b _hb
      exact congrArg Finset.card (hfiber b)
    _ ≤ ∑ _b ∈ newPairs P R q G, ((64 * R) ^ 4 * P.N) :=
      Finset.sum_le_sum (fun b _hb => coarse_incidence_capacity P h R q hR G b)
    _ = ((64 * R) ^ 4 * P.N) * (newPairs P R q G).card := by simp [Nat.mul_comm]

/-- The pair count is exactly the sum of row cell counts, including empty rows. -/
theorem card_newPairs_eq_sum_cells (R q : ℕ) (G : Finset Index) :
    (newPairs P R q G).card = ∑ i : Fin n, (cells P R q G i).card := by
  have hrow (i : Fin n) :
      (newPairs P R q G).filter (fun b => b.1 = i) =
        (cells P R q G i).image (fun k => (i, k)) := by
    ext b
    constructor
    · intro hb
      obtain ⟨hb, hbi⟩ := Finset.mem_filter.mp hb
      obtain ⟨p, hp, hpb⟩ := Finset.mem_image.mp hb
      have hpi : p.1 = i := (congrArg Prod.fst hpb).trans hbi
      refine Finset.mem_image.mpr ⟨coarse P R q p.2, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpi⟩, rfl⟩
      · have hsecond : coarse P R q p.2 = b.2 :=
          congrArg (fun x : Fin n × Index => x.2) hpb
        exact Prod.ext hbi.symm hsecond
    · intro hb
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hp, hpi⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨p, hp, Prod.ext hpi rfl⟩, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hrow i, Finset.card_image_of_injective _ (fun _ _ he => congrArg Prod.snd he)]

/-- The resulting actual cubical shading volume is its exact new-incidence count times mesh^4. -/
theorem source_total_shading_volume (h : P.Hypotheses) (R q : ℕ) (hR : 0 < R)
    (G : Finset Index) (hinj : Function.Injective (fun i => (P.tubeSlope i, P.tubeOffset i))) :
    wzTotalShadingVolume (source P R q G h.N_pos hinj) =
      (newPairs P R q G).card * (ENNReal.ofReal (mesh P R)) ^ 4 := by
  change (∑ i : Fin n, volume (wzCellShading (mesh P R) (cells P R q G) i)) = _
  simp_rw [volume_wzCellShading (mesh_pos P h R hR)]
  rw [← Finset.sum_mul]
  have hc : (∑ i : Fin n, ((cells P R q G i).card : ENNReal)) = (newPairs P R q G).card := by
    exact_mod_cast (card_newPairs_eq_sum_cells P R q G).symm
  rw [hc]

/-- Literal coverage of every retained old center by its original tube's new shading. -/
theorem source_covers_retained_centers (h : P.Hypotheses) (R q : ℕ)
    (hR : (P.E : ℝ) + 1 ≤ (R : ℝ)) (G : Finset Index)
    (hpad : ∀ d ∈ G, ∀ j, 4 * (R : ℤ) ≤ (d j + (q : ℤ)) % (64 * R : ℕ) ∧
      (d j + (q : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ))
    (hinj : Function.Injective (fun i => (P.tubeSlope i, P.tubeOffset i)))
    {p : Fin n × Cell} (hp : p ∈ retained P G) :
    contract P q (point P p.2) ∈ (source P R q G h.N_pos hinj).shading p.1 := by
  change contract P q (point P p.2) ∈ wzCellShading (mesh P R) (cells P R q G) p.1
  simp only [wzCellShading, Set.mem_iUnion]
  exact ⟨coarse P R q p.2, Finset.mem_image.mpr
    ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩,
    coarse_point_mem P h R q hR G hpad hp⟩

/-- Selected global fine-bin fibers keep every original heavy incidence in that bin. -/
theorem retained_fine_fiber_eq (G : Finset Index) {d : Index} (hd : d ∈ G) :
    (retained P G).filter (fun p => fine P p.2 = d) =
      P.keptIncidences.filter (fun p => fine P p.2 = d) := by
  ext p
  simp only [retained, Finset.mem_filter]
  constructor
  · exact fun ⟨⟨hp, _⟩, he⟩ => ⟨hp, he⟩
  · exact fun ⟨hp, he⟩ => ⟨⟨hp, he ▸ hd⟩, he⟩

/-- If the chosen numerical mesh is dyadic, the literal factor-two comparable-cube clause follows. -/
theorem source_comparable_cubical (h : P.Hypotheses) (R q : ℕ) (hR : 0 < R)
    (G : Finset Index) (hinj : Function.Injective (fun i => (P.tubeSlope i, P.tubeOffset i)))
    (hdyadic : IsWZDyadicScale (mesh P R)) (i : Fin n) :
    IsWZComparableCubicalShading (source P R q G h.N_pos hinj).thickness
      ((source P R q G h.N_pos hinj).shading i) := by
  have hm := mesh_pos P h R hR
  exact ⟨mesh P R, hm, by change mesh P R ≤ 2 * mesh P R; linarith,
    le_rfl, hdyadic, (source_cubical_measurable P R q G h.N_pos hinj i).1⟩

/-- Actual global padding, actual physical witnesses, and actual native source assembly.
The type remains `FiniteScaleSource n`; every original row, including an empty row, remains.
Window and cube-containment conclusions are proved from the construction.
Direction separation, AD, and convex-Wolff remain separate obligations. -/
theorem exists_actual_padded_cubical_source
    (hδ : 0 < P.δ) (hN : 0 < P.N) (hσ : P.σ ≤ 1)
    (hlam : 0 < P.lam) (hlamOne : P.lam ≤ 1)
    (hslope : ∀ i j, |P.slope i j| ≤ 1)
    (htime : ∀ p ∈ P.incidences, |(P.center p.2).2| ≤ 1)
    (hphysical : ∀ p ∈ P.incidences, ∀ j,
      |P.residual p.1 p.2 j| ≤ (P.E : ℝ) * P.σ)
    (hinj : Function.Injective (fun i => (P.tubeSlope i, P.tubeOffset i)))
    (hdensity : P.lam * (n : ℝ) ≤ P.δ * P.incidences.card)
    (R : ℕ) (hR : (P.E : ℝ) + 1 ≤ (R : ℝ)) :
    ∃ q : Fin (64 * R), ∃ G : Finset Index,
      G ⊆ fineBins P ∧
      retained P G ⊆ P.incidences ∧
      P.incidences.card ≤ 4 * (retained P G).card ∧
      P.lam * (n : ℝ) ≤ 4 * P.δ * (retained P G).card ∧
      P.lam * (n : ℝ) ≤
        32 * ((64 * R : ℕ) : ℝ) ^ 3 * mesh P R * (newPairs P R q.val G).card ∧
      (∀ p ∈ retained P G,
        contract P q.val (point P p.2) ∈ (source P R q.val G hN hinj).shading p.1) ∧
      (∀ i k, k ∈ cells P R q.val G i →
        ∃ u : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), |(u : ℝ)| ≤ 1 / 4 ∧
          rawFrontParam (line P q.val i, (u : ℝ)) ∈ wzDyadicCell (mesh P R) k) ∧
      (∀ i : Fin n,
        IsValidLine ((source P R q.val G hN hinj).line i) ∧
        (source P R q.val G hN hinj).weight i = 1 ∧
        IsWZCubicalShading (mesh P R) ((source P R q.val G hN hinj).shading i) ∧
        MeasurableSet ((source P R q.val G hN hinj).shading i) ∧
        (source P R q.val G hN hinj).shading i ⊆
          markedUnitTube ((source P R q.val G hN hinj).line i)
            (source P R q.val G hN hinj).thickness) ∧
      HasNormalizedWZGraphSlab (source P R q.val G hN hinj) ∧
      HasFixedWZGraphNormalization (source P R q.val G hN hinj) ∧
      wzTotalShadingVolume (source P R q.val G hN hinj) =
        (newPairs P R q.val G).card * (ENNReal.ofReal (mesh P R)) ^ 4 := by
  have hdensityB : P.lam * ((Finset.univ : Finset (Fin n)).card : ℝ) ≤
      P.δ * P.incidences.card := by simpa using hdensity
  have h := P.hypotheses_of_full_backbone_density Finset.univ
    (Finset.subset_univ _) hδ hN hσ hlam hlamOne (fun i _hi => hslope i)
    htime hphysical hdensityB
  have hRpos : 0 < R := by exact_mod_cast (show 0 < (R : ℝ) by linarith [(show (0 : ℝ) ≤ P.E from Nat.cast_nonneg _)])
  obtain ⟨q, G, hG, hkeep, hpad⟩ := exists_padding P R hRpos
  have hquarter : P.incidences.card ≤ 4 * (retained P G).card := by
    have := P.half_mass h
    omega
  have hquarterR : (P.incidences.card : ℝ) ≤ 4 * (retained P G).card := by exact_mod_cast hquarter
  have hretained : P.lam * (n : ℝ) ≤ 4 * P.δ * (retained P G).card := by
    calc
      P.lam * (n : ℝ) ≤ P.δ * P.incidences.card := hdensity
      _ ≤ P.δ * (4 * (retained P G).card) := mul_le_mul_of_nonneg_left hquarterR h.delta_pos.le
      _ = 4 * P.δ * (retained P G).card := by ring
  have hcap : ((retained P G).card : ℝ) ≤
      (((64 * R) ^ 4 * P.N : ℕ) : ℝ) * (newPairs P R q.val G).card := by
    exact_mod_cast retained_card_le_newPairs P h R q.val hRpos G
  have hnew : P.lam * (n : ℝ) ≤
      32 * ((64 * R : ℕ) : ℝ) ^ 3 * mesh P R * (newPairs P R q.val G).card := by
    calc
      P.lam * (n : ℝ) ≤ 4 * P.δ * (retained P G).card := hretained
      _ ≤ (4 * P.δ) * ((((64 * R) ^ 4 * P.N : ℕ) : ℝ) * (newPairs P R q.val G).card) :=
        mul_le_mul_of_nonneg_left hcap (mul_nonneg (by norm_num) h.delta_pos.le)
      _ = 32 * ((64 * R : ℕ) : ℝ) ^ 3 * mesh P R * (newPairs P R q.val G).card := by
        dsimp [mesh, PhysicalRescalingIncidenceTransfer.Data.σ]
        push_cast
        ring
  have hnorm := source_normalization P R q.val G hN hinj hslope
  refine ⟨q, G, hG, retained_subset P G, hquarter, hretained, hnew,
    (fun _ hp => source_covers_retained_centers P h R q.val hR G hpad hinj hp),
    (fun i k hk => cell_has_marked_witness P h hslope R q.val hR G hpad i k hk), ?_,
    hnorm.1, hnorm.2, source_total_shading_volume P h R q.val hRpos G hinj⟩
  intro i
  have hc := source_cubical_measurable P R q.val G hN hinj i
  exact ⟨NativeGraphMarkedLine.valid _ _ _, rfl, hc.1, hc.2,
    source_shading_subset P h hslope R q.val hR G hpad hinj i⟩

end StickyKakeya4.PaddedRescalingCubicalSource
