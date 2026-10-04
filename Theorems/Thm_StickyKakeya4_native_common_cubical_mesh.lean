import Theorems.Thm_StickyKakeya4_wz_carrier_pruning
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000
noncomputable section
namespace NativeCommonCubicalMesh
open Classical Finset MeasureTheory StickyKakeya4
abbrev Index := Fin 4 → ℤ

def halfChildren (k : Index) : Finset Index :=
  (univ : Finset (Fin 4 → Fin 2)).image (fun b j => 2 * k j + ((b j).val : ℤ))

lemma mem_halfChildren (k l : Index) : l ∈ halfChildren k ↔
    ∀ j, l j = 2 * k j ∨ l j = 2 * k j + 1 := by
  constructor
  · intro hl
    obtain ⟨b, _hb, rfl⟩ := mem_image.mp hl
    intro j
    have hj := (b j).isLt
    have hc : (b j).val = 0 ∨ (b j).val = 1 := by omega
    rcases hc with hc | hc <;> simp [hc]
  · intro hl
    let b : Fin 4 → Fin 2 := fun j => if l j = 2 * k j then 0 else 1
    apply mem_image.mpr
    refine ⟨b, mem_univ _, ?_⟩
    funext j
    by_cases hj : l j = 2 * k j
    · simp [b, hj]
    · have he := (hl j).resolve_left hj
      simp [b, he]

lemma cell_eq_half_children {delta : ℝ} (hd : 0 < delta) (k : Index) :
    wzDyadicCell delta k =
      ⋃ l ∈ (halfChildren k : Set Index), wzDyadicCell (delta / 2) l := by
  ext x
  simp only [Set.mem_iUnion, mem_coe]
  constructor
  · intro hx
    let l := wzDyadicCellIndex (delta / 2) x
    refine ⟨l, (mem_halfChildren k l).mpr ?_, mem_wzDyadicCell_index (half_pos hd) x⟩
    intro j
    have hxlo : (k j : ℝ) ≤ x j / delta := (le_div_iff₀ hd).mpr (hx j).1
    have hxhi : x j / delta < (k j : ℝ) + 1 := (div_lt_iff₀ hd).mpr (hx j).2
    have hdiv : x j / (delta / 2) = 2 * (x j / delta) := by ring
    have hlo : 2 * k j ≤ l j := by
      apply Int.le_floor.mpr
      rw [hdiv]
      push_cast
      linarith
    have hhi : l j < 2 * k j + 2 := by
      apply Int.floor_lt.mpr
      rw [hdiv]
      push_cast
      linarith
    omega
  · rintro ⟨l, hl, hx⟩
    intro j
    have hj := (mem_halfChildren k l).mp hl j
    have hxj := hx j
    rcases hj with hj | hj <;> rw [hj] at hxj <;> push_cast at hxj <;>
      constructor <;> nlinarith [hd]

lemma cubical_at_half {delta : ℝ} (hd : 0 < delta) {S : Set E4}
    (hS : IsWZCubicalShading delta S) : IsWZCubicalShading (delta / 2) S := by
  obtain ⟨cells, hcells⟩ := hS
  refine ⟨cells.biUnion halfChildren, ?_⟩
  rw [hcells]
  ext x
  simp only [Set.mem_iUnion, mem_coe, mem_biUnion]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [cell_eq_half_children hd k] at hx
    obtain ⟨l, hl, hxl⟩ := by simpa only [Set.mem_iUnion, mem_coe] using hx
    exact ⟨l, ⟨k, hk, hl⟩, hxl⟩
  · rintro ⟨l, ⟨k, hk, hl⟩, hx⟩
    refine ⟨k, hk, ?_⟩
    rw [cell_eq_half_children hd k]
    exact Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨hl, hx⟩⟩

/-- Two comparable dyadic meshes have exactly the two possible integer levels. -/
lemma comparable_dyadic_cases {delta mesh : ℝ}
    (hd : IsWZDyadicScale delta) (hm : IsWZDyadicScale mesh)
    (hmd : mesh ≤ delta) (hdm : delta ≤ 2 * mesh) :
    mesh = delta ∨ mesh = delta / 2 := by
  obtain ⟨n, rfl⟩ := hd
  obtain ⟨m, rfl⟩ := hm
  have hnm : n ≤ m := (pow_le_pow_iff_right_of_lt_one₀
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).mp hmd
  have hpow : ((2 : ℝ)⁻¹) ^ (n + 1) ≤ ((2 : ℝ)⁻¹) ^ m := by
    rw [pow_succ]
    nlinarith
  have hmn : m ≤ n + 1 := (pow_le_pow_iff_right_of_lt_one₀
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).mp hpow
  have he : m = n ∨ m = n + 1 := by omega
  rcases he with rfl | rfl
  · exact Or.inl rfl
  · right
    rw [pow_succ]
    ring

/-- Every original row shading is represented at ONE common mesh delta/2;
the actual source and all its original points remain exactly the same. -/
theorem input_exists_common_cells {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) :
    ∃ cells : Fin n → Finset Index, ∀ i,
      D.shading i = wzCellShading (D.thickness / 2) cells i := by
  obtain ⟨hi, _hg, _hnrm⟩ := h
  obtain ⟨_hn, hd, _hd1, hdy, _hv, _hw, _hm, hcub, _hsub, _hsep, _hAD, _hCW, _hden⟩ := hi
  have hrows : ∀ i, IsWZCubicalShading (D.thickness / 2) (D.shading i) := by
    intro i
    obtain ⟨mesh, _hmesh, hmd, hdm, hmdy, hrow⟩ := hcub i
    rcases comparable_dyadic_cases hdy hmdy hmd hdm with he | he
    · rw [he] at hrow
      exact cubical_at_half hd hrow
    · rwa [he] at hrow
  simp only [IsWZCubicalShading] at hrows
  choose cells hcells using hrows
  exact ⟨cells, hcells⟩
end NativeCommonCubicalMesh
