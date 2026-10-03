import Mathlib

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Classical

namespace ShearBinFibers

/-- A global old-cell or target-bin index, with three spatial coordinates and one time coordinate. -/
abbrev Index := (Fin 3 → ℤ) × ℤ

/-- A time-dependent integer translation, followed by Euclidean division in time. -/
def triangularBin (N : ℕ) (shift : ℤ → Fin 3 → ℤ) (c : Index) : Index :=
  (fun j => c.1 j + shift c.2 j, c.2 / (N : ℤ))

/-- The old center in a specified bin with time remainder `r`. -/
def fiberPoint (N : ℕ) (shift : ℤ → Fin 3 → ℤ) (d : Index) (r : Fin N) : Index :=
  (fun j => d.1 j - shift ((N : ℤ) * d.2 + r.val) j,
    (N : ℤ) * d.2 + r.val)

theorem fiberPoint_injective (N : ℕ) (shift : ℤ → Fin 3 → ℤ) (d : Index) :
    Function.Injective (fiberPoint N shift d) := by
  intro r s h
  have ht := congrArg Prod.snd h
  dsimp only [fiberPoint] at ht
  apply Fin.ext
  omega

theorem triangularBin_fiberPoint (N : ℕ) (hN : 0 < N)
    (shift : ℤ → Fin 3 → ℤ) (d : Index) (r : Fin N) :
    triangularBin N shift (fiberPoint N shift d r) = d := by
  have hNz : (N : ℤ) ≠ 0 := by omega
  have hr0 : (0 : ℤ) ≤ r.val := by omega
  have hrN : (r.val : ℤ) < N := by exact_mod_cast r.isLt
  apply Prod.ext
  · funext j
    simp [triangularBin, fiberPoint]
  · change ((N : ℤ) * d.2 + r.val) / N = d.2
    rw [Int.add_ediv_of_dvd_left (dvd_mul_right (N : ℤ) d.2),
      Int.mul_ediv_cancel_left _ hNz, Int.ediv_eq_zero_of_lt hr0 hrN, add_zero]

/-- Euclidean remainders enumerate the entire fiber, including negative old time indices. -/
theorem triangularBin_eq_iff (N : ℕ) (hN : 0 < N)
    (shift : ℤ → Fin 3 → ℤ) (c d : Index) :
    triangularBin N shift c = d ↔ ∃ r : Fin N, fiberPoint N shift d r = c := by
  constructor
  · intro h
    have ht : c.2 / (N : ℤ) = d.2 := congrArg Prod.snd h
    have hs : ∀ j, c.1 j + shift c.2 j = d.1 j :=
      fun j => congrFun (congrArg Prod.fst h) j
    have hNz : (N : ℤ) ≠ 0 := by omega
    have hr0 := Int.emod_nonneg c.2 hNz
    have hrN := Int.emod_lt_of_pos c.2 (show (0 : ℤ) < N by omega)
    let r : Fin N := ⟨(c.2 % (N : ℤ)).toNat, (Int.toNat_lt hr0).mpr hrN⟩
    have hrcast : (r.val : ℤ) = c.2 % (N : ℤ) := Int.toNat_of_nonneg hr0
    have hk : (N : ℤ) * d.2 + r.val = c.2 := by
      rw [hrcast, ← ht]
      exact Int.mul_ediv_add_emod c.2 N
    refine ⟨r, Prod.ext ?_ hk⟩
    funext j
    change d.1 j - shift ((N : ℤ) * d.2 + r.val) j = c.1 j
    rw [hk, ← hs j]
    omega
  · rintro ⟨r, rfl⟩
    exact triangularBin_fiberPoint N hN shift d r

/-- An explicit finite enumeration of one full infinite-grid fiber. -/
def fiber (N : ℕ) (shift : ℤ → Fin 3 → ℤ) (d : Index) : Finset Index :=
  Finset.univ.image (fiberPoint N shift d)

@[simp] theorem mem_fiber (N : ℕ) (hN : 0 < N)
    (shift : ℤ → Fin 3 → ℤ) (c d : Index) :
    c ∈ fiber N shift d ↔ triangularBin N shift c = d := by
  simp only [fiber, Finset.mem_image, Finset.mem_univ, true_and]
  exact (triangularBin_eq_iff N hN shift c d).symm

@[simp] theorem card_fiber (N : ℕ) (shift : ℤ → Fin 3 → ℤ) (d : Index) :
    (fiber N shift d).card = N := by
  rw [fiber, Finset.card_image_of_injective _ (fiberPoint_injective N shift d)]
  simp

/-- The full fiber has exactly `N` elements, with no restriction to a finite window. -/
theorem triangularBin_fiber_ncard (N : ℕ) (hN : 0 < N)
    (shift : ℤ → Fin 3 → ℤ) (d : Index) :
    {c : Index | triangularBin N shift c = d}.ncard = N := by
  have heq : {c : Index | triangularBin N shift c = d} = (fiber N shift d : Set Index) := by
    ext c
    exact (mem_fiber N hN shift c d).symm
  rw [heq, Set.ncard_coe_finset, card_fiber]

/-- Any finite old-cell selection has at most `N` cells in each global bin. -/
theorem triangularBin_filter_card_le (N : ℕ) (hN : 0 < N)
    (shift : ℤ → Fin 3 → ℤ) (C : Finset Index) (d : Index) :
    (C.filter (fun c => triangularBin N shift c = d)).card ≤ N := by
  calc
    _ ≤ (fiber N shift d).card := Finset.card_le_card (by
      intro c hc
      exact (mem_fiber N hN shift c d).mpr (Finset.mem_filter.mp hc).2)
    _ = N := card_fiber N shift d

/-- Physical space-time coordinates, separated to avoid imposing any norm convention. -/
abbrev Point := (Fin 3 → ℝ) × ℝ

/-- Center of the old half-open `δ`-grid cell with integer index `c`. -/
def oldCenter (δ : ℝ) (c : Index) : Point :=
  (fun j => δ * ((c.1 j : ℝ) + 1 / 2), δ * ((c.2 : ℝ) + 1 / 2))

/-- The actual affine shear/rescaling `(X,t) ↦ ((X-b-ta)/ρ,t)`. -/
def shearRescale (ρ : ℝ) (a b : Fin 3 → ℝ) (p : Point) : Point :=
  (fun j => (p.1 j - b j - p.2 * a j) / ρ, p.2)

/-- Assignment to a single global grid by coordinate floors. -/
def gridBin (σ : ℝ) (p : Point) : Index :=
  (fun j => ⌊p.1 j / σ⌋, ⌊p.2 / σ⌋)

/-- The physical map uses `ρ = 1/N` and target scale `σ = Nδ`.
It contains no tube labels or tube-dependent bin choices. -/
def actualBin (δ : ℝ) (N : ℕ) (a b : Fin 3 → ℝ) (c : Index) : Index :=
  gridBin ((N : ℝ) * δ) (shearRescale (1 / (N : ℝ)) a b (oldCenter δ c))

/-- The global spatial translation induced at old time level `k`. -/
def shearShift (δ : ℝ) (a b : Fin 3 → ℝ) (k : ℤ) (j : Fin 3) : ℤ :=
  ⌊(1 / 2 : ℝ) - (b j + a j * δ * ((k : ℝ) + 1 / 2)) / δ⌋

/-- The actual spatial floor is an integer spatial index plus a time-only translation. -/
theorem actualBin_space (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (a b : Fin 3 → ℝ) (c : Index) (j : Fin 3) :
    (actualBin δ N a b c).1 j = c.1 j + shearShift δ a b c.2 j := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  change ⌊((δ * ((c.1 j : ℝ) + 1 / 2) - b j -
      δ * ((c.2 : ℝ) + 1 / 2) * a j) / (1 / (N : ℝ))) / ((N : ℝ) * δ)⌋ = _
  have heq : ((δ * ((c.1 j : ℝ) + 1 / 2) - b j -
      δ * ((c.2 : ℝ) + 1 / 2) * a j) / (1 / (N : ℝ))) / ((N : ℝ) * δ) =
      (c.1 j : ℝ) + (1 / 2 - (b j + a j * δ * ((c.2 : ℝ) + 1 / 2)) / δ) := by
    field_simp
    ring
  rw [heq, Int.floor_intCast_add]
  rfl

/-- The actual time floor is Euclidean integer division, also for negative times. -/
theorem actualBin_time (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (a b : Fin 3 → ℝ) (c : Index) :
    (actualBin δ N a b c).2 = c.2 / (N : ℤ) := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  change ⌊(δ * ((c.2 : ℝ) + 1 / 2)) / ((N : ℝ) * δ)⌋ = _
  have heq : (δ * ((c.2 : ℝ) + 1 / 2)) / ((N : ℝ) * δ) =
      ((c.2 : ℝ) + 1 / 2) / (N : ℝ) := by
    field_simp
  rw [heq, Int.floor_div_natCast, Int.floor_intCast_add]
  norm_num

/-- The actual affine/floor grid assignment is exactly the triangular integer map. -/
theorem actualBin_eq_triangularBin (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (a b : Fin 3 → ℝ) (c : Index) :
    actualBin δ N a b c = triangularBin N (shearShift δ a b) c := by
  apply Prod.ext
  · funext j
    exact actualBin_space δ hδ N hN a b c j
  · exact actualBin_time δ hδ N hN a b c

/-- Explicit full fiber enumeration for the actual geometric map. -/
theorem actualBin_eq_iff (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (a b : Fin 3 → ℝ) (c d : Index) :
    actualBin δ N a b c = d ↔
      ∃ r : Fin N, fiberPoint N (shearShift δ a b) d r = c := by
  rw [actualBin_eq_triangularBin δ hδ N hN]
  exact triangularBin_eq_iff N hN (shearShift δ a b) c d

/-- Every global target bin contains exactly `N` old centers in the full lattice. -/
theorem actualBin_fiber_ncard (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (a b : Fin 3 → ℝ) (d : Index) :
    {c : Index | actualBin δ N a b c = d}.ncard = N := by
  simp only [actualBin_eq_triangularBin δ hδ N hN]
  exact triangularBin_fiber_ncard N hN (shearShift δ a b) d

/-- The concrete geometric fiber bound, applicable to every finite old-cell set.
This is only a bound on collisions in one global bin; it asserts no tube-bin or shading estimate. -/
theorem actualBin_filter_card_le (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (a b : Fin 3 → ℝ) (C : Finset Index) (d : Index) :
    (C.filter (fun c => actualBin δ N a b c = d)).card ≤ N := by
  simp only [actualBin_eq_triangularBin δ hδ N hN]
  exact triangularBin_filter_card_le N hN (shearShift δ a b) C d

/-- The same finite-cell bound in the rescaling notation `L = 1/ρ`, with `ρ = 1/N`. -/
theorem actualBin_filter_card_le_inv_rho (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (a b : Fin 3 → ℝ) (C : Finset Index) (d : Index) :
    ((C.filter (fun c => actualBin δ N a b c = d)).card : ℝ) ≤ 1 / (1 / (N : ℝ)) := by
  simpa only [one_div_one_div] using
    (show ((C.filter (fun c => actualBin δ N a b c = d)).card : ℝ) ≤ (N : ℝ) from
      by exact_mod_cast actualBin_filter_card_le δ hδ N hN a b C d)

end ShearBinFibers
