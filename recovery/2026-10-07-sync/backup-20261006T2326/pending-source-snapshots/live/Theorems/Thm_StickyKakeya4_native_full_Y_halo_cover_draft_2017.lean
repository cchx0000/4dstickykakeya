/- UNVERIFIED full-Y halo reader. No compiler or axiom audit has run.

The reference is the FULL scalar Y from LiteralAligned.fibers, at the
actual mesh e=rho/tau=sigma/32768. It is not the selected output quotient.
The output points have one-sided13sigma witnesses near512Y+beta, supplied
by first_aligned_native_scalar_witness. Original-cell labels are untouched.
For every grid width r>=sigma/2, inverse scaling gives r/512>=32e and
grid-center witnesses with27 inverse-grid widths of error.

The global cover is DERIVED from reference AD lower mass, bounded overlap
of the actual output grid, and the full scalar reference cardinality.
The local upper reuses NativeRecodedGridUpper.grid_ball_upper_of_witnesses.
No density, AD, lower count, or covering upper of the output is an input.
Only finitely many fixed scheduled radii are to be installed as uniform
relations; these hereditary upper statements hold at all allowed radii.
-/
import Theorems.Thm_StickyKakeya4_native_recoded_grid_upper
import Theorems.Thm_StickyKakeya4_original_representative_grid_comparison

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeFullYHaloCoverDraft2017
open Classical Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open NativeLiteralGridOverlap NativeRecodedGridUpper
open scoped BigOperators

lemma scalar_unit_interval_count (Y S : Finset ℝ) (hSY : S⊆Y)
    (e K alpha a : ℝ) (he : 0<e) (he1 : e≤1) (hK : 0<K)
    (H : ADBounds Y e K alpha) (hS : ∀y∈S,a≤y ∧ y≤a+1) :
    (S.card:ℝ)≤K*e^(-alpha) := by
  by_cases hSn : S.Nonempty
  · obtain ⟨c,hc⟩ := hSn
    have hsub : S⊆carrierBall Y c 1 := by
      intro y hy
      apply (mem_carrierBall Y y c 1).mpr
      refine ⟨hSY hy,?_⟩
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith only [(hS y hy).1,(hS y hy).2,(hS c hc).1,(hS c hc).2],
        by linarith only [(hS y hy).1,(hS y hy).2,(hS c hc).1,(hS c hc).2]⟩
    have hu := (H c (hSY hc) 1 he1 le_rfl).2
    have hid : (1/e)^alpha=e^(-alpha) := by
      rw [Real.div_rpow (by norm_num) he.le,Real.one_rpow,Real.rpow_neg he.le,one_div]
    exact (show (S.card:ℝ)≤(carrierBall Y c 1).card by exact_mod_cast card_le_card hsub).trans
      (by simpa only [hid] using hu)
  · rw [not_nonempty_iff_eq_empty.mp hSn,card_empty,Nat.cast_zero]
    exact mul_nonneg hK.le (Real.rpow_nonneg he.le _)

/-- LiteralAligned supplies |y|<=1, not a silently strengthened unit
diameter hypothesis. Two genuine unit intervals give the global count. -/
theorem full_scalar_global_count (Y : Finset ℝ) (e K alpha : ℝ)
    (he : 0<e) (he1 : e≤1) (hK : 0<K)
    (H : ADBounds Y e K alpha) (hY : ∀y∈Y,|y|≤1) :
    (Y.card:ℝ)≤2*K*e^(-alpha) := by
  let L := Y.filter (fun y => y≤0)
  let R := Y.filter (fun y => 0≤y)
  have hcover : Y⊆L∪R := by
    intro y hy
    rcases le_total y 0 with h | h
    · exact mem_union_left R (mem_filter.mpr ⟨hy,h⟩)
    · exact mem_union_right L (mem_filter.mpr ⟨hy,h⟩)
  have hL := scalar_unit_interval_count Y L (filter_subset _ _) e K alpha (-1) he he1 hK H
    (fun y hy => by
      have hb := abs_le.mp (hY y (mem_filter.mp hy).1)
      exact ⟨hb.1,by simpa using (mem_filter.mp hy).2⟩)
  have hR := scalar_unit_interval_count Y R (filter_subset _ _) e K alpha 0 he he1 hK H
    (fun y hy => by
      have hb := abs_le.mp (hY y (mem_filter.mp hy).1)
      exact ⟨(mem_filter.mp hy).2,by simpa using hb.2⟩)
  have hc : (Y.card:ℝ)≤(L.card:ℝ)+R.card := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le L R)
  linarith only [hc,hL,hR]

lemma weaken_AD (Y : Finset ℝ) (e K L alpha : ℝ) (he : 0<e)
    (hK : 0<K) (hKL : K≤L) (H : ADBounds Y e K alpha) : ADBounds Y e L alpha := by
  intro y hy r hr hr1
  have hh := H y hy r hr hr1
  have hp : 0≤(r/e)^alpha := Real.rpow_nonneg (div_nonneg (he.le.trans hr) he.le) _
  exact ⟨(div_le_div_of_nonneg_left hp hK hKL).trans hh.1,
    hh.2.trans (mul_le_mul_of_nonneg_right hKL hp)⟩

def shiftedScalar (b : ℝ) : ℝ ≃ᵢ (Fin 1 → ℝ) where
  toFun := fun y _ => y+b
  invFun := fun x => x 0-b
  left_inv := by intro y; simp
  right_inv := by
    intro x
    funext j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    simp
  isometry_toFun := Isometry.of_dist_eq (by
    intro x y
    rw [dist_pi_const,Real.dist_eq,Real.dist_eq]
    congr 1
    ring)

def scalarGrid {X : Type*} (P : Finset X) (q : X → ℝ) (r : ℝ) : Finset (Fin 1 → ℤ) :=
  P.image (fun p _ => ⌊q p/r⌋)

lemma midpoint_error (r : ℝ) (hr : 0<r) (x : ℝ) :
    |r*((⌊x/r⌋:ℝ)+1/2)-x|≤r/2 := by
  have hl := (le_div_iff₀ hr).mp (Int.floor_le (x/r))
  have hu := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (x/r))
  exact abs_le.mpr ⟨by nlinarith only [hl,hu],by nlinarith only [hl,hu]⟩

/-- The actual normal-grid labels obtain witnesses in a translated copy
of FULL Y at the literal inverse physical scale. -/
theorem inverse_grid_witness {X : Type*} (P : Finset X) (q : X → ℝ) (Y : Finset ℝ)
    (sigma r beta : ℝ) (hSigma : 0<sigma) (hr : sigma/2≤r)
    (H : ∀p∈P,∃y∈Y,|q p-(512*y+beta)|≤13*sigma) :
    ∀k∈scalarGrid P q r,∃a∈Y.image (shiftedScalar (beta/512)),
      dist (center (r/512) k) a≤27*(r/512) := by
  have hr0 : 0<r := (half_pos hSigma).trans_le hr
  intro k hk
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
  obtain ⟨y,hy,hclose⟩ := H p hp
  refine ⟨shiftedScalar (beta/512) y,mem_image_of_mem _ hy,?_⟩
  apply (dist_pi_le_iff (by positivity : (0:ℝ)≤27*(r/512))).mpr
  intro j
  rw [Real.dist_eq]
  change |(r/512)*((⌊q p/r⌋:ℝ)+1/2)-(y+beta/512)|≤27*(r/512)
  have hm := midpoint_error r hr0 (q p)
  have ht := abs_sub_le (r*((⌊q p/r⌋:ℝ)+1/2)) (q p) (512*y+beta)
  have hh : |r*((⌊q p/r⌋:ℝ)+1/2)-(512*y+beta)|≤27*r := by
    nlinarith only [hm,ht,hclose,hr]
  have he : (r/512)*((⌊q p/r⌋:ℝ)+1/2)-(y+beta/512)=
      (r*((⌊q p/r⌋:ℝ)+1/2)-(512*y+beta))/512 := by ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
  exact (div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ)≤512)).trans_eq (by ring)

/-- Global version of the existing grid-ball double count. Full-reference
AD lower mass and actual grid overlap give the entire occupied cover upper. -/
theorem global_grid_upper {l : ℕ} (A : Finset (Fin l → ℝ)) (B : Finset (Fin l → ℤ))
    (witness : (Fin l → ℤ) → (Fin l → ℝ)) (N : ℕ)
    (e r K alpha : ℝ) (he : 0<e) (her : e≤r) (hr1 : r≤1) (hK : 0<K)
    (H : ADBounds A e K alpha) (hGlobal : e^alpha*(A.card:ℝ)≤K)
    (hMem : ∀k∈B,witness k∈A)
    (hClose : ∀k∈B,dist (center r k) (witness k)≤(N:ℝ)*r) :
    (B.card:ℝ)≤(((4*N+5)^l:ℕ):ℝ)*K^2*r^(-alpha) := by
  have hr : 0<r := he.trans_le her
  have hScaled := scaled_bounds_of_ADBounds he hK H
  let M : ℝ := (((4*N+5)^l:ℕ):ℝ)
  have hM : 0≤M := Nat.cast_nonneg _
  have hRows : (B.card:ℝ)*r^alpha≤K*e^alpha*
      ∑k∈B,((A.filter (fun a => dist a (witness k)≤r)).card:ℝ) := by
    calc
      _ = ∑_k∈B,r^alpha := by simp
      _ ≤ ∑k∈B,K*e^alpha*((A.filter (fun a => dist a (witness k)≤r)).card:ℝ) := by
        apply sum_le_sum
        intro k hk
        exact (hScaled (witness k) (hMem k hk) r her hr1).1
      _ = _ := by rw [mul_sum]
  have hCols : ∀a∈A,((B.filter (fun k => dist a (witness k)≤r)).card:ℝ)≤M := by
    intro a _ha
    have hsub : B.filter (fun k => dist a (witness k)≤r) ⊆
        B.filter (fun k => dist (center r k) a≤((N+1:ℕ):ℝ)*r) := by
      intro k hk
      obtain ⟨hkB,hka⟩ := mem_filter.mp hk
      have ht := dist_triangle (center r k) (witness k) a
      have hc := hClose k hkB
      rw [dist_comm (witness k) a] at ht
      apply mem_filter.mpr ⟨hkB,?_⟩
      push_cast
      nlinarith only [ht,hc,hka]
    have hh := (card_le_card hsub).trans (grid_ball_card_le B hr a (N+1))
    dsimp only [M]
    have hid : 4*(N+1)+1=4*N+5 := by omega
    simpa only [hid] using
      (show ((B.filter (fun k => dist a (witness k)≤r)).card:ℝ)≤
        (((4*(N+1)+1)^l:ℕ):ℝ) by exact_mod_cast hh)
  rw [NativeRecodedGridUpper.incidence_sum_swap] at hRows
  have hSum : (∑a∈A,((B.filter (fun k => dist a (witness k)≤r)).card:ℝ))≤(A.card:ℝ)*M := by
    calc
      _ ≤ ∑_a∈A,M := sum_le_sum hCols
      _ = _ := by simp
  have hTotal : (B.card:ℝ)*r^alpha≤M*K^2 := by
    calc
      _ ≤ K*e^alpha*((A.card:ℝ)*M) := hRows.trans
        (mul_le_mul_of_nonneg_left hSum (mul_nonneg hK.le (Real.rpow_nonneg he.le _)))
      _ = M*K*(e^alpha*(A.card:ℝ)) := by ring
      _ ≤ M*K*K := mul_le_mul_of_nonneg_left hGlobal (mul_nonneg hM hK.le)
      _ = _ := by ring
  rw [Real.rpow_neg hr.le]
  have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hr alpha)).mpr hTotal
  simpa only [div_eq_mul_inv] using hh

/-- Full scalar bounds, translation and the13sigma actual-source halo
produce global and local occupied normal-grid uppers. Radius R is in
inverse-physical units in the local conclusion; it is later set to rOut/512. -/
theorem scalar_halo_grid_upper {X : Type*} (P : Finset X) (q : X → ℝ) (Y : Finset ℝ)
    (sigma e r beta K alpha : ℝ) (hSigma : 0<sigma) (heq : e=sigma/32768)
    (hr : sigma/2≤r) (hr1 : r≤1) (hK : 1≤K) (hAlpha : 0≤alpha)
    (H : ADBounds Y e K alpha) (hY : ∀y∈Y,|y|≤1)
    (hNear : ∀p∈P,∃y∈Y,|q p-(512*y+beta)|≤13*sigma) :
    ((scalarGrid P q r).card:ℝ)≤452*K^2*(r/512)^(-alpha) ∧
    ∀(x : Fin 1 → ℝ) (R : ℝ),r/512≤R → R≤1 →
      (((scalarGrid P q r).filter (fun k => dist (center (r/512) k) x≤R)).card:ℝ)≤
        452*K^2*58^alpha*(R/(r/512))^alpha := by
  have he : 0<e := by rw [heq]; positivity
  have hr0 : 0<r := (half_pos hSigma).trans_le hr
  have her : e≤r/512 := by rw [heq]; linarith only [hr,hSigma]
  have hr512 : r/512≤1 := by linarith only [hr1]
  have he1 : e≤1 := her.trans hr512
  have hK0 : 0<K := lt_of_lt_of_le zero_lt_one hK
  have h2K : 1≤2*K := by linarith only [hK]
  let A := Y.image (shiftedScalar (beta/512))
  let B := scalarGrid P q r
  have hYad : ADBounds Y e (2*K) alpha := weaken_AD Y e K (2*K) alpha he hK0 (by linarith) H
  have hAad : ADBounds A e (2*K) alpha :=
    OriginalRepresentativeGridComparison.point_AD_isometric_image (shiftedScalar (beta/512)) Y hYad
  have hGlobal : (A.card:ℝ)≤(2*K)*e^(-alpha) := by
    rw [card_image_of_injective _ (shiftedScalar (beta/512)).injective]
    exact full_scalar_global_count Y e K alpha he he1 hK0 H hY
  have hScaledGlobal : e^alpha*(A.card:ℝ)≤2*K := by
    have hh := mul_le_mul_of_nonneg_left hGlobal (Real.rpow_nonneg he.le alpha)
    have hc : e^alpha*e^(-alpha)=1 := by rw [←Real.rpow_add he,add_neg_cancel,Real.rpow_zero]
    calc
      _ ≤ e^alpha*((2*K)*e^(-alpha)) := hh
      _ = (2*K)*(e^alpha*e^(-alpha)) := by ring
      _ = _ := by rw [hc,mul_one]
  have hN := inverse_grid_witness P q Y sigma r beta hSigma hr hNear
  let witness : (Fin 1 → ℤ) → (Fin 1 → ℝ) := fun k =>
    if hk : k∈B then Classical.choose (hN k hk) else 0
  have hMem : ∀k∈B,witness k∈A := by
    intro k hk
    simp only [witness,dif_pos hk]
    exact (Classical.choose_spec (hN k hk)).1
  have hClose : ∀k∈B,dist (center (r/512) k) (witness k)≤(27:ℕ)*(r/512) := by
    intro k hk
    simp only [witness,dif_pos hk]
    exact (Classical.choose_spec (hN k hk)).2
  constructor
  · have hh := global_grid_upper A B witness 27 e (r/512) (2*K) alpha he her hr512
      (by positivity) hAad hScaledGlobal hMem hClose
    convert hh using 1 <;> norm_num <;> ring
  · intro x R hR hR1
    have hh := grid_ball_upper_of_witnesses A B witness 27 he her h2K hAlpha hAad hGlobal
      hMem hClose x R hR hR1
    convert hh using 1 <;> norm_num <;> ring

/-- The actual HeightAlignment exponent range supplies these hypotheses:
0<=kappa<=1 and0<=s<=1. The extra exponent is charged at native sigma. -/
theorem exponent_range_and_charge (kappa s sigma r : ℝ)
    (hk0 : 0≤kappa) (hk1 : kappa≤1) (hs0 : 0≤s) (hs1 : s≤1)
    (hSigma : 0<sigma) (hr : sigma≤r) :
    0≤2-kappa-s ∧ 2-kappa-s≤2 ∧
      (512:ℝ)^(2-kappa-s)≤512^2 ∧
      r^(-(2-kappa-s))≤sigma^(-(1-s))*r^(-(1-kappa)) := by
  have ha0 : 0≤2-kappa-s := by linarith only [hk1,hs1]
  have ha2 : 2-kappa-s≤2 := by linarith only [hk0,hs0]
  have hr0 : 0<r := hSigma.trans_le hr
  refine ⟨ha0,ha2,?_,?_⟩
  · have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤512) ha2
    norm_num at hh ⊢
    exact hh
  · have hsplit : -(2-kappa-s)=-(1-kappa)+(-(1-s)) := by ring
    rw [hsplit,Real.rpow_add hr0]
    have hh := Real.rpow_le_rpow_of_nonpos hSigma hr (by linarith only [hs1] : -(1-s)≤0)
    exact (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hr0.le _)).trans_eq (by ring)

end NativeFullYHaloCoverDraft2017
