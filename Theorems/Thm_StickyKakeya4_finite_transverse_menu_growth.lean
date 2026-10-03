import Mathlib.Tactic
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Theorems.Thm_StickyKakeya4_two_step_menu_paths
import Theorems.Thm_StickyKakeya4_two_dimensional_transverse_escape
import Theorems.Thm_StickyKakeya4_two_dimensional_time_fibers

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace FiniteTransverseMenuGrowth

open scoped BigOperators
noncomputable section
open Classical

lemma card_le_real_mul_of_fibers {S T : Type*} [DecidableEq T]
    (P : Finset S) (Q : Finset T) (f : S → T) (B : ℝ)
    (hmaps : ∀ p ∈ P, f p ∈ Q)
    (hfib : ∀ q ∈ Q, ((P.filter (fun p => f p = q)).card : ℝ) ≤ B) :
    (P.card : ℝ) ≤ (Q.card : ℝ) * B := by
  have hpart := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (P.card : ℝ) = ∑ q ∈ Q, ((P.filter (fun p => f p = q)).card : ℝ) := by
      exact_mod_cast hpart
    _ ≤ ∑ _q ∈ Q, B := Finset.sum_le_sum hfib
    _ = (Q.card : ℝ) * B := by simp

lemma same_floor_abs_sub_le {r x y : ℝ} (hr : 0 < r)
    (hfloor : ⌊x / r⌋ = ⌊y / r⌋) : |x-y| ≤ r := by
  have hxl : (⌊x/r⌋ : ℝ) * r ≤ x := (le_div_iff₀ hr).mp (Int.floor_le _)
  have hxu : x < ((⌊x/r⌋ : ℝ)+1)*r := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one _)
  have hyl : (⌊y/r⌋ : ℝ) * r ≤ y := (le_div_iff₀ hr).mp (Int.floor_le _)
  have hyu : y < ((⌊y/r⌋ : ℝ)+1)*r := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one _)
  rw [hfloor] at hxl hxu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma floor_fiber_card_le (Z : Finset ℝ) {r H : ℝ} (hr : 0 < r)
    (hcap : ∀ c : ℝ, ((Z.filter (fun z => c ≤ z ∧ z ≤ c+r)).card : ℝ) ≤ H)
    (k : ℤ) : ((Z.filter (fun z => ⌊z/r⌋ = k)).card : ℝ) ≤ H := by
  have hsub : Z.filter (fun z => ⌊z/r⌋ = k) ⊆
      Z.filter (fun z => (k : ℝ)*r ≤ z ∧ z ≤ (k : ℝ)*r+r) := by
    intro z hz
    obtain ⟨hzZ, hzk⟩ := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨hzZ, ?_, ?_⟩
    · have hh := (le_div_iff₀ hr).mp (Int.floor_le (z/r))
      simpa only [hzk] using hh
    · have hh := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (z/r))
      rw [hzk] at hh
      nlinarith
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcap ((k : ℝ)*r))

/-- The actual time-interval cap implies a longer interval bound by original
floor cells. No endpoint multiplicity estimate is assumed. -/
theorem interval_population (Z : Finset ℝ) {r H L c : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hcap : ∀ b : ℝ, ((Z.filter (fun z => b ≤ z ∧ z ≤ b+r)).card : ℝ) ≤ H) :
    ((Z.filter (fun z => |z-c| ≤ L*r)).card : ℝ) ≤ (2*L+2)*H := by
  classical
  let P := Z.filter (fun z => |z-c| ≤ L*r)
  let lo : ℤ := ⌊c/r-L⌋
  let hi : ℤ := ⌊c/r+L⌋
  let Q := Finset.Icc lo hi
  have hlohi : lo ≤ hi := Int.floor_mono (by linarith)
  have hmaps : ∀ z ∈ P, ⌊z/r⌋ ∈ Q := by
    intro z hz
    have hzc := abs_le.mp (Finset.mem_filter.mp hz).2
    have hl : c/r-L ≤ z/r := by
      apply (le_div_iff₀ hr).mpr
      have hc : c/r*r = c := div_mul_cancel₀ c hr.ne'
      nlinarith [hzc.1]
    have hu : z/r ≤ c/r+L := by
      apply (div_le_iff₀ hr).mpr
      have hc : c/r*r = c := div_mul_cancel₀ c hr.ne'
      nlinarith [hzc.2]
    exact Finset.mem_Icc.mpr ⟨Int.floor_mono hl, Int.floor_mono hu⟩
  have hfib : ∀ k ∈ Q, ((P.filter (fun z => ⌊z/r⌋=k)).card : ℝ) ≤ H := by
    intro k _hk
    have hsub : P.filter (fun z => ⌊z/r⌋=k) ⊆ Z.filter (fun z => ⌊z/r⌋=k) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1,
        (Finset.mem_filter.mp hz).2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (floor_fiber_card_le Z hr hcap k)
  have hQ : (Q.card : ℝ) ≤ 2*L+2 := by
    have hc : (Q.card : ℤ) = hi+1-lo := by
      dsimp [Q]
      exact Int.card_Icc_of_le _ _ (by omega)
    have hcast : (Q.card : ℝ) = (hi : ℝ)+1-(lo : ℝ) := by exact_mod_cast hc
    have hh := Int.floor_le (c/r+L)
    have hl := Int.lt_floor_add_one (c/r-L)
    change (hi : ℝ) ≤ c/r+L at hh
    change c/r-L < (lo : ℝ)+1 at hl
    rw [hcast]
    linarith
  exact (card_le_real_mul_of_fibers P Q (fun z => ⌊z/r⌋) H hmaps hfib).trans
    (mul_le_mul_of_nonneg_right hQ hH)

lemma scalar_coefficient_control {r E h v x₀ y y₀ c d : ℝ}
    (hh : 0 < h) (hv : h ≤ |v|) (hyy : |y-y₀| ≤ r)
    (hc : |y-x₀-c*v| ≤ E*r) (hd : |y₀-x₀-d*v| ≤ E*r) :
    |c-d| ≤ ((1+2*E)/h)*r := by
  have hprod : |(c-d)*v| ≤ (1+2*E)*r := by
    calc
      |(c-d)*v| = |(y-y₀)-(y-x₀-c*v)+(y₀-x₀-d*v)| := by congr 1; ring
      _ ≤ |y-y₀|+|y-x₀-c*v|+|y₀-x₀-d*v| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
      _ ≤ r+E*r+E*r := add_le_add (add_le_add hyy hc) hd
      _ = (1+2*E)*r := by ring
  rw [abs_mul] at hprod
  have hmul : |c-d| * h ≤ (1+2*E)*r :=
    (mul_le_mul_of_nonneg_left hv (abs_nonneg _)).trans hprod
  have hdiv := (le_div_iff₀ hh).mpr hmul
  calc
    |c-d| ≤ ((1+2*E)*r)/h := hdiv
    _ = ((1+2*E)/h)*r := by ring

lemma first_fixed_second_injective (F : Finset (ℝ × ℝ)) (z : ℝ)
    (hz : ∀ t ∈ F, t.1=z) : Set.InjOn (fun t : ℝ × ℝ => t.2) (↑F) := by
  intro t ht s hs hts
  exact Prod.ext ((hz t ht).trans (hz s hs).symm) hts

/-- At fixed angle, endpoint grid cell, and unprimed time, the original
time-interval cap bounds the actual primed-time fiber. -/
theorem scalar_endpoint_fiber (Z : Finset ℝ) (P : Finset (ℝ × ℝ))
    (endpoint : ℝ × ℝ → ℝ) {r H E h v x₀ : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H) (hE : 0 ≤ E) (hh : 0 < h)
    (hsub : P ⊆ Z ×ˢ Z) (hv : h ≤ |v|)
    (hcap : ∀ b : ℝ, ((Z.filter (fun z => b ≤ z ∧ z ≤ b+r)).card : ℝ) ≤ H)
    (happrox : ∀ t ∈ P, |endpoint t-x₀-(t.2-t.1)*v| ≤ E*r)
    (k : ℤ) (z : ℝ) :
    (((P.filter (fun t => ⌊endpoint t/r⌋=k)).filter (fun t => t.1=z)).card : ℝ)
      ≤ (2*((1+2*E)/h)+2)*H := by
  classical
  let F := (P.filter (fun t => ⌊endpoint t/r⌋=k)).filter (fun t => t.1=z)
  by_cases hF : F.Nonempty
  · obtain ⟨t₀, ht₀⟩ := hF
    have hmem : ∀ t ∈ F, t ∈ P ∧ ⌊endpoint t/r⌋=k ∧ t.1=z := by
      intro t ht
      obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.mp ht
      obtain ⟨htP, htk⟩ := Finset.mem_filter.mp ht₁
      exact ⟨htP, htk, ht₂⟩
    have hnear : ∀ t ∈ F, |t.2-t₀.2| ≤ ((1+2*E)/h)*r := by
      intro t ht
      have hc := scalar_coefficient_control hh hv
        (same_floor_abs_sub_le hr ((hmem t ht).2.1.trans (hmem t₀ ht₀).2.1.symm))
        (happrox t (hmem t ht).1) (happrox t₀ (hmem t₀ ht₀).1)
      have heq : t.1=t₀.1 := (hmem t ht).2.2.trans (hmem t₀ ht₀).2.2.symm
      rw [heq] at hc
      simpa only [sub_sub_sub_cancel_right] using hc
    have himage : F.image (fun t => t.2) ⊆
        Z.filter (fun q => |q-t₀.2| ≤ ((1+2*E)/h)*r) := by
      intro q hq
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (hsub (hmem t ht).1)).2,
        hnear t ht⟩
    have hinj := first_fixed_second_injective F z (fun t ht => (hmem t ht).2.2)
    have hcard : (F.card : ℝ) ≤
        ((Z.filter (fun q => |q-t₀.2| ≤ ((1+2*E)/h)*r)).card : ℝ) := by
      rw [← Finset.card_image_of_injOn hinj]
      exact_mod_cast Finset.card_le_card himage
    exact hcard.trans (interval_population Z hr hH (by positivity) hcap)
  · have hzero : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card : ℝ) ≤ _
    rw [hzero]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- Fixed-angle scalar growth, deriving every endpoint multiplicity from
the original time interval cap and the approximate displacement. -/
theorem scalar_fixed_angle_growth (Z : Finset ℝ) (P : Finset (ℝ × ℝ))
    (endpoint : ℝ × ℝ → ℝ) {r H E h v x₀ : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H) (hE : 0 ≤ E) (hh : 0 < h) (hhone : h ≤ 1)
    (hsub : P ⊆ Z ×ˢ Z) (hv : h ≤ |v|)
    (hcap : ∀ b : ℝ, ((Z.filter (fun z => b ≤ z ∧ z ≤ b+r)).card : ℝ) ≤ H)
    (happrox : ∀ t ∈ P, |endpoint t-x₀-(t.2-t.1)*v| ≤ E*r) :
    h*(P.card : ℝ) ≤
      (4+4*E)*H*(Z.card : ℝ)*(P.image (fun t => ⌊endpoint t/r⌋)).card := by
  classical
  let Q := P.image (fun t => ⌊endpoint t/r⌋)
  have hfib : ∀ k ∈ Q,
      ((P.filter (fun t => ⌊endpoint t/r⌋=k)).card : ℝ) ≤
        (Z.card : ℝ)*((2*((1+2*E)/h)+2)*H) := by
    intro k _hk
    apply card_le_real_mul_of_fibers _ Z (fun t => t.1) _
    · intro t ht
      exact (Finset.mem_product.mp (hsub (Finset.mem_filter.mp ht).1)).1
    · intro z _hz
      exact scalar_endpoint_fiber Z P endpoint hr hH hE hh hsub hv hcap happrox k z
  have hcard := card_le_real_mul_of_fibers P Q (fun t => ⌊endpoint t/r⌋) _
    (fun t ht => Finset.mem_image_of_mem _ ht) hfib
  have hnumeric : h*(2*((1+2*E)/h)+2) ≤ 4+4*E := by
    have hc : h*((1+2*E)/h) = 1+2*E := mul_div_cancel₀ _ hh.ne'
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hcard hh.le
  have hrest : 0 ≤ H*(Z.card : ℝ)*(Q.card : ℝ) := by positivity
  have hnum := mul_le_mul_of_nonneg_right hnumeric hrest
  change h*(P.card : ℝ) ≤ (4+4*E)*H*(Z.card : ℝ)*(Q.card : ℝ)
  nlinarith

abbrev Menu (A : Type*) := (ℝ × ℝ) × (A × A)

def oneStepCells {X A : Type*} [DecidableEq X]
    (M : X → Finset (Menu A)) (next : X → Menu A → X)
    (x : X → ℝ) (root : X) (r : ℝ) : Finset ℤ :=
  (insert root ((M root).image (next root))).image (fun v => ⌊x v/r⌋)

/-- Native a=1 finite transverse menu growth. The actual angular pair is
frozen by finite pigeonhole, and the endpoint multiplicity is then derived
from the original time-interval bound. The stated count includes the root. -/
theorem scalar_menu_growth {X A : Type*} [DecidableEq X] [DecidableEq A]
    (Z : Finset ℝ) (angles : Finset A) (M : X → Finset (Menu A))
    (next : X → Menu A → X) (x : X → ℝ) (phi : A → ℝ)
    {r H E h beta : ℝ} (root : X)
    (hZ : Z.Nonempty) (hA : angles.Nonempty)
    (hr : 0 < r) (hH : 0 ≤ H) (hE : 0 ≤ E)
    (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta)
    (hmenu : ∀ v, M v ⊆ (Z ×ˢ Z) ×ˢ (angles ×ˢ angles))
    (hcap : ∀ b : ℝ, ((Z.filter (fun z => b ≤ z ∧ z ≤ b+r)).card : ℝ) ≤ H)
    (happrox : ∀ v, ∀ s ∈ M v,
      |x (next v s)-x v-(s.1.2-s.1.1)*(phi s.2.2-phi s.2.1)| ≤ E*r)
    (hrich : ∀ v,
      beta*(Z.card : ℝ)^2*(angles.card : ℝ)^2 ≤
        (((M v).filter (fun s => h ≤ |phi s.2.2-phi s.2.1|)).card : ℝ)) :
    beta*h*(Z.card : ℝ) ≤
      (4+4*E)*H*(oneStepCells M next x root r).card := by
  classical
  let S := (M root).filter (fun s => h ≤ |phi s.2.2-phi s.2.1|)
  have hm : ∀ s ∈ S, s.2 ∈ angles ×ˢ angles := by
    intro s hs
    exact (Finset.mem_product.mp (hmenu root (Finset.mem_filter.mp hs).1)).2
  have hpigeon : (angles ×ˢ angles).card • (beta*(Z.card : ℝ)^2) ≤ (S.card : ℝ) := by
    simpa only [Finset.card_product, nsmul_eq_mul, Nat.cast_mul, pow_two,
      mul_assoc, mul_left_comm, mul_comm, S] using hrich root
  obtain ⟨ap, _hap, hfrozen⟩ :=
    Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hm (hA.product hA) hpigeon
  let F := S.filter (fun s => s.2=ap)
  let P := F.image (fun s => s.1)
  let endpoint : ℝ × ℝ → ℝ := fun t => x (next root (t,ap))
  have hFmem : ∀ s ∈ F, s ∈ M root ∧ h ≤ |phi s.2.2-phi s.2.1| ∧ s.2=ap := by
    intro s hs
    obtain ⟨hsS, hsa⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsM, hesc⟩ := Finset.mem_filter.mp hsS
    exact ⟨hsM, hesc, hsa⟩
  have hinj : Set.InjOn (fun s : Menu A => s.1) (↑F) := by
    intro s hs t ht hst
    exact Prod.ext hst ((hFmem s hs).2.2.trans (hFmem t ht).2.2.symm)
  have hPcard : P.card=F.card := Finset.card_image_of_injOn hinj
  have hPlower : beta*(Z.card : ℝ)^2 ≤ (P.card : ℝ) := by
    rw [hPcard]
    exact hfrozen
  have hFpos : 0 < (F.card : ℝ) := by
    have hZpos : (0 : ℝ) < Z.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hZ)
    exact (mul_pos hbeta (sq_pos_of_pos hZpos)).trans_le hfrozen
  obtain ⟨s₀, hs₀⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hFpos)
  have hv : h ≤ |phi ap.2-phi ap.1| := by
    have he := (hFmem s₀ hs₀).2.1
    rw [(hFmem s₀ hs₀).2.2] at he
    exact he
  have hPm : ∀ t ∈ P, (t,ap) ∈ M root := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp ht
    have heq : (t,ap)=s := Prod.ext hst.symm (hFmem s hs).2.2.symm
    rw [heq]
    exact (hFmem s hs).1
  have hPsub : P ⊆ Z ×ˢ Z := by
    intro t ht
    exact (Finset.mem_product.mp (hmenu root (hPm t ht))).1
  have hgrowth := scalar_fixed_angle_growth Z P endpoint hr hH hE hh hhone hPsub hv
    hcap (fun t ht => happrox root (t,ap) (hPm t ht))
  have hcellsub : P.image (fun t => ⌊endpoint t/r⌋) ⊆ oneStepCells M next x root r := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_image.mpr
    refine ⟨next root (t,ap), ?_, rfl⟩
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hPm t ht))
  have hcell : ((P.image (fun t => ⌊endpoint t/r⌋)).card : ℝ) ≤
      (oneStepCells M next x root r).card := Nat.cast_le.mpr (Finset.card_le_card hcellsub)
  have hcombine : beta*h*(Z.card : ℝ)^2 ≤
      (4+4*E)*H*(Z.card : ℝ)*(oneStepCells M next x root r).card := by
    have hl := mul_le_mul_of_nonneg_left hPlower hh.le
    have hu := mul_le_mul_of_nonneg_left hcell
      (show 0 ≤ (4+4*E)*H*(Z.card : ℝ) by positivity)
    nlinarith
  have hZpos : (0 : ℝ) < Z.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hZ)
  apply (mul_le_mul_iff_right₀ hZpos).mp
  nlinarith [hcombine]

lemma planar_line_ne_top (b : ℝ × ℝ) : Submodule.span ℝ ({b} : Set (ℝ × ℝ)) ≠ ⊤ := by
  intro htop
  have hfull := (Submodule.span_singleton_eq_top_iff ℝ b).mp htop
  by_cases hb : b.1=0
  · obtain ⟨t, ht⟩ := hfull (1,0)
    have hx := congrArg Prod.fst ht
    simp only [Prod.smul_fst, smul_eq_mul, hb, mul_zero] at hx
    norm_num at hx
  · obtain ⟨t, ht⟩ := hfull (0,1)
    have hx : t*b.1=0 := congrArg Prod.fst ht
    have htzero : t=0 := (mul_eq_zero.mp hx).resolve_right hb
    have hy := congrArg Prod.snd ht
    simp only [Prod.smul_snd, smul_eq_mul, htzero, zero_mul] at hy
    norm_num at hy

def angularDifference {A : Type*} (phi : A → ℝ × ℝ) (ap : A × A) : ℝ × ℝ :=
  ((phi ap.2).1-(phi ap.1).1, (phi ap.2).2-(phi ap.1).2)

def planarEscape {A : Type*} (phi : A → ℝ × ℝ) (h : ℝ) (b : ℝ × ℝ)
    (s : Menu A) : Prop :=
  ∀ t : ℝ, h ≤ max |(angularDifference phi s.2).1-t*b.1|
    |(angularDifference phi s.2).2-t*b.2|

/-- Every line used by the two-level construction is a proper subspace.
The original distance-from-subspace menu hypothesis supplies all line menus. -/
theorem planar_line_richness_of_subspaces {X A : Type*}
    (M : X → Finset (Menu A)) (phi : A → ℝ × ℝ) (h B : ℝ)
    (hrich : ∀ v, ∀ L : Submodule ℝ (ℝ × ℝ), L ≠ ⊤ →
      B ≤ (((M v).filter (fun s => h ≤ Metric.infDist (angularDifference phi s.2) (L : Set (ℝ × ℝ)))).card : ℝ)) :
    ∀ v b, B ≤ (((M v).filter (planarEscape phi h b)).card : ℝ) := by
  classical
  intro v b
  let L := Submodule.span ℝ ({b} : Set (ℝ × ℝ))
  have hsub : (M v).filter (fun s => h ≤ Metric.infDist (angularDifference phi s.2)
      (L : Set (ℝ × ℝ))) ⊆ (M v).filter (planarEscape phi h b) := by
    intro s hs
    obtain ⟨hsM, hsL⟩ := Finset.mem_filter.mp hs
    refine Finset.mem_filter.mpr ⟨hsM, ?_⟩
    intro t
    have ht : t • b ∈ L := L.smul_mem t (Submodule.mem_span_singleton_self b)
    have hd := hsL.trans (Metric.infDist_le_dist_of_mem ht)
    simpa only [Prod.dist_eq, Real.dist_eq, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] using hd
  exact (hrich v L (planar_line_ne_top b)).trans
    (Nat.cast_le.mpr (Finset.card_le_card hsub))

/-- Construct the depth-two genuine menu paths and freeze their actual
angular labels without assuming a path count or a projection fiber bound. -/
theorem planar_frozen_paths {X A : Type*} [DecidableEq A]
    (Z : Finset ℝ) (angles : Finset A) (M : X → Finset (Menu A))
    (next : X → Menu A → X) (phi : A → ℝ × ℝ) (root : X)
    {h beta : ℝ} (hZ : Z.Nonempty) (hA : angles.Nonempty) (hbeta : 0 < beta)
    (hmenu : ∀ v, M v ⊆ (Z ×ˢ Z) ×ˢ (angles ×ˢ angles))
    (hrich : ∀ v b,
      beta*(Z.card : ℝ)^2*(angles.card : ℝ)^2 ≤
        (((M v).filter (planarEscape phi h b)).card : ℝ)) :
    ∃ ap ∈ (angles ×ˢ angles) ×ˢ (angles ×ˢ angles),
      ∃ P : Finset ((ℝ × ℝ) × (ℝ × ℝ)),
        P ⊆ (Z ×ˢ Z) ×ˢ (Z ×ˢ Z) ∧
        beta^2*(Z.card : ℝ)^4 ≤ (P.card : ℝ) ∧
        h ≤ max |(angularDifference phi ap.1).1| |(angularDifference phi ap.1).2| ∧
        (∀ t : ℝ, h ≤ max
          |(angularDifference phi ap.2).1-t*(angularDifference phi ap.1).1|
          |(angularDifference phi ap.2).2-t*(angularDifference phi ap.1).2|) ∧
        (∀ t ∈ P,
          (t.1,ap.1) ∈ M root ∧
          (t.2,ap.2) ∈ M (next root (t.1,ap.1))) := by
  classical
  let S := (M root).filter (planarEscape phi h (0,0))
  let T : Menu A → Finset (Menu A) := fun s =>
    (M (next root s)).filter (planarEscape phi h (angularDifference phi s.2))
  let B := beta*(Z.card : ℝ)^2*(angles.card : ℝ)^2
  let b := beta^2*(Z.card : ℝ)^4
  have hroot : ∀ s ∈ S, s.2 ∈ angles ×ˢ angles := by
    intro s hs
    exact (Finset.mem_product.mp (hmenu root (Finset.mem_filter.mp hs).1)).2
  have hsecond : ∀ s ∈ S, ∀ t ∈ T s, t.2 ∈ angles ×ˢ angles := by
    intro s _hs t ht
    exact (Finset.mem_product.mp (hmenu (next root s) (Finset.mem_filter.mp ht).1)).2
  have hb : b*((angles ×ˢ angles).card : ℝ)^2 ≤ B^2 := by
    dsimp [b, B]
    simp only [Finset.card_product, Nat.cast_mul]
    ring_nf
    exact le_refl _
  obtain ⟨ap, hap, _hsub, hfixed, hcard⟩ := TwoStepMenuPaths.exists_frozen_paths
    S T (angles ×ˢ angles) (fun s : Menu A => s.2) (hA.product hA) hroot hsecond
    B b (by dsimp [B]; positivity) (hrich root (0,0))
    (fun s _hs => hrich (next root s) (angularDifference phi s.2)) hb
  let F := TwoStepMenuPaths.frozen (TwoStepMenuPaths.paths S T)
    (fun s : Menu A => s.2) ap
  let P := F.image TwoStepMenuPaths.orderedTimes
  have hFmem : ∀ p ∈ F,
      p.1 ∈ S ∧ p.2 ∈ T p.1 ∧ TwoStepMenuPaths.pathLabel Prod.snd p=ap := by
    intro p hp
    exact (TwoStepMenuPaths.mem_frozen_paths S T Prod.snd ap p).mp hp
  have hPm : ∀ t ∈ P,
      ((t.1,ap.1),(t.2,ap.2)) ∈ F := by
    intro t ht
    obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp ht
    have hpa := (hFmem p hp).2.2
    have heq : ((t.1,ap.1),(t.2,ap.2))=p := by
      apply Prod.ext
      · exact Prod.ext (congrArg Prod.fst hpt).symm (congrArg Prod.fst hpa).symm
      · exact Prod.ext (congrArg Prod.snd hpt).symm (congrArg Prod.snd hpa).symm
    rw [heq]
    exact hp
  have hactual : ∀ t ∈ P,
      (t.1,ap.1) ∈ M root ∧ (t.2,ap.2) ∈ M (next root (t.1,ap.1)) := by
    intro t ht
    have hp := hFmem _ (hPm t ht)
    exact ⟨(Finset.mem_filter.mp hp.1).1, (Finset.mem_filter.mp hp.2.1).1⟩
  have hPsub : P ⊆ (Z ×ˢ Z) ×ˢ (Z ×ˢ Z) := by
    intro t ht
    have ha := hactual t ht
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp (hmenu root ha.1)).1,
       (Finset.mem_product.mp (hmenu _ ha.2)).1⟩
  have hPlower : b ≤ (P.card : ℝ) := by
    rw [show P.card=F.card from
      TwoStepMenuPaths.card_orderedTimes_image_of_fixed_angles F ap hfixed]
    exact hcard
  have hPpos : 0 < (P.card : ℝ) := by
    have hZpos : (0 : ℝ) < Z.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hZ)
    have hbpos : 0 < b := by dsimp [b]; positivity
    exact hbpos.trans_le hPlower
  obtain ⟨t₀, ht₀⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hPpos)
  have hp₀ := hFmem _ (hPm t₀ ht₀)
  have hfirst : h ≤ max |(angularDifference phi ap.1).1| |(angularDifference phi ap.1).2| := by
    have he := (Finset.mem_filter.mp hp₀.1).2 (0 : ℝ)
    simpa only [mul_zero, sub_zero] using he
  have htrans : ∀ t : ℝ, h ≤ max
      |(angularDifference phi ap.2).1-t*(angularDifference phi ap.1).1|
      |(angularDifference phi ap.2).2-t*(angularDifference phi ap.1).2| :=
    (Finset.mem_filter.mp hp₀.2.1).2
  exact ⟨ap, hap, P, hPsub, hPlower, hfirst, htrans, hactual⟩

lemma scalar_infDist_bot (x : ℝ) :
    Metric.infDist x ((⊥ : Submodule ℝ ℝ) : Set ℝ)=|x| := by
  have heq : ((⊥ : Submodule ℝ ℝ) : Set ℝ)={0} := by ext z; simp
  rw [heq, Metric.infDist_singleton, Real.dist_eq, sub_zero]

/-- The one-dimensional theorem with the original proper-subspace escape
hypothesis, rather than a separately supplied scalar escape certificate. -/
theorem scalar_menu_growth_from_subspaces {X A : Type*} [DecidableEq X] [DecidableEq A]
    (Z : Finset ℝ) (angles : Finset A) (M : X → Finset (Menu A))
    (next : X → Menu A → X) (x : X → ℝ) (phi : A → ℝ)
    {r H E h beta : ℝ} (root : X)
    (hZ : Z.Nonempty) (hA : angles.Nonempty)
    (hr : 0 < r) (hH : 0 ≤ H) (hE : 0 ≤ E)
    (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta)
    (hmenu : ∀ v, M v ⊆ (Z ×ˢ Z) ×ˢ (angles ×ˢ angles))
    (hcap : ∀ b : ℝ, ((Z.filter (fun z => b ≤ z ∧ z ≤ b+r)).card : ℝ) ≤ H)
    (happrox : ∀ v, ∀ s ∈ M v,
      |x (next v s)-x v-(s.1.2-s.1.1)*(phi s.2.2-phi s.2.1)| ≤ E*r)
    (hrich : ∀ v, ∀ L : Submodule ℝ ℝ, L ≠ ⊤ →
      beta*(Z.card : ℝ)^2*(angles.card : ℝ)^2 ≤
        (((M v).filter (fun s =>
          h ≤ Metric.infDist (phi s.2.2-phi s.2.1) (L : Set ℝ))).card : ℝ)) :
    beta*h*(Z.card : ℝ) ≤
      (4+4*E)*H*(oneStepCells M next x root r).card := by
  apply scalar_menu_growth Z angles M next x phi root hZ hA hr hH hE hh hhone hbeta
    hmenu hcap happrox
  intro v
  simpa only [scalar_infDist_bot] using hrich v ⊥ (by exact bot_ne_top)

def planarTwoStepCells {X A : Type*} [DecidableEq X] [DecidableEq A]
    (M : X → Finset (Menu A)) (next : X → Menu A → X)
    (x : X → ℝ × ℝ) (root : X) (r : ℝ) : Finset (ℤ × ℤ) :=
  (insert root (((M root).image (next root)) ∪
    ((TwoStepMenuPaths.paths (M root) (fun s => M (next root s))).image
      (fun p => next (next root p.1) p.2)))).image
    (fun v => (⌊(x v).1/r⌋, ⌊(x v).2/r⌋))

lemma two_step_coordinate_error {x₀ x₁ x₂ c₁ c₂ v₁ v₂ E r : ℝ}
    (h₁ : |x₁-x₀-c₁*v₁| ≤ E*r) (h₂ : |x₂-x₁-c₂*v₂| ≤ E*r) :
    |x₂-x₀-c₁*v₁-c₂*v₂| ≤ 2*E*r := by
  calc
    |x₂-x₀-c₁*v₁-c₂*v₂| = |(x₁-x₀-c₁*v₁)+(x₂-x₁-c₂*v₂)| := by congr 1; ring
    _ ≤ |x₁-x₀-c₁*v₁|+|x₂-x₁-c₂*v₂| := abs_add_le _ _
    _ ≤ E*r+E*r := add_le_add h₁ h₂
    _ = 2*E*r := by ring

/-- Native a=2 finite transverse growth from the actual subspace-escape menus.
The proof constructs the two-generation path family, freezes genuine angular
labels, derives determinant and inverse bounds, and derives terminal fibers
from the original time cap. Its constant is exactly the audited C_growth. -/
theorem planar_menu_growth {X A : Type*} [DecidableEq X] [DecidableEq A]
    (Z : Finset ℝ) (angles : Finset A) (M : X → Finset (Menu A))
    (next : X → Menu A → X) (x : X → ℝ × ℝ) (phi : A → ℝ × ℝ)
    {r H E h beta V : ℝ} (root : X)
    (hZ : Z.Nonempty) (hA : angles.Nonempty)
    (hr : 0 < r) (hH : 0 ≤ H) (hE : 0 ≤ E)
    (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta) (hV : 0 < V)
    (hbound : ∀ a ∈ angles, ∀ b ∈ angles,
      |(phi b).1-(phi a).1| ≤ V ∧ |(phi b).2-(phi a).2| ≤ V)
    (hmenu : ∀ v, M v ⊆ (Z ×ˢ Z) ×ˢ (angles ×ˢ angles))
    (hcap : ∀ b : ℝ, ((Z.filter (fun z => b ≤ z ∧ z ≤ b+r)).card : ℝ) ≤ H)
    (happrox : ∀ v, ∀ s ∈ M v,
      max |(x (next v s)).1-(x v).1-(s.1.2-s.1.1)*(angularDifference phi s.2).1|
          |(x (next v s)).2-(x v).2-(s.1.2-s.1.1)*(angularDifference phi s.2).2| ≤ E*r)
    (hrich : ∀ v, ∀ L : Submodule ℝ (ℝ × ℝ), L ≠ ⊤ →
      beta*(Z.card : ℝ)^2*(angles.card : ℝ)^2 ≤
        (((M v).filter (fun s =>
          h ≤ Metric.infDist (angularDifference phi s.2) (L : Set (ℝ × ℝ)))).card : ℝ)) :
    beta^2*h^4*(Z.card : ℝ)^2 ≤
      (4*V*(1+4*E)+2)^2*H^2*(planarTwoStepCells M next x root r).card := by
  classical
  have hlines := planar_line_richness_of_subspaces M phi h
    (beta*(Z.card : ℝ)^2*(angles.card : ℝ)^2) hrich
  obtain ⟨ap, hap, P, hPsub, hPlower, hfirst, htrans, hactual⟩ :=
    planar_frozen_paths Z angles M next phi root hZ hA hbeta hmenu hlines
  let endpoint : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ × ℝ := fun t =>
    x (next (next root (t.1,ap.1)) (t.2,ap.2))
  have hap₁ := Finset.mem_product.mp (Finset.mem_product.mp hap).1
  have hap₂ := Finset.mem_product.mp (Finset.mem_product.mp hap).2
  have hv₁ := hbound ap.1.1 hap₁.1 ap.1.2 hap₁.2
  have hv₂ := hbound ap.2.1 hap₂.1 ap.2.2 hap₂.2
  have herr : ∀ t ∈ P,
      |(endpoint t).1-(x root).1-(t.1.2-t.1.1)*(angularDifference phi ap.1).1-
        (t.2.2-t.2.1)*(angularDifference phi ap.2).1| ≤ 2*E*r ∧
      |(endpoint t).2-(x root).2-(t.1.2-t.1.1)*(angularDifference phi ap.1).2-
        (t.2.2-t.2.1)*(angularDifference phi ap.2).2| ≤ 2*E*r := by
    intro t ht
    have h₁ := happrox root (t.1,ap.1) (hactual t ht).1
    have h₂ := happrox (next root (t.1,ap.1)) (t.2,ap.2) (hactual t ht).2
    exact ⟨two_step_coordinate_error ((le_max_left _ _).trans h₁) ((le_max_left _ _).trans h₂),
      two_step_coordinate_error ((le_max_right _ _).trans h₁) ((le_max_right _ _).trans h₂)⟩
  have hgrowth := TwoDimensionalTimeFibers.two_dimensional_fixed_angle_growth
    Z P endpoint hr hH hE hh hhone hV hPsub hfirst htrans
    hv₁.1 hv₁.2 hv₂.1 hv₂.2 hcap herr
  have hcellsub : P.image (TwoDimensionalTimeFibers.gridCell endpoint r) ⊆
      planarTwoStepCells M next x root r := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_image.mpr
    refine ⟨next (next root (t.1,ap.1)) (t.2,ap.2), ?_, rfl⟩
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨((t.1,ap.1),(t.2,ap.2)), ?_, rfl⟩
    exact (TwoStepMenuPaths.mem_paths _ _ _).mpr (hactual t ht)
  have hcell : ((P.image (TwoDimensionalTimeFibers.gridCell endpoint r)).card : ℝ) ≤
      (planarTwoStepCells M next x root r).card :=
    Nat.cast_le.mpr (Finset.card_le_card hcellsub)
  have hl := mul_le_mul_of_nonneg_left hPlower (show 0 ≤ h^4 by positivity)
  have hu := mul_le_mul_of_nonneg_left hcell
    (show 0 ≤ (4*V*(1+4*E)+2)^2*H^2*(Z.card : ℝ)^2 by positivity)
  have hcombine : (beta^2*h^4*(Z.card : ℝ)^2)*(Z.card : ℝ)^2 ≤
      ((4*V*(1+4*E)+2)^2*H^2*(planarTwoStepCells M next x root r).card)*(Z.card : ℝ)^2 := by
    calc
      _ = h^4*(beta^2*(Z.card : ℝ)^4) := by ring
      _ ≤ h^4*(P.card : ℝ) := hl
      _ ≤ _ := hgrowth.trans hu
      _ = _ := by ring
  have hZpos : (0 : ℝ) < Z.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hZ)
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hZpos)).mp hcombine

end
end FiniteTransverseMenuGrowth
