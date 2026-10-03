import Mathlib.Tactic
import Mathlib.Data.Int.Interval
import Theorems.Thm_StickyKakeya4_two_dimensional_transverse_escape

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace TwoDimensionalTimeFibers

open scoped BigOperators
noncomputable section

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

/-- The ordered time pairs of the two steps. -/
abbrev TimePath := (ℝ × ℝ) × (ℝ × ℝ)

def firstTimes (t : TimePath) : ℝ × ℝ := (t.1.1, t.2.1)
def secondTimes (t : TimePath) : ℝ × ℝ := (t.1.2, t.2.2)
def gridCell (endpoint : TimePath → ℝ × ℝ) (r : ℝ) (t : TimePath) : ℤ × ℤ :=
  (⌊(endpoint t).1 / r⌋, ⌊(endpoint t).2 / r⌋)

/-- Subtracting two approximate displacements in one coordinate. -/
lemma linear_combination_control {r E u u₀ base c₁ c₂ d₁ d₂ v₁ v₂ : ℝ}
    (hu : |u-u₀| ≤ r)
    (hc : |u-base-c₁*v₁-c₂*v₂| ≤ 2*E*r)
    (hd : |u₀-base-d₁*v₁-d₂*v₂| ≤ 2*E*r) :
    |v₁*(c₁-d₁)+v₂*(c₂-d₂)| ≤ (1+4*E)*r := by
  calc
    |v₁*(c₁-d₁)+v₂*(c₂-d₂)| =
        |(u-u₀)-(u-base-c₁*v₁-c₂*v₂)+(u₀-base-d₁*v₁-d₂*v₂)| := by congr 1; ring
    _ ≤ |u-u₀|+|u-base-c₁*v₁-c₂*v₂|+|u₀-base-d₁*v₁-d₂*v₂| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ r+2*E*r+2*E*r := add_le_add (add_le_add hu hc) hd
    _ = (1+4*E)*r := by ring

/-- The two transverse directions control both coefficient differences. -/
theorem coefficient_control
    {r E h V x₀ y₀ x y x' y' c₁ c₂ d₁ d₂ v₁x v₁y v₂x v₂y : ℝ}
    (hh : 0 < h)
    (hfirst : h ≤ max |v₁x| |v₁y|)
    (htrans : ∀ s : ℝ, h ≤ max |v₂x-s*v₁x| |v₂y-s*v₁y|)
    (hv₁x : |v₁x| ≤ V) (hv₁y : |v₁y| ≤ V)
    (hv₂x : |v₂x| ≤ V) (hv₂y : |v₂y| ≤ V)
    (hx : |x-x'| ≤ r) (hy : |y-y'| ≤ r)
    (hcx : |x-x₀-c₁*v₁x-c₂*v₂x| ≤ 2*E*r)
    (hcy : |y-y₀-c₁*v₁y-c₂*v₂y| ≤ 2*E*r)
    (hdx : |x'-x₀-d₁*v₁x-d₂*v₂x| ≤ 2*E*r)
    (hdy : |y'-y₀-d₁*v₁y-d₂*v₂y| ≤ 2*E*r) :
    |c₁-d₁| ≤ (2*V*(1+4*E)/h^2)*r ∧
    |c₂-d₂| ≤ (2*V*(1+4*E)/h^2)*r := by
  have hcoeff := TwoDimensionalTransverseEscape.coefficient_differences_bound_of_max_transverse
    h V ((1+4*E)*r) v₁x v₁y v₂x v₂y c₁ c₂ d₁ d₂ hh hfirst htrans
    hv₁x hv₁y hv₂x hv₂y (linear_combination_control hx hcx hdx)
    (linear_combination_control hy hcy hdy)
  have heq : 2*V*((1+4*E)*r)/h^2 = (2*V*(1+4*E)/h^2)*r := by ring
  rwa [heq] at hcoeff

lemma firstTimes_fixed_secondTimes_injective (F : Finset TimePath) (z : ℝ × ℝ)
    (hz : ∀ t ∈ F, firstTimes t = z) : Set.InjOn secondTimes (↑F) := by
  intro t ht s hs hts
  have hfst : firstTimes t = firstTimes s := (hz t ht).trans (hz s hs).symm
  have h₁ : t.1.1=s.1.1 := by
    simpa only [firstTimes] using congrArg (fun p : ℝ × ℝ => p.1) hfst
  have h₂ : t.2.1=s.2.1 := by
    simpa only [firstTimes] using congrArg (fun p : ℝ × ℝ => p.2) hfst
  have h₁' : t.1.2=s.1.2 := by
    simpa only [secondTimes] using congrArg (fun p : ℝ × ℝ => p.1) hts
  have h₂' : t.2.2=s.2.2 := by
    simpa only [secondTimes] using congrArg (fun p : ℝ × ℝ => p.2) hts
  exact Prod.ext (Prod.ext h₁ h₁') (Prod.ext h₂ h₂')

/-- With both unprimed times fixed, a single endpoint cell contains at most
the product of the two actual interval populations of primed times. -/
theorem two_dimensional_endpoint_fiber
    (Z : Finset ℝ) (P : Finset TimePath) (endpoint : TimePath → ℝ × ℝ)
    {r H E h V x₀ y₀ v₁x v₁y v₂x v₂y : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H) (hE : 0 ≤ E) (hh : 0 < h) (hV : 0 < V)
    (hsub : P ⊆ (Z ×ˢ Z) ×ˢ (Z ×ˢ Z))
    (hfirst : h ≤ max |v₁x| |v₁y|)
    (htrans : ∀ s : ℝ, h ≤ max |v₂x-s*v₁x| |v₂y-s*v₁y|)
    (hv₁x : |v₁x| ≤ V) (hv₁y : |v₁y| ≤ V)
    (hv₂x : |v₂x| ≤ V) (hv₂y : |v₂y| ≤ V)
    (hcap : ∀ b : ℝ, ((Z.filter (fun z => b ≤ z ∧ z ≤ b+r)).card : ℝ) ≤ H)
    (happrox : ∀ t ∈ P,
      |(endpoint t).1-x₀-(t.1.2-t.1.1)*v₁x-(t.2.2-t.2.1)*v₂x| ≤ 2*E*r ∧
      |(endpoint t).2-y₀-(t.1.2-t.1.1)*v₁y-(t.2.2-t.2.1)*v₂y| ≤ 2*E*r)
    (k : ℤ × ℤ) (z : ℝ × ℝ) :
    (((P.filter (fun t => gridCell endpoint r t=k)).filter
      (fun t => firstTimes t=z)).card : ℝ) ≤ ((2*(2*V*(1+4*E)/h^2)+2)*H)^2 := by
  classical
  let L : ℝ := 2*V*(1+4*E)/h^2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let F := (P.filter (fun t => gridCell endpoint r t=k)).filter (fun t => firstTimes t=z)
  change (F.card : ℝ) ≤ ((2*L+2)*H)^2
  by_cases hF : F.Nonempty
  · obtain ⟨t₀, ht₀⟩ := hF
    have hmem : ∀ t ∈ F, t ∈ P ∧ gridCell endpoint r t=k ∧ firstTimes t=z := by
      intro t ht
      obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.mp ht
      obtain ⟨htP, htk⟩ := Finset.mem_filter.mp ht₁
      exact ⟨htP, htk, ht₂⟩
    have hnear : ∀ t ∈ F, |t.1.2-t₀.1.2| ≤ L*r ∧ |t.2.2-t₀.2.2| ≤ L*r := by
      intro t ht
      have hcell : gridCell endpoint r t = gridCell endpoint r t₀ :=
        (hmem t ht).2.1.trans (hmem t₀ ht₀).2.1.symm
      have hcell₁ : ⌊(endpoint t).1/r⌋ = ⌊(endpoint t₀).1/r⌋ :=
        congrArg (fun p : ℤ × ℤ => p.1) hcell
      have hcell₂ : ⌊(endpoint t).2/r⌋ = ⌊(endpoint t₀).2/r⌋ :=
        congrArg (fun p : ℤ × ℤ => p.2) hcell
      have hc := coefficient_control hh hfirst htrans hv₁x hv₁y hv₂x hv₂y
        (same_floor_abs_sub_le hr hcell₁) (same_floor_abs_sub_le hr hcell₂)
        (happrox t (hmem t ht).1).1 (happrox t (hmem t ht).1).2
        (happrox t₀ (hmem t₀ ht₀).1).1 (happrox t₀ (hmem t₀ ht₀).1).2
      have heq : firstTimes t = firstTimes t₀ :=
        (hmem t ht).2.2.trans (hmem t₀ ht₀).2.2.symm
      have heq₁ : t.1.1=t₀.1.1 := by
        simpa only [firstTimes] using congrArg (fun p : ℝ × ℝ => p.1) heq
      have heq₂ : t.2.1=t₀.2.1 := by
        simpa only [firstTimes] using congrArg (fun p : ℝ × ℝ => p.2) heq
      rw [heq₁, heq₂] at hc
      simpa only [sub_sub_sub_cancel_right] using hc
    let U₁ := Z.filter (fun q => |q-t₀.1.2| ≤ L*r)
    let U₂ := Z.filter (fun q => |q-t₀.2.2| ≤ L*r)
    have himage : F.image secondTimes ⊆ U₁ ×ˢ U₂ := by
      intro q hq
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
      have htZ := Finset.mem_product.mp (hsub (hmem t ht).1)
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp htZ.1).2, (hnear t ht).1⟩,
        Finset.mem_filter.mpr ⟨(Finset.mem_product.mp htZ.2).2, (hnear t ht).2⟩⟩
    have hinj := firstTimes_fixed_secondTimes_injective F z (fun t ht => (hmem t ht).2.2)
    have hcard : (F.card : ℝ) ≤ (U₁.card : ℝ)*(U₂.card : ℝ) := by
      rw [← Nat.cast_mul, ← Finset.card_product, ← Finset.card_image_of_injOn hinj]
      exact_mod_cast Finset.card_le_card himage
    have hU₁ : (U₁.card : ℝ) ≤ (2*L+2)*H := interval_population Z hr hH hL hcap
    have hU₂ : (U₂.card : ℝ) ≤ (2*L+2)*H := interval_population Z hr hH hL hcap
    calc
      (F.card : ℝ) ≤ (U₁.card : ℝ)*(U₂.card : ℝ) := hcard
      _ ≤ ((2*L+2)*H)*((2*L+2)*H) :=
        mul_le_mul hU₁ hU₂ (Nat.cast_nonneg _) (by positivity)
      _ = ((2*L+2)*H)^2 := by ring
  · have hzero : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    rw [hzero]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- The fixed-angle two-dimensional endpoint count. Every multiplicity is
derived from the original interval cap and transverse geometry. -/
theorem two_dimensional_fixed_angle_growth
    (Z : Finset ℝ) (P : Finset TimePath) (endpoint : TimePath → ℝ × ℝ)
    {r H E h V x₀ y₀ v₁x v₁y v₂x v₂y : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H) (hE : 0 ≤ E)
    (hh : 0 < h) (hhone : h ≤ 1) (hV : 0 < V)
    (hsub : P ⊆ (Z ×ˢ Z) ×ˢ (Z ×ˢ Z))
    (hfirst : h ≤ max |v₁x| |v₁y|)
    (htrans : ∀ s : ℝ, h ≤ max |v₂x-s*v₁x| |v₂y-s*v₁y|)
    (hv₁x : |v₁x| ≤ V) (hv₁y : |v₁y| ≤ V)
    (hv₂x : |v₂x| ≤ V) (hv₂y : |v₂y| ≤ V)
    (hcap : ∀ b : ℝ, ((Z.filter (fun z => b ≤ z ∧ z ≤ b+r)).card : ℝ) ≤ H)
    (happrox : ∀ t ∈ P,
      |(endpoint t).1-x₀-(t.1.2-t.1.1)*v₁x-(t.2.2-t.2.1)*v₂x| ≤ 2*E*r ∧
      |(endpoint t).2-y₀-(t.1.2-t.1.1)*v₁y-(t.2.2-t.2.1)*v₂y| ≤ 2*E*r) :
    h^4*(P.card : ℝ) ≤ (4*V*(1+4*E)+2)^2*H^2*(Z.card : ℝ)^2*
      ((P.image (gridCell endpoint r)).card : ℝ) := by
  classical
  let L : ℝ := 2*V*(1+4*E)/h^2
  let D : ℝ := 2*L+2
  let C : ℝ := 4*V*(1+4*E)+2
  let Q := P.image (gridCell endpoint r)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfib : ∀ k ∈ Q,
      ((P.filter (fun t => gridCell endpoint r t=k)).card : ℝ) ≤
        (Z.card : ℝ)^2*(D*H)^2 := by
    intro k _hk
    have hf := card_le_real_mul_of_fibers
      (P.filter (fun t => gridCell endpoint r t=k)) (Z ×ˢ Z) firstTimes ((D*H)^2) ?_ ?_
    · simpa only [Finset.card_product, Nat.cast_mul, pow_two] using hf
    · intro t ht
      have htZ := Finset.mem_product.mp (hsub (Finset.mem_filter.mp ht).1)
      exact Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp htZ.1).1, (Finset.mem_product.mp htZ.2).1⟩
    · intro z _hz
      exact two_dimensional_endpoint_fiber Z P endpoint hr hH hE hh hV hsub hfirst htrans
        hv₁x hv₁y hv₂x hv₂y hcap happrox k z
  have hcard := card_le_real_mul_of_fibers P Q (gridCell endpoint r) _
    (fun t ht => Finset.mem_image_of_mem _ ht) hfib
  have hnumeric : h^2*D ≤ C := by
    have hc : h^2*L = 2*V*(1+4*E) := by
      exact mul_div_cancel₀ _ (pow_ne_zero 2 hh.ne')
    have hsq : h^2 ≤ 1 := by nlinarith
    dsimp [D, C]
    nlinarith
  have hnumeric_sq : (h^2*D)^2 ≤ C^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnumeric)
      (show 0 ≤ C+h^2*D by positivity)]
  have hrest : 0 ≤ H^2*(Z.card : ℝ)^2*(Q.card : ℝ) := by positivity
  change h^4*(P.card : ℝ) ≤ C^2*H^2*(Z.card : ℝ)^2*(Q.card : ℝ)
  calc
    h^4*(P.card : ℝ) ≤ h^4*((Q.card : ℝ)*((Z.card : ℝ)^2*(D*H)^2)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (h^2*D)^2*(H^2*(Z.card : ℝ)^2*(Q.card : ℝ)) := by ring
    _ ≤ C^2*(H^2*(Z.card : ℝ)^2*(Q.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hnumeric_sq hrest
    _ = C^2*H^2*(Z.card : ℝ)^2*(Q.card : ℝ) := by ring

end

end TwoDimensionalTimeFibers
