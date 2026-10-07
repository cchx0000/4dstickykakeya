import Theorems.Thm_StickyKakeya4_native_dyadic_parent_cells

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeFixedSizeScaleMenu

/-- The number of entries is fixed independently of the source depth. -/
def schedule (g level : ℕ) (j : Fin (g+1)) : Fin (level+1) :=
  ⟨j.val*level/g, Nat.lt_succ_of_le (Nat.div_le_of_le_mul
    (Nat.mul_le_mul_right level (Nat.le_of_lt_succ j.isLt)))⟩

lemma schedule_zero (g level : ℕ) : (schedule g level 0).val = 0 := by
  simp [schedule]

lemma schedule_last (g level : ℕ) (hg : 0 < g) :
    (schedule g level (Fin.last g)).val = level := by
  exact Nat.mul_div_cancel_left level hg

/-- Integer division supplies a predecessor in the fixed menu, with both
the integer gap and its sharper real-valued estimate. -/
theorem exists_predecessor (g level m : ℕ) (hg : 0 < g)
    (hlevel : 0 < level) (hm : m ≤ level) :
    ∃ j : Fin (g+1), (schedule g level j).val ≤ m ∧
      m-(schedule g level j).val ≤ level/g+1 ∧
      ((m-(schedule g level j).val : ℕ) : ℝ) ≤ (level:ℝ)/g+1 := by
  let j : ℕ := m*g/level
  have hj : j ≤ g := Nat.div_le_of_le_mul (by nlinarith)
  let c : ℕ := j*level/g
  have hjlo : j*level ≤ m*g := Nat.div_mul_le_self (m*g) level
  have hjhi : m*g < level*(j+1) := Nat.lt_mul_div_succ (m*g) hlevel
  have hclo : c*g ≤ j*level := Nat.div_mul_le_self (j*level) g
  have hchi : j*level < g*(c+1) := Nat.lt_mul_div_succ (j*level) hg
  have hcm : c ≤ m := by nlinarith
  have hsub : m-c+c=m := Nat.sub_add_cancel hcm
  have hdiff : (m-c)*g < level+g := by nlinarith
  have hlevelhi : level < g*(level/g+1) := Nat.lt_mul_div_succ level hg
  have hgap : m-c ≤ level/g+1 := by nlinarith
  have hgr : (0:ℝ) < g := by exact_mod_cast hg
  have hdiffR : ((m-c:ℕ):ℝ)*(g:ℝ) < (level:ℝ)+g := by exact_mod_cast hdiff
  have hgapR : ((m-c:ℕ):ℝ) ≤ (level:ℝ)/g+1 := by
    calc
      _ ≤ ((level:ℝ)+g)/g := (le_div_iff₀ hgr).mpr hdiffR.le
      _ = _ := by rw [add_div,div_self hgr.ne']
  exact ⟨⟨j,by omega⟩,hcm,hgap,hgapR⟩

/-- A preceding menu depth stays inside the relaxed power window. -/
theorem exists_predecessor_in_window (w : ℝ) (hw : 0 < w)
    (_hwsmall : w < 1/2) (g level m : ℕ) (hg : 0 < g)
    (hgrid : 1/(g:ℝ) < w/4) (hlarge : 4 ≤ w*(level:ℝ))
    (hlo : w*(level:ℝ) ≤ m) (hhi : (m:ℝ) ≤ (1-w)*(level:ℝ)) :
    ∃ j : Fin (g+1), (schedule g level j).val ≤ m ∧
      m-(schedule g level j).val ≤ level/g+1 ∧
      ((m-(schedule g level j).val : ℕ) : ℝ) ≤ (level:ℝ)/g+1 ∧
      (w/2)*(level:ℝ) ≤ (schedule g level j).val ∧
      ((schedule g level j).val:ℝ) ≤ (1-w/2)*(level:ℝ) := by
  have hlpos : 0 < level := by
    by_contra hnot
    have he : level=0 := by omega
    simp only [he,Nat.cast_zero,mul_zero] at hlarge
    norm_num at hlarge
  have hm : m ≤ level := by
    have hnon : 0 ≤ (level:ℝ) := Nat.cast_nonneg _
    have hh : (m:ℝ) ≤ level := by nlinarith
    exact_mod_cast hh
  obtain ⟨j,hjm,hgap,hgapR⟩ := exists_predecessor g level m hg hlpos hm
  have hsub : ((m-(schedule g level j).val:ℕ):ℝ) =
      (m:ℝ)-(schedule g level j).val := by rw [Nat.cast_sub hjm]
  have hgrid' := mul_le_mul_of_nonneg_right hgrid.le (Nat.cast_nonneg level : (0:ℝ)≤level)
  have hlg : (level:ℝ)/g ≤ (w/4)*(level:ℝ) := by
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hgrid'
  have hjmR : ((schedule g level j).val:ℝ) ≤ m := by exact_mod_cast hjm
  refine ⟨j,hjm,hgap,hgapR,?_,?_⟩
  · rw [hsub] at hgapR
    nlinarith
  · have hnon : 0 ≤ (level:ℝ) := Nat.cast_nonneg _
    nlinarith

/-- Exact conversion of a depth gap into an original-scale power. -/
lemma dyadic_gap_power {delta : ℝ} (level m c g : ℕ) (_hg : 0 < g)
    (hdy : delta=(2:ℝ)⁻¹^level)
    (hgap : ((m-c:ℕ):ℝ) ≤ (level:ℝ)/g+1) :
    ((2^(m-c):ℕ):ℝ) ≤ 2*delta^(-(1/(g:ℝ))) := by
  have hd2 : delta = (2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,inv_pow]
  have hdelta : delta^(-(1/(g:ℝ))) = (2:ℝ)^((level:ℝ)/g) := by
    rw [hd2,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  rw [hdelta,Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hgap
  rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one] at hp
  simpa only [mul_comm] using hp

/-- A dyadic source cutoff forces the requested lower bound on its depth. -/
lemma depth_le_of_dyadic_cutoff {delta : ℝ} (level N : ℕ)
    (hdy : delta=(2:ℝ)⁻¹^level) (hsmall : delta ≤ (2:ℝ)⁻¹^N) : N ≤ level := by
  rw [hdy] at hsmall
  exact (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    (by norm_num : (2:ℝ)⁻¹<1)).mp hsmall

/-- Grid size and minimum depth are chosen before any source or level. -/
theorem exists_fixed_parameters (w : ℝ) (hw : 0 < w) :
    ∃ g N : ℕ, 0 < g ∧ 0 < N ∧ 1/(g:ℝ) < w/4 ∧
      ∀ level : ℕ, N ≤ level → 4 ≤ w*(level:ℝ) := by
  obtain ⟨g,hg⟩ := exists_nat_gt (4/w)
  have hgR : (0:ℝ)<g := (div_pos (by norm_num) hw).trans hg
  have hgN : 0<g := by exact_mod_cast hgR
  have hgrid : 1/(g:ℝ)<w/4 := by
    apply (div_lt_iff₀ hgR).mpr
    have hh := (div_lt_iff₀ hw).mp hg
    nlinarith
  refine ⟨g,g,hgN,hgN,hgrid,?_⟩
  intro level hlevel
  have hh := (div_lt_iff₀ hw).mp hg
  have hlevelR : (g:ℝ)≤level := by exact_mod_cast hlevel
  nlinarith

/-- Clamping changes no menu value already inside the specified interval. -/
def clippedSchedule (g level lo hi : ℕ) (hhi : hi ≤ level)
    (j : Fin (g+1)) : Fin (level+1) :=
  ⟨min hi (max lo (schedule g level j).val),
    Nat.lt_succ_of_le ((min_le_left _ _).trans hhi)⟩

lemma clippedSchedule_bounds (g level lo hi : ℕ) (hhi : hi ≤ level)
    (hlohi : lo ≤ hi) (j : Fin (g+1)) :
    lo ≤ (clippedSchedule g level lo hi hhi j).val ∧
      (clippedSchedule g level lo hi hhi j).val ≤ hi := by
  exact ⟨le_min hlohi (le_max_left _ _),min_le_left _ _⟩

lemma clippedSchedule_fix (g level lo hi : ℕ) (hhi : hi ≤ level)
    (j : Fin (g+1)) (hlo : lo ≤ (schedule g level j).val)
    (hup : (schedule g level j).val ≤ hi) :
    (clippedSchedule g level lo hi hhi j).val = (schedule g level j).val := by
  simp only [clippedSchedule,max_eq_right hlo,min_eq_right hup]

def lowerDepth (w : ℝ) (level : ℕ) : ℕ := ⌈(w/2)*(level:ℝ)⌉₊
def upperDepth (w : ℝ) (level : ℕ) : ℕ := ⌊(1-w/2)*(level:ℝ)⌋₊

lemma upperDepth_le (w : ℝ) (hw : 0 ≤ w) (level : ℕ) :
    upperDepth w level ≤ level := by
  apply Nat.floor_le_of_le
  have hl : (0:ℝ) ≤ level := Nat.cast_nonneg _
  nlinarith

lemma depth_interval_nonempty (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (level : ℕ) (hlarge : 4 ≤ w*(level:ℝ)) :
    lowerDepth w level ≤ upperDepth w level := by
  have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ (w/2)*(level:ℝ) by positivity)).le
  have hwL := mul_le_mul_of_nonneg_right hwsmall.le hln
  apply Nat.le_floor
  change (⌈(w/2)*(level:ℝ)⌉₊:ℝ) ≤ (1-w/2)*(level:ℝ)
  nlinarith

/-- Every entry of this fixed-size schedule lies in the relaxed window.
Repeated endpoints are allowed; no source-dependent cardinality is used. -/
def windowSchedule (w : ℝ) (hw : 0 ≤ w) (g level : ℕ) :
    Fin (g+1) → Fin (level+1) :=
  clippedSchedule g level (lowerDepth w level) (upperDepth w level)
    (upperDepth_le w hw level)

theorem windowSchedule_bounds (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hlarge : 4 ≤ w*(level:ℝ)) (j : Fin (g+1)) :
    (w/2)*(level:ℝ) ≤ (windowSchedule w hw.le g level j).val ∧
      ((windowSchedule w hw.le g level j).val:ℝ) ≤ (1-w/2)*(level:ℝ) := by
  obtain ⟨hl,hu⟩ := clippedSchedule_bounds g level (lowerDepth w level)
    (upperDepth w level) (upperDepth_le w hw.le level)
    (depth_interval_nonempty w hw hwsmall level hlarge) j
  constructor
  · exact (Nat.le_ceil _).trans (by exact_mod_cast hl)
  · exact (show ((windowSchedule w hw.le g level j).val:ℝ) ≤ upperDepth w level by
      exact_mod_cast hu).trans (Nat.floor_le (by
        have hl : (0:ℝ) ≤ level := Nat.cast_nonneg _
        have hw2 : 0 ≤ 1-w/2 := by linarith
        exact mul_nonneg hw2 hl))

/-- The raw predecessor is unchanged by clamping, so the entire admissible
schedule and every target-scale witness share one fixed finite index type. -/
theorem exists_window_predecessor (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level m : ℕ) (hg : 0 < g) (hgrid : 1/(g:ℝ) < w/4)
    (hlarge : 4 ≤ w*(level:ℝ))
    (hlo : w*(level:ℝ) ≤ m) (hhi : (m:ℝ) ≤ (1-w)*(level:ℝ)) :
    ∃ j : Fin (g+1), (windowSchedule w hw.le g level j).val ≤ m ∧
      m-(windowSchedule w hw.le g level j).val ≤ level/g+1 ∧
      ((m-(windowSchedule w hw.le g level j).val:ℕ):ℝ) ≤ (level:ℝ)/g+1 := by
  obtain ⟨j,hjm,hgap,hgapR,hjl,hju⟩ :=
    exists_predecessor_in_window w hw hwsmall g level m hg hgrid hlarge hlo hhi
  have hl : lowerDepth w level ≤ (schedule g level j).val := Nat.ceil_le.mpr hjl
  have hu : (schedule g level j).val ≤ upperDepth w level := Nat.le_floor hju
  have he := clippedSchedule_fix g level (lowerDepth w level) (upperDepth w level)
    (upperDepth_le w hw.le level) j hl hu
  change (windowSchedule w hw.le g level j).val = (schedule g level j).val at he
  exact ⟨j,by simpa only [he] using hjm,by simpa only [he] using hgap,
    by simpa only [he] using hgapR⟩

lemma windowSchedule_zero (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hlarge : 4 ≤ w*(level:ℝ)) :
    (windowSchedule w hw.le g level 0).val = lowerDepth w level := by
  have hh := depth_interval_nonempty w hw hwsmall level hlarge
  simp only [windowSchedule,clippedSchedule,schedule_zero,Nat.max_zero,min_eq_right hh]

lemma windowSchedule_last (w : ℝ) (hw : 0 ≤ w) (g level : ℕ) (hg : 0 < g) :
    (windowSchedule w hw g level (Fin.last g)).val = upperDepth w level := by
  have hh := (upperDepth_le w hw level).trans (le_max_right (lowerDepth w level) level)
  simp only [windowSchedule,clippedSchedule,schedule_last g level hg,min_eq_left hh]

/-- Real depth-window inequalities are exactly the required original-scale
power windows; the dyadic level is not replaced by a logarithmic estimate. -/
lemma depth_window_powers {delta w : ℝ} (level c : ℕ)
    (hdy : delta=(2:ℝ)⁻¹^level)
    (hlo : (w/2)*(level:ℝ) ≤ c) (hhi : (c:ℝ) ≤ (1-w/2)*(level:ℝ)) :
    1/((2^c:ℕ):ℝ) ≤ delta^(w/2) ∧
      delta/(1/((2^c:ℕ):ℝ)) ≤ delta^(w/2) := by
  have hd : delta = (2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,inv_pow]
  have hr : 1/((2^c:ℕ):ℝ) = (2:ℝ)^(-(c:ℝ)) := by
    simp only [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,
      Nat.cast_pow,Nat.cast_ofNat,one_div]
  have he : delta^(w/2) = (2:ℝ)^(-(level:ℝ)*(w/2)) := by
    rw [hd,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  constructor
  · rw [hr,he]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    nlinarith
  · rw [hr,he,hd,←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    nlinarith

/-- A single cutoff and a single finite index count are chosen before the
dyadic source. Every scheduled scale is admitted to the relaxed window, and
every scale in the target window has a preceding scheduled witness. -/
theorem exists_source_window_menu (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2) :
    ∃ (g : ℕ) (delta0 : ℝ), 0 < g ∧ 0 < delta0 ∧ 1/(g:ℝ) < w/4 ∧
      ∀ (delta : ℝ) (level : ℕ), delta=(2:ℝ)⁻¹^level → delta ≤ delta0 →
        (∀ j : Fin (g+1),
          1/((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ) ≤ delta^(w/2) ∧
          delta/(1/((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ)) ≤ delta^(w/2)) ∧
        ∀ m : ℕ, w*(level:ℝ) ≤ m → (m:ℝ) ≤ (1-w)*(level:ℝ) →
          ∃ j : Fin (g+1), (windowSchedule w hw.le g level j).val ≤ m ∧
            m-(windowSchedule w hw.le g level j).val ≤ level/g+1 ∧
            ((m-(windowSchedule w hw.le g level j).val:ℕ):ℝ) ≤ (level:ℝ)/g+1 ∧
            ((2^(m-(windowSchedule w hw.le g level j).val):ℕ):ℝ) ≤
              2*delta^(-(1/(g:ℝ))) := by
  obtain ⟨g,N,hg,_hN,hgrid,hlarge⟩ := exists_fixed_parameters w hw
  refine ⟨g,(2:ℝ)⁻¹^N,hg,by positivity,hgrid,?_⟩
  intro delta level hdy hsmall
  have hL := hlarge level (depth_le_of_dyadic_cutoff level N hdy hsmall)
  refine ⟨?_,?_⟩
  · intro j
    obtain ⟨hl,hu⟩ := windowSchedule_bounds w hw hwsmall g level hL j
    exact depth_window_powers level _ hdy hl hu
  · intro m hlo hhi
    obtain ⟨j,hjm,hgap,hgapR⟩ :=
      exists_window_predecessor w hw hwsmall g level m hg hgrid hL hlo hhi
    exact ⟨j,hjm,hgap,hgapR,dyadic_gap_power level m _ g hg hdy hgapR⟩

/-- The rounding allowance can instead be absorbed into a pure fractional
depth gap, as required by the local multiplicity interpolation theorem. -/
lemma gap_le_twice_fraction (g level m c : ℕ) (hg : 0 < g) (hgl : g ≤ level)
    (hgap : ((m-c:ℕ):ℝ) ≤ (level:ℝ)/g+1) :
    ((m-c:ℕ):ℝ) ≤ (2/(g:ℝ))*(level:ℝ) := by
  have hgr : (0:ℝ) < g := by exact_mod_cast hg
  have hlg : (1:ℝ) ≤ (level:ℝ)/g := by
    apply (le_div_iff₀ hgr).mpr
    simpa only [one_mul] using (show (g:ℝ) ≤ level by exact_mod_cast hgl)
  have he : (2/(g:ℝ))*(level:ℝ) = 2*((level:ℝ)/g) := by ring
  rw [he]
  linarith

lemma gap_le_twice_fraction_of_cutoff {delta : ℝ} (g level m c : ℕ) (hg : 0 < g)
    (hdy : delta=(2:ℝ)⁻¹^level) (hsmall : delta ≤ (2:ℝ)⁻¹^g)
    (hgap : ((m-c:ℕ):ℝ) ≤ (level:ℝ)/g+1) :
    ((m-c:ℕ):ℝ) ≤ (2/(g:ℝ))*(level:ℝ) :=
  gap_le_twice_fraction g level m c hg (depth_le_of_dyadic_cutoff level g hdy hsmall) hgap

end NativeFixedSizeScaleMenu
