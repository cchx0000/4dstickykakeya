import Theorems.Thm_StickyKakeya4_native_fixed_size_scale_menu
import Theorems.Thm_StickyKakeya4_native_incident_rank_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeRankRadiusMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeFixedSizeScaleMenu NativeDirectionRankDichotomy NativeIncidentRankSelection

/-- The radius is attached to the already installed original parent map. -/
def radius (w : ℝ) (hw : 0 ≤ w) (g level : ℕ) (j : Fin (g+1)) : ℝ :=
  1/(48*((2^(windowSchedule w hw g level j).val:ℕ):ℝ))

lemma radius_pos (w : ℝ) (hw : 0 ≤ w) (g level : ℕ) (j : Fin (g+1)) :
    0 < radius w hw g level j := by
  unfold radius
  positivity

lemma radius_parent_identity (w : ℝ) (hw : 0 ≤ w) (g level : ℕ)
    (j : Fin (g+1)) :
    48*((2^(windowSchedule w hw g level j).val:ℕ):ℝ)*radius w hw g level j=1 := by
  unfold radius
  have hN : (((2^(windowSchedule w hw g level j).val:ℕ):ℝ)) ≠ 0 := by positivity
  field_simp

lemma radius_le_one_div_48 (w : ℝ) (hw : 0 ≤ w) (g level : ℕ)
    (j : Fin (g+1)) : radius w hw g level j ≤ 1/48 := by
  have hN : (1:ℝ) ≤ ((2^(windowSchedule w hw g level j).val:ℕ):ℝ) := by
    exact_mod_cast (Nat.one_le_pow _ _ (by norm_num : 1 ≤ (2:ℕ)))
  unfold radius
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith

/-- The source cutoff supplies all geometric scale conditions, uniformly
over the fixed reference menu. -/
theorem radius_geometry {delta : ℝ} (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hlarge : 4 ≤ w*(level:ℝ))
    (hdy : delta=(2:ℝ)⁻¹^level) (hcut : delta^(w/2) ≤ 1/48)
    (j : Fin (g+1)) :
    delta ≤ radius w hw.le g level j ∧ radius w hw.le g level j ≤ 1/4 ∧
      48*((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ)*
        radius w hw.le g level j=1 ∧
      ((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ)*delta ≤ 1 := by
  obtain ⟨hl,hu⟩ := windowSchedule_bounds w hw hwsmall g level hlarge j
  obtain ⟨_hfirst,hsecond⟩ := depth_window_powers level _ hdy hl hu
  have hN : (0:ℝ) < ((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ) := by positivity
  have hsmall : ((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ)*delta ≤ 1/48 := by
    have hh := hsecond.trans hcut
    simpa only [div_div_eq_mul_div,div_one,mul_comm] using hh
  refine ⟨?_,(radius_le_one_div_48 w hw.le g level j).trans (by norm_num),
    radius_parent_identity w hw.le g level j,hsmall.trans (by norm_num)⟩
  unfold radius
  apply (le_div_iff₀ (mul_pos (by norm_num) hN)).mpr
  nlinarith

lemma last_depth_ge_half (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hg : 0 < g) (hlarge : 4 ≤ w*(level:ℝ)) :
    (level:ℝ)/2 ≤ (windowSchedule w hw.le g level (Fin.last g)).val := by
  rw [windowSchedule_last w hw.le g level hg]
  have hfloor := Nat.lt_floor_add_one ((1-w/2)*(level:ℝ))
  have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
  have hwL := mul_le_mul_of_nonneg_right hwsmall.le hln
  change (level:ℝ)/2 ≤ (⌊(1-w/2)*(level:ℝ)⌋₊:ℝ)
  nlinarith

/-- The final installed radius meets every cutoff exponent at most one half. -/
lemma last_radius_le_cutoff {delta : ℝ} (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hg : 0 < g) (hlarge : 4 ≤ w*(level:ℝ))
    (hdy : delta=(2:ℝ)⁻¹^level) (a : ℝ) (ha : a ≤ 1/2) :
    radius w hw.le g level (Fin.last g) ≤ delta^a := by
  have hd0 : 0 < delta := by rw [hdy]; positivity
  have hd1 : delta ≤ 1 := by
    rw [hdy]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hd : delta=(2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,inv_pow]
  have hhalf := last_depth_ge_half w hw hwsmall g level hg hlarge
  have hpow : 1/((2^(windowSchedule w hw.le g level (Fin.last g)).val:ℕ):ℝ) ≤
      delta^(1/2:ℝ) := by
    rw [hd,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have he : 1/((2^(windowSchedule w hw.le g level (Fin.last g)).val:ℕ):ℝ) =
        (2:ℝ)^(-((windowSchedule w hw.le g level (Fin.last g)).val:ℝ)) := by
      simp only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
        Nat.cast_pow,Nat.cast_ofNat,one_div]
    rw [he]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    linarith
  apply le_trans ?_ (hpow.trans (Real.rpow_le_rpow_of_exponent_ge hd0 hd1 ha))
  unfold radius
  apply one_div_le_one_div_of_le (by positivity)
  have hN : (0:ℝ) ≤ ((2^(windowSchedule w hw.le g level (Fin.last g)).val:ℕ):ℝ) := by positivity
  nlinarith

def allowed (delta w : ℝ) (hw : 0 ≤ w) (g level : ℕ) (a : ℝ) : Finset (Fin (g+1)) :=
  univ.filter (fun j => radius w hw g level j ≤ delta^a)

lemma allowed_nonempty {delta : ℝ} (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hg : 0 < g) (hlarge : 4 ≤ w*(level:ℝ))
    (hdy : delta=(2:ℝ)⁻¹^level) (a : ℝ) (ha : a ≤ 1/2) :
    (allowed delta w hw.le g level a).Nonempty := by
  refine ⟨Fin.last g,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
  exact last_radius_le_cutoff w hw hwsmall g level hg hlarge hdy a ha

/-- Increasing the power exponent shrinks the allowed radius submenu. -/
lemma allowed_antitone {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1)
    (w : ℝ) (hw : 0 ≤ w) (g level : ℕ) {a b : ℝ} (hab : a ≤ b) :
    allowed delta w hw g level b ⊆ allowed delta w hw g level a := by
  intro j hj
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2.trans
    (Real.rpow_le_rpow_of_exponent_ge hd0 hd1 hab)⟩

/-- A largest installed test radius below the target automatically contains
the stopping radius. The scalar exponent comparison proves that this test
belongs to the previous rank's allowed cutoff, also on any fixed submenu. -/
theorem exists_test_radius {delta : ℝ} (w : ℝ) (hw : 0 ≤ w) (g level : ℕ)
    (hdy : delta=(2:ℝ)⁻¹^level) (M : Finset (Fin (g+1)))
    (stop : Fin (g+1)) (hstopM : stop∈M) (a b beta : ℝ)
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hstop : radius w hw g level stop ≤ delta^a) (hcompat : b ≤ a*beta) :
    ∃test∈M,test∈allowed delta w hw g level b ∧
      radius w hw g level stop ≤ radius w hw g level test ∧
      radius w hw g level test ≤ (radius w hw g level stop)^beta ∧
      ∀j∈M,radius w hw g level j ≤ (radius w hw g level stop)^beta →
        radius w hw g level j ≤ radius w hw g level test := by
  have hd0 : 0 < delta := by rw [hdy]; positivity
  have hd1 : delta ≤ 1 := by
    rw [hdy]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hr0 := radius_pos w hw g level stop
  have hr1 : radius w hw g level stop ≤ 1 :=
    (radius_le_one_div_48 w hw g level stop).trans (by norm_num)
  have hself : radius w hw g level stop ≤ (radius w hw g level stop)^beta := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hbeta1)
  have htarget : (radius w hw g level stop)^beta ≤ delta^b := by
    calc
      _ ≤ (delta^a)^beta := Real.rpow_le_rpow hr0.le hstop hbeta.le
      _ = delta^(a*beta) := (Real.rpow_mul hd0.le a beta).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd0 hd1 hcompat
  let T := M.filter (fun j => radius w hw g level j ≤ (radius w hw g level stop)^beta)
  have hstopT : stop∈T := mem_filter.mpr ⟨hstopM,hself⟩
  obtain ⟨test,htest,hmax⟩ := exists_max_image T (radius w hw g level) ⟨stop,hstopT⟩
  obtain ⟨htestM,htarget'⟩ := mem_filter.mp htest
  refine ⟨test,htestM,mem_filter.mpr ⟨mem_univ _,htarget'.trans htarget⟩,
    hmax stop hstopT,htarget',?_⟩
  intro j hj hjs
  exact hmax j (mem_filter.mpr ⟨hj,hjs⟩)

/-- A fixed positive rank cutoff, independent of the later master tolerance,
gives a lower bound on the winning parent depth after a source cutoff. -/
theorem depth_lower_of_radius_cutoff {delta : ℝ} (w : ℝ) (hw : 0 ≤ w)
    (g level : ℕ) (hdy : delta=(2:ℝ)⁻¹^level) (j : Fin (g+1))
    (aMin a : ℝ) (hmin : aMin ≤ a) (hcut : delta^(aMin/2) ≤ 1/48)
    (hstop : radius w hw g level j ≤ delta^a) :
    (aMin/2)*(level:ℝ) ≤ (windowSchedule w hw g level j).val ∧
      1/((2^(windowSchedule w hw g level j).val:ℕ):ℝ) ≤ delta^(aMin/2) := by
  have hd0 : 0 < delta := by rw [hdy]; positivity
  have hd1 : delta ≤ 1 := by
    rw [hdy]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hstop' := hstop.trans (Real.rpow_le_rpow_of_exponent_ge hd0 hd1 hmin)
  have hsq : delta^aMin=(delta^(aMin/2))^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hd0.le]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_left hcut (Real.rpow_nonneg hd0.le (aMin/2))
  have htarget : 48*delta^aMin ≤ delta^(aMin/2) := by nlinarith
  have hid : 48*radius w hw g level j = 1/((2^(windowSchedule w hw g level j).val:ℕ):ℝ) := by
    unfold radius
    have hN : (((2^(windowSchedule w hw g level j).val:ℕ):ℝ)) ≠ 0 := by positivity
    field_simp
  have hpow : 1/((2^(windowSchedule w hw g level j).val:ℕ):ℝ) ≤ delta^(aMin/2) := by
    rw [←hid]
    exact (mul_le_mul_of_nonneg_left hstop' (by norm_num)).trans htarget
  refine ⟨?_,hpow⟩
  have hd : delta=(2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,inv_pow]
  have he : 1/((2^(windowSchedule w hw g level j).val:ℕ):ℝ) =
      (2:ℝ)^(-((windowSchedule w hw g level j).val:ℝ)) := by
    simp only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
      Nat.cast_pow,Nat.cast_ofNat,one_div]
  rw [he,hd,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at hpow
  have hh := (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hpow
  nlinarith

theorem relative_power_of_radius_cutoff {delta : ℝ} (w : ℝ) (hw : 0 ≤ w)
    (g level : ℕ) (hdy : delta=(2:ℝ)⁻¹^level) (j : Fin (g+1))
    (aMin a tau : ℝ) (haMin : 0 < aMin) (htau : 0 ≤ tau)
    (hmin : aMin ≤ a) (hcut : delta^(aMin/2) ≤ 1/48)
    (hstop : radius w hw g level j ≤ delta^a) :
    (1/((2^(windowSchedule w hw g level j).val:ℕ):ℝ))^(2*tau/aMin) ≤ delta^tau := by
  have hd0 : 0 < delta := by rw [hdy]; positivity
  have hp := (depth_lower_of_radius_cutoff w hw g level hdy j aMin a hmin hcut hstop).2
  have hexponent : 0 ≤ 2*tau/aMin := by positivity
  have hh := Real.rpow_le_rpow (by positivity) hp hexponent
  rw [←Real.rpow_mul hd0.le] at hh
  have he : (aMin/2)*(2*tau/aMin)=tau := by field_simp [haMin.ne']
  simpa only [he] using hh

/-- Rank and radius are selected from the parent maps installed before E.
The original point degrees supply the category weights and all plane witnesses
are produced by the finite direction selection theorem. -/
theorem exists_installed_rank_retention {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (hEn : E.Nonempty)
    (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2) (g level : ℕ) (hg : 0 < g)
    (hlarge : 4 ≤ w*(level:ℝ)) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcut : D.thickness^(w/2) ≤ 1/48)
    (a eta : Fin 4 → ℝ) (ha : ∀ell,0 < a ell ∧ a ell ≤ 1/2)
    (heta : ∀ell,0 < eta ell) :
    ∃ell : Fin 4,∃j : Fin (g+1),
      radius w hw.le g level j ≤ D.thickness^(a ell) ∧
      D.thickness ≤ radius w hw.le g level j ∧ radius w hw.le g level j ≤ 1/4 ∧
      48*((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ)*radius w hw.le g level j=1 ∧
      ((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ)*D.thickness ≤ 1 ∧
      ∃F⊆E,F.Nonempty ∧
        ((radius w hw.le g level j)^(eta ell)/(4*((g:ℝ)+1)))*(E.card:ℝ) ≤ (F.card:ℝ) ∧
        ∃P : Index → Submodule ℝ E4,
          (∀z∈F,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ radius w hw.le g level j) ∧
          ∀k∈F.image Prod.snd,
            Module.finrank ℝ (P k) ≤ ell.val+1 ∧
            pointSet F k=pointNear D E k (radius w hw.le g level j) (P k) ∧
            (radius w hw.le g level j)^(eta ell)*((pointSet E k).card:ℝ) ≤ (pointSet F k).card ∧
            ∀ell' : Fin 4,ell' < ell → ∀j' : Fin (g+1),
              radius w hw.le g level j' ≤ D.thickness^(a ell') →
              ∀Q : Submodule ℝ E4,Module.finrank ℝ Q ≤ ell'.val+1 →
                ((pointNear D E k (radius w hw.le g level j') Q).card:ℝ) <
                  (radius w hw.le g level j')^(eta ell')*((pointSet E k).card:ℝ) := by
  obtain ⟨ell,j,hj,F,hFE,hFn,hret,P,hnear,hpoints⟩ :=
    exists_rank_scale_retention D E hEn (univ:Finset (Fin (g+1)))
      (radius w hw.le g level) eta (fun ell => allowed D.thickness w hw.le g level (a ell))
      (fun _ => filter_subset _ _) heta
      (fun j _hj => ⟨radius_pos w hw.le g level j,
        (radius_le_one_div_48 w hw.le g level j).trans (by norm_num)⟩)
      (allowed_nonempty w hw hwsmall g level hg hlarge hdy (a 3) (ha 3).2)
  obtain ⟨hrlo,hrhi,hidentity,hscale⟩ := radius_geometry w hw hwsmall g level hlarge hdy hcut j
  refine ⟨ell,j,(mem_filter.mp hj).2,hrlo,hrhi,hidentity,hscale,F,hFE,hFn,?_,P,hnear,?_⟩
  · simpa only [card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hret
  · intro k hk
    obtain ⟨hdim,hfiber,hmass,hearlier⟩ := hpoints k hk
    refine ⟨hdim,hfiber,hmass,?_⟩
    intro ell' hell' j' hj' Q hQ
    exact hearlier ell' hell' j' (mem_filter.mpr ⟨mem_univ _,hj'⟩) Q hQ

end NativeRankRadiusMenu
