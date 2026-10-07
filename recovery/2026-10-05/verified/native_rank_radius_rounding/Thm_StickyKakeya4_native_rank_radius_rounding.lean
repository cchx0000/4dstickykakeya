import Theorems.Thm_StickyKakeya4_native_rank_mesoscopic_radius_menu
import Theorems.Thm_StickyKakeya4_native_scale_menu_successor

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeRankRadiusRounding
open Classical Finset
open NativeFixedSizeScaleMenu NativeScaleMenuSuccessor NativeRankRadiusMenu

def atDepth (m : ℕ) : ℝ := 1/(48*((2^m:ℕ):ℝ))

lemma atDepth_pos (m : ℕ) : 0 < atDepth m := by unfold atDepth; positivity

lemma atDepth_antitone {m c : ℕ} (hmc : m ≤ c) : atDepth c ≤ atDepth m := by
  unfold atDepth
  apply one_div_le_one_div_of_le (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hmc

lemma atDepth_succ (m : ℕ) : atDepth m=2*atDepth (m+1) := by
  unfold atDepth
  rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
  have hN : (((2^m:ℕ):ℝ)) ≠ 0 := by positivity
  field_simp

lemma atDepth_ratio {m c : ℕ} (hmc : m ≤ c) :
    atDepth m=((2^(c-m):ℕ):ℝ)*atDepth c := by
  have he : (2^c:ℕ)=2^(c-m)*2^m :=
    (congrArg (fun n : ℕ => 2^n) (Nat.sub_add_cancel hmc).symm).trans (pow_add 2 _ _)
  unfold atDepth
  rw [he,Nat.cast_mul]
  have hN : (((2^m:ℕ):ℝ)) ≠ 0 := by positivity
  have hgap : (((2^(c-m):ℕ):ℝ)) ≠ 0 := by positivity
  field_simp

/-- A finite dyadic search brackets a real target without logarithms. -/
theorem exists_target_depth (lo hi : ℕ) (hlohi : lo ≤ hi) (s : ℝ)
    (hhi : atDepth hi ≤ s) (hlo : s ≤ atDepth lo) :
    ∃m∈Icc lo hi,atDepth m ≤ s ∧ s ≤ 2*atDepth m := by
  let A := (Icc lo hi).filter (fun m => atDepth m ≤ s)
  have hAn : A.Nonempty := ⟨hi,mem_filter.mpr ⟨mem_Icc.mpr ⟨hlohi,le_rfl⟩,hhi⟩⟩
  let m := A.min' hAn
  have hm : m∈A := A.min'_mem hAn
  obtain ⟨hmI,hms⟩ := mem_filter.mp hm
  obtain ⟨hml,hmh⟩ := mem_Icc.mp hmI
  refine ⟨m,hmI,hms,?_⟩
  by_cases he : m=lo
  · have hh : s ≤ atDepth m := by simpa only [he] using hlo
    nlinarith [atDepth_pos m]
  · have hprevI : m-1∈Icc lo hi := mem_Icc.mpr ⟨by omega,by omega⟩
    have hprev : s < atDepth (m-1) := by
      apply lt_of_not_ge
      intro hs
      have hprevA : m-1∈A := mem_filter.mpr ⟨hprevI,hs⟩
      have hmin : m ≤ m-1 := A.min'_le _ hprevA
      omega
    have hid := atDepth_succ (m-1)
    rw [show m-1+1=m by omega] at hid
    linarith

lemma gap_power {delta : ℝ} (level c m g : ℕ)
    (hdy : delta=(2:ℝ)⁻¹^level) (hgap : ((c-m:ℕ):ℝ) ≤ (level:ℝ)/g) :
    ((2^(c-m):ℕ):ℝ) ≤ delta^(-(1/(g:ℝ))) := by
  have hd : delta=(2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,inv_pow]
  have he : delta^(-(1/(g:ℝ)))=(2:ℝ)^((level:ℝ)/g) := by
    rw [hd,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [he,Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hgap

/-- Installed successors approximate every target above an installed stopping
radius. If a successor overshoots the stopping depth, the stopping entry itself
has a smaller gap. Thus any previously imposed depth cap is preserved. -/
theorem exists_near_radius {delta : ℝ} (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hg : 0 < g) (hlarge : 4 ≤ w*(level:ℝ))
    (hdy : delta=(2:ℝ)⁻¹^level) (cap : ℕ) (stop : Fin (g+1))
    (hstopcap : (windowSchedule w hw.le g level stop).val ≤ cap)
    (s : ℝ) (hstop : radius w hw.le g level stop ≤ s)
    (hfirst : s ≤ radius w hw.le g level 0) :
    ∃j : Fin (g+1),(windowSchedule w hw.le g level j).val ≤ cap ∧
      radius w hw.le g level j ≤ s ∧
      s ≤ (2*delta^(-(1/(g:ℝ))))*radius w hw.le g level j := by
  have hlpos : 0 < level := by
    by_contra hnot
    have he : level=0 := by omega
    simp only [he,Nat.cast_zero,mul_zero] at hlarge
    norm_num at hlarge
  have hinterval := depth_interval_nonempty w hw hwsmall level hlarge
  obtain ⟨hstoplo,hstophi⟩ := clippedSchedule_bounds g level (lowerDepth w level)
    (upperDepth w level) (upperDepth_le w hw.le level) hinterval stop
  change lowerDepth w level ≤ (windowSchedule w hw.le g level stop).val at hstoplo
  change (windowSchedule w hw.le g level stop).val ≤ upperDepth w level at hstophi
  have hfirst' : s ≤ atDepth (lowerDepth w level) := by
    simpa only [radius,windowSchedule_zero w hw hwsmall g level hlarge,atDepth] using hfirst
  obtain ⟨m,hmI,hms,hsm⟩ := exists_target_depth (lowerDepth w level)
    (windowSchedule w hw.le g level stop).val hstoplo s hstop hfirst'
  obtain ⟨hml,hmtop⟩ := mem_Icc.mp hmI
  obtain ⟨j,hjm,_hgap,hgapR⟩ := exists_clipped_successor g level (lowerDepth w level)
    (upperDepth w level) m hg hlpos (upperDepth_le w hw.le level) hml (hmtop.trans hstophi)
  change m ≤ (windowSchedule w hw.le g level j).val at hjm
  change (((windowSchedule w hw.le g level j).val-m:ℕ):ℝ) ≤ (level:ℝ)/g at hgapR
  have hex : ∃j' : Fin (g+1),m ≤ (windowSchedule w hw.le g level j').val ∧
      (windowSchedule w hw.le g level j').val ≤ (windowSchedule w hw.le g level stop).val ∧
      (((windowSchedule w hw.le g level j').val-m:ℕ):ℝ) ≤ (level:ℝ)/g := by
    by_cases hle : (windowSchedule w hw.le g level j).val ≤ (windowSchedule w hw.le g level stop).val
    · exact ⟨j,hjm,hle,hgapR⟩
    · refine ⟨stop,hmtop,le_rfl,?_⟩
      have hsub := Nat.sub_le_sub_right (le_of_not_ge hle) m
      exact (show (((windowSchedule w hw.le g level stop).val-m:ℕ):ℝ) ≤
        (((windowSchedule w hw.le g level j).val-m:ℕ):ℝ) by exact_mod_cast hsub).trans hgapR
  obtain ⟨j',hmj',hj'top,hj'gap⟩ := hex
  have hp := gap_power level (windowSchedule w hw.le g level j').val m g hdy hj'gap
  have hid := atDepth_ratio hmj'
  refine ⟨j',hj'top.trans hstopcap,(atDepth_antitone hmj').trans hms,?_⟩
  have hr : 0 ≤ atDepth (windowSchedule w hw.le g level j').val := (atDepth_pos _).le
  have hmul := mul_le_mul_of_nonneg_right hp hr
  change s ≤ (2*delta^(-(1/(g:ℝ))))*atDepth (windowSchedule w hw.le g level j').val
  rw [hid] at hsm
  nlinarith

/-- The maximal test index from the same mesoscopic reference menu has both
the ordering needed for exact rank and the quantitative finite-mesh lower bound. -/
theorem exists_mesoscopic_test_radius {delta : ℝ} (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hg : 0 < g) (hlarge : 4 ≤ w*(level:ℝ))
    (hdy : delta=(2:ℝ)⁻¹^level) (stop : Fin (g+1))
    (hstopM : stop∈NativeRankMesoscopicRadiusMenu.menu w hw.le g level)
    (a b beta : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hstop : radius w hw.le g level stop ≤ delta^a) (hcompat : b ≤ a*beta)
    (hfirst : (radius w hw.le g level stop)^beta ≤ radius w hw.le g level 0) :
    ∃test∈NativeRankMesoscopicRadiusMenu.allowed delta w hw.le g level b,
      radius w hw.le g level stop ≤ radius w hw.le g level test ∧
      radius w hw.le g level test ≤ (radius w hw.le g level stop)^beta ∧
      (radius w hw.le g level stop)^beta/(2*delta^(-(1/(g:ℝ)))) ≤ radius w hw.le g level test := by
  obtain ⟨test,htestM,htestcut,hstoptest,htarget,hmax⟩ := exists_test_radius w hw.le g level hdy
    (NativeRankMesoscopicRadiusMenu.menu w hw.le g level) stop hstopM a b beta hbeta hbeta1 hstop hcompat
  obtain ⟨j,hjcap,hjtarget,hjclose⟩ := exists_near_radius w hw hwsmall g level hg hlarge hdy
    (level/4) stop (mem_filter.mp hstopM).2 ((radius w hw.le g level stop)^beta)
    (hstoptest.trans htarget) hfirst
  have hjM : j∈NativeRankMesoscopicRadiusMenu.menu w hw.le g level := mem_filter.mpr ⟨mem_univ _,hjcap⟩
  have hjtest := hmax j hjM hjtarget
  have hd0 : 0 < delta := by rw [hdy]; positivity
  have hfactor : 0 < 2*delta^(-(1/(g:ℝ))) := by positivity
  refine ⟨test,mem_filter.mpr ⟨htestM,(mem_filter.mp htestcut).2⟩,hstoptest,htarget,?_⟩
  apply (div_le_iff₀ hfactor).mpr
  have hh := hjclose.trans (mul_le_mul_of_nonneg_left hjtest hfactor.le)
  simpa only [mul_comm] using hh

lemma first_radius_lower {delta : ℝ} (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hlarge : 4 ≤ w*(level:ℝ)) (hdy : delta=(2:ℝ)⁻¹^level) :
    delta^(w/2)/96 ≤ radius w hw.le g level 0 := by
  have hdepth : ((windowSchedule w hw.le g level 0).val:ℝ) ≤ (w/2)*(level:ℝ)+1 := by
    rw [windowSchedule_zero w hw hwsmall g level hlarge]
    exact (Nat.ceil_lt_add_one (show 0 ≤ (w/2)*(level:ℝ) by positivity)).le
  have hd : delta=(2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,inv_pow]
  have hp : delta^(w/2) ≤ 2/((2^(windowSchedule w hw.le g level 0).val:ℕ):ℝ) := by
    calc
      _ = (2:ℝ)^(-(level:ℝ)*(w/2)) := by
        rw [hd,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ (2:ℝ)^(1-((windowSchedule w hw.le g level 0).val:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        nlinarith
      _ = _ := by
        simp only [Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_one,
          Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat]
  have hid : 2/((2^(windowSchedule w hw.le g level 0).val:ℕ):ℝ) =
      96*radius w hw.le g level 0 := by
    unfold radius
    have hN : (((2^(windowSchedule w hw.le g level 0).val:ℕ):ℝ)) ≠ 0 := by positivity
    field_simp
    norm_num
  rw [hid] at hp
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 96)).mpr
  nlinarith

lemma target_le_first_radius {delta : ℝ} (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hlarge : 4 ≤ w*(level:ℝ)) (hdy : delta=(2:ℝ)⁻¹^level)
    (stop : Fin (g+1)) (a beta : ℝ) (hbeta : 0 ≤ beta)
    (hstop : radius w hw.le g level stop ≤ delta^a)
    (hcut : delta^(a*beta-w/2) ≤ 1/96) :
    (radius w hw.le g level stop)^beta ≤ radius w hw.le g level 0 := by
  have hd0 : 0 < delta := by rw [hdy]; positivity
  have hp : (radius w hw.le g level stop)^beta ≤ delta^(a*beta) := by
    calc
      _ ≤ (delta^a)^beta := Real.rpow_le_rpow (radius_pos w hw.le g level stop).le hstop hbeta
      _ = _ := (Real.rpow_mul hd0.le a beta).symm
  have hh := mul_le_mul_of_nonneg_left hcut (Real.rpow_nonneg hd0.le (w/2))
  have he : delta^(w/2)*delta^(a*beta-w/2)=delta^(a*beta) := by
    rw [←Real.rpow_add hd0]
    congr 1
    ring
  rw [he] at hh
  have hmid : delta^(a*beta) ≤ delta^(w/2)/96 := by
    simpa only [div_eq_mul_inv,one_div,one_mul] using hh
  exact hp.trans (hmid.trans (first_radius_lower w hw hwsmall g level hlarge hdy))

/-- The endpoint condition is discharged by a scalar source cutoff. There is
no supplied test index, radius admissibility witness, or new reference map. -/
theorem exists_mesoscopic_test_radius_of_cutoff {delta : ℝ}
    (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g level : ℕ) (hg : 0 < g) (hlarge : 4 ≤ w*(level:ℝ))
    (hdy : delta=(2:ℝ)⁻¹^level) (stop : Fin (g+1))
    (hstopM : stop∈NativeRankMesoscopicRadiusMenu.menu w hw.le g level)
    (a b beta : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hstop : radius w hw.le g level stop ≤ delta^a) (hcompat : b ≤ a*beta)
    (hcut : delta^(a*beta-w/2) ≤ 1/96) :
    ∃test∈NativeRankMesoscopicRadiusMenu.allowed delta w hw.le g level b,
      radius w hw.le g level stop ≤ radius w hw.le g level test ∧
      radius w hw.le g level test ≤ (radius w hw.le g level stop)^beta ∧
      (radius w hw.le g level stop)^beta/(2*delta^(-(1/(g:ℝ)))) ≤ radius w hw.le g level test :=
  exists_mesoscopic_test_radius w hw hwsmall g level hg hlarge hdy stop hstopM
    a b beta hbeta hbeta1 hstop hcompat
    (target_le_first_radius w hw hwsmall g level hlarge hdy stop a beta hbeta.le hstop hcut)

end NativeRankRadiusRounding
