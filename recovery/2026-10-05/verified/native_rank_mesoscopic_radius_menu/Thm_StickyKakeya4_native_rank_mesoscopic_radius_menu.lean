import Theorems.Thm_StickyKakeya4_native_rank_radius_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeRankMesoscopicRadiusMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeFixedSizeScaleMenu NativeDirectionRankDichotomy NativeIncidentRankSelection
open NativeRankRadiusMenu

/-- This is a subset of the parent maps already installed on the reference. -/
def menu (w : ℝ) (hw : 0 ≤ w) (g level : ℕ) : Finset (Fin (g+1)) :=
  univ.filter (fun j => (windowSchedule w hw g level j).val ≤ level/4)

def allowed (delta w : ℝ) (hw : 0 ≤ w) (g level : ℕ) (a : ℝ) : Finset (Fin (g+1)) :=
  (menu w hw g level).filter (fun j => radius w hw g level j ≤ delta^a)

lemma allowed_antitone {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1)
    (w : ℝ) (hw : 0 ≤ w) (g level : ℕ) {a b : ℝ} (hab : a ≤ b) :
    allowed delta w hw g level b ⊆ allowed delta w hw g level a := by
  intro j hj
  exact mem_filter.mpr ⟨(mem_filter.mp hj).1,(mem_filter.mp hj).2.trans
    (Real.rpow_le_rpow_of_exponent_ge hd0 hd1 hab)⟩

/-- A preceding installed entry lies between one eighth and one quarter
of the original depth. No new parent map is introduced after selection. -/
theorem exists_middle_entry (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/8)
    (g level : ℕ) (hg : 0 < g) (hgrid : 1/(g:ℝ) < w/4)
    (hlarge : 4 ≤ w*(level:ℝ)) :
    ∃j : Fin (g+1),j∈menu w hw.le g level ∧
      (level:ℝ)/8 ≤ (windowSchedule w hw.le g level j).val := by
  have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
  have hwL := mul_le_mul_of_nonneg_right hwsmall.le hln
  have hdivhi : ((level/4:ℕ):ℝ)*4 ≤ level := by
    exact_mod_cast Nat.div_mul_le_self level 4
  have hdivlo : (level:ℝ) < 4*(((level/4:ℕ):ℝ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ level (by norm_num : 0 < (4:ℕ))
  have hlo : w*(level:ℝ) ≤ (level/4:ℕ) := by nlinarith
  have hhi : ((level/4:ℕ):ℝ) ≤ (1-w)*(level:ℝ) := by nlinarith
  obtain ⟨j,hjm,_hgap,hgapR⟩ := exists_window_predecessor w hw (by linarith)
    g level (level/4) hg hgrid hlarge hlo hhi
  have hgridL := mul_le_mul_of_nonneg_right hgrid.le hln
  have hlg : (level:ℝ)/g ≤ (w/4)*(level:ℝ) := by
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hgridL
  rw [Nat.cast_sub hjm] at hgapR
  exact ⟨j,mem_filter.mpr ⟨mem_univ _,hjm⟩,by nlinarith⟩

lemma radius_le_cutoff_of_eighth_depth {delta : ℝ} (w : ℝ) (hw : 0 ≤ w)
    (g level : ℕ) (hdy : delta=(2:ℝ)⁻¹^level) (j : Fin (g+1))
    (hj : (level:ℝ)/8 ≤ (windowSchedule w hw g level j).val)
    (a : ℝ) (ha : a ≤ 1/8) : radius w hw g level j ≤ delta^a := by
  have hd0 : 0 < delta := by rw [hdy]; positivity
  have hd1 : delta ≤ 1 := by
    rw [hdy]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hd : delta=(2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,inv_pow]
  have he : 1/((2^(windowSchedule w hw g level j).val:ℕ):ℝ) =
      (2:ℝ)^(-((windowSchedule w hw g level j).val:ℝ)) := by
    simp only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
      Nat.cast_pow,Nat.cast_ofNat,one_div]
  have hp : 1/((2^(windowSchedule w hw g level j).val:ℕ):ℝ) ≤ delta^(1/8:ℝ) := by
    rw [he,hd,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    linarith
  apply le_trans ?_ (hp.trans (Real.rpow_le_rpow_of_exponent_ge hd0 hd1 ha))
  unfold radius
  apply one_div_le_one_div_of_le (by positivity)
  have hN : (0:ℝ) ≤ ((2^(windowSchedule w hw g level j).val:ℕ):ℝ) := by positivity
  nlinarith

lemma allowed_nonempty {delta : ℝ} (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/8)
    (g level : ℕ) (hg : 0 < g) (hgrid : 1/(g:ℝ) < w/4)
    (hlarge : 4 ≤ w*(level:ℝ)) (hdy : delta=(2:ℝ)⁻¹^level)
    (a : ℝ) (ha : a ≤ 1/8) : (allowed delta w hw.le g level a).Nonempty := by
  obtain ⟨j,hj,hdepth⟩ := exists_middle_entry w hw hwsmall g level hg hgrid hlarge
  exact ⟨j,mem_filter.mpr ⟨hj,radius_le_cutoff_of_eighth_depth w hw.le g level hdy j hdepth a ha⟩⟩

lemma radius_ge_quarter_power {delta : ℝ} (w : ℝ) (hw : 0 ≤ w)
    (g level : ℕ) (hdy : delta=(2:ℝ)⁻¹^level) (j : Fin (g+1))
    (hj : j∈menu w hw g level) : delta^(1/4:ℝ)/48 ≤ radius w hw g level j := by
  have hm : (windowSchedule w hw g level j).val*4 ≤ level :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < (4:ℕ))).mp (mem_filter.mp hj).2
  have hmR : ((windowSchedule w hw g level j).val:ℝ)*4 ≤ level := by exact_mod_cast hm
  have hd : delta=(2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,inv_pow]
  have he : 1/((2^(windowSchedule w hw g level j).val:ℕ):ℝ) =
      (2:ℝ)^(-((windowSchedule w hw g level j).val:ℝ)) := by
    simp only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
      Nat.cast_pow,Nat.cast_ofNat,one_div]
  have hp : delta^(1/4:ℝ) ≤ 1/((2^(windowSchedule w hw g level j).val:ℕ):ℝ) := by
    rw [he,hd,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    linarith
  calc
    _ ≤ (1/((2^(windowSchedule w hw g level j).val:ℕ):ℝ))/48 :=
      div_le_div_of_nonneg_right hp (by norm_num)
    _ = _ := by unfold radius; rw [div_div]; congr 1; ring

/-- The squared stopping radius remains inside the proved point-scale range. -/
theorem radius_square_ge_source {delta : ℝ} (w : ℝ) (hw : 0 ≤ w)
    (g level : ℕ) (hdy : delta=(2:ℝ)⁻¹^level)
    (hcut : delta^(1/2:ℝ) ≤ 1/147456) (j : Fin (g+1))
    (hj : j∈menu w hw g level) : 64*delta ≤ (radius w hw g level j)^2 := by
  have hd0 : 0 < delta := by rw [hdy]; positivity
  have hr := radius_ge_quarter_power w hw g level hdy j hj
  have hsq : (delta^(1/4:ℝ))^2=delta^(1/2:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hd0.le]
    norm_num
  have hhalf : (delta^(1/2:ℝ))^2=delta := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hd0.le]
    norm_num
  have hlow : delta^(1/2:ℝ)/2304 ≤ (radius w hw g level j)^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ delta^(1/4:ℝ)/48) hr 2
    simpa only [div_pow,hsq,show (48:ℝ)^2=2304 by norm_num] using hh
  have hmul := mul_le_mul_of_nonneg_left hcut
    (Real.rpow_nonneg hd0.le (1/2:ℝ))
  nlinarith

/-- The literal rank producer is applied only to the preinstalled mesoscopic
entries, so the resulting stopping radius and its square are both admissible. -/
theorem exists_mesoscopic_rank_retention {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (hEn : E.Nonempty)
    (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/8) (g level : ℕ) (hg : 0 < g)
    (hgrid : 1/(g:ℝ) < w/4) (hlarge : 4 ≤ w*(level:ℝ))
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hcut : D.thickness^(w/2) ≤ 1/48)
    (hsquare : D.thickness^(1/2:ℝ) ≤ 1/147456)
    (a eta : Fin 4 → ℝ) (ha : ∀ell,0 < a ell ∧ a ell ≤ 1/8)
    (heta : ∀ell,0 < eta ell) :
    ∃ell : Fin 4,∃j : Fin (g+1),j∈menu w hw.le g level ∧
      radius w hw.le g level j ≤ D.thickness^(a ell) ∧
      D.thickness ≤ radius w hw.le g level j ∧ radius w hw.le g level j ≤ 1/4 ∧
      48*((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ)*radius w hw.le g level j=1 ∧
      ((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ)*D.thickness ≤ 1 ∧
      64*D.thickness ≤ (radius w hw.le g level j)^2 ∧
      ∃F⊆E,F.Nonempty ∧
        ((radius w hw.le g level j)^(eta ell)/(4*((g:ℝ)+1)))*(E.card:ℝ) ≤ (F.card:ℝ) ∧
        ∃P : Index → Submodule ℝ E4,
          (∀z∈F,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ radius w hw.le g level j) ∧
          ∀k∈F.image Prod.snd,
            Module.finrank ℝ (P k) ≤ ell.val+1 ∧
            pointSet F k=pointNear D E k (radius w hw.le g level j) (P k) ∧
            (radius w hw.le g level j)^(eta ell)*((pointSet E k).card:ℝ) ≤ (pointSet F k).card ∧
            ∀ell' : Fin 4,ell' < ell → ∀j'∈menu w hw.le g level,
              radius w hw.le g level j' ≤ D.thickness^(a ell') →
              ∀Q : Submodule ℝ E4,Module.finrank ℝ Q ≤ ell'.val+1 →
                ((pointNear D E k (radius w hw.le g level j') Q).card:ℝ) <
                  (radius w hw.le g level j')^(eta ell')*((pointSet E k).card:ℝ) := by
  obtain ⟨ell,j,hj,F,hFE,hFn,hret,P,hnear,hpoints⟩ :=
    exists_rank_scale_retention D E hEn (univ:Finset (Fin (g+1)))
      (radius w hw.le g level) eta (fun ell => allowed D.thickness w hw.le g level (a ell))
      (fun _ _ _ => mem_univ _) heta
      (fun j _hj => ⟨radius_pos w hw.le g level j,
        (radius_le_one_div_48 w hw.le g level j).trans (by norm_num)⟩)
      (allowed_nonempty w hw hwsmall g level hg hgrid hlarge hdy (a 3) (ha 3).2)
  obtain ⟨hjmenu,hjcut⟩ := mem_filter.mp hj
  obtain ⟨hrlo,hrhi,hidentity,hscale⟩ :=
    radius_geometry w hw (by linarith) g level hlarge hdy hcut j
  refine ⟨ell,j,hjmenu,hjcut,hrlo,hrhi,hidentity,hscale,
    radius_square_ge_source w hw.le g level hdy hsquare j hjmenu,F,hFE,hFn,?_,P,hnear,?_⟩
  · simpa only [card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hret
  · intro k hk
    obtain ⟨hdim,hfiber,hmass,hearlier⟩ := hpoints k hk
    refine ⟨hdim,hfiber,hmass,?_⟩
    intro ell' hell' j' hj' hcut' Q hQ
    exact hearlier ell' hell' j' (mem_filter.mpr ⟨hj',hcut'⟩) Q hQ

end NativeRankMesoscopicRadiusMenu
