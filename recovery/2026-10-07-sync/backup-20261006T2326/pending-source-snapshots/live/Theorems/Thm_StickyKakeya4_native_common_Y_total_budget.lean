import Theorems.Thm_StickyKakeya4_native_actual_common_Y_graph_mass
import Theorems.Thm_StickyKakeya4_native_output_alignment_menu_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeCommonYTotalBudget
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeQuarterScaleParameters NativeWholeYGraphRetention NativeLiteralYHeightAlignment
open NativeOutputAlignmentMenuBudget

lemma fine_mesh_eq (u : ℕ) :
    64/((2^(u+12):ℕ):ℝ)=(2:ℝ)⁻¹^(u+6) := by
  push_cast
  simp only [pow_add,inv_pow]
  norm_num
  field_simp

lemma input_mesh_eq (u : ℕ) :
    (2:ℝ)⁻¹^u/512=(64/((2^(u+12):ℕ):ℝ))/8 := by
  rw [fine_mesh_eq,pow_add]
  norm_num
  ring

/-- The initial physical scale guard suffices; no stronger depth window
is introduced. The same reference has r=deltaOriginal/rho(m). -/
theorem source_thickness_sq_le_original {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
    (hscale : D.thickness ≤ (rho m)^2) :
    (source h R Eref a m p).thickness^2 ≤ D.thickness := by
  have hrho:=rho_pos m
  have hd:=h.1.2.1
  have hid : (source h R Eref a m p).thickness*rho m=D.thickness := by
    rw [source_thickness]
    unfold rho
    field_simp
    ring
  apply (mul_le_mul_iff_right₀ (show 0 < (rho m)^2 by positivity)).mp
  have hh:=mul_le_mul_of_nonneg_left hscale hd.le
  have he : (source h R Eref a m p).thickness^2*(rho m)^2=D.thickness^2 := by
    rw [←mul_pow,hid]
  rw [he]
  nlinarith only [hh]

/-- The actual natural third factor is at least one. This step explicitly
pays the Q^4 appearing in the new graph-retention inequality. -/
lemma radix_cost_from_raw {delta r c3 : ℝ} (F3 Q3 : ℕ)
    (hF3 : 1 ≤ F3) (hr : 0 < r) (hc3 : 0 ≤ c3)
    (hscale : r^2 ≤ delta)
    (H3 : (F3:ℝ)*(Q3:ℝ)^4 ≤ delta^(-c3)) :
    (Q3:ℝ)^4 ≤ r^(-(2*c3)) := by
  have hF : (1:ℝ) ≤ F3 := by exact_mod_cast hF3
  have hQ : (Q3:ℝ)^4 ≤ delta^(-c3) :=
    (le_mul_of_one_le_left (by positivity) hF).trans H3
  have hh:=Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ)<r^2) hscale (neg_nonpos.mpr hc3)
  have he : (r^2)^(-c3)=r^(-(2*c3)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  exact hQ.trans (hh.trans_eq he)

/-- The literal planar gap gives sigma<=32768*(eps/8)^chi. The fixed
32768 is paid after chi and the baseline window are chosen. -/
lemma local_sigma_from_gap {r eps rho tau chi window : ℝ}
    (hr : 0 < r) (heps : 0 < eps) (_hrho : 0 < rho) (_htau : 0 < tau)
    (hchi : 0 < chi)
    (hgap : (eps/8)^(-chi) ≤ tau/rho) (hepsUpper : eps ≤ r^window)
    (hfixed : 32768*r^(window*chi/2) ≤ 1) :
    32768*rho/tau ≤ r^(window*chi/2) := by
  have hh:=one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity : (0:ℝ)<eps/8) _) hgap
  have hratio : rho/tau ≤ (eps/8)^chi := by
    simpa only [one_div_div,Real.rpow_neg (by positivity : (0:ℝ)≤eps/8),one_div,inv_inv] using hh
  have hdiv : eps/8 ≤ eps := by linarith only [heps]
  have hpow := (Real.rpow_le_rpow (by positivity : (0:ℝ)≤eps/8) hdiv hchi.le).trans
    (Real.rpow_le_rpow heps.le hepsUpper hchi.le)
  have hdouble : (r^window)^chi = r^(window*chi/2)*r^(window*chi/2) := by
    rw [←Real.rpow_mul hr.le,←Real.rpow_add hr]
    congr 1
    ring
  calc
    32768*rho/tau = 32768*(rho/tau) := by ring
    _ ≤ 32768*((r^window)^chi) := mul_le_mul_of_nonneg_left (hratio.trans hpow) (by norm_num)
    _ = (32768*r^(window*chi/2))*r^(window*chi/2) := by rw [hdouble]; ring
    _ ≤ 1*r^(window*chi/2) := mul_le_mul_of_nonneg_right hfixed (Real.rpow_nonneg hr.le _)
    _ = _ := one_mul _

/-- Genuine pre-source cutoffs pay the actual common menu, the32768 gap
constant, and the fixed graph/Y conversion constant. Both actual fine-scale
guards r<=eps and eps<=r^window remain explicit. -/
theorem exists_total_cutoff (E zeta53 chi window menuTax : ℝ)
    (hE : 0 < E) (hchi : 0 < chi) (hwindow : 0 < window)
    (hmenuTax : 0 < menuTax) (bins : ℕ) :
    ∃r0 : ℝ,0 < r0 ∧ r0 ≤ 1 ∧
      ∀r : ℝ,0 < r → r ≤ r0 →
      32768*r^(window*chi/2) ≤ 1 ∧
      ((5:ℝ)^4*(32768:ℝ)^zeta53/16)*r^((window*chi/2)*(E/8192)) ≤ 1 ∧
      ∀u : ℕ,r ≤ (2:ℝ)⁻¹^(u+6) → (2:ℝ)⁻¹^(u+6) ≤ r^window →
        2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ) ≤ r^(-menuTax) := by
  let a:ℝ:=window*chi/2
  let B:ℝ:=(5:ℝ)^4*(32768:ℝ)^zeta53/16
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨dm,hdm,_hdm1,Hmenu⟩:=exists_menu_cutoff menuTax hmenuTax bins
  obtain ⟨dw,hdw,hdw1,Hwindow⟩:=exists_small_power_cutoff hwindow hdm
  obtain ⟨dg,hdg,_hdg1,Hgap⟩:=exists_small_power_cutoff ha (by norm_num : (0:ℝ)<1/32768)
  obtain ⟨dc,hdc,_hdc1,Hconstant⟩:=exists_small_power_cutoff
    (show 0 < a*(E/8192) by positivity) (div_pos (by norm_num : (0:ℝ)<1) hB)
  refine ⟨min dw (min dg dc),lt_min hdw (lt_min hdg hdc),(min_le_left _ _).trans hdw1,?_⟩
  intro r hr hsmall
  have hg:=Hgap r hr (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc:=Hconstant r hr (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨by linarith only [hg],?_,?_⟩
  · have hh:=(le_div_iff₀ hB).mp hc
    simpa only [mul_comm] using hh
  · intro u hLower hUpper
    have hsmallEps:=hUpper.trans (Hwindow r hr (hsmall.trans (min_le_left _ _)))
    have hm:=Hmenu u hsmallEps
    exact hm.trans (Real.rpow_le_rpow_of_nonpos hr hLower (neg_nonpos.mpr hmenuTax.le))

/-- The actual source graph lower and its raw costs supply htotal. The
only lower input is the conclusion of exists_actual_common_mass, before
any small-power payment; the desired htotal is not a premise. -/
theorem pay_actual_graph_mass {r eps sigma E zeta53 eB c3 menuTax aGap N total : ℝ}
    (Q3 : ℕ) (hr : 0 < r) (hr1 : r ≤ 1) (hrEps : r ≤ eps)
    (hs : 0 < sigma) (hE : 0 < E)
    (hzetaSmall : zeta53 ≤ E/16384) (heB : 0 ≤ eB) (ha : 0 < aGap)
    (htax : 5*eB/16+2*c3+menuTax ≤ aGap*(E/16384))
    (hMenu : N ≤ r^(-menuTax))
    (hQ : (Q3:ℝ)^4 ≤ r^(-(2*c3))) (hSigma : sigma ≤ r^aGap)
    (hfixed : ((5:ℝ)^4*(32768:ℝ)^zeta53/16)*r^(aGap*(E/8192)) ≤ 1)
    (htotal : 0 ≤ total)
    (Hsource : (16/(5:ℝ)^4)*(sigma/32768)^zeta53*eps^(5*eB/16) ≤
      N*(Q3:ℝ)^4*eps^4*total) :
    sigma^(E/4096) ≤ eps^4*total := by
  let tax:ℝ:=5*eB/16+2*c3+menuTax
  let B:ℝ:=(5:ℝ)^4*(32768:ℝ)^zeta53/16
  have hB : 0 < B := by dsimp [B]; positivity
  have hs1 : sigma ≤ 1 := hSigma.trans (by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hr hr1 ha.le)
  have hFixedSigma : B*sigma^(E/8192) ≤ 1 := by
    have hh:=Real.rpow_le_rpow hs.le hSigma (by positivity : 0 ≤ E/8192)
    rw [←Real.rpow_mul hr.le] at hh
    exact (mul_le_mul_of_nonneg_left hh hB.le).trans hfixed
  have hCost : N*(Q3:ℝ)^4 ≤ r^(-(2*c3+menuTax)) := by
    have hh:=mul_le_mul hMenu hQ (by positivity) (by positivity)
    apply hh.trans_eq
    rw [←Real.rpow_add hr]
    congr 1
    ring
  have hBase : (16/(5:ℝ)^4)*(sigma/32768)^zeta53*r^(5*eB/16) ≤
      r^(-(2*c3+menuTax))*(eps^4*total) := by
    calc
      _ ≤ (16/(5:ℝ)^4)*(sigma/32768)^zeta53*eps^(5*eB/16) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hrEps (by positivity)) (by positivity)
      _ ≤ N*(Q3:ℝ)^4*eps^4*total := Hsource
      _ = (N*(Q3:ℝ)^4)*(eps^4*total) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCost (by positivity)
  have hpaid : sigma^zeta53*r^tax ≤ B*(eps^4*total) := by
    have hh:=mul_le_mul_of_nonneg_left hBase
      (show 0 ≤ B*r^(2*c3+menuTax) by positivity)
    have hl : (B*r^(2*c3+menuTax))*
        ((16/(5:ℝ)^4)*(sigma/32768)^zeta53*r^(5*eB/16))=sigma^zeta53*r^tax := by
      rw [Real.div_rpow hs.le (by norm_num)]
      have hp : r^(2*c3+menuTax)*r^(5*eB/16)=r^tax := by
        rw [←Real.rpow_add hr]
        congr 1
        dsimp [tax]
        ring
      calc
        _ = sigma^zeta53*(r^(2*c3+menuTax)*r^(5*eB/16)) := by
          dsimp [B]
          field_simp [(Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<32768) zeta53).ne']
          ring
        _ = _ := by rw [hp]
    have hrhs : (B*r^(2*c3+menuTax))*(r^(-(2*c3+menuTax))*(eps^4*total))=B*(eps^4*total) := by
      rw [Real.rpow_neg hr.le]
      field_simp [(Real.rpow_pos_of_pos hr (2*c3+menuTax)).ne']
    rwa [hl,hrhs] at hh
  have hSmallTax : sigma^(E/16384) ≤ r^tax := by
    have hh:=Real.rpow_le_rpow hs.le hSigma (by positivity : 0 ≤ E/16384)
    rw [←Real.rpow_mul hr.le] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_ge hr hr1 htax)
  have hZ : sigma^(E/16384) ≤ sigma^zeta53 :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 hzetaSmall
  have hLow : sigma^(E/8192) ≤ B*(eps^4*total) := by
    have hh:=mul_le_mul hZ hSmallTax (by positivity) (by positivity)
    have he : sigma^(E/16384)*sigma^(E/16384)=sigma^(E/8192) := by
      rw [←Real.rpow_add hs]
      congr 1
      ring
    rw [he] at hh
    exact hh.trans hpaid
  have hSquare : sigma^(E/4096)=sigma^(E/8192)*sigma^(E/8192) := by
    rw [←Real.rpow_add hs]
    congr 1
    ring
  rw [hSquare]
  calc
    _ ≤ (B*(eps^4*total))*sigma^(E/8192) := mul_le_mul_of_nonneg_right hLow (by positivity)
    _ = (B*sigma^(E/8192))*(eps^4*total) := by ring
    _ ≤ 1*(eps^4*total) := mul_le_mul_of_nonneg_right hFixedSigma (by positivity)
    _ = _ := one_mul _

end NativeCommonYTotalBudget
