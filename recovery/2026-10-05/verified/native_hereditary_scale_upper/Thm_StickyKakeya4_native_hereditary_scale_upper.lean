import Theorems.Thm_StickyKakeya4_native_hereditary_conditional_upper
import Theorems.Thm_StickyKakeya4_native_two_scale_boundary_window

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeHereditaryScaleUpper
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeConditionedPairMenu
open NativeIncidenceMultiplicityTower NativeTwoAxisPowerInterpolation NativeFixedSizeScaleMenu
open NativeHereditaryConditionalUpper NativeConditionalParentBoundary NativeTwoScaleBoundaryWindow

/-- Upper interpolation throughout the middle window for any literal F⊆E.
The scheduled upper and both conditioned uniformities belong only to E.
No lower bound or nonemptiness is needed on F. -/
theorem middle_pair_upper {n : ℕ} {D : FiniteScaleSource n} {eta a kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E F : Finset (Fin n × Index)) (hFE : F ⊆ E)
    (hE : E ⊆ NativeCubicalIncidenceCounts.incidences original) (hER : ∀z∈E,z.1∈R)
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2) (g rad : ℕ)
    (hg : 0 < g) (hgl : g ≤ level) (hgrid : 1/(g:ℝ) < w/4)
    (hlarge : 4 ≤ w*(level:ℝ)) (hk : 0 ≤ kappa) (hk3 : kappa ≤ 3)
    (loss target : ℝ) (hcostQ : (729:ℝ)*(rad:ℝ)^4 ≤ D.thickness^(-loss))
    (hdiag : 12*w ≤ target) (hmargin : 2*loss+16*(2/(g:ℝ)) ≤ target)
    (HU : ∀i j : Fin (g+1),
      HasUniformFibers E rad (conditionedGlobalPair h R a level
        (windowSchedule w hw.le g level i).val (windowSchedule w hw.le g level j).val) ∧
      HasUniformFibers E rad (conditionedGlobalPoint h R a level
        (windowSchedule w hw.le g level i).val (windowSchedule w hw.le g level j).val))
    (HM : ∀i j : Fin (g+1),
      (windowSchedule w hw.le g level i).val ≤ (windowSchedule w hw.le g level j).val →
      ∀q,(parentEdges D a (2^(windowSchedule w hw.le g level i).val) E q).Nonempty →
        multiplicity ((parentEdges D a (2^(windowSchedule w hw.le g level i).val) E q).image
          (physicalPair h R a level (windowSchedule w hw.le g level j).val)) ≤
        D.thickness^(-loss)*depthPower kappa (windowSchedule w hw.le g level i).val
          (windowSchedule w hw.le g level j).val)
    (m f : ℕ) (hmf : m ≤ f) (hmlo : w*(level:ℝ) ≤ m)
    (hfhi : (f:ℝ) ≤ (1-w)*(level:ℝ)) (p : Parent) :
    multiplicity ((parentEdges D a (2^m) F p).image (physicalPair h R a level f)) ≤
      D.thickness^(-target)*depthPower kappa m f := by
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
  have hmfR : (m:ℝ) ≤ f := by exact_mod_cast hmf
  have hmhi : (m:ℝ) ≤ (1-w)*(level:ℝ) := hmfR.trans hfhi
  have hflo : w*(level:ℝ) ≤ f := hmlo.trans hmfR
  have hfl : f ≤ level := by
    have hh : (f:ℝ) ≤ level := by nlinarith
    exact_mod_cast hh
  have hP := (depthPower_pos kappa m f).le
  by_cases hNear : ((f-m:ℕ):ℝ) ≤ (2*w)*(level:ℝ)
  · have hh := short_gap_upper h R F a level m f hmf hdy hk hNear p
    exact hh.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith : -target ≤ -6*(2*w))) hP)
  · obtain ⟨jc,hcm,_hcGap,hcGapR⟩ :=
      exists_window_predecessor w hw hwsmall g level m hg hgrid hlarge hmlo hmhi
    obtain ⟨jb,hbf,_hbGap,hbGapR⟩ :=
      exists_window_predecessor w hw hwsmall g level f hg hgrid hlarge hflo hfhi
    let c := (windowSchedule w hw.le g level jc).val
    let b := (windowSchedule w hw.le g level jb).val
    let s := 2/(g:ℝ)
    have hs : 0 ≤ s := by dsimp [s]; positivity
    have hsSmall : s ≤ w/2 := by
      dsimp [s]
      rw [show 2/(g:ℝ)=2*(1/(g:ℝ)) by ring]
      linarith
    have hGapC : ((m-c:ℕ):ℝ) ≤ s*level := gap_le_twice_fraction g level m c hg hgl hcGapR
    have hGapF : ((f-b:ℕ):ℝ) ≤ s*level := gap_le_twice_fraction g level f b hg hgl hbGapR
    have hFar : 2*w*(level:ℝ) < (f:ℝ)-(m:ℝ) := by
      rw [Nat.cast_sub hmf] at hNear
      exact lt_of_not_ge hNear
    have hGapFR : (f:ℝ)-(b:ℝ) ≤ s*level := by
      calc
        _ = ((f-b:ℕ):ℝ) := (Nat.cast_sub hbf).symm
        _ ≤ _ := hGapF
    have hSmallLevel : s*(level:ℝ) ≤ (w/2)*(level:ℝ) := mul_le_mul_of_nonneg_right hsSmall hln
    have hmb : m ≤ b := by
      have hh : (m:ℝ) ≤ b := by nlinarith
      exact_mod_cast hh
    obtain ⟨hG,hX⟩ := HU jc jb
    have hh := far_pair_upper h original horiginal ha R E F hFE hE hER level c m b f hdy
      hcm hbf hfl hGapC hGapF hk rad hG hX hcostQ (HM jc jb (hcm.trans hmb)) p
    have hmarginUpper : 2*loss+s*(10+kappa) ≤ target := by
      change 2*loss+16*s ≤ target at hmargin
      nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hmarginUpper)) hP)

/-- The boundary geometry pays its own smaller constant exponent. This
avoids charging the entire reference upper loss a second time. -/
theorem boundary_pair_upper_separate_cost {n : ℕ} {D : FiniteScaleSource n}
    {eta a loss cost s kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (F : Finset (Fin n × Index))
    (hF : F ⊆ NativeCubicalIncidenceCounts.incidences original) (hFR : ∀z∈F,z.1∈R)
    (level m d b f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hmd : m ≤ d) (hdb : d ≤ b) (hbf : b ≤ f) (hfl : f ≤ level)
    (hgapD : ((d-m:ℕ):ℝ) ≤ s*level) (hgapF : ((f-b:ℕ):ℝ) ≤ s*level)
    (hk : 0 ≤ kappa) (hconstant : (729:ℝ) ≤ D.thickness^(-cost))
    (HM : ∀q,multiplicity ((parentEdges D a (2^d) F q).image (physicalPair h R a level b)) ≤
      D.thickness^(-loss)*depthPower kappa d b) (p : Parent) :
    multiplicity ((parentEdges D a (2^m) F p).image (physicalPair h R a level f)) ≤
      D.thickness^(-(loss+cost+16*s))*depthPower kappa m f := by
  have hd := h.1.2.1
  let rD := ((2^(d-m):ℕ):ℝ)
  let rF := ((2^(f-b):ℕ):ℝ)
  have hrD : 0 ≤ rD := by dsimp [rD]; positivity
  have hrF : 0 ≤ rF := by dsimp [rF]; positivity
  have hratioD : rD ≤ D.thickness^(-s) := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgapD
  have hratioF : rF ≤ D.thickness^(-s) := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgapF
  have hpowD := nat_power_cost hd hrD hratioD 6
  have hpowF := nat_power_cost hd hrF hratioF 10
  have hPower := depthPower_mono hk hmd hbf
  let Fp := parentEdges D a (2^m) F p
  have hFp : Fp ⊆ NativeCubicalIncidenceCounts.incidences original := (filter_subset _ _).trans hF
  have hFpR : ∀z∈Fp,z.1∈R := fun z hz => hFR z (mem_filter.mp hz).1
  have hP := (depthPower_pos kappa m f).le
  have hUpper := coarser_outer_parent_upper h R F a level m d b hmd hdb
    (D.thickness^(-loss)*depthPower kappa d b)
    (mul_nonneg (Real.rpow_pos_of_pos hd _).le (depthPower_pos _ _ _).le) (fun q _hq => HM q) p
  have hReverse := NativeCoarseScaleReverse.actual_multiplicity_le h original horiginal ha
    R Fp hFp hFpR level b f hdy hbf hfl
  have hCost : (729:ℝ)*rF^10*rD^6 ≤ D.thickness^(-(cost+16*s)) := by
    calc
      _ ≤ (D.thickness^(-cost)*D.thickness^(-s*(10:ℝ)))*D.thickness^(-s*(6:ℝ)) :=
        mul_le_mul (mul_le_mul hconstant hpowF (pow_nonneg hrF 10)
          (Real.rpow_pos_of_pos hd _).le) hpowD (pow_nonneg hrD 6) (by positivity)
      _ = _ := by rw [←Real.rpow_add hd,←Real.rpow_add hd]; congr 1; ring
  calc
    _ ≤ 729*rF^10*multiplicity (Fp.image (physicalPair h R a level b)) := hReverse
    _ ≤ 729*rF^10*(rD^6*(D.thickness^(-loss)*depthPower kappa d b)) :=
      mul_le_mul_of_nonneg_left hUpper (by positivity)
    _ ≤ 729*rF^10*(rD^6*(D.thickness^(-loss)*depthPower kappa m f)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPower (by positivity))
          (pow_nonneg hrD 6)) (by positivity)
    _ = (729*rF^10*rD^6)*(D.thickness^(-loss)*depthPower kappa m f) := by ring
    _ ≤ D.thickness^(-(cost+16*s))*(D.thickness^(-loss)*depthPower kappa m f) :=
      mul_le_mul_of_nonneg_right hCost (mul_nonneg (Real.rpow_pos_of_pos hd _).le hP)
    _ = _ := by rw [←mul_assoc,←Real.rpow_add hd]; congr 2; ring

/-- All boundary depths inherit any already established hereditary middle
upper. Only actual physical maps of F and literal parent partitions occur. -/
theorem all_pair_upper {n : ℕ} {D : FiniteScaleSource n} {eta a kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (F : Finset (Fin n × Index))
    (hF : F ⊆ NativeCubicalIncidenceCounts.incidences original) (hFR : ∀z∈F,z.1∈R)
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hk : 0 ≤ kappa)
    (w loss cost target : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1/8) (hlarge : 4 ≤ w*(level:ℝ))
    (hconstant : (729:ℝ) ≤ D.thickness^(-cost)) (hdiag : 48*w ≤ target)
    (hmargin : loss+cost+32*w ≤ target)
    (HM : ∀d b : ℕ,d ≤ b → w*(level:ℝ) ≤ d → (b:ℝ) ≤ (1-w)*(level:ℝ) →
      ∀p,multiplicity ((parentEdges D a (2^d) F p).image (physicalPair h R a level b)) ≤
        D.thickness^(-loss)*depthPower kappa d b)
    (m f : ℕ) (hmf : m ≤ f) (hfl : f ≤ level) (p : Parent) :
    multiplicity ((parentEdges D a (2^m) F p).image (physicalPair h R a level f)) ≤
      D.thickness^(-target)*depthPower kappa m f := by
  have hP := (depthPower_pos kappa m f).le
  by_cases hNear : ((f-m:ℕ):ℝ) ≤ 8*w*(level:ℝ)
  · have hh := short_gap_upper h R F a level m f hmf hdy hk hNear p
    exact hh.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1
        (by linarith : -target ≤ -6*(8*w))) hP)
  · obtain ⟨d,b,hmd,hdb,hbf,hdlo,hbhi,hgapD,hgapF⟩ :=
      exists_clamped_depths w hw hwsmall level m f hlarge hmf hfl (lt_of_not_ge hNear)
    have hh := boundary_pair_upper_separate_cost h original horiginal ha R F hF hFR level m d b f hdy
      hmd hdb hbf hfl hgapD hgapF hk hconstant (HM d b hdb hdlo hbhi) p
    have he : loss+cost+16*(2*w) ≤ target := by linarith
    exact hh.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1 (neg_le_neg he)) hP)

/-- The two geometric budgets needed below follow from the reference
source's existing retention/radix cost, with no extra source cutoff. -/
theorem reference_cost_budgets {delta eta gamma t : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta) (ht : 0 ≤ t)
    (F Q : ℕ) (hF : 0 < F) (hQ : 1 ≤ Q) (hbudget : 2*gamma ≤ t/4)
    (hcost : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤ delta^(-gamma)) :
    (729:ℝ)*(Q:ℝ)^4 ≤ delta^(-t) ∧ (729:ℝ) ≤ delta^(-(t/4)) := by
  have hfour := (NativePairScaleBudget.radix_four_cost hd hd1 heta F Q hF hcost).1
  have hsmall : (41472:ℝ)*(Q:ℝ)^4 ≤ delta^(-(t/4)) :=
    hfour.trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hbudget))
  have hQr : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hQpow : (1:ℝ) ≤ (Q:ℝ)^4 := one_le_pow₀ hQr
  constructor
  · exact ((mul_le_mul_of_nonneg_right (by norm_num : (729:ℝ) ≤ 41472)
      (pow_nonneg (Nat.cast_nonneg Q) 4)).trans hsmall).trans
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith))
  · exact (show (729:ℝ) ≤ 41472*(Q:ℝ)^4 by nlinarith).trans hsmall

/-- A single reference menu with upper loss t gives EVERY literal subset a
physical conditional upper with loss 3t at EVERY original dyadic pair.
This uses the public reference upper t, not a hidden stronger menu bound.
The original R and its full physical representative map remain unchanged. -/
theorem hereditary_three_loss {n : ℕ} {D : FiniteScaleSource n} {eta a kappa t w : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index))
    (hE : E ⊆ NativeCubicalIncidenceCounts.incidences original) (hER : ∀z∈E,z.1∈R)
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hk : 0 ≤ kappa) (hk3 : kappa ≤ 3)
    (_ht : 0 < t) (hw : 0 < w) (hwsmall : w ≤ 1/8) (hwloss : w ≤ t/16000)
    (g rad : ℕ) (hg : 0 < g) (hgl : g ≤ level) (hgrid : 1/(g:ℝ) < w/4)
    (hlarge : 4 ≤ w*(level:ℝ))
    (hcostQ : (729:ℝ)*(rad:ℝ)^4 ≤ D.thickness^(-t))
    (hconstant : (729:ℝ) ≤ D.thickness^(-(t/4)))
    (HU : ∀i j : Fin (g+1),
      HasUniformFibers E rad (conditionedGlobalPair h R a level
        (windowSchedule w hw.le g level i).val (windowSchedule w hw.le g level j).val) ∧
      HasUniformFibers E rad (conditionedGlobalPoint h R a level
        (windowSchedule w hw.le g level i).val (windowSchedule w hw.le g level j).val))
    (HM : ∀i j : Fin (g+1),
      (windowSchedule w hw.le g level i).val ≤ (windowSchedule w hw.le g level j).val →
      ∀q,(parentEdges D a (2^(windowSchedule w hw.le g level i).val) E q).Nonempty →
        multiplicity ((parentEdges D a (2^(windowSchedule w hw.le g level i).val) E q).image
          (physicalPair h R a level (windowSchedule w hw.le g level j).val)) ≤
        D.thickness^(-t)*depthPower kappa (windowSchedule w hw.le g level i).val
          (windowSchedule w hw.le g level j).val) :
    ∀F ⊆ E,∀m f : ℕ,m ≤ f → f ≤ level → ∀p : Parent,
      (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) F p))).toReal ≤
        D.thickness^(-(3*t))*
          ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-kappa) := by
  have hsmall : w < 1/2 := hwsmall.trans_lt (by norm_num)
  have hs : 2/(g:ℝ) ≤ w/2 := by
    rw [show 2/(g:ℝ)=2*(1/(g:ℝ)) by ring]
    linarith
  have hdiagMid : 12*w ≤ 9*t/4 := by linarith
  have hmarginMid : 2*t+16*(2/(g:ℝ)) ≤ 9*t/4 := by linarith
  have hdiagAll : 48*w ≤ 3*t := by linarith
  have hmarginAll : 9*t/4+t/4+32*w ≤ 3*t := by linarith
  intro F hFE m f hmf hfl p
  have hF := hFE.trans hE
  have hFR : ∀z∈F,z.1∈R := fun z hz => hER z (hFE hz)
  have hMid : ∀d b : ℕ,d ≤ b → w*(level:ℝ) ≤ d → (b:ℝ) ≤ (1-w)*(level:ℝ) →
      ∀q,multiplicity ((parentEdges D a (2^d) F q).image (physicalPair h R a level b)) ≤
        D.thickness^(-(9*t/4))*depthPower kappa d b := by
    intro d b hdb hdlo hbhi q
    exact middle_pair_upper h original horiginal ha R E F hFE hE hER level hdy w hw hsmall
      g rad hg hgl hgrid hlarge hk hk3 t (9*t/4) hcostQ hdiagMid hmarginMid HU HM
      d b hdb hdlo hbhi q
  have hh := all_pair_upper h original horiginal ha R F hF hFR level hdy hk
    w (9*t/4) (t/4) (3*t) hw hwsmall hlarge hconstant hdiagAll hmarginAll hMid m f hmf hfl p
  rw [NativeCoarsePointMultiplicity.full_source_multiplicity_real h R a level f (parentEdges D a (2^m) F p)
    (fun z hz => hFR z (mem_filter.mp hz).1)]
  rw [←depthPower_eq_relative]
  exact hh

end NativeHereditaryScaleUpper
