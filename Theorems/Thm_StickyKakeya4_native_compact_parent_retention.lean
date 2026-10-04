import Theorems.Thm_StickyKakeya4_native_compact_carrier_count
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeCompactParentRetention
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalParentCount
open NativeCompactChartReach NativeCompactCarrierCount
open scoped ENNReal

lemma parent_count_real {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (N : ℕ) {r : ℝ}
    (hdr : D.thickness≤r) (hr1 : r≤1)
    (hs : 6*(N:ℝ)*r≤1) (hb : ((3+6*(chartReach D a:ℝ))/4)*(N:ℝ)*r≤1) :
    ((parents D a N).card:ℝ)*D.thickness^eta*(r/D.thickness)^3≤729*n := by
  have hh := parent_count h a N hdr hr1 hs hb
  have hr := ENNReal.toReal_mono (by finiteness) hh
  simp only [ENNReal.rpow_eq_pow] at hr
  have hd := h.1.2.1
  have hr0 := hd.trans_le hdr
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hd.le,
    ENNReal.toReal_ofReal (div_pos hr0 hd).le] at hr
  simpa only [mul_assoc,ENNReal.toReal_ofNat] using hr

lemma parent_bound_of_source_count {n : ℕ} {D : FiniteScaleSource n} {eta a C L : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N : ℕ) (hN : 0<N)
    (hL : 6≤L) (hreach : (3+6*(chartReach D a:ℝ))/4≤L)
    (hscale : D.thickness*(L*N)≤1)
    (hcount : (n:ℝ)≤C*D.thickness^(-eta)*(1/D.thickness)^3) :
    ((parents D a N).card:ℝ)≤729*C*L^3*(N:ℝ)^3*D.thickness^(-2*eta) := by
  have hd := h.1.2.1
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hLp : 0<L := by linarith
  let r := 1/(L*N)
  have hr : 0<r := by dsimp [r]; positivity
  have hdr : D.thickness≤r := (le_div_iff₀ (mul_pos hLp hNr)).mpr (by simpa [r] using hscale)
  have hr1 : r≤1 := by
    apply (div_le_iff₀ (mul_pos hLp hNr)).mpr
    have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
    nlinarith
  have hNrid : (N:ℝ)*r=1/L := by dsimp [r]; field_simp
  have hs : 6*(N:ℝ)*r≤1 := by
    rw [mul_assoc,hNrid,mul_one_div]
    exact (div_le_iff₀ hLp).mpr (by simpa using hL)
  have hb : ((3+6*(chartReach D a:ℝ))/4)*(N:ℝ)*r≤1 := by
    rw [mul_assoc,hNrid,mul_one_div]
    exact (div_le_iff₀ hLp).mpr (by simpa using hreach)
  have hpc := parent_count_real h a N hdr hr1 hs hb
  have hboth : ((parents D a N).card:ℝ)*(D.thickness^eta*(r/D.thickness)^3)≤
      729*(C*D.thickness^(-eta)*(1/D.thickness)^3) :=
    (by simpa only [mul_assoc] using hpc.trans (mul_le_mul_of_nonneg_left hcount (by norm_num)))
  have hp := Real.rpow_pos_of_pos hd eta
  have hpneg : D.thickness^(-2*eta)=1/(D.thickness^eta)^2 := by
    rw [show -2*eta=-(eta*2) by ring,Real.rpow_neg hd.le]
    rw [show eta*2=eta*(2:ℕ) by norm_num,Real.rpow_mul_natCast hd.le eta 2]
    simp only [one_div]
  have he : (729*C*L^3*(N:ℝ)^3*D.thickness^(-2*eta)) *
      (D.thickness^eta*(r/D.thickness)^3) =
      729*(C*D.thickness^(-eta)*(1/D.thickness)^3) := by
    rw [hpneg,Real.rpow_neg hd.le]
    dsimp [r]
    field_simp
  apply (mul_le_mul_iff_left₀ (show 0<D.thickness^eta*(r/D.thickness)^3 by positivity)).mp
  rw [he]
  exact hboth

/-- Both constants are chosen from the original compact marked family before
scale selection. This gives the genuine cubic parent-count loss, with the
native AD loss squared, on every original retained finite source. -/
theorem compact_parent_bound (K : Set MarkedLine) (hK : IsCompact K) :
    ∃ C L : ℝ, 0<C ∧ 6≤L ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta a : ℝ) (N : ℕ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i,D.line i∈K) →
      (∀ i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
      0<N → D.thickness*(L*N)≤1 →
      ((parents D a N).card:ℝ)≤C*D.thickness^(-2*eta)*(N:ℝ)^3 := by
  obtain ⟨M,hM,hreach⟩ := compact_uniform_chartReach K hK
  obtain ⟨C,hC,hcount⟩ := compact_carrier_card_bound K hK
  let L := max 6 ((3+6*M)/4)
  have hL : 6≤L := le_max_left _ _
  have hLp : 0<L := by linarith
  refine ⟨729*C*L^3,L,by positivity,hL,?_⟩
  intro n D eta a N h hDK ha hN hscale
  have hco := hcount n D eta h hDK
  have hd := h.1.2.1
  have hr := ENNReal.toReal_mono (by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_ne_zero (by positivity) ENNReal.ofReal_ne_top)
    · finiteness) hco
  simp only [ENNReal.rpow_eq_pow] at hr
  simp only [ENNReal.toReal_mul,← ENNReal.toReal_rpow,ENNReal.toReal_natCast,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal h.1.2.1.le,
    ENNReal.toReal_ofReal (one_div_pos.mpr h.1.2.1).le] at hr
  have hR : (3+6*(chartReach D a:ℝ))/4≤L := by
    have hh := hreach n D eta a h hDK ha
    have hml : (3+6*M)/4≤L := le_max_right _ _
    linarith
  have hh := parent_bound_of_source_count h N hN hL hR hscale hr
  convert hh using 1; ring

end NativeCompactParentRetention
