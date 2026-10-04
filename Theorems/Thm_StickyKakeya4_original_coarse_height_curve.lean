import Theorems.Thm_StickyKakeya4_original_separated_height_cap
import Theorems.Thm_StickyKakeya4_original_height_graph_density
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalCoarseHeightCurve
open Classical
abbrev Point := ℝ × (ℝ × ℝ)
def coarseHeight (width : ℝ) (z : ℝ) : ℤ := ⌊z/width⌋
def representative (Z : Finset ℝ) (hZ : Z.Nonempty) (width : ℝ) (k : ℤ) : ℝ :=
  if hk : k ∈ Z.image (coarseHeight width) then Classical.choose (Finset.mem_image.mp hk) else Classical.choose hZ
lemma representative_spec (Z : Finset ℝ) (hZ : Z.Nonempty) (width : ℝ)
    (k : ℤ) (hk : k ∈ Z.image (coarseHeight width)) :
    representative Z hZ width k ∈ Z ∧ coarseHeight width (representative Z hZ width k)=k := by
  simpa only [representative,dif_pos hk] using Classical.choose_spec (Finset.mem_image.mp hk)
def heightGraph (rho Lip z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ) (z : ℝ) : Point :=
  ((z-z₀)/rho,(Lip*rho)⁻¹ • (f z-f₀))
theorem sampled_height_interval_cap (Q : Finset ℤ) (sample : ℤ → ℝ)
    {rho width : ℝ} (hrho : 0 < rho) (hw : 0 < width)
    (hlabel : ∀ k ∈ Q, coarseHeight width (sample k)=k) (z₀ c R : ℝ) (hR : 0 ≤ R) :
    ((Q.filter (fun k => c ≤ (sample k-z₀)/rho ∧ (sample k-z₀)/rho ≤ c+R)).card : ℝ) ≤ (rho*R)/width+2 := by
  let S := Q.filter (fun k => c ≤ (sample k-z₀)/rho ∧ (sample k-z₀)/rho ≤ c+R)
  let J := Finset.Icc ⌊(rho*c+z₀)/width⌋ ⌊(rho*c+z₀+rho*R)/width⌋
  have hsub : S ⊆ J := by
    intro k hk
    obtain ⟨hkQ,hlo,hhi⟩ := Finset.mem_filter.mp hk
    have hl := (le_div_iff₀ hrho).mp hlo
    have hu := (div_le_iff₀ hrho).mp hhi
    have hkl : ⌊(rho*c+z₀)/width⌋ ≤ ⌊sample k/width⌋ :=
      Int.floor_mono (div_le_div_of_nonneg_right (by nlinarith : rho*c+z₀ ≤ sample k) hw.le)
    have hku : ⌊sample k/width⌋ ≤ ⌊(rho*c+z₀+rho*R)/width⌋ :=
      Int.floor_mono (div_le_div_of_nonneg_right (by nlinarith : sample k ≤ rho*c+z₀+rho*R) hw.le)
    have he := hlabel k hkQ
    exact Finset.mem_Icc.mpr ⟨hkl.trans_eq he,he.symm.trans_le hku⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (OriginalHeightIntervalCap.floor_interval_card width (rho*c+z₀) (rho*R) hw (mul_nonneg hrho.le hR))
theorem sampled_curve_ball_cap (Q : Finset ℤ) (sample : ℤ → ℝ)
    {rho width : ℝ} (hrho : 0 < rho) (hw : 0 < width)
    (hlabel : ∀ k ∈ Q, coarseHeight width (sample k)=k)
    (Lip z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ) (center : Point) {R : ℝ} (hR : 0 ≤ R) :
    ((Q.filter (fun k => ‖heightGraph rho Lip z₀ f₀ f (sample k)-center‖ ≤ R)).card : ℝ) ≤ 2*rho*R/width+2 := by
  have hsub : Q.filter (fun k => ‖heightGraph rho Lip z₀ f₀ f (sample k)-center‖ ≤ R) ⊆
      Q.filter (fun k => center.1-R ≤ (sample k-z₀)/rho ∧ (sample k-z₀)/rho ≤ center.1-R+2*R) := by
    intro k hk
    obtain ⟨hkQ,hkn⟩ := Finset.mem_filter.mp hk
    have hh := (max_le_iff.mp hkn).1
    change |(sample k-z₀)/rho-center.1| ≤ R at hh
    obtain ⟨hl,hu⟩ := abs_le.mp hh
    exact Finset.mem_filter.mpr ⟨hkQ,by linarith,by linarith⟩
  have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (sampled_height_interval_cap Q sample hrho hw hlabel z₀ (center.1-R) (2*R) (by positivity))
  have hid : rho*(2*R)=2*rho*R := by ring
  simpa only [hid] using hc
theorem original_coarse_curve_KT1 (Z : Finset ℝ) (hZ : Z.Nonempty)
    {rho width : ℝ} (hrho : 0 < rho) (hw : 0 < width)
    (Lip z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ) (center : Point) {R : ℝ} (hR : width/rho ≤ R) :
    (((Z.image (coarseHeight width)).filter (fun k =>
      ‖heightGraph rho Lip z₀ f₀ f (representative Z hZ width k)-center‖ ≤ R)).card : ℝ) ≤ 4*R/(width/rho) := by
  have hR0 : 0 ≤ R := (div_pos hw hrho).le.trans hR
  have hh := sampled_curve_ball_cap (Z.image (coarseHeight width)) (representative Z hZ width)
    hrho hw (fun k hk => (representative_spec Z hZ width k hk).2) Lip z₀ f₀ f center hR0
  have hr : 1 ≤ rho*R/width := (le_div_iff₀ hw).mpr (by
    have hc := (div_le_iff₀ hrho).mp hR
    nlinarith)
  have hid : 4*R/(width/rho)=4*(rho*R/width) := by field_simp
  rw [hid]
  calc
    _ ≤ 2*rho*R/width+2 := hh
    _ ≤ 4*(rho*R/width) := by
      have heq : 2*rho*R/width=2*(rho*R/width) := by ring
      rw [heq]
      linarith
theorem same_cell_graph_error {rho Lip width z w : ℝ}
    (hrho : 0 < rho) (hLip : 0 < Lip) (hw : 0 < width)
    (z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ)
    (hcell : coarseHeight width z=coarseHeight width w) (hosc : ‖f z-f w‖ ≤ Lip*width) :
    ‖heightGraph rho Lip z₀ f₀ f z-heightGraph rho Lip z₀ f₀ f w‖ ≤ width/rho := by
  have hz₁ := (le_div_iff₀ hw).mp (Int.floor_le (z/width))
  have hz₂ := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (z/width))
  have hw₁ := (le_div_iff₀ hw).mp (Int.floor_le (w/width))
  have hw₂ := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (w/width))
  change ⌊z/width⌋=⌊w/width⌋ at hcell
  rw [hcell] at hz₁ hz₂
  have hgap : |z-w| ≤ width := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  change max |(z-z₀)/rho-(w-z₀)/rho| ‖(Lip*rho)⁻¹ • (f z-f₀)-(Lip*rho)⁻¹ • (f w-f₀)‖ ≤ width/rho
  apply max_le
  · have hid : (z-z₀)/rho-(w-z₀)/rho=(z-w)/rho := by ring
    rw [hid,abs_div,abs_of_pos hrho]
    exact div_le_div_of_nonneg_right hgap hrho.le
  · have hid : (Lip*rho)⁻¹ • (f z-f₀)-(Lip*rho)⁻¹ • (f w-f₀)=(Lip*rho)⁻¹ • (f z-f w) := by module
    rw [hid,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (mul_pos hLip hrho))]
    calc
      _ = ‖f z-f w‖/(Lip*rho) := by ring
      _ ≤ (Lip*width)/(Lip*rho) := div_le_div_of_nonneg_right hosc (mul_pos hLip hrho).le
      _ = width/rho := by field_simp
end OriginalCoarseHeightCurve
