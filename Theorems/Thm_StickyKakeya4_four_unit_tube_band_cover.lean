import Theorems.Thm_StickyKakeya4_planar_strip_intersection
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped BigOperators
noncomputable section
namespace FourUnitTubeBandCover
open PlanarStripIntersection

def normalLength (a b : ℝ) : ℝ := Real.sqrt (a^2+b^2)

/-- Euclidean normalization is derived from an actual infinity-unit normal. -/
theorem normalized_frame (a b : ℝ) (hunit : |a|=1 ∨ |b|=1) :
    1≤normalLength a b ∧ |a/normalLength a b|≤1 ∧ |b/normalLength a b|≤1 ∧
      (a/normalLength a b)^2+(b/normalLength a b)^2=1 := by
  have hs : (normalLength a b)^2=a^2+b^2 := Real.sq_sqrt (by positivity)
  have hL : 1≤normalLength a b := by
    apply Real.le_sqrt_of_sq_le
    rcases hunit with ha|hb
    · have hh := congrArg (fun x : ℝ => x^2) ha
      simp only [sq_abs,one_pow] at hh
      nlinarith [sq_nonneg b]
    · have hh := congrArg (fun x : ℝ => x^2) hb
      simp only [sq_abs,one_pow] at hh
      nlinarith [sq_nonneg a]
  have hpos : 0<normalLength a b := zero_lt_one.trans_le hL
  have ha : |a|≤normalLength a b := Real.le_sqrt_of_sq_le (by nlinarith [sq_abs a,sq_nonneg b])
  have hb : |b|≤normalLength a b := Real.le_sqrt_of_sq_le (by nlinarith [sq_abs b,sq_nonneg a])
  have hna : |a/normalLength a b|≤1 := by
    rw [abs_div,abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr (by simpa only [one_mul] using ha)
  have hnb : |b/normalLength a b|≤1 := by
    rw [abs_div,abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr (by simpa only [one_mul] using hb)
  refine ⟨hL,hna,hnb,?_⟩
  field_simp [ne_of_gt hpos]
  exact hs.symm

/-- Four literal closed unit intervals cover every allowed longitudinal
coordinate; boundary points do not disappear. -/
theorem four_unit_intervals (t : ℝ) (ht : |t|≤2) :
    ∃ k∈Finset.Icc (-2:ℤ) 1, |t-((k:ℝ)+1/2)|≤1/2 := by
  obtain ⟨hl,hu⟩ := abs_le.mp ht
  by_cases h1 : t≤-1
  · refine ⟨-2,by decide,?_⟩
    norm_num
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · by_cases h2 : t≤0
    · refine ⟨-1,by decide,?_⟩
      norm_num
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    · by_cases h3 : t≤1
      · refine ⟨0,by decide,?_⟩
        norm_num
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      · refine ⟨1,by decide,?_⟩
        norm_num
        exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- A physical rectangle of full width theta and length one, in the
orthonormal frame determined by the Euclidean unit normal (nx,ny). -/
def unitTube (Pts : Finset (ℝ × ℝ)) (nx ny c h theta : ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact Pts.filter (fun p => |nx*p.1+ny*p.2-c|≤theta/2 ∧
    |-ny*p.1+nx*p.2-h|≤1/2)

/-- Original unit-tube two-ends bounds imply the required whole-band count
by an ACTUAL four-tube cover of the bounded source, with no cover premise. -/
theorem band_card_le_four
    (Pts : Finset (ℝ × ℝ)) (a b c B theta eta : ℝ)
    (hunit : |a|=1 ∨ |b|=1) (hB : B≤theta/2)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (htwoends : ∀ nx ny c0 h0 : ℝ, nx^2+ny^2=1 →
      ((unitTube Pts nx ny c0 h0 theta).card : ℝ)≤eta*Pts.card) :
    ((Pts.filter (fun p => |PlanarStripIntersection.residual a b c p|≤B)).card : ℝ)≤
      4*eta*Pts.card := by
  classical
  let L := normalLength a b
  let nx := a/L
  let ny := b/L
  have hframe := normalized_frame a b hunit
  have hL : 1≤L := hframe.1
  have hLpos : 0<L := zero_lt_one.trans_le hL
  have hnx : |nx|≤1 := hframe.2.1
  have hny : |ny|≤1 := hframe.2.2.1
  have hnorm : nx^2+ny^2=1 := hframe.2.2.2
  let Tubes := fun k : ℤ => unitTube Pts nx ny (c/L) ((k:ℝ)+1/2) theta
  have hcover : Pts.filter (fun p => |PlanarStripIntersection.residual a b c p|≤B)⊆
      (Finset.Icc (-2:ℤ) 1).biUnion Tubes := by
    intro p hp
    obtain ⟨hpP,hpB⟩ := Finset.mem_filter.mp hp
    have ht : |-ny*p.1+nx*p.2|≤2 := by
      have h1 := mul_le_mul hny (hbox p hpP).1 (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
      have h2 := mul_le_mul hnx (hbox p hpP).2 (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
      have h := abs_add_le (-ny*p.1) (nx*p.2)
      simp only [abs_mul,abs_neg] at h
      nlinarith only [h,h1,h2]
    obtain ⟨k,hk,hkt⟩ := four_unit_intervals (-ny*p.1+nx*p.2) ht
    apply Finset.mem_biUnion.mpr
    refine ⟨k,hk,Finset.mem_filter.mpr ⟨hpP,?_,hkt⟩⟩
    have heq : nx*p.1+ny*p.2-c/L=PlanarStripIntersection.residual a b c p/L := by
      dsimp [nx,ny]
      unfold PlanarStripIntersection.residual
      ring
    rw [heq,abs_div,abs_of_pos hLpos]
    calc
      _ ≤ |PlanarStripIntersection.residual a b c p| := by
        apply (div_le_iff₀ hLpos).mpr
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hL
          (abs_nonneg (PlanarStripIntersection.residual a b c p))
      _ ≤ B := hpB
      _ ≤ _ := hB
  have hcard : (Pts.filter (fun p => |PlanarStripIntersection.residual a b c p|≤B)).card≤
      ∑ k∈Finset.Icc (-2:ℤ) 1, (Tubes k).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcardR : ((Pts.filter (fun p => |PlanarStripIntersection.residual a b c p|≤B)).card : ℝ)≤
      ∑ k∈Finset.Icc (-2:ℤ) 1, ((Tubes k).card : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ _ := hcardR
    _ ≤ ∑ _k∈Finset.Icc (-2:ℤ) 1, eta*(Pts.card : ℝ) :=
      Finset.sum_le_sum (fun k _ => htwoends nx ny (c/L) ((k:ℝ)+1/2) hnorm)
    _ = _ := by
      have hc : (Finset.Icc (-2:ℤ) 1).card=4 := by decide
      simp only [Finset.sum_const,hc,nsmul_eq_mul]
      ring

end FourUnitTubeBandCover
