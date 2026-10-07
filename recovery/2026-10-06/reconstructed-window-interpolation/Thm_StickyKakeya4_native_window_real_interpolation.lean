import Theorems.Thm_StickyKakeya4_native_window_integer_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

noncomputable section
namespace NativeWindowRealInterpolation
open Classical Finset NativeWindowNesting NativeWindowXYLabels
open NativeQuotientLatticeTransport NativeQuotientGridCenters GridQuotientAD
open NativeWindowIntegerInterpolation RealScalarADInterpolation

def points {k l : ℕ} (S : Finset (XY k l)) (R : ℕ) (mu : ℝ) (z : XY k l) :
    Finset (Fin l → ℝ) := (atPoint S R z).image (center mu)

lemma ball_count_eq {k l : ℕ} (S : Finset (XY k l)) (R : ℕ) {mu : ℝ}
    (hmu : 0 < mu) (z : XY k l) (n : ℕ) :
    ballCount (points S R mu z) (center mu (gridDiv R z.2.2)) (mu*(n:ℝ)) =
      count S R z n := by
  unfold ballCount points count
  rw [ball_card _ hmu]

lemma points_card {k l : ℕ} (S : Finset (XY k l)) (R : ℕ) {mu : ℝ}
    (hmu : 0 < mu) (z : XY k l) : (points S R mu z).card=(atPoint S R z).card :=
  card_image_of_injective _ (center_injective hmu)

lemma atPoint_eq_of_height {k l : ℕ} (S : Finset (XY k l)) (R : ℕ) (z w : XY k l)
    (h : z.1/((8*R:ℕ):ℤ)=w.1/((8*R:ℕ):ℤ)) : atPoint S R z=atPoint S R w := by
  unfold atPoint
  rw [h]

/-- Interpolation uses a genuine fine descendant and a genuine coarse
ancestor of the SAME source point. No mass is moved between windows. -/
theorem real_counts_from_brackets {k l : ℕ} (S : Finset (XY k l))
    (R Ds Db N : ℕ) (hDs : 0 < Ds) (hDb : 0 < Db) (hN : 1 ≤ N)
    (z : XY k l) {mu c U G s : ℝ}
    (hmu : 0 < mu) (hc : 0 ≤ c) (hU : 0 ≤ U) (hG : 0 ≤ G) (hs : 0 ≤ s)
    (hscale : mu*((Db*N:ℕ):ℝ)=1/2)
    (Hfine : ∀n:ℕ,1 ≤ n → n ≤ Ds*(Db*N) → c*(n:ℝ)^s ≤ count S R z n)
    (Hbig : ∀n:ℕ,1 ≤ n → n ≤ N → count S ((R*Ds)*Db) z n ≤ U*(n:ℝ)^s)
    (Hglobal : ((atPoint S ((R*Ds)*Db) z).card:ℝ) ≤ G*(N:ℝ)^s)
    (r : ℝ) (hr : mu ≤ r) (hrone : r ≤ 1) :
    (c/(Ds:ℝ)^l)*(r/mu)^s ≤
      (2:ℝ)^s*ballCount (points S (R*Ds) mu z) (center mu (gridDiv (R*Ds) z.2.2)) r ∧
    ballCount (points S (R*Ds) mu z) (center mu (gridDiv (R*Ds) z.2.2)) r ≤
      (2:ℝ)^s*max (upperConstant l Db U s) ((Db:ℝ)^l*G)*(r/mu)^s := by
  apply NativeHalfScaleInterpolation.all_radius_counts
    (points S (R*Ds) mu z) (center mu (gridDiv (R*Ds) z.2.2)) (Db*N)
    (hN.trans (Nat.le_mul_of_pos_left N hDb)) hmu hs
    (by positivity) (upperConstant_nonneg l Db U s) (by positivity) hscale
  · intro n hn hnN
    rw [ball_count_eq S (R*Ds) hmu]
    exact ⟨lower_from_descendant S R Ds (Db*N) hDs z hc hs Hfine n hn hnN,
      upper_from_ancestor S (R*Ds) Db N hDb z hU hs Hbig n hn hnN⟩
  · rw [points_card S (R*Ds) hmu]
    exact global_from_ancestor S (R*Ds) Db N hDb z hG hs Hglobal
  · exact hr
  · exact hrone

/-- Every point of an occupied intermediate window has its own original
source anchor. This upgrades the two prepared-scale profiles to the actual
whole intermediate quotient set, at all real radii from its mesh to one. -/
theorem AD_from_brackets {k l : ℕ} (S : Finset (XY k l))
    (R Ds Db N : ℕ) (hDs : 0 < Ds) (hDb : 0 < Db) (hN : 1 ≤ N)
    {mu c U G s : ℝ} (hmu : 0 < mu) (hc : 0 < c)
    (hU : 0 ≤ U) (hG : 0 ≤ G) (hs : 0 ≤ s)
    (hscale : mu*((Db*N:ℕ):ℝ)=1/2)
    (Hfine : ∀z∈S,∀n:ℕ,1 ≤ n → n ≤ Ds*(Db*N) → c*(n:ℝ)^s ≤ count S R z n)
    (Hbig : ∀z∈S,∀n:ℕ,1 ≤ n → n ≤ N → count S ((R*Ds)*Db) z n ≤ U*(n:ℝ)^s)
    (Hglobal : ∀z∈S,((atPoint S ((R*Ds)*Db) z).card:ℝ) ≤ G*(N:ℝ)^s)
    (anchor : XY k l) :
    FiniteVoronoiRealADCoarsening.ADBounds (points S (R*Ds) mu anchor) mu
      (NativeHalfScaleInterpolation.constant (c/(Ds:ℝ)^l)
        (upperConstant l Db U s) ((Db:ℝ)^l*G) s) s := by
  have hDsp : (0:ℝ)<Ds := by exact_mod_cast hDs
  apply NativeHalfScaleInterpolation.ADBounds_of_counts _ hmu (by positivity)
  intro x hx r hr hro
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
  rw [atPoint_eq_image] at hy
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
  obtain ⟨hzS,hheight⟩ := mem_filter.mp hz
  have he : points S (R*Ds) mu z=points S (R*Ds) mu anchor := by
    unfold points
    rw [atPoint_eq_of_height S (R*Ds) z anchor hheight]
  have hh := real_counts_from_brackets S R Ds Db N hDs hDb hN z hmu hc.le hU hG hs
    hscale (Hfine z hzS) (Hbig z hzS) (Hglobal z hzS) r hr hro
  simpa only [he] using hh

end NativeWindowRealInterpolation
