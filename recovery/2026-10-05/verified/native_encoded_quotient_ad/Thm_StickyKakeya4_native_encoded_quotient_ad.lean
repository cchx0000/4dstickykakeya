import Theorems.Thm_StickyKakeya4_native_quotient_lattice_transport
import Theorems.Thm_StickyKakeya4_native_quotient_lattice_counts
import Theorems.Thm_StickyKakeya4_native_quotient_grid_centers
import Theorems.Thm_StickyKakeya4_native_half_scale_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000
noncomputable section
namespace NativeEncodedQuotientAD
open Classical Finset GridQuotientAD NativeTwoMapRetainedSliceLabels
open NativeQuotientLatticeTransport NativeQuotientLatticeCounts NativeQuotientGridCenters
open NativeSliceClassBalls NativeHalfScaleInterpolation

/-- Explicit quotient AD constant. Its inputs are the ambient AD constant
and the already obtained full tangent-fiber population. -/
def quotientConstant (k l : ℕ) (lam K t : ℝ) : ℝ :=
  NativeHalfScaleInterpolation.constant ((1/K)/(3:ℝ)^k)
    ((3:ℝ)^k*(2:ℝ)^(k+l)*K/lam) ((5:ℝ)^(k+l)*K/lam) (t-k)

lemma quotientConstant_one_le (k l : ℕ) (lam K t : ℝ) : 1 ≤ quotientConstant k l lam K t :=
  NativeHalfScaleInterpolation.constant_one_le _ _ _ _

/-- Ambient encoded XY AD plus genuine full X-fiber population gives actual
quotient AD. The upper test through2N has physical radius at mostone;
large quotient radii use a derived global count rather than a full-ball claim. -/
theorem quotient_AD_of_encoded_AD {k l : ℕ} (hd : k+l=3)
    (S : Finset (XY k l)) (height : ℤ) (N : ℕ) (hN : 1 ≤ N)
    {mu lam K t : ℝ} (hmu : 0 < mu) (hlam : 0 < lam) (hK : 0 < K)
    (hscale : mu*(N:ℝ)=1/2) (hkt : (k:ℝ) ≤ t) (htdim : t ≤ ((k+l:ℕ):ℝ))
    (hx : ∀p∈productSlice S height,∀i,|p.1 i| ≤ (N:ℤ))
    (hy : ∀p∈productSlice S height,∀i,|p.2 i| ≤ ((2*N:ℕ):ℤ))
    (hdense : ∀y∈(productSlice S height).image Prod.snd,
      lam*(N:ℝ)^k ≤ ((fiber (productSlice S height) y).card:ℝ))
    (H : FiniteVoronoiRealADCoarsening.ADBounds
      (realizedSlice (S.image (encode hd)) mu height) mu K t) :
    0 ≤ t-k ∧ FiniteVoronoiRealADCoarsening.ADBounds
      (((productSlice S height).image Prod.snd).image (center mu)) mu
      (quotientConstant k l lam K t) (t-k) := by
  have hupper : ∀p∈productSlice S height,∀R:ℕ,1 ≤ R → R ≤ 2*N →
      ((ambientBox (productSlice S height) p R).card:ℝ) ≤ K*(R:ℝ)^t := by
    intro p hp R hR hRN
    have hRone : mu*(R:ℝ) ≤ 1 := by
      have hh : (R:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hRN
      nlinarith only [hh,hmu,hscale]
    exact (ambient_bounds_of_AD hd S height hmu H p hp R hR hRone).2
  have hlower : ∀p∈productSlice S height,∀R:ℕ,1 ≤ R → R ≤ N →
      (1/K)*(R:ℝ)^t ≤ ((ambientBox (productSlice S height) p R).card:ℝ) := by
    intro p hp R hR hRN
    have hRone : mu*(R:ℝ) ≤ 1 := by
      have hh : (R:ℝ) ≤ (N:ℝ) := by exact_mod_cast hRN
      nlinarith only [hh,hmu,hscale]
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using
      (ambient_bounds_of_AD hd S height hmu H p hp R hR hRone).1
  have hcounts := quotient_counts (productSlice S height) N hN lam (1/K) K t
    hlam hK.le hkt htdim hx hy hdense hlower hupper
  refine ⟨hcounts.1.1,?_⟩
  apply NativeHalfScaleInterpolation.ADBounds_of_counts _ hmu (by positivity)
  intro z hz r hr hro
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
  have htest : ∀R:ℕ,1 ≤ R → R ≤ N →
      ((1/K)/(3:ℝ)^k)*(R:ℝ)^(t-k) ≤
        RealScalarADInterpolation.ballCount (((productSlice S height).image Prod.snd).image (center mu))
          (center mu y) (mu*(R:ℝ)) ∧
      RealScalarADInterpolation.ballCount (((productSlice S height).image Prod.snd).image (center mu))
          (center mu y) (mu*(R:ℝ)) ≤
        ((3:ℝ)^k*(2:ℝ)^(k+l)*K/lam)*(R:ℝ)^(t-k) := by
    intro R hR hRN
    rw [quotient_ball_count _ hmu]
    exact hcounts.1.2 y hy R hR hRN
  have hglobal : ((((productSlice S height).image Prod.snd).image (center mu)).card:ℝ) ≤
      ((5:ℝ)^(k+l)*K/lam)*(N:ℝ)^(t-k) := by
    rw [quotient_card _ hmu]
    exact hcounts.2
  exact all_radius_counts _ (center mu y) N hN hmu hcounts.1.1
    (by positivity) (by positivity) (by positivity) hscale htest hglobal r hr hro

end NativeEncodedQuotientAD
