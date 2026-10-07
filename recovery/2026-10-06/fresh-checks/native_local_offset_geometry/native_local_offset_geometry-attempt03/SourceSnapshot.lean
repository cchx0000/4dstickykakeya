import Theorems.Thm_StickyKakeya4_native_matrix_height_wholepoint

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section

namespace NativeLocalOffsetGeometry
open Classical Finset
open scoped BigOperators

/-- A single affine coordinate, using at most two actual tangent entries.
Only local matrix oscillation v is used; no global Lipschitz bound occurs. -/
theorem affine_offset_difference {k : ℕ} (hk : k ≤ 2)
    (F G tangent tangent' : Fin k → ℝ) (normal normal' xi xi' E M v A B : ℝ)
    (hM : 0 < M) (hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀j,|F j| ≤ (1/4:ℝ))
    (hT : ∀j,|tangent' j| ≤ B)
    (hTd : ∀j,|tangent j-tangent' j| ≤ A/M)
    (hFd : ∀j,|F j-G j| ≤ v)
    (hN : |normal-normal'| ≤ A/M)
    (hres : |normal-(∑j,F j*tangent j)-xi| ≤ E)
    (hres' : |normal'-(∑j,G j*tangent' j)-xi'| ≤ E) :
    |xi-xi'| ≤ 2*E+2*A/M+2*B*v := by
  have hInv : 0 ≤ A/M := by positivity
  have hterm (j : Fin k) : |F j*tangent j-G j*tangent' j| ≤ (1/4:ℝ)*(A/M)+v*B := by
    calc
      _ = |F j*(tangent j-tangent' j)+(F j-G j)*tangent' j| := by congr 1; ring
      _ ≤ |F j*(tangent j-tangent' j)|+|(F j-G j)*tangent' j| := abs_add_le _ _
      _ = |F j| * |tangent j-tangent' j|+|F j-G j| * |tangent' j| := by rw [abs_mul,abs_mul]
      _ ≤ (1/4:ℝ)*(A/M)+v*B := add_le_add
        (mul_le_mul (hF j) (hTd j) (abs_nonneg _) (by norm_num))
        (mul_le_mul (hFd j) (hT j) (abs_nonneg _) hv)
      _ = _ := by ring
  have hsum : |(∑j,F j*tangent j)-(∑j,G j*tangent' j)| ≤ A/M+2*B*v := by
    have hkR : (k:ℝ) ≤ 2 := by exact_mod_cast hk
    calc
      _ = |∑j,(F j*tangent j-G j*tangent' j)| := by rw [sum_sub_distrib]
      _ ≤ ∑j,|F j*tangent j-G j*tangent' j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑_j : Fin k,((1/4:ℝ)*(A/M)+v*B) := sum_le_sum (fun j _ => hterm j)
      _ = (k:ℝ)*((1/4:ℝ)*(A/M)+v*B) := by simp; ring
      _ ≤ 2*((1/4:ℝ)*(A/M)+v*B) := mul_le_mul_of_nonneg_right hkR (by positivity)
      _ ≤ A/M+2*B*v := by nlinarith only [hInv]
  obtain ⟨hresL,hresU⟩ := abs_le.mp hres
  obtain ⟨hresL',hresU'⟩ := abs_le.mp hres'
  obtain ⟨hNL,hNU⟩ := abs_le.mp hN
  obtain ⟨hSL,hSU⟩ := abs_le.mp hsum
  rw [mul_div_assoc]
  apply abs_le.mpr
  constructor <;> nlinarith only [hresL,hresU,hresL',hresU',hNL,hNU,hSL,hSU]

/-- Two genuine incident directions with the same angular label control
the original point offsets coordinate by coordinate. The angle-coordinate
readback, residuals, and local field oscillation are explicit geometric inputs. -/
theorem shared_angle_offsets {P T Angle : Type*} {k ell : ℕ}
    (S : Finset (P × T)) (angle : T → Angle)
    (tangent : T → Fin k → ℝ) (normal : T → Fin ell → ℝ)
    (field : P → Fin ell → Fin k → ℝ) (xi : P → Fin ell → ℝ)
    (E M v A B : ℝ) (hk : k ≤ 2) (hM : 0 < M) (hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT : ∀z∈S,∀j,|tangent z.2 j| ≤ B)
    (hF : ∀p∈S.image Prod.fst,∀i j,|field p i j| ≤ (1/4:ℝ))
    (hVar : ∀p∈S.image Prod.fst,∀q∈S.image Prod.fst,∀i j,|field p i j-field q i j| ≤ v)
    (hAngle : ∀z∈S,∀w∈S,angle z.2=angle w.2 →
      (∀j,|tangent z.2 j-tangent w.2 j| ≤ A/M) ∧
      (∀i,|normal z.2 i-normal w.2 i| ≤ A/M))
    (hRes : ∀z∈S,∀i,|normal z.2 i-(∑j,field z.1 i j*tangent z.2 j)-xi z.1 i| ≤ E)
    {z w : P × T} (hz : z∈S) (hw : w∈S) (ha : angle z.2=angle w.2) :
    ∀i,|xi z.1 i-xi w.1 i| ≤ 2*E+2*A/M+2*B*v := by
  intro i
  have hzP := mem_image_of_mem Prod.fst hz
  have hwP := mem_image_of_mem Prod.fst hw
  obtain ⟨hTd,hNd⟩ := hAngle z hz w hw ha
  exact affine_offset_difference hk (field z.1 i) (field w.1 i)
    (tangent z.2) (tangent w.2) (normal z.2 i) (normal w.2 i) (xi z.1 i) (xi w.1 i)
    E M v A B hM hv hA hB (hF z.1 hzP i) (hT w hw) hTd (hVar z.1 hzP w.1 hwP i)
    (hNd i) (hRes z hz i) (hRes w hw i)

end NativeLocalOffsetGeometry
