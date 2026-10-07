import Theorems.Thm_StickyKakeya4_native_matrix_height_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeActualNewCutBudget
open Classical Finset NativeMatrixHeightWholePoint NativeMatrixHeightBudget
open scoped BigOperators

/-- Kcoh is fixed before epsilon and the hierarchy; it is independent of g,
Khalf and the number of source levels. Only the prepared mesh VALUES vary. -/
def offsetCoefficient (normal g : ℕ) (meshConstant row : ℝ) : ℝ :=
  (4:ℝ)^normal * meshConstant * (2744*row*((g:ℝ)+1))

/-- The literal quotient used inside the actual source's Gcoh ceiling. -/
def offsetCharge (normal g : ℕ) (meshConstant row r loss d kappa mesh : ℝ) : ℝ :=
  ((4:ℝ)^normal*(meshConstant*r^(-loss)*mesh^(-kappa)))/
    (mesh^(-kappa)/((2744*row*((g:ℝ)+1))*r^(-(9*d))))

def coherenceCharge (K normal g : ℕ) (meshConstant row r loss d metric kappa : ℝ)
    (mesh : Fin K → ℝ) : ℕ :=
  (modulus (2*metric))^(2*K)*∏j,⌈offsetCharge normal g meshConstant row r loss d kappa (mesh j)⌉₊

/-- Exactly the NEW cuts. The old graph cost, quotientCost and third
F3/Q3 allowance do not appear in this charge. -/
def newCutCharge (K Ksupport normal g R0 : ℕ)
    (meshConstant row r loss d metric kappa : ℝ) (mesh : Fin K → ℝ) : ℕ :=
  coherenceCharge K normal g meshConstant row r loss d metric kappa mesh *
    (8*R0)*53^(4*Ksupport)*8^4

/-- Normal dimension is bounded by4, making this fixed factor uniform in
all later selected ranks. It may depend on g, which is fixed before D. -/
def fixedFactor (K Ksupport g : ℕ) (meshConstant row : ℝ) : ℝ :=
  (144:ℝ)^K*(offsetCoefficient 4 g meshConstant row+1)^K*
    1280*(53:ℝ)^(4*Ksupport)*(8:ℝ)^4

def newExponent (K : ℕ) (epsilon loss d : ℝ) : ℝ :=
  (4*(K:ℝ)+2)*epsilon+(K:ℝ)*(loss+9*d)

lemma offsetCharge_eq (normal g : ℕ) (meshConstant row r loss d kappa mesh : ℝ)
    (hr : 0 < r) (hmesh : 0 < mesh) :
    offsetCharge normal g meshConstant row r loss d kappa mesh=
      offsetCoefficient normal g meshConstant row*r^(-(loss+9*d)) := by
  have hp : mesh^(-kappa) ≠ 0 := (Real.rpow_pos_of_pos hmesh _).ne'
  have he : r^(-loss)*r^(-(9*d))=r^(-(loss+9*d)) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  calc
    _ = offsetCoefficient normal g meshConstant row*(r^(-loss)*r^(-(9*d))) := by
      unfold offsetCharge offsetCoefficient
      rw [div_div_eq_mul_div]
      field_simp [hp]
    _ = _ := by rw [he]

lemma ceiling_power_bound {A r power : ℝ} (hA : 0 ≤ A)
    (hr : 0 < r) (hr1 : r ≤ 1) (hpower : 0 ≤ power) :
    (⌈A*r^(-power)⌉₊:ℝ) ≤ (A+1)*r^(-power) := by
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg hA (Real.rpow_nonneg hr.le (-power)))).le
  have hone := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1
    (neg_nonpos.mpr hpower)
  nlinarith only [hceil,hone]

lemma offset_product_bound (K normal g : ℕ) (hnormal : normal ≤ 4)
    (meshConstant row r loss d kappa : ℝ) (mesh : Fin K → ℝ)
    (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row) (hr : 0 < r) (hr1 : r ≤ 1)
    (hloss : 0 ≤ loss) (hd : 0 ≤ d) (hmesh : ∀j,0 < mesh j) :
    ((∏j,⌈offsetCharge normal g meshConstant row r loss d kappa (mesh j)⌉₊:ℕ):ℝ) ≤
      (offsetCoefficient 4 g meshConstant row+1)^K*r^(-((K:ℝ)*(loss+9*d))) := by
  have hA : 0 ≤ offsetCoefficient normal g meshConstant row := by
    unfold offsetCoefficient
    positivity
  have hfour : (4:ℝ)^normal ≤ (4:ℝ)^4 := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (4:ℕ)) hnormal
  have hA4 : offsetCoefficient normal g meshConstant row ≤ offsetCoefficient 4 g meshConstant row := by
    unfold offsetCoefficient
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfour hC) (by positivity)
  have hceil (j : Fin K) :
      (⌈offsetCharge normal g meshConstant row r loss d kappa (mesh j)⌉₊:ℝ) ≤
        (offsetCoefficient 4 g meshConstant row+1)*r^(-(loss+9*d)) := by
    rw [offsetCharge_eq normal g meshConstant row r loss d kappa (mesh j) hr (hmesh j)]
    exact (ceiling_power_bound hA hr hr1 (by positivity)).trans
      (mul_le_mul_of_nonneg_right (add_le_add hA4 (le_refl (1:ℝ))) (Real.rpow_nonneg hr.le _))
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏_j : Fin K,(offsetCoefficient 4 g meshConstant row+1)*r^(-(loss+9*d)) :=
      prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun j _ => hceil j)
    _ = (offsetCoefficient 4 g meshConstant row+1)^K*(r^(-(loss+9*d)))^K := by
      simp only [prod_const,card_univ,Fintype.card_fin,mul_pow]
    _ = _ := by
      rw [←Real.rpow_mul_natCast hr.le]
      congr 2
      ring

/-- The exact source Gcoh, including its natural palette and all ceilings,
has no remaining dependence on the prepared mesh powers. -/
theorem coherenceCharge_bound (K normal g : ℕ) (hnormal : normal ≤ 4)
    (meshConstant row r loss d metric epsilon kappa : ℝ) (mesh : Fin K → ℝ)
    (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row) (hr : 0 < r) (hr1 : r ≤ 1)
    (hloss : 0 ≤ loss) (hd : 0 ≤ d) (hmetric : 0 ≤ metric) (hepsilon : 0 ≤ epsilon)
    (hLip : metric ≤ r^(-2*epsilon)) (hmesh : ∀j,0 < mesh j) :
    (coherenceCharge K normal g meshConstant row r loss d metric kappa mesh:ℝ) ≤
      (144:ℝ)^K*(offsetCoefficient 4 g meshConstant row+1)^K*
        r^(-(4*(K:ℝ)*epsilon+(K:ℝ)*(loss+9*d))) := by
  have hPal : ((modulus (2*metric)^(2*K):ℕ):ℝ) ≤
      (144:ℝ)^K*r^(-(4*(K:ℝ)*epsilon)) := by
    have hp := Real.rpow_pos_of_pos hr (-2*epsilon)
    simpa only [Nat.cast_pow] using natural_palette_le_explicit_power K hr hr1
      (show 0 ≤ 2*metric by positivity) hepsilon
      (show 2*metric ≤ 3*r^(-2*epsilon) by nlinarith only [hLip,hp])
  have hOffset := offset_product_bound K normal g hnormal meshConstant row r loss d kappa mesh
    hC hrow hr hr1 hloss hd hmesh
  have hp := mul_le_mul hPal hOffset (Nat.cast_nonneg _) (by positivity)
  have he : r^(-(4*(K:ℝ)*epsilon))*r^(-((K:ℝ)*(loss+9*d)))=
      r^(-(4*(K:ℝ)*epsilon+(K:ℝ)*(loss+9*d))) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  unfold coherenceCharge
  rw [Nat.cast_mul]
  calc
    _ ≤ ((144:ℝ)^K*r^(-(4*(K:ℝ)*epsilon)))*
        ((offsetCoefficient 4 g meshConstant row+1)^K*r^(-((K:ℝ)*(loss+9*d)))) := hp
    _ = ((144:ℝ)^K*(offsetCoefficient 4 g meshConstant row+1)^K)*
        (r^(-(4*(K:ℝ)*epsilon))*r^(-((K:ℝ)*(loss+9*d)))) := by ring
    _ = _ := by rw [he]

/-- The already constructed base supplies the height charge. Its comparison
with r pays two further epsilon; no old graph/quotient/core cost is repeated. -/
theorem newCutCharge_bound (K Ksupport normal g R0 : ℕ) (hnormal : normal ≤ 4)
    (meshConstant row r loss d metric epsilon kappa mu : ℝ) (mesh : Fin K → ℝ)
    (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row) (hr : 0 < r) (hr1 : r ≤ 1)
    (hloss : 0 ≤ loss) (hd : 0 ≤ d) (hmetric : 0 ≤ metric) (hepsilon : 0 ≤ epsilon)
    (hLip : metric ≤ r^(-2*epsilon)) (hmesh : ∀j,0 < mesh j) (hrmu : r ≤ mu)
    (hHeight : ((8*R0:ℕ):ℝ) ≤ 1280*mu^(-2*epsilon)) :
    (newCutCharge K Ksupport normal g R0 meshConstant row r loss d metric kappa mesh:ℝ) ≤
      fixedFactor K Ksupport g meshConstant row*r^(-newExponent K epsilon loss d) := by
  have hCoh := coherenceCharge_bound K normal g hnormal meshConstant row r loss d metric epsilon kappa mesh
    hC hrow hr hr1 hloss hd hmetric hepsilon hLip hmesh
  have hHeightR : ((8*R0:ℕ):ℝ) ≤ 1280*r^(-2*epsilon) := hHeight.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr hrmu
      (show -2*epsilon ≤ 0 by linarith only [hepsilon])) (by norm_num))
  have hA : 0 ≤ offsetCoefficient 4 g meshConstant row := by unfold offsetCoefficient; positivity
  have hp := mul_le_mul hCoh hHeightR (Nat.cast_nonneg _) (by positivity)
  have he : r^(-(4*(K:ℝ)*epsilon+(K:ℝ)*(loss+9*d)))*r^(-2*epsilon)=
      r^(-newExponent K epsilon loss d) := by
    rw [←Real.rpow_add hr]
    congr 1
    unfold newExponent
    ring
  unfold newCutCharge
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_mul]
  calc
    _ ≤ (((144:ℝ)^K*(offsetCoefficient 4 g meshConstant row+1)^K*
        r^(-(4*(K:ℝ)*epsilon+(K:ℝ)*(loss+9*d))))*(1280*r^(-2*epsilon)))*
        ((53^(4*Ksupport):ℕ):ℝ)*((8^4:ℕ):ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = fixedFactor K Ksupport g meshConstant row*
        (r^(-(4*(K:ℝ)*epsilon+(K:ℝ)*(loss+9*d)))*r^(-2*epsilon)) := by
      unfold fixedFactor
      push_cast
      ring
    _ = _ := by rw [he]

/-- The actual middle-scale bounds imply the finer working mesh is at least
the original stop radius. No comparison is imposed on the chosen R0. -/
lemma stop_radius_le_mesh (m : ℕ) (r : ℝ)
    (hsmall : (64:ℝ)/((2^m:ℕ):ℝ) ≤ 1)
    (hstop : 3072*r ≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2) :
    r ≤ ((64:ℝ)/((2^m:ℕ):ℝ))/64 := by
  have hpos : 0 ≤ (64:ℝ)/((2^m:ℕ):ℝ) := by positivity
  have hsq : ((64:ℝ)/((2^m:ℕ):ℝ))^2 ≤ (64:ℝ)/((2^m:ℕ):ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hsmall hpos
    nlinarith only [hh]
  nlinarith only [hstop,hsq,hpos]

/-- Actual prepared depths and the actual base height allowance supply the
new-cut estimate directly. K and Ksupport precede epsilon and source choices;
g appears only in the fixed coefficient, not in the number of rounds. -/
theorem source_new_cut_cost (K Ksupport normal g R0 m : ℕ) (hnormal : normal ≤ 4)
    (meshConstant row r loss d metric epsilon kappa : ℝ) (depths : Fin K → ℕ)
    (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row) (hr : 0 < r) (hr1 : r ≤ 1)
    (hloss : 0 ≤ loss) (hd : 0 ≤ d) (hmetric : 0 ≤ metric) (hepsilon : 0 ≤ epsilon)
    (hLip : metric ≤ r^(-2*epsilon))
    (hsmall : (64:ℝ)/((2^m:ℕ):ℝ) ≤ 1)
    (hstop : 3072*r ≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2)
    (hHeight : ((8*R0:ℕ):ℝ) ≤ 1280*(((64:ℝ)/((2^m:ℕ):ℝ))/64)^(-2*epsilon)) :
    (newCutCharge K Ksupport normal g R0 meshConstant row r loss d metric kappa
      (fun j => 64/((2^(depths j):ℕ):ℝ)):ℝ) ≤
        fixedFactor K Ksupport g meshConstant row*r^(-newExponent K epsilon loss d) :=
  newCutCharge_bound K Ksupport normal g R0 hnormal meshConstant row r loss d metric epsilon kappa
    (((64:ℝ)/((2^m:ℕ):ℝ))/64) (fun j => 64/((2^(depths j):ℕ):ℝ))
    hC hrow hr hr1 hloss hd hmetric hepsilon hLip (fun _ => by positivity)
    (stop_radius_le_mesh m r hsmall hstop) hHeight

end NativeActualNewCutBudget
