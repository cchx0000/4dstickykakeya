import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu
import Theorems.Thm_StickyKakeya4_native_original_point_angular_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8500000

noncomputable section
namespace NativeNestedParentPhysicalMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentGeometry NativeLocalParentPhysicalMap
open NativeNormalizedCellRelativeMenu NativeAnisotropicShortRowGeometry NativeContractedUnitParent
open NativeSpatialAngularGeometry NativeNormalizedCellAngularMenu NativeOriginalPointAngularLower
open NativeRelativeCoarseGeometry

/-- Exact affine change between two nested ORIGINAL phase-parent charts.
The common height is unchanged; only the horizontal coordinates rescale. -/
def rebase (R : ℕ) (p q : Parent) (x : E4) : E4 :=
  ActualSlopeSource.heightPoint (WithLp.toLp 2 (fun j : Fin 3 =>
    (R:ℝ)*x j.castSucc+((R:ℝ)*(p.1 j:ℝ)-(q.1 j:ℝ))*x (3:Fin 4)+
      ((R:ℝ)*(p.2 j:ℝ)-(q.2 j:ℝ))/128)) (x (3:Fin 4))

theorem physical_rebase {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N R : ℕ) (p q : Parent) (x : E4) :
    physicalMap D a (R*N) q x=rebase R p q (physicalMap D a N p x) := by
  ext v
  refine Fin.lastCases ?_ (fun j => ?_) v
  · simp only [NativeLocalParentPhysicalMap.physicalMap,NativeLocalParentPhysicalMap.baseMap,contractPoint,rebase,ActualSlopeSource.heightPoint_last,
      PiLp.smul_apply,smul_eq_mul,show (3:Fin 4)=Fin.last 3 by rfl]
  · simp only [NativeLocalParentPhysicalMap.physicalMap,NativeLocalParentPhysicalMap.baseMap,contractPoint,rebase,ActualSlopeSource.heightPoint_castSucc,
      show (3:Fin 4)=Fin.last 3 by rfl,ActualSlopeSource.heightPoint_last,
      PiLp.smul_apply,smul_eq_mul,Nat.cast_mul]
    ring

/-- For an occupied descendant, the shear coefficient is at most the
scale ratio. This follows from the actual parent slope labels. -/
theorem parent_shear_bound {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N R : ℕ) (hR : 0< R) (p q : Parent) (i : Fin n)
    (hp : parentLabel D a N i=p) (hq : parentLabel D a (R*N) i=q) (j : Fin 3) :
    |(R:ℝ)*(p.1 j:ℝ)-(q.1 j:ℝ)|≤ R := by
  have hOuter := (parameter_box D a N p i hp).1 j
  have hInner := (parameter_box D a (R*N) q i hq).1 j
  have hR1 : (1:ℝ)≤ R := by exact_mod_cast hR
  have hid : (R:ℝ)*(p.1 j:ℝ)-(q.1 j:ℝ)=
      localSlope D (R*N) q i j-(R:ℝ)*localSlope D N p i j := by
    simp only [localSlope,Nat.cast_mul]
    ring
  rw [hid]
  have hmul0 := mul_nonneg (Nat.cast_nonneg R) hOuter.1
  have hmul1 := mul_le_mul_of_nonneg_left hOuter.2.le (Nat.cast_nonneg R)
  exact abs_le.mpr ⟨by nlinarith only [hInner.1,hmul1],by nlinarith only [hInner.2,hmul0,hR1]⟩

theorem rebase_coordinate_bound (R : ℕ) (hR : 0< R) (p q : Parent)
    (hShear : ∀j,|(R:ℝ)*(p.1 j:ℝ)-(q.1 j:ℝ)|≤ R)
    (x y : E4) (rho : ℝ) (hrho : 0≤ rho) (hxy : ∀v,|x v-y v|≤ rho) (v : Fin 4) :
    |rebase R p q x v-rebase R p q y v|≤ 2*(R:ℝ)*rho := by
  have hR1 : (1:ℝ)≤ R := by exact_mod_cast hR
  refine Fin.lastCases ?_ (fun j => ?_) v
  · have hh := hxy (3:Fin 4)
    change |x (3:Fin 4)-y (3:Fin 4)|≤ 2*(R:ℝ)*rho
    nlinarith only [hh,hR1,hrho]
  · have hid : rebase R p q x j.castSucc-rebase R p q y j.castSucc=
        (R:ℝ)*(x j.castSucc-y j.castSucc)+
          ((R:ℝ)*(p.1 j:ℝ)-(q.1 j:ℝ))*(x (3:Fin 4)-y (3:Fin 4)) := by
      simp only [rebase,ActualSlopeSource.heightPoint_castSucc]
      ring
    rw [hid]
    have h1 : |(R:ℝ)*(x j.castSucc-y j.castSucc)|≤ (R:ℝ)*rho := by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg R)]
      exact mul_le_mul_of_nonneg_left (hxy j.castSucc) (Nat.cast_nonneg R)
    have h2 : |((R:ℝ)*(p.1 j:ℝ)-(q.1 j:ℝ))*(x (3:Fin 4)-y (3:Fin 4))|≤ (R:ℝ)*rho := by
      rw [abs_mul]
      exact mul_le_mul (hShear j) (hxy 3) (abs_nonneg _) (Nat.cast_nonneg R)
    have hh := (abs_add_le _ _).trans (add_le_add h1 h2)
    linarith only [hh]

/-- The source-independent finite menu of inner physical cells meeting
one outer physical cell. Its size does not depend on rho, sigma or D. -/
def innerMenu (R M M' : ℕ) (p q : Parent) (z : Index) : Finset Index :=
  columnHalo 3 3 (wzDyadicCellIndex (64/(M':ℝ))
    (rebase R p q (cellCenter (64/(M:ℝ)) z)))

lemma innerMenu_card (R M M' : ℕ) (p q : Parent) (z : Index) :
    (innerMenu R M M' p q z).card=7^4 := by
  rw [innerMenu,columnHalo_card]
  norm_num

theorem physical_cell_mem_innerMenu {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N R M M' : ℕ) (hR : 0< R) (hM : 0< M) (hM' : 0< M')
    (hwidth : (64:ℝ)/(M':ℝ)=(R:ℝ)*(64/(M:ℝ)))
    (p q : Parent) (i : Fin n) (hp : parentLabel D a N i=p)
    (hq : parentLabel D a (R*N) i=q) (k : Index) :
    physicalCell D a (R*N) M' q k∈innerMenu R M M' p q (physicalCell D a N M p k) := by
  have hw : (0:ℝ)< 64/(M:ℝ) := by positivity
  have hw' : (0:ℝ)< 64/(M':ℝ) := by positivity
  have hPoint : physicalPoint D a (R*N) q k=rebase R p q (physicalPoint D a N p k) :=
    physical_rebase D a N R p q _
  have hxy (v : Fin 4) : |physicalPoint D a N p k v-
      cellCenter (64/(M:ℝ)) (physicalCell D a N M p k) v|≤ 64/(M:ℝ) := by
    have hh := cell_center_coordinate_error hw (physicalPoint D a N p k) v
    rw [abs_sub_comm] at hh
    exact hh.trans (by linarith only [hw])
  have hBound (v : Fin 4) : |physicalPoint D a (R*N) q k v-
      rebase R p q (cellCenter (64/(M:ℝ)) (physicalCell D a N M p k)) v|≤ 2*(64/(M':ℝ)) := by
    rw [hPoint,hwidth]
    simpa only [mul_assoc] using rebase_coordinate_bound R hR p q (parent_shear_bound D a N R hR p q i hp hq)
      _ _ _ hw.le hxy v
  apply Fintype.mem_piFinset.mpr
  intro v
  simp only [ite_self]
  change ⌊physicalPoint D a (R*N) q k v/(64/(M':ℝ))⌋∈
    Icc (⌊rebase R p q (cellCenter (64/(M:ℝ)) (physicalCell D a N M p k)) v/(64/(M':ℝ))⌋-3)
      (⌊rebase R p q (cellCenter (64/(M:ℝ)) (physicalCell D a N M p k)) v/(64/(M':ℝ))⌋+3)
  apply floor_mem_interval 2
  rw [←sub_div,abs_div,abs_of_pos hw']
  exact (div_le_iff₀ hw').mpr (hBound v)

/-- The standard finest angular grid is unchanged by nested-parent
normalization, up to an injective integer translation. -/
theorem angular_image_global_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m s : ℕ) (hs : 3≤ s) (p : Parent) (E : Finset (Fin n × Index)) :
    (E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card=
      (E.image (fun z => (parentLabel D a (2^(m+s-3)) z.1).1)).card := by
  have hid : E.image (fun z => angularCell D (2^m) (2^s) p z.1)=
      (E.image (fun z => (parentLabel D a (2^(m+s-3)) z.1).1)).image (translateAngle p s) := by
    rw [image_image]
    apply image_congr
    intro z _hz
    exact angular_global_readback D a m s hs p z.1
  rw [hid]
  exact card_image_of_injective _ (translateAngle_injective p s)

theorem nested_angular_image_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m s t : ℕ) (ht : 6≤ t) (hts : t≤ s) (p q : Parent) (E : Finset (Fin n × Index)) :
    (E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card=
      (E.image (fun z => angularCell D (2^(m+t-6)) (2^(s-t+6)) q z.1)).card := by
  rw [angular_image_global_card D a m s (by omega) p E,
    angular_image_global_card D a (m+t-6) (s-t+6) (by omega) q E]
  have he : (m+t-6)+(s-t+6)-3=m+s-3 := by omega
  rw [he]

end NativeNestedParentPhysicalMenu
