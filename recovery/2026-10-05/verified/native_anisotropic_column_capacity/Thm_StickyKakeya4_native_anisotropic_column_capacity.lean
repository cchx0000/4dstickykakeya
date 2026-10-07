import Theorems.Thm_StickyKakeya4_native_anisotropic_column_menus

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2800000

noncomputable section
namespace NativeAnisotropicColumnCapacity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeSpatialAngularGeometry
open NativeAnisotropicShortRowGeometry NativeAnisotropicColumnMenus
open scoped BigOperators

/-- Possible original sigma-height labels in one column of raw height T*sigma. -/
def heightMenu (T : ℕ) (r : ℤ) : Finset ℤ :=
  Icc (r-((T+1:ℕ):ℤ)) (r+((T+1:ℕ):ℤ))

lemma heightMenu_card (T : ℕ) (r : ℤ) : (heightMenu T r).card=2*T+3 := by
  have hh : ((heightMenu T r).card:ℤ)=2*(T:ℤ)+3 := by
    unfold heightMenu
    rw [Int.card_Icc_of_le _ _ (by omega)]
    push_cast
    ring
  exact_mod_cast hh

lemma same_column_height_mem_menu {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N K T : ℕ) (hK : 0 < K) (hT : 0 < T) (p : Parent)
    (H : ℝ) (hH : H=(T:ℝ)*(64/(K:ℝ))) (k l : Index)
    (hcol : columnLabel D a N p (64/(K:ℝ)) H k=
      columnLabel D a N p (64/(K:ℝ)) H l) :
    spatialLabel D K k (3:Fin 4)∈heightMenu T (spatialLabel D K l (3:Fin 4)) := by
  have hσ : (0:ℝ)<64/(K:ℝ) := by positivity
  have hHp : 0 < H := by rw [hH]; positivity
  have hh := same_column_height_close D a N p (64/(K:ℝ)) H hHp k l hcol
  change ⌊cellCenter (mesh D) k (3:Fin 4)/(64/(K:ℝ))⌋∈
    Icc (⌊cellCenter (mesh D) l (3:Fin 4)/(64/(K:ℝ))⌋-((T+1:ℕ):ℤ))
      (⌊cellCenter (mesh D) l (3:Fin 4)/(64/(K:ℝ))⌋+((T+1:ℕ):ℤ))
  apply floor_mem_interval T
  rw [←sub_div,abs_div,abs_of_pos hσ]
  apply (div_le_iff₀ hσ).mpr
  simpa only [hH] using hh

/-- A fixed original height bin in one column fits in an eleven-by-eleven-by-eleven
box of original spatial labels. The fourth label stays exactly fixed. -/
lemma same_column_same_height_mem_halo {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p)
    (H : ℝ) (k l : Index)
    (hcol : columnLabel D a N p (64/(K:ℝ)) H k=
      columnLabel D a N p (64/(K:ℝ)) H l)
    (ht : spatialLabel D K k (3:Fin 4)=spatialLabel D K l (3:Fin 4)) :
    spatialLabel D K k∈columnHalo 5 0 (spatialLabel D K l) := by
  have hσ : (0:ℝ)<64/(K:ℝ) := by positivity
  apply Fintype.mem_piFinset.mpr
  intro v
  refine Fin.lastCases ?_ (fun v => ?_) v
  · simp only [show (Fin.last 3:Fin 4)=3 by rfl,if_true,
      Nat.cast_zero,sub_zero,add_zero,mem_Icc]
    exact ⟨ht.ge,ht.le⟩
  · have hv : v.castSucc≠(3:Fin 4) := Fin.castSucc_ne_last v
    simp only [if_neg hv]
    change ⌊cellCenter (mesh D) k v.castSucc/(64/(K:ℝ))⌋∈
      Icc (⌊cellCenter (mesh D) l v.castSucc/(64/(K:ℝ))⌋-5)
        (⌊cellCenter (mesh D) l v.castSucc/(64/(K:ℝ))⌋+5)
    apply floor_mem_interval 4
    rw [←sub_div,abs_div,abs_of_pos hσ]
    apply (div_le_iff₀ hσ).mpr
    exact same_column_same_height_spatial_close h N K hN hK p i hp H k l hcol ht v

/-- This geometric capacity counts distinct ORIGINAL raw vertices, without an
incidence, shading, or admissibility hypothesis on the point set. -/
theorem column_height_fiber_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p)
    (H : ℝ) (S : Finset Index) (q : Index)
    (hcol : ∀k∈S,columnLabel D a N p (64/(K:ℝ)) H k=q) (t : ℤ) :
    ((S.image (spatialLabel D K)).filter (fun v => v (3:Fin 4)=t)).card ≤ 1331 := by
  let V := (S.image (spatialLabel D K)).filter (fun v => v (3:Fin 4)=t)
  by_cases hV : V.Nonempty
  · obtain ⟨v,hv⟩ := hV
    obtain ⟨hvS,hvt⟩ := mem_filter.mp hv
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hvS
    have hsub : V⊆columnHalo 5 0 (spatialLabel D K l) := by
      intro w hw
      obtain ⟨hwS,hwt⟩ := mem_filter.mp hw
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hwS
      exact same_column_same_height_mem_halo h N K hN hK p i hp H k l
        ((hcol k hk).trans (hcol l hl).symm) (hwt.trans hvt.symm)
    have hh := card_le_card hsub
    rw [columnHalo_card] at hh
    norm_num at hh
    exact hh
  · have he : V=∅ := not_nonempty_iff_eq_empty.mp hV
    change V.card ≤ 1331
    rw [he]
    simp

/-- The exact finite menu bound is 1331 times the 2*T+3 possible raw heights. -/
theorem column_vertices_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N K T : ℕ)
    (hN : 0 < N) (hK : 0 < K) (hT : 0 < T)
    (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p)
    (H : ℝ) (hH : H=(T:ℝ)*(64/(K:ℝ))) (S : Finset Index) (q : Index)
    (hcol : ∀k∈S,columnLabel D a N p (64/(K:ℝ)) H k=q) :
    (S.image (spatialLabel D K)).card ≤ 1331*(2*T+3) := by
  by_cases hS : S.Nonempty
  · obtain ⟨l,hl⟩ := hS
    have hm : ∀v∈S.image (spatialLabel D K),
        v (3:Fin 4)∈heightMenu T (spatialLabel D K l (3:Fin 4)) := by
      intro v hv
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
      exact same_column_height_mem_menu D a N K T hK hT p H hH k l
        ((hcol k hk).trans (hcol l hl).symm)
    have hh := card_le_mul_card_image_of_maps_to hm 1331
      (fun t _ => column_height_fiber_card_le h N K hN hK p i hp H S q hcol t)
    simpa only [heightMenu_card] using hh
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp

/-- For positive integer T, one anisotropic column contains at most6655*T
distinct original sigma-vertices. -/
theorem column_vertices_card_le_mul {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N K T : ℕ)
    (hN : 0 < N) (hK : 0 < K) (hT : 0 < T)
    (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p)
    (H : ℝ) (hH : H=(T:ℝ)*(64/(K:ℝ))) (S : Finset Index) (q : Index)
    (hcol : ∀k∈S,columnLabel D a N p (64/(K:ℝ)) H k=q) :
    (S.image (spatialLabel D K)).card ≤ 6655*T := by
  have hh := column_vertices_card_le h N K T hN hK hT p i hp H hH S q hcol
  omega

lemma dyadic_height_eq (m f : ℕ) (hmf : m ≤ f) :
    64/((2^m:ℕ):ℝ)=((2^(f-m):ℕ):ℝ)*(64/((2^f:ℕ):ℝ)) := by
  have hp : (2^f:ℕ)=2^m*2^(f-m) := by
    rw [←Nat.pow_add,Nat.add_sub_of_le hmf]
  rw [hp,Nat.cast_mul]
  field_simp

theorem dyadic_column_vertices_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m f : ℕ) (hmf : m ≤ f)
    (p : Parent) (i : Fin n) (hp : parentLabel D a (2^m) i=p)
    (S : Finset Index) (q : Index)
    (hcol : ∀k∈S,columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ))
      (64/((2^m:ℕ):ℝ)) k=q) :
    (S.image (spatialLabel D (2^f))).card ≤ 6655*2^(f-m) := by
  exact column_vertices_card_le_mul h (2^m) (2^f) (2^(f-m))
    (by positivity) (by positivity) (by positivity) p i hp _
    (dyadic_height_eq m f hmf) S q hcol

end NativeAnisotropicColumnCapacity
