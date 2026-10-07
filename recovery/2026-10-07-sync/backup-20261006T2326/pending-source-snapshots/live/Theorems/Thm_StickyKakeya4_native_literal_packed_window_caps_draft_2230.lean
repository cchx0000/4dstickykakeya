import Theorems.Thm_StickyKakeya4_native_compact_source_coordinate_caps_draft_2218
import Theorems.Thm_StickyKakeya4_native_quantized_line_packets
import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_geometry

/- UNVERIFIED literal native-cell / packed lower-XY window capacities.
Both keys use the same native physical time floor. The field is only
evaluated at occupied original native heights, and variation is required
only inside the queried time bin. No parent-normalized source is used.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeLiteralPackedWindowCapsDraft2230
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeConfiguredLowerQuotientReadback NativePackedHigherCapacityDraft2006
open NativeCompactSourceCoordinateCapsDraft2218 NativeCubicalIncidenceCounts
open NativeCubicalDiameterCount NativeQuantizedLinePackets NativeMatchedShadowConfiguredGeometry

def physicalKey (mu r : ℝ) (k : Index) : Index := wzDyadicCellIndex r (cellCenter mu k)

def lowerXYKey (mu r : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4)
    (F : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (k : Index) : Index :=
  let x := O (cellCenter mu k)
  ![⌊x 0/r⌋,⌊lowerQuotient (F (k 3)) x 0/r⌋,
    ⌊lowerQuotient (F (k 3)) x 1/r⌋,physicalKey mu r k 3]

lemma lowerXYKey_normal (mu r : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4)
    (F : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (k : Index) (j : Fin 2) :
    lowerXYKey mu r O F k j.castSucc.succ=
      ⌊lowerQuotient (F (k 3)) (O (cellCenter mu k)) j/r⌋ := by
  fin_cases j <;> rfl

def menuRadius (L : ℝ) : ℕ := ⌈8+28*L⌉₊

/-- In one exact XY window, the triangular inverse and the actual height
coordinate give distance at most(4+14L)r in the original Euclidean chart. -/
theorem same_XY_distance (mu r L : ℝ) (hr : 0<r) (hL : 0≤L)
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4,O x 3=x 3)
    (F : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (k l : Index)
    (hF : ∀j,|F (k 3) j 0|≤1/4) (hl : ‖cellCenter mu l‖≤7)
    (hLip : ∀j,|F (k 3) j 0-F (l 3) j 0|≤L*r)
    (he : lowerXYKey mu r O F k=lowerXYKey mu r O F l) :
    dist (cellCenter mu k) (cellCenter mu l)≤(4+14*L)*r := by
  let x := O (cellCenter mu k)
  let y := O (cellCenter mu l)
  have hx : |x 0-y 0|≤r := floor_equal_abs_le r hr _ _ (congrFun he 0)
  have hy0 : |y 0|≤7 := by
    have hh := PiLp.norm_apply_le y 0
    have hny : ‖y‖≤7 := by simpa only [y,O.norm_map] using hl
    exact (show |y 0|≤‖y‖ by simpa only [Real.norm_eq_abs] using hh).trans hny
  have hq (j : Fin 2) : |lowerQuotient (F (k 3)) x j-lowerQuotient (F (l 3)) y j|≤r := by
    apply floor_equal_abs_le r hr
    simpa only [lowerXYKey_normal] using congrFun he j.castSucc.succ
  have hn (j : Fin 2) : |x j.castSucc.succ-y j.castSucc.succ|≤(2+7*L)*r := by
    have hid : x j.castSucc.succ-y j.castSucc.succ=
        (lowerQuotient (F (k 3)) x j-lowerQuotient (F (l 3)) y j)+
          F (k 3) j 0*(x 0-y 0)+(F (k 3) j 0-F (l 3) j 0)*y 0 := by
      dsimp only [lowerQuotient]
      ring
    have h1 := abs_add_le
      (lowerQuotient (F (k 3)) x j-lowerQuotient (F (l 3)) y j) (F (k 3) j 0*(x 0-y 0))
    have h2 := abs_add_le
      ((lowerQuotient (F (k 3)) x j-lowerQuotient (F (l 3)) y j)+F (k 3) j 0*(x 0-y 0))
      ((F (k 3) j 0-F (l 3) j 0)*y 0)
    have h3 := mul_le_mul (hF j) hx (abs_nonneg _) (by norm_num : (0:ℝ)≤1/4)
    have h4 := mul_le_mul (hLip j) hy0 (abs_nonneg _) (mul_nonneg hL hr.le)
    simp only [abs_mul] at h1 h2
    rw [hid]
    nlinarith only [h1,h2,h3,h4,hq j,hr]
  have ht : |x 3-y 3|≤r := by
    have hh := congrFun he 3
    change physicalKey mu r k 3=physicalKey mu r l 3 at hh
    dsimp only [x,y]
    rw [hO,hO]
    exact floor_equal_abs_le r hr _ _ hh
  have hCoords : ∀v : Fin 4,|x v-y v|≤(2+7*L)*r := by
    intro v
    fin_cases v
    · change |x 0-y 0|≤_
      nlinarith only [hx,hL,hr]
    · exact hn 0
    · exact hn 1
    · change |x 3-y 3|≤_
      nlinarith only [ht,hL,hr]
  have hh := distance_of_coordinates x y ((2+7*L)*r) (by positivity) hCoords
  have hh' : dist x y≤(4+14*L)*r := hh.trans_eq (by ring)
  simpa only [x,y,O.dist_map] using hh'

/-- One physical window gives bounded change in every packed XY
coordinate. The field difference is multiplied by the actual norm7 bound. -/
theorem same_physical_XY_neighbor (mu r L : ℝ) (hr : 0<r) (hL : 0≤L)
    (O : E4 ≃ₗᵢ[ℝ] E4) (F : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (k l : Index)
    (hF : ∀j,|F (k 3) j 0|≤1/4) (hl : ‖cellCenter mu l‖≤7)
    (hLip : ∀j,|F (k 3) j 0-F (l 3) j 0|≤L*r)
    (he : physicalKey mu r k=physicalKey mu r l) :
    lowerXYKey mu r O F k∈indexBox (lowerXYKey mu r O F l) (menuRadius L) := by
  let x := O (cellCenter mu k)
  let y := O (cellCenter mu l)
  have hDist : dist x y≤2*r := by
    rw [O.dist_map]
    exact distance_of_coordinates _ _ r hr.le (fun v => floor_equal_abs_le r hr _ _ (congrFun he v))
  have hCoord (v : Fin 4) : |x v-y v|≤2*r :=
    (show _≤dist x y by simpa only [Real.dist_eq] using PiLp.dist_apply_le x y v).trans hDist
  have hy0 : |y 0|≤7 := by
    have hh := PiLp.norm_apply_le y 0
    have hny : ‖y‖≤7 := by simpa only [y,O.norm_map] using hl
    exact (show |y 0|≤‖y‖ by simpa only [Real.norm_eq_abs] using hh).trans hny
  have hq (j : Fin 2) : |lowerQuotient (F (k 3)) x j-lowerQuotient (F (l 3)) y j|≤(3+7*L)*r := by
    have hid : lowerQuotient (F (k 3)) x j-lowerQuotient (F (l 3)) y j=
        (x j.castSucc.succ-y j.castSucc.succ)-F (k 3) j 0*(x 0-y 0)-
          (F (k 3) j 0-F (l 3) j 0)*y 0 := by dsimp only [lowerQuotient]; ring
    have h1 := abs_sub (x j.castSucc.succ-y j.castSucc.succ) (F (k 3) j 0*(x 0-y 0))
    have h2 := abs_sub ((x j.castSucc.succ-y j.castSucc.succ)-F (k 3) j 0*(x 0-y 0))
      ((F (k 3) j 0-F (l 3) j 0)*y 0)
    have h3 := mul_le_mul (hF j) (hCoord 0) (abs_nonneg _) (by norm_num : (0:ℝ)≤1/4)
    have h4 := mul_le_mul (hLip j) hy0 (abs_nonneg _) (mul_nonneg hL hr.le)
    simp only [abs_mul] at h1 h2
    rw [hid]
    nlinarith only [h1,h2,h3,h4,hCoord j.castSucc.succ,hr]
  have hK : 8+28*L≤(menuRadius L:ℝ) := Nat.le_ceil _
  have hFwd : (3+7*L)*r≤(menuRadius L:ℝ)*r := by nlinarith only [hK,hL,hr]
  have hTwo : 2*r≤(menuRadius L:ℝ)*r := by nlinarith only [hK,hL,hr]
  have hFloor (u v : ℝ) (huv : |u-v|≤(menuRadius L:ℝ)*r) :
      ⌊u/r⌋∈Icc (⌊v/r⌋-(menuRadius L:ℤ)) (⌊v/r⌋+menuRadius L) := by
    apply floor_mem_interval
    rw [←sub_div,abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr huv
  apply Fintype.mem_piFinset.mpr
  intro v
  fin_cases v
  · exact hFloor _ _ ((hCoord 0).trans hTwo)
  · exact hFloor _ _ ((hq 0).trans hFwd)
  · exact hFloor _ _ ((hq 1).trans hFwd)
  · change physicalKey mu r k 3∈Icc _ _
    rw [congrFun he 3]
    exact mem_Icc.mpr ⟨by omega,by omega⟩

/-- The inverse native physical window has the same fixed grid halo. -/
theorem same_XY_physical_neighbor (mu r L : ℝ) (hr : 0<r) (hL : 0≤L)
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4,O x 3=x 3)
    (F : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (k l : Index)
    (hF : ∀j,|F (k 3) j 0|≤1/4) (hl : ‖cellCenter mu l‖≤7)
    (hLip : ∀j,|F (k 3) j 0-F (l 3) j 0|≤L*r)
    (he : lowerXYKey mu r O F k=lowerXYKey mu r O F l) :
    physicalKey mu r k∈indexBox (physicalKey mu r l) (menuRadius L) := by
  have hDist := same_XY_distance mu r L hr hL O hO F k l hF hl hLip he
  have hK : 8+28*L≤(menuRadius L:ℝ) := Nat.le_ceil _
  have hBound : (4+14*L)*r≤(menuRadius L:ℝ)*r := by nlinarith only [hK,hL,hr]
  apply Fintype.mem_piFinset.mpr
  intro v
  apply floor_mem_interval
  rw [←sub_div,abs_div,abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  exact ((show |cellCenter mu k v-cellCenter mu l v|≤dist (cellCenter mu k) (cellCenter mu l) by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le (cellCenter mu k) (cellCenter mu l) v).trans hDist).trans hBound

lemma image_fiber_count (P : Finset Index) (f g : Index → Index) (K : ℕ)
    (hNear : ∀k∈P,∀l∈P,f k=f l → g k∈indexBox (g l) K) (v : Index) :
    ((P.filter (fun k => f k=v)).image g).card≤(2*K+1)^4 := by
  let S := P.filter (fun k => f k=v)
  by_cases hn : S.Nonempty
  · obtain ⟨l,hl⟩ := hn
    have hSub : S.image g⊆indexBox (g l) K := by
      intro q hq
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hq
      exact hNear k (mem_filter.mp hk).1 l (mem_filter.mp hl).1
        ((mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm)
    exact (card_le_card hSub).trans_eq (by rw [indexBox_card])
  · simp only [not_nonempty_iff_eq_empty.mp hn,image_empty,card_empty,Nat.zero_le]

/-- Actual source-facing two-way capacities, on the SAME native points.
The norm7 bound is derived from the compact native source internally.
Only the actual occupied-height field and its within-bin variation remain
geometric inputs, with every cost displayed through menuRadius L. -/
theorem actual_source_window_capacities {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (hK : ∀i,D.line i∈NativeUnitParentNormalization.fixedCompactClass)
    (cells : Fin n → Finset Index) (hCells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences cells)
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4,O x 3=x 3)
    (F : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (r L : ℝ) (hr : 0<r) (hL : 0≤L)
    (hF : ∀k∈E.image Prod.snd,∀j,|F (k 3) j 0|≤1/4)
    (hLip : ∀k∈E.image Prod.snd,∀l∈E.image Prod.snd,
      physicalKey (mesh D) r k 3=physicalKey (mesh D) r l 3 →
        ∀j,|F (k 3) j 0-F (l 3) j 0|≤L*r) :
    (∀v : Index,(((E.image Prod.snd).filter (fun k => lowerXYKey (mesh D) r O F k=v)).image
      (physicalKey (mesh D) r)).card≤(2*menuRadius L+1)^4) ∧
    (∀v : Index,(((E.image Prod.snd).filter (fun k => physicalKey (mesh D) r k=v)).image
      (lowerXYKey (mesh D) r O F)).card≤(2*menuRadius L+1)^4) := by
  have hNorm := original_cell_center_norm h hK cells hCells E hE
  constructor
  · intro v
    apply image_fiber_count
    intro k hk l hl he
    have ht : physicalKey (mesh D) r k 3=physicalKey (mesh D) r l 3 := congrFun he 3
    exact same_XY_physical_neighbor (mesh D) r L hr hL O hO F k l
      (hF k hk) (hNorm l hl) (hLip k hk l hl ht) he
  · intro v
    apply image_fiber_count
    intro k hk l hl he
    exact same_physical_XY_neighbor (mesh D) r L hr hL O F k l
      (hF k hk) (hNorm l hl) (hLip k hk l hl (congrFun he 3)) he

end NativeLiteralPackedWindowCapsDraft2230
