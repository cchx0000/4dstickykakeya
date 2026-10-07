import Theorems.Thm_StickyKakeya4_native_actual_higher_remembered_caller_construction_draft_2100
import Theorems.Thm_StickyKakeya4_native_coarse_representative_geometry

/- UNVERIFIED actual-source time and tangent-grid capacities.
All points below are ORIGINAL cell centers of a native source in the fixed
compact tube class. The packed isometry is evaluated only inside the key.
Thus the bounds remove the time-count and global-X-cap inputs of the
same-source higher population readers without rotating a cubical source.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeCompactSourceCoordinateCapsDraft2218
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalIncidenceCounts NativeTangentGridCoarsening NativePackedHigherCapacityDraft2006
open NativeUnitParentNormalization NativeCoarseRepresentativeGeometry

/-- A genuine tube point in the fixed compact source has a uniform norm
bound. Its actual marked-segment witness supplies this bound directly. -/
theorem compact_tube_point_norm {line : MarkedLine} (hv : IsValidLine line)
    (hK : line∈fixedCompactClass) {delta : ℝ} (hd : 0<delta) (hd1 : delta≤1)
    {x : E4} (hx : x∈markedUnitTube line delta) : ‖x‖≤7 := by
  obtain ⟨t,ht,hDist⟩ := exists_rawFrontParam_dist_lt_of_infDist_le line x hx hd
  obtain ⟨hMark,hOffset⟩ := compact_mark_offset hK
  have hTime : |t|≤(1/2:ℝ) := abs_le.mpr ht
  have hFront : ‖rawFrontParam (line,t)‖≤(9/2:ℝ) := by
    calc
      _ ≤ ‖offset line‖+‖(mark line+t) • direction line‖ := norm_add_le _ _
      _ = ‖offset line‖+|mark line+t| := by rw [norm_smul,Real.norm_eq_abs,hv.1,mul_one]
      _ ≤ ‖offset line‖+(|mark line|+|t|) := add_le_add_left (abs_add_le _ _) _
      _ ≤ 9/2 := by linarith only [hMark,hOffset,hTime]
  have hTri := norm_add_le (x-rawFrontParam (line,t)) (rawFrontParam (line,t))
  rw [sub_add_cancel] at hTri
  rw [dist_eq_norm] at hDist
  linarith only [hTri,hDist,hFront,hd1]

/-- Every retained literal cell center inherits the actual tube point
bound; neither deduplicated mass nor a new point presentation is used. -/
theorem original_cell_center_norm {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (cells : Fin n → Finset Index) (hCells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences cells)
    (k : Index) (hk : k∈E.image Prod.snd) : ‖cellCenter (mesh D) k‖≤7 := by
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
  have hzCell := (mem_incidences cells z.1 z.2).mp (hE hz)
  have hShade : cellCenter (mesh D) z.2∈D.shading z.1 := by
    rw [hCells]
    exact Set.mem_iUnion.mpr ⟨z.2,Set.mem_iUnion.mpr
      ⟨hzCell,cellCenter_mem (half_pos h.1.2.1) z.2⟩⟩
  exact compact_tube_point_norm (h.1.2.2.2.2.1 z.1) (hK z.1) h.1.2.1 h.1.2.2.1
    (h.1.2.2.2.2.2.2.2.2.1 z.1 hShade)

/-- The actual original native height alphabet contains at most32/sigma
values. The proof uses the exact floor of its cell center, not a translated
or packed height identification. -/
theorem native_height_count {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (cells : Fin n → Finset Index) (hCells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences cells) :
    (((E.image Prod.snd).image (fun k => k 3)).card:ℝ)≤32/D.thickness := by
  let P := E.image Prod.snd
  have hd := h.1.2.1
  have hm : 0<mesh D := half_pos hd
  have hBound : ∀k∈P,(-7:ℝ)≤cellCenter (mesh D) k 3 ∧ cellCenter (mesh D) k 3≤ -7+14 := by
    intro k hk
    have hc := (PiLp.norm_apply_le (cellCenter (mesh D) k) 3).trans
      (original_cell_center_norm h hK cells hCells E hE k hk)
    have hc' : |cellCenter (mesh D) k 3|≤7 := by simpa only [Real.norm_eq_abs] using hc
    simpa only [show (-7:ℝ)+14=7 by norm_num] using abs_le.mp hc'
  have hGrid := scalar_interval_grid_card P (fun k => cellCenter (mesh D) k 3) hm
    (by norm_num : (0:ℝ)≤14) hBound
  have hRead (k : Index) : ⌊cellCenter (mesh D) k 3/mesh D⌋=k 3 := by
    change ⌊(mesh D*((k 3:ℝ)+1/2))/mesh D⌋=k 3
    rw [mul_div_cancel_left₀ _ hm.ne',Int.floor_intCast_add]
    norm_num
  have hImage : scalarCells P (fun k => cellCenter (mesh D) k 3) (mesh D)=P.image (fun k => k 3) := by
    unfold scalarCells
    congr 1
    funext k
    exact hRead k
  rw [hImage] at hGrid
  have hPaid : 14/mesh D+2≤32/D.thickness := by
    dsimp only [mesh]
    apply (le_div_iff₀ hd).mpr
    have hCancel : (14/(D.thickness/2)+2)*D.thickness=28+2*D.thickness := by field_simp; ring
    rw [hCancel]
    linarith only [h.1.2.2.1]
  exact hGrid.trans hPaid

/-- A packed tangent query at any positive mesh r has the actual planar
box count (14/r+2)^2. No tangent-grid occupancy is assumed. -/
theorem packed_tangent_grid_count {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (cells : Fin n → Finset Index) (hCells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences cells)
    (O : E4 ≃ₗᵢ[ℝ] E4) (r : ℝ) (hr : 0<r) :
    (((E.image Prod.snd).image (fun k => fun j : Fin 2 =>
      ⌊O (cellCenter (mesh D) k) j.castSucc.castSucc/r⌋)).card:ℝ)≤(14/r+2)^2 := by
  let P := E.image Prod.snd
  let x := fun k : Index => (O (cellCenter (mesh D) k) 0,O (cellCenter (mesh D) k) 1)
  have hBound (k : Index) (hk : k∈P) (v : Fin 4) : |O (cellCenter (mesh D) k) v|≤7 := by
    have hh := PiLp.norm_apply_le (O (cellCenter (mesh D) k)) v
    rw [O.norm_map] at hh
    exact (show |O (cellCenter (mesh D) k) v|≤‖cellCenter (mesh D) k‖ by
      simpa only [Real.norm_eq_abs] using hh).trans (original_cell_center_norm h hK cells hCells E hE k hk)
  have hRect : ∀k∈P,((-7:ℝ)≤(x k).1 ∧ (x k).1≤ -7+14) ∧
      ((-7:ℝ)≤(x k).2 ∧ (x k).2≤ -7+14) := by
    intro k hk
    exact ⟨by simpa only [show (-7:ℝ)+14=7 by norm_num] using abs_le.mp (hBound k hk 0),
      by simpa only [show (-7:ℝ)+14=7 by norm_num] using abs_le.mp (hBound k hk 1)⟩
  have hGrid := planar_rectangle_grid_card P x hr (by norm_num : (0:ℝ)≤14)
    (by norm_num : (0:ℝ)≤14) hRect
  let label := fun k : Index => fun j : Fin 2 => ⌊O (cellCenter (mesh D) k) j.castSucc.castSucc/r⌋
  have hInj : Function.Injective (fun v : Fin 2 → ℤ => (v 0,v 1)) := by
    intro v w he
    funext j
    fin_cases j
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  have hImage : (P.image label).image (fun v => (v 0,v 1))=planarCells P x r := by
    rw [image_image]
    rfl
  have hCard : (P.image label).card=(planarCells P x r).card := by
    rw [←hImage,card_image_iff.mpr (fun _ _ _ _ hh => hInj hh)]
  change ((P.image label).card:ℝ)≤_
  rw [hCard]
  simpa only [pow_two] using hGrid

/-- In particular the actual fine packed X alphabet needed by
packed_Y_class_lower has capacity1024 sigma^-2 on this SAME graph. -/
theorem packed_fine_X_count {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (cells : Fin n → Finset Index) (hCells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences cells) (O : E4 ≃ₗᵢ[ℝ] E4) :
    (((E.image Prod.snd).image (packedXKey (mesh D) O)).card:ℝ)≤1024/D.thickness^2 := by
  have hd := h.1.2.1
  have hGrid := packed_tangent_grid_count h hK cells hCells E hE O (mesh D) (half_pos hd)
  change (((E.image Prod.snd).image (packedXKey (mesh D) O)).card:ℝ)≤(14/mesh D+2)^2 at hGrid
  have hPaid : 14/mesh D+2≤32/D.thickness := by
    dsimp only [mesh]
    apply (le_div_iff₀ hd).mpr
    have hCancel : (14/(D.thickness/2)+2)*D.thickness=28+2*D.thickness := by field_simp; ring
    rw [hCancel]
    linarith only [h.1.2.2.1]
  exact hGrid.trans ((pow_le_pow_left₀ (by positivity) hPaid 2).trans_eq (by ring))

end NativeCompactSourceCoordinateCapsDraft2218
