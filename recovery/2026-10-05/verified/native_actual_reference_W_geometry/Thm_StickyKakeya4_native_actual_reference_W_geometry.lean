import Theorems.Thm_StickyKakeya4_native_column_population_bounds
import Theorems.Thm_StickyKakeya4_original_scalar_collision_mass

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeActualReferenceWGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts
open NativeOriginalParentPhysicalData NativeLocalParentPhysicalMap NativeLocalParentGeometry
open NativeAnisotropicShortRowGeometry NativeAnisotropicColumnMenus NativeAnisotropicGlobalSourceBridge
open NativeDirectionRankDichotomy NativeRawShadowPointComparison
open NativeSpatialAngularGeometry

/-- Distinct geometric column/phase incidences; original labels are witnesses,
not multiplicities in this finite graph. -/
def incidences {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ) (p : Parent)
    (H : Finset (Fin n × Index)) : Finset (Index × Parent) :=
  H.image (fun z => ((columnPair D a m f p z).2,(columnPair D a m f p z).1))

lemma incidence_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ) (p : Parent)
    (H : Finset (Fin n × Index)) :
    (incidences D a m f p H).card=(H.image (columnPair D a m f p)).card := by
  have he : incidences D a m f p H=(H.image (columnPair D a m f p)).image Prod.swap := by
    simp only [incidences,image_image,Function.comp_def,Prod.swap]
  rw [he]
  exact card_image_of_injective _ Prod.swap_injective

/-- Equal physical height labels give the actual raw height gap H, with
the chart translation retained. No independent height-filling is assumed. -/
lemma equal_column_height_gap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (sigma H : ℝ) (hH : 0 < H) (k l : Index)
    (he : columnLabel D a N p sigma H k (3:Fin 4)=
      columnLabel D a N p sigma H l (3:Fin 4)) :
    |cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4)| ≤ H := by
  simp only [columnLabel,chartWidth,if_true] at he
  have hh := same_floor_width_close (by positivity : (0:ℝ)<H/512) he
  rw [chart_height_sub,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)] at hh
  linarith only [hh]

/-- An actual fine phase in one actual parent and one height bin occupies
a fixed finite column halo. This uses original tube geometry, not AD. -/
theorem same_phase_height_column_halo {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m f : ℕ) (hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ))
    (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (p : Parent) (x y : Fin n × Index)
    (hx : x∈NativeCubicalIncidenceCounts.incidences original)
    (hy : y∈NativeCubicalIncidenceCounts.incidences original)
    (hp : parentLabel D a (2^m) x.1=p)
    (hphase : parentLabel D a (2^f) y.1=parentLabel D a (2^f) x.1)
    (hheight : (columnPair D a m f p y).2 (3:Fin 4)=(columnPair D a m f p x).2 (3:Fin 4)) :
    (columnPair D a m f p y).2∈columnHalo 27 0 ((columnPair D a m f p x).2) := by
  let N : ℝ := ((2^m:ℕ):ℝ)
  let H : ℝ := 64/N
  let sigma : ℝ := 64/((2^f:ℕ):ℝ)
  let X := cellCenter (mesh D) x.2
  let Y := cellCenter (mesh D) y.2
  let dt := Y (3:Fin 4)-X (3:Fin 4)
  have hN : 0<N := by dsimp [N]; positivity
  have hH : 0<H := by dsimp [H]; positivity
  have hsig : 0<sigma := by dsimp [sigma]; positivity
  have ht : |dt| ≤ H := equal_column_height_gap D a (2^m) p sigma H hH y.2 x.2 hheight
  have hNH : N*H=64 := by dsimp [H]; field_simp
  have htSmall : H ≤ N*sigma := by
    have hh := mul_le_mul_of_nonneg_left hwindow hN.le
    change N*H^2 ≤ N*sigma at hh
    have hi : N*H^2=64*H := by rw [pow_two,←mul_assoc,hNH]
    rw [hi] at hh
    linarith only [hh,hH]
  have hxTube := original_cell_in_tube h original horiginal hx
  have hyTube := original_cell_in_tube h original horiginal hy
  have he : 2*mesh D=D.thickness := by unfold mesh; ring
  rw [he] at hxTube hyTube
  have hw := NativeSameFineParentPacket.same_parent_displacement_error h ha (2^f)
    (by positivity) x.1 y.1 hphase hxTube hyTube
  let w := (Y-X)-dt • slopeVector D x.1
  have hwb : ‖w‖ ≤ 25*sigma := by
    change ‖w‖ ≤ 24*D.thickness+16/((2^f:ℕ):ℝ) at hw
    have hi : 16/((2^f:ℕ):ℝ)=sigma/4 := by dsimp [sigma]; ring
    rw [hi] at hw
    change D.thickness ≤ sigma at hdelta
    linarith only [hw,hdelta,hsig]
  apply Fintype.mem_piFinset.mpr
  intro v
  refine Fin.lastCases ?_ (fun v => ?_) v
  · simp only [show (Fin.last 3:Fin 4)=3 by rfl,if_true,mem_Icc]
    simpa only [Nat.cast_zero,sub_zero,add_zero,hheight] using
      (show (columnPair D a m f p x).2 (3:Fin 4) ≤ (columnPair D a m f p x).2 (3:Fin 4) ∧
        (columnPair D a m f p x).2 (3:Fin 4) ≤ (columnPair D a m f p x).2 (3:Fin 4) from ⟨le_rfl,le_rfl⟩)
  · have hv : v.castSucc≠(3:Fin 4) := Fin.castSucc_ne_last v
    simp only [columnPair,columnLabel,chartWidth,if_neg hv]
    apply floor_mem_interval 26
    rw [←sub_div,NativeAnisotropicShortRowGeometry.chart_spatial_sub,abs_div,
      abs_of_pos (by positivity : (0:ℝ)<N*sigma/512)]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    apply (div_le_iff₀ (by positivity)).mpr
    have hcoord : |w v.castSucc| ≤ 25*sigma := by
      have hh : |w v.castSucc| ≤ ‖w‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w v.castSucc
      exact hh.trans hwb
    have h1 : |N*w v.castSucc| ≤ 25*N*sigma := by
      rw [abs_mul,abs_of_pos hN]
      nlinarith only [mul_le_mul_of_nonneg_left hcoord hN.le]
    have hs := localSlope_bound D a (2^m) p x.1 hp v
    have h2 : |(N*slope (D.line x.1) v-(p.1 v:ℝ))*dt| ≤ N*sigma := by
      rw [abs_mul]
      exact ((mul_le_mul hs ht (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq
        (one_mul H)).trans htSmall
    have hi : N*(Y v.castSucc-X v.castSucc)-(p.1 v:ℝ)*dt=
      N*w v.castSucc+(N*slope (D.line x.1) v-(p.1 v:ℝ))*dt := by
      dsimp [w,slopeVector]
      simp only [ActualSlopeSource.heightPoint_castSucc]
      ring
    change |N*(Y v.castSucc-X v.castSucc)-(p.1 v:ℝ)*dt|/512 ≤
      (26:ℝ)*(N*sigma/512)
    rw [hi]
    have hh := (abs_add_le _ _).trans (add_le_add h1 h2)
    linarith only [hh]

def heightColumnCost : ℕ := 55^3

/-- Bounded DISTINCT point occupancy of each geometric tube at each actual
column height. The original fine labels are used only to prove containment. -/
theorem pointsAt_card_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m f : ℕ) (hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ))
    (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (p : Parent) (H : Finset (Fin n × Index))
    (hH : H⊆NativeCubicalIncidenceCounts.incidences original)
    (hp : ∀z∈H,parentLabel D a (2^m) z.1=p) (t : Parent) (z : ℤ) :
    (OriginalWWitnessCounts.pointsAt (incidences D a m f p H) (fun k => k (3:Fin 4)) t z).card ≤
      heightColumnCost := by
  let A := OriginalWWitnessCounts.pointsAt (incidences D a m f p H) (fun k => k (3:Fin 4)) t z
  by_cases hn : A.Nonempty
  · obtain ⟨k,hk⟩ := hn
    have hkI : (k,t)∈incidences D a m f p H := (OriginalWWitnessCounts.mem_pointsAt _ _ _ _ _).mp hk |>.1
    have hkz : k (3:Fin 4)=z := (OriginalWWitnessCounts.mem_pointsAt _ _ _ _ _).mp hk |>.2
    obtain ⟨x,hx,hxe⟩ := mem_image.mp hkI
    have hxk : (columnPair D a m f p x).2=k := congrArg Prod.fst hxe
    have hxt : (columnPair D a m f p x).1=t := congrArg Prod.snd hxe
    have hsub : A⊆columnHalo 27 0 k := by
      intro l hl
      obtain ⟨hlI,hlz⟩ := (OriginalWWitnessCounts.mem_pointsAt _ _ _ _ _).mp hl
      obtain ⟨y,hy,hye⟩ := mem_image.mp hlI
      have hyk : (columnPair D a m f p y).2=l := congrArg Prod.fst hye
      have hyt : (columnPair D a m f p y).1=t := congrArg Prod.snd hye
      have hphase : parentLabel D a (2^f) y.1=parentLabel D a (2^f) x.1 := hyt.trans hxt.symm
      have hheight : (columnPair D a m f p y).2 (3:Fin 4)=
          (columnPair D a m f p x).2 (3:Fin 4) := by rw [hyk,hxk,hlz,hkz]
      have hh := same_phase_height_column_halo h original horiginal ha m f hdelta hwindow p x y
        (hH hx) (hH hy) (hp x hx) hphase hheight
      simpa only [hyk,hxk] using hh
    exact (card_le_card hsub).trans_eq (by rw [columnHalo_card]; norm_num [heightColumnCost])
  · change A.card ≤ heightColumnCost
    rw [not_nonempty_iff_eq_empty.mp hn,card_empty]
    exact Nat.zero_le _

end NativeActualReferenceWGeometry
