import Theorems.Thm_StickyKakeya4_native_actual_rich_packet_layers
import Theorems.Thm_StickyKakeya4_native_compatible_node_directions

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeActualGrainHistory
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeSquaredGrainQueries NativeNodalReferenceLift
open NativeTaggedPacketRows NativeQueriedVertexWeights NativeTaggedReferenceDensity
open NativeJointUniformCoarseRelations NativeDirectionRankDichotomy NativeCompatibleAngularCandidates
open RichDirectionalLayers WeightedRichDirectionalLayers NativeWeightedPacketLayers NativePacketRetainedLayers
open NativeActualRichPacketLayers NativeCompatibleNodeDirections
open scoped BigOperators

def scaleLift {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (S : Finset Index) : Finset (Index × Index) :=
  currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))

def scaleThreshold {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : ℕ) (S : Finset Index) (ell : ℕ) (dir : ℕ → Index → Fin n) (i : ℕ) : ℕ :=
  let A := reference D m E S
  let U := scaleLift D m S
  let packet := fun r => packetSet D m E S (dir r)
  let label := fun r => assignedLabel D m (dir r)
  let w := tagWeight E
  richThreshold (mass U w) (referenceBudget A U packet label w ell) ell
    (referenceMinimum A U (packet i) (label i) w)

def scaleLayers {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : ℕ) (S : Finset Index) (ell : ℕ) (dir : ℕ → Index → Fin n) : ℕ → Finset (Index × Index) :=
  NativeWeightedPacketLayers.layers (scaleLift D m S) (fun i => packetSet D m E S (dir i))
    (fun i => assignedLabel D m (dir i)) (tagWeight E) (scaleThreshold D E m S ell dir)

def nextPoints {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : ℕ) (S : Finset Index) (ell : ℕ) (dir : ℕ → Index → Fin n) : Finset Index :=
  (scaleLayers D E m S ell dir ell).image Prod.snd

/-- Full quantitative one-scale record, retaining the actual computed packet
minima, thresholds, original reference weights, and every predecessor layer. -/
def HasScaleRecord {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : ℕ) (S : Finset Index) (ell : ℕ) (dir : ℕ → Index → Fin n)
    (Q2 : ℕ) (lambda c1 c2 : ℝ) : Prop :=
  let A := reference D m E S
  let U := scaleLift D m S
  let packet := fun i => packetSet D m E S (dir i)
  let label := fun i => assignedLabel D m (dir i)
  let w := tagWeight E
  let M := vertexCap E (spatialLabel D (2^(phaseDepth m))) Q2
  let N := referenceBudget A U packet label w ell
  let b := fun i => referenceMinimum A U (packet i) (label i) w
  let k := scaleThreshold D E m S ell dir
  let Omega := scaleLayers D E m S ell dir
  U⊆A ∧ mass U w=mass S (pointWeight E) ∧ N ≤ referenceConstant*E.card ∧
    (∀i<ell,(M:ℝ)*lambda*D.thickness^(c1+5*c2)/(64/((2^m:ℕ):ℝ)) ≤ (b i:ℝ)) ∧
    Omega 0=U ∧ (∀i,Omega (i+1)⊆Omega i) ∧ (∀i,Omega i⊆A) ∧
    mass U w ≤ 2*mass (Omega ell) w ∧ 0 < mass (Omega ell) w ∧
    (∀i<ell,∀u∈Omega (i+1),k i ≤ packetMass (Omega i) (packet i) w (label i u)) ∧
    0 < ∏i∈range ell,k i ∧
    ∀i<ell,((mass S (pointWeight E):ℝ)/(E.card:ℝ))*lambda*D.thickness^(c1+5*c2)/
      (2*(ell:ℝ)*(referenceConstant:ℝ)*(64/((2^m:ℕ):ℝ))) < (k i:ℝ)/(M:ℝ)

lemma scaleLayers_subset_lift {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : ℕ) (S : Finset Index) (ell : ℕ) (dir : ℕ → Index → Fin n) (i : ℕ) :
    scaleLayers D E m S ell dir i⊆scaleLift D m S :=
  NativeWeightedPacketLayers.layers_subset_start _ _ _ _ _ i

/-- A subset of the actual one-tag-per-point lift is exactly recovered by
its old-point projection. No multiplicity or replacement-label premise is used. -/
lemma lift_of_snd_image {α : Type*} [DecidableEq α] (S : Finset α) (point : α → E4) (delta : ℝ)
    (T : Finset (Index × α)) (hT : T⊆currentLift S point delta) :
    currentLift (T.image Prod.snd) point delta=T := by
  have hid : ∀u∈T,(wzDyadicCellIndex delta (point u.2),u.2)=u := by
    intro u hu
    have hh := hT hu
    simp only [currentLift,mem_image] at hh
    obtain ⟨k,_hk,rfl⟩ := hh
    rfl
  ext u
  simp only [currentLift,mem_image]
  constructor
  · rintro ⟨k,⟨v,hv,hvk⟩,he⟩
    have huv : u=v := by rw [←he,←hvk]; exact hid v hv
    simpa only [huv] using hv
  · intro hu
    exact ⟨u.2,⟨u,hu,rfl⟩,hid u hu⟩

lemma lift_snd_image {α : Type*} [DecidableEq α] (S : Finset α) (point : α → E4) (delta : ℝ) :
    (currentLift S point delta).image Prod.snd=S := by
  simp only [currentLift,image_image,Function.comp_def,image_id']

lemma original_tag_mem_lift {α : Type*} (S : Finset α) (point : α → E4) (delta : ℝ)
    (k : α) (hk : k∈S) : (wzDyadicCellIndex delta (point k),k)∈currentLift S point delta :=
  mem_image_of_mem _ hk

theorem terminal_lift {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : ℕ) (S : Finset Index) (ell : ℕ) (dir : ℕ → Index → Fin n) :
    scaleLayers D E m S ell dir ell=scaleLift D m (nextPoints D E m S ell dir) :=
  (lift_of_snd_image S _ _ _ (scaleLayers_subset_lift D E m S ell dir ell)).symm

theorem terminal_mass {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : ℕ) (S : Finset Index) (ell : ℕ) (dir : ℕ → Index → Fin n) :
    mass (scaleLayers D E m S ell dir ell) (tagWeight E)=
      mass (nextPoints D E m S ell dir) (pointWeight E) := by
  rw [terminal_lift]
  exact currentLift_mass _ _ _ _

theorem nextPoints_subset {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : ℕ) (S : Finset Index) (ell : ℕ) (dir : ℕ → Index → Fin n) :
    nextPoints D E m S ell dir⊆S := by
  have hh := image_subset_image (f:=Prod.snd) (scaleLayers_subset_lift D E m S ell dir ell)
  simpa only [scaleLift,lift_snd_image,nextPoints] using hh

theorem record_retention {n : ℕ} {D : FiniteScaleSource n} {E : Finset (Fin n × Index)}
    {m ell Q2 : ℕ} {S : Finset Index} {dir : ℕ → Index → Fin n} {lambda c1 c2 : ℝ}
    (H : HasScaleRecord D E m S ell dir Q2 lambda c1 c2) :
    (nextPoints D E m S ell dir).Nonempty ∧
      mass S (pointWeight E) ≤ 2*mass (nextPoints D E m S ell dir) (pointWeight E) := by
  obtain ⟨_hUA,hmass,_hbudget,_hb,_hz,_hsub,_hA,hhalf,hpos,_hpred,_hprod,_hratio⟩ := H
  rw [terminal_mass] at hpos hhalf
  rw [hmass] at hhalf
  refine ⟨?_,hhalf⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty.mp hne] at hpos
  simp [WeightedRichDirectionalLayers.mass] at hpos

/-- Sequential actual grain extraction. The maps and original E weights are
fixed; only the current old-point set changes. Past J the history is constant. -/
def history {n J : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : Fin J → ℕ) (ell : ℕ) (dir : Fin J → ℕ → Index → Fin n)
    (S0 : Finset Index) : ℕ → Finset Index
  | 0 => S0
  | r+1 => if hr : r<J then nextPoints D E (m ⟨r,hr⟩)
      (history D E m ell dir S0 r) ell (dir ⟨r,hr⟩) else history D E m ell dir S0 r

theorem history_step_subset {n J : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : Fin J → ℕ) (ell : ℕ) (dir : Fin J → ℕ → Index → Fin n) (S0 : Finset Index) (r : ℕ) :
    history D E m ell dir S0 (r+1)⊆history D E m ell dir S0 r := by
  rw [history]
  split_ifs with hr
  · exact nextPoints_subset _ _ _ _ _ _
  · exact Subset.refl _

theorem history_antitone {n J : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : Fin J → ℕ) (ell : ℕ) (dir : Fin J → ℕ → Index → Fin n) (S0 : Finset Index) :
    Antitone (history D E m ell dir S0) :=
  antitone_nat_of_succ_le (history_step_subset D E m ell dir S0)

def HasGrainHistory {n J : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : Fin J → ℕ) (ell : ℕ) (dir : Fin J → ℕ → Index → Fin n) (S0 : Finset Index)
    (Q2 : ℕ) (lambda c1 c2 : ℝ) : Prop :=
  let S := history D E m ell dir S0
  S 0=S0 ∧ (∀r,S (r+1)⊆S r) ∧
    (∀r,r≤J → (S r).Nonempty ∧ S r⊆S0 ∧ mass S0 (pointWeight E) ≤ 2^r*mass (S r) (pointWeight E)) ∧
    mass S0 (pointWeight E) ≤ 2^J*mass (S J) (pointWeight E) ∧
    (∀j : Fin J,HasScaleRecord D E (m j) (S j.val) ell (dir j) Q2 lambda c1 c2) ∧
    (∀j : Fin J,scaleLayers D E (m j) (S j.val) ell (dir j) ell=scaleLift D (m j) (S (j.val+1))) ∧
    ∀j : Fin J,∀k∈S J,(spatialLabel D (2^(m j)) k,k)∈scaleLayers D E (m j) (S j.val) ell (dir j) ell

/-- Finite bookkeeping helper. The source-facing theorem below supplies Hstep
by the actual queried packet constructor, not by an assumed rich factory. -/
theorem history_of_rich_scales {n J : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : Fin J → ℕ) (ell : ℕ) (dir : Fin J → ℕ → Index → Fin n)
    (S0 : Finset Index) (hS0 : S0.Nonempty) (Q2 : ℕ) (lambda c1 c2 : ℝ)
    (Hstep : ∀j : Fin J,∀S⊆S0,S.Nonempty → HasScaleRecord D E (m j) S ell (dir j) Q2 lambda c1 c2) :
    HasGrainHistory D E m ell dir S0 Q2 lambda c1 c2 := by
  let S := history D E m ell dir S0
  have hmono : Antitone S := history_antitone D E m ell dir S0
  have hsub (r : ℕ) : S r⊆S0 := hmono (Nat.zero_le r)
  have hvalid : ∀r,r≤J → (S r).Nonempty ∧ mass S0 (pointWeight E) ≤ 2^r*mass (S r) (pointWeight E) := by
    intro r
    induction r with
    | zero =>
      intro _
      exact ⟨hS0,by simpa only [S,history,pow_zero,one_mul] using
        (Nat.le_refl (mass S0 (pointWeight E)))⟩
    | succ r ih =>
      intro hrJ
      have hr : r<J := by omega
      obtain ⟨hne,hmass⟩ := ih (by omega)
      have H := Hstep ⟨r,hr⟩ (S r) (hsub r) hne
      obtain ⟨hnext,hhalf⟩ := record_retention H
      have he : S (r+1)=nextPoints D E (m ⟨r,hr⟩) (S r) ell (dir ⟨r,hr⟩) := by
        simp only [S,history,dif_pos hr]
      refine ⟨by simpa only [he] using hnext,?_⟩
      calc
        _ ≤ 2^r*mass (S r) (pointWeight E) := hmass
        _ ≤ 2^r*(2*mass (S (r+1)) (pointWeight E)) :=
          Nat.mul_le_mul_left _ (by simpa only [he] using hhalf)
        _ = _ := by rw [pow_succ]; ring
  have hrecord (j : Fin J) : HasScaleRecord D E (m j) (S j.val) ell (dir j) Q2 lambda c1 c2 :=
    Hstep j (S j.val) (hsub j.val) (hvalid j.val j.isLt.le).1
  have hterminal (j : Fin J) : scaleLayers D E (m j) (S j.val) ell (dir j) ell=
      scaleLift D (m j) (S (j.val+1)) := by
    have he : S (j.val+1)=nextPoints D E (m j) (S j.val) ell (dir j) := by
      simp only [S,history,dif_pos j.isLt]
    rw [he]
    exact terminal_lift D E (m j) (S j.val) ell (dir j)
  refine ⟨rfl,history_step_subset D E m ell dir S0,?_,(hvalid J le_rfl).2,hrecord,hterminal,?_⟩
  · exact fun r hr => ⟨(hvalid r hr).1,hsub r,(hvalid r hr).2⟩
  · intro j k hk
    rw [hterminal j]
    have hk' : k∈S (j.val+1) := hmono (Nat.succ_le_of_lt j.isLt) hk
    exact original_tag_mem_lift _ _ _ k hk'

/-- Source-facing finite history. The actual packet constructor supplies each
step from the SAME E2 query fields, and the prescribed compatible pair family
supplies the node directions once. No rich-factory or final-history premise is
assumed. The only repeated loss is the fixed natural factor 2^J. -/
theorem construct_actual_grain_history {n level J : ℕ} {D : FiniteScaleSource n}
    {eta eta2 a lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hER : ∀z∈E,z.1∈R)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (stop : ℕ) (m : Fin J → ℕ) (hms : ∀j,m j ≤ stop)
    (hm6 : ∀j,6 ≤ m j) (hpL : ∀j,phaseDepth (m j) ≤ level)
    (hscale : ∀j,D.thickness ≤ (64/((2^(m j):ℕ):ℝ))^2)
    (HF : ∀j,HasUniformFibers E Q2
      (fixedPair D a level (phaseDepth (m j)) (phaseDepth (m j))
        (representative h R a (2^(phaseDepth (m j))))))
    (HC : ∀j,HasUniformFibers E Q2
      (fixedPair D a level (phaseDepth (m j)) (m j)
        (representative h R a (2^(phaseDepth (m j))))))
    (HV : ∀j,HasUniformFibers E Q2 (fun z => spatialLabel D (2^(phaseDepth (m j))) z.2))
    (q : ℝ) (hq : 0 < q) (ell : ℕ) (hell : 0 < ell)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hP : P⊆terminalFamily D a stop E q ell)
    (hPne : P.Nonempty)
    (hcompat : ∀j : Fin J,∀x y,x∈P → y∈P →
      spatialLabel D (2^(m j)) x.1=spatialLabel D (2^(m j)) y.1 →
      projectWord stop (m j) x.2=projectWord stop (m j) y.2) :
    ∃ (point : Fin J → Index → Index)
      (tuple : Fin J → Index → Fin ell → (Fin n × Index))
      (anchor : Fin J → Index → Fin ell → Fin n),
      (∀j,IsNodeDirectionSystem D a (m j) E (P.image Prod.fst) q ell
        (point j) (tuple j) (anchor j)) ∧
      HasGrainHistory D E m ell (fun j => natStageDirectionIndex h (tuple j))
        (P.image Prod.fst) Q2 lambda c1 c2 := by
  have H (j : Fin J) := exists_node_direction_system h a stop (m j) (hms j)
    E q hq ell P hP (hcompat j)
  choose point tuple anchor hsystem using H
  have hnode (j : Fin J) := (hsystem j).1
  have hS0E : P.image Prod.fst⊆E.image Prod.snd := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    exact ((CompatibleTupleSelection.mem_goodPairs _ _ p).mp (hP hp)).1
  refine ⟨point,tuple,anchor,hnode,?_⟩
  apply history_of_rich_scales D E m ell (fun j => natStageDirectionIndex h (tuple j))
    (P.image Prod.fst) (hPne.image Prod.fst) Q2 lambda c1 c2
  intro j S hSS0 hSn
  have Hcurrent := node_direction_system_mono (hnode j) hSS0
  have hanchor : ∀i<ell,∀k∈S,∃v : Fin n,(v,k)∈E ∧
      (parentLabel D a (2^(m j)) v).1=
        (parentLabel D a (2^(m j))
          (natStageDirectionIndex h (tuple j) i (spatialLabel D (2^(m j)) k))).1 := by
    intro i hi k hk
    exact ⟨natStageAnchorIndex h (anchor j) i k,nat_stage_anchor_readback h Hcurrent k hk i hi⟩
  exact construct_rich_packet_layers h original horiginal ha R E hE hER F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2 (m j) (hm6 j) (hpL j)
    (hscale j) (HF j) (HC j) (HV j) S (hSS0.trans hS0E) hSn ell hell
    (natStageDirectionIndex h (tuple j)) hanchor

end NativeActualGrainHistory
