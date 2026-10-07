import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu
import Theorems.Thm_StickyKakeya4_native_bounded_parent_point_transfer
import Theorems.Thm_StickyKakeya4_native_parent_slice_caller_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeNormalizedCellRelativeCore
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts
open NativeLocalParentSource NativeRelativeParentLabels NativeRelativeCoarsePointMenu NativeRelativeCoarseReadback
open NativeNormalizedCellRelativeMenu NativeJointUniformCoarseRelations NativeConditionedPairMenu SelfUniform
open NativeIncidenceMultiplicityTower

/-- The full-R relative representative is defined for all parents before E2.
The empty-parent fallback is never used on retained source incidences. -/
def backboneRepresentative {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m M : ℕ) (p t : Parent) : Fin n :=
  if hp : (parentLabels D R a (2^m) p).Nonempty then originalRepresentative h R a m p hp M t
  else ⟨0,h.1.1⟩

def pairLabel {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m M : ℕ) (z : Fin n × Index) : Parent × (Parent × Index) :=
  let p := parentLabel D a (2^m) z.1
  let t := relativeLabel D a (2^m) p M z.1
  (p,(t,doubleLabel D a (2^m) M p (backboneRepresentative h R a m M p t) z.1 z.2))

def pointLabel {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m M : ℕ) (z : Fin n × Index) : Parent × Index :=
  ((pairLabel h R a m M z).1,(pairLabel h R a m M z).2.2)

/-- Exactly two equality relations per requested relative scale, installed
before the single E2 call. All representatives depend only on the old R. -/
def relations {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m : ℕ) (scales : Fin K → ℕ) :
    Fin (K+K) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases (fun j x y => pairLabel h R a m (scales j) x=pairLabel h R a m (scales j) y)
    (fun j x y => pointLabel h R a m (scales j) x=pointLabel h R a m (scales j) y)

lemma relations_refl {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m : ℕ) (scales : Fin K → ℕ) : ∀j x,relations h R a m scales j x x := by
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro j x <;>
    simp only [relations,Fin.addCases_left,Fin.addCases_right]

lemma relations_symm {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m : ℕ) (scales : Fin K → ℕ) :
    ∀j x y,relations h R a m scales j x y → relations h R a m scales j y x := by
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro j x y H <;>
    simp only [relations,Fin.addCases_left,Fin.addCases_right] at H ⊢ <;> exact H.symm

theorem caller_relative_uniformities {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m : ℕ) (scales : Fin K → ℕ) (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (relations h R a m scales j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations h R a m scales j) E y)
    (p : Parent) (hp : (parentLabels D R a (2^m) p).Nonempty) (j : Fin K) :
    HasUniformFibers (parentEdges D a (2^m) E p) Q (doublePair h R a m p hp (scales j)) ∧
    HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => (doublePair h R a m p hp (scales j) z).2) := by
  have hPair : HasUniformFibers E Q (pairLabel h R a m (scales j)) := by
    intro x hx y hy
    simpa only [relations,Fin.addCases_left,unit_degree_eq_fiber] using H (Fin.castAdd K j) x y hx hy
  have hPoint : HasUniformFibers E Q (pointLabel h R a m (scales j)) := by
    intro x hx y hy
    simpa only [relations,Fin.addCases_right,unit_degree_eq_fiber] using H (Fin.natAdd K j) x y hx hy
  have hRead (z : Fin n × Index) (hz : z∈parentEdges D a (2^m) E p) :
      (pairLabel h R a m (scales j) z).2=doublePair h R a m p hp (scales j) z := by
    simp only [pairLabel,(mem_filter.mp hz).2,backboneRepresentative,dif_pos hp,doublePair]
  constructor
  · apply uniformity_congr _ (fun z => (pairLabel h R a m (scales j) z).2) _ Q hRead
    exact conditioned_uniformity E (fun z => parentLabel D a (2^m) z.1) _ Q hPair p
  · apply uniformity_congr _ (fun z => (pointLabel h R a m (scales j) z).2) _ Q
      (fun z hz => by
        change (pairLabel h R a m (scales j) z).2.2=(doublePair h R a m p hp (scales j) z).2
        exact congrArg Prod.snd (hRead z hz))
    exact conditioned_uniformity E (fun z => parentLabel D a (2^m) z.1) _ Q hPoint p

def normalizedPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m M : ℕ) (p : Parent)
    (z : Fin n × Index) : Parent × Index :=
  (relativeLabel D a (2^m) p M z.1,physicalCell D a (2^m) M p z.2)

/-- The explicit physical-cube menu applies to the unchanged full-R
representative used by the exact relative full-source readback. -/
theorem physical_fiber_relative_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (m M : ℕ) (hM : 0 < M)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*(M:ℝ) ≤ 64)
    (p : Parent) (hp : (parentLabels D R a (2^m) p).Nonempty)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hlabels : ∀z∈E,z.1∈parentLabels D R a (2^m) p) (q : Index) :
    ((E.filter (fun z => (normalizedPair D a m M p z).2=q)).image
      (fun z => (doublePair h R a m p hp M z).2)).card ≤ 81 := by
  rw [←forwardMenu_card M q]
  apply card_le_card
  intro w hw
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
  obtain ⟨hz,hzq⟩ := mem_filter.mp hz
  have hh := double_label_mem_forward h original horiginal ha (2^m) M (by positivity) hM
    hNscale hRelScale p z.1 (originalRepresentative h R a m p hp M (relativeLabel D a (2^m) p M z.1)) z.2
    ((mem_incidences original z.1 z.2).mp (hE hz)) (mem_filter.mp (hlabels z hz)).2
    (originalRepresentative_label h R a m p hp M z.1 (hlabels z hz))
  change physicalCell D a (2^m) M p z.2=q at hzq
  simpa only [doublePair,hzq] using hh

/-- Actual normalized-cell degree is bounded by the exact relative-image
average. Only preinstalled pair/point reference uniformity is used. -/
theorem normalized_cell_degree_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (m M : ℕ) (hM : 0 < M)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*(M:ℝ) ≤ 64)
    (p : Parent) (hp : (parentLabels D R a (2^m) p).Nonempty)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hlabels : ∀z∈E,z.1∈parentLabels D R a (2^m) p) (Q : ℕ)
    (hPair : HasUniformFibers E Q (doublePair h R a m p hp M))
    (hPoint : HasUniformFibers E Q (fun z => (doublePair h R a m p hp M z).2)) (q : Index) :
    (((E.image (normalizedPair D a m M p)).filter (fun z => z.2=q)).card:ℝ) ≤
      81*(Q:ℝ)^4*multiplicity (E.image (doublePair h R a m p hp M)) := by
  let g := doublePair h R a m p hp M
  have hParent (t : Parent) : ((E.filter (fun z => (g z).1=t)).image
      (fun z => (normalizedPair D a m M p z).1)).card ≤ 1 := by
    have hs : (E.filter (fun z => (g z).1=t)).image
        (fun z => (normalizedPair D a m M p z).1)⊆{t} := by
      intro u hu
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hu
      exact mem_singleton.mpr (mem_filter.mp hz).2
    exact (card_le_card hs).trans_eq (card_singleton t)
  have hDegree (y : Index) : (((E.image g).filter (fun z => z.2=y)).card:ℝ) ≤
      (Q:ℝ)^4*multiplicity (E.image g) := by
    have hh := NativeCoarseUniformImageDegrees.image_point_degree_le_multiplicity
      E g (Q^2) (Q^2) hPair hPoint y
    simpa only [Nat.cast_pow,show (Q:ℝ)^2*(Q:ℝ)^2=(Q:ℝ)^4 by ring] using hh
  have hh := NativeBoundedParentPointTransfer.image_point_degree_le E
    (normalizedPair D a m M p) g 1 81 ((Q:ℝ)^4*multiplicity (E.image g)) hParent
    (physical_fiber_relative_menu h original horiginal ha R m M hM hNscale hRelScale p hp E hE hlabels)
    (by unfold NativeIncidenceMultiplicityTower.multiplicity; positivity) hDegree q
  simpa only [Nat.cast_one,Nat.cast_ofNat,one_mul,mul_assoc] using hh

end NativeNormalizedCellRelativeCore
