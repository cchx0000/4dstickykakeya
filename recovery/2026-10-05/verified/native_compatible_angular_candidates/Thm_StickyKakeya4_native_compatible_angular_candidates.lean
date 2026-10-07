import Theorems.Thm_StickyKakeya4_native_master_successor_menu
import Theorems.Thm_StickyKakeya4_native_original_angular_tuple_menu
import Theorems.Thm_StickyKakeya4_native_retained_query_menu
import Theorems.Thm_StickyKakeya4_compatible_tuple_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

noncomputable section
namespace NativeCompatibleAngularCandidates
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeOriginalParentDensityCore
open NativeSpatialAngularGeometry NativeSuccessorAngularCount NativeOriginalAngularTupleMenu
open NativeOriginalCoarseTupleMenu NativeIncidentRankSelection NativeDirectionRankDichotomy
open NativeRetainedQueryMenu CompatibleTupleSelection SelfUniform
open scoped BigOperators

/-- Literal integer-grid ancestors, applied coordinatewise to terminal words. -/
def angularAncestor (fine coarse : ℕ) (u : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun v => u v / (2^(fine-coarse):ℕ)

def projectWord (fine coarse : ℕ) (u : List (Fin 3 → ℤ)) : List (Fin 3 → ℤ) :=
  u.map (angularAncestor fine coarse)

def spatialAncestor (fine coarse : ℕ) (u : Index) : Index :=
  fun v => u v / (2^(fine-coarse):ℕ)

lemma angularAncestor_label {n : ℕ} (D : FiniteScaleSource n)
    {m f : ℕ} (hmf : m ≤ f) (i : Fin n) :
    angularAncestor f m (angularLabel D (2^f) i)=angularLabel D (2^m) i := by
  funext v
  simp only [angularAncestor,angularLabel,Nat.cast_pow,Nat.cast_ofNat]
  exact (NativeDyadicParentCells.floor_dyadic_ancestor _ hmf).symm

lemma spatialLabel_coordinate {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (k : Index) (v : Fin 4) :
    spatialLabel D (2^m) k v=⌊(2:ℝ)^m*(cellCenter (mesh D) k v/64)⌋ := by
  change ⌊cellCenter (mesh D) k v/(64/((2^m:ℕ):ℝ))⌋=_
  congr 1
  rw [Nat.cast_pow,Nat.cast_ofNat,div_div_eq_mul_div]
  ring

lemma spatialAncestor_label {n : ℕ} (D : FiniteScaleSource n)
    {m f : ℕ} (hmf : m ≤ f) (k : Index) :
    spatialAncestor f m (spatialLabel D (2^f) k)=spatialLabel D (2^m) k := by
  funext v
  simp only [spatialAncestor,spatialLabel_coordinate]
  exact (NativeDyadicParentCells.floor_dyadic_ancestor _ hmf).symm

lemma angularTuple_cons {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (z : Fin n × Index) (xs : List (Fin n × Index)) :
    angularTuple D a m (z::xs)=angularLabel D (2^m) z.1::angularTuple D a m xs := rfl

lemma angularTuple_length {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (xs : List (Fin n × Index)) : (angularTuple D a m xs).length=xs.length := by
  simp only [angularTuple,coarseTuple,List.length_map]

lemma projectWord_angularTuple {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    {m f : ℕ} (hmf : m ≤ f) (xs : List (Fin n × Index)) :
    projectWord f m (angularTuple D a f xs)=angularTuple D a m xs := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
    change angularAncestor f m (angularLabel D (2^f) z.1)::projectWord f m (angularTuple D a f xs)=
      angularLabel D (2^m) z.1::angularTuple D a m xs
    rw [angularAncestor_label D hmf,ih]

lemma projectWord_self (m : ℕ) (u : List (Fin 3 → ℤ)) : projectWord m m u=u := by
  have he : angularAncestor m m=fun u : Fin 3 → ℤ => u := by
    funext u v
    simp only [angularAncestor,Nat.sub_self,pow_zero,Nat.cast_one,Int.ediv_one]
  simp only [projectWord,he,List.map_id_fun']
  rfl

/-- The finite grain count J is independent of the source-dependent stop.
Extend its already-constructed Fin schedule constantly past its endpoint. -/
def depth (J stop j : ℕ) : ℕ :=
  grainDepth J stop ⟨min j J,Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma depth_bounds (J stop j : ℕ) : depth J stop j ≤ stop :=
  (grainDepth_bounds J stop _).2

lemma depth_zero (J stop : ℕ) : depth J stop 0=min 6 stop := by
  have he : (⟨min 0 J,Nat.lt_succ_of_le (min_le_right 0 J)⟩ : Fin (J+1))=0 := by
    apply Fin.ext
    simp
  unfold depth
  rw [he,grainDepth_zero]

lemma depth_last (J stop : ℕ) (hJ : 0 < J) : depth J stop J=stop := by
  have he : (⟨min J J,Nat.lt_succ_of_le (min_le_right J J)⟩ : Fin (J+1))=Fin.last J := by
    apply Fin.ext
    simp
  unfold depth
  rw [he,grainDepth_last J stop hJ]

lemma depth_mono (J stop : ℕ) {i j : ℕ} (hij : i ≤ j) : depth J stop i ≤ depth J stop j := by
  apply grainDepth_mono
  exact min_le_min_right J hij

/-- Every genuine terminal angular word at its original point is retained
until compatible selection; no preliminary choice of one witness is made. -/
def terminalFamily {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (stop : ℕ)
    (E2 : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ) :
    Finset (Index × List (Fin 3 → ℤ)) :=
  goodPairs (E2.image Prod.snd) (fun k => angularMenu D a stop E2 k q ell)

lemma terminal_member {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (stop : ℕ)
    (E2 : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ)
    (p : Index × List (Fin 3 → ℤ)) (hp : p∈terminalFamily D a stop E2 q ell) :
    ∃xs∈chains (pointSet E2 p.1) (fun z => slopeVector D z.1) q ell,
      angularTuple D a stop xs=p.2 ∧ xs.length=ell ∧ ∀z∈xs,z∈E2 ∧ z.2=p.1 := by
  have hG := ((mem_goodPairs _ _ p).mp hp).2
  obtain ⟨xs,hxs,hmap⟩ := mem_image.mp hG
  refine ⟨xs,hxs,hmap,chains_length _ _ _ _ xs hxs,?_⟩
  intro z hz
  exact mem_filter.mp (chains_labels _ _ _ _ xs hxs z hz)

/-- Local witness provenance includes the actual fine chain, its unchanged
original incidences, and its proved transversality. -/
def LocalWitness {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (stop : ℕ)
    (E2 : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ)
    (p : Index × List (Fin 3 → ℤ)) : Prop :=
  ∃xs∈chains (pointSet E2 p.1) (fun z => slopeVector D z.1) q ell,
    angularTuple D a stop xs=p.2 ∧ xs.length=ell ∧
    (∀z∈xs,z∈E2 ∧ z.2=p.1) ∧
    LinearIndependent ℝ (fun i : Fin xs.length => slopeVector D (xs.get i).1) ∧
    q^(2*ell) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => slopeVector D (xs.get i).1)).det

lemma terminal_local_witness {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (stop : ℕ)
    (E2 : Finset (Fin n × Index)) (q : ℝ) (hq : 0 < q) (ell : ℕ)
    (p : Index × List (Fin 3 → ℤ)) (hp : p∈terminalFamily D a stop E2 q ell) :
    LocalWitness D a stop E2 q ell p :=
  angular_member_fine_witness D a stop E2 p.1 q hq ell p.2 ((mem_goodPairs _ _ p).mp hp).2

/-- A concrete finite product menu of successor labels, preserving word order. -/
def wordSuccessors {n : ℕ} (D : FiniteScaleSource n) (E1 : Finset (Fin n × Index))
    (m f : ℕ) (Q : Index) : List (Fin 3 → ℤ) → Finset (List (Fin 3 → ℤ))
  | [] => {[]}
  | u::us => ((successorLabels D E1 m f Q u) ×ˢ wordSuccessors D E1 m f Q us).image
      (fun z => z.1::z.2)

lemma wordSuccessors_card {n : ℕ} (D : FiniteScaleSource n) (E1 : Finset (Fin n × Index))
    (m f : ℕ) (Q : Index) (B : ℕ)
    (H : ∀u,(successorLabels D E1 m f Q u).card ≤ B) (us : List (Fin 3 → ℤ)) :
    (wordSuccessors D E1 m f Q us).card ≤ B^us.length := by
  induction us with
  | nil => simp only [wordSuccessors,card_singleton,List.length_nil,pow_zero]; exact le_rfl
  | cons u us ih =>
    calc
      _ ≤ ((successorLabels D E1 m f Q u) ×ˢ wordSuccessors D E1 m f Q us).card := card_image_le
      _ = (successorLabels D E1 m f Q u).card*(wordSuccessors D E1 m f Q us).card := card_product _ _
      _ ≤ B*B^us.length := Nat.mul_le_mul (H u) ih
      _ = _ := by rw [List.length_cons,pow_succ,Nat.mul_comm]

lemma angularTuple_mem_successors {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (E1 : Finset (Fin n × Index)) (m f : ℕ) (Q : Index)
    (xs : List (Fin n × Index))
    (H : ∀z∈xs,z∈E1 ∧ spatialLabel D (2^f) z.2=Q) :
    angularTuple D a f xs∈wordSuccessors D E1 m f Q (angularTuple D a m xs) := by
  induction xs with
  | nil => exact mem_singleton_self _
  | cons z xs ih =>
    rw [angularTuple_cons,angularTuple_cons,wordSuccessors]
    apply mem_image.mpr
    refine ⟨(angularLabel D (2^f) z.1,angularTuple D a f xs),mem_product.mpr ⟨?_,?_⟩,rfl⟩
    · exact mem_image.mpr ⟨z,mem_filter.mpr ⟨(H z (by simp)).1,(H z (by simp)).2,rfl⟩,rfl⟩
    · exact ih (fun v hv => H v (List.mem_cons_of_mem z hv))

/-- All words over a fixed finite alphabet, used only for the bounded root. -/
def allWords (A : Finset (Fin 3 → ℤ)) : ℕ → Finset (List (Fin 3 → ℤ))
  | 0 => {[]}
  | ell+1 => (A ×ˢ allWords A ell).image (fun z => z.1::z.2)

lemma allWords_card (A : Finset (Fin 3 → ℤ)) (ell : ℕ) :
    (allWords A ell).card=A.card^ell := by
  induction ell with
  | zero => simp only [allWords,card_singleton,pow_zero]
  | succ ell ih =>
    rw [allWords,card_image_of_injective _ NativeFiniteTupleFibers.cons_pair_injective,
      card_product,ih,pow_succ,Nat.mul_comm]

lemma angularTuple_mem_allWords {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (A : Finset (Fin 3 → ℤ)) (xs : List (Fin n × Index))
    (H : ∀z∈xs,angularLabel D (2^m) z.1∈A) :
    angularTuple D a m xs∈allWords A xs.length := by
  induction xs with
  | nil => exact mem_singleton_self _
  | cons z xs ih =>
    rw [angularTuple_cons,List.length_cons,allWords]
    exact mem_image.mpr ⟨(angularLabel D (2^m) z.1,angularTuple D a m xs),
      mem_product.mpr ⟨H z (by simp),ih (fun v hv => H v (List.mem_cons_of_mem z hv))⟩,rfl⟩

lemma angularLabel_mem_root_box {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : m ≤ 6) (i : Fin n) :
    angularLabel D (2^m) i∈integerBox 3 129 0 := by
  apply Fintype.mem_piFinset.mpr
  intro v
  have hs := slope_bound (D.line i) (h.1.2.2.2.2.1 i) (h.2.1.1 i) v
  have hN : ((2^m:ℕ):ℝ) ≤ 64 := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hm
  have hb : |((2^m:ℕ):ℝ)*slope (D.line i) v| ≤ 128 := by
    rw [abs_mul,abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans (by linarith)
  have hh := floor_mem_interval (x:=((2^m:ℕ):ℝ)*slope (D.line i) v) (y:=0) 128
    (by simpa only [sub_zero,Nat.cast_ofNat] using hb)
  simpa only [angularLabel,Int.floor_zero,Pi.zero_apply] using hh

/-- Root projected words are bounded by the actual north-chart slope box. -/
theorem projected_root_card {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (stop m : ℕ)
    (hm : m ≤ 6) (hms : m ≤ stop) (E2 : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ) (Q : Index) :
    (((terminalFamily D a stop E2 q ell).filter (fun p => spatialLabel D (2^m) p.1=Q)).image
      (fun p => projectWord stop m p.2)).card ≤ (259^3)^ell := by
  have hsub : ((terminalFamily D a stop E2 q ell).filter
      (fun p => spatialLabel D (2^m) p.1=Q)).image (fun p => projectWord stop m p.2) ⊆
      allWords (integerBox 3 129 0) ell := by
    intro u hu
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hu
    obtain ⟨xs,_hxs,hmap,hlen,_hlabels⟩ := terminal_member D a stop E2 q ell p (mem_filter.mp hp).1
    rw [←hmap,projectWord_angularTuple D a hms]
    rw [←hlen]
    exact angularTuple_mem_allWords D a m _ xs (fun z _hz => angularLabel_mem_root_box h m hm z.1)
  exact (card_le_card hsub).trans_eq (by rw [allWords_card,integerBox_card])

/-- Every projected successor word has literal E1 incidence witnesses at the
same original point in the stated child cube. The bound uses the original
reference menu, even when E2 was selected later. -/
theorem projected_successor_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (stop m f : ℕ) (hms : m ≤ stop) (hfs : f ≤ stop)
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (q : ℝ) (ell : ℕ)
    (Q : Index) (u : List (Fin 3 → ℤ)) (B : ℕ)
    (H : ∀v,(successorLabels D E1 m f Q v).card ≤ B) :
    (((terminalFamily D a stop E2 q ell).filter (fun p =>
      spatialLabel D (2^f) p.1=Q ∧ projectWord stop m p.2=u)).image
      (fun p => projectWord stop f p.2)).card ≤ B^ell := by
  let F := (terminalFamily D a stop E2 q ell).filter (fun p =>
    spatialLabel D (2^f) p.1=Q ∧ projectWord stop m p.2=u)
  by_cases hne : F.Nonempty
  · obtain ⟨p0,hp0⟩ := hne
    obtain ⟨xs0,_hxs0,hmap0,hlen0,_hlabels0⟩ :=
      terminal_member D a stop E2 q ell p0 (mem_filter.mp hp0).1
    have hu : u.length=ell := by
      rw [←(mem_filter.mp hp0).2.2,←hmap0,projectWord_angularTuple D a hms,angularTuple_length,hlen0]
    have hsub : F.image (fun p => projectWord stop f p.2) ⊆ wordSuccessors D E1 m f Q u := by
      intro v hv
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
      obtain ⟨xs,_hxs,hmap,_hlen,hlabels⟩ :=
        terminal_member D a stop E2 q ell p (mem_filter.mp hp).1
      rw [←hmap,projectWord_angularTuple D a hfs]
      have hcoarse : angularTuple D a m xs=u := by
        rw [←projectWord_angularTuple D a hms,hmap]
        exact (mem_filter.mp hp).2.2
      rw [←hcoarse]
      apply angularTuple_mem_successors D a E1 m f Q xs
      intro z hz
      exact ⟨h21 (hlabels z hz).1,by rw [(hlabels z hz).2]; exact (mem_filter.mp hp).2.1⟩
    exact (card_le_card hsub).trans (by simpa only [hu] using wordSuccessors_card D E1 m f Q B H u)
  · change (F.image (fun p => projectWord stop f p.2)).card ≤ _
    rw [not_nonempty_iff_eq_empty.mp hne,image_empty,card_empty]
    exact Nat.zero_le _

/-- A candidate node remembers both its original spatial cube and its actual
projected terminal word. Candidates themselves remain sets of original pairs. -/
def node {n : ℕ} (D : FiniteScaleSource n) (J stop j : ℕ)
    (p : Index × List (Fin 3 → ℤ)) : Index × List (Fin 3 → ℤ) :=
  (spatialLabel D (2^(depth J stop j)) p.1,projectWord stop (depth J stop j) p.2)

def ancestorNode (fine coarse : ℕ) (v : Index × List (Fin 3 → ℤ)) :
    Index × List (Fin 3 → ℤ) := (spatialAncestor fine coarse v.1,projectWord fine coarse v.2)

def candidate {n : ℕ} (D : FiniteScaleSource n) (J stop j : ℕ)
    (A : Finset (Index × List (Fin 3 → ℤ))) (v : Index × List (Fin 3 → ℤ)) :
    Finset (Index × List (Fin 3 → ℤ)) := A.filter (fun p => node D J stop j p=v)

lemma actual_node_ancestor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (J stop j : ℕ)
    (E2 : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ)
    (p : Index × List (Fin 3 → ℤ)) (hp : p∈terminalFamily D a stop E2 q ell) :
    ancestorNode (depth J stop (j+1)) (depth J stop j) (node D J stop (j+1) p)=
      node D J stop j p := by
  have hmf := depth_mono J stop (Nat.le_succ j)
  obtain ⟨xs,_hxs,hmap,_hlen,_hlabels⟩ := terminal_member D a stop E2 q ell p hp
  apply Prod.ext
  · exact spatialAncestor_label D hmf p.1
  · change projectWord (depth J stop (j+1)) (depth J stop j)
      (projectWord stop (depth J stop (j+1)) p.2)=projectWord stop (depth J stop j) p.2
    rw [←hmap,projectWord_angularTuple D a (depth_bounds J stop (j+1)),
      projectWord_angularTuple D a hmf,projectWord_angularTuple D a (depth_bounds J stop j)]

/-- Each occupied selected child has its deterministic occupied parent and an
actual surviving pair in their intersection. This does not assert containment
of an unpruned child candidate in any pruned parent candidate. -/
theorem selected_child_parent_trace {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (J stop j : ℕ) (E2 : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hP : P⊆terminalFamily D a stop E2 q ell)
    (v : Index × List (Fin 3 → ℤ)) (hv : v∈P.image (node D J stop (j+1))) :
    ancestorNode (depth J stop (j+1)) (depth J stop j) v∈P.image (node D J stop j) ∧
    (candidate D J stop (j+1) P v ∩
      candidate D J stop j P
        (ancestorNode (depth J stop (j+1)) (depth J stop j) v)).Nonempty := by
  obtain ⟨p,hp,hpv⟩ := mem_image.mp hv
  have hparent : node D J stop j p=ancestorNode (depth J stop (j+1)) (depth J stop j) v := by
    rw [←hpv]
    exact (actual_node_ancestor D a J stop j E2 q ell p (hP hp)).symm
  refine ⟨mem_image.mpr ⟨p,hp,hparent⟩,p,mem_inter.mpr ⟨?_,?_⟩⟩
  · exact mem_filter.mpr ⟨hp,hpv⟩
  · exact mem_filter.mpr ⟨hp,hparent⟩

/-- Explicit rounded single-coordinate capacity; no power absorption is hidden. -/
def singleCapacity {n : ℕ} (D : FiniteScaleSource n) (loss kappa : ℝ) (m f : ℕ) : ℕ :=
  ⌈(131^3*2401:ℝ)*D.thickness^(-loss)*
    ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-kappa)⌉₊

def selectionBudget {n : ℕ} (D : FiniteScaleSource n) (loss kappa : ℝ)
    (J stop ell j : ℕ) : ℕ :=
  if j=0 then (259^3)^ell else
    (singleCapacity D loss kappa (depth J stop (j-1)) (depth J stop j))^ell

/-- The result records retained actual pairs, their original-label mass, all
local fine-chain witnesses, and actual predecessor intersections. -/
def HasCompatibleCandidates {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (stop : ℕ)
    (E2 : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ) (w : Index → ℕ)
    (J : ℕ) (loss kappa : ℝ) : Prop :=
  ∃P⊆terminalFamily D a stop E2 q ell, ∃S⊆E2.image Prod.snd,
    S=P.image Prod.fst ∧
    (∀x y,x∈P → y∈P → x.1=y.1 → x=y) ∧
    SelfUniform.mass (fun p => w p.1) P=SelfUniform.mass w S ∧
    (∑k∈E2.image Prod.snd,w k*(angularMenu D a stop E2 k q ell).card) ≤
      (∏j∈range (J+1),selectionBudget D loss kappa J stop ell j)*SelfUniform.mass w S ∧
    (∀j,j<J+1 → ∀x y,x∈P → y∈P →
      spatialLabel D (2^(depth J stop j)) x.1=spatialLabel D (2^(depth J stop j)) y.1 →
      projectWord stop (depth J stop j) x.2=projectWord stop (depth J stop j) y.2) ∧
    (∀p∈P,LocalWitness D a stop E2 q ell p) ∧
    ∀j,j<J → ∀v∈P.image (node D J stop (j+1)),
      ancestorNode (depth J stop (j+1)) (depth J stop j) v∈P.image (node D J stop j) ∧
      (candidate D J stop (j+1) P v ∩
        candidate D J stop j P
          (ancestorNode (depth J stop (j+1)) (depth J stop j) v)).Nonempty

/-- Actual E2 terminal families satisfy every finite selection premise using
only the already-proved original E1 successor bound. The independent J is an
input, while the stop and actual source are allowed to be chosen later. -/
theorem select_actual_candidates {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ)
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1)
    (level J stop : ℕ) (hJ : 0 < J) (hstop : stop ≤ level)
    (q : ℝ) (hq : 0 < q) (ell : ℕ) (w : Index → ℕ) (loss kappa : ℝ)
    (H : ∀m f : ℕ,m ≤ f → f ≤ level → ∀Q : Index,∀u : Fin 3 → ℤ,
      ((successorLabels D E1 m f Q u).card:ℝ) ≤
        (131^3*2401:ℝ)*D.thickness^(-loss)*
          ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-kappa)) :
    HasCompatibleCandidates D a stop E2 q ell w J loss kappa := by
  let b := selectionBudget D loss kappa J stop ell
  let space := fun j k => spatialLabel D (2^(depth J stop j)) k
  let word := fun j u => projectWord stop (depth J stop j) u
  have hspace : ∀j,j+1<J+1 → ∀x y,space (j+1) x=space (j+1) y → space j x=space j y := by
    intro j _hj x y hxy
    have hh := congrArg (spatialAncestor (depth J stop (j+1)) (depth J stop j)) hxy
    simpa only [space,spatialAncestor_label D (depth_mono J stop (Nat.le_succ j))] using hh
  have hroot : ∀Q,
      (((terminalFamily D a stop E2 q ell).filter (fun p => space 0 p.1=Q)).image
        (fun p => word 0 p.2)).card ≤ b 0 := by
    intro Q
    have hm : depth J stop 0 ≤ 6 := by rw [depth_zero]; exact min_le_left _ _
    simpa [b,selectionBudget,space,word] using
      projected_root_card h a stop (depth J stop 0) hm (depth_bounds J stop 0) E2 q ell Q
  have hstep : ∀j,j+1<J+1 → ∀Q u,
      (((terminalFamily D a stop E2 q ell).filter (fun p =>
        space (j+1) p.1=Q ∧ word j p.2=u)).image (fun p => word (j+1) p.2)).card ≤ b (j+1) := by
    intro j _hj Q u
    have hmf := depth_mono J stop (Nat.le_succ j)
    have hfl := (depth_bounds J stop (j+1)).trans hstop
    have hmenu : ∀v,(successorLabels D E1 (depth J stop j) (depth J stop (j+1)) Q v).card ≤
        singleCapacity D loss kappa (depth J stop j) (depth J stop (j+1)) := by
      intro v
      have hh : ((successorLabels D E1 (depth J stop j) (depth J stop (j+1)) Q v).card:ℝ) ≤
          (singleCapacity D loss kappa (depth J stop j) (depth J stop (j+1)):ℝ) :=
        (H _ _ hmf hfl Q v).trans (Nat.le_ceil _)
      exact_mod_cast hh
    have hc := projected_successor_card D a stop (depth J stop j) (depth J stop (j+1))
      (depth_bounds J stop j) (depth_bounds J stop (j+1)) E1 E2 h21 q ell Q u _ hmenu
    simpa [b,selectionBudget,space,word] using hc
  have hfinal : ∀u,word J u=u := by
    intro u
    dsimp only [word]
    rw [depth_last J stop hJ,projectWord_self]
  obtain ⟨P,hP,S,hSsub,hS,hinj,hmass,hret,hcompat⟩ :=
    weighted_good_tuple_family_selection w (E2.image Prod.snd)
      (fun k => angularMenu D a stop E2 k q ell) space word b J hspace hroot hstep hfinal
  refine ⟨P,hP,S,hSsub,hS,hinj,hmass,hret,hcompat,?_,?_⟩
  · exact fun p hp => terminal_local_witness D a stop E2 q hq ell p (hP hp)
  · intro j _hj v hv
    exact selected_child_parent_trace D a J stop j E2 q ell P hP v hv

open NativeJointUniformCoarseRelations NativeConditionedPairMenu NativeTwoScaleConfiguration
open NativeFixedCompactKakeyaExponent NativeFixedSizeScaleMenu NativeMiddleWindowBalance
open NativeAllTwoScaleConfiguration

/-- Direct assembly from the one original master witness and any later E2.
No menu-cardinality certificate, adaptive pointwise uniformity, or candidate
retention assumption is an input. Ceilings and the finite product remain
explicit for the subsequent small-tau parameter budget with J fixed first. -/
theorem from_master_reference {n d g L level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed t : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1)
    (schedule : Fin (g+1) → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (ht : 0 < t) (heta : 0 ≤ eta) (hseed : seed ≤ t/16384)
    (hg : 0 < g) (hgl : g ≤ level)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow t) ((t/16)/1000)/4)
    (hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule = fullSchedule t ht g level)
    (hcore : IsCore D original R a eta zeta d (g+1) L Rel
      (fun j => 2^(schedule j).val) E1)
    (hcost : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f t)
    (J stop : ℕ) (hJ : 0 < J) (hstop : stop ≤ level)
    (q : ℝ) (hq : 0 < q) (ell : ℕ) (w : Index → ℕ) :
    HasCompatibleCandidates D a stop E2 q ell w J (3*t) extremalExponent := by
  have H := NativeMasterSuccessorMenu.from_master_reference h original R E1 schedule Rel
    ht heta hseed hg hgl hgrid hbackbone hschedule hcore hcost hconditioned hreference
  exact select_actual_candidates h a E1 E2 h21 level J stop hJ hstop q hq ell w
    (3*t) extremalExponent H

end NativeCompatibleAngularCandidates
