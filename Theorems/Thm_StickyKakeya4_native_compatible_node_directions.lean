import Theorems.Thm_StickyKakeya4_native_compatible_angular_candidates
import Theorems.Thm_StickyKakeya4_native_global_angular_representatives
import Theorems.Thm_StickyKakeya4_native_rank_one_slope_cap
import Theorems.Thm_StickyKakeya4_native_separated_fiber_iteration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4800000

noncomputable section
namespace NativeCompatibleNodeDirections
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeSpatialAngularGeometry
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeOriginalAngularTupleMenu
open NativeOriginalCoarseTupleMenu NativeCompatibleAngularCandidates NativeGlobalAngularRepresentatives

/-- Actual occupied spatial nodes of the prescribed retained original points. -/
def nodes {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (S : Finset Index) : Finset Index :=
  S.image (spatialLabel D (2^m))

/-- A node tuple is a genuine global fine witness; its incident anchors may
vary with the current old point. Bounds hold for the original slope vectors.
No plane common to distinct points and no rounded-vector transversality is asserted. -/
def IsNodeDirectionSystem {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (E : Finset (Fin n × Index)) (S : Finset Index) (q : ℝ) (ell : ℕ)
    (point : Index → Index) (tuple : Index → Fin ell → (Fin n × Index))
    (anchor : Index → Fin ell → Fin n) : Prop :=
  (∀Q∈nodes D m S, point Q∈E.image Prod.snd ∧
    (∀i,tuple Q i∈E ∧ (tuple Q i).2=point Q) ∧
    List.ofFn (tuple Q)∈chains (pointSet E (point Q)) (fun z => slopeVector D z.1) q ell ∧
    Separated (fun z => slopeVector D z.1) q (List.ofFn (tuple Q)) ∧
    LinearIndependent ℝ (fun i => slopeVector D (tuple Q i).1) ∧
    q^(2*ell) ≤ (Matrix.gram ℝ (fun i => slopeVector D (tuple Q i).1)).det) ∧
  (∀k∈S,∀i,(anchor k i,k)∈E ∧
    (parentLabel D a (2^m) (anchor k i)).1=
      (parentLabel D a (2^m) (tuple (spatialLabel D (2^m) k) i).1).1) ∧
  (∀Q i, ‖slopeVector D (tuple Q i).1‖ ≤ 2 ∧ slopeVector D (tuple Q i).1 (3:Fin 4)=1)

lemma angular_ofFn_coordinate {n ell : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (u v : Fin ell → (Fin n × Index))
    (he : angularTuple D a m (List.ofFn u)=angularTuple D a m (List.ofFn v)) (i : Fin ell) :
    (parentLabel D a (2^m) (u i).1).1=(parentLabel D a (2^m) (v i).1).1 := by
  have hh : (fun j => (parentLabel D a (2^m) (u j).1).1)=
      (fun j => (parentLabel D a (2^m) (v j).1).1) := by
    apply List.ofFn_injective
    simpa only [angularTuple,coarseTuple,List.map_ofFn,Function.comp_def] using he
  exact congrFun hh i

/-- The terminal witness has the fixed coordinate type needed by the packet
caller, with literal old incidences and no replacement of its point. -/
theorem terminal_fixed_tuple {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (stop : ℕ)
    (E : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ) (p : Index × List (Fin 3 → ℤ))
    (hp : p∈terminalFamily D a stop E q ell) :
    ∃t : Fin ell → (Fin n × Index),
      (∀i,t i∈E ∧ (t i).2=p.1) ∧
      List.ofFn t∈chains (pointSet E p.1) (fun z => slopeVector D z.1) q ell ∧
      angularTuple D a stop (List.ofFn t)=p.2 := by
  obtain ⟨xs,hxs,hmap,hlen,hlabels⟩ := terminal_member D a stop E q ell p hp
  subst ell
  refine ⟨xs.get,?_,?_,?_⟩
  · exact fun i => hlabels (xs.get i) (List.get_mem xs i)
  · simpa only [List.ofFn_get] using hxs
  · simpa only [List.ofFn_get] using hmap

/-- Projecting a retained terminal word gives an actually occupied global
angular word at every coarser depth, witnessed by the same original chain. -/
theorem projected_word_global {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (stop m : ℕ) (hms : m ≤ stop) (E : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ)
    (p : Index × List (Fin 3 → ℤ)) (hp : p∈terminalFamily D a stop E q ell) :
    projectWord stop m p.2∈globalAngularMenu D a m E q ell := by
  have hpS := ((CompatibleTupleSelection.mem_goodPairs _ _ p).mp hp).1
  obtain ⟨xs,hxs,hmap,_hlen,_hlabels⟩ := terminal_member D a stop E q ell p hp
  apply mem_biUnion.mpr
  refine ⟨p.1,hpS,?_⟩
  apply mem_image.mpr
  refine ⟨xs,hxs,?_⟩
  rw [←hmap,projectWord_angularTuple D a hms]

/-- Compatibility supplies the UNIQUE coarse word in an occupied spatial
node. The value is a member of the previously constructed global word menu. -/
theorem exists_node_word {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (stop m : ℕ) (hms : m ≤ stop) (E : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hP : P⊆terminalFamily D a stop E q ell)
    (HC : ∀x y,x∈P → y∈P → spatialLabel D (2^m) x.1=spatialLabel D (2^m) y.1 →
      projectWord stop m x.2=projectWord stop m y.2)
    (Q : Index) (hQ : Q∈nodes D m (P.image Prod.fst)) :
    ∃word : globalAngularMenu D a m E q ell,
      ∀p∈P,spatialLabel D (2^m) p.1=Q → projectWord stop m p.2=word.val := by
  obtain ⟨k,hk,hkQ⟩ := mem_image.mp hQ
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
  refine ⟨⟨projectWord stop m p.2,projected_word_global D a stop m hms E q ell p (hP hp)⟩,?_⟩
  intro t ht htQ
  exact HC t p ht hp (htQ.trans hkQ.symm)

/-- Deterministic on the PRESCRIBED retained pair family P: choose global
fine representatives once per angular word, then use compatibility to assign
them to nodes and construct genuine incident local anchors at every old point. -/
theorem exists_node_direction_system {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (stop m : ℕ) (hms : m ≤ stop)
    (E : Finset (Fin n × Index)) (q : ℝ) (hq : 0 < q) (ell : ℕ)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hP : P⊆terminalFamily D a stop E q ell)
    (HC : ∀x y,x∈P → y∈P → spatialLabel D (2^m) x.1=spatialLabel D (2^m) y.1 →
      projectWord stop m x.2=projectWord stop m y.2) :
    ∃ (point : Index → Index) (tuple : Index → Fin ell → (Fin n × Index))
      (anchor : Index → Fin ell → Fin n),
      IsNodeDirectionSystem D a m E (P.image Prod.fst) q ell point tuple anchor ∧
      (∀p∈P,angularTuple D a m (List.ofFn (tuple (spatialLabel D (2^m) p.1)))=
        projectWord stop m p.2) ∧
      (∀x y,x∈P → y∈P → projectWord stop m x.2=projectWord stop m y.2 →
        tuple (spatialLabel D (2^m) x.1)=tuple (spatialLabel D (2^m) y.1) ∧
        point (spatialLabel D (2^m) x.1)=point (spatialLabel D (2^m) y.1)) := by
  let S := P.image Prod.fst
  let V := nodes D m S
  have HW (Q : V) := exists_node_word D a stop m hms E q ell P hP HC Q.val Q.property
  choose word hword using HW
  obtain ⟨globalPoint,globalTuple,HG⟩ := exists_global_representatives D a m E q hq ell
  let first : Fin n := ⟨0,h.1.1⟩
  let point : Index → Index := fun Q => if hQ : Q∈V then globalPoint (word ⟨Q,hQ⟩) else 0
  let tuple : Index → Fin ell → (Fin n × Index) :=
    fun Q => if hQ : Q∈V then globalTuple (word ⟨Q,hQ⟩) else fun _ => (first,0)
  have hpoint (Q : Index) (hQ : Q∈V) : point Q=globalPoint (word ⟨Q,hQ⟩) := by
    simp only [point,dif_pos hQ]
  have htuple (Q : Index) (hQ : Q∈V) : tuple Q=globalTuple (word ⟨Q,hQ⟩) := by
    simp only [tuple,dif_pos hQ]
  have hnode (p : Index × List (Fin 3 → ℤ)) (hp : p∈P) : spatialLabel D (2^m) p.1∈V :=
    mem_image_of_mem _ (mem_image_of_mem Prod.fst hp)
  have hmap (p : Index × List (Fin 3 → ℤ)) (hp : p∈P) :
      angularTuple D a m (List.ofFn (tuple (spatialLabel D (2^m) p.1)))=projectWord stop m p.2 := by
    rw [htuple _ (hnode p hp)]
    exact (HG (word ⟨_,hnode p hp⟩)).2.2.2.1.trans (hword ⟨_,hnode p hp⟩ p hp rfl).symm
  have HA (k : S) : ∃t : Fin ell → Fin n,∀i,(t i,k.val)∈E ∧
      (parentLabel D a (2^m) (t i)).1=
        (parentLabel D a (2^m) (tuple (spatialLabel D (2^m) k.val) i).1).1 := by
    obtain ⟨p,hp,hpk⟩ := mem_image.mp k.property
    obtain ⟨t,ht,hchain,hstop⟩ := terminal_fixed_tuple D a stop E q ell p (hP hp)
    have hm : angularTuple D a m (List.ofFn t)=projectWord stop m p.2 := by
      rw [←hstop,projectWord_angularTuple D a hms]
    have he := hm.trans (hmap p hp).symm
    refine ⟨fun i => (t i).1,?_⟩
    intro i
    have hti : (t i).2=k.val := (ht i).2.trans hpk
    refine ⟨?_,?_⟩
    · simpa only [←hti] using (ht i).1
    · have hh := angular_ofFn_coordinate D a m t (tuple (spatialLabel D (2^m) p.1)) he i
      simpa only [hpk] using hh
  choose localAnchor hlocal using HA
  let anchor : Index → Fin ell → Fin n :=
    fun k => if hk : k∈S then localAnchor ⟨k,hk⟩ else fun _ => first
  refine ⟨point,tuple,anchor,?_,hmap,?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro Q hQ
      obtain ⟨hp,ht,hchain,_hmap,hli,hgram⟩ := HG (word ⟨Q,hQ⟩)
      rw [hpoint Q hQ,htuple Q hQ]
      exact ⟨hp,ht,hchain,chains_separated _ _ _ _ _ hchain,hli,hgram⟩
    · intro k hk i
      change k∈S at hk
      simpa only [anchor,dif_pos hk] using hlocal ⟨k,hk⟩ i
    · exact fun Q i => ⟨NativeRankOneSlopeCap.slopeVector_norm_le_two h _,slopeVector_last D _⟩
  · intro x y hx hy hxy
    have hwordeq : word ⟨_,hnode x hx⟩=word ⟨_,hnode y hy⟩ := by
      apply Subtype.ext
      exact (hword ⟨_,hnode x hx⟩ x hx rfl).symm.trans
        (hxy.trans (hword ⟨_,hnode y hy⟩ y hy rfl))
    rw [htuple _ (hnode x hx),htuple _ (hnode y hy),hpoint _ (hnode x hx),hpoint _ (hnode y hy),hwordeq]
    exact ⟨rfl,rfl⟩

/-- Later point refinements inherit the IDENTICAL original directions and
anchors. No new tuple, witness point, or angular choice is selected. -/
theorem node_direction_system_mono {n ell m : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {E : Finset (Fin n × Index)} {S T : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor) (hTS : T⊆S) :
    IsNodeDirectionSystem D a m E T q ell point tuple anchor := by
  refine ⟨?_,?_,H.2.2⟩
  · exact fun Q hQ => H.1 Q ((image_subset_image hTS) hQ)
  · exact fun k hk i => H.2.1 k (hTS hk) i

/-- Prefix iteration traverses the original separated chain in reverse.
This is a deterministic index change, with no new tuple choice. -/
def stageDirectionIndex {n ell : ℕ} (tuple : Index → Fin ell → (Fin n × Index))
    (i : Fin ell) (Q : Index) : Fin n := (tuple Q i.rev).1

def stageAnchorIndex {n ell : ℕ} (anchor : Index → Fin ell → Fin n)
    (i : Fin ell) (k : Index) : Fin n := anchor k i.rev

/-- Exact installed-direction readback to the existing reverseFamily API.
Only the equality between the original tuple length and ell is transported. -/
theorem stage_direction_readback {n ell : ℕ} (D : FiniteScaleSource n)
    (tuple : Index → Fin ell → (Fin n × Index)) (Q : Index)
    (i : Fin (List.ofFn (tuple Q)).length) :
    NativeSeparatedFiberIteration.reverseFamily (fun z : Fin n × Index => slopeVector D z.1)
      (List.ofFn (tuple Q)) i=
      slopeVector D (stageDirectionIndex tuple (Fin.cast (by simp) i) Q) := by
  simp only [NativeSeparatedFiberIteration.reverseFamily,List.get_ofFn,stageDirectionIndex,Fin.cast_rev]

/-- The same reversal supplies actual local incident anchors for the installed
stage direction, preserving the original old point and its retained edge. -/
theorem stage_anchor_readback {n ell m : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor)
    (k : Index) (hk : k∈S) (i : Fin ell) :
    (stageAnchorIndex anchor i k,k)∈E ∧
      (parentLabel D a (2^m) (stageAnchorIndex anchor i k)).1=
        (parentLabel D a (2^m) (stageDirectionIndex tuple i (spatialLabel D (2^m) k))).1 :=
  H.2.1 k hk i.rev

theorem stage_direction_bounds {n ell m : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor) (Q : Index) (i : Fin ell) :
    ‖slopeVector D (stageDirectionIndex tuple i Q)‖ ≤ 2 ∧
      slopeVector D (stageDirectionIndex tuple i Q) (3:Fin 4)=1 := H.2.2 Q i.rev

/-- The reversal agrees at the level of original tube indices, so a consumer
never needs to infer index equality from equality of geometric vectors. -/
theorem stage_index_readback {n ell : ℕ}
    (tuple : Index → Fin ell → (Fin n × Index)) (Q : Index)
    (i : Fin (List.ofFn (tuple Q)).length) :
    stageDirectionIndex tuple (Fin.cast (by simp) i) Q=
      ((List.ofFn (tuple Q)).get i.rev).1 := by
  simp only [List.get_ofFn,stageDirectionIndex,Fin.cast_rev]

/-- Natural-number stages use the same installed original indices. The
irrelevant stages beyond ell use a native original index without a new choice. -/
def natStageDirectionIndex {n ell : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (tuple : Index → Fin ell → (Fin n × Index)) (r : ℕ) (Q : Index) : Fin n :=
  if hr : r < ell then stageDirectionIndex tuple ⟨r,hr⟩ Q else ⟨0,h.1.1⟩

def natStageAnchorIndex {n ell : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (anchor : Index → Fin ell → Fin n) (r : ℕ) (k : Index) : Fin n :=
  if hr : r < ell then stageAnchorIndex anchor ⟨r,hr⟩ k else ⟨0,h.1.1⟩

/-- Exact original-index input required by the actual chain iteration. -/
theorem nat_stage_index_readback {n ell : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (tuple : Index → Fin ell → (Fin n × Index)) (Q : Index)
    (i : Fin (List.ofFn (tuple Q)).length) :
    natStageDirectionIndex h tuple i.val Q=((List.ofFn (tuple Q)).get i.rev).1 := by
  have hi : i.val < ell := by simpa only [List.length_ofFn] using i.isLt
  rw [natStageDirectionIndex,dif_pos hi]
  exact stage_index_readback tuple Q i

/-- Natural-stage local anchors retain their actual old point and incidence,
with the precise angular match to the corresponding installed stage direction. -/
theorem nat_stage_anchor_readback {n ell m : ℕ} {D : FiniteScaleSource n} {a q eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor)
    (k : Index) (hk : k∈S) (r : ℕ) (hr : r < ell) :
    (natStageAnchorIndex h anchor r k,k)∈E ∧
      (parentLabel D a (2^m) (natStageAnchorIndex h anchor r k)).1=
        (parentLabel D a (2^m) (natStageDirectionIndex h tuple r (spatialLabel D (2^m) k))).1 := by
  rw [natStageAnchorIndex,natStageDirectionIndex,dif_pos hr,dif_pos hr]
  exact stage_anchor_readback H k hk ⟨r,hr⟩

/-- The actual compatible-candidate fields supply all grain depths on one
prescribed P, with one fixed tuple/anchor system at every depth. -/
theorem exists_scheduled_node_directions {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (stop J : ℕ)
    (E : Finset (Fin n × Index)) (q : ℝ) (hq : 0 < q) (ell : ℕ)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hP : P⊆terminalFamily D a stop E q ell)
    (HC : ∀j,j<J+1 → ∀x y,x∈P → y∈P →
      spatialLabel D (2^(depth J stop j)) x.1=spatialLabel D (2^(depth J stop j)) y.1 →
      projectWord stop (depth J stop j) x.2=projectWord stop (depth J stop j) y.2) :
    ∃ (point : Fin (J+1) → Index → Index)
      (tuple : Fin (J+1) → Index → Fin ell → (Fin n × Index))
      (anchor : Fin (J+1) → Index → Fin ell → Fin n),
      ∀j, IsNodeDirectionSystem D a (depth J stop j.val) E (P.image Prod.fst) q ell
        (point j) (tuple j) (anchor j) ∧
        (∀p∈P,angularTuple D a (depth J stop j.val)
          (List.ofFn (tuple j (spatialLabel D (2^(depth J stop j.val)) p.1)))=
            projectWord stop (depth J stop j.val) p.2) ∧
        (∀x y,x∈P → y∈P →
          projectWord stop (depth J stop j.val) x.2=projectWord stop (depth J stop j.val) y.2 →
          tuple j (spatialLabel D (2^(depth J stop j.val)) x.1)=
            tuple j (spatialLabel D (2^(depth J stop j.val)) y.1) ∧
          point j (spatialLabel D (2^(depth J stop j.val)) x.1)=
            point j (spatialLabel D (2^(depth J stop j.val)) y.1)) := by
  have H (j : Fin (J+1)) := exists_node_direction_system h a stop (depth J stop j.val)
    (depth_bounds J stop j.val) E q hq ell P hP (HC j.val j.isLt)
  choose point tuple anchor hsystem using H
  exact ⟨point,tuple,anchor,hsystem⟩

end NativeCompatibleNodeDirections
