/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Countable.FirstCountable

/-!
# Second-countable topological spaces
-/

@[expose] public section

noncomputable section

open Topology Filter Set

namespace TopologicalSpace

universe u

variable {α : Type u} [t : TopologicalSpace α]

variable (α) in
/-- A second-countable space is one with a countable basis. -/
class _root_.SecondCountableTopology : Prop where
  /-- There exists a countable set of sets that generates the topology. -/
  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b

protected theorem IsTopologicalBasis.secondCountableTopology {b : Set (Set α)}
    (hb : IsTopologicalBasis b) (hc : b.Countable) : SecondCountableTopology α :=
  ⟨⟨b, hc, hb.eq_generateFrom⟩⟩

lemma SecondCountableTopology.mk' {α} {b : Set (Set α)} (hc : b.Countable) :
    @SecondCountableTopology α (generateFrom b) :=
  @SecondCountableTopology.mk α (generateFrom b) ⟨b, hc, rfl⟩

instance _root_.Finite.toSecondCountableTopology [Finite α] : SecondCountableTopology α where
  is_open_generated_countable :=
    ⟨_, {U | IsOpen U}.to_countable, TopologicalSpace.isTopologicalBasis_opens.eq_generateFrom⟩

variable (α)

theorem exists_countable_basis [SecondCountableTopology α] :
    ∃ b : Set (Set α), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := by
  obtain ⟨b, hb₁, hb₂⟩ := @SecondCountableTopology.is_open_generated_countable α _ _
  refine ⟨_, ?_, notMem_sdiff_of_mem ?_, (isTopologicalBasis_of_subbasis hb₂).sdiff_empty⟩
  exacts [((countable_ofPred_finite_subset hb₁).image _).mono sdiff_subset, rfl]

theorem exists_seq_basis [SecondCountableTopology α] :
    ∃ b : ℕ → Set α, IsTopologicalBasis (range b) := by
  obtain ⟨t, ht⟩ := TopologicalSpace.exists_countable_basis α
  by_cases! hn : t.Nonempty
  · obtain ⟨b, rfl⟩ := ht.1.exists_eq_range hn
    exact ⟨b, ht.2.2⟩
  · exact ⟨fun n => ∅, by simp_all⟩

/-- A countable topological basis of `α`. -/
def countableBasis [SecondCountableTopology α] : Set (Set α) :=
  (exists_countable_basis α).choose

theorem countable_countableBasis [SecondCountableTopology α] : (countableBasis α).Countable :=
  (exists_countable_basis α).choose_spec.1

instance encodableCountableBasis [SecondCountableTopology α] : Encodable (countableBasis α) :=
  (countable_countableBasis α).toEncodable

theorem empty_notMem_countableBasis [SecondCountableTopology α] : ∅ ∉ countableBasis α :=
  (exists_countable_basis α).choose_spec.2.1

theorem isBasis_countableBasis [SecondCountableTopology α] :
    IsTopologicalBasis (countableBasis α) :=
  (exists_countable_basis α).choose_spec.2.2

theorem eq_generateFrom_countableBasis [SecondCountableTopology α] :
    ‹TopologicalSpace α› = generateFrom (countableBasis α) :=
  (isBasis_countableBasis α).eq_generateFrom

variable {α}

theorem isOpen_of_mem_countableBasis [SecondCountableTopology α] {s : Set α}
    (hs : s ∈ countableBasis α) : IsOpen s :=
  (isBasis_countableBasis α).isOpen hs

theorem nonempty_of_mem_countableBasis [SecondCountableTopology α] {s : Set α}
    (hs : s ∈ countableBasis α) : s.Nonempty :=
  nonempty_iff_ne_empty.2 <| ne_of_mem_of_not_mem hs <| empty_notMem_countableBasis α

variable (α)

-- see Note [lower instance priority]
instance (priority := 100) SecondCountableTopology.to_firstCountableTopology
    [SecondCountableTopology α] : FirstCountableTopology α :=
  ⟨fun _ => HasCountableBasis.isCountablyGenerated <|
      ⟨(isBasis_countableBasis α).nhds_hasBasis,
        (countable_countableBasis α).mono inter_subset_left⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) [Countable α] [FirstCountableTopology α] :
    SecondCountableTopology α where
  is_open_generated_countable := by
    -- The countable union of the countable neighborhood bases at each point is a countable basis.
    choose b hxb hbb using fun x : α => (nhds_basis_opens x).exists_antitone_subbasis
    use range b.uncurry, countable_range b.uncurry
    apply le_antisymm
    · rw [le_generateFrom_iff_subset_isOpen]
      rintro _ ⟨⟨x, n⟩, rfl⟩
      exact (hxb x n).right
    · rw [le_iff_nhds]
      intro x
      rw [(hbb x).ge_iff]
      intro n _
      refine @IsOpen.mem_nhds α (generateFrom (range b.uncurry)) x (b x n) ?_ (hxb x n).left
      exact isOpen_generateFrom_of_mem ⟨⟨x, n⟩, rfl⟩

/-- If `β` is a second-countable space, then its induced topology via
`f` on `α` is also second-countable. -/
theorem secondCountableTopology_induced (α β) [t : TopologicalSpace β] [SecondCountableTopology β]
    (f : α → β) : @SecondCountableTopology α (t.induced f) := by
  rcases @SecondCountableTopology.is_open_generated_countable β _ _ with ⟨b, hb, eq⟩
  let := t.induced f
  refine { is_open_generated_countable := ⟨preimage f '' b, hb.image _, ?_⟩ }
  rw [eq, induced_generateFrom_eq]

variable {α}

instance Subtype.secondCountableTopology (s : Set α) [SecondCountableTopology α] :
    SecondCountableTopology s :=
  secondCountableTopology_induced s α (↑)

lemma secondCountableTopology_iInf {α ι} [Countable ι] {t : ι → TopologicalSpace α}
    (ht : ∀ i, @SecondCountableTopology α (t i)) : @SecondCountableTopology α (⨅ i, t i) := by
  rw [funext fun i => @eq_generateFrom_countableBasis α (t i) (ht i), ← generateFrom_iUnion]
  exact SecondCountableTopology.mk' <|
    countable_iUnion fun i => @countable_countableBasis _ (t i) (ht i)

-- TODO: more fine grained instances for `FirstCountableTopology`, `SeparableSpace`, `T2Space`, ...
instance {β : Type*} [TopologicalSpace β] [SecondCountableTopology α] [SecondCountableTopology β] :
    SecondCountableTopology (α × β) :=
  ((isBasis_countableBasis α).prod (isBasis_countableBasis β)).secondCountableTopology <|
    (countable_countableBasis α).image2 (countable_countableBasis β) _

instance {ι : Type*} {X : ι → Type*} [Countable ι] [∀ a, TopologicalSpace (X a)]
    [∀ a, SecondCountableTopology (X a)] : SecondCountableTopology (∀ a, X a) :=
  secondCountableTopology_iInf fun _ => secondCountableTopology_induced _ _ _

-- see Note [lower instance priority]
instance (priority := 100) SecondCountableTopology.to_separableSpace [SecondCountableTopology α] :
    SeparableSpace α := by
  choose p hp using fun s : countableBasis α => nonempty_of_mem_countableBasis s.2
  exact ⟨⟨range p, countable_range _, (isBasis_countableBasis α).dense_iff.2 fun o ho _ =>
          ⟨p ⟨o, ho⟩, hp ⟨o, _⟩, mem_range_self _⟩⟩⟩

/-- A countable open cover induces a second-countable topology if all open covers
are themselves second countable. -/
theorem secondCountableTopology_of_countable_cover {ι} [Countable ι] {U : ι → Set α}
    [∀ i, SecondCountableTopology (U i)] (Uo : ∀ i, IsOpen (U i)) (hc : ⋃ i, U i = univ) :
    SecondCountableTopology α :=
  haveI : IsTopologicalBasis (⋃ i, image ((↑) : U i → α) '' countableBasis (U i)) :=
    isTopologicalBasis_of_cover Uo hc fun i => isBasis_countableBasis (U i)
  this.secondCountableTopology (countable_iUnion fun _ => (countable_countableBasis _).image _)

/-- In a second-countable space, an open set, given as a union of open sets,
is equal to the union of countably many of those sets.
In particular, any open covering of `α` has a countable subcover: α is a Lindelöf space. -/
theorem isOpen_iUnion_countable [SecondCountableTopology α] {ι} (s : ι → Set α)
    (H : ∀ i, IsOpen (s i)) : ∃ T : Set ι, T.Countable ∧ ⋃ i ∈ T, s i = ⋃ i, s i := by
  let B := { b ∈ countableBasis α | ∃ i, b ⊆ s i }
  choose f hf using fun b : B => b.2.2
  have : Countable B := ((countable_countableBasis α).mono (sep_subset _ _)).to_subtype
  refine ⟨_, countable_range f, (iUnion₂_subset_iUnion _ _).antisymm (sUnion_subset ?_)⟩
  rintro _ ⟨i, rfl⟩ x xs
  rcases (isBasis_countableBasis α).exists_subset_of_mem_open xs (H _) with ⟨b, hb, xb, bs⟩
  exact ⟨_, ⟨_, rfl⟩, _, ⟨⟨⟨_, hb, _, bs⟩, rfl⟩, rfl⟩, hf _ xb⟩

theorem isOpen_biUnion_countable [SecondCountableTopology α] {ι : Type*} (I : Set ι) (s : ι → Set α)
    (H : ∀ i ∈ I, IsOpen (s i)) : ∃ T ⊆ I, T.Countable ∧ ⋃ i ∈ T, s i = ⋃ i ∈ I, s i := by
  simp_rw [← Subtype.exists_set_subtype, biUnion_image]
  rcases isOpen_iUnion_countable (fun i : I ↦ s i) fun i ↦ H i i.2 with ⟨T, hTc, hU⟩
  exact ⟨T, hTc.image _, hU.trans <| iUnion_subtype ..⟩

theorem isOpen_sUnion_countable [SecondCountableTopology α] (S : Set (Set α))
    (H : ∀ s ∈ S, IsOpen s) : ∃ T : Set (Set α), T.Countable ∧ T ⊆ S ∧ ⋃₀ T = ⋃₀ S := by
  simpa only [and_left_comm, sUnion_eq_biUnion] using! isOpen_biUnion_countable S id H

/-- In a topological space with second countable topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
theorem countable_cover_nhds [SecondCountableTopology α] {f : α → Set α} (hf : ∀ x, f x ∈ 𝓝 x) :
    ∃ s : Set α, s.Countable ∧ ⋃ x ∈ s, f x = univ := by
  rcases isOpen_iUnion_countable (fun x => interior (f x)) fun x => isOpen_interior with
    ⟨s, hsc, hsU⟩
  suffices ⋃ x ∈ s, interior (f x) = univ from
    ⟨s, hsc, flip eq_univ_of_subset this <| iUnion₂_mono fun _ _ => interior_subset⟩
  simp only [hsU, eq_univ_iff_forall, mem_iUnion]
  exact fun x => ⟨x, mem_interior_iff_mem_nhds.2 (hf x)⟩

theorem countable_cover_nhdsWithin [SecondCountableTopology α] {f : α → Set α} {s : Set α}
    (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) : ∃ t ⊆ s, t.Countable ∧ s ⊆ ⋃ x ∈ t, f x := by
  have : ∀ x : s, (↑) ⁻¹' f x ∈ 𝓝 x := fun x => preimage_coe_mem_nhds_subtype.2 (hf x x.2)
  rcases countable_cover_nhds this with ⟨t, htc, htU⟩
  refine ⟨(↑) '' t, Subtype.coe_image_subset _ _, htc.image _, fun x hx => ?_⟩
  simp only [biUnion_image, eq_univ_iff_forall, ← preimage_iUnion, mem_preimage] at htU ⊢
  exact htU ⟨x, hx⟩

/-- In a second countable topological space, any open set is a countable union of elements in a
given topological basis. -/
lemma IsTopologicalBasis.exists_countable_biUnion_of_isOpen [SecondCountableTopology α]
    {t : Set (Set α)} (ht : IsTopologicalBasis t) {u : Set α} (hu : IsOpen u) :
    ∃ s ⊆ t, s.Countable ∧ u = ⋃ a ∈ s, a := by
  have A : ∀ x ∈ u, ∃ a ∈ t, x ∈ a ∧ a ⊆ u :=
    fun x hx ↦ ht.exists_subset_of_mem_open hx hu
  choose! a hat xa au using A
  obtain ⟨T, T_count, hT⟩ : ∃ T : Set u, T.Countable ∧ ⋃ i ∈ T, a i = ⋃ (i : u), a i := by
    apply isOpen_iUnion_countable _
    rintro ⟨x, hx⟩
    exact ht.isOpen (hat x hx)
  refine ⟨(fun (x : u) ↦ a x) '' T, ?_, T_count.image _, ?_⟩
  · simp only [image_subset_iff]
    rintro ⟨x, xu⟩ -
    exact hat x xu
  rw [biUnion_image, hT]
  apply Subset.antisymm
  · intro x hx
    simp
    grind
  · simp
    grind

/-- In a second countable topological space, any topological basis contains a countable subset
which is also a topological basis. -/
lemma IsTopologicalBasis.exists_countable
    [SecondCountableTopology α] {t : Set (Set α)} (ht : IsTopologicalBasis t) :
    ∃ s ⊆ t, s.Countable ∧ IsTopologicalBasis s := by
  have A : ∀ u ∈ countableBasis α, ∃ s ⊆ t, s.Countable ∧ u = ⋃ a ∈ s, a :=
    fun u hu ↦ ht.exists_countable_biUnion_of_isOpen ((isBasis_countableBasis α).isOpen hu)
  choose! s hst s_count hs using A
  refine ⟨⋃ u ∈ countableBasis α, s u, by simpa using hst,
    (countable_countableBasis α).biUnion s_count, ?_⟩
  apply isTopologicalBasis_of_isOpen_of_nhds
  · simp only [mem_iUnion, exists_prop, forall_exists_index, and_imp]
    have := @ht.isOpen
    grind
  · intro x v hx hv
    simp only [mem_iUnion, exists_prop]
    obtain ⟨u, u_mem, xu, uv⟩ : ∃ u ∈ countableBasis α, x ∈ u ∧ u ⊆ v :=
      (isBasis_countableBasis α).isOpen_iff.1 hv _ hx
    have : x ∈ ⋃ a ∈ s u, a := by
      convert! xu
      exact (hs u u_mem).symm
    obtain ⟨w, ws, xw⟩ : ∃ w ∈ s u, x ∈ w := by simpa using this
    refine ⟨w, ⟨u, u_mem, ws⟩, xw, ?_⟩
    apply Subset.trans (Subset.trans _ (hs u u_mem).symm.subset) uv
    exact subset_iUnion₂_of_subset w ws (Subset.refl _)

/-- In a second countable topological space, any family generating the topology admits a
countable generating subfamily. -/
lemma exists_countable_of_generateFrom
    {α : Type*} [ts : TopologicalSpace α] [SecondCountableTopology α] {t : Set (Set α)}
    (ht : ts = generateFrom t) :
    ∃ s ⊆ t, s.Countable ∧ ts = generateFrom s := by
  let t' := (fun f => ⋂₀ f) '' { f : Set (Set α) | f.Finite ∧ f ⊆ t }
  have : IsTopologicalBasis t' := TopologicalSpace.isTopologicalBasis_of_subbasis ht
  obtain ⟨s', s't', s'_count, hs'⟩ : ∃ s' ⊆ t', s'.Countable ∧ IsTopologicalBasis s' :=
    this.exists_countable
  have A : ∀ u ∈ s', ∃ (f : Set (Set α)), f.Finite ∧ f ⊆ t ∧ ⋂₀ f = u :=
    fun u hu ↦ by simpa [t', and_assoc] using s't' hu
  choose! f f_fin ft hf using A
  refine ⟨⋃ u ∈ s', f u, by simpa using ft, ?_, ?_⟩
  · apply s'_count.biUnion
    intro u hu
    exact Finite.countable (f_fin u hu)
  · apply le_antisymm
    · apply le_generateFrom_iff_subset_isOpen.2
      simp only [iUnion_subset_iff]
      intro u hu v hv
      rw [ht]
      apply isOpen_generateFrom_of_mem
      exact ft u hu hv
    · rw [hs'.eq_generateFrom]
      apply le_generateFrom_iff_subset_isOpen.2
      intro u hu
      rw [← hf u hu, sInter_eq_biInter]
      change IsOpen[generateFrom _] (⋂ i ∈ f u, i)
      apply @Finite.isOpen_biInter _ _ (generateFrom (⋃ u ∈ s', f u)) _ _
      · apply f_fin u hu
      · intro i hi
        apply isOpen_generateFrom_of_mem
        simp
        grind

section Sigma

variable {ι : Type*} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]

/-- A countable disjoint union of second countable spaces is second countable. -/
instance [Countable ι] [∀ i, SecondCountableTopology (E i)] :
    SecondCountableTopology (Σ i, E i) := by
  let b := ⋃ i : ι, (fun u => (Sigma.mk i '' u : Set (Σ i, E i))) '' countableBasis (E i)
  have A : IsTopologicalBasis b := IsTopologicalBasis.sigma fun i => isBasis_countableBasis _
  have B : b.Countable := countable_iUnion fun i => (countable_countableBasis _).image _
  exact A.secondCountableTopology B

end Sigma

section Sum

variable {β : Type*} [TopologicalSpace β]

/-- A sum type of two second countable spaces is second countable. -/
instance [SecondCountableTopology α] [SecondCountableTopology β] :
    SecondCountableTopology (α ⊕ β) := by
  let b :=
    (fun u => Sum.inl '' u) '' countableBasis α ∪ (fun u => Sum.inr '' u) '' countableBasis β
  have A : IsTopologicalBasis b := (isBasis_countableBasis α).sum (isBasis_countableBasis β)
  have B : b.Countable :=
    (Countable.image (countable_countableBasis _) _).union
      (Countable.image (countable_countableBasis _) _)
  exact A.secondCountableTopology B

end Sum

section Quotient

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {π : X → Y}

/-- A second countable space is mapped by an open quotient map to a second countable space. -/
theorem _root_.Topology.IsQuotientMap.secondCountableTopology [SecondCountableTopology X]
    (h' : IsQuotientMap π) (h : IsOpenMap π) : SecondCountableTopology Y where
  is_open_generated_countable := by
    obtain ⟨V, V_countable, -, V_generates⟩ := exists_countable_basis X
    exact ⟨Set.image π '' V, V_countable.image (Set.image π),
      (V_generates.isQuotientMap h' h).eq_generateFrom⟩

variable {S : Setoid X}

/-- An open quotient of a second countable space is second countable. -/
theorem Quotient.secondCountableTopology [SecondCountableTopology X]
    (h : IsOpenMap (Quotient.mk' : X → Quotient S)) : SecondCountableTopology (Quotient S) :=
  isQuotientMap_quotient_mk'.secondCountableTopology h

end Quotient

end TopologicalSpace

open TopologicalSpace

variable {α β : Type*} [TopologicalSpace α] {f : α → β}

protected theorem Topology.IsInducing.secondCountableTopology [TopologicalSpace β]
    [SecondCountableTopology β] (hf : IsInducing f) : SecondCountableTopology α := by
  rw [hf.1]
  exact secondCountableTopology_induced α β f

protected theorem Topology.IsEmbedding.secondCountableTopology
    [TopologicalSpace β] [SecondCountableTopology β]
    (hf : IsEmbedding f) : SecondCountableTopology α :=
  hf.1.secondCountableTopology

protected theorem Topology.IsEmbedding.separableSpace
    [TopologicalSpace β] [SecondCountableTopology β] {f : α → β} (hf : IsEmbedding f) :
    TopologicalSpace.SeparableSpace α := by
  have := hf.secondCountableTopology
  exact SecondCountableTopology.to_separableSpace
