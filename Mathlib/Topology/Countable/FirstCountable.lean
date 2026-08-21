/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Constructions
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.NhdsWithin

/-!
# First-countable topological spaces
-/

@[expose] public section

open Topology Filter

namespace TopologicalSpace

universe u

variable (α : Type u) [t : TopologicalSpace α]

/-- A first-countable space is one in which every point has a
  countable neighborhood basis. -/
class _root_.FirstCountableTopology : Prop where
  /-- The filter `𝓝 a` is countably generated for all points `a`. -/
  nhds_generated_countable : ∀ a : α, (𝓝 a).IsCountablyGenerated

attribute [instance] FirstCountableTopology.nhds_generated_countable

/-- If `β` is a first-countable space, then its induced topology via `f` on `α` is also
first-countable. -/
theorem firstCountableTopology_induced (α β : Type*) [t : TopologicalSpace β]
    [FirstCountableTopology β] (f : α → β) : @FirstCountableTopology α (t.induced f) :=
  let _ := t.induced f
  ⟨fun x ↦ nhds_induced f x ▸ inferInstance⟩

variable {α}

instance Subtype.firstCountableTopology (s : Set α) [FirstCountableTopology α] :
    FirstCountableTopology s :=
  firstCountableTopology_induced s α (↑)

protected theorem _root_.Topology.IsInducing.firstCountableTopology {β : Type*}
    [TopologicalSpace β] [FirstCountableTopology β] {f : α → β} (hf : IsInducing f) :
    FirstCountableTopology α := by
  rw [hf.1]
  exact firstCountableTopology_induced α β f

protected theorem _root_.Topology.IsEmbedding.firstCountableTopology {β : Type*}
    [TopologicalSpace β] [FirstCountableTopology β] {f : α → β} (hf : IsEmbedding f) :
    FirstCountableTopology α :=
  hf.1.firstCountableTopology

section FirstCountableTopology

variable [FirstCountableTopology α] {x : α}

/-- In a first-countable space, a cluster point `x` of a countably generated filter is the limit of
some sequence. -/
theorem _root_.ClusterPt.exists_seq_tendsto {f : Filter α} [IsCountablyGenerated f]
    (hx : ClusterPt x f) :
    ∃ ψ : ℕ → α, Tendsto ψ atTop (𝓝 x) ∧ Tendsto ψ atTop f := by
  unfold ClusterPt at hx
  obtain ⟨g, hg⟩ := Filter.exists_seq_tendsto (𝓝 x ⊓ f)
  exact ⟨g, (tendsto_inf.1 hg).1, (tendsto_inf.1 hg).2⟩

theorem _root_.MapClusterPt.exists_seq_tendsto {ι : Type*} {f : Filter ι} [IsCountablyGenerated f]
    {x : α} {u : ι → α} (hx : MapClusterPt x f u) :
    ∃ ψ : ℕ → ι, Tendsto (u ∘ ψ) atTop (𝓝 x) ∧ Tendsto ψ atTop f := by
  grind [exists_seq_comp_tendsto hx]

/-- In a first-countable space, a cluster point `x` of a sequence
is the limit of some subsequence. -/
theorem _root_.MapClusterPt.tendsto_subseq {u : ℕ → α} (hx : MapClusterPt x atTop u) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (u ∘ ψ) atTop (𝓝 x) :=
  subseq_tendsto_of_neBot hx

@[deprecated MapClusterPt.tendsto_subseq (since := "2026-03-29")]
theorem FirstCountableTopology.tendsto_subseq {u : ℕ → α} {x : α}
    (hx : MapClusterPt x atTop u) : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (u ∘ ψ) atTop (𝓝 x) :=
  subseq_tendsto_of_neBot hx

end FirstCountableTopology

instance {β} [TopologicalSpace β] [FirstCountableTopology α] [FirstCountableTopology β] :
    FirstCountableTopology (α × β) :=
  ⟨fun ⟨x, y⟩ => by rw [nhds_prod_eq]; infer_instance⟩

section Pi

instance {ι : Type*} {X : ι → Type*} [Countable ι] [∀ i, TopologicalSpace (X i)]
    [∀ i, FirstCountableTopology (X i)] : FirstCountableTopology (∀ i, X i) :=
  ⟨fun f => by rw [nhds_pi]; infer_instance⟩

end Pi

instance isCountablyGenerated_nhdsWithin (x : α) [IsCountablyGenerated (𝓝 x)] (s : Set α) :
    IsCountablyGenerated (𝓝[s] x) :=
  Inf.isCountablyGenerated _ _

end TopologicalSpace
