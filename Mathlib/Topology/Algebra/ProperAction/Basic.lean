/-
Copyright (c) 2024 Anatole Dedeker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedeker, Etienne Marion, Florestan Martin-Baillon, Vincent Guirardel
-/
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Proper group action

In this file we define proper action of a group on a topological space, and we prove that in this
case the quotient space is T2. We also give equivalent definitions of proper action using
ultrafilters and show the transfer of proper action to a closed subgroup.

## Main definitions

* `ProperSMul` : a group `G` acts properly on a topological space `X`
  if the map `(g, x) ↦ (g • x, x)` is proper, in the sense of `IsProperMap`.

## Main statements

* `t2Space_quotient_mulAction_of_properSMul`: If a group `G` acts properly
  on a topological space `X`, then the quotient space is Hausdorff (T2).
* `t2Space_of_properSMul_of_t1Group`: If a T1 group acts properly on a topological space,
  then this topological space is T2.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

## Tags

Hausdorff, group action, proper action
-/

open Filter Topology Set Prod

/-- Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
  isProperMap_vadd_pair : IsProperMap (fun gx ↦ (gx.1 +ᵥ gx.2, gx.2) : G × X → X × X)

/-- Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
@[to_additive existing (attr := mk_iff)]
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
  isProperMap_smul_pair (G X) : IsProperMap (fun gx ↦ (gx.1 • gx.2, gx.2) : G × X → X × X)

notation "Φ_{"G","X"}" => (fun gx : G × X ↦ (Prod.fst gx • Prod.snd gx, Prod.snd gx))

attribute [to_additive existing] properSMul_iff

variable {ι G X : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace G] [TopologicalSpace X]

/-- If a group acts properly then in particular it acts continuously. -/
@[to_additive /-- If a group acts properly then in particular it acts continuously. -/]
-- See note [lower instance property]
instance (priority := 100) ProperSMul.toContinuousSMul [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := isProperMap_smul_pair G X |>.continuous.fst

@[to_additive]
theorem ProperSMul.ultrafilter_tendsto_of_smul [ProperSMul G X] {g : ι → G} {x : ι → X}
    {𝓤 : Ultrafilter ι} {a b : X} (H₁ : Tendsto x 𝓤 (𝓝 a)) (H₂ : Tendsto (g • x) 𝓤 (𝓝 b)) :
    ∃ g' : G, g' • a = b ∧ Tendsto g 𝓤 (𝓝 g') := by
  have : Tendsto (fun i ↦ (g i • x i, x i)) 𝓤 (𝓝 (b, a)) := by
    simpa [Prod.tendsto_iff] using ⟨H₂, H₁⟩
  rcases ProperSMul.isProperMap_smul_pair G X |>.ultrafilter_tendsto_of_tendsto
    (φ := fun i ↦ (g i, x i)) this with ⟨⟨g', a'⟩, heq, hg'⟩
  rw [Prod.mk_inj] at heq
  use g', heq.2 ▸ heq.1, hg'.fst_nhds

/-- A group `G` acts properly on a topological space `X` if and only if for all ultrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `g • x₂ = x₁` and `𝒰.fst` converges to `g`. -/
@[to_additive /-- An additive group `G` acts properly on a topological space `X` if and only if
for all ultrafilters `𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)`
along the map `(g, x) ↦ (g • x, x)`, then there exists `g : G` such that `g • x₂ = x₁`
and `𝒰.fst` converges to `g`. -/]
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto :
    ProperSMul G X ↔ ContinuousSMul G X ∧
      (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
        Tendsto Φ_{G, X} 𝒰 (𝓝 (x₁, x₂)) →
        ∃ g : G, g • x₂ = x₁ ∧ Tendsto (Prod.fst : G × X → G) 𝒰 (𝓝 g)) := by
  refine ⟨fun h ↦ ⟨inferInstance, fun 𝒰 x₁ x₂ h' ↦ ?_⟩, fun ⟨cont, h⟩ ↦ ?_⟩
  · exact ProperSMul.ultrafilter_tendsto_of_smul h'.snd_nhds h'.fst_nhds
  · rw [properSMul_iff, isProperMap_iff_ultrafilter]
    refine ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx ↦ ?_⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg1, hg2⟩
    refine ⟨(g, x₂), by simp_rw [hg1], ?_⟩
    rw [nhds_prod_eq, 𝒰.le_prod]
    exact ⟨hg2, (continuous_snd.tendsto _).comp hxx⟩

/-- A group `G` acts properly on a T2 topological space `X` if and only if for all ultrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `𝒰.fst` converges to `g`. -/
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X] :
    ProperSMul G X ↔ ContinuousSMul G X ∧
      (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
        Tendsto Φ_{G, X} 𝒰 (𝓝 (x₁, x₂)) →
        ∃ g : G, Tendsto (Prod.fst : G × X → G) 𝒰 (𝓝 g)) := by
  rw [properSMul_iff_continuousSMul_ultrafilter_tendsto]
  refine and_congr_right fun hc ↦ ?_
  congrm ∀ 𝒰 x₁ x₂ hxx, ∃ g, ?_
  exact and_iff_right_of_imp fun hg ↦ tendsto_nhds_unique
    (hg.smul ((continuous_snd.tendsto _).comp hxx)) ((continuous_fst.tendsto _).comp hxx)

/-- If `G` acts properly on `X`, then the quotient space is Hausdorff (T2). -/
@[to_additive /-- If `G` acts properly on `X`, then the quotient space is Hausdorff (T2). -/]
instance t2Space_quotient_mulAction_of_properSMul [ProperSMul G X] :
    T2Space (Quotient (MulAction.orbitRel G X)) := by
  rw [t2_iff_isClosed_diagonal]
  set R := MulAction.orbitRel G X
  let π : X → Quotient R := Quotient.mk'
  have : IsOpenQuotientMap (Prod.map π π) :=
    MulAction.isOpenQuotientMap_quotientMk.prodMap MulAction.isOpenQuotientMap_quotientMk
  rw [← this.isQuotientMap.isClosed_preimage]
  convert ProperSMul.isProperMap_smul_pair G X |>.isClosedMap.isClosed_range
  ext ⟨x₁, x₂⟩
  simp only [mem_preimage, map_apply, mem_diagonal_iff, mem_range, Prod.mk.injEq, Prod.exists,
    exists_eq_right]
  rw [Quotient.eq', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

/-- If a T1 group acts properly on a topological space, then this topological space is T2. -/
@[to_additive /-- If a T1 group acts properly on a topological space,
then this topological space is T2. -/]
theorem t2Space_of_properSMul_of_t1Group [h_proper : ProperSMul G X] [T1Space G] : T2Space X := by
  let f := fun x : X ↦ ((1 : G), x)
  have proper_f : IsProperMap f := by
    refine IsClosedEmbedding.isProperMap ⟨?_, ?_⟩
    · let g := fun gx : G × X ↦ gx.2
      have : Function.LeftInverse g f := fun x ↦ by simp [f, g]
      exact this.isEmbedding (by fun_prop) (by fun_prop)
    · have : range f = ({1} ×ˢ univ) := by simp [f, Set.singleton_prod]
      rw [this]
      exact isClosed_singleton.prod isClosed_univ
  rw [t2_iff_isClosed_diagonal]
  let g := fun gx : G × X ↦ (gx.1 • gx.2, gx.2)
  have proper_g : IsProperMap g := (properSMul_iff G X).1 h_proper
  have : g ∘ f = fun x ↦ (x, x) := by ext x <;> simp [f, g]
  have range_gf : range (g ∘ f) = diagonal X := by simp [this]
  rw [← range_gf]
  exact (proper_g.comp proper_f).isClosed_range

@[deprecated (since := "2025-03-21")]
alias t2Space_of_properSMul_of_t2Group := t2Space_of_properSMul_of_t1Group

@[to_additive]
theorem setOf_smul_eq_eq_image_fst_preimage_smul_pair {M X : Type*} [SMul M X] {a b : X} :
    {m : M | m • a = b} = fst '' (Φ_{M, X} ⁻¹' {(b, a)}) := by
  ext
  simp

@[to_additive]
theorem ProperSMul.isCompact_setOf_smul_eq [ProperSMul G X] {a b : X} :
    IsCompact {g : G | g • a = b} := by
  rw [setOf_smul_eq_eq_image_fst_preimage_smul_pair]
  exact isProperMap_smul_pair G X |>.isCompact_preimage isCompact_singleton |>.image continuous_fst

@[to_additive]
theorem ProperSMul.isCompact_stabilizer [ProperSMul G X] {a : X} :
    IsCompact (MulAction.stabilizer G a : Set G) :=
  ProperSMul.isCompact_setOf_smul_eq

theorem ProperSMul.tendsto_nhdsSet_of_smul [ProperSMul G X] {g : ι → G} {x : ι → X}
    {𝓕 : Filter ι} {a b : X} (H₁ : Tendsto x 𝓕 (𝓝 a)) (H₂ : Tendsto (g • x) 𝓕 (𝓝 b)) :
    Tendsto g 𝓕 (𝓝ˢ {k | k • a = b}) := by
  rw [setOf_smul_eq_eq_image_fst_preimage_smul_pair]
  have : Tendsto (fun i ↦ (g i, x i)) 𝓕 (𝓝ˢ (Φ_{G, X} ⁻¹' {(b, a)})) := by
    rw [← (isProperMap_smul_pair G X).isClosedMap.comap_nhdsSet_eq (by fun_prop), tendsto_comap_iff,
        nhdsSet_singleton, Prod.tendsto_iff]
    exact ⟨H₂, H₁⟩
  exact continuous_fst.tendsto_nhdsSet (mapsTo_image _ _) |>.comp this

/-- If two groups `H` and `G` act on a topological space `X` such that `G` acts properly and
there exists a group homomorphism `H → G` which is a closed embedding compatible with the actions,
then `H` also acts properly on `X`. -/
@[to_additive /-- If two groups `H` and `G` act on a topological space `X` such that `G` acts
properly and there exists a group homomorphism `H → G` which is a closed embedding compatible with
the actions, then `H` also acts properly on `X`. -/]
theorem properSMul_of_isClosedEmbedding {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H]
    [ProperSMul G X] (f : H →* G) (f_clemb : IsClosedEmbedding f)
    (f_compat : ∀ (h : H) (x : X), f h • x = h • x) : ProperSMul H X where
  isProperMap_smul_pair := by
    have h : IsProperMap (Prod.map f (@id X)) := f_clemb.isProperMap.prodMap isProperMap_id
    have : Φ_{H, X} = Φ_{G, X} ∘ (Prod.map f (@id X)) := by
      simp [Function.comp_def, f_compat]
    rw [this]
    exact ProperSMul.isProperMap_smul_pair G X |>.comp h

/-- If `H` is a closed subgroup of `G` and `G` acts properly on `X`, then so does `H`. -/
@[to_additive
/-- If `H` is a closed subgroup of `G` and `G` acts properly on `X`, then so does `H`. -/]
instance {H : Subgroup G} [ProperSMul G X] [H_closed : IsClosed (H : Set G)] : ProperSMul H X :=
  properSMul_of_isClosedEmbedding H.subtype H_closed.isClosedEmbedding_subtypeVal fun _ _ ↦ rfl

/-- The action `G ↷ G` by left translations is proper. -/
@[to_additive
/-- The action `G ↷ G` by left translations is proper. -/]
instance [IsTopologicalGroup G] : ProperSMul G G where
  isProperMap_smul_pair := by
    let Φ : G × G ≃ₜ G × G :=
    { toFun := fun gh ↦ (gh.1 * gh.2, gh.2)
      invFun := fun gh ↦ (gh.1 * gh.2⁻¹, gh.2)
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
    exact Φ.isProperMap

open MulOpposite in
/-- The action `Gᵐᵒᵖ ↷ G` by right translations is proper. -/
@[to_additive
/-- The action `Gᵐᵒᵖ ↷ G` by right translations is proper. -/]
instance [IsTopologicalGroup G] : ProperSMul Gᵐᵒᵖ G where
  isProperMap_smul_pair := by
    let Φ : Gᵐᵒᵖ × G ≃ₜ G × G :=
    { toFun := fun gh ↦ (gh.2 * (unop gh.1), gh.2)
      invFun := fun gh ↦ (op (gh.2⁻¹ * gh.1), gh.2)
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
    exact Φ.isProperMap

/-- Given a closed subgroup `H` of a topological group `G`, the right action of `H` on `G`
is proper. Note that the corresponding statement for the left action can be proven by
`inferInstance`. -/
@[to_additive /-- Given a closed subgroup `H` of an additive topological group `G`, the right
action of `H` on `G` is proper. Note that the corresponding statement for the left action can be
proven by `inferInstance`. -/]
instance [IsTopologicalGroup G] {H : Subgroup G} [H_closed : IsClosed (H : Set G)] :
    ProperSMul H.op G :=
  have : IsClosed (H.op : Set Gᵐᵒᵖ) := H_closed.preimage MulOpposite.continuous_unop
  inferInstance

@[to_additive]
instance QuotientGroup.instT2Space [IsTopologicalGroup G] {H : Subgroup G} [IsClosed (H : Set G)] :
    T2Space (G ⧸ H) :=
  t2Space_quotient_mulAction_of_properSMul
