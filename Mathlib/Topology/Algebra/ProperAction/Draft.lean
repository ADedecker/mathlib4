import Mathlib.Topology.Algebra.ProperAction.Basic

open Filter Set Topology Prod Function

lemma Filter.exists_injOn_iff {A B : Type*} {𝓕 : Filter A} {f : A → B} :
    (∃ U ∈ 𝓕, InjOn f U) ↔ (∀ᶠ c in 𝓕 ×ˢ 𝓕, f c.1 = f c.2 → c.1 = c.2) := by
  rw [Filter.eventually_prod_self_iff (r := fun x y ↦ f x = f y → x = y)] -- ???
  simp_rw [InjOn]

lemma Filter.eventually_iff_ultrafilter {ι : Type*} {𝓕 : Filter ι} {p : ι → Prop} :
    (∀ᶠ i in 𝓕, p i) ↔ ∀ 𝓤 : Ultrafilter ι, 𝓤 ≤ 𝓕 → ∀ᶠ i in 𝓤, p i :=
  Filter.mem_iff_ultrafilter

theorem IsProperMap.ultrafilter_tendsto_of_tendsto {ι X Y}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : IsProperMap f)
    {𝓤 : Ultrafilter ι} {φ : ι → X} {y : Y} (hy : Tendsto (f ∘ φ) (𝓤) (𝓝 y)) :
    ∃ x, f x = y ∧ Tendsto φ 𝓤 (𝓝 x) := by
  rw [← tendsto_map'_iff, ← Ultrafilter.coe_map] at hy
  simp_rw [Tendsto]
  exact hf.ultrafilter_le_nhds_of_tendsto hy

variable {G X : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace G] [TopologicalSpace X]
variable [hproper : ProperSMul G X]

theorem ProperSMul.ultrafilter_tendsto_of_smul {ι : Type*} {g : ι → G} {x : ι → X}
    {𝓤 : Ultrafilter ι} {a b : X} (H₁ : Tendsto x 𝓤 (𝓝 a)) (H₂ : Tendsto (g • x) 𝓤 (𝓝 b)) :
    ∃ g' : G, g' • a = b ∧ Tendsto g 𝓤 (𝓝 g') := by
  set φ := fun i ↦ (g i, x i)
  set f := fun gx : G × X ↦ (gx.1 • gx.2, gx.2)
  have : Tendsto (f ∘ φ) 𝓤 (𝓝 (b, a)) := by
    simpa [Prod.tendsto_iff] using ⟨H₂, H₁⟩
  rcases ProperSMul.isProperMap_smul_pair.ultrafilter_tendsto_of_tendsto this
    with ⟨⟨g', a'⟩, heq, hg'⟩
  rw [Prod.mk_inj] at heq
  use g', heq.2 ▸ heq.1, hg'.fst_nhds

-- Une variation (d'un sens) de `TG III §4.3 Prop 6`
theorem ProperSMul.tendsto_of_smul_of_free {ι : Type*} {g : ι → G} {x : ι → X}
    {𝓕 : Filter ι} {a b : X} (H₁ : Tendsto x 𝓕 (𝓝 a)) (H₂ : Tendsto (g • x) 𝓕 (𝓝 b))
    (free_a : Injective ((· • a) : G → X)) {k : G} (k_a_eq_b : k • a = b) :
    Tendsto g 𝓕 (𝓝 k) := by
  rw [tendsto_iff_ultrafilter]
  intro 𝓤 h𝓤
  rcases ProperSMul.ultrafilter_tendsto_of_smul (H₁.mono_left h𝓤) (H₂.mono_left h𝓤)
    with ⟨k', k'_a_eq_b, hk'⟩
  have : k' = k := free_a (k'_a_eq_b.trans k_a_eq_b.symm)
  exact this ▸ hk'

theorem ProperSMul.tendsto_one_of_smul_of_free {ι : Type*} {g : ι → G} {x : ι → X}
    {𝓕 : Filter ι} {a : X} (H₁ : Tendsto x 𝓕 (𝓝 a)) (H₂ : Tendsto (g • x) 𝓕 (𝓝 a))
    (free_a : Injective ((· • a) : G → X)) :
    Tendsto g 𝓕 (𝓝 1) :=
  ProperSMul.tendsto_of_smul_of_free H₁ H₂ free_a (one_smul _ _)

-- Preuve par l'absurde, comme des suites
theorem v1 {W : Set X} {U : Set G} (U_mem : U ∈ 𝓝 1) (hU : InjOn (fun gx ↦ gx.1 • gx.2) (U ×ˢ W))
    {x : X} (free_x : Injective ((· • x) : G → X)) :
    ∃ W' ∈ 𝓝[W] x, InjOn (fun gx : G × X ↦ gx.1 • gx.2) (snd ⁻¹' W') := by
  set f := fun gx : G × X ↦ gx.1 • gx.2
  set 𝓕 : Filter ((G × X) × (G × X)) := ((𝓝 1 ×ˢ 𝓟 W) ×ˢ (𝓝 1 ×ˢ 𝓟 W))
  set 𝓖 : Filter ((G × X) × (G × X)) := ((⊤ ×ˢ (𝓝[W] x)) ×ˢ (⊤ ×ˢ (𝓝[W] x))) with 𝓖_def
  suffices ∀ᶠ c in 𝓖, f c.1 = f c.2 → c.1 = c.2 by
    rw [𝓖_def, ← exists_injOn_iff] at this
    simp_rw [top_prod, mem_comap] at this
    rcases this with ⟨W'', ⟨W', W'_mem, hsub⟩, hW''⟩
    use W', W'_mem, hW''.mono hsub
  by_contra H
  simp_rw [not_eventually, _root_.not_imp, frequently_iff_neBot] at H
  set 𝓗 := 𝓖 ⊓ 𝓟 {c | f c.1 = f c.2 ∧ c.1 ≠ c.2} with 𝓗_eq
  set g : (G × X) × (G × X) → G := fst ∘ fst
  set g' : (G × X) × (G × X) → G := fst ∘ snd
  set y : (G × X) × (G × X) → X := snd ∘ fst
  set y' : (G × X) × (G × X) → X := snd ∘ snd
  obtain ⟨y_tendsto, y_mem, y'_tendsto, y'_mem, heq, hne⟩ :
      Tendsto y 𝓗 (𝓝 x) ∧ (∀ᶠ i in 𝓗, y i ∈ W) ∧
      Tendsto y' 𝓗 (𝓝 x) ∧ (∀ᶠ i in 𝓗, y' i ∈ W) ∧
      (∀ᶠ i in 𝓗, g i • y i = g' i • y' i) ∧
      (∀ᶠ i in 𝓗, (g i, y i) ≠ (g' i, y' i)) := by
    have := 𝓗_eq.le
    simp_rw [le_inf_iff, 𝓖, le_prod, tendsto_prod_iff', le_principal_iff, ← eventually_iff,
      eventually_and, tendsto_nhdsWithin_iff, tendsto_top, true_and, and_assoc] at this
    exact this
  simp_rw [smul_eq_iff_eq_inv_smul, ← mul_smul] at heq
  set h : (G × X) × (G × X) → G := fun i ↦ (g i) ⁻¹ * (g' i)
  have hy'_tendsto : Tendsto (h • y') 𝓗 (𝓝 x) := y_tendsto.congr' heq
  have h_tendsto : Tendsto h 𝓗 (𝓝 1) :=
    ProperSMul.tendsto_one_of_smul_of_free y'_tendsto hy'_tendsto free_x
  rw [← @eventually_const _ 𝓗 _ False]
  filter_upwards [h_tendsto.eventually_mem U_mem, heq, hne, y_mem, y'_mem]
    with i h_mem heq hne y_mem y'_mem
  apply hne
  rw [Prod.mk_inj, ← inv_mul_eq_one, eq_comm, ← Prod.mk_inj]
  exact hU (mk_mem_prod (mem_of_mem_nhds U_mem) y_mem) (mk_mem_prod h_mem y'_mem)
    (by simpa [f] using heq)

-- Preuve vraiment filtres
theorem v2 {W : Set X} {U : Set G} (U_mem : U ∈ 𝓝 1) (hU : InjOn (fun gx ↦ gx.1 • gx.2) (U ×ˢ W))
    {x : X} (free_x : Injective ((· • x) : G → X)) :
    ∃ W' ∈ 𝓝[W] x, InjOn (fun gx : G × X ↦ gx.1 • gx.2) (snd ⁻¹' W') := by
  set f := fun gx : G × X ↦ gx.1 • gx.2
  set I := (G × X) × (G × X)
  set A : Set I := {c | f c.1 = f c.2} with A_def
  set Δ : Set I := {c | c.1 = c.2} with Δ_def
  set 𝓕 : Filter I := ((𝓝 1 ×ˢ 𝓟 W) ×ˢ (𝓝 1 ×ˢ 𝓟 W))
  set 𝓖 : Filter I := ((⊤ ×ˢ (𝓝[W] x)) ×ˢ (⊤ ×ˢ (𝓝[W] x))) with 𝓖_def
  suffices 𝓖 ⊓ 𝓟 A ≤ 𝓟 Δ by
    simp_rw [le_principal_iff, Δ_def, ← eventually_iff,
      eventually_inf_principal, A_def, mem_setOf] at this
    rw [𝓖_def, ← exists_injOn_iff] at this
    simp_rw [top_prod, mem_comap] at this
    rcases this with ⟨W'', ⟨W', W'_mem, hsub⟩, hW''⟩
    use W', W'_mem, hW''.mono hsub
  have hyp : 𝓕 ⊓ 𝓟 A ≤ 𝓟 Δ := by
    simp_rw [le_principal_iff, Δ_def, ← eventually_iff,
      eventually_inf_principal, A_def, mem_setOf]
    rw [← exists_injOn_iff]
    use U ×ˢ W, prod_mem_prod U_mem (mem_principal_self _)
  set φ : I → I := fun c ↦ ⟨⟨1, c.1.2⟩, ⟨c.1.1⁻¹ * c.2.1, c.2.2⟩⟩ with φ_def
  have φ_Δ : φ ⁻¹' Δ = Δ := by
    ext
    simp [Δ, φ, eq_inv_mul_iff_mul_eq, Prod.eq_iff_fst_eq_snd_eq]
  have φ_A : φ ⁻¹' A = A := by
    ext
    simp [A, f, φ, mul_smul, smul_eq_iff_eq_inv_smul]
  suffices Tendsto φ (𝓖 ⊓ 𝓟 A) 𝓕 from
    calc
      𝓖 ⊓ 𝓟 A
        ≤ comap φ 𝓕 ⊓ 𝓟 A := le_inf this.le_comap inf_le_right
      _ = comap φ (𝓕 ⊓ 𝓟 A) := by rw [comap_inf, comap_principal, φ_A]
      _ ≤ comap φ (𝓟 Δ) := comap_mono hyp
      _ = 𝓟 Δ := by rw [comap_principal, φ_Δ]
  rw [tendsto_prod_iff', tendsto_prod_iff', tendsto_prod_iff']
  refine ⟨⟨tendsto_const_nhds, tendsto_inf_left <| tendsto_fst.snd.mono_right inf_le_right⟩,
    ⟨?_, tendsto_inf_left <| tendsto_snd.snd.mono_right inf_le_right⟩⟩
  refine ProperSMul.tendsto_one_of_smul_of_free
    (tendsto_inf_left <| tendsto_snd.snd.mono_right inf_le_left)
    ((tendsto_inf_left <| tendsto_fst.snd.mono_right inf_le_left).congr' ?_)
    free_x
  filter_upwards [mem_inf_of_right <| mem_principal_self A] with a
  simpa [A, f, φ, smul_eq_iff_eq_inv_smul, mul_smul] using id

-- Ce qui sert pour construire des revêtements
open Pointwise in
theorem corollary [DiscreteTopology G] {x : X} (free_x : Injective ((· • x) : G → X)) :
    ∃ U ∈ 𝓝 x, ∀ s t : G, (s • U ∩ t • U).Nonempty → s = t := by
  have : InjOn (fun gx : G × X ↦ gx.1 • gx.2) ({1} ×ˢ univ) :=
    fun gx ⟨(hgx : gx.1 = 1), _⟩ gx' ⟨(hgx' : gx'.1 = 1), _⟩ heq ↦
    Prod.mk_inj.mpr ⟨hgx.trans hgx'.symm, by simpa [hgx, hgx'] using heq⟩
  rcases v2 (nhds_discrete G ▸ singleton_mem_pure) this free_x with ⟨U, hUx, hU⟩
  rw [nhdsWithin_univ] at hUx
  use U, hUx
  intro s t ⟨x, ⟨u, hu, hux⟩, ⟨v, hv, hvx⟩⟩
  exact congrArg fst (@hU ⟨s, u⟩ hu ⟨t, v⟩ hv (hux.trans hvx.symm))
