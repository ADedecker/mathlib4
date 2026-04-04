/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.PointwiseConvergence

/-!
# TODO
-/

@[expose] public section

open Set Topology

namespace ContinuousLinearMap

attribute [local instance] SMulCommClass.symm

variable {R S R₂ S₂ : Type*} (A : Type*) [NormedField R] [NormedField S] [NormedField R₂]
  [NormedField S₂] [Semiring A]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module S N] [Module R₂ P] [Module S₂ P] [Module A P]
  [SMulCommClass S₂ R₂ P] [SMulCommClass A S₂ P] [SMulCommClass A R₂ P]
  {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [IsTopologicalAddGroup M] [IsTopologicalAddGroup N] [IsTopologicalAddGroup P]
  [ContinuousConstSMul R M] [ContinuousConstSMul S N]
  [ContinuousConstSMul R₂ P] [ContinuousConstSMul S₂ P] [ContinuousConstSMul A P]

open scoped UniformConvergenceCLM

def flipPointwiseUniform {𝔖 : Set (Set N)} (h𝔖 : ⋃₀ 𝔖 = univ) :
    (M →SLₚₜ[ρ₁₂] N →SLᵤ[σ₁₂, 𝔖] P) →L[A] (N →SLᵤ[σ₁₂, 𝔖] M →SLₚₜ[ρ₁₂] P) where
  toFun L :=
    letI Lₗ : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P := ContinuousLinearMap.coeLMₛₗ _ ∘ₛₗ L.toLinearMap
    { toFun n :=
      { toFun m := L m n
        map_add' _ _ := Lₗ.map_add₂ ..
        map_smul' _ _ := Lₗ.map_smulₛₗ₂ ..
        cont := by
          have : ContinuousEvalConst (N →SLᵤ[σ₁₂, 𝔖] P) N P :=
            UniformConvergenceCLM.continuousEvalConst _ _ _ h𝔖
          fun_prop }
      map_add' _ _ := by ext; exact (Lₗ _).map_add ..
      map_smul' _ _ := by ext; exact (Lₗ _).map_smulₛₗ ..
      cont := PointwiseConvergenceCLM.continuous_of_continuous_eval fun m ↦ (L m).continuous }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  cont := by
    set Φ : (M →SLₚₜ[ρ₁₂] P) →L[R₂] (M → P) := .pi (PointwiseConvergenceCLM.evalCLM ρ₁₂ _)
    have : IsEmbedding Φ := PointwiseConvergenceCLM.isEmbedding_coeFn ρ₁₂ M P
    rw [UniformConvergenceCLM.isEmbedding_postcomp σ₁₂ Φ this _ |>.continuous_iff]
    have := UniformConvergenceCLM.isEmbedding_postcomp ρ₁₂ Φ this (_ : Set (Set M))
    simp only [PointwiseConvergenceCLM.isEmbedding_coeFn _ _ _ |>.continuous_iff, continuous_pi_iff]
    intro n m
    change Continuous fun (L : M →SLₚₜ[ρ₁₂] N →SLₚₜ[σ₁₂] P) ↦ L m n
    fun_prop

def flipPointwisePointwise : (M →SLₚₜ[ρ₁₂] N →SLₚₜ[σ₁₂] P) →L[A] (N →SLₚₜ[σ₁₂] M →SLₚₜ[ρ₁₂] P) where
  toFun L :=
    letI Lₗ : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P := ContinuousLinearMap.coeLMₛₗ _ ∘ₛₗ L.toLinearMap
    { toFun n :=
      { toFun m := L m n
        map_add' _ _ := Lₗ.map_add₂ ..
        map_smul' _ _ := Lₗ.map_smulₛₗ₂ ..
        cont := by fun_prop }
      map_add' _ _ := by ext; exact (Lₗ _).map_add ..
      map_smul' _ _ := by ext; exact (Lₗ _).map_smulₛₗ ..
      cont := by
        rw [PointwiseConvergenceCLM.isEmbedding_coeFn _ _ _ |>.continuous_iff, continuous_pi_iff]
        intro m
        exact (L m).continuous }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  cont := by
    simp only [PointwiseConvergenceCLM.isEmbedding_coeFn _ _ _ |>.continuous_iff, continuous_pi_iff]
    intro n m
    change Continuous fun (L : M →SLₚₜ[ρ₁₂] N →SLₚₜ[σ₁₂] P) ↦ L m n
    fun_prop

def flipPointwisePointwise : (M →SLₚₜ[ρ₁₂] N →SLₚₜ[σ₁₂] P) ≃L[A] (N →SLₚₜ[σ₁₂] M →SLₚₜ[ρ₁₂] P) where
  toFun L :=
    letI Lₗ : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P := ContinuousLinearMap.coeLMₛₗ _ ∘ₛₗ L.toLinearMap
    { toFun n :=
      { toFun m := L m n
        map_add' _ _ := Lₗ.map_add₂ ..
        map_smul' _ _ := Lₗ.map_smulₛₗ₂ ..
        cont := by fun_prop }
      map_add' _ _ := by ext; exact (Lₗ _).map_add ..
      map_smul' _ _ := by ext; exact (Lₗ _).map_smulₛₗ ..
      cont := by
        rw [PointwiseConvergenceCLM.isEmbedding_coeFn _ _ _ |>.continuous_iff, continuous_pi_iff]
        intro m
        exact (L m).continuous }
  invFun := sorry
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

end ContinuousLinearMap
