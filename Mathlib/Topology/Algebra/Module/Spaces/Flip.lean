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
    let _ := IsTopologicalAddGroup.rightUniformSpace P
    have _ : IsUniformAddGroup P := isUniformAddGroup_of_addCommGroup
    have : IsUniformEmbedding ((↑) : (M →SLₚₜ[ρ₁₂] P) → M → P) :=
      PointwiseConvergenceCLM.isUniformEmbedding_coeFn ρ₁₂ M P
    rw [UniformConvergenceCLM.isEmbedding_coeFn _ _ _ |>.continuous_iff,
      UniformOnFun.postcomp_isUniformEmbedding this |>.isEmbedding.continuous_iff,
      UniformOnFun.uniformEquivPiComm _ _ |>.isUniformEmbedding.isEmbedding.continuous_iff,
      continuous_pi_iff]
    exact fun m ↦ UniformConvergenceCLM.isEmbedding_coeFn _ _ _ |>.continuous.comp
      <| continuous_eval_const m

def flipUniformPointwise {𝔖 : Set (Set M)} (h𝔖 : ⋃₀ 𝔖 = univ) :
    (M →SLᵤ[ρ₁₂, 𝔖] N →SLₚₜ[σ₁₂] P) →L[A] (N →SLₚₜ[σ₁₂] M →SLᵤ[ρ₁₂, 𝔖] P) where
  toFun L :=
    letI Lₗ : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P := ContinuousLinearMap.coeLMₛₗ _ ∘ₛₗ L.toLinearMap
    { toFun n :=
      { toFun m := L m n
        map_add' _ _ := Lₗ.map_add₂ ..
        map_smul' _ _ := Lₗ.map_smulₛₗ₂ ..
        cont := by fun_prop }
      map_add' _ _ := by ext; exact (Lₗ _).map_add ..
      map_smul' _ _ := by ext; exact (Lₗ _).map_smulₛₗ ..
      cont := sorry }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval fun n ↦ by

    sorry

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
