/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Anatole Dedecker
-/

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMapZero

/-!
# Integrals and the continuous functional calculus

This file gives results about integrals of the form `∫ x, cfc (f x) a`. Most notably, we show
that the integral commutes with the continuous functional calculus under appropriate conditions.

## Main declarations

+ `cfc_setIntegral` (resp. `cfc_integral`): given a function `f : X → 𝕜 → 𝕜`, we have that
  `cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ`
  under appropriate conditions (resp. with `s = univ`)
+ `cfcₙ_integral`: the same for the non-unital continuous functional calculus
+ `integrable_cfc_set`, `integrable_cfcₙ_set`, `integrable_cfc`, `integrable_cfcₙ`:
  functions of the form `fun x => cfc (f x) a` are integrable.

## TODO

+ Lift this to the case where the CFC is over `ℝ≥0`
+ Use this to prove operator monotonicity and concavity/convexity of `rpow` and `log`
-/

open MeasureTheory Topology
open scoped ContinuousMapZero

section unital

open ContinuousMap

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X}
  [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
  [ContinuousFunctionalCalculus 𝕜 A p]

/-- A version of `cfc_apply` in terms of `ContinuousMapZero.mkD` -/
lemma cfc_apply_mkD {f : 𝕜 → 𝕜} {a : A} (ha : p a := by cfc_tac) :
    cfc f a = cfcHom (a := a) ha (mkD ((spectrum 𝕜 a).restrict f) 0) := by
  by_cases hf : ContinuousOn f (spectrum 𝕜 a)
  · rw [cfc_apply f a, mkD_of_continuousOn hf]
  · rw [cfc_apply_of_not_continuousOn a hf, mkD_of_not_continuousOn hf,
      map_zero]

/-- A version of `cfc_eq_cfcL` in terms of `ContinuousMapZero.mkD` -/
lemma cfc_eq_cfcL_mkD {f : 𝕜 → 𝕜} {a : A} (ha : p a := by cfc_tac) :
    cfc f a = cfcL (a := a) ha (mkD ((spectrum 𝕜 a).restrict f) 0) :=
  cfc_apply_mkD

variable [CompleteSpace A]

lemma cfcL_integral [NormedSpace ℝ A] (a : A) (f : X → C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ)
    (ha : p a := by cfc_tac) :
    ∫ x, cfcL (a := a) ha (f x) ∂μ = cfcL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

lemma cfcL_integrable (a : A) (f : X → C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    Integrable (fun x ↦ cfcL (a := a) ha (f x)) μ :=
  ContinuousLinearMap.integrable_comp _ hf₁

lemma cfcHom_integral [NormedSpace ℝ A] (a : A) (f : X → C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcHom (a := a) ha (f x) ∂μ = cfcHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcL_integral a f hf₁ ha

lemma integrable_cfc₀ (f : X → 𝕜 → 𝕜) (a : A)
    (hf : Integrable
      (fun x : X => mkD ((spectrum 𝕜 a).restrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  conv in cfc _ _ => rw [cfc_eq_cfcL_mkD (a := a) ha]
  exact cfcL_integrable _ _ hf ha

lemma integrableOn_cfc₀ {s : Set X} (f : X → 𝕜 → 𝕜) (a : A)
    (hf : IntegrableOn
      (fun x : X => mkD ((spectrum 𝕜 a).restrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  exact integrable_cfc₀ _ _ hf ha

lemma integrable_cfc' (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) (hf₁ : ∀ᵐ x ∂μ, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : AEStronglyMeasurable
      (fun x : X => mkD ((spectrum 𝕜 a).restrict (f x)) 0) μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  refine integrable_cfc₀ _ _ ⟨hf₂, ?_⟩ ha
  exact hasFiniteIntegral_mkD_restrict_of_bound _ _ hf₁ bound bound_int bound_ge

lemma integrableOn_cfc' {s : Set X} (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) (hf₁ : ∀ᵐ x ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : AEStronglyMeasurable
      (fun x : X => mkD ((spectrum 𝕜 a).restrict (f x)) 0) (μ.restrict s))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ :=
  integrable_cfc' f bound a hf₁ hf₂ bound_ge bound_int ha

open Set Function in
lemma integrable_cfc [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  refine integrable_cfc₀ _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact .of_forall fun x ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨trivial, hz⟩

open Set Function in
lemma integrableOn_cfc [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  refine integrableOn_cfc₀ _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩

open Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_integral₀ [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂μ, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : Integrable
      (fun x : X => mkD ((spectrum 𝕜 a).restrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have key₁ (z : spectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((spectrum 𝕜 a).restrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₂]
    refine integral_congr_ae ?_
    filter_upwards [hf₁] with x cont_x
    rw [mkD_apply_of_continuousOn cont_x]
  have key₂ (z : spectrum 𝕜 a) :
      ∫ x, f x z ∂μ = mkD ((spectrum 𝕜 a).restrict (fun z ↦ ∫ x, f x z ∂μ)) 0 z := by
    rw [mkD_apply_of_continuousOn]
    rw [continuousOn_iff_continuous_restrict]
    refine continuous_congr key₁ |>.mpr ?_
    exact map_continuous (∫ x, mkD ((spectrum 𝕜 a).restrict (f x)) 0 ∂μ)
  simp_rw [cfc_eq_cfcL_mkD (a := a) ha, cfcL_integral a _ hf₂ ha]
  congr
  ext z
  rw [← key₁, key₂]

open Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_setIntegral₀ {s : Set X} [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : IntegrableOn
      (fun x : X => mkD ((spectrum 𝕜 a).restrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x in s, f x z ∂μ) a = ∫ x in s, cfc (f x) a ∂μ :=
  cfc_integral₀ _ _ hf₁ hf₂ ha

open Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_integral' [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    (hf₁ : ∀ᵐ x ∂μ, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : AEStronglyMeasurable (fun x ↦ mkD ((spectrum 𝕜 a).restrict (f x)) 0) μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  nontriviality A
  refine cfc_integral₀ _ _ hf₁ ⟨hf₂, ?_⟩ ha
  exact hasFiniteIntegral_mkD_restrict_of_bound _ _ hf₁ bound bound_int bound_ge

open Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_setIntegral' [NormedSpace ℝ A] {s : Set X} (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) (hf₁ : ∀ᵐ x ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : AEStronglyMeasurable (fun x ↦ mkD ((spectrum 𝕜 a).restrict (f x)) 0) (μ.restrict s))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ := by
  nontriviality A
  refine cfc_setIntegral₀ _ _ hf₁ ⟨hf₂, ?_⟩ ha
  exact hasFiniteIntegral_mkD_restrict_of_bound _ _ hf₁ bound bound_int bound_ge

open Function Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_integral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X]
    (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂μ, ContinuousOn (f x) (spectrum 𝕜 a) := .of_forall fun x ↦
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨trivial, hz⟩
  refine cfc_integral₀ _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this bound bound_int bound_ge

open Function Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_setIntegral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  refine cfc_setIntegral₀ _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this bound bound_int bound_ge

end unital

section nonunital

open ContinuousMapZero

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X} [NonUnitalNormedRing A] [StarRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 A p]

/-- A version of `cfcₙ_apply` in terms of `ContinuousMapZero.mkD` -/
lemma cfcₙ_apply_mkD {f : 𝕜 → 𝕜} {a : A} (ha : p a := by cfc_tac) :
    cfcₙ f a = cfcₙHom (a := a) ha (mkD ((quasispectrum 𝕜 a).restrict f) 0) := by
  by_cases f_cont : ContinuousOn f (quasispectrum 𝕜 a)
  · by_cases f_zero : f 0 = 0
    · rw [cfcₙ_apply f a, mkD_of_continuousOn f_cont f_zero]
    · rw [cfcₙ_apply_of_not_map_zero a f_zero, mkD_of_not_zero, map_zero]
      exact f_zero
  · rw [cfcₙ_apply_of_not_continuousOn a f_cont, mkD_of_not_continuousOn f_cont, map_zero]

lemma cfcₙ_eq_cfcₙL_mkD {f : 𝕜 → 𝕜} {a : A} (ha : p a := by cfc_tac) :
    cfcₙ f a = cfcₙL (a := a) ha (mkD ((quasispectrum 𝕜 a).restrict f) 0) :=
  cfcₙ_apply_mkD

variable [CompleteSpace A]

lemma cfcₙL_integral [NormedSpace ℝ A] (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙL (a := a) ha (f x) ∂μ = cfcₙL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

lemma cfcₙHom_integral [NormedSpace ℝ A] (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙHom (a := a) ha (f x) ∂μ = cfcₙHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcₙL_integral a f hf₁ ha

lemma cfcₙL_integrable (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    Integrable (fun x ↦ cfcₙL (a := a) ha (f x)) μ :=
  ContinuousLinearMap.integrable_comp _ hf₁

lemma integrable_cfcₙ₀ (f : X → 𝕜 → 𝕜) (a : A)
    (hf : Integrable
      (fun x : X => mkD ((quasispectrum 𝕜 a).restrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  conv in cfcₙ _ _ => rw [cfcₙ_eq_cfcₙL_mkD (a := a) ha]
  exact cfcₙL_integrable _ _ hf ha

lemma integrableOn_cfcₙ₀ {s : Set X} (f : X → 𝕜 → 𝕜) (a : A)
    (hf : IntegrableOn
      (fun x : X => mkD ((quasispectrum 𝕜 a).restrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  exact integrable_cfcₙ₀ _ _ hf ha

lemma integrable_cfcₙ' (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) (hf₁ : ∀ᵐ x ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ᵐ x ∂μ, f x 0 = 0)
    (hf₃ : AEStronglyMeasurable
      (fun x : X => mkD ((quasispectrum 𝕜 a).restrict (f x)) 0) μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  refine integrable_cfcₙ₀ _ _ ⟨hf₃, ?_⟩ ha
  exact hasFiniteIntegral_mkD_restrict_of_bound _ _ hf₁ hf₂ bound bound_int bound_ge

lemma integrableOn_cfcₙ' {s : Set X} (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) (hf₁ : ∀ᵐ x ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (hf₃ : AEStronglyMeasurable
      (fun x : X => mkD ((quasispectrum 𝕜 a).restrict (f x)) 0) (μ.restrict s))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ :=
  integrable_cfcₙ' f bound a hf₁ hf₂ hf₃ bound_ge bound_int ha

open Set Function in
lemma integrable_cfcₙ [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂μ, f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  refine integrable_cfcₙ₀ _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact .of_forall fun x ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨trivial, hz⟩

open Set Function in
lemma integrableOn_cfcₙ [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  refine integrableOn_cfcₙ₀ _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩

open Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfcₙ_integral₀ [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ᵐ x ∂μ, f x 0 = 0)
    (hf₃ : Integrable
      (fun x : X => mkD ((quasispectrum 𝕜 a).restrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have key₁ (z : quasispectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((quasispectrum 𝕜 a).restrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₃]
    refine integral_congr_ae ?_
    filter_upwards [hf₁, hf₂] with x cont_x zero_x
    rw [mkD_apply_of_continuousOn cont_x zero_x]
  have key₂ (z : quasispectrum 𝕜 a) :
      ∫ x, f x z ∂μ = mkD ((quasispectrum 𝕜 a).restrict (fun z ↦ ∫ x, f x z ∂μ)) 0 z := by
    rw [mkD_apply_of_continuousOn]
    · rw [continuousOn_iff_continuous_restrict]
      refine continuous_congr key₁ |>.mpr ?_
      exact map_continuous (∫ x, mkD ((quasispectrum 𝕜 a).restrict (f x)) 0 ∂μ)
    · exact integral_eq_zero_of_ae hf₂
  simp_rw [cfcₙ_eq_cfcₙL_mkD (a := a) ha, cfcₙL_integral a _ hf₃ ha]
  congr
  ext z
  rw [← key₁, key₂]

open Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfcₙ_setIntegral₀ {s : Set X} [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (hf₃ : IntegrableOn
      (fun x : X => mkD ((quasispectrum 𝕜 a).restrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x in s, f x z ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ :=
  cfcₙ_integral₀ _ _ hf₁ hf₂ hf₃ ha

open Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfcₙ_integral' [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    (hf₁ : ∀ᵐ x ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ᵐ x ∂μ, f x 0 = 0)
    (hf₃ : AEStronglyMeasurable (fun x ↦ mkD ((quasispectrum 𝕜 a).restrict (f x)) 0) μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  refine cfcₙ_integral₀ _ _ hf₁ hf₂ ⟨hf₃, ?_⟩ ha
  exact hasFiniteIntegral_mkD_restrict_of_bound _ _ hf₁ hf₂ bound bound_int bound_ge

open Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfcₙ_setIntegral' [NormedSpace ℝ A] {s : Set X} (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) (hf₁ : ∀ᵐ x ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (hf₃ : AEStronglyMeasurable (fun x ↦ mkD ((quasispectrum 𝕜 a).restrict (f x)) 0) (μ.restrict s))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ := by
  refine cfcₙ_setIntegral₀ _ _ hf₁ hf₂ ⟨hf₃, ?_⟩ ha
  exact hasFiniteIntegral_mkD_restrict_of_bound _ _ hf₁ hf₂ bound bound_int bound_ge

open Function Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfcₙ_integral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X]
    (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂μ, f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a) := .of_forall fun x ↦
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨trivial, hz⟩
  refine cfcₙ_integral₀ _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this f_zero bound bound_int bound_ge

open Function Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfcₙ_setIntegral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  refine cfcₙ_setIntegral₀ _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf f_zero
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this f_zero bound bound_int bound_ge

end nonunital
