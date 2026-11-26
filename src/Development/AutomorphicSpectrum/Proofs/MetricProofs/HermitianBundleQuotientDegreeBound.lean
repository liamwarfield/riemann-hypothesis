module

public import GroundTheory.HeightsAndTheta.Heights.Slopes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedChartSectionForm

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AmpleLineBundles.SlopeMaxLeOfComparableMetric
section -- merged from Development.WeilBound.CoreStatements.AmpleLineBundles.StandardHermitianBundleSemistable
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

def tailIncl (K : Type) [Field K] (r : ℕ) : (Fin r → 𝓞 K) →ₗ[𝓞 K] (Fin (r + 1) → 𝓞 K) where
  toFun x := Fin.cons 0 x
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

omit [NumberField K] in
theorem coord_tail_zero (σ : K →+* ℂ) (r : ℕ) (x : Fibre σ (Fin r → 𝓞 K)) :
    standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) x) 0 = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [standardCoord, tailIncl]
  | add a b ha hb => simp only [map_add (f := _), PiLp.add_apply] at ha hb ⊢; rw [ha, hb, add_zero]

omit [NumberField K] in
theorem coord_tail_succ (σ : K →+* ℂ) (r : ℕ) (x : Fibre σ (Fin r → 𝓞 K)) (j : Fin r) :
    standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) x) j.succ =
      standardCoord K σ (Fin r) x j := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [standardCoord, tailIncl]
  | add a b ha hb => simp only [map_add (f := _), PiLp.add_apply] at ha hb ⊢; rw [ha, hb]

omit [NumberField K] in
theorem coord_head (σ : K →+* ℂ) (r : ℕ) (x : Fibre σ (Fin (r + 1) → 𝓞 K)) :
    integersCoord K σ ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) x) =
      standardCoord K σ (Fin (r + 1)) x 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [standardCoord, integersCoord]
  | add a b ha hb => simp only [map_add (f := _)] at ha hb ⊢; rw [ha, hb]; rfl

theorem coord_zero_of_orth (σ : K →+* ℂ) (r : ℕ) (v : Fibre σ (Fin (r + 1) → 𝓞 K))
    (hv : ∀ w : Fibre σ (Fin r → 𝓞 K), ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner
      ((tailIncl K r).lTensor (ComplexAt σ) w) v = 0) (j : Fin r) :
    standardCoord K σ (Fin (r + 1)) v j.succ = 0 := by
  have h := hv (1 ⊗ₜ Pi.single j 1)
  change inner ℂ (standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) (1 ⊗ₜ Pi.single j 1)))
      (standardCoord K σ (Fin (r + 1)) v) = 0 at h
  rw [PiLp.inner_apply, Fin.sum_univ_succ] at h
  simp only [coord_tail_zero, coord_tail_succ, inner_zero_left, zero_add] at h
  simpa [standardCoord, Pi.single_apply] using h

theorem tail_iso (σ : K →+* ℂ) (r : ℕ) (x y : Fibre σ (Fin r → 𝓞 K)) :
    ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner
      ((tailIncl K r).lTensor (ComplexAt σ) x) ((tailIncl K r).lTensor (ComplexAt σ) y) =
      ((HermitianMetric.standard K (Fin r)).form σ).inner x y := by
  show inner ℂ (standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) x))
      (standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) y)) =
    inner ℂ (standardCoord K σ (Fin r) x) (standardCoord K σ (Fin r) y)
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [coord_tail_zero, coord_tail_succ, inner_zero_left, zero_add]

theorem head_coiso (σ : K →+* ℂ) (r : ℕ) (x y : Fibre σ (Fin (r + 1) → 𝓞 K))
    (hy : ∀ w : Fibre σ (Fin r → 𝓞 K), ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner
      ((tailIncl K r).lTensor (ComplexAt σ) w) y = 0) :
    ((HermitianMetric.integers K).form σ).inner
      ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) x)
      ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) y) =
      ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner x y := by
  show inner ℂ (integersCoord K σ ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) x))
      (integersCoord K σ ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) y)) =
    inner ℂ (standardCoord K σ (Fin (r + 1)) x) (standardCoord K σ (Fin (r + 1)) y)
  rw [coord_head, coord_head, PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [coord_zero_of_orth σ r y hy, inner_zero_right, Finset.sum_const_zero, add_zero]

def stdExt (K : Type) [Field K] [NumberField K] (r : ℕ) :
    HermitianExtension (HermitianBundle.standard K r) (HermitianBundle.standard K (r + 1))
      (HermitianBundle.integers K) where
  incl := tailIncl K r
  proj := (LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K)
  incl_injective := fun a b h => funext fun j => congrFun h j.succ
  proj_surjective := fun a => ⟨fun _ => a, rfl⟩
  exact := by
    intro y
    constructor
    · intro hy
      refine ⟨fun j => y j.succ, funext fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (show y 0 = 0 from hy).symm
      · rfl
    · rintro ⟨a, rfl⟩
      rfl
  incl_isometric σ x y := tail_iso σ r x y
  proj_coisometric σ x y _ hy := head_coiso σ r x y hy

private theorem exists_injective_quotient_span_map {M N : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup N]
    [Module (𝓞 K) N] (φ : M →ₗ[𝓞 K] N) (hφ : Function.Injective φ) (m : M) :
    ∃ f : M ⧸ Submodule.span (𝓞 K) {m} → N ⧸ Submodule.span (𝓞 K) {φ m}, Function.Injective f := by
  have h : Submodule.span (𝓞 K) {m} ≤ (Submodule.span (𝓞 K) {φ m}).comap φ := by
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap]
    exact Submodule.mem_span_singleton_self _
  refine ⟨Submodule.mapQ _ _ φ h, fun x y hxy => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy
  rw [Submodule.Quotient.eq]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hxy
  exact Submodule.mem_span_singleton.2 ⟨c, hφ (by rw [map_smul, map_sub]; exact hc)⟩

set_option maxHeartbeats 400000 in
theorem integers_deg_le (G : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) :
    (HermitianBundle.integers K).degree G ≤ 0 := by
  by_cases hG : G = ⊥
  · rw [hG, HermitianBundle.degree_bot]
  obtain ⟨a, haG, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hG
  let sG : Fin 1 → G := fun _ => ⟨a, haG⟩
  let sT : Fin 1 → (⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) :=
    fun _ => ⟨a, Submodule.mem_top⟩
  have liG : LinearIndependent (𝓞 K) sG :=
    linearIndependent_unique_iff.2 (fun h => ha0 (congrArg Subtype.val h))
  have liT : LinearIndependent (𝓞 K) sT :=
    linearIndependent_unique_iff.2 (fun h => ha0 (congrArg Subtype.val h))
  have rT : (HermitianBundle.integers K).rank ⊤ = 1 := by
    show Module.finrank (𝓞 K) (⊤ : Submodule (𝓞 K) (𝓞 K)) = 1
    rw [finrank_top, Module.finrank_self]
  have rG : (HermitianBundle.integers K).rank G = 1 := by
    refine le_antisymm ?_ ?_
    · show Module.finrank (𝓞 K) G ≤ 1
      calc Module.finrank (𝓞 K) G ≤ Module.finrank (𝓞 K) (𝓞 K) := Submodule.finrank_le G
        _ = 1 := Module.finrank_self _
    · have h := liG.fintype_card_le_finrank
      rw [Fintype.card_fin] at h
      exact h
  have hGd := (HermitianBundle.integers K).degree_eq_of_linearIndependent G liG (by simp [rG])
  have hTd := (HermitianBundle.integers K).degree_eq_of_linearIndependent ⊤ liT (by simp [rT])
  have hT0 : (HermitianBundle.integers K).degree ⊤ = 0 := by
    rw [HermitianBundle.degree_top_eq_arithDegree, HermitianBundle.arithDegree_integers]
  have hsame : (fun i => (sG i : (HermitianBundle.integers K).carrier)) =
      fun i => (sT i : (HermitianBundle.integers K).carrier) := rfl
  rw [hsame] at hGd
  rw [Set.range_const] at hGd hTd
  have hfin : Finite (𝓞 K ⧸ Ideal.span {(show 𝓞 K from a)}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by rw [Ne, Ideal.span_singleton_eq_bot]; exact ha0)
  obtain ⟨f1, hf1⟩ := exists_injective_quotient_span_map
    (⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier).subtype Subtype.val_injective (sT 0)
  obtain ⟨f2, hf2⟩ := exists_injective_quotient_span_map (Submodule.inclusion (le_top : G ≤ ⊤))
    (Submodule.inclusion_injective _) (sG 0)
  have hfinT : Finite ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
      Submodule.span (𝓞 K) {sT 0}) := by
    have : Finite ((HermitianBundle.integers K).carrier ⧸ Submodule.span (𝓞 K)
      {((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier).subtype (sT 0))}) := hfin
    exact Finite.of_injective f1 hf1
  have hfinT' : Finite ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
      Submodule.span (𝓞 K) {Submodule.inclusion (le_top : G ≤ ⊤) (sG 0)}) := hfinT
  have hfinG : Finite (G ⧸ Submodule.span (𝓞 K) {sG 0}) := Finite.of_injective f2 hf2
  have hle : Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0}) ≤
      Nat.card ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
        Submodule.span (𝓞 K) {sT 0}) :=
    Nat.card_le_card_of_injective f2 hf2
  have hpos : 0 < Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0}) := Nat.card_pos
  have hlog := Real.log_le_log (by exact_mod_cast hpos)
    (Nat.cast_le.2 hle : (Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0}) : ℝ) ≤ _)
  have e1 : (HermitianBundle.integers K).degree G =
      Real.log (Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0})) -
        1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet (HermitianBundle.integers K).metric σ
          fun i => (sT i : (HermitianBundle.integers K).carrier)) := hGd
  have e2 : (HermitianBundle.integers K).degree ⊤ =
      Real.log (Nat.card ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
        Submodule.span (𝓞 K) {sT 0})) -
        1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet (HermitianBundle.integers K).metric σ
          fun i => (sT i : (HermitianBundle.integers K).carrier)) := hTd
  linarith

theorem std_deg (r : ℕ) : (∀ F, (HermitianBundle.standard K r).degree F ≤ 0) ∧
    (HermitianBundle.standard K r).degree ⊤ = 0 := by
  induction r with
  | zero =>
    have hs : ∀ F : Submodule (𝓞 K) (HermitianBundle.standard K 0).carrier, F = ⊥ := by
      intro F
      refine (Submodule.eq_bot_iff F).2 fun x _ => ?_
      show (x : Fin 0 → 𝓞 K) = 0
      funext i
      exact i.elim0
    refine ⟨fun F => ?_, ?_⟩
    · rw [hs F, HermitianBundle.degree_bot]
    · rw [hs ⊤, HermitianBundle.degree_bot]
  | succ r ih =>
    refine ⟨fun F => ?_, ?_⟩
    · have h1 := ih.1 (Submodule.comap (stdExt K r).incl F)
      have h2 := integers_deg_le (Submodule.map (stdExt K r).proj F)
      have h3 := (stdExt K r).degree_submodule_le F
      linarith
    · rw [HermitianBundle.degree_top_eq_arithDegree, (stdExt K r).arithDegree_eq_add,
        ← HermitianBundle.degree_top_eq_arithDegree, ih.2,
        HermitianBundle.arithDegree_integers, add_zero]

theorem standard_hermitian_bundle_semistable : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ), (HermitianBundle.standard K r).slopeMax ≤ 0 ∧ (HermitianBundle.standard K r).normDegree ⊤ = 0 := by
  intro K _ _ r
  have h := std_deg (K := K) r
  refine ⟨?_, ?_⟩
  · refine iSup_le fun F => iSup_le fun _ => ?_
    have hF : HermitianBundle.slope _ F ≤ 0 := by
      unfold HermitianBundle.slope HermitianBundle.normDegree
      refine div_nonpos_iff.2 (Or.inr ⟨div_nonpos_iff.2 (Or.inr ⟨h.1 F, by positivity⟩), by positivity⟩)
    exact_mod_cast hF
  · simp [HermitianBundle.normDegree, h.2]

end CoverDenseAlt
end

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

theorem sqAt_std (r : ℕ) (σ : K →+* ℂ) (y : Fibre σ (Fin r → 𝓞 K)) :
    sqAt (HermitianBundle.standard K r) σ y = ∑ a, ‖standardCoord K σ (Fin r) y a‖ ^ 2 := by
  have h := HermitianMetric.standard_inner K (Fin r) σ y y
  unfold sqAt
  erw [h]
  simp only [Complex.conj_mul', Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

omit [NumberField K] in
theorem sum_coord {M : Type} [AddCommGroup M] [Module (𝓞 K) M] {r : ℕ}
    (b : Module.Basis (Fin r) (𝓞 K) M) (σ : K →+* ℂ) (y : Fibre σ (Fin r → 𝓞 K)) :
    ∑ a, ComplexAt.ofComplex σ (standardCoord K σ (Fin r) y a) ⊗ₜ[𝓞 K] b a =
      b.equivFun.symm.toLinearMap.lTensor (ComplexAt σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul z f =>
    have hc : ∀ a, ComplexAt.ofComplex σ (standardCoord K σ (Fin r) (z ⊗ₜ f) a) = f a • z := by
      intro a
      simp [standardCoord]
    simp only [hc, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    simp only [map_add (f := _), WithLp.ofLp_add, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

theorem slopeMax_le_of_comparable_metric : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C := by
  intro K _ _ E r b C hC h
  have hC0 : 0 < C := by linarith
  let φ : E.carrier →ₗ[𝓞 K] (HermitianBundle.standard K r).carrier := b.equivFun.toLinearMap
  let ψ : (HermitianBundle.standard K r).carrier →ₗ[𝓞 K] E.carrier := b.equivFun.symm.toLinearMap
  have hb : ∀ (σ : K →+* ℂ) (y : Fibre σ (HermitianBundle.standard K r).carrier),
      C⁻¹ * sqAt (HermitianBundle.standard K r) σ y ≤ sqAt E σ (ψ.lTensor (ComplexAt σ) y) ∧
      sqAt E σ (ψ.lTensor (ComplexAt σ) y) ≤ C * sqAt (HermitianBundle.standard K r) σ y := by
    intro σ y
    have := h σ fun a => standardCoord K σ (Fin r) y a
    rw [sum_coord b σ y, ← sqAt_std r σ y] at this
    exact this
  have hψφ : ψ ∘ₗ φ = LinearMap.id := LinearMap.ext fun x => b.equivFun.symm_apply_apply x
  have h1 := normDegree_le_of_metric_bounded_map K E (HermitianBundle.standard K r) φ C b.equivFun.injective hC0 (fun σ x => by
    have := (hb σ (φ.lTensor (ComplexAt σ) x)).1
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hψφ, LinearMap.lTensor_id,
      LinearMap.id_apply, inv_mul_le_iff₀ hC0] at this
    exact this)
  have h2 := normDegree_le_of_metric_bounded_map K (HermitianBundle.standard K r) E ψ C b.equivFun.symm.injective hC0
    fun σ y => (hb σ y).2
  obtain ⟨s1, s2⟩ := standard_hermitian_bundle_semistable K r
  refine ⟨h1.2.trans ?_, ?_⟩
  · refine (add_le_add_left s1 _).trans ?_
    rw [zero_add]
  · have a := h1.1 ⊤
    have c := h2.1 ⊤
    have e1 : (⊤ : Submodule (𝓞 K) E.carrier).map φ = ⊤ := by
      rw [Submodule.map_top]; exact LinearMap.range_eq_top.mpr b.equivFun.surjective
    have e2 : (⊤ : Submodule (𝓞 K) (HermitianBundle.standard K r).carrier).map ψ = ⊤ := by
      rw [Submodule.map_top]; exact LinearMap.range_eq_top.mpr b.equivFun.symm.surjective
    have r1 : E.rank ⊤ = r := by
      rw [HermitianBundle.rank, finrank_top, Module.finrank_eq_card_basis b, Fintype.card_fin]
    have r2 : (HermitianBundle.standard K r).rank ⊤ = r := by
      rw [HermitianBundle.rank, finrank_top]
      exact Module.finrank_fin_fun (𝓞 K)
    rw [e1, s2, r1] at a
    rw [e2, s2, r2] at c
    rw [abs_le]
    constructor <;> linarith

end CoverDenseAlt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SlopeBoundComparableMetric
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SlopeBoundComparableMetric
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem basis_slope_degree_bound : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C :=
  @CoverDenseAlt.slopeMax_le_of_comparable_metric

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SlopeBoundComparableMetricStatement
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_bound_comparable_metric : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.basis_slope_degree_bound | exact GlobalTheory.CompanionTheory.Ar.basis_slope_degree_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.basis_slope_degree_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeBoundedMap
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeBoundedMap
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.MapCompare

theorem main : ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ), Function.Injective φ → 0 < c → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) → (∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c) ∧ E.slopeMax ≤ E'.slopeMax + ((Real.log c / 2 : ℝ) : EReal) :=
  CoverDenseAlt.normDegree_le_of_metric_bounded_map

end GlobalTheory.CompanionTheory.Ar.MapCompare
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeBoundedMapStatement
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_bounded_map : ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ), Function.Injective φ → 0 < c → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) → (∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c) ∧ E.slopeMax ≤ E'.slopeMax + ((Real.log c / 2 : ℝ) : EReal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MapCompare.main | exact GlobalTheory.CompanionTheory.Ar.MapCompare.main | (intros; apply GlobalTheory.CompanionTheory.Ar.MapCompare.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianBundleQuotientDegreeBound
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PtBoundary

variable {K : Type} [Field K] [NumberField K]

theorem finrank_submodule_of_torsion {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] (N : Submodule R M) (h : ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x ∈ N) :
    Module.finrank R N = Module.finrank R M := by
  have h0 : Module.rank R (M ⧸ N) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨a, ha, hax⟩ := h x
    refine ⟨a, ha, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hax
  have h1 := rank_quotient_add_rank_of_isDomain N
  rw [h0, zero_add] at h1
  simp only [Module.finrank, h1]

theorem saturated_ker (E E' : HermitianBundle.{0} K) (q : E.carrier →ₗ[𝓞 K] E'.carrier) :
    E.Saturated (LinearMap.ker q) := by
  intro a x ha hx
  rw [LinearMap.mem_ker, map_smul] at hx
  rw [LinearMap.mem_ker]
  have : Module.IsTorsionFree (𝓞 K) E'.carrier := inferInstance
  exact (smul_eq_zero.mp hx).resolve_left ha

def barMap (E E' : HermitianBundle.{0} K) (P : Submodule (𝓞 K) E.carrier) (hP : E.Saturated P)
    (q : E.carrier →ₗ[𝓞 K] E'.carrier) (hq : P ≤ LinearMap.ker q) :
    (E.quot P hP).carrier →ₗ[𝓞 K] E'.carrier :=
  P.liftQ q hq

theorem sqAt_barMap_le (E E' : HermitianBundle.{0} K) (P : Submodule (𝓞 K) E.carrier)
    (hP : E.Saturated P) (q : E.carrier →ₗ[𝓞 K] E'.carrier) (hq : P ≤ LinearMap.ker q) (c : ℝ)
    (h : ∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier),
      sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x)
    (σ : K →+* ℂ) (y : Fibre σ (E.quot P hP).carrier) :
    sqAt E' σ ((barMap E E' P hP q hq).lTensor (ComplexAt σ) y) ≤
      c * sqAt (E.quot P hP) σ y := by
  letI := HermitianBundle.quot_projective hP
  let V := subFibre E.metric σ P
  let y' : Fibre σ (E.carrier ⧸ P) := y
  let s : Fibre σ E.carrier := fibreMap σ (HermitianBundle.quotSection E P hP) y'
  let v : FibreSpace E.metric σ := HermitianBundle.quotFibreMap E P hP σ y
  let x : Fibre σ E.carrier := (FibreSpace.equiv E.metric σ).symm v
  have hvx : FibreSpace.equiv E.metric σ x = v := by simp [x]
  have hdiff : FibreSpace.equiv E.metric σ s - v ∈ V := by
    have hv : v = Vᗮ.starProjection (FibreSpace.equiv E.metric σ s) := rfl
    have e : Vᗮ.starProjection (FibreSpace.equiv E.metric σ s) =
        FibreSpace.equiv E.metric σ s - V.starProjection (FibreSpace.equiv E.metric σ s) := by
      rw [Submodule.starProjection_orthogonal']
      rfl
    rw [hv, e, sub_sub_cancel]
    exact V.starProjection_apply_mem _
  obtain ⟨w, hw⟩ := hdiff
  have hw' : fibreMap σ P.subtype w = s - x := by
    apply (FibreSpace.equiv E.metric σ).injective
    rw [map_sub, hvx]
    exact hw
  have hsub : q ∘ₗ P.subtype = 0 := by
    ext z
    exact hq z.2
  have hsec : q ∘ₗ HermitianBundle.quotSection E P hP = P.liftQ q hq := by
    have h1 : P.liftQ q hq ∘ₗ P.mkQ = q := Submodule.liftQ_mkQ P q hq
    calc q ∘ₗ HermitianBundle.quotSection E P hP
        = P.liftQ q hq ∘ₗ (P.mkQ ∘ₗ HermitianBundle.quotSection E P hP) := by
          rw [← LinearMap.comp_assoc, h1]
      _ = P.liftQ q hq := by
          rw [HermitianBundle.mkQ_comp_quotSection, LinearMap.comp_id]
  have hqx : (barMap E E' P hP q hq).lTensor (ComplexAt σ) y = q.lTensor (ComplexAt σ) x := by
    have h1 : fibreMap σ q s = (barMap E E' P hP q hq).lTensor (ComplexAt σ) y := by
      have h0 : fibreMap σ q s = fibreMap σ (P.liftQ q hq) y' :=
        (fibreMap_fibreMap σ q (HermitianBundle.quotSection E P hP) y').trans
          (congrArg (fun f => fibreMap σ f y') hsec)
      exact h0
    have h2 : fibreMap σ q (s - x) = 0 := by
      rw [← hw', fibreMap_fibreMap, hsub]
      simp [fibreMap]
    rw [map_sub, h1] at h2
    exact sub_eq_zero.mp h2
  have hnorm : sqAt (E.quot P hP) σ y = sqAt E σ x := by
    have h1 : sqAt E σ x = (inner ℂ (FibreSpace.equiv E.metric σ x) (FibreSpace.equiv E.metric σ x)).re := rfl
    rw [h1, hvx]
    rfl
  rw [hqx, hnorm]
  exact h σ x

theorem normDegree_top_eq (E : HermitianBundle.{0} K) :
    E.normDegree ⊤ = E.arithDegree / Module.finrank ℚ K := by
  rw [HermitianBundle.normDegree, HermitianBundle.degree_top_eq_arithDegree]

theorem final_real (C L ρ m x g : ℝ) (hC : 1 ≤ C) (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hm : 0 ≤ m) (hx : 0 ≤ x) (hg : 0 ≤ g)
    (hρg : ρ ≤ g) (hmx : m ≤ x + g * L) :
    C * Real.log (2 + ρ + m) + L / 2 ≤
      (C + g + g * L + L) * Real.log (2 + (C + g + g * L + L) + x) + (C + g + g * L + L) := by
  have hgL : 0 ≤ g * L := mul_nonneg hg hL
  set C' := C + g + g * L + L with hC'
  have h1 : 2 + ρ + m ≤ 2 + C' + x := by rw [hC']; linarith
  have h0 : 0 < 2 + ρ + m := by linarith
  have h2 : Real.log (2 + ρ + m) ≤ Real.log (2 + C' + x) := Real.log_le_log h0 h1
  have h3 : 0 ≤ Real.log (2 + ρ + m) := Real.log_nonneg (by linarith)
  have h4 : C ≤ C' := by rw [hC']; linarith
  have h5 : C * Real.log (2 + ρ + m) ≤ C' * Real.log (2 + C' + x) :=
    mul_le_mul h4 h2 h3 (by linarith)
  have h6 : L / 2 ≤ C' := by rw [hC']; linarith
  linarith

theorem slopeMax_le_log : ∀ (g : ℕ) (C : ℝ), 1 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (r : ℕ) (ε : Fin r → E.carrier) (q : E.carrier →ₗ[𝓞 K] E'.carrier), Module.finrank (𝓞 K) E.carrier = g → LinearIndependent (𝓞 K) ε → LinearMap.ker q = Submodule.span (𝓞 K) (Set.range ε) → (∀ e' : E'.carrier, ∃ (a : 𝓞 K) (e : E.carrier), a ≠ 0 ∧ q e = a • e') → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2) → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ C * sqAt E σ x) → E'.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 K) E'.carrier + max (-E'.normDegree ⊤) 0) : ℝ) : EReal) → E.slopeMax ≤ ((C' * Real.log (2 + C' + max (-E.normDegree ⊤) 0) + C' : ℝ) : EReal) := by
  intro g C hC
  have hC0 : 0 < C := by linarith
  have hL : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨C + g + g * Real.log C + Real.log C, by positivity, ?_⟩
  intro K _ _ E E' r ε q hg hli hker hfull hgram hexp hslope
  set L := Real.log C with hLdef
  set P : Submodule (𝓞 K) E.carrier := Submodule.span (𝓞 K) (Set.range ε) with hPdef
  have hP : E.Saturated P := hker ▸ saturated_ker E E' q
  have hPq : P ≤ LinearMap.ker q := hker.ge
  set X := HermitianBundle.subQuotExtension E P hP with hX
  set φ := barMap E E' P hP q hPq with hφ
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have hφq : ∀ e, φ (P.mkQ e) = q e := fun e => rfl

  let b : Module.Basis (Fin r) (𝓞 K) (E.sub P).carrier := Module.Basis.span hli
  have hb : ∀ (σ : K →+* ℂ) (w : Fin r → ℂ),
      sqAt (E.sub P) σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) =
        sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) := by
    intro σ w
    have h1 : X.incl.lTensor (ComplexAt σ) (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) =
        ∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.lTensor_tmul]
      congr 1
      exact congrArg Subtype.val (Module.Basis.span_apply hli a)
    rw [← h1]
    simp only [sqAt]
    rw [X.incl_isometric]
  obtain ⟨hP1, hP2⟩ := GlobalTheory.T.slope_bound_comparable_metric K (E.sub P) r b C hC (fun σ w => by rw [hb]; exact hgram σ w)

  obtain ⟨hQ1, hQ2⟩ := GlobalTheory.T.normalized_degree_bounded_map K (E.quot P hP) E' φ C hφinj hC0
    (fun σ y => sqAt_barMap_le E E' P hP q hPq C hexp σ y)

  have hrP : Module.finrank (𝓞 K) (E.sub P).carrier = r := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hrk := X.finrank_eq
  have hrange : Module.finrank (𝓞 K) ((⊤ : Submodule (𝓞 K) (E.quot P hP).carrier).map φ) =
      Module.finrank (𝓞 K) E'.carrier := by
    apply finrank_submodule_of_torsion
    intro e'
    obtain ⟨a, e, ha, he⟩ := hfull e'
    exact ⟨a, ha, he ▸ ⟨P.mkQ e, trivial, hφq e⟩⟩
  have hrQ : Module.finrank (𝓞 K) (E.quot P hP).carrier = Module.finrank (𝓞 K) E'.carrier := by
    rw [← hrange, Submodule.map_top]
    exact (LinearMap.finrank_range_of_inj hφinj).symm
  have hsum : r + Module.finrank (𝓞 K) E'.carrier = g := by
    rw [← hg, hrk, hrP, hrQ]
  obtain ⟨hI1, -⟩ := GlobalTheory.T.normalized_degree_full_rank_sublattice K E' ((⊤ : Submodule (𝓞 K) (E.quot P hP).carrier).map φ) hrange

  have hdeg : E.normDegree ⊤ = (E.sub P).normDegree ⊤ + (E.quot P hP).normDegree ⊤ := by
    rw [normDegree_top_eq, normDegree_top_eq, normDegree_top_eq, X.arithDegree_eq_add, add_div]
  have hQd := hQ1 ⊤
  have hrkTop : (E.quot P hP).rank ⊤ = Module.finrank (𝓞 K) E'.carrier := by
    rw [HermitianBundle.rank, finrank_top, hrQ]
  rw [hrkTop] at hQd
  set ρ : ℕ := Module.finrank (𝓞 K) E'.carrier with hρ
  have hsumR : (r : ℝ) + ρ = g := by exact_mod_cast hsum
  have hP2' := (abs_le.mp hP2).2
  have hgL : (g : ℝ) * L = r * L + ρ * L := by rw [← hsumR]; ring
  have hrL : 0 ≤ (r : ℝ) * L := by positivity
  have hρL : 0 ≤ (ρ : ℝ) * L := by positivity
  have hm : max (-E'.normDegree ⊤) 0 ≤ max (-E.normDegree ⊤) 0 + g * L := by
    apply max_le
    · have := le_max_left (-E.normDegree ⊤) 0
      nlinarith
    · have := le_max_right (-E.normDegree ⊤) 0
      nlinarith
  have hreal := final_real C L ρ (max (-E'.normDegree ⊤) 0) (max (-E.normDegree ⊤) 0) g hC hL
    (by positivity) (le_max_right _ _) (le_max_right _ _) (by positivity)
    (by have : (0 : ℝ) ≤ r := by positivity
        linarith) hm
  have hfirst : L / 2 ≤ (C + g + g * L + L) * Real.log (2 + (C + g + g * L + L) + max (-E.normDegree ⊤) 0) + (C + g + g * L + L) := by
    have h0 : (0 : ℝ) ≤ g := by positivity
    have h1 : 0 ≤ (C + g + g * L + L) := by positivity
    have h2 : 0 ≤ Real.log (2 + (C + g + g * L + L) + max (-E.normDegree ⊤) 0) :=
      Real.log_nonneg (by have := le_max_right (-E.normDegree ⊤) 0; linarith)
    have h3 := mul_nonneg h1 h2
    nlinarith
  refine (SlopeMaxExtension.main K _ _ _ X).trans (max_le ?_ ?_)
  · exact hP1.trans (by exact_mod_cast hfirst)
  · refine hQ2.trans ((add_le_add_left hslope _).trans ?_)
    rw [← EReal.coe_add]
    exact_mod_cast hreal

end GlobalTheory.CompanionTheory.Ar.PtBoundary

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianBundleQuotientDegreeBoundStatement
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_bundle_quotient_degree_bound : ∀ (g : ℕ) (C : ℝ), 1 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (r : ℕ) (ε : Fin r → E.carrier) (q : E.carrier →ₗ[𝓞 K] E'.carrier), Module.finrank (𝓞 K) E.carrier = g → LinearIndependent (𝓞 K) ε → LinearMap.ker q = Submodule.span (𝓞 K) (Set.range ε) → (∀ e' : E'.carrier, ∃ (a : 𝓞 K) (e : E.carrier), a ≠ 0 ∧ q e = a • e') → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2) → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ C * sqAt E σ x) → E'.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 K) E'.carrier + max (-E'.normDegree ⊤) 0) : ℝ) : EReal) → E.slopeMax ≤ ((C' * Real.log (2 + C' + max (-E.normDegree ⊤) 0) + C' : ℝ) : EReal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log | exact GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log | (intros; apply GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log <;> assumption)
end
