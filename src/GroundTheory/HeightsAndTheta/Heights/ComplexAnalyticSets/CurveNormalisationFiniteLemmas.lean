module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalMaxIdeals
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGradDensSheetBound
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CurveNormalisationFiniteLemmas
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets FieldNumbers

noncomputable section

theorem exists_finset_span_integral_of_div (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O Ω : Type}
    [CommRing O] [Field Ω] [Algebra O Ω] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f)
    (hΩ : ∀ x : Ω, ∃ a b : O, x = algebraMap O Ω a / algebraMap O Ω b) :
    ∃ t : Finset Ω, ∀ x : Ω, IsIntegral O x → x ∈ Submodule.span O (t : Set Ω) := by
  let ψ : MvPolynomial (Fin n) ℂ →+* Ω := (algebraMap O Ω).comp φ
  let _ : Algebra ℂ Ω := (ψ.comp C).toAlgebra
  let S : Set Ω := Set.range fun i ↦ ψ (X i)
  have hpoly : ∀ f, ψ f ∈ Algebra.adjoin ℂ S := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f i hf => rw [map_mul]; exact mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
  let A : Subalgebra ℂ Ω :=
    { toSubsemiring := (algebraMap O Ω).rangeS, algebraMap_mem' := fun c ↦ ⟨φ (C c), rfl⟩ }
  have hRA : Algebra.adjoin ℂ S ≤ A := Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact ⟨φ (X i), rfl⟩)
  have hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin ℂ S, ∃ d ∈ Algebra.adjoin ℂ S, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹ := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨f, s, hs, ho⟩ := hφ o
    refine ⟨ψ f, hpoly f, ψ s, hpoly s, (hs.map (algebraMap O Ω)).ne_zero, ⟨↑hs.unit⁻¹, ?_⟩, ?_⟩
    · change algebraMap O Ω ↑hs.unit⁻¹ = (algebraMap O Ω (φ s))⁻¹
      rw [map_units_inv, IsUnit.unit_spec]
    · refine (eq_mul_inv_iff_mul_eq₀ (hs.map (algebraMap O Ω)).ne_zero).2 ?_
      change algebraMap O Ω o * algebraMap O Ω (φ s) = algebraMap O Ω (φ f)
      rw [← map_mul, ho]
  have hE : ∀ x : Ω, x ∈ IntermediateField.adjoin ℂ S := by
    have hA : ∀ a ∈ A, a ∈ IntermediateField.adjoin ℂ S := by
      intro a ha
      obtain ⟨r, hr, d, hd, -, -, rfl⟩ := hloc a ha
      exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hr)
        (inv_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hd))
    intro x
    obtain ⟨a, b, rfl⟩ := hΩ x
    exact div_mem (hA _ ⟨a, rfl⟩) (hA _ ⟨b, rfl⟩)
  have hfin : FiniteDimensional (IntermediateField.adjoin ℂ S)
      (IntermediateField.extendScalars (le_refl (IntermediateField.adjoin ℂ S))) := by
    rw [IntermediateField.extendScalars_self]; infer_instance
  obtain ⟨t, -, ht⟩ := exists_finset_integral_span hN (Set.finite_range _) A _ hRA hloc le_rfl hfin
  let _ : Algebra O A := ((algebraMap O Ω).codRestrict A fun o ↦ (⟨o, rfl⟩ : algebraMap O Ω o ∈ (algebraMap O Ω).rangeS)).toAlgebra
  have : IsScalarTower O A Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsur : Function.Surjective (algebraMap O A) := by rintro ⟨_, o, rfl⟩; exact ⟨o, rfl⟩
  refine ⟨t, fun x hx ↦ ?_⟩
  rw [← Submodule.restrictScalars_span O A hsur]
  exact ht x (hE x) hx.tower_top

theorem exists_algHom_span_of_mem_minimalPrimes (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ}
    {O : Type} [CommRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) {p : Ideal O} (hp : p ∈ minimalPrimes O) :
    ∃ g : FractionRing O →ₐ[O] FractionRing (O ⧸ p), ∃ t : Finset (FractionRing (O ⧸ p)),
      ∀ x : FractionRing O, IsIntegral O x → g x ∈ Submodule.span O (t : Set (FractionRing (O ⧸ p))) := by
  have := Ideal.IsMinimalPrime.isPrime hp
  have hu : ∀ y : nonZeroDivisors O, IsUnit (Algebra.ofId O (FractionRing (O ⧸ p)) y) := by
    intro y
    refine IsUnit.mk0 _ fun h ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes ?_ hp y.2
    have h' : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p y) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by rw [map_zero]; exact h
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ h')
  obtain ⟨t, ht⟩ := exists_finset_span_integral_of_div hN φ hφ (Ω := FractionRing (O ⧸ p)) fun x ↦ by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O ⧸ p) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨a, b, rfl⟩
  exact ⟨IsLocalization.liftAlgHom (M := nonZeroDivisors O) hu, t, fun x hx ↦ ht _ (hx.map _)⟩

theorem finite_integralClosure_of_isReduced (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O : Type}
    [CommRing O] [IsReduced O] [IsNoetherianRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) :
    Module.Finite O (integralClosure O (FractionRing O)) := by
  have := (minimalPrimes.finite_of_isNoetherianRing O).to_subtype
  choose g t ht using fun p : minimalPrimes O ↦ exists_algHom_span_of_mem_minimalPrimes hN φ hφ p.2
  let F : integralClosure O (FractionRing O) →ₗ[O]
      ((p : minimalPrimes O) → Submodule.span O (t p : Set (FractionRing (O ⧸ (p : Ideal O))))) :=
    LinearMap.pi fun p ↦ LinearMap.codRestrict _
      ((g p).toLinearMap ∘ₗ (integralClosure O (FractionRing O)).val.toLinearMap) fun x ↦ ht p x x.2
  refine Module.Finite.of_injective F ((injective_iff_map_eq_zero F).2 fun x hx ↦ ?_)
  have h0 : ∀ p : minimalPrimes O, g p x = 0 := fun p ↦ congrArg Subtype.val (congr_fun hx p)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) (x : FractionRing O)
  have ha : a ∈ sInf (minimalPrimes O) := by
    refine Ideal.mem_sInf.2 fun p hp ↦ ?_
    have := Ideal.IsMinimalPrime.isPrime hp
    have e : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p a) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by
      rw [map_zero]
      change algebraMap O (FractionRing (O ⧸ p)) a = 0
      rw [← (g ⟨p, hp⟩).commutes, ← hab, map_mul, h0, zero_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ e)
  rw [Ideal.sInf_minimalPrimes, Ideal.mem_radical_iff] at ha
  obtain ⟨k, hk⟩ := ha
  have ha0 : a = 0 := IsNilpotent.eq_zero ⟨k, by simpa using hk⟩
  rw [ha0, map_zero, (IsLocalization.map_units (FractionRing O) b).mul_left_eq_zero] at hab
  exact Subtype.ext hab

theorem isReduced_curveLocalRing {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (h : IsRadicalAt I q) : IsReduced (curveLocalRing I q) := by
  refine (Ideal.isRadical_iff_quotient_reduced _).1 ?_
  rw [Ideal.IsRadical, ← IsLocalization.map_radical (RingHom.ker (eval q)).primeCompl]
  refine Ideal.map_le_iff_le_comap.2 fun f hf ↦ ?_
  obtain ⟨s, hs, hsf⟩ := h f hf
  have hu : IsUnit (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) s) :=
    IsLocalization.map_units _ (⟨s, fun h' ↦ hs (RingHom.mem_ker.1 h')⟩ : (RingHom.ker (eval q)).primeCompl)
  exact (Ideal.unit_mul_mem_iff_mem _ hu).1 (by rw [← map_mul]; exact Ideal.mem_map_of_mem _ hsf)

theorem curveLocalRing_eq_div {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (o : curveLocalRing I q) : ∃ f s, IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s) ∧
      o * algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s =
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by
  obtain ⟨z, rfl⟩ : ∃ z, Ideal.Quotient.mk
      (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))) z = o :=
    Ideal.Quotient.mk_surjective o
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval q)).primeCompl z
  refine ⟨f, s, isUnit_algebraMap_curveLocalRing I q s fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have e := congrArg (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval q))) f s)
  rw [map_mul] at e
  exact e

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegDensNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open scoped ComplexOrder

noncomputable section

namespace RegularizedDensityNonneg

theorem half_log_eq_phi (a : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    Real.log (‖a‖ ^ 2 + ε) / 2 = phi (![a, ((√ε : ℝ) : ℂ)] : Fin 2 → ℂ) := by
  simp only [phi, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε]
  ring

end RegularizedDensityNonneg

theorem RegDensNonneg.proof : RegDensNonneg.Statement := by
  intro n d J A u ε x s hε hs
  have han : AnalyticAt ℂ s (A *ᵥ x) := FormIntegralPositivity.analyticAt_sheet hs
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.cons_val_zero]
    set y := A *ᵥ x
    have hh : AnalyticAt ℂ (fun w => linEval u (s w)) y := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 han) j)
    let τ : (Fin (d + 1) → ℂ) → (Fin 2 → ℂ) := fun w => ![linEval u (s w), ((√ε : ℝ) : ℂ)]
    have hτ : AnalyticAt ℂ τ y := by
      refine analyticAt_pi_iff.2 fun i => ?_
      fin_cases i
      · simpa [τ] using hh
      · simpa [τ] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin (d + 1) → ℂ => ((√ε : ℝ) : ℂ)) y)
    have hS : sqSum (τ y) ≠ 0 := by
      have : sqSum (τ y) = ‖linEval u (s y)‖ ^ 2 + ε := by
        simp only [τ, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε.le]
      rw [this]
      positivity
    have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
    have hfun : logReg u ε ∘ s = phi ∘ τ := by
      funext w
      exact RegularizedDensityNonneg.half_log_eq_phi _ hε.le
    rw [hfun]
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  · simp only [Matrix.cons_val_succ]
    have hE : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s (A *ᵥ x)) :=
      ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have e : (euclPot : (Fin n → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
      funext w; simp [euclPot, Complex.normSq_eq_norm_sq]
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ _ _ han hE, e, ReciprocityTheory.AnForm.A.hessC_sum_normSq]
    exact GradDensSheetBound.posSemidef_transpose_mul_mul_conj _ PosSemidef.one

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurveRegularPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalCurveRegularPoint

theorem fderiv_eval_single {σ : Type} [Fintype σ] [DecidableEq σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) (i : σ) :
    fderiv ℂ (fun x : σ → ℂ => eval x g) z (Pi.single i 1) = eval z (pderiv i g) := by
  induction g using MvPolynomial.induction_on generalizing z with
  | C a => simp
  | add p q hp hq =>
    have hp' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p z trivial).differentiableAt
    have hq' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) q z trivial).differentiableAt
    simp only [map_add (f := _)]
    rw [fderiv_fun_add hp' hq']
    simp [hp, hq]
  | mul_X p j hp =>
    have hp' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p z trivial).differentiableAt
    have hX : DifferentiableAt ℂ (fun x : σ → ℂ => x j) z := differentiableAt_apply j z
    simp only [eval_mul, eval_X]
    rw [fderiv_fun_mul hp' hX]
    simp [hp, Derivation.leibniz, pderiv_X, Pi.single_apply, fderiv_apply, mul_comm]
    split_ifs <;> simp

end NormalCurveRegularPoint

theorem NormalCurveRegularPoint.proof (hJ : NormalCurveJacobian.Statement) : NormalCurveRegularPoint.Statement := by
  classical
  intro σ _ I w hI hnorm hdim hw
  obtain ⟨k, f, D, hk, hfI, hlin, hD, hgen⟩ := hJ σ I w hI hnorm hdim hw
  set W : Set (σ → ℂ) := {z | eval z D ≠ 0}
  have hWo : IsOpen W := isOpen_ne_fun (continuous_eval D) continuous_const
  have hder : ∀ j, (fun i : σ => fderiv ℂ (fun z : σ → ℂ => eval z (f j)) w (Pi.single i 1)) =
      fun i => eval w (pderiv i (f j)) := fun j => funext fun i =>
    NormalCurveRegularPoint.fderiv_eval_single (f j) w i
  let Φ : ((σ → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (σ → ℂ) :=
    { toFun := fun L i => L (Pi.single i 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hlin' : LinearIndependent ℂ (fun j => fderiv ℂ (fun z : σ → ℂ => eval z (f j)) w) := by
    refine LinearIndependent.of_comp Φ ?_
    convert hlin using 1
    funext j
    exact hder j
  obtain ⟨d, A, O, V, g, hd, hO, hV, hwV, hVW, hg, hAg, hset⟩ :=
    IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.proof σ (Fin k) (fun j z => eval z (f j)) w W
      (fun j => AnalyticOnNhd.eval_mvPolynomial (f j) w trivial) (fun j => hw _ (hfI j)) hlin'
      (hWo.mem_nhds hD)
  simp only [Fintype.card_fin] at hd
  obtain rfl : d = 1 := by omega
  refine ⟨A, O, V, g, hO, hV, hwV, hg, hAg, ?_⟩
  rw [← hset]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, hzV⟩
    exact ⟨hzV, fun j => hz _ (hfI j)⟩
  · rintro ⟨hzV, hzf⟩
    refine ⟨fun q hq => ?_, hzV⟩
    have hspan : Ideal.span (Set.range f) ≤ RingHom.ker (eval z) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hzf j
    have h0 : eval z (D * q) = 0 := hspan (hgen q hq)
    rw [eval_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hVW hzV)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionInjectiveOffHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem ProjectionInjectiveOffHypersurface.proof (hF : FrameJacobianGeneric.Statement) :
    ProjectionInjectiveOffHypersurface.Statement := by
  classical
  intro σ _ I k hI hk
  set n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let φ : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ := renameEquiv ℂ e
  let J : Ideal (MvPolynomial (Fin n) ℂ) := I.map φ
  have hJ : J.IsPrime := Ideal.map_isPrime_of_equiv φ
  have hJk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) := by
    rw [← hk]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv I J φ rfl).symm)
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, -, hcard, hfJ, -, hdet, -⟩ := hF n k J hJ hJk b

  let T : (σ → ℂ) → EuclideanSpace ℂ (Fin n) := fun x => WithLp.toLp 2 (x ∘ e.symm)
  have hT : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ),
      eval (fun i => T x i) p = eval x (φ.symm p) := by
    intro x p
    have : φ.symm p = rename e.symm p := rfl
    rw [this, eval_rename]
  have hTinj : Function.Injective T := by
    intro x y hxy
    funext s
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v (e s)) hxy
    simpa [T] using this
  have hTc : Continuous T :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply _)
  refine ⟨φ.symm (frameJacobianDet b I₀ f), ?_, ?_⟩
  · intro hmem
    apply hdet
    exact (Ideal.mem_map_of_equiv φ _).2 ⟨_, hmem, by simp⟩
  intro z hz hzh
  have hf0 : ∀ x ∈ zeroSetIn I, ∀ j, eval (fun i => T x i) (f j) = 0 := by
    intro x hx j
    obtain ⟨q, hq, hqf⟩ := (Ideal.mem_map_of_equiv φ (f j)).1 (hfJ j)
    rw [hT, ← hqf, AlgEquiv.symm_apply_apply]
    exact hx q hq
  have hz' : eval (fun i => T z i) (frameJacobianDet b I₀ f) ≠ 0 := by rwa [hT]
  obtain ⟨Ω, V, g, -, hV, hzV, -, -, hpg, hgraph⟩ :=
    FrameImplicitGraph.proof n b I₀ f (T z) (hf0 z hz) hz' Set.univ isOpen_univ (Set.mem_univ _)
  let c : Fin k ≃ I₀ := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let A : (σ → ℂ) →L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm (c j : Fin n))
  refine ⟨T ⁻¹' V, hV.preimage hTc, hzV, A, ?_⟩

  have hback : ∀ x ∈ zeroSetIn I ∩ T ⁻¹' V, g (Heights.frameProj b I₀ (T x)) = T x := by
    rintro x ⟨hx, hxV⟩
    have hmem : T x ∈ {y : EuclideanSpace ℂ (Fin n) | ∀ j, eval (fun i => y i) (f j) = 0} ∩ V :=
      ⟨hf0 x hx, hxV⟩
    rw [hgraph] at hmem
    obtain ⟨w, hw, hwx⟩ := hmem
    rw [← hwx, hpg w hw]
  intro x hx y hy hAxy
  apply hTinj
  have hproj : Heights.frameProj b I₀ (T x) = Heights.frameProj b I₀ (T y) := by
    funext i
    have := congrFun hAxy (c.symm i)
    show inner ℂ (b i) (T x) = inner ℂ (b i) (T y)
    rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner]
    simpa [A, T] using this
  rw [← hback x hx, ← hback y hy, hproj]

theorem ProjectionInjectiveOffHypersurface.proof_of_rank (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : ProjectionInjectiveOffHypersurface.Statement :=
  ProjectionInjectiveOffHypersurface.proof (FrameJacobianGeneric.proof hR hC)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUniformiserGradientIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem UniformiserGradientIndependent.proof (hjac : NormalCurveJacobian.Statement)
    (hdvr : NormalCurvePointDVR.Statement) : UniformiserGradientIndependent.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, -, hk, hfI, hli, -, -⟩ := hjac σ I w hI hic hdim hw
  obtain ⟨_, _⟩ := hdvr σ I w hI hic hdim hw
  refine ⟨k, f, hk, hfI, hli.finCons fun hmem ↦ ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  set φ := algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) with hφ
  have hfw : ∀ j, eval w (f j) = 0 := fun j ↦ hw (f j) (hfI j)
  have htw : eval w t = 0 := by
    by_contra h
    exact ht.not_isUnit (isUnit_algebraMap_pointLocalRing I w t h)
  set p := t - ∑ j, C (c j) * f j with hp
  have hpm : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) := by
    simp [hp, RingHom.mem_ker, htw, hfw]
  have hpg : GradientAtPoint.grad w p = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hp, map_sub, map_sum]
    simp_rw [GradientAtPoint.grad_mul_of_eval_eq_zero w _ _ (hfw _), eval_C]
    have hg : ∀ q, GradientAtPoint.grad w q = fun i ↦ eval w (pderiv i q) :=
      fun q ↦ funext (GradientAtPoint.grad_apply w q)
    simp_rw [hg]
    exact sub_eq_zero.2 hc.symm
  have hp2 := GradientAtPoint.mem_sq_of_grad_eq_zero w hpm hpg
  have hφf : ∀ j, φ (f j) = 0 := fun j ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ (hfI j))
  have hφt : φ t = φ p := by simp [hp, hφf]
  have hmax : Ideal.map φ (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ≤
      IsLocalRing.maximalIdeal (pointLocalRing I w) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu ↦ pointLocalRing_eval_ne_zero_of_isUnit I w hw g hu (RingHom.mem_ker.1 hg)
  have ht2 : φ t ∈ IsLocalRing.maximalIdeal (pointLocalRing I w) ^ 2 := by
    rw [hφt]
    exact Ideal.pow_right_mono hmax 2 (Ideal.map_pow φ _ 2 ▸ Ideal.mem_map_of_mem φ hp2)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 ht, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at ht2
  obtain ⟨a, ha⟩ := ht2
  have h1 : φ t * (a * φ t) = φ t * 1 := by rw [mul_one]; nth_rewrite 3 [← ha]; ring
  exact ht.not_isUnit
    (IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact mul_left_cancel₀ ht.ne_zero h1))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PJacobianRankOffHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem JacobianRankOffHypersurface.eval_pderiv_sum_mul {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (c g : ι → MvPolynomial σ ℂ) (hg : ∀ k, eval w (g k) = 0) (x : σ) :
    eval w (pderiv x (∑ k, c k * g k)) = ∑ k, eval w (c k) * eval w (pderiv x (g k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Derivation.leibniz, smul_eq_mul, hg]

theorem JacobianRankOffHypersurface.grad_mem_span {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (a p : MvPolynomial σ ℂ) (c g : ι → MvPolynomial σ ℂ) (hsum : ∑ k, c k * g k = a * p)
    (hg : ∀ k, eval w (g k) = 0) (hp : eval w p = 0) (ha : eval w a ≠ 0) :
    (fun x ↦ eval w (pderiv x p)) ∈
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (g k))) := by
  have key : (fun x ↦ eval w (pderiv x p)) =
      (eval w a)⁻¹ • ∑ k, eval w (c k) • (fun x ↦ eval w (pderiv x (g k))) := by
    funext x
    have h1 := congrArg (fun f ↦ eval w (pderiv x f)) hsum
    simp only [JacobianRankOffHypersurface.eval_pderiv_sum_mul w c g hg x, Derivation.leibniz, smul_eq_mul,
      map_add, map_mul, hp, zero_mul, add_zero] at h1
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1]
    rw [inv_mul_cancel_left₀ ha]
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem JacobianRankOffHypersurface.finrank_of_generators {σ ι : Type*} [Fintype σ] [Fintype ι]
    (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ) (t : MvPolynomial σ ℂ)
    (hqQ : ∀ j, q j ∈ Q) (hgen : ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q))
    (f : ι → MvPolynomial σ ℂ) (s δ : MvPolynomial σ ℂ) (hfQ : ∀ k, f k ∈ Q)
    (hs : ∀ p ∈ Q, s * p ∈ Ideal.span (Set.range f))
    (hδ : ∀ w : σ → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k x ↦ eval w (pderiv x (f k)))
    (hcard : Fintype.card ι + d = Fintype.card σ) (w : σ → ℂ) (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q)
    (hμ : eval w (s * t * δ) ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j)))) + d =
      Fintype.card σ := by
  have hw' : ∀ p ∈ Q, eval w p = 0 := hw
  simp only [map_mul, mul_ne_zero_iff] at hμ
  obtain ⟨⟨hs0, ht0⟩, hδ0⟩ := hμ
  have heq : Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j))) =
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (f k))) := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro j
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs (q j) (hqQ j))
      exact JacobianRankOffHypersurface.grad_mem_span w s (q j) c f hc (fun k ↦ hw' _ (hfQ k))
        (hw' _ (hqQ j)) hs0
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro k
      obtain ⟨i, hi⟩ := hgen (f k) (hfQ k)
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hi
      refine JacobianRankOffHypersurface.grad_mem_span w (t ^ i) (f k) c q hc (fun j ↦ hw' _ (hqQ j))
        (hw' _ (hfQ k)) ?_
      rw [map_pow]
      exact pow_ne_zero _ ht0
  rw [heq, finrank_span_eq_card (hδ w hδ0)]
  exact hcard

theorem JacobianRankOffHypersurface.exists_fin (hF : FrameJacobianGeneric.Statement) {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) :
    ∃ (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s δ : MvPolynomial (Fin n) ℂ),
      Fintype.card {j // j ∉ I₀} + d = n ∧ (∀ k, f k ∈ J) ∧ s ∉ J ∧ δ ∉ J ∧
        (∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)) ∧
        ∀ w : Fin n → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k l ↦ eval w (pderiv l (f k)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, s, hcard, hfJ, hsJ, hδJ, hgen⟩ := hF n d J hJ hd b
  refine ⟨I₀, f, s, frameJacobianDet b I₀ f, ?_, hfJ, hsJ, hδJ, hgen, ?_⟩
  · have h1 : Fintype.card {j // j ∉ I₀} = n - I₀.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    have h2 : I₀.card ≤ n := (Finset.card_le_univ I₀).trans_eq (Fintype.card_fin n)
    omega
  · intro w hw
    let M : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun j l ↦ b j l
    have hdet := hw
    rw [frameJacobianDet, RingHom.map_det] at hdet
    have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
    have hrows : (fun k ↦ ((eval w).mapMatrix (Matrix.of fun k j : {j // j ∉ I₀} ↦ frameDeriv b j (f k))) k) =
        (Matrix.mulVecLin M) ∘ fun k l ↦ eval w (pderiv l (f k)) := by
      funext k j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [frameDeriv, M, Matrix.mulVec, dotProduct, map_sum]
    change LinearIndependent ℂ (fun k ↦ ((eval w).mapMatrix
      (Matrix.of fun k j : {j // j ∉ I₀} ↦ frameDeriv b j (f k))) k) at hli
    rw [hrows] at hli
    exact hli.of_comp _

theorem JacobianRankOffHypersurface.proof_of_frame (hF : FrameJacobianGeneric.Statement) :
    JacobianRankOffHypersurface.Statement := by
  intro σ _ Q d r q t hQ hd hqQ htQ hgen
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := Q.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ), eval x (φ p) = eval (x ∘ e.symm) p := fun x p ↦ by
    simp [φ, eval_rename]
  have hJd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    rw [← hd]
    refine (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv Q J φ.toRingEquiv.symm ?_)).symm
    exact (Ideal.map_symm (I := Q) φ.toRingEquiv).symm
  obtain ⟨I₀, f, s, δ, hcard, hfJ, hsJ, hδJ, hsgen, hlin⟩ :=
    JacobianRankOffHypersurface.exists_fin hF J hJ hJd
  have hfQ : ∀ k, φ (f k) ∈ Q := fun k ↦ Ideal.mem_comap.mp (hfJ k)
  have hsQ : φ s ∉ Q := fun h ↦ hsJ (Ideal.mem_comap.mpr h)
  have hδQ : φ δ ∉ Q := fun h ↦ hδJ (Ideal.mem_comap.mpr h)
  have hs : ∀ p ∈ Q, φ s * p ∈ Ideal.span (Set.range fun k ↦ φ (f k)) := by
    intro p hp
    have hp' : φ.symm p ∈ J := Ideal.mem_comap.mpr (by rwa [AlgEquiv.apply_symm_apply])
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hsgen _ hp')
    refine Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun k ↦ φ (c k), ?_⟩
    have := congrArg φ hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_mul, AlgEquiv.apply_symm_apply] at this
    simpa [map_mul] using this
  have hδ : ∀ w : σ → ℂ, eval w (φ δ) ≠ 0 →
      LinearIndependent ℂ fun k x ↦ eval w (pderiv x (φ (f k))) := by
    intro w hw
    rw [hφ] at hw
    have hL := (hlin _ hw).map' (LinearMap.funLeft ℂ ℂ e)
      (LinearMap.ker_eq_bot.mpr (LinearMap.funLeft_injective_of_surjective _ _ _ e.surjective))
    have hfam : (fun k x ↦ eval w (pderiv x (φ (f k)))) =
        (LinearMap.funLeft ℂ ℂ e) ∘ fun k l ↦ eval (w ∘ e.symm) (pderiv l (f k)) := by
      funext k x
      simp only [Function.comp_apply, LinearMap.funLeft_apply]
      have hx : pderiv x (φ (f k)) = φ (pderiv (e x) (f k)) := by
        have := pderiv_rename (R := ℂ) e.symm.injective (e x) (f k)
        rw [Equiv.symm_apply_apply] at this
        exact this
      rw [hx, hφ]
    rw [hfam]
    exact hL
  have hμQ : φ s * t * φ δ ∉ Q := by
    intro h
    rcases hQ.mem_or_mem h with h | h
    · rcases hQ.mem_or_mem h with h | h
      · exact hsQ h
      · exact htQ h
    · exact hδQ h
  exact ⟨φ s * t * φ δ, hμQ, fun w hw hμ ↦
    JacobianRankOffHypersurface.finrank_of_generators Q d r q t hqQ hgen (fun k ↦ φ (f k)) (φ s) (φ δ) hfQ hs hδ
      hcard w hw hμ⟩

theorem JacobianRankOffHypersurface.proof : JacobianRankOffHypersurface.Statement :=
  JacobianRankOffHypersurface.proof_of_frame
    (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)

end

end GroundTheory.Heights₂.Heights
end
