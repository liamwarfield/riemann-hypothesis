module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.IndNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.CoreInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FinsumSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.OneSideX
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.KillExempt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ExistsPositivePeriodLine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceSm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.ProjInner
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.IndAutCs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CyclicLiftRankTwoOfCyclicBaseChange

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IndCsOfBcfl
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.Cix
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.KillEx2
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.killEx2 :
    KillEx2 := by
  intro F E _ _ _ _ _ _ _ n SE SF hS B B' _ _ b b' hb hb' L t hc h h'
  exact UpperTheory.ConvolutionTheory.Ci.killEx_listed UpperTheory.ConvolutionTheory.Dp.parEx F E n SE SF hS B B' b b' hb hb' L t hc h h'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.TruncCpt
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.truncCpt :
    ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => TruncCpt μ A A' := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' a P Λ T ha hD hP hT hΛ
  obtain ⟨kk, -, -, -, -, h⟩ := truncKer K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP ha hD
  exact (h T Λ hT hΛ).2.2.1.isCompactOperator
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FamEx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ScatOnSpan
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq PositivityTheory.Rg.Tf.Adel ContinuousLinearMap
open scoped InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem tc_two {A : H →L[ℂ] K} {B : K →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsTraceClass (A ∘L B) := by
  obtain ⟨V, -, -, hV⟩ := exists_polar (A ∘L B)
  let b := stdHilbertBasis ℂ K
  have h1 : IsHilbertSchmidt (adjoint A ∘L V) := hA.adjoint.comp_right V
  refine (traceNorm_le_of_adjoint_comp b hV).trans_lt ?_
  have h2 : ∑' i, ‖⟪V (b i), (A ∘L B) (b i)⟫_ℂ‖ₑ ≤ ∑' i, (‖(adjoint A ∘L V) (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [comp_apply, ← adjoint_inner_left, comp_apply]
    exact (enorm_inner_le _ _).trans (ennreal_mul_le_sq_add_sq _ _)
  refine h2.trans_lt ?_
  rw [ENNReal.tsum_add, ← hsNormSq_eq_tsum b, ← hsNormSq_eq_tsum b]
  exact ENNReal.add_lt_top.2 ⟨h1, hB⟩

private theorem tr_compress (ι : K →L[ℂ] H) (π : H →L[ℂ] K) {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (hP : (ι ∘L π) ∘L T = T) : IsTraceClass (π ∘L T ∘L ι) ∧ trace (π ∘L T ∘L ι) = trace T := by
  obtain ⟨S, R, hS, hR, rfl⟩ := hT.exists_comp
  have hA : IsHilbertSchmidt (π ∘L S) := hS.comp_left π
  have hB : IsHilbertSchmidt (R ∘L ι) := hR.comp_right ι
  have e : π ∘L (S ∘L R) ∘L ι = (π ∘L S) ∘L (R ∘L ι) := by ext1 x; rfl
  rw [e]
  refine ⟨tc_two hA hB, ?_⟩
  have h1 : trace ((π ∘L S) ∘L (R ∘L ι)) = trace ((R ∘L ι) ∘L (π ∘L S)) :=
     (hasSum_inner_comp_comm (stdHilbertBasis ℂ K) (stdHilbertBasis ℂ H) hA hB).tsum_eq
  have h2 : trace (R ∘L ((ι ∘L π) ∘L S)) = trace (((ι ∘L π) ∘L S) ∘L R) :=
    trace_comp_comm_of_isHilbertSchmidt hR (hS.comp_left _)
  have h4 : (R ∘L ι) ∘L (π ∘L S) = R ∘L ((ι ∘L π) ∘L S) := by ext1 x; rfl
  rw [h1, h4, h2, comp_assoc, hP]

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

private theorem sa_of {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →L[ℂ] E}
    (h : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) : IsSelfAdjoint A :=
  isSelfAdjoint_iff_isSymmetric.2 h

private theorem sa_to {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →L[ℂ] E}
    (h : IsSelfAdjoint A) (x y : E) : ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ :=
  isSelfAdjoint_iff_isSymmetric.1 h x y

private theorem core (hM : Main) (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (ι : K →L[ℂ] H) (π : H →L[ℂ] K)
    (J₀ : L V →ₗᵢ[ℂ] K) (J₀' : L W →ₗᵢ[ℂ] K) (hJ : ∀ u, ι (J₀ u) = J u) (hJ' : ∀ u, ι (J₀' u) = J' u)
    (hπι : ∀ x, π (ι x) = x) (hadj : ∀ x h, ⟪ι x, h⟫_ℂ = ⟪x, π h⟫_ℂ)
    (hspan : ∀ h, (∀ u, ⟪J u, h⟫_ℂ = 0) → (∀ v, ⟪J' v, h⟫_ℂ = 0) → π h = 0)
    (shift : ∀ (t : ℝ) (u u' : L V) (v v' : L W), (∀ᵐ x : ℝ, u' x = u (x + t)) → (∀ᵐ x : ℝ, v' x = v (x + t)) →
      ⟪J u', J' v⟫_ℂ = ⟪J u, J' v'⟫_ℂ)
    (causal : ∀ (s : ℝ) (u : L V) (v : L W), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → (∀ᵐ x : ℝ, x ≤ 2 * 0 - s → v x = 0) →
      ⟪J u, J' v⟫_ℂ = 0)
    (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W) (hβ : Ker β) (hβ' : Ker β') (hu : IsUnit (symb β 0))
    (hu' : IsUnit (symb β' 0)) (hB : IsSelfAdjoint B) (hBJ : Conv J J B β) (hBJ' : Conv J' J' B β')
    (hc : ∀ (T : ℝ) (Λ : H →L[ℂ] H), 0 ≤ T → IsTrunc J J' T Λ → IsCompactOperator (Λ ∘L B ∘L (ι ∘L π))) :
    ∃ N : W ≃ₗᵢ[ℂ] V,
      (∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → Conv J J Y β → Conv J' J' Y β' →
        ∀ w, N (symb β' 0 w) = symb β 0 (N w)) ∧
      ∀ (X Λ : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W) (T C : ℝ), Ker κ → Conv J J' X κ → X ∘L (ι ∘L π) = (ι ∘L π) ∘L X → 0 ≤ T →
        IsTrunc J J' T Λ → IsTraceClass (Λ ∘L X ∘L (ι ∘L π) ∘L Λ) →
        (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ C / (1 + |z.im|)) →
        ‖trace (Λ ∘L X ∘L (ι ∘L π) ∘L Λ) -
            (1 / 2 : ℂ) * LinearMap.trace ℂ V ((N.toLinearEquiv : W →ₗ[ℂ] V) ∘ₗ (symb κ 0 : V →ₗ[ℂ] W))‖ ≤
          Module.finrank ℂ V * C * Real.exp (-2 * T) := by
  have hadj' : ∀ x h, ⟪h, ι x⟫_ℂ = ⟪π h, x⟫_ℂ := fun x h => by
    rw [← inner_conj_symm, hadj, inner_conj_symm]
  have hii : ∀ x y, ⟪ι x, ι y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => by rw [hadj, hπι]
  have hπJ : ∀ u, π (J u) = J₀ u := fun u => by rw [← hJ, hπι]
  have hπJ' : ∀ u, π (J' u) = J₀' u := fun u => by rw [← hJ', hπι]
  have hin : ∀ u v, ⟪J₀ u, J₀' v⟫_ℂ = ⟪J u, J' v⟫_ℂ := fun u v => by rw [← hii, hJ, hJ']
  let D : Datum K V W :=
    { J := J₀
      J' := J₀'
      T₀ := 0
      B := π ∘L B ∘L ι
      β := β
      β' := β'
      span := fun h h1 h2 => by
        rw [← hπι h]
        refine hspan _ (fun u => ?_) fun u => ?_
        · rw [← hJ, hii, h1]
        · rw [← hJ', hii, h2]
      shift := fun t u u' v v' h1 h2 => by rw [hin, hin]; exact shift t u u' v v' h1 h2
      causal := fun s u v h1 h2 => by rw [hin]; exact causal s u v h1 h2
      β_ker := hβ
      β'_ker := hβ'
      β_unit := hu
      β'_unit := hu'
      B_sa := sa_of fun x y => by
        simp only [comp_apply]
        rw [← hadj', ← hadj, sa_to hB]
      B_J := fun u v h => by simp only [comp_apply]; rw [hJ, hBJ u v h, hπJ]
      B_J' := fun u v h => by simp only [comp_apply]; rw [hJ', hBJ' u v h, hπJ']
      compact := fun T Λ hT hΛ => by
        obtain ⟨s1, s2, s3⟩ := hΛ
        have s2' : ∀ x, Λ (Λ x) = Λ x := fun x => congrArg (fun A : K →L[ℂ] K => A x) s2
        have ht : IsTrunc J J' T (ι ∘L Λ ∘L π + (1 - ι ∘L π)) := by
          refine ⟨sa_of fun x y => ?_, ?_, fun h => ?_⟩
          · simp only [add_apply, sub_apply, comp_apply, one_apply_eq_self, inner_add_left, inner_add_right, inner_sub_left,
              inner_sub_right, hadj, hadj', sa_to s1]
          · ext x
            simp [hπι, s2']
          · simp only [add_apply, sub_apply, comp_apply, one_apply_eq_self]
            constructor
            · intro h0
              have h1 : Λ (π h) = 0 := by simpa [hπι] using congrArg π h0
              have h2 : h = ι (π h) := by simpa [h1, sub_eq_zero] using h0
              obtain ⟨u, v, a1, a2, a3⟩ := (s3 _).1 h1
              exact ⟨u, v, a1, a2, by rw [h2, a3, map_add (f := _), hJ, hJ']⟩
            · rintro ⟨u, v, a1, a2, rfl⟩
              have h1 := (s3 _).2 ⟨u, v, a1, a2, rfl⟩
              rw [map_add π, hπJ, hπJ', h1, map_add ι, hJ, hJ']
              simp
        have hk := ((hc T _ hT ht).comp_clm (ι ∘L Λ)).clm_comp π
        have e : ⇑(Λ ∘L (π ∘L B ∘L ι) ∘L Λ) =
            ⇑π ∘ ⇑((ι ∘L Λ ∘L π + (1 - ι ∘L π)) ∘L B ∘L ι ∘L π) ∘ ⇑(ι ∘L Λ) := by
          funext x
          simp [hπι]
        rw [e]
        exact hk }
  obtain ⟨N, hN1, hN2⟩ := hM K V W D
  refine ⟨N, fun Y b b' k k' c c' => hN1 (π ∘L Y ∘L ι) b b' k k' (fun u v h => ?_) fun u v h => ?_, ?_⟩
  · change π (Y (ι (J₀ u))) = J₀ v
    rw [hJ, c u v h, hπJ]
  · change π (Y (ι (J₀' u))) = J₀' v
    rw [hJ', c' u v h, hπJ']
  intro X Λ κ T C hκ hX hXP hT hΛ htc hb
  obtain ⟨s1, s2, s3⟩ := hΛ
  have s2' : ∀ x, Λ (Λ x) = Λ x := fun x => congrArg (fun A : H →L[ℂ] H => A x) s2
  have hXP' : ∀ x, X (ι (π x)) = ι (π (X x)) := fun x => congrArg (fun A : H →L[ℂ] H => A x) hXP
  have e1 : ∀ x, ι (π (x - Λ x)) = x - Λ x := fun x => by
    obtain ⟨u, v, -, -, a⟩ := (s3 (x - Λ x)).1 (by simp [s2'])
    rw [a, map_add (f := _), map_add (f := _), hπJ, hπJ', hJ, hJ']
  have e2 : ∀ x, Λ (ι (π x)) = ι (π (Λ x)) := fun x => by
    have a : ι (π x) - Λ (ι (π x)) = x - Λ x := by
      refine ext_inner_left ℂ fun y => ?_
      have b : ∀ z, ⟪y, z - Λ z⟫_ℂ = ⟪y - Λ y, z⟫_ℂ := fun z => by rw [inner_sub_left, inner_sub_right, sa_to s1]
      rw [b, b, hadj', ← hadj', ← e1 y, hadj, hadj, hπι]
    have a' := e1 x
    rw [map_sub, map_sub, ← a] at a'
    exact (sub_right_injective a').symm
  have e3 : ∀ x, ι (π (Λ (ι x))) = Λ (ι x) := fun x => by rw [← e2, hπι]
  have ht : IsTrunc J₀ J₀' T (π ∘L Λ ∘L ι) := by
    refine ⟨sa_of fun x y => ?_, ?_, fun h => ?_⟩
    · simp only [comp_apply]
      rw [← hadj', ← hadj, sa_to s1]
    · ext1 x
      simp only [comp_apply, e3, s2']
    · simp only [comp_apply]
      constructor
      · intro h0
        have h1 : Λ (ι h) = 0 := by rw [← e3, h0, map_zero]
        obtain ⟨u, v, a1, a2, a3⟩ := (s3 _).1 h1
        exact ⟨u, v, a1, a2, by rw [← hπι h, a3, map_add (f := _), hπJ, hπJ']⟩
      · rintro ⟨u, v, a1, a2, rfl⟩
        rw [map_add ι, hJ, hJ', (s3 _).2 ⟨u, v, a1, a2, rfl⟩, map_zero]
  obtain ⟨t1, t2⟩ := tr_compress ι π htc (by
    ext1 x
    simp only [comp_apply]
    rw [← e2, ← hXP', hπι])
  have e4 : (π ∘L Λ ∘L ι) ∘L (π ∘L X ∘L ι) ∘L (π ∘L Λ ∘L ι) = π ∘L (Λ ∘L X ∘L (ι ∘L π) ∘L Λ) ∘L ι := by
    ext1 x
    simp only [comp_apply]
    rw [← hXP', hπι]
  have := hN2 (π ∘L X ∘L ι) (π ∘L Λ ∘L ι) κ T C hκ (fun u v h => by
    change π (X (ι (J₀ u))) = J₀' v
    rw [hJ, hX u v h, hπJ']) hT ht (e4 ▸ t1) hb
  rw [e4, t2] at this
  simpa [D] using this

theorem scat_on_span (hM : Main) (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P : H →L[ℂ] H) (hP : IsOrthogonalProjectionTwoLines J J' P)
    (shift : ∀ (t : ℝ) (u u' : L V) (v v' : L W), (∀ᵐ x : ℝ, u' x = u (x + t)) → (∀ᵐ x : ℝ, v' x = v (x + t)) →
      ⟪J u', J' v⟫_ℂ = ⟪J u, J' v'⟫_ℂ)
    (causal : ∀ (s : ℝ) (u : L V) (v : L W), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → (∀ᵐ x : ℝ, x ≤ 2 * 0 - s → v x = 0) →
      ⟪J u, J' v⟫_ℂ = 0)
    (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W) (hβ : Ker β) (hβ' : Ker β') (hu : IsUnit (symb β 0))
    (hu' : IsUnit (symb β' 0)) (hB : IsSelfAdjoint B) (hBJ : Conv J J B β) (hBJ' : Conv J' J' B β')
    (hc : ∀ (T : ℝ) (Λ : H →L[ℂ] H), 0 ≤ T → IsTrunc J J' T Λ → IsCompactOperator (Λ ∘L B ∘L P)) :
    ∃ N : W ≃ₗᵢ[ℂ] V,
      (∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → Conv J J Y β → Conv J' J' Y β' →
        ∀ w, N (symb β' 0 w) = symb β 0 (N w)) ∧
      ∀ (X Λ : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W) (T C : ℝ), Ker κ → Conv J J' X κ → X ∘L P = P ∘L X → 0 ≤ T →
        IsTrunc J J' T Λ → IsTraceClass (Λ ∘L X ∘L P ∘L Λ) →
        (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ C / (1 + |z.im|)) →
        ‖trace (Λ ∘L X ∘L P ∘L Λ) -
            (1 / 2 : ℂ) * LinearMap.trace ℂ V ((N.toLinearEquiv : W →ₗ[ℂ] V) ∘ₗ (symb κ 0 : V →ₗ[ℂ] W))‖ ≤
          Module.finrank ℂ V * C * Real.exp (-2 * T) := by
  obtain ⟨p1, p2, p3⟩ := hP
  have p2' : ∀ x, P (P x) = P x := fun x => congrArg (fun A : H →L[ℂ] H => A x) p2
  let S : Submodule ℂ H := (1 - P : H →L[ℂ] H).ker
  have hS : ∀ x, x ∈ S ↔ P x = x := fun x => by
    simp only [S, LinearMap.mem_ker, coe_coe, sub_apply, one_apply_eq_self, sub_eq_zero]
    exact eq_comm
  haveI : CompleteSpace S := (1 - P : H →L[ℂ] H).isClosed_ker.completeSpace_coe
  have fix : ∀ x, (∀ h, P h = 0 → ⟪x, h⟫_ℂ = 0) → x ∈ S := fun x hx => by
    refine (hS x).2 (ext_inner_right ℂ fun y => ?_)
    have := hx (y - P y) (by simp [p2'])
    rw [inner_sub_right, sub_eq_zero] at this
    rw [sa_to p1, this]
  have m1 : ∀ u, J u ∈ S := fun u => fix _ fun h hh => ((p3 h).1 hh).1 u
  have m2 : ∀ u, J' u ∈ S := fun u => fix _ fun h hh => ((p3 h).1 hh).2 u
  let π : H →L[ℂ] S := P.codRestrict S fun x => (hS _).2 (p2' x)
  have e : S.subtypeL ∘L π = P := by ext1 x; rfl
  have := core hM J J' S.subtypeL π ⟨J.toLinearMap.codRestrict S m1, fun u => J.norm_map u⟩
    ⟨J'.toLinearMap.codRestrict S m2, fun u => J'.norm_map u⟩ (fun _ => rfl) (fun _ => rfl)
    (fun x => Subtype.ext ((hS _).1 x.2))
    (fun x h => by
      change ⟪(x : H), h⟫_ℂ = ⟪(x : H), P h⟫_ℂ
      rw [← sa_to p1, (hS _).1 x.2])
    (fun h h1 h2 => Subtype.ext ((p3 h).2 ⟨h1, h2⟩)) shift causal B β β' hβ hβ' hu hu' hB hBJ hBJ' (by rw [e]; exact hc)
  rwa [e] at this

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
end

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.famEx :
    (ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => TruncCpt μ A A') → UnitB → UnipotentBlockPairs → PositivityTheory.Rg.Tf.IntegralApplyAeEq.Main → FamEx := by
  intro hC hU hF hM K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' P hP
  obtain ⟨a, β, β', sm, hk, st, ⟨k, c, -⟩, ⟨k', c', -⟩, u, u'⟩ := hU K μ μ₂ τ₁ τ₂ hp D d d' A A'
  obtain ⟨sh, ca⟩ := hF K μ μ₂ τ₁ τ₂ hp D d d' A A'
  have sa : IsSelfAdjoint (Rop μ a) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', UpperTheory.ConvolutionTheory.K.ropAdj, st]
  obtain ⟨N, h1, h2⟩ := scat_on_span hM A.J A'.J P hP sh ca (Rop μ a) β β' k k' u u' sa c c'
    fun T Λ hT hΛ => hC K μ μ₂ τ₁ τ₂ hp D d d' A A' a P Λ T sm hk hP hT hΛ
  refine ⟨N, Module.finrank ℂ (Eu d), ⟨fun f b b' hb hb' => h1 _ b b' hb.1 hb'.1 hb.2.1 hb'.2.1, h2⟩, ?_⟩
  intro Y s s' hs hs' w
  obtain ⟨κ, m1, m2, m3⟩ := (actLaws A.J).2.2.2.2 _ Y β s k c hs
  obtain ⟨κ', n1, n2, n3⟩ := (actLaws A'.J).2.2.2.2 _ Y β' s' k' c' hs'
  have e := h1 _ κ κ' m1 n1 m2 n2 w
  rw [m3, n3, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1 _ β β' k k' c c'] at e
  obtain ⟨g, hg⟩ := u.exists_left_inv
  have inv : ∀ x, g (symb β 0 x) = x := fun x => congrArg (fun B : Eu d →L[ℂ] Eu d => B x) hg
  rw [← inv (N _), e, inv]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ImportsAlt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ImportsBis
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.OntoJ
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvDense
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.FourConv
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.fourConv :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → ∀ u : L V, ∀ᵐ ξ : ℝ,
      Lp.fourierTransformₗᵢ ℝ W (conv κ u) ξ = symb κ (2 * Real.pi * Complex.I * ξ) (Lp.fourierTransformₗᵢ ℝ V u ξ) := by
  intro V _ _ _ _ W _ _ _ _ κ hk u
  have ki : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
  let σ : ℝ → V →L[ℂ] W := fun ξ => symb κ (2 * Real.pi * Complex.I * ξ)
  have hσ : ∀ ξ, σ ξ = 𝓕 (fun t => κ (-t)) ξ := fun ξ => by
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [neg_neg]
    congr 2
    push_cast; ring
  have σc : Continuous σ := by
    rw [show σ = _ from funext hσ]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ ki.comp_neg
  have σb : ∀ ξ, ‖σ ξ‖ ≤ ∫ t, ‖κ (-t)‖ := fun ξ => by
    rw [hσ]; exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  set C := ∫ t, ‖κ (-t)‖
  have hm : ∀ v : L V, MemLp (fun ξ => σ ξ (v ξ)) 2 volume := fun v =>
    (Lp.memLp v).of_le_mul (c := C)
      ((ContinuousLinearMap.id ℂ (V →L[ℂ] W)).aestronglyMeasurable_comp₂ σc.aestronglyMeasurable (Lp.aestronglyMeasurable v))
      (Eventually.of_forall fun ξ => (σ ξ).le_of_opNorm_le (σb ξ) _)
  let T : L V → L W := fun v => (hm v).toLp _
  have Tc : Continuous T := by
    refine (LipschitzWith.of_dist_le' (K := C) fun v v' => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm]
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub (T v) (T v'), Lp.coeFn_sub v v', (hm v).coeFn_toLp, (hm v').coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, ← map_sub]
    exact (σ x).le_of_opNorm_le (σb x) _
  have key : Lp.fourierTransformₗᵢ ℝ W (conv κ u) = T (Lp.fourierTransformₗᵢ ℝ V u) := by
    refine DenseRange.induction_on (p := fun u : L V => Lp.fourierTransformₗᵢ ℝ W (conv κ u) = T (Lp.fourierTransformₗᵢ ℝ V u))
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := V) (p := 2) (μ := volume) ENNReal.ofNat_ne_top) u
      (isClosed_eq ((Lp.fourierTransformₗᵢ ℝ W).continuous.comp (conv κ).continuous)
        (Tc.comp (Lp.fourierTransformₗᵢ ℝ V).continuous)) fun f => ?_
    set w : L V := SchwartzMap.toLpCLM ℝ V 2 volume f
    have wi : Integrable (w : ℝ → V) := f.integrable.congr (f.coeFn_toLp 2 volume).symm
    have e : (conv κ w : ℝ → W) =ᵐ[volume] convolution (fun t => κ (-t)) w (ContinuousLinearMap.id ℂ (V →L[ℂ] W)) volume := by
      filter_upwards [(convSpec κ hk w).1] with x hx
      rw [hx, convolution_def, ← integral_neg_eq_self]
      simp [sub_eq_add_neg]
    have ci : Integrable (conv κ w : ℝ → W) := (ki.comp_neg.integrable_convolution _ wi).congr e.symm
    refine Lp.ext ?_
    filter_upwards [fourAe _ ci, fourAe _ wi, (hm (Lp.fourierTransformₗᵢ ℝ V w)).coeFn_toLp] with ξ h1 h2 h3
    rw [h1, h3, h2, Real.fourier_congr_ae e, Real.fourier_bilin_convolution_eq _ ki.comp_neg wi, hσ]
    rfl
  rw [key]
  exact (hm _).coeFn_toLp
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem symb_diff {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (κ : ℝ → V →L[ℂ] V) (hk : Ker κ) : Differentiable ℂ (symb κ) := fun z => by
  have c1 : ∀ w : ℂ, Continuous fun t : ℝ => Complex.exp (w * t) • κ t := fun w =>
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul hk.1
  have c2 : Continuous fun t : ℝ => (Complex.exp (z * t) * t) • κ t :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul Complex.continuous_ofReal).smul hk.1
  have c3 : Continuous fun t : ℝ => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖ := by
    have := hk.1
    fun_prop
  have s1 : HasCompactSupport fun t : ℝ => Complex.exp (z * t) • κ t := hk.2.mono fun t ht h => ht (by simp [h])
  have s3 : HasCompactSupport fun t : ℝ => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖ := hk.2.mono fun t ht h => ht (by simp [h])
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := fun (w : ℂ) (t : ℝ) => Complex.exp (w * t) • κ t)
    (F' := fun (w : ℂ) (t : ℝ) => (Complex.exp (w * t) * t) • κ t) (bound := fun t => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖)
    (Metric.ball_mem_nhds z one_pos) (Eventually.of_forall fun w => (c1 w).aestronglyMeasurable)
    ((c1 z).integrable_of_hasCompactSupport s1) c2.aestronglyMeasurable
    (Eventually.of_forall fun t w hw => ?_) (c3.integrable_of_hasCompactSupport s3)
    (Eventually.of_forall fun t w _ => ?_)).2.differentiableAt
  · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    have := norm_sub_norm_le w z
    rw [Metric.mem_ball, dist_eq_norm] at hw
    linarith
  · simpa using (((hasDerivAt_id w).mul_const (t : ℂ)).cexp).smul_const (κ t)

theorem UpperTheory.V.Z.IntegralApplyAeEq.convDense :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (β : ℝ → V →L[ℂ] V), Ker β → IsUnit (symb β 0) → DenseRange (conv β) := by
  intro V _ _ _ _ β hk hu
  obtain ⟨k1, k2, k3⟩ := convAdj β hk
  let D : ℂ → ℂ := fun z => LinearMap.det (symb (sharp β) z : V →ₗ[ℂ] V)
  have hD : Differentiable ℂ D := by
    let b := Module.finBasis ℂ V
    have e : D = fun z => ∑ s : Equiv.Perm (Fin (Module.finrank ℂ V)), ((Equiv.Perm.sign s : ℤ) : ℂ) *
        ∏ i, (b.coord (s i)).toContinuousLinearMap (symb (sharp β) z (b i)) := by
      funext z
      simp only [D]
      rw [← LinearMap.det_toMatrix b, Matrix.det_apply']
      simp [LinearMap.toMatrix_apply]
    rw [e]
    refine Differentiable.fun_sum fun s _ => (differentiable_const _).mul ?_
    intro z
    apply (Finset.analyticAt_fun_prod Finset.univ ?_).differentiableAt
    intro i _
    exact ((ContinuousLinearMap.differentiable _).comp ((symb_diff _ k1).clm_apply (differentiable_const _))).analyticAt z
  have h0 : D 0 ≠ 0 := by
    have : IsUnit (symb (sharp β) 0) := by
      rw [k3, map_zero, neg_zero]; exact hu.star
    exact ((LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2 (ContinuousLinearMap.isUnit_iff_bijective.1 this))).ne_zero
  let g : ℝ → ℂ := fun ξ => D (2 * Real.pi * Complex.I * ξ)
  have ga : AnalyticOnNhd ℝ g univ := fun ξ _ => by
    have h1 : AnalyticAt ℝ (fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ : ℂ)) ξ :=
      analyticAt_const.mul (Complex.ofRealCLM.analyticAt ξ)
    exact (hD.analyticAt _).restrictScalars.comp h1
  have gz : ∀ᵐ ξ : ℝ, g ξ ≠ 0 := by
    have h1 := ga.preimage_zero_mem_codiscreteWithin (x := 0) (by simpa [g] using h0) trivial isConnected_univ
    have h2 := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ h1
    rw [Measure.restrict_univ] at h2
    exact h2
  have inj : ∀ y : L V, conv (sharp β) y = 0 → y = 0 := fun y hy => by
    rw [← (Lp.fourierTransformₗᵢ ℝ V).map_eq_zero_iff]
    refine Lp.ext ?_
    have h1 := fourConv (sharp β) k1 y
    rw [hy, map_zero] at h1
    filter_upwards [h1, gz, Lp.coeFn_zero V 2 (volume : Measure ℝ)] with ξ a b c
    rw [c] at a ⊢
    have := ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit b))).1
    exact this (a₁ := _) (a₂ := 0) (a.symm.trans (map_zero _).symm)
  have bot : (LinearMap.range (conv β : L V →ₗ[ℂ] L V))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine inj y (ext_inner_left ℂ fun x => ?_)
    rw [← k2, ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    exact hy _ ⟨x, rfl⟩
  exact Submodule.dense_iff_topologicalClosure_eq_top.2 (Submodule.topologicalClosure_eq_top_iff.2 bot)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CptNull
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cptNull :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (l : Filter ι) (K : H →L[ℂ] H) (x : ι → H) (C : ℝ), IsCompactOperator K → (∀ i, ‖x i‖ ≤ C) →
      (∀ y, Tendsto (fun i => ⟪y, x i⟫_ℂ) l (𝓝 0)) → Tendsto (fun i => K (x i)) l (𝓝 0) := by
  intro H _ _ _ ι l K x C hK hb hw
  obtain ⟨S, hS, hsub⟩ := hK.image_closedBall_subset_compact C
  refine hS.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall fun i => hsub ⟨x i, by simpa using hb i, rfl⟩) ?_
  intro y _ hy
  have h1 : Tendsto (fun i => ⟪y, K (x i)⟫_ℂ) l (𝓝 0) := by
    simpa [ContinuousLinearMap.adjoint_inner_left] using hw (ContinuousLinearMap.adjoint K y)
  have h2 : MapClusterPt ⟪y, y⟫_ℂ l (fun i => ⟪y, K (x i)⟫_ℂ) :=
    hy.continuousAt_comp (f := fun z => ⟪y, z⟫_ℂ) (by fun_prop)
  have h3 : ⟪y, y⟫_ℂ = 0 := eq_of_nhds_neBot (h2.clusterPt.mono h1).neBot
  exact inner_self_eq_zero.1 h3
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.ontoJ :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (D : Datum H V W), Function.Surjective D.J := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ D
  set J := D.J.toContinuousLinearMap with hJ
  set J' := D.J'.toContinuousLinearMap with hJ'
  set A := ContinuousLinearMap.adjoint J with hA
  set A' := ContinuousLinearMap.adjoint J' with hA'
  have aJ : ∀ u, A (D.J u) = u := fun u => ext_inner_left ℂ fun y => by
    rw [hA, ContinuousLinearMap.adjoint_inner_right]; exact D.J.inner_map_map _ _
  have aJ' : ∀ u, A' (D.J' u) = u := fun u => ext_inner_left ℂ fun y => by
    rw [hA', ContinuousLinearMap.adjoint_inner_right]; exact D.J'.inner_map_map _ _
  have iA : ∀ u h, ⟪D.J u, h⟫_ℂ = ⟪u, A h⟫_ℂ := fun u h => (ContinuousLinearMap.adjoint_inner_right J u h).symm
  have iA' : ∀ u h, ⟪D.J' u, h⟫_ℂ = ⟪u, A' h⟫_ℂ := fun u h => (ContinuousLinearMap.adjoint_inner_right J' u h).symm
  have shf : ∀ t u v, ⟪D.J (sh V t u), D.J' v⟫_ℂ = ⟪D.J u, D.J' (sh W t v)⟫_ℂ := fun t u v =>
    D.shift t u _ v _ (sh_ae V _ u) (sh_ae W _ v)
  have adV : ∀ t (x y : L V), ⟪sh V t x, y⟫_ℂ = ⟪x, sh V (-t) y⟫_ℂ := fun t x y => by
    have := (avSpec (shF V)).1 t
    rw [← ContinuousLinearMap.adjoint_inner_right]; exact congrArg (fun Z : L V →L[ℂ] L V => ⟪x, Z y⟫_ℂ) this
  have adW : ∀ t (x y : L W), ⟪sh W t x, y⟫_ℂ = ⟪x, sh W (-t) y⟫_ℂ := fun t x y => by
    have := (avSpec (shF W)).1 t
    rw [← ContinuousLinearMap.adjoint_inner_right]; exact congrArg (fun Z : L W →L[ℂ] L W => ⟪x, Z y⟫_ℂ) this
  have S1 : ∀ t v, A (D.J' (sh W t v)) = sh V (-t) (A (D.J' v)) := fun t v => ext_inner_left ℂ fun y => by
    rw [← iA, ← shf, iA, adV]
  have S2 : ∀ t u, A' (D.J (sh V (-t) u)) = sh W t (A' (D.J u)) := fun t u => ext_inner_left ℂ fun y => by
    rw [← iA', ← inner_conj_symm, shf, inner_conj_symm, iA', adW, neg_neg]
  let Q : H →L[ℂ] H := 1 - J ∘L A
  have Qa : ∀ h, Q h = h - D.J (A h) := fun _ => rfl
  have AQ : ∀ h, A (Q h) = 0 := fun h => by rw [Qa, map_sub, aJ, sub_self]
  have nQ : ∀ h, ‖Q h‖ ^ 2 = ‖h‖ ^ 2 - ‖A h‖ ^ 2 := fun h => by
    have h1 : ⟪D.J (A h), Q h⟫_ℂ = 0 := by rw [iA, AQ, inner_zero_right]
    have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h1
    rw [Qa h, add_sub_cancel, D.J.norm_map, ← Qa] at h2
    nlinarith
  let x : L W → ℝ → H := fun v t => Q (D.J' (sh W t v))
  have Ax : ∀ v t, A (x v t) = 0 := fun v t => AQ _
  have nx : ∀ v t, ‖x v t‖ = ‖Q (D.J' v)‖ := fun v t => by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [nQ, nQ, S1, D.J'.norm_map, D.J'.norm_map]
    exact congrArg₂ (fun a b : ℝ => a ^ 2 - b ^ 2) ((shF W).norm t v) ((shF V).norm _ _)
  have A'x : ∀ v t, A' (x v t) = sh W t (v - A' (D.J (A (D.J' v)))) := fun v t => by
    show A' (Q _) = _
    rw [Qa, map_sub, aJ', S1, S2, map_sub]
  have dense : ∀ (y : H) (ε : ℝ), 0 < ε → ∃ u v, ‖y - (D.J u + D.J' v)‖ < ε := by
    intro y ε hε
    have : (LinearMap.range D.J.toLinearMap ⊔ LinearMap.range D.J'.toLinearMap).topologicalClosure = ⊤ := by
      rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
      exact fun h hh => D.span h (fun u => hh _ (Submodule.mem_sup_left ⟨u, rfl⟩)) fun v => hh _ (Submodule.mem_sup_right ⟨v, rfl⟩)
    have hy : y ∈ closure ((LinearMap.range D.J.toLinearMap ⊔ LinearMap.range D.J'.toLinearMap : Submodule ℂ H) : Set H) := by
      rw [← Submodule.topologicalClosure_coe, this]; trivial
    obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.1 hy ε hε
    obtain ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hz
    exact ⟨u, v, by rwa [dist_eq_norm] at hd⟩
  have weak : ∀ v y, Tendsto (fun t => ⟪y, x v t⟫_ℂ) atTop (𝓝 0) := by
    intro v y
    rw [Metric.tendsto_nhds]
    intro ε hε
    set c := ‖Q (D.J' v)‖ + 1 with hc
    have c0 : 0 < c := by positivity
    obtain ⟨u, w, hd⟩ := dense y (ε / 2 / c) (by positivity)
    have h1 := Metric.tendsto_nhds.1 (shNull (V := W) (v - A' (D.J (A (D.J' v)))) w).1 (ε / 2) (by positivity)
    filter_upwards [h1] with t ht
    rw [dist_zero_right] at ht ⊢
    have e : ⟪y, x v t⟫_ℂ = ⟪y - (D.J u + D.J' w), x v t⟫_ℂ + ⟪w, (shF W).U t (v - A' (D.J (A (D.J' v))))⟫_ℂ := by
      rw [inner_sub_left, inner_add_left, iA, iA', A'x, Ax, inner_zero_right, zero_add]
      exact (sub_add_cancel _ _).symm
    rw [e]
    have h2 : ‖⟪y - (D.J u + D.J' w), x v t⟫_ℂ‖ ≤ ε / 2 / c * c := by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [nx]; gcongr; linarith
    rw [div_mul_cancel₀ _ c0.ne'] at h2
    linarith [norm_add_le ⟪y - (D.J u + D.J' w), x v t⟫_ℂ ⟪w, (shF W).U t (v - A' (D.J (A (D.J' v))))⟫_ℂ]
  have sup : ∀ {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [CompleteSpace X] (s : ℝ) (u : L X),
      ∀ᵐ x : ℝ, x ≤ s → cut X (Ioi s) u x = 0 := fun s u =>
    (((cutLaws (Ioi s) (Ioi s) measurableSet_Ioi measurableSet_Ioi).2.2.2.2.2.2.2.1 _).1
      (by simpa using DFunLike.congr_fun (cutLaws (Ioi s) (Ioi s) measurableSet_Ioi measurableSet_Ioi).1 u)).mono
      fun x h hx => h (by simpa using hx)
  set Λ : H →L[ℂ] H := 1 - J ∘L cut V (Ioi D.T₀) ∘L A - J' ∘L cut W (Ioi D.T₀) ∘L A' with hΛ
  have tr : IsTrunc D.J D.J' D.T₀ Λ := (truncEq D.J D.J' D.T₀ Λ fun u v =>
    D.causal D.T₀ _ _ (sup _ u) ((sup _ v).mono fun x h hx => h (by linarith))).2 rfl
  have Λx : ∀ v, Tendsto (fun t => x v t - Λ (x v t)) atTop (𝓝 0) := fun v => by
    have := (D.J'.continuous.tendsto 0).comp ((cutLim (v - A' (D.J (A (D.J' v))))).1 D.T₀)
    rw [map_zero] at this
    refine this.congr fun t => ?_
    show _ = x v t - (x v t - D.J (cut V _ (A (x v t))) - D.J' (cut W _ (A' (x v t))))
    rw [A'x, Ax]; simp
  have BJ : ∀ u, D.B (D.J u) = D.J (conv D.β u) := fun u => D.B_J u _ (convSpec _ D.β_ker u).1
  have BJ' : ∀ u, D.B (D.J' u) = D.J' (conv D.β' u) := fun u => D.B_J' u _ (convSpec _ D.β'_ker u).1
  have BQ : ∀ h, D.B (Q h) = Q (D.B h) := fun h => by
    have h1 : A (D.B (Q h)) = 0 := ext_inner_left ℂ fun y => by
      rw [← iA, ← D.B_sa.isSymmetric.apply_clm, BJ, iA, AQ, inner_zero_right, inner_zero_right]
    have h2 : D.B h = D.B (Q h) + D.J (conv D.β (A h)) := by rw [← BJ, ← map_add (f := _), Qa, sub_add_cancel]
    rw [Qa (D.B h)]
    conv_rhs => rw [h2, map_add (f := _), h1, aJ, zero_add, add_sub_cancel_right]
  have Bx : ∀ v t, D.B (x v t) = x (conv D.β' v) t := fun v t => by
    show D.B (Q _) = Q _
    rw [BQ, BJ']
    exact congrArg (fun z => Q (D.J' z)) (DFunLike.congr_fun ((convLaws _ D.β'_ker).1 t) v)
  have zero : ∀ v, Q (D.J' (conv D.β' v)) = 0 := fun v => by
    have t1 := cptNull atTop _ (x v) _ (D.compact _ Λ le_rfl tr) (fun t => (nx v t).le) (weak v)
    have t2 := ((Λ ∘L D.B).continuous.tendsto 0).comp (Λx v)
    have t3 := (t1.add t2).add (Λx (conv D.β' v))
    simp only [map_zero, add_zero] at t3
    have t4 : Tendsto (fun t => x (conv D.β' v) t) atTop (𝓝 0) := t3.congr fun t => by
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_sub, Bx]; abel
    have t5 := tendsto_zero_iff_norm_tendsto_zero.1 t4
    simp only [nx] at t5
    exact norm_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds t5)
  have QJ' : ∀ v, Q (D.J' v) = 0 := fun v =>
    (convDense _ D.β'_ker D.β'_unit).induction_on v (isClosed_eq (Q.continuous.comp D.J'.continuous) continuous_const) zero
  intro h
  refine ⟨A h, (sub_eq_zero.1 (D.span (Q h) (fun u => by rw [iA, AQ, inner_zero_right]) fun v => ?_)).symm⟩
  have e : D.J' v = D.J (A (D.J' v)) := sub_eq_zero.1 (QJ' v)
  rw [e, iA, AQ, inner_zero_right]
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.model :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (D : Datum H V W), ∃ M : Sc H V W, M.T₀ = D.T₀ ∧ (∀ u, M.J u = D.J u) ∧ (∀ v, M.J' v = D.J' v) ∧
      ∀ T Λ, D.T₀ ≤ T → (IsTrunc D.J D.J' T Λ ↔ Λ = M.abelian₂ T T) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ D
  let D' : Datum H W V :=
    { J := D.J', J' := D.J, T₀ := D.T₀, B := D.B, β := D.β', β' := D.β
      span := fun h a b => D.span h b a
      shift := fun t u u' v v' a b => by
        rw [← inner_conj_symm, ← D.shift t v v' u u' b a, inner_conj_symm]
      causal := fun s u v a b => by
        rw [← inner_conj_symm, D.causal (2 * D.T₀ - s) v u b (by simpa using a), map_zero]
      β_ker := D.β'_ker, β'_ker := D.β_ker, β_unit := D.β'_unit, β'_unit := D.β_unit, B_sa := D.B_sa
      B_J := D.B_J', B_J' := D.B_J
      compact := fun T Λ hT h => D.compact T Λ hT ⟨h.1, h.2.1, fun x => (h.2.2 x).trans
        ⟨fun ⟨u, v, a, b, c⟩ => ⟨v, u, b, a, c.trans (add_comm _ _)⟩, fun ⟨u, v, a, b, c⟩ => ⟨v, u, b, a, c.trans (add_comm _ _)⟩⟩⟩ }
  let J := LinearIsometryEquiv.ofSurjective D.J (ontoJ D)
  let J' := LinearIsometryEquiv.ofSurjective D.J' (ontoJ D')
  have hJ : ∀ u, J u = D.J u := fun _ => rfl
  have hJ' : ∀ u, J' u = D.J' u := fun _ => rfl
  let F : Flow H :=
    { U := fun t => (J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L sh V t ∘L (J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
      zero := fun h => by
        show J ((shF V).U 0 (J.symm h)) = h
        rw [(shF V).zero, J.apply_symm_apply]
      add := fun s t h => by
        show J ((shF V).U (s + t) (J.symm h)) = J ((shF V).U s (J.symm (J ((shF V).U t (J.symm h)))))
        rw [(shF V).add, J.symm_apply_apply]
      norm := fun t h => by
        show ‖J ((shF V).U t (J.symm h))‖ = _
        rw [J.norm_map, (shF V).norm, J.symm.norm_map]
      cont := fun h => J.continuous.comp ((shF V).cont _) }
  have hU : ∀ t u, F.U t (J u) = J (sh V t u) := fun t u => by
    show J (sh V t (J.symm (J u))) = _
    rw [J.symm_apply_apply]
  have sup : ∀ {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [CompleteSpace X] (s : ℝ) (u : L X),
      ∀ᵐ x : ℝ, x ≤ s → cut X (Ioi s) u x = 0 := fun s u =>
    (cutSpec (Ioi s) measurableSet_Ioi u).mono fun x h hx => by rw [h, indicator_of_notMem (by simpa using hx)]
  have caus : ∀ (s : ℝ) (u : L V) (v : L W), ⟪J (cut V (Ioi s) u), J' (cut W (Ioi (2 * D.T₀ - s)) v)⟫_ℂ = 0 :=
    fun s u v => D.causal s _ _ (sup s u) (sup _ v)
  refine ⟨⟨J, J', F, D.T₀, hU, fun t v => ?_, caus⟩, rfl, hJ, hJ', fun T Λ hT => ?_⟩
  · refine ext_inner_left ℂ fun h => ?_
    obtain ⟨u, rfl⟩ := J.surjective h
    have e : J u = F.U t (J (sh V (-t) u)) := by rw [← hU, ← F.add, add_neg_cancel, F.zero]
    conv_lhs => rw [e]
    refine ((⟨(F.U t : H →ₗ[ℂ] H), F.norm t⟩ : H →ₗᵢ[ℂ] H).inner_map_map _ _).trans ?_
    exact D.shift (-t) u _ v _ (sh_ae V _ u) (sh_ae W _ v)
  · rw [truncEq D.J D.J' T Λ fun u v => D.causal T _ _ (sup T u) ((sup T v).mono fun x h hx => h (by linarith))]
    have a1 : ContinuousLinearMap.adjoint D.J.toContinuousLinearMap = (J.symm.toContinuousLinearEquiv : H →L[ℂ] L V) :=
      ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => (J.inner_map_map _ _).symm.trans (by
        show ⟪J (J.symm x), J y⟫_ℂ = _
        rw [J.apply_symm_apply]; rfl)).symm
    have a2 : ContinuousLinearMap.adjoint D.J'.toContinuousLinearMap = (J'.symm.toContinuousLinearEquiv : H →L[ℂ] L W) :=
      ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => (J'.inner_map_map _ _).symm.trans (by
        show ⟪J' (J'.symm x), J' y⟫_ℂ = _
        rw [J'.apply_symm_apply]; rfl)).symm
    rw [a1, a2]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceNear
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W)

private theorem k1 {T : ℝ} (hT : M.T₀ ≤ T) {r : ℝ} (hr : r ≤ 0) (h : H) : M.abelian₂ T T (M.F.U r (M.P (Ioi T) h)) = 0 := by
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have x1 := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T))).2.2.2.2 r).1 h
  have y1 : (fun x : ℝ => x + r) ⁻¹' Ioi T = Ioi (T - r) := by ext x; simp [sub_lt_iff_lt_add]
  have x2 := (hP _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T - r))).1
  rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at x2
  rw [y1, ← x2] at x1
  simp only [ContinuousLinearMap.comp_apply] at x1
  rw [x1]
  exact DFunLike.congr_fun (hL T T (by linarith)).2.2.2.2.2.1 _

private theorem k2 {T δ : ℝ} (hT : M.T₀ ≤ T) {r : ℝ} (hr : -δ ≤ r) (h : H) : M.abelian₂ T T (M.F.U r (M.P' (Ioi (T + δ)) h)) = 0 := by
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have x1 := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioi (a := T + δ)) (measurableSet_Ioi (a := T))).2.2.2.2 r).2 h
  have y1 : (fun x : ℝ => x - r) ⁻¹' Ioi (T + δ) = Ioi (T + δ + r) := by ext x; simp [lt_sub_iff_add_lt]
  have x2 : M.P' (Ioi T) ∘L M.P' (Ioi (T + δ + r)) = M.P' (Ioi T ∩ Ioi (T + δ + r)) :=
    ((projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T + δ + r))).1
  rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at x2
  rw [y1, ← x2] at x1
  simp only [ContinuousLinearMap.comp_apply] at x1
  rw [x1]
  exact DFunLike.congr_fun (hL T T (by linarith)).2.2.2.2.2.2.2.1 _

private theorem k3 {ψ : ℝ → ℝ} {δ : ℝ} (hψ : Bump ψ (-δ) 0) (A : H →L[ℂ] H) (h : H)
    (hA : ∀ r, -δ ≤ r → r ≤ 0 → A (M.F.U r h) = 0) : A (M.F.av (fun t => (ψ t : ℂ)) h) = 0 := by
  obtain ⟨i, e⟩ := ((avSpec M.F).2.2.2 _ (avApprox.2.1 ψ _ _ hψ).2.1).1 h
  rw [e, ← A.integral_comp_comm i]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ Icc (-δ) 0
  · simp [hA r hr.1 hr.2]
  · simp [hψ.supp r hr]

private theorem k4 {T ρ : ℝ} (hρ : 0 ≤ ρ) : M.P' (Ioi T) = M.P' (Ioc T (T + ρ)) + M.P' (Ioi (T + ρ)) := by
  have := ((projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioc (a := T) (b := T + ρ)) (measurableSet_Ioi (a := T + ρ))).2.2.2.1
    (Ioc_disjoint_Ioi le_rfl)
  rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this

private theorem k5 (T : ℝ) (h : H) : h = M.abelian₂ T T h + M.P (Ioi T) h + M.P' (Ioi T) h := by
  show h = h - M.P (Ioi T) h - M.P' (Ioi T) h + _ + _
  abel

private theorem k6 {X : H →L[ℂ] H} {κ : ℝ → V →L[ℂ] W} (hk : Ker κ) (hX : M.Carries X κ) {ψ : ℝ → ℝ} {δ : ℝ} (hψ : Bump ψ (-δ) 0)
    {a b : ℝ} (hab : a ≤ b) :
    IsHilbertSchmidt (M.F.av (fun t => (ψ t : ℂ)) ∘L M.P' (Ioc a b)) ∧ IsHilbertSchmidt (M.P' (Ioc a b) ∘L X) ∧
    hsNorm (M.F.av (fun t => (ψ t : ℂ)) ∘L M.P' (Ioc a b)) ^ 2 = (b - a) * (Module.finrank ℂ W * ∫ x, ψ x ^ 2) ∧
    hsNorm (M.P' (Ioc a b) ∘L X) ^ 2 = (b - a) * ∑ i, ‖kv (sharp κ) (stdOrthonormalBasis ℂ W i)‖ ^ 2 ∧
    M.P' (Ioc a b) ∘L M.P' (Ioc a b) = M.P' (Ioc a b) := by
  obtain ⟨hs, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  obtain ⟨b1, b2, b3, b4, -⟩ := bandHS M.swap _ _ (convAdj κ hk).1 (carLaws M X κ hk hX).2.1 (fun t => (ψ (-t) : ℂ)) a b
    (Complex.continuous_ofReal.comp (hψ.cont.comp continuous_neg))
    ((hs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun x : ℝ => (x : ℂ)) rfl) hab
  have e : M.swap.F.av (fun t => (ψ (-t) : ℂ)) = M.F.av fun t => (ψ t : ℂ) := by
    have := ((avSpec M.F).2.2.2 _ hi.comp_neg).2.2.2.1
    simp only [neg_neg] at this
    exact this
  rw [e] at b3 b4
  obtain ⟨p1, p2, -⟩ := (projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioc (a := a) (b := b)) (measurableSet_Ioc (a := a) (b := b))
  rw [inter_self] at p1
  have e2 : M.P' (Ioc a b) ∘L X = ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint X ∘L M.swap.P (Ioc a b)) := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, p2.adjoint_eq]; rfl
  refine ⟨b3, e2 ▸ b1.adjoint, b4.trans ?_, by rw [e2, hsNorm_adjoint, b2], p1⟩
  have := integral_neg_eq_self (fun x => ψ x ^ 2) volume
  simp [this]
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceNear :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ T : ℝ, M.T₀ ≤ T → IsTraceClass (M.abelian₂ T T ∘L X ∘L M.abelian₂ T T) → ∀ ε : ℝ, 0 < ε →
      ∃ (ψ : ℝ → ℝ) (δ : ℝ), 0 < δ ∧ δ ≤ 1 / 2 ∧ Bump ψ (-δ) 0 ∧
        ‖trace (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) - trace (M.abelian₂ T T ∘L X ∘L M.abelian₂ T T)‖ ≤ ε := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX T hT htc ε hε
  obtain ⟨-, -, l0, sa, ln, -⟩ := (projLaws M).2.2.2.2.2.2.2 T T (by linarith)
  set Λ := M.abelian₂ T T
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) / 2
  have d0 : ∀ n, 0 < d n := fun n => by positivity
  have d1 : ∀ n, d n ≤ 1 / 2 := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    show _ / 2 ≤ _; linarith
  have dt : Tendsto d atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2 : ℝ)
    rwa [zero_div] at this
  choose ψ hψ using fun n => avApprox.1 (-d n) 0 (by linarith [d0 n])
  let Ψ : ℕ → H →L[ℂ] H := fun n => M.F.av fun t => (ψ n t : ℂ)
  have nΨ : ∀ n, ‖Ψ n‖ ≤ 1 := fun n => by
    refine ((avSpec M.F).2.2.2 _ (avApprox.2.1 _ _ _ (hψ n)).2.1).2.1.trans_eq ?_
    rw [← (hψ n).total]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp [abs_of_nonneg ((hψ n).nonneg t)])
  have sΨ : ∀ h, Tendsto (fun n => Ψ n h) atTop (𝓝 h) := fun h => by
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨δ, hδ, H1⟩ := avApprox.2.2 M.F h (η / 2) (by positivity)
    filter_upwards [dt.eventually (ge_mem_nhds hδ)] with n hn
    rw [dist_eq_norm]
    linarith [H1 _ _ _ (hψ n) (neg_le_neg hn) hδ.le]
  have t1 := trWeak atTop (fun n => Λ ∘L Ψ n) Λ _ htc
    (fun n => (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_one₀ ln (norm_nonneg _) (nΨ n)))
    fun x y => tendsto_const_nhds.inner ((Λ.continuous.tendsto y).comp (sΨ y))
  rw [show Λ ∘L (Λ ∘L X ∘L Λ) = Λ ∘L X ∘L Λ from congrArg (· ∘L (X ∘L Λ)) l0] at t1
  set c := ∑ i, ‖kv (sharp κ) (stdOrthonormalBasis ℂ W i)‖ ^ 2
  have t2 : Tendsto (fun n => √(2 * Module.finrank ℂ W) * √(d n * c)) atTop (𝓝 0) := by
    simpa using ((dt.mul_const c).sqrt).const_mul √(2 * Module.finrank ℂ W)
  obtain ⟨n, hn1, hn2⟩ := ((Metric.tendsto_nhds.1 t1 (ε / 2) (by positivity)).and
    (t2.eventually (ge_mem_nhds (show 0 < ε / 2 by positivity)))).exists
  refine ⟨ψ n, d n, d0 n, d1 n, hψ n, ?_⟩
  obtain ⟨h1, h2, h4, h5, h3⟩ := k6 M hk hX (hψ n) (a := T) (b := T + d n) (by linarith [d0 n])
  set E := M.P' (Ioc T (T + d n))
  have key : Λ ∘L (Ψ n ∘L X) ∘L Λ = (Λ ∘L Ψ n) ∘L (Λ ∘L X ∘L Λ) + (Λ ∘L (Ψ n ∘L E)) ∘L ((E ∘L X) ∘L Λ) := by
    ext h
    have a1 : Λ (Ψ n (M.P (Ioi T) (X (Λ h)))) = 0 := k3 M (hψ n) _ _ fun r _ hr => k1 M hT hr _
    have a2 : Λ (Ψ n (M.P' (Ioi (T + d n)) (X (Λ h)))) = 0 := k3 M (hψ n) _ _ fun r hr _ => k2 M hT hr _
    have a3 : E (E (X (Λ h))) = E (X (Λ h)) := DFunLike.congr_fun h3 _
    show Λ (Ψ n (X (Λ h))) = Λ (Ψ n (Λ (X (Λ h)))) + Λ (Ψ n (E (E (X (Λ h)))))
    conv_lhs => rw [k5 M T (X (Λ h)), k4 M (d0 n).le, ContinuousLinearMap.add_apply]
    simp only [map_add (f := _)]
    rw [a1, a2, a3, add_zero, add_zero]
  have g1 := h1.comp_left Λ
  have g2 := h2.comp_right Λ
  have tc := isTraceClass_comp g1 g2
  have nl : ‖Λ‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one ln
  have b1 : hsNorm (Λ ∘L (Ψ n ∘L E)) ≤ √(2 * Module.finrank ℂ W) := by
    refine Real.le_sqrt_of_sq_le ?_
    have : hsNorm (Λ ∘L (Ψ n ∘L E)) ^ 2 ≤ hsNorm (Ψ n ∘L E) ^ 2 := by
      rw [hsNorm_sq, hsNorm_sq]
      refine ENNReal.toReal_mono (ne_of_lt h1) ((hsNormSq_comp_left_le _ _).trans ?_)
      exact mul_le_of_le_one_left' (pow_le_one' nl 2)
    refine this.trans (h4.trans_le ?_)
    have i := (avApprox.2.1 _ _ _ (hψ n)).2.2
    rw [add_sub_cancel_left]
    rw [sub_neg_eq_add, zero_add, le_div_iff₀ (d0 n)] at i
    nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℂ W)]
  have b2 : hsNorm ((E ∘L X) ∘L Λ) ≤ √(d n * c) := by
    refine Real.le_sqrt_of_sq_le ?_
    have : hsNorm ((E ∘L X) ∘L Λ) ^ 2 ≤ hsNorm (E ∘L X) ^ 2 := by
      rw [hsNorm_sq, hsNorm_sq]
      refine ENNReal.toReal_mono (ne_of_lt h2) ((hsNormSq_comp_right_le _ _).trans ?_)
      exact mul_le_of_le_one_left' (pow_le_one' nl 2)
    exact this.trans (h5.trans (by rw [add_sub_cancel_left])).le
  have b3 : ‖trace ((Λ ∘L (Ψ n ∘L E)) ∘L ((E ∘L X) ∘L Λ))‖ ≤ ε / 2 := by
    refine le_trans ?_ ((traceNorm_comp_le g1 g2).trans ((mul_le_mul b1 b2 (hsNorm_nonneg _) (Real.sqrt_nonneg _)).trans hn2))
    have := ENNReal.toReal_mono (ne_of_lt tc) (enorm_trace_le ((Λ ∘L (Ψ n ∘L E)) ∘L ((E ∘L X) ∘L Λ)))
    simpa using this
  show ‖trace (Λ ∘L (Ψ n ∘L X) ∘L Λ) - _‖ ≤ ε
  rw [key, trace_add (htc.comp_left _) tc, add_sub_right_comm]
  rw [dist_eq_norm] at hn1
  exact (norm_add_le _ _).trans (by linarith)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NInt
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nInt :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → M.Acts Y β β' →
      ∀ w, N (symb β' 0 w) = symb β 0 (N w) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN Y β β' k1 k2 ha w
  obtain ⟨-, cadd, -, -, -, -, -, cmap⟩ := cobLaws M.F
  have hY : ∀ t h, Y (M.F.U t h) = M.F.U t (Y h) := fun t h => by
    obtain ⟨u, rfl⟩ := M.J.surjective h
    rw [M.hJ, ha.1, ha.1, M.hJ]
    exact congrArg M.J (DFunLike.congr_fun ((convLaws β k1).1 t) u)
  have h1 := cmap M.F Y hY _ (hN w)
  rw [map_sub, ha.1, ha.2] at h1
  obtain ⟨-, b1, s1⟩ := (svSpec (V := W)).2 w
  obtain ⟨-, b2, s2⟩ := (svSpec (V := V)).2 (N w)
  obtain ⟨b3, s3⟩ := (convLaws β' k2).2.2 _ b1
  obtain ⟨b4, s4⟩ := (convLaws β k1).2.2 _ b2
  have h2 := nAll M N hN _ b3
  rw [s3, s1] at h2
  have h3 := ((cobTail _).2 ((cobTail _).1 b4)).2
  rw [s4, s2] at h3
  have h4 := (cobLaws (shF V)).2.2.2.2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) (fun t h => (M.hJ t h).symm) _ h3
  have h5 := (cadd _ _ (cadd _ _ h1 h2).2 h4).1
  have h6 : M.F.Cob (M.J (one V (N (symb β' 0 w) - symb β 0 (N w)))) := by
    convert h5 using 1
    simp
  exact sub_eq_zero.1 ((nIso M).1 _ h6)
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.main :
    PositivityTheory.Rg.Tf.IntegralApplyAeEq.Main := by
  intro H V W _ _ _ _ _ _ _ _ _ D
  haveI := FiniteDimensional.complete ℂ V
  haveI := FiniteDimensional.complete ℂ W
  obtain ⟨M, hT, hJ, hJ', hL⟩ := model D
  have act : ∀ Y β β', Ker β → Ker β' → Conv D.J D.J Y β → Conv D.J' D.J' Y β' → M.Acts Y β β' := fun Y β β' k k' c c' =>
    ⟨fun u => by rw [hJ, hJ]; exact c u _ (convSpec β k u).1, fun v => by rw [hJ', hJ']; exact c' v _ (convSpec β' k' v).1⟩
  obtain ⟨N, hN⟩ := nUnit M D.B D.β D.β' D.β_ker D.β'_ker D.β_unit D.β'_unit (act _ _ _ D.β_ker D.β'_ker D.B_J D.B_J')
    (hT ▸ D.compact D.T₀ _ le_rfl ((hL _ _ le_rfl).2 rfl))
  refine ⟨N, fun Y β β' k k' c c' => nInt M _ hN Y β β' k k' (act _ _ _ k k' c c'), ?_⟩
  intro X Λ κ T K hk hc hT' hΛ htc hb
  obtain rfl := (hL T Λ hT').1 hΛ
  have hX : M.Carries X κ := fun u => by rw [hJ, hJ']; exact hc u _ (convSpec κ hk u).1
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨ψ, δ, -, hδ, hψ, h1⟩ := traceNear M X κ hk hX T (hT ▸ hT') htc ε hε
  have h2 := traceSm M N hN X κ hk hX ψ δ T K hδ hψ (hT ▸ hT') htc hb
  rw [hT] at h2
  rw [norm_sub_rev] at h1
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add h1 h2).trans_eq (add_comm _ _))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.CixOf
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.Ci UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cix_of (hK : KernX) (hT : ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => TruncCpt μ A A') : CIx :=
  cixOf Dp.parEx (trExp expForm) (evVal evEx Dp.parEx) valBc killEx2 kfBc truncSpec sepPoly
    (oneSide K.kern2 C.polyBdAll C.smoothDecay C.decayTraceClass C.cuspTrBand Dp.multiplicity_one_cuspidal_spectrum_normOneGL evEx) (oneSideX hK evEx) evEx kill
    killExempt (famEx hT unitB pairFacts UpperTheory.V.Z.IntegralApplyAeEq.main)
end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cix : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.CIx := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cix_of UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.kernX UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.truncCpt
end

open UpperTheory.ConvolutionTheory UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indCs_of_gm (hG : GM.GM) : IndCs :=
  indCs (indNorm (coreInd cix hG (T.liftAll (T.liftStep (T.coreLift ci hG)))))

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indCs_of_bcfl (h : PositivityTheory.Rg.Tf.Loc.BCFLUnit) : IndCs :=
  indCs_of_gm (GM.gm_of_bcfl h)
end

namespace UpperTheory.V.Z.Bc

theorem indCs : Z.InvariantSubmoduleMonicPolynomial.E.IndCs := Z.InvariantSubmoduleMonicPolynomial.E.indCs_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit

end UpperTheory.V.Z.Bc
