module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.KillsIrreducible
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LineVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.TypeOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCuspidalSectionFromLeviAverage
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLevelAndKTypeVectorForLeviInduction

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LeviInducedSectionFixedByArchIdempotentAndLevel
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

private theorem cont_int {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℂ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private theorem swap3 {A V : Type*} [TopologicalSpace A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [TopologicalSpace V] [CompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] (κ : Measure A) (ρ : Measure V) [IsFiniteMeasure κ] [IsFiniteMeasure ρ]
    (G : A → V → V → ℂ) (hG : Continuous fun p : A × V × V => G p.1 p.2.1 p.2.2) :
    ∫ a, ∫ v₁, ∫ v₂, G a v₁ v₂ ∂ρ ∂ρ ∂κ = ∫ v₁, ∫ v₂, ∫ a, G a v₁ v₂ ∂κ ∂ρ ∂ρ := by
  have h1 : Integrable (Function.uncurry fun a v₁ => ∫ v₂, G a v₁ v₂ ∂ρ) (κ.prod ρ) := by
    have h : Integrable (fun p : (A × V) × V => G p.1.1 p.1.2 p.2) ((κ.prod ρ).prod ρ) :=
      cont_int _ (hG.comp (f := fun q : (A × V) × V => (q.1.1, q.1.2, q.2)) (by fun_prop))
    exact h.integral_prod_left
  rw [integral_integral_swap h1]
  refine integral_congr_ae (ae_of_all _ fun v₁ => ?_)
  refine integral_integral_swap ?_
  exact cont_int _ (hG.comp (f := fun q : A × V => (q.1, v₁, q.2)) (by fun_prop))

theorem UpperTheory.leviInducedSection_fixed_by_archIdempotent_and_level :
    ∀ {K : Type} [Field K] [NumberField K] (ρ : Measure (KG K 2)), IsProbabilityMeasure ρ → ∀ Ψ : G1 K (2 + 2) → ℂ, (Continuous fun k : KG K (2 + 2) => Ψ k) → ∀ φ₁ φ₂ : G1 K 2 → ℂ, Continuous φ₁ → Continuous φ₂ → (∃ B : ℝ, ∀ m, ‖φ₁ m‖ ≤ B) → (∃ B : ℝ, ∀ m, ‖φ₂ m‖ ≤ B) → ∀ f : G1 K (2 + 2) → ℂ, (∀ X m₁ m₂ t, ∀ k ∈ KG K (2 + 2), f (nn X * lv m₁ m₂ t * k) = ∫ v₁ : KG K 2, ∫ v₂ : KG K 2, Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹) ∂ρ ∂ρ) → (∀ (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ), IdemA κ e → (∀ k ∈ KG K (2 + 2), ∫ a, e a * Ψ (k * arc1 a) ∂κ = Ψ k) → FixA κ e f) ∧ ∀ U : Subgroup (FA K (2 + 2)), U ≤ AdelicGLn.integralFiniteGL K (2 + 2) → (∀ k ∈ KG K (2 + 2), ∀ u ∈ U, Ψ (k * fin1 u) = Ψ k) → FixF U f := by
  intro K _ _ ρ hρ Ψ hΨ φ₁ φ₂ h₁ h₂ _ _ f hf
  obtain ⟨-, -, -, hlvc, -, -, -, -, -, -, hlvK, hcomp⟩ := blkLaws (K := K)
  obtain ⟨α, β, -, -, -, -, harc, hfin⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) (2 + 2)
  haveI : CompactSpace (KG K 2) := isCompact_iff_compactSpace.1 (hcomp 2).1
  refine ⟨fun κ e he hfix g => ?_, fun U hU hfix u hu g => ?_⟩
  · haveI := he.haar.prob
    obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    have harc1 : Continuous fun a : archCompact K (2 + 2) => arc1 a :=
      continuous_archP.comp continuous_subtype_val
    have hfa : ∀ a : archCompact K (2 + 2), e a * f (nn X * lv m₁ m₂ t * k * arc1 a) =
        ∫ v₁ : KG K 2, ∫ v₂ : KG K 2, e a * (Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k * arc1 a)) *
          φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹)) ∂ρ ∂ρ := by
      intro a
      rw [mul_assoc (nn X * lv m₁ m₂ t) k, hf X m₁ m₂ t _ (mul_mem hk (harc a)), ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun v₁ => ?_)
      beta_reduce
      rw [← integral_const_mul]
    have hlv : Continuous fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 =>
        lv (p.2.1 : G1 K 2) (p.2.2 : G1 K 2) 0 :=
      hlvc.comp (f := fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 =>
        ((p.2.1 : G1 K 2), (p.2.2 : G1 K 2), (0 : ℝ))) (by fun_prop)
    have hpsi : Continuous fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 =>
        Ψ (lv (p.2.1 : G1 K 2) (p.2.2 : G1 K 2) 0 * (k * arc1 p.1)) :=
      hΨ.comp (Continuous.subtype_mk (hlv.mul (continuous_const.mul (harc1.comp continuous_fst)))
        fun p => mul_mem (hlvK _ p.2.1.2 _ p.2.2.2) (mul_mem hk (harc p.1)))
    have hc₁ : Continuous fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 =>
        φ₁ (m₁ * (p.2.1 : G1 K 2)⁻¹) :=
      h₁.comp (continuous_const.mul (by fun_prop))
    have hc₂ : Continuous fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 =>
        φ₂ (m₂ * (p.2.2 : G1 K 2)⁻¹) :=
      h₂.comp (continuous_const.mul (by fun_prop))
    have he' : Continuous fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 => e p.1 :=
      he.cont.comp continuous_fst
    simp_rw [hfa]
    rw [swap3 κ ρ (fun a v₁ v₂ => e a * (Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k * arc1 a)) *
      φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹))) (he'.mul ((hpsi.mul hc₁).mul hc₂)),
      hf X m₁ m₂ t k hk]
    refine integral_congr_ae (ae_of_all _ fun v₁ => integral_congr_ae (ae_of_all _ fun v₂ => ?_))
    have hfx := hfix _ (mul_mem (hlvK _ v₁.2 _ v₂.2) hk)
    have hsplit : ∀ a : archCompact K (2 + 2), e a * (Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k * arc1 a)) *
        φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹)) =
        e a * Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k * arc1 a) *
          (φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹)) := by
      intro a
      rw [← mul_assoc (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0) k]
      ring
    show ∫ a, e a * (Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k * arc1 a)) *
        φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹)) ∂κ = _
    simp_rw [hsplit]
    rw [integral_mul_const, hfx, mul_assoc]
  · obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    have hu' : fin1 u ∈ KG K (2 + 2) := hfin ⟨u, hU hu⟩
    rw [mul_assoc (nn X * lv m₁ m₂ t) k, hf X m₁ m₂ t _ (mul_mem hk hu'), hf X m₁ m₂ t k hk]
    refine integral_congr_ae (ae_of_all _ fun v₁ => integral_congr_ae (ae_of_all _ fun v₂ => ?_))
    show Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k * fin1 u)) * _ * _ = Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k) * _ * _
    rw [← mul_assoc, hfix _ (mul_mem (hlvK _ v₁.2 _ v₂.2) hk) u hu]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSpanMaximalCompactTranslatesOfF
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

theorem UpperTheory.finiteDimensional_span_maximalCompact_translates_of_fix :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (f : G1 K n → ℂ), Continuous f → D.Fix f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K n => fun m => f (m * k))) := by
  intro K _ _ n D f hf hfix
  obtain ⟨-, -, 𝒜, hfd, -, hA⟩ := typeFin D
  haveI := hfd
  obtain ⟨O, hO, hUO⟩ := D.isOpen
  haveI : CompactSpace (KG K n) :=
    isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1
  let W : Subgroup (KG K n) := D.U.subgroupOf (KG K n)
  have hWo : IsOpen (W : Set (KG K n)) := by
    have hW : (W : Set (KG K n)) = (fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n)) ⁻¹' O := by
      ext k
      exact ⟨fun h => ((hUO k).1 h).1, fun h => (hUO k).2 ⟨h, k.2⟩⟩
    rw [hW]
    exact hO.preimage (continuous_subtype_val.comp continuous_subtype_val)
  haveI : Finite (KG K n ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo
  let B := Module.finBasis ℂ 𝒜
  let x : G1 K n → 𝒜 := fun m => ⟨fun u : D.U => f (m * u), hA f hf hfix m⟩
  let c : Fin (Module.finrank ℂ 𝒜) × (KG K n ⧸ W) → G1 K n → ℂ :=
    fun p m => B.repr (x (m * ((Quotient.out p.2 : KG K n) : G1 K n))) p.1
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul W k
  set q : KG K n ⧸ W := (k : KG K n ⧸ W) with hq
  let u : D.U := ⟨(((h : KG K n)⁻¹ : KG K n) : G1 K n), Subgroup.mem_subgroupOf.1 (W.inv_mem h.2)⟩
  have hk : (k : G1 K n) = ((Quotient.out q : KG K n) : G1 K n) * u := by
    have : k = Quotient.out q * (h : KG K n)⁻¹ := by
      rw [hh]; simp
    exact congrArg Subtype.val this
  have e : (fun m => f (m * k)) = ∑ i, ((B i : 𝒜) : D.U → ℂ) u • c (i, q) := by
    funext m
    have h1 := congrArg (fun y : 𝒜 => (y : D.U → ℂ) u)
      (B.sum_repr (x (m * ((Quotient.out q : KG K n) : G1 K n))))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk, ← mul_assoc]
    change _ = ∑ i, ((B i : 𝒜) : D.U → ℂ) u * B.repr (x (m * ((Quotient.out q : KG K n) : G1 K n))) i
    simp only [mul_comm (((B _ : 𝒜) : D.U → ℂ) u)]
    exact h1.symm
  change (fun m => f (m * (k : G1 K n))) ∈ Submodule.span ℂ (Set.range c)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, q), rfl⟩)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.IntegralMemFd
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem proj_fix (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (A B : H →L[ℂ] H)
    (hAB : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ) (hA : ∀ y ∈ Y, A y ∈ Y) (hB : ∀ y ∈ Y, B y ∈ Y) (v : H) (hv : A v = v) :
    A (Y.starProjection v) = Y.starProjection v := by
  have hpY : Y.starProjection v ∈ Y := Submodule.starProjection_apply_mem Y v
  have hz : ∀ y ∈ Y, ⟪v - Y.starProjection v, y⟫_ℂ = 0 := fun y hy =>
    Submodule.inner_left_of_mem_orthogonal hy (Submodule.sub_starProjection_mem_orthogonal v)
  have hAz : ∀ y ∈ Y, ⟪A (v - Y.starProjection v), y⟫_ℂ = 0 := fun y hy => by
    rw [hAB]; exact hz _ (hB y hy)
  have e : A (Y.starProjection v) - Y.starProjection v =
      (v - Y.starProjection v) - A (v - Y.starProjection v) := by
    rw [map_sub, hv]; abel
  have h1 : A (Y.starProjection v) - Y.starProjection v ∈ Y := Y.sub_mem (hA _ hpY) hpY
  have h0 : ⟪A (Y.starProjection v) - Y.starProjection v, A (Y.starProjection v) - Y.starProjection v⟫_ℂ = 0 := by
    nth_rw 1 [e]
    rw [inner_sub_left, hz _ h1, hAz _ h1, sub_zero]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

private theorem integral_mem_fd (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] {α : Type*} [MeasurableSpace α] (m : Measure α)
    (f : α → H) (hf : ∀ a, f a ∈ Y) : ∫ a, f a ∂m ∈ Y := by
  by_cases hi : Integrable f m
  · have h := (Y.starProjection).integral_comp_comm hi
    have e : ∀ a, Y.starProjection (f a) = f a := fun a => Submodule.starProjection_eq_self_iff.2 (hf a)
    simp only [e] at h
    rw [h]
    exact Submodule.starProjection_apply_mem Y _
  · rw [integral_undef hi]
    exact Y.zero_mem

end Hilbert

section Forms

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]

private theorem cls_tr {φ ψ : cuspForms K n} (x : G1 K n)
    (h : ∀ y : G1 K n, (ψ : AdelicGLn.AdelicGL K n → ℂ) y =
      (φ : AdelicGLn.AdelicGL K n → ℂ) ((y * x : G1 K n) : AdelicGLn.AdelicGL K n)) :
    Dp.clsL μ ψ = rightRegularRep (Gam K n) μ x (Dp.clsL μ φ) := by
  have h1 := isContRep_cuspToL2 μ ψ
  have h2 := (isContRep_cuspToL2 μ φ).translate x
  have e : (fun y : G1 K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) y) =
      fun y => (φ : AdelicGLn.AdelicGL K n → ℂ) ((y * x : G1 K n) : AdelicGLn.AdelicGL K n) := funext h
  rw [e] at h1
  exact Lp.ext (h1.ae_eq_quotFun.trans h2.ae_eq_quotFun.symm)

private theorem mem_fixF' (W : Subgroup (FA K n)) (x : LL μ) :
    x ∈ fixF μ W ↔ ∀ u ∈ W, rightRegularRep (Gam K n) μ (fin1 u) x = x := by
  simp [fixF, rhoF, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem lev_max (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw n w)) (hU : Lev U) (u : FA K n)
    (hu : u ∈ levOn S U) : finEmb K n u ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) := by
  refine finEmb_mem_maxCompact ((AdelicGLn.mem_integralFiniteGL_iff_forall ..).2 fun v => ?_)
  have h : finAt v (finEmb K n u) ∈ if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion K) n := hu v
  have h2 : finAt v (finEmb K n u) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    by_cases hv : v ∈ S
    · rw [if_pos hv] at h; exact (hU v).2 h
    · rwa [if_neg hv] at h
  have e : finAt v (finEmb K n u) = AdelicGLn.finiteRestrictedEquiv K n u v := by
    show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n u)).2) v = _
    rw [prodEquiv_finEmb]
  rw [e] at h2
  exact h2

end Forms

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.vecEx :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (LL μ)), CuspIrr μ τ → ∀ (n : ι → ℕ) (q : ι → ℤ), (∀ i, ∃ v ∈ τ, C.Pi μ i (n i) (q i) v ≠ 0) → ∀ S : Finset (Pl K), SphOff μ τ S →
      ∃ (U : ∀ w : Pl K, Subgroup (Gw 2 w)) (φ : G1 K 2 → ℂ), Lev U ∧ φ ≠ 0 ∧ Rd τ φ ∧ (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧
        FixA C.κ₂ (C.p n q) φ ∧ FixF (levOn S U) φ := by
  intro K _ _ _ ι _ C μ _ τ hτ n q hn S hS
  haveI : T2Space (G1 K 2) := by
    set_option synthInstance.maxHeartbeats 100000 in
      infer_instance
  have hSum : IsSummand μ τ := ⟨hτ.le, hτ.closed, hτ.inv, hτ.ne, hτ.irr⟩
  obtain ⟨U, hU, hUne⟩ := UpperTheory.ConvolutionTheory.T.levelEx K 2 μ τ hSum S hS
  have hZne : τ ⊓ fixF μ (levOn S U) ≠ ⊥ := by
    rw [UpperTheory.ConvolutionTheory.C.fixLev K 2 μ S U, ← inf_assoc]
    exact hUne
  obtain ⟨hP, hPp, hPi, -⟩ := piLaws K ι C μ
  have hcomm : ∀ i a (u : FA K 2), Commute (fin1 u) (C.gl i a) := fun i a u =>
    MultiplicityOne.finProj_mul_archProj_comm u _
  obtain ⟨v, hvZ, hv0, hvP⟩ := occ K ι C μ τ hτ (τ ⊓ fixF μ (levOn S U)) Finset.univ n q inf_le_left hZne
    (fun i a x hx => ⟨hτ.inv _ _ hx.1, (mem_fixF' μ _ _).2 fun u hu => by
      rw [← UnitaryRep.map_mul_apply, (hcomm i a u).eq, UnitaryRep.map_mul_apply, (mem_fixF' μ _ _).1 hx.2 u hu]⟩)
    (fun i n' q' x hx => by
      obtain ⟨P, hPv, -, -, -, hc, hτP⟩ := hP i n' q'
      rw [← hPv]
      refine ⟨hτP τ hτ x hx.1, (mem_fixF' μ _ _).2 fun u hu => ?_⟩
      have h := DFunLike.congr_fun (hc (fin1 u) fun b => hcomm i b u).eq x
      simp only [ContinuousLinearMap.mul_apply] at h
      rw [← h, (mem_fixF' μ _ _).1 hx.2 u hu]) hn
  have hvτ : v ∈ τ := hvZ.1
  have hvF := (mem_fixF' μ _ _).1 hvZ.2
  have hforms := Dp.formsIrr K 2 μ τ hSum
  obtain ⟨Φ, hΦ, hne⟩ : ∃ Φ ∈ Dp.formsIn μ τ, ⟪Dp.clsL μ Φ, v⟫_ℂ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hcl : IsClosed {x : LL μ | ⟪x, v⟫_ℂ = 0} := isClosed_eq (by fun_prop) continuous_const
    have hsub : (((Dp.formsIn μ τ).map (Dp.clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) ⊆ {x : LL μ | ⟪x, v⟫_ℂ = 0} := by
      rintro _ ⟨φ, h, rfl⟩
      exact hcon φ h
    have hm : v ∈ closure (((Dp.formsIn μ τ).map (Dp.clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) := by
      rw [← Submodule.topologicalClosure_coe, hforms.2.2.2]
      exact hvτ
    exact hv0 (inner_self_eq_zero.1 (closure_minimal hsub hcl hm))
  let A : Submodule ℂ (AdelicGLn.AdelicGL K 2 → ℂ) := Submodule.span ℂ
    (Set.range fun k : (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)) =>
      GroundTheory.Automorphic.rightTranslate (k : AdelicGLn.AdelicGL K 2) (Φ : AdelicGLn.AdelicGL K 2 → ℂ))
  haveI hAfd : FiniteDimensional ℂ A := Φ.2.1.isKFinite
  have hAst : ∀ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)), ∀ f ∈ A, (fun g => f (g * k)) ∈ A := by
    intro k hk f hf
    have hle : A ≤ A.comap (LinearMap.funLeft ℂ ℂ fun g : AdelicGLn.AdelicGL K 2 => g * k) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨⟨k * k', mul_mem hk k'.2⟩, ?_⟩
      funext g
      simp [GroundTheory.Automorphic.rightTranslate, LinearMap.funLeft_apply, mul_assoc]
    exact hle hf
  let W : Submodule ℂ (cuspForms K 2) := Dp.formsIn μ τ ⊓ A.comap (cuspForms K 2).subtype
  haveI hWfd : FiniteDimensional ℂ W := by
    let f : W →ₗ[ℂ] A := ((cuspForms K 2).subtype ∘ₗ W.subtype).codRestrict A fun x => x.2.2
    exact FiniteDimensional.of_injective f fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : AdelicGLn.AdelicGL K 2 → ℂ)) h))
  let Y : Submodule ℂ (LL μ) := W.map (Dp.clsL μ)
  haveI hYfd : FiniteDimensional ℂ Y := inferInstance
  have hcen : ∀ ψ ∈ W, ψ ∈ centralCuspForms K 2 := fun ψ h => h.1.1
  have hYσ : ∀ (k : archCompact K 2), ∀ y ∈ Y, rightRegularRep (Gam K 2) μ (arc1 k) y ∈ Y := by
    rintro k _ ⟨ψ, hψ, rfl⟩
    refine ⟨(gkModuleCusp K 2).σ k ψ, ⟨hforms.1.σ k ψ hψ.1, hAst _ k.2 _ hψ.2⟩, ?_⟩
    exact cls_tr μ (φ := ψ) (ψ := (gkModuleCusp K 2).σ k ψ) (arc1 k)
      fun y => apply_mul_infEmb_of_mem (hcen ψ hψ) y k
  have hYf : ∀ u ∈ levOn S U, ∀ y ∈ Y, rightRegularRep (Gam K 2) μ (fin1 u) y ∈ Y := by
    rintro u hu _ ⟨ψ, hψ, rfl⟩
    have hm := lev_max S U hU u hu
    refine ⟨finRepCusp K 2 u ψ, ⟨hforms.1.τ u ψ hψ.1, hAst _ hm _ hψ.2⟩, ?_⟩
    refine cls_tr μ (fin1 u) fun y => ?_
    have e : ((fin1 u : G1 K 2) : AdelicGLn.AdelicGL K 2) = finEmb K 2 u := by
      rw [fin1, MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL hm)]
    show (ψ : AdelicGLn.AdelicGL K 2 → ℂ) (y * finEmb K 2 u) = (ψ : AdelicGLn.AdelicGL K 2 → ℂ) (y * (fin1 u : G1 K 2))
    rw [e]
  have hYP : ∀ i n' q', ∀ y ∈ Y, C.Pi μ i n' q' y ∈ Y := fun i n' q' y hy =>
    integral_mem_fd Y μK _ fun m => Y.smul_mem _ (hYσ _ y hy)
  have hy₀P : ∀ i, C.Pi μ i (n i) (q i) (Y.starProjection v) = Y.starProjection v := by
    intro i
    obtain ⟨P, hPv, hsa, -⟩ := hP i (n i) (q i)
    have hst : ∀ y ∈ Y, P y ∈ Y := fun y hy => by rw [hPv]; exact hYP _ _ _ y hy
    rw [← hPv]
    exact proj_fix Y P P (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa) hst hst v
      (by rw [hPv]; exact hvP i (Finset.mem_univ i))
  have hy₀F : ∀ u ∈ levOn S U, rightRegularRep (Gam K 2) μ (fin1 u) (Y.starProjection v) = Y.starProjection v :=
    fun u hu => proj_fix Y _ (rightRegularRep (Gam K 2) μ (fin1 u)⁻¹)
      (UnitaryRep.inner_map_left _ _) (hYf u hu)
      (fun y hy => by rw [← map_inv]; exact hYf _ (inv_mem hu) y hy) v (hvF u hu)
  obtain ⟨Φ₀, hΦ₀, hcls⟩ : Y.starProjection v ∈ Y := Submodule.starProjection_apply_mem Y v
  have hrep : IsContRep μ (Y.starProjection v) fun m : G1 K 2 => (Φ₀ : AdelicGLn.AdelicGL K 2 → ℂ) m := by
    rw [← hcls]
    exact isContRep_cuspToL2 μ Φ₀
  have hy₀τ : Y.starProjection v ∈ τ := by
    rw [← hcls]
    exact hΦ₀.1.2
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K 2 => fun m : G1 K 2 =>
      (Φ₀ : AdelicGLn.AdelicGL K 2 → ℂ) ((m * k : G1 K 2) : AdelicGLn.AdelicGL K 2))) := by
    refine Submodule.finiteDimensional_of_le
      (S₂ := A.map (LinearMap.funLeft ℂ ℂ fun m : G1 K 2 => (m : AdelicGLn.AdelicGL K 2))) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hAst _ k.2 _ hΦ₀.2, rfl⟩
  have hRd := (cuspIrr_kFinite_rep_eq_centralCuspForm μ τ hτ _ hrep.1 ⟨_, hy₀τ, hrep.2.2⟩ hfin).1
  obtain ⟨B, hB⟩ := hRd.decay 0
  refine ⟨U, _, hU, ?_, hRd, ⟨B, fun x => by simpa using hB x⟩,
    ((ptPi K ι C μ _ _ hrep.1 hrep.2.2).2 C.κ₂ (C.p n q) (hPi n q)).1 ((hPp n q _).2 hy₀P), fun u hu g => ?_⟩
  · intro h0
    have hz : Y.starProjection v = 0 := by
      rw [h0] at hrep
      exact Lp.ext (hrep.ae_eq_quotFun.trans (isContRep_zero (μ := μ)).ae_eq_quotFun.symm)
    have hΦA : (Φ : AdelicGLn.AdelicGL K 2 → ℂ) ∈ A := Submodule.subset_span ⟨1, by
      funext x
      simp [GroundTheory.Automorphic.rightTranslate]⟩
    have hΦW : Φ ∈ W := ⟨hΦ, hΦA⟩
    have hΦY : Dp.clsL μ Φ ∈ Y := Submodule.mem_map_of_mem hΦW
    have hin : ⟪Dp.clsL μ Φ, v - Y.starProjection v⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hΦY (Submodule.sub_starProjection_mem_orthogonal v)
    rw [hz, sub_zero] at hin
    exact hne hin
  · have h2 := hrep.translate (fin1 u)
    rw [hy₀F u hu] at h2
    exact congrFun (h2.unique hrep) g
end

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.lineEx :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ →
      ∀ (μ : Measure U4) (e : ι → U4 → ℂ) n q n' q' (x : ι → U4), Haar4 μ → ExtP μ e n q n' q' x →
      (∀ i, ∃ v ∈ τ₁, C.Pi μ₂ i (n i) (q i) v ≠ 0) → (∀ i, ∃ v ∈ τ₂, C.Pi μ₂ i (n' i) (q' i) v ≠ 0) →
      ∀ S : Finset (Pl K), SphOff μ₂ τ₁ S → SphOff μ₂ τ₂ S →
        ∃ (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)) (f : G1 K (2 + 2) → ℂ), Lev U ∧ f ≠ 0 ∧ IsSec τ₁ τ₂ f ∧ FixA (C.κ₄ μ) (C.e e) f ∧ FixF (levOn S U) f := by
  intro K _ _ _ ι _ C μ₂ _ τ₁ τ₂ hP μ e n q n' q' x hμ hE h₁ h₂ S hS₁ hS₂
  obtain ⟨U₁, φ₁, hU₁, hφ₁, hR₁, hB₁, hA₁, hF₁⟩ := vecEx K ι C μ₂ τ₁ hP.irr₁ n q h₁ S hS₁
  obtain ⟨U₂, φ₂, hU₂, hφ₂, hR₂, hB₂, hA₂, hF₂⟩ := vecEx K ι C μ₂ τ₂ hP.irr₂ n' q' h₂ S hS₂
  obtain ⟨-, -, hId, -⟩ := piLaws K ι C μ₂
  have hfd : ∀ (p : archCompact K 2 → ℂ) (V : ∀ w : Pl K, Subgroup (Gw 2 w)) (φ : G1 K 2 → ℂ), IdemA C.κ₂ p → Lev V → Continuous φ → FixA C.κ₂ p φ →
      FixF (levOn S V) φ → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K 2 => fun m => φ (m * k))) := by
    intro p V φ hp hV hc ha hf
    obtain ⟨hco, hle⟩ := (IwahoriBlocks.levLaws (K := K) 2 S).1 V hV
    obtain ⟨D, hD, -⟩ := typeOf K 2 C.κ₂ p hp (levOn S V) hle hco.2
    exact UpperTheory.finiteDimensional_span_maximalCompact_translates_of_fix D φ hc ((hD.fix φ hc).2 ⟨ha, hf⟩)
  obtain ⟨U, ρ, Ψ, c, hU, hρ, hρi, hΨ, hN, hΨA, hΨF, hc, hval⟩ := UpperTheory.exists_level_and_KTypeVector_for_leviInduction K ι C μ e n q n' q' x hμ hE S U₁ U₂ hU₁ hU₂
  obtain ⟨f, hfc, hfb, hfu, hfr, hfs, hform⟩ := UpperTheory.exists_cuspidal_section_from_levi_average μ₂ τ₁ τ₂ hP.irr₁ hP.irr₂ ρ hρ hρi Ψ hΨ hN φ₁ φ₂ hR₁.cont hR₂.cont hB₁ hB₂ hR₁.rep hR₂.rep
    (hfd _ U₁ φ₁ (hId n q) hU₁ hR₁.cont hA₁ hF₁) (hfd _ U₂ φ₂ (hId n' q') hU₂ hR₂.cont hA₂ hF₂)
  obtain ⟨hfixA, hfixF⟩ := UpperTheory.leviInducedSection_fixed_by_archIdempotent_and_level ρ hρ Ψ hΨ φ₁ φ₂ hR₁.cont hR₂.cont hB₁ hB₂ f hform
  obtain ⟨hIdem, -⟩ := lineVal K ι C μ₂ τ₁ τ₂ hP μ e n q n' q' x hμ hE
  obtain ⟨hco, hle⟩ := (IwahoriBlocks.levLaws (K := K) (2 + 2) S).1 U hU
  have fA := hfixA _ _ hIdem hΨA
  have fF := hfixF _ hle hΨF
  obtain ⟨D, hD, -⟩ := typeOf K (2 + 2) (C.κ₄ μ) (C.e e) hIdem (levOn S U) hle hco.2
  have hDf : D.Fix f := (hD.fix f hfc).2 ⟨fA, fF⟩
  refine ⟨U, f, hU, ?_, (secCrit μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ f hDf).2 ⟨hfc, hfb, hfu, hfr, hfs⟩, fA, fF⟩
  intro h0
  obtain ⟨m₁, hm₁⟩ := Function.ne_iff.1 hφ₁
  obtain ⟨m₂, hm₂⟩ := Function.ne_iff.1 hφ₂
  obtain ⟨-, -, -, -, -, -, hkA, -⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) (2 + 2)
  have hv := hform 0 m₁ m₂ 0 _ (hkA ((C.Φ (2 + 2)).symm x))
  rw [hval φ₁ φ₂ hR₁.cont hR₂.cont hA₁ hA₂ hF₁ hF₂ m₁ m₂, h0] at hv
  have : (c : ℂ) * φ₁ m₁ * φ₂ m₂ ≠ 0 := mul_ne_zero (mul_ne_zero (by exact_mod_cast hc.ne') hm₁) hm₂
  exact this hv.symm
