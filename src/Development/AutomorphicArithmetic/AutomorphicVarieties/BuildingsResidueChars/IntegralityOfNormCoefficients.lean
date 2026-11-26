module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PlaceMove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

@[expose] public section

attribute [-instance] Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Hi.IsCNL.toIsLocalRing
  GroundTheory.Heights₂.Heights.IsCohenMacaulayLocalRing.toIsLocalRing
  Formalism.L2.Pj.rulesCommRing
  UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoefficientsOfField
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralIffNormLeOne
open Polynomial

theorem UpperTheory.padicAlgCl_isIntegral_iff_norm_le_one :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l), IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ (1 : ℝ) := by
  intro l _ x
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hx
  have key : ‖x‖ ≤ (1 : ℝ) ↔ ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 :=
    spectralValue_le_one_iff hm
  rw [key]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact ((minpoly ℤ_[l] x).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsDiscreteValuationRingIntegralClosure
open Polynomial

private theorem isIntegral_of_spectralNorm_le_one (l : ℕ) [Fact l.Prime] (L : Type*) [Field L]
    [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L]
    [IsScalarTower ℤ_[l] ℚ_[l] L] (x : L) (hx : spectralNorm ℚ_[l] L x ≤ 1) :
    IsIntegral ℤ_[l] x := by
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).mp hx
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

private theorem isIntegral_or_isIntegral_inv (l : ℕ) [Fact l.Prime] (L : Type*) [Field L]
    [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L]
    [IsScalarTower ℤ_[l] ℚ_[l] L] (x : L) :
    IsIntegral ℤ_[l] x ∨ IsIntegral ℤ_[l] x⁻¹ := by
  by_cases hx : spectralNorm ℚ_[l] L x ≤ 1
  · exact Or.inl (isIntegral_of_spectralNorm_le_one l L x hx)
  · refine Or.inr (isIntegral_of_spectralNorm_le_one l L x⁻¹ ?_)
    have hx1 : 1 < spectralNorm ℚ_[l] L x := not_le.mp hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [spectralNorm_zero] at hx1
      exact absurd hx1 (by norm_num)
    have hmul : spectralNorm ℚ_[l] L x * spectralNorm ℚ_[l] L x⁻¹ = 1 := by
      have h := spectralAlgNorm_mul (K := ℚ_[l]) (L := L) x x⁻¹
      rw [mul_inv_cancel₀ hx0, spectralAlgNorm_one] at h
      exact h.symm
    have h0 : 0 ≤ spectralNorm ℚ_[l] L x⁻¹ := spectralNorm_nonneg _
    nlinarith

private theorem isDiscreteValuationRing_integralClosure (l : ℕ) [Fact l.Prime] (L : Type*) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L] [IsScalarTower ℤ_[l] ℚ_[l] L] :
    IsDiscreteValuationRing (integralClosure ℤ_[l] L) := by
  have hD : IsDedekindDomain (integralClosure ℤ_[l] L) :=
    integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] L
  have hF : IsFractionRing (integralClosure ℤ_[l] L) L :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] L
  have hV : ValuationRing (integralClosure ℤ_[l] L) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _ L]
    intro x
    rcases isIntegral_or_isIntegral_inv l L x with h | h
    · exact Or.inl ⟨⟨x, h⟩, rfl⟩
    · exact Or.inr ⟨⟨x⁻¹, h⟩, rfl⟩
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] L)) := by
    intro a b hab
    have h : algebraMap ℤ_[l] L a = algebraMap ℤ_[l] L b :=
      congrArg (fun z : integralClosure ℤ_[l] L => (z : L)) hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] L, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] L b]
      at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] L).injective h)
  have hnf : ¬ IsField (integralClosure ℤ_[l] L) := fun h =>
    IsDiscreteValuationRing.not_isField ℤ_[l] (isField_of_isIntegral_of_isField hinj h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[l] L) hnf).out 1 2).mpr hV

theorem UpperTheory.integralClosure_isDVR :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] ↥K], IsDiscreteValuationRing ↥(integralClosure ℤ_[l] ↥K) := by
  intro l _ K _
  exact isDiscreteValuationRing_integralClosure l K
end

theorem UpperTheory.Reformulated.B.CoefficientsOfField.coef_of_field :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] ↥K],
    ∃ (c : UpperTheory.V.HV.Coef l),
      ∀ x ∈ K,
        ‖x‖ ≤ (1 : ℝ) → x ∈ c.O := by
  intro l _ K _
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  have hd : IsDiscreteValuationRing (integralClosure ℤ_[l] K) := UpperTheory.integralClosure_isDVR K
  have hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K _
  refine ⟨⟨(integralClosure ℤ_[l] K).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x hx h1 => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (isIntegral_algHom_iff f hf).1 ((UpperTheory.padicAlgCl_isIntegral_iff_norm_le_one x).2 h1)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem coef_of_field {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O :=
  _root_.UpperTheory.Reformulated.B.CoefficientsOfField.coef_of_field K

private theorem mem_pow_iff {l : ℕ} [Fact l.Prime] (c : Coef l) : ∃ a : ℝ, 0 < a ∧ a < 1 ∧
    ∀ (n : ℕ) (x : c.O), x ∈ maximalIdeal c.O ^ n ↔ ‖(x : PadicAlgCl l)‖ ≤ a ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h1 : ‖(ϖ : PadicAlgCl l)‖ < 1 := (UpperTheory.V.Fr.sc_norm l c ϖ).2.1 hϖ.not_isUnit
  have h0 : 0 < ‖(ϖ : PadicAlgCl l)‖ := norm_pos_iff.2 fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨_, h0, h1, fun n x => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (UpperTheory.V.Fr.sc_norm l c y).1
  · intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    have hu : ‖((u : c.O) : PadicAlgCl l)‖ = 1 :=
      le_antisymm (UpperTheory.V.Fr.sc_norm l c u).1 (not_lt.1 fun h => (UpperTheory.V.Fr.sc_norm l c u).2.2 h u.isUnit)
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, hu, one_mul] at hx
    exact (pow_dvd_pow ϖ ((pow_le_pow_iff_right_of_lt_one₀ h0 h1).1 hx)).mul_left _

theorem UpperTheory.integrality_of_norm_coefficients :
    UpperTheory.V.Sd.S3.CoefEx := by
  intro l _
  refine ⟨fun c E hE => ?_, fun c Γ _ f => ?_⟩
  · obtain ⟨c', hc'⟩ := coef_of_field E
    obtain ⟨c₁, h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c c'
    exact ⟨c₁, h1, fun y hy h => h2 (hc' y hy h)⟩
  obtain ⟨a, h0, h1, ha⟩ := mem_pow_iff c
  constructor
  · intro hf
    rw [continuous_iff_continuousAt]
    intro g₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
    filter_upwards [(hf n).eventually_eq g₀] with g hg
    rw [dist_eq_norm, ← Subalgebra.coe_sub]
    exact lt_of_le_of_lt ((ha n _).1 (Ideal.Quotient.eq.1 hg)) hn
  · intro hf n
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g₀
    filter_upwards [Metric.tendsto_nhds.1 (hf.tendsto g₀) (a ^ n) (pow_pos h0 n)] with g hg
    rw [dist_eq_norm, ← Subalgebra.coe_sub] at hg
    exact Ideal.Quotient.eq.2 ((ha n _).2 hg.le)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermUpperBlock
open UpperTheory.V.Sd.Eis

open NumberField IsDedekindDomain GlobalTheory.CuspRep in
private theorem cont_nilM (F : Type) [Field F] [NumberField F] :
    Continuous (fun x : NA F => (nilM x : Matrix (Fin 2) (Fin 2) (Ad F))) := by
  refine continuous_matrix fun i j => ?_
  simp only [nilM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

open NumberField IsDedekindDomain GlobalTheory.CuspRep in
theorem UpperTheory.eisenstein_constantTerm_upperBlock :
    UpperTheory.V.Sd.Eis.BlockTop := by
  intro F _ _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact (Set.countable_range _).to_subtype
  · obtain ⟨C, hC, hx⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
    have hD : IsCompact (C ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :
        Set (Ad F)) := hC.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F)
    refine ⟨_, isCompact_univ_pi fun _ : BlockIx 2 1 => hD, fun x => ?_⟩
    choose k hk using hx
    exact ⟨fun p => algebraMap F (Ad F) (k (x p)), ⟨fun p => k (x p), rfl⟩, fun p _ => hk (x p)⟩
  · exact Units.continuous_iff.2 ⟨continuous_const.add (cont_nilM F), continuous_const.sub (cont_nilM F)⟩
  · intro x
    refine Units.ext ?_
    change 1 + nilM x = !![((1 : (Ad F)ˣ) : Ad F), x ⟨(0, 1), by decide⟩; 0, 1]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [nilM]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaActsTriviallyOnRootsOfUnity
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem no_tors (l : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (u : ℤ_[l]) (hu : u ^ l = 1) : u = 1 := by
  by_contra h1
  have hm : PadicInt.toZMod (u - 1) = 0 := by
    have := congrArg PadicInt.toZMod hu
    rw [map_pow, ZMod.pow_card, map_one] at this
    rw [map_sub, this, map_one, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  obtain ⟨b, hb⟩ := hm
  have hu' : u = 1 + l * b := by rw [← hb]; ring
  have hs : ∑ i ∈ Finset.range l, u ^ i = 0 := by
    have := mul_geom_sum u l
    rw [hu, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  have hd := odd_sq_dvd_geom_sum₂_sub (1 : ℤ_[l]) b (hl.out.odd_of_ne_two h2)
  simp only [one_pow, mul_one, ← hu', hs, zero_sub, dvd_neg] at hd
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hd' : (l : ℤ_[l]) * l ∣ l * 1 := by rwa [mul_one, ← sq]
  exact PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hl0).1 hd'))

theorem UpperTheory.inertia_acts_trivially_on_roots_of_unity :
    UpperTheory.V.Sd.S3.MuIne := by
  intro F Ω _ _ _ _ _ l hl h2 A hA s ⟨h1, a, h3⟩
  refine ⟨Rq.powIne F Ω l A hA s h1 _ (pow_pos hl.out.pos a)
    (Subgroup.topologicalClosure_minimal _ (UpperTheory.V.B1.decComm F Ω l A hA) (isClosed_Ine A) h3), ?_⟩
  have h4 : s ^ l ^ a ∈ (cycZ F Ω l).ker := by
    refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_singleton.preimage (continuous_cycZ F Ω l)) h3
    rw [Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  rw [MonoidHom.mem_ker, map_pow] at h4
  have : ∀ (b : ℕ) (u : ℤ_[l]), u ^ l ^ b = 1 → u = 1 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih => intro u hu; exact ih u (no_tors l h2 _ (by rw [← pow_mul, ← pow_succ, hu]))
  exact Units.ext (this a _ (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinSmoothContinuous
open UpperTheory.V.Sd.Eis
open NumberField Topology Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host UpperTheory.V

private theorem cont_map {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (a : ℕ) (f : R →+* S) (hf : Continuous f) :
    Continuous (fun g : GL (Fin a) R => GeneralLinearGroup.map f g) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hf
  · exact Units.continuous_coe_inv.matrix_map hf

private theorem cont_pInf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : Continuous (TR.pInf F) := by
  have h : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
        (continuous_apply w)
  exact h.comp continuous_fst

theorem UpperTheory.eisenstein_smooth_continuous :
    UpperTheory.V.Sd.Eis.SmCont := by
  intro F _ _ _ a φ hU
  have hy := cont_map a (TR.pInf F) (cont_pInf F)
  have hk := cont_map a (pFin F) continuous_snd
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  set k₀ := GeneralLinearGroup.map (pFin F) g₀ with hk₀
  have hy' : Continuous fun g : GA F a => TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (TR.Rinf F))).comp hy
  have hc : ContinuousAt (fun g : GA F a =>
      TR.chart φ.1 (finGL F a k₀) (TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val)) g₀ :=
    ContinuousAt.comp (f := fun g : GA F a => TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val)
      (TR.contDiffAt_chart φ.2 _ (TR.val_mem_invSet _)).continuousAt hy'.continuousAt
  refine hc.congr ?_
  have hk' : Continuous fun g : GA F a => k₀⁻¹ * GeneralLinearGroup.map (pFin F) g :=
    continuous_const.mul hk
  have hn : ∀ᶠ g : GA F a in 𝓝 g₀, TR.finRep F a (k₀⁻¹ * GeneralLinearGroup.map (pFin F) g) φ = φ := by
    refine (hU.preimage hk').mem_nhds ?_
    change TR.finRep F a (k₀⁻¹ * k₀) φ = φ
    rw [inv_mul_cancel, map_one]; rfl
  filter_upwards [hn] with g hg
  rw [TR.chart_val]
  have e := congrFun (congrArg Subtype.val hg) (finGL F a k₀ * TR.infGL F a (GeneralLinearGroup.map (TR.pInf F) g))
  rw [← e]
  change φ.1 (_ * finGL F a _) = _
  rw [← TR.infGL_comm, mul_assoc, ← map_mul, mul_inv_cancel_left, TR.infGL_mul_finGL]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PeriodicIntegralFundamentalDomainInvariant
open UpperTheory.V.Sd.Eis
open MeasureTheory Measure Pointwise

private theorem perMean_fin {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [Countable Γ] (hc : Cocpt Γ) (μ : Measure A) [μ.IsAddHaarMeasure]
    (D : Set A) (hD : IsAddFundamentalDomain Γ D μ) : μ D ≠ ⊤ := by
  obtain ⟨C, hC, hcov⟩ := hc
  have h1 : D ⊆ ⋃ g : Γ, ((g +ᵥ C) ∩ D) := by
    intro x hx
    obtain ⟨γ, hγ, h⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨x - γ, h, ?_⟩, hx⟩
    change γ + (x - γ) = x
    abel
  have h2 : μ D ≤ μ C := by
    rw [hD.measure_eq_tsum C]
    exact (measure_mono h1).trans (measure_iUnion_le _)
  exact ne_top_of_le_ne_top hC.measure_lt_top.ne h2

private theorem perMean_key {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [Countable Γ] (μ : Measure A) [μ.IsAddHaarMeasure]
    (D : Set A) (hD : IsAddFundamentalDomain Γ D μ) (hfin : μ D ≠ ⊤) (e : A ≃ᵐ A) (c : NNReal)
    (he : μ.map e = c • μ) (σ : Γ → Γ) (hσ : Function.Bijective σ) (hs : ∀ (g : Γ) x, e ((σ g : A) + x) = (g : A) + e x)
    (f : A → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) :
    ∫ x in D, f (e x) ∂μ = ∫ x in D, f x ∂μ := by
  have hq : QuasiMeasurePreserving e μ μ := ⟨e.measurable.aemeasurable, by rw [he]; exact Measure.smul_absolutelyContinuous⟩
  have hD' : IsAddFundamentalDomain Γ (e ⁻¹' D) μ := hD.preimage_of_equiv hq hσ (fun g x => hs g x)
  have hm : μ (e ⁻¹' D) = μ D := by
    have := hD'.measure_set_eq hD MeasurableSet.univ (fun g => by simp)
    simpa using this
  have h0 : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)
  have hc : (c : ENNReal) = 1 := by
    rw [← e.map_apply, he, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hm
    exact (ENNReal.mul_left_inj h0 hfin).1 (by rw [hm, one_mul])
  have hc' : c = 1 := by exact_mod_cast hc
  rw [hc', one_smul] at he
  have h1 : ∫ x in D, f (e x) ∂μ = ∫ x in e ⁻¹' D, f (e x) ∂μ := by
    refine hD.setIntegral_eq hD' (fun g x => ?_)
    obtain ⟨g', rfl⟩ := hσ.2 g
    change f (e ((σ g' : A) + x)) = _
    rw [hs, hf _ g'.2]
  rw [h1, ← setIntegral_map_equiv, he]

theorem UpperTheory.periodic_integral_fundamentalDomain_invariant :
    UpperTheory.V.Sd.Eis.PerMean := by
  intro A _ _ _ _ _ _ _ _ Γ _ hc μ _ D hD
  have hfin := perMean_fin Γ hc μ D hD
  refine ⟨hfin, fun f hf => ⟨fun hcont => ?_, fun y => ?_, fun e he => ?_⟩⟩
  · obtain ⟨C, hC, hcov⟩ := hc
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
    refine Measure.integrableOn_of_bounded hfin hcont.aestronglyMeasurable (M := M) (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨γ, hγ, h⟩ := hcov x
    have := hf γ hγ (x - γ)
    rw [add_sub_cancel] at this
    rw [this]
    exact hM _ h
  · refine perMean_key Γ μ D hD hfin (MeasurableEquiv.addRight y) 1 ?_ id Function.bijective_id ?_ f hf
    · rw [one_smul]
      exact map_add_right_eq_self μ y
    · intro g x
      exact add_assoc _ _ _
  · haveI : (μ.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ e
    refine perMean_key Γ μ D hD hfin e.toHomeomorph.toMeasurableEquiv _
      (Measure.isAddLeftInvariant_eq_smul (μ.map e) μ)
      (fun g => ⟨e.symm g, (he _).1 (by simpa using g.2)⟩) ⟨fun a b h => ?_, fun b => ⟨⟨e b, (he _).2 b.2⟩, ?_⟩⟩ ?_ f hf
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · exact Subtype.ext (e.symm_apply_apply _)
    · intro g x
      change e (e.symm g + x) = g + e x
      rw [map_add (f := _), e.apply_symm_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaUnramifiedOfKillsRootsOfUnity
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => power_bounds_of_between A (aux_one A hm hη) h i

private theorem inertia_fixes_prime_to_roots {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hA : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) {ζ : Ω} (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have hv := aux_one A hm hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have e : g ζ / ζ - 1 = (g ζ - ζ) / ζ := by field_simp
  have : g ζ / ζ = 1 := by
    refine root_of_unity_eq_one_of_close_residue A hm hA (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) ?_
    rw [e, map_div₀, hv, div_one]; exact hg.2 ζ hv.le
  exact (div_eq_one_iff_eq h0).1 this

private theorem open_kernel_killing_roots_of_unity {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) {C : Type} [Group C]
    (θ : G ℚ Ω →* C) (hk : KillsMu w θ) : IsOpen (θ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ w = 1}.Finite := by
    refine (nthRoots w (1 : Ω)).finite_toSet.subset fun ζ hζ => ?_
    exact (mem_nthRoots (Nat.pos_of_ne_zero hw)).2 hζ
  haveI : Finite {ζ : Ω | ζ ^ w = 1} := hfin
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}).fixingSubgroup) (fun g hg => ?_)
    (IntermediateField.fixingSubgroup_isOpen _)
  refine hk g fun ζ hζ => ?_
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ (IntermediateField.subset_adjoin _ _ hζ)

theorem UpperTheory.theta_unramified_of_kills_roots_of_unity :
    UpperTheory.V.Sd.S3.ThetaUnr := by
  intro Ω _ _ _ l hl w hw θ hθ hk
  have h1 : ∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker := fun A hA g hg =>
    hk g fun ζ hζ => inertia_fixes_prime_to_roots A hw.ne_zero (hA w (Finset.mem_singleton_self w)) hg hζ
  refine ⟨h1, fun F hF => ?_⟩
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  haveI : NeZero (l : Qbar l) := ⟨Nat.cast_ne_zero.2 hl.out.ne_zero⟩
  have hc : Nat.card (rootsOfUnity l (Qbar l)) = Nat.card (Multiplicative (ZMod l)) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity]; simp
  let e := mulEquivOfCyclicCardEq hc
  have hm : ∀ g, θ g ∈ rootsOfUnity l (Qbar l) := fun g => by
    rw [mem_rootsOfUnity]
    exact DFunLike.congr_fun hθ g
  have hker : (e.toMonoidHom.comp (θ.codRestrict _ hm)).ker = θ.ker := by
    ext g
    simp [MonoidHom.mem_ker, Subtype.ext_iff]
  have := hF (e.toMonoidHom.comp (θ.codRestrict _ hm))
  rw [hker] at this
  exact this (open_kernel_killing_roots_of_unity hw.ne_zero θ hk) h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ComplexConjugationsAreConjugate
theorem UpperTheory.complex_conjugations_are_conjugate :
    UpperTheory.V.Sd.S2.ConjCc := by
  intro Ω _ _ _ a b ha hb
  obtain ⟨j, hj⟩ := ha
  obtain ⟨j', hj'⟩ := hb
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j j'
    (Subsingleton.elim _ _)
  have h : ∀ x, j (σ.symm x) = j' x := fun x => by
    rw [← hσ]; rfl
  refine isConj_iff.2 ⟨σ, ?_⟩
  refine AlgEquiv.ext fun x => ?_
  apply j'.injective
  rw [hj', ← h, ← h]
  change j (σ.symm (σ (a (σ.symm x)))) = _
  rw [AlgEquiv.symm_apply_apply, hj]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinPeriodDerivative
open UpperTheory.V.Sd.Eis

private theorem UpperTheory.exists_bound_of_continuous_periodic_cocompact (A : Type) [AddCommGroup A] [TopologicalSpace A] (Γ : AddSubgroup A)
    (hC : Cocpt Γ) (g : A → ℝ → ℂ) (hg : Continuous (Function.uncurry g))
    (hgp : ∀ γ ∈ Γ, ∀ (x : A), g (γ + x) = g x) :
    ∃ M : ℝ, ∀ x : A, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖g x t‖ ≤ M := by
  obtain ⟨C, hCc, hCx⟩ := hC
  have hK : IsCompact (C ×ˢ Set.Icc (-1 : ℝ) 1) := hCc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨M, fun x t ht => ?_⟩
  obtain ⟨γ, hγ, hxγ⟩ := hCx x
  have h1 : g x = g (x - γ) := by
    have := hgp γ hγ (x - γ)
    rw [add_sub_cancel] at this
    exact this
  rw [h1]
  exact hM (x - γ, t) ⟨hxγ, ht⟩

theorem UpperTheory.eisenstein_period_derivative :
    UpperTheory.V.Sd.Eis.PerDeriv := by
  intro A _ _ _ _ _ _ Γ hC μ D hDt f f' hf hf' hfp hf'p hd
  obtain ⟨M, hM⟩ := UpperTheory.exists_bound_of_continuous_periodic_cocompact A Γ hC f' hf' hf'p
  obtain ⟨N, hN⟩ := UpperTheory.exists_bound_of_continuous_periodic_cocompact A Γ hC f hf hfp
  have hslice : ∀ (g : A → ℝ → ℂ), Continuous (Function.uncurry g) → ∀ t : ℝ, Continuous (fun x => g x t) :=
    fun g hg t => hg.comp (continuous_id.prodMk continuous_const)
  haveI hfin : MeasureTheory.IsFiniteMeasure (μ.restrict D) := MeasureTheory.isFiniteMeasure_restrict.2 hDt
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict D)
    (F := fun t x => f x t) (F' := fun t x => f' x t) (x₀ := (0 : ℝ)) (bound := fun _ => M)
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun t => (hslice f hf t).aestronglyMeasurable)
    (MeasureTheory.Measure.integrableOn_of_bounded (M := N) hDt (hslice f hf 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hN x 0 ⟨by norm_num, by norm_num⟩))
    (hslice f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht => hM x t ht)
    (MeasureTheory.integrable_const M)
    (Filter.Eventually.of_forall fun x t _ => hd x t)
  exact key.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinLieAlgebraAction
open UpperTheory.V.Sd.Eis

private theorem complex_linear_combination_eq_half_of_relations (a b c d e f x y z w κ : ℂ) (hc : c - Complex.I * d ≠ 0)
    (h1 : a * e + b * f = 1) (h2 : c * e + d * f = 0)
    (hp1 : x + w = 0) (hp2 : y - z = Complex.I * κ) (hp3 : x - w = Complex.I * (y + z))
    (hE : e * (c * x + d * y) + f * (c * z + d * w) = 0) :
    e * (a * x + b * y) + f * (a * z + b * w) = κ / 2 := by
  have hw : w = -x := by linear_combination hp1
  have hs : y + z = -2 * Complex.I * x := by
    linear_combination (norm := skip) (Complex.I) * hp3 + (Complex.I) * hp1
    ring_nf; simp only [Complex.I_sq]; ring_nf
  have hy : y = -Complex.I * x + Complex.I * κ / 2 := by
    linear_combination (1/2) * hs + (1/2) * hp2
  have hz : z = -Complex.I * x - Complex.I * κ / 2 := by
    linear_combination (1/2) * hs - (1/2) * hp2
  subst hw hy hz
  apply mul_left_cancel₀ hc
  linear_combination (norm := skip) (a - Complex.I * b) * hE
    + (-κ/2) * (Complex.I * d - c) * h1 + (-κ/2) * (a - Complex.I * b) * h2
  ring_nf; simp only [Complex.I_sq, Complex.I_pow_four]; ring_nf

theorem UpperTheory.eisenstein_lie_algebra_action :
    UpperTheory.V.Sd.Eis.LieAlg := by
  intro h p κ hp1 hp2 hp3 hE
  have hMN : (h : Matrix (Fin 2) (Fin 2) ℝ) * ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1 := congrFun (congrFun hMN 0) 0
  have e2 := congrFun (congrFun hMN 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e1 e2
  have hdet : (h : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hMN
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [Matrix.det_fin_two] at hdet
  have hc : ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) - Complex.I * ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp at hre him
    apply hdet
    rw [hre, him]; ring
  have hent : ∀ (k i j : Fin 2),
      (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.single (0 : Fin 2) k (1 : ℝ)
        * (h : Matrix (Fin 2) (Fin 2) ℝ)) i j
        = ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) k j := by
    intro k i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  simp only [hent, Fin.sum_univ_two, Complex.ofReal_mul] at hE ⊢
  have e1' : ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)
      + ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 1 := by
    exact_mod_cast e1
  have e2' : ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)
      + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 0 := by
    exact_mod_cast e2
  have := complex_linear_combination_eq_half_of_relations _ _ _ _ _ _ (p 0 0) (p 0 1) (p 1 0) (p 1 1) κ hc e1' e2' hp1 hp2 hp3
    (by linear_combination hE)
  linear_combination this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermOfPeriodMeanOfUpperBlock
open UpperTheory.V.Sd.Eis

open UpperTheory.V.Sd in
private theorem cb_aff_mul {R : Type} [CommRing R] (y y' : Rˣ) (x x' : R) :
    aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

open NumberField GlobalTheory.CuspRep UpperTheory.V.Sd in
private theorem cb_rat_aff (F : Type) [Field F] [NumberField F] (a : Fˣ) (y : F) :
    ratGL F 2 (aff a y) =
      aff (Units.map (algebraMap F (Ad F)).toMonoidHom a) (algebraMap F (Ad F) y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, ratGL]

open NumberField GlobalTheory.CuspRep in
private noncomputable def cb_scale (F : Type) [Field F] [NumberField F] (u : (Ad F)ˣ) : NA F ≃ₜ+ NA F where
  toFun x p := (u : Ad F) * x p
  invFun x p := ((u⁻¹ : (Ad F)ˣ) : Ad F) * x p
  left_inv x := funext fun p => Units.inv_mul_cancel_left u (x p)
  right_inv x := funext fun p => Units.mul_inv_cancel_left u (x p)
  map_add' x y := funext fun p => mul_add _ _ _
  continuous_toFun := continuous_pi fun p => continuous_const.mul (continuous_apply p)
  continuous_invFun := continuous_pi fun p => continuous_const.mul (continuous_apply p)

open NumberField GlobalTheory.CuspRep in
private theorem cb_mem (F : Type) [Field F] [NumberField F] (a : F) (x : NA F) (hx : x ∈ ratN F 2 1) :
    (fun p => algebraMap F (Ad F) a * x p) ∈ ratN F 2 1 := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => a * y p, funext fun p => map_mul (algebraMap F (Ad F)) _ _⟩

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock :
    UpperTheory.V.Sd.Eis.PerMean → UpperTheory.V.Sd.Eis.BlockTop → UpperTheory.V.Sd.Eis.CtBasic := by
  intro hM hB F _ _ _ _ μ _ D hF φ hc hl
  obtain ⟨i1, i2, i3, i4, hco, hu, hx⟩ := hB F
  have hper : ∀ (h : GA F 2), ∀ γ ∈ ratN F 2 1, ∀ x : NA F, φ (unip (γ + x) * h) = φ (unip x * h) := by
    rintro h _ ⟨y, rfl⟩ x
    rw [hx, hx x]
    refine Eq.trans ?_ (hl (aff 1 (y ⟨(0, 1), by decide⟩)) _)
    rw [← mul_assoc, cb_rat_aff, cb_aff_mul, map_one, one_mul, Units.val_one, one_mul, add_comm (x _)]
    rfl
  have key := fun g : GA F 2 =>
    (hM (NA F) (ratN F 2 1) hco μ D hF).2 (fun x => φ (unip x * g)) (hper g)
  refine ⟨fun g => (key g).1 (hc.comp (hu.mul continuous_const)), fun y g => ?_, fun a g => ?_⟩
  · unfold cterm
    refine Eq.trans ?_ ((key g).2.1 fun _ => y)
    refine congrArg (integral (μ.restrict D)) (funext fun x => ?_)
    rw [hx, hx, ← mul_assoc, cb_aff_mul, one_mul, Units.val_one, one_mul, add_comm y]
    rfl
  · let u : (Ad F)ˣ := Units.map (algebraMap F (Ad F)).toMonoidHom a
    unfold cterm
    refine Eq.trans ?_ ((key g).2.2 (cb_scale F u⁻¹) fun x => ⟨fun h => ?_, fun h => cb_mem F ((a⁻¹ : Fˣ) : F) x h⟩)
    · refine congrArg (integral (μ.restrict D)) (funext fun x => ?_)
      refine Eq.trans ?_ (hl (aff a 0) _)
      rw [hx, hx, cb_rat_aff, map_zero, ← mul_assoc, ← mul_assoc, cb_aff_mul, cb_aff_mul, one_mul, mul_one,
        mul_zero, zero_add, add_zero]
      change φ (aff u _ * g) = φ (aff u ((u : Ad F) * (((u⁻¹ : (Ad F)ˣ) : Ad F) * x _)) * g)
      rw [Units.mul_inv_cancel_left]
    · have h2 := cb_mem F (a : F) _ h
      have e : (fun p => algebraMap F (Ad F) (a : F) * cb_scale F u⁻¹ x p) = x :=
        funext fun p => Units.mul_inv_cancel_left u (x p)
      rwa [e] at h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermAutomorphy
open UpperTheory.V.Sd.Eis

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
private theorem ct_cont_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) :
    Continuous (TR.infGL F a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (TR.sInf F : TR.Rinf F → Ad F) := (TR.continuous_infEq F).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
private theorem ct_aff_add (F : Type) [Field F] [NumberField F] (y : F) (x : Ad F) :
    (aff 1 (algebraMap F (Ad F) y + x) : GA F 2) = ratGL F 2 (aff 1 y) * aff 1 x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aff, ratGL, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
private theorem ct_level (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a) (X : TR.Lie F a)
    (h : IsOpen {k | TR.finRep F a k φ = φ}) : IsOpen {k | TR.finRep F a k (TR.lie F a X φ) = TR.lie F a X φ} := by
  let S : TR.Sm F a → Subgroup (GL (Fin a) (Af F)) := fun ψ =>
    { carrier := {k | TR.finRep F a k ψ = ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  refine Subgroup.isOpen_mono (H₁ := S φ) (H₂ := S (TR.lie F a X φ)) (fun k hk => ?_) h
  have hk' : TR.rt F a (finGL F a k) φ = φ := hk
  have e := LinearMap.congr_fun (TR.lie_rt_fin X k) φ
  rw [Module.End.mul_apply, Module.End.mul_apply, hk'] at e
  exact e.symm

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.constant_term_automorphy :
    UpperTheory.V.Sd.Eis.SmCont → UpperTheory.V.Sd.Eis.PerMean → UpperTheory.V.Sd.Eis.PerDeriv → UpperTheory.V.Sd.Eis.BlockTop → UpperTheory.V.Sd.Eis.CtLie := by
  intro hS hM hD hB F _ _ _ _ _ μ _ D hF φ hl ho X
  have hl' : ∀ γ g, (TR.lie F 2 X φ).1 (ratGL F 2 γ * g) = (TR.lie F 2 X φ).1 g := by
    intro γ g
    have e : TR.chart φ.1 (ratGL F 2 γ * g) = TR.chart φ.1 g := by
      funext x
      simp only [TR.chart, mul_assoc, hl]
    simp only [TR.lie_apply, TR.lieD, e]
  have hc' : Continuous (TR.lie F 2 X φ).1 := hS F 2 _ (ct_level F 2 φ X ho)
  have hc : Continuous φ.1 := hS F 2 _ ho
  refine ⟨⟨hl', hc'⟩, fun c hcc hmul hder g => ?_⟩
  obtain ⟨i1, i2, i3, i4, hco, hu, hx⟩ := hB F
  have h0 : c 0 = 1 := by
    have := hmul 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hfin := (hM (NA F) (ratN F 2 1) hco μ D hF).1
  have hcont : Continuous fun p : NA F × ℝ => (unip p.1 : GA F 2) * (g * TR.infGL F 2 (c p.2)) :=
    (hu.comp continuous_fst).mul (continuous_const.mul ((ct_cont_infGL F 2).comp (hcc.comp continuous_snd)))
  have hper : ∀ ψ : GA F 2 → ℂ, (∀ γ g, ψ (ratGL F 2 γ * g) = ψ g) → ∀ γ ∈ ratN F 2 1, ∀ (x : NA F) (h : GA F 2),
      ψ (unip (γ + x) * h) = ψ (unip x * h) := by
    rintro ψ hψ _ ⟨y, rfl⟩ x h
    rw [hx, hx x]
    refine Eq.trans ?_ (hψ (aff 1 (y ⟨(0, 1), by decide⟩)) _)
    rw [← mul_assoc, ← ct_aff_add]
    rfl
  have key := hD (NA F) (ratN F 2 1) hco μ D hfin
    (fun x t => φ.1 (unip x * (g * TR.infGL F 2 (c t))))
    (fun x t => (TR.lie F 2 X φ).1 (unip x * (g * TR.infGL F 2 (c t))))
    (hc.comp hcont) (hc'.comp hcont)
    (fun γ hγ x => funext fun t => hper _ hl γ hγ x _)
    (fun γ hγ x => funext fun t => hper _ hl' γ hγ x _)
    (fun x t => by
      have h1 := TR.hasDerivAt_curve φ (unip x * (g * TR.infGL F 2 (c t))) c X h0 hder
      have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
      have h3 := HasDerivAt.scomp_of_eq t h1 h2 (sub_self t).symm
      rw [one_smul] at h3
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp_apply, mul_assoc, ← map_mul, ← hmul, add_sub_cancel])
  simpa only [cterm, h0, map_one, mul_one] using key
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricSquareMixedCharpoly
open Polynomial Matrix

namespace UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly

variable {k : Type} [Field k]

private def blk (A B : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 4) (Fin 4) k :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]

private def ant (A B : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1; B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0]

private def Pm (α β : k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, α, 0, α; β, 0, -β, 0; 0, -1, 0, 1; 1, 0, 1, 0]

private def Qm (α β : k) : Matrix (Fin 4) (Fin 4) k :=
  (2 : k)⁻¹ • !![0, β⁻¹, 0, 1; α⁻¹, 0, -1, 0; 0, -β⁻¹, 0, 1; α⁻¹, 0, 1, 0]

private lemma PQ (h2 : (2 : k) ≠ 0) {α β : k} (ha : α ≠ 0) (hb : β ≠ 0) : Pm α β * Qm α β = 1 := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp [h2, ha, hb] <;> ring

private lemma cp_conj (h2 : (2 : k) ≠ 0) {α β : k} (ha : α ≠ 0) (hb : β ≠ 0) (M N : Matrix (Fin 4) (Fin 4) k)
    (h : Pm α β * M = N * Pm α β) : M.charpoly = N.charpoly := by
  have h1 := PQ h2 ha hb
  have h3 : Qm α β * Pm α β = 1 := mul_eq_one_comm.mp h1
  have : M = Qm α β * (N * Pm α β) := by rw [← h, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [this, Matrix.charpoly_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

private lemma P_mix (h2 : (2 : k) ≠ 0) (α β : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) :
    Pm (α : k) β * mix (β / α) A B = blk A B * Pm (α : k) β := by
  have ha := α.ne_zero
  have hb := β.ne_zero
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [Pm, mix, blk, Matrix.mul_apply, Fin.sum_univ_four, Units.val_div_eq_div_val] <;>
    field_simp [h2, ha, hb] <;> ring

private lemma blk_P (α β : k) (A B : Matrix (Fin 2) (Fin 2) k) :
    blk A B * Pm α β * Matrix.diagonal ![β, -α, -β, α] =
      ant (A * Matrix.diagonal ![α ^ 2, β ^ 2]) B * Pm α β := by
  ext i j : 1
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [Pm, ant, blk, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private lemma cp_blk (A B : Matrix (Fin 2) (Fin 2) k) : (blk A B).charpoly = A.charpoly * B.charpoly := by
  simp only [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Matrix.charmatrix_apply]
  norm_num [blk, Fin.succAbove, Fin.lt_def, Fin.ext_iff, Matrix.diagonal_apply]
  ring

private lemma cp_ant (A B : Matrix (Fin 2) (Fin 2) k) : (ant A B).charpoly = (A * B).charpoly.comp (X ^ 2) := by
  simp only [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Matrix.charmatrix_apply]
  norm_num [ant, Fin.succAbove, Fin.lt_def, Fin.ext_iff, Matrix.diagonal_apply, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

end UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly

open UpperTheory.V.Sd.S2 UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly in
theorem UpperTheory.symmetric_square_mixed_charpoly :
    UpperTheory.V.Sd.S2.MixCp := by
  intro k Γ₀ Γ _ _ _ j t α β ρ R H s hs
  have hN : j.range.Normal := Subgroup.normal_of_index_eq_two H.index
  have hc : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := fun h => by
    have := hN.conj_mem' (j h) ⟨h, rfl⟩ t
    exact this
  have hm : ∀ a b : Γ, a ∉ j.range → b ∉ j.range → a * b ∈ j.range := fun a b ha hb =>
    (Subgroup.mul_mem_iff_of_index_two H.index).mpr (by simp [ha, hb])
  have ht' : t⁻¹ ∉ j.range := fun h => H.nmem (inv_mem_iff.mp h)
  refine ⟨fun g g' hg => ?_, fun g hg => ?_⟩
  · obtain ⟨h, hh⟩ := hm _ _ ht' hs
    obtain ⟨g'', hg''⟩ := hc g
    have e : g' = h⁻¹ * g'' * h := H.inj (by
      rw [map_mul, map_mul, map_inv, hh, hg'', hg]; group)
    rw [H.on g g'' hg'', cp_conj H.two α.ne_zero β.ne_zero _ _ (P_mix H.two α β _ _), cp_blk, e]
    congr 1
    rw [map_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  · obtain ⟨h, hh⟩ := hm _ _ hs ht'
    obtain ⟨h', hh'⟩ := hc h
    obtain ⟨u, hu⟩ := hm _ _ H.nmem H.nmem
    have e : g = h * u * h' := H.inj (by
      rw [map_mul, map_mul, hh', hu, hh, hg]; group)
    have es : s = j h * t := by rw [hh]; group
    have key : Pm (α : k) β * (R s : Matrix (Fin 4) (Fin 4) k) =
        ant ((ρ h : Matrix (Fin 2) (Fin 2) k) * Matrix.diagonal ![(α : k) ^ 2, (β : k) ^ 2]) (ρ h') * Pm (α : k) β := by
      rw [es, map_mul, Units.val_mul, H.on h h' hh', H.off, ← Matrix.mul_assoc, P_mix H.two, blk_P]
    rw [cp_conj H.two α.ne_zero β.ne_zero _ _ key, cp_ant, e, map_mul, map_mul, Units.val_mul, Units.val_mul, H.sq u hu]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinCentralLieAction
open UpperTheory.V.Sd.Eis

theorem UpperTheory.eisenstein_central_lie_action :
    UpperTheory.V.Sd.Eis.CentLie :=
  fun F _ _ _ _ _ ω hω φ hφ v => UpperTheory.V.Sd.Hm.trzero F ω hω φ hφ.cent v
end
