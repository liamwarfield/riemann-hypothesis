module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinQ

section Gen

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem coe_eq_algebraMap (z : K) : (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z := by
  simp [HeightOneSpectrum.algebraMap_adicCompletion]

theorem valued_algebraMap (z : K) :
    Valued.v (algebraMap K (v.adicCompletion K) z) = v.valuation K z := by
  rw [← coe_eq_algebraMap]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z

end Gen

theorem pOf_prime (v : Pl) : (pOf v).Prime := by
  have pOf_eq_prime (u : Pl) : pOf u = RationalSymbol.prime u := by
    show Ideal.absNorm u.asIdeal = RationalSymbol.prime u
    rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
    have h : ((RationalSymbol.prime u : ℕ) : 𝓞 ℚ) =
        algebraMap ℤ (𝓞 ℚ) ((RationalSymbol.prime u : ℕ) : ℤ) := by simp
    rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
    simp
  rw [pOf_eq_prime]
  exact Fact.out

theorem coe_uniformizer (v : Pl) :
    ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v) = ((pOf v : ℕ) : Qv v) := by
  have pOf_eq_prime (u : Pl) : pOf u = RationalSymbol.prime u := by
    show Ideal.absNorm u.asIdeal = RationalSymbol.prime u
    rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
    have h : ((RationalSymbol.prime u : ℕ) : 𝓞 ℚ) =
        algebraMap ℤ (𝓞 ℚ) ((RationalSymbol.prime u : ℕ) : ℤ) := by simp
    rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
    simp
  rw [pOf_eq_prime, DirichletHecke.uniformizer, IdeleGroup.coe_finiteProj_diagonal,
    RationalSymbol.coe_primeRat]
  rw [coe_eq_algebraMap, map_natCast]

theorem ord_pOf (v : Pl) : ord ((pOf v : ℕ) : Qv v) = 1 := by
  rw [← coe_uniformizer]
  have h1 : Valued.v ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v) = WithZero.exp (-1) :=
    DirichletHecke.valued_uniformizer v
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord (K := ℚ) (v := v)
    (x := ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v)) (Units.ne_zero _)
  have h3 := WithZero.exp_injective (h2.symm.trans h1)
  omega

theorem residueCard_Qv (v : Pl) : residueCard (Qv v) = pOf v :=
  residueCard_adicCompletion

theorem differentIdeal_rat : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal (K := ℚ) (𝒪 := 𝓞 ℚ),
    Rat.numberField_discr]
  rfl

theorem isStd_local (v : Pl) : IsStd (localAdelicChar ℚ v) := by
  refine ⟨continuous_localAdelicChar v, localAdelicChar_ne_one v, ?_⟩
  rw [addCharConductor_localAdelicChar, differentExp, differentIdeal_rat, FractionalIdeal.coeIdeal_top,
    FractionalIdeal.count_one, neg_zero]

theorem isUnit1_localChar (c : HeckeCharacter ℚ) (v : Pl) : IsUnit1 (localChar c v) :=
  ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c v, fun x => by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _⟩

theorem pOf_injective : Function.Injective pOf := by
  have pOf_eq_prime (u : Pl) : pOf u = RationalSymbol.prime u := by
    show Ideal.absNorm u.asIdeal = RationalSymbol.prime u
    rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
    have h : ((RationalSymbol.prime u : ℕ) : 𝓞 ℚ) =
        algebraMap ℤ (𝓞 ℚ) ((RationalSymbol.prime u : ℕ) : ℤ) := by simp
    rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
    simp
  intro v w h
  rw [pOf_eq_prime, pOf_eq_prime] at h
  exact HeightOneSpectrum.ext (by rw [DirichletHecke.asIdeal_eq_span v, DirichletHecke.asIdeal_eq_span w, h])

theorem pOf_surjective (p : ℕ) (hp : p.Prime) : ∃ v, pOf v = p :=
  ⟨RationalSymbol.placeOf ⟨p, hp⟩, by
    have pOf_eq_prime (u : Pl) : pOf u = RationalSymbol.prime u := by
      show Ideal.absNorm u.asIdeal = RationalSymbol.prime u
      rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
      have h : ((RationalSymbol.prime u : ℕ) : 𝓞 ℚ) =
          algebraMap ℤ (𝓞 ℚ) ((RationalSymbol.prime u : ℕ) : ℤ) := by simp
      rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
      simp
    rw [pOf_eq_prime]; exact RationalSymbol.prime_placeOf ⟨p, hp⟩⟩

theorem natCast_mem_asIdeal (v : Pl) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ pOf v ∣ n := by
  have pOf_eq_prime (u : Pl) : pOf u = RationalSymbol.prime u := by
    show Ideal.absNorm u.asIdeal = RationalSymbol.prime u
    rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
    have h : ((RationalSymbol.prime u : ℕ) : 𝓞 ℚ) =
        algebraMap ℤ (𝓞 ℚ) ((RationalSymbol.prime u : ℕ) : ℤ) := by simp
    rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
    simp
  rw [DirichletHecke.asIdeal_eq_span, Ideal.mem_span_singleton, pOf_eq_prime,
    ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast, map_natCast, Int.natCast_dvd_natCast]

theorem ord_natCast_of_not_dvd (v : Pl) {m : ℕ} (h : ¬ pOf v ∣ m) : ord ((m : ℕ) : Qv v) = 0 := by
  have hm : m ≠ 0 := by
    rintro rfl
    simp at h
  have e : Valued.v ((m : ℕ) : Qv v) = v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) := by
    rw [← valued_algebraMap, map_natCast (algebraMap (𝓞 ℚ) ℚ)]
    exact congrArg _ (map_natCast _ m).symm
  have h0 : ((m : ℕ) : Qv v) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [← valued_eq_one_iff_ord h0, e,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff,
    natCast_mem_asIdeal]
  exact h

theorem ord_pow_natCast (v : Pl) (p a : ℕ) (hp : p ≠ 0) :
    ord (((p : ℕ) : Qv v) ^ a) = a * ord ((p : ℕ) : Qv v) := by
  have h0 : ((p : ℕ) : Qv v) ≠ 0 := Nat.cast_ne_zero.2 hp
  induction a with
  | zero => simp [ord]
  | succ n ih =>
    rw [pow_succ, ord_mul (pow_ne_zero _ h0) h0, ih]
    push_cast
    ring

theorem ord_natCast (v : Pl) (n : ℕ) (hn : n ≠ 0) :
    ord ((n : ℕ) : Qv v) = n.factorization (pOf v) := by
  have hp := pOf_prime v
  have hc : ordCompl[pOf v] n ≠ 0 := (Nat.ordCompl_pos _ hn).ne'
  have h0 : ((ordCompl[pOf v] n : ℕ) : Qv v) ≠ 0 := Nat.cast_ne_zero.2 hc
  have h1 : ((pOf v : ℕ) : Qv v) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n (pOf v)]
  rw [Nat.cast_mul, Nat.cast_pow, ord_mul (pow_ne_zero _ h1) h0, ord_pow_natCast v _ _ hp.ne_zero,
    ord_pOf, ord_natCast_of_not_dvd v (Nat.not_dvd_ordCompl hp hn)]
  simp

theorem finite_not_integral (g : G2) : {v : Pl | finAt v g ∉ integralGL (Qv v) 2}.Finite :=
  Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL ℚ 2 g)

theorem adelic_GL2_ext_of_local_components (g g' : G2) (h : ∀ v, finAt v g = finAt v g') (h' : ∀ w, infAt w g = infAt w g') : g = g' :=
  GroundTheory.Automorphic.Reduction.adelicGL_ext h' h

def ofFinSupp (S : Finset Pl) (f : ∀ v : Pl, GL (Fin 2) (Qv v)) (hf : ∀ v ∉ S, f v = 1) : G2 :=
  (AdelicGLn.restrictedProductEquiv ℚ 2).symm (1, ⟨f, by
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra hvS
    exact hv (by rw [hf v hvS]; exact one_mem _)⟩)

theorem finAt_ofFinSupp (S : Finset Pl) (f : ∀ v : Pl, GL (Fin 2) (Qv v)) (hf : ∀ v ∉ S, f v = 1) (v : Pl) :
    finAt v (ofFinSupp S f hf) = f v := by
  simp [finAt, ofFinSupp]

theorem infAt_ofFinSupp (S : Finset Pl) (f : ∀ v : Pl, GL (Fin 2) (Qv v)) (hf : ∀ v ∉ S, f v = 1)
    (w : InfinitePlace ℚ) : infAt w (ofFinSupp S f hf) = 1 := by
  simp [infAt, ofFinSupp]

theorem exists_isLoc2 (v : Pl) (x : GL (Fin 2) (Qv v)) : ∃ h, IsLoc2 v x h := by
  let f : ∀ u : Pl, GL (Fin 2) (Qv u) := fun u => if e : u = v then e ▸ x else 1
  have hf : ∀ u ∉ ({v} : Finset Pl), f u = 1 := fun u hu => dif_neg (by simpa using hu)
  refine ⟨ofFinSupp {v} f hf, ?_, fun u hu => ?_, fun w => infAt_ofFinSupp _ _ _ w⟩
  · rw [finAt_ofFinSupp]
    exact dif_pos rfl
  · rw [finAt_ofFinSupp]
    exact dif_neg hu

theorem exists_isUn (S : Finset Pl) (x : ∀ v : S, Qv v.1) : ∃ h, IsUn S x h := by
  let f : ∀ u : Pl, GL (Fin 2) (Qv u) := fun u => if e : u ∈ S then uni2 (x ⟨u, e⟩) else 1
  have hf : ∀ u ∉ S, f u = 1 := fun u hu => dif_neg hu
  refine ⟨ofFinSupp S f hf, fun v => ?_, fun u hu => ?_, fun w => infAt_ofFinSupp _ _ _ w⟩
  · rw [finAt_ofFinSupp]
    exact dif_pos v.2
  · rw [finAt_ofFinSupp]
    exact hf u hu

instance compactSpace_integralGL (v : Pl) : CompactSpace (integralGL (Qv v) 2) :=
  isCompact_iff_compactSpace.1 (GLnLocal.isCompact_integralGL (Qv v) 2)

theorem exists_isK : ∃ m, IsK m := by
  refine ⟨fun v => Measure.haarMeasure ⊤, fun v => ⟨inferInstance, ⟨?_⟩⟩⟩
  exact Measure.haarMeasure_self

theorem isLoc2_uni (v : Pl) (x : Qv v) : IsLoc2 v (uni2 x) (uni2 (finitePlaceIncl v x)) := by
  refine ⟨?_, fun u hu => ?_, fun w => ?_⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni2, finitePlaceIncl_apply] <;> rfl
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni2, finitePlaceIncl_apply, finiteAdeleSingleAdd_apply_of_ne hu] <;> rfl
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni2, finitePlaceIncl_apply] <;> rfl

theorem isLoc2_dg (v : Pl) (a d : (Qv v)ˣ) :
    IsLoc2 v (dg2 a d) (dg2 (IdeleGroup.finiteEmbedding v a) (IdeleGroup.finiteEmbedding v d)) := by
  refine ⟨?_, fun u hu => ?_, fun w => ?_⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> rfl
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2, IdeleGroup.finiteAdeleSingle_apply_of_ne hu] <;> rfl
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> rfl

theorem exists_local_data (v : Pl) (x : Qv v) (a d : (Qv v)ˣ) :
    ∃ (x' : 𝔸[ℚ]) (a' d' : Jd), IsLoc2 v (uni2 x) (uni2 x') ∧ IsLoc2 v (dg2 a d) (dg2 a' d') ∧
      adelicChar ℚ x' = localAdelicChar ℚ v x ∧ (a = d → a' = d') ∧
      ∀ c : HeckeCharacter ℚ, (c.toIdele a' : ℂ) = localChar c v a ∧ (c.toIdele d' : ℂ) = localChar c v d :=
  ⟨finitePlaceIncl v x, IdeleGroup.finiteEmbedding v a, IdeleGroup.finiteEmbedding v d, isLoc2_uni v x,
    isLoc2_dg v a d, rfl, fun h => by rw [h], fun _ => ⟨rfl, rfl⟩⟩

theorem b0 : B0 :=
  ⟨fun v => ⟨isStd_local v, residueCard_Qv v, pOf_prime v, ord_pOf v, ord_natCast v, exists_isLoc2 v,
      fun c => isUnit1_localChar c v⟩,
    pOf_injective, pOf_surjective, adelic_GL2_ext_of_local_components, exists_isUn, exists_isK, finite_not_integral, exists_local_data⟩

end GlobalTheory.CompanionTheory.RankinQ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFactsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_rankin_selberg_basic_facts : Ad3.R.B0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinQ.b0 | exact GlobalTheory.CompanionTheory.RankinQ.b0 | (intros; apply GlobalTheory.CompanionTheory.RankinQ.b0 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBound
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.EisTerm

theorem flat_norm_le_height_rpow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (K : Subgroup (G2 σ Y))
    (a : G2 σ Y → ℝ) (hK : IsCompact (K : Set (G2 σ Y))) (hH : IsHgt K a) (ha : ∀ x, 0 < a x)
    (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ C : ℝ, ∀ (s : ℂ) (x : G2 σ Y), ‖flat a f s₁ s x‖ ≤ C * a x ^ (s.re + (n : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun s x => ?_⟩
  obtain ⟨p, t, hp, k, hk, rfl⟩ := hH.iwa x
  have hpos := ha (p * k)
  have hval := hH.val p t hp k hk
  have hlaw := hf.law p t k hp
  have hfk : ‖f (p * k)‖ = a (p * k) ^ (s₁.re + (n : ℝ) / 2) * ‖f k‖ := by
    have h1 : ‖(χ (Matrix.GeneralLinearGroup.det t) : ℂ)‖ = 1 := by
      first
        | exact Circle.norm_coe _
        | exact Circle.abs_coe _
        | simp
        | exact mem_sphere_zero_iff_norm.mp (χ (Matrix.GeneralLinearGroup.det t)).2
    rw [hlaw, ← hval, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, h1, one_mul]
    congr 2
    simp
  have e1 : a (p * k) ^ (s.re + (n : ℝ) / 2) =
      a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2) := by
    rw [← Real.rpow_add hpos]
    congr 1
    rw [Complex.sub_re]
    ring
  show ‖((a (p * k) : ℝ) : ℂ) ^ (s - s₁) * f (p * k)‖ ≤ _
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hfk, e1]
  have h0 : 0 ≤ a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hpos.le _) (Real.rpow_nonneg hpos.le _)
  calc a (p * k) ^ ((s - s₁).re) * (a (p * k) ^ (s₁.re + (n : ℝ) / 2) * ‖f k‖)
      = (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) * ‖f k‖ := by ring
    _ ≤ (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) * C :=
      mul_le_mul_of_nonneg_left (hC k hk) h0
    _ = C * (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) := by ring

end GlobalTheory.CompanionTheory.EisTerm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_section_growth_bound : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsCompact (K : Set (G2 σ Y)) → IsHgt K a → (∀ x, 0 < a x) → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ C : ℝ, ∀ (s : ℂ) (x : G2 σ Y), ‖flat a f s₁ s x‖ ≤ C * a x ^ (s.re + (n : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow | exact GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow | (intros; apply GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExists
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CompanionTheory.LieCurve

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

def expUnit (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) : GL (Fin a) (Cinf E) where
  val := NormedSpace.exp (t • M)
  inv := NormedSpace.exp (-(t • M))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • M)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • M)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem expUnit_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    (expUnit E a M t).val = NormedSpace.exp (t • M) := rfl

theorem expUnit_inv_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    ((expUnit E a M t)⁻¹).val = NormedSpace.exp ((-t) • M) := by
  change NormedSpace.exp (-(t • M)) = _
  rw [neg_smul]

theorem hasDerivAt_exp (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • M)) (NormedSpace.exp (t • M) * M) t := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) M t

theorem continuous_exp_smul (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    Continuous fun t : ℝ => NormedSpace.exp (t • M) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp E a M t).continuousAt

theorem continuous_expUnit (M : Matrix (Fin a) (Fin a) (Cinf E)) : Continuous (expUnit E a M) := by
  refine Units.continuous_iff.2 ⟨continuous_exp_smul E a M, ?_⟩
  exact ((continuous_exp_smul E a M).comp continuous_neg).congr fun t => (expUnit_inv_val E a M t).symm

theorem expUnit_zero (M : Matrix (Fin a) (Fin a) (Cinf E)) : expUnit E a M 0 = 1 := by
  ext1
  rw [expUnit_val, zero_smul, NormedSpace.exp_zero]
  rfl

theorem expUnit_add (M : Matrix (Fin a) (Fin a) (Cinf E)) (s t : ℝ) :
    expUnit E a M (s + t) = expUnit E a M s * expUnit E a M t := by
  ext1
  rw [Units.val_mul, expUnit_val, expUnit_val, expUnit_val, add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl M).smul_left s).smul_right t)]

theorem expUnit_mem_unitary (M : Matrix (Fin a) (Fin a) (Cinf E)) (h : Mᴴ = -M) (t : ℝ) :
    (expUnit E a M t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := by
  have e : star (NormedSpace.exp (t • M)) = NormedSpace.exp (-(t • M)) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, h]
    simp
  rw [Matrix.mem_unitaryGroup_iff, expUnit_val, e]
  exact (expUnit E a M t).val_inv

def toLieL : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.of.symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem toLieL_apply (M : Matrix (Fin a) (Fin a) (Cinf E)) : toLieL E a M = Matrix.of.symm M := rfl

theorem hasDerivAt_toL (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    HasDerivAt (fun t : ℝ => toL (expUnit E a M t).val) (Matrix.of.symm M) 0 := by
  have h := (toLieL E a).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp E a M 0)
  have e : toLieL E a (NormedSpace.exp ((0 : ℝ) • M) * M) = Matrix.of.symm M := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]; rfl
  exact h.congr_deriv e

end

theorem exists_curve (E : Type) [Field E] [NumberField E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧
      HasDerivAt (fun t => toL (c t).val) X 0 ∧
      ((Matrix.of X)ᴴ = -(Matrix.of X) → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) :=
  ⟨expUnit E a (Matrix.of X), continuous_expUnit E a _, expUnit_zero E a _, expUnit_add E a _,
    hasDerivAt_toL E a _, fun h t => expUnit_mem_unitary E a _ h t⟩

end GlobalTheory.CompanionTheory.LieCurve
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExistsStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_parameter_subgroup_exists : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a), ∃ c : ℝ → GL (Fin a) (Cinf E), Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => toL (c t).val) X 0 ∧ ((Matrix.of X)ᴴ = -(Matrix.of X) → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  first | exact @GlobalTheory.CompanionTheory.LieCurve.exists_curve | exact GlobalTheory.CompanionTheory.LieCurve.exists_curve | (intros; apply GlobalTheory.CompanionTheory.LieCurve.exists_curve <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitaryIrreducibleRep
open Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.admitted

theorem isAdmissible_of_unitary_irreducible : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    PositivityTheory.Tls2.Iua.AdmG G → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn G σ → Formalism.MainNotions.S.IsIrredOn G σ →
    GlobalTheory.LinRed.IsAdmOn G σ := by
  intro n G hG hA H _ _ _ σ hσ hirr
  refine ⟨hσ.1, hσ.2.2, fun k hk v => hσ.2.1 k hk.1 v, ?_⟩
  intro S hfd hS _
  haveI := hfd
  let b := Module.finBasis ℂ S
  choose Y hYfd _ hvY hY using fun i => hA H σ hσ hirr S hS (b i) (b i).2
  haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYfd
  have hsup : FiniteDimensional ℂ (⨆ i, Y i : Submodule ℂ H) := Submodule.finiteDimensional_iSup Y
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Y i) (sSup_le ?_)
  rintro _ ⟨Θ, rfl, hΘ⟩
  let T : H →L[ℂ] H := (LinearMap.toContinuousLinearMap (Θ.domRestrict S)).comp S.orthogonalProjectionOnto
  have hT : ∀ k ∈ GlobalTheory.LinRed.maxCpt G, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    have hk1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    have hks : k.conjTranspose ∈ GlobalTheory.LinRed.maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
    have hiso : ∀ x y, ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
      (LinearIsometry.mk (σ k : H →ₗ[ℂ] H) (hσ.2.1 k hk.1)).inner_map_map x y
    have hP : ((S.orthogonalProjectionOnto (σ k u) : S) : H) = σ k (S.orthogonalProjectionOnto u : S) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.orthogonalProjectionOnto u).2) ?_
      intro w hw
      have hw' : σ k (σ k.conjTranspose w) = w := by
        rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hk.1 _ hks.1, hk1, hσ.1.1]
        rfl
      rw [← hw', ← map_sub, hiso]
      exact S.starProjection_inner_eq_zero u _ (hS _ hks w hw)
    have h := hΘ k hk _ (S.orthogonalProjectionOnto u).2
    simpa [T, hP] using h
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v = ((⟨v, hv⟩ : S) : H) := rfl
  rw [hv', ← b.sum_repr ⟨v, hv⟩]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ?_)
  have := hY i T hT _ (hvY i)
  simpa [T] using this

end GlobalTheory.CompanionTheory.admitted

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeckeFunctional
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeckeFunctional
noncomputable section

namespace GlobalTheory.CompanionTheory.EisRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem hgt_par_mul {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) {p : G2 σ Y} {t : GL (Fin n) (AE F E)}
    (hp : IsPar p t) (x : G2 σ Y) :
    a (p * x) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) * a x := by
  obtain ⟨p', t', hp', k, hk, rfl⟩ := hK.iwa x
  rw [← mul_assoc, hK.val _ _ (hp.mul hp') k hk, hK.val _ _ hp' k hk, map_mul, map_mul]
  push_cast
  rfl

theorem hgt_nonneg {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) (x : G2 σ Y) : 0 ≤ a x := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := hK.iwa x
  rw [hK.val _ _ hp k hk]
  exact NNReal.coe_nonneg _

theorem absE_ne_zero (u : (AF F ⊗[F] E)ˣ) : ((absE F E u : ℝ) : ℂ) ≠ 0 := by
  have h : absE F E u ≠ 0 := ((absE F E).toHomUnits u).ne_zero
  exact_mod_cast h

theorem law_flat {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) {χ : Chr F E} {s₁ : ℂ} {f : G2 σ Y → ℂ}
    (hf : IsSec K χ s₁ f) (s : ℂ) : Law χ (s + n / 2) (flat a f s₁ s) := by
  intro p t x hp
  have hd := absE_ne_zero (F := F) (E := E) (Matrix.GeneralLinearGroup.det t)
  have h0 : (0 : ℝ) ≤ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := NNReal.coe_nonneg _
  have hc : ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s + (n : ℂ) / 2) =
      ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s - s₁) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s₁ + (n : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hd]
    congr 1
    ring
  unfold GlobalTheory.ThK.Dbl.flat
  rw [hgt_par_mul hK hp x, hf.law p t x hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg h0 (hgt_nonneg hK x), hc]
  ring

end GlobalTheory.CompanionTheory.EisRat

namespace GlobalTheory.CompanionTheory.EisRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem eis_left_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → IsHecke F E χ → ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → ∀ s : ℂ, t < s.re → ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := by
  intro F E _ _ _ _ _ σ B n Y r s _ _ _ b K a _ _ hK χ s₁ f hf hχ t Ê hs s' hs' γ hγ x
  exact (law_flat hK hf s').eis_rat hχ (hs s' hs') hγ x

end GlobalTheory.CompanionTheory.EisRat

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeckeFunctionalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_hecke_functional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → IsHecke F E χ → ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → ∀ s : ℂ, t < s.re → ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := by
  first | exact @GlobalTheory.CompanionTheory.EisRat.eis_left_rat | exact GlobalTheory.CompanionTheory.EisRat.eis_left_rat | (intros; apply GlobalTheory.CompanionTheory.EisRat.eis_left_rat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplit
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitHomeo

open GroundTheory.Automorphic GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_splitCentre : Continuous (splitCentre E a) := by
  have e : splitCentre E a = fun t : ℝ =>
      Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) :=
    funext splitCentre_eq_scalar
  rw [e]
  refine Continuous.units_map _ ?_ |>.comp ((continuous_infId E).comp
    (continuous_expU.comp (continuous_pi fun _ => Complex.continuous_ofReal)))
  change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin a => x
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal


variable (E) in
def expIdele (t : ℝ) : IdeleGroup E := infId E (expU fun _ : InfinitePlace E => (t : ℂ))

theorem pInf_expIdele (t : ℝ) (w : InfinitePlace E) :
    pInf E (expIdele E t : Ad E) w = Complex.exp t := by
  have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  change pInf E (1 - sInf E 1 + sInf E _) w = _
  simp only [map_add (f := _), map_sub, map_one, h, sub_self, zero_add]
  rfl

theorem pFin_expIdele (t : ℝ) : pFin E (expIdele E t : Ad E) = 1 := by
  change (1 : Af E) - 0 + 0 = 1
  simp

theorem ideleModule_expIdele (t : ℝ) :
    (IdeleGroup.ideleModule E (expIdele E t) : ℝ) = Real.exp (Module.finrank ℚ E * t) := by
  have h1 : ∀ v : InfinitePlace E, ‖(expIdele E t : Ad E).1 v‖ = Real.exp t := fun v => by
    have := pInf_expIdele (E := E) t v
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    refine (congrArg norm this).trans ?_
    rw [Complex.norm_exp, Complex.ofReal_re]
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(expIdele E t : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (expIdele E t : Ad E) v‖ = 1
    rw [pFin_expIdele]
    exact norm_one
  rw [IdeleGroup.ideleModule_eq]
  change (∏ v : InfinitePlace E, ‖(expIdele E t : Ad E).1 v‖ ^ v.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(expIdele E t : Ad E).2 v‖ = _
  simp only [h1, h2, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← Real.exp_nat_mul]

theorem det_splitCentre (t : ℝ) : AdelicGLn.det E a (splitCentre E a t) = expIdele E t ^ a := by
  rw [splitCentre_eq_scalar]
  refine Units.ext ?_
  change (Matrix.scalar (Fin a) (expIdele E t : Ad E)).det = _
  simp

theorem ideleModule_det_splitCentre (t : ℝ) :
    (IdeleGroup.ideleModule E (AdelicGLn.det E a (splitCentre E a t)) : ℝ) =
      Real.exp ((a * Module.finrank ℚ E : ℝ) * t) := by
  rw [det_splitCentre, map_pow, Positive.val_pow, ideleModule_expIdele, ← Real.exp_nat_mul]
  congr 1
  ring

def splitDeg (E : Type) [Field E] [NumberField E] (a : ℕ) (g : GA E a) : ℝ :=
  Real.log (IdeleGroup.ideleModule E (AdelicGLn.det E a g)) / (a * Module.finrank ℚ E : ℝ)

theorem continuous_splitDeg : Continuous (splitDeg E a) := by
  refine Continuous.div_const (Continuous.log ?_ fun g => ?_) _
  · exact continuous_subtype_val.comp
      (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  · exact (IdeleGroup.ideleModule E (AdelicGLn.det E a g)).2.ne'

theorem coeff_ne_zero (ha : 0 < a) : (a * Module.finrank ℚ E : ℝ) ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.2 ha.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')

theorem splitCentre_neg_mul_mem (ha : 0 < a) (g : GA E a) :
    splitCentre E a (-splitDeg E a g) * g ∈ Reduction.normOneGL (K := E) (n := a) := by
  have hc := coeff_ne_zero (E := E) ha
  have hpos := (IdeleGroup.ideleModule E (AdelicGLn.det E a g)).2
  rw [Reduction.mem_normOneGL, map_mul, map_mul, Positive.val_mul, ideleModule_det_splitCentre,
    mul_neg, splitDeg, mul_div_cancel₀ _ hc, Real.exp_neg, Real.exp_log hpos, inv_mul_cancel₀ hpos.ne']

theorem splitDeg_splitCentre_mul (ha : 0 < a) (x : Reduction.normOneGL (K := E) (n := a)) (t : ℝ) :
    splitDeg E a (splitCentre E a t * (x : GA E a)) = t := by
  have hc := coeff_ne_zero (E := E) ha
  have hx : (IdeleGroup.ideleModule E (AdelicGLn.det E a (x : GA E a)) : ℝ) = 1 :=
    Reduction.mem_normOneGL.1 x.2
  rw [splitDeg, map_mul, map_mul, Positive.val_mul, ideleModule_det_splitCentre, hx, mul_one,
    Real.log_exp, mul_div_cancel_left₀ _ hc]

theorem splitCentre_neg_mul_self (t : ℝ) (g : GA E a) :
    splitCentre E a (-t) * (splitCentre E a t * g) = g := by
  rw [← mul_assoc, ← splitCentre_add, neg_add_cancel, splitCentre_zero, one_mul]

theorem exists_homeomorph (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ha : 0 < a) :
    ∃ e : Reduction.normOneGL (K := E) (n := a) × ℝ ≃ₜ GA E a, ∀ x t, e (x, t) = splitCentre E a t * (x : GA E a) := by
  refine ⟨{
    toFun := fun p => splitCentre E a p.2 * (p.1 : GA E a)
    invFun := fun g => (⟨splitCentre E a (-splitDeg E a g) * g, splitCentre_neg_mul_mem ha g⟩, splitDeg E a g)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }, fun _ _ => rfl⟩
  · rintro ⟨x, t⟩
    refine Prod.ext (Subtype.ext ?_) (splitDeg_splitCentre_mul ha x t)
    change splitCentre E a (-splitDeg E a (splitCentre E a t * (x : GA E a))) * _ = _
    rw [splitDeg_splitCentre_mul ha x t, splitCentre_neg_mul_self]
  · intro g
    change splitCentre E a (splitDeg E a g) * (splitCentre E a (-splitDeg E a g) * g) = g
    simpa using splitCentre_neg_mul_self (-splitDeg E a g) g
  · exact (continuous_splitCentre.comp continuous_snd).mul
      (continuous_subtype_val.comp continuous_fst)
  · refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_splitDeg
    exact (continuous_splitCentre.comp continuous_splitDeg.neg).mul continuous_id

end GlobalTheory.CompanionTheory.SplitHomeo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplitStatement
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_GL_norm_one_split : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∃ e : GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a) × ℝ ≃ₜ GA E a, ∀ x t, e (x, t) = splitCentre E a t * (x : GA E a) := by
  first | exact @GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph | exact GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph | (intros; apply GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslate
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.TransDeriv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}

theorem descend_eq_sec {X : Type} {f : G → X} (h : LeftInv Γ f) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) :
    descend Γ f q = f (sec Γ q) := by
  conv_lhs => rw [← mk_sec q]
  exact h.descend_mk _

theorem sec_mul_eq {X : Type} {f : G → X} (h : LeftInv Γ f) (g : G) :
    (fun q : GlobalTheory.AutomorphicL2Unitary.Quot Γ => f (sec Γ q * g)) = descend Γ f ∘ rmul Γ g := by
  funext q
  have e : rmul Γ g q = mk Γ (sec Γ q * g) := by
    conv_lhs => rw [← mk_sec q]
    rfl
  rw [Function.comp_apply, e, h.descend_mk]

variable [μ.IsMulLeftInvariant]

theorem inner_toL2_eq_integral {f : G → ℂ} (hf : MemL2Quotient Γ μ f) (u : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) :
    ⟪u, hf.toL2⟫_ℂ = ∫ q : GlobalTheory.AutomorphicL2Unitary.Quot Γ, conj (u q) * f (sec Γ q) ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL2] with q e
  rw [e, descend_eq_sec hf.1]
  simp [mul_comm]

theorem sub_eq_integral {φ ψ : G → ℂ} {c : ℝ → G} (hψ : Continuous ψ) (hc : Continuous c) (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hd : ∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) (x : G) (t : ℝ) :
    φ (x * c t) - φ x = ∫ s in (0 : ℝ)..t, ψ (x * c s) := by
  have hs : ∀ s, HasDerivAt (fun r => φ (x * c r)) (ψ (x * c s)) s := fun s => by
    have h2 : HasDerivAt (fun t => φ (x * c s * c t)) (ψ (x * c s)) (s - s) := by simpa using hd (x * c s)
    have h3 := h2.comp_sub_const s s
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    have : c r = c s * c (r - s) := by rw [← hadd]; congr 1; ring
    simp only [this, mul_assoc]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hs s)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [h0]

theorem integrable_pair [μ.IsMulRightInvariant] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] {ψ : G → ℂ}
    (hψ : MemL2Quotient Γ μ ψ) (hψc : Continuous ψ) {c : ℝ → G} (hc : Continuous c) (u : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (t : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s))
      ((volume.restrict (Set.uIoc 0 t)).prod (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) := by
  have hsec := (measurableEmbedding_sec (Γ := Γ)).measurable
  have hm : Measurable (fun p : ℝ × GlobalTheory.AutomorphicL2Unitary.Quot Γ => ψ (sec Γ p.2 * c p.1)) :=
    hψc.measurable.comp ((hsec.comp measurable_snd).mul (hc.measurable.comp measurable_fst))
  have hu : Measurable (fun p : ℝ × GlobalTheory.AutomorphicL2Unitary.Quot Γ => conj (u p.2)) :=
    Complex.continuous_conj.measurable.comp ((Lp.stronglyMeasurable u).measurable.comp measurable_snd)
  have hF : Measurable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s)) :=
    hu.mul hm
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hF.enorm.aemeasurable]
  set C : ENNReal := eLpNorm u 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * eLpNorm (descend Γ ψ) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) with hC
  have hb : ∀ s, ∫⁻ q, ‖Function.uncurry (fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s)) (s, q)‖ₑ
      ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ ≤ C := fun s => by
    have h1 := eLpNorm_le_eLpNorm_mul_eLpNorm (μ := GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) (p := 2) (q := 2) (r := 1)
      (fun a b : ℂ => conj a * b) 1 (by fun_prop)
      (Lp.aestronglyMeasurable u) ((hψ.mul_right (c s)).2.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => by simp)
    have h2 : eLpNorm (descend Γ fun x => ψ (x * c s)) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) = eLpNorm (descend Γ ψ) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
      have e : descend Γ (fun x => ψ (x * c s)) = descend Γ ψ ∘ rmul Γ (c s) := by
        funext q
        rw [descend_eq_sec (hψ.1.mul_right (c s)), ← sec_mul_eq hψ.1]
      rw [e]
      exact eLpNorm_comp_measurePreserving hψ.2.aestronglyMeasurable (measurePreserving_rmul (c s))
    have hm₁ : AEStronglyMeasurable (fun q => conj (u q) * descend Γ (fun x => ψ (x * c s)) q)
        (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
      (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).mul
        (hψ.mul_right (c s)).2.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_eNorm hm₁, h2] at h1
    simp only [ENNReal.coe_one, one_mul] at h1
    refine le_trans (le_of_eq ?_) h1
    refine lintegral_congr fun q => ?_
    simp only [Function.uncurry, descend_eq_sec (hψ.1.mul_right (c s))]
  refine lt_of_le_of_lt (lintegral_mono hb) ?_
  rw [lintegral_const, Measure.restrict_apply_univ]
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (Lp.memLp u) hψ.2) ?_
  simp [Set.uIoc, Real.volume_Ioc]

variable [μ.IsMulRightInvariant] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ]

theorem R_sub_eq_integral {φ ψ : G → ℂ} (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ)
    (hψc : Continuous ψ) {c : ℝ → G} (hc : Continuous c) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hd : ∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) (t : ℝ) :
    R Γ μ (c t) hφ.toL2 - hφ.toL2 = ∫ s in (0 : ℝ)..t, R Γ μ (c s) hψ.toL2 := by
  have hcont : Continuous fun s => R Γ μ (c s) hψ.toL2 := (continuous_R _).comp hc
  refine ext_inner_left ℂ fun u => ?_
  have e1 := (innerSL ℂ u).intervalIntegral_comp_comm (hcont.intervalIntegrable (μ := volume) 0 t)
  simp only [innerSL_apply_apply] at e1
  rw [← e1, inner_sub_right]
  simp only [right_translate_toL2, inner_toL2_eq_integral]
  have hi : ∀ {f : G → ℂ} (hf : MemL2Quotient Γ μ f),
      Integrable (fun q : GlobalTheory.AutomorphicL2Unitary.Quot Γ => conj (u q) * f (sec Γ q)) (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := fun {f} hf => by
    have h := (Lp.memLp u).star.integrable_mul hf.2
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    simp [descend_eq_sec hf.1]
  rw [← integral_sub (hi (hφ.mul_right (c t))) (hi hφ), intervalIntegral.intervalIntegral_eq_integral_uIoc,
    integral_integral_swap (integrable_pair hψ hψc hc u t), ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [integral_const_mul]
  rw [← mul_sub, sub_eq_integral hψc hc h0 hadd hd, intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [mul_smul_comm]

theorem hasDerivAt_R : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (φ ψ : G → ℂ) (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ) (c : ℝ → G), Continuous φ → Continuous ψ → Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → (∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) → ∀ t, HasDerivAt (fun s => R Γ μ (c s) hφ.toL2) (R Γ μ (c t) hψ.toL2) t := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c _ hψc hc h0 hadd hd t
  have hcont : Continuous fun s => R Γ μ (c s) hψ.toL2 := (continuous_R _).comp hc
  have e : (fun s => R Γ μ (c s) hφ.toL2) = fun s => hφ.toL2 + ∫ r in (0 : ℝ)..s, R Γ μ (c r) hψ.toL2 := by
    funext s
    rw [← R_sub_eq_integral hφ hψ hψc hc h0 hadd hd s]
    abel
  rw [e]
  exact (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _

end GlobalTheory.CompanionTheory.TransDeriv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslateStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_right_translate_toL2 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (φ ψ : G → ℂ) (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ) (c : ℝ → G), Continuous φ → Continuous ψ → Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → (∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) → ∀ t, HasDerivAt (fun s => R Γ μ (c s) hφ.toL2) (R Γ μ (c t) hψ.toL2) t := by
  first | exact @GlobalTheory.CompanionTheory.TransDeriv.hasDerivAt_R | exact GlobalTheory.CompanionTheory.TransDeriv.hasDerivAt_R | (intros; apply GlobalTheory.CompanionTheory.TransDeriv.hasDerivAt_R <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLe
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLe
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitalCount

theorem relIndex_open_compact_and_twisted :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K L : Subgroup H),
      IsOpen (L : Set H) → IsCompact (K : Set H) → L ≤ K → L.relIndex K ≠ 0 ∧
        ∀ (T C : Subgroup H) (x : H),
          (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 →
            (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 := by
  intro H _ _ _ K L hL hK hLK
  have hKL : L.relIndex K ≠ 0 := by
    haveI := isCompact_iff_compactSpace.mp hK
    haveI : Finite (K ⧸ L.subgroupOf K) :=
      Subgroup.quotient_finite_of_isOpen _ (hL.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  refine ⟨hKL, fun T C x hC => ?_⟩
  have hf : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have h1 : (L.map (MulAut.conj x).toMonoidHom).relIndex (K.map (MulAut.conj x).toMonoidHom) ≠ 0 := by
    rwa [Subgroup.relIndex_map_map_of_injective L K hf]
  have h2 : (L.map (MulAut.conj x).toMonoidHom).relIndex (T ⊓ K.map (MulAut.conj x).toMonoidHom) ≠ 0 :=
    fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h)
  have h3 : T.relIndex (T ⊓ K.map (MulAut.conj x).toMonoidHom) ≠ 0 := by
    rw [Subgroup.relIndex_eq_one.mpr inf_le_left]
    exact one_ne_zero
  exact Subgroup.relIndex_ne_zero_trans (Subgroup.relIndex_inf_ne_zero h3 h2) hC

end GlobalTheory.CompanionTheory.OrbitalCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLeStatement
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_index_ne_zero_of_open_le : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K L : Subgroup H), IsOpen (L : Set H) → IsCompact (K : Set H) → L ≤ K → L.relIndex K ≠ 0 ∧ ∀ (T C : Subgroup H) (x : H), (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 → (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted | exact GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted | (intros; apply GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted <;> assumption)
end
end
