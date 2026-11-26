module

public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.AlgebraMapMemChartRingJoinPt
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReducedRadical
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMParameterQuotient
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CurveNormalisationFiniteLemmas
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInvarianceOfDomain
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFreenessClosed
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalUniversalDenominator
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurveJacobian
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedBranchSameOrder
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreSFlatAscent
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointDegreePos
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCombContract
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCombCyclic
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeFinite
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAlt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsAlgebraicAdjoin
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormOfMemChartRingOver
public import GroundTheory.AutomorphicForms.HermitianExistenceLocal
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PRootsOfUnityValuation
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymDivisible
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymStability
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupAction
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHecke
public import GroundTheory.GlobalFields.Artin.OneDim
public import GroundTheory.GlobalFields.Artin.Series
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveNormalisationFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem CurveNormalisationFinite.proof (hN : FieldNumbers.NoetherIntegralClosureFinite.Statement.{0}) :
    CurveNormalisationFinite.Statement := by
  intro n I q hI
  have := isReduced_curveLocalRing I q hI
  exact finite_integralClosure_of_isReduced hN (algebraMap _ (curveLocalRing I q)) (curveLocalRing_eq_div I q)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthCutLocalizedModule
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

open IsLocalRing

theorem LengthCutLocalizedModule.proof (hG : LengthCutGlobal.Statement.{u, max u v})
    (hL : LengthLocalizedLocalized.Statement.{u, v}) : LengthCutLocalizedModule.Statement.{u, v} := by
  intro B _ _ P _ y Q₀ _ M _ _ _ hnil hy hQ htf
  have hPQ : P ≤ Q₀ := hQ ▸ le_sup_left
  have hdisj : Disjoint (Q₀.primeCompl : Set B) P := Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP)
  have hP' : (P.map (algebraMap B (Localization.AtPrime Q₀))).IsPrime :=
    LengthLocalizedLocalized.map_isPrime B P Q₀ hPQ
  have : IsNoetherianRing (Localization.AtPrime Q₀) :=
    IsLocalization.isNoetherianRing Q₀.primeCompl _ inferInstance
  have hunder : (P.map (algebraMap B (Localization.AtPrime Q₀))).comap (algebraMap B (Localization.AtPrime Q₀)) =
      P := IsLocalization.under_map_of_isPrime_disjoint Q₀.primeCompl _ ‹P.IsPrime› hdisj

  have hy' : algebraMap B (Localization.AtPrime Q₀) y ∉ P.map (algebraMap B (Localization.AtPrime Q₀)) := by
    intro h
    apply hy
    rw [← hunder]
    exact h

  have hsup : P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔
      Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} = maximalIdeal (Localization.AtPrime Q₀) := by
    have hmap : Ideal.map (algebraMap B (Localization.AtPrime Q₀)) Q₀ =
        Ideal.map (algebraMap B (Localization.AtPrime Q₀)) (P ⊔ Ideal.span {y}) := congrArg _ hQ
    rw [← Localization.AtPrime.map_eq_maximalIdeal, hmap, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hmax : (P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔
      Ideal.span {algebraMap B (Localization.AtPrime Q₀) y}).IsMaximal := by
    rw [hsup]
    exact maximalIdeal.isMaximal _

  have hnil' : IsNilpotent (P.map (algebraMap B (Localization.AtPrime Q₀))) := by
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow, hn]
    simp

  have hpir : IsPrincipalIdealRing
      (Localization.AtPrime Q₀ ⧸ P.map (algebraMap B (Localization.AtPrime Q₀))) := by
    set I := P.map (algebraMap B (Localization.AtPrime Q₀)) with hI
    have : IsLocalRing (Localization.AtPrime Q₀ ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hm : maximalIdeal (Localization.AtPrime Q₀ ⧸ I) =
        Ideal.span {Ideal.Quotient.mk I (algebraMap B (Localization.AtPrime Q₀) y)} := by
      have hc : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).comap (Ideal.Quotient.mk I) =
          maximalIdeal (Localization.AtPrime Q₀) :=
        eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (maximalIdeal _), hc, ← hsup,
        Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
    have hprin : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).IsPrincipal := ⟨⟨_, hm⟩⟩
    exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime Q₀ ⧸ I)).out 1 5).mpr hprin

  have htf' : ∀ s ∉ P.map (algebraMap B (Localization.AtPrime Q₀)), ∀ m : LocalizedModule Q₀.primeCompl M,
      s • m = 0 → m = 0 := by
    intro s hs m hsm
    induction s using Localization.induction_on with
    | H x =>
    obtain ⟨a, t⟩ := x
    dsimp only at hs hsm
    have ha : a ∉ P := by
      intro ha
      apply hs
      rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    induction m using LocalizedModule.induction_on with
    | h m u =>
      rw [LocalizedModule.mk_smul_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hsm
      obtain ⟨v, hv⟩ := hsm
      simp only [smul_zero, one_smul, Submonoid.smul_def, smul_smul] at hv
      have hva : (v : B) * a ∉ P := fun h =>
        (‹P.IsPrime›.mem_or_mem h).elim (fun h1 => v.2 (hPQ h1)) ha
      rw [htf _ hva m hv, LocalizedModule.zero_mk]

  have hloc : (Ideal.span {y} • ⊤ : Submodule B M).localized' (Localization.AtPrime Q₀) Q₀.primeCompl
      (LocalizedModule.mkLinearMap Q₀.primeCompl M) =
      (Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} • ⊤ :
        Submodule (Localization.AtPrime Q₀) (LocalizedModule Q₀.primeCompl M)) := by
    rw [Submodule.localized'_smul, Submodule.localized'_top, Ideal.localized'_eq_map, Ideal.map_span,
      Set.image_singleton]
  let e := (IsLocalizedModule.linearEquiv Q₀.primeCompl
    ((Ideal.span {y} • ⊤ : Submodule B M).toLocalizedQuotient' (Localization.AtPrime Q₀) Q₀.primeCompl
      (LocalizedModule.mkLinearMap Q₀.primeCompl M))
    (LocalizedModule.mkLinearMap Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M)))).extendScalarsOfIsLocalization
      Q₀.primeCompl (Localization.AtPrime Q₀)
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hloc).length_eq,
    hG (Localization.AtPrime Q₀) (P.map (algebraMap B (Localization.AtPrime Q₀)))
      (algebraMap B (Localization.AtPrime Q₀) y) (LocalizedModule Q₀.primeCompl M) hnil' hpir hy' hmax htf',
    hL B P Q₀ M hPQ]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthCutGlobal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped Pointwise

universe u v

namespace LengthCutGlobal

section Layers

variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]

theorem length_localized_add {N M Q : Type*} [AddCommGroup N] [Module C N] [AddCommGroup M]
    [Module C M] [AddCommGroup Q] [Module C Q] (f : N →ₗ[C] M) (g : M →ₗ[C] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl N) +
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl Q) := by
  let fN := LocalizedModule.mkLinearMap P.primeCompl N
  let fM := LocalizedModule.mkLinearMap P.primeCompl M
  let fQ := LocalizedModule.mkLinearMap P.primeCompl Q
  exact Module.length_eq_add_of_exact
    ((IsLocalizedModule.map P.primeCompl fN fM f).extendScalarsOfIsLocalization P.primeCompl
      (Localization.AtPrime P))
    ((IsLocalizedModule.map P.primeCompl fM fQ g).extendScalarsOfIsLocalization P.primeCompl
      (Localization.AtPrime P))
    (IsLocalizedModule.map_injective P.primeCompl fN fM f hf)
    (IsLocalizedModule.map_surjective P.primeCompl fM fQ g hg)
    (IsLocalizedModule.map_exact P.primeCompl fN fM fQ f g H)


omit [P.IsPrime] in
theorem length_quotSMulTop_add (y : C) {N M Q : Type*} [AddCommGroup N] [Module C N]
    [AddCommGroup M] [Module C M] [AddCommGroup Q] [Module C Q] (f : N →ₗ[C] M) (g : M →ₗ[C] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    (hy : ∀ q : Q, y • q = 0 → q = 0) :
    Module.length C (QuotSMulTop y M) =
      Module.length C (QuotSMulTop y N) + Module.length C (QuotSMulTop y Q) := by
  refine Module.length_eq_add_of_exact (QuotSMulTop.map y f) (QuotSMulTop.map y g) ?_
    (QuotSMulTop.map_surjective y hg) (QuotSMulTop.map_exact y H hg)
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨m, -, hm⟩ := hx
  have hgm : g m = 0 := hy _ (by rw [← map_smul, hm]; exact (H (f n)).2 ⟨n, rfl⟩)
  obtain ⟨n', rfl⟩ := (H m).1 hgm
  have hn : n = y • n' := hf (by rw [map_smul, hm])
  rw [Submodule.Quotient.mk_eq_zero, hn]
  exact Submodule.smul_mem_pointwise_smul n' y ⊤ trivial

theorem lengths_of_subsingleton (y : C) (X : Type*) [AddCommGroup X] [Module C X] [Subsingleton X] :
    Module.length C (QuotSMulTop y X) = 0 ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl X) = 0 := by
  have : Subsingleton (QuotSMulTop y X) := (Submodule.mkQ_surjective _).subsingleton
  exact ⟨Module.length_eq_zero, Module.length_eq_zero⟩

theorem smul_injective_pi {y : C} (hy : y ∉ P) (n : ℕ) (v : Fin n → C ⧸ P) (h : y • v = 0) :
    v = 0 := by
  funext i
  have hi := congrFun h i
  rw [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Pi.zero_apply] at hi
  exact (mul_eq_zero.1 hi).resolve_left (fun h => hy (Ideal.Quotient.eq_zero_iff_mem.1 h))


omit [P.IsPrime] in
theorem length_quotSMulTop_quot {y : C} (hmax : (P ⊔ Ideal.span {y}).IsMaximal) :
    Module.length C (QuotSMulTop y (C ⧸ P)) = 1 := by
  let g : C →ₗ[C] QuotSMulTop y (C ⧸ P) :=
    (y • (⊤ : Submodule C (C ⧸ P))).mkQ ∘ₗ Algebra.linearMap C (C ⧸ P)
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp Ideal.Quotient.mk_surjective
  have hker : LinearMap.ker g = P ⊔ Ideal.span {y} := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Algebra.linearMap_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective t
      have hmem : x - y * c ∈ P := by
        rw [← Ideal.Quotient.eq, map_mul, ← Ideal.Quotient.algebraMap_eq, ← ht, Algebra.smul_def]
        rfl
      rw [show x = (x - y * c) + y * c by ring]
      exact Submodule.add_mem_sup hmem (Ideal.mem_span_singleton'.2 ⟨c, mul_comm c y⟩)
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine ⟨Ideal.Quotient.mk P c, ?_⟩
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add (f := _),
        Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, map_mul, mul_comm]
  rw [← (g.quotKerEquivOfSurjective hg).length_eq, hker]
  exact Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.1 hmax))

theorem length_localized_quot :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (C ⧸ P)) = 1 := by
  let S := Localization.AtPrime P
  have hJ : (P : Submodule C C).localized' S P.primeCompl (Algebra.linearMap C S) =
      IsLocalRing.maximalIdeal S := by
    rw [Submodule.localized'_eq_span, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv P.primeCompl
    ((P : Submodule C C).toLocalizedQuotient' S P.primeCompl (Algebra.linearMap C S))
    (LocalizedModule.mkLinearMap P.primeCompl (C ⧸ P))).extendScalarsOfIsLocalization P.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.mpr
    (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal S)))

theorem lengths_pi {y : C} (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal) (n : ℕ) :
    Module.length C (QuotSMulTop y (Fin n → C ⧸ P)) = n ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (Fin n → C ⧸ P)) = n := by
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero]
    exact lengths_of_subsingleton P y (Fin 0 → C ⧸ P)
  | succ n ih =>
    let f : (C ⧸ P) →ₗ[C] (Fin (n + 1) → C ⧸ P) := LinearMap.single C (fun _ => C ⧸ P) 0
    let g : (Fin (n + 1) → C ⧸ P) →ₗ[C] (Fin n → C ⧸ P) := LinearMap.funLeft C (C ⧸ P) Fin.succ
    have hf : Function.Injective f := fun a b h => by simpa [f] using congrFun h 0
    have hg : Function.Surjective g :=
      LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
    have H : Function.Exact f g := by
      intro v
      constructor
      · intro hv
        refine ⟨v 0, funext fun i => ?_⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [f]
        · have hj : v j.succ = 0 := congrFun hv j
          simp [f, hj, Fin.succ_ne_zero]
      · rintro ⟨t, rfl⟩
        funext j
        simp [f, g, LinearMap.funLeft, Fin.succ_ne_zero]
    rw [length_quotSMulTop_add y f g hf hg H (smul_injective_pi P hy n),
      length_localized_add P f g hf hg H, ih.1, ih.2, length_quotSMulTop_quot P hmax,
      length_localized_quot P]
    constructor <;> push_cast <;> ring

theorem lengths_free {y : C} (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal) {n : ℕ}
    {X : Type*} [AddCommGroup X] [Module C X] (e : X ≃ₗ[C] (Fin n → C ⧸ P)) :
    Module.length C (QuotSMulTop y X) = n ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl X) = n := by
  rw [(QuotSMulTop.congr y e).length_eq,
    (IsLocalizedModule.mapEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl X)
      (LocalizedModule.mkLinearMap P.primeCompl (Fin n → C ⧸ P)) (Localization.AtPrime P) e).length_eq]
  exact lengths_pi P hy hmax n

end Layers

theorem lengths_eq {C : Type u} [CommRing C] [IsNoetherianRing C] (P : Ideal C) [P.IsPrime] (y : C)
    (hPID : IsPrincipalIdealRing (C ⧸ P)) (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal)
    (k : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module C M] [Module.Finite C M],
      (∀ p ∈ P ^ k, ∀ m : M, p • m = 0) → (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length C (QuotSMulTop y M) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) := by
  induction k with
  | zero =>
    intro M _ _ _ hann _
    have : Subsingleton M := ⟨fun a b => by
      rw [← one_smul C a, ← one_smul C b, hann 1 (by simp) a, hann 1 (by simp) b]⟩
    rw [(lengths_of_subsingleton P y M).1, (lengths_of_subsingleton P y M).2]
  | succ k ih =>
    intro M _ _ _ hann hinj
    have := hPID

    have : Module.Finite C (Submodule.torsionBySet C M (P : Set C)) :=
      Module.Finite.of_injective (Submodule.torsionBySet C M (P : Set C)).subtype
        (Submodule.torsionBySet C M (P : Set C)).injective_subtype
    have : Module.Finite (C ⧸ P) (Submodule.torsionBySet C M (P : Set C)) :=
      Module.Finite.of_restrictScalars_finite C (C ⧸ P) _
    have : Module.IsTorsionFree (C ⧸ P) (Submodule.torsionBySet C M (P : Set C)) := by
      refine Module.IsTorsionFree.of_smul_eq_zero fun r n h => ?_
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
      by_cases hs : s ∈ P
      · exact Or.inl (Ideal.Quotient.eq_zero_iff_mem.2 hs)
      · right
        rw [Submodule.torsionBySet.mk_smul] at h
        exact Subtype.ext (hinj s hs n (congrArg Subtype.val h))
    obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := C ⧸ P)
      (M := Submodule.torsionBySet C M (P : Set C))
    have hN := lengths_free P hy hmax (b.equivFun.restrictScalars C)

    have hannQ : ∀ p ∈ P ^ k, ∀ q : M ⧸ Submodule.torsionBySet C M (P : Set C), p • q = 0 := by
      intro p hp q
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      rw [smul_smul]
      exact hann _ (by rw [pow_succ']; exact Ideal.mul_mem_mul ha hp) m
    have hinjQ : ∀ s ∉ P, ∀ q : M ⧸ Submodule.torsionBySet C M (P : Set C), s • q = 0 → q = 0 := by
      intro s hs q hq
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_torsionBySet_iff] at hq
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      apply hinj s hs
      rw [smul_comm]
      exact hq ⟨a, ha⟩
    have hQ := ih (M ⧸ Submodule.torsionBySet C M (P : Set C)) hannQ hinjQ
    let N := Submodule.torsionBySet C M (P : Set C)
    rw [length_quotSMulTop_add y N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N) (hinjQ y hy),
      length_localized_add P N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hQ, hN.1, hN.2]

theorem proof : LengthCutGlobal.Statement.{u, v} := by
  intro C _ _ P _ y M _ _ _ hnil hPID hy hmax hinj
  obtain ⟨k, hk⟩ := hnil
  rw [Submodule.ideal_span_singleton_smul]
  refine lengths_eq P y hPID hy hmax k M (fun p hp m => ?_) hinj
  rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
  rw [hp, zero_smul]

end LengthCutGlobal

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthLocalizedLocalized
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

theorem LengthLocalizedLocalized.isLocalization_atPrime_map (B : Type u) [CommRing B] (P Q : Ideal B)
    [hP : P.IsPrime] [Q.IsPrime] [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime] (hPQ : P ≤ Q) :
    IsLocalization P.primeCompl (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) := by
  have h : Ideal.under B (P.map (algebraMap B (Localization.AtPrime Q))) = P :=
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) hP
      (Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP))
  have key : IsLocalization ((P.map (algebraMap B (Localization.AtPrime Q))).comap
        (algebraMap B (Localization.AtPrime Q))).primeCompl
      (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) :=
    IsLocalization.isLocalization_atPrime_localization_atPrime Q.primeCompl _
  rw [Ideal.under] at h
  have e : P.primeCompl = ((P.map (algebraMap B (Localization.AtPrime Q))).comap
      (algebraMap B (Localization.AtPrime Q))).primeCompl :=
    Submonoid.ext fun x => by rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, h]
  rw [e]
  exact key

theorem LengthLocalizedLocalized.proof : LengthLocalizedLocalized.Statement.{u, v} := by
  intro B _ P Q _ _ _ M _ _ hPQ
  have hloc := LengthLocalizedLocalized.isLocalization_atPrime_map B P Q hPQ

  let σ : Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))) ≃ₐ[B]
      Localization.AtPrime P := IsLocalization.algEquiv P.primeCompl _ _
  let : Algebra (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P) := σ.toRingHom.toAlgebra
  let : Module (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule P.primeCompl M) :=
    Module.compHom _ (algebraMap (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P))
  have : IsScalarTower (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    ⟨fun r l x => by
      show (r • l) • x = algebraMap _ (Localization.AtPrime P) r • (l • x)
      rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower B (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule P.primeCompl M) :=
    ⟨fun b r x => by
      show algebraMap _ (Localization.AtPrime P) (b • r) • x =
        b • (algebraMap _ (Localization.AtPrime P) r • x)
      rw [Algebra.smul_def, map_mul, mul_smul]
      rw [show algebraMap (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
          (Localization.AtPrime P) (algebraMap B _ b) = algebraMap B (Localization.AtPrime P) b from
          σ.commutes b, algebraMap_smul]⟩

  have hf : IsBaseChange (Localization.AtPrime Q) (LocalizedModule.mkLinearMap Q.primeCompl M) :=
    IsLocalizedModule.isBaseChange Q.primeCompl _ _
  have hg : IsBaseChange (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule.mkLinearMap (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl
        (LocalizedModule Q.primeCompl M)) :=
    IsLocalizedModule.isBaseChange (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl _ _
  have hfg := hf.comp hg
  have h0 : IsBaseChange (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule.mkLinearMap P.primeCompl M) :=
    IsLocalizedModule.isBaseChange P.primeCompl _ _
  rw [← (h0.equiv.symm.trans hfg.equiv).length_eq]
  exact Module.length_eq_of_surjective σ.surjective

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChangeOfVariablesDegree
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChangeOfVariablesDegreePiola
set_option maxSynthPendingDepth 1

open scoped ContDiff
open MeasureTheory

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace ChangeOfVariablesDegree

variable {n : ℕ}

noncomputable def jacobian (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun k l => fderiv ℝ H x (Pi.single l 1) k

theorem det_fderiv_eq_det_jacobian (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) :
    (fderiv ℝ H x).det = (Matrix.of (jacobian H x)).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  congr 1

theorem jacobian_eq_fderiv_apply (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ)
    (hd : DifferentiableAt ℝ H x) (k l : Fin n) :
    jacobian H x k l = fderiv ℝ (fun y => H y k) x (Pi.single l 1) := by
  have hd' : HasFDerivAt (fun y => H y k) ((ContinuousLinearMap.proj k).comp (fderiv ℝ H x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp x
      hd.hasFDerivAt
  rw [hd'.fderiv]; rfl

noncomputable def detCML : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := continuous_id.matrix_det }

theorem detCML_apply (M : Fin n → Fin n → ℝ) : detCML M = Matrix.det (Matrix.of M) := rfl

theorem det_update_eq_sum (V : Fin n → Fin n → ℝ) (k : Fin n) (r : Fin n → ℝ) :
    Matrix.det (Matrix.of (Function.update V k r)) =
      ∑ l, r l * Matrix.det (Matrix.of (Function.update V k (Pi.single l 1))) := by
  have hr : r = ∑ l, r l • (Pi.single l 1 : Fin n → ℝ) := by
    ext m; simp [Pi.single_apply]
  conv_lhs => rw [hr]
  change (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap.toLinearMap V k
    (∑ l, r l • (Pi.single l 1 : Fin n → ℝ)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul, MultilinearMap.toLinearMap_apply]
  rfl

noncomputable def entriesCLM : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun l =>
    (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.apply ℝ (Fin n → ℝ) (Pi.single l 1))

noncomputable def killRow (i : Fin n) : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => if k = i then 0 else ContinuousLinearMap.proj k

theorem killRow_apply_self (i : Fin n) (M : Fin n → Fin n → ℝ) : killRow i M i = 0 := by
  simp [killRow]

theorem killRow_apply_ne {i k : Fin n} (h : k ≠ i) (M : Fin n → Fin n → ℝ) :
    killRow i M k = M k := by
  simp [killRow, h]

theorem update_eq_killRow (M : Fin n → Fin n → ℝ) (i : Fin n) (c : Fin n → ℝ) :
    Function.update M i c = killRow i M + Pi.single i c := by
  funext k
  by_cases h : k = i
  · subst h; simp [killRow_apply_self]
  · simp [killRow_apply_ne h, h]

noncomputable def cofactorFn (H : (Fin n → ℝ) → Fin n → ℝ) (i j : Fin n) (y : Fin n → ℝ) : ℝ :=
  Matrix.det (Matrix.of (Function.update (jacobian H y) i (Pi.single j 1)))

theorem hasFDerivAt_cofactorFn (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H)
    (i j : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (cofactorFn H i j)
      ((detCML.linearDeriv (Function.update (jacobian H x) i (Pi.single j 1))).comp
        ((killRow i).comp (entriesCLM.comp (fderiv ℝ (fderiv ℝ H) x)))) x := by
  have h2 : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) x) x :=
    ((hH.fderiv_right (m := ∞) le_rfl).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hM : HasFDerivAt
      (fun y => (Function.update (jacobian H y) i (Pi.single j 1) : Fin n → Fin n → ℝ))
      ((killRow i).comp (entriesCLM.comp (fderiv ℝ (fderiv ℝ H) x))) x := by
    have : (fun y => (Function.update (jacobian H y) i (Pi.single j 1) : Fin n → Fin n → ℝ)) =
        fun y => killRow i (entriesCLM (fderiv ℝ H y)) + Pi.single i (Pi.single j 1) := by
      funext y; exact update_eq_killRow _ _ _
    rw [this]
    exact ((killRow i).hasFDerivAt.comp x (entriesCLM.hasFDerivAt.comp x h2)).add_const _
  exact (detCML.hasFDerivAt _).comp x hM

theorem sum_det_symm_eq_zero (A : Fin n → Fin n → ℝ) {i k : Fin n} (hik : i ≠ k)
    (S : Fin n → Fin n → ℝ) (hS : ∀ j l, S j l = S l j) :
    ∑ j, Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single j 1)) k (S j))) =
      0 := by
  simp_rw [det_update_eq_sum _ k (S _)]
  set T : Fin n → Fin n → ℝ := fun j l =>
    Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single j 1)) k
      (Pi.single l 1))) with hTdef
  have hT : ∀ j l, T j l = - T l j := by
    intro j l
    have hw : (Function.update (Function.update A i (Pi.single l 1)) k (Pi.single j 1)) =
        (Function.update (Function.update A i (Pi.single j 1)) k (Pi.single l 1)) ∘
          Equiv.swap i k := by
      funext r
      by_cases hri : r = i
      · subst hri; simp [Equiv.swap_apply_left, hik]
      · by_cases hrk : r = k
        · subst hrk; simp [Equiv.swap_apply_right, hik]
        · simp [Equiv.swap_apply_of_ne_of_ne hri hrk, hri, hrk]
    have h1 : T l j = - T j l := by
      show Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single l 1)) k
        (Pi.single j 1))) = _
      rw [hw]
      exact (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).map_swap
        (Function.update (Function.update A i (Pi.single j 1)) k (Pi.single l 1)) hik
    linarith
  have hX : ∑ j, ∑ l, S j l * T j l = - ∑ j, ∑ l, S j l * T j l := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hS l j, hT l j]; ring
  change ∑ j, ∑ l, S j l * T j l = 0
  linarith

theorem sum_fderiv_cofactorFn_eq_zero (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H) (i : Fin n)
    (x : Fin n → ℝ) :
    ∑ j, fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) = 0 := by
  set D2 := fderiv ℝ (fderiv ℝ H) x with hD2
  have hsym : ∀ v w, D2 v w = D2 w v :=
    (hH.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  simp_rw [(hasFDerivAt_cofactorFn H hH i _ x).fderiv, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [killRow_apply_self, Function.update_idem]
    exact detCML.map_update_zero _ _
  · simp_rw [killRow_apply_ne hk]
    have := sum_det_symm_eq_zero (jacobian H x) (Ne.symm hk)
      (fun j l => D2 (Pi.single j 1) (Pi.single l 1) k)
      (fun j l => by simp only [hsym (Pi.single j 1)])
    exact this

theorem contDiff_cofactorFn (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H) (i j : Fin n) :
    ContDiff ℝ ∞ (cofactorFn H i j) := by
  have : cofactorFn H i j =
      fun y => detCML (killRow i (entriesCLM (fderiv ℝ H y)) + Pi.single i (Pi.single j 1)) := by
    funext y; rw [detCML_apply, ← update_eq_killRow]; rfl
  rw [this]
  exact detCML.contDiff.comp (((killRow i).contDiff.comp
    (entriesCLM.contDiff.comp (hH.fderiv_right (m := ∞) le_rfl))).add contDiff_const)

theorem integral_det_fderiv_eq_zero (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H)
    (i : Fin n) (hi : HasCompactSupport fun x => H x i) : ∫ x, (fderiv ℝ H x).det = 0 := by
  set h : (Fin n → ℝ) → ℝ := fun x => H x i with hh
  have hhs : ContDiff ℝ ∞ h := (contDiff_apply ℝ (fun _ => ℝ) i).comp hH
  have hJ : ∀ x j, jacobian H x i j = fderiv ℝ h x (Pi.single j 1) := fun x j =>
    jacobian_eq_fderiv_apply H x ((hH.differentiable (by simp)) x) i j
  have hexp : ∀ x, (fderiv ℝ H x).det =
      ∑ j, cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1) := by
    intro x
    rw [det_fderiv_eq_det_jacobian]
    have := det_update_eq_sum (jacobian H x) i (jacobian H x i)
    rw [Function.update_eq_self] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ, mul_comm]; rfl
  have hcof := contDiff_cofactorFn H hH i
  have hcd : ∀ j, Continuous fun x => fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) := fun j =>
    ((hcof j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hhd : ∀ j, Continuous fun x => fderiv ℝ h x (Pi.single j 1) := fun j =>
    (hhs.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : ∀ j, Integrable (fun x => fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) * h x) :=
    fun j => ((hcd j).mul hhs.continuous).integrable_of_hasCompactSupport hi.mul_left
  have i2 : ∀ j, Integrable (fun x => cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1)) :=
    fun j => ((hcof j).continuous.mul (hhd j)).integrable_of_hasCompactSupport
      (hi.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)).mul_left
  have i3 : ∀ j, Integrable (fun x => cofactorFn H i j x * h x) :=
    fun j => ((hcof j).continuous.mul hhs.continuous).integrable_of_hasCompactSupport hi.mul_left
  have hibp : ∀ j, ∫ x, cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1) =
      - ∫ x, fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) * h x := fun j =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (i1 j) (i2 j) (i3 j)
      (fun x _ => ((hcof j).differentiable (by simp)) x)
      (fun x _ => (hhs.differentiable (by simp)) x)
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => i2 j]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ => i1 j]
  simp_rw [← Finset.sum_mul, sum_fderiv_cofactorFn_eq_zero H hH i, zero_mul, integral_zero, neg_zero]

end ChangeOfVariablesDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

set_option maxSynthPendingDepth 1

open scoped ContDiff

open MeasureTheory Metric

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace ChangeOfVariablesDegree

theorem continuous_det_fderiv {n : ℕ} (φ : (Fin n → ℝ) → Fin n → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Continuous fun x => (fderiv ℝ φ x).det := by
  have : (fun x => (fderiv ℝ φ x).det) = fun x => detCML (entriesCLM (fderiv ℝ φ x)) := by
    funext x; rw [det_fderiv_eq_det_jacobian]; rfl
  rw [this]
  exact detCML.cont.comp (entriesCLM.continuous.comp (hφ.continuous_fderiv (by simp)))

theorem hasCompactSupport_comp_sub {n : ℕ} (φ : (Fin n → ℝ) → Fin n → ℝ) (C : ℝ)
    (hC : ∀ x, ‖φ x - x‖ ≤ C) (g : (Fin n → ℝ) → ℝ) (hgc : HasCompactSupport g)
    (y₀ : Fin n → ℝ) : HasCompactSupport fun x => g (φ x - y₀) := by
  obtain ⟨r, hr⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (r + ‖y₀‖ + C))
    fun x hx => ?_
  by_contra hne
  have h1 := hr (subset_tsupport _ hne)
  rw [mem_closedBall_zero_iff] at h1
  apply hx
  rw [mem_closedBall_zero_iff]
  have h2 : ‖x‖ ≤ ‖φ x - y₀‖ + ‖y₀‖ + ‖φ x - x‖ := by
    calc ‖x‖ = ‖(φ x - y₀) + y₀ - (φ x - x)‖ := by congr 1; abel
      _ ≤ ‖(φ x - y₀) + y₀‖ + ‖φ x - x‖ := norm_sub_le _ _
      _ ≤ ‖φ x - y₀‖ + ‖y₀‖ + ‖φ x - x‖ := by gcongr; exact norm_add_le _ _
  linarith [hC x]

theorem clm_apply_eq_sum {n : ℕ} (T : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    T v = ∑ k, v k * T (Pi.single k 1) := by
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin n → ℝ) := by
    ext m; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul]

variable {m : ℕ}

theorem integral_fderiv_comp_mul_det_eq_zero (φ : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hu : HasCompactSupport fun x => φ x - x)
    (g : (Fin (m + 1) → ℝ) → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, fderiv ℝ g (φ x) (Pi.single 0 1) * (fderiv ℝ φ x).det = 0 := by
  obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
  set H : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ := fun x => Function.update (φ x) 0 (g (φ x))
    with hH
  have hH0 : (fun x => H x 0) = fun x => g (φ x) := by
    funext x; simp [hH]
  have hHk : ∀ k, k ≠ 0 → (fun x => H x k) = fun x => φ x k := by
    intro k hk; funext x; simp [hH, hk]
  have hHs : ContDiff ℝ ∞ H := by
    refine contDiff_pi.2 fun k => ?_
    by_cases hk : k = 0
    · subst hk; rw [hH0]; exact hg.comp hφ
    · rw [hHk k hk]; exact (contDiff_apply ℝ (fun _ => ℝ) k).comp hφ
  have hHc : HasCompactSupport fun x => H x 0 := by
    rw [hH0]
    simpa using hasCompactSupport_comp_sub φ C hC g hgc 0
  have hdet : ∀ x, (fderiv ℝ H x).det =
      fderiv ℝ g (φ x) (Pi.single 0 1) * (fderiv ℝ φ x).det := by
    intro x
    have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
    have hgd : DifferentiableAt ℝ g (φ x) := (hg.differentiable (by simp)) (φ x)
    set c : Fin (m + 1) → ℝ := fun k => fderiv ℝ g (φ x) (Pi.single k 1) with hc
    have hJ : Matrix.of (jacobian H x) = (Matrix.of (jacobian φ x)).updateRow 0
        (∑ k, c k • (Matrix.of (jacobian φ x)) k) := by
      ext r l
      rw [Matrix.of_apply, jacobian_eq_fderiv_apply H x ((hHs.differentiable (by simp)) x)]
      by_cases hr : r = 0
      · subst hr
        rw [hH0, Matrix.updateRow_self]
        have : fderiv ℝ (fun y => g (φ y)) x = (fderiv ℝ g (φ x)).comp (fderiv ℝ φ x) :=
          fderiv_comp x hgd hφd
        rw [this, ContinuousLinearMap.comp_apply, clm_apply_eq_sum]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, hc]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [jacobian, mul_comm]
      · rw [hHk r hr, Matrix.updateRow_ne hr, Matrix.of_apply,
          jacobian_eq_fderiv_apply φ x hφd]
    rw [det_fderiv_eq_det_jacobian, hJ, Matrix.det_updateRow_sum, det_fderiv_eq_det_jacobian,
      smul_eq_mul]
  simp_rw [← hdet]
  exact integral_det_fderiv_eq_zero H hHs 0 hHc

theorem integral_comp_sub_mul_det_eq (φ : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hu : HasCompactSupport fun x => φ x - x)
    (f : (Fin (m + 1) → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (s : ℝ) :
    ∫ x, f (φ x - s • (Pi.single 0 1 : Fin (m + 1) → ℝ)) * (fderiv ℝ φ x).det =
      ∫ x, f (φ x) * (fderiv ℝ φ x).det := by
  set e : Fin (m + 1) → ℝ := Pi.single 0 1 with he
  obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
  have hC' : ∀ x, ‖φ x - x‖ ≤ C := hC
  obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨Cf, hCf⟩ := ((hf.continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := e))).bounded_above_of_compact_support (hfc.fderiv_apply (𝕜 := ℝ) e)
  have hdc := continuous_det_fderiv φ hφ
  set Φ : ℝ → ℝ := fun s => ∫ x, f (φ x - s • e) * (fderiv ℝ φ x).det with hΦ
  have hderiv : ∀ s₀, HasDerivAt Φ 0 s₀ := by
    intro s₀
    set R := r + C + (|s₀| + 1) * ‖e‖ with hR
    set F' : ℝ → (Fin (m + 1) → ℝ) → ℝ :=
      fun s x => -(fderiv ℝ f (φ x - s • e) e) * (fderiv ℝ φ x).det with hF'
    have hbound : ∀ᵐ x ∂(volume : Measure (Fin (m + 1) → ℝ)), ∀ s ∈ ball s₀ 1,
        ‖F' s x‖ ≤ (closedBall (0 : Fin (m + 1) → ℝ) R).indicator
          (fun x => Cf * |(fderiv ℝ φ x).det|) x := by
      refine Filter.Eventually.of_forall fun x s hs => ?_
      by_cases hx : x ∈ closedBall (0 : Fin (m + 1) → ℝ) R
      · rw [Set.indicator_of_mem hx]
        simp only [hF', norm_mul, norm_neg, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hCf (φ x - s • e))
          (abs_nonneg _)
      · rw [Set.indicator_of_notMem hx]
        have hnot : φ x - s • e ∉ tsupport f := by
          intro hmem
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          apply hx
          rw [mem_closedBall_zero_iff]
          have hs' : |s| ≤ |s₀| + 1 := by
            rw [mem_ball, Real.dist_eq] at hs
            have := abs_sub_abs_le_abs_sub s s₀
            linarith
          have hse : ‖s • e‖ ≤ (|s₀| + 1) * ‖e‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
          have h2 : ‖x‖ ≤ ‖φ x - s • e‖ + ‖s • e‖ + ‖φ x - x‖ := by
            calc ‖x‖ = ‖(φ x - s • e) + s • e - (φ x - x)‖ := by congr 1; abel
              _ ≤ ‖(φ x - s • e) + s • e‖ + ‖φ x - x‖ := norm_sub_le _ _
              _ ≤ ‖φ x - s • e‖ + ‖s • e‖ + ‖φ x - x‖ := by gcongr; exact norm_add_le _ _
          linarith [hC' x]
        have h0 : fderiv ℝ f (φ x - s • e) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hnot (tsupport_fderiv_subset ℝ h)
        simp [hF', h0]
    have hdiff : ∀ᵐ x ∂(volume : Measure (Fin (m + 1) → ℝ)), ∀ s ∈ ball s₀ 1,
        HasDerivAt (fun s => f (φ x - s • e) * (fderiv ℝ φ x).det) (F' s x) s := by
      refine Filter.Eventually.of_forall fun x s _ => ?_
      have hl : HasDerivAt (fun s : ℝ => φ x - s • e) (-e) s := by
        simpa using ((hasDerivAt_id s).smul_const e).const_sub (φ x)
      have := (((hf.differentiable (by simp)) (φ x - s • e)).hasFDerivAt.comp_hasDerivAt s
        hl).mul_const ((fderiv ℝ φ x).det)
      refine this.congr_deriv ?_
      simp only [hF', map_neg, neg_mul]
    have hcF : ∀ s : ℝ, Continuous fun x => f (φ x - s • e) * (fderiv ℝ φ x).det := fun s =>
      (hf.continuous.comp (hφ.continuous.sub continuous_const)).mul hdc
    have hcF' : Continuous (F' s₀) :=
      (((hf.continuous_fderiv (by simp)).comp (hφ.continuous.sub continuous_const)).clm_apply
        continuous_const).neg.mul hdc
    have hcB : Continuous fun x => Cf * |(fderiv ℝ φ x).det| := continuous_const.mul hdc.abs
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun s x => f (φ x - s • e) * (fderiv ℝ φ x).det) (F' := F') (x₀ := s₀)
      (bound := (closedBall (0 : Fin (m + 1) → ℝ) R).indicator
        fun x => Cf * |(fderiv ℝ φ x).det|)
      (ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => (hcF s).aestronglyMeasurable)
      ((hcF s₀).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_sub φ C hC' f hfc _).mul_right)
      hcF'.aestronglyMeasurable
      hbound
      ((hcB.continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)).integrable_indicator measurableSet_closedBall)
      hdiff
    have h0 : ∫ x, F' s₀ x = 0 := by
      simp only [hF', neg_mul, integral_neg]
      have hg := integral_fderiv_comp_mul_det_eq_zero φ hφ hu (fun y => f (y - s₀ • e))
        (hf.comp (contDiff_id.sub contDiff_const))
        (hfc.comp_homeomorph (Homeomorph.subRight (s₀ • e)))
      simp only [fderiv_comp_sub] at hg
      rw [hg, neg_zero]
    rw [← h0]
    exact key.2
  have hΦd : Differentiable ℝ Φ := fun s => (hderiv s).differentiableAt
  have := is_const_of_deriv_eq_zero hΦd (fun s => (hderiv s).deriv) s 0
  simpa [hΦ] using this

end ChangeOfVariablesDegree

theorem ChangeOfVariablesDegree.proof : ChangeOfVariablesDegree.Statement := by
  intro n φ hφ hu f hf hfc
  cases n with
  | zero =>
    have hid : φ = id := funext fun x => Subsingleton.elim _ _
    subst hid
    simp only [fderiv_id, id_eq, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
      LinearMap.det_id, mul_one]
  | succ m =>
    set e : Fin (m + 1) → ℝ := Pi.single 0 1 with he
    obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
    have hC' : ∀ x, ‖φ x - x‖ ≤ C := hC
    obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
    obtain ⟨ru, hru⟩ := hu.isCompact.isBounded.subset_closedBall 0
    have he1 : ‖e‖ = 1 := by simp [he, Pi.norm_single]
    set R := |r| + |ru| + |C| + 1 with hR
    have hpt : ∀ x, f (φ x - R • e) * (fderiv ℝ φ x).det = f (x - R • e) := by
      intro x
      have hRe : ‖R • e‖ = R := by
        rw [norm_smul, he1, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
      by_cases hx : x ∈ tsupport fun x => φ x - x
      · have hx' := hru hx
        rw [mem_closedBall_zero_iff] at hx'
        have hf1 : f (φ x - R • e) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          have h2 : ‖R • e‖ ≤ ‖φ x - R • e‖ + ‖φ x - x‖ + ‖x‖ := by
            calc ‖R • e‖ = ‖-(φ x - R • e) + (φ x - x) + x‖ := by congr 1; abel
              _ ≤ ‖-(φ x - R • e) + (φ x - x)‖ + ‖x‖ := norm_add_le _ _
              _ ≤ ‖φ x - R • e‖ + ‖φ x - x‖ + ‖x‖ := by
                gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg])
          rw [hRe] at h2
          linarith [hC' x, le_abs_self r, le_abs_self ru, le_abs_self C]
        have hf2 : f (x - R • e) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          have h2 : ‖R • e‖ ≤ ‖x - R • e‖ + ‖x‖ := by
            calc ‖R • e‖ = ‖-(x - R • e) + x‖ := by congr 1; abel
              _ ≤ ‖-(x - R • e)‖ + ‖x‖ := norm_add_le _ _
              _ = ‖x - R • e‖ + ‖x‖ := by rw [norm_neg]
          rw [hRe] at h2
          have := abs_nonneg C
          linarith [le_abs_self r, le_abs_self ru]
        rw [hf1, hf2, zero_mul]
      · rw [notMem_tsupport_iff_eventuallyEq] at hx
        have hev : φ =ᶠ[nhds x] id := hx.mono fun y hy => by simpa [sub_eq_zero] using hy
        have hfd : fderiv ℝ φ x = ContinuousLinearMap.id ℝ _ := by
          rw [hev.fderiv_eq, fderiv_id]
        have hφx : φ x = x := hev.self_of_nhds
        rw [hfd, hφx, ContinuousLinearMap.det,
          ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]
    calc ∫ x, f (φ x) * (fderiv ℝ φ x).det
        = ∫ x, f (φ x - R • e) * (fderiv ℝ φ x).det :=
          (ChangeOfVariablesDegree.integral_comp_sub_mul_det_eq φ hφ hu f hf hfc R).symm
      _ = ∫ x, f (x - R • e) := by simp_rw [hpt]
      _ = ∫ x, f x := integral_sub_right_eq_self f (R • e)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FrameJacobianGeneric : GroundTheory.Heights₂.Heights.FrameJacobianGeneric.Statement :=
  @GroundTheory.Heights₂.Heights.FrameJacobianGeneric.proof GroundTheory.Heights₂.Heights.JacobianRankGeneric.proof GroundTheory.Heights₂.Heights.ConormalGenerationGeneric.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationFinite : GroundTheory.Heights₂.Heights.CurveNormalisationFinite.Statement :=
  @GroundTheory.Heights₂.Heights.CurveNormalisationFinite.proof GroundTheory.Heights₂.Heights.FieldNumbers.NoetherIntegralClosureFinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_jacobian_ne_zero_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CMHeightAddDim.{u} : GroundTheory.Heights₂.Heights.CMHeightAddDim.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.CMHeightAddDim.proof.{u} GroundTheory.Heights₂.Heights.CMRegularElement.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.SliceLocalDimGeneral : GroundTheory.Heights₂.Heights.SliceLocalDimGeneral.Statement :=
  @GroundTheory.Heights₂.Heights.SliceLocalDimGeneral.proof GroundTheory.Heights₂.Heights.LocalDimDomain.proof GroundTheory.Heights₂.Heights.SliceLocalDimUpperZariski.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LengthCutLocalizedModule.{u, v} : GroundTheory.Heights₂.Heights.LengthCutLocalizedModule.Statement.{u, v} :=
  @GroundTheory.Heights₂.Heights.LengthCutLocalizedModule.proof.{u, v} GroundTheory.Heights₂.Heights.LengthCutGlobal.proof GroundTheory.Heights₂.Heights.LengthLocalizedLocalized.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.GenericFibreTor : GroundTheory.Heights₂.Heights.GenericFibreTor.Statement :=
  @GroundTheory.Heights₂.Heights.GenericFibreTor.proof GroundTheory.Heights₂.Heights.GenericFreeness.full

theorem GroundTheory.Heights₂.Heights.AutoClose.local_universal_denominator_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalUniversalDenominator.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalUniversalDenominator.proof GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster.proof GroundTheory.Heights₂.Heights.ComplexSets.RootSumHolomorphic.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.regular_locus_dense_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularLocusDense.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularLocusDense.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CMParameterQuotient : GroundTheory.Heights₂.Heights.CMParameterQuotient.Statement :=
  @GroundTheory.Heights₂.Heights.CMParameterQuotient.proof GroundTheory.Heights₂.Heights.CMRegularElement.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.ChartChangeSheetNull : GroundTheory.Heights₂.Heights.ChartChangeSheetNull.Statement :=
  @GroundTheory.Heights₂.Heights.ChartChangeSheetNull.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.unbranched_proper_count_constant_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.UnbranchedProperCountConstant.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.UnbranchedProperCountConstant.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.UnbranchedProperCountLocallyConstant.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ManifoldZerosComplementConnected.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.sheet_product_analytic_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.UnbranchedFibreSections.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.projection_injective_off_hypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProjectionInjectiveOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProjectionInjectiveOffHypersurface.proof_of_rank GroundTheory.Heights₂.Heights.JacobianRankGeneric.proof GroundTheory.Heights₂.Heights.ConormalGenerationGeneric.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.BranchInCurveComponent : GroundTheory.Heights₂.Heights.BranchInCurveComponent.Statement :=
  @GroundTheory.Heights₂.Heights.BranchInCurveComponent.proof GroundTheory.Heights₂.Heights.BranchInComponent.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NormalCurveJacobian : GroundTheory.Heights₂.Heights.NormalCurveJacobian.Statement :=
  @GroundTheory.Heights₂.Heights.NormalCurveJacobian.proof GroundTheory.Heights₂.Heights.NormalCurvePointDVR.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.brouwer_fixed_point_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BrouwerFixedPoint.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BrouwerFixedPoint.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree.proof
