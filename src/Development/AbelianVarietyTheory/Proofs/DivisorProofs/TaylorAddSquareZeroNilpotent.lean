module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivWordEqCoeff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSubInOfCob2In

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
open Filter Topology

namespace GlobalTheory.PeriodFamily

section Alg

variable {I R D : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing D] [Algebra R D]


omit [DecidableEq I] in
theorem mvAeval_add_of_mul_eq_zero (t n : I → D) (hn : ∀ i j, n i * n j = 0)
    (P : MvPolynomial I R) :
    MvPolynomial.aeval (fun i ↦ t i + n i) P =
      MvPolynomial.aeval t P + ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i P) * n i := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]; ring
  | mul_X p j hp =>
    have h1 : (∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i) * n j = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_assoc, hn, mul_zero]
    have h2 : ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * n i =
        (∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i) * t j +
          MvPolynomial.aeval t p * n j := by
      have h3 : ∀ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * n i =
          MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i * t j +
            if j = i then MvPolynomial.aeval t p * n i else 0 := by
        intro i
        rw [MvPolynomial.pderiv_mul, map_add (f := _), map_mul, map_mul, MvPolynomial.aeval_X,
          MvPolynomial.pderiv_X, Pi.single_apply]
        split_ifs <;> simp <;> ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_mul]
    rw [map_mul, map_mul, hp, h2, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    linear_combination h1

theorem aeval_truncTotal_succ (N : ℕ) (t : I → D) (F : MvPowerSeries I R) :
    MvPolynomial.aeval t (MvPowerSeries.truncTotal (N + 1) F) =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m F • ∏ i, t i ^ m i := by
  have h : MvPowerSeries.truncTotal (N + 1) F =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F) := by
    ext d
    rw [MvPowerSeries.coeff_truncTotal_eq_ite]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true, Finset.sum_ite_eq,
      Finset.mem_range, Finsupp.degree_eq_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Algebra.smul_def]


omit [Fintype I] [DecidableEq I] in
theorem ideal_pow_eq_bot_of_prod {J : Ideal D} {k : ℕ}
    (h : ∀ s : Fin k → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) : J ^ k = ⊥ := by
  rw [Submodule.pow_eq_span_pow_set, Submodule.span_eq_bot]
  intro x hx
  obtain ⟨f, rfl⟩ := Set.mem_pow.1 hx
  rw [List.prod_ofFn]
  exact h _ fun a => (f a).2


omit [DecidableEq I] in
theorem aeval_pderiv_truncTotal_mul {J : Ideal D} {N : ℕ} (hJ : J ^ (N + 1) = ⊥) {t : I → D}
    (ht : ∀ i, t i ∈ J) {x : D} (hx : x ∈ J) (F : MvPowerSeries I R) (i : I) :
    MvPolynomial.aeval t (MvPolynomial.pderiv i (MvPowerSeries.truncTotal (N + 1) F)) * x =
      MvPolynomial.aeval t (MvPowerSeries.truncTotal (N + 1) (MvPowerSeries.pderiv (R := R) i F)) * x := by
  classical
  rw [← sub_eq_zero, ← sub_mul, ← map_sub, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    Finset.sum_mul]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : N ≤ m.degree := by
    by_contra hlt
    refine MvPolynomial.mem_support_iff.1 hm ?_
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_pderiv, MvPowerSeries.coeff_truncTotal _
      (by rw [map_add (f := _), Finsupp.degree_single]; omega), MvPowerSeries.coeff_truncTotal _ (by omega),
      MvPowerSeries.coeff_pderiv, sub_self]
  have h1 : ∏ j, t j ^ m j ∈ J ^ N := by
    refine Ideal.pow_le_pow_right hdeg ?_
    rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun j _ => Ideal.pow_mem_pow (ht j) _
  have h2 : (∏ j, t j ^ m j) * x = 0 := by
    rw [← Ideal.mem_bot, ← hJ, pow_succ]
    exact Ideal.mul_mem_mul h1 hx
  rw [mul_assoc, h2, mul_zero]

end Alg

theorem taylor_add_of_mul_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (n : I → D), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ Ideal.span (Set.range t ∪ Set.range n)) → ∏ a, s a = 0) → (∀ i j, n i * n j = 0) → ∀ f : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N (fun i ↦ t i + n i) f = GlobalTheory.PeriodFamily.taylor N t f + ∑ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ fderiv ℂ f z (Pi.single i 1)) * n i := by
  intro I _ _ D _ _ N t n hs hn f hf
  have key : ∀ (u : I → D) (g : (I → ℂ) → ℂ), AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N u g =
      MvPolynomial.aeval u (MvPowerSeries.truncTotal (N + 1) (GlobalTheory.taylor g)) := fun u g hg => by
    rw [aeval_truncTotal_succ, taylor_eq_sum_coeff_taylor N u g hg]
  rw [key _ _ hf, key _ _ hf, mvAeval_add_of_mul_eq_zero t n hn]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key _ _ (GlobalTheory.analyticAt_fderiv_apply hf _), GlobalTheory.taylor_fderiv hf]
  exact aeval_pderiv_truncTotal_mul (ideal_pow_eq_bot_of_prod hs)
    (fun j => Ideal.subset_span (Or.inl ⟨j, rfl⟩)) (Ideal.subset_span (Or.inr ⟨i, rfl⟩)) _ i

end GlobalTheory.PeriodFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotentStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_add_square_zero_nilpotent : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (n : I → D), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ Ideal.span (Set.range t ∪ Set.range n)) → ∏ a, s a = 0) → (∀ i j, n i * n j = 0) → ∀ f : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N (fun i ↦ t i + n i) f = GlobalTheory.PeriodFamily.taylor N t f + ∑ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ fderiv ℂ f z (Pi.single i 1)) * n i := by
  first | exact @GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero | exact GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero | (intros; apply GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtNatural
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvalNat

theorem evalAt_natural : ∀ {X : Scheme.{0}} {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U), ∃ h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U, (∀ f : Γ(X, U), evalAt (spMap φ ≫ x) U h' f = φ (evalAt x U h f)) ∧ ∀ (U' : X.Opens) (i : U ≤ U') (h'' : ⊤ ≤ x ⁻¹ᵁ U') (f : Γ(X, U')), evalAt x U' h'' f = evalAt x U h ((X.presheaf.map (homOfLE i).op).hom f) := by
  intro X C C' _ _ φ x U h
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ ((spMap φ) p))
  refine ⟨h', fun f ↦ ?_, fun U' i h'' f ↦ ?_⟩
  · have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C')).hom =
        x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫ CommRingCat.ofHom φ := by
      rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
      congr 2
    exact congrArg (fun t ↦ t.hom f) e
  · have e : x.appLE U' ⊤ h'' = X.presheaf.map (homOfLE i).op ≫ x.appLE U ⊤ h := by
      rw [Scheme.Hom.map_appLE]
    unfold evalAt
    rw [e]
    rfl

end GlobalTheory.EvalNat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapValHomFromSpec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

variable {X : Scheme.{0}}

def valHom (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valHom x U h f = valAt' x U f := by
  rw [valAt', dite_eq_left h]; rfl

theorem specMap_valHom_fromSpec (x : Sp ℂ ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    spMap (valHom x U h) ≫ hU.fromSpec = x := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Sp ℂ)) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have e2 : CommRingCat.ofHom (valHom x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := rfl
  rw [spMap, e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem exists_pt_of_affine : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) (W : Opens (Tot I g)), (∀ p ∈ W, p.1 ∈ F.V) → ∀ U : X.Opens, IsAffineOpen U → (∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U) → ∃ x : Sp (Hol W) ⟶ X, ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p := by
  intro I _ g Λ _ F B _ X s σ u W hW U hU hWU
  have han : ∀ f : Γ(X, U), AnalyticOnNhd ℂ (fun p ↦ valAt' (u.E p) U f) W := fun f p hp ↦
    GlobalTheory.SCV.analyticAt_of_differentiableOn (u.hol U f).2 ((u.hol U f).1.mem_nhds ⟨hW p hp, hWU p hp⟩)
  let φ : Γ(X, U) →+* Hol W :=
    (RingHom.pi fun p : W ↦ valHom (u.E p) U (hWU p p.2)).codRestrict (holSub W) fun f ↦
      ⟨fun p ↦ valAt' (u.E p) U f, han f, fun p ↦ valHom_apply _ _ _ f⟩
  refine ⟨spMap φ ≫ hU.fromSpec, ?_, fun p hp ↦ ?_⟩
  · simp [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
  · have e : (Hol.ev p hp).toRingHom.comp φ = valHom (u.E p) U (hWU p hp) := RingHom.ext fun f ↦ rfl
    rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    exact specMap_valHom_fromSpec _ hU _

end GlobalTheory.AnPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfIsProperOfIsHomId
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory

theorem exists_lift_of_isProper_of_isHom_id :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z),
      M.IsHom Y (AlgHom.id o Ω) q → IsProper q → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z),
        ∃ y' : Sp (OO p) ⟶ Y.Z, y' ≫ q = y := by
  intro o Ω _ _ _ Y M q hq hp p _ y
  have hq' : Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt := by
    first | exact hq | exact hq.1 | exact hq.2
  have hsurj : Function.Surjective q := by
    have hc : IsClosed (Set.range q) := q.isClosedMap.isClosed_range
    have hg : genericPoint M.Z ∈ Set.range q := by
      have w : Sp Ω := IsLocalRing.closedPoint Ω
      refine ⟨Y.pt w, ?_⟩
      have h1 : (Y.pt ≫ q) w = (spMap (AlgHom.id o Ω).toRingHom ≫ M.pt) w := by rw [hq']
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, M.pt_apply] at h1
      exact h1
    intro z
    exact (genericPoint_specializes z).mem_closed hc hg
  obtain ⟨K', _, σ, y₁, hσ, hy₁⟩ := exists_finite_ext_point_lift_of_surjective_lft q inferInstance hsurj
    (PadicAlgCl p) (gPt p ≫ y)
  have hbij : Function.Bijective σ := by
    letI := σ.toAlgebra
    haveI : Module.Finite (PadicAlgCl p) K' := hσ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := PadicAlgCl p) (K := K')
  let e := RingEquiv.ofBijective σ hbij
  have he : e.symm.toRingHom.comp σ = RingHom.id _ := RingHom.ext fun x => e.symm_apply_apply x
  have h2 : (spMap e.symm.toRingHom ≫ y₁) ≫ q = gPt p ≫ y := by
    rw [Category.assoc, hy₁, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, he]
    have : spMap (RingHom.id (PadicAlgCl p)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  have hE : ValuativeCriterion.Existence q :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed q) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) q).1
  obtain ⟨⟨l⟩⟩ := hE
    { R := OO p, K := PadicAlgCl p, i₁ := spMap e.symm.toRingHom ≫ y₁, i₂ := y, commSq := ⟨h2⟩ }
  exact ⟨l.l, l.fac_right⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRestrictionEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRestrictionEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem uniformisedOneFormEvaluation_restriction_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V) (ξ : Ω[Sec (str A) U.1⁄ℂ]), ∀ z ∈ pre u.ex V.1, evForm u.ex V.1 z (p1 (OAff (str A)) a ξ) = evForm u.ex U.1 z ξ := by
  intro A _ g L u U V a ξ z hz
  obtain ⟨hopen, -, -, -, -, hmono, -, -, hres, -, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hVU : V.1 ≤ U.1 := leOfHom a.unop
  have hzU : z ∈ pre u.ex U.1 := hmono _ _ hVU hz
  have evV := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u V.1 z hz
  have evU := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hzU
  have hD : ∀ b : Sec (str A) U.1, fderiv ℂ (val u.ex V.1 (Sec.res (str A) hVU b)) z = fderiv ℂ (val u.ex U.1 b) z := by
    intro b
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(hopen V.1).mem_nhds hz] with w hw
    exact hres _ _ hVU b w hw
  have hξ : ξ ∈ Submodule.span (Sec (str A) U.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U.1))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [p1_D, evV.2.2, evU.2.2]
    exact hD b
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul b x _ hx =>
    rw [oneFormsMapOfFunctorMorphism_smul, evV.2.1, evU.2.1, hx]
    congr 1
    exact hres _ _ hVU b z hz

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRestrictionEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evForm_restriction_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V) (ξ : Ω[Sec (str A) U.1⁄ℂ]), ∀ z ∈ pre u.ex V.1, evForm u.ex V.1 z (p1 (OAff (str A)) a ξ) = evForm u.ex U.1 z ξ := by
  first | exact @GlobalTheory.CechPer.uniformisedOneFormEvaluation_restriction_eq | exact GlobalTheory.CechPer.uniformisedOneFormEvaluation_restriction_eq | (intros; apply GlobalTheory.CechPer.uniformisedOneFormEvaluation_restriction_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideBis
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

theorem glue : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ f : ∀ k, Hol (K.W k), (∀ k k' (h : K.le 0 k' k), Charts.sh h (f k) = f k') → ∃ G : Tot I g → ℂ, AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, (f k).fn p = G p) ∧ (∀ (l : Λ) (q : Hol F.V), (∀ k k' (h : K.le l k' k), Charts.sh h (f k) = f k' + K.cst k' q) → ∀ p : Tot I g, p.1 ∈ F.V → G (F.shift l p) = G p + q.fn p.1) ∧ ((∀ k a, dw a (f k) = 0) → ∀ z ∈ F.V, ∀ w, G (z, w) = G (z, 0)) := by
  intro I _ g Λ _ F K hK f hf
  classical
  have indep : ∀ k₁ k₂ p, p ∈ K.W k₁ → p ∈ K.W k₂ → (f k₁).fn p = (f k₂).fn p := by
    intro k₁ k₂ p h₁ h₂
    obtain ⟨k, hk, hl₁, hl₂⟩ := hK.2 0 k₁ k₂ p h₁ (by rw [F.shift_zero]; exact h₂)
    have e₁ := Charts.fn_sh hl₁ (f k₁) hk
    have e₂ := Charts.fn_sh hl₂ (f k₂) hk
    rw [hf k₁ k hl₁, F.shift_zero] at e₁
    rw [hf k₂ k hl₂, F.shift_zero] at e₂
    rw [← e₁, ← e₂]
  let G : Tot I g → ℂ := fun p ↦ if h : ∃ k, p ∈ K.W k then (f h.choose).fn p else 0
  have hG : ∀ k, ∀ p ∈ K.W k, (f k).fn p = G p := by
    intro k p hp
    have h : ∃ k, p ∈ K.W k := ⟨k, hp⟩
    simp only [G, dif_pos h]
    exact indep _ _ _ hp h.choose_spec
  have hGev : ∀ k, ∀ p ∈ K.W k, G =ᶠ[𝓝 p] (f k).fn := fun k p hp ↦ by
    filter_upwards [(K.W k).isOpen.mem_nhds hp] with q hq using (hG k q hq).symm
  refine ⟨G, ?_, hG, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, hk⟩ := hK.1 p hp
    exact ((f k).analytic p hk).congr (hGev k p hk).symm
  · intro l q hq p hp
    obtain ⟨k₁, h₁⟩ := hK.1 p hp
    obtain ⟨k₂, h₂⟩ := hK.1 (F.shift l p) hp
    obtain ⟨k, hk, -, hl⟩ := hK.2 l k₁ k₂ p h₁ h₂
    have e := congrArg (fun u ↦ Hol.fn u p) (hq k₂ k hl)
    rw [Charts.fn_sh hl _ hk, Hol.fn_add _ _ hk, Charts.fn_cst K k q hk] at e
    rw [← hG k₂ _ h₂, ← hG k p hk, e]
  · intro h0 z hz w
    have hder : ∀ w' : Fin g → ℂ, HasFDerivAt (fun u ↦ G (z, u)) (0 : (Fin g → ℂ) →L[ℂ] ℂ) w' := by
      intro w'
      obtain ⟨k, hk⟩ := hK.1 (z, w') hz
      have hfd : HasFDerivAt (fun u : Fin g → ℂ ↦ ((z, u) : Tot I g))
          (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ)) w' :=
        (hasFDerivAt_const z w').prodMk (hasFDerivAt_id w')
      have hGd : HasFDerivAt G (fderiv ℂ (f k).fn (z, w')) (z, w') := by
        rw [← (hGev k _ hk).fderiv_eq]
        exact (((f k).analytic _ hk).differentiableAt.congr_of_eventuallyEq (hGev k _ hk)).hasFDerivAt
      have hL : (fderiv ℂ (f k).fn (z, w')).comp (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ)) = 0 := by
        have hs : ∀ a : Fin g, fderiv ℂ (f k).fn (z, w') ((0, Pi.single a 1) : Tot I g) = 0 := by
          intro a
          have := Hol.fn_der ((0, Pi.single a 1) : Tot I g) (f k) hk
          rw [show Hol.der _ (f k) = dw a (f k) from rfl, h0 k a, ← Hol.ev_apply _ hk, map_zero] at this
          exact this.symm
        refine ContinuousLinearMap.ext fun v ↦ ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Finset.univ_sum_single v, map_sum, ContinuousLinearMap.zero_apply]
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        have e : Pi.single a (v a) = v a • (Pi.single a 1 : Fin g → ℂ) := by
          rw [← Pi.single_smul]; simp
        rw [e, map_smul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hs a, smul_zero]
      have := hGd.comp w' hfd
      rw [hL] at this
      exact this
    exact is_const_of_fderiv_eq_zero (fun w' ↦ (hder w').differentiableAt) (fun w' ↦ (hder w').fderiv) w 0

end GlobalTheory.AnPer.Charts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLeibniz
namespace GlobalTheory.TensorLeibnizRule

open TensorProduct

theorem lTensor_leibniz {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) (x y : TensorProduct ℂ R S) :
    (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) (x * y) =
      x * (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) y +
      y * (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' s' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, TensorProduct.tmul_add]
      rw [mul_comm r' r]
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, map_add (f := _), h₁, h₂, map_add (f := _), mul_add, add_mul]
      abel
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, map_add (f := _), h₁, h₂, map_add (f := _), add_mul, mul_add]
    abel

end GlobalTheory.TensorLeibnizRule
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroMove

theorem gen_hom {A C : Type} [CommRing A] [CommRing C] {g : ℕ} (ψ : A →+* C) (D : Fin g → A →+ A)
    (h1 : ∀ a, D a 1 = 0) (hL : ∀ a x y, D a (x * y) = x * D a y + y * D a x)
    (n : Fin g → C) (hn : ∀ a b, n a * n b = 0) :
    ∃ ψ' : A →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (D a x) * n a := by
  have hsq : ∀ (u v : Fin g → C), (∑ a, u a * n a) * (∑ b, v b * n b) = 0 := by
    intro u v
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    calc u a * n a * (v b * n b) = u a * v b * (n a * n b) := by ring
      _ = 0 := by rw [hn a b, mul_zero]
  refine ⟨{ toFun := fun x => ψ x + ∑ a, ψ (D a x) * n a,
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun x => rfl⟩
  · simp [h1]
  · intro x y
    have e := hsq (fun a => ψ (D a x)) (fun a => ψ (D a y))
    simp only [hL, map_add (f := _), map_mul, add_mul, Finset.sum_add_distrib]
    have ex : ∑ a, ψ x * ψ (D a y) * n a = ψ x * ∑ a, ψ (D a y) * n a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    have ey : ∑ a, ψ y * ψ (D a x) * n a = ψ y * ∑ a, ψ (D a x) * n a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [ex, ey]
    linear_combination (-1 : C) * e
  · simp
  · intro x y
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]
    ring

theorem lTensor_leibniz {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) (x y : R ⊗[ℂ] S) :
    LinearMap.lTensor R d.toLinearMap (x * y) =
      x * LinearMap.lTensor R d.toLinearMap y + y * LinearMap.lTensor R d.toLinearMap x := by
  first
  | exact @_root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz
  | exact _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz
  | (apply _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz ..)

theorem lTensor_one {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) : LinearMap.lTensor R d.toLinearMap (1 : R ⊗[ℂ] S) = 0 := by
  rw [Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
    TensorProduct.tmul_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem sqZeroMove : ∀ {g : ℕ} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (ψ : R ⊗[ℂ] Hol W₀ →+* C) (n : Fin g → C), (∀ a b, n a * n b = 0) → ∃ ψ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (LinearMap.lTensor R (dw a).toLinearMap x) * n a := by
  intro g W₀ R _ _ C _ ψ n hn
  exact gen_hom ψ (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
    (fun a => lTensor_one _) (fun a x y => lTensor_leibniz _ x y) n hn

end GlobalTheory.SqZeroMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphicStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZero_move_tensor_holomorphic :
    ∀ {g : ℕ} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R]
      {C : Type} [CommRing C] (ψ : R ⊗[ℂ] Hol W₀ →+* C) (n : Fin g → C),
      (∀ a b, n a * n b = 0) → ∃ ψ' : R ⊗[ℂ] Hol W₀ →+* C,
        ∀ x, ψ' x = ψ x + ∑ a, ψ (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap x) * n a := by
  intro g W₀ R _ _ C _ ψ n hn
  have hMove := GlobalTheory.SqZeroMove.gen_hom ψ
    (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
    (fun a => GlobalTheory.SqZeroMove.lTensor_one (R := R) (dw (W := W₀) a))
    (fun a x y => GlobalTheory.SqZeroMove.lTensor_leibniz (dw (W := W₀) a) x y) n hn
  exact hMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLogWithLinearPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLogWithLinearPart
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.LogLin

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

theorem mvPowerSeriesMap_evalTwoGroups (h : R →+* S) {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (at2 c u v) = at2 (map h c) (fun i => map h (u i)) (fun i => map h (v i)) := by
  unfold at2
  rw [map_subst (CobCob.elim_has hu hv)]
  congr 1
  funext j
  cases j <;> rfl

theorem map_op (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {τ : Type}
    {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    op (fun i => map h (μ i)) (fun i => map h (u i)) (fun i => map h (v i)) =
      fun i => map h (op μ u v i) :=
  funext fun i => (mvPowerSeriesMap_evalTwoGroups h hu hv (μ i)).symm

theorem map_threeGroupsFirstVariables (h : R →+* S) : (fun i => map h (x1 (R := R) (d := d) i)) = x1 := by
  funext i; simp [x1]

theorem map_threeGroupsSecondVariables (h : R →+* S) : (fun i => map h (x2 (R := R) (d := d) i)) = x2 := by
  funext i; simp [x2]

theorem map_threeGroupsThirdVariables (h : R →+* S) : (fun i => map h (x3 (R := R) (d := d) i)) = x3 := by
  funext i; simp [x3]

theorem map_assoc (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0) (ha : op μ (op μ x1 x2) x3 = op μ x1 (op μ x2 x3)) :
    op (fun i => map h (μ i)) (op (fun i => map h (μ i)) x1 x2) x3 =
      op (fun i => map h (μ i)) x1 (op (fun i => map h (μ i)) x2 x3) := by
  have h12 := CobCob.op_const hc (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
  have h23 := CobCob.op_const hc (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
  rw [← map_threeGroupsFirstVariables h, ← map_threeGroupsSecondVariables h, ← map_threeGroupsThirdVariables h, map_op h μ CobCob.constantCoeff_threeGroupsFirstVariables CobCob.constantCoeff_threeGroupsSecondVariables,
    map_op h μ CobCob.constantCoeff_threeGroupsSecondVariables CobCob.constantCoeff_threeGroupsThirdVariables, map_op h μ h12 CobCob.constantCoeff_threeGroupsThirdVariables,
    map_op h μ CobCob.constantCoeff_threeGroupsFirstVariables h23, ha]

theorem map_swap (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (swap c) = swap (map h c) := by
  unfold swap
  rw [mvPowerSeriesMap_evalTwoGroups h (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_formalGroupLawCoboundaryOne_eq (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    map h (cob1 μ f) = cob1 (fun i => map h (μ i)) (map h f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hc),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem constantCoeff_formalGroupLawCoboundaryOne_eq_zero (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0) {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (cob1 μ f) = 0 := by
  unfold cob1 inL inR
  rw [map_sub, map_sub,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hc) hc hf,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) hf,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) hf, sub_zero, sub_zero]

theorem lin_form (w : Fin d → R) (i : Fin d) :
    lin (∑ j, w j • (X j : MvPowerSeries (Fin d) R)) i = w i := by
  classical
  unfold lin
  simp [coeff_X, Finsupp.single_left_inj]

end GlobalTheory.QLog.LogLin


open GlobalTheory.QLog.LogLin in
theorem GlobalTheory.QLog.exists_log_of_lin : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ w : Fin d → O, ∃ f : MvPowerSeries (Fin d) C, constantCoeff f = 0 ∧ (∀ i, lin f i = algebraMap O C (w i)) ∧ cob1 (up C μ) f = 0 := by
  intro p _ O C _ _ _ hF d μ hμ w
  classical
  let F : MvPowerSeries (Fin d) O := ∑ j, w j • (X j : MvPowerSeries (Fin d) O)
  have hF0 : constantCoeff F = 0 := by simp [F]
  let h : O →+* C := algebraMap O C
  have hup : up C μ = fun i => map h (μ i) := rfl
  have hc' : ∀ i, constantCoeff (up C μ i) = 0 := fun i => by
    rw [hup]; simp only [constantCoeff_map, hμ.const i, map_zero]
  have hcmap : cob1 (up C μ) (map h F) = map h (cob1 μ F) :=
    (map_formalGroupLawCoboundaryOne_eq h μ hμ.const F).symm
  have hlift : IsLift (RingHom.id O) μ :=
    ⟨hμ.const, hμ.unit, hμ.comm, by simpa using hμ⟩
  have rules := formalGroupLawCoboundaryTwo_coboundaryOne_alt C d (up C μ) hc' (map h F)
  have hass : op (up C μ) (op (up C μ) x1 x2) x3 = op (up C μ) x1 (op (up C μ) x2 x3) :=
    map_assoc h μ hμ.const hμ.assoc
  have hcomm : (fun i => swap (up C μ i)) = up C μ := by
    funext i; rw [hup]; dsimp only; rw [← map_swap, hμ.comm i]
  obtain ⟨g, hg0, hglin, -, hgc⟩ := GlobalTheory.T.swap_sub_in_of_cob2_in p O O C (RingHom.id O) hF d μ hlift ⊥ ⊤ bot_le
    (cob1 (up C μ) (map h F)) (Or.inl hμ)
    (by rw [hcmap, constantCoeff_map, constantCoeff_formalGroupLawCoboundaryOne_eq_zero μ hμ.const hF0, map_zero])
    (fun α => ⟨0, coeff α (cob1 μ F), Submodule.mem_top, by
      rw [pow_zero, one_mul, hcmap, coeff_map]⟩)
    (fun α => ⟨0, Submodule.zero_mem _, by
      rw [rules.1, hass, sub_self, map_zero, map_zero]⟩)
    (fun α => ⟨0, Submodule.zero_mem _, by
      rw [rules.2.1, hcomm, sub_self, map_zero, map_zero]⟩)
  have hzero : cob1 (up C μ) (map h F) - cob1 (up C μ) g = 0 := by
    ext α
    obtain ⟨b, hb, he⟩ := hgc α
    rw [Ideal.mem_bot] at hb
    rw [he, hb, map_zero, map_zero]
  refine ⟨map h F - g, ?_, fun i => ?_, ?_⟩
  · rw [map_sub, constantCoeff_map, hF0, map_zero, hg0, sub_zero]
  · have := congrFun hglin i
    unfold lin at this ⊢
    rw [map_sub, coeff_map, this, Pi.zero_apply, sub_zero]
    exact congrArg h (lin_form w i)
  · rw [sub_eq_add_neg, formalCoboundary_add hc', ← neg_one_smul C g, formalCoboundary_smul hc', neg_one_smul,
      ← sub_eq_add_neg, hzero]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLogWithLinearPartStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ w : Fin d → O, ∃ f : MvPowerSeries (Fin d) C, constantCoeff f = 0 ∧ (∀ i, lin f i = algebraMap O C (w i)) ∧ cob1 (up C μ) f = 0 := by
  first | exact @GlobalTheory.QLog.exists_log_of_lin | exact GlobalTheory.QLog.exists_log_of_lin | (intros; apply GlobalTheory.QLog.exists_log_of_lin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleModIdealEqCoboundaryQuasiLog
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleModIdealEqCoboundaryQuasiLog
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CocLift

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem hasSubst_elim (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

theorem powerSeriesEvalTwoGroups_smul (c : MvPowerSeries (Fin d ⊕ Fin d) R) (r : R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (r • c) u v = r • at2 c u v :=
  subst_smul (hasSubst_elim u v hu hv) r c

theorem constantCoeff_powerSeriesEvalTwoGroups_zero (c : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (hc : constantCoeff c = 0) : constantCoeff (at2 c u v) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim u v hu hv) (fun s => by cases s <;> simp [hu, hv]) hc

theorem mvPowerSeriesMap_evalTwoGroups (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    map h (at2 c u v) = at2 (map h c) (fun i => map h (u i)) (fun i => map h (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_elim u v hu hv)]
  congr 1
  funext s
  cases s <;> rfl

theorem constantCoeff_threeGroupsFirstVariables_eq_zero : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
theorem constantCoeff_threeGroupsSecondVariables_eq_zero : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
theorem constantCoeff_threeGroupsThirdVariables_eq_zero : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _

theorem cOp (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : ∀ i, constantCoeff (op μ u v i) = 0 :=
  fun i => constantCoeff_powerSeriesEvalTwoGroups_zero _ u v hu hv (hμ i)

theorem formalGroupLawCoboundaryTwo_smul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (r : R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) : cob2 μ (r • c) = r • cob2 μ c := by
  unfold cob2
  rw [powerSeriesEvalTwoGroups_smul _ _ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, powerSeriesEvalTwoGroups_smul _ _ _ _ (cOp μ hμ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero) constantCoeff_threeGroupsThirdVariables_eq_zero,
    powerSeriesEvalTwoGroups_smul _ _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero (cOp μ hμ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero), powerSeriesEvalTwoGroups_smul _ _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero]
  simp only [smul_sub, smul_add]

theorem map_threeGroupsFirstVariables (h : R →+* S) : (fun i => map h (x1 (R := R) (d := d) i)) = x1 := by
  funext i; simp [x1]
theorem map_threeGroupsSecondVariables (h : R →+* S) : (fun i => map h (x2 (R := R) (d := d) i)) = x2 := by
  funext i; simp [x2]
theorem map_threeGroupsThirdVariables (h : R →+* S) : (fun i => map h (x3 (R := R) (d := d) i)) = x3 := by
  funext i; simp [x3]

theorem map_op (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => map h (op μ u v i)) = op (fun i => map h (μ i)) (fun i => map h (u i)) (fun i => map h (v i)) := by
  funext i
  exact mvPowerSeriesMap_evalTwoGroups h _ u v hu hv

theorem map_formalGroupLawCoboundaryTwo (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (cob2 μ c) = cob2 (fun i => map h (μ i)) (map h c) := by
  unfold cob2
  simp only [map_sub, map_add (f := _)]
  rw [mvPowerSeriesMap_evalTwoGroups h _ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, mvPowerSeriesMap_evalTwoGroups h _ _ _ (cOp μ hμ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero) constantCoeff_threeGroupsThirdVariables_eq_zero,
    mvPowerSeriesMap_evalTwoGroups h _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero (cOp μ hμ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero), mvPowerSeriesMap_evalTwoGroups h _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero,
    map_op h μ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero, map_op h μ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, map_threeGroupsFirstVariables, map_threeGroupsSecondVariables, map_threeGroupsThirdVariables]

theorem cYX : ∀ i : Fin d, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
  fun i => constantCoeff_X _
theorem cXX : ∀ i : Fin d, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
  fun i => constantCoeff_X _

theorem swap_smul (r : R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) : swap (r • c) = r • swap c :=
  powerSeriesEvalTwoGroups_smul c r _ _ cYX cXX

theorem map_swap (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (swap c) = swap (map h c) := by
  unfold swap
  rw [mvPowerSeriesMap_evalTwoGroups h _ _ _ cYX cXX]
  simp

end GlobalTheory.CocLift

namespace GlobalTheory.CocLift

theorem cocycle_lift : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (a : O), a ∣ p → ∀ c : MvPowerSeries (Fin d ⊕ Fin d) O, constantCoeff c = 0 → (∀ α, a ∣ coeff α (cob2 μ c)) → (∀ α, a ∣ coeff α (swap c - c)) → ∃ g : MvPowerSeries (Fin d) C, QL μ ⊤ g ∧ lin g = 0 ∧ In (Ideal.span {a}) (cob1 (up C μ) g - map (algebraMap O C) c) := by
  intro p _ O C _ _ _ hF d μ hμ a ha c hc0 hcob hsw
  set A : C := algebraMap O C a with hA
  have hAu : IsUnit A := by
    obtain ⟨b, hb⟩ := ha
    have : (p : C) = A * algebraMap O C b := by rw [hA, ← map_mul, ← hb, map_natCast]
    exact isUnit_of_mul_isUnit_left (this ▸ hF.unit_p)
  obtain ⟨u, hu⟩ := hAu
  set ai : C := ↑u⁻¹ with hai
  have hAai : A * ai = 1 := by rw [hai, ← hu, Units.mul_inv]
  have hμc : ∀ i, constantCoeff (up C μ i) = 0 := fun i => by
    simp [up, hμ.const i]
  set c' : MvPowerSeries (Fin d ⊕ Fin d) C := ai • map (algebraMap O C) c with hc'
  have hlift : IsLift (RingHom.id O) μ := by
    refine ⟨hμ.const, hμ.unit, hμ.comm, ?_⟩
    have : (fun i => map (RingHom.id O) (μ i)) = μ := by
      funext i; ext α; simp [coeff_map]
    rw [this]; exact hμ
  have hc'0 : constantCoeff c' = 0 := by
    simp [hc', hc0]
  have hden : ∀ α, ∃ k : ℕ, ∃ b ∈ (⊤ : Ideal O), (p : C) ^ k * coeff α c' = algebraMap O C b := by
    intro α
    obtain ⟨k, b, hb⟩ := hF.denom (coeff α c')
    exact ⟨k, b, Submodule.mem_top, hb⟩
  have hcob' : In (⊤ : Ideal O) (cob2 (up C μ) c') := by
    intro α
    obtain ⟨b, hb⟩ := hcob α
    refine ⟨b, Submodule.mem_top, ?_⟩
    have h1 : cob2 (up C μ) c' = ai • map (algebraMap O C) (cob2 μ c) := by
      rw [hc', formalGroupLawCoboundaryTwo_smul _ hμc, map_formalGroupLawCoboundaryTwo _ _ hμ.const]; rfl
    rw [h1, coeff_smul, coeff_map, hb, map_mul, ← mul_assoc, mul_comm ai, hAai, one_mul]
  have hsw' : In (⊤ : Ideal O) (swap c' - c') := by
    intro α
    obtain ⟨b, hb⟩ := hsw α
    refine ⟨b, Submodule.mem_top, ?_⟩
    have h1 : swap c' - c' = ai • map (algebraMap O C) (swap c - c) := by
      rw [hc', swap_smul, map_sub, map_swap, smul_sub]
    rw [h1, coeff_smul, coeff_map, hb, map_mul, ← mul_assoc, mul_comm ai, hAai, one_mul]
  obtain ⟨g', hg0, hglin, -, hgIn⟩ := GlobalTheory.T.swap_sub_in_of_cob2_in p O O C (RingHom.id O) hF d μ hlift ⊤ ⊤ le_rfl c'
    (Or.inl hμ) hc'0 hden hcob' hsw'
  have hcob1 : cob1 (up C μ) (A • g') = A • cob1 (up C μ) g' := formalCoboundary_smul hμc A g'
  have hlin : lin (A • g') = 0 := by
    funext i
    have := congrFun hglin i
    simp only [lin, coeff_smul, Pi.zero_apply] at this ⊢
    rw [this, mul_zero]
  refine ⟨A • g', ⟨?_, ?_, ?_⟩, hlin, ?_⟩
  · simp [hg0]
  · intro i; exact ⟨0, Submodule.mem_top, by rw [hlin, map_zero]; rfl⟩
  · intro α
    obtain ⟨b, -, hb⟩ := hgIn α
    refine ⟨coeff α c - a * b, Submodule.mem_top, ?_⟩
    have e : coeff α (cob1 (up C μ) g') = coeff α c' - algebraMap O C b := by
      rw [← hb, map_sub]; ring
    rw [hcob1, coeff_smul, e, hc', coeff_smul, coeff_map, map_sub, map_mul]
    linear_combination (algebraMap O C (coeff α c)) * hAai
  · intro α
    obtain ⟨b, -, hb⟩ := hgIn α
    refine ⟨a * (-b), Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a), ?_⟩
    have e : coeff α (cob1 (up C μ) g') = coeff α c' - algebraMap O C b := by
      rw [← hb, map_sub]; ring
    rw [map_sub, hcob1, coeff_smul, e, hc', coeff_smul, coeff_map, map_mul, map_neg]
    linear_combination (algebraMap O C (coeff α c)) * hAai

end GlobalTheory.CocLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleModIdealEqCoboundaryQuasiLogStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricCocycle_modIdeal_eq_coboundary_quasiLog : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (a : O), a ∣ p → ∀ c : MvPowerSeries (Fin d ⊕ Fin d) O, constantCoeff c = 0 → (∀ α, a ∣ coeff α (cob2 μ c)) → (∀ α, a ∣ coeff α (swap c - c)) → ∃ g : MvPowerSeries (Fin d) C, QL μ ⊤ g ∧ lin g = 0 ∧ In (Ideal.span {a}) (cob1 (up C μ) g - map (algebraMap O C) c) := by
  first | exact @GlobalTheory.CocLift.cocycle_lift | exact GlobalTheory.CocLift.cocycle_lift | (intros; apply GlobalTheory.CocLift.cocycle_lift <;> assumption)
end
end
