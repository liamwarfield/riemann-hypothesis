module

public import Formalism.DegreeFormula.PointDegree.PowSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFinite
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvalues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingOpenSubgroupsFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula
open MvPolynomial Finset Formalism.DegreeFormula

namespace GlobalTheory.FlagPoly

open MvPolynomial Finset in
private theorem coeff_linearForm_pow_eq_factorial_mul_prod {σ : Type} [Fintype σ] [DecidableEq σ] (c : σ → ℝ) (n : ℕ)
    (d : σ →₀ ℕ) (hd : d.degree = n) :
    AddMonoidAlgebra.coeff ((∑ x, C (c x) * X x) ^ n) d =
      (n.factorial : ℝ) * ∏ x, (c x ^ d x / ((d x).factorial : ℝ)) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    ← map_natCast (C : ℝ →+* MvPolynomial σ ℝ), ← mul_assoc, ← map_mul, coeff_C_mul,
    coeff_prod_X_pow]
  have hsum : ∑ i, d i = n := by
    rw [← hd, Finsupp.degree_eq_sum]
  rw [Finset.sum_eq_single (⇑d)]
  · have hind : d = Finsupp.indicator univ (fun i _ => d i) := by
      ext i; simp
    rw [if_pos hind, mul_one]
    have hspec := Nat.multinomial_spec (univ : Finset σ) (⇑d)
    rw [hsum] at hspec
    have hpos : (∏ i, ((d i).factorial : ℝ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; intro i _; exact_mod_cast (Nat.factorial_pos _).ne'
    rw [Finset.prod_div_distrib, ← hspec]
    push_cast
    field_simp
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro h
    apply hk
    funext i
    have := congrArg (fun f : σ →₀ ℕ => f i) h
    simpa using this.symm
  · intro h
    exfalso; apply h
    rw [Finset.mem_piAntidiag]
    exact ⟨hsum, fun i _ => Finset.mem_univ i⟩

open MvPolynomial Finset in
private theorem prod_factorial_rev_eq_prod_sub (N : ℕ) :
    ∏ j : Fin N, ((j.rev : ℕ).factorial : ℝ) =
      ∏ i : Fin N, ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
  cases N with
  | zero => simp
  | succ n =>
    have h1 : ∏ i : Fin (n + 1), ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) =
        (n.superFactorial : ℝ) := by
      rw [← Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) n, Matrix.det_vandermonde]
    rw [h1, ← Nat.prod_range_succ_factorial, Nat.cast_prod,
      ← Fin.prod_univ_eq_prod_range (fun x => ((x.factorial : ℕ) : ℝ)) (n + 1)]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun j => rfl)

open MvPolynomial Finset in
private theorem sum_sign_prod_pow_div_factorial_eq_prod {N : ℕ} (v : Fin N → ℝ) :
    ∑ π : Equiv.Perm (Fin N), ((Equiv.Perm.sign π : ℤ) : ℝ) *
        ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) =
      ∏ i : Fin N, ∏ k : Fin N,
        if i < k then (v i - v k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1 := by
  have hrev : ∀ j : Fin N, N - 1 - (j : ℕ) = (j.rev : ℕ) := by
    intro j; rw [Fin.val_rev]; omega
  have hterm : ∀ π : Equiv.Perm (Fin N),
      ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) =
        (∏ i, Matrix.transpose (Matrix.projVandermonde 1 v) (π i) i) *
          ∏ j : Fin N, (((j.rev : ℕ).factorial : ℝ))⁻¹ := by
    intro π
    simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib, hrev]
    congr 1
    · simp [Matrix.projVandermonde_apply]
    · exact Fintype.prod_equiv π _ _ (fun i => rfl)
  simp_rw [hterm, ← mul_assoc, ← Finset.sum_mul, ← Matrix.det_apply', Matrix.det_transpose,
    Matrix.det_projVandermonde, Finset.prod_inv_distrib, prod_factorial_rev_eq_prod_sub,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_div_distrib, div_eq_mul_inv]
  simp only [Pi.one_apply, one_mul]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  congr 1
  ext k
  simp


open MvPolynomial Finset in
theorem _root_.GlobalTheory.FlagPoly.flagDegFormula : _root_.Formalism.DegreeFormula.FlagDegFormula := by
  unfold _root_.Formalism.DegreeFormula.FlagDegFormula
  intro ι _ _ N lam
  unfold _root_.Formalism.DegreeFormula.flagDeg _root_.Formalism.DegreeFormula.weylProd _root_.Formalism.DegreeFormula.linRoot
  rw [neg_pow, ← map_one (C : ℝ →+* MvPolynomial (ι × Fin N) ℝ), ← map_neg, ← map_pow, _root_.Formalism.DegreeFormula.PPowSum.degFl_C_mul]
  unfold _root_.Formalism.DegreeFormula.degFl
  simp_rw [coeff_linearForm_pow_eq_factorial_mul_prod _ _ _ (_root_.Formalism.DegreeFormula.PPowSum.degree_permExp _)]
  have hexp : ∀ (σ : ι → Equiv.Perm (Fin N)) (τ : ι) (i : Fin N),
      (_root_.Formalism.DegreeFormula.permExp σ) (τ, i) = N - 1 - ((σ τ) i : ℕ) := by
    intro σ τ i
    unfold _root_.Formalism.DegreeFormula.permExp
    rfl
  simp_rw [Fintype.prod_prod_type, hexp]
  rw [← Finset.prod_congr rfl (fun τ _ => sum_sign_prod_pow_div_factorial_eq_prod (lam τ)),
    Fintype.prod_sum]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.FlagPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjOfIsConjGlFieldExtensionInclusion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjOfIsConjGlFieldExtensionInclusion
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.ConjDesc

noncomputable section

theorem smul_of_X {F : Type} [Field F] {M N : Type} [AddCommGroup M] [Module F M] [Module F[X] M]
    [IsScalarTower F F[X] M] [AddCommGroup N] [Module F N] [Module F[X] N] [IsScalarTower F F[X] N]
    (e : M ≃ₗ[F] N) (h : ∀ m, e ((X : F[X]) • m) = (X : F[X]) • e m) (p : F[X]) (m : M) :
    e (p • m) = p • e m := by
  revert m
  induction p using Polynomial.induction_on with
  | C a =>
    intro m
    rw [← Polynomial.algebraMap_eq, algebraMap_smul, algebraMap_smul]
    exact e.map_smul a m
  | add p q hp hq =>
    intro m
    rw [add_smul, add_smul, map_add (f := _), hp, hq]
  | monomial k a ih =>
    intro m
    rw [pow_succ, ← mul_assoc, mul_smul (C a * X ^ k) X m, ih, h, ← mul_smul]

def equivOfX {F : Type} [Field F] {M N : Type} [AddCommGroup M] [Module F M] [Module F[X] M]
    [IsScalarTower F F[X] M] [AddCommGroup N] [Module F N] [Module F[X] N] [IsScalarTower F F[X] N]
    (e : M ≃ₗ[F] N) (h : ∀ m, e ((X : F[X]) • m) = (X : F[X]) • e m) : M ≃ₗ[F[X]] N :=
  { e with
    map_smul' := fun p m => smul_of_X e h p m }

def swapE (F : Type) [Field F] (a b : ℕ) : (Fin a → Fin b → F) ≃ₗ[F] (Fin b → Fin a → F) :=
  { Equiv.piComm (fun (_ : Fin a) (_ : Fin b) => F) with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

def coordE {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ) :
    (Fin n → F') ≃ₗ[F] (Fin l → Fin n → F) :=
  (LinearEquiv.piCongrRight fun _ : Fin n => b.equivFun).trans (swapE F n l)

theorem coordE_apply {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ)
    (v : Fin n → F') (k : Fin l) (i : Fin n) : coordE b n v k i = b.equivFun (v i) k := rfl

theorem coordE_mulVec {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ)
    (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F') :
    coordE b n (Matrix.mulVec (A.map (algebraMap F F')) v) = fun k => Matrix.mulVec A (coordE b n v k) := by
  funext k i
  rw [coordE_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, ← Algebra.smul_def, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordE_apply]

end

end GlobalTheory.Shin.ConjDesc

namespace GlobalTheory.Shin


open ConjDesc in
theorem isConj_of_isConj_incl : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (n : ℕ)
    (γ γ' : GL (Fin n) F), IsConj (incl F F' n γ) (incl F F' n γ') → IsConj γ γ' := by
  intro F F' _ _ _ _ n γ γ' hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hcA : (c : Matrix (Fin n) (Fin n) F') * ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) =
      ((γ' : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) * (c : Matrix (Fin n) (Fin n) F') := by
    have h2 : c * incl F F' n γ = incl F F' n γ' * c := by rw [← hc]; group
    exact congrArg (fun x : GL (Fin n) F' => (x : Matrix (Fin n) (Fin n) F')) h2
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : FiniteDimensional F F' := inferInstance
  have hl : 0 < Module.finrank F F' := Module.finrank_pos
  let b := Module.finBasis F F'
  let f := Matrix.toLin' (γ : Matrix (Fin n) (Fin n) F)
  let g := Matrix.toLin' (γ' : Matrix (Fin n) (Fin n) F)
  let Fc : (Fin n → F') ≃ₗ[F] (Fin n → F') :=
    (LinearEquiv.ofLinear (Matrix.toLin' (c : Matrix (Fin n) (Fin n) F'))
      (Matrix.toLin' ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F'))
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])).restrictScalars F
  have hFc : ∀ w, Fc w = Matrix.mulVec (c : Matrix (Fin n) (Fin n) F') w := fun w => rfl
  let core : (Fin (Module.finrank F F') → Fin n → F) ≃ₗ[F] (Fin (Module.finrank F F') → Fin n → F) :=
    (coordE b n).symm.trans (Fc.trans (coordE b n))
  have hcore : ∀ x, core (fun k => f (x k)) = fun k => g (core x k) := by
    intro x
    obtain ⟨v, rfl⟩ := (coordE b n).surjective x
    have h1 : (fun k => f (coordE b n v k)) =
        coordE b n (Matrix.mulVec ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) v) := by
      rw [coordE_mulVec]; rfl
    rw [h1]
    show coordE b n (Fc ((coordE b n).symm (coordE b n
        (Matrix.mulVec ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) v)))) =
      fun k => g (coordE b n (Fc ((coordE b n).symm (coordE b n v))) k)
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hFc, hFc, Matrix.mulVec_mulVec, hcA,
      ← Matrix.mulVec_mulVec, coordE_mulVec]
    rfl
  let Θ : (Fin (Module.finrank F F') → Module.AEval' f) ≃ₗ[F] (Fin (Module.finrank F F') → Module.AEval' g) :=
    (LinearEquiv.piCongrRight fun _ => (Module.AEval'.of f).symm).trans
      (core.trans (LinearEquiv.piCongrRight fun _ => Module.AEval'.of g))
  have hΘ : ∀ x, Θ ((X : F[X]) • x) = (X : F[X]) • Θ x := by
    intro x
    have h3 : (fun k => (Module.AEval'.of f).symm (((X : F[X]) • x) k)) =
        fun k => f ((Module.AEval'.of f).symm (x k)) :=
      funext fun k => Module.AEval'.of_symm_X_smul f (x k)
    funext k
    show Module.AEval'.of g (core (fun k => (Module.AEval'.of f).symm (((X : F[X]) • x) k)) k) =
      (X : F[X]) • Module.AEval'.of g (core (fun k => (Module.AEval'.of f).symm (x k)) k)
    rw [h3, hcore, Module.AEval'.X_smul_of]
  haveI : Finite (Module.AEval' f) := Finite.of_equiv _ (Module.AEval'.of f).toEquiv
  haveI : Finite (Module.AEval' g) := Finite.of_equiv _ (Module.AEval'.of g).toEquiv
  obtain ⟨ψ⟩ := GlobalTheory.T.nonempty_linearEquiv_of_pi_fin_pow_finite F[X] (Module.AEval' f) (Module.AEval' g) (Module.finrank F F') hl
    ⟨equivOfX Θ hΘ⟩
  let e : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    (Module.AEval'.of f).trans ((ψ.restrictScalars F).trans (Module.AEval'.of g).symm)
  have he : ∀ v, e (f v) = g (e v) := by
    intro v
    have h1 : Module.AEval'.of f (f v) = (X : F[X]) • Module.AEval'.of f v :=
      (Module.AEval'.X_smul_of f v).symm
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h1, map_smul]
    exact Module.AEval'.of_symm_X_smul g _
  let P : GL (Fin n) F := ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine isConj_iff.mpr ⟨P, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  have h4 : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap := LinearMap.ext he
  have h5 := congrArg LinearMap.toMatrix' h4
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp] at h5
  simpa [P, f, g, LinearMap.toMatrix'_toLin'] using h5

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjOfIsConjGlFieldExtensionInclusionStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (n : ℕ) (γ γ' : GL (Fin n) F), IsConj (incl F F' n γ) (incl F F' n γ') → IsConj γ γ' := by
  first | (exact @GlobalTheory.Shin.isConj_of_isConj_incl) | (exact GlobalTheory.Shin.isConj_of_isConj_incl) | (intros; apply GlobalTheory.Shin.isConj_of_isConj_incl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesNoInvariant
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)), hx⟩

end GlobalTheory.PrinTwo.NoFix

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.PrinTwo.NoFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.PsiPhi

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem phiInv_ofPadic (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  have key : ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  simp only [phiInv, ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _

end GlobalTheory.DetInv.PsiPhi

namespace GlobalTheory.DetInv

end GlobalTheory.DetInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocF
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.HeckeSplitGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def intAEF : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a : Af F, (∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def splitLocF (σ : E →ₐ[F] E) : Set (AEF F E)ˣ :=
  {x | ∃ e, IsSplitIdemF σ e ∧ (e + cAF σ e) * ((x : AEF F E) - 1) = (x : AEF F E) - 1}


variable (F E) in
def modSetF (N : ℕ) : Set (AEF F E)ˣ :=
  {x | infPartF F E (x : AEF F E) = 1 ∧
    (∃ r ∈ intAEF F E, finPartF F E (x : AEF F E) - 1 = (N : Af F ⊗[F] E) * r) ∧
    finPartF F E ((x⁻¹ : (AEF F E)ˣ) : AEF F E) ∈ intAEF F E}

def grpHF (σ : E →ₐ[F] E) (N : ℕ) : Subgroup (AEF F E)ˣ :=
  Subgroup.closure (Set.range (Units.map (incAF F E).toMonoidHom) ∪ splitLocF σ ∪ modSetF F E N)

end GlobalTheory.HeckeSplitGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSepClosedResidueFieldOfModuleFinite
noncomputable section

namespace GlobalTheory

open IsLocalRing

theorem isLocalHom_algebraMap_of_moduleFinite (R T : Type) [CommRing R] [IsLocalRing R]
    [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T] :
    IsLocalHom (algebraMap R T) := by
  constructor
  intro a ha
  by_contra hna
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI hmax : (Ideal.comap (algebraMap R T) (maximalIdeal T)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal T)
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hm : a ∈ Ideal.comap (algebraMap R T) (maximalIdeal T) := by
    rw [heq]; exact (mem_maximalIdeal a).2 hna
  exact (mem_maximalIdeal _).1 hm ha

theorem isSepClosed_residueField_of_moduleFinite (R T : Type) [CommRing R] [IsLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing T] [IsLocalRing T] [Algebra R T]
    [Module.Finite R T] : IsSepClosed (ResidueField T) := by
  haveI := isLocalHom_algebraMap_of_moduleFinite R T
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (ResidueField R) (ResidueField T) := inferInstance
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField T) := inferInstance
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField R)

theorem finite_algebra_strictly_henselian_pi : ∀ (R S : Type) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing S] [Algebra R S] [Module.Finite R S],
    ∃ (ι : Type) (_ : Finite ι) (T : ι → Type) (_ : ∀ i, CommRing (T i))
      (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i) (_ : ∀ i, HenselianLocalRing (T i)),
      ∀ i, IsSepClosed (ResidueField (T i)) ∧ Module.Finite R (T i) := by
  intro R S _ _ _ _ _ _
  obtain ⟨ι, hι, T, hT, hA, e, h⟩ := ((finite_algebras_over_henselian R).1 S).1
  refine ⟨ι, hι, T, hT, hA, e, fun i ↦ (h i).1, fun i ↦ ⟨?_, (h i).2⟩⟩
  haveI := (h i).1
  haveI := (h i).2
  exact isSepClosed_residueField_of_moduleFinite R (T i)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapComp
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

theorem preimage_spMap_comp_eq_top {Y : Scheme.{0}} {V : Y.Opens} {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') {u : Sp S ⟶ Y} (h : u ⁻¹ᵁ V = ⊤) : (spMap g ≫ u) ⁻¹ᵁ V = ⊤ := by
  rw [Scheme.Hom.comp_preimage, h, Scheme.Hom.preimage_top]

theorem chartHom_spMap_comp {Y : Scheme.{0}} (V : Y.Opens) {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') (u : Sp S ⟶ Y) (h : u ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ u) ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V (spMap g ≫ u) h' x = g (chartHom V u h x) := by
  have e1 : ((spMap g ≫ u).appLE V ⊤ h'.ge).hom x = (spMap g).appTop.hom ((u.appLE V ⊤ h.ge).hom x) := by
    have e : (spMap g).appTop = (spMap g).appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [e]
    exact (congrArg (fun q => q.hom x) (Scheme.Hom.appLE_comp_appLE (spMap g) u V ⊤ ⊤ h.ge le_top)).symm
  have e2 := congrArg (fun q => q.hom ((u.appLE V ⊤ h.ge).hom x))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g))
  simp only [chartHom, RingHom.comp_apply]
  rw [e1]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e2
  exact e2

theorem isCombIn_spMap_comp (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S']
    (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S) (hC : IsCombIn V u c w a) :
    IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  obtain ⟨hu, hc, hw, hx⟩ := hC
  refine ⟨preimage_spMap_comp_eq_top g hu, preimage_spMap_comp_eq_top g hc,
    fun i => preimage_spMap_comp_eq_top g (hw i), fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [chartHom_spMap_comp V g c hc, chartHom_spMap_comp V g u hu, hx x, map_add (f := _), map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [chartHom_spMap_comp V g (w i) (hw i), map_mul, map_sub]

end GlobalTheory.SecGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapCompStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineCombinationInChart_specMap_comp : ∀ (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S'] (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), GlobalTheory.SecGlue.IsCombIn V u c w a →
    GlobalTheory.SecGlue.IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  first | exact @GlobalTheory.SecGlue.isCombIn_spMap_comp | exact GlobalTheory.SecGlue.isCombIn_spMap_comp | (intros; apply GlobalTheory.SecGlue.isCombIn_spMap_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerMapSubsetImMap
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem ker_map_subset_im_map (R C : Type) [CommRing R] [Field C] (f : R →+* C) (ξ ν : R) (N : ℕ)
    (F G : Matrix (Fin N) (Fin N) R) (hξ : ξ ∈ nonZeroDivisors R) (hν : f ν ≠ 0)
    (hfrac : ∀ c : C, ∃ s t : R, f s ≠ 0 ∧ c * f s = f t)
    (hker : ∃ s : R, f s ≠ 0 ∧ ∀ r : R, f r = 0 → ξ ∣ s * r)
    (hGF : G * F = (ξ * ν) • (1 : Matrix (Fin N) (Fin N) R))
    (x : Fin N → C) (hx : F.map f *ᵥ x = 0) : ∃ y : Fin N → C, x = G.map f *ᵥ y := by
  classical
  obtain ⟨s, hs, hsker⟩ := hker
  choose a b ha hab using fun i => hfrac (x i)

  set s0 : R := ∏ i, a i with hs0
  have hs0ne : f s0 ≠ 0 := by
    rw [hs0, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  let t : Fin N → R := fun i => b i * ∏ j ∈ Finset.univ.erase i, a j
  have ht : ∀ i, f (t i) = x i * f s0 := by
    intro i
    have h1 : s0 = a i * ∏ j ∈ Finset.univ.erase i, a j :=
      (Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)).symm
    simp only [t, map_mul, ← hab i]
    rw [h1, map_mul, mul_assoc]
  have hft : (f ∘ t) = f s0 • x := by
    funext i
    simp [ht i, mul_comm]

  have hFt : ∀ i, f ((F *ᵥ t) i) = 0 := by
    intro i
    rw [RingHom.map_mulVec, hft, Matrix.mulVec_smul, hx]
    simp
  choose w hw using fun i => hsker _ (hFt i)
  have hw' : s • (F *ᵥ t) = ξ • w := by
    funext i
    simpa using hw i

  have hG : ξ • ((s * ν) • t) = ξ • (G *ᵥ w) := by
    have h2 : G *ᵥ (s • (F *ᵥ t)) = G *ᵥ (ξ • w) := by rw [hw']
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGF, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h2
    rw [← h2]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hcancel : ∀ i, (s * ν) * t i = (G *ᵥ w) i := by
    intro i
    have h3 := congrFun hG i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    exact (mul_cancel_left_mem_nonZeroDivisors hξ).mp h3

  refine ⟨(f s * f ν * f s0)⁻¹ • (f ∘ w), ?_⟩
  funext i
  have h4 : f s * f ν * f s0 ≠ 0 := mul_ne_zero (mul_ne_zero hs hν) hs0ne
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← RingHom.map_mulVec, ← hcancel i, map_mul,
    map_mul, ht i]
  field_simp

end GlobalTheory.DetInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficients
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma one_sub_mul_sum_range_natCast_mul_pow_add (x : ℂ) (n : ℕ) :
    (1 - x) * ∑ i ∈ Finset.range n, (i : ℂ) * x ^ i + n * x ^ n =
      ∑ i ∈ Finset.range n, x ^ (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    push_cast
    ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma isIntegral_natCast_div_one_sub_of_isIntegral_of_ne_one (ζ : ℂ) (M : ℕ) (hζ : IsIntegral ℤ ζ)
    (hM : ζ ^ M = 1) (h1 : ζ ≠ 1) : IsIntegral ℤ ((M : ℂ) / (1 - ζ)) := by
  have hsub : (1 - ζ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hgeom : ∑ i ∈ Finset.range M, ζ ^ (i + 1) = 0 := by
    simp_rw [pow_succ]
    rw [← Finset.sum_mul, geom_sum_eq h1, hM, sub_self, zero_div, zero_mul]
  have key := one_sub_mul_sum_range_natCast_mul_pow_add ζ M
  rw [hgeom, hM, mul_one] at key
  have hq : (M : ℂ) / (1 - ζ) = -∑ i ∈ Finset.range M, (i : ℂ) * ζ ^ i := by
    rw [div_eq_iff hsub]
    linear_combination key
  rw [hq]
  exact (IsIntegral.sum _ fun i _ => (isIntegral_natCast i).mul (hζ.pow i)).neg


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.isIntegral_coefficients : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ),
    0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cP N x k) ∧
      IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by
  intro N _ M x k _ hx
  obtain ⟨-, -, hzero, -, hpow, -, -, hint⟩ :=
    _root_.GlobalTheory.WpFam.AddCharZMod.main N
  have h12 : IsIntegral ℤ (12 : ℂ) := by simpa using isIntegral_natCast (R := ℤ) (B := ℂ) 12
  have htw : ∀ (a : ℕ) (s : ℂ), IsIntegral ℤ s →
      IsIntegral ℤ (_root_.GlobalTheory.WpFam.cSum N a s x k) := by
    intro a s hs
    unfold _root_.GlobalTheory.WpFam.cSum
    refine IsIntegral.sum _ fun m _ => ((isIntegral_natCast m).pow a).mul ?_
    refine IsIntegral.add ?_ (hs.mul ?_)
    · split_ifs
      · exact hint _
      · exact isIntegral_zero
    · split_ifs
      · exact hint _
      · exact isIntegral_zero
  have hG : IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by
    unfold _root_.GlobalTheory.WpFam.cG
    split_ifs
    · rw [show (12 : ℂ) * (-1 / 12) = -1 by norm_num]
      exact isIntegral_one.neg
    · exact h12.mul ((isIntegral_natCast 2).mul (isIntegral_natCast _))
    · simp [isIntegral_zero]
  have hB : IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) := by
    unfold _root_.GlobalTheory.WpFam.cB _root_.GlobalTheory.WpFam.cD
    split_ifs with hk h0
    · by_cases h1 : _root_.GlobalTheory.WpFam.ch N (x 1) = 1
      · simp [h1, isIntegral_zero]
      · have hζM : _root_.GlobalTheory.WpFam.ch N (x 1) ^ M = 1 := by
          have hx1 := congr_fun hx 1
          simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at hx1
          rw [← hpow, hx1, hzero]
        have hq := isIntegral_natCast_div_one_sub_of_isIntegral_of_ne_one _ M (hint (x 1)) hζM h1
        constructor
        · rw [show (M : ℂ) ^ 2 * (_root_.GlobalTheory.WpFam.ch N (x 1) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1)) ^ 2)
              = _root_.GlobalTheory.WpFam.ch N (x 1) * ((M : ℂ) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1))) ^ 2 by
              rw [div_pow]; ring]
          exact (hint _).mul (hq.pow 2)
        · rw [show (M : ℂ) ^ 3 * (_root_.GlobalTheory.WpFam.ch N (x 1) * (1 + _root_.GlobalTheory.WpFam.ch N (x 1)) /
              (1 - _root_.GlobalTheory.WpFam.ch N (x 1)) ^ 3) = _root_.GlobalTheory.WpFam.ch N (x 1) *
              (1 + _root_.GlobalTheory.WpFam.ch N (x 1)) *
              ((M : ℂ) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1))) ^ 3 by rw [div_pow]; ring]
          exact ((hint _).mul (isIntegral_one.add (hint _))).mul (hq.pow 3)
    · simp [isIntegral_zero]
    · exact ⟨((isIntegral_natCast M).pow 2).mul (htw 1 1 isIntegral_one),
        ((isIntegral_natCast M).pow 3).mul (htw 2 (-1) isIntegral_one.neg)⟩
  refine ⟨hB.1, hB.2, ?_, hG⟩
  unfold _root_.GlobalTheory.WpFam.cP
  split_ifs
  · simp [isIntegral_zero]
  · rw [show 12 * (M : ℂ) ^ 2 * (_root_.GlobalTheory.WpFam.cB N x k - _root_.GlobalTheory.WpFam.cG N k)
        = 12 * ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) -
          (M : ℂ) ^ 2 * (12 * _root_.GlobalTheory.WpFam.cG N k) by ring]
    exact (h12.mul hB.1).sub (((isIntegral_natCast M).pow 2).mul hG)

end GlobalTheory.WpFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficientsStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ), 0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * cB N x k) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * cP N x k) ∧ IsIntegral ℤ (12 * cG N k) := by
  first | exact @GlobalTheory.WpFam.isIntegral_coefficients | exact GlobalTheory.WpFam.isIntegral_coefficients | (intros; apply GlobalTheory.WpFam.isIntegral_coefficients <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCharacterSeminormBound
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

noncomputable section

namespace GlobalTheory.PhaseLipschitz

def psi (k : ℝ) : ℝ → ℂ := fun t =>
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) - 1

theorem eChar_sub_one_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (k : ℝ) :
    (fun y => eChar (L y + k) - 1) = psi k ∘ ⇑L := by
  funext y
  simp only [psi, Function.comp_apply, eChar_apply, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem contDiff_psi (k : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (psi k) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  unfold psi; fun_prop

theorem norm_psi_le (k t : ℝ) : ‖psi k t‖ ≤ 2 * Real.pi * |t + k| := by
  have e : psi k t = Complex.exp (Complex.I * ((2 * Real.pi * (t + k) : ℝ) : ℂ)) - 1 := by
    simp only [psi, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

theorem iteratedDeriv_psi_succ (k : ℝ) (j : ℕ) :
    iteratedDeriv (j + 1) (psi k) = fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * (2 * Real.pi * Complex.I) ^ (j + 1) *
        Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) := by
  rw [iteratedDeriv_succ']
  have hd : deriv (psi k) = deriv (fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) := by
    unfold psi; exact deriv_sub_const_fun _
  rw [hd, ← iteratedDeriv_succ', GlobalTheory.LinPhaseSeminorm.iteratedDeriv_const_mul_cexp]

theorem norm_iteratedDeriv_psi_succ (k : ℝ) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv (j + 1) (psi k) t‖ = (2 * Real.pi) ^ (j + 1) := by
  rw [iteratedDeriv_psi_succ]
  have h1 : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
    intro r
    rw [show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  simp only [norm_mul, norm_pow, h1]
  simp [abs_of_pos Real.pi_pos]

theorem norm_iteratedFDeriv_psi_comp_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) {N i : ℕ} (hi : i ≤ N) (x : V) :
    ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ ≤
      (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * (1 + ‖x‖) := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hL := norm_nonneg L
  have hx := norm_nonneg x
  have hk := abs_nonneg k
  have h1N : (1 : ℝ) ≤ (1 + ‖L‖) ^ N := one_le_pow₀ (by linarith)
  rcases i with _ | j
  · rw [norm_iteratedFDeriv_zero, Function.comp_apply]
    refine (norm_psi_le k (L x)).trans ?_
    have h2 : |L x + k| ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by
      have h3 : |L x| ≤ ‖L‖ * ‖x‖ := by simpa [Real.norm_eq_abs] using L.le_opNorm x
      calc |L x + k| ≤ |L x| + |k| := abs_add_le _ _
        _ ≤ ‖L‖ * ‖x‖ + |k| := by linarith
        _ ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by nlinarith
    have h4 : 2 * Real.pi ≤ (2 * Real.pi) ^ (N + 1) := le_self_pow₀ hpi (by omega)
    calc 2 * Real.pi * |L x + k| ≤ 2 * Real.pi * ((‖L‖ + |k|) * (1 + ‖x‖)) := by gcongr
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * 1) * (1 + ‖x‖) := by
          rw [mul_one]; rw [← mul_assoc]; gcongr
      _ ≤ _ := by gcongr
  · rw [L.iteratedFDeriv_comp_right (contDiff_psi k) x (i := j + 1) (by exact_mod_cast le_top)]
    have h5 : (2 * Real.pi) ^ (j + 1) ≤ (2 * Real.pi) ^ (N + 1) := pow_le_pow_right₀ hpi (by omega)
    have h6 : ‖L‖ ^ (j + 1) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by
      rw [pow_succ']
      gcongr
      · linarith
      · calc ‖L‖ ^ j ≤ (1 + ‖L‖) ^ j := by gcongr; linarith
          _ ≤ (1 + ‖L‖) ^ N := pow_le_pow_right₀ (by linarith) (by omega)
    calc _ ≤ ‖iteratedFDeriv ℝ (j + 1) (psi k) (L x)‖ * ∏ _j : Fin (j + 1), ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = (2 * Real.pi) ^ (j + 1) * ‖L‖ ^ (j + 1) := by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_psi_succ]; simp
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * 1 := by
          rw [mul_one]; gcongr
      _ ≤ _ := by gcongr; linarith

theorem hasTemperateGrowth_phase {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) : Function.HasTemperateGrowth (fun y => eChar (L y + k)) :=
  hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))

theorem coe_smulLeft_sub {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    ⇑(SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) = fun y => (psi k ∘ ⇑L) y * f y := by
  funext y
  rw [SchwartzMap.sub_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase L k), smul_eq_mul,
    ← congrFun (eChar_sub_one_eq L k) y]
  ring

theorem seminorm_smulLeft_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A N a n : ℕ} (ha : a ≤ A) (hn : n ≤ N) (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ a n (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) ≤
      ((N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1)) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) *
        (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f := by
  set S := (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f with hS
  set P := (‖L‖ + |k|) * (1 + ‖L‖) ^ N with hP
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hP0 : 0 ≤ P := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ a n _ (by positivity) fun x => ?_
  rw [coe_smulLeft_sub]
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_psi k).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hx := norm_nonneg x
  have hf : ∀ j ≤ N, ‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ j f x‖ ≤ 2 ^ (A + 1) * S := by
    intro j hj
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (A + 1, N)) (k := a + 1) (n := j)
      (by simp; omega) hj f x
    have h' : ‖x‖ ^ a * (1 + ‖x‖) ≤ (1 + ‖x‖) ^ (a + 1) := by
      rw [pow_succ]; gcongr; linarith
    calc _ ≤ (1 + ‖x‖) ^ (a + 1) * ‖iteratedFDeriv ℝ j f x‖ := by gcongr
      _ ≤ _ := h
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := norm_iteratedFDeriv_psi_comp_le L k (N := N) (i := i) (by omega) x
    have h2 := hf (n - i) (by omega)
    have hc : (n.choose i : ℝ) ≤ 2 ^ N :=
      (by exact_mod_cast Nat.choose_le_two_pow n i : (n.choose i : ℝ) ≤ 2 ^ n).trans
        (pow_le_pow_right₀ (by norm_num) hn)
    calc ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        ≤ ‖x‖ ^ a * ((2 ^ N : ℝ) * ((2 * Real.pi) ^ (N + 1) * P * (1 + ‖x‖)) *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by gcongr
      _ = 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) *
          (‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ _ := by gcongr
  calc ‖x‖ ^ a * ‖iteratedFDeriv ℝ n (fun y => (psi k ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ a * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ a * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (n + 1), 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by simp
    _ ≤ ((N : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by
        gcongr
    _ = _ := by ring

theorem continuous_finset_sup_seminorm {E ι : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {p : ι → Seminorm ℂ E} (hp : ∀ i, Continuous (p i)) (s : Finset ι) :
    Continuous ⇑(s.sup p : Seminorm ℂ E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact continuous_const
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact ((hp i).max ih).congr fun x => (Seminorm.sup_apply _ _ _).symm

theorem seminorm_smulLeft_eChar_sub_le : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (L : V →L[ℝ] ℝ) (k : ℝ) (f : SchwartzMap V ℂ),
      p (SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f) ≤
        (‖L‖ + |k|) * (1 + ‖L‖) ^ M * q f := by
  intro V _ _ p hp
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  set A := s.sup Prod.fst with hA
  set N := s.sup Prod.snd with hN
  set K : ℝ := (N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  set Q : Seminorm ℂ (SchwartzMap V ℂ) :=
    (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) with hQ
  refine ⟨(C * ⟨K, hK0⟩ : NNReal) • Q, N, ?_, ?_⟩
  · exact (continuous_finset_sup_seminorm
      (fun i => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i) _).const_smul _
  · intro L k f
    set g := SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f
    have hP0 : 0 ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by positivity
    have hQ0 : 0 ≤ Q f := apply_nonneg _ _
    have hs : (s.sup (schwartzSeminormFamily ℂ V ℂ)) g ≤ K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      exact seminorm_smulLeft_sub_le (Finset.le_sup (f := Prod.fst) hi) (Finset.le_sup (f := Prod.snd) hi) L k f
    calc p g ≤ (C • s.sup (schwartzSeminormFamily ℂ V ℂ)) g := hC g
      _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) g := by
          rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
      _ ≤ (C : ℝ) * (K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f) := by gcongr
      _ = (‖L‖ + |k|) * (1 + ‖L‖) ^ N * (((C * ⟨K, hK0⟩ : NNReal) • Q) f) := by
          rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
          change (C : ℝ) * _ = _ * (((C : ℝ) * K) * Q f)
          ring

end GlobalTheory.PhaseLipschitz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEThreeOfFreeRegularLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEThreeOfFreeRegularLocal
open IsLocalRing RingTheory.Sequence

namespace GlobalTheory

theorem modDepthGE_three_of_free_of_isRegularLocalRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    3 ≤ ringKrullDim R → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] [Nontrivial M], ReciprocityTheory.CA.ModDepthGE R M 3 := by
  intro R _ _ hd M _ _ _ _ _
  obtain ⟨xs, h, hl⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg : IsRegular R xs := isRegular_of_ofList_eq_maximalIdeal h hl.le
  have h3 : 3 ≤ xs.length := by
    rw [← hl] at hd
    exact_mod_cast hd
  have hm : ∀ r ∈ xs.take 3, r ∈ maximalIdeal R := fun r hr =>
    h ▸ Ideal.subset_span (List.mem_of_mem_take hr)
  have hw : IsWeaklyRegular R (xs.take 3) := by
    have := hreg.1
    rw [← List.take_append_drop 3 xs, isWeaklyRegular_append_iff] at this
    exact this.1
  have hwM : IsWeaklyRegular M (xs.take 3) := by
    have := hw.isWeaklyRegular_lTensor (M₂ := M)
    exact ((TensorProduct.rid R M).isWeaklyRegular_congr _).mp this
  refine ⟨xs.take 3, by simp [h3], hm, ?_⟩
  exact (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hwM

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEThreeOfFreeRegularLocalStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modDepthGE_three_of_free_regularLocal : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M] [Nontrivial M], ReciprocityTheory.CA.ModDepthGE R M 3 := by
  first | exact @GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing | exact GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing | (intros; apply GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing <;> assumption)
end
end
