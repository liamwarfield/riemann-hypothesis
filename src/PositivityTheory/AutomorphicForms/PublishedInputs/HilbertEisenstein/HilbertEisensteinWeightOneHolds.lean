module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PoissonSummationHolds
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.InvMulVecScalarMul
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SGrowth
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.OpenKernelHolds
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.EisensteinLowWeight
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.FourierExpansionHolds

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ScalarActionHolds
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

theorem scalar_action_holds : SPois → SInt → SSmooth → SSmul := by
  intro _ _ _ F _ _ _ ω c k φ a ha
  have e2 : ∀ g, (a • φ).1 g = a * φ.1 g := fun _ => rfl
  refine ⟨fun h => ?_, fun c₀ b h => ?_⟩
  · obtain ⟨⟨hl, hlev, hk, hz, hg⟩, hlevel, hcent, hwt, hlow⟩ := h
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, fun w => Submodule.smul_mem _ a (hlevel w),
      fun z g => ?_, fun v => ?_, fun v => ?_⟩
    · rw [e2, e2, hl]
    · have e : {x | UpperTheory.V.TR.finRep F 2 x (a • φ) = a • φ} = {x | UpperTheory.V.TR.finRep F 2 x φ = φ} := by
        ext x
        simp only [Set.mem_ofPred_eq, map_smul]
        exact smul_right_inj ha
      rw [e]
      exact hlev
    · refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℂ (Set.range fun x => UpperTheory.V.TR.cptRep F 2 x φ)) (Submodule.span_le.2 ?_)
      rintro _ ⟨x, rfl⟩
      show UpperTheory.V.TR.cptRep F 2 x (a • φ) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)
    · refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (UpperTheory.V.TR.Sm F 2) => z φ) '' UpperTheory.V.TR.Zalg F 2))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz', rfl⟩
      show z (a • φ) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨z, hz', rfl⟩)
    · obtain ⟨C, N, hC⟩ := hg g
      refine ⟨‖a‖ * C, N, fun y => ?_⟩
      rw [e2, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg a)
    · rw [e2, e2, hcent]
      ring
    · simp only [map_smul]
      rw [← smul_sub, hwt v]
      exact smul_comm _ _ _
    · simp only [map_smul]
      rw [← smul_sub, hlow v, ← smul_add]
      exact smul_comm _ _ _
  · intro x y hy yf
    have e : ∀ z : Af F, coefAt (fun 𝔪 => a * b 𝔪) z = a * coefAt b z := by
      intro z
      unfold coefAt
      split_ifs <;> simp
    convert (h x y hy yf).mul_left a using 1
    · funext ξ
      rw [e, mul_assoc]
    · rw [e2]
      simp only
      ring

end UpperTheory.HilbertEisensteinWeightOne
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LeftInvarianceHolds
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

namespace LeftInvarianceEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rowA_vecMul (ξ : Fin 2 → F) (γ : GL (Fin 2) F) :
    rowA ξ ᵥ* ((ratGL F 2 γ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      rowA (ξ ᵥ* (γ : Matrix (Fin 2) (Fin 2) F)) := by
  funext i
  exact (RingHom.map_vecMul (algebraMap F (Ad F)) (γ : Matrix (Fin 2) (Fin 2) F) ξ i).symm

def permE (γ : GL (Fin 2) F) : {ξ : Fin 2 → F // ξ ≠ 0} ≃ {ξ : Fin 2 → F // ξ ≠ 0} where
  toFun ξ := ⟨ξ.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) F), fun h => ξ.2 (by
    have := congrArg (· ᵥ* ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Matrix.vecMul_vecMul] using this)⟩
  invFun ξ := ⟨ξ.1 ᵥ* ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), fun h => ξ.2 (by
    have := congrArg (· ᵥ* (γ : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Matrix.vecMul_vecMul] using this)⟩
  left_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul])
  right_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul])

theorem thetaS_ratGL (Ψ : (Fin 2 → Ad F) → ℂ) (a : (Ad F)ˣ) (γ : GL (Fin 2) F) (g : GA F 2) :
    thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * (ratGL F 2 γ * g)) =
      thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g) := by
  unfold thetaS
  refine Eq.trans ?_ ((permE γ).tsum_eq (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
    Ψ (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)))))
  refine tsum_congr fun ξ => ?_
  rw [← mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, mul_assoc, Units.val_mul,
    ← Matrix.vecMul_vecMul, rowA_vecMul]
  rfl

theorem absD_ratGL (γ : GL (Fin 2) F) (g : GA F 2) : absD (ratGL F 2 γ * g) = absD g := by
  have h : Matrix.GeneralLinearGroup.det (ratGL F 2 γ) =
      IdeleGroup.diagonal F (Matrix.GeneralLinearGroup.det γ) := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap F (Ad F)) γ) = _
    rw [Matrix.GeneralLinearGroup.map_det]
    rfl
  unfold absD
  rw [map_mul, map_mul, h, IdeleGroup.ideleModule_diagonal, one_mul]

end LeftInvarianceEisenstein

theorem left_invariance_holds : SPois → SInt → SSmooth → SLeft := by
  intro _ _ _ F _ _ _ ω c γ g
  unfold Eis eisInt
  simp_rw [LeftInvarianceEisenstein.thetaS_ratGL, LeftInvarianceEisenstein.absD_ratGL]

end UpperTheory.HilbertEisensteinWeightOne
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CenterFinitenessHolds
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

private theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

private theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : ∀ (z : Ideles F) (g : GA F 2), φ.1 (GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  _root_.UpperTheory.Reformulated.B.Qf10.casimir E hE k φ h0 h1 h2 u

theorem UpperTheory.HilbertEisensteinWeightOne.center_finiteness_holds : SPois → SInt → SSmooth → SZfin := by
  intro _ _ _ F _ _ _ ω c hω φ hc hw hl
  have hcap : ∀ v u, ∃ c : ℂ, TR.cap v u φ = c • φ := fun v u => by
    have h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
      classical
      rw [← lie_scalar hω hc (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have := casimir _ (TR.glRel_Eop v) ((1 : ℕ) : ℂ) φ h0 (hw v) (hl v) u
    refine ⟨_, Eq.trans ?_ this⟩
    rw [TR.cap]
    norm_num
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, u, rfl⟩ := hx
    obtain ⟨c, e⟩ := hcap v u
    exact Submodule.mem_span_singleton.2 ⟨c, e.symm⟩
  | algebraMap c => exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 hy
    have e' : c • φ = y φ := e
    change x (y φ) ∈ Submodule.span ℂ {φ}
    rw [← e', map_smul]
    exact Submodule.smul_mem _ _ hx
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.KFinitenessHolds
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def sgn (b : Bool) : ℝ := if b then 1 else -1

def archE (ε : InfinitePlace F → Bool) (x y : UpperTheory.V.TR.Rinf F) : ℂ :=
  ∏ v, (((x v : ℂ) + (sgn (ε v) : ℂ) * Complex.I * (y v : ℂ)) *
    Complex.exp (-(Real.pi : ℂ) * ((x v : ℂ) ^ 2 + (y v : ℂ) ^ 2)))


open Classical in
def PhiE (c : HeightOneSpectrum (𝓞 F) → ℕ) (ε : InfinitePlace F → Bool) (ξ : Fin 2 → Ad F) : ℂ :=
  archE ε (UpperTheory.V.TR.pInf F (ξ 0)) (UpperTheory.V.TR.pInf F (ξ 1)) *
    if ∀ w, Valued.v (pLoc F w (pFin F (ξ 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F (ξ 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) then 1 else 0

def lam (k : UpperTheory.V.TR.Kinf F 2) : ℂ := ∏ w, ((k.1 0 0 w : ℂ) + Complex.I * (k.1 0 1 w : ℂ))

def eps (k : UpperTheory.V.TR.Kinf F 2) (w : InfinitePlace F) : Bool :=
  decide (0 < k.1 0 0 w * k.1 1 1 w - k.1 0 1 w * k.1 1 0 w)

theorem place (a b c d x y : ℝ) (h1 : a * a + c * c = 1) (h2 : b * b + d * d = 1) (h3 : a * b + c * d = 0)
    (h4 : a * a + b * b = 1) (h5 : c * c + d * d = 1) (h6 : a * c + b * d = 0) :
    (((x * a + y * c : ℝ) : ℂ) + Complex.I * ((x * b + y * d : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (((x * a + y * c : ℝ) : ℂ) ^ 2 + ((x * b + y * d : ℝ) : ℂ) ^ 2)) =
    ((a : ℂ) + Complex.I * (b : ℂ)) * (((x : ℂ) + (sgn (decide (0 < a * d - b * c)) : ℂ) * Complex.I * (y : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) := by
  have hsq : (x * a + y * c) ^ 2 + (x * b + y * d) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination x ^ 2 * h4 + y ^ 2 * h5 + 2 * x * y * h6
  have hC : (((x * a + y * c : ℝ) : ℂ) ^ 2 + ((x * b + y * d : ℝ) : ℂ) ^ 2) = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 := by
    exact_mod_cast hsq
  rw [hC]
  generalize Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) = E
  have hs2 : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h4 + h5 - (a * c + b * d) * h6
  have hsg : ((sgn true : ℝ) : ℂ) = 1 := by simp [sgn]
  have hsg' : ((sgn false : ℝ) : ℂ) = -1 := by simp [sgn]
  rcases mul_self_eq_one_iff.mp hs2 with hs | hs
  · have hc : c = -b := by linear_combination (-c) * h4 + a * h6 - b * hs
    have hd : d = a := by linear_combination (-d) * h4 + b * h6 + a * hs
    have hpos : 0 < a * d - b * c := by
      rw [hs]
      norm_num
    rw [decide_eq_true hpos, hsg]
    subst hc hd
    push_cast
    linear_combination (-((b : ℂ) * (y : ℂ) * E)) * Complex.I_sq
  · have hc : c = b := by linear_combination (-c) * h4 + a * h6 - b * hs
    have hd : d = -a := by linear_combination (-d) * h4 + b * h6 + a * hs
    have hneg : ¬ 0 < a * d - b * c := by
      rw [hs]
      norm_num
    rw [decide_eq_false hneg, hsg']
    subst hc hd
    push_cast
    linear_combination ((c : ℂ) * (y : ℂ) * E) * Complex.I_sq

theorem rels (k : UpperTheory.V.TR.Kinf F 2) (w : InfinitePlace F) :
    k.1 0 0 w * k.1 0 0 w + k.1 1 0 w * k.1 1 0 w = 1 ∧ k.1 0 1 w * k.1 0 1 w + k.1 1 1 w * k.1 1 1 w = 1 ∧
    k.1 0 0 w * k.1 0 1 w + k.1 1 0 w * k.1 1 1 w = 0 ∧ k.1 0 0 w * k.1 0 0 w + k.1 0 1 w * k.1 0 1 w = 1 ∧
    k.1 1 0 w * k.1 1 0 w + k.1 1 1 w * k.1 1 1 w = 1 ∧ k.1 0 0 w * k.1 1 0 w + k.1 0 1 w * k.1 1 1 w = 0 := by
  have hA := Unitary.coe_star_mul_self k
  have hB := Unitary.coe_mul_star_self k
  have e : ∀ (M N : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)), M = N → ∀ i j, M i j w = N i j w :=
    fun M N h i j => by rw [h]
  have a1 := e _ _ hA 0 0
  have a2 := e _ _ hA 1 1
  have a3 := e _ _ hA 0 1
  have b1 := e _ _ hB 0 0
  have b2 := e _ _ hB 1 1
  have b3 := e _ _ hB 0 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at a1 a2 a3 b1 b2 b3
  exact ⟨a1, a2, a3, b1, b2, b3⟩

theorem arch_rot (k : UpperTheory.V.TR.Kinf F 2) (X Y : UpperTheory.V.TR.Rinf F) :
    arch (fun w => X w * k.1 0 0 w + Y w * k.1 1 0 w) (fun w => X w * k.1 0 1 w + Y w * k.1 1 1 w) =
      lam k * archE (eps k) X Y := by
  unfold arch archE lam
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rels k w
  exact place (k.1 0 0 w) (k.1 0 1 w) (k.1 1 0 w) (k.1 1 1 w) (X w) (Y w) h1 h2 h3 h4 h5 h6

theorem phi_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (k : UpperTheory.V.TR.Kinf F 2) (v : Fin 2 → Ad F) :
    Phi c (v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      lam k * PhiE c (eps k) v := by
  have hK : ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map
      (UpperTheory.V.TR.pInf F) = k.1 := by
    have h := congrArg Units.val (UpperTheory.V.TR.pInf_infGL (E := F) (Unitary.toUnits k))
    exact h
  have hKf : ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map
      (pFin F) = 1 := by
    have h := congrArg Units.val (UpperTheory.V.TR.pFin_infGL (E := F) (Unitary.toUnits k))
    exact h
  have ef : ∀ i, pFin F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) i) = pFin F (v i) := by
    intro i
    rw [RingHom.map_vecMul, hKf, Matrix.vecMul_one]
    rfl
  have e0 : UpperTheory.V.TR.pInf F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) 0) =
      fun w => UpperTheory.V.TR.pInf F (v 0) w * k.1 0 0 w + UpperTheory.V.TR.pInf F (v 1) w * k.1 1 0 w := by
    rw [RingHom.map_vecMul, hK]
    funext w
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have e1 : UpperTheory.V.TR.pInf F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) 1) =
      fun w => UpperTheory.V.TR.pInf F (v 0) w * k.1 0 1 w + UpperTheory.V.TR.pInf F (v 1) w * k.1 1 1 w := by
    rw [RingHom.map_vecMul, hK]
    funext w
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  unfold Phi PhiE
  rw [ef 0, ef 1, e0, e1, arch_rot k, mul_assoc]

theorem absD_mul (g h : GA F 2) : absD (g * h) = absD g * absD h := by
  unfold absD
  rw [map_mul, map_mul]
  rfl

theorem absD_nonneg (g : GA F 2) : 0 ≤ absD g := by
  unfold absD
  exact ((IdeleGroup.ideleModule F) (Matrix.GeneralLinearGroup.det g)).2.le

theorem eis_smul (ω : HChar F) (a : ℂ) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) :
    Eis ω (fun v => a * Ψ v) g = a * Eis ω Ψ g := by
  unfold Eis
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  try dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  try dsimp only
  unfold eisInt thetaS
  simp only [tsum_mul_left]
  ring

theorem eis_mul_right (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g K : GA F 2) :
    Eis ω Ψ (g * K) = ((absD K ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
      Eis ω (fun v => Ψ (v ᵥ* (K : Matrix (Fin 2) (Fin 2) (Ad F)))) g := by
  unfold Eis
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  try dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  try dsimp only
  unfold eisInt thetaS
  rw [absD_mul, Real.mul_rpow (absD_nonneg g) (absD_nonneg K)]
  simp only [← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) _) g K, Units.val_mul, ← Matrix.vecMul_vecMul]
  push_cast
  ring

theorem cpt_eq (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (hs : Eis ω (Phi c) ∈ UpperTheory.V.TR.Sm F 2)
    (k : UpperTheory.V.TR.Kinf F 2) (g : GA F 2) :
    (UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩).1 g =
      ((((absD (UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * lam k) *
        Eis ω (PhiE c (eps k)) g := by
  change Eis ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k)) = _
  rw [eis_mul_right, show (fun v => Phi c (v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)))) = fun v => lam k * PhiE c (eps k) v from funext (phi_rot c k), eis_smul]
  ring

end UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein

open UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein in
theorem UpperTheory.HilbertEisensteinWeightOne.K_finiteness_holds : SPois → SInt → SSmooth → SKfin := by
  intro _ _ _ F _ _ _ ω c _ hs
  haveI : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun ε : InfinitePlace F → Bool => Eis ω (PhiE c ε))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hle : (Submodule.span ℂ (Set.range fun k => UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩)).map
      (UpperTheory.V.TR.Sm F 2).subtype ≤
      Submodule.span ℂ (Set.range fun ε : InfinitePlace F → Bool => Eis ω (PhiE c ε)) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have e : (UpperTheory.V.TR.Sm F 2).subtype (UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩) =
        ((((absD (UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * lam k) •
          Eis ω (PhiE c (eps k)) :=
      funext fun g => by rw [Pi.smul_apply, smul_eq_mul]; exact cpt_eq ω c hs k g
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨eps k, rfl⟩)
  haveI := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.WeightHolds
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation

open Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def ca (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Rinf F := fun u => if u = v then Real.cos θ else 1

def sa (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Rinf F := fun u => if u = v then Real.sin θ else 0

omit [NumberField F] [IsTotallyReal F] in
theorem ca_sq (v : InfinitePlace F) (θ : ℝ) (u : InfinitePlace F) : ca v θ u ^ 2 + sa v θ u ^ 2 = 1 := by
  unfold ca sa
  split_ifs <;> simp [Real.cos_sq_add_sin_sq]

def rotv (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Kinf F 2 :=
  ⟨!![ca v θ, sa v θ; -sa v θ, ca v θ], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [ca_sq v θ u]⟩

theorem rotv_zero (v : InfinitePlace F) : rotv v 0 = (1 : UpperTheory.V.TR.Kinf F 2) := by
  ext i j u
  fin_cases i <;> fin_cases j <;> simp [rotv, ca, sa]

def Xv (v : InfinitePlace F) : UpperTheory.V.TR.Lie F 2 :=
  UpperTheory.V.TR.toL (Matrix.single 0 1 (Pi.single v 1)) - UpperTheory.V.TR.toL (Matrix.single 1 0 (Pi.single v 1))

theorem rot_deriv (v : InfinitePlace F) :
    HasDerivAt (fun t : ℝ => UpperTheory.V.TR.toL (Unitary.toUnits (rotv v t)).val) (Xv v) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
  by_cases hu : u = v
  · subst hu
    fin_cases i <;> fin_cases j
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_cos 0
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_sin 0
    · simpa [Xv, rotv, ca, sa] using (Real.hasDerivAt_sin 0).fun_neg
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_cos 0
  · fin_cases i <;> fin_cases j <;> simp [Xv, rotv, ca, sa, hu, hasDerivAt_const]

theorem det_rotv (v : InfinitePlace F) (θ : ℝ) :
    Matrix.GeneralLinearGroup.det (Unitary.toUnits (rotv v θ)) = 1 := by
  refine Units.ext ?_
  ext u
  simp [rotv, Matrix.det_fin_two]
  nlinarith [ca_sq v θ u]

theorem factor (x y a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    (((x * a + y * -b : ℝ) : ℂ) + Complex.I * ((x * b + y * a : ℝ) : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * (((x * a + y * -b : ℝ) : ℂ) ^ 2 + ((x * b + y * a : ℝ) : ℂ) ^ 2)) =
      ((a : ℂ) + Complex.I * (b : ℂ)) *
        (((x : ℂ) + Complex.I * (y : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) := by
  have hr : (x * a + y * -b) ^ 2 + (x * b + y * a) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination (x ^ 2 + y ^ 2) * h
  have hc : (((x * a + y * -b : ℝ) : ℂ) ^ 2 + ((x * b + y * a : ℝ) : ℂ) ^ 2) = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 := by
    exact_mod_cast hr
  rw [hc]
  push_cast
  linear_combination (-(b : ℂ) * y * Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) * Complex.I_sq

omit [IsTotallyReal F] in
theorem prod_rot (v : InfinitePlace F) (θ : ℝ) :
    ∏ u, (((ca v θ u : ℝ) : ℂ) + Complex.I * ((sa v θ u : ℝ) : ℂ)) = Complex.exp (θ * Complex.I) := by
  rw [Fintype.prod_eq_single v (fun u hu => by simp [ca, sa, hu])]
  simp [ca, sa, Complex.exp_mul_I]
  ring

theorem phi_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (η : Fin 2 → Ad F) :
    Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ)) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      Complex.exp (θ * Complex.I) * Phi c η := by
  set M := ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ)) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))
  have hI : M.map (UpperTheory.V.TR.pInf F) = ((Unitary.toUnits (rotv v θ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
      Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :=
    congrArg Units.val (UpperTheory.V.TR.pInf_infGL (Unitary.toUnits (rotv v θ)))
  have hF : M.map (pFin F) = 1 := congrArg Units.val (UpperTheory.V.TR.pFin_infGL (Unitary.toUnits (rotv v θ)))
  have eI : ∀ i, UpperTheory.V.TR.pInf F ((η ᵥ* M) i) = ((fun j => UpperTheory.V.TR.pInf F (η j)) ᵥ*
      ((Unitary.toUnits (rotv v θ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) i :=
    fun i => by rw [RingHom.map_vecMul, hI]; rfl
  have eF : ∀ i, pFin F ((η ᵥ* M) i) = pFin F (η i) := fun i => by
    rw [RingHom.map_vecMul, hF, Matrix.vecMul_one]; rfl
  unfold Phi
  rw [eF 0, eF 1, eI 0, eI 1, ← mul_assoc]
  congr 1
  unfold arch
  rw [← prod_rot v θ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun u _ => ?_
  have h := factor (UpperTheory.V.TR.pInf F (η 0) u) (UpperTheory.V.TR.pInf F (η 1) u) (ca v θ u) (sa v θ u) (ca_sq v θ u)
  simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two, rotv] using h

theorem thetaS_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (h : GA F 2) :
    thetaS (Phi c) (h * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) =
      Complex.exp (θ * Complex.I) * thetaS (Phi c) h := by
  unfold thetaS
  rw [← tsum_mul_left]
  congr 1
  funext ξ
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, phi_rot]

theorem eis_rot (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (g : GA F 2) :
    Eis ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) =
      Complex.exp (θ * Complex.I) * Eis ω (Phi c) g := by
  have hd : absD (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) = absD g := by
    unfold absD
    rw [map_mul, UpperTheory.V.TR.det_infGL, det_rotv, map_one, mul_one]
  have he : ∀ t u, eisInt ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) t u =
      Complex.exp (θ * Complex.I) * eisInt ω (Phi c) g t u := by
    intro t u
    unfold eisInt
    rw [← mul_assoc, thetaS_rot, hd]
    ring
  simp only [Eis, he, integral_const_mul]

end UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation

open UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation in
theorem UpperTheory.HilbertEisensteinWeightOne.weight_holds : SPois → SInt → SSmooth → SWt := by
  intro _ _ _ F _ _ _ ω c _ hs v
  set φ : UpperTheory.V.TR.Sm F 2 := ⟨Eis ω (Phi c), hs⟩
  have hX : UpperTheory.V.TR.Eop v 0 1 φ - UpperTheory.V.TR.Eop v 1 0 φ = UpperTheory.V.TR.lie F 2 (Xv v) φ := by
    unfold UpperTheory.V.TR.Eop
    rw [← LinearMap.sub_apply, ← map_sub]
    rfl
  rw [hX]
  apply Subtype.ext
  funext g
  have h1 := UpperTheory.V.TR.hasDerivAt_curve φ g (fun t => Unitary.toUnits (rotv v t)) (Xv v)
    (by rw [rotv_zero, map_one]) (rot_deriv v)
  have h2 : HasDerivAt (fun t : ℝ => φ.1 (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v t))))
      (Complex.I * φ.1 g) 0 := by
    have e : (fun t : ℝ => φ.1 (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v t)))) =
        fun t : ℝ => Complex.exp (t * Complex.I) * φ.1 g := funext fun t => eis_rot ω c v t g
    rw [e]
    have h3 := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).cexp.mul_const (φ.1 g)
    simpa using h3
  rw [UpperTheory.V.TR.lie_apply, h1.unique h2]
  simp [φ]
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ImportsAlt
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

theorem top (hP : SPois) (hI : SPois → SInt) (hG : SPois → SInt → SSmooth → SGrowth) (hS : SPois → SInt → SSmooth)
    (hL : SPois → SInt → SSmooth → SLeft) (hV : SPois → SInt → SSmooth → SLevel) (hO : SPois → SInt → SSmooth → SOpen) (hC : SPois → SInt → SSmooth → SCent)
    (hK : SPois → SInt → SSmooth → SKfin) (hW : SPois → SInt → SSmooth → SWt) (hLo : SPois → SInt → SSmooth → SLow) (hZ : SPois → SInt → SSmooth → SZfin)
    (hE : SPois → SInt → SSmooth → SExp) (hM : SPois → SInt → SSmooth → SSmul) : HilbertEisOne := by
  have hI' := hI hP
  have hS' := hS hP hI'
  intro F _ _ _ ω c hfin hodd hcond hram
  have H : Hyp ω c := ⟨hfin, hodd, hcond, hram⟩
  obtain ⟨C₀, L, hC₀, hexp⟩ := hE hP hI' hS' F ω c H
  have hs := hS' F ω c H
  let φ : UpperTheory.V.TR.Sm F 2 := ⟨Eis ω (Phi c), hs⟩
  have hlev : ∀ w, φ ∈ UpperTheory.V.Hi.fixd (locSm F w) (K1 w (c w)) := by
    intro w k hk
    refine Subtype.ext (funext fun g => ?_)
    exact hV hP hI' hS' F ω c H w k hk g
  have hcent := hC hP hI' hS' F ω c H
  have hwt := hW hP hI' hS' F ω c H hs
  have hlow := hLo hP hI' hS' F ω c H hs
  have hol : IsHol 1 c ω φ :=
    { aut := ⟨hL hP hI' hS' F ω c, hO hP hI' hS' F ω c H hs, hK hP hI' hS' F ω c H hs, hZ hP hI' hS' F ω c hfin φ hcent hwt hlow,
        hG hP hI' hS' F ω c H⟩
      level := hlev
      cent := hcent
      wt := hwt
      low := hlow }
  have hM' := hM hP hI' hS' F ω c 1 φ C₀⁻¹ (inv_ne_zero hC₀)
  refine ⟨C₀⁻¹ • φ, C₀⁻¹ * L, hM'.1 hol, ?_⟩
  have h2 := hM'.2 _ _ hexp
  convert h2 using 2
  rw [← mul_assoc, inv_mul_cancel₀ hC₀, one_mul]

end UpperTheory.HilbertEisensteinWeightOne
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SLevel
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.LevelEisenstein

variable {F : Type} [Field F] [NumberField F]

theorem v_le_of_mem_pow (w : HeightOneSpectrum (𝓞 F)) : ∀ (n : ℕ) (a : w.adicCompletionIntegers F),
    a ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ n →
    Valued.v (a : w.adicCompletion F) ≤ WithZero.exp (-(n : ℤ))
  | 0, a, _ => by rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]; exact a.2
  | n + 1, a, ha => by
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on (C := fun a : w.adicCompletionIntegers F =>
      Valued.v (a : w.adicCompletion F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))) ha ?_ ?_
    · intro x hx y hy
      have h1 := v_le_of_mem_pow w n x hx
      have hy1 : Valued.v (y : w.adicCompletion F) < 1 := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
          HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hy
        exact lt_of_le_of_ne y.2 hy
      have h2 : Valued.v (y : w.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
        by_cases h0 : Valued.v (y : w.adicCompletion F) = 0
        · rw [h0]; exact zero_le
        · rw [← WithZero.exp_log h0] at hy1 ⊢
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy1
          rw [WithZero.exp_le_exp]; omega
      show Valued.v ((x : w.adicCompletion F) * (y : w.adicCompletion F)) ≤ _
      rw [map_mul]
      refine (mul_le_mul' h1 h2).trans_eq ?_
      rw [← WithZero.exp_add]
      congr 1
      push_cast
      ring
    · intro x y hx hy
      show Valued.v ((x : w.adicCompletion F) + (y : w.adicCompletion F)) ≤ _
      exact (Valued.v.map_add _ _).trans (max_le hx hy)

theorem congruence_subgroup_entries_bound {w : HeightOneSpectrum (𝓞 F)} {n : ℕ} {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w n) :
    (∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j) ≤ 1) ∧
      Valued.v ((k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v ((k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨k', hk', rfl⟩ := hk
  have hk'' := hk'
  change ![0, 1] ᵥ* _ = ![0, 1] at hk''
  have h0 := congrFun hk'' 0
  have h1 := congrFun hk'' 1
  have m0 : k' 1 0 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ n := by
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0
    change 0 * _ + 1 * Ideal.Quotient.mk _ (k' 1 0) = 0 at h0
    rwa [zero_mul, one_mul, zero_add] at h0
  have m1 : k' 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ n := by
    refine Ideal.Quotient.eq.1 ?_
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using h1
  refine ⟨fun i j => (k' i j).2, v_le_of_mem_pow w n _ m0, ?_⟩
  have := v_le_of_mem_pow w n _ m1
  simpa using this

theorem loc_vecMul {w : HeightOneSpectrum (𝓞 F)} {n : ℕ} {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w n)
    {y : Fin 2 → w.adicCompletion F}
    (hy : Valued.v (y 0) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (y 1 - 1) ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v ((y ᵥ* (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) 0) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v ((y ᵥ* (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) 1 - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨he, h10, h11⟩ := congruence_subgroup_entries_bound hk
  have hε : WithZero.exp (-(n : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hmul : ∀ {a b : w.adicCompletion F} {A B : WithZero (Multiplicative ℤ)}, Valued.v a ≤ A → Valued.v b ≤ B →
      Valued.v (a * b) ≤ A * B := fun ha hb => by rw [map_mul]; exact mul_le_mul' ha hb
  have hadd : ∀ {a b : w.adicCompletion F} {C : WithZero (Multiplicative ℤ)}, Valued.v a ≤ C → Valued.v b ≤ C →
      Valued.v (a + b) ≤ C := fun ha hb => (Valued.v.map_add _ _).trans (max_le ha hb)
  have hy1 : Valued.v (y 1) ≤ 1 := by
    have : y 1 = (y 1 - 1) + 1 := by ring
    rw [this]
    exact hadd (hy.2.trans hε) (by rw [map_one])
  constructor
  · have e : (y ᵥ* (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) 0 =
        y 0 * (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 0 0 +
          y 1 * (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0 := by
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [e]
    exact hadd ((hmul hy.1 (he 0 0)).trans_eq (mul_one _)) ((hmul hy1 h10).trans_eq (one_mul _))
  · have e : (y ᵥ* (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) 1 - 1 =
        y 0 * (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 0 1 +
          (y 1 - 1) * (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 +
          ((k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) := by
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      ring
    rw [e]
    exact hadd (hadd ((hmul hy.1 (he 0 1)).trans_eq (mul_one _)) ((hmul hy.2 (he 1 1)).trans_eq (mul_one _))) h11

theorem norm_det_congruence_subgroup {w : HeightOneSpectrum (𝓞 F)} {n : ℕ} {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w n) :
    ‖((Matrix.GeneralLinearGroup.det k : (w.adicCompletion F)ˣ) : w.adicCompletion F)‖ = 1 := by
  obtain ⟨k', -, rfl⟩ := hk
  rw [det_map]
  refine GroundTheory.Global.IdeleGroup.norm_eq_one_of_mul_eq_one
    (b := (w.adicCompletionIntegers F).subtype ((Matrix.GeneralLinearGroup.det k')⁻¹ : (w.adicCompletionIntegers F)ˣ))
    ?_ (SetLike.coe_mem _) (SetLike.coe_mem _)
  rw [← map_mul, Units.mul_inv, map_one]

variable [IsTotallyReal F]

theorem pInf_vecMul (w : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (w.adicCompletion F)) (x : Fin 2 → Ad F) (i : Fin 2) :
    UpperTheory.V.TR.pInf F ((x ᵥ* ((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) i) =
      UpperTheory.V.TR.pInf F (x i) := by
  have hK := UpperTheory.V.TR.pInf_finGL (E := F) (a := 2) (locGL F 2 w k)
  have hKij : ∀ a b, UpperTheory.V.TR.pInf F (((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) a b) =
      (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) a b := fun a b =>
    congrArg (fun M : GL (Fin 2) (UpperTheory.V.TR.Rinf F) => (M : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) a b) hK
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, hKij]
  fin_cases i <;> simp [Fin.sum_univ_two, Matrix.one_apply]

theorem pLoc_vecMul (w v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (w.adicCompletion F)) (x : Fin 2 → Ad F)
    (i : Fin 2) :
    pLoc F v (pFin F ((x ᵥ* ((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) i)) =
      ((fun j => pLoc F v (pFin F (x j))) ᵥ*
        ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w k) : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) i := by
  have hK := pFin_finGL (E := F) (a := 2) (locGL F 2 w k)
  have hKij : ∀ a b, pFin F (((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) a b) =
      ((locGL F 2 w k : GL (Fin 2) (Af F)) : Matrix (Fin 2) (Fin 2) (Af F)) a b := fun a b =>
    congrArg (fun M : GL (Fin 2) (Af F) => (M : Matrix (Fin 2) (Fin 2) (Af F)) a b) hK
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, hKij]
  rfl

def cond (c : HeightOneSpectrum (𝓞 F) → ℕ) (x : Fin 2 → Ad F) : Prop :=
  ∀ v, Valued.v (pLoc F v (pFin F (x 0))) ≤ WithZero.exp (-(c v : ℤ)) ∧
    Valued.v (pLoc F v (pFin F (x 1)) - 1) ≤ WithZero.exp (-(c v : ℤ))

theorem cond_mul (c : HeightOneSpectrum (𝓞 F) → ℕ) {w : HeightOneSpectrum (𝓞 F)} {k : GL (Fin 2) (w.adicCompletion F)}
    (hk : k ∈ K1 w (c w)) {x : Fin 2 → Ad F} (hx : cond c x) :
    cond c (x ᵥ* ((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) := by
  intro v
  rw [pLoc_vecMul, pLoc_vecMul]
  by_cases hv : v = w
  · subst hv
    rw [pLoc_locGL]
    exact loc_vecMul hk (hx v)
  · rw [pLoc_locGL_of_ne hv, Units.val_one, Matrix.vecMul_one]
    exact hx v

theorem cond_iff (c : HeightOneSpectrum (𝓞 F) → ℕ) {w : HeightOneSpectrum (𝓞 F)} {k : GL (Fin 2) (w.adicCompletion F)}
    (hk : k ∈ K1 w (c w)) (x : Fin 2 → Ad F) :
    cond c (x ᵥ* ((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) ↔ cond c x := by
  refine ⟨fun h => ?_, cond_mul c hk⟩
  have := cond_mul c (inv_mem hk) h
  rwa [Matrix.vecMul_vecMul, ← Units.val_mul, map_inv, map_inv, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one] at this

theorem Phi_vecMul (c : HeightOneSpectrum (𝓞 F) → ℕ) {w : HeightOneSpectrum (𝓞 F)} {k : GL (Fin 2) (w.adicCompletion F)}
    (hk : k ∈ K1 w (c w)) (x : Fin 2 → Ad F) :
    Phi c (x ᵥ* ((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) = Phi c x := by
  unfold Phi
  rw [pInf_vecMul, pInf_vecMul]
  congr 2
  exact propext (cond_iff c hk x)

theorem thetaS_mul (c : HeightOneSpectrum (𝓞 F) → ℕ) {w : HeightOneSpectrum (𝓞 F)} {k : GL (Fin 2) (w.adicCompletion F)}
    (hk : k ∈ K1 w (c w)) (h : GA F 2) :
    thetaS (Phi c) (h * finGL F 2 (locGL F 2 w k)) = thetaS (Phi c) h := by
  unfold thetaS
  refine tsum_congr fun ξ => ?_
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, Phi_vecMul c hk]

theorem absD_mul (g h : GA F 2) : absD (g * h) = absD g * absD h := by
  unfold absD
  rw [map_mul, map_mul, Positive.val_mul]

theorem absD_K {w : HeightOneSpectrum (𝓞 F)} {n : ℕ} {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w n) :
    absD (finGL F 2 (locGL F 2 w k)) = 1 := by
  unfold absD
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have hp : UpperTheory.V.TR.pInf F
      ((Matrix.GeneralLinearGroup.det (finGL F 2 (locGL F 2 w k)) : (Ad F)ˣ) : Ad F) = 1 := by
    rw [← det_map, UpperTheory.V.TR.pInf_finGL]
    simp
  have hinf' : ((Matrix.GeneralLinearGroup.det (finGL F 2 (locGL F 2 w k)) : (Ad F)ˣ) : Ad F).1 = 1 :=
    (UpperTheory.V.TR.infEq F).symm.injective (hp.trans (map_one _).symm)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((Matrix.GeneralLinearGroup.det (finGL F 2 (locGL F 2 w k)) : (Ad F)ˣ) : Ad F).2 v‖ = 1 := by
    intro v
    have e : ((Matrix.GeneralLinearGroup.det (finGL F 2 (locGL F 2 w k)) : (Ad F)ˣ) : Ad F).2 v =
        ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w k)) :
          (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      change pLoc F v (pFin F ((Matrix.GeneralLinearGroup.det (finGL F 2 (locGL F 2 w k)) : (Ad F)ˣ) : Ad F)) = _
      rw [← det_map (pFin F), pFin_finGL, ← det_map]
    rw [e]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL]
      exact norm_det_congruence_subgroup hk
    · rw [pLoc_locGL_of_ne hv]
      simp
  rw [hinf', finprod_eq_one_of_forall_eq_one hfin, mul_one]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [show (1 : InfiniteAdeleRing F) v = 1 from rfl, norm_one, one_pow]

end UpperTheory.HilbertEisensteinWeightOne.LevelEisenstein

namespace UpperTheory.HilbertEisensteinWeightOne

open LevelEisenstein in
theorem level_holds : SPois → SInt → SSmooth → SLevel := by
  intro _ _ _ F _ _ _ ω c _ w k hk g
  have e : eisInt ω (Phi c) (g * finGL F 2 (locGL F 2 w k)) = eisInt ω (Phi c) g := by
    funext t u
    unfold eisInt
    rw [← mul_assoc, thetaS_mul c hk, absD_mul, absD_K hk, mul_one]
  unfold Eis
  rw [e]

end UpperTheory.HilbertEisensteinWeightOne
end
end

open UpperTheory.HilbertEisensteinWeightOne in
theorem UpperTheory.V.Published.hilbert_eisenstein_weight_one_holds : UpperTheory.V.Published.HilbertEisOne :=
  top poisson_summation_holds s_integrality moderate_growth_holds smoothness_holds left_invariance_holds level_holds open_kernel_holds central_character_holds K_finiteness_holds
    weight_holds low_weight_holds center_finiteness_holds fourier_expansion_holds scalar_action_holds
