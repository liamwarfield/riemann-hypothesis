module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMassOfFibre
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussNormEqCoeffGaussNorm
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartKernel
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeChartArea

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

variable {m n : ℕ}

theorem HermNorm.pointOf_add' (h : HermNorm n) (v w : EuclideanSpace ℂ (Fin n)) :
    h.pointOf (v + w) = h.pointOf v + h.pointOf w := by
  simp only [HermNorm.pointOf]
  rw [← Matrix.mulVec_add]
  rfl

theorem HermNorm.pointOf_smul' (h : HermNorm n) (c : ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOf (c • v) = c • h.pointOf v := by
  simp only [HermNorm.pointOf]
  rw [← Matrix.mulVec_smul]
  rfl

def coneTangent (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (y : EuclideanSpace ℂ (Fin n)) : Submodule ℂ (EuclideanSpace ℂ (Fin n)) where
  carrier := {v | ∀ q ∈ J, ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf v j = 0}
  add_mem' {v w} hv hw q hq := by
    simp only [HermNorm.pointOf_add', Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hv q hq, hw q hq, add_zero]
  zero_mem' q _ := by
    have h0 : h.pointOf 0 = 0 := by simpa using h.pointOf_smul' 0 0
    simp [h0]
  smul_mem' c v hv q hq := by
    simp only [HermNorm.pointOf_smul', Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      ← Finset.mul_sum]
    rw [hv q hq, mul_zero]

def tangentJac (π : Fin m → Fin n → ℂ) (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : ℝ :=
  LinearMap.normDet (𝕜 := ℂ) (U := T) (V := EuclideanSpace ℂ (Fin m)) ((linProjₗ π).comp T.subtype) ^ 2

def coneJac (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : ℝ :=
  tangentJac π (coneTangent h J y)

def firstCoordVec (n : ℕ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j => if (j : ℕ) = 0 then 1 else 0

def leadCoordPlane (n m : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin n)) where
  carrier := {y | ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0}
  add_mem' {v w} hv hw j hj := by
    simp [hv j hj, hw j hj]
  zero_mem' j _ := by
    simp
  smul_mem' c v hv j hj := by
    simp [hv j hj]

def tangentGaussProfile (n m : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) *
      ENNReal.ofReal (tangentJac π (leadCoordPlane n m))

def ConeAreaFormula.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
    ∀ (π : Fin m → Fin n → ℂ) (g : EuclideanSpace ℂ (Fin m) → ℝ≥0∞), Measurable g →
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in coneSet h J, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w : EuclideanSpace ℂ (Fin m), (fibreCount h J π w : ℝ≥0∞) * g w

def ConeTangentAverage.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
          ∫⁻ y in coneSet h J,
            (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
              ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        ∫⁻ y in coneSet h J, tangentGaussProfile n m ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))

def ConeRadialIntegral.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → ∀ C : Set (EuclideanSpace ℂ (Fin n)),
    (∀ y ∈ C, ∀ t : ℝ, 0 < t → t • y ∈ C) →
    Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) {y | ‖y‖ < 1 ∧ y ∈ C} < ⊤ →
    ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ y in C, f ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) {y | ‖y‖ < 1 ∧ y ∈ C} *
          ∫⁻ r in Set.Ioi (0 : ℝ), f r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))

def TangentGaussMoment.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → m ≤ n →
    Measurable (tangentGaussProfile n m) ∧ AntitoneOn (tangentGaussProfile n m) (Set.Ici 0) ∧
      (∀ r : ℝ, 0 < tangentGaussProfile n m r) ∧
      0 < ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile n m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) ∧
      ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile n m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) < ⊤

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

namespace VerticalPartMultiplicity

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)

theorem length_localizedModule_quotient {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

theorem length_self_eq_of_ringEquiv {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by
  letI := RingHomInvPair.of_ringEquiv τ
  letI := RingHomInvPair.symm (↑τ : Q →+* Q') (τ.symm : Q' →+* Q)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap τ.toSemilinearEquiv)]

variable {n : ℕ}

end VerticalPartMultiplicity

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughPointIncIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ThroughPointIncIdeal.eval_aeval {F K : Type*} [Field F] [Field K] [Algebra F K] {σ τ : Type*}
    (s : σ → MvPolynomial τ K) (a : τ → K) (g : MvPolynomial σ F) :
    eval a (aeval s g) = aeval (fun i => eval a (s i)) g := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem ThroughPointIncIdeal.eval_genSubst_vanish {K : Type*} [Field K] {n k : ℕ} (x c : Fin n → K)
    (hc : ∑ j, c j * x j = 1) (a : Fin k × Fin n → K) (i : Fin k) :
    ∑ j, eval a (genSubst (k := k) x c (i, j)) * x j = 0 := by
  have h : ∀ j, eval a (genSubst (k := k) x c (i, j)) =
      a (i, j) - (∑ l, a (i, l) * x l) * c j := fun j => by simp [genSubst]
  simp_rw [h, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hc, mul_one, sub_self]

theorem ThroughPointIncIdeal.proof : ThroughPointIncIdeal.Statement := by
  intro F _ n k Q x c hc hinc g hg
  apply MvPolynomial.funext
  intro a
  rw [map_zero, ThroughPointIncIdeal.eval_aeval]
  have hu := hinc (fun ij => eval a (genSubst (k := k) x c ij))
    (ThroughPointIncIdeal.eval_genSubst_vanish x c hc a)
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
  exact hg _ hu

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealNeBotDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealNeBotDim.proof (h₁ : IncIdealDim.Statement) : IncIdealNeBotDim.Statement := by
  intro F _ n k Q hQ hI
  have := hQ.isPrime
  obtain ⟨j, -⟩ := hQ.isRelevant
  have hn : 0 < n := j.pos

  have hle : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((n : ℕ) : WithBot ℕ∞) := by
    have h := ringKrullDim_le_of_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((m : ℕ) : WithBot ℕ∞) := by
    have hbot : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = D at hle hbot ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd rfl hbot
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
        exact ENat.natCast_ne_top n (top_le_iff.mp (WithBot.coe_le_coe.mp h'))
      | coe m => exact ⟨m, rfl⟩
  have hm1 : 1 ≤ m := one_le_of_isProjPrime hQ hm
  rw [hm]
  by_contra hlt
  have hkm : k < m := by
    by_contra h
    exact hlt (by exact_mod_cast Nat.le_of_not_lt h)

  have hdim := h₁ F n k (m - 1) Q hQ (by rw [Nat.sub_add_cancel hm1]; exact hm)
  have hmin : min k (m - 1) = k := min_eq_left (by omega)
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn
  rw [hmin, Nat.sub_add_cancel hkn] at hdim

  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hgnz : g ∈ nonZeroDivisors (MvPolynomial (Fin k × Fin n) F) := mem_nonZeroDivisors_of_ne_zero hg0
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hgnz
  have h3 : ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ incIdeal Q k) ≤
      ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ Ideal.span {g}) :=
    ringKrullDim_le_of_surjective
      (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem _).mpr hg))
      (Ideal.Quotient.factor_surjective _)
  have hS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_add]
  rw [hdim] at h3
  rw [hS] at h2
  have h4 : (((k * n : ℕ) : WithBot ℕ∞)) + 1 ≤ ((k * n : ℕ) : WithBot ℕ∞) :=
    le_trans (add_le_add h3 le_rfl) h2
  have h5 : ((k * n + 1 : ℕ) : WithBot ℕ∞) ≤ ((k * n : ℕ) : WithBot ℕ∞) := by exact_mod_cast h4
  have h6 : k * n + 1 ≤ k * n := by exact_mod_cast h5
  omega

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIntChowFormExists
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

theorem chowFormExists : ChowFormExists.Statement :=
  ChowFormExists.of_affineChartTrdeg AffineChartTrdeg.proof

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetArea
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)

open scoped ENNReal ComplexOrder

theorem gramVol_nonneg {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    0 ≤ gramVol v y := by
  unfold gramVol
  dsimp only
  set w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  have hM : (Matrix.of fun a b => ∑ i, star (w a i) * w b i) =
      (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)ᴴ *
        Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h := (Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)).det_nonneg
  rw [← hM] at h
  exact (Complex.nonneg_iff.1 h).1

section Abstract

variable {E X W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

variable [MeasurableSpace X]

end Abstract

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealSeparate.proof (hZ : IncidenceZeroLocus.Statement) (hT : FormsThroughPoint.Statement)
    (hD : IncIdealNeBotDim.Statement) : IncIdealSeparate.Statement := by
  intro F _ n k P Q hP hQ hne hle q hqQ
  by_contra hqP
  have := hP.isPrime

  obtain ⟨φ, hφ⟩ : ∃ φ : (MvPolynomial (Fin n) F ⧸ P) →ₐ[F] AlgebraicClosure F,
      φ (Ideal.Quotient.mk P q) ≠ 0 := by
    by_contra h
    push Not at h
    exact hqP (Ideal.Quotient.eq_zero_iff_mem.mp
      (FGNullstellensatz.proof F (MvPolynomial (Fin n) F ⧸ P) (Ideal.Quotient.mk P q) h))
  let x : Fin n → AlgebraicClosure F := fun j => φ (Ideal.Quotient.mk P (X j))
  have hev : ∀ g, aeval x g = φ (Ideal.Quotient.mk P g) := by
    intro g
    have h : (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) =
        φ.comp (Ideal.Quotient.mkₐ F P) := by
      ext j
      simp [x]
    rw [h]
    rfl
  have hxq : aeval x q ≠ 0 := by rw [hev]; exact hφ
  have hx0 : x ≠ 0 := by
    intro h0
    apply hxq
    have hc : constantCoeff q = 0 := by
      by_contra hc
      have hmem := hQ.isHomog q hqQ 0
      rw [homogeneousComponent_zero, ← constantCoeff_eq] at hmem
      exact hQ.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map C))
    rw [h0, aeval_zero, hc, map_zero]

  obtain ⟨u, hux, huQ⟩ := hT F n k Q hQ (hD F n k Q hQ hne) x hx0 ⟨q, hqQ, hxq⟩
  apply huQ
  refine hZ F n k Q hQ.isHomog (AlgebraicClosure F) u fun g hg => ?_
  have hgP := hle hg
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hgP
  refine hgP u ⟨x, hx0, fun g' hg' => ?_, hux⟩
  rw [hev, Ideal.Quotient.eq_zero_iff_mem.mpr hg', map_zero]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLocalSectionLengthSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module Submodule
open scoped Pointwise

namespace LocalSectionLengthSum

theorem length_quot_smul_top_eq {B : Type*} [CommRing B] (I : Ideal B) (f : B) :
    Module.length B ((B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I))) =
      Module.length B (B ⧸ (I ⊔ Ideal.span {f})) := by
  let g : B →ₗ[B] (B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I)) :=
    (f • ⊤ : Submodule B (B ⧸ I)).mkQ ∘ₗ I.mkQ
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker g = I ⊔ Ideal.span {f} := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
      Quotient.mk_eq_zero, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul] at hy
      have hx : x = f * b - (f * b - x) := by ring
      rw [hx]
      exact sub_mem (mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
        (mem_sup_left hy)
    · intro hx
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]
      have h : f * a - (y + a * f) = -y := by ring
      rw [h]
      exact neg_mem hy
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq]

theorem length_pi_quot_smul_top_eq {B ι : Type*} [CommRing B] [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] (f : B) :
    Module.length B ((Π i, M i) ⧸ (f • ⊤ : Submodule B (Π i, M i))) =
      ∑ i, Module.length B (M i ⧸ (f • ⊤ : Submodule B (M i))) := by
  let g : (Π i, M i) →ₗ[B] (Π i, M i ⧸ (f • ⊤ : Submodule B (M i))) :=
    LinearMap.pi fun i => (f • ⊤ : Submodule B (M i)).mkQ ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro y
    choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)
    exact ⟨x, funext fun i => by simp [g, hx i]⟩
  have hker : LinearMap.ker g = f • ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · intro h
      have hx : ∀ i, ∃ y : M i, f • y = x i := fun i => by
        have h' := congrFun h i
        simpa [g, mem_smul_pointwise_iff_exists] using h'
      choose y hy using hx
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      funext i
      exact (Quotient.mk_eq_zero _).mpr (smul_mem_pointwise_smul (y i) f ⊤ mem_top)
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq, Module.length_pi_of_fintype]

end LocalSectionLengthSum

theorem LocalSectionLengthSum.proof (hPi : PiQuotCokerFiniteLength.Statement) :
    LocalSectionLengthSum.Statement := by
  intro B _ _ _ J f hJ hf hQ
  obtain ⟨hinj, hfin⟩ := hPi B J hJ hQ
  have hfinite := J.finite_minimalPrimes_of_isNoetherianRing B
  let _ : Fintype J.minimalPrimes := hfinite.fintype
  have hreg : Function.Injective fun x : ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) => f • x := by
    intro x y hxy
    funext P
    have : (P : Ideal B).IsPrime := P.2.1.1
    have h : f • x P = f • y P := congrFun hxy P
    rw [Algebra.smul_def, Algebra.smul_def] at h
    refine mul_left_cancel₀ ?_ h
    rw [Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hf P P.2
  have e1 := Model.TorsionFreeQuotientLength.length_quot_smul_eq (quotToPiMinimalPrimes J) hinj
    hreg hfin
  rw [← LocalSectionLengthSum.length_quot_smul_top_eq J f, ← e1,
    LocalSectionLengthSum.length_pi_quot_smul_top_eq]
  simp_rw [LocalSectionLengthSum.length_quot_smul_top_eq]
  exact (Finset.sum_subtype (p := (· ∈ J.minimalPrimes)) hfinite.toFinset
    (fun P => hfinite.mem_toFinset)
    (fun P : Ideal B => Module.length B (B ⧸ (P ⊔ Ideal.span {f})))).symm

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConePtsIntegral
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar ptsIntegral ptsIntegralAt pot)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.InhabitedChartFracSeparable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartFracSeparableInhabited

theorem chartLocDomain : ChartLocDomain.Statement :=
  ChartLocDomain.proof (IncIdealBelow.proof ChowFormMultiHomog.full) ChartIncDomain.proof
    (ChartKernel.proof IncidenceGeneric.full ChartIncDomain.proof)


end ChartFracSeparableInhabited



end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetAreaLintegral
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)

open scoped ENNReal

theorem gramVol_congr {e n : ℕ} {v v' : (Fin e → ℂ) → (Fin n → ℂ)} {y : Fin e → ℂ}
    (h : v =ᶠ[𝓝 y] v') : gramVol v y = gramVol v' y := by
  unfold gramVol
  rw [h.eq_of_nhds, h.fderiv_eq]

def gramForm {e n : ℕ} (p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ))) : ℝ :=
  let w : Fin (e + 1) → Fin n → ℂ := Fin.cons p.1 fun j => p.2 (Pi.single j 1)
  (Matrix.det (Matrix.of fun a b => ∑ i, star (w a i) * w b i)).re

theorem gramVol_eq_gramForm {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    gramVol v y = gramForm (v y, fderiv ℂ v y) := rfl

theorem continuous_gramForm {e n : ℕ} :
    Continuous (gramForm : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) → ℝ) := by
  have hw : Continuous fun p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) =>
      (Fin.cons p.1 fun j => p.2 (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) := by
    refine continuous_pi fun a => ?_
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa using continuous_fst
    · simpa using continuous_snd.clm_apply continuous_const
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp ((continuous_apply a).comp hw)).star.mul
    ((continuous_apply i).comp ((continuous_apply b).comp hw))

theorem aemeasurable_coneTerm {e n : ℕ} {U D : Set (Fin e → ℂ)} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hU : IsOpen U) (hDU : D ⊆ U)
    (hv : DifferentiableOn ℂ v U) (hF : Measurable F) :
    AEMeasurable (fun x => ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
      ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)) (volume.restrict D) := by
  have ha : AEMeasurable v (volume.restrict D) :=
    (hv.continuousOn.aemeasurable hU.measurableSet).mono_measure (Measure.restrict_mono hDU le_rfl)
  have hg : AEMeasurable (fun x => gramVol v x) (volume.restrict D) := by
    have h := continuous_gramForm.measurable.comp_aemeasurable
      (ha.prodMk (measurable_fderiv ℂ v).aemeasurable)
    simpa only [Function.comp_def, ← gramVol_eq_gramForm] using h
  have hmeas : Measurable fun p : (Fin e → ℂ) × ℂ => F (p.2 • WithLp.toLp 2 (ha.mk v p.1)) *
      ENNReal.ofReal (‖p.2‖ ^ (2 * e) * hg.mk _ p.1) := by
    refine (hF.comp (measurable_snd.smul ((PiLp.continuous_toLp 2 _).measurable.comp
      (ha.measurable_mk.comp measurable_fst)))).mul ?_
    exact ENNReal.measurable_ofReal.comp
      ((measurable_snd.norm.pow_const _).mul (hg.measurable_mk.comp measurable_fst))
  refine ⟨_, hmeas.lintegral_prod_right' (ν := (volume : Measure ℂ)), ?_⟩
  filter_upwards [ha.ae_eq_mk, hg.ae_eq_mk] with x h1 h2
  simp only [h1, h2]

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFibreDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

namespace ConeFibreDegree

theorem ae_eval_ne_zero_univ {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖u‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm u i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r) (fun u => eval u g ≠ 0)).mpr
    fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

theorem ae_eval_matrix_ne_zero {k n : ℕ} (g : MvPolynomial (Fin k × Fin n) ℂ) (hg : g ≠ 0) :
    ∀ᵐ π : Fin k → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) g ≠ 0 := by
  have hmap : (volume : Measure (Fin k → Fin n → ℂ)) =
      (volume : Measure (Fin k × Fin n → ℂ)).map (MeasurableEquiv.curry (Fin k) (Fin n) ℂ) := by
    rw [ObjectsHeight.map_curry_volume]
    rfl
  rw [hmap, (MeasurableEquiv.curry (Fin k) (Fin n) ℂ).measurableEmbedding.ae_map_iff]
  exact ae_eval_ne_zero_univ g hg

theorem ae_eval_euclid_ne_zero {m : ℕ} (g : MvPolynomial (Fin m) ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), eval (WithLp.ofLp w) g ≠ 0 := by
  let L : EuclideanSpace ℂ (Fin m) ≃L[ℝ] (Fin m → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin m => ℂ)
  have hac : (volume : Measure (EuclideanSpace ℂ (Fin m))).map L ≪ volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h : ∀ᵐ u ∂(volume : Measure (EuclideanSpace ℂ (Fin m))).map L, eval u g ≠ 0 :=
    hac.ae_le (ae_eval_ne_zero_univ g hg)
  rw [ae_map_iff L.continuous.measurable.aemeasurable] at h
  · exact h
  · exact (isClosed_eq (continuous_eval g) continuous_const).isOpen_compl.measurableSet

theorem fibreCount_eq {k n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (π : Fin k → Fin n → ℂ) (w : EuclideanSpace ℂ (Fin k)) :
    fibreCount h W π w =
      (ComplexSets.fibre W (Matrix.of π * (h.matᵀ)⁻¹) (WithLp.ofLp w)).encard := by
  have hu : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  have hinj : Function.Injective h.pointOf := by
    intro y y' hyy
    have hv := congrArg (fun v => (h.matᵀ)⁻¹ *ᵥ v) hyy
    simp only [HermNorm.pointOf, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec] at hv
    exact WithLp.ofLp_injective 2 hv
  have hπ : ∀ y : EuclideanSpace ℂ (Fin n),
      (Matrix.of π * (h.matᵀ)⁻¹) *ᵥ h.pointOf y = WithLp.ofLp (linProj π y) := by
    intro y
    rw [HermNorm.pointOf, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
    ext i
    simp [linProj, mulVec, dotProduct]
  rw [fibreCount, ← hinj.injOn.encard_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, ComplexSets.fibre, ComplexSets.zeroSet, coneSet]
  constructor
  · rintro ⟨y, ⟨hy, rfl⟩, rfl⟩
    exact ⟨hy, hπ y⟩
  · rintro ⟨hx, hxw⟩
    have hpt : h.pointOf (WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = x := by
      simp [HermNorm.pointOf, mulVec_mulVec, mul_nonsing_inv _ hu]
    refine ⟨WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x), ⟨?_, ?_⟩, hpt⟩
    · rw [hpt]; exact hx
    · apply WithLp.ofLp_injective 2
      rw [← hπ, hpt, hxw]

theorem proof (hD : ConeDimOfChowForm.Statement)
    (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hC : ComplexSets.DiscriminantCover.Statement) (hP : ProjDegreeChow.Statement) :
    ConeFibreDegree.Statement := by
  intro n e δ h W f hW hf hδ
  have hdim := hD ℂ n (e + 1) W f hW hf
  obtain ⟨⟨U, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hUfin⟩, -, -, -⟩ := hG n (e + 1) W hW.isPrime hdim
  rw [hS] at hA₀
  obtain ⟨p, hpS, hp⟩ := hA₀
  have hu : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  set B := (h.matᵀ)⁻¹ with hB
  set q : MvPolynomial (Fin (e + 1) × Fin n) ℂ :=
    bind₁ (fun ij => ∑ k, X (ij.1, k) * C (B k ij.2)) p with hqdef
  have hq : ∀ π : Fin (e + 1) → Fin n → ℂ,
      eval (fun ij => π ij.1 ij.2) q = eval (fun ij => (Matrix.of π * B) ij.1 ij.2) p := by
    intro π
    show eval₂Hom (RingHom.id ℂ) _ q = eval₂Hom (RingHom.id ℂ) _ p
    rw [hqdef, eval₂Hom_bind₁]
    congr 2
    funext ij
    simp [Matrix.mul_apply]
  have hq0 : q ≠ 0 := by
    intro h0
    have h1 := hq fun i j => (A₀ * h.matᵀ) i j
    have hA : Matrix.of (fun i j => (A₀ * h.matᵀ) i j) * B = A₀ := by
      rw [hB, show Matrix.of (fun i j => (A₀ * h.matᵀ) i j) = A₀ * h.matᵀ from rfl, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    rw [h0, map_zero, hA] at h1
    exact hp h1.symm
  filter_upwards [ae_eval_matrix_ne_zero q hq0] with π hπ
  have hfin : ComplexSets.IsFiniteProjection W (Matrix.of π * B) := by
    have hmem : Matrix.of π * B ∈ {A : Matrix (Fin (e + 1)) (Fin n) ℂ |
        ∃ p ∈ S, eval (fun ij => A ij.1 ij.2) p ≠ 0} := ⟨p, hpS, by rw [← hq]; exact hπ⟩
    rw [← hS] at hmem
    exact hUfin _ hmem
  obtain ⟨P, hP0, hPy⟩ := hC n (e + 1) W (Matrix.of π * B) hW.isPrime hdim hfin
  filter_upwards [ae_eval_euclid_ne_zero P hP0] with w hw
  obtain ⟨hfinite, hcard, -⟩ := hPy _ hw
  rw [fibreCount_eq, ← hfinite.cast_ncard_eq, hcard, hP n e δ W f _ hW hf hδ hfin]

end ConeFibreDegree

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormBirationalAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem not_dvd_pderiv_of_pderiv_ne_zero {F σ : Type*} [Field F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hne : pderiv i g ≠ 0) : ¬ g ∣ pderiv i g := by
  classical
  rintro ⟨q, hq⟩
  have hi : 0 < degreeOf i g := by
    obtain ⟨m, hm⟩ := support_nonempty.2 hne
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  have hlt : degreeOf i (pderiv i g) < degreeOf i g := by
    rw [degreeOf_lt_iff hi]
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  rw [hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))] at hlt
  omega

theorem IsChowForm.exists_pderiv_ne_zero {F : Type} [Field F] [IsAlgClosed F] {p : ℕ} [hp : Fact p.Prime]
    [CharP F p] {n k : ℕ} {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P)
    {g : MvPolynomial (Fin (k + 1) × Fin n) F} (hg : IsChowForm P (k + 1) g) :
    ∃ l, pderiv (0, l) g ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon

  have hall : ∀ v, pderiv v g = 0 := by
    rintro ⟨i, l⟩
    obtain ⟨c, hc2, hc⟩ := hg.rename_swap 0 i
    have hinj : Function.Injective (Prod.map (Equiv.swap (0 : Fin (k + 1)) i) (id : Fin n → Fin n)) :=
      (Equiv.swap 0 i).injective.prodMap Function.injective_id
    have h := pderiv_rename hinj (0, l) g
    rw [hc, pderiv_C_mul, hcon l, map_zero, Prod.map_apply, Equiv.swap_apply_left, id] at h
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc2
    exact (mul_eq_zero.1 h).resolve_left fun h0 => hc0 (C_eq_zero.1 h0)

  have hexp : ∀ s ∈ g.support, ∀ v, p ∣ s v := by
    intro s hs v
    by_cases h0 : s v = 0
    · simp [h0]
    have hle : Finsupp.single v 1 ≤ s := Finsupp.single_le_iff.2 (by omega)
    have h1 := congrArg (AddMonoidAlgebra.coeff · (s - Finsupp.single v 1)) (hall v)
    rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, tsub_add_cancel_of_le hle] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left (mem_support_iff.1 hs)
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same] at h2
    have h3 : ((s v : ℕ) : F) = 0 := by
      rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
      push_cast
      exact h2
    exact (CharP.cast_eq_zero_iff F p _).1 h3

  obtain ⟨h, hgh⟩ : ∃ h : MvPolynomial (Fin (k + 1) × Fin n) F, h ^ p = g := by
    have hroot : ∀ a : F, ∃ b : F, b ^ p = a := fun a => IsAlgClosed.exists_pow_nat_eq a hp.out.pos
    choose r hr using hroot
    refine ⟨∑ s ∈ g.support, monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) s) (r (AddMonoidAlgebra.coeff g s)), ?_⟩
    rw [sum_pow_char]
    conv_rhs => rw [as_sum g]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : p • Finsupp.mapRange (· / p) (Nat.zero_div p) s = s := by
      ext v
      simp [Nat.mul_div_cancel' (hexp s hs v)]
    rw [monomial_pow, hr, hs']

  have hmem : ∀ q, q ∈ incIdeal P (k + 1) ↔ g ∣ q := by
    intro q
    rw [← hg.2 q, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hprime : Prime g := by
    have hI := IncIdealPrime.full F n (k + 1) P hP.isPrime hP.isRelevant
    have hspan : incIdeal P (k + 1) = Ideal.span {g} := by
      ext q
      rw [Ideal.mem_span_singleton, hmem]
    rw [hspan] at hI
    exact (Ideal.span_singleton_prime hg.1).1 hI
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hg.1 (by rw [← hgh, zero_pow hp.out.ne_zero])
  obtain ⟨q, hq⟩ := hprime.dvd_of_dvd_pow (show g ∣ h ^ p by rw [hgh])
  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  have h1 : h * (h ^ (m + 1) * q) = h * 1 := by
    rw [mul_one]
    conv_rhs => rw [hq, ← hgh, hm]
    ring
  have hu : IsUnit (h ^ (m + 1)) := IsUnit.of_mul_eq_one q (mul_left_cancel₀ hh0 h1)
  have hu' : IsUnit h := (isUnit_pow_iff (Nat.succ_ne_zero m)).1 hu
  exact hprime.not_isUnit (hgh ▸ hu'.pow p)

theorem ChowFormBirationalAlgClosed.proof : ChowFormBirationalAlgClosed.Statement := by
  intro F _ _ n k P g c hP hg hc
  obtain _ | ⟨p, hp, hch⟩ := CharP.exists' F
  · exact ChowFormBirational.full F n k P g c hP hg hc
  have := hP.isPrime
  classical

  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (IncidenceGeneric.full F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)

  have hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) =
      C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l) := by
    intro m
    have h := pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g
    rw [hg0, map_zero] at h
    simp only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h
    rw [eq_comm, sub_eq_zero] at h
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩

  obtain ⟨l, hl⟩ := IsChowForm.exists_pderiv_ne_zero (p := p) hP hg
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_pderiv_ne_zero hg.1 hl
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l' _ => ?_
      ring

end

end GroundTheory.Heights₂.Heights
end
