module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkNeTopOfNoGenerisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkNeTopOfNoGenerisation
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory

namespace GlobalTheory

theorem isFiniteLength_localized_of_minimal_prime {A B M N : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [Algebra A B] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime B p]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] (f : M →ₗ[A] N) [IsLocalizedModule p.primeCompl f]
    (h : ∀ q : Ideal A, q.IsPrime → Module.annihilator A M ≤ q → q ≤ p → q = p) :
    IsFiniteLength B N := by
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  have : Module.Finite B N := Module.Finite.of_isLocalizedModule p.primeCompl f
  have : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B p
  have : IsArtinianRing (B ⧸ Module.annihilator B N) := by
    rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
    refine ⟨inferInstance, Ring.krullDimLE_zero_iff.mpr fun Q hQ => ?_⟩
    let Q' := Q.comap (Ideal.Quotient.mk (Module.annihilator B N))
    have hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
    have h1 : Module.annihilator A M ≤ Q'.comap (algebraMap A B) := by
      intro a ha
      have : algebraMap A B a ∈ Module.annihilator B N := by
        rw [← map_annihilator_of_isLocalizedModule p.primeCompl f]
        exact Ideal.mem_map_of_mem _ ha
      simp only [Q', Ideal.mem_comap]
      rw [Ideal.Quotient.eq_zero_iff_mem.2 this]
      exact Q.zero_mem
    have h2 : Q'.comap (algebraMap A B) ≤ p := by
      rw [← IsLocalization.AtPrime.under_maximalIdeal B p]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ'.ne_top)
    have h3 : Ideal.under A Q' = p := h _ (Ideal.comap_isPrime _ _) h1 h2
    have h4 : Q' = IsLocalRing.maximalIdeal B := by
      rw [← IsLocalization.map_under p.primeCompl B Q', h3,
        IsLocalization.AtPrime.map_eq_maximalIdeal]
    have h5 : Q'.IsMaximal := h4 ▸ IsLocalRing.maximalIdeal.isMaximal B
    have h6 := Ideal.map_eq_top_or_isMaximal_of_surjective
      (Ideal.Quotient.mk (Module.annihilator B N)) Ideal.Quotient.mk_surjective h5
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h6
    exact h6.resolve_left hQ.ne_top
  exact isFiniteLength_of_isArtinianRing_annihilator

theorem QCoh.length_stalk_ne_top_of_no_generisation (X : Scheme.{0}) [IsLocallyNoetherian X]
    (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] (w : X)
    (h : ∀ y ∈ GlobalTheory.QCoh.support F, w ∈ closure ({y} : Set X) → y = w) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) ≠ ⊤ := by
  obtain ⟨U, hU, hx⟩ := QCoh.exists_affine_mem w
  obtain ⟨x, rfl⟩ : ∃ x' : U, x' = w := ⟨⟨w, hx⟩, rfl⟩
  have := hU.isLocalization_stalk x
  have := QCoh.isLocalizedModule_germLinear F hU x
  have := QCoh.finite_sections F hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  rw [Module.length_ne_top_iff]
  refine isFiniteLength_localized_of_minimal_prime (hU.primeIdealOf x).asIdeal
    (QCoh.germLinear F x) fun q hq h1 h2 => ?_
  let P : PrimeSpectrum Γ(X, U) := ⟨q, hq⟩
  have hP : hU.fromSpec P ∈ QCoh.support F := by
    have : P ∈ Module.support Γ(X, U) Γ(F, U) := Module.mem_support_iff_of_finite.2 h1
    rw [← QCoh.fromSpec_preimage_support F hU] at this
    exact this
  have hs : P ⤳ hU.primeIdealOf x := (PrimeSpectrum.le_iff_specializes _ _).1 h2
  have hs' : hU.fromSpec P ⤳ (x : X) := by
    rw [← hU.fromSpec_primeIdealOf x]
    exact hs.map hU.fromSpec.continuous
  have e := h _ hP (specializes_iff_mem_closure.1 hs')
  rw [← hU.fromSpec_primeIdealOf x] at e
  have e' : P = hU.primeIdealOf x := hU.fromSpec.isOpenEmbedding.injective e
  exact congrArg PrimeSpectrum.asIdeal e'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkNeTopOfNoGenerisationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_stalk_ne_infty_of_no_generization : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] (w : X), (∀ y ∈ GlobalTheory.QCoh.support F, w ∈ closure ({y} : Set X) → y = w) → Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) ≠ ⊤ := by
  first | exact @GlobalTheory.QCoh.length_stalk_ne_top_of_no_generisation | exact GlobalTheory.QCoh.length_stalk_ne_top_of_no_generisation | (intros; apply GlobalTheory.QCoh.length_stalk_ne_top_of_no_generisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingUnitsIntegralCofinite
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocNormTau

variable {p : ℕ} [Fact p.Prime]

def tauR (G : HTGroup p) (β : G.Cˣ) (R : Type) [CommRing R] [Algebra ℚ R] (x : R ⊗[ℚ] G.C) : R ⊗[ℚ] G.C :=
  inC G R (β : G.C) * (starT G.star R x).unop * inC G R ((β⁻¹ : G.Cˣ) : G.C)

variable (G : HTGroup p) (β : G.Cˣ) (R : Type) [CommRing R] [Algebra ℚ R]

theorem tauR_add (x y : R ⊗[ℚ] G.C) : tauR G β R (x + y) = tauR G β R x + tauR G β R y := by
  simp only [tauR, map_add (f := _), MulOpposite.unop_add, mul_add, add_mul]

theorem inC_inv_mul : inC G R ((β⁻¹ : G.Cˣ) : G.C) * inC G R (β : G.C) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

theorem tauR_mul (x y : R ⊗[ℚ] G.C) : tauR G β R (x * y) = tauR G β R y * tauR G β R x := by
  have h := inC_inv_mul G β R
  simp only [tauR, map_mul, MulOpposite.unop_mul, mul_assoc]
  congr 2
  rw [← mul_assoc (inC G R ((β⁻¹ : G.Cˣ) : G.C)), h, one_mul]

theorem tauR_one : tauR G β R 1 = 1 := by
  simp only [tauR, map_one, MulOpposite.unop_one, mul_one]
  rw [← map_mul, Units.mul_inv, map_one]

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem tauR_inC (c : G.C) :
    tauR G β R (inC G R c) = inC G R ((β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C)) := by
  have h : (starT G.star R (inC G R c)).unop = inC G R (sh G c) := by
    change (starT G.star R ((1 : R) ⊗ₜ c)).unop = (1 : R) ⊗ₜ (G.star c).unop
    exact starT_tmul G.star R 1 c
  simp only [tauR, h, map_mul]

theorem commute_inC_of_forall (e : G.C) (he : ∀ c : G.C, Commute e c) (x : R ⊗[ℚ] G.C) :
    Commute (inC G R e) x := by
  induction x using TensorProduct.induction_on with
  | zero => exact Commute.zero_right _
  | tmul r c =>
    change (1 : R) ⊗ₜ e * r ⊗ₜ c = r ⊗ₜ c * (1 : R) ⊗ₜ e
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, (he c).eq]
  | add x y hx hy => exact hx.add_right hy

end GlobalTheory.LocNormTau

namespace GlobalTheory.LocNormTau

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_neg (G : HTGroup p) : ∃ f : G.F, f ≠ 0 ∧ IsCMField.complexConj G.F f = -f := by
  have hne := IsCMField.complexConj_ne_one G.F
  obtain ⟨x, hx⟩ : ∃ x, IsCMField.complexConj G.F x ≠ x := by
    by_contra h
    push_neg at h
    exact hne (AlgEquiv.ext h)
  refine ⟨x - IsCMField.complexConj G.F x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
  simp [IsCMField.complexConj_apply_apply]

theorem norm_aux {A : Type*} [Ring A] (a b E : A) (ha : Commute E a) (hb : Commute E b) (hab : a * b = b * a) :
    (a + b * E) * (a - E * b) = a * a - E * E * (b * b) ∧ (a - E * b) * (a + b * E) = a * a - E * E * (b * b) := by
  have h1 : a * (E * b) = a * b * E := by rw [hb.eq, mul_assoc]
  have h2 : b * E * a = a * b * E := by rw [mul_assoc, ha.eq, ← mul_assoc, hab]
  have h3 : b * E * (E * b) = E * E * (b * b) := by
    calc b * E * (E * b) = b * (E * E) * b := by noncomm_ring
      _ = E * E * (b * b) := by rw [← (hb.mul_left hb).eq, mul_assoc]
  have h4 : E * b * a = a * b * E := by rw [mul_assoc, ← hab, (ha.mul_right hb).eq]
  have h5 : E * b * (b * E) = E * E * (b * b) := by
    calc E * b * (b * E) = E * ((b * b) * E) := by noncomm_ring
      _ = E * E * (b * b) := by rw [← (hb.mul_right hb).eq, mul_assoc]
  constructor
  · rw [show (a + b * E) * (a - E * b) = a * a - a * (E * b) + b * E * a - b * E * (E * b) by noncomm_ring,
      h1, h2, h3]
    abel
  · rw [show (a - E * b) * (a + b * E) = a * a + a * b * E - E * b * a - E * b * (b * E) by noncomm_ring,
      h4, h5]
    abel

end GlobalTheory.LocNormTau
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwap
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.SymplSkew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem herm_inv {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (a b : Fin n) :
    σ (J⁻¹ b a) = J⁻¹ a b := by
  have hmap : J.map σ = Jᵀ := by ext i j; simp [Matrix.transpose_apply, hJ.1 j i]
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have h1 : (J⁻¹).map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]; simp
  have h2 : (J⁻¹).map σ = (J⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, ← hmap]; exact (Matrix.inv_eq_left_inv h1).symm
  have := congrFun (congrFun h2 b) a
  rw [Matrix.map_apply] at this
  rw [this, Matrix.transpose_apply]

noncomputable def cEquiv (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) : AEF F E ≃ₐ[AF F] AEF F E :=
  Algebra.TensorProduct.congr (AlgEquiv.refl) (AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun e => hσ e) (AlgHom.ext fun e => hσ e))

theorem cEquiv_apply (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AEF F E) : cEquiv σ hσ z = cAF σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cAF_cAF (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AEF F E) : cAF σ (cAF σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) ((Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) (a ⊗ₜ e)) = a ⊗ₜ e
    simp [hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cAF_incAF (σ : E →ₐ[F] E) (e : E) : cAF σ (incAF F E e) = incAF F E (σ e) := by
  show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) ((1 : AF F) ⊗ₜ e) = (1 : AF F) ⊗ₜ σ e
  simp

theorem cAF_hOF (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) (x y : WOF F E nS nT) :
    cAF σ (hOF σ JS JT x y) = hOF σ JS JT y x := by
  unfold hOF
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, cAF_incAF, cAF_cAF σ hσ, herm_inv hS, hT.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem symplOF_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, σ ξ₀ = -ξ₀ → ∀ x y : WOF F E nS nT,
      symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  intro F E _ _ _ _ _ σ hσ nS nT JS JT hS hT ξ₀ hξ x y
  unfold symplOF
  have hx : incAF F E ξ₀ = cAF σ (incAF F E (-ξ₀)) := by rw [cAF_incAF, ← hξ, hσ]
  rw [← cAF_hOF σ hσ hS hT x y]
  have key : incAF F E ξ₀ * cAF σ (hOF σ JS JT x y) = cEquiv σ hσ (incAF F E (-ξ₀) * hOF σ JS JT x y) := by
    rw [cEquiv_apply, map_mul, ← hx]
  rw [key, Algebra.trace_eq_of_algEquiv, map_neg, neg_mul, map_neg]

end GlobalTheory.SymplSkew
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwapStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, σ ξ₀ = -ξ₀ → ∀ x y : WOF F E nS nT,
      symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  first | exact @GlobalTheory.SymplSkew.symplOF_swap | exact GlobalTheory.SymplSkew.symplOF_swap | (intros; apply GlobalTheory.SymplSkew.symplOF_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInf
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable (F : Type) [Field F] [NumberField F]

def finU : (Af F)ˣ →* (AF F)ˣ := Units.map (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem continuous_finU : Continuous (finU F) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

def sndU : (AF F)ˣ →* (Af F)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem continuous_circle_toUnits : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, by
    have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
    refine h.congr fun z => ?_
    simp⟩

theorem exists_cong_sub (K : Set (Af F)ˣ) (hK : K ∈ 𝓝 1) : ∃ M : ℕ, 0 < M ∧ ∀ u : (Af F)ˣ,
    (∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ (u : Af F) - 1 = M • c) →
    (∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ((u⁻¹ : (Af F)ˣ) : Af F) - 1 = M • c) → u ∈ K := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hK
  obtain ⟨T, hT, hTK⟩ := hK
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : Af F => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : Af F => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : Af F => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (Filter.inter_mem h1 h2)
  refine ⟨N, hN, fun u ⟨a, ha, e⟩ ⟨b, hb, e'⟩ => hTK (hTT ⟨?_, ?_⟩)⟩
  · change (u : Af F) ∈ T1
    rw [eq_add_of_sub_eq' e]; exact (hNW a ha).1
  · change MulOpposite.op ((u⁻¹ : (Af F)ˣ) : Af F) ∈ T2
    rw [eq_add_of_sub_eq' e']; exact (hNW b hb).2

theorem exists_cong_ker (lam : (AF F)ˣ →* Circle) (hlam : Continuous lam)
    (h : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) :
    ∃ M : ℕ, 0 < M ∧ ∀ b : (AF F)ˣ,
      (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1 := by
  let ψ : (Af F)ˣ →* ℂˣ := Circle.toUnits.comp (lam.comp (finU F))
  have hψ : Continuous ψ := (continuous_circle_toUnits).comp (hlam.comp (continuous_finU F))
  have hK := (GlobalTheory.CuspRep.isOpen_ker_finIdele F ψ hψ).mem_nhds (x := 1) (by simp)
  obtain ⟨M, hM, hMK⟩ := exists_cong_sub F _ hK
  refine ⟨M, hM, fun b hb hb' => ?_⟩
  obtain ⟨c, hc, e⟩ := hb
  obtain ⟨c', hc', e'⟩ := hb'
  have h2 : ψ (sndU F b) = 1 := hMK (sndU F b) ⟨c, hc, e⟩ ⟨c', hc', e'⟩
  have h3 : lam (finU F (sndU F b)) = 1 := by
    have := congrArg Units.val h2
    exact Subtype.ext (by simpa [ψ] using this)
  set a : (AF F)ˣ := b * (finU F (sndU F b))⁻¹ with ha
  have hfin : ((a : AF F)).2 = 1 := by
    show (b : AF F).2 * ((b⁻¹ : (AF F)ˣ) : AF F).2 = 1
    exact congrArg Prod.snd (Units.mul_inv b)
  have hA : At (evI F) ((a : AF F) - 1) := by
    intro u hu
    have hu1 : u.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu
    refine Prod.ext ?_ ?_
    · show u.1 * ((a : AF F).1 - 1) = 0
      rw [hu1, zero_mul]
    · show u.2 * ((a : AF F).2 - 1) = 0
      rw [hfin, sub_self, mul_zero]
  have hb : b = a * finU F (sndU F b) := by rw [ha, inv_mul_cancel_right]
  rw [hb, map_mul, h a hA, h3, mul_one]

end GlobalTheory.HeckeExtend

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInfStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity : ∀ (F : Type) [Field F] [NumberField F] (lam : (AF F)ˣ →* Circle), Continuous lam →
    (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) → ∃ M : ℕ, 0 < M ∧ ∀ b : (AF F)ˣ,
      (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1 := by
  first | exact @GlobalTheory.HeckeExtend.exists_cong_ker | exact GlobalTheory.HeckeExtend.exists_cong_ker | (intros; apply GlobalTheory.HeckeExtend.exists_cong_ker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongru
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongru
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend.TraceCE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def trAF : AF F ⊗[F] E →ₗ[AF F] AF F :=
  (Algebra.TensorProduct.rid F (AF F) (AF F)).toLinearMap ∘ₗ (Algebra.trace F E).baseChange (AF F)

theorem trAF_tmul (s : AF F) (e : E) :
    trAF (s ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) * s := by
  simp [trAF, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem gen_eq (s : AF F) (o : 𝓞 E) :
    algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o = s ⊗ₜ[F] (o : E) := by
  show (s ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] (o : E)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem intF_zero : (0 : AF F) ∈ intF F 1 := ⟨0, fun _ => zero_mem _, by rw [one_smul]; rfl⟩

theorem intF_add {x y : AF F} (hx : x ∈ intF F 1) (hy : y ∈ intF F 1) : x + y ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  obtain ⟨d, hd, e'⟩ := hy
  refine ⟨c + d, fun v => add_mem (hc v) (hd v), ?_⟩
  rw [one_smul] at e e' ⊢
  show x.2 + y.2 = c + d
  rw [e, e']

theorem intF_neg {x : AF F} (hx : x ∈ intF F 1) : -x ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  refine ⟨-c, fun v => neg_mem (hc v), ?_⟩
  rw [one_smul] at e ⊢
  show -x.2 = -c
  rw [e]

theorem intF_algebraMap (t : 𝓞 F) : algebraMap F (AF F) (t : F) ∈ intF F 1 :=
  ⟨algebraMap F (Af F) (t : F), fun v => HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v t,
    by rw [one_smul]; rfl⟩

theorem trAF_mem_of_mem_SE {z : AF F ⊗[F] E} (hz : z ∈ SE F E) : trAF z ∈ intF F 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, o, rfl⟩ := hg
    rw [gen_eq, trAF_tmul]
    have hi : IsIntegral ℤ (Algebra.trace F E (o : E)) := Algebra.isIntegral_trace o.2
    exact intF_one_mul (intF_algebraMap (⟨_, hi⟩ : 𝓞 F)) hs
  | zero => rw [map_zero]; exact intF_zero
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact intF_add ha hb
  | neg a _ ha => rw [map_neg]; exact intF_neg ha

theorem trAF_algebraMap (x : AF F) :
    trAF (algebraMap (AF F) (AF F ⊗[F] E) x) = Module.finrank F E • x := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, trAF_tmul]
  have h : Algebra.trace F E 1 = (Module.finrank F E : F) := by
    simpa using Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
  rw [h, map_natCast, nsmul_eq_mul]

theorem finrank_smul_mem_intF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (x : AF F),
    algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E N → Module.finrank F E • x ∈ intF F N := by
  intro F E _ _ _ _ _ N x h
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  have h1 := trAF_algebraMap (E := E) x
  rw [← e, map_nsmul] at h1
  obtain ⟨c, hc, ec⟩ := trAF_mem_of_mem_SE hs
  refine ⟨c, hc, ?_⟩
  rw [← h1]
  rw [one_smul] at ec
  rw [← ec]
  rfl

end GlobalTheory.HeckeExtend.TraceCE

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongruStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (x : AF F),
    algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E N → Module.finrank F E • x ∈ intF F N := by
  first | exact @GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF | exact GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF | (intros; apply GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowPartsFullSphericalAlgebraStableFiniteGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowPartsFullSphericalAlgebraStableFiniteGroup
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.RowPartStable

variable {D : D7}

theorem sphericalOperator_commute_levelFiniteGroup (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : LevDat D.host.E ℂ V.rank) (hB : IsBaseFrame V β Λ N) (P : Pl D.host.E) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) {d : List ℤ} {B : Finset (GA D V)}
    (hS : GlobalTheory.Hk3.SphOp V P d B) (g0 : G0 L.Pg L.r) (Φ : GA D V → ℂ) (hΦ : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, Φ (h * k) = Φ h) :
    actG0 V β L g0 (heckeLin V B Φ) = heckeLin V B (actG0 V β L g0 Φ) := by
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
  obtain ⟨hJ', -, hs'⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hP hN hPP
  unfold actG0
  split_ifs with hex
  · have hl := hex.choose_spec
    generalize hex.choose = κ at hl ⊢
    have hκ : κ ∈ levG V β (flagL L) := ⟨hl.1, hl.2.1, Subgroup.mem_top _⟩
    obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs' κ hκ
    have e1 : (fun x => (levChi V β (flagL L) (k₁ * k₂))⁻¹ * Φ (x * (k₁ * k₂))) =
      (levChi V β (flagL L) (k₁ * k₂))⁻¹ • fun x => Φ (x * (k₁ * k₂)) := rfl
    rw [e1, LinearMap.map_smul]
    funext h
    rw [GlobalTheory.LevOp.heckeLin_translate hP hJ' hS hΦ hk₁ s₁ s₂]
    rfl
  · rw [LinearMap.map_zero]

theorem mult_lev {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    {U : MMap M} (hU : U ∈ Mult θ M J χ) (v : M.Vec) (k : GA D V) (hk : k ∈ J) (g : GA D V) : U v (g * k) = χ k * U v g := by
  induction hU using Submodule.span_induction with
  | mem U hU => exact hU.lev v k hk g
  | zero => simp
  | add U U' _ _ h h' => simp [h, h', mul_add]
  | smul a U _ h => simp [h, mul_left_comm]

theorem map_gE_le : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → ∀ SF, IsSF R SF → ∀ c g, (EEc R SF c).map (R.gE g) ≤ EEc R SF c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hC SF hSF c g
  rintro _ ⟨x, hx, rfl⟩
  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    intro y
    have h : R.HE.e y ∈ R.EEat R.triv := hC.models.HE.2.1 ▸ LinearMap.mem_range_self _ y
    exact goodPart_le _ _ _ _ _ h
  have hx' := ((mem_partFull R.θ (R.MY 0) _ _ SF _ _).1 hx).2
  refine (mem_partFull R.θ (R.MY 0) _ _ SF _ _).2 ⟨hmem _, fun P d B hB v => ?_⟩
  obtain ⟨-, hgood, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hO : OffS D SF P := by
    obtain ⟨e, f, ϖ, α, h, -⟩ := hB
    exact h
  have hG : Good R A.μ0 P := (hoff SF hSF P).1 hO
  obtain ⟨n, hn⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hN : (((D.host.g 0 * D.host.g 1) ^ n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_pow]
    exact fun h => (hgood _ P hG).1 (P.isPrime.mem_of_pow_mem n h)
  have hPP : ∀ PP, PP ∈ (R.dat0 R.triv).Pg ∨ PP ∈ (R.dat0 R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    rcases hPP with hPP | hPP
    · exact hG PP (Or.inl hPP)
    · exact absurd hPP (Finset.notMem_empty _)
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hn P hN hPP
  have hS := ((h2 SF d B).1 hB).2
  have hfix : ∀ y, ∀ k ∈ GlobalTheory.Hk3.hyp (Yc D 0) P, ∀ h, R.HE.e y v (h * k) = R.HE.e y v h := by
    intro y k hk h
    rw [mult_lev _ _ _ _ (hmem y) v k (h1 k hk).1 h, (h1 k hk).2, one_mul]
  have hact : R.HE.e (R.gE g x) v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.HE.e x v) := by
    rw [hC.models.gE g x]; rfl
  have hcomm := sphericalOperator_commute_levelFiniteGroup (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hn P hN hPP hS (R.eG g) (R.HE.e x v) (hfix x)
  rw [hx' P d B hB v] at hcomm
  rw [hact]
  exact hcomm.symm.trans ((actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)).map_smul _ _)

end GlobalTheory.RowPartStable

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowPartsFullSphericalAlgebraStableFiniteGroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowParts_full_spherical_algebra_stable_finiteGroup : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → ∀ SF, IsSF R SF → ∀ c g, (EEc R SF c).map (R.gE g) ≤ EEc R SF c := by
  first | exact @GlobalTheory.RowPartStable.map_gE_le | exact GlobalTheory.RowPartStable.map_gE_le | (intros; apply GlobalTheory.RowPartStable.map_gE_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiples
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiples
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F : Type} [Field F] [NumberField F]


variable (F) in
theorem intF_isOpen (M : ℕ) (hM : 0 < M) : IsOpen (intF F M) := by
  let S : AddSubgroup (Af F) :=
    { carrier := {c | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a}
      zero_mem' := ⟨0, fun v => zero_mem _, (smul_zero M).symm⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun v => add_mem (ha v) (hb v), (smul_add M a b).symm⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun v => neg_mem (ha v), (smul_neg M a).symm⟩ }
  have hS : IsOpen (S : Set (Af F)) :=
    S.isOpen_of_mem_nhds (g := 0) (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F M hM)
  have e : intF F M = Prod.snd ⁻¹' (S : Set (Af F)) := by
    ext x
    constructor
    · rintro ⟨c, hc, e⟩
      exact ⟨c, hc, e⟩
    · rintro ⟨c, hc, e⟩
      exact ⟨c, hc, e⟩
  rw [e]
  exact hS.preimage continuous_snd

theorem exists_intF_one_mul (M : ℕ) (hM : 0 < M) {x : AF F} (hx : x ∈ intF F M) :
    ∃ s ∈ intF F 1, (M : AF F) * s = x := by
  obtain ⟨c, hc, e⟩ := hx
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  refine ⟨algebraMap F (AF F) ((M : F)⁻¹) * x, ⟨c, hc, ?_⟩, ?_⟩
  · show (algebraMap F (AF F) ((M : F)⁻¹)).2 * x.2 = 1 • c
    rw [e, one_smul, nsmul_eq_mul]
    have h2 : (algebraMap F (AF F) ((M : F)⁻¹)).2 = algebraMap F (Af F) ((M : F)⁻¹) := rfl
    rw [h2, ← mul_assoc, ← map_natCast (algebraMap F (Af F)) M, ← map_mul, inv_mul_cancel₀ hM', map_one, one_mul]
  · rw [← mul_assoc, ← map_natCast (algebraMap F (AF F)) M, ← map_mul, mul_inv_cancel₀ hM', map_one, one_mul]

end GlobalTheory.HeckeExtend

theorem GlobalTheory.HeckeExtend.CE_isOpen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ), 0 < N → IsOpen (CE F E N : Set (AF F ⊗[F] E)) := by
  intro F E _ _ _ _ _ N hN
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let b₀ := Module.finBasis F E
  have hint : ∀ i, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * b₀ i) := by
    intro i
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have : Algebra.IsAlgebraic ℤ E := Algebra.IsAlgebraic.trans ℤ ℚ E
    obtain ⟨y, hy, h⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := b₀ i) (Algebra.IsAlgebraic.isAlgebraic _)
    refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
    have h1 : (((y * y).natAbs : ℕ) : E) = (y : E) * (y : E) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y), Int.cast_mul]
    rw [h1, mul_assoc]
    rw [zsmul_eq_mul] at h
    exact (isIntegral_algebraMap (x := y)).mul h
  choose d hd hdint using hint
  let B := Algebra.TensorProduct.basis (AF F) b₀
  let U : Set (AF F ⊗[F] E) := ⋂ i, (fun z => B.repr z i) ⁻¹' intF F (N * d i)
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => (intF_isOpen F _ (Nat.mul_pos hN (hd i))).preimage ?_
    exact IsModuleTopology.continuous_of_linearMap (B.coord i)
  have h0 : (0 : AF F ⊗[F] E) ∈ U := by
    refine Set.mem_iInter.2 fun i => ⟨0, fun v => zero_mem _, ?_⟩
    show (B.repr 0 i).2 = (N * d i) • 0
    rw [map_zero, smul_zero]
    rfl
  have hsub : U ⊆ (CE F E N : Set (AF F ⊗[F] E)) := by
    intro z hz
    have hz' : ∀ i, B.repr z i ∈ intF F (N * d i) := fun i => Set.mem_iInter.1 hz i
    choose s hs hsx using fun i => exists_intF_one_mul (N * d i) (Nat.mul_pos hN (hd i)) (hz' i)
    refine mem_CE.2 ⟨∑ i, algebraMap (AF F) (AF F ⊗[F] E) (s i) * incAF F E ((⟨(d i : E) * b₀ i, hdint i⟩ : 𝓞 E) : E),
      sum_mem fun i _ => AddSubgroup.subset_closure ⟨s i, hs i, ⟨(d i : E) * b₀ i, hdint i⟩, rfl⟩, ?_⟩
    rw [Finset.smul_sum]
    conv_rhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsx i, Algebra.TensorProduct.basis_apply, nsmul_eq_mul, Algebra.smul_def]
    have h1 : incAF F E ((d i : E) * b₀ i) = (d i : AF F ⊗[F] E) * (1 ⊗ₜ b₀ i) := by
      rw [map_mul, map_natCast]
      rfl
    have hc : ((⟨(d i : E) * b₀ i, hdint i⟩ : 𝓞 E) : E) = (d i : E) * b₀ i := rfl
    rw [hc, h1, map_mul, map_natCast]
    push_cast
    ring
  exact (CE F E N).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds h0) hsub)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiplesStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_integralTensorAdeleMultiples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    IsOpen (CE F E N : Set (AF F ⊗[F] E)) := by
  first | exact @GlobalTheory.HeckeExtend.CE_isOpen | exact GlobalTheory.HeckeExtend.CE_isOpen | (intros; apply GlobalTheory.HeckeExtend.CE_isOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxSubsetOfMemNhdsZero
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.NearOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eventually_valuation_sub_lt_one (a : k) : ∀ᶠ x in nhds a, valuation k (x - a) < 1 := by
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨1, one_ne_zero, subset_rfl⟩
  have hc : Filter.Tendsto (fun x : k => x - a) (nhds a) (nhds 0) := by
    have : Continuous (fun x : k => x - a) := by fun_prop
    simpa using this.tendsto a
  exact hc h0

theorem exists_box_subset_of_mem_nhds_zero {p q : ℕ} {S : Set (Matrix (Fin p) (Fin q) k)} (hS : S ∈ nhds 0) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ box p q d ⊆ S := by
  have hk : ∀ s ∈ nhds (0 : k), ∀ᶠ d in nhds (0 : k), {x : k | valuation k x ≤ valuation k d} ⊆ s := by
    intro s hs
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
    have h0 : {x : k | valuation k x < r} ∈ nhds (0 : k) :=
      (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨r, hr, subset_rfl⟩
    filter_upwards [h0] with d hd x hx
    exact hrs (lt_of_le_of_lt hx hd)
  have hS' : {x : Fin p → Fin q → k | Matrix.of x ∈ S} ∈ nhds (0 : Fin p → Fin q → k) := hS
  rw [nhds_pi, Filter.mem_pi'] at hS'
  obtain ⟨I, t, ht, hI⟩ := hS'
  have ht' : ∀ i, ∃ u : Fin q → Set k, (∀ j, u j ∈ nhds (0 : k)) ∧ Set.univ.pi u ⊆ t i := by
    intro i
    have h := ht i
    rw [nhds_pi, Filter.mem_pi'] at h
    obtain ⟨J, u, hu, hJ⟩ := h
    exact ⟨u, hu, fun x hx => hJ fun j _ => hx j trivial⟩
  choose u hu hut using ht'
  have hev : ∀ᶠ d in nhds (0 : k), valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j :=
    (eventually_valuation_sub_lt_one 0).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hk _ (hu i j))
  have hne : ∃ d : k, d ≠ 0 ∧ valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j := by
    have hd : (nhdsWithin (0 : k) {0}ᶜ).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
      intro s hs
      obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
      obtain ⟨r', hr', hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
      obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective r
      have hy : y ≠ 0 := by simpa using hr
      refine ⟨r' * y, hrs ?_, mul_ne_zero (by simpa using hr') hy⟩
      show valuation k (r' * y) < valuation k y
      rw [map_mul]
      exact mul_lt_of_lt_one_left (zero_lt_iff.mpr hr) hr1
    exact (eventually_mem_nhdsWithin.and (hev.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ)))).exists
  obtain ⟨d, hd0, hd1, hdu⟩ := hne
  refine ⟨Units.mk0 d hd0, by simpa using hd1.le, fun X hX => hI fun i _ => hut i fun j _ => hdu i j (hX i j)⟩

theorem one_add_small_near_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ nhds (1 : GL (Fin n) k)) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ ∀ N ∈ box n n d, ∃ A : GL (Fin n) k, A.val = 1 + N ∧ A ∈ U ∧
      valuation k (GeneralLinearGroup.det A : k) = 1 ∧ A⁻¹.val ∈ box n n 1 := by
  have hadd : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => 1 + N) (nhds 0) (nhds 1) := by
    have : Continuous (fun N : Matrix (Fin n) (Fin n) k => 1 + N) := by fun_prop
    simpa using this.tendsto 0
  have hdet : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N).det) (nhds 0) (nhds 1) := by
    have : Continuous (fun M : Matrix (Fin n) (Fin n) k => M.det) := continuous_id.matrix_det
    have h2 := (this.tendsto 1).comp hadd
    rw [det_one] at h2
    exact h2
  have hinv : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N)⁻¹) (nhds 0) (nhds 1) := by
    have : ContinuousAt Inv.inv (1 : Matrix (Fin n) (Fin n) k) := by
      apply continuousAt_matrix_inv
      rw [det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h2 := this.tendsto.comp hadd
    rw [inv_one] at h2
    exact h2
  have hv : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, valuation k (1 + N).det = 1 := by
    filter_upwards [hdet (eventually_valuation_sub_lt_one 1)] with N hN
    have hN' : valuation k ((1 + N).det - 1) < 1 := hN
    have := Valuation.map_one_add_of_lt (valuation k) hN'
    simpa using this
  have hb : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, ∀ i j, valuation k ((1 + N)⁻¹ i j) ≤ 1 := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    have hc : Continuous (fun M : Matrix (Fin n) (Fin n) k => M i j) := continuous_id.matrix_elem i j
    filter_upwards [((hc.tendsto 1).comp hinv) (eventually_valuation_sub_lt_one _)] with N hN
    have hN' : valuation k ((1 + N)⁻¹ i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := hN
    have h1 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have := Valuation.map_add_le (valuation k) hN'.le h1
    simpa using this
  have hval : ∀ N : Matrix (Fin n) (Fin n) k, valuation k (1 + N).det = 1 → (toGL (1 + N)).val = 1 + N := by
    intro N hN
    have hu : IsUnit (1 + N) := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro h
      rw [h] at hN
      simp at hN
    unfold toGL
    rw [dite_eq_left hu]
    rfl
  have hGL : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => toGL (1 + N)) (nhds 0) (nhds 1) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    have h3 := hadd.prodMk_nhds ((MulOpposite.continuous_op.tendsto 1).comp hinv)
    have e : (Units.embedProduct _ (1 : GL (Fin n) k)) = (1, MulOpposite.op 1) := by simp
    rw [e]
    refine Filter.Tendsto.congr' ?_ h3
    filter_upwards [hv] with N hN
    simp only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, hval N hN]
  obtain ⟨d, hd, hS⟩ := exists_box_subset_of_mem_nhds_zero (p := n) (q := n) (hv.and (hb.and (hGL hU)))
  refine ⟨d, hd, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS hN
  refine ⟨toGL (1 + N), hval N h1, h3, ?_, fun i j => ?_⟩
  · rw [GeneralLinearGroup.val_det_apply, hval N h1, h1]
  · rw [Matrix.coe_units_inv, hval N h1]
    simpa using h2 i j

end GlobalTheory.GamMul.NearOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCanonicalBundleBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCanonicalBundleBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem cls_canonLB_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f'] (K : CanonLB f d) (K' : CanonLB f' d), IsPullback π f' f (spMap φ) → cls K'.bundle K'.isLB = CechPic.pull π (cls K.bundle K.isLB) := by
  intro R R' _ _ φ X X' f f' π d _ _ K K' H
  rw [← cls_pull K.isLB π (K.baseChange H).isLB]
  exact (cls_eq_iff _ _).2 (CanonLB.lbIso K' (K.baseChange H))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCanonicalBundleBaseChangeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardClass_canonicalBundle_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f'] (K : CanonLB f d) (K' : CanonLB f' d), IsPullback π f' f (spMap φ) → cls K'.bundle K'.isLB = CechPic.pull π (cls K.bundle K.isLB) := by
  first | exact @GlobalTheory.cls_canonLB_baseChange | exact GlobalTheory.cls_canonLB_baseChange | (intros; apply GlobalTheory.cls_canonLB_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSubschemeClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem openSubscheme_closedFibre_lift (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R')
    (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X'.Opens)
    (hφ : Function.Surjective φ) (h : IsPullback π f' f (spMap φ)) :
    ∃ (W : X.Opens) (ρ : U.toScheme ⟶ W.toScheme), ρ ≫ W.ι = U.ι ≫ π ∧
      IsPullback ρ (U.ι ≫ f') (W.ι ≫ f) (spMap φ) := by
  have hsp : IsClosedImmersion (spMap φ) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  have hπ : IsClosedImmersion π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) h.flip hsp
  obtain ⟨t, ht, hts⟩ :=
    (IsClosedImmersion.isClosedEmbedding π).isInducing.isOpen_iff.mp U.isOpen
  let W : X.Opens := ⟨t, ht⟩
  have hW : π ⁻¹ᵁ W = U := Opens.ext hts
  subst hW
  refine ⟨W, π ∣_ W, morphismRestrict_ι π W, ?_⟩
  exact IsPullback.paste_vert (isPullback_morphismRestrict π W) h

end GlobalTheory
end
