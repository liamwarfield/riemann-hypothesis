module

public import ReciprocityTheory.Automorphisms.InstMainA
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentEigenvalueSumFormula
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
open NumberField IsDedekindDomain Polynomial

noncomputable section

-- Some compiled versions of `Unitary` omit this structure.
run_cmd do
  let name := `ReciprocityTheory.Aut.SplitPlace
  unless (← Lean.getEnv).contains name do
    Lean.Elab.Command.elabCommand (← `(
      structure $(Lean.mkIdent name) (L : Type*) [Field L] [NumberField L]
        [IsCMField L] where
        v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))
        i : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)))

namespace GlobalTheory.SplitSep

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L
local notation3 "cc" => IsCMField.complexConj L

theorem exists_near (v : HeightOneSpectrum (𝓞 L⁺))
    (f : v.adicCompletion L⁺ → v.adicCompletion L⁺) (hf : Continuous f)
    (y₀ : v.adicCompletion L⁺) (hy₀ : Valued.v (f y₀) < 1) :
    ∃ a : L⁺, Valued.v (f (algebraMap L⁺ (v.adicCompletion L⁺) a)) < 1 := by
  have hU : IsOpen {z : v.adicCompletion L⁺ | Valued.v (f z) < 1} := by
    have h := (Valued.isOpen_ball (v.adicCompletion L⁺) 1).preimage hf
    convert h using 2 with z
    simp [Valuation.restrict_lt_iff_lt_embedding]
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L⁺) (K := L⁺) v).exists_mem_open
    hU ⟨y₀, hy₀⟩
  exact ⟨k, hk⟩


variable (L) in
theorem exists_sep (s : ReciprocityTheory.Aut.SplitPlace L) :
    ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧
      Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := by
  obtain ⟨θ, hθ⟩ : ∃ θ : L, cc θ ≠ θ := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext h)
  obtain ⟨δ, hδ⟩ : ∃ δ : L, δ = θ - cc θ := ⟨_, rfl⟩
  have hcδ : cc δ = -δ := by rw [hδ, map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hδ0 : δ ≠ 0 := by rw [hδ]; exact sub_ne_zero.mpr (Ne.symm hθ)
  obtain ⟨t, ht_def⟩ : ∃ t : s.v.adicCompletion L⁺, t = s.i δ := ⟨_, rfl⟩
  have ht : t ≠ 0 := by rw [ht_def]; exact (_root_.map_ne_zero s.i).mpr hδ0
  have h2 : (2 : s.v.adicCompletion L⁺) ≠ 0 := by
    have e : (2 : s.v.adicCompletion L⁺) = algebraMap L⁺ _ 2 := by rw [map_ofNat]
    rw [e]
    exact (_root_.map_ne_zero _).mpr two_ne_zero
  have h2half : (2 : s.v.adicCompletion L⁺)⁻¹ + 2⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ h2]
  obtain ⟨a, ha⟩ := exists_near s.v (fun z => z - 2⁻¹) (by fun_prop) (2⁻¹) (by simp)
  have h0 : t⁻¹ * 2⁻¹ * t - 2⁻¹ = 0 := by
    rw [mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht, mul_one, sub_self]
  obtain ⟨b, hb⟩ := exists_near s.v (fun z => z * t - 2⁻¹)
    (by fun_prop) (t⁻¹ * 2⁻¹)
    (by simp only [h0, map_zero]; exact zero_lt_one)
  obtain ⟨x, hx⟩ : ∃ x : L, x = algebraMap L⁺ L a + algebraMap L⁺ L b * δ := ⟨_, rfl⟩
  have hix : s.i x = algebraMap L⁺ (s.v.adicCompletion L⁺) a +
      algebraMap L⁺ (s.v.adicCompletion L⁺) b * t := by
    rw [hx, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, ht_def]
  have hcx : cc x = algebraMap L⁺ L a - algebraMap L⁺ L b * δ := by
    rw [hx, map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcδ]; ring
  have hicx : s.i (cc x) = algebraMap L⁺ (s.v.adicCompletion L⁺) a -
      algebraMap L⁺ (s.v.adicCompletion L⁺) b * t := by
    rw [hcx, map_sub, map_mul, AlgHom.commutes, AlgHom.commutes, ht_def]
  have hx1 : Valued.v (s.i x) = 1 := by
    have e : s.i x - 1 = (algebraMap L⁺ (s.v.adicCompletion L⁺) a - 2⁻¹) +
        (algebraMap L⁺ (s.v.adicCompletion L⁺) b * t - 2⁻¹) := by
      rw [hix]; linear_combination h2half
    refine (Valued.v.map_eq_of_sub_lt ?_).trans (map_one _)
    rw [map_one, e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  have hcx1 : Valued.v (s.i (cc x)) < 1 := by
    have e : s.i (cc x) = (algebraMap L⁺ (s.v.adicCompletion L⁺) a - 2⁻¹) -
        (algebraMap L⁺ (s.v.adicCompletion L⁺) b * t - 2⁻¹) := by
      rw [hicx]; ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hb)
  have hT : cc (x + cc x) = x + cc x := by
    rw [map_add (f := _), IsCMField.complexConj_apply_apply, add_comm]
  have hN : cc (x * cc x) = x * cc x := by
    rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]
  let T : L⁺ := ⟨x + cc x, (IsCMField.complexConj_eq_self_iff (K := L) _).mp hT⟩
  let N : L⁺ := ⟨x * cc x, (IsCMField.complexConj_eq_self_iff (K := L) _).mp hN⟩
  have hTL : algebraMap L⁺ L T = x + cc x := rfl
  have hNL : algebraMap L⁺ L N = x * cc x := rfl
  have hvT : s.v.valuation L⁺ T ≤ 1 := by
    rw [← ReciprocityTheory.Aut.adic_valued_algebraMap s.v, ← s.i.commutes, hTL, map_add (f := _)]
    exact (Valuation.map_add _ _ _).trans (max_le hx1.le hcx1.le)
  have hvN : s.v.valuation L⁺ N ≤ 1 := by
    rw [← ReciprocityTheory.Aut.adic_valued_algebraMap s.v, ← s.i.commutes, hNL, map_mul,
      Valuation.map_mul, hx1, one_mul]
    exact hcx1.le
  obtain ⟨n₁, d₁, hd₁⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer s.v T hvT
  obtain ⟨n₂, d₂, hd₂⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer s.v N hvN
  obtain ⟨m, hm_def⟩ : ∃ m : 𝓞 L⁺, m = (d₁ : 𝓞 L⁺) * d₂ := ⟨_, rfl⟩
  have hm : m ∉ s.v.asIdeal := by rw [hm_def]; exact (d₁ * d₂).2
  obtain ⟨mK, hmK⟩ : ∃ mK : L⁺, mK = algebraMap (𝓞 L⁺) L⁺ m := ⟨_, rfl⟩
  have hp' : algebraMap (𝓞 L⁺) L⁺ (n₁ * d₂) = mK * T := by
    rw [map_mul, ← hd₁, hmK, hm_def, map_mul]; ring
  have hq' : algebraMap (𝓞 L⁺) L⁺ (n₂ * d₁ ^ 2 * d₂) = mK ^ 2 * N := by
    rw [map_mul, map_mul, map_pow, ← hd₂, hmK, hm_def, map_mul]; ring
  have hp : algebraMap (𝓞 L⁺) L (n₁ * d₂) = algebraMap L⁺ L mK * (x + cc x) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 L⁺) L⁺ L, hp', map_mul, hTL]
  have hq : algebraMap (𝓞 L⁺) L (n₂ * d₁ ^ 2 * d₂) = (algebraMap L⁺ L mK) ^ 2 * (x * cc x) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 L⁺) L⁺ L, hq', map_mul, map_pow, hNL]
  obtain ⟨y, hy_def⟩ : ∃ y : L, y = algebraMap L⁺ L mK * x := ⟨_, rfl⟩
  have hyA : IsIntegral (𝓞 L⁺) y := by
    refine ⟨X ^ 2 - C (n₁ * (d₂ : 𝓞 L⁺)) * X + C (n₂ * (d₁ : 𝓞 L⁺) ^ 2 * d₂), by monicity!, ?_⟩
    rw [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_X_pow, hp, hq, hy_def]
    ring
  have hy : IsIntegral ℤ y := isIntegral_trans y hyA
  have hvm : Valued.v (algebraMap L⁺ (s.v.adicCompletion L⁺) mK) = 1 := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap s.v, hmK]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem s.v).mpr hm
  refine ⟨⟨y, hy⟩, ?_, ?_⟩
  · show Valued.v (s.i y) = 1
    rw [hy_def, map_mul, s.i.commutes, Valuation.map_mul, hvm, hx1, one_mul]
  · show Valued.v (s.i (cc y)) < 1
    rw [hy_def, map_mul, AlgEquiv.commutes, map_mul, s.i.commutes, Valuation.map_mul, hvm, one_mul]
    exact hcx1

end GlobalTheory.SplitSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousOfValuationEq
open IsDedekindDomain Topology

namespace GlobalTheory.ValuationExtensionContinuous

theorem continuous_of_valuation_eq {A B Γ : Type} [Ring A] [Ring B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ]
    (hs : Function.Surjective (Valued.v : A → Γ)) (g : A →+* B)
    (hg : ∀ a, Valued.v (g a) = (Valued.v a : Γ)) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A Γ).tendsto_iff
    (Valued.hasBasis_nhds_zero B Γ)]
  intro γ _
  obtain ⟨k, hk⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hk0 : (Valued.v k : Γ) ≠ 0 := by
    rw [hk]
    exact (map_ne_zero _).mpr γ.ne_zero
  have hk1 : (Valued.v : Valuation A Γ).restrict k ≠ 0 := by simpa using hk0
  refine ⟨Units.mk0 _ hk1, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, hg, ← hk]
  exact hx

theorem exists_extension {K : Type} [Field K] [NumberField K] {R L : Type} [CommRing R]
    [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers K)) (u : HeightOneSpectrum R)
    (f : K →+* u.adicCompletion L)
    (hf : ∀ x : K, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K (w.adicCompletion K) x) = f x) ∧
      ∀ y : w.adicCompletion K, Valued.v (φ y) = Valued.v y := by
  let g : WithVal (w.valuation K) →+* u.adicCompletion L :=
    f.comp (WithVal.equiv (w.valuation K)).toRingHom
  have hg : Continuous g := by
    refine continuous_of_valuation_eq (fun c => ?_) g (fun a => hf _)
    obtain ⟨k, hk⟩ := w.valuation_surjective K c
    exact ⟨WithVal.toVal _ k, hk⟩
  let ψ := UniformSpace.Completion.extensionHom g hg
  let φ : w.adicCompletion K →+* u.adicCompletion L :=
    ψ.comp (HeightOneSpectrum.adicCompletion.equiv K w).toRingHom
  have hψ : Continuous ψ := UniformSpace.Completion.continuous_extension
  have hφ : Continuous φ :=
    hψ.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w)
  have hφa : ∀ a : WithVal (w.valuation K),
      φ (HeightOneSpectrum.adicCompletion.ofCompletion (a : (w.valuation K).Completion))
        = f a.ofVal := fun a => UniformSpace.Completion.extensionHom_coe g hg a
  refine ⟨φ, hφ, fun x => hφa (WithVal.toVal _ x), fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero, map_zero]
  have h1 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  have h2 : (Valued.v (φ y) : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  have hU := Filter.inter_mem (Valued.locally_const h1)
    (hφ.continuousAt.preimage_mem_nhds (Valued.locally_const h2))
  have hV := (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).continuousAt
    (x := y.toCompletion) |>.preimage_mem_nhds hU
  obtain ⟨a, ha1, ha2⟩ := UniformSpace.Completion.denseRange_coe.mem_nhds hV
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at ha1 ha2
  rw [← ha1, ← ha2, hφa, hf]
  exact (HeightOneSpectrum.adicCompletion.valued_coe K w a.ofVal).symm

end GlobalTheory.ValuationExtensionContinuous
end

open NumberField IsDedekindDomain

open WithZero

namespace GlobalTheory.DenseCompl

section DVR

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]

noncomputable def closedPoint (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] :
    HeightOneSpectrum W :=
  ⟨IsLocalRing.maximalIdeal W, inferInstance, IsDiscreteValuationRing.not_a_field W⟩

theorem asIdeal_eq_span {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) :
    v.asIdeal = Ideal.span {π} := by
  rw [← hπ.maximalIdeal_eq]
  exact IsLocalRing.eq_maximalIdeal v.isMaximal

theorem valuation_uniformiser {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) :
    v.valuation Qq (algebraMap W Qq π) = exp (-1) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_singleton hπ.ne_zero (asIdeal_eq_span hπ v)

theorem exists_eq_pow_mul_iff {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) (q : Qq) (n : ℕ) :
    (∃ w : W, q = algebraMap W Qq (π ^ n * w)) ↔ v.valuation Qq q ≤ exp (-(n : ℤ)) := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      asIdeal_eq_span hπ v, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  · intro h
    have hπ0 : algebraMap W Qq π ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W Qq)]
      exact hπ.ne_zero
    obtain ⟨w, hw⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one Qq
      (q / algebraMap W Qq π ^ n) fun v' => by
        have hv : v' = v :=
          HeightOneSpectrum.ext ((asIdeal_eq_span hπ v').trans (asIdeal_eq_span hπ v).symm)
        subst hv
        rw [map_div₀, map_pow, valuation_uniformiser hπ v', ← WithZero.exp_nsmul, smul_neg, nsmul_one,
          div_le_iff₀ exp_pos, one_mul]
        exact h
    refine ⟨w, ?_⟩
    rw [map_mul, map_pow, hw, mul_div_cancel₀ _ (pow_ne_zero _ hπ0)]

end DVR

theorem le_of_forall_le_exp {a b : ℤᵐ⁰} (hb : b ≤ 1)
    (h : ∀ n : ℕ, b ≤ exp (-(n : ℤ)) → a ≤ exp (-(n : ℤ))) : a ≤ b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · by_contra ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha le_rfl
    obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt ha0
    exact absurd (h n zero_le') (not_le.2 hn)
  · have hl : log b ≤ 0 := by
      rw [← exp_le_exp, exp_log hb0, exp_zero]
      exact hb
    have hn : (((-log b).toNat : ℕ) : ℤ) = -log b := Int.toNat_of_nonneg (by omega)
    have he : exp (-(((-log b).toNat : ℕ) : ℤ)) = b := by
      rw [hn, neg_neg, exp_log hb0]
    exact (h _ he.ge).trans he.le

theorem eq_zero_of_forall_le_exp {a : ℤᵐ⁰} (h : ∀ n : ℕ, a ≤ exp (-(n : ℤ))) : a = 0 :=
  le_antisymm (le_of_forall_le_exp zero_le' fun n _ => h n) zero_le'

theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx


open scoped WithZeroTopology in
theorem exists_extension {K : Type} [Field K] [NumberField K] {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum R) (f : K →+* u.adicCompletion L)
    (hf : ∀ x, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K _ x) = f x) ∧ ∀ y, Valued.v (φ y) = Valued.v y := by
  first
  | exact @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension
  | exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension
  | (apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension ..)

end GlobalTheory.DenseCompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et

namespace GlobalTheory.Et.H0

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem sh : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (coefPre R) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)]
  have h : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} R) :=
    .of_le Scheme.proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf R)
  have h2 : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} R ⋙ uliftFunctor.{1}) := by
    rw [isSheaf_iff_isSheaf_of_type] at h ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor _) h
  exact h2

def yonedaAdd (X : Scheme.{0}) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    (uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R) ⟶ P) ≃+ P.obj (op X) where
  toEquiv := (((ModuleCat.adj (ULift.{1} R)).whiskerRight Scheme.{0}ᵒᵖ).homEquiv (uliftYoneda.{1}.obj X) P).trans
    uliftYonedaEquiv
  map_add' _ _ := rfl

def eAdd (X : Scheme.{0}) : H R 0 X ≃+ C(X, R) :=
  (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R)).trans <|
  ((sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homAddEquiv _ (coef R)).trans <|
  (yonedaAdd R X (coef R).obj).trans <|
  ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv).toAddEquiv.trans AddEquiv.ulift)

theorem eAdd_smul (X : Scheme.{0}) (r : R) (x : H R 0 X) : eAdd R X (r • x) = r • eAdd R X x := by
  have h1 : Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (r • x) =
      ULift.up r • Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x :=
    (Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (freeOn R).obj X) (Y := coef R)).map_smul (ULift.up r) x
  change AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (r • x))))) =
    r • AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x))))
  rw [h1]
  have h2 : yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
      (ULift.up r • Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x)) =
      ULift.up r • yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x)) := rfl
  rw [h2]
  exact (congrArg AddEquiv.ulift (LinearEquiv.map_smul (((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv) (ULift.up r) _)).trans rfl

def e (X : Scheme.{0}) : H R 0 X ≃ₗ[R] C(X, R) :=
  { eAdd R X with map_smul' := eAdd_smul R X }

end GlobalTheory.Et.H0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqFixedUnitHenselian
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqFixedUnitHenselian
open Polynomial

namespace GlobalTheory.HenselianNorm

theorem exists_mem_add_mul_sq_eq {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
    (n : R) {e : R} (he : e ∈ I) : ∃ t ∈ I, t + n * t ^ 2 = e := by
  obtain ⟨s, hs, hsI⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 + X - C (n * e))
    (by monicity!) 0
    (by
      simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C]
      simpa using I.mul_mem_left n he)
    (by simp)
  have h0 : eval s (X ^ 2 + X - C (n * e)) = 0 := hs
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h0
  rw [sub_zero] at hsI
  obtain ⟨U, hU⟩ := (Ring.mem_jacobson_iff.mp (HenselianRing.jac hsI)) 1
  have hinv : (s + 1) * (↑U⁻¹ : R) = 1 := by
    rw [show s + 1 = (U : R) by rw [hU]; ring]
    exact U.mul_inv
  have hnt : n * (e * ↑U⁻¹) = s := by
    linear_combination (-(↑U⁻¹ : R)) * h0 + s * hinv
  refine ⟨e * ↑U⁻¹, I.mul_mem_right _ he, ?_⟩
  linear_combination (e * ↑U⁻¹) * hnt + e * hinv

theorem exists_norm_eq_one_add {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
    (c : R →+* R) (hc : ∀ x, c (c x) = x) (hI : ∀ x ∈ I, c x ∈ I) {w : R} (hw : w + c w = 1)
    {e : R} (he : e ∈ I) (hce : c e = e) : ∃ x, x * c x = 1 + e := by
  obtain ⟨t, htI, ht⟩ := exists_mem_add_mul_sq_eq I (w * c w) he
  have hct : c t = t := by
    have h1 : c t + w * c w * c t ^ 2 = e := by
      have h := congrArg c ht
      simp only [map_add (f := _), map_mul, map_pow, hc, hce] at h
      linear_combination h
    have hm : w * c w * (t + c t) ∈ I := I.mul_mem_left _ (I.add_mem htI (hI t htI))
    obtain ⟨U, hU⟩ := (Ring.mem_jacobson_iff.mp (HenselianRing.jac hm)) 1
    have hz : (t - c t) * (U : R) = 0 := by
      rw [hU]
      linear_combination ht - h1
    have h2 := (U.isUnit.mul_left_eq_zero).mp hz
    linear_combination -h2
  refine ⟨1 + w * t, ?_⟩
  rw [map_add (f := _), map_one, map_mul, hct]
  linear_combination ht + t * hw

theorem exists_norm_eq : ∀ (R : Type) [CommRing R] (I : Ideal R) [HenselianRing R I]
    [Finite (R ⧸ I)] (c : R →+* R), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) →
    (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  intro R _ I _ _ c hc hI hω u hcu hu
  obtain ⟨ω, D, hD⟩ := hω
  have hcD : (c ω - ω) * c ↑D⁻¹ = 1 := by
    have h := congrArg c D.mul_inv
    rw [map_mul, map_one, hD, map_sub, hc] at h
    exact h
  have hw : ω * ↑D⁻¹ + c (ω * ↑D⁻¹) = 1 := by
    have hinv : (↑D⁻¹ : R) * (ω - c ω) = 1 := by rw [← hD]; exact D.inv_mul
    rw [map_mul]
    linear_combination (1 - ω * ↑D⁻¹) * hcD - ω * c ↑D⁻¹ * hinv
  have hI' : I ≤ I.comap c := fun x hx => hI x hx
  let cb : R ⧸ I →+* R ⧸ I := Ideal.quotientMap I c hI'
  have hmk : ∀ x, cb (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (c x) :=
    fun x => Ideal.quotientMap_mk
  have hcb : ∀ x, cb (cb x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hmk, hmk, hc]
  have hunit : IsUnit (Ideal.Quotient.mk I ω - cb (Ideal.Quotient.mk I ω)) := by
    rw [hmk, ← map_sub, ← hD]
    exact D.isUnit.map _
  obtain ⟨xb, hxb⟩ := GlobalTheory.T.finite_involution_fixed_unit_eq_mul_conj (R ⧸ I) cb hcb ⟨_, hunit⟩ (Ideal.Quotient.mk I u)
    (by rw [hmk, hcu]) (hu.map _)
  obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective xb
  rw [hmk, ← map_mul] at hxb
  have hmem : x₀ * c x₀ - u ∈ I := Ideal.Quotient.eq.mp hxb
  obtain ⟨U, rfl⟩ := hu
  have hcU : c ↑U⁻¹ = ↑U⁻¹ := by
    have h : (U : R) * c ↑U⁻¹ = 1 := by
      rw [← hcu, ← map_mul, U.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h).symm
  obtain ⟨a, ha⟩ : ∃ a, a = (x₀ * c x₀ - ↑U) * ↑U⁻¹ := ⟨_, rfl⟩
  have haI : a ∈ I := ha ▸ I.mul_mem_right _ hmem
  have hca : c a = a := by
    rw [ha]
    simp only [map_mul, map_sub, hc, hcu, hcU]
    ring
  obtain ⟨V, hV⟩ := (Ring.mem_jacobson_iff.mp (HenselianRing.jac haI)) 1
  have hcV : c ↑V = ↑V := by rw [hV, map_add (f := _), map_mul, map_one, hca]
  have hcVi : c ↑V⁻¹ = ↑V⁻¹ := by
    have h : (V : R) * c ↑V⁻¹ = 1 := by
      rw [← hcV, ← map_mul, V.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h).symm
  have heI : (↑V⁻¹ : R) - 1 ∈ I := by
    have h : (↑V⁻¹ : R) - 1 = -(↑V⁻¹ * a) := by
      linear_combination (-(↑V⁻¹ : R)) * hV + V.inv_mul
    rw [h]
    exact I.neg_mem (I.mul_mem_left _ haI)
  obtain ⟨y, hy⟩ := exists_norm_eq_one_add I c hc hI hw heI (by rw [map_sub, hcVi, map_one])
  have hvU : x₀ * c x₀ = ↑U * ↑V := by
    rw [hV, ha]
    linear_combination (-(x₀ * c x₀ - ↑U)) * U.mul_inv
  refine ⟨x₀ * y, ?_⟩
  rw [map_mul]
  linear_combination (x₀ * c x₀) * hy + (↑V⁻¹ : R) * hvU + (↑U : R) * V.mul_inv

end GlobalTheory.HenselianNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqFixedUnitHenselianStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_eq_fixed_unit_henselian : ∀ (R : Type) [CommRing R] (I : Ideal R) [HenselianRing R I] [Finite (R ⧸ I)] (c : R →+* R), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  first | exact @GlobalTheory.HenselianNorm.exists_norm_eq | exact GlobalTheory.HenselianNorm.exists_norm_eq | (intros; apply GlobalTheory.HenselianNorm.exists_norm_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleTensorProductLeft
open CategoryTheory

namespace GlobalTheory

theorem isIndEtale_tensorProduct_left (C A M : Type) [CommRing C] [CommRing A] [CommRing M]
    [Algebra C A] [Algebra C M] (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap C A)) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap M (TensorProduct C M A)) := by
  haveI : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := MorphismProperty.ind.{0}
    (RingHom.toMorphismProperty @RingHom.Etale))
    (CommRingCat.isPushout_tensorProduct C M A) h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FaceFaceApply
set_option autoImplicit false

open CategoryTheory

universe v u

namespace GlobalTheory.CatH.DSq

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{0} R)

theorem sign_swap {q : ℕ} (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (-1 : ℤ) ^ (i.succAbove k : ℕ) * (-1) ^ (k.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (k : ℕ)) := by
  have h : (i.succAbove k : ℕ) + (k.predAbove i : ℕ) + 1 = (i : ℕ) + (k : ℕ) ∨
      (i.succAbove k : ℕ) + (k.predAbove i : ℕ) = (i : ℕ) + (k : ℕ) + 1 := by
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val, Fin.val_pred,
      Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
    split_ifs <;> omega
  rw [← pow_add, ← pow_add]
  rcases h with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

end GlobalTheory.CatH.DSq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeakApproxUnitFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeakApproxUnitFinitePlace
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalTheory.HkFin

theorem exists_weak_approx_unit (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℕ) :
    ∃ y : E, y ≠ 0 ∧ Valued.v ((y : w.adicCompletion E) * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1)
      ≤ WithZero.exp (-(n : ℤ)) ∧ ∀ v ∈ S, v ≠ w → v.valuation E (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  obtain ⟨a, ha0, ha, -⟩ := PI.FinOrdValD.WA.weakApprox (insert w S)
    (Function.update (fun v => (1 : v.adicCompletion E)) w (x : w.adicCompletion E))
    (Function.update (fun _ => exp (-(n : ℤ))) w (Valued.v (x : w.adicCompletion E) * exp (-(n : ℤ))))
    (fun v _ => by
      by_cases h : v = w
      · subst h; simp only [Function.update_self]
        exact mul_ne_zero ((Valuation.ne_zero_iff _).mpr x.ne_zero) exp_ne_zero
      · simp only [Function.update_of_ne h]; exact exp_ne_zero)
  refine ⟨a, ha0, ?_, fun v hv hvw => ?_⟩
  · have h := ha w (Finset.mem_insert_self w S)
    simp only [Function.update_self] at h
    have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    have e1 : (a : w.adicCompletion E) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) - 1 =
        (algebraMap E (w.adicCompletion E) a - x) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) := by
      rw [sub_mul, Units.mul_inv]; rfl
    rw [e1, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [mul_comm] at h
    exact (mul_inv_lt_of_lt_mul₀ h).le
  · have h := ha v (Finset.mem_insert_of_mem hv)
    simp only [Function.update_of_ne hvw] at h
    rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h.le

end GlobalTheory.HkFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeakApproxUnitFinitePlaceStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weak_approx_unit_finite_place : ∀ (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℕ), ∃ y : E, y ≠ 0 ∧ Valued.v ((y : w.adicCompletion E) * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ ∀ v ∈ S, v ≠ w → v.valuation E (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.HkFin.exists_weak_approx_unit | exact GlobalTheory.HkFin.exists_weak_approx_unit | (intros; apply GlobalTheory.HkFin.exists_weak_approx_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfIsLocalization
open CategoryTheory Limits

noncomputable section

namespace GlobalTheory.IndEtaleLoc

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) {S : Type} [CommRing S]
  (s : D ⟶ (Functor.const J).obj (CommRingCat.of S)) (M : Submonoid S)

structure Idx where

  j : J

  e : D.obj j
  mem : (s.app j).hom e ∈ M

variable {D s M}

theorem app_map_apply {j k : J} (φ : j ⟶ k) (x : D.obj j) :
    (s.app k).hom ((D.map φ).hom x) = (s.app j).hom x := by
  have h := congr(($(s.naturality φ)).hom x)
  simpa using h

instance : SmallCategory (Idx D s M) where
  Hom a b := {φ : a.j ⟶ b.j // ∃ c : D.obj b.j, (D.map φ).hom a.e * c = b.e}
  id a := ⟨𝟙 a.j, 1, by simp⟩
  comp φ ψ := ⟨φ.1 ≫ ψ.1, by
    obtain ⟨c, hc⟩ := φ.2
    obtain ⟨d, hd⟩ := ψ.2
    exact ⟨(D.map ψ.1).hom c * d, by
      rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, ← mul_assoc, ← map_mul, hc,
        hd]⟩⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

theorem isUnit_map {a b : Idx D s M} (φ : a ⟶ b) :
    IsUnit (algebraMap (D.obj b.j) (Localization.Away b.e) ((D.map φ.1).hom a.e)) := by
  obtain ⟨c, hc⟩ := φ.2
  refine isUnit_of_mul_isUnit_left (y := algebraMap _ (Localization.Away b.e) c) ?_
  rw [← map_mul, hc]
  exact IsLocalization.Away.algebraMap_isUnit b.e

def locMap {a b : Idx D s M} (φ : a ⟶ b) : Localization.Away a.e →+* Localization.Away b.e :=
  IsLocalization.Away.lift a.e (g := (algebraMap _ (Localization.Away b.e)).comp (D.map φ.1).hom)
    (isUnit_map φ)

@[simp] theorem locMap_algebraMap {a b : Idx D s M} (φ : a ⟶ b) (x : D.obj a.j) :
    locMap φ (algebraMap _ _ x) = algebraMap _ (Localization.Away b.e) ((D.map φ.1).hom x) := by
  simp [locMap, IsLocalization.Away.lift]

variable (D s M)

def diag : Idx D s M ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away a.e)
  map φ := CommRingCat.ofHom (locMap φ)
  map_id a := by
    ext : 1
    refine IsLocalization.ringHom_ext (Submonoid.powers a.e) (RingHom.ext fun x => ?_)
    simp [show (𝟙 a : a ⟶ a).1 = 𝟙 a.j from rfl]
  map_comp {a b c} φ ψ := by
    ext : 1
    refine IsLocalization.ringHom_ext (Submonoid.powers a.e) (RingHom.ext fun x => ?_)
    simp [show (φ ≫ ψ).1 = φ.1 ≫ ψ.1 from rfl]

end GlobalTheory.IndEtaleLoc

namespace GlobalTheory.IndEtaleLoc

variable {J : Type} [SmallCategory J] {D : J ⥤ CommRingCat.{0}} {S : Type} [CommRing S]
  {s : D ⟶ (Functor.const J).obj (CommRingCat.of S)} {M : Submonoid S}

instance [IsFiltered J] : IsFiltered (Idx D s M) := by
  haveI : Nonempty (Idx D s M) := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    exact ⟨⟨j, 1, by simpa using M.one_mem⟩⟩
  refine { cocone_objs := fun a b => ?_, cocone_maps := fun a b φ ψ => ?_ }
  · let u := IsFiltered.leftToMax a.j b.j
    let v := IsFiltered.rightToMax a.j b.j
    refine ⟨⟨IsFiltered.max a.j b.j, (D.map u).hom a.e * (D.map v).hom b.e, ?_⟩,
      ⟨u, (D.map v).hom b.e, rfl⟩, ⟨v, (D.map u).hom a.e, mul_comm _ _⟩, trivial⟩
    rw [map_mul, app_map_apply, app_map_apply]
    exact M.mul_mem a.mem b.mem
  · let h := IsFiltered.coeqHom φ.1 ψ.1
    refine ⟨⟨IsFiltered.coeq φ.1 ψ.1, (D.map h).hom b.e, by rw [app_map_apply]; exact b.mem⟩,
      ⟨h, 1, mul_one _⟩, Subtype.ext ?_⟩
    change φ.1 ≫ h = ψ.1 ≫ h
    exact IsFiltered.coeq_condition φ.1 ψ.1

end GlobalTheory.IndEtaleLoc

namespace GlobalTheory.IndEtaleLoc

variable {J : Type} [SmallCategory J] {D : J ⥤ CommRingCat.{0}} {S : Type} [CommRing S]
  {s : D ⟶ (Functor.const J).obj (CommRingCat.of S)} {M : Submonoid S}

def fromBase {R : Type} [CommRing R] (t : (Functor.const J).obj (CommRingCat.of R) ⟶ D) :
    (Functor.const (Idx D s M)).obj (CommRingCat.of R) ⟶ diag D s M where
  app a := CommRingCat.ofHom ((algebraMap (D.obj a.j) (Localization.Away a.e)).comp (t.app a.j).hom)
  naturality a b φ := by
    ext x
    have h := congr(($(t.naturality φ.1)).hom x)
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
      CommRingCat.hom_comp, RingHom.comp_apply] at h
    change algebraMap _ (Localization.Away b.e) ((t.app b.j).hom x) =
      locMap φ (algebraMap _ (Localization.Away a.e) ((t.app a.j).hom x))
    rw [locMap_algebraMap, h]

variable (S' : Type) [CommRing S'] [Algebra S S'] [IsLocalization M S']

def leg (a : Idx D s M) : Localization.Away a.e →+* S' :=
  IsLocalization.Away.lift a.e (g := (algebraMap S S').comp ((s.app a.j).hom : D.obj a.j →+* S))
    (IsLocalization.map_units S' (⟨(s.app a.j).hom a.e, a.mem⟩ : M))

@[simp] theorem leg_algebraMap (a : Idx D s M) (x : D.obj a.j) :
    leg S' a (algebraMap (D.obj a.j) (Localization.Away a.e) x) =
      algebraMap S S' (((s.app a.j).hom : D.obj a.j →+* S) x) := by
  simp [leg, IsLocalization.Away.lift]

def toLoc : diag D s M ⟶ (Functor.const (Idx D s M)).obj (CommRingCat.of S') where
  app a := CommRingCat.ofHom (leg S' a)
  naturality a b φ := by
    ext : 1
    change (leg S' b).comp (locMap φ) = (RingHom.id S').comp (leg S' a)
    rw [RingHom.id_comp]
    refine IsLocalization.ringHom_ext (Submonoid.powers a.e) (RingHom.ext fun x => ?_)
    change leg S' b (locMap φ (algebraMap _ (Localization.Away a.e) x)) =
      leg S' a (algebraMap _ (Localization.Away a.e) x)
    rw [locMap_algebraMap, leg_algebraMap, leg_algebraMap]
    exact congrArg _ (app_map_apply φ.1 x)

def isColimitToLoc [IsFiltered J] (hs : IsColimit (Cocone.mk _ s)) :
    IsColimit (Cocone.mk _ (toLoc (s := s) (M := M) S')) := by
  have hc := isColimitOfPreserves (forget CommRingCat.{0}) hs
  haveI : ReflectsColimit (diag D s M) (forget CommRingCat.{0}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{0}) ?_
  have hsurj : ∀ x : S', ∃ (a : Idx D s M) (z : Localization.Away a.e), x = leg S' a z := by
    intro x
    obtain ⟨⟨y, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    obtain ⟨j, y', hy'⟩ := Types.jointly_surjective_of_isColimit hc y
    obtain ⟨k, m', hm'⟩ := Types.jointly_surjective_of_isColimit hc (m : S)
    change (s.app j).hom y' = y at hy'
    change (s.app k).hom m' = (m : S) at hm'
    let u := IsFiltered.leftToMax j k
    let v := IsFiltered.rightToMax j k
    let a : Idx D s M :=
      ⟨IsFiltered.max j k, (D.map v).hom m', by rw [app_map_apply, hm']; exact m.2⟩
    let p : Submonoid.powers a.e := ⟨a.e, Submonoid.mem_powers _⟩
    refine ⟨a, IsLocalization.mk' (Localization.Away a.e) ((D.map u).hom y') p, ?_⟩
    change _ = leg S' a _
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    have h1 := congrArg (leg S' a) (IsLocalization.mk'_spec (Localization.Away a.e)
      ((D.map u).hom y') p)
    rw [map_mul, leg_algebraMap, leg_algebraMap] at h1
    have e1 : (s.app a.j).hom (p : D.obj a.j) = (m : S) := by
      change (s.app _).hom ((D.map v).hom m') = (m : S)
      rw [app_map_apply, hm']
    have e2 : (s.app a.j).hom ((D.map u).hom y') = (y : S) := by
      change (s.app _).hom ((D.map u).hom y') = (y : S)
      rw [app_map_apply, hy']
    rw [e1, e2] at h1
    exact h1.symm
  have hinj : ∀ (a : Idx D s M) (x y : Localization.Away a.e), leg S' a x = leg S' a y →
      ∃ (b : Idx D s M) (f : a ⟶ b), locMap f x = locMap f y := by
    intro a x y hxy
    suffices H : ∀ z, leg S' a z = 0 → ∃ (b : Idx D s M) (f : a ⟶ b), locMap f z = 0 by
      obtain ⟨b, f, hf⟩ := H (x - y) (by rw [map_sub, hxy, sub_self])
      refine ⟨b, f, ?_⟩
      rwa [map_sub, sub_eq_zero] at hf
    intro z hz
    obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a.e) z
    have hspec := IsLocalization.mk'_spec (Localization.Away a.e) c
      (⟨a.e ^ n, n, rfl⟩ : Submonoid.powers a.e)
    have hc0 : algebraMap S S' ((s.app a.j).hom c) = 0 := by
      have := congrArg (leg S' a) hspec
      rw [map_mul, hz, zero_mul, leg_algebraMap] at this
      exact this.symm
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M S' _).1 hc0
    obtain ⟨k, m', hm'⟩ := Types.jointly_surjective_of_isColimit hc (m : S)
    change (s.app k).hom m' = (m : S) at hm'
    let u := IsFiltered.leftToMax a.j k
    let v := IsFiltered.rightToMax a.j k
    have h0 : (s.app (IsFiltered.max a.j k)).hom ((D.map v).hom m' * (D.map u).hom c) =
        (s.app (IsFiltered.max a.j k)).hom 0 := by
      rw [map_mul, app_map_apply, app_map_apply, hm', map_zero, hm]
    obtain ⟨l, f1, hf1⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 h0
    have hf1' : (D.map f1).hom ((D.map v).hom m' * (D.map u).hom c) = (D.map f1).hom 0 := hf1
    rw [map_zero, map_mul] at hf1'
    let b : Idx D s M := ⟨l, (D.map (u ≫ f1)).hom a.e * (D.map (v ≫ f1)).hom m', by
      rw [map_mul, app_map_apply, app_map_apply, hm']; exact M.mul_mem a.mem m.2⟩
    let f : a ⟶ b := ⟨u ≫ f1, (D.map (v ≫ f1)).hom m', rfl⟩
    refine ⟨b, f, ?_⟩
    have hu : IsUnit (locMap f (algebraMap _ _ (a.e ^ n))) := by
      rw [locMap_algebraMap, map_pow, map_pow]
      exact (isUnit_map f).pow n
    have hzero : algebraMap (D.obj b.j) (Localization.Away b.e) ((D.map f.1).hom c) = 0 := by
      have hb : IsUnit (algebraMap (D.obj b.j) (Localization.Away b.e) b.e) :=
        IsLocalization.Away.algebraMap_isUnit b.e
      refine (hb.mul_right_eq_zero).1 ?_
      rw [← map_mul]
      have : b.e * (D.map f.1).hom c = (D.map (u ≫ f1)).hom a.e *
          ((D.map f1).hom ((D.map v).hom m') * (D.map f1).hom ((D.map u).hom c)) := by
        simp only [b, f, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]
        ring
      rw [this, hf1', mul_zero, map_zero]
    have := congrArg (locMap f) hspec
    rw [map_mul, locMap_algebraMap f c, hzero] at this
    exact (hu.mul_left_eq_zero).1 this
  exact Types.FilteredColimit.isColimitOf' _ _ (fun x => hsurj x) (fun a x y h => hinj a x y h)

end GlobalTheory.IndEtaleLoc

namespace GlobalTheory.IndEtaleLoc

theorem isIndEtale_of_isLocalization : ∀ (R S S' : Type) [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] (M : Submonoid S)
    [IsLocalization M S'], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R S) →
      GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R S') := by
  intro R S S' _ _ _ _ _ _ _ M _ h
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  refine ⟨Idx D s M, inferInstance, inferInstance, diag D s M, fromBase t, toLoc S',
    isColimitToLoc S' hs, fun a => ⟨?_, ?_⟩⟩
  · show RingHom.Etale ((algebraMap (D.obj a.j) (Localization.Away a.e)).comp (t.app a.j).hom)
    exact RingHom.Etale.stableUnderComposition _ _ (hst a.j).1
      (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway a.e))
  · ext x
    have h := congr(($((hst a.j).2)).hom x)
    change (s.app a.j).hom ((t.app a.j).hom x) = algebraMap R S x at h
    change leg S' a (algebraMap _ (Localization.Away a.e) ((t.app a.j).hom x)) = algebraMap R S' x
    rw [leg_algebraMap]
    change algebraMap S S' ((s.app a.j).hom ((t.app a.j).hom x)) = _
    rw [h, ← IsScalarTower.algebraMap_apply]

end GlobalTheory.IndEtaleLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntPolyEsymmEqPowerSumMultiset
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntPolyEsymmEqPowerSumMultiset
open GlobalTheory.Cong

namespace GlobalTheory.PowerSumPoly
open MvPolynomial

theorem exists_intPoly_psum_eq : ∀ a n : ℕ, 1 ≤ n → ∃ P : MvPolynomial (Fin (a + 1)) ℤ, ∀ s : Multiset ℂ,
    Multiset.card s = a → MvPolynomial.aeval (fun j : Fin (a + 1) => s.esymm j) P = (s.map (· ^ n)).sum := by
  intro a n _
  obtain ⟨Q, hQ⟩ := esymmAlgHom_surjective ℤ (σ := Fin a) (n := a) (by simp)
    ⟨psum (Fin a) ℤ n, psum_isSymmetric (Fin a) ℤ n⟩
  have hQ' : aeval (fun i : Fin a => esymm (Fin a) ℤ (i + 1)) Q = psum (Fin a) ℤ n := by
    rw [← esymmAlgHom_apply, hQ]
  refine ⟨rename Fin.succ Q, fun s hs => ?_⟩
  set f : Fin a → ℂ := fun i => s.toList[(i : ℕ)]'(by simp [hs]) with hf
  have hsf : (Finset.univ.val.map f) = s := by
    rw [Fin.univ_val_map]
    conv_rhs => rw [← Multiset.coe_toList s]
    congr 1
    apply List.ext_getElem (by simp [hs])
    intro i h1 h2
    simp [f]
  have key : aeval f (aeval (fun i : Fin a => esymm (Fin a) ℤ (i + 1)) Q) =
      aeval (fun i : Fin a => aeval f (esymm (Fin a) ℤ (i + 1))) Q := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rw [hQ'] at key
  rw [aeval_rename]
  have lhs : (fun j : Fin (a + 1) => s.esymm j) ∘ Fin.succ = fun i : Fin a => aeval f (esymm (Fin a) ℤ (i + 1)) := by
    funext i
    simp [aeval_esymm_eq_multiset_esymm, hsf]
  rw [lhs, ← key]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [psum, map_sum]
  simp only [map_pow, aeval_X]
  conv_rhs => rw [← hsf]
  simp [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

end GlobalTheory.PowerSumPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntPolyEsymmEqPowerSumMultisetStatement
open GlobalTheory.Cong
theorem _root_.GlobalTheory.T.exists_intPoly_esymm_eq_powerSum_multiset : ∀ a n : ℕ, 1 ≤ n → ∃ P : MvPolynomial (Fin (a + 1)) ℤ, ∀ s : Multiset ℂ, Multiset.card s = a → MvPolynomial.aeval (fun j : Fin (a + 1) => s.esymm j) P = (s.map (· ^ n)).sum := by
  first | exact @GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq | exact GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq | (intros; apply GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq <;> assumption)
end
end
