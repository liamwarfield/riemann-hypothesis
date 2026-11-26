module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentInFibreIffOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdeleEquivOfLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenMapTmulEq
open scoped TensorProduct

namespace GlobalTheory.CentralizerMapTensor

theorem cenMap_tmul_eq (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (x : ℚ_[ℓ]) (f : F) :
    GlobalTheory.LKInvGood.cenMap ℓ F B (x ⊗ₜ[ℚ] f) = x ⊗ₜ[ℚ] algebraMap F B f := rfl

theorem commute_cenMap (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (a : ℚ_[ℓ] ⊗[ℚ] F) (y : ℚ_[ℓ] ⊗[ℚ] B) :
    Commute (GlobalTheory.LKInvGood.cenMap ℓ F B a) y := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Commute.zero_left _
  | add a₁ a₂ h₁ h₂ => rw [map_add (f := _)]; exact h₁.add_left h₂
  | tmul x f =>
    rw [cenMap_tmul_eq]
    induction y using TensorProduct.induction_on with
    | zero => exact Commute.zero_right _
    | add y₁ y₂ h₁ h₂ => exact h₁.add_right h₂
    | tmul z b =>
      unfold Commute SemiconjBy
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_comm x z, Algebra.commutes f b]

end GlobalTheory.CentralizerMapTensor
end

noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

variable (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B]
  [Algebra ℚ B] [IsScalarTower ℚ F B]

theorem cenMap_tmul (q : ℚ_[ℓ]) (f : F) : cenMap ℓ F B (q ⊗ₜ f) = q ⊗ₜ algebraMap F B f := by
  simp [cenMap]

theorem cenMap_mem (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ)
    {a : ℚ_[ℓ] ⊗[ℚ] F} (ha : a ∈ cenOrder ℓ F) : cenMap ℓ F B a ∈ locOrder ℓ Λ := by
  have h : cenOrder ℓ F ≤ (locOrder ℓ Λ).comap ((cenMap ℓ F B).restrictScalars ℤ_[ℓ]) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨a, rfl⟩
    show cenMap ℓ F B _ ∈ locOrder ℓ Λ
    rw [cenMap_tmul]
    exact Algebra.subset_adjoin ⟨_, hΛ a, rfl⟩
  exact h ha

theorem cenMap_commute (a : ℚ_[ℓ] ⊗[ℚ] F) (y : ℚ_[ℓ] ⊗[ℚ] B) : Commute (cenMap ℓ F B a) y := by
  first
  | exact @_root_.GlobalTheory.CentralizerMapTensor.commute_cenMap
  | exact _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap
  | (apply _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> assumption)
  | (intros; apply _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap ..)

def cenIncl (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    cenOrder ℓ F →ₐ[ℤ_[ℓ]] locOrder ℓ Λ :=
  (((cenMap ℓ F B).restrictScalars ℤ_[ℓ]).comp (cenOrder ℓ F).val).codRestrict (locOrder ℓ Λ)
    (fun a => cenMap_mem ℓ F B Λ hΛ a.2)

theorem coe_cenIncl (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) (a : cenOrder ℓ F) :
    (cenIncl ℓ F B Λ hΛ a : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B a := rfl

def cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    Algebra (cenOrder ℓ F) (locOrder ℓ Λ) :=
  (cenIncl ℓ F B Λ hΛ).toRingHom.toAlgebra' fun a x => Subtype.ext (cenMap_commute ℓ F B a x)

theorem algebraMap_cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) (a : cenOrder ℓ F) :
    letI := cenAlgebra ℓ F B Λ hΛ
    algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a = cenIncl ℓ F B Λ hΛ a := rfl

theorem isScalarTower_cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    letI := cenAlgebra ℓ F B Λ hΛ
    IsScalarTower ℤ_[ℓ] (cenOrder ℓ F) (locOrder ℓ Λ) := by
  letI := cenAlgebra ℓ F B Λ hΛ
  exact IsScalarTower.of_algebraMap_eq fun r => ((cenIncl ℓ F B Λ hΛ).commutes r).symm

end GlobalTheory.LocMatrix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFromPadicNormBound
open NumberField Polynomial

namespace GlobalTheory

def unitBallSubring (A : Type) [NormedField A] [IsUltrametricDist A] : Subring A :=
  GlobalTheory.ClosedBallValuationSubring.closedBallSubring A

theorem den_eq_one_of_padicNorm_le_one (c : ℚ)
    (h : ∀ q : ℕ, q.Prime → padicNorm q c ≤ 1) : c.den = 1 := by
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact q.Prime := ⟨hq⟩
  have hc : c ≠ 0 := by
    rintro rfl; simp at hne
  have h1 := h q hq
  rw [padicNorm.eq_zpow_of_ne_zero hc] at h1
  have hv : 0 ≤ padicValRat q c := by
    by_contra hlt
    push Not at hlt
    have hq1 : (1 : ℚ) < q := by exact_mod_cast hq.one_lt
    have : (1 : ℚ) < (q : ℚ) ^ (-padicValRat q c) := one_lt_zpow₀ hq1 (by omega)
    linarith
  have hden : 1 ≤ multiplicity q c.den :=
    one_le_multiplicity_of_dvd c.den_nz hqd
  have hnum : padicValInt q c.num = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hdvd
    have hcop := c.reduced
    have : q ∣ Nat.gcd c.num.natAbs c.den :=
      Nat.dvd_gcd (Int.natCast_dvd.mp hdvd) hqd
    rw [hcop] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  unfold padicValRat at hv
  omega

theorem isIntegral_of_forall_padicAlgCl_norm_le_one :
    ∀ (M : Type) [Field M] [NumberField M] (a : M),
      (∀ (q : ℕ) [Fact q.Prime] (τ : M →+* PadicAlgCl q), ‖τ a‖ ≤ 1) → IsIntegral ℤ a := by
  intro M _ _ a h
  set f := minpoly ℚ a with hf
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hmon : f.Monic := minpoly.monic hint
  have hcoeff : ∀ q : ℕ, q.Prime → ∀ n, padicNorm q (f.coeff n) ≤ 1 := by
    intro q hq n
    have : Fact q.Prime := ⟨hq⟩
    let S := unitBallSubring (PadicAlgCl q)
    set g := f.map (algebraMap ℚ (PadicAlgCl q)) with hg
    have hroots : ∀ b ∈ g.roots, b ∈ S := by
      intro b hb
      have hb' : b ∈ f.rootSet (PadicAlgCl q) := by
        rw [Polynomial.mem_rootSet]
        obtain ⟨hne, hr⟩ := (mem_roots'.mp hb)
        refine ⟨fun h0 => hne (by rw [hg, h0, Polynomial.map_zero]), ?_⟩
        rw [← eval_map_algebraMap]; exact hr
      rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly] at hb'
      obtain ⟨τ, rfl⟩ := hb'
      exact h q τ
    have hcard : Multiset.card g.roots = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
    have hgmon : g.Monic := hmon.map _
    have hgc : g.coeff n ∈ S := by
      by_cases hn : n ≤ g.natDegree
      · rw [coeff_eq_esymm_roots_of_card hcard hn, hgmon.leadingCoeff, one_mul]
        refine S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) ?_
        unfold Multiset.esymm
        refine S.multiset_sum_mem _ fun x hx => ?_
        obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
        refine S.multiset_prod_mem _ fun y hy => hroots y ?_
        exact Multiset.mem_of_le (Multiset.mem_powersetCard.mp hs).1 hy
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact S.zero_mem
    have h1 : ‖algebraMap ℚ (PadicAlgCl q) (f.coeff n)‖ ≤ 1 := by
      rw [← coeff_map]; exact hgc
    have e : algebraMap ℚ (PadicAlgCl q) (f.coeff n) =
        ((f.coeff n : ℚ_[q]) : PadicAlgCl q) := by simp
    rw [e, PadicAlgCl.norm_extends, Padic.eq_padicNorm] at h1
    exact_mod_cast h1
  have hlift : f ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨(f.coeff n).num, ?_⟩
    have := den_eq_one_of_padicNorm_le_one _ (fun q hq => hcoeff q hq n)
    simpa using Rat.intCast_num_of_den_eq_one this
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨g, hgm, ?_⟩
  have h0 : aeval a f = 0 := minpoly.aeval ℚ a
  rw [← hg, ← algebraMap_int_eq, aeval_map_algebraMap] at h0
  exact h0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormLinearPhaseSecondOrderLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormLinearPhaseSecondOrderLe
open scoped SchwartzMap

namespace GlobalTheory.LinearPhase

open Complex GlobalTheory.CharFormDeriv

theorem seminorm_phase_sub_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by
  intro V _ _ L c f k n
  set L' : V →L[ℝ] ℝ := (-(2 * Real.pi)) • L with hL'
  have hL'x : ∀ x, ((L' x : ℝ) : ℂ) = -(2 * Real.pi) * (L x : ℂ) := fun x => by
    simp [hL']
  set K := 3 * 2 ^ n * (1 + ‖L'‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)
      with hK
  have hgt : Function.HasTemperateGrowth (fun x : V => ((L x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp L).hasTemperateGrowth
  set g : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f with hgdef
  have hg : ∀ x, g x = (L x : ℂ) * f x := fun x => by
    rw [hgdef, SchwartzMap.smulLeftCLM_apply_apply hgt, smul_eq_mul]
  refine ⟨K + 2 * |2 * Real.pi * c| *
    (SchwartzMap.seminorm ℂ k n f + 2 * Real.pi * SchwartzMap.seminorm ℂ k n g), fun t ht1 => ?_⟩
  set a : ℂ := Complex.exp (((-(2 * Real.pi * c * t ^ 2) : ℝ) : ℂ) * I) with ha
  have hfun : (fun x : V => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
      = fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ)) := by
    funext x
    rw [ha, ← Complex.exp_add, hL'x]
    congr 1
    push_cast
    ring
  have het : Function.HasTemperateGrowth fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ)) :=
    (Function.HasTemperateGrowth.const a).mul (hasTemperateGrowth_char L' t)
  rw [hfun]
  set A : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : V => Complex.exp ((I * t) * (L' x : ℂ))) f with hAdef
  have hA : ∀ x, A x = Complex.exp ((I * t) * (L' x : ℂ)) * f x := fun x => by
    rw [hAdef, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_char L' t), smul_eq_mul]
  set E : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ))) f with hEdef
  have hE : ∀ x, E x = a * Complex.exp ((I * t) * (L' x : ℂ)) * f x := fun x => by
    rw [hEdef, SchwartzMap.smulLeftCLM_apply_apply het, smul_eq_mul]
  rcases eq_or_ne t 0 with ht0 | ht0
  · have h0 : E - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • g = 0 := by
      ext x
      simp only [SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hE, ha, ht0]
      simp
    rw [h0, map_zero, ht0]
    simp
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  set u : 𝓢(V, ℂ) := (t : ℂ)⁻¹ • (A - f) + (2 * Real.pi * I : ℂ) • g with hudef
  have hu : ∀ x, u x = rem t (L' x) * f x := fun x => by
    simp only [hudef, SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hA, hg,
      rem, smul_eq_mul, hL'x]
    ring
  have hub : SchwartzMap.seminorm ℂ k n u ≤ |t| * K := seminorm_rem_mul_le L' f u ht0 ht1 hu k n
  have hid : E - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • g
      = (a * t) • u + ((a - 1) • f + (-((a - 1) * t * (2 * Real.pi * I))) • g) := by
    ext x
    simp only [hudef, SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hA, hE,
      smul_eq_mul]
    field_simp
    ring
  have hna : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hna1 : ‖a - 1‖ ≤ 2 * |2 * Real.pi * c| * t ^ 2 := by
    refine (norm_cexp_mul_I_sub_one_le _).trans (le_of_eq ?_)
    rw [abs_neg, abs_mul (2 * Real.pi * c), abs_of_nonneg (sq_nonneg t)]
    ring
  have hpf := apply_nonneg (SchwartzMap.seminorm ℂ k n) f
  have hpg := apply_nonneg (SchwartzMap.seminorm ℂ k n) g
  have hpi := Real.pi_pos
  have hn1 : ‖a * t‖ = |t| := by rw [norm_mul, hna, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖-((a - 1) * t * (2 * Real.pi * I))‖ ≤ 2 * |2 * Real.pi * c| * t ^ 2 * (2 * Real.pi) := by
    have h2 : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos hpi]
    rw [norm_neg, norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_eq_abs]
    calc ‖a - 1‖ * |t| * (2 * Real.pi) ≤ (2 * |2 * Real.pi * c| * t ^ 2) * 1 * (2 * Real.pi) := by
          gcongr
      _ = _ := by ring
  rw [hid]
  calc SchwartzMap.seminorm ℂ k n ((a * t) • u + ((a - 1) • f + (-((a - 1) * t * (2 * Real.pi * I))) • g))
      ≤ SchwartzMap.seminorm ℂ k n ((a * t) • u) + (SchwartzMap.seminorm ℂ k n ((a - 1) • f) +
          SchwartzMap.seminorm ℂ k n ((-((a - 1) * t * (2 * Real.pi * I))) • g)) :=
        (map_add_le_add _ _ _).trans (by gcongr; exact map_add_le_add _ _ _)
    _ = |t| * SchwartzMap.seminorm ℂ k n u + (‖a - 1‖ * SchwartzMap.seminorm ℂ k n f +
          ‖-((a - 1) * t * (2 * Real.pi * I))‖ * SchwartzMap.seminorm ℂ k n g) := by
        rw [map_smul_eq_mul, map_smul_eq_mul, map_smul_eq_mul, hn1]
    _ ≤ |t| * (|t| * K) + (2 * |2 * Real.pi * c| * t ^ 2 * SchwartzMap.seminorm ℂ k n f +
          2 * |2 * Real.pi * c| * t ^ 2 * (2 * Real.pi) * SchwartzMap.seminorm ℂ k n g) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← sq, sq_abs]; ring

end GlobalTheory.LinearPhase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormLinearPhaseSecondOrderLeStatement
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzSeminorm_linearPhase_second_order_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by
  first | exact @GlobalTheory.LinearPhase.seminorm_phase_sub_le | exact GlobalTheory.LinearPhase.seminorm_phase_sub_le | (intros; apply GlobalTheory.LinearPhase.seminorm_phase_sub_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallAlgHom
open TensorProduct

noncomputable section
namespace GlobalTheory.CxPointsSep

theorem eq_zero_of_forall_algHom {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [IsReduced A] [Algebra.FiniteType k A] (a : A) (h : ∀ e : A →ₐ[k] k, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hb : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ k m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem isReduced_complex_tensor (D : Type) [CommRing D] [IsDomain D] [Algebra ℚ D]
    [Algebra.FiniteType ℚ D] : IsReduced (ℂ ⊗[ℚ] D) := by
  set K := FractionRing D
  have : Algebra.EssFiniteType ℚ K := inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))
  have h1 : IsReduced (K ⊗[ℚ] ℂ) := ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType K ℂ
  have h2 : IsReduced (ℂ ⊗[ℚ] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm ℚ ℂ K).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)).toRingHom hinj

theorem exists_det_ne_zero (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (r : ℕ) (f : Fin r → B) (hf : LinearIndependent ℤ f) :
    ∃ x : Fin r → (B →+* ℂ), (Matrix.of fun i j => x i (f j)).det ≠ 0 := by
  classical
  let K := FractionRing B
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ B).FG)
  let D : Subalgebra ℚ K := Algebra.adjoin ℚ ((algebraMap B K) '' (s : Set B))
  have hmem : ∀ b : B, algebraMap B K b ∈ D := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := by rw [hs]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem D n
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  haveI : Algebra.FiniteType ℚ D := by
    rw [← Subalgebra.fg_iff_finiteType]
    have := Subalgebra.fg_adjoin_finset (R := ℚ) (s.image (algebraMap B K))
    simpa [D] using this
  let g : B →+* D := (algebraMap B K).codRestrict D hmem
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective B K (congrArg Subtype.val h)
  have hD : LinearIndependent ℚ (fun j => g (f j)) := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
    exact hf.map' g.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.mpr hg)
  have hT : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] g (f j)) :=
    Module.Flat.linearIndependent_one_tmul hD
  haveI : IsReduced (ℂ ⊗[ℚ] D) := isReduced_complex_tensor D
  let pt : ((ℂ ⊗[ℚ] D) →ₐ[ℂ] ℂ) → (B →+* ℂ) := fun φ =>
    (φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℂ) (B := D)).toRingHom).comp g
  let S : Set (Fin r → ℂ) := Set.range fun x : B →+* ℂ => fun j => x (f j)
  have hspan : Submodule.span ℂ S = ⊤ := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : Fin r → ℂ := fun i => ℓ (fun j => if i = j then 1 else 0)
    have hℓv : ∀ v, ℓ v = ∑ i, v i * c i := fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ ℓ v]; rfl
    have hu : ∑ i, c i • ((1 : ℂ) ⊗ₜ[ℚ] g (f i)) = 0 := by
      apply eq_zero_of_forall_algHom (k := ℂ)
      intro φ
      have h0 : ℓ (fun j => pt φ (f j)) = 0 := hle (Submodule.subset_span ⟨pt φ, rfl⟩)
      rw [hℓv] at h0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    have hc : c = 0 := funext fun i => Fintype.linearIndependent_iff.mp hT c hu i
    apply hℓ
    refine LinearMap.ext fun v => ?_
    rw [hℓv, hc]
    simp
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent ℂ S
  have hb_top : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let bb := Module.Basis.mk hli hb_top
  let e : b ≃ Fin r := bb.indexEquiv (Pi.basisFun ℂ (Fin r))
  have hx : ∀ i : Fin r, ∃ x : B →+* ℂ, (fun j => x (f j)) = ((e.symm i : b) : Fin r → ℂ) :=
    fun i => hbS (e.symm i).2
  choose x hx using hx
  refine ⟨x, ?_⟩
  have hrows : LinearIndependent ℂ (fun i => (Matrix.of fun i j => x i (f j)) i) := by
    have : (fun i => (Matrix.of fun i j => x i (f j)) i) = (fun v : b => (v : Fin r → ℂ)) ∘ e.symm := by
      funext i; exact hx i
    rw [this]; exact hli.comp _ e.symm.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

end GlobalTheory.CxPointsSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertRepresentingUniversalSubscheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertRepresentingUniversalSubscheme
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem sigma_inv (r : ℕ) {T : Scheme.{0}} {g₀ g : T ⟶ Spec (CommRingCat.of A)}
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I : (pullback (str A B) g).IdealSheafData}
    {h₀ : Good A B r g₀ I₀} {h₁ : Good A B r g I}
    (e : (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g, ⟨I, h₁⟩⟩) :
    ∃ h : g₀ = g, I = I₀.comap
      (pullback.map (str A B) g (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])) := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp e
  refine ⟨rfl, ?_⟩
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id]
  exact (congrArg Subtype.val (eq_of_heq h2)).symm

theorem good_ker (r : ℕ) {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) {V : Scheme.{0}}
    (v : V ⟶ pullback (str A B) g) [IsClosedImmersion v] (h1 : IsFinite (v ≫ pullback.snd _ g))
    (h2 : Flat (v ≫ pullback.snd _ g)) (h3 : ∀ y, (v ≫ pullback.snd _ g).finrank y = r) :
    Good A B r g v.ker := by
  let φ := IsClosedImmersion.lift v v.ker.subschemeι (by rw [Scheme.IdealSheafData.ker_subschemeι])
  have hφ : φ ≫ v = v.ker.subschemeι := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso φ := IsClosedImmersion.isIso_of_ker_eq v.ker.subschemeι v φ hφ
    (Scheme.IdealSheafData.ker_subschemeι _)
  have e : v.ker.subschemeι ≫ pullback.snd _ g = φ ≫ (v ≫ pullback.snd _ g) := by
    rw [← Category.assoc, hφ]
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [e]; infer_instance
  · rw [e]; infer_instance
  · rw [e, Scheme.Hom.finrank_comp_left_of_isIso, h3]

end GlobalTheory.HilbAff

theorem GlobalTheory.HilbAff.universal : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ∃ (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (R.homEquiv (𝟙 H)).1), IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ Flat (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ (∀ y, (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ (R.homEquiv (𝟙 H)).1 = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro A B _ _ _ r H R
  have key : ∀ {T : Scheme.{0}} (f : T ⟶ H), R.homEquiv f =
      ⟨f ≫ (R.homEquiv (𝟙 H)).1, ⟨(R.homEquiv (𝟙 H)).2.1.comap
        (GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f), GlobalTheory.HilbAff.good_comap A B r _ f _
          (R.homEquiv (𝟙 H)).2.2⟩⟩ := fun f => by
    have := R.homEquiv_comp f (𝟙 H)
    rw [Category.comp_id] at this
    rw [this]; rfl
  refine ⟨(R.homEquiv (𝟙 H)).2.1.subscheme, (R.homEquiv (𝟙 H)).2.1.subschemeι, inferInstance,
    (R.homEquiv (𝟙 H)).2.2.1, (R.homEquiv (𝟙 H)).2.2.2.1, (R.homEquiv (𝟙 H)).2.2.2.2, ?_⟩
  intro T g V v hv h1 h2 h3
  have hG := GlobalTheory.HilbAff.good_ker A B r g v h1 h2 h3
  let y : (GlobalTheory.HilbAff.functor A B r).obj (op T) := ⟨g, ⟨v.ker, hG⟩⟩

  have cmp : ∀ (f : T ⟶ H) (hf : f ≫ (R.homEquiv (𝟙 H)).1 = g),
      pullback.map (GlobalTheory.HilbAff.str A B) g (GlobalTheory.HilbAff.str A B) (f ≫ (R.homEquiv (𝟙 H)).1)
          (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hf]) ≫
        GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f =
      pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp)
        (by rw [Category.comp_id, hf]) := by
    intro f hf
    apply pullback.hom_ext <;>
      simp only [GlobalTheory.HilbAff.bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  have cmp' : ∀ (f : T ⟶ H) (hf : f ≫ (R.homEquiv (𝟙 H)).1 = g),
      pullback.map (GlobalTheory.HilbAff.str A B) (f ≫ (R.homEquiv (𝟙 H)).1) (GlobalTheory.HilbAff.str A B) g
          (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hf]) ≫
        pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp)
          (by rw [Category.comp_id, hf]) =
      GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f := by
    intro f hf
    apply pullback.hom_ext <;>
      simp only [GlobalTheory.HilbAff.bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  let f := R.homEquiv.symm y
  have hfy : R.homEquiv f = y := Equiv.apply_symm_apply _ _
  rw [key] at hfy
  obtain ⟨hf, hI⟩ := GlobalTheory.HilbAff.sigma_inv A B r hfy
  have hcomap : (R.homEquiv (𝟙 H)).2.1.comap (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f
      (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) = v.ker := by
    rw [hI, ← Scheme.IdealSheafData.comap_comp, cmp f hf]
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · have hle : ((R.homEquiv (𝟙 H)).2.1.subschemeι).ker ≤ (v ≫ pullback.map _ g _
        (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.le_map_iff_comap_le, hcomap]
    refine ⟨IsClosedImmersion.lift _ _ hle, ?_⟩
    exact isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ hle).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, hcomap])
  · rintro f' ⟨hf', w', hpb⟩
    have hv : v.ker = (R.homEquiv (𝟙 H)).2.1.comap (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _)
        f' (𝟙 _) (by simp) (by rw [Category.comp_id, hf'])) := by
      rw [← hpb.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]
    have h' : R.homEquiv f' = y := by
      rw [key]
      refine GlobalTheory.HilbAff.sigma_eq A B r hf' ?_ _ _
      rw [hv, ← Scheme.IdealSheafData.comap_comp, cmp' f' hf']
    apply R.homEquiv.injective
    rw [h']
    exact (Equiv.apply_symm_apply R.homEquiv y).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertRepresentingUniversalSubschemeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbert_representing_universal_subscheme : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ∃ (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (R.homEquiv (𝟙 H)).1), IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ Flat (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ (∀ y, (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ (R.homEquiv (𝟙 H)).1 = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbAff.universal) | (exact GlobalTheory.HilbAff.universal) | (intros; apply GlobalTheory.HilbAff.universal  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAevalEqAevalMapOfCoprimeCharpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAevalEqAevalMapOfCoprimeCharpoly
noncomputable section

open Polynomial Matrix GlobalTheory.LatOrb IsLocalRing

namespace GlobalTheory.MaxOrder

theorem exists_eq_uniformizer_smul {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {n : ℕ} (P₀ : O[X])
    (hP : IsCoprime P₀ (derivative P₀)) (γ : Matrix (Fin n) (Fin n) K)
    (hγ : γ.charpoly = P₀.map (algebraMap O K)) (π : O) (hπ : Irreducible π)
    (y : Matrix (Fin n) (Fin n) K) (hy : IsIntegral O y) (N : ℕ) (hN : 1 ≤ N) (f : O[X])
    (hf : aeval γ f = π ^ N • y) : ∃ h : O[X], aeval γ f = π • aeval γ h := by
  classical
  obtain ⟨Q, hQm, hQ⟩ := hy
  set m := Q.natDegree with hm
  set u := π ^ N with hu
  let F : O[X] := ∑ i ∈ Finset.range (m + 1), C (Q.coeff i * u ^ (m - i)) * f ^ i
  have hF : aeval γ F = 0 := by
    have h1 : aeval γ F = u ^ m • aeval y Q := by
      rw [aeval_eq_sum_range (p := Q) y, Finset.smul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [F, map_sum, map_mul, aeval_C, map_pow, hf]
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hAlg : ∀ (c : O) (X : Matrix (Fin n) (Fin n) K), algebraMap O _ c * X = c • X :=
        fun c X => (Algebra.smul_def c X).symm
      have hmi : u ^ (m - i) * u ^ i = u ^ m := by rw [← pow_add, Nat.sub_add_cancel him]
      simp only [_root_.smul_pow, ← map_pow, hAlg, smul_mul_assoc, smul_smul]
      congr 1
      linear_combination (Q.coeff i) * hmi
    rw [h1, show aeval y Q = 0 from hQ, smul_zero]
  have hmon : P₀.Monic := monic_of_injective (IsFractionRing.injective O K) (hγ ▸ γ.charpoly_monic)
  have hd : P₀ ∣ F ^ n := by
    have h := GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval γ (F.map (algebraMap O K))
      (by rw [aeval_map_algebraMap]; exact hF)
    rw [hγ, Fintype.card_fin, ← Polynomial.map_pow] at h
    exact (map_dvd_map _ (IsFractionRing.injective O K) hmon).1 h
  let φ := residue O
  have hφπ : φ π = 0 := (residue_eq_zero_iff π).2 ((mem_maximalIdeal _).2 hπ.not_isUnit)
  have hFm : F.map φ = (f.map φ) ^ m := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_mul, map_pow]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, hQm.coeff_natDegree, Nat.sub_self,
      pow_zero, mul_one, map_one, C_1, one_mul]
    intro i hi
    have him : 0 < m - i := Nat.sub_pos_of_lt (Finset.mem_range.1 hi)
    rw [hu, map_pow, hφπ, zero_pow (by omega), C_0, zero_pow him.ne', mul_zero, zero_mul]
  have hsep : (P₀.map φ).Separable := by
    unfold Separable
    rw [derivative_map]
    exact hP.map (mapRingHom φ)
  have hd2 : P₀.map φ ∣ (f.map φ) ^ (m * n + 1) := by
    have h := Polynomial.map_dvd φ hd
    rw [Polynomial.map_pow, hFm, ← pow_mul] at h
    exact h.trans (pow_dvd_pow _ (Nat.le_succ _))
  obtain ⟨qb, hqb⟩ := (hsep.squarefree.dvd_pow_iff_dvd (Nat.succ_ne_zero _)).1 hd2
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective φ (residue_surjective) qb
  have hker : f - P₀ * q ∈ Ideal.span {C π} := by
    have h : f - P₀ * q ∈ RingHom.ker (mapRingHom φ) := by
      rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, hqb, sub_self]
    rwa [Polynomial.ker_mapRingHom, ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ,
      Ideal.map_span, Set.image_singleton] at h
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hker
  refine ⟨h, ?_⟩
  have hP0 : aeval γ P₀ = 0 := by
    rw [← aeval_map_algebraMap K, ← hγ, aeval_self_charpoly]
  have hfe : f = P₀ * q + h * C π := by rw [hh]; ring
  rw [hfe, map_add (f := _), map_mul, map_mul, hP0, zero_mul, zero_add, aeval_C, ← Algebra.commutes,
    ← Algebra.smul_def]

theorem isIntegral_aeval_eq_aeval_map : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ p : K[X], IsIntegral O (aeval γ p) → ∃ r : O[X], aeval γ p = aeval γ (r.map (algebraMap O K)) := by
  intro O K _ _ _ _ _ _ n P₀ hP γ hγ p hp
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  simp only [aeval_map_algebraMap]
  have hπK : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]; exact hπ.ne_zero
  have key : ∀ k : ℕ, ∀ f : O[X], aeval γ f = π ^ k • aeval γ p → ∃ r : O[X], aeval γ p = aeval γ r := by
    intro k
    induction k with
    | zero => intro f hf; exact ⟨f, by rw [hf, pow_zero, one_smul]⟩
    | succ k ih =>
      intro f hf
      obtain ⟨h, hh⟩ := exists_eq_uniformizer_smul P₀ hP γ hγ π hπ _ hp (k + 1) (by omega) f hf
      refine ih h ?_
      have h1 : π • (π ^ k • aeval γ p) = π • aeval γ h := by rw [smul_smul, ← pow_succ', ← hf, hh]
      rw [← algebraMap_smul K π (π ^ k • aeval γ p), ← algebraMap_smul K π (aeval γ h)] at h1
      exact (smul_right_injective _ hπK h1).symm
  obtain ⟨b, hb, hbmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) p
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
  refine key k (C (↑v⁻¹ : O) * IsLocalization.integerNormalization (nonZeroDivisors O) p) ?_
  rw [map_mul, aeval_C, ← aeval_map_algebraMap K γ (IsLocalization.integerNormalization _ p), hbmap,
    ← algebraMap_smul K b p, map_smul, algebraMap_smul, ← Algebra.smul_def, smul_smul, hv,
    ← mul_assoc, Units.inv_mul, one_mul]

end GlobalTheory.MaxOrder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_aeval_eq_aeval_map_of_coprime_charpoly : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ p : K[X], IsIntegral O (aeval γ p) → ∃ r : O[X], aeval γ p = aeval γ (r.map (algebraMap O K)) := by
  first | exact @GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map | exact GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map | (intros; apply GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatInt
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.AdeleZ

open Rat.HeightOneSpectrum GlobalTheory.NormLevelCompare

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem padic_ccast {p q : Nat.Primes} (h : p = q) :
    ∃ e : ℚ_[p] ≃A[ℚ] ℚ_[q], ∀ x, e x ∈ PadicInt.subring q ↔ x ∈ PadicInt.subring p := by
  subst h
  exact ⟨ContinuousAlgEquiv.refl ℚ _, fun _ => Iff.rfl⟩

theorem exists_clocal (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃A[ℚ] w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have h : primesEquiv (primeCorr w) = primesEquiv w := by simp [primeCorr]
  obtain ⟨c, hc⟩ := padic_ccast h
  refine ⟨((adicCompletion.padicEquiv (primeCorr w)).trans c).trans
    (adicCompletion.padicEquiv w).symm, fun x => ?_⟩
  rw [← padicEquiv_mem w, ← padicEquiv_mem (primeCorr w), ← hc]
  change adicCompletion.padicEquiv w ((adicCompletion.padicEquiv w).symm _) ∈ _ ↔ _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  rfl

variable (e : ∀ w : HeightOneSpectrum ℤ, (primeCorr w).adicCompletion ℚ ≃A[ℚ] w.adicCompletion ℚ)
  (he : ∀ w x, e w x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ)

theorem tendsto_primeCorr : Filter.Tendsto primeCorr Filter.cofinite Filter.cofinite :=
  primeCorr.injective.tendsto_cofinite

include he in
theorem maps_int : ∀ᶠ w in Filter.cofinite, Set.MapsTo
    (fun x => ((e w).toRingHom : (primeCorr w).adicCompletion ℚ →+* w.adicCompletion ℚ) x)
      ((primeCorr w).adicCompletionIntegers ℚ) (w.adicCompletionIntegers ℚ) :=
  .of_forall fun w x hx => (he w x).2 hx

def adeleMap : FiniteAdeleRing (𝓞 ℚ) ℚ →+* FiniteAdeleRing ℤ ℚ :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
      (fun w : HeightOneSpectrum ℤ => w.adicCompletion ℚ)
      (B₁ := fun v => v.adicCompletionIntegers ℚ) (B₂ := fun w => w.adicCompletionIntegers ℚ)
      primeCorr tendsto_primeCorr (fun w => (e w).toRingHom) (maps_int e he)

theorem continuous_adeleMap : Continuous (adeleMap e he) :=
  RestrictedProduct.mapAlong_continuous _ _ primeCorr tendsto_primeCorr _ (maps_int e he)
    fun w => (e w).continuous

def adeleAlgHom : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] FiniteAdeleRing ℤ ℚ where
  toFun a := ⟨fun w => e w (a (primeCorr w)), by
    have h1 := primeCorr.injective.tendsto_cofinite.eventually a.2
    exact h1.mono fun w hw => (he w _).2 hw⟩
  map_one' := FiniteAdeleRing.ext _ fun w => map_one (e w)
  map_mul' := fun a b => FiniteAdeleRing.ext _ fun w => map_mul (e w) _ _
  map_zero' := FiniteAdeleRing.ext _ fun w => map_zero (e w)
  map_add' := fun a b => FiniteAdeleRing.ext _ fun w => map_add (e w) _ _
  commutes' := fun r => FiniteAdeleRing.ext _ fun w => (e w).commutes r

theorem adeleAlgHom_apply (a : FiniteAdeleRing (𝓞 ℚ) ℚ) (w : HeightOneSpectrum ℤ) :
    adeleAlgHom e he a w = e w (a (primeCorr w)) := rfl

theorem adeleAlgHom_eq : ⇑(adeleAlgHom e he) = ⇑(adeleMap e he) := by
  funext a
  exact FiniteAdeleRing.ext _ fun w => rfl

theorem adeleAlgHom_injective : Function.Injective (adeleAlgHom e he) := by
  intro a b hab
  refine FiniteAdeleRing.ext _ fun v => ?_
  obtain ⟨w, rfl⟩ := primeCorr.surjective v
  have h := congrArg (fun x : FiniteAdeleRing ℤ ℚ => x w) hab
  simp only [adeleAlgHom_apply] at h
  exact (e w).injective h

theorem adeleAlgHom_surjective : Function.Surjective (adeleAlgHom e he) := by
  intro b
  obtain ⟨f, hf⟩ : ∃ f : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletion ℚ,
      ∀ w, f (primeCorr w) = (e w).symm (b w) :=
    ⟨_, fun w => Equiv.piCongrLeft_apply_apply
      (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ) primeCorr
      (fun w => (e w).symm (b w)) w⟩
  have hfi : ∀ᶠ v in Filter.cofinite, f v ∈ v.adicCompletionIntegers ℚ := by
    have h1 := primeCorr.symm.injective.tendsto_cofinite.eventually b.2
    refine h1.mono fun v hv => ?_
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    rw [Equiv.symm_apply_apply] at hv
    rw [hf, ← he, ContinuousAlgEquiv.apply_symm_apply]
    exact hv
  obtain ⟨a, ha⟩ : ∃ a : FiniteAdeleRing (𝓞 ℚ) ℚ, ∀ v, a v = f v := ⟨⟨f, hfi⟩, fun _ => rfl⟩
  refine ⟨a, FiniteAdeleRing.ext _ fun w => ?_⟩
  rw [adeleAlgHom_apply, ha, hf, ContinuousAlgEquiv.apply_symm_apply]


omit e he in
theorem exists_continuous_adele_equiv :
    ∃ e : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] FiniteAdeleRing ℤ ℚ, Continuous e := by
  choose e he using exists_clocal
  refine ⟨AlgEquiv.ofBijective (adeleAlgHom e he)
    ⟨adeleAlgHom_injective e he, adeleAlgHom_surjective e he⟩, ?_⟩
  change Continuous (adeleAlgHom e he)
  rw [adeleAlgHom_eq]
  exact continuous_adeleMap e he

end GlobalTheory.AdeleZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatIntStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int : ∃ e : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] FiniteAdeleRing ℤ ℚ, Continuous e := by
  first | (exact @GlobalTheory.AdeleZ.exists_continuous_adele_equiv) | (exact GlobalTheory.AdeleZ.exists_continuous_adele_equiv) | (intros; apply GlobalTheory.AdeleZ.exists_continuous_adele_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAlgebraMapOfIntegralAtHeightOnePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAlgebraMapOfIntegralAtHeightOnePrimes
open scoped BigOperators Matrix ComplexConjugate
open Polynomial

namespace GlobalTheory

theorem integral_of_forall_height_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
      (t : FractionRing R),
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧
        t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) →
      ∃ a : R, algebraMap R (FractionRing R) a = t := by
  intro R _ _ _ _ t h
  exact ReciprocityTheory.ChartRestriction.G.T0.mem_of_mem_heightOne_localizations (K := FractionRing R) t
    (fun p hp h1 => @h p hp h1)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAlgebraMapOfIntegralAtHeightOnePrimesStatement
open scoped BigOperators Matrix ComplexConjugate
open Polynomial
theorem _root_.GlobalTheory.T.exists_eq_algebraMap_of_integral_at_height_one_primes : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (t : FractionRing R), (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧ t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) → ∃ a : R, algebraMap R (FractionRing R) a = t := by
  first | exact @GlobalTheory.integral_of_forall_height_one | exact GlobalTheory.integral_of_forall_height_one | (intros; apply GlobalTheory.integral_of_forall_height_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDifferentials
open scoped TensorProduct Polynomial

namespace GlobalTheory.EtaleCoordRank

open KaehlerDifferential TensorProduct

theorem finrank_and_linearIndependent_D_unit_mul : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  intro R B K _ _ _ _ _ d t h
  have key : ∃ b : Module.Basis (Fin d) B Ω[B⁄R], ∀ i, b i = D R B (t i) := by
    letI : Algebra (MvPolynomial (Fin d) R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
    haveI : IsScalarTower R (MvPolynomial (Fin d) R) B :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R B r = MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.C r)
        simp
    haveI : Algebra.Etale (MvPolynomial (Fin d) R) B := h
    obtain ⟨⟨b, hb⟩, _⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B (Fin d)
    refine ⟨b, fun i => ?_⟩
    rw [hb]
    congr 1
    change MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.X i) = t i
    simp
  obtain ⟨b, hb⟩ := key
  let b' : Module.Basis (Fin d) K (K ⊗[B] Ω[B⁄R]) := b.baseChange K
  refine ⟨by rw [Module.finrank_eq_card_basis b', Fintype.card_fin], ?_⟩
  intro ι e u ht
  have hli : LinearIndependent K (fun i => b' (e i)) := b'.linearIndependent.comp e e.injective
  have hfun : (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) =
      (fun i => Units.map (algebraMap B K : B →* K) (u i)) • (fun i => b' (e i)) := by
    funext i
    simp only [Pi.smul_apply', Units.smul_def, Units.coe_map, MonoidHom.coe_coe, b',
      Module.Basis.baseChange_apply, hb]
    rw [Derivation.leibniz, tmul_add, tmul_smul, tmul_smul, ← algebraMap_smul K (u i : B),
      ← algebraMap_smul K (t (e i)), ht, zero_smul, add_zero]
  rw [hfun]
  exact hli.units_smul _

end GlobalTheory.EtaleCoordRank
end
