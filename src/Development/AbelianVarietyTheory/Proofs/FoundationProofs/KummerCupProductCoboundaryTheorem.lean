module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerCoboundaryOfNorms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmodule
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaMemRange
open Polynomial

namespace GlobalTheory.KummerCob

theorem zeta_mem_range : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Field Ω] [Algebra K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → ζ ∈ Set.range (algebraMap K Ω) := by
  intro k K Ω _ _ _ _ _ _ _ N ζ hN hζ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : k) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  let φ : k →+* Ω := (algebraMap K Ω).comp ((algebraMap k[X] K).comp Polynomial.C)
  have hφ : Function.Injective φ := φ.injective
  have hξ' : IsPrimitiveRoot (φ ξ) N := hξ.map_of_injective hφ
  obtain ⟨i, -, hi⟩ := hξ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine ⟨(algebraMap k[X] K (Polynomial.C ξ)) ^ i, ?_⟩
  rw [map_pow, ← hi]
  rfl

end GlobalTheory.KummerCob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerDivisorDescendsFunctionField
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSq
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem kummer_aeval_mem_integralClosure {A₀ F E : Type} [CommRing A₀] [Field F] [Field E] [Algebra A₀ F]
    [Algebra F E] [Algebra A₀ E] [IsScalarTower A₀ F E] {x : E} (hx : IsIntegral A₀ x)
    (p : (integralClosure A₀ F)[X]) : IsIntegral A₀ (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
  | monomial n c =>
    rw [aeval_monomial]
    refine IsIntegral.mul ?_ (hx.pow n)
    have : algebraMap (integralClosure A₀ F) E c = algebraMap F E (c : F) := rfl
    rw [this]
    exact c.2.map (IsScalarTower.toAlgHom A₀ F E)

theorem kummer_dual_step (A₀ K₀ F E : Type) [CommRing A₀] [IsDomain A₀] [Field K₀] [Algebra A₀ K₀]
    [IsFractionRing A₀ K₀] [Field F] [Field E] [Algebra K₀ F] [Algebra F E] [Algebra K₀ E]
    [IsScalarTower K₀ F E] [Algebra A₀ F] [Algebra A₀ E] [IsScalarTower A₀ K₀ F] [IsScalarTower A₀ K₀ E]
    [IsScalarTower A₀ F E] [FiniteDimensional K₀ F] [FiniteDimensional F E] [CharZero K₀]
    (N : ℕ) (hN : IsUnit (N : A₀)) (x : E) (u : A₀ˣ) (hx : x ^ N = algebraMap A₀ E u)
    (hgen : Algebra.adjoin F {x} = ⊤)
    (hF : ∀ y : F, (∀ z : F, IsIntegral A₀ z → Algebra.trace K₀ F (y * z) ∈ (algebraMap A₀ K₀).range) →
      IsIntegral A₀ y) :
    ∀ y : E, (∀ z : E, IsIntegral A₀ z → Algebra.trace K₀ E (y * z) ∈ (algebraMap A₀ K₀).range) →
      IsIntegral A₀ y := by
  intro y hy
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K₀ F).injective
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI : Algebra.IsSeparable F E := inferInstance
  let C := integralClosure A₀ F
  haveI : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension A₀ K₀ F C
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K₀
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have hxA : IsIntegral A₀ x := by
    refine ⟨X ^ N - Polynomial.C (u : A₀), monic_X_pow_sub_C _ hN0, ?_⟩
    simp [eval₂_sub, hx]
  have hxC : IsIntegral C x := hxA.tower_top
  have key := traceForm_dualSubmodule_adjoin C F hgen hxC

  have hymem : y ∈ (Algebra.traceForm F E).dualSubmodule (Subalgebra.toSubmodule (Algebra.adjoin C {x})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro z hz
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    have hzA : IsIntegral A₀ (aeval x p) := kummer_aeval_mem_integralClosure hxA p
    rw [Algebra.traceForm_apply]
    have hw : IsIntegral A₀ (Algebra.trace F E (y * aeval x p)) := by
      apply hF
      intro c hc
      have : Algebra.trace F E (y * aeval x p) * c =
          Algebra.trace F E (y * (aeval x p * algebraMap F E c)) := by
        rw [mul_comm _ c, ← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def]
        ring_nf
      rw [this, Algebra.trace_trace]
      exact hy _ (hzA.mul (hc.map (IsScalarTower.toAlgHom A₀ F E)))
    exact Submodule.mem_one.mpr ⟨⟨_, hw⟩, rfl⟩
  rw [key, Submodule.mem_smul_pointwise_iff_exists] at hymem
  obtain ⟨z, hz, rfl⟩ := hymem
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨q, rfl⟩ := hz
  have hmin : minpoly F x = map (algebraMap C F) (minpoly C x) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' F hxC
  have hdvd : minpoly C x ∣ X ^ N - Polynomial.C (algebraMap A₀ C u) := by
    apply minpoly.isIntegrallyClosed_dvd hxC
    simp [hx, ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, hg⟩ := hdvd
  have hder := congrArg (fun p => aeval x (derivative p)) hg
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, derivative_mul, map_add (f := _), map_mul,
    minpoly.aeval, zero_mul, add_zero] at hder
  set d := aeval x (derivative (minpoly C x))
  let v : A₀ˣ := hN.unit * u
  have hinv : (aeval x (derivative (minpoly F x)))⁻¹ = aeval x g * x * algebraMap A₀ E (↑v⁻¹ : A₀) := by
    rw [hmin, derivative_map, aeval_map_algebraMap]
    apply inv_eq_of_mul_eq_one_right
    change d * _ = 1
    have h1 : d * aeval x g = (N : E) * x ^ (N - 1) := by rw [← hder]; simp
    have hv : ((v : A₀)) = (N : A₀) * u := by simp [v]
    calc d * (aeval x g * x * algebraMap A₀ E ↑v⁻¹)
        = (N : E) * (x ^ (N - 1) * x) * algebraMap A₀ E ↑v⁻¹ := by
          rw [← mul_assoc, ← mul_assoc, h1]; ring
      _ = algebraMap A₀ E ((v : A₀) * ↑v⁻¹) := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN0), hx, map_mul, hv, map_mul,
          map_natCast]
      _ = 1 := by simp
  rw [smul_eq_mul, hinv]
  refine IsIntegral.mul (IsIntegral.mul (kummer_aeval_mem_integralClosure hxA g) hxA) isIntegral_algebraMap
    |>.mul (kummer_aeval_mem_integralClosure hxA q)

end GlobalTheory

namespace GlobalTheory

theorem kummer_dual_induction (A₀ K₀ : Type) [CommRing A₀] [IsDomain A₀] [Field K₀] [Algebra A₀ K₀]
    [IsFractionRing A₀ K₀] [CharZero K₀] (N : ℕ) (hN : IsUnit (N : A₀)) :
    ∀ (n : ℕ) (E : Type) [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E]
      [IsScalarTower A₀ K₀ E] (s : Finset E), s.card = n → IntermediateField.adjoin K₀ (s : Set E) = ⊤ →
      (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
      ∀ y : E, (∀ z : E, IsIntegral A₀ z → Algebra.trace K₀ E (y * z) ∈ (algebraMap A₀ K₀).range) →
        IsIntegral A₀ y := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ _ _ s hs hadj _ y hy
    rw [Finset.card_eq_zero] at hs
    subst hs
    rw [Finset.coe_empty, IntermediateField.adjoin_empty] at hadj
    have hr : Module.finrank K₀ E = 1 := IntermediateField.bot_eq_top_iff_finrank_eq_one.mp hadj
    have hyb : y ∈ (⊥ : IntermediateField K₀ E) := hadj ▸ IntermediateField.mem_top
    obtain ⟨k, rfl⟩ := IntermediateField.mem_bot.mp hyb
    obtain ⟨a, ha⟩ := hy 1 isIntegral_one
    rw [mul_one, Algebra.trace_algebraMap, hr, one_smul] at ha
    rw [← ha, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  | succ n ih =>
    intro E _ _ _ _ _ s hs hadj hu y hy
    classical
    obtain ⟨x, hxs⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
    let t := s.erase x
    let F := IntermediateField.adjoin K₀ (t : Set E)
    let s' : Finset F := t.subtype (· ∈ F)
    have hs' : s'.card = n := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem (s := t) (p := (· ∈ F))
        (fun y hy => IntermediateField.subset_adjoin K₀ (t : Set E) hy),
        Finset.card_erase_of_mem hxs, hs]
      rfl
    have hadj' : IntermediateField.adjoin K₀ (s' : Set F) = ⊤ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
      change _ = IntermediateField.adjoin K₀ (t : Set E)
      congr 1
      ext w
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact Finset.mem_subtype.mp hw
      · intro hw
        exact ⟨⟨w, IntermediateField.subset_adjoin K₀ _ hw⟩, Finset.mem_subtype.mpr hw, rfl⟩
    have hu' : ∀ y ∈ s', ∃ u : A₀ˣ, y ^ N = algebraMap A₀ F u := by
      intro y hy
      obtain ⟨u, hu⟩ := hu y (Finset.mem_of_mem_erase (Finset.mem_subtype.mp hy))
      exact ⟨u, Subtype.ext hu⟩
    have hF := ih F s' hs' hadj' hu'
    obtain ⟨u, hux⟩ := hu x hxs
    have hgen : Algebra.adjoin F {x} = ⊤ := by
      have h1 : IntermediateField.adjoin F ({x} : Set E) = ⊤ := by
        apply IntermediateField.restrictScalars_injective K₀
        rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top, ← hadj]
        congr 1
        rw [Set.union_singleton, ← Finset.coe_insert, Finset.insert_erase hxs]
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun z _ => Algebra.IsAlgebraic.isAlgebraic z), h1]
      rfl
    haveI : IsScalarTower A₀ F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact kummer_dual_step A₀ K₀ F E N hN x u hux hgen hF y hy

end GlobalTheory

namespace GlobalTheory

theorem kummer_not_map_comap_le_sq :
    ∀ (A₀ K₀ E : Type) [CommRing A₀] [IsDedekindDomain A₀] [Field K₀] [CharZero K₀] [Algebra A₀ K₀]
      [IsFractionRing A₀ K₀] [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E]
      [IsScalarTower A₀ K₀ E] (N : ℕ), IsUnit (N : A₀) →
      ∀ s : Finset E, IntermediateField.adjoin K₀ (s : Set E) = ⊤ →
      (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
      ∀ P : Ideal (integralClosure A₀ E), P.IsPrime → P ≠ ⊥ →
        ¬ Ideal.map (algebraMap A₀ (integralClosure A₀ E))
          (P.comap (algebraMap A₀ (integralClosure A₀ E))) ≤ P ^ 2 := by
  intro A₀ K₀ E _ _ _ _ _ _ _ _ _ _ _ N hN s hadj hu P hP hP0 hle
  have hdual := kummer_dual_induction A₀ K₀ N hN _ E s rfl hadj hu
  haveI : IsFractionRing (integralClosure A₀ E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A₀ K₀ E _
  haveI : IsDedekindDomain (integralClosure A₀ E) := integralClosure.isDedekindDomain A₀ K₀ E
  haveI : Module.Finite A₀ (integralClosure A₀ E) := IsIntegralClosure.finite A₀ K₀ E _
  have hinj : Function.Injective (algebraMap A₀ E) := by
    rw [IsScalarTower.algebraMap_eq A₀ K₀ E]
    exact (algebraMap K₀ E).injective.comp (IsFractionRing.injective A₀ K₀)
  haveI : FaithfulSMul A₀ (integralClosure A₀ E) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  haveI : Module.IsTorsionFree A₀ (integralClosure A₀ E) := inferInstance
  have hone : Submodule.traceDual A₀ K₀ (1 : Submodule (integralClosure A₀ E) E) = 1 := by
    refine le_antisymm ?_ Submodule.one_le_traceDual_one
    intro y hy
    rw [Submodule.mem_traceDual] at hy
    refine Submodule.mem_one.mpr ⟨⟨y, hdual y fun z hz => ?_⟩, rfl⟩
    exact hy z (Submodule.mem_one.mpr ⟨⟨z, hz⟩, rfl⟩)
  have hdiff : differentIdeal A₀ (integralClosure A₀ E) = 1 := by
    rw [← FractionalIdeal.coeIdeal_eq_one (K := E), coeIdeal_differentIdeal A₀ K₀ E]
    have : FractionalIdeal.dual A₀ K₀
        (1 : FractionalIdeal (nonZeroDivisors (integralClosure A₀ E)) E) = 1 := by
      apply FractionalIdeal.coeToSubmodule_injective
      simp only [FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one, hone]
    rw [this, inv_one]
  obtain ⟨b, hbP, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hp0 : P.comap (algebraMap A₀ (integralClosure A₀ E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hb0 hbP (Algebra.IsIntegral.isIntegral b)
  haveI : (P.comap (algebraMap A₀ (integralClosure A₀ E))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hp0
  have h := pow_sub_one_dvd_differentIdeal_aux A₀ K₀ E
    (p := P.comap (algebraMap A₀ (integralClosure A₀ E))) P (e := 2) hp0
    (Ideal.dvd_iff_le.mpr hle)
  rw [hdiff, Ideal.dvd_iff_le] at h
  apply hP.ne_top
  simpa using h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSqStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_extension_prime_not_map_comap_le_sq : ∀ (A₀ K₀ E : Type) [CommRing A₀] [IsDedekindDomain A₀] [Field K₀] [CharZero K₀] [Algebra A₀ K₀] [IsFractionRing A₀ K₀]
  [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E] [IsScalarTower A₀ K₀ E] (N : ℕ), IsUnit (N : A₀) →
  ∀ s : Finset E, IntermediateField.adjoin K₀ (s : Set E) = ⊤ → (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
  ∀ P : Ideal (integralClosure A₀ E), P.IsPrime → P ≠ ⊥ →
    ¬ Ideal.map (algebraMap A₀ (integralClosure A₀ E)) (P.comap (algebraMap A₀ (integralClosure A₀ E))) ≤ P ^ 2 := by
  first | exact @GlobalTheory.kummer_not_map_comap_le_sq | exact GlobalTheory.kummer_not_map_comap_le_sq | (intros; apply GlobalTheory.kummer_not_map_comap_le_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerDivisorDescendsFunctionField
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

theorem descent_abstract (A K E Ω : Type) [CommRing A] [IsDedekindDomain A] [Field K] [CharZero K] [Algebra A K]
    [IsFractionRing A K] [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E] [Algebra A E]
    [IsScalarTower A K E] [Field Ω] [Algebra E Ω] (N : ℕ) (hN : 0 < N) (hNu : IsUnit (N : A))
    (s : Finset E) (hs : IntermediateField.adjoin K (s : Set E) = ⊤)
    (hsu : ∀ x ∈ s, ∃ u : Aˣ, x ^ N = algebraMap A E u)
    (hcl : ∀ c : ClassGroup A, ∃ d, c = d ^ N) (w : E) (hw : w ≠ 0)
    (hσ : ∀ σ : E ≃ₐ[K] E, ∃ u : E, u ≠ 0 ∧ σ w = w * u ^ N) :
    ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, (∀ x : A, algebraMap E Ω (algebraMap A E x) ∈ B) →
      ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / algebraMap K E f / c ^ N)) = 1 := by
  haveI : IsDedekindDomain (integralClosure A E) := integralClosure.isDedekindDomain A K E
  haveI : IsFractionRing (integralClosure A E) E := integralClosure.isFractionRing_of_finite_extension K E
  obtain ⟨f, J, hf, hJ⟩ := GlobalTheory.T.divisor_descent_mod_unramified_galois_submodule A (integralClosure A E) K E N hN
    (GlobalTheory.T.kummer_extension_prime_not_map_comap_le_sq A K E N hNu s hs hsu) hcl w hw hσ
  refine ⟨f, hf, fun B hB => ?_⟩
  refine GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span E Ω (integralClosure A E).toSubring B J N hN ?_ _ ?_ hJ
  · intro x
    show algebraMap E Ω (x : E) ∈ B
    obtain ⟨p, hp, hpx⟩ : IsIntegral A (x : E) := x.2
    let φ : A →+* B := ((algebraMap E Ω).comp (algebraMap A E)).codRestrict B.toSubring hB
    have hint : IsIntegral B (algebraMap E Ω x) := by
      refine ⟨p.map φ, hp.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      have h := congrArg (algebraMap E Ω) hpx
      rw [Polynomial.hom_eval₂, map_zero] at h
      exact h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hy]
    exact y.2
  · exact div_ne_zero hw ((_root_.map_ne_zero _).mpr hf)

theorem isGalois_adjoin_pair (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hζK : ζ ∈ Set.range (algebraMap K Ω))
    (a b : K) (α β : Ω) (ha : a ≠ 0) (hb : b ≠ 0) (hα : α ^ N = algebraMap K Ω a) (hβ : β ^ N = algebraMap K Ω b) :
    IsGalois K (IntermediateField.adjoin K {α, β}) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have key : ∀ (c : K) (γ x : Ω), c ≠ 0 → γ ^ N = algebraMap K Ω c → γ ∈ IntermediateField.adjoin K {α, β} →
      x ^ N = algebraMap K Ω c → x ∈ IntermediateField.adjoin K {α, β} := by
    intro c γ x hc hγ hm hx
    have hc' : algebraMap K Ω c ≠ 0 := (_root_.map_ne_zero _).mpr hc
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      rw [zero_pow hN.ne'] at hγ
      exact hc' hγ.symm
    have h1 : (x / γ) ^ N = 1 := by rw [div_pow, hx, hγ, div_self hc']
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
    obtain ⟨z, rfl⟩ := hζK
    have : x = algebraMap K Ω z ^ i * γ := by rw [hi, div_mul_cancel₀ _ hγ0]
    rw [this]
    exact mul_mem (pow_mem (IntermediateField.algebraMap_mem _ z) i) hm
  let p : K[X] := (X ^ N - C a) * (X ^ N - C b)
  have hp0 : p ≠ 0 := mul_ne_zero (X_pow_sub_C_ne_zero hN a) (X_pow_sub_C_ne_zero hN b)
  have hroot : ∀ x : Ω, x ∈ p.rootSet Ω ↔ x ^ N = algebraMap K Ω a ∨ x ^ N = algebraMap K Ω b := by
    intro x
    rw [mem_rootSet_of_ne hp0]
    simp [p, sub_eq_zero]
  have heq : IntermediateField.adjoin K {α, β} = IntermediateField.adjoin K (p.rootSet Ω) := by
    apply le_antisymm
    · apply IntermediateField.adjoin.mono
      rintro x (rfl | rfl)
      · exact (hroot _).mpr (Or.inl hα)
      · exact (hroot _).mpr (Or.inr hβ)
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases (hroot x).mp hx with h | h
      · exact key a α x ha hα (IntermediateField.subset_adjoin _ _ (by simp)) h
      · exact key b β x hb hβ (IntermediateField.subset_adjoin _ _ (by simp)) h
  rw [heq]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField (K := K) (L := Ω) (p := p) (IsAlgClosed.splits _)
  haveI : Normal K (IntermediateField.adjoin K (p.rootSet Ω)) := Normal.of_isSplittingField p
  exact ⟨⟩

theorem adjoin_pair_eq_top (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (α β : Ω)
    (α' β' : IntermediateField.adjoin K {α, β}) (hα : (α' : Ω) = α) (hβ : (β' : Ω) = β) :
    IntermediateField.adjoin K ({α', β'} : Set (IntermediateField.adjoin K {α, β})) = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.adjoin K {α, β}).val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
    Set.image_pair]
  simp [hα, hβ]

theorem divisor_descends : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ : Ω, θ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} →
      (∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N) →
      ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        ∃ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 ∧ B.valuation (θ ^ N / (algebraMap K Ω f * c ^ N)) = 1 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ hθ hw hs
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  haveI := isGalois_adjoin_pair K Ω N ζ hN hζ (zeta_mem_range k K Ω N ζ hN hζ) a b α β ha0 hb0 hα hβ
  haveI : FiniteDimensional K (IntermediateField.adjoin K {α, β}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  have hNu : IsUnit (N : FunctionField.ringOfIntegers k K) := by
    have h1 : IsUnit (N : k) := (Nat.cast_ne_zero.mpr hN.ne').isUnit
    have h2 := h1.map ((algebraMap k[X] (FunctionField.ringOfIntegers k K)).comp C)
    rwa [map_natCast] at h2
  let α' : IntermediateField.adjoin K {α, β} := ⟨α, IntermediateField.subset_adjoin _ _ (by simp)⟩
  let β' : IntermediateField.adjoin K {α, β} := ⟨β, IntermediateField.subset_adjoin _ _ (by simp)⟩
  obtain ⟨f, hf, hB⟩ := descent_abstract (FunctionField.ringOfIntegers k K) K (IntermediateField.adjoin K {α, β}) Ω
    N hN hNu {α', β'} (by rw [Finset.coe_pair]; exact adjoin_pair_eq_top K Ω α β α' β' rfl rfl)
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, ha'⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩,
          Subtype.ext hα⟩
      · rw [Finset.mem_singleton.mp hx]
        exact ⟨⟨⟨b, hb⟩, ⟨b⁻¹, hb'⟩, Subtype.ext (mul_inv_cancel₀ hb0), Subtype.ext (inv_mul_cancel₀ hb0)⟩,
          Subtype.ext hβ⟩)
    (GlobalTheory.T.classGroup_affineCurve_divisible_charZero k K N hN) ⟨θ ^ N, hw⟩ (fun h => pow_ne_zero N hθ (congrArg Subtype.val h))
    (by
      intro σ
      obtain ⟨u, hu, hu0, h⟩ := hs (σ.liftNormal Ω)
      refine ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      exact (σ.liftNormal_commutes Ω ⟨θ ^ N, hw⟩).symm.trans h)
  refine ⟨f, hf, fun B hO => ?_⟩
  obtain ⟨c, hc, hv⟩ := hB B fun x => hO x.1 x.2
  refine ⟨c, c.2, fun h => hc (Subtype.ext h), ?_⟩
  rw [div_div, map_div₀, map_mul, map_pow] at hv
  exact hv

end GlobalTheory.KummerCob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerDivisorDescendsFunctionFieldStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_divisor_descends_functionField : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ : Ω, θ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} →
      (∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N) →
      ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        ∃ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 ∧ B.valuation (θ ^ N / (algebraMap K Ω f * c ^ N)) = 1 := by
  first | exact @GlobalTheory.KummerCob.divisor_descends | exact GlobalTheory.KummerCob.divisor_descends | (intros; apply GlobalTheory.KummerCob.divisor_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCharacterGaloisInvariantClass
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CochainCoboundaryProdHomIdentities
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CochainCoboundaryProdHomIdentities
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem cochain_coboundary_prod_hom_identities :
    ∀ (Γ : Type) [Group Γ] (N : ℕ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
    (∀ g h, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g) →
    η 1 = 0 ∧ (∀ g n, η (g * n * g⁻¹) = η n + (x n).toAdd * (y g).toAdd - (x g).toAdd * (y n).toAdd) ∧
    (∀ m n, (x m).toAdd = 0 → η (m * n) = η m + η n) := by
  intro Γ _ N x y η h
  refine ⟨?_, ?_, ?_⟩
  · have h0 := h 1 1
    simp only [map_one, toAdd_one, zero_mul, mul_one] at h0
    linear_combination -h0
  · intro g n
    have h1 := h g n
    have h2 := h (g * n * g⁻¹) g
    have e : g * n * g⁻¹ * g = g * n := by group
    have e2 : (x (g * n * g⁻¹)).toAdd = (x n).toAdd := by
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
      ring
    rw [e, e2] at h2
    linear_combination h1 - h2
  · intro m n hm
    have h3 := h m n
    rw [hm, zero_mul] at h3
    linear_combination h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CochainCoboundaryProdHomIdentitiesStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_one_conj_mul_of_cup_coboundary : ∀ (Γ : Type) [Group Γ] (N : ℕ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
  (∀ g h, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g) →
  η 1 = 0 ∧ (∀ g n, η (g * n * g⁻¹) = η n + (x n).toAdd * (y g).toAdd - (x g).toAdd * (y n).toAdd) ∧
  (∀ m n, (x m).toAdd = 0 → η (m * n) = η m + η n) := by
  first | exact @GlobalTheory.cochain_coboundary_prod_hom_identities | exact GlobalTheory.cochain_coboundary_prod_hom_identities | (intros; apply GlobalTheory.cochain_coboundary_prod_hom_identities <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCharacterGaloisInvariantClass
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem kum_eq_of_apply {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N : ℕ} (hN : 0 < N) {ζ θ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) (g : Ω ≃ₐ[K] Ω) (i : ZMod N) (hg : g θ = ζ ^ i.val * θ) :
    kum ζ θ g = i := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hex : ∃ j : ZMod N, g θ = ζ ^ j.val * θ := ⟨i, hg⟩
  unfold kum
  rw [dite_eq_left hex]
  have h1 := hex.choose_spec
  have h2 : ζ ^ i.val = ζ ^ hex.choose.val := mul_right_cancel₀ hθ (hg.symm.trans h1)
  have h3 := (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)) h2
  exact (ZMod.val_injective N h3).symm

theorem eta_kummer_galoisInvariant : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
  α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b → ∀ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η →
  (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ IntermediateField.adjoin K {α, β} ∧
    (∀ g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup, η g = kum ζ θ g) ∧
    ∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix a b α β ha hb hα hβ η hη hcob
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  set E := IntermediateField.adjoin K ({α, β} : Set Ω) with hE
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hα; exact ha ((map_eq_zero _).mp hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hβ; exact hb ((map_eq_zero _).mp hβ.symm)
  obtain ⟨-, hαapp, hαmul, hαker⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨-, hβapp, hβmul, hβker⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  let x : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum ζ α g)) (fun g h => by simp [hαmul, ofAdd_add])
  let y : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum ζ β g)) (fun g h => by simp [hβmul, ofAdd_add])
  obtain ⟨-, hconj, hhom⟩ := GlobalTheory.T.eta_one_conj_mul_of_cup_coboundary (Ω ≃ₐ[K] Ω) N x y η (fun g h => hcob g h)

  have memH : ∀ g : Ω ≃ₐ[K] Ω, g ∈ E.fixingSubgroup ↔ g α = α ∧ g β = β := by
    intro g
    constructor
    · intro hg
      exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg α
          (IntermediateField.subset_adjoin K _ (by simp)),
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg β
          (IntermediateField.subset_adjoin K _ (by simp))⟩
    · rintro ⟨h1, h2⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem w hw =>
        rcases hw with rfl | rfl
        · exact h1
        · exact h2
      | algebraMap r => exact g.commutes r
      | add u v _ _ hu hv => rw [map_add (f := _), hu, hv]
      | inv u _ hu => rw [map_inv₀, hu]
      | mul u v _ _ hu hv => rw [map_mul, hu, hv]
  have kα0 : ∀ g ∈ E.fixingSubgroup, kum (N := N) ζ α g = 0 := fun g hg => (hαker g).2 ((memH g).1 hg).1
  have kβ0 : ∀ g ∈ E.fixingSubgroup, kum (N := N) ζ β g = 0 := fun g hg => (hβker g).2 ((memH g).1 hg).2
  have hηhom : ∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, η (g * h) = η g + η h :=
    fun g hg h _ => hhom g h (kα0 g hg)
  obtain ⟨θ, hθ0, hθE, hθapp⟩ := GlobalTheory.T.exists_kummer_generator_of_locallyConstant_hom K Ω N ζ hN hζ hfix E η hη hηhom
  have hkθ : ∀ g ∈ E.fixingSubgroup, η g = kum ζ θ g := fun g hg =>
    (kum_eq_of_apply hN hζ hθ0 g (η g) (hθapp g hg)).symm
  refine ⟨θ, hθ0, hθE, hkθ, fun s => ?_⟩

  have hconjH : ∀ m ∈ E.fixingSubgroup, s⁻¹ * m * s ∈ E.fixingSubgroup ∧ η (s⁻¹ * m * s) = η m := by
    intro m hm
    obtain ⟨hmα, hmβ⟩ := (memH m).1 hm
    have hsα : m (s α) = s α := by
      rw [hαapp s, map_mul, map_pow, hfix m, hmα]
    have hsβ : m (s β) = s β := by
      rw [hβapp s, map_mul, map_pow, hfix m, hmβ]
    refine ⟨(memH _).2 ⟨?_, ?_⟩, ?_⟩
    · show s⁻¹ (m (s α)) = α
      rw [hsα]; exact s.symm_apply_apply α
    · show s⁻¹ (m (s β)) = β
      rw [hsβ]; exact s.symm_apply_apply β
    · have := hconj s⁻¹ m
      rw [inv_inv] at this
      rw [this]
      simp [x, y, kα0 m hm, kβ0 m hm]
  set u := s θ / θ with hu
  have hsθ0 : s θ ≠ 0 := by simpa using hθ0
  have hu0 : u ≠ 0 := div_ne_zero hsθ0 hθ0
  refine ⟨u, ?_, hu0, ?_⟩
  · rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro m hm
    obtain ⟨hmem, hηeq⟩ := hconjH m hm
    have h1 : m θ = ζ ^ (η m).val * θ := hθapp m hm
    have h2 : (s⁻¹ * m * s) θ = ζ ^ (η m).val * θ := by rw [← hηeq]; exact hθapp _ hmem
    have h3 : m (s θ) = ζ ^ (η m).val * s θ := by
      have : s ((s⁻¹ * m * s) θ) = m (s θ) := by
        show s (s⁻¹ (m (s θ))) = m (s θ)
        exact s.apply_symm_apply _
      rw [← this, h2, map_mul, map_pow, hfix s]
    have hz : ζ ^ (η m).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hN.ne')
    rw [hu, map_div₀, h1, h3, mul_div_mul_left _ _ hz]
  · rw [map_pow, hu, div_pow, mul_div_cancel₀ _ (pow_ne_zero N hθ0)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCharacterGaloisInvariantClassStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cochain_character_galoisInvariant_class : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
  α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b → ∀ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η →
  (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ IntermediateField.adjoin K {α, β} ∧
    (∀ g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup, η g = kum ζ θ g) ∧
    ∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N := by
  first | exact @GlobalTheory.eta_kummer_galoisInvariant | exact GlobalTheory.eta_kummer_galoisInvariant | (intros; apply GlobalTheory.eta_kummer_galoisInvariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesAdjoinKummerRootsAndValuesEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesAdjoinKummerRootsAndValuesEq
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.InertKummer

theorem valuation_eq_one_of_mem {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {x : Ω} (hx : x ∈ B) (hx' : x⁻¹ ∈ B)
    (h0 : x ≠ 0) : B.valuation x = 1 := by
  have hu : IsUnit (⟨x, hx⟩ : B) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hx'⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  exact (B.valuation_eq_one_iff ⟨x, hx⟩).mp hu

theorem inert_fixes_adjoin_and_kum_eq : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ θ₀ : Ω, θ ≠ 0 → θ₀ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} → θ₀ ^ N ∈ Set.range (algebraMap K Ω) →
      ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
      ∀ g : Ω ≃ₐ[K] Ω, GlobalTheory.NeedB.Inert B g → ∀ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 →
        B.valuation (θ ^ N / (θ₀ ^ N * c ^ N)) = 1 →
        g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup ∧ GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum ζ θ₀ g := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ θ₀ hθ hθ₀ hθE hθ₀K B hB g hg c hcE hc0 hv
  haveI : NeZero N := ⟨hN.ne'⟩

  have hunit : ∀ x : K, x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 →
      B.valuation (algebraMap K Ω x) = 1 := by
    intro x hx hx' hx0
    refine valuation_eq_one_of_mem B (hB x hx) ?_ ((_root_.map_ne_zero _).mpr hx0)
    rw [← map_inv₀]; exact hB _ hx'

  have hNK0 : (N : K) ≠ 0 := by
    have : ((algebraMap k[X] K).comp Polynomial.C) (N : k) = (N : K) := map_natCast _ _
    rw [← this]; exact (_root_.map_ne_zero _).mpr (by exact_mod_cast hN.ne')
  have hNmem : (N : K) ∈ FunctionField.ringOfIntegers k K := Subalgebra.natCast_mem _ N
  have hNinv : (N : K)⁻¹ ∈ FunctionField.ringOfIntegers k K := by
    have : ((algebraMap k[X] K).comp Polynomial.C) ((N : k)⁻¹) = (N : K)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [← this]
    exact Subalgebra.algebraMap_mem _ _
  have hvN : B.valuation (N : Ω) = 1 := by
    have := hunit _ hNmem hNinv hNK0
    rwa [map_natCast] at this

  have hroot : ∀ (γ : Ω) (x : K), x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 →
      γ ^ N = algebraMap K Ω x → g γ = γ := by
    intro γ x hx hx' hx0 hγ
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N 1 γ hN hvN hg (map_one g) one_ne_zero ?_ ?_
    · rw [hγ]; exact g.commutes x
    · rw [one_pow, div_one, hγ]; exact hunit x hx hx' hx0
  have hgα : g α = α := hroot α a ha ha' ha0 hα
  have hgβ : g β = β := hroot β b hb hb' hb0 hβ
  have hfix : g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup := by
    have hz : Subgroup.zpowers g ≤ (IntermediateField.adjoin K {α, β}).fixingSubgroup := by
      rw [← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
      intro x hx
      have hgx : g x = x := by
        rcases hx with rfl | hx
        · exact hgα
        · rw [Set.mem_singleton_iff.mp hx]; exact hgβ
      have hs : g ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := hgx
      intro f
      have hf : (f : Ω ≃ₐ[K] Ω) ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := Subgroup.zpowers_le.mpr hs f.2
      exact hf
    exact hz (Subgroup.mem_zpowers g)
  have hfixE : ∀ x ∈ IntermediateField.adjoin K {α, β}, g x = x := fun x hx => hfix ⟨x, hx⟩
  refine ⟨hfix, ?_⟩

  have hgθN : g (θ ^ N) = θ ^ N := hfixE _ hθE
  have hgθ₀N : g (θ₀ ^ N) = θ₀ ^ N := by
    obtain ⟨y, hy⟩ := hθ₀K; rw [← hy]; exact g.commutes y
  have hq : g (θ / θ₀) = θ / θ₀ := by
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N c (θ / θ₀) hN hvN hg (hfixE c hcE) hc0 ?_ ?_
    · rw [div_pow, map_div₀, hgθN, hgθ₀N]
    · rw [div_pow, div_div]; exact hv
  have hq' : g θ₀ = g θ * θ₀ / θ := by
    rw [map_div₀] at hq
    have hgθ₀0 : g θ₀ ≠ 0 := (_root_.map_ne_zero g).mpr hθ₀
    rw [div_eq_div_iff hgθ₀0 hθ₀] at hq
    rw [eq_div_iff hθ, hq, mul_comm]

  have hξ : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hgθN, div_self (pow_ne_zero _ hθ)]
  obtain ⟨i, hiN, hi⟩ := hζ.eq_pow_of_pow_eq_one hξ
  have hval : ((i : ZMod N)).val = i := ZMod.val_cast_of_lt hiN
  have h1 : g θ = ζ ^ ((i : ZMod N)).val * θ := by
    rw [hval, hi]; field_simp
  have h2 : g θ₀ = ζ ^ ((i : ZMod N)).val * θ₀ := by
    rw [hq', h1]; field_simp
  rw [kum_eq_of hζ hθ _ h1, kum_eq_of hζ hθ₀ _ h2]

end GlobalTheory.InertKummer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesAdjoinKummerRootsAndValuesEqStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ θ₀ : Ω, θ ≠ 0 → θ₀ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} → θ₀ ^ N ∈ Set.range (algebraMap K Ω) →
      ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
      ∀ g : Ω ≃ₐ[K] Ω, GlobalTheory.NeedB.Inert B g → ∀ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 →
        B.valuation (θ ^ N / (θ₀ ^ N * c ^ N)) = 1 →
        g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup ∧ GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum ζ θ₀ g := by
  first | exact @GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq | exact GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq | (intros; apply GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheorem
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

theorem cup_eq_coboundary_vanishing_on_inertia : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) ∧
        ∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hC1 : IsFirstChernClassOfLineBundle K := GlobalTheory.T.tsen_theorem k K
  have hnorm : ∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 →
      ∃ x : L, Algebra.norm K x = c := fun L _ c hc => GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass K L hC1 c hc
  obtain ⟨η₀, hη₀c, hη₀⟩ := GlobalTheory.T.exists_locallyConstant_kum_cup_coboundary_of_norm_surj K Ω N ζ hN hζ hfix hnorm a b α β ha0 hb0 hα hβ
  obtain ⟨θ, hθ0, hθE, hθη, hθs⟩ :=
    GlobalTheory.T.kummer_cochain_character_galoisInvariant_class K Ω N ζ hN hζ hfix a b α β ha0 hb0 hα hβ η₀ hη₀c hη₀
  obtain ⟨f, hf0, hfB⟩ := GlobalTheory.T.kummer_divisor_descends_functionField k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ hθ0 hθE hθs
  obtain ⟨θ₀, hθ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω f) hN
  have hθ₀0 : θ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hθ₀
    exact hf0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hθ₀.symm)
  obtain ⟨hk0c, -, hk0add, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ θ₀ hN hζ hfix hθ₀0 ⟨f, hθ₀.symm⟩
  refine ⟨fun g => η₀ g - kum ζ θ₀ g, hη₀c.sub hk0c, ?_, ?_⟩
  · intro g h
    simp only
    rw [hη₀ g h, hk0add g h]
    ring
  · intro B hB g hg
    obtain ⟨c, hcE, hc0, hcv⟩ := hfB B hB
    rw [← hθ₀] at hcv
    obtain ⟨hgE, hk⟩ := GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ θ₀ hθ0 hθ₀0 hθE
      ⟨f, hθ₀.symm⟩ B hB g hg c hcE hc0 hcv
    show η₀ g - kum ζ θ₀ g = 0
    rw [hθη g hgE, hk, sub_self]

theorem thmA : GlobalTheory.NeedB.ThmA := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha0 hb0 haA hai hbA hbi hα hβ
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hβ.symm)
  obtain ⟨hαc, -, hαadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hβc, -, hβadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  exact ⟨hαadd, hαc, hβadd, hβc,
    cup_eq_coboundary_vanishing_on_inertia k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ⟩

end GlobalTheory.KummerCob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheoremStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCupProduct_coboundary_theorem : GlobalTheory.NeedB.ThmA := by
  first | exact @GlobalTheory.KummerCob.thmA | exact GlobalTheory.KummerCob.thmA | (intros; apply GlobalTheory.KummerCob.thmA <;> assumption)
end
