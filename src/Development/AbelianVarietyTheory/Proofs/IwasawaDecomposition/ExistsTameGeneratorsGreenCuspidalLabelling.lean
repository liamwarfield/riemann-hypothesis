module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoupledTameInertiaGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldOverPlaceAlgClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgClosedResidueField
noncomputable section

namespace GlobalTheory.ResidueFieldAlgClosed

open Polynomial

theorem isAlgClosed_residueField {Ω : Type} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  have hlift : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    Polynomial.map_surjective _ IsLocalRing.residue_surjective p
  obtain ⟨P, hPmap, hPdeg, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hdeg : (P.map (algebraMap A Ω)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj, hPdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  have hint : IsIntegral A α := ⟨P, hPmon, by rw [← Polynomial.eval_map]; exact hα⟩
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have h0 : P.eval a = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]
    exact hα
  refine ⟨IsLocalRing.residue A a, ?_⟩
  rw [← hPmap, Polynomial.eval_map, Polynomial.eval₂_hom, h0, map_zero]

theorem isAlgebraic_residueField {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω)
    (hΩ : ∀ y : Ω, IsAlgebraic ℤ y) (g : ℕ) [Fact g.Prime] [Algebra (ZMod g) (IsLocalRing.ResidueField A)] :
    Algebra.IsAlgebraic (ZMod g) (IsLocalRing.ResidueField A) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨p, hp0, hpa⟩ := hΩ (a : Ω)
  have hc : (p.content : Ω) ≠ 0 := Int.cast_ne_zero.mpr (mt Polynomial.content_eq_zero_iff.mp hp0)
  have hqa : Polynomial.aeval (a : Ω) p.primPart = 0 := by
    rw [Polynomial.eq_C_content_mul_primPart p, map_mul, Polynomial.aeval_C] at hpa
    exact (mul_eq_zero.mp hpa).resolve_left (by simpa using hc)
  have hA0 : Polynomial.aeval a p.primPart = 0 := by
    apply IsFractionRing.injective A Ω
    rw [map_zero]
    calc algebraMap A Ω (Polynomial.aeval a p.primPart)
        = Polynomial.aeval (algebraMap A Ω a) p.primPart :=
          (Polynomial.aeval_algHom_apply (algebraMap A Ω).toIntAlgHom a p.primPart).symm
      _ = 0 := hqa
  have hqg : p.primPart.map (Int.castRingHom (ZMod g)) ≠ 0 := by
    intro h
    have hdvd : Polynomial.C (g : ℤ) ∣ p.primPart := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi := congrArg (fun r => _root_.AddMonoidAlgebra.coeff (M := ℕ) r i) h
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at hi
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ g).mp hi
    have hu := Polynomial.isPrimitive_primPart p _ hdvd
    rw [Int.isUnit_iff] at hu
    have h2 := (Fact.out : g.Prime).two_le
    omega
  refine ⟨p.primPart.map (Int.castRingHom (ZMod g)), hqg, ?_⟩
  have h2 := Polynomial.aeval_algHom_apply (IsLocalRing.residue A).toIntAlgHom a p.primPart
  rw [hA0, map_zero] at h2
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [Polynomial.aeval_def] at h2
  have hφ : (algebraMap (ZMod g) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod g)) =
      algebraMap ℤ (IsLocalRing.ResidueField A) := RingHom.ext_int _ _
  rw [hφ]
  exact h2

theorem residueField_equiv (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) (g : ℕ) [Fact (Nat.Prime g)]
    (hg : (g : NumberField.RingOfIntegers E) ∈ v.asIdeal) :
    Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have hΩ : ∀ y : Ω, IsAlgebraic ℤ y := fun y =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  have hg0 : (g : IsLocalRing.ResidueField A) = 0 := by
    have h1 := (hA (g : NumberField.RingOfIntegers E)).mpr hg
    have h2 : A.valuation ((g : A) : Ω) < 1 := by simpa using h1
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact (A.valuation_lt_one_iff (g : A)).mpr h2
  have : CharP (IsLocalRing.ResidueField A) g := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hg0
  let _ : Algebra (ZMod g) (IsLocalRing.ResidueField A) := ZMod.algebra _ g
  have _ := isAlgClosed_residueField A
  have _ := isAlgebraic_residueField A hΩ g
  have : IsAlgClosure (ZMod g) (IsLocalRing.ResidueField A) := ⟨inferInstance, inferInstance⟩
  exact ⟨(IsAlgClosure.equiv (ZMod g) (IsLocalRing.ResidueField A) (Formalism.CyclotomicNorms.Fbar g)).toRingEquiv⟩

end GlobalTheory.ResidueFieldAlgClosed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldOverPlaceAlgClosure
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.ResidueBar

theorem residueField_ringEquiv_fbar : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  first
  | exact @_root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv
  | exact _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv
  | (apply _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv ..)

end GlobalTheory.ResidueBar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldOverPlaceAlgClosureStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_field_over_place_alg_closure : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  first | exact @GlobalTheory.ResidueBar.residueField_ringEquiv_fbar | exact GlobalTheory.ResidueBar.residueField_ringEquiv_fbar | (intros; apply GlobalTheory.ResidueBar.residueField_ringEquiv_fbar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaWildOfTrivialTameCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaWildOfTrivialTameCharacters
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

namespace GlobalTheory.TameWild

theorem sub_one_lt_one_of_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {g : ℕ} [hg : Fact g.Prime]
    (hvg : A.valuation (g : Ω) < 1) {z : Ω} (a : ℕ) (hz : A.valuation (z ^ (g ^ a) - 1) < 1) :
    A.valuation (z - 1) < 1 := by
  have hz1 : A.valuation z ≤ 1 := by
    have h : A.valuation (z ^ g ^ a) ≤ 1 := by
      have e : z ^ g ^ a = (z ^ g ^ a - 1) + 1 := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le hz.le (by simp))
    rw [map_pow] at h
    by_contra hc
    push Not at hc
    exact absurd h (not_le.2 (one_lt_pow' hc (pow_ne_zero _ hg.out.ne_zero)))
  have hzA : z ∈ A := (A.valuation_le_one_iff z).1 hz1
  let zA : A := ⟨z, hzA⟩
  haveI : CharP (IsLocalRing.ResidueField A) g := by
    rw [CharP.charP_iff_prime_eq_zero hg.out, ← map_natCast (IsLocalRing.residue A),
      IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hvg
  have h1 : IsLocalRing.residue A (zA ^ g ^ a - 1) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa [zA] using hz
  have h2 : IsLocalRing.residue A (zA - 1) = 0 := by
    apply pow_eq_zero_iff (n := g ^ a) (pow_ne_zero _ hg.out.ne_zero) |>.1
    rw [map_sub, map_one, sub_pow_char_pow, one_pow, ← map_pow, ← map_one (IsLocalRing.residue A), ← map_sub, h1]
  rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff] at h2
  simpa [zA] using h2


open GlobalTheory.TameInertiaGen in
theorem cob_lt_one_of_tame : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1 := by
  intro E Ω _ _ _ _ _ A v hA g hg hgv τ hτ hroot y hy
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hvg : A.valuation (g : Ω) < 1 := by
    have := (hA (g : 𝓞 E)).2 hgv
    simpa using this
  obtain ⟨p, hp0, hp⟩ := exists_nat_gen A
  have halg : IsAlgebraic ℤ y := by
    have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨m, k, hm, hk⟩ := exists_pow_eq A hp0 hp hy halg
  obtain ⟨e, he⟩ := hp g hg.out.ne_zero
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [he, pow_zero] at hvg
    exact lt_irrefl _ hvg
  have hM0 : m * e ≠ 0 := mul_ne_zero hm he0
  have hM : A.valuation y ^ (m * e) = A.valuation (g : Ω) ^ k := by
    rw [pow_mul, hk, he, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  obtain ⟨a, m', hm', hM'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM0 g hg.out.ne_one
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    exact hm' (dvd_zero _)
  set d := m'.totient with hd
  have hdpos : 0 < d := Nat.totient_pos.2 (Nat.pos_of_ne_zero hm'0)
  have hcop : g.Coprime m' := (Nat.Prime.coprime_iff_not_dvd hg.out).2 hm'
  have hdvd : m' ∣ g ^ d - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hg.out.pos)).1 (Nat.ModEq.pow_totient hcop).symm
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨r, hr, hrτ⟩ := hroot d hdpos
  have hN : g ^ d - 1 ≠ 0 := by
    have := Nat.one_lt_pow hdpos.ne' hg.out.one_lt
    omega
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hr
    exact hg.out.ne_zero (by exact_mod_cast hr.symm)
  have hR : cob τ (Units.mk0 r hr0) ∈ A.principalUnitGroup := by
    rw [ValuationSubring.mem_principalUnitGroup_iff, coe_cob, Units.val_mk0]
    exact hrτ
  have hval : A.valuation ((Units.mk0 (y ^ g ^ a) (pow_ne_zero _ hy) : Ωˣ) : Ω) =
      A.valuation ((Units.mk0 r hr0 : Ωˣ) : Ω) ^ ((c : ℤ) * k) := by
    rw [Units.val_mk0, Units.val_mk0, ← pow_left_inj₀ zero_le zero_le hm'0, map_pow, ← pow_mul, ← hM', hM, ← hr,
      map_pow, hc, ← zpow_natCast (A.valuation r) (m' * c),
      ← zpow_natCast (A.valuation r ^ ((c : ℤ) * k)) m', ← zpow_mul, ← zpow_mul]
    congr 1
    push_cast
    ring
  have h1 := cob_mem_of_zpow hτ hR hval
  rw [ValuationSubring.mem_principalUnitGroup_iff, coe_cob, Units.val_mk0, map_pow, ← div_pow] at h1
  exact sub_one_lt_one_of_pow A hvg a h1

end GlobalTheory.TameWild
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaWildOfTrivialTameCharactersStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_wild_of_trivial_tame_characters : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1 := by
  first | exact @GlobalTheory.TameWild.cob_lt_one_of_tame | exact GlobalTheory.TameWild.cob_lt_one_of_tame | (intros; apply GlobalTheory.TameWild.cob_lt_one_of_tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityLiftFromResidueField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityLiftFromResidueField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameLift

theorem valuation_sub_lt_of_redThrough_eq {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {g : ℕ} [Fact g.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) {x y : Ω} (hx : x ∈ A) (hy : y ∈ A)
    (h : redThrough A κ x = redThrough A κ y) : A.valuation (x - y) < 1 := by
  unfold redThrough at h
  rw [dite_eq_left hx, dite_eq_left hy] at h
  have h1 := κ.injective h
  have h2 : (⟨x, hx⟩ : A) - ⟨y, hy⟩ ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h1, sub_self]
  have := (A.valuation_lt_one_iff _).1 h2
  simpa using this

theorem exists_lift : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime],
    ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m →
    ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c := by
  intro E Ω _ _ _ _ _ A v hA g hg hgv κ m hm hgm c hc
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩

  have hvg : A.valuation (g : Ω) < 1 := by
    have := (hA (g : 𝓞 E)).2 hgv
    simpa using this

  have hvm : ¬ A.valuation (m : Ω) < 1 := by
    intro hlt
    have hcop : Nat.Coprime m g :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hg.out).mpr hgm)
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have e : ((u : Ω) * (m : Ω)) + (w : Ω) * (g : Ω) = 1 := by
      have := congrArg (fun z : ℤ => (z : Ω)) huw
      push_cast at this
      exact this
    have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A u)
    have hw : A.valuation (w : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A w)
    have h1 : A.valuation ((u : Ω) * (m : Ω)) < 1 := by
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' hu) hlt
    have h2 : A.valuation ((w : Ω) * (g : Ω)) < 1 := by
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' hw) hvg
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [e, Valuation.map_one] at h3
    exact lt_irrefl _ h3
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hζA : ζ ∈ A := mem_of_pow_eq_one A hm hζ.pow_eq_one
  have hr : IsPrimitiveRoot (redThrough A κ ζ) m := by
    refine IsPrimitiveRoot.mk_of_lt _ hm ?_ ?_
    · rw [← redThrough_pow A κ hζA, hζ.pow_eq_one, redThrough_one]
    · intro l hl hlm hrl
      rw [← redThrough_pow A κ hζA, ← redThrough_one A κ] at hrl
      have hv := valuation_sub_lt_of_redThrough_eq A κ (pow_mem hζA l) (one_mem A) hrl
      have heq : ζ ^ l = 1 := eq_of_pow_eq_one A hvm
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (one_pow _) hv
      exact hζ.pow_ne_one_of_pos_of_lt hl.ne' hlm heq
  obtain ⟨i, -, hi⟩ := hr.eq_pow_of_pow_eq_one hc
  refine ⟨ζ ^ i, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [redThrough_pow A κ hζA, hi]

end GlobalTheory.TameLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityLiftFromResidueFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rootOfUnity_lift_from_residueField : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m → ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c := by
  first | exact @GlobalTheory.TameLift.exists_lift | exact GlobalTheory.TameLift.exists_lift | (intros; apply GlobalTheory.TameLift.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoupledTameInertiaGenerator
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
noncomputable section

open GlobalTheory.TameCoupledEx in
theorem GlobalTheory.TameCoupledEx.exists_coupled_of (hK : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g)) (hL : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m → ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c) (hS : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (m : ℕ), 0 < m → ¬ g ∣ m → ∀ Y μ : Ω, Y ^ m = ((g : ℕ) : Ω) → μ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ Y = μ * Y) (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ := by
  intro E Ω _ _ _ _ _ A v hA g _ hg hg2 ζ hζ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsGalois E Ω := {}
  have hgp : g.Prime := Fact.out
  have hgv : A.valuation ((g : ℕ) : Ω) < 1 := val_g_lt A v hA hg
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  obtain ⟨κ⟩ := hK E Ω A v hA g hg
  let D : ℕ → ℕ := fun n => (n + 1).factorial
  have hDpos : ∀ n, 0 < D n := fun n => Nat.factorial_pos _
  have hNpos : ∀ d, 0 < d → 0 < g ^ d - 1 := fun d hd => pow_sub_one_pos hgp hd
  have hgN : ∀ d, 0 < d → ¬ g ∣ g ^ d - 1 := fun d hd => not_dvd_pow_sub_one hgp hd
  have hroot : ∀ n, ∃ r : Ω, r ^ (g ^ D n - 1) = ((g : ℕ) : Ω) := fun n =>
    IsAlgClosed.exists_pow_nat_eq _ (hNpos _ (hDpos n))
  choose r hr using hroot
  have hDdvd : ∀ n, D n ∣ D (n + 1) := fun n => Nat.factorial_dvd_factorial (by omega)
  have hdD : ∀ d, 0 < d → d ∣ D d := fun d hd => Nat.dvd_factorial hd (by omega)
  have hmem : ∀ (σ : G E Ω) {N : ℕ} {y : Ω}, 0 < N → y ^ N = ((g : ℕ) : Ω) → σ y / y ∈ A :=
    fun σ N y hN hy => tameQuot_mem A σ hN hg0 hy
  have hcl : ∀ (x : Ω) (P : Ω → Prop), IsClosed {τ : G E Ω | P (τ x)} := fun x P =>
    ReciprocityTheory.Gal.isClosed_setOf_apply x P
  let T : ℕ → Set (G E Ω) := fun n =>
    (Ine (F := E) A : Set (G E Ω)) ∩ {σ | redThrough A κ (σ (r n) / r n) = ζ (D n)}
  obtain ⟨σ, hσ⟩ : (⋂ n, T n).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T ?_ ?_ ?_ ?_
    · rintro n σ ⟨hI, hv⟩
      refine ⟨hI, ?_⟩
      show redThrough A κ (σ (r n) / r n) = ζ (D n)
      have hv' : redThrough A κ (σ (r (n + 1)) / r (n + 1)) = ζ (D (n + 1)) := hv
      rw [ratio_descent hgp hgv hI (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
        redThrough_pow A κ (hmem σ (hNpos _ (hDpos _)) (hr (n + 1))), hv']
      exact (hζ (D n) (hDpos n)).2 (D (n + 1)) (hDdvd n) (hDpos (n + 1))
    · intro n
      have hc : ζ (D n) ^ (g ^ D n - 1) = 1 := by
        rw [← (hζ _ (hDpos n)).1]; exact pow_orderOf_eq_one _
      obtain ⟨μ, hμ, hμc⟩ := hL E Ω A v hA g hg κ _ (hNpos _ (hDpos n)) (hgN _ (hDpos n)) _ hc
      obtain ⟨σ, hσI, hσr⟩ := hS E Ω A v hA g hg hg2 _ (hNpos _ (hDpos n)) (hgN _ (hDpos n)) (r n) μ (hr n) hμ
      refine ⟨σ, hσI, ?_⟩
      show redThrough A κ (σ (r n) / r n) = ζ (D n)
      have hr0 : r n ≠ 0 := ne_zero_of_pow_eq hgp (hNpos _ (hDpos n)) (hr n)
      rw [hσr, mul_div_cancel_right₀ _ hr0, hμc]
    · exact ((ReciprocityTheory.Gal.isClosed_Ine A).inter (hcl (r 0) (fun t => redThrough A κ (t / r 0) = ζ (D 0)))).isCompact
    · intro n
      exact (ReciprocityTheory.Gal.isClosed_Ine A).inter (hcl (r n) (fun t => redThrough A κ (t / r n) = ζ (D n)))
  simp only [Set.mem_iInter] at hσ
  have hσI : σ ∈ Ine (F := E) A := (hσ 0).1
  have hσv : ∀ n, redThrough A κ (σ (r n) / r n) = ζ (D n) := fun n => (hσ n).2
  refine ⟨κ, σ, hσI, ⟨hσI, ?_⟩, ?_⟩
  · intro τ hτ
    have hτI : τ ∈ Ine (F := E) A := hτ
    let Z : Set (G E Ω) := closure (Subgroup.zpowers σ : Set (G E Ω))
    have hZI : Z ⊆ Ine (F := E) A := closure_minimal (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx; exact zpow_mem hσI k) (ReciprocityTheory.Gal.isClosed_Ine A)
    let U : ℕ → Set (G E Ω) := fun n =>
      Z ∩ {h | redThrough A κ (h (r n) / r n) = redThrough A κ (τ (r n) / r n)}
    obtain ⟨h, hh⟩ : (⋂ n, U n).Nonempty := by
      refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed U ?_ ?_ ?_ ?_
      · rintro n x ⟨hxZ, hx⟩
        refine ⟨hxZ, ?_⟩
        show redThrough A κ (x (r n) / r n) = redThrough A κ (τ (r n) / r n)
        have hx' : redThrough A κ (x (r (n + 1)) / r (n + 1)) = redThrough A κ (τ (r (n + 1)) / r (n + 1)) := hx
        rw [ratio_descent hgp hgv (hZI hxZ) (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
          ratio_descent hgp hgv hτI (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
          redThrough_pow A κ (hmem x (hNpos _ (hDpos _)) (hr (n + 1))),
          redThrough_pow A κ (hmem τ (hNpos _ (hDpos _)) (hr (n + 1))), hx']
      · intro n
        have hN := hNpos _ (hDpos n)
        haveI : NeZero (g ^ D n - 1) := ⟨hN.ne'⟩
        have hprim : IsPrimitiveRoot (ζ (D n)) (g ^ D n - 1) := (hζ _ (hDpos n)).1 ▸ IsPrimitiveRoot.orderOf _
        have hc : (redThrough A κ (τ (r n) / r n)) ^ (g ^ D n - 1) = 1 := by
          rw [← redThrough_pow A κ (hmem τ hN (hr n)), tameQuot_pow τ hg0 (hr n), redThrough_one]
        obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hc
        refine ⟨σ ^ j, subset_closure (Subgroup.mem_zpowers_iff.2 ⟨(j : ℤ), by simp⟩), ?_⟩
        show redThrough A κ ((σ ^ j) (r n) / r n) = _
        rw [ratio_pow hgp hgv hσI hN (hgN _ (hDpos n)) (hr n), redThrough_pow A κ (hmem σ hN (hr n)), hσv n, hj]
      · exact (isClosed_closure.inter (hcl (r 0)
          (fun t => redThrough A κ (t / r 0) = redThrough A κ (τ (r 0) / r 0)))).isCompact
      · intro n
        exact isClosed_closure.inter (hcl (r n)
          (fun t => redThrough A κ (t / r n) = redThrough A κ (τ (r n) / r n)))
    simp only [Set.mem_iInter] at hh
    have hhZ : h ∈ Z := (hh 0).1
    have hhI := hZI hhZ
    have hhv : ∀ n, redThrough A κ (h (r n) / r n) = redThrough A κ (τ (r n) / r n) := fun n => (hh n).2
    have hρI : h⁻¹ * τ ∈ Ine (F := E) A := mul_mem (inv_mem hhI) hτI
    have hρW : ∀ y : Ω, y ≠ 0 → A.valuation ((h⁻¹ * τ) y / y - 1) < 1 := by
      refine hW E Ω A v hA g hg _ hρI ?_
      intro d hd
      have hN := hNpos _ (hDpos d)
      refine ⟨r d ^ ((g ^ D d - 1) / (g ^ d - 1)), root_down (hdD d hd) (hr d), ?_⟩
      apply val_sub_one_lt_of_red κ (hmem _ (hNpos _ hd) (root_down (hdD d hd) (hr d)))
      rw [ratio_descent hgp hgv hρI hd (hdD d hd) (root_down (hdD d hd) (hr d)) (hr d),
        redThrough_pow A κ (hmem _ hN (hr d))]
      have e1 : (h * (h⁻¹ * τ)) (r d) / r d = (h (r d) / r d) * ((h⁻¹ * τ) (r d) / r d) :=
        ratio_mul hgp hgv hhI _ hN (hgN _ (hDpos d)) (hr d)
      rw [mul_inv_cancel_left] at e1
      have e2 := congrArg (redThrough A κ) e1
      rw [redThrough_mul A κ (hmem h hN (hr d)) (hmem _ hN (hr d)), ← hhv d] at e2
      have hne : redThrough A κ (h (r d) / r d) ≠ 0 := by
        intro h0
        have : (redThrough A κ (h (r d) / r d)) ^ (g ^ D d - 1) = 1 := by
          rw [← redThrough_pow A κ (hmem h hN (hr d)), tameQuot_pow h hg0 (hr d), redThrough_one]
        rw [h0, zero_pow hN.ne'] at this
        exact zero_ne_one this
      have e3 : redThrough A κ ((h⁻¹ * τ) (r d) / r d) = 1 :=
        (mul_eq_left₀ hne).1 e2.symm
      rw [e3, one_pow]
    set C : Subgroup (G E Ω) :=
      Subgroup.closure (insert σ {σ' : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ' y / y - 1) < 1}) with hC
    have h1 : h ∈ C.topologicalClosure := by
      refine closure_mono ?_ hhZ
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _) : σ ∈ C) k
    have h2 : h⁻¹ * τ ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem _ hρW)
    have h3 := C.topologicalClosure.mul_mem h1 (C.le_topologicalClosure h2)
    rw [mul_inv_cancel_left] at h3
    exact h3
  · intro d hd y hy
    rw [ratio_descent hgp hgv hσI hd (hdD d hd) hy (hr d),
      redThrough_pow A κ (hmem σ (hNpos _ (hDpos d)) (hr d)), hσv d]
    exact (hζ d hd).2 (D d) (hdD d hd) (hDpos d)

theorem GlobalTheory.TameCoupledEx.exists_coupled_tame_generator : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ :=
  GlobalTheory.TameCoupledEx.exists_coupled_of GlobalTheory.T.residue_field_over_place_alg_closure GlobalTheory.T.exists_rootOfUnity_lift_from_residueField GlobalTheory.T.tame_kummer_inertia_surjective GlobalTheory.T.inertia_wild_of_trivial_tame_characters
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoupledTameInertiaGeneratorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coupled_tame_inertia_generator : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ := by
  first | exact @GlobalTheory.TameCoupledEx.exists_coupled_tame_generator | exact GlobalTheory.TameCoupledEx.exists_coupled_tame_generator | (intros; apply GlobalTheory.TameCoupledEx.exists_coupled_tame_generator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPlaceIsTeichmullerLiftFbar
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerReindexComplexPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerReindexComplexPlace
open Polynomial

noncomputable section

namespace GlobalTheory.TeichAt

open Formalism.L2.NT GlobalTheory.ParRay

theorem orderOf_coprime {g : ℕ} [hg : Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : (orderOf x).Coprime g := by
  have hpos := (isOfFinOrder_fbar hx).orderOf_pos
  set n := orderOf x with hn
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hg.out).2 ?_))
  intro hdvd
  have hm : g ^ n.factorization g * (n / g ^ n.factorization g) = n := Nat.ordProj_mul_ordCompl_eq_self n g
  have h1 : x ^ (g ^ n.factorization g * (n / g ^ n.factorization g)) = 1 := by rw [hm, hn, pow_orderOf_eq_one]
  have h2 : x ^ (n / g ^ n.factorization g) = 1 := pow_eq_one_of_charP g x _ _ h1
  have h3 : n ∣ n / g ^ n.factorization g := orderOf_dvd_of_pow_eq_one h2
  exact Nat.not_dvd_ordCompl hg.out hpos.ne' (hdvd.trans h3)

theorem map_zero_of_inj {Ω : Type} [Field Ω] {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
  by_contra h0
  have h1 : t 0 = 1 := (mul_eq_left₀ h0).1 h
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  apply hx.2
  refine ht x 1 hx.1 one_ne_zero ?_
  have : t x = t x * t 0 := by rw [h1, mul_one]
  rw [this, ← map_mul, mul_zero, h1, map_one]

theorem exists_teich_reindex : ∀ (g : ℕ) [Fact g.Prime] (A : ValuationSubring ℂ)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ),
    (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ t₀ : Formalism.CyclotomicNorms.Fbar g →* ℂ,
      Formalism.L2.NT.IsTeich A κ t₀ ∧ ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t₀ x = t₀ y → x = y := by
  intro g _ A κ t ht
  set s := redHom A κ t with hs_def
  have hs : ∀ x, s x = redThrough A κ (t x) := fun x => rfl
  have ht0 : t 0 = 0 := map_zero_of_inj t ht
  have hs0 : s 0 = 0 := by
    rw [hs, ht0]; unfold redThrough; rw [dite_eq_left (zero_mem A)]
    have : (⟨0, zero_mem A⟩ : A) = 0 := rfl
    rw [this, map_zero, map_zero]
  have hsne : ∀ x, x ≠ 0 → s x ≠ 0 := by
    intro x hx h0
    have hpos := (isOfFinOrder_fbar hx).orderOf_pos
    have : s x ^ orderOf x = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [h0, zero_pow hpos.ne'] at this
    exact zero_ne_one this
  have hinj : Function.Injective s := by
    intro x y h
    rcases eq_or_ne x 0 with rfl | hx
    · rcases eq_or_ne y 0 with rfl | hy
      · rfl
      · exact absurd (h.symm.trans hs0) (hsne y hy)
    · rcases eq_or_ne y 0 with rfl | hy
      · exact absurd (h.trans hs0) (hsne x hx)
      · exact redHom_inj A κ t ht x y hx hy (orderOf_coprime hx) (orderOf_coprime hy) h
  have hsurj : Function.Surjective s := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, hs0⟩
    have hn := (isOfFinOrder_fbar hy).orderOf_pos
    set n := orderOf y
    have hmem : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ∈ nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g) ↔ z ^ n = 1 :=
      fun z => mem_nthRootsFinset hn 1
    obtain ⟨a, -, ha⟩ := Finset.surj_on_of_inj_on_of_card_le (s := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g))
      (t := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g)) (fun a _ => s a)
      (fun a ha => (hmem _).2 (by rw [← map_pow, (hmem a).1 ha, map_one]))
      (fun a₁ a₂ _ _ h => hinj h) le_rfl y ((hmem y).2 (pow_orderOf_eq_one y))
    exact ⟨a, ha.symm⟩
  let e : Formalism.CyclotomicNorms.Fbar g ≃* Formalism.CyclotomicNorms.Fbar g := MulEquiv.ofBijective s ⟨hinj, hsurj⟩
  have he : ∀ x, e x = s x := fun x => rfl
  refine ⟨t.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro x
    refine ⟨mem_of_monoidHom A t _, ?_⟩
    have h1 : s (e.symm x) = x := by rw [← he, MulEquiv.apply_symm_apply]
    have h2 := hs (e.symm x)
    unfold redThrough at h2
    rw [dite_eq_left (mem_of_monoidHom A t _)] at h2
    exact h2.symm.trans h1
  · intro x y hx hy h
    have hx' : e.symm x ≠ 0 := fun h0 => hx (by rw [← e.apply_symm_apply x, h0, he, hs0])
    have hy' : e.symm y ≠ 0 := fun h0 => hy (by rw [← e.apply_symm_apply y, h0, he, hs0])
    exact e.symm.injective (ht _ _ hx' hy' h)

end GlobalTheory.TeichAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerReindexComplexPlaceStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_teichmuller_reindex_complexPlace : ∀ (g : ℕ) [Fact g.Prime] (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ t₀ : Formalism.CyclotomicNorms.Fbar g →* ℂ, Formalism.L2.NT.IsTeich A κ t₀ ∧ ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t₀ x = t₀ y → x = y := by
  first | exact @GlobalTheory.TeichAt.exists_teich_reindex | exact GlobalTheory.TeichAt.exists_teich_reindex | (intros; apply GlobalTheory.TeichAt.exists_teich_reindex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FbarExistsComplexAutCompEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FbarExistsComplexAutCompEq
open Polynomial

noncomputable section

namespace GlobalTheory.TeichGalois

variable {g : ℕ} [Fact g.Prime]

theorem map_zero_eq_zero (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  have h2 : t 0 * (t 0 - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, mul_zero, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exfalso
    have h1 : t 0 = 1 := sub_eq_zero.1 h
    have hall : ∀ x, t x = 1 := fun x => by
      have : t (x * 0) = t x * t 0 := map_mul t x 0
      rw [mul_zero, h1, mul_one] at this
      exact this.symm
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    exact hy.2 (ht y 1 hy.1 one_ne_zero (by rw [hall, hall]))

theorem exists_coprime_pow_eq_one {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) :
    ∃ m : ℕ, g.Coprime m ∧ x ^ m = 1 := by
  let K := IntermediateField.adjoin (ZMod g) ({x} : Set (Formalism.CyclotomicNorms.Fbar g))
  haveI : FiniteDimensional (ZMod g) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  have hxK : (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : K) ≠ 0 := by
    intro h; apply hx; simpa using congrArg Subtype.val h
  let u := Units.mk0 _ hxK
  have hn : x ^ orderOf u = 1 := by
    have h3 : (u : K) ^ orderOf u = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    have h4 : ((u : K) : Formalism.CyclotomicNorms.Fbar g) ^ orderOf u = 1 := by
      rw [← IntermediateField.coe_pow, h3, IntermediateField.coe_one]
    exact h4
  have hpos : 0 < orderOf u := orderOf_pos u
  obtain ⟨a, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' g (Fact.out : g.Prime).ne_one
  refine ⟨m, (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm, ?_⟩
  have h2 : (x ^ m - 1) ^ (g ^ a) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, ← heq, hn, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : g.Prime).ne_zero) |>.1 h2)

theorem exists_common_exponent (s : Finset (Formalism.CyclotomicNorms.Fbar g)) (hs : ∀ x ∈ s, x ≠ 0) :
    ∃ m : ℕ, g.Coprime m ∧ ∀ x ∈ s, x ^ m = 1 := by
  have h := fun x (hx : x ∈ s) => exists_coprime_pow_eq_one (hs x hx)
  choose! e he using h
  refine ⟨∏ x ∈ s, e x, Nat.Coprime.prod_right fun x hx => (he x hx).1, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem e hx
  rw [hc, pow_mul, (he x hx).2, one_pow]

theorem isPrimitiveRoot_map (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) {u : Formalism.CyclotomicNorms.Fbar g} {m : ℕ}
    (hm : 0 < m) (hu : IsPrimitiveRoot u m) : IsPrimitiveRoot (t u) m := by
  have hu0 : u ≠ 0 := hu.ne_zero hm.ne'
  refine ⟨by rw [← map_pow, hu.pow_eq_one, map_one], fun l hl => hu.dvd_of_pow_eq_one l ?_⟩
  exact ht _ _ (pow_ne_zero _ hu0) one_ne_zero (by rw [map_pow, hl, map_one])

theorem lift_apply_eq_sum (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (f : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) :
    MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t f = ∑ x ∈ f.coeff.support, (f.coeff x : ℂ) * t x := by
  rw [MonoidAlgebra.lift_apply, Finsupp.sum]
  simp [zsmul_eq_mul]

theorem lift_eq_zero_of_lift_eq_zero (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ht' : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y)
    (f : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) (h : MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t' f = 0) :
    MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t f = 0 := by
  classical
  set s := f.coeff.support.filter (· ≠ 0) with hs
  obtain ⟨m, hmc, hpow⟩ := exists_common_exponent s (fun x hx => (Finset.mem_filter.1 hx).2)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : g.Prime).ne_one (Nat.coprime_zero_right _ |>.1 hmc)
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  haveI : NeZero m := ⟨hm0⟩
  haveI : NeZero (m : Formalism.CyclotomicNorms.Fbar g) := ⟨by
    rw [Ne, CharP.cast_eq_zero_iff (Formalism.CyclotomicNorms.Fbar g) g]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hmc⟩
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (cyclotomic m (Formalism.CyclotomicNorms.Fbar g))
    (degree_cyclotomic_pos m _ hm).ne'
  have hu : IsPrimitiveRoot u m := isRoot_cyclotomic_iff.1 hu
  have hk : ∀ x ∈ s, ∃ i : ℕ, u ^ i = x := fun x hx => by
    obtain ⟨i, -, hi⟩ := hu.eq_pow_of_pow_eq_one (hpow x hx)
    exact ⟨i, hi⟩
  choose! k hk using hk
  let P : ℤ[X] := ∑ x ∈ s, C (f.coeff x) * X ^ (k x)
  have heval : ∀ τ : Formalism.CyclotomicNorms.Fbar g →* ℂ, τ 0 = 0 →
      MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) τ f = aeval (τ u) P := by
    intro τ hτ
    rw [lift_apply_eq_sum, ← Finset.sum_filter_of_ne (p := (· ≠ 0)) (fun x _ hx h0 => hx (by rw [h0, hτ, mul_zero]))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_sum, map_mul, aeval_C, map_pow, aeval_X, algebraMap_int_eq, eq_intCast, map_intCast]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← map_pow, hk x hx]
  have hζ := isPrimitiveRoot_map t ht hm hu
  have hζ' := isPrimitiveRoot_map t' ht' hm hu
  have h1 : aeval (t' u) P = 0 := by rw [← heval t' (map_zero_eq_zero t' ht'), h]
  have hdvd : minpoly ℤ (t' u) ∣ P := minpoly.isIntegrallyClosed_dvd (hζ'.isIntegral hm) h1
  rw [← cyclotomic_eq_minpoly hζ' hm, cyclotomic_eq_minpoly hζ hm] at hdvd
  rw [heval t (map_zero_eq_zero t ht)]
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (t u))

instance countable_fbar : Countable (Formalism.CyclotomicNorms.Fbar g) :=
  Cardinal.mk_le_aleph0_iff.1 ((Algebra.IsAlgebraic.cardinalMk_le_max (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).trans
    (max_le Cardinal.mk_le_aleph0 le_rfl))

theorem exists_ringEquiv_comp_eq : ∀ (g : ℕ) [Fact g.Prime] (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) → ∃ σ : ℂ ≃+* ℂ, ∀ x, σ (t' x) = t x := by
  intro g _ t t' ht ht'
  let α : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) →+* ℂ := (MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t').toRingHom
  let β : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) →+* ℂ := (MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t).toRingHom
  have hker : RingHom.ker α ≤ RingHom.ker β := fun f hf =>
    lift_eq_zero_of_lift_eq_zero t t' ht ht' f hf
  have hker' : RingHom.ker β ≤ RingHom.ker α := fun f hf =>
    lift_eq_zero_of_lift_eq_zero t' t ht' ht f hf
  haveI : (RingHom.ker α).IsPrime := RingHom.ker_isPrime α
  let Q := MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) ⧸ RingHom.ker α
  let α' : Q →+* ℂ := RingHom.kerLift α
  let β' : Q →+* ℂ := Ideal.Quotient.lift (RingHom.ker α) β hker
  have hα' : Function.Injective α' := RingHom.kerLift_injective α
  have hβ' : Function.Injective β' := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    have : β f = 0 := hq
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hker' this)
  haveI : Countable (MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) :=
    Function.Injective.countable (f := MonoidAlgebra.coeff) (fun a b h => by ext x; rw [h])
  haveI : Countable Q := Function.Surjective.countable Ideal.Quotient.mk_surjective
  haveI : Countable (FractionRing Q) :=
    Function.Surjective.countable (IsLocalization.mk'_surjective (nonZeroDivisors Q) (S := FractionRing Q))
  let a : FractionRing Q →+* ℂ := IsFractionRing.lift hα'
  let b : FractionRing Q →+* ℂ := IsFractionRing.lift hβ'
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq a b
  refine ⟨σ, fun x => ?_⟩
  have h := hσ (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1)))
  have ha : a (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1))) = t' x := by
    simp only [a]
    rw [IsFractionRing.lift_algebraMap]
    simp only [α']
    rw [RingHom.kerLift_mk]
    simp [α, MonoidAlgebra.lift_single]
  have hb : b (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1))) = t x := by
    simp only [b]
    rw [IsFractionRing.lift_algebraMap]
    show β (MonoidAlgebra.single x 1) = t x
    simp [β, MonoidAlgebra.lift_single]
  rw [ha, hb] at h
  exact h

end GlobalTheory.TeichGalois
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FbarExistsComplexAutCompEqStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fbar_exists_complexAut_comp_eq : ∀ (g : ℕ) [Fact g.Prime] (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) → ∃ σ : ℂ ≃+* ℂ, ∀ x, σ (t' x) = t x := by
  first | exact @GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq | exact GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq | (intros; apply GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPlaceIsTeichmullerLiftFbar
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section
namespace GlobalTheory.TeichPlace

theorem exists_place_isTeich : ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g), IsTeich A κ t := by
  intro g _ t ht
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex g
  obtain ⟨κ₀⟩ := GlobalTheory.HeightCounting.nonempty_residueField_unitBall_equiv ι
  obtain ⟨t₀, ht₀, hinj₀⟩ := GlobalTheory.T.exists_teichmuller_reindex_complexPlace g (GlobalTheory.HeightCounting.unitBall ι) κ₀ t ht
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.fbar_exists_complexAut_comp_eq g t t₀ ht hinj₀
  let A : ValuationSubring ℂ := (GlobalTheory.HeightCounting.unitBall ι).comap (σ.symm : ℂ →+* ℂ)
  have hmem : ∀ z : ℂ, z ∈ A ↔ σ.symm z ∈ GlobalTheory.HeightCounting.unitBall ι := fun z => ValuationSubring.mem_comap
  let e : A ≃+* GlobalTheory.HeightCounting.unitBall ι :=
    { toFun := fun a => ⟨σ.symm a, (hmem a).1 a.2⟩
      invFun := fun b => ⟨σ b, (hmem _).2 (by simpa using b.2)⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  refine ⟨A, (IsLocalRing.ResidueField.mapEquiv e).trans κ₀, fun x => ?_⟩
  have hx : σ.symm (t x) = t₀ x := by rw [← hσ x, RingEquiv.symm_apply_apply]
  obtain ⟨h₀, e₀⟩ := ht₀ x
  refine ⟨(hmem _).2 (hx ▸ h₀), ?_⟩
  refine Eq.trans ?_ e₀
  change κ₀ (IsLocalRing.ResidueField.map (e : A →+* GlobalTheory.HeightCounting.unitBall ι) (IsLocalRing.residue A _)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  congr 2
  exact Subtype.ext hx

end GlobalTheory.TeichPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPlaceIsTeichmullerLiftFbarStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_isTeichmuller_lift_Fbar : ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g), IsTeich A κ t := by
  first | exact @GlobalTheory.TeichPlace.exists_place_isTeich | exact GlobalTheory.TeichPlace.exists_place_isTeich | (intros; apply GlobalTheory.TeichPlace.exists_place_isTeich <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGeneratorsGreenCuspidalLabelling
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TameGrp

theorem isGenSys_gen {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) : IsGenSys L.gen := by
  intro d hd
  refine ⟨L.gen_order d hd, fun d' hdd hd' => ?_⟩
  obtain ⟨e, rfl⟩ := hdd
  have he : 0 < e := Nat.pos_of_mul_pos_left hd'
  exact L.gen_norm d e hd he

theorem prod_rootsBar_X_sub_one_pow {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (n : ℕ) :
    ((Formalism.CyclotomicNorms.rootsBar ((X - 1 : (ZMod g)[X]) ^ n)).map fun x => X - Polynomial.C (t x)).prod = (X - 1 : ℂ[X]) ^ n := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, Polynomial.roots_pow,
    ← Polynomial.C_1, Polynomial.roots_X_sub_C, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton,
    Multiset.prod_singleton, map_one, Polynomial.C_1]


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_tame_generators_cuspidal_labelling : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk), IsEmpty L.nd.Loc ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∃ Gs : GrpSide (setK D L hZ hη), ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Gs.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ ChiTOk (setK D L hZ hη) (cfK L hZ hη cf) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) := by
  intro hG _ D hE cf _ hT
  haveI : IsEmpty D.nd.Loc := hE

  have htame : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k),
        ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
          TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) σ ∧
            TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ σ (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen := by
    intro k v
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    haveI := D.nd.acOm
    exact GlobalTheory.T.exists_coupled_tame_inertia_generator D.host.E D.nd.Om (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.nd.plOm.2 _)
      (D.host.g k) (D.naut.plGw_over k v)
      (Formalism.MainNotions.Gaps.LevGap.natCast_notMem_sq_of_split _ (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v))
      _ (isGenSys_gen _)
  choose kv tg tg_mem tg_gen tg_coup using htame

  let N1 := ndLab D.nd D.nd.lab D.nd.lab_monic
  haveI : IsEmpty N1.Loc := hE
  let A : NAut N1 := GlobalTheory.Mem.GaloisStage.nAut N1 D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj
  obtain ⟨C⟩ := GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc _ _ _ N1 A hE
  have hl1 : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod :=
    fun k v L _ => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (prod_rootsBar_X_sub_one_pow (D.ntypes.teichC k) _).symm
  let D1 := setAut D hE D.nd.lab D.nd.lab_monic A C D.ntypes.tg_mem D.ntypes.tg_gen hl1
  let X1 : NTypes D1.naut :=
    { D1.ntypes with
      tg := tg
      tg_mem := tg_mem
      tg_gen := tg_gen
      heckeLoc_gamma_places := fun i => hE.elim i
      inertiaCharpoly_type := fun k v L _ => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        (prod_rootsBar_X_sub_one_pow (D.ntypes.teichC k) _).symm
      chiT_tg := fun i => hE.elim i }
  let D2 := setTy D1 hE X1 D1.nStage_trivialCharacter_compat D1.nStage_trivialCharacter_coeff_eq
  let L : Lay0 D := lay0 D2
  have hZ : L.ZOk := ⟨fun i => hE.elim i, fun i => hE.elim i⟩
  have hη : L.EtaOk := D.etaJ_tie
  refine ⟨L, hZ, hη, hE, ⟨hT.pl, hT.teich, hT.chi, hT.ser⟩, rfl, HEq.rfl, HEq.rfl, HEq.rfl, ?_, ?_, rfl,
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  · have hteich := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      GlobalTheory.T.exists_place_isTeichmuller_lift_Fbar (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
    choose tA tκ hTe using hteich
    have hlab : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k))
          (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen (isGenSys_gen _)),
          Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
            ∀ f, D.ntypes.eSer k f = eSerO O D.R.r f := by
      intro k
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      obtain ⟨O, hO1, hO2, hO3⟩ := GlobalTheory.T.exists_equivariant_labelMap_twist_cuspidalLabel (ZMod (D.host.g k)) _
        (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
          (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen (isGenSys_gen _))
      have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
      exact ⟨O, hO1, hO2, fun f => (hT.ser k f).trans
        (GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent hG _ _ _ _ _ (hT.teich k) O hO3 D.R.r f hr)⟩
    choose O hOe hOt hOs using hlab
    exact ⟨{ tA := tA, tκ := tκ, teichC_def := hTe
             ζ := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen
             ζ_gen := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; isGenSys_gen _
             O := O, eSer_def := hOs, kv := kv, tg_tame := tg_coup, O_equiv := hOe, O_tw := hOt }, fun _ => rfl⟩
  · intro k v j u hu hrep
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    haveI := D.nd.acOm
    have hP := D.nd.plOm.2 (D.naut.plGw k v)
    obtain ⟨a, ha, hua, hga⟩ := GlobalTheory.T.tameInertia_representative_residue D.host.E D.nd.Om (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v)
      (D.host.g k) hP (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v))
      (D.naut.plGw_over k v)
      (Formalism.MainNotions.Gaps.LevGap.natCast_notMem_sq_of_split _ (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v))
      (kv k v) (tg k v) _ (tg_mem k v) (isGenSys_gen _) (tg_coup k v)
      (fun A' hA' hσ hne => GlobalTheory.T.inertia_two_places_over_same_prime_trivial_meet D.host.E D.nd.Om _ _ _ hP hA' (tg k v) (tg_mem k v) hσ hne) u hrep
    refine ⟨(D.nd.chiT k v j)⁻¹, Or.inr rfl, ?_⟩
    change ((((cf.mu0 j).locK (D.naut.plGw k v)) (Units.mk0 (((show 𝓞 D.host.E from u) : 𝓞 D.host.E) : D.host.E) hu) : ℂˣ) : ℂ) =
      (D.ntypes.teichC k) ((algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))
        (((D.nd.chiT k v j)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))
    rw [GlobalTheory.T.muZeroChar_locK_congruent_rational_integer cf.P cf.W _ _ _ (cf.isMu0 j) k _ (hT.pl k v) u hu a ha hua, hT.teich k, hT.chi k v j]
    have hlabel := (GlobalTheory.Mem.Top.isCharLab_omLab cf.W k).2 (ZMod.unitOfCoprime a ha) (by simpa using hga)
    have key : ∀ z : Formalism.CyclotomicNorms.Fbar (D.host.g k), z ≠ 0 →
        (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).teich z⁻¹ = ((GlobalTheory.Mem.TypePl.labDat (D.host.g k)).teich z)⁻¹ :=
      fun z hz => eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hz, map_one])
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hlabel, Units.val_inv_eq_inv_val, map_inv₀, key _ (by
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_ne_zero _ ((_root_.map_ne_zero _).2 (Units.ne_zero _))), Units.val_pow_eq_pow_val, map_pow, map_pow]

end GlobalTheory.HeightCounting.TameGrp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGeneratorsGreenCuspidalLabellingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tame_generators_green_cuspidal_labelling : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk), IsEmpty L.nd.Loc ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∃ Gs : GrpSide (setK D L hZ hη), ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Gs.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ ChiTOk (setK D L hZ hη) (cfK L hZ hη cf) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) := by
  first | exact @GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling | exact GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling | (intros; apply GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling <;> assumption)
end
