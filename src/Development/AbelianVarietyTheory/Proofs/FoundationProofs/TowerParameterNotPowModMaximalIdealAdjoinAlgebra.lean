module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePidSubalgebraDivPadicInt
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePidSubalgebraDivPadicInt
namespace GlobalTheory

theorem exists_finite_pid_subalgebra_div_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgebraic ℤ_[p] s) →
  ∃ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R ∧ IsPrincipalIdealRing R ∧ ∀ s ∈ S, ∃ a ∈ R, ∃ b ∈ R, s = a / b := by
  intro p _ Ω _ _ hinj S hS
  haveI : FaithfulSMul ℤ_[p] Ω := (faithfulSMul_iff_algebraMap_injective ℤ_[p] Ω).mpr hinj
  letI : Algebra (FractionRing ℤ_[p]) Ω := FractionRing.liftAlgebra ℤ_[p] Ω
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) Ω := FractionRing.isScalarTower_liftAlgebra ℤ_[p] Ω
  set L := IntermediateField.adjoin (FractionRing ℤ_[p]) (S : Set Ω) with hL
  haveI : FiniteDimensional (FractionRing ℤ_[p]) L := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    exact ((hS x hx).extendScalars (IsFractionRing.injective ℤ_[p] (FractionRing ℤ_[p]))).isIntegral
  haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) L := inferInstance
  haveI : IsDedekindDomain (integralClosure ℤ_[p] L) :=
    integralClosure.isDedekindDomain ℤ_[p] (FractionRing ℤ_[p]) L
  haveI : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.finite ℤ_[p] (FractionRing ℤ_[p]) L (integralClosure ℤ_[p] L)
  have hPID : IsPrincipalIdealRing (integralClosure ℤ_[p] L) := by
    apply IsPrincipalIdealRing.of_finite_primes
    haveI := GlobalTheory.finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[p] (integralClosure ℤ_[p] L)
    apply ((Set.finite_range (fun M : MaximalSpectrum (integralClosure ℤ_[p] L) => M.asIdeal)).insert ⊥).subset
    intro I hI
    by_cases h : I = ⊥
    · exact Or.inl h
    · exact Or.inr ⟨⟨I, (show I.IsPrime from hI).isMaximal h⟩, rfl⟩
  let f : L →ₐ[ℤ_[p]] Ω :=
    { algebraMap L Ω with
      commutes' := fun r => by
        change ((algebraMap ℤ_[p] L r : L) : Ω) = _
        rw [IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) L r]
        exact (IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) Ω r).symm }
  have hf : Function.Injective f := Subtype.val_injective
  let e := Subalgebra.equivMapOfInjective (integralClosure ℤ_[p] L) f hf
  refine ⟨(integralClosure ℤ_[p] L).map f, Module.Finite.equiv e.toLinearEquiv,
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective, ?_⟩
  intro s hs
  obtain ⟨c, hc0, hci⟩ := (hS s hs).exists_integral_multiple
  have hsL : s ∈ L := IntermediateField.subset_adjoin _ _ hs
  refine ⟨c • s, ?_, algebraMap ℤ_[p] Ω c, Subalgebra.algebraMap_mem _ c, ?_⟩
  · rw [Subalgebra.mem_map]
    refine ⟨c • ⟨s, hsL⟩, ?_, rfl⟩
    show IsIntegral ℤ_[p] (c • (⟨s, hsL⟩ : L))
    rw [← isIntegral_algHom_iff f hf]
    exact hci
  · rw [Algebra.smul_def, mul_div_cancel_left₀ _ ((map_ne_zero_iff _ hinj).mpr hc0)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePidSubalgebraDivPadicIntStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgebraic ℤ_[p] s) →
  ∃ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R ∧ IsPrincipalIdealRing R ∧ ∀ s ∈ S, ∃ a ∈ R, ∃ b ∈ R, s = a / b := by
  first | exact @GlobalTheory.exists_finite_pid_subalgebra_div_padicInt | exact GlobalTheory.exists_finite_pid_subalgebra_div_padicInt | (intros; apply GlobalTheory.exists_finite_pid_subalgebra_div_padicInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorValuationPrimeDvdPowSubOfFinitePa
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorValuationPrimeDvdPowSubOfFinitePa
namespace GlobalTheory

theorem exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ v : Valuation Ω NNReal, (∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1) → v (p : Ω) < 1 →
  ∀ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R → IsPrincipalIdealRing R →
  ∃ π ∈ R, π ≠ 0 ∧ v π < 1 ∧ (p : Ω) / π ∈ R ∧ ∃ f : ℕ, 0 < f ∧ ∀ t ∈ R, (t ^ p ^ f - t) / π ∈ R := by
  intro p _ Ω _ _ hinj v hint hp R hfin hpid
  have hle : ∀ x : R, v (x : Ω) ≤ 1 := fun x => hint _ ((IsIntegral.of_finite ℤ_[p] x).map R.val)
  obtain ⟨P, hP⟩ : ∃ P : Ideal R, ∀ x, x ∈ P ↔ v (x : Ω) < 1 := by
    refine ⟨{ carrier := {x | v (x : Ω) < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun x => Iff.rfl⟩
    · intro a b ha hb
      simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at *
      exact lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
    · simp
    · intro c x hx
      simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, map_mul] at *
      calc v (c:Ω) * v x ≤ 1 * v x := mul_le_mul' (hle c) le_rfl
        _ = v x := one_mul _
        _ < 1 := hx
  have hpR : ((p : R) : Ω) = (p : Ω) := by simp
  have hpP : (p : R) ∈ P := by rw [hP, hpR]; exact hp
  have hp0 : (p : Ω) ≠ 0 := by
    intro h
    have h1 : algebraMap ℤ_[p] Ω (p : ℤ_[p]) = algebraMap ℤ_[p] Ω 0 := by simp [h]
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (hinj h1)
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro h
      have h1 : (1 : R) ∈ P := h ▸ Submodule.mem_top
      rw [hP] at h1; simp at h1
    · intro x y hxy
      rw [hP, hP]; rw [hP] at hxy
      simp only [Subalgebra.coe_mul, map_mul] at hxy
      by_contra hc
      push_neg at hc
      have hx1 : v x = 1 := le_antisymm (hle x) hc.1
      have hy1 : v y = 1 := le_antisymm (hle y) hc.2
      rw [hx1, hy1, one_mul] at hxy
      exact lt_irrefl _ hxy
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    apply hp0; rw [← hpR, hpP]; rfl
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hPne
  set g := Submodule.IsPrincipal.generator P with hgdef
  have hgmem : g ∈ P := Submodule.IsPrincipal.generator_mem P
  have hg0 : g ≠ 0 := by
    intro h; apply hPne
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero P).mpr h
  have hdvd : ∀ x : R, x ∈ P → ∃ c : R, x = g * c := fun x hx =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd P).mp hx

  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hpk : ((p : ℕ) : R ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hpP
  have hchar : CharP (R ⧸ P) p := by
    rw [← ringChar.eq_iff]
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (ringChar.dvd hpk) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  have hunder : P.under ℤ_[p] = IsLocalRing.maximalIdeal ℤ_[p] := by
    apply le_antisymm
    · apply IsLocalRing.le_maximalIdeal
      intro h
      apply hPprime.ne_top
      rw [Ideal.eq_top_iff_one] at h ⊢
      simpa [Ideal.mem_comap] using h
    · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
      show (p : ℤ_[p]) ∈ P.comap (algebraMap ℤ_[p] R)
      rw [Ideal.mem_comap, map_natCast]; exact hpP
  haveI : Finite (ℤ_[p] ⧸ P.under ℤ_[p]) := by
    rw [hunder]
    exact Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  haveI : Finite (R ⧸ P) := Module.finite_of_finite (ℤ_[p] ⧸ P.under ℤ_[p])
  letI := Fintype.ofFinite (R ⧸ P)
  obtain ⟨n, -, hcard⟩ := FiniteField.card (R ⧸ P) p
  refine ⟨(g : Ω), g.2, ?_, ?_, ?_, (n : ℕ), n.pos, ?_⟩
  · exact fun h => hg0 (Subtype.ext h)
  · exact (hP g).mp hgmem
  · obtain ⟨c, hc⟩ := hdvd _ hpP
    have : (p : Ω) = (g : Ω) * (c : Ω) := by rw [← hpR, hc]; rfl
    rw [this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]
    exact c.2
  · intro t ht
    have hmk : Ideal.Quotient.mk P (⟨t, ht⟩ ^ p ^ (n : ℕ)) = Ideal.Quotient.mk P ⟨t, ht⟩ := by
      rw [map_pow, ← hcard, FiniteField.pow_card]
    rw [Ideal.Quotient.eq] at hmk
    obtain ⟨c, hc⟩ := hdvd _ hmk
    have : t ^ p ^ (n : ℕ) - t = (g : Ω) * (c : Ω) := by
      have := congrArg (fun x : R => (x : Ω)) hc
      simpa using this
    rw [this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]
    exact c.2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorValuationPrimeDvdPowSubOfFinitePaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ v : Valuation Ω NNReal, (∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1) → v (p : Ω) < 1 →
  ∀ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R → IsPrincipalIdealRing R →
  ∃ π ∈ R, π ≠ 0 ∧ v π < 1 ∧ (p : Ω) / π ∈ R ∧ ∃ f : ℕ, 0 < f ∧ ∀ t ∈ R, (t ^ p ^ f - t) / π ∈ R := by
  first | exact @GlobalTheory.exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt | exact GlobalTheory.exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt | (intros; apply GlobalTheory.exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivMemSubalgebraOfValuationLeOneOfUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivMemSubalgebraOfValuationLeOneOfUniformizer
namespace GlobalTheory.K5.IntFrac

open Polynomial

theorem mem_adjoin_inv_of_isIntegral' {R K : Type*} [CommRing R] [Field K] [Algebra R K] {z : K}
    (hz : z ≠ 0) (hi : IsIntegral R z) : z ∈ Algebra.adjoin R {z⁻¹} := by
  obtain ⟨p, hpm, hp⟩ := hi
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one,
    one_mul] at hp
  obtain ⟨m, hm⟩ : ∃ m, p.natDegree = m + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h => ?_
    rw [h, Finset.sum_range_zero, pow_zero, zero_add] at hp
    exact one_ne_zero hp
  rw [hm] at hp
  have hzn : z ^ (m + 1) = -∑ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hp
  have h1 : z = z ^ (m + 1) * z⁻¹ ^ m := by
    rw [pow_succ, mul_comm (z ^ m) z, mul_assoc, ← mul_pow, mul_inv_cancel₀ hz, one_pow, mul_one]
  have hterm : ∀ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z ^ i * z⁻¹ ^ m =
      algebraMap R K (p.coeff i) * z⁻¹ ^ (m - i) := by
    intro i hi
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    rw [hk, Nat.add_sub_cancel_left, mul_assoc, pow_add, ← mul_assoc (z ^ i), ← mul_pow,
      mul_inv_cancel₀ hz, one_pow, one_mul]
  have key : z = -∑ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z⁻¹ ^ (m - i) := by
    rw [← Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← neg_mul, ← hzn]
    exact h1
  have hmem : -∑ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z⁻¹ ^ (m - i) ∈
      Algebra.adjoin R {z⁻¹} := by
    refine Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _
      (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ (Algebra.subset_adjoin ?_) _))
    exact Set.mem_singleton _
  rw [← key] at hmem
  exact hmem

theorem mem_of_div_le_one : ∀ (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (B : Subalgebra O Ω), (∀ x ∈ B, v x ≤ 1) → ∀ π ∈ B, π ≠ 0 → v π < 1 → (∀ x ∈ B, v x < 1 → x / π ∈ B) →
  ∀ a ∈ B, ∀ b ∈ B, v (a / b) ≤ 1 → a / b ∈ B := by
  intro O Ω _ _ _ v hv B hB π hπB hπ0 hπ1 hdiv
  have hvπ : 0 < v π := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hπ0)
  have hA : ∀ n : ℕ, ∀ a ∈ B, v (a / π ^ n) ≤ 1 → a / π ^ n ∈ B := by
    intro n
    induction n with
    | zero => intro a ha _; simpa using ha
    | succ k ih =>
      intro a ha hle
      have hlt : v a < 1 := by
        have he : v a = v (a / π ^ (k + 1)) * v π ^ (k + 1) := by
          rw [map_div₀, map_pow, div_mul_cancel₀]
          exact pow_ne_zero _ hvπ.ne'
        rw [he]
        calc v (a / π ^ (k + 1)) * v π ^ (k + 1) ≤ 1 * v π ^ (k + 1) := by gcongr
          _ < 1 := by
            rw [one_mul]
            exact pow_lt_one₀ hvπ.le hπ1 (Nat.succ_ne_zero k)
      have he : a / π ^ (k + 1) = a / π / π ^ k := by rw [pow_succ', div_div]
      rw [he] at hle ⊢
      exact ih _ (hdiv a ha hlt) hle
  intro a ha b hb hab
  by_cases hb0 : b = 0
  · rw [hb0, div_zero]
    exact B.zero_mem
  have hvb : 0 < v b := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hb0)
  have hex : ∃ n, v π ^ (n + 1) < v b := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hvb hπ1
    cases m with
    | zero => exact absurd (hB b hb) (not_le.mpr (by simpa using hm))
    | succ k => exact ⟨k, hm⟩
  classical
  set n := Nat.find hex with hndef
  have hn : v π ^ (n + 1) < v b := Nat.find_spec hex
  have hle : v b ≤ v π ^ n := by
    by_cases h0 : n = 0
    · rw [h0, pow_zero]
      exact hB b hb
    · have hmin := Nat.find_min hex (show n - 1 < n by omega)
      have hn1 : n - 1 + 1 = n := by omega
      rw [hn1] at hmin
      exact not_lt.mp hmin
  have hvπn : 0 < v π ^ n := pow_pos hvπ n
  have hvw_le : v (b / π ^ n) ≤ 1 := by
    rw [map_div₀, map_pow, div_le_one₀ hvπn]
    exact hle
  have hwB : b / π ^ n ∈ B := hA n b hb hvw_le
  have hvw : v (b / π ^ n) = 1 := by
    refine le_antisymm hvw_le (not_lt.mp fun hlt => ?_)
    have h2 := hB _ (hdiv _ hwB hlt)
    rw [div_div, ← pow_succ, map_div₀, map_pow, div_le_one₀ (pow_pos hvπ _)] at h2
    exact not_le.mpr hn h2
  have hw0 : b / π ^ n ≠ 0 := by
    intro h
    rw [h, map_zero] at hvw
    exact zero_ne_one hvw
  have hwinv : (b / π ^ n)⁻¹ ∈ B := by
    have hint : IsIntegral O (b / π ^ n)⁻¹ := (hv _).mp (by rw [map_inv₀, hvw, inv_one])
    have hmem := mem_adjoin_inv_of_isIntegral' (inv_ne_zero hw0) hint
    rw [inv_inv] at hmem
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hwB) hmem
  have haπ : a / π ^ n ∈ B := by
    apply hA n a ha
    have he : a / π ^ n = a / b * (b / π ^ n) := by field_simp
    rw [he, map_mul, hvw, mul_one]
    exact hab
  have he : a / b = a / π ^ n * (b / π ^ n)⁻¹ := by field_simp
  rw [he]
  exact B.mul_mem haπ hwinv

end GlobalTheory.K5.IntFrac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivMemSubalgebraOfValuationLeOneOfUniformizerStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer : ∀ (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (B : Subalgebra O Ω), (∀ x ∈ B, v x ≤ 1) → ∀ π ∈ B, π ≠ 0 → v π < 1 → (∀ x ∈ B, v x < 1 → x / π ∈ B) →
  ∀ a ∈ B, ∀ b ∈ B, v (a / b) ≤ 1 → a / b ∈ B := by
  first | exact @GlobalTheory.K5.IntFrac.mem_of_div_le_one | exact GlobalTheory.K5.IntFrac.mem_of_div_le_one | (intros; apply GlobalTheory.K5.IntFrac.mem_of_div_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsFieldAndPthRootsOfLocalAlgFrobeniusFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsFieldAndPthRootsOfLocalAlgFrobeniusFixed
namespace GlobalTheory

theorem localAlg_frob_fixed_isField_and_pth_roots :
    ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
  (T : Finset A) (f : ℕ), 0 < f → Algebra.adjoin k (T : Set A) = ⊤ → (∀ t ∈ T, t ^ p ^ f = t) →
  IsField A ∧ ∀ (y : A) (a : k), y ^ p = algebraMap k A a → ∃ b : k, y = algebraMap k A b := by
  intro p hp k A _ _ _ _ _ T f hf hT hfix
  have hp1 : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt

  have hint : ∀ t ∈ (T : Set A), IsIntegral k t := by
    intro t ht
    refine ⟨Polynomial.X ^ (p ^ f) - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hp1)
    · simp [hfix t ht]
  have hfinA : Module.Finite k (Algebra.adjoin k (T : Set A)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet hint
  rw [hT] at hfinA
  haveI : Module.Finite k A := Module.Finite.equiv (Subalgebra.topEquiv (R := k) (A := A)).toLinearEquiv

  have hpk : ((p ^ f : ℕ) : k) = 0 := by
    rw [CharP.cast_eq_zero_iff k p]; exact dvd_pow_self p hf.ne'
  have hD : KaehlerDifferential.D k A = 0 := by
    apply Derivation.ext_of_adjoin_eq_top (T : Set A) hT
    intro t ht
    have h1 := (KaehlerDifferential.D k A).leibniz_pow t (p ^ f)
    rw [hfix t ht] at h1
    rw [h1, ← Nat.cast_smul_eq_nsmul k, hpk, zero_smul]
    rfl
  haveI : Subsingleton (Ω[A⁄k]) := by
    constructor
    intro x y
    have hx : ∀ z : Ω[A⁄k], z = 0 := by
      intro z
      have htop := KaehlerDifferential.span_range_derivation k A
      have hz : z ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by rw [htop]; trivial
      rw [hD] at hz
      have : Set.range (⇑(0 : Derivation k A (Ω[A⁄k]))) ⊆ ({0} : Set (Ω[A⁄k])) := by
        rintro _ ⟨w, rfl⟩; simp
      have := Submodule.span_mono (R := A) this hz
      simpa using this
    rw [hx x, hx y]
  haveI : Algebra.FormallyUnramified k A := ⟨inferInstance⟩
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hField : IsField A := IsArtinianRing.isField_of_isReduced_of_isLocalRing A
  refine ⟨hField, ?_⟩
  intro y a hy
  letI : Field A := hField.toField
  haveI : Algebra.IsSeparable k A := Algebra.FormallyUnramified.isSeparable k A
  haveI : ExpChar k p := ExpChar.prime hp.out
  have hmem : y ∈ perfectClosure k A := by
    rw [mem_perfectClosure_iff_pow_mem p]
    exact ⟨1, by rw [pow_one, hy]; exact ⟨a, rfl⟩⟩
  rw [perfectClosure.eq_bot_of_isSeparable, IntermediateField.mem_bot] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb.symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsFieldAndPthRootsOfLocalAlgFrobeniusFixedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_and_pthRoots_of_localAlg_frobenius_fixed : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
  (T : Finset A) (f : ℕ), 0 < f → Algebra.adjoin k (T : Set A) = ⊤ → (∀ t ∈ T, t ^ p ^ f = t) →
  IsField A ∧ ∀ (y : A) (a : k), y ^ p = algebraMap k A a → ∃ b : k, y = algebraMap k A b := by
  first | exact @GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots | exact GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots | (intros; apply GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots <;> assumption)
end
end

open GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.NotPow

theorem residue_core : ∀ (p : ℕ) [Fact p.Prime] (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω], (Ideal.span {(p : O)}).IsMaximal →
  ∀ (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (T : Finset Ω), (∀ t ∈ T, IsIntegral O t) → ∀ π ∈ Algebra.adjoin O (T : Set Ω), π ≠ 0 → v π < 1 →
  (p : Ω) / π ∈ Algebra.adjoin O (T : Set Ω) →
  ∀ f : ℕ, 0 < f → (∀ t ∈ T, (t ^ p ^ f - t) / π ∈ Algebra.adjoin O (T : Set Ω)) →
  (∀ x ∈ Algebra.adjoin O (T : Set Ω), v x < 1 → x / π ∈ Algebra.adjoin O (T : Set Ω)) ∧
  ∀ y ∈ Algebra.adjoin O (T : Set Ω), ∀ a : O, v (y ^ p - algebraMap O Ω a) < 1 → ∃ b : O, v (y - algebraMap O Ω b) < 1 := by
  intro p _ O Ω _ _ _ hmax v hv T hT π hπ hπ0 hvπ hpπ f hf hstep
  classical
  have hint : ∀ x ∈ Algebra.adjoin O (T : Set Ω), v x ≤ 1 := fun x hx =>
    (hv x).2 (Algebra.adjoin_le (S := integralClosure O Ω) (fun t ht => hT t ht) hx)
  have hunit : ∀ x ∈ Algebra.adjoin O (T : Set Ω), v x = 1 →
      ∃ w ∈ Algebra.adjoin O (T : Set Ω), x * w = 1 := by
    intro x hx hx1
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx1
      exact zero_ne_one hx1
    obtain ⟨P, hPm, hP⟩ := (hv x⁻¹).1 (by rw [map_inv₀, hx1, inv_one])
    letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
    have h1 := Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) x⁻¹ P
    rw [hP, invOf_eq_inv, inv_inv] at h1
    have h2 : Polynomial.eval₂ (algebraMap O Ω) x P.reverse = 0 :=
      (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ (inv_ne_zero hx0))
    have h3 := Polynomial.divX_mul_X_add P.reverse
    rw [Polynomial.coeff_zero_reverse, hPm.leadingCoeff, Polynomial.C_1] at h3
    rw [← h3, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      Polynomial.eval₂_one] at h2
    refine ⟨-Polynomial.eval₂ (algebraMap O Ω) x (Polynomial.divX P.reverse), neg_mem ?_, ?_⟩
    · have hm := (Polynomial.aeval (⟨x, hx⟩ : Algebra.adjoin O (T : Set Ω))
        (Polynomial.divX P.reverse)).2
      rwa [Polynomial.aeval_subalgebra_coe, Polynomial.aeval_def] at hm
    · linear_combination -h2
  let I : Ideal (Algebra.adjoin O (T : Set Ω)) := Ideal.span {⟨π, hπ⟩}
  have memI : ∀ z : Algebra.adjoin O (T : Set Ω), z ∈ I ↔
      (z : Ω) / π ∈ Algebra.adjoin O (T : Set Ω) := by
    intro z
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, rfl⟩
      show ((w : Ω) * π) / π ∈ _
      rw [mul_div_cancel_right₀ _ hπ0]
      exact w.2
    · intro h
      exact ⟨⟨(z : Ω) / π, h⟩, Subtype.ext (div_mul_cancel₀ _ hπ0)⟩
  have hvI : ∀ z : Algebra.adjoin O (T : Set Ω), z ∈ I → v z < 1 := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    show v ((w : Ω) * π) < 1
    rw [map_mul]
    calc v w * v π ≤ 1 * v π := mul_le_mul_of_nonneg_right (hint _ w.2) zero_le
      _ < 1 := by rw [one_mul]; exact hvπ
  have hpI : (p : Algebra.adjoin O (T : Set Ω)) ∈ I := by
    rw [memI]
    simpa using hpπ
  haveI hmaxI := hmax
  letI hk : Field (O ⧸ Ideal.span {(p : O)}) := Ideal.Quotient.field _
  haveI : CharP (O ⧸ Ideal.span {(p : O)}) p :=
    CharP.quotient O p (fun hu => hmax.ne_top (Ideal.span_singleton_eq_top.2 hu))
  let φ : (O ⧸ Ideal.span {(p : O)}) →+* Algebra.adjoin O (T : Set Ω) ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (algebraMap O _)) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
      exact I.mul_mem_left _ hpI)
  letI : Algebra (O ⧸ Ideal.span {(p : O)}) (Algebra.adjoin O (T : Set Ω) ⧸ I) := φ.toAlgebra
  haveI hnt : Nontrivial (Algebra.adjoin O (T : Set Ω) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by
    intro h
    have h1 : (1 : Algebra.adjoin O (T : Set Ω)) ∈ I := by rw [h]; exact Submodule.mem_top
    have := hvI 1 h1
    simp at this)
  haveI : IsLocalRing (Algebra.adjoin O (T : Set Ω) ⧸ I) := by
    refine { toNontrivial := hnt, isUnit_or_isUnit_of_add_one := ?_ }
    intro a b hab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hxy : x + y - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), hab, map_one, sub_self]
    have hv1 := hvI _ hxy
    have key : v x = 1 ∨ v y = 1 := by
      by_contra hcon
      push_neg at hcon
      have hx' : v x < 1 := lt_of_le_of_ne (hint _ x.2) hcon.1
      have hy' : v y < 1 := lt_of_le_of_ne (hint _ y.2) hcon.2
      have e1 : (1 : Ω) = ((x : Ω) + y) - ((x + y - 1 : Algebra.adjoin O (T : Set Ω)) : Ω) := by
        push_cast
        ring
      have : v (1 : Ω) < 1 := by
        rw [e1]
        exact lt_of_le_of_lt (v.map_sub _ _)
          (max_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt hx' hy')) hv1)
      simp at this
    rcases key with h | h
    · obtain ⟨w, hw, hxw⟩ := hunit _ x.2 h
      left
      have e : x * ⟨w, hw⟩ = 1 := Subtype.ext hxw
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I ⟨w, hw⟩) ?_
      rw [← map_mul, e, map_one]
    · obtain ⟨w, hw, hyw⟩ := hunit _ y.2 h
      right
      have e : y * ⟨w, hw⟩ = 1 := Subtype.ext hyw
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I ⟨w, hw⟩) ?_
      rw [← map_mul, e, map_one]
  let T' : Finset (Algebra.adjoin O (T : Set Ω) ⧸ I) :=
    T.attach.image (fun t => Ideal.Quotient.mk I ⟨t.1, Algebra.subset_adjoin (Finset.mem_coe.2 t.2)⟩)
  have hgen0 : ∀ x (hx : x ∈ Algebra.adjoin O (T : Set Ω)),
      Ideal.Quotient.mk I ⟨x, hx⟩ ∈ Algebra.adjoin (O ⧸ Ideal.span {(p : O)})
        (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I)) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem t ht =>
      apply Algebra.subset_adjoin
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩
    | algebraMap r =>
      convert Subalgebra.algebraMap_mem
        (Algebra.adjoin (O ⧸ Ideal.span {(p : O)}) (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I)))
        (Ideal.Quotient.mk (Ideal.span {(p : O)}) r) using 1
      rfl
    | add x y hx hy ihx ihy =>
      have e : (⟨x + y, add_mem hx hy⟩ : Algebra.adjoin O (T : Set Ω)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, map_add (f := _)]
      exact add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      have e : (⟨x * y, mul_mem hx hy⟩ : Algebra.adjoin O (T : Set Ω)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul]
      exact mul_mem ihx ihy
  have hgen : Algebra.adjoin (O ⧸ Ideal.span {(p : O)})
      (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I)) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hgen0 x hx
  have hfrob : ∀ t ∈ T', t ^ p ^ f = t := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨⟨t0, ht0⟩, -, rfl⟩ := ht
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, memI]
    simpa using hstep t0 ht0
  obtain ⟨hfield, hroot⟩ := GlobalTheory.T.isField_and_pthRoots_of_localAlg_frobenius_fixed p (O ⧸ Ideal.span {(p : O)})
    (Algebra.adjoin O (T : Set Ω) ⧸ I) T' f hf hgen hfrob
  have hzero : ∀ z : Algebra.adjoin O (T : Set Ω), v z < 1 → z ∈ I := by
    intro z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    by_contra hne
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : z * w - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]
    have h2 := hvI _ h1
    have h3 : v ((z : Ω) * w) < 1 := by
      rw [map_mul]
      calc v z * v w ≤ v z * 1 := mul_le_mul_of_nonneg_left (hint _ w.2) zero_le
        _ < 1 := by rw [mul_one]; exact hz
    have e1 : (1 : Ω) = (z : Ω) * w - ((z * w - 1 : Algebra.adjoin O (T : Set Ω)) : Ω) := by
      push_cast
      ring
    have : v (1 : Ω) < 1 := by
      rw [e1]
      exact lt_of_le_of_lt (v.map_sub _ _) (max_lt h3 h2)
    simp at this
  refine ⟨fun x hx hvx => (memI ⟨x, hx⟩).1 (hzero _ hvx), ?_⟩
  intro y hy a hva
  have hI : (⟨y, hy⟩ : Algebra.adjoin O (T : Set Ω)) ^ p - algebraMap O _ a ∈ I :=
    hzero _ (by simpa using hva)
  have heq : (Ideal.Quotient.mk I ⟨y, hy⟩) ^ p =
      algebraMap (O ⧸ Ideal.span {(p : O)}) _ (Ideal.Quotient.mk _ a) := by
    have h0 := (Ideal.Quotient.eq_zero_iff_mem).2 hI
    rw [map_sub, map_pow] at h0
    exact sub_eq_zero.1 h0
  obtain ⟨b', hb'⟩ := hroot _ _ heq
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  refine ⟨b, ?_⟩
  have h5 : (⟨y, hy⟩ : Algebra.adjoin O (T : Set Ω)) - algebraMap O _ b ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hb', sub_eq_zero]
    rfl
  simpa using hvI _ h5

theorem q_not_pow_mod (p : ℕ) [hp : Fact p.Prime] (a : O0 p) : ¬ (p : O0 p) ∣ a ^ p - qO p := by
  intro h
  obtain ⟨e, he⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  rcases h with ⟨c, hc⟩
  have hmem : a ^ p - qO p ∈ Ideal.span {(p : O0 p)} :=
    Ideal.mem_span_singleton'.2 ⟨c, by simpa [mul_comm] using hc.symm⟩
  have h1 := (Ideal.Quotient.eq_zero_iff_mem).2 hmem
  have h2 : Ideal.Quotient.mk (Ideal.span {(p : O0 p)}) (a ^ p) -
      Ideal.Quotient.mk (Ideal.span {(p : O0 p)}) (qO p) = 0 := by
    simpa only [RingHom.map_sub] using h1
  have h1 : (Ideal.Quotient.mk (Ideal.span {(p : O0 p)}) a) ^ p =
      Ideal.Quotient.mk (Ideal.span {(p : O0 p)}) (qO p) := by
    simpa only [RingHom.map_pow] using sub_eq_zero.mp h2
  have h2 := congrArg e h1
  rw [map_pow, he] at h2
  have h3 := congrArg HahnSeries.order h2
  rw [HahnSeries.order_pow, HahnSeries.order_single one_ne_zero, nsmul_eq_mul] at h3
  have h4 : (p : ℤ) ∣ 1 := Dvd.intro _ h3
  exact hp.out.not_dvd_one (by exact_mod_cast h4)

theorem not_pow_mod_max : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgZp (p := p) s) →
  ∀ y ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)), IsInt (p := p) y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω)) := by
  intro p _ Ω _ _ hclo S hS y hy hyint
  rintro ⟨m, hm, hmint⟩
  classical
  haveI := Basic.charZero_of_isClo hclo
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have huni := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal := by
    rw [← huni]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [huni]
    exact GlobalTheory.T.unramified_integers_adic_complete p
  have := hclo.alg
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr
    (O0 p) Ω hclo.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hvp0 : 0 < v (p : Ω) := (Valuation.pos_iff v).2 hp0
  have hvp1 : v (p : Ω) < 1 := by
    have hpint : IsIntegral (O0 p) (p : Ω) := by
      simpa only [map_natCast] using
        (isIntegral_algebraMap (A := Ω) (x := (p : O0 p)))
    refine lt_of_le_of_ne ((hv _).2 hpint) ?_
    intro heq
    have hinv : IsInt (p := p) ((p : Ω)⁻¹) := (hv _).1 (by rw [map_inv₀, heq, inv_one])
    exact Basic.not_cong_one_zero hclo 1 one_ne_zero
      ⟨(p : Ω)⁻¹, hinv, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  letI : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap ℤ_[p] Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have e := PadicInt.unitCoeff_spec hx0
    rw [e, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h | h
    · exact ((Units.isUnit _).map (algebraMap ℤ_[p] Ω)).ne_zero h
    · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h
  have hvint : ∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1 := fun x hx =>
    (hv x).2 (IsIntegral.tower_top (A := O0 p) hx)
  have hSalg : ∀ s ∈ S, IsAlgebraic ℤ_[p] s := by
    intro s hs
    obtain ⟨P, hP0, hP⟩ := hS s hs
    exact ⟨P, hP0, by rwa [Polynomial.aeval_map_algebraMap] at hP⟩
  obtain ⟨R, hRfin, hRpid, hRS⟩ := GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions p Ω hinj S hSalg
  obtain ⟨π, hπR, hπ0, hvπ, hpπ, f, hf, hstep⟩ :=
    GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr p Ω hinj v hvint hvp1 R hRfin hRpid
  have hfg : (Subalgebra.toSubmodule R).FG := Module.Finite.iff_fg.1 hRfin
  obtain ⟨T, hT⟩ := Subalgebra.fg_of_fg_toSubmodule hfg
  have hRB : ∀ x ∈ R, x ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
    intro x hx
    have hle : Algebra.adjoin ℤ_[p] (T : Set Ω) ≤
        (Algebra.adjoin (O0 p) (T : Set Ω)).restrictScalars ℤ_[p] :=
      Algebra.adjoin_le (fun t ht => (Subalgebra.mem_restrictScalars _).2 (Algebra.subset_adjoin ht))
    rw [hT] at hle
    exact (Subalgebra.mem_restrictScalars _).1 (hle hx)
  have hTR : ∀ t ∈ T, t ∈ R := fun t ht => hT ▸ Algebra.subset_adjoin (Finset.mem_coe.2 ht)
  have hTint : ∀ t ∈ T, IsIntegral (O0 p) t := fun t ht =>
    (IsIntegral.of_mem_of_fg R hfg t (hTR t ht)).tower_top
  obtain ⟨hdiv, hres⟩ := residue_core p (O0 p) Ω hmax v hv T hTint π (hRB _ hπR) hπ0 hvπ
    (hRB _ hpπ) f hf (fun t ht => hRB _ (hstep t (hTR t ht)))
  have hBint : ∀ x ∈ Algebra.adjoin (O0 p) (T : Set Ω), v x ≤ 1 := fun x hx =>
    (hv x).2 (Algebra.adjoin_le (S := integralClosure (O0 p) Ω) (fun t ht => hTint t ht) hx)
  have hclosed := GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer (O0 p) Ω v hv _ hBint π (hRB _ hπR) hπ0 hvπ hdiv
  have hsub : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) ≤
      Subfield.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω) := by
    rw [Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ c)
    · obtain ⟨a, ha, b, hb, rfl⟩ := hRS x hx
      exact div_mem (Subfield.subset_closure (hRB _ ha)) (Subfield.subset_closure (hRB _ hb))
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.1 (hsub hy)
  have hcl : ∀ z ∈ Subring.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω),
      z ∈ Algebra.adjoin (O0 p) (T : Set Ω) := fun z hz =>
    (Subring.closure_le (t := (Algebra.adjoin (O0 p) (T : Set Ω)).toSubring)).2 (fun _ h => h) hz
  have hyv : v y ≤ 1 := (hv y).2 hyint
  have hyB : y ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
    rw [← hab]
    exact hclosed a (hcl a ha) b (hcl b hb) (by rw [hab]; exact hyv)
  have hvq : v (y ^ p - algebraMap (O0 p) Ω (qO p)) < 1 := by
    have h1 := (hv _).2 hmint
    rw [map_div₀, map_pow] at h1
    have h2 : v (y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m < 1 :=
      lt_of_le_of_lt ((div_le_one₀ hvp0).1 h1) hvp1
    by_contra hc
    push_neg at hc
    exact absurd h2 (not_lt.2 (one_le_pow₀ hc))
  obtain ⟨b, hb⟩ := hres y hyB (qO p) hvq
  have hbv : v (algebraMap (O0 p) Ω b) ≤ 1 := (hv _).2 isIntegral_algebraMap
  have hvb : v (algebraMap (O0 p) Ω (b ^ p - qO p)) < 1 := by
    have e : algebraMap (O0 p) Ω (b ^ p - qO p) = (y ^ p - algebraMap (O0 p) Ω (qO p)) -
        (y ^ p - (algebraMap (O0 p) Ω b) ^ p) := by
      rw [map_sub, map_pow]
      ring
    have hg : v (y ^ p - (algebraMap (O0 p) Ω b) ^ p) < 1 := by
      rw [← geom_sum₂_mul, map_mul]
      have hs : v (∑ i ∈ Finset.range p, y ^ i * (algebraMap (O0 p) Ω b) ^ (p - 1 - i)) ≤ 1 := by
        apply v.map_sum_le
        intro i _
        rw [map_mul, map_pow, map_pow]
        exact mul_le_one' (pow_le_one' hyv _) (pow_le_one' hbv _)
      calc _ ≤ 1 * v (y - algebraMap (O0 p) Ω b) := mul_le_mul_of_nonneg_right hs zero_le
        _ < 1 := by rw [one_mul]; exact hb
    rw [e]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hvq hg)
  apply q_not_pow_mod p b
  by_contra hnd
  have hu : IsUnit (b ^ p - qO p) := by
    by_contra hnu
    apply hnd
    have hmem : b ^ p - qO p ∈ IsLocalRing.maximalIdeal (O0 p) :=
      (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [huni] at hmem
    exact Ideal.mem_span_singleton.1 hmem
  obtain ⟨u, hu⟩ := hu
  have h1 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h2 : v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) ≤ 1 := (hv _).2 isIntegral_algebraMap
  rw [← hu] at hvb
  have h4 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) < 1 :=
    calc _ ≤ v (algebraMap (O0 p) Ω (u : O0 p)) * 1 := mul_le_mul_of_nonneg_left h2 zero_le
      _ < 1 := by rw [mul_one]; exact hvb
  rw [h1] at h4
  exact lt_irrefl _ h4

end GlobalTheory.K5.NotPow
