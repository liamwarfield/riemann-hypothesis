module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.RayNorm

open NumberField IsDedekindDomain GlobalTheory.NT
open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem heckeIdeal_prime_pow (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 K)) (f : ℕ) :
    heckeIdeal L χ (𝔮.asIdeal ^ f) = heckeVal L χ 𝔮 ^ f := by
  unfold heckeIdeal
  rw [finprod_eq_single _ 𝔮]
  · rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot)
      (HeightOneSpectrum.associates_irreducible 𝔮), Associates.count_self
      (HeightOneSpectrum.associates_irreducible 𝔮), mul_one]
  · intro 𝔭 h𝔭
    have hne : Associates.mk 𝔭.asIdeal ≠ Associates.mk 𝔮.asIdeal := by
      intro h
      apply h𝔭
      rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq] at h
      exact HeightOneSpectrum.ext h
    rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot)
      (HeightOneSpectrum.associates_irreducible 𝔭), Associates.count_eq_zero_of_ne
      (HeightOneSpectrum.associates_irreducible 𝔭) (HeightOneSpectrum.associates_irreducible 𝔮) hne,
      mul_zero, pow_zero]


omit [NumberField K] [NumberField L] in
theorem pow_smul_sub_mem (P : Ideal (𝓞 L)) {σ : L ≃ₐ[K] L} {q : ℕ} (h : ∀ x : 𝓞 L, σ • x - x ^ q ∈ P) (k : ℕ)
    (x : 𝓞 L) : σ ^ k • x - x ^ q ^ k ∈ P := by
  have h' : ∀ y : 𝓞 L, Ideal.Quotient.mk P (σ • y) = Ideal.Quotient.mk P y ^ q := fun y => by
    rw [← map_pow, Ideal.Quotient.eq]
    exact h y
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Ideal.Quotient.eq] at ih ⊢
    rw [pow_succ' σ k, mul_smul, h', ih, ← map_pow, ← pow_mul, ← pow_succ]

theorem exists_frob_pow_eq_one [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (hu : UnramIn L 𝔭)
    (P : HeightOneSpectrum (𝓞 L)) [hPo : P.asIdeal.LiesOver 𝔭.asIdeal] {f : ℕ}
    (hf : Ideal.absNorm P.asIdeal = Ideal.absNorm 𝔭.asIdeal ^ f) :
    ∃ σ : L ≃ₐ[K] L, IsFrob L 𝔭 σ ∧ σ ^ f = 1 := by
  unfold UnramIn at hu
  have hq : Nat.card (𝓞 K ⧸ P.asIdeal.under (𝓞 K)) = Ideal.absNorm 𝔭.asIdeal := by
    rw [← hPo.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (𝓞 L ⧸ P.asIdeal) :=
    (Ideal.absNorm_ne_zero_iff _).mp (fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P.asIdeal
  have hσ' : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P.asIdeal := fun x => by
    have h1 := hσ x
    rw [hq] at h1
    exact h1
  refine ⟨σ, ⟨P.asIdeal, P.isPrime, hPo, hσ'⟩, ?_⟩
  have hfix : ∀ x : 𝓞 L, σ ^ f • x - x ∈ P.asIdeal := fun x => by
    have h1 := pow_smul_sub_mem P.asIdeal hσ' f x
    have h2 : x ^ Ideal.absNorm 𝔭.asIdeal ^ f - x ∈ P.asIdeal := by
      let _ := Ideal.Quotient.field P.asIdeal
      have _ := Fintype.ofFinite (𝓞 L ⧸ P.asIdeal)
      rw [← hf, ← Ideal.Quotient.eq, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, FiniteField.pow_card]
    have h3 := P.asIdeal.add_mem h1 h2
    rw [sub_add_sub_cancel] at h3
    exact h3
  apply hu
  exact ⟨P.asIdeal, P.isPrime, hPo, hfix⟩

theorem exists_gen_of_ray {𝔮 I : Ideal (𝓞 K)}
    (h : ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α}) :
    ∃ π : 𝓞 K, I = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  obtain ⟨α, β, hr, hI⟩ := h
  unfold RayPair at hr
  obtain ⟨-, hβ, -, hβc, hαβ, -⟩ := hr
  have hα : α ∈ I * Ideal.span {β} := by
    rw [hI]
    exact Ideal.mem_span_singleton_self α
  obtain ⟨π, -, hπ⟩ := Submodule.mem_mul_span_singleton.mp hα
  have hb0 : Ideal.span {β} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hβ
  refine ⟨π, ?_, ?_⟩
  · apply mul_right_cancel₀ hb0
    rw [hI, Ideal.span_singleton_mul_span_singleton, hπ]
  · have hq : β * (π - 1) ∈ 𝔮 := by
      have e : β * (π - 1) = α - β := by
        rw [← hπ]
        ring
      rw [e]
      exact hαβ
    have h1 : (1 : 𝓞 K) ∈ Ideal.span {β} ⊔ 𝔮 := by
      rw [Ideal.isCoprime_iff_sup_eq.mp hβc]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e2 : π - 1 = c * (β * (π - 1)) + (π - 1) * z := by
      calc π - 1 = (π - 1) * (c * β + z) := by rw [hyz, mul_one]
        _ = c * (β * (π - 1)) + (π - 1) * z := by ring
    rw [e2]
    exact 𝔮.add_mem (𝔮.mul_mem_left c hq) (𝔮.mul_mem_left (π - 1) hz)

private theorem pow_residue_degree_eq_one_of_isFrobenius [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (hu : UnramIn L 𝔭)
    (Q : Ideal (𝓞 L)) [hQ : Q.IsPrime] [hQo : Q.LiesOver 𝔭.asIdeal] {f : ℕ}
    (hQf : Ideal.absNorm Q = Ideal.absNorm 𝔭.asIdeal ^ f) (τ : L ≃ₐ[K] L)
    (hτ : ∀ x : 𝓞 L, τ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q) : τ ^ f = 1 := by
  unfold UnramIn at hu
  have hN0 : Ideal.absNorm Q ≠ 0 := by
    rw [hQf]
    exact pow_ne_zero f (fun h0 => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  have hQ0 : Q ≠ ⊥ := fun h0 => hN0 (Ideal.absNorm_eq_zero_iff.mpr h0)
  have hfin : Finite (𝓞 L ⧸ Q) := (Ideal.absNorm_ne_zero_iff _).mp hN0
  haveI : Q.IsMaximal := hQ.isMaximal hQ0
  have hfix : ∀ x : 𝓞 L, τ ^ f • x - x ∈ Q := fun x => by
    have h1 := pow_smul_sub_mem Q hτ f x
    have h2 : x ^ Ideal.absNorm 𝔭.asIdeal ^ f - x ∈ Q := by
      let _ := Ideal.Quotient.field Q
      have _ := Fintype.ofFinite (𝓞 L ⧸ Q)
      rw [← hQf, ← Ideal.Quotient.eq, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, FiniteField.pow_card]
    have h3 := Q.add_mem h1 h2
    rw [sub_add_sub_cancel] at h3
    exact h3
  exact hu _ ⟨Q, hQ, hQo, hfix⟩

theorem containsRayField_of_ray [IsGalois K L] (n : ℕ)
    (hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} → UnramIn L 𝔭)
    (hart : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I (Ideal.span {(n : 𝓞 K)}) →
      (∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) →
        ∃ α β : 𝓞 K, RayPair (Ideal.span {(n : 𝓞 K)}) α β ∧ I * Ideal.span {β} = Ideal.span {α}) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap K L) n := by
  intro 𝔓 h𝔓
  haveI := 𝔓.isPrime
  have hN : ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 K) ∈
      𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap K L)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap K L)) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hN
    have h2 := congrArg (algebraMap (𝓞 K) K) hN
    rw [map_natCast, map_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h2
    exact 𝔓.ne_bot h2
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨_, inferInstance, hne⟩
  haveI : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := ⟨rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f, f = 𝔓.asIdeal.inertiaDeg (𝓞 K) := ⟨_, rfl⟩
  have hf : Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal ^ f := by
    rw [hfdef, Ideal.absNorm_pow_inertiaDeg]
  have hn𝔭 : ((n : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro h
    apply h𝔓
    have h' : (RingOfIntegers.mapRingHom (algebraMap K L)) (n : 𝓞 K) ∈ 𝔓.asIdeal := h
    rwa [map_natCast] at h'
  have hu : UnramIn L 𝔭 := hun 𝔭 (fun h => hn𝔭 (Ideal.dvd_span_singleton.mp h))
  have hcop1 : IsCoprime 𝔭.asIdeal (Ideal.span {(n : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne2
    have e := (𝔭.isMaximal).eq_of_le hne2 le_sup_left
    have h2 : (n : 𝓞 K) ∈ 𝔭.asIdeal ⊔ Ideal.span {(n : 𝓞 K)} :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← e] at h2
    exact hn𝔭 h2
  have hI0 : 𝔭.asIdeal ^ f ≠ ⊥ := pow_ne_zero f 𝔭.ne_bot
  have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ (𝔭.asIdeal ^ f) = 1 := by
    intro χ
    rw [heckeIdeal_prime_pow]
    obtain ⟨σ0, hσ0, -⟩ := exists_frob_pow_eq_one 𝔭 hu 𝔓 hf
    have hc : (∀ σ : L ≃ₐ[K] L, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ :=
      ⟨fun σ hσ => by rw [hu σ hσ, map_one], ⟨σ0, hσ0⟩⟩
    unfold heckeVal
    rw [dite_eq_left hc]
    obtain ⟨Q, hQp, hQo, hQ⟩ := hc.2.choose_spec
    have hQf : Ideal.absNorm Q = Ideal.absNorm 𝔭.asIdeal ^ f := by
      rw [hfdef, Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal 𝔓.asIdeal Q (L ≃ₐ[K] L),
        Ideal.absNorm_pow_inertiaDeg]
    have hτ := pow_residue_degree_eq_one_of_isFrobenius 𝔭 hu Q hQf _ hQ
    have hχτ : χ hc.2.choose ^ f = 1 := by rw [← map_pow, hτ, map_one]
    rw [← Units.val_pow_eq_pow_val, hχτ, Units.val_one]
  obtain ⟨α, β, hr, hI⟩ := hart (𝔭.asIdeal ^ f) hI0 hcop1.pow_left hχ
  obtain ⟨π, hπ, hπ1⟩ := exists_gen_of_ray ⟨α, β, hr, hI⟩
  exact ⟨f, π, hf, hπ, Ideal.mem_span_singleton.mp hπ1⟩

end GlobalTheory.FieldSize.RayNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldComp
open NumberField IsDedekindDomain

namespace GlobalTheory.RayDescent

theorem dvd_intNorm_sub_one (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (n : ℕ)
    (a : 𝓞 E) (h : (n : 𝓞 E) ∣ a - 1) : (n : 𝓞 K) ∣ Algebra.intNorm (𝓞 K) (𝓞 E) a - 1 := by
  classical
  obtain ⟨c, hc⟩ := h
  have ha : a = 1 + n * c := by rw [← hc]; ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha]
  let F := AlgebraicClosure E
  let r : (E →ₐ[K] F) → (𝓞 E →+* 𝓞 F) := fun σ => RingOfIntegers.mapRingHom (σ : E →+* F)
  have hd : (n : 𝓞 F) ∣ (∏ σ : E →ₐ[K] F, r σ a) - 1 := by
    have : ∀ s : Finset (E →ₐ[K] F), (n : 𝓞 F) ∣ (∏ σ ∈ s, r σ a) - 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert σ s hσ ih =>
        rw [Finset.prod_insert hσ]
        obtain ⟨d, hd⟩ := ih
        refine ⟨r σ a * d + r σ c, ?_⟩
        have h1 : r σ a = 1 + n * r σ c := by rw [ha]; simp
        have h2 : ∏ σ ∈ s, r σ a = 1 + n * d := by rw [← hd]; ring
        rw [h2, h1]; ring
    exact this _
  obtain ⟨d, hd⟩ := hd
  set N := Algebra.intNorm (𝓞 K) (𝓞 E) a with hN
  have hNK : (N : K) = Algebra.norm K (a : E) := Algebra.algebraMap_intNorm (L := E) a
  have hprod : algebraMap K F (N : K) = 1 + n * (d : F) := by
    rw [hNK, Algebra.norm_eq_prod_embeddings K F]
    have := congrArg (algebraMap (𝓞 F) F) hd
    rw [map_sub, map_prod, map_one, map_mul, map_natCast] at this
    rw [← this]
    simp [r]
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
  have hy : algebraMap K F (((N : K) - 1) / n) = d := by
    rw [map_div₀, map_sub, hprod, map_one, map_natCast]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hnF]
  have hint : IsIntegral ℤ (((N : K) - 1) / n) := by
    rw [← isIntegral_algebraMap_iff (B := F), hy]
    exact d.isIntegral_coe
  obtain ⟨y, hy'⟩ : ∃ y : 𝓞 K, (y : K) = ((N : K) - 1) / n := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨y, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 K) K (N - 1) = algebraMap (𝓞 K) K (n * y)
  rw [map_sub, map_mul, map_one, map_natCast]
  change (N : K) - 1 = n * (y : K)
  rw [hy', mul_div_cancel₀ _ hnK]

theorem containsRayField_comp (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Field L] [NumberField L]
    (φ : K →+* E) (ψ : E →+* L) (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField ψ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (ψ.comp φ) n := by
  intro P hP
  obtain ⟨f, α, h1, h2, h3⟩ := h P hP
  letI : Algebra K E := φ.toAlgebra
  letI : Algebra E L := ψ.toAlgebra
  have hq : P.asIdeal.comap (RingOfIntegers.mapRingHom ψ) = P.asIdeal.under (𝓞 E) := rfl
  have hp : P.asIdeal.comap (RingOfIntegers.mapRingHom (ψ.comp φ)) = (P.asIdeal.under (𝓞 E)).under (𝓞 K) := by
    ext x
    rfl
  rw [hq] at h1 h2
  rw [hp]
  haveI := P.isMaximal
  set q := P.asIdeal.under (𝓞 E)
  set p := q.under (𝓞 K)
  haveI : q.IsMaximal := inferInstance
  haveI : p.IsMaximal := inferInstance
  have hrel : Ideal.relNorm (𝓞 K) q = p ^ q.inertiaDeg (𝓞 K) := Ideal.relNorm_eq_pow_of_isMaximal q p
  refine ⟨q.inertiaDeg (𝓞 K) * f, Algebra.intNorm (𝓞 K) (𝓞 E) α, ?_, ?_, dvd_intNorm_sub_one K E n α h3⟩
  · rw [h1, pow_mul, ← map_pow Ideal.absNorm p, ← hrel, Ideal.absNorm_relNorm]
  · rw [pow_mul, ← hrel, ← map_pow, h2, Ideal.relNorm_singleton]

end GlobalTheory.RayDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompleteSplittingCompositumDegreeOnePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FrobeniusFixesOfSplitsCompletelyIntermediate
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FrobeniusFixesOfSplitsCompletelyIntermediate
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
open scoped Pointwise

namespace GlobalTheory.SplitCriterion

theorem frob_fix_of_ncard_primes_eq_finrank (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N]
    [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard
      = Module.finrank K M) (σ : N ≃ₐ[K] N) (hσ : GlobalTheory.NT.IsFrob N 𝔭 σ) : ∀ x ∈ M, σ x = x := by
  have := 𝔭.isPrime
  obtain ⟨P, hP, hPo, hx⟩ := hσ
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := hP.isMaximal hne
  have hq : Ideal.absNorm 𝔭.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.ne_bot
  have hfix : σ⁻¹ • P = P := by
    symm
    refine hPm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun x hxP => ?_
    rw [Ideal.mem_inv_pointwise_smul_iff]
    have h1 := P.add_mem (hx x) (P.pow_mem_of_mem hxP _ (Nat.pos_of_ne_zero hq))
    rw [sub_add_cancel] at h1
    exact h1
  let f : (N ≃ₐ[K] N) → Ideal (𝓞 M) := fun σ => (σ⁻¹ • P).under (𝓞 M)
  have hker : ∀ σ τ, σ⁻¹ * τ ∈ M.fixingSubgroup → f σ = f τ := by
    intro σ τ e
    have e' := (IntermediateField.mem_fixingSubgroup_iff _ _).1 e
    ext x
    simp only [f, Ideal.under, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff]
    have : (σ⁻¹ * τ) • algebraMap (𝓞 M) (𝓞 N) x = algebraMap (𝓞 M) (𝓞 N) x := by
      apply RingOfIntegers.ext
      exact e' _ (x : M).2
    rw [mul_smul, inv_smul_eq_iff] at this
    rw [this]
  have hr : Set.range f = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨inferInstance, ⟨?_⟩⟩
      simp only [f]
      rw [Ideal.under_under]
      exact Ideal.LiesOver.over
    · rintro ⟨hQ, hQo⟩
      obtain ⟨P', hP', hPo'⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 N)))
      have : P'.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans P' Q _
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 N) (N ≃ₐ[K] N) P P'
        (hPo.over.symm.trans this.over)
      exact ⟨g⁻¹, by simp only [f]; rw [inv_inv, ← hg]; exact hPo'.over.symm⟩
  have hs : (fun Q : HeightOneSpectrum (𝓞 M) => Q.asIdeal) ''
      {Q | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal} = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩
    · rintro ⟨hQ, hQo⟩
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q⟩, hQo.over.symm, rfl⟩
  rw [← Set.ncard_image_of_injective _ (fun _ _ e => HeightOneSpectrum.ext e), hs, ← hr,
    IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index, ← Nat.card_coe_set_eq] at h
  let F : (N ≃ₐ[K] N) ⧸ M.fixingSubgroup → Set.range f :=
    Quotient.lift (fun g => ⟨f g, g, rfl⟩) fun a b e =>
      Subtype.ext (hker a b (QuotientGroup.leftRel_apply.1 e))
  have hF : Function.Surjective F := by
    rintro ⟨_, g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hinj : Function.Injective F := (hF.bijective_of_nat_card_le h.ge).1
  have h1 : F (QuotientGroup.mk 1) = F (QuotientGroup.mk σ) := by
    apply Subtype.ext
    change f 1 = f σ
    simp only [f]
    rw [hfix, inv_one, one_smul]
  have h2 := QuotientGroup.eq.1 (hinj h1)
  rw [inv_one, one_mul] at h2
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h2

end GlobalTheory.SplitCriterion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FrobeniusFixesOfSplitsCompletelyIntermediateStatement
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_fixes_of_splitsCompletely_intermediate : ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K)), {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard = Module.finrank K M → ∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x := by
  first | exact @GlobalTheory.SplitCriterion.frob_fix_of_ncard_primes_eq_finrank | exact GlobalTheory.SplitCriterion.frob_fix_of_ncard_primes_eq_finrank | (intros; apply GlobalTheory.SplitCriterion.frob_fix_of_ncard_primes_eq_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompleteSplittingCompositumDegreeOnePrime
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.SplitCompositum

theorem ncard_over_congr {K M M' : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field M']
    [NumberField M'] [Algebra K M] [Algebra K M'] (e : M ≃ₐ[K] M') (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {Q : HeightOneSpectrum (𝓞 M') | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M')) = 𝔭.asIdeal}.ncard =
      {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard := by
  classical
  let φ : 𝓞 M ≃+* 𝓞 M' := NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
  have hφ : ∀ x : 𝓞 K, φ (algebraMap (𝓞 K) (𝓞 M) x) = algebraMap (𝓞 K) (𝓞 M') x := by
    intro x
    apply NumberField.RingOfIntegers.ext
    show e (algebraMap (𝓞 M) M (algebraMap (𝓞 K) (𝓞 M) x)) = algebraMap (𝓞 M') M' (algebraMap (𝓞 K) (𝓞 M') x)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) K M, IsScalarTower.algebraMap_apply (𝓞 K) K M']
    exact e.commutes _
  have hcomp : ∀ I : Ideal (𝓞 M'),
      (I.comap φ).comap (algebraMap (𝓞 K) (𝓞 M)) = I.comap (algebraMap (𝓞 K) (𝓞 M')) := by
    intro I
    ext x
    simp only [Ideal.mem_comap]
    rw [hφ]
  refine Set.ncard_congr (fun Q _ => (⟨Q.asIdeal.comap φ, Ideal.comap_isPrime φ Q.asIdeal, fun h => Q.ne_bot (by
      have h' := congrArg (Ideal.map φ) h
      rwa [Ideal.map_comap_of_surjective φ φ.surjective, Ideal.map_bot] at h')⟩ : HeightOneSpectrum (𝓞 M)))
    ?_ ?_ ?_
  · intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ ⊢
    rw [hcomp, hQ]
  · intro Q₁ Q₂ _ _ h
    apply HeightOneSpectrum.ext
    have h' := congrArg HeightOneSpectrum.asIdeal h
    exact Ideal.comap_injective_of_surjective φ φ.surjective h'
  · intro Q hQ
    refine ⟨⟨Q.asIdeal.comap φ.symm, Ideal.comap_isPrime φ.symm Q.asIdeal, fun h => Q.ne_bot (by
      have h' := congrArg (Ideal.map φ.symm) h
      rwa [Ideal.map_comap_of_surjective φ.symm φ.symm.surjective, Ideal.map_bot] at h')⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq] at hQ ⊢
      rw [← hQ, ← hcomp]
      congr 1
      ext x
      simp [Ideal.mem_comap]
    · apply HeightOneSpectrum.ext
      ext x
      simp [Ideal.mem_comap]

theorem ncard_eq_finrank_of_generated (K L M M' : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field M'] [NumberField M'] [Algebra K L] [Algebra K M] [Algebra L M'] [Algebra K M']
    [IsScalarTower K L M'] (f : M →ₐ[K] M')
    (hgen : ∀ (N : Type) [Field N] [Algebra L N] (g g' : M' →ₐ[L] N), (∀ x, g (f x) = g' (f x)) → g = g')
    (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔓 : HeightOneSpectrum (𝓞 L))
    (hover : 𝔓.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal)
    (hnorm : Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal)
    (hsplit : {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard =
      Module.finrank K M) :
    {Q : HeightOneSpectrum (𝓞 M') | Q.asIdeal.comap (algebraMap (𝓞 L) (𝓞 M')) = 𝔓.asIdeal}.ncard =
      Module.finrank L M' := by
  classical
  haveI : IsGalois K (AlgebraicClosure M') := IsAlgClosure.isGalois K _
  set N : IntermediateField K (AlgebraicClosure M') :=
    IntermediateField.normalClosure K M' (AlgebraicClosure M') with hN
  haveI : FiniteDimensional K N := normalClosure.is_finiteDimensional K M' (AlgebraicClosure M')
  haveI : IsGalois K N := IsGalois.normalClosure K M' (AlgebraicClosure M')
  haveI : IsScalarTower ℚ K N := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_ratCast (algebraMap ℚ N), eq_ratCast (algebraMap ℚ K), map_ratCast])
  haveI : FiniteDimensional ℚ N := Module.Finite.trans K N
  haveI : NumberField N := NumberField.mk
  letI : Algebra L N := ((algebraMap M' N).comp (algebraMap L M')).toAlgebra
  haveI : IsScalarTower L M' N := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap K N x = algebraMap M' N (algebraMap L M' (algebraMap K L x))
    rw [← IsScalarTower.algebraMap_apply K L M', ← IsScalarTower.algebraMap_apply K M' N])
  haveI : IsGalois L N := IsGalois.tower_top_of_isGalois K L N
  let ι : M' →ₐ[L] N := IsScalarTower.toAlgHom L M' N
  let g : M →ₐ[K] N := (IsScalarTower.toAlgHom K M' N).comp f
  have h1 : {Q : HeightOneSpectrum (𝓞 g.fieldRange) |
      Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 g.fieldRange)) = 𝔭.asIdeal}.ncard =
      Module.finrank K g.fieldRange := by
    rw [ncard_over_congr g.equivFieldRange 𝔭, hsplit]
    exact g.equivFieldRange.toLinearEquiv.finrank_eq
  have hfix1 := GlobalTheory.T.frobenius_fixes_of_splitsCompletely_intermediate K N g.fieldRange 𝔭 h1
  have hfix2 : ∀ σ : N ≃ₐ[L] N, GlobalTheory.NT.IsFrob N 𝔓 σ → ∀ x ∈ ι.fieldRange, σ x = x := by
    intro σ hσ
    have hK : GlobalTheory.NT.IsFrob N 𝔭 (σ.restrictScalars K) := by
      obtain ⟨P, hP, hPo, hx⟩ := hσ
      refine ⟨P, hP, ⟨?_⟩, ?_⟩
      · rw [← hover, hPo.over, Ideal.under, Ideal.under, Ideal.comap_comap,
          ← IsScalarTower.algebraMap_eq]
      · intro x
        rw [← hnorm]
        exact hx x
    have hM1 := hfix1 (σ.restrictScalars K) hK
    have hg : (σ.toAlgHom.comp ι) = ι := hgen N _ _ (fun x => by
      have := hM1 (g x) ⟨x, rfl⟩
      exact this)
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun h : M' →ₐ[L] N => h y) hg
  have h2 := GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix L N ι.fieldRange 𝔓 hfix2
  rw [← ncard_over_congr ι.equivFieldRange 𝔓, h2]
  exact ι.equivFieldRange.toLinearEquiv.finrank_eq.symm

theorem ncard_eq_finrank_adjoin : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] (h : K ≤ L) (S : Set ℂ) [NumberField (IntermediateField.adjoin K S)] [NumberField (IntermediateField.adjoin L S)] (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔓 : HeightOneSpectrum (𝓞 L)), 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) = 𝔭.asIdeal → Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin K S)) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 (IntermediateField.adjoin K S))) = 𝔭.asIdeal}.ncard = Module.finrank K (IntermediateField.adjoin K S) → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin L S)) | Q.asIdeal.comap (algebraMap (𝓞 L) (𝓞 (IntermediateField.adjoin L S))) = 𝔓.asIdeal}.ncard = Module.finrank L (IntermediateField.adjoin L S) := by
  intro K L _ _ h S _ _ 𝔭 𝔓 hover hnorm hsplit
  letI : Algebra K L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  letI : Algebra K (IntermediateField.adjoin L S) :=
    ((algebraMap L (IntermediateField.adjoin L S)).comp (algebraMap K L)).toAlgebra
  haveI : IsScalarTower K L (IntermediateField.adjoin L S) := IsScalarTower.of_algebraMap_eq' rfl
  have hle : IntermediateField.adjoin K S ≤ (IntermediateField.adjoin L S).restrictScalars K :=
    IntermediateField.adjoin_le_iff.mpr (fun z hz => IntermediateField.subset_adjoin L S hz)
  let f : IntermediateField.adjoin K S →ₐ[K] IntermediateField.adjoin L S :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hgen : ∀ (N : Type) [Field N] [Algebra L N] (g g' : IntermediateField.adjoin L S →ₐ[L] N),
      (∀ x, g (f x) = g' (f x)) → g = g' := by
    intro N _ _ g g' hgg
    apply IntermediateField.adjoin_algHom_ext
    intro x hx
    exact hgg ⟨x, IntermediateField.subset_adjoin K S hx⟩
  have hover' : 𝔓.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal := by
    rw [← hover]
    rfl
  exact ncard_eq_finrank_of_generated K L (IntermediateField.adjoin K S) (IntermediateField.adjoin L S) f hgen
    𝔭 𝔓 hover' hnorm hsplit

end GlobalTheory.SplitCompositum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompleteSplittingCompositumDegreeOnePrimeStatement
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completeSplitting_compositum_degreeOnePrime : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] (h : K ≤ L) (S : Set ℂ) [NumberField (IntermediateField.adjoin K S)] [NumberField (IntermediateField.adjoin L S)] (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔓 : HeightOneSpectrum (𝓞 L)), 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) = 𝔭.asIdeal → Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin K S)) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 (IntermediateField.adjoin K S))) = 𝔭.asIdeal}.ncard = Module.finrank K (IntermediateField.adjoin K S) → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin L S)) | Q.asIdeal.comap (algebraMap (𝓞 L) (𝓞 (IntermediateField.adjoin L S))) = 𝔓.asIdeal}.ncard = Module.finrank L (IntermediateField.adjoin L S) := by
  first | exact @GlobalTheory.SplitCompositum.ncard_eq_finrank_adjoin | exact GlobalTheory.SplitCompositum.ncard_eq_finrank_adjoin | (intros; apply GlobalTheory.SplitCompositum.ncard_eq_finrank_adjoin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def casOp (σ : Mx n → (H →L[ℂ] H)) {d e : ℕ} (X : Fin d → Mx n) (Y : Fin e → Mx n) (v : H) : H :=
  ∑ b, dRep σ (Y b) (dRep σ (Y b) v) - ∑ i, dRep σ (X i) (dRep σ (X i) v)

theorem sm_dRep_sq (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {v : H} (hv : Sm ε σ v) :
    Sm ε σ (dRep σ Z (dRep σ Z v)) :=
  dRep_mem (isUnit_Jm ε) hσ (dRep_mem (isUnit_Jm ε) hσ hv hZ) hZ

theorem inner_dRep_sq (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {b v : H} (hb : Sm ε σ b)
    (hv : Sm ε σ v) : ⟪b, dRep σ Z (dRep σ Z v)⟫_ℂ = ⟪dRep σ Z (dRep σ Z b), v⟫_ℂ := by
  have hv1 := dRep_mem (isUnit_Jm ε) hσ hv hZ
  have hb1 := dRep_mem (isUnit_Jm ε) hσ hb hZ
  rw [inner_dRep (isUnit_Jm ε) hσ hb hv1 hZ, inner_dRep (isUnit_Jm ε) hσ hb1 hv hZ, neg_neg]

variable {d e : ℕ} {X : Fin d → Mx n} {Y : Fin e → Mx n}

theorem sm_casOp (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) : Sm ε σ (casOp σ X Y v) :=
  (smooth (Jm ε) σ).sub_mem ((smooth (Jm ε) σ).sum_mem fun b _ => sm_dRep_sq hσ (hY b) hv)
    ((smooth (Jm ε) σ).sum_mem fun i _ => sm_dRep_sq hσ (hX i) hv)

theorem inner_casOp (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {b v : H}
    (hb : Sm ε σ b) (hv : Sm ε σ v) : ⟪b, casOp σ X Y v⟫_ℂ = ⟪casOp σ X Y b, v⟫_ℂ := by
  simp only [casOp, inner_sub_left, inner_sub_right, inner_sum, sum_inner, inner_dRep_sq hσ (hX _) hb hv,
    inner_dRep_sq hσ (hY _) hb hv]

theorem casOp_add (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {x y : H}
    (hx : Sm ε σ x) (hy : Sm ε σ y) : casOp σ X Y (x + y) = casOp σ X Y x + casOp σ X Y y := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (x + y)) = dRep σ Z (dRep σ Z x) + dRep σ Z (dRep σ Z y) :=
    fun Z hZ => Dw_add hσ (l := [Z, Z]) (by simp [hZ]) hx hy
  simp only [casOp, h _ (hX _), h _ (hY _), Finset.sum_add_distrib]
  abel

theorem casOp_smul (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) (c : ℂ)
    {x : H} (hx : Sm ε σ x) : casOp σ X Y (c • x) = c • casOp σ X Y x := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (c • x)) = c • dRep σ Z (dRep σ Z x) :=
    fun Z hZ => Dw_smul hσ (l := [Z, Z]) (by simp [hZ]) c hx
  simp only [casOp, h _ (hX _), h _ (hY _), ← Finset.smul_sum, smul_sub]

end GlobalTheory.TypeSum.CasBasis

end
end
