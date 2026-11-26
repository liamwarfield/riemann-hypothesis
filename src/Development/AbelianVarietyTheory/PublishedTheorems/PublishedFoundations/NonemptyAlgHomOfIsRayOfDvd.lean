module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwoPrimesSameNormOfTrivialFrobenius
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ForallHeckeIdealIff
noncomputable section

namespace GlobalTheory.RayFieldCompare

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals
open scoped nonZeroDivisors Pointwise

theorem ker_eq_of_submonoid {H G : Type*} [CommGroup H] [Group G] [Finite G] (M : Submonoid H)
    (hM : Subgroup.closure (M : Set H) = ⊤) (P : Subgroup H) (φ : H →* G)
    (h : ∀ m ∈ M, φ m = 1 ↔ m ∈ P) : φ.ker = P := by
  have hn : Nat.card G = (Nat.card G - 1) + 1 := (Nat.sub_add_cancel Nat.card_pos).symm
  have key : ∀ J : H, ∃ m ∈ M, φ m = φ J ∧ J⁻¹ * m ∈ P := by
    intro J
    have hJ : J ∈ Subgroup.closure (M : Set H) := hM ▸ Subgroup.mem_top J
    induction hJ using Subgroup.closure_induction with
    | mem x hx => exact ⟨x, hx, rfl, by simp⟩
    | one => exact ⟨1, M.one_mem, rfl, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, ha1, ha2⟩ := hx
      obtain ⟨b, hb, hb1, hb2⟩ := hy
      refine ⟨a * b, M.mul_mem ha hb, by rw [map_mul, map_mul, ha1, hb1], ?_⟩
      have := P.mul_mem ha2 hb2
      rwa [mul_mul_mul_comm, ← mul_inv] at this
    | inv x _ hx =>
      obtain ⟨a, ha, ha1, ha2⟩ := hx
      have h1 : φ (a ^ Nat.card G) = 1 := by rw [map_pow, pow_card_eq_one']
      have h2 := (h _ (M.pow_mem ha _)).1 h1
      refine ⟨a ^ (Nat.card G - 1), M.pow_mem ha _, ?_, ?_⟩
      · rw [map_inv, ← ha1]
        rw [hn, pow_succ, map_mul] at h1
        exact eq_inv_of_mul_eq_one_left h1
      · have := P.mul_mem (P.inv_mem ha2) h2
        rw [hn, pow_succ] at this
        convert this using 1
        rw [mul_inv, inv_inv, mul_comm (a ^ _) a, mul_assoc, inv_mul_cancel_left]
  ext J
  obtain ⟨m, hm, h1, h2⟩ := key J
  rw [MonoidHom.mem_ker, ← h1, h m hm]
  constructor
  · intro hp
    have := P.mul_mem (P.inv_mem h2) hp
    simpa using this
  · intro hp
    simpa using P.mul_mem hp h2

variable {K : Type} [Field K] [NumberField K]

theorem finite_support_zpow {A : Type*} [CommGroup A] (f : HeightOneSpectrum (𝓞 K) → A)
    (J : FractionalIdeal (𝓞 K)⁰ K) :
    Function.HasFiniteMulSupport fun 𝔭 => f 𝔭 ^ FractionalIdeal.count K 𝔭 J := by
  refine (FractionalIdeal.finite_factors J).subset ?_
  intro 𝔭 h h0
  exact h (by simp only [Set.mem_ofPred_eq] at h0; simp [h0])

def extend {A : Type*} [CommGroup A] (𝔪 : Ideal (𝓞 K)) (f : HeightOneSpectrum (𝓞 K) → A) :
    idealsPrimeTo 𝔪 →* A :=
  MonoidHom.mk' (fun J => ∏ᶠ 𝔭, f 𝔭 ^ FractionalIdeal.count K 𝔭 (J.1 : FractionalIdeal (𝓞 K)⁰ K)) (by
    intro a b
    rw [← finprod_mul_distrib (finite_support_zpow f _) (finite_support_zpow f _)]
    refine finprod_congr fun 𝔭 => ?_
    rw [Subgroup.coe_mul, Units.val_mul, FractionalIdeal.count_mul K 𝔭 a.1.ne_zero b.1.ne_zero, zpow_add])

theorem extend_primeElt {A : Type*} [CommGroup A] (𝔪 : Ideal (𝓞 K)) (f : HeightOneSpectrum (𝓞 K) → A)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ 𝔭.asIdeal ∣ 𝔪) : extend 𝔪 f (primeElt 𝔪 𝔭 h) = f 𝔭 := by
  change ∏ᶠ 𝔮, f 𝔮 ^ FractionalIdeal.count K 𝔮 (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [finprod_eq_single _ 𝔭, FractionalIdeal.count_self, zpow_one]
  intro 𝔮 hq
  rw [FractionalIdeal.count_maximal_coprime K 𝔮 hq.symm, zpow_zero]


open Classical in
def gen (𝔪 : Ideal (𝓞 K)) (𝔭 : HeightOneSpectrum (𝓞 K)) : idealsPrimeTo 𝔪 :=
  if h : ¬ 𝔭.asIdeal ∣ 𝔪 then primeElt 𝔪 𝔭 h else 1

theorem finprod_gen (𝔪 : Ideal (𝓞 K)) (J : idealsPrimeTo 𝔪) :
    ∏ᶠ 𝔭, gen 𝔪 𝔭 ^ FractionalIdeal.count K 𝔭 (J.1 : FractionalIdeal (𝓞 K)⁰ K) = J := by
  apply Subtype.ext
  apply Units.ext
  have := MonoidHom.map_finprod ((Units.coeHom _).comp (idealsPrimeTo 𝔪).subtype)
    (finite_support_zpow (gen 𝔪) (J.1 : FractionalIdeal (𝓞 K)⁰ K))
  refine this.trans ?_
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K J.1.ne_zero]
  refine finprod_congr fun 𝔭 => ?_
  by_cases h : 𝔭.asIdeal ∣ 𝔪
  · rw [J.2 𝔭 h]; simp
  · simp [gen, h, primeElt]

theorem mem_of_primeElt (𝔪 : Ideal (𝓞 K)) (S : Subgroup (idealsPrimeTo 𝔪))
    (hS : ∀ 𝔭 h, primeElt 𝔪 𝔭 h ∈ S) : S = ⊤ := by
  refine eq_top_iff.2 fun J _ => ?_
  rw [← finprod_gen 𝔪 J]
  refine finprod_induction (· ∈ S) S.one_mem (fun _ _ => S.mul_mem) fun 𝔭 => S.zpow_mem ?_ _
  by_cases h : 𝔭.asIdeal ∣ 𝔪
  · simp [gen, h]
  · simpa [gen, h] using hS 𝔭 h

def integral (𝔪 : Ideal (𝓞 K)) : Submonoid (idealsPrimeTo 𝔪) where
  carrier := {J | ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔪 ∧ (J.1 : FractionalIdeal (𝓞 K)⁰ K) = I}
  one_mem' := ⟨1, one_ne_zero, isCoprime_one_left, by simp⟩
  mul_mem' := by
    rintro a b ⟨I, hI, hI', ha⟩ ⟨J, hJ, hJ', hb⟩
    exact ⟨I * J, mul_ne_zero hI hJ, hI'.mul_left hJ', by
      rw [Subgroup.coe_mul, Units.val_mul, ha, hb, FractionalIdeal.coeIdeal_mul]⟩

theorem closure_integral (𝔪 : Ideal (𝓞 K)) :
    Subgroup.closure (integral 𝔪 : Set (idealsPrimeTo 𝔪)) = ⊤ :=
  mem_of_primeElt 𝔪 _ fun 𝔭 h => Subgroup.subset_closure
    ⟨𝔭.asIdeal, 𝔭.ne_bot, by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      have := 𝔭.isMaximal.eq_of_le hne le_sup_left
      exact h (Ideal.dvd_iff_le.2 (this ▸ le_sup_right)), rfl⟩

theorem exists_integral (𝔪 I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hc : IsCoprime I 𝔪) :
    ∃ J : idealsPrimeTo 𝔪, (J.1 : FractionalIdeal (𝓞 K)⁰ K) = I := by
  refine ⟨⟨Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hI), fun 𝔭 hp => ?_⟩, rfl⟩
  rw [Units.val_mk0, FractionalIdeal.count_coe K 𝔭 hI]
  norm_cast
  by_contra hne
  have hd : 𝔭.asIdeal ∣ I := (Associates.count_ne_zero_iff_dvd hI 𝔭.irreducible).1 hne
  exact 𝔭.prime.not_isUnit (hc.isUnit_of_dvd' hd hp)

theorem mem_rayPrincipal_iff (𝔪 I : Ideal (𝓞 K)) (J : idealsPrimeTo 𝔪)
    (hJ : (J.1 : FractionalIdeal (𝓞 K)⁰ K) = I) :
    J ∈ (rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪) ↔
      ∃ α β : 𝓞 K, RayPair 𝔪 α β ∧ I * Ideal.span {β} = Ideal.span {α} := by
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, ⟨a, b, hab, hx⟩, hxJ⟩
    refine ⟨a, b, hab, ?_⟩
    apply FractionalIdeal.coeIdeal_injective (K := K)
    simp only
    rw [FractionalIdeal.coeIdeal_mul, ← hJ, ← hxJ, coe_toPrincipalIdeal,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    exact congrArg _ hx
  · rintro ⟨a, b, hab, h⟩
    have ha : (a : K) ≠ 0 := by exact_mod_cast hab.1
    have hb : (b : K) ≠ 0 := by exact_mod_cast hab.2.1
    refine ⟨Units.mk0 ((a : K) / b) (div_ne_zero ha hb), ⟨a, b, hab, by simp [hb]⟩, ?_⟩
    apply Units.ext
    have h' := congrArg (fun I : Ideal (𝓞 K) => (I : FractionalIdeal (𝓞 K)⁰ K)) h
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at h'
    have hb' : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b) ≠ 0 := by
      simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hb
    apply mul_right_cancel₀ hb'
    rw [hJ, h', coe_toPrincipalIdeal, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    exact div_mul_cancel₀ _ hb

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

theorem exists_isFrob [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) : ∃ σ, IsFrob L 𝔭 σ := by
  haveI := 𝔭.isPrime
  obtain ⟨⟨P, hP, hl⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) 𝔭.asIdeal
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P
  refine ⟨σ, P, hP, hl, fun x => ?_⟩
  have := hσ x
  rwa [← hl.over, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] at this

theorem isFrob_unique [IsAbelianGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭)
    {σ τ : L ≃ₐ[K] L} (hσ : IsFrob L 𝔭 σ) (hτ : IsFrob L 𝔭 τ) : σ = τ := by
  obtain ⟨P, hP, hPl, hs⟩ := hσ
  obtain ⟨Q, hQ, hQl, ht⟩ := hτ
  obtain ⟨g, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal P Q (L ≃ₐ[K] L)
  have ht' : ∀ x : 𝓞 L, τ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P := by
    intro x
    have := ht (g • x)
    rwa [smul_smul, mul_comm' τ g, mul_smul, ← smul_pow', ← smul_sub, Ideal.smul_mem_pointwise_smul_iff] at this
  have : σ * τ⁻¹ = 1 := by
    refine hu _ ⟨P, hP, hPl, fun x => ?_⟩
    have := P.sub_mem (hs (τ⁻¹ • x)) (ht' (τ⁻¹ • x))
    simpa [mul_smul] using this
  exact mul_inv_eq_one.1 this

theorem heckeVal_eq [IsAbelianGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭)
    {σ : L ≃ₐ[K] L} (hσ : IsFrob L 𝔭 σ) (χ : (L ≃ₐ[K] L) →* ℂˣ) : heckeVal L χ 𝔭 = χ σ := by
  have h : (∀ σ, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ :=
    ⟨fun τ hτ => by rw [hu τ hτ, map_one], σ, hσ⟩
  rw [heckeVal, dite_eq_left h, isFrob_unique L hu h.2.choose_spec hσ]

theorem heckeIdeal_eq [IsAbelianGalois K L] (𝔪 : Ideal (𝓞 K)) (ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L))
    (hψ : ∀ 𝔭 h, UnramIn L 𝔭 ∧ IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h))) (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (J : idealsPrimeTo 𝔪) (hJ : (J.1 : FractionalIdeal (𝓞 K)⁰ K) = I) :
    heckeIdeal L χ I = χ (ψ J) := by
  have := MonoidHom.map_finprod ((Units.coeHom ℂ).comp (χ.comp ψ))
    (finite_support_zpow (gen 𝔪) (J.1 : FractionalIdeal (𝓞 K)⁰ K))
  rw [finprod_gen] at this
  refine Eq.trans ?_ this.symm
  refine finprod_congr fun 𝔭 => ?_
  have hc := FractionalIdeal.count_coe K 𝔭 hI
  rw [← hJ] at hc
  by_cases h : 𝔭.asIdeal ∣ 𝔪
  · have h0 := J.2 𝔭 h
    rw [h0]
    rw [h0, eq_comm, Nat.cast_eq_zero] at hc
    rw [zpow_zero, map_one]
    convert pow_zero _ using 2
  · rw [hc, zpow_natCast, map_pow, heckeVal_eq L (hψ 𝔭 h).1 (hψ 𝔭 h).2]
    simp [gen, h]

theorem forall_heckeIdeal_iff [IsAbelianGalois K L] (𝔪 : Ideal (𝓞 K)) (ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L))
    (hψ : ∀ 𝔭 h, UnramIn L 𝔭 ∧ IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h)))
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (J : idealsPrimeTo 𝔪) (hJ : (J.1 : FractionalIdeal (𝓞 K)⁰ K) = I) :
    (∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔ ψ J = 1 := by
  constructor
  · intro h
    by_contra hne
    letI : CommGroup (L ≃ₐ[K] L) := { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := mul_comm' }
    obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) ℂ hne
    have := h χ
    rw [heckeIdeal_eq L 𝔪 ψ hψ χ I hI J hJ] at this
    exact hχ (Units.ext this)
  · intro h χ
    rw [heckeIdeal_eq L 𝔪 ψ hψ χ I hI J hJ, h, map_one, Units.val_one]

theorem clauses_iff [IsAbelianGalois K L] (𝔪 : Ideal (𝓞 K)) :
    ((∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 → UnramIn L 𝔭) ∧
      Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 ∧ IsFrob L 𝔭 σ} = ⊤ ∧
      ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔪 →
        ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔
          ∃ α β : 𝓞 K, RayPair 𝔪 α β ∧ I * Ideal.span {β} = Ideal.span {α})) ↔
    ∃ Art : RayClassGroup 𝔪 ≃* (L ≃ₐ[K] L),
      ∀ (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ 𝔭.asIdeal ∣ 𝔪),
        UnramIn L 𝔭 ∧ IsFrob L 𝔭 (Art (primeClass 𝔪 𝔭 h)) := by
  constructor
  · rintro ⟨hu, hg, hk⟩
    letI : CommGroup (L ≃ₐ[K] L) := { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := mul_comm' }
    choose fr hfr using exists_isFrob (K := K) L
    let ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L) := extend 𝔪 fr
    have hψ : ∀ 𝔭 h, UnramIn L 𝔭 ∧ IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h)) := fun 𝔭 h =>
      ⟨hu 𝔭 h, by rw [extend_primeElt]; exact hfr 𝔭⟩
    have hker : ψ.ker = (rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪) := by
      refine ker_eq_of_submonoid (integral 𝔪) (closure_integral 𝔪) _ ψ ?_
      rintro J ⟨I, hI, hc, hJ⟩
      rw [← forall_heckeIdeal_iff L 𝔪 ψ hψ I hI J hJ, hk I hI hc, mem_rayPrincipal_iff 𝔪 I J hJ]
    have hsurj : Function.Surjective ψ := by
      rw [← MonoidHom.range_eq_top, eq_top_iff, ← hg, Subgroup.closure_le]
      rintro σ ⟨𝔭, h, hσ⟩
      exact ⟨primeElt 𝔪 𝔭 h, isFrob_unique L (hu 𝔭 h) (hψ 𝔭 h).2 hσ⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj), hψ⟩
  · rintro ⟨Art, h⟩
    let ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L) := Art.toMonoidHom.comp (QuotientGroup.mk' _)
    have hψ : ∀ 𝔭 h, UnramIn L 𝔭 ∧ IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h)) := h
    refine ⟨fun 𝔭 hp => (h 𝔭 hp).1, ?_, fun I hI hc => ?_⟩
    · have := mem_of_primeElt 𝔪 ((Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K),
        ¬ 𝔭.asIdeal ∣ 𝔪 ∧ IsFrob L 𝔭 σ}).comap ψ) fun 𝔭 hp => Subgroup.subset_closure ⟨𝔭, hp, (hψ 𝔭 hp).2⟩
      refine eq_top_iff.2 fun σ _ => ?_
      obtain ⟨c, rfl⟩ := Art.surjective σ
      obtain ⟨J, rfl⟩ := QuotientGroup.mk_surjective c
      exact (this ▸ Subgroup.mem_top J : J ∈ Subgroup.comap ψ _)
    · obtain ⟨J, hJ⟩ := exists_integral 𝔪 I hI hc
      rw [forall_heckeIdeal_iff L 𝔪 ψ hψ I hI J hJ, ← mem_rayPrincipal_iff 𝔪 I J hJ,
        ← QuotientGroup.eq_one_iff]
      exact Art.map_eq_one_iff

theorem rayField_iff : GlobalTheory.NT.RayField ↔ GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.RayField := by
  refine forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun 𝔪 =>
    forall_congr' fun _ => exists_congr fun L => exists_congr fun _ => exists_congr fun _ =>
    exists_congr fun _ => ?_
  exact ⟨fun ⟨i, h⟩ => ⟨i, (clauses_iff L 𝔪).1 h⟩, fun ⟨i, h⟩ => ⟨i, (clauses_iff L 𝔪).2 h⟩⟩

end GlobalTheory.RayFieldCompare

end
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.FieldSize

namespace GlobalTheory.Published

def RayClassFieldSt : Prop := GlobalTheory.NT.RayField

theorem rayClassFieldSt_iff_artinIso : RayClassFieldSt ↔
    ∀ (K : Type) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L), IsAbelianGalois K L ∧
        ∃ Art : GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.RayClassGroup 𝔪 ≃* (L ≃ₐ[K] L),
          ∀ (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ 𝔭.asIdeal ∣ 𝔪),
            UnramIn L 𝔭 ∧ IsFrob L 𝔭 (Art (GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeClass 𝔪 𝔭 h)) :=
  GlobalTheory.RayFieldCompare.rayField_iff

theorem rayClassFieldSt_iff_isRayField : RayClassFieldSt ↔
    ∀ (K : Type) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L), GlobalTheory.Mem.Fld.IsRayField K L 𝔪 :=
  GlobalTheory.Mem.Fld.rayField_iff

def RayClassFieldMaximalSt : Prop :=
  ∀ (K L L' : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Field L'] [NumberField L'] [Algebra K L'] [IsAbelianGalois K L'] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → IsRay L 𝔪 →
    (∀ χ : (L' ≃ₐ[K] L') →* ℂˣ, IsModulus L' χ 𝔪) → Nonempty (L' →ₐ[K] L)

end GlobalTheory.Published

namespace GlobalTheory.RayMaximal

open GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.RayFieldCompare

variable {K : Type} [Field K] [NumberField K]

theorem eq_of_forall_char {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    {σ τ : L ≃ₐ[K] L} (h : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, χ σ = χ τ) : σ = τ := by
  by_contra hne
  letI : CommGroup (L ≃ₐ[K] L) := { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := mul_comm' }
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) ℂ
    (mt mul_inv_eq_one.1 hne)
  exact hχ (by rw [map_mul, map_inv, h χ, mul_inv_cancel])

theorem unramIn_of_isModulus {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    {𝔪 : Ideal (𝓞 K)} (h : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, IsModulus L χ 𝔪) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hp : ¬ 𝔭.asIdeal ∣ 𝔪) : UnramIn L 𝔭 := fun σ hσ => eq_of_forall_char fun χ => by
  by_contra hne
  exact (h χ).2.1 𝔭 hp (heckeVal_eq_zero L χ 𝔭 fun H => hne (by rw [H σ hσ, map_one]))

theorem isModulus_of_isRay {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    {𝔪 𝔫 : Ideal (𝓞 K)} (h : IsRay L 𝔪) (hd : 𝔪 ∣ 𝔫) (hn : 𝔫 ≠ ⊥) (χ : (L ≃ₐ[K] L) →* ℂˣ) : IsModulus L χ 𝔫 := by
  obtain ⟨Art, hA⟩ := (clauses_iff L 𝔪).1 h
  refine ⟨hn, fun 𝔭 hp => ?_, ?_⟩
  · have hp' : ¬ 𝔭.asIdeal ∣ 𝔪 := fun h => hp (h.trans hd)
    rw [heckeVal_of_unramIn L χ (hA 𝔭 hp').1 (hA 𝔭 hp').2]
    exact Units.ne_zero _
  · rintro α β ⟨ha, hb, ha', hb', hab, hpos⟩
    have ha0 : Ideal.span {α} ≠ ⊥ := by simpa using ha
    have hb0 : Ideal.span {β} ≠ ⊥ := by simpa using hb
    have hr : RayPair 𝔪 α β := ⟨ha, hb, ha'.of_isCoprime_of_dvd_right hd, hb'.of_isCoprime_of_dvd_right hd,
      Ideal.le_of_dvd hd hab, hpos⟩
    obtain ⟨A, hA'⟩ := exists_integral 𝔪 _ ha0 hr.2.2.1
    obtain ⟨B, hB'⟩ := exists_integral 𝔪 _ hb0 hr.2.2.2.1
    let ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L) := Art.toMonoidHom.comp (QuotientGroup.mk' _)
    rw [heckeIdeal_eq L 𝔪 ψ hA χ _ ha0 A hA', heckeIdeal_eq L 𝔪 ψ hA χ _ hb0 B hB']
    have : (QuotientGroup.mk B : RayClassGroup 𝔪) = QuotientGroup.mk A := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have haK : (α : K) ≠ 0 := by exact_mod_cast ha
      have hbK : (β : K) ≠ 0 := by exact_mod_cast hb
      refine ⟨Units.mk0 ((α : K) / β) (div_ne_zero haK hbK), ⟨α, β, hr, by simp [hbK]⟩, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, hA', hB', coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
      congr 1
      exact mul_div_cancel₀ _ hbK
    change ((χ (Art (QuotientGroup.mk A)) : ℂˣ) : ℂ) = χ (Art (QuotientGroup.mk B))
    rw [this]

theorem isFrob_restrictNormal {L M : Type} [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [Normal K L] {𝔭 : HeightOneSpectrum (𝓞 K)} {σ : M ≃ₐ[K] M} (h : IsFrob M 𝔭 σ) :
    IsFrob L 𝔭 (σ.restrictNormal L) := by
  obtain ⟨P, hP, hPo, hx⟩ := h
  refine ⟨P.under (𝓞 L), inferInstance, inferInstance, fun x => ?_⟩
  have h1 : algebraMap (𝓞 L) (𝓞 M) (σ.restrictNormal L • x) = σ • algebraMap (𝓞 L) (𝓞 M) x :=
    RingOfIntegers.ext (σ.restrictNormal_commutes L x)
  rw [Ideal.mem_under, map_sub, map_pow, h1]
  exact hx _

theorem unramIn_of_tower {L M : Type} [Field L] [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [IsGalois K L] [IsGalois K M] {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h : UnramIn M 𝔭) : UnramIn L 𝔭 := by
  rintro σ ⟨P, hP, hPo, hσ⟩
  have := 𝔭.isMaximal
  obtain ⟨⟨Q, hQ, hQo⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
  have hQo' : Q.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans Q P 𝔭.asIdeal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P)
  have : Q.IsMaximal := hQ.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)
  have h1 : Q.inertia (M ≃ₐ[K] M) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => h τ ⟨Q, hQ, hQo', hτ⟩
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) 𝔭.asIdeal Q
  have h3 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P
  rw [h1, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (M ≃ₐ[K] M),
    Ideal.ramificationIdx_tower P Q] at h2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[K] L), Nat.eq_one_of_mul_eq_one_right h2.symm,
    Subgroup.card_eq_one] at h3
  exact (Subgroup.eq_bot_iff_forall _).1 h3 σ hσ

theorem closure_isFrob_eq_top (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] {𝔪 : Ideal (𝓞 K)}
    (hm : 𝔪 ≠ ⊥) :
    Subgroup.closure {σ : M ≃ₐ[K] M | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 ∧ IsFrob M 𝔭 σ} = ⊤ := by
  have hS : {𝔭 : HeightOneSpectrum (𝓞 K) | 𝔭.asIdeal ∣ 𝔪}.Finite := Ideal.finite_factors hm
  refine GlobalTheory.Mem.FieldsEx.closure_frob_eq_top K M {𝔭 : HeightOneSpectrum (𝓞 K) | 𝔭.asIdeal ∣ 𝔪} hS fun F _ _ _ hF σ => ?_
  by_contra hσ
  obtain ⟨T, hT, H⟩ := GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one K F σ hσ
  choose P Q hne hP hQ hNP hNQ using fun v : {v // v ∉ {𝔭 : HeightOneSpectrum (𝓞 K) | 𝔭.asIdeal ∣ 𝔪} ∪ T} =>
    H v.1 (fun h => v.2 (Or.inr h)) (hF v.1 fun h => v.2 (Or.inl h))
  have hu : ∀ x : _ × Bool, (cond x.2 (P x.1) (Q x.1)).asIdeal.under (𝓞 K) = x.1.1.asIdeal := by
    rintro ⟨v, _ | _⟩
    exacts [(hQ v).over.symm, (hP v).over.symm]
  refine GlobalTheory.Mem.ZetaPole.not_injective_double_primes K F ({𝔭 : HeightOneSpectrum (𝓞 K) | 𝔭.asIdeal ∣ 𝔪} ∪ T) (hS.union hT) (fun x => cond x.2 (P x.1) (Q x.1))
    (fun x y h => ?_) ?_
  · have e : x.1 = y.1 := Subtype.ext (HeightOneSpectrum.ext (by rw [← hu x, ← hu y]; exact congrArg _ (congrArg _ h)))
    obtain ⟨v, a⟩ := x
    obtain ⟨w, b⟩ := y
    obtain rfl : v = w := e
    cases a <;> cases b
    exacts [rfl, absurd h.symm (hne v), absurd h (hne v), rfl]
  · rintro ⟨v, _ | _⟩
    exacts [hNQ v, hNP v]

theorem range_le {L L' M : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Field L'] [NumberField L'] [Algebra K L'] [IsAbelianGalois K L'] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] [Algebra L M] [IsScalarTower K L M] [Algebra L' M] [IsScalarTower K L' M] {𝔪 : Ideal (𝓞 K)}
    (hM : Subgroup.closure {σ : M ≃ₐ[K] M | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 ∧ IsFrob M 𝔭 σ} = ⊤)
    (h : IsRay L 𝔪) (h' : ∀ χ : (L' ≃ₐ[K] L') →* ℂˣ, IsModulus L' χ 𝔪) :
    (IsScalarTower.toAlgHom K L' M).fieldRange ≤ (IsScalarTower.toAlgHom K L M).fieldRange := by
  obtain ⟨Art, hA⟩ := (clauses_iff L 𝔪).1 h
  letI : CommGroup (L' ≃ₐ[K] L') := { (inferInstance : Group (L' ≃ₐ[K] L')) with mul_comm := mul_comm' }
  choose fr hfr using GlobalTheory.NT.exists_isFrob (K := K) L'
  let ψ' : idealsPrimeTo 𝔪 →* (L' ≃ₐ[K] L') := extend 𝔪 fr
  have hψ' : ∀ 𝔭 hp, UnramIn L' 𝔭 ∧ IsFrob L' 𝔭 (ψ' (primeElt 𝔪 𝔭 hp)) := fun 𝔭 hp =>
    ⟨unramIn_of_isModulus h' hp, by rw [extend_primeElt]; exact hfr 𝔭⟩
  let ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L) := Art.toMonoidHom.comp (QuotientGroup.mk' _)
  have key : ∀ g : M ≃ₐ[K] M, ∃ J, AlgEquiv.restrictNormalHom L g = ψ J ∧ AlgEquiv.restrictNormalHom L' g = ψ' J := by
    intro g
    have hg : g ∈ Subgroup.closure _ := hM ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨𝔭, hp, hx⟩ := hx
      exact ⟨primeElt 𝔪 𝔭 hp, isFrob_unique L (hA 𝔭 hp).1 (isFrob_restrictNormal hx) (hA 𝔭 hp).2,
        isFrob_unique L' (hψ' 𝔭 hp).1 (isFrob_restrictNormal hx) (hψ' 𝔭 hp).2⟩
    | one => exact ⟨1, by simp, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, h1, h2⟩ := hx
      obtain ⟨b, h3, h4⟩ := hy
      exact ⟨a * b, by rw [map_mul, map_mul, h1, h3], by rw [map_mul, map_mul, h2, h4]⟩
    | inv x _ hx =>
      obtain ⟨a, h1, h2⟩ := hx
      exact ⟨a⁻¹, by rw [map_inv, map_inv, h1], by rw [map_inv, map_inv, h2]⟩
  have hker : ∀ J, ψ J = 1 → ψ' J = 1 := by
    intro J hJ
    have hJ' : J ∈ (rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪) :=
      (QuotientGroup.eq_one_iff J).1 (Art.map_eq_one_iff.1 hJ)
    obtain ⟨x, ⟨α, β, hr, hx⟩, hxJ⟩ := Subgroup.mem_subgroupOf.1 hJ'
    have ha0 : Ideal.span {α} ≠ ⊥ := by simpa using hr.1
    have hb0 : Ideal.span {β} ≠ ⊥ := by simpa using hr.2.1
    obtain ⟨A, hA'⟩ := exists_integral 𝔪 _ ha0 hr.2.2.1
    obtain ⟨B, hB'⟩ := exists_integral 𝔪 _ hb0 hr.2.2.2.1
    have e : J * B = A := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Units.val_mul, hA', hB', ← hxJ, coe_toPrincipalIdeal,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.spanSingleton_mul_spanSingleton]
      exact congrArg _ hx
    have e' : ψ' A = ψ' B := eq_of_forall_char fun χ => Units.ext (by
      rw [← heckeIdeal_eq L' 𝔪 ψ' hψ' χ _ ha0 A hA', ← heckeIdeal_eq L' 𝔪 ψ' hψ' χ _ hb0 B hB']
      exact (h' χ).2.2 α β hr)
    rw [← e, map_mul] at e'
    exact mul_eq_right.1 e'
  rintro _ ⟨y, rfl⟩
  rw [← IsGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom K L M).fieldRange, IntermediateField.mem_fixedField_iff]
  intro g hg
  obtain ⟨J, h1, h2⟩ := key g
  have h3 : AlgEquiv.restrictNormalHom L g = 1 := AlgEquiv.ext fun x => (algebraMap L M).injective
    ((g.restrictNormal_commutes L x).trans ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨x, rfl⟩))
  rw [hker J (h1 ▸ h3)] at h2
  exact (g.restrictNormal_commutes L' y).symm.trans (congrArg (algebraMap L' M) (AlgEquiv.congr_fun h2 y))

end GlobalTheory.RayMaximal

namespace GlobalTheory.Published

theorem rayClassFieldMaximalSt_holds : RayClassFieldMaximalSt := by
  intro K L L' _ _ _ _ _ _ _ _ _ _ 𝔪 hm h h'
  let i : L →ₐ[K] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let j : L' →ₐ[K] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e := AlgEquiv.ofInjectiveField i
  let e' := AlgEquiv.ofInjectiveField j
  have : IsGalois K i.fieldRange := IsGalois.of_algEquiv e
  have : IsGalois K j.fieldRange := IsGalois.of_algEquiv e'
  have : FiniteDimensional K i.fieldRange := e.toLinearEquiv.finiteDimensional
  have : FiniteDimensional K j.fieldRange := e'.toLinearEquiv.finiteDimensional
  let M : IntermediateField K (AlgebraicClosure K) := i.fieldRange ⊔ j.fieldRange
  have : IsGalois K M := {}
  have : NumberField M := NumberField.of_module_finite K M
  let i' : L →ₐ[K] M := (IntermediateField.inclusion le_sup_left).comp e.toAlgHom
  let j' : L' →ₐ[K] M := (IntermediateField.inclusion le_sup_right).comp e'.toAlgHom
  let _ := i'.toRingHom.toAlgebra
  let _ := j'.toRingHom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x => (i'.commutes x).symm
  have : IsScalarTower K L' M := IsScalarTower.of_algebraMap_eq fun x => (j'.commutes x).symm
  have hle := GlobalTheory.RayMaximal.range_le (GlobalTheory.RayMaximal.closure_isFrob_eq_top M hm) h h'
  exact ⟨(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L M)).symm.toAlgHom.comp
    ((IntermediateField.inclusion hle).comp (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L' M)).toAlgHom)⟩

theorem nonempty_algHom_of_isRay_of_dvd {K L L' : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field L'] [NumberField L'] [Algebra K L']
    [IsAbelianGalois K L'] {𝔪 𝔫 : Ideal (𝓞 K)} (hn : 𝔫 ≠ ⊥) (hd : 𝔪 ∣ 𝔫) (h : IsRay L 𝔫) (h' : IsRay L' 𝔪) :
    Nonempty (L' →ₐ[K] L) :=
  rayClassFieldMaximalSt_holds K L L' 𝔫 hn h (GlobalTheory.RayMaximal.isModulus_of_isRay h' hd hn)

end GlobalTheory.Published

end
