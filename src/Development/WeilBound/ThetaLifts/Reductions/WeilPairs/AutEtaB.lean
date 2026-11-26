module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SquareOfApproximation
namespace UpperTheory.Reformulated.B.SquareOfApproximation

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Filter Topology

private lemma small_power_bound {A : Type*} [Ring A] [_i : Valued A (WithZero (Multiplicative ℤ))]
    (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ) :
    ∃ N : ℕ, ∀ x : A, Valued.v x ≤ exp (-(N : ℤ)) → _i.v.restrict x < γ.1 := by
  have hg : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = exp k :=
    ⟨log _, (exp_log hg).symm⟩
  refine ⟨(-k + 1).toNat, fun x hx => ?_⟩
  apply _i.v.restrict_lt_iff_lt_embedding.mpr
  change _i.v x < MonoidWithZeroHom.ValueGroup₀.embedding γ.1
  rw [hk]
  refine lt_of_le_of_lt hx ?_
  rw [exp_lt_exp]
  have := Int.self_le_toNat (-k + 1)
  omega

private lemma square_of_approx {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (b : ℕ → R) (d : R)
    (hb : ∀ m k, m ≤ k → b k - b m ∈ v.asIdeal ^ m)
    (hd : ∀ m, b m * b m - d ∈ v.asIdeal ^ m) :
    IsSquare (algebraMap K (v.adicCompletion K) (algebraMap R K d)) := by
  set f : ℕ → v.adicCompletion K :=
    fun m => algebraMap K (v.adicCompletion K) (algebraMap R K (b m)) with hf
  set D := algebraMap K (v.adicCompletion K) (algebraMap R K d) with hD
  have hval : ∀ (r : R) (m : ℕ), r ∈ v.asIdeal ^ m →
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ exp (-(m : ℤ)) := by
    intro r m hr
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) =
        v.valuation K (algebraMap R K r) := valuedAdicCompletion_eq_valuation' v _
    rw [h1, valuation_of_algebraMap]
    exact (intValuation_le_pow_iff_mem v r m).2 hr
  have hcau : CauchySeq f := by
    rw [CauchySeq, Valued.cauchy_iff]
    refine ⟨inferInstance, fun γ => ?_⟩
    obtain ⟨N, hN⟩ := small_power_bound γ
    refine ⟨f '' Set.Ici N, Filter.image_mem_map (Filter.mem_atTop N), ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨k, hk, rfl⟩
    apply hN
    have hm' : N ≤ m := hm
    have hk' : N ≤ k := hk
    have : b k - b m ∈ v.asIdeal ^ N := by
      rcases le_total m k with h | h
      · exact Ideal.pow_le_pow_right hm' (hb m k h)
      · have := Ideal.pow_le_pow_right hk' (hb k m h)
        rw [← neg_sub]; exact neg_mem this
    have h2 := hval _ _ this
    simpa [hf, map_sub] using h2
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  have h0 : Tendsto (fun m => f m * f m - D) atTop (𝓝 0) := by
    rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := small_power_bound γ
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    apply hN
    have := hval _ _ (Ideal.pow_le_pow_right hm (hd m))
    simpa [hf, hD, map_sub, map_mul] using this
  have h1 : Tendsto (fun m => f m * f m - D) atTop (𝓝 (L * L - D)) :=
    (hL.mul hL).sub_const D
  have h2 : L * L - D = 0 := tendsto_nhds_unique h1 h0
  exact ⟨L, (sub_eq_zero.1 h2).symm⟩

private lemma approx {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)
    (hσ : ∀ x, σ (σ x) = x)
    (htr : ∀ y, ∃ r : R, algebraMap R S r = y + σ y)
    (hnm : ∀ y, ∃ r : R, algebraMap R S r = y * σ y)
    (P Q : Ideal S) [hP : P.IsMaximal] [hQ : Q.IsMaximal] (hne : P ≠ Q)
    (hc : P.comap (algebraMap R S) = Q.comap (algebraMap R S)) (t : S) (n : ℕ) :
    ∃ a : R, t - algebraMap R S a ∈ P ^ n := by
  have hsurj : Function.Surjective σ := fun x => ⟨σ x, hσ x⟩
  have hP'max : (P.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hne' : P ≠ P.comap σ := by
    intro h
    obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q, x ∉ P := by
      by_contra hcon
      push Not at hcon
      exact hne ((hQ.eq_of_le hP.ne_top hcon).symm)
    obtain ⟨r, hr⟩ := hnm x
    have h1 : r ∈ Q.comap (algebraMap R S) := by
      rw [Ideal.mem_comap, hr]; exact Q.mul_mem_right _ hxQ
    rw [← hc, Ideal.mem_comap, hr] at h1
    rcases hP.isPrime.mem_or_mem h1 with h2 | h2
    · exact hxP h2
    · apply hxP; rw [h]; exact h2
  have hcop : IsCoprime (P ^ n) ((P.comap σ) ^ n) :=
    IsCoprime.pow ((Ideal.isCoprime_iff_sup_eq).2 (Ideal.IsMaximal.coprime_of_ne hP hP'max hne'))
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 hcop
  obtain ⟨a, ha⟩ := htr (t * q)
  refine ⟨a, ?_⟩
  have hsq : σ q ∈ P ^ n := by
    have h1 : σ q ∈ ((P.comap σ) ^ n).map σ := Ideal.mem_map_of_mem σ hq
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono (Ideal.map_comap_le) n h1
  rw [ha, map_mul]
  have h3 : t - (t * q + σ t * σ q) = t * p - σ t * σ q := by
    have : q = 1 - p := by rw [← hpq]; ring
    rw [this]; simp only [map_sub, map_one]; ring
  rw [h3]
  exact sub_mem (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hsq)

private theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {θ : E} {d : 𝓞 F} (hd : (d : F) ≠ 0) (hσ : σ θ = -θ)
    (hθ : θ * θ = algebraMap F E d)
    (hsp : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (P Q : HeightOneSpectrum (𝓞 E)) (hne : P ≠ Q)
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal)
    (hQ : Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) :
    IsSquare (algebraMap F (v.adicCompletion F) (d : F)) := by
  have hsp' : ∀ x : E, ∃ u w : F, x = algebraMap F E u + algebraMap F E w * θ := by
    intro x
    obtain ⟨u, w, h⟩ := hsp x
    exact ⟨u, w, by rw [h, Algebra.smul_def, Algebra.smul_def, mul_one]⟩
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    apply hd
    have h0 : algebraMap F E d = 0 := by rw [← hθ]; simp
    exact (map_eq_zero (algebraMap F E)).1 h0
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨u, w, rfl⟩ := hsp' x
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hσ, map_neg, mul_neg, neg_neg]
  have hfix : ∀ x, σ x = x → ∃ u : F, x = algebraMap F E u := by
    intro x hx
    obtain ⟨u, w, rfl⟩ := hsp' x
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hσ, mul_neg] at hx
    have h2 : (2 : E) * (algebraMap F E w * θ) = 0 := by
      have h3 := add_left_cancel hx
      linear_combination -h3
    have hw : w = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h two_ne_zero
      · rcases mul_eq_zero.1 h with h | h
        · exact (map_eq_zero (algebraMap F E)).1 h
        · exact absurd h hθ0
    exact ⟨u, by simp [hw]⟩
  let s : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)
  have hs : ∀ y : 𝓞 E, ((s y : 𝓞 E) : E) = σ y := fun _ => rfl
  have hss : ∀ y, s (s y) = y := by
    intro y
    apply RingOfIntegers.ext
    rw [hs, hs, hσσ]
  have hfixO : ∀ y : 𝓞 E, s y = y → ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y := by
    intro y hy
    obtain ⟨u, hu⟩ := hfix (y : E) (by rw [← hs, hy])
    have hint : IsIntegral ℤ u := by
      have h1 : IsIntegral ℤ (algebraMap F E u) := hu ▸ RingOfIntegers.isIntegral_coe y
      exact (isIntegral_algebraMap_iff ).1 h1
    refine ⟨⟨u, hint⟩, ?_⟩
    apply RingOfIntegers.ext
    exact hu.symm
  have htr : ∀ y, ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y + s y := fun y =>
    hfixO _ (by rw [map_add (f := _), hss, add_comm])
  have hnm : ∀ y, ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y * s y := fun y =>
    hfixO _ (by rw [map_mul, hss, mul_comm])
  have hint : IsIntegral ℤ θ := by
    have h1 : IsIntegral ℤ (θ ^ 2) := by
      rw [pow_two, hθ]
      exact (RingOfIntegers.isIntegral_coe d).algebraMap
    exact h1.of_pow (by norm_num)
  let t : 𝓞 E := ⟨θ, hint⟩
  have ht : t * t = algebraMap (𝓞 F) (𝓞 E) d := by
    apply RingOfIntegers.ext
    exact hθ
  have := P.isMaximal
  have := Q.isMaximal
  have hne' : P.asIdeal ≠ Q.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  choose a ha using
    approx (R := 𝓞 F) s hss htr hnm P.asIdeal Q.asIdeal hne' (hP.trans hQ.symm) t
  have : P.asIdeal.LiesOver v.asIdeal := ⟨hP.symm⟩
  have he : v.asIdeal.ramificationIdx' P.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P.asIdeal v.ne_bot
  set e := v.asIdeal.ramificationIdx' P.asIdeal with he'
  have hdown : ∀ (x : 𝓞 F) (m : ℕ), algebraMap (𝓞 F) (𝓞 E) x ∈ P.asIdeal ^ (e * m) →
      x ∈ v.asIdeal ^ m := by
    intro x m hx
    rw [← intValuation_le_pow_iff_mem] at hx ⊢
    rw [← intValuation_liesOver v P x] at hx
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P.asIdeal v.ne_bot, ← he'] at hx
    have h1 : exp (-((e * m : ℕ) : ℤ)) = (exp (-(m : ℤ))) ^ e := by
      rw [← exp_nsmul]
      congr 1
      simp
    rw [h1] at hx
    exact (pow_le_pow_iff_left₀ zero_le zero_le he).1 hx
  have hb : ∀ m k, m ≤ k → a (e * k) - a (e * m) ∈ v.asIdeal ^ m := by
    intro m k hmk
    apply hdown
    have h1 := ha (e * m)
    have h2 := Ideal.pow_le_pow_right (Nat.mul_le_mul_left e hmk) (ha (e * k))
    have h3 := sub_mem h1 h2
    have h4 : t - algebraMap (𝓞 F) (𝓞 E) (a (e * m)) - (t - algebraMap (𝓞 F) (𝓞 E) (a (e * k))) =
        algebraMap (𝓞 F) (𝓞 E) (a (e * k) - a (e * m)) := by
      rw [map_sub]; ring
    rwa [h4] at h3
  have hdd : ∀ m, a (e * m) * a (e * m) - d ∈ v.asIdeal ^ m := by
    intro m
    apply hdown
    have h1 := Ideal.mul_mem_left _ (-(t + algebraMap (𝓞 F) (𝓞 E) (a (e * m)))) (ha (e * m))
    have h2 : -(t + algebraMap (𝓞 F) (𝓞 E) (a (e * m))) * (t - algebraMap (𝓞 F) (𝓞 E) (a (e * m))) =
        algebraMap (𝓞 F) (𝓞 E) (a (e * m) * a (e * m) - d) := by
      rw [map_sub, map_mul, ← ht]; ring
    rwa [h2] at h1
  exact square_of_approx v (fun m => a (e * m)) d hb hdd

noncomputable def IsCMExt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  IsTotallyReal F ∧ IsTotallyComplex E ∧ Module.finrank F E = 2 ∧
    ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)

theorem aux2 {F E : Type} [Field F] [Field E] :
    RingHomClass (𝓞 F →+* 𝓞 E) (𝓞 F) (𝓞 E) :=
  inferInstance

noncomputable def IsSplit {F E : Type} [Field F] [Field E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ P Q : HeightOneSpectrum (𝓞 E),
    P ≠ Q ∧
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal ∧
      Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal

@[reducible] noncomputable def Fv (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : Type :=
  v.adicCompletion F

theorem main {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (_ : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd : (d : F) ≠ 0) (hσ : σ θ = -θ)
    (hθ : θ * θ = algebraMap F E d) (hsp : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsSplit (E := E) v) :
    IsSquare (algebraMap F (Fv F v) d) := by
  obtain ⟨P, Q, hne, hP, hQ⟩ := hv
  exact core σ hd hσ hθ hsp P Q hne hP hQ

end UpperTheory.Reformulated.B.SquareOfApproximation
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaA
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF

namespace PositivityTheory.ThKW.AutEtaA

section Abstract

variable {E : Type} [Field E] [NumberField E]

theorem hom_fix (Fx : HeightOneSpectrum (𝓞 E) → Prop) {G : Type} [CommGroup G]
    (w : HeightOneSpectrum (𝓞 E) → G →* WithZero (Multiplicative ℤ)) (i : Eˣ →* G) (ψ : G →* Circle)
    (lam : ℕ →* ℂ) (hi : ∀ Q k, w Q (i k) = Q.valuation E (k : E))
    (h1 : ∀ y, (∀ Q, Fx Q → w Q y = 1) → ψ y = 1)
    (h3 : ∀ P, Fx P → ∃ z, w P z = WithZero.exp (-1 : ℤ) ∧ (∀ Q, Q ≠ P → w Q z = 1) ∧ (ψ z : ℂ) = -1)
    (h5 : ∀ P : HeightOneSpectrum (𝓞 E), (Fx P →
        lam (Ideal.absNorm P.asIdeal) = -(Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)) ∧
      (¬ Fx P → lam (Ideal.absNorm P.asIdeal) = (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)))
    (u : 𝓞 E) (k : Eˣ) (hk : (k : E) = u) :
    lam (Ideal.absNorm (Ideal.span {u})) = (ψ (i k) : ℂ) * (Real.sqrt (Ideal.absNorm (Ideal.span {u})) : ℂ) := by
  let Gen : Ideal (𝓞 E) → G → Prop := fun B y =>
    ∀ Q : HeightOneSpectrum (𝓞 E), Fx Q → w Q y = WithZero.exp (-multiplicity Q.asIdeal B : ℤ)
  have gmul : ∀ {A B y z}, A ≠ ⊥ → B ≠ ⊥ → Gen A y → Gen B z → Gen (A * B) (y * z) := by
    intro A B y z hA hB hy hz Q hQ
    rw [map_mul, hy Q hQ, hz Q hQ, GlobalTheory.EtaProduct.mult_mul Q hA hB, ← WithZero.exp_add]
    push_cast
    rw [neg_add]
  have guniq : ∀ {B y z}, Gen B y → Gen B z → ψ y = ψ z := by
    intro B y z hy hz
    have := h1 (y * z⁻¹) fun Q hQ => by
      rw [map_mul, map_inv, hy Q hQ, hz Q hQ, mul_inv_cancel₀ WithZero.exp_ne_zero]
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have gspan : ∀ (u : 𝓞 E) (k : Eˣ), (k : E) = u → Gen (Ideal.span {u}) (i k) := by
    intro u k hk Q _
    have hu : u ≠ 0 := by
      rintro rfl
      exact k.ne_zero (by simpa using hk)
    rw [hi, hk, GlobalTheory.EtaProduct.val_int Q hu]
  have gone : Gen ⊤ 1 := fun Q _ => by
    rw [map_one, ← Ideal.one_eq_top, multiplicity_eq_zero_of_not_dvd Q.prime.not_dvd_one]
    simp
  have gmov : ∀ P : HeightOneSpectrum (𝓞 E), ¬ Fx P → Gen P.asIdeal 1 := fun P hP Q hQ => by
    rw [map_one, GlobalTheory.EtaProduct.mult_ne (P := P) (Q := Q) (fun h => hP (h ▸ hQ))]
    simp
  have gfix : ∀ (P : HeightOneSpectrum (𝓞 E)) z, w P z = WithZero.exp (-1 : ℤ) → (∀ Q, Q ≠ P → w Q z = 1) →
      Gen P.asIdeal z := by
    intro P z a1 a3 Q _
    by_cases hQ : Q = P
    · rw [hQ, a1, multiplicity_self (FiniteMultiplicity.of_prime_left P.prime P.ne_bot)]; simp
    · rw [a3 Q hQ, GlobalTheory.EtaProduct.mult_ne hQ]; simp
  have gprime : ∀ P : HeightOneSpectrum (𝓞 E), ∃ z, Gen P.asIdeal z := by
    intro P
    by_cases hP : Fx P
    · obtain ⟨z, a1, a3, -⟩ := h3 P hP
      exact ⟨z, gfix P z a1 a3⟩
    · exact ⟨1, gmov P hP⟩
  have gex : ∀ B : Ideal (𝓞 E), B ≠ ⊥ → ∃ z, Gen B z := by
    intro B
    induction B using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ B hB => intro _; rw [Ideal.isUnit_iff.1 hB]; exact ⟨1, gone⟩
    | h₃ C P hC hP ih =>
      intro _
      obtain ⟨a, a1⟩ := gprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
      obtain ⟨b, b1⟩ := ih hC
      exact ⟨a * b, gmul hP.ne_zero hC a1 b1⟩
  have vprime : ∀ (P : HeightOneSpectrum (𝓞 E)) y, Gen P.asIdeal y →
      lam (Ideal.absNorm P.asIdeal) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) := by
    intro P y hy
    by_cases hP : Fx P
    · obtain ⟨z, a1, a3, a4⟩ := h3 P hP
      rw [guniq hy (gfix P z a1 a3), a4, (h5 P).1 hP, neg_one_mul]
    · rw [guniq hy (gmov P hP), map_one, (h5 P).2 hP]
      simp
  have main : ∀ B : Ideal (𝓞 E), B ≠ ⊥ → ∀ y, Gen B y →
      lam (Ideal.absNorm B) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm B) : ℂ) := by
    intro B
    induction B using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ B hB =>
      intro _ y hy
      rw [Ideal.isUnit_iff.1 hB] at hy ⊢
      rw [guniq hy gone, Ideal.absNorm_top, map_one, map_one]
      simp
    | h₃ C P hC hP ih =>
      intro _ y hy
      obtain ⟨a, a1⟩ := gprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
      obtain ⟨b, b1⟩ := gex C hC
      have v1 := vprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩ a a1
      rw [guniq hy (gmul hP.ne_zero hC a1 b1), map_mul, map_mul, map_mul, v1, ih hC b b1, Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, Circle.coe_mul]
      ring
  refine main _ ?_ _ (gspan u k hk)
  rw [Ne, Ideal.span_singleton_eq_bot]
  rintro rfl
  exact k.ne_zero (by simpa using hk)

end Abstract

section Half

open GlobalTheory.SplitDetCharF

theorem exists_half_abstract' {F T T' : Type} [Field F] [NumberField F] [CommRing T] [CommRing T']
    (j : AF F →+* T) (c : T →+* T) (p : T →+* T') (δ : T) (d : 𝓞 F) (hd0 : (d : F) ≠ 0) (hinj : Function.Injective j)
    (hcj : ∀ a, c (j a) = j a) (hcδ : c δ = -δ) (hδ2 : δ * δ = j (algebraMap F (AF F) (d : F)))
    (hdec : ∀ z, ∃ a b, z = j a + j b * δ) (hinf : ∀ α, p (j (pairA F 0 α)) = 0) :
    ∃ (ε : T) (ι : Af F), ε * ε = ε ∧ ε * c ε = 0 ∧ p ε = 0 ∧ ε + c ε = j (pairA F 0 ι) ∧
      (∀ v, (evalV F v ι = 1 ∧ IsSquare (algebraMap F (Fv F v) (d : F))) ∨
        (evalV F v ι = 0 ∧ ¬ IsSquare (algebraMap F (Fv F v) (d : F)))) ∧
      ∀ e, (e * e = e ∧ e * c e = 0 ∧ ∃ v η, IsPlaceIdemF F v η ∧ e + c e = j η) →
        (ε * e = e ∧ ε * c e = 0) ∨ (ε * e = 0 ∧ ε * c e = c e) := by
  obtain ⟨s, ι, hsι⟩ := exists_sqrt_adele F d
  have hsq : ∀ v, (evalV F v ι = 1 ∧ IsSquare (algebraMap F (Fv F v) (d : F))) ∨
      (evalV F v ι = 0 ∧ ¬ IsSquare (algebraMap F (Fv F v) (d : F))) := fun v =>
    (hsι v).imp (fun h => ⟨h.1, ⟨_, h.2.symm⟩⟩) (fun h => ⟨h.1, fun ⟨r, hr⟩ => h.2.2 r hr.symm⟩)
  obtain ⟨h, hh⟩ : ∃ h : AF F, h * (2 * algebraMap F (AF F) (d : F)) = 1 := by
    have hd : (2 * (d : F)) ≠ 0 := mul_ne_zero two_ne_zero hd0
    have := congrArg (algebraMap F (AF F)) (inv_mul_cancel₀ hd)
    rw [map_mul, map_mul, map_ofNat, map_one] at this
    exact ⟨_, this⟩
  have hH : j h * (2 * j (algebraMap F (AF F) (d : F))) = 1 := by
    have := congrArg j hh
    rwa [map_mul, map_mul, map_ofNat, map_one] at this
  have hII : j (pairA _ 0 ι) * j (pairA _ 0 ι) = j (pairA _ 0 ι) := by
    rw [← map_mul, pair_mul]
    congr 2
    refine af_ext' _ fun w => ?_
    rw [map_mul]
    rcases hsι w with h | h <;> simp [h.1]
  have hIS : j (pairA _ 0 ι) * j (pairA _ 0 s) = j (pairA _ 0 s) := by
    rw [← map_mul, pair_mul]
    congr 2
    refine af_ext' _ fun w => ?_
    rw [map_mul]
    rcases hsι w with h | h
    · simp [h.1]
    · simp [h.2.1]
  have hSS : j (pairA _ 0 s) * j (pairA _ 0 s) = j (pairA _ 0 ι) * j (algebraMap F (AF F) (d : F)) := by
    rw [← map_mul, ← map_mul, pair_mul, pair_mul']
    congr 2
    refine af_ext' _ fun w => ?_
    rw [map_mul, map_mul, evalV_snd_algebraMap]
    rcases hsι w with h | h
    · rw [h.1, h.2, one_mul]
    · rw [h.1, h.2.1, zero_mul, zero_mul]
  obtain ⟨ε, hε⟩ : ∃ ε : T, ε = j h * (j (pairA _ 0 ι) * j (algebraMap F (AF F) (d : F)) - j (pairA _ 0 s) * δ) :=
    ⟨_, rfl⟩
  have hcε : c ε = j h * (j (pairA _ 0 ι) * j (algebraMap F (AF F) (d : F)) + j (pairA _ 0 s) * δ) := by
    rw [hε, map_mul, map_sub, map_mul, map_mul, hcj, hcj, hcj, hcj, hcδ]; ring
  have hinfε : p ε = 0 := by
    rw [hε, map_mul, map_sub, map_mul, map_mul, hinf, hinf]; simp
  generalize hI : j (pairA _ 0 ι) = I at hII hIS hSS hε hcε
  generalize hS : j (pairA _ 0 s) = S at hIS hSS hε hcε
  generalize hD : j (algebraMap F (AF F) (d : F)) = D at hH hSS hε hcε hδ2
  generalize hHH : j h = H at hH hε hcε
  have h2 : ε * c ε = 0 := by
    rw [hcε, hε]
    linear_combination H * H * D * D * hII - H * H * δ * δ * hSS - H * H * I * D * hδ2
  have h3 : ε + c ε = I := by
    rw [hcε, hε]
    linear_combination I * hH
  have h4 : I * ε = ε := by
    rw [hε]
    linear_combination H * D * hII - H * δ * hIS
  have h1 : ε * ε = ε := by
    linear_combination ε * h3 - h2 + h4
  refine ⟨ε, ι, h1, h2, hinfε, h3.trans hI.symm, hsq, ?_⟩
  rintro e ⟨he1, he2, v, η, ⟨α, rfl, hα1, hα0⟩, he3⟩
  obtain ⟨a, b, hab⟩ := hdec e
  have hce : c e = j a - j b * δ := by
    rw [hab, map_add (f := _), map_mul, hcj, hcj, hcδ]; ring
  have he4 : c e * c e = c e := by rw [← map_mul, he1]
  obtain ⟨B, hB⟩ : ∃ B : AF F, B = 2 * algebraMap F (AF F) (d : F) * b := ⟨_, rfl⟩
  have hjB : j B = δ * (e - c e) := by
    rw [hB, map_mul, map_mul, map_ofNat, hD, hce]
    linear_combination -δ * hab - 2 * j b * hδ2
  have hB1 : pairA _ 0 α * B = B := hinj (by
    rw [map_mul, ← he3, hjB]
    linear_combination δ * he1 - δ * he4)
  have hB2 : B * B = pairA _ 0 α * algebraMap F (AF F) (d : F) := hinj (by
    rw [map_mul, map_mul, hD, ← he3, hjB]
    linear_combination δ * δ * he1 + δ * δ * he4 - 2 * δ * δ * he2 + (e + c e) * hδ2)
  have hB3 : evalV _ v (sndA _ B) * evalV _ v (sndA _ B) = algebraMap F (Fv F v) (d : F) := by
    rw [← map_mul, ← map_mul, hB2, map_mul, map_mul, evalV_snd_algebraMap]
    change evalV _ v α * _ = _
    rw [hα1, one_mul]
  rcases hsι v with ⟨hι, hs⟩ | ⟨-, -, hn⟩
  swap
  · exact absurd hB3 (hn _)
  have hNI : (e + c e) * I = e + c e := by
    rw [he3, ← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hι, map_one]), mul_one]
  rcases mul_self_eq_mul_self_iff.1 (hB3.trans hs.symm) with hp | hp
  · right
    have : j B = (e + c e) * S := by
      rw [he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', place_ext _ hα0 hp]
    have h5 : c e = (e + c e) * ε := by
      rw [hε]
      linear_combination -H * D * hNI - H * δ * this + H * δ * hjB + H * (e - c e) * hδ2 - c e * hH
    constructor
    · linear_combination -e * h5 + (1 - ε) * he2 - ε * he1
    · linear_combination -(c e) * h5 + (1 - ε) * he4 - ε * he2
  · left
    have : j B = -((e + c e) * S) := by
      rw [he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', ← map_neg, pair_neg, ← mul_neg,
        place_ext _ hα0 (y := -s) (by rw [hp, map_neg])]
    have h5 : e = (e + c e) * ε := by
      rw [hε]
      linear_combination -H * D * hNI + H * δ * this - H * δ * hjB - H * (e - c e) * hδ2 - e * hH
    constructor
    · linear_combination -e * h5 + (1 - ε) * he1 - ε * he2
    · linear_combination -(c e) * h5 + (1 - ε) * he2 - ε * he4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_half {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (θ : E) (d : 𝓞 F) (ε : AEF F E) (ι : Af F), (d : F) ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E (d : F) ∧
      (∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ) ∧
      ε * ε = ε ∧ ε * cAF σ ε = 0 ∧ infPartF F E ε = 0 ∧ ε + cAF σ ε = algebraMap (AF F) (AEF F E) (pairA F 0 ι) ∧
      (∀ v, (evalV F v ι = 1 ∧ IsSquare (algebraMap F (Fv F v) (d : F))) ∨
        (evalV F v ι = 0 ∧ ¬ IsSquare (algebraMap F (Fv F v) (d : F)))) ∧
      ∀ e, IsSplitIdemF σ e → (ε * e = e ∧ ε * cAF σ e = 0) ∨ (ε * e = 0 ∧ ε * cAF σ e = cAF σ e) := by
  obtain ⟨θ, d, hd0, hσθ, hθθ, hdec⟩ := exists_int_basis h
  have hs : ∀ (a : AF F) (x : E), cAF σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := fun _ _ => rfl
  obtain ⟨ε, ι, h1, h2, h3, h5, h6, h4⟩ := exists_half_abstract' (algebraMap (AF F) (AEF F E)) (cAF σ) (infPartF F E)
    ((1 : AF F) ⊗ₜ[F] θ) d hd0 tensor_inj
    (fun a => by
      rw [Algebra.TensorProduct.algebraMap_apply, hs, map_one])
    (by rw [hs, hσθ, TensorProduct.tmul_neg])
    (by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hθθ, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one (A := AF F),
        TensorProduct.smul_tmul']
      congr 1
      exact (algebraMap_smul (AF F) (d : F) (1 : AF F)).symm)
    (tensor_decomp θ hdec)
    (fun α => by
      show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (algebraMap (AF F) (AEF F E) (pairA F 0 α)) = 0
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul, Algebra.algebraMap_self,
        RingHom.id_apply, show fstA F (pairA F 0 α) = 0 from rfl, TensorProduct.zero_tmul])
  exact ⟨θ, d, ε, ι, hd0, hσθ, hθθ, hdec, h1, h2, h3, h5, h6, fun e he => h4 e he⟩

end Half

end PositivityTheory.ThKW.AutEtaA

end
end

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.LiftF Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.AutEtaA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Ev


variable (F E) in
def ev (Q : HeightOneSpectrum (𝓞 E)) : AEF F E →+* Q.adicCompletion E :=
  ((evalV E Q).toRingHom.comp (GlobalTheory.LFun.finAdEquiv F E).toRingHom).comp (finPartF F E)

theorem ev_tmul (Q : HeightOneSpectrum (𝓞 E)) (a : AF F) (x : E) :
    ev F E Q (a ⊗ₜ[F] x) = complMap rfl ((sndA F a) (Q.under (𝓞 F))) * algebraMap E _ x := rfl

theorem ev_inc (Q : HeightOneSpectrum (𝓞 E)) (x : E) : ev F E Q (incAF F E x) = algebraMap E _ x := by
  have : incAF F E x = (1 : AF F) ⊗ₜ[F] x := rfl
  rw [this, ev_tmul, map_one]
  erw [map_one, one_mul]

theorem ev_alg (Q : HeightOneSpectrum (𝓞 E)) (a : AF F) :
    ev F E Q (algebraMap (AF F) (AEF F E) a) = complMap rfl ((sndA F a) (Q.under (𝓞 F))) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, ev_tmul, map_one, mul_one]


variable (F E) in
def wv (Q : HeightOneSpectrum (𝓞 E)) : (AEF F E)ˣ →* WithZero (Multiplicative ℤ) :=
  ((Valued.v (R := Q.adicCompletion E)).toMonoidWithZeroHom.toMonoidHom.comp (ev F E Q).toMonoidHom).comp
    (Units.coeHom _)

theorem wv_apply (Q : HeightOneSpectrum (𝓞 E)) (y : (AEF F E)ˣ) : wv F E Q y = Valued.v (ev F E Q y) := rfl

theorem wv_inc (Q : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    wv F E Q (Units.map (incAF F E).toMonoidHom k) = Q.valuation E (k : E) := by
  rw [wv_apply]
  change Valued.v (ev F E Q (incAF F E (k : E))) = _
  rw [ev_inc]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q (k : E)

theorem int_iff (y : AEF F E) : finPartF F E y ∈ intAEF F E ↔ ∀ Q, Valued.v (ev F E Q y) ≤ 1 :=
  GlobalTheory.LFun.mem_int_iff (finPartF F E y)

end Ev

section Fix

variable {σ : E →ₐ[F] E}


variable (σ) in
def Fx (Q : HeightOneSpectrum (𝓞 E)) : Prop := ∀ r ∈ Q.asIdeal, sgOF σ r ∈ Q.asIdeal

theorem sgOF_sgOF (h : IsCMExt F E σ) (x : 𝓞 E) : sgOF σ (sgOF σ x) = x :=
  RingOfIntegers.ext (GlobalTheory.SplitDetCharF.sig_invol h (x : E))

theorem sgOF_alg (a : 𝓞 F) : sgOF σ (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a :=
  RingOfIntegers.ext (σ.commutes (a : F))

theorem isSplit_of_not_fx (h : IsCMExt F E σ) {Q : HeightOneSpectrum (𝓞 E)} (hQ : ¬ Fx σ Q) :
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (Q.under (𝓞 F)) := by
  have hne : Q.asIdeal.comap (sgOF σ) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    intro hb
    have : sgOF σ x ∈ Q.asIdeal.comap (sgOF σ) := by
      show sgOF σ (sgOF σ x) ∈ Q.asIdeal
      rw [sgOF_sgOF h]; exact hx
    rw [hb, Ideal.mem_bot] at this
    exact hx0 (by rw [← sgOF_sgOF h x, this, map_zero])
  let Q' : HeightOneSpectrum (𝓞 E) := ⟨Q.asIdeal.comap (sgOF σ), Ideal.comap_isPrime _ _, hne⟩
  refine GlobalTheory.LFun.isSplit_iff.2 ⟨Q', Q, fun e => hQ fun r hr => ?_, ?_, rfl⟩
  · have : r ∈ Q'.asIdeal := by rw [e]; exact hr
    exact this
  · refine HeightOneSpectrum.ext ?_
    show (Q.asIdeal.comap (sgOF σ)).comap (algebraMap (𝓞 F) (𝓞 E)) = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    rw [Ideal.comap_comap]
    congr 1
    exact RingHom.ext sgOF_alg

theorem isQuad (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ) :
    GlobalTheory.QNorm.IsQuad (d : F) θ
      (AlgEquiv.ofAlgHom σ σ (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h)) (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h))) := by
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_mul, eq_comm, map_eq_zero] at hθθ
    exact hd0 hθθ
  refine ⟨fun ⟨r, hr⟩ => ?_, by rw [pow_two, hθθ], hσθ, fun x => ?_⟩
  · have h1 : θ * θ = algebraMap F E r * algebraMap F E r := by rw [hθθ, hr, map_mul]
    rcases mul_self_eq_mul_self_iff.1 h1 with h2 | h2
    · have := hσθ
      rw [h2, AlgHom.commutes] at this
      have h4 : (2 : E) * algebraMap F E r = 0 := by linear_combination this
      rcases mul_eq_zero.1 h4 with h3 | h3
      · exact two_ne_zero h3
      · exact hθ0 (h2.trans h3)
    · have := hσθ
      rw [h2, map_neg, AlgHom.commutes, neg_neg] at this
      have h4 : (2 : E) * algebraMap F E r = 0 := by linear_combination -this
      rcases mul_eq_zero.1 h4 with h3 | h3
      · exact two_ne_zero h3
      · exact hθ0 (by rw [h2, h3, neg_zero])
  · obtain ⟨u, w, e⟩ := hdec x
    exact ⟨u, w, by rw [e, Algebra.smul_def, Algebra.smul_def, mul_one]⟩

theorem not_sq_of_fx (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : Fx σ Q) : ¬ IsSquare (algebraMap F (Fv F (Q.under (𝓞 F))) (d : F)) := by
  let σe : E ≃ₐ[F] E :=
    AlgEquiv.ofAlgHom σ σ (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h)) (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h))
  let s : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (σe : E ≃+* E)
  have hs : ∀ x, ((s x : 𝓞 E) : E) = σe x := fun _ => rfl
  have hsg : ∀ x, s x = sgOF σ x := fun _ => rfl
  refine GlobalTheory.FixedPrimeNorm.not_isSquare_of_fixed (isQuad h hd0 hσθ hθθ hdec) s hs Q (le_antisymm ?_ ?_)
  · refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    show s r ∈ Q.asIdeal
    rw [hsg]; exact hQ r hr
  · intro x hx
    have : x = s (sgOF σ x) := by rw [hsg, sgOF_sgOF h]
    rw [this]
    exact Ideal.mem_map_of_mem _ (hQ x hx)

theorem sq_of_split (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) :
    IsSquare (algebraMap F (Fv F v) (d : F)) :=
  _root_.UpperTheory.Reformulated.B.SquareOfApproximation.main h hd0 hσθ hθθ hdec hv

end Fix

end PositivityTheory.ThKW.AutEtaA

end
