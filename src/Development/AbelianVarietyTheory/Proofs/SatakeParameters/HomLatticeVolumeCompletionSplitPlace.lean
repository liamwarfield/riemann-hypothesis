module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemClosureIffMapMemMatrixHomLatticeCompletion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFiel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldCompletionRingEquivOfDenseUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemPowHeightOneIdealIffDvdEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemPowHeightOneIdealIffDvdEmbedding
open NumberField IsDedekindDomain WithZero

namespace GlobalTheory

theorem ordIdeal_of_ringHom {R W : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (P : HeightOneSpectrum R) (p : W) (hp : Irreducible p) (f : R →+* W)
    (hP : ∀ x : R, x ∈ P.asIdeal ↔ p ∣ f x)
    (hd : ∀ (y : W) (n : ℕ), ∃ (x : R) (z : W), f x = y + p ^ n * z)
    (x : R) (k : ℕ) : x ∈ P.asIdeal ^ k ↔ p ^ k ∣ f x := by

  have hpp : Prime p := hp.prime
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨π, z, hπ⟩ := hd p 2
  have hπP : π ∈ P.asIdeal := (hP π).2 ⟨1 + p * z, by rw [hπ]; ring⟩
  set Q : Ideal R := Ideal.comap f (Ideal.span {p ^ k}) with hQdef
  have hQ : ∀ y : R, y ∈ Q ↔ p ^ k ∣ f y := fun y => by
    rw [hQdef, Ideal.mem_comap, Ideal.mem_span_singleton]
  have hle : P.asIdeal ^ k ≤ Q := by
    have h1 : P.asIdeal ≤ Ideal.comap f (Ideal.span {p}) := fun y hy => by
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact (hP y).1 hy
    calc P.asIdeal ^ k ≤ (Ideal.comap f (Ideal.span {p})) ^ k := Ideal.pow_right_mono h1 k
      _ ≤ Ideal.comap f ((Ideal.span {p}) ^ k) := Ideal.le_comap_pow f k
      _ = Q := by rw [Ideal.span_singleton_pow]
  obtain ⟨j, hj, hassoc⟩ := (dvd_prime_pow P.prime k).1 (Ideal.dvd_iff_le.2 hle)
  have hQj : Q = P.asIdeal ^ j := associated_iff_eq.1 hassoc
  have hjk : j = k := by
    by_contra hne
    have hjk' : j ≤ k - 1 := by omega
    have hmem : π ^ (k - 1) ∈ Q := by
      rw [hQj]
      exact Ideal.pow_le_pow_right hjk' (Ideal.pow_mem_pow hπP _)
    rw [hQ, map_pow, hπ] at hmem
    have hfac : (p + p ^ 2 * z) ^ (k - 1) = p ^ (k - 1) * (1 + p * z) ^ (k - 1) := by
      rw [← mul_pow]; ring
    have hk' : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hfac, hk'] at hmem
    have hdiv := (mul_dvd_mul_iff_left (pow_ne_zero (k - 1) hp0)).1 hmem
    have hdiv' := hpp.dvd_of_dvd_pow hdiv
    have hone : p ∣ 1 := (dvd_add_left (dvd_mul_right p z)).1 hdiv'
    exact hp.not_isUnit (isUnit_of_dvd_one hone)
  rw [← hQ, hQj, hjk]

theorem ordIdeal_of_embedding {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (x : 𝓞 E) (y : W) (k : ℕ) : ρ x = algebraMap W Qq y → (x ∈ P.asIdeal ^ k ↔ (p : W) ^ k ∣ y) := by

  intro hxy
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  choose F hF using h1
  let f : 𝓞 E →+* W :=
    { toFun := F
      map_one' := hinj (by rw [← (hF 1).1]; simp)
      map_mul' := fun a b => hinj (by
        rw [map_mul, ← (hF (a * b)).1, ← (hF a).1, ← (hF b).1]; simp)
      map_zero' := hinj (by rw [← (hF 0).1]; simp)
      map_add' := fun a b => hinj (by
        rw [map_add (f := _), ← (hF (a + b)).1, ← (hF a).1, ← (hF b).1]; simp) }
  have hfx : ∀ a : 𝓞 E, algebraMap W Qq (f a) = ρ a := fun a => ((hF a).1).symm
  have hP : ∀ a : 𝓞 E, a ∈ P.asIdeal ↔ (p : W) ∣ f a := fun a => (hF a).2
  have hd : ∀ (b : W) (n : ℕ), ∃ (a : 𝓞 E) (c : W), f a = b + (p : W) ^ n * c := by
    intro b n
    obtain ⟨a, c, hac⟩ := h2 b n
    exact ⟨a, c, hinj (by rw [hfx, hac])⟩
  have hy : f x = y := hinj (by rw [hfx, hxy])
  rw [ordIdeal_of_ringHom P (p : W) hp f hP hd x k, hy]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemPowHeightOneIdealIffDvdEmbeddingStatement
open NumberField IsDedekindDomain WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_pow_heightOneIdeal_iff_dvd_embedding : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (x : 𝓞 E) (y : W) (k : ℕ), ρ x = algebraMap W Qq y → (x ∈ P.asIdeal ^ k ↔ (p : W) ^ k ∣ y) := by
  first | exact @GlobalTheory.ordIdeal_of_embedding | exact GlobalTheory.ordIdeal_of_embedding | (intros; apply GlobalTheory.ordIdeal_of_embedding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SurjectiveAlgebraMapAdicCompletionCompleteDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SurjectiveAlgebraMapAdicCompletionCompleteDvr
open NumberField IsDedekindDomain WithZero

namespace GlobalTheory.DenseCompl

theorem exists_eq_algebraMap_of_valued_le_one {W Qq : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] {π : W}
    (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W)
    {a : v.adicCompletion Qq} (ha : Valued.v a ≤ 1) :
    ∃ L : W, a = algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq L) := by
  choose r hr using fun n : ℕ => GlobalTheory.Idele.exists_valued_sub_le v ha n
  have hle : ∀ m n : ℕ, m ≤ n → exp (-(n : ℤ)) ≤ exp (-(m : ℤ)) := fun m n h => by
    rw [exp_le_exp]; omega
  have hdiv : ∀ m n : ℕ, m ≤ n → π ^ m ∣ r n - r m := by
    intro m n hmn
    have h1 : v.valuation Qq (algebraMap W Qq (r n - r m)) ≤ exp (-(m : ℤ)) := by
      rw [← GlobalTheory.Idele.valued_algebraMap, map_sub, map_sub]
      have he : algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n)) -
          algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r m)) =
          (a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r m))) -
          (a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n))) := by ring
      rw [he]
      exact (Valuation.map_sub _ _ _).trans (max_le (hr m) ((hr n).trans (hle m n hmn)))
    obtain ⟨w, hw⟩ := (exists_eq_pow_mul_iff hπ v _ m).2 h1
    exact ⟨w, IsFractionRing.injective W Qq hw⟩
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec (f := r) (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact (dvd_sub_comm).1 (hdiv m n hmn))
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero, ← Valuation.zero_iff Valued.v]
  refine eq_zero_of_forall_le_exp fun n => ?_
  have h2 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h2
  obtain ⟨w, hw⟩ := h2
  have h3 : Valued.v (algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n - L))) ≤
      exp (-(n : ℤ)) := by
    rw [GlobalTheory.Idele.valued_algebraMap]
    exact (exists_eq_pow_mul_iff hπ v _ n).1 ⟨w, by rw [hw]⟩
  have he : a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq L) =
      (a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n))) +
      algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n - L)) := by
    rw [map_sub, map_sub]; ring
  rw [he]
  exact (Valuation.map_add _ _ _).trans (max_le (hr n) h3)

theorem surjective_algebraMap_adicCompletion : ∀ {W Qq : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (π : W)
    (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W),
    Function.Surjective (algebraMap Qq (v.adicCompletion Qq)) := by
  intro W Qq _ _ _ _ _ _ π hπ hc v a
  by_cases ha : Valued.v a ≤ 1
  · obtain ⟨L, hL⟩ := exists_eq_algebraMap_of_valued_le_one hπ hc v ha
    exact ⟨_, hL.symm⟩
  have ha0 : Valued.v a ≠ 0 := fun h => ha (h ▸ zero_le')
  set p := algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq π) with hpdef
  have hp : Valued.v p = exp (-1) := by
    rw [hpdef, GlobalTheory.Idele.valued_algebraMap, valuation_uniformiser hπ v]
  have hp0 : p ≠ 0 := fun h => exp_ne_zero (by rw [← hp, h, map_zero] : exp (-1 : ℤ) = 0)
  set m := (log (Valued.v a)).toNat
  have hva : Valued.v a = exp (log (Valued.v a)) := (exp_log ha0).symm
  have hle : Valued.v (a * p ^ m) ≤ 1 := by
    rw [map_mul, map_pow, hva, hp, ← exp_nsmul, ← exp_add, ← exp_zero, exp_le_exp]
    have := Int.self_le_toNat (log (Valued.v a))
    simp only [smul_neg, nsmul_eq_mul, mul_one]
    omega
  obtain ⟨L, hL⟩ := exists_eq_algebraMap_of_valued_le_one hπ hc v hle
  refine ⟨algebraMap W Qq L / algebraMap W Qq π ^ m, ?_⟩
  rw [map_div₀, map_pow, ← hL, ← hpdef, mul_div_cancel_right₀ _ (pow_ne_zero _ hp0)]

end GlobalTheory.DenseCompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SurjectiveAlgebraMapAdicCompletionCompleteDvrStatement
open NumberField IsDedekindDomain WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_algebraMap_adicCompletion_complete_dvr : ∀ {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (π : W) (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W), Function.Surjective (algebraMap Qq (v.adicCompletion Qq)) := by
  first | exact @GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion | exact GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion | (intros; apply GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldCompletionRingEquivOfDenseUnramified
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt
open WithZero

namespace GlobalTheory.DenseCompl

theorem completion_ringEquiv_of_dense : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (hc : IsAdicComplete (Ideal.span {(p : W)}) W) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)), ∃ φ : P.adicCompletion E ≃+* Qq, (∀ x : E, φ (algebraMap E (P.adicCompletion E) x) = ρ x) ∧ (∀ n : ℕ, IsOpen {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)}) ∧ ∀ U ∈ nhds (0 : P.adicCompletion E), ∃ n : ℕ, {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} ⊆ U := by
  intro E _ _ P W Qq _ _ _ _ _ _ p hp hc ρ h1 h2
  classical
  set v := closedPoint W
  have hint : ∀ x : 𝓞 E, v.valuation Qq (ρ x) = P.valuation E x := by
    intro x
    obtain ⟨y, hy, -⟩ := h1 x
    have hx : (x : E) = algebraMap (𝓞 E) E x := rfl
    rw [hy, hx, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    have key : ∀ k : ℕ, P.intValuation x ≤ exp (-(k : ℤ)) ↔ v.intValuation y ≤ exp (-(k : ℤ)) := by
      intro k
      rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
        asIdeal_eq_span hp v, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact GlobalTheory.T.mem_pow_heightOneIdeal_iff_dvd_embedding P p hp ρ h1 h2 x y k hy
    exact le_antisymm (le_of_forall_le_exp (P.intValuation_le_one x) fun k hk => (key k).1 hk)
      (le_of_forall_le_exp (v.intValuation_le_one y) fun k hk => (key k).2 hk)
  have hval : ∀ x : E, v.valuation Qq (ρ x) = P.valuation E x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hint a) (hint b)
  have hf : ∀ x : E, Valued.v (((algebraMap Qq (v.adicCompletion Qq)).comp ρ) x) = P.valuation E x :=
    fun x => by rw [RingHom.comp_apply, GlobalTheory.Idele.valued_algebraMap, hval]
  obtain ⟨ψ, -, hψ, hψv⟩ := exists_extension P v _ hf
  have hψW : ∀ y : W, algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq y) ∈ Set.range ψ := by
    intro y
    choose x z hxz using fun n : ℕ => h2 y n
    let u : ℕ → P.adicCompletion E := fun n => algebraMap E _ (x n : E)
    have hu : ∀ m n : ℕ, n ≤ m → Valued.v (u m - u n) ≤ exp (-(n : ℤ)) := by
      intro m n hnm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      simp only [u]
      rw [← map_sub, GlobalTheory.Idele.valued_algebraMap, ← hval, map_sub, hxz, hxz, ← map_sub]
      refine (exists_eq_pow_mul_iff hp v _ n).1 ⟨(p : W) ^ k * z (n + k) - z n, ?_⟩
      congr 1
      ring
    obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_limit P u hu
    refine ⟨t, ?_⟩
    rw [← sub_eq_zero]
    refine Valued.v.zero_iff.1 (eq_zero_of_forall_le_exp fun n => ?_)
    have e : ψ t - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq y) =
        ψ (t - u n) + algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq ((p : W) ^ n * z n)) := by
      rw [map_sub, hψ, RingHom.comp_apply, hxz, map_add (f := _), map_add (f := _)]
      ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [hψv]
      exact ht n
    · rw [GlobalTheory.Idele.valued_algebraMap]
      exact (exists_eq_pow_mul_iff hp v _ n).1 ⟨z n, rfl⟩
  have hι := GlobalTheory.T.surjective_algebraMap_adicCompletion_complete_dvr (Qq := Qq) (p : W) hp hc v
  have hsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨q, rfl⟩ := hι a
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) q
    obtain ⟨s, hs⟩ := hψW a
    obtain ⟨t, ht⟩ := hψW b
    exact ⟨s / t, by rw [map_div₀, hs, ht, map_div₀]⟩
  let eψ := RingEquiv.ofBijective ψ ⟨ψ.injective, hsurj⟩
  let eι := RingEquiv.ofBijective (algebraMap Qq (v.adicCompletion Qq))
    ⟨(algebraMap Qq (v.adicCompletion Qq)).injective, hι⟩
  have hφ : ∀ z, algebraMap Qq (v.adicCompletion Qq) ((eψ.trans eι.symm) z) = ψ z :=
    fun z => eι.apply_symm_apply (ψ z)
  have hS : ∀ (n : ℕ) (z : P.adicCompletion E),
      (∃ w : W, (eψ.trans eι.symm) z = algebraMap W Qq ((p : W) ^ n * w)) ↔ Valued.v z ≤ exp (-(n : ℤ)) := by
    intro n z
    rw [exists_eq_pow_mul_iff hp v, ← GlobalTheory.Idele.valued_algebraMap v, hφ, hψv]
  refine ⟨eψ.trans eι.symm, fun x => ?_, fun n => ?_, fun U hU => ?_⟩
  · apply (algebraMap Qq (v.adicCompletion Qq)).injective
    rw [hφ, hψ]
    rfl
  · have e : {z : P.adicCompletion E | ∃ w : W, (eψ.trans eι.symm) z = algebraMap W Qq ((p : W) ^ n * w)} =
        {z | Valued.v z ≤ exp (-(n : ℤ))} := Set.ext fun z => hS n z
    rw [e]
    exact GlobalTheory.Idele.isOpen_valued_le P (-(n : ℤ))
  · obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
    obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt
      (γ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by simp)
    refine ⟨n, fun z hz => hγ ?_⟩
    have hz' := (hS n z).1 hz
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact hz'.trans_lt hn

end GlobalTheory.DenseCompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldCompletionRingEquivOfDenseUnramifiedStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numberField_completion_ringEquiv_of_dense_unramified : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (hc : IsAdicComplete (Ideal.span {(p : W)}) W) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)), ∃ φ : P.adicCompletion E ≃+* Qq, (∀ x : E, φ (algebraMap E (P.adicCompletion E) x) = ρ x) ∧ (∀ n : ℕ, IsOpen {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)}) ∧ ∀ U ∈ nhds (0 : P.adicCompletion E), ∃ n : ℕ, {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} ⊆ U := by
  first | exact @GlobalTheory.DenseCompl.completion_ringEquiv_of_dense | exact GlobalTheory.DenseCompl.completion_ringEquiv_of_dense | (intros; apply GlobalTheory.DenseCompl.completion_ringEquiv_of_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixHomLatticeLeSpanIdealHomImage
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixHomLatticeLeSpanIdealHomImage
noncomputable section

namespace GlobalTheory.VolOnto

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

theorem exists_unit_cols {W : Type} [CommRing W] [IsLocalRing W] {k : ℕ} (G : Set (Fin k → W))
    (hG : Submodule.span W G = ⊤) :
    ∃ T : Matrix (Fin k) (Fin k) W, IsUnit T.det ∧ ∀ j, (fun i => T i j) ∈ G := by
  classical
  let r := IsLocalRing.residue W
  let red : (Fin k → W) → (Fin k → IsLocalRing.ResidueField W) := fun c i => r (c i)
  have hred : ∀ c ∈ Submodule.span W G,
      red c ∈ Submodule.span (IsLocalRing.ResidueField W) (red '' G) := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : red 0 = 0 := by ext i; simp [red]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : red (x + y) = red x + red y := by ext i; simp [red]
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : red (a • x) = r a • red x := by
        ext i
        simp only [red, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  have htop : Submodule.span (IsLocalRing.ResidueField W) (red '' G) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    choose c hc using fun i => IsLocalRing.residue_surjective (v i)
    have : red c = v := funext hc
    rw [← this]
    exact hred c (hG ▸ Submodule.mem_top)
  obtain ⟨b, hbG, hbs, hbli⟩ := exists_linearIndependent (IsLocalRing.ResidueField W) (red '' G)
  let bs := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbs, htop])
  haveI : Fintype b := Module.Basis.fintypeIndexOfRankLtAleph0 bs (by simp)
  have hcard : Fintype.card (Fin k) = Fintype.card b := by
    have := Module.finrank_eq_card_basis bs
    simpa using this
  let e : Fin k ≃ b := Fintype.equivOfCardEq hcard
  have hex : ∀ j : Fin k, ∃ c ∈ G, red c = ((e j : b) : Fin k → IsLocalRing.ResidueField W) := by
    intro j
    obtain ⟨c, hc, h⟩ := hbG (e j).2
    exact ⟨c, hc, h⟩
  choose c hcG hcr using hex
  refine ⟨Matrix.of fun i j => c j i, ?_, fun j => hcG j⟩
  let bs' := bs.reindex e.symm
  have hT : (Matrix.of fun i j => c j i : Matrix (Fin k) (Fin k) W).map r =
      (Pi.basisFun (IsLocalRing.ResidueField W) (Fin k)).toMatrix bs' := by
    ext i j
    have := congrFun (hcr j) i
    simpa [Module.Basis.toMatrix_apply, bs', bs, red] using this
  have hU : IsUnit ((Pi.basisFun (IsLocalRing.ResidueField W) (Fin k)).toMatrix bs').det :=
    Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  rw [← hT] at hU
  have h2 : r (Matrix.of fun i j => c j i : Matrix (Fin k) (Fin k) W).det =
      ((Matrix.of fun i j => c j i : Matrix (Fin k) (Fin k) W).map r).det := RingHom.map_det r _
  rw [← h2] at hU
  exact isUnit_of_map_unit r _ hU

section Gen

variable {O E W Qq : Type} [CommRing O] [IsDedekindDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq]

theorem exists_inv_of_notMem (P : HeightOneSpectrum O) {p : ℕ} (ρ : E →+* Qq) (hp : Irreducible (p : W))
    (h1 : ∀ x : O, ∃ y : W, ρ (algebraMap O E x) = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y))
    {s : O} (hs : s ∉ P.asIdeal) : ∃ u : W, algebraMap W Qq u * ρ (algebraMap O E s) = 1 := by
  obtain ⟨y, hy, hi⟩ := h1 s
  have hnd : ¬ (p : W) ∣ y := fun h => hs (hi.2 h)
  have hu : IsUnit y := by
    by_contra hu
    have hm : y ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).2 hu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hp] at hm
    exact hnd (Ideal.mem_span_singleton.1 hm)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u⁻¹ : Wˣ), ?_⟩
  rw [hy, ← map_mul, Units.inv_mul, map_one]

theorem den_of_int (P : HeightOneSpectrum O) {p : ℕ} (ρ : E →+* Qq)
    (h1 : ∀ x : O, ∃ y : W, ρ (algebraMap O E x) = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y))
    (e : E) (w : W) (he : ρ e = algebraMap W Qq w) :
    ∃ s : O, s ∉ P.asIdeal ∧ ∃ r : O, algebraMap O E s * e = algebraMap O E r := by
  by_cases e0 : e = 0
  · exact ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), 0, by simp [e0]⟩
  have hS := P.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization P.asIdeal.primeCompl (P.valuationSubringAtPrime E) :=
    Localization.subalgebra.isLocalization_ofField E _ hS
  rcases (P.valuationSubringAtPrime E).mem_or_inv_mem e with h | h
  · obtain ⟨⟨r, s⟩, hh⟩ := IsLocalization.surj P.asIdeal.primeCompl (⟨e, h⟩ : P.valuationSubringAtPrime E)
    have h2 : e * algebraMap O E s = algebraMap O E r := congrArg Subtype.val hh
    exact ⟨s, s.2, r, by rw [mul_comm]; exact h2⟩
  · obtain ⟨⟨r, s⟩, hh⟩ := IsLocalization.surj P.asIdeal.primeCompl (⟨e⁻¹, h⟩ : P.valuationSubringAtPrime E)
    have h2 : e⁻¹ * algebraMap O E s = algebraMap O E r := congrArg Subtype.val hh
    have h3 : algebraMap O E r * e = algebraMap O E s := by
      rw [← h2, mul_comm e⁻¹, mul_assoc, inv_mul_cancel₀ e0, mul_one]
    have hr : r ∉ P.asIdeal := by
      intro hrP
      obtain ⟨y, hy, hi⟩ := h1 r
      obtain ⟨y', hy', hi'⟩ := h1 s
      have hd := hi.1 hrP
      have h4 : y' = w * y := IsFractionRing.injective W Qq (by
        rw [map_mul, ← hy', ← he, ← hy, ← map_mul, mul_comm, h3])
      exact s.2 (hi'.2 (h4 ▸ dvd_mul_of_dvd_right hd w))
    exact ⟨r, hr, s, h3⟩

theorem uniform_den (P : HeightOneSpectrum O) {M : Type} [AddCommGroup M] [Module O M]
    (N : Submodule O M) (hN : N.FG) (l : M →ₗ[O] E)
    (h : ∀ n ∈ N, ∃ s : O, s ∉ P.asIdeal ∧ ∃ r : O, algebraMap O E s * l n = algebraMap O E r) :
    ∃ s : O, s ∉ P.asIdeal ∧ ∀ n ∈ N, ∃ r : O, algebraMap O E s * l n = algebraMap O E r := by
  classical
  obtain ⟨g, rfl⟩ := hN
  have key : ∀ g' : Finset M, (g' : Set M) ⊆ Submodule.span O (g : Set M) →
      ∃ s : O, s ∉ P.asIdeal ∧ ∀ n ∈ Submodule.span O (g' : Set M),
        ∃ r : O, algebraMap O E s * l n = algebraMap O E r := by
    intro g'
    induction g' using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), fun n hn => ⟨0, ?_⟩⟩
      have : n = 0 := by simpa using hn
      simp [this]
    | insert m g' _ ih =>
      intro hsub
      rw [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨s, hs, hh⟩ := ih hsub.2
      obtain ⟨s₀, hs₀, r₀, hr₀⟩ := h m hsub.1
      refine ⟨s₀ * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs₀ hs, fun n hn => ?_⟩
      rw [Finset.coe_insert, Submodule.mem_span_insert] at hn
      obtain ⟨a, z, hz, rfl⟩ := hn
      obtain ⟨r, hr⟩ := hh z hz
      refine ⟨a * s * r₀ + s₀ * r, ?_⟩
      rw [map_add (f := _), map_smul, Algebra.smul_def]
      simp only [map_add (f := _), map_mul]
      rw [← hr, ← hr₀]
      ring
  obtain ⟨s, hs, hh⟩ := key g Submodule.subset_span
  exact ⟨s, hs, hh⟩

end Gen

section Main

variable {O E W Qq : Type} [CommRing O] [IsDedekindDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq]

theorem mem_colSpan_iff {k : ℕ} (a : Matrix (Fin k) (Fin k) Qq) (y : Fin k → Qq) :
    y ∈ colSpan W a ↔ ∃ c : Fin k → W, y = a *ᵥ (fun i => algebraMap W Qq (c i)) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]

theorem exists_frame {k : ℕ} (ρ : E →+* Qq) (N : Submodule O (Fin k → E))
    (a : Matrix (Fin k) (Fin k) Qq) (ha : IsUnit a.det)
    (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → E))) = colSpan W a) :
    ∃ (B : Matrix (Fin k) (Fin k) E) (T : Matrix (Fin k) (Fin k) W), IsUnit T.det ∧
      (∀ j, (fun i => B i j) ∈ N) ∧ B.map ρ = a * T.map (algebraMap W Qq) := by
  classical
  let f : (Fin k → W) → (Fin k → Qq) := fun c => a *ᵥ (fun i => algebraMap W Qq (c i))
  have hinj : Function.Injective f := by
    intro c c' h
    have h2 : a⁻¹ *ᵥ (f c) = a⁻¹ *ᵥ (f c') := by rw [h]
    simp only [f, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ha, Matrix.one_mulVec] at h2
    funext i
    exact IsFractionRing.injective W Qq (congrFun h2 i)
  have hadd : ∀ c c', f (c + c') = f c + f c' := by
    intro c c'
    simp only [f, ← Matrix.mulVec_add]
    congr 1
    ext i
    simp
  have hsmul : ∀ (w : W) c, f (w • c) = w • f c := by
    intro w c
    simp only [f]
    rw [← Matrix.mulVec_smul]
    congr 1
    ext i
    simp [Algebra.smul_def]
  let G : Set (Fin k → W) := {c | f c ∈ (fun x i => ρ (x i)) '' (N : Set (Fin k → E))}
  have hlift : ∀ y ∈ Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → E))),
      ∃ c ∈ Submodule.span W G, f c = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      have hm : x ∈ colSpan W a := hNa ▸ Submodule.subset_span hx
      obtain ⟨c, rfl⟩ := (mem_colSpan_iff a x).1 hm
      exact ⟨c, Submodule.subset_span hx, rfl⟩
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have h0 : (fun i : Fin k => algebraMap W Qq ((0 : Fin k → W) i)) = 0 := by ext i; simp
      simp only [f, h0, Matrix.mulVec_zero]
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', Submodule.add_mem _ hc hc', hadd c c'⟩
    | smul w x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨w • c, Submodule.smul_mem _ _ hc, hsmul w c⟩
  have hG : Submodule.span W G = ⊤ := by
    refine eq_top_iff.2 fun c _ => ?_
    have hm : f c ∈ colSpan W a := (mem_colSpan_iff a _).2 ⟨c, rfl⟩
    rw [← hNa] at hm
    obtain ⟨c', hc', h⟩ := hlift _ hm
    exact hinj h ▸ hc'
  obtain ⟨T, hT, hcols⟩ := exists_unit_cols G hG
  choose n hn hnf using hcols
  refine ⟨Matrix.of fun i j => n j i, T, hT, fun j => hn j, ?_⟩
  ext i j
  have := congrFun (hnf j) i
  simpa [f, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem homLat_le_span (P : HeightOneSpectrum O) {p : ℕ} (ρ : E →+* Qq) (hp : Irreducible (p : W))
    (h1 : ∀ x : O, ∃ y : W, ρ (algebraMap O E x) = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y))
    {k k' : ℕ} (N : Submodule O (Fin k → E)) (N' : Submodule O (Fin k' → E)) (hN : N.FG)
    (a : Matrix (Fin k) (Fin k) Qq) (ha : IsUnit a.det)
    (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → E))) = colSpan W a)
    (Y : Set (Matrix (Fin k') (Fin k) E))
    (hY : ∀ A : Matrix (Fin k') (Fin k) E, (∀ n ∈ N, A *ᵥ n ∈ N') →
      ∃ t : O, t ∉ P.asIdeal ∧ algebraMap O E t • A ∈ Y) :
    homLat W (colSpan W a) (Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → E)))) ≤
      Submodule.span W ((fun A : Matrix (Fin k') (Fin k) E => A.map ρ) '' Y) := by
  classical
  obtain ⟨B, T, hT, hB, hBa⟩ := exists_frame (W := W) ρ N a ha hNa
  have hdet : IsUnit (B.map ρ).det := by
    rw [hBa, Matrix.det_mul]
    refine ha.mul ?_
    have : (T.map (algebraMap W Qq)).det = algebraMap W Qq T.det := (RingHom.map_det _ _).symm
    rw [this]
    exact hT.map _
  have hBdet : IsUnit B.det := by
    have h2 : ρ B.det = (B.map ρ).det := RingHom.map_det ρ B
    rw [← h2] at hdet
    exact isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hdet
  have hBB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBdet
  have hBB' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBdet
  have hRB : (B⁻¹).map ρ * B.map ρ = 1 := by
    rw [← Matrix.map_mul, hBB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBR : B.map ρ * (B⁻¹).map ρ = 1 := by
    rw [← Matrix.map_mul, hBB', Matrix.map_one _ (map_zero _) (map_one _)]
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hT
  have hRa : (B⁻¹).map ρ * a = (T⁻¹).map (algebraMap W Qq) := by
    have h3 : a = B.map ρ * (T⁻¹).map (algebraMap W Qq) := by
      rw [hBa, Matrix.mul_assoc, ← Matrix.map_mul, hTT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    rw [h3, ← Matrix.mul_assoc, hRB, Matrix.one_mul]
  have hint : ∀ n ∈ N, ∀ j, ∃ w : W, ρ ((B⁻¹ *ᵥ n) j) = algebraMap W Qq w := by
    intro n hn j
    have hm : (fun i => ρ (n i)) ∈ colSpan W a := hNa ▸ Submodule.subset_span ⟨n, hn, rfl⟩
    obtain ⟨c, hc⟩ := (mem_colSpan_iff a _).1 hm
    refine ⟨(T⁻¹ *ᵥ c) j, ?_⟩
    have e1 : ρ ((B⁻¹ *ᵥ n) j) = ((B⁻¹).map ρ *ᵥ (fun i => ρ (n i))) j := RingHom.map_mulVec ρ _ _ j
    have e2 : algebraMap W Qq ((T⁻¹ *ᵥ c) j) = ((T⁻¹).map (algebraMap W Qq) *ᵥ (fun i => algebraMap W Qq (c i))) j :=
      RingHom.map_mulVec _ _ _ j
    rw [e1, e2, hc, Matrix.mulVec_mulVec, hRa]
  intro x hx
  have hdec : x = ∑ j, vecMulVec (x *ᵥ (fun i => ρ (B i j))) ((B⁻¹).map ρ j) := by
    have h4 : x = (x * B.map ρ) * (B⁻¹).map ρ := by rw [Matrix.mul_assoc, hBR, Matrix.mul_one]
    conv_lhs => rw [h4]
    ext i l
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [hdec]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨s, hs, hden⟩ := uniform_den P N hN
    (((LinearMap.proj j : (Fin k → E) →ₗ[E] E) ∘ₗ (B⁻¹).mulVecLin).restrictScalars O) (fun n hn => by
      obtain ⟨w, hw⟩ := hint n hn j
      exact den_of_int P ρ h1 _ w hw)
  have hcol : x *ᵥ (fun i => ρ (B i j)) ∈
      Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → E))) :=
    hx _ (hNa ▸ Submodule.subset_span ⟨fun i => B i j, hB j, rfl⟩)
  suffices key : ∀ l ∈ Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → E))),
      vecMulVec l ((B⁻¹).map ρ j) ∈
        Submodule.span W ((fun A : Matrix (Fin k') (Fin k) E => A.map ρ) '' Y) from key _ hcol
  intro l hl
  induction hl using Submodule.span_induction with
  | mem l hl =>
    obtain ⟨n', hn', rfl⟩ := hl
    let A : Matrix (Fin k') (Fin k) E := algebraMap O E s • vecMulVec n' (B⁻¹ j)
    have hA : ∀ n ∈ N, A *ᵥ n ∈ N' := by
      intro n hn
      obtain ⟨r, hr⟩ := hden n hn
      have e : A *ᵥ n = r • n' := by
        have hr' : algebraMap O E s * (B⁻¹ *ᵥ n) j = algebraMap O E r := hr
        ext i
        simp only [A, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, Pi.smul_apply, smul_eq_mul,
          Algebra.smul_def]
        rw [← hr']
        simp [Matrix.mulVec, mul_comm, mul_assoc, mul_left_comm]
      rw [e]
      exact N'.smul_mem r hn'
    obtain ⟨t, ht, htY⟩ := hY A hA
    obtain ⟨u, hu⟩ := exists_inv_of_notMem P ρ hp h1
      (show t * s ∉ P.asIdeal from fun hm => (P.isPrime.mem_or_mem hm).elim ht hs)
    have e : vecMulVec (fun i => ρ (n' i)) ((B⁻¹).map ρ j) = u • (algebraMap O E t • A).map ρ := by
      ext i l
      simp only [A, Matrix.vecMulVec_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Algebra.smul_def] at hu ⊢
      linear_combination (-(ρ (n' i) * ρ (B⁻¹ j l))) * hu
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, htY, rfl⟩)
  | zero =>
    have : vecMulVec (0 : Fin k' → Qq) ((B⁻¹).map ρ j) = 0 := by ext i l; simp [Matrix.vecMulVec_apply]
    rw [this]; exact Submodule.zero_mem _
  | add l l' _ _ hl hl' =>
    have : vecMulVec (l + l') ((B⁻¹).map ρ j) = vecMulVec l ((B⁻¹).map ρ j) + vecMulVec l' ((B⁻¹).map ρ j) := by
      ext i m; simp [Matrix.vecMulVec_apply, add_mul]
    rw [this]; exact Submodule.add_mem _ hl hl'
  | smul w l _ hl =>
    have : vecMulVec (w • l) ((B⁻¹).map ρ j) = w • vecMulVec l ((B⁻¹).map ρ j) := by
      ext i m; simp [Matrix.vecMulVec_apply, Algebra.smul_def, mul_assoc]
    rw [this]; exact Submodule.smul_mem _ _ hl

end Main

theorem homLat_le_span_YYl : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (hN : N.FG) (hN' : N'.FG) (hsN : Submodule.span D.host.E (N : Set (Fin k → D.host.E)) = ⊤) (hsN' : Submodule.span D.host.E (N' : Set (Fin k' → D.host.E)) = ⊤) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (ha : IsUnit a.det) (hb : IsUnit b.det) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), homLat W (colSpan W a) (colSpan W b) ≤ Submodule.span W ((fun A : Matrix (Fin k') (Fin k) D.host.E => A.map ρ) '' (TaylorLogMetric.YYl D N N' : Set (Matrix (Fin k') (Fin k) D.host.E))) := by
  intro D P W Qq _ _ _ _ _ _ p hp ρ hA h1 k k' N N' hN _ _ _ a b ha _ hNa hNb
  rw [← hNb]
  have h1mem : (1 : D.host.E) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [hA]
    exact ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using Submodule.one_le.1 le_rfl⟩
  obtain ⟨t, ht, htA⟩ := h1mem
  refine homLat_le_span P ρ hp h1 N N' hN a ha hNa _ fun A hAN => ⟨t, ht, ?_⟩
  refine Submodule.subset_span ⟨t • (1 : D.host.E), htA, A, Submodule.subset_span hAN, ?_⟩
  rw [Algebra.smul_def, mul_one]

end GlobalTheory.VolOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixHomLatticeLeSpanIdealHomImageStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixHomLattice_le_span_ideal_hom_image : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (hN : N.FG) (hN' : N'.FG) (hsN : Submodule.span D.host.E (N : Set (Fin k → D.host.E)) = ⊤) (hsN' : Submodule.span D.host.E (N' : Set (Fin k' → D.host.E)) = ⊤) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (ha : IsUnit a.det) (hb : IsUnit b.det) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), homLat W (colSpan W a) (colSpan W b) ≤ Submodule.span W ((fun A : Matrix (Fin k') (Fin k) D.host.E => A.map ρ) '' (TaylorLogMetric.YYl D N N' : Set (Matrix (Fin k') (Fin k) D.host.E))) := by
  first | exact @GlobalTheory.VolOnto.homLat_le_span_YYl | exact GlobalTheory.VolOnto.homLat_le_span_YYl | (intros; apply GlobalTheory.VolOnto.homLat_le_span_YYl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdealMulHomMapMemMatrixHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdealMulHomMapMemMatrixHomLattice
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

noncomputable section

namespace GlobalTheory.TwU

theorem map_mem_homLat_of_mem_YYl : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), ∀ A ∈ TaylorLogMetric.YYl D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
  intro D P W Qq _ _ _ _ _ _ p hp ρ hA h1 k k' N N' a b hNa hNb

  have hsc : ∀ (c : D.host.E) (M : Matrix (Fin k') (Fin k) D.host.E), (∃ y : W, ρ c = algebraMap W Qq y) →
      M.map ρ ∈ homLat W (colSpan W a) (colSpan W b) → (c • M).map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
    rintro c M ⟨y, hy⟩ hM z hz
    have e : (c • M).map ρ = y • M.map ρ := by
      ext i j
      simp [Matrix.map_apply, map_mul, hy, Algebra.smul_def]
    rw [e, Matrix.smul_mulVec]
    exact (colSpan W b).smul_mem y (hM z hz)
  have hO : ∀ c : 𝓞 D.host.E, ∃ y : W, ρ (c : D.host.E) = algebraMap W Qq y := fun c =>
    (h1 c).imp fun y hy => hy.1

  have hAA : ∀ x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ y : W, ρ x = algebraMap W Qq y := by
    intro x hx
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
      ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩
    rw [hA] at hx'
    obtain ⟨s, hs, hsx⟩ := hx'
    obtain ⟨t, ht⟩ := Submodule.mem_one.1 hsx
    obtain ⟨ys, hys, hsP⟩ := h1 s
    obtain ⟨yt, hyt⟩ := hO t
    have hu : IsUnit ys := by
      have hmax : IsLocalRing.maximalIdeal W = Ideal.span {(p : W)} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hp
      by_contra hn
      have : ys ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal ys).2 hn
      rw [hmax, Ideal.mem_span_singleton] at this
      exact hs (hsP.2 this)
    refine ⟨hu.unit⁻¹ * yt, ?_⟩
    have e1 : ρ (algebraMap (𝓞 D.host.E) D.host.E t) = ρ (s : D.host.E) * ρ x := by
      rw [ht, Algebra.smul_def, map_mul]
    have e2 : algebraMap W Qq ys ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W Qq)]
      exact hu.ne_zero
    rw [map_mul, ← hyt]
    change _ = _ * ρ (t : D.host.E)
    rw [show ((t : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E t from rfl, e1, hys, ← mul_assoc, ← map_mul,
      IsUnit.val_inv_mul, map_one, one_mul]

  have hHom : ∀ A ∈ TaylorLogMetric.homL D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
    intro A hA'
    induction hA' using Submodule.span_induction with
    | mem A hA0 =>
      intro z hz
      rw [← hNa] at hz
      rw [← hNb]
      induction hz using Submodule.span_induction with
      | mem z hz0 =>
        obtain ⟨x, hx, rfl⟩ := hz0
        refine Submodule.subset_span ⟨A *ᵥ x, hA0 x hx, ?_⟩
        funext i
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hz hz'
      | smul c z _ hz => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hz
    | zero => rw [Matrix.map_zero _ (map_zero ρ)]; exact Submodule.zero_mem _
    | add A B _ _ hA hB => rw [Matrix.map_add _ (map_add ρ)]; exact Submodule.add_mem _ hA hB
    | smul c A _ hA => exact hsc (c : D.host.E) A (hO c) hA
  intro A hA'
  induction hA' using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA0, rfl⟩ := hB
    exact hsc c A (hAA c hc) (hHom A hA0)
  | zero => rw [Matrix.map_zero _ (map_zero ρ)]; exact Submodule.zero_mem _
  | add A B _ _ hA hB => rw [Matrix.map_add _ (map_add ρ)]; exact Submodule.add_mem _ hA hB
  | smul c A _ hA => exact hsc (c : D.host.E) A (hO c) hA

end GlobalTheory.TwU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdealMulHomMapMemMatrixHomLatticeStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_mul_hom_map_mem_matrixHomLattice : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), ∀ A ∈ TaylorLogMetric.YYl D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
  first | exact @GlobalTheory.TwU.map_mem_homLat_of_mem_YYl | exact GlobalTheory.TwU.map_mem_homLat_of_mem_YYl | (intros; apply GlobalTheory.TwU.map_mem_homLat_of_mem_YYl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomLatticeVolumeCompletionSplitPlace
noncomputable section

namespace GlobalTheory.VolAt

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix

theorem latAt_lattice {p : ℕ} [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup)
    (hL : (X.Pj j).IsLatTup L) :
    ∃ g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v), IsUnit g.det ∧
      X.latAt v j L = colSpan (X.G.P.W v) g ∧ len X v j L = -ordP (X.G.P.W v) p g.det := by
  have hS := X.G.P.setting v
  haveI := hS.frac_alt
  cases j with
  | zero =>
    have h0 : IsLattice (X.G.P.W v) (X.latAt v 0 L) := hL v
    obtain ⟨g, hg, hL'⟩ := h0
    refine ⟨g, hg, hL', ?_⟩
    change lenLat (X.G.P.W v) p (X.latAt v 0 L) = _
    rw [hL']
    exact lenLat_colSpan hS.p_unif g hg
  | succ j =>
    have h0 : IsLattice (X.G.P.W v) (X.latAt v (j + 1) L) := hL v
    obtain ⟨g, hg, hL'⟩ := h0
    refine ⟨g, hg, hL', ?_⟩
    change lenLat (X.G.P.W v) p (X.latAt v (j + 1) L) = _
    rw [hL']
    exact lenLat_colSpan hS.p_unif g hg

theorem Pj_m_succ {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) : (X.Pj j).m + 1 = NN X.G.P.m X.t j := by
  cases j with
  | zero => simp [NN, Sys.Pj, Fills.Pj]
  | succ j =>
    simp only [NN, Sys.Pj, Fills.Pj, Places.withWt, Sys.t]
    ring

theorem homLat_conj {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (M g : Matrix (Fin k) (Fin k) Qq) (M' g' : Matrix (Fin k') (Fin k') Qq) (hM' : IsUnit M'.det)
    (z : Matrix (Fin k') (Fin k) Qq) :
    z ∈ homLat W (colSpan W (M * g)) (colSpan W (M' * g')) ↔
      ∀ y ∈ colSpan W g, (M'⁻¹ * z * M) *ᵥ y ∈ colSpan W g' := by
  rw [← colSpan_mul, ← colSpan_mul, mem_homLat]
  have hinv : M'⁻¹ * M' = 1 := Matrix.nonsing_inv_mul M' hM'
  have hinv' : M' * M'⁻¹ = 1 := Matrix.mul_nonsing_inv M' hM'
  constructor
  · intro h y hy
    obtain ⟨u, hu, hu'⟩ := h (M *ᵥ y) (Submodule.mem_map_of_mem hy)
    have e : (M'⁻¹ * z * M) *ᵥ y = u := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have : z *ᵥ (M *ᵥ y) = M' *ᵥ u := hu'.symm
      rw [this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [e]
    exact hu
  · rintro h _ ⟨y, hy, rfl⟩
    have e : z *ᵥ ((M.mulVecLin.restrictScalars W) y) = M' *ᵥ ((M'⁻¹ * z * M) *ᵥ y) := by
      change z *ᵥ (M *ᵥ y) = _
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv', Matrix.one_mul]
    rw [e]
    exact Submodule.mem_map_of_mem (h y hy)

theorem vol_main : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (ρ : D.host.E →+* X.G.P.Qq v) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) → (∀ x : 𝓞 D.host.E, ∃ y : X.G.P.W v, ρ x = algebraMap _ _ y ∧ (x ∈ P.asIdeal ↔ (p : X.G.P.W v) ∣ y)) → (∀ (y : X.G.P.W v) (n : ℕ), ∃ (x : 𝓞 D.host.E) (z : X.G.P.W v), ρ x = algebraMap _ _ (y + (p : X.G.P.W v) ^ n * z)) → ∃ φ : GL3Theta.EP D P ≃+* X.G.P.Qq v, (∀ x : D.host.E, φ (algebraMap _ _ x) = ρ x) ∧ ∀ (M : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (M' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)), IsUnit M.det → IsUnit M'.det → ∀ (N : (X.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)) (N' : (X.Pj (j + 1)).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E)) (S : Set ((X.Pj j).Tup × (X.Pj (j + 1)).Tup)), (∀ q ∈ S, (X.Pj j).IsLatTup q.1 ∧ (X.Pj (j + 1)).IsLatTup q.2 ∧ TaylorLogMetric.admitted D _ _ (N q.1) (N' q.2) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) = (X.latAt v j q.1).map ((M.mulVecLin).restrictScalars (X.G.P.W v)) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) = (X.latAt v (j + 1) q.2).map ((M'.mulVecLin).restrictScalars (X.G.P.W v))) → ∀ q ∈ S, (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ X.ind v j q.1 q.2 (M'⁻¹ * y.map φ * M) = 1) ∧ ∀ q₀ ∈ S, GL3Theta.volP (GL3Theta.YP D P (N q₀.1) (N' q₀.2)) (GL3Theta.YP D P (N q.1) (N' q.2)) = (p : ℝ) ^ ((X.G.P.n' v : ℤ) * (volE X v j q.1 q.2 - volE X v j q₀.1 q₀.2)) := by
  intro D p _ X v j ρ P hA h1 h2
  have hS := X.G.P.setting v
  haveI := hS.frac_alt
  obtain ⟨φ, hφ, hop, hnb⟩ := GlobalTheory.T.numberField_completion_ringEquiv_of_dense_unramified P p hS.p_unif hS.eq_sum_herm_smul_frame_of_inW ρ h1 h2
  refine ⟨φ, hφ, ?_⟩
  intro M M' hM hM' N N' S hSq
  have key : ∀ q ∈ S, ∃ (g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
      (g' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)),
      IsUnit (M * g).det ∧ IsUnit (M' * g').det ∧
      (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ y.map φ ∈ homLat (X.G.P.W v) (colSpan (X.G.P.W v) (M * g))
        (colSpan (X.G.P.W v) (M' * g'))) ∧
      (∀ z, X.ind v j q.1 q.2 (M'⁻¹ * z * M) = 1 ↔ z ∈ homLat (X.G.P.W v) (colSpan (X.G.P.W v) (M * g))
        (colSpan (X.G.P.W v) (M' * g'))) ∧
      ordP (X.G.P.W v) p (M * g).det = ordP (X.G.P.W v) p M.det - len X v j q.1 ∧
      ordP (X.G.P.W v) p (M' * g').det = ordP (X.G.P.W v) p M'.det - len X v (j + 1) q.2 := by
    intro q hq
    obtain ⟨hL, hL', hAdm, hsp, hsp'⟩ := hSq q hq
    obtain ⟨g, hg, hgL, hlen⟩ := latAt_lattice X v j q.1 hL
    obtain ⟨g', hg', hgL', hlen'⟩ := latAt_lattice X v (j + 1) q.2 hL'
    have hMg : IsUnit (M * g).det := by rw [Matrix.det_mul]; exact hM.mul hg
    have hMg' : IsUnit (M' * g').det := by rw [Matrix.det_mul]; exact hM'.mul hg'
    have hNa : Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) =
        colSpan (X.G.P.W v) (M * g) := by rw [hsp, hgL, colSpan_mul]
    have hNb : Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) =
        colSpan (X.G.P.W v) (M' * g') := by rw [hsp', hgL', colSpan_mul]
    obtain ⟨-, -, ⟨hFG, hspan, -⟩, ⟨hFG', hspan', -⟩⟩ := hAdm
    refine ⟨g, g', hMg, hMg', fun y => ?_, fun z => ?_, ?_, ?_⟩
    · exact GlobalTheory.T.mem_closure_iff_map_mem_matrixHomLattice_completion P p hS.p_unif ρ h2 φ hφ hop hnb (TaylorLogMetric.YYl D (N q.1) (N' q.2)) _ _ hMg hMg'
        (GlobalTheory.T.ideal_mul_hom_map_mem_matrixHomLattice D P p hS.p_unif ρ hA h1 _ _ _ _ hNa hNb)
        (GlobalTheory.T.matrixHomLattice_le_span_ideal_hom_image D P p hS.p_unif ρ hA h1 _ _ hFG hFG' hspan hspan' _ _ hMg hMg' hNa hNb) y
    · rw [homLat_conj M g M' g' hM' z, ← hgL, ← hgL']
      unfold Sys.ind
      split_ifs with h
      · exact iff_of_true rfl h
      · exact iff_of_false (by norm_num) h
    · rw [Matrix.det_mul, ordP_mul hS.p_unif hM.ne_zero hg.ne_zero, hlen]
      ring
    · rw [Matrix.det_mul, ordP_mul hS.p_unif hM'.ne_zero hg'.ne_zero, hlen']
      ring
  intro q hq
  obtain ⟨g, g', hMg, hMg', hY, hind, ho, ho'⟩ := key q hq
  refine ⟨fun y => (hY y).trans (hind _).symm, fun q₀ hq₀ => ?_⟩
  obtain ⟨g₀, g₀', hMg₀, hMg₀', hY₀, -, ho₀, ho₀'⟩ := key q₀ hq₀
  let e : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (GL3Theta.EP D P) →+
      Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
    φ.toAddEquiv.toAddMonoidHom.mapMatrix
  have he : Function.Surjective e := fun z => ⟨z.map φ.symm, by ext i l; simp [e]⟩
  have hYc : ∀ (A : Submodule (X.G.P.W v) _), (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ y.map φ ∈ A) →
      GL3Theta.YP D P (N q.1) (N' q.2) = A.toAddSubgroup.comap e := fun A h => by
    ext y; exact h y
  have hYc₀ : ∀ (A : Submodule (X.G.P.W v) _), (∀ y, y ∈ GL3Theta.YP D P (N q₀.1) (N' q₀.2) ↔ y.map φ ∈ A) →
      GL3Theta.YP D P (N q₀.1) (N' q₀.2) = A.toAddSubgroup.comap e := fun A h => by
    ext y; exact h y
  have hrel : ∀ A B : AddSubgroup (Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      ((A.comap e).addSubgroupOf (B.comap e)).index = A.relIndex B := fun A B => by
    change (A.comap e).relIndex (B.comap e) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective he]
  unfold GL3Theta.volP
  rw [hYc _ hY, hYc₀ _ hY₀, hrel, hrel,
    GlobalTheory.T.relIndex_matrixHomLattice_ratio_eq_residue_pow p (X.G.P.n' v) hS.p_unif hS.res_card _ _ _ _ hMg₀ hMg hMg₀' hMg', ho, ho', ho₀, ho₀']
  congr 1
  unfold volE
  rw [← Pj_m_succ X j, ← Pj_m_succ X (j + 1)]
  push_cast
  ring

end GlobalTheory.VolAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomLatticeVolumeCompletionSplitPlaceStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLattice_volume_completion_splitPlace : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (ρ : D.host.E →+* X.G.P.Qq v) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) → (∀ x : 𝓞 D.host.E, ∃ y : X.G.P.W v, ρ x = algebraMap _ _ y ∧ (x ∈ P.asIdeal ↔ (p : X.G.P.W v) ∣ y)) → (∀ (y : X.G.P.W v) (n : ℕ), ∃ (x : 𝓞 D.host.E) (z : X.G.P.W v), ρ x = algebraMap _ _ (y + (p : X.G.P.W v) ^ n * z)) → ∃ φ : GL3Theta.EP D P ≃+* X.G.P.Qq v, (∀ x : D.host.E, φ (algebraMap _ _ x) = ρ x) ∧ ∀ (M : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (M' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)), IsUnit M.det → IsUnit M'.det → ∀ (N : (X.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)) (N' : (X.Pj (j + 1)).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E)) (S : Set ((X.Pj j).Tup × (X.Pj (j + 1)).Tup)), (∀ q ∈ S, (X.Pj j).IsLatTup q.1 ∧ (X.Pj (j + 1)).IsLatTup q.2 ∧ TaylorLogMetric.admitted D _ _ (N q.1) (N' q.2) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) = (X.latAt v j q.1).map ((M.mulVecLin).restrictScalars (X.G.P.W v)) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) = (X.latAt v (j + 1) q.2).map ((M'.mulVecLin).restrictScalars (X.G.P.W v))) → ∀ q ∈ S, (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ X.ind v j q.1 q.2 (M'⁻¹ * y.map φ * M) = 1) ∧ ∀ q₀ ∈ S, GL3Theta.volP (GL3Theta.YP D P (N q₀.1) (N' q₀.2)) (GL3Theta.YP D P (N q.1) (N' q.2)) = (p : ℝ) ^ ((X.G.P.n' v : ℤ) * (volE X v j q.1 q.2 - volE X v j q₀.1 q₀.2)) := by
  first | exact @GlobalTheory.VolAt.vol_main | exact GlobalTheory.VolAt.vol_main | (intros; apply GlobalTheory.VolAt.vol_main <;> assumption)
end
