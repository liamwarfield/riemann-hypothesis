module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClassesSelfDualOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.SelectIdem

section Ring

variable {R : Type*} [CommRing R]

def LocDvd (P : Ideal R) (n x : R) : Prop := ∃ s, s ∉ P ∧ n ∣ s * x

theorem dvd_of_locDvd {n x : R} (h : ∀ P : Ideal R, P.IsMaximal → LocDvd P n x) : n ∣ x := by
  by_contra hx
  let I : Ideal R := Submodule.comap (LinearMap.toSpanSingleton R R x) (Ideal.span {n})
  have hI : ∀ s, s ∈ I ↔ n ∣ s * x := fun s => by
    simp [I, Ideal.mem_span_singleton]
  have hne : I ≠ ⊤ := fun h1 => hx (by
    have : (1 : R) ∈ I := h1 ▸ Submodule.mem_top
    simpa using (hI 1).1 this)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨s, hs, hd⟩ := h P hP
  exact hs (hIP ((hI s).2 hd))

theorem LocDvd.comb {P : Ideal R} (hP : P.IsPrime) {n x y z : R} (a b : R)
    (hx : LocDvd P n x) (hy : LocDvd P n y) (hz : z = a * x + b * y) : LocDvd P n z := by
  obtain ⟨s, hs, hs'⟩ := hx
  obtain ⟨t, ht, ht'⟩ := hy
  refine ⟨s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  have : s * t * z = (t * a) * (s * x) + (s * b) * (t * y) := by rw [hz]; ring
  rw [this]
  exact dvd_add (hs'.mul_left _) (ht'.mul_left _)

theorem LocDvd.of_dvd {P : Ideal R} {n m x : R} (h : n ∣ m) (hx : LocDvd P m x) :
    LocDvd P n x := by
  obtain ⟨s, hs, hs'⟩ := hx
  exact ⟨s, hs, h.trans hs'⟩

theorem LocDvd.of_not_mem {P : Ideal R} {n : R} (h : n ∉ P) (x : R) : LocDvd P n x :=
  ⟨n, h, dvd_mul_right _ _⟩

theorem exists_loc [IsDedekindDomain R] {n : R} (hn : n ≠ 0) (T : Ideal R → Prop) :
    ∃ ε : R, ∀ P : Ideal R, P.IsMaximal → LocDvd P n (ε - if T P then 1 else 0) := by
  have hn' : Ideal.span {n} ≠ (⊥ : Ideal R) := by simpa using hn
  let S : Finset (Ideal R) := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).toFinset
  have hS : ∀ P : Ideal R, P ∈ S ↔ P.IsPrime ∧ n ∈ P := fun P => by
    simp only [S, Multiset.mem_toFinset]
    rw [Ideal.mem_normalizedFactors_iff hn', Ideal.span_singleton_le_iff_mem]
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun P => P) (fun _ => 1)
    (fun P hP => by
      obtain ⟨h1, h2⟩ := (hS P).1 hP
      refine Ideal.prime_of_isPrime ?_ h1
      rintro rfl
      exact hn (by simpa using h2))
    (fun _ _ _ _ h => h) (fun P => if T P.1 then 1 else 0)
  have hb' : ∀ P : Ideal R, P.IsPrime → n ∈ P → b - (if T P then 1 else 0) ∈ P := fun P h1 h2 => by
    simpa using hb P ((hS P).2 ⟨h1, h2⟩)
  have hrad : (1 - b) * b ∈ (Ideal.span {n}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨h1, h2⟩
    have h3 := hb' P h2 ((Ideal.span_singleton_le_iff_mem _).1 h1)
    by_cases hT : T P
    · rw [if_pos hT] at h3
      have : (1 - b) * b = (-b) * (b - 1) := by ring
      rw [this]; exact P.mul_mem_left _ h3
    · rw [if_neg hT, sub_zero] at h3
      exact P.mul_mem_left _ h3
  obtain ⟨k, hk⟩ := hrad
  rw [Ideal.mem_span_singleton, mul_pow] at hk
  have hc : IsCoprime (1 - b) b := ⟨1, 1, by ring⟩
  obtain ⟨u, v, huv⟩ := hc.pow (m := k) (n := k)
  refine ⟨v * b ^ k, fun P hP => ?_⟩
  by_cases hnP : n ∈ P
  · have h3 := hb' P hP.isPrime hnP
    by_cases hT : T P
    · rw [if_pos hT] at h3 ⊢
      refine ⟨b ^ k, fun h => ?_, ?_⟩
      · have h4 := hP.isPrime.mem_of_pow_mem k h
        have : (1 : R) ∈ P := by simpa using P.sub_mem h4 h3
        exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
      · have : b ^ k * (v * b ^ k - 1) = (-u) * ((1 - b) ^ k * b ^ k) := by
          linear_combination b ^ k * huv
        rw [this]; exact hk.mul_left _
    · rw [if_neg hT, sub_zero] at h3 ⊢
      refine ⟨(1 - b) ^ k, fun h => ?_, ?_⟩
      · have h4 := hP.isPrime.mem_of_pow_mem k h
        have : (1 : R) ∈ P := by simpa using P.add_mem h4 h3
        exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
      · have : (1 - b) ^ k * (v * b ^ k) = v * ((1 - b) ^ k * b ^ k) := by ring
        rw [this]; exact hk.mul_left _
  · exact LocDvd.of_not_mem hnP _

theorem exists_select [IsDedekindDomain R] [CharZero R] {G : Type*} [Group G]
    [MulSemiringAction G R] (c : G) (hc : c * c = 1) :
    ∃ e : ℕ → R, (∀ N m : ℕ, 0 < N → 0 < m → (N : R) ∣ e (N * m) - e N) ∧
      (∀ N : ℕ, 0 < N → (N : R) ∣ e N * e N - e N ∧ (N : R) ∣ e N * (c • e N)) ∧
      ∀ N : ℕ, 0 < N →
        ((∀ P : Ideal R, P.IsMaximal → (N : R) ∈ P → c • P = P) → (N : R) ∣ e N + c • e N) ∧
        ((∀ P : Ideal R, P.IsMaximal → (N : R) ∈ P → c • P ≠ P) →
          (N : R) ∣ 1 - (e N + c • e N)) := by
  let T : Ideal R → Prop := fun P => WellOrderingRel P (c • P)
  have hcc : ∀ P : Ideal R, c • c • P = P := fun P => by rw [smul_smul, hc, one_smul]
  have hT1 : ∀ P, T P → ¬ T (c • P) := fun P h1 h2 => by
    simp only [T, hcc] at h1 h2
    exact asymm h1 h2
  have hT2 : ∀ P, c • P ≠ P → ¬ T P → T (c • P) := fun P h1 h2 => by
    simp only [T, hcc] at h2 ⊢
    rcases trichotomous_of WellOrderingRel P (c • P) with h | h | h
    · exact (h2 h).elim
    · exact (h1 h.symm).elim
    · exact h
  have hT3 : ∀ P, c • P = P → ¬ T P := fun P h1 h2 => hT1 P h2 (h1.symm ▸ h2)
  have hex : ∀ N : ℕ, ∃ ε : R, 0 < N →
      ∀ P : Ideal R, P.IsMaximal → LocDvd P (N : R) (ε - if T P then 1 else 0) := fun N => by
    by_cases hN : 0 < N
    · obtain ⟨ε, h⟩ := exists_loc (n := (N : R)) (by exact_mod_cast hN.ne') T
      exact ⟨ε, fun _ => h⟩
    · exact ⟨0, fun h => (hN h).elim⟩
  choose e he using hex
  have he' : ∀ N : ℕ, 0 < N → ∀ P : Ideal R, P.IsMaximal →
      LocDvd P (N : R) (c • e N - if T (c • P) then 1 else 0) := fun N hN P hP => by
    have hP' : (c • P).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (MulSemiringAction.toRingHom G R c)
        (MulAction.surjective c) hP with h | h
      · exact absurd h (Ideal.IsPrime.smul (H := hP.isPrime) c).ne_top
      · exact h
    obtain ⟨s, hs, t, ht⟩ := he N hN _ hP'
    refine ⟨c • s, fun h => hs ?_, c • t, ?_⟩
    · have := Ideal.smul_mem_pointwise_smul c _ _ h
      rwa [smul_smul, hc, one_smul] at this
    · have h := congrArg (MulSemiringAction.toRingHom G R c) ht
      simp only [map_mul, map_sub, map_natCast, MulSemiringAction.toRingHom_apply] at h
      rw [← h]
      split_ifs <;> simp
  refine ⟨e, fun N m hN hm => ?_, fun N hN => ⟨?_, ?_⟩, fun N hN => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine dvd_of_locDvd fun P hP => ?_
    exact LocDvd.comb hP.isPrime 1 (-1)
      ((he (N * m) (Nat.mul_pos hN hm) P hP).of_dvd (by push_cast; exact dvd_mul_right _ _))
      (he N hN P hP) (by ring)
  · refine dvd_of_locDvd fun P hP => ?_
    have h := he N hN P hP
    by_cases hT : T P
    · rw [if_pos hT] at h
      exact LocDvd.comb hP.isPrime (e N) 0 h h (by ring)
    · rw [if_neg hT] at h
      exact LocDvd.comb hP.isPrime (e N - 1) 0 h h (by ring)
  · refine dvd_of_locDvd fun P hP => ?_
    have h := he N hN P hP
    have h' := he' N hN P hP
    by_cases hT : T P
    · rw [if_neg (hT1 P hT)] at h'
      exact LocDvd.comb hP.isPrime (e N) 0 h' h' (by ring)
    · rw [if_neg hT] at h
      exact LocDvd.comb hP.isPrime (c • e N) 0 h h (by ring)
  · refine dvd_of_locDvd fun P hP => ?_
    by_cases hNP : (N : R) ∈ P
    · have h1 := he N hN P hP
      have h2 := he' N hN P hP
      have h3 := h P hP hNP
      rw [h3] at h2
      rw [if_neg (hT3 P h3)] at h1 h2
      exact LocDvd.comb hP.isPrime 1 1 h1 h2 (by ring)
    · exact LocDvd.of_not_mem hNP _
  · refine dvd_of_locDvd fun P hP => ?_
    by_cases hNP : (N : R) ∈ P
    · have h1 := he N hN P hP
      have h2 := he' N hN P hP
      have h3 := h P hP hNP
      by_cases hT : T P
      · rw [if_pos hT] at h1
        rw [if_neg (hT1 P hT)] at h2
        exact LocDvd.comb hP.isPrime (-1) (-1) h1 h2 (by ring)
      · rw [if_neg hT] at h1
        rw [if_pos (hT2 P h3 hT)] at h2
        exact LocDvd.comb hP.isPrime (-1) (-1) h1 h2 (by ring)
    · exact LocDvd.of_not_mem hNP _

end Ring

theorem smul_eq_of_abelian {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
    (hcomm : ∀ σ τ : E ≃ₐ[ℚ] E, σ * τ = τ * σ) (c : E ≃ₐ[ℚ] E) {q : ℕ} (hq : q.Prime)
    (P Q : Ideal (𝓞 E)) (hP : P.IsPrime) (hQ : Q.IsPrime) (hqP : (q : 𝓞 E) ∈ P)
    (hqQ : (q : 𝓞 E) ∈ Q) (h : c • P = P) : c • Q = Q := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have key : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → P.LiesOver (Ideal.span {(q : ℤ)}) :=
    fun P hP h => ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
      simpa using h)⟩
  haveI := key P hP hqP
  haveI := key Q hQ hqQ
  obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  rw [smul_smul, hcomm, ← smul_smul, h]

theorem exists_select_idem : ∀ (D : D7), ∃ e : ℕ → 𝓞 D.host.E, (∀ N m : ℕ, 0 < N → 0 < m → (N : 𝓞 D.host.E) ∣ e (N * m) - e N) ∧ (∀ N : ℕ, 0 < N → (N : 𝓞 D.host.E) ∣ e N * e N - e N ∧ (N : 𝓞 D.host.E) ∣ e N * (D.host.conj • e N)) ∧ ∀ q k : ℕ, q.Prime → (InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ e (q ^ k) + D.host.conj • e (q ^ k)) ∧ (¬ InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ 1 - (e (q ^ k) + D.host.conj • e (q ^ k))) := by
  intro D
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hcomm : ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, σ * τ = τ * σ := fun σ τ =>
    D.host.galE_injective (by
      rw [D.host.galE_mul,
        D.host.galE_mul, mul_comm])
  have hc : D.host.conj * D.host.conj = 1 := by
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    refine AlgEquiv.ext fun x => φ.injective ?_
    have h1 := D.host.conjE_apply φ
    exact (h1 _).trans ((congrArg _ (h1 x)).trans (Complex.conj_conj _))
  obtain ⟨e, h1, h2, h3⟩ := exists_select (R := 𝓞 D.host.E) D.host.conj hc
  refine ⟨e, h1, h2, fun q k hq => ?_⟩
  have hq' : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ((q ^ k : ℕ) : 𝓞 D.host.E) ∈ P →
      (q : 𝓞 D.host.E) ∈ P := fun P hP h =>
    hP.isPrime.mem_of_pow_mem k (by simpa using h)
  obtain ⟨h4, h5⟩ := h3 (q ^ k) (pow_pos hq.pos k)
  refine ⟨fun hI => h4 fun P hP h => hI P hP.isPrime ?_ (hq' P hP h), fun hI => h5 fun P hP h hfix => hI ?_⟩
  · rintro rfl
    have := hq' _ hP h
    rw [Ideal.mem_bot] at this
    exact hq.ne_zero (by exact_mod_cast this)
  · intro Q hQ _ hqQ
    exact smul_eq_of_abelian hcomm _ hq P Q hP.isPrime hQ (hq' P hP h) hqQ hfix

end GlobalTheory.SelectIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_idempotents_select_conjugate_primes : ∀ (D : D7), ∃ e : ℕ → 𝓞 D.host.E, (∀ N m : ℕ, 0 < N → 0 < m → (N : 𝓞 D.host.E) ∣ e (N * m) - e N) ∧ (∀ N : ℕ, 0 < N → (N : 𝓞 D.host.E) ∣ e N * e N - e N ∧ (N : 𝓞 D.host.E) ∣ e N * (D.host.conj • e N)) ∧ ∀ q k : ℕ, q.Prime → (InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ e (q ^ k) + D.host.conj • e (q ^ k)) ∧ (¬ InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ 1 - (e (q ^ k) + D.host.conj • e (q ^ k))) := by
  first | exact @GlobalTheory.SelectIdem.exists_select_idem | exact GlobalTheory.SelectIdem.exists_select_idem | (intros; apply GlobalTheory.SelectIdem.exists_select_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HomDual

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rw [← h, ← h, star_star]

theorem pairing_mem (D : D7) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L)
    {u x : Fin N → D.host.E} (hu : u ∈ L) (hx : x ∈ L) :
    ∃ c : 𝓞 D.host.E, (c : D.host.E) = ∑ b, D.host.conj (u b) * x b := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨c, hc⟩ := (hL.2.2 x).1 hx u hu
  refine ⟨c, hc.trans ?_⟩
  simp only [stdH, h]

theorem exists_resolution (D : D7) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hL : SD D L) : ∃ (m : ℕ) (v w : Fin m → Fin N → D.host.E), (∀ i, v i ∈ L) ∧ (∀ i, w i ∈ L) ∧
      ∀ (u : Fin N → D.host.E) (a : Fin N),
        u a = ∑ i, (∑ b, u b * D.host.conj (w i b)) * v i a := by
  letI := D.host.cmStar
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h' : ∀ x : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x := h
  have hh : ∀ x y : Fin N → D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.herm 1 y x = stdH D.host.E N x y := by
    intro x y
    rw [GlobalTheory.DualFamily.herm_one_eq]
    simp only [stdH, h, h', mul_comm]
  have hr : ∀ z : D.host.E, z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ z :=
    fun z => ⟨fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨-, m, v, w, hv, hw, he⟩ := GlobalTheory.exists_dual_family L hL.1
    (fun x hx y hy => by rw [hh, ← hr]; exact (hL.2.2 x).1 hx y hy)
    (fun x hx => (hL.2.2 x).2 fun y hy => by rw [hr, ← hh]; exact hx y hy)
  refine ⟨m, v, w, hv, hw, fun u a => ?_⟩
  have := congrFun (he u) a
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.DualFamily.herm_one_eq, h']
    using this

theorem rank_one_mem (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) {c : D.host.E}
    (hc : c ∈ D.host.AA0) {u : Fin N → D.host.E} (hu : u ∈ L) {v : Fin N' → D.host.E}
    (hv : v ∈ L') :
    c • (Matrix.of fun a b => v a * D.host.conj (u b)) ∈ YYl D L L' := by
  refine Submodule.subset_span ⟨c, hc, _, Submodule.subset_span fun x hx => ?_, rfl⟩
  obtain ⟨e, he⟩ := pairing_mem D hL hu hx
  have : (Matrix.of fun a b => v a * D.host.conj (u b)).mulVec x = e • v := by
    funext a
    change ∑ b, v a * D.host.conj (u b) * x b = (e : D.host.E) * v a
    rw [he, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  exact L'.smul_mem e hv

theorem exists_dual_family_hom : ∀ (D : D7), (∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (r : ℕ) (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ YYl D L L') ∧ (∀ i, y' i ∈ YYl D L L') ∧ ∀ x : Matrix (Fin N') (Fin N) D.host.E, x = ∑ i, hYY D x (y' i) • y i := by
  rintro D ⟨r, a, a', ha, ha', ht⟩ N N' L L' hL hL'
  obtain ⟨m, u, u', hu, hu', eu⟩ := exists_resolution D hL
  obtain ⟨m', v, v', hv, hv', ev⟩ := exists_resolution D hL'
  let Y : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E :=
    fun p => a p.2.2 • Matrix.of fun s t => v p.1 s * D.host.conj (u p.2.1 t)
  let Y' : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E :=
    fun p => a' p.2.2 • Matrix.of fun s t => v' p.1 s * D.host.conj (u' p.2.1 t)
  let e := (Fintype.equivFin (Fin m' × Fin m × Fin r)).symm
  refine ⟨_, Y ∘ e, Y' ∘ e, fun i => rank_one_mem D hL (ha _) (hu _) (hv _),
    fun i => rank_one_mem D hL (ha' _) (hu' _) (hv' _), fun x => ?_⟩
  refine Eq.trans ?_ (e.sum_comp fun p => hYY D x (Y' p) • Y p).symm
  refine Matrix.ext fun s t => ?_
  have eu' : ∀ (z : Fin N → D.host.E) (t : Fin N),
      z t = ∑ i, (∑ b, z b * u' i b) * D.host.conj (u i t) := by
    intro z t
    have := congrArg D.host.conj (eu (fun b => D.host.conj (z b)) t)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, conj_conj] using this
  have hT : ∀ j i k, hYY D x (Y' (j, i, k)) = Algebra.trace D.host.K D.host.E
      ((∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b) * D.host.conj (a' k)) := by
    intro j i k
    unfold hYY
    congr 1
    simp only [Y', Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul, conj_conj,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Matrix.sum_apply, Fintype.sum_prod_type, ev (fun c => x c t) s]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type, eu' (fun b => ∑ c, x c b * D.host.conj (v' j c)) t, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ht (∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b), Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hT]
  simp only [Y, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, smul_mul_assoc]
  congr 1
  ring

end GlobalTheory.HomDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceDual_family_homLattice : ∀ (D : D7), (∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (r : ℕ) (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ YYl D L L') ∧ (∀ i, y' i ∈ YYl D L L') ∧ ∀ x : Matrix (Fin N') (Fin N) D.host.E, x = ∑ i, hYY D x (y' i) • y i := by
  first | exact @GlobalTheory.HomDual.exists_dual_family_hom | exact GlobalTheory.HomDual.exists_dual_family_hom | (intros; apply GlobalTheory.HomDual.exists_dual_family_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfValuationLeOne
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PadicPlaceBound

open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

def smallIdeal {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) : Ideal (𝓞 K) where
  carrier := {a | ‖φ (a : K)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    have h := IsUltrametricDist.norm_add_le_max (φ (a : K)) (φ (b : K))
    have h2 : φ ((a + b : 𝓞 K) : K) = φ (a : K) + φ (b : K) := by simp
    change ‖φ ((a + b : 𝓞 K) : K)‖ < 1
    rw [h2]
    exact h.trans_lt (max_lt ha hb)
  smul_mem' := by
    intro c a ha
    have h2 : φ ((c • a : 𝓞 K) : K) = φ (c : K) * φ (a : K) := by simp
    change ‖φ ((c • a : 𝓞 K) : K)‖ < 1
    rw [h2, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral
      (map_isIntegral_int φ c.isIntegral_coe))).trans_lt ha

theorem mem_smallIdeal {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) (a : 𝓞 K) :
    a ∈ smallIdeal φ ↔ ‖φ (a : K)‖ < 1 := Iff.rfl

theorem norm_int_le_one {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) (a : 𝓞 K) :
    ‖φ (a : K)‖ ≤ 1 :=
  GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int φ a.isIntegral_coe)

theorem smallIdeal_isPrime {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) :
    (smallIdeal φ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    by_contra h
    rw [not_or, mem_smallIdeal, mem_smallIdeal, not_lt, not_lt] at h
    have h2 : φ ((a * b : 𝓞 K) : K) = φ (a : K) * φ (b : K) := by simp
    rw [mem_smallIdeal, h2, norm_mul] at hab
    exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hab)

theorem exists_embedding_smallIdeal_eq {C : Type} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] {l : ℕ} (hl : l.Prime) (hlC : ‖(l : C)‖ < 1) (w : HeightOneSpectrum (𝓞 K))
    (hw : (l : 𝓞 K) ∈ w.asIdeal) : ∃ φ : K →+* C, smallIdeal φ = w.asIdeal := by
  have hsub : (w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ φ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] C)) : Set (K →ₐ[ℚ] C)), (smallIdeal φ.toRingHom : Set (𝓞 K)) := by
    intro a ha
    by_contra hna
    simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe,
      not_exists, mem_smallIdeal, not_lt] at hna
    have h1 : ∀ φ : K →ₐ[ℚ] C, ‖φ (a : K)‖ = 1 := fun φ =>
      le_antisymm (norm_int_le_one φ.toRingHom a) (hna φ)
    have h2 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ C (a : K))
    rw [norm_prod, Finset.prod_eq_one (fun φ _ => h1 φ), ← Algebra.coe_norm_int, map_intCast] at h2
    have h3 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) ∈ w.asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).2 ha (Ideal.absNorm_mem _)
    rw [Ideal.absNorm_span_singleton] at h3
    have h4 : l ∣ (Algebra.norm ℤ a).natAbs := by
      by_contra hnd
      have hc : IsCoprime (l : 𝓞 K) (((Algebra.norm ℤ a).natAbs : ℕ) : 𝓞 K) :=
        Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)
      obtain ⟨u, v, huv⟩ := hc
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (huv ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left u hw) (w.asIdeal.mul_mem_left v h3)))
    obtain ⟨c, hc⟩ := Int.natCast_dvd.2 h4
    rw [hc, Int.cast_mul, Int.cast_natCast, norm_mul] at h2
    have h5 := (mul_le_of_le_one_right (norm_nonneg (l : C))
      (IsUltrametricDist.norm_intCast_le_one C c)).trans_lt hlC
    exact absurd h2 h5.ne
  have φ₀ : K →ₐ[ℚ] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨φ, -, hφ⟩ := (Ideal.subset_union_prime φ₀ φ₀
    (fun φ _ _ _ => smallIdeal_isPrime φ.toRingHom)).1 hsub
  exact ⟨φ.toRingHom, (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hφ).symm⟩

theorem norm_le_one_of_valuation_le_one {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C)
    (w : HeightOneSpectrum (𝓞 K)) (hφ : smallIdeal φ = w.asIdeal) (y : K) (hy : w.valuation K y ≤ 1) :
    ‖φ y‖ ≤ 1 := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer y hy
  have hd' : d ∉ smallIdeal φ := by rw [hφ]; exact hd
  rw [mem_smallIdeal, not_lt] at hd'
  have h1 : ‖φ y‖ * ‖φ (d : K)‖ = ‖φ (n : K)‖ := by
    rw [← norm_mul, ← map_mul]
    exact congrArg (fun z => ‖φ z‖) hnd
  calc ‖φ y‖ ≤ ‖φ y‖ * ‖φ (d : K)‖ := le_mul_of_one_le_right (norm_nonneg _) hd'
    _ = ‖φ (n : K)‖ := h1
    _ ≤ 1 := norm_int_le_one φ n

theorem exists_lamC_eq {l : ℕ} [Fact l.Prime] (σ : K →+* ℂ) (φ : K →+* ℂ_[l]) :
    ∃ lam : Qbar →+* ℂ_[l], ∀ x : K, lamC lam (σ x) = φ x := by
  have hmem : ∀ x : K, σ x ∈ Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
  let σ' : K →+* Qbar := σ.codRestrict Qbar hmem
  letI : Algebra K Qbar := σ'.toAlgebra
  letI : Algebra K ℂ_[l] := φ.toAlgebra
  haveI : IsScalarTower ℚ K Qbar := IsScalarTower.of_algebraMap_eq fun q =>
    ((eq_ratCast (algebraMap ℚ Qbar) q).trans (map_ratCast σ' q).symm).trans
      (congrArg σ' (eq_ratCast (algebraMap ℚ K) q).symm)
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic K Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let lam : Qbar →ₐ[K] ℂ_[l] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨lam.toRingHom, fun x => ?_⟩
  unfold lamC
  rw [dite_eq_left (hmem x)]
  exact lam.commutes x

theorem norm_prime_padicComplex (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)),
    ← Padic.norm_p]
  exact PadicAlgCl.norm_extends l _

theorem neg_mul_vw_le_vw : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (x : K) (l : ℕ) [Fact l.Prime] (w : Formalism.PairingDivisionLocalBalance.Pl K) (e : ℝ), x ≠ 0 → (l : 𝓞 K) ∈ w.asIdeal → (∀ lam : Qbar →+* ℂ_[l], ‖lamC lam (σ x)‖ ≤ (l : ℝ) ^ e) → -(e * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w x : ℝ) := by
  intro K _ _ σ x l hl w e hx hw h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := one_pos.trans hl1
  have hlK : (l : K) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  obtain ⟨φ, hφ⟩ := exists_embedding_smallIdeal_eq (C := ℂ_[l]) hl.out
    (by rw [norm_prime_padicComplex]; exact inv_lt_one_of_one_lt₀ hl1) w hw
  obtain ⟨lam, hlam⟩ := exists_lamC_eq σ φ
  have hb := h lam
  rw [hlam] at hb
  have hvx : w.valuation K x = WithZero.exp (-Formalism.DivisionValues.vw w x) := GlobalTheory.Idele.valuation_eq_exp_neg_count w hx
  have hvl : w.valuation K (l : K) = WithZero.exp (-Formalism.DivisionValues.vw w (l : K)) :=
    GlobalTheory.Idele.valuation_eq_exp_neg_count w hlK
  set n := Formalism.DivisionValues.vw w x
  set m := Formalism.DivisionValues.vw w (l : K)
  have hm : 0 ≤ m := by
    have h1 : w.valuation K (l : K) ≤ 1 := by
      simpa using w.valuation_le_one (K := K) (l : 𝓞 K)
    rw [hvl, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  have hy : w.valuation K ((l : K) ^ n / x ^ m) ≤ 1 := by
    rw [map_div₀, map_zpow₀, map_zpow₀, hvx, hvl, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul,
      ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp only [smul_eq_mul]
    nlinarith
  have h1 := norm_le_one_of_valuation_le_one φ w hφ _ hy
  have hφx : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx)
  rw [map_div₀, map_zpow₀, map_zpow₀, norm_div, norm_zpow, norm_zpow, map_natCast,
    norm_prime_padicComplex, div_le_one (zpow_pos hφx _)] at h1
  have h2 : ‖φ x‖ ^ m ≤ ((l : ℝ) ^ e) ^ m := zpow_le_zpow_left₀ hm hφx.le hb
  have h3 := h1.trans h2
  rw [inv_zpow', ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hl0.le,
    Real.rpow_le_rpow_left_iff hl1] at h3
  push_cast at h3
  linarith

end GlobalTheory.PadicPlaceBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowth
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GaussCauchy

theorem factor_le (A B : ℝ) (hA : 0 < A) (n : ℕ) (hn : (n : ℝ) ≤ 2 * B) :
    ((n.factorial : ℝ)) ^ 2 * Real.exp n / (A * n / Real.pi) ^ n
      ≤ (2 * Real.exp 1 * Real.pi * B / A) ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h
  have hpi := Real.pi_pos
  rw [div_le_iff₀ (by positivity), ← mul_pow]
  have h1 : 2 * Real.exp 1 * Real.pi * B / A * (A * n / Real.pi) = (2 * B) * n * Real.exp 1 := by
    field_simp
  have h2 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h3 : (n : ℝ) ^ n ≤ (2 * B) ^ n := pow_le_pow_left₀ hn0.le hn n
  rw [h1, mul_pow, mul_pow (2 * B), ← Real.exp_nat_mul, mul_one, sq]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_mul (h2.trans h3) h2 (by positivity) ((by positivity : (0 : ℝ) ≤ (n : ℝ) ^ n).trans h3)

theorem pderivIter_sq_le {ι : Type*} [DecidableEq ι] [Fintype ι] (F : (ι → ℂ) → ℂ) (S A B : ℝ)
    (hA : 0 < A) (hS : 0 ≤ S) (hF : Differentiable ℂ F)
    (hb : ∀ z, ‖F z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ k, ‖z k‖ ^ 2) / A))
    (α : ι →₀ ℕ) (hα : ∀ k, (α k : ℝ) ≤ 2 * B) :
    ‖pderivIter α F 0‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (∑ k, α k) := by
  have hpi := Real.pi_pos
  have hsq : ∀ k, Real.sqrt (A * α k / Real.pi) ^ 2 = A * α k / Real.pi := fun k =>
    Real.sq_sqrt (by positivity)
  have h := norm_pderivIter_le_of_differentiable (F := F) (a := 0)
    (r := fun k => Real.sqrt (A * α k / Real.pi))
    (M := Real.sqrt (S * Real.exp (∑ k, (α k : ℝ)))) α (fun k => Real.sqrt_nonneg _)
    (fun k hk => by
      have : (0 : ℝ) < α k := by exact_mod_cast Nat.pos_of_ne_zero hk
      exact Real.sqrt_pos.mpr (by positivity)) hF
    (fun z hz => by
      apply Real.le_sqrt_of_sq_le
      refine (hb z).trans (le_of_eq ?_)
      congr 2
      simp only [Pi.zero_apply, sub_zero] at hz
      simp only [hz, hsq, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp)
  refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans ?_
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), ← Finset.prod_pow, ← Finset.prod_pow,
    Real.exp_sum, ← Finset.prod_pow_eq_pow_sum, mul_left_comm, mul_div_assoc,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_) hS
  rw [← pow_mul, mul_comm (α k) 2, pow_mul, hsq]
  exact factor_le A B hA _ (hα k)

noncomputable def curry (D : D7) (N N' : ℕ) :
    (D.what₂.Tau × Fin N' × Fin N → ℂ) →ₗ[ℂ] VC D N N' where
  toFun w := fun τ i j => w (τ, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem curry_single (D : D7) (N N' : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    curry D N N' (Pi.single k 1) = coordV D k := by
  funext τ i j
  obtain ⟨a, b, c⟩ := k
  simp [curry, coordV, Pi.single_apply, Prod.ext_iff]

theorem factorial_mul_taylor (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (hG : Differentiable ℂ G)
    (α : Mono D N N') :
    (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α
      = pderivIter α (fun w => G (curry D N N' w)) 0 := by
  have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have han : AnalyticAt ℂ G 0 := SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _)
  rw [taylor, mul_div_cancel₀ _ hne, pderivIter, pderivList, lineDerivList_comp_linearMap,
    ← lineDerivList_ofFn han]
  simp only [map_zero, List.map_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [curry_single]

theorem monomial_deriv_bound : ∀ (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ α : Mono D N N', (∀ k, (α k : ℝ) ≤ 2 * B) → ‖(α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (α.sum fun _ n => n) := by
  intro D N N' G S A B hA _ hS hG hb α hα
  rw [factorial_mul_taylor D N N' G hG, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  refine pderivIter_sq_le _ S A B hA hS
    (hG.comp (LinearMap.toContinuousLinearMap (curry D N N')).differentiable) (fun z => ?_) α hα
  simp only [Fintype.sum_prod_type]
  exact hb (curry D N N' z)

end GlobalTheory.GaussCauchy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowthStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomialDeriv_cauchy_bound_gaussianGrowth : ∀ (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ α : Mono D N N', (∀ k, (α k : ℝ) ≤ 2 * B) → ‖(α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (α.sum fun _ n => n) := by
  first | exact @GlobalTheory.GaussCauchy.monomial_deriv_bound | exact GlobalTheory.GaussCauchy.monomial_deriv_bound | (intros; apply GlobalTheory.GaussCauchy.monomial_deriv_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalTransitionDetMulConjEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalTransitionDetMulConjEqOne
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

noncomputable def hYYLeft (D : D7) {N N' : ℕ} (y : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] D.host.K where
  toFun x := hYY D x y
  map_add' x x' := by
    simp only [hYY, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' c x := by
    simp only [hYY, Matrix.smul_apply, smul_mul_assoc, RingHom.id_apply]
    rw [← map_smul, Finset.smul_sum]
    simp only [Finset.smul_sum]

theorem hYY_herm (D : D7) (h : TraceMapNormalisation D) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D y x : D.host.K) : D.host.E) =
      starRingEnd ℂ (D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E)) := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  unfold hYY
  rw [← h, ← h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc, Complex.conj_conj]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem onB_expand (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b)
    (x : Matrix (Fin N') (Fin N) D.host.E) : x = ∑ i, hYY D x (b i) • b i := by
  have hx : x ∈ Submodule.span D.host.K (Set.range b) := by rw [hb.2]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.K).1 hx
  have h1 : ∀ k, hYY D x (b k) = c k := by
    intro k
    change hYYLeft D (b k) x = c k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum]
    have h2 : ∀ i, hYYLeft D (b k) (c i • b i) = if i = k then c i else 0 := by
      intro i
      rw [map_smul]
      change c i • hYY D (b i) (b k) = _
      rw [hb.1 i k]
      split_ifs <;> simp
    simp only [h2]
    simp
  simp only [h1]
  exact hc.symm

theorem onB_parseval (D : D7) (h : TraceMapNormalisation D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : OnB D b) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) =
      ∑ i, D.host.φ₀ ((hYY D x (b i) : D.host.K) : D.host.E) *
        starRingEnd ℂ (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)) := by
  have h1 : hYY D x y = ∑ i, hYY D x (b i) * hYY D (b i) y := by
    change hYYLeft D y x = _
    conv_lhs => rw [onB_expand D b hb x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  have h2 := congrArg (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h2
  refine h2.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, ← hYY_herm D h y (b i)]
  rfl

theorem det_onB_mul_conj : ∀ (D : D7), admG1 D → ∀ (N N' r : ℕ) (b₀ b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b₀ → OnB D b → (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) * D.host.conj (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) = 1 := by
  intro D hD N N' r b₀ b hb₀ hb
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  set M : Matrix (Fin r) (Fin r) D.host.K := Matrix.of fun i j => hYY D (b j) (b₀ i) with hM
  let ψ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have hA : (ψ.mapMatrix M).transpose * (starRingEnd ℂ).mapMatrix (ψ.mapMatrix M) = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    have h1 := onB_parseval D hD.2 b₀ hb₀ (b j) (b k)
    rw [hb.1 j k] at h1
    refine Eq.trans h1.symm ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact map_one ψ
    · exact map_zero ψ
  have hdet := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det (starRingEnd ℂ), ← RingHom.map_det ψ, Matrix.det_one] at hdet
  apply D.host.φ₀.injective
  rw [map_mul, hc, map_one]
  exact hdet

end GlobalTheory.NormSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalTransitionDetMulConjEqOneStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalTransition_det_mul_conj_eq_one : ∀ (D : D7), admG1 D → ∀ (N N' r : ℕ) (b₀ b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b₀ → OnB D b → (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) * D.host.conj (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) = 1 := by
  first | exact @GlobalTheory.NormSum.det_onB_mul_conj | exact GlobalTheory.NormSum.det_onB_mul_conj | (intros; apply GlobalTheory.NormSum.det_onB_mul_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSelfDualClassesRootDiscr
open NumberField Module Submodule
open ReciprocityTheory.ChartRestriction.G.FD (herm cc fdeg rdE)

namespace GlobalTheory

namespace RootClassCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIntegral_herm_iff {n : ℕ} (x y : Fin n → E) :
    IsIntegral ℤ (herm 1 y x) ↔ IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i) := by
  rw [DualFamily.herm_one_eq]
  simp only [cc, mul_comm]

theorem mul_conjTranspose_eq_one {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (h : ∀ x y, herm 1 (γ.mulVec x) (γ.mulVec y) = herm 1 x y) :
    γ * (γ.map (IsCMField.complexConj E)).transpose = 1 := by
  rw [mul_eq_one_comm]
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rw [DualFamily.herm_one_eq, DualFamily.herm_one_eq] at this
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, cc] at this
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mul_comm, Matrix.one_apply]
  rw [this]
  simp [Pi.single_apply, eq_comm]

omit [IsCMField E] in
theorem rdE_eq : rdE E = |(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := rfl

omit [IsCMField E] in
theorem one_le_rootDiscr : 1 ≤ |(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := by
  refine Real.one_le_rpow ?_ (by positivity)
  exact_mod_cast Int.one_le_abs (discr_ne_zero E)

theorem exists_bounded_basis {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hint : ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ L, IsIntegral ℤ (herm 1 x y)) → x ∈ L) :
    ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ L) ∧ LinearIndependent E v ∧
      ∀ (σ : E →+* ℂ) (i k : Fin n), ‖σ (herm 1 (v i) (v k))‖ ≤
        4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2 := by
  obtain ⟨v, hv, hli, -, hle⟩ := exists_short_vectors L hfg hint hdual
  obtain ⟨s, hs1, hs2, -⟩ := euclidean_basis_exists E (Fin n → E) _ v hli (by
    simp [ShortVectors.finrank_eq])
  have hsr : s.card = n := by simpa using hs1
  let e : Fin n ≃ s := (s.equivFinOfCardEq hsr).symm
  have h3 : ((fdeg E : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (fdeg E : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_natCast]
    norm_num
  refine ⟨fun i => v (e i), fun i => hv _, hs2.comp e e.injective, fun σ i k => ?_⟩
  refine (SelfDualClasses.norm_herm_le σ _ _ _ (hle _ σ) (hle _ σ)).trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, mul_pow, h3]
  ring

theorem bound_le (f n : ℕ) {r : ℝ} (hf : 0 < f) (hr : 1 ≤ r) :
    (1 + 2 * (4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2)) ^ (2 * f * n ^ 2) *
      (n * (4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2)) ^ (2 * f * n ^ 2) ≤
      (3 * (((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2)) ^ (3 * (2 * f) * n ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set p : ℝ := ((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2 with hp
  have hp' : p = 4 * (f : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2 := by rw [hp]; push_cast; ring
  have hB : 4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2 = f * p := by rw [hp']; ring
  have h1 : (f : ℝ) ^ 2 * n ≤ p := by
    rw [hp']
    have h2 : (n : ℝ) ≤ n ^ 4 := le_self_pow₀ hn' (by norm_num)
    have h3 : 1 ≤ r ^ 2 := one_le_pow₀ hr
    calc (f : ℝ) ^ 2 * n = 1 * (f : ℝ) ^ 2 * n * 1 := by ring
      _ ≤ _ := by gcongr; norm_num
  have h4 : 1 ≤ (f : ℝ) ^ 2 * n := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf') hn'
  have h5 : 1 ≤ p := h4.trans h1
  have h6 : 1 ≤ f * p := one_le_mul_of_one_le_of_one_le hf' h5
  rw [hB, ← mul_pow, mul_assoc 3, pow_mul _ 3]
  gcongr
  calc (1 + 2 * (f * p)) * (n * (f * p)) ≤ (3 * (f * p)) * (n * (f * p)) := by
        gcongr; linarith
    _ = 3 * ((f : ℝ) ^ 2 * n) * p ^ 2 := by ring
    _ ≤ 27 * p * p ^ 2 := by gcongr; norm_num
    _ = _ := by ring

end RootClassCount


open RootClassCount in
theorem exists_finset_selfDual_classes_rootDiscr :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ R : Finset (Submodule (𝓞 E) (Fin n → E)),
      (R.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
        (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i)) →
        ∃ L₀ ∈ R, ∃ γ : Matrix (Fin n) (Fin n) E,
          γ * (γ.map (IsCMField.complexConj E)).transpose = 1 ∧
          ∀ x, x ∈ L₀ ↔ γ.mulVec x ∈ L := by
  intro E _ _ _ n
  obtain ⟨R, -, h2, h3⟩ := ClassCount.exists_finset_classes (K := E) (r := n) (G := 1)
    {L | L.FG ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (herm 1 y x)}
    (B := 4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2) (by positivity) fun L hL =>
      ⟨by simp, fun x hx => (hL.2 x).1 hx,
        exists_bounded_basis L hL.1 (fun x hx => (hL.2 x).1 hx) fun x hx => (hL.2 x).2 hx⟩
  refine ⟨R, h3.trans ?_, fun L hfg _ hsd => ?_⟩
  · have h := bound_le (fdeg E) n ClassCount.fdeg_pos (one_le_rootDiscr (E := E))
    rw [← ShortVectors.finrank_eq] at h
    rw [rdE_eq, ← ShortVectors.finrank_eq]
    exact h
  · obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := h2 L ⟨hfg, fun y => by
      simp only [isIntegral_herm_iff]; exact hsd y⟩
    exact ⟨L₀, hL₀, γ, mul_conjTranspose_eq_one _ hγ, hm⟩

end GlobalTheory
end
