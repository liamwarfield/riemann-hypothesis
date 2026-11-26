module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.ExpCond

theorem not_mem_sq_of_not_dvd_discr {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro h2
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hvZ : ((p : ℤ) : 𝓞 E) ∈ w.asIdeal := by simpa using hv
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpZ).mp hd w.asIdeal w.isPrime hvZ
  have hunder : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    symm
    refine (PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible).eq_of_le
      (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_comap.mpr (by simpa using hv)
  let := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under ℤ) w.asIdeal
  have hloc := ((Algebra.isUnramifiedAt_iff_map_eq ℤ (w.asIdeal.under ℤ) w.asIdeal).mp hun).2
  have h1 := (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot Ideal.map_comap_le).mpr hloc
  refine (Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).mpr ?_ h1
  have hunder' : Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal = Ideal.span {(p : ℤ)} := hunder
  rw [hunder', Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  simpa using h2

variable {E : Type} [Field E] [NumberField E]

theorem mem_below (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) : (p : OF E) ∈ (below w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  show (p : OF E) ∈ Ideal.comap (algebraMap (OF E) (𝓞 E)) w.asIdeal ↔ _
  rw [Ideal.mem_comap, map_natCast]

theorem emult_zero (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (h : (p : 𝓞 E) ∉ w.asIdeal) :
    emultiplicity (below w).asIdeal (Ideal.span {(p : OF E)}) = 0 := by
  rw [emultiplicity_eq_zero, Ideal.dvd_span_singleton, mem_below]
  exact h

theorem emult_one (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (h : (p : 𝓞 E) ∈ w.asIdeal) :
    emultiplicity (below w).asIdeal (Ideal.span {(p : OF E)}) = 1 := by
  have hle : Ideal.map (algebraMap (OF E) (𝓞 E)) (below w).asIdeal ≤ w.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (fun x hx => hx)
  have hdvd : (below w).asIdeal ^ 1 ∣ Ideal.span {(p : OF E)} := by
    rw [pow_one, Ideal.dvd_span_singleton, mem_below]
    exact h
  have hndvd : ¬ (below w).asIdeal ^ (1 + 1) ∣ Ideal.span {(p : OF E)} := by
    intro h2
    rw [Ideal.dvd_span_singleton] at h2
    have hm := Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at hm
    have hsq : (Ideal.map (algebraMap (OF E) (𝓞 E)) (below w).asIdeal) ^ (1 + 1) ≤ w.asIdeal ^ 2 := by
      rw [show (1 + 1 : ℕ) = 2 from rfl, pow_two, pow_two]
      exact Ideal.mul_mono hle hle
    exact not_mem_sq_of_not_dvd_discr hp hd w h (hsq hm)
  have := (emultiplicity_eq_coe (n := 1)).mpr ⟨hdvd, hndvd⟩
  simpa using this

theorem not_mem_of_ne (w : HeightOneSpectrum (𝓞 E)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h : (p : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∉ w.asIdeal := by
  intro hq'
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨u, v, huv⟩ := hc
  have e : (u : 𝓞 E) * (p : 𝓞 E) + (v : 𝓞 E) * (q : 𝓞 E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) huv
    push_cast at this
    exact this
  have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
    rw [← e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ hq')
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem emult_cond (v v0 : HeightOneSpectrum (OF E)) (a b c d : ℕ) :
    emultiplicity v.asIdeal (Ideal.span {((a * b * c * d : ℕ) : OF E)} ^ 2 * v0.asIdeal) =
      2 * (emultiplicity v.asIdeal (Ideal.span {(a : OF E)}) + emultiplicity v.asIdeal (Ideal.span {(b : OF E)}) +
        emultiplicity v.asIdeal (Ideal.span {(c : OF E)}) + emultiplicity v.asIdeal (Ideal.span {(d : OF E)})) +
        emultiplicity v.asIdeal v0.asIdeal := by
  have hv := v.prime
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    emultiplicity_mul hv, emultiplicity_pow hv, emultiplicity_mul hv, emultiplicity_mul hv,
    emultiplicity_mul hv]
  push_cast
  ring

theorem emult_ne {v v0 : HeightOneSpectrum (OF E)} (h : v ≠ v0) : emultiplicity v.asIdeal v0.asIdeal = 0 := by
  rw [emultiplicity_eq_zero, Ideal.dvd_iff_le]
  intro hle
  apply h
  exact HeightOneSpectrum.ext ((v0.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)

theorem emult_self (v : HeightOneSpectrum (OF E)) : emultiplicity v.asIdeal v.asIdeal = 1 := by
  simpa using emultiplicity_pow_self_of_prime v.prime 1

end GlobalTheory.LamTie.ExpCond

namespace GlobalTheory.LamTie

open ExpCond

theorem expIn_cond0 : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), PlacesOk H q0 w0 →
    ∀ w : HeightOneSpectrum (𝓞 H.E), (Over4 H w → expIn (cond0 H w0) (below w) = 2) ∧
      (below w = below w0 → ¬ Over4 H w ∧ expIn (cond0 H w0) (below w) = 1) ∧
      (¬ Over4 H w → below w ≠ below w0 → expIn (cond0 H w0) (below w) = 0) := by
  intro R H q0 w0 hP w
  obtain ⟨hw0, hdist, hspl⟩ := hP
  have hq0 : (q0 : 𝓞 H.E) ∈ w0.asIdeal := hw0
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, or_false] at hdist
  have pr : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := fun p hp => (hspl p hp).1
  have dc : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ¬ (p : ℤ) ∣ discr H.E := fun p hp => (hspl p hp).2.2.1
  have uniq : ∀ x ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ y ∈ [H.g 0, H.g 1, H.pde, H.pde', q0],
      (x : 𝓞 H.E) ∈ w.asIdeal → (y : 𝓞 H.E) ∈ w.asIdeal → x = y := by
    intro x hx y hy mx my
    by_contra hxy
    exact not_mem_of_ne w (pr x hx) (pr y hy) hxy mx my
  have key : emultiplicity (below w).asIdeal (cond0 H w0) =
      2 * (emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)})) +
      emultiplicity (below w).asIdeal (below w0).asIdeal :=
    emult_cond (below w) (below w0) (H.g 0) (H.g 1) H.pde H.pde'
  have qw : below w = below w0 → (q0 : 𝓞 H.E) ∈ w.asIdeal := fun heq =>
    (mem_below w q0).mp (heq ▸ (mem_below w0 q0).mpr hq0)
  have toExp : ∀ n : ℕ, emultiplicity (below w).asIdeal (cond0 H w0) = n → expIn (cond0 H w0) (below w) = n :=
    fun n h => multiplicity_eq_of_emultiplicity_eq_some h
  have m0 : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m1 : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m2 : (H.pde : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m3 : (H.pde' : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have n0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) = 0 :=
    emult_zero w
  have n1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) = 0 :=
    emult_zero w
  have n2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) = 0 :=
    emult_zero w
  have n3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)}) = 0 :=
    emult_zero w
  have u := fun x (hx : x ∈ [H.g 0, H.g 1, H.pde, H.pde', q0]) y (hy : y ∈ [H.g 0, H.g 1, H.pde, H.pde', q0])
    (hne : x ≠ y) (mx : (x : 𝓞 H.E) ∈ w.asIdeal) (my : (y : 𝓞 H.E) ∈ w.asIdeal) => hne (uniq x hx y hy mx my)
  refine ⟨fun hO => ?_, fun heq => ?_, fun hO hne => ?_⟩
  · have hne : below w ≠ below w0 := by
      intro heq
      have hq := qw heq
      rcases hO with ⟨k, hk⟩ | hk | hk
      · fin_cases k
        · have hk : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal := hk
          exact u _ (by simp) _ (by simp) (by omega) hk hq
        · have hk : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal := hk
          exact u _ (by simp) _ (by simp) (by omega) hk hq
      · exact u _ (by simp) _ (by simp) (by omega) hk hq
      · exact u _ (by simp) _ (by simp) (by omega) hk hq
    apply toExp
    rw [key, emult_ne hne]
    rcases hO with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · have hk : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal := hk
        rw [m0 hk, n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
        norm_num
      · have hk : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal := hk
        rw [m1 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
        norm_num
    · have hk : (H.pde : 𝓞 H.E) ∈ w.asIdeal := hk
      rw [m2 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
      norm_num
    · have hk : (H.pde' : 𝓞 H.E) ∈ w.asIdeal := hk
      rw [m3 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
      norm_num
  · have hq := qw heq
    have a0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    refine ⟨?_, ?_⟩
    · rintro (⟨k, hk⟩ | hk | hk)
      · fin_cases k
        · exact a0 hk
        · exact a1 hk
      · exact a2 hk
      · exact a3 hk
    · apply toExp
      rw [key, n0 a0, n1 a1, n2 a2, n3 a3, heq, emult_self]
      norm_num
  · have a0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inl ⟨0, h⟩)
    have a1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inl ⟨1, h⟩)
    have a2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inr (Or.inl h))
    have a3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inr (Or.inr h))
    apply toExp
    rw [key, n0 a0, n1 a1, n2 a2, n3 a3, emult_ne hne]
    norm_num

end GlobalTheory.LamTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlacesStatement
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_exponent_at_places : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), PlacesOk H q0 w0 → ∀ w : HeightOneSpectrum (𝓞 H.E), (Over4 H w → expIn (cond0 H w0) (below w) = 2) ∧ (below w = below w0 → ¬ Over4 H w ∧ expIn (cond0 H w0) (below w) = 1) ∧ (¬ Over4 H w → below w ≠ below w0 → expIn (cond0 H w0) (below w) = 0) := by
  first | exact @GlobalTheory.LamTie.expIn_cond0 | exact GlobalTheory.LamTie.expIn_cond0 | (intros; apply GlobalTheory.LamTie.expIn_cond0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturated
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturated
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

theorem ainf_exists_l_mul_of_coeff_zero (a : Ainf l) (h : a.coeff 0 = 0) :
    ∃ b : Ainf l, a = (l : Ainf l) * b := by
  have hv := WittVector.eq_iterate_verschiebung (n := 1) (x := a) (fun i hi => by
    rw [Nat.lt_one_iff.1 hi]; exact h)
  have hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l) := by
    rw [WittVector.frobenius_eq_map_frobenius]
    exact WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective
  obtain ⟨c, hc⟩ := hsurj (a.shift 1)
  refine ⟨c, ?_⟩
  rw [hv, Function.iterate_one, ← hc, WittVector.verschiebung_frobenius, mul_comm]

theorem coeff_zero_l_mul {R : Type} [CommRing R] [CharP R l] (x : WittVector l R) :
    ((l : WittVector l R) * x).coeff 0 = 0 := by
  change WittVector.constantCoeff ((l : WittVector l R) * x) = 0
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem isUnit_inclW_per_and_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → IsUnit (inclW l τ) ∧ (∀ g : GQ l, IsUnit (inclW l (Per.σA g τ))) ∧
      ∀ (k : ℕ) (a : Ainf l), ((l : ℕ) : WCb l) ^ k ∣ inclW l a → ((l : ℕ) : Ainf l) ^ k ∣ a := by
  intro l _ K bk τ hτ
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  have hε1 : ε ≠ 1 := by
    rintro rfl
    obtain ⟨-, hu⟩ := hε
    exact hu (by rw [map_one]; simp)
  have hc0 : τ.coeff 0 ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x => WittVector.constantCoeff x) hφ
    change (WittVector.frobenius τ).coeff 0 = _ at h1
    rw [WittVector.coeff_frobenius_charP, h0, zero_pow (Fact.out : l.Prime).ne_zero, map_mul, map_sub, map_one] at h1
    change 0 = WittVector.constantCoeff (η : Ainf l) * ((WittVector.teichmuller l ε).coeff 0 - 1) at h1
    rw [WittVector.teichmuller_coeff_zero] at h1
    have hη : IsUnit (WittVector.constantCoeff (η : Ainf l)) := η.isUnit.map _
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact hη.ne_zero h
    · exact hε1 (sub_eq_zero.1 h)
  have hU : IsUnit (inclW l τ) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change algebraMap (OCb l) (Cb l) (τ.coeff 0) ≠ 0
    exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hc0
  refine ⟨hU, fun g => ?_, ?_⟩
  · rw [← galW_inclW]
    exact hU.map (galW l g)
  · intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ⟨c, hc⟩
      have h0 : a.coeff 0 = 0 := by
        have h1 : (inclW l a).coeff 0 = 0 := by
          rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
        change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
        exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
      obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
      have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
        have h1 := congrArg (fun x : WCb l => x.coeff 1) h
        simp [WittVector.coeff_p] at h1
      have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
        refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
        rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
      exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturatedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → IsUnit (inclW l τ) ∧ (∀ g : GQ l, IsUnit (inclW l (Per.σA g τ))) ∧ ∀ (k : ℕ) (a : Ainf l), ((l : ℕ) : WCb l) ^ k ∣ inclW l a → ((l : ℕ) : Ainf l) ^ k ∣ a := by
  first | exact @GlobalTheory.BSP.isUnit_inclW_per_and_saturated | exact GlobalTheory.BSP.isUnit_inclW_per_and_saturated | (intros; apply GlobalTheory.BSP.isUnit_inclW_per_and_saturated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearCoefficientMapCocycles
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.ResSel.CoefMap

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R' M']
  (rho : Representation R Γ M) (rho' : Representation R' Γ M') (u : M →ₛₗ[σ] M') (hu : Continuous u)
  (he : ∀ g m, u (rho g m) = rho' g (u m))

def semilinearCoefficientMapCocycles : Z1 rho →ₛₗ[σ] Z1 rho' where
  toFun z := ⟨fun g => u (z.1 g), hu.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add (f := _), he]⟩
  map_add' z w := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' c z := Subtype.ext (funext fun g => map_smulₛₗ u _ _)

def slH1 : H1 rho →ₛₗ[σ] H1 rho' :=
  Submodule.mapQ _ _ (semilinearCoefficientMapCocycles rho rho' u hu he) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hz
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    change u (z.1 g) = _
    rw [show z.1 g = _ from hm g, map_sub, he]

theorem res_slH1 {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (slH1 rho rho' u hu he x) =
      slH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem slH1_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) :
    slH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_slH1 rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (map_zero _))

end General

section Coef

variable {O K K' : Type} [CommRing O] [CommRing K] [CommRing K'] [Algebra O K] [Algebra O K'] (f : K →ₐ[O] K') (r : ℕ)

def vecMap : (Fin r → K) →ₛₗ[(f : K →+* K')] (Fin r → K') where
  toFun m a := f (m a)
  map_add' m m' := funext fun a => map_add f _ _
  map_smul' c m := funext fun a => map_mul f _ _

theorem vecMap_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (g : Γ) (m : Fin r → K) :
    vecMap f r (repOn ρ (1 : Γ →* Kˣ) K g m) = repOn ρ (1 : Γ →* K'ˣ) K' g (vecMap f r m) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vecMap, repOn, matAct, map_sum]

end Coef

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {K K' : Type} [CommRing K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
  [CommRing K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K'] (f : K →ₐ[X.O0 i] K')

theorem slH1_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v) :
    slH1 ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype) ((repOn ρ (1 : GE N →* K'ˣ) K').comp (DecV N v).subtype)
      (vecMap f r) continuous_of_discreteTopology (fun g m => vecMap_repOn f ρ g.1 m) x ∈
      bkOn bkP i ρ (1 : GE N →* K'ˣ) K' v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (vecMap f r) continuous_of_discreteTopology
        (fun g m => vecMap_repOn f ρ g.1 m) z, c, y, f b, hc, hy, fun g a => ?_, rfl⟩
      change f ((z : ↥(DecV N v) → Fin r → K) g a) = _
      rw [hz, smul_eq_mul, smul_eq_mul, map_mul, AlgHom.commutes]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem slH1_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ (1 : GE N →* Kˣ) K))
    (hx : x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) :
    slH1 (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecMap f r) continuous_of_discreteTopology
      (vecMap_repOn f ρ) x ∈ selOn bkP i ρ (1 : GE N →* K'ˣ) K' Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_slH1 (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecMap f r) continuous_of_discreteTopology
    (vecMap_repOn f ρ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact slH1_mem_bkOn bkP i ρ f v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

theorem cl_mem_selOn_of_algHom (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (bkP : BKPh X) (i : X.Tw) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (K K' : Type)
    [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
    [Field K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K'] (f : K →ₐ[X.O0 i] K')
    (Q : Finset (PlE D.host)) (x : Z1 (red i K ρ)) (x' : Z1 (red i K' ρ)) (h : ∀ g a, x'.1 g a = f (x.1 g a))
    (hx : cl x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) : cl x' ∈ selOn bkP i ρ (1 : GE N →* K'ˣ) K' Q := by
  have e : x' = semilinearCoefficientMapCocycles _ _ (vecMap f D.R.r) continuous_of_discreteTopology (vecMap_repOn f ρ) x :=
    Subtype.ext (funext fun g => funext fun a => h g a)
  rw [e]
  exact slH1_mem_selOn bkP i ρ f Q (cl x) hx

end GlobalTheory.ResSel.CoefMap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoLMk
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevel

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def ioL (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) :
    (↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) →ₗ[O] (V ⧸ L.T) :=
  (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T).liftQ
    (L.T.mkQ ∘ₗ (((algebraMap O LL ϖ)⁻¹ ^ r • (LinearMap.id : V →ₗ[LL] V)).restrictScalars O) ∘ₗ
      L.T.subtype) (by
    intro x hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.coe_smul,
      LinearMap.coe_restrictScalars, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [← algebraMap_smul LL (ϖ ^ r) (y : V), smul_smul, map_pow, ← mul_pow]
    rcases eq_or_ne (algebraMap O LL ϖ) 0 with h | h
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simpa using y.2
      · rw [h, inv_zero, zero_mul, zero_pow hr.ne', zero_smul]; exact L.T.zero_mem
    · rw [inv_mul_cancel₀ h, one_pow, one_smul]; exact y.2)

theorem ioL_mk (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (y : ↥L.T) :
    ioL L ϖ r (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r • (y : V)) := rfl

variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def cupQ (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O)
    (r : ℕ) (c : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (c' : G → ↥L'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L'.T)) (x : G × G) : LL :=
  (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (c x.1)) (ρ' x.1 (Formalism.MainNotions.LocalSituation.liftQ L' _ (c' x.2)))

end GlobalTheory.BKFinLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusD
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusD
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.CMType

theorem isCMType_conj {E : Type} [Field E] {I : Type} (φ : I → E →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) :
    IsCMType fun i => ComplexEmbedding.conjugate (φ i) := by
  unfold IsCMType
  intro σ
  have hmk : ∀ j, InfinitePlace.mk (φ j) = InfinitePlace.mk σ ↔
      (σ = ComplexEmbedding.conjugate (φ j) ∨
        σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j))) := by
    intro j
    have cc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j)) = φ j := star_star (φ j)
    rw [InfinitePlace.mk_eq_iff, cc]
    constructor
    · rintro (e | e)
      · exact Or.inr e.symm
      · exact Or.inl e.symm
    · rintro (e | e)
      · exact Or.inr e.symm
      · exact Or.inl e.symm
  obtain ⟨i, hi⟩ := h.2 (InfinitePlace.mk σ)
  exact ⟨i, (hmk i).1 hi, fun j hj => h.1 (((hmk j).2 hj).trans hi.symm)⟩

theorem phi_cmType : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R),
    IsCMType (phi H) ∧ ∀ g g', phi H g H.sqrtMinusD = phi H g' H.sqrtMinusD := by
  intro R H
  obtain ⟨_, -, ⟨-, -, -, -, hbij⟩, -, hsq, -⟩ := GlobalTheory.Mem.HostCM.host_cm_embedding_properties R H
  refine ⟨isCMType_conj (embPsi H) hbij, fun g g' => ?_⟩
  show ComplexEmbedding.conjugate (embPsi H g) H.sqrtMinusD =
    ComplexEmbedding.conjugate (embPsi H g') H.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hsq g, hsq g']

end GlobalTheory.LamTie.CMType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusDStatement
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateEmbedding_isCMType_sqrtMinusD : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsCMType (phi H) ∧ ∀ g g', phi H g H.sqrtMinusD = phi H g' H.sqrtMinusD := by
  first | exact @GlobalTheory.LamTie.CMType.phi_cmType | exact GlobalTheory.LamTie.CMType.phi_cmType | (intros; apply GlobalTheory.LamTie.CMType.phi_cmType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulSubMemOfRootsModPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulSubMemOfRootsModPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem pow_mul_sub_mem_of_roots_mod_pow :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (p : Polynomial R) (x y b lam : R) (n : ℕ),
      p.eval x ∈ I ^ n → p.eval y ∈ I ^ n → x - y ∈ I →
        b * (Polynomial.derivative p).eval x - lam ∈ I → lam ^ n * (x - y) ∈ I ^ n := by
  intro R _ I p x y b lam n hx hy hxy hb
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion p x (y - x)
  have hy' : x + (y - x) = y := by ring
  rw [hy'] at hk
  obtain ⟨d, hdd⟩ : ∃ d, d = y - x := ⟨_, rfl⟩
  rw [← hdd] at hk
  have hd : d ∈ I := by
    have e : d = -(x - y) := by rw [hdd]; ring
    rw [e]; exact I.neg_mem hxy
  obtain ⟨h, hh⟩ : ∃ h, h = (Polynomial.derivative p).eval x + k * d := ⟨_, rfl⟩
  have hdh : d * h ∈ I ^ n := by
    have e : d * h = p.eval y - p.eval x := by rw [hk, hh]; ring
    rw [e]; exact sub_mem hy hx
  obtain ⟨j, hjj⟩ : ∃ j, j = b * h - lam := ⟨_, rfl⟩
  have hj : j ∈ I := by
    have e : j = (b * (Polynomial.derivative p).eval x - lam) + b * k * d := by
      rw [hjj, hh]; ring
    rw [e]; exact add_mem hb (I.mul_mem_left _ hd)
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow lam (-j) n
  have e : lam ^ n * (x - y) = -(b * q * (d * h)) - (-j) ^ n * d := by
    have e1 : lam ^ n = (lam - -j) * q + (-j) ^ n := by rw [← hq]; ring
    have e2 : lam - -j = b * h := by rw [hjj]; ring
    have e3 : x - y = -d := by rw [hdd]; ring
    rw [e1, e2, e3]; ring
  rw [e]
  exact sub_mem (neg_mem (Ideal.mul_mem_left _ _ hdh))
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (neg_mem hj) n))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulSubMemOfRootsModPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_sub_mem_pow_of_eval_mem_pow : ∀ (R : Type) [CommRing R] (I : Ideal R) (p : Polynomial R) (x y b lam : R) (n : ℕ), p.eval x ∈ I ^ n → p.eval y ∈ I ^ n → x - y ∈ I → b * (Polynomial.derivative p).eval x - lam ∈ I → lam ^ n * (x - y) ∈ I ^ n := by
  first | exact @GlobalTheory.pow_mul_sub_mem_of_roots_mod_pow | exact GlobalTheory.pow_mul_sub_mem_of_roots_mod_pow | (intros; apply GlobalTheory.pow_mul_sub_mem_of_roots_mod_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExistsAdicSumOfNullFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExistsAdicSumOfNullFamily
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem TopBasis.exists_sum_of_null {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (σ : ι → S) (hσ : ∀ n : ℕ, {i | σ i ∉ I ^ n}.Finite) :
    ∃ L : A, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, s (σ i) * TB.b i ∈ (I ^ n).map s := by
  classical
  let F : ℕ → Finset ι := fun n => (hσ n).toFinset
  have memF : ∀ n i, i ∈ F n ↔ σ i ∉ I ^ n := fun n i => by simp [F]
  have tail : ∀ m (G : Finset ι), F m ⊆ G →
      ∑ i ∈ G, s (σ i) * TB.b i - ∑ i ∈ F m, s (σ i) * TB.b i ∈ (I ^ m).map s := by
    intro m G hG
    rw [← Finset.sum_sdiff_eq_sub hG]
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have h : i ∉ F m := (Finset.mem_sdiff.1 hi).2
    rw [memF] at h
    exact not_not.1 h
  have mono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} h i hi => by
    rw [memF] at hi ⊢
    exact fun h' => hi (Ideal.pow_le_pow_right h h')
  have key : ∀ (n : ℕ) (x : A), x ∈ ((I.map s) ^ n • ⊤ : Submodule A A) ↔ x ∈ (I ^ n).map s := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.map_pow]
  obtain ⟨L, hL⟩ := TB.complete.toIsPrecomplete.prec (f := fun n => ∑ i ∈ F n, s (σ i) * TB.b i)
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, key, ← neg_sub]
      exact neg_mem (tail m (F n) (mono hmn)))
  refine ⟨L, fun n => ⟨F n, fun G hG => ?_⟩⟩
  have h1 := hL n
  rw [SModEq.sub_mem, key] at h1
  have h2 := tail n G hG
  have e : L - ∑ i ∈ G, s (σ i) * TB.b i =
      -((∑ i ∈ F n, s (σ i) * TB.b i - L) + (∑ i ∈ G, s (σ i) * TB.b i - ∑ i ∈ F n, s (σ i) * TB.b i)) := by
    ring
  rw [e]
  exact neg_mem (add_mem h1 h2)

theorem exists_sum_null_ev : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type)
    (TB : TopBasis bk.ev bk.J ι) (σ : ι → bk.S), (∀ n : ℕ, {i | σ i ∉ bk.J ^ n}.Finite) →
    ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, bk.ev (σ i) * TB.b i ∈ (bk.J ^ n).map bk.ev :=
  fun _ _ _ _ _ TB σ hσ => TB.exists_sum_of_null σ hσ

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExistsAdicSumOfNullFamilyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_exists_adic_sum_of_null_family : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) (TB : TopBasis bk.ev bk.J ι) (σ : ι → bk.S), (∀ n : ℕ, {i | σ i ∉ bk.J ^ n}.Finite) → ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G → L - ∑ i ∈ G, bk.ev (σ i) * TB.b i ∈ (bk.J ^ n).map bk.ev := by
  first | exact @GlobalTheory.BSP.exists_sum_null_ev | exact GlobalTheory.BSP.exists_sum_null_ev | (intros; apply GlobalTheory.BSP.exists_sum_null_ev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrimeUniformizerClass
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrimeUniformizerClass
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem prime_mk_X_of_constantCoeff {W : Type} [CommRing W] [IsDomain W] {p : W} (hp : Prime p) (E : W⟦X⟧)
    (w : Wˣ) (hE : constantCoeff E = p * w) :
    Prime (Ideal.Quotient.mk (Ideal.span {E}) (X : W⟦X⟧)) := by
  have key : ∀ f : W⟦X⟧, Ideal.Quotient.mk (Ideal.span {E}) (X : W⟦X⟧) ∣ Ideal.Quotient.mk (Ideal.span {E}) f ↔
      p ∣ constantCoeff f := by
    intro f
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
      obtain ⟨d, hd⟩ := hc
      have h := congrArg constantCoeff hd
      simp only [map_sub, map_mul, constantCoeff_X, zero_mul, sub_zero, hE] at h
      exact ⟨w * constantCoeff d, by rw [h, mul_assoc]⟩
    · rintro ⟨c, hc⟩
      have h0 : constantCoeff (f - E * C (((w⁻¹ : Wˣ) : W) * c)) = 0 := by
        simp only [map_sub, map_mul, constantCoeff_C, hE, hc]
        rw [mul_assoc, ← mul_assoc (w : W), Units.mul_inv, one_mul, sub_self]
      obtain ⟨g, hg⟩ := X_dvd_iff.2 h0
      refine ⟨Ideal.Quotient.mk _ g, ?_⟩
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨C (((w⁻¹ : Wˣ) : W) * c), by rw [← hg]; ring⟩
  refine ⟨fun h => ?_, fun h => ?_, fun a b hab => ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h1 := congrArg constantCoeff hc
    simp only [map_mul, constantCoeff_X, hE] at h1
    have h2 : constantCoeff c = 0 :=
      (mul_eq_zero.1 h1.symm).resolve_left (mul_ne_zero hp.ne_zero w.ne_zero)
    obtain ⟨g, rfl⟩ := X_dvd_iff.2 h2
    have h3 : (1 : W⟦X⟧) = E * g := by
      apply mul_left_cancel₀ (X_ne_zero (R := W))
      rw [mul_one]
      linear_combination hc
    have h4 := congrArg constantCoeff h3
    simp only [map_mul, map_one, hE] at h4
    exact hp.not_isUnit (isUnit_of_dvd_one ⟨w * constantCoeff g, by rw [h4, mul_assoc]⟩)
  · have h1 := (key 1).1 h.dvd
    rw [map_one] at h1
    exact hp.not_isUnit (isUnit_of_dvd_one h1)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, key, map_mul] at hab
    rw [key, key]
    exact hp.dvd_or_dvd hab

theorem BK.prime_unif (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) :
    Prime (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) ∧
      intToOC K (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) = bk.flat.untilt := by
  constructor
  · obtain ⟨w, hw⟩ := bk.coeff_zero
    have hp : Prime (l : Wq l bk.a) := (WittVector.irreducible l).prime
    have hE : constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; exact Polynomial.constantCoeff_coe _
    exact (MulEquiv.prime_iff bk.str.symm).2 (prime_mk_X_of_constantCoeff hp bk.E w hE)
  · rw [← bk.θ_ev _ X (bk.str.apply_symm_apply _).symm, bk.ev_X]
    exact WittVector.fontaineTheta_teichmuller _

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrimeUniformizerClassStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_prime_uniformizer_class : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Prime (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) ∧ intToOC K (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) = bk.flat.untilt := by
  first | exact @GlobalTheory.BSP.BK.prime_unif | exact GlobalTheory.BSP.BK.prime_unif | (intros; apply GlobalTheory.BSP.BK.prime_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEisensteinImageTeichmullerPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEisensteinImageTeichmullerPow
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EisImage

theorem isUnit_of_constantCoeff {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [CharP O l] [PerfectRing O l]
    (c : WittVector l O) (h : IsUnit (WittVector.constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have h1 : c * WittVector.teichmuller l ((u⁻¹ : Oˣ) : O) - 1 ∈ Ideal.span {(l : WittVector l O)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have h2 := IsAdicComplete.le_jacobson_bot (Ideal.span {(l : WittVector l O)}) h1
  have h3 := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ h2
  exact isUnit_of_mul_isUnit_left h3

theorem exists_eq {R : Type} [CommRing R] (l : R) (P : Polynomial R) (hm : P.Monic) (hd : 0 < P.natDegree)
    (hc : ∀ i < P.natDegree, l ∣ P.coeff i) (w : R) (h0 : P.coeff 0 = l * w) :
    ∃ G : Polynomial R, P = Polynomial.X ^ P.natDegree +
      Polynomial.C l * (Polynomial.C w + Polynomial.X * G) := by
  have h1 : Polynomial.C l ∣ (P - Polynomial.X ^ P.natDegree).divX := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_divX, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy (i + 1) P.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]
      exact hc _ h
    · rw [if_pos h, h, hm.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]
      exact dvd_zero _
  obtain ⟨G, hG⟩ := h1
  refine ⟨G, ?_⟩
  have h2 := Polynomial.X_mul_divX_add (P - Polynomial.X ^ P.natDegree)
  rw [hG, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hd.ne, sub_zero, h0, map_mul] at h2
  linear_combination -h2

theorem map_E_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsLocalRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ¬ IsUnit (ψ bk.flat) → ∃ w : WittVector l O, IsUnit w ∧ WittVector.map ψ (bk.ev bk.E) = WittVector.teichmuller l (ψ bk.flat) ^ bk.Ep.natDegree + ((l : ℕ) : WittVector l O) * w := by
  intro l _ K bk O _ _ _ _ ψ hψ
  obtain ⟨w₀, hw₀⟩ := bk.coeff_zero
  obtain ⟨G, hG⟩ := exists_eq (l : Wq l bk.a) bk.Ep bk.monic bk.deg_pos bk.dvd_coeff w₀ hw₀
  let f : Polynomial (Wq l bk.a) →+* WittVector l O :=
    (WittVector.map ψ).comp (bk.ev.comp (Polynomial.coeToPowerSeries.ringHom))
  have hX : f Polynomial.X = WittVector.teichmuller l (ψ bk.flat) := by
    change WittVector.map ψ (bk.ev ((Polynomial.X : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧)) = _
    rw [Polynomial.coe_X, bk.ev_X, WittVector.map_teichmuller]
  refine ⟨f (Polynomial.C (w₀ : Wq l bk.a) + Polynomial.X * G), ?_, ?_⟩
  · apply isUnit_of_constantCoeff
    have hu : IsUnit (WittVector.constantCoeff (f (Polynomial.C (w₀ : Wq l bk.a)))) :=
      ((w₀.isUnit.map Polynomial.C).map f).map _
    rw [map_add (f := _), map_mul, hX, map_add (f := _), map_mul, WittVector.constantCoeff_apply (WittVector.teichmuller l _),
      WittVector.teichmuller_coeff_zero]
    by_contra hn
    have h1 : ψ bk.flat * WittVector.constantCoeff (f G) ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ hψ
    have h2 := Ideal.sub_mem _ (show _ ∈ IsLocalRing.maximalIdeal O from hn) h1
    rw [add_sub_cancel_right] at h2
    exact h2 hu
  · have h1 := congrArg f hG
    rw [map_add (f := _), map_pow, hX, map_mul, map_natCast Polynomial.C, map_natCast f] at h1
    exact h1

end GlobalTheory.BSP.EisImage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEisensteinImageTeichmullerPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_eisenstein_image_teichmuller_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsLocalRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ¬ IsUnit (ψ bk.flat) → ∃ w : WittVector l O, IsUnit w ∧ WittVector.map ψ (bk.ev bk.E) = WittVector.teichmuller l (ψ bk.flat) ^ bk.Ep.natDegree + ((l : ℕ) : WittVector l O) * w := by
  first | exact @GlobalTheory.BSP.EisImage.map_E_eq | exact GlobalTheory.BSP.EisImage.map_E_eq | (intros; apply GlobalTheory.BSP.EisImage.map_E_eq <;> assumption)
end
end
