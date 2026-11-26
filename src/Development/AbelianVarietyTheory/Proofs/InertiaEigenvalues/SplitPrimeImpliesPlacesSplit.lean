module

public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjSqrt
theorem UpperTheory.Reformulated.B.Rc9.conj_sqrt :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    (H.conj : H.E → H.E) H.sqd =
      -H.sqd := by
  intro R H
  have h := H.gal_sqd H.conj
  have hc : H.gal H.conj = R.toFrame.cc := H.gal.apply_symm_apply _
  have h2 : (R.toFrame.cc).1.2 = -1 := rfl
  rw [hc, h2] at h
  simpa using h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitPlaces

variable {R : Ranks} (H : Host R)

theorem sqrt_sq : (H.sqd) ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem conj_sqrt : H.conj (H.sqd) = -H.sqd :=
  by apply _root_.UpperTheory.Reformulated.B.Rc9.conj_sqrt <;> assumption

theorem exists_conjPl (l : ℕ) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E l) :
    ∃ w' ∈ placesOver H.E l, IsConjPl H w w' := by
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  refine ⟨HeightOneSpectrum.comap (c.symm : 𝓞 H.E →+* 𝓞 H.E) c.symm.surjective w, ?_, ?_⟩
  · show (c.symm : 𝓞 H.E →+* 𝓞 H.E) (l : 𝓞 H.E) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  · intro x y hxy
    have : y = c x := by
      apply RingOfIntegers.ext
      rw [hxy]; rfl
    subst this
    show _ ↔ c.symm (c x) ∈ w.asIdeal
    rw [c.symm_apply_apply]

theorem not_isConjPl_self {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hld : l ≠ H.d)
    (hj : jacobiSym (-(H.d : ℤ)) l = 1) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E l) :
    ¬ IsConjPl H w w := by
  intro h
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨m, hm⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective m
  have hdvd : (l : ℤ) ∣ n * n + H.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hm ⊢
    rw [← hm]; ring
  have hint : IsIntegral ℤ (H.sqd) := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [sqrt_sq]
    exact (isIntegral_natCast _).neg
  let b : 𝓞 H.E := ⟨H.sqd, hint⟩
  have hb : b ^ 2 = -(H.d : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    have e : ((b : 𝓞 H.E) : H.E) = H.sqd := rfl
    simp only [map_neg, map_pow, map_natCast, e]
    exact sqrt_sq H
  have hiff : b - n ∈ w.asIdeal ↔ b + n ∈ w.asIdeal := by
    rw [h (b - n) (-(b + n)) ?_, neg_mem_iff]
    have e : ((b : 𝓞 H.E) : H.E) = H.sqd := rfl
    simp only [map_neg, map_add (f := _), map_sub, map_intCast, e, conj_sqrt]
    ring
  have hprod : (b - n) * (b + n) ∈ w.asIdeal := by
    obtain ⟨k, hk⟩ := hdvd
    have hk' : ((n * n + H.d : ℤ) : 𝓞 H.E) = ((l * k : ℤ) : 𝓞 H.E) := by rw [hk]
    push_cast at hk'
    have : (b - n) * (b + n) = (l : 𝓞 H.E) * (-k) := by
      linear_combination hb - hk'
    rw [this]
    exact w.asIdeal.mul_mem_right _ hw
  have hboth : b - n ∈ w.asIdeal ∧ b + n ∈ w.asIdeal := by
    rcases w.isPrime.mem_or_mem hprod with h1 | h1
    exacts [⟨h1, hiff.mp h1⟩, ⟨hiff.mpr h1, h1⟩]
  have h2n : ((2 * n : ℤ) : 𝓞 H.E) ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem hboth.2 hboth.1
    convert this using 1
    push_cast; ring
  have hlo := GlobalTheory.HubLoc.liesOver_of_mem hl hw
  have hl2n : (l : ℤ) ∣ 2 * n := by
    rw [← Ideal.mem_span_singleton, hlo.over, Ideal.under_def, Ideal.mem_comap]
    simpa using h2n
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  rcases hp.dvd_or_dvd hl2n with h1 | h1
  · have h3 : l ∣ 2 := by exact_mod_cast h1
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h3)
  · have h3 : (l : ℤ) ∣ H.d := (dvd_add_right (h1.mul_right n)).mp hdvd
    have h4 : l ∣ H.d := by exact_mod_cast h3
    exact hld ((Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).mp h4)

theorem placesSplit : ∀ {R : Ranks} (H : Host R) (l : ℕ), SplitRowPrime H l → PlacesSplit H l := by
  intro R H l ⟨hl, h5, _, hd, _, hc⟩ w hw
  have hl2 : l ≠ 2 := by omega
  obtain ⟨hN, hj⟩ := (primeClass_eq_splitK_iff' (H := H.toHostRaw) hl).1 hc
  refine ⟨GlobalTheory.HubLoc.ramIdx_eq_one H hl hN w hw, exists_conjPl H l w hw, ?_⟩
  rintro w' h rfl
  exact not_isConjPl_self H hl hl2 hd hj _ hw h

end GlobalTheory.SplitPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplitStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_prime_implies_places_split : ∀ {R : Ranks} (H : Host R) (l : ℕ), SplitRowPrime H l → PlacesSplit H l := by
  first | exact @GlobalTheory.SplitPlaces.placesSplit | exact GlobalTheory.SplitPlaces.placesSplit | (intros; apply GlobalTheory.SplitPlaces.placesSplit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugate
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe

namespace GlobalTheory.SplitType

theorem exists_sqrt (l d : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (hj : jacobiSym (-(d : ℤ)) l = 1) :
    ∃ s : ℤ_[l], s ^ 2 = -(d : ℤ_[l]) ∧ ‖2 * s‖ = 1 := by
  have hd : ¬ (l : ℤ) ∣ (d : ℤ) := by
    intro h
    have : jacobiSym (-(d : ℤ)) l = 0 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h.neg_right
    omega
  have h2' : ¬ (l : ℤ) ∣ 2 := fun h =>
    h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 (by exact_mod_cast h))
  have one_of : ∀ k : ℤ, ¬ (l : ℤ) ∣ k → ‖(k : ℤ_[l])‖ = 1 := fun k hk =>
    le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd k).1 h))
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective r
  have ha : (l : ℤ) ∣ a ^ 2 + d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    linear_combination -hr
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have ha' : ¬ (l : ℤ) ∣ 2 * a := by
    intro h
    rcases hp.dvd_or_dvd h with h | h
    · exact h2' h
    · exact hd ((dvd_add_right (dvd_pow h two_ne_zero)).1 ha)
  obtain ⟨s, hs⟩ := Misc.isSquare_of_hensel l d a (by
    rw [one_of _ ha', one_pow]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).2 ha)
  have hs2 : s ^ 2 = -(d : ℤ_[l]) := by
    rw [sq, ← hs]; simp
  refine ⟨s, hs2, ?_⟩
  have n2 : ‖(2 : ℤ_[l])‖ = 1 := by simpa using one_of 2 h2'
  have nd : ‖(d : ℤ_[l])‖ = 1 := by simpa using one_of d hd
  have : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs2, norm_neg, nd]
  rw [norm_mul, n2, one_mul]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this

theorem exists_root {l d : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] (f : ℤ_[l] →+* A)
    {s : ℤ_[l]} (hs : s ^ 2 = -(d : ℤ_[l])) {y : A} (hy : y ^ 2 = -(d : A)) :
    ∃ t : ℤ_[l], (t = s ∨ t = -s) ∧ f t = y := by
  have : y ^ 2 = (f s) ^ 2 := by rw [← map_pow, hs, hy]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
  · exact ⟨s, Or.inl rfl, h.symm⟩
  · exact ⟨-s, Or.inr rfl, by rw [map_neg, h]⟩

section Host
variable {R : Ranks} (H : Host R)

theorem sqrtE_sq : (H.sqd) ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem map_sqrt_sq {A : Type} [CommRing A] (φ : H.E →+* A) : φ (H.sqd) ^ 2 = -(H.d : A) := by
  rw [← map_pow, sqrtE_sq]; simp

theorem conj_sqrtE : H.conj (H.sqd) = -H.sqd := by
  apply H.φ₀.injective
  have h : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [conj_sqrt, map_neg, h]
  simp

theorem isIntegral_sqrtE : IsIntegral ℤ (H.sqd) := by
  refine IsIntegral.of_pow two_pos ?_
  rw [sqrtE_sq]
  exact (isIntegral_natCast _).neg

end Host

section Loc
variable (D : D7) (i : D.nd.Loc)

theorem root_of_embIn (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    {s₀ t : ℤ_[D.nd.l i]}
    (h₀ : algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (algebraMap ℤ_[D.nd.l i] (D.nd.O i) s₀) =
      D.nd.embK i (D.embE (D.host.sqd)))
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    (EmbIn (N := D.nd) D.nbr i true w hw τ → t = s₀) ∧
      (EmbIn (N := D.nd) D.nbr i false w hw τ → t = -s₀) := by
  have e1 : τ (Br.cEw D.nbr i w hw (D.host.sqd)) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (t : ℚ_[D.nd.l i]) := by
    rw [← τ.commutes]
    exact congrArg τ (Subtype.ext ht.symm)
  have e2 : Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sqd))) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (s₀ : ℚ_[D.nd.l i]) := by
    rw [← h₀, Br.toLLK_alg, (D.nbr i w hw).eO_alg]
    rfl
  have e3 : D.what₂.embLL (D.embE (D.host.sqd)) =
      Complex.I * (Real.sqrt D.host.d : ℂ) :=
    (DFunLike.congr_fun D.embE_φ₀ _).trans D.host.φ₀_mem
  have inj := (algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)).injective
  constructor
  · rintro ⟨h1, φ, hφ, h2⟩
    obtain ⟨y, hy⟩ := h1 (D.host.sqd)
    have hφ' : φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) := hφ
    have : y = D.embE (D.host.sqd) :=
      D.what₂.embLL.injective ((h2 _ y hy).trans (hφ'.trans e3.symm))
    rw [this, e1, e2] at hy
    exact Subtype.ext (inj hy).symm
  · rintro ⟨h1, φ, hφ, h2⟩
    obtain ⟨y, hy⟩ := h1 (D.host.sqd)
    have hφ' := (mem_halfType_false D.host φ).1 hφ
    have : y = -D.embE (D.host.sqd) :=
      D.what₂.embLL.injective (by rw [h2 _ y hy, hφ', map_neg, e3])
    rw [this, e1, map_neg, map_neg, e2, ← map_neg] at hy
    exact Subtype.ext (inj hy).symm

theorem mem_iff_norm (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (x : 𝓞 D.host.E) (z : ℤ_[D.nd.l i])
    (hz : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (z : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))) :
    x ∈ w.asIdeal ↔ ‖z‖ < 1 := by
  rw [bridge_place D i w hw x, ← hz, norm_algebraMap', PadicInt.norm_def]

theorem root_ne (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') {t : ℤ_[D.nd.l i]}
    (hn : ‖2 * t‖ = 1)
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (ht' : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w' hw').j (algebraMap D.host.E D.nd.Om (D.host.sqd))) : False := by
  let β : 𝓞 D.host.E := ⟨D.host.sqd, isIntegral_sqrtE D.host⟩
  have hβ : (β : D.host.E) = D.host.sqd := rfl
  set n : ℕ := t.zmodRepr with hn'
  have h1 : ‖t - n‖ < 1 := PadicInt.mem_nonunits.1 (PadicInt.sub_zmodRepr_mem t)
  have hx : ((β - n : 𝓞 D.host.E) : D.host.E) = D.host.sqd - n := by
    simp [← hβ]
  have hy : ((-β - n : 𝓞 D.host.E) : D.host.E) = -D.host.sqd - n := by
    simp [← hβ]
  have h2 : β - n ∈ w.asIdeal := (mem_iff_norm D i w hw _ (t - n) (by
    rw [hx, map_sub, map_sub, ← ht]; simp)).2 h1
  have h3 : -β - n ∈ w'.asIdeal := (hc (β - n) (-β - n) (by
    rw [hx, hy, map_sub, conj_sqrtE, map_natCast])).1 h2
  have h4 : ‖-t - n‖ < 1 := (mem_iff_norm D i w' hw' _ (-t - n) (by
    rw [hy, map_sub, map_sub, map_neg, map_neg, ← ht']; simp)).1 h3
  have h5 : 2 * t = (t - n) + -(-t - n) := by ring
  have h6 := PadicInt.nonarchimedean (t - (n : ℤ_[D.nd.l i])) (-(-t - (n : ℤ_[D.nd.l i])))
  rw [← h5, hn, norm_neg] at h6
  exact absurd h6 (not_le.2 (max_lt h1 h4))

end Loc

theorem place_type_conj : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) →
    ∀ (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (hw' : w' ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host w w' →
      (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨
        (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  intro D i hl w w' hw hw' hc
  obtain ⟨-, h5, hq, hd, -, hcls⟩ := hl
  have h2 : D.nd.l i ≠ 2 := by omega
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 := by
    by_contra hj
    simp only [Host.cls, primeClass, if_neg h2, if_neg hq, if_neg hd, if_neg hj] at hcls
    split_ifs at hcls
  obtain ⟨s, hs, hn⟩ := exists_sqrt (D.nd.l i) D.host.d h2 hj
  obtain ⟨s₀, hs₀, h₀⟩ := exists_root
    ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs
    (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))
  have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]
  have hn0 : ‖2 * s₀‖ = 1 := by rcases hs₀ with rfl | rfl <;> simpa using hn
  have hne : s₀ ≠ -s₀ := fun e => by
    rw [show 2 * s₀ = 0 by linear_combination e] at hn0
    simp at hn0
  have key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)),
      ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
        (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧
        ((t = s₀ ∧ PlIn (N := D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by
    intro v hv
    obtain ⟨t, ht, h⟩ := exists_root
      ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0
      (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))
    refine ⟨t, h, ?_⟩
    rcases ht with ht | ht
    · refine Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact e.1
      · exact absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne
    · refine Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne
      · exact e.1
  obtain ⟨t, ht, h⟩ := key w hw
  obtain ⟨t', ht', h'⟩ := key w' hw'
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩
  · exact (root_ne D i w w' hw hw' hc hn0 ht (e ▸ ht')).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (root_ne D i w w' hw hw' hc (by simpa using hn0) ht (e ▸ ht')).elim

end GlobalTheory.SplitType

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugateStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPrime_place_cmType_conjugate : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hw' : w' ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host w w' → (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨ (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  first | exact @GlobalTheory.SplitType.place_type_conj | exact GlobalTheory.SplitType.place_type_conj | (intros; apply GlobalTheory.SplitType.place_type_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

structure SameGalois {D D' : D7} (N : NData D.R D.host D.what₂) (N' : NData D'.R D'.host D'.what₂) : Prop where
  R : D.R = D'.R
  host : HEq D.host D'.host
  loc : D.loc = D'.loc
  Om : HEq (@NData.Om _ _ _ N) (@NData.Om _ _ _ N')
  instOm : HEq (@NData.instOm _ _ _ N) (@NData.instOm _ _ _ N')
  algOm : HEq (@NData.algOm _ _ _ N) (@NData.algOm _ _ _ N')
  plOm : HEq (@NData.plOm _ _ _ N) (@NData.plOm _ _ _ N')
  PlG : HEq (@NData.PlG _ _ _ N) (@NData.PlG _ _ _ N')

structure TwistDataAgreeAcrossCoefficients {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    (X : NTw D.R D.host D.what₂ D.LL0 N) (X' : NTw D'.R D'.host D'.what₂ D'.LL0 N') : Prop where
  cc : HEq X.cc X'.cc
  Tw : HEq X.Tw X'.Tw
  l : HEq X.l X'.l
  O0 : HEq X.O0 X'.O0
  crO0 : HEq X.crO0 X'.crO0
  algO0 : HEq X.algO0 X'.algO0
  topO0 : HEq X.topO0 X'.topO0
  O : HEq X.O X'.O
  crO : HEq X.crO X'.crO
  algO : HEq X.algO X'.algO
  Ok : HEq X.Ok X'.Ok
  crOk : HEq X.crOk X'.crOk
  algOk : HEq X.algOk X'.algOk
  zk : HEq X.zk X'.zk
  pD : HEq X.pD X'.pD
  chi1 : HEq X.chi1 X'.chi1
  Sig : HEq X.Sig X'.Sig
  finSig : HEq X.finSig X'.finSig
  jS : HEq X.jS X'.jS
  side : HEq X.side X'.side
  rhoS : HEq X.rhoS X'.rhoS
  S0 : HEq X.S0 X'.S0
  hEig : HEq X.hEig X'.hEig
  abelian₂ : HEq X.abelian₂ X'.abelian₂
  sideL : HEq X.sideL X'.sideL
  RCG : HEq X.RCG X'.RCG
  grpRCG : HEq X.grpRCG X'.grpRCG
  finRCG : HEq X.finRCG X'.finRCG
  art : HEq X.art X'.art
  th : HEq X.th X'.th

structure SameForms {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (Y : NExp D.R D.host D.what₂ D.LL0 N X) (Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X') : Prop where
  Fm : HEq Y.Fm Y'.Fm
  acgFm : HEq Y.acgFm Y'.acgFm
  modFmK : HEq Y.modFmK Y'.modFmK
  modFmO : HEq Y.modFmO Y'.modFmO
  actG : HEq Y.actG Y'.actG
  U : HEq Y.U Y'.U
  psiU : HEq Y.psiU Y'.psiU
  eAlg : HEq Y.eAlg Y'.eAlg
  Dat : HEq Y.Dat Y'.Dat
  th : HEq Y.th Y'.th
  lev : HEq Y.lev Y'.lev
  thPsi : HEq Y.thPsi Y'.thPsi
  MtV : HEq Y.MtV Y'.MtV
  acgMt : HEq Y.acgMt Y'.acgMt
  modMtK : HEq Y.modMtK Y'.modMtK
  modMtO : HEq Y.modMtO Y'.modMtO
  MtLat : HEq Y.MtLat Y'.MtLat
  thP : HEq Y.thP Y'.thP
  hkF : HEq Y.hkF Y'.hkF


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem goodTw_transfer {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y')
    {B : BlochKatoReduction.Gen.BKPh X} {B' : BlochKatoReduction.Gen.BKPh X'} (hB : HEq B.br B'.br) (hY : B.ex = Y) (hY' : B'.ex = Y')
    {E : IntegralHeckeForms.ExpDat Y} {E' : IntegralHeckeForms.ExpDat Y'} (hE : HEq E.Dat0 E'.Dat0) {N0 : X.Tw → ℕ} {N0' : X'.Tw → ℕ} (hN : HEq N0 N0')
    {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') (e : ℝ)
    {S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)} {S' : ∀ (j : ℕ) (b : Bool), Finset (Y'.Dat i' j b)} (hS : HEq S S')
    {A Q : Finset (PlE D.host)} {A' Q' : Finset (PlE D'.host)} (hA : HEq A A') (hQ : HEq Q Q') (k : ℕ)
    {ψ : X.RCG i Q →* (X.Ok i k)ˣ} {ψ' : X'.RCG i' Q' →* (X'.Ok i' k)ˣ} (hψ : HEq ψ ψ')
    (h : IntegralHeckeForms.GoodTw Y B E N0 i e S A Q k ψ) : IntegralHeckeForms.GoodTw Y' B' E' N0' i' e S' A' Q' k ψ' := by
  obtain ⟨br, Y₁⟩ := B
  obtain ⟨br', Y₁'⟩ := B'
  obtain ⟨E, hE₁⟩ := E
  obtain ⟨E', hE₁'⟩ := E'
  dsimp only at hB hY hY' hE
  subst Y₁; subst Y₁'
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  subst hB; subst hE; subst hN; subst hi; subst hS; subst hA; subst hQ; subst hψ
  delta IntegralHeckeForms.GoodTw IntegralHeckeForms.eG IntegralHeckeForms.eO IntegralHeckeForms.Fm0 IntegralHeckeForms.V0 IntegralHeckeForms.Th IntegralHeckeForms.ThPsi
    IntegralHeckeForms.eTh IntegralHeckeForms.eThPsi IntegralHeckeForms.eThPMt IntegralHeckeForms.levs IntegralHeckeForms.SgJ IntegralHeckeForms.IdxAt IntegralHeckeForms.InclAt
    BlochKatoReduction.Gen.GE BlochKatoReduction.Gen.phiK BlochKatoReduction.Gen.chiS BlochKatoReduction.Gen.goodE BlochKatoReduction.Gen.goodS BlochKatoReduction.Gen.SigG
    BlochKatoReduction.Gen.Trep BlochKatoReduction.Gen.Tgl BlochKatoReduction.Gen.DecV BlochKatoReduction.Gen.PDv BlochKatoReduction.Gen.repV BlochKatoReduction.Gen.IsFrac BlochKatoReduction.Gen.IsImgK
    BlochKatoReduction.Gen.bk BlochKatoReduction.Gen.Spl BlochKatoReduction.Gen.selT BlochKatoReduction.Gen.sLen BlochKatoReduction.Gen.kMap BlochKatoReduction.Gen.thEval BlochKatoReduction.Gen.c0
    BlochKatoReduction.Gen.tameVal BlochKatoReduction.Gen.TrivAbove BlochKatoReduction.Gen.PsiOk BlochKatoReduction.Gen.partAT BlochKatoReduction.Gen.nu BlochKatoReduction.Gen.partC BlochKatoReduction.Gen.partD at h ⊢
  dsimp only at h ⊢
  exact h


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem fullRk_basisOf_transfer {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y')
    {E : IntegralHeckeForms.ExpDat Y} {E' : IntegralHeckeForms.ExpDat Y'} (hE : HEq E.Dat0 E'.Dat0)
    {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') (j : ℕ) (b : Bool)
    {S : Finset (Y.Dat i j b)} {S' : Finset (Y'.Dat i' j b)} (hS : HEq S S')
    (h : IntegralHeckeForms.FullRk Y E i j b (IntegralHeckeForms.SgJ Y E i j b) ∧ IntegralHeckeForms.BasisOf Y i j b (IntegralHeckeForms.SgJ Y E i j b) S) :
    IntegralHeckeForms.FullRk Y' E' i' j b (IntegralHeckeForms.SgJ Y' E' i' j b) ∧ IntegralHeckeForms.BasisOf Y' i' j b (IntegralHeckeForms.SgJ Y' E' i' j b) S' := by
  delta IntegralHeckeForms.FullRk IntegralHeckeForms.BasisOf IntegralHeckeForms.AO at h ⊢
  rw [N.restN_card_levelGroup_eq] at h
  rw [N'.restN_card_levelGroup_eq]
  obtain ⟨E, hE₁⟩ := E
  obtain ⟨E', hE₁'⟩ := E'
  dsimp only at hE
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  subst hE; subst hi; subst hS
  exact h


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem same_basic {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y') :
    X.Tw = X'.Tw ∧
    (Σ (i : X.Tw) (Q : Finset (PlE D.host)) (k : ℕ), X.RCG i Q →* (X.Ok i k)ˣ) =
      (Σ (i : X'.Tw) (Q : Finset (PlE D'.host)) (k : ℕ), X'.RCG i Q →* (X'.Ok i k)ˣ) ∧
    (∀ i j b, Finset (Y.Dat i j b)) = (∀ i j b, Finset (Y'.Dat i j b)) ∧
    (∀ (p : Σ (i : X.Tw) (Q : Finset (PlE D.host)) (k : ℕ), X.RCG i Q →* (X.Ok i k)ˣ)
      (p' : Σ (i : X'.Tw) (Q : Finset (PlE D'.host)) (k : ℕ), X'.RCG i Q →* (X'.Ok i k)ˣ), HEq p p' →
      HEq p.1 p'.1 ∧ HEq p.2.1 p'.2.1 ∧ p.2.2.1 = p'.2.2.1 ∧ HEq p.2.2.2 p'.2.2.2) ∧
    ∀ (i : X.Tw) (i' : X'.Tw), HEq i i' → X.l i = X'.l i' ∧
      (∀ (S : ∀ i j b, Finset (Y.Dat i j b)) (S' : ∀ i j b, Finset (Y'.Dat i j b)), HEq S S' →
        HEq (S i) (S' i') ∧ ∀ j b, HEq (S i j b) (S' i' j b)) ∧
      ∀ (a : FractionRing (X.O0 i)) (a' : FractionRing (X'.O0 i')), HEq a a' →
        ((∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = a) ↔
          ∃ y ∈ IsLocalRing.maximalIdeal (X'.O0 i'), algebraMap (X'.O0 i') (FractionRing (X'.O0 i')) y = a') := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  refine ⟨rfl, rfl, rfl, fun p p' hp => ?_, fun i i' hi => ?_⟩
  · subst hp
    exact ⟨HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩
  · subst hi
    refine ⟨rfl, fun S S' hS => ?_, fun a a' ha => ?_⟩
    · subst hS
      exact ⟨HEq.rfl, fun _ _ => HEq.rfl⟩
    · subst ha
      exact Iff.rfl

structure SameExport (D D' : D7) : Prop where
  gal : SameGalois D.nd D'.nd
  set : TwistDataAgreeAcrossCoefficients D.ntw D'.ntw
  frm : SameForms D.nexp D'.nexp
  br : HEq D.ntwbr D'.ntwbr
  av : avPrimes D = avPrimes D'

theorem SameExport.refl (D : D7) : SameExport D D :=
  ⟨by constructor <;> rfl, by constructor <;> rfl, by constructor <;> rfl, HEq.rfl, rfl⟩

theorem SameExport.trans {D D' D'' : D7} (h : SameExport D D') (h' : SameExport D' D'') : SameExport D D'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om, h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    ⟨h.set.cc.trans h'.set.cc, h.set.Tw.trans h'.set.Tw, h.set.l.trans h'.set.l, h.set.O0.trans h'.set.O0, h.set.crO0.trans h'.set.crO0, h.set.algO0.trans h'.set.algO0, h.set.topO0.trans h'.set.topO0, h.set.O.trans h'.set.O, h.set.crO.trans h'.set.crO, h.set.algO.trans h'.set.algO, h.set.Ok.trans h'.set.Ok, h.set.crOk.trans h'.set.crOk, h.set.algOk.trans h'.set.algOk, h.set.zk.trans h'.set.zk, h.set.pD.trans h'.set.pD, h.set.chi1.trans h'.set.chi1, h.set.Sig.trans h'.set.Sig, h.set.finSig.trans h'.set.finSig, h.set.jS.trans h'.set.jS, h.set.side.trans h'.set.side, h.set.rhoS.trans h'.set.rhoS, h.set.S0.trans h'.set.S0, h.set.hEig.trans h'.set.hEig, h.set.abelian₂.trans h'.set.abelian₂, h.set.sideL.trans h'.set.sideL, h.set.RCG.trans h'.set.RCG, h.set.grpRCG.trans h'.set.grpRCG, h.set.finRCG.trans h'.set.finRCG, h.set.art.trans h'.set.art, h.set.th.trans h'.set.th⟩,
    ⟨h.frm.Fm.trans h'.frm.Fm, h.frm.acgFm.trans h'.frm.acgFm, h.frm.modFmK.trans h'.frm.modFmK, h.frm.modFmO.trans h'.frm.modFmO, h.frm.actG.trans h'.frm.actG, h.frm.U.trans h'.frm.U, h.frm.psiU.trans h'.frm.psiU, h.frm.eAlg.trans h'.frm.eAlg, h.frm.Dat.trans h'.frm.Dat, h.frm.th.trans h'.frm.th, h.frm.lev.trans h'.frm.lev, h.frm.thPsi.trans h'.frm.thPsi, h.frm.MtV.trans h'.frm.MtV, h.frm.acgMt.trans h'.frm.acgMt, h.frm.modMtK.trans h'.frm.modMtK, h.frm.modMtO.trans h'.frm.modMtO, h.frm.MtLat.trans h'.frm.MtLat, h.frm.thP.trans h'.frm.thP, h.frm.hkF.trans h'.frm.hkF⟩,
    h.br.trans h'.br, h.av.trans h'.av⟩

theorem heq_places {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') {A : Finset (PlE H)}
    {A' : Finset (PlE H')} {s : Finset ℕ} (h : ∀ v, v ∈ A ↔ ∃ p ∈ s, v ∈ placesOver H.E p)
    (h' : ∀ v, v ∈ A' ↔ ∃ p ∈ s, v ∈ placesOver H'.E p) : HEq A A' := by
  subst hR
  subst hH
  exact heq_of_eq (Finset.ext fun v => (h v).trans (h' v).symm)

theorem SameExport.avRec {D D' : D7} (h : SameExport D D') : HEq (AvRec D) (AvRec D') :=
  heq_places h.gal.R h.gal.host mem_avRec (by rw [h.av]; exact mem_avRec)

theorem SameExport.good {D D' : D7} (h : SameExport D D') {I : TwIn D} {I' : TwIn D'} (hE : HEq I.E.Dat0 I'.E.Dat0)
    (hN : HEq I.N0 I'.N0) (hS : HEq I.S I'.S) {p : TwPack D} {p' : TwPack D'} (hp : HEq p p')
    (hg : I.Ok p.1 ∧ IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 p.1 (twEps D p.1) (I.S p.1) (AvRec D) p.2.1 p.2.2.1 p.2.2.2) :
    I'.Ok p'.1 ∧ IntegralHeckeForms.GoodTw D'.nexp (BlochKatoReduction.bk0 D') I'.E I'.N0 p'.1 (twEps D' p'.1) (I'.S p'.1) (AvRec D') p'.2.1 p'.2.2.1 p'.2.2.2 := by
  obtain ⟨-, -, -, h1, h2⟩ := same_basic h.gal h.set h.frm
  obtain ⟨h3, h4, h5, h6⟩ := h1 p p' hp
  obtain ⟨h7, h8, -⟩ := h2 _ _ h3
  obtain ⟨i, Q, k, ψ⟩ := p
  obtain ⟨i', Q', k', ψ'⟩ := p'
  dsimp only at h3 h4 h5 h6 h7 h8 hg ⊢
  subst h5
  have hm : D'.R.m = D.R.m := by rw [h.gal.R]
  have h9 := fun j (hj : j ∈ Finset.Icc 1 D'.R.m) b => fullRk_basisOf_transfer h.gal h.set h.frm hE h3 j b ((h8 _ _ hS).2 j b)
    ⟨hg.1.1 j (hm ▸ hj) b, hg.1.2 j (hm ▸ hj) b⟩
  have he : twEps D' i' = twEps D i := by rw [twEps, twEps, h7]
  rw [he]
  exact ⟨⟨fun j hj b => (h9 j hj b).1, fun j hj b => (h9 j hj b).2⟩,
    goodTw_transfer h.gal h.set h.frm (B := BlochKatoReduction.bk0 D) (B' := BlochKatoReduction.bk0 D') h.br rfl rfl hE hN h3 _ (h8 _ _ hS).1 h.avRec h4 k h6 hg.2⟩

end GlobalTheory.TwistChoice

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddCrisToOD
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddCrisToOD
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.CrisBounded

theorem dvd_of_ev_eq_zero {l : ℕ} [Fact l.Prime] {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l))
    (m : ℕ) (y : Per.BdRp l) (hy : Per.ev l m y = 0) : ainfToBdRp l d ^ m ∣ y := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have h2 := hd.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  have h3 : d ∣ GlobalTheory.MemLoc.xi e := Ideal.mem_span_singleton.1 (h2 ▸ Ideal.mem_span_singleton_self _)
  have h4 := ((GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE).1 m y).1 ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m y).2 hy)
  exact (pow_dvd_pow_of_dvd (map_dvd (GlobalTheory.MemLoc.aDp l) h3) m).trans h4

theorem bdd_crisP {l : ℕ} [Fact l.Prime] {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) (m : ℕ) :
    ∃ N : ℕ, ∀ x : Per.Acris l, ∃ a : Ainf l,
      ainfToBdRp l d ^ m ∣ (l : Per.BdRp l) ^ N * acrisToBdRp l x - ainfToBdRp l a := by
  obtain ⟨N, hN⟩ := (isCrisP_crisP l).bdd m
  refine ⟨N, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hN x
  refine ⟨a, dvd_of_ev_eq_zero hd m _ ?_⟩
  rw [map_sub, sub_eq_zero]
  exact ha.trans (GlobalTheory.MemLoc.CrisUnique.ev_aDp m a).symm

theorem bdd_tensor {Z O A C D : Type} [CommRing Z] [CommRing O] [Algebra Z O] [Module.Free Z O]
    [Module.Finite Z O] [CommRing A] [Algebra Z A] [CommRing C] [Algebra Z C] [CommRing D] [Algebra Z D]
    (f : A →ₐ[Z] D) (j : C →ₐ[Z] D) (t : D) (n : ℕ) (h : ∀ x : C, ∃ a : A, t ∣ (n : D) * j x - f a)
    (z : O ⊗[Z] C) : ∃ y : O ⊗[Z] A, ((1 : O) ⊗ₜ[Z] t) ∣
      (n : O ⊗[Z] D) * Algebra.TensorProduct.map (AlgHom.id O O) j z -
        Algebra.TensorProduct.map (AlgHom.id O O) f y := by
  let b := Module.Free.chooseBasis Z O
  choose a c hc using fun i => h (GlobalTheory.Decompl.crd b i z)
  refine ⟨∑ i, b i ⊗ₜ[Z] a i, ∑ i, b i ⊗ₜ[Z] c i, GlobalTheory.Decompl.ext_crd b fun i => ?_⟩
  rw [map_sub, GlobalTheory.Decompl.crd_natCast_mul, GlobalTheory.Decompl.crd_map, GlobalTheory.Decompl.crd_map, GlobalTheory.Decompl.crd_mul,
    GlobalTheory.Decompl.crd_sum, GlobalTheory.Decompl.crd_sum, hc]

theorem bdd_crisToOD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ), ∃ N : ℕ, ∀ z : OCr l O, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ (l : OD l O) ^ N * crisToOD l O z - toOD l O y := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ m
  rw [show ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) from
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))]
  obtain ⟨N, hN⟩ := bdd_crisP (ϖ.span_ev_eis 1) m
  refine ⟨N, fun z => ?_⟩
  obtain ⟨y, hy⟩ := bdd_tensor (ainfToBdRp l) (acrisToBdRp l) _ (l ^ N)
    (fun x => by rw [Nat.cast_pow]; exact hN x) z
  refine ⟨y, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← Nat.cast_pow]
  exact hy

end GlobalTheory.BKReal.CrisBounded
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddCrisToODStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_crisToOD_sub_toOD_dvd : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ), ∃ N : ℕ, ∀ z : OCr l O, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ (l : OD l O) ^ N * crisToOD l O z - toOD l O y := by
  first | exact @GlobalTheory.BKReal.CrisBounded.bdd_crisToOD | exact GlobalTheory.BKReal.CrisBounded.bdd_crisToOD | (intros; apply GlobalTheory.BKReal.CrisBounded.bdd_crisToOD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedDiscLinearDisjointOverPowerSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedDiscLinearDisjointOverPowerSeries
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem breuilKisinDatum_uniformizer_radius_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨?_, ?_⟩
  · unfold BK.ρ₀
    exact NNReal.rpow_pos (by positivity)
  · unfold BK.ρ₀
    exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
      have : (0:ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by positivity
      linarith)

theorem linDisjoint_disc (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (sA : bk.S →+* A) (ι : Type) (TB : TopBasis sA bk.J ι) (j : bk.DS bk.ρ₀ →+* Disc l (sA X) bk.ρ₀)
    (hj : IsDiscMap (l := _) (u := _) (ρ := _) sA j) (x y : A) (f g : bk.DS bk.ρ₀) (hg : g ≠ 0) (hy : y ≠ 0)
    (h : toDisc l (sA X) bk.ρ₀ x * j g = toDisc l (sA X) bk.ρ₀ y * j f) :
    ∃ δ a : bk.S, δ ≠ 0 ∧ sA δ * x = sA a * y := by
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatum_uniformizer_radius_pos_lt_one bk
  obtain ⟨cD, hc1, hc2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A sA ι TB bk.ρ₀ hρ0 hρ1 j hj
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hH : IsHausdorff bk.J bk.S := inferInstance
  obtain ⟨hz, -⟩ := GlobalTheory.BSP.TopBasis.basic_facts bk.S A sA bk.J ι TB hH
  have hinj : Function.Injective (toDisc l (X : bk.S) bk.ρ₀) :=
    (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk bk.S (RingHom.id _) Unit (TopBasis.self bk.J) bk.ρ₀ hρ0 hρ1).1
  have hmul := GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative l K bk bk.ρ₀ hρ0 hρ1

  have key : ∀ i, g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i x) = f * toDisc l (X : bk.S) bk.ρ₀ (TB.c i y) := by
    intro i
    have e := congrArg (cD i) h
    rw [mul_comm, mul_comm (toDisc l (sA X) bk.ρ₀ y), hc2, hc2, hc1, hc1] at e
    exact e
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, TB.c i₀ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (hz y hc)
  refine ⟨TB.c i₀ y, TB.c i₀ x, hi₀, ?_⟩
  rw [← sub_eq_zero]
  apply hz
  intro i
  rw [map_sub, TB.c_mul, TB.c_mul]
  apply hinj
  rw [map_zero]
  have h0 : g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y * TB.c i x - TB.c i₀ x * TB.c i y) = 0 := by
    rw [map_sub, map_mul, map_mul, mul_sub]
    have e1 := key i
    have e2 := key i₀
    linear_combination (toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y)) * e1 - (toDisc l (X : bk.S) bk.ρ₀ (TB.c i y)) * e2
  have hn := congrArg norm h0
  rw [hmul, norm_zero, mul_eq_zero] at hn
  rcases hn with hn | hn
  · exact absurd (norm_eq_zero.1 hn) hg
  · exact norm_eq_zero.1 hn

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedDiscLinearDisjointOverPowerSeriesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (sA : bk.S →+* A) (ι : Type) (TB : TopBasis sA bk.J ι) (j : bk.DS bk.ρ₀ →+* Disc l (sA X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) sA j → ∀ (x y : A) (f g : bk.DS bk.ρ₀), g ≠ 0 → y ≠ 0 → toDisc l (sA X) bk.ρ₀ x * j g = toDisc l (sA X) bk.ρ₀ y * j f → ∃ δ a : bk.S, δ ≠ 0 ∧ sA δ * x = sA a * y := by
  first | exact @GlobalTheory.BSP.linDisjoint_disc | exact GlobalTheory.BSP.linDisjoint_disc | (intros; apply GlobalTheory.BSP.linDisjoint_disc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mk_one_eq_zero_iff_pow_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A) (x : M) :
    LocalizedModule.mk x (1 : Submonoid.powers t) = 0 ↔ ∃ r : ℕ, t ^ r • x = 0 := by
  rw [← LocalizedModule.zero_mk (1 : Submonoid.powers t), LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨_, r, rfl⟩, h⟩
    exact ⟨r, by simpa [Submonoid.smul_def] using h⟩
  · rintro ⟨r, h⟩
    exact ⟨⟨t ^ r, r, rfl⟩, by simpa [Submonoid.smul_def] using h⟩

theorem exists_eq_mk_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A)
    (z : LocalizedModule (Submonoid.powers t) M) :
    ∃ (n : M) (k : ℕ), IsFrac t z n k := by
  induction z using LocalizedModule.induction_on with
  | _ n s =>
    obtain ⟨_, k, rfl⟩ := s
    exact ⟨n, k, rfl⟩

theorem mk_one_eq_pow_smul_of_isFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A)
    (z : LocalizedModule (Submonoid.powers t) M) (m : M) (k : ℕ) (h : IsFrac t z m k) :
    LocalizedModule.mk m (1 : Submonoid.powers t) = t ^ k • z := by
  rw [h, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def]⟩

theorem exists_pow_smul_eq_zero_of_sum {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
    (t c : A) (m : M) (k : ℕ) (v : ι → A) (w : ι → M) (z : ι → LocalizedModule (Submonoid.powers t) M)
    (Z : LocalizedModule (Submonoid.powers t) M) (hm : IsFrac t Z m k) (hZ : Z = ∑ j, v j • z j)
    (hw : ∀ j, LocalizedModule.mk (w j) (1 : Submonoid.powers t) = c • z j) :
    ∃ r : ℕ, t ^ r • (c • m - t ^ k • ∑ j, v j • w j) = 0 := by
  rw [← mk_one_eq_zero_iff_pow_smul]
  have h1 := mk_one_eq_pow_smul_of_isFrac t Z m k hm
  have hlin : ∀ x : M, LocalizedModule.mk x (1 : Submonoid.powers t) =
      LocalizedModule.mkLinearMap (Submonoid.powers t) M x := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hlin, map_sub, map_smul, map_smul, map_sum]
  simp only [map_smul, ← hlin, hw, h1, hZ, Finset.smul_sum, smul_smul]
  rw [sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← LocalizedModule.smul'_mk, hw, smul_smul, smul_smul]
  congr 1
  ring

theorem mk_tr_eq_smul_Φ_tr {l : ℕ} {R : Type} [CommRing R] (M : FCrys l R) {P P' : Obj l R} (f : Hom P P')
    (d : ↥P.I) (d' : ↥P'.I) (x mx : M.M P) (k : ℕ) (hreg : IsSMulRegular (M.M P') (f.f d))
    (h : IsFrac (d : P.A) (M.Φ P d x) mx k) :
    LocalizedModule.mk (M.tr f mx) (1 : Submonoid.powers (d' : P'.A)) = f.f d ^ k • M.Φ P' d' (M.tr f x) := by
  obtain ⟨n, s, hn⟩ := exists_eq_mk_pow (d' : P'.A) (M.Φ P' d' (M.tr f x))
  obtain ⟨r, hr⟩ := M.Φ_nat f d d' x mx k n s h hn
  rw [mul_pow, mul_smul] at hr
  have hr' := (hreg.pow r).right_eq_zero_of_smul hr
  rw [smul_sub, sub_eq_zero] at hr'
  rw [hn, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨⟨(d' : P'.A) ^ r, r, rfl⟩, ?_⟩
  simpa [Submonoid.smul_def] using hr'

theorem frob_tr_basis (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ) (A : Matrix (Fin d) (Fin d) bk.S)
    (hA : ∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j))
      (∑ i, bk.toP (A i j) • e i) a)
    (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (t : ↥Q.I) (y : Fin d → Q.A) (m : M.M Q) (k : ℕ)
    (hm : IsFrac (t : Q.A) (M.Φ Q t (∑ j, y j • M.tr g (e j))) m k) :
    ∃ r : ℕ, (t : Q.A) ^ r • (BK.hf g bk.E ^ a • m - (t : Q.A) ^ k •
      ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i)) = 0 := by
  have hreg : IsSMulRegular (M.M Q) (BK.hf g bk.E) := by
    haveI := M.proj Q
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk Q g).2

  have key : ∀ j : Fin d, LocalizedModule.mk (M.tr g (∑ i, bk.toP (A i j) • e i)) (1 : Submonoid.powers (t : Q.A)) =
      BK.hf g bk.E ^ a • M.Φ Q t (M.tr g (e j)) := fun j =>
    mk_tr_eq_smul_Φ_tr M g ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ t (e j) _ a hreg (hA j)
  have hsum : ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i) =
      ∑ j, Q.D.φ (y j) • M.tr g (∑ i, bk.toP (A i j) • e i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]; rfl
  have hΦ : M.Φ Q t (∑ j, y j • M.tr g (e j)) = ∑ j, Q.D.φ (y j) • M.Φ Q t (M.tr g (e j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, RingHom.comp_apply, algebraMap_smul]
  rw [hsum]
  exact exists_pow_smul_eq_zero_of_sum (t : Q.A) (BK.hf g bk.E ^ a) m k (fun j => Q.D.φ (y j))
    (fun j => M.tr g (∑ i, bk.toP (A i j) • e i)) (fun j => M.Φ Q t (M.tr g (e j))) _ hm hΦ key

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ) (A : Matrix (Fin d) (Fin d) bk.S), (∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a) → ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (t : ↥Q.I) (y : Fin d → Q.A) (m : M.M Q) (k : ℕ), IsFrac (t : Q.A) (M.Φ Q t (∑ j, y j • M.tr g (e j))) m k → ∃ r : ℕ, (t : Q.A) ^ r • (BK.hf g bk.E ^ a • m - (t : Q.A) ^ k • ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i)) = 0 := by
  first | exact @GlobalTheory.BSP.frob_tr_basis | exact GlobalTheory.BSP.frob_tr_basis | (intros; apply GlobalTheory.BSP.frob_tr_basis <;> assumption)
end
end
