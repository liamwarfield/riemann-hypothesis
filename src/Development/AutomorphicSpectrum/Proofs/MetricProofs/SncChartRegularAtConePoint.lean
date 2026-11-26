module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AffineChartIdealPrimeAndSaturated
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRingAltBis
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PrimesBelowParams
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages GlobalTheory.CompanionTheory.Ar.Cmp

variable {m : ℕ}

theorem algebraMap_locRing_eq_zero_of_mem {I : Ideal (MvPolynomial (Fin m) ℂ)} (t : Fin m → ℂ)
    {h : MvPolynomial (Fin m) ℂ} (hh : h ∈ I) : algebraMap _ (locRing I t) h = 0 := by
  have halg : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) h =
      Ideal.Quotient.mk _ (algebraMap _ (locPt t) h) := rfl
  rw [halg, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hh

theorem map_ptIdeal_eq_maximalIdeal {I : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    (hI : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_algebraMap_locRing_iff I t hI]
    simpa using RingHom.mem_ker.mp hg
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have hbu := (isUnit_algebraMap_locRing_iff I t hI b).mpr hb
    have ha : a ∈ ptIdeal t := by
      refine RingHom.mem_ker.mpr ?_
      by_contra hne
      have hau := (isUnit_algebraMap_locRing_iff I t hI a).mpr hne
      rw [← hab] at hau
      exact ((IsLocalRing.mem_maximalIdeal _).mp hx) (isUnit_of_mul_isUnit_left hau)
    obtain ⟨v, hv⟩ := hbu.exists_right_inv
    have : x = algebraMap _ (locRing I t) a * v := by
      rw [← hab, mul_assoc, hv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

theorem chPrime_le_of_mem {I 𝔮 : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    {f : MvPolynomial (Fin m) ℂ} (h𝔮 : 𝔮.IsPrime) (hI𝔮 : I ≤ 𝔮) (h𝔮t : 𝔮 ≤ ptIdeal t)
    (hf : f ∈ 𝔮) : chPrime I t f ≤ 𝔮 := by
  intro g hg
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hg)
  obtain ⟨a₀, b₀, hb₀, hab⟩ := exists_mk_locRing I t a
  have hz : algebraMap _ (locRing I t) (b₀ * g - a₀ * f) = 0 := by
    rw [map_sub, map_mul, map_mul, ← ha, ← hab]
    ring
  obtain ⟨s, hs, hsI⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t hz
  have hmem : (s * b₀) * g ∈ 𝔮 := by
    have h1 := 𝔮.add_mem (hI𝔮 hsI) (𝔮.mul_mem_left (s * a₀) hf)
    have h2 : s * (b₀ * g - a₀ * f) + s * a₀ * f = (s * b₀) * g := by ring
    rwa [h2] at h1
  refine (h𝔮.mem_or_mem hmem).resolve_left fun hc => ?_
  have := RingHom.mem_ker.mp (h𝔮t hc)
  rw [map_mul] at this
  exact mul_ne_zero hs hb₀ this

theorem primes_below_params : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∀ i ∈ Jf, (SncRes.Par.chPrime I t (r i)).IsPrime ∧ I ≤ SncRes.Par.chPrime I t (r i) ∧ SncRes.Par.chPrime I t (r i) ≤ ptIdeal t ∧ Dc ≤ SncRes.Par.chPrime I t (r i) ∧ r i ∈ SncRes.Par.chPrime I t (r i) ∧ (∀ j ∈ Jf, j ≠ i → r j ∉ SncRes.Par.chPrime I t (r i)) ∧ ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → r i ∈ 𝔮 → SncRes.Par.chPrime I t (r i) ≤ 𝔮 := by
  intro m e I Dc t r Jf hIDc hI hreg hdim hspan hDc i hi
  haveI := hreg
  haveI : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing (locRing I t)
  have hmax := map_ptIdeal_eq_maximalIdeal hI
  have hspan' : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      IsLocalRing.maximalIdeal (locRing I t) := hspan.trans hmax
  have hprime : ∀ l, Prime (algebraMap _ (locRing I t) (r l)) :=
    prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm
  have hnassoc := (regular_params_spec (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm).2
  have hIt : I ≤ ptIdeal t := fun h hh => RingHom.mem_ker.mpr (hI h hh)
  have hRi : r i ∈ chPrime I t (r i) := Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
  have hle : chPrime I t (r i) ≤ ptIdeal t := by
    intro g hg
    have hg' : algebraMap _ (locRing I t) g ∈ Ideal.span {algebraMap _ (locRing I t) (r i)} :=
      Ideal.mem_comap.mp hg
    have hsub : Ideal.span {algebraMap _ (locRing I t) (r i)} ≤ IsLocalRing.maximalIdeal (locRing I t) := by
      rw [Ideal.span_singleton_le_iff_mem, ← hspan']
      exact Ideal.subset_span ⟨i, rfl⟩
    have hnu := (IsLocalRing.mem_maximalIdeal _).mp (hsub hg')
    refine RingHom.mem_ker.mpr ?_
    by_contra hne
    exact hnu ((isUnit_algebraMap_locRing_iff I t hI g).mpr hne)
  have hpr : (chPrime I t (r i)).IsPrime := by
    haveI : (Ideal.span {algebraMap _ (locRing I t) (r i)}).IsPrime :=
      (Ideal.span_singleton_prime (hprime i).ne_zero).mpr (hprime i)
    exact Ideal.comap_isPrime _ _
  have hIle : I ≤ chPrime I t (r i) := by
    intro h hh
    refine Ideal.mem_comap.mpr ?_
    rw [algebraMap_locRing_eq_zero_of_mem t hh]
    exact Ideal.zero_mem _
  refine ⟨hpr, hIle, hle, (hDc _ hpr hIle hle).mpr ⟨i, hi, hRi⟩, hRi, ?_, ?_⟩
  · intro j _ hji hj
    have hd : algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) (r j) :=
      Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hj)
    exact hnassoc i j (Ne.symm hji) ((hprime i).associated_of_dvd (hprime j) hd)
  · intro 𝔮 h𝔮 hI𝔮 h𝔮t hr
    exact chPrime_le_of_mem h𝔮 hI𝔮 h𝔮t hr

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_system_of_parameters_local_ring_alt : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∀ i ∈ Jf, (SncRes.Par.chPrime I t (r i)).IsPrime ∧ I ≤ SncRes.Par.chPrime I t (r i) ∧ SncRes.Par.chPrime I t (r i) ≤ ptIdeal t ∧ Dc ≤ SncRes.Par.chPrime I t (r i) ∧ r i ∈ SncRes.Par.chPrime I t (r i) ∧ (∀ j ∈ Jf, j ≠ i → r j ∉ SncRes.Par.chPrime I t (r i)) ∧ ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → r i ∈ 𝔮 → SncRes.Par.chPrime I t (r i) ≤ 𝔮 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularAtConePoint
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ideal_mono {S S' : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (h : S ≤ S') (p : (k : K) → ι k) :
    SncRes.ideal S p ≤ SncRes.ideal S' p :=
  Ideal.map_mono (sup_le_sup_right h _)

theorem renR_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
    {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ S) : renR (Σ k, ι k) g ∈ SncRes.ideal S p :=
  Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hg)

theorem renR_X_sub_one_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (k : K) :
    renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ SncRes.ideal S p :=
  Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))

theorem renR_sub_deh_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (f : MvPolynomial (Σ k, ι k) ℂ) :
    renR (Σ k, ι k) f - bind₁ (SncRes.lift p) f ∈ SncRes.ideal S p := by
  classical
  have key : (Ideal.Quotient.mk (SncRes.ideal S p)).comp
        (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) =
      (Ideal.Quotient.mk (SncRes.ideal S p)).comp
        (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [renameEquiv_apply]
    · rintro ⟨k, i⟩
      by_cases h : i = p k
      · subst h
        have h1 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
        have h2 := renR_X_sub_one_mem S p k
        rw [map_sub, map_one] at h2
        simpa [h1] using Ideal.Quotient.eq.2 h2
      · have h1 : SncRes.lift p ⟨k, i⟩ = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
          simp [SncRes.lift, h]
        simp [h1, renameEquiv_apply]
  exact Ideal.Quotient.eq.1 (RingHom.congr_fun key f)

theorem deh_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
    {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ S) : bind₁ (SncRes.lift p) g ∈ SncRes.ideal S p := by
  have h := (SncRes.ideal S p).sub_mem (renR_mem p hg) (renR_sub_deh_mem S p g)
  simpa using h

theorem exists_compIdeal_eq {P D Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hQ : Q ∈ (P ⊔ D).minimalPrimes) : ∃ k, SncRes.compIdeal P D k = Q := by
  refine ⟨(SncRes.finite_minimalPrimes (P ⊔ D)).toFinset.equivFin
    ⟨Q, (Set.Finite.mem_toFinset _).2 hQ⟩, ?_⟩
  simp [SncRes.compIdeal]

theorem compIdeal_injective (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :
    Function.Injective (SncRes.compIdeal P D) := by
  intro a b h
  exact ((SncRes.finite_minimalPrimes (P ⊔ D)).toFinset.equivFin).symm.injective (Subtype.ext h)

theorem exists_minimal_below {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
    {𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)} (h𝔮 : 𝔮.IsPrime)
    (hD : SncRes.ideal (P ⊔ D) p ≤ 𝔮) :
    ∃ Q ∈ (P ⊔ D).minimalPrimes,
      (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) ∧ SncRes.ideal Q p ≤ 𝔮 := by
  classical
  have hle : P ⊔ D ≤ 𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _) :=
    fun g hg => hD (deh_mem p hg)
  have : (𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _)).IsPrime :=
    Ideal.comap_isPrime _ _
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨Q, hQ, fun k hX => ?_, ?_⟩
  · have h1 : bind₁ (SncRes.lift p) (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∈ 𝔮 := hQle hX
    have h2 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
    rw [bind₁_X_right, h2] at h1
    exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · refine Ideal.map_le_iff_le_comap.2 (sup_le ?_ ?_)
    · intro f hf
      have h1 : bind₁ (SncRes.lift p) f ∈ 𝔮 := hQle hf
      have h2 := 𝔮.add_mem (hD (renR_sub_deh_mem (P ⊔ D) p f)) h1
      simpa using h2
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact hD (renR_X_sub_one_mem (P ⊔ D) p k)

theorem components_of_params : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ σ : Fin e → Option (Fin (SncRes.rc P D)), Set.InjOn σ Jf ∧ (∀ l, σ l = none ↔ l ∉ Jf) ∧ (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r l) ∧ ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k) ∧ ∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval z g = 0) → ∃ l ∈ Jf, σ l = some k := by
  intro K _ ι _ P D e p z r Jf hP hD hz hzp hI reg dim span hprim
  have hIDc : SncRes.ideal P p ≤ SncRes.ideal (P ⊔ D) p := ideal_mono le_sup_left p
  have pr := GlobalTheory.T.regular_system_of_parameters_local_ring_alt _ e (SncRes.ideal P p) (SncRes.ideal (P ⊔ D) p) (renPt (affCoord p z)) r Jf
    hIDc hI reg dim span hprim
  have hmin := GlobalTheory.T.minimal_primes_of_multihomog_sup K ι P D hP hD
  have chart_prime_and_mem_iff (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ))
      (hQ : IsMultiHomogIdeal Q) (hprime : Q.IsPrime)
      (hX : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) :
      (SncRes.ideal Q p).IsPrime ∧
        ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a →
          (bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ↔ f ∈ Q) := by
    have hker := SncRes.Dict.ker_theta Q hQ p hX
    refine ⟨?_, fun f a hf => ?_⟩
    · have : (chartIdeal Q p).IsPrime := hker ▸ RingHom.ker_isPrime (SncRes.Dict.theta Q p)
      exact Ideal.map_isPrime_of_equiv (renR (Σ k, ι k))
    · have hquot := Ideal.Quotient.eq.2 (renR_sub_deh_mem Q p f)
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hquot, Ideal.Quotient.eq_zero_iff_mem,
        SncRes.ideal, mem_map_renR_iff, RingEquiv.symm_apply_apply, ← hker, RingHom.mem_ker]
      exact SncRes.Dict.theta_eq_zero_iff Q p hX hf
  have step : ∀ l (_ : l ∈ Jf), ∃ k, SncRes.ideal (SncRes.compIdeal P D k) p =
        SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r l) ∧
      ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k := by
    intro l hl
    obtain ⟨hpr, hIq, hqt, hDq, hrl, hsep, hmn⟩ := pr l hl
    obtain ⟨Q, hQ, hX, hQle⟩ := exists_minimal_below p hpr hDq
    have hQh := hmin Q hQ
    have hQp : Q.IsPrime := hQ.1.1
    obtain ⟨hQpr, -⟩ := chart_prime_and_mem_iff Q hQh hQp hX
    have hDQ : SncRes.ideal (P ⊔ D) p ≤ SncRes.ideal Q p := ideal_mono hQ.1.2 p
    have hIQ := hIDc.trans hDQ
    obtain ⟨j, hj, hrj⟩ := (hprim _ hQpr hIQ (hQle.trans hqt)).1 hDQ
    have hjl : j = l := by
      by_contra hne
      exact hsep j hj hne (hQle hrj)
    subst hjl
    obtain ⟨k, rfl⟩ := exists_compIdeal_eq hQ
    exact ⟨k, le_antisymm hQle (hmn _ hQpr hIQ (hQle.trans hqt) hrj), hX⟩
  classical
  choose κ hκ using step
  have hσ : ∀ l k, (if h : l ∈ Jf then some (κ l h) else none) = some k →
      ∃ h : l ∈ Jf, κ l h = k := by
    intro l k h
    by_cases hl : l ∈ Jf
    · rw [dite_eq_left hl] at h
      exact ⟨hl, Option.some.inj h⟩
    · rw [dite_eq_right hl] at h
      cases h
  refine ⟨fun l => if h : l ∈ Jf then some (κ l h) else none, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : a ∈ Jf := ha
    have hb' : b ∈ Jf := hb
    simp only [dite_eq_left ha', dite_eq_left hb'] at hab
    have hk := Option.some.inj hab
    have heq : SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r a) =
        SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r b) := by
      rw [← (hκ a ha').1, ← (hκ b hb').1, hk]
    by_contra hne
    obtain ⟨-, -, -, -, -, hsep, -⟩ := pr a ha'
    obtain ⟨-, -, -, -, hrb, -, -⟩ := pr b hb'
    exact hsep b hb' (Ne.symm hne) (heq ▸ hrb)
  · intro l
    by_cases hl : l ∈ Jf <;> simp [hl]
  · intro l k h
    obtain ⟨hl, rfl⟩ := hσ l k h
    exact hκ l hl
  · intro k hk
    have hQk := SncRes.compIdeal_mem (P := P) D k
    have hkh := hmin _ hQk
    have hkp : (SncRes.compIdeal P D k).IsPrime := hQk.1.1
    have hX : ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k := by
      intro k' hx
      exact hzp k' (by simpa using hk _ hx)
    obtain ⟨hkpr, hdict⟩ := chart_prime_and_mem_iff _ hkh hkp hX
    have hzc : z ∈ conePts (SncRes.compIdeal P D k) := ⟨hz.1, hk⟩
    have hpt : SncRes.ideal (SncRes.compIdeal P D k) p ≤ ptIdeal (renPt (affCoord p z)) := by
      intro h hh
      exact renPt_zero _ _ ((mem_conePts_iff_chartIdeal hkh p z hzp).1 hzc) h hh
    have hDk : SncRes.ideal (P ⊔ D) p ≤ SncRes.ideal (SncRes.compIdeal P D k) p :=
      ideal_mono hQk.1.2 p
    have hIk := hIDc.trans hDk
    obtain ⟨l, hl, hrl⟩ := (hprim _ hkpr hIk hpt).1 hDk
    obtain ⟨-, -, -, -, -, -, hmn⟩ := pr l hl
    have hle := hmn _ hkpr hIk hpt hrl
    rw [← (hκ l hl).1] at hle
    have hQ0 := SncRes.compIdeal_mem (P := P) D (κ l hl)
    obtain ⟨S, hS, hSeq⟩ := hmin _ hQ0
    have hsub : SncRes.compIdeal P D (κ l hl) ≤ SncRes.compIdeal P D k := by
      rw [hSeq, Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hS f hf
      have hfQ : f ∈ SncRes.compIdeal P D (κ l hl) := hSeq ▸ Ideal.subset_span hf
      exact (hdict f a ha).1 (hle (deh_mem p hfQ))
    have heq : SncRes.compIdeal P D (κ l hl) = SncRes.compIdeal P D k :=
      le_antisymm hsub (hQk.2 ⟨hQ0.1.1, hQ0.1.2⟩ hsub)
    refine ⟨l, hl, ?_⟩
    beta_reduce
    rw [dite_eq_left hl, compIdeal_injective P D heq]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularAtConePointStatement
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_regular_at_cone_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ σ : Fin e → Option (Fin (SncRes.rc P D)), Set.InjOn σ Jf ∧ (∀ l, σ l = none ↔ l ∉ Jf) ∧ (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r l) ∧ ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k) ∧ ∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval z g = 0) → ∃ l ∈ Jf, σ l = some k := by
  intro K _ ι _ P D e p z r Jf hP hD hz hzp hI reg dim span hprim
  have ideal_mono {S S' : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (h : S ≤ S') (p : (k : K) → ι k) :
      SncRes.ideal S p ≤ SncRes.ideal S' p :=
    Ideal.map_mono (sup_le_sup_right h _)

  have renR_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
      {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ S) : renR (Σ k, ι k) g ∈ SncRes.ideal S p :=
    Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hg)

  have renR_X_sub_one_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (k : K) :
      renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ SncRes.ideal S p :=
    Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))

  have renR_sub_deh_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
      (f : MvPolynomial (Σ k, ι k) ℂ) :
      renR (Σ k, ι k) f - bind₁ (SncRes.lift p) f ∈ SncRes.ideal S p := by
    classical
    have key : (Ideal.Quotient.mk (SncRes.ideal S p)).comp
          (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) =
        (Ideal.Quotient.mk (SncRes.ideal S p)).comp
          (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [renameEquiv_apply]
      · rintro ⟨k, i⟩
        by_cases h : i = p k
        · subst h
          have h1 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
          have h2 := renR_X_sub_one_mem S p k
          rw [map_sub, map_one] at h2
          simpa [h1] using Ideal.Quotient.eq.2 h2
        · have h1 : SncRes.lift p ⟨k, i⟩ = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
            simp [SncRes.lift, h]
          simp [h1, renameEquiv_apply]
    exact Ideal.Quotient.eq.1 (RingHom.congr_fun key f)

  have deh_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
      {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ S) : bind₁ (SncRes.lift p) g ∈ SncRes.ideal S p := by
    have h := (SncRes.ideal S p).sub_mem (renR_mem p hg) (renR_sub_deh_mem S p g)
    simpa using h

  have exists_compIdeal_eq {P D Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
      (hQ : Q ∈ (P ⊔ D).minimalPrimes) : ∃ k, SncRes.compIdeal P D k = Q := by
    refine ⟨(SncRes.finite_minimalPrimes (P ⊔ D)).toFinset.equivFin
      ⟨Q, (Set.Finite.mem_toFinset _).2 hQ⟩, ?_⟩
    simp [SncRes.compIdeal]

  have compIdeal_injective (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :
      Function.Injective (SncRes.compIdeal P D) := by
    intro a b h
    exact ((SncRes.finite_minimalPrimes (P ⊔ D)).toFinset.equivFin).symm.injective (Subtype.ext h)

  have exists_minimal_below {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
      {𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)} (h𝔮 : 𝔮.IsPrime)
      (hD : SncRes.ideal (P ⊔ D) p ≤ 𝔮) :
      ∃ Q ∈ (P ⊔ D).minimalPrimes,
        (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) ∧ SncRes.ideal Q p ≤ 𝔮 := by
    classical
    have hle : P ⊔ D ≤ 𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _) :=
      fun g hg => hD (deh_mem p hg)
    have : (𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _)).IsPrime :=
      Ideal.comap_isPrime _ _
    obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
    refine ⟨Q, hQ, fun k hX => ?_, ?_⟩
    · have h1 : bind₁ (SncRes.lift p) (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∈ 𝔮 := hQle hX
      have h2 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
      rw [bind₁_X_right, h2] at h1
      exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · refine Ideal.map_le_iff_le_comap.2 (sup_le ?_ ?_)
      · intro f hf
        have h1 : bind₁ (SncRes.lift p) f ∈ 𝔮 := hQle hf
        have h2 := 𝔮.add_mem (hD (renR_sub_deh_mem (P ⊔ D) p f)) h1
        simpa using h2
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        exact hD (renR_X_sub_one_mem (P ⊔ D) p k)
  have hIDc : SncRes.ideal P p ≤ SncRes.ideal (P ⊔ D) p := ideal_mono le_sup_left p
  have pr := GlobalTheory.T.regular_system_of_parameters_local_ring_alt _ e (SncRes.ideal P p) (SncRes.ideal (P ⊔ D) p) (renPt (affCoord p z)) r Jf
    hIDc hI reg dim span hprim
  have hmin := GlobalTheory.T.minimal_primes_of_multihomog_sup K ι P D hP hD
  have chart_prime_and_mem_iff (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ))
      (hQ : IsMultiHomogIdeal Q) (hprime : Q.IsPrime)
      (hX : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) :
      (SncRes.ideal Q p).IsPrime ∧
        ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a →
          (bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ↔ f ∈ Q) := by
    have hker := SncRes.Dict.ker_theta Q hQ p hX
    refine ⟨?_, fun f a hf => ?_⟩
    · have : (chartIdeal Q p).IsPrime := hker ▸ RingHom.ker_isPrime (SncRes.Dict.theta Q p)
      exact Ideal.map_isPrime_of_equiv (renR (Σ k, ι k))
    · have hquot := Ideal.Quotient.eq.2 (renR_sub_deh_mem Q p f)
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hquot, Ideal.Quotient.eq_zero_iff_mem,
        SncRes.ideal, mem_map_renR_iff, RingEquiv.symm_apply_apply, ← hker, RingHom.mem_ker]
      exact SncRes.Dict.theta_eq_zero_iff Q p hX hf
  have step : ∀ l (_ : l ∈ Jf), ∃ k, SncRes.ideal (SncRes.compIdeal P D k) p =
        SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r l) ∧
      ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k := by
    intro l hl
    obtain ⟨hpr, hIq, hqt, hDq, hrl, hsep, hmn⟩ := pr l hl
    obtain ⟨Q, hQ, hX, hQle⟩ := exists_minimal_below p hpr hDq
    have hQh := hmin Q hQ
    have hQp : Q.IsPrime := hQ.1.1
    obtain ⟨hQpr, -⟩ := chart_prime_and_mem_iff Q hQh hQp hX
    have hDQ : SncRes.ideal (P ⊔ D) p ≤ SncRes.ideal Q p := ideal_mono hQ.1.2 p
    have hIQ := hIDc.trans hDQ
    obtain ⟨j, hj, hrj⟩ := (hprim _ hQpr hIQ (hQle.trans hqt)).1 hDQ
    have hjl : j = l := by
      by_contra hne
      exact hsep j hj hne (hQle hrj)
    subst hjl
    obtain ⟨k, rfl⟩ := exists_compIdeal_eq hQ
    exact ⟨k, le_antisymm hQle (hmn _ hQpr hIQ (hQle.trans hqt) hrj), hX⟩
  classical
  choose κ hκ using step
  have hσ : ∀ l k, (if h : l ∈ Jf then some (κ l h) else none) = some k →
      ∃ h : l ∈ Jf, κ l h = k := by
    intro l k h
    by_cases hl : l ∈ Jf
    · rw [dite_eq_left hl] at h
      exact ⟨hl, Option.some.inj h⟩
    · rw [dite_eq_right hl] at h
      cases h
  refine ⟨fun l => if h : l ∈ Jf then some (κ l h) else none, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : a ∈ Jf := ha
    have hb' : b ∈ Jf := hb
    simp only [dite_eq_left ha', dite_eq_left hb'] at hab
    have hk := Option.some.inj hab
    have heq : SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r a) =
        SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r b) := by
      rw [← (hκ a ha').1, ← (hκ b hb').1, hk]
    by_contra hne
    obtain ⟨-, -, -, -, -, hsep, -⟩ := pr a ha'
    obtain ⟨-, -, -, -, hrb, -, -⟩ := pr b hb'
    exact hsep b hb' (Ne.symm hne) (heq ▸ hrb)
  · intro l
    by_cases hl : l ∈ Jf <;> simp [hl]
  · intro l k h
    obtain ⟨hl, rfl⟩ := hσ l k h
    exact hκ l hl
  · intro k hk
    have hQk := SncRes.compIdeal_mem (P := P) D k
    have hkh := hmin _ hQk
    have hkp : (SncRes.compIdeal P D k).IsPrime := hQk.1.1
    have hX : ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k := by
      intro k' hx
      exact hzp k' (by simpa using hk _ hx)
    obtain ⟨hkpr, hdict⟩ := chart_prime_and_mem_iff _ hkh hkp hX
    have hzc : z ∈ conePts (SncRes.compIdeal P D k) := ⟨hz.1, hk⟩
    have hpt : SncRes.ideal (SncRes.compIdeal P D k) p ≤ ptIdeal (renPt (affCoord p z)) := by
      intro h hh
      exact renPt_zero _ _ ((mem_conePts_iff_chartIdeal hkh p z hzp).1 hzc) h hh
    have hDk : SncRes.ideal (P ⊔ D) p ≤ SncRes.ideal (SncRes.compIdeal P D k) p :=
      ideal_mono hQk.1.2 p
    have hIk := hIDc.trans hDk
    obtain ⟨l, hl, hrl⟩ := (hprim _ hkpr hIk hpt).1 hDk
    obtain ⟨-, -, -, -, -, -, hmn⟩ := pr l hl
    have hle := hmn _ hkpr hIk hpt hrl
    rw [← (hκ l hl).1] at hle
    have hQ0 := SncRes.compIdeal_mem (P := P) D (κ l hl)
    obtain ⟨S, hS, hSeq⟩ := hmin _ hQ0
    have hsub : SncRes.compIdeal P D (κ l hl) ≤ SncRes.compIdeal P D k := by
      rw [hSeq, Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hS f hf
      have hfQ : f ∈ SncRes.compIdeal P D (κ l hl) := hSeq ▸ Ideal.subset_span hf
      exact (hdict f a ha).1 (hle (deh_mem p hfQ))
    have heq : SncRes.compIdeal P D (κ l hl) = SncRes.compIdeal P D k :=
      le_antisymm hsub (hQk.2 ⟨hQ0.1.1, hQ0.1.2⟩ hsub)
    refine ⟨l, hl, ?_⟩
    beta_reduce
    rw [dite_eq_left hl, compIdeal_injective P D heq]
end
