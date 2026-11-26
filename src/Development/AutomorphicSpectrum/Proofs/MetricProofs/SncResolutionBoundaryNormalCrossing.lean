module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularAtConePoint
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerFromAffineChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartParametersAtConePoint

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerInAffineChart
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerInAffineChart
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_smul_of_isMultiHomog {L : Type} [CommRing L] [Algebra ℂ L]
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → L)
    (y : (Σ k, ι k) → L) :
    aeval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * aeval y f := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ q : (Σ k, ι k), (c q.1 * y q) ^ m q =
      (∏ k, c k ^ a k) * ∏ q : (Σ k, ι k), y q ^ m q := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [h1]; ring

def chartSub {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L) :
    MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ →ₐ[ℂ] L :=
  aeval fun j => w ((Fintype.equivFin (Σ k, ι k)).symm j)

theorem chartSub_renC {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L)
    (h : MvPolynomial (Σ k, ι k) ℂ) : chartSub w (renC (Σ k, ι k) h) = aeval w h := by
  simp [chartSub, renC, renameEquiv_apply, aeval_rename, Function.comp_def]

theorem chartSub_bind {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L)
    (p : (k : K) → ι k) (h1 : ∀ k, w ⟨k, p k⟩ = 1) (f : MvPolynomial (Σ k, ι k) ℂ) :
    chartSub w (bind₁ (lift p) f) = aeval w f := by
  have : (chartSub w).comp (bind₁ (lift p)) = aeval w := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [AlgHom.comp_apply, bind₁_X_right, aeval_X]
    unfold lift
    split_ifs with h
    · obtain ⟨k, i⟩ := q
      simp only at h
      subst h
      rw [h1 k, map_one]
    · simp [chartSub]
  exact DFunLike.congr_fun this f

variable {L : Type} [CommRing L] [Algebra ℂ L] [Algebra (MvPolynomial (Σ k, ι k) ℂ) L]
  [IsScalarTower ℂ (MvPolynomial (Σ k, ι k) ℂ) L]

theorem aeval_algebraMap_X (g : MvPolynomial (Σ k, ι k) ℂ) :
    aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) g =
      algebraMap (MvPolynomial (Σ k, ι k) ℂ) L g := by
  have : aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) =
      IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ) L :=
    MvPolynomial.algHom_ext fun q => by simp
  exact DFunLike.congr_fun this g

theorem map_ideal_le (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hS : IsMultiHomogIdeal S)
    (p : (k : K) → ι k) (c : K → L)
    (hc : ∀ k, c k * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X ⟨k, p k⟩) = 1) :
    (ideal S p).map (chartSub fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) ≤
      S.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) := by
  rw [Ideal.map_le_iff_le_comap]
  unfold ideal
  rw [Ideal.map_le_iff_le_comap]
  intro h hh
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have key : ∀ h ∈ chartIdeal S p, aeval (fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) h ∈
      S.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) := by
    obtain ⟨G, hG, rfl⟩ := hS
    intro h hh
    have hle : chartIdeal (Ideal.span G) p ≤
        (Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) (Ideal.span G)).comap
          (aeval (fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) :
            MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] L) := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le]
        intro g hg
        obtain ⟨b, hb⟩ := hG g hg
        rw [SetLike.mem_coe, Ideal.mem_comap, aeval_smul_of_isMultiHomog hb, aeval_algebraMap_X]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hg))
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap]
        simp [hc k]
    exact hle hh
  have e : (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) h = renC (Σ k, ι k) h := rfl
  rw [e, chartSub_renC]
  exact key h hh

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem relation_homogenises (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ)
    (a : K → ℕ) (n : ℕ) (s' : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
    (hP : IsMultiHomogIdeal P) (hQ : IsMultiHomogIdeal Q) (hQp : Q.IsPrime)
    (hX : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) (hf : IsMultiHomog f a)
    (hs' : s' ∉ SncRes.ideal Q p)
    (hrel : s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p) :
    ∃ s ∉ Q, s * f ∈ Q ^ n ⊔ P := by
  set x : MvPolynomial (Σ k, ι k) ℂ := ∏ k, X ⟨k, p k⟩ with hx
  let L := Localization.Away x
  let i : MvPolynomial (Σ k, ι k) ℂ →+* L := algebraMap _ L
  have hxu : IsUnit (i x) := IsLocalization.Away.algebraMap_isUnit x
  have hu : ∀ k, IsUnit (i (X ⟨k, p k⟩)) := fun k =>
    isUnit_of_dvd_unit (map_dvd i (Finset.dvd_prod_of_mem (fun k => (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ)) (Finset.mem_univ k))) hxu
  have hv : ∀ k, ∃ v, v * i (X ⟨k, p k⟩) = 1 := fun k => (hu k).exists_left_inv
  choose c hc using hv
  let w : (Σ k, ι k) → L := fun q => c q.1 * i (X q)
  have hw1 : ∀ k, w ⟨k, p k⟩ = 1 := hc
  let ψ := chartSub w
  have hψf : ψ (bind₁ (lift p) f) = (∏ k, c k ^ a k) * i f := by
    rw [chartSub_bind w p hw1, aeval_smul_of_isMultiHomog hf c, aeval_algebraMap_X]

  have h1 : ψ s' * ψ (bind₁ (lift p) f) ∈ (Q ^ n ⊔ P).map i := by
    have h2 : (ideal Q p ^ n ⊔ ideal P p).map ψ ≤ (Q ^ n ⊔ P).map i := by
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_sup, Ideal.map_pow]
      exact sup_le_sup (Ideal.pow_right_mono (map_ideal_le Q hQ p c hc) n)
        (map_ideal_le P hP p c hc)
    have := h2 (Ideal.mem_map_of_mem ψ hrel)
    rwa [map_mul] at this
  have hinv : (∏ k, i (X ⟨k, p k⟩) ^ a k) * ∏ k, c k ^ a k = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [← mul_pow, mul_comm, hc k, one_pow]
  have h3 : ψ s' * i f ∈ (Q ^ n ⊔ P).map i := by
    have := Ideal.mul_mem_left _ (∏ k, i (X ⟨k, p k⟩) ^ a k) h1
    rw [hψf] at this
    have e : (∏ k, i (X ⟨k, p k⟩) ^ a k) * (ψ s' * ((∏ k, c k ^ a k) * i f)) =
        ((∏ k, i (X ⟨k, p k⟩) ^ a k) * ∏ k, c k ^ a k) * (ψ s' * i f) := by ring
    rwa [e, hinv, one_mul] at this
  obtain ⟨e, s₀, hs₀⟩ := IsLocalization.Away.surj x (ψ s')
  have h4 : i (s₀ * f) ∈ (Q ^ n ⊔ P).map i := by
    rw [map_mul]
    change i s₀ * i f ∈ _
    rw [show i s₀ = ψ s' * i x ^ e from hs₀.symm]
    have := Ideal.mul_mem_left _ (i x ^ e) h3
    convert this using 1
    ring
  obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers x) L _ _).1 h4
  refine ⟨m * s₀, ?_, by rwa [mul_assoc]⟩
  intro hmem
  have hxQ : x ∉ Q := by
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 h
    exact hX k hk
  obtain ⟨N, rfl⟩ := hm
  have hs₀Q : s₀ ∈ Q := by
    rcases hQp.mem_or_mem hmem with h | h
    · exact absurd (hQp.mem_of_pow_mem _ h) hxQ
    · exact h

  let J := ideal Q p
  let g : MvPolynomial (Σ k, ι k) ℂ →+* (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    (Ideal.Quotient.mk J).comp (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)
  have hg1 : ∀ k, g (X ⟨k, p k⟩) = 1 := by
    intro k
    have hmem : (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) (X ⟨k, p k⟩ - 1) ∈ J :=
      Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
    have := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at this
    exact this
  have hgx : g x = 1 := by
    rw [hx, map_prod]
    exact Finset.prod_eq_one fun k _ => hg1 k
  let Φ : L →+* (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    IsLocalization.Away.lift x (g := g) (by rw [hgx]; exact isUnit_one)
  have hΦ : ∀ h, Φ (i h) = g h := fun h => IsLocalization.Away.lift_eq x _ h
  have hΦc : ∀ k, Φ (c k) = 1 := by
    intro k
    have := congrArg Φ (hc k)
    rwa [map_mul, hΦ, hg1, mul_one, map_one] at this
  have hΦψ : Φ.comp (ψ : _ →+* L) = Ideal.Quotient.mk J := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · have e1 : ψ (C r) = i (C r) := by
        rw [show (C r : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) = algebraMap ℂ _ r from rfl,
          AlgHom.commutes]
        exact IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) L r
      show Φ (ψ (C r)) = _
      rw [e1, hΦ]
      simp [g]
    · show Φ (ψ (X j)) = _
      have e1 : ψ (X j) = w ((Fintype.equivFin (Σ k, ι k)).symm j) := by simp [ψ, chartSub]
      rw [e1]
      show Φ (c _ * i (X _)) = _
      rw [map_mul, hΦc, one_mul, hΦ]
      simp [g, renC, renameEquiv_apply]
  apply hs'
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h5 : Φ (ψ s') = Ideal.Quotient.mk J s' := DFunLike.congr_fun hΦψ s'
  have h6 := congrArg Φ hs₀
  rw [map_mul, map_pow, hΦ, hΦ, hgx, one_pow, mul_one, h5] at h6
  rw [h6]
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hs₀Q))

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerInAffineChartStatement
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symbolic_power_in_affine_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ) (s' : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), IsMultiHomogIdeal P → IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) → IsMultiHomog f a → s' ∉ SncRes.ideal Q p → s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p → ∃ s ∉ Q, s * f ∈ Q ^ n ⊔ P := by
  exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.relation_homogenises
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartMultihomogOrderAtPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartMultihomogOrderAtPoint
noncomputable section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono

theorem exists_unit_mul_monomial_of_primes {m e : ℕ} (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hI : ∀ h ∈ I, eval t h = 0) [hreg : IsRegularLocalRing (locRing I t)]
    (hdim : ringKrullDim (locRing I t) = e) (r : Fin e → MvPolynomial (Fin m) ℂ) (J : Finset (Fin e))
    (hspan : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t))
    (hpr : ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t →
      (Dc ≤ 𝔮 ↔ ∃ i ∈ J, r i ∈ 𝔮))
    (g : MvPolynomial (Fin m) ℂ)
    (hg : ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → g ∈ 𝔮 → Dc ≤ 𝔮) :
    ∃ (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ J → mm i = 0) ∧
      algebraMap _ (locRing I t) g = u * ∏ i ∈ J, algebraMap _ (locRing I t) (r i) ^ mm i := by
  classical
  have hdom : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing (locRing I t)
  have hKt : I ≤ ptIdeal t := fun h hh => RingHom.mem_ker.mpr (hI h hh)
  have hspan' : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      IsLocalRing.maximalIdeal (locRing I t) := by
    rw [hspan, maximalIdeal_locRing hKt]
  have hdim' : (e : WithBot ℕ∞) = ringKrullDim (locRing I t) := hdim.symm
  have hprime : ∀ i, Prime (algebraMap _ (locRing I t) (r i)) :=
    prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim'

  have hcontr : ∀ 𝔓 : Ideal (locRing I t), 𝔓.IsPrime →
      (𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t))).IsPrime ∧
      I ≤ 𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) ∧
      𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) ≤ ptIdeal t := by
    intro 𝔓 h𝔓
    refine ⟨Ideal.comap_isPrime _ _, ?_, ?_⟩
    · intro h hh
      rw [Ideal.mem_comap]
      have : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) h = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hh)
      rw [this]
      exact 𝔓.zero_mem
    · intro h hh
      rw [Ideal.mem_comap] at hh
      by_contra hne
      have hne' : eval t h ≠ 0 := fun h0 => hne (RingHom.mem_ker.mpr h0)
      have hu := (IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI h).mpr hne'
      exact h𝔓.ne_top (Ideal.eq_top_of_isUnit_mem _ hh hu)
  have hg0 : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) g ≠ 0 := by
    intro h0
    obtain ⟨h1, h2, h3⟩ := hcontr ⊥ Ideal.isPrime_bot
    have hgm : g ∈ (⊥ : Ideal (locRing I t)).comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) := by
      rw [Ideal.mem_comap, h0]; exact Ideal.zero_mem _
    obtain ⟨i, -, hi⟩ := (hpr _ h1 h2 h3).1 (hg _ h1 h2 h3 hgm)
    rw [Ideal.mem_comap, Ideal.mem_bot] at hi
    exact (hprime i).ne_zero hi
  have hrad : (∏ i ∈ J, algebraMap _ (locRing I t) (r i)) ∈
      (Ideal.span {algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) g}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro 𝔓 ⟨hle, h𝔓⟩
    obtain ⟨h1, h2, h3⟩ := hcontr 𝔓 h𝔓
    have hgm : g ∈ 𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) := by
      rw [Ideal.mem_comap]; exact hle (Ideal.mem_span_singleton_self _)
    obtain ⟨i, hiJ, hi⟩ := (hpr _ h1 h2 h3).1 (hg _ h1 h2 h3 hgm)
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hiJ) hi
  exact eq_unit_mul_monomial (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim' J hg0 hrad

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ideal_sup_le_of_mem (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (hP : IsMultiHomogIdeal P) (f : MvPolynomial (Σ k, ι k) ℂ)
    (hf : ∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D)
    (𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)) (h𝔮 : 𝔮.IsPrime)
    (hI : SncRes.ideal P p ≤ 𝔮) (hg : bind₁ (SncRes.lift p) f ∈ 𝔮) :
    SncRes.ideal (P ⊔ D) p ≤ 𝔮 := by
  classical
  intro h hh
  have hvan : h ∈ vanishingIdeal ℂ (zeroLocus ℂ 𝔮) := by
    rw [mem_vanishingIdeal_iff]
    intro w hw
    have hw0 : ∀ c ∈ 𝔮, eval w c = 0 := fun c hc => by simpa using hw c hc
    let w' : (Σ k, ι k) → ℂ := w ∘ Fintype.equivFin (Σ k, ι k)
    have hpt : renPt w' = w := by
      funext j
      simp [renPt, w']
    have hren : ∀ x, eval w (renC (Σ k, ι k) x) = eval w' x := fun x => by
      rw [← eval_renC w' x, hpt]
    have hchart : ∀ c ∈ chartIdeal P p, eval w' c = 0 := fun c hc => by
      rw [← hren]
      have hs : (renR (Σ k, ι k)).symm (renC (Σ k, ι k) c) = c := (renR (Σ k, ι k)).symm_apply_apply c
      have hm : renC (Σ k, ι k) c ∈ SncRes.ideal P p := by
        unfold SncRes.ideal
        rw [mem_map_renR_iff, hs]
        exact hc
      exact hw0 _ (hI hm)
    obtain ⟨hcone, h1, -⟩ := conePts_of_chartIdeal hP p w' hchart
    have hlift : (fun q => eval w (SncRes.lift p q)) = w' := by
      funext q
      unfold SncRes.lift
      split_ifs with hq
      · obtain ⟨k, i⟩ := q
        simp only at hq
        subst hq
        simp [h1 k]
      · simp [w']
    have hfz : eval w' f = 0 := by
      have h2 : eval w (bind₁ (SncRes.lift p) f) = eval (fun q => eval w (SncRes.lift p q)) f :=
        eval₂Hom_bind₁ _ _ _ _
      rw [← hlift, ← h2]
      exact hw0 _ hg
    have hD := hf w' hcone hfz
    have hle : chartIdeal (P ⊔ D) p ≤ RingHom.ker (eval w') := by
      refine sup_le (sup_le (fun c hc => RingHom.mem_ker.mpr (hcone.2 c hc))
        (fun c hc => RingHom.mem_ker.mpr (hD.2 c hc))) ?_
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show eval w' _ = 0
      simp [h1 k]
    have h3 : eval w' ((renR (Σ k, ι k)).symm h) = 0 :=
      RingHom.mem_ker.mp (hle ((mem_map_renR_iff _ h).1 hh))
    have e1 : renC (Σ k, ι k) ((renR (Σ k, ι k)).symm h) = h := (renR (Σ k, ι k)).apply_symm_apply h
    show eval w h = 0
    rw [← e1, hren, h3]
  rwa [vanishingIdeal_zeroLocus_eq_radical, h𝔮.radical] at hvan

theorem exists_unit_mul_monomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → IsMultiHomog f a → (∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D) → ∃ (u : (locRing (SncRes.ideal P p) (renPt (affCoord p z)))ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ Jf → mm i = 0) ∧ algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (bind₁ (SncRes.lift p) f) = u * ∏ i ∈ Jf, algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r i) ^ mm i := by
  intro K _ ι _ P D e p z r Jf f a hP _ _ _ hI hreg hdim hspan hpr _ hf
  exact exists_unit_mul_monomial_of_primes (SncRes.ideal P p) (SncRes.ideal (P ⊔ D) p) _ hI hdim r Jf
    hspan hpr _ fun 𝔮 h𝔮 hle _ hg => ideal_sup_le_of_mem P D p hP f hf 𝔮 h𝔮 hle hg

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartMultihomogOrderAtPointStatement
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_multihomog_order_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → IsMultiHomog f a → (∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D) → ∃ (u : (locRing (SncRes.ideal P p) (renPt (affCoord p z)))ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ Jf → mm i = 0) ∧ algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (bind₁ (SncRes.lift p) f) = u * ∏ i ∈ Jf, algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r i) ^ mm i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.exists_unit_mul_monomial | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.exists_unit_mul_monomial | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.exists_unit_mul_monomial <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRing
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRing
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

variable {m : ℕ}

theorem algebraMap_locRing_eq_zero_of_mem (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    {a : MvPolynomial (Fin m) ℂ} (ha : a ∈ I) : algebraMap _ (locRing I t) a = 0 := by
  have halg : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a =
      Ideal.Quotient.mk _ (algebraMap _ (locPt t) a) := rfl
  rw [halg, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ ha

theorem map_ptIdeal_eq_maximalIdeal (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hp : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_algebraMap_locRing_iff I t hp, not_not]
    exact RingHom.mem_ker.mp ha
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have hbu := (isUnit_algebraMap_locRing_iff I t hp b).mpr hb
    have hxn : ¬ IsUnit x := hx
    have ha : eval t a = 0 := by
      by_contra hne
      have hau := (isUnit_algebraMap_locRing_iff I t hp a).mpr hne
      rw [← hab] at hau
      exact hxn (isUnit_of_mul_isUnit_left hau)
    obtain ⟨u, hu⟩ := hbu
    have hx' : x = algebraMap _ (locRing I t) a * ↑u⁻¹ := by
      rw [← hab, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hx']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr ha))

theorem exists_den_of_mem_map (I D : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (hID : I ≤ D)
    (hp : ∀ h ∈ I, eval t h = 0) {f : MvPolynomial (Fin m) ℂ}
    (hf : algebraMap _ (locRing I t) f ∈ Ideal.map (algebraMap _ (locRing I t)) D) :
    ∃ s, eval t s ≠ 0 ∧ s * f ∈ D := by
  have key : ∀ x ∈ Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) D,
      ∃ a ∈ D, ∃ b, eval t b ≠ 0 ∧ x * algebraMap _ (locRing I t) b = algebraMap _ (locRing I t) a := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ∃ a ∈ D, ∃ b, eval t b ≠ 0 ∧
      x * algebraMap _ (locRing I t) b = algebraMap _ (locRing I t) a) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, ha, 1, by simp, by simp⟩
    · exact ⟨0, D.zero_mem, 1, by simp, by simp⟩
    · rintro x y _ _ ⟨a, ha, b, hb, hab⟩ ⟨c, hc, d, hd, hcd⟩
      refine ⟨a * d + c * b, D.add_mem (D.mul_mem_right _ ha) (D.mul_mem_right _ hc), b * d,
        by simpa using ⟨hb, hd⟩, ?_⟩
      simp only [map_add (f := _), map_mul, ← hab, ← hcd]
      ring
    · rintro c x _ ⟨a, ha, b, hb, hab⟩
      obtain ⟨u, v, hv, huv⟩ := exists_mk_locRing I t c
      refine ⟨u * a, D.mul_mem_left _ ha, v * b, by simpa using ⟨hv, hb⟩, ?_⟩
      simp only [smul_eq_mul, map_mul, ← hab, ← huv]
      ring
  obtain ⟨a, ha, b, hb, hab⟩ := key _ hf
  have h0 : algebraMap _ (locRing I t) (f * b - a) = 0 := by
    rw [map_sub, map_mul, hab, sub_self]
  obtain ⟨s, hs, hsm⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
  refine ⟨s * b, by simpa using ⟨hs, hb⟩, ?_⟩
  have : s * b * f = s * (f * b - a) + s * a := by ring
  rw [this]
  exact D.add_mem (hID hsm) (D.mul_mem_left _ ha)

theorem radical_span_prod_eq {O ι : Type*} [CommRing O] [IsDomain O] (R : ι → O) (J : Finset ι)
    (hpr : ∀ i, Prime (R i)) (hna : ∀ i j, i ≠ j → ¬ Associated (R i) (R j)) :
    (Ideal.span {∏ i ∈ J, R i}).radical = Ideal.span {∏ i ∈ J, R i} := by
  classical
  apply le_antisymm _ Ideal.le_radical
  rintro g ⟨n, hn⟩
  rw [Ideal.mem_span_singleton] at hn ⊢
  have hdiv : ∀ i ∈ J, R i ∣ g := fun i hi =>
    (hpr i).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem R hi).trans hn)
  clear hn
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    obtain ⟨c, rfl⟩ := ih fun i hi => hdiv i (Finset.mem_insert_of_mem hi)
    have hac := hdiv a (Finset.mem_insert_self _ _)
    rcases (hpr a).dvd_or_dvd hac with h | h
    · exfalso
      obtain ⟨j, hj, hd⟩ := (Prime.exists_mem_finset_dvd (hpr a) h)
      have hne : a ≠ j := fun e => ha (e ▸ hj)
      exact hna a j hne (((hpr a).dvd_prime_iff_associated (hpr j)).mp hd)
    · obtain ⟨d, rfl⟩ := h
      exact ⟨d, by ring⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

theorem exists_den_prod_params : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ h : MvPolynomial (Fin m) ℂ, eval t h ≠ 0 ∧ h * ∏ l ∈ Jf, r l ∈ Dc.radical ∧ ∀ g ∈ Dc.radical, h * g ∈ Ideal.span {∏ l ∈ Jf, r l} ⊔ I := by
  classical
  intro m e I Dc t r Jf hID hp hreg hdim hspan hprime
  haveI := hreg
  haveI : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing (locRing I t)
  set alg : MvPolynomial (Fin m) ℂ →+* locRing I t := algebraMap _ (locRing I t) with halg
  set R : Fin e → locRing I t := fun l => alg (r l) with hR
  have hspan' : Ideal.span (Set.range R) = IsLocalRing.maximalIdeal (locRing I t) := by
    rw [← map_ptIdeal_eq_maximalIdeal I t hp]
    exact hspan
  have hpr : ∀ i, Prime (R i) := prime_of_regular_params R hspan' hdim.symm
  have hna := (regular_params_spec R hspan' hdim.symm).2
  set Q : MvPolynomial (Fin m) ℂ := ∏ l ∈ Jf, r l with hQ
  have hPQ : alg Q = ∏ l ∈ Jf, R l := map_prod alg _ _

  have hpr2 : ∀ 𝔓 : Ideal (locRing I t), 𝔓.IsPrime →
      (Ideal.map alg Dc ≤ 𝔓 ↔ alg Q ∈ 𝔓) := by
    intro 𝔓 h𝔓
    have hq1 : (Ideal.comap alg 𝔓).IsPrime := Ideal.comap_isPrime alg 𝔓
    have hq2 : I ≤ Ideal.comap alg 𝔓 := fun a ha => by
      rw [Ideal.mem_comap, halg, algebraMap_locRing_eq_zero_of_mem I t ha]
      exact 𝔓.zero_mem
    have hq3 : Ideal.comap alg 𝔓 ≤ ptIdeal t := fun a ha => by
      by_contra hne
      have hu := (isUnit_algebraMap_locRing_iff I t hp a).mpr fun h => hne (RingHom.mem_ker.mpr h)
      exact h𝔓.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    rw [Ideal.map_le_iff_le_comap, hprime _ hq1 hq2 hq3, hPQ, Ideal.IsPrime.prod_mem_iff]
    rfl
  have hrad : (Ideal.map alg Dc).radical = Ideal.span {alg Q} := by
    rw [hPQ, ← radical_span_prod_eq R Jf hpr hna, ← hPQ, Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
    congr 1
    ext 𝔓
    simp only [Set.mem_setOf_eq, Ideal.span_singleton_le_iff_mem]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(hpr2 𝔓 h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hpr2 𝔓 h2).mpr h1, h2⟩⟩

  obtain ⟨h', hh', hQrad⟩ : ∃ h', eval t h' ≠ 0 ∧ h' * Q ∈ Dc.radical := by
    have h1 : alg Q ∈ (Ideal.map alg Dc).radical := by
      rw [hrad]; exact Ideal.mem_span_singleton_self _
    obtain ⟨N, hN⟩ := h1
    rw [← map_pow] at hN
    obtain ⟨s, hs, hsm⟩ := exists_den_of_mem_map I Dc t hID hp hN
    refine ⟨s, hs, N + 1, ?_⟩
    have : (s * Q) ^ (N + 1) = s ^ N * Q * (s * Q ^ N) := by ring
    rw [this]
    exact Dc.mul_mem_left _ hsm

  have hone : ∀ g ∈ Dc.radical, ∃ hg, eval t hg ≠ 0 ∧ hg * g ∈ Ideal.span {Q} ⊔ I := by
    rintro g ⟨n, hn⟩
    have h1 : alg g ∈ (Ideal.map alg Dc).radical :=
      ⟨n, by rw [← map_pow]; exact Ideal.mem_map_of_mem _ hn⟩
    rw [hrad, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t c
    have h0 : algebraMap _ (locRing I t) (g * b - Q * a) = 0 := by
      change alg (g * b - Q * a) = 0
      have hab' : c * alg b = alg a := hab
      rw [map_sub, map_mul, map_mul, hc, ← hab']
      ring
    obtain ⟨s, hs, hsm⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
    refine ⟨s * b, by simpa using ⟨hs, hb⟩, ?_⟩
    have : s * b * g = s * (g * b - Q * a) + Q * (s * a) := by ring
    rw [this, add_comm]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right hsm)

  obtain ⟨S, hS⟩ : Dc.radical.FG := IsNoetherian.noetherian _
  have hSm : ∀ g, g ∈ S → ∃ hg, eval t hg ≠ 0 ∧ hg * g ∈ Ideal.span {Q} ⊔ I := fun g hg =>
    hone g (hS ▸ Submodule.subset_span hg)
  choose! f hf0 hf1 using hSm
  set H : MvPolynomial (Fin m) ℂ := ∏ g ∈ S, f g with hH
  have hH0 : eval t H ≠ 0 := by
    rw [hH, map_prod]
    exact Finset.prod_ne_zero_iff.mpr hf0
  have hHS : Dc.radical ≤
      Submodule.comap (LinearMap.mulLeft (MvPolynomial (Fin m) ℂ) H) (Ideal.span {Q} ⊔ I) := by
    rw [← hS]
    refine Submodule.span_le.mpr fun g hg => ?_
    obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem f hg
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    rw [hH, hw, mul_comm (f g) w, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hf1 g hg)
  refine ⟨h' * H, by simpa using ⟨hh', hH0⟩, ?_, fun g hg => ?_⟩
  · have : h' * H * Q = H * (h' * Q) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hQrad
  · have h1 := hHS hg
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at h1
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ h1

end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRingStatement
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_radical_locally_eq_span_prod : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ h : MvPolynomial (Fin m) ℂ, eval t h ≠ 0 ∧ h * ∏ l ∈ Jf, r l ∈ Dc.radical ∧ ∀ g ∈ Dc.radical, h * g ∈ Ideal.span {∏ l ∈ Jf, r l} ⊔ I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params | exact GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.UnitTimesParameterMonomial
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.UnitTimesParameterMonomial
noncomputable section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

theorem le_of_mul_pow_mem_span_pow {O : Type*} [CommRing O] [IsDomain O] {p a : O} (hp : Prime p)
    (ha : ¬ p ∣ a) {k n : ℕ} (h : a * p ^ k ∈ Ideal.span {p} ^ n) : n ≤ k := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  by_contra hlt
  have hlt' : k + 1 ≤ n := by omega
  have h1 : p ^ (k + 1) ∣ a * p ^ k := (pow_dvd_pow p hlt').trans h
  rw [pow_succ, mul_comm a, mul_comm (p ^ k) p, mul_comm p] at h1
  exact ha ((mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).mp (by simpa [mul_comm] using h1))

theorem map_ptIdeal_eq_maximalIdeal_ordAff {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hI : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  have hu := IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu x]
    exact not_not.mpr (RingHom.mem_ker.mp hx)
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have ha : eval t a = 0 := by
      by_contra ha
      have h1 := (hu a).mpr ha
      rw [← hab] at h1
      exact (IsLocalRing.mem_maximalIdeal _).mp hx (isUnit_of_mul_isUnit_left h1)
    obtain ⟨v, hv⟩ := (hu b).mpr hb
    have hx' : x = algebraMap _ (locRing I t) a * ((v⁻¹ : (locRing I t)ˣ) : locRing I t) := by
      rw [← hab, ← hv]
      simp
    rw [hx']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr ha))

theorem exponent_eq_order_polynomial : ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)) (g : MvPolynomial (Fin m) ℂ) (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → algebraMap _ (locRing I t) g = u * ∏ i ∈ Jf, algebraMap _ (locRing I t) (r i) ^ mm i → ∀ i ∈ Jf, ∀ n : ℕ, (∃ s ∉ SncRes.Par.chPrime I t (r i), s * g ∈ SncRes.Par.chPrime I t (r i) ^ n ⊔ I) ↔ n ≤ mm i := by
  intro m e I t r Jf g u mm hI hreg hdim hspan hg i hi n
  haveI := hreg
  haveI hdom : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing (locRing I t)
  have hu := IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI
  have hmax := map_ptIdeal_eq_maximalIdeal_ordAff I t hI
  have hspan' := hspan.trans hmax
  have hprime := prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm
  have hnon := (regular_params_spec (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm).2
  have hp : Prime (algebraMap _ (locRing I t) (r i)) := hprime i
  have hkill : ∀ h ∈ I, algebraMap _ (locRing I t) h = 0 := fun h hh =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hh)
  constructor
  · rintro ⟨s, hs, hsg⟩
    have hs' : ¬ algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) s := fun h =>
      hs (Ideal.mem_comap.mpr (Ideal.mem_span_singleton.mpr h))
    have hle : SncRes.Par.chPrime I t (r i) ^ n ⊔ I ≤
        (Ideal.span {algebraMap _ (locRing I t) (r i)} ^ n).comap (algebraMap _ (locRing I t)) := by
      refine sup_le ?_ ?_
      · rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono Ideal.map_comap_le n
      · intro h hh
        rw [Ideal.mem_comap, hkill h hh]
        exact zero_mem _
    have hmap := Ideal.mem_comap.mp (hle hsg)
    have hprod := Finset.mul_prod_erase Jf (fun j => algebraMap _ (locRing I t) (r j) ^ mm j) hi
    refine le_of_mul_pow_mem_span_pow hp (a := algebraMap _ (locRing I t) s *
      (u * ∏ j ∈ Jf.erase i, algebraMap _ (locRing I t) (r j) ^ mm j)) ?_ ?_
    · intro hd
      rcases hp.dvd_or_dvd hd with h | h
      · exact hs' h
      rcases hp.dvd_or_dvd h with h | h
      · exact hp.not_unit (isUnit_of_dvd_unit h u.isUnit)
      · obtain ⟨j, hj, hd'⟩ := (Prime.dvd_finsetProd_iff hp _).mp h
        have hd'' := hp.dvd_of_dvd_pow hd'
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        exact hnon i j hji.symm (hp.associated_of_dvd (hprime j) hd'')
    · rw [map_mul, hg, ← hprod] at hmap
      convert hmap using 1
      ring
  · intro hn
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t (u : locRing I t)
    have hz : algebraMap _ (locRing I t) (b * g - a * ∏ j ∈ Jf, r j ^ mm j) = 0 := by
      simp only [map_sub, map_mul, map_prod, map_pow]
      rw [hg, ← hab]
      ring
    obtain ⟨c, hc, hcI⟩ := IrreducibleComponentPreimages.exists_mul_mem_of_algebraMap_locRing_eq_zero I t hz
    refine ⟨c * b, ?_, ?_⟩
    · intro hmem
      have h1 : algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) (c * b) :=
        Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hmem)
      have h2 := (hu (c * b)).mpr (by rw [map_mul]; exact mul_ne_zero hc hb)
      exact hp.not_unit (isUnit_of_dvd_unit h1 h2)
    · have hri : r i ∈ SncRes.Par.chPrime I t (r i) :=
        Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
      have hpow : c * a * ∏ j ∈ Jf, r j ^ mm j ∈ SncRes.Par.chPrime I t (r i) ^ n := by
        apply Ideal.pow_le_pow_right hn
        obtain ⟨d, hd⟩ : r i ^ mm i ∣ ∏ j ∈ Jf, r j ^ mm j :=
          Finset.dvd_prod_of_mem (fun j => r j ^ mm j) hi
        rw [hd]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hri _))
      have hsplit : c * b * g = c * (b * g - a * ∏ j ∈ Jf, r j ^ mm j) +
          c * a * ∏ j ∈ Jf, r j ^ mm j := by ring
      rw [hsplit]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hcI) (Ideal.mem_sup_left hpow)

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.UnitTimesParameterMonomialStatement
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_times_parameter_monomial : ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)) (g : MvPolynomial (Fin m) ℂ) (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → algebraMap _ (locRing I t) g = u * ∏ i ∈ Jf, algebraMap _ (locRing I t) (r i) ^ mm i → ∀ i ∈ Jf, ∀ n : ℕ, (∃ s ∉ SncRes.Par.chPrime I t (r i), s * g ∈ SncRes.Par.chPrime I t (r i) ^ n ⊔ I) ↔ n ≤ mm i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionBoundaryNormalCrossing
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_sncData_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, ∃ d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)), (∃ O : Set (SncRes.Pts (pC (mCoordIdeal y))), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src (pC (mCoordIdeal y)) p ∧ ∀ k, SncRes.comp (pC (mCoordIdeal y)) (pC J) k ∩ O = {x' ∈ O | ∃ l, d.σ l = some k ∧ eval (SncRes.coord (pC (mCoordIdeal y)) p x') (d.r l) = 0}) ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), ReciprocityTheory.AnForm.R.IsMultiHomog f a → f ∉ pC (mCoordIdeal y) → (∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)), eval z f = 0 → z ∈ ReciprocityTheory.AnForm.R.conePts (pC J)) → ∃ u : ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x), IsUnit u ∧ algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (bind₁ (SncRes.lift p) f) = u * ∏ l ∈ d.J, algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (d.r l) ^ (d.σ l).elim 0 (fun k => SncRes.ordAlong (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k) (pC (mCoordIdeal y)) f) := by
  intro K _ ι _ Ω _ _ y e J hA hJ hJn hS p x hx
  have hPm : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hA.2.1.2.1
  have hDm : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC J) := isMultiHomogIdeal_pC hJ
  have hz : ∀ k, SncRes.rep x ⟨k, p k⟩ ≠ 0 := hx
  have hzc := SncRes.rep_mem x
  obtain ⟨r, Jf, hIt, hreg, hdim, hspan, hpr⟩ := GlobalTheory.T.snc_chart_parameters_at_cone_point K ι Ω y e J hA hS p (SncRes.rep x) hzc hz
  have hID : SncRes.ideal (pC (mCoordIdeal y)) p ≤ SncRes.ideal (pC (mCoordIdeal y) ⊔ pC J) p :=
    Ideal.map_mono (sup_le_sup_right le_sup_left _)
  obtain ⟨h, hh, hmem, hle⟩ := GlobalTheory.T.exists_radical_locally_eq_span_prod _ e _ _ _ r Jf hID hIt hreg hdim hspan hpr
  obtain ⟨σ, hinj, hnone, hσ, hcov⟩ := GlobalTheory.T.snc_chart_regular_at_cone_point K ι _ (pC J) e p (SncRes.rep x) r Jf hPm hDm hzc hz hIt hreg hdim hspan hpr
  let d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)) :=
    { r := r, J := Jf, h := h, σ := σ, σ_injOn := hinj, σ_eq_none := hnone, span_eq := hspan, eval_h := hh,
      mem_bd := hmem, le_span := hle }
  refine ⟨d, GlobalTheory.T.snc_chart_regular_with_boundary_choice K ι _ (pC J) e p x r Jf σ hPm hDm hx hIt hreg hdim hspan hnone (fun l k hl => (hσ l k hl).1) hcov, ?_⟩
  intro f a hf hfP hfz
  obtain ⟨u, mm, hm0, hfac⟩ := GlobalTheory.T.snc_chart_multihomog_order_at_point K ι _ (pC J) e p (SncRes.rep x) r Jf f a hPm hDm hzc hz hIt hreg hdim hspan hpr hf hfz
  refine ⟨u.val, u.isUnit, ?_⟩
  refine hfac.trans (congrArg (fun w => u.val * w) (Finset.prod_congr rfl fun l hl => ?_))
  have hlJ : l ∈ Jf := hl
  obtain ⟨k, hk⟩ : ∃ k, σ l = some k := by
    cases hσl : σ l with
    | none => exact absurd hlJ ((hnone l).1 hσl)
    | some k => exact ⟨k, rfl⟩
  have hdσ : d.σ l = some k := hk
  rw [hdσ]
  obtain ⟨hQc, hX⟩ := hσ l k hk
  have hQmin := SncRes.compIdeal_mem (P := pC (mCoordIdeal y)) (pC J) k
  have hQm := GlobalTheory.T.minimal_primes_of_multihomog_sup K ι _ _ hPm hDm _ hQmin
  have hQp : (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k).IsPrime := hQmin.1.1
  have hord := GlobalTheory.T.unit_times_parameter_monomial _ e _ _ r Jf _ u mm hIt hreg hdim hspan hfac l hlJ
  have key : ∀ n : ℕ, (∃ s ∉ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k,
      s * f ∈ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k ^ n ⊔ pC (mCoordIdeal y)) ↔ n ≤ mm l := by
    intro n
    rw [← hord n, ← hQc]
    constructor
    · rintro ⟨s, hs, hsf⟩
      exact GlobalTheory.T.symbolic_power_from_affine_chart K ι _ _ p f s a n hPm hQm hQp hX hf hs hsf
    · rintro ⟨s', hs, hsf⟩
      exact GlobalTheory.T.symbolic_power_in_affine_chart K ι _ _ p f a n s' hPm hQm hQp hX hf hs hsf
  have hset : {n : ℕ | ∃ s ∉ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k,
      s * f ∈ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k ^ n ⊔ pC (mCoordIdeal y)} = Set.Iic (mm l) := by
    ext n
    exact key n
  show _ ^ mm l = _ ^ (SncRes.ordAlong _ _ f)
  rw [SncRes.ordAlong, hset, csSup_Iic]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionBoundaryNormalCrossingStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_resolution_boundary_normal_crossing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, ∃ d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)), (∃ O : Set (SncRes.Pts (pC (mCoordIdeal y))), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src (pC (mCoordIdeal y)) p ∧ ∀ k, SncRes.comp (pC (mCoordIdeal y)) (pC J) k ∩ O = {x' ∈ O | ∃ l, d.σ l = some k ∧ eval (SncRes.coord (pC (mCoordIdeal y)) p x') (d.r l) = 0}) ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), ReciprocityTheory.AnForm.R.IsMultiHomog f a → f ∉ pC (mCoordIdeal y) → (∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)), eval z f = 0 → z ∈ ReciprocityTheory.AnForm.R.conePts (pC J)) → ∃ u : ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x), IsUnit u ∧ algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (bind₁ (SncRes.lift p) f) = u * ∏ l ∈ d.J, algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (d.r l) ^ (d.σ l).elim 0 (fun k => SncRes.ordAlong (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k) (pC (mCoordIdeal y)) f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel <;> assumption)
end
