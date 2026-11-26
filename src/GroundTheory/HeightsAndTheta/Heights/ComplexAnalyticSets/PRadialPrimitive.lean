module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdFiniteNonZeroDivisor
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotientMinimalPrimeAddOne

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRadialPrimitive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ContDiff

noncomputable section

theorem RadialPrimitive.primitive_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiff ℝ ∞ (fun t => ∫ τ in c..t, f τ) ∧ deriv (fun t => ∫ τ in c..t, f τ) = f := by
  have hd : deriv (fun t => ∫ τ in c..t, f τ) = f :=
    funext fun t => hf.continuous.deriv_integral f c t
  refine ⟨contDiff_infty_iff_deriv.2 ⟨fun t => ?_, by rw [hd]; exact hf⟩, hd⟩
  exact (hf.continuous.integral_hasStrictDerivAt c t).hasDerivAt.differentiableAt

theorem RadialPrimitive.proof : RadialPrimitive.Statement := by
  intro e a t₀ T ha ht₀ hconst hzero hint
  set c : ℝ := ((e + 1 : ℕ) : ℝ) with hc
  set g : ℝ → ℝ := fun τ => a τ * (c * τ ^ (e + 1 - 1)) with hg
  set P : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, g τ with hP
  have hgs : ContDiff ℝ ∞ g := ha.mul (contDiff_const.mul (contDiff_id.pow _))
  obtain ⟨hPs, hPd⟩ := RadialPrimitive.primitive_contDiff g hgs 0
  have hrt : ∀ t, radialTransform (e + 1) a t = a t * t ^ (e + 1) - P t := fun t => rfl

  have hPc : ∀ t ∈ Set.Icc 0 t₀, P t = a 0 * t ^ (e + 1) := by
    intro t ht
    have h0 := radialTransform_eq_zero_of_const e a hconst ht
    rw [hrt, hconst t ht] at h0
    linarith
  set h : ℝ → ℝ := fun t => if t < t₀ then a 0 else P t / t ^ (e + 1) with hh
  have hlow : ∀ t, t < t₀ → h t = a 0 := fun t ht => if_pos ht
  have hpos : ∀ t, 0 < t → h t = P t / t ^ (e + 1) := by
    intro t ht
    by_cases h1 : t < t₀
    · rw [hlow t h1, hPc t ⟨ht.le, h1.le⟩, mul_div_assoc, div_self (pow_ne_zero _ ht.ne'), mul_one]
    · exact if_neg h1
  have hlowE : ∀ x, x < t₀ → h =ᶠ[nhds x] fun _ => a 0 := fun x hx =>
    Filter.eventually_of_mem (isOpen_Iio.mem_nhds hx) fun t ht => hlow t ht
  have hposE : ∀ x, 0 < x → h =ᶠ[nhds x] fun t => P t / t ^ (e + 1) := fun x hx =>
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) fun t ht => hpos t ht
  have hs : ContDiff ℝ ∞ h := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < t₀
    · exact contDiffAt_const.congr_of_eventuallyEq (hlowE x hx)
    · have hx0 : 0 < x := lt_of_lt_of_le ht₀ (not_lt.1 hx)
      exact (hPs.contDiffAt.div (contDiff_id.pow _).contDiffAt (pow_ne_zero _ hx0.ne')).congr_of_eventuallyEq
        (hposE x hx0)

  set R : ℝ := max T t₀ with hR
  have hPz : ∀ t, R ≤ t → P t = 0 := by
    intro t ht
    have hTt : T ≤ t := le_trans (le_max_left _ _) ht
    have hgc : Continuous g := hgs.continuous
    have htail : ∫ τ in T..t, g τ = 0 := by
      have hcg : ∫ τ in T..t, g τ = ∫ τ in T..t, (0 : ℝ) :=
        intervalIntegral.integral_congr fun τ hτ => by
          rw [Set.uIcc_of_le hTt] at hτ
          simp [hg, hzero τ hτ.1]
      rw [hcg]
      simp
    have := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := T) (c := t)
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
    simp only [hP]
    rw [← this, htail, add_zero]
    exact hint
  have hhz : ∀ t, R ≤ t → h t = 0 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₀ (le_trans (le_max_right _ _) ht)
    rw [hpos t ht0, hPz t ht, zero_div]
  obtain ⟨hQs, hQd⟩ := RadialPrimitive.primitive_contDiff h hs R
  refine ⟨fun t => ∫ τ in R..t, h τ, hQs, ⟨R, fun t ht => ?_⟩, ?_, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · have hcg : ∫ τ in R..t, h τ = ∫ τ in R..t, (0 : ℝ) :=
      intervalIntegral.integral_congr fun τ hτ => by
        rw [Set.uIcc_of_le ht] at hτ
        exact hhz τ hτ.1
    show ∫ τ in R..t, h τ = 0
    rw [hcg]
    simp
  · rw [hQd]
    exact hlow 0 ht₀
  · rw [hQd, (hlowE 0 ht₀).deriv_eq]
    simp
  · rw [hQd, hpos t ht, hrt, div_mul_cancel₀ _ (pow_ne_zero _ ht.ne')]
    ring
  · rw [hQd, (hposE t ht).deriv_eq, hrt]
    have hPt : HasDerivAt P (g t) t := (hgs.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hq : HasDerivAt (fun s => P s / s ^ (e + 1))
        ((g t * t ^ (e + 1) - P t * (((e + 1 : ℕ) : ℝ) * t ^ (e + 1 - 1))) / (t ^ (e + 1)) ^ 2) t :=
      hPt.div (hasDerivAt_pow (e + 1) t) (pow_ne_zero _ ht.ne')
    rw [hq.deriv]
    simp only [hg, hc, Nat.add_sub_cancel]
    have ht' : t ≠ 0 := ht.ne'
    push_cast
    field_simp
    ring

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCMUnmixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

theorem sliceCMUnmixed_local (h : CMQuotientUnmixed.Statement) {R : Type} [CommRing R] [IsNoetherianRing R]
    (m : Ideal R) [m.IsPrime] {d : ℕ} (J : Ideal R) (ℓ : Fin d → R) (hℓ : ∀ i, ℓ i ∈ m)
    (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (π : Localization.AtPrime m →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J.map (algebraMap R (Localization.AtPrime m)))
    (hB : ringKrullDim B = (d + 1 : ℕ))
    (hS : ringKrullDim (Localization.AtPrime m ⧸
      (J ⊔ Ideal.span (Set.range ℓ)).map (algebraMap R (Localization.AtPrime m))) = (1 : ℕ)) :
    ∀ P ∈ associatedPrimes R (R ⧸ (J ⊔ Ideal.span (Set.range ℓ))), P ≤ m →
      P ∈ (J ⊔ Ideal.span (Set.range ℓ)).minimalPrimes ∧ P ≠ m := by
  intro P hP hPm
  obtain ⟨I, hI⟩ : ∃ I, I = J ⊔ Ideal.span (Set.range ℓ) := ⟨_, rfl⟩
  rw [← hI] at hP hS ⊢
  have hJI : J ≤ I := hI ▸ le_sup_left
  let x : Fin d → B := fun i => π (algebraMap R (Localization.AtPrime m) (ℓ i))

  have hspan : Ideal.span (Set.range x) = (I.map (algebraMap R (Localization.AtPrime m))).map π := by
    rw [hI, Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker π).2 hker.ge, bot_sup_eq,
      Ideal.map_map, Ideal.map_span, ← Set.range_comp]
    rfl
  have hker_le : ∀ Q : Ideal R, J ≤ Q → RingHom.ker π ≤ Q.map (algebraMap R (Localization.AtPrime m)) :=
    fun Q hQ => hker ▸ Ideal.map_mono hQ
  have hcomap : ∀ Q : Ideal R, J ≤ Q →
      ((Q.map (algebraMap R (Localization.AtPrime m))).map π).comap π =
        Q.map (algebraMap R (Localization.AtPrime m)) := fun Q hQ => by
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 (hker_le Q hQ)]

  have hdimx : ringKrullDim (B ⧸ Ideal.span (Set.range x)) = (1 : ℕ) := by
    let f : Localization.AtPrime m →+* B ⧸ Ideal.span (Set.range x) := (Ideal.Quotient.mk _).comp π
    have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hπ
    have hkf : RingHom.ker f = I.map (algebraMap R (Localization.AtPrime m)) := by
      ext c
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hspan, ← Ideal.mem_comap,
        hcomap I hJI]
    rw [← ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf),
      ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hkf), hS]
  have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => by
    have : IsLocalHom π := IsLocalHom.of_surjective π hπ
    exact map_nonunit π _ ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m (ℓ i)).2
      (hℓ i))
  have hsum : ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B := by
    rw [hdimx, hB, ← Nat.cast_add, Nat.add_comm]

  obtain ⟨hPp, y, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmemP : ∀ s, s ∈ P ↔ s * r ∈ I := fun s => by
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot,
      show s • Ideal.Quotient.mk I r = Ideal.Quotient.mk I (s * r) from rfl, Ideal.Quotient.eq_zero_iff_mem]
  have hIP : I ≤ P := fun s hs => (hmemP s).2 (I.mul_mem_right r hs)
  have hdisj : ∀ Q : Ideal R, Q ≤ m → Disjoint (m.primeCompl : Set R) Q :=
    fun Q hQ => Set.disjoint_left.2 fun u hu huQ => hu (hQ huQ)
  have hprime : ∀ Q : Ideal R, Q.IsPrime → Q ≤ m → J ≤ Q →
      ((Q.map (algebraMap R (Localization.AtPrime m))).map π).IsPrime := fun Q hQ hQm hJQ => by
    have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) Q hQ (hdisj Q hQm)
    exact Ideal.map_isPrime_of_surjective hπ (hker_le Q hJQ)
  have hback : ∀ Q : Ideal R, Q.IsPrime → Q ≤ m → J ≤ Q →
      (((Q.map (algebraMap R (Localization.AtPrime m))).map π).comap π).comap
        (algebraMap R (Localization.AtPrime m)) = Q := fun Q hQ hQm hJQ => by
    rw [hcomap Q hJQ]
    exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ hQ (hdisj Q hQm)
  obtain ⟨p, hp⟩ : ∃ p, p = (P.map (algebraMap R (Localization.AtPrime m))).map π := ⟨_, rfl⟩
  have hpP : p.IsPrime := hp ▸ hprime P hPp hPm (hJI.trans hIP)

  have hass : p ∈ associatedPrimes B (B ⧸ Ideal.span (Set.range x)) := by
    refine isAssociatedPrime_iff.2 ⟨hpP, Ideal.Quotient.mk _ (π (algebraMap R (Localization.AtPrime m) r)), ?_⟩
    ext b
    obtain ⟨a, rfl⟩ := hπ b
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot,
      show π a • Ideal.Quotient.mk (Ideal.span (Set.range x)) (π (algebraMap R (Localization.AtPrime m) r)) =
        Ideal.Quotient.mk _ (π (a * algebraMap R (Localization.AtPrime m) r)) by rw [map_mul]; rfl,
      Ideal.Quotient.eq_zero_iff_mem, hspan, ← Ideal.mem_comap, ← Ideal.mem_comap, hcomap I hJI, hp,
      hcomap P (hJI.trans hIP)]
    obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl a
    rw [← IsLocalization.mk'_one (M := m.primeCompl) (Localization.AtPrime m) r, ← IsLocalization.mk'_mul,
      mul_one, IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
    simp_rw [hmemP, mul_assoc]
  obtain ⟨hmin, hdimp⟩ := h B d x hxm hsum p hass
  refine ⟨⟨⟨hPp, hIP⟩, fun Q ⟨hQp, hIQ⟩ hQP => ?_⟩, fun hPeq => ?_⟩
  · have hQm : Q ≤ m := hQP.trans hPm
    have hJQ : J ≤ Q := hJI.trans hIQ
    have h1 : Ideal.span (Set.range x) ≤ (Q.map (algebraMap R (Localization.AtPrime m))).map π := by
      rw [hspan]
      exact Ideal.map_mono (Ideal.map_mono hIQ)
    have h2 : (Q.map (algebraMap R (Localization.AtPrime m))).map π ≤ p :=
      hp ▸ Ideal.map_mono (Ideal.map_mono hQP)
    have h3 := hmin.2 ⟨hprime Q hQp hQm hJQ, h1⟩ h2
    rw [← hback P hPp hPm (hJI.trans hIP), ← hback Q hQp hQm hJQ, ← hp]
    exact Ideal.comap_mono (Ideal.comap_mono h3)
  · have hpmax : p.IsMaximal := by
      have := Ideal.map_eq_top_or_isMaximal_of_surjective π hπ
        (maximalIdeal.isMaximal (Localization.AtPrime m))
      rw [hPeq, Localization.AtPrime.map_eq_maximalIdeal] at hp
      rw [← hp] at this
      exact this.resolve_left hpP.ne_top
    let := Ideal.Quotient.field p
    have h0 : ringKrullDim (B ⧸ p) = 0 := ringKrullDim_eq_zero_of_field (B ⧸ p)
    rw [hdimp, hdimx] at h0
    exact absurd h0 (by simp)

theorem SliceCMUnmixed.proof (h : CMQuotientUnmixed.Statement) : SliceCMUnmixed.Statement := by
  intro n d J L q hCM hdimB hdimS P hP hPm
  have : IsCohenMacaulayLocalRing (localRingAt J q) := hCM
  have hℓ : ∀ i, linPoly L i - C ((L *ᵥ q) i) ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := by
    intro i
    rw [RingHom.mem_ker, map_sub, eval_linPoly, eval_C, sub_self]
  have hsl : sliceIdeal J L q = J ⊔ Ideal.span (Set.range fun i => linPoly L i - C ((L *ᵥ q) i)) := rfl
  rw [hsl] at hP hdimS ⊢
  have h1 := sliceCMUnmixed_local h (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) J
    (fun i => linPoly L i - C ((L *ᵥ q) i)) hℓ (localRingAt J q)
  have h2 := h1 (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective Ideal.mk_ker
  have h3 := h2 hdimB hdimS
  exact h3 P hP hPm

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorOneComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

namespace DivisorOneComponent

theorem mem_zeroSet_iff {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    q ∈ zeroSet K ↔ K ≤ RingHom.ker (eval q) :=
  ⟨fun h f hf => RingHom.mem_ker.2 (h f hf), fun h _ hf => RingHom.mem_ker.1 (h hf)⟩

theorem isClosed_zeroSet {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet K) := by
  have : zeroSet K = ⋂ f ∈ K, {x : Fin n → ℂ | eval x f = 0} := by ext x; simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

theorem exists_bound (d : ℕ) : ∃ N : WithBot ℕ∞, N < (d : WithBot ℕ∞) ∧
    ∀ x : WithBot ℕ∞, x + 1 ≤ (d : WithBot ℕ∞) → x ≤ N := by
  rcases d with _ | k
  · refine ⟨⊥, WithBot.bot_lt_coe _, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe y =>
      have : y + 1 ≤ 0 := by exact_mod_cast hx
      simp at this
  · refine ⟨(k : WithBot ℕ∞), by exact_mod_cast Nat.lt_succ_self k, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe y =>
      have h1 : y + 1 ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast hx
      have h2 : y ≤ (k : ℕ∞) := by
        cases y using ENat.recTopCoe with
        | top => simp at h1
        | coe y =>
          have h3 : y + 1 ≤ k + 1 := by exact_mod_cast h1
          exact_mod_cast (by omega : y ≤ k)
      exact_mod_cast h2

theorem dim_sup_add_one_le {n d : ℕ} {J W W' : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime] {u : Fin n → ℂ}
    (hu : linForm u ∉ J) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hW : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes)
    (hW' : W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) (hne : W ≠ W') :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1 ≤ (d : WithBot ℕ∞) := by
  have _ : W.IsPrime := hW.1.1
  obtain ⟨x, hxW', hxW⟩ : ∃ x ∈ W', x ∉ W := by
    by_contra! h
    exact hne (le_antisymm (hW.2 hW'.1 h) h)
  have hle : W ⊔ Ideal.span {x} ≤ W ⊔ W' := sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hxW') _
  have hx : x ∈ W ⊔ Ideal.span {x} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  have hr : Ideal.Quotient.mk W x ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ W) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hsurj : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) ≤
      ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor
      (le_sup_left.trans hle)) ?_) (Ideal.Quotient.lift_surjective_of_surjective _ _
        (Ideal.Quotient.factor_surjective _))
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h0 : Ideal.Quotient.mk (W ⊔ W') (c' * x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (hle hx))
    simpa [Ideal.Quotient.factor_mk, map_mul] using h0
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1
      ≤ ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x}) + 1 := by gcongr
    _ ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
    _ = (d : WithBot ℕ∞) := ringKrullDim_component hu hW hdim

end DivisorOneComponent


open DivisorOneComponent in
theorem DivisorOneComponent.proof : DivisorOneComponent.Statement := by
  classical
  intro n d J u hJ hdim hu
  have hKq : ∀ x ∈ zeroSet J, linEval u x = 0 → J ⊔ Ideal.span {linForm u} ≤ RingHom.ker (eval x) := by
    intro x hxJ hxu
    refine sup_le ((mem_zeroSet_iff J x).1 hxJ) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    simpa [linForm, linEval] using hxu
  generalize hK : J ⊔ Ideal.span {linForm u} = K at hKq ⊢
  have hM : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨S, hS⟩ : ∃ S : Finset (Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ)),
      ∀ p, p ∈ S ↔ p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 :=
    ⟨(hM.prod hM).toFinset.filter fun p => p.1 ≠ p.2, fun p => by rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_prod, and_assoc]⟩
  obtain ⟨I, hI⟩ : ∃ I, I = S.inf fun p => p.1 ⊔ p.2 := ⟨_, rfl⟩
  have hmemS : ∀ p ∈ S, p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 := fun p hp => (hS p).1 hp
  have hpair : ∀ W W', W ∈ K.minimalPrimes → W' ∈ K.minimalPrimes → W ≠ W' → I ≤ W ⊔ W' :=
    fun W W' hW hW' hne => by
      have h := Finset.inf_le (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ((hS (W, W')).2 ⟨hW, hW', hne⟩)
      rw [hI]; exact h
  have hKI : K ≤ I := by
    have h := Finset.le_inf (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) (a := K) (s := S) fun p hp => (hmemS p hp).1.1.2.trans le_sup_left
    rw [hI]; exact h
  obtain ⟨N, hN, hxN⟩ := exists_bound d
  refine ⟨I, hKI, ?_, ?_⟩
  · refine lt_of_le_of_lt (ComplexSets.quotient_dim_le_of_minimalPrimes I fun Z hZ => ?_) hN
    have hZI : S.inf (fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ≤ Z := by rw [← hI]; exact hZ.1.2
    obtain ⟨p, hp, hpZ⟩ := (Ideal.IsPrime.inf_le' (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) hZ.1.1).1 hZI
    obtain ⟨h1, h2, h12⟩ := hmemS p hp
    exact (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hpZ)).trans
      (hxN _ (dim_sup_add_one_le hu hdim (by rw [hK]; exact h1) (by rw [hK]; exact h2) h12))
  · intro q hqJ hqu hqI
    obtain ⟨W, hW, hWq⟩ := Ideal.exists_minimalPrimes_le (hKq q hqJ hqu)
    have huniq : ∀ W' ∈ K.minimalPrimes, q ∈ zeroSet W' → W' = W := by
      intro W' hW' hq'
      by_contra hne
      exact hqI ((mem_zeroSet_iff I q).2 ((hpair W W' hW hW' (Ne.symm hne)).trans
        (sup_le hWq ((mem_zeroSet_iff W' q).1 hq'))))
    refine ⟨W, hW, (mem_zeroSet_iff W q).2 hWq, huniq, ⋂ W' ∈ K.minimalPrimes \ {W}, (zeroSet W')ᶜ, ?_, ?_⟩
    · refine (biInter_mem (hM.subset Set.sdiff_subset)).2 fun W' hW' => (isClosed_zeroSet W').isOpen_compl.mem_nhds ?_
      exact fun hq' => hW'.2 (huniq W' hW'.1 hq')
    · rintro x ⟨hxJ, hxU⟩ hxu
      obtain ⟨W'', hW'', hW''x⟩ := Ideal.exists_minimalPrimes_le (hKq x hxJ hxu)
      by_cases h : W'' = W
      · subst h; exact (mem_zeroSet_iff W'' x).2 hW''x
      · exact absurd ((mem_zeroSet_iff W'' x).2 hW''x) (Set.mem_iInter₂.1 hxU W'' ⟨hW'', h⟩)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.POrdDeterminesPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

instance isIntegral_curveNormalisation (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
  inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
    ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))

theorem ringKrullDim_curveNormalisation_le (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    ringKrullDim (curveNormalisation I q) ≤ ringKrullDim (curveLocalRing I q) :=
  Order.krullDim_le_of_strictMono
    (fun Q ↦ ⟨Q.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q)), inferInstance⟩)
    fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap (R := curveLocalRing I q) h

theorem exists_ord_eq_ord_polynomial (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (a : curveLocalRing I q) : ∃ f : MvPolynomial (Fin n) ℂ, ∀ P : MaximalSpectrum (curveNormalisation I q),
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
        Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨⟨f, h⟩, hfh⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval q)).primeCompl y
  refine ⟨f, fun P ↦ ?_⟩
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (h : MvPolynomial (Fin n) ℂ)) :=
    isUnit_algebraMap_curveLocalRing I q h fun H ↦ h.2 (RingHom.mem_ker.2 H)
  let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
  have hπ : ∀ g : MvPolynomial (Fin n) ℂ, algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) g =
      π (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) g) := fun _ ↦ rfl
  have hy' : π y = a := hy
  have hfh' : IsLocalization.mk' (Localization.AtPrime (RingHom.ker (eval q))) f h = y := hfh
  have heq : a *
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (h : MvPolynomial (Fin n) ℂ) =
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by
    rw [← hy', ← hfh', hπ, hπ, ← map_mul, IsLocalization.mk'_spec]
  rw [← heq, map_mul, map_mul, Ring.ord_mul_of_isUnit_right ((hu.map _).map _)]

theorem OrdDeterminesPlace.proof (hfin : CurveNormalisationFinite.Statement) : OrdDeterminesPlace.Statement := by
  intro n I q hrad hdim P P' hord
  have : Module.Finite (curveLocalRing I q) (curveNormalisation I q) := hfin n I q hrad
  have : IsNoetherianRing (curveNormalisation I q) := IsNoetherianRing.of_finite (curveLocalRing I q) _

  have hdimP : ∀ Q : MaximalSpectrum (curveNormalisation I q), Ring.KrullDimLE 1 (Localization.AtPrime Q.asIdeal) := by
    intro Q
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height Q.asIdeal]
    calc (Q.asIdeal.height : WithBot ℕ∞) ≤ ringKrullDim (curveNormalisation I q) :=
          Ideal.height_le_ringKrullDim_of_ne_top Q.isMaximal.ne_top
      _ ≤ ringKrullDim (curveLocalRing I q) := ringKrullDim_curveNormalisation_le I q
      _ = 1 := by rw [hdim]

  have hO : ∀ a : curveLocalRing I q,
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) := by
    intro a
    obtain ⟨f, hf⟩ := exists_ord_eq_ord_polynomial I q a
    rw [hf P, hf P', hord f]
  by_contra hne
  obtain ⟨x, hxP, hxP'⟩ : ∃ x, x ∈ P.asIdeal ∧ x ∉ P'.asIdeal := by
    by_contra! H
    exact hne (MaximalSpectrum.ext (P.isMaximal.eq_of_le P'.isMaximal.ne_top H))

  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (curveLocalRing I q))
    (show ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))) from x).1
  have hax : algebraMap (curveLocalRing I q) (curveNormalisation I q) a =
      algebraMap (curveLocalRing I q) (curveNormalisation I q) s * x := by
    apply Subtype.ext
    change algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) a =
      algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) s * (show ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))) from x).1
    rw [← hs, IsLocalization.mk'_spec']

  have hsN : algebraMap (curveLocalRing I q) (curveNormalisation I q) s ∈ nonZeroDivisors (curveNormalisation I q) := by
    have hu : IsUnit (algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) s) :=
      IsLocalization.map_units _ s
    exact mem_nonZeroDivisors_of_injective (f := (integralClosure (curveLocalRing I q)
      (FractionRing (curveLocalRing I q))).val) Subtype.val_injective hu.mem_nonZeroDivisors
  have hsP : ∀ Q : MaximalSpectrum (curveNormalisation I q),
      algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s) ∈
        nonZeroDivisors (Localization.AtPrime Q.asIdeal) := fun Q ↦
    IsLocalization.nonZeroDivisors_le_comap Q.asIdeal.primeCompl _ hsN

  have h' : Ring.ord (Localization.AtPrime P'.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
      Ring.ord (Localization.AtPrime P'.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) := by
    rw [hax, map_mul, Ring.ord_mul_of_isUnit_right]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ P'.asIdeal x).2 hxP'

  have hP : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
      Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) +
      Ring.ord (Localization.AtPrime P.asIdeal)
        (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) := by
    rw [hax, map_mul, Ring.ord_mul' _ (hsP P)]
  have hfin' : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) ≠ ⊤ := by
    have := hdimP P
    exact Ring.ord_ne_top (hsP P)
  rw [hO a, h', ← hO s] at hP
  have hx0 : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) = 0 := by
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hfin'
    rw [← hk] at hP
    generalize Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) = y at hP ⊢
    induction y using ENat.recTopCoe with
    | top => simp at hP
    | coe m => norm_cast at hP ⊢; omega

  rw [Ring.ord, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top] at hx0
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ P.asIdeal x).1 hx0 hxP

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelGoodPointGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ringKrullDim_quotient_minimalPrime_add_one_of_fintype {σ : Type} [Fintype σ]
    {V W : Ideal (MvPolynomial σ ℂ)} [hVp : V.IsPrime]
    {f : MvPolynomial σ ℂ} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MvPolynomial σ ℂ ⧸ V) ≠ ⊤) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ W) + 1 = ringKrullDim (MvPolynomial σ ℂ ⧸ V) := by
  have hPW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hq : W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk V)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk V f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk V)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk V f ∈ W.map (Ideal.Quotient.mk V) := Ideal.mem_map_of_mem _ hfW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have : IsDomain (MvPolynomial σ ℂ ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ V) (Ideal.Quotient.mkₐ_surjective ℂ V)
  have : IsNoetherianRing (MvPolynomial σ ℂ ⧸ V) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial σ ℂ ⧸ V) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h ↦ by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ ℂ ⧸ V)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial σ ℂ ⧸ V)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial σ ℂ ⧸ V)
    (fun M N hM hN ↦ (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)] at key
  exact_mod_cast key

theorem NormalModelGoodPointGeneric.proof (h₁ : NormalCodimOneCompleteIntersection.Statement)
    (h₂ : NormalCodimOneUniformiser.Statement) (h₃ : JacobianRankOffHypersurface.Statement)
    (h₄ : ProjectionUnramifiedGeneric.Statement) : NormalModelGoodPointGeneric.Statement := by
  classical
  intro n d J u M hJ hdim hu
  have hP : M.ideal.IsPrime := M.isPrime
  set ut : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := rename Sum.inl (linForm u) with hut
  have hutP : ut ∉ M.ideal := by
    intro h
    apply hu
    rw [← M.comap_eq]
    exact h
  have hdimP : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (d + 1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  have hev : ∀ x : Fin n ⊕ Fin M.m → ℂ, eval x ut = linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords x) := fun x ↦ by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hut, linForm, linEval, IndefiniteRowSideFullHecke.ComplexSets.firstCoords, map_sum]
  set L : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) := M.ideal ⊔ Ideal.span {ut} with hL
  have hfinM : L.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ L
  set T := hfinM.toFinset with hT
  have hmemT : ∀ W, W ∈ T ↔ W ∈ L.minimalPrimes := fun W ↦ hfinM.mem_toFinset

  have hdimW : ∀ W ∈ L.minimalPrimes, ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ W) = (d : ℕ) := by
    intro W hW
    have key := ringKrullDim_quotient_minimalPrime_add_one_of_fintype hutP hW (fun h ↦ by
      rw [hdimP] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
    rw [hdimP] at key
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key

  have hgood : ∀ W ∈ L.minimalPrimes, ∃ β : MvPolynomial (Fin n ⊕ Fin M.m) ℂ, β ∉ W ∧
      ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn W, eval w β ≠ 0 → NormalModelDivisorGoodPoint M u d w := by
    intro W hW
    have hWp : W.IsPrime := hW.1.1
    have hPW : M.ideal ≤ W := le_sup_left.trans hW.1.2
    have hutW : ut ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnm : ∀ x y, x ∉ W → y ∉ W → x * y ∉ W := fun x y hx hy hm ↦ (hWp.mem_or_mem hm).elim hx hy
    obtain ⟨c, f, h, hc, hfP, hhW, hgen⟩ :=
      h₁ _ M.ideal W d hP hWp hPW M.isIntegrallyClosed hdimP (hdimW W hW)
    obtain ⟨g, a, b, t, k, hgW, hk, haW, hbW, htW, hrel, hgenW⟩ :=
      h₂ _ M.ideal W d ut hP hWp hPW M.isIntegrallyClosed hdimP (hdimW W hW) hutW hutP
    set q : Fin (c + 1) → MvPolynomial (Fin n ⊕ Fin M.m) ℂ := Fin.cons g f with hq
    have hqW : ∀ j, q j ∈ W := fun j ↦ Fin.cases (by simpa [hq] using hgW)
      (fun j ↦ by simpa [hq] using hPW (hfP j)) j
    have hspan : Ideal.span (Set.range f) ≤ Ideal.span (Set.range q) :=
      Ideal.span_mono (Set.range_subset_iff.2 fun j ↦ ⟨j.succ, by simp [hq]⟩)
    have hgq : g ∈ Ideal.span (Set.range q) := Ideal.subset_span ⟨0, by simp [hq]⟩
    have hgenq : ∀ p ∈ W, ∃ i : ℕ, (h * t) ^ i * p ∈ Ideal.span (Set.range q) := by
      intro p hp
      obtain ⟨i₁, hi₁⟩ := hgenW p hp
      obtain ⟨r, hr, s, hs, hrs⟩ := Submodule.mem_sup.1 hi₁
      obtain ⟨i₂, hi₂⟩ := hgen r hr
      refine ⟨i₁ + i₂, ?_⟩
      have e : (h * t) ^ (i₁ + i₂) * p = h ^ i₁ * t ^ i₂ * (h ^ i₂ * r) + h ^ (i₁ + i₂) * t ^ i₂ * s := by
        linear_combination (-(h ^ (i₁ + i₂) * t ^ i₂)) * hrs
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hspan hi₂))
        (Ideal.mul_mem_left _ _ ((Ideal.span_singleton_le_iff_mem _).2 hgq hs))
    have hint : ∀ i : Fin M.m, ∃ F : Polynomial (MvPolynomial (Fin n) ℂ), F.Monic ∧
        F.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
          (X (Sum.inr i)) ∈ W := fun i ↦ by
      obtain ⟨F, hF, hmem⟩ := M.integral i
      exact ⟨F, hF, hPW hmem⟩
    obtain ⟨μ₁, hμ₁W, hμ₁⟩ := h₃ _ W d (c + 1) q (h * t) hWp (hdimW W hW) hqW (hnm _ _ hhW htW) hgenq
    obtain ⟨μ₂, hμ₂W, hμ₂⟩ := h₄ (Fin n) (Fin M.m) W (c + 1) q (h * t) hWp hint hqW (hnm _ _ hhW htW) hgenq
    refine ⟨h * t * a * b * μ₁ * μ₂,
      hnm _ _ (hnm _ _ (hnm _ _ (hnm _ _ (hnm _ _ hhW htW) haW) hbW) hμ₁W) hμ₂W, fun w hw hβ ↦ ?_⟩
    have hwP : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := fun p hp ↦ hw p (hPW hp)
    simp only [map_mul, ne_eq, mul_eq_zero, not_or] at hβ
    obtain ⟨⟨⟨⟨⟨hwh, hwt⟩, hwa⟩, hwb⟩, hwμ₁⟩, hwμ₂⟩ := hβ
    have hc' : c + (d + 1) = n + M.m := by simpa using hc
    have hfam : (Fin.cons (fun s ↦ eval w (pderiv s g)) (fun j s ↦ eval w (pderiv s (f j))) :
        Fin (c + 1) → Fin n ⊕ Fin M.m → ℂ) = fun j s ↦ eval w (pderiv s (q j)) := by
      funext j s
      refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [hq]
    refine ⟨hwP, c, f, h, g, a, b, k, hc', hfP, hwh, hgen, hw g hgW, ?_, hk, hwa, hwb, hrel, ?_⟩
    · rw [hfam, linearIndependent_iff_card_eq_finrank_span]
      have := hμ₁ w hw hwμ₁
      simp only [Fintype.card_sum, Fintype.card_fin] at this ⊢
      show c + 1 = Module.finrank ℂ (Submodule.span ℂ (Set.range fun j s ↦ eval w (pderiv s (q j))))
      omega
    · intro v hv hgv hfv
      refine hμ₂ w hw hwμ₂ v hv fun j ↦ Fin.cases ?_ (fun j ↦ ?_) j
      · simpa [hq] using hgv
      · simpa [hq] using hfv j
  choose! β hβW hβ using hgood

  have hcomp : ∀ x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords x) = 0 →
      ∃ W ∈ L.minimalPrimes, x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn W := by
    intro x hxJ hxu
    have hxL : L ≤ RingHom.ker (eval x) := sup_le (fun p hp ↦ RingHom.mem_ker.mpr (hxJ p hp))
      (Ideal.span_le.mpr (by simpa [hev] using hxu))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hW, hWx⟩ := Ideal.exists_minimalPrimes_le hxL
    exact ⟨W, hW, fun p hp ↦ RingHom.mem_ker.mp (hWx hp)⟩

  have hsep : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → ∃ g ∈ V, g ∉ W := by
    intro W hW V hV hne
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (hW.2 hV.1 hcon) hcon)
  choose! gg hggV hggW using hsep
  set e : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) → MvPolynomial (Fin n ⊕ Fin M.m) ℂ :=
    fun W ↦ ∏ V ∈ T.erase W, gg W V with he
  have heW : ∀ W ∈ L.minimalPrimes, e W ∉ W := by
    intro W hW hmem
    have : W.IsPrime := hW.1.1
    obtain ⟨V, hV, hgV⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hggW W hW V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) (Finset.ne_of_mem_erase hV).symm hgV
  have heV : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → e W ∈ V := by
    intro W hW V hV hne
    have : V.IsPrime := hV.1.1
    exact Ideal.IsPrime.prod_mem_iff.mpr
      ⟨V, Finset.mem_erase.mpr ⟨hne.symm, (hmemT V).mpr hV⟩, hggV W hW V hV hne⟩
  set F : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := ∑ W ∈ T, β W * e W with hF
  have hsplit : ∀ W ∈ T, F = β W * e W + ∑ V ∈ T.erase W, β V * e V := fun W hW ↦
    (Finset.add_sum_erase T _ hW).symm
  have hrest : ∀ W ∈ L.minimalPrimes, ∑ V ∈ T.erase W, β V * e V ∈ W := by
    intro W hW
    refine Ideal.sum_mem _ fun V hV ↦ Ideal.mul_mem_left _ _ ?_
    exact heV V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) W hW (Finset.ne_of_mem_erase hV)
  have hFW : ∀ W ∈ L.minimalPrimes, F ∉ W := by
    intro W hW hmem
    rw [hsplit W ((hmemT W).mpr hW), Ideal.add_mem_iff_left _ (hrest W hW)] at hmem
    rcases hW.1.1.mem_or_mem hmem with h | h
    · exact hβW W hW h
    · exact heW W hW h
  refine ⟨L ⊔ Ideal.span {F}, le_sup_left, ringKrullDim_quotient_sup_span_lt hFW hdimW, ?_⟩
  intro w hwJ hwu hwB
  obtain ⟨W, hW, hwW⟩ := hcomp w hwJ hwu
  have hFw : eval w F ≠ 0 := by
    intro h0
    refine hwB fun p hp ↦ ?_
    have hle : L ⊔ Ideal.span {F} ≤ RingHom.ker (eval w) := by
      refine sup_le (fun p hp ↦ RingHom.mem_ker.mpr (hwW p (hW.1.2 hp))) (Ideal.span_le.mpr (by simpa using h0))
    exact RingHom.mem_ker.mp (hle hp)
  rw [hsplit W ((hmemT W).mpr hW), map_add (f := _), hwW _ (hrest W hW), add_zero, map_mul] at hFw
  exact hβ W hW w hwW (left_ne_zero_of_mul hFw)

end

end GroundTheory.Heights₂.Heights
end
