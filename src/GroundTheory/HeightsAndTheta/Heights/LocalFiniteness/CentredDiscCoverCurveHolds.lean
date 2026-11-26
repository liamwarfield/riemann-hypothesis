module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMinimalPrimePlace

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StReducedNormalisationPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def ReducedNormalisationPlace.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (P : MaximalSpectrum (integralClosure R (FractionRing R))),
    ∃ p ∈ minimalPrimes R, ∀ (S : Type) [CommRing S] (φ : R →+* S),
      Function.Surjective φ → RingHom.ker φ = p →
        ∃ P' : MaximalSpectrum (integralClosure S (FractionRing S)), ∀ x : R,
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (integralClosure R (FractionRing R)) (Localization.AtPrime P.asIdeal)
                (algebraMap R (integralClosure R (FractionRing R)) x)) =
            Ring.ord (Localization.AtPrime P'.asIdeal)
              (algebraMap (integralClosure S (FractionRing S)) (Localization.AtPrime P'.asIdeal)
                (algebraMap S (integralClosure S (FractionRing S)) (φ x)))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroDimIsolated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def ZeroDimIsolated.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) ≤ 0 → ∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ {q}

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimComponentBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def LocalDimComponentBound.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), q ∈ zeroSet I →
    ∃ W : Ideal (MvPolynomial (Fin n) ℂ), W.IsPrime ∧ I ≤ W ∧ q ∈ zeroSet W ∧
      ringKrullDim (curveLocalRing I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveMinimalPrimeQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def CurveMinimalPrimeQuotient.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (p : Ideal (curveLocalRing I q)),
    p ∈ minimalPrimes (curveLocalRing I q) →
      ∃ J : Ideal (MvPolynomial (Fin n) ℂ), J ∈ I.minimalPrimes ∧ J ≤ RingHom.ker (eval q) ∧
        ∃ φ : curveLocalRing I q →+* curveLocalRing J q, Function.Surjective φ ∧ RingHom.ker φ = p ∧
          ∀ f : MvPolynomial (Fin n) ℂ, φ (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f) =
            algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PReducedNormalisationPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets MinimalPrimePlace

noncomputable section

namespace ReducedNormalisationPlace

variable {A B : Type*} [CommRing A] [CommRing B]

theorem fracMap_mk'_eq_zero_iff [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (a : A)
    (u : nonZeroDivisors A) :
    fracMap π hker (IsLocalization.mk' (FractionRing A) a u) = 0 ↔ a ∈ RingHom.ker π := by
  rw [IsLocalization.map_mk', IsFractionRing.mk'_eq_zero_iff_eq_zero, RingHom.mem_ker]

theorem fracMap_eq_zero_iff {C : Type*} [CommRing C] [IsDomain B] [IsDomain C] (π : A →+* B) (π' : A →+* C)
    (hker : RingHom.ker π ∈ minimalPrimes A) (hker' : RingHom.ker π' ∈ minimalPrimes A)
    (h : RingHom.ker π = RingHom.ker π') (z : FractionRing A) :
    fracMap π hker z = 0 ↔ fracMap π' hker' z = 0 := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  rw [fracMap_mk'_eq_zero_iff, fracMap_mk'_eq_zero_iff, h]

theorem eq_zero_of_forall_num_mem [IsReduced A] (z : FractionRing A)
    (h : ∀ p ∈ minimalPrimes A, ∀ (a : A) (u : nonZeroDivisors A),
      z = IsLocalization.mk' (FractionRing A) a u → a ∈ p) : z = 0 := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  show IsLocalization.mk' (FractionRing A) a u = 0
  rw [eq_zero_of_forall_mem_minimalPrimes fun p hp ↦ h p hp a u rfl, IsLocalization.mk'_zero]

theorem exists_idempotent [IsNoetherianRing A] [IsReduced A] (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    ∃ e : integralClosure A (FractionRing A), ∀ (B : Type) [CommRing B] [IsDomain B] (π : A →+* B),
      Function.Surjective π → ∀ hker : RingHom.ker π = p,
        fracMap π (by rw [hker]; exact hp) e = 1 ∧
          ∀ z, fracMap π (by rw [hker]; exact hp) z = 0 → (e : FractionRing A) * z = 0 := by
  have := hp.1.1
  have hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes A := by rwa [Ideal.mk_ker]
  obtain ⟨e, he1, hek, -⟩ := exists_fracMap_unit (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective hk
  have he : IsIntegral A e := by
    simpa using isIntegral_mul_of_fracMap _ Ideal.Quotient.mk_surjective hk (x := 1) he1 hek
      (by rw [map_one]; exact isIntegral_one)
  refine ⟨⟨e, he⟩, fun B _ _ π _ hker ↦ ⟨?_, fun z hz ↦ hek z ?_⟩⟩
  · have hπ : RingHom.ker π ∈ minimalPrimes A := by rw [hker]; exact hp
    rw [← sub_eq_zero, ← map_one (fracMap π hπ), ← map_sub,
      fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]), map_sub, he1, map_one,
      sub_self]
  · have hπ : RingHom.ker π ∈ minimalPrimes A := by rw [hker]; exact hp
    exact (fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]) z).1 hz

end ReducedNormalisationPlace


open ReducedNormalisationPlace in
theorem ReducedNormalisationPlace.proof : ReducedNormalisationPlace.Statement := by
  intro R _ _ _ P
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have := P.isMaximal.isPrime
  choose! e he using fun p (hp : p ∈ minimalPrimes R) ↦ exists_idempotent p hp
  have hprodK : ∏ p ∈ hfin.toFinset, (1 - (e p : FractionRing R)) = 0 := by
    refine eq_zero_of_forall_num_mem _ fun p hp a u hz ↦ ?_
    have := hp.1.1
    have hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes R := by rwa [Ideal.mk_ker]
    have h0 : fracMap (Ideal.Quotient.mk p) hk (∏ q ∈ hfin.toFinset, (1 - (e q : FractionRing R))) = 0 := by
      rw [map_prod]
      refine Finset.prod_eq_zero (hfin.mem_toFinset.2 hp) ?_
      rw [map_sub, map_one,
        (he p hp (R ⧸ p) (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective Ideal.mk_ker).1, sub_self]
    rw [hz, fracMap_mk'_eq_zero_iff, Ideal.mk_ker] at h0
    exact h0
  have hprod : ∏ p ∈ hfin.toFinset, (1 - e p) = 0 := Subtype.ext (by push_cast; exact hprodK)
  obtain ⟨p, hpT, hp1⟩ := (Ideal.IsPrime.prod_mem_iff (p := P.asIdeal)).1
    (by rw [hprod]; exact P.asIdeal.zero_mem)
  have hpmin : p ∈ minimalPrimes R := hfin.mem_toFinset.1 hpT
  have hepP : e p ∉ P.asIdeal := fun h ↦
    P.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.asIdeal.add_mem h hp1))
  refine ⟨p, hpmin, fun S _ φ hφ hkerφ ↦ ?_⟩
  have hpr : (RingHom.ker φ).IsPrime := hkerφ ▸ hpmin.1.1
  have : IsDomain S :=
    MulEquiv.isDomain (R ⧸ RingHom.ker φ) (RingHom.quotientKerEquivOfSurjective hφ).symm.toMulEquiv
  have hker : RingHom.ker φ ∈ minimalPrimes R := by rw [hkerφ]; exact hpmin
  obtain ⟨he1, hek⟩ := he p hpmin S φ hφ hkerφ
  obtain ⟨_, -, -, hsurj⟩ := exists_fracMap_unit φ hφ hker
  have hN : Function.Surjective (normMap φ hker) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hint : IsIntegral R ((e p : FractionRing R) * x) :=
      isIntegral_mul_of_fracMap φ hφ hker he1 hek (by rw [hx]; exact y.2)
    refine ⟨⟨_, hint⟩, Subtype.ext ?_⟩
    show fracMap φ hker ((e p : FractionRing R) * x) = y
    rw [map_mul, he1, one_mul, hx]
  have hε1 : normMap φ hker (e p) = 1 := Subtype.ext he1
  have hε : ∀ z, normMap φ hker z = 0 → e p * z = 0 := fun z hz ↦
    Subtype.ext (hek z (congrArg Subtype.val hz))
  have hkerP : RingHom.ker (normMap φ hker) ≤ P.asIdeal := fun z hz ↦
    (P.isMaximal.isPrime.mem_or_mem (by rw [hε z hz]; exact P.asIdeal.zero_mem)).resolve_left hepP
  have hcm : (P.asIdeal.map (normMap φ hker)).comap (normMap φ hker) = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ hN, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hkerP]
  have hmax : (P.asIdeal.map (normMap φ hker)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hN P.isMaximal).resolve_left fun h ↦
      P.isMaximal.ne_top (by rw [← hcm, h, Ideal.comap_top])
  obtain ⟨E, hE⟩ := exists_localization_ringEquiv (normMap φ hker) hN (e p) hε1 hε
    (P.asIdeal.map (normMap φ hker))
  refine ⟨⟨_, hmax⟩, fun x ↦ ?_⟩
  have key : ∀ (Q : Ideal (integralClosure R (FractionRing R))) [Q.IsPrime], Q = P.asIdeal →
      ∀ E' : Localization.AtPrime Q ≃+* Localization.AtPrime (P.asIdeal.map (normMap φ hker)),
        (∀ r, E' (algebraMap _ _ r) = algebraMap _ _ (normMap φ hker r)) →
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap _ (Localization.AtPrime P.asIdeal) (algebraMap R (integralClosure R (FractionRing R)) x)) =
          Ring.ord (Localization.AtPrime (P.asIdeal.map (normMap φ hker)))
            (algebraMap _ (Localization.AtPrime (P.asIdeal.map (normMap φ hker)))
              (algebraMap S (integralClosure S (FractionRing S)) (φ x))) := by
    rintro Q _ rfl E' hE'
    rw [← ord_ringEquiv (R := Localization.AtPrime P.asIdeal)
      (S := Localization.AtPrime (P.asIdeal.map (normMap φ hker))) E', hE', normMap_algebraMap]
  exact key _ hcm E hE

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceOnComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] (hR : ringKrullDim R = 1) {p : Ideal R} (hp : p ∈ minimalPrimes R) (φ : R →+* S)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = p) : ringKrullDim S = 1 := by
  have hpp : p.IsPrime := hp.1.1
  refine le_antisymm (hR ▸ ringKrullDim_le_of_surjective φ hφ) ?_
  obtain ⟨x, y, hxy⟩ := Order.one_le_krullDim_iff.1 (le_of_eq hR.symm : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
  have hxm : x.asIdeal < IsLocalRing.maximalIdeal R :=
    lt_of_lt_of_le hxy (IsLocalRing.le_maximalIdeal y.isPrime.ne_top)
  have hpm : p < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpp.ne_top) fun h ↦ ?_
    have hpx : p ≤ x.asIdeal := hp.2 ⟨x.isPrime, bot_le⟩ (h ▸ hxm.le)
    exact (lt_of_le_of_lt hpx hxm).ne h
  have hk : ∀ K : Ideal R, p ≤ K → (K.map φ).comap φ = K := fun K hK ↦ by
    rw [Ideal.comap_map_of_surjective' φ hφ, hker, sup_eq_left.2 hK]
  have h0 : (p.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hker.le
  have h1 : ((IsLocalRing.maximalIdeal R).map φ).IsPrime :=
    Ideal.map_isPrime_of_surjective hφ (hker.le.trans hpm.le)
  refine Order.one_le_krullDim_iff.2 ⟨⟨_, h0⟩, ⟨_, h1⟩, ?_⟩
  change p.map φ < (IsLocalRing.maximalIdeal R).map φ
  refine lt_of_le_of_ne (Ideal.map_mono hpm.le) fun h ↦ hpm.ne ?_
  rw [← hk p le_rfl, h, hk _ hpm.le]

theorem PlaceOnComponent.proof (h₁ : ReducedNormalisationPlace.Statement)
    (h₂ : CurveMinimalPrimeQuotient.Statement) : PlaceOnComponent.Statement := by
  intro n I q hrad hdim P
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  have : Nontrivial (curveLocalRing I q) := by
    refine not_subsingleton_iff_nontrivial.1 fun h ↦ ?_
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨p, hp, hS⟩ := h₁ (curveLocalRing I q) P
  obtain ⟨J, hJ, hJq, φ, hφ, hker, hφf⟩ := h₂ n I q p hp
  obtain ⟨P', hP'⟩ := hS (curveLocalRing J q) φ hφ hker
  refine ⟨J, hJ, hJq, ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes hdim hp φ hφ hker, P', fun f ↦ ?_⟩
  have e := hP' (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)
  rw [hφf] at e
  exact e

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchGermDimOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology
open scoped NNReal ENNReal

theorem VarBranch.dimH_image_le_two {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (c : VarBranch I 1 q) : dimH c.image ≤ 2 := by
  let ι : ℂ → (Fin 1 → ℂ) := fun τ _ ↦ τ
  have hι : ∀ τ : ℂ, ‖ι τ‖ = ‖τ‖ := fun τ ↦ by simp [ι, pi_norm_const]
  have himg : c.image = (c.toFun ∘ ι) '' Metric.ball 0 c.radius := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t 0, ?_, ?_⟩
      · have h0 : ‖t 0‖ ≤ ‖t‖ := norm_le_pi_norm t 0
        rw [Metric.mem_ball, dist_zero_right] at ht ⊢
        linarith
      · simp only [Function.comp, ι]
        congr 1
        funext i
        rw [Subsingleton.elim i 0]
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨ι τ, ?_, rfl⟩
      rw [Metric.mem_ball, dist_zero_right] at hτ ⊢
      rwa [hι]
  have hd : DifferentiableOn ℂ (c.toFun ∘ ι) (Metric.ball 0 c.radius) := by
    have hιd : Differentiable ℂ ι := differentiable_pi.2 fun _ ↦ differentiable_id
    refine c.differentiableOn.comp hιd.differentiableOn fun τ hτ ↦ ?_
    rw [Metric.mem_ball, dist_zero_right] at hτ ⊢
    rwa [hι]
  have hcd : ContDiffOn ℝ 1 (c.toFun ∘ ι) (Metric.ball 0 c.radius) :=
    (hd.contDiffOn Metric.isOpen_ball).restrict_scalars ℝ
  rw [himg]
  calc dimH ((c.toFun ∘ ι) '' Metric.ball 0 c.radius) ≤ dimH (Metric.ball (0 : ℂ) c.radius) :=
        hcd.dimH_image_le (convex_ball 0 c.radius) le_rfl
    _ ≤ dimH (Set.univ : Set ℂ) := dimH_mono (Set.subset_univ _)
    _ = 2 := by rw [Real.dimH_univ_eq_finrank ℂ, Complex.finrank_real_complex]; norm_num

theorem BranchGermDimOne.proof (h₀ : LocalDimComponentBound.Statement) (h₁ : ZeroDimIsolated.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement) : BranchGermDimOne.Statement := by
  intro n I q m c hm ⟨N, hN, hcov⟩
  let c₀ := c ⟨0, hm⟩
  have hq : q ∈ zeroSet I := c₀.map_zero ▸ c₀.mapsTo (Metric.mem_ball_self c₀.radius_pos)
  have hdimH : dimH (zeroSet I ∩ N) ≤ 2 :=
    (dimH_mono hcov).trans ((dimH_iUnion _).le.trans (iSup_le fun b ↦ (c b).dimH_image_le_two))
  apply le_antisymm
  · obtain ⟨W, hW, hIW, hqW, hle⟩ := h₀ n I q hq
    have hup : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : ℕ) := by
      refine (ringKrullDim_quotient_le W).trans (le_of_eq ?_)
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) := by
      have := hW
      exact ringKrullDim_nonneg_of_nontrivial
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d := by
      revert hnn hup
      generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = x
      intro hup hnn
      induction x using WithBot.recBotCoe with
      | bot => exact absurd hnn (by simp)
      | coe e =>
        induction e using ENat.recTopCoe with
        | top => exact absurd hup (not_le.2 (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n)))
        | coe d => exact ⟨d, rfl⟩
    rw [hd] at hle
    refine hle.trans ?_
    by_contra hlt
    have h2 : 2 ≤ d := by
      by_contra h
      exact hlt (by exact_mod_cast (by omega : d ≤ 1))
    have hpos := h₂ n d W hW hd q (interior N) isOpen_interior (mem_interior_iff_mem_nhds.2 hN) hqW
    have hsub : zeroSet W ∩ interior N ⊆ zeroSet I ∩ N :=
      fun x hx ↦ ⟨fun f hf ↦ hx.1 f (hIW hf), interior_subset hx.2⟩
    have hlt' : dimH (zeroSet W ∩ interior N) < (((2 * d : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      refine ((dimH_mono hsub).trans hdimH).trans_lt ?_
      rw [ENNReal.coe_natCast]
      exact_mod_cast (by omega : 2 < 2 * d)
    have h0 := hausdorffMeasure_of_dimH_lt hlt'
    rw [NNReal.coe_natCast] at h0
    exact hpos.ne' h0
  · by_contra hlt
    have h0 : ringKrullDim (curveLocalRing I q) ≤ 0 := by
      generalize ringKrullDim (curveLocalRing I q) = x at hlt
      induction x using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe e =>
        have he : e < 1 := by
          by_contra h'
          exact hlt (by exact_mod_cast not_lt.1 h')
        rw [Order.lt_one_iff] at he
        subst he
        exact le_rfl
    obtain ⟨N', hN', hiso⟩ := h₁ n I q h0
    have hcont : ContinuousAt c₀.toFun 0 :=
      c₀.differentiableOn.continuousOn.continuousAt (Metric.ball_mem_nhds 0 c₀.radius_pos)
    have hN'' : N' ∈ 𝓝 (c₀.toFun 0) := by rw [c₀.map_zero]; exact hN'
    have hev : ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), t ∈ Metric.ball 0 c₀.radius ∧ c₀.toFun t ∈ N' :=
      Filter.Eventually.and (Metric.ball_mem_nhds 0 c₀.radius_pos) (hcont hN'')
    have hne : (𝓝[≠] (0 : Fin 1 → ℂ)).NeBot := inferInstance
    have hev' : ∀ᶠ t in 𝓝[≠] (0 : Fin 1 → ℂ), (t ∈ Metric.ball 0 c₀.radius ∧ c₀.toFun t ∈ N') ∧ t ≠ 0 :=
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev).and self_mem_nhdsWithin
    obtain ⟨t, ⟨ht, htN⟩, ht0⟩ := hev'.exists
    have hx : c₀.toFun t = q := hiso ⟨c₀.mapsTo ht, htN⟩
    exact ht0 (c₀.injOn ht (Metric.mem_ball_self c₀.radius_pos) (hx.trans c₀.map_zero.symm))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZeroDimIsolated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem ZeroDimIsolated.proof : ZeroDimIsolated.Statement := by
  intro n I q hdim
  classical
  have : Ring.KrullDimLE 0 (curveLocalRing I q) := Ring.krullDimLE_iff.2 (by simpa using hdim)
  have hnil : ∀ i : Fin n, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧
      ∃ k : ℕ, s * (X i - C (q i)) ^ k ∈ I := by
    intro i
    have hmem : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i - C (q i)) ∈
        Ring.jacobson (curveLocalRing I q) := by
      rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
      intro P hP
      have hP' : Ideal.IsMaximal P := hP
      let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
      have hPm : (Ideal.comap π P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective (H := hP')
      have hL : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
          (X i - C (q i)) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval q))) := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (RingHom.ker (eval q))]
        simp [RingHom.mem_ker]
      rw [← IsLocalRing.eq_maximalIdeal hPm] at hL
      exact hL
    rw [Ring.jacobson_eq_nilradical_of_krullDimLE_zero, mem_nilradical] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [← map_pow] at hk
    have hmap : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
        ((X i - C (q i)) ^ k) ∈
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.Quotient.eq_zero_iff_mem.1 hk
    obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (RingHom.ker (eval q)).primeCompl (Localization.AtPrime (RingHom.ker (eval q))) I _).1 hmap
    exact ⟨m, fun h ↦ hm (RingHom.mem_ker.2 h), k, hmI⟩
  choose s hs k hk using hnil
  refine ⟨{x | eval x (∏ i, s i) ≠ 0}, ?_, ?_⟩
  · apply (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const).mem_nhds
    simp [map_prod, Finset.prod_ne_zero_iff, hs]
  · rintro x ⟨hxZ, hxN⟩
    simp only [Set.mem_ofPred_eq, map_prod, Finset.prod_ne_zero_iff] at hxN
    rw [Set.mem_singleton_iff]
    funext i
    have h := hxZ _ (hk i)
    simp only [map_mul, map_pow, map_sub, eval_X, eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at h
    rcases h with h | ⟨h, -⟩
    · exact absurd h (hxN i (Finset.mem_univ i))
    · exact sub_eq_zero.1 h

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimComponentBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

theorem comap_curveLocalRing_strictMono (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    StrictMono (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q))) := by
  refine Monotone.strictMono_of_injective (fun P Q h ↦ Ideal.comap_mono h) ?_
  intro P Q h
  apply PrimeSpectrum.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := I.map
    (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))
  apply PrimeSpectrum.localization_comap_injective _ (RingHom.ker (eval q)).primeCompl
  exact h

theorem le_comap_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    I ≤ (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal := by
  intro x hx
  have h0 : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q)))))
      (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hx)
  change algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x ∈ P.asIdeal
  rw [show algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x = 0 from h0]
  exact P.asIdeal.zero_mem

theorem comap_curveLocalRing_le (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal ≤
      RingHom.ker (eval q) := by
  intro x hx
  by_contra h
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
    (isUnit_algebraMap_curveLocalRing I q x fun h' ↦ h (RingHom.mem_ker.2 h')))

theorem LocalDimComponentBound.proof : LocalDimComponentBound.Statement := by
  intro n I q hq
  rcases subsingleton_or_nontrivial (curveLocalRing I q) with hO | hO
  · refine ⟨RingHom.ker (eval q), inferInstance, fun x hx ↦ RingHom.mem_ker.2 (hq x hx),
      fun x hx ↦ RingHom.mem_ker.1 hx, ?_⟩
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set f := algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)
  set p := LTSeries.longestOf (PrimeSpectrum (curveLocalRing I q))
  set W := (PrimeSpectrum.comap f p.head).asIdeal with hW
  have hWle : ∀ i, W ≤ (PrimeSpectrum.comap f (p i)).asIdeal := fun i ↦
    Ideal.comap_mono (p.monotone (Fin.zero_le i))
  let p' : LTSeries (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) W) :=
    { length := p.length
      toFun := fun i ↦ ⟨PrimeSpectrum.comap f (p i), hWle i⟩
      step := fun i ↦ comap_curveLocalRing_strictMono I q (p.step i) }
  refine ⟨W, (PrimeSpectrum.comap f p.head).isPrime, le_comap_curveLocalRing I q _,
    fun x hx ↦ RingHom.mem_ker.1 (comap_curveLocalRing_le I q _ hx), ?_⟩
  rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder, ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim p'

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveMinimalPrimeQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem CurveMinimalPrimeQuotient.proof : CurveMinimalPrimeQuotient.Statement := by
  intro n I q p hp
  have hpP : p.IsPrime := hp.1.1

  let ext : Ideal (MvPolynomial (Fin n) ℂ) → Ideal (Localization.AtPrime (RingHom.ker (eval q))) :=
    fun K ↦ K.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  let mk := Ideal.Quotient.mk (ext I)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomp : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) =
      mk.comp (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) := rfl

  let P : Ideal (Localization.AtPrime (RingHom.ker (eval q))) := p.comap mk
  have hPP : P.IsPrime := Ideal.comap_isPrime mk p
  have hIP : ext I ≤ P := fun x hx ↦ by
    change mk x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact p.zero_mem
  have hpmap : P.map mk = p := Ideal.map_comap_of_surjective mk hmk p
  let J : Ideal (MvPolynomial (Fin n) ℂ) :=
    P.comap (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  have hJP : J.IsPrime := Ideal.comap_isPrime _ P
  have hJmem : ∀ f, f ∈ J ↔ algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ p := fun f ↦ by
    rw [hcomp]; rfl
  have hextJ : ext J = P := IsLocalization.map_under (RingHom.ker (eval q)).primeCompl _ P
  have hIJ : I ≤ J := fun f hf ↦ hIP (Ideal.mem_map_of_mem _ hf)
  have hJm : J ≤ RingHom.ker (eval q) := by
    intro f hf
    by_contra h
    exact hpP.ne_top (Ideal.eq_top_of_isUnit_mem _ ((hJmem f).1 hf)
      (isUnit_algebraMap_curveLocalRing I q f fun h' ↦ h (RingHom.mem_ker.2 h')))

  have hJmin : J ∈ I.minimalPrimes := by
    refine ⟨⟨hJP, hIJ⟩, fun J' hJ' hJ'J ↦ ?_⟩
    obtain ⟨hJ'P, hIJ'⟩ := hJ'
    have hdisj : Disjoint ((RingHom.ker (eval q)).primeCompl : Set (MvPolynomial (Fin n) ℂ)) J' :=
      Set.disjoint_left.2 fun x hx hx' ↦ hx (hJm (hJ'J hx'))
    have hP'P : (ext J').IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl _ J' hJ'P hdisj
    have hIP' : ext I ≤ ext J' := Ideal.map_mono hIJ'
    have hker : RingHom.ker mk ≤ ext J' := by
      rw [Ideal.mk_ker]; exact hIP'
    have hp'P : ((ext J').map mk).IsPrime := Ideal.map_isPrime_of_surjective hmk hker
    have hp'le : (ext J').map mk ≤ p := by
      rw [← hpmap, ← hextJ]
      exact Ideal.map_mono (Ideal.map_mono hJ'J)
    have hpp' : p ≤ (ext J').map mk := hp.2 ⟨hp'P, bot_le⟩ hp'le
    intro f hf
    have h1 : mk (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) f) ∈ (ext J').map mk :=
      hpp' ((hJmem f).1 hf)
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective mk hmk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.2 hIP'] at h1
    have h2 := (IsLocalization.under_map_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl
      (Localization.AtPrime (RingHom.ker (eval q))) hJ'P hdisj)
    rw [← h2]
    exact h1

  have hle : ext I ≤ ext J := Ideal.map_mono hIJ
  refine ⟨J, hJmin, hJm, (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q),
    Ideal.Quotient.factor_surjective hle, ?_, fun f ↦ Ideal.Quotient.factor_mk hle _⟩
  change RingHom.ker (Ideal.Quotient.factor hle) = p
  rw [Ideal.Quotient.factor_ker, hextJ]
  exact hpmap

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCentredDiscCoverCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Matrix

noncomputable section

theorem centredDiscCover_punctured_branch (hPCC : PuncturedCoverCycles.Statement)
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) :
    ∃ (δ : ℝ) (k : ℕ) (φ : ℂ → σ → ℂ), 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ k ∧
      DifferentiableOn ℂ φ (ball 0 δ \ {0}) ∧ Set.InjOn φ (ball 0 δ \ {0}) ∧
      ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k := by
  obtain ⟨hwY, hN, hmaps, huniq, hcard, -, hsec⟩ := hY
  have hρ : 0 < ρ := dist_nonneg.trans_lt (hmaps hwY)
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let Φ : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv
  let L : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    ContinuousLinearMap.pi fun _ => p.comp (Φ : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))
  let A : Matrix (Fin (0 + 1)) (Fin (Fintype.card σ)) ℂ :=
    LinearMap.toMatrix' (L : (Fin (Fintype.card σ) → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))
  have hA : ∀ z, A *ᵥ z = fun _ => p (Φ z) := fun z => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hpT : ∀ z, p (w + Φ z) = p w + p (Φ z) := fun z => map_add p w (Φ z)
  have hT : ∀ x, w + Φ (Φ.symm (x - w)) = x := fun x => by simp
  have hone : ∀ (y : Fin (0 + 1) → ℂ) (t : ℂ), t = y 0 → (fun _ => t) = y := fun y t ht => by
    funext i
    rw [show i = 0 from Subsingleton.elim (α := Fin 1) _ _, ht]
  let X : Set (Fin (Fintype.card σ) → ℂ) := {z | w + Φ z ∈ Y ∧ p (Φ z) ≠ 0}
  obtain ⟨m, ord, ψ, δ, hδ, hδ1, hsum, hord, hdiff, hmap, hinj, -, -⟩ :=
    hPCC (Fintype.card σ) 0 N A 0 ρ X hρ rfl
      (fun x hx => by
        rw [hA, dist_zero_right, pi_norm_const]
        refine ⟨?_, hx.2⟩
        have := hmaps hx.1
        rwa [mem_ball, dist_eq_norm, hpT, add_sub_cancel_left] at this)
      (fun y hy hy0 => by
        have hyρ : p w + y 0 ∈ ball (p w) ρ := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
          exact (norm_le_pi_norm y 0).trans_lt (by rwa [dist_zero_right] at hy)
        rw [← hcard _ hyρ (by simpa using hy0), ← ((add_right_injective w).comp Φ.injective).injOn.encard_image]
        congr 1
        ext x
        constructor
        · rintro ⟨z, ⟨⟨hzY, -⟩, hzy⟩, rfl⟩
          refine ⟨hzY, ?_⟩
          rw [Function.comp_apply, hpT, ← congrFun ((hA z).symm.trans hzy) 0]
        · rintro ⟨hxY, hxp⟩
          refine ⟨Φ.symm (x - w), ⟨⟨by rwa [hT], ?_⟩, ?_⟩, hT x⟩
          · simpa [hxp] using hy0
          · rw [hA]
            exact hone y _ (by simp [hxp]))
      (fun x hx => by
        obtain ⟨O₀, V₀, g₀, hO₀, hV₀, hxV₀, hg₀, hpg₀, hYV⟩ :=
          hsec (w + Φ x) hx.1 (by rw [hpT]; simpa using hx.2)
        have hsec' : ∀ z, w + Φ z ∈ Y ∩ V₀ → p w + p (Φ z) ∈ O₀ ∧ g₀ (p w + p (Φ z)) = w + Φ z := by
          intro z hz
          rw [hYV] at hz
          obtain ⟨t, ht, hgt⟩ := hz
          have : t = p w + p (Φ z) := by rw [← hpT, ← hgt, hpg₀ t ht]
          subst this
          exact ⟨ht, hgt⟩
        obtain ⟨hxO, hgx⟩ := hsec' x ⟨hx.1, hxV₀⟩
        refine ⟨{y | p w + y 0 ∈ O₀ ∧ y 0 ≠ 0}, {z | w + Φ z ∈ V₀ ∧ p (Φ z) ≠ 0},
          fun y => Φ.symm (g₀ (p w + y 0) - w),
          (hO₀.preimage (continuous_const.add (continuous_apply 0))).inter
            (isOpen_ne_fun (continuous_apply 0) continuous_const),
          by rw [hA]; exact ⟨hxO, hx.2⟩,
          (hV₀.preimage (continuous_const.add Φ.continuous)).inter
            (isOpen_ne_fun (p.continuous.comp Φ.continuous) continuous_const),
          ⟨hxV₀, hx.2⟩, ?_, by rw [hA]; simp [hgx], fun y hy => ?_, ?_⟩
        · refine Φ.symm.differentiable.comp_differentiableOn
            ((hg₀.comp ((differentiableOn_const _).add (differentiable_apply 0).differentiableOn)
              ?_).sub_const w)
          intro y hy
          exact hy.1
        · rw [hA]
          refine hone y _ ?_
          simp [hpg₀ _ hy.1]
        · ext z
          constructor
          · rintro ⟨⟨hzY, hz0⟩, hzV, -⟩
            obtain ⟨hzO, hgz⟩ := hsec' z ⟨hzY, hzV⟩
            exact ⟨fun _ => p (Φ z), ⟨hzO, hz0⟩, by simp [hgz]⟩
          · rintro ⟨y, ⟨hyO, hy0⟩, rfl⟩
            have hw : w + Φ (Φ.symm (g₀ (p w + y 0) - w)) = g₀ (p w + y 0) := hT _
            have hp : p (Φ (Φ.symm (g₀ (p w + y 0) - w))) = y 0 := by simp [hpg₀ _ hyO]
            have hmem : g₀ (p w + y 0) ∈ Y ∩ V₀ := by rw [hYV]; exact ⟨_, hyO, rfl⟩
            show (w + Φ (Φ.symm (g₀ (p w + y 0) - w)) ∈ Y ∧ p (Φ (Φ.symm (g₀ (p w + y 0) - w))) ≠ 0) ∧
              (w + Φ (Φ.symm (g₀ (p w + y 0) - w)) ∈ V₀ ∧ p (Φ (Φ.symm (g₀ (p w + y 0) - w))) ≠ 0)
            rw [hw, hp]
            exact ⟨⟨hmem.1, hy0⟩, hmem.2, hy0⟩)
  obtain ⟨b⟩ : Nonempty (Fin m) := by
    rcases m with _ | m
    · simp at hsum
      omega
    · exact ⟨0⟩
  have hpunct : ∀ s ∈ ball (0 : ℂ) δ \ {0},
      (fun _ => s) ∈ ball (0 : Fin (0 + 1) → ℂ) δ ∩ {t | t 0 ≠ 0} := fun s hs =>
    ⟨by rw [mem_ball, dist_zero_right, pi_norm_const]; exact mem_ball_zero_iff.1 hs.1, hs.2⟩
  refine ⟨δ, ord b, fun s => w + Φ (ψ b fun _ => s), hδ, hδ1, hord b, ?_, ?_, fun s hs => ?_⟩
  · exact (differentiableOn_const w).add (Φ.differentiable.comp_differentiableOn
      ((hdiff b).comp (differentiable_pi.2 fun _ => differentiable_id).differentiableOn hpunct))
  · intro s hs s' hs' hss'
    have := hinj b (hpunct s hs) (hpunct s' hs') (Φ.injective (add_left_cancel hss'))
    exact congrFun this 0
  · obtain ⟨hX, hAψ⟩ := hmap b _ (hpunct s hs)
    refine ⟨hX.1, ?_⟩
    rw [hpT]
    have := congrFun ((hA _).symm.trans hAψ) 0
    simp only [Function.update_self] at this
    rw [this]

theorem centredDiscCover_extend_across_centre
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) {δ : ℝ} {k : ℕ} {φ : ℂ → σ → ℂ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 1 ≤ k) (hφd : DifferentiableOn ℂ φ (ball 0 δ \ {0})) (hφi : Set.InjOn φ (ball 0 δ \ {0}))
    (hφY : ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k) :
    ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
      DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) Y := by
  obtain ⟨hwY, -, hmaps, huniq, -, hprop, -⟩ := hY
  have hρ : 0 < ρ := dist_nonneg.trans_lt (hmaps hwY)
  set r := min δ (ρ / 2) with hr
  have hr0 : 0 < r := lt_min hδ (half_pos hρ)
  have hrδ : ball (0 : ℂ) r \ {0} ⊆ ball 0 δ \ {0} :=
    Set.sdiff_subset_sdiff_left (ball_subset_ball (min_le_left _ _))
  have hK : IsCompact {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} :=
    hprop _ (closedBall_subset_ball (half_lt_self hρ)) (isCompact_closedBall _ _)
  have hφK : ∀ s ∈ ball (0 : ℂ) r \ {0}, φ s ∈ {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} := by
    intro s hs
    obtain ⟨hY', hp⟩ := hφY s (hrδ hs)
    refine ⟨hY', ?_⟩
    rw [mem_closedBall, hp, dist_eq_norm, add_sub_cancel_left, norm_pow]
    have h1 : ‖s‖ < r := mem_ball_zero_iff.1 hs.1
    calc ‖s‖ ^ k ≤ ‖s‖ :=
          pow_le_of_le_one (norm_nonneg _) (h1.le.trans ((min_le_left _ _).trans hδ1)) (by omega)
      _ ≤ ρ / 2 := h1.le.trans (min_le_right _ _)
  have hbdd : BddAbove (norm ∘ φ '' (ball 0 r \ {0})) := by
    refine (hK.image continuous_norm).bddAbove.mono ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨φ s, hφK s hs, rfl⟩
  have hF := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hr0) (hφd.mono hrδ) hbdd
  set ℓ := limUnder (𝓝[≠] (0 : ℂ)) φ with hℓdef
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ∈ ball (0 : ℂ) r \ {0} := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds 0 hr0)] with s h1 h2
    exact ⟨h2, h1⟩
  have hlim : Tendsto φ (𝓝[≠] 0) (𝓝 ℓ) := by
    have hc := (hF.continuousOn.continuousAt (ball_mem_nhds 0 hr0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    rw [Function.update_self] at hc
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact Function.update_of_ne hs _ _
  have hℓK : ℓ ∈ {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} :=
    hK.isClosed.mem_of_tendsto hlim (hev.mono hφK)
  have hpℓ : p ℓ = p w := by
    have h1 : Tendsto (fun s => p (φ s)) (𝓝[≠] 0) (𝓝 (p ℓ)) := (p.continuous.tendsto ℓ).comp hlim
    have h2 : Tendsto (fun s : ℂ => p w + s ^ k) (𝓝[≠] 0) (𝓝 (p w)) := by
      have : Tendsto (fun s : ℂ => p w + s ^ k) (𝓝 0) (𝓝 (p w + 0 ^ k)) :=
        (continuous_const.add (continuous_pow k)).tendsto 0
      rw [zero_pow (by omega), add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (h1.congr' ?_) h2
    filter_upwards [hev] with s hs
    exact (hφY s (hrδ hs)).2
  have hℓ : ℓ = w := huniq ℓ hℓK.1 hpℓ
  refine ⟨r, hr0, Function.update φ 0 w, ?_, ?_, Function.update_self _ _ _, ?_⟩
  · rw [← hℓ]
    exact hF
  · have hoff : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → Function.update φ 0 w s ≠ w := by
      intro s hs h0 heq
      rw [Function.update_of_ne h0] at heq
      have := (hφY s (hrδ ⟨hs, h0⟩)).2
      rw [heq] at this
      exact pow_ne_zero k h0 (by linear_combination -this)
    intro s hs s' hs' hss'
    by_cases h0 : s = 0 <;> by_cases h0' : s' = 0
    · rw [h0, h0']
    · subst h0
      rw [Function.update_self] at hss'
      exact absurd hss'.symm (hoff s' hs' h0')
    · subst h0'
      rw [Function.update_self] at hss'
      exact absurd hss' (hoff s hs h0)
    · rw [Function.update_of_ne h0, Function.update_of_ne h0'] at hss'
      exact hφi (hrδ ⟨hs, h0⟩) (hrδ ⟨hs', h0'⟩) hss'
  · intro s hs
    by_cases h0 : s = 0
    · subst h0
      rw [Function.update_self]
      exact hwY
    · rw [Function.update_of_ne h0]
      exact (hφY s (hrδ ⟨hs, h0⟩)).1

theorem CentredDiscCoverCurve.proof (hPCC : PuncturedCoverCycles.Statement) :
    CentredDiscCoverCurve.Statement := by
  intro σ _ Y w p ρ N hY
  obtain ⟨δ, k, φ, hδ, hδ1, hk, hφd, hφi, hφY⟩ := centredDiscCover_punctured_branch hPCC hY
  exact centredDiscCover_extend_across_centre hY hδ hδ1 hk hφd hφi hφY

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LogIntegrable : GroundTheory.Heights₂.Heights.LogIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.LogIntegrable.proof GroundTheory.Heights₂.Heights.SheetSumMeasurable.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompare GroundTheory.Heights₂.Heights.VarSlabMeasure.full GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite

theorem GroundTheory.Heights₂.Heights.AutoClose.VarIntAdd : GroundTheory.Heights₂.Heights.VarIntAdd.Statement :=
  @GroundTheory.Heights₂.Heights.VarIntAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.BranchGermDimOne : GroundTheory.Heights₂.Heights.BranchGermDimOne.Statement :=
  @GroundTheory.Heights₂.Heights.BranchGermDimOne.proof GroundTheory.Heights₂.Heights.LocalDimComponentBound.proof GroundTheory.Heights₂.Heights.ZeroDimIsolated.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full

theorem GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound : GroundTheory.Heights₂.Heights.DominantFibreBound.Statement :=
  @GroundTheory.Heights₂.Heights.DominantFibreBound.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full

theorem GroundTheory.Heights₂.Heights.AutoClose.branchFillDimension_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.centredDiscCoverCurve_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.full

theorem GroundTheory.Heights₂.Heights.AutoClose.PlaceOnComponent : GroundTheory.Heights₂.Heights.PlaceOnComponent.Statement :=
  @GroundTheory.Heights₂.Heights.PlaceOnComponent.proof GroundTheory.Heights₂.Heights.ReducedNormalisationPlace.proof GroundTheory.Heights₂.Heights.CurveMinimalPrimeQuotient.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem GroundTheory.Heights₂.Heights.AutoClose.LelongLimitOffZero : GroundTheory.Heights₂.Heights.LelongLimitOffZero.Statement :=
  @GroundTheory.Heights₂.Heights.LelongLimitOffZero.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.VarMassNearSmall : GroundTheory.Heights₂.Heights.VarMassNearSmall.Statement :=
  @GroundTheory.Heights₂.Heights.VarMassNearSmall.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact
