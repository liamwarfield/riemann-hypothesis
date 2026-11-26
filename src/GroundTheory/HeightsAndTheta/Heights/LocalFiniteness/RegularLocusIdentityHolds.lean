module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveGermComponents
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveGermComponents.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet I ∩ N, ∃ W ∈ I.minimalPrimes,
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1 ∧ q ∈ zeroSet W ∧ x ∈ zeroSet W

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalizeQuotientStages
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem isPrime_map_quotient_localization {R : Type*} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    (hWm : W ≤ m) (hIW : I ≤ W) :
    (W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m)))).IsPrime := by
  rw [← Ideal.map_map]
  have hd : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) W ‹_› hd
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact Ideal.map_mono hIW)

def LocalizeQuotientStages.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime], W ≤ m → I ≤ W →
    ∀ (P : Ideal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))) [P.IsPrime],
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) = P →
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) =
        Module.length (Localization.AtPrime W)
          (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W)))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUniformiserBranchSimpleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem UniformiserBranchSimpleZero.proof (hloc : UniformiserLocallyInjective.Statement)
    (hder : InjectiveHolomorphicDerivNeZero.Statement) : UniformiserBranchSimpleZero.Statement := by
  intro σ _ I w t r φ hI hic hdim ht hr hdiff hinj hmaps hw0
  have hball : ∀ {ρ : ℝ} {τ : ℂ}, τ ∈ Metric.ball (0 : ℂ) ρ →
      (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) ρ := by
    intro ρ τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hwZ : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I := hw0 ▸ hmaps (Metric.mem_ball_self hr)
  have htw : eval w t = 0 := by
    by_contra h
    exact ht.not_isUnit (isUnit_algebraMap_pointLocalRing I w t h)
  obtain ⟨U, hU, hUinj⟩ := hloc σ I w t hI hic hdim hwZ ht
  have hφc : ContinuousAt φ 0 :=
    (hdiff.differentiableAt (Metric.ball_mem_nhds 0 hr)).continuousAt
  have hc1 : Continuous fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ) := continuous_pi fun _ ↦ continuous_id
  have hcont : ContinuousAt (fun τ : ℂ ↦ φ fun _ ↦ τ) 0 :=
    ContinuousAt.comp_of_eq (g := φ) (f := fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) hφc hc1.continuousAt rfl
  have hpre : (fun τ : ℂ ↦ φ fun _ ↦ τ) ⁻¹' U ∈ 𝓝 (0 : ℂ) :=
    hcont.preimage_mem_nhds (by rw [← hw0] at hU; exact hU)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hpre (Metric.ball_mem_nhds 0 hr))
  have hfd : DifferentiableOn ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) (Metric.ball 0 ε) :=
    (differentiable_eval_pointLocal t).comp_differentiableOn (hdiff.comp
      (differentiable_pi.2 fun _ ↦ differentiable_id).differentiableOn fun τ hτ ↦ hball (hεU hτ).2)
  have hfi : Set.InjOn (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) (Metric.ball 0 ε) := by
    intro a ha b hb hab
    have hab' := hUinj ⟨hmaps (hball (hεU ha).2), (hεU ha).1⟩ ⟨hmaps (hball (hεU hb).2), (hεU hb).1⟩ hab
    exact congrFun (hinj (hball (hεU ha).2) (hball (hεU hb).2) hab') 0
  have hd := hder _ _ Metric.isOpen_ball hfd hfi 0 (Metric.mem_ball_self hε)
  have hf0 : (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 = 0 := by
    change eval (φ 0) t = 0
    rw [hw0, htw]
  exact (analyticAt_eval_disc hr hdiff t).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf0 hd

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveGermComponents
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

namespace CurveGermComponents

variable {n : ℕ}

theorem mem_zeroSet_iff_le_ker (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    x ∈ zeroSet J ↔ J ≤ RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ) := by
  simp only [zeroSet, Set.mem_ofPred_eq, SetLike.le_def, RingHom.mem_ker]

theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have h : zeroSet J = ⋂ f ∈ J, {x : Fin n → ℂ | eval x f = 0} := by
    ext x
    simp [zeroSet]
  rw [h]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

theorem exists_minimalPrime_mem_zeroSet {I : Ideal (MvPolynomial (Fin n) ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ zeroSet I) : ∃ W ∈ I.minimalPrimes, x ∈ zeroSet W := by
  rw [mem_zeroSet_iff_le_ker] at hx
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le hx
  exact ⟨W, hW, (mem_zeroSet_iff_le_ker W x).2 hle⟩

theorem ringKrullDim_curveLocalRing_le_zero {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hm : RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) ∈ I.minimalPrimes) :
    ringKrullDim (curveLocalRing I q) ≤ 0 := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef
  let L := Localization.AtPrime m
  let J : Ideal L := I.map (algebraMap (MvPolynomial (Fin n) ℂ) L)
  change ringKrullDim (L ⧸ J) ≤ 0
  have hK : Ring.KrullDimLE 0 (L ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro p hp
    set Q := p.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hP : (Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime := Ideal.comap_isPrime _ _
    have hIP : I ≤ Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) := by
      rw [← Ideal.map_le_iff_le_comap]
      intro y hy
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hy]
      exact p.zero_mem
    have hPm : Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ m := by
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)).trans
        (Localization.AtPrime.under_maximalIdeal (I := m)).le
    have hPeq : Q.under (MvPolynomial (Fin n) ℂ) = m := le_antisymm hPm (hm.2 ⟨hP, hIP⟩ hPm)
    have hQmax : Q = IsLocalRing.maximalIdeal L := Localization.AtPrime.eq_maximalIdeal_iff_under_eq.1 hPeq
    have hQm : Q.IsMaximal := hQmax ▸ IsLocalRing.maximalIdeal.isMaximal L
    have h := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hQm
    rw [hQdef, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
    exact h.resolve_left hp.ne_top
  exact_mod_cast Ring.krullDimLE_iff.1 hK

theorem ringKrullDim_localRingAt_eq_one {I W : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hW : W ∈ I.minimalPrimes) (hq : q ∈ zeroSet W) (hdim : ringKrullDim (curveLocalRing I q) = 1) :
    ringKrullDim (localRingAt W q) = 1 := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef
  have hWm : W ≤ m := (mem_zeroSet_iff_le_ker W q).1 hq
  have hWp : W.IsPrime := hW.1.1
  let L := Localization.AtPrime m
  have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ W.map (algebraMap (MvPolynomial (Fin n) ℂ) L) :=
    Ideal.map_mono hW.1.2
  have hup : ringKrullDim (localRingAt W q) ≤ 1 := by
    rw [← hdim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have disj : Disjoint (m.primeCompl : Set (MvPolynomial (Fin n) ℂ)) W := by
    rw [Set.disjoint_left]
    intro a ha haW
    exact ha (hWm haW)
  have hWL : (W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl L W hWp disj
  have hne : ¬ ringKrullDim (localRingAt W q) ≤ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (localRingAt W q) := Ring.krullDimLE_iff.2 (by exact_mod_cast h0)
    have : IsDomain (localRingAt W q) := Ideal.Quotient.isDomain _
    have hf : IsField (localRingAt W q) := Ring.KrullDimLE.isField_of_isDomain (R := localRingAt W q)
    have hmax : (W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ hf
    have hWeq : W = m := by
      have h1 := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl L hWp disj
      rw [IsLocalRing.eq_maximalIdeal hmax, Localization.AtPrime.under_maximalIdeal] at h1
      exact h1.symm
    rw [hWeq] at hW
    have h2 := ringKrullDim_curveLocalRing_le_zero hW
    rw [hdim] at h2
    exact absurd h2 (by decide)
  exact le_antisymm hup (Order.succ_le_of_lt (lt_of_not_ge hne))

theorem exists_ringKrullDim_quotient_eq_nat (W : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime] :
    ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (e : ℕ) := by
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
  have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : ℕ) :=
    (ringKrullDim_quotient_le W).trans (by simp)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d at h0 h1 ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at h0
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, WithBot.coe_le_coe] at h1
      exact absurd h1 (not_le.2 (ENat.natCast_lt_top n))
    | coe e => exact ⟨e, rfl⟩

theorem proof : CurveGermComponents.Statement := by
  intro n I q hdim
  classical
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  refine ⟨⋂ W ∈ {W ∈ I.minimalPrimes | q ∉ zeroSet W}, (zeroSet W)ᶜ, ?_, ?_⟩
  · exact (Filter.biInter_mem (hfin.subset (Set.sep_subset _ _))).2 fun W hW =>
      (isClosed_zeroSet W).isOpen_compl.mem_nhds hW.2
  · rintro x ⟨hxI, hxN⟩
    obtain ⟨W, hW, hxW⟩ := exists_minimalPrime_mem_zeroSet hxI
    have hqW : q ∈ zeroSet W := by
      by_contra hq
      exact Set.mem_iInter₂.1 hxN W ⟨hW, hq⟩ hxW
    refine ⟨W, hW, ?_, hqW, hxW⟩
    have hWp : W.IsPrime := hW.1.1
    obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_nat W
    have h1 := LocalDimDomain.proof n e W hWp he q hqW
    rw [ringKrullDim_localRingAt_eq_one hW hqW hdim] at h1
    rw [he]
    exact_mod_cast h1.symm

end CurveGermComponents

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthTransverseSlice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

theorem length_slice_of_isCohenMacaulay (hCM : CMLengthParameters.Statement.{0})
    (hLS : LocalizeQuotientStages.Statement.{0}) {R : Type} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    [IsCohenMacaulayLocalRing (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))]
    (hW : W ∈ I.minimalPrimes) (hWm : W ≤ m) (huniq : ∀ W' ∈ I.minimalPrimes, W' ≤ m → W' = W)
    (d : ℕ) (lin : Fin d → R) (hlin : ∀ i, lin i ∈ m)
    (hdim : ringKrullDim (Localization.AtPrime m ⧸ W.map (algebraMap R (Localization.AtPrime m))) = (d : ℕ))
    (hT : ∀ g ∈ m, ∃ s ∉ m, s * g ∈ W ⊔ Ideal.span (Set.range lin)) :
    Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W))) =
      Module.length (Localization.AtPrime m)
        (Localization.AtPrime m ⧸ (I ⊔ Ideal.span (Set.range lin)).map (algebraMap R (Localization.AtPrime m))) := by
  classical
  have hIW : I ≤ W := hW.1.2
  have hP := isPrime_map_quotient_localization m W I hWm hIW

  have hunit : ∀ s ∉ m, IsUnit (((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) s) := fun s hs =>
    ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime m) m s).2 hs).map
      (Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m))))

  have hall : ∀ Q : Ideal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))), Q.IsPrime →
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) ≤ Q := by
    intro Q hQ
    have hIQ : I ≤ Q.comap ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) := fun f hf => by
      rw [Ideal.mem_comap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hf)]
      exact Q.zero_mem
    have hQm : Q.comap ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) ≤ m := fun f hf => by
      by_contra h
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hf (hunit f h))
    obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le hIQ
    have : W' = W := huniq W' hW' (hW'Q.trans hQm)
    subst this
    exact Ideal.map_le_iff_le_comap.2 hW'Q
  have hmin : minimalPrimes (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) =
      {W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m)))} := by
    ext Q
    rw [Set.mem_singleton_iff]
    constructor
    · intro hQ
      exact le_antisymm (hQ.2 ⟨hP, bot_le⟩ (hall Q hQ.1.1)) (hall Q hQ.1.1)
    · rintro rfl
      exact ⟨⟨hP, bot_le⟩, fun Q hQ _ => hall Q hQ.1⟩

  have hPdef : W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) =
      (W.map (algebraMap R (Localization.AtPrime m))).map (Ideal.Quotient.mk _) := by
    rw [Ideal.map_map]
  have hdimP : ringKrullDim ((Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) ⧸
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m)))) = (d : ℕ) := by
    rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hPdef).trans
      (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hIW)))]
    exact hdim

  have hmB : m.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) =
      maximalIdeal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) := by
    rw [← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    exact map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (Set.range fun i => ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) (lin i)) =
      (Ideal.span (Set.range lin)).map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have hmax : Ideal.span (Set.range fun i => ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) (lin i)) ⊔
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) =
      maximalIdeal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) := by
    rw [hspan, ← Ideal.map_sup, sup_comm, ← hmB]
    apply le_antisymm
    · refine Ideal.map_mono (sup_le hWm ?_)
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hlin i
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      obtain ⟨s, hs, hsg⟩ := hT g hg
      rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ (hunit s hs), ← map_mul]
      exact Ideal.mem_map_of_mem _ hsg
  have key := hCM _ _ d _ hmin hdimP hmax
  rw [hLS R m W I hWm hIW _ rfl] at key
  rw [← key, ← Module.length_eq_of_surjective (S := Localization.AtPrime m)
    (R := Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) Ideal.Quotient.mk_surjective,
    hspan, ← Ideal.map_map, Ideal.map_sup]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ (Localization.AtPrime m) _ _).toLinearEquiv.length_eq

theorem LengthTransverseSlice.proof (hCM : CMLengthParameters.Statement.{0})
    (hLS : LocalizeQuotientStages.Statement.{0}) : LengthTransverseSlice.Statement := by
  intro n d I W q L hW hdim hq huniq hCMq hT
  have hWp : W.IsPrime := hW.1.1
  have hWm : W ≤ RingHom.ker (eval q) := fun f hf => RingHom.mem_ker.2 (hq f hf)
  have : IsCohenMacaulayLocalRing (localRingAt I q) := hCMq
  have h := length_slice_of_isCohenMacaulay hCM hLS (RingHom.ker (eval q)) W I hW hWm
    (fun W' hW' hle => huniq W' hW' fun f hf => RingHom.mem_ker.1 (hle hf)) d
    (fun i => linPoly L i - C ((L *ᵥ q) i))
    (fun i => by rw [RingHom.mem_ker, map_sub, eval_linPoly, eval_C, sub_self])
    (LocalDimDomain.proof n d W hWp hdim q hq)
    (fun g hg => by
      obtain ⟨s, hs, hsg⟩ := hT g (RingHom.mem_ker.1 hg)
      exact ⟨s, fun h => hs (RingHom.mem_ker.1 h), hsg⟩)
  unfold localMult
  rw [dite_eq_left hWp, dite_eq_left (inferInstance : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime), h]
  rfl

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveRegularOffCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveRegularOffCentre.proof (hG : CurveGermComponents.Statement) (hR : CurveRegularOffFinite.Statement)
    (hF : CurveProperClosedFinite.Statement) : CurveRegularOffCentre.Statement := by
  classical
  intro n I q hdim
  obtain ⟨N, hN, hcomp⟩ := hG n I q hdim
  have hZc : ∀ J : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet J) := fun J ↦ by
    have : zeroSet J = ⋂ p ∈ J, {x : Fin n → ℂ | eval x p = 0} := by ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun p _ ↦ isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
  have hM : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  set S := {W | W ∈ I.minimalPrimes ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1}
  have hS : S.Finite := hM.subset fun W hW ↦ hW.1
  choose! F hFfin hFchart using fun W (hW : W ∈ S) ↦ hR n W hW.1.1.1 hW.2
  have hnle : ∀ W ∈ S, ∀ W' ∈ I.minimalPrimes \ {W}, ¬ W' ≤ W := fun W hW W' hW' hle ↦
    hW'.2 (le_antisymm hle (hW.1.2 hW'.1.1 hle))
  set Bad := (⋃ W ∈ S, F W) ∪ ⋃ W ∈ S, ⋃ W' ∈ I.minimalPrimes \ {W}, zeroSet W ∩ zeroSet W'
  have hBad : Bad.Finite := (hS.biUnion hFfin).union (hS.biUnion fun W hW ↦
    hM.sdiff.biUnion fun W' hW' ↦ hF n W W' hW.1.1.1 hW.2 (hnle W hW W' hW'))
  have hN'o : IsOpen (interior N \ (Bad \ {q})) := isOpen_interior.sdiff hBad.sdiff.isClosed
  refine ⟨_, hN'o.mem_nhds ⟨mem_interior_iff_mem_nhds.2 hN, fun h ↦ h.2 rfl⟩, ?_⟩
  rintro x ⟨hxI, hxN, hxB⟩ hxq
  have hxBad : x ∉ Bad := fun h ↦ hxB ⟨h, hxq⟩
  obtain ⟨W, hWm, hWd, -, hxW⟩ := hcomp x ⟨hxI, interior_subset hxN⟩
  have hWS : W ∈ S := ⟨hWm, hWd⟩
  obtain ⟨A, O, V, g, hO, hV, hxV, hg, hAg, hWV⟩ :=
    hFchart W hWS x hxW fun h ↦ hxBad (Or.inl (Set.mem_biUnion hWS h))
  set V' := V ∩ interior N ∩ ⋂ W' ∈ I.minimalPrimes \ {W}, (zeroSet W')ᶜ
  have hV' : IsOpen V' := (hV.inter isOpen_interior).inter
    (hM.sdiff.isOpen_biInter fun W' _ ↦ (hZc W').isOpen_compl)
  have hIV' : zeroSet I ∩ V' = zeroSet W ∩ V' := by
    ext z
    refine ⟨fun ⟨hzI, hzV⟩ ↦ ⟨?_, hzV⟩, fun ⟨hzW, hzV⟩ ↦ ⟨fun p hp ↦ hzW p (hWm.1.2 hp), hzV⟩⟩
    obtain ⟨W'', hW''m, -, -, hzW''⟩ := hcomp z ⟨hzI, interior_subset hzV.1.2⟩
    by_cases h : W'' = W
    · exact h ▸ hzW''
    · exact absurd hzW'' (Set.mem_iInter₂.1 hzV.2 W'' ⟨hW''m, h⟩)
  refine ⟨A, O ∩ g ⁻¹' V', V', g, hg.continuousOn.isOpen_inter_preimage hO hV', hV',
    ⟨⟨hxV, hxN⟩, Set.mem_iInter₂.2 fun W' hW' hxW' ↦ hxBad (Or.inr (Set.mem_biUnion hWS
      (Set.mem_biUnion hW' ⟨hxW, hxW'⟩)))⟩, hg.mono Set.inter_subset_left,
    fun y hy ↦ hAg y hy.1, ?_⟩
  rw [hIV', Set.image_inter_preimage, ← hWV]
  ext z
  exact ⟨fun ⟨hzW, hzV⟩ ↦ ⟨⟨hzW, hzV.1.1⟩, hzV⟩, fun ⟨⟨hzW, _⟩, hzV⟩ ↦ ⟨hzW, hzV⟩⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMHeightOneGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem isCohenMacaulayLocalRing_of_minimalPrimes_sup_span {R : Type*} [CommRing R] [IsNoetherianRing R]
    {J W : Ideal R} {g : R} [J.IsPrime] [W.IsPrime] (hg : g ∉ J)
    (hW : W ∈ (J ⊔ Ideal.span {g}).minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hgW : g ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ W := by rwa [Ideal.mk_ker]
  set W' : Ideal (R ⧸ J) := W.map (Ideal.Quotient.mk J) with hW'
  have : W'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : W'.comap (Ideal.Quotient.mk J) = W := by
    rw [hW', Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker]
  have hmem : ∀ a : R, Ideal.Quotient.mk J a ∈ W' ↔ a ∈ W := fun a => by
    rw [← Ideal.mem_comap, hcomap]
  have hsub : W.primeCompl.map (Ideal.Quotient.mk J) = W'.primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · intro hx
      obtain ⟨b, hb, hba⟩ := Submonoid.mem_map.mp hx
      change Ideal.Quotient.mk J a ∉ W'
      rw [← hba, hmem]
      exact hb
    · intro ha
      exact Submonoid.mem_map.mpr ⟨a, fun h => ha ((hmem a).mpr h), rfl⟩
  have hloc : IsLocalization.AtPrime (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      W' := by
    have h := Vertical.SpecChart.isLocalization_quot W J
    rw [hsub] at h
    exact h
  have : IsLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.AtPrime.isLocalRing _ W'
  have : IsDomain (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors W')
  set x := algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
    (Ideal.Quotient.mk J g) with hx
  have hg0 : Ideal.Quotient.mk J g ≠ 0 := fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hx0 : x ≠ 0 := by
    intro h
    apply hg0
    have h0 : x = algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) 0 := by
      rw [map_zero]
      exact h
    exact IsLocalization.injective (S := Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors W') h0
  have hxm : x ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W']
    exact Ideal.mem_map_of_mem _ ((hmem g).mpr hgW)
  have hheight : W'.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hW) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h
    apply hg0
    rw [← Ideal.mem_bot, ← h]
    exact (hmem g).mpr hgW
  refine { exists_isWeaklyRegular := ⟨[x], ?_, ?_, ?_⟩ }
  · intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hxm
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    intro a b hab
    simp only [smul_eq_mul] at hab
    exact mul_left_cancel₀ hx0 hab
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height W', hheight]
    simp

theorem CMHeightOneGeneral.proof (hopen : CMLocusOpen.Statement) : CMHeightOneGeneral.Statement := by
  intro n J W g hJ hg hW
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  obtain ⟨f, hfW, hf⟩ := hopen n J W hJW (isCohenMacaulayLocalRing_of_minimalPrimes_sup_span hg hW)
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := fun p hp =>
    RingHom.mem_ker.mpr (hq p hp)
  exact hf _ (hJW.trans hWq) (fun h => hfq (RingHom.mem_ker.mp h))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMGeneralPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets IsLocalRing

theorem isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes {n : ℕ}
    {I W : Ideal (MvPolynomial (Fin n) ℂ)} [W.IsPrime] (hW : W ∈ I.minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime W))) := by
  set S := Localization.AtPrime W
  set J := I.map (algebraMap (MvPolynomial (Fin n) ℂ) S)
  have hJm : J ≤ maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hW.1.2
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hdim : Ring.KrullDimLE 0 (S ⧸ J) := by
    rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
    intro K hK
    have : K.IsPrime := hK.1.1
    have hKm : K ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal hK.1.1.ne_top
    have hI : I ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      Ideal.map_le_iff_le_comap.mp hK.1.2
    have hKW : K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) ≤ W := by
      have h := Ideal.comap_mono (f := algebraMap (MvPolynomial (Fin n) ℂ) S) hKm
      rwa [show (maximalIdeal S).comap (algebraMap (MvPolynomial (Fin n) ℂ) S) = W from
        Localization.AtPrime.under_maximalIdeal] at h
    have hWK : W ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      hW.2 ⟨Ideal.IsPrime.comap _, hI⟩ hKW
    have hmK : maximalIdeal S ≤ K := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_le_iff_le_comap.mpr hWK
    rw [le_antisymm hKm hmK]
    exact maximalIdeal.isMaximal S
  have h0 : ringKrullDim (S ⧸ J) = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdim
  exact
    { exists_isWeaklyRegular := ⟨[], by simp, RingTheory.Sequence.IsWeaklyRegular.nil _ _, by simpa using h0⟩ }

theorem CMGeneralPoint.proof (hOpen : CMLocusOpen.Statement) : CMGeneralPoint.Statement := by
  intro n I W hW
  have : W.IsPrime := hW.1.1
  obtain ⟨g, hgW, hg⟩ :=
    hOpen n I W hW.1.2 (isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes hW)
  have hfin : (I.minimalPrimes \ {W}).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset Set.sdiff_subset
  have hsel : ∀ W' ∈ I.minimalPrimes \ {W}, ∃ h, h ∈ W' ∧ h ∉ W := by
    rintro W' ⟨hW', hne⟩
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hc (hW.2 hW'.1 hc))
  choose! h hh using hsel
  refine ⟨g * ∏ W' ∈ hfin.toFinset, h W', ?_, ?_⟩
  · intro hmem
    rcases Ideal.IsPrime.mem_or_mem ‹W.IsPrime› hmem with h1 | h1
    · exact hgW h1
    · obtain ⟨W', hW', h2⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact (hh W' (hfin.mem_toFinset.mp hW')).2 h2
  · intro q hq hf
    rw [map_mul, map_prod] at hf
    have hg0 : eval q g ≠ 0 := left_ne_zero_of_mul hf
    have hp0 := right_ne_zero_of_mul hf
    refine ⟨fun W' hW' hqW' => ?_, ?_⟩
    · by_contra hne
      have hmem : W' ∈ I.minimalPrimes \ {W} := ⟨hW', hne⟩
      exact hp0 (Finset.prod_eq_zero (hfin.mem_toFinset.mpr hmem) (hqW' _ (hh W' hmem).1))
    · have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
        fun x hx => RingHom.mem_ker.mpr (hq x hx)
      exact hg _ (hW.1.2.trans hWq) fun hk => hg0 (RingHom.mem_ker.mp hk)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalizeQuotientStages
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem length_self_eq_of_ringEquiv {A C : Type*} [CommRing A] [CommRing C] (e : A ≃+* C) :
    Module.length A A = Module.length C C := by
  have : RingHomSurjective (e : A →+* C) := ⟨e.surjective⟩
  let f : A →ₛₗ[(e : A →+* C)] C :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun a b => by simp }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

theorem LocalizeQuotientStages.proof : LocalizeQuotientStages.Statement.{u} := by
  intro R _ m W I _ _ hWm hIW P _ hP
  let Q := R ⧸ I
  let B := Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))
  let T := Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W))

  have hdisj : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have hPR : P.comap (algebraMap R B) = W := by
    rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime m) B, ← Ideal.comap_comap,
      Ideal.Quotient.algebraMap_eq, ← hP,
      ← Ideal.map_map, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 (Ideal.map_mono hIW)]
    exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ ‹W.IsPrime› hdisj

  have hsub : (P.comap (algebraMap Q B)).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : Ideal.Quotient.mk I r ∈ (P.comap (algebraMap Q B)).primeCompl ↔ r ∉ W := by
      rw [← hPR]; exact Iff.rfl
    rw [h1]
    constructor
    · intro hr; exact ⟨r, hr, rfl⟩
    · rintro ⟨r', hr', he⟩ hr
      apply hr'
      have : r' - r ∈ I := Ideal.Quotient.eq.1 he
      simpa using W.add_mem (hIW this) hr
  have hBP : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl)
      (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid Q m.primeCompl) (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) T
  exact (length_self_eq_of_ringEquiv (A := Localization.AtPrime P) (C := T) e.toRingEquiv).trans
    (Module.length_eq_of_surjective (R := T) (S := Localization.AtPrime W) (M := T)
      Ideal.Quotient.mk_surjective).symm

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFibreRadicalAway
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RadicalAwayRabinowitsch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {R : Type*} [CommRing R] {ι : Type*}

def rabinowitschIdeal (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    Ideal (MvPolynomial (Option ι) R) :=
  K.map (rename (R := R) some).toRingHom ⊔ Ideal.span {X none * rename some g - 1}

theorem rabinowitschIdeal_map {R' : Type*} [CommRing R'] (φ : R →+* R')
    (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    (rabinowitschIdeal K g).map (MvPolynomial.map φ) =
      rabinowitschIdeal (K.map (MvPolynomial.map φ)) (MvPolynomial.map φ g) := by
  have h : (MvPolynomial.map φ).comp (rename (R := R) (some : ι → Option ι)).toRingHom =
      (rename (R := R') (some : ι → Option ι)).toRingHom.comp (MvPolynomial.map φ) :=
    RingHom.ext fun p => by simp [map_rename]
  simp only [rabinowitschIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map, Set.image_singleton,
    map_sub, map_mul, map_one, map_X, h]
  simp [map_rename]

theorem pow_sub_one_mem_span (g : MvPolynomial ι R) (k : ℕ) :
    (X none * rename some g) ^ k - 1 ∈
      (Ideal.span {X none * rename some g - 1} : Ideal (MvPolynomial (Option ι) R)) := by
  rw [Ideal.mem_span_singleton]
  simpa using sub_dvd_pow_sub_pow (X none * rename some g : MvPolynomial (Option ι) R) 1 k

def rabinowitschEval (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    MvPolynomial (Option ι) R →+* Localization.Away (Ideal.Quotient.mk K g) :=
  eval₂Hom ((algebraMap (MvPolynomial ι R ⧸ K) _).comp ((Ideal.Quotient.mk K).comp C))
    fun o => Option.elim o (IsLocalization.Away.invSelf (Ideal.Quotient.mk K g))
      fun i => algebraMap (MvPolynomial ι R ⧸ K) _ (Ideal.Quotient.mk K (X i))

theorem rabinowitschEval_rename (K : Ideal (MvPolynomial ι R)) (g p : MvPolynomial ι R) :
    rabinowitschEval K g (rename some p) =
      algebraMap (MvPolynomial ι R ⧸ K) _ (Ideal.Quotient.mk K p) := by
  have h : (rabinowitschEval K g).comp (rename (R := R) (some : ι → Option ι)).toRingHom =
      (algebraMap (MvPolynomial ι R ⧸ K) (Localization.Away (Ideal.Quotient.mk K g))).comp
        (Ideal.Quotient.mk K) :=
    MvPolynomial.ringHom_ext (fun r => by simp [rabinowitschEval]) (fun i => by simp [rabinowitschEval])
  exact congrArg (fun f => f p) h

theorem rabinowitschIdeal_le_ker (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    rabinowitschIdeal K g ≤ RingHom.ker (rabinowitschEval K g) := by
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    simp [RingHom.mem_ker, rabinowitschEval_rename, Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_one, rabinowitschEval_rename]
    rw [show rabinowitschEval K g (X none) = IsLocalization.Away.invSelf (Ideal.Quotient.mk K g) by
      simp [rabinowitschEval], mul_comm, IsLocalization.Away.mul_invSelf, sub_self]

theorem rename_mem_rabinowitschIdeal_iff (K : Ideal (MvPolynomial ι R)) (g f : MvPolynomial ι R) :
    rename some f ∈ rabinowitschIdeal K g ↔ ∃ k : ℕ, g ^ k * f ∈ K := by
  constructor
  · intro hf
    have h0 := rabinowitschIdeal_le_ker K g hf
    rw [RingHom.mem_ker, rabinowitschEval_rename,
      IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk K g))] at h0
    obtain ⟨⟨m, k, rfl⟩, hm⟩ := h0
    refine ⟨k, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simpa using hm
  · rintro ⟨k, hk⟩
    have e : (rename some f : MvPolynomial (Option ι) R) =
        X none ^ k * rename some (g ^ k * f) -
          rename some f * ((X none * rename some g) ^ k - 1) := by
      simp only [map_mul, map_pow]; ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left ?_))
      (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (pow_sub_one_mem_span g k)))
    exact Ideal.mem_map_of_mem _ hk

theorem exists_pow_mul_sub_rename_mem (g : MvPolynomial ι R) (h : MvPolynomial (Option ι) R) :
    ∃ (N : ℕ) (f : MvPolynomial ι R), rename some g ^ N * h - rename some f ∈
      (Ideal.span {X none * rename some g - 1} : Ideal (MvPolynomial (Option ι) R)) := by
  induction h using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp⟩
  | add p q hp hq =>
    obtain ⟨N₁, f₁, h₁⟩ := hp
    obtain ⟨N₂, f₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, g ^ N₂ * f₁ + g ^ N₁ * f₂, ?_⟩
    have e : rename some g ^ (N₁ + N₂) * (p + q) - rename some (g ^ N₂ * f₁ + g ^ N₁ * f₂) =
        rename some g ^ N₂ * (rename some g ^ N₁ * p - rename some f₁) +
          rename some g ^ N₁ * (rename some g ^ N₂ * q - rename some f₂) := by
      simp only [map_add (f := _), map_mul, map_pow]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
  | mul_X p j hp =>
    obtain ⟨N, f, hf⟩ := hp
    cases j with
    | none =>
      refine ⟨N + 1, f, ?_⟩
      have e : rename some g ^ (N + 1) * (p * X none) - rename some f =
          (rename some g ^ N * p - rename some f) +
            rename some g ^ N * p * (X none * rename some g - 1) := by ring
      rw [e]
      exact Ideal.add_mem _ hf (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    | some i =>
      refine ⟨N, f * X i, ?_⟩
      have e : rename some g ^ N * (p * X (some i)) - rename some (f * X i) =
          (rename some g ^ N * p - rename some f) * X (some i) := by
        simp only [map_mul, rename_X]; ring
      rw [e]
      exact Ideal.mul_mem_right _ _ hf

theorem isRadicalAway_iff_isRadical_rabinowitschIdeal (K : Ideal (MvPolynomial ι R))
    (g : MvPolynomial ι R) : IsRadicalAway K g ↔ (rabinowitschIdeal K g).IsRadical := by
  constructor
  · intro hK h ⟨m, hm⟩
    obtain ⟨N, f, hf⟩ := exists_pow_mul_sub_rename_mem g h
    have hf' : rename some g ^ N * h - rename some f ∈ rabinowitschIdeal K g := Ideal.mem_sup_right hf

    have hfm : rename some (f ^ m) ∈ rabinowitschIdeal K g := by
      have hd : (rename some g ^ N * h) ^ m - rename some f ^ m ∈ rabinowitschIdeal K g := by
        obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (rename some g ^ N * h) (rename some f) m
        rw [hc]
        exact Ideal.mul_mem_right _ _ hf'
      have hp : (rename some g ^ N * h) ^ m ∈ rabinowitschIdeal K g := by
        rw [mul_pow]
        exact Ideal.mul_mem_left _ _ hm
      rw [map_pow]
      simpa using Ideal.sub_mem _ hp hd
    obtain ⟨k, hk⟩ := (rename_mem_rabinowitschIdeal_iff K g _).1 hfm

    have hrad : g ^ k * f ∈ K.radical := by
      refine ⟨m + 1, ?_⟩
      have e : (g ^ k * f) ^ (m + 1) = (g ^ (k * m) * f) * (g ^ k * f ^ m) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hk
    obtain ⟨j, hj⟩ := hK _ hrad
    have hfK : rename some f ∈ rabinowitschIdeal K g :=
      (rename_mem_rabinowitschIdeal_iff K g f).2 ⟨j + k, by rw [pow_add, mul_assoc]; exact hj⟩
    have hgh : rename some g ^ N * h ∈ rabinowitschIdeal K g := by
      simpa using Ideal.add_mem _ hf' hfK
    have e : h = X none ^ N * (rename some g ^ N * h) -
        h * ((X none * rename some g) ^ N - 1) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hgh)
      (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (pow_sub_one_mem_span g N)))
  · intro hR f ⟨m, hm⟩
    have h1 : rename some f ∈ rabinowitschIdeal K g := by
      refine hR ⟨m, ?_⟩
      rw [← map_pow]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hm)
    exact (rename_mem_rabinowitschIdeal_iff K g f).1 h1

end

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem GenericFibreRadicalAway.proof (hR : GenericFibreRadical.Statement) :
    GenericFibreRadicalAway.Statement := by
  intro σ _ n K g hK
  obtain ⟨F, hF0, hF⟩ := hR σ (Option (Fin n)) (rabinowitschIdeal K g)
    ((isRadicalAway_iff_isRadical_rabinowitschIdeal K g).1 hK)
  refine ⟨F, hF0, fun t ht => ?_⟩
  have h := hF t ht
  rw [rabinowitschIdeal_map] at h
  exact (isRadicalAway_iff_isRadical_rabinowitschIdeal (fibreIdeal K t) _).2 h

end

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadicalAway : GroundTheory.Heights₂.Heights.GenericFibreRadicalAway.Statement :=
  @GroundTheory.Heights₂.Heights.GenericFibreRadicalAway.proof GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadical

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffCentre : GroundTheory.Heights₂.Heights.CurveRegularOffCentre.Statement :=
  @GroundTheory.Heights₂.Heights.CurveRegularOffCentre.proof GroundTheory.Heights₂.Heights.CurveGermComponents.proof GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffFinite GroundTheory.Heights₂.Heights.CurveProperClosedFinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LengthTransverseSlice : GroundTheory.Heights₂.Heights.LengthTransverseSlice.Statement :=
  @GroundTheory.Heights₂.Heights.LengthTransverseSlice.proof GroundTheory.Heights₂.Heights.AutoClose.CMLengthParameters GroundTheory.Heights₂.Heights.LocalizeQuotientStages.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CMGeneralPoint : GroundTheory.Heights₂.Heights.CMGeneralPoint.Statement :=
  @GroundTheory.Heights₂.Heights.CMGeneralPoint.proof GroundTheory.Heights₂.Heights.AutoClose.CMLocusOpen

theorem GroundTheory.Heights₂.Heights.AutoClose.UniformiserBranchSimpleZero : GroundTheory.Heights₂.Heights.UniformiserBranchSimpleZero.Statement :=
  @GroundTheory.Heights₂.Heights.UniformiserBranchSimpleZero.proof GroundTheory.Heights₂.Heights.AutoClose.UniformiserLocallyInjective GroundTheory.Heights₂.Heights.InjectiveHolomorphicDerivNeZero.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CMHeightOneGeneral : GroundTheory.Heights₂.Heights.CMHeightOneGeneral.Statement :=
  @GroundTheory.Heights₂.Heights.CMHeightOneGeneral.proof GroundTheory.Heights₂.Heights.AutoClose.CMLocusOpen

theorem GroundTheory.Heights₂.Heights.AutoClose.regular_locus_identity_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularLocusIdentity.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularLocusIdentity.proof GroundTheory.Heights₂.Heights.AutoClose.regular_off_hypersurface_holds
