module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactorAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.SideE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.CosAct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtZero

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem ad_ext (F : Type) [Field F] [NumberField F] [Algebra F E] {g g' : AdelicGLn.AdelicGL E n}
    (h1 : T4.pI E n g = T4.pI E n g') (h2 : ∀ v : Pl F, T4.pE E n v g = T4.pE E n v g') : g = g' := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ (FiniteAdeleRing.ext E fun w => ?_))
  · exact congrArg (fun x : GL (Fin n) (InfiniteAdeleRing E) => x.val a b) h1
  · exact congrArg (fun x : GL (Fin n) (CompletionsOver E (AdeleBaseChange.below F w)) =>
      x.val a b ⟨w, AdeleBaseChange.liesOver_below w⟩) (h2 _)

private theorem pI_eq (g : AdelicGLn.AdelicGL E n) : T4.pI E n g = (AdelicGLn.prodEquiv E n g).1 :=
  Units.ext (Matrix.ext fun a b => (AdelicGLn.prodEquiv_apply_fst E n g a b).symm)

private theorem pE_ext {v : Pl F} {g : AdelicGLn.AdelicGL E n} (h : ∀ w : PlacesOver E v, finAt w.1 g = 1) :
    T4.pE E n v g = 1 := by
  refine Units.ext (Matrix.ext fun a b => funext fun w => ?_)
  have h1 : (g.val a b).2 w.1 = (1 : GL (Fin n) (w.1.adicCompletion E)).val a b := by
    rw [← h w, finAt_apply]
  refine h1.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> rfl

private theorem gal_cent (σ : E ≃ₐ[F] E) (s : {r : ℝ // 0 < r}) :
    mapGL n (galAd σ) (centralSection E n s) = centralSection E n s := by
  have hl : Module.finrank F E ≠ 0 := Module.finrank_pos.ne'
  have e : (⟨(s : ℝ) ^ ((Module.finrank F E : ℝ))⁻¹, Real.rpow_pos_of_pos s.2 _⟩ : {r : ℝ // 0 < r}) ^
      Module.finrank F E = s := by
    apply Subtype.ext
    rw [Positive.val_pow]
    exact Real.rpow_inv_natCast_pow s.2.le hl
  rw [← e, ← UpperTheory.centralSection_baseChange F E n]
  exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).2.2.2.2.1 _

private theorem gal_retract (σ : E ≃ₐ[F] E) (hn : 0 < n) {μ : Measure (G1 E n)} [μ.IsHaarMeasure] {θ : Twist μ}
    (hθ : IsGalTwist σ θ) (x : AdelicGLn.AdelicGL E n) :
    θ.e (retractOne x) = retractOne (mapGL n (galAd σ) x) := by
  have h1 : ((θ.e (retractOne x) : G1 E n) : AdelicGLn.AdelicGL E n) * centralSection E n (detModule E n x) =
      mapGL n (galAd σ) x := by
    rw [hθ, coe_retractOne, map_mul, map_inv, gal_cent, inv_mul_cancel_right]
  rw [← h1, retractOne_mul, retractOne_coe, retractOne_centralSection, mul_one]

private theorem gal_infEmb (σ : E ≃ₐ[F] E) (a : archGroup E n) :
    mapGL n (galAd σ) (infEmb E n a) =
      infEmb E n (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) := by
  obtain ⟨c1, c2, -⟩ := UpperTheory.adele_galois_action_baseChange_compat F E σ n
  refine ad_ext F ?_ fun v => ?_
  · rw [c1, pI_eq, pI_eq, prodEquiv_infEmb, prodEquiv_infEmb, ContinuousMulEquiv.symm_apply_apply]
  · rw [c2, pE_ext fun w => finAt_infEmb w.1 _, pE_ext fun w => finAt_infEmb w.1 _, map_one]

private theorem arch_shift {σ : E ≃ₐ[F] E} {m : ℕ} (D : InfD σ m) (k : archGroup E n) :
    ∃ k' : archGroup E n, (∀ i, compA D n i k' = compA D n (i + 1) k) ∧
      mapGL n (galAd σ) (infEmb E n k) = infEmb E n k' := by
  refine ⟨_, fun i => ?_, gal_infEmb σ k⟩
  have hsh := (UpperTheory.ConvolutionTheory.L1.glueBasic _ _ _ _ m D n).2.2.2.2.2.2.1
  have h : ∀ i x, compA D n i x = archEquiv F n (D.comp n i ((archEquiv E n).symm x)) := fun _ _ => rfl
  rw [h, h, ContinuousMulEquiv.symm_apply_apply, hsh]

private theorem comp_loc {σ : E ≃ₐ[F] E} {v : Pl F} (D : Split (incFin E v) (galFin σ v) 1)
    (w : Fin 2 ≃ PlacesOver E v)
    (hD : ∀ (b : CompletionsOver E v) i, completionMap v (w i).1 (D.e b i) = b (w i))
    (i j : Fin 2) (g : Gw n v) :
    D.comp n j (T4.pE E n v (finEmb E n (AdelicGLn.localEmbedding (w i).1 (mapGL n (completionMap v (w i).1) g)))) =
      if j = i then g else 1 := by
  refine Units.ext (Matrix.ext fun a b => (completionMap v (w j).1).injective ?_)
  refine (hD _ j).trans ?_
  change (finAt (w j).1 (finEmb E n (AdelicGLn.localEmbedding (w i).1 (mapGL n (completionMap v (w i).1) g)))).val a b = _
  split_ifs with h
  · subst h
    rw [(UpperTheory.ConvolutionTheory.Tf.locEmb E n (w j).1).2.1]
    rfl
  · rw [(UpperTheory.ConvolutionTheory.Tf.locEmb E n (w i).1).2.2.1 (w j).1 (fun h' => h (w.injective (Subtype.ext h')))]
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs <;> simp

private theorem pE_loc {v v' : Pl F} (h : v' ≠ v) (w : PlacesOver E v) (x : Gw n w.1) :
    T4.pE E n v' (finEmb E n (AdelicGLn.localEmbedding w.1 x)) = 1 := by
  refine pE_ext fun u => (UpperTheory.ConvolutionTheory.Tf.locEmb E n w.1).2.2.1 u.1 (fun h' => h ?_) x
  apply HeightOneSpectrum.ext
  rw [u.2.over, w.2.over, h']

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc :
    GalLoc := by
  intro F E _ _ _ _ _ _ _ _ σ h2 hσ n hn μ _ θ
  refine ⟨?_, fun hθ => ⟨fun g => ?_, fun D eF e he k => ?_, fun v hv => ?_⟩⟩
  · unfold IsGalTwist UpperTheory.ConvolutionTheory.K.IsGal
    rw [UpperTheory.ConvolutionTheory.K.galAdEq]
  · have hs : σ.toRingEquiv.trans σ.toRingEquiv = RingEquiv.refl E := by
      have h : σ ^ 2 = 1 := by
        rw [← h2, ← IsGalois.card_aut_eq_finrank F E]
        exact pow_card_eq_one'
      ext x
      exact congrArg (fun τ : E ≃ₐ[F] E => τ x) ((sq σ).symm.trans h)
    apply Subtype.ext
    rw [hθ, hθ, UpperTheory.ConvolutionTheory.K.galAdEq]
    refine Units.ext (Matrix.ext fun a b => ?_)
    obtain ⟨-, b1, b2⟩ := UpperTheory.ConvolutionTheory.K.adBasic E
    refine (b2 _ _ _).symm.trans ?_
    rw [hs, b1]
  · have hc := (UpperTheory.ConvolutionTheory.L1.positionOf F E σ 1 D).2 n
    have hk := (hc k).1 k.2
    obtain ⟨k', key, hk'⟩ := arch_shift D (k : archGroup E n)
    have hm : k' ∈ archCompact E n := (hc k').2 fun i => by rw [key i]; exact hk (i + 1)
    refine ⟨⟨k', hm⟩, ?_, ?_⟩
    · change θ.e (archP E n k) = archP E n k'
      rw [← retract_infEmb, ← retract_infEmb, gal_retract σ hn hθ, hk']
    · rw [he k (fun i => ⟨_, hk i⟩) fun _ => rfl, he ⟨k', hm⟩ (fun i => ⟨_, hk (i + 1)⟩) fun i => (key i).symm,
        Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
      rfl
  · obtain ⟨w₀⟩ : Nonempty (PlacesOver E v) := by
      obtain ⟨⟨P, hP, hl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
      exact ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hl⟩⟩
    obtain ⟨D, w, -, hD⟩ := UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ 1 h2 v w₀ hv
    refine ⟨w, fun i g => ?_⟩
    obtain ⟨c1, c2, -⟩ := UpperTheory.adele_galois_action_baseChange_compat F E σ n
    obtain ⟨-, g2, -, -, -, -, hsh, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic _ _ _ _ 1 D n
    change θ.e (retractOne (finEmb E n _)) = retractOne (finEmb E n _)
    rw [gal_retract σ hn hθ]
    congr 1
    refine ad_ext F ?_ fun v' => ?_
    · rw [c1, pI_eq, pI_eq, prodEquiv_finEmb, prodEquiv_finEmb, map_one]
    · rw [c2]
      by_cases h : v' = v
      · subst h
        rw [← g2 (mapGL n (galFin σ v') _), ← g2 (T4.pE E n v' (finEmb E n (AdelicGLn.localEmbedding (w (i + 1)).1 _)))]
        congr 1
        funext j
        rw [hsh, comp_loc D w hD, comp_loc D w hD]
        have : j + 1 = i ↔ j = i + 1 := by revert i j; decide
        simp only [this]
      · rw [pE_loc h, pE_loc h, map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.TensAmp
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.tensAmp :
    TensAmp := by
  intro K _ _ _ n hn μ _ 𝔞 φ hφ
  obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ 𝔞.ν
  have hUo := 𝔞.isOpen
  have hUc : IsCompact (𝔞.U : Set (FA K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hUo) 𝔞.le
  have hpos : 0 < m.real (𝔞.U : Set (FA K n)) :=
    ENNReal.toReal_pos (hUo.measure_pos m ⟨1, 𝔞.U.one_mem⟩).ne' hUc.measure_lt_top.ne
  have hne : ((m.real (𝔞.U : Set (FA K n)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  refine ⟨⟨m.real (𝔞.U : Set (FA K n)), hpos, fun Θ hΘ hfix x => ?_, ?_⟩, fun c => ?_⟩
  · rw [hC 𝔞.a₀ φ (fun g => Θ (x * g)) (hΘ.comp (continuous_const.mul continuous_id)), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    have h1 : ∀ h : FA K n, 𝔞.a₀ a * φ h * Θ (x * (archP K n a * MultiplicityOne.finProj K n h)) =
        (𝔞.U : Set (FA K n)).indicator (fun _ => 𝔞.a₀ a * Θ (x * archP K n a)) h := by
      intro h
      by_cases hh : h ∈ (𝔞.U : Set (FA K n))
      · rw [hφ, Set.indicator_of_mem hh, Set.indicator_of_mem hh, ← mul_assoc x, hfix h hh]
        simp
      · rw [hφ, Set.indicator_of_notMem hh, Set.indicator_of_notMem hh]
        simp
    simp only [h1]
    rw [integral_indicator_const _ hUo.measurableSet, Complex.real_smul]
  · obtain ⟨e, he, hO⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m 𝔞.U hUo hUc
    have h2 : φ = ((m.real (𝔞.U : Set (FA K n)) : ℝ) : ℂ) • e := by
      ext h
      rw [CompactlySupportedContinuousMap.smul_apply, he, hφ]
      by_cases hh : h ∈ (𝔞.U : Set (FA K n))
      · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh, smul_eq_mul, mul_inv_cancel₀ hne]
        rfl
      · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh, smul_zero]
    have h3 := UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ 𝔞.ν m hC 𝔞.a₀ φ
    have h4 := ((UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν m).2.2.1 ((m.real (𝔞.U : Set (FA K n)) : ℝ) : ℂ) 𝔞.a₀ e).2
    rw [← h2, hO] at h4
    rw [h4, ContinuousLinearMap.comp_smul] at h3
    exact h3
  · rw [← ((UpperTheory.ConvolutionTheory.Tf.tensApply K n hn 𝔞.a₀ φ).2.2.2.2 c).2]
    refine (UpperTheory.ConvolutionTheory.Tf.leftSm K n hn 𝔞.a₀ (c • φ)).1 𝔞.smooth ⟨𝔞.U, hUo, fun u hu h => ?_⟩
    rw [CompactlySupportedContinuousMap.smul_apply, CompactlySupportedContinuousMap.smul_apply, hφ, hφ]
    by_cases hh : h ∈ (𝔞.U : Set (FA K n))
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (show u * h ∈ (𝔞.U : Set (FA K n)) from 𝔞.U.mul_mem hu hh)]
      rfl
    · rw [Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (show u * h ∉ (𝔞.U : Set (FA K n)) from fun h' => hh ((𝔞.U.mul_mem_cancel_left hu).1 h'))]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.UiwAct
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem fix_of_avg {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (ν : Measure G)
    (e : G → ℂ) (u : G) (hu : MeasurePreserving (u * ·) ν ν) (he : ∀ᵐ k ∂ν, e (u * k) = e k) (w : H)
    (hw : ∫ k, e k • π k w ∂ν = w) : π u w = w := by
  by_cases hi : Integrable (fun k => e k • π k w) ν
  · have h1 := (π u).integral_comp_comm hi
    have h2 := hu.integral_comp (Homeomorph.mulLeft u).measurableEmbedding (fun k => e k • π k w)
    rw [hw] at h1 h2
    rw [← h1]
    refine Eq.trans (integral_congr_ae ?_) h2
    filter_upwards [he] with k hk
    rw [map_smul, hk, π.map_mul_apply]
  · rw [integral_undef hi] at hw
    rw [← hw, map_zero]

private theorem coset_bij {G L : Type*} [Group G] [Group L] (loc : L →* G) (p : G →* L) (h1 : ∀ x, p (loc x) = x)
    (hc : ∀ h, p h = 1 → ∀ x, loc x * h = h * loc x) (J : Subgroup L) (x : L) (U : Subgroup G)
    (hJU : ∀ j ∈ J, loc j ∈ U) (hUJ : ∀ u ∈ U, p u ∈ J) :
    Set.BijOn (fun c : L ⧸ J => (QuotientGroup.mk (loc c.out) : G ⧸ U)) {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}
      {c | ∃ k ∈ U, c = QuotientGroup.mk (k * loc x)} := by
  have key : ∀ y : L, (QuotientGroup.mk (loc (QuotientGroup.mk y : L ⧸ J).out) : G ⧸ U) = QuotientGroup.mk (loc y) := by
    intro y
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J y
    rw [hj, map_mul, QuotientGroup.mk_mul_of_mem _ (hJU _ j.2)]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨loc k, hJU k hk, by simp only [key, map_mul]⟩
  · intro a _ b _ hab
    have h := hUJ _ (QuotientGroup.eq.1 hab)
    rw [map_mul, map_inv, h1, h1] at h
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    exact QuotientGroup.eq.2 h
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨QuotientGroup.mk (p k * x), ⟨p k, hUJ k hk, rfl⟩, ?_⟩
    have hp : p (k * (loc (p k))⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have e1 : k * loc x = loc (p k * x) * (k * (loc (p k))⁻¹) := by
      rw [hc _ hp, map_mul]
      group
    simp only [key]
    rw [e1, QuotientGroup.mk_mul_of_mem _ (U.mul_mem hk (U.inv_mem (hJU _ (hUJ k hk))))]

private theorem hop_prj {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (Gw n w)) (x : Gw n w) (U : Subgroup (FA K n)) (hJ : CO J)
    (hJU : ∀ j ∈ J, AdelicGLn.localEmbedding w j ∈ U) (hUJ : ∀ u ∈ U, finAt w (finEmb K n u) ∈ J) :
    (∑ᶠ c ∈ {c : FA K n ⧸ U | ∃ k ∈ U, c = QuotientGroup.mk (k * AdelicGLn.localEmbedding w x)}, rhoF μ c.out) ∘L
      prj (fixF μ U) = Hop μ w J x ∘L prj (fixF μ U) := by
  obtain ⟨hfin, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hJ.2 hJ.1
  obtain ⟨-, hmemU, hPU, -, habs, hmul, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U
  obtain ⟨-, hmemJ, -, hPJ, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))
  obtain ⟨-, hl1, -, -, hl5⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  have hb := coset_bij (AdelicGLn.localEmbedding w)
    (MonoidHom.mk' (fun g : FA K n => finAt w (finEmb K n g)) fun a b => by rw [map_mul, finAt_mul]) hl1 hl5 J x U hJU hUJ
  have hfin' := hb.image_eq ▸ hfin.image _
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : prj (fixL μ w J) (prj (fixF μ U) v) = prj (fixF μ U) v := by
    refine hPJ _ ((hmemJ _).2 ?_)
    rintro _ ⟨j, hj, rfl⟩
    exact (hmemU _).1 (hPU v) _ (hJU j hj)
  rw [Hop, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hv]
  let ev : (LL μ →L[ℂ] LL μ) →+ LL μ := AddMonoidHom.mk' (fun T => T (prj (fixF μ U) v)) fun _ _ => rfl
  refine (ev.map_finsum_mem _ hfin').trans (Eq.trans ?_ (ev.map_finsum_mem _ hfin).symm)
  refine (finsum_mem_eq_of_bijOn _ hb fun c _ => ?_).symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (AdelicGLn.localEmbedding w c.out)
  change rhoF μ _ (prj (fixF μ U) v) = rhoF μ _ (prj (fixF μ U) v)
  rw [hu, hmul, ContinuousLinearMap.comp_apply, (hmemU _).1 (hPU v) u u.2]

private theorem level_facts {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (D : TypeDat K n) (U : Subgroup (FA K n)) (hD : D.Level U) (hle : U ≤ AdelicGLn.integralFiniteGL K n) :
    IsOpen (U : Set (FA K n)) ∧ IsCompact (U : Set (FA K n)) ∧ ∀ v, D.FixedByTypeProjector μ v → v ∈ fixF μ U := by
  have hpe : ∀ u ∈ AdelicGLn.integralFiniteGL K n, ((fin1 u : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n u := by
    intro u hu
    exact congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hu)))
  have hiff : ∀ u ∈ AdelicGLn.integralFiniteGL K n, fin1 u ∈ D.U ↔ u ∈ U := by
    intro u hu
    have h := hD.1 (fin1 u) (by rw [hpe u hu, prodEquiv_finEmb])
    rwa [hpe u hu, prodEquiv_finEmb] at h
  have ho : IsOpen (U : Set (FA K n)) := by
    obtain ⟨O, hO, hUO⟩ := D.isOpen
    have : (U : Set (FA K n)) = (AdelicGLn.integralFiniteGL K n : Set (FA K n)) ∩ finEmb K n ⁻¹' O := by
      ext u
      constructor
      · intro hu
        have h := ((hUO _).1 ((hiff u (hle hu)).2 hu)).1
        rw [hpe u (hle hu)] at h
        exact ⟨hle hu, h⟩
      · rintro ⟨hu, h⟩
        refine (hiff u hu).1 ((hUO _).2 ?_)
        rw [hpe u hu]
        exact ⟨h, finEmb_mem_maxCompact hu⟩
    rw [this]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).inter (hO.preimage continuous_finEmb)
  refine ⟨ho, (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (U.isClosed_of_isOpen ho) hle, fun v hv => ?_⟩
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U).2.1 v).2 fun u hu => ?_
  have hu' := (hiff u (hle hu)).2 hu
  refine fix_of_avg _ D.ν D.e (fin1 u) (D.inv _ hu') ?_ v hv
  filter_upwards [D.supp] with k hk
  exact hD.2.2 _ hu' (by rw [hpe u (hle hu), prodEquiv_finEmb]) k hk

private theorem comm_proj {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P T : H →L[ℂ] H) (F : Submodule ℂ H) (hP : IsOrthogonalProjectionTwoLines J J' P)
    (hJ : ∀ u, J u ∈ F) (hJ' : ∀ u, J' u ∈ F) (hT : Commute T (prj F))
    (hY : (T ∘L prj F) ∘L P = P ∘L (T ∘L prj F)) : T ∘L P = P ∘L T := by
  have h0 : ∀ a ∈ F, ∀ h, inner ℂ a (h - prj F h) = 0 := fun a ha h =>
    inner_eq_zero_symm.1 (Submodule.starProjection_inner_eq_zero h a (F.le_topologicalClosure ha))
  have h1 : P * prj F = P := by
    refine ContinuousLinearMap.ext fun h => ?_
    have := (hP.2.2 (h - prj F h)).2 ⟨fun u => h0 _ (hJ u) h, fun u => h0 _ (hJ' u) h⟩
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  have hQ : IsSelfAdjoint (prj F) := isSelfAdjoint_starProjection _
  have h2 : prj F * P = P := by
    have := congrArg star h1
    rwa [star_mul, hQ.star_eq, hP.1.star_eq] at this
  change (T * prj F) * P = P * (T * prj F) at hY
  change T * P = P * T
  rw [mul_assoc, h2, hT.eq, ← mul_assoc, h1] at hY
  exact hY

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.uiwAct :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
          [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)), Lev U → ∀ (D : TypeDat K (2 + 2)), D.Level (levOn S U) →
          ∀ (d d' : ℕ) (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d'), ∀ w ∈ S, U w = GLnLocal.iwahori (w.adicCompletion K) (2 + 2) → ∀ ν : Fin (2 + 2) → ℤ,
          (∃ s, Act A.J (Uiw μ w ν) s ∧
            HeckeAt A (levOn S U) (AdelicGLn.localEmbedding w (Cartan.diagPow (w.adicCompletion K) (2 + 2) ν)) (s 0 : Eu d →ₗ[ℂ] Eu d)) ∧
          ∀ P, IsOrthogonalProjectionTwoLines A.J A'.J P → Uiw μ w ν ∘L P = P ∘L Uiw μ w ν := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp S U hU D hD d d' A A' w hw hI ν
  have hmem : ∀ u, u ∈ levOn S U ↔ ∀ v, finAt v (finEmb K (2 + 2) u) ∈
      (if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion K) (2 + 2)) := fun u => Iff.rfl
  have hle : levOn S U ≤ AdelicGLn.integralFiniteGL K (2 + 2) := by
    intro u hu
    refine (AdelicGLn.mem_integralFiniteGL_iff_forall K (2 + 2)).2 fun v => ?_
    have h := (hmem u).1 hu v
    split_ifs at h
    · exact (hU v).2 h
    · exact h
  obtain ⟨-, hl1, hl2, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K (2 + 2) w
  have hJU : ∀ j ∈ U w, AdelicGLn.localEmbedding w j ∈ levOn S U := by
    intro j hj
    refine (hmem _).2 fun v => ?_
    by_cases hv : v = w
    · subst hv
      rw [hl1, if_pos hw]
      exact hj
    · rw [hl2 v hv]
      exact one_mem _
  have hUJ : ∀ u ∈ levOn S U, finAt w (finEmb K (2 + 2) u) ∈ U w := by
    intro u hu
    have h := (hmem u).1 hu w
    rwa [if_pos hw] at h
  obtain ⟨ho, hc, hfix⟩ := level_facts μ D _ hD hle
  have hT : Uiw μ w ν = Hop μ w (U w) (Cartan.diagPow (w.adicCompletion K) (2 + 2) ν) := by rw [hI]; rfl
  obtain ⟨⟨s, ⟨u, κ, hκ, hact, hs⟩, hsec⟩, hcomm⟩ := cosAct K μ μ₂ τ₁ τ₂ hp D d d' A A' _ hD hle _ _
    (hop_prj μ w (U w) (Cartan.diagPow (w.adicCompletion K) (2 + 2) ν) _ (hU w).1 hJU hUJ).symm
  have hA : ∀ x, A.J x ∈ fixF μ (levOn S U) := fun x => hfix _ (ctZero K μ μ₂ τ₁ τ₂ hp D d d' A A' x).2.1
  have hA' : ∀ x, A'.J x ∈ fixF μ (levOn S U) := fun x =>
    hfix _ (ctZero K μ μ₂ τ₂ τ₁ ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩ D d' d A' A x).2.1
  rw [hT]
  refine ⟨⟨s, ⟨u, κ, hκ, fun x => ?_, hs⟩, fun v => funext fun x => hsec 0 v x⟩, fun P hP => ?_⟩
  · rw [← hact x, ContinuousLinearMap.comp_apply, (UpperTheory.ConvolutionTheory.Tf.commPrj K (2 + 2) μ _).2.2.2.1 _ (hA x)]
  · refine comm_proj A.J A'.J P _ _ hP hA hA' ?_ (hcomm P hP)
    refine (UpperTheory.ConvolutionTheory.Tf.hopLevel K (2 + 2) μ Measure.haar w (U w) _ _ (hU w).1.2 (hU w).1.1 ho hc ?_ hUJ).1
    rintro _ ⟨j, hj, rfl⟩
    exact hJU j hj
end
