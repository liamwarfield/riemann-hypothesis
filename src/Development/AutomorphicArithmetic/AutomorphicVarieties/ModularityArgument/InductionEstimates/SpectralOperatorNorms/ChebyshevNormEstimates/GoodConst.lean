module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FinAct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ConvBump

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.EllLin
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem memLp_out {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {v : L2 μ} {φ : G1 K n → ℂ} (hc : Continuous φ) (hr : Reps μ v φ) :
    MemLp (fun m : RightCosetSpace (Gam K n) => φ (Quotient.out m)) 2 (quotientMeasure (Gam K n) μ) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have hinv : ∀ γ ∈ Gam K n, ∀ y, φ (γ * y) = φ y := fun γ hγ => by
    have h1 : (fun y => φ (γ * y)) =ᵐ[μ] φ := by
      filter_upwards [hr, (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae hr] with y a b
      rw [← a, ← b]
      congr 1
      exact Quotient.sound ⟨⟨γ, hγ⟩, rfl⟩
    exact congrFun (((hc.comp (continuous_const_mul γ)).ae_eq_iff_eq μ hc).1 h1)
  let q : RightCosetSpace (Gam K n) → ℂ := Quotient.lift φ (fun a b hab => by
    obtain ⟨γ, rfl⟩ := hab
    exact hinv γ γ.2 b)
  have hq : Continuous q := (isOpenQuotientMap_mk (Gam K n)).isQuotientMap.continuous_iff.2 hc
  have h2 : (v : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ] q := by
    have hm : ∀ᵐ x ∂(Measure.map (mk (Gam K n)) (μ.restrict (fundamentalDomain (Gam K n)))),
        (v : RightCosetSpace (Gam K n) → ℂ) x = q x := by
      refine (ae_map_iff (measurable_mk (Gam K n)).aemeasurable
        (measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable hq.measurable)).2 ?_
      exact ae_restrict_of_ae (hr.mono fun y hy => by
        change v (mk (Gam K n) y) = φ y
        exact hy)
    rwa [map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K n) μ)] at hm
  have h3 : (fun m : RightCosetSpace (Gam K n) => φ (Quotient.out m)) = q := by
    funext m
    conv_rhs => rw [← Quotient.out_eq m]
    rfl
  rw [h3]
  exact (Lp.memLp v).ae_eq h2

private theorem int_pair {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (Pl E)} (b : BW.Blo S 2)
    {τ : Submodule ℂ (L2 (BW.mu1 E 2))} {m B} (hb : BloIn b τ m B) {v : L2 (BW.mu1 E 2)} {φ : G1 E 2 → ℂ} (hc : Continuous φ)
    (hr : Reps (BW.mu1 E 2) v φ) :
    Integrable (fun x : RightCosetSpace (Gam E 2) => φ (Quotient.out x) *
      starRingEnd ℂ (b.f.1 ((Quotient.out x : G1 E 2) : GlobalTheory.CuspRep.GA E 2))) (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := by
  obtain ⟨w, -, hw⟩ := hb.mem
  have hf : Continuous b.f.1 := ((BW.umgOps E 2).2 b.f (BW.cuspUmg E 2 b.f b.cusp).1).1
  exact (memLp_out hc hr).integrable_mul (memLp_out (hf.comp continuous_subtype_val) hw).star

private theorem zt_zero (K : Type) [Field K] [NumberField K] : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.zt K 0 = 1 := by
  have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext Real.exp_zero
  rw [UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.zt, this, map_one]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ellLin {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {μ : Measure (normOneGL (K := E) (n := (2 + 2)))}
    [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : _root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) (b b' : BW.Blo 𝔢.S 2) (hb : BloIn b 𝔵.τ₂ 𝔵.m₂ 𝔵.B₂)
    (hb' : BloIn b' 𝔵.τ₁ 𝔵.m₁ 𝔵.B₁) (k : G1 E (2 + 2)) :
    ∃ ℓ : Eu 𝔵.d' →L[ℂ] ℂ, ∀ v, ℓ v = ell b b' k (𝔵.A'.sec v) := by
  set Q := quotientMeasure (Gam E 2) (BW.mu1 E 2)
  let F : Eu 𝔵.d' → RightCosetSpace (Gam E 2) → RightCosetSpace (Gam E 2) → ℂ := fun v m₁ m₂ =>
    𝔵.A'.sec v (lv (Quotient.out m₁) (Quotient.out m₂) 0 * k) *
      starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)) *
      starRingEnd ℂ (b'.f.1 ((Quotient.out m₂ : G1 E 2) : GlobalTheory.CuspRep.GA E 2))
  have key : ∀ v, (∀ m₁, Integrable (F v m₁) Q) ∧ Integrable (fun m₁ => ∫ m₂, F v m₁ m₂ ∂Q) Q := fun v => by
    obtain ⟨d, φ, ψ, hφ, hψ, h⟩ := (((𝔵.A'.onto _).1 ⟨v, rfl⟩).1).levi k
    have e : ∀ m₁ m₂, F v m₁ m₂ = ∑ i, (φ i (Quotient.out m₁) *
        starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2))) * (ψ i (Quotient.out m₂) *
        starRingEnd ℂ (b'.f.1 ((Quotient.out m₂ : G1 E 2) : GlobalTheory.CuspRep.GA E 2))) := fun m₁ m₂ => by
      simp only [F]
      rw [h (Quotient.out m₁) (Quotient.out m₂) _ (by
        rw [Subgroup.coe_mul, blkLaws.1, neg_zero, zt_zero, mul_one, mul_one]), Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have i₁ := fun i => int_pair b hb (hφ i).1 (hφ i).2.choose_spec.2
    have i₂ := fun i => int_pair b' hb' (hψ i).1 (hψ i).2.choose_spec.2
    refine ⟨fun m₁ => ?_, ?_⟩
    · rw [funext (e m₁)]
      exact integrable_finsetSum _ fun i _ => (i₂ i).const_mul _
    · simp only [e]
      have : ∀ m₁ : RightCosetSpace (Gam E 2), _ := fun m₁ => integral_finsetSum (μ := Q) Finset.univ fun i _ =>
        (i₂ i).const_mul (φ i (Quotient.out m₁) * starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)))
      simp only [this, integral_const_mul]
      exact integrable_finsetSum _ fun i _ => (i₁ i).mul_const _
  let l : Eu 𝔵.d' →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ m₁, ∫ m₂, F v m₁ m₂ ∂Q ∂Q
      map_add' := fun v w => by
        rw [← integral_add (key v).2 (key w).2]
        refine integral_congr_ae (Eventually.of_forall fun m₁ => ?_)
        simp only
        rw [← integral_add ((key v).1 m₁) ((key w).1 m₁)]
        refine integral_congr_ae (Eventually.of_forall fun m₂ => ?_)
        simp only [F, map_add (f := _), Pi.add_apply]
        ring
      map_smul' := fun c v => by
        simp only [F, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, integral_const_mul c] }
  exact ⟨LinearMap.toContinuousLinearMap l, fun v => rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeEigenvalueRankTwoData
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FixOfLevel
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped InnerProductSpace Pointwise

private theorem fix_of_level {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (D : TypeDat K n) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (hD : D.Level U)
    (hU : U ≤ AdelicGLn.integralFiniteGL K n) (v : LL μ) (hv : D.FixedByTypeProjector μ v) : v ∈ fixF μ U := by
  rw [(UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U).2.1]
  intro u hu
  have key : ∀ u ∈ U, MultiplicityOne.finProj K n u ∈ D.U ∧ (AdelicGLn.prodEquiv K n (MultiplicityOne.finProj K n u : G1 K n)).1 = 1 := by
    intro u hu
    have h1 : ((MultiplicityOne.finProj K n u : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n u := by
      rw [MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact (hU hu)))]
    have h2 : AdelicGLn.prodEquiv K n (finEmb K n u) = (1, u) := (AdelicGLn.prodEquiv K n).apply_symm_apply _
    have h3 : (AdelicGLn.prodEquiv K n (MultiplicityOne.finProj K n u : G1 K n)).1 = 1 := by rw [h1, h2]
    refine ⟨(hD.1 _ h3).2 ?_, h3⟩
    rw [h1, h2]; exact hu
  set g := MultiplicityOne.finProj K n u with hg
  obtain ⟨hgU, hg1⟩ := key u hu
  have hme : MeasurableEmbedding (fun k : G1 K n => g * k) := measurableEmbedding_mulLeft g
  have hcomp := (D.inv g hgU).integral_comp hme (fun k => D.e k • rightRegularRep (Gam K n) μ k v)
  unfold TypeDat.FixedByTypeProjector at hv
  have hint : Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k v) D.ν ∨ v = 0 := by
    by_cases h : Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k v) D.ν
    · exact Or.inl h
    · rw [integral_undef h] at hv
      exact Or.inr hv.symm
  rcases hint with hint | h0
  · calc rhoF μ u v = rhoF μ u (∫ k, D.e k • rightRegularRep (Gam K n) μ k v ∂D.ν) := by rw [hv]
      _ = ∫ k, rhoF μ u (D.e k • rightRegularRep (Gam K n) μ k v) ∂D.ν := ((rhoF μ u).integral_comp_comm hint).symm
      _ = ∫ k, D.e (g * k) • rightRegularRep (Gam K n) μ (g * k) v ∂D.ν := by
          refine integral_congr_ae (D.supp.mono fun k hk => ?_)
          show rhoF μ u (D.e k • rightRegularRep (Gam K n) μ k v) = D.e (g * k) • rightRegularRep (Gam K n) μ (g * k) v
          rw [hD.2.2 g hgU hg1 k hk, map_smul, UnitaryRep.map_mul_apply]
          rfl
      _ = v := hcomp.trans hv
  · rw [h0, map_zero]

private theorem proj_absorb {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P e : H →L[ℂ] H) (hP : IsOrthogonalProjectionTwoLines J J' P) (he : IsSelfAdjoint e)
    (h1 : ∀ u, e (J u) = J u) (h2 : ∀ u, e (J' u) = J' u) : P * e = P ∧ e * P = P := by
  have hs : ∀ x y, ⟪x, e y⟫_ℂ = ⟪e x, y⟫_ℂ := fun x y => (he.isSymmetric x y).symm
  have a : P * e = P := by
    refine ContinuousLinearMap.ext fun h => ?_
    have : P (e h - h) = 0 := (hP.2.2 _).2 ⟨fun u => by rw [inner_sub_right, hs, h1, sub_self],
      fun u => by rw [inner_sub_right, hs, h2, sub_self]⟩
    rw [map_sub, sub_eq_zero] at this
    exact this
  refine ⟨a, ?_⟩
  have := congrArg star a
  rwa [star_mul, he.star_eq, hP.1.star_eq] at this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.genTk :
    ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {μ : Measure (normOneGL (K := E) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : _root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) (w : Pl E), w ∉ 𝔢.S → ∀ i : Fin (2 + 2),
      (∃ s, Act 𝔵.A'.J (Tsph μ w i) s) ∧ Tsph μ w i ∘L 𝔵.P = 𝔵.P ∘L Tsph μ w i := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 w hw i
  have hc : IsCompact (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) :=
    (AdelicGLn.isCompact_integralFiniteGL E (2 + 2)).of_isClosed_subset (𝔢.U.isClosed_of_isOpen 𝔢.isOpen) 𝔢.le
  have hp' : Pair (BW.mu1 E 2) 𝔵.τ₂ 𝔵.τ₁ := ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩
  let m : Measure (AdelicGLn.FiniteAdelicGL E (2 + 2)) := Measure.haar
  set x := Cartan.diagPow (w.adicCompletion E) (2 + 2) fun a => if a ≤ i then 1 else 0 with hx
  set T := Hop μ w (GLnLocal.integralGL (w.adicCompletion E) (2 + 2)) x with hT
  obtain ⟨hcomm, e, he, hO⟩ := UpperTheory.ConvolutionTheory.Tf.hopLevel E (2 + 2) μ m w (GLnLocal.integralGL (w.adicCompletion E) (2 + 2)) x 𝔢.U
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) 𝔢.isOpen hc (𝔢.max w hw)
    fun u hu => (mem_maxCompact.1 (finEmb_mem_maxCompact (𝔢.le hu))).2 w
  have hbi : ∀ k ∈ 𝔢.U, ∀ h, e (k * h) = e h ∧ e (h * k) = e h := by
    have hl : ∀ k ∈ 𝔢.U, ∀ h ∈ (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) * {AdelicGLn.localEmbedding w x} * (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))),
        k * h ∈ (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) * {AdelicGLn.localEmbedding w x} * (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) ∧
        h * k ∈ (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) * {AdelicGLn.localEmbedding w x} * (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) := by
      rintro k hk _ ⟨_, ⟨a, ha, y, hy, rfl⟩, b, hb, rfl⟩
      exact ⟨⟨_, ⟨k * a, 𝔢.U.mul_mem hk ha, y, hy, rfl⟩, b, hb, by simp only [mul_assoc]⟩,
        ⟨_, ⟨a, ha, y, hy, rfl⟩, b * k, 𝔢.U.mul_mem hb hk, by simp only [mul_assoc]⟩⟩
    intro k hk h
    rw [he, he, he]
    by_cases hh : h ∈ (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) * {AdelicGLn.localEmbedding w x} * (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2)))
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (hl k hk h hh).1, Set.indicator_of_mem (hl k hk h hh).2]
      exact ⟨rfl, rfl⟩
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem, Set.indicator_of_notMem]
      · exact ⟨rfl, rfl⟩
      · intro h'
        have := (hl _ (𝔢.U.inv_mem hk) _ h').2
        rw [mul_inv_cancel_right] at this
        exact hh this
      · intro h'
        have := (hl _ (𝔢.U.inv_mem hk) _ h').1
        rw [inv_mul_cancel_left] at this
        exact hh this
  have hfix := (UpperTheory.ConvolutionTheory.Tf.commPrj E (2 + 2) μ 𝔢.U).2.2.2.1
  have f1 : ∀ u, prj (fixF μ 𝔢.U) (𝔵.A.J u) = 𝔵.A.J u := fun u =>
    hfix _ (fix_of_level μ 𝔵.D 𝔢.U 𝔵.level 𝔢.le _ (ctZero E μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' u).2.1)
  have f2 : ∀ u, prj (fixF μ 𝔢.U) (𝔵.A'.J u) = 𝔵.A'.J u := fun u =>
    hfix _ (fix_of_level μ 𝔵.D 𝔢.U 𝔵.level 𝔢.le _ (ctZero E μ _ _ _ hp' 𝔵.D _ _ 𝔵.A' 𝔵.A u).2.1)
  have hsa : IsSelfAdjoint (prj (fixF μ 𝔢.U)) := isSelfAdjoint_starProjection _
  obtain ⟨a1, a2⟩ := proj_absorb 𝔵.A.J 𝔵.A'.J 𝔵.P _ 𝔵.isP hsa f1 f2
  have hPc := (finAct E μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' 𝔢.U 𝔵.level 𝔢.le m e hbi).2 𝔵.P 𝔵.isP
  obtain ⟨s, ⟨u, κ, hκ, hact, hs⟩, -⟩ := (finAct E μ _ _ _ hp' 𝔵.D _ _ 𝔵.A' 𝔵.A 𝔢.U 𝔵.level 𝔢.le m e hbi).1
  have hA : Act 𝔵.A'.J T s := ⟨u, κ, hκ, fun y => by
    rw [← hact y, hO, ContinuousLinearMap.comp_apply, f2], hs⟩
  have hTP : T * 𝔵.P = 𝔵.P * T := by
    rw [hO] at hPc
    have h1 : T * prj (fixF μ 𝔢.U) * 𝔵.P = 𝔵.P * (T * prj (fixF μ 𝔢.U)) := hPc
    rwa [mul_assoc, a2, hcomm.eq, ← mul_assoc, a1] at h1
  refine ⟨⟨_, ((actLaws 𝔵.A'.J).2.2.1 T s hA).2 _⟩, ?_⟩
  unfold Tsph
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  exact congrArg _ hTP
end

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem esymm_coeff (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (Polynomial.C a * Polynomial.X + 1 : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty => rcases n with _ | n <;> simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul, ih]
    rcases n with _ | n
    · simp [Multiset.esymm]
    · rw [Polynomial.coeff_X_mul, ih, add_comm]
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

private theorem esymm_two (s t : Multiset ℂ) (j : ℕ) :
    ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) j, s.esymm (a 0) * t.esymm (a 1) = (s + t).esymm j := by
  rw [← esymm_coeff (s + t), Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul]
  simp only [esymm_coeff]
  refine Finset.sum_nbij' (fun a => (a 0, a 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simpa [Finset.mem_piAntidiag, Fin.sum_univ_two] using ha
  · intro p hp
    simpa [Finset.mem_piAntidiag, Fin.sum_univ_two] using hp
  · intro a _
    funext i
    fin_cases i <;> rfl
  · intro p _
    rfl
  · intro a _
    rfl

private theorem act_cc {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] {J : L V →ₗᵢ[ℂ] H} {Y : H →L[ℂ] H} {s : ℂ → V →L[ℂ] V} (h : Act J Y s)
    {u : ℝ → V} {U : L V} (hc : Continuous u) (hs : HasCompactSupport u) (hU : ∀ᵐ x : ℝ, U x = u x) :
    ∃ (u' : ℝ → V) (U' : L V), Continuous u' ∧ HasCompactSupport u' ∧ (∀ᵐ x : ℝ, U' x = u' x) ∧ Y (J U) = J U' ∧
      ∫ x, u' x = s 0 (∫ x, u x) := by
  obtain ⟨a, κ, hκ, hY, hs0⟩ := h
  have hκ' : Continuous fun t => κ (-t) := hκ.1.comp continuous_neg
  have hκs : HasCompactSupport fun t => κ (-t) := hκ.2.comp_homeomorph (Homeomorph.neg ℝ)
  have hκi := hκ'.integrable_of_hasCompactSupport (μ := volume) hκs
  have hui := hc.integrable_of_hasCompactSupport (μ := volume) hs
  let cv := convolution (fun t => κ (-t)) u (ContinuousLinearMap.id ℂ (V →L[ℂ] V)) volume
  have cvc : Continuous cv := hs.continuous_convolution_right _ hκi.locallyIntegrable hc
  have cvs : HasCompactSupport cv := hκs.convolution _ hs
  have cve : ∀ x, cv x = ∫ t, κ t (u (x + t)) := fun x => by
    rw [← integral_neg_eq_self]
    simp only [cv, convolution, ContinuousLinearMap.id_apply, sub_eq_add_neg]
  have cvi : ∫ x, cv x = symb κ 0 (∫ x, u x) := by
    rw [integral_convolution _ hκi hui, integral_neg_eq_self κ, symb]
    simp
  have tc : ∀ t, Continuous fun x => a t (u (x + t)) := fun t => (a t).continuous.comp (hc.comp (continuous_add_const t))
  have ts : ∀ t, HasCompactSupport fun x => a t (u (x + t)) := fun t =>
    (hs.comp_homeomorph (Homeomorph.addRight t)).comp_left (g := a t) (map_zero _)
  have sc : Continuous fun x => ∑ t ∈ a.support, a t (u (x + t)) := by
    induction a.support using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact continuous_const
    | insert t T ht ih =>
      simp only [Finset.sum_insert ht]
      exact (tc t).add ih
  have ss : HasCompactSupport fun x => ∑ t ∈ a.support, a t (u (x + t)) := by
    induction a.support using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact HasCompactSupport.zero
    | insert t T ht ih =>
      simp only [Finset.sum_insert ht]
      exact (ts t).add ih
  refine ⟨fun x => ∑ t ∈ a.support, a t (u (x + t)) + cv x, _, sc.add cvc, ss.add cvs, ?_, hY U, ?_⟩
  · have h1 : ∀ᵐ x : ℝ, ∀ t ∈ a.support, (a t).compLpL 2 volume (sh V t U) x = a t (u (x + t)) := by
      refine (Filter.eventually_all_finset _).2 fun t _ => ?_
      filter_upwards [(a t).coeFn_compLpL (sh V t U), sh_ae V t U,
        (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hU] with x p q r
      rw [p, q, r]
    filter_upwards [h1, Lp.coeFn_add (a.sum fun t c => c.compLpL 2 volume (sh V t U)) (conv κ U), (convSpec κ hκ U).1,
      MeasureTheory.Lp.coeFn_finsetSum a.support fun t => (a t).compLpL 2 volume (sh V t U)] with x p q r o
    rw [q, Pi.add_apply, r, cve, Finsupp.sum, o]
    congr 1
    · rw [Finset.sum_apply]
      exact Finset.sum_congr rfl p
    · refine integral_congr_ae ?_
      filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hU] with t ht
      rw [ht]
  · rw [integral_add (sc.integrable_of_hasCompactSupport ss) (cvc.integrable_of_hasCompactSupport cvs), cvi, hs0,
      integral_finsetSum _ fun t _ => (tc t).integrable_of_hasCompactSupport (ts t), ContinuousLinearMap.add_apply, Finsupp.sum,
      ContinuousLinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(a t).integral_comp_comm (hui.comp_add_right t), integral_add_right_eq_self]
    simp

private theorem sign_data_rank_two {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (Pl E)} (b b' : BW.Blo S 2) :
    (dat2 b b').rho (0 : Fin 2) = -1 ∧ (dat2 b b').rho (1 : Fin 2) = 1 := by
  constructor
  · show ((∑ _l ∈ (∅ : Finset (Fin 2)), ((2 : ℕ) : ℝ)) - ((((2 : ℕ) : ℝ)) + 0)) / 2 = -1
    norm_num
  · show (((((2 : ℕ) : ℝ)) + 0) - ∑ _l ∈ (∅ : Finset (Fin 2)), ((2 : ℕ) : ℝ)) / 2 = 1
    norm_num

private theorem hecke_eigenvalue_rank_two_data {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (Pl E)} (b b' : BW.Blo S 2)
    (φ : GlobalTheory.CuspRep.Sm E (2 + 2)) (w : Pl E) (j : ℕ) (t : Fin 2 → ℝ) (h : BW.Umg φ) (hS : BW.Sph S φ) (hw : w ∉ S) (hj : j ≤ 2 + 2) :
    (dat2 b b').comp (BW.hk (2 + 2) w j φ).1 t = ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) j,
      (((b.sat w).map fun x : ℂˣ => (x : ℂ)).esymm (a 0) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-((-1 : ℝ) : ℂ) * a 0)) *
      (((b'.sat w).map fun x : ℂˣ => (x : ℂ)).esymm (a 1) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-((1 : ℝ) : ℂ) * a 1)) *
      (dat2 b b').comp φ.1 (fun l : Fin 2 => t l - a l * Real.log (Formalism.UG.qV E w)) := by
  refine (BW.compHecke E S (2 + 2) (dat2 b b') φ w j t h hS hw hj).trans (Finset.sum_congr rfl fun a _ => ?_)
  refine congrArg₂ (· * ·) ((Fin.prod_univ_two _).trans ?_) rfl
  rw [← (sign_data_rank_two b b').1]
  conv_rhs => enter [2]; rw [← (sign_data_rank_two b b').2]
  rfl

private theorem cancel {q : ℕ} (hq : q ≠ 0) (x : ℝ) (a b : ℕ) :
    (q : ℂ) ^ (-((-1 : ℝ) : ℂ) * a) * (q : ℂ) ^ (-((1 : ℝ) : ℂ) * b) *
      Complex.exp ((x - a * Real.log q - (-x - b * Real.log q) : ℝ) : ℂ) = Complex.exp ((x - -x : ℝ) : ℂ) := by
  have h : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [Complex.cpow_def_of_ne_zero h, Complex.cpow_def_of_ne_zero h, ← Complex.exp_add, ← Complex.exp_add, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.genT :
    ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {μ : Measure (normOneGL (K := E) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : _root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) (w : Pl E), w ∉ 𝔢.S → ∀ i : Fin (2 + 2),
      (∃ s, Act 𝔵.A'.J (Tsph μ w i) s ∧ s 0 ∘L 𝔵.a₀ = hval 𝔵.t (w, i) • 𝔵.a₀) ∧ Tsph μ w i ∘L 𝔵.P = 𝔵.P ∘L Tsph μ w i := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 w hw i
  obtain ⟨⟨s, hs⟩, hP⟩ := genTk 𝔵 w hw i
  refine ⟨⟨s, hs, ?_⟩, hP⟩
  ext1 e
  obtain ⟨ρ, N, Lf, hL, -⟩ := BW.ampRep E (2 + 2) μ 𝔢.toAmp (by norm_num)
  let β : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have c₀ : Continuous fun x : ℝ => β.normed volume x • e := β.continuous_normed.smul continuous_const
  have s₀ : HasCompactSupport fun x : ℝ => β.normed volume x • e := β.hasCompactSupport_normed.smul_right
  have i₀ : ∫ x : ℝ, β.normed volume x • e = e := by rw [integral_smul_const, β.integral_normed, one_smul]
  have m₀ : MemLp (fun x : ℝ => β.normed volume x • e) 2 volume := c₀.memLp_of_hasCompactSupport s₀
  obtain ⟨u, U, uc, us, hU, hAU, iu⟩ := act_cc ((actLaws 𝔵.A'.J).2.1 _ _ 𝔵.a_acts.1 𝔵.a_acts.2.1) c₀ s₀ m₀.coeFn_toLp
  obtain ⟨u', U', uc', us', hU', hTU, iu'⟩ := act_cc hs uc us hU
  rw [i₀] at iu
  obtain ⟨hR, -, hS⟩ := hL (𝔵.A'.J m₀.toLp)
  set φ := Lf (𝔵.A'.J m₀.toLp)
  rw [← 𝔢.a_op, hAU] at hR
  have hR' := (BW.repOps E (2 + 2) μ (by norm_num) _ _ hR).2.2.2 w i (hS w hw)
  rw [hTU] at hR'
  refine sub_eq_zero.1 (bloEx 𝔵 _ fun b b' hb hb' k hk => ?_)
  obtain ⟨ℓ, hℓ⟩ := ellLin 𝔵 b b' hb hb' k
  obtain ⟨c, hc, hcl⟩ := compLine 𝔵 b b' hb hb'
  have h1 := hcl k hk u U φ uc us hU hR
  have h2 := hcl k hk u' U' _ uc' us' hU' hR'
  obtain ⟨hS', hcomm⟩ := ((BW.hkOps E (2 + 2) w (i + 1)).2.2.2 𝔢.S φ hw hS).2.2.1 ⟨_, hk⟩
  have hU2 := ((BW.umgOps E (2 + 2)).2 φ hR.umg).2.2.2.2.1 ((k : G1 E (2 + 2)) : GlobalTheory.CuspRep.GA E (2 + 2))
  have pw : ∀ x : ℝ, ℓ (u' x) = ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) (i + 1 : ℕ),
      (𝔵.B₂ w).esymm (a 0) * (𝔵.B₁ w).esymm (a 1) * ℓ (u (x - ((a 0 : ℝ) - a 1) * Real.log (Formalism.UG.qV E w) / 2)) := fun x => by
    have h3 := hecke_eigenvalue_rank_two_data b b' _ w (i + 1) ![x, -x] hU2 hS' hw i.2
    have h5 : c * Complex.exp ((x - -x : ℝ) : ℂ) * ell b b' k (𝔵.A'.sec (u' ((x - -x) / 2))) = _ :=
      (h2 (![x, -x] : Fin 2 → ℝ)).symm.trans ((congrArg (fun ψ : GlobalTheory.CuspRep.Sm E (2 + 2) => (dat2 b b').comp ψ.1 (![x, -x] : Fin 2 → ℝ))
        hcomm).trans h3)
    rw [show (x - -x) / 2 = x by ring] at h5
    refine mul_left_cancel₀ (mul_ne_zero hc (Complex.exp_ne_zero ((x - -x : ℝ) : ℂ))) ?_
    rw [hℓ, Finset.mul_sum, h5]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h6 : _ = c * Complex.exp ((x - a 0 * Real.log (Formalism.UG.qV E w) - (-x - a 1 * Real.log (Formalism.UG.qV E w)) : ℝ) : ℂ) *
        ell b b' k (𝔵.A'.sec (u ((x - a 0 * Real.log (Formalism.UG.qV E w) - (-x - a 1 * Real.log (Formalism.UG.qV E w))) / 2))) :=
      h1 fun l : Fin 2 => (![x, -x] : Fin 2 → ℝ) l - a l * Real.log (Formalism.UG.qV E w)
    rw [h6, hb.sat w hw, hb'.sat w hw, hℓ, ← cancel (GlobalTheory.LFun.qV_ne_zero w) x (a 0) (a 1),
      show x - ((a 0 : ℝ) - a 1) * Real.log (Formalism.UG.qV E w) / 2 =
        (x - a 0 * Real.log (Formalism.UG.qV E w) - (-x - a 1 * Real.log (Formalism.UG.qV E w))) / 2 by ring]
    ring
  have hui := uc.integrable_of_hasCompactSupport (μ := volume) us
  have h4 := integral_congr_ae (μ := volume) (Eventually.of_forall pw)
  rw [ℓ.integral_comp_comm (uc'.integrable_of_hasCompactSupport us'),
    integral_finsetSum _ fun a _ => (ℓ.integrable_comp (hui.comp_sub_right _)).const_mul _] at h4
  simp only [integral_const_mul, integral_sub_right_eq_self fun x => ℓ (u x)] at h4
  rw [← Finset.sum_mul, esymm_two, ℓ.integral_comp_comm hui, iu', iu, add_comm] at h4
  rw [← hℓ, map_sub, sub_eq_zero]
  exact h4.trans (ℓ.map_smul _ _).symm
end

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

private def Good (J : L V →ₗᵢ[ℂ] H) (P : H →L[ℂ] H) (a : V →L[ℂ] V) (Y : H →L[ℂ] H) (c : ℝ → ℂ) : Prop :=
  (∃ s, Act J Y s ∧ ∀ x : ℝ, 0 < x → ∀ v ∈ Module.End.eigenspace (a : V →ₗ[ℂ] V) (x : ℂ), s 0 v = c x • v) ∧
    Y ∘L P = P ∘L Y

variable {J : L V →ₗᵢ[ℂ] H} {P : H →L[ℂ] H} {a : V →L[ℂ] V}

private theorem act_const (c : ℂ) : Act J (c • (1 : H →L[ℂ] H)) fun _ => c • (1 : V →L[ℂ] V) :=
  ((actLaws J).2.2.1 _ _ (actLaws J).1).2 c

private theorem good_const (c : ℂ) : Good J P a (c • (1 : H →L[ℂ] H)) fun _ => c := by
  refine ⟨⟨_, act_const c, fun x _ v _ => by simp⟩, ?_⟩
  ext v
  simp

private theorem good_add {Y Y' : H →L[ℂ] H} {c c' : ℝ → ℂ} (h : Good J P a Y c) (h' : Good J P a Y' c') :
    Good J P a (Y + Y') fun x => c x + c' x := by
  obtain ⟨⟨s, hs, hz⟩, hc⟩ := h
  obtain ⟨⟨s', hs', hz'⟩, hc'⟩ := h'
  refine ⟨⟨_, ((actLaws J).2.2.2.1 _ _ _ _ hs hs').1, fun x hx v hv => ?_⟩, ?_⟩
  · simp only [ContinuousLinearMap.add_apply, hz x hx v hv, hz' x hx v hv, add_smul]
  · rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hc, hc']

private theorem good_mul {Y Y' : H →L[ℂ] H} {c c' : ℝ → ℂ} (h : Good J P a Y c) (h' : Good J P a Y' c') :
    Good J P a (Y * Y') fun x => c x * c' x := by
  obtain ⟨⟨s, hs, hz⟩, hc⟩ := h
  obtain ⟨⟨s', hs', hz'⟩, hc'⟩ := h'
  refine ⟨⟨_, ((actLaws J).2.2.2.1 _ _ _ _ hs hs').2, fun x hx v hv => ?_⟩, ?_⟩
  · simp only [ContinuousLinearMap.comp_apply, hz x hx v hv, hz' x hx v hv, map_smul, smul_smul, mul_comm]
  · change (Y ∘L Y') ∘L P = P ∘L (Y ∘L Y')
    rw [ContinuousLinearMap.comp_assoc, hc', ← ContinuousLinearMap.comp_assoc, hc, ContinuousLinearMap.comp_assoc]

private theorem symb_hom {R : Type} [Semiring R] (f : R →+* (H →L[ℂ] H)) (h : ∀ r, ∃ s, Act J (f r) s) :
    ∃ e : ℂ → R →+* (V →L[ℂ] V), ∀ r, Act J (f r) fun z => e z r := by
  choose s hs using h
  have h1 : s 1 = fun _ => 1 := actUniq J _ _ _ (hs 1) (by rw [map_one]; exact (actLaws J).1)
  have h0 : s 0 = fun _ => 0 := actUniq J _ _ _ (hs 0) (by
    have := act_const (J := J) 0
    rw [map_zero]
    simpa only [zero_smul] using this)
  have ha : ∀ r r', s (r + r') = fun z => s r z + s r' z := fun r r' =>
    actUniq J _ _ _ (hs _) (by rw [map_add (f := _)]; exact ((actLaws J).2.2.2.1 _ _ _ _ (hs r) (hs r')).1)
  have hm : ∀ r r', s (r * r') = fun z => s r z * s r' z := fun r r' =>
    actUniq J _ _ _ (hs _) (by rw [map_mul]; exact ((actLaws J).2.2.2.1 _ _ _ _ (hs r) (hs r')).2)
  exact ⟨fun z =>
    { toFun := fun r => s r z
      map_one' := congrFun h1 z
      map_mul' := fun r r' => congrFun (hm r r') z
      map_zero' := congrFun h0 z
      map_add' := fun r r' => congrFun (ha r r') z }, hs⟩

private theorem good_poly {σ τ : Type} (f : MvPolynomial σ (MvPolynomial τ ℂ) →+* (H →L[ℂ] H))
    (g : ℝ → MvPolynomial σ (MvPolynomial τ ℂ) →+* ℂ)
    (hc : ∀ c, Good J P a (f (C (C c))) fun x => g x (C (C c)))
    (ht : ∀ t, Good J P a (f (C (X t))) fun x => g x (C (X t)))
    (hs : ∀ s, Good J P a (f (X s)) fun x => g x (X s)) (r : MvPolynomial σ (MvPolynomial τ ℂ)) :
    Good J P a (f r) fun x => g x r := by
  induction r using MvPolynomial.induction_on with
  | C p =>
    induction p using MvPolynomial.induction_on with
    | C c => exact hc c
    | add p q hp hq => simpa only [map_add (f := _)] using good_add hp hq
    | mul_X p t hp => simpa only [map_mul] using good_mul hp (ht t)
  | add p q hp hq => simpa only [map_add (f := _)] using good_add hp hq
  | mul_X p t hp => simpa only [map_mul] using good_mul hp (hs t)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.evzEx :
    ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {μ : Measure (normOneGL (K := E) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (ev : PR E (2 + 2) →+* (LL μ →L[ℂ] LL μ)), 𝔢.toAmp.IsEv ev → ∃ evz, 𝔵.IsEvz ev evz := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 ev hev
  classical
  let π : PR E (2 + 2) →+* PR E (2 + 2) := eval₂Hom C fun y => if y.1 ∈ 𝔢.S then 0 else X y
  have hπC : ∀ p, π (C p) = C p := fun p => eval₂Hom_C _ _ _
  have hπX : ∀ y, π (X y) = if y.1 ∈ 𝔢.S then 0 else X y := fun y => eval₂Hom_X' _ _ _
  have hπ : ∀ R : PR E (2 + 2), (∀ y ∈ R.vars, y.1 ∉ 𝔢.S) → π R = R := fun R hR =>
    hom_congr_vars (f₁ := π) (f₂ := RingHom.id _) (RingHom.ext fun p => hπC p)
      (fun y hy _ => by rw [hπX, if_neg (hR y hy)]; rfl) rfl
  have hA : Act 𝔵.A'.J 𝔢.toAmp.A (symb 𝔵.βa) := by
    rw [← 𝔢.a_op]
    exact (actLaws 𝔵.A'.J).2.1 _ _ 𝔵.a_acts.1 𝔵.a_acts.2.1
  have hG : ∀ R, Good 𝔵.A'.J 𝔵.P 𝔵.a₀ ((ev.comp π) R) fun x => ((val x 𝔵.Λ 𝔵.t).comp π) R := by
    refine good_poly (ev.comp π) (fun x => (val x 𝔵.Λ 𝔵.t).comp π) (fun c => ?_) (fun t => ?_) (fun y => ?_)
    · simp only [RingHom.comp_apply, hπC, hev.const, val, eval₂Hom_C, eval_C]
      exact good_const c
    · simp only [RingHom.comp_apply, hπC, val, eval₂Hom_C, eval_X]
      cases t with
      | none =>
        rw [hev.amp]
        refine ⟨⟨_, hA, fun x _ v hv => Module.End.mem_eigenspace_iff.1 hv⟩, ?_⟩
        rw [← 𝔢.a_op]
        exact (Hecke₃ E μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' 𝔵.P 𝔵.isP).2 _ 𝔵.a_hecke
      | some y =>
        rw [hev.cen]
        obtain ⟨⟨β, hk, hc, hz⟩, hP⟩ := genZ 𝔵 y
        refine ⟨⟨_, (actLaws 𝔵.A'.J).2.1 _ _ hk hc, fun x _ v hv => ?_⟩, hP⟩
        have hv' : 𝔵.a₀ v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv
        rw [hz, ContinuousLinearMap.smul_apply, hv', smul_smul, mul_comm]
        rfl
    · simp only [RingHom.comp_apply, hπX]
      by_cases hy : y.1 ∈ 𝔢.S
      · simp only [if_pos hy, map_zero]
        simpa only [zero_smul] using good_const (J := 𝔵.A'.J) (P := 𝔵.P) (a := 𝔵.a₀) 0
      · obtain ⟨w, i⟩ := y
        simp only [if_neg hy, val, eval₂Hom_X']
        rw [hev.hecke w hy i]
        obtain ⟨⟨s, hs, hz⟩, hP⟩ := genT 𝔵 w hy i
        refine ⟨⟨s, hs, fun x hx v hv => ?_⟩, hP⟩
        have hv' : 𝔵.a₀ v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv
        have h1 : s 0 (𝔵.a₀ v) = hval 𝔵.t (w, i) • 𝔵.a₀ v := DFunLike.congr_fun hz v
        rw [hv', map_smul, smul_comm] at h1
        exact smul_right_injective _ (Complex.ofReal_ne_zero.2 hx.ne') h1
  obtain ⟨e, he⟩ := symb_hom (J := 𝔵.A'.J) (ev.comp π) fun R => (hG R).1.imp fun _ h => h.1
  refine ⟨e, fun R hR => ?_, fun R hR => ?_, fun z c => ?_, fun z => ?_, fun R hR x hx v hv => ?_⟩
  · have := he R
    rwa [RingHom.comp_apply, hπ R hR] at this
  · have := (hG R).2
    rwa [RingHom.comp_apply, hπ R hR] at this
  · have := he (C (C c))
    rw [RingHom.comp_apply, hπC, hev.const] at this
    exact congrFun (actUniq _ _ _ _ this (act_const c)) z
  · have := he (C (X none))
    rw [RingHom.comp_apply, hπC, hev.amp] at this
    exact congrFun (actUniq _ _ _ _ this hA) z
  · obtain ⟨s, hs, hz⟩ := (hG R).1
    have h1 : e 0 R = s 0 := congrFun (actUniq _ _ _ _ (he R) hs) 0
    have h2 := hz x hx v hv
    simp only [RingHom.comp_apply, hπ R hR] at h2
    rw [h1, h2]
