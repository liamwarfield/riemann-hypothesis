module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.PairGOps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExpAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.SideCenOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.CoefSm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.SideOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ContDiffFderivApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.HasDerivAtProdLog
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.TestEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.HasFDerivAtExpF
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.MatchBCOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.LeviDiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.CoefInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppBridge
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Reps

@[expose] public section

attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.GamLocOf
open NumberField IsDedekindDomain MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet GroundTheory.Automorphic.GJStandardL
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem UpperTheory.V.Z.Gam.gamLocOf :
    UpperTheory.V.Z.Gam.GamLocOf := by
  intro hL hC hS K _ _ n _ v V _ _ π s hs
  have hirr : π.IsIrreducible := hs.isIrreducible
  have hsm : IsSmooth π := hs.isSmooth
  have hψ := GroundTheory.Global.continuous_localAdelicChar (K := K) v
  have hψ1 := GroundTheory.Global.localAdelicChar_ne_one (K := K) v
  obtain ⟨β, W, _, _, σ, hσirr, hσs, hσc, hσa, ι, hι⟩ := exists_embedding_parabolicInd (π := π) hsm
  obtain ⟨γ, hγ⟩ := exists_leviFE hσa hσc (inducedChar β) continuous_inducedChar
    (leviMeasure β (GroundTheory.Global.localAdelicChar K v)) hψ hψ1
  obtain ⟨P, c, j, h0, hd, hc, hγ'⟩ := hL _ n β W σ hσa hσirr hσc _ continuous_inducedChar _ _ hψ hψ1 γ hγ
  refine ⟨P, c, j, h0, ?_, hc, ?_⟩
  · rw [hd]
    exact (hS _ n V π s hs β W σ hσa hσirr hσc ι hι).symm
  · rw [← GroundTheory.Global.residueCard_adicCompletion, ← hγ']
    exact hC _ n V π hsm β W σ hσs ι hι _ _ hψ hψ1 γ (inducedFE_of_leviFE _ hψ hψ1 hγ)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SideGCenOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.HenQ Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.GJStandardLCuspidal UpperTheory.V UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem eval_quot (N D : ℂ[X]) (x : ℂ) (hD : D.eval x ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) D).eval (RingHom.id ℂ) x = N.eval x / D.eval x := by
  have hD0 : D ≠ 0 := fun e => hD (by simp [e])
  set R := algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) D with hR
  have h1 : R.denom ∣ D := RatFunc.denom_div_dvd N D
  have h2 : R.denom.eval x ≠ 0 := fun e => by
    obtain ⟨u, hu⟩ := h1
    exact hD (by rw [hu, eval_mul, e, zero_mul])
  have h3 : R.num * D = N * R.denom := (RatFunc.num_mul_eq_mul_denom_iff hD0).2 hR
  have h4 := congrArg (eval x) h3
  simp only [eval_mul] at h4
  simp only [RatFunc.eval, eval₂_id]
  rw [div_eq_div_iff h2 hD, h4]

private theorem loc_dual {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (P : ℂ[X]) (c Q b : ℂ) (j : ℤ) (hP : P.eval 0 = 1) {A B : ℂ → ℂ}
    (h : RatFE F (RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) P /
      algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C Q * X))) A B) (hA : ∀ s, A s = b) :
    ∃ r : ℝ, ∀ s : ℂ, s.re < -r → B s = c * b * qs F s ^ j * P.eval (qs F s) / P.eval (Q * qs F s) := by
  obtain ⟨R, s₁, h1, h2⟩ := h
  have hR : R = RatFunc.C b := eq_of_eval_qs_eq_right (F := F) (s₁ := s₁) fun s hs => by
    rw [← h1 s hs, hA, RatFunc.eval_C]
    rfl
  have hD0 : P.comp (C Q * X) ≠ 0 := fun e => by
    have := congrArg (eval 0) e
    simp [eval_comp, hP] at this
  obtain ⟨Bd, hB, h4⟩ := exists_norm_gt_eval_ne_zero hD0
  have hq : (1 : ℝ) < GroundTheory.LocalField.residueCard F := by exact_mod_cast GroundTheory.LocalField.one_lt_residueCard
  refine ⟨max s₁ (Real.logb (GroundTheory.LocalField.residueCard F) Bd), fun s hs => ?_⟩
  have hs1 := le_max_left s₁ (Real.logb (GroundTheory.LocalField.residueCard F) Bd)
  have hs2 := le_max_right s₁ (Real.logb (GroundTheory.LocalField.residueCard F) Bd)
  have h5 : (P.comp (C Q * X)).eval (qs F s) ≠ 0 := h4 _ (by
    rw [norm_qs]
    calc Bd = (GroundTheory.LocalField.residueCard F : ℝ) ^ (Real.logb (GroundTheory.LocalField.residueCard F) Bd) :=
          (Real.rpow_logb (by linarith) hq.ne' hB).symm
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt hq (by linarith))
  have hx : qs F s ≠ 0 := qs_ne_zero s
  have hj : j = (j.toNat : ℤ) - ((-j).toNat : ℤ) := (Int.toNat_sub_toNat_neg j).symm
  have e : RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) P /
      algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C Q * X)) * RatFunc.C b =
      algebraMap ℂ[X] (RatFunc ℂ) (C c * C b * X ^ j.toNat * P) /
        algebraMap ℂ[X] (RatFunc ℂ) (X ^ (-j).toNat * P.comp (C Q * X)) := by
    simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rw [hj, zpow_sub₀ RatFunc.X_ne_zero, zpow_natCast, zpow_natCast, ← hj]
    ring
  rw [h2 s (by linarith), hR, e, eval_quot _ _ _ (by rw [eval_mul, eval_pow, eval_X]; exact mul_ne_zero (pow_ne_zero _ hx) h5)]
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_comp]
  rw [hj, zpow_sub₀ hx, zpow_natCast, zpow_natCast, ← hj]
  ring

private theorem comb {I : Type} (S : Finset I) (N : I → ℕ) (P : I → ℂ[X]) (c : I → ℂ) (j : I → ℤ) (q : ℕ) (f d : I → ℕ)
    (hq : 1 < q) (h : ∀ v ∈ S, 1 < N v ∧ (P v).eval 0 = 1 ∧ (P v).natDegree = d v ∧ (d v ≠ 0 → N v = q ^ f v)) :
    ∃ (P₀ : ℂ[X]) (c₀ : ℂ) (t : ℝ), P₀.eval 0 = 1 ∧ P₀.natDegree = ∑ v ∈ S, f v * d v ∧ ∀ s : ℂ,
      ∏ v ∈ S, c v * ((N v : ℂ) ^ (-s)) ^ j v * (P v).eval ((N v : ℂ) ^ (-s)) / (P v).eval (N v * (N v : ℂ) ^ (-s)) =
        fac c₀ t q P₀ s := by
  have h1 : ∀ v ∈ S, d v = 0 → P v = 1 := fun v hv e => by
    have a := eq_C_of_natDegree_eq_zero ((h v hv).2.2.1.trans e)
    have b := (h v hv).2.1
    rw [a, eval_C] at b
    rw [a, b, C_1]
  have h0 : ∀ v ∈ S, ((P v).comp (X ^ f v)).eval 0 = 1 := fun v hv => by
    by_cases e : d v = 0
    · simp [h1 v hv e]
    · have hf : f v ≠ 0 := fun e' => by
        have := (h v hv).2.2.2 e
        have := (h v hv).1
        rw [e', pow_zero] at *
        omega
      rw [eval_comp, eval_pow, eval_X, zero_pow hf, (h v hv).2.1]
  have hev : ∀ v ∈ S, ∀ u : ℂ, ((P v).comp (X ^ f v)).eval (((q : ℝ) : ℂ) ^ u) = (P v).eval ((N v : ℂ) ^ u) := fun v hv u => by
    by_cases e : d v = 0
    · simp [h1 v hv e]
    · rw [eval_comp, eval_pow, eval_X, (h v hv).2.2.2 e, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
        Complex.ofReal_natCast, Complex.cpow_nat_mul]
  refine ⟨∏ v ∈ S, (P v).comp (X ^ f v), ∏ v ∈ S, c v, ∑ v ∈ S, -(j v * Real.log (N v)), ?_, ?_, fun s => ?_⟩
  · rw [eval_prod]
    exact Finset.prod_eq_one h0
  · rw [natDegree_prod _ _ fun v hv e => by simpa [e] using h0 v hv]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [natDegree_comp, natDegree_X_pow, (h v hv).2.2.1, mul_comm]
  · rw [fac, eval_prod, eval_prod, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hN : (N v : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (h v hv).1; omega)
    rw [hev v hv, hev v hv, sub_eq_add_neg, Complex.cpow_add _ _ hN, Complex.cpow_one]
    congr 3
    rw [Complex.cpow_def_of_ne_zero hN, ← Complex.exp_int_mul, ← Complex.natCast_log]
    congr 1
    push_cast
    ring

private theorem far_ne {A : ℂ → ℂ} (hA : Differentiable ℂ A) (h0 : A ≠ 0) (c : ℝ) : ∃ s : ℂ, c < s.re ∧ A s ≠ 0 := by
  by_contra h
  push Not at h
  refine h0 (funext fun x => AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hA.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ ((c + 1 : ℝ) : ℂ)) ?_ trivial)
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show c < ((c + 1 : ℝ) : ℂ).re by simp)] with s hs using h s hs

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Z.Gam.sideGCenOf :
    UpperTheory.V.Z.Gam.SideGCenOf := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro hGL hLI K _ _ _ n hn σ h S hRS B hB sp q f hq hsp
    classical
    have hLU := locUnr
    have hSD := satDict
    have hCS := coefSm
    have hAS := archOf (shiftOf (ptwOf weyl) parts) fourD testEx (bridgeOf haarL)
    choose m hm using fun τ : K →+* ℂ => (GlobalTheory.ResW.IrrInfChar.main K n τ).1 σ
    have hn1 : 1 ≤ n := by omega
    obtain ⟨D⟩ := (Cm.toRep σ h).nonempty_adelicDecomposition
    let μ : Measure (Reduction.normOneGL (K := K) (n := n)) := Measure.haar
    obtain ⟨a, x, hx, ha, hx0, hxK⟩ := exists_pureTensor_spherical _ D
    obtain ⟨ℓ, fi, hℓs, hℓ1, hℓK, hf, hF1⟩ := matrixCoeff_factorization_of_pureTensor _ D μ a x hx ha hx0
    have hfix : ∀ v ∉ S, x v ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) := fun v hv =>
      hxK v ((hLI K n σ h D v).2 _ (hB v hv))
    have hsm : ∀ v, x v ∈ smoothVectors (D.finite.π v) := fun v => (D.finite.isAdmissible v).1 (x v)
    set φ₀ : cuspForms K n := Phi0 _ D a x hx with hφ₀
    have hmem : φ₀ ∈ Cm.carrier σ := (phi D a x hx).2
    have hf' : ∀ g, GJGlobal.matrixCoeff μ φ₀.1 φ₀.1 g = fi (archComp K n g) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v)
          (localComp n v g) := hf
    have hF1' : GJGlobal.matrixCoeff μ φ₀.1 φ₀.1 1 ≠ 0 := hF1
    have hone : ∀ v : HeightOneSpectrum (𝓞 K),
        Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v) 1 = 1 := fun v => by
      simpa [Parabolic.matrixCoeff] using hℓ1 v

    obtain ⟨T, hT, hTc⟩ := hCS K n hn1 μ σ h φ₀
    let p : σ.V := ⟨Cm.ofCusp K n φ₀, hmem⟩
    have hfi : ∀ y, fi y = (T p).1 ((AdelicGLn.prodEquiv K n).symm (y, 1)) := fun y => by
      have e1 : archComp K n ((AdelicGLn.prodEquiv K n).symm (y, 1)) = y :=
        congrArg Prod.fst ((AdelicGLn.prodEquiv K n).apply_symm_apply (y, 1))
      have e2 : ∀ v, localComp n v ((AdelicGLn.prodEquiv K n).symm (y, 1)) = 1 := fun v => by
        have e : finComp K n ((AdelicGLn.prodEquiv K n).symm (y, 1)) = 1 :=
          congrArg Prod.snd ((AdelicGLn.prodEquiv K n).apply_symm_apply (y, 1))
        change AdelicGLn.finiteRestrictedEquiv K n (finComp K n _) v = 1
        rw [e, map_one, RestrictedProduct.one_apply]
      rw [hT]
      change _ = GJGlobal.matrixCoeff μ φ₀.1 φ₀.1 _
      rw [hf', e1]
      simp [e2, hone]
    have hfi0 : ∃ y, fi y ≠ 0 := ⟨_, left_ne_zero_of_mul (hf' 1 ▸ hF1')⟩
    obtain ⟨φ, φ', k, k', hk, hk', hAd, hA0, hsh, hsh'⟩ := hAS K n hn1 (T p) m (fun τ u => by
      rw [← hTc τ u p (((m τ).map (u + ·)).prod • p) (show _ = _ by first | exact (hm τ u _ hmem).symm | exact ((hm τ).2 u _ hmem).symm | exact (hm τ _ hmem u).symm | exact ((hm τ).2 _ hmem u).symm), map_smul]) fi hfi hfi0 Measure.haar

    have hz : ∀ v, ∃ z : Fin n → ℂˣ, v ∉ S →
        Spherical.IsSatakeParameter (F := v.adicCompletion K) (D.finite.π v) (localHaar n v) z ∧ B v = Finset.univ.val.map z :=
      fun v => by
        by_cases hv : v ∈ S
        · exact ⟨1, fun e => absurd hv e⟩
        · exact (hSD K n σ h D v _ (hB v hv)).imp fun z hz _ => hz
    choose z hz using hz
    have hb := fun v : HeightOneSpectrum (𝓞 K) => exists_localBump (localHaar n v) (D.finite.π v) (hsm v) (ℓ v) (g₀ := 1)
      (by rw [hone]; exact one_ne_zero)
    choose Φb hΦb b hb0 hb using hb
    let Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ :=
      fun v => if v ∈ S then Φb v else integralIndicator (v.adicCompletion K) n
    have hΦS : ∀ v ∈ S, Φ v = Φb v := fun v hv => if_pos hv
    obtain ⟨c, c', hc, hc', hSB1, hG⟩ := genFE hn μ φ₀.2 φ₀.2 (h hmem) S hRS
      D.finite.π x ℓ hsm hℓs (fun v hv => ⟨hfix v hv, hℓ1 v⟩) (fun v hv => hℓK v (hfix v hv)) D.finite.isIrreducible
      D.finite.isAdmissible z (fun v hv => (hz v hv).1) fi hf' ⟨1, hF1'⟩ Φ (fun v hv => hΦS v hv ▸ hΦb v)
      (fun v hv => if_neg hv)
    obtain ⟨σ₁, Λ, hΛ, h1⟩ := hG φ
    obtain ⟨σ₂, Λ', hΛ', h2⟩ := hG φ'
    have hloc : ∀ s, ∏ v ∈ S, zetaIntegral (localHaar n v) (Φ v)
        (Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v)) s = ∏ v ∈ S, b v := fun s =>
      Finset.prod_congr rfl fun v hv => by rw [hΦS v hv, (hb v s).2.2, detPow, GodementJacquet.absDet]; simp
    have hU := fun v (hv : v ∉ S) => hLU K n hn1 v _ (D.finite.π v) (D.finite.isIrreducible v) (D.finite.isAdmissible v)
      (fun e => hx0 v (by simpa [e] using hfix v hv)) (z v) (hz v hv).1
    have hL : ∀ s, partialL S D.finite.π s = eulerL K (cx B) S s := fun s =>
      tprod_congr fun v => by
        rw [(hU v.1 v.2 s).1, cx, (hz v.1 v.2).2, Multiset.map_map, Multiset.map_map]
        rfl
    have hL' : ∀ s, dualPartialL S D.finite.π (1 - s) = eulerLd K (cx B) S s := fun s =>
      tprod_congr fun v => by
        rw [(hU v.1 v.2 (1 - s)).2]
        simp only [cx]
        rw [(hz v.1 v.2).2, Multiset.map_map, Multiset.map_map, Multiset.map_map]
        rfl
    have hd : ∀ v, ∃ (P : ℂ[X]) (e : ℂ) (j : ℤ) (c : ℝ), v ∈ S → P.eval 0 = 1 ∧ P.natDegree = cnt (sp v) 1 ∧
        ∀ s : ℂ, s.re < -c →
        zetaIntegral (localHaar n v) (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))
          (fun g => Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v) g⁻¹) (1 - s) =
          e * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ^ j * P.eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) /
            P.eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) :=
      fun v => by
        by_cases hv : v ∈ S
        · obtain ⟨P, e, j, hP0, hPd, -, hγ⟩ := hGL K n hn1 v _ (D.finite.π v) (sp v) ((hLI K n σ h D v).1 _ (hsp v hv).1)
          obtain ⟨r, hr⟩ := loc_dual P e _ (b v) j hP0 (hγ (Φ v) (hΦS v hv ▸ hΦb v) (x v) (ℓ v) (hℓs v)) fun s => by
            rw [hΦS v hv, (hb v s).2.2, detPow, GodementJacquet.absDet]; simp
          refine ⟨P, e * b v, j, r, fun _ => ⟨hP0, hPd, fun s hs => ?_⟩⟩
          have hqs : qs (v.adicCompletion K) s = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) := by
            rw [qs, GroundTheory.Global.residueCard_adicCompletion]
          rw [← hqs]
          exact hr s hs
        · exact ⟨0, 0, 0, 0, fun e => absurd e hv⟩
    choose P e j cv hd using hd
    obtain ⟨P₀, c₀, t, hP0, hPd, hfac⟩ := comb S (fun v => Ideal.absNorm v.asIdeal) P e j q f (fun v => cnt (sp v) 1) hq
      fun v hv => ⟨NumberField.HeightOneSpectrum.one_lt_absNorm v, (hd v hv).1, (hd v hv).2.1, (hsp v hv).2⟩
    have hb' : ∏ v ∈ S, b v ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hb0 v
    set r : ℝ := |σ₁| + |σ₂| + ∑ v ∈ S, |cv v| + 2 with hr
    have hs0 : 0 ≤ ∑ v ∈ S, |cv v| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have a1 := le_abs_self σ₁
    have a2 := le_abs_self σ₂
    have a3 := abs_nonneg σ₁
    have a4 := abs_nonneg σ₂
    have hND : ∀ s : ℂ, s.re < -r + 1 → (∏ v ∈ S, zetaIntegral (localHaar n v)
        (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))
        (fun g => Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v) g⁻¹) (1 - s)) =
        fac c₀ t q P₀ s := fun s hs => by
      rw [← hfac]
      refine Finset.prod_congr rfl fun v hv => (hd v hv).2.2 s ?_
      have := Finset.single_le_sum (f := fun v => |cv v|) (fun _ _ => abs_nonneg _) hv
      linarith [le_abs_self (cv v)]
    refine ⟨linPoly (∑ τ, m τ), P₀, (monic_multiset_prod_of_monic _ _ fun z _ => monic_X_add_C z).ne_zero, hP0, hPd,
      Λ, fun s => Λ' (s + 1), fun s => c * archZeta Measure.haar φ fi s * ∏ v ∈ S, b v,
      fun s => c' * archZeta Measure.haar (archMatrixFourier φ) (fun y => fi y⁻¹) (1 - s),
      k, k', c₀, t, r, hΛ, hΛ'.comp (differentiable_id.add_const 1), ?_, hk, hk', fun s hs => ⟨?_, ?_⟩,
      fun s hs => ⟨?_, ?_⟩⟩
    · obtain ⟨s, hs, hA⟩ := far_ne hAd hA0 σ₁
      intro e
      have := (h1 s hs).2.1
      rw [e, hloc] at this
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc hA) hb') (h1 s hs).1 this.symm
    · rw [(h1 s (by linarith)).2.1, hloc, hL]
      ring
    · beta_reduce
      rw [(h2 (s + 1) (by simp; linarith)).2.1, hloc, hL, hsh]
      ring
    · have := (h1 (1 - s) (by simp; linarith)).2.2
      rw [sub_sub_cancel, hL', hND s (by linarith)] at this
      rw [this]
      ring
    · have := (h2 (1 - (s + 1)) (by simp; linarith)).2.2
      rw [sub_sub_cancel, hL', hND (s + 1) (by simp; linarith), hsh', show 1 - (s + 1) + 1 = 1 - s by ring] at this
      beta_reduce
      rw [this]
      ring
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SideGOf
open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

variable {K : Type} [Field K] [NumberField K]

private theorem norm_ne (w : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  exact_mod_cast h0

private theorem euler_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerL K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerL K B S s := by
  unfold eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

private theorem eulerd_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerLd K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerLd K B S s := by
  unfold eulerLd eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_inv, Complex.cpow_neg, inv_inv, mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

private theorem cnt_unram {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL (k := k))) {χ : kˣ →* ℂˣ} (h : IsUnram χ) : cnt s χ = cnt s 1 := by
  unfold cnt
  congr 1
  refine Multiset.filter_congr fun y _ => ?_
  have key : ∀ ξ : kˣ →* ℂˣ, IsUnram (ξ * χ) ↔ IsUnram (ξ * 1) := fun ξ =>
    forall_congr' fun x => forall_congr' fun hx => by
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, h x hx, MonoidHom.one_apply]
  simp only [key]

private theorem unram_loc {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : χ.UnrAt v) : IsUnram (χ.loc v) := by
  intro x hx
  haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact h x ((ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).eq_one_iff_eq_one.1 hx)

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.sideGOf :
    UpperTheory.V.Z.Gam.SideGOf := by
  intro hO hF hC K _ _ _ n hn σ S hS B hB s q f hq hs
  let x : GlobalTheory.ResW.Letter K := ⟨n, σ⟩
  have hd : ((n : ℂ) * (Module.finrank ℚ K : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  let z : ℂ := -GlobalTheory.ResW.cex x / ((n : ℂ) * (Module.finrank ℚ K : ℂ))
  let χ : HChar K := Model.absC K z
  have hspec := (GlobalTheory.ResW.letter_centralExponent K x).1
  have htr : (Matrix.of (oneL K n)).trace = (n : ℝ) • (1 : Cinf K) := by
    change (Matrix.of (fun i j : Fin n => if i = j then (1 : Cinf K) else 0)).trace = _
    simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
  have hz : ∀ φ ∈ (σ.twist χ).V, lie K n (oneL K n) φ = 0 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have e0 : lie K n (oneL K n) ψ = GlobalTheory.ResW.cex x • ψ := hspec ψ hψ
    have e1 : dchi χ (Matrix.of (oneL K n)).trace = -GlobalTheory.ResW.cex x := by
      rw [htr, map_smul, GlobalTheory.ResW.dchi_absC_one_finrank]
      have hzd : z * ((n : ℂ) * (Module.finrank ℚ K : ℂ)) = -GlobalTheory.ResW.cex x := div_mul_cancel₀ _ hd
      simp only [Complex.real_smul, Complex.ofReal_natCast]
      linear_combination hzd
    change lie K n (oneL K n) (mulChi n χ ψ) = 0
    rw [lie_mulChi, e0, e1, ← add_smul, add_neg_cancel, zero_smul, map_zero]
  have hval : ∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z) := fun v => by
    refine ⟨fun y hy => Units.ext ?_, ?_⟩
    · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v y)) = 1
      rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v y 0 (by simpa [IsUnitAt] using hy)]; simp
    · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v (atFin v (unif v)))) = _
      have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
      rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
        ← Complex.natCast_log]
      congr 1; push_cast; ring
  have hex : ∀ v, ∃ s', v ∈ S → SuppAt (σ.twist χ) v s' ∧ cnt s' 1 = cnt (s v) 1 := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨s', h1, h2, -⟩ := (hF K n (by omega) σ v).2.2.2.2 χ (s v) (hs v hv).1
      refine ⟨s', fun _ => ⟨h1, ?_⟩⟩
      rw [h2, mul_one, cnt_unram _ (unram_loc (hval v).1)]
    · exact ⟨0, fun h => absurd h hv⟩
  choose s' hs' using hex
  obtain ⟨β, P, hβ, hP0, hdeg, hP⟩ := hC K n hn (σ.twist χ) (Cm.carrier_le_central _ hz) S hS
    (fun w => (B w).map (· * χ.val w)) (fun w hw => by
      have h := (hB w hw).twist (hval w).1
      rwa [CG.twist_mk] at h) s' q f hq
    (fun v hv => ⟨(hs' v hv).1, fun h => (hs v hv).2 (by rwa [← (hs' v hv).2])⟩)
  have hP2 := hO.2.2.2 _ _ _ _ _ z (by exact_mod_cast hq) hP
  have e : ∀ w, cx (fun w => (B w).map (· * χ.val w)) w =
      (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z) := fun w => by
    simp only [cx, Multiset.map_map, Function.comp_def, Units.val_mul, (hval w).2]
  have e' : cx (fun w => (B w).map (· * χ.val w)) =
      fun w => (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z) := funext e
  rw [e'] at hP2
  have hqz : (((q : ℝ) : ℂ) ^ z) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    have : q = 0 := by exact_mod_cast h
    omega
  refine ⟨β.comp (X - C z), P.comp (C (((q : ℝ) : ℂ) ^ z) * X), ?_, ?_, ?_, ?_⟩
  · intro h
    apply hβ
    have := congrArg (fun p => p.comp (X + C z)) h
    simpa [comp_assoc] using this
  · simp [eval_comp, hP0]
  · rw [natDegree_comp, natDegree_C_mul_X _ hqz, mul_one, hdeg]
    exact Finset.sum_congr rfl fun v hv => by rw [(hs' v hv).2]
  · simpa only [euler_shift, eulerd_shift] using hP2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.IndTorOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

private theorem reps {α : Type*} (r : α → α → Prop) (hr : Equivalence r) (A : Finset α) :
    ∃ T : Finset α, T ⊆ A ∧ (∀ t ∈ T, ∀ t' ∈ T, r t t' → t = t') ∧ ∀ a ∈ A, ∃ t ∈ T, r a t :=
  _root_.UpperTheory.Reformulated.B.Qh68.reps r hr A

private theorem swapc {α ι : Type*} (I : Finset ι) (p : ι → α → Prop) (s : Multiset α) :
    ∑ i ∈ I, (s.filter (p i)).card = (s.map fun y => (I.filter fun i => p i y).card).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ← ih, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Multiset.filter_cons, Multiset.card_add]
    split_ifs <;> simp

private theorem allone {α : Type*} (d g : α → ℕ) (F : ℕ) (hF : 0 < F) (s : Multiset α) (hpos : ∀ y ∈ s, 0 < d y)
    (hg : ∀ y ∈ s, g y ≤ F ∧ (d y ≠ 1 → g y = 0)) (h : F * (s.map d).sum ≤ (s.map g).sum) : ∀ y ∈ s, d y = 1 := by
  intro y hy
  by_contra hne
  have hlt : (s.map g).sum < (s.map fun y => F * d y).sum := by
    refine Multiset.sum_lt_sum (fun z hz => (hg z hz).1.trans (Nat.le_mul_of_pos_right _ (hpos z hz))) ⟨y, hy, ?_⟩
    rw [(hg y hy).2 hne]
    exact Nat.mul_pos hF (hpos y hy)
  rw [Multiset.sum_map_mul_left] at hlt
  omega

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem unr_of {a b c : kˣ →* ℂˣ} (ha : IsUnram a) (hb : IsUnram b) (h : ∀ x, a x = 1 → b x = 1 → c x = 1) :
    IsUnram c := fun x hx => h x (ha x hx) (hb x hx)

end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

private theorem sum_right (N : k'ˣ →* kˣ) (T : Finset (kˣ →* ℂˣ)) (s : Multiset (IrrGL (k := k')))
    (h2 : ∀ t ∈ T, ∀ t' ∈ T, IsUnram ((t * t'⁻¹).comp N) → t = t')
    (h3 : ∀ y ∈ s, ∃ ζ hζ, y = IrrGL.ofChar ζ hζ ∧ ∃ t ∈ T, IsUnram (ζ * t.comp N)) :
    ∑ t ∈ T, cnt s (t.comp N) = s.card := by
  unfold cnt
  rw [swapc T (fun t y => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * t.comp N)) s]
  rw [Multiset.map_congr rfl (g := fun _ => 1) fun y hy => ?_]
  · simp
  obtain ⟨ζ, hζ, rfl, t, ht, e⟩ := h3 y hy
  refine Finset.card_eq_one.2 ⟨t, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨ht, ζ, hζ, rfl, e⟩, fun t' ht' => ?_⟩⟩
  obtain ⟨ht', ξ, hξ, e1, e2⟩ := Finset.mem_filter.1 ht'
  obtain rfl := IrrGL.ofChar_inj.1 e1
  refine h2 t' ht' t ht (unr_of e2 e fun x a b => ?_)
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply] at a b ⊢
  rw [mul_inv_eq_one]
  exact mul_left_cancel (a.trans b.symm)

private theorem left_le (N : k'ˣ →* kˣ) (T : Finset (kˣ →* ℂˣ)) (J : Finset ℕ) (e : ℕ → (kˣ →* ℂˣ)) (F : ℕ)
    (hT : ∀ t ∈ T, IsSmoothChar t) (he : ∀ j, IsSmoothChar (e j)) (heN : ∀ j x, e j (N x) = 1)
    (h2 : ∀ t ∈ T, ∀ t' ∈ T, IsUnram ((t * t'⁻¹).comp N) → t = t')
    (hup : ∀ θ : kˣ →* ℂˣ, IsSmoothChar θ → IsUnram θ → IsUnram (θ.comp N))
    (hF : ∀ θ : kˣ →* ℂˣ, IsSmoothChar θ → IsUnram (θ.comp N) → (J.filter fun j => IsUnram (θ * e j)).card = F)
    (y : IrrGL (k := k)) :
    ((T ×ˢ J).filter fun p => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (p.1 * e p.2))).card ≤ F := by
  rcases Finset.eq_empty_or_nonempty
    ((T ×ˢ J).filter fun p => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (p.1 * e p.2))) with h | ⟨p, hp⟩
  · rw [h]; exact Nat.zero_le _
  obtain ⟨hp0, ξ, hξ, rfl, hu⟩ := Finset.mem_filter.1 hp
  have key : ∀ t ∈ T, ∀ j, IsUnram (ξ * (t * e j)) → IsUnram ((ξ * t).comp N) := fun t ht j h => by
    have := hup _ (hξ.mul ((hT t ht).mul (he j))) h
    refine unr_of this this fun x a _ => ?_
    simpa only [MonoidHom.mul_apply, MonoidHom.comp_apply, heN, mul_one] using a
  have hp1 := (Finset.mem_product.1 hp0).1
  have k1 := key p.1 hp1 p.2 hu
  rw [← hF _ (hξ.mul (hT _ hp1)) k1]
  have hall : ∀ q ∈ ((T ×ˢ J).filter fun p => ∃ ξ' hξ', IrrGL.ofChar ξ hξ = IrrGL.ofChar ξ' hξ' ∧
      IsUnram (ξ' * (p.1 * e p.2))), q.1 = p.1 ∧ q.2 ∈ J ∧ IsUnram (ξ * p.1 * e q.2) := fun q hq => by
    obtain ⟨hq, ξ', hξ', e1, e2⟩ := Finset.mem_filter.1 hq
    obtain rfl := IrrGL.ofChar_inj.1 e1
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
    have : q.1 = p.1 := by
      refine h2 _ hq1 _ hp1 (unr_of (key _ hq1 _ e2) k1 fun x a b => ?_)
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply] at a b ⊢
      rw [mul_inv_eq_one]
      exact mul_left_cancel (a.trans b.symm)
    exact ⟨this, hq2, by rw [mul_assoc, ← this]; exact e2⟩
  refine Finset.card_le_card_of_injOn Prod.snd (fun q hq => ?_) fun q hq q' hq' h => ?_
  · exact Finset.mem_coe.2 (Finset.mem_filter.2 (hall q hq).2)
  · exact Prod.ext ((hall q hq).1.trans (hall q' hq').1.symm) h

private theorem unr_equiv (N : k'ˣ →* kˣ) : Equivalence fun t t' : kˣ →* ℂˣ => IsUnram ((t * t'⁻¹).comp N) := by
  refine ⟨fun t x _ => by simp, fun h => unr_of h h fun x a _ => ?_, fun h h' => unr_of h h' fun x a b => ?_⟩
  · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, mul_inv_eq_one] at a ⊢
    exact a.symm
  · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, mul_inv_eq_one] at a b ⊢
    exact a.trans b

end

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.indTorOf :
    UpperTheory.V.Z.Gam.IndTorOf := by
  intro hS hN hM K M _ _ _ _ _ _ _ hKM P π hI v hv
  haveI : Algebra.IsQuadraticExtension K M := ⟨hKM⟩
  obtain ⟨η, -, hη⟩ := hN K M (hKM ▸ Nat.prime_two)
  obtain ⟨w₀⟩ : Nonempty (PlacesOver M v) := (placesOverEquiv M v).nonempty_congr.2 inferInstance
  obtain ⟨⟨s, hs⟩, -, h3, -⟩ := hS K (2 * 2) (by norm_num) P v
  obtain ⟨hiff, hsum, hpos⟩ := h3 s hs
  choose s' hs' using fun w : PlacesOver M v => (hS M 2 (by norm_num) π w.1).1
  have hone : ∀ w, ∀ y ∈ s' w, y.1 = 1 := fun w =>
    ((hS M 2 (by norm_num) π w.1).2.2.1 _ (hs' w)).1.1 (hv w).1
  have hcard : ∀ w, (s' w).card = 2 := fun w => by
    have := ((hS M 2 (by norm_num) π w.1).2.2.1 _ (hs' w)).2.1
    rw [Multiset.map_congr rfl (g := fun _ => 1) (hone w)] at this
    simpa using this
  have hχ : ∀ (w : PlacesOver M v) (y : IrrGL (k := w.1.adicCompletion M)), ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      IsSmoothChar χ ∧ (y ∈ s' w → ∃ ζ hζ, y = IrrGL.ofChar ζ hζ ∧ IsUnram (ζ * χ.comp (nm w))) := fun w y => by
    by_cases hy : y ∈ s' w
    · obtain ⟨ζ, hζ, rfl⟩ := TemperedTests.exists_eq_ofChar y (hone w y hy)
      obtain ⟨χ, h1, h2⟩ := (hv w).2 _ (hs' w) ζ hζ hy
      exact ⟨χ, h1, fun _ => ⟨ζ, hζ, rfl, h2⟩⟩
    · exact ⟨1, isSmoothChar_one, fun h => absurd h hy⟩
  choose χ hχs hχ using hχ
  obtain ⟨T, hT1, hT2, hT3⟩ := reps _ (unr_equiv (nm w₀))
    (Finset.univ.biUnion fun w : PlacesOver M v => (s' w).toFinset.image (χ w))
  have hT : ∀ t ∈ T, IsSmoothChar t := fun t ht => by
    obtain ⟨w, -, h⟩ := Finset.mem_biUnion.1 (hT1 ht)
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 h
    exact hχs w y
  have hR : ∀ w, ∑ t ∈ T, cnt (s' w) (t.comp (nm w)) = 2 := fun w => by
    rw [← hcard w]
    refine sum_right (nm w) T (s' w) (fun t ht t' ht' h => hT2 t ht t' ht' ((hη v w).2.1 w₀ _ h)) fun y hy => ?_
    obtain ⟨ζ, hζ, e, hu⟩ := hχ w y hy
    obtain ⟨t, ht, h⟩ := hT3 (χ w y) (Finset.mem_biUnion.2 ⟨w, Finset.mem_univ _,
      Finset.mem_image.2 ⟨y, Multiset.mem_toFinset.2 hy, rfl⟩⟩)
    refine ⟨ζ, hζ, e, t, ht, unr_of hu ((hη v w₀).2.1 w _ h) fun x a b => ?_⟩
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, mul_inv_eq_one] at a b ⊢
    rw [← b]; exact a
  have heN : ∀ (w : PlacesOver M v) (j : ℕ) x, (η ^ j).loc v (nm w x) = 1 := fun w j x => by
    have : η.loc v (nm w x) = 1 := DFunLike.congr_fun (hη v w).1 x
    show η.loc v (nm w x) ^ j = 1
    rw [this, one_pow]
  have hF : 0 < ∑ w : PlacesOver M v, fdeg w := by
    rw [← ((hη v w₀).2.2 1 isSmoothChar_one).2.2 (fun x _ => rfl)]
    exact Finset.card_pos.2 ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), fun x _ => by
      show (1 : ℂˣ) * η.loc v x ^ 0 = 1
      simp⟩⟩
  have htot : ∑ p ∈ T ×ˢ Finset.range (Module.finrank K M), cnt s (p.1 * (η ^ p.2).loc v) =
      (∑ w : PlacesOver M v, fdeg w) * (2 * 2) := by
    have h1 : ∀ p ∈ T ×ˢ Finset.range (Module.finrank K M), cnt s (p.1 * (η ^ p.2).loc v) =
        ∑ w : PlacesOver M v, fdeg w * cnt (s' w) (p.1.comp (nm w)) := fun p hp => by
      rw [hM K M hKM P π hI v s s' hs hs' _ ((hT _ (Finset.mem_product.1 hp).1).mul (ParLaws.isSmoothChar_loc _ v))]
      refine Finset.sum_congr rfl fun w _ => ?_
      congr 2
      ext x
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, heN, mul_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_product_right]
    simp only [Finset.sum_const, Finset.card_range, hKM, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hR, ← Finset.sum_mul]
    ring
  unfold cnt at htot
  rw [swapc _ (fun (p : ((v.adicCompletion K)ˣ →* ℂˣ) × ℕ) y =>
    ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (p.1 * (η ^ p.2).loc v))) s, ← hsum] at htot
  refine hiff.2 (allone Sigma.fst _ _ hF s hpos (fun y _ => ⟨?_, fun hy => ?_⟩) htot.ge)
  · exact left_le (nm w₀) T _ (fun j => (η ^ j).loc v) _ hT (fun j => ParLaws.isSmoothChar_loc _ v) (heN w₀) hT2
      (fun θ h => ((hη v w₀).2.2 θ h).2.1) (fun θ h => ((hη v w₀).2.2 θ h).2.2) y
  · refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun p _ => ?_)
    rintro ⟨ξ, hξ, rfl, -⟩
    exact hy rfl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.UpDownOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

private theorem count_cls {Y T : Type*} (E : T → T → Prop) (hE : ∀ t, E t t) (R : Y → T → Prop)
    (hR : ∀ y t, R y t → ∀ t', R y t' ↔ E t t') (s : Multiset Y) (t : T) :
    ((s.filter fun y => ∃ t, R y t).map fun y => {t | R y t}).count {t' | E t t'} = (s.filter fun y => R y t).card := by
  rw [Multiset.count_map, Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun y _ => ⟨fun h => ?_, fun h => ⟨?_, t, h⟩⟩
  · have : t ∈ {t' | E t t'} := hE t
    rw [h.1] at this
    exact this
  · exact Set.ext fun t' => (hR y t h t').symm

private theorem count_ncls {Y T : Type*} (E : T → T → Prop) (R : Y → T → Prop)
    (hR : ∀ y t, R y t → ∀ t', R y t' ↔ E t t') (s : Multiset Y) (S : Set T) (hS : ¬ ∃ t, S = {t' | E t t'}) :
    ((s.filter fun y => ∃ t, R y t).map fun y => {t | R y t}).count S = 0 := by
  rw [Multiset.count_eq_zero]
  intro h
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 h
  obtain ⟨t, ht⟩ := (Multiset.mem_filter.1 hy).2
  exact hS ⟨t, Set.ext fun t' => hR y t ht t'⟩

private theorem total {Y T ι : Type*} [Fintype ι] {Y' : ι → Type*} (E : T → T → Prop) (hE : ∀ t, E t t)
    (R : Y → T → Prop) (hR : ∀ y t, R y t → ∀ t', R y t' ↔ E t t')
    (R' : ∀ i, Y' i → T → Prop) (hR' : ∀ i y t, R' i y t → ∀ t', R' i y t' ↔ E t t')
    (s : Multiset Y) (s' : ∀ i, Multiset (Y' i)) (F : ℕ) (f : ι → ℕ)
    (h : ∀ t, F * (s.filter fun y => R y t).card = ∑ i, f i * ((s' i).filter fun y => R' i y t).card) :
    F * (s.filter fun y => ∃ t, R y t).card = ∑ i, f i * ((s' i).filter fun y => ∃ t, R' i y t).card := by
  have key : F • ((s.filter fun y => ∃ t, R y t).map fun y => {t | R y t}) =
      ∑ i, f i • (((s' i).filter fun y => ∃ t, R' i y t).map fun y => {t | R' i y t}) := by
    ext S
    rw [Multiset.count_sum']
    simp only [Multiset.count_nsmul]
    by_cases hS : ∃ t, S = {t' | E t t'}
    · obtain ⟨t, rfl⟩ := hS
      rw [count_cls E hE R hR, h t]
      exact Finset.sum_congr rfl fun i _ => by rw [count_cls E hE (R' i) (hR' i)]
    · rw [count_ncls E R hR s S hS, mul_zero]
      exact (Finset.sum_eq_zero fun i _ => by rw [count_ncls E (R' i) (hR' i) _ S hS, mul_zero]).symm
  have := congrArg Multiset.card key
  simpa [Multiset.card_sum, Multiset.card_nsmul] using this

private theorem card_le_sum {s : Multiset ℕ} (h : ∀ y ∈ s, 0 < y) : s.card ≤ s.sum := by
  simpa using Multiset.card_nsmul_le_sum (a := 1) h

private theorem sum_card_filter {Y : Type*} (s : Multiset Y) (d F : ℕ) (A : Y → ℕ → Prop) (B : Y → Prop)
    (h1 : ∀ y, B y → ((Finset.range d).filter (A y)).card = F) (h2 : ∀ y j, A y j → B y) :
    ∑ j ∈ Finset.range d, (s.filter fun y => A y j).card = F * (s.filter B).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons y s ih =>
    simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib, ih, mul_add]
    congr 1
    by_cases hB : B y
    · rw [← h1 y hB, Finset.card_filter, if_pos hB, Multiset.card_singleton, mul_one]
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    · rw [if_neg hB]
      exact Finset.sum_eq_zero fun j _ => by rw [if_neg fun hA => hB (h2 y j hA)]; simp

private theorem loc_pow {K : Type} [Field K] [NumberField K] (η : HChar K) (j : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (η ^ j).loc v = η.loc v ^ j := by
  ext1 x
  show (η ^ j).1 _ = η.1 _ ^ j
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem cls_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ζ a b : kˣ →* ℂˣ} (h : IsUnram (ζ * a)) : IsUnram (ζ * b) ↔ IsUnram (a⁻¹ * b) := by
  constructor
  · intro h'
    have := isUnram_mul (isUnram_inv h) h'
    rwa [show (ζ * a)⁻¹ * (ζ * b) = a⁻¹ * b by rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]] at this
  · intro h'
    have := isUnram_mul h h'
    rwa [mul_assoc, mul_inv_cancel_left] at this

private theorem all_of_le {Y : Type*} {s : Multiset Y} {p : Y → Prop} (h : s.card ≤ (s.filter p).card) :
    ∀ y ∈ s, p y :=
  Multiset.filter_eq_self.1 (Multiset.eq_of_le_of_card_le (Multiset.filter_le p s) h)

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.upDownOf :
    UpperTheory.V.Z.Gam.UpDownOf := by
  intro hS hN hM K L _ _ _ _ _ _ _ _ hp n hn π P hBC v
  obtain ⟨η, hη, hloc⟩ := hN K L hp
  have hSK := hS K n (by omega) π v
  have hSL := fun w : PlacesOver L v => hS L n (by omega) P w.1
  obtain ⟨s, hs⟩ := hSK.1
  choose s' hs' using fun w => (hSL w).1
  obtain ⟨w₀⟩ : Nonempty (PlacesOver L v) :=
    ⟨(placesOverEquiv L v).symm (Classical.choice (Ideal.nonempty_primesOver v.asIdeal))⟩
  have hf : ∀ w : PlacesOver L v, 0 < fdeg w := fun w => Ideal.inertiaDeg'_pos _ _
  have hcs : s.card ≤ n := by
    obtain ⟨-, h1, h2⟩ := hSK.2.2.1 s hs
    rw [← h1, ← Multiset.card_map Sigma.fst s]
    exact card_le_sum fun d hd => by obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hd; exact h2 y hy
  have hcs' : ∀ w, (s' w).card ≤ n := fun w => by
    obtain ⟨-, h1, h2⟩ := (hSL w).2.2.1 _ (hs' w)
    rw [← h1, ← Multiset.card_map Sigma.fst (s' w)]
    exact card_le_sum fun d hd => by obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hd; exact h2 y hy
  have key := total (T := {θ : (v.adicCompletion K)ˣ →* ℂˣ // IsSmoothChar θ})
    (fun a b => IsUnram ((a.1⁻¹ * b.1).comp (nm w₀))) (fun a x _ => by simp)
    (fun y t => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram ((ξ * t.1).comp (nm w₀)))
    (by
      rintro y t ⟨ξ, hξ, rfl, h⟩ t'
      refine Iff.trans ⟨?_, fun h' => ⟨ξ, hξ, rfl, h'⟩⟩
        (cls_iff (ζ := ξ.comp (nm w₀)) (a := t.1.comp (nm w₀)) (b := t'.1.comp (nm w₀)) h)
      rintro ⟨ξ', hξ', e, h'⟩
      obtain rfl := IrrGL.ofChar_inj.1 e
      exact h')
    (fun (w : PlacesOver L v) y t => ∃ ζ hζ, y = IrrGL.ofChar ζ hζ ∧ IsUnram (ζ * t.1.comp (nm w)))
    (by
      rintro w y t ⟨ζ, hζ, rfl, h⟩ t'
      refine Iff.trans ⟨?_, fun h' => ⟨ζ, hζ, rfl, h'⟩⟩ ((cls_iff (b := t'.1.comp (nm w)) h).trans
        ⟨(hloc v w).2.1 w₀ (t.1⁻¹ * t'.1), (hloc v w₀).2.1 w (t.1⁻¹ * t'.1)⟩)
      rintro ⟨ξ', hξ', e, h'⟩
      obtain rfl := IrrGL.ofChar_inj.1 e
      exact h')
    s s' (∑ w : PlacesOver L v, fdeg w) (fun w => fdeg w) (fun t => by
      refine Eq.trans ?_ (hM K L hp n hn π P hBC η hη v s s' hs hs' t.1 t.2)
      symm
      refine sum_card_filter s _ _
        (fun y j => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (t.1 * (η ^ j).loc v))) _ ?_ ?_
      · rintro y ⟨ξ, hξ, rfl, h⟩
        rw [← ((hloc v w₀).2.2 (ξ * t.1) (hξ.mul t.2)).2.2 h]
        congr 1
        refine Finset.filter_congr fun j _ => ⟨?_, fun h' => ⟨ξ, hξ, rfl, by rwa [← mul_assoc]⟩⟩
        rintro ⟨ξ', hξ', e, h'⟩
        obtain rfl := IrrGL.ofChar_inj.1 e
        rwa [mul_assoc]
      · rintro y j ⟨ξ, hξ, rfl, h⟩
        refine ⟨ξ, hξ, rfl, fun x hx => ?_⟩
        have h1 := ((hloc v w₀).2.2 _ (isSmoothChar_of_isUnram h)).2.1 h x hx
        have h2 : η.loc v (nm w₀ x) = 1 := DFunLike.congr_fun (hloc v w₀).1 x
        simpa [loc_pow, h2] using h1)
  constructor
  · intro hT w
    have h1 := (hSK.2.2.1 s hs).1.1 hT
    have hn' : s.card = n := by
      rw [← (hSK.2.2.1 s hs).2.1, Multiset.map_congr rfl h1]; simp
    rw [Multiset.filter_eq_self.2 fun y hy => by
      obtain ⟨ξ, hξ, rfl⟩ := GlobalTheory.LocGL.TemperedTests.exists_eq_ofChar y (h1 y hy)
      exact ⟨⟨ξ⁻¹, hξ.inv⟩, ξ, hξ, rfl, fun x _ => by simp⟩, hn', Finset.sum_mul] at key
    have h2 := (Finset.sum_eq_sum_iff_of_le fun w _ => Nat.mul_le_mul_left _
      ((Multiset.card_le_card (Multiset.filter_le _ _)).trans (hcs' w))).1 key.symm w (Finset.mem_univ w)
    have h3 := all_of_le ((hcs' w).trans (Nat.eq_of_mul_eq_mul_left (hf w) h2).ge)
    refine ⟨((hSL w).2.2.1 _ (hs' w)).1.2 fun y hy => ?_, fun r hr ζ hζ hm => ?_⟩
    · obtain ⟨t, ζ, hζ, rfl, -⟩ := h3 y hy
      rfl
    · obtain rfl := (hSL w).2.1 _ _ (hs' w) hr
      obtain ⟨t, ζ', hζ', e, h⟩ := h3 _ hm
      obtain rfl := IrrGL.ofChar_inj.1 e
      exact ⟨t.1, t.2, h⟩
  · intro hT
    have h1 := fun w => ((hSL w).2.2.1 _ (hs' w)).1.1 (hT w).1
    have hn' : ∀ w, (s' w).card = n := fun w => by
      rw [← ((hSL w).2.2.1 _ (hs' w)).2.1, Multiset.map_congr rfl (h1 w)]; simp
    replace key := key.trans (Finset.sum_congr (g := fun w : PlacesOver L v => fdeg w * n) rfl fun w _ => by
      rw [Multiset.filter_eq_self.2 fun y hy => by
        obtain ⟨ζ, hζ, rfl⟩ := GlobalTheory.LocGL.TemperedTests.exists_eq_ofChar y (h1 w y hy)
        obtain ⟨χ, hχ, h⟩ := (hT w).2 _ (hs' w) ζ hζ hy
        exact ⟨⟨χ, hχ⟩, ζ, hζ, rfl, h⟩, hn' w])
    rw [← Finset.sum_mul] at key
    have hF : 0 < ∑ w : PlacesOver L v, fdeg w := Finset.sum_pos (fun w _ => hf w) ⟨w₀, Finset.mem_univ _⟩
    have h3 := all_of_le (hcs.trans (Nat.eq_of_mul_eq_mul_left hF key).ge)
    refine (hSK.2.2.1 s hs).1.2 fun y hy => ?_
    obtain ⟨t, ζ, hζ, rfl, -⟩ := h3 y hy
    rfl
end
end

namespace UpperTheory.V.Z.Gam

theorem crossG : CrossG := crossGOf Inf.expAlg Inf.expIndep secDiff

theorem sideG : SideG := sideGOf pairGOps suppFacts (sideGCenOf (gamLocOf leviDiv coefInd suppBridge) locIso)

theorem upDown : UpDown := upDownOf suppFacts normCnt (matchBCOf pairGOps crossG sideG suppFacts normLoc globTw regroupBC)

theorem indTor : IndTor := indTorOf suppFacts normCnt (matchIndOf pairGOps crossG sideG suppFacts normLoc globTw)

end UpperTheory.V.Z.Gam
