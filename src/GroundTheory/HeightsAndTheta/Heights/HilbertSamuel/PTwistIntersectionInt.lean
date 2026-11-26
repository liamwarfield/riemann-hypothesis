module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersectionInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace TwistIntersectionInt

theorem proof (hPc : EmbeddingPieces.Statement) (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    TwistIntersectionInt.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D A B II Λ _ hII hP hbir hA hBa hB hΛ hex hloc
  classical
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  have hC : IsSmoothHerm (A.tensor B) := hA.mul hB
  have hopen : IsOpen {u : (Σ k, ι k) → ℂ | ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hCloc : ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((A.tensor B).h u) = Real.log (A.h u) + c := by
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    refine ⟨Real.log (Λ sg), ?_⟩
    filter_upwards [hloc z hz sg hsg, hopen.mem_nhds hz.1] with u hu hu'
    show Real.log (A.h u * B.h u) = _
    rw [hu, Real.log_mul (A.pos u hu').ne' (hΛ sg).ne']
  let L : Finset (Fin (D + 1)) → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun S i => if i ∈ S then A.tensor B else A
  have hLs : ∀ S i, IsSmoothHerm (L S i) := by
    intro S i
    dsimp only [L]
    split_ifs
    exacts [hC, hA]
  have hLpot : ∀ S i, ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((L S i).h u) = Real.log (A.h u) + c := by
    intro S i z hz
    dsimp only [L]
    split_ifs
    · exact hCloc z hz
    · exact ⟨0, Eventually.of_forall fun u => by rw [add_zero]⟩
  have step : ∀ (S : Finset (Fin (D + 1))) (j : Fin (D + 1)), j ∉ S →
      II K ι (mCoordIdeal y) (D + 1) (L (insert j S)) = II K ι (mCoordIdeal y) (D + 1) (L S) +
        -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S j hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := Fin.init (L S ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (insert j S) ∘ σ) = M := by
      funext i
      simp only [hMdef, Fin.init, Function.comp, L, Finset.mem_insert, hne i, false_or]
    have e0 : L S ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L S ∘ σ)
      have hl : (L S ∘ σ) (Fin.last D) = A := by simp [L, hσl, hj]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (insert j S) ∘ σ = Fin.snoc M (A.tensor B) := by
      have h0 := Fin.snoc_init_self (q := L (insert j S) ∘ σ)
      have hl : (L (insert j S) ∘ σ) (Fin.last D) = A.tensor B := by simp [L, hσl]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs S _
    have hint : ptsIntegral (mCoordIdeal y) (pot M) (logNorm B 1) =
        ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) :=
      TwistIntersection.ptsIntegral_add_locConst _ (fun i z hz => hLpot S (σ (Fin.castSucc i)) z hz) _
    rw [← hI.1 _ (D + 1) (L (insert j S)) σ hP (hLs _), ← hI.1 _ (D + 1) (L S) σ hP (hLs S), e0, e1,
      hI.2.1 _ D M A B hP hMs hA hB, TwistIntersection.I_snoc_degZero hI hP hMs hB hBa, hint]
  have hall : ∀ S : Finset (Fin (D + 1)), II K ι (mCoordIdeal y) (D + 1) (L S) =
      II K ι (mCoordIdeal y) (D + 1) (L ∅) +
        S.card * -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S
    refine Finset.induction_on S (by simp) ?_
    intro j S hj ih
    rw [step S j hj, ih, Finset.card_insert_of_notMem hj]
    push_cast
    ring
  have hL0 : L ∅ = fun _ => A := by
    funext i
    simp [L]
  have hLu : L Finset.univ = fun _ => A.tensor B := by
    funext i
    simp [L]
  have hw : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      logNorm B 1 =ᶠ[𝓝 z] fun _ => (fun sg => -Real.log (Λ sg)) sg := by
    intro z hz sg hsg
    filter_upwards [hloc z hz sg hsg] with u hu
    simp [logNorm, hu, Real.log_inv]
  have hpc := hPc K ι Ω F y D (fun _ => A) (fun sg => -Real.log (Λ sg)) (logNorm B 1) hP hbir
    (fun _ => hA) hex hw
  have hg : ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (fun _ => 1) =
      (genDeg (mCoordIdeal y) D A.a : ℝ) := by
    rw [hDG K ι (mCoordIdeal y) D (fun _ => A) hP (fun _ => hA)]
    unfold genDeg
    congr
  have := hall Finset.univ
  rw [hL0, hLu, Finset.card_univ, Fintype.card_fin] at this
  rw [this, hpc, hg, Finset.sum_neg_distrib]
  push_cast
  ring

end TwistIntersectionInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentsMeetNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ComponentsMeetNull.proof (hA : ChartDimLt.Statement) (hB : ChartRatioImageNull.Statement) :
    ComponentsMeetNull.Statement := by
  classical
  intro K _ ι _ P e Ψ S hP _ hS
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC

  have hdimW : ∀ W ∈ PC.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ W) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
    have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
    have : PQ.IsPrime := hvar.1.isPrime
    have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
      rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
      congr 1
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
      · simp only [RingHom.comp_apply, MvPolynomial.map_C]
        congr 1
      · simp
    intro W hW
    rw [← hext] at hW
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ W hW]
    exact hvar.2

  have hPCh : IsMultiHomogIdeal PC := by
    obtain ⟨T, hT, hPT⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [hPC, hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩
  have hWh : ∀ W ∈ PC.minimalPrimes, IsMultiHomogIdeal W := fun W hW =>
    (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp
      (GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimeMultiHomog.proof ℂ K ι PC W
        ((GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff PC).mpr hPCh) hW)
  have hsuph : ∀ W ∈ PC.minimalPrimes, ∀ W' ∈ PC.minimalPrimes, IsMultiHomogIdeal (W ⊔ W') := by
    intro W hW W' hW'
    obtain ⟨T, hT, rfl⟩ := hWh W hW
    obtain ⟨T', hT', rfl⟩ := hWh W' hW'
    exact ⟨T ∪ T', fun f hf => hf.elim (hT f) (hT' f), (Ideal.span_union T T').symm⟩

  have hsup : ∀ W ∈ PC.minimalPrimes, ∀ W' ∈ PC.minimalPrimes, W ≠ W' →
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ W')) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro W hW W' hW' hne
    have : W.IsPrime := hW.1.1
    obtain ⟨g, hgW', hgW⟩ : ∃ g ∈ W', g ∉ W := by
      by_contra hcon
      push_neg at hcon
      exact hne (le_antisymm (hW.2 hW'.1 hcon) hcon)
    have hg0 : Ideal.Quotient.mk W g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hg0)
    have eqv : ((MvPolynomial (Σ k, ι k) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W g}) ≃+*
        MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ Ideal.span {g}) :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
        (DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {g}))
    rw [ringKrullDim_eq_of_ringEquiv eqv, hdimW W hW] at h1
    have hle : W ⊔ Ideal.span {g} ≤ W ⊔ W' :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hgW') W
    have h2 := ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ Ideal.span {g})) = a at h1 h2
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ W')) = b at h2 ⊢
    refine lt_of_le_of_lt h2 ?_
    induction a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h1 (by exact_mod_cast (show ¬ ((⊤ : ℕ∞) + 1 ≤ ((e + Fintype.card K : ℕ) : ℕ∞)) by simp))
      | coe a =>
        have : a + 1 ≤ e + Fintype.card K := by exact_mod_cast h1
        exact_mod_cast (show a < e + Fintype.card K by omega)

  refine measure_mono_null (t := ⋃ W ∈ (S : Set _), ⋃ W' ∈ (S : Set _), ⋃ (_ : W ≠ W'), ⋃ p : (k : K) → ι k,
      {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal (W ⊔ W') p), Ψ (segre z) 0 ≠ 0 ∧
        (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)}) ?_ ?_
  · rintro y ⟨z, hz, hzy, W, hWS, W', hW'S, hne, hzW, hzW'⟩
    choose p hp using hz.1
    simp only [Set.mem_iUnion, Finset.mem_coe]
    refine ⟨W, hWS, W', hW'S, hne, p, ReciprocityTheory.AnForm.R.affCoord p z, ?_, ?_⟩
    · have hcone : z ∈ ReciprocityTheory.AnForm.R.conePts (W ⊔ W') := by
        refine ⟨hz.1, fun f hf => ?_⟩
        have hker : W ⊔ W' ≤ RingHom.ker (eval z) := sup_le
          (fun f hf => RingHom.mem_ker.mpr (by simpa [MvPolynomial.coe_aeval_eq_eval] using hzW f hf))
          (fun f hf => RingHom.mem_ker.mpr (by simpa [MvPolynomial.coe_aeval_eq_eval] using hzW' f hf))
        exact RingHom.mem_ker.mp (hker hf)
      have h := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal
        (hsuph W (hS W hWS) W' (hS W' hW'S)) p z hp).1 hcone
      intro f hf
      have hf' := h f hf
      rwa [← MvPolynomial.coe_aeval_eq_eval] at hf'
    · have hc : (∏ k, z ⟨k, p k⟩)⁻¹ ≠ 0 := inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => hp k)
      have hseg : segre (ReciprocityTheory.AnForm.R.affCoord p z) = (∏ k, z ⟨k, p k⟩)⁻¹ • segre z := by
        funext i
        simp only [segre, ReciprocityTheory.AnForm.R.affCoord, Pi.smul_apply, smul_eq_mul, Finset.prod_div_distrib]
        rw [div_eq_inv_mul]
      have hΨ : Ψ (segre (ReciprocityTheory.AnForm.R.affCoord p z)) =
          (∏ k, z ⟨k, p k⟩)⁻¹ • (Fin.cons 1 y : Fin (e + 1) → ℂ) := by
        rw [hseg, map_smul, hzy]
      rw [hΨ, Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
      exact ⟨hc, rfl⟩
  · refine (measure_biUnion_null_iff S.countable_toSet).2 fun W hW => ?_
    refine (measure_biUnion_null_iff S.countable_toSet).2 fun W' hW' => ?_
    refine measure_iUnion_null fun hne => measure_iUnion_null fun p => ?_
    exact hB K ι _ e Ψ (hA K ι (W ⊔ W') e p (hsuph W (hS W hW) W' (hS W' hW'))
      (hsup W (hS W hW) W' (hS W' hW') hne))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartRatioImageNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

theorem ChartRatioImageNull.volume_eq_zero_of_dimH_lt {e : ℕ} {S : Set (Fin e → ℂ)}
    (hS : dimH S < 2 * (e : ℝ≥0∞)) : volume S = 0 := by
  let E : ((Σ _ : Fin e, Fin 2) → ℝ) ≃L[ℝ] (Fin e → ℂ) :=
    (Pi.basis (fun _ : Fin e => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin e, Fin 2) = 2 * e := by
    simp [Fintype.card_sigma, mul_comm]
  have hT : volume (E ⁻¹' S) = 0 := by
    rw [← hausdorffMeasure_pi_real, hcard]
    have h := hausdorffMeasure_of_dimH_lt (s := E ⁻¹' S) (d := ((2 * e : ℕ) : ℝ≥0)) (by
      rw [ContinuousLinearEquiv.dimH_preimage]
      simpa using hS)
    simpa using h
  have : (Measure.map E volume).IsAddHaarMeasure := E.isAddHaarMeasure_map volume
  have hac : (volume : Measure (Fin e → ℂ)) ≪ Measure.map E volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply hac
  exact (E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT

theorem ChartRatioImageNull.proof : ChartRatioImageNull.Statement := by
  intro K _ ι _ J e Ψ hdim
  classical
  set S := {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ J, Ψ (segre z) 0 ≠ 0 ∧
    (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)} with hSdef
  by_cases hJ : J = ⊤
  · have hS : S = ∅ := by
      ext y
      simp only [hSdef, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨z, hz, -⟩
      have h1 := hz 1 (hJ ▸ Submodule.mem_top)
      simp at h1
    rw [hS, measure_empty]
  have : Nontrivial (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Σ k, ι k) ℂ ⧸ J)
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := by
    rcases e with _ | m
    · exact absurd (h0.trans_lt hdim) (by simp)
    · exact ⟨m, rfl⟩
  have hle : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) ≤ (m : WithBot ℕ∞) := by
    rcases hx : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) with _ | x
    · exact bot_le
    · rw [hx] at hdim
      have hx' : x < (m : ℕ∞) + 1 := by
        have h5 : ((x : WithBot ℕ∞)) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := hdim
        have h6 := WithBot.coe_lt_coe.1 h5
        exact_mod_cast h6
      exact WithBot.coe_le_coe.2 ((ENat.lt_add_one_iff (ENat.natCast_ne_top m)).1 hx')

  let eqv : (Σ k, ι k) ≃ Fin (Fintype.card (Σ k, ι k)) := Fintype.equivFin _
  let J' : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) := J.map (rename eqv)
  have hdim' : ringKrullDim (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J') ≤ (m : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv J J' (renameEquiv ℂ eqv).toRingEquiv rfl)]
    exact hle
  have hV' := GroundTheory.Heights₂.Heights.ZeroLocusDimH.full _ m J' hdim'
  let L : ((Σ k, ι k) → ℂ) ≃L[ℂ] (Fin (Fintype.card (Σ k, ι k)) → ℂ) :=
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) eqv).toContinuousLinearEquiv
  have hVsub : zeroLocus ℂ J ⊆ L ⁻¹' {x | ∀ q ∈ J', eval x q = 0} := by
    intro z hz q hq
    have hJle : J ≤ (RingHom.ker (eval (L z))).comap (rename eqv) := by
      intro p hp
      simp only [Ideal.mem_comap, RingHom.mem_ker, eval_rename]
      have h2 : (L z) ∘ eqv = z := by
        funext i; simp [L]
      rw [h2]
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz p hp
    exact Ideal.map_le_iff_le_comap.mpr hJle hq
  have hV : dimH (zeroLocus ℂ J : Set ((Σ k, ι k) → ℂ)) ≤ 2 * (m : ℝ≥0∞) :=
    (dimH_mono hVsub).trans ((L.dimH_preimage _).le.trans hV')

  let G : ((Σ k, ι k) → ℂ) → (Fin (m + 1) → ℂ) := fun z j => (Ψ (segre z) 0)⁻¹ * Ψ (segre z) j.succ
  let U := {z : (Σ k, ι k) → ℂ | Ψ (segre z) 0 ≠ 0}
  have hSsub : S ⊆ G '' (zeroLocus ℂ J ∩ U) := by
    rintro y ⟨z, hz, hz0, hy⟩
    refine ⟨z, ⟨hz, hz0⟩, ?_⟩
    funext j
    have h3 := congrFun hy j.succ
    simpa [G] using h3.symm
  have hsmooth : ContDiff ℂ ⊤ (fun z : (Σ k, ι k) → ℂ => Ψ (segre z)) := by
    have h1 : ContDiff ℂ ⊤ (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) := by
      apply contDiff_pi.2
      intro i
      exact contDiff_prod (fun k _ => contDiff_apply ℂ (fun _ => ℂ) _)
    exact (LinearMap.toContinuousLinearMap Ψ).contDiff.comp h1
  have hc : ∀ i, ContDiff ℂ ⊤ (fun z : (Σ k, ι k) → ℂ => Ψ (segre z) i) :=
    fun i => (contDiff_apply ℂ (fun _ => ℂ) i).comp hsmooth
  have hG : ∀ z ∈ U, ContDiffAt ℂ 1 G z := by
    intro z hz
    apply contDiffAt_pi.2
    intro j
    exact (((hc 0).contDiffAt.inv hz).mul (hc j.succ).contDiffAt).of_le le_top
  have hGdim : dimH (G '' (zeroLocus ℂ J ∩ U)) ≤ dimH (zeroLocus ℂ J ∩ U) := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro z hz
    obtain ⟨C, t, ht, hlip⟩ := (hG z hz.2).exists_lipschitzOnWith
    exact ⟨C, t, mem_nhdsWithin_of_mem_nhds ht, hlip⟩
  apply ChartRatioImageNull.volume_eq_zero_of_dimH_lt
  calc dimH S ≤ dimH (G '' (zeroLocus ℂ J ∩ U)) := dimH_mono hSsub
    _ ≤ dimH (zeroLocus ℂ J ∩ U) := hGdim
    _ ≤ dimH (zeroLocus ℂ J : Set ((Σ k, ι k) → ℂ)) := dimH_mono inter_subset_left
    _ ≤ 2 * (m : ℝ≥0∞) := hV
    _ < 2 * ((m + 1 : ℕ) : ℝ≥0∞) := by
      have h4 : 2 * m < 2 * (m + 1) := by omega
      exact_mod_cast h4

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsReductionComplex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace FibreReduction

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem idealOver_int (y : (Σ k, ι k) → Ω) : GenOnFibres.idealOver y ℤ = mCoordIdeal y := by
  have h : (MvPolynomial.map (Int.castRingHom ℤ) : MRingOver ℤ ι →+* MRingOver ℤ ι) = RingHom.id _ := by
    refine RingHom.ext fun f => ?_
    rw [show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _, map_id]
    rfl
  show Ideal.map _ _ = _
  rw [h, Ideal.map_id]

def redRing (y : (Σ k, ι k) → Ω) (p : ℕ) :
    (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) →+* (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) :=
  Ideal.quotientMap _ (MvPolynomial.map (Int.castRingHom (ZMod p))) (by
    rw [idealOver_int]
    exact Ideal.le_comap_map)

theorem redRing_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (f : MRingOver ℤ ι) :
    redRing y p (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (MvPolynomial.map (Int.castRingHom (ZMod p)) f) :=
  Ideal.quotientMap_mk

theorem redRing_smul (y : (Σ k, ι k) → Ω) (p : ℕ) (r : MRingOver ℤ ι)
    (x : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) :
    redRing y p (r • x) = MvPolynomial.map (Int.castRingHom (ZMod p)) r • redRing y p x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [GenOnFibres.smul_mk, redRing_mk, redRing_mk, GenOnFibres.smul_mk, map_mul]

theorem map_mem_cellMon (p : ℕ) {I : ∀ k, Finset (ι k)} {t : MRingOver ℤ ι} (ht : t ∈ KH.cellMon ℤ I) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) t ∈ KH.cellMon (ZMod p) I := by
  unfold KH.cellMon at ht ⊢
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    rw [map_X]
    exact Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul f g _ _ hf hg => rw [map_mul]; exact mul_mem hf hg

def redLocFun (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ)) :
    LocalizedModule (KH.cellMon (ZMod p) I) (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) :=
  x.liftOn (fun mt => LocalizedModule.mk (redRing y p mt.1) ⟨_, map_mem_cellMon p mt.2.2⟩) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    refine LocalizedModule.mk_eq.mpr ⟨⟨_, map_mem_cellMon p u.2⟩, ?_⟩
    have h := congrArg (redRing y p) hu
    simp only [Submonoid.smul_def, redRing_smul] at h ⊢
    exact h)

theorem redLocFun_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (m : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) (t : KH.cellMon ℤ I) :
    redLocFun y p I (LocalizedModule.mk m t) =
      LocalizedModule.mk (redRing y p m) ⟨_, map_mem_cellMon p t.2⟩ := by
  unfold redLocFun
  exact LocalizedModule.liftOn_mk _ _ _

def redLoc (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k)) :
    LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) →+
      LocalizedModule (KH.cellMon (ZMod p) I) (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) where
  toFun := redLocFun y p I
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, redLocFun_mk, map_zero, LocalizedModule.zero_mk]
  map_add' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, redLocFun_mk, redLocFun_mk, redLocFun_mk,
        LocalizedModule.mk_add_mk, (redRing y p).map_add]
      simp only [Submonoid.smul_def, redRing_smul]
      congr 1
      exact Subtype.ext (map_mul _ _ _)

theorem redLoc_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (m : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) (t : KH.cellMon ℤ I) :
    redLoc y p I (LocalizedModule.mk m t) = LocalizedModule.mk (redRing y p m) ⟨_, map_mem_cellMon p t.2⟩ :=
  redLocFun_mk y p I m t

def redCoch (y : (Σ k, ι k) → Ω) (p n : ℕ) :
    KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n →+
      KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n :=
  { toFun := fun w I => redLoc y p I.1 (w I)
    map_zero' := funext fun I => map_zero (redLoc y p I.1)
    map_add' := fun w w' => funext fun I => map_add (redLoc y p I.1) (w I) (w' I) }

theorem redCoch_apply (y : (Σ k, ι k) → Ω) (p n : ℕ)
    (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) (I : KH.Cell K ι n) :
    redCoch y p n w I = redLoc y p I.1 (w I) :=
  rfl

end FibreReduction

def ReductionComplex.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D p : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → p.Prime →
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p (n + 1) (KH.cechD ℤ ι _ n w) =
        KH.cechD (ZMod p) ι _ n (FibreReduction.redCoch y p n w)) ∧
    (∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w ∈
        KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n) ∧
    (∀ n : ℕ, ∀ z ∈ KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n,
      ∃ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, FibreReduction.redCoch y p n w = z) ∧
    (∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w = 0 →
        ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w') ∧
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n), (p : ℤ) • w = 0 → w = 0) ∧
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p n ((p : ℤ) • w) = 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsMultiHomogSumSmulMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

namespace SectionL2Lattice

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem measurableSet_mcPts (P : Ideal (MRing ι)) : MeasurableSet (mcPts P) := by
  have h1 : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h2 : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  exact h1.measurableSet.inter h2.measurableSet


omit [Fintype K] in
theorem isMultiHomog_sum_smul_map {r : ℕ} {e : K → ℕ} {g : Fin r → MRing ι} (hg : ∀ i, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g i) e)
    (c : Fin r → ℂ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∑ i, c i • map (Int.castRingHom ℂ) (g i)) e := by
  classical
  intro m hm k
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
  exact hg i m (MvPolynomial.support_map_subset _ _ (MvPolynomial.support_smul hi)) k

variable {Ω : Type} [Field Ω]


omit [∀ k, Fintype (ι k)] in
theorem chartLat_le_chartLatNm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ :=
  fun _ hs c hc => isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hs c hc⟩)


omit [∀ k, Fintype (ι k)] in
theorem finite_chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (hfin : Module.Finite ℤ (chartLatNm y a τ)) :
    Module.Finite ℤ (chartLat y a τ) ∧
      Module.finrank ℤ (chartLat y a τ) ≤ Module.finrank ℤ (chartLatNm y a τ) := by
  let f : chartLat y a τ →ₗ[ℤ] chartLatNm y a τ :=
    (AddSubgroup.inclusion (chartLat_le_chartLatNm y a τ)).toIntLinearMap
  have hf : Function.Injective f := AddSubgroup.inclusion_injective (chartLat_le_chartLatNm y a τ)
  have : Module.Finite ℤ (chartLat y a τ) := Module.Finite.of_injective f hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hf⟩

end SectionL2Lattice


open SectionL2Lattice in
theorem SectionL2Lattice.proof (hV : SectionPointValue.Statement) (hF : RealFormsOnPoints.Statement)
    (hG : L2GramLattice.Statement) (hN : NmSectionsRankBound.Statement) (hB : SectionSupBound.Statement) :
    SectionL2Lattice.Statement := by
  intro K _ ι _ Ω _ _ y D A har hbir hcont μ _ hμ hZ
  obtain ⟨w, hwc, hwrep, hwnorm, hwmul, hwden⟩ := hV K ι Ω y A har.2.1.2.2 hcont
  obtain ⟨hfin, C, -, hC⟩ := hN K ι Ω y D A.a har hbir
  have hae : ∀ᵐ z ∂μ, z ∈ mcPts (mCoordIdeal y) := hμ
  have hrest : μ.restrict (mcPts (mCoordIdeal y)) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hmeas : ∀ (n : ℕ) (s : chartLat y A.a n), AEStronglyMeasurable (w n s) μ := fun n s => by
    rw [← hrest]; exact (hwc n s).aestronglyMeasurable (measurableSet_mcPts _)
  have hbdd : ∀ (n : ℕ) (s : chartLat y A.a n), ∃ c : ℝ, ∀ᵐ z ∂μ, ‖w n s z‖ ≤ c := fun n s => by
    obtain ⟨c, -, hc⟩ := hB K ι Ω y A n s hcont s.2
    refine ⟨Real.exp c, hae.mono fun z hz => ?_⟩
    rw [← hwnorm n s z hz]
    exact secNormAt_le (Real.exp_pos c).le (isBoundedAt_of_isBoundedH hc hz)
  have hint : ∀ (n : ℕ) (s : chartLat y A.a n), Integrable (fun z => ‖w n s z‖ ^ 2) μ := fun n s => by
    obtain ⟨c, hc⟩ := hbdd n s
    refine (integrable_const (c ^ 2)).mono' ((hmeas n s).norm.pow 2) (hc.mono fun z hz => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have key : ∀ n : ℕ, ∃ φ : chartLat y A.a n →+ EuclideanSpace ℝ (Fin (Module.finrank ℤ (chartLat y A.a n))),
      Function.Injective φ ∧ DiscreteTopology (imageLattice φ) ∧
      (∀ [DiscreteTopology (imageLattice φ)], IsZLattice ℝ (imageLattice φ)) ∧
      ∀ s, ‖φ s‖ = Real.sqrt (∫ z, ‖w n s z‖ ^ 2 ∂μ) := by
    intro n
    have : Module.Finite ℤ (chartLat y A.a n) := (finite_chartLat y A.a n (hfin n)).1
    have : Module.Free ℤ (chartLat y A.a n) := Module.free_of_finite_type_torsion_free'
    refine hG _ _ μ (w n) (hmeas n) (hbdd n) ?_
    intro r x hx c hc
    obtain ⟨e, e', h, g, hh, hg, he, hy, hgy⟩ := hwden n r x
    refine hF K ι Ω y (D + 1) e r g har hg ?_ c ?_
    · have h1 : LinearIndependent ℤ (fun i => (x i : Ω)) :=
        hx.map' (chartLat y A.a n).subtype.toIntLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
      have h2 := h1.map' (LinearMap.mulRight ℤ (aeval y h))
        (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hy))
      convert h2 using 1 <;> first | rfl | (funext i; simp [hgy i])
    · intro z hz
      have hF' := hZ e (∑ i, (c i : ℂ) • map (Int.castRingHom ℂ) (g i)) (isMultiHomog_sum_smul_map hg _) ?_ z hz
      set_option synthInstance.maxHeartbeats 100000 in
        · simpa only [map_sum, smul_eval] using hF'
      · filter_upwards [hc, hae] with z hz0 hzP
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [smul_eval]
        calc ∑ i, (c i : ℂ) * eval z (map (Int.castRingHom ℂ) (g i))
            = ∑ i, (c i : ℂ) * (w n (x i) z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hwrep n (x i) e e' (g i) h z (hg i) hh he (hgy i) hzP]
          _ = (∑ i, (c i : ℂ) * w n (x i) z) * (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
          _ = 0 := by rw [hz0, zero_mul]
  choose φ hinj hdisc hlat hnorm using key
  refine ⟨fun n => Module.finrank ℤ (chartLat y A.a n), φ, hinj, hdisc, fun n _ => hlat n, ?_, ?_, ?_, ?_⟩
  · intro n c s hc hs
    rw [hnorm, ← Real.sqrt_sq hc]
    refine Real.sqrt_le_sqrt ?_
    calc ∫ z, ‖w n s z‖ ^ 2 ∂μ ≤ ∫ _, c ^ 2 ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) (integrable_const _)
            (hae.mono fun z hz => by
              show ‖w n s z‖ ^ 2 ≤ c ^ 2
              rw [← hwnorm n s z hz]
              exact pow_le_pow_left₀ (secNormAt_nonneg _ _ _ _ _)
                (secNormAt_le hc (isBoundedAt_of_isBoundedH hs hz)) 2)
      _ = c ^ 2 := by simp
  · intro n k s t st ht hst
    rw [hnorm, hnorm]
    refine Real.sqrt_le_sqrt (integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) (hint n s)
      (hae.mono fun z hz => ?_))
    have h1 : ‖w k t z‖ ≤ 1 := by
      rw [← hwnorm k t z hz]
      refine secNormAt_le zero_le_one fun dg dh g h hg hh hd he => ?_
      rw [one_mul]
      exact ht dg dh g h z hg hh hd he hz
    show ‖w (n + k) st z‖ ^ 2 ≤ ‖w n s z‖ ^ 2
    rw [hwmul n k s t st hst z hz, norm_mul, mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) h1)
  · exact ⟨C, fun n => le_trans (by exact_mod_cast (finite_chartLat y A.a n (hfin n)).2) (hC n)⟩
  · intro n s
    rw [hnorm, sectionL2Norm]
    congr 1
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    simp only [hwnorm n s z hz]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.H1VanishGeneratedOfLocalizedSubsingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Trivial

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]


omit [Fintype K] [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] in
theorem loc_subsingleton_of_kill {T : Submonoid (MRingOver S ι)} {u : MRingOver S ι} (hu : u ∈ T)
    (hk : ∀ y : M, u • y = 0) : Subsingleton (LocalizedModule T M) := by
  have h0 : ∀ x : LocalizedModule T M, x = 0 := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h y s =>
      rw [← LocalizedModule.zero_mk s]
      refine LocalizedModule.mk_eq.mpr ⟨⟨u, hu⟩, ?_⟩
      simp only [Submonoid.smul_def, smul_zero]
      rw [smul_comm, hk, smul_zero]
  exact ⟨fun a b => by rw [h0 a, h0 b]⟩

theorem h1_vanish_generated_of_localized_subsingleton
    (h : ∀ (n : ℕ) (I : KH.Cell K ι n), Subsingleton (LocalizedModule (KH.cellMon S I.1) M))
    (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    Subsingleton (KH.cechHc ι 𝓜 d 1) ∧ GeneratedMod S ι 𝓜 d := by
  have : Subsingleton (KH.CechC S ι M 1) := ⟨fun f g => funext fun I => (h 1 I).elim _ _⟩
  refine ⟨⟨fun x y => ?_⟩, fun I x _ => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]
  · refine ⟨1, 0, 0, Fin.elim0, Fin.elim0, Submonoid.one_mem _, isMultiHomog_one_zero, fun j => j.elim0,
      fun j => j.elim0, ?_⟩
    rw [one_smul, Fin.sum_univ_zero]
    exact (h 0 I).elim _ _


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem isMGraded_punit : KH.IsMGraded S ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) := by
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (fun _ => disjoint_bot_left)
    (Subsingleton.elim _ _), fun _ _ _ _ _ _ => (Submodule.mem_bot _).2 (Subsingleton.elim _ _)⟩

end Trivial

theorem H1GenerationDevissage.proof (hPF : KH.PrimeFiltStatement) (hSES : KH.CechSESStatement)
    (hGQ : GradedSubquot.Statement) (hGS : GenSESStep.Statement) : H1GenerationDevissage.Statement := by
  intro S _ K _ _ ι _ _ V N hS hP M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩ := hPF S K ι M 𝓜 hS hfin hgr
  let G : ℕ → Set M := fun j => m '' {l | (l : ℕ) < j}
  let F : ℕ → Submodule (MRingOver S ι) M := fun j => Submodule.span _ (G j)
  have hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c' := by
    rintro j _ ⟨l, -, rfl⟩
    exact ⟨c l, hm l⟩
  have hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)
  have hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j)) := fun j =>
    (hGQ S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1
  have key : ∀ j ≤ r, ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      Subsingleton (KH.cechHc ι (subGrading 𝓜 (F j)) (e + n • N) 1) ∧
        GeneratedMod S ι (subGrading 𝓜 (F j)) (e + n • N) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hF0 : F 0 = ⊥ := by simp [F, G]
      refine ⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton
        (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun y => ?_) _ _⟩
      rw [one_smul]
      have hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M) := by
        rw [← hF0]
        exact y.2
      exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot _).1 hy)
    | succ j ih =>
      intro hj
      obtain ⟨c₀, hc₀⟩ := ih (Nat.le_of_succ_le hj)
      let l : Fin r := ⟨j, hj⟩
      let L : Submodule (MRingOver S ι) (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hq := (hGQ S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1)) (hFmono (Nat.le_succ j))).2
      have hcolj : ∀ p : MRingOver S ι, p • m l ∈ F j ↔ p ∈ 𝔭 l := fun p => hcol l p
      have hkill : ∀ p ∈ 𝔭 l, ∀ y ∈ F (j + 1), p • y ∈ F j := by
        intro p hp y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨l', hl', rfl⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h
          · exact (F j).smul_mem p (Submodule.subset_span ⟨l', h, rfl⟩)
          · rw [show l' = l from Fin.ext h]
            exact (hcolj p).2 hp
        | zero => rw [smul_zero]; exact (F j).zero_mem
        | add x y _ _ hx hy => rw [smul_add]; exact (F j).add_mem hx hy
        | smul a x _ hx => rw [smul_comm]; exact (F j).smul_mem a hx
      have hann : 𝔭 l ≤ Module.annihilator (MRingOver S ι) (F (j + 1) ⧸ L) := by
        intro p hp
        rw [Module.mem_annihilator]
        intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective L q
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        show ((p • y : F (j + 1)) : M) ∈ F j
        rw [Submodule.coe_smul]
        exact hkill p hp y y.2
      have hfinQ : Module.Finite (MRingOver S ι) (F (j + 1) ⧸ L) := by
        have : Module.Finite (MRingOver S ι) (F (j + 1)) :=
          Module.Finite.iff_fg.2 (Submodule.fg_span ((Set.toFinite _).image m))
        infer_instance
      obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n →
          Subsingleton (KH.cechHc ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) 1) ∧
            GeneratedMod S ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) := by
        by_cases hrel : IsMultiProjPrime (𝔭 l)
        · exact hP (𝔭 l) hrel (hV.trans (h𝔭 l).2.2) (F (j + 1) ⧸ L) _ hfinQ hq hann e
        · have hirr : ¬ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (𝔭 l) := fun h => hrel ⟨(h𝔭 l).1, (h𝔭 l).2.1, h⟩
          simp only [ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, not_forall, not_exists, not_not] at hirr
          obtain ⟨k, hk⟩ := hirr
          refine ⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton (fun _ I => ?_) _ _⟩
          obtain ⟨i, hi⟩ := I.2.1 k
          exact loc_subsingleton_of_kill (Submonoid.subset_closure ⟨k, i, hi, rfl⟩)
            (Module.mem_annihilator.1 (hann (hk i)))
      refine ⟨max c₀ c₂, fun n hn => ?_⟩
      have h0 := hc₀ n (le_of_max_le_left hn)
      have h2 := hc₂ n (le_of_max_le_right hn)
      let g := Submodule.inclusion (hFmono (Nat.le_succ j))
      have hex : LinearMap.range g = LinearMap.ker L.mkQ := by
        rw [Submodule.range_inclusion, Submodule.ker_mkQ]
      have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g := fun _ _ hx => hx
      have hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L)
          L.mkQ := fun _ _ hx => Submodule.mem_map_of_mem hx
      have H := hSES S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex (e + n • N) 1
      exact ⟨H.1 h0.1 h2.1, hGS S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex _ h0.1 h0.2 h2.2⟩
  have hFr : F r = ⊤ := by
    rw [← hspan]
    simp [F, G]
  obtain ⟨c₁, hc₁⟩ := key r le_rfl
  refine ⟨c₁, fun n hn => ?_⟩
  obtain ⟨h1, hgen⟩ := hc₁ n hn
  let g := (F r).subtype
  have hex : LinearMap.range g = LinearMap.ker (0 : M →ₗ[MRingOver S ι] PUnit) := by
    rw [Submodule.range_subtype, hFr, LinearMap.ker_zero]
  have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F r)) 𝓜 g := fun _ _ hx => hx
  have hhG : KH.IsMGradedMap S ι 𝓜 (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) 0 :=
    fun _ _ _ => Submodule.zero_mem _
  have hU := h1_vanish_generated_of_localized_subsingleton (M := PUnit) (S := S) (ι := ι)
    (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun _ => Subsingleton.elim _ _)
    (fun _ => ⊥) (e + n • N)
  have H := hSES S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG
    (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex (e + n • N) 1
  exact ⟨H.1 h1 hU.1, hGS S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG
    (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex _ h1 hgen hU.2⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ArithmeticVolumeDimensionOne.proof (hG6 : ArithmeticVolumeBigDimensionOne.Statement) : ArithmeticVolumeDimensionOne.Statement := by
  intro K _ ι _ Ω _ _ y M P0 II hII har hb hM hpos
  set T := II K ι (mCoordIdeal y) 1 (fun _ => M)
  set g := geomDeg (mCoordIdeal y) M 0
  have hden : 0 < 2 * (|g| + 1) := by positivity
  set η := T / (2 * (|g| + 1))
  have hη0 : 0 < η := div_pos hpos hden
  have he : η * (2 * (|g| + 1)) = T := div_mul_cancel₀ T hden.ne'
  have hηlt : η * g < T := by
    have h1 : η * g ≤ η * |g| := mul_le_mul_of_nonneg_left (le_abs_self g) hη0.le
    nlinarith
  have hshift := ConstantShift.proof K ι (II K ι) (mCoordIdeal y) 0 M η (hII K ι) har hM.semipos.1
  have hpos' : 0 < II K ι (mCoordIdeal y) 1 (fun _ => HermLine.constShift M η) := by
    have e : II K ι (mCoordIdeal y) 1 (fun _ => HermLine.constShift M η) = T - ((0 : ℕ) + 1 : ℝ) * η * g :=
      hshift
    rw [e]
    push_cast
    linarith
  have hvol := hG6 K ι Ω y (HermLine.constShift M η) P0 II hII har hb hM.normalForm_baseLattice_le_dualSpan_sup_line
    (isSemipositiveRel_constShift hM.semipos η) (by rw [constShift_a]; exact hM.nef)
    (isConjInvariantH_constShift hM.conjInv η)
  obtain ⟨n, hn, s, hs, hs0, hsmall⟩ := exists_small_section_of_arithmeticVolume_pos (hpos'.trans_le hvol)
  have hn' : (0 : ℝ) < n * η := mul_pos (by exact_mod_cast hn) hη0
  refine ⟨n, s, hn, by rwa [constShift_a] at hs, hs0, Real.exp (-(n * η)), ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    linarith
  · intro dg dh g' h z hg hh hdeg heq hz
    have hle := hsmall dg dh g' h z hg hh (by rw [constShift_a]; exact hdeg) heq hz
    have e : Real.exp (-(n * η)) = Real.exp (-η) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    refine hle.trans (le_of_eq ?_)
    rw [constShift_h, mul_pow, e]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
