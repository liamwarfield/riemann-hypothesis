module

public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstant
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberMetricChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothWeightConstNearEmbeddings
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
open Set Manifold GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight

theorem exists_smooth_weight_const_near_embeddings :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F]
      [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (Λ : (F →+* ℂ) → ℝ), (∀ sg, 0 < Λ sg) →
      (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) →
      ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ,
        LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg := by
  intro K _ ι _ Ω _ F _ _ _ y Λ hpos huniq
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg =>
    {z | z ∈ mcPts (mCoordIdeal y) ∧ LiesOver y sg z}
  let C : (F →+* ℂ) → Set ((Σ k, ι k × ι k) → ℂ) := fun sg => projPt '' S sg
  have hSmul : ∀ sg z (c : K → ℂ), (∀ k, c k ≠ 0) → z ∈ S sg → (fun p => c p.1 * z p) ∈ S sg :=
    fun sg z c hc hz => ⟨mcPts_smul (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y) c hc hz.1,
      liesOver_smul hz.2 c⟩
  have hC : ∀ sg, IsCompact (C sg) := by
    intro sg
    have hK : IsCompact (S sg ∩ {z | ∀ k, blockNormSq z k = 1}) := by
      refine isCompact_sphere.of_isClosed_subset ?_ inter_subset_right
      have : S sg ∩ {z | ∀ k, blockNormSq z k = 1} =
          ({z | ∀ f ∈ mCoordIdeal y, eval z (map (Int.castRingHom ℂ) f) = 0} ∩
            {z | LiesOver y sg z}) ∩ {z | ∀ k, blockNormSq z k = 1} := by
        ext z
        simp only [S, mcPts, mem_inter_iff, mem_setOf_eq]
        constructor
        · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3⟩
          exact ⟨⟨h1, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨⟨⟨fun k => ?_, h1⟩, h2⟩, h3⟩
          by_contra hcon
          push_neg at hcon
          have := h3 k
          simp [blockNormSq, hcon] at this
      rw [this]
      exact ((isClosed_zeros _).inter (EmbeddingWeight.isClosed_liesOver y sg)).inter
        isCompact_sphere.isClosed
    have heq : C sg = projPt '' (S sg ∩ {z | ∀ k, blockNormSq z k = 1}) := by
      refine Subset.antisymm ?_ (image_mono inter_subset_left)
      rintro e ⟨z, hz, rfl⟩
      obtain ⟨c, hc, hc1⟩ := exists_smul_sphere hz.1.1
      exact ⟨_, ⟨hSmul sg z c hc hz, hc1⟩, projPt_smul c hc z⟩
    rw [heq]
    exact hK.image_of_continuousOn (contDiffOn_projPt.continuousOn.mono fun z hz => hz.1.1.1)
  have hdisj : ∀ sg tg, sg ≠ tg → Disjoint (C sg) (C tg) := by
    intro sg tg hne
    rw [Set.disjoint_left]
    rintro e ⟨z, ⟨hzP, hzs⟩, rfl⟩ ⟨w, ⟨hwP, hwt⟩, hw⟩
    obtain ⟨c, hc, rfl⟩ := exists_smul_of_projPt_eq hzP.1 hwP.1 hw.symm
    exact hne ((huniq _ hwP).unique (liesOver_smul hzs c) hwt)
  have hsep : ∀ sg, ∃ χ : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ᶠ e in 𝓝ˢ (⋃ tg ∈ Finset.univ.erase sg, C tg), χ e = 0) ∧
      (∀ᶠ e in 𝓝ˢ (C sg), χ e = 1) := by
    intro sg
    obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
      𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) (n := ⊤)
      (isClosed_biUnion_finset fun tg _ => (hC tg).isClosed) (hC sg).isClosed
      (Set.disjoint_iUnion₂_left.2 fun tg htg => hdisj tg sg (Finset.ne_of_mem_erase htg))
    exact ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, h0, h1⟩
  choose χ hχs hχ0 hχ1 using hsep
  let g : ((Σ k, ι k × ι k) → ℂ) → ℝ := fun e => ∑ sg, Real.log (Λ sg) * χ sg e
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    ContDiff.sum fun sg _ => contDiff_const.mul (hχs sg)
  have hloc : ∀ sg, ∀ e ∈ C sg, ∀ᶠ e' in 𝓝 e, g e' = Real.log (Λ sg) := by
    intro sg e he
    have : ∀ tg, ∀ᶠ e' in 𝓝 e, χ tg e' = if tg = sg then 1 else 0 := by
      intro tg
      by_cases htg : tg = sg
      · subst htg
        simpa using (hχ1 tg).filter_mono (nhds_le_nhdsSet he)
      · simp only [htg, if_false]
        exact (hχ0 tg).filter_mono (nhds_le_nhdsSet
          (Set.mem_iUnion₂.2 ⟨sg, Finset.mem_erase.2 ⟨Ne.symm htg, Finset.mem_univ _⟩, he⟩))
    filter_upwards [Filter.eventually_all.2 this] with e' he'
    simp only [g, he', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  let u : ((Σ k, ι k) → ℂ) → ℝ := fun z => g (projPt z)
  have hu_smul : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) →
      (fun z => -u z) (fun p => c p.1 * z p) = (fun z => -u z) z := by
    intro c z hc
    simp only [u, projPt_smul c hc]
  refine ⟨HermLine.ofWeight (fun z => -u z) hu_smul, rfl, ?_, ?_⟩
  · have h1 := hg.comp_contDiffOn (contDiffOn_projPt (ι := ι))
    have hu := h1.neg.neg
    exact Real.contDiff_exp.comp_contDiffOn hu
  · intro z hz sg hsg
    have hzC : projPt z ∈ C sg := ⟨z, ⟨hz, hsg⟩, rfl⟩
    have hcont : ContinuousAt projPt z :=
      contDiffOn_projPt.continuousOn.continuousAt (EmbeddingWeight.isOpen_blockNonzero.mem_nhds hz.1)
    filter_upwards [Filter.Tendsto.eventually hcont (hloc sg _ hzC)] with w hw1
    change Real.exp (-(-u w)) = Λ sg
    simp only [u, hw1, neg_neg, Real.exp_log (hpos sg)]

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionLocConstTrivial
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem intersection_locConst_trivial : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (B : HermLine ι) (Λ : (F →+* ℂ) → ℝ) (II : IntersectionSystem), IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → B.a = 0 → IsSmoothHerm B → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) → II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) = ∑ sg : F →+* ℂ, Real.log (Λ sg) * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hInt K _ ι _ Ω _ F _ _ _ y D L B Λ II hII hP hL hB0 hB hex hloc
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg => {z | LiesOver y sg z}
  have hSc : ∀ sg, IsClosed (S sg) := fun sg =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.isClosed_liesOver y sg
  have hSs : ∀ sg (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S sg →
      (fun p => t p.1 * z p) ∈ S sg :=
    fun _ t _ _ hz => GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.liesOver_smul hz t
  have hex' : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg, z ∈ S sg := hex
  have hR := (hII K ι).2.2 (mCoordIdeal y) D L B 1 0 hP hL hB (fun k => by simp [hB0])
    tele_one_homog (fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1))
  have hnum : II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) =
      ptsIntegral (mCoordIdeal y) (pot L) fun z => Real.log (B.h z) := by
    rw [hR]
    unfold recR
    rw [tele_divSupp_one, finsum_mem_empty, zero_sub]
    unfold arInt
    have hl : logNorm B 1 = fun z => - Real.log (B.h z) := by
      funext z
      simp [logNorm, Real.log_inv]
    rw [hl, tele_ptsIntegral_neg, neg_neg]
    rfl
  have hw : ptsIntegral (mCoordIdeal y) (pot L) (fun z => Real.log (B.h z)) =
      ptsIntegral (mCoordIdeal y) (pot L)
        (fun z => ∑ s, Real.log (Λ s) * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    have hval : B.h z = Λ sg := (hloc z hz sg hsg).self_of_nhds
    rw [Finset.sum_eq_single sg]
    · rw [Set.indicator_of_mem (show z ∈ S sg from hsg), mul_one, hval]
    · intro s _ hs
      have hns : z ∉ S s := fun h => hs ((hex z hz).unique h hsg)
      rw [Set.indicator_of_notMem hns, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  rw [hnum, hw]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt K ι _ D L (F →+* ℂ) S
    (fun s => Real.log (Λ s)) hP hL hSc hSs hex'

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetric
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstant
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstant
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem mixedDisc_eq_zero_of_eq_zero {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (j : Fin D)
    (hA : A j = 0) : mixedDisc A = 0 := by
  classical
  have pair : ∀ T : Finset (Fin D), j ∉ T →
      (-1 : ℂ) ^ (D - T.card) * (∑ k ∈ T, A k).det +
        (-1 : ℂ) ^ (D - (insert j T).card) * (∑ k ∈ insert j T, A k).det = 0 := by
    intro T hj
    rw [Finset.sum_insert hj, hA, zero_add, Finset.card_insert_of_notMem hj]
    have hlt : T.card < D := by simpa using Finset.card_lt_univ_of_notMem hj
    obtain ⟨m, hm⟩ : ∃ m, D - T.card = m + 1 := ⟨D - T.card - 1, by omega⟩
    have hm' : D - (T.card + 1) = m := by omega
    rw [hm, hm', pow_succ]
    ring
  unfold mixedDisc
  rw [Finset.sum_involution (fun S _ => if j ∈ S then S.erase j else insert j S), mul_zero]
  · intro S _
    split_ifs with h
    · have := pair (S.erase j) (Finset.notMem_erase j S)
      rw [Finset.insert_erase h] at this
      rw [add_comm]
      exact this
    · exact pair S h
  · intro S _ _
    split_ifs with h
    · intro e
      have hmem : j ∈ S.erase j := by
        rw [e]
        exact h
      exact Finset.notMem_erase j S hmem
    · exact fun e => h (e ▸ Finset.mem_insert_self j S)
  · intro S _
    exact Finset.mem_univ _
  · intro S _
    by_cases h : j ∈ S
    · simp [h, Finset.insert_erase]
    · simp [h, Finset.erase_insert]

theorem cxHessian_zero {D : ℕ} (z : Fin D → ℂ) : cxHessian (fun _ => (0 : ℝ)) z = 0 := by
  have h : fderiv ℝ (fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ))) z = 0 := by
    have h1 : fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ)) = fun _ => 0 := by
      funext x
      exact fderiv_const_apply 0
    rw [h1]
    exact fderiv_const_apply 0
  ext a b
  simp [cxHessian, h]

theorem sheetDensity_update_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (Function.update φ j 0) g y w = 0 := by
  unfold sheetDensity
  split_ifs with hγ
  · have hm : mixedDisc (fun k => cxHessian
        (fun y' => Function.update φ j 0 k (hγ.choose y')) y) = 0 := by
      refine mixedDisc_eq_zero_of_eq_zero _ j ?_
      simpa using cxHessian_zero y
    simp [maDensity, hm]
  · rfl

theorem ptsIntegral_eq_zero_of_locConst :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
      (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e),
      (∀ z ∈ mcPts P, ∃ c : ℝ, φ j =ᶠ[𝓝 z] fun _ => c) → ptsIntegral P φ g = 0 := by
  intro K _ ι _ P e φ g j hj
  have hshift : ∀ i, ∀ z ∈ mcPts P, ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, φ i u = Function.update φ j 0 i u + c := by
    intro i z hz
    by_cases hi : i = j
    · subst hi
      obtain ⟨c, hc⟩ := hj z hz
      refine ⟨c, hc.mono fun u hu => ?_⟩
      simpa using hu
    · exact ⟨0, Eventually.of_forall fun u => by simp [Function.update_of_ne hi]⟩
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersection.ptsIntegral_add_locConst P hshift g]
  unfold ptsIntegral
  split_ifs
  · simp [ptsIntegralAt, sheetDensity_update_zero]
  · rfl

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstantStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_integral_zero_of_locally_constant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e), (∀ z ∈ mcPts P, ∃ c : ℝ, φ j =ᶠ[𝓝 z] fun _ => c) → ptsIntegral P φ g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetric
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

section FactorChange

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem snoc_update_comp_swap {D : ℕ} (W : Fin D → HermLine ι) (m : Fin D) (X B : HermLine ι) :
    (Fin.snoc (Function.update W m X) B : Fin (D + 1) → HermLine ι) ∘
        Equiv.swap m.castSucc (Fin.last D) =
      Fin.snoc (Function.update W m B) X := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Function.comp_apply, Equiv.swap_apply_right, Fin.snoc_castSucc, Function.update_self, Fin.snoc_last]
  · by_cases hi : i = m
    · subst hi
      rw [Function.comp_apply, Equiv.swap_apply_left, Fin.snoc_last, Fin.snoc_castSucc, Function.update_self]
    · have h1 : i.castSucc ≠ m.castSucc := fun h => hi (Fin.castSucc_injective _ h)
      have h2 : i.castSucc ≠ Fin.last D := (Fin.castSucc_lt_last i).ne
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.snoc_castSucc, Fin.snoc_castSucc,
        Function.update_of_ne hi, Function.update_of_ne hi]

theorem smooth_update {D : ℕ} {W : Fin D → HermLine ι} (hW : ∀ j, IsSmoothHerm (W j)) (m : Fin D)
    {X : HermLine ι} (hX : IsSmoothHerm X) (j : Fin D) : IsSmoothHerm (Function.update W m X j) := by
  by_cases hj : j = m
  · subst hj
    simpa using hX
  · simpa [Function.update_of_ne hj] using hW j

theorem smooth_snoc {D : ℕ} {W : Fin D → HermLine ι} (hW : ∀ j, IsSmoothHerm (W j)) {X : HermLine ι}
    (hX : IsSmoothHerm X) (j : Fin (D + 1)) :
    IsSmoothHerm ((Fin.snoc W X : Fin (D + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    exact hX
  · rw [Fin.snoc_castSucc]
    exact hW i

theorem position_change (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) {D : ℕ} (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1))
    (W : Fin D → HermLine ι) (hW : ∀ j, IsSmoothHerm (W j)) (m : Fin D) (A A' B : HermLine ι)
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (hB : IsSmoothHerm B) (hab : A'.a = A.a)
    (hloc : ∀ z ∈ mcPts P, ∃ c : ℝ, B.h =ᶠ[𝓝 z] fun _ => c) :
    I P (D + 1) (Fin.snoc (Function.update W m A) B) =
      I P (D + 1) (Fin.snoc (Function.update W m A') B) := by
  have hM := smooth_update hW m hB
  have hswap : ∀ X : HermLine ι, IsSmoothHerm X →
      I P (D + 1) (Fin.snoc (Function.update W m X) B) = I P (D + 1) (Fin.snoc (Function.update W m B) X) := by
    intro X hX
    rw [← snoc_update_comp_swap W m X B]
    exact (hI.1 P (D + 1) _ _ hP (smooth_snoc (smooth_update hW m hX) hB)).symm
  rw [hswap A hA, hswap A' hA',
    GlobalTheory.CompanionTheory.Ar.Tele.step GroundTheory.Heights₂.Heights.ForSecondHalf.MetricLocal.full I hI P D _ A A' hP hM hA hA' hab,
    GlobalTheory.T.points_integral_zero_of_locally_constant K ι P D (pot (Function.update W m B)) _ m ?_, sub_zero]
  intro z hz
  obtain ⟨c, hc⟩ := hloc z hz
  refine ⟨Real.log c, ?_⟩
  filter_upwards [hc] with x hx
  simp [pot, hx]

theorem word_change (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) {D : ℕ} (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1))
    (L L' : Fin D → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j))
    (ha : ∀ j, (L j).a = (L' j).a) (B : HermLine ι) (hB : IsSmoothHerm B)
    (hloc : ∀ z ∈ mcPts P, ∃ c : ℝ, B.h =ᶠ[𝓝 z] fun _ => c) :
    I P (D + 1) (Fin.snoc L B) = I P (D + 1) (Fin.snoc L' B) := by
  let Wd : ℕ → Fin D → HermLine ι := fun m j => if (j : ℕ) < m then L' j else L j
  have hWd : ∀ m j, IsSmoothHerm (Wd m j) := by
    intro m j
    by_cases h : (j : ℕ) < m
    · simpa [Wd, h] using hL' j
    · simpa [Wd, h] using hL j
  have key : ∀ m, m ≤ D → I P (D + 1) (Fin.snoc L B) = I P (D + 1) (Fin.snoc (Wd m) B) := by
    intro m
    induction m with
    | zero =>
      intro _
      have : Wd 0 = L := by
        funext j
        simp [Wd]
      rw [this]
    | succ m ih =>
      intro hm
      let i : Fin D := ⟨m, hm⟩
      have e0 : Function.update (Wd m) i (L i) = Wd m := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [Wd, i]
        · simp [Function.update_of_ne hj]
      have e1 : Function.update (Wd m) i (L' i) = Wd (m + 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [Wd, i]
        · have hne : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
          have hiff : (j : ℕ) < m + 1 ↔ (j : ℕ) < m := by omega
          simp [Function.update_of_ne hj, Wd, hiff]
      rw [ih (by omega), ← e1]
      conv_lhs => rw [← e0]
      exact position_change I hI P hP (Wd m) (hWd m) i (L i) (L' i) B (hL i) (hL' i) hB (ha i).symm hloc
  have hD : Wd D = L' := by
    funext j
    simp [Wd]
  rw [key D le_rfl, hD]

end FactorChange

theorem mass_eq_of_degrees : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L L' : Fin D → HermLine ι) (sg : F →+* ℂ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, (L j).a = (L' j).a) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L') ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hA hInt K _ ι _ Ω _ F _ _ _ y D L L' sg hP hL hL' ha hex
  classical
  obtain ⟨II, hII, -⟩ := hA
  let Λ : (F →+* ℂ) → ℝ := fun s => if s = sg then Real.exp 1 else 1
  have hΛ : ∀ s, 0 < Λ s := by
    intro s
    by_cases h : s = sg
    · simp [Λ, h, Real.exp_pos]
    · simp [Λ, h]
  obtain ⟨B, hB0, hBs, hBloc⟩ :=
    exists_smooth_weight_const_near_embeddings K ι Ω F y Λ hΛ hex
  have mass : ∀ M : Fin D → HermLine ι, (∀ j, IsSmoothHerm (M j)) →
      II K ι (mCoordIdeal y) (D + 1) (Fin.snoc M B) =
        ptsIntegral (mCoordIdeal y) (pot M) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
    intro M hM
    rw [intersection_locConst_trivial hInt K ι Ω F y D M B Λ II hII hP hM hB0 hBs hex hBloc,
      Finset.sum_eq_single sg]
    · simp [Λ]
    · intro s _ hs
      simp [Λ, hs]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  rw [← mass L hL, ← mass L' hL']
  refine word_change (II K ι) (hII K ι) _ hP L L' hL hL' ha B hBs ?_
  intro z hz
  obtain ⟨s, hs, -⟩ := hex z hz
  exact ⟨Λ s, hBloc z hz s hs⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetricStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_integral_independent_of_metric : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L L' : Fin D → HermLine ι) (sg : F →+* ℂ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, (L j).a = (L' j).a) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L') ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.mass_eq_of_degrees | exact GlobalTheory.CompanionTheory.Ar.Giv.mass_eq_of_degrees | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.mass_eq_of_degrees <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvariance
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvariance
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem sum_log_unit_mul_mass_eq_zero : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (θ : (𝓞 F)ˣ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = 0 := by
  intro hSys hInt K _ ι _ Ω _ F _ _ _ y D L θ hP hbir hL hex
  classical
  obtain ⟨II, hII, -⟩ := hSys
  obtain ⟨x, hx⟩ : ∃ x : F, x = ((θ : 𝓞 F) : F) := ⟨_, rfl⟩
  have hmul : ((((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) * x = 1 := by
    rw [hx]
    have h1 : (((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (θ : 𝓞 F)) = 1 := by simp
    exact_mod_cast congrArg (fun u : 𝓞 F => (u : F)) h1
  have hxinv : ((((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) = x⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact zero_ne_one hmul
  have hxI : IsIntegral ℤ x := hx ▸ RingOfIntegers.isIntegral_coe (θ : 𝓞 F)
  have hxI' : IsIntegral ℤ x⁻¹ := hxinv ▸ RingOfIntegers.isIntegral_coe ((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  rw [← hx]
  have ht0 : algebraMap F Ω x ≠ 0 := (map_ne_zero _).mpr hx0
  have htI : IsIntegral ℤ (algebraMap F Ω x) := hxI.map (algebraMap F Ω).toIntAlgHom
  have htI' : IsIntegral ℤ (algebraMap F Ω x)⁻¹ := by
    rw [← map_inv₀]
    exact hxI'.map (algebraMap F Ω).toIntAlgHom
  obtain ⟨d, f, g, hf, hg, hg0, hfg⟩ := hbir (algebraMap F Ω x)
  have hf0 : aeval y f ≠ 0 := by
    rw [hfg]
    exact mul_ne_zero ht0 hg0
  have hgP : g ∉ mCoordIdeal y := fun h => hg0
    ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hg).mp h)
  have hfP : f ∉ mCoordIdeal y := fun h => hf0
    ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).mp h)
  obtain ⟨B, hB0, hBs, hBl⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun sg => ‖sg x‖) (fun sg => norm_pos_iff.mpr ((map_ne_zero sg).mpr hx0)) hex
  obtain ⟨A, hAa, hA⟩ : ∃ A : HermLine ι, (∀ k, A.a k = d k) ∧ IsSmoothHerm A :=
    ⟨HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (d k : ℤ)), fun _ => rfl,
      GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs _⟩
  have hAB : IsSmoothHerm (A.tensor B) := ContDiffOn.mul hA hBs
  have hABa : ∀ k, (A.tensor B).a k = d k := fun k => by
    simp [HermLine.tensor, hB0, hAa k]
  have hRA := (hII K ι).2.2 (mCoordIdeal y) D L A g d hP hL hA hAa hg hgP
  have hRB := (hII K ι).2.2 (mCoordIdeal y) D L (A.tensor B) f d hP hL hAB hABa hf hfP
  have hadd := (hII K ι).2.1 (mCoordIdeal y) D L A B hP hL hA hBs
  obtain ⟨hsupp, hmult⟩ := GlobalTheory.T.unit_ratio_divisor_support_eq K ι Ω y D d f g (algebraMap F Ω x) hP hf hg hg0 ht0 htI htI' hfg
  have hlog : ∀ z ∈ mcPts (mCoordIdeal y), logNorm (A.tensor B) f z = logNorm A g z := by
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    have hval : B.h z = ‖sg x‖ := (hBl z hz sg hsg).self_of_nhds
    have hfz := hsg d f g x hf hg hfg
    have hs0 : ‖sg x‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero sg).mpr hx0)
    have hAz : A.h z ≠ 0 := (A.pos z hz.1).ne'
    unfold logNorm
    congr 1
    show ‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * B.h z) = _
    rw [hfz, hval, norm_mul]
    field_simp
  have hrec : recR (II K ι) (mCoordIdeal y) L (A.tensor B) f = recR (II K ι) (mCoordIdeal y) L A g := by
    unfold recR
    rw [hsupp]
    congr 1
    · exact finsum_mem_congr rfl fun W hW => by rw [hmult W hW]
    · exact GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) hlog
  rw [← intersection_locConst_trivial hInt K ι Ω F y D L B (fun sg => ‖sg x‖) II hII hP hL hB0 hBs hex hBl]
  linarith [hRA, hRB, hadd, hrec]

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvarianceStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_over_embeddings_unit_invariance : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (θ : (𝓞 F)ˣ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetry
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetry
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MeasureTheory

section Hess

variable {D : ℕ}

theorem hess_comp_star (φ : (Fin D → ℂ) → ℝ) (z u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => φ (star y))) z u v =
      fderiv ℝ (fderiv ℝ φ) (star z) (star u) (star v) := by
  let σ : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) := starL' ℝ
  let T : ((Fin D → ℂ) →L[ℝ] ℝ) ≃L[ℝ] ((Fin D → ℂ) →L[ℝ] ℝ) :=
    σ.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have h1 : fderiv ℝ (fun y => φ (star y)) = T ∘ ((fderiv ℝ φ) ∘ σ) := by
    funext y
    have := σ.comp_right_fderiv (f := φ) (x := y)
    exact this
  rw [h1, T.comp_fderiv, σ.comp_right_fderiv]
  rfl

theorem cxHessian_comp_star (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    cxHessian (fun y => φ (star y)) z = (cxHessian φ (star z)).map (starRingEnd ℂ) := by
  ext i j
  have hs : ∀ i : Fin D, star (Pi.single i 1 : Fin D → ℂ) = Pi.single i 1 := fun i => by
    ext l; by_cases h : l = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hI : ∀ i : Fin D, star (Complex.I • (Pi.single i 1 : Fin D → ℂ)) =
      -(Complex.I • (Pi.single i 1 : Fin D → ℂ)) := fun i => by
    rw [star_smul, hs]; simp
  simp only [cxHessian, Matrix.map_apply, hess_comp_star, hs, hI, map_neg,
    ContinuousLinearMap.neg_apply, neg_neg]
  simp only [map_div₀, map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  have h4 : starRingEnd ℂ (4 : ℂ) = 4 := map_ofNat _ 4
  simp [h4]
  ring

theorem mixedDisc_map_conj (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mixedDisc, map_mul, map_sum, map_pow, map_neg, map_one, map_div₀, map_natCast]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.sum_apply]

theorem maDensity_comp_star (φ : Fin D → (Fin D → ℂ) → ℝ) (y : Fin D → ℂ) :
    maDensity (fun j y' => φ j (star y')) y = maDensity φ (star y) := by
  simp only [maDensity, cxHessian_comp_star, mixedDisc_map_conj, Complex.conj_re]

theorem star_measurePreserving :
    MeasurePreserving (star : (Fin D → ℂ) → (Fin D → ℂ)) volume volume := by
  have h : MeasurePreserving (starRingEnd ℂ : ℂ → ℂ) volume volume :=
    Complex.conjLIE.measurePreserving
  exact volume_preserving_pi (fun _ => h)

end Hess

section Pts

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_star (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval (star z) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  exact Subsingleton.elim _ _

theorem star_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    star z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa using hi⟩
  · rw [eval_star, hz.2 f hf, map_zero]

theorem segre_star (z : (Σ k, ι k) → ℂ) : segre (star z) = star (segre z) := by
  funext i
  simp [segre, map_prod]

theorem cons_star {e : ℕ} (y : Fin e → ℂ) :
    (Fin.cons 1 (star y) : Fin (e + 1) → ℂ) = star (Fin.cons 1 y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

variable {e : ℕ} {P : Ideal (MRing ι)}
  {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}

theorem star_mem_fibre (hΨ : ∀ w, Ψ' (star w) = star (Ψ w)) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y) : star w ∈ fibre P Ψ' (star y) := by
  obtain ⟨z, hz, rfl, h⟩ := hw
  exact ⟨star z, star_mem_mcPts hz, segre_star z, by rw [hΨ, h, cons_star]⟩

theorem differentiableAt_star_star {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [StarAddMonoid E] [StarModule ℂ E] [StarModule ℝ E]
    [ContinuousStar E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] [StarAddMonoid F] [StarModule ℂ F] [StarModule ℝ F] [ContinuousStar F]
    {γ : E → F} {x : E} (h : DifferentiableAt ℂ γ (star x)) :
    DifferentiableAt ℂ (fun y => star (γ (star y))) x := by
  have hD := h.hasFDerivAt
  set D := fderiv ℂ γ (star x)
  let sE : E →L[ℝ] E := (starL' ℝ : E ≃L[ℝ] E)
  let sF : F →L[ℝ] F := (starL' ℝ : F ≃L[ℝ] F)
  have hs : HasFDerivAt (star : E → E) sE x := sE.hasFDerivAt
  have hr : HasFDerivAt γ (D.restrictScalars ℝ) (star x) := hD.restrictScalars ℝ
  have hc : HasFDerivAt (fun y => star (γ (star y)))
      (sF.comp ((D.restrictScalars ℝ).comp sE)) x :=
    HasFDerivAt.comp x (g := (star : F → F)) sF.hasFDerivAt (hr.comp x hs)
  let cE : E →SL[starRingEnd ℂ] E := ((starL ℂ : E ≃L⋆[ℂ] E) : E →SL[starRingEnd ℂ] E)
  let cF : F →SL[starRingEnd ℂ] F := ((starL ℂ : F ≃L⋆[ℂ] F) : F →SL[starRingEnd ℂ] F)
  let D' : E →L[ℂ] F := cF.comp (D.comp cE)
  have : HasFDerivAt (fun y => star (γ (star y))) D' x :=
    hasFDerivAt_of_restrictScalars ℝ hc (by ext v; rfl)
  exact this.differentiableAt

theorem isSheet_star (hΨ : ∀ w, Ψ' (star w) = star (Ψ w)) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    IsSheet P Ψ' (star y) (star w) (fun y' => star (γ (star y'))) := by
  refine ⟨by simp only [star_star, segre_star, h.1], ?_⟩
  have ht : Tendsto (star : (Fin e → ℂ) → (Fin e → ℂ)) (𝓝 (star y)) (𝓝 y) := by
    have := (continuous_star (R := Fin e → ℂ)).tendsto (star y)
    simpa using this
  filter_upwards [ht.eventually h.2] with y' ⟨h1, h2, h3⟩
  refine ⟨differentiableAt_star_star h1, star_mem_mcPts h2, ?_⟩
  rw [segre_star, hΨ, h3, cons_star, star_star]

theorem sheetDensity_star {L : Fin e → HermLine ι} (hLc : ∀ j, IsConjInvariantH (L j))
    {B B' : HermLine ι} (hBB : ∀ z ∈ mcPts P, B'.h (star z) = B.h z)
    (hΨ : ∀ w, Ψ' (star w) = star (Ψ w)) (hΨ' : ∀ w, Ψ (star w) = star (Ψ' w)) {y : Fin e → ℂ}
    (hy : ∀ w γ γ', IsSheet P Ψ y w γ → IsSheet P Ψ y w γ' →
      logNorm B 1 (γ y) * maDensity (fun j y' => pot L j (γ y')) y =
        logNorm B 1 (γ' y) * maDensity (fun j y' => pot L j (γ' y')) y)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (pot L) (logNorm B 1) y w =
      sheetDensity P Ψ' (pot L) (logNorm B' 1) (star y) (star w) := by
  have back : ∀ γ, IsSheet P Ψ' (star y) (star w) γ →
      IsSheet P Ψ y w (fun y' => star (γ (star y'))) := fun γ h => by
    have := isSheet_star hΨ' h
    simpa only [star_star] using this
  unfold sheetDensity
  by_cases hex : ∃ γ, IsSheet P Ψ y w γ
  · have hex' : ∃ γ, IsSheet P Ψ' (star y) (star w) γ :=
      ⟨_, isSheet_star hΨ hex.choose_spec⟩
    rw [dite_eq_left hex, dite_eq_left hex', hy w _ _ hex.choose_spec (back _ hex'.choose_spec)]
    set γ := hex'.choose with hγ
    have hspec : IsSheet P Ψ' (star y) (star w) γ := hex'.choose_spec
    have hz : γ (star y) ∈ mcPts P := hspec.2.self_of_nhds.2.1
    have h1 : logNorm B 1 (star (γ (star (y)))) = logNorm B' 1 (γ (star y)) := by
      have h2 : B'.h (γ (star y)) = B.h (star (γ (star y))) := by
        have := hBB _ (star_mem_mcPts hz)
        rwa [star_star] at this
      simp [logNorm, h2]
    have h3 : maDensity (fun j y' => pot L j (star (γ (star y')))) y =
        maDensity (fun j y' => pot L j (γ y')) (star y) := by
      rw [← maDensity_comp_star]
      congr 1
      funext j y'
      simp only [pot]
      congr 1
      exact hLc j _
    rw [h1, h3]
  · have hex' : ¬ ∃ γ, IsSheet P Ψ' (star y) (star w) γ := fun ⟨γ, h⟩ => hex ⟨_, back γ h⟩
    rw [dite_eq_right hex, dite_eq_right hex']

end Pts

theorem ptsIntegralAt_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (B B' : HermLine ι), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ' (star w) = star (Ψ w)) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → B.a = 0 → IsSmoothHerm B → B'.a = 0 → IsSmoothHerm B' → (∀ z ∈ mcPts P, B'.h (star z) = B.h z) → IsGoodProj P Ψ' ∧ ptsIntegralAt P Ψ' (pot L) (logNorm B' 1) = ptsIntegralAt P Ψ (pot L) (logNorm B 1) := by
  intro K _ ι _ P e Ψ Ψ' L B B' hP hΨ hΨs hLs hLc hBa hBs _ _ hBB
  have hΨ2 : ∀ w, Ψ (star w) = star (Ψ' w) := fun w => by
    have := hΨs (star w)
    rw [star_star] at this
    rw [this, star_star]
  refine ⟨fun z hz h0 => ?_, ?_⟩
  · refine hΨ _ (star_mem_mcPts hz) ?_
    rw [segre_star, hΨ2, h0, star_zero]
  · have hsec : IsSectionOn P B 1 := by
      refine ⟨0, fun k => by simp [hBa], fun m hm k => ?_, ?_⟩
      · have : m = 0 := by
          have := MvPolynomial.support_one (R := ℤ) (σ := Σ k, ι k)
          rw [this] at hm
          simpa using hm
        simp [this]
      · exact fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    have hme : MeasurableEmbedding (star : (Fin e → ℂ) → (Fin e → ℂ)) :=
      (starL' ℝ : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)).toHomeomorph.measurableEmbedding
    unfold ptsIntegralAt
    rw [← star_measurePreserving.integral_comp hme]
    refine integral_congr_ae ?_
    filter_upwards [sheetIndep K ι P e Ψ L B 1 hP hΨ hLs hBs hsec] with y hy
    symm
    refine finsum_mem_eq_of_bijOn star ⟨fun w hw => star_mem_fibre hΨs hw, ?_, ?_⟩ fun w _ =>
      sheetDensity_star hLc hBB hΨs hΨ2 hy w
    · exact star_injective.injOn
    · intro w hw
      refine ⟨star w, ?_, star_star w⟩
      have := star_mem_fibre hΨ2 hw
      rwa [star_star] at this

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetryStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_integral_conjugation_symmetry : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (B B' : HermLine ι), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ' (star w) = star (Ψ w)) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → B.a = 0 → IsSmoothHerm B → B'.a = 0 → IsSmoothHerm B' → (∀ z ∈ mcPts P, B'.h (star z) = B.h z) → IsGoodProj P Ψ' ∧ ptsIntegralAt P Ψ' (pot L) (logNorm B' 1) = ptsIntegralAt P Ψ (pot L) (logNorm B 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegralAt_conj | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegralAt_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegralAt_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbedding
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def conjugateProjection {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) where
  toFun w := star (Ψ (star w))
  map_add' a b := by simp only [star_add, map_add (f := _)]
  map_smul' c w := by
    simp only [star_smul, map_smul, RingHom.id_apply, star_star]

theorem conjugateProjection_star {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ) : conjugateProjection Ψ (star w) = star (Ψ w) := by
  change star (Ψ (star (star w))) = _
  rw [star_star]

theorem isSectionOn_one_of_degree_zero {P : Ideal (MRing ι)} {d : ℕ} {A : HermLine ι}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P d) (hA : A.a = 0) : IsSectionOn P A 1 := by
  refine ⟨0, fun k => by simp [hA], ?_, ?_⟩
  · intro m hm k
    have hm0 : m = 0 := by
      classical
      have := MvPolynomial.support_one (R := ℤ) (σ := Σ k, ι k) ▸ hm
      simpa using this
    simp [hm0]
  · exact (Ideal.ne_top_iff_one P).1 hP.2.1.1.ne_top


open Classical in
theorem logNorm_one_eq_indicator {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω] {y : (Σ k, ι k) → Ω}
    {P : Ideal (MRing ι)} {tg : F →+* ℂ} {B : HermLine ι}
    (huniq : ∀ z ∈ mcPts P, ∃! s : F →+* ℂ, LiesOver y s z)
    (hB : ∀ z ∈ mcPts P, ∀ s : F →+* ℂ, LiesOver y s z → B.h z = if s = tg then Real.exp (-1) else 1) :
    ∀ z ∈ mcPts P, logNorm B 1 z = ({z | LiesOver y tg z}.indicator fun _ => (1 : ℝ)) z := by
  classical
  intro z hz
  obtain ⟨s, hs, hs'⟩ := huniq z hz
  have hone : ‖eval z (map (Int.castRingHom ℂ) (1 : MRing ι))‖ = 1 := by simp
  unfold logNorm
  rw [hone, hB z hz s hs]
  by_cases hst : s = tg
  · subst hst
    rw [Set.indicator_of_mem (show z ∈ {z | LiesOver y s z} from hs), if_pos rfl, one_div,
      Real.log_inv, Real.log_exp, neg_neg]
  · rw [Set.indicator_of_notMem (fun h => hst (hs' tg h).symm), if_neg hst]
    simp

end SlopeTestRemainingChoices

theorem conjugate_pieces_same_mass :
    ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (sg : F →+* ℂ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y (ComplexEmbedding.conjugate sg) z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hRes K _ ι _ Ω _ F _ _ _ y D L sg hP hL hC huniq
  classical
  have hpos : ∀ tg s : F →+* ℂ, 0 < (if s = tg then Real.exp (-1) else (1 : ℝ)) := by
    intro tg s
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  obtain ⟨B, hBa, hBs, hB⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun s => if s = sg then Real.exp (-1) else 1) (hpos sg) huniq
  obtain ⟨B', hBa', hBs', hB'⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun s => if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1)
    (hpos (ComplexEmbedding.conjugate sg)) huniq
  have hBv : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z →
      B.h z = if s = sg then Real.exp (-1) else 1 := fun z hz s hs => (hB z hz s hs).self_of_nhds
  have hBv' : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z →
      B'.h z = if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1 :=
    fun z hz s hs => (hB' z hz s hs).self_of_nhds
  rw [← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y)
      (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv'),
    ← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y)
      (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv)]
  by_cases hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (mCoordIdeal y) Ψ
  · obtain ⟨Ψ, hΨ⟩ := hex
    have hstar : ∀ z ∈ mcPts (mCoordIdeal y), B'.h (star z) = B.h z := by
      intro z hz
      obtain ⟨s, hs, -⟩ := huniq z hz
      have hzc : star z ∈ mcPts (mCoordIdeal y) := conjVec_mem_mcPts hz
      have hsc : LiesOver y (ComplexEmbedding.conjugate s) (star z) := liesOver_conjVec hs
      have hiff : ComplexEmbedding.conjugate s = ComplexEmbedding.conjugate sg ↔ s = sg :=
        ⟨fun h => by simpa using congrArg ComplexEmbedding.conjugate h, fun h => by rw [h]⟩
      rw [hBv' _ hzc _ hsc, hBv z hz s hs]
      simp only [hiff]
    obtain ⟨hΨ', hI⟩ := GlobalTheory.T.points_integral_conjugation_symmetry K ι (mCoordIdeal y) D Ψ (conjugateProjection Ψ) L B B' hP hΨ
      (conjugateProjection_star Ψ) hL hC hBa hBs hBa' hBs' hstar
    rw [ptsIntegral_eq_at hRes resBridge hP hΨ' hL hBs' (isSectionOn_one_of_degree_zero hP hBa'),
      ptsIntegral_eq_at hRes resBridge hP hΨ hL hBs (isSectionOn_one_of_degree_zero hP hBa), hI]
  · unfold ptsIntegral
    rw [dite_eq_right hex, dite_eq_right hex]

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbeddingStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_integral_unique_embedding : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (sg : F →+* ℂ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y (ComplexEmbedding.conjugate sg) z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.conjugate_pieces_same_mass | exact GlobalTheory.CompanionTheory.Ar.Giv.conjugate_pieces_same_mass | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.conjugate_pieces_same_mass <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

def fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) A.a

theorem fsOfDegree_a {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    (fsOfDegree A).a = A.a := rfl

theorem isSmoothHerm_fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    IsSmoothHerm (fsOfDegree A) :=
  GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs A.a

theorem isConjInvariantH_fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    IsConjInvariantH (fsOfDegree A) := by
  intro z
  simp only [fsOfDegree, HermLine.ofMetrics]
  exact Finset.prod_congr rfl fun k _ => by
    rw [GroundTheory.Heights₂.Heights.FubiniStudyConjugationInvariant.fsMetric_conj (fun i => z ⟨k, i⟩)]

theorem pieceDegree : ArithIntersectionSystemStatement → ResExistsStatement → PtsIntegrableStatement →
    GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.Statement := by
  intro hAr hRes hPts K _ ι _ Ω _ F _ _ _ y D L sg sg' har hbir hsm hone
  have hsm₀ : ∀ j, IsSmoothHerm (fsOfDegree (L j)) := fun j => isSmoothHerm_fsOfDegree _
  have hcj₀ : ∀ j, IsConjInvariantH (fsOfDegree (L j)) := fun j => isConjInvariantH_fsOfDegree _
  have hind : ∀ s : F →+* ℂ,
      ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)) =
        ptsIntegral (mCoordIdeal y) (pot fun j => fsOfDegree (L j))
          ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)) := fun s =>
    GlobalTheory.T.points_integral_independent_of_metric hAr hPts K ι Ω F y D L (fun j => fsOfDegree (L j)) s har hsm hsm₀
      (fun j => (fsOfDegree_a (L j)).symm) hone
  rw [hind sg, hind sg']
  exact GlobalTheory.T.unit_log_orthogonal_weight_constant F
    (fun s => ptsIntegral (mCoordIdeal y) (pot fun j => fsOfDegree (L j))
      ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)))
    (fun s => GlobalTheory.T.points_integral_unique_embedding hRes K ι Ω F y D _ s har hsm₀ hcj₀ hone)
    (fun θ => GlobalTheory.T.sum_over_embeddings_unit_invariance hAr hPts K ι Ω F y D _ θ har hbir hsm₀ hone) sg sg'

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolutionStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piece_degree_of_intersection_and_resolution : ArithIntersectionSystemStatement → ResExistsStatement → PtsIntegrableStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree | exact GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolution
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem embeddingPieces_of_resK (hA : ArithIntersectionSystemStatement)
    (hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) :
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement :=
  have hInt : PtsIntegrableStatement := GlobalTheory.T.points_integrable_of_resolution_statement hR
  have hRes : ResExistsStatement := GlobalTheory.T.resolution_exists_of_resolution_statement hR
  GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt)
    (GlobalTheory.T.piece_degree_of_intersection_and_resolution hA hRes hInt)

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolutionStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_pieces_of_intersection_and_resolution : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.embeddingPieces_of_resK | exact GlobalTheory.CompanionTheory.Ar.Giv.embeddingPieces_of_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.embeddingPieces_of_resK <;> assumption)
end
