module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerVolumeAlmostAll

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreIntegral
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem compact_finite_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → (∀ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C → m' (hermOf R σ T hT) C < ⊤) → ∀ C : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E), IsCompact C → m (hermOf R σ _ hT') C < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ t ht n T hT hT' R _ _ _ _ _ hR d b lam hlam m m₁ m' hm hm₁ hm' c hc hfin C hC
  obtain ⟨b1, b2, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hcm M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨b2 hJ.1, by rw [b1]; exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2⟩
  have hR' := hR
  obtain ⟨_, _, _, _, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have := hB n M
  have := hB 1 (M + 1)
  have := hB (n + 1) (M + 1)
  obtain ⟨hTG, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm _ _ hJ' R
  obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm R d b lam hlam
  have e0 : gramR R σ (blockOne (algebraMap F E t) J) (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    funext a a'
    simp only [gramR, hR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform, JR, blockOne, Fin.sum_univ_succ, hermScal, Fin.cons_zero, Fin.cons_succ,
      map_one, map_zero, one_mul, mul_one, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.map_apply,
      Matrix.of_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes t
  obtain ⟨s, sm, s1, s2⟩ := GlobalTheory.T.rank_one_gram_measurable_section F E σ hcm _ _ hJ' R hR (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) (by
    rw [e0, Matrix.det_unique]
    exact (ht.isUnit.map (algebraMap F R)).map (algebraMap R (R ⊗[F] E)))
  rw [e0] at s1 s2
  have hCm : MeasurableSet C := hC.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.scalar_extension_fibre_measure F E σ hcm M J hJ t ht n T hT hT' R hR d b lam hlam m m₁ m' hm hm₁ hm' c hc
    (C.indicator 1) (measurable_one.indicator hCm)
  rw [lintegral_indicator_one hCm] at hint
  have hc' : Continuous (consTup : (Fin n → Fin M → R ⊗[F] E) → _) := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun i => ?_) i
    exacts [continuous_const, continuous_const, continuous_const, continuous_apply_apply a i]

  let p : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → (Fin 1 → Fin (M + 1) → R ⊗[F] E) := fun X _ => X 0
  have hpc : Continuous p := continuous_pi fun _ => continuous_apply 0
  have hC₁ : IsCompact (p '' C) := hC.image hpc
  obtain ⟨C', hC', hs⟩ := s2 _ hC₁

  let r : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) := fun Y a i => Y a.succ i.succ
  have hrc : Continuous r := continuous_pi fun a => continuous_pi fun i => continuous_apply_apply a.succ i.succ
  have hD : IsCompact ((fun q : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      actW R σ _ q.1⁻¹ q.2) '' (C' ×ˢ C)) :=
    (hC'.prod hC).image ((hact (n + 1)).1.comp (continuous_fst.inv.prodMk continuous_snd))
  obtain ⟨K, hK, hKsub⟩ : ∃ K : Set (Fin n → Fin M → R ⊗[F] E), IsCompact K ∧
      ∀ h ∈ C', ∀ X, actW R σ _ h (consTup X) ∈ C → X ∈ K := by
    refine ⟨_, hD.image hrc, fun h hh X hX => ⟨consTup X, ⟨(h, _), ⟨hh, hX⟩, ?_⟩, rfl⟩⟩
    show actW R σ _ h⁻¹ (actW R σ _ h (consTup X)) = consTup X
    rw [← (hact _).2.2.1, inv_mul_cancel, (hact _).2.1]
  have hKf := hfin K hK
  have hfirst : ∀ (h : HA R σ (blockOne (algebraMap F E t) J)) (X : Fin n → Fin M → R ⊗[F] E),
      p (actW R σ _ h (consTup X)) = actW R σ _ h (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) := fun h X => rfl
  have hae : ∀ᵐ y ∂(m₁ (hermScal R σ (algebraMap F R t))),
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    refine measure_mono_null ?_ (hm₁.1 (hermScal R σ (algebraMap F R t)))
    intro y hy hy'
    exact hy hy'.1
  have hbound : ∀ᵐ y ∂(m₁ (hermScal R σ (algebraMap F R t))),
      Ψ y ≤ (p '' C).indicator (fun _ => m' (hermOf R σ T hT) K) y := by
    filter_upwards [hae] with y hy
    have hy' := s1 y hy
    have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => actW R σ _ (s y) (consTup X) :=
      ((hact _).1.comp (continuous_const.prodMk hc')).measurable
    have hΨy : Ψ y = m' (hermOf R σ T hT) {X | actW R σ _ (s y) (consTup X) ∈ C} := by
      have h1 := hΨ (s y)
      rw [hy'] at h1
      rw [h1]
      have h2 : (fun X : Fin n → Fin M → R ⊗[F] E =>
          C.indicator (1 : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (actW R σ _ (s y) (consTup X))) =
          {X | actW R σ _ (s y) (consTup X) ∈ C}.indicator 1 := by
        funext X
        simp [Set.indicator]
      rw [h2]
      exact lintegral_indicator_one (hmeas hCm)
    by_cases hyC : y ∈ p '' C
    · rw [Set.indicator_of_mem hyC, hΨy]
      exact measure_mono fun X hX => hKsub _ (hs y hyC hy) X hX
    · have hempty : {X | actW R σ _ (s y) (consTup X) ∈ C} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun X hX => hyC ⟨_, hX, ?_⟩
        rw [hfirst, hy']
      rw [hΨy, hempty, measure_empty]
      exact bot_le
  have hloc := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm _ _ hJ' R hR 1 _ _ _ (k1 1 (M + 1)) (k2 1) hm₁
    (hermScal R σ (algebraMap F R t))).1
  have hΨf : ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) < ⊤ := by
    refine (lintegral_mono_ae hbound).trans_lt ?_
    rw [lintegral_indicator_const hC₁.measurableSet]
    exact ENNReal.mul_lt_top hKf hC₁.measure_lt_top
  rw [hint]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hΨf

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreIntegralStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_extension_fibre_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → (∀ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C → m' (hermOf R σ T hT) C < ⊤) → ∀ C : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E), IsCompact C → m (hermOf R σ _ hT') C < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.compact_finite_block | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.compact_finite_block | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.compact_finite_block <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeUnramifiedAlmostAll
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeUnramifiedAlmostAll
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageGoodFree

theorem stage_good_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Fv F v) σ J n μ ν m → ∀ h : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m (hermOf (Fv F v) σ T hT) {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m (hermOf (Fv F v) σ T hT) (latV b v)) (actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [GoodTrans.good_trans F E σ hCM (M + 1) _ hND t ht d b,
    (LatRat.latV_rational F E σ hCM d b n M).2.2, (LatRat.latV_rational F E σ hCM d b 0 M).2.2]
    with v hv hv1 hv0
  intro μ ν m hμ hν hm h
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hBorel, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have := hBorel n M
  have hOpen := ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2
  obtain ⟨-, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hND (Fv F v)
  obtain ⟨-, -, -, -, -, hactJ⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (Fv F v)
  obtain ⟨-, hone, hmul, hgram⟩ := hact 1
  by_cases he : actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) ∈ latV b v
  · rw [Set.indicator_of_mem he]
    have he0 : (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) ∈ latV b v := by
      have h0 := (hv0 (fun a : Fin 0 => a.elim0)).2 (fun a => a.elim0)
      have hc : consTup (fun a : Fin 0 => a.elim0) =
          (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) := by
        funext a
        exact Fin.cases rfl (fun j => j.elim0) a
      rwa [hc] at h0
    obtain ⟨k, hk, hkl⟩ := hv _ _ he0 he (StageGood.gram_first (Fv F v) σ J t) (hgram h _)
    obtain ⟨ι, -, -, hrange, -, hcons⟩ := StabFirst.stab_first F E σ hCM M J hJ t ht (Fv F v)
    have hg : actW (Fv F v) σ _ (k⁻¹ * h) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) =
        (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) := by
      rw [hmul, ← hk, ← hmul, inv_mul_cancel, hone]
    obtain ⟨u, hu⟩ := (hrange _).2 hg
    have hh : h = k * ι u := by rw [hu]; group
    have hset : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} =
        actW (Fv F v) σ J u ⁻¹' latV b v := by
      ext X
      rw [Set.mem_ofPred_eq, Set.mem_preimage, hh]
      have := (hact (n + 1)).2.2.1 k (ι u) (consTup X)
      rw [this, hkl, hcons, hv1]
    have hcont : Continuous (actW (Fv F v) σ J u : (Fin n → Fin M → Fv F v ⊗[F] E) → _) :=
      (hactJ n).1.comp (Continuous.prodMk continuous_const continuous_id)
    rw [hset, ← Measure.map_apply hcont.measurable hOpen.measurableSet,
      GlobalTheory.T.local_gram_fibration_disintegration F E σ hCM M J hJ (Fv F v) hLoc n μ ν m hμ hν hm u]
  · rw [Set.indicator_of_notMem he]
    have hempty : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = ∅ := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hX => he (StageGood.first_mem b v σ _ h X hX)
    rw [hempty, measure_empty]

end GlobalTheory.CompanionTheory.SW.StageGoodFree
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeUnramifiedAlmostAllStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_volume_unramified_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Fv F v) σ J n μ ν m → ∀ h : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m (hermOf (Fv F v) σ T hT) {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m (hermOf (Fv F v) σ T hT) (latV b v)) (actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free | exact GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free | (intros; apply GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureExtensionByScalar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureExtensionByScalar
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta

section Tuples

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem linearIndependent_mulVec {M n : ℕ} (A : GL (Fin M) E) {X : Fin n → Fin M → E}
    (hX : LinearIndependent E X) :
    LinearIndependent E (fun a => (A : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) := by
    intro x y hxy
    have h : ∀ z : Fin M → E,
        ((A⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ ((A : Matrix (Fin M) (Fin M) E) *ᵥ z) = z := by
      intro z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      simp
    have hxy' : (A : Matrix (Fin M) (Fin M) E) *ᵥ x = (A : Matrix (Fin M) (Fin M) E) *ᵥ y := hxy
    rw [← h x, ← h y, hxy']
  exact hX.map' (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) (LinearMap.ker_eq_bot.2 hinj)

theorem linearIndependent_gact (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (gact σ g X) :=
  linearIndependent_mulVec (g : GL (Fin M) E) hX

theorem linearIndependent_consTup {M n : ℕ} (X : Fin n → Fin M → E) :
    LinearIndependent E (consTup X) ↔ LinearIndependent E X := by
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h c hc a
    have h1 := h (Fin.cons 0 c) (by
      rw [Fin.sum_univ_succ]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [consTup, Finset.sum_apply]
      · have := congrFun hc i
        simpa [consTup, Finset.sum_apply] using this) a.succ
    simpa using h1
  · intro h c hc
    have h0 : c 0 = 0 := by
      have := congrFun hc 0
      rw [Fin.sum_univ_succ] at this
      simpa [consTup, Finset.sum_apply] using this
    have h1 : ∀ a : Fin n, c a.succ = 0 := h (fun a => c a.succ) (by
      funext i
      have := congrFun hc i.succ
      rw [Fin.sum_univ_succ] at this
      simpa [consTup, Finset.sum_apply] using this)
    intro a
    exact Fin.cases h0 h1 a

theorem tsum_gact_frames (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) (T : Matrix (Fin n) (Fin n) E) (f : (Fin n → Fin M → E) → ℝ≥0∞) :
    ∑' X : framesE σ J T, f (gact σ g X.1) = ∑' X : framesE σ J T, f X.1 := by
  let e : framesE σ J T ≃ framesE σ J T :=
    { toFun := fun X => ⟨gact σ g X.1, linearIndependent_gact σ g X.2.1, by
        rw [gramE_gact]; exact X.2.2⟩
      invFun := fun X => ⟨gact σ g⁻¹ X.1, linearIndependent_gact σ g⁻¹ X.2.1, by
        rw [gramE_gact]; exact X.2.2⟩
      left_inv := fun X => Subtype.ext (gact_inv_gact σ g X.1)
      right_inv := fun X => Subtype.ext (gact_gact_inv σ g X.1) }
  exact e.tsum_eq (fun X => f X.1)

theorem tsum_block_frames (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) {t : E} (ht : t ≠ 0)
    (T : Matrix (Fin n) (Fin n) E)
    (rr : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t} →
      UJ (σ : E →+* E) (blockOne t J))
    (hrr : ∀ q, gact σ (rr q) q.1 = fun _ => Fin.cons 1 (fun _ => 0))
    (f : (Fin (n + 1) → Fin (M + 1) → E) → ℝ≥0∞) :
    ∑' Y : framesE σ (blockOne t J) (blockOne t T), f Y.1 =
      ∑' q : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t},
        ∑' X : framesE σ J T, f (gact σ (rr q)⁻¹ (consTup X.1)) := by
  have hrow : ∀ (q : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t})
      (X : Fin n → Fin M → E), gact σ (rr q)⁻¹ (consTup X) 0 = q.1 0 := by
    intro q X
    have h := congrArg (gact σ (rr q)⁻¹) (hrr q)
    rw [gact_inv_gact] at h
    exact (congrFun h 0).symm
  let m : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t} ×
      framesE σ J T → framesE σ (blockOne t J) (blockOne t T) :=
    fun p => ⟨gact σ (rr p.1)⁻¹ (consTup p.2.1),
      linearIndependent_gact σ _ ((linearIndependent_consTup _).2 p.2.2.1), by
      rw [gramE_gact, BlockAlg.gramE_consTup]
      exact congrArg (blockOne t) p.2.2.2⟩
  have hinj : Function.Injective m := by
    rintro ⟨q, X⟩ ⟨q', X'⟩ h
    have h1 : gact σ (rr q)⁻¹ (consTup X.1) = gact σ (rr q')⁻¹ (consTup X'.1) :=
      congrArg Subtype.val h
    have hq : q = q' := by
      apply Subtype.ext
      funext a
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      rw [← hrow q X.1, ← hrow q' X'.1, h1]
    subst hq
    have h2 := congrArg (gact σ (rr q)) h1
    rw [gact_gact_inv, gact_gact_inv] at h2
    exact Prod.ext rfl (Subtype.ext (consTup_injective h2))
  have hsurj : Function.Surjective m := by
    rintro ⟨Y, hYl, hY'⟩
    have hy : gramE σ (blockOne t J) (fun _ : Fin 1 => Y 0) = fun _ _ => t := by
      funext a b
      exact congrFun (congrFun hY' 0) 0
    let q : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t} := ⟨_, hy⟩
    have h0 : gact σ (rr q) Y 0 = Fin.cons 1 (fun _ => 0) := congrFun (hrr q) 0
    have hG : gramE σ (blockOne t J) (gact σ (rr q) Y) = blockOne t T := by
      rw [gramE_gact]; exact hY'
    obtain ⟨X, hX, hYX⟩ := BlockAlg.exists_consTup_of_gramE σ J ht T _ h0 hG
    have hXl : LinearIndependent E X := by
      rw [← linearIndependent_consTup, ← hYX]
      exact linearIndependent_gact σ _ hYl
    refine ⟨(q, ⟨X, hXl, hX⟩), Subtype.ext ?_⟩
    change gact σ (rr q)⁻¹ (consTup X) = Y
    rw [← hYX, gact_inv_gact]
  let e := Equiv.ofBijective m ⟨hinj, hsurj⟩
  rw [← e.tsum_eq (fun Y => f Y.1), ENNReal.tsum_prod']
  rfl

end Tuples


set_option maxHeartbeats 1000000 in
theorem theta_stage_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) 𝓕, IsHaarH F E σ (M + 1) _ μ → IsFDH F E σ (M + 1) _ μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ (Φ : (Fin (n + 1) → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, Φ (actW (AF F) σ _ h (consTup X)) ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J T))) → ∫⁻ X, Φ X ∂(thetaMeas σ _ μ 𝓕 (framesE σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T))) = ∫⁻ y, Ψ y ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) := by
  intro F E _ _ _ _ _ σ hσ M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ Φ Ψ hΦ hΨ hyp
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  have ht' : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨b1, b2, -, -⟩ := BlockAlg.block_alg F E σ hσ M J t
  have hJb : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨b2 hJ.1, by rw [b1]; exact mul_ne_zero ht' hJ.2⟩
  obtain ⟨tg, lc, sc, t2, bs, act⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ (M + 1) _ hJb (AF F)
  obtain ⟨tg₁, lc₁, sc₁, t2₁, bs₁, act₁⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := tg
  haveI := lc
  haveI := sc
  haveI := t2
  haveI := bs
  haveI := tg₁
  haveI := lc₁
  haveI := sc₁
  haveI := t2₁
  haveI := bs₁
  obtain ⟨-, -, -, -, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hσ (AF F)
  haveI := hB (n + 1) (M + 1)
  haveI := hB 1 (M + 1)
  haveI := hB n M
  haveI := hB n (M + 1)
  haveI : μ.IsHaarMeasure := hμ
  haveI : μ₁.IsHaarMeasure := hμ₁
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI hc : Countable (HFinIn (AF F) σ (blockOne (algebraMap F E t) J)) :=
    (rational_countable_discrete F E σ hσ (M + 1) _ hJb).1
  haveI hc₁ : Countable (HFinIn (AF F) σ J) := (rational_countable_discrete F E σ hσ M J hJ).1
  let Γ : Subgroup (HA (AF F) σ (blockOne (algebraMap F E t) J)) :=
    HFinIn (AF F) σ (blockOne (algebraMap F E t) J)
  let Γ₁ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI hc' : Countable Γ := hc
  haveI hc₁' : Countable Γ₁ := hc₁
  have hfin : μ₁ 𝓕₁ < ⊤ := ((finVol_unitaryGroup F E σ hσ M J hJ).2 μ₁ hμ₁).2 𝓕₁ h𝓕₁
  obtain ⟨ι, hιc, -, hιrange, hιF, hιcons⟩ :=
    StabFirst.stab_first F E σ hσ M J hJ t ht (AF F)
  have hmul : ∀ (g h : HA (AF F) σ (blockOne (algebraMap F E t) J)) {k : ℕ}
      (X : Fin k → Fin (M + 1) → AF F ⊗[F] E), actW (AF F) σ _ (g * h) X =
        actW (AF F) σ _ g (actW (AF F) σ _ h X) := fun g h {k} X => (act k).2.2.1 g h X
  have hW : ∀ q : {y : Fin 1 → Fin (M + 1) → E |
      gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t},
      ∃ g : UJ (σ : E →+* E) (blockOne (algebraMap F E t) J),
        gact σ g q.1 = fun _ => Fin.cons 1 (fun _ => 0) := by
    intro q
    have hq : gramE σ (blockOne (algebraMap F E t) J) q.1 = fun _ _ => algebraMap F E t := q.2
    obtain ⟨g, hg, hgy⟩ := GlobalTheory.T.witt_extension_global F E σ hσ (M + 1) _ hJb 1 q.1
      (fun _ => Fin.cons 1 (fun _ => 0)) (by rw [hq, gram_first])
      (by rw [hq]; intro h; exact ht' ((Matrix.det_fin_one (fun _ _ => algebraMap F E t : Matrix (Fin 1) (Fin 1) E)).symm.trans h))
    exact ⟨⟨g, hg⟩, funext hgy⟩
  choose rr hrr using hW
  let r := fun q => ratH (AF F) σ (blockOne (algebraMap F E t) J) (rr q)
  let φ : HA (AF F) σ (blockOne (algebraMap F E t) J) → ℝ≥0∞ := fun g =>
    ∑' X : framesE σ J T,
      Φ (actW (AF F) σ _ g⁻¹ (consTup (ratTup (AF F) X.1)))
  have hφ : Measurable φ := by
    refine Measurable.tsum fun X => hΦ.comp ?_
    have : Continuous fun g : HA (AF F) σ (blockOne (algebraMap F E t) J) =>
        actW (AF F) σ _ g⁻¹ (consTup (ratTup (AF F) X.1)) :=
      (act (n + 1)).1.comp (continuous_inv.prodMk continuous_const)
    exact this.measurable
  have hinv : ∀ u ∈ HFinIn (AF F) σ J, ∀ g, φ (ι u * g) = φ g := by
    intro u hu g
    obtain ⟨w, rfl⟩ := exists_ratH (AF F) σ J u hu
    have e : ∀ X : Fin n → Fin M → E,
        actW (AF F) σ _ (ι (ratH (AF F) σ J w) * g)⁻¹ (consTup (ratTup (AF F) X)) =
          actW (AF F) σ _ g⁻¹ (consTup (ratTup (AF F) (gact σ w⁻¹ X))) := by
      intro X
      rw [mul_inv_rev, hmul, ← map_inv ι, hιcons, ratH_inv, actW_ratH']
    change ∑' X : framesE σ J T,
        Φ (actW (AF F) σ _ (ι (ratH (AF F) σ J w) * g)⁻¹ (consTup (ratTup (AF F) X.1))) = φ g
    simp only [e]
    exact tsum_gact_frames σ w⁻¹ T (fun X => Φ (actW (AF F) σ _ g⁻¹ (consTup (ratTup (AF F) X))))
  have hΓ : ∀ u ∈ HFinIn (AF F) σ J, ι u ∈ HFinIn (AF F) σ (blockOne (algebraMap F E t) J) :=
    fun u hu => (mem_HFinIn_iff _ σ _ _).2 ((hιF u).2 ((mem_HFinIn_iff _ σ _ _).1 hu))
  have hfix : ∀ (g : UJ (σ : E →+* E) (blockOne (algebraMap F E t) J)),
      actW (AF F) σ _ (ratH (AF F) σ _ g)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → AF F ⊗[F] E)) =
      ratTup (AF F) (gact σ g (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → E))) := by
    intro g
    rw [← ratTup_first, actW_ratH']
  have hrinv : ∀ q, gact σ (rr q)⁻¹ (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → E)) = q.1 := by
    intro q
    rw [← hrr q, gact_inv_gact]
  have hstab : ∀ u, actW (AF F) σ _ (ι u)
      (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → AF F ⊗[F] E)) =
      fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → AF F ⊗[F] E) :=
    fun u => (hιrange (ι u)).1 ⟨u, rfl⟩
  have huniq : ∀ γ ∈ HFinIn (AF F) σ (blockOne (algebraMap F E t) J), ∃! q, ∃ u ∈ HFinIn (AF F) σ J,
      γ = ι u * r q := by
    intro γ hγ
    obtain ⟨g, rfl⟩ := exists_ratH (AF F) σ _ γ hγ
    have hy : gramE σ (blockOne (algebraMap F E t) J)
        (gact σ g⁻¹ (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → E))) =
        fun _ _ => algebraMap F E t := by
      rw [gramE_gact, gram_first]
    let q : {y : Fin 1 → Fin (M + 1) → E |
      gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t} := ⟨_, hy⟩
    have hrange : ratH (AF F) σ _ g * (r q)⁻¹ ∈ ι.range := by
      refine (hιrange _).2 ?_
      have e1 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
      rw [hmul, e1, hfix, hrinv, actW_ratH']
      change ratTup (AF F) (gact σ g (gact σ g⁻¹ _)) = _
      rw [gact_gact_inv, ratTup_first]
    obtain ⟨u, hu⟩ := hrange
    have hmemu : u ∈ HFinIn (AF F) σ J := by
      refine (mem_HFinIn_iff _ σ _ _).2 ((hιF u).1 ((mem_HFinIn_iff _ σ _ _).1 ?_))
      rw [hu]
      exact Subgroup.mul_mem _ (ratH_mem _ σ _ g) (Subgroup.inv_mem _ (ratH_mem _ σ _ (rr q)))
    refine ⟨q, ⟨u, hmemu, by rw [hu, inv_mul_cancel_right]⟩, ?_⟩
    rintro q' ⟨u', -, he⟩
    apply Subtype.ext
    apply ratTup_adele_injective (F := F)
    have e1 : actW (AF F) σ _ (ratH (AF F) σ _ g)⁻¹
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → AF F ⊗[F] E)) =
        ratTup (AF F) q.1 := by
      rw [ratH_inv, hfix]
    have e2 : actW (AF F) σ _ (ratH (AF F) σ _ g)⁻¹
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → AF F ⊗[F] E)) =
        ratTup (AF F) q'.1 := by
      have e3 : (r q')⁻¹ = ratH (AF F) σ _ (rr q')⁻¹ := ratH_inv _ σ _ _
      have h6 : (ratH (AF F) σ _ g)⁻¹ = (r q')⁻¹ * ι u'⁻¹ := by
        rw [he, mul_inv_rev]
        exact congrArg _ (map_inv ι u').symm
      rw [h6, hmul, hstab, e3, hfix, hrinv]
    rw [← e1, ← e2]
  have key := GlobalTheory.T.quotient_measure_tower _ _ ι hιc μ μ₁ Γ Γ₁ 𝓕 𝓕₁ h𝓕 h𝓕₁ hfin hΓ _ r (fun q => ratH_mem _ σ _ _) huniq φ hφ hinv
  have hA : ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J),
      ∑' Y : framesE σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T),
        Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y.1)) =
      ∑' q, φ (r q * h) := by
    intro h
    rw [tsum_block_frames σ J ht' T rr hrr (fun Y => Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y)))]
    refine tsum_congr fun q => tsum_congr fun X => ?_
    have e3 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
    rw [mul_inv_rev, hmul, e3, ← ratTup_consTup, actW_ratH']
  have hC : ∀ g : HA (AF F) σ (blockOne (algebraMap F E t) J),
      (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁ =
        Ψ (actW (AF F) σ _ g⁻¹ (fun _ => Fin.cons 1 (fun _ => 0))) := by
    intro g
    have hm : Measurable fun X : Fin n → Fin M → AF F ⊗[F] E =>
        Φ (actW (AF F) σ _ g⁻¹ (consTup X)) := by
      refine hΦ.comp ?_
      have : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
          actW (AF F) σ _ g⁻¹ (consTup X) :=
        (act (n + 1)).1.comp (continuous_const.prodMk continuous_consTup)
      exact this.measurable
    rw [hyp g⁻¹, GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ M J hJ μ₁ 𝓕₁ hμ₁ h𝓕₁ n _ _ hm]
    congr 1
    refine lintegral_congr fun u => tsum_congr fun X => ?_
    rw [mul_inv_rev, hmul, ← map_inv ι, hιcons]
  rw [GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ (M + 1) _ hJb μ 𝓕 hμ h𝓕 (n + 1) _ Φ hΦ,
    GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ (M + 1) _ hJb μ 𝓕 hμ h𝓕 1 _ Ψ hΨ]
  congr 1
  calc _ = ∫⁻ h in 𝓕, ∑' q, φ (r q * h) ∂μ := lintegral_congr hA
    _ = _ := key
    _ = _ := by
      refine lintegral_congr fun h => tsum_congr fun q => ?_
      have e3 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
      rw [hC, mul_inv_rev, hmul, e3, hfix, hrinv]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureExtensionByScalarStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_extension_by_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) 𝓕, IsHaarH F E σ (M + 1) _ μ → IsFDH F E σ (M + 1) _ μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ (Φ : (Fin (n + 1) → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, Φ (actW (AF F) σ _ h (consTup X)) ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J T))) → ∫⁻ X, Φ X ∂(thetaMeas σ _ μ 𝓕 (framesE σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T))) = ∫⁻ y, Ψ y ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta.theta_stage_frames | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta.theta_stage_frames | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta.theta_stage_frames <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOfLocalIdentities
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOfLocalIdentities
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt

open GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale

theorem exists_scale_cover {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fin n → Fin M → Fv F v ⊗[F] E)) (hC : IsCompact C) :
    ∃ (c : F) (hc : c ≠ 0), C ⊆ latV (scaleB b c hc) v := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set p : Fv F v := algebraMap F (Fv F v) π with hp
  have hval : Valued.v p = WithZero.exp (-1 : ℤ) := by
    have h0 : Valued.v (algebraMap F (Fv F v) π) = v.valuation F π :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
    rw [hp, h0, hπ]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hlt : Valued.v p < 1 := by
    rw [hval]
    decide
  have hpO : p ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hlt.le
  have hnorm : ‖p‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 hlt
  have hlim : Filter.Tendsto (fun k : ℕ => p ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hOopen : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  have hmem : ∀ (k : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E),
      X ∈ latV (scaleB b (π ^ k) (pow_ne_zero k hπ0)) v ↔
        ∀ a i l, p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          v.adicCompletionIntegers F := by
    intro k X
    simp only [latV, Set.mem_setOf_eq, repr_scaleB, map_pow, hp]
  let U : ℕ → Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun k => latV (scaleB b (π ^ k) (pow_ne_zero k hπ0)) v
  have hUo : ∀ k, IsOpen (U k) := fun k =>
    (((GlobalTheory.T.adelic_tuple_projections F E σ hcm d (scaleB b (π ^ k) (pow_ne_zero k hπ0)) n M).2.2.2.1 v).2)
  have hcov : C ⊆ ⋃ k, U k := by
    intro X _
    have h1 : ∀ a i l, ∀ᶠ k : ℕ in Filter.atTop,
        p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          (v.adicCompletionIntegers F : Set (Fv F v)) := by
      intro a i l
      have h2 : Filter.Tendsto
          (fun k : ℕ => p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l)
          Filter.atTop (𝓝 0) := by
        simpa using hlim.mul_const ((Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l)
      exact h2 (hOopen.mem_nhds (zero_mem _))
    have h3 : ∀ᶠ k : ℕ in Filter.atTop, ∀ a i l,
        p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          (v.adicCompletionIntegers F : Set (Fv F v)) :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i =>
        Filter.eventually_all.2 fun l => h1 a i l
    obtain ⟨k, hk⟩ := h3.exists
    exact Set.mem_iUnion.2 ⟨k, (hmem k X).2 hk⟩
  have hmono : Monotone U := monotone_nat_of_le_succ fun k X hX => by
    refine (hmem (k + 1) X).2 fun a i l => ?_
    have h := (hmem k X).1 hX a i l
    rw [pow_succ', mul_assoc]
    exact mul_mem hpO h
  obtain ⟨k, hk⟩ := hC.elim_directed_cover U hUo hcov hmono.directed_le
  exact ⟨π ^ k, pow_ne_zero k hπ0, hk⟩

theorem fibre_compact_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J T hT → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) m → ∀ C : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact C → m (hermOf (Fv F v) σ T hT) C < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ n T hT hSW d b laminf lam hinf hv v m hm C hC
  classical
  obtain ⟨c, hc, hCc⟩ := exists_scale_cover σ hcm b n M v C hC
  set b' := scaleB b c hc with hb'
  have hrV : ∀ w, IsLocR (Fv F w) := GlobalTheory.T.completion_is_local_ring F
  haveI : ∀ w, BorelSpace (Fv F w) := fun _ => ⟨rfl⟩
  obtain ⟨k, hk0, hk⟩ := coord_rescale σ hcm J (Fv F v) (hrV v) b b' (lam v) (hv v).1 n m hm
  have hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hWi, hHi⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Ainf F) _ b' laminf hinf.1
  obtain ⟨minf, hminf⟩ := GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hcm M n J hJ (coordW (Ainf F) b' laminf n M)
    (coordHerm (Ainf F) σ b' laminf n) (hWi n M) (hHi n)
  have hfV : ∀ w : HeightOneSpectrum (𝓞 F), ∃ fib : HermR (Fv F w) σ n → Measure (Fin n → Fin M → Fv F w ⊗[F] E),
      IsGramFibFree (Fv F w) σ J n (coordW (Fv F w) b' (lam w) n M) (coordHerm (Fv F w) σ b' (lam w) n) fib := fun w => by
    have := PI.VolStabS.secondCountable_Fv F w
    have := PI.VolStabS.locallyCompact_Fv F w
    obtain ⟨-, hWv, hHv⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F w) _ b' (lam w) (hv w).1
    exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J w n hcm hJ _ _ (hWv n M) (hHv n)
  choose m₀ hm₀ using hfV
  let m₂ : ∀ w : HeightOneSpectrum (𝓞 F), HermR (Fv F w) σ n → Measure (Fin n → Fin M → Fv F w ⊗[F] E) :=
    Function.update m₀ v (fun S => k • m S)
  have hm₂v : m₂ v = fun S => k • m S := Function.update_self _ _ _
  have hm₂ : ∀ w, IsGramFibFree (Fv F w) σ J n (coordW (Fv F w) b' (lam w) n M)
      (coordHerm (Fv F w) σ b' (lam w) n) (m₂ w) := fun w => by
    by_cases h : w = v
    · subst h
      rw [hm₂v]
      exact hk
    · have : m₂ w = m₀ w := Function.update_of_ne h _ _
      rw [this]
      exact hm₀ w
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁
  have hE := hSW d b' laminf lam hinf hv μ₁ 𝓕₁ hμ₁ h𝓕₁ minf m₂ hminf hm₂
  have h1 : (k • m (hermOf (Fv F v) σ T hT)) (latV b' v) < ⊤ := by
    have h2 : m₂ v (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := hE.1 v
    rwa [hm₂v] at h2
  have h3 : m (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := by
    by_contra hx
    have hs : (k • m (hermOf (Fv F v) σ T hT)) (latV b' v) =
        (k : ℝ≥0∞) * m (hermOf (Fv F v) σ T hT) (latV b' v) := by
      rw [Measure.smul_apply]
      rfl
    rw [hs, not_lt_top_iff.1 hx, ENNReal.mul_top (by exact_mod_cast hk0)] at h1
    exact lt_irrefl _ h1
  exact (measure_mono hCc).trans_lt h3

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOfLocalIdentitiesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_product_of_local_identities : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J T hT → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) m → ∀ C : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact C → m (hermOf (Fv F v) σ T hT) C < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt.fibre_compact_lt_top | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt.fibre_compact_lt_top | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt.fibre_compact_lt_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeExtendByScalarBlock
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso

theorem free_inf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)) (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ m, IsGramFibFree (Ainf F) σ J n (coordW (Ainf F) b lam n M) (coordHerm (Ainf F) σ b lam n) m := by
  have hB : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) _ b lam hlam
  exact GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hCM M n J hJ _ _ (hW n M) (hH n)

theorem free_v {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ m, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m := by
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  have hB : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) _ b lam hlam
  exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J v n hCM hJ _ _ (hW n M) (hH n)

theorem good_mass_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ c : ℝ≥0, (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c • coordK (Fv F v) b lam → m (hermOf (Fv F v) σ _ hT') (latV b v) = (c : ℝ≥0∞) ^ n * (m' (hermOf (Fv F v) σ T hT) (latV b v) * m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hT' d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [GlobalTheory.T.local_volume_unramified_almost_all F E σ hCM M J hJ t ht n T hT d b] with v hv
  intro lam hlam m m₁ m' hm hm₁ hm' c hc
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have hH := coord_measures_haar F E σ hCM (Fv F v) d b lam hlam
  obtain ⟨hring, -, -, -, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have hlat : ∀ n' M' : ℕ, MeasurableSet (latV b v : Set (Fin n' → Fin M' → Fv F v ⊗[F] E)) := by
    intro n' M'
    haveI := hB n' M'
    exact ((MeasProj.proj_props F E σ hCM d b n' M').2.2.2.1 v).2.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.scalar_extension_fibre_measure F E σ hCM M J hJ t ht n T hT hT' (Fv F v) hLoc d b lam hlam
    m m₁ m' hm hm₁ hm' c hc ((latV b v).indicator 1) (measurable_one.indicator (hlat _ _))
  set A := m' (hermOf (Fv F v) σ T hT) (latV b v) with hA
  have hae : Ψ =ᵐ[m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))] (latV b v).indicator (fun _ => A) := by
    filter_upwards [mem_ae_iff.2 (hm₁.1 (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hg : gramR (Fv F v) σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) =
        gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y :=
      (StageGood.gram_first (Fv F v) σ J t).trans hy1.symm
    obtain ⟨h, rfl⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hCM (M + 1) _ hND (Fv F v) 1 _ y hg
      (by rw [hg]; exact hy2)
    rw [hΨ h]
    haveI := hB n M
    haveI := hB (n + 1) (M + 1)
    have hS : MeasurableSet {X : Fin n → Fin M → Fv F v ⊗[F] E |
        actW (Fv F v) σ _ h (consTup X) ∈ latV b v} :=
      (GoodMass.continuous_act_consTup (Fv F v) hring σ _ h).measurable (hlat _ _)
    have hfun : (fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
        (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ h (consTup X))) =
        {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v}.indicator 1 := by
      funext X
      rfl
    rw [hfun, lintegral_indicator_one hS, hv _ _ m' (hH.2.1 n M) (hH.2.2 n) hm' h]
  rw [← lintegral_indicator_one (hlat _ _), hint, lintegral_congr_ae hae,
    lintegral_indicator_const (hlat _ _)]

theorem summable_mul_sub_one {ι : Type} {x y : ι → ℝ} (hx : Summable fun i => |x i - 1|)
    (hy : Summable fun i => |y i - 1|) : Summable fun i => |x i * y i - 1| := by
  have ht : ∀ᶠ i in Filter.cofinite, |y i - 1| < 1 := by
    have := hy.tendsto_cofinite_zero
    exact this.eventually (gt_mem_nhds one_pos)
  refine Summable.of_norm_bounded_eventually (g := fun i => 2 * |x i - 1| + |y i - 1|)
    ((hx.mul_left 2).add hy) ?_
  filter_upwards [ht] with i hi
  have e : x i * y i - 1 = (x i - 1) * (y i - 1) + (x i - 1) + (y i - 1) := by ring
  rw [Real.norm_eq_abs, abs_abs, e]
  have h1 : |(x i - 1) * (y i - 1)| ≤ |x i - 1| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hi.le
  calc _ ≤ |(x i - 1) * (y i - 1) + (x i - 1)| + |y i - 1| := abs_add_le _ _
    _ ≤ |(x i - 1) * (y i - 1)| + |x i - 1| + |y i - 1| := by gcongr; exact abs_add_le _ _
    _ ≤ 2 * |x i - 1| + |y i - 1| := by linarith

theorem aniso_step : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ n : ℕ, 2 * n + 1 < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), (framesE σ J T).Nonempty → SWFree σ J T hT → SWFree σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT' := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n hn T hT hT' _ hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have hta : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨hdetb, hhermb, -, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩

  obtain ⟨m₁inf, hm₁inf⟩ := Step.loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1
  obtain ⟨m'inf, hm'inf⟩ := free_inf σ hCM J hJ b laminf hinf.1 n
  choose m₁ hm₁ using fun v => Step.loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1
  choose m' hm' using fun v => free_v σ hCM J hJ b v (lam v) (hlam v).1 n
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁

  obtain ⟨cinf, c, hc, hcinf, hcv⟩ := GlobalTheory.T.scalar_multiplication_euler_product F E σ hCM (algebraMap F E t) hta
  have hKi : (coordK (Ainf F) b laminf).map (fun y => inclR (Ainf F) (algebraMap F E t) * y) =
      cinf • coordK (Ainf F) b laminf := by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLi
    exact hcinf _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1).1
  have hKv : ∀ v, (coordK (Fv F v) b (lam v)).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) =
      c v • coordK (Fv F v) b (lam v) := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    exact hcv v _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1).1
  obtain ⟨-, -, -, -, -, -, -, S₃, hS₃⟩ := GlobalTheory.T.unit_product_closure_properties F cinf 1 c (fun _ => 1) hc ⟨by simp, by simp⟩

  have hE' := hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf (fun v => m' v) hm'inf hm'
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun a b => by simp [T1]
  have hdet1 : T1.det ≠ 0 := by rw [Matrix.det_fin_one]; exact hta
  have hE₁ := GlobalTheory.T.siegel_weil_measure_rank_one F E σ hCM (M + 1) _ hJ' (by omega) T1 hT1 hdet1 d b laminf lam hinf hlam μ 𝓕 hμ h𝓕
    m₁inf m₁ hm₁inf hm₁
  obtain ⟨β, hβ1, -, hβ2⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hCM T1 hT1
  have hβ : β = t := (algebraMap F E).injective (congrFun (congrFun hβ1 0) 0).symm
  rw [hβ] at hβ2
  simp only [hβ2] at hE₁
  obtain ⟨-, hsum₁, S₁, hS₁⟩ := hE₁
  have hsum' := hE'.2.1
  have hG := good_mass_free F E σ hCM M J hJ t ht n T hT hT' d b
  have hgood₁ : ∀ v, m v (hermOf (Fv F v) σ _ hT') (latV b v) < ⊤ := fun v =>
    GlobalTheory.T.scalar_extension_fibre_integral F E σ hCM M J hJ t ht n T hT hT' (Fv F v) (hLv v) d b (lam v) (hlam v).1 (m v) (m₁ v) (m' v)
      (hm v) (hm₁ v) (hm' v) (c v) (hKv v)
      (GlobalTheory.T.siegel_weil_product_of_local_identities F E σ hCM M J hJ n T hT hSW d b laminf lam hinf hlam v (m' v) (hm' v)) _
      ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b (n + 1) (M + 1)).2.2.2.1 v).1
  have hgood₂ : Summable fun v => |(m v (hermOf (Fv F v) σ _ hT') (latV b v)).toReal - 1| := by
    have hP := summable_mul_sub_one hsum' hsum₁
    refine (summable_congr_cofinite ?_).1 hP
    filter_upwards [hG, hc.1] with v hv hcv1
    rw [hv (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v), hcv1]
    simp [ENNReal.toReal_mul]
  refine ⟨hgood₁, hgood₂, ?_⟩
  obtain ⟨S₂, hS₂⟩ := Step.theta_hypothesis F E σ hCM M J hJ t ht n d b _ _ _ hE'
  have hSG := GlobalTheory.T.local_volume_unramified_almost_all F E σ hCM M J hJ t ht n T hT d b
  refine ⟨S₁ ∪ S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hG).toFinset ∪ (Filter.eventually_cofinite.1 hSG).toFinset,
    fun S hS φinf φ hφinf hφ => ?_⟩
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have hS3 : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have hS4 : (Filter.eventually_cofinite.1 hG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inl (Or.inr hx))
  have hS5 : (Filter.eventually_cofinite.1 hSG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inr hx)
  obtain ⟨hc1, hc2⟩ := hS₃ S hS3
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := GlobalTheory.T.scalar_extension_fibre_measure F E σ hCM M J hJ t ht n T hT hT' (Ainf F) hLi d b
    laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf
  choose Ψ hΨm hΨ1 hΨ2 using fun v => GlobalTheory.T.scalar_extension_fibre_measure F E σ hCM M J hJ t ht n T hT hT' (Fv F v) (hLv v) d b
    (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (φ v) (hφ v)
  have hHv : ∀ v, (coordW (Fv F v) b (lam v) n M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) n).IsAddHaarMeasure := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact ⟨hh.2.1 n M, hh.2.2 n⟩
  have hHyp := hS₂ S hS2 φinf φ Ψinf Ψ hφinf hφ hΨinf1 hΨ1 (fun v hv g =>
    Step.of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g)
  set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) with hτ'
  have hPm : Measurable (pureL b S Ψinf Ψ) := GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b 1 (M + 1) S Ψinf Ψ hΨinfm hΨm
  have hth := GlobalTheory.T.theta_measure_extension_by_scalar F E σ hCM M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ)
    (fun y => τ' * pureL b S Ψinf Ψ y) (GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b (n + 1) (M + 1) S φinf φ hφinf hφ)
    (hPm.const_mul τ') hHyp
  have hone := hS₁ S hS1 Ψinf Ψ hΨinfm hΨm
  rw [hth, lintegral_const_mul _ hPm]
  have hone' : ∫⁻ X, pureL b S Ψinf Ψ X ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) = _ := hone
  rw [hone']
  have hprod : (∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ _ hT'))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ _ hT')) =
      (∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))) := by
    have hone2 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by exact_mod_cast hc2
    rw [hΨinf2, Finset.prod_congr rfl (fun v _ => hΨ2 v), Finset.prod_mul_distrib, Finset.prod_pow]
    calc _ = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) ^ n * ((∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))) := by rw [mul_pow]; ring
      _ = _ := by rw [hone2, one_pow, one_mul]
  have htail : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal) =
      τ' * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal) := by
    have hA := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal)
      (hsum'.subtype _)
    have hB := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal)
      (hsum₁.subtype _)
    have hcong : ∀ v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal =
        (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal * (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal := fun v => by
      rw [Step.of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]
      simp [ENNReal.toReal_mul]
    rw [tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]
  rw [hprod, htail]
  simp only [ENNReal.coe_one, one_mul]
  ring

end GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeExtendByScalarBlockStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilFree_extend_by_scalar_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ n : ℕ, 2 * n + 1 < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), (framesE σ J T).Nonempty → SWFree σ J T hT → SWFree σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT' := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso.aniso_step | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso.aniso_step | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso.aniso_step <;> assumption)
end
