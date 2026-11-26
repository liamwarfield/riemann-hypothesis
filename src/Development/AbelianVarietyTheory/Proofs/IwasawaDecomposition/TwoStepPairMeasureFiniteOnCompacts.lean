module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompacts
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompacts
noncomputable section

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct NNReal ENNReal

theorem tsfin_compact_lift {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X] (x : X)
    (hc : IsClosed (MulAction.orbit G x)) {K : Set X} (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ ∀ y ∈ K, (∃ g : G, g • x = y) → ∃ g ∈ C, g • x = y := by
  haveI : LocallyCompactSpace (MulAction.orbit G x) := hc.locallyCompactSpace
  haveI : ContinuousSMul G (MulAction.orbit G x) :=
    ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  let x₀ : MulAction.orbit G x := ⟨x, MulAction.mem_orbit_self x⟩
  have ho : IsOpenMap fun g : G => g • x₀ := isOpenMap_smul_of_sigmaCompact x₀
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit G x)) :=
    hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  let ex := CompactExhaustion.choice G
  obtain ⟨n, hn⟩ := hK'.elim_directed_cover (fun n : ℕ => (fun g : G => g • x₀) '' interior (ex n))
    (fun n => ho _ isOpen_interior)
    (by
      rintro ⟨y, g, rfl⟩ _
      obtain ⟨n, hn⟩ := ex.exists_mem g
      exact Set.mem_iUnion.2 ⟨n + 1, g, ex.subset_interior_succ n hn, rfl⟩)
    (Monotone.directed_le fun a b hab => Set.image_mono (interior_mono (ex.subset hab)))
  refine ⟨ex n, ex.isCompact n, fun y hy hg => ?_⟩
  obtain ⟨g, hg1, hg2⟩ := hn (a := ⟨y, hg⟩) hy
  exact ⟨g, interior_subset hg1, congrArg Subtype.val hg2⟩

theorem tsfin_hform_mulVec {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J g : Matrix (Fin n) (Fin n) A)
    (hg : Formalism.UG.cT σ g * J * g = J) (x : Fin n → A) :
    Formalism.UG.hform σ J (g.mulVec x) (g.mulVec x) = Formalism.UG.hform σ J x x := by
  have key : ∀ (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A),
      Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ J.mulVec y := by
    intro J x y
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : σ ∘ g.mulVec x = (g.map σ).mulVec (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ g x i
  rw [key, key, h2]
  conv_rhs => rw [← hg]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec (M := Formalism.UG.cT σ g), Matrix.dotProduct_mulVec (σ ∘ x),
    Formalism.UG.cT, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tsfin_q_smul (g : HA R σ J) (y : Fin 1 → Fin M → R ⊗[F] E) :
    qR R σ J ((g • y) 0) = qR R σ J (y 0) := by
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J :=
    Subtype.property (p := fun x => x ∈ HR R σ J) g
  unfold qR hR
  rw [← tsfin_hform_mulVec _ _ _ hg (y 0)]
  rfl

theorem tsfin_q_rat [CharZero F] (h2 : Module.finrank F E = 2) (x : Fin 1 → Fin M → E) (a : F)
    (hx : hE σ J (x 0) (x 0) = algebraMap F E a) :
    qR R σ J (ratTup (F := F) R x 0) = algebraMap F R a := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have h : hR R σ J (ratTup (F := F) R x 0) (ratTup (F := F) R x 0) =
      (1 : R) ⊗ₜ[F] algebraMap F E a := by
    rw [← hx]
    simp [hR, hE, Formalism.UG.hform, ratTup, JR, inclR, sigR, TensorProduct.tmul_sum]
  rw [qR, h, qloc_trace_tmul, Algebra.trace_algebraMap, h2, one_mul, ← map_mul]
  congr 1
  simp

theorem tsfin_q_cont [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun y : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (y 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (sigR R σ) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  unfold qR hR Formalism.UG.hform
  fun_prop

end

theorem twoStep_finite_on_compacts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → TwoStep R σ J x B m m' N → IsFiniteMeasureOnCompacts N := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR M J x a B J' m m' N hS hO hm hm' _ hT
  classical
  obtain ⟨hJ, ha, hx, -, hJ', hJ'nd⟩ := hS
  have hq := tsfin_q_rat R σ J hcm.2.2.1 x a hx
  have hu : IsUnit (algebraMap F R a) := (IsUnit.mk0 a ha).map _
  have hc : IsClosed (MulAction.orbit (HA R σ J) (ratTup (F := F) R x)) := by
    have : MulAction.orbit (HA R σ J) (ratTup (F := F) R x) =
        {y | qR R σ J (y 0) = algebraMap F R a} := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact (tsfin_q_smul R σ J g _).trans hq
      · intro hy
        exact GlobalTheory.GaugeWittLoc.exists_smul_eq F E σ hcm R hR (M + 1) J hJ _ _ y hu hq hy
    rw [this]
    exact isClosed_eq (tsfin_q_cont R σ J) continuous_const
  refine ⟨fun K hK => ?_⟩
  let K₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E) := (fun X _ => X 0) '' K
  have hK₁ : IsCompact K₁ := hK.image (by fun_prop)
  obtain ⟨C, hC, hCK⟩ := tsfin_compact_lift _ hc hK₁
  let L : Matrix (Fin M) (Fin (M + 1)) E := J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)
  have hL : L * B = 1 := by
    rw [Matrix.mul_assoc, ← hJ']
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hJ'nd.2)
  have hL' : L.map (inclR (F := F) R) * B.map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  let K' : Set (Fin 1 → Fin M → R ⊗[F] E) :=
    (fun p : HA R σ J × (Fin 2 → Fin (M + 1) → R ⊗[F] E) => fun _ =>
      (L.map (inclR (F := F) R)).mulVec ((p.1⁻¹ • p.2) 1)) '' (C ×ˢ K)
  have hK' : IsCompact K' := (hC.prod hK).image (continuous_pi fun _ =>
    continuous_const.matrix_mulVec ((continuous_apply 1).comp (continuous_fst.inv.smul continuous_snd)))
  let s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J := fun y =>
    if h : ∃ g ∈ C, g • ratTup (F := F) R x = y then h.choose
    else if h' : ∃ g : HA R σ J, g • ratTup (F := F) R x = y then h'.choose else 1
  have hs : IsSec R σ J x s := by
    intro y hy
    by_cases h : ∃ g ∈ C, g • ratTup (F := F) R x = y
    · simp only [s, dif_pos h]
      exact h.choose_spec.2
    · simp only [s, dif_neg h, dif_pos hy]
      exact hy.choose_spec
  have hsC : ∀ y ∈ K₁, (∃ g : HA R σ J, g • ratTup (F := F) R x = y) → s y ∈ C := by
    intro y hy hg
    have h := hCK y hy hg
    simp only [s, dif_pos h]
    exact h.choose_spec.1
  have h1 := hT (K.indicator 1) (measurable_one.indicator hK.measurableSet) s hs
  rw [lintegral_indicator_one hK.measurableSet] at h1
  rw [h1]
  have hae : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F := F) R x = y := hO
  calc _ ≤ ∫⁻ y, K₁.indicator (fun _ => m' K') y ∂m := by
        refine lintegral_mono_ae (hae.mono fun y hy => ?_)
        by_cases hyK : y ∈ K₁
        · rw [Set.indicator_of_mem hyK, ← lintegral_indicator_one hK'.measurableSet]
          refine lintegral_mono fun y' => ?_
          by_cases hp : pairOf R σ J B y (s y) y' ∈ K
          · have : y' ∈ K' := by
              refine ⟨(s y, pairOf R σ J B y (s y) y'), ⟨hsC y hyK hy, hp⟩, ?_⟩
              funext i
              have e : ((s y)⁻¹ • pairOf R σ J B y (s y) y') 1 =
                  ((s y)⁻¹ • s y • fun _ : Fin 1 => (B.map (inclR (F := F) R)).mulVec (y' 0)) 0 := rfl
              simp only
              rw [e, inv_smul_smul, Matrix.mulVec_mulVec, hL', Matrix.one_mulVec,
                Subsingleton.elim i 0]
            simp [Set.indicator_of_mem hp, Set.indicator_of_mem this]
          · simp [Set.indicator_of_notMem hp]
        · have : ∀ y', pairOf R σ J B y (s y) y' ∉ K := fun y' hp =>
            hyK ⟨_, hp, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩
          simp [Set.indicator_of_notMem (this _)]
    _ < ⊤ := by
        rw [lintegral_indicator_const hK₁.measurableSet]
        exact ENNReal.mul_lt_top hK'.measure_lt_top hK₁.measure_lt_top

end GlobalTheory.GaugeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompactsStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoStep_pair_measure_finite_on_compacts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → TwoStep R σ J x B m m' N → IsFiniteMeasureOnCompacts N := by
  first | exact @GlobalTheory.GaugeEx.twoStep_finite_on_compacts | exact GlobalTheory.GaugeEx.twoStep_finite_on_compacts | (intros; apply GlobalTheory.GaugeEx.twoStep_finite_on_compacts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationality
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationality
noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct Pointwise

section Span

variable {D : D7} {n : ℕ}

theorem ratSpan_smul (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    D.what₂.embLL r • P ∈ RatSpan D lam := by
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r', f, hf, rfl⟩ := hp
    exact AddSubgroup.subset_closure ⟨r * r', f, hf, by rw [smul_smul, map_mul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_embLL_smul {σ : Type} (r : D.what₂.LL) (F : MvPolynomial σ D.what₂.LL) :
    MvPolynomial.map D.what₂.embLL (r • F) = D.what₂.embLL r • MvPolynomial.map D.what₂.embLL F := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

theorem exists_of_mem_ratSpan (lam : D.what₂.Tau → DomWeight n)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    ∃ F ∈ Formalism.L2.DIV.VV D.what₂.LL lam, MvPolynomial.map D.what₂.embLL F = P := by
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    refine ⟨r • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb D.what₂.LL τ (MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)),
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩), ?_⟩
    · exact Formalism.GradedWeylDivisibility.weylLeDual _ n n le_rfl _ (Formalism.L2.Col.natW_anti (lam τ)) (Formalism.L2.Col.map_mem_weyl le_rfl _ _ (hf τ))
    · rw [map_embLL_smul, Formalism.L2.Col.map_ten]
      congr 2
      funext τ
      rw [MvPolynomial.map_map]
      congr 2
      exact RingHom.ext_int _ _
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, rfl⟩ := hx
    obtain ⟨G, hG, rfl⟩ := hy
    exact ⟨F + G, add_mem hF hG, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact ⟨-F, neg_mem hF, map_neg _ _⟩

theorem map_mem_ratSpan (lam : D.what₂.Tau → DomWeight n)
    {F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL} (hF : F ∈ Formalism.L2.DIV.VV D.what₂.LL lam) :
    MvPolynomial.map D.what₂.embLL F ∈ RatSpan D lam := by
  classical
  haveI : CharZero D.what₂.LL := D.what₂.embLL.charZero
  let S : D.what₂.Tau → Set (MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) := fun τ =>
    Set.range fun w : List (Fin n × Fin n × ℕ) =>
      MvPolynomial.rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord D.what₂.LL w (Formalism.GradedWeylDivisibility.hw D.what₂.LL le_rfl (lam τ).natW))
  have hle : Formalism.L2.DIV.VV D.what₂.LL lam ≤ Submodule.span D.what₂.LL (∏ τ, S τ) := by
    unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h1 : ∀ τ, MvPolynomial.rename (Prod.mk τ) (f τ) ∈ Submodule.span D.what₂.LL (S τ) := by
      intro τ
      have hf' : f τ ∈ delSq D.what₂.LL n (lam τ) := by
        rw [← Formalism.L2.Col.nablaSq_eq_delSq]; exact hf τ
      have h := Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := D.what₂.LL)
        (Prod.mk τ : Fin n × Fin n → D.what₂.Tau × Fin n × Fin n)).toLinearMap) hf'
      unfold delSq Formalism.GradedWeylDivisibility.weyl at h
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact h
    rw [← Submodule.prod_span]
    exact Formalism.L2.Col.prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
  have hF' := hle hF
  clear hF
  induction hF' using Submodule.span_induction with
  | mem x hx =>
    rw [Set.mem_finsetProd] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ),
        MvPolynomial.rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord D.what₂.LL w (Formalism.GradedWeylDivisibility.hw D.what₂.LL le_rfl (lam τ).natW)) = g τ :=
      fun τ => hg (Finset.mem_univ τ)
    choose w hw using hg'
    refine AddSubgroup.subset_closure ⟨1, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (w τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
      fun τ => Submodule.subset_span ⟨w τ, rfl⟩, ?_⟩
    rw [map_one, one_smul, map_prod, ten]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← hw τ, MvPolynomial.map_rename, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map,
      ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_embLL_smul]; exact ratSpan_smul lam c hx

theorem ratSpan_blockAct (lam : D.what₂.Tau → DomWeight n) (g : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (g τ).map D.what₂.embLL) P ∈ RatSpan D lam := by
  obtain ⟨F, hF, rfl⟩ := exists_of_mem_ratSpan lam hP
  rw [← Formalism.L2.Col.map_blockAct]
  apply map_mem_ratSpan
  exact (Formalism.GradedWeylDivisibility.blockActTensor D.what₂.LL D.what₂.LL D.what₂.Tau n n g).2 (fun τ => nablaSq D.what₂.LL n (lam τ))
    (fun τ => nablaSq D.what₂.LL n (lam τ)) (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable D.what₂.LL n n _ _ f hf) F hF

theorem exists_ratSpan_fnOf_atInf (lam : D.what₂.Tau → DomWeight n) (G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (s : D.what₂.Tau → ℤ) (γ : Matrix (Fin n) (Fin n) D.host.E)
    {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ RatSpan D lam) :
    ∃ Q ∈ RatSpan D lam, fnOf G s (atInf (embT D) γ) P = fnOf G s 1 Q := by
  let g : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL := fun τ =>
    γ.map fun a => D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) a)
  have hg : atInf (embT D) γ = fun τ => (g τ).map D.what₂.embLL := by
    funext τ
    ext a b
    exact bwA_embT_eq D τ (γ a b)
  refine ⟨D.what₂.embLL (∏ τ, (g τ).det ^ s τ) • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (g τ).map D.what₂.embLL) P,
    ratSpan_smul lam _ (ratSpan_blockAct lam g hP), ?_⟩
  have h := Formalism.L2.Col.fnOf_mul G s (fun τ => (g τ).map D.what₂.embLL) 1 P
  simp only [Pi.one_apply, Matrix.mul_one] at h
  rw [hg, h, map_prod]
  simp only [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]

end Span


set_option maxHeartbeats 1000000 in
theorem chi_mem_range {D : D7} {u : D.what₂.Word} (T : Forms0 D u)
    (h : ∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x) (κ : T.cls0.lev.U) :
    ((T.cls0.lev.chi κ : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  rw [T.glev0.chi_eq κ]
  refine prod_mem fun i _ => ?_
  refine finprod_induction (fun z : ℂ => z ∈ D.what₂.embLL.fieldRange) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun v => ?_
  refine finprod_induction (fun z : ℂ => z ∈ D.what₂.embLL.fieldRange) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun hv => ?_
  refine inv_mem ?_
  unfold lamJ
  rw [Finset.range_zero, Finset.prod_empty, mul_one]
  exact h i v hv _


set_option maxHeartbeats 1000000 in
theorem uop_rat (D : D7) (u : D.what₂.Word) (T : Forms0 D u)
    (h : ∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x)
    (v : (D.mem u).A.vT) (x : ((D.fm u).lat 0).V)
    (hFi : LT.Uop D u 0 v ((D.fm u).emb 0 x) ∈ (D.fm u).Fi 0) :
    ∃ y, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x) := by
  classical
  refine (T.val0.rat _).2 ⟨hFi, fun c => ?_⟩
  have hx := ((T.val0.rat _).1 ⟨x, rfl⟩).2
  have key : ∀ w : (D.fm u).lv 0 v c, (D.fm u).fv 0 v c w = 1 → ∃ P ∈ RatSpan D ((D.fm u).lam 0), ∀ z,
      (D.fm u).upT 0 v c w ((D.fm u).emb 0 x ((D.fm u).up 0 v c w)) z =
        fnOf _ (shiftOf (lamT u 0)) 1 P (T.val0.eY z) := by
    intro w hw
    obtain ⟨z, rfl⟩ := T.lv0.pr_surj v c w
    obtain ⟨γ, η, κ, -, -, -, -, -, hT⟩ := T.up_natural_level_zero v c z hw
    obtain ⟨P, hP, hPe⟩ := hx ((D.fm u).up 0 v c (T.lv0.pr v c z))
    obtain ⟨Q, hQ, hQe⟩ := exists_ratSpan_fnOf_atInf ((D.fm u).lam 0)
      (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (γ.1⁻¹).1 hP
    obtain ⟨r, hr⟩ := chi_mem_range T h κ⁻¹
    refine ⟨D.what₂.embLL r • Q, ratSpan_smul _ r hQ, fun s => ?_⟩
    let y' : Fr D 0 (Nat.zero_le _) := (T.val0.eY s).tr _ (isUnit_det_atInf (embT D) γ.1⁻¹)
    have htr : IsTr (atInf (embT D) γ.1.1) (T.val0.eY (T.val0.eY.symm y')) (T.val0.eY s) := by
      rw [Equiv.apply_symm_apply]
      intro τ
      show (T.val0.eY s).1 τ = atInf (embT D) γ.1.1 τ * (atInf (embT D) (γ.1⁻¹).1 τ * (T.val0.eY s).1 τ)
      rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]
    rw [hT _ s _ htr, hPe, Equiv.apply_symm_apply,
      Formalism.L2.Col.fnOf_tr (shiftOf (lamT u 0)) 1 (atInf (embT D) (γ.1⁻¹).1) P y' (T.val0.eY s) (fun τ => rfl),
      map_smul, Pi.smul_apply, smul_eq_mul, ← hQe, hr, map_inv]
    simp only [Pi.one_apply, Matrix.one_mul]
  choose! P hP hPe using key
  refine ⟨∑ w ∈ Finset.univ.filter (fun w : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c w = 1), P w,
    sum_mem fun w hw => hP w (Finset.mem_filter.1 hw).2, fun z => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  simp only [LT.Uop, LinearMap.pi_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearEquiv.coe_coe]
  convert Finset.sum_congr rfl fun w hw => hPe w (Finset.mem_filter.1 hw).2 z

end GlobalTheory.LevelHecke

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationalityStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardOperator_preserves_rationality : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), (∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x) → ∀ (v : (D.mem u).A.vT) (x : ((D.fm u).lat 0).V), LT.Uop D u 0 v ((D.fm u).emb 0 x) ∈ (D.fm u).Fi 0 → ∃ y, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x) := by
  first | exact @GlobalTheory.LevelHecke.uop_rat | exact GlobalTheory.LevelHecke.uop_rat | (intros; apply GlobalTheory.LevelHecke.uop_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquations
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffPowEqZeroOfDegreeLt
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscExpDeriv

theorem coeff_pow_eq_zero_of_degree_lt {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℂ)
    (hq : AddMonoidAlgebra.coeff q 0 = 0) (n : ℕ) :
    ∀ γ : σ →₀ ℕ, γ.degree < n → AddMonoidAlgebra.coeff (q ^ n) γ = 0 := by
  induction n with
  | zero => intro γ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro γ h
    rw [pow_succ, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' : x.1 + x.2 = γ := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h2 : x.2 = 0
    · rw [h2, hq, mul_zero]
    · have hd : x.2.degree ≠ 0 := fun h0 => h2 ((Finsupp.degree_eq_zero_iff _).1 h0)
      have hs : x.1.degree + x.2.degree = γ.degree := by rw [← hx', map_add (f := _)]
      rw [ih x.1 (by omega), zero_mul]

theorem coeff_expPS_eq_sum {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℂ)
    (hq : AddMonoidAlgebra.coeff q 0 = 0) (γ : σ →₀ ℕ) (N : ℕ) (hN : γ.degree < N) :
    MvPowerSeries.coeff γ (expPS q) =
      ∑ n ∈ Finset.range N, AddMonoidAlgebra.coeff (q ^ n) γ / (n.factorial : ℂ) := by
  change ∑ n ∈ Finset.range (γ.degree + 1), AddMonoidAlgebra.coeff (q ^ n) γ / (n.factorial : ℂ) = _
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => ?_
  rw [coeff_pow_eq_zero_of_degree_lt q hq n γ (by simp only [Finset.mem_range] at hn; omega),
    zero_div]

theorem coeff_deriv_expPS : ∀ (σ : Type) [DecidableEq σ] (q : MvPolynomial σ ℂ),
    AddMonoidAlgebra.coeff q 0 = 0 → ∀ (l : σ) (α : σ →₀ ℕ),
      ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) (expPS q) =
        MvPowerSeries.coeff α
          (((MvPolynomial.pderiv l q : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) * expPS q) := by
  intro σ _ q hq l α
  rw [coeff_expPS_eq_sum q hq _ (α.degree + 1 + 1)
    (by rw [map_add (f := _), Finsupp.degree_single]; omega), Finset.mul_sum, MvPowerSeries.coeff_mul]
  have h1 : ∀ n : ℕ, ((α l : ℂ) + 1) *
      (AddMonoidAlgebra.coeff (q ^ n) (α + Finsupp.single l 1) / (n.factorial : ℂ)) =
      AddMonoidAlgebra.coeff (MvPolynomial.pderiv l (q ^ n)) α / (n.factorial : ℂ) := by
    intro n
    rw [MvPolynomial.coeff_pderiv]
    ring
  simp only [h1]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Derivation.map_one_eq_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_div, add_zero]
  have h2 : ∀ n : ℕ, AddMonoidAlgebra.coeff (MvPolynomial.pderiv l (q ^ (n + 1))) α /
      (((n + 1).factorial : ℕ) : ℂ) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, AddMonoidAlgebra.coeff (MvPolynomial.pderiv l q) x.1 *
        (AddMonoidAlgebra.coeff (q ^ n) x.2 / (n.factorial : ℂ)) := by
    intro n
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, mul_comm, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_mul, Nat.factorial_succ, nsmul_eq_mul]
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div]
    push_cast
    field_simp
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = α := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have hs : x.1.degree + x.2.degree = α.degree := by rw [← hx', map_add (f := _)]
  rw [coeff_expPS_eq_sum q hq x.2 (α.degree + 1) (by omega), MvPolynomial.coeff_coe, Finset.mul_sum]

end GlobalTheory.OscExpDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquations
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

section General

variable {σ : Type} [DecidableEq σ] {F : Fock σ} {v : F.H} {E : MvPowerSeries σ ℂ}


omit [DecidableEq σ] in
theorem prod_factorial_add_single (α : σ →₀ ℕ) (l : σ) :
    (α + Finsupp.single l 1).prod (fun _ k => (k.factorial : ℂ)) =
      ((α l : ℂ) + 1) * α.prod (fun _ k => (k.factorial : ℂ)) := by
  classical
  rw [← FockSeq.mfact_cast, ← FockSeq.mfact_cast, Oscillator.mfact_add_single]
  push_cast
  ring

theorem inner_X_mul_monomial (h : HasCoeff F v E) (l : σ) (α : σ →₀ ℕ) :
    inner ℂ (F.ι (MvPolynomial.X l * MvPolynomial.monomial α 1)) v =
      α.prod (fun _ k => (k.factorial : ℂ)) *
        (((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E) := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm, h, prod_factorial_add_single]
  ring

theorem inner_pderiv_monomial (h : HasCoeff F v E) (m : σ) (α : σ →₀ ℕ) :
    inner ℂ (F.ι (MvPolynomial.pderiv m (MvPolynomial.monomial α 1))) v =
      α.prod (fun _ k => (k.factorial : ℂ)) * MvPowerSeries.coeff α (MvPowerSeries.X m * E) := by
  have e : ∀ (γ : σ →₀ ℕ) (c : ℂ), (MvPolynomial.monomial γ c : MvPolynomial σ ℂ) =
      c • MvPolynomial.monomial γ 1 := fun γ c => by simp [MvPolynomial.smul_monomial]
  rw [MvPolynomial.pderiv_monomial, e, map_smul, inner_smul_left, h, MvPowerSeries.X_def,
    MvPowerSeries.coeff_monomial_mul]
  by_cases h0 : α m = 0
  · have : ¬ Finsupp.single m 1 ≤ α := by rw [Finsupp.single_le_iff, h0]; omega
    simp [h0, this]
  · have hle : Finsupp.single m 1 ≤ α := Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero h0)
    obtain ⟨β, rfl⟩ := exists_add_of_le hle
    rw [if_pos hle, add_tsub_cancel_left, add_comm, prod_factorial_add_single]
    simp
    ring

theorem inner_X_mul_of_deriv {κ : Type} [Fintype κ] (h : HasCoeff F v E) (l : σ) (c : ℂ) (a : κ → ℂ) (m : κ → σ)
    (hE : ∀ α : σ →₀ ℕ, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E =
      MvPowerSeries.coeff α (((MvPolynomial.C c + ∑ k, MvPolynomial.C (a k) * MvPolynomial.X (m k) :
        MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) * E)) (f : MvPolynomial σ ℂ) :
    inner ℂ (F.ι (MvPolynomial.X l * f)) v =
      c * inner ℂ (F.ι f) v + ∑ k, a k * inner ℂ (F.ι (MvPolynomial.pderiv (m k) f)) v := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
    simp only [mul_add, map_add (f := _), inner_add_left, hf, hg, Finset.sum_add_distrib]
    ring
  | monomial α b =>
    have e : (MvPolynomial.monomial α b : MvPolynomial σ ℂ) = b • MvPolynomial.monomial α 1 := by
      simp [MvPolynomial.smul_monomial]
    have e2 : ((MvPolynomial.C c + ∑ k, MvPolynomial.C (a k) * MvPolynomial.X (m k) :
        MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) =
        MvPowerSeries.C c + ∑ k, MvPowerSeries.C (a k) * MvPowerSeries.X (m k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add (f := _), map_sum]
      simp
    rw [e, mul_smul_comm]
    simp only [Derivation.map_smul, map_smul, inner_smul_left]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [inner_X_mul_monomial h, inner_pderiv_monomial h, h α, hE, e2, add_mul, Finset.sum_mul, map_add (f := _),
      map_sum, mul_assoc, MvPowerSeries.coeff_C_mul, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring

end General

variable {P Q : ℕ}

theorem pderiv_inl_gaussPoly (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (i : Fin P) :
    MvPolynomial.pderiv (Sum.inl i) (gaussPoly A x) =
      MvPolynomial.C (x (Sum.inl i)) + ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inr j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gaussPoly, map_add (f := _), map_sum, mul_assoc, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]
  rw [add_comm, Finset.sum_comm]
  simp

theorem pderiv_inr_gaussPoly (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (j : Fin Q) :
    MvPolynomial.pderiv (Sum.inr j) (gaussPoly A x) =
      MvPolynomial.C (x (Sum.inr j)) + ∑ i, MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inl i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gaussPoly, map_add (f := _), map_sum, mul_assoc, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]
  rw [add_comm]
  simp

theorem gauss_annihilator (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H)
    (h : HasCoeff F v (expPS (gaussPoly A x))) :
    (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v =
      x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) ∧
    (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v =
      x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) := by
  refine ⟨fun i f => ?_, fun j f => ?_⟩
  · refine inner_X_mul_of_deriv h _ _ (fun j => A i j) (fun j => Sum.inr j) (fun α => ?_) f
    rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x), pderiv_inl_gaussPoly]
  · refine inner_X_mul_of_deriv h _ _ (fun i => A i j) (fun i => Sum.inl i) (fun α => ?_) f
    rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x), pderiv_inr_gaussPoly]

end GlobalTheory.OscGauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianVector_annihilator_equations : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), HasCoeff F v (expPS (gaussPoly A x)) → (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) ∧ (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) := by
  first | exact @GlobalTheory.OscGauss.gauss_annihilator | exact GlobalTheory.OscGauss.gauss_annihilator | (intros; apply GlobalTheory.OscGauss.gauss_annihilator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProd
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProd
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdInt

theorem map_eq_smul_prod {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c) :
    ρ.map (fun X => (pi X, fun v : S => pv v X)) = c • mi.prod (Measure.pi fun v : S => mv v) := by
  classical
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (Measurable.of_eval fun v => hpv v)
  by_cases hc0 : c = 0
  · have := h (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
    simp only [hc0, mul_zero, Finset.prod_const_one, mul_one, lintegral_const, one_mul,
      Measure.measure_univ_eq_zero] at this
    simp [this, hc0]
  have key : mi.prod (Measure.pi fun v : S => mv v) =
      c⁻¹ • ρ.map (fun X => (pi X, fun v : S => pv v X)) := by
    refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
      (D := Set.pi Set.univ '' Set.pi Set.univ fun v : S => {s : Set (Zv v) | MeasurableSet s})
      MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      MeasurableSpace.isPiSystem_measurableSet isPiSystem_pi mi.toFiniteSpanningSetsIn
      (Measure.FiniteSpanningSetsIn.pi fun v : S => (mv v).toFiniteSpanningSetsIn) ?_
    rintro s hs _ ⟨t, ht, rfl⟩
    have hs' : MeasurableSet s := hs
    have ht' : ∀ v : S, MeasurableSet (t v) := fun v => ht v (Set.mem_univ _)
    let fv : ∀ v, Zv v → ℝ≥0∞ := fun v => if hv : v ∈ S then (t ⟨v, hv⟩).indicator 1 else 0
    have hfv : ∀ v, Measurable (fv v) := by
      intro v
      by_cases hv : v ∈ S
      · simp only [fv, dif_pos hv]
        exact measurable_one.indicator (ht' _)
      · simp only [fv, dif_neg hv]
        exact measurable_zero
    have hfv' : ∀ v : S, fv v = (t v).indicator 1 := fun v => by simp only [fv, dif_pos v.2]
    have h1 := h (s.indicator 1) fv (measurable_one.indicator hs') hfv
    have hm : MeasurableSet (s ×ˢ Set.pi Set.univ t) :=
      hs'.prod (MeasurableSet.univ_pi ht')
    rw [Measure.smul_apply, Measure.map_apply hT hm, ← lintegral_indicator_one (hT hm), Measure.pi_pi]
    have h2 : ∀ X, ((fun X => (pi X, fun v : S => pv v X)) ⁻¹' (s ×ˢ Set.pi Set.univ t)).indicator
        (1 : Z → ℝ≥0∞) X = s.indicator 1 (pi X) * ∏ v ∈ S, fv v (pv v X) := by
      intro X
      rw [← Finset.prod_coe_sort S]
      simp only [hfv']
      by_cases hX : pi X ∈ s
      · by_cases hY : ∀ v : S, pv v X ∈ t v
        · rw [Set.indicator_of_mem (by simpa [hX] using hY)]
          simp [hX, hY]
        · rw [Set.indicator_of_notMem (by simpa [hX] using hY)]
          push_neg at hY
          obtain ⟨v, hv⟩ := hY
          rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])]
          simp
      · rw [Set.indicator_of_notMem (by simp [hX])]
        simp [hX]
    simp_rw [h2]
    rw [h1, ← Finset.prod_coe_sort S]
    simp only [hfv', lintegral_indicator_one hs', lintegral_indicator_one (ht' _), smul_eq_mul]
    rw [mul_comm c⁻¹, mul_assoc, ENNReal.mul_inv_cancel hc0 hc, mul_one]
  rw [key, smul_smul, ENNReal.mul_inv_cancel hc0 hc, one_smul]

theorem integral_tensor {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c)
    (Φi : Zi → ℂ) (Φv : ∀ v, Zv v → ℂ) (hi : Integrable Φi mi) (hv : ∀ v, Integrable (Φv v) (mv v)) :
    Integrable (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) ρ ∧
      ∫ X, Φi (pi X) * ∏ v ∈ S, Φv v (pv v X) ∂ρ =
        (∫ Y, Φi Y ∂mi) * ((∏ v ∈ S, ∫ Y, Φv v Y ∂(mv v)) * (c.toReal : ℂ)) := by
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (Measurable.of_eval fun v => hpv v)
  have hmap := map_eq_smul_prod ρ mi mv pi pv hpi hpv S c hc h
  let G : Zi × (∀ v : S, Zv v) → ℂ := fun Y => Φi Y.1 * ∏ v : S, Φv v (Y.2 v)
  have hG : Integrable G (mi.prod (Measure.pi fun v : S => mv v)) :=
    hi.mul_prod (Integrable.fintype_prod_dep (f := fun v : S => Φv v) fun v => hv v)
  have hG' : Integrable G (ρ.map (fun X => (pi X, fun v : S => pv v X))) := by
    rw [hmap]; exact hG.smul_measure hc
  have he : (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) =
      G ∘ (fun X => (pi X, fun v : S => pv v X)) := by
    funext X
    simp only [G, Function.comp]
    rw [← Finset.prod_coe_sort S]
  rw [he]
  refine ⟨(integrable_map_measure hG'.aestronglyMeasurable hT.aemeasurable).1 hG', ?_⟩
  have := integral_map hT.aemeasurable hG'.aestronglyMeasurable
  simp only [Function.comp_def]
  rw [← this, hmap, integral_smul_measure]
  simp only [G]
  rw [integral_prod_mul Φi (fun Y : ∀ v : S, Zv v => ∏ v : S, Φv v (Y v)),
    integral_fintype_prod_eq_prod (fun v : S => Φv v), ← Finset.prod_coe_sort S, Complex.real_smul]
  ring

theorem hasProd_of_tail {ι : Type} (f : ι → ℂ) (a : ι → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hs : Summable fun v => |a v - 1|) (S : Finset ι) (hf : ∀ v ∉ S, f v = a v) :
    HasProd f ((∏ v ∈ S, f v) *
      (((ENNReal.ofReal (∏' v : {v // v ∉ S}, a v.1)).toReal : ℝ) : ℂ)) := by
  have hm : Multipliable fun v : {v // v ∉ S} => a v.1 := by
    have h1 : Summable fun v : {v // v ∉ S} => ‖a v.1 - 1‖ := hs.subtype _
    simpa using multipliable_one_add_of_summable h1
  have h0 : 0 ≤ ∏' v : {v // v ∉ S}, a v.1 :=
    ge_of_tendsto' hm.hasProd fun s => Finset.prod_nonneg fun v _ => ha _
  rw [ENNReal.toReal_ofReal h0]
  have h2 := hm.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
  refine (S.hasProd f).mul_compl ?_
  have h3 : (f ∘ Subtype.val : {v // v ∉ S} → ℂ) = Complex.ofRealHom ∘ fun v : {v // v ∉ S} => a v.1 :=
    funext fun v => hf v.1 v.2
  have h4 : HasProd (f ∘ Subtype.val : {v // v ∉ S} → ℂ)
      ((∏' v : {v // v ∉ S}, a v.1 : ℝ) : ℂ) := by rw [h3]; exact h2
  exact h4

theorem integral_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf → Integrable Φ ν ∧ Multipliable (fun v => ∫ X, Φv v X ∂(mv v)) ∧ ∫ X, Φ X ∂ν = (∫ X, Φinf X ∂mi) * ∏' v, ∫ X, Φv v X ∂(mv v) := by
  intro F E _ _ _ _ _ d b n M ν mi mv hP d' b' Φ Φinf Φf Φv hc hcs hpure hΦ
  obtain ⟨⟨hmi, hmv, hsum⟩, hP⟩ := hP
  obtain ⟨hsb, hae, hfin⟩ := hpure
  obtain ⟨hco, -, hint, hbb⟩ := GlobalTheory.GaugeEx.IntBasis.main F E (AlgHom.id F E) d b
  obtain ⟨-, -, hci, hcv⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hae' : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 := by
    filter_upwards [hae, hbb d' b'] with v h1 h2
    rw [h1]
    congr 1
    ext Y
    rw [mem_latV_iff, mem_latV_iff, h2]
  have hfinS := Filter.eventually_cofinite.1 hae'
  set S := hfinS.toFinset with hS
  have hout : ∀ v ∉ S, Φv v = (latV b v).indicator 1 := by
    intro v hv
    by_contra hne
    exact hv (by simpa [hS] using hne)
  have hlat : ∀ v : HeightOneSpectrum (𝓞 F),
      IsClosed (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    have : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
        ⋂ a, ⋂ i, (fun Y => Y a i) ⁻¹' intV b v := by
      ext Y; simp [mem_latV_iff]
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun i =>
      (hco v).1.isClosed.preimage (by fun_prop)
  set B : Set (Fin n → Fin M → AF F ⊗[F] E) := {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v} with hB
  have hBm : MeasurableSet B := by
    have : B = ⋂ v, ⋂ (_ : v ∉ S), (fun X => projV v (projFin X)) ⁻¹' latV b v := by
      ext X; simp [hB]
    rw [this]
    exact (isClosed_iInter fun v => isClosed_iInter fun _ => (hlat v).preimage (hcv v)).measurableSet
  have hΦB : Φ = B.indicator fun X => Φinf (projInf X) * ∏ v ∈ S, Φv v (projV v (projFin X)) := by
    funext X
    rw [hΦ X, hfin]
    by_cases hX : X ∈ B
    · rw [Set.indicator_of_mem hX, finprod_eq_prod_of_mulSupport_subset (s := S)]
      intro v hv
      by_contra hvS
      have hvS' : v ∉ S := hvS
      apply hv
      simp only [hout v hvS']
      exact Set.indicator_of_mem (hX v hvS') _
    · rw [Set.indicator_of_notMem hX]
      simp only [hB, Set.mem_setOf_eq, not_forall] at hX
      obtain ⟨v, hvS, hv⟩ := hX
      have hev : ∀ᶠ v in Filter.cofinite, Φv v (projV v (projFin X)) = 1 := by
        have h1 : ∀ᶠ v in Filter.cofinite, ∀ a i, prV v (X a i) ∈ intV b v :=
          Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i => hint _
        filter_upwards [hae', h1] with w h2 h3
        rw [h2]
        exact Set.indicator_of_mem (show projV w (projFin X) ∈ latV b w from h3) _
      rw [finprod_eq_zero _ v (by rw [hout v hvS]; exact Set.indicator_of_notMem hv _)
        (Filter.eventually_cofinite.1 hev), mul_zero]
  haveI : SigmaFinite mi := inferInstance
  haveI : ∀ v, SigmaFinite (mv v) := fun v => inferInstance
  obtain ⟨h1, h2⟩ := integral_tensor (ν.restrict B) mi mv projInf (fun v X => projV v (projFin X))
    hci.measurable (fun v => (hcv v).measurable) S (tailProd b mv S) ENNReal.ofReal_ne_top (hP S)
    Φinf Φv (hc.integrable_of_hasCompactSupport hcs)
    (fun v => (hsb v).1.continuous.integrable_of_hasCompactSupport (hsb v).2)
  have h3 := hasProd_of_tail (fun v => ∫ X, Φv v X ∂(mv v)) (fun v => (mv v (latV b v)).toReal)
    (fun v => ENNReal.toReal_nonneg) hsum S (by
      intro v hv
      rw [hout v hv]
      have := integral_indicator_const (μ := mv v) (1 : ℂ) (hlat v).measurableSet
      simpa [Measure.real, Pi.one_def] using this)
  refine ⟨?_, h3.multipliable, ?_⟩
  · rw [hΦB]; exact (integrable_indicator_iff hBm).2 h1
  · rw [h3.tprod_eq, hΦB, integral_indicator hBm, h2]
    rfl

end GlobalTheory.GaugeEx.ProdInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProdStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf → Integrable Φ ν ∧ Multipliable (fun v => ∫ X, Φv v X ∂(mv v)) ∧ ∫ X, Φ X ∂ν = (∫ X, Φinf X ∂mi) * ∏' v, ∫ X, Φv v X ∂(mv v) := by
  first | exact @GlobalTheory.GaugeEx.ProdInt.integral_pure | exact GlobalTheory.GaugeEx.ProdInt.integral_pure | (intros; apply GlobalTheory.GaugeEx.ProdInt.integral_pure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOfWeakDerivOnInvariantTotalSet
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOfWeakDerivOnInvariantTotalSet
namespace GlobalTheory.Mem.Osc

theorem hasDerivAt_of_weak_on_invariant_total
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ℝ → H →L[ℂ] H) (D : Set H) (x w : H) (h0 : U 0 = 1)
    (hadd : ∀ s t, U (s + t) = U s * U t) (hn : ∀ t y, ‖U t y‖ = ‖y‖)
    (hc : ∀ y, Continuous fun t => U t y) (hD : Dense (Submodule.span ℂ D : Set H))
    (hinv : ∀ t, ∀ y ∈ D, U t y ∈ D)
    (hw : ∀ y ∈ D, HasDerivAt (fun t : ℝ => inner ℂ (U t x) y) (inner ℂ w y) 0) :
    HasDerivAt (fun t : ℝ => U t x) w 0 := by
  have hiso : ∀ t a b, inner ℂ (U t a) (U t b) = inner ℂ a b := fun t a b =>
    (⟨(U t).toLinearMap, hn t⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b
  have hadj : ∀ t a y, inner ℂ (U t a) y = inner ℂ a (U (-t) y) := by
    intro t a y
    have : U t (U (-t) y) = y := by
      have := congrArg (fun A : H →L[ℂ] H => A y) (hadd t (-t))
      simpa [h0] using this.symm
    rw [← hiso t a (U (-t) y), this]
  have hI : ∀ t : ℝ, HasDerivAt (fun u : ℝ => ∫ s in (0:ℝ)..u, U s w) (U t w) t := fun t =>
    ((hc w).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hall : ∀ y ∈ D, ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => inner ℂ (U u x) y) (inner ℂ (U t w) y) t := by
    intro y hy t
    have h1 := hw _ (hinv (-t) y hy)
    rw [← hadj] at h1
    have h2 : HasDerivAt (fun u : ℝ => inner ℂ (U u x) (U (-t) y)) (inner ℂ (U t w) y) (t - t) := by
      simpa using h1
    have h3 := h2.comp_sub_const t t
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    have h4 : U u x = U t (U (u - t) x) := by
      have := congrArg (fun A : H →L[ℂ] H => A x) (hadd t (u - t))
      simpa using this
    simp only
    rw [← hadj, ← h4]
  have hz : ∀ y ∈ D, ∀ t : ℝ, inner ℂ (U t x - x - ∫ s in (0:ℝ)..t, U s w) y = 0 := by
    intro y hy t
    have hd : ∀ u : ℝ, HasDerivAt
        (fun u : ℝ => inner ℂ (U u x) y - inner ℂ (∫ s in (0:ℝ)..u, U s w) y) (0:ℂ) u := by
      intro u
      have h5 := (hI u).inner ℂ (hasDerivAt_const u y)
      have h6 := (hall y hy u).sub h5
      simp only [inner_zero_right, zero_add, sub_self] at h6
      exact h6
    have h7 := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
      (fun u => (hd u).deriv) t 0
    simp only [h0, intervalIntegral.integral_same, inner_zero_left, sub_zero,
      one_apply_eq_self] at h7
    rw [inner_sub_left, inner_sub_left, ← h7]
    ring
  have hF : ∀ t : ℝ, U t x = x + ∫ s in (0:ℝ)..t, U s w := by
    intro t
    have h8 : U t x - x - ∫ s in (0:ℝ)..t, U s w = 0 := by
      refine hD.eq_zero_of_inner_left (𝕜 := ℂ) ?_
      intro v hv
      induction hv using Submodule.span_induction with
      | mem y hy => exact hz y hy t
      | zero => simp
      | add a b _ _ ha hb => simp only [inner_add_right] at *; rw [ha, hb, add_zero]
      | smul c a _ ha => simp only [inner_smul_right] at *; rw [ha, mul_zero]
    rw [sub_sub, sub_eq_zero] at h8
    exact h8
  have h9 := (hI 0).const_add x
  simp only [h0, one_apply_eq_self] at h9
  exact h9.congr_of_eventuallyEq (Filter.Eventually.of_forall hF)

end GlobalTheory.Mem.Osc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOfWeakDerivOnInvariantTotalSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_of_weak_deriv_on_invariant_total_set : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (D : Set H) (x w : H), U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ t y, ‖U t y‖ = ‖y‖) → (∀ y, Continuous fun t => U t y) → Dense (Submodule.span ℂ D : Set H) → (∀ t, ∀ y ∈ D, U t y ∈ D) → (∀ y ∈ D, HasDerivAt (fun t : ℝ => inner ℂ (U t x) y) (inner ℂ w y) 0) → HasDerivAt (fun t : ℝ => U t x) w 0 := by
  first | exact @GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total | exact GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total | (intros; apply GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total <;> assumption)
end
end
