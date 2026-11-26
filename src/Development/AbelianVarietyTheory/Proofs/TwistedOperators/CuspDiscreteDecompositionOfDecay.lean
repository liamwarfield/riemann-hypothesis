module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHilbertSchmidtOfAePointwiseBoundedLpTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffRightConvolutionAlongOneParameterProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionPreservesCuspidal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionPreservesCuspidal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspConv

theorem isCuspFun_convR_lift : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ,
    F ∈ GlobalTheory.Cusp.L2cusp V μ → IsCuspFun V (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) := by
  intro D V μ _ _ f hf F hF
  obtain ⟨hc, hs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have h := (GlobalTheory.CuspAE.mem_L2cusp_iff_isCuspAE D V μ F).1 hF
  have hl := (GlobalTheory.AutomorphicL2Unitary.leftInv_lift (Γ := GQ V) F).convR (μ := μ) f
  refine GlobalTheory.Cusp.isCuspFun_of_forall_flag hl fun 𝔉 h𝔉 => funext fun x => ?_
  refine (GlobalTheory.CuspAE.constTermOn_convR (GlobalTheory.Cusp.cocompact_flag D V 𝔉) (GlobalTheory.AutomorphicL2Unitary.leftInv_lift _)
    ((Lp.stronglyMeasurable F).comp_measurable GlobalTheory.AutomorphicL2Unitary.measurable_mk) (GlobalTheory.CuspAE.locallyIntegrable_lift F)
    hc hs x).trans ?_
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [(measurePreserving_mul_left μ x).quasiMeasurePreserving.ae (h 𝔉 h𝔉)] with y hy
  exact mul_eq_zero_of_right _ hy

end GlobalTheory.CuspConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionPreservesCuspidalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_preserves_cuspidal : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, F ∈ GlobalTheory.Cusp.L2cusp V μ → IsCuspFun V (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) := by
  first | exact @GlobalTheory.CuspConv.isCuspFun_convR_lift | exact GlobalTheory.CuspConv.isCuspFun_convR_lift | (intros; apply GlobalTheory.CuspConv.isCuspFun_convR_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionRightInvariantOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionRightInvariantOpen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConvLevel

theorem ccGA_leftInv {D : D7} {V : HSp D} {f : GA D V → ℂ} (hf : f ∈ GlobalTheory.Orb.CcGA V) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ y, f (k * y) = f y := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, -, b, hb, rfl⟩ := hf
    obtain ⟨K, hK, hb'⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨K.comap (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram),
      hK.preimage (GlobalTheory.AdelicU.continuous_projFin _ _), fun k hk hk' y => ?_⟩
    have h1 : GlobalTheory.AdelicU.projInf D.sp.cm.sig V.gram k = 1 := GlobalTheory.AdelicU.mem_finPts.1 hk'
    simp only [GlobalTheory.Orb.infFin, map_mul, h1, one_mul]
    rw [(hb' _ hk _).1]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add f f' _ _ h h' =>
    obtain ⟨U, hU, e⟩ := h
    obtain ⟨U', hU', e'⟩ := h'
    exact ⟨U ⊓ U', hU.inter hU', fun k hk hk' y => by
      simp only [Pi.add_apply, e k hk.1 hk' y, e' k hk.2 hk' y]⟩
  | smul c f _ h =>
    obtain ⟨U, hU, e⟩ := h
    exact ⟨U, hU, fun k hk hk' y => by simp only [Pi.smul_apply, e k hk hk' y]⟩

theorem convR_level : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, ∀ k ∈ U, k ∈ GfC V → ∀ g, GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * k) = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g := by
  intro D V μ _ _ f hf
  obtain ⟨U, hU, e⟩ := ccGA_leftInv hf
  refine ⟨U, hU, fun F k hk hk' g => ?_⟩
  rw [GlobalTheory.AutomorphicL2Unitary.convR_eq, GlobalTheory.AutomorphicL2Unitary.convR_eq]
  congr 1
  funext y
  rw [mul_inv_rev, mul_assoc, e _ (U.inv_mem hk) ((GfC V).inv_mem hk')]

end GlobalTheory.ConvLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionRightInvariantOpenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_right_invariant_open : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, ∀ k ∈ U, k ∈ GfC V → ∀ g, GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * k) = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g := by
  first | exact @GlobalTheory.ConvLevel.convR_level | exact GlobalTheory.ConvLevel.convR_level | (intros; apply GlobalTheory.ConvLevel.convR_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NcardRationalPointsInTranslateLeHeightPow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMulHeightMinpolyCoeffLeRelativeHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NnnormMinpolyCoeffFinitePlaceLePow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NnnormMinpolyCoeffFinitePlaceLePow
open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

namespace GlobalTheory.CoefHeight

open Polynomial

theorem val_coeff_prod_X_sub_C_le {K : Type} [Field K] (w : Valuation K ℝ≥0) {M : ℝ≥0} (hM : 1 ≤ M)
    (s : Multiset K) (hs : ∀ z ∈ s, w z ≤ M) (j : ℕ) :
    w ((s.map fun a => X - C a).prod.coeff j) ≤ M ^ Multiset.card s := by
  induction s using Multiset.induction_on generalizing j with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, coeff_one]
    split_ifs <;> simp
  | cons a s ih =>
    have ha : w a ≤ M := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ z ∈ s, w z ≤ M := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine (w.map_sub _ _).trans (max_le ?_ ?_)
    · cases j with
      | zero => rw [coeff_X_mul_zero, map_zero]; exact bot_le
      | succ i => rw [coeff_X_mul]; exact (ih hs' i).trans (pow_le_pow_right₀ hM (Nat.le_succ _))
    · rw [map_mul, pow_succ']
      exact mul_le_mul' ha (ih hs' j)

theorem nnnorm_coeff_minpoly_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E) (v : HeightOneSpectrum (𝓞 F)) (j : ℕ) :
    ‖algebraMap F (v.adicCompletion F) ((minpoly F x).coeff j)‖₊ ≤
      max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) ^ Module.finrank F E := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  set p := minpoly F x with hp
  set q := p.map (algebraMap F (FvBar F v)) with hqdef
  have hmon : q.Monic := (minpoly.monic hint).map _
  have hsplit : q.Splits := IsAlgClosed.splits q
  have hq : q = (q.roots.map fun a => X - C a).prod := hsplit.eq_prod_roots_of_monic hmon
  have hroots : ∀ z ∈ q.roots, valBar F v z ≤ M := by
    intro z hz
    have hq0 : q ≠ 0 := hmon.ne_zero
    have hz' : aeval z p = 0 := by
      rw [mem_roots hq0, IsRoot, hqdef, eval_map_algebraMap] at hz; exact hz
    obtain ⟨τ, hτ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hz'
    have h1 : finEmb F v τ ((1 : v.adicCompletion F) ⊗ₜ[F] x) = z := by rw [finEmb_tmul, map_one, one_mul, hτ]
    show absBar F v z ≤ M
    rw [← h1]; exact (le_absFin F v τ _).trans (le_max_right _ _)
  have hcard : Multiset.card q.roots ≤ Module.finrank F E := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hqdef, natDegree_map]; exact minpoly.natDegree_le x
  have key := val_coeff_prod_X_sub_C_le (valBar F v) hM q.roots hroots j
  rw [← hq] at key
  have hc : valBar F v (q.coeff j) = ‖algebraMap F (v.adicCompletion F) (p.coeff j)‖₊ := by
    show absBar F v _ = _
    rw [hqdef, coeff_map, IsScalarTower.algebraMap_apply F (v.adicCompletion F) (FvBar F v), absBar_algebraMap]
  rw [← hc]
  exact key.trans (pow_le_pow_right₀ hM hcard)

end GlobalTheory.CoefHeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NnnormMinpolyCoeffFinitePlaceLePowStatement
open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nnnorm_minpoly_coeff_finitePlace_le_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : E) (v : HeightOneSpectrum (𝓞 F)) (j : ℕ), ‖algebraMap F (v.adicCompletion F) ((minpoly F x).coeff j)‖₊ ≤ max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) ^ Module.finrank F E := by
  first | exact @GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le | exact GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le | (intros; apply GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePlaceMinpolyCoeffLePowMaxEmbeddings
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePlaceMinpolyCoeffLePowMaxEmbeddings
open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

namespace GlobalTheory

theorem minpoly_coeff_le_inf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E) (w : InfinitePlace F) (j : ℕ) :
    w ((minpoly F x).coeff j) ≤ 2 ^ Module.finrank F E *
      ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ) ^ Module.finrank F E := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  set M : ℝ≥0 := max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) with hM
  set p := minpoly F x
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h1 : p.Monic := minpoly.monic hx
  have hd : p.natDegree ≤ Module.finrank F E := minpoly.natDegree_le x
  have h3 : ∀ z ∈ (p.map w.embedding).roots, ‖z‖ ≤ (M : ℝ) := by
    intro z hz
    have hz' : z ∈ p.rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨h1.ne_zero, ?_⟩
      have := (Polynomial.mem_roots (Polynomial.map_monic_ne_zero h1)).1 hz
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact this
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hz'
    obtain ⟨ψ, rfl⟩ := hz'
    let τ : EmbOver E w := ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a⟩
    have : ‖ψ x‖₊ ≤ M :=
      le_trans (Finset.le_sup (f := fun τ : EmbOver E w => ‖τ.1 x‖₊) (Finset.mem_univ τ)) (le_max_right _ _)
    exact_mod_cast this
  have key := Polynomial.coeff_le_of_roots_le (f := w.embedding) j h1 (IsAlgClosed.splits _) h3
  rw [Polynomial.coeff_map] at key
  have hw : w (p.coeff j) = ‖w.embedding (p.coeff j)‖ := (InfinitePlace.norm_embedding_eq w _).symm
  rw [hw]
  refine key.trans ?_
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_max_left _ _
  have hpow : (M : ℝ) ^ (p.natDegree - j) ≤ (M : ℝ) ^ Module.finrank F E :=
    pow_le_pow_right₀ hM1 (le_trans (Nat.sub_le _ _) hd)
  have hch : ((p.natDegree.choose j : ℕ) : ℝ) ≤ 2 ^ Module.finrank F E := by
    have := (Nat.choose_le_two_pow p.natDegree j).trans (Nat.pow_le_pow_right (by norm_num) hd)
    exact_mod_cast this
  rw [mul_comm]
  exact mul_le_mul hch hpow (by positivity) (by positivity)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePlaceMinpolyCoeffLePowMaxEmbeddingsStatement
open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitePlace_minpoly_coeff_le_pow_max_embeddings : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : E) (w : InfinitePlace F) (j : ℕ), w ((minpoly F x).coeff j) ≤ 2 ^ Module.finrank F E * ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ) ^ Module.finrank F E := by
  first | exact @GlobalTheory.minpoly_coeff_le_inf | exact GlobalTheory.minpoly_coeff_le_inf | (intros; apply GlobalTheory.minpoly_coeff_le_inf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMulHeightMinpolyCoeffLeRelativeHeight
open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal

namespace GlobalTheory.RatCount.CoefHt

theorem mult_le_two (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) : w.mult ≤ 2 := by
  unfold InfinitePlace.mult; split_ifs <;> norm_num


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
open Classical in
theorem exists_mulHeight_coeff_minpoly_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ),
    ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a := by
  intro F E _ _ _ _ _
  refine ⟨4 ^ (Module.finrank F E * Fintype.card (InfinitePlace F)), 2 * Module.finrank F E, fun x j => ?_⟩
  set m := Module.finrank F E with hm
  set c := (minpoly F x).coeff j with hc
  let A : InfinitePlace F → ℝ := fun w =>
    ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ)
  let B0 : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x))
  let B : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (B0 v : ℝ)
  have hA : ∀ w, 1 ≤ A w := fun w => by simp only [A]; exact_mod_cast le_max_left _ _
  have hB : ∀ v, 1 ≤ B v := fun v => by simp only [B, B0]; exact_mod_cast le_max_left _ _
  have hB0fin : Function.HasFiniteMulSupport B0 := by
    have h := eventually_absFin_le_one (E := E) F ((1 : AF F) ⊗ₜ[F] x)
    refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
    have e : compFin F E v ((1 : AF F) ⊗ₜ[F] x) = (1 : v.adicCompletion F) ⊗ₜ[F] x := by
      simp [compFin, map_one]
    rw [e] at hv'
    exact max_eq_left hv'
  have hBfin : Function.HasFiniteMulSupport B := by
    refine hB0fin.subset fun v hv hv' => hv ?_
    simp only [B, hv', NNReal.coe_one]
  have hht : (htE F x : ℝ) = (∏ w, A w) * ∏ᶠ v, B v := by
    rw [htE, NNReal.coe_mul, NNReal.coe_prod]
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      simp only [A]
      congr 2
      exact Finset.sup_congr (by ext; simp) fun _ _ => rfl
    · exact (MonoidHom.map_finprod NNReal.toRealHom.toMonoidHom hB0fin)
  have hB1 : ∀ v, 1 ≤ B v ^ m := fun v => one_le_pow₀ (hB v)

  have hinf : (∏ w : InfinitePlace F, max (w c) 1 ^ w.mult) ≤
      4 ^ (m * Fintype.card (InfinitePlace F)) * (∏ w, A w) ^ (2 * m) := by
    have h1 : ∀ w : InfinitePlace F, max (w c) 1 ^ w.mult ≤ 4 ^ m * A w ^ (2 * m) := fun w => by
      have hb : 1 ≤ 2 ^ m * A w ^ m := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (hA w))
      have h2 : max (w c) 1 ≤ 2 ^ m * A w ^ m := max_le (GlobalTheory.T.infinitePlace_minpoly_coeff_le_pow_max_embeddings F E x w j) hb
      calc max (w c) 1 ^ w.mult ≤ (2 ^ m * A w ^ m) ^ w.mult :=
            pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _)) h2 _
        _ ≤ (2 ^ m * A w ^ m) ^ 2 := pow_le_pow_right₀ hb (mult_le_two F w)
        _ = 4 ^ m * A w ^ (2 * m) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m 2, pow_mul, mul_comm 2 m, pow_mul]; norm_num
    calc (∏ w : InfinitePlace F, max (w c) 1 ^ w.mult) ≤ ∏ w : InfinitePlace F, (4 ^ m * A w ^ (2 * m)) :=
          Finset.prod_le_prod₀ (fun w _ => pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _) fun w _ => h1 w
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, Finset.prod_pow]

  have hfin : (∏ᶠ v : FinitePlace F, max (v c) 1) ≤ (∏ᶠ v, B v) ^ (2 * m) := by
    have e : (∏ᶠ v : FinitePlace F, max (v c) 1) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 F), max (FinitePlace.mk v c) 1 := by
      rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
      rfl
    have hle : ∀ v : HeightOneSpectrum (𝓞 F), max (FinitePlace.mk v c) 1 ≤ B v ^ m := fun v => by
      refine max_le ?_ (hB1 v)
      rw [FinitePlace.mk_apply]
      have := GlobalTheory.T.nnnorm_minpoly_coeff_finitePlace_le_pow F E x v j
      simp only [B, B0]
      exact_mod_cast this
    have hBm : Function.HasFiniteMulSupport fun v => B v ^ m := by
      refine hBfin.subset fun v hv hv' => hv ?_
      simp only [hv', one_pow]
    have hf : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => max (FinitePlace.mk v c) 1 := by
      refine hBfin.subset fun v hv hv' => hv ?_
      exact le_antisymm ((hle v).trans (by rw [hv', one_pow])) (le_max_right _ _)
    rw [e]
    calc (∏ᶠ v : HeightOneSpectrum (𝓞 F), max (FinitePlace.mk v c) 1) ≤ ∏ᶠ v, B v ^ m :=
          finprod_le_finprod₀ hf (fun v => le_trans zero_le_one (le_max_right _ _)) hBm hle
      _ = (∏ᶠ v, B v) ^ m := (finprod_pow hBfin m).symm
      _ ≤ (∏ᶠ v, B v) ^ (2 * m) := pow_le_pow_right₀ (one_le_finprod fun v => hB v) (by omega)
  rw [NumberField.mulHeight₁_eq, hht, mul_pow, ← mul_assoc]
  exact mul_le_mul hinf hfin (finprod_nonneg fun v => le_trans zero_le_one (le_max_right _ _))
    (mul_nonneg (by positivity) (pow_nonneg (Finset.prod_nonneg fun w _ => le_trans zero_le_one (hA w)) _))

end GlobalTheory.RatCount.CoefHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMulHeightMinpolyCoeffLeRelativeHeightStatement
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mulHeight_minpoly_coeff_le_relativeHeight : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a := by
  first | exact @GlobalTheory.RatCount.CoefHt.exists_mulHeight_coeff_minpoly_le | exact GlobalTheory.RatCount.CoefHt.exists_mulHeight_coeff_minpoly_le | (intros; apply GlobalTheory.RatCount.CoefHt.exists_mulHeight_coeff_minpoly_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeHeightEntryLeAdelicHeightGL
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeHeightEntryLeAdelicHeightGL
open NumberField

noncomputable section
namespace GlobalTheory.RatCount
open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Formalism.UG
open scoped TensorProduct NNReal

theorem nnnorm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖₊ ≤ opNorm A := by
  unfold opNorm
  have h1 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ d, A i d * (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n) d = A i j
    simp [PiLp.single_apply]
  have h2 := ContinuousLinearMap.le_opNNNorm (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) (EuclideanSpace.single j 1)
  rw [PiLp.nnNorm_single, nnNorm_one, mul_one] at h2
  rw [← h1]
  exact (PiLp.nnNorm_apply_le _ i).trans h2

theorem htE_entry_le_heightGL (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N) :
    GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤
      GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ) := by
  classical
  set x : E := (γ : Matrix (Fin N) (Fin N) E) i j with hx
  set g := Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ with hg
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      max 1 (absFin F v ((1 : Fv F v) ⊗ₜ[F] x)) ≤ htFin F v (bc (compFin F E v) g) := by
    intro v
    refine max_le (one_le_htOf _ _) (le_trans ?_ (le_htOf _ _))
    have he : ((bc (compFin F E v) g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) i j = (1 : Fv F v) ⊗ₜ[F] x := by
      change compFin F E v ((1 : AF F) ⊗ₜ[F] x) = _
      simp [compFin, Algebra.TensorProduct.map_tmul]
    rw [← he]
    exact absFin_le_normFin F v _ i j
  have hinf : ∀ w : InfinitePlace F,
      max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) ≤ htInf F w (bc (compInf F E w) g) := by
    intro w
    refine max_le (one_le_htOf _ _) (le_trans ?_ (le_htOf _ _))
    refine Finset.sup_le fun τ _ => ?_
    have he : (((bc (compInf F E w) g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _).map (infEmb τ)) i j = τ.1 x := by
      change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] x)) = _
      simp [compInf, Algebra.TensorProduct.map_tmul, infEmb_tmul]
    rw [← he]
    exact (nnnorm_entry_le_opNorm _ i j).trans ((normInf_le_iff F w).1 le_rfl τ)
  unfold htE heightGL
  refine mul_le_mul' (Finset.prod_le_prod fun w _ => by convert hinf w) ?_
  have hg' := finite_mulSupport_htFin F g
  refine finprod_le_finprod' (hg'.subset fun v hv hv' => hv ?_) hg' hfin
  exact le_antisymm ((hfin v).trans (le_of_eq hv')) (le_max_left _ _)

end GlobalTheory.RatCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeHeightEntryLeAdelicHeightGLStatement
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeHeight_entry_le_adelicHeightGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ) := by
  first | exact @GlobalTheory.RatCount.htE_entry_le_heightGL | exact GlobalTheory.RatCount.htE_entry_le_heightGL | (intros; apply GlobalTheory.RatCount.htE_entry_le_heightGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndNcardMinpolyCoeffHeightLe
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndNcardMinpolyCoeffHeightLe
open NumberField Polynomial

namespace GlobalTheory.MinpolyHeightCount

theorem finite_and_ncard_le_of_fibres {α β : Type*} {S : Set α} {T : Set β} {f : α → β}
    (hT : T.Finite) (hf : Set.MapsTo f S T) (m : ℕ)
    (hfib : ∀ t ∈ T, (S ∩ f ⁻¹' {t}).Finite ∧ (S ∩ f ⁻¹' {t}).ncard ≤ m) :
    S.Finite ∧ S.ncard ≤ m * T.ncard := by
  classical
  have hS : S.Finite := by
    refine (hT.biUnion fun t ht => (hfib t ht).1).subset fun x hx => ?_
    exact Set.mem_biUnion (hf hx) ⟨hx, rfl⟩
  refine ⟨hS, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hS, Set.ncard_eq_toFinset_card _ hT]
  refine Finset.card_le_mul_card_image_of_maps_to (f := f)
    (fun a ha => by simpa using hf (by simpa using ha)) m fun t ht => ?_
  have h := (hfib t (by simpa using ht)).2
  have e : (({a ∈ hS.toFinset | f a = t} : Finset α) : Set α) = S ∩ f ⁻¹' {t} := by
    ext a; simp
  rw [← Set.ncard_coe_finset, e]
  exact h

theorem finite_and_ncard_le_of_eval_eq_zero {L : Type*} [Field L] {S : Set L} {p : L[X]}
    (hp : p ≠ 0) (hS : ∀ x ∈ S, p.eval x = 0) : S.Finite ∧ S.ncard ≤ p.natDegree := by
  classical
  have hsub : S ⊆ (p.roots.toFinset : Set L) := fun x hx => by
    simp [Multiset.mem_toFinset, mem_roots hp, IsRoot.def, hS x hx]
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  calc S.ncard ≤ (p.roots.toFinset : Set L).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p

theorem finite_and_ncard_le_of_fibres_roots {L β : Type*} [Field L] {S : Set L} {T : Set β}
    {f : L → β} (hT : T.Finite) (hf : Set.MapsTo f S T) (m : ℕ)
    (hfib : ∀ t ∈ T, ∃ p : L[X], p ≠ 0 ∧ p.natDegree ≤ m ∧ ∀ x ∈ S, f x = t → p.eval x = 0) :
    S.Finite ∧ S.ncard ≤ m * T.ncard := by
  refine finite_and_ncard_le_of_fibres hT hf m fun t ht => ?_
  obtain ⟨p, hp, hdeg, hroot⟩ := hfib t ht
  obtain ⟨h1, h2⟩ := finite_and_ncard_le_of_eval_eq_zero (S := S ∩ f ⁻¹' {t}) hp
    fun x hx => hroot x hx.1 hx.2
  exact ⟨h1, h2.trans hdeg⟩

section Integral

variable (K : Type) [Field K] [NumberField K]

theorem natDegree_minpoly_int_le {x : K} (hx : IsIntegral ℤ x) :
    (minpoly ℤ x).natDegree ≤ Module.finrank ℚ K := by
  rw [← (minpoly.monic hx).natDegree_map (algebraMap ℤ ℚ),
    ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx]
  exact minpoly.natDegree_le x

theorem abs_coeff_minpoly_int_le {x : K} (hx : IsIntegral ℤ x) {R : ℝ}
    (h : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R) (i : ℕ) :
    (|(minpoly ℤ x).coeff i| : ℝ) ≤ max R 1 ^ Module.finrank ℚ K *
      (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2) := by
  refine Eq.trans_le ?_ (Embeddings.coeff_bdd_of_norm_le h i)
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, coeff_map, eq_intCast,
    Int.norm_cast_rat, Int.norm_eq_abs]

theorem finite_and_ncard_integral_le (R : ℝ) :
    {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.Finite ∧
    (({x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.ncard : ℕ) : ℝ) ≤
      Module.finrank ℚ K * (2 * (max R 1 ^ Module.finrank ℚ K *
        (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2)) + 3) ^
          (Module.finrank ℚ K + 1) := by
  classical
  set d := Module.finrank ℚ K with hd
  set M : ℝ := max R 1 ^ d * (d.choose (d / 2) : ℝ) with hM
  set C : ℕ := ⌈M⌉₊ with hC
  set T : Set (Fin (d + 1) → ℤ) :=
    ((Fintype.piFinset fun _ : Fin (d + 1) => Finset.Icc (-(C : ℤ)) C : Finset (Fin (d + 1) → ℤ)) :
      Set (Fin (d + 1) → ℤ)) with hTdef
  set f : K → Fin (d + 1) → ℤ := fun x i => (minpoly ℤ x).coeff i with hfdef
  have hT : T.ncard = (2 * C + 1) ^ (d + 1) := by
    rw [hTdef, Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Int.card_Icc,
      Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  have hmaps : Set.MapsTo f {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R} T := by
    intro x hx
    rw [hTdef, Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 := abs_coeff_minpoly_int_le K hx.1 hx.2 i
    have h2 : (|(minpoly ℤ x).coeff i| : ℝ) ≤ (C : ℝ) := h1.trans (Nat.le_ceil _)
    have h3 : |(minpoly ℤ x).coeff i| ≤ (C : ℤ) := by exact_mod_cast h2
    exact abs_le.mp h3
  obtain ⟨hfin, hcard⟩ := finite_and_ncard_le_of_fibres_roots (Finset.finite_toSet _) hmaps d
    (by
      intro t _
      by_cases h : ∃ x0 ∈ {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}, f x0 = t
      · obtain ⟨x0, hx0, hfx0⟩ := h
        refine ⟨(minpoly ℤ x0).map (algebraMap ℤ K), ((minpoly.monic hx0.1).map _).ne_zero, ?_, ?_⟩
        · rw [(minpoly.monic hx0.1).natDegree_map]
          exact natDegree_minpoly_int_le K hx0.1
        · intro y hy hfy
          have heq : minpoly ℤ y = minpoly ℤ x0 := by
            ext i
            by_cases hi : i < d + 1
            · exact congrFun (hfy.trans hfx0.symm) ⟨i, hi⟩
            · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_minpoly_int_le K hy.1).trans_lt
                (by omega)), coeff_eq_zero_of_natDegree_lt
                ((natDegree_minpoly_int_le K hx0.1).trans_lt (by omega))]
          rw [eval_map_algebraMap, ← heq]
          exact minpoly.aeval ℤ y
      · refine ⟨1, one_ne_zero, by simp, fun x hx hfx => (h ⟨x, hx, hfx⟩).elim⟩)
  refine ⟨hfin, ?_⟩
  have hM0 : 0 ≤ M := by positivity
  have hC' : (C : ℝ) ≤ M + 1 := (Nat.ceil_lt_add_one hM0).le
  rw [hT] at hcard
  calc (({x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.ncard : ℕ) : ℝ)
      ≤ ((d * (2 * C + 1) ^ (d + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (d : ℝ) * (2 * (C : ℝ) + 1) ^ (d + 1) := by push_cast; ring
    _ ≤ (d : ℝ) * (2 * M + 3) ^ (d + 1) := by
      have h23 : 2 * (C : ℝ) + 1 ≤ 2 * M + 3 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h23 _) (by positivity)

end Integral

section Height

variable {K : Type} [Field K] [NumberField K]

theorem norm_embedding_le_mulHeight₁ (φ : K →+* ℂ) (c : K) : ‖φ c‖ ≤ Height.mulHeight₁ c := by
  classical
  set w := InfinitePlace.mk φ
  have hw : w c = ‖φ c‖ := InfinitePlace.apply φ c
  rw [← hw, NumberField.mulHeight₁_eq]
  have h1 : ∀ v : InfinitePlace K, 1 ≤ max (v c) 1 ^ v.mult :=
    fun v => one_le_pow₀ (le_max_right _ _)
  calc w c ≤ max (w c) 1 := le_max_left _ _
    _ ≤ max (w c) 1 ^ w.mult := le_self_pow₀ (le_max_right _ _) w.mult_ne_zero
    _ ≤ ∏ v : InfinitePlace K, max (v c) 1 ^ v.mult := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      exact le_mul_of_one_le_right (by positivity) (Finset.one_le_prod₀ fun v _ => h1 v)
    _ ≤ _ := le_mul_of_one_le_right (Finset.prod_nonneg fun v _ => by positivity)
        (one_le_finprod fun _ => le_max_right _ _)


variable (K) in
theorem exists_ncard_mulHeight₁_le : ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B →
    {c : K | Height.mulHeight₁ c ≤ B}.Finite ∧
      (({c : K | Height.mulHeight₁ c ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by
  classical
  set d := Module.finrank ℚ K with hd
  refine ⟨d * (2 * (d.choose (d / 2) : ℝ) + 3) ^ (d + 1), 1 + 2 * d * (d + 1), fun B hB => ?_⟩
  refine ⟨finite_setOfPred_mulHeight₁_le K B, ?_⟩
  choose n hn0 hnle hint using fun c : K => exists_nat_le_mulHeight₁ c
  set A := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B ^ 2} with hAdef
  obtain ⟨hAfin, hAcard⟩ := finite_and_ncard_integral_le K (B ^ 2)
  set P : Set (ℕ × K) := (↑(Finset.Icc 1 ⌊B⌋₊) : Set ℕ) ×ˢ A with hPdef
  have hP : P.Finite := (Finset.finite_toSet _).prod hAfin
  have hle : {c : K | Height.mulHeight₁ c ≤ B}.ncard ≤ P.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun c => (n c, (n c : K) * c)) ?_ ?_ hP
    · intro c hc
      have hc' : Height.mulHeight₁ c ≤ B := hc
      refine Set.mk_mem_prod ?_ ⟨hint c, fun φ => ?_⟩
      · rw [Finset.mem_coe, Finset.mem_Icc]
        exact ⟨Nat.one_le_iff_ne_zero.mpr (hn0 c), Nat.le_floor ((hnle c).trans hc')⟩
      · rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast, sq]
        exact mul_le_mul ((hnle c).trans hc') ((norm_embedding_le_mulHeight₁ φ c).trans hc')
          (norm_nonneg _) (by linarith)
    · intro c _ c' _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1] at h2
      exact mul_left_cancel₀ (by exact_mod_cast hn0 c') h2
  have hPcard : P.ncard = ⌊B⌋₊ * A.ncard := by
    rw [hPdef, Set.ncard_prod, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel]
  have hfl : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hmax : max (B ^ 2) 1 = B ^ 2 := max_eq_left (by nlinarith)
  rw [hmax] at hAcard
  have hX : 1 ≤ B ^ (2 * d) := one_le_pow₀ hB
  have hch : (0 : ℝ) ≤ (d.choose (d / 2) : ℝ) := Nat.cast_nonneg _
  have hstep : 2 * ((B ^ 2) ^ d * (d.choose (d / 2) : ℝ)) + 3 ≤
      (2 * (d.choose (d / 2) : ℝ) + 3) * B ^ (2 * d) := by
    rw [← pow_mul]; nlinarith
  calc (({c : K | Height.mulHeight₁ c ≤ B}.ncard : ℕ) : ℝ) ≤ (P.ncard : ℝ) := by
        exact_mod_cast hle
    _ = (⌊B⌋₊ : ℝ) * (A.ncard : ℝ) := by rw [hPcard]; push_cast; ring
    _ ≤ B * (d * (2 * ((B ^ 2) ^ d * (d.choose (d / 2) : ℝ)) + 3) ^ (d + 1)) :=
        mul_le_mul hfl hAcard (Nat.cast_nonneg _) (by linarith)
    _ ≤ B * (d * ((2 * (d.choose (d / 2) : ℝ) + 3) * B ^ (2 * d)) ^ (d + 1)) := by
        gcongr
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add B 1, pow_one]; ring

end Height

theorem finite_and_ncard_minpoly_height_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B →
      {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧
      (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤
        C * B ^ k := by
  intro F E _ _ _ _ _
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨C₁, k₁, h₁⟩ := exists_ncard_mulHeight₁_le (K := F)
  set m := Module.finrank F E with hm
  refine ⟨m * C₁ ^ (m + 1), k₁ * (m + 1), fun B hB => ?_⟩
  obtain ⟨hSfin, hScard⟩ := h₁ B hB
  set S := {c : F | Height.mulHeight₁ c ≤ B} with hSdef
  set X := {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B} with hXdef
  set T : Set (Fin (m + 1) → F) :=
    ((Fintype.piFinset fun _ : Fin (m + 1) => hSfin.toFinset : Finset (Fin (m + 1) → F)) :
      Set (Fin (m + 1) → F)) with hTdef
  set f : E → Fin (m + 1) → F := fun x j => (minpoly F x).coeff j with hfdef
  have hT : T.ncard = S.ncard ^ (m + 1) := by
    rw [hTdef, Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Set.ncard_eq_toFinset_card _ hSfin]
  have hmaps : Set.MapsTo f X T := by
    intro x hx
    rw [hTdef, Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    rw [Set.Finite.mem_toFinset]
    exact hx j
  obtain ⟨hXfin, hXcard⟩ := finite_and_ncard_le_of_fibres_roots (Finset.finite_toSet _) hmaps m
    (by
      intro t _
      by_cases h : ∃ x0 ∈ X, f x0 = t
      · obtain ⟨x0, -, hfx0⟩ := h
        have hi0 : IsIntegral F x0 := Algebra.IsIntegral.isIntegral x0
        refine ⟨(minpoly F x0).map (algebraMap F E), ((minpoly.monic hi0).map _).ne_zero, ?_, ?_⟩
        · rw [(minpoly.monic hi0).natDegree_map]; exact minpoly.natDegree_le x0
        · intro y _ hfy
          have heq : minpoly F y = minpoly F x0 := by
            ext i
            by_cases hi : i < m + 1
            · exact congrFun (hfy.trans hfx0.symm) ⟨i, hi⟩
            · rw [coeff_eq_zero_of_natDegree_lt ((minpoly.natDegree_le y).trans_lt (by omega)),
                coeff_eq_zero_of_natDegree_lt ((minpoly.natDegree_le x0).trans_lt (by omega))]
          rw [eval_map_algebraMap, ← heq]
          exact minpoly.aeval F y
      · exact ⟨1, one_ne_zero, by simp, fun x hx hfx => (h ⟨x, hx, hfx⟩).elim⟩)
  refine ⟨hXfin, ?_⟩
  rw [hT] at hXcard
  have h0 : (0 : ℝ) ≤ (S.ncard : ℝ) := Nat.cast_nonneg _
  calc ((X.ncard : ℕ) : ℝ) ≤ ((m * S.ncard ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hXcard
    _ = (m : ℝ) * (S.ncard : ℝ) ^ (m + 1) := by push_cast; ring
    _ ≤ (m : ℝ) * (C₁ * B ^ k₁) ^ (m + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hScard _) (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.MinpolyHeightCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndNcardMinpolyCoeffHeightLeStatement
section

open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by
  first | exact @GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le | exact GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le | (intros; apply GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NcardRationalPointsInTranslateLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Formalism.UG
open scoped NNReal

namespace GlobalTheory.RatCount

theorem gl_count (hA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k) (hB : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a) (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ))
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) :
    ∃ (C : ℝ) (A : ℕ), ∀ T : ℝ, 1 ≤ T →
      {γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T}.Finite ∧
      (({γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T}.ncard : ℕ) : ℝ) ≤ C * T ^ A := by
  obtain ⟨C0, k, hk⟩ := hA F E
  obtain ⟨c, a, ha⟩ := hB F E
  refine ⟨C0 ^ (N * N) * (max 1 c) ^ (k * (N * N)), a * k * (N * N), fun T hT => ?_⟩
  set B : ℝ := max 1 c * T ^ a with hBdef
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hT)
  obtain ⟨hXf, hXc⟩ := hk B hB1
  set X := {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B} with hXdef
  set S := {γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T} with hSdef
  have hmem : ∀ γ ∈ S, ∀ p : Fin N × Fin N, (γ : Matrix (Fin N) (Fin N) E) p.1 p.2 ∈ X := by
    intro γ hγ p j
    refine (ha _ j).trans ?_
    have h1 : (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ≤ T :=
      (NNReal.coe_le_coe.2 (hC F E N γ p.1 p.2)).trans hγ
    calc c * (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ^ a
        ≤ max 1 c * (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 a)
          (zero_le_one.trans (le_max_left _ _))
  let f : GL (Fin N) E → (Fin N × Fin N → E) := fun γ p => (γ : Matrix (Fin N) (Fin N) E) p.1 p.2
  have hinj : Set.InjOn f S := fun γ _ δ _ h => Units.ext (Matrix.ext fun i j => congrFun h (i, j))
  set P : Finset (Fin N × Fin N → E) := Fintype.piFinset fun _ => hXf.toFinset with hPdef
  have hmaps : ∀ γ ∈ S, f γ ∈ (P : Set (Fin N × Fin N → E)) := fun γ hγ => by
    simp only [P, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun p => hmem γ hγ p
  have hSf : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset (by
    rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj
  refine ⟨hSf, ?_⟩
  have h1 : S.ncard ≤ (P : Set (Fin N × Fin N → E)).ncard :=
    Set.ncard_le_ncard_of_injOn f hmaps hinj P.finite_toSet
  rw [Set.ncard_coe_finset, hPdef, Fintype.card_piFinset] at h1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
  rw [← Set.ncard_eq_toFinset_card X hXf] at h1
  have hC0 : 0 ≤ C0 := by
    have := (Nat.cast_nonneg (α := ℝ) _).trans hXc
    exact nonneg_of_mul_nonneg_left this (by positivity)
  calc ((S.ncard : ℕ) : ℝ) ≤ ((X.ncard : ℝ)) ^ (N * N) := by exact_mod_cast h1
    _ ≤ (C0 * B ^ k) ^ (N * N) := pow_le_pow_left₀ (by positivity) hXc _
    _ = C0 ^ (N * N) * (max 1 c) ^ (k * (N * N)) * T ^ (a * k * (N * N)) := by
        rw [hBdef]; ring

theorem gq_count (hA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k) (hB : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a) (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ)) {D : D7} (V : HSp D) :
    ∃ (C : ℝ) (A : ℕ), ∀ T : ℝ, 1 ≤ T →
      {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T}.Finite ∧
      (({γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T}.ncard : ℕ) : ℝ) ≤ C * T ^ A := by
  obtain ⟨C, A, h⟩ := gl_count hA hB hC D.host.F D.host.E V.rank
  refine ⟨C, A, fun T hT => ?_⟩
  obtain ⟨hf, hc⟩ := h T hT
  have hex : ∀ γ : GQ V, ∃ δ : GL (Fin V.rank) D.host.E,
      bc (inclR (F := D.host.F) (AF D.host.F)) δ = matHom V (γ : GA D V) := by
    intro γ
    have h1 := γ.2
    simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf, Subgroup.mem_map] at h1
    obtain ⟨δ, -, hδ⟩ := h1
    exact ⟨δ, hδ⟩
  choose φ hφ using hex
  have hmaps : ∀ γ ∈ {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T},
      φ γ ∈ {δ : GL (Fin V.rank) D.host.E | (heightGL D.host.F (bc (inclR (F := D.host.F) (AF D.host.F)) δ) : ℝ) ≤ T} := by
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ ⊢
    rw [hφ]
    exact hγ
  have hinj : Set.InjOn φ {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T} := by
    intro a _ b _ hab
    have h2 : matHom V (a : GA D V) = matHom V (b : GA D V) := by rw [← hφ, ← hφ, hab]
    unfold Formalism.L2.Theta.matHom at h2
    exact Subtype.ext (Subgroup.subtype_injective _ h2)
  refine ⟨Set.Finite.of_finite_image (hf.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj, ?_⟩
  exact (Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn φ hmaps hinj hf)).trans hc

theorem ncard_rat_mem_translate_le : ∀ {D : D7} {V : HSp D} {Ω : Set (GA D V)}, IsCompact Ω → ∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A) := by
  intro D V Ω hΩ
  obtain ⟨C, A, hcount⟩ := gq_count GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le GlobalTheory.T.exists_mulHeight_minpoly_coeff_le_relativeHeight GlobalTheory.T.relativeHeight_entry_le_adelicHeightGL V
  have hK : IsCompact ((fun p : GA D V × GA D V => p.1 * p.2⁻¹) '' (Ω ×ˢ Ω)) :=
    (hΩ.prod hΩ).image (by fun_prop)
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hK
  have hC : 0 ≤ C := by
    have := (Nat.cast_nonneg (α := ℝ) _).trans (hcount 1 le_rfl).2
    simpa using this
  refine ⟨A, C * max C₀ 1 ^ A, fun g x => ?_⟩
  rcases Set.eq_empty_or_nonempty {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω} with hS | ⟨γ₀, hγ₀⟩
  · rw [hS]
    refine ⟨Set.finite_empty, ?_⟩
    simp only [Set.ncard_empty, Nat.cast_zero]
    have := GlobalTheory.Grow.height_pos V g
    positivity
  · set T : ℝ := max C₀ 1 * GlobalTheory.Grow.height V g ^ 2 with hTdef
    have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (one_le_pow₀ (GlobalTheory.Grow.one_le_height V g))
    obtain ⟨hf, hc⟩ := hcount T hT
    let φ : GQ V → GQ V := fun γ => γ * γ₀⁻¹
    obtain ⟨y₀, hy₀, e₀⟩ := hγ₀
    have hmaps : ∀ γ ∈ {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω},
        φ γ ∈ {δ : GQ V | GlobalTheory.Grow.height V (δ : GA D V) ≤ T} := by
      intro γ hγ
      obtain ⟨y, hy, e⟩ := hγ
      have h1 : ((φ γ : GQ V) : GA D V) = g * (y * y₀⁻¹) * g⁻¹ := by
        have e' : (γ : GA D V) = g * y * x⁻¹ := by
          rw [show g * y = (γ : GA D V) * x from e, mul_inv_cancel_right]
        have e₀' : (γ₀ : GA D V) = g * y₀ * x⁻¹ := by
          rw [show g * y₀ = (γ₀ : GA D V) * x from e₀, mul_inv_cancel_right]
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, e', e₀']
        group
      have hyy : GlobalTheory.Grow.height V (y * y₀⁻¹) ≤ max C₀ 1 :=
        (hC₀ _ ⟨(y, y₀), ⟨hy, hy₀⟩, rfl⟩).trans (le_max_left _ _)
      show GlobalTheory.Grow.height V ((φ γ : GQ V) : GA D V) ≤ T
      rw [h1]
      calc GlobalTheory.Grow.height V (g * (y * y₀⁻¹) * g⁻¹)
          ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height V (y * y₀⁻¹) * GlobalTheory.Grow.height V g⁻¹ :=
            (GlobalTheory.Grow.height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right (GlobalTheory.Grow.height_mul_le V _ _)
              (GlobalTheory.Grow.height_pos V _).le)
        _ ≤ GlobalTheory.Grow.height V g * max C₀ 1 * GlobalTheory.Grow.height V g := by
            rw [GlobalTheory.Grow.height_inv]
            have := GlobalTheory.Grow.height_pos V g
            gcongr
        _ = T := by rw [hTdef]; ring
    have hinj : Set.InjOn φ {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω} :=
      fun a _ b _ hab => mul_right_cancel hab
    refine ⟨Set.Finite.of_finite_image (hf.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj, ?_⟩
    calc (({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℕ) : ℝ)
        ≤ (({δ : GQ V | GlobalTheory.Grow.height V (δ : GA D V) ≤ T}.ncard : ℕ) : ℝ) :=
          Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn φ hmaps hinj hf)
      _ ≤ C * T ^ A := hc
      _ = C * max C₀ 1 ^ A * GlobalTheory.Grow.height V g ^ (2 * A) := by rw [hTdef]; ring

end GlobalTheory.RatCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NcardRationalPointsInTranslateLeHeightPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_rational_points_in_translate_le_height_pow : ∀ {D : D7} {V : HSp D} {Ω : Set (GA D V)}, IsCompact Ω → ∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A) := by
  first | exact @GlobalTheory.RatCount.ncard_rat_mem_translate_le | exact GlobalTheory.RatCount.ncard_rat_mem_translate_le | (intros; apply GlobalTheory.RatCount.ncard_rat_mem_translate_le <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CuspHS

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Orb

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem norm_convR_le (hP : GlobalTheory.Published.CuspDecayBound) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    ∃ K : ℝ, ∀ F : DividedPowerChartLift V μ, F ∈ L2cusp V μ → ∀ g, ‖convR μ f (lift (GQ V) F) g‖ ≤ K * ‖F‖ := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hfc := continuous_of_mem_ccAd hf
  have hder : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∃ f' ∈ CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : DividedPowerChartLift V μ,
        l.foldr (fun p φ => Rder θ V p.1 p.2 φ) (convR μ f (lift (GQ V) F)) = convR μ f' (lift (GQ V) F) := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨f, hf, subset_rfl, fun F => rfl⟩
    | cons p l ih =>
      intro hl
      obtain ⟨f₁, h₁, s₁, e₁⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      obtain ⟨f₂, h₂, s₂, e₂⟩ := GlobalTheory.T.right_derivative_rightConvolution_eq_test_function μ θ hθ h₁ (hl p List.mem_cons_self)
      exact ⟨f₂, h₂, s₂.trans s₁, fun F => by simp only [List.foldr_cons, e₁ F, e₂ F]⟩
  choose! fl hfl hsl hel using hder
  have hM : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∃ M : ℝ, ∀ y, ‖fl l y‖ ≤ M := fun l hl =>
    have c := continuous_of_mem_ccAd (hfl l hl)
    c.1.bounded_above_of_compact_support c.2
  choose! M hM using hM
  obtain ⟨A, Cg, hg⟩ := GlobalTheory.T.norm_rightConvolution_le_adelic_height_pow μ hfc.2.isCompact (GlobalTheory.T.ncard_rational_points_in_translate_le_height_pow hfc.2.isCompact)
  obtain ⟨U, hU, hlev⟩ := GlobalTheory.T.convolution_right_invariant_open μ hf
  obtain ⟨L, C, hL, hB⟩ := hP D θ hθ V U hU A 0
  refine ⟨C * ∑ l ∈ L, Cg * M l, fun F hF g => ?_⟩
  have hgr : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → ∀ x,
      ‖(l.foldr (fun p φ => Rder θ V p.1 p.2 φ) (convR μ f (lift (GQ V) F))) x‖ ≤
        Cg * M l * ‖F‖ * GlobalTheory.Grow.height V x ^ A := fun l hl x => by
    rw [hel l hl F]
    exact hg _ (continuous_of_mem_ccAd (hfl l hl)).1 (hsl l hl) _ (hM l hl) F x
  have hcont := (GlobalTheory.AutomorphicL2Local.continuous_convR_lift _ (GQ V) μ f hfc.1 hfc.2 F).2
  have key := hB (convR μ f (lift (GQ V) F))
    ⟨fun γ hγ x => ((leftInv_lift (Γ := GQ V) F).convR (μ := μ) f) γ hγ x, ⟨U, hU, hlev F⟩, hcont⟩
    (hlev F) (GlobalTheory.T.contDiff_rightConvolution_along_one_parameter_products μ θ hθ hf F) (fun l hl => ⟨_, hgr l hl⟩) (GlobalTheory.T.convolution_preserves_cuspidal μ hf F hF)
    (fun l => Cg * M l * ‖F‖) (fun l hl x => hgr l (hL l hl) x) g
  rw [pow_zero, mul_one, ← Finset.sum_mul, ← mul_assoc] at key
  exact key

theorem isHilbertSchmidt_RcuspOp (hP : GlobalTheory.Published.CuspDecayBound) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    IsHilbertSchmidt (RcuspOp V μ f) := by
  obtain ⟨K, hK⟩ := norm_convR_le (μ := μ) hP hf
  have hfc := continuous_of_mem_ccAd hf
  have hi : Integrable f μ := hfc.1.integrable_of_hasCompactSupport hfc.2
  have h1 : IsHilbertSchmidt ((L2cusp V μ).subtypeL ∘L RcuspOp V μ f) := by
    refine GlobalTheory.T.isHilbertSchmidt_of_ae_pointwise_bounded_Lp_two _ K fun v => ?_
    have e : ((L2cusp V μ).subtypeL ∘L RcuspOp V μ f) v = RopG V μ f v := coe_RcuspOp V μ hi v
    rw [e]
    refine ae_quotMeasure_iff.2 ?_
    filter_upwards [(GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ (GQ V) μ f hi v).2] with x hx
    have hx' : (RopG V μ f v) (mk (GQ V) x) = convR μ f (lift (GQ V) (v : DividedPowerChartLift V μ)) x := hx
    rw [hx']
    simpa using hK v v.2 x
  exact h1.of_norm_le 1 fun x => by simp

end GlobalTheory.CuspHS

namespace GlobalTheory.Published

theorem cuspTraceClass_of_decay (hP : CuspDecayBound) (hDM : DixmierMalliavinFactorisation) : CuspTraceClass :=
  fun _ _ _ _ _ _ hf => CuspSpectrum.isTraceClass_of_isHilbertSchmidt hDM
    (fun _ hg => CuspHS.isHilbertSchmidt_RcuspOp hP hg) hf

end GlobalTheory.Published

end
