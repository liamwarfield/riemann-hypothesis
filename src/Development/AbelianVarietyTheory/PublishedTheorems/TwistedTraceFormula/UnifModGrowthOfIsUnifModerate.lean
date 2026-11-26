module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
noncomputable section

open scoped TensorProduct ContDiff
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published


open GlobalTheory.Grow in
def CuspDecayBound : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ A N : ℕ,
      ∃ (L : Finset (List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ),
        (∀ l ∈ L, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧
        ∀ φ : GA D V → ℂ, IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) →
          (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
            (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
              ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) →
          (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
            ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)) →
          IsCuspFun V φ →
          ∀ c : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) → ℝ,
            (∀ l ∈ L, ∀ g, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) g‖ ≤ c l * height V g ^ A) →
            ∀ g, ‖φ g‖ * quotHeight V g ^ N ≤ C * ∑ l ∈ L, c l

end GlobalTheory.Published

namespace GlobalTheory.Grow

open GlobalTheory.SmoothForms
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (IsUnifModerate IsSmoothInf)

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem quotHeight_comparison (hθ : IsInfFam θ) (V : HSp D) : ∃ C : ℝ, 0 < C ∧ ∀ g : GA D V,
    (GlobalTheory.CuspDecay.quotHeight θ V g : ℝ) ≤ C * quotHeight V g ∧
      quotHeight V g ≤ C * (GlobalTheory.CuspDecay.quotHeight θ V g : ℝ) := by
  obtain ⟨C, hC, h⟩ := height_comparison V hθ
  refine ⟨C * 2, by positivity, fun g => ⟨?_, ?_⟩⟩
  · obtain ⟨γ, hγ, h2⟩ := exists_height_le_two_mul_quotHeight V g
    rw [mul_assoc]
    exact (NNReal.coe_le_coe.2 (GlobalTheory.CuspDecay.quotHeight_le g hγ)).trans
      ((h _).1.trans (mul_le_mul_of_nonneg_left h2 hC.le))
  · obtain ⟨γ, hγ, h2⟩ := GlobalTheory.CuspDecay.exists_height_le (θ := θ) g
    rw [mul_assoc]
    exact (quotHeight_le V g hγ).trans ((h _).2.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast h2) hC.le))

theorem rapidDec_iff_isRapidDecay (hθ : IsInfFam θ) {φ : GA D V → ℂ} :
    RapidDec V φ ↔ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ Continuous φ ∧ GlobalTheory.CuspDecay.IsRapidDecay θ V φ := by
  obtain ⟨K, hK, h⟩ := quotHeight_comparison hθ V
  have key : ∀ {a b x C : ℝ} {N : ℕ}, 0 ≤ a → 0 ≤ x → a ≤ K * b → x * b ^ N ≤ C → x * a ^ N ≤ K ^ N * C :=
    fun {a b x C N} ha hx h1 h2 => (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha h1 N) hx).trans (by
      rw [mul_pow, mul_left_comm]; exact mul_le_mul_of_nonneg_left h2 (pow_pos hK N).le)
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun N => ⟨?_, ?_⟩
  · rintro ⟨C, hC⟩
    exact ⟨_, fun g => key (NNReal.coe_nonneg _) (norm_nonneg _) (h g).1 (hC g)⟩
  · rintro ⟨C, hC⟩
    exact ⟨_, fun g => key (quotHeight_pos V g).le (norm_nonneg _) (h g).2 (hC g)⟩

theorem unifModGrowth_of_isUnifModerate (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsUnifModerate θ V (expInf θ V) φ) : UnifModGrowth V θ φ := by
  obtain ⟨K, hK, hh⟩ := height_comparison V hθ
  obtain ⟨A, hA⟩ := h
  have key : ∀ ψ : GA D V → ℂ, (∃ C : ℝ, ∀ g, ‖ψ g‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ A) →
      ModGrowthExp V A ψ := by
    rintro ψ ⟨C, hC⟩
    refine ⟨|C| * K ^ A, fun g => (hC g).trans ?_⟩
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hh g).1 A)
      (pow_nonneg (NNReal.coe_nonneg _) A) (abs_nonneg _)
  refine ⟨A, fun l hl => key _ ?_⟩
  obtain ⟨l', hl'⟩ := exists_sigma_list l hl
  rw [hl', foldr_Rder_eq ((GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V)]
  exact hA _

theorem unifModGrowth_of_isAutFunSm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) :
    UnifModGrowth V θ φ :=
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  unifModGrowth_of_isUnifModerate hθ ((growth_iff hθ R h.toIsAutFun ((smooth_iff R φ).1 h.smooth)).1 h.growth)

theorem cuspRapidDecay_of_bound (hP : GlobalTheory.Published.CuspDecayBound) : GlobalTheory.Published.CuspRapidDecay := by
  intro D θ hθ V e he φ ha hs hg hc
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain rfl := eq_expInf R he
  obtain ⟨A, hA⟩ := unifModGrowth_of_isUnifModerate hθ hg
  obtain ⟨U, hU, hφ⟩ := ha.level
  refine ((rapidDec_iff_isRapidDecay hθ).1 ⟨ha.left, ha.cont, fun N => ?_⟩).2.2
  obtain ⟨L, C, hL, h⟩ := hP D θ hθ V U hU A N
  choose! c hc' using hA
  exact ⟨_, h φ ha hφ ((smooth_iff R φ).2 hs) (fun l hl => ⟨c l, hc' l hl⟩) hc c fun l hl => hc' l (hL l hl)⟩

theorem rapidDec_of_unifModGrowth (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hg : UnifModGrowth V θ φ) (hc : IsCuspFun V φ) : RapidDec V φ :=
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hs' := (smooth_iff R φ).1 hs
  (rapidDec_iff_isRapidDecay hθ).2 ⟨ha.left, ha.cont,
    hP D θ hθ V _ (isExpFam_expInf R) φ ha hs' ((growth_iff hθ R ha hs').1 (hg.growth hθ)) hc⟩

theorem rapidDec_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : RapidDec V φ :=
  rapidDec_of_unifModGrowth hP hθ h.toIsAutFun h.smooth (unifModGrowth_of_isAutFunSm hθ h) hc

theorem RapidDec.integrableOn_fundamentalDomain {Φ : GA D V → ℂ} (h : RapidDec V Φ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : IntegrableOn Φ 𝓕 μ :=
  h.integrableOn (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne

theorem RapidDec.integrableOn_mul_of_le {f Φ : GA D V → ℂ} (h : RapidDec V Φ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hm : AEStronglyMeasurable f (μ.restrict 𝓕)) {C : ℝ} {A : ℕ} (hf : ∀ g, ‖f g‖ ≤ C * quotHeight V g ^ A) :
    IntegrableOn (f * Φ) 𝓕 μ := by
  obtain ⟨B, hB⟩ := h.decay A
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  refine Integrable.of_bound (hm.mul h.continuous.aestronglyMeasurable) (|C| * B) (.of_forall fun g => ?_)
  have hq := (pow_pos (quotHeight_pos V g) A).le
  calc ‖(f * Φ) g‖ = ‖f g‖ * ‖Φ g‖ := norm_mul _ _
    _ ≤ |C| * quotHeight V g ^ A * ‖Φ g‖ :=
        mul_le_mul_of_nonneg_right ((hf g).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hq)) (norm_nonneg _)
    _ = |C| * (‖Φ g‖ * quotHeight V g ^ A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB g) (abs_nonneg C)

theorem RapidDec.integrableOn_modGrowth_mul {f Φ : GA D V → ℂ} (h : RapidDec V Φ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hf : ModGrowth V f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (hm : AEStronglyMeasurable f (μ.restrict 𝓕)) :
    IntegrableOn (f * Φ) 𝓕 μ := by
  obtain ⟨C, A, hC⟩ := hf
  exact h.integrableOn_mul_of_le hμ h𝓕 hm (norm_le_quotHeight_pow hl hC)

end GlobalTheory.Grow

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
noncomputable section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelFormula

variable {D : D7}

def coord {d m n : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) :
    Fin m × Fin n × Fin d → AF D.host.F :=
  fun p => (Algebra.TensorProduct.basis (AF D.host.F) ε).repr (x p.1 p.2.1) p.2.2

def invPt (B : HSp D) {a : ℕ} (h : GA D B) (ξ : Matrix (Fin B.rank) (Fin a) D.host.E) : Mx D B.rank a :=
  HMul.hMul (Formalism.L2.Theta.mt B h⁻¹) (ξ.map (incA D))

def absTheta (B : HSp D) {a : ℕ} (φ : Mx D B.rank a → ℂ) (h : GA D B) : ℝ≥0∞ :=
  ∑' ξ : Matrix (Fin B.rank) (Fin a) D.host.E, ‖φ (invPt B h ξ)‖ₑ

def absThetaInt (B : HSp D) (m : Measure (GA D B)) {a : ℕ} (φ : Mx D B.rank a → ℂ) : ℝ≥0∞ :=
  ∫⁻ q, descend (GQ B) (absTheta B φ) q ∂autMeasure B m

def pureS {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (g : WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) : WeilM.schA F κ :=
  ⟨WeilM.pureA F f g, Submodule.subset_span ⟨f, g, g.2, rfl⟩⟩

def IsContSeminorm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ν : Seminorm ℂ (WeilM.schA F κ)) : Prop :=
  ∀ g, Continuous fun f => ν (pureS g f)

def lagr (A B : HSp D) (y : Mx D B.rank A.rank) : WO (dblSp A) B :=
  Matrix.of fun i => pairVec finSumFinEquiv (y i) (-y i)

def valZero (A B : HSp D) (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)) (f : WO (dblSp A) B → ℂ) : ℂ :=
  ∫ y in 𝓖, f (lagr A B y) ∂ν

def swSection (A B : HSp D) (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank))
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (f : WO (dblSp A) B → ℂ) : GA D (dblSp A) → ℂ :=
  fun g => valZero A B ν 𝓖 (ω (g, 1) f)

end GlobalTheory.SiegelFormula

namespace GlobalTheory.Published

open GlobalTheory.SiegelFormula

def WeilSiegelFormulaUnitary : Prop :=
  ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank →
    (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) →
    (∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E),
      ∃ ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)), IsContSeminorm ν ∧
        ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d),
          absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ)) ∧
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
      IsWeilDatumO ψ (dblSp A) B 1 χ ω → ∀ f, IsThetaFunO ψ (dblSp A) B f →
      (∀ g, Integrable (descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B m)) ∧
      (2 * A.rank < B.rank → ∀ ν 𝓖, IsCovolOne (ratL B A) ν 𝓖 →
        LeftInv (siegelQ A) (swSection A B ν 𝓖 ω f) ∧ ∀ g, CosetConv (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g ∧
          cosetSum (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g = ⨍ q, descend (GQ B) (fun h => thetaKO ω g h f) q ∂autMeasure B m)

end GlobalTheory.Published

namespace GlobalTheory.SiegelFormula

variable {D : D7}

theorem leftInv_absTheta (B : HSp D) {a : ℕ} (φ : Mx D B.rank a → ℂ) : LeftInv (GQ B) (absTheta B φ) := by
  intro γ hγ h
  obtain ⟨δ, -, hδ⟩ : ∃ δ : GL (Fin B.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom B γ⁻¹ := inv_mem hγ
  let e : Matrix (Fin B.rank) (Fin a) D.host.E ≃ Matrix (Fin B.rank) (Fin a) D.host.E :=
    ⟨fun ξ => δ.1 * ξ, fun ξ => δ⁻¹.1 * ξ, fun ξ => by simp, fun ξ => by simp⟩
  have h1 : Formalism.L2.Theta.mt B γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt B (γ * h)⁻¹ = Formalism.L2.Theta.mt B h⁻¹ * Formalism.L2.Theta.mt B γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => ‖φ (invPt B h ξ)‖ₑ)
  simp only [invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

theorem leftInv_thetaKO {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT ω) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (g : GA D S) : LeftInv (GQ T) fun h => thetaKO ω g h f := fun γ hγ h => by
  have e : ω (g, γ * h) = ω (1, γ) * ω (g, h) := by rw [← map_mul, Prod.mk_mul_mk, one_mul]
  simp only [thetaKO, e, Module.End.mul_apply]
  exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ f hf)

theorem om_rat_apply {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT ω) {f : WO S T → ℂ}
    {γ : GA D S} (hγ : γ ∈ GQ S) {δ : GA D T} (hδ : δ ∈ GQ T) (w : WO S T)
    (hf : IsThetaFunO ψ S T f) (hw : IsThetaFunO ψ S T (heisO ψ S T w f)) : ω (γ, δ) f (actO S T γ δ w) = f w := by
  have h1 := hω.om_aut γ hγ δ hδ _ hw
  rw [hω.om_heis _ _ _ _ hf] at h1
  simpa [heisO, symplOH, symplO, hO] using h1

end GlobalTheory.SiegelFormula

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsQuotHeightMulExpInfLe
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

def CuspBounded : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ →
      (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
        (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
          ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) →
      (∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
          ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) →
      IsCuspFun V φ →
      ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∃ C : ℝ, ∀ g, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) g‖ ≤ C

end GlobalTheory.Published

namespace GlobalTheory.CuspDecay

open GlobalTheory.SmoothForms

theorem mul_norm_deriv_le {f f₁ f₂ : ℝ → ℂ} (h₁ : ∀ t, HasDerivAt f (f₁ t) t) (h₂ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    {h B : ℝ} (hh : 0 ≤ h) (hB : ∀ t ∈ Set.Icc 0 h, ‖f₂ t‖ ≤ B) :
    h * ‖f₁ 0‖ ≤ ‖f h‖ + ‖f 0‖ + B * h * h := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hh⟩)
  have a1 : ∀ t ∈ Set.Icc 0 h, ‖f₁ t - f₁ 0‖ ≤ B * h := fun t ht => by
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f₁) (f' := f₂) (a := 0) (b := h) (C := B)
      (fun s _ => (h₂ s).hasDerivWithinAt) (fun s hs => hB s ⟨hs.1, hs.2.le⟩) t ht
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB0)
  have a2 := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t : ℝ => f t - t • f₁ 0)
    (f' := fun t => f₁ t - f₁ 0) (a := 0) (b := h) (C := B * h)
    (fun s _ => by
      have := ((h₁ s).sub ((hasDerivAt_id s).smul_const (f₁ 0))).hasDerivWithinAt (s := Set.Icc 0 h)
      rwa [one_smul] at this)
    (fun s hs => a1 s ⟨hs.1, hs.2.le⟩) h ⟨hh, le_rfl⟩
  have e : h • f₁ 0 = f h - f 0 - (f h - h • f₁ 0 - (f 0 - (0 : ℝ) • f₁ 0)) := by rw [zero_smul]; ring
  have a3 : ‖h • f₁ 0‖ ≤ ‖f h‖ + ‖f 0‖ + B * h * (h - 0) := by
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) a2)
  rwa [norm_smul, Real.norm_of_nonneg hh, sub_zero] at a3

theorem decay_of_decay_of_growth {G : Type} [Group G] {q : G → ℝ} (hq : ∀ g, 1 ≤ q g) {a : ℝ → G} (a0 : a 0 = 1)
    (ha : ∀ s t, a (s + t) = a s * a t) {c : ℝ} (hc : ∀ g, ∀ t ∈ Set.Icc (-1 : ℝ) 1, q (g * a t) ≤ c * q g)
    {ψ ψ₁ ψ₂ : G → ℂ} (h₁ : ∀ g, HasDerivAt (fun t => ψ (g * a t)) (ψ₁ g) 0)
    (h₂ : ∀ g, HasDerivAt (fun t => ψ₁ (g * a t)) (ψ₂ g) 0)
    (hψ : ∀ M : ℕ, ∃ C : ℝ, ∀ g, ‖ψ g‖ * q g ^ M ≤ C) {N : ℕ} {B : ℝ} (hB : ∀ g, ‖ψ₂ g‖ ≤ B * q g ^ N) (M : ℕ) :
    ∃ C : ℝ, ∀ g, ‖ψ₁ g‖ * q g ^ M ≤ C := by
  have shift : ∀ {χ χ₁ : G → ℂ}, (∀ g, HasDerivAt (fun t => χ (g * a t)) (χ₁ g) 0) →
      ∀ g s, HasDerivAt (fun t => χ (g * a t)) (χ₁ (g * a s)) s := fun {χ χ₁} h g s => by
    have h1 : HasDerivAt (fun t => χ (g * a s * a t)) (χ₁ (g * a s)) (s - s) := by rw [sub_self]; exact h _
    have h2 := h1.comp_sub_const s s
    simpa only [mul_assoc, ← ha, add_sub_cancel] using h2
  obtain ⟨C, hC⟩ := hψ (N + M + M)
  refine ⟨|c| ^ (N + M + M) * C + C + |B| * |c| ^ N, fun g => ?_⟩
  have q0 : 0 < q g := zero_lt_one.trans_le (hq g)
  have p1 : 1 ≤ q g ^ (N + M) := one_le_pow₀ (hq g)
  set h := (q g ^ (N + M))⁻¹ with hh
  have h0 : 0 < h := by positivity
  have h1 : h ≤ 1 := inv_le_one_of_one_le₀ p1
  have key := mul_norm_deriv_le (shift h₁ g) (shift h₂ g) h0.le (B := |B| * (|c| * q g) ^ N) fun t ht =>
    (hB _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (zero_le_one.trans (hq _))
      ((hc g t ⟨by linarith [ht.1], ht.2.trans h1⟩).trans (mul_le_mul_of_nonneg_right (le_abs_self _) q0.le)) N)
      (pow_nonneg (zero_le_one.trans (hq _)) N) (abs_nonneg _))
  simp only [a0, mul_one] at key
  have b1 : q g ≤ |c| * q (g * a h) := by
    have := hc (g * a h) (-h) ⟨by linarith, by linarith⟩
    rw [mul_assoc, ← ha, add_neg_cancel, a0, mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans (hq _)))
  have b2 : ‖ψ (g * a h)‖ * q g ^ (N + M + M) ≤ |c| ^ (N + M + M) * C :=
    calc ‖ψ (g * a h)‖ * q g ^ (N + M + M) ≤ ‖ψ (g * a h)‖ * (|c| * q (g * a h)) ^ (N + M + M) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ q0.le b1 _) (norm_nonneg _)
      _ = |c| ^ (N + M + M) * (‖ψ (g * a h)‖ * q (g * a h) ^ (N + M + M)) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC _) (by positivity)
  calc ‖ψ₁ g‖ * q g ^ M = h * ‖ψ₁ g‖ * q g ^ (N + M + M) := by rw [hh]; field_simp; ring
    _ ≤ (‖ψ (g * a h)‖ + ‖ψ g‖ + |B| * (|c| * q g) ^ N * h * h) * q g ^ (N + M + M) :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = ‖ψ (g * a h)‖ * q g ^ (N + M + M) + ‖ψ g‖ * q g ^ (N + M + M) + |B| * |c| ^ N := by
        rw [hh]; field_simp; ring
    _ ≤ _ := add_le_add (add_le_add b2 (hC g)) le_rfl

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem expInf_add_smul (R : RealPoints θ V) (X : LieInf V) (s t : ℝ) :
    expInf θ V ((s + t) • X : LieInf V) = expInf θ V (s • X : LieInf V) * expInf θ V (t • X : LieInf V) := by
  have he := isExpFam_expInf R
  refine R.2.2.1 _ (he _).1 _ (mul_mem (he _).1 (he _).1) fun τ => ?_
  rw [R.2.2.2.1, (he _).2, (he _).2, (he _).2]
  change NormedSpace.exp ((s + t) • (X τ).1) = NormedSpace.exp (s • (X τ).1) * NormedSpace.exp (t • (X τ).1)
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)]

theorem expInf_zero_smul (R : RealPoints θ V) (X : LieInf V) : expInf θ V ((0 : ℝ) • X : LieInf V) = 1 := by
  have := expInf_add_smul R X 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem continuous_infNorm_expInf (R : RealPoints θ V) (X : LieInf V) (τ : D.what₂.Tau) :
    Continuous fun t : ℝ => infNorm θ V τ (expInf θ V (t • X : LieInf V)) := by
  have h1 : Continuous fun t : ℝ => NormedSpace.exp (t • (X τ).1) := by
    have : CompleteSpace (AlgInf V) := FiniteDimensional.complete ℝ _
    letI : NormedAlgebra ℚ (AlgInf V) := NormedAlgebra.restrictScalars ℚ ℝ _
    have h0 : Continuous fun t : ℝ => (NormedSpace.exp (t • jInf V X) : AlgInf V) :=
      NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    have h3 : Continuous fun u : AlgInf V => u τ := continuous_apply τ
    exact (h3.comp h0).congr fun t => exp_algInf V _ τ
  have h2 : Continuous (Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ)) :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
  refine (h2.comp h1).nnnorm.congr fun t => ?_
  rw [infNorm, (isExpFam_expInf R _).2]
  rfl

theorem exists_quotHeight_mul_expInf_le (R : RealPoints θ V) (X : LieInf V) : ∃ c : ℝ, ∀ g, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
    (quotHeight θ V (g * expInf θ V (t • X : LieInf V)) : ℝ) ≤ c * quotHeight θ V g := by
  have hinv : ∀ t : ℝ, (expInf θ V (t • X : LieInf V))⁻¹ = expInf θ V ((-t) • X : LieInf V) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← expInf_add_smul R, add_neg_cancel, expInf_zero_smul R])
  have hcont : Continuous fun t : ℝ => ((∏ τ, infHt θ V τ (expInf θ V (t • X : LieInf V)) : NNReal) : ℝ) := by
    refine NNReal.continuous_coe.comp (continuous_finsetProd _ fun τ _ => ?_)
    simp only [infHt, hinv]
    exact continuous_const.max ((continuous_infNorm_expInf R X τ).max
      ((continuous_infNorm_expInf R X τ).comp continuous_neg))
  obtain ⟨c, hc⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image hcont.continuousOn
  refine ⟨2 * c, fun g t ht => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 := (quotHeight_le (θ := θ) (g * expInf θ V (t • X : LieInf V)) hγ).trans
    ((congrArg _ (mul_assoc _ _ _).symm).trans_le
      (HeightCoset.height_mul_le θ V (γ * g) _ (isExpFam_expInf R (t • X)).1))
  have h2 := NNReal.coe_le_coe.2 (h1.trans (mul_le_mul_left hle _))
  rw [NNReal.coe_mul, NNReal.coe_mul] at h2
  refine h2.trans ((mul_le_mul_of_nonneg_left (hc ⟨t, ht, rfl⟩) (by positivity)).trans_eq ?_)
  push_cast
  ring

theorem IsRapidDecay.wordDer (R : RealPoints θ V) {φ : GA D V → ℂ} (h : IsRapidDecay θ V φ)
    (hl : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (hs : IsSmoothInf V (expInf θ V) φ)
    (hg : IsUnifModerate θ V (expInf θ V) φ) (l : List (LieInf V)) :
    IsRapidDecay θ V (wordDer V (expInf θ V) l φ) := by
  have sm : ∀ l : List (LieInf V), Sm (expInf θ V) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.wordDer V (expInf θ V) l φ) := fun l => by
    rw [show φ = (⟨φ, hs⟩ : SmF θ V).1 from rfl, wordDer_eq R]
    exact Subtype.prop _
  induction l with
  | nil => exact h
  | cons X l ih =>
    obtain ⟨N, hN⟩ := hg
    obtain ⟨B, hB⟩ := hN (X :: X :: l)
    obtain ⟨c, hc⟩ := exists_quotHeight_mul_expInf_le R X
    refine decay_of_decay_of_growth (q := fun g => (quotHeight θ V g : ℝ))
      (fun g => by exact_mod_cast one_le_quotHeight g) (a := fun t => expInf θ V (t • X : LieInf V))
      (expInf_zero_smul R X) (expInf_add_smul R X) hc
      (ψ₂ := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.wordDer V (expInf θ V) (X :: X :: l) φ)
      (fun g => ((sm l).differentiableAt g X).hasDerivAt) (fun g => ((sm (X :: l)).differentiableAt g X).hasDerivAt)
      ih (N := N) (B := |B| * 2 ^ N) fun g => ?_
    obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
    have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
    rw [← wordDer_left (expInf θ V) (hl γ hγ) _ g, mul_assoc, ← mul_pow]
    exact (hB _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h1 N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _))

theorem isRapidDecay_foldr_Rder (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hg : ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N)
    (hc : IsCuspFun V φ) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) : IsRapidDecay θ V (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  have R := (RealPts.realPoints D).2 θ hθ V
  have hs' := (smooth_iff R φ).1 hs
  have hg' := (growth_iff hθ R ha hs').1 hg
  obtain ⟨l', rfl⟩ := exists_sigma_list l hl
  rw [foldr_Rder_eq R]
  exact (hP D θ hθ V _ (isExpFam_expInf R) φ ha hs' hg' hc).wordDer R ha.left hs' hg' _

theorem cuspBounded_of_cuspRapidDecay (hP : GlobalTheory.Published.CuspRapidDecay) : GlobalTheory.Published.CuspBounded :=
  fun _ _ hθ _ _ ha hs hg hc l hl => (isRapidDecay_foldr_Rder hP hθ ha hs hg hc l hl).bounded

theorem memLp_of_bounded {φ : GA D V → ℂ} (hφ : Continuous φ) (hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (p : ENNReal) :
    MemLp φ p (μ.restrict 𝓕) := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  obtain ⟨C, hC⟩ := hb
  exact MemLp.of_bound hφ.measurable.aestronglyMeasurable C (.of_forall hC)

theorem memLp_two_of_cuspBounded (hP : GlobalTheory.Published.CuspBounded) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hg : ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N)
    (hc : IsCuspFun V φ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : MemLp φ 2 (μ.restrict 𝓕) :=
  memLp_of_bounded ha.cont (hP D θ hθ V φ ha hs hg hc [] fun _ h => absurd h List.not_mem_nil) μ 𝓕 hμ h𝓕 2

end GlobalTheory.CuspDecay

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published
open GlobalTheory.Parabolic (isIrreducible_of_equiv)

namespace GlobalTheory.SegmentRepModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def Concl {d : ℕ} (σ : Representation ℂ (GL (Fin d) k) V) (l : ℕ) : Prop :=
  ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
    S.toRepresentation.IsIrreducible ∧
    (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
      S'.toRepresentation.IsIrreducible → S' = S) ∧
    Nonempty ((GlobalTheory.SmGL.jac (consecBlocks l d) S.toRepresentation).Equiv (piTensor (segTerm σ l)))

def jacCongr {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) : (GlobalTheory.SmGL.jac e π).Equiv (GlobalTheory.SmGL.jac e τ) :=
  equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap,
      fun y => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact congrArg Submodule.Quotient.mk (φ.symm_apply_apply v),
      fun y => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact congrArg Submodule.Quotient.mk (φ.apply_symm_apply v)⟩)

theorem concl_of_isSocle {d l : ℕ} {σ : Representation ℂ (GL (Fin d) k) V}
    {τ : Representation ℂ (GL (Fin (l * d)) k) W}
    (h : IsSocle τ (multiProd (consecBlocks l d) (segTerm σ l)))
    (hj : Nonempty ((GlobalTheory.SmGL.jac (consecBlocks l d) τ).Equiv (piTensor (segTerm σ l)))) : Concl σ l := by
  obtain ⟨hi, f, hf, hS⟩ := h
  have inc : ∀ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
      ∃ g : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ l)),
        Function.Injective g ∧ g.range = S := fun S =>
    ⟨⟨S.toSubmodule.subtype, fun _ => rfl⟩, Subtype.val_injective,
      Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)⟩
  obtain ⟨g, hg, hr⟩ := inc f.range
  obtain ⟨φ⟩ := nonempty_equiv_of_range_eq f hf g hg hr.symm
  obtain ⟨ψ⟩ := hj
  refine ⟨f.range, isIrreducible_of_equiv φ hi, fun S' hS' => ?_, ⟨(jacCongr _ φ.symm).trans ψ⟩⟩
  obtain ⟨g', hg', hr'⟩ := inc S'
  exact hS _ (hr' ▸ isAtom_range hS' g' hg')

theorem concl_two {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) : Concl (detRep (Fin 1) χ) 2 := by
  classical
  have he : consecBlocks 2 1 = (ProjLine.pts : (Σ _ : Fin 2, Fin 1) ≃ Fin (2 * 1)) := by
    ext ⟨a, j⟩
    rw [consecBlocks_val, ProjLine.pts_apply]
    omega
  have hη : IsSmoothChar (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)) := hχ.mul (isSmoothChar_absPow _)
  obtain ⟨ψ⟩ := nonempty_jac_det_equiv (consecBlocks 2 1) χ
  refine concl_of_isSocle (τ := detRep (Fin (2 * 1)) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))) ?_ ⟨ψ⟩
  obtain ⟨X, _, _, π, f, ⟨φ⟩, hf, h0, h, -⟩ := ProjLine.exists_line hη
  let a : (ofChar (detLevi (consecBlocks 2 1) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)))).Equiv
      (GlobalTheory.SmGL.jac (consecBlocks 2 1) (detRep (Fin (2 * 1)) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)))) :=
    .mk (Submodule.quotEquivOfEqBot _ (twKer_detRep _ _)).symm fun g => LinearMap.ext fun c => by
      simp only [LinearMap.comp_apply]
      rw [Model.jac_detRep, ofChar_apply]
      exact map_smul _ (_ : ℂ) c
  have b := parIndEquiv (consecBlocks 2 1) (a.trans ψ)
  have φ' : π.Equiv (parInd (consecBlocks 2 1)
      (ofChar (detLevi (consecBlocks 2 1) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))))) := by
    rw [he]; exact φ
  exact (ProjLine.isSocle_of_le (isIrreducible_ofChar _) f hf h0 h).of_equiv (.refl _) (φ'.trans b)

end GlobalTheory.SegmentRepModel

end
end
