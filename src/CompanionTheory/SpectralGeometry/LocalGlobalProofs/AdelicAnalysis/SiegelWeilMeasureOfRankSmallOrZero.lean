module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentTarget
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddBlockAnisotropic

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureRankZero
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureRankZero
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ZeroTuple

theorem lintegral_unique {V : Type} [MeasurableSpace V] [Unique V] (m : Measure V)
    (h : m Set.univ = 1) (φ : V → ℝ≥0∞) : ∫⁻ x, φ x ∂m = φ default := by
  have : φ = fun _ => φ default := funext fun x => by rw [Subsingleton.elim x default]
  rw [this, lintegral_const, h, mul_one]

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

instance uniqueHerm (σ : E →ₐ[F] E) : Unique (HermR R σ 0) :=
  ⟨⟨0⟩, fun S => Subtype.ext (Matrix.ext fun a => a.elim0)⟩

variable [TopologicalSpace R] [MeasurableSpace R]

theorem coordW_univ {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (M : ℕ) :
    coordW R b lam 0 M Set.univ = 1 := by
  unfold coordW
  rw [Measure.pi_of_empty]
  simp

theorem coordHerm_univ (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) :
    coordHerm R σ b lam 0 Set.univ = 1 := by
  unfold coordHerm
  haveI : IsEmpty {p : Fin 0 × Fin 0 // p.1 < p.2} := ⟨fun p => p.1.1.elim0⟩
  rw [Measure.comap_apply _ (fun x y _ => Subsingleton.elim x y)
    (fun s _ => Subsingleton.measurableSet) _ MeasurableSet.univ]
  rw [Measure.pi_of_empty, Measure.pi_of_empty]
  have : (fun S : HermR R σ 0 =>
      ((fun i : Fin 0 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 0) (Fin 0) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 0 × Fin 0 // p.1 < p.2} =>
          (S : Matrix (Fin 0) (Fin 0) (R ⊗[F] E)) p.1.1 p.1.2))) '' Set.univ = Set.univ :=
    Set.eq_univ_of_forall fun x => ⟨default, Set.mem_univ _, Subsingleton.elim _ _⟩
  rw [this]
  simp


omit [MeasurableSpace R] in
theorem fib_univ (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin 0 → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ 0))
    (m : HermR R σ 0 → Measure (Fin 0 → Fin M → R ⊗[F] E))
    (hμ : μ Set.univ = 1) (hν : ν Set.univ = 1) (h : IsGramFib R σ J 0 μ ν m)
    (S : HermR R σ 0) : m S Set.univ = 1 := by
  obtain ⟨-, h2, -⟩ := h
  have h3 := h2 (fun _ => 1) measurable_const
  have hU : {X : Fin 0 → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} = Set.univ :=
    Set.eq_univ_of_forall fun X => by simp
  rw [hU, Measure.restrict_univ, lintegral_one, hμ] at h3
  simp only [lintegral_one] at h3
  rw [lintegral_unique ν hν (fun b => m b Set.univ)] at h3
  rw [Subsingleton.elim S default]
  exact h3.symm

end Loc

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem theta_univ (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (h0 : μ 𝓕 ≠ 0) (h1 : μ 𝓕 ≠ ⊤) (T : Matrix (Fin 0) (Fin 0) E) :
    thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} Set.univ = 1 := by
  have hS : {X : Fin 0 → Fin M → E | gramE σ J X = T} = Set.univ :=
    Set.eq_univ_of_forall fun X => Subsingleton.elim _ _
  unfold thetaMeas
  rw [hS, Measure.smul_apply, Measure.sum_apply _ MeasurableSet.univ]
  have h2 : ∀ X : (Set.univ : Set (Fin 0 → Fin M → E)),
      ((μ.restrict 𝓕).map fun h => actW (AF F) σ J h⁻¹
        (ratTup (AF F) (X : Fin 0 → Fin M → E))) Set.univ = μ 𝓕 := fun X => by
    rw [Measure.map_apply (measurable_of_subsingleton_codomain _) MeasurableSet.univ]
    simp
  simp only [h2]
  rw [tsum_fintype]
  simp [ENNReal.inv_mul_cancel h0 h1]

end Glob

theorem swMeas_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (T : Matrix (Fin 0) (Fin 0) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J T hT := by
  intro F E _ _ _ _ _ σ hCM M J hJ T hT _ d b laminf lam _ _ μ 𝓕 hμ h𝓕 minf m hinf hv
  have hfin : μ 𝓕 < ⊤ := ((GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M J hJ).2 μ hμ).2 𝓕 h𝓕
  obtain ⟨⟨hLC, hSC, hT2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨tg, lc, sc, t2, bs, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI : Countable Γ := (GlobalTheory.CompanionTheory.SW.rational_countable_discrete F E σ hCM M J hJ).1
  haveI : μ.IsHaarMeasure := hμ
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  have h0 : μ 𝓕 ≠ 0 :=
    (GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain (HA (AF F) σ J) Γ μ 𝓕 h𝓕' hfin).1
  have hI := theta_univ σ J μ 𝓕 h0 hfin.ne T
  have hminf : ∀ S, minf S Set.univ = 1 := fib_univ (Ainf F) σ J _ _ minf
    (coordW_univ _ b laminf M) (coordHerm_univ _ σ b laminf) hinf
  have hm : ∀ v S, m v S Set.univ = 1 := fun v => fib_univ (Fv F v) σ J _ _ (m v)
    (coordW_univ _ b (lam v) M) (coordHerm_univ _ σ b (lam v)) (hv v)
  have hlat : ∀ v, latV b v = (Set.univ : Set (Fin 0 → Fin M → Fv F v ⊗[F] E)) := fun v =>
    Set.eq_univ_of_forall fun Y a => a.elim0
  refine ⟨fun v => ?_, ?_, ∅, fun S _ φinf φ _ _ => ?_⟩
  · rw [hlat, hm]; exact ENNReal.one_lt_top
  · simp [hlat, hm, summable_zero]
  · rw [lintegral_unique _ hI, lintegral_unique _ (hminf _)]
    simp only [lintegral_unique _ (hm _ _), hlat, hm]
    simp only [pureL]
    rw [Set.indicator_of_mem (fun v _ a => a.elim0)]
    simp only [ENNReal.toReal_one, tprod_one, ENNReal.ofReal_one, mul_one, ENNReal.coe_one, one_mul]
    exact congrArg₂ (· * ·) (congrArg φinf (Subsingleton.elim _ _))
      (Finset.prod_congr rfl fun v _ => congrArg (φ v) (Subsingleton.elim _ _))

end GlobalTheory.CompanionTheory.SW.ZeroTuple
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureRankZeroStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_measure_rank_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (T : Matrix (Fin 0) (Fin 0) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.SW.ZeroTuple.swMeas_zero | exact GlobalTheory.CompanionTheory.SW.ZeroTuple.swMeas_zero | (intros; apply GlobalTheory.CompanionTheory.SW.ZeroTuple.swMeas_zero <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfRankSmallOrZero
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AllFrames

theorem swMeas_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 →
    SWMeas σ J T hT := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro M J hJ _ T hT hd
    exact GlobalTheory.T.siegel_weil_measure_rank_zero F E σ hσ M J hJ T hT hd
  | succ n ih =>
    intro M J hJ hn T hT hd
    have hM : n + 3 ≤ M := by omega
    obtain ⟨t, x, ht, hx⟩ := GlobalTheory.CompanionTheory.SW.HermRep.exists_repr F E σ hσ n T ⟨hT, hd⟩
    obtain ⟨g, T₁, hT₁, hb, -⟩ :=
      GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hσ n T ⟨hT, hd⟩ t x ht hx
    obtain ⟨hdet, hblk, -, -⟩ := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hσ n T₁ t
    have hT' := hblk hT₁.1
    have htE : algebraMap F E t ≠ 0 := by
      simpa using ht
    have hd' : (blockOne (algebraMap F E t) T₁).det ≠ 0 := by
      rw [hdet]
      exact mul_ne_zero htE hT₁.2
    refine GlobalTheory.T.siegel_weil_measure_of_congruent_target F E σ hσ M J hJ (n + 1) T hT hd g _ hT' hb ?_
    by_cases hrep : ∃ y : Fin M → E, hE σ J y y = algebraMap F E t
    · obtain ⟨y, hy⟩ := hrep
      obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 1 := ⟨M - 1, by omega⟩
      obtain ⟨g', J₁, hJ₁, hb', -⟩ :=
        GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hσ M₁ J hJ t y ht hy
      refine GlobalTheory.T.siegel_weil_measure_of_congruent_form F E σ hσ (M₁ + 1) J hJ g' _ hb' (n + 1) _ hT' hd' ?_
      exact GlobalTheory.T.siegel_weil_measure_add_rank_one_block F E σ hσ M₁ J₁ hJ₁ t ht n (by omega) T₁ hT₁.1 hT₁.2 hT'
        (ih M₁ J₁ hJ₁ (Or.inr (by omega)) T₁ hT₁.1 hT₁.2)
    · exact GlobalTheory.T.siegel_weil_measure_block_one_of_not_represented F E σ hσ M J hJ t ht n hM T₁ hT₁.1 hT₁.2 hT'
        (fun y hy => hrep ⟨y, hy⟩)

end GlobalTheory.CompanionTheory.SW.AllFrames
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfRankSmallOrZeroStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_measure_of_rank_small_or_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.SW.AllFrames.swMeas_all | exact GlobalTheory.CompanionTheory.SW.AllFrames.swMeas_all | (intros; apply GlobalTheory.CompanionTheory.SW.AllFrames.swMeas_all <;> assumption)
end
