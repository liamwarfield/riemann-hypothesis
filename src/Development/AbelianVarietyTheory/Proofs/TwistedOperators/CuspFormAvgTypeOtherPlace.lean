module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AvgOtherPlace

open Formalism.MainNotions.S Formalism.REAL MeasureTheory Matrix GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open scoped TensorProduct

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem atTau_comm (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) {g h : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ')) :
    atTau θ V τ g * atTau θ V τ' h = atTau θ V τ' h * atTau θ V τ g := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have a := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  have b := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ' hh
  refine R.2.2.1 _ (mul_mem a.1 b.1) _ (mul_mem b.1 a.1) fun ρ => ?_
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul]
  by_cases c : ρ = τ
  · subst c
    rw [a.2.1, b.2.2 ρ (Ne.symm hne), Matrix.mul_one, Matrix.one_mul]
  · rw [a.2.2 ρ c, Matrix.mul_one, Matrix.one_mul]

theorem adAt_atTau_of_ne (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    adAt θ (atTau θ V τ g) τ' X = X := by
  have a := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  have b := GlobalTheory.PointAtPlaceHom.isAtTau_inv V τ hg a
  rw [adAt, a.2.2 τ' hne, b.2.2 τ' hne, Matrix.one_mul, Matrix.mul_one]

section Avg

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}


variable (θ V) in
def avgF (τ : D.what₂.Tau) (κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ) (e : K → ℂ) (φ : GA D V → ℂ) : GA D V → ℂ :=
  fun x => ∫ k, e k * φ (x * atTau θ V τ (κ k)) ∂μ

theorem avgF_zero : avgF θ V μ τ κ e 0 = 0 := by
  funext x
  simp [avgF]

theorem avgF_add (hθ : IsInfFam θ) (hκ : Continuous κ) (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (he : Continuous e) {f g : GA D V → ℂ} (hf : Continuous f) (hg : Continuous g) :
    avgF θ V μ τ κ e (f + g) = avgF θ V μ τ κ e f + avgF θ V μ τ κ e g := by
  funext x
  simp only [avgF, Pi.add_apply, mul_add]
  exact integral_add (GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hf x)
    (GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hg x)

theorem avgF_smul (c : ℂ) (f : GA D V → ℂ) : avgF θ V μ τ κ e (c • f) = c • avgF θ V μ τ κ e f := by
  funext x
  simp only [avgF, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul c _

theorem avgF_Rder (hθ : IsInfFam θ) (hne : τ' ≠ τ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (he : Continuous e) {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ') :
    Rder θ V τ' X (avgF θ V μ τ κ e ψ) = avgF θ V μ τ κ e (Rder θ V τ' X ψ) := by
  set 𝒟 : Set (GA D V → ℂ) := {ψ | IsAutFunSm θ V ψ}
  have h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ := fun _ h => h
  have hR : ∀ ψ ∈ 𝒟, ∀ τ'' X, X ∈ lieAt V τ'' → Rder θ V τ'' X ψ ∈ 𝒟 :=
    fun _ h _ _ hX => GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX h
  have F := GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives D θ hθ V K μ (GlobalTheory.RealAverage.famSpan θ V τ κ 𝒟)
    (GlobalTheory.RealAverage.famSpan_cont hθ hκ hU h𝒟) (GlobalTheory.RealAverage.famSpan_sm hθ hU h𝒟)
    (GlobalTheory.RealAverage.famSpan_Rder hθ hκ hU h𝒟 hR)
    (fun k x => e k * ψ (x * atTau θ V τ (κ k))) (Submodule.subset_span ⟨e, he, ψ, hψ, rfl⟩)
  have h1 := F.2.2.1 [(τ', X)] (by simpa using hX)
  simp only [List.foldr_cons, List.foldr_nil] at h1
  show Rder θ V τ' X (fun x => ∫ k, e k * ψ (x * atTau θ V τ (κ k)) ∂μ) = _
  rw [h1]
  funext x
  simp only [avgF]
  congr 1
  funext k
  have e1 : (fun x => e k * ψ (x * atTau θ V τ (κ k))) = e k • rTr V (atTau θ V τ (κ k)) ψ := rfl
  rw [e1, Rder_smul, Rder_rTr hθ (isRealPt_atTau hθ τ (hU k)) hX, adAt_atTau_of_ne hθ hne (hU k)]
  rfl

theorem isGKMap_avgF (hθ : IsInfFam θ) (hne : τ' ≠ τ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (he : Continuous e) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ε : Fin V.rank → Bool} {σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} {T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ)} (hT : IsGKMap θ V τ' ε σ P T) :
    ∃ T' : kFin ε σ →ₗ[ℂ] (GA D V → ℂ), IsGKMap θ V τ' ε σ P T' ∧ ∀ v, T' v = avgF θ V μ τ κ e (T v) := by
  let T' : kFin ε σ →ₗ[ℂ] (GA D V → ℂ) :=
    { toFun := fun v => avgF θ V μ τ κ e (T v)
      map_add' := fun a b => by
        rw [map_add (f := _)]
        exact avgF_add μ hθ hκ hU he (hT.aut a).cont (hT.aut b).cont
      map_smul' := fun c a => by
        rw [map_smul]
        exact avgF_smul μ c (T a) }
  refine ⟨T', ⟨fun v => ?_, fun g hg hgK v w hw => ?_, fun X hX v w hd => ?_⟩, fun v => rfl⟩
  · exact GlobalTheory.RealAverage.isAutFunSm_average D θ hθ V τ K μ κ hκ hU e he _ (hT.aut v)
  · show avgF θ V μ τ κ e (T w) = rTr V (atTau θ V τ' g) (avgF θ V μ τ κ e (T v))
    rw [hT.mapK g hg hgK v w hw]
    funext x
    simp only [avgF, rTr]
    congr 1
    funext k
    rw [mul_assoc, mul_assoc, atTau_comm hθ hne (hU k) hg]
  · show avgF θ V μ τ κ e (T w) = Rder θ V τ' X (avgF θ V μ τ κ e (T v))
    rw [hT.mapLie X hX v w hd, avgF_Rder μ hθ hne hκ hU he (hT.aut v) hX]

end Avg

section Closure

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}

theorem hasTypeAt_avgF (hθ : IsInfFam θ) (hne : τ' ≠ τ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (he : Continuous e) {S : SPar} {φ : GA D V → ℂ}
    (hφc : Continuous φ) (h : HasTypeAt θ V τ' S φ) : HasTypeAt θ V τ' S (avgF θ V μ τ κ e φ) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : Continuous fun k => atTau θ V τ (κ k) := GlobalTheory.RealAverage.continuous_atTau hθ hκ hU
  let W' : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | Continuous f ∧ avgF θ V μ τ κ e f ∈ finPartOfType θ V τ' S}
      zero_mem' := ⟨continuous_const, by rw [avgF_zero]; exact zero_mem _⟩
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, by
        rw [avgF_add μ hθ hκ hU he ha.1 hb.1]; exact add_mem ha.2 hb.2⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, by
        rw [avgF_smul]; exact Submodule.smul_mem _ c ha.2⟩ }
  have hle : finPartOfType θ V τ' S ≤ W' := by
    refine sSup_le ?_
    rintro W ⟨H, _, _, σ, lam, ε, P, T, hE, hlam, hD, hP, hJ, hT, rfl⟩ f ⟨v, rfl⟩
    obtain ⟨T', hT', hv⟩ := isGKMap_avgF μ hθ hne hκ hU he hT
    refine ⟨(hT.aut v).cont, ?_⟩
    rw [← hv]
    exact (le_sSup (a := LinearMap.range T') ⟨H, _, _, σ, lam, ε, P, T', hE, hlam, hD, hP, hJ, hT', rfl⟩ :
      _ ≤ finPartOfType θ V τ' S) ⟨v, rfl⟩
  intro C hC δ hδ
  have hI0 : 0 ≤ ∫ k, ‖e k‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  set M : ℝ := (∫ k, ‖e k‖ ∂μ) + 1 with hMdef
  have hM : 0 < M := by linarith
  have hC' : IsCompact ((fun p : GA D V × K => p.1 * atTau θ V τ (κ p.2)) '' (C ×ˢ Set.univ)) :=
    (hC.prod isCompact_univ).image (continuous_fst.mul (hk.comp continuous_snd))
  obtain ⟨ψ, hψ, hap⟩ := h _ hC' (δ / M) (div_pos hδ hM)
  have hψ' := hle hψ
  refine ⟨_, hψ'.2, fun x hx => ?_⟩
  have i1 := GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hφc x
  have i2 := GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hψ'.1 x
  simp only [avgF]
  rw [← integral_sub i1 i2]
  have hb : ∀ k, ‖e k * φ (x * atTau θ V τ (κ k)) - e k * ψ (x * atTau θ V τ (κ k))‖ ≤ ‖e k‖ * (δ / M) :=
    fun k => by
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (hap _ ⟨(x, k), ⟨hx, Set.mem_univ _⟩, rfl⟩).le (norm_nonneg _)
  have hie : Integrable (fun k => ‖e k‖) μ :=
    he.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le (hie.mul_const _) (Filter.Eventually.of_forall hb)) ?_
  rw [integral_mul_const]
  have hlt : (∫ k, ‖e k‖ ∂μ) < M := by linarith
  calc (∫ k, ‖e k‖ ∂μ) * (δ / M) < M * (δ / M) := mul_lt_mul_of_pos_right hlt (div_pos hδ hM)
    _ = δ := mul_div_cancel₀ _ hM.ne'

end Closure

end GlobalTheory.AvgOtherPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchWeilOperatorUnitaryWLintegralNormEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchWeilOperatorUnitaryWLintegralNormEq
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
open MeasureTheory

namespace GlobalTheory.ArchimedeanLineL2

theorem archOp_lintegral_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    ∀ h ∈ UAt σ W (evI F), ∀ (N : ℕ) (C : (Fin n × Fin d → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin N))
      (f : SInf F (Fin n × Fin d)),
      ∫⁻ x, ‖archOp om h f (C.symm x)‖ₑ ^ 2 = ∫⁻ x, ‖f (C.symm x)‖ₑ ^ 2 := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW hex h hh N C f
  haveI := GlobalTheory.ArchimedeanUnitaryL2.opensMeasurable F (Fin n × Fin d)
  set μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Measure.map C.symm volume with hμ
  haveI : μ.IsAddHaarMeasure := C.symm.isAddHaarMeasure_map volume
  obtain ⟨g, hg, hg0⟩ : ∃ g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ,
      g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ g 0 ≠ 0 := by
    refine ⟨_, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _, ?_⟩
    have h0 : (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F (Fin n × Fin d) :=
      fun i _ v => zero_mem (v.adicCompletionIntegers F)
    rw [Set.indicator_of_mem h0]
    exact one_ne_zero
  obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := GlobalTheory.ArchimedeanUnitaryL2.exists_haar F _ μ g hg hg0
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => g fun i => (x i).2
  have hS : ∀ f' : SInf F (Fin n × Fin d), tens (evI F) (⇑f') r ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun f' => Submodule.subset_span ⟨f', g, hg, rfl⟩
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := by
    intro x z hz
    refine congrArg g (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchimedeanUnitaryL2.snd_eq_zero hz i, add_zero]
  have hU := (IsUWeilPair.isUSplitting hW).unit μA hμA (1, h) (tens (evI F) (⇑f) r) (hS f)
  have hAct : om (1, h) (tens (evI F) (⇑f) r) = tens (evI F) (⇑(archOp om h f)) r :=
    acts_archOp om h f (hex h hh f) r ⟨hr, hS f⟩
  rw [hAct] at hU
  have h1 := ((hc (archOp om h f)).symm.trans hU).trans (hc f)
  have h2 := (ENNReal.mul_right_inj hc0 hct).1 h1
  rw [hμ, lintegral_map ((archOp om h f).continuous.measurable.enorm.pow_const 2) C.symm.continuous.measurable,
    lintegral_map (f.continuous.measurable.enorm.pow_const 2) C.symm.continuous.measurable] at h2
  exact h2

end GlobalTheory.ArchimedeanLineL2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchWeilOperatorUnitaryWLintegralNormEqStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archWeilOperator_unitaryW_lintegral_norm_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    ∀ h ∈ UAt σ W (evI F), ∀ (N : ℕ) (C : (Fin n × Fin d → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin N))
      (f : SInf F (Fin n × Fin d)),
      ∫⁻ x, ‖archOp om h f (C.symm x)‖ₑ ^ 2 = ∫⁻ x, ‖f (C.symm x)‖ₑ ^ 2 := by
  first | exact @GlobalTheory.ArchimedeanLineL2.archOp_lintegral_eq | exact GlobalTheory.ArchimedeanLineL2.archOp_lintegral_eq | (intros; apply GlobalTheory.ArchimedeanLineL2.archOp_lintegral_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedDict

open scoped Matrix

theorem sum_form_orthoFrame {K : Type} [Field K] [StarRing K] {n : ℕ} (G B : Matrix (Fin n) (Fin n) K)
    (hB : Bᴴ * G * B = 1) (c d : Fin n → K) :
    ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = ∑ i, star (c i) * d i := by
  have h1 : ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = star (B *ᵥ c) ⬝ᵥ (G *ᵥ (B *ᵥ d)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
    Matrix.one_mulVec]
  rfl

theorem isSelfDualC_inV : ∀ {D : D7} (S : HSp D) (fr : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1 → ∀ Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), SD D Ls → ∃ Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), (Λ : Set (Fin S.rank → D.host.E)) = GlobalTheory.MovedDict.inV fr Ls ∧ IsSelfDualC S Λ := by
  intro D S fr hfr Ls hLs
  classical
  have hB : fr.1ᴴ * S.gram * fr.1 = 1 := hfr
  obtain ⟨hfg, hspan, hdual⟩ := hLs
  let f : (Fin S.rank → D.host.E) →ₗ[D.host.E] (Fin S.rank → D.host.E) := Matrix.toLin' fr.1
  have hinv : ∀ y, fr.1 *ᵥ ((fr⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinv' : ∀ y, (fr⁻¹).1 *ᵥ (fr.1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hmem : ∀ y, y ∈ Ls.map (f.restrictScalars (𝓞 D.host.E)) ↔ (fr⁻¹).1 *ᵥ y ∈ Ls := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [f, Matrix.toLin'_apply, hinv'] using hx
    · intro h
      exact ⟨_, h, by simp [f, Matrix.toLin'_apply, hinv]⟩
  have hform : ∀ x y : Fin S.rank → D.host.E, ∑ i, ∑ j, star (x i) * S.gram i j * y j =
      ∑ i, star (((fr⁻¹).1 *ᵥ x) i) * ((fr⁻¹).1 *ᵥ y) i := by
    intro x y
    have := sum_form_orthoFrame S.gram fr.1 hB ((fr⁻¹).1 *ᵥ x) ((fr⁻¹).1 *ᵥ y)
    rwa [hinv, hinv] at this
  refine ⟨Ls.map (f.restrictScalars (𝓞 D.host.E)), ?_, Submodule.IsLattice.of_fg D.host.E (hfg.map _), fun y => ?_⟩
  · ext x
    simp [inV, f, Matrix.toLin'_apply]
  · rw [hmem, hdual]
    constructor
    · intro h x hx
      rw [hmem] at hx
      obtain ⟨b, hb⟩ := h _ hx
      exact ⟨b, by rw [hform]; exact hb⟩
    · intro h x' hx'
      have hx : fr.1 *ᵥ x' ∈ Ls.map (f.restrictScalars (𝓞 D.host.E)) := by
        rw [hmem, hinv']; exact hx'
      obtain ⟨b, hb⟩ := h _ hx
      rw [hform, hinv'] at hb
      exact ⟨b, hb⟩

end GlobalTheory.MovedDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDual_image_orthonormalFrame_lattice : ∀ {D : D7} (S : HSp D) (fr : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1 → ∀ Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), SD D Ls → ∃ Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), (Λ : Set (Fin S.rank → D.host.E)) = GlobalTheory.MovedDict.inV fr Ls ∧ IsSelfDualC S Λ := by
  first | exact @GlobalTheory.MovedDict.isSelfDualC_inV | exact GlobalTheory.MovedDict.isSelfDualC_inV | (intros; apply GlobalTheory.MovedDict.isSelfDualC_inV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReduction
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameIdem

section General

variable {R : Type} [CommRing R] {n : ℕ}

theorem cut_mem (O : Subring R) {f f' : R} (hf : f ∈ O) (hf' : f' ∈ O) (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, f * A i j ∈ O) (h' : ∀ i j, f' * A i j ∈ O) (i j : Fin n) :
    ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j ∈ O := by
  have e : ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j =
      f * A i j + f' * A i j + (1 - (f + f')) * (1 : Matrix (Fin n) (Fin n) R) i j := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul]
  rw [e]
  refine O.add_mem (O.add_mem (h i j) (h' i j)) (O.mul_mem (O.sub_mem O.one_mem (O.add_mem hf hf')) ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

theorem exists_cut (O : Subring R) {f f' : R} (hf : f ∈ O) (hf' : f' ∈ O) (hff : f * f = f) (hff' : f' * f' = f')
    (h0 : f * f' = 0) (A B : Matrix (Fin n) (Fin n) R) (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i j, f * A i j ∈ O) (hA' : ∀ i j, f' * A i j ∈ O)
    (hB : ∀ i j, f * B i j ∈ O) (hB' : ∀ i j, f' * B i j ∈ O) :
    ∃ Y : GL (Fin n) O, Y.1.map O.subtype = (f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) ∧
      ∀ {k : Type} [CommRing k] (ρ : O →+* k), ρ ⟨f, hf⟩ = 1 →
        ∀ i j, ρ (Y.1 i j) = ρ ⟨f * A i j, hA i j⟩ := by
  have hφ : (f + f') * (f + f') = f + f' := by
    have h0' : f' * f = 0 := by rw [mul_comm, h0]
    simp only [add_mul, mul_add, hff, hff', h0, h0', add_zero, zero_add]
  let Ym : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, cut_mem O hf hf' A hA hA' i j⟩
  let Ym' : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, cut_mem O hf hf' B hB hB' i j⟩
  have hm : Ym.map O.subtype = (f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) := rfl
  have hm' : Ym'.map O.subtype = (f + f') • B + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) := rfl
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype) := by
    intro M N h
    ext i j
    exact congrFun (congrFun h i) j
  have e1 : Ym * Ym' = 1 := inj (by
    show (Ym * Ym').map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hm, hm', GlobalTheory.CompStab.idem_mul _ hφ A B hAB, Matrix.map_one _ (map_zero _) (map_one _)])
  have e2 : Ym' * Ym = 1 := inj (by
    show (Ym' * Ym).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hm, hm', GlobalTheory.CompStab.idem_mul _ hφ B A hBA, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨Ym, Ym', e1, e2⟩, hm, ?_⟩
  intro k _ ρ hρ i j
  have hz : ρ ⟨f', hf'⟩ = 0 := by
    have : (⟨f, hf⟩ : O) * ⟨f', hf'⟩ = 0 := Subtype.ext h0
    have h2 := congrArg ρ this
    rwa [map_mul, hρ, one_mul, map_zero] at h2
  have hz' : ρ ⟨f' * A i j, hA' i j⟩ = 0 := by
    have : (⟨f, hf⟩ : O) * ⟨f' * A i j, hA' i j⟩ = 0 :=
      Subtype.ext (show f * (f' * A i j) = 0 by rw [← mul_assoc, h0, zero_mul])
    have h2 := congrArg ρ this
    rwa [map_mul, hρ, one_mul, map_zero] at h2
  have hd : ρ ((1 : Matrix (Fin n) (Fin n) O) i j) * 0 = 0 := mul_zero _
  have split : Ym i j = ⟨f * A i j, hA i j⟩ + ⟨f' * A i j, hA' i j⟩ +
      (1 - (⟨f, hf⟩ + ⟨f', hf'⟩)) * (1 : Matrix (Fin n) (Fin n) O) i j := by
    apply Subtype.ext
    show ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j = _
    have : (((1 : Matrix (Fin n) (Fin n) O) i j : O) : R) = (1 : Matrix (Fin n) (Fin n) R) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Subring.coe_add, Subring.coe_mul,
      this]
    rfl
  show ρ (Ym i j) = _
  rw [split, map_add (f := _), map_add (f := _), map_mul, map_sub, map_add (f := _), hρ, hz, hz', map_one]
  simp

end General

theorem frGL_val {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (frGL β Y).1 = β.1 * Y.1.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 := rfl


set_option maxHeartbeats 400000 in
theorem cut_mem_St_red : ∀ {D : D7} (n : ℕ) (β γ y : GL (Fin n) (EAf D)) (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → IsIntM (toEAf D e • γ.1) → IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) → IsIntM (toEAf D (cA D e) • γ.1) → IsIntM (toEAf D (cA D e) • (γ⁻¹ : GL (Fin n) (EAf D)).1) → y.1 = β.1 * (toEAf D (e + cA D e) • γ.1 + (1 - toEAf D (e + cA D e)) • (1 : Matrix (Fin n) (Fin n) (EAf D))) * (β⁻¹ : GL (Fin n) (EAf D)).1 → y ∈ St β ∧ ∀ PP ∈ Z, ((redFn β PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) = redM PP (toEAf D e • γ.1) := by
  intro D n β γ y Z e he h1 h2 h3 h4 hy
  obtain ⟨hf, hres⟩ := GlobalTheory.InnerSteps.resS_idemSum he
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hfc : toEAf D e * toEAf D (cA D e) = 0 := by rw [← map_mul, he.2, map_zero]
  have hf' : toEAf D (cA D e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hcc]))
  obtain ⟨Y, hY, hred⟩ := exists_cut (Formalism.L2.Herm.intAf D.host.F D.host.E) hf hf'
    (by rw [← map_mul, hee]) (by rw [← map_mul, hcc]) hfc γ.1 (γ⁻¹ : GL (Fin n) (EAf D)).1
    γ.mul_inv γ.inv_mul h1 h3 h2 h4
  have hyY : y = frGL β Y := by
    have hs : toEAf D (e + cA D e) = toEAf D e + toEAf D (cA D e) := (toEAf D).map_add _ _
    refine Units.ext (hy.trans ?_)
    rw [frGL_val, hY, hs]
  subst hyY
  refine ⟨⟨Y, rfl⟩, fun PP hP => ?_⟩
  rw [redFn_frGL]
  ext i j
  have := hred (resS D.host.F PP) (hres PP hP) i j
  refine this.trans ?_
  unfold redM
  rw [dite_eq_left (h1 i j)]
  rfl

end GlobalTheory.FrameIdem

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction : ∀ {D : D7} (n : ℕ) (β γ y : GL (Fin n) (EAf D)) (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → IsIntM (toEAf D e • γ.1) → IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) → IsIntM (toEAf D (cA D e) • γ.1) → IsIntM (toEAf D (cA D e) • (γ⁻¹ : GL (Fin n) (EAf D)).1) → y.1 = β.1 * (toEAf D (e + cA D e) • γ.1 + (1 - toEAf D (e + cA D e)) • (1 : Matrix (Fin n) (Fin n) (EAf D))) * (β⁻¹ : GL (Fin n) (EAf D)).1 → y ∈ St β ∧ ∀ PP ∈ Z, ((redFn β PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) = redM PP (toEAf D e • γ.1) := by
  first | exact @GlobalTheory.FrameIdem.cut_mem_St_red | exact GlobalTheory.FrameIdem.cut_mem_St_red | (intros; apply GlobalTheory.FrameIdem.cut_mem_St_red <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartz
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree

theorem isDatum_add : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} [AddCommGroup Z]
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ),
    IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + Φ') (f + f') := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z _ crd Φ Φ' f f' h h'
  refine ⟨add_mem h.1 h'.1, fun u => ?_⟩
  have e : M.co.rho ψ u (Φ + Φ') = M.co.rho ψ u Φ + M.co.rho ψ u Φ' := by
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]
    ring
  rw [e, GlobalTheory.WeilM.thetaSum_add F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u Φ h.1)
    (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u Φ' h'.1), h.2 u, h'.2 u]
  rfl

end GlobalTheory.SquareAgree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartzStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} [AddCommGroup Z]
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ),
    IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + Φ') (f + f') := by
  first | exact @GlobalTheory.SquareAgree.isDatum_add | exact GlobalTheory.SquareAgree.isDatum_add | (intros; apply GlobalTheory.SquareAgree.isDatum_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridCommonDataPropertiesHold
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridCommonDataPropertiesHold
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto

theorem comOK : ComOK := by
  intro D _ _ T L μ0 _ sc _ G W M _
  have hchi : ∀ k, k < D.R.m → ChrEq (G.ch.chi (D.R.m - k)) (G.ch.chiH (D.R.m - k)) :=
    fun k hk => G.ch.chi_eq _ (by omega) (by omega)
  refine ⟨W.θ_is, W.ψ_std, fun k (hk : k < D.R.m) => ?_, fun k (hk : k < D.R.m) τ => ?_, fun k (hk : k < D.R.m) => ?_,
    fun i k hik (hk : k < D.R.m) τ => ?_, ?_, ?_⟩
  · show IsHeckeChar D (G.ch.chi (D.R.m - k))⁻¹ ∧ Formalism.L2.Theta.ResEta D (G.ch.chi (D.R.m - k))⁻¹ 0
    have hw := W.om_is (.core k) (show k + 1 ≤ D.R.m by omega)
    have e := (G.chr_core (i := k) (by omega)).1
    have hr : (G.pS (.core k)).rank = rankP D (k + 1) := (G.sp.P_is _ (by omega)).rank
    have h1 := hw.hecS
    have h2 := hw.resS
    rw [e] at h1 h2
    rw [hr] at h2
    obtain ⟨a, ha⟩ := even_rankP D (k + 1)
    exact GlobalTheory.StdUnn.isHeckeChar_resEta_inv D _ 0 h1 (Formalism.L2.Theta.resEta_parity h2 (by omega))
  · show HasInfExp D (G.ch.chi (D.R.m - k))⁻¹ τ (-(cen D sc.cGap τ (D.R.m - k) : ℚ))
    have h := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - k) : ℚ)) (hchi k hk)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - k), fun τ => by push_cast; ring, G.ch.inf _ (by omega) (by omega)⟩ τ
    exact GlobalTheory.Chain.StepVac.hasInfExp_inv h
  · show GlobalTheory.LFun.UnrOff (G.ch.chi (D.R.m - k))⁻¹ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F)))
    intro w hw
    have hu : GlobalTheory.LFun.UnrAt (G.ch.chi (D.R.m - k)) w :=
      (GlobalTheory.LFun.unrAt_iff_of_chrEq (hchi k hk) w).2 (G.ch.unr _ (by omega) (by omega) w hw)
    intro x hx
    have := hu x hx
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv] at this ⊢
    rw [this, inv_one]
  · show -(cen D sc.cGap τ (D.R.m - i) : ℚ) ≠ -(cen D sc.cGap τ (D.R.m - k) : ℚ)
    intro h
    have hg : 0 < gap D sc.cGap := lt_of_le_of_lt (Nat.zero_le _) (sLen_lt_gap D sc.cGap)
    set g := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D sc.cGap) 0 with hgdef
    have hc : ∀ j, cen D sc.cGap τ j = ⌊g.mid j⌋ := fun j => rfl
    have hga : (g.ga : ℚ) = (gap D sc.cGap : ℚ) := rfl
    have e1 : ((D.R.m - i : ℕ) : ℚ) = ((D.R.m - k : ℕ) : ℚ) + ((k - i : ℕ) : ℚ) := by
      rw [← Nat.cast_add]; congr 1; omega
    have hmid : g.mid (D.R.m - k) = g.mid (D.R.m - i) + (((k - i) * gap D sc.cGap : ℕ) : ℤ) := by
      rw [g.mid_eq (by omega), g.mid_eq (by omega)]
      have := g.a_sub_a (D.R.m - k) (D.R.m - i)
      rw [e1, hga] at this
      push_cast
      linarith
    have hf : cen D sc.cGap τ (D.R.m - k) = cen D sc.cGap τ (D.R.m - i) + (((k - i) * gap D sc.cGap : ℕ) : ℤ) := by
      rw [hc, hc, hmid, Int.floor_add_intCast]
    have h' : cen D sc.cGap τ (D.R.m - i) = cen D sc.cGap τ (D.R.m - k) := by exact_mod_cast neg_inj.1 h
    have hpos : 0 < (k - i) * gap D sc.cGap := Nat.mul_pos (by omega) hg
    omega
  · show 1 ≤ D.R.r + 1
    omega
  · show D.R.r + 1 + 2 ≤ D.R.r + 6 - 1
    omega

end GlobalTheory.CoreOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridCommonDataPropertiesHoldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testGridCommonData_properties_hold : ComOK := by
  first | exact @GlobalTheory.CoreOnto.comOK | exact GlobalTheory.CoreOnto.comOK | (intros; apply GlobalTheory.CoreOnto.comOK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch.FourierInv

open ValuativeRel

theorem card_res_pow (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (e : ℕ) : Fintype.card (Res k e) = resCard k ^ e := by
  rw [← Nat.card_eq_fintype_card]
  have hne : IsLocalRing.maximalIdeal 𝒪[k] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) hne (i := e)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  exact hq

theorem fourierSum_invFourierSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (n : ℕ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Ξ : Matrix A C k → ℂ, HasDepth ϖ n (blockLat ϖ n P) Ξ → fourierSum ψ ϖ n P (invFourierSum ψ ϖ n P Ξ) = Ξ := by
  intro k _ _ _ _ A _ _ C _ _ ψ ϖ n P hϖ hψ Ξ hΞ
  funext Y
  rw [fourierSum_apply]
  split_ifs with hY
  · let r : A → P → 𝒪[k] := fun i j => ⟨((ϖ ^ n : kˣ) : k) * Y i j, hY i j j.2⟩
    let S₀ : A → P → Res k n := fun i j => Ideal.Quotient.mk _ (r i j)
    set M : Matrix A P k := (ϖ ^ n)⁻¹ • liftRes S₀ with hM
    have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
    have hdiff : ∀ i (j : P), Y i j - M i j ∈ 𝒪[k] := fun i j => by
      have h1 : ((Quotient.out (S₀ i j) : 𝒪[k]) - r i j) ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n :=
        Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
      rw [GlobalTheory.SplitFlip.Model.val_le_iff_mem hϖ] at h1
      have e1 : Y i j - M i j = -((((ϖ ^ n)⁻¹ : kˣ) : k) * (((Quotient.out (S₀ i j) : 𝒪[k]) - r i j : 𝒪[k]) : k)) := by
        simp only [hM, Matrix.smul_apply, Units.smul_def, smul_eq_mul, liftRes, Matrix.of_apply, r]
        push_cast
        rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]
        ring
      rw [e1, Valuation.mem_integer_iff, Valuation.map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_mul_le_one_of_le₀ h1 h0.le
    have triv : ∀ y : k, y ∈ 𝒪[k] → ψ y = 1 := fun y hy =>
      (hψ 1).2 le_rfl y (by simpa using (Valuation.mem_integer_iff _ _).1 hy)
    have hpair : ∀ T : A → P → Res k n,
        ψ (pairCols P Y (liftRes T)) = ψ (pairCols P (setCols P Y M) (liftRes T)) := fun T => by
      have e2 : pairCols P Y (liftRes T) = pairCols P (setCols P Y M) (liftRes T) +
          ∑ i, ∑ j : P, liftRes T i j * (Y i j - M i j) := by
        simp only [pairCols, setCols, Matrix.of_apply, Finset.coe_mem, dif_pos, Subtype.coe_eta,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e2, AddChar.map_add_eq_mul, triv _ (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        mul_mem (liftRes_mem T i j) (hdiff i j)), mul_one]
    have hinv : Ξ (setCols P Y M) = Ξ Y := by
      have e3 : setCols P Y M = Y + Matrix.of fun i j => if h : j ∈ P then M i ⟨j, h⟩ - Y i j else 0 := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      rw [e3]
      refine hΞ.2 Y _ (GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩)
      · simp only [Matrix.of_apply, dif_pos hj]
        have := neg_mem (hdiff i ⟨j, hj⟩)
        simpa using this
      · simp [hj]
    simp_rw [hpair]
    rw [GlobalTheory.SplitFlip.Model.sum_invFourierSum hϖ hψ n P Ξ Y S₀]
    have hq : (resCard k : ℂ) ≠ 0 := by
      show ((Nat.card 𝓀[k] : ℕ) : ℂ) ≠ 0
      exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])).ne'
    have hc : ((resCard k : ℂ) ^ (n * Fintype.card A * P.card))⁻¹ *
        ((resCard k : ℂ) ^ n) ^ (Fintype.card A * P.card) = 1 := by
      rw [← pow_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq)]
    rw [← hM, hinv, card_res_pow, Nat.cast_pow, ← mul_assoc, hc, one_mul]
  · symm
    refine hΞ.1 Y fun h => hY ?_
    exact (GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat.1 h).1

end GlobalTheory.FlipMatch.FourierInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourierSum_inverse_of_latticeDepth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (n : ℕ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Ξ : Matrix A C k → ℂ, HasDepth ϖ n (blockLat ϖ n P) Ξ → fourierSum ψ ϖ n P (invFourierSum ψ ϖ n P Ξ) = Ξ := by
  first | exact @GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum | exact GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum | (intros; apply GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

namespace GlobalTheory.ConjSplitIdem

theorem isIdemAt_cA_of_ne : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)), w ≠ w' → w.under (𝓞 D.host.F) = v → w'.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → Formalism.L2.NTheta.IsIdemAt (cA D ε) w' := by
  intro D v w w' hne hw hw' ε hε
  rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (P := w) (Q := w') (by rw [hw, hw']) with h | h
  · exact absurd h.symm hne
  · subst h
    exact GlobalTheory.MovedIdem.isIdemAt_conj hε (fun x => Iff.rfl)

end GlobalTheory.ConjSplitIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIdemAt_conj_of_other_prime_over_split : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)), w ≠ w' → w.under (𝓞 D.host.F) = v → w'.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → Formalism.L2.NTheta.IsIdemAt (cA D ε) w' := by
  first | exact @GlobalTheory.ConjSplitIdem.isIdemAt_cA_of_ne | exact GlobalTheory.ConjSplitIdem.isIdemAt_cA_of_ne | (intros; apply GlobalTheory.ConjSplitIdem.isIdemAt_cA_of_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.HaarNorm

theorem measLevW_unique {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hg : ∀ ρ m, good ρ m → m.IsHaarMeasure) {μ μ' : Measure (GA D V)}
    (h : Formalism.IndefR.Lev.IsMeasLevW V K good μ) (h' : Formalism.IndefR.Lev.IsMeasLevW V K good μ') : μ = μ' := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hμ, ⟨θ, hθ⟩, hθall⟩ := h
  obtain ⟨⟨A, hA⟩, hAall⟩ := hθall θ hθ
  obtain ⟨⟨m, hm⟩, hmall⟩ := hAall A hA
  have e := hmall m hm
  have e' := ((h'.2.2 θ hθ).2 A hA).2 m hm
  have hμ' := h'.1
  have hB : ∀ ρ : D.what₂.Tau, ∃ B : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2),
      MeasurableSet B ∧ m ρ B ≠ 0 ∧ m ρ B ≠ ⊤ := by
    intro ρ
    obtain ⟨j1, j2, j3, -, j5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2
    haveI := hg ρ (m ρ) (hm ρ)
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)
    exact ⟨C, hC.measurableSet, (by first | exact (Measure.measure_pos_of_mem_nhds (m ρ) hC1).ne' | exact (measure_pos_of_nonempty_interior (m ρ) ⟨1, mem_interior_iff_mem_nhds.2 hC1⟩).ne'), hC.measure_lt_top.ne⟩
  choose B hBm hB0 hBt using hB
  set S := {h : GA D V | Lev.finE V h ∈ K ∧
      ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hS : μ S = ∏ ρ, m ρ (B ρ) := e B hBm
  have hS' : μ' S = ∏ ρ, m ρ (B ρ) := e' B hBm
  have hp0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hB0 ρ
  have hpt : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => hBt ρ
  have hc := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hcS : μ' S = (Measure.haarScalarFactor μ' μ : ENNReal) * μ S := by
    conv_lhs => rw [hc]
    rfl
  rw [hS, hS'] at hcS
  have hc1 : (Measure.haarScalarFactor μ' μ : ENNReal) = 1 := by
    have := (ENNReal.mul_left_inj hp0 hpt).1 (hcS.symm.trans (one_mul _).symm)
    exact this
  rw [hc, ENNReal.coe_eq_one.1 hc1, one_smul]

theorem vol_nu_eq_of_isAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := by
  intro D T L sc G M M' X K h h'
  unfold GlobalTheory.FunObj.Vol.IsAt at h h'
  split_ifs at h h'
  · exact measLevW_unique _ _ _ (fun _ _ hm => hm.1) h.1 h'.1
  · exact measLevW_unique _ _ _ (fun _ _ hm => hm.1) h.1 h'.1

end GlobalTheory.HaarNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridVertexMeasure_eq_of_same_normalisation : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := by
  first | exact @GlobalTheory.HaarNorm.vol_nu_eq_of_isAt | exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt | (intros; apply GlobalTheory.HaarNorm.vol_nu_eq_of_isAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalFunctionBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpArrowApprox

theorem ptF_eq_fock {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (p : GlobalTheory.Grid.Pol S T) :
    GlobalTheory.ChainFr.ptF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f p =
      GlobalTheory.Grid.fock ψ θ true S T f p := by
  have : (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS true S :=
    funext fun τ => GlobalTheory.PairLift.cart_frSgn true _ τ
  unfold GlobalTheory.ChainFr.ptF GlobalTheory.Grid.fock
  rw [this]
  rfl

theorem isFinVec_of_isVacF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D}
    {f : WO S.V T.V → ℂ}
    (h : GlobalTheory.ChainFr.IsVacF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f) :
    GlobalTheory.Grid.IsFinVec ψ θ true S T f :=
  ⟨h.1, fun τ => by have := h.2 τ; rwa [GlobalTheory.PairLift.cart_frSgn] at this⟩

end GlobalTheory.UpArrowApprox

namespace GlobalTheory.UpArrowApprox

end GlobalTheory.UpArrowApprox
end
