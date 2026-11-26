module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.BridgeA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.LevelRaise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem exists_enum (o : Obj D l b s) {M : ℕ} (hM : 0 < M) :
    ∃ (J : Type) (_ : Finite J), ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
      ∃ u : J → (Over.mk x ⟶ o.t.G), Function.Injective u ∧ ∀ w, w ^ M = 1 ↔ ∃ j, u j = w := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient D M hM
  refine ⟨J, inferInstance, fun K _ _ x => ?_⟩
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨-, I, -⟩ := o.geom K x β.hom hβ.symm
  have hI : ∀ a b, I.ev M a = I.ev M b ↔ π a = π b := fun a b => by
    have h : I.ev M a = I.ev M (a - b) * I.ev M b := by rw [← I.add, sub_add_cancel]
    rw [hπ, h, mul_eq_right, I.ker M hM]
    rfl
  refine ⟨fun j => I.ev M (r j), fun i j hij => ?_, fun w => (I.onto M hM w).trans ⟨?_, ?_⟩⟩
  · have := (hI _ _).1 hij
    rwa [hr, hr] at this
  · rintro ⟨a, rfl⟩
    exact ⟨π a, (hI _ _).2 (hr _)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, rfl⟩

theorem exists_finite_set (o : Obj D l b s) {M : ℕ} (hM : 0 < M) {K F : Type} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed F] (x : Sp K ⟶ S) :
    ∃ T : Set F, T.Finite ∧ ∀ L : IntermediateField K F, T ⊆ L →
      ∀ w : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ o.t.G, w ^ M = 1 →
        ∃ q : Over.mk (spMap (algebraMap K L) ≫ x) ⟶ o.t.G, spMap (algebraMap L F) ≫ q.left = w.left := by
  haveI := o.proper
  obtain ⟨J, _, hJ⟩ := exists_enum o hM
  obtain ⟨u, -, hu⟩ := hJ F (spMap (algebraMap K F) ≫ x)
  choose T hT using fun j => TorsionRat.exists_finset_over o.t.G x (u j)
  refine ⟨⋃ j, (T j : Set F), Set.finite_iUnion fun j => (T j).finite_toSet, fun L hL w hw => ?_⟩
  obtain ⟨j, rfl⟩ := (hu w).1 hw
  exact hT j L ((Set.subset_iUnion (fun j => (T j : Set F)) j).trans hL)

end GlobalTheory.LevelRaise
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeisenbergOperatorBoundedThetaFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeisenbergOperatorBoundedThetaFunction
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem exists_compact_cover (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (nS nT : ℕ) : ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  refine ⟨Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

theorem continuous_rhoBF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) : ∀ f : BBF σ JS JT ξ₀ ψ, Continuous fun w => rhoBF σ JS JT ξ₀ ψ hψ w f := by
  intro f
  obtain ⟨K, hK, hc⟩ := exists_compact_cover F E nS nT
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let G : C(WOF F E nS nT × K, ℂ) := ⟨fun p => heisOF σ JS JT ξ₀ ψ p.1 f.1 p.2,
    (hψ.1.comp (continuous_symplOHF σ JS JT ξ₀ (continuous_subtype_val.comp continuous_snd) continuous_fst)).mul
      (f.1.continuous.comp ((continuous_subtype_val.comp continuous_snd).add continuous_fst))⟩
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (G.curry.continuous.tendsto w₀)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun w => ?_) h1)
  refine norm_QB_le _ (norm_nonneg _) fun x => ?_
  obtain ⟨γ, hγ, h⟩ := hc x
  rw [← BBF_norm_periodic hψ _ γ hγ]
  exact (G.curry w - G.curry w₀).norm_coe_le_norm ⟨γ + x, h⟩

end GlobalTheory.RealWeilF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeisenbergOperatorBoundedThetaFunctionStatement
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ), ∀ f : BBF σ JS JT ξ₀ ψ, Continuous fun w => rhoBF σ JS JT ξ₀ ψ hψ w f := by
  first | exact @GlobalTheory.RealWeilF.continuous_rhoBF | exact GlobalTheory.RealWeilF.continuous_rhoBF | (intros; apply GlobalTheory.RealWeilF.continuous_rhoBF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetLeOfWeightedEntryBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetLeOfWeightedEntryBound
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem norm_det_le_of_weighted {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Equiv.Perm (Fin n))
    (w : Fin n → ℝ) (c : ℝ) (hw : ∀ a, 0 < w a)
    (h : ∀ i b, ‖M i b‖ * (w (u i) * w b) ≤ c) :
    ‖M.det‖ ≤ (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  have hM : ∀ i b, ‖M i b‖ ≤ |c| * ((w (u i))⁻¹ * (w b)⁻¹) := by
    intro i b
    have hp : 0 < w (u i) * w b := mul_pos (hw _) (hw _)
    rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ hp]
    exact (h i b).trans (le_abs_self c)
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ ≤ |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
    intro σ
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
    rw [norm_mul, hs, one_mul, norm_prod]
    calc ∏ i, ‖M (σ i) i‖ ≤ ∏ i, |c| * ((w (u (σ i)))⁻¹ * (w i)⁻¹) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hM _ _)
      _ = |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
          have e : ∏ i, (w (u (σ i)))⁻¹ = ∏ a, (w a)⁻¹ :=
            Equiv.prod_comp (σ.trans u) (fun a => (w a)⁻¹)
          rw [e, ← Finset.prod_mul_distrib]
          simp only [sq]
  rw [Matrix.det_apply']
  calc _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetLeOfWeightedEntryBoundStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_det_le_of_weighted_entry_bound : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i b, ‖M i b‖ * (w (u i) * w b) ≤ c) → ‖M.det‖ ≤ (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  first | exact @GlobalTheory.GoodTop.norm_det_le_of_weighted | exact GlobalTheory.GoodTop.norm_det_le_of_weighted | (intros; apply GlobalTheory.GoodTop.norm_det_le_of_weighted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonal
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section
namespace GlobalTheory.WeilDatumF

theorem fst_symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h : y.map (infPartF F E) = 0 ∨ z.map (infPartF F E) = 0) : fstA F (symplOF σ JS JT ξ₀ y z) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.OrientedHeis.map_trace_hO_zero (fstA F) σ (incAF F E ξ₀) (fun a b => incAF F E (JS⁻¹ a b))
    (fun c d => incAF F E (JT c d)) y z h

theorem snd_symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h : y.map (finPartF F E) = 0 ∨ z.map (finPartF F E) = 0) : sndA F (symplOF σ JS JT ξ₀ y z) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.OrientedHeis.map_trace_hO_zero (sndA F) σ (incAF F E ξ₀) (fun a b => incAF F E (JS⁻¹ a b))
    (fun c d => incAF F E (JT c d)) y z h

theorem symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h1 : y.map (infPartF F E) = 0 ∨ z.map (infPartF F E) = 0)
    (h2 : y.map (finPartF F E) = 0 ∨ z.map (finPartF F E) = 0) : symplOF σ JS JT ξ₀ y z = 0 :=
  Prod.ext (fst_symplOF_eq_zero σ JS JT ξ₀ y z h1) (snd_symplOF_eq_zero σ JS JT ξ₀ y z h2)

theorem symplOHF_fin_real_orth (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u x : WOF F E nS nT) :
      u.map (infPartF F E) = 0 → x.map (finPartF F E) = 0 → symplOHF σ JS JT ξ₀ u x = 0 ∧ symplOHF σ JS JT ξ₀ x u = 0 := by
  intro hu hx
  have e1 := symplOF_eq_zero σ JS JT ξ₀ u x (Or.inl hu) (Or.inr hx)
  have e2 := symplOF_eq_zero σ JS JT ξ₀ x u (Or.inr hu) (Or.inl hx)
  unfold symplOHF
  rw [e1, e2, mul_zero]
  exact ⟨rfl, rfl⟩

end GlobalTheory.WeilDatumF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonalStatement
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u x : WOF F E nS nT),
      u.map (infPartF F E) = 0 → x.map (finPartF F E) = 0 → symplOHF σ JS JT ξ₀ u x = 0 ∧ symplOHF σ JS JT ξ₀ x u = 0 := by
  first | exact @GlobalTheory.WeilDatumF.symplOHF_fin_real_orth | exact GlobalTheory.WeilDatumF.symplOHF_fin_real_orth | (intros; apply GlobalTheory.WeilDatumF.symplOHF_fin_real_orth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardMeasureUnitaryPQEqVolumeSmulCompactDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardMeasureUnitaryPQEqVolumeSmulCompactDual
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.CompactDualScale

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ENNReal} (a : ENNReal) (ha : a ≠ ⊤)
    (h : OmegaDensity μ c) : OmegaDensity (a • μ) (a * c) := by
  obtain ⟨lam, hlam, hl⟩ := h
  refine ⟨lam, hlam, ?_⟩
  refine (ENNReal.Tendsto.const_mul hl (Or.inr ha)).congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ENNReal}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c = c' := by
  obtain ⟨lam, hlam, hl⟩ := h
  obtain ⟨lam', hlam', hl'⟩ := h'
  rw [Formalism.IndefR.Eqv.MU.omegaLeb_unique hlam hlam'] at hl'
  exact tendsto_nhds_unique hl hl'

theorem isMinf_eq_volU_smul_cd : ∀ (cd : CDHaar) (p q : ℕ) (m : Measure (UpqT p q)), Lev.IsMinf m →
    m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q := by
  intro cd p q m hm
  obtain ⟨c, hc0, hctop, hpq, hN⟩ := cd.trick p q
  haveI := cd.haar (p + q) 0
  haveI := cd.prob (p + q)
  haveI := cd.haar p q
  have hmain := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.omegaDensity_main (N := p + q) (cd.cd (p + q) 0)
  have hc := omegaDensity_unique hN hmain
  have hV : 0 < ReciprocityTheory.ChartRestriction.DS.volU (p + q) := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.volU_pos (p + q)
  have hκ : (0 : ℝ) < 2 ^ ((p + q) * (p + q - 1) / 2) := by positivity
  have hmul : ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) * c = Formalism.L2.Theta.minfDensity (p + q) := by
    rw [hc, ← ENNReal.ofReal_mul hV.le, Formalism.L2.Theta.minfDensity]
    have e : ReciprocityTheory.ChartRestriction.DS.volU (p + q) * (1 / (2 ^ ((p + q) * (p + q - 1) / 2) * ReciprocityTheory.ChartRestriction.DS.volU (p + q)))
        = ((2 : ℝ) ^ ((p + q) * (p + q - 1) / 2))⁻¹ := by
      field_simp
    rw [e, ENNReal.ofReal_inv_of_pos hκ, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hV0 : ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) ≠ 0 := (ENNReal.ofReal_pos.2 hV).ne'
  have hm' : Lev.IsMinf (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q) := by
    refine ⟨Measure.IsHaarMeasure.smul _ hV0 ENNReal.ofReal_ne_top, ?_⟩
    rw [← hmul]
    exact omegaDensity_smul _ ENNReal.ofReal_ne_top hpq
  exact Formalism.IndefR.Eqv.MU.isMinf_unique hm' hm

end GlobalTheory.LowRow.CompactDualScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardMeasureUnitaryPQEqVolumeSmulCompactDualStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardMeasure_unitaryPQ_eq_volume_smul_compactDual : ∀ (cd : CDHaar) (p q : ℕ) (m : Measure (UpqT p q)), Lev.IsMinf m → m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q := by
  first | exact @GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd | exact GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd | (intros; apply GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCompletionLatticeEqColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCompletionLatticeEqColumns
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLat

theorem exists_GLw_lat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ L : Submodule K.O B.A, GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ g : GLw m w, GlobalTheory.TwLat.lat e b g = L := by
  intro E _ _ _ _ w _ K e _ _ _ B m b L hL
  obtain ⟨hfg, hsp⟩ := hL
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors K.O B.A := by
    constructor
    intro c x h
    rw [← algebraMap_smul K.E c x, smul_eq_zero] at h
    rcases h with h | h
    · left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)
    · right; exact h
  haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'
  set n := Module.finrank K.O L
  let bL := Module.finBasis K.O L
  let v : Fin n → B.A := fun i => (bL i : B.A)
  have hspanO : Submodule.span K.O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range bL := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bL.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent K.E v := by
    rw [← LinearIndependent.iff_fractionRing K.O K.E]
    exact LinearIndependent.map' bL.linearIndependent L.subtype (by simp)
  have hspE : ⊤ ≤ Submodule.span K.E (Set.range v) := by
    rw [← Submodule.span_span_of_tower K.O K.E (Set.range v), hspanO, hsp]
  let bE := Module.Basis.mk hli hspE
  have hnm : n = m := by
    have h1 := Module.finrank_eq_card_basis bE
    have h2 := Module.finrank_eq_card_basis b
    simp only [Fintype.card_fin] at h1 h2
    omega
  let v' : Fin m → B.A := v ∘ finCongr hnm.symm
  let bE' := bE.reindex (finCongr hnm)
  have hv' : ∀ j, bE' j = v' j := by
    intro j; simp [bE', v', bE, Module.Basis.mk_apply]
  let M : Matrix (Fin m) (Fin m) K.E := b.toMatrix bE'
  have hM : IsUnit M := by
    haveI := b.invertibleToMatrix bE'
    exact isUnit_of_invertible M
  have hMe : IsUnit (M.map e) := hM.map e.mapMatrix
  refine ⟨hMe.unit, ?_⟩
  unfold lat
  rw [← hspanO]
  have hcol : (fun j => ∑ i, e.symm ((hMe.unit : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) • b i) = v' := by
    funext j
    simp only [IsUnit.unit_spec, Matrix.map_apply, RingEquiv.symm_apply_apply, M, Module.Basis.toMatrix_apply]
    rw [b.sum_repr, hv']
  rw [hcol]
  congr 1
  exact EquivLike.range_comp v _

end GlobalTheory.TwLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCompletionLatticeEqColumnsStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_completion_lattice_eq_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ L : Submodule K.O B.A, GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ g : GLw m w, GlobalTheory.TwLat.lat e b g = L := by
  first | exact @GlobalTheory.TwLat.exists_GLw_lat_eq | exact GlobalTheory.TwLat.exists_GLw_lat_eq | (intros; apply GlobalTheory.TwLat.exists_GLw_lat_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PBConjTranspose
noncomputable section

open Formalism.REAL (UJ KG toM inG Jm)
open GlobalTheory.PsCo.Pc1
open scoped Matrix

namespace GlobalTheory.PsCo.Pc3

variable {n : ℕ}

theorem pB_conjTranspose (ε : Fin n → Bool) (B : Mode ε → ℂ) : (pB ε B)ᴴ = pB ε B := by
  ext a b
  simp only [Matrix.conjTranspose_apply]
  cases ha : ε a <;> cases hb : ε b <;> simp [pB, ha, hb]

theorem pB_ne (ε : Fin n → Bool) (B : Mode ε → ℂ) (a b : Fin n) (h : ε a = ε b) : pB ε B a b = 0 := by
  simp only [pB]
  rw [dite_eq_right (by rintro ⟨h1, h2⟩; rw [h, h2] at h1; simp at h1),
    dite_eq_right (by rintro ⟨h1, h2⟩; rw [← h, h2] at h1; simp at h1)]

theorem pB_inG (ε : Fin n → Bool) (B : Mode ε → ℂ) : inG ε (pB ε B) := by
  unfold inG
  rw [pB_conjTranspose]
  ext a b
  simp only [Matrix.add_apply, Matrix.zero_apply, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ε a = ε b
  · rw [pB_ne ε B a b h]; simp
  · cases ha : ε a <;> cases hb : ε b <;> simp_all

theorem continuous_pB (ε : Fin n → Bool) : Continuous (pB ε) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [pB]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).star
  · exact continuous_const

theorem pB_zero (ε : Fin n → Bool) : pB ε 0 = 0 := by
  ext a b; simp only [pB]; split_ifs <;> simp

theorem toM_eB (ε : Fin n → Bool) (B : Mode ε → ℂ) : toM (eB ε B) = NormedSpace.exp (pB ε B) := by
  rw [eB, Formalism.REAL.toM_expG ε _ 1 (pB_inG ε B)]; simp

theorem toM_inv (ε : Fin n → Bool) (g : UJ ε) : toM g⁻¹ = (toM g)⁻¹ := by
  show (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
  rw [Matrix.coe_units_inv]

theorem stEB : StEB := by
  intro n ε
  refine ⟨?_, ?_, fun B => ⟨toM_eB ε B, ?_⟩⟩
  · rw [(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.continuous_iff]
    change Continuous fun B => toM (eB ε B)
    simp_rw [toM_eB]
    have hc : Continuous (NormedSpace.exp : Mat n → Mat n) := by
      letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
      letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℚ) (α := ℂ)
      exact @NormedSpace.exp_continuous (Matrix (Fin n) (Fin n) ℂ) _ _
        (inferInstanceAs (CompleteSpace (Fin n → Fin n → ℂ)))
    exact hc.comp (continuous_pB ε)
  · apply Subtype.ext; apply Units.ext
    change toM (eB ε 0) = 1
    rw [toM_eB, pB_zero, NormedSpace.exp_zero]
  · rw [toM_inv, toM_eB]
    rw [Matrix.exp_neg]

end GlobalTheory.PsCo.Pc3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGeometricFibre
noncomputable section

namespace GlobalTheory.UPel.GeometricLevelExistence

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem epi_spMap_field {K L : Type} [Field K] [Field L] (σ : K →+* L) : Epi (spMap σ) := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem unitOn_pull_spMap {K Ω : Type} [CommRing K] [CommRing Ω] (i : K →+* Ω) (c : Kˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map i.toMonoidHom c) := by
  apply Units.ext
  exact (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm

theorem eq_iff_of_add {La G : Type} [AddGroup La] [Group G] (P : La → G)
    (hP : ∀ a b, P (a + b) = P a * P b) (a b : La) : P a = P b ↔ P (-a + b) = 1 := by
  have h := hP a (-a + b)
  rw [add_neg_cancel_left] at h
  rw [h]
  constructor
  · intro e
    exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)
  · intro e
    rw [e, _root_.mul_one]

theorem exists_eq_of_count {La G : Type} [AddCommGroup La] [Module.Finite ℤ La] [Group G] (n : ℕ) (hn : 0 < n)
    (P Q : La → G) (hPa : ∀ a b, P (a + b) = P a * P b) (hQa : ∀ a b, Q (a + b) = Q a * Q b)
    (hP : ∀ a, P a = 1 ↔ ∃ b, a = n • b) (hQ : ∀ a, Q a = 1 ↔ ∃ b, a = n • b)
    (hPQ : ∀ a, ∃ c, P a = Q c) (c : La) : ∃ a, P a = Q c := by
  let m : La →+ La := AddMonoidHom.mk' (fun a : La => n • a) (fun a b => smul_add n a b)
  let K : AddSubgroup La := m.range
  have hK : ∀ a, a ∈ K ↔ ∃ b, a = n • b := fun a => by
    simp only [K, AddMonoidHom.mem_range]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have : AddGroup.FG La := Module.Finite.iff_addGroup_fg.1 inferInstance
  have : Finite (La ⧸ K) := AddCommGroup.finite_of_fg_torsion _ fun q => by
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hK]
      exact ⟨a, rfl⟩
  have hmk : ∀ (R : La → G), (∀ a b, R (a + b) = R a * R b) → (∀ a, R a = 1 ↔ ∃ b, a = n • b) →
      ∀ a b, R a = R b ↔ (a : La ⧸ K) = b := fun R hRa hR a b => by
    rw [eq_iff_of_add R hRa, QuotientAddGroup.eq, hK, hR]
  choose f hf using hPQ
  let g : La ⧸ K → La ⧸ K := fun q => (f q.out : La ⧸ K)
  have hg : Function.Injective g := fun q q' e => by
    have e' := (hmk Q hQa hQ _ _).2 e
    rw [← hf, ← hf, hmk P hPa hP] at e'
    simpa using e'
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.1 hg) (c : La ⧸ K)
  refine ⟨q.out, ?_⟩
  rw [hf, hmk Q hQa hQ]
  exact hq

end GlobalTheory.UPel.GeometricLevelExistence

namespace GlobalTheory.UPel.GeometricLevelExistence

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

end GlobalTheory.UPel.GeometricLevelExistence
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfMulAndAbsHalfNegOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfMulAndAbsHalfNegOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.AbsHalf

theorem ordL_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hxy : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  unfold ordL
  rw [dite_eq_right hxy, dite_eq_right hx', dite_eq_right hy']
  have : WithZero.unzero hxy = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    simp [map_mul]
  rw [this, toAdd_mul]
  ring

theorem ordL_neg_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ordL (-1 : L) = 0 := by
  have h1 : Valued.v (-1 : L) ≠ 0 := by simp
  unfold ordL
  rw [dite_eq_right h1]
  have : WithZero.unzero h1 = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero]
    simp only [Valuation.map_neg, Valuation.map_one]
    rfl
  rw [this]
  simp

end GlobalTheory.AbsHalf

namespace GlobalTheory.AbsHalf

theorem absHalf_mul_neg_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x y : w.adicCompletion E, x ≠ 0 → y ≠ 0 → absHalf w (x * y) = absHalf w x * absHalf w y) ∧
      absHalf w (-1) = 1 := by
  intro E _ _ _ w
  have hq : (0 : ℝ) < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  refine ⟨fun x y hx hy => ?_, ?_⟩
  · unfold absHalf
    rw [ordL_mul x y hx hy, neg_add, zpow_add₀ hq.ne', Real.sqrt_mul (zpow_nonneg hq.le _)]
    push_cast
    ring
  · unfold absHalf
    rw [ordL_neg_one]
    simp

end GlobalTheory.AbsHalf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfMulAndAbsHalfNegOneStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absHalf_mul_and_absHalf_neg_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), (∀ x y : w.adicCompletion E, x ≠ 0 → y ≠ 0 → absHalf w (x * y) = absHalf w x * absHalf w y) ∧ absHalf w (-1) = 1 := by
  first | exact @GlobalTheory.AbsHalf.absHalf_mul_neg_one | exact GlobalTheory.AbsHalf.absHalf_mul_neg_one | (intros; apply GlobalTheory.AbsHalf.absHalf_mul_neg_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixTraceFormBasisChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixTraceFormBasisChange
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GramChange

open GlobalTheory.UnitLemma

theorem herm_sum_sum (K : UQ) (B : InvAlg K) (β : B.A) {a : ℕ} (b : Fin a → B.A)
    (M : Matrix (Fin a) (Fin a) K.E) (i j : Fin a) :
    B.herm β (∑ k, M k i • b k) (∑ l, M l j • b l) =
      ∑ k, ∑ l, M k i * B.herm β (b k) (b l) * K.c (M l j) := by
  have hσ : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  unfold InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hσ, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    LinearMap.map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_of_sum (K : UQ) (B : InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L)
    (he : ∀ x, e (K.c x) = c (e x)) {a : ℕ} (β : B.A) (b v : Fin a → B.A)
    (M : Matrix (Fin a) (Fin a) K.E) (hv : ∀ j, v j = ∑ i, M i j • b i) :
    (Matrix.of fun i j => e (B.herm β (v i) (v j))) =
      (M.map e)ᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * (M.map e).map c := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.of_apply, hv, herm_sum_sum, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, he, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_basis_change : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → ∀ (a : ℕ) (β : B.A) (b : Module.Basis (Fin a) K.E B.A), (∀ P : GL (Fin a) L, ∃ b' : Module.Basis (Fin a) K.E B.A, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c) ∧ ∀ b' : Module.Basis (Fin a) K.E B.A, ∃ P : GL (Fin a) L, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c := by
  intro K B L _ e c he a β b
  refine ⟨fun P => ?_, fun b' => ?_⟩
  · set M : Matrix (Fin a) (Fin a) K.E := P.val.map e.symm with hM
    have hMe : M.map e = P.val := by
      ext i j; simp [hM]
    have hdet : IsUnit M.det := by
      have h1 : e M.det = P.val.det := by
        rw [← hMe]; exact RingHom.map_det (e : K.E →+* L) M
      have h2 : IsUnit P.val.det := (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      rw [← h1] at h2
      exact (isUnit_map_iff e _).mp h2
    refine ⟨b.map (Matrix.toLinearEquiv b M hdet), ?_⟩
    rw [gram_of_sum K B L e c he β b _ M, hMe]
    intro j
    simp [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  · have hdet : IsUnit ((b.toMatrix b').map e).det := by
      have h1 : e (b.toMatrix b').det = ((b.toMatrix b').map e).det :=
        RingHom.map_det (e : K.E →+* L) _
      rw [← h1]
      exact (isUnit_map_iff e _).mpr (b.isUnit_det b')
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet.ne_zero, ?_⟩
    rw [gram_of_sum K B L e c he β b b' (b.toMatrix b')]
    · rfl
    · intro j; rw [b.sum_toMatrix_smul_self]

end GlobalTheory.GramChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixTraceFormBasisChangeStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMatrix_traceForm_basis_change : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → ∀ (a : ℕ) (β : B.A) (b : Module.Basis (Fin a) K.E B.A), (∀ P : GL (Fin a) L, ∃ b' : Module.Basis (Fin a) K.E B.A, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c) ∧ ∀ b' : Module.Basis (Fin a) K.E B.A, ∃ P : GL (Fin a) L, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c := by
  first | exact @GlobalTheory.GramChange.gram_basis_change | exact GlobalTheory.GramChange.gram_basis_change | (intros; apply GlobalTheory.GramChange.gram_basis_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicActionRealCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicActionRealCoordinates
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.RealWeilF.MCont

theorem continuous_fstA (F : Type) [Field F] [NumberField F] : Continuous (fstA F) := continuous_fst

theorem continuous_comp_infPartF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) : Continuous (θ.comp (infPartF F E)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := isModuleTopology_AE F E
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hrep : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
  have hg : Continuous fun a : AF F => θ (fstA F a ⊗ₜ[F] (1 : E)) := h.2.comp (continuous_fstA F)
  have e : ∀ z, (θ.comp (infPartF F E)) z = ∑ i, θ (fstA F (B.equivFun z i) ⊗ₜ[F] (1 : E)) * τ (b i) := by
    intro z
    conv_lhs => rw [← B.sum_equivFun z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, RingHom.comp_apply]
    have : infPartF F E (B.equivFun z i ⊗ₜ[F] b i) = (fstA F (B.equivFun z i) ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] b i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    rw [this, map_mul, h.1]
  have : (θ.comp (infPartF F E) : AF F ⊗[F] E → ℂ) = fun z => ∑ i, θ (fstA F (B.equivFun z i) ⊗ₜ[F] (1 : E)) * τ (b i) :=
    funext e
  rw [this]
  exact continuous_finsetSum _ fun i _ => (hg.comp ((continuous_apply i).comp hrep)).mul continuous_const

theorem continuous_mMF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT θ hθ
  have hc : ∀ (w : InfinitePlace F) (m n : ℕ), Continuous fun x : Matrix (Fin m) (Fin n) (AEF F E) => compAtF θ w x :=
    fun w m n => continuous_id.matrix_map (continuous_comp_infPartF (hθ w))
  have h1 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JT p.2 :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_snd
  have h2 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JS p.1⁻¹ := by
    have : (fun g : GAF σ JS => mtF σ JS g⁻¹) =
        fun g => (((Subtype.val (show HR (AF F) σ JS from g))⁻¹ : GL (Fin nS) (AF F ⊗[F] E)) : Matrix _ _ _) := rfl
    have hi : Continuous fun g : GAF σ JS => mtF σ JS g⁻¹ := by
      rw [this]; exact Units.continuous_coe_inv.comp continuous_subtype_val
    exact hi.comp continuous_fst
  have e : (mMF σ JS JT θ : GAF σ JS × GAF σ JT → _) = fun p =>
      GlobalTheory.RealWeil.blk (fun w => compAtF θ w (mtF σ JT p.2)) fun w => compAtF θ w (mtF σ JS p.1⁻¹) := funext fun p => rfl
  rw [e]
  exact GlobalTheory.RealWeil.continuous_blk (fun w => (hc w _ _).comp h1) fun w => (hc w _ _).comp h2

end GlobalTheory.RealWeilF.MCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicActionRealCoordinatesStatement
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_adelicAction_realCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  first | exact @GlobalTheory.RealWeilF.MCont.continuous_mMF | exact GlobalTheory.RealWeilF.MCont.continuous_mMF | (intros; apply GlobalTheory.RealWeilF.MCont.continuous_mMF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageProdMulEqMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageProdMulEqMul
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.AvgProd

lemma apply_out_rStab {H : Type} [Group H] (u : H → ℂ) (x : H) :
    u ((x : H ⧸ rStab u).out) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
  rw [hk]
  have hk' : ∀ y, u (y * (k : H)) = u y := k.2
  exact hk' x

theorem avg_prod : ∀ (H H' : Type) [Group H] [Group H'] (u : H → ℂ) (v : H' → ℂ), (rStab u).index ≠ 0 →
    (rStab v).index ≠ 0 → avg (fun x : H × H' => u x.1 * v x.2) = avg u * avg v := by
  intro H H' _ _ u v hu hv
  set S : Subgroup (H × H') := (rStab u).prod (rStab v) with hS
  have hle : S ≤ rStab (fun x : H × H' => u x.1 * v x.2) := by
    intro p hp
    rw [hS, Subgroup.mem_prod] at hp
    have ha : ∀ y, u (y * p.1) = u y := hp.1
    have hb : ∀ y, v (y * p.2) = v y := hp.2
    intro x
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [ha x.1, hb x.2]
  have hSi : S.index = (rStab u).index * (rStab v).index := Subgroup.index_prod _ _
  have hS0 : S.index ≠ 0 := by rw [hSi]; exact mul_ne_zero hu hv
  rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser _ _ S hle hS0]
  haveI : (rStab u).FiniteIndex := ⟨hu⟩
  haveI : (rStab v).FiniteIndex := ⟨hv⟩
  haveI : S.FiniteIndex := ⟨hS0⟩
  letI : Fintype (H ⧸ rStab u) := Fintype.ofFinite _
  letI : Fintype (H' ⧸ rStab v) := Fintype.ofFinite _
  letI : Fintype ((H × H') ⧸ S) := Fintype.ofFinite _
  let f : (H × H') ⧸ S → (H ⧸ rStab u) × (H' ⧸ rStab v) :=
    fun q => ((q.out.1 : H ⧸ rStab u), (q.out.2 : H' ⧸ rStab v))
  have hf : Function.Bijective f := by
    constructor
    · intro q q' h
      simp only [f, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [QuotientGroup.eq] at h1 h2
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
      exact (Subgroup.mem_prod (H := rStab u) (K := rStab v)).2 ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨a, b⟩
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      refine ⟨((x, y) : (H × H') ⧸ S), ?_⟩
      have h := QuotientGroup.out_eq' ((x, y) : (H × H') ⧸ S)
      rw [QuotientGroup.eq] at h
      replace h := (Subgroup.mem_prod (H := rStab u) (K := rStab v)).1 h
      simp only [f, Prod.mk.injEq]
      rw [QuotientGroup.eq, QuotientGroup.eq]
      exact ⟨by simpa using h.1, by simpa using h.2⟩
  have hsum : ∑ᶠ q : (H × H') ⧸ S, (fun x : H × H' => u x.1 * v x.2) q.out =
      (∑ᶠ a : H ⧸ rStab u, u a.out) * ∑ᶠ b : H' ⧸ rStab v, v b.out := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_mul_sum,
      ← Fintype.sum_prod_type']
    refine Fintype.sum_bijective f hf _ _ ?_
    intro q
    simp only [f, apply_out_rStab]
  rw [hsum]
  unfold avg
  rw [hSi]
  push_cast
  rw [mul_inv]
  ring

end GlobalTheory.AvgProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageProdMulEqMulStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupAverage_prod_mul_eq_mul : ∀ (H H' : Type) [Group H] [Group H'] (u : H → ℂ) (v : H' → ℂ), (rStab u).index ≠ 0 → (rStab v).index ≠ 0 → avg (fun x : H × H' => u x.1 * v x.2) = avg u * avg v := by
  first | exact @GlobalTheory.AvgProd.avg_prod | exact GlobalTheory.AvgProd.avg_prod | (intros; apply GlobalTheory.AvgProd.avg_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSameSeparableCharpolySplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSameSeparableCharpolySplitPlace
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitConj

theorem exists_conj_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ P ∈ Ell E n,
    ∀ w : Pl E, IsSplitAt w → ∀ γ γ' : UL n w, γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P →
      ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  intro E _ _ _ n P hP w hw γ γ' h h'
  have hs : (atPl w P).Separable := hP.2.2.1.map
  obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.conj_of_charpoly γ.1 γ'.1 (by rw [h]; exact hs) (h.trans h'.symm)
  have hmem : g ∈ UL n w := by
    rw [UL, if_pos hw]
    exact Subgroup.mem_top g
  exact ⟨⟨g, hmem⟩, Subtype.ext hg⟩

end GlobalTheory.BCT.SplitConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSameSeparableCharpolySplitPlaceStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_same_separable_charpoly_split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ P ∈ Ell E n, ∀ w : Pl E, IsSplitAt w → ∀ γ γ' : UL n w, γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  first | exact @GlobalTheory.BCT.SplitConj.exists_conj_of_isSplitAt | exact GlobalTheory.BCT.SplitConj.exists_conj_of_isSplitAt | (intros; apply GlobalTheory.BCT.SplitConj.exists_conj_of_isSplitAt <;> assumption)
end
end
