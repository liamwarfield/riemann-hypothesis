module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationAlongContinuousQuotientMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundFromBoxVolumeGrowth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumQuadraticCharacterBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCompactSetDensityBounded
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeGaussSumEstimate

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DenLE
noncomputable def UpperTheory.Reformulated.B.Yhb9.DenLE :
    {V H : Type} →
      [inst : MeasurableSpace V] →
        [inst_1 : MeasurableSpace H] → MeasureTheory.Measure V → MeasureTheory.Measure H → (V → H) → Set V → ENNReal → Prop :=
    fun {V H : Type} [MeasurableSpace V] [MeasurableSpace H] (μ : MeasureTheory.Measure V) (ν : MeasureTheory.Measure H)
        (q : V → H) (S : Set V) (C : ENNReal) ↦
      ∀ (Y : Set H), MeasurableSet Y → (μ : Set V → ENNReal) (S ∩ q ⁻¹' Y) ≤ C * (ν : Set H → ENNReal) Y

theorem UpperTheory.Reformulated.B.Yhb9.main :
    ∀ {V H : Type} [inst : MeasurableSpace V] [inst_1 : MeasurableSpace H] {μ : MeasureTheory.Measure V}
      {ν : MeasureTheory.Measure H} {q : V → H} {T : V → V} {τ : H → H},
      MeasurableEmbedding T →
        Measurable τ →
          (∀ (X : V), q (T X) = τ (q X)) →
            ∀ {a c : NNReal},
              a ≠ (0 : NNReal) →
                MeasureTheory.Measure.map T μ = a • μ →
                  MeasureTheory.Measure.map τ ν = c • ν →
                    ∀ {S : Set V} {C : ENNReal},
                      UpperTheory.Reformulated.B.Yhb9.DenLE μ ν q S C → UpperTheory.Reformulated.B.Yhb9.DenLE μ ν q (T '' S) ((↑(a⁻¹ * c) : ENNReal) * C) := by
  intro V H _ _ μ ν q T τ hT hτ hq a c ha hTμ hτν S C hS Y hY
  have h1 : T ⁻¹' (T '' S ∩ q ⁻¹' Y) = S ∩ q ⁻¹' (τ ⁻¹' Y) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, hT.injective.mem_set_image, hq]
  have h2 : (a : ENNReal) * μ (T '' S ∩ q ⁻¹' Y) = μ (S ∩ q ⁻¹' (τ ⁻¹' Y)) := by
    have := congrArg (fun m => m (T '' S ∩ q ⁻¹' Y)) hTμ
    rw [hT.map_apply, h1, MeasureTheory.Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    exact this.symm
  have h3 : ν (τ ⁻¹' Y) = (c : ENNReal) * ν Y := by
    have := congrArg (fun m => m Y) hτν
    rw [MeasureTheory.Measure.map_apply hτ hY, MeasureTheory.Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at this
    exact this
  have h4 := hS (τ ⁻¹' Y) (hτ hY)
  rw [h3, ← h2] at h4
  have ha' : (a : ENNReal) ≠ 0 := by exact_mod_cast ha
  calc μ (T '' S ∩ q ⁻¹' Y) = (a : ENNReal)⁻¹ * ((a : ENNReal) * μ (T '' S ∩ q ⁻¹' Y)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha' ENNReal.coe_ne_top, one_mul]
    _ ≤ (a : ENNReal)⁻¹ * (C * ((c : ENNReal) * ν Y)) := by gcongr
    _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_inv ha]; ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesArchimedeanHaar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesArchimedeanHaar
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem pi_map_update_add {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] {n : ℕ}
    (ν : Measure V) [SigmaFinite ν] [ν.IsAddRightInvariant] (a : Fin n) (T : (Fin n → V) → V)
    (hT : Measurable T) (hTa : ∀ x y, T (Function.update x a y) = T x) :
    (Measure.pi fun _ : Fin n => ν).map (fun x => Function.update x a (x a + T x)) =
      Measure.pi fun _ : Fin n => ν := by
  have hf : Measurable (fun x : Fin n → V => Function.update x a (x a + T x)) := by
    refine Measurable.of_eval fun j => ?_
    by_cases h : j = a
    · subst h
      simp only [Function.update_self]
      exact (measurable_pi_apply j).add hT
    · simpa [Function.update_of_ne h] using measurable_pi_apply j
  refine (Measure.pi_eq fun s hs => ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [← Measure.pi_pi, ← lintegral_indicator_one h2s, ← lintegral_indicator_one h2s,
    lintegral_map (measurable_one.indicator h2s) hf]
  refine lintegral_eq_of_lmarginal_eq {a} ((measurable_one.indicator h2s).comp hf)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  have key : ∀ y : V, Function.update (Function.update x a y) a (Function.update x a y a + T (Function.update x a y))
      = Function.update x a (y + T x) := by
    intro y
    simp [hTa]
  simp only [Function.comp_def, key]
  exact lintegral_add_right_eq_self
    (fun y => (Set.univ.pi s).indicator (1 : (Fin n → V) → ℝ≥0∞) (Function.update x a y)) (T x)

theorem coordW_map_shearK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s) = GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  intro F E _ _ _ _ _ σ hσ n M d b lam hlam a s hs
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) := inferInstance
  haveI hν : (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).IsAddHaarMeasure := inferInstance
  have hmul : ∀ c : Ainf F ⊗[F] E, Measurable (fun y : Ainf F ⊗[F] E => c * y) := fun c =>
    (continuous_const.mul continuous_id).measurable
  have hT : Measurable (fun (x : Fin n → Fin M → Ainf F ⊗[F] E) (i : Fin M) => ∑ c, s c * x c i) := by
    refine Measurable.of_eval fun i => ?_
    refine Finset.measurable_sum _ fun c _ => ?_
    exact (hmul (s c)).comp ((measurable_pi_apply i).comp (measurable_pi_apply c))
  have hTa : ∀ (x : Fin n → Fin M → Ainf F ⊗[F] E) (y : Fin M → Ainf F ⊗[F] E),
      (fun i => ∑ c, s c * Function.update x a y c i) = fun i => ∑ c, s c * x c i := by
    intro x y
    funext i
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : c = a
    · subst h; simp [hs]
    · simp [Function.update_of_ne h]
  exact pi_map_update_add (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) a _ hT hTa

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesArchimedeanHaarStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_preserves_archimedean_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s) = GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.coordW_map_shearK | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.coordW_map_shearK | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.coordW_map_shearK <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMeasureScalingByUnits
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMeasureScalingByUnits
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

theorem pi_smul_nnreal {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  classical
  refine Measure.pi_eq (μ := fun i => c i • μ i) fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib]
  norm_cast

theorem coordW_map_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (fun X a i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * X a i) = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  intro F E _ _ _ _ _ σ hσ n M d b lam hlam e he t ht
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  have hfm : ∀ a, Measurable (fun y : Ainf F ⊗[F] E => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * y) :=
    fun a => (continuous_const.mul continuous_id).measurable
  have hrow : ∀ a, (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map
      (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) =
      (((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam := by
    intro a
    obtain ⟨u, hu⟩ := ht a
    have h := GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t a) (ht a)
    rw [← hu] at h
    have hk := coordK_map_unit (Ainf F) σ hσ b lam u _ h
    rw [hu] at hk
    have hk1 := pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) _ (hfm a) _ hk
    simp only [Fintype.card_fin, ← pow_mul] at hk1
    exact hk1
  have hrm : ∀ a, Measurable (fun (x : Fin M → Ainf F ⊗[F] E) i =>
      algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) := fun a =>
    measurable_pi_iff.2 fun i => (hfm a).comp (measurable_pi_apply i)
  haveI : ∀ a, SigmaFinite ((Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map
      (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i)) := fun a => by
    rw [hrow a]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : Fin n => Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam)
    (f := fun a (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) (fun a => (hrm a).aemeasurable)
  unfold GlobalTheory.CompanionTheory.SW.coordW
  refine hmap.trans ?_
  simp only [hrow]
  exact pi_smul_nnreal _ _

end GlobalTheory.CompanionTheory.SW.Dil
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMeasureScalingByUnitsStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_measure_scaling_by_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (fun X a i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * X a i) = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  first | exact @GlobalTheory.CompanionTheory.SW.Dil.coordW_map_units | exact GlobalTheory.CompanionTheory.SW.Dil.coordW_map_units | (intros; apply GlobalTheory.CompanionTheory.SW.Dil.coordW_map_units <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHermitianScalingByUnits
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHermitianScalingByUnits
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.DiagScale

section Gen

theorem pi_map_scale_family {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (f : ι → X → X) (hf : ∀ i, Measurable (f i)) (c : ι → ℝ≥0) (h : ∀ i, μ.map (f i) = c i • μ) :
    (Measure.pi fun _ : ι => μ).map (fun x i => f i (x i)) =
      (∏ i, c i) • Measure.pi fun _ : ι => μ := by
  haveI : ∀ i, SigmaFinite (μ.map (f i)) := fun i => by rw [h i]; infer_instance
  rw [Measure.pi_map_pi (f := f) (fun i => (hf i).aemeasurable)]
  simp only [h]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
  push_cast
  rfl

theorem map_mul_scale {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [MeasurableSpace A] [BorelSpace A] (lam : Measure A) (u v : A) (c c' : ℝ≥0)
    (hu : lam.map (fun y => u * y) = c • lam) (hv : lam.map (fun y => v * y) = c' • lam) :
    lam.map (fun y => u * v * y) = (c * c') • lam := by
  have hm : ∀ x : A, Measurable (fun y : A => x * y) :=
    fun x => (continuous_const.mul continuous_id).measurable
  have e : (fun y => u * v * y) = (fun y => u * y) ∘ (fun y => v * y) := by
    funext y
    simp [mul_assoc]
  rw [e, ← Measure.map_map (hm u) (hm v), hv,
    Measure.map_smul c' (hm u).aemeasurable, hu, smul_smul, mul_comm]

def mulU (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [MeasurableSpace A] [BorelSpace A] (u : Aˣ) : A ≃ᵐ A :=
  { toEquiv := Units.mulLeft u
    measurable_toFun := (continuous_const.mul continuous_id).measurable
    measurable_invFun := (continuous_const.mul continuous_id).measurable }

theorem prod_pairs {n : ℕ} (c : Fin n → ℝ≥0) :
    (∏ i, c i * c i) * ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2 =
      ∏ a, c a ^ (2 * n) := by
  classical
  set g : Fin n × Fin n → ℝ≥0 := fun x => c x.1 * c x.2 with hg
  have h1 : ∏ x : Fin n × Fin n, g x = (∏ a, c a) ^ (2 * n) := by
    rw [Fintype.prod_prod_type]
    simp only [hg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_pow]
    ring
  have hU : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x =
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, g p :=
    Finset.prod_subtype _ (by simp) _
  have hL : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.2 < x.1), g x =
      ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x :=
    Finset.prod_equiv (Equiv.prodComm _ _) (by simp) (by simp [hg, mul_comm])
  have hD : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 = x.2), g x =
      ∏ i, c i * c i := by
    symm
    refine Finset.prod_nbij' (fun i => (i, i)) Prod.fst (by simp) (by simp) (by simp) ?_ (by simp [hg])
    rintro ⟨a, b⟩ h
    simpa using (Finset.mem_filter.1 h).2
  have hS : ∏ x : Fin n × Fin n, g x =
      (∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x) *
      ((∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 = x.2), g x) *
       (∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.2 < x.1), g x)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x : Fin n × Fin n => x.1 < x.2) g]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not
      (Finset.univ.filter (fun x : Fin n × Fin n => ¬ x.1 < x.2)) (fun x => x.1 = x.2) g,
      Finset.filter_filter, Finset.filter_filter]
    congr 1
    · refine Finset.prod_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by simp [h], h⟩
    · refine Finset.prod_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
      constructor
      · intro h
        exact lt_of_le_of_ne (not_lt.1 h.1) (fun e => h.2 e.symm)
      · intro h
        exact ⟨not_lt.2 h.le, h.ne'⟩
  have hP : ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2 =
      (∏ p : {p : Fin n × Fin n // p.1 < p.2}, g p) ^ 2 := by
    rw [Finset.prod_pow]
  have hT : ∏ a, c a ^ (2 * n) = (∏ a, c a) ^ (2 * n) := Finset.prod_pow _ _ _
  rw [hT, ← h1, hS, hL, hD, hU, hP]
  ring

end Gen

section H
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

theorem coordHerm_map_diag (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (lam : Measure R) [lam.IsAddHaarMeasure] {n : ℕ}
    (u : Fin n → Rˣ) (c : Fin n → ℝ≥0) (h : ∀ a, lam.map (fun y => (u a : R) * y) = c a • lam)
    (τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n) (hτm : Measurable τ)
    (hτ : ∀ S i j, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j =
      algebraMap R (R ⊗[F] E) (u i) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j *
        algebraMap R (R ⊗[F] E) (u j)) :
    (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n).map τ =
      (∏ a, c a ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hσ
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  obtain ⟨hK, -, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ R 2 b lam ‹_›
  haveI := hK
  haveI := hH n
  have hhom := GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6
  let φ := GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord R σ n
  let Q : Measure ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    Measure.pi fun _ => GlobalTheory.CompanionTheory.SW.coordK R b lam
  let P := (Measure.pi fun _ : Fin n => lam).prod Q
  have hν : GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n = Measure.comap φ P := rfl
  have hcond : Function.Injective φ ∧ ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P := by
    by_contra hc
    have h0 : GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n = 0 := by
      rw [hν, Measure.comap, dite_eq_right hc]
    have := isOpen_univ.measure_pos (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n) Set.univ_nonempty
    simp [h0] at this
  let D1 : (Fin n → R) ≃ᵐ (Fin n → R) :=
    MeasurableEquiv.piCongrRight fun i => mulU R (u i * u i)
  let D2 : ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) ≃ᵐ
      ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    MeasurableEquiv.piCongrRight fun p =>
      mulU (R ⊗[F] E) (Units.map (algebraMap R (R ⊗[F] E)).toMonoidHom (u p.1.1 * u p.1.2))
  have hsc : ∀ a a', lam.map (fun y => ((u a * u a' : Rˣ) : R) * y) = (c a * c a') • lam := by
    intro a a'
    rw [Units.val_mul]
    exact map_mul_scale lam _ _ _ _ (h a) (h a')
  have m1 : (Measure.pi fun _ : Fin n => lam).map D1 =
      (∏ i, c i * c i) • Measure.pi fun _ : Fin n => lam :=
    pi_map_scale_family lam (fun i y => ((u i * u i : Rˣ) : R) * y)
      (fun i => (continuous_const.mul continuous_id).measurable) _ (fun i => hsc i i)
  have m2 : Q.map D2 = (∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2) • Q :=
    pi_map_scale_family (GlobalTheory.CompanionTheory.SW.coordK R b lam)
      (fun (p : {p : Fin n × Fin n // p.1 < p.2}) y => algebraMap R (R ⊗[F] E) ((u p.1.1 * u p.1.2 : Rˣ) : R) * y)
      (fun p => (continuous_const.mul continuous_id).measurable) _
      (fun p => GlobalTheory.CompanionTheory.SW.Dil.coordK_map_unit R σ hσ b lam _ _ (hsc p.1.1 p.1.2))
  have hD : P.map (D1.prodCongr D2) = (∏ a, c a ^ (2 * n)) • P := by
    have e := Measure.map_prod_map (Measure.pi fun _ : Fin n => lam) Q D1.measurable D2.measurable
    rw [m1, m2, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, prod_pairs] at e
    exact e.symm
  rw [hν]
  refine GlobalTheory.CompanionTheory.SW.Dil.map_comap_scale φ P τ hτm (D1.prodCongr D2) _ hhom.surjective hcond.1 hcond.2 ?_ hD
  intro S
  refine Prod.ext ?_ ?_
  · funext i
    change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i) =
      ((u i * u i : Rˣ) : R) * (algebraMap F R (1 / 2) *
        Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i))
    have e : algebraMap R (R ⊗[F] E) (u i) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i *
        algebraMap R (R ⊗[F] E) (u i) =
        ((u i * u i : Rˣ) : R) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i := by
      rw [Algebra.smul_def, Units.val_mul, map_mul]
      ring
    rw [hτ, e, map_smul, smul_eq_mul]
    ring
  · funext p
    change (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2 =
      algebraMap R (R ⊗[F] E) ((u p.1.1 * u p.1.2 : Rˣ) : R) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2
    rw [hτ, Units.val_mul, map_mul]
    ring

end H

theorem coordHerm_map_diag_ainf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S i j, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) (t i) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j * algebraMap (Ainf F) (Ainf F ⊗[F] E) (t j)) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  intro F E _ _ _ _ _ σ hσ n d b lam hlam e he t ht τ hτm hτ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact coordHerm_map_diag (Ainf F) σ hσ b lam (fun a => (ht a).unit)
    (fun a => (∏ w, ‖e (t a) w‖₊)⁻¹)
    (fun a => GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t a) (ht a)) τ hτm hτ

end GlobalTheory.CompanionTheory.SW.DiagScale
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHermitianScalingByUnitsStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_hermitian_scaling_by_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S i j, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) (t i) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j * algebraMap (Ainf F) (Ainf F ⊗[F] E) (t j)) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  first | exact @GlobalTheory.CompanionTheory.SW.DiagScale.coordHerm_map_diag_ainf | exact GlobalTheory.CompanionTheory.SW.DiagScale.coordHerm_map_diag_ainf | (intros; apply GlobalTheory.CompanionTheory.SW.DiagScale.coordHerm_map_diag_ainf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilMeasure
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem isSplitK_of_isCoord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ)}
    {τ : NumberField.InfinitePlace F → (E →+* ℂ)} {Θ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)}
    (h : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.IsCoord σ e τ Θ) : IsSplitK e σ Θ := by
  refine ⟨h.1, h.2.1, fun a w => ?_⟩
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hs : sigR (Ainf F) σ (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) = algebraMap (Ainf F) (Ainf F ⊗[F] E) a := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  have h1 := h.2.1 (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) w
  rw [hs] at h1
  have h2 := h.2.2.2 (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) w
  rw [← h1] at h2
  have h3 : Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) = 2 * a := by
    rw [Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Ainf F) (Module.finBasis F E))]
    simp [hCM.2.2.1, two_mul, two_nsmul]
  rw [h3, map_mul, map_ofNat] at h2
  have h4 : ((2 : NumberField.InfinitePlace F → ℝ) w) = 2 := rfl
  rw [Pi.mul_apply, h4] at h2
  push_cast at h2
  linear_combination (-1 / 2 : ℂ) * h2

end GlobalTheory.CompanionTheory.WhitFree.AvgInf

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem denLE_image {V H : Type} [MeasurableSpace V] [MeasurableSpace H] {μ : Measure V} {ν : Measure H} {q : V → H}
    {T : V → V} {τ : H → H} (hT : MeasurableEmbedding T) (hτ : Measurable τ) (hq : ∀ X, q (T X) = τ (q X))
    {a c : ℝ≥0} (ha : a ≠ 0) (hμ : μ.map T = a • μ) (hν : ν.map τ = c • ν) {S : Set V} {C : ℝ≥0∞}
    (h : DenLE μ ν q S C) : DenLE μ ν q (T '' S) (((a⁻¹ * c : ℝ≥0) : ℝ≥0∞) * C) :=
  _root_.UpperTheory.Reformulated.B.Yhb9.main hT hτ hq ha hμ hν h

theorem dom_generic {K W : Type} [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) {n M : ℕ} (hn : 0 < n) (hM : 2 * n < M)
    {H : Type} [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] {μ : Measure (Fin n → Fin M → K)}
    {ν : Measure H} {q : (Fin n → Fin M → K) → H} {C₀ : ℝ≥0∞} (hC : C₀ ≠ ⊤)
    (hbox : ∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) →
      DenLE μ ν q (boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n))))
    (hsh : ∀ (S : Set (Fin n → Fin M → K)) (C : ℝ≥0∞) (a : Fin n) (s : Fin n → K), s a = 0 →
      DenLE μ ν q S C → DenLE μ ν q (shearK a s '' S) C)
    (hq : Measurable q) (hbm : ∀ r : Fin n → W → ℝ, MeasurableSet (boxK (M := M) κ r))
    {φ : (Fin n → Fin M → K) → ℂ} {B : ℝ} (hB : ∀ X, ‖φ X‖ ≤ B)
    (hdec : ∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ R ε' : ℝ, 0 < ε' ∧ ∀ Y, MeasurableSet Y →
      ∫⁻ X in (goodK κ R ε')ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  have hε2 : ε / 2 ≠ 0 := by simp [ENNReal.div_eq_top, hε]
  obtain ⟨R, hR, htail⟩ := GlobalTheory.T.exists_box_radius_tail_lintegral_le_eps_mul K W κ n M H μ ν q C₀ hC hbox hq hbm φ hdec (ε / 2) hε2
  set Bc : ℝ≥0∞ := ENNReal.ofReal B with hBc
  have hBt : Bc + 1 ≠ ⊤ := by simp [hBc]
  have hδ : ε / 2 / (Bc + 1) ≠ 0 := by
    simp [ENNReal.div_eq_top, hε, hBc]
  obtain ⟨ε', hε', hbad⟩ := GlobalTheory.T.density_bound_from_box_volume_growth K W κ n M hn hM H μ ν q C₀ hC hbox hsh R hR _ hδ
  refine ⟨R, ε', hε', fun Y hY => ?_⟩
  have hsub : (goodK κ R ε')ᶜ ∩ q ⁻¹' Y ⊆ ((boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y) ∪
      ((boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y) := by
    rintro X ⟨hX, hXY⟩
    by_cases hb : X ∈ boxK κ (fun _ _ => R)
    · exact Or.inr ⟨⟨hb, hX⟩, hXY⟩
    · exact Or.inl ⟨hb, hXY⟩
  have h2 : ∫⁻ X in (boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε / 2 * ν Y := by
    calc ∫⁻ X in (boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ
        ≤ ∫⁻ _ in (boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y, Bc ∂μ :=
          lintegral_mono fun X => by
            rw [hBc, ← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (hB X)
      _ = Bc * μ ((boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y) := by
          rw [setLIntegral_const]
      _ ≤ Bc * (ε / 2 / (Bc + 1) * ν Y) := by
          gcongr
          exact hbad Y hY
      _ ≤ (Bc + 1) * (ε / 2 / (Bc + 1)) * ν Y := by
          rw [← mul_assoc]
          gcongr
          exact le_self_add
      _ ≤ ε / 2 * ν Y := by
          gcongr
          exact ENNReal.mul_div_le
  calc ∫⁻ X in (goodK κ R ε')ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ
      ≤ ∫⁻ X in ((boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y) ∪
        ((boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y), ‖φ X‖ₑ ∂μ := lintegral_mono_set hsub
    _ ≤ _ + _ := lintegral_union_le _ _ _
    _ ≤ ε / 2 * ν Y + ε / 2 * ν Y := add_le_add (htail Y hY) h2
    _ = ε * ν Y := by rw [← add_mul, ENNReal.add_halves]

end GlobalTheory.CompanionTheory.WhitFree.AvgInf

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem shearK_eq_rmul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n M : ℕ}
    (a : Fin n) (s : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    shearK a s X = GlobalTheory.CompanionTheory.SW.rmul R X (shearM a s) := by
  funext c i
  simp only [shearK, GlobalTheory.CompanionTheory.SW.rmul, shearM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : c = a
  · subst h
    simp [mul_comm]
  · simp [Function.update, h]

theorem shearK_neg {K : Type} [CommRing K] {n M : ℕ} (a : Fin n) (s : Fin n → K) (hs : s a = 0)
    (X : Fin n → Fin M → K) : shearK a (-s) (shearK a s X) = X := by
  funext c i
  by_cases h : c = a
  · subst h
    have h1 : ∀ b, (-s) b * shearK c s X b i = -(s b * X b i) := by
      intro b
      by_cases hb : b = c
      · subst hb
        simp [hs]
      · simp [shearK, Function.update, hb]
    simp only [shearK, Function.update_self]
    have h2 : ∑ b, (-s) b * (Function.update X c (fun i => X c i + ∑ b, s b * X b i)) b i = -∑ b, s b * X b i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => h1 b
    rw [h2]
    ring
  · simp [shearK, Function.update, h]

end GlobalTheory.CompanionTheory.WhitFree.AvgInf

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem avgInf_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∀ minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E), IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ (c : HermR (Ainf F) σ n) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Measurable φ ∧ Integrable φ (minf c) ∧ ∀ ρ : ℕ → HermR (Ainf F) σ n → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets → (∀ k, Integrable (fun X => φ X * (gramTest (Ainf F) σ J c (ρ k) X : ℂ)) (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) ∧ Filter.Tendsto (fun k => (∫ X, φ X * (gramTest (Ainf F) σ J c (ρ k) X : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) / ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(minf c))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn hM d b lam hinf minf hminf c φ hφ
  classical
  have hlam : lam.IsAddHaarMeasure := hinf.1
  obtain ⟨ρ0, e, hρ0, he, hρe, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hCM.1
  obtain ⟨τ₀, κ, hco⟩ := GlobalTheory.T.complex_coordinates_exist_at_infinity F E σ hCM ρ0 e hρ0 he hρe
  obtain ⟨hκ, -, hκa⟩ := isSplitK_of_isCoord hCM hco
  have hloc := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  haveI i1 : LocallyCompactSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) := hLH
  haveI i2 : SecondCountableTopology (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) := hSH
  haveI i3 : T2Space (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) := hT2H
  haveI i4 : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) := ⟨rfl⟩
  haveI i5 : LocallyCompactSpace (HermR (Ainf F) σ n) := hLH
  haveI i6 : SecondCountableTopology (HermR (Ainf F) σ n) := hSH
  haveI i7 : T2Space (HermR (Ainf F) σ n) := hT2H
  haveI i8 : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b lam hlam
  haveI := hW n M
  haveI := hH n
  obtain ⟨halg, -, -, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hCM M J hJ (Ainf F) n
  set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M with hμdef
  set ν := GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n with hνdef
  set Q := GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) (n := n) with hQdef
  have hQc : Continuous Q := by
    obtain ⟨G, hGc, hGe⟩ := hG M J hJ
    have : Q = G := by
      funext X
      exact Subtype.ext (hGe X)
    rw [this]
    exact hGc
  have hQv : ∀ X, (Q X : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = gramR (Ainf F) σ J X := fun _ => rfl
  obtain ⟨hbc, hUo, hgood⟩ := GlobalTheory.T.good_set_compact_linearly_independent (Ainf F ⊗[F] E) (NumberField.InfinitePlace F) κ hκ n M
  have hd : d = 2 := by
    rw [← hCM.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  obtain ⟨C₀, hC₀, hden⟩ := GlobalTheory.T.archimedean_compact_set_density_bounded F E σ hCM M J hJ n hn hM 2 b lam hlam (boxK κ fun _ _ => 1) (hbc _)
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E), Continuous fun S : HermR (Ainf F) σ n =>
      HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) h * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * h := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let τg : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun g S =>
    ⟨HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g, hmem S g⟩
  have hτm : ∀ g, Measurable (τg g) := fun g => ((hcj g).subtype_mk _).measurable
  have hτq : ∀ g X, Q (GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X g) = τg g (Q X) := fun g X => Subtype.ext (halg X g)
  have hrc : ∀ h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E),
      Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X h := by
    intro h
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [GlobalTheory.CompanionTheory.SW.rmul]
    refine continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun Y : Fin n → Fin M → Ainf F ⊗[F] E => Y k i :=
      (continuous_apply i).comp (continuous_apply k)
    exact h1.mul continuous_const
  have hsh : ∀ (S : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (C : ℝ≥0∞) (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 →
      DenLE μ ν Q S C → DenLE μ ν Q (shearK a s '' S) C := by
    intro S C a s hs hS
    have hsn : (-s) a = 0 := by simp [hs]
    have hcs : ∀ s' : Fin n → Ainf F ⊗[F] E,
        Continuous (shearK a s' : (Fin n → Fin M → Ainf F ⊗[F] E) → _) := by
      intro s'
      have : (shearK a s' : (Fin n → Fin M → Ainf F ⊗[F] E) → _) =
          fun X => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X (shearM a s') := funext fun X => shearK_eq_rmul _ a s' X
      rw [this]
      exact hrc _
    let eT : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → Fin M → Ainf F ⊗[F] E) :=
      { toFun := shearK a s
        invFun := shearK a (-s)
        left_inv := fun X => shearK_neg a s hs X
        right_inv := fun X => by
          have := shearK_neg a (-s) hsn X
          rwa [neg_neg] at this
        continuous_toFun := hcs s
        continuous_invFun := hcs (-s) }
    have hT : MeasurableEmbedding (shearK a s : (Fin n → Fin M → Ainf F ⊗[F] E) → _) := eT.measurableEmbedding
    have hμ' : μ.map (shearK a s) = (1 : ℝ≥0) • μ := by
      rw [one_smul]
      exact GlobalTheory.T.shear_preserves_archimedean_haar F E σ hCM n M 2 b lam hlam a s hs
    have hν' : ν.map (τg (shearM a s)) = (1 : ℝ≥0) • ν := by
      rw [one_smul]
      exact GlobalTheory.T.shear_pushforward_hermitian_measure F E σ hCM n 2 b lam hlam a s hs _ (hτm _) fun S => rfl
    have := denLE_image hT (hτm (shearM a s)) (fun X => by rw [shearK_eq_rmul]; exact hτq _ X) one_ne_zero hμ' hν' hS
    have e1 : (((1 : ℝ≥0)⁻¹ * 1 : ℝ≥0) : ℝ≥0∞) * C = C := by simp
    rw [e1] at this
    exact this
  have hbox : ∀ r : Fin n → NumberField.InfinitePlace F → ℝ, (∀ a w, 0 < r a w) →
      DenLE μ ν Q (boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n))) := by
    intro r hr
    let t : Fin n → Ainf F := fun a => e.symm (r a)
    let ti : Fin n → Ainf F := fun a => e.symm (fun w => (r a w)⁻¹)
    have het : ∀ a, e (t a) = r a := fun a => e.apply_symm_apply _
    have htt : ∀ a, t a * ti a = 1 := by
      intro a
      apply e.injective
      rw [map_mul, map_one, het]
      funext w
      simp only [ti, e.apply_symm_apply, Pi.mul_apply, Pi.one_apply]
      exact mul_inv_cancel₀ (hr a w).ne'
    have ht : ∀ a, IsUnit (t a) := fun a => IsUnit.of_mul_eq_one _ (htt a)
    let al : Ainf F → Ainf F ⊗[F] E := algebraMap (Ainf F) (Ainf F ⊗[F] E)
    have hal1 : ∀ a, al (t a) * al (ti a) = 1 := fun a => by
      simp only [al]
      rw [← map_mul, htt, map_one]
    let g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) := Matrix.diagonal fun a => al (t a)
    let T : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E) := fun X a i => al (t a) * X a i
    have hTr : ∀ X, T X = GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X g := by
      intro X
      funext a i
      simp [T, g, GlobalTheory.CompanionTheory.SW.rmul, Matrix.diagonal_apply, mul_comm]
    have hTc : ∀ u : Fin n → Ainf F ⊗[F] E, Continuous fun (X : Fin n → Fin M → Ainf F ⊗[F] E) a i => u a * X a i := by
      intro u
      refine continuous_pi fun a => continuous_pi fun i => ?_
      exact continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
    let eT : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → Fin M → Ainf F ⊗[F] E) :=
      { toFun := T
        invFun := fun X a i => al (ti a) * X a i
        left_inv := fun X => by
          funext a i
          simp only [T]
          rw [← mul_assoc, mul_comm (al (ti a)), hal1, one_mul]
        right_inv := fun X => by
          funext a i
          simp only [T]
          rw [← mul_assoc, hal1, one_mul]
        continuous_toFun := hTc _
        continuous_invFun := hTc _ }
    have hT : MeasurableEmbedding T := eT.measurableEmbedding
    have hsal : ∀ x : Ainf F, sigR (Ainf F) σ (al x) = al x := by
      intro x
      simp [al, sigR, Algebra.TensorProduct.algebraMap_apply]
    have hτe : ∀ (S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) i j,
        (τg g S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j =
          al (t i) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j * al (t j) := by
      intro S i j
      have h1 : HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g = g := by
        ext p q
        by_cases hpq : p = q
        · subst hpq
          simp [HeckeCharacterZeroLocus.SiegelWeilU.cT, g, hsal]
        · have hqp : q ≠ p := fun h => hpq h.symm
          simp [HeckeCharacterZeroLocus.SiegelWeilU.cT, g, Matrix.diagonal_apply, hpq, hqp]
      show (HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g) i j = _
      rw [h1]
      simp only [g, Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hμ' := GlobalTheory.T.archimedean_measure_scaling_by_units F E σ hCM n M 2 b lam hlam e he t ht
    have hν' := GlobalTheory.T.archimedean_hermitian_scaling_by_units F E σ hCM n 2 b lam hlam e he t ht (τg g) (hτm g) hτe
    set P : Fin n → ℝ≥0 := fun a => ∏ w, ‖e (t a) w‖₊ with hP
    have hP0 : ∀ a, P a ≠ 0 := by
      intro a
      refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
      rw [het]
      exact nnnorm_ne_zero_iff.2 (hr a w).ne'
    have ha : (∏ a, ((P a)⁻¹) ^ (2 * M)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (inv_ne_zero (hP0 a))
    have hq : ∀ X, Q (T X) = τg g (Q X) := fun X => by rw [hTr]; exact hτq g X
    have h1 := denLE_image hT (hτm g) hq ha hμ' hν' hden
    have himg : T '' (boxK κ fun _ _ => 1) = boxK κ r := by
      have hκn : ∀ (a : Fin n) (x : Ainf F ⊗[F] E) w, ‖κ (al (t a) * x) w‖ = r a w * ‖κ x w‖ := by
        intro a x w
        rw [map_mul, Pi.mul_apply, norm_mul, show κ (al (t a)) w = (e (t a) w : ℂ) from hκa _ _, het,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr a w)]
      ext X
      constructor
      · rintro ⟨Z, hZ, rfl⟩ a i w
        show ‖κ (al (t a) * Z a i) w‖ ≤ r a w
        rw [hκn]
        have := hZ a i w
        nlinarith [hr a w, norm_nonneg (κ (Z a i) w)]
      · intro hX
        refine ⟨eT.symm X, ?_, eT.apply_symm_apply X⟩
        intro a i w
        have h2 : T (eT.symm X) = X := eT.apply_symm_apply X
        have h3 := hX a i w
        rw [← h2] at h3
        change ‖κ (al (t a) * (eT.symm X) a i) w‖ ≤ r a w at h3
        rw [hκn] at h3
        have := hr a w
        by_contra hc
        push_neg at hc
        nlinarith
    rw [himg] at h1
    have hconst : (((∏ a, ((P a)⁻¹) ^ (2 * M))⁻¹ * ∏ a, ((P a)⁻¹) ^ (2 * n) : ℝ≥0) : ℝ≥0∞) * C₀ =
        C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)) := by
      have hk : ∀ a, ((P a)⁻¹ ^ (2 * M))⁻¹ * (P a)⁻¹ ^ (2 * n) = P a ^ (2 * (M - n)) := by
        intro a
        obtain ⟨k, rfl⟩ : ∃ k, M = n + k := ⟨M - n, by omega⟩
        have hx := hP0 a
        rw [Nat.add_sub_cancel_left, mul_add, inv_pow, inv_inv, pow_add, inv_pow, mul_comm,
          inv_mul_cancel_left₀ (pow_ne_zero _ hx)]
      have h2 : ((∏ a, ((P a)⁻¹) ^ (2 * M))⁻¹ * ∏ a, ((P a)⁻¹) ^ (2 * n) : ℝ≥0) = ∏ a, P a ^ (2 * (M - n)) := by
        rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun a _ => hk a
      rw [h2, mul_comm]
      congr 1
      push_cast
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [hP]
      push_cast
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [het]
      congr 1
      rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (hr a w).le]
      congr 1
      ext
      simp [abs_of_pos (hr a w)]
    rw [hconst] at h1
    exact h1
  have hbm : ∀ r : Fin n → NumberField.InfinitePlace F → ℝ, MeasurableSet (boxK (M := M) κ r) :=
    fun r => (hbc r).measurableSet
  obtain ⟨hφc, hφi, ⟨B, hB⟩, hdec⟩ := GlobalTheory.T.schwartz_arch_continuous_integrable F E σ hCM κ hκ n M 2 b lam hlam φ hφ
  have hdom : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ A : Set (Fin n → Fin M → Ainf F ⊗[F] E), IsCompact A ∧
      A ⊆ {X | LinearIndependent (Ainf F ⊗[F] E) X} ∧ ∀ Y, MeasurableSet Y →
        ∫⁻ X in Aᶜ ∩ Q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
    intro ε hε
    obtain ⟨R, ε', h0, h⟩ := dom_generic κ hn hM hC₀ hbox hsh hQc.measurable hbm hB hdec hε
    exact ⟨goodK κ R ε', (hgood R ε' h0).1, (hgood R ε' h0).2, h⟩
  let Q' : (Fin n → Fin M → Ainf F ⊗[F] E) → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n := Q
  have hQc' : Continuous Q' := hQc
  have key := GlobalTheory.T.disintegration_along_continuous_quotient_map (Fin n → Fin M → Ainf F ⊗[F] E) (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n)
    (Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) μ ν (gramR (Ainf F) σ J) Subtype.val Q' _ minf hUo hQc'
    Subtype.val_injective hQv hminf φ hφc hφi hdom c
  refine ⟨hφc.measurable, key.1, fun ρ hρ hs => ?_⟩
  have hgt : ∀ k X, gramTest (Ainf F) σ J c (ρ k) X = ρ k (c - Q X) := by
    intro k X
    have hm : (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) - gramR (Ainf F) σ J X ∈ HermR (Ainf F) σ n := (c - Q X).2
    unfold gramTest
    exact dif_pos hm
  let r : ℕ → HermR (Ainf F) σ n → ℝ := fun k y => ρ k (c - y)
  have hr1 : ∀ k, Continuous (r k) := fun k => (hρ k).1.comp (continuous_const.sub continuous_id)
  have hr2 : ∀ k, HasCompactSupport (r k) := fun k => (hρ k).2.1.comp_homeomorph (Homeomorph.subLeft c)
  have hint : ∀ k, ∫ y, r k y ∂ν = ∫ y, ρ k y ∂ν := fun k => integral_sub_left_eq_self (G := HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) (ρ k) ν c
  have hrk : ∀ k, Continuous (r k) ∧ HasCompactSupport (r k) ∧ (∀ y, 0 ≤ r k y) ∧ 0 < ∫ y, r k y ∂ν :=
    fun k => ⟨hr1 k, hr2 k, fun y => (hρ k).2.2.1 _, by rw [hint]; exact (hρ k).2.2.2⟩
  have hrs : Filter.Tendsto (fun k => tsupport (r k)) Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have h0 : (fun u => c - u) ⁻¹' t ∈ nhds (0 : HermR (Ainf F) σ n) := by
      have : Continuous fun u : HermR (Ainf F) σ n => c - u := continuous_const.sub continuous_id
      exact this.continuousAt.preimage_mem_nhds (by simpa using ht)
    filter_upwards [(Filter.tendsto_smallSets_iff.1 hs) _ h0] with k hk y hy
    have h1 : tsupport (r k) = (Homeomorph.subLeft c) ⁻¹' tsupport (ρ k) :=
      tsupport_comp_eq_preimage (ρ k) (Homeomorph.subLeft c)
    rw [h1] at hy
    have := hk hy
    simpa using this
  have hlim := key.2 r hrk hrs
  refine ⟨fun k => ?_, ?_⟩
  · obtain ⟨C, hC⟩ := (hr2 k).exists_bound_of_continuous (hr1 k)
    refine (hφi.norm.mul_const C).mono' ?_ (Filter.Eventually.of_forall fun X => ?_)
    · refine hφc.aestronglyMeasurable.mul ?_
      have : (fun X => ((gramTest (Ainf F) σ J c (ρ k) X : ℝ) : ℂ)) = fun X => ((r k (Q X) : ℝ) : ℂ) := by
        funext X
        rw [hgt]
      rw [this]
      exact (Complex.continuous_ofReal.comp ((hr1 k).comp hQc)).aestronglyMeasurable
    · rw [norm_mul, hgt, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · refine (hlim.congr fun k => ?_)
    rw [hint]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show φ X * ((r k (Q X) : ℝ) : ℂ) = φ X * ((gramTest (Ainf F) σ J c (ρ k) X : ℝ) : ℂ)
    rw [hgt]

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilMeasureStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_siegel_weil_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∀ minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E), IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ (c : HermR (Ainf F) σ n) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Measurable φ ∧ Integrable φ (minf c) ∧ ∀ ρ : ℕ → HermR (Ainf F) σ n → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets → (∀ k, Integrable (fun X => φ X * (gramTest (Ainf F) σ J c (ρ k) X : ℂ)) (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) ∧ Filter.Tendsto (fun k => (∫ X, φ X * (gramTest (Ainf F) σ J c (ρ k) X : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) / ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(minf c))) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.avgInf_tendsto | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.avgInf_tendsto | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.avgInf_tendsto <;> assumption)
end
