module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSemiPosMassFinite
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartSheetCompare
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjGenericRank
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualOperatorCommutesLie
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMassFiniteDirect

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.AdelCont

open PositivityTheory.Rg.Tf.Loc (twConj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem orbFn_mul_right (S : Set (Pl E)) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (U : Subgroup (Gf E a b))
    (hU : ∀ u ∈ U, ∀ y, finFn S φ₁ φ₂ (u⁻¹ * y * thP E a b u) = finFn S φ₁ φ₂ y)
    (x u : Gf E a b) (hu : u ∈ U) : orbFn S φ₁ φ₂ δ₁ δ₂ (x * u) = orbFn S φ₁ φ₂ δ₁ δ₂ x := by
  unfold orbFn
  rw [← hU u hu (x⁻¹ * (ratF E a δ₁, ratF E b δ₂) * thP E a b x), map_mul]
  congr 1
  group

theorem continuous_of_right_invariant {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] (f : G → X) (U : Subgroup G) (hUo : IsOpen (U : Set G))
    (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) : Continuous f := by
  have : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hmem : (x⁻¹ * ·) ⁻¹' (U : Set G) ∈ nhds x := by
      apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      apply hUo.mem_nhds
      simp [U.one_mem]
    filter_upwards [hmem] with y hy
    have := hf x (x⁻¹ * y) hy
    simpa using this
  exact this.continuous

theorem continuous_twConj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : Monoid.End G) (hθ : Continuous θ) (δ : G) : Continuous fun g : G => twConj θ g δ := by
  unfold twConj
  exact (continuous_inv.mul continuous_const).mul hθ

theorem adelContOf : AdelContOf := by
  intro hEq hFin hComp hTopo E _ _ _ hUnr a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ hψ t₁ t₂ d₁ d₂
  obtain ⟨e, he⟩ := hComp E a b
  have hc : Continuous (comps : GA E a × GA E b → Gi E a b × Gf E a b) := by
    have : (comps : GA E a × GA E b → Gi E a b × Gf E a b) = e := funext fun x => (he x).symm
    rw [this]; exact e.continuous
  have hθa : Continuous (thetaR (starRingEnd ℂ) a) := (hTopo E a).2.2.2.2.2
  have hθb : Continuous (thetaR (starRingEnd ℂ) b) := (hTopo E b).2.2.2.2.2
  obtain ⟨U, hUo, hU⟩ := hFin E hUnr a b S φ₁ φ₂ t₁ t₂
  have hfin : Continuous (orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)) :=
    continuous_of_right_invariant _ U hUo fun x u hu => orbFn_mul_right S φ₁ φ₂ _ _ U hU x u hu
  have hrw : (fun x : GA E a × GA E b =>
      adel S u₁ u₂ ψ φ₁ φ₂ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂))) =
      fun x => (∏ v, ψ v (twConj (thetaR (starRingEnd ℂ) a) ((comps x).1 v).1 (GeneralLinearGroup.map v.embedding d₁),
        twConj (thetaR (starRingEnd ℂ) b) ((comps x).1 v).2 (GeneralLinearGroup.map v.embedding d₂))) *
      orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) (comps x).2 :=
    funext fun x => hEq E a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ d₁ d₂ x
  rw [hrw]
  refine Continuous.mul (continuous_finsetProd _ fun v _ => (hψ v).comp ?_) (hfin.comp (continuous_snd.comp hc))
  have hv : Continuous fun x : GA E a × GA E b => (comps x).1 v :=
    (continuous_apply v).comp (continuous_fst.comp hc)
  exact ((continuous_twConj _ hθa _).comp (continuous_fst.comp hv)).prodMk
    ((continuous_twConj _ hθb _).comp (continuous_snd.comp hv))

end GlobalTheory.CompanionTheory.AdelCont

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScalarOfCentral
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.TranslAdele

theorem thetaR_thetaR {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (n : ℕ)
    (g : GL (Fin n) A) : thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  ext i j
  change σ (σ (g.val i j)) = g.val i j
  exact hσ _

theorem exists_scalar_of_central {K : Type} [Field K] {n : ℕ} (z : GL (Fin n) K)
    (hz : ∀ h : GL (Fin n) K, z * h = h * z) : ∃ c : K, z.val = Matrix.scalar (Fin n) c := by
  have : z.val ∈ Set.range (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    have h := hz ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩
    have h' := congrArg Units.val h
    exact h'.symm
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc.symm⟩

theorem Phi_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    (GlobalTheory.Tw.Phi n R).map f = GlobalTheory.Tw.Phi n S := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem translAd : TranslAd := by
  intro E _ _ _ n u hu g

  have hz : ∀ h : GL (Fin n) E, ((PhiU n E)⁻¹ * u) * h = h * ((PhiU n E)⁻¹ * u) := by
    intro h
    have hinv : thetaE E n (thetaE E n h) = h :=
      thetaR_thetaR (conjE E) (fun x => IsCMField.complexConj_apply_apply E x) n h
    have h1 := hu.1 (thetaE E n h)
    rw [hinv] at h1
    have h2 : thE E n (thetaE E n h) = PhiU n E * h * (PhiU n E)⁻¹ := by
      have := thetaGL_eq n E (IsCMField.complexConj E).toRingEquiv.toRingHom (thetaE E n h)
      rw [show thetaR (IsCMField.complexConj E).toRingEquiv.toRingHom n (thetaE E n h) = h from hinv] at this
      exact this
    rw [h2] at h1
    have h3 : h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * u * h := by
      have h4 : PhiU n E * h * (PhiU n E)⁻¹ * u = u * h := by rw [h1]; group
      calc h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * (PhiU n E * h * (PhiU n E)⁻¹ * u) := by group
        _ = (PhiU n E)⁻¹ * u * h := by rw [h4]; group
    rw [← h3, mul_assoc h]
  obtain ⟨c, hc⟩ := exists_scalar_of_central _ hz

  set w : GA E n := ratGL E n ((PhiU n E)⁻¹ * u) with hw
  have hwc : ∀ t : GA E n, w * t = t * w := by
    intro t
    apply Units.ext
    have hval : w.val = Matrix.scalar (Fin n) (algebraMap E (Ad E) c) := by
      have : w.val = (((PhiU n E)⁻¹ * u : GL (Fin n) E).val).map (algebraMap E (Ad E)) := rfl
      rw [this, hc]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [Units.val_mul, Units.val_mul, hval]
    exact Matrix.scalar_commute _ (fun r' => Commute.all _ _) _
  have hP : ratGL E n (PhiU n E) = PhiU n (Ad E) := by
    apply Units.ext
    rw [phiU_val, ← Phi_map (algebraMap E (Ad E)) n, ← phiU_val]
    rfl
  have hr : ratGL E n u = PhiU n (Ad E) * w := by
    rw [hw, map_mul, map_inv, hP, mul_inv_cancel_left]
  rw [thetaGL_eq, hr]
  have h5 : w * thetaA E n g * w⁻¹ = thetaA E n g := by rw [hwc]; group
  calc PhiU n (Ad E) * thetaR (conjAd E) n g * (PhiU n (Ad E))⁻¹
      = PhiU n (Ad E) * (w * thetaA E n g * w⁻¹) * (PhiU n (Ad E))⁻¹ := by rw [h5]
    _ = PhiU n (Ad E) * w * thetaA E n g * (PhiU n (Ad E) * w)⁻¹ := by group

end GlobalTheory.CompanionTheory.TranslAdele

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHolds
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.SegreChart

theorem Chart.incIdealDim : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
  GroundTheory.Heights₂.Heights.IncIdealDim.proof
    (GroundTheory.Heights₂.Heights.IncidenceGeneric.proof GroundTheory.Heights₂.Heights.FGNullstellensatz.proof)
    GroundTheory.Heights₂.Heights.GenericLinearTrdeg.proof GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof

theorem Chart.incIdealPrime : GroundTheory.Heights₂.Heights.IncIdealPrime.Statement :=
  GroundTheory.Heights₂.Heights.IncIdealPrime.proof
    (GroundTheory.Heights₂.Heights.IncidenceGeneric.proof GroundTheory.Heights₂.Heights.FGNullstellensatz.proof)

theorem Chart.coneDimOfChowForm : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof Chart.incIdealDim Chart.incIdealPrime

theorem Chart.GoodChartDim : GroundTheory.Heights₂.Heights.GoodChartDim.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartDim.proof GroundTheory.Heights₂.Heights.ConeVanishingHomog.proof GroundTheory.Heights₂.Heights.ConeSliceIdeal.proof GroundTheory.Heights₂.Heights.ChartDehomogPrime.proof

theorem Chart.GoodChartModel : GroundTheory.Heights₂.Heights.GoodChartModel.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartModel.proof GroundTheory.Heights₂.Heights.GoodChartZeroSet.proof Chart.GoodChartDim

theorem Chart.PtsGenericCount : GroundTheory.Heights₂.Heights.PtsGenericCount.Statement :=
  @GroundTheory.Heights₂.Heights.PtsGenericCount.proof Chart.GoodChartModel GroundTheory.Heights₂.Heights.ComponentsGenericCount.proof GroundTheory.Heights₂.Heights.SheetLift.proof

theorem Chart.PtsSheetSimpleNull : GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.proof Chart.PtsGenericCount

theorem Chart.PtsSheetOnlyNull : GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.proof GroundTheory.Heights₂.Heights.CriticalFibreInfinite.proof

theorem Chart.PtsPosPartProjIndep : GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.proof Chart.PtsSheetSimpleNull Chart.PtsSheetOnlyNull GroundTheory.Heights₂.Heights.PtsPosPartLocal.proof GroundTheory.Heights₂.Heights.PtsPosDensMeasurable.proof

theorem Chart.PtsSegreChartFibreSum : GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof

theorem Chart.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem Chart.ConeSliceSheetParam : GroundTheory.Heights₂.Heights.ConeSliceSheetParam.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSliceSheetParam.proof Chart.DiscriminantSheetCover

theorem Chart.AreaFormulaInjSet : GroundTheory.Heights₂.Heights.AreaFormulaInjSet.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInjSet.proof GroundTheory.Heights₂.Heights.AreaFormulaLocal.proof

theorem Chart.AreaFormulaInj : GroundTheory.Heights₂.Heights.AreaFormulaInj.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInj.proof Chart.AreaFormulaInjSet

theorem Chart.ConeMapAreaOne : GroundTheory.Heights₂.Heights.ConeMapAreaOne.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapAreaOne.proof Chart.AreaFormulaInj

theorem Chart.ConeMapArea : GroundTheory.Heights₂.Heights.ConeMapArea.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapArea.proof Chart.ConeMapAreaOne

theorem Chart.ConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.proof Chart.ConeSliceSheetParam Chart.ConeMapArea

theorem Chart.SliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.SliceMassFinite.proof' Chart.ConeSheetGramLintegral GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite Chart.coneDimOfChowForm

theorem Chart.SegreChartAbsIntegrable : GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.proof Chart.SliceMassFinite GroundTheory.Heights₂.Heights.SegreChartSheetCompare.proof

theorem Chart.PtsSemiPosMassFinite : GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.proof Chart.PtsPosPartProjIndep Chart.PtsSegreChartFibreSum Chart.SegreChartAbsIntegrable

theorem Chart.PtsPosDensIntegrable : GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.proof Chart.PtsSemiPosMassFinite

theorem Chart.PtsIntegralProjIndep : GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.proof Chart.PtsPosDensIntegrable Chart.PtsPosPartProjIndep

theorem Chart.PtsIntegralSegreChartProj : GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof Chart.SegreChartAbsIntegrable Chart.PtsSegreChartFibreSum

theorem Chart.SegreChartIntegral : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartIntegral.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SegreCoordGoodProj Chart.PtsIntegralProjIndep Chart.PtsIntegralSegreChartProj

end GlobalTheory.CompanionTheory.Ar.SegreChart
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segre_chart_integral_holds : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | exact GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceOrbitCoefficient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceOrbitCoefficient
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth

theorem isOpen_rightPeriods {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (F : G → Z)
    (N : Set G) (hN : N ∈ nhds (1 : G)) (h : ∀ g ∈ N, ∀ m, F (m * g) = F m) :
    IsOpen {g : G | ∀ m, F (m * g) = F m} := by
  let T : Subgroup G :=
    { carrier := {g : G | ∀ m, F (m * g) = F m}
      mul_mem' := by
        intro a b ha hb m
        rw [← mul_assoc, hb, ha]
      one_mem' := by intro m; rw [mul_one]
      inv_mem' := by
        intro a ha m
        have := ha (m * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hN ?_)
  intro g hg
  exact h g hg

theorem isOpen_stab_ind {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (v : smoothPart (ind H σ)) :
    IsOpen {x : G | ∀ y, v.1.1 (y * x) = v.1.1 y} := by
  have h : IsOpen {g : G | ind H σ g v.1 = v.1} := v.2
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    exact Subtype.ext (funext hx)
  · intro hx y
    exact congrFun (congrArg Subtype.val hx) y

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_castM {a b : ℕ} (h : a = b) : Continuous (castM k h) := by
  subst h
  exact continuous_id

theorem continuous_sEmb (n : ℕ) : Continuous (sEmb k n) :=
  GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM k n

theorem isOpen_dpowM_eq_one (n : ℕ) (s : ℝ) : IsOpen {g : Mir k n | dpowM n s g = 1} :=
  (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow k (n + 1) s).preimage continuous_subtype_val

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

theorem intO_mul_of_stab (f : XS τ σ) (κ : Mir k ((i + 1) + t + 1))
    (hκ : ∀ x : Mir k ((i + 1) + (t + 1)), evX f (x * κ) = evX f x) (y : Mir k ((i + 1) + t + 1)) :
    intO f (y * κ) = intO f y := by
  unfold intO
  congr 1
  funext d
  rw [← mul_assoc]
  exact hκ _

theorem eO_mul_of_stab (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k (i + (t + 1)))
    (hd : dpowM (i + (t + 1)) (-1 / 2) g = 1)
    (hκ : ∀ x : Mir k ((i + 1) + (t + 1)),
      evX f (x * sEmb k _ (castM k (by omega : i + (t + 1) = (i + 1) + t) g)) = evX f x) :
    eO ψ f (m * g) = eO ψ f m := by
  unfold eO
  rw [map_mul, hd, mul_one, map_mul, map_mul, ← mul_assoc, intO_mul_of_stab f _ hκ]

theorem isOpen_evX_stab (f : XS τ σ) :
    IsOpen {x : Mir k ((i + 1) + (t + 1)) | ∀ y : Mir k ((i + 1) + (t + 1)), evX f (y * x) = evX f y} :=
  isOpen_stab_ind _ _ (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ)))

end GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth

namespace GlobalTheory.CompanionTheory.BZPhiPG


open GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth in
theorem isOpen_eO_rightPeriods : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ),
    IsOpen {g : Mir k (i + (t + 1)) | ∀ m, eO ψ f (m * g) = eO ψ f m} := by
  intro k _ _ _ _ i t ψ τ σ f
  have hs : i + (t + 1) = (i + 1) + t := by omega
  have hφ : Continuous fun g : Mir k (i + (t + 1)) => sEmb k _ (castM k hs g) :=
    (continuous_sEmb _).comp (continuous_castM hs)
  have hU : IsOpen ({g : Mir k (i + (t + 1)) | dpowM (i + (t + 1)) (-1 / 2) g = 1} ∩
      (fun g : Mir k (i + (t + 1)) => sEmb k _ (castM k hs g)) ⁻¹'
        {x : Mir k ((i + 1) + (t + 1)) | ∀ y : Mir k ((i + 1) + (t + 1)), evX f (y * x) = evX f y}) :=
    (isOpen_dpowM_eq_one _ _).inter ((isOpen_evX_stab f).preimage hφ)
  refine isOpen_rightPeriods (eO ψ f) _ (hU.mem_nhds ⟨map_one _, ?_⟩) ?_
  · intro y
    simp
  · rintro g ⟨hd, hst⟩ m
    exact eO_mul_of_stab ψ f m g hd hst

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceOrbitCoefficientStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_right_invariance_orbit_coefficient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ),
  IsOpen {g : Mir k (i + (t + 1)) | ∀ m, eO ψ f (m * g) = eO ψ f m} := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.isOpen_eO_rightPeriods | exact GlobalTheory.CompanionTheory.BZPhiPG.isOpen_eO_rightPeriods | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.isOpen_eO_rightPeriods <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqSign
noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.LocalThetaTranslation

theorem phi_transpose (n : ℕ) (R : Type) [CommRing R] :
    (GlobalTheory.Tw.Phi n R)ᵀ = ((-1 : R) ^ (n + 1)) • GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + j + 1 = n
  · have h' : (j : ℕ) + i + 1 = n := by omega
    rw [if_pos h, if_pos h', ← pow_add]
    have e : n + 1 + (i : ℕ) = j + 2 * ((i : ℕ) + 1) := by omega
    rw [e, pow_add, pow_mul]
    simp
  · have h' : ¬ (j : ℕ) + i + 1 = n := by omega
    rw [if_neg h, if_neg h']
    simp

theorem phi_map (n : ℕ) {R : Type} [CommRing R] (c : R →+* R) : (GlobalTheory.Tw.Phi n R).map c = GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_mul_self (n : ℕ) (R : Type) [CommRing R] :
    GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R = ((-1 : R) ^ (n + 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h := Phi_mul_transpose n R
  rw [phi_transpose, Matrix.mul_smul] at h
  have e : ((-1 : R) ^ (n + 1)) * ((-1 : R) ^ (n + 1)) = 1 := by
    rw [← mul_pow]; simp
  rw [← h, smul_smul, e, one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_conj_eq_sign (n : ℕ) : ∃ s : E, s ≠ 0 ∧ conjE E s = (-1 : E) ^ (n + 1) * s := by
  rcases neg_one_pow_eq_or E (n + 1) with h | h
  · exact ⟨1, one_ne_zero, by rw [h, map_one, one_mul]⟩
  · have hx : ∃ x : E, conjE E x ≠ x := by
      by_contra hc
      push Not at hc
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext hc)
    obtain ⟨x, hx⟩ := hx
    have hcc : conjE E (conjE E x) = x := IsCMField.complexConj_apply_apply E x
    refine ⟨x - conjE E x, sub_ne_zero.2 hx.symm, ?_⟩
    rw [h, map_sub, hcc]
    ring


omit [NumberField E] [IsCMField E] in
theorem scalar_val {n : ℕ} (t : Eˣ) :
    (GeneralLinearGroup.scalar (Fin n) t).val = (t : E) • (1 : Matrix (Fin n) (Fin n) E) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [GeneralLinearGroup.scalar]
  · simp [GeneralLinearGroup.scalar, h]


omit [NumberField E] [IsCMField E] in
theorem scalar_commute {n : ℕ} (t : Eˣ) (g : GL (Fin n) E) :
    GeneralLinearGroup.scalar (Fin n) t * g = g * GeneralLinearGroup.scalar (Fin n) t := by
  apply Units.ext
  simp only [Units.val_mul, scalar_val]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem thetaE_phiU (n : ℕ) : (thetaE E n (PhiU n E)).val = GlobalTheory.Tw.Phi n E := by
  change ((((PhiU n E)⁻¹).val).map (conjE E))ᵀ = _
  rw [phiU_inv_val, Matrix.transpose_map, Matrix.transpose_transpose, phi_map]

theorem thetaE_scalar {n : ℕ} (t : Eˣ) :
    (thetaE E n (GeneralLinearGroup.scalar (Fin n) t)).val =
      (conjE E (t : E))⁻¹ • (1 : Matrix (Fin n) (Fin n) E) := by
  change ((((GeneralLinearGroup.scalar (Fin n) t)⁻¹).val).map (conjE E))ᵀ = _
  rw [← map_inv, scalar_val]
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · have h' : j ≠ i := fun e => h e.symm
    simp [h, h']

theorem translEx : TranslEx := by
  intro E _ _ _ n
  obtain ⟨s, hs, hc⟩ := exists_conj_eq_sign (E := E) n
  have hcs : conjE E s ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hs
  refine ⟨GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E, ?_, ?_⟩
  · intro g
    have h1 : thE E n g = PhiU n E * thetaE E n g * (PhiU n E)⁻¹ := thetaGL_eq n E _ g
    rw [h1]
    have h2 := scalar_commute (Units.mk0 s hs) (PhiU n E * thetaE E n g * (PhiU n E)⁻¹)
    have h3 : GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E * thetaE E n g *
        (GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * (PhiU n E * thetaE E n g * (PhiU n E)⁻¹) *
          (GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs))⁻¹ := by
      group
    rw [h3, h2, mul_inv_cancel_right]
  · apply Units.ext
    rw [map_mul, Units.val_mul, Units.val_mul, Units.val_mul, thetaE_phiU, thetaE_scalar, scalar_val, phiU_val]
    simp only [Units.val_mk0, Units.val_one]
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      phi_mul_self, smul_smul, smul_smul, hc]
    have hp : ((-1 : E) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    have : s * (((-1 : E) ^ (n + 1)) * s)⁻¹ * ((-1 : E) ^ (n + 1)) = 1 := by
      field_simp
    rw [this, one_smul]

end GlobalTheory.CompanionTheory.LocalThetaTranslation
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylConjParabolicProj
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylConjParabolicProj
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.EtaConj

open GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_val {a b : ℕ} (e : a = b) (m : Mir k a) (x y : Fin (b + 1)) :
    ((castM k e m : Mir k b) : GL (Fin (b + 1)) k).val x y =
      (m : GL (Fin (a + 1)) k).val (Fin.cast (by omega) x) (Fin.cast (by omega) y) := by
  subst e
  rfl

theorem piPerm_cast (i t : ℕ) (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    piPerm i t (Fin.cast (by omega) (ePG i (t + 1) s)) = eGP (i + 1) t s := by
  show eGP (i + 1) t ((ePG i (t + 1)).symm (Fin.cast (by omega) (Fin.cast (by omega) (ePG i (t + 1) s)))) = _
  simp

theorem conj_entry (i t : ℕ) (r : GL (Fin ((i + 1) + t + 1)) k) (x y : Fin ((i + 1) + t + 1)) :
    (wGL k i t * r * (wGL k i t)⁻¹).val (piPerm i t x) (piPerm i t y) = r.val x y := by
  show (Equiv.Perm.permMatrix k (piPerm i t)⁻¹ * r.val * Equiv.Perm.permMatrix k (piPerm i t)) _ _ = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]

theorem conj_block (i t : ℕ) (h : Mir k (i + (t + 1))) (s s' : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    (wGL k i t * ((castM k (by omega) h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val
        (eGP (i + 1) t s) (eGP (i + 1) t s') =
      (h : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) s') := by
  rw [← piPerm_cast, ← piPerm_cast, conj_entry, castM_val]
  rfl

theorem eta_val (i t : ℕ) (m : Mir k ((i + 1) + t)) (x y : Fin ((i + 1) + t + 1 + 1)) :
    ((wEl k i t * sEmb k ((i + 1) + t) m * (wEl k i t)⁻¹ : Mir k ((i + 1) + t + 1)) :
        GL (Fin ((i + 1) + t + 1 + 1)) k).val x y =
      glEmbMat k ((i + 1) + t + 1) (wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val x y := by
  have e : wEl k i t * sEmb k ((i + 1) + t) m * (wEl k i t)⁻¹ =
      levi k _ (wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹) := by
    simp only [map_mul, map_inv]
    rfl
  rw [e]
  rfl

theorem eta_mem (i t : ℕ) (h : HPG k i (t + 1)) :
    wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈
      HPG k (i + 1) (t + 1) := by
  have hh := mem_parab_iff.1 (show ((h : Mir k (i + (t + 1))) : GL (Fin (i + (t + 1) + 1)) k) ∈ parab k (ePG i (t + 1)) from h.2)
  show ((wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ :
    Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1))
  rw [mem_parab_iff]
  intro x y b a hxy
  cases x <;> cases y <;> first | exact absurd hxy (by decide) | skip
  refine (eta_val i t _ _ _).trans ?_
  rw [ePG_true_eq]
  induction a using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    exact glEmbMat_cl k _ _ _
  | cast a =>
    rw [ePG_false_castSucc, glEmbMat_cc, conj_block]
    exact hh true false b a hxy

theorem eta_mem_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i (t + 1)),
  ∃ hη : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈ HPG k (i + 1) (t + 1),
    pgProj k (i + 1) (t + 1) ⟨_, hη⟩ = (sEmb k i (pgProj k i (t + 1) h).1, (pgProj k i (t + 1) h).2) := by
  intro k _ _ _ _ i t h
  refine ⟨eta_mem i t h, ?_⟩
  have hent : ∀ x z : Fin ((i + 1) + t + 1 + 1),
      ((hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩ : parab k (ePG (i + 1) (t + 1))) :
        GL (Fin ((i + 1) + (t + 1) + 1)) k).val x z =
        glEmbMat k ((i + 1) + t + 1) (wGL k i t * ((castM k (by omega) (h : Mir k (i + (t + 1))) : Mir k ((i + 1) + t)) :
          GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val x z :=
    fun x z => eta_val i t _ x z
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (leviProj k (ePG (i + 1) (t + 1)) (hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩) false).val a b =
      glEmbMat k (i + 1) (leviProj k (ePG i (t + 1)) (hpgIncl k i (t + 1) h) false).val a b
    rw [leviProj_apply, hent]
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last]
        exact (glEmbMat_ll k _ _).trans (glEmbMat_ll k _ _).symm
      | cast b =>
        rw [ePG_false_last, ePG_false_castSucc]
        exact (glEmbMat_lc k _ _ _).trans (glEmbMat_lc k _ _ _).symm
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last, ePG_false_castSucc]
        exact (glEmbMat_cl k _ _ _).trans (glEmbMat_cl k _ _ _).symm
      | cast b =>
        rw [ePG_false_castSucc, ePG_false_castSucc, glEmbMat_cc, glEmbMat_cc, leviProj_apply, conj_block]
        rfl
  · apply Units.ext
    ext a b
    show (leviProj k (ePG (i + 1) (t + 1)) (hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩) true).val a b =
      (leviProj k (ePG i (t + 1)) (hpgIncl k i (t + 1) h) true).val a b
    rw [leviProj_apply, hent, ePG_true_eq, ePG_true_eq, glEmbMat_cc, leviProj_apply, conj_block]
    rfl

end GlobalTheory.CompanionTheory.BZPhiPG.EtaConj

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylConjParabolicProjStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_conj_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i (t + 1)),
  ∃ hη : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈ HPG k (i + 1) (t + 1),
    pgProj k (i + 1) (t + 1) ⟨_, hη⟩ = (sEmb k i (pgProj k i (t + 1) h).1, (pgProj k i (t + 1) h).2) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.EtaConj.eta_mem_proj | exact GlobalTheory.CompanionTheory.BZPhiPG.EtaConj.eta_mem_proj | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.EtaConj.eta_mem_proj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialFiniteAdeles
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.TwistCent

theorem map_thetaR {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map f g) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, thetaR_val, thetaR_val, ← map_inv]
  simp only [Matrix.transpose_apply, Matrix.map_apply, GeneralLinearGroup.map_apply, h]

theorem map_phiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  simp only [GeneralLinearGroup.map_apply, phiU_val, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem map_thetaGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaGL n c g) = thetaGL n c' (GeneralLinearGroup.map f g) := by
  rw [thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, map_phiU, map_thetaR f c c' h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thF_ratF (g : GL (Fin n) E) : thF E n (ratF E n g) = ratF E n (thE E n g) :=
  (map_thetaGL (algebraMap E (Af E)) _ _
    (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) n g).symm

theorem nontrivial_finiteAdeles : Nontrivial (Af E) := by
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal (𝓞 E)
  let v₀ : HeightOneSpectrum (𝓞 E) :=
    ⟨m₀, hm₀.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm₀ (RingOfIntegers.not_isField E)⟩
  exact ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x : Af E => x v₀) h)⟩⟩

theorem ratF_injective : Function.Injective (ratF E n) := by
  haveI : Nontrivial (Af E) := nontrivial_finiteAdeles
  intro g h e
  apply Units.ext
  ext i j
  have := congrArg (fun x : GL (Fin n) (Af E) => x.val i j) e
  exact (algebraMap E (Af E)).injective this

theorem pFin_ratGL (g : GL (Fin n) E) : GeneralLinearGroup.map (pFin E) (ratGL E n g) = ratF E n g := by
  apply Units.ext
  ext i j
  rfl

theorem cV_ratGL (v : InfinitePlace E) (g : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n g) = GeneralLinearGroup.map v.embedding g := by
  apply Units.ext
  ext i j
  exact pInf_algebraMap (g.val i j) v

theorem mem_twCent_iff {u : GL (Fin n) E} (hu : IsTransl u) (g d : GL (Fin n) E) :
    g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d ↔ g * (d * u⁻¹) = d * u⁻¹ * thE E n g := by
  rw [PositivityTheory.Rg.Tf.Loc.mem_twCent, hu.1 g]
  constructor
  · intro h
    have h' : g * d = d * thetaE E n g := by
      calc g * d = g * (g⁻¹ * d * thetaE E n g) := by rw [h]
        _ = d * thetaE E n g := by group
    calc g * (d * u⁻¹) = g * d * u⁻¹ := by group
      _ = d * thetaE E n g * u⁻¹ := by rw [h']
      _ = d * u⁻¹ * (u * thetaE E n g * u⁻¹) := by group
  · intro h
    have h' : g * d = d * thetaE E n g := by
      calc g * d = g * (d * u⁻¹) * u := by group
        _ = d * u⁻¹ * (u * thetaE E n g * u⁻¹) * u := by rw [h]
        _ = d * thetaE E n g := by group
    calc g⁻¹ * d * thetaE E n g = g⁻¹ * (d * thetaE E n g) := by group
      _ = g⁻¹ * (g * d) := by rw [h']
      _ = d := by group

theorem mem_twCent_iff_ratF {u : GL (Fin n) E} (hu : IsTransl u) (g d : GL (Fin n) E) :
    g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d ↔
      ratF E n g * ratF E n (d * u⁻¹) = ratF E n (d * u⁻¹) * thF E n (ratF E n g) := by
  rw [mem_twCent_iff hu, thF_ratF, ← map_mul, ← map_mul]
  exact ratF_injective.eq_iff.symm

theorem map_mem_twCent (v : InfinitePlace E) {g d : GL (Fin n) E}
    (h : g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d) :
    GeneralLinearGroup.map v.embedding g ∈
      PositivityTheory.Rg.Tf.Loc.twCent (thetaR (starRingEnd ℂ) n) (GeneralLinearGroup.map v.embedding d) := by
  have h' : g⁻¹ * d * thetaE E n g = d := h
  rw [PositivityTheory.Rg.Tf.Loc.mem_twCent]
  rw [← map_thetaR v.embedding (conjE E) (starRingEnd ℂ)
    (fun x => IsCMField.complexEmbedding_complexConj E v.embedding x) n g, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ h'

theorem centEq : CentEq := by
  intro E _ _ _ a b u₁ u₂ h₁ h₂ d₁ d₂
  refine ⟨fun y => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨⟨⟨g₁, g₂⟩, rfl⟩, hc⟩
    have hc' := Prod.ext_iff.1 hc
    refine ⟨(ratGL E a g₁, ratGL E b g₂), ?_, ?_⟩
    · exact ⟨⟨g₁, (mem_twCent_iff_ratF h₁ g₁ d₁).2 hc'.1, rfl⟩, ⟨g₂, (mem_twCent_iff_ratF h₂ g₂ d₂).2 hc'.2, rfl⟩⟩
    · exact Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
  · rintro ⟨⟨γ₁, γ₂⟩, ⟨⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, rfl⟩⟩, rfl⟩
    have e : (comps (ratGL E a g₁, ratGL E b g₂)).2 = (ratF E a g₁, ratF E b g₂) :=
      Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
    rw [e]
    exact ⟨⟨(g₁, g₂), rfl⟩, Prod.ext ((mem_twCent_iff_ratF h₁ g₁ d₁).1 hg₁) ((mem_twCent_iff_ratF h₂ g₂ d₂).1 hg₂)⟩
  · rintro ⟨γ₁, γ₂⟩ ⟨⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, rfl⟩⟩
    refine ⟨fun h => ?_, fun v => ?_⟩
    · have e : (comps (ratGL E a g₁, ratGL E b g₂)).2 = (ratF E a g₁, ratF E b g₂) :=
        Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
      rw [e] at h
      have e₁ : g₁ = 1 := ratF_injective ((congrArg Prod.fst h).trans (map_one _).symm)
      have e₂ : g₂ = 1 := ratF_injective ((congrArg Prod.snd h).trans (map_one _).symm)
      subst e₁ e₂
      exact Prod.ext (map_one _) (map_one _)
    · constructor
      · show GeneralLinearGroup.map (cV v) (ratGL E a g₁) ∈ _
        rw [cV_ratGL]
        exact map_mem_twCent v hg₁
      · show GeneralLinearGroup.map (cV v) (ratGL E b g₂) ∈ _
        rw [cV_ratGL]
        exact map_mem_twCent v hg₂

end GlobalTheory.CompanionTheory.TwistCent

end
end
