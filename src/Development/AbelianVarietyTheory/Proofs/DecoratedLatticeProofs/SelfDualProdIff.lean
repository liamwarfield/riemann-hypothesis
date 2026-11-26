module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionTypingsCompare
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModules
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC

noncomputable section

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

theorem eq_of_test_haar {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {κ P : Measure V} {χ : V → V → ℂ}
    (hκ : SelfDual κ χ) (hP : P.IsAddHaarMeasure) (Φ : V → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ) (hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂P) P) (z : V)
    (h1 : ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P = Φ (-z)) (hz : Φ (-z) ≠ 0) : κ = P := by
  have := hκ.1
  have e : κ = Measure.addHaarScalarFactor κ P • P := Measure.isAddLeftInvariant_eq_smul κ P
  set c : NNReal := Measure.addHaarScalarFactor κ P with hcdef
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂κ = (c : ℂ) * ∫ x, Φ x * χ x y ∂P := by
    intro y
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hI' : Integrable (fun y => ∫ x, Φ x * χ x y ∂κ) κ := by
    simp only [hT]
    rw [e]
    exact (hI.const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := hκ.2 Φ hc hs hI' z
  simp only [hT] at h2
  rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h2
  have h3 : ∫ y, ((c : ℂ) * ∫ x, Φ x * χ x y ∂P) * χ y z ∂P =
      (c : ℂ) * ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [h3, h1, ← mul_assoc] at h2
  have h4 : ((c : ℂ)) * (c : ℂ) = 1 := mul_right_cancel₀ hz (by rw [h2, one_mul])
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have h7 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h7
  rw [e, h6, one_smul]

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrdLEqNegLog
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.AbsInert

theorem ordL_eq_neg_log {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {y : L}
    (hy : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ))) : ordL y = -WithZero.log (Valued.v y) := by
  unfold ordL
  rw [dite_eq_right hy, WithZero.toAdd_unzero_eq_log]

theorem absEv_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV F v : ℝ) ^ (-(2 * ordL (toCompl h x.1))) := by
  intro F E _ _ _ _ _ σ hσ v w h hw x

  set N : Fv F v := Algebra.norm (Fv F v) x.1 with hNdef
  set z : w.adicCompletion E := toCompl h x.1 with hzdef
  have hN0 : N ≠ 0 := ((x.isUnit.map (Algebra.norm (Fv F v))).ne_zero)
  have hz0 : z ≠ 0 := (x.isUnit.map (toCompl h)).ne_zero

  have key := GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x.1
  have key' := congrArg (toCompl h) key
  rw [map_mul] at key'
  have hl : toCompl h (algebraMap (Fv F v) (Fv F v ⊗[F] E) N) = GlobalTheory.LFun.complMap h N := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [hl] at key'

  let c : w.adicCompletion E →+* w.adicCompletion E :=
    (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp
      (((sigR (Fv F v) σ : Fv F v ⊗[F] E →+* Fv F v ⊗[F] E)).comp (GlobalTheory.LFun.InertChart.complEquiv hw h).symm.toRingHom)
  have he : ∀ t, GlobalTheory.LFun.InertChart.complEquiv hw h t = toCompl h t := fun _ => rfl
  have hs : (GlobalTheory.LFun.InertChart.complEquiv hw h).symm z = x.1 := by
    rw [RingEquiv.symm_apply_eq, he]
  have hcz : c z = toCompl h (sigR (Fv F v) σ x.1) := by
    show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) = _
    rw [hs, he]
  have hc : GlobalTheory.LFun.IsConjAt σ h c := by
    unfold GlobalTheory.LFun.IsConjAt
    intro t
    show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (toCompl h t))) = _
    rw [← he t, RingEquiv.symm_apply_apply, he]

  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv hσ hw hc
  have hvc : Valued.v (toCompl h (sigR (Fv F v) σ x.1)) = Valued.v z := by
    rw [← hcz]
    exact hU.2.1 z

  have he1 : w.asIdeal.ramificationIdx (𝓞 F) = 1 :=
    GlobalTheory.LFun.isUnram_iff.mp (GlobalTheory.LFun.isUnram_of_isInertAt hw) w h
  have hvN : Valued.v N = Valued.v z ^ 2 := by
    have hv := GlobalTheory.LFun.valued_complMap h hN0
    rw [he1, pow_one, key', map_mul, hvc] at hv
    rw [sq]
    exact hv.symm
  have hz' : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
  have hN' : Valued.v N ≠ 0 := (Valuation.ne_zero_iff _).mpr hN0

  rw [GlobalTheory.Doubling.absEv_apply, coe_nnnorm]
  show ‖N‖ = _
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hN',
    hvN, WithZero.log_pow, ordL_eq_neg_log (y := toCompl h x.1) hz']
  have hq : ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) = (qV F v : ℝ) := by simp [qV]
  rw [NNReal.coe_zpow, hq]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.AbsInert

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInert
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInert
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.LFun

theorem ideleAt_eq_locIdele_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w)
    (x : (Fv F v ⊗[F] E)ˣ) :
    ideleAt F E v x = locIdele F w (Units.map (toCompl h).toMonoidHom x) := by
  refine eq_locIdele ?_ ?_
  · exact map_extUnit_zero (fstA F) (inFin v) (inFin_mul v) (fun _ => rfl) x
  · refine FiniteAdeleRing.ext _ fun u => ?_
    rw [finAdEquiv_apply rfl]
    have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F (u.under (𝓞 F))) (AlgHom.id F E)
        (finTens F E (ideleAt F E v x : AF F ⊗[F] E)) = (unitFin F E (u.under (𝓞 F)) (ideleAt F E v x) : Fv _ _ ⊗[F] E) := by
      change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) _) = _
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
      rfl
    rw [e]
    by_cases hu : u.under (𝓞 F) = v
    · obtain rfl : u = w := (InertChart.under_eq_iff hw u).1 hu
      subst h
      rw [unitFin_ideleAt_self]
      exact (finSingle_self u _).symm
    · rw [unitFin_ideleAt_ne hu, Units.val_one, map_one]
      exact (finSingle_ne (fun e : u = w => hu (e ▸ h)) _).symm

theorem charAt_eq_locChar_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) := by
  intro F E _ _ _ _ _ χ v w h hw x
  show ((χ (ideleAt F E v x) : Circle) : ℂ) = ((Circle.toUnits (χ (locIdele F w _)) : ℂˣ) : ℂ)
  rw [GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw x]
  rfl

end GlobalTheory.LFun
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInertStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) := by
  first | exact @GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt | exact GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt | (intros; apply GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqMulOfSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqMulOfSplit
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem charAt_eq_locChar_mul_locChar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) * (locChar χ w' (Units.map (toCompl h').toMonoidHom x) : ℂˣ) := by
  intro F E _ _ _ _ _ χ v w h w' h' hne hall x
  have key : ideleAt F E v x = locIdele F w (Units.map (toCompl h).toMonoidHom x) *
      locIdele F w' (Units.map (toCompl h').toMonoidHom x) := by
    refine Units.ext (tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun u => ?_)))
    · rw [Units.val_mul, map_mul, infTens_locIdele, infTens_locIdele, mul_one]
      exact map_extUnit_zero (fstA F) _ _ (fun a => rfl) x
    · rw [Units.val_mul, map_mul (finTens F E), map_mul, finTens_locIdele, finTens_locIdele]
      have hc : ∀ u' : HeightOneSpectrum (𝓞 F), Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u') (AlgHom.id F E)
          (finTens F E (ideleAt F E v x)) = (unitFin F E u' (ideleAt F E v x) : Fv F u' ⊗[F] E) := fun u' => by
        change ((Algebra.TensorProduct.map _ _).comp (Algebra.TensorProduct.map _ _)) _ = _
        rw [← Algebra.TensorProduct.map_comp]
        rfl
      change _ = Neutral.B1.finiteSingle E w (Units.map (toCompl h).toMonoidHom x) u *
        Neutral.B1.finiteSingle E w' (Units.map (toCompl h').toMonoidHom x) u
      by_cases hu : u.under (𝓞 F) = v
      · rw [finAdEquiv_apply hu, hc, unitFin_ideleAt_self]
        rcases (hall u).1 hu with rfl | rfl
        · rw [finSingle_self, finSingle_ne hne, mul_one]
          rfl
        · rw [finSingle_self, finSingle_ne (Ne.symm hne), one_mul]
          rfl
      · rw [finAdEquiv_apply rfl, hc, unitFin_ideleAt_ne hu, Units.val_one, map_one,
          finSingle_ne (fun e => hu (by rw [e]; exact h)), finSingle_ne (fun e => hu (by rw [e]; exact h')), mul_one]
  show ((χ (ideleAt F E v x) : Circle) : ℂ) = _
  rw [key, map_mul]
  rfl

end GlobalTheory.LFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqMulOfSplitStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_mul_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) * (locChar χ w' (Units.map (toCompl h').toMonoidHom x) : ℂˣ) := by
  first | exact @GlobalTheory.LFun.charAt_eq_locChar_mul_locChar | exact GlobalTheory.LFun.charAt_eq_locChar_mul_locChar | (intros; apply GlobalTheory.LFun.charAt_eq_locChar_mul_locChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoundLatLoc
noncomputable section

namespace GlobalTheory.LocalLatticeBound

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem abs_zero_le (v : HeightOneSpectrum (𝓞 F)) (C : ℝ≥0) : absFin F v (0 : Fv F v ⊗[F] E) ≤ C :=
  (absFin_le_iff F v).2 fun τ => by rw [map_zero, (absBar_eq_zero F v).2 rfl]; exact zero_le

theorem abs_neg_le (v : HeightOneSpectrum (𝓞 F)) {C : ℝ≥0} {y : Fv F v ⊗[F] E} (h : absFin F v y ≤ C) :
    absFin F v (-y) ≤ C :=
  (absFin_le_iff F v).2 fun τ => by rw [map_neg, absBar_neg]; exact (le_absFin F v τ y).trans h

theorem abs_int_mul_le (v : HeightOneSpectrum (𝓞 F)) {C : ℝ≥0} {c y : Fv F v ⊗[F] E} (hc : c ∈ intLoc F E v)
    (h : absFin F v y ≤ C) : absFin F v (c * y) ≤ C :=
  (absFin_mul_le F v c y).trans ((mul_le_mul' (absFin_le_one_of_mem_intLoc hc) h).trans_eq (one_mul C))

theorem exists_bound_rat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ C : ℝ≥0, ∀ x ∈ L, ∀ i, absFin F v ((1 : Fv F v) ⊗ₜ[F] x i) ≤ C := by
  obtain ⟨S, rfl⟩ := hL
  refine ⟨S.sup fun s => Finset.univ.sup fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i), fun x hx i => ?_⟩
  induction hx using Submodule.span_induction with
  | mem s hs =>
    exact (Finset.le_sup (f := fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i)) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun s : Fin n → E => Finset.univ.sup fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i)) hs)
  | zero => rw [Pi.zero_apply, TensorProduct.tmul_zero]; exact abs_zero_le v _
  | add x y _ _ hx hy =>
    rw [Pi.add_apply, TensorProduct.tmul_add]
    exact (absFin_add_le F v _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    have e : (1 : Fv F v) ⊗ₜ[F] (c • x) i = ((1 : Fv F v) ⊗ₜ[F] (c : E)) * ((1 : Fv F v) ⊗ₜ[F] x i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl
    rw [e]
    exact abs_int_mul_le v (tmul_mem_intLoc (one_mem _) c) hx

theorem exists_bound_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i : Fin n, absFin F v (y i) ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_rat L (Submodule.IsLattice.fg (A := E) L) v
  refine ⟨C, fun y hy i => ?_⟩
  change y ∈ AddSubgroup.closure _ at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have e : a ⊗ₜ[F] x i = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] x i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]; simp
    change absFin F v (a ⊗ₜ[F] x i) ≤ C
    rw [e]
    exact abs_int_mul_le v (tmul_mem_intLoc ha 1) (hC x hx i)
  | zero => exact abs_zero_le v C
  | add y z _ _ hy hz => exact (absFin_add_le F v _ _).trans (max_le hy hz)
  | neg y _ hy => exact abs_neg_le v hy

end GlobalTheory.LocalLatticeBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantSphericalCoefficientEqZeroOrZonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantSphericalCoefficientEqZeroOrZonal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.ZonalCoeff

open Formalism.UG

theorem apply_heckeVec {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}
    (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Formalism.UG.Hecke ℂ K) (ρ : Representation ℂ G V) (x : V)
    (l : V →ₗ[ℂ] ℂ) : l (GlobalTheory.LFun.heckeVec ρ K h x) = ∑ᶠ c : G ⧸ K, h c.out * l (ρ c.out x) :=
  (l.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK hh ρ x)).trans (finsum_congr fun c => by simp)

theorem eq_zero_of_doset_sum {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K) {w : G → ℂ}
    (hw : IsBiInv K w) (g : G) (e : ∑ᶠ c : G ⧸ K, dosetInd ℂ K g c.out * w c.out = 0) : w g = 0 := by
  classical
  have hfin := Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem G K ℂ g).2
  have hmem : ∀ c ∈ hfin.toFinset, c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K := fun c hc => by
    by_contra hn
    exact (hfin.mem_toFinset.1 hc) (Set.indicator_of_notMem hn _)
  have h1 : ∀ c ∈ hfin.toFinset, dosetInd ℂ K g c.out * w c.out = w g := fun c hc => by
    obtain ⟨a, ha, b, hb, e'⟩ := DoubleCoset.mem_doubleCoset.1 (hmem c hc)
    rw [dosetInd, Set.indicator_of_mem (hmem c hc), Pi.one_apply, one_mul, e']
    exact hw ⟨a, ha⟩ ⟨b, hb⟩ g
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ fun c hc =>
      hfin.mem_toFinset.2 (left_ne_zero_of_mul hc),
    Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul] at e
  refine (mul_eq_zero.1 e).resolve_left (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), ?_⟩))
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  refine hfin.mem_toFinset.2 ?_
  change dosetInd ℂ K g _ ≠ 0
  rw [dosetInd, Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩)]
  exact one_ne_zero

theorem coeff_zero_or_zonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x = 0 → ∀ g, ℓ (ρ g x) = 0) ∧ (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α fun g => ℓ (ρ g x) / ℓ x) := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ x α hx l hl
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have hbi : IsBiInv (KU σ n) fun g => l (ρ g x) := fun a b g => by
    beta_reduce
    rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ b.2, hl _ a.2]
  refine ⟨fun h0 g => eq_zero_of_doset_sum hK hbi g ?_, fun h0 => ⟨fun a b g => ?_, ?_, fun h hh => ?_⟩⟩
  · have hm := Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g
    rw [← apply_heckeVec hK hm, hx.2.2 _ hm, map_smul, h0, smul_zero]
  · exact congrArg (· / l x) (hbi a b g)
  · simpa using div_self h0
  · have e := apply_heckeVec hK hh ρ x ((l x)⁻¹ • l)
    rw [hx.2.2 h hh, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ h0, mul_one] at e
    rw [e]
    exact finsum_congr fun c => by simp [div_eq_inv_mul]

end GlobalTheory.ZonalCoeff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantSphericalCoefficientEqZeroOrZonalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x = 0 → ∀ g, ℓ (ρ g x) = 0) ∧ (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α fun g => ℓ (ρ g x) / ℓ x) := by
  first | exact @GlobalTheory.ZonalCoeff.coeff_zero_or_zonal | exact GlobalTheory.ZonalCoeff.coeff_zero_or_zonal | (intros; apply GlobalTheory.ZonalCoeff.coeff_zero_or_zonal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorWeylModuleMapsInjectiveOnPureSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorWeylModuleMapsInjectiveOnPureSpan
open Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.TenInj

noncomputable def tenMap {ι : Type} [Fintype ι] {n : ℕ} {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) :
    (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × Fin n × Fin n) ℂ)).compLinearMap
    (fun τ => (MvPolynomial.rename (Prod.mk τ)).toLinearMap ∘ₗ j τ))

theorem tenMap_tprod {ι : Type} [Fintype ι] {n : ℕ} {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (x : ∀ τ, V τ) :
    tenMap j (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  unfold tenMap ten
  rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rfl

theorem nfAll_zero_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam 0 q = 0 := by
  have h := GlobalTheory.TenTypes.nfAll_smul_left lam 0 0 q
  simpa using h

theorem main : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ι → ℕ) (b : ∀ τ, Module.Basis (Fin (d τ)) ℂ (V τ)), (∀ τ ξ, j τ ξ ∈ delSq ℂ n (lam τ)) → (∀ τ, ∀ p ∈ delSq ℂ n (lam τ), ∃ ξ, j τ ξ = p) → (∀ τ a a', normFock (lam τ) (j τ (b τ a)) (j τ (b τ a')) = if a = a' then 1 else 0) → ∃ Jt : (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, Function.Injective Jt ∧ LinearMap.range Jt = CSpan lam ∧ ∀ x : (∀ τ, V τ), Jt (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  intro ι _ n lam V _ _ j d b hin hon hortho
  refine ⟨tenMap j, ?_, ?_, tenMap_tprod j⟩
  ·
    let B := Basis.piTensorProduct b
    have hB : ∀ i, B i = PiTensorProduct.tprod ℂ (fun τ => b τ (i τ)) := fun i => Basis.piTensorProduct_apply b i
    obtain ⟨hprod, -, -⟩ := GlobalTheory.FockTen.nfAll_ten ι n lam
    have hpair : ∀ i i', nfAll lam (tenMap j (B i)) (tenMap j (B i')) = if i = i' then 1 else 0 := by
      intro i i'
      rw [hB, hB, tenMap_tprod, tenMap_tprod, hprod]
      simp_rw [hortho]
      by_cases h : i = i'
      · subst h; simp
      · rw [if_neg h]
        obtain ⟨τ, hτ⟩ : ∃ τ, i τ ≠ i' τ := by
          by_contra hc; push_neg at hc; exact h (funext hc)
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)
    have hcoord : ∀ i' x, nfAll lam (tenMap j x) (tenMap j (B i')) = B.coord i' x := by
      intro i'
      let L : (⨂[ℂ] τ, V τ) →ₗ[ℂ] ℂ :=
        { toFun := fun x => nfAll lam (tenMap j x) (tenMap j (B i'))
          map_add' := fun x y => by rw [map_add (f := _), GlobalTheory.TenTypes.nfAll_add_left]
          map_smul' := fun c x => by rw [map_smul, GlobalTheory.TenTypes.nfAll_smul_left]; rfl }
      have hL : L = B.coord i' := by
        refine B.ext fun i => ?_
        show nfAll lam (tenMap j (B i)) (tenMap j (B i')) = B.coord i' (B i)
        rw [hpair, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      intro x
      exact LinearMap.congr_fun hL x
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine B.ext_elem fun i' => ?_
    rw [map_zero, Finsupp.zero_apply, ← Module.Basis.coord_apply, ← hcoord, hx, nfAll_zero_left]
  ·
    rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    unfold CSpan
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨fun τ => j τ (x τ), fun τ => hin τ _, tenMap_tprod j x⟩
    · rintro ⟨f, hf, rfl⟩
      choose ξ hξ using fun τ => hon τ (f τ) (hf τ)
      refine ⟨PiTensorProduct.tprod ℂ ξ, ⟨ξ, rfl⟩, ?_⟩
      rw [tenMap_tprod]
      congr 1
      funext τ
      exact hξ τ

end GlobalTheory.TenInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorWeylModuleMapsInjectiveOnPureSpanStatement
open Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_weyl_module_maps_injective_on_pure_span : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ι → ℕ) (b : ∀ τ, Module.Basis (Fin (d τ)) ℂ (V τ)), (∀ τ ξ, j τ ξ ∈ delSq ℂ n (lam τ)) → (∀ τ, ∀ p ∈ delSq ℂ n (lam τ), ∃ ξ, j τ ξ = p) → (∀ τ a a', normFock (lam τ) (j τ (b τ a)) (j τ (b τ a')) = if a = a' then 1 else 0) → ∃ Jt : (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, Function.Injective Jt ∧ LinearMap.range Jt = CSpan lam ∧ ∀ x : (∀ τ, V τ), Jt (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  first | exact @GlobalTheory.TenInj.main | exact GlobalTheory.TenInj.main | (intros; apply GlobalTheory.TenInj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLatticeFrameAtPlaceDirectSumBlockDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLatticeFrameAtPlaceDirectSumBlockDiagonal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem latAt_sumLat_self {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) :
    latAt w (sumLat finSumFinEquiv L L) = sumLat finSumFinEquiv (latAt w L) (latAt w L) := by
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  have hl0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e (x + y) 0 = pairVec e x 0 + pairVec e y 0 := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hr0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e 0 (x + y) = pairVec e 0 x + pairVec e 0 y := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hls : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e (c • x) 0 = c • pairVec e x 0 := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hrs : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e 0 (c • x) = c • pairVec e 0 x := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hz : pairVec e (0 : Fin n → w.adicCompletion E) 0 = 0 := by
    funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hsplit : ∀ (x y : Fin n → w.adicCompletion E), pairVec e x y = pairVec e x 0 + pairVec e 0 y := by
    intro x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  set φ : (Fin n → E) → (Fin n → w.adicCompletion E) := fun x i => algebraMap E (w.adicCompletion E) (x i)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_sumLat] at hx ⊢
    exact ⟨Submodule.subset_span ⟨_, hx.1, rfl⟩, Submodule.subset_span ⟨_, hx.2, rfl⟩⟩
  · intro z hz'
    rw [← pairVec_eta e z, pairVec_mem_sumLat] at hz'
    rw [← pairVec_eta e z, hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inl i)) := ⟨_, rfl⟩
      have hu' := hz'.1
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e y 0, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨hy, L.zero_mem⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hl0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hls]; exact Submodule.smul_mem _ c hx
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inr i)) := ⟨_, rfl⟩
      have hu' := hz'.2
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e 0 y, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨L.zero_mem, hy⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hr0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hrs]; exact Submodule.smul_mem _ c hx

theorem isFrameAt_sumLat_blkGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (w.adicCompletion E)), IsFrameAt w L a → IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  intro E _ _ w n L a ha y
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  rw [latAt_sumLat_self, ← pairVec_eta e y, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat,
    ← ha, ← ha]
  constructor
  · intro h; exact ⟨fun i => by simpa using h (e (.inl i)), fun i => by simpa using h (e (.inr i))⟩
  · rintro ⟨h1, h2⟩ j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [h1, h2]

end GlobalTheory.LFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLatticeFrameAtPlaceDirectSumBlockDiagonalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLatticeFrameAtPlace_directSum_blockDiagonal : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (w.adicCompletion E)), IsFrameAt w L a → IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  first | exact @GlobalTheory.LFun.isFrameAt_sumLat_blkGL | exact GlobalTheory.LFun.isFrameAt_sumLat_blkGL | (intros; apply GlobalTheory.LFun.isFrameAt_sumLat_blkGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory.CritLevelSize

open Formalism.FourierDecayAlt Finset GlobalTheory.CritLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem num_bound_pow (k m r e : ℕ) (B P ae c ka : ℝ) (hm : m = 2 * r + 2) (he : 2 * e + 40 ≤ m) (hk : 5 ≤ k)
    (hB : (k : ℝ) ^ 40 ≤ B) (hP : B ^ m ≤ P) (ha0 : 0 < ae) (ha : ae ≤ B ^ e) (hc : 1 / 8 ≤ c) (hka0 : 0 < ka)
    (hka : ka ≤ 4) : (k : ℝ) ^ (3 * r) ≤ c * (ka ^ (m - 1))⁻¹ * P / ae := by
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have h1 : ka ^ (m - 1) ≤ (k : ℝ) ^ (m - 1) := pow_le_pow_left₀ hka0.le (by linarith) _
  have h2 : (8 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have h3 : (k : ℝ) ^ (3 * r) * (k : ℝ) ^ (m - 1) * (k : ℝ) ^ 2 ≤ B ^ (m - e) := by
    rw [← pow_add, ← pow_add]
    calc (k : ℝ) ^ (3 * r + (m - 1) + 2) ≤ (k : ℝ) ^ (40 * (m - e)) := pow_le_pow_right₀ (by linarith) (by omega)
      _ = ((k : ℝ) ^ 40) ^ (m - e) := pow_mul _ _ _
      _ ≤ B ^ (m - e) := pow_le_pow_left₀ (by positivity) hB _
  have h4 : B ^ (m - e) * B ^ e = B ^ m := by rw [← pow_add]; congr 1; omega
  have h5 : (k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae ≤ P :=
    calc (k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae
        ≤ (k : ℝ) ^ (3 * r) * (k : ℝ) ^ (m - 1) * (k : ℝ) ^ 2 * B ^ e := by gcongr
      _ ≤ B ^ (m - e) * B ^ e := by gcongr
      _ ≤ P := h4 ▸ hP
  rw [le_div_iff₀ ha0]
  calc (k : ℝ) ^ (3 * r) * ae = 1 / 8 * (ka ^ (m - 1))⁻¹ * ((k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae) := by
        field_simp
    _ ≤ c * (ka ^ (m - 1))⁻¹ * P := by
        gcongr

theorem le_pow_ceil (b B u cb Cu : ℝ) (hcb : 0 < cb) (hb : 1 ≤ b) (hB : b ^ cb ≤ B) (hu : u ≤ b ^ Cu) :
    u ≤ B ^ ⌈max Cu 0 / cb⌉₊ := by
  have hB1 : 1 ≤ B := le_trans (Real.one_le_rpow hb hcb.le) hB
  have hM : 0 ≤ max Cu 0 / cb := div_nonneg (le_max_right _ _) hcb.le
  calc u ≤ b ^ Cu := hu
    _ ≤ b ^ max Cu 0 := Real.rpow_le_rpow_of_exponent_le hb (le_max_left _ _)
    _ = (b ^ cb) ^ (max Cu 0 / cb) := by
        rw [← Real.rpow_mul (by linarith)]; congr 1; field_simp
    _ ≤ B ^ (max Cu 0 / cb) := Real.rpow_le_rpow (by positivity) hB hM
    _ ≤ B ^ ((⌈max Cu 0 / cb⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (Nat.le_ceil _)
    _ = B ^ ⌈max Cu 0 / cb⌉₊ := Real.rpow_natCast _ _


set_option maxHeartbeats 1600000 in
theorem tcrit_low_of_sizes (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hcb : 0 < cb)
    (hCl : 2 * ((⌈max Cu 0 / cb⌉₊ + 4 : ℕ) : ℝ) + 40 ≤ Cl)
    (hVV : ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) :
    UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  rintro ⟨hH, hD, -⟩ u τ
  obtain ⟨-, -, -, -, -, -, hmL, hbD, -, -, -, hg0, -, hg1, -, hbj, -, hu, hv, hDel, hgap, -, -, hClm, -⟩ := hH
  obtain ⟨hvw, -, ha, ha', hl, htop, -⟩ := hD
  set e : ℕ := ⌈max Cu 0 / cb⌉₊ + 4 with he
  have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
  have hCl40 : (40 : ℝ) ≤ Cl := by linarith
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm := GlobalTheory.CritLevel.m_eq D.R
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hmR : (40 : ℝ) ≤ D.R.m := hCl40.trans hClm
  have hme : 2 * e + 40 ≤ D.R.m := by
    have : ((2 * e + 40 : ℕ) : ℝ) ≤ D.R.m := by push_cast; linarith
    exact_mod_cast this
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (by omega) D.R.m_le_f
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  have hlog : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hD1 : (1 : ℝ) ≤ D.s.Del :=
    le_trans (Real.one_le_rpow (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hf) hL)
      (by linarith)) hDel
  set B := bOne D τ 1 with hBdef
  have hB : (D.R.k : ℝ) ^ 40 ≤ B := by
    refine le_trans ?_ ((le_max_left _ _).trans (hbj τ 1 le_rfl (by omega)).1)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hCl40)
  have hBcb : large₂.sc.b ^ cb ≤ B := (le_max_right _ _).trans (hbj τ 1 le_rfl (by omega)).1
  have hk2 : 3 * (D.R.k : ℝ) ≤ B := by
    refine le_trans ?_ hB
    calc 3 * (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hB1 : 1 ≤ B := by linarith
  have hkD : 0 < (D.R.k : ℝ) * D.s.Del := by positivity
  have hBD : 40 * (D.R.m * D.R.k * D.s.Del) ≤ B :=
    le_trans (mul_le_mul_of_nonneg_right hCl40 (by positivity)) (hbD τ 1 le_rfl (by omega))
  have hBD' : 8 * ((D.R.k : ℝ) * D.s.Del) ≤ B := by nlinarith
  have hg : ∀ j, 1 ≤ j → j < D.R.m → bOne D τ j + 1 ≤ bOne D τ (j + 1) := fun j h1 h2 => by
    have h3 := hgap τ j h1 h2
    have h4 : (1 : ℝ) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hn)) (one_le_pow₀ hf)) hL
    linarith
  have hmono : ∀ j, 1 ≤ j → j ≤ D.R.m → B ≤ bOne D τ j := by
    intro j h1
    induction j, h1 using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j h1 ih => intro h2; linarith [ih (by omega), hg j h1 h2]
  set c := GlobalTheory.CritLevel.cfg D u τ with hc
  have hv1 : c.v 1 = vOne D τ 1 := GlobalTheory.CritLevel.cfg_v D u τ le_rfl (by omega)
  have htp : c.top = true ↔ IsTop D τ := by simp [hc, GlobalTheory.CritLevel.cfg]
  have hOk : c.Ok := by
    refine ⟨show 4 ≤ D.R.k by omega, hm2, hD1, (hvw τ _ (by omega) le_rfl).1, ?_, hB1, hg, ?_, fun h => ?_⟩
    · rw [hv1]; exact (hvw τ 1 le_rfl (by omega)).2
    · rw [hv1]; exact ha u τ
    · have := htop τ (htp.1 h)
      exact ⟨this.2, show bTop D τ ≤ B - 3 by linarith [this.1]⟩
  have hSm : c.Small large₂.sc.b := by
    refine ⟨hb, ?_, fun j h1 h2 => ?_, ?_⟩
    · show 4 * (D.R.m : ℝ) * D.R.k * D.s.Del / B ≤ 1 / 10
      rw [div_le_iff₀ (by linarith)]
      linarith
    · have := (hbj τ j h1 h2).2
      rwa [Real.rpow_two] at this
    · show 2 * (D.R.m : ℝ) * Real.log large₂.sc.b / D.R.k ≤ 1 / 10
      rw [hlog, div_le_iff₀ (by linarith)]
      have h1 : (D.R.m : ℝ) * large₂.sc.L ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := by gcongr; nlinarith
      have h2 : 40 * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) := by gcongr
      have h3 : 0 ≤ (D.R.m : ℝ) * large₂.sc.L := by positivity
      linarith
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hgg : 2 * Real.pi ≤ gg D := by
    have h1 : (5 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
      le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
    unfold gg
    nlinarith
  have hV : 0 < VV D τ := mul_pos (D.dsig_pos τ) (prod_pos fun i _ => by positivity)
  have hlow := Final.sz_tcritLower c D.R.rS large₂.sc.b (GlobalTheory.CritLevel.letters D u) D.host.ka D.host.rdE (gg D) (VV D τ) hOk hm hSm
    (GlobalTheory.CritLevel.isWord_letters D u) (by linarith) (by rw [hrd]; unfold Host.ka; field_simp) hgg (by
      show (1 - 1 / 2) * Sz.Vand (D.R.k + D.R.m - 1) c.lam ≤ _
      rw [← GlobalTheory.CritLevel.cfg_lam D u τ, ← hVV]
      linarith)
  change _ * gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * _ / _ ≤
    Sz.Tcrit D.R.k D.R.m _ _ _ _ (Sz.Vand D.R.k _) at hlow
  rw [← GlobalTheory.CritLevel.cfg_u D u τ (hl u τ), ← GlobalTheory.CritLevel.tcrit_eq D (by linarith)] at hlow
  have hg0' : 0 < gg D := by linarith
  have hvone := (hvw τ 1 le_rfl (by omega)).1
  have hBe : B ≤ B ^ e := le_self_pow₀ hB1 (by omega)
  have hae : 0 < c.aeff ∧ c.aeff ≤ B ^ e ∧ 0 ≤ c.vthp ∧ c.vthp ≤ 1 := by
    unfold Sz.Cfg.aeff Sz.Cfg.vthp
    by_cases ht : IsTop D τ
    · rw [if_pos (htp.2 ht), if_pos (htp.2 ht)]
      obtain ⟨t1, t2⟩ := htop τ ht
      have ha0 : 0 < uOne D u τ 1 := by linarith [ha u τ]
      have hbp : 0 < bTop D τ := by linarith
      have hu1 : uOne D u τ 1 ≤ B ^ ⌈max Cu 0 / cb⌉₊ := le_pow_ceil _ _ _ _ _ hcb hb hBcb (hu u τ)
      have hpe : B ^ ⌈max Cu 0 / cb⌉₊ * B ≤ B ^ e := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hB1 (by omega)
      refine ⟨div_pos (mul_pos ha0 hbp) hkD, ?_, ?_, ?_⟩
      · show uOne D u τ 1 * bTop D τ / ((D.R.k : ℝ) * D.s.Del) ≤ B ^ e
        refine (div_le_self (by positivity) (by nlinarith)).trans ?_
        calc uOne D u τ 1 * bTop D τ ≤ B ^ ⌈max Cu 0 / cb⌉₊ * B := by gcongr; linarith
          _ ≤ B ^ e := hpe
      · show 0 ≤ 4 * (D.R.k : ℝ) * D.s.Del / bTop D τ
        positivity
      · show 4 * (D.R.k : ℝ) * D.s.Del / bTop D τ ≤ 1
        rw [div_le_one hbp]
        linarith
    · rw [if_neg (fun h => ht (htp.1 h)), if_neg (fun h => ht (htp.1 h)), hv1]
      have h1 := ha u τ
      have h2 := ha' u τ ht
      refine ⟨?_, ?_, le_rfl, zero_le_one⟩
      · show 0 < uOne D u τ 1 - vOne D τ 1
        linarith
      · show uOne D u τ 1 - vOne D τ 1 ≤ B ^ e
        linarith
  have hc1 : 1 / 8 ≤ Sz.cOne c large₂.sc.b := by
    unfold Sz.cOne
    have h1 := Real.add_one_le_exp (-(2 * c.m * Real.log large₂.sc.b / c.k))
    have h2 := hSm.hmu
    rw [le_div_iff₀ (by linarith [hae.2.2.1])]
    linarith [hae.2.2.2]
  have hP : B ^ D.R.m ≤ c.prodb := by
    have := prod_le_prod₀ (s := Icc 1 D.R.m) (f := fun _ => B) (g := bOne D τ) (fun _ _ => by linarith)
      fun j hj => hmono j (mem_Icc.1 hj).1 (mem_Icc.1 hj).2
    rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel] at this
    exact this
  have hka0 : 0 < D.host.ka := div_pos hpi (by linarith)
  have hka : D.host.ka ≤ 4 := (div_le_self hpi.le hv).trans hpi4
  have hnum := num_bound_pow D.R.k D.R.m D.R.rS e B c.prodb c.aeff _ _ hm hme (by omega) hB hP
    hae.1 hae.2.1 hc1 hka0 hka
  rw [Real.rpow_neg hg0'.le, Real.rpow_natCast, le_inv_mul_iff₀ (by positivity)]
  refine le_trans ?_ hlow
  calc gg D ^ D.R.m * (D.R.k : ℝ) ^ (3 * D.R.rS)
      ≤ gg D ^ D.R.m * (Sz.cOne c large₂.sc.b * (D.host.ka ^ (D.R.m - 1))⁻¹ * c.prodb / c.aeff) := by gcongr
    _ = _ := by ring

end GlobalTheory.CritLevelSize

theorem GlobalTheory.CritLevelSize.tcritLow_sizes : ∀ cb Cu : ℝ, 0 < cb → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cT CT C0 : ℝ), thr ≤ Cl → (∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) → UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro cb Cu hcb
  exact ⟨2 * ((⌈max Cu 0 / cb⌉₊ + 4 : ℕ) : ℝ) + 40, fun D large₂ C' Cl Cg cT CT C0 hCl hVV =>
    GlobalTheory.CritLevelSize.tcrit_low_of_sizes D large₂ C' Cl Cg cb Cu cT CT C0 hcb hCl hVV⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBoundStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_threshold_criticalLevel_lower_bound : ∀ cb Cu : ℝ, 0 < cb → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cT CT C0 : ℝ), thr ≤ Cl → (∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) → UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  first | exact @GlobalTheory.CritLevelSize.tcritLow_sizes | exact GlobalTheory.CritLevelSize.tcritLow_sizes | (intros; apply GlobalTheory.CritLevelSize.tcritLow_sizes <;> assumption)
end
end
