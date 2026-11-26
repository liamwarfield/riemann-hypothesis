module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjScale


open Classical in
noncomputable def forestLift {G : Type} [Group G] {r : ℕ} (Ed : Fin r → Fin r → Prop) (hlt : ∀ i j, Ed i j → i < j)
    (w : Fin r → Fin r → G) (j : Fin r) : G :=
  if h : ∃ i, Ed i j then forestLift Ed hlt w (Classical.choose h) * w (Classical.choose h) j else 1
termination_by j.val
decreasing_by all_goals (try simp_wf); exact hlt _ _ (Classical.choose_spec h)

theorem forestLift_edge {G : Type} [Group G] {r : ℕ} (Ed : Fin r → Fin r → Prop) (hlt : ∀ i j, Ed i j → i < j)
    (huniq : ∀ i i' j, Ed i j → Ed i' j → i = i') (w : Fin r → Fin r → G) {i j : Fin r} (h : Ed i j) :
    (forestLift Ed hlt w i)⁻¹ * forestLift Ed hlt w j = w i j := by
  have hex : ∃ i, Ed i j := ⟨i, h⟩
  have hc : Classical.choose hex = i := huniq _ _ _ (Classical.choose_spec hex) h
  have e : forestLift Ed hlt w j = forestLift Ed hlt w i * w i j := by
    rw [forestLift, dite_eq_left hex, hc]
  rw [e, inv_mul_cancel_left]

theorem symEdge_lt {r : ℕ} (ρ k : ℕ) : ∀ i j : Fin r, symEdge ρ k i j → i < j := by
  intro i j h
  show i.val < j.val
  unfold symEdge at h
  omega

theorem symEdge_uniq {r : ℕ} (ρ k : ℕ) : ∀ i i' j : Fin r, symEdge ρ k i j → symEdge ρ k i' j → i = i' := by
  intro i i' j h h'
  apply Fin.ext
  unfold symEdge at h h'
  omega

theorem scale_conj : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ {r : ℕ} (ρ k : ℕ) (ψ' ψ0 : AddChar κf ℂ), ψ' ≠ 1 → ψ0 ≠ 1 → ∀ a : Fin r → Fin r → κfˣ, ∃ d : Fin r → κfˣ, ∀ u : GL (Fin r) κf, u ∈ unipSym κf r ρ k → ψ' (∑ i, ∑ j, if symEdge ρ k i j then (a i j : κf) * u.val i j else 0) = ψ0 (edgeSum (symEdge ρ k) ((diagGL d)⁻¹ * u * diagGL d)) := by
  intro κf _ _ hF r ρ k ψ' ψ0 h1 h0 a
  let _ : Field κf := hF.toField
  have := Fintype.ofFinite κf
  have hprim : ψ0.IsPrimitive := AddChar.IsPrimitive.of_ne_one h0
  have hinj : Function.Injective ψ0.mulShift := AddChar.to_mulShift_inj_of_isPrimitive hprim
  have hbij : Function.Bijective ψ0.mulShift := by
    classical
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, (AddChar.card_eq).symm⟩
  obtain ⟨c, hc⟩ := hbij.2 ψ'
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h1
    rw [← hc]
    exact AddChar.mulShift_zero ψ0
  let w : Fin r → Fin r → κfˣ := fun i j => Units.mk0 c hc0 * a i j
  refine ⟨forestLift (symEdge ρ k) (symEdge_lt ρ k) w, fun u _ => ?_⟩
  rw [← hc, AddChar.mulShift_apply]
  congr 1
  unfold edgeSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [diagGL_conj_apply]
    have e := congrArg Units.val (forestLift_edge (symEdge ρ k) (symEdge_lt ρ k) (symEdge_uniq ρ k) w h)
    rw [Units.val_mul] at e
    have e2 : (((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) *
        ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf) = c * (a i j : κf) := by
      rw [e]; rfl
    symm
    calc (((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) * u.val i j *
          ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf)
        = ((((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) *
          ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf)) * u.val i j := by ring
      _ = c * ((a i j : κf) * u.val i j) := by rw [e2]; ring
  · rw [mul_zero]

end GlobalTheory.SeeConjScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_conj_edgeSum_addChar_finiteField : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ {r : ℕ} (ρ k : ℕ) (ψ' ψ0 : AddChar κf ℂ), ψ' ≠ 1 → ψ0 ≠ 1 → ∀ a : Fin r → Fin r → κfˣ, ∃ d : Fin r → κfˣ, ∀ u : GL (Fin r) κf, u ∈ unipSym κf r ρ k → ψ' (∑ i, ∑ j, if symEdge ρ k i j then (a i j : κf) * u.val i j else 0) = ψ0 (edgeSum (symEdge ρ k) ((diagGL d)⁻¹ * u * diagGL d)) := by
  first | exact @GlobalTheory.SeeConjScale.scale_conj | exact GlobalTheory.SeeConjScale.scale_conj | (intros; apply GlobalTheory.SeeConjScale.scale_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPowerDetAbsRealDiagonalTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPowerDetAbsRealDiagonalTorus
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.HalfModTorus

open GlobalTheory.Doubling

theorem compFin_eq_one {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AE D) (h : finPart D y = 1) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E v y = 1 := by
  have h' : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y = 1 := h
  have e : GlobalTheory.AdelicU.compFin D.host.F D.host.E v y =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e, h', map_one]

theorem unitFin_eq_one {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (x : (AE D)ˣ) (h : finPart D (x : AE D) = 1) :
    unitFin D.host.F D.host.E v x = 1 :=
  Units.ext (compFin_eq_one v (x : AE D) h)

theorem compInf_eq {D : D7} (w : InfinitePlace D.host.F) (t' : GlobalTheory.AdelicU.EmbOver D.host.E w) (y : AE D) :
    GlobalTheory.AdelicU.infEmb t' (GlobalTheory.AdelicU.compInf D.host.F D.host.E w y) = GlobalTheory.AdelicU.infProj t' (infPart D y) := by
  have e : GlobalTheory.AdelicU.compInf D.host.F D.host.E w y =
      Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e]
  rfl

theorem absE_of_components {D : D7} (x : (AE D)ˣ) (c : NNReal)
    (hf : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x) = 1)
    (hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) (unitInf D.host.F D.host.E _ x) = c) :
    absE D.host.F D.host.E x = c ^ Fintype.card D.what₂.Tau := by
  have e1 : (∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x)) = 1 :=
    finprod_eq_one_of_forall_eq_one hf
  have e2 : (∏ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x)) = c ^ Fintype.card D.what₂.Tau := by
    rw [← (GlobalTheory.CMTypePlaces.places_bijective D).prod_comp
      (fun w => absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x))]
    simp only [hw, Finset.prod_const, Finset.card_univ]
  rw [absE_apply, e1, e2, mul_one]

theorem halfMod_torus : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (r n : ℕ) (t : Fin r → ℝ), (∀ i, 0 < t i) →
    ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 →
      (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n α = ∏ i, t i ^ (Module.finrank ℚ D.host.F * n) := by
  intro D θ hθ r n t ht α hfin hinf
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  haveI := hcm.1
  have hxv : ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D) = α.1.det := rfl
  have h1 : finPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D) = 1 := by
    rw [hxv, RingHom.map_det, RingHom.mapMatrix_apply, hfin, Matrix.det_one]
  have hf : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det α)) = 1 :=
    fun v => by rw [unitFin_eq_one v _ h1, map_one]
  have hdet : ∀ τ, θ τ (infPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D)) = ((∏ i, t i : ℝ) : ℂ) := by
    intro τ
    have e : θ τ (infPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D)) = (compAt θ τ α.1).det := by
      rw [hxv, ← RingHom.comp_apply, RingHom.map_det]
      rfl
    rw [e, hinf τ, Matrix.det_diagonal, Complex.ofReal_prod]
  have hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (unitInf D.host.F D.host.E _ (Matrix.GeneralLinearGroup.det α)) = ‖((∏ i, t i : ℝ) : ℂ)‖₊ ^ 2 := by
    intro τ
    let t' : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) :=
      ⟨tauE D τ, (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm⟩
    rw [absEw_eq_sq hcm t', ← hdet τ,
      GlobalTheory.AutFunCompare.isInfEmb_unique _ _ _ (hθ τ) (GlobalTheory.AdelicU.isInfEmb_infProj t')]
    exact congrArg (fun z : ℂ => ‖z‖₊ ^ 2) (compInf_eq _ t' _)
  have hcard : Fintype.card D.what₂.Tau = Module.finrank ℚ D.host.F := by
    rw [Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D), IsTotallyReal.finrank,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  have hP : 0 < ∏ i, t i := Finset.prod_pos fun i _ => ht i
  have habs : ((absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det α) : NNReal) : ℝ) =
      (∏ i, t i) ^ (2 * Module.finrank ℚ D.host.F) := by
    rw [absE_of_components _ _ hf hw, hcard, NNReal.coe_pow, NNReal.coe_pow, coe_nnnorm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hP, ← pow_mul]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod
  rw [habs, Finset.prod_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]
  congr 1
  push_cast
  ring

end GlobalTheory.HalfModTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPowerDetAbsRealDiagonalTorusStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPowerDetAbs_realDiagonal_torus : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (r n : ℕ) (t : Fin r → ℝ), (∀ i, 0 < t i) →
    ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 →
      (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n α = ∏ i, t i ^ (Module.finrank ℚ D.host.F * n) := by
  first | exact @GlobalTheory.HalfModTorus.halfMod_torus | exact GlobalTheory.HalfModTorus.halfMod_torus | (intros; apply GlobalTheory.HalfModTorus.halfMod_torus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzUnitaryIntertwinerScalar
open scoped Matrix

noncomputable section

open MeasureTheory Complex
open scoped Real RealInnerProductSpace ComplexConjugate FourierTransform SchwartzMap

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

def modPt (q : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim 0 fun i => q i

def trPt (p : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim (fun i => p i) 0

theorem pPart_modPt (q : EuclideanSpace ℝ l) : pPart (modPt q) = 0 := by
  ext i; simp [pPart, modPt]

theorem qPart_modPt (q : EuclideanSpace ℝ l) : qPart (modPt q) = q := by
  ext i; simp [qPart, modPt]

theorem pPart_trPt (p : EuclideanSpace ℝ l) : pPart (trPt p) = p := by
  ext i; simp [pPart, trPt]

theorem qPart_trPt (p : EuclideanSpace ℝ l) : qPart (trPt p) = 0 := by
  ext i; simp [qPart, trPt]

theorem rhoFun_modPt (q : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (modPt q) f x = cexp (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * I) * f x := by
  simp [rhoFun, phase, pPart_modPt, qPart_modPt]

theorem rhoFun_trPt (p : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (trPt p) f x = f (x + p) := by
  simp [rhoFun, phase, pPart_trPt, qPart_trPt]

def modS (q : EuclideanSpace ℝ l) (g : Sch l) : Sch l :=
  SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫) g

theorem coe_modS (q : EuclideanSpace ℝ l) (g : Sch l) : ⇑(modS q g) = rhoFun (modPt q) ⇑g := by
  have ht : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫ :=
    GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (innerSL ℝ q).hasTemperateGrowth
  funext x
  rw [modS, SchwartzMap.smulLeftCLM_apply_apply ht, GlobalTheory.Published.Metaplectic.eChar_apply, rhoFun_modPt, smul_eq_mul]
  congr 2
  push_cast
  ring

def trS (p : EuclideanSpace ℝ l) (g : Sch l) : Sch l := SchwartzMap.compSubConstCLM ℂ (-p) g

theorem coe_trS (p : EuclideanSpace ℝ l) (g : Sch l) : ⇑(trS p g) = rhoFun (trPt p) ⇑g := by
  funext x
  rw [trS, SchwartzMap.compSubConstCLM_apply, rhoFun_trPt, sub_neg_eq_add]

theorem integrable_conj_mul (a b : Sch l) : Integrable (fun x => conj (a x) * b x) := by
  refine b.integrable.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 a)
    (Complex.continuous_conj.comp a.continuous).aestronglyMeasurable (.of_forall fun x => ?_)
  rw [Complex.norm_conj]
  exact SchwartzMap.norm_le_seminorm ℝ a x

theorem integral_conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) :
    ∫ x, conj (U f x) * U g x = ∫ x, conj (f x) * g x := by
  have hn : ∀ h : Sch l, ‖(U h).toLp 2‖ = ‖h.toLp 2‖ := fun h => by
    rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) (U h).continuous.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) h.continuous.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hU]
  have hlin : ∀ (b : ℂ) (u v : Sch l), u.toLp 2 volume + b • v.toLp 2 volume = (u + b • v).toLp 2 volume := fun b u v => by
    have := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_add u (b • v)
    rw [(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_smul] at this
    exact this.symm
  have key : ∀ b : ℂ, ‖(U f).toLp 2 volume + b • (U g).toLp 2 volume‖ = ‖f.toLp 2 volume + b • g.toLp 2 volume‖ := fun b => by
    rw [hlin, hlin, ← map_smul, ← map_add (f := _), hn]
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key (-(RCLike.I : ℂ))
  have k4 := key (RCLike.I : ℂ)
  simp only [one_smul, neg_one_smul, neg_smul, ← sub_eq_add_neg] at k1 k2 k3 k4
  have e1 := SchwartzMap.inner_toL2_toL2_eq (U f) (U g) volume
  have e2 := SchwartzMap.inner_toL2_toL2_eq f g volume
  simp only [RCLike.inner_apply] at e1 e2
  simp only [mul_comm (starRingEnd ℂ _)]
  rw [← e1, ← e2, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, k1, k2, k3, k4]

end GlobalTheory.RealWeil.SchurSchwartz

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

theorem conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hc : ∀ (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h → ⇑(U h₁) = rhoFun w ⇑(U h))
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) (x : EuclideanSpace ℝ l) :
    conj (U f x) * U g x = conj (f x) * g x := by
  set D : EuclideanSpace ℝ l → ℂ := fun y => conj (U f y) * U g y - conj (f y) * g y with hD
  have hDi : Integrable D := (integrable_conj_mul (U f) (U g)).sub (integrable_conj_mul f g)
  have hDc : Continuous D :=
    ((Complex.continuous_conj.comp (U f).continuous).mul (U g).continuous).sub
      ((Complex.continuous_conj.comp f.continuous).mul g.continuous)
  have hF : 𝓕 D = 0 := by
    funext w
    rw [Real.fourier_eq', Pi.zero_apply]
    have h1 := hc (modPt (-w)) g (modS (-w) g) (coe_modS _ _)
    have h2 := integral_conj_mul_eq U hU f (modS (-w) g)
    rw [← sub_eq_zero, ← integral_sub (integrable_conj_mul _ _) (integrable_conj_mul _ _)] at h2
    rw [← h2]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [h1, coe_modS, rhoFun_modPt, hD, smul_eq_mul]
    rw [inner_neg_left, real_inner_comm]
    push_cast
    ring_nf
  have hinv := hDc.fourierInv_fourier_eq hDi (by rw [hF]; exact integrable_zero _ _ _)
  have hz : 𝓕⁻ (0 : EuclideanSpace ℝ l → ℂ) = 0 := by
    first
      | exact FourierTransform.fourierInv_zero
      | (funext w; simp [Real.fourierInv_eq])
  rw [hF, hz] at hinv
  have hx := congrFun hinv x
  simp only [hD, Pi.zero_apply] at hx
  exact sub_eq_zero.1 hx.symm

end GlobalTheory.RealWeil.SchurSchwartz

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOver
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOver
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocHat

open GlobalTheory.StdFrames (cpt cpt_ext toAd_spec)

variable {D : D7} {n : ℕ}

theorem mem_hat_iff_locL {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) (y : Fin n → EAf D) :
    y ∈ hat Λ ↔ ∀ v : HeightOneSpectrum (𝓞 D.host.F),
      (fun i => Formalism.UG.prV (E := D.host.E) v (y i)) ∈ Formalism.L2.Herm.locL v Λ := by
  haveI : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.mpr h
  rw [mem_hat]
  exact GlobalTheory.LatticeStabLocal.mem_latS_adele_iff Λ y

theorem prV_eq_zero_iff_cpt (v : HeightOneSpectrum (𝓞 D.host.F)) (z : EAf D) :
    Formalism.UG.prV (E := D.host.E) v z = 0 ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → cpt Q z = 0 := by
  refine (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (toAd_spec D) v z).trans ?_
  exact Iff.rfl

theorem mem_hat_iff_of_supp {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    (v : HeightOneSpectrum (𝓞 D.host.F)) {y : Fin n → EAf D}
    (hy : ∀ w, w ≠ v → ∀ i, Formalism.UG.prV (E := D.host.E) w (y i) = 0) :
    y ∈ hat Λ ↔ (fun i => Formalism.UG.prV (E := D.host.E) v (y i)) ∈ Formalism.L2.Herm.locL v Λ := by
  rw [mem_hat_iff_locL h]
  refine ⟨fun H => H v, fun H w => ?_⟩
  by_cases hwv : w = v
  · subst hwv
    exact H
  · have hz : (fun i => Formalism.UG.prV (E := D.host.E) w (y i)) = 0 := by
      ext i
      exact hy w hwv i
    rw [hz]
    exact Submodule.zero_mem _

set_option maxHeartbeats 800000 in
theorem locL_le {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) (h' : Λ'.FG)
    (v : HeightOneSpectrum (𝓞 D.host.F))
    (H : ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ → idem Q • y ∈ hat Λ') :
    Formalism.L2.Herm.locL v Λ ≤ Formalism.L2.Herm.locL v Λ' := by
  obtain ⟨e, -, -, he1, he0⟩ :=
    GlobalTheory.StdFrames.exists_idem (D := D) {Q : Pl D.host.E | Q.under (𝓞 D.host.F) = v}

  have hpe : Formalism.UG.prV (E := D.host.E) v e = 1 := by
    have h0 : Formalism.UG.prV (E := D.host.E) v (e - 1) = 0 := by
      rw [prV_eq_zero_iff_cpt]
      intro Q hQ
      rw [map_sub, map_one, he1 Q hQ, sub_self]
    rwa [map_sub, map_one, sub_eq_zero] at h0

  have key : ∀ x ∈ Λ, (e • fun i => inc D (x i)) ∈ hat Λ' := by
    intro x hx
    refine mem_hat_of_idem h' fun w => ?_
    rw [smul_smul]
    by_cases hw : w.under (𝓞 D.host.F) = v
    · have hwe : idem w * e = idem w := by
        refine cpt_ext fun Q => ?_
        rw [map_mul]
        by_cases hQ : Q = w
        · subst hQ
          rw [cpt_idem_self, he1 Q hw, one_mul]
        · rw [cpt_idem_ne hQ, zero_mul]
      rw [hwe]
      exact H w hw _ (smul_mem_hat (idem_mem w) (inc_mem_hat hx))
    · have hwe : idem w * e = 0 := by
        refine cpt_ext fun Q => ?_
        rw [map_mul, map_zero]
        by_cases hQ : Q = w
        · subst hQ
          rw [he0 Q hw, mul_zero]
        · rw [cpt_idem_ne hQ, zero_mul]
      rw [hwe, zero_smul]
      exact zero_mem_hat

  unfold Formalism.L2.Herm.locL Formalism.UG.latS
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have hm := (mem_hat_iff_locL h' _).mp (key x hx) v
  have hxe : (fun i => Formalism.UG.prV (E := D.host.E) v ((e • fun i => inc D (x i)) i)) =
      fun i => Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) (x i) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hpe, one_mul]
    rw [Formalism.UG.P.afsplit_prV_inclE]
  rw [hxe] at hm
  exact hm

theorem prV_idem_smul {v : HeightOneSpectrum (𝓞 D.host.F)} {Q : Pl D.host.E} (hQ : Q.under (𝓞 D.host.F) = v)
    (y : Fin n → EAf D) : ∀ w, w ≠ v → ∀ i, Formalism.UG.prV (E := D.host.E) w ((idem Q • y) i) = 0 := by
  intro w hw i
  have hQw : Formalism.UG.prV (E := D.host.E) w (idem Q) = 0 := by
    rw [prV_eq_zero_iff_cpt]
    intro Q' hQ'
    apply cpt_idem_ne
    intro hEq
    subst hEq
    exact hw (hQ'.symm.trans hQ)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, hQw, zero_mul]

theorem locL_eq_iff_idem : ∀ (D : D7) (n : ℕ) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Λ.FG → Λ'.FG → ∀ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ' ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ ↔ idem Q • y ∈ hat Λ' := by
  intro D n Λ Λ' h h' v
  constructor
  · intro heq Q hQ y
    rw [mem_hat_iff_of_supp h v (prV_idem_smul hQ y), mem_hat_iff_of_supp h' v (prV_idem_smul hQ y), heq]
  · intro H
    exact le_antisymm (locL_le h h' v fun Q hQ y => (H Q hQ y).mp)
      (locL_le h' h v fun Q hQ y => (H Q hQ y).mpr)

end GlobalTheory.LocHat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOverStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLattice_eq_iff_idempotent_components_over : ∀ (D : D7) (n : ℕ) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Λ.FG → Λ'.FG → ∀ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ' ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ ↔ idem Q • y ∈ hat Λ' := by
  first | exact @GlobalTheory.LocHat.locL_eq_iff_idem | exact GlobalTheory.LocHat.locL_eq_iff_idem | (intros; apply GlobalTheory.LocHat.locL_eq_iff_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedHermitianLatticeUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedHermitianLatticeUnique
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GlueUnique

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_proj {K M : Type} [Field K] [AddCommGroup M] [Module K M] (U : Submodule K M) :
    ∃ Q : M →ₗ[K] M, (∀ x ∈ U, Q x = 0) ∧ ∀ x, x - Q x ∈ U := by
  obtain ⟨W, hW⟩ := U.exists_isCompl
  refine ⟨LinearMap.id - U.subtype ∘ₗ U.projectionOnto W hW, fun x hx => ?_, fun x => ?_⟩
  · have := Submodule.projectionOnto_apply_left hW ⟨x, hx⟩
    simp [this]
  · simp

theorem exists_lattice {O K : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K] {n : ℕ} (Λ : Submodule O (Fin n → K))
    (h : Λ.FG) : ∃ (Q : (Fin n → K) →ₗ[K] (Fin n → K)) (Λ' : Submodule O (Fin n → K)),
      Submodule.IsFullLattice K Λ' ∧ Λ ≤ Λ' ∧ (∀ x ∈ Λ, Q x = 0) ∧ ∀ x ∈ Λ', Q x = 0 → x ∈ Λ := by
  classical
  obtain ⟨Q, h1, h2⟩ := exists_proj (Submodule.span K (Λ : Set (Fin n → K)))
  have h3 : ∀ x, Q (Q x) = Q x := fun x => by
    have := h1 _ (h2 x)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  let N := Submodule.span O (Set.range fun j : Fin n => Q (Pi.single j 1))
  have hfg : (Λ ⊔ N).FG := h.sup (Submodule.fg_span (Set.finite_range _))
  refine ⟨Q, Λ ⊔ N, { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := ?_ }, le_sup_left,
    fun x hx => h1 x (Submodule.subset_span hx), fun x hx h0 => ?_⟩
  · apply Submodule.eq_top_iff'.2
    intro x
    have hQ : Q x ∈ Submodule.span K (N : Set (Fin n → K)) := by
      have hx : (∑ j : Fin n, x j • Pi.single j (1 : K)) = x := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply, mul_ite]
      rw [← hx, map_sum]
      exact Submodule.sum_mem _ fun j _ => by
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩))
    have hleft := Submodule.span_mono (R := K) (show Λ ≤ Λ ⊔ N from le_sup_left)
    have hright := Submodule.span_mono (R := K) (show N ≤ Λ ⊔ N from le_sup_right)
    simpa only [sub_add_cancel] using add_mem (hleft (h2 x)) (hright hQ)
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have h4 : Q b = b := by
      refine Submodule.span_induction (p := fun b _ => Q b = b) ?_ (map_zero Q) ?_ ?_ hb
      · rintro _ ⟨j, rfl⟩
        exact h3 _
      · intro x y _ _ hx hy
        rw [map_add (f := _), hx, hy]
      · intro c x _ hx
        rw [← algebraMap_smul K c x, map_smul, hx]
    rw [map_add (f := _), h1 a (Submodule.subset_span ha), h4, zero_add] at h0
    rwa [h0, add_zero]

theorem map_mulVec_gen {K A : Type} [CommRing K] [CommRing A] (f : K →+* A) {n : ℕ}
    (Q : (Fin n → K) →ₗ[K] (Fin n → K)) (x : Fin n → K) :
    (LinearMap.toMatrix' Q).map f *ᵥ (fun i => f (x i)) = fun i => f (Q x i) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec, RingHom.map_mulVec]
  rfl

variable {D : D7}

theorem inc_injective : Function.Injective (inc D) := by
  obtain ⟨P, hP, h0⟩ := Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField D.host.E) |>.imp fun _ h => h.symm
  intro a b hab
  have := congrArg (GlobalTheory.StdFrames.cpt (D := D) ⟨P, hP.isPrime, h0⟩) hab
  rw [cpt_inc, cpt_inc] at this
  exact (algebraMap D.host.E _).injective this

theorem mem_of_inc_mem_hat {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    {x : Fin n → D.host.E} (hx : (fun i => inc D (x i)) ∈ hat Λ) : x ∈ Λ := by
  obtain ⟨Q, Λ', h1, h2, h3, h4⟩ := exists_lattice Λ h
  have := h1
  refine h4 x ((inc_mem_hat_iff (by infer_instance) x).1 (hat_mono h2 hx)) ?_
  have h5 : (LinearMap.toMatrix' Q).map (inc D) *ᵥ (fun i => inc D (x i)) = 0 := by
    refine hat_induction (p := fun y => (LinearMap.toMatrix' Q).map (inc D) *ᵥ y = 0) ?_ (mulVec_zero _) ?_ ?_ hx
    · intro y hy
      rw [map_mulVec_gen, h3 y hy]
      funext i
      exact RingHom.map_zero _
    · intro a b ha hb
      rw [mulVec_add, ha, hb, add_zero]
    · intro a _ b hb
      rw [mulVec_smul, hb, smul_zero]
  rw [map_mulVec_gen] at h5
  funext i
  exact inc_injective ((congrFun h5 i).trans (RingHom.map_zero _).symm)

theorem inCmp_iff {u : D.what₂.Word} {π : 𝓞 D.host.E} (hπ : IsPi u π) {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V}
    {z : Y.V} {L₀ : Lat X} {f₀ : Pl D.host.E → Fin X.rank → EAf D} {L L' : Submodule (𝓞 D.host.E) Y.V}
    (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y L) y ↔ InCmp (idem w) (Formalism.L2.Herm.crdLat Y L') y := by
  by_cases hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  · rcases (T_mem_iff hπ w).1 hT with hw | hw
    · exact ((h.2.2 w _ (isPlIdem_idem w) hw).1 y).trans ((h'.2.2 w _ (isPlIdem_idem w) hw).1 y).symm
    · have a := h.2.2 _ _ (isPlIdem_idem _) hw
      have a' := h'.2.2 _ _ (isPlIdem_idem _) hw
      rw [cjA_idem, GlobalTheory.StdFrames.cP_cP] at a a'
      refine (a.2 y).trans (Iff.trans ?_ (a'.2 y).symm)
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun y' => ?_
      rw [a.1 y', a'.1 y']
  · exact (h.2.1 w _ (isPlIdem_idem w) hT y).trans (h'.2.1 w _ (isPlIdem_idem w) hT y).symm

theorem glued_le {u : D.what₂.Word} {π : 𝓞 D.host.E} (hπ : IsPi u π) {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V}
    {z : Y.V} {L₀ : Lat X} {f₀ : Pl D.host.E → Fin X.rank → EAf D} {L L' : Submodule (𝓞 D.host.E) Y.V}
    (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') : L ≤ L' := by
  intro x hx
  have hfg : (Formalism.L2.Herm.crdLat Y L').FG := h'.1.map _
  have h1 : vA Y x ∈ hat (Formalism.L2.Herm.crdLat Y L') := mem_hat_of_idem hfg fun w =>
    ((inCmp_iff hπ h h' w _).1 ⟨smul_mem_hat (idem_mem w) (vA_mem_hat Y hx), by rw [smul_smul, idem_mul_self]⟩).1
  obtain ⟨x', hx', e⟩ := mem_of_inc_mem_hat hfg h1
  rwa [← (Formalism.L2.Herm.crd Y).injective e]

theorem glued_unique (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (Y X : HSp D)
    (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D)
    (L L' : Submodule (𝓞 D.host.E) Y.V) (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') :
    L = L' :=
  le_antisymm (glued_le hπ h h') (glued_le hπ h' h)

end GlobalTheory.GlueUnique

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedHermitianLatticeUniqueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedHermitianLattice_unique : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D) (L L' : Submodule (𝓞 D.host.E) Y.V), IsGlued Y X ι z u π L₀ f₀ L → IsGlued Y X ι z u π L₀ f₀ L' → L = L' := by
  first | exact @GlobalTheory.GlueUnique.glued_unique | exact GlobalTheory.GlueUnique.glued_unique | (intros; apply GlobalTheory.GlueUnique.glued_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepActsOnPureTensorsPlacewise
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationPlaceByPlaceOnPureTensors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationPlaceByPlaceOnPureTensors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.OmPure

theorem ipO_om_left {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : OmT S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    (g : GA D S) (h : GA D T) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    ipO μ 𝓕 (om (g, h) f) f' = ipO μ 𝓕 f (om (g⁻¹, h⁻¹) f') := by
  have e : om (g, h) (om (g⁻¹, h⁻¹) f') = f' := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have k : ipO μ 𝓕 (om (g, h) f) (om (g, h) (om (g⁻¹, h⁻¹) f')) = ipO μ 𝓕 f (om (g⁻¹, h⁻¹) f') :=
    GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW μ 𝓕 hμ (g, h) f _ hf (hW.om_pres _ _ hf')
  rwa [e] at k

theorem isPure_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (g : GA D S) (h : GA D T), {p : Place D | om (gAt S p g, gAt T p h) f₀ ≠ f₀}.Finite → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (om (g⁻¹, h⁻¹) f₀) → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ g h hfin hinv x f hx
  have hpres := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hW.std S T).1
  have h0 := base_theta hB
  refine ⟨⟨fun p => GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW (base_inf hB) p _ (hx.1.1 p) g h, ?_⟩,
    hW.om_pres _ _ hx.2.1, fun w => ?_⟩
  · refine (hfin.union hx.1.2).subset fun p hp => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hp (by simp only [hc.2, hc.1])
  · have hy := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ _ hinv (actO S T g⁻¹ h⁻¹ w)
    have hp := GlobalTheory.T.pureTensor_innerProduct_eq_finprod_localInnerProducts D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ _ _ _ hx hy
    have e : (fun p => ipO μ 𝓕 (om (gAt S p g, gAt T p h) (x p)) (heisO ψ S T (wAt p w) f₀)) =
        fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p (actO S T g⁻¹ h⁻¹ w)) (om (gAt S p g⁻¹, gAt T p h⁻¹) f₀)) := by
      funext p
      rw [ipO_om_left hW hμ _ _ (hx.1.1 p).1 (hpres _ _ h0), ← gAt_inv, ← gAt_inv, hW.om_heis _ _ _ _ h0,
        ((GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).2 S T p g⁻¹ h⁻¹ w).2]
    refine ⟨by rw [e]; exact hp.1, ?_⟩
    rw [e, ipO_om_left hW hμ _ _ hx.2.1 (hpres _ _ h0), hW.om_heis _ _ _ _ h0]
    exact hp.2

end GlobalTheory.PlaceTensor.OmPure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationPlaceByPlaceOnPureTensorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_placeByPlace_on_pureTensors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (g : GA D S) (h : GA D T), {p : Place D | om (gAt S p g, gAt T p h) f₀ ≠ f₀}.Finite → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (om (g⁻¹, h⁻¹) f₀) → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  first | exact @GlobalTheory.PlaceTensor.OmPure.isPure_om | exact GlobalTheory.PlaceTensor.OmPure.isPure_om | (intros; apply GlobalTheory.PlaceTensor.OmPure.isPure_om <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepActsOnPureTensorsPlacewise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.PureOm

theorem isPure_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (g : GA D S) (h : GA D T), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  obtain ⟨U, U', hU, hU', hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hW.std S T om (GlobalTheory.Ker.isWeak_of_datum hW)
    hW.om_cont f₀ (base_theta hB)
  have hgen := GlobalTheory.T.weilRepresentation_placeByPlace_on_pureTensors D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  obtain ⟨hp0, hploc⟩ := GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  have hstab := GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW (base_inf hB)
  have hgat := (GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).1
  let Good : GA D S → GA D T → Prop := fun g h => ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ),
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f)
  have om1 : ∀ u : WO S T → ℂ, om (1, 1) u = u := fun u => by
    have : om (1, 1) = 1 := map_one om
    rw [this]; rfl
  have omm : ∀ (g g' : GA D S) (h h' : GA D T) (u : WO S T → ℂ),
      om (g * g', h * h') u = om (g, h) (om (g', h') u) := fun g g' h h' u => by
    have : om (g * g', h * h') = om (g, h) * om (g', h') := map_mul om (g, h) (g', h')
    rw [this]; rfl
  have G1 : Good 1 1 := fun x f hx => by
    simpa only [gAt_one, om1] using hx
  have Gmul : ∀ g h g' h', Good g h → Good g' h' → Good (g * g') (h * h') := fun g h g' h' a b x f hx => by
    simpa only [gAt_mul, omm] using a _ _ (b x f hx)
  have Gloc : ∀ q g h, gAt S q g = g → gAt T q h = h → Good g h := fun q g h hg hh => by
    have e1 : ∀ p, p ≠ q → gAt S p g = 1 := fun p hp => by
      rw [← hg]; exact (hgat S q g).2.2 p hp
    have e2 : ∀ p, p ≠ q → gAt T p h = 1 := fun p hp => by
      rw [← hh]; exact (hgat T q h).2.2 p hp
    refine hgen g h ?_ ?_
    · refine (Set.finite_singleton q).subset fun p hp => ?_
      by_contra hpq
      exact hp (by rw [e1 p hpq, e2 p hpq, om1])
    · have := hploc q (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (hstab q f₀ (base_isLocal hB q) _ _)
        (fun p hp => by simp only [gAt_inv, e1 p hp, e2 p hp, inv_one, om1])
      have e : om (gAt S q g⁻¹, gAt T q h⁻¹) f₀ = om (g⁻¹, h⁻¹) f₀ := by rw [gAt_inv, gAt_inv, hg, hh]
      simp only [e] at this
      exact this
  have Gfin : ∀ g h, (g ∈ U ∧ g ∈ GfC S ∧ ∀ p, gAt S p g ∈ U ∧ gAt S p g ∈ GfC S) →
      (h ∈ U' ∧ h ∈ GfC T ∧ ∀ p, gAt T p h ∈ U' ∧ gAt T p h ∈ GfC T) → Good g h := fun g h hg hh => by
    refine hgen g h ?_ ?_
    · refine Set.finite_empty.subset fun p hp => ?_
      exact hp (hfix _ (hg.2.2 p).1 (hg.2.2 p).2 _ (hh.2.2 p).1 (hh.2.2 p).2)
    · have e : (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) = fun _ => f₀ := funext fun p => by
        rw [gAt_inv, gAt_inv]
        exact hfix _ (inv_mem (hg.2.2 p).1) (inv_mem (hg.2.2 p).2) _ (inv_mem (hh.2.2 p).1) (inv_mem (hh.2.2 p).2)
      rw [e, hfix _ (inv_mem hg.1) (inv_mem hg.2.1) _ (inv_mem hh.1) (inv_mem hh.2.1)]
      exact hp0
  have GS : ∀ g, Good g 1 := fun g => by
    have hg : g ∈ Submonoid.closure _ := (GlobalTheory.T.adelicUnitary_closure_local_components_open D S U hU).2 ▸ Submonoid.mem_top g
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      rcases hg with ⟨q, hq⟩ | hg
      · exact Gloc q g 1 hq (gAt_one T q)
      · exact Gfin g 1 hg ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩
    | one => exact G1
    | mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb
  have GT : ∀ h, Good 1 h := fun h => by
    have hh : h ∈ Submonoid.closure _ := (GlobalTheory.T.adelicUnitary_closure_local_components_open D T U' hU').2 ▸ Submonoid.mem_top h
    induction hh using Submonoid.closure_induction with
    | mem h hh =>
      rcases hh with ⟨q, hq⟩ | hh
      · exact Gloc q 1 h (gAt_one S q) hq
      · exact Gfin 1 h ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩ hh
    | one => exact G1
    | mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb
  intro x f hx g h
  have := Gmul _ _ _ _ (GS g) (GT h)
  rw [mul_one, one_mul] at this
  exact this x f hx

end GlobalTheory.PlaceTensor.PureOm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepActsOnPureTensorsPlacewiseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_acts_on_pureTensors_placewise : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (g : GA D S) (h : GA D T), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  first | exact @GlobalTheory.PlaceTensor.PureOm.isPure_om | exact GlobalTheory.PlaceTensor.PureOm.isPure_om | (intros; apply GlobalTheory.PlaceTensor.PureOm.isPure_om <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralConvergentDefinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefLiftSmooth

theorem hasDerivAt_integral_of_cocompact {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K K' : ℝ → H → ℂ)
    (hK : ∀ t, Continuous (K t)) (hK' : Continuous fun p : ℝ × H => K' p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ t h, K t (γ * h) = K t h) (hinv' : ∀ γ ∈ Γ, ∀ t h, K' t (γ * h) = K' t h)
    (hd : ∀ t h, HasDerivAt (fun s => K s h) (K' t h) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ h in 𝓕, K t h ∂μ) (∫ h in 𝓕, K' t₀ h ∂μ) t₀ := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t₀ 1).prod hC).exists_bound_of_continuousOn hK'.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hK'c : ∀ t, Continuous (K' t) := fun t => hK'.comp (Continuous.prodMk_right t)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => ‖(M : ℂ)‖)
    (Metric.ball_mem_nhds t₀ one_pos) (Filter.Eventually.of_forall fun t => (hK t).aestronglyMeasurable)
    (GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ (hK t₀) (fun γ hγ h => hinv γ hγ t₀ h))
    (hK'c t₀).aestronglyMeasurable ?_ hconst.norm ?_).2
  · refine Filter.Eventually.of_forall fun h t ht => ?_
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hinv' γ hγ]
    refine (hM (t, c) ⟨Metric.ball_subset_closedBall ht, hc⟩).trans ?_
    rw [Complex.norm_real]
    exact le_abs_self M
  · exact Filter.Eventually.of_forall fun h t _ => hd t h

end GlobalTheory.DefLiftSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolIntegrableOnIff
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

namespace GlobalTheory.VolIdent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vol_nu_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) : ∀ X : Node, X.InRange D.R.m → M.ν X = M'.ν X :=
  fun X hX => GlobalTheory.FunObjModel.isAt_unique (hM.vtx X hX) (hM'.vtx X hX)

theorem vol_setIntegral_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) {X : Node} (hX : X.InRange D.R.m) (f : GA D (G.V X) → ℂ)
    (hf : ∀ γ ∈ GQ (G.V X), ∀ u, f (γ * u) = f u) :
    ∫ u in M.fd X, f u ∂M.ν X = ∫ u in M'.fd X, f u ∂M'.ν X := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  have e := vol_nu_eq M M' hM hM' X hX
  have h1 := (hM.vtx X hX).haar_fund
  have h2 := (hM'.vtx X hX).haar_fund
  rw [← e] at h2 ⊢
  have := h1.1
  exact h1.2.setIntegral_eq h2.2 fun γ g => hf γ γ.2 g

theorem vol_integrableOn_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) {X : Node} (hX : X.InRange D.R.m) (f : GA D (G.V X) → ℂ)
    (hf : ∀ γ ∈ GQ (G.V X), ∀ u, f (γ * u) = f u) :
    IntegrableOn f (M.fd X) (M.ν X) ↔ IntegrableOn f (M'.fd X) (M'.ν X) := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  have e := vol_nu_eq M M' hM hM' X hX
  have h1 := (hM.vtx X hX).haar_fund
  have h2 := (hM'.vtx X hX).haar_fund
  rw [← e] at h2 ⊢
  have := h1.1
  exact h1.2.integrableOn_iff h2.2 fun γ g => hf γ γ.2 g

end GlobalTheory.VolIdent

end
end
