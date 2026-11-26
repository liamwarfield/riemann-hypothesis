module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf

theorem contAut_rapidDec_bounded_integrable : ∀ (D : D7) (V : HSp D), CoCpt V → ∀ φ : GA D V → ℂ, IsContAut V φ → RapidDec V φ ∧ (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ ∀ v : Vol V, IntegrableOn φ v.𝓕 v.μ := by
  intro D V hV φ hφ
  obtain ⟨K, hK, hS⟩ := hV
  have hr : RapidDec V φ := RapidDec.of_isCompact hφ.1 hφ.2 hK hS
  exact ⟨hr, hr.bounded, fun v => hr.integrableOn_fundamentalDomain v.haar v.fund⟩

end GlobalTheory.Unf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open scoped ContDiff

namespace GlobalTheory.CjNeg

variable {D : D7}

theorem inv_neg_mat {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have hn : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h1 : ψ a * ψ (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : starRingEnd ℂ (ψ a) * ψ a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  calc starRingEnd ℂ (ψ a) = starRingEnd ℂ (ψ a) * (ψ a * ψ (-a)) := by rw [h1, mul_one]
    _ = ψ (-a) := by rw [← mul_assoc, h2, one_mul]

theorem symplOH_negT (S T : HSp D) (x y : WO S T) :
    symplOH S (GlobalTheory.ChiGrid.negSp T) x y = -symplOH S T x y := by
  simp only [symplOH, symplO, hO, GlobalTheory.ChiGrid.negSp_gram, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

theorem symplOH_negS (S T : HSp D) (x y : WO S T) :
    symplOH (GlobalTheory.ChiGrid.negSp S) T x y = -symplOH S T x y := by
  simp only [symplOH, symplO, hO, GlobalTheory.ChiGrid.negSp_gram, inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S (GlobalTheory.ChiGrid.negSp T) w (cj id f) = cj id (heisO ψ S T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negT]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negS {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ (GlobalTheory.ChiGrid.negSp S) T w (cj id f) = cj id (heisO ψ S T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negS]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negT' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S T w (cj id f) = cj id (heisO ψ S (GlobalTheory.ChiGrid.negSp T) w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negT, neg_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negS' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S T w (cj id f) = cj id (heisO ψ (GlobalTheory.ChiGrid.negSp S) T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negS, neg_neg]

theorem contDiff_conj {k : ℕ} {g : (Fin k → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun t => starRingEnd ℂ (g t) :=
  Complex.conjCLE.contDiff.comp hg

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S (GlobalTheory.ChiGrid.negSp T) (ratW T S γ) w)) * starRingEnd ℂ (f w)
    rw [hf.quasi, map_mul, conj_psi hψ, symplOH_negT]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negT hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negT' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) f) : IsThetaFunO ψ S T (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    have hq : f (ratW T S γ + w) = ψ (-(symplOH S (GlobalTheory.ChiGrid.negSp T) (ratW T S γ) w)) * f w := hf.quasi γ w
    rw [hq, map_mul, conj_psi hψ, symplOH_negT, neg_neg]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negT' hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negS {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH (GlobalTheory.ChiGrid.negSp S) T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    rw [hf.quasi, map_mul, conj_psi hψ, symplOH_negS]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negS hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negS' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f) : IsThetaFunO ψ S T (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    have hq : f (ratW T S γ + w) = ψ (-(symplOH (GlobalTheory.ChiGrid.negSp S) T (ratW T S γ) w)) * f w := hf.quasi γ w
    rw [hq, map_mul, conj_psi hψ, symplOH_negS, neg_neg]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negS' hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

theorem cj_id_cj_id {S T : HSp D} (f : WO S T → ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = f :=
  GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj_cj id id (fun _ => rfl) f

theorem theta_heis_neg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ f : WO S T → ℂ, (IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f) ∧ (IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f)) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S (GlobalTheory.ChiGrid.negSp T) w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) ∧ heisO ψ (GlobalTheory.ChiGrid.negSp S) T w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) := by
  intro D ψ hψ S T
  refine ⟨fun f => ⟨⟨fun h => ?_, theta_negT hψ⟩, ⟨fun h => ?_, theta_negS hψ⟩⟩, fun w f => ⟨heis_negT hψ S T w f, heis_negS hψ S T w f⟩⟩
  · simpa only [cj_id_cj_id] using theta_negT' hψ h
  · simpa only [cj_id_cj_id] using theta_negS' hψ h

end GlobalTheory.CjNeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaHeisenberg_conjugation_negHermitianSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ f : WO S T → ℂ, (IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f) ∧ (IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f)) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S (GlobalTheory.ChiGrid.negSp T) w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) ∧ heisO ψ (GlobalTheory.ChiGrid.negSp S) T w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) := by
  first | exact @GlobalTheory.CjNeg.theta_heis_neg | exact GlobalTheory.CjNeg.theta_heis_neg | (intros; apply GlobalTheory.CjNeg.theta_heis_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptOfIsAnisoOrPosDef
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf.CoCptOf

theorem coCpt_of_mul {D : D7} {V : HSp D}
    (h : ∃ K : Set (GA D V), IsCompact K ∧ ∀ g, ∃ γ ∈ GQ V, ∃ k ∈ K, g = γ * k) : CoCpt V := by
  obtain ⟨K, hK, h⟩ := h
  refine ⟨K, hK, fun g => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

theorem coCpt_of_isAniso_or_posDef :
    ∀ (D : D7) (V : HSp D), (IsAniso V → CoCpt V) ∧ ((∀ τ, (gramAt D V τ).PosDef) → CoCpt V) :=
  fun D V => ⟨fun h => coCpt_of_mul (GlobalTheory.Mem.AnisoQuotient.exists_compact D V h),
    fun h => coCpt_of_mul (GlobalTheory.definite_unitary_cocompact V h)⟩

end GlobalTheory.Unf.CoCptOf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.BoxSlice

open GlobalTheory.MixModel.OrthDec

variable {D : D7} {S A B : HSp D} (d : GlobalTheory.MixModel.OrthDec S A B)

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp only [heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem resS_symm_left (T : HSp D) (u : WO A T) :
    (d.resS T).symm (u, 0) = GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA u := by
  rw [resS_symm_apply, GlobalTheory.MixModel.sandwich_apply, Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem isThetaFunO_slice_left {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (v : WO B T) : IsThetaFunO ψ A T fun u => f ((d.resS T).symm (u, v)) := {
  quasi γ u := by
    have e0 : (d.resS T).symm (ratW T A γ, 0) = ratW T S (γ * d.qA) := by
      rw [resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    have e : ((ratW T A γ + u, v) : WO A T × WO B T) = (ratW T A γ, (0 : WO B T)) + (u, v) := by simp
    show f ((d.resS T).symm (ratW T A γ + u, v)) = ψ (-(symplOH A T (ratW T A γ) u)) * f ((d.resS T).symm (u, v))
    rw [e, map_add (f := _), e0, hf.quasi, ← e0, d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.MixModel.symplOH_zero_left, add_zero]
  level := by
    obtain ⟨U, hU, k⟩ := hf.level
    refine ⟨U.comap (GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA),
      hU.preimage (GlobalTheory.MixModel.continuous_sandwich _ _), fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (k _ hu (GlobalTheory.MixModel.map_sandwich _ _ _ h0)) ((d.resS T).symm (w, v))
    rw [← resS_symm_left] at e1
    simp only [heisO] at e1 ⊢
    rw [← e1, ← map_add (d.resS T).symm, Prod.mk_add_mk, add_zero, d.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  cont := hf.cont.comp ((d.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const))
  smooth k L hL h0 w := by
    have e : ∀ t, (d.resS T).symm (w + L t, v) =
        (d.resS T).symm (w, v) + ((GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA).comp L) t := by
      intro t
      rw [AddMonoidHom.comp_apply, ← resS_symm_left, ← map_add (d.resS T).symm, Prod.mk_add_mk, add_zero]
    simp only [e]
    exact hf.smooth k ((GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA).comp L)
      ((GlobalTheory.MixModel.continuous_sandwich _ _).comp hL) (fun t => GlobalTheory.MixModel.map_sandwich _ _ _ (h0 t)) _ }

theorem isThetaFunO_slice_right {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (u : WO A T) : IsThetaFunO ψ B T fun v => f ((d.resS T).symm (u, v)) := by
  have h := isThetaFunO_slice_left d.symm hf u
  have e : ∀ v, (d.symm.resS T).symm (v, u) = (d.resS T).symm (u, v) := fun v => by
    rw [resS_symm_apply, resS_symm_apply, add_comm]; rfl
  simp only [e] at h
  exact h

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), (∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (o.boxS T fA fB)) ∧ (∀ fA fB, o.boxS T fA fB 0 = fA 0 * fB 0) ∧ (∀ fA fB, (∀ u, heisO ψ S T ((o.resS T).symm (u, 0)) (o.boxS T fA fB) = o.boxS T (heisO ψ A T u fA) fB) ∧ ∀ v, heisO ψ S T ((o.resS T).symm (0, v)) (o.boxS T fA fB) = o.boxS T fA (heisO ψ B T v fB)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ v, IsThetaFunO ψ A T fun u => f ((o.resS T).symm (u, v))) ∧ ∀ u, IsThetaFunO ψ B T fun v => f ((o.resS T).symm (u, v)) := by
  intro D ψ _ S A B T o
  refine ⟨fun fA fB hA hB => o.isThetaFunO_boxS hA hB, fun fA fB => o.boxS_zero T fA fB,
    fun fA fB => ⟨fun u => ?_, fun v => ?_⟩, fun f hf => ⟨fun v => isThetaFunO_slice_left o hf v,
      fun u => isThetaFunO_slice_right o hf u⟩⟩
  · rw [o.heisO_boxS, AddEquiv.apply_symm_apply, heisO_zero']
  · rw [o.heisO_boxS, AddEquiv.apply_symm_apply, heisO_zero']

end GlobalTheory.BoxSlice

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), (∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (o.boxS T fA fB)) ∧ (∀ fA fB, o.boxS T fA fB 0 = fA 0 * fB 0) ∧ (∀ fA fB, (∀ u, heisO ψ S T ((o.resS T).symm (u, 0)) (o.boxS T fA fB) = o.boxS T (heisO ψ A T u fA) fB) ∧ ∀ v, heisO ψ S T ((o.resS T).symm (0, v)) (o.boxS T fA fB) = o.boxS T fA (heisO ψ B T v fB)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ v, IsThetaFunO ψ A T fun u => f ((o.resS T).symm (u, v))) ∧ ∀ u, IsThetaFunO ψ B T fun v => f ((o.resS T).symm (u, v)) := by
  first | exact @GlobalTheory.BoxSlice.main | exact GlobalTheory.BoxSlice.main | (intros; apply GlobalTheory.BoxSlice.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

variable {D : D7}

theorem linInd_e {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : LinearIndependent D.host.E d.e.transpose := by
  show LinearIndependent D.host.E (fun i : Fin ρ => fun k : Fin W.rank => d.e k i)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : d.e *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← this]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : (d.e'ᴴ * W.gram * d.e) *ᵥ g = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  rw [d.e'e, Matrix.one_mulVec] at h2
  intro i; exact congrFun h2 i

theorem gramQ_e {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : gramQ W d.e = 0 := by
  rw [gramQ, ← Matrix.mul_assoc]; exact d.ee

theorem flagUnipotent_anisotropic_projection_eq_one {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) {n : GA D W} (hn : n ∈ flagN d) :
    d.p0 ⬝ (mt W n ⬝ d.j0) = 1 := by
  obtain ⟨u, -, b, c, rfl⟩ := ((flag_jacobi_structure D W W₀ ρ d).1 n).1 hn
  rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic,
    ← Matrix.mul_assoc (mt W (d.levi u)) d.jX, d.levi_jX, Matrix.mul_add, d.p0_j0, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, Matrix.zero_mul, add_zero]

theorem Rgrp_eq {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : Rgrp W (rat d.e) = jacGrp d := by
  have dec := flag_jacobi_structure D W W₀ ρ d
  ext r
  constructor
  · rintro ⟨u, hu, hr⟩
    have hs : d.levi u⁻¹ * r ∈ stabX d := by
      show mt W (d.levi u⁻¹ * r) ⬝ d.jX = d.jX
      rw [mt_mul, Matrix.mul_assoc, show mt W r ⬝ d.jX = d.jX ⬝ u.1 from hr, ← Matrix.mul_assoc, d.levi_jX,
        Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    obtain ⟨n, hn, h, he⟩ := (dec.2.2.1 _).1 hs
    have hl : d.levi u ∈ flagN d := (dec.1 _).2 ⟨u, hu, 0, 0, by rw [d.nB_zero, d.nC_zero, mul_one, mul_one]⟩
    refine (dec.2.2.2.1 r).2 ⟨d.levi u * n, mul_mem hl (Subgroup.mem_inf.1 hn).1, h, ?_⟩
    rw [mul_assoc, ← he, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  · intro hr
    obtain ⟨n, hn, h, rfl⟩ := (dec.2.2.2.1 r).1 hr
    obtain ⟨u, hu, b, c, rfl⟩ := (dec.1 n).1 hn
    refine ⟨u, hu, ?_⟩
    show mt W _ ⬝ d.jX = d.jX ⬝ u.1
    rw [mt_mul, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.nC_jX, d.nB_jX,
      d.levi_jX]

theorem flagUnipotent_mul_emb_mem_rational_iff {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) {n : GA D W} (hn : n ∈ flagN d) (h : GA D W₀) :
    n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  constructor
  · intro hg
    have hh : h ∈ GQ W₀ := by
      rw [mem_GQ_iff] at hg ⊢
      have e : mt W₀ h = d.p0 ⬝ (mt W (n * d.emb0 h) ⬝ d.j0) := by
        rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt W n), ← Matrix.mul_assoc, flagUnipotent_anisotropic_projection_eq_one d hn,
          Matrix.one_mul]
      rw [e]
      exact ratMx_mul (rat_mem _) (ratMx_mul hg (rat_mem _))
    refine ⟨?_, hh⟩
    have : n = n * d.emb0 h * (d.emb0 h)⁻¹ := by rw [mul_inv_cancel_right]
    rw [this]
    exact mul_mem hg (inv_mem (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hh))
  · rintro ⟨h1, h2⟩
    exact mul_mem h1 (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h2)

theorem base_point : ∀ (D : D7) (W W₀ : HSp D) (ρ : ℕ) (d : HypDec W W₀ ρ), IsBase W d.e ∧ gramQ W d.e = 0 ∧ xZero d = rat d.e ∧ Rgrp W (rat d.e) = jacGrp d ∧ Continuous d.emb0 ∧ ∀ n ∈ flagN d, ∀ h, n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  intro D W W₀ ρ d
  refine ⟨⟨linInd_e d, fun u _ => ?_⟩, gramQ_e d, rfl, Rgrp_eq d, d.continuous_embed, fun n hn h => flagUnipotent_mul_emb_mem_rational_iff d hn h⟩
  rw [gramQ_e d, rat_zero, Matrix.zero_mul, Matrix.mul_zero]

end GlobalTheory.Unf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_base_point_fourierJacobi_group : ∀ (D : D7) (W W₀ : HSp D) (ρ : ℕ) (d : HypDec W W₀ ρ), IsBase W d.e ∧ gramQ W d.e = 0 ∧ xZero d = rat d.e ∧ Rgrp W (rat d.e) = jacGrp d ∧ Continuous d.emb0 ∧ ∀ n ∈ flagN d, ∀ h, n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  first | exact @GlobalTheory.Unf.base_point | exact GlobalTheory.Unf.base_point | (intros; apply GlobalTheory.Unf.base_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
set_option synthInstance.maxHeartbeats 400000
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatLatV

variable {D : D7}

def cut (P : Pl D → Prop) (u : Af D.host.F ⊗[D.host.F] D.host.E) : AE D :=
  Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift ((GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * u)

def cutHom (P : Pl D → Prop) : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D where
  toFun := cut P
  map_zero' := by
    show Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ = 0
    rw [mul_zero]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift_zero
  map_add' a b := by
    show Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ = Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ + Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _
    rw [mul_add]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift_add _ _

theorem cut_tmul (P : Pl D → Prop) (a : Af D.host.F) (x : D.host.E) :
    cut P (a ⊗ₜ[D.host.F] x) = pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP P * a) ⊗ₜ[D.host.F] x := by
  unfold cut
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl


set_option maxHeartbeats 800000 in
theorem cut_finPart (P : Pl D → Prop) (u : AE D) (hu : u ∈ idAt D P) : cut P (finPart D u) = u := by
  unfold idAt at hu
  rw [Ideal.mem_inf] at hu
  obtain ⟨hinf, hfin⟩ := hu
  rw [RingHom.mem_ker] at hinf
  have hoff : ∀ w : Pl D, ¬ P w → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D u) = 0 := by
    intro w hw
    have := (Submodule.mem_iInf _).1 hfin ⟨w, hw⟩
    exact (RingHom.mem_ker).1 this
  have hcut : (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D u = finPart D u := by
    refine (sub_eq_zero.mp (GlobalTheory.SelfDualAt.eq_zero_of_compFin _ fun w => ?_)).symm
    rw [map_sub, map_mul]
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) =
        evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hc, GlobalTheory.SelfDualAt.evalV_indP]
    by_cases hw : P w
    · rw [if_pos hw, ← Algebra.TensorProduct.one_def, one_mul, sub_self]
    · rw [if_neg hw, TensorProduct.zero_tmul, zero_mul, sub_zero, hoff w hw]
  unfold cut
  rw [hcut]
  exact (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.eq_lift_of_infPart u hinf).symm

theorem mem_latV_of_hatL : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D),
    (∀ i, y i ∈ idAt D P) →
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := by
  intro D S L P y hy hz
  have hlat : (fun i => finPart D (y i)) ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) :=
    (GlobalTheory.LevSplit.latHat_iff L _).2 hz
  have key : y = AddMonoidHom.compLeft (cutHom P) (Fin S.rank) (fun i => finPart D (y i)) :=
    funext fun i => (cut_finPart P (y i) (hy i)).symm
  rw [key]
  refine AddSubgroup.closure_induction
    (p := fun u _ => AddMonoidHom.compLeft (cutHom P) (Fin S.rank) u ∈ latV S L P) ?_ ?_ ?_ ?_ hlat
  · rintro _ ⟨a, ha, x, hx, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨GlobalTheory.SelfDualAt.indP P * a, ?_, ?_, 1, rfl, x, hx, ?_⟩
    · intro v
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
      split_ifs
      · rw [one_mul]; exact ha v
      · rw [zero_mul]; exact zero_mem _
    · intro v hv
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hv, zero_mul]
    · funext i
      show cut P (a ⊗ₜ[D.host.F] x i) = _
      rw [cut_tmul, one_mul]
  · rw [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact add_mem ha hb
  · intro a _ ha
    rw [map_neg]; exact neg_mem ha

end GlobalTheory.HatLatV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLattiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := by
  first | exact @GlobalTheory.HatLatV.mem_latV_of_hatL | exact GlobalTheory.HatLatV.mem_latV_of_hatL | (intros; apply GlobalTheory.HatLatV.mem_latV_of_hatL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenberg
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenberg
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped ContDiff

namespace GlobalTheory.AdjointPair

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

theorem dagger_add (S T : HSp D) (x y : WO S T) : dagger S T (x + y) = dagger S T x + dagger S T y := by
  simp only [dagger, adj_add, Matrix.mul_add, Matrix.add_mul]

def daggerHom (S T : HSp D) : WO S T →+ WO T S where
  toFun := dagger S T
  map_zero' := by simp only [dagger, adj_zero, Matrix.zero_mul, Matrix.mul_zero]
  map_add' := dagger_add S T

theorem continuous_dagger (S T : HSp D) : Continuous (dagger S T) :=
  continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)

theorem dagger_rat (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    dagger S T (rat γ) = rat (S.gram⁻¹ * (γᴴ * T.gram)) := by
  rw [rat_mul, rat_mul, rat_conjTranspose]; rfl

theorem infPart_cA (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem map_dagger_zero {B : Type} [CommRing B] (p : AE D →+* B) (hp : ∀ z, p z = 0 → p (cA D z) = 0)
    (S T : HSp D) {x : WO S T} (hx : x.map p = 0) : (dagger S T x).map p = 0 := by
  have h1 : (adj x).map p = 0 := by
    funext i j
    have := congrFun (congrFun hx j) i
    simp only [adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.zero_apply] at this ⊢
    exact hp _ this
  rw [dagger, Matrix.map_mul, Matrix.map_mul, h1, Matrix.zero_mul, Matrix.mul_zero]

theorem infPart_zero (z : AE D) (h : infPart D z = 0) : infPart D (cA D z) = 0 := by
  rw [infPart_cA, h, RingHom.map_zero]

theorem finPart_zero (z : AE D) (h : finPart D z = 0) : finPart D (cA D z) = 0 := by
  rw [finPart_cA, h, RingHom.map_zero]

theorem hO_dagger (S T : HSp D) (x y : WO S T) : hO T S (dagger S T x) (dagger S T y) = hO S T y x := by
  rw [hO_eq_trace, hO_eq_trace]
  simp only [dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, gA_giA_cancel, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplO_dagger (S T : HSp D) (x y : WO S T) :
    symplO T S (dagger S T x) (dagger S T y) = -symplO S T x y := by
  have h := GlobalTheory.OrientedHeis.symplO_skew x y
  unfold symplO at h ⊢
  rw [hO_dagger]
  exact h

theorem symplOH_dagger (S T : HSp D) (x y : WO S T) :
    symplOH T S (dagger S T x) (dagger S T y) = -symplOH S T x y := by
  unfold symplOH
  rw [symplO_dagger, mul_neg]

theorem act_dagger (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    dagger S T (actO S T g h x) = actO T S h g (dagger S T x) := by
  simp only [dagger, actO_eq, adj_mul, mt_inv S g, mt_inv T h, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel]

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (hn a)).symm

theorem heis_dagger (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) : heisO ψ T S (dagger S T w) (cj (dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (heisO ψ S T w f) := by
  funext y
  have hs : symplOH T S y (dagger S T w) = -symplOH S T (dagger T S y) w := by
    have := symplOH_dagger S T (dagger T S y) w
    rwa [dagger_dagger] at this
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, map_mul]
  rw [dagger_add, dagger_dagger, hs, conj_psi hn]

theorem theta_fwd (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ T S (cj (dagger T S) f) := {
  quasi γ w := by
    have hr : dagger T S (ratW S T γ) = ratW T S (T.gram⁻¹ * (γᴴ * S.gram)) := by
      rw [ratW_eq, ratW_eq]; exact dagger_rat T S γ
    have hq := hf.quasi (T.gram⁻¹ * (γᴴ * S.gram)) (dagger T S w)
    rw [← hr, symplOH_dagger, neg_neg] at hq
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [dagger_add, hq, map_mul, conj_psi hn]
  level := by
    obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (daggerHom T S), hU.preimage (continuous_dagger T S), fun u hu hinf => ?_⟩
    have h1 := heis_dagger ψ hn S T (dagger T S u) f
    rw [dagger_dagger, hfix (dagger T S u) hu (map_dagger_zero (infPart D) infPart_zero T S hinf)] at h1
    exact h1
  cont := Complex.continuous_conj.comp (hf.cont.comp (continuous_dagger T S))
  smooth k L hL hfin w := by
    have h := hf.smooth k ((daggerHom T S).comp L) ((continuous_dagger T S).comp hL)
      (fun t => map_dagger_zero (finPart D) finPart_zero T S (hfin t)) (dagger T S w)
    have e : (fun t => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f (w + L t)) =
        fun t => Complex.conjCLE (f (dagger T S w + (daggerHom T S).comp L t)) := by
      funext t
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, AddMonoidHom.comp_apply, Complex.conjCLE_apply]
      rw [dagger_add]; rfl
    rw [e]
    exact Complex.conjCLE.contDiff.comp h }

theorem theta_iff (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (f : WO S T → ℂ) :
    IsThetaFunO ψ T S (cj (dagger T S) f) ↔ IsThetaFunO ψ S T f := by
  refine ⟨fun h => ?_, theta_fwd ψ hn S T⟩
  have := theta_fwd ψ hn T S h
  rwa [cj_cj (dagger T S) (dagger S T) (dagger_dagger S T)] at this

theorem adjoint_clauses : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ x y : WO S T, symplO T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T y) = -symplO S T x y) ∧ (∀ g h (x : WO S T), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (actO S T g h x) = actO T S h g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x)) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) ↔ IsThetaFunO ψ S T f) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T w) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) (heisO ψ S T w f) := by
  intro D ψ hψ S T
  exact ⟨symplO_dagger S T, act_dagger S T, fun f => theta_iff ψ hψ.1.2.1 S T f, heis_dagger ψ hψ.1.2.1 S T⟩

end GlobalTheory.AdjointPair

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenbergStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ x y : WO S T, symplO T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T y) = -symplO S T x y) ∧ (∀ g h (x : WO S T), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (actO S T g h x) = actO T S h g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x)) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) ↔ IsThetaFunO ψ S T f) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T w) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) (heisO ψ S T w f) := by
  first | exact @GlobalTheory.AdjointPair.adjoint_clauses | exact GlobalTheory.AdjointPair.adjoint_clauses | (intros; apply GlobalTheory.AdjointPair.adjoint_clauses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.BesSemi

variable {D : D7}

theorem continuous_embA {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) :
    Continuous (embA d o) := by
  have h : (embA d o : GA D A → GA D S) = fun h => d.emb0 (o.emb (h, 1)) := funext fun h => embA_apply d o h
  rw [h]
  exact d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))

theorem besselCompression_unipotent_mul_embedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {n : GA D S} (hn : n ∈ flagN d) (k : GA D S₀) :
    d.p0 * (mt S (n * d.emb0 k) * d.j0) = mt S₀ k := by
  have hflag := (GlobalTheory.BesselChar.mem_NFlag_iff S d.e
    (GlobalTheory.MixPer.Decomp.linInd d) n).1 hn
  have hcols : ∀ j : Fin S₀.rank, ∃ a : Fin ρ → AE D,
      mt S n *ᵥ (fun i => d.j0 i j) = (fun i => d.j0 i j) + d.jX *ᵥ a := by
    intro j
    apply hflag.2
    change d.pY *ᵥ (fun i => d.j0 i j) = 0
    funext i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using
      congrFun (congrFun d.pY_j0 i) j
  choose a ha using hcols
  have h0 : mt S n * d.j0 = d.j0 + d.jX * Matrix.of (fun i j => a j i) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (ha j) i
  have hproj : d.p0 * (mt S n * d.j0) = 1 := by
    rw [h0, Matrix.mul_add, d.p0_j0, ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic,
    ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc d.p0, hproj, Matrix.one_mul]

theorem unique {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {n n' : GA D S}
    (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) {h h' : GA D A} (e : n * embA d o h = n' * embA d o h') :
    n = n' ∧ h = h' := by
  have e0 := congrArg (fun g => d.p0 * (mt S g * d.j0)) e
  rw [embA_apply, embA_apply, besselCompression_unipotent_mul_embedding d hn,
    besselCompression_unipotent_mul_embedding d hn'] at e0
  have hh : h = h' := congrArg Prod.fst (o.emb_injective (mt_injective S₀ e0))
  subst h'
  exact ⟨mul_right_cancel e, rfl⟩

theorem rat_iff {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {n : GA D S}
    (hn : n ∈ flagN d) (h : GA D A) : n * embA d o h ∈ GQ S ↔ n ∈ GQ S ∧ h ∈ GQ A := by
  constructor
  · intro hg
    have hk : o.emb (h, 1) ∈ GQ S₀ := by
      rw [mem_GQ_iff]
      rw [embA_apply] at hg
      rw [← besselCompression_unipotent_mul_embedding d hn]
      exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S _).1 hg) (rat_mem _))
    have hA : h ∈ GQ A := by
      rw [mem_GQ_iff]
      have e : o.pA * (mt S₀ (o.emb (h, 1)) * o.jA) = mt A h := by
        rw [o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]
      rw [← e]
      exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S₀ _).1 hk) (rat_mem _))
    have he : embA d o h ∈ GQ S := by rw [embA_apply]; exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hk
    refine ⟨?_, hA⟩
    have : n = n * embA d o h * (embA d o h)⁻¹ := (mul_inv_cancel_right n _).symm
    rw [this]
    exact mul_mem hg (inv_mem he)
  · rintro ⟨hn', hA⟩
    refine mul_mem hn' ?_
    rw [embA_apply]
    exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (o.emb_mem_GQ hA (one_mem _))

end GlobalTheory.Unf.BesSemi

namespace GlobalTheory.Unf

theorem besSemi : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), Continuous (embA B.d B.o) ∧ IsClosed (flagN B.d : Set (GA D B.V)) ∧ (∀ n ∈ flagN B.d, ∀ h, embA B.d B.o h * n * (embA B.d B.o h)⁻¹ ∈ flagN B.d) ∧ (∀ n ∈ flagN B.d, ∀ n' ∈ flagN B.d, ∀ h h', n * embA B.d B.o h = n' * embA B.d B.o h' → n = n' ∧ h = h') ∧ ∀ n ∈ flagN B.d, ∀ h, n * embA B.d B.o h ∈ GQ B.V ↔ n ∈ GQ B.V ∧ h ∈ GQ B.A := by
  intro D σ B
  refine ⟨BesSemi.continuous_embA B.d B.o, GlobalTheory.Mem.TrueRecord.isClosed_NFlag B.V (isIsoSub_e B.d),
    fun n hn h => ?_, fun n hn n' hn' h h' e => BesSemi.unique B.d B.o hn hn' e,
    fun n hn h => BesSemi.rat_iff B.d B.o hn h⟩
  rw [embA_apply]
  let g := B.d.emb0 (B.o.emb (h, 1))
  have hg : mt B.V g * B.d.e.map (incA D) = B.d.e.map (incA D) :=
    B.d.wittDecomp_anisotropicEmbedding_inclX _
  have hg' := GlobalTheory.BesselChar.inv_fix_cols (mt_inv_mul B.V g) hg
  have hflag := GlobalTheory.BesselChar.mem_NFlag_iff B.V B.d.e
    (GlobalTheory.MixPer.Decomp.linInd B.d)
  change g * n * g⁻¹ ∈ flagN B.d
  apply (hflag _).2
  rw [mt_mul, mt_mul]
  exact ((hflag n).1 hn).conj hg hg' (mt_mul_inv B.V g)
    (GlobalTheory.BesselChar.perp_fixed B.d.e g⁻¹ hg')

end GlobalTheory.Unf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRationalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselGroup_semidirectProduct_rational : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), Continuous (embA B.d B.o) ∧ IsClosed (flagN B.d : Set (GA D B.V)) ∧ (∀ n ∈ flagN B.d, ∀ h, embA B.d B.o h * n * (embA B.d B.o h)⁻¹ ∈ flagN B.d) ∧ (∀ n ∈ flagN B.d, ∀ n' ∈ flagN B.d, ∀ h h', n * embA B.d B.o h = n' * embA B.d B.o h' → n = n' ∧ h = h') ∧ ∀ n ∈ flagN B.d, ∀ h, n * embA B.d B.o h ∈ GQ B.V ↔ n ∈ GQ B.V ∧ h ∈ GQ B.A := by
  first | exact @GlobalTheory.Unf.besSemi | exact GlobalTheory.Unf.besSemi | (intros; apply GlobalTheory.Unf.besSemi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDoma
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDoma
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.RationalSubgroupFund

theorem countable_discrete_exists_fundamentalDomain : ∀ (D : D7) (W : HSp D) (Γ : Subgroup (GA D W)), Γ ≤ GQ W → Countable Γ ∧ DiscreteTopology Γ ∧ ∀ μ : Measure (GA D W), μ.IsHaarMeasure → ∃ 𝓑 : Set (GA D W), IsFundamentalDomain Γ 𝓑 μ := by
  intro D W Γ hΓ
  obtain ⟨_, h2, _, h4, h5, h6, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := h2; haveI := h4; haveI := h5; haveI := h6
  haveI hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : Γ => (⟨(x : GA D W), hΓ x.2⟩ : GQ W))
      (continuous_subtype_val.subtype_mk _)
      (fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy))
  obtain ⟨hc, 𝓓, h𝓓m, h𝓓⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ
  haveI := hc
  refine ⟨hc, hdisc, fun μ _ => ⟨𝓓, ?_⟩⟩
  exact IsFundamentalDomain.mk' h𝓓m.nullMeasurableSet (fun g => h𝓓 g)

end GlobalTheory.RationalSubgroupFund
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDomaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain : ∀ (D : D7) (W : HSp D) (Γ : Subgroup (GA D W)), Γ ≤ GQ W → Countable Γ ∧ DiscreteTopology Γ ∧ ∀ μ : Measure (GA D W), μ.IsHaarMeasure → ∃ 𝓑 : Set (GA D W), IsFundamentalDomain Γ 𝓑 μ := by
  first | exact @GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain | exact GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain | (intros; apply GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasures
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasures
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem sFinite_vol : ∀ (D : D7) (ρ m : ℕ) (vb : VolM D ρ m) (vU : VolU D ρ), SFinite vb.μ ∧ SFinite vU.ν := by
  intro D ρ m vb vU
  constructor
  · obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D ρ m
    haveI : IsTopologicalAddGroup (Mx D ρ m) := i1
    haveI : LocallyCompactSpace (Mx D ρ m) := i2
    haveI : SecondCountableTopology (Mx D ρ m) := i3
    haveI : vb.μ.IsAddHaarMeasure := vb.covol.1
    haveI : SigmaFinite vb.μ := Measure.IsAddHaarMeasure.sigmaFinite _
    infer_instance
  · obtain ⟨i1, i2, -⟩ := GlobalTheory.UnitU.topology D ρ
    haveI : LocallyCompactSpace (UX D ρ) := i1
    haveI : SecondCountableTopology (UX D ρ) := i2
    haveI : vU.ν.IsHaarMeasure := vU.unit.1
    haveI : SigmaFinite vU.ν := Measure.IsHaarMeasure.sigmaFinite _
    haveI : ∀ n, Fact (vU.ν (disjointed (spanningSets vU.ν) n) < ⊤) :=
      fun n => ⟨(measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top vU.ν n)⟩
    exact ⟨⟨fun n => vU.ν.restrict (disjointed (spanningSets vU.ν) n), fun _ => inferInstance,
      (sum_restrict_disjointed_spanningSets vU.ν vU.ν).symm⟩⟩

end GlobalTheory.Unf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasuresStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sFinite_covolume_one_matrix_unitriangular_measures : ∀ (D : D7) (ρ m : ℕ) (vb : VolM D ρ m) (vU : VolU D ρ), SFinite vb.μ ∧ SFinite vU.ν := by
  first | exact @GlobalTheory.Unf.sFinite_vol | exact GlobalTheory.Unf.sFinite_vol | (intros; apply GlobalTheory.Unf.sFinite_vol <;> assumption)
end
end
