module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermBoundedDenominatorsMovedLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctions
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heisO_add_fun (S T : HSp D) (u : WO S T) (G H : WO S T → ℂ) :
    heisO ψ S T u (G + H) = heisO ψ S T u G + heisO ψ S T u H := by
  funext w
  simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_smul_fun (S T : HSp D) (u : WO S T) (c : ℂ) (G : WO S T → ℂ) :
    heisO ψ S T u (c • G) = c • heisO ψ S T u G := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous (isoPart V W C) := by
  unfold isoPart
  exact continuous_id.matrix_mul continuous_const

theorem integrableOn_heisO (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (u a : WO V W) :
    IntegrableOn (fun z => heisO ψ V W u G (isoPart V W C z + a)) 𝓨 μ := by
  obtain ⟨-, -, hvol⟩ := h
  obtain ⟨c, hc⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hcont : Continuous (fun z => heisO ψ V W u G (isoPart V W C z + a)) :=
    (GlobalTheory.HeisOrtho.continuous_heisO hψ.1 hG.cont u).comp ((continuous_isoPart V W C).add continuous_const)
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hfin : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  refine Integrable.of_bound hcont.aestronglyMeasurable c (Filter.Eventually.of_forall fun z => ?_)
  rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1]
  exact hc _

theorem term_linear : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ G H : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → term ψ V V' W C C' B μ 𝓨 (G + H) y = term ψ V V' W C C' B μ 𝓨 G y + term ψ V V' W C C' B μ 𝓨 H y) ∧ ∀ (c : ℂ) (G : WO V W → ℂ), IsThetaFunO ψ V W G → term ψ V V' W C C' B μ 𝓨 (c • G) y = c * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 h y
  have key : ∀ G, IsThetaFunO ψ V W G → IntegrableOn
      (fun z => heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G (isoPart V W C z + midPart V V' W B 0)) 𝓨 μ :=
    fun G hG => integrableOn_heisO V W C hψ h hG _ _
  refine ⟨fun G H hG hH => ?_, fun c G hG => ?_⟩
  · simp only [term, res, heisO_add_fun, Pi.add_apply]
    exact integral_add (key G hG) (key H hH)
  · simp only [term, res, heisO_smul_fun, Pi.smul_apply, smul_eq_mul]
    first
      | exact integral_const_mul c _
      | exact integral_mul_left c _

end GlobalTheory.MixedTerm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTerm_linear_thetaFunctions : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ G H : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → term ψ V V' W C C' B μ 𝓨 (G + H) y = term ψ V V' W C C' B μ 𝓨 G y + term ψ V V' W C C' B μ 𝓨 H y) ∧ ∀ (c : ℂ) (G : WO V W → ℂ), IsThetaFunO ψ V W G → term ψ V V' W C C' B μ 𝓨 (c • G) y = c * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTerm.term_linear | exact GlobalTheory.MixedTerm.term_linear | (intros; apply GlobalTheory.MixedTerm.term_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaTermsSummableHeightBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivAlongRationalPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivativeIsotropicDirection
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivativeIsotropicDirection
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm.IsoDeriv

variable {D : D7} {θ : InfFam D}

theorem isoPart_lineAt (hθ : IsInfFam θ) (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (t : ℝ) :
    isoPart V W C (lineAt θ τ z t) = lineAt θ τ (dirAt V W C τ z) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO V W :=
    { toFun := fun t => isoPart V W C (lineAt θ τ z t)
      map_zero' := by unfold isoPart; rw [AddMonoidHom.map_zero, Matrix.zero_mul]
      map_add' := fun s t => by unfold isoPart; rw [AddMonoidHom.map_add (f := _), Matrix.add_mul] }
  have hL' : IsLineAt θ τ (dirAt V W C τ z) L := by
    refine ⟨(continuous_isoPart V W C).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (isoPart V W C (lineAt θ τ z t)).map (finPart D) = 0
      unfold isoPart
      rw [Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' (isoPart V W C (lineAt θ τ z t)) = _
      unfold isoPart
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2]
      have e : compAt θ τ' ((adj D C * V.gram).map (incA D)) = (adj D C * V.gram).map (tauE D τ') := by
        unfold compAt
        rw [Matrix.map_map]
        congr 1
        funext e
        exact GlobalTheory.FockCompare.comp_incA hθ τ' e
      rw [e]
      split_ifs with h
      · subst h
        unfold dirAt
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

end GlobalTheory.MixedTerm.IsoDeriv

namespace GlobalTheory.MixedTerm.IsoDeriv

variable {D : D7} {θ : InfFam D}

theorem phase_lineAt (hθ : IsInfFam θ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hCC : adj D C * V.gram * C' = 1) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (t : ℝ) :
    phase ψ V W C C' y (lineAt θ τ z t) = Complex.exp (2 * Real.pi * Complex.I *
      ((t * (2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re) : ℝ) : ℂ)) := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  rw [GlobalTheory.T.mixedModelHeisenbergPhase_eq_cexp_realPoints D V W r C C' hCC ψ hψ θ hθ y _ (hL.2.1 t)]
  congr 4
  simp only [hL.2.2 t]
  rw [Finset.sum_eq_single τ (fun b _ hb => by rw [if_neg hb, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re,
    mul_zero]) (by simp), if_pos rfl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  ring

end GlobalTheory.MixedTerm.IsoDeriv

namespace GlobalTheory.MixedTerm.IsoDeriv

theorem term_dRho_dirAt : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y = (2 * Real.pi * Complex.I * ((2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hs hCC ψ hψ θ hθ μ 𝓨 h G hG τ z y
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re := ⟨_, rfl⟩
  rw [← hc]
  have hL'r := GlobalTheory.OrientedHeis.isRealDir_lineAt (S := V) (T := W) hθ τ (dirAt V W C τ z)

  have hg : ∀ t : ℝ, term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y =
      Complex.exp (2 * Real.pi * Complex.I * ((t * c : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := fun t => by
    rw [← isoPart_lineAt hθ V W C τ z t, GlobalTheory.T.mixedModelTerm_heisenbergIsotropic_character D V V' W r C C' B hs ψ hψ μ 𝓨 h G hG y _,
      phase_lineAt hθ V W C C' hCC hψ y τ z t, hc]
  have hd1 : HasDerivAt (fun t : ℝ => term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y)
      (2 * Real.pi * Complex.I * (c : ℂ) * term ψ V V' W C C' B μ 𝓨 G y) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * ((t * c : ℝ) : ℂ)) (2 * Real.pi * Complex.I * (c : ℂ)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp).const_mul (2 * Real.pi * Complex.I)
      simpa using this
    have h2 := (h1.cexp).mul_const (term ψ V V' W C C' B μ 𝓨 G y)
    rw [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
    exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hg t)

  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL'r hG)
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : heisO ψ V W (lineAt θ τ (dirAt V W C τ z) 0) (GlobalTheory.OrientedHeis.dLine ψ V W (lineAt θ τ (dirAt V W C τ z)) G) =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G := by
    rw [AddMonoidHom.map_zero, GlobalTheory.OrientedHeis.heisO_zero]
    rfl
  have hd2 : HasDerivAt (fun t : ℝ => term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y)
      (term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y) 0 := by
    rw [← e0]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓨) (x₀ := (0 : ℝ))
      (F' := fun t x => heisO ψ V W (isoPart V W C' (Matrix.map y (incA D)))
        (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t)
          (GlobalTheory.OrientedHeis.dLine ψ V W (lineAt θ τ (dirAt V W C τ z)) G)) (isoPart V W C x + midPart V V' W B 0))
      (bound := fun _ => K) (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const K) ?_).2
    · exact Filter.Eventually.of_forall fun t =>
        (integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 t) hG) _ _).aestronglyMeasurable
    · exact integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 0) hG) _ _
    · exact (integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 0)
        (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL'r hG)) _ _).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x t _ => ?_
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1, GlobalTheory.HeisOrtho.norm_heisO hψ.1]
      exact hK _
    · refine Filter.Eventually.of_forall fun x t _ => ?_
      exact (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL'r hG _ t).const_mul _
  rw [hd2.unique hd1]

end GlobalTheory.MixedTerm.IsoDeriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivativeIsotropicDirectionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTerm_derivative_isotropicDirection : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y = (2 * Real.pi * Complex.I * ((2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTerm.IsoDeriv.term_dRho_dirAt | exact GlobalTheory.MixedTerm.IsoDeriv.term_dRho_dirAt | (intros; apply GlobalTheory.MixedTerm.IsoDeriv.term_dRho_dirAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivAlongRationalPairing
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm

namespace GlobalTheory.MixedTerm.DerLaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_tauE_add_conj (D : D7) (e : D.host.E) :
    ∑ t, (tauE D t e + starRingEnd ℂ (tauE D t e)) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [Finset.sum_add_distrib, h4]

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  rw [← sum_tauE_add_conj]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

theorem trace_map_mul (D : D7) (τ : D.what₂.Tau) {m n : ℕ} (P : Matrix (Fin m) (Fin n) D.host.E)
    (x : Matrix (Fin n) (Fin m) D.host.E) :
    Matrix.trace (P.map (tauE D τ) * x.map (tauE D τ)) = tauE D τ (Matrix.trace (P * x)) := by
  rw [← Matrix.map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem term_derAlong : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ x y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 (derAlong ψ θ V W C x G) y = (2 * Real.pi * Complex.I * (ratPair W y x : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hiso hCC ψ hψ θ hθ μ 𝓨 hcov G hG x y
  have hlin := GlobalTheory.T.mixedModelTerm_linear_thetaFunctions D V V' W r C C' B ψ hψ μ 𝓨 hcov y
  have hder := fun τ => GlobalTheory.T.mixedModelTerm_derivative_isotropicDirection D V V' W r C C' B hiso hCC ψ hψ θ hθ μ 𝓨 hcov G hG τ (x.map (tauE D τ)) y
  set f : D.what₂.Tau → WO V W → ℂ :=
    fun τ => Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G with hf
  have hft : ∀ τ, IsThetaFunO ψ V W (f τ) := fun τ => GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hG
  have hsum : ∀ s : Finset D.what₂.Tau,
      term ψ V V' W C C' B μ 𝓨 (∑ τ ∈ s, f τ) y = ∑ τ ∈ s, term ψ V V' W C C' B μ 𝓨 (f τ) y := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      have h0 := hlin.2 0 G hG
      rw [zero_smul, zero_mul] at h0
      simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hlin.1 _ _ (hft a) (GlobalTheory.Size.theta_finsetSum s fun i _ => hft i), ih]
  show term ψ V V' W C C' B μ 𝓨 (∑ τ, f τ) y = _
  rw [hsum, Finset.sum_congr rfl fun τ _ => hder τ, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  simp only [trace_map_mul, sum_two_re_tauE, ratPair, Complex.ofReal_ratCast]

end GlobalTheory.MixedTerm.DerLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivAlongRationalPairingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTerm_derivAlong_rational_pairing : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ x y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 (derAlong ψ θ V W C x G) y = (2 * Real.pi * Complex.I * (ratPair W y x : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTerm.DerLaw.term_derAlong | exact GlobalTheory.MixedTerm.DerLaw.term_derAlong | (intros; apply GlobalTheory.MixedTerm.DerLaw.term_derAlong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EnormMixedModelTermLeISup
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EnormMixedModelTermLeISup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm

theorem enorm_term_le_iSup : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ ≤ ⨆ w, ‖G w‖ₑ := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 hμ G y
  have hψ1 : ∀ x, ‖(ψ x : ℂ)‖ₑ = 1 := fun x => by
    rw [← ofReal_norm_eq_enorm, hψ.1.2.1 x, ENNReal.ofReal_one]
  calc ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ
      ≤ ∫⁻ z in 𝓨, ‖heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G
          (isoPart V W C z + midPart V V' W B 0)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ _ in 𝓨, (⨆ w, ‖G w‖ₑ) ∂μ := by
        refine lintegral_mono fun z => ?_
        simp only [heisO, enorm_mul, hψ1, one_mul]
        exact le_iSup (fun w => ‖G w‖ₑ) _
    _ = ⨆ w, ‖G w‖ₑ := by rw [setLIntegral_const, hμ.2.2, mul_one]

end GlobalTheory.MixedTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EnormMixedModelTermLeISupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enorm_mixedModelTerm_le_iSup : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ ≤ ⨆ w, ‖G w‖ₑ := by
  first | exact @GlobalTheory.MixedTerm.enorm_term_le_iSup | exact GlobalTheory.MixedTerm.enorm_term_le_iSup | (intros; apply GlobalTheory.MixedTerm.enorm_term_le_iSup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumLeOfLatticeCoordsQuadraticDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumLeOfLatticeCoordsQuadraticDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped ENNReal

namespace GlobalTheory.TwBoundFour

def wt (N : ℕ) (c : ℤ) : ℝ≥0∞ := ENNReal.ofReal (1 / (1 + ((c : ℝ) / N) ^ 2))

lemma real_bound (N : ℕ) (hN : 0 < N) (y : ℝ) (hy : 0 < y) :
    1 / (1 + (y / N) ^ 2) ≤ (N:ℝ)^2 * (1 / y^2) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  field_simp
  nlinarith [sq_nonneg y, sq_nonneg (N:ℝ)]

lemma half_sum_le (N : ℕ) (hN : 0 < N) :
    ∑' m : ℕ, ENNReal.ofReal (1 / (1 + (((m:ℝ) + 1) / N) ^ 2)) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
  have hz : HasSum (fun m : ℕ => (1:ℝ) / ((m:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
    simpa using h
  have hz2 : HasSum (fun m : ℕ => (N:ℝ)^2 * (1 / ((m:ℝ) + 1) ^ 2)) ((N:ℝ)^2 * (Real.pi ^ 2 / 6)) :=
    hz.mul_left _
  calc ∑' m : ℕ, ENNReal.ofReal (1 / (1 + (((m:ℝ) + 1) / N) ^ 2))
      ≤ ∑' m : ℕ, ENNReal.ofReal ((N:ℝ)^2 * (1 / ((m:ℝ) + 1) ^ 2)) :=
        ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal (real_bound N hN _ (by positivity))
    _ = ENNReal.ofReal ((N:ℝ)^2 * (Real.pi ^ 2 / 6)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hz2.summable, hz2.tsum_eq]
    _ ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
        apply ENNReal.ofReal_le_ofReal
        have hp := Real.pi_lt_d2
        have hp0 := Real.pi_pos
        have : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith
        nlinarith [sq_nonneg (N:ℝ)]

lemma int_sum_le (N : ℕ) (hN : 0 < N) :
    ∑' c : ℤ, wt N c ≤ ENNReal.ofReal (5 * (N:ℝ)^2) := by
  rw [tsum_of_add_one_of_neg_add_one ENNReal.summable ENNReal.summable]
  have h1 : ∑' m : ℕ, wt N ((m:ℤ) + 1) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
    refine le_trans (le_of_eq ?_) (half_sum_le N hN)
    congr 1; funext m; simp [wt]
  have h2 : ∑' m : ℕ, wt N (-((m:ℤ) + 1)) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
    refine le_trans (le_of_eq ?_) (half_sum_le N hN)
    congr 1; funext m; unfold wt; congr 1; push_cast; ring
  have h0 : wt N 0 = 1 := by simp [wt]
  have hN1 : (1:ℝ) ≤ (N:ℝ)^2 := by
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  calc _ ≤ ENNReal.ofReal (2 * (N:ℝ)^2) + 1 + ENNReal.ofReal (2 * (N:ℝ)^2) := by
        rw [h0]; gcongr
    _ = ENNReal.ofReal (2 * (N:ℝ)^2 + 1 + 2 * (N:ℝ)^2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (5 * (N:ℝ)^2) := ENNReal.ofReal_le_ofReal (by linarith)

lemma pi_sum_le (n : ℕ) (f : ℤ → ℝ≥0∞) :
    ∑' c : Fin n → ℤ, ∏ j, f (c j) ≤ (∑' z, f z) ^ n := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  let t : Fin n → Finset ℤ := fun j => s.image (fun x => x j)
  have hs : s ⊆ Fintype.piFinset t := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_image_of_mem _ hx
  calc ∑ c ∈ s, ∏ j, f (c j) ≤ ∑ c ∈ Fintype.piFinset t, ∏ j, f (c j) :=
        Finset.sum_le_sum_of_subset hs
    _ = ∏ j, ∑ z ∈ t j, f z := (Finset.prod_univ_sum t (fun _ z => f z)).symm
    _ ≤ ∏ _j : Fin n, ∑' z, f z := Finset.prod_le_prod' fun j _ => ENNReal.sum_le_tsum _
    _ = (∑' z, f z) ^ n := by simp

theorem tsum_le {Y : Type} (n N : ℕ) (hN : 0 < N) (a : Y → ENNReal) (T : Fin n → Y → ℝ)
    (hinj : ∀ y y', a y ≠ 0 → a y' ≠ 0 → (∀ j, T j y = T j y') → y = y')
    (hint : ∀ y, a y ≠ 0 → ∀ j, ∃ c : ℤ, (N : ℝ) * T j y = c) (S : ENNReal)
    (hS : ∀ y, a y * ∏ j, ENNReal.ofReal (1 + T j y ^ 2) ≤ S) :
    ∑' y, a y ≤ S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
  classical
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let cf : Function.support a → Fin n → ℤ := fun y j => Classical.choose (hint y.1 y.2 j)
  have hcf : ∀ (y : Function.support a) j, (N : ℝ) * T j y.1 = cf y j :=
    fun y j => Classical.choose_spec (hint y.1 y.2 j)
  have hT : ∀ (y : Function.support a) j, T j y.1 = (cf y j : ℝ) / N := fun y j => by
    rw [eq_div_iff hN', mul_comm]; exact hcf y j
  have hcinj : Function.Injective cf := by
    intro y y' h
    apply Subtype.ext
    apply hinj y.1 y'.1 y.2 y'.2
    intro j
    rw [hT y j, hT y' j, h]
  have hbound : ∀ y : Function.support a, a y.1 ≤ S * ∏ j, wt N (cf y j) := by
    intro y
    have hP : (∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun j _ => ?_
      have hpos : (0:ℝ) < 1 + T j y.1 ^ 2 := by positivity
      rw [wt, ← hT y j, ← ENNReal.ofReal_mul hpos.le, mul_one_div_cancel hpos.ne', ENNReal.ofReal_one]
    calc a y.1 = a y.1 * ((∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j)) := by
          rw [hP, mul_one]
      _ = (a y.1 * ∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j) := by
          rw [mul_assoc]
      _ ≤ S * ∏ j, wt N (cf y j) := by gcongr; exact hS y.1
  rw [← tsum_subtype_support]
  calc ∑' y : Function.support a, a y.1 ≤ ∑' y : Function.support a, S * ∏ j, wt N (cf y j) :=
        ENNReal.tsum_le_tsum hbound
    _ = S * ∑' y : Function.support a, ∏ j, wt N (cf y j) := ENNReal.tsum_mul_left
    _ ≤ S * ∑' c : Fin n → ℤ, ∏ j, wt N (c j) := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hcinj (fun c => ∏ j, wt N (c j))
    _ ≤ S * (∑' z, wt N z) ^ n := by gcongr; exact pi_sum_le n (wt N)
    _ ≤ S * ENNReal.ofReal (5 * (N:ℝ)^2) ^ n := by gcongr; exact int_sum_le N hN
    _ = S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
        rw [ENNReal.ofReal_pow (by positivity)]

end GlobalTheory.TwBoundFour
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumLeOfLatticeCoordsQuadraticDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_le_of_lattice_coords_quadraticDecay : ∀ {Y : Type} (n N : ℕ), 0 < N → ∀ (a : Y → ENNReal) (T : Fin n → Y → ℝ), (∀ y y', a y ≠ 0 → a y' ≠ 0 → (∀ j, T j y = T j y') → y = y') → (∀ y, a y ≠ 0 → ∀ j, ∃ c : ℤ, (N : ℝ) * T j y = c) → ∀ S : ENNReal, (∀ y, a y * ∏ j, ENNReal.ofReal (1 + T j y ^ 2) ≤ S) → ∑' y, a y ≤ S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
  first | exact @GlobalTheory.TwBoundFour.tsum_le | exact GlobalTheory.TwBoundFour.tsum_le | (intros; apply GlobalTheory.TwBoundFour.tsum_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralMatricesSeparatingRationalPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralMatricesSeparatingRationalPairing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatPairSep

variable {D : D7}

theorem eq_zero_of_trace_integralBasis (D : D7) (q : D.host.E)
    (h : ∀ k, Algebra.trace ℚ D.host.E (q * integralBasis D.host.E k) = 0) : q = 0 := by
  refine (traceForm_nondegenerate ℚ D.host.E).1 q fun z => ?_
  have hl : (Algebra.traceForm ℚ D.host.E) q = 0 :=
    (integralBasis D.host.E).ext fun k => by
      rw [LinearMap.zero_apply, Algebra.traceForm_apply]; exact h k
  rw [hl, LinearMap.zero_apply]

theorem pairQ_sub (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E) :
    pairQ W y - pairQ W y' = pairQ W (y - y') := by
  have : adj D (y - y') = adj D y - adj D y' := by
    ext i j; simp [adj, Formalism.UG.cT]
  simp only [pairQ, this, Matrix.sub_mul, smul_sub]

theorem eq_of_pairQ_eq (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E)
    (h : pairQ W y = pairQ W y') : y = y' := by
  have h1 : adj D y * W.gram = adj D y' * W.gram := by
    have := congrArg (fun M => (D.host.xi0)⁻¹ • M) h
    simpa [pairQ, smul_smul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)] using this
  have h2 : adj D y = adj D y' := by
    have := congrArg (fun M => M * W.gram⁻¹) h1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit W)] using this
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h2 j) i
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact (D.sp.cm.sig : D.host.E →+* D.host.E).injective this

theorem exists_sep (D : D7) (W : HSp D) (r : ℕ) :
    ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E), (∀ j a b, IsIntegral ℤ (X j a b)) ∧
      ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := by
  let ι := Fin W.rank × Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)
  let e := Fintype.equivFin ι
  let Y : ι → Matrix (Fin W.rank) (Fin r) D.host.E := fun t => Matrix.single t.1 t.2.1 (integralBasis D.host.E t.2.2)
  refine ⟨Fintype.card ι, fun j => Y (e.symm j), ?_, ?_⟩
  · intro j a b
    simp only [Y, Matrix.single_apply]
    split_ifs
    · rw [integralBasis_apply]; exact (RingOfIntegers.basis D.host.E _).isIntegral_coe
    · exact isIntegral_zero
  · intro y y' h
    apply eq_of_pairQ_eq W y y'
    rw [← sub_eq_zero, pairQ_sub]
    refine Matrix.ext fun l i => ?_
    rw [Matrix.zero_apply]
    refine eq_zero_of_trace_integralBasis D _ fun k => ?_
    have hj := h (e (i, l, k))
    simp only [ratPair, Equiv.symm_apply_apply, Y, Rat.cast_inj] at hj
    rw [← sub_eq_zero, ← map_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, pairQ_sub,
      Matrix.trace_mul_single] at hj
    simpa [MulOpposite.smul_eq_mul_unop] using hj

end GlobalTheory.RatPairSep

theorem GlobalTheory.RatPairSep.main : ∀ (D : D7) (W : HSp D) (r : ℕ), ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E),
    (∀ j a b, IsIntegral ℤ (X j a b)) ∧ ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E,
    (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := GlobalTheory.RatPairSep.exists_sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralMatricesSeparatingRationalPairingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_matrices_separating_rationalPairing : ∀ (D : D7) (W : HSp D) (r : ℕ), ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E), (∀ j a b, IsIntegral ℤ (X j a b)) ∧ ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := by
  first | exact @GlobalTheory.RatPairSep.main | exact GlobalTheory.RatPairSep.main | (intros; apply GlobalTheory.RatPairSep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaTermsSummableHeightBound
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

namespace GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev supWord (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (k : ℕ) (G : WO V W → ℂ) : ℝ≥0∞ :=
  GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k G

theorem enorm_real_cast {a : ℝ} (h : 0 ≤ a) : ‖(a : ℂ)‖ₑ = ENNReal.ofReal a := by
  rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg h]

def opAlong (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E) (G : WO V W → ℂ) : WO V W → ℂ :=
  G - (((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) • derAlong ψ θ V W C x (derAlong ψ θ V W C x G)

theorem theta_derAlong {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E)
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) : IsThetaFunO ψ V W (derAlong ψ θ V W C x G) := by
  obtain ⟨U, -, hU⟩ := GlobalTheory.Size.isTheta_iff_level.mp hG
  unfold derAlong
  exact GlobalTheory.Size.theta_finsetSum Finset.univ fun τ _ => (GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ hU τ _).1

theorem theta_sub_smul {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {G H : WO V W → ℂ} (c : ℂ)
    (hG : IsThetaFunO ψ V W G) (hH : IsThetaFunO ψ V W H) : IsThetaFunO ψ V W (G - c • H) := by
  have h := GlobalTheory.OrientedHeis.theta_add hG (GlobalTheory.OrientedHeis.theta_smul (-c) hH)
  rwa [neg_smul, ← sub_eq_add_neg] at h

theorem term_opAlong {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (x y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C x G) y =
      ((1 + ratPair W y x ^ 2 : ℝ) : ℂ) * term ψ V V' W C C' B μ 𝓨 G y := by
  have hG1 := theta_derAlong hψ hθ C x hG
  have hG2 := theta_derAlong hψ hθ C x hG1
  obtain ⟨hadd, hsmul⟩ := GlobalTheory.T.mixedModelTerm_linear_thetaFunctions D V V' W r C C' B ψ hψ μ 𝓨 hμ y
  have e1 := GlobalTheory.T.mixedModelTerm_derivAlong_rational_pairing D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ G hG x y
  have e2 := GlobalTheory.T.mixedModelTerm_derivAlong_rational_pairing D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ _ hG1 x y
  have hsplit : opAlong ψ θ V W C x G = G + (-(((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) •
      derAlong ψ θ V W C x (derAlong ψ θ V W C x G) := by
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  rw [hsplit, hadd _ _ hG (GlobalTheory.OrientedHeis.theta_smul _ hG2), hsmul _ _ hG2, e2, e1]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (4 * (Real.pi : ℂ) ^ 2)⁻¹ * (4 * (Real.pi : ℂ) ^ 2) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ))
  push_cast
  linear_combination (-(ratPair W y x : ℂ) ^ 2 * term ψ V V' W C C' B μ 𝓨 G y * Complex.I ^ 2) * hc +
    (-(ratPair W y x : ℂ) ^ 2 * term ψ V V' W C C' B μ 𝓨 G y) * Complex.I_sq

theorem term_decay {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    (l : List (Matrix (Fin W.rank) (Fin r) D.host.E)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ y,
      ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ * (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod ≤
        ENNReal.ofReal K * supWord ψ θ V W (2 * l.length) G := by
  induction l with
  | nil =>
    refine ⟨1, zero_le_one, fun G _ y => ?_⟩
    simp only [List.map_nil, List.prod_nil, mul_one, ENNReal.ofReal_one, one_mul, List.length_nil,
      mul_zero]
    unfold supWord
    rw [GlobalTheory.Size.wordSum_zero]
    exact GlobalTheory.T.enorm_mixedModelTerm_le_iSup D V V' W r C C' B ψ hψ μ 𝓨 hμ G y
  | cons a l ih =>
    obtain ⟨K, hK, hb⟩ := ih
    obtain ⟨hsub, hder⟩ := GlobalTheory.T.supNormWordSum_sub_le_and_derivative_cost D V W ψ hψ θ hθ
    obtain ⟨c₀, hc₀, hd⟩ := hder r C a
    have he0 : (0 : ℝ) ≤ (4 * Real.pi ^ 2)⁻¹ := by positivity
    refine ⟨K * (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀), by positivity, fun G hG y => ?_⟩
    have hG1 := theta_derAlong hψ hθ C a hG
    have hG2 := theta_derAlong hψ hθ C a hG1
    have hop : IsThetaFunO ψ V W (opAlong ψ θ V W C a G) :=
      theta_sub_smul ((((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) hG hG2
    have hp : (0 : ℝ) ≤ 1 + ratPair W y a ^ 2 := by positivity
    have hterm : ‖term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C a G) y‖ₑ =
        ENNReal.ofReal (1 + ratPair W y a ^ 2) * ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ := by
      rw [term_opAlong hs h1 hψ hθ hμ hG a y, enorm_mul, enorm_real_cast hp]
    have hlen : 2 * (a :: l).length = 2 * l.length + 1 + 1 := by
      simp only [List.length_cons]
      ring
    have hsize : supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G) ≤
        ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) * supWord ψ θ V W (2 * (a :: l).length) G := by
      rw [hlen]
      have s1 := hsub G _ ((((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) (2 * l.length) hG hG2
      have s2 := hd _ hG1 (2 * l.length)
      have s3 := hd G hG (2 * l.length + 1)
      have s4 := GlobalTheory.Size.wordSum_mono (A := GlobalTheory.Size.heisDer ψ θ)
        (p := fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (show 2 * l.length ≤ 2 * l.length + 1 + 1 by omega) G
      rw [enorm_real_cast he0] at s1
      calc supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G)
          ≤ supWord ψ θ V W (2 * l.length) G + ENNReal.ofReal (4 * Real.pi ^ 2)⁻¹ *
              supWord ψ θ V W (2 * l.length) (derAlong ψ θ V W C a (derAlong ψ θ V W C a G)) := s1
        _ ≤ supWord ψ θ V W (2 * l.length + 1 + 1) G + ENNReal.ofReal (4 * Real.pi ^ 2)⁻¹ *
              (ENNReal.ofReal c₀ * (ENNReal.ofReal c₀ * supWord ψ θ V W (2 * l.length + 1 + 1) G)) := by
            gcongr
            exact s2.trans (by gcongr)
        _ = ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) * supWord ψ θ V W (2 * l.length + 1 + 1) G := by
            rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul he0]
            ring
    rw [List.map_cons, List.prod_cons]
    calc ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ * (ENNReal.ofReal (1 + ratPair W y a ^ 2) *
          (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod)
        = ‖term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C a G) y‖ₑ *
          (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod := by
          rw [hterm]
          ring
      _ ≤ ENNReal.ofReal K * supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G) := hb _ hop y
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) *
          supWord ψ θ V W (2 * (a :: l).length) G) := by gcongr
      _ = ENNReal.ofReal (K * (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀)) *
          supWord ψ θ V W (2 * (a :: l).length) G := by
          rw [ENNReal.ofReal_mul hK]
          ring

theorem mixed_terms_bound : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A d : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : ℝ, ∀ (g : GA D V) (h : GA D W) (F : WO V W → ℂ), IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) F) 0‖ₑ ≤ ENNReal.ofReal (K * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) d F := by
  intro D V V' W r C C' B hs h1 _ _ ψ hψ θ hθ μ 𝓨 hμ
  obtain ⟨e, he⟩ := GlobalTheory.T.mixedModelTerm_bounded_denominators_moved_level D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ
  obtain ⟨n, X, hXint, hXsep⟩ := GlobalTheory.T.exists_integral_matrices_separating_rationalPairing D W r
  obtain ⟨K₀, hK₀, hdec⟩ := term_decay hs h1 hψ hθ hμ (List.ofFn X)
  refine ⟨2 * e * n, 2 * n, fun U hU => ?_⟩
  obtain ⟨M, _, hN⟩ := he U hU
  refine ⟨K₀ * (5 * (M : ℝ) ^ 2) ^ n, fun g h F hF hfix => ?_⟩
  obtain ⟨N, hNpos, hNle, hint⟩ := hN g h
  have hg1 := (GlobalTheory.Size.height_laws V).1 g
  have hh1 := (GlobalTheory.Size.height_laws W).1 h
  have ht0 : (0 : ℝ) ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h :=
    mul_nonneg (by linarith) (by linarith)
  have hbound := GlobalTheory.T.tsum_le_of_lattice_coords_quadraticDecay (Y := Matrix (Fin W.rank) (Fin r) D.host.E) n N hNpos
    (fun y => ‖term ψ V V' W C C' B μ 𝓨 F y‖ₑ) (fun j y => ratPair W y (X j))
    (fun y y' _ _ hyy => hXsep y y' hyy)
    (fun y hy j => hint F hF hfix y (enorm_ne_zero.mp hy) (X j) (hXint j))
    (ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F)
    (fun y => by
      have hy := hdec F hF y
      rw [List.map_ofFn, List.prod_ofFn, List.length_ofFn] at hy
      exact hy)
  have hNM : (5 * (N : ℝ) ^ 2) ^ n ≤
      (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n) := by
    calc (5 * (N : ℝ) ^ 2) ^ n
        ≤ (5 * ((M : ℝ) * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e) ^ 2) ^ n := by gcongr
      _ = (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n) := by ring
  show ∑' y, ‖term ψ V V' W C C' B μ 𝓨 F y‖ₑ ≤ _
  refine hbound.trans ?_
  calc ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n)
      ≤ ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F * ENNReal.ofReal ((5 * (M : ℝ) ^ 2) ^ n *
          (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n)) := by gcongr
    _ = ENNReal.ofReal (K₀ * (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n)) *
          supWord ψ θ V W (2 * n) F := by
        rw [mul_assoc K₀, ENNReal.ofReal_mul hK₀]
        ring

end GlobalTheory.MixedTerm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaTermsSummableHeightBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelThetaTerms_summable_heightBound : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A d : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : ℝ, ∀ (g : GA D V) (h : GA D W) (F : WO V W → ℂ), IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) F) 0‖ₑ ≤ ENNReal.ofReal (K * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) d F := by
  first | exact @GlobalTheory.MixedTerm.mixed_terms_bound | exact GlobalTheory.MixedTerm.mixed_terms_bound | (intros; apply GlobalTheory.MixedTerm.mixed_terms_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedHeisenbergWeilTranslateAtZer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedHeisenbergWeilTranslateAtZer
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResHeisCont

theorem continuous_res_heisO : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ u : WO V W, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W u (ω p f)) 0 := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 h𝓨 f hf u
  have hψ := hω.std.1
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).1
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h𝓨.2.2]; exact ENNReal.one_lt_top⟩
  have hy : Continuous fun y : Mx D W.rank r => isoPart V W C y + midPart V V' W B 0 := by
    unfold isoPart
    exact (continuous_id.matrix_mul continuous_const).add continuous_const
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds p₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ V W χS χT ω hω f hf K hK
  unfold res
  refine continuousAt_of_dominated (bound := fun _ => c) ?_ ?_ (integrable_const c) ?_
  · exact Filter.Eventually.of_forall fun p =>
      ((GlobalTheory.HeisOrtho.continuous_heisO hψ (hω.om_pres p f hf).cont u).comp hy).aestronglyMeasurable
  · filter_upwards [hKn] with p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ]; exact hc p hp _
  · refine Filter.Eventually.of_forall fun y => ?_
    unfold heisO
    exact (continuous_const.mul (hω.om_cont f hf _)).continuousAt

end GlobalTheory.ResHeisCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedHeisenbergWeilTranslateAtZerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_restrictedHeisenbergWeilTranslate_at_zero : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ u : WO V W, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W u (ω p f)) 0 := by
  first | exact @GlobalTheory.ResHeisCont.continuous_res_heisO | exact GlobalTheory.ResHeisCont.continuous_res_heisO | (intros; apply GlobalTheory.ResHeisCont.continuous_res_heisO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaSeriesModerateGrowth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedSeriesGrowth

theorem mixed_series_growth : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, ∀ (g : GA D V) (h : GA D W), (∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω p f)) 0) ∧ ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (g, h) f)) 0‖ₑ ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) := by
  intro D V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hμ
  obtain ⟨⟨θ, hθ⟩, -, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨A₁, d, hF⟩ := GlobalTheory.T.mixedModelThetaTerms_summable_heightBound D V V' W r C C' B hs h1 h2 h3 ψ hω.std θ hθ μ 𝓨 hμ
  obtain ⟨A₂, hS⟩ := GlobalTheory.T.heisenbergWords_weilOperator_supNorm_polynomialGrowth D ψ V W χS χT ω hω θ hθ d
  refine ⟨A₁ + A₂, fun f hf => ?_⟩
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K, hK⟩ := hF U hU
  obtain ⟨c, hc⟩ := hS f hf
  refine ⟨max K 0 * max c 0, fun g h => ⟨fun y => GlobalTheory.T.continuous_restrictedHeisenbergWeilTranslate_at_zero D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ f hf _, ?_⟩⟩
  have hH : 0 ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h :=
    mul_nonneg (GlobalTheory.Grow.height_pos V g).le (GlobalTheory.Grow.height_pos W h).le
  refine (hK g h (ω (g, h) f) (hω.om_pres _ f hf) (fun u hu h0 => ?_)).trans ?_
  · rw [← hω.om_heis g h u f hf, hl u hu h0]
  · refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left K 0) (pow_nonneg hH _)))
      ((hc g h).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left c 0)
        (pow_nonneg hH _))))).trans_eq ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right K 0) (pow_nonneg hH _)), pow_add]
    congr 1; ring

end GlobalTheory.MixedSeriesGrowth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaSeriesModerateGrowthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModel_thetaSeries_moderate_growth : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, ∀ (g : GA D V) (h : GA D W), (∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω p f)) 0) ∧ ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (g, h) f)) 0‖ₑ ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) := by
  first | exact @GlobalTheory.MixedSeriesGrowth.mixed_series_growth | exact GlobalTheory.MixedSeriesGrowth.mixed_series_growth | (intros; apply GlobalTheory.MixedSeriesGrowth.mixed_series_growth <;> assumption)
end
