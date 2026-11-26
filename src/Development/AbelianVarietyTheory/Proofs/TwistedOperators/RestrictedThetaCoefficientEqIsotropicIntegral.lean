module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroAtZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffAdelicIsotropicPart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoeffIsotropicTranslatesEqFourierCoeffs
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoeffIsotropicTranslatesEqFourierCoeffs
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCoefUnfold

theorem pcoef : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ (y : Mx D W.rank r) (a : Matrix (Fin W.rank) (Fin r) D.host.E), (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = ∫ t in 𝓨, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * (κ • (∫ y' in 𝓨, ∫ x in 𝓕', (heisO ψ V W (isoPart V W C y) F) (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ)) ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μV 𝓕V hμV h𝓕V μ' 𝓕' hμ' h𝓕' κ hκ F G hF hG y a
  have hth := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W
  have horth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hPt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) := hth.1 _ F hF
  have hγrat : isoPart V W C (a.map (incA D)) ∈ ratL W V := by
    rw [← GlobalTheory.TwistEquiRat.ratW_eq_isoPart]; exact ⟨_, rfl⟩
  have hfirst : heisO ψ V W (isoPart V W C (y + a.map (incA D))) F =
      heisO ψ V W (isoPart V W C (a.map (incA D))) (heisO ψ V W (isoPart V W C y) F) := by
    rw [hth.2.1, GlobalTheory.TwistEquiRat.symplOH_isoPart V W C hs.frame, AddChar.map_zero_eq_one, one_smul,
      GlobalTheory.TwistEquiRat.isoPart_add, add_comm]
  have hpt : ∀ w, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) =
      ψ (symplO V W w (isoPart V W C (a.map (incA D)))) * (heisO ψ V W (isoPart V W C y) F w * star (G w)) := by
    intro w
    rw [hfirst, GlobalTheory.ThetaSchur.heisO_rat hPt hγrat]
    ring
  have hsym : ∀ t y' x, symplO V W (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)
      (isoPart V W C (a.map (incA D))) = symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))) := by
    intro t y' x
    rw [GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left, horth.1 y' _,
      GlobalTheory.PlaceModel.symplO_skew V W (isoPart V W C (a.map (incA D))) (midPart V V' W B x), horth.2.1 _ x]
    simp
  have hHt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C (y + a.map (incA D))) F) := hth.1 _ F hF
  have hHc : Continuous fun w => heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) :=
    hHt.cont.mul hG.cont.star
  have hHb : ∃ b : ℝ, ∀ w, ‖heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w)‖ ≤ b := by
    obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn hHc.continuousOn
    refine ⟨b, fun w => ?_⟩
    obtain ⟨g, hg, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w]
    exact hb _ h
  have key := hκ _ hHc hHb (fun g hg w => GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w)
  rw [key]
  simp_rw [hpt, hsym, integral_const_mul]
  rw [← integral_smul]
  congr 1
  funext t
  rw [mul_smul_comm]

end GlobalTheory.TwistCoefUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoeffIsotropicTranslatesEqFourierCoeffsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixCoeff_isotropicTranslates_eq_fourierCoeffs : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ (y : Mx D W.rank r) (a : Matrix (Fin W.rank) (Fin r) D.host.E), (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = ∫ t in 𝓨, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * (κ • (∫ y' in 𝓨, ∫ x in 𝓕', (heisO ψ V W (isoPart V W C y) F) (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ)) ∂μ := by
  first | exact @GlobalTheory.TwistCoefUnfold.pcoef | exact GlobalTheory.TwistCoefUnfold.pcoef | (intros; apply GlobalTheory.TwistCoefUnfold.pcoef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicPartRationalCharactersAdelicMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicPartRationalCharactersAdelicMatrices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoDualChars

variable {D : D7}

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y y' : Mx D W.rank r) :
    isoPart V W C (y + y') = isoPart V W C y + isoPart V W C y' := by
  simp only [isoPart, Matrix.add_mul]

theorem isoPart_zero (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    isoPart V W C 0 = 0 := by
  simp only [isoPart, Matrix.zero_mul]

theorem midPart_zero (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    midPart V V' W B 0 = 0 := by
  simp only [midPart, Matrix.zero_mul]

theorem continuous_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous fun y : Mx D W.rank r => isoPart V W C y := by
  unfold isoPart
  exact continuous_id.matrix_mul continuous_const

theorem symplO_smul_left' (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T (c • x) y = c * symplO S T x y := by
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.SplitScalar.symplOH_add_self,
    GlobalTheory.FinTranslate.symplOH_smul_left, mul_add]

theorem symplO_smul_right' (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = c * symplO S T x y := by
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.SplitScalar.symplOH_add_self,
    GlobalTheory.FinTranslate.symplOH_smul_right, mul_add]

theorem trace_incA' (x : D.host.E) : Algebra.trace (AF D.host.F) (AE D) (incA D x) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) := by
  show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem exists_pair_ne_one (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (c : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hc : c ≠ 0) :
    ∃ w : WO S T, ψ (symplO S T (c.map (incA D)) w) ≠ 1 := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, c i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (Matrix.ext h)
  obtain ⟨x₀, hx₀⟩ := hψ.1.2.2.2
  set q : D.host.F := Algebra.trace D.host.F D.host.E 1 with hq
  have hq0 : q ≠ 0 := by
    rw [hq, ← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    exact_mod_cast (Module.finrank_pos (R := D.host.F) (M := D.host.E)).ne'
  set s : AF D.host.F := x₀ * algebraMap D.host.F (AF D.host.F) q⁻¹
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.RatAnnih.exists_symplO_eq S T (s • c.map (incA D)) i j (c i j)⁻¹
  refine ⟨s • γ, ?_⟩
  have h1 : symplO S T (c.map (incA D)) (s • γ) = x₀ := by
    rw [symplO_smul_right', ← symplO_smul_left', hγ, Matrix.smul_apply, Matrix.map_apply, mul_smul_comm,
      map_smul, ← map_mul, inv_mul_cancel₀ hij, trace_incA', smul_eq_mul, ← hq, mul_assoc, ← map_mul,
      inv_mul_cancel₀ hq0, map_one, mul_one]
  rw [h1]
  exact hx₀

end GlobalTheory.IsoDualChars

namespace GlobalTheory.IsoDualChars


open GlobalTheory.LatVac in
theorem chars : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E), Continuous fun t : Mx D W.rank r => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E) t s, ψ (symplO V W (isoPart V W C' (t + s)) (isoPart V W C (a.map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' s) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a b : Matrix (Fin W.rank) (Fin r) D.host.E) t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C ((a + b).map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' t) (isoPart V W C (b.map (incA D))))) ∧ (∀ t, (∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) ↔ t ∈ ratMx D W.rank r) ∧ ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) → a = 0 := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ
  obtain ⟨e, he, hrat⟩ := GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition D V V' W r C B hs C' h1 h2 h3
  obtain ⟨oII, oIM, oDM, oDD⟩ := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hs C' h1 h2 h3
  have hdual : ∀ t, isoPart V W C' t = e (t, 0, 0) := fun t => by
    rw [he, isoPart_zero, midPart_zero, add_zero, add_zero]
  have hiso : ∀ y, isoPart V W C y = e (0, y, 0) := fun y => by
    rw [he, isoPart_zero, midPart_zero, add_zero, zero_add]
  have hmapr : ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, a.map (incA D) ∈ ratMx D W.rank r := fun a => ⟨a, rfl⟩
  refine ⟨fun a => ?_, fun a t s => ?_, fun a b t => ?_, fun t => ?_, fun a ha => ?_⟩
  · exact hψ.1.1.comp (GlobalTheory.SplitScalar.continuous_symplO V W (continuous_isoPart V W C') continuous_const)
  · rw [isoPart_add, symplO_add_left, AddChar.map_add_eq_mul]
  · rw [Matrix.map_add _ (map_add (incA D)), isoPart_add, symplO_add_right, AddChar.map_add_eq_mul]
  · constructor
    · intro h
      have hmem : isoPart V W C' t ∈ ratL W V := by
        refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).1 fun γ hγ => ?_
        obtain ⟨⟨t₀, y₀, x₀⟩, rfl⟩ := e.surjective γ
        obtain ⟨-, ⟨a₀, rfl⟩, -⟩ := (hrat t₀ _ x₀).1 hγ
        rw [he, symplO_add_right, symplO_add_right, oDD, oDM, zero_add, add_zero]
        exact h a₀
      rw [hdual] at hmem
      exact ((hrat t 0 0).1 hmem).1
    · intro ht a
      have hx : isoPart V W C' t ∈ ratL W V := by
        rw [hdual]; exact (hrat t 0 0).2 ⟨ht, zero_mem _, zero_mem _⟩
      have hy : isoPart V W C (a.map (incA D)) ∈ ratL W V := by
        rw [hiso]; exact (hrat 0 _ 0).2 ⟨zero_mem _, hmapr a, zero_mem _⟩
      exact (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).2 hx _ hy
  · set z := isoPart V W C (a.map (incA D)) with hz
    have hall : ∀ w : WO V W, ψ (symplO V W z w) = 1 := fun w => by
      obtain ⟨⟨t, y, x⟩, rfl⟩ := e.surjective w
      have hskew : symplO V W z (e (t, y, x)) = -symplO V W (e (t, y, x)) z := by
        exact GlobalTheory.SplitScalar.symplO_skew V W _ _
      rw [hskew, he, symplO_add_left, symplO_add_left, hz, oII, GlobalTheory.SplitScalar.symplO_skew V W _ (midPart V V' W B x),
        oIM, neg_zero, add_zero, add_zero, AddChar.map_neg_eq_inv, ha t, inv_one]
    have hzc : z = (a * (adj D C * V.gram)).map (incA D) := by
      simp only [hz, isoPart, Matrix.map_mul]
    by_contra ha0
    have hc : a * (adj D C * V.gram) ≠ 0 := by
      intro h0
      apply ha0
      calc a = a * (adj D C * V.gram * C') := by rw [h1, Matrix.mul_one]
        _ = a * (adj D C * V.gram) * C' := (Matrix.mul_assoc _ _ _).symm
        _ = 0 := by rw [h0, Matrix.zero_mul]
    obtain ⟨w, hw⟩ := exists_pair_ne_one ψ hψ V W _ hc
    rw [← hzc] at hw
    exact hw (hall w)

end GlobalTheory.IsoDualChars
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicPartRationalCharactersAdelicMatricesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_part_rational_characters_adelic_matrices : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E), Continuous fun t : Mx D W.rank r => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E) t s, ψ (symplO V W (isoPart V W C' (t + s)) (isoPart V W C (a.map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' s) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a b : Matrix (Fin W.rank) (Fin r) D.host.E) t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C ((a + b).map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' t) (isoPart V W C (b.map (incA D))))) ∧ (∀ t, (∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) ↔ t ∈ ratMx D W.rank r) ∧ ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) → a = 0 := by
  first | exact @GlobalTheory.IsoDualChars.chars | exact GlobalTheory.IsoDualChars.chars | (intros; apply GlobalTheory.IsoDualChars.chars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProductMeanContinuousPeriodicDualVariable
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProductMeanContinuousPeriodicDualVariable
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistThetaMean

variable {D : D7}

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a b : Mx D W.rank r) :
    isoPart V W C (a + b) = isoPart V W C a + isoPart V W C b :=
  Matrix.add_mul _ _ _

theorem isoPart_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {γ : Mx D W.rank r}
    (hγ : γ ∈ ratMx D W.rank r) : isoPart V W C γ ∈ ratL W V := by
  obtain ⟨g, rfl⟩ := hγ
  refine ⟨g * (adj D C * V.gram), ?_⟩
  show (g * (adj D C * V.gram)).map (incA D) = g.map (incA D) * (adj D C * V.gram).map (incA D)
  exact Matrix.map_mul

theorem isoPart_continuous (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous (isoPart V W C) :=
  continuous_id.matrix_mul continuous_const

theorem midPart_continuous (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    Continuous (midPart V V' W B) :=
  continuous_id.matrix_mul continuous_const

end GlobalTheory.TwistThetaMean

namespace GlobalTheory.TwistThetaMean

theorem integral_continuous_of_bounded {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : X × Y → ℂ) (hk : Continuous k) (b : ℝ) (hb : ∀ q, ‖k q‖ ≤ b) :
    Continuous (fun p => ∫ y, k (p, y) ∂ν) ∧ ∀ p, ‖∫ y, k (p, y) ∂ν‖ ≤ b * ν.real Set.univ := by
  refine ⟨continuous_of_dominated (bound := fun _ => b) (fun p => ?_) (fun p => ?_) (integrable_const _) ?_,
    fun p => norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => hb _)⟩
  · exact (hk.comp (Continuous.prodMk_right p)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hb _
  · exact Filter.Eventually.of_forall fun y => hk.comp (Continuous.prodMk_left y)

end GlobalTheory.TwistThetaMean

namespace GlobalTheory.TwistThetaMean


open TopologicalSpace in
theorem mean_continuous_periodic : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ P G, IsThetaFunO ψ V W P → IsThetaFunO ψ V W G → Continuous (fun t : Mx D W.rank r => ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) ∧ ∀ γ ∈ ratMx D W.rank r, ∀ t : Mx D W.rank r, (∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  intro D V V' W r C B _hs C' _h1 _h2 _h3 ψ hψ μ 𝓨 hY μ' 𝓕' hμ' h𝓕' P G hP hG
  haveI hAE : SecondCountableTopology (AE D) := by
    have : SecondCountableTopology (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
    have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E)
      (AF D.host.F)
    exact e.secondCountableTopology
  haveI hM : SecondCountableTopology (Mx D W.rank r) :=
    inferInstanceAs (SecondCountableTopology (Fin W.rank → Fin r → AE D))
  haveI hM2 : SecondCountableTopology (Mx D W.rank r × Mx D W.rank r) :=
    @instSecondCountableTopologyProd _ _ _ _ hM hM
  haveI : FirstCountableTopology (Mx D W.rank r × Mx D W.rank r) :=
    SecondCountableTopology.to_firstCountableTopology _
  haveI : FirstCountableTopology (Mx D W.rank r) := SecondCountableTopology.to_firstCountableTopology _
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V'
  haveI : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO V' W) (ratL W V') hK hKc μ' h𝓕'⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by
    rw [Measure.restrict_apply_univ, hY.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨b1, hb1⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hP
  obtain ⟨b2, hb2⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hh : Continuous fun w => P w * star (G w) := hP.cont.mul hG.cont.star
  have hhb : ∀ w, ‖P w * star (G w)‖ ≤ b1 * b2 := fun w => by
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb1 w) (hb2 w) (norm_nonneg _) ((norm_nonneg _).trans (hb1 w))
  have hu : Continuous fun q : (Mx D W.rank r × Mx D W.rank r) × WO V' W =>
      isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2 :=
    (((isoPart_continuous V W C').comp (continuous_fst.comp continuous_fst)).add
      ((isoPart_continuous V W C).comp (continuous_snd.comp continuous_fst))).add
      ((midPart_continuous V V' W B).comp continuous_snd)
  obtain ⟨hin, hinb⟩ := integral_continuous_of_bounded (μ'.restrict 𝓕')
    (fun q : (Mx D W.rank r × Mx D W.rank r) × WO V' W =>
      P (isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2) *
        star (G (isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2))) (hh.comp hu) (b1 * b2)
    (fun q => hhb _)
  refine ⟨?_, ?_⟩
  · exact (integral_continuous_of_bounded (μ.restrict 𝓨)
      (fun q : Mx D W.rank r × Mx D W.rank r => ∫ x in 𝓕',
        P (isoPart V W C' q.1 + isoPart V W C q.2 + midPart V V' W B x) *
          star (G (isoPart V W C' q.1 + isoPart V W C q.2 + midPart V V' W B x)) ∂μ') hin _ hinb).1
  · intro γ hγ t
    have key : ∀ y x, P (isoPart V W C' (γ + t) + isoPart V W C y + midPart V V' W B x) *
        star (G (isoPart V W C' (γ + t) + isoPart V W C y + midPart V V' W B x)) =
        P (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) *
        star (G (isoPart V W C' t + isoPart V W C y + midPart V V' W B x)) := fun y x => by
      rw [isoPart_add, add_assoc (isoPart V W C' γ) (isoPart V W C' t),
        add_assoc (isoPart V W C' γ) (isoPart V W C' t + isoPart V W C y)]
      exact GlobalTheory.ThetaSchur.prod_periodic hψ hP hG (isoPart_rat V W C' hγ) _
    simp_rw [key]

end GlobalTheory.TwistThetaMean
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProductMeanContinuousPeriodicDualVariableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaProductMean_continuous_periodic_dualVariable : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ P G, IsThetaFunO ψ V W P → IsThetaFunO ψ V W G → Continuous (fun t : Mx D W.rank r => ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) ∧ ∀ γ ∈ ratMx D W.rank r, ∀ t : Mx D W.rank r, (∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  first | exact @GlobalTheory.TwistThetaMean.mean_continuous_periodic | exact GlobalTheory.TwistThetaMean.mean_continuous_periodic | (intros; apply GlobalTheory.TwistThetaMean.mean_continuous_periodic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanThetaProductConjEqRestrictionProduc
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanThetaProductConjEqRestrictionProduc
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanProd

variable {D : D7}

theorem symplOH_iso_mid {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (a : Mx D W.rank r) (x : WO V' W) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (isoPart V W C a + midPart V V' W B x) = 0 := by
  have rat_mul {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E)
      (N : Matrix (Fin m) (Fin n) D.host.E) :
      GlobalTheory.MixModel.rat (M * N) = GlobalTheory.MixModel.rat M * GlobalTheory.MixModel.rat N := Matrix.map_mul
  have adj_mul {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x :=
    Formalism.UG.cT_mul (cA D) x y
  have hO_eq_trace (T : HSp D) (x y : WO V T) :
      hO V T x y = (GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA T * x))).trace := by
    simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
    rfl
  set P : Mx D r V.rank := GlobalTheory.MixModel.rat (adj D C * V.gram) with hP
  set Q : Mx D V'.rank V.rank := GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) with hQ
  have hG := GlobalTheory.MixModel.gram_conjTranspose V
  have hG' := GlobalTheory.MixModel.gramInv_conjTranspose V'
  have hU := GlobalTheory.MixModel.gram_isUnit_det V
  have hC0 : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hO : adj D C * V.gram * B = 0 := hs.orth
  have k1 : P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj P = 0 := by
    rw [hP, ← GlobalTheory.MixModel.rat_conjTranspose, GlobalTheory.MixModel.giA, ← rat_mul, ← rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (adj D C * V.gram)ᴴ = 0 := by
      change Cᴴ * V.gram * V.gram⁻¹ * (Cᴴ * V.gram)ᴴ = 0
      change Cᴴ * V.gram * C = 0 at hC0
      rw [Matrix.conjTranspose_mul, hG, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc (Cᴴ * V.gram),
        ← Matrix.mul_assoc V.gram⁻¹, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul, hC0]
    rw [this, GlobalTheory.MixModel.rat_zero]
  have k2 : P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Q = 0 := by
    rw [hP, hQ, ← GlobalTheory.MixModel.rat_conjTranspose, GlobalTheory.MixModel.giA, ← rat_mul, ← rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
      change Cᴴ * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * Bᴴ * V.gram)ᴴ = 0
      change Cᴴ * V.gram * B = 0 at hO
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG, hG', Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc (Cᴴ * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ hU, Matrix.one_mul, ← Matrix.mul_assoc, hO, Matrix.zero_mul]
    rw [this, GlobalTheory.MixModel.rat_zero]
  have e1 : isoPart V W C (q₀.map (incA D)) = GlobalTheory.MixModel.rat q₀ * P := rfl
  have e2 : isoPart V W C a + midPart V V' W B x = a * P + x * Q := rfl
  have k3 : P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q) = 0 := by
    rw [GlobalTheory.MixModel.adj_add, adj_mul, adj_mul, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, k1, k2, Matrix.zero_mul, Matrix.zero_mul, add_zero]
  rw [GlobalTheory.MixModel.symplOH_eq, hO_eq_trace, e1, e2]
  have e3 : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (a * P + x * Q) * (GlobalTheory.MixModel.gA W * (GlobalTheory.MixModel.rat q₀ * P))) =
      (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q) * GlobalTheory.MixModel.gA W * GlobalTheory.MixModel.rat q₀) * P := by
    simp only [Matrix.mul_assoc]
  rw [e3, Matrix.trace_mul_comm]
  have e4 : P * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q) * GlobalTheory.MixModel.gA W * GlobalTheory.MixModel.rat q₀) =
      (P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q)) * (GlobalTheory.MixModel.gA W * GlobalTheory.MixModel.rat q₀) := by
    simp only [Matrix.mul_assoc]
  rw [e4, k3, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem iso_periodic {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      f (isoPart V W C (γ + a) + midPart V V' W B x) = f (isoPart V W C a + midPart V V' W B x) := by
  rintro _ ⟨q₀, rfl⟩ a
  have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
  have hadd : isoPart V W C (q₀.map (incA D) + a) = isoPart V W C (q₀.map (incA D)) + isoPart V W C a :=
    Matrix.add_mul _ _ _
  have hrat : ratW W V (q₀ * (adj D C * V.gram)) = isoPart V W C (q₀.map (incA D)) := Matrix.map_mul
  rw [e3, hadd, add_assoc, ← hrat, hf.quasi, hrat, symplOH_iso_mid hs, neg_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.IsoMeanProd

namespace GlobalTheory.IsoMeanProd

theorem mean_iso_mul_star : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ ∂μ = ∫ x in 𝓕', res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) ∂μ' := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 hμ μ' 𝓕' hμ' h𝓕' F G hF hG
  have hμ1 : IsCovolOne (GlobalTheory.MixModel.ratMx D W.rank r) μ 𝓨 := hμ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI hfin1 : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (GlobalTheory.Size.measure_dom hμ' h𝓕').2⟩
  haveI hsf1 : SigmaFinite (μ.restrict 𝓨) := @IsFiniteMeasure.toSigmaFinite _ _ _ hfin1
  haveI : SFinite (μ.restrict 𝓨) := @instSFiniteOfSigmaFinite _ _ _ hsf1
  haveI : SigmaFinite (μ'.restrict 𝓕') := inferInstance
  haveI : SFinite (μ'.restrict 𝓕') := inferInstance
  obtain ⟨cF, hcF⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hF
  obtain ⟨cG, hcG⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hG
  have ciso : Continuous (fun y : Mx D W.rank r => isoPart V W C y) := continuous_id.matrix_mul continuous_const
  have cmid : Continuous (fun x : WO V' W => midPart V V' W B x) := continuous_id.matrix_mul continuous_const
  obtain ⟨H, hH⟩ : ∃ H : Mx D W.rank r → Mx D W.rank r → WO V' W → ℂ, H = fun y y' x =>
      F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) := ⟨_, rfl⟩
  have hHb : ∀ y y' x, ‖H y y' x‖ ≤ cF * cG := by
    intro y y' x
    rw [hH, norm_mul, norm_star]
    exact mul_le_mul (hcF _) (hcG _) (norm_nonneg _) ((norm_nonneg _).trans (hcF 0))
  have hHc : Continuous fun p : Mx D W.rank r × Mx D W.rank r × WO V' W => H p.1 p.2.1 p.2.2 := by
    rw [hH]
    exact (hF.cont.comp ((ciso.comp (continuous_fst.add continuous_snd.fst)).add (cmid.comp continuous_snd.snd))).mul
      (continuous_star.comp (hG.cont.comp ((ciso.comp continuous_snd.fst).add (cmid.comp continuous_snd.snd))))
  have hint : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X)
      [IsFiniteMeasure ν] (g : X → ℂ), Continuous g → (∀ z, ‖g z‖ ≤ cF * cG) → Integrable g ν :=
    fun ν _ g hg hb => Integrable.of_bound hg.aestronglyMeasurable _ (Filter.Eventually.of_forall hb)
  have hI1 : ∀ y, Integrable (Function.uncurry fun y' x => H y y' x) ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) :=
    fun y => hint _ _ (hHc.comp (continuous_const.prodMk continuous_id)) fun z => hHb _ _ _
  have hI3 : Integrable (fun q : (Mx D W.rank r × WO V' W) × Mx D W.rank r => H q.1.1 q.2 q.1.2)
      (((μ.restrict 𝓨).prod (μ'.restrict 𝓕')).prod (μ.restrict 𝓨)) :=
    hint _ _ (hHc.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))) fun z => hHb _ _ _
  have hI2 : Integrable (Function.uncurry fun y x => ∫ y', H y y' x ∂(μ.restrict 𝓨))
      ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) := hI3.integral_prod_left
  have hI4 : ∀ x, Integrable (Function.uncurry fun y y' => H y y' x) ((μ.restrict 𝓨).prod (μ.restrict 𝓨)) :=
    fun x => hint _ _ (hHc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))) fun z => hHb _ _ _
  have step4 : ∀ x y', ∫ y in 𝓨, H y y' x ∂μ =
      res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) := by
    intro x y'
    rw [hH]
    simp only
    rw [integral_mul_const]
    congr 1
    exact GlobalTheory.MixModel.covolOne_integral_add hμ1 (fun a => F (isoPart V W C a + midPart V V' W B x))
      (iso_periodic hs hF x) y'
  have step5 : ∀ x, ∫ y' in 𝓨, res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ =
      res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) := by
    intro x
    rw [integral_const_mul]
    congr 1
    exact integral_conj
  have e0 : ∀ y y' x, F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) = H y y' x := by
    intro y y' x; rw [hH]
  simp only [e0]
  calc ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', H y y' x ∂μ' ∂μ ∂μ
      = ∫ y in 𝓨, ∫ x in 𝓕', ∫ y' in 𝓨, H y y' x ∂μ ∂μ' ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => integral_integral_swap (hI1 y))
    _ = ∫ x in 𝓕', ∫ y in 𝓨, ∫ y' in 𝓨, H y y' x ∂μ ∂μ ∂μ' := integral_integral_swap hI2
    _ = ∫ x in 𝓕', ∫ y' in 𝓨, ∫ y in 𝓨, H y y' x ∂μ ∂μ ∂μ' :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => integral_integral_swap (hI4 x))
    _ = ∫ x in 𝓕', ∫ y' in 𝓨, res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ ∂μ' :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          integral_congr_ae (Filter.Eventually.of_forall fun y' => step4 x y'))
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => step5 x)

end GlobalTheory.IsoMeanProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanThetaProductConjEqRestrictionProducStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicMean_thetaProduct_conj_eq_restrictionProduct : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ ∂μ = ∫ x in 𝓕', res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) ∂μ' := by
  first | exact @GlobalTheory.IsoMeanProd.mean_iso_mul_star | exact GlobalTheory.IsoMeanProd.mean_iso_mul_star | (intros; apply GlobalTheory.IsoMeanProd.mean_iso_mul_star <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqSetIntegralTsumRationalTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqSetIntegralTsumRationalTranslates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.Periodize

theorem integral_eq_setIntegral_tsum (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (ratMx D m n) 𝓕 μ) (c : Mx D m n → ℂ)
    (hc : Integrable c μ) :
    (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧
      ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D m n) := i5
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let e : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
    Equiv.ofBijective (fun a => ⟨a.map (incA D), a, rfl⟩)
      ⟨fun a b h => Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h),
        fun γ => by obtain ⟨a, ha⟩ := γ.2; exact ⟨a, Subtype.ext ha⟩⟩
  have he : ∀ a, ((e a : ratMx D m n) : Mx D m n) = a.map (incA D) := fun _ => rfl

  have hm : ∀ γ : ratMx D m n, AEStronglyMeasurable (fun y => c (y + γ)) (μ.restrict 𝓕) := by
    intro γ
    have := hc.1.comp_quasiMeasurePreserving (measurePreserving_add_right μ (γ : Mx D m n)).quasiMeasurePreserving
    exact this.restrict

  have hl : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ := by
    rw [hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp only [AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
  have hfin : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hc.2.ne

  have hae : ∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : ratMx D m n => ‖c (y + γ)‖ := by
    have h1 : ∫⁻ y in 𝓕, ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun γ => (hm γ).enorm]; exact hfin
    have h2 : AEMeasurable (fun y => ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ) (μ.restrict 𝓕) :=
      AEMeasurable.tsum fun γ => (hm γ).enorm
    filter_upwards [ae_lt_top' h2 h1] with y hy
    have : ∑' γ : ratMx D m n, (‖c (y + γ)‖₊ : ENNReal) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hy.ne
    exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with y hy
    exact (e.summable_iff.2 hy).congr fun a => by rw [Function.comp_apply, he]
  · have h3 : ∫ y in 𝓕, ∑' γ : ratMx D m n, c (y + γ) ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ :=
      integral_tsum hm hfin
    have h4 : ∫ y, c y ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ := by
      rw [hF.integral_eq_tsum' c hc, ← (Equiv.neg (ratMx D m n)).tsum_eq]
      refine tsum_congr fun γ => ?_
      simp only [Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
    rw [h4, ← h3]
    congr 1
    funext y
    rw [← e.tsum_eq]
    rfl

end GlobalTheory.Twist.Periodize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqSetIntegralTsumRationalTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_setIntegral_tsum_rationalTranslates : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratMx D m n) 𝓕 μ → ∀ c : Mx D m n → ℂ, Integrable c μ → (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧ ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  first | exact @GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum | exact GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum | (intros; apply GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedThetaCoefficientEqIsotropicIntegral
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefUnfold

theorem isoPart_add' {D : D7} (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y z : Mx D W.rank r) :
    isoPart V W C (y + z) = isoPart V W C y + isoPart V W C z := by
  unfold isoPart
  rw [Matrix.add_mul]

private theorem symplOH_eq_zero_of_symplO_eq_zero {D : D7} (S T : HSp D) (a b : WO S T) (h : symplO S T a b = 0) :
    symplOH S T a b = 0 := by
  have h2 : (2 : AF D.host.F) * symplOH S T a b = 0 := by
    rw [two_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 a b, h]
  have hu : IsUnit (2 : AF D.host.F) := by
    have e : (algebraMap D.host.F (AF D.host.F)) 2 = 2 := map_ofNat _ 2
    rw [← e]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  exact hu.mul_right_eq_zero.1 h2

theorem sum_translates_eq : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ y : Mx D W.rank r, Summable (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV‖) → ∑' a : Matrix (Fin W.rank) (Fin r) D.host.E, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = κ • ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  intro D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ F G hF hG y hs
  have hY' := hY
  obtain ⟨hμH, hYF, hY1⟩ := hY'
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  haveI : IsTopologicalAddGroup (Mx D W.rank r) := i1
  haveI : LocallyCompactSpace (Mx D W.rank r) := i2
  haveI : SecondCountableTopology (Mx D W.rank r) := i3
  haveI : T2Space (Mx D W.rank r) := i4
  haveI : DiscreteTopology (ratMx D W.rank r) := i5
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : Countable D.host.E := Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin W.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin r → D.host.E))
  have hsp := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hCB C' h1 h2 h3
  have hiso0 : isoPart V W C' (0 : Mx D W.rank r) = 0 := by
    have e := isoPart_add' V W C' (0 : Mx D W.rank r) 0
    rw [add_zero] at e
    have e' : isoPart V W C' (0 : Mx D W.rank r) + isoPart V W C' 0 = isoPart V W C' 0 + 0 := by
      rw [add_zero]; exact e.symm
    exact add_left_cancel e'
  have hpt : ∀ (y' : Mx D W.rank r) (x : WO V' W),
      heisO ψ V W (isoPart V W C y) F (isoPart V W C y' + midPart V V' W B x) =
        F (isoPart V W C (y + y') + midPart V V' W B x) := by
    intro y' x
    have z1 : symplOH V W (isoPart V W C y') (isoPart V W C y) = 0 :=
      symplOH_eq_zero_of_symplO_eq_zero V W _ _ (hsp.1 y' y)
    have z2 : symplOH V W (midPart V V' W B x) (isoPart V W C y) = 0 := by
      rw [GlobalTheory.MixModel.symplOH_skew, symplOH_eq_zero_of_symplO_eq_zero V W _ _ (hsp.2.1 y x), neg_zero]
    show ψ (symplOH V W (isoPart V W C y' + midPart V V' W B x) (isoPart V W C y)) *
        F (isoPart V W C y' + midPart V V' W B x + isoPart V W C y) = _
    rw [(GlobalTheory.OrientedFormLaws.symplOH_laws D V W).1, z1, z2, add_zero, AddChar.map_zero_eq_one, one_mul,
      isoPart_add']
    congr 1
    abel
  have hP : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1 _ _ hF
  let χ : Matrix (Fin W.rank) (Fin r) D.host.E → Mx D W.rank r → ℂ :=
    fun a t => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))
  let Φ : Mx D W.rank r → ℂ := fun t => κ • ∫ y' in 𝓨, ∫ x in 𝓕',
    heisO ψ V W (isoPart V W C y) F (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) *
      star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ
  have hterm : ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E,
      (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) =
        ∫ t in 𝓨, χ a t * Φ t ∂μ := fun a =>
    GlobalTheory.T.matrixCoeff_isotropicTranslates_eq_fourierCoeffs D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ F G hF hG y a
  obtain ⟨hχc, hχx, hχa, hχΓ, hχ0⟩ := GlobalTheory.T.isotropic_part_rational_characters_adelic_matrices D V V' W r C B hCB C' h1 h2 h3 ψ hψ
  obtain ⟨hΦc, hΦp⟩ := GlobalTheory.T.thetaProductMean_continuous_periodic_dualVariable D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μ' 𝓕' hμ' hF' _ G hP hG
  have hsum : Summable (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ t in 𝓨, χ a t * Φ t ∂μ‖) := by
    have e : (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ t in 𝓨, χ a t * Φ t ∂μ‖) =
        fun a => ‖∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV‖ :=
      funext fun a => by rw [hterm a]
    rw [e]
    exact hs
  have key := GlobalTheory.T.fourier_inversion_zero_compact_quotient (Mx D W.rank r) (ratMx D W.rank r) K hK hKc (Matrix (Fin W.rank) (Fin r) D.host.E) χ
    hχc (fun a t s => hχx a t s) (fun a b t => hχa a b t) (fun a t => hψ.1.2.1 _) hχΓ hχ0 μ 𝓨 hμH hYF hY1 Φ
    (hΦc.const_smul κ) (fun γ hγ t => congrArg (fun z : ℂ => κ • z) (hΦp γ hγ t)) hsum
  rw [tsum_congr hterm, ← key]
  show κ • (∫ y' in 𝓨, ∫ x in 𝓕',
    heisO ψ V W (isoPart V W C y) F (isoPart V W C' 0 + isoPart V W C y' + midPart V V' W B x) *
      star (G (isoPart V W C' 0 + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = _
  simp only [hiso0, zero_add]
  simp_rw [hpt]

private theorem symplOH_eq_zero_of_symplO_eq_zero' {D : D7} (S T : HSp D) (a b : WO S T) (h : symplO S T a b = 0) :
    symplOH S T a b = 0 := by
  have h2 : (2 : AF D.host.F) * symplOH S T a b = 0 := by
    rw [two_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 a b, h]
  have hu : IsUnit (2 : AF D.host.F) := by
    have e : (algebraMap D.host.F (AF D.host.F)) 2 = 2 := map_ofNat _ 2
    rw [← e]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  exact hu.mul_right_eq_zero.1 h2

theorem coef_unfold : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ ν : Measure (Mx D W.rank r), ν.IsAddHaarMeasure ∧ ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ x : WO V' W, ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 F) w * star (res V V' W C B μ 𝓨 G w) ∂μ' = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) F w * star (G w) ∂μV) ∂ν := by
  intro D V V' W r C B hCB ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding D V V' r C B hCB
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.integral_hom_fundamental_domain_isotropic_split_coords D V V' W r C B hCB C' h1 h2 h3 μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  have hY' := hY
  obtain ⟨hμH, hYF, -⟩ := hY'
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := hμH
  have hc0 : ENNReal.ofReal κ⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hκ0)).ne'
  refine ⟨ENNReal.ofReal κ⁻¹ • μ, MeasureTheory.Measure.IsAddHaarMeasure.smul μ hc0 ENNReal.ofReal_ne_top, ?_⟩
  intro F G hF hG x
  have hsp := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hCB C' h1 h2 h3
  have hF₁ := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1 (midPart V V' W B x) F hF
  have he : ∀ y : Mx D W.rank r, heisO ψ V W (isoPart V W C y) (heisO ψ V W (midPart V V' W B x) F) =
      heisO ψ V W (isoPart V W C y + midPart V V' W B x) F := by
    intro y
    rw [(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).2.1, symplOH_eq_zero_of_symplO_eq_zero' V W _ _ (hsp.2.1 y x),
      AddChar.map_zero_eq_one, one_smul]
  rw [← ((GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hCB ψ hψ μ 𝓨 hY).1 F hF).2.2.1 x,
    ← GlobalTheory.T.isotropicMean_thetaProduct_conj_eq_restrictionProduct D V V' W r C B hCB ψ hψ μ 𝓨 hY μ' 𝓕' hμ' hF' _ G hF₁ hG]
  simp_rw [← he]
  obtain ⟨hsum, hint⟩ := GlobalTheory.T.integral_eq_setIntegral_tsum_rationalTranslates D W.rank r μ 𝓨 hμH hYF
    (fun y => ∫ w in 𝓕V, heisO ψ V W (isoPart V W C y) (heisO ψ V W (midPart V V' W B x) F) w * star (G w) ∂μV)
    (GlobalTheory.T.integrable_matrixCoeff_adelicIsotropicPart D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ hμH μV 𝓕V hμV hFV _ G hF₁ hG)
  beta_reduce at hsum hint
  rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 hκ0).le, hint,
    ← MeasureTheory.integral_smul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hsum] with y hy
  rw [sum_translates_eq D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ _ G hF₁ hG y hy,
    smul_smul, inv_mul_cancel₀ hκ0.ne', one_smul]

end GlobalTheory.CoefUnfold

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedThetaCoefficientEqIsotropicIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedTheta_coefficient_eq_isotropic_integral : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ ν : Measure (Mx D W.rank r), ν.IsAddHaarMeasure ∧ ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ x : WO V' W, ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 F) w * star (res V V' W C B μ 𝓨 G w) ∂μ' = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) F w * star (G w) ∂μV) ∂ν := by
  first | exact @GlobalTheory.CoefUnfold.coef_unfold | exact GlobalTheory.CoefUnfold.coef_unfold | (intros; apply GlobalTheory.CoefUnfold.coef_unfold <;> assumption)
end
