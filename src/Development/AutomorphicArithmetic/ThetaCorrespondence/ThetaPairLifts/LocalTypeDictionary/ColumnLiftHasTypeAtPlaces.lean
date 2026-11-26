module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalSum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmoothOfThetaLiftFiniteSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ColFockRed
open GlobalTheory.Grid
theorem theta_lift_finite_sum_smooth : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    ∀ (n : ℕ) (F : Fin n → (G.Xp j).Cusp R.θ) (w : Fin n → SmT (G.Xp j).M),
    (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g) (G.measX j).fd (G.measX j).ν) →
    ∃ (k : ℕ) (F' : Fin k → (G.Xp (j + 1)).Cusp R.θ) (z : Fin k → SmT (G.Xp (j + 1)).M),
      (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g ∂(G.measX j).ν) = ∑ i, (F' i).1 (z i) := by
  intro hL _hPr D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t j hj Φ hΦ n F w hint
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hRB hG
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨νS, PS, hS⟩ := xp_is hG j hj.le
  obtain ⟨νT, PT, hT⟩ := xp_is hG (j + 1) hj
  obtain ⟨hsig, hdef⟩ := GlobalTheory.ColTypeLift.xp_definite hG j hj.le
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_realCentralCharacter_definiteVertexMultiplicity D R.θ hθ (G.Xp j) νS PS hS
  have hψc : GlobalTheory.SeeSaw.HasCen (G.Xp j).V χ (∑ i, (F i).1 (w i)) := fun z hz hc h => by
    simp only [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hχ (F i) (w i) z hz hc h
  have hψa : GlobalTheory.Unf.IsContAut (G.Xp j).V (∑ i, (F i).1 (w i)) := by
    refine ⟨fun γ hγ g => ?_, by rw [Finset.sum_fn]; exact continuous_finsetSum _ fun i _ => (isContAut_cusp (F i) (w i)).2⟩
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (isContAut_cusp (F i) (w i)).1 γ hγ g
  obtain ⟨hν, hfd⟩ := measX_haar_fd hG j hj.le
  have hA := hG.arrows.col t j hj
  obtain ⟨Φ', hΦ', heig, heq⟩ := GlobalTheory.T.exists_thetaLift_realCentre_average_eigenvector D R.ψ _ _ _ _ (G.col t j).ω hA.weil hsig hdef _ _ hν hfd χ _ hψc hψa Φ hΦ hint
  obtain ⟨k, f, p, hf, hsum⟩ := GlobalTheory.T.centreEigen_thetaFunction_finite_sum_fockPolynomials D R.ψ R.θ hθ (G.Xp j) (G.Xp (j + 1)) νS νT PS PT hS hT (G.col t j) _ _ hA
    (fun z => (χ z)⁻¹) Φ' hΦ' heig
  have hcol := hCA.col t j hj
  choose F' hF' hI using fun (l : Fin k) (i : Fin n) => hcol (f l) (hf l) (F i).1 (F i).2
  refine ⟨k * n, fun q => ⟨F' (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2, hF' _ _⟩,
    fun q => (G.col t j).It (p (finProdFinEquiv.symm q).1) (w (finProdFinEquiv.symm q).2), ?_⟩
  funext h
  rw [heq h, hsum]
  have key : ∀ g, thetaKO (G.col t j).ω g h (∑ l, fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
      (∑ i, (F i).1 (w i)) g = ∑ l, ∑ i, thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
        (F i).1 (w i) g := fun g => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [thetaKO, map_sum, Finset.sum_apply, Finset.sum_mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ => (hI l i (p l) (w i) h).1]
  simp_rw [integral_finsetSum _ fun i _ => (hI _ i _ (w i) h).1]
  have e2 : ∀ l i, ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
      (F i).1 (w i) g ∂(G.measX j).ν = F' l i ((G.col t j).It (p l) (w i)) h := fun l i => (hI l i (p l) (w i) h).2
  simp_rw [e2]
  rw [← Fintype.sum_prod_type']
  rw [Finset.sum_apply]
  exact (finProdFinEquiv.symm.sum_comp (fun x : Fin k × Fin n => F' x.1 x.2 ((G.col t j).It (p x.1) (w x.2)) h)).symm
end GlobalTheory.ColFockRed
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_of_theta_lift_finite_sum : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    ∀ (n : ℕ) (F : Fin n → (G.Xp j).Cusp R.θ) (w : Fin n → SmT (G.Xp j).M),
    (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g) (G.measX j).fd (G.measX j).ν) →
    ∃ (k : ℕ) (F' : Fin k → (G.Xp (j + 1)).Cusp R.θ) (z : Fin k → SmT (G.Xp (j + 1)).M),
      (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g ∂(G.measX j).ν) = ∑ i, (F' i).1 (z i) := by
  first | exact @_root_.GlobalTheory.ColFockRed.theta_lift_finite_sum_smooth | exact _root_.GlobalTheory.ColFockRed.theta_lift_finite_sum_smooth | (intros; apply _root_.GlobalTheory.ColFockRed.theta_lift_finite_sum_smooth <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DefiniteUnitaryCuspidalDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
open Classical
namespace GlobalTheory.DefiniteDecomp
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid
theorem cusp_forms_decompose_definite_unitary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D), IsInfFam θ → N.V.SigOK → N.V.IsDefinite →
    ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
      ∃ (n : ℕ) (F : Fin n → N.Cusp θ) (w : Fin n → SmT N.M), φ = ∑ i, (F i).1 (w i) := by
  intro hP D θ N hθ hs hd φ hφ
  obtain ⟨hAut, -, hType⟩ := hφ
  haveI hfd : ∀ τ, FiniteDimensional ℂ (N.M.H τ) := fun τ => GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  have hmulK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
      g * h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := fun τ g hg h hh => GlobalTheory.PointAtPlaceHom.mul_mem_UH hg hh
  have hρ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
      (N.M.rep τ (g * h) : N.M.H τ →ₗ[ℂ] N.M.H τ) =
        (N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ) := by
    intro τ g hg h hh
    rw [rep_mul N.M τ hg hh]
    rfl
  have hframe : ∀ τ, ∃ (m : ℕ) (k : Fin m → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ)
      (B : Fin m → (N.M.H τ →ₗ[ℂ] N.M.H τ)), (∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) ∧
      (∀ A : N.M.H τ →ₗ[ℂ] N.M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
        LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ A) =
          ∑ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ (k j) : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ A) *
            LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), B i ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ) =
        ∑ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ (k j) : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ
          (B i ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ))) • B j) :=
    fun τ => GlobalTheory.T.exists_dual_frame_span_unitary_representation (Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) (fun g => (N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ))
      (hmulK τ) (hρ τ) (fun g hg => ⟨g⁻¹, (GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional N.M τ hg).1, (GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional N.M τ hg).2⟩)
  choose m k B hk hB1 hB2 using hframe
  have hexp : ∀ τ x, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), φ (x * atTau θ N.V τ g) =
      ∑ j, φ (x * atTau θ N.V τ (k τ j)) *
        LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j) :=
    fun τ x g hg => GlobalTheory.T.modelType_form_expands_along_dualFrame hP.discreteSeriesHermitianUnique θ N.M τ (k τ) (hk τ) (B τ) (hB1 τ) (hType τ) x hg
  let F : GA D N.V → (D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ) → ℂ :=
    fun x g => φ (x * realProd θ N.V g)
  have hsplit : ∀ x (g : D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) → ∀ τ₀ g', g' ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀) →
      F x (Function.update g τ₀ g') = φ ((x * realProd θ N.V (Function.update g τ₀ 1)) * atTau θ N.V τ₀ g') := by
    intro x g hg τ₀ g' hg'
    show φ (x * realProd θ N.V (Function.update g τ₀ g')) = _
    rw [realProd_update hθ hg τ₀ hg', (realProd_commute hθ hg τ₀ hg').eq, mul_assoc]
  have hFexp : ∀ x τ₀ (g : D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) → F x g = ∑ j, F x (Function.update g τ₀ (k τ₀ j)) *
        LinearMap.trace ℂ (N.M.H τ₀) ((N.M.rep τ₀ (g τ₀) : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀) ∘ₗ B τ₀ j) := by
    intro x τ₀ g hg
    have e0 : F x g = F x (Function.update g τ₀ (g τ₀)) := by rw [Function.update_eq_self]
    rw [e0, hsplit x g hg τ₀ _ (hg τ₀), hexp τ₀ _ _ (hg τ₀)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsplit x g hg τ₀ _ (hk τ₀ j)]
  let bH : ∀ τ, Module.Basis (Fin (Module.finrank ℂ (N.M.H τ))) ℂ (N.M.H τ) := fun τ => Module.finBasis ℂ (N.M.H τ)
  let ℓ : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))) → ∀ τ, Fin (m τ) → (N.M.sm τ →ₗ[ℂ] ℂ) :=
    fun a τ j => (bH τ).coord (a τ) ∘ₗ B τ j ∘ₗ (N.M.sm τ).subtype
  let T : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))) → MMap N.M := fun a =>
    ∑ J : (∀ τ, Fin (m τ)), ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).compLinearMap
      (fun τ => ℓ a τ (J τ))).smulRight (fun x => F x (fun τ => k τ (J τ)))
  have hT : ∀ a (v : ∀ τ, N.M.sm τ) (x : GA D N.V), T a v x = ∑ J : (∀ τ, Fin (m τ)), (∏ τ, ℓ a τ (J τ) (v τ)) * F x (fun τ => k τ (J τ)) := by
    intro a v x
    simp only [T, MultilinearMap.sum_apply, Finset.sum_apply, MultilinearMap.smulRight_apply,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, Pi.smul_apply, smul_eq_mul]
  have hMult : ∀ a, IsMultMap θ N.M ∅ 1 (T a) := by
    intro a
    refine ⟨fun v => ?_, fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _,
      fun v k' hk' => absurd hk' (Set.notMem_empty k'), fun τ₀ h hh v w hw => ?_, fun τ v x => ?_⟩
    · have e : T a v = ∑ J : (∀ τ, Fin (m τ)), (∏ τ, ℓ a τ (J τ) (v τ)) •
          rTr N.V (realProd θ N.V (fun τ => k τ (J τ))) φ := by
        funext x
        rw [hT, Finset.sum_apply]
        rfl
      rw [e]
      refine Finset.sum_induction _ (IsAutFunSm θ N.V) (fun f g hf hg => GlobalTheory.MultMem.isAutFunSm_add hf hg) ?_
        (fun J _ => GlobalTheory.MultMem.isAutFunSm_smul _ (isAutFunSm_realProd hθ _ hAut))
      exact Formalism.L2.Theta.isAutFunSm_const (θ := θ) (V := N.V) (c := (0 : ℂ))
    · funext x
      have hkJ : ∀ J : (∀ τ, Fin (m τ)), ∀ τ, (fun τ => k τ (J τ)) τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
        fun J τ => hk τ (J τ)
      have hF' : ∀ J : (∀ τ, Fin (m τ)), F (x * atTau θ N.V τ₀ h) (fun τ => k τ (J τ)) =
          F x (Function.update (fun τ => k τ (J τ)) τ₀ (h * k τ₀ (J τ₀))) := by
        intro J
        show φ (x * atTau θ N.V τ₀ h * realProd θ N.V _) = φ (x * realProd θ N.V _)
        have e1 := realProd_update hθ (hkJ J) τ₀ (hmulK τ₀ h hh _ (hk τ₀ (J τ₀)))
        have e2 := realProd_update hθ (hkJ J) τ₀ (hk τ₀ (J τ₀))
        rw [Function.update_eq_self] at e2
        rw [e1, e2, GlobalTheory.PointAtPlaceHom.atTau_mul hθ N.V τ₀ hh (hk τ₀ (J τ₀))]
        simp only [mul_assoc]
      show T a (Function.update v τ₀ w) x = T a v (x * atTau θ N.V τ₀ h)
      rw [hT, hT]
      simp only [hF']
      have key := GlobalTheory.T.sum_prod_update_regroup_of_update_eq (X := fun _ => Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ) (W := fun τ => N.M.sm τ)
        k (ℓ a) τ₀ (F x) (fun g => F x (Function.update g τ₀ (h * g τ₀))) (v τ₀) w ?_ v
      · rw [Function.update_eq_self] at key
        exact key
      intro J
      simp only [Function.update_idem, Function.update_self]
      have hf : ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀), F x (Function.update (fun τ => k τ (J τ)) τ₀ g') =
          ∑ j, F x (Function.update (fun τ => k τ (J τ)) τ₀ (k τ₀ j)) *
            LinearMap.trace ℂ (N.M.H τ₀) ((N.M.rep τ₀ g' : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀) ∘ₗ B τ₀ j) := by
        intro g' hg'
        rw [hsplit x _ (hkJ J) τ₀ g' hg', hexp τ₀ _ g' hg']
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsplit x _ (hkJ J) τ₀ _ (hk τ₀ j)]
      have := equiv_one (Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀)) (fun g => (N.M.rep τ₀ g : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀))
        (hρ τ₀) (k τ₀) (hk τ₀) (B τ₀) (hB2 τ₀) _ hf (hmulK τ₀) ((bH τ₀).coord (a τ₀)) (v τ₀ : N.M.H τ₀) hh
      simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, hw]
      exact this
    · exact GlobalTheory.DefiniteEnd.exists_sobCont N.M τ (T a) v x
  have hmem : ∀ a, PiTensorProduct.lift (T a) ∈ N.Cusp θ := fun a =>
    (mem_multT θ N.M ∅ 1 _).2 (by rw [LinearEquiv.symm_apply_apply]; exact Submodule.subset_span (hMult a))
  let e : ∀ τ, Fin (Module.finrank ℂ (N.M.H τ)) → N.M.sm τ := fun τ i => ⟨bH τ i, by rw [sm_eq_top N.M τ]; trivial⟩
  have htr : ∀ τ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ 1 : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j) =
      ∑ i, (bH τ).coord i (B τ j (bH τ i)) := by
    intro τ j
    rw [rep_one N.M τ, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id, LinearMap.id_comp,
      LinearMap.trace_eq_matrix_trace ℂ (bH τ), Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
  have hrep : ∀ x, φ x = ∑ a : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))), T a (fun τ => e τ (a τ)) x := by
    intro x
    have h1 : φ x = F x (fun _ => 1) := by
      show φ x = φ (x * realProd θ N.V _)
      rw [realProd_one hθ, mul_one]
    have h2 := GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate (X := fun _ => Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ)
      (fun τ => Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) m k hk
      (fun τ j g => LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j)) (F x)
      (fun τ₀ g hg => hFexp x τ₀ g hg) (fun _ => 1) (fun τ => GlobalTheory.PointAtPlaceHom.one_mem_UH _)
    rw [h1, h2]
    simp only [hT]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    simp only [htr]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rfl
  let eqv := Fintype.equivFin (∀ τ, Fin (Module.finrank ℂ (N.M.H τ)))
  refine ⟨Fintype.card _, fun i => ⟨PiTensorProduct.lift (T (eqv.symm i)), hmem _⟩,
    fun i => PiTensorProduct.tprod ℂ (fun τ => e τ (eqv.symm i τ)), ?_⟩
  funext x
  rw [hrep x, Finset.sum_apply]
  simp only [PiTensorProduct.lift.tprod]
  exact (Equiv.sum_comp eqv.symm (fun a => T a (fun τ => e τ (a τ)) x)).symm
end GlobalTheory.DefiniteDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_unitary_cuspidal_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D), IsInfFam θ → N.V.SigOK → N.V.IsDefinite →
    ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
      ∃ (n : ℕ) (F : Fin n → N.Cusp θ) (w : Fin n → SmT N.M), φ = ∑ i, (F i).1 (w i) := by
  first | exact @_root_.GlobalTheory.DefiniteDecomp.cusp_forms_decompose_definite_unitary | exact _root_.GlobalTheory.DefiniteDecomp.cusp_forms_decompose_definite_unitary | (intros; apply _root_.GlobalTheory.DefiniteDecomp.cusp_forms_decompose_definite_unitary <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ColTypeLift
theorem columnLift_isTypeAt_place : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → ∀ τ, IsTypeAt R.θ (G.Xp (j + 1)).V τ ((G.Xp (j + 1)).S τ) (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t j hj Φ hΦ φ hφ hI τ
  have h0 := xp_definite hG j hj.le
  have h1 := xp_definite hG (j + 1) hj
  obtain ⟨n, F, w, rfl⟩ := _root_.GlobalTheory.T.definite_unitary_cuspidal_decomposition hP R.θ (G.Xp j) hR.inf h0.1 h0.2 φ hφ
  obtain ⟨k, F', z, e⟩ := _root_.GlobalTheory.T.smooth_of_theta_lift_finite_sum hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ n F w hI
  rw [e]
  exact isTypeAt_sum R.θ (G.Xp (j + 1)) h1.1 h1.2 τ F' z
end GlobalTheory.ColTypeLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLift_hasTypeAtPlaces : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → ∀ τ, IsTypeAt R.θ (G.Xp (j + 1)).V τ ((G.Xp (j + 1)).S τ) (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  first | exact @_root_.GlobalTheory.ColTypeLift.columnLift_isTypeAt_place | exact _root_.GlobalTheory.ColTypeLift.columnLift_isTypeAt_place | (intros; apply _root_.GlobalTheory.ColTypeLift.columnLift_isTypeAt_place <;> assumption)
end
