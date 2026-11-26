module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakWeilRepEqUnitSmulOscillatorRealPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaThetaFunctionsFromMatrixCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaThetaFunctionsFromMatrixCoefficients
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem exists_scalar_of_forall_eigen {V : Type*} [AddCommGroup V] [Module ℂ V] (P : V → Prop)
    (hP : ∀ f g, P f → P g → P (f + g)) (M : Module.End ℂ V) (h : ∀ f, P f → ∃ c : ℂ, ‖c‖ = 1 ∧ M f = c • f) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, P f → M f = c • f := by
  by_cases h0 : ∃ f₀, P f₀ ∧ f₀ ≠ 0
  · obtain ⟨f₀, hf₀, hne⟩ := h0
    obtain ⟨c, hc, ec⟩ := h f₀ hf₀
    refine ⟨c, hc, fun f hf => ?_⟩
    by_cases ha : ∃ a : ℂ, f = a • f₀
    · obtain ⟨a, rfl⟩ := ha
      rw [LinearMap.map_smul, ec, smul_comm]
    · obtain ⟨e, -, ee⟩ := h f hf
      obtain ⟨d, -, ed⟩ := h (f + f₀) (hP _ _ hf hf₀)
      rw [LinearMap.map_add (f := _), ec, ee, smul_add] at ed
      have k : (e - d) • f = (d - c) • f₀ := by
        rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, ed, add_comm]
      have hed : e - d = 0 := by
        by_contra hn
        exact ha ⟨(e - d)⁻¹ * (d - c), by rw [mul_smul, ← k, smul_smul, inv_mul_cancel₀ hn, one_smul]⟩
      rw [hed, zero_smul] at k
      have hdc : d - c = 0 := (smul_eq_zero.1 k.symm).resolve_right hne
      rw [ee, sub_eq_zero.1 hed, sub_eq_zero.1 hdc]
  · refine ⟨1, norm_one, fun f hf => ?_⟩
    have : f = 0 := by
      by_contra hn
      exact h0 ⟨f, hf, hn⟩
    rw [this, LinearMap.map_zero, smul_zero]

theorem schur_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → M f = c • f := by
  intro D ψ hψ S T M hM hcomm hiso
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, -⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hc
  refine exists_scalar_of_forall_eigen _ (fun f g hf hg => GlobalTheory.OrientedHeis.theta_add hf hg) M fun f hf => ?_
  refine GlobalTheory.T.thetaFunction_eq_unitSmul_of_diagonalCoefficient_eq D ψ hψ S T μ 𝓕 hμ h𝓕 f (M f) hf (hM f hf) fun w => ?_
  rw [← hcomm w f hf]
  exact GlobalTheory.T.thetaFunction_scalarProduct_preserved_isometry D ψ hψ S T μ 𝓕 hμ h𝓕 M hM (hiso μ 𝓕 hμ h𝓕) _ _
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w) hf

end GlobalTheory.Mem.Lift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaThetaFunctionsFromMatrixCoefficientsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_lemma_thetaFunctions_from_matrixCoefficients : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → M f = c • f := by
  first | exact @GlobalTheory.Mem.Lift.schur_theta | exact GlobalTheory.Mem.Lift.schur_theta | (intros; apply GlobalTheory.Mem.Lift.schur_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakWeilRepEqUnitSmulOscillatorRealPoints
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.Mem.LiftCmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.RealWeil GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem actO_inv_cancel {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  have a : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  have b : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  unfold actO
  rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, a, Matrix.one_mul, Matrix.mul_assoc, b, Matrix.mul_one]

theorem eq_smul_of_inv_mul {G H M : Type} [Group G] [Group H] [AddCommGroup M] [Module ℂ M]
    (om : G × H →* Module.End ℂ M) (A : Module.End ℂ M) (g : G) (k : H) {c : ℂ} (hc : c ≠ 0) (f : M)
    (e : (om (g⁻¹, k⁻¹) * A) f = c • f) : om (g, k) f = c⁻¹ • A f := by
  have e := congrArg (om (g, k)) e
  rw [← Module.End.mul_apply, ← mul_assoc, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel,
    Prod.mk_one_one, map_one, one_mul, map_smul] at e
  rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem weil_eq_smul_osc : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ Ω : GA D S × GA D T → GlobalTheory.RealWeil.BB ψ S T → GlobalTheory.RealWeil.BB ψ S T, GlobalTheory.RealWeil.IsOsc (GlobalTheory.RealWeil.rhoV hψ σ S T) (fun p v => GlobalTheory.RealWeil.mM θ S T p *ᵥ v) Ω → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → om (g, h) F.1 = c • ((Ω (g, h) F).1 : WO S T → ℂ) := by
  intro D θ σ h ψ hψ S T om hw Ω hΩ g hg k hk
  unfold IsOsc at hΩ
  obtain ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩ := hΩ
  have hθ := h.inf
  have sm := sm_of_theta (S := S) (T := T) h hψ
  have hfin : ∀ p {u : WO S T}, u.map (infPart D) = 0 → ∀ F, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) F →
      Ω p (rhoB hψ u F) = rhoB hψ u (Ω p F) := fun p u hu F hF => hcomm p _ (rhoB_comm h hψ hu) F hF
  have hth : ∀ p F, IsThetaFunO ψ S T F.1 → IsThetaFunO ψ S T (Ω p F).1 := by
    intro p F hF
    obtain ⟨U, hU, hl⟩ := hF.level
    refine theta_of_sm h hψ _ (hsm p F (sm F hF)) ⟨U, hU, fun u hu h0 => ?_⟩
    have e : rhoB hψ u F = F := QB_ext fun x => by rw [coe_rhoB, hl u hu h0]
    rw [← coe_rhoB hψ, ← hfin p h0 F (sm F hF), e]
  obtain ⟨om', hom⟩ := exists_hom hψ Ω hth (fun p F F' h1 h2 => hadd p F F' (sm F h1) (sm F' h2))
    (fun p a F h1 => hsmul p a F (sm F h1)) (fun F h1 => hone F (sm F h1)) fun p p' F h1 => hmul p p' F (sm F h1)
  have lift : ∀ f, IsThetaFunO ψ S T f → ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    fun f hf => ⟨toB hψ f hf, coe_toB hψ f hf⟩
  have pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om' p f) := by
    intro p f hf
    obtain ⟨F, rfl⟩ := lift f hf
    rw [hom p F hf]
    exact hth p F hf
  have Heisenberg₂ : ∀ w f, IsThetaFunO ψ S T f →
      om' (g, k) (heisO ψ S T w f) = heisO ψ S T (actO S T g k w) (om' (g, k) f) := by
    intro w f hf
    obtain ⟨F, rfl⟩ := lift f hf
    obtain ⟨u, v, hu, rfl⟩ := exists_parts h w
    have h1 : IsThetaFunO ψ S T (rhoV hψ σ S T v F).1 := by
      rw [coe_rhoV]
      exact theta_heisO_real hθ hψ (real_iotaV h v) hf
    have h2 : IsThetaFunO ψ S T (rhoB hψ u (rhoV hψ σ S T v F)).1 := by
      rw [coe_rhoB]
      exact GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 h1 hu
    have e1 : actO S T g k (u + iotaV σ S T v) = u + iotaV σ S T (mM θ S T (g, k) *ᵥ v) := by
      rw [GlobalTheory.WeilVacMove.actO_add, actO_fin h hg hk hu, actO_iotaV h]
    rw [hom _ F hf, e1, ← coe_rhoB hψ _ F, ← coe_rhoB hψ _ (Ω (g, k) F), rhoB_add h hψ hu v F,
      rhoB_add h hψ hu _ (Ω (g, k) F), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm F hf)]
  obtain ⟨c, hc, hM⟩ := GlobalTheory.T.schur_lemma_thetaFunctions_from_matrixCoefficients D ψ hψ S T (om (g⁻¹, k⁻¹) * om' (g, k))
    (fun f hf => hw.om_pres _ _ (pres _ f hf))
    (fun w f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, Heisenberg₂ w f hf, hw.om_heis _ _ _ _ (pres _ f hf),
        actO_inv_cancel])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hw.om_unit μ 𝓕 hμ h𝓕 _ _ (pres _ f hf)]
      obtain ⟨F, rfl⟩ := lift f hf
      rw [hom _ F hf]
      exact lintegral_eq_of_norms hψ μ 𝓕 hμ h𝓕 fun H _ _ _ Φ hΦ =>
        hunit H Φ (fun v => hΦ _) _ F (sm F hf))
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], fun F hF => ?_⟩
  rw [← hom _ F hF]
  exact eq_smul_of_inv_mul om _ g k hc0 _ (hM F.1 hF)

end GlobalTheory.Mem.LiftCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakWeilRepEqUnitSmulOscillatorRealPointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakWeilRep_eq_unit_smul_oscillator_real_points : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ Ω : GA D S × GA D T → GlobalTheory.RealWeil.BB ψ S T → GlobalTheory.RealWeil.BB ψ S T, GlobalTheory.RealWeil.IsOsc (GlobalTheory.RealWeil.rhoV hψ σ S T) (fun p v => GlobalTheory.RealWeil.mM θ S T p *ᵥ v) Ω → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → om (g, h) F.1 = c • ((Ω (g, h) F).1 : WO S T → ℂ) := by
  first | exact @GlobalTheory.Mem.LiftCmp.weil_eq_smul_osc | exact GlobalTheory.Mem.LiftCmp.weil_eq_smul_osc | (intros; apply GlobalTheory.Mem.LiftCmp.weil_eq_smul_osc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffEqTensorSquareTopCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffEqTensorSquareTopCoefficient
noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel.TopRead

variable {n : ℕ}

theorem list_prod_gen {m : ℕ} (x : Fin m → Fin n × Fin n) :
    (List.ofFn fun j => gen n (x j)).prod =
      (List.ofFn fun j => vec n (x j).1).prod ⊗ₜ (List.ofFn fun j => vec n (x j).2).prod := by
  induction m with
  | zero => simp [Algebra.TensorProduct.one_def]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => x j.succ)]
    simp only [List.ofFn_succ, List.prod_cons, gen, Algebra.TensorProduct.tmul_mul_tmul]

theorem topBig_toEven_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    topBig n ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) := by
  have h1 : ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) = (List.ofFn fun j => gen n (x j)).prod := by
    rw [map_prod, ← List.prod_ofFn, ← Subalgebra.coe_val, map_list_prod, List.map_ofFn]
    congr 1
    exact congrArg List.ofFn (funext fun j => by simp [toEven, aeval_X])
  rw [h1, list_prod_gen, topBig_tmul]
  simp only [topExt, vec]
  rw [← ExteriorAlgebra.ιMulti_apply, ← ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.liftAlternating_apply_ιMulti, ExteriorAlgebra.liftAlternating_apply_ιMulti]

theorem toMultiset_sum_single {α : Type*} [DecidableEq α] {m : ℕ} (x : Fin m → α) :
    Finsupp.toMultiset (∑ j, Finsupp.single (x j) 1) = Finset.univ.val.map x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_multiset_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  have : (fun j => ({x j} : Multiset α)) = (fun a => ({a} : Multiset α)) ∘ x := rfl
  rw [this, ← Multiset.map_map, Multiset.sum_map_singleton]

theorem toMultiset_injective' {α : Type*} [DecidableEq α] :
    Function.Injective (Finsupp.toMultiset : (α →₀ ℕ) → Multiset α) := fun f g h => by
  rw [← Finsupp.toMultiset_toFinsupp f, h, Finsupp.toMultiset_toFinsupp]

theorem coeff_prod_X {m : ℕ} (x : Fin m → Fin n × Fin n) (d : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) d =
      if Finset.univ.val.map x = Finsupp.toMultiset d then 1 else 0 := by
  classical
  have e : (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (x j) 1) 1 :=
    (monomial_sum_one _ _).symm
  rw [e, coeff_monomial, ← toMultiset_sum_single]
  simp only [toMultiset_injective'.eq_iff]

theorem topForm_self (v : Fin n → Fin n → ℂ) : topForm n n v = (Pi.basisFun ℂ (Fin n)).det v := by
  simp [topForm]

theorem det_single_perm (π : Equiv.Perm (Fin n)) :
    (Pi.basisFun ℂ (Fin n)).det (fun j => Pi.single (π j) 1) = ((Equiv.Perm.sign π : ℤ) : ℂ) := by
  have : (fun j => (Pi.single (π j) 1 : Fin n → ℂ)) = (Pi.basisFun ℂ (Fin n)) ∘ π := by
    funext j; simp
  rw [this, AlternatingMap.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]

theorem det_single_not_inj (a : Fin n → Fin n) (ha : ¬ Function.Injective a) :
    (Pi.basisFun ℂ (Fin n)).det (fun j => Pi.single (a j) 1) = 0 := by
  refine AlternatingMap.map_eq_zero_of_not_injective _ _ fun h => ha fun i j hij => h ?_
  simp [hij]


open Classical in
theorem topCoeff_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    GlobalTheory.GoodMetric.topCoeff (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) := by
  unfold GlobalTheory.GoodMetric.topCoeff
  simp_rw [coeff_prod_X, toMultiset_sum_single]
  by_cases hm : m = n
  swap
  · have h0 : topForm n m = 0 := by simp [topForm, hm]
    rw [h0]
    simp only [AlternatingMap.zero_apply, mul_zero]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    intro heq
    have := congrArg Multiset.card heq
    simp at this
    exact hm this
  subst hm
  rw [topForm_self, topForm_self]
  set a : Fin m → Fin m := fun j => (x j).1 with ha_def
  set b : Fin m → Fin m := fun j => (x j).2 with hb_def

  have hcond : ∀ w : Equiv.Perm (Fin m),
      Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, w c)) →
        Function.Injective a ∧ Function.Injective b := by
    intro w heq
    have h1 := congrArg (Multiset.map Prod.fst) heq
    have h2 := congrArg (Multiset.map Prod.snd) heq
    simp only [Multiset.map_map] at h1 h2
    have e1 : Multiset.map (Prod.fst ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val := by
      simp
    have e2 : Multiset.map (Prod.snd ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val := by
      simpa using Multiset.map_univ_val_equiv w
    rw [e1] at h1
    rw [e2] at h2
    constructor
    · have hn : (Multiset.map (Prod.fst ∘ x) Finset.univ.val).Nodup := by rw [h1]; exact Finset.univ.nodup
      exact fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij
    · have hn : (Multiset.map (Prod.snd ∘ x) Finset.univ.val).Nodup := by rw [h2]; exact Finset.univ.nodup
      exact fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij
  by_cases hab : Function.Injective a ∧ Function.Injective b
  swap
  · have : (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).1 1) *
        (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).2 1) = 0 := by
      rcases not_and_or.mp hab with h | h
      · rw [det_single_not_inj a h, zero_mul]
      · rw [det_single_not_inj b h, mul_zero]
    rw [this]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    exact fun heq => hab (hcond w heq)
  obtain ⟨ha, hb⟩ := hab
  let π : Equiv.Perm (Fin m) := Equiv.ofBijective a (Finite.injective_iff_bijective.mp ha)
  let τ : Equiv.Perm (Fin m) := Equiv.ofBijective b (Finite.injective_iff_bijective.mp hb)
  have hπ : ∀ j, (x j).1 = π j := fun j => rfl
  have hτ : ∀ j, (x j).2 = τ j := fun j => rfl
  simp_rw [hπ, hτ, det_single_perm]
  have hx : x = (fun c => (c, (τ * π⁻¹) c)) ∘ π := by
    funext j
    simp [Prod.ext_iff, hπ, hτ]
  have hmap : Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c)) := by
    rw [hx, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [Finset.sum_eq_single (τ * π⁻¹)]
  · rw [if_pos hmap, mul_one, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    push_cast
    ring
  · intro w _ hw
    rw [if_neg, mul_zero]
    intro heq
    apply hw
    ext c
    have hc : (c, w c) ∈ Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c)) := by
      rw [← hmap, heq]; simp
    obtain ⟨c', _, hc'⟩ := Multiset.mem_map.mp hc
    simp only [Prod.mk.injEq] at hc'
    obtain ⟨rfl, h⟩ := hc'
    exact congrArg Fin.val h.symm
  · intro h; exact absurd (Finset.mem_univ _) h

theorem topCoeff_eq_topBig (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    GlobalTheory.GoodMetric.topCoeff P = topBig n (toEven n P : Big n) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨l, hl⟩ : ∃ l : List (Fin n × Fin n), (l : Multiset _) = Finsupp.toMultiset u :=
      ⟨_, Multiset.coe_toList _⟩
    have hu : u = ∑ j, Finsupp.single (l.get j) 1 := by
      apply toMultiset_injective'
      rw [toMultiset_sum_single, Fin.univ_val_map, List.ofFn_get, hl]
    have hmon : (monomial u c : MvPolynomial (Fin n × Fin n) ℂ) = c • ∏ j, X (l.get j) := by
      rw [hu, show (∏ j, X (l.get j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (l.get j) 1) 1 from
        (monomial_sum_one _ _).symm, smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, Subalgebra.coe_smul, map_smul, smul_eq_mul, topBig_toEven_prod, ← topCoeff_prod]
    unfold GlobalTheory.GoodMetric.topCoeff
    simp only [coeff_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  | add p q hp hq =>
    rw [map_add (f := _), Subalgebra.coe_add, map_add (f := _), ← hp, ← hq]
    unfold GlobalTheory.GoodMetric.topCoeff
    simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.GrassModel.TopRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffEqTensorSquareTopCoefficientStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_eq_tensorSquareTopCoefficient : ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), GlobalTheory.GoodMetric.topCoeff P = GlobalTheory.GrassModel.topBig n (GlobalTheory.GrassModel.toEven n P : GlobalTheory.GrassModel.Big n) := by
  first | exact @GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig | exact GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig | (intros; apply GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig <;> assumption)
end
end
