module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTwoTriplesAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaLiftSmoothAut
theorem theta_lift_of_cusp_form_isSmoothAutomorphic : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → IsAutFunSm R.θ (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  intro _hL hP D _hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ _hI
  have hM := GlobalTheory.PairLift.haar_vert hRB hG t hi (Nat.succ_le_of_lt hj)
  have hw : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω := (hG.arrows.th t i j hi hj).weil
  exact isAutFunSm_thetaLift hP.cuspRapidDecay hRB.inf hw hΦ hM.1 hM.2 hφ.1 hφ.2.1
end GlobalTheory.ThetaLiftSmoothAut
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isSmoothAutomorphic : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → IsAutFunSm R.θ (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  first | exact @_root_.GlobalTheory.ThetaLiftSmoothAut.theta_lift_of_cusp_form_isSmoothAutomorphic | exact _root_.GlobalTheory.ThetaLiftSmoothAut.theta_lift_of_cusp_form_isSmoothAutomorphic | (intros; apply _root_.GlobalTheory.ThetaLiftSmoothAut.theta_lift_of_cusp_form_isSmoothAutomorphic <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftIsSmoothAutomorphic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.UpConjLift
theorem upward_theta_lift_isSmoothAutomorphic : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsAutFunSm R.θ (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ _
  have hq : GlobalTheory.Mem.Th.IsQuot (G.P i).V (G.mP i).ν (G.mP i).fd := by
    have := (hG.meas.P i hi.le).2 (by omega)
    exact ⟨this.1.1, this.2⟩
  exact (conj_lift hPr.cuspRapidDecay hR.inf (G.dn i).ω (hG.arrows.dn i hi).weil hΦ hq ⟨hφ.1, hφ.2.1⟩).2
end GlobalTheory.UpConjLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_upward_theta_lift_isSmoothAutomorphic : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsAutFunSm R.θ (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.UpConjLift.upward_theta_lift_isSmoothAutomorphic | exact _root_.GlobalTheory.UpConjLift.upward_theta_lift_isSmoothAutomorphic | (intros; apply _root_.GlobalTheory.UpConjLift.upward_theta_lift_isSmoothAutomorphic <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationRankLeDim
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace GlobalTheory.ThK.PolRank
open Module
theorem polarization_rank_le : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  have hX := fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s _ (X.θ w) (h.herm.sig w) (h.herm.cartan w)
  have hW := fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists d r' s' _ (W.θ w) (h.skew.sig w) (h.skew.cartan w)
  choose A hA hAθ using hX
  choose C hC hCθ using hW
  have hfr : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := by
    refine ⟨one_mul _, fun w => ?_, fun w => ?_⟩
    · rw [incM_map_piInf, one_smul]; exact hA w
    · rw [incM_map_piInf]; exact hC w
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) r s r' s' B.ψ B.emb
    (incM F X.J) (incM F W.J) M.co 1 Complex.I A C h.base.cm h.base.std hfr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.T.archActionReadings_compatible GlobalTheory.T.archHeisenbergDerivatives_exist (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives GlobalTheory.T.archHeisenbergDerivatives_exist) F E σ n d r s r' s' X W M B.ψ B.emb
    A C Φ h.base.cm h.base.std hfr hAθ hCθ hΦ
  rw [← hr]
  exact (rank_range_le Φ).trans (rank_tens_le F r s r' s')
end GlobalTheory.ThK.PolRank
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_rank_le_dim : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  first | exact @_root_.GlobalTheory.ThK.PolRank.polarization_rank_le | exact _root_.GlobalTheory.ThK.PolRank.polarization_rank_le | (intros; apply _root_.GlobalTheory.ThK.PolRank.polarization_rank_le <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealWeilRepresentationSchurScalar
section
open scoped Matrix
noncomputable section
open MeasureTheory Complex
open scoped Real RealInnerProductSpace ComplexConjugate FourierTransform SchwartzMap
namespace GlobalTheory.RealWeil.SchurSchwartz
variable {l : Type} [Fintype l]
end GlobalTheory.RealWeil.SchurSchwartz
namespace GlobalTheory.RealWeil.SchurSchwartz
variable {l : Type} [Fintype l]
theorem weil_schwartz_schur_lemma : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] (U : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
    (∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(U h₁) = GlobalTheory.RealWeil.rhoFun w ⇑(U h)) →
    (∀ h : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, U h = a • h := by
  intro _ l _ U hc hU
  by_cases h0 : ∃ (g : Sch l) (y : EuclideanSpace ℝ l), g y ≠ 0
  · obtain ⟨g, y0, hg⟩ := h0
    have hb := conj_mul_eq U hc hU g g y0
    rw [Complex.conj_mul', Complex.conj_mul'] at hb
    have h2 : ‖U g y0‖ ^ 2 = ‖g y0‖ ^ 2 := by exact_mod_cast hb
    have hnb : ‖U g y0‖ = ‖g y0‖ := by
      first
        | exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
        | exact pow_left_injective₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero h2
        | nlinarith [norm_nonneg (U g y0), norm_nonneg (g y0)]
    have hb0 : U g y0 ≠ 0 := by
      intro h
      apply hg
      rw [← norm_eq_zero, ← hnb, h, norm_zero]
    have hcb : conj (U g y0) ≠ 0 := (map_ne_zero _).2 hb0
    refine ⟨conj (g y0 / U g y0), ?_, fun f => ?_⟩
    · rw [Complex.norm_conj, norm_div, hnb, div_self (norm_ne_zero_iff.2 hg)]
    · ext x
      have e1 := conj_mul_eq U hc hU f (trS (y0 - x) g) x
      have hxy : x + (y0 - x) = y0 := by abel
      rw [hc (trPt (y0 - x)) g (trS (y0 - x) g) (coe_trS _ _), coe_trS, rhoFun_trPt, rhoFun_trPt, hxy] at e1
      have e2 := congrArg conj e1
      simp only [map_mul, Complex.conj_conj] at e2
      rw [SchwartzMap.smul_apply, smul_eq_mul, map_div₀, div_mul_eq_mul_div, eq_div_iff hcb, e2, mul_comm]
  · push_neg at h0
    refine ⟨1, by simp, fun h => ?_⟩
    ext x
    rw [h0 (U h) x, one_smul, h0 h x]
end GlobalTheory.RealWeil.SchurSchwartz
end
end

section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_weil_representation_schur_scalar : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] (U : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
    (∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(U h₁) = GlobalTheory.RealWeil.rhoFun w ⇑(U h)) →
    (∀ h : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, U h = a • h := by
  first | exact @_root_.GlobalTheory.RealWeil.SchurSchwartz.weil_schwartz_schur_lemma | exact _root_.GlobalTheory.RealWeil.SchurSchwartz.weil_schwartz_schur_lemma | (intros; apply _root_.GlobalTheory.RealWeil.SchurSchwartz.weil_schwartz_schur_lemma <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteCuspFormAverageApprox
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp
namespace GlobalTheory.KFinCuspApprox
theorem isCuspForm_kFinite_average : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D)
    (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ φ : GA D N.V → ℂ, IsAutFunSm θ N.V φ →
    IsCuspFun N.V φ → IsCuspFun N.V (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro D θ hθ _ N τ e he φ hφ hc
  set A : Formalism.REAL.KG (N.M.ε τ) → GA D N.V :=
    fun k => atTau θ N.V τ ((N.M.fr τ)⁻¹ * Formalism.REAL.toMK k * N.M.fr τ) with hA
  have hAc : Continuous A := (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ).comp_continuous
    GlobalTheory.SeriesToClosure.continuous_conjK fun k => GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k
  have hl : LeftInv (GQ N.V) φ := hφ.left
  have havg : ∀ x, GlobalTheory.KFinCuspApprox.avgN θ N τ e φ x = ∫ k, e k * φ (x * A k) ∂(Formalism.REAL.muK (N.M.ε τ)) :=
    fun x => rfl
  have hlA : LeftInv (GQ N.V) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := fun γ hγ g => by
    simp only [havg, mul_assoc, hl γ hγ]
  refine (isCuspFun_iff hlA).2 fun W hW => funext fun x => ?_
  have hcc := cocompact_single hW
  have h0 := congrFun ((isCuspFun_iff hl).1 hc W hW)
  set NN := NA (IsoFlag.single hW) with hNN
  have h𝓕 := isFundamentalDomain_stdDom ((GQ N.V).subgroupOf NN) (Measure.haar : Measure NN)
  have hfin := hcc.measure_ne_top h𝓕
  show constTermOn (GQ N.V) NN _ x = 0
  rw [hcc.constTermOn_eq_zero_iff h𝓕 hlA x]
  have hz : ∀ y, ∫ n in stdDom ((GQ N.V).subgroupOf NN), φ ((n : GA D N.V) * y) ∂(Measure.haar : Measure NN) = 0 :=
    fun y => (hcc.constTermOn_eq_zero_iff h𝓕 hl y).1 (h0 y)
  obtain ⟨K0, hK0, hs⟩ := hcc
  have hcont : Continuous fun p : NN × Formalism.REAL.KG (N.M.ε τ) => φ ((p.1 : GA D N.V) * x * A p.2) :=
    hφ.cont.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul (hAc.comp continuous_snd))
  obtain ⟨C, hC⟩ := (hK0.prod (isCompact_univ (X := Formalism.REAL.KG (N.M.ε τ)))).exists_bound_of_continuousOn
    hcont.continuousOn
  have hb : ∀ (n : NN) k, ‖φ ((n : GA D N.V) * x * A k)‖ ≤ C := fun n k => by
    obtain ⟨γ, hγ, hk⟩ := hs n
    have h1 := hC (γ * n, k) ⟨hk, trivial⟩
    have h2 := hl ((γ : NN) : GA D N.V) (Subgroup.mem_subgroupOf.1 hγ) ((n : GA D N.V) * x * A k)
    simp only [Subgroup.coe_mul] at h1
    have e1 : ((γ : NN) : GA D N.V) * n * x * A k = (γ : GA D N.V) * ((n : GA D N.V) * x * A k) := by
      simp only [mul_assoc]
    rwa [e1, h2] at h1
  obtain ⟨Ce, hCe⟩ := (isCompact_univ (X := Formalism.REAL.KG (N.M.ε τ))).exists_bound_of_continuousOn he.continuousOn
  haveI : IsFiniteMeasure ((Measure.haar : Measure NN).restrict (stdDom ((GQ N.V).subgroupOf NN))) :=
    isFiniteMeasure_restrict.2 hfin
  have hint : Integrable (Function.uncurry fun (n : NN) (k : Formalism.REAL.KG (N.M.ε τ)) => e k * φ ((n : GA D N.V) * x * A k))
      (((Measure.haar : Measure NN).restrict (stdDom ((GQ N.V).subgroupOf NN))).prod (Formalism.REAL.muK (N.M.ε τ))) := by
    refine Integrable.mono' (integrable_const (Ce * C)) ?_ (ae_of_all _ fun p => ?_)
    · exact ((he.comp continuous_snd).mul hcont).aestronglyMeasurable
    · show ‖e p.2 * φ ((p.1 : GA D N.V) * x * A p.2)‖ ≤ Ce * C
      rw [norm_mul]
      exact mul_le_mul (hCe p.2 trivial) (hb p.1 p.2) (norm_nonneg _) ((norm_nonneg _).trans (hCe p.2 trivial))
  calc ∫ n in stdDom ((GQ N.V).subgroupOf NN), GlobalTheory.KFinCuspApprox.avgN θ N τ e φ ((n : GA D N.V) * x)
        ∂(Measure.haar : Measure NN)
      = ∫ n in stdDom ((GQ N.V).subgroupOf NN), ∫ k, e k * φ ((n : GA D N.V) * x * A k) ∂(Formalism.REAL.muK (N.M.ε τ))
        ∂(Measure.haar : Measure NN) := by simp only [havg]
    _ = ∫ k, ∫ n in stdDom ((GQ N.V).subgroupOf NN), e k * φ ((n : GA D N.V) * x * A k)
        ∂(Measure.haar : Measure NN) ∂(Formalism.REAL.muK (N.M.ε τ)) := integral_integral_swap hint
    _ = ∫ k, e k * 0 ∂(Formalism.REAL.muK (N.M.ε τ)) := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only
        rw [integral_const_mul, ← hz (x * A k)]
        simp only [mul_assoc]
    _ = 0 := by simp
end GlobalTheory.KFinCuspApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_cuspForm_average_approx : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ φ : GA D N.V → ℂ, IsAutFunSm θ N.V φ → IsCuspFun N.V φ → IsCuspFun N.V (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average | exact _root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average | (intros; apply _root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealEmbeddingsOfCharactersOfSameExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RealMapsChars
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.RealMapsChars
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealMapsChars in
theorem GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  intro hP F E _ _ _ _ _ σ B a a' Γ Xa Xb oa oa' ob ob' R hA hB hR
  obtain ⟨hV, hV'⟩ := GlobalTheory.T.weilOperators_eq_at_realPlaces_same_exponents F E σ B a a' Γ Xa Xb oa oa' ob ob' hA hB
  have lV : ∀ g ∈ UAt σ Γ.V (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (g, 1) Φ = ob (g, 1) Φ :=
    fun g hg Φ hΦ => hV g 1 hg one_mem_uAt Φ hΦ
  have lV' : ∀ g ∈ UAt σ Γ.V' (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (g, 1) Φ = ob' (g, 1) Φ :=
    fun g hg Φ hΦ => hV' g 1 hg one_mem_uAt Φ hΦ
  have lW : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (1, h) Φ = ob (1, h) Φ :=
    fun h hh Φ hΦ => hV 1 h one_mem_uAt hh Φ hΦ
  have lW' : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (1, h) Φ = ob' (1, h) Φ :=
    fun h hh Φ hΦ => hV' 1 h one_mem_uAt hh Φ hΦ
  have bV : ∀ g ∈ UAt σ Γ.V (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), ob (g, 1) Φ = oa (g, 1) Φ :=
    fun g hg Φ hΦ => (lV g hg Φ hΦ).symm
  have bV' : ∀ g ∈ UAt σ Γ.V' (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), ob' (g, 1) Φ = oa' (g, 1) Φ :=
    fun g hg Φ hΦ => (lV' g hg Φ hΦ).symm
  have bW : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), ob (1, h) Φ = oa (1, h) Φ :=
    fun h hh Φ hΦ => (lW h hh Φ hΦ).symm
  have bW' : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), ob' (1, h) Φ = oa' (1, h) Φ :=
    fun h hh Φ hΦ => (lW' h hh Φ hΦ).symm
  refine ⟨⟨hR.quot.onto, ?_, ?_⟩, ⟨hR.quot'.onto, ?_, ?_⟩, ?_, ?_, hR.nontriv, ?_⟩
  · intro γ hγ f hf f₁ h
    exact hR.quot.lie γ hγ f hf f₁ (actsD_of_eqOn (fun t => bV _ (hγ.2 _)) h)
  · intro k hk f hf f₁ h
    exact hR.quot.cpt k hk f hf f₁ (acts_of_eqOn (bV k hk.1) h)
  · intro γ hγ f hf f₁ h
    exact hR.quot'.lie γ hγ f hf f₁ (actsD_of_eqOn (fun t => bV' _ (hγ.2 _)) h)
  · intro k hk f hf f₁ h
    exact hR.quot'.cpt k hk f hf f₁ (acts_of_eqOn (bV' k hk.1) h)
  · intro γ hγ f hf f' hf' f₁ f₁' h h'
    exact hR.lie γ hγ f hf f' hf' f₁ f₁' (actsD_of_eqOn (fun t => bW _ (hγ.2 _)) h)
      (actsD_of_eqOn (fun t => bW' _ (hγ.2 _)) h')
  · intro k hk f hf f' hf' f₁ f₁' h h'
    exact hR.cpt k hk f hf f' hf' f₁ f₁' (acts_of_eqOn (bW k hk.1) h) (acts_of_eqOn (bW' k hk.1) h')
  · intro N h1 h2
    refine hR.irred N (fun γ hγ f hf f₁ h => h1 γ hγ f hf f₁ (actsD_of_eqOn (fun t => lW _ (hγ.2 _)) h))
      (fun k hk f hf f₁ h => h2 k hk f hf f₁ (acts_of_eqOn (lW k hk.1) h))
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  first | exact @_root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent | exact _root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent | (intros; apply _root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsKFiniteCuspOfTypeOfMemGKGenerated
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGKForms
open Matrix Filter Topology GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes GlobalTheory.CuspGK
open Formalism.IndefR.Mult
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
section Sig
variable (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} {S : SPar} {φ ψ : GA D V → ℂ}
include hPr hθ
theorem hasTypeAt_of_cuspForm_gK (hV : V.SigOK) (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ S φ) : φ ∈ typeSub θ V τ S :=
  GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ V τ S φ hPr.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique) hPr.harishChandraModules
    hPr.casselmanWallach hθ hV (goodPar_of_isTypeAt hV h) hφ h
theorem isTypeAt_of_cuspForm_gK (hV : V.SigOK) (h : IsTypeAt θ V τ S φ) (hψ : IsAutFunSm θ V ψ) (h' : ψ ∈ typeSub θ V τ S) :
    IsTypeAt θ V τ S ψ :=
  GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series θ V τ S ψ hPr.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique) hPr.harishChandraModules
    hPr.casselmanWallach hθ hV (goodPar_of_isTypeAt hV h) hψ h'
theorem isTypeAt_add_of_sigma (hV : V.SigOK) (hφ : IsAutFunSm θ V φ) (hψ : IsAutFunSm θ V ψ) (h : IsTypeAt θ V τ S φ)
    (h' : IsTypeAt θ V τ S ψ) : IsTypeAt θ V τ S (φ + ψ) :=
  _root_.GlobalTheory.CuspGKForms.isTypeAt_of_cuspForm_gK hPr hθ hV h (GlobalTheory.Mem.AutSpace.isAutFunSm_add hφ hψ)
    (add_mem (_root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV hφ h) (_root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV hψ h'))
theorem isTypeAt_liftDeriv_of_sigma (hV : V.SigOK) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ' S φ) : IsTypeAt θ V τ' S (Rder θ V τ X φ) := by
  refine _root_.GlobalTheory.CuspGKForms.isTypeAt_of_cuspForm_gK hPr hθ hV h (GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hφ) fun C hC δ hδ => ?_
  obtain ⟨t, ht⟩ := exists_quotient_near hθ hX hφ hC (half_pos hδ)
  have hk := GlobalTheory.Mem.Lift.exp_mem hX t
  have m1 : rTr V (oneP θ V τ X t) φ ∈ typeSub θ V τ' S :=
    _root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV (isAutFunSm_rTr_atTau D θ hθ V φ hφ τ _ hk) (isTypeAt_rTr hθ h hk)
  have m2 : ((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ) ∈ typeSub θ V τ' S :=
    Submodule.smul_mem _ _ (add_mem m1 (Submodule.smul_mem _ _ (_root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV hφ h)))
  obtain ⟨χ, hχ, h2⟩ := m2 C hC (δ / 2) (half_pos hδ)
  refine ⟨χ, hχ, fun x hx => ?_⟩
  have := norm_sub_le_norm_sub_add_norm_sub (Rder θ V τ X φ x)
    ((((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ)) x) (χ x)
  linarith [ht x hx, h2 x hx]
theorem isTypeAt_add_cuspForm (hφ : IsAutFunSm θ V φ) (hψ : IsAutFunSm θ V ψ) (h : IsTypeAt θ V τ S φ)
    (h' : IsTypeAt θ V τ S ψ) : IsTypeAt θ V τ S (φ + ψ) := by
  obtain ⟨s, hs⟩ := exists_sigOK V
  exact _root_.GlobalTheory.CuspGKForms.isTypeAt_add_of_sigma (V := GlobalTheory.SmoothAutCheck.reSig V s) hPr hθ hs
    ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s φ).2 hφ) ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s ψ).2 hψ) h h'
theorem isTypeAt_liftDeriv_cuspForm {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ' S φ) : IsTypeAt θ V τ' S (Rder θ V τ X φ) := by
  obtain ⟨s, hs⟩ := exists_sigOK V
  exact _root_.GlobalTheory.CuspGKForms.isTypeAt_liftDeriv_of_sigma (V := GlobalTheory.SmoothAutCheck.reSig V s) hPr hθ hs hX
    ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s φ).2 hφ) h
end Sig
variable {S : D.what₂.Tau → SPar}
def cuspFormGKSubmodule (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ) (M : DSModel V S) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | IsKFinCuspOfType θ M f}
  zero_mem' := ⟨Formalism.IndefR.Mult.isAutFunSm_zero θ V, Formalism.IndefR.Mult.isCuspFun_zero V,
    fun τ => (GlobalTheory.TypeAtTest.isTypeAt_zero θ V).2
      ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, M.ds τ, M.fr_unit τ, M.fr_gram τ⟩,
    ⊥, inferInstance, zero_mem _, fun τ g _ _ h hh => by
      rw [Submodule.mem_bot] at hh ⊢
      subst hh
      rfl⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3, W, hW, a4, a5⟩ ⟨b1, b2, b3, W', hW', b4, b5⟩
    refine ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add a1 b1, GlobalTheory.MultMem.isCuspFun_add a1.toIsAutFun b1.toIsAutFun a2 b2,
      fun τ => _root_.GlobalTheory.CuspGKForms.isTypeAt_add_cuspForm hPr hθ a1 b1 (a3 τ) (b3 τ), W ⊔ W', inferInstance, Submodule.add_mem_sup a4 b4,
      fun τ g hg hk h hh => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hh
    exact Submodule.add_mem_sup (a5 τ g hg hk y hy) (b5 τ g hg hk z hz)
  smul_mem' := by
    rintro c a ⟨a1, a2, a3, W, hW, a4, a5⟩
    exact ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_smul c a1, Formalism.IndefR.Mult.isCuspFun_smul V a2 c,
      fun τ => GlobalTheory.Mem.Th.isTypeAt_smul c (a3 τ), W, hW, W.smul_mem c a4, a5⟩
theorem isGKSubmodule_cuspFormGKSubmodule (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ) (M : DSModel V S) :
    IsGKSub θ M (_root_.GlobalTheory.CuspGKForms.cuspFormGKSubmodule hPr hθ M) := by
  constructor
  · intro τ g hg f hf
    obtain ⟨a1, a2, a3, W, hW, a4, a5⟩ := hf
    exact ⟨isAutFunSm_rTr_atTau D θ hθ V f a1 τ g hg.1, GlobalTheory.Cusp.isCuspFun_rTr a2 _,
      fun τ' => isTypeAt_rTr hθ (a3 τ') hg.1, W, hW, a5 τ g hg.1 hg.2 f a4, a5⟩
  · intro τ X hX f hf
    obtain ⟨a1, a2, a3, W, hW, a4, a5⟩ := hf
    refine ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX a1, GlobalTheory.CuspLie.isCuspFun_Rder hθ hX a1 a2,
      fun τ' => _root_.GlobalTheory.CuspGKForms.isTypeAt_liftDeriv_cuspForm hPr hθ hX a1 (a3 τ'),
      (Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 ((Submodule.FG.map₂ _ Module.Finite.fg_top (GlobalTheory.CuspLie.fg_comap hW)).map _),
      ⟨derEnd hθ τ X ⟨f, a1.smooth⟩,
        Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := X)) (n := (⟨f, a1.smooth⟩ : SmFun θ V)) a4,
        GlobalTheory.CuspLie.derEnd_coe hθ hX ⟨f, a1.smooth⟩⟩, fun τ' g hg hk => ?_⟩
    have hr := isRealPt_atTau hθ τ' hg
    have hi : IsRealPt θ (atTau θ V τ' g)⁻¹ :=
      ⟨inv_mem hr.1, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V _⟩
    set k := atTau θ V τ' g
    have hle : Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype) ≤
        (((Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype).comap
          (rTrLin k)).comap (SmFun θ V).subtype := by
      refine Submodule.map₂_le.2 fun Z _ u hu => ?_
      refine ⟨_, Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := adAt θ k⁻¹ τ Z))
        (n := ⟨rTr V k u.1, rTr_mem hθ hr u.2⟩) (a5 τ' g hg hk _ hu), ?_⟩
      show RderC θ V τ (adAt θ k⁻¹ τ Z) (rTr V k u.1) = rTr V k (RderC θ V τ Z u.1)
      funext y
      have := congrFun (RderC_rTr hθ hi τ Z (rTr V k u.1)) (y * k)
      rw [show rTr V k⁻¹ (rTr V k u.1) = u.1 from funext fun y => by simp [rTr]] at this
      rw [rTr, this, rTr, mul_inv_cancel_right]
    rintro _ ⟨u, hu, rfl⟩
    exact hle hu
theorem isKFiniteCuspOfType_of_mem_gKGenerated : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M ψ → ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f :=
  fun hPr _ θ _ _ M hθ _ hψ _ hf => gkGen_le θ M (A := _root_.GlobalTheory.CuspGKForms.cuspFormGKSubmodule hPr hθ M) hψ (_root_.GlobalTheory.CuspGKForms.isGKSubmodule_cuspFormGKSubmodule hPr hθ M) hf
end GlobalTheory.CuspGKForms
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_gK_submodule_of_type : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M ψ → ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f := by
  first | exact @_root_.GlobalTheory.CuspGKForms.isKFiniteCuspOfType_of_mem_gKGenerated | exact _root_.GlobalTheory.CuspGKForms.isKFiniteCuspOfType_of_mem_gKGenerated | (intros; apply _root_.GlobalTheory.CuspGKForms.isKFiniteCuspOfType_of_mem_gKGenerated <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsLinearFunctionalAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
open GlobalTheory.ThK GlobalTheory.KSplit
noncomputable section
namespace GlobalTheory.LinWSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.LinWSplit
namespace GlobalTheory.LinWSplit
theorem exists_linearFunctional_at_split_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∃ ι, M.IsLinW B.ψ t b c ι := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c
  have hcm : IsCMExt F E σ := hP.base.cm
  have hstd := hP.base.std
  have hX := hP.herm.herm
  have hY := hP.skew.skew
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdX : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.herm.sig w0)
    have e : (X.J.map (B.emb w0).1).det = (B.emb w0).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.skew.sig w0)
    have e : (W.J.map (B.emb w0).1).det = (B.emb w0).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hA : IsUnit (X.J.map t).det := by
    rw [show (X.J.map t).det = (t : E →+* Fv F v) X.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB : IsUnit (W.J.map t)ᵀ.det := by
    rw [Matrix.det_transpose, show (W.J.map t).det = (t : E →+* Fv F v) W.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  have hat_add : ∀ x y : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → At (evFin F v) y →
      At (evFin F v) (x + y) := fun x y hx hy r hr => by rw [smul_add, hx r hr, hy r hr, add_zero]
  have heq := fun (u u' : Matrix (Fin n) (Fin d) (AE F E)) => locCo_eq_of hcm X W hX hY M t u u'
  let P0 : Matrix (Fin n) (Fin d) (Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) := fun Y => b.1 * Y * c.1ᵀ
  let Q : Matrix (Fin n) (Fin d) (Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) :=
    fun z => -((X.J.map t)⁻¹ * (b⁻¹).1ᵀ * z * (c⁻¹).1 * ((W.J.map t)ᵀ)⁻¹)
  have hP0 : ∀ P, P0 ((b⁻¹).1 * P * (c⁻¹).1ᵀ) = P := by
    intro P
    simp only [P0, ← Matrix.mul_assoc]
    rw [show b.1 * (b⁻¹).1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
      show (c⁻¹).1ᵀ * c.1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]
  have hQ : ∀ P, Q (-(b.1ᵀ * X.J.map t * P * (W.J.map t)ᵀ * c.1)) = P := by
    intro P
    simp only [Q, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((b⁻¹).1ᵀ), show (b⁻¹).1ᵀ * b.1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp,
      Matrix.one_mul, ← Matrix.mul_assoc (c.1), show c.1 * (c⁻¹).1 = 1 by simp, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hB, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hA]
  have hcoX0 : ∀ Y, GlobalTheory.FlipMatch.coX t b c (U (P0 Y) 0) = Y := by
    intro Y
    simp only [GlobalTheory.FlipMatch.coX, hU0, P0, ← Matrix.mul_assoc]
    rw [show (b⁻¹).1 * b.1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
      show c.1ᵀ * (c⁻¹).1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]
  have hcoY1 : ∀ z, GlobalTheory.FlipMatch.coY σ X W t b c (U 0 (Q z)) = z := by
    intro z
    simp only [GlobalTheory.FlipMatch.coY, hU1, Q, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hB,
      ← Matrix.mul_assoc (b.1ᵀ), show b.1ᵀ * (b⁻¹).1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.one_mul,
      show (c⁻¹).1 * c.1 = 1 by simp, Matrix.mul_one]
  have hcoY0 : ∀ P, GlobalTheory.FlipMatch.coY σ X W t b c (U P 0) = 0 := by
    intro P; simp [GlobalTheory.FlipMatch.coY, hU1]
  have hcoX1 : ∀ P, GlobalTheory.FlipMatch.coX t b c (U 0 P) = 0 := by
    intro P; simp [GlobalTheory.FlipMatch.coX, hU0]
  have hU00 : GlobalTheory.LatVac.locCo M.co v (U 0 0) = 0 :=
    locCo_eq_zero hcm X W hX hY M t _ (hUat 0 0) (hU0 0 0) (hU1 0 0)
  have hadd0 : ∀ P P', GlobalTheory.LatVac.locCo M.co v (U (P + P') 0) =
      GlobalTheory.LatVac.locCo M.co v (U P 0) + GlobalTheory.LatVac.locCo M.co v (U P' 0) := by
    intro P P'
    rw [← map_add (f := _)]
    apply heq _ _ (hUat _ _) (hat_add _ _ (hUat _ _) (hUat _ _))
    · rw [Matrix.map_add _ (map_add _), hU0, hU0, hU0]
    · rw [Matrix.map_add _ (map_add _), hU1, hU1, hU1, add_zero]
  have hadd1 : ∀ P P', GlobalTheory.LatVac.locCo M.co v (U 0 (P + P')) =
      GlobalTheory.LatVac.locCo M.co v (U 0 P) + GlobalTheory.LatVac.locCo M.co v (U 0 P') := by
    intro P P'
    rw [← map_add (f := _)]
    apply heq _ _ (hUat _ _) (hat_add _ _ (hUat _ _) (hUat _ _))
    · rw [Matrix.map_add _ (map_add _), hU0, hU0, hU0, add_zero]
    · rw [Matrix.map_add _ (map_add _), hU1, hU1, hU1]
  let wT : Matrix (Fin n) (Fin d) (Fv F v) →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun Y => GlobalTheory.LatVac.locCo M.co v (U (P0 Y) 0)
      map_zero' := by
        show GlobalTheory.LatVac.locCo M.co v (U (b.1 * 0 * c.1ᵀ) 0) = 0
        rw [Matrix.mul_zero, Matrix.zero_mul]; exact hU00
      map_add' := fun Y Y' => by
        show GlobalTheory.LatVac.locCo M.co v (U (b.1 * (Y + Y') * c.1ᵀ) 0) = _
        rw [Matrix.mul_add, Matrix.add_mul]; exact hadd0 _ _ }
  let wM : Matrix (Fin n) (Fin d) (Fv F v) →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun z => GlobalTheory.LatVac.locCo M.co v (U 0 (Q z))
      map_zero' := by
        show GlobalTheory.LatVac.locCo M.co v (U 0 (Q 0)) = 0
        have : Q 0 = 0 := by simp [Q]
        rw [this]; exact hU00
      map_add' := fun z z' => by
        show GlobalTheory.LatVac.locCo M.co v (U 0 (Q (z + z'))) = _
        have : Q (z + z') = Q z + Q z' := by simp only [Q, Matrix.mul_add, Matrix.add_mul, neg_add]
        rw [this]; exact hadd1 _ _ }
  have hwT : ∀ Y, wT Y = GlobalTheory.LatVac.locCo M.co v (U (P0 Y) 0) := fun _ => rfl
  have hwM : ∀ z, wM z = GlobalTheory.LatVac.locCo M.co v (U 0 (Q z)) := fun _ => rfl
  have hform := fun (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) =>
    (locCo_form M.co v x u).trans (evFin_symp hcm X W hX hY t b c x u hx)
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hstd.1 v
  have hψne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_anyCharacter (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψne wT wM
    (fun Y Y' => by
      rw [hwT, hwT, hform _ _ (hUat _ _), hcoX0, hcoX0, hcoY0, hcoY0]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun z z' => by
      rw [hwM, hwM, hform _ _ (hUat _ _), hcoX1, hcoX1, hcoY1, hcoY1]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun Y z => by
      rw [hwT, hwM, hform _ _ (hUat _ _), hcoX0, hcoX1, hcoY0, hcoY1]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj M.co v w
      refine ⟨GlobalTheory.FlipMatch.coX t b c u, GlobalTheory.FlipMatch.coY σ X W t b c u, ?_⟩
      rw [hwT, hwM, ← map_add (f := _)]
      apply heq _ _ (hat_add _ _ (hUat _ _) (hUat _ _)) hu
      · rw [Matrix.map_add _ (map_add _), hU0, hU0, add_zero]
        exact hP0 _
      · rw [Matrix.map_add _ (map_add _), hU1, hU1, zero_add]
        exact hQ _)
  have hφ₁ : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    have e2 : GlobalTheory.LatVac.locCo M.co v u = wT (GlobalTheory.FlipMatch.coX t b c u) := by
      rw [hwT]
      apply heq _ _ hu (hUat _ _)
      · rw [hU0]; exact (hP0 _).symm
      · rw [hU1]; exact hu0
    rw [e1, e2]
    exact congrFun (htr _ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    have e2 : GlobalTheory.LatVac.locCo M.co v u = wM (GlobalTheory.FlipMatch.coY σ X W t b c u) := by
      rw [hwM]
      apply heq _ _ hu (hUat _ _)
      · rw [hU0]; exact hu1
      · rw [hU1]; exact (hQ _).symm
    have hcx : GlobalTheory.FlipMatch.coY σ X W t b c x = 0 := by simp [GlobalTheory.FlipMatch.coY, hx0]
    rw [e1, e2, congrFun (hmu _ φ hφ), GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp σ _ _ x u hx),
      evFin_symp hcm X W hX hY t b c x u hx, hcx, ← GlobalTheory.LatVac.psiAt_apply]
    simp [GlobalTheory.FlipMatch.pairM, GlobalTheory.FlipMatch.coX]
end GlobalTheory.LinWSplit
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_linearFunctional_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∃ ι, M.IsLinW B.ψ t b c ι := by
  first | exact @_root_.GlobalTheory.LinWSplit.exists_linearFunctional_at_split_place | exact _root_.GlobalTheory.LinWSplit.exists_linearFunctional_at_split_place | (intros; apply _root_.GlobalTheory.LinWSplit.exists_linearFunctional_at_split_place <;> assumption)
end
end
