module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepRankZeroWittEmbeddingValueAtZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixesLatticeVacuumPeriodLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalMatrixOfMemPeriodLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalMatrixOfMemPeriodLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.LamPre

theorem exists_mat_of_mem_lamC : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧ embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := by
  intro D S T a b hS hT δ N N' x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hx
  refine ⟨(LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm, ?_, ?_, ?_⟩
  · have e : toHom S T hS hT ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm) = y := by
      unfold toHom
      rw [show ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm).reindex (finCongr hT) (finCongr hS)
          = LinearMap.toMatrix' y from by ext i j; simp, Matrix.toLin'_toMatrix']
    rw [e]; exact hy
  · have e : toHom S T hS hT ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm) = y := by
      unfold toHom
      rw [show ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm).reindex (finCongr hT) (finCongr hS)
          = LinearMap.toMatrix' y from by ext i j; simp, Matrix.toLin'_toMatrix']
    rw [e]
  · exact ⟨GlobalTheory.VacUnique.finRat S T _, GlobalTheory.VacUnique.finRat_inf S T _, GlobalTheory.VacUnique.finRat_fin S T _⟩

end GlobalTheory.AdForm.LamPre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalMatrixOfMemPeriodLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalMatrix_of_mem_periodLattice : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧ embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := by
  first | exact @GlobalTheory.AdForm.LamPre.exists_mat_of_mem_lamC | exact GlobalTheory.AdForm.LamPre.exists_mat_of_mem_lamC | (intros; apply GlobalTheory.AdForm.LamPre.exists_mat_of_mem_lamC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedVac

theorem halfBack : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (e : AE D) (u : WO S T),
    IsHalf e (actO S T g h u) → IsHalf e u := by
  intro D S T g h e u hu
  have hA : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom T h))
  have hB : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom S g))
  have cancel : ∀ X : Matrix (Fin T.rank) (Fin S.rank) (AE D),
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) X)
        (Formalism.L2.Theta.mt S g⁻¹))) (Formalism.L2.Theta.mt S g) = X := by
    intro X
    simp only [Matrix.mul_assoc, hB, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have key : e • actO S T g h u = actO S T g h u := by
    ext i j; exact hu i j
  have key2 : e • u = u := by
    have h1 := congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) M) (Formalism.L2.Theta.mt S g)) key
    simp only [actO] at h1
    rw [cancel u] at h1
    simp only [Matrix.mul_smul, Matrix.smul_mul] at h1
    rw [cancel u] at h1
    exact h1
  intro i j
  have := congrFun (congrFun key2 i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this

theorem norm_weilRepresentation_thetaFunction_preserved : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : (AE D)ˣ →* Circle) (om : Om S T),
    IsWeilDatumO ψ S T μ μ om → ∀ f, IsThetaFunO ψ S T f → ∀ p (m : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsCovolOne (ratL T S) m 𝓕 → nrm2 m 𝓕 (om p f) = nrm2 m 𝓕 f := by
  intro D ψ S T μ om hW f hf p m 𝓕 hm
  have hU := hW.om_unit m 𝓕 hm.1 hm.2.1 p f hf
  have hf' := hW.om_pres p f hf
  haveI : OpensMeasurableSpace (WO S T) := ⟨le_rfl⟩
  have key : ∀ F : WO S T → ℂ, Continuous F → nrm2 m 𝓕 F = (∫⁻ w in 𝓕, ‖F w‖ₑ ^ 2 ∂m).toReal := by
    intro F hF
    unfold nrm2
    have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
      (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun w => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [key _ hf'.cont, key _ hf.cont, hU]

theorem latMove : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' →
    ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True),
      ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := GlobalTheory.T.unitaryPair_maps_completedHomLattice_onto_translate

theorem latSign : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a)
    (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f →
    ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
    toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ v, GlobalTheory.AdTh.IsFinOf S T γ v →
    ∀ w, alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT γ)) * heisO ψ S T v f w = f w := GlobalTheory.T.heisenberg_fixes_latticeVacuum_periodLattice

theorem lamPre : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N',
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧
      embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := GlobalTheory.T.exists_rationalMatrix_of_mem_periodLattice

theorem fixedLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a)
    (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f →
    xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc)
      (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' f hf hl x hx z
  obtain ⟨γ, hγ, rfl, v, hv⟩ := lamPre D S T a b hS hT δ N N' x hx
  have hs := latSign D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' f hf hl γ hγ v hv
  have hu := GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP f hf γ v hv
  rw [← hu]
  simp only [xiN]
  rw [← hs]
  ring

theorem vac_moved : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ N N', Moves S hS g N → Moves T hT h N' → IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) ∧ xiN θ S T hS hT δ sc (om (g, h) f) ∈ Formalism.L2.Th1.H.Th (HV sc) (alV D.host.d sc) (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ∧ xiN θ S T hS hT δ sc (om (g, h) f) ≠ 0 := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hW f hf g hg h hh N N' hN hN'
  obtain ⟨hstd, hv⟩ := hf
  have hhol : IsHol θ S T ψ f := ⟨hv.theta, hv.fock⟩
  have hI := GlobalTheory.T.om_pureTensorO_comm D ψ θ S T a b hS hT δ sc hP μ om hW g hg h hh f hhol
  have hth' : IsThetaFunO ψ S T (om (g, h) f) := hW.om_pres _ f hv.theta
  have hvac : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) := by
    refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ?_, fock := hI.1.2, norm := ?_ }⟩
    · refine ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩
      · obtain ⟨u, hu, rfl⟩ := latMove D S T a b hS hT hP.gS hP.gT g hg h hh N N' hN hN' u' hu'
        have h2 : actO S T g h u + actO S T g h u = actO S T g h (u + u) := by
          simp only [actO, Matrix.mul_add, Matrix.add_mul]
        have h3 := hv.lat.1 u hu
        rw [two_nsmul] at h3 ⊢
        rw [h2, ← hW.om_heis g h _ f hv.theta, h3]
      · obtain ⟨u, hu, rfl⟩ := latMove D S T a b hS hT hP.gS hP.gT g hg h hh N N' hN hN' u' hu'
        rw [← hW.om_heis g h u f hv.theta, hv.lat.2 e he u hu (halfBack D S T g h e u hhalf)]
    · refine ⟨hv.norm.1, fun p hp => ?_⟩
      show nrm2 p.1 p.2 (om (g, h) f) = 1
      rw [norm_weilRepresentation_thetaFunction_preserved D ψ S T μ om hW f hv.theta (g, h) p.1 p.2 hp]
      exact hv.norm.2 p hp
  have hne : om (g, h) f ≠ 0 := by
    intro h0
    obtain ⟨p, hp⟩ := hvac.2.norm.1
    have h1 := hvac.2.norm.2 p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hII := GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective D ψ θ S T a b hS hT δ sc hP
  refine ⟨hvac, ⟨GlobalTheory.SCV.analyticOnNhd_of_differentiable (hII.1 _ hI.1) _,
    fixedLine D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' _ hth' hvac.2.lat⟩, fun h0 => hne (hII.2 _ hth' h0)⟩

end GlobalTheory.MovedVac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedWeilVacuum_eq_vacuum_of_movedLattices : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ N N', Moves S hS g N → Moves T hT h N' → IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) ∧ xiN θ S T hS hT δ sc (om (g, h) f) ∈ Formalism.L2.Th1.H.Th (HV sc) (alV D.host.d sc) (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ∧ xiN θ S T hS hT δ sc (om (g, h) f) ≠ 0 := by
  first | exact @GlobalTheory.MovedVac.vac_moved | exact GlobalTheory.MovedVac.vac_moved | (intros; apply GlobalTheory.MovedVac.vac_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.IdVMul

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, w, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w' => ?_, u * w, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w') (hb w')
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

variable {v : Pl D}

theorem intAt_mul {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [(finPart D).map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem intAt_zero : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [(finPart D).map_zero]; exact zero_mem _⟩

theorem intAt_add {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [(finPart D).map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {a : AE D} (ha : a ∈ intAt D (· = v)) : -a ∈ intAt D (· = v) :=
  ⟨neg_mem ha.1, by rw [(finPart D).map_neg]; exact neg_mem ha.2⟩

theorem pairA_zero_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)
  rw [zero_mul]

theorem evalV_single_self (v : Pl D) : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1

theorem evalV_single_ne {v w : Pl D} (hw : w ≠ v) : evalV D.host.F w (singleV D.host.F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw

theorem single_int (v : Pl D) : singleV D.host.F v 1 ∈ intAf D.host.F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_single_self]; exact one_mem _
  · rw [evalV_single_ne hw]; exact zero_mem _

theorem mul_single {α : Af D.host.F} (hα : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    α * singleV D.host.F v 1 = α := by
  apply RestrictedProduct.ext
  intro w
  change evalV D.host.F w (α * singleV D.host.F v 1) = evalV D.host.F w α
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [evalV_single_self, mul_one]
  · rw [hα w hw, zero_mul]

theorem gen_mem {𝔞 : FI D} {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0)
    {a : D.host.E} (ha : a ∈ 𝔞) : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] a ∈ idV 𝔞 v :=
  AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, rfl⟩

theorem tmul_mem_idAt {α : Af D.host.F} (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0) (x : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hαv _ w.2, TensorProduct.zero_tmul]

theorem tmul_one_mem_intAt {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨tmul_mem_idAt hαv 1, ?_⟩
  change α ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D
  exact AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩

theorem tmul_mul_tmul' (α β : Af D.host.F) (a b : D.host.E) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] b) =
      (pairA D.host.F 0 (α * β)) ⊗ₜ[D.host.F] (a * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_zero_mul]

theorem incA_mul_tmul (x : D.host.E) (α : AF D.host.F) (b : D.host.E) :
    incA D x * (α ⊗ₜ[D.host.F] b : AE D) = α ⊗ₜ[D.host.F] (x * b) := by
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) * (α ⊗ₜ[D.host.F] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mul_mem_idV {𝔞 𝔟 : FI D} {a b : AE D} (ha : a ∈ idV 𝔞 v) (hb : b ∈ idV 𝔟 v) : a * b ∈ idV (𝔞 * 𝔟) v := by
  induction ha using AddSubgroup.closure_induction with
  | mem a' ha' =>
    obtain ⟨α, hα, hαv, a, ha, rfl⟩ := ha'
    induction hb using AddSubgroup.closure_induction with
    | mem b' hb' =>
      obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := hb'
      rw [tmul_mul_tmul']
      refine gen_mem (fun w => ?_) (fun w hw => ?_) (FractionalIdeal.mul_mem_mul ha hb)
      · rw [map_mul]; exact mul_mem (hα w) (hβ w)
      · rw [map_mul, hαv w hw, zero_mul]
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg x _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg x _ h => rw [neg_mul]; exact neg_mem h

theorem incA_mul_mem {𝔞 𝔟 : FI D} {x : D.host.E} (hx0 : x ≠ 0)
    (hx : ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) {t : AE D} (ht : t ∈ idV 𝔟 v) :
    incA D x * t ∈ idV (𝔞 * 𝔟) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem t' ht' =>
    obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := ht'
    have e : incA D x * ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] b) =
        ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] x : AE D) * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b) := by
      rw [incA_mul_tmul, tmul_mul_tmul', mul_single hβv]
    rw [e]
    refine mul_mem_idV ((hx _).2 ⟨?_, tmul_mem_idAt hβv x⟩)
      (gen_mem (single_int v) (fun w hw => evalV_single_ne hw) hb)
    rw [incA_mul_tmul, inv_mul_cancel₀ hx0]
    exact tmul_one_mem_intAt hβ hβv
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

theorem idV_mul_gen : ∀ (D : D7) (v : Pl D) (𝔞 𝔟 : FI D) (x y : D.host.E), x ≠ 0 → y ≠ 0 → (∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) → (∀ s, s ∈ idV 𝔟 v ↔ incA D y⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) → ∀ s, s ∈ idV (𝔞 * 𝔟) v ↔ incA D (x * y)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 𝔟 x y hx0 hy0 hx hy
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  intro s
  constructor
  · intro hs
    refine AddSubgroup.closure_induction (p := fun s _ => incA D (x * y)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v))
      ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨α, hα, hαv, c, hc, rfl⟩
      refine FractionalIdeal.mul_induction_on (C := fun c => incA D (x * y)⁻¹ * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] c) ∈
        intAt D (· = v) ∧ (pairA D.host.F 0 α) ⊗ₜ[D.host.F] c ∈ idAt D (· = v)) hc ?_ ?_
      · intro a ha b hb
        have hA := (hx _).1 (gen_mem hα hαv ha)
        have hB := (hy _).1 (gen_mem (single_int v) (fun w hw => evalV_single_ne hw) hb)
        have e : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * b) =
            ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b) := by
          rw [tmul_mul_tmul', mul_single hαv]
        rw [e]
        refine ⟨?_, Ideal.mul_mem_right _ _ hA.2⟩
        have e2 : incA D (x * y)⁻¹ * (((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) *
            ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b)) =
            (incA D x⁻¹ * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a)) *
              (incA D y⁻¹ * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b)) := by
          rw [mul_inv, (incA D).map_mul]; ring
        rw [e2]
        exact intAt_mul hA.1 hB.1
      · intro c d hc hd
        rw [TensorProduct.tmul_add, mul_add]
        exact ⟨intAt_add hc.1 hd.1, add_mem hc.2 hd.2⟩
    · rw [mul_zero]; exact ⟨intAt_zero, zero_mem _⟩
    · intro a b _ _ ha hb
      rw [mul_add]; exact ⟨intAt_add ha.1 hb.1, add_mem ha.2 hb.2⟩
    · intro a _ ha
      rw [mul_neg]; exact ⟨intAt_neg ha.1, neg_mem ha.2⟩
  · rintro ⟨ho, hs⟩
    have hso : s = incA D x * (incA D y * (incA D (x * y)⁻¹ * s)) := by
      rw [← mul_assoc, ← mul_assoc, ← (incA D).map_mul, ← (incA D).map_mul, mul_inv_cancel₀ hxy0, (incA D).map_one,
        one_mul]
    have ht : incA D y * (incA D (x * y)⁻¹ * s) ∈ idV 𝔟 v := by
      refine (hy _).2 ⟨?_, Ideal.mul_mem_left _ _ ho.1⟩
      rw [← mul_assoc, ← (incA D).map_mul, inv_mul_cancel₀ hy0, (incA D).map_one, one_mul]
      exact ho
    rw [hso]
    exact incA_mul_mem hx0 hx ht

end GlobalTheory.SeeSaw.IdVMul

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def dualC (𝔟 : FI D) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {c | ∀ b ∈ 𝔟, star b * c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range}
  add_mem' := fun {x y} hx hy b hb => by
    rw [mul_add]; exact add_mem (hx b hb) (hy b hb)
  zero_mem' := fun b _ => by rw [mul_zero]; exact zero_mem _
  smul_mem' := fun r x hx b hb => by
    obtain ⟨o, ho⟩ := hx b hb
    refine ⟨r * o, ?_⟩
    rw [map_mul, ho, Algebra.smul_def]; ring

theorem mem_dualC {𝔟 : FI D} {c : D.host.E} :
    c ∈ dualC 𝔟 ↔ ∀ b ∈ 𝔟, star b * c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := Iff.rfl

def crd {m : ℕ} (q : Matrix (Fin m) (Fin S.rank) D.host.E) : (Fin S.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin m → D.host.E) :=
  (Matrix.mulVecLin q).restrictScalars (𝓞 D.host.E)

def splitL (d : HypDec S S₀ ρ) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) : Lat S :=
  (⨅ i : Fin ρ, (𝔟 i : Submodule (𝓞 D.host.E) D.host.E).comap ((LinearMap.proj i).comp (crd d.qX))) ⊓
    L₀.comap (crd d.q0) ⊓ ⨅ i : Fin ρ, (dualC (𝔟 i)).comap ((LinearMap.proj i).comp (crd d.qY))

theorem mem_splitL (d : HypDec S S₀ ρ) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (y : Fin S.rank → D.host.E) :
    y ∈ splitL d L₀ 𝔟 ↔ (∀ i : Fin ρ, (d.qX *ᵥ y) i ∈ 𝔟 i) ∧ d.q0 *ᵥ y ∈ L₀ ∧ ∀ i : Fin ρ, (d.qY *ᵥ y) i ∈ dualC (𝔟 i) := by
  simp only [splitL, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply, LinearMap.proj_apply]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

variable (d : HypDec S S₀ ρ)

theorem qX_e : d.qX * d.e = 1 := d.e'e
theorem qX_i₀ : d.qX * d.i₀ = 0 := by
  have h := congrArg Matrix.conjTranspose d.i₀e'
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
    Matrix.conjTranspose_zero, HypDec.qX, HypDec.qY, Matrix.mul_assoc] using h
theorem qX_e' : d.qX * d.e' = 0 := d.e'e'
theorem qY_e : d.qY * d.e = 0 := d.ee
theorem qY_i₀ : d.qY * d.i₀ = 0 := by
  have h := congrArg Matrix.conjTranspose d.i₀e
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
    Matrix.conjTranspose_zero, HypDec.qX, HypDec.qY, Matrix.mul_assoc] using h
theorem qY_e' : d.qY * d.e' = 1 := by
  have h := congrArg Matrix.conjTranspose d.e'e
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
    Matrix.conjTranspose_one, HypDec.qY, Matrix.mul_assoc] using h
theorem wittDecomposition_coreProj_mul_e_eq_zero : d.q0 * d.e = 0 := by
  simp only [HypDec.q0, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.i₀e, Matrix.mul_zero]
theorem wittDecomposition_coreProj_mul_core_eq_one : d.q0 * d.i₀ = 1 := by
  rw [HypDec.q0, Matrix.mul_assoc, d.iso,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (gram_det_ne S₀))]
theorem wittZeroProjection_mul_dualBasis_eq_zero : d.q0 * d.e' = 0 := by
  simp only [HypDec.q0, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.i₀e', Matrix.mul_zero]

theorem gram_eq : S.gram = d.qYᴴ * d.qX + d.q0ᴴ * (S₀.gram * d.q0) + d.qXᴴ * d.qY := by
  have h0 : d.q0ᴴ * S₀.gram = S.gram * d.i₀ := by
    simp only [HypDec.q0, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (gram_det_ne S₀)), Matrix.mul_one]
  have hx : d.qXᴴ = S.gram * d.e' := by simp [HypDec.qX, gram_conjTranspose]
  have hy : d.qYᴴ = S.gram * d.e := by simp [HypDec.qY, gram_conjTranspose]
  rw [hy, hx, ← Matrix.mul_assoc d.q0ᴴ, h0]
  simp only [Matrix.mul_assoc, ← Matrix.mul_add, d.sum_eq_one_rat, Matrix.mul_one]

theorem rat_mulVec_gen {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (t : AF D.host.F) (x : Fin n → D.host.E) :
    rat M *ᵥ (fun l => t ⊗ₜ[D.host.F] (1 * x l)) = fun k => t ⊗ₜ[D.host.F] (1 * (M *ᵥ x) k) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, one_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k l) * (t ⊗ₜ[D.host.F] x l) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem rat_mulVec_mem_latV {S' : HSp D} (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat S'}
    (hM : ∀ x ∈ L, M *ᵥ x ∈ L') (P : Pl D → Prop) {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    rat M *ᵥ y ∈ latV S' L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [rat_mulVec_gen]
    exact AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, _, hM x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

variable {d} {L₀ : Lat S₀} {𝔟 : ℕ → FI D}

theorem e_mem {w : Fin ρ → D.host.E} (hw : ∀ i : Fin ρ, w i ∈ 𝔟 i) : d.e *ᵥ w ∈ splitL d L₀ 𝔟 := by
  refine (mem_splitL d L₀ 𝔟 _).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mulVec_mulVec, qX_e, Matrix.one_mulVec]; exact hw i
  · rw [Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_e_eq_zero, Matrix.zero_mulVec]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, qY_e, Matrix.zero_mulVec]; exact zero_mem _

theorem i₀_mem {x : Fin S₀.rank → D.host.E} (hx : x ∈ L₀) : d.i₀ *ᵥ x ∈ splitL d L₀ 𝔟 := by
  refine (mem_splitL d L₀ 𝔟 _).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mulVec_mulVec, qX_i₀, Matrix.zero_mulVec]
    show (0 : D.host.E) ∈ (𝔟 i : Submodule (𝓞 D.host.E) D.host.E); exact zero_mem _
  · rw [Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec]; exact hx
  · rw [Matrix.mulVec_mulVec, qY_i₀, Matrix.zero_mulVec]; exact zero_mem _

theorem e'_mem {w : Fin ρ → D.host.E} (hw : ∀ i : Fin ρ, w i ∈ dualC (𝔟 i)) : d.e' *ᵥ w ∈ splitL d L₀ 𝔟 := by
  refine (mem_splitL d L₀ 𝔟 _).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mulVec_mulVec, qX_e', Matrix.zero_mulVec]
    show (0 : D.host.E) ∈ (𝔟 i : Submodule (𝓞 D.host.E) D.host.E); exact zero_mem _
  · rw [Matrix.mulVec_mulVec, wittZeroProjection_mul_dualBasis_eq_zero, Matrix.zero_mulVec]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, qY_e', Matrix.one_mulVec]; exact hw i

theorem single_mem_of_mem {I : ℕ → Submodule (𝓞 D.host.E) D.host.E} (i : Fin ρ) {a : D.host.E} (ha : a ∈ I i) (j : Fin ρ) :
    (Pi.single i a : Fin ρ → D.host.E) j ∈ I j := by
  by_cases h : j = i
  · subst h; rw [Pi.single_eq_same]; exact ha
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

def colProj {m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) :
    Matrix (Fin S.rank) (Fin m) D.host.E := Matrix.of fun k l => f k i * q i l

theorem colProj_mulVec {m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ)
    (x : Fin m → D.host.E) : colProj q f i *ᵥ x = f *ᵥ Pi.single i ((q *ᵥ x) i) := by
  funext k
  simp only [colProj, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.single_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]

theorem colMul_rat {m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ)
    (y : Fin m → AE D) : colMul (rat f) i ((rat q *ᵥ y) i) = rat (colProj q f i) *ᵥ y := by
  funext k
  simp only [colMul, colProj, rat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem colMul_eq_mulVec {m n : ℕ} (x : Mx D m n) (i : Fin n) (a : AE D) : colMul x i a = x *ᵥ Pi.single i a := by
  funext k
  simp only [colMul, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, mul_comm]

theorem mulVec_eq_sum_colMul {m n : ℕ} (x : Mx D m n) (w : Fin n → AE D) : x *ᵥ w = ∑ i, colMul x i (w i) := by
  funext k
  simp only [colMul, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

variable (d L₀ 𝔟)

theorem monoAt_splitL (v : Pl D) : MonoAt d (splitL d L₀ 𝔟) L₀ v := by
  have hX : ∀ i : Fin ρ, ∀ x ∈ splitL d L₀ 𝔟, colProj d.qX d.e i *ᵥ x ∈ splitL d L₀ 𝔟 := fun i x hx => by
    rw [colProj_mulVec]
    exact e_mem (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i
      (((mem_splitL d L₀ 𝔟 x).1 hx).1 i))
  have hY : ∀ i : Fin ρ, ∀ x ∈ splitL d L₀ 𝔟, colProj d.qY d.e' i *ᵥ x ∈ splitL d L₀ 𝔟 := fun i x hx => by
    rw [colProj_mulVec]
    exact e'_mem (single_mem_of_mem (I := fun j => dualC (𝔟 j)) i (((mem_splitL d L₀ 𝔟 x).1 hx).2.2 i))
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hX i) _ hy
    · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hY i) _ hy
    · exact rat_mulVec_mem_latV d.q0 (fun x hx => ((mem_splitL d L₀ 𝔟 x).1 hx).2.1) _ hy
  · rintro ⟨h1, h3, h2⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        (show d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY = 1 from by
          have h := congrArg rat d.sum_eq_one_rat
          simpa only [rat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), HypDec.jX, HypDec.j0,
            HypDec.jY, HypDec.pX, HypDec.p0, HypDec.pY] using h), Matrix.one_mulVec]
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
    exact rat_mulVec_mem_latV d.i₀ (fun x hx => i₀_mem hx) _ h2

theorem line_splitL (v : Pl D) (i : Fin ρ) (a : AE D) :
    colMul d.jX i a ∈ latV S (splitL d L₀ 𝔟) (· = v) ↔ a ∈ idV (𝔟 i) v := by
  constructor
  · intro ha
    have key : ∀ y ∈ latV S (splitL d L₀ 𝔟) (· = v), (d.pX *ᵥ y) i ∈ idV (𝔟 i) v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
        rw [Set.mem_singleton_iff] at hc
        subst hc
        change (rat d.qX *ᵥ _) i ∈ _
        rw [rat_mulVec_gen]
        refine AddSubgroup.subset_closure ⟨β, hβi, hβ, _, ?_, rfl⟩
        rw [one_mul]
        exact ((mem_splitL d L₀ 𝔟 x).1 hx).1 i
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
      | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz
    have h := key _ ha
    rwa [colMul_eq_mulVec, Matrix.mulVec_mulVec, (show d.pX * d.jX = 1 from by
      have h := congrArg rat (qX_e d)
      simpa only [rat, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), HypDec.pX, HypDec.jX] using h), Matrix.one_mulVec, Pi.single_eq_same] at h
  · intro ha
    rw [idV] at ha
    induction ha using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, b, hb, rfl⟩ := hz
      have e : colMul d.jX i (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
          rat d.e *ᵥ fun l => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (Pi.single i b : Fin ρ → D.host.E) l) := by
        rw [colMul_eq_mulVec]
        change rat d.e *ᵥ _ = _
        congr 1
        funext l
        by_cases h : l = i
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      rw [e, rat_mulVec_gen]
      exact AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, _,
        e_mem (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i hb), rfl⟩
    | zero =>
      have : colMul d.jX i 0 = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    | add z z' _ _ hz hz' =>
      have : colMul d.jX i (z + z') = colMul d.jX i z + colMul d.jX i z' := by funext k; simp [colMul, add_mul]
      rw [this]; exact add_mem hz hz'
    | neg z _ hz =>
      have : colMul d.jX i (-z) = -colMul d.jX i z := by funext k; simp [colMul]
      rw [this]; exact neg_mem hz

end GlobalTheory.SeeSaw.SplitLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompact
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.KComm

variable {D : D7}

theorem comm_of_unitary_isom {m : ℕ} {u J : Matrix (Fin m) (Fin m) ℂ} (hu : uᴴ * u = 1) (hJ : uᴴ * J * u = J) :
    u * J = J * u := by
  have hu' : u * uᴴ = 1 := mul_eq_one_comm.1 hu
  calc u * J = u * (uᴴ * J * u) := by rw [hJ]
    _ = (u * uᴴ) * J * u := by simp only [Matrix.mul_assoc]
    _ = J * u := by rw [hu', Matrix.one_mul]

theorem compAt_K_comm (θ : InfFam D) (hθ : IsInfFam θ) (n : ℕ) (k : G D n) (hk : k ∈ K D n) (τ : D.what₂.Tau) :
    compAt θ τ (mat k) * blk4 0 1 (-1) 0 = blk4 0 1 (-1) 0 * compAt θ τ (mat k) := by
  have e1 : compAt θ τ (mat k) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k := rfl
  have e2 : θ τ = AdelicU.infProj (embOverOf D τ) := AdelicU.eq_infProj hθ (embOverOf D τ) rfl
  have hk' : k ∈ AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hw := (AdelicU.mem_levelAll.1 hk').2 (placeOf D τ)
  have hunit := (GlobalTheory.Doubling.mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) (Jst D n) 1 k).1 hw
  rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)] at hunit
  simp only [Matrix.one_mul, Matrix.mul_one] at hunit
  rw [← e2, ← e1] at hunit
  have hiso := (AdelicU.archEquiv (Jst D n) (isCMExt_host D) (embOverOf D τ)
    (AdelicU.projArch D.sp.cm.sig (Jst D n) (placeOf D τ) k)).2
  have hiso' : (compAt θ τ (mat k))ᴴ * (Jst D n).map (embOverOf D τ).1 * compAt θ τ (mat k) =
      (Jst D n).map (embOverOf D τ).1 := by
    rw [e1, e2, AdelicU.infMat_infProj (Jst D n) (isCMExt_host D)]
    exact hiso
  rw [Jst, GlobalTheory.CartanPt.blkJ_map] at hiso'
  exact comm_of_unitary_isom hunit hiso'

end GlobalTheory.StdUnn.KComm

namespace GlobalTheory.StdUnn.KComm

theorem exists_stdInv_comm_K : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ θ : InfFam D, IsInfFam θ → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ k : GA D (dblSp A), κ k ∈ K D A.rank → ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * s' τ = s' τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  intro D A μ hμ κ hκ θ hθ
  obtain ⟨k₀, -, hk₀⟩ := GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv D θ hθ A.rank μ hμ
  have hch : ∀ g τ, (Tm A μ).map (tauE D τ) * compAt θ τ (mat (κ g)) =
      compAt θ τ (Formalism.L2.Theta.mt (dblSp A) g) * (Tm A μ).map (tauE D τ) := by
    intro g τ
    have h2 := congrArg (compAt θ τ) (hκ g)
    have hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul, hr] at h2
    exact h2
  refine ⟨fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀)), fun τ => ?_, fun k hk τ => ?_⟩
  · have h := hch (κ.symm k₀) τ
    rw [κ.apply_symm_apply, hk₀] at h
    exact h.symm
  · dsimp only
    set T := (Tm A μ).map (tauE D τ) with hTdef
    have hT : IsUnit T.det := by
      have h := (GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ).2.1.map (tauE D τ)
      rwa [RingHom.map_det] at h
    set X := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)
    set S := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀))
    set U := compAt θ τ (mat (κ k))
    have hX : T * U = X * T := hch k τ
    have hS : T * stdInv A.rank μ τ = S * T := by
      have h := hch (κ.symm k₀) τ
      rw [κ.apply_symm_apply, hk₀] at h
      exact h
    have hU : U * stdInv A.rank μ τ = stdInv A.rank μ τ * U := by
      rw [stdInv, Matrix.mul_smul, Matrix.smul_mul, compAt_K_comm θ hθ A.rank (κ k) hk τ]
    have key : X * S * T = S * X * T := by
      calc X * S * T = X * (T * stdInv A.rank μ τ) := by rw [hS, Matrix.mul_assoc]
        _ = T * U * stdInv A.rank μ τ := by rw [hX, Matrix.mul_assoc]
        _ = T * stdInv A.rank μ τ * U := by rw [Matrix.mul_assoc, hU, Matrix.mul_assoc]
        _ = S * X * T := by rw [hS, Matrix.mul_assoc, hX, Matrix.mul_assoc]
    have h2 := congrArg (· * T⁻¹) key
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT, Matrix.mul_one] using h2

end GlobalTheory.StdUnn.KComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompactStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardCartanInvolution_commute_compact : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ θ : InfFam D, IsInfFam θ → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ k : GA D (dblSp A), κ k ∈ K D A.rank → ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * s' τ = s' τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  first | exact @GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K | exact GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K | (intros; apply GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemFiniteAdelicUnitaryGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Corev.EmbAGfC

variable {D : D7}

abbrev finfR (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GfC_iff' (V : HSp D) (g : GA D V) : g ∈ GfC V ↔ (Formalism.L2.Theta.mt V g).map (finfR D) = 1 := by
  show infHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand' {k n : ℕ} (x : Mx D k n) (m : Mx D n n) (y : Mx D n k) (hm : m.map (finfR D) = 1) :
    (x ⬝ m ⬝ y).map (finfR D) = (x ⬝ y).map (finfR D) := by
  have e1 : (x ⬝ m ⬝ y).map (finfR D) = x.map (finfR D) ⬝ m.map (finfR D) ⬝ y.map (finfR D) := by
    rw [Matrix.map_mul (f := finfR D), Matrix.map_mul (f := finfR D)]
  have e2 : (x ⬝ y).map (finfR D) = x.map (finfR D) ⬝ y.map (finfR D) := Matrix.map_mul (f := finfR D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GfC' {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GfC A) :
    o.emb (a, 1) ∈ GfC S := by
  rw [mem_GfC_iff'] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finfR D)), map_sand' _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one,
    ← Matrix.map_add _ (map_add (finfR D)), o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem wittCoreEmbedding_mem_finiteAdelicUnitaryGroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {g : GA D S₀} (hg : g ∈ GfC S₀) :
    d.emb0 g ∈ GfC S := by
  rw [mem_GfC_iff'] at hg ⊢
  rw [HypDec.unitaryMatrix_wittCoreEmbedding, Matrix.map_add _ (map_add (finfR D)), Matrix.map_add _ (map_add (finfR D)), map_sand' _ _ _ hg,
    ← Matrix.map_add _ (map_add (finfR D)), ← Matrix.map_add _ (map_add (finfR D)), d.sum_eq_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem embA_mem_GfC_fin : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (κ : GA D A), κ ∈ GfC A → embA d o κ ∈ GfC S := by
  intro D S S₀ A L ρ d o κ hκ
  rw [embA_apply]
  exact wittCoreEmbedding_mem_finiteAdelicUnitaryGroup d (orth_emb_mem_GfC' o hκ)

end GlobalTheory.Corev.EmbAGfC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValConjSubLt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair

namespace GlobalTheory.SeeSaw.LevChi

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colChar colPos superSum)
open GlobalTheory.SymBridge

section Split

variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt q.e PP)
include h

theorem val_rat_lt {y : D.host.E} (hy : PP.valuation D.host.E y < 1) : valuation K (q.pr (incA D y)) < 1 := by
  obtain ⟨r, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hy.le
  have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
    le_antisymm (LevelTest.val_le_one q _) (not_lt.1 fun h' => d.2 ((LevelTest.val_lt_one_iff q h _).1 h'))
  have hr : r ∈ PP.asIdeal := by
    refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP r).1 ?_
    show PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E r) < 1
    rw [← e, map_mul]
    exact (mul_le_of_le_one_right' (PP.valuation_le_one _)).trans_lt hy
  have := (LevelTest.val_lt_one_iff q h r).2 hr
  rwa [show (r : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd, mul_one] at this


set_option maxHeartbeats 1000000 in
theorem val_pr_lt {z : AE D} (hz : Valued.v (adAt D.host.F PP (toEAf D z)) < 1) : valuation K (q.pr z) < 1 := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := D.host.F) (toEAf D z) {PP} (γ := 1) one_ne_zero
  have hN' := hN PP (Finset.mem_singleton_self PP)
  have h1 : PP.valuation D.host.E y < 1 := by
    rw [← valued_algebraMap, ← adAt_inclE D.host.F, ← sub_eq_iff_eq_add.2 e, map_sub]
    exact Valuation.map_sub_lt _ hz (valued_nat_mul_lt hr hN')
  have hnat : ∀ M : ℕ, (M : 𝓞 D.host.E) ∈ PP.asIdeal → valuation K (M : K) < 1 := fun M hM => by
    simpa using (LevelTest.val_lt_one_iff q h _).2 hM
  let sw := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
  have hf : finPart D (z - incA D y) = (N : Af D.host.F ⊗[D.host.F] D.host.E) * sw.symm r := by
    apply sw.injective
    rw [map_mul, map_natCast, AlgEquiv.apply_symm_apply]
    show toEAf D (z - incA D y) = _
    rw [RingHom.map_sub, e]
    exact add_sub_cancel_left _ _
  have h2 : valuation K (q.pr (z - incA D y)) < 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · refine (GlobalTheory.FinPl.SplitApprox.val_le q (Ideal.absNorm PP.asIdeal)
        (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)) _ 0 (zero_mem _) ?_).trans_lt
        (hnat _ (Ideal.absNorm_mem _))
      rw [hf, Nat.cast_zero, zero_mul, mul_zero]
    · refine (GlobalTheory.FinPl.SplitApprox.val_le q N hpos _ _ ((GlobalTheory.IdemSupport.mem_intAE_iff _).2 ?_) hf).trans_lt (hnat _ ?_)
      · exact (show Lev.swapAE D (sw.symm r) = r from sw.apply_symm_apply r).symm ▸ hr
      · rw [LevRead.valued_natCast] at hN'
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP _).1 hN'
  have h3 := (valuation K).map_add_lt h2 (val_rat_lt q h h1)
  rwa [← map_add, sub_add_cancel] at h3

end Split

section Local

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP)

end Local

end GlobalTheory.SeeSaw.LevChi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFractionalIdealRelations
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ChainIdeals

theorem host_ne_zero (D : D7) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ≠ 0 ∧ D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ dI D ≠ 0 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
  · rw [h, zero_mul, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul] at hP; exact zero_ne_one hP
  · rw [dI] at h; rw [h, zero_mul] at hP; exact zero_ne_one hP

end GlobalTheory.SeeSaw.ChainIdeals
end
