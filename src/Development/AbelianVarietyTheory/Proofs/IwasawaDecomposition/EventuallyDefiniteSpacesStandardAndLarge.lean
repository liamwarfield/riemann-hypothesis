module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotVstdOfGramOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionToG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.StdSize

theorem vstd_size_ev : Top.Ev fun K => ∀ X : Stages, K.Over X.B.toPre →
    (∀ i, Formalism.IndefR.FWT.VStd X.toD7 i) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  intro K hK X hX
  obtain ⟨-, -, -, -, -, -, hVf, -⟩ := hK X hX
  obtain ⟨hR, -⟩ := GlobalTheory.Mem.HostFrames.val_of_over hX
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hVf i
    rw [GlobalTheory.StdFrameCounterexample.vstd_iff]
    refine ⟨Matrix.ext fun a b => ?_, fun x => ?_⟩
    · rw [HSpace.gram, h1, Matrix.one_apply]
    · rw [h2, Module.Basis.mem_span_iff_repr_mem, Module.Basis.repr_sum_self]
      refine forall_congr' fun a => ?_
      constructor
      · rintro ⟨y, hy⟩
        rw [← hy]; exact y.2
      · intro h
        exact ⟨⟨x a, h⟩, rfl⟩
  · have h4 := hR.2.2.2
    show 8 * X.B.R.f * X.B.R.r + 4 ≤ X.B.R.r + X.B.R.t
    omega

end GlobalTheory.Mem.StdSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLargeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_definiteSpaces_standard_and_large : Top.Ev fun K => ∀ X : Stages, K.Over X.B.toPre → (∀ i, Formalism.IndefR.FWT.VStd X.toD7 i) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  first | exact @GlobalTheory.Mem.StdSize.vstd_size_ev | exact GlobalTheory.Mem.StdSize.vstd_size_ev | (intros; apply GlobalTheory.Mem.StdSize.vstd_size_ev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacter
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompactAction

theorem trace_Jm {n p q : ℕ} (h : p + q = n) (ε : Fin n → Bool) (hε : ∀ a, ε a = decide ((a : ℕ) < p)) :
    (Formalism.REAL.Jm ε).trace = (p : ℂ) - q := by
  subst h
  unfold Formalism.REAL.Jm
  rw [Matrix.trace_diagonal, Fin.sum_univ_add]
  simp [hε, sub_eq_add_neg]

theorem isCartanInv_one {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have hu : IsUnit B := IsUnit.of_mul_eq_one _ hB
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hi, hB, Matrix.conjTranspose_one]
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G := by rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ← hi]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  exact (Matrix.isUnit_nonsing_inv_iff).2 hu

theorem conj_unitary {n : ℕ} {G B g : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have h0 : B * B⁻¹ = 1 := by rw [hi, hB]
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h0, Matrix.conjTranspose_one]
  have hG : (B⁻¹)ᴴ * B⁻¹ = G := by
    calc _ = (B⁻¹)ᴴ * (Bᴴ * G) := by rw [← hi]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = Bᴴ * (gᴴ * ((B⁻¹)ᴴ * B⁻¹) * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hG, hg, h]

theorem det_conj {n : ℕ} {F F' : Matrix (Fin n) (Fin n) ℂ} (h : F' * F = 1) (A C x : Matrix (Fin n) (Fin n) ℂ) :
    (A * (F * x * F') + C).det = (F' * A * F * x + F' * C * F).det := by
  have e : F' * A * F * x + F' * C * F = F' * (A * (F * x * F') + C) * F := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h, Matrix.mul_one]
  have hd : F'.det * F.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  rw [e, Matrix.det_mul, Matrix.det_mul]
  linear_combination (-(A * (F * x * F') + C).det) * hd

theorem pureTensorO_smul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (c : ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  have hd : ∀ τ z (f : WO S T → ℂ), dRho (heisO ψ S T) θ τ z (c • f) = c • dRho (heisO ψ S T) θ τ z f := by
    intro τ z f
    funext x
    simp only [Formalism.IndefR.Datum.dRho, heisO, Pi.smul_apply, smul_eq_mul]
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    ring
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) _ _ (c • (1 : Module.End ℂ (WO S T → ℂ))) (fun k f _ => ⟨trivial, ?_⟩) f trivial P).2.symm
  simp only [aPlusAll, Formalism.IndefR.Datum.aPlus, crea, LinearMap.smul_apply, Module.End.one_apply, hd]
  rw [smul_comm Complex.I c, ← smul_sub, smul_comm]

theorem om_pureTensorO_eq_fact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (p q : D.what₂.Tau → ℕ), (∀ τ, p τ + q τ = T.rank) → (∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℚ) = -(((p τ : ℚ) - q τ) / 2 + b τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ ∀ P : PolF D T.rank S.rank, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fact M.ε x₁ x₂ x₃ (fun τ => M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹) (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) P) := by
  intro D ψ θ S T χS χT om Sp M BS hom hθ hS hT hBS p q hpq hε a b ha hb x₁ x₂ x₃ h₁ h₂ h₃ f hf hv g hg h hh hk
  have hu : ∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ :=
    fun τ => conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S g τ)
  refine ⟨hu, fun P => ?_⟩
  have f1 : ∀ τ, M.fr τ * (M.fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have f2 : ∀ τ, (M.fr τ)⁻¹ * M.fr τ = 1 := fun τ => mul_eq_one_comm.1 (f1 τ)
  have b1 : ∀ τ, BS τ * (BS τ)⁻¹ = 1 := fun τ => by
    have hB : BS τ * ((BS τ)ᴴ * gramAt D S τ) = 1 := mul_eq_one_comm.1 (hBS τ)
    rw [Matrix.inv_eq_right_inv hB, hB]
  have hc : ∀ τ, cart M τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * cart M τ := fun τ => by
    have e := congrArg (fun X => (M.fr τ)⁻¹ * X * M.fr τ) (hk τ).2
    simp only [Matrix.mul_assoc, f2, Matrix.mul_one] at e
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), f2, Matrix.one_mul] at e
    unfold cart
    simp only [Matrix.mul_assoc]
    exact e.symm
  have htr : ∀ τ, (cart M τ).trace = (p τ : ℂ) - q τ := fun τ => by
    unfold cart
    rw [Matrix.trace_mul_cycle, f1, Matrix.one_mul, trace_Jm (hpq τ) _ (hε τ)]
  have hvac := GlobalTheory.T.vacuum_character_positive_definite_source D ψ θ S T χS χT om hom hθ hS hT (cart M) (fun τ => isCartanInv_one (hBS τ))
    (GlobalTheory.Chain.VacVec.cart_isCartanInv M) a b ha hb x₁ x₂ x₃ h₁ h₂ (fun τ => by
      rw [htr]
      have := congrArg (fun x : ℚ => (x : ℂ)) (h₃ τ)
      push_cast at this
      exact this) f hf hv g hg h hh hc
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ (fun _ => 1) (fun _ => 1) BS
    (fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ)) (cart M) (cart M) (onb M)
    (fun τ => onb M τ * (M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹)) g h
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) hc
    (fun τ => by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b1, Matrix.one_mul])
    (fun τ => by unfold onb; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, f2, Matrix.one_mul]) f hf P).2,
    GlobalTheory.T.fockPolynomialVector_change_orthonormalBases_subst D ψ θ S T Sp M BS hom.std hθ hBS _ _ hk hu _ (hom.om_pres _ _ hf), hvac, pureTensorO_smul]
  unfold fact
  rw [LinearMap.smul_apply, map_smul]
  congr 1
  unfold fchar
  refine Finset.prod_congr rfl fun τ _ => ?_
  have eP : (M.fr τ)⁻¹ * ((1 / 2 : ℂ) • (1 + Formalism.REAL.Jm (M.ε τ))) * M.fr τ = (1 / 2 : ℂ) • (1 + cart M τ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, f2]; rfl
  have eM : (M.fr τ)⁻¹ * ((1 / 2 : ℂ) • (1 - Formalism.REAL.Jm (M.ε τ))) * M.fr τ = (1 / 2 : ℂ) • (1 - cart M τ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, f2]; rfl
  have eU : ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ).det = (compAt θ τ (Formalism.L2.Theta.mt S g)).det := by
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, b1, Matrix.one_mul]
  unfold detP detM
  rw [det_conj (f2 τ), det_conj (f2 τ), eP, eM, eU]

end GlobalTheory.FockCompactAction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_maximalCompact_fock_substitution_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (p q : D.what₂.Tau → ℕ), (∀ τ, p τ + q τ = T.rank) → (∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℚ) = -(((p τ : ℚ) - q τ) / 2 + b τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ ∀ P : PolF D T.rank S.rank, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fact M.ε x₁ x₂ x₃ (fun τ => M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹) (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) P) := by
  first | exact @GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact | exact GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact | (intros; apply GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullAlgebraPartLeSplitHeckePart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullAlgebraPartLeSplitHeckePart
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.HeckeSplitPart

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem goodPl (R : RealDat D A Ks) (F : Face D A) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam)
    {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSF : IsSF R SF) {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ} (hβ : IsSDFrame V β Λ N)
    (hN : N = 1 ∨ N = D.host.g 0 * D.host.g 1) :
    GlobalTheory.HeckeParts.GoodPl V β R.Pg (A.ok A.μ0) R.pl A.q SF := by
  obtain ⟨hQ, h2, h3, h4⟩ := GlobalTheory.GoodPrimes.good_primes R F hL
  intro P hP
  obtain ⟨hg, hc, hq⟩ := h4 hF _ P hP
  refine ⟨?_, (h3 SF hSF _).2 hg, ?_, fun L hLP hLQ e f hef => ?_⟩
  · rw [hq, Nat.cast_ne_zero]
    exact fun h => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
    exact fun h => hc (HeightOneSpectrum.ext h)
  · obtain ⟨c, hcB⟩ := hβ
    refine (GlobalTheory.LevSplit.lev_split V β Λ _ L hcB).2 (R.pl P) e f hef ?_ ?_
    · intro h
      rw [Nat.cast_pow] at h
      have h' := (R.pl P).isPrime.mem_of_pow_mem _ h
      rcases hN with rfl | rfl
      · exact (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h'))
      · exact (h2 _ _ hg).1 h'
    · rw [hLP, hLQ]
      rintro PP (h | h)
      · exact hg PP (Or.inl h)
      · simp at h

theorem parts_in_hPart : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ (c : Pl D.host.E → List ℤ → ℂ) (Sg : Pl0 → ℂ[X]), ((∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) → ∀ x ∈ EEc R SF c, R.HE.e x ∈ hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q Sg) ∧ ∀ i, (∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (splitLab D.R.r k)) → ∀ x ∈ Wcc R SF i c, (R.HW i _).e x ∈ hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q Sg := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ hC SF hSF c Sg
  have hY := goodPl R F hC.lev hC.fam hSF (hC.lev.βY 0 (by have := D.R.two_le_m; omega)) (Or.inr rfl)
  have hW := fun i => goodPl R F hC.lev hC.fam hSF (hC.lev.βW i) (Or.inl rfl)
  refine ⟨fun hSg x hx => ?_, fun i hSg x hx => ?_⟩
  · exact GlobalTheory.HeckeParts.mem_hPart_of_partFull (V := Yc D 0) (β := R.βY 0) (r := D.R.r) (t := D.R.t) (hr := r_le_Y 0)
      (Pg := R.Pg) (χ := R.chi) (ξ := fun _ => 1) (c := fun P d => c P (dualLab d)) hY R.triv hx
      (fun P hP => by rw [hSg P hP, GlobalTheory.HeckeParts.rank_zeroth_component_eq])
  · exact GlobalTheory.HeckeParts.mem_hPart_of_partFull (V := Wc D i) (β := R.βW i) (r := D.R.r) (t := D.R.t) (hr := r_le_rank_Wc i)
      (Pg := R.Pg) (χ := fun _ _ => 1) (ξ := fun _ => 1) (c := c) (hW i) R.triv hx.2
      (fun P hP => by rw [hSg P hP, GlobalTheory.HeckeParts.rank_weight_component_eq])

end GlobalTheory.HeckeSplitPart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullAlgebraPartLeSplitHeckePartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_algebra_part_le_split_hecke_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ (c : Pl D.host.E → List ℤ → ℂ) (Sg : Pl0 → ℂ[X]), ((∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) → ∀ x ∈ EEc R SF c, R.HE.e x ∈ hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q Sg) ∧ ∀ i, (∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (splitLab D.R.r k)) → ∀ x ∈ Wcc R SF i c, (R.HW i _).e x ∈ hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q Sg := by
  first | exact @GlobalTheory.HeckeSplitPart.parts_in_hPart | exact GlobalTheory.HeckeSplitPart.parts_in_hPart | (intros; apply GlobalTheory.HeckeSplitPart.parts_in_hPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrtWLeHPart
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3


set_option maxHeartbeats 1000000 in
theorem prtW_le_hPart : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → ∀ i : Fin D.R.m, (Y.IL.prtW : ∀ i : Fin D.R.m, D.what₂.FT → Submodule ℂ (AmbT (R.MW i (sg0 D A3.A)))) i π ≤ (hPart (R.MW i (sg0 D A3.A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A3.A.ok A3.A.μ0) R.pl A3.A.q (RealDat.polW (A := A3.A) p.1.1)).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap := by
  intro _ _ _ hcusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hc hcar i
  obtain ⟨hC, -, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have ht : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).1
  have hSb : R.Sb = R.Pg := hP.char.allPl
  have hSF : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    classical
    intro v
    unfold SsetF
    rw [ht, hQ, hSb, Finset.union_empty, Finset.mem_image]
    refine exists_congr fun PP => and_congr_right fun _ => ?_
    rw [← underPl_asIdeal]
    exact ⟨fun h => by rw [h], fun h => HeightOneSpectrum.ext h⟩
  have hlab := GlobalTheory.T.heckePolynomials_of_carried_eigensystem R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hcusp D) hH.ok hP.char hH.aux.ex
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hcusp R.toRealDat)
    (GlobalTheory.AdjPart.adjoint_injective_on_part R ⟨hH.prim.posScal.1, fun i t p => hH.prim.posScal.2 i t p _⟩ hH.prim.thmB)
    p c hcar
  rw [Y.prtWE i π]
  refine Submodule.map_mono fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.typePart_le_eigensystemPart_principalLevel R.toRealDat F.lv2 hH.ok.ok2 hC _ hSF Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2
    _ ⟨0, Y.hm⟩ c hc i U hU
  exact (GlobalTheory.T.full_algebra_part_le_split_hecke_part R.toRealDat F.lv2 hH.ok.ok2 hC _ hSF c _).2 i (fun P hP => (hlab P hP).2) x hx

end GlobalTheory.Mem.R3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrtLeHPartOfCarries
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem isSF_ssetF_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2) :
    GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat A3.A.μ0) := by
  intro v
  have hQ := (GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev).1
  have hS : R.Sb = R.Pg := hW.allPl
  unfold SsetF
  rw [hQ, hS]
  simp only [Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  exact ⟨fun h => by rw [← h]; rfl, fun h => HeightOneSpectrum.ext h⟩


set_option maxHeartbeats 1000000 in
theorem prt_le_hPart_of_carries : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → (Y.Ish.prt : D.what₂.FT → Submodule ℂ (AmbT (R.MY 0))) π ≤ (hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A3.A.ok A3.A.μ0) R.pl A3.A.q (RealDat.polE (A := A3.A) p.1.1)).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := by
  intro _ _ _ hR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hE hc
  obtain ⟨hC, hSF, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hR R.toRealDat
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hSF' : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    rw [hμ]; exact isSF_ssetF_base R F hP.char hC
  have hinj := GlobalTheory.AdjPart.adjoint_injective_on_part R
    ⟨hH.prim.posScal.1, fun i t p => hH.prim.posScal.2 i t p _⟩ hH.prim.thmB
  have hlab := GlobalTheory.T.heckePolynomials_of_carried_eigensystem R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hR D) hH.ok hP.char hH.aux.ex hS hinj p c hc
  have hpart := (GlobalTheory.T.full_algebra_part_le_split_hecke_part R.toRealDat F.lv2 (s := 1) hH.ok.ok2 hC _ hSF' c (RealDat.polE (A := A3.A) p.1.1)).1
    fun P hP => (hlab P hP).1
  rw [Y.prtE π]
  refine Submodule.map_mono fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.rowTypePart_le_eigensystemPart R.toRealDat F.lv2 (s := 1) hC hS _ hSF' Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2
    _ _ c hE true U hU
  exact hpart x hx

end GlobalTheory.Mem.R3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharacters
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

theorem partsRec_of_eig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → (∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) → Xd.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e))) → ∃ (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PartsRec R.toRealDat F.lv2 Y.tupT Y.hm Y.PY Y.PW Y.eFT E labPi piOf Y.Ish.prt Y.IL.prtW := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd hP hH hHost hgen hLam
  have e1 := GlobalTheory.T.exists_sphericalEigensystem_firstLift_baseLevel hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost hgen
  have e2 := GlobalTheory.Mem.EigCarry.carries_of_hasEig hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e3 := GlobalTheory.Mem.R3.IsotPart.isot_le_part hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e4 := GlobalTheory.Mem.R3.prt_le_hPart_of_carries hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e5 := GlobalTheory.Mem.R3.prtW_le_hPart hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have hc : Formalism.L2.Col.PairComm (A3.fam3.F.R A3.fam3.F.μ0).op := (hH.ok.ok2.what₂ A3.fam3.F.μ0).comm
  classical

  have hE : ∀ π, HasEig R F Y π (eigOfType R F Y π) := fun π => hasEig_eigOfType (e1 π)
  have hK : ∀ π, ∃ p, R.Carries p (eigOfType R F Y π) := fun π => e2 π _ (hE π)
  let Pi : Type := Set.range (eigOfType R F Y)
  have hPi : ∀ c : Pi, ∃ p, R.Carries p c.1 := by
    rintro ⟨c, π, rfl⟩
    exact hK π
  let labP : Pi → A3.fam3.base3.Ix := fun c => (hPi c).choose
  let E : EigIdx D Xd :=
    { Pi := Pi
      fin := Set.fintypeRange _
      dec := Classical.decEq _
      cOf := fun π => ⟨eigOfType R F Y π, π, rfl⟩
      lam_const := by
        intro j hj π π' e h1 h2 hcc
        have hc' : eigOfType R F Y π = eigOfType R F Y π' := congrArg Subtype.val hcc
        obtain ⟨p, hp⟩ := hK π
        have hp' : R.Carries p (eigOfType R F Y π') := hc' ▸ hp
        have hj' : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have hk : k < D.R.m := by omega
        have a1 := hLam ⟨k, hk⟩ π p e h1 (e3 π _ p (hE π) hp ⟨k, hk⟩)
        have a2 := hLam ⟨k, hk⟩ π' p e h2 (e3 π' _ p (hE π') hp' ⟨k, hk⟩)
        exact a1.trans a2.symm }
  refine ⟨E, fun c => A3.fam3.toIx2 hc (labP c), Subtype.val, ?_⟩
  refine ⟨fun π => rfl, Subtype.val_injective, ?_, ?_⟩
  · intro π
    exact e4 π _ _ (hE π) (hPi _).choose_spec
  · intro i π
    have h5 := e5 π _ _ (hE π) (hPi (E.cOf π)).choose_spec i
    exact h5

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharactersStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partsRow_of_eigensystemIndex_goodCharacters : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → (∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) → Xd.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e))) → ∃ (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PartsRec R.toRealDat F.lv2 Y.tupT Y.hm Y.PY Y.PW Y.eFT E labPi piOf Y.Ish.prt Y.IL.prtW := by
  first | exact @GlobalTheory.Mem.R3.partsRec_of_eig | exact GlobalTheory.Mem.R3.partsRec_of_eig | (intros; apply GlobalTheory.Mem.R3.partsRec_of_eig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoRawMulLevelIwahoriReduction
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

open Formalism.UG Formalism.MainNotions

namespace GlobalTheory.Mem.ColAd.LevGrp

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem decoRaw_mul_levelIwahori_reduction (g z : GL (Fin n) (AfE F E)) (hz : z ∈ J0 hc n ST) :
    decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 (redG hc n ST SG ⟨z, hz⟩)⁻¹ := by
  have h := decoRaw_rawSm hc ST SG 1 (⟨z, hz⟩⁻¹ : J0 hc n ST) g
  rw [map_one, map_inv] at h
  have e : Formalism.UG.bc (iA F E) ((1 : URat hc n) : GL (Fin n) E) * g *
      (((⟨z, hz⟩⁻¹ : J0 hc n ST) : J0 hc n ST) : GL (Fin n) (AfE F E))⁻¹ = g * z := by
    simp
  rw [e] at h
  exact h

end Gen

section Top

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) [NeZero n]

end Top

end GlobalTheory.Mem.ColAd.LevGrp

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.ColAd.LevGrp

end GlobalTheory.Mem.Col2.TC
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco

open GlobalTheory.Mem.R3.RowAd

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem gram_X'_eq_one (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem ptE_mul (h k : Bridge.Gf X.toD7.sp.X') : ptE X (h * k) = ptE X h * ptE X k := by
  unfold ptE
  rw [Subgroup.coe_mul, map_mul, map_mul]
  rfl

theorem ptE_finHom (g : GA X.toD7 X.toD7.sp.X') :
    ptE X ⟨finHom X.toD7.sp.X' g, g, rfl⟩ = ColAd.finN X.toD7.sp.X' (rank_X' X) g := by
  apply Units.ext
  ext i j
  rw [ColAd.finN_apply]
  rfl

theorem ptE_mem_UAd (hI : I.Ok) (h : Bridge.Gf X.toD7.sp.X') :
    ptE X h ∈ Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) := by
  obtain ⟨g, hg⟩ := h.2
  have e : h = ⟨finHom X.toD7.sp.X' g, g, rfl⟩ := Subtype.ext hg.symm
  rw [e, ptE_finHom]
  exact ColAd.finN_mem (rank_X' X) (gram_X'_eq_one X I hI) g

end GlobalTheory.Mem.R3.RowDeco

noncomputable section
namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd
variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem decoAd_mul (hI : I.Ok) {U : Set I.ι} (t : TupU I U) (h q : Bridge.Gf X.toD7.sp.X')
    (hz : ptE X q ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅) :
    decoAd X I t (h * q) =
      ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
        ((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨ptE X q, hz⟩)⁻¹ :
          Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))) •
        decoAd X I t h := by
  have hh := ptE_mem_UAd X I hI h
  have hq := ptE_mem_UAd X I hI q
  unfold decoAd Formalism.L2.Col.decoOf
  rw [ptE_mul]
  split_ifs with h1 h2 h2
  · apply Subtype.ext
    rw [Formalism.L2.Col.DecoSet.smul_val]
    exact ColAd.LevGrp.decoRaw_mul_levelIwahori_reduction X.toD7.sp.cm (ptE X h) (ptE X q) hz
  · exact absurd (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm _ _ _ _ hh) h2
  · exact absurd (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm _ _ _ _ (mul_mem hh hq)) h1
  · exact absurd (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm _ _ _ _ (mul_mem hh hq)) h1

end GlobalTheory.Mem.R3.RowDeco

noncomputable section
namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd
variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem reindex_mem_St_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ} (e : Fin a ≃ Fin b)
    {x : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ Formalism.L2.DIV.St (1 : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    Units.map (Matrix.reindexAlgEquiv (E ⊗[F] Formalism.L2.Herm.Af F) (E ⊗[F] Formalism.L2.Herm.Af F) e).toMonoidHom x ∈ Formalism.L2.DIV.St (1 : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨Units.map (Matrix.reindexAlgEquiv (Formalism.L2.Herm.intAf F E) (Formalism.L2.Herm.intAf F E) e).toMonoidHom y, ?_⟩
  apply Units.ext
  ext i j
  simp [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL]
  rfl

end GlobalTheory.Mem.R3.RowDeco

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd
variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem unitaryFiniteAdelicPointAsMatrix_mem_flagIwahori (hI : I.Ok) {U : Set I.ι} (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U)
    (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q) :
    ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ := by
  refine ⟨⟨ptE_mem_UAd X I hI _, ?_⟩, ?_⟩
  · have hSt := Formalism.L2.DIV.parLev_St (RowAct.parLev_of_Q X.toD7.sp.X' L.βX (L.datXt t) q)
    have e : Formalism.L2.DIV.St L.βX = Formalism.L2.DIV.St 1 := by rw [hL.beta.2]
    rw [e] at hSt
    exact reindex_mem_St_one _ hSt
  · refine Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => ?_
    exact absurd hP (Finset.notMem_empty _)

end GlobalTheory.Mem.R3.RowDeco

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd

theorem redAt_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ} (e : Fin a ≃ Fin b)
    (β : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : β = 1)
    (x : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.St β)
    (hx' : Units.map (Matrix.reindexAlgEquiv (E ⊗[F] Formalism.L2.Herm.Af F) (E ⊗[F] Formalism.L2.Herm.Af F) e).toMonoidHom x ∈
      Formalism.L2.DIV.St (1 : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F))) (PP : Formalism.L2.DIV.Pl E) :
    Formalism.L2.DIV.redAt 1 PP ⟨_, hx'⟩ =
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP PP) (Formalism.L2.DIV.kP PP) e).toMonoidHom (Formalism.L2.DIV.redFn β PP x) := by
  subst hβ
  obtain ⟨y, rfl⟩ := hx
  have hy : Units.map (Matrix.reindexAlgEquiv (E ⊗[F] Formalism.L2.Herm.Af F) (E ⊗[F] Formalism.L2.Herm.Af F) e).toMonoidHom
      (Formalism.L2.DIV.frGL 1 y) =
      Formalism.L2.DIV.frGL 1 (Units.map (Matrix.reindexAlgEquiv (Formalism.L2.Herm.intAf F E) (Formalism.L2.Herm.intAf F E) e).toMonoidHom y) := by
    apply Units.ext
    ext i j
    simp [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL]
    rfl
  have hred : ∀ (z : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F)) (hz : z ∈ Formalism.L2.DIV.St 1)
      (y' : GL (Fin b) (Formalism.L2.Herm.intAf F E)) (hzy : Formalism.L2.DIV.frGL 1 y' = z),
      Formalism.L2.DIV.redAt 1 PP ⟨z, hz⟩ = Formalism.UG.bc (Formalism.L2.DIV.resS F PP) y' := by
    intro z hz y' hzy
    subst hzy
    exact congrArg (Formalism.UG.bc (Formalism.L2.DIV.resS F PP)) (Formalism.L2.DIV.pullFr_frGL 1 y')
  rw [hred _ hx' _ hy.symm, Formalism.L2.DIV.redFn_frGL]
  apply Units.ext
  ext i j
  rfl

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem redG_ptE {U : Set I.ι} (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U)
    (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
    (hz : ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
    (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :
    Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ w =
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))) :=
  redAt_reindex (finCongr (rank_X' X)) L.βX hL.beta.2 _
    (Formalism.L2.DIV.parLev_St (RowAct.parLev_of_Q X.toD7.sp.X' L.βX (L.datXt t) q)) (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz) w.1

end GlobalTheory.Mem.R3.RowDeco
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisation
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisation
noncomputable section

open CategoryTheory Polynomial Formalism.L2.NT

namespace GlobalTheory.GreenParam

open GlobalTheory.GLq GlobalTheory.GLq.LabelUnique Formalism.IrreducibleCountingLemmas.TYPES

variable {g : ℕ} [Fact g.Prime]

def datum (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) : LabelDatum g where
  teich := t
  teich_inj := ht
  gen := ζ
  gen_order d hd := (hζ d hd).1
  gen_norm d e hd he := (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)

theorem mem_rootsBar_of_aeval {P : (ZMod g)[X]} (hP : P ≠ 0) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : aeval x P = 0) : x ∈ Formalism.CyclotomicNorms.rootsBar P := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots (Polynomial.map_ne_zero hP), IsRoot, Polynomial.eval_map, ← aeval_def]
  exact hx

theorem isPrimeLab_iff (d : ℕ) (P : (ZMod g)[X]) :
    IsPrimeLab d P ↔ P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = d := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, ?_, h4⟩
    rintro rfl
    exact h3 (by simp)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, fun h0 => h3 ?_, h4⟩
    have hd : (X : (ZMod g)[X]) ∣ P := X_dvd_iff.2 h0
    exact (eq_of_monic_of_associated monic_X h1 (irreducible_X.associated_of_dvd h2 hd)).symm

theorem isPrimeLab_charpoly {d : ℕ} (y : Gn g d) (hy : Irreducible (y : Mt g d).charpoly) :
    IsPrimeLab d (y : Mt g d).charpoly := by
  refine ⟨Matrix.charpoly_monic _, hy, fun h0 => ?_, by simp [Matrix.charpoly_natDegree_eq_dim]⟩
  have hdet := Matrix.det_eq_sign_charpoly_coeff (y : Mt g d)
  rw [h0, mul_zero] at hdet
  exact (Matrix.isUnits_det_units y).ne_zero hdet

theorem exists_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {z : Formalism.CyclotomicNorms.Fbar g}
    (hz : z ^ (g ^ d - 1) = 1) : ∃ m : ℕ, L.gen d ^ m = z := by
  have h1 : 1 < g ^ d := Nat.one_lt_pow hd.ne' (Fact.out : g.Prime).one_lt
  haveI : NeZero (g ^ d - 1) := ⟨by omega⟩
  have hp : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := by
    rw [← L.gen_order d hd]; exact IsPrimitiveRoot.orderOf _
  obtain ⟨m, -, hm⟩ := hp.eq_pow_of_pow_eq_one hz
  exact ⟨m, hm⟩

theorem sum_thetaOf (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {P : (ZMod g)[X]} (hP : IsPrimeLab d P)
    {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ Formalism.CyclotomicNorms.rootsBar P) (m : ℕ) :
    ∑ i ∈ Finset.range d, thetaOf L d x ((L.gen d ^ m) ^ (g ^ i)) =
      ∑ i ∈ Finset.range d, L.teich x ^ (m * g ^ i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, pow_sub_one_eq_one hP hx, map_one]
  rw [← pow_mul, thetaOf_gen_pow L d hd x hw]

theorem hasCuspLabel_iff (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) {d : ℕ} (V : FDRep ℂ (GL (Fin d) (ZMod g)))
    (hV : IsCusp (fun x => V.character x)) (P : (ZMod g)[X]) :
    HasCuspLabel (convC t ht ζ hζ) V P ↔ IsCuspOf (datum t ht ζ hζ) P (fun x => V.character x) := by
  have hd : 0 < d := hV.1
  unfold HasCuspLabel
  simp only [Fintype.card_fin, ZMod.card]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hP : IsPrimeLab d P := (isPrimeLab_iff d P).2 ⟨h1, h2, h3, h4⟩
    refine ⟨hP, hV, fun x hx y hy z hz => ?_⟩
    have hy' := isPrimeLab_charpoly y hy
    obtain ⟨m, rfl⟩ := exists_gen_pow (datum t ht ζ hζ) hd (pow_sub_one_eq_one hy' hz)
    rw [sum_thetaOf _ hd hP hx]
    exact h5 x (aeval_eq_zero_of_mem h1.ne_zero hx) y hy _ (aeval_eq_zero_of_mem hy.ne_zero hz) m rfl
  · rintro ⟨hP, -, h5⟩
    obtain ⟨h1, h2, h3, h4⟩ := (isPrimeLab_iff d P).1 hP
    refine ⟨h1, h2, h3, h4, fun x hx y hy z hz m hm => ?_⟩
    have hx' := mem_rootsBar_of_aeval h1.ne_zero hx
    have h := h5 x hx' y hy z (mem_rootsBar_of_aeval hy.ne_zero hz)
    have hm' : (datum t ht ζ hζ).gen d ^ m = z := hm
    rw [← hm', sum_thetaOf _ hd hP hx'] at h
    exact h

theorem nonempty_iso_of_character {G : Type} [Group G] [Fintype G] (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : V.character = W.character) : Nonempty (V ≅ W) := by
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Fintype.card_pos.ne')
  have h1 := FDRep.char_orthonormal V W
  have h2 := FDRep.char_orthonormal V V
  rw [← h, h2, if_pos ⟨Iso.refl V⟩] at h1
  by_contra h3
  rw [if_neg h3] at h1
  exact one_ne_zero h1

theorem cuspParam_of_green : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g)
    (hζ : IsGenSys ζ), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam (ZMod g) (convC t ht ζ hζ) := by
  intro hG g _ t ht ζ hζ d hd
  obtain ⟨τ, hτ, -, hall⟩ := hG g (datum t ht ζ hζ) d hd
  have huniq := GlobalTheory.GLq.LabelUniqueAll.label_eq (datum t ht ζ hζ) d
  refine ⟨fun V hs hc => ?_, fun P h1 h2 h3 h4 => ?_, fun V W P hs hc hs' hc' hP hP' => ?_⟩
  · have hV := (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).2 hc
    obtain ⟨Q, hQ, hVQ⟩ := hall _ hV
    refine ⟨⟨Q, ?_, fun P hP => ?_⟩, ?_⟩
    · refine (hasCuspLabel_iff t ht ζ hζ V hV Q).2 ?_
      rw [hVQ]; exact (hτ Q hQ).1
    · refine huniq P Q _ ((hasCuspLabel_iff t ht ζ hζ V hV P).1 hP) ?_
      rw [hVQ]; exact (hτ Q hQ).1
    · have h1 : V.character 1 = τ Q 1 := congrFun hVQ 1
      rw [FDRep.char_one, (hτ Q hQ).2] at h1
      simp only [q, ZMod.card]
      exact_mod_cast h1
  · have hP : IsPrimeLab d P := (isPrimeLab_iff d P).2 ⟨h1, h2, h3, h4⟩
    have hc := (hτ P hP).1
    obtain ⟨V, hs, hVχ⟩ := hc.2.1.2.1
    have he : (fun x => V.character x) = τ P := funext hVχ
    have hV : IsCusp (fun x => V.character x) := he ▸ hc.2.1
    exact ⟨V, hs, (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).1 hV, (hasCuspLabel_iff t ht ζ hζ V hV P).2 (he ▸ hc)⟩
  · have hV := (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).2 hc
    have hW := (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d W hd hs').2 hc'
    obtain ⟨Q, hQ, hVQ⟩ := hall _ hV
    obtain ⟨Q', hQ', hWQ⟩ := hall _ hW
    have e1 : P = Q := huniq P Q _ ((hasCuspLabel_iff t ht ζ hζ V hV P).1 hP) (hVQ ▸ (hτ Q hQ).1)
    have e2 : P = Q' := huniq P Q' _ ((hasCuspLabel_iff t ht ζ hζ W hW P).1 hP') (hWQ ▸ (hτ Q' hQ').1)
    refine nonempty_iso_of_character V W ?_
    exact hVQ.trans ((e1.symm.trans e2) ▸ hWQ.symm)

end GlobalTheory.GreenParam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspParam_of_greenParametrisation : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam (ZMod g) (convC t ht ζ hζ) := by
  first | exact @GlobalTheory.GreenParam.cuspParam_of_green | exact GlobalTheory.GreenParam.cuspParam_of_green | (intros; apply GlobalTheory.GreenParam.cuspParam_of_green <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceHarishChandraInducedEqProductCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceHarishChandraInducedEqProductCharacters
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.HCChar

open Formalism.IrreducibleCountingLemmas.TYPES

theorem trace_hcRep_eq_hcL : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b →
    ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam)
      (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x := by
  intro g _ r s b lam _ x
  classical
  have h1 : LinearMap.trace ℂ (hcSpace (ZMod g) b lam) (hcRep (ZMod g) b lam x) =
      (Representation.coind (parab (ZMod g) b).subtype (PI.SerBridgeGLW.inflRep (ZMod g) b lam)).character x := rfl
  rw [h1, GlobalTheory.GoodTypeGeneric.character_coind_eq_ind]
  let d : Fin s → ℕ := fun c => Fintype.card {i // b i = c}
  let α : ∀ c, GlobalTheory.GLq.Gn g (d c) → ℂ := fun c y => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character y
  let j : ∀ c, Fin (d c) → Fin r := fun c t => ((Fintype.equivFin {i // b i = c}).symm t).1
  obtain ⟨σ, hσ1, -, hσ3, hσ4⟩ := GlobalTheory.TypeCharProduct.exists_enum b d α j
    (fun c => Subtype.val_injective.comp (Equiv.injective _))
    (fun c t => ((Fintype.equivFin {i // b i = c}).symm t).2)
    (fun i => ⟨Fintype.equivFin {k // b k = b i} ⟨i, rfl⟩, by simp [j]⟩)
    (List.finRange s) (List.pairwise_lt_finRange s)
  have hL : GlobalTheory.SerCmp.canonList b lam = (List.finRange s).map fun c => (⟨d c, α c⟩ : GlobalTheory.GLq.Pc g) := rfl
  rw [hL, ← GlobalTheory.TypeCharProduct.ind_eq_hcL _ ?_ r σ ⟨hσ1, fun i => hσ3 i (List.mem_finRange _)⟩
    (fun y => y ∈ parab (ZMod g) b)
    (fun y => if h : y ∈ parab (ZMod g) b then (PI.SerBridgeGLW.inflRep (ZMod g) b lam).character ⟨y, h⟩ else 0)
    ?_ ?_]
  · unfold GlobalTheory.BI.ind GlobalTheory.TypeCharProduct.ind
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold GlobalTheory.BI.ext0
    beta_reduce
    by_cases h : y⁻¹ * x * y ∈ parab (ZMod g) b
    · rw [dite_eq_left h, if_pos h]
    · rw [dite_eq_right h, if_neg h]
  · intro q hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
    intro y z
    exact FDRep.char_conj _ y z
  · intro y
    rw [(hσ4 _).1, GlobalTheory.HCInduction.parab_eq_blockTri]
    show Matrix.BlockTriangular _ _ ↔ _
    simp only [List.mem_finRange, true_implies]
    exact ⟨fun h i k hik => h hik, fun h i k hik => h i k hik⟩
  · intro y hy
    rw [dite_eq_left hy, (hσ4 _).2, ← Fin.prod_univ_def]
    show LinearMap.trace ℂ _ (PiTensorProduct.map fun c => (lam c).ρ (levi (ZMod g) b c ⟨y, hy⟩)) = _
    rw [PI.SerBridgeGLW.trace_piTensorMap]
    refine Finset.prod_congr rfl fun c _ => ?_
    have hu : (y : Matrix (Fin r) (Fin r) (ZMod g)).submatrix (j c) (j c) =
        ((glEquiv (ZMod g) (Fintype.equivFin {i // b i = c}) (levi (ZMod g) b c ⟨y, hy⟩) : GL _ (ZMod g)) :
          Matrix _ _ (ZMod g)) := by
      ext t t'
      simp [glEquiv, levi, blk, j, Matrix.reindexAlgEquiv]
    have hg : GlobalTheory.GLq.toG ((y : Matrix (Fin r) (Fin r) (ZMod g)).submatrix (j c) (j c)) =
        glEquiv (ZMod g) (Fintype.equivFin {i // b i = c}) (levi (ZMod g) b c ⟨y, hy⟩) := by
      apply Units.ext
      rw [GlobalTheory.TypeCharProduct.coe_toG (by rw [hu]; exact Units.isUnit _), hu]
    show _ = (transp (Fintype.equivFin {i // b i = c}) (lam c)).character _
    rw [hg]
    show _ = LinearMap.trace ℂ _ ((lam c).ρ ((glEquiv (ZMod g) (Fintype.equivFin {i // b i = c})).symm _))
    rw [MulEquiv.symm_apply_apply]

end GlobalTheory.HCChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceHarishChandraInducedEqProductCharactersStatement
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_harishChandra_induced_eq_product_characters : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x := by
  first | exact @GlobalTheory.HCChar.trace_hcRep_eq_hcL | exact GlobalTheory.HCChar.trace_hcRep_eq_hcL | (intros; apply GlobalTheory.HCChar.trace_hcRep_eq_hcL <;> assumption)
end
end
