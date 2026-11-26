module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSpace

open GlobalTheory.WeilVacMove

variable {D : D7} {S T : HSp D}

theorem stdL_full (E : Type) [Field E] [NumberField E] (r : ℕ) :
    (stdL E r).FG ∧ Submodule.span E (stdL E r : Set (Fin r → E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin r)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

theorem map_sub_eq_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {a b : A} (ha : φ a = 0) (hb : φ b = 0) :
    φ (a - b) = 0 := by rw [map_sub, ha, hb, sub_zero]

theorem map_nsmul_eq_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {a : A} (ha : φ a = 0) (N : ℕ) :
    φ (N • a) = 0 := by rw [map_nsmul, ha, smul_zero]

theorem isRealPt_sub {u v : WO S T} (hu : IsRealPt u) (hv : IsRealPt v) : IsRealPt (u - v) := by
  ext i j
  have h1 : finPart D (u i j) = 0 := congrFun (congrFun hu i) j
  have h2 : finPart D (v i j) = 0 := congrFun (congrFun hv i) j
  exact map_sub_eq_zero (finPart D) h1 h2

theorem isFinPt_nsmul {u : WO S T} (hu : IsFinPt u) (N : ℕ) : IsFinPt (N • u) := by
  ext i j
  have h1 : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  exact map_nsmul_eq_zero (infPart D) h1 N

theorem exists_fin_add_real (C : Ctx S T) (w : WO S T) : ∃ u v, IsFinPt u ∧ IsRealPt v ∧ w = u + v := by
  obtain ⟨R, -, -, -, h1, -, h2, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  exact ⟨_, _, h2 w, (h1 _).1, (sub_add_cancel _ _).symm⟩

theorem isTh_rho (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (w : WO S T) : C.IsTh (C.rho w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real C w
  have hfin {a : WO S T} (ha : IsFinPt a) {g : WO S T → ℂ} (hg : C.IsTh g) : C.IsTh (C.rho a g) := {
    quasi := heisO_quasi C.ψ S T a g hg.quasi
    level := by
      obtain ⟨U, hU, h1⟩ := hg.level
      refine ⟨U ⊓ GlobalTheory.FinTranslate.annSub C.ψ S T a, hU.inter (GlobalTheory.FinTranslate.isOpen_annSub C.std.1 ha), fun u hu h0 => ?_⟩
      have h2 : C.ψ (symplOH S T u a) = 1 ∧ C.ψ (symplOH S T a u) = 1 := hu.2
      conv_rhs => rw [← h1 u hu.1 h0]
      unfold Ctx.rho
      rw [heisO_heisO, heisO_heisO, h2.1, h2.2, add_comm]
    cont := by
      haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
      haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
      exact (C.std.1.1.comp (continuous_symplOH S T continuous_id continuous_const)).mul
        (hg.cont.comp (continuous_id.add continuous_const))
    smooth k L h1 h2 w := by
      have e : (fun t => heisO C.ψ S T a g (w + L t)) = fun t => C.ψ (symplOH S T w a) * g (w + a + L t) := by
        funext t
        rw [heisO, symplOH_add_left, (symplOH_fin_real S T a (L t) ha (h2 t)).2, add_zero, add_right_comm]
      rw [e]
      exact contDiff_const.mul (hg.smooth k L h1 h2 (w + a)) }
  have h := hfin hu (isTheta_heisO_real C.std hv hf)
  unfold Ctx.rho at h ⊢
  rwa [heisO_heisO, (symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one, one_smul] at h

theorem exists_level (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  obtain ⟨U, hU, h⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := h4 U hU
  exact ⟨N, hN, fun u hu => h _ (hNU u hu) (isFinPt_nsmul (h3 u hu).1 N)⟩

theorem eq_zero_of_real (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (h0 : ∀ w, IsRealPt w → f w = 0) :
    f = 0 := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have h7 := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.2
  obtain ⟨N, hN, hl⟩ := exists_level C hf
  funext w
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real C w
  obtain ⟨y, hy⟩ := h1 u hu
  obtain ⟨-, hy2⟩ := h3 _ hy
  obtain ⟨y', -, u', hu', e⟩ := hy2 N hN
  have hr := isRealPt_sub hv (h7 (y + y')).2.2.1
  have e1 : u + v = ratW T S (y + y')ᵀ + ((v - (ratW T S (y + y')ᵀ - finW S T (y + y'))) + N • u') := by
    rw [(h7 y).2.2.2 y', sub_eq_iff_eq_add.1 e]
    abel
  have e2 := congrFun (hl u' hu') (v - (ratW T S (y + y')ᵀ - finW S T (y + y')))
  rw [h0 _ hr] at e2
  unfold Ctx.rho heisO at e2
  rw [(symplOH_fin_real S T _ _ (isFinPt_nsmul (h3 u' hu').1 N) hr).2, AddChar.map_zero_eq_one, one_mul] at e2
  rw [e1, hf.quasi, e2, mul_zero, Pi.zero_apply]

theorem rho_finW (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
    (w : WO S T) (hw : IsRealPt w) : C.rho (finW S T y) f w =
      cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y)) := by
  obtain ⟨-, h2, -, -, -, -, -, h7⟩ := GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C
  obtain ⟨-, -, -, hadd, -, -, -, hfin, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  obtain ⟨a1, a2, a3, -⟩ := h7 y
  set z := ratW T S yᵀ - finW S T y with hz
  have hr : ratW T S yᵀ = finW S T y + z := by rw [hz]; abel
  have hp : C.realPt z = embR C.X y := by
    rw [← a1, hr, hadd, hfin _ a2, zero_add]
  have e1 : w + finW S T y = ratW T S yᵀ + (w - z) := by rw [hz]; abel
  have hzz : symplOH S T z z = 0 := by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.1, mul_zero]
  have e2 : -symplOH S T (ratW T S yᵀ) (w - z) = symplOH S T w z := by
    have e3 : symplOH S T z w = symplOH S T z (w - z) + symplOH S T z z := by
      rw [← symplOH_add_right, sub_add_cancel]
    rw [hr, symplOH_add_left, (symplOH_fin_real S T _ _ a2 (isRealPt_sub hw a3)).1, zero_add, symplOH_skew S T z w,
      e3, hzz, add_zero]
  unfold Ctx.rho heisO
  rw [(symplOH_fin_real S T _ _ a2 hw).2, AddChar.map_zero_eq_one, one_mul, e1, hf.quasi, e2, h2 w z hw a3, hp]

theorem exists_mt_eq (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) :
    ∃ m : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = m.map (incA D) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem isTh_actO (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T}
    (hγ' : γ' ∈ GQ T) : C.IsTh fun w => f (actO S T γ γ' w) := by
  have hs : ∀ w w', symplOH S T (actO S T γ γ' w) (actO S T γ γ' w') = symplOH S T w w' := fun w w' => by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.1]
  obtain ⟨R, -, -, -, -, -, -, -, -, hact⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  let A : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')
  have hA : Continuous (actO S T γ γ') := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨m, hm⟩ := exists_mt_eq S ((GQ S).inv_mem hγ)
    obtain ⟨m', hm'⟩ := exists_mt_eq T hγ'
    have e : actO S T γ γ' (ratW T S x) = ratW T S (m' * x * m) := by
      unfold actO ratW
      rw [hm, hm', Matrix.map_mul, Matrix.map_mul]
    rw [actO_add, ← hs, e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu ((hact γ γ' u).2.1 h0)) (actO S T γ γ' w)
    unfold heisO at e ⊢
    rw [← e, ← hs w u]
    exact congrArg (fun x => _ * f x) (actO_add γ γ' w u)
  · have := hf.smooth k (A.comp L) (hA.comp h1) (fun t => (hact γ γ' (L t)).1 (h2 t)) (actO S T γ γ' w)
    simp only [actO_add]
    exact this

theorem theta_space_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), C.IsTh 0 ∧ (∀ f f', C.IsTh f → C.IsTh f' → C.IsTh (f + f') ∧ ((∀ w, IsRealPt w → f w = f' w) → f = f')) ∧ ∀ f, C.IsTh f → (∀ a : ℂ, C.IsTh (a • f)) ∧ (∀ w, C.IsTh (C.rho w f)) ∧ (∀ w w', C.rho w (C.rho w' f) = C.ψ (symplOH S T w w') • C.rho (w + w') f) ∧ (∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) w, IsRealPt w → C.rho (finW S T y) f w = cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y))) ∧ (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, C.IsTh fun w => f (actO S T γ γ' w)) ∧ ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  intro D S T C
  have hz : C.IsTh 0 := {
    quasi γ w := by simp only [Pi.zero_apply, mul_zero]
    level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
    cont := continuous_const
    smooth k L _ _ w := contDiff_const }
  have ha {f g : WO S T → ℂ} (hf : C.IsTh f) (hg : C.IsTh g) : C.IsTh (f + g) := {
    quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
    cont := hf.cont.add hg.cont
    smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w) }
  have hs (c : ℂ) {f : WO S T → ℂ} (hf : C.IsTh f) : C.IsTh (c • f) := {
    quasi γ w := by rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    cont := hf.cont.const_smul c
    smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w) }
  refine ⟨hz, fun f f' hf hf' => ⟨ha hf hf', fun h => ?_⟩, fun f hf =>
    ⟨fun a => hs a hf, isTh_rho C hf, fun w w' => heisO_heisO _ _ _ _ _ _, rho_finW C hf,
      fun γ hγ γ' hγ' => isTh_actO C hf hγ hγ', exists_level C hf⟩⟩
  exact sub_eq_zero.1 (eq_zero_of_real C (isTheta_sub hf hf') fun w hw => sub_eq_zero.2 (h w hw))

end GlobalTheory.ThetaSpace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_space_heisenberg_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), C.IsTh 0 ∧ (∀ f f', C.IsTh f → C.IsTh f' → C.IsTh (f + f') ∧ ((∀ w, IsRealPt w → f w = f' w) → f = f')) ∧ ∀ f, C.IsTh f → (∀ a : ℂ, C.IsTh (a • f)) ∧ (∀ w, C.IsTh (C.rho w f)) ∧ (∀ w w', C.rho w (C.rho w' f) = C.ψ (symplOH S T w w') • C.rho (w + w') f) ∧ (∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) w, IsRealPt w → C.rho (finW S T y) f w = cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y))) ∧ (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, C.IsTh fun w => f (actO S T γ γ' w)) ∧ ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  first | exact @GlobalTheory.ThetaSpace.theta_space_laws | exact GlobalTheory.ThetaSpace.theta_space_laws | (intros; apply GlobalTheory.ThetaSpace.theta_space_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TensLatMove

variable {D : D7}

def emb (D : D7) : AfE D →ₗ[D.host.F] AE D :=
  TensorProduct.map (GlobalTheory.AdelicLatMove.finIncl D) LinearMap.id

theorem emb_tmul (e : D.host.E) (α : Af D.host.F) :
    emb D (α ⊗ₜ[D.host.F] e) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] e := rfl

theorem finPart_tmul (x : AF D.host.F) (e : D.host.E) :
    Formalism.L2.Theta.finPart D (x ⊗ₜ[D.host.F] e) = (sndA D.host.F x) ⊗ₜ[D.host.F] e := rfl

theorem emb_mul (a : AE D) (x : AfE D) : emb D (Formalism.L2.Theta.finPart D a * x) = a * emb D x := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add (f := _), add_mul, ha, hb]
  | tmul y e =>
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add (f := _), mul_add, ha, hb]
    | tmul α f =>
      rw [finPart_tmul, Algebra.TensorProduct.tmul_mul_tmul, emb_tmul, emb_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      exact Prod.ext (mul_zero y.1).symm rfl

def outer (S T : HSp D) (v : Fin S.rank → AfE D) (u : Fin T.rank → AfE D) : WO S T :=
  Matrix.of fun a k => emb D (u a * v k)

def outerHom (S T : HSp D) : (Fin S.rank → AfE D) →+ (Fin T.rank → AfE D) →+ WO S T :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun u => outer S T v u) (fun u u' => by
      ext i j
      simp only [outer, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul]))
    (fun v v' => AddMonoidHom.ext fun u => by
      ext i j
      simp only [outer, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Matrix.of_apply, Matrix.add_apply,
        Pi.add_apply, map_add, mul_add])

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) (hβ : β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) :
    α * β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem intAf_one : (1 : Af D.host.F) ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem outer_pure (S T : HSp D) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (α β : Af D.host.F) :
    outer S T (fun i => α ⊗ₜ[D.host.F] s i) (fun i => β ⊗ₜ[D.host.F] t i) =
      Matrix.of fun a k => (pairA D.host.F 0 (β * α)) ⊗ₜ[D.host.F] (vecMulVec s t k a) := by
  ext a k
  simp only [outer, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, emb_tmul, vecMulVec_apply, mul_comm (t a)]

theorem outer_mem (S T : HSp D) (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank)
    (v : Fin S.rank → AfE D) (hv : v ∈ hatV Λ) (u : Fin T.rank → AfE D) (hu : u ∈ hatV L) :
    outer S T v u ∈ hatA S T (tens Λ L) := by
  change outerHom S T v u ∈ _
  induction hv using AddSubgroup.closure_induction with
  | mem s hs =>
    induction hu using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      apply AddSubgroup.subset_closure
      exact ⟨β * α, intAf_mul hβ hα, vecMulVec x y, AddSubgroup.subset_closure ⟨x, hx, y, hy, rfl⟩,
        outer_pure S T x y α β⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem hatA_le (S T : HSp D) (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank) (K : AddSubgroup (WO S T))
    (hK : ∀ v ∈ hatV Λ, ∀ u ∈ hatV L, outer S T v u ∈ K) : hatA S T (tens Λ L) ≤ K := by
  rw [hatA, AddSubgroup.closure_le]
  rintro _ ⟨α, hα, y, hy, rfl⟩
  change _ ∈ K
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, hs, t, ht, rfl⟩ := hy
    have e := outer_pure S T s t 1 α
    rw [mul_one] at e
    rw [← e]
    exact hK _ (AddSubgroup.subset_closure ⟨1, intAf_one, s, hs, rfl⟩) _
      (AddSubgroup.subset_closure ⟨α, hα, t, ht, rfl⟩)
  | zero =>
    convert zero_mem K using 1
    ext a k
    simp
  | add y z _ _ hy hz =>
    convert add_mem hy hz using 1
    ext a k
    simp [TensorProduct.tmul_add]
  | neg y _ hy =>
    convert neg_mem hy using 1
    ext a k
    simp [TensorProduct.tmul_neg]

theorem actO_outer (S T : HSp D) (hS : S.gram = 1) (h : GA D S) (g : GA D T) (v : Fin S.rank → AfE D)
    (u : Fin T.rank → AfE D) :
    actO S T h g (outer S T v u) = outer S T (fmtC S h *ᵥ v) (fmt T g *ᵥ u) := by
  have key := GlobalTheory.AdelicLatMove.gram_mul_inv S h
  have h1 : S.gram.map (incA D) = 1 := by rw [hS, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h1, Matrix.one_mul, Matrix.mul_one] at key
  ext i j
  simp only [actO, key, outer, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← emb_mul, ← map_sum, mul_comm (emb D _)]
  congr 1
  simp only [fmt, fmtC, Formalism.L2.Theta.cM, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

def actHom (S T : HSp D) (h : GA D S) (g : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T h g) (fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul])

theorem mem_hatA_iff (S T : HSp D) (hS : S.gram = 1) (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank)
    (L L' : Lt D.host.E T.rank) (h1 : IsMov (fmtC S h) Λ Λ') (h2 : IsMov (fmt T g) L L') (u : WO S T) :
    u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀ := by
  constructor
  · intro hu
    have := hatA_le S T Λ' L' ((hatA S T (tens Λ L)).map (actHom S T h g)) (fun v hv w hw => by
      obtain ⟨v₀, hv₀, rfl⟩ := (h1 v).1 hv
      obtain ⟨w₀, hw₀, rfl⟩ := (h2 w).1 hw
      exact ⟨_, outer_mem S T Λ L v₀ hv₀ w₀ hw₀, actO_outer S T hS h g v₀ w₀⟩) hu
    obtain ⟨u₀, hu₀, e⟩ := this
    exact ⟨u₀, hu₀, e.symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    refine hatA_le S T Λ L ((hatA S T (tens Λ' L')).comap (actHom S T h g)) (fun v hv w hw => ?_) hu
    change actO S T h g _ ∈ hatA S T (tens Λ' L')
    rw [actO_outer S T hS]
    exact outer_mem S T Λ' L' _ ((h1 _).2 ⟨v, hv, rfl⟩) _ ((h2 _).2 ⟨w, hw, rfl⟩)

theorem hatA_move : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank) (L L' : Lt D.host.E T.rank), IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → (∀ u, u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀) ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ f, C.IsTh f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ' L')) (om (h, g) f) := by
  intro D S T C h g Λ Λ' L L' h1 h2
  have hΛ := mem_hatA_iff S T C.m.gS h g Λ Λ' L L' h1 h2
  refine ⟨hΛ, fun om hW f hth hlat => ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩⟩
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    rw [← GlobalTheory.WeilVacMove.actO_two_nsmul, ← hW.om_heis h g _ f hth, hlat.1 u₀ hu₀]
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    have h0 : IsHalf e u₀ := by
      have := GlobalTheory.WeilVacMove.isHalf_actO e h⁻¹ g⁻¹ hh
      rwa [GlobalTheory.WeilVacMove.actO_inv_actO] at this
    rw [← hW.om_heis h g _ f hth, hlat.2 e he u₀ hu₀ h0]

end GlobalTheory.TensLatMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedTensorLattice_lattice_vacuum_transport : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank) (L L' : Lt D.host.E T.rank), IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → (∀ u, u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀) ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ f, C.IsTh f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ' L')) (om (h, g) f) := by
  first | exact @GlobalTheory.TensLatMove.hatA_move | exact GlobalTheory.TensLatMove.hatA_move | (intros; apply GlobalTheory.TensLatMove.hatA_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectors
noncomputable section

namespace GlobalTheory.Ker.WeakMove

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hom : IsWeak ψ S T om) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {L L' : ℝ →+ WO S T} (hL : IsRealDir T S L) (hL' : IsRealDir T S L') (hLL : ∀ t, L' t = actO S T g h (L t))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := i1; have := i2; have := i3; have := i4; have := i5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable (ratL T S) := countable_of_Lindelof_of_discrete
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have hF : IsThetaFunO ψ S T (om (g, h) f) := hom.om_pres _ _ hf
  have hd : IsThetaFunO ψ S T (dLine ψ S T L f) := theta_dLine hθ hψ hL hf
  have hd' : IsThetaFunO ψ S T (dLine ψ S T L' (om (g, h) f)) := theta_dLine hθ hψ hL' hF
  have hδ : IsThetaFunO ψ S T (om (g, h) (dLine ψ S T L f) - dLine ψ S T L' (om (g, h) f)) :=
    theta_sub (hom.om_pres _ _ hd) hd'
  obtain ⟨C₁, hC₁⟩ := quotient_bound hθ hψ hL hf
  obtain ⟨C₂, hC₂⟩ := quotient_bound hθ hψ hL' hF
  have hν : (μ.restrict 𝓕) Set.univ = 1 := by rw [Measure.restrict_apply_univ]; exact h1
  have h0 : ∫⁻ w, ‖(om (g, h) (dLine ψ S T L f) - dLine ψ S T L' (om (g, h) f)) w‖ₑ ^ 2 ∂(μ.restrict 𝓕) = 0 := by
    refine lintegral_eq_zero_of_approx (μ.restrict 𝓕) hν _ C₁ C₂ fun t ht => ?_
    have hq : IsThetaFunO ψ S T ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)) :=
      theta_smul _ (theta_sub (theta_heisO_real hθ hψ (hL.2 t) hf) hf)
    have hom_q : om (g, h) ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)) =
        (t : ℂ)⁻¹ • (heisO ψ S T (L' t) (om (g, h) f) - om (g, h) f) := by
      rw [map_smul, map_sub, hom.om_heis g h (L t) f hf, ← hLL t]
    refine ⟨om (g, h) (dLine ψ S T L f - (t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)),
      dLine ψ S T L' (om (g, h) f) - om (g, h) ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)),
      dLine ψ S T L f - (t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f), ?_, ?_, ?_, ?_⟩
    · rw [map_sub]; abel
    · exact hom.om_unit μ 𝓕 hμ h𝓕 _ _ (theta_sub hd hq)
    · intro w
      rw [Pi.sub_apply, norm_sub_rev, ← Pi.sub_apply]
      exact hC₁ t ht w
    · intro w
      rw [hom_q, Pi.sub_apply, norm_sub_rev, ← Pi.sub_apply]
      exact hC₂ t ht w
  exact sub_eq_zero.mp
    (eq_zero_of_lintegral_eq_zero (ratL T S) μ 𝓕 h𝓕 _ hδ.cont (theta_norm_periodic hψ hδ) h0)

theorem om_dRho (hom : IsWeak ψ S T om) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) := by
  rw [dRho_eq_dLine, dRho_eq_dLine]
  exact GlobalTheory.Ker.WeakMove.om_dLine hom hψ hθ g h (isRealDir_lineAt hθ τ z) (isRealDir_lineAt hθ τ _)
    (fun t => lineAt_move hθ g h τ z t) hf

theorem sB_mvB (C : Ctx S T) (g : GA D T) (B : C.Bas) (τ : D.what₂.Tau) :
    C.sB (C.mvB g B) τ * compAt C.θ τ (mt T g) = compAt C.θ τ (mt T g) * C.sB B τ := by
  have h1 : compAt C.θ τ (mt T g) * compAt C.θ τ (mt T g⁻¹) = 1 := compAt_mt_mul_inv τ g
  have h2 : (compAt C.θ τ (mt T g))⁻¹ * compAt C.θ τ (mt T g) = 1 := by
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h1)
  simp only [Ctx.sB, Ctx.mvB, Matrix.mul_inv_rev, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem isFock_om (C : Ctx S T) (hom : IsWeak C.ψ S T om) (h : GA D S) (g : GA D T) {f : WO S T → ℂ} (hf : C.IsTh f)
    (B : C.Bas) (hB : C.IsFock B f) : C.IsFock (C.mvB g B) (om (h, g) f) := by
  intro τ z
  have hM : compAt C.θ τ (mt T g) * compAt C.θ τ (mt T g⁻¹) = 1 := compAt_mt_mul_inv τ g
  have hG : compAt C.θ τ (mt S h) * compAt C.θ τ (mt S h⁻¹) = 1 := compAt_mt_mul_inv τ h
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin T.rank) (Fin S.rank) ℂ, z = compAt C.θ τ (mt T g) * z₀ * compAt C.θ τ (mt S h⁻¹) := by
    refine ⟨compAt C.θ τ (mt T g⁻¹) * z * compAt C.θ τ (mt S h), ?_⟩
    simp only [Matrix.mul_assoc, hG, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hM, Matrix.one_mul]
  have key := hB τ z₀
  have hc : cplxO 1 (C.sB (C.mvB g B) τ) (compAt C.θ τ (mt T g) * z₀ * compAt C.θ τ (mt S h⁻¹)) =
      compAt C.θ τ (mt T g) * cplxO 1 (C.sB B τ) z₀ * compAt C.θ τ (mt S h⁻¹) :=
    cplxO_move hG (by rw [Matrix.one_mul, Matrix.mul_one]) (sB_mvB C g B τ) z₀
  unfold annih at key ⊢
  rw [hc, ← GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ z₀ hf,
    ← GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ _ hf, ← map_smul, ← map_add, key, map_zero]

theorem om_fvec (C : Ctx S T) (hom : IsWeak C.ψ S T om) (h : GA D S) (g : GA D T) {f : WO S T → ℂ} (hf : C.IsTh f)
    (B : C.Bas) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B))
      (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  unfold Ctx.fvec pureTensorO
  refine (pureTensorL_intertwine (IsThetaFunO C.ψ S T) theta_zero (fun a b ha hb => theta_add ha hb)
    (fun c a ha => theta_smul c ha) _ _ (om (h, g)) ?_ f hf Q).2
  intro k f' hf'
  have hG : compAt C.θ k.1 (mt S h) * compAt C.θ k.1 (mt S h⁻¹) = 1 := compAt_mt_mul_inv k.1 h
  have hu : unitMap (compAt C.θ k.1 (mt S h)) (C.mvB g B k.1) k.2.1 k.2.2 =
      compAt C.θ k.1 (mt T g) * unitMap 1 (B k.1) k.2.1 k.2.2 * compAt C.θ k.1 (mt S h⁻¹) := by
    have := unitMap_move (B := 1) (B' := B k.1) (H := compAt C.θ k.1 (mt T g)) hG k.2.1 k.2.2
    rwa [Matrix.mul_one] at this
  have hc : ∀ z, cplxO 1 (C.sB (C.mvB g B) k.1) (compAt C.θ k.1 (mt T g) * z * compAt C.θ k.1 (mt S h⁻¹)) =
      compAt C.θ k.1 (mt T g) * cplxO 1 (C.sB B k.1) z * compAt C.θ k.1 (mt S h⁻¹) := fun z =>
    cplxO_move hG (by rw [Matrix.one_mul, Matrix.mul_one]) (sB_mvB C g B k.1) z
  unfold aPlusAll aPlus crea
  beta_reduce
  refine ⟨?_, ?_⟩
  · exact theta_smul _ (theta_sub (theta_dRho C.inf C.std _ _ hf') (theta_smul _ (theta_dRho C.inf C.std _ _ hf')))
  · simp only [map_smul, map_sub]
    rw [GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g _ _ hf', GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g _ _ hf',
      hu]
    exact congrArg _ (congrArg _ (congrArg _
      (congrArg (fun z => Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ k.1 z (om (h, g) f')) (hc _).symm)))

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem om_move : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (h : GA D S) (g : GA D T) f, C.IsTh f → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), om (h, g) (dRho (heisO C.ψ S T) C.θ τ z f) = dRho (heisO C.ψ S T) C.θ τ (compAt C.θ τ (mt T g) * z * compAt C.θ τ (mt S h⁻¹)) (om (h, g) f)) ∧ ∀ B, C.IsB B → (C.IsFock B f → C.IsFock (C.mvB g B) (om (h, g) f)) ∧ ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B)) (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  intro D S T C om hom h g f hf
  exact ⟨fun τ z => GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ z hf,
    fun B _ => ⟨fun hB => isFock_om C hom h g hf B hB, fun Q => om_fvec C hom h g hf B Q⟩⟩

end

end GlobalTheory.Ker.WeakMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakWeilRep_carries_derivatives_vacua_fockVectors : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (h : GA D S) (g : GA D T) f, C.IsTh f → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), om (h, g) (dRho (heisO C.ψ S T) C.θ τ z f) = dRho (heisO C.ψ S T) C.θ τ (compAt C.θ τ (mt T g) * z * compAt C.θ τ (mt S h⁻¹)) (om (h, g) f)) ∧ ∀ B, C.IsB B → (C.IsFock B f → C.IsFock (C.mvB g B) (om (h, g) f)) ∧ ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B)) (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  first | exact @GlobalTheory.Ker.WeakMove.om_move | exact GlobalTheory.Ker.WeakMove.om_move | (intros; apply GlobalTheory.Ker.WeakMove.om_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HeisDeriv

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [hx, Matrix.mulVec_add, add_dotProduct]

theorem hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [hx, Matrix.mulVec_add, star_add, dotProduct_add]

theorem hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [hx, Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem hx_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x z (c • w) = conj c * hx X bas idx x z w := by
  simp only [hx, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_eq_mul, Complex.star_def]

theorem hx_rsmul_left (t : ℝ) (z w : Fin g → ℂ) :
    hx X bas idx x (t • z) w = t * hx X bas idx x z w := by
  rw [← Complex.coe_smul, hx_smul_left]

theorem hx_rsmul_right (t : ℝ) (z w : Fin g → ℂ) :
    hx X bas idx x z (t • w) = t * hx X bas idx x z w := by
  rw [← Complex.coe_smul, hx_smul_right, Complex.conj_ofReal]

theorem hasDerivAt_translate (hs : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w))
    (Φ : (Fin n → Fin g → ℂ) → ℂ) (hΦ : Differentiable ℝ Φ) (ζ u : Fin n → Fin g → ℂ) :
    HasDerivAt (fun t : ℝ => cexp (π * I * ((∑ k, hx X bas idx x (ζ k) ((t • u) k)).im : ℝ)) *
      (gaussR X bas idx x (ζ + t • u) * Φ (ζ + t • u)))
      (gaussR X bas idx x ζ * (-(π * ∑ k, hx X bas idx x (u k) (ζ k)) * Φ ζ + fderiv ℝ Φ ζ u)) 0 := by
  have hab : ∑ k, hx X bas idx x (ζ k) (u k) = conj (∑ k, hx X bas idx x (u k) (ζ k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hs (u k) (ζ k)
  have hph : ∀ t : ℝ, (((∑ k, hx X bas idx x (ζ k) ((t • u) k)).im : ℝ) : ℂ) =
      (t : ℂ) * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) := by
    intro t
    have h : ∑ k, hx X bas idx x (ζ k) ((t • u) k) = (t : ℂ) * ∑ k, hx X bas idx x (ζ k) (u k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, hx_rsmul_right]
    rw [h, Complex.im_ofReal_mul, Complex.ofReal_mul]
  have hq : ∀ t : ℝ, ∑ k, hx X bas idx x ((ζ + t • u) k) ((ζ + t • u) k) =
      ∑ k, hx X bas idx x (ζ k) (ζ k) +
        (t : ℂ) * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) +
        (t : ℂ) ^ 2 * ∑ k, hx X bas idx x (u k) (u k) := by
    intro t
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, hx_add_left, hx_add_right, hx_rsmul_left, hx_rsmul_right]
    ring
  have hT : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hE : HasDerivAt (fun t : ℝ => (Real.pi : ℂ) * I * ((t : ℂ) * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ)) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (ζ k) +
          (t : ℂ) * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) +
          (t : ℂ) ^ 2 * ∑ k, hx X bas idx x (u k) (u k)))
      ((Real.pi : ℂ) * I * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k))) 0 := by
    have h := ((hT.mul_const (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ)).const_mul ((Real.pi : ℂ) * I)).sub
      ((((hT.mul_const (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k))).const_add
        (∑ k, hx X bas idx x (ζ k) (ζ k))).add ((hT.pow 2).mul_const (∑ k, hx X bas idx x (u k) (u k)))).const_mul
          ((Real.pi : ℂ) / 2))
    exact h.congr_deriv (by simp)
  have hL : HasDerivAt (fun t : ℝ => ζ + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add ζ
  have hΦt : HasDerivAt (fun t : ℝ => Φ (ζ + t • u)) (fderiv ℝ Φ ζ u) 0 :=
    (hΦ ζ).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hL (by simp)
  have hF := hE.cexp.mul hΦt
  refine (hF.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · have key : (Real.pi : ℂ) * I * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) =
        -((Real.pi : ℂ) * ∑ k, hx X bas idx x (u k) (ζ k)) := by
      rw [hab]
      generalize ∑ k, hx X bas idx x (u k) (ζ k) = b
      have e1 : conj b = (b.re : ℂ) - (b.im : ℂ) * I := by apply Complex.ext <;> simp
      have e2 : b = (b.re : ℂ) + (b.im : ℂ) * I := (Complex.re_add_im b).symm
      rw [Complex.conj_im, e1]
      push_cast
      linear_combination ((Real.pi : ℂ) / 2) * e2
    rw [key]
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero, zero_smul, zero_sub,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    unfold GlobalTheory.Ker.gaussR
    ring
  · beta_reduce
    rw [hph t]
    unfold GlobalTheory.Ker.gaussR
    rw [hq t, ← mul_assoc, ← Complex.exp_add]
    congr 2

end Classical

variable {D : D7} {S T : HSp D}

theorem dRho_eq (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (G : WO S T → ℂ)
    (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ) (hΦ : Differentiable ℝ Φ)
    (hG : ∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ)
    (hu : u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))
    (w : WO S T) (hw : IsRealPt w) :
    Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ τ z G w =
      gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) *
        (-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w) +
          fderiv ℝ Φ (C.zOf (C.xB B) w) u) := by
  obtain ⟨R, -, -, -, hR1, hR2, -, -, hline, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hdom : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hs := (GlobalTheory.Dict.hx_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even (C.xB B) hdom).1
  have hE := (zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (C.xB B) hdom).2.1
  have hψ := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.1
  have hlin : ∀ (a : WR C.X S.rank) (t : ℝ) (b : WR C.X S.rank),
      zR C.X C.idx (C.xB B) (a + t • b) = zR C.X C.idx (C.xB B) a + t • zR C.X C.idx (C.xB B) b := by
    intro a t b
    have h := (zRLin C.X C.idx (C.xB B) (n := S.rank)).map_add a (t • b)
    rw [map_smul] at h
    exact h
  have hsm : ∀ (t : ℝ) (b : WR C.X S.rank),
      zR C.X C.idx (C.xB B) (t • b) = t • zR C.X C.idx (C.xB B) b := fun t b =>
    (zRLin C.X C.idx (C.xB B) (n := S.rank)).map_smul t b
  have hT := hasDerivAt_translate C.X C.bas C.idx (C.xB B) hs Φ hΦ (C.zOf (C.xB B) w) u
  unfold Formalism.IndefR.Datum.dRho heisO
  refine (hT.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).deriv
  beta_reduce
  have hw' : w + lineAt C.θ τ z t =
      R (C.realPt w + t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank)) := by
    rw [hline, map_add (f := _), hR2 w hw]
  have hz : C.zOf (C.xB B)
      (R (C.realPt w + t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) =
      C.zOf (C.xB B) w + t • u := by
    unfold Ctx.zOf
    rw [(hR1 _).2, hlin, hu]
  rw [hw', hG _ (hR1 _).1, hz, hline, hψ w _ hw (hR1 _).1, (hR1 _).2, ← hE, hsm, ← hu]
  rfl

end GlobalTheory.Ker.HeisDeriv

theorem GlobalTheory.Ker.annih_crea_coord : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℝ Φ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w)) → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ), u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) → ∀ w, IsRealPt w → annih (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u + I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)) ∧ crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (2 * ((-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k))) * Φ (C.zOf (C.xB B) w) + (1 / 2 : ℂ) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u - I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)))) := by
  intro D S T C B hB G Φ hΦ hG τ z u hu w hw
  have h1 := GlobalTheory.Ker.HeisDeriv.dRho_eq C B hB G Φ hΦ hG τ z u hu w hw
  have hJ : I • u = zR C.X C.idx (C.xB B)
      (Pi.single (C.m.e τ) (fun k a => conj ((cplxO 1 (C.sB B τ) z) a k)) : WR C.X S.rank) := by
    rw [hu]
    exact (((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.2.2.1 τ z).symm
  have h2 := GlobalTheory.Ker.HeisDeriv.dRho_eq C B hB G Φ hΦ hG τ (cplxO 1 (C.sB B τ) z) (I • u) hJ w hw
  simp only [Pi.smul_apply, GlobalTheory.Ker.HeisDeriv.hx_smul_left, ← Finset.mul_sum] at h2
  unfold Formalism.IndefR.Datum.annih Formalism.IndefR.Datum.crea
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  constructor
  · linear_combination (-(gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (Real.pi : ℂ) *
      (∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w))) * I_sq
  · linear_combination (gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (Real.pi : ℂ) *
      (∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w)) * I_sq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilation_creation_periodCoordinates : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℝ Φ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w)) → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ), u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) → ∀ w, IsRealPt w → annih (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u + I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)) ∧ crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (2 * ((-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k))) * Φ (C.zOf (C.xB B) w) + (1 / 2 : ℂ) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u - I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)))) := by
  first | exact @GlobalTheory.Ker.annih_crea_coord | exact GlobalTheory.Ker.annih_crea_coord | (intros; apply GlobalTheory.Ker.annih_crea_coord <;> assumption)
end
end
