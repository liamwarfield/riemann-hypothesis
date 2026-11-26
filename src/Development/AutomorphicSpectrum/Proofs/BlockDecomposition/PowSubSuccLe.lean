module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}

def secs {E : X.Modules} (S : Subobject E) (V : X.Opens) : Set Γ(E, V) :=
  Set.range (S.arrow.app V)

def Killed (J : X.IdealSheafData) {E : X.Modules} (S : Subobject E) : Prop :=
  ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U → ∀ x : Γ(E, U), a • x ∈ secs S U

variable [X.Over (Spec (.of A))]

def powSub (E : X.Modules) (n : ℕ) : Subobject E := Subobject.mk (idealPowι I E n)

def PropSupp (A : Type) [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules}
    (S : Subobject E) : Prop :=
  ∃ T : X.IdealSheafData, IsProper (T.subschemeι ≫ (X ↘ Spec (.of A))) ∧
    Scheme.Modules.SupportedIn (cokernel S.arrow) (T.support : Set X)

structure ClosedSys (E : X.Modules) (S : ℕ → Subobject E) : Prop where
  qcoh : ∀ e, (S e : X.Modules).IsQuasicoherent
  pow_le : ∀ e, powSub I E (e + 1) ≤ S e
  succ : ∀ e, S e = S (e + 1) ⊔ powSub I E (e + 1)

def Alg (E : X.Modules) (S : ℕ → Subobject E) : Prop :=
  ∃ B : Subobject E, (B : X.Modules).IsQuasicoherent ∧ PropSupp A B ∧
    ∀ e, B ⊔ powSub I E (e + 1) = S e

def Statement (J : X.IdealSheafData) : Prop :=
  ∀ (E : X.Modules), IsCoherent E → ∀ S : ℕ → Subobject E, ClosedSys I E S →
    (∀ e, Killed J (S e)) → PropSupp A (S 0) → Alg I E S

def restrictSys {E : X.Modules} (D : Subobject E) (S : ℕ → Subobject E) (c e : ℕ) :
    Subobject (D : X.Modules) :=
  (Subobject.pullback D.arrow).obj (S (e + c)) ⊔ powSub I (D : X.Modules) (e + 1)

lemma powSub_succ_le (E : X.Modules) (n : ℕ) : powSub I E (n + 1) ≤ powSub I E n :=
  Subobject.mk_le_mk_of_comm (idealPowSucc I E n) (idealPowSucc_ι I E n)

theorem closedSys_pow (E : X.Modules) [E.IsQuasicoherent] :
    ClosedSys I E (fun e => powSub I E (e + 1)) := by
  refine { qcoh := ?_, pow_le := fun _ => le_rfl, succ := ?_ }
  · intro e
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (idealPowι I E (e + 1))).symm inferInstance
  · intro e
    exact (sup_eq_right.2 (powSub_succ_le I E (e + 1))).symm

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.KUFactsU

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem iwGL_entries {n : ℕ} {x : GL (Fin n) L} (hx : x ∈ IwGL L n) (i j : Fin n) :
    (x : Matrix (Fin n) (Fin n) L) i j ∈ intL L := by
  have hk := (Subgroup.mem_iInf.1 hx) (Fin.last n)
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hk
  have hmem : (Pi.single j 1 : Fin n → L) ∈ latK L n (Fin.last n) := by
    intro l
    simp only [Fin.val_last, l.isLt, if_true]
    by_cases hl : l = j
    · subst hl
      simp
    · simp [Pi.single_apply, hl]
  have h2 : (Matrix.GeneralLinearGroup.toLin : GL (Fin n) L ≃* _).toMonoidHom x •
      (Pi.single j 1 : Fin n → L) ∈ latK L n (Fin.last n) := by
    rw [← hk]
    exact Set.smul_mem_smul_set hmem
  have h3 := h2 i
  simp only [Fin.val_last, i.isLt, if_true] at h3
  show (x : Matrix (Fin n) (Fin n) L) i j ∈ Valued.v.integer
  rw [Valuation.mem_integer_iff]
  convert h3 using 2
  simp [Units.smul_def, Matrix.GeneralLinearGroup.toLin, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem iwU_le_KU (σ : L →+* L) (n : ℕ) : IwU σ n ≤ KU σ n := by
  intro x hx
  have hx' : (x : GL (Fin n) L) ∈ IwGL L n := Subgroup.mem_subgroupOf.1 hx
  have hxi : ((x : GL (Fin n) L))⁻¹ ∈ IwGL L n := inv_mem hx'
  have hmem : x ∈ ((KU σ n : Subgroup (GU σ n)) : Set (GU σ n)) := by
    rw [GlobalTheory.LFun.IntPtsUnitary.coe_KU, Set.mem_preimage, GlobalTheory.LFun.IntPtsUnitary.coe_GLint]
    exact ⟨fun i j => iwGL_entries hx' i j, fun i j => iwGL_entries hxi i j⟩
  exact hmem

theorem ordL_zpow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (d : ℤ) : ordL (ϖ ^ d) = d := by
  have h1 : Valued.v (ϖ ^ d) =
      ((Multiplicative.ofAdd (-d) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_zpow₀, hϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_neg, smul_eq_mul, mul_one]
  have hne : Valued.v (ϖ ^ d) ≠ 0 := by
    rw [h1]
    exact WithZero.coe_ne_zero
  unfold ordL
  rw [dite_eq_right hne]
  have key : WithZero.unzero hne = Multiplicative.ofAdd (-d) :=
    WithZero.coe_injective (by rw [WithZero.coe_unzero, h1])
  rw [key, toAdd_ofAdd, neg_neg]

def expo (n : ℕ) (i : Fin n) : ℤ := (n : ℤ) - 1 - 2 * (i.val : ℤ)

def tGL {ϖ : L} (h0 : ϖ ≠ 0) (n : ℕ) : GL (Fin n) L where
  val := Matrix.diagonal fun i => ϖ ^ expo n i
  inv := Matrix.diagonal fun i => ϖ ^ (-expo n i)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← zpow_add₀ h0]; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← zpow_add₀ h0]; simp

theorem tGL_mem {ϖ : L} (h0 : ϖ ≠ 0) {σ : L →+* L} (hσ : σ ϖ = ϖ) (n : ℕ) : tGL h0 n ∈ GU σ n := by
  show cT σ ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n *
    ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antiJ L n
  have hc : cT σ ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun i => ϖ ^ expo n i := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [cT, tGL, map_zpow₀, hσ]
    · simp [cT, tGL, hab, Ne.symm hab]
  rw [hc]
  ext a b
  simp only [tGL, Matrix.diagonal_mul, Matrix.mul_diagonal, antiJ]
  split_ifs with hab
  · have he : expo n a + expo n b = 0 := by
      unfold expo
      omega
    rw [mul_one, ← zpow_add₀ h0, he, zpow_zero]
  · simp

theorem exists_strictDom {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ t : GU σ n, IsDiagM (t : GL (Fin n) L) ∧ IsStrictDom (t : GL (Fin n) L) := by
  obtain ⟨-, -, hσ, hϖ, -⟩ := h
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨⟨tGL h0 n, tGL_mem h0 hσ n⟩, fun i j hij => ?_, fun i j hij => ?_⟩
  · show (Matrix.diagonal fun i => ϖ ^ expo n i) i j = 0
    exact Matrix.diagonal_apply_ne _ hij
  · show ordL ((Matrix.diagonal fun i => ϖ ^ expo n i) j j) <
      ordL ((Matrix.diagonal fun i => ϖ ^ expo n i) i i)
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ordL_zpow hϖ, ordL_zpow hϖ]
    unfold expo
    have hlt : (i : ℕ) < j := hij
    omega

theorem kuFacts : PositivityTheory.SphericalProduct.KUFacts := by
  intro L _ _ _ ϖ σ q n h
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h
  exact ⟨ho, hc, iwU_le_KU σ n, exists_strictDom h n⟩

end GlobalTheory.CompanionTheory.KUFactsU

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

section U

variable {L : Type} [Field L] {σ : L →+* L} {n : ℕ}

def IsPermW (w : GU σ n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ a c : Fin n, ((w : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a c = if c = π a then 1 else 0

variable [Valued L (WithZero (Multiplicative ℤ))]

def permWt (t : GU σ n) (π : Equiv.Perm (Fin n)) : ℤ :=
  ∑ a : Fin n, ((a.val : ℤ) + 1) * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a))

end U

def aOp {G : Type} [Group G] (R : Finset G) (t : G) (φ : G → ℂ) : G → ℂ :=
  fun g => ∑ r ∈ R, φ (g * r * t)

end GlobalTheory.CompanionTheory.SatPow

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyEqOfAgreeGLs
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

section Local

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eventuallyEq_of_agree_GLs {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) {x : Mat n}
    (hx : x ∈ GLs n) : F =ᶠ[nhds x] F' := by
  have ho : IsOpen (GLs n) := by
    have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
    exact isOpen_ne.preimage this
  exact Filter.eventuallyEq_of_mem (ho.mem_nhds hx) h

theorem Rd_agree_GLs (X : Mat n) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, Rd X F x = Rd X F' x := by
  intro x hx
  simp only [Rd, (eventuallyEq_of_agree_GLs h hx).fderiv_eq]

theorem Eu_agree_GLs (s : Bool) (a b : Fin n) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, Eu s a b F x = Eu s a b F' x := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_agree_GLs _ h x hx]

theorem Epow_agree_GLs (s : Bool) (m : ℕ) (a b : Fin n) {F F' : Mat n → V}
    (h : ∀ g ∈ GLs n, F g = F' g) : ∀ x ∈ GLs n, Epow s m a b F x = Epow s m a b F' x := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    by_cases hab : a = b
    · simpa [Epow, hab] using h x hx
    · simp [Epow, hab]
  | succ m ih =>
    intro x hx
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => Eu_agree_GLs s a c (ih c b) x hx

theorem gel_agree_GLs (s : Bool) (m : ℕ) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, gel s m F x = gel s m F' x := by
  intro x hx
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => Epow_agree_GLs s m a a h x hx

end Local

theorem zOp_agree_GLs : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Bool × ℕ)) (F F' : Mat n → V), (∀ g ∈ GLs n, F g = F' g) →
    ∀ x ∈ GLs n, zOp w F x = zOp w F' x := by
  intro n V _ _ w
  induction w with
  | nil => exact fun F F' h x hx => h x hx
  | cons p w ih => exact fun F F' h => gel_agree_GLs p.1 p.2 (ih F F' h)

end GlobalTheory.CompanionTheory.WaveMult
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmooth
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL.Smooth

theorem isOpen_GLs' (n : ℕ) : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

theorem continuous_cm' (n : ℕ) : Continuous (cm (n := n)) := by
  unfold cm
  exact continuous_finsetSum _ fun p _ => (continuous_apply p).smul continuous_const

theorem cm_zero' (n : ℕ) : cm (n := n) 0 = 0 := by
  simp [cm]

def mulRight' {n : ℕ} (X : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

theorem contDiffOn_fderiv_apply' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {A : E → E} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply hA

theorem Rw_contDiffOn' {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Idx n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    exact contDiffOn_fderiv_apply' (isOpen_GLs' n) ih (mulRight' (bs p)).contDiff.contDiffOn

theorem Dw_contDiffOn' {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) :
    ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  induction L with
  | nil => exact hf
  | cons p L ih =>
    exact contDiffOn_fderiv_apply' (isOpen_GLs' n) ih contDiffOn_const

theorem smooth_all : ∀ n : ℕ, IsOpen (GLs n) ∧ Continuous (cm (n := n)) ∧ cm (n := n) 0 = 0 ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
      (∀ w, ContDiffOn ℝ ∞ (Rw w f) (GLs n)) ∧ ∀ L : List (Idx n), ContDiffOn ℝ ∞ (Dw L f) (GLs n) :=
  fun n => ⟨isOpen_GLs' n, continuous_cm' n, cm_zero' n, fun _ _ _ _ hf =>
    ⟨Rw_contDiffOn' hf, Dw_contDiffOn' hf⟩⟩

end GlobalTheory.CompanionTheory.SobGL.Smooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmoothStatement
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_and_right_words_smooth : ∀ n : ℕ, IsOpen (GLs n) ∧ Continuous (cm (n := n)) ∧ cm (n := n) 0 = 0 ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
      (∀ w, ContDiffOn ℝ ∞ (Rw w f) (GLs n)) ∧ ∀ L : List (Idx n), ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.Smooth.smooth_all | exact GlobalTheory.CompanionTheory.SobGL.Smooth.smooth_all | (intros; apply GlobalTheory.CompanionTheory.SobGL.Smooth.smooth_all <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RdSkewEqConst
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianUnitaryFlow
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianUnitaryFlow
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

namespace GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve

section RingNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_exp_smul {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp (t • Y)) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y t).continuousAt

theorem hasDerivAt_exp_smul_zero {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Y)) Y 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

end RingNorm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exp_smul_mem_unitaryGroup {n : ℕ} (Y : Mat n) (hY : Yᴴ = -Y) (t : ℝ) :
    NormedSpace.exp (t • Y) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hc : (t • Y)ᴴ = -(t • Y) := by
    rw [conjTranspose_smul, hY]; simp
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Y)).neg_right]
  simp

theorem exists_unitary_curve : ∀ {n : ℕ} (Y : Mat n), Yᴴ = -Y →
    ∃ c : ℝ → Matrix.unitaryGroup (Fin n) ℂ, Continuous c ∧ c 0 = 1 ∧
      (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => (c t).1) Y 0 := by
  intro n Y hY
  refine ⟨fun t => ⟨NormedSpace.exp (t • Y), exp_smul_mem_unitaryGroup Y hY t⟩,
    (continuous_exp_smul Y).subtype_mk _, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp
  · intro s t
    apply Subtype.ext
    show NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y)
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _
      (((Commute.refl Y).smul_left s).smul_right t)
  · exact hasDerivAt_exp_smul_zero Y

end GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianUnitaryFlowStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_unitary_flow : ∀ {n : ℕ} (Y : Mat n), Yᴴ = -Y → ∃ c : ℝ → Matrix.unitaryGroup (Fin n) ℂ, Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => (c t).1) Y 0 := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve | exact GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOneParamDifferentiable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOneParamDifferentiable
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.OneParam

theorem hasDerivAt_zero_of_continuous_oneParam
    {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (Φ : ℝ → 𝔸)
    (hc : Continuous Φ) (h0 : Φ 0 = 1) (hadd : ∀ s t, Φ (s + t) = Φ s * Φ t) :
    ∃ B, HasDerivAt Φ B 0 := by

  set F : ℝ → 𝔸 := fun x => ∫ s in (0 : ℝ)..x, Φ s with hF
  have hFd : ∀ x, HasDerivAt F (Φ x) x := fun x =>
    (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hF0 : F 0 = 0 := by simp [hF]

  have hsl : Filter.Tendsto (slope F 0) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (1 : 𝔸)) := by
    have := hasDerivAt_iff_tendsto_slope.1 (hFd 0)
    rwa [h0] at this
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, ‖slope F 0 ε - 1‖ < 1 := by
    have := hsl.eventually (Metric.ball_mem_nhds (1 : 𝔸) one_pos)
    filter_upwards [this] with ε hε
    simpa [dist_eq_norm] using hε
  obtain ⟨ε, hε, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hε0' : ε ≠ 0 := hε0

  set u : 𝔸 := slope F 0 ε with hu
  have huF : u = ε⁻¹ • F ε := by
    simp [hu, slope_def_module, hF0]
  have hone : ‖1 - u‖ < 1 := by rwa [norm_sub_rev]
  have huU : IsUnit u := by
    have := (Units.oneSub (1 - u) hone).isUnit
    simpa using this
  obtain ⟨U, hU⟩ := huU
  set v : 𝔸 := ((U⁻¹ : 𝔸ˣ) : 𝔸) with hv
  have huv : u * v = 1 := by rw [← hU, hv]; exact U.mul_inv

  have hmul : ∀ t, Φ t * F ε = F (t + ε) - F t := by
    intro t
    have h1 : Φ t * F ε = ∫ s in (0 : ℝ)..ε, Φ (t + s) := by
      have := (ContinuousLinearMap.mul ℝ 𝔸 (Φ t)).intervalIntegral_comp_comm
        (hc.intervalIntegrable (μ := volume) 0 ε)
      simp only [ContinuousLinearMap.mul_apply'] at this
      rw [hF]
      simp only [hadd]
      exact this.symm
    have h2 : (∫ s in (0 : ℝ)..ε, Φ (t + s)) = ∫ s in (t + 0)..(t + ε), Φ s :=
      intervalIntegral.integral_comp_add_left (a := 0) (b := ε) Φ t
    rw [h1, h2, add_zero]
    exact (intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable 0 _) (hc.intervalIntegrable 0 _)).symm

  have hrec : ∀ t, Φ t = (ε⁻¹ • (F (t + ε) - F t)) * v := by
    intro t
    rw [← hmul, ← mul_smul_comm, ← huF, mul_assoc, huv, mul_one]

  have hshift : HasDerivAt (fun t => F (t + ε)) (Φ (0 + ε)) 0 :=
    (hFd (0 + ε)).comp_add_const 0 ε
  have hd : HasDerivAt (fun t => (ε⁻¹ • (F (t + ε) - F t)) * v)
      ((ε⁻¹ • (Φ (0 + ε) - Φ 0)) * v) 0 :=
    ((hshift.sub (hFd 0)).const_smul ε⁻¹).mul_const v
  have hfun : Φ = fun t => (ε⁻¹ • (F (t + ε) - F t)) * v := funext hrec
  exact ⟨(ε⁻¹ • (Φ (0 + ε) - Φ 0)) * v, by rw [show HasDerivAt Φ = HasDerivAt (fun t => (ε⁻¹ • (F (t + ε) - F t)) * v) from congrArg _ hfun]; exact hd⟩

end GlobalTheory.CompanionTheory.OneParam
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOneParamDifferentiableStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_one_param_differentiable : ∀ {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (Φ : ℝ → 𝔸), Continuous Φ → Φ 0 = 1 → (∀ s t, Φ (s + t) = Φ s * Φ t) → ∃ B, HasDerivAt Φ B 0 := by
  first | exact @GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam | exact GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam | (intros; apply GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam <;> assumption)
end
end

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem rd_skew_eq_const {n : ℕ} (E : KMod n) (Y : Mat n) (hY : Yᴴ = -Y) :
    ∃ B : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g) := by
  obtain ⟨c, hc, c0, cadd, cd⟩ := GlobalTheory.T.skew_hermitian_unitary_flow Y hY
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← cadd, add_neg_cancel, c0])
  let Φ : ℝ → (E.V →L[ℂ] E.V) := fun t => E.ρ (c (-t))
  have hΦc : Continuous Φ := E.cont.comp (hc.comp continuous_neg)
  have hΦ0 : Φ 0 = 1 := by simp only [Φ, neg_zero, c0, map_one]
  have hΦa : ∀ s t, Φ (s + t) = Φ s * Φ t := fun s t => by
    simp only [Φ, neg_add, cadd, map_mul]
  obtain ⟨B, hB⟩ := GlobalTheory.T.continuous_one_param_differentiable Φ hΦc hΦ0 hΦa
  refine ⟨B, fun f hf g hg => ?_⟩
  have hk : ∀ t, f (g * (c t).1) = Φ t (f g) := fun t => by
    rw [hf.2 g hg (c t), hinv]
  have h1 : HasDerivAt (fun t => Φ t (f g)) (B (f g)) 0 :=
    ((ContinuousLinearMap.apply ℂ E.V (f g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hB
  let L : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ g)
  have h2 : HasDerivAt (fun t => g * (c t).1) (g * Y) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 cd
  have hd : DifferentiableAt ℝ f g :=
    (hf.1.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by simp)
  have h3 : HasFDerivAt f (fderiv ℝ f g) (g * (c 0).1) := by
    simpa [c0] using hd.hasFDerivAt
  have h4 : HasDerivAt (fun t => f (g * (c t).1)) (fderiv ℝ f g (g * Y)) 0 :=
    h3.comp_hasDerivAt 0 h2
  have h5 : (fun t => f (g * (c t).1)) = fun t => Φ t (f g) := funext hk
  rw [h5] at h4
  exact h4.unique h1

end GlobalTheory.CompanionTheory.WaveSpd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevel
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL

def lgArg {n : ℕ} (p : Mat n × Mat n) : ℝ :=
  1 + ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)

theorem lgArg_continuous {n : ℕ} : Continuous (lgArg (n := n)) := by
  unfold lgArg
  refine continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_)
  have h1 : Continuous fun p : Mat n × Mat n => p.1 a b :=
    (continuous_id.matrix_elem a b).comp continuous_fst
  have h2 : Continuous fun p : Mat n × Mat n => p.2 a b :=
    (continuous_id.matrix_elem a b).comp continuous_snd
  exact (h1.norm.pow 2).add (h2.norm.pow 2)

theorem one_le_lgArg {n : ℕ} (p : Mat n × Mat n) : 1 ≤ lgArg p := by
  unfold lgArg
  have : 0 ≤ ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  linarith

theorem entry_sq_le_lgArg {n : ℕ} (p : Mat n × Mat n) (a b : Fin n) :
    ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ lgArg p := by
  unfold lgArg
  have h1 : ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.single_le_sum (f := fun b => ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)
      (fun b _ => by positivity) (Finset.mem_univ b)
  have h2 : ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.single_le_sum (f := fun a => ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2))
      (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a)
  linarith

theorem lg_eq_log_lgArg {n : ℕ} (y : Mat n) : lg y = Real.log (lgArg (y, y⁻¹)) := rfl

theorem continuousOn_matInv {n : ℕ} : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have hdet : ContinuousOn (fun y : Mat n => (y.det)⁻¹) (GLs n) :=
    (continuous_id.matrix_det).continuousOn.inv₀ fun y hy => hy
  have hadj : Continuous fun y : Mat n => y.adjugate := continuous_id.matrix_adjugate
  have : (fun y : Mat n => y⁻¹) = fun y => (y.det)⁻¹ • y.adjugate := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact hdet.smul hadj.continuousOn

theorem continuousOn_lg {n : ℕ} : ContinuousOn (lg (n := n)) (GLs n) := by
  have hp : ContinuousOn (fun y : Mat n => (y, y⁻¹)) (GLs n) :=
    continuousOn_id.prodMk continuousOn_matInv
  have h := lgArg_continuous.comp_continuousOn hp
  exact ContinuousOn.log h fun y _ => (lt_of_lt_of_le one_pos (one_le_lgArg (y, y⁻¹))).ne'

def pairOf {n : ℕ} (y : G n) : Mat n × Mat n := (y.val, (y⁻¹ : G n).val)

theorem pairOf_isInducing {n : ℕ} : Topology.IsInducing (pairOf (n := n)) := by
  have h := (Units.isEmbedding_embedProduct (M := Mat n)).isInducing
  have h2 : Topology.IsInducing (fun p : Mat n × (Mat n)ᵐᵒᵖ => (p.1, p.2.unop)) :=
    ((Homeomorph.refl (Mat n)).prodCongr MulOpposite.opHomeomorph.symm).isInducing
  exact h2.comp h

theorem isCompact_entryBox {n : ℕ} (r : ℝ) : IsCompact {m : Mat n | ∀ a b, ‖m a b‖ ≤ r} := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) r) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {m : Fin n → Fin n → ℂ | ∀ a b, ‖m a b‖ ≤ r} = Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) r := by
    ext m
    simp [Set.mem_pi]
  have h' : IsCompact {m : Fin n → Fin n → ℂ | ∀ a b, ‖m a b‖ ≤ r} := e ▸ h
  exact h'

theorem isCompact_lg_le {n : ℕ} (R : ℝ) : IsCompact {y : G n | lg y.val ≤ R} := by
  rw [pairOf_isInducing.isCompact_iff]
  have hset : pairOf '' {y : G n | lg y.val ≤ R} =
      {p : Mat n × Mat n | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 ∧ lgArg p ≤ Real.exp R} := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨by simp [pairOf], by simp [pairOf], ?_⟩
      have hinv : (y⁻¹ : G n).val = y.val⁻¹ := Matrix.coe_units_inv y
      have hy' : Real.log (lgArg (pairOf y)) ≤ R := by
        have : lg y.val = Real.log (lgArg (pairOf y)) := by
          rw [lg_eq_log_lgArg, pairOf, hinv]
        rw [← this]; exact hy
      have hpos : 0 < lgArg (pairOf y) := lt_of_lt_of_le one_pos (one_le_lgArg _)
      exact (Real.log_le_iff_le_exp hpos).1 hy'
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨p.1, p.2, h1, h2⟩, ?_, ?_⟩
      · set y : G n := ⟨p.1, p.2, h1, h2⟩ with hy
        have hinv : (y⁻¹ : G n).val = y.val⁻¹ := Matrix.coe_units_inv y
        have hpy : pairOf y = p := rfl
        have : lg y.val = Real.log (lgArg p) := by
          rw [lg_eq_log_lgArg, ← hinv, ← hpy]; rfl
        have hpos : 0 < lgArg p := lt_of_lt_of_le one_pos (one_le_lgArg _)
        show lg y.val ≤ R
        rw [this]
        exact (Real.log_le_iff_le_exp hpos).2 h3
      · rfl
  rw [hset]
  have hbox : IsCompact ({m : Mat n | ∀ a b, ‖m a b‖ ≤ Real.sqrt (Real.exp R)} ×ˢ
      {m : Mat n | ∀ a b, ‖m a b‖ ≤ Real.sqrt (Real.exp R)}) :=
    (isCompact_entryBox _).prod (isCompact_entryBox _)
  refine hbox.of_isClosed_subset ?_ ?_
  · have c1 : IsClosed {p : Mat n × Mat n | p.1 * p.2 = 1} :=
      isClosed_eq (continuous_fst.matrix_mul continuous_snd) continuous_const
    have c2 : IsClosed {p : Mat n × Mat n | p.2 * p.1 = 1} :=
      isClosed_eq (continuous_snd.matrix_mul continuous_fst) continuous_const
    have c3 : IsClosed {p : Mat n × Mat n | lgArg p ≤ Real.exp R} :=
      isClosed_le lgArg_continuous continuous_const
    exact c1.inter (c2.inter c3)
  · rintro p ⟨-, -, h3⟩
    have hb : ∀ a b, ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ Real.exp R := fun a b =>
      (entry_sq_le_lgArg p a b).trans h3
    refine ⟨fun a b => Real.le_sqrt_of_sq_le ?_, fun a b => Real.le_sqrt_of_sq_le ?_⟩
    · have := hb a b; nlinarith [sq_nonneg ‖p.2 a b‖]
    · have := hb a b; nlinarith [sq_nonneg ‖p.1 a b‖]

theorem lg_continuousOn_and_isCompact :
    ∀ n : ℕ, ContinuousOn (lg (n := n)) (GLs n) ∧ ∀ R : ℝ, IsCompact {y : G n | lg y.val ≤ R} :=
  fun _ => ⟨continuousOn_lg, isCompact_lg_le⟩

end GlobalTheory.CompanionTheory.SobGL
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevelStatement
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_continuous_proper_sublevel : ∀ n : ℕ, ContinuousOn (lg (n := n)) (GLs n) ∧ ∀ R : ℝ, IsCompact {y : G n | lg y.val ≤ R} := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact | exact GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact | (intros; apply GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjKInner
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK.Base

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def RwLin : Prop :=
  ∀ (n : ℕ) (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (ι : Type) [Fintype ι] (L : ι → V →L[ℝ] W) (f : ι → Mat n → V), (∀ i, ContDiffOn ℝ ∞ (f i) (GLs n)) →
    ∀ (w : List (Bool × Fin n × Fin n)), ∀ x ∈ GLs n, Rw w (fun y => ∑ i, L i (f i y)) x = ∑ i, L i (Rw w (f i) x)

end GlobalTheory.CompanionTheory.WaveK.Base
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeReversal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeReversal
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem isWave_time_refl : ∀ {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → IsWave E fun s => u (-s) := by
  intro n E u hu
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨?_, fun t => h2 (-t), ?_, ?_⟩
  · have hm : Set.MapsTo (fun p : ℝ × Mat n => (-p.1, p.2)) (Set.univ ×ˢ GLs n) (Set.univ ×ˢ GLs n) :=
      fun p hp => ⟨Set.mem_univ _, hp.2⟩
    have hc : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => (-p.1, p.2)) (Set.univ ×ˢ GLs n) :=
      (contDiff_fst.neg.prodMk contDiff_snd).contDiffOn
    exact h1.comp hc hm
  · intro t g hg
    have := iteratedDeriv_comp_neg (𝕜 := ℝ) 2 (fun s => u s g) t
    rw [this, h3 (-t) g hg]
    simp
  · intro g hg
    have := deriv_comp_neg (𝕜 := ℝ) (fun s => u s g) 0
    rw [this]
    simpa using h4 g hg

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeReversalStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_time_reversal : ∀ {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → IsWave E fun s => u (-s) := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl | exact GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveCptBoundedTime
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem lg_le_lg_mul_add (hL : LgFacts) {n : ℕ} {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) :
    lg x ≤ lg (x * y) + lg y := by
  have hdx : x.det ≠ 0 := hx
  have hdy : y.det ≠ 0 := hy
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdx hdy
  have hu : IsUnit y.det := isUnit_iff_ne_zero.mpr hdy
  have h1 := (hL n).1 (x * y) hxy y⁻¹ (inv_mem_GLs hy)
  have h2 := (hL n).2.1 y hy
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ hu, h2] at h1
  exact h1

theorem wave_cpt_bounded_time : LgFacts → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V),
    IsWave E u → Cpt (u 0) → ∀ T : ℝ, ∃ R : ℝ, ∀ t, |t| ≤ T → ∀ y ∈ GLs n, R < lg y → u t y = 0 := by
  intro hL hS n E u hu hc T
  obtain ⟨c, hc'⟩ := hS n
  obtain ⟨R₀, hR₀⟩ := hc
  refine ⟨R₀ + |c| * (1 + |T|), fun t ht x hx hlg => hc' E u hu t x hx fun y hy hly => ?_⟩
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  refine hR₀ (x * y) hxy ?_
  have h1 := lg_le_lg_mul_add hL hx hy
  have h2 : |t| ≤ |T| := ht.trans (le_abs_self T)
  have h3 : c * (1 + |t|) ≤ |c| * (1 + |T|) :=
    calc c * (1 + |t|) ≤ |c| * (1 + |t|) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      _ ≤ |c| * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
  linarith

end GlobalTheory.CompanionTheory.WaveMult
end
end
