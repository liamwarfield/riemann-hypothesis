module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianActionColumnBase
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CasselmanWallachLift
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyGrpData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

def liftI (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) : Ideal (𝓞 D.host.E) :=
  ∏ PP ∈ Pg ∪ Q, conjI PP.asIdeal

theorem frMapAdj_zero (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapAdj S T βS βT 0 = 0 := by
  unfold frMapAdj
  simp

theorem isIntM_zero {b a : ℕ} : IsIntM (0 : Matrix (Fin b) (Fin a) (EAf D)) := fun _ _ => zero_mem _

theorem redM_frMapAdj_zero (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (PP : Formalism.L2.DIV.Pl D.host.E) : redM PP (frMapAdj S T βS βT 0) = 0 := by
  have h0 : IsIntM (frMapAdj S T βS βT 0) := by rw [frMapAdj_zero]; exact isIntM_zero
  have h := (GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT 0 0 h0 h0).2 PP
  rw [add_zero] at h
  exact (left_eq_add.mp h)

def liftL (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) : AddSubgroup (WO S T) where
  carrier := {x | IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧
    ∀ PP ∈ Pg ∪ Q, redM PP (frMapAdj S T βS βT x) = 0}
  zero_mem' := by
    refine ⟨fun i j => by simp, ?_, fun PP _ => ?_⟩
    · rw [frMapAdj_zero]; exact isIntM_zero
    · exact redM_frMapAdj_zero S T βS βT PP
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x y hx2 hy2
    refine ⟨fun i j => ?_, h1, fun PP hPP => ?_⟩
    · simp only [Matrix.add_apply, mul_add, hx1 i j, hy1 i j]
    · rw [h2, hx3 PP hPP, hy3 PP hPP, add_zero]
  neg_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    have hneg : frMapAdj S T βS βT (-x) = -frMapAdj S T βS βT x := by
      unfold frMapAdj
      simp [Matrix.map_neg, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]
    have hI : IsIntM (frMapAdj S T βS βT (-x)) := fun i j => by
      rw [hneg, Matrix.neg_apply]; exact neg_mem (hx2 i j)
    obtain ⟨-, h2⟩ := GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x (-x) hx2 hI
    refine ⟨fun i j => ?_, hI, fun PP hPP => ?_⟩
    · simp only [Matrix.neg_apply, mul_neg, hx1 i j]
    · have := h2 PP
      rw [add_neg_cancel, redM_frMapAdj_zero, hx3 PP hPP, zero_add] at this
      exact this.symm

def adjA (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (a : AE D) (x : WO S T) :
    Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  toEAf D a • HMul.hMul βS.val (frMapAdj S T βS βT x)

def IsMover (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e a : AE D)
    (k₀ : GA D S) : Prop :=
  k₀ ∈ GfC S ∧ (∀ x : WO S T, IsHalf (1 - e - cA D e) x → actO S T k₀ 1 x = x) ∧
    ∀ x : WO S T, IsHalf (cA D e) x →
      frMapAdj S T βS βT (actO S T k₀ 1 x) = adjA S T βS βT a x

def IsGen {S T : HSp D} (C : Ctx S T) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e a : AE D) : Prop :=
  ∀ x : WO S T, IsHalf (cA D e) x →
    (IsIntM (adjA S T βS βT a x) ↔
      x ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ)) ∧
    ((IsIntM (adjA S T βS βT a x) ∧
      ∀ PP ∈ Pg ∪ Q, redM PP (adjA S T βS βT a x) = 0) ↔
      x ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)))

end GlobalTheory.LiftLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIff
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecModel

section Conj

variable {n : ℕ} {J P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem lie_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * G + G * X = 0) :
    (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹)
      = (P * X * P⁻¹)ᴴ * J * (P * P⁻¹) + (P * P⁻¹)ᴴ * J * (P * X * P⁻¹) := by rw [h1]; simp
    _ = (P⁻¹)ᴴ * (Xᴴ * G + G * X) * P⁻¹ := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem lie_conj_inv (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * J + J * X = 0) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * (Xᴴ * ((P * P⁻¹)ᴴ * J) + J * (P * P⁻¹) * X) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp

theorem exp_smul_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P * X * P⁻¹)) = P * NormedSpace.exp (t • X) * P⁻¹ := by
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

theorem prod_conj (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P * g * P⁻¹).prod = P * l.prod * P⁻¹ := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h1]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P * a * P⁻¹ * (P * l.prod * P⁻¹) = P * a * (P⁻¹ * P) * l.prod * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
        simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smoothVec_of_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * J + J * X = 0} σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

theorem smoothVec_to_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ w) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w := by
  intro k Xs hXs
  have h := hw k (fun i => P * Xs i * P⁻¹) fun i => lie_conj hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))).prod =
      P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹ := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P * g * P⁻¹ := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj hP _ _
    rw [this, prod_conj hP]
  simpa only [e] using h

end Conj

theorem mem_sm_iff : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ),
    w ∈ M.sm τ ↔ SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w := by
  intro D V S M τ w
  rw [GlobalTheory.SmVec.sm_eq M τ, GlobalTheory.SmVec.mem_smSub]
  constructor
  · intro h
    exact smoothVec_of_conj (M.fr_unit τ) (M.fr_gram τ) h
  · intro h
    exact smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) h

end GlobalTheory.SmVecModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ),
    w ∈ M.sm τ ↔ SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w := by
  first | exact @GlobalTheory.SmVecModel.mem_sm_iff | exact GlobalTheory.SmVecModel.mem_sm_iff | (intros; apply GlobalTheory.SmVecModel.mem_sm_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

def cplx {D : D7} (V W : HSp D) {k : ℕ} (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (z : Mx D 1 k) :
    WO V W :=
  ∑ i, z 0 i • (B i).map (incA D)

section

variable {D : D7} (V W : HSp D) {k : ℕ} (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E)

theorem cplx_add (z z' : Mx D 1 k) : cplx V W B (z + z') = cplx V W B z + cplx V W B z' := by
  simp only [cplx, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem cplx_zero : cplx V W B 0 = 0 := by
  simp [cplx]

theorem continuous_cplx : Continuous (cplx V W B) := by
  unfold cplx
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_id.matrix_elem 0 i).smul continuous_const

theorem cplx_rat (c : Matrix (Fin 1) (Fin k) D.host.E) :
    cplx V W B (c.map (incA D)) = (∑ i, c 0 i • B i).map (incA D) := by
  ext p q
  set_option synthInstance.maxHeartbeats 100000 in
    simp [cplx, Matrix.sum_apply, map_sum, smul_eq_mul]

end

theorem symplO_eq_add {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold symplOH
  linear_combination (-symplO S T x y) * h2

theorem meanX_heisO_rat {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b))
    (ψ : AddChar (AF D.host.F) ℂ) (F : WO V W → ℂ) (hF : IsThetaFunO ψ V W F) (w : WO V W) (hw : w ∈ ratL W V)
    (hwX : ∀ y, symplO V W w (emb V W P Q y) = 0) (x : WO V W) (hx : ∀ y, symplO V W x (emb V W P Q y) = 0) :
    meanX V W P Q μ 𝓨 (heisO ψ V W w F) x = ψ (symplO V W x w) * meanX V W P Q μ 𝓨 F x := by
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  obtain ⟨γ, rfl⟩ := hw
  unfold meanX
  rw [← integral_const_mul]
  congr 1
  funext y
  have hq := hF.quasi γ (emb V W P Q y + x)
  have er : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ) = ratW W V γ := rfl
  simp only [heisO]
  rw [er] at hwX ⊢
  rw [show emb V W P Q y + x + ratW W V γ = ratW W V γ + (emb V W P Q y + x) by abel, hq, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  congr 2
  rw [l1, l2, skew (ratW W V γ) (emb V W P Q y), hH0 _ _ (hwX y), skew (ratW W V γ) x, symplO_eq_add, skew (ratW W V γ) x]
  ring

theorem meanX_mul_star_rat {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b))
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (F F' : WO V W → ℂ) (hF : IsThetaFunO ψ V W F)
    (hF' : IsThetaFunO ψ V W F') (w : WO V W) (hw : w ∈ ratL W V)
    (hwX : ∀ y, symplO V W w (emb V W P Q y) = 0) (x : WO V W) :
    meanX V W P Q μ 𝓨 F (w + x) * star (meanX V W P Q μ 𝓨 F' (w + x)) =
      meanX V W P Q μ 𝓨 F x * star (meanX V W P Q μ 𝓨 F' x) := by
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  obtain ⟨γ, rfl⟩ := hw
  have er : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ) = ratW W V γ := rfl
  rw [er] at hwX ⊢
  have key : ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G →
      meanX V W P Q μ 𝓨 G (ratW W V γ + x) = ψ (-(symplOH V W (ratW W V γ) x)) * meanX V W P Q μ 𝓨 G x := by
    intro G hG
    unfold meanX
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [show emb V W P Q y + (ratW W V γ + x) = ratW W V γ + (emb V W P Q y + x) by abel, hG.quasi, l2,
      hH0 _ _ (hwX y), zero_add]
  rw [key F hF, key F' hF', star_mul]
  have hn : ψ (-(symplOH V W (ratW W V γ) x)) * star (ψ (-(symplOH V W (ratW W V γ) x))) = 1 := by
    have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ) x))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    norm_num
  linear_combination (meanX V W P Q μ 𝓨 F x * star (meanX V W P Q μ 𝓨 F' x)) * hn

end GlobalTheory.IsoMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeil
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.SiegelSet.ConeConv

theorem lintegral_Ici_rpow {b p : ℝ} (hb : 0 < b) (hp : p < 0) :
    ∫⁻ x, (Set.Ici b).indicator (fun x => ENNReal.ofReal (x ^ (p - 1))) x = ENNReal.ofReal (b ^ p / (-p)) := by
  rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici.symm]
  have hlt : p - 1 < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hlt hb)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x (hx : b < x) =>
      Real.rpow_nonneg (le_of_lt (lt_trans hb hx)) _)), integral_Ioi_rpow_of_lt hlt hb]
  congr 1
  have : p - 1 + 1 = p := by ring
  rw [this, div_neg, neg_div]

theorem mem_cone_cons {m : ℕ} {c x : ℝ} (y : Fin (m + 1) → ℝ) :
    (Fin.cons x y : Fin (m + 2) → ℝ) ∈ GlobalTheory.SiegelSet.cone (m + 2) c ↔
      (0 < x ∧ c * y 0 ≤ x) ∧ y ∈ GlobalTheory.SiegelSet.cone (m + 1) c := by
  simp only [GlobalTheory.SiegelSet.cone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hpos, hstep, hlast⟩
    refine ⟨⟨by simpa using hpos 0, by simpa using hstep 0 1 (by simp)⟩, fun i => by simpa using hpos i.succ,
      fun i j hij => by simpa using hstep i.succ j.succ (by simp [hij]),
      fun i hi => by simpa using hlast i.succ (by simp; omega)⟩
  · rintro ⟨⟨h0, h01⟩, hpos, hstep, hlast⟩
    refine ⟨fun i => Fin.cases (by simpa using h0) (fun i => by simpa using hpos i) i, fun i j hij => ?_,
      fun i hi => ?_⟩
    · induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        induction i using Fin.cases with
        | zero =>
          have : j = 0 := Fin.ext (by simpa using hij)
          subst this; simpa using h01
        | succ i => simpa using hstep i j (by simpa using hij)
    · induction i using Fin.cases with
      | zero => simp at hi
      | succ i => simpa using hlast i (by simpa using hi)

theorem mem_cone_one {c x : ℝ} (hc : 0 < c) :
    (fun _ => x : Fin 1 → ℝ) ∈ GlobalTheory.SiegelSet.cone 1 c ↔ c ≤ x := by
  simp only [GlobalTheory.SiegelSet.cone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, _, hlast⟩
    exact hlast 0 rfl
  · intro h
    refine ⟨fun _ => lt_of_lt_of_le hc h, fun i j hij => ?_, fun _ _ => h⟩
    exact absurd hij (by omega)

theorem lintegral_cone_lt_top {c : ℝ} (hc : 0 < c) : ∀ (m : ℕ) (a : ℕ → ℝ),
    (∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a i < 0) →
    ∫⁻ t, (GlobalTheory.SiegelSet.cone (m + 1) c).indicator
      (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) t < ⊤ := by
  intro m
  induction m with
  | zero =>
    intro a ha
    have ha0 : a 0 < 0 := by simpa using ha 0 le_rfl
    change ∫⁻ t : Fin 1 → ℝ, (GlobalTheory.SiegelSet.cone 1 c).indicator
      (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) t < ⊤
    have key := (MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) ℝ)).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
      (fun t : Fin 1 → ℝ => (GlobalTheory.SiegelSet.cone 1 c).indicator
        (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) t)
    refine lt_of_eq_of_lt key.symm ?_
    have : ∀ x : ℝ, (GlobalTheory.SiegelSet.cone 1 c).indicator
        (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm x)
        = (Set.Ici c).indicator (fun x => ENNReal.ofReal (x ^ (a 0 - 1))) x := by
      intro x
      have hx : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm x = fun _ => x := by
        funext i; simp [MeasurableEquiv.funUnique_symm_apply]
      rw [hx]
      by_cases h : c ≤ x
      · rw [Set.indicator_of_mem ((mem_cone_one hc).2 h), Set.indicator_of_mem (Set.mem_Ici.2 h)]
        simp
      · rw [Set.indicator_of_notMem (fun h' => h ((mem_cone_one hc).1 h')),
          Set.indicator_of_notMem (fun h' => h (Set.mem_Ici.1 h'))]
    simp_rw [this]
    rw [lintegral_Ici_rpow hc ha0]
    exact ENNReal.ofReal_lt_top
  | succ m ih =>
    intro a ha
    have ha0 : a 0 < 0 := by simpa using ha 0 (Nat.zero_le _)
    set a' : ℕ → ℝ := fun i => if i = 0 then a 0 + a 1 else a (i + 1) with ha'
    have hsum : ∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a' i < 0 := by
      intro k hk
      have h := ha (k + 1) (by omega)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
      rw [Finset.sum_range_succ']
      simp only [ha', if_pos, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false] at *
      linarith
    set K : ℝ≥0∞ := ENNReal.ofReal (c ^ a 0 / (-a 0))
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0
    rw [← (MeasurePreserving.symm _ (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0)).lintegral_comp_emb
      e.symm.measurableEmbedding, Measure.volume_eq_prod, ← lintegral_prod_swap]
    refine lt_of_le_of_lt (lintegral_prod_le _) ?_
    have hpt : ∀ y : Fin (m + 1) → ℝ, ∫⁻ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
        (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (e.symm (Prod.swap (y, x)))
        ≤ K * (GlobalTheory.SiegelSet.cone (m + 1) c).indicator
          (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a' i.val - 1))) y := by
      intro y
      have he : ∀ x, e.symm (Prod.swap (y, x)) = Fin.cons x y := by
        intro x; simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero'] <;> rfl
      simp_rw [he]
      by_cases hy : y ∈ GlobalTheory.SiegelSet.cone (m + 1) c
      · have hy0 : 0 < y 0 := hy.1 0
        have hb : 0 < c * y 0 := mul_pos hc hy0
        set T : ℝ≥0∞ := ∏ i : Fin (m + 1), ENNReal.ofReal (y i ^ (a (i.val + 1) - 1))
        have hfun : ∀ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
            (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (Fin.cons x y)
            = (Set.Ici (c * y 0)).indicator (fun x => ENNReal.ofReal (x ^ (a 0 - 1))) x * T := by
          intro x
          by_cases hx : c * y 0 ≤ x
          · rw [Set.indicator_of_mem ((mem_cone_cons y).2 ⟨⟨lt_of_lt_of_le hb hx, hx⟩, hy⟩),
              Set.indicator_of_mem (Set.mem_Ici.2 hx), Fin.prod_univ_succ]
            simp [T, Fin.val_succ]
          · rw [Set.indicator_of_notMem (fun h' => hx ((mem_cone_cons y).1 h').1.2),
              Set.indicator_of_notMem (fun h' => hx (Set.mem_Ici.1 h')), zero_mul]
        simp_rw [hfun]
        rw [lintegral_mul_const' _ _ (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top),
          lintegral_Ici_rpow hb ha0, Set.indicator_of_mem hy]
        apply le_of_eq
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        have hrest : ∏ j : Fin m, ENNReal.ofReal (y j.succ ^ (a (j.succ.val + 1) - 1))
            = ∏ j : Fin m, ENNReal.ofReal (y j.succ ^ (a' j.succ.val - 1)) :=
          Finset.prod_congr rfl fun j _ => by simp [ha', Fin.val_succ]
        have h1 : 0 ≤ (c * y 0) ^ a 0 / (-a 0) := div_nonneg (Real.rpow_nonneg hb.le _) (by linarith)
        have h2 : 0 ≤ c ^ a 0 / (-a 0) := div_nonneg (Real.rpow_nonneg hc.le _) (by linarith)
        have h0 : ENNReal.ofReal ((c * y 0) ^ a 0 / (-a 0)) * ENNReal.ofReal (y 0 ^ (a ((0 : Fin (m + 1)).val + 1) - 1))
            = K * ENNReal.ofReal (y 0 ^ (a' (0 : Fin (m + 1)).val - 1)) := by
          simp only [K, ha', Fin.val_zero, zero_add, if_true]
          rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2]
          congr 1
          rw [Real.mul_rpow hc.le hy0.le, show a 0 + a 1 - 1 = (a 1 - 1) + a 0 by ring, Real.rpow_add hy0]
          ring
        rw [hrest, ← mul_assoc, ← mul_assoc, h0]
      · have hz : ∀ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
            (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (Fin.cons x y) = 0 :=
          fun x => Set.indicator_of_notMem (fun h' => hy ((mem_cone_cons y).1 h').2) _
        simp_rw [hz, lintegral_zero]
        exact bot_le
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ih a' hsum)

theorem measurableSet_cone (r : ℕ) (c : ℝ) : MeasurableSet (GlobalTheory.SiegelSet.cone r c) := by
  simp only [GlobalTheory.SiegelSet.cone, Set.setOf_and, Set.setOf_forall]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_const.mul (measurable_pi_apply j)) (measurable_pi_apply i)).inter
     (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_le measurable_const (measurable_pi_apply i)))

end GlobalTheory.SiegelSet.ConeConv


open GlobalTheory.SiegelSet.ConeConv in
theorem GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top : ∀ (F : Type) [Field F] [NumberField F] (n r d : ℕ) {c : ℝ}, 0 < c →
    d < 2 * (n - r) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n r d c hc hd
  have hf : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos
  cases r with
  | zero =>
    simp only [GlobalTheory.SiegelSet.modulus, Finset.univ_eq_empty, Finset.prod_empty, mul_one, inv_one, ENNReal.ofReal_one,
      lintegral_const, one_mul]
    rw [Measure.restrict_apply MeasurableSet.univ]
    change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) _ < ⊤
    rw [Measure.pi_of_empty]
    simp only [Set.univ_inter]
    exact measure_lt_top _ _
  | succ m =>
    set f := Module.finrank ℚ F with hfdef
    set a : ℕ → ℝ := fun i => (f : ℝ) * d - 2 * f * ((n : ℝ) - 2 * i - 1) with hadef
    have closed : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), a i = f * (k + 1) * (d - 2 * n + 2 * (k + 1)) := by
      intro k
      induction k with
      | zero => rw [Finset.sum_range_one]; simp only [hadef]; push_cast; ring
      | succ k ih => rw [Finset.sum_range_succ, ih]; simp only [hadef]; push_cast; ring
    have hsum : ∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a i < 0 := by
      intro k hk
      rw [closed]
      have h1 : d + 2 * (k + 1) < 2 * n := by omega
      have h2 : (d : ℝ) + 2 * (k + 1) < 2 * n := by exact_mod_cast h1
      exact mul_neg_of_pos_of_neg (mul_pos hf (by positivity)) (by linarith)
    have hmeas := measurableSet_cone (m + 1) c
    rw [setLIntegral_congr_fun hmeas (g := fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) ?_,
      ← lintegral_indicator hmeas]
    · exact lintegral_cone_lt_top hc m a hsum
    intro t ht
    have hpos : ∀ i, 0 < t i := ht.1
    dsimp only
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => pow_nonneg (hpos i).le _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hpos i).le _)]
    congr 1
    unfold GlobalTheory.SiegelSet.modulus
    rw [← hfdef]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hti := hpos i
    rw [← Real.rpow_natCast, ← Real.rpow_intCast,
      show a i.val - 1 = ((f * d : ℕ) : ℝ) - ((2 * (f : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1 by
        simp only [hadef]; push_cast; ring,
      Real.rpow_sub hti, Real.rpow_sub hti, Real.rpow_one]
    field_simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil : ∀ (F : Type) [Field F] [NumberField F] (n r d : ℕ) {c : ℝ}, 0 < c → d < 2 * (n - r) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) * ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top | exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top | (intros; apply GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory NumberField Matrix

namespace GlobalTheory.KFiniteDetermined

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_kFin_of_mem_lowT {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {v : M.sm τ} (hv : v ∈ lowT M τ) : (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ :=
  (sSup_le (a := GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) fun A hA _ hw => ⟨A, hA.1, hw, hA.2.1⟩) hv

theorem restrInj : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.RestrInj D :=
  fun D θ hθ V S M J χ T hT h0 =>
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D V S M θ hθ (GlobalTheory.LowTypeRestriction.lowT_ne_bot M) J χ T hT
      fun v => h0 _ fun τ => mem_kFin_of_mem_lowT M τ (v τ).2

end GlobalTheory.KFiniteDetermined
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal TensorProduct

namespace GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def term (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E) : ℂ :=
  res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G) 0

def phase (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) : ℂ :=
  ψ (symplO V W (isoPart V W C' (Matrix.map y (incA D))) (isoPart V W C κ))

def pairQ (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) : Matrix (Fin r) (Fin W.rank) D.host.E :=
  D.host.xi0 • (adj D y * W.gram)

def ratPair (W : HSp D) {r : ℕ} (y x : Matrix (Fin W.rank) (Fin r) D.host.E) : ℝ :=
  ((Algebra.trace ℚ D.host.E (Matrix.trace (pairQ W y * x)) : ℚ) : ℝ)

def dirAt (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin r) ℂ) : Matrix (Fin W.rank) (Fin V.rank) ℂ :=
  z * (adj D C * V.gram).map (tauE D τ)

def derAlong (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E) (G : WO V W → ℂ) : WO V W → ℂ :=
  ∑ τ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G

def finLift {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  x.map fun e => (pairA D.host.F 0 1 : AF D.host.F) ⊗ₜ[D.host.F] e

end GlobalTheory.MixedTerm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowerWittTowerIsotropicSplitEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowerWittTowerIsotropicSplitEmbedding
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerSplit

theorem signCard_of_isEnum {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) (b : Bool) :
    GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard S b = (Finset.univ.filter fun a => ε a = b).card := by
  obtain ⟨hl, q, hq, rfl⟩ := h
  have hinj : Function.Injective q := fun a c hac => hl.injective (by rw [hq, hq, hac])
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard
  rw [Finset.filter_image, Finset.card_image_of_injective]
  intro a c hac
  exact hinj (Prod.ext_iff.1 hac).1

theorem hasSignature_of_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    Formalism.UG.HasSignature (gramAt D V τ) (GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (S τ) true)
      (GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (S τ) false) := by
  rw [signCard_of_isEnum (M.enum τ), signCard_of_isEnum (M.enum τ)]
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  refine GlobalTheory.AutInhab.hasSignature_of_frame (P := (M.fr τ)⁻¹) ?_ ?_
  · exact IsUnit.of_mul_eq_one _ (Matrix.nonsing_inv_mul _ hd)
  · rw [← M.fr_gram τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one,
      Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem exists_isoSplit : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (_M : DSModel V S) (r : ℕ)
    (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∃ (V' : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B ∧
      GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S r V' := by
  intro D V S M r C hC
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj V C
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp V.frame.equivFun.toLinearMap hC.2.1
  have hiso : ∀ a b, V.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hC.2.2]; rfl
  obtain ⟨V', ι, h1, h2, h3⟩ := GlobalTheory.WittLow.exists_lower Examples₂.star_isIntegral V e he hiso
  have hlow : IsWittLower V V' r := by
    refine ⟨h1, ι, h2, _, ⟨hC.2.1, hC.2.2⟩, ?_⟩
    refine Matrix.ext fun a b => ?_
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h3 _ _
  refine ⟨V', frameMat V V' ι, ⟨hC, ?_, ?_, by omega⟩, fun τ => ?_⟩
  · refine Matrix.ext fun a b => ?_
    unfold adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h2 _ _
  · refine Matrix.ext fun a b => ?_
    unfold adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul, ← V.herm.eq, h3]
    simp
  · obtain ⟨s, hs⟩ := GlobalTheory.WittLow.exists_sig V' (tauE D τ)
    have hs' : Formalism.UG.HasSignature (gramAt D V' τ) s.1 s.2 := hs
    obtain ⟨e1, e2⟩ := Formalism.UG.P.signature_unique _ _ _ _ _ _ (GlobalTheory.WittSign.hasSignature_of_isWittLower hlow τ hs')
      (hasSignature_of_model M τ)
    exact ⟨s.1, s.2, e1, e2, hs'⟩

end GlobalTheory.TowerSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowerWittTowerIsotropicSplitEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerWittTower_isotropicSplitEmbedding : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (_M : DSModel V S) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∃ (V' : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B ∧ GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S r V' := by
  first | exact @GlobalTheory.TowerSplit.exists_isoSplit | exact GlobalTheory.TowerSplit.exists_isoSplit | (intros; apply GlobalTheory.TowerSplit.exists_isoSplit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrability
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrability
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumFockLaws

theorem vacuumFock_onObjects : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D :=
  fun D => vacuumFock_of_thetaSquareIntegrable D (GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D)

end GlobalTheory.VacuumFockLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrabilityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_overVacuum_isometry : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := by
  first | exact @GlobalTheory.VacuumFockLaws.vacuumFock_onObjects | exact GlobalTheory.VacuumFockLaws.vacuumFock_onObjects | (intros; apply GlobalTheory.VacuumFockLaws.vacuumFock_onObjects <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachOfHyp
noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix Filter GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped Topology

namespace GlobalTheory.CWGeneral

variable {n : ℕ} {ε : Fin n → Bool}

section Sub

variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]


end Sub

section KFin

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)}

theorem dense_smoothAll_of_irred (hσ : IsURepOn (UJset ε) σ) (hi : IsIrredOn (UJset ε) σ) :
    Dense (smoothAll (Jm ε) σ : Set H) := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · intro x
    rw [Subsingleton.elim x 0]
    exact subset_closure (smoothAll (Jm ε) σ).zero_mem
  · refine dense_of_irred hi (fun g hg v hv k x hx hxG => ?_) ?_
    · letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
      letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
      have h1 := hv k (fun t => x t * g) (hx.mul contDiff_const) fun t => mul_mem_UJ (hxG t) hg
      convert h1 using 2 with t
      exact (sigma_mul hσ (hxG t) hg v).symm
    · obtain ⟨v, hv, hs⟩ := GlobalTheory.GardingVec.exists_garding hσ
      exact (Submodule.ne_bot_iff _).2 ⟨v, hs, hv⟩

theorem sm_of_isKFin (hHC : GlobalTheory.Published.HarishChandraModules) (hσ : IsURepOn (UJset ε) σ)
    (hi : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : Sm ε σ v := by
  have := hHC.smoothVec hσ hi hv (P := 1) (G := Jm ε) isUnit_one (by simp)
  rwa [conj_one_eq] at this

theorem isKFin_dRep_of_irred (hHC : GlobalTheory.Published.HarishChandraModules) (hσ : IsURepOn (UJset ε) σ)
    (hi : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    IsKFin ε σ (dRep σ X v) := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  have hS : S ≤ smooth (Jm ε) σ := fun s hs => sm_of_isKFin hHC hσ hi ⟨S, h1, hs, h3⟩
  let b := Module.finBasis ℝ (lie (Jm ε))
  let L : Fin (Module.finrank ℝ (lie (Jm ε))) → (S →ₗ[ℂ] H) := fun i =>
    (smooth (Jm ε) σ).subtype ∘ₗ dOp (isUnit_Jm ε) hσ (b i).2 ∘ₗ Submodule.inclusion hS
  let T : Submodule ℂ H := ⨆ i, LinearMap.range (L i)
  have hT : ∀ Y ∈ lieSet ε, ∀ s ∈ S, dRep σ Y s ∈ T := by
    intro Y hY s hs
    have e : Y = ∑ i, b.repr ⟨Y, hY⟩ i • (b i : Mx n) := by
      have := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
      simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using this.symm
    rw [e, GlobalTheory.LowTypeDetermined.dRep_sum (isUnit_Jm ε) hσ (dense_smoothAll_of_irred hσ hi) (fun i => (b i).2)
      (hS hs)]
    refine T.sum_mem fun i _ => T.smul_mem _ ?_
    exact Submodule.mem_iSup_of_mem i ⟨⟨s, hs⟩, rfl⟩
  refine ⟨T, inferInstance, hT X hX v h2, fun k hk w hw => ?_⟩
  have hg := K_le_UJ hk
  have : T ≤ T.comap (σ k : H →ₗ[ℂ] H) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    have hinv : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv (mul_inv_UJ hg)
    have hY : k * (b i : Mx n) * k⁻¹ ∈ lieSet ε := by
      have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) (b i).2
      rwa [hinv] at this
    have e := Dw_translate hσ hg (hS s.2) (l := [k * (b i : Mx n) * k⁻¹]) (by simpa using hY)
    have e2 : k⁻¹ * (k * (b i : Mx n) * k⁻¹) * k = b i := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_UJ hg, one_mul, mul_assoc, inv_mul_UJ hg, mul_one]
    simp only [Dw, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, e2] at e
    show σ k (dRep σ (b i) s) ∈ T
    rw [← e]
    exact hT _ hY _ (h3 k hk s s.2)
  exact this hw

end KFin

end GlobalTheory.CWGeneral

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

noncomputable section

namespace GlobalTheory.LeviNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def phase (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y u : Mx D W.rank r) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D)
    (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace))

def resNorm (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)) (f : WO V W → ℂ) (u : Mx D W.rank r) : ℂ :=
  ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x *
    starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x) ∂μ'

theorem phase_apply (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y u : Mx D W.rank r) :
    phase ψ W y u = ψ (Algebra.trace (AF D.host.F) (AE D)
      (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace)) := rfl

end GlobalTheory.LeviNorm

end
end
