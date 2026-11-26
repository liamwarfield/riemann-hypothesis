module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementGelfandPolynomialFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminorStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilTheta

theorem schwartzA_continuous_and_dominated : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (Φ : Mx D m n → ℂ),
    Φ ∈ schwartzA θ m n → Continuous Φ ∧ ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
      (g : Fin k → (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) ∧
      ∀ x, ‖Φ x‖ₑ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := by
  intro D θ hθ m n Φ hΦ
  have hy : Continuous fun x : Mx D m n => (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ m n).matrix_elem i j
  have hz : Continuous fun x : Mx D m n =>
      (fun i j => finPart D (x i j) : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j)
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨(f.continuous.comp hy).mul (hg.1.continuous.comp hz), 1, fun _ => f, fun _ => g, fun _ => hg, fun x => ?_⟩
    simp
  | zero =>
    exact ⟨continuous_const, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun x => by simp⟩
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, k₁, f₁, g₁, hg₁, hb₁⟩ := h₁
    obtain ⟨c₂, k₂, f₂, g₂, hg₂, hb₂⟩ := h₂
    refine ⟨c₁.add c₂, k₁ + k₂, Fin.append f₁ f₂, Fin.append g₁ g₂, fun i => ?_, fun x => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]; exact hg₁ i
      · rw [Fin.append_right]; exact hg₂ i
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      exact (enorm_add_le _ _).trans (add_le_add (hb₁ x) (hb₂ x))
  | smul c Φ _ h =>
    obtain ⟨hc, k, f, g, hg, hb⟩ := h
    refine ⟨hc.const_smul c, k, fun i => c • f i, g, hg, fun x => ?_⟩
    have e : ∀ i, ‖(c • f i) (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ =
        ‖c‖ₑ * ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := fun i => by
      rw [smul_apply, smul_eq_mul, mul_assoc, enorm_mul]
    simp only [e, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, enorm_mul]
    gcongr
    exact hb x

end GlobalTheory.CompanionTheory.WeilTheta

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfiniteStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bound_finite_infinite : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (Φ : Mx D m n → ℂ), Φ ∈ schwartzA θ m n → Continuous Φ ∧ ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ) (g : Fin k → (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ), (∀ i, g i ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ∀ x, ‖Φ x‖ₑ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := by
  first | exact @GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated | exact GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated | (intros; apply GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitriangularMapInduction
open MeasureTheory Matrix
open scoped Pointwise

namespace GlobalTheory.UnipChange

section Shear

variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
  {ι : Type} [Fintype ι]

end Shear

section Linear

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]

private theorem map_mul_left_eq_smul' (a : F) (ha : a ≠ 0) :
    Measure.map (fun x => a * x) ν = distribHaarChar F (Units.mk0 a ha)⁻¹ • ν := by
  have hf : (fun x : F => a * x) = fun x => Units.mk0 a ha • x := by
    funext x; simp [Units.smul_def]
  ext s hs
  rw [Measure.map_apply (by rw [hf]; exact (continuous_const_smul _).measurable) hs, hf,
    Set.preimage_smul, ← distribHaarChar_mul ν]
  rw [Measure.coe_nnreal_smul_apply]

private theorem map_diagonal_mulVec_pi (D : κ → F) (hD : ∀ i, D i ≠ 0) :
    Measure.map (diagonal D).mulVec (Measure.pi fun _ : κ => ν)
      = (∏ i, distribHaarChar F (Units.mk0 (D i) (hD i))⁻¹) • Measure.pi fun _ : κ => ν := by
  have hfun : (diagonal D).mulVec = fun x i => (fun y => D i * y) (x i) := by
    funext x i; simp [mulVec_diagonal]
  haveI : ∀ i, SigmaFinite (Measure.map (fun y => D i * y) ν) := fun i => by
    rw [map_mul_left_eq_smul' ν (D i) (hD i)]; infer_instance
  rw [hfun, Measure.pi_map_pi (f := fun i y => D i * y)
    (fun i => (continuous_const.mul continuous_id).aemeasurable)]
  simp_rw [map_mul_left_eq_smul' ν _ (hD _)]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Measure.coe_nnreal_smul_apply _ _ _

private theorem measurePreserving_transvection_mulVec (t : TransvectionStruct κ F) :
    MeasurePreserving t.toMatrix.mulVec (Measure.pi fun _ : κ => ν)
      (Measure.pi fun _ : κ => ν) := by
  let p : κ → Prop := fun i => i ≠ t.i
  let α : Type := { x // p x }
  let β : Type := { x // ¬p x }
  let g : (α → F) → (β → F) → β → F := fun a b => (fun _ => t.c * a ⟨t.j, t.hij.symm⟩) + b
  let G : (α → F) × (β → F) → (α → F) × (β → F) := fun q => (id q.1, g q.1 q.2)
  let e : (κ → F) ≃ᵐ (α → F) × (β → F) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : κ => F) p
  have hmv : t.toMatrix.mulVec = e.symm ∘ G ∘ e := by
    cases t with | mk i j hij c =>
    ext f k
    by_cases h : i = k
    · subst h
      simp [e, G, g, p, TransvectionStruct.toMatrix, transvection, mulVec, dotProduct,
        add_mul, Finset.sum_add_distrib, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd, Matrix.single, ite_and, Matrix.one_apply, ite_mul]
      ring
    · simp [e, G, g, p, TransvectionStruct.toMatrix, transvection, mulVec, dotProduct,
        add_mul, Finset.sum_add_distrib, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd, h, Matrix.single, ite_and, Ne.symm h, Matrix.one_apply,
        ite_mul]
  rw [hmv]
  have hA : MeasurePreserving e (Measure.pi fun _ : κ => ν)
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : κ => ν) p
  have hB : MeasurePreserving G ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν))
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) := by
    have hg : Measurable (Function.uncurry g) := by
      refine Measurable.add ?_ measurable_snd
      exact Measurable.of_eval fun _ =>
        ((measurable_pi_apply _).comp measurable_fst).const_mul _
    exact (MeasurePreserving.id _).skew_product hg
      (Filter.Eventually.of_forall fun a => map_add_left_eq_self _ _)
  exact ((hA.symm e).comp hB).comp hA

theorem _root_.GlobalTheory.UnipChange.smul_map_mulVec_pi (M : Matrix κ κ F) (u : Fˣ)
    (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν)
      = Measure.pi fun _ : κ => ν := by
  have hmeas : ∀ N : Matrix κ κ F, Measurable N.mulVec := fun N =>
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have key : ∀ u : Fˣ, (u : F) = M.det → Measure.map M.mulVec (Measure.pi fun _ : κ => ν)
      = distribHaarChar F u⁻¹ • Measure.pi fun _ : κ => ν := by
    refine diagonal_transvection_induction_of_det_ne_zero (fun N : Matrix κ κ F => ∀ u : Fˣ,
      (u : F) = N.det → Measure.map N.mulVec (Measure.pi fun _ : κ => ν)
        = distribHaarChar F u⁻¹ • Measure.pi fun _ : κ => ν) M
      (hu ▸ u.ne_zero) ?_ ?_ ?_
    · intro D hD u hu
      have hD' : ∀ i, D i ≠ 0 := fun i => by
        rw [det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      rw [map_diagonal_mulVec_pi ν D hD']
      have hu' : u = ∏ i, Units.mk0 (D i) (hD' i) := by
        ext
        rw [hu, det_diagonal, Units.coe_prod]
        rfl
      rw [hu', ← Finset.prod_inv_distrib, map_prod]
    · intro t u hu
      have hu' : u = 1 := by
        ext
        rw [hu, TransvectionStruct.det, Units.val_one]
      rw [hu', inv_one, map_one, one_smul]
      exact (measurePreserving_transvection_mulVec ν t).map_eq
    · intro A B hA hB hPA hPB u hu
      have hcomp : (A * B).mulVec = A.mulVec ∘ B.mulVec :=
        funext fun x => (mulVec_mulVec x A B).symm
      have hu' : u = Units.mk0 _ hA * Units.mk0 _ hB := by
        ext
        simp [hu, det_mul]
      rw [hcomp, ← Measure.map_map (hmeas A) (hmeas B), hPB (Units.mk0 _ hB) rfl,
        Measure.map_smul _ (hmeas A).aemeasurable, hPA (Units.mk0 _ hA) rfl, smul_smul, hu', _root_.mul_inv_rev, map_mul,
        mul_comm]
  rw [key u hu]
  ext s hs
  rw [Measure.smul_apply, Measure.coe_nnreal_smul_apply, smul_eq_mul, ← mul_assoc,
    ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one, one_mul]

end Linear

section Algebra

variable {k : Type} [Field k] {r : ℕ} {b : Fin r → ℕ}

end Algebra

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
  {r : ℕ} {b : Fin r → ℕ}

end Top

end GlobalTheory.UnipChange
end

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def uM (n : ℕ) (x : Fin n → k) : Mir k n := unipIn k n (Multiplicative.ofAdd x)

def shearGL (n : ℕ) (b : Fin (n + 1) → k) : GL (Fin (n + 1)) k :=
  open Classical in if h : IsUnit (1 + vecMulVec (eLast k n) b) then h.unit else 1

def piHaar [MeasurableSpace k] (ν : Measure k) (m : ℕ) : Measure (Fin m → k) := Measure.pi fun _ => ν

def wt (ψ : AddChar k Circle) (n : ℕ) (x : Fin (n + 1) → k) : ℂ := ((ψ (-x (Fin.last n)) : Circle) : ℂ)

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def coef (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v' : V') (x : Fin n → k) : ℂ :=
  B (T (uM n x) v) v'

def TwInv (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ) : Prop :=
  ∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
    ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v'

def JJ [MeasurableSpace k] (ν : Measure k) (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V') : ℂ :=
  ∫ x in M, wt ψ n x * coef T B v v' x ∂(piHaar ν (n + 1))

def EvVal [MeasurableSpace k] (ν : Measure k) (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v' : V') (A : ℂ) : Prop :=
  ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) →
    JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' = A

end Rep

end GlobalTheory.CompanionTheory.MirPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

structure Good (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) : Prop where
  left : ∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g
  level : ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : GlobalTheory.UAut.IsSm σ J φ
  growth : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr lineDer φ g‖ ≤ C * (height σ J g : ℝ) ^ A
  cusp : IsCuspidal σ J φ

def CloseInf (u : GAd σ J) (δ : ℝ) : Prop :=
  u ∈ infPts σ J ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
    ‖(archMat σ J τ (projArch σ J w u) - 1) i j‖ ≤ δ

variable {σ J}

def pre (X : Matrix (Fin n) (Fin r) E) (s : Fin r) : Matrix (Fin n) (Fin (s.val + 1)) E :=
  X.submatrix id (Fin.castLE s.2)

def ratio (t : Fin r → ℝ) (s : Fin r) : ℝ :=
  if h : s.val + 1 < r then t s / t ⟨s.val + 1, h⟩ else t s

def rbar (t : Fin r → ℝ) : ℝ := Finset.univ.fold max 1 (ratio t)

theorem one_le_rbar (t : Fin r → ℝ) : 1 ≤ rbar t := Finset.le_fold_max _ |>.2 (Or.inl le_rfl)

theorem ratio_le_rbar (t : Fin r → ℝ) (s : Fin r) : ratio t s ≤ rbar t :=
  (Finset.le_fold_max _).2 (Or.inr ⟨s, Finset.mem_univ s, le_rfl⟩)

theorem rbar_eq (t : Fin r → ℝ) : rbar t = 1 ∨ ∃ s, rbar t = ratio t s := by
  have key : ∀ S : Finset (Fin r), S.fold max 1 (ratio t) = 1 ∨ ∃ s, S.fold max 1 (ratio t) = ratio t s := fun S => by
    induction S using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert a S ha ih =>
      rw [Finset.fold_insert ha]
      rcases max_choice (ratio t a) (S.fold max 1 (ratio t)) with e | e
      · exact Or.inr ⟨a, e⟩
      · rw [e]; exact ih
  exact key _

theorem ratio_pos {c : ℝ} {t : Fin r → ℝ} (ht : t ∈ cone r c) (s : Fin r) : 0 < ratio t s := by
  unfold ratio
  split_ifs with h
  · exact div_pos (ht.1 _) (ht.1 _)
  · exact ht.1 _

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecomp
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecomp
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.HpgMem

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
    (h : HPG k i t), ∃ (x : Fin i → k) (q : Qp k i t),
      (h : Mir k (i + t)) = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) := by
  intro k _ _ _ _ i t h
  set M : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k :=
    (((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) with hM
  have hmem : ((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) ∈
      GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG i t) := h.2
  have hp := GlobalTheory.SmGL.mem_parab_iff.1 hmem
  have hp' : ∀ (a : Fin t) (b : Fin (i + 1)),
      M (GlobalTheory.BZMir.Leib.ePG i t ⟨true, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = 0 :=
    fun a b => hp true false a b (by decide)
  have hzero : ∀ (r : Fin t) (c : Fin i),
      M (Fin.castSucc (Fin.natAdd i r)) (Fin.castSucc (Fin.castAdd t c)) = 0 := by
    intro r c
    have h₁ : Fin.castSucc (Fin.natAdd i r) = GlobalTheory.BZMir.Leib.ePG i t ⟨true, r⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val, Fin.coe_natAdd])
    have h₂ : Fin.castSucc (Fin.castAdd t c) =
        GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.castSucc c⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_false_val, Fin.coe_castAdd])
    rw [h₁, h₂]
    exact hp' r (Fin.castSucc c)
  have hlast : ∀ r : Fin t, M (Fin.castSucc (Fin.natAdd i r)) (Fin.last (i + t)) = 0 := by
    intro r
    have h₁ : Fin.castSucc (Fin.natAdd i r) = GlobalTheory.BZMir.Leib.ePG i t ⟨true, r⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val, Fin.coe_natAdd])
    rw [h₁, ← GlobalTheory.BZMir.Leib.ePG_false_last i t]
    exact hp' r (Fin.last i)
  have hgen : ∀ (r : Fin t) (c : Fin i) (x y : Fin (i + t)), (x : ℕ) = i + r → (y : ℕ) = c →
      ((GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t)) k) :
        Matrix (Fin (i + t)) (Fin (i + t)) k) x y = 0 := by
    intro r c x y hx hy
    have hx' : x = Fin.natAdd i r := Fin.ext (by rw [hx, Fin.coe_natAdd])
    have hy' : y = Fin.castAdd t c := Fin.ext (by rw [hy, Fin.coe_castAdd])
    subst hx' hy'
    exact hzero r c
  have hq : GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)) ∈
      GlobalTheory.CompanionTheory.BZPsiPG.Qp k i t := by
    unfold GlobalTheory.CompanionTheory.BZPsiPG.Qp
    rw [GlobalTheory.SmGL.mem_parab_iff]
    intro a b ia jb hab
    cases a <;> cases b
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
    · refine hgen ia jb _ _ ?_ ?_
      · rfl
      · rfl
    · exact absurd hab (by decide)
  obtain ⟨x, hx⟩ : ∃ x : Fin i → k, x = fun a => M (Fin.castSucc (Fin.castAdd t a)) (Fin.last (i + t)) :=
    ⟨_, rfl⟩
  have hv : (fun r : Fin (i + t) => M (Fin.castSucc r) (Fin.last (i + t))) = GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x := by
    funext r
    cases r using Fin.addCases with
    | left a => rw [GlobalTheory.CompanionTheory.BZPsiPG.topV, Fin.append_left, hx]
    | right b => rw [GlobalTheory.CompanionTheory.BZPsiPG.topV, Fin.append_right, Pi.zero_apply]; exact hlast b
  refine ⟨x, ⟨_, hq⟩, ?_⟩
  apply Subtype.ext
  have hd : ((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k) =
      unip k (i + t) (Multiplicative.ofAdd fun r => M (Fin.castSucc r) (Fin.last (i + t))) *
        glEmb k (i + t) (mirabolicProjection k (i + t) (h : Mir k (i + t))) := by
    have hh := (mem_Mir_iff k ((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k)).1 (h : Mir k (i + t)).2
    ext1
    rw [Units.val_mul]
    show _ = (1 + colMat k (i + t) _) * glEmbMat k (i + t) (blockMat k (i + t) _)
    rw [add_mul, one_mul, colMat_mul_glEmbMat]
    ext a b
    induction a using Fin.lastCases with
    | last =>
      rw [hh]
      induction b using Fin.lastCases <;>
        simp [glEmbMat, colMat, eLast, Fin.castSucc_ne_last, Pi.single_apply]
    | cast a =>
      induction b using Fin.lastCases <;>
        simp [glEmbMat, colMat, blockMat, Fin.castSucc_ne_last, M]
  refine hd.trans ?_
  exact congrArg (· * glEmb k (i + t) (mirabolicProjection k (i + t) (h : Mir k (i + t))))
    (congrArg (fun w => unip k (i + t) (Multiplicative.ofAdd w)) hv)

end GlobalTheory.CompanionTheory.BZPsiPG.HpgMem
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_unipotent_levi_decomp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i t), ∃ (x : Fin i → k) (q : Qp k i t), (h : Mir k (i + t)) = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main | exact GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestDerivativeOfProduct
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HighestDeriv

section Coinv

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Coinv

def piFinTwoTensor (X : Fin 2 → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] :
    (⨂[ℂ] a, X a) ≃ₗ[ℂ] X 0 ⊗[ℂ] X 1 :=
  ((LinearEquiv.lTensor _ (PiTensorProduct.subsingletonEquiv (s := fun i : Fin 1 => X i.succ) 0).symm).trans
    (GlobalTheory.SmGL.MultiIrr.tensorCons X)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Two

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t : ℕ}

def piTensorTwoEquiv' (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    (piTensor (GlobalTheory.BZMir.Leib.twoRep (k := k) π₁ π₂)).Equiv
      ((extTensor π₁ π₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
  .mk (GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W)
        (piTensor (GlobalTheory.BZMir.Leib.twoRep (k := k) π₁ π₂) g (PiTensorProduct.tprod ℂ x)) =
      extTensor π₁ π₂ ((leviTwo k (Fin r) (Fin t)).symm g)
        (GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod, GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod]
    exact (extTensor_tmul π₁ π₂ ((leviTwo k (Fin r) (Fin t)).symm g) (x false) (x true)).symm

theorem nonempty_prod2_equiv (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty ((prod2 (k := k) rfl π₁ π₂).Equiv (prod₂ π₁ π₂)) :=
  ⟨LocGL.parIndEquiv (two (stdSum (rfl : r + t = r + t))) (piTensorTwoEquiv' π₁ π₂)⟩

end Two

section Main

end Main

end GlobalTheory.CompanionTheory.HighestDeriv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredity
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZSeg

theorem rank_piTensorProduct_le_one {ι : Type} [Fintype ι] (W : ι → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module ℂ (W a)] (hW : ∀ a, Module.rank ℂ (W a) ≤ 1) : Module.rank ℂ (⨂[ℂ] a, W a) ≤ 1 := by
  classical
  choose w hw using fun a => rank_le_one_iff.1 (hW a)
  refine rank_le_one_iff.2 ⟨PiTensorProduct.tprod ℂ w, fun t => ?_⟩
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    choose c hc using fun a => hw a (f a)
    refine ⟨r * ∏ a, c a, ?_⟩
    have hf : f = fun a => c a • w a := funext fun a => (hc a).symm
    rw [hf, (PiTensorProduct.tprod ℂ).map_smul_univ, smul_smul]
    simp only [RingHom.id_apply]
  | add x y hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨r + s, add_smul _ _ _⟩

theorem whitRank_multiProd_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (ψ : AddChar k Circle) (hc : Continuous ψ)
    (h1 : ψ ≠ 1) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : ∀ a, IsSmooth (π a))
    (hr : ∀ a, Module.rank ℂ (TwJacquet (π a) (unipB k (Fin (d a))) (whitChar ψ (d a))) ≤ 1) :
    Module.rank ℂ (TwJacquet (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  obtain ⟨e⟩ := hH ψ hc h1 h N d hd X π hs
  exact e.rank_eq.le.trans (rank_piTensorProduct_le_one _ hr)

theorem whitRankStd_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k →
    GlobalTheory.BZSeg.WhitRankStd k := by
  intro k _ _ _ _ hH hR ψ hc h1 h N x hd
  exact whitRank_multiProd_le_one hH ψ hc h1 h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep)
    (fun a => (x a).2.rep.smooth)
    (fun a => hR ψ hc h1 (x a).1 (x a).2.rep.V (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)

end GlobalTheory.CompanionTheory.BZSeg

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredityStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_rank_standard_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.WhitRankStd k := by
  first | exact @GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity | exact GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity | (intros; apply GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValues
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementCapelliRecursion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementCapelliRecursion
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CapelliEigen

open Formalism.REAL Finset Polynomial GlobalTheory.CapelliNewton

theorem etr_apply_of_eigen : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (P : Polynomial ℂ) (v : V), (∀ u : ℂ, Formalism.REAL.qdet E u v = P.eval u • v) → ∀ (N : ℕ) (t : ℕ → ℂ), (∀ k < N, Formalism.REAL.etr E k v = t k • v) → Formalism.REAL.etr E N v = ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((P).comp (Polynomial.X + 1) - (P)) - (P) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * t k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) • v := by
  intro V _ _ m E hE P v hP N t ht
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) E
  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → Module.End ℂ V, ∀ w : ℂ,
      qminor E (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap (Module.End ℂ V) (m + 1) m E (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let Rc : ℕ → Module.End ℂ V := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * cm i j d * epow E (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
      (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * qminor E (Fin.succAbove j) (Fin.succAbove i) w
        * epow E (N + 1) j i = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  set Rp := polyOf m Rc φ v with hRp
  set Pq := polyOf (m + 1) c φ (etr E N v) with hPq
  have hPqe : ∀ w : ℂ, Pq.eval w = φ (qdet E w (etr E N v)) := fun w => by rw [hPq, polyOf_eval, hc]
  have hPv : ∀ w : ℂ, φ (qdet E w v) = P.eval w * φ v := fun w => by
    rw [hP, map_smul, smul_eq_mul]
  have hsq : (((-1 : ℂ) ^ N) ^ 2) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * ((P.eval (w + 1) - P.eval w) * φ v) + (-1) ^ N * Rp.eval w
      = (∑ k ∈ range N, (-1) ^ k * (w - m) ^ (N - k) * t k) * (P.eval w * φ v) + (-1) ^ N * Pq.eval w := by
    intro w
    have h1 := congrArg (fun T : Module.End ℂ V => φ (T v)) (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse (Module.End ℂ V) m E hE w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    have h2 : (qdet E w * ∑ k ∈ range (N + 1), algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
        = (∑ k ∈ range N, (-1) ^ k * (w - m) ^ (N - k) * t k) • qdet E w v
          + ((-1 : ℂ) ^ N) • qdet E w (etr E N v) := by
      have h3 : ∀ k ∈ range N, (algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
          = ((-1) ^ k * (w - m) ^ (N - k) * t k) • v := by
        intro k hk
        rw [Module.End.mul_apply, ht k (mem_range.mp hk), Module.algebraMap_end_apply, smul_smul]
      rw [Module.End.mul_apply, sum_range_succ, LinearMap.add_apply, LinearMap.sum_apply, sum_congr rfl h3,
        ← sum_smul, map_add, map_smul, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
      simp
    rw [h2] at h1
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_add (f := _), map_smul,
      LinearMap.sub_apply, map_sub, smul_eq_mul] at h1
    rw [← polyOf_eval, ← hRp, ← hPqe] at h1
    simp only [hPv] at h1
    linear_combination h1
  have hpoly : C (φ v) * ((-1 : ℂ[X]) ^ N * ((X - C (m : ℂ)) ^ (N + 1) * (P.comp (X + 1) - P)
      - P * ∑ k ∈ range N, C ((-1) ^ k * t k) * (X - C (m : ℂ)) ^ (N - k))) = Pq - Rp := by
    refine Polynomial.funext fun w => ?_
    have h1 := hrec w
    simp only [eval_mul, eval_C, eval_pow, eval_neg, eval_one, eval_sub, eval_X, eval_comp, eval_add,
      eval_finsetSum]
    have h4 : ∑ k ∈ range N, (-1) ^ k * t k * (w - m) ^ (N - k)
        = ∑ k ∈ range N, (-1) ^ k * (w - m) ^ (N - k) * t k :=
      sum_congr rfl fun k _ => by ring
    rw [h4]
    linear_combination ((-1 : ℂ) ^ N) * h1 + (Pq.eval w - Rp.eval w) * hsq
  have hco := congrArg (fun p : ℂ[X] => p.coeff (m + 1)) hpoly
  simp only [coeff_C_mul, coeff_sub] at hco
  have hPc : Pq.coeff (m + 1) = φ (etr E N v) := by
    rw [hPq, polyOf_coeff, hc1]; simp
  have hRc : Rp.coeff (m + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((polyOf_natDegree _ _ _ _).trans_lt (Nat.lt_succ_self m))
  rw [hPc, hRc, sub_zero] at hco
  rw [map_sub, map_smul, smul_eq_mul, ← hco]
  ring

end GlobalTheory.CompanionTheory.CapelliEigen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementCapelliRecursionStatement
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_element_capelli_recursion : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (P : Polynomial ℂ) (v : V), (∀ u : ℂ, Formalism.REAL.qdet E u v = P.eval u • v) → ∀ (N : ℕ) (t : ℕ → ℂ), (∀ k < N, Formalism.REAL.etr E k v = t k • v) → Formalism.REAL.etr E N v = ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((P).comp (Polynomial.X + 1) - (P)) - (P) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * t k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) • v := by
  first | exact @GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen | exact GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen | (intros; apply GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValues
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CapelliGelfand

theorem etr_eq_gelfVal_of_capelli :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V)
      (χ : Fin (m + 1) → ℂ) (v : V), Formalism.REAL.GlRel E →
      (∀ Y : ℂ, Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP χ Y • v) →
      ∀ k : ℕ, Formalism.REAL.etr E k v = GlobalTheory.Dec.gelfVal χ k • v := by
  intro V _ _ m E χ v hE hq
  have hcap : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP χ Y = ∏ s, (Y + χ s) := by
    intro Y
    rfl
  have hP : ∀ u : ℂ, Formalism.REAL.qdet E u v =
      (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))).eval u • v := by
    intro u
    have h := hq (u - (m : ℂ) / 2)
    have h1 : u - (m : ℂ) / 2 + (((m + 1 : ℕ) : ℂ) - 1) / 2 = u := by
      push_cast
      ring
    rw [h1, hcap] at h
    rw [h, Polynomial.eval_prod]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    ring
  intro k
  induction k using Nat.strong_induction_on with
  | _ N ih =>
    rw [GlobalTheory.T.trace_element_capelli_recursion V m E hE _ v hP N (fun k => GlobalTheory.Dec.gelfVal χ k) (fun k hk => ih k hk)]
    rw [GlobalTheory.T.trace_element_gelfand_polynomial_formula m χ N]

end GlobalTheory.CompanionTheory.CapelliGelfand
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValuesStatement
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_elements_act_by_gelfand_values : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V) (χ : Fin (m + 1) → ℂ) (v : V), Formalism.REAL.GlRel E → (∀ Y : ℂ, Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP χ Y • v) → ∀ k : ℕ, Formalism.REAL.etr E k v = GlobalTheory.Dec.gelfVal χ k • v := by
  first | exact @GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli | exact GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli | (intros; apply GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIff
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIff
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.SegDualPrec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section

variable (hc : ∀ x : IrrGL (k := k), x.IsCusp → (dualCl x).IsCusp)

include hc

theorem segDual_eq (Δ : Segment k) : segDual Δ =
    Segment.ofFirst ((dualCl Δ.first).nu (1 - (Δ.len : ℂ))) ((hc _ Δ.isCusp_first).nu _) Δ.len Δ.len_pos :=
  dite_eq_left (hc _ Δ.isCusp_first)

theorem first_segDual (Δ : Segment k) : (segDual Δ).first = (dualCl Δ.first).nu (1 - (Δ.len : ℂ)) := by
  rw [segDual_eq hc]; rfl

theorem len_segDual (Δ : Segment k) : (segDual Δ).len = Δ.len := by
  rw [segDual_eq hc]; rfl

variable (hn : ∀ (x : IrrGL (k := k)) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s))

include hn

theorem carrier_segDual (Δ : Segment k) : (segDual Δ).carrier = dualCl '' Δ.carrier := by
  ext x
  simp only [Set.mem_image, Segment.mem_carrier, first_segDual hc, len_segDual hc, IrrGL.nu_nu]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨_, ⟨Δ.len - 1 - a, by omega, rfl⟩, ?_⟩
    rw [hn]
    congr 1
    have h1 : a + 1 ≤ Δ.len := ha
    have h2 : ((Δ.len - 1 - a : ℕ) : ℂ) = (Δ.len : ℂ) - 1 - a := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h2]
    ring
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨Δ.len - 1 - b, by omega, ?_⟩
    rw [hn]
    congr 1
    have h1 : b + 1 ≤ Δ.len := hb
    have h2 : ((Δ.len - 1 - b : ℕ) : ℂ) = (Δ.len : ℂ) - 1 - b := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h2]
    ring

variable (hd : ∀ x : IrrGL (k := k), dualCl (dualCl x) = x)

include hd

theorem dualCl_injective : Function.Injective (dualCl : IrrGL (k := k) → IrrGL (k := k)) :=
  Function.LeftInverse.injective hd

theorem segDual_segDual (Δ : Segment k) : segDual (segDual Δ) = Δ := by
  refine Segment.ext_first ?_ (by rw [len_segDual hc, len_segDual hc])
  rw [first_segDual hc, first_segDual hc, len_segDual hc, hn, hd, IrrGL.nu_nu]
  simp

theorem linked_segDual {Δ Δ' : Segment k} (h : Δ.Linked Δ') : (segDual Δ).Linked (segDual Δ') := by
  obtain ⟨⟨Γ, hΓ⟩, h1, h2⟩ := h
  have hi := dualCl_injective hc hn hd
  refine ⟨⟨segDual Γ, ?_⟩, ?_, ?_⟩
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, carrier_segDual hc hn, hΓ, Set.image_union]
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, Set.image_subset_image_iff hi]
    exact h1
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, Set.image_subset_image_iff hi]
    exact h2

theorem precedes_segDual {Δ Δ' : Segment k} (h : Δ'.Precedes Δ) : (segDual Δ).Precedes (segDual Δ') := by
  obtain ⟨hl, j, hj, hf⟩ := h
  refine ⟨linked_segDual hc hn hd hl.symm, ?_⟩
  have hlen : Δ'.len < j + Δ.len := by
    by_contra hle
    refine hl.2.2 fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
    refine Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩
    rw [hf, IrrGL.nu_nu]
    push_cast
    rfl
  refine ⟨j + Δ.len - Δ'.len, by omega, ?_⟩
  rw [first_segDual hc, first_segDual hc, hf, hn, IrrGL.nu_nu, IrrGL.nu_nu]
  congr 1
  rw [Nat.cast_sub hlen.le]
  push_cast
  ring

theorem segDual_precedes_iff (Δ Δ' : Segment k) : (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := by
  refine ⟨fun h => ?_, precedes_segDual hc hn hd⟩
  have := precedes_segDual hc hn hd h
  rwa [segDual_segDual hc hn hd, segDual_segDual hc hn hd] at this

end

theorem segDual_precedes : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ Δ' : Segment k),
    (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := by
  intro k _ _ _ _ hA Δ Δ'
  have hadm (x : IrrGL (k := k)) : IsAdmissible x.rep :=
    hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr
  have hirr (x : IrrGL (k := k)) : (contra x.rep).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible
      (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (hadm x) x.2.rep.irr
  have hdual (x : IrrGL (k := k)) :
      dualCl x = IrrGL.of (contra x.rep) (isSmooth_contra _) (hirr x) :=
    dite_eq_left (hirr x)
  have hc (x : IrrGL (k := k)) (hx : x.IsCusp) : (dualCl x).IsCusp := by
    rw [hdual x, IrrGL.isCusp_of]
    exact ⟨hx.1, GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k x.1 _ _
      (GlobalTheory.CompanionTheory.DualCusp.isSupercuspidal_contra
        (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (hadm x)
        (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k x.1 _ _ hx.2))⟩
  have hn (x : IrrGL (k := k)) (s : ℂ) : dualCl (x.nu s) = (dualCl x).nu (-s) := by
    have hs : IsSmoothChar (absPow k s) := isSmoothChar_absPow s
    have hs_neg : IsSmoothChar (absPow k (-s)) := isSmoothChar_absPow (-s)
    have hmul : absPow k s * absPow k (-s) = 1 := by
      rw [absPow_neg, mul_inv_cancel]
    obtain ⟨e⟩ := GlobalTheory.CompanionTheory.ZcDual.nonempty_equiv_contra_twist
      hA x.rep x.2.rep.smooth x.2.rep.irr hs hs_neg hmul
    rw [hdual (x.nu s), hdual x]
    change IrrGL.of (contra (x.nu s).rep) _ _ =
      (IrrGL.of (contra x.rep) _ _).tw (absPow k (-s)) hs_neg
    rw [IrrGL.tw_of]
    exact IrrGL.of_eq_of.mpr ⟨(GlobalTheory.ContraRefl.contraEquiv (x.twEquiv _ hs)).trans e.symm⟩
  have hd (x : IrrGL (k := k)) : dualCl (dualCl x) = x := by
    rw [hdual x, hdual]
    conv_rhs => rw [← IrrGL.of_rep x]
    exact IrrGL.of_eq_of.mpr ⟨
      (GlobalTheory.ContraRefl.contraEquiv (IrrGL.equivOf (contra x.rep) _ _)).trans
        (GlobalTheory.ContraRefl.evEquiv
          (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (hadm x)).symm⟩
  exact segDual_precedes_iff hc hn hd Δ Δ'

end GlobalTheory.CompanionTheory.SegDualPrec
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIffStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_dual_precedes_iff : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ Δ' : Segment k), (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegDualPrec.segDual_precedes | exact GlobalTheory.CompanionTheory.SegDualPrec.segDual_precedes | (intros; apply GlobalTheory.CompanionTheory.SegDualPrec.segDual_precedes <;> assumption)
end
end
