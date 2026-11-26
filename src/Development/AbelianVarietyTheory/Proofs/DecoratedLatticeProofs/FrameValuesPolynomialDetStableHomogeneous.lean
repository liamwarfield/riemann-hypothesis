module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentities
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramUnimodular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombination
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KJInf.ValPol

variable {ι : Type} [Fintype ι] {a : ℕ}

theorem evalAt_eq (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y F = MvPolynomial.eval (fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) F := rfl

theorem evalAt_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    evalAt y (Formalism.L2.Ker.frDet ℂ a τ) = (y τ).det := by
  rw [evalAt_eq, Formalism.L2.Ker.frDet, RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply]

theorem evalAt_mul_prod (y : ι → Matrix (Fin a) (Fin a) ℂ) (P : PY ι a) (n : ι → ℕ) :
    evalAt y (P * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ n τ) = evalAt y P * ∏ τ, (y τ).det ^ n τ := by
  rw [evalAt_eq, map_mul, map_prod, ← evalAt_eq]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, ← evalAt_eq, evalAt_frDet]

theorem fnOf_one_apply {G : ι → Matrix (Fin a) (Fin a) ℂ} (s : ι → ℤ) (P : PY ι a) (y : Frames G) :
    fnOf G s 1 P y = (∏ τ, (y.1 τ).det ^ s τ) * evalAt y.1 P := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, one_mul, evalAt]

theorem evalAt_lft (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [evalAt, lft]
  | add p q hp hq => simp only [evalAt, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p v hp =>
    simp only [evalAt, map_mul] at *
    rw [hp]
    simp [lft, Matrix.mul_apply]

theorem shift_eq {G : ι → Matrix (Fin a) (Fin a) ℂ} (lam : ι → DomWeight a) {n : ι → ℕ} {s : ι → ℤ}
    (hns : ∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) (P : PY ι a) (y : Frames G) :
    evalAt y.1 (P * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ n τ) * ∏ τ, (y.1 τ).det ^ (-s τ) =
      fnOf G (shiftOf lam) 1 P y := by
  rw [evalAt_mul_prod, fnOf_one_apply, mul_assoc, mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : (y.1 τ).det ≠ 0 := (y.2 τ).ne_zero
  rw [← zpow_natCast, ← zpow_add₀ hd, hns τ]
  congr 1
  ring

theorem mem_valC_iff (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (n : ι → ℕ) (s : ι → ℤ)
    (hns : ∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) (Φ : Frames G → ℂ) :
    Φ ∈ ValC G lam ↔ ∃ F ∈ Vn lam n, ∀ y, Φ y = evalAt y.1 F * ∏ τ, (y.1 τ).det ^ (-s τ) := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨_, ⟨P, hP, rfl⟩, fun y => (shift_eq lam hns P y).symm⟩
  · rintro ⟨F, ⟨P, hP, rfl⟩, hΦ⟩
    refine ⟨P, hP, funext fun y => ?_⟩
    rw [hΦ y]
    exact (shift_eq lam hns P y).symm

def nOf (lam : ι → DomWeight a) : ι → ℕ := fun τ => (shiftOf lam τ).toNat

def sOf (lam : ι → DomWeight a) : ι → ℤ := fun τ => (nOf lam τ : ℤ) - shiftOf lam τ

theorem nOf_eq (lam : ι → DomWeight a) (τ : ι) : (nOf lam τ : ℤ) = shiftOf lam τ + sOf lam τ := by
  simp [sOf]

theorem valC_eq_map (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) :
    ValC G lam = (Vn lam (nOf lam)).map (fnOf G (fun τ => -sOf lam τ) 1) := by
  ext Φ
  rw [mem_valC_iff G lam _ _ (nOf_eq lam)]
  constructor
  · rintro ⟨F, hF, hΦ⟩
    refine ⟨F, hF, funext fun y => ?_⟩
    rw [hΦ y, fnOf_one_apply, mul_comm]
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, hF, fun y => by rw [fnOf_one_apply, mul_comm]⟩

theorem finiteDimensional_valC (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) :
    FiniteDimensional ℂ (ValC G lam) := by
  haveI := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam (nOf lam)).1
  rw [valC_eq_map]
  infer_instance

theorem valC_stable (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (Φ : Frames G → ℂ) (hΦ : Φ ∈ ValC G lam)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (Φ' : Frames G → ℂ) (hΦ' : ∀ y y', IsTr g y y' → Φ' y = Φ y') (hg : IsInv g) :
    Φ' ∈ ValC G lam := by
  obtain ⟨F, hF, hΦF⟩ := (mem_valC_iff G lam _ _ (nOf_eq lam) Φ).1 hΦ
  rw [mem_valC_iff G lam _ _ (nOf_eq lam)]
  refine ⟨(∏ τ, (g τ).det ^ (-sOf lam τ)) • lft g F,
    Submodule.smul_mem _ _ ((GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam (nOf lam)).2 g F hF), fun y => ?_⟩
  let y' : Frames G := ⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩
  rw [hΦ' y y' (fun τ => rfl), hΦF y']
  have e : evalAt y.1 ((∏ τ, (g τ).det ^ (-sOf lam τ)) • lft g F) =
      (∏ τ, (g τ).det ^ (-sOf lam τ)) * evalAt (fun τ => g τ * y.1 τ) F := by
    rw [evalAt_eq, MvPolynomial.smul_eval, ← evalAt_eq, evalAt_lft]
  rw [e]
  simp only [y', Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

theorem natW_anti' (l : DomWeight a) : Antitone l.natW := fun i j h =>
  Int.toNat_le_toNat (by have := l.anti h; omega)

theorem isHomogeneous_of_mem_delSq (l : DomWeight a) {f : MvPolynomial (Fin a × Fin a) ℂ} (hf : f ∈ delSq ℂ a l) :
    f.IsHomogeneous (∑ r, l.natW r) := by
  have h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f l.natW :=
    (Formalism.GradedWeylDivisibility.weylLeDual ℂ a a le_rfl l.natW (natW_anti' l) hf).1
  intro m hm
  rw [← h hm]
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Formalism.GradedWeylDivisibility.colW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply]

theorem eval_smul_of_isHomogeneous {σ : Type} {f : MvPolynomial σ ℂ} {d : ℕ} (hf : f.IsHomogeneous d)
    (c : ℂ) (v : σ → ℂ) : MvPolynomial.eval (c • v) f = c ^ d * MvPolynomial.eval v f := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (MvPolynomial.mem_support_iff.1 hm)
  rw [← this, Finsupp.degree_apply]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem sum_w_eq (l : DomWeight a) : ∑ i, l.w i = ∑ i, ((l.natW i : ℕ) : ℤ) + (a : ℤ) * l.detShift := by
  have h : ∀ i, ((l.natW i : ℕ) : ℤ) = l.w i - l.detShift := by
    intro i
    have hpos : 0 < a := Fin.pos i
    have hle : l.w ⟨a - 1, by omega⟩ ≤ l.w i := l.anti (Fin.le_iff_val_le_val.2 (by simp; omega))
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hpos]
    exact Int.toNat_of_nonneg (by omega)
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem evalAt_scale_cSpan (lam : ι → DomWeight a) (z : ι → ℂ) (y y' : ι → Matrix (Fin a) (Fin a) ℂ)
    (hy : ∀ τ, y' τ = z τ • y τ) (P : PY ι a) (hP : P ∈ CSpan lam) :
    evalAt y' P = (∏ τ, z τ ^ (∑ i, (lam τ).natW i)) * evalAt y P := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    simp only [evalAt_eq, ten, map_prod, MvPolynomial.eval_rename]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have e : ((fun x : ι × Fin a × Fin a => y' x.1 x.2.1 x.2.2) ∘ Prod.mk τ) =
        z τ • ((fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) ∘ Prod.mk τ) := by
      funext x
      simp [hy τ]
    rw [e, eval_smul_of_isHomogeneous (isHomogeneous_of_mem_delSq (lam τ) (hf τ))]
  | zero => simp [evalAt_eq]
  | add p q _ _ hp hq => simp only [evalAt_eq, map_add (f := _)] at *; rw [hp, hq]; ring
  | smul c p _ hp => simp only [evalAt_eq, MvPolynomial.smul_eval] at *; rw [hp]; ring

theorem valC_homog (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (Φ : Frames G → ℂ) (hΦ : Φ ∈ ValC G lam)
    (z : ι → ℂ) (y y' : Frames G) (hy : ∀ τ, y'.1 τ = z τ • y.1 τ) :
    Φ y' = (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * Φ y := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have : y' = y := Subtype.ext (funext fun τ => Subsingleton.elim _ _)
    simp [this]
  obtain ⟨P, hP, rfl⟩ := hΦ
  rw [fnOf_one_apply, fnOf_one_apply, evalAt_scale_cSpan lam z y.1 y'.1 hy P hP]
  have hz : ∀ τ, z τ ≠ 0 := by
    intro τ h0
    have hne := (y'.2 τ).ne_zero
    haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
    rw [hy τ, h0, zero_smul, Matrix.det_zero] at hne
    exact hne rfl
  have per : ∀ (zz d : ℂ) (sh : ℤ) (deg : ℕ) (W : ℤ), zz ≠ 0 → W = deg + a * sh →
      (zz ^ a * d) ^ sh * zz ^ deg = zz ^ W * d ^ sh := by
    intro zz d sh deg W hz hW
    rw [mul_zpow, ← zpow_natCast zz a, ← _root_.zpow_mul, hW, zpow_add₀ hz, zpow_natCast]
    ring
  have key : (∏ τ, (y'.1 τ).det ^ shiftOf lam τ) * ∏ τ, z τ ^ (∑ i, (lam τ).natW i) =
      (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * ∏ τ, (y.1 τ).det ^ shiftOf lam τ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hy τ, Matrix.det_smul, Fintype.card_fin]
    exact per _ _ _ _ _ (hz τ) (by rw [sum_w_eq, Nat.cast_sum]; rfl)
  linear_combination (evalAt y.1 P) * key

end GlobalTheory.KJInf.ValPol

theorem GlobalTheory.KJInf.valC_poly : ∀ (ι : Type) [Fintype ι] (a : ℕ) (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a), (∀ (n : ι → ℕ) (s : ι → ℤ), (∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) → ∀ Φ : Frames G → ℂ, Φ ∈ ValC G lam ↔ ∃ F ∈ Vn lam n, ∀ y, Φ y = evalAt y.1 F * ∏ τ, (y.1 τ).det ^ (-s τ)) ∧ FiniteDimensional ℂ (ValC G lam) ∧ (∀ Φ ∈ ValC G lam, ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, ∀ Φ' : Frames G → ℂ, (∀ y y', IsTr g y y' → Φ' y = Φ y') → IsInv g → Φ' ∈ ValC G lam) ∧ ∀ Φ ∈ ValC G lam, ∀ (z : ι → ℂ) (y y' : Frames G), (∀ τ, y'.1 τ = z τ • y.1 τ) → Φ y' = (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * Φ y := by
  intro ι _ a G lam
  refine ⟨fun n s hns Φ => GlobalTheory.KJInf.ValPol.mem_valC_iff G lam n s hns Φ,
    GlobalTheory.KJInf.ValPol.finiteDimensional_valC G lam,
    fun Φ hΦ g Φ' hΦ' hg => GlobalTheory.KJInf.ValPol.valC_stable G lam Φ hΦ g Φ' hΦ' hg,
    fun Φ hΦ z y y' hy => GlobalTheory.KJInf.ValPol.valC_homog G lam Φ hΦ z y y' hy⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_values_polynomial_det_stable_homogeneous : ∀ (ι : Type) [Fintype ι] (a : ℕ) (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a), (∀ (n : ι → ℕ) (s : ι → ℤ), (∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) → ∀ Φ : Frames G → ℂ, Φ ∈ ValC G lam ↔ ∃ F ∈ Vn lam n, ∀ y, Φ y = evalAt y.1 F * ∏ τ, (y.1 τ).det ^ (-s τ)) ∧ FiniteDimensional ℂ (ValC G lam) ∧ (∀ Φ ∈ ValC G lam, ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, ∀ Φ' : Frames G → ℂ, (∀ y y', IsTr g y y' → Φ' y = Φ y') → IsInv g → Φ' ∈ ValC G lam) ∧ ∀ Φ ∈ ValC G lam, ∀ (z : ι → ℂ) (y y' : Frames G), (∀ τ, y'.1 τ = z τ • y.1 τ) → Φ y' = (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * Φ y := by
  first | exact @GlobalTheory.KJInf.valC_poly | exact GlobalTheory.KJInf.valC_poly | (intros; apply GlobalTheory.KJInf.valC_poly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntertwiningStabilizerTranslateScalar
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.IkStab

variable {D : D7}

theorem exists_valuation_adapted_index {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) {p : GA D T} (hp : p ∈ stab d) :
    ∃ (β : Mx D t T'.rank) (g : GA D T'), mt T p ⬝ d.j0 = d.jX ⬝ β + d.j0 ⬝ mt T' g := by
  obtain ⟨α, hα⟩ := hp
  have hu := mt_unitary T p
  have h1 : adj (mt T p ⬝ d.jX) ⬝ (gA T ⬝ (mt T p ⬝ d.j0)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ hu, d.wittDecomp_gram_X_anisotropic]
  have h2 : d.pY ⬝ (mt T p ⬝ d.j0) = 0 := by
    rw [hα, adj_mul, Matrix.mul_assoc] at h1
    have h3 := congrArg (fun z : Mx D t T'.rank => adj (α⁻¹).1 ⬝ z) h1
    simp only [← Matrix.mul_assoc (adj (α⁻¹).1), ← adj_mul, Units.mul_inv, adj_one, Matrix.one_mul,
      Matrix.mul_zero] at h3
    rw [d.pY_eq, Matrix.mul_assoc, h3]
  have h4 : mt T p ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt T p ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt T p ⬝ d.j0)) := by
    conv_lhs => rw [← Matrix.one_mul (mt T p ⬝ d.j0), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_zero, add_zero]
  have h5 : adj (mt T p ⬝ d.j0) ⬝ (gA T ⬝ (mt T p ⬝ d.j0)) = gA T' := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ hu, d.gram_00]
  generalize d.pX ⬝ (mt T p ⬝ d.j0) = β at h4
  generalize d.p0 ⬝ (mt T p ⬝ d.j0) = g at h4
  rw [h4] at h5
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₃ d.gram_XX,
    cancel₃ d.wittDecomp_gram_X_anisotropic, cancel₃ d.gram_0X, cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    add_zero] at h5
  exact ⟨β, ofMat T' g h5, h4⟩

end GlobalTheory.RegSch.IkStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiTContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.KUni

variable {D : D7} {V : HSp D}

theorem inv_eq {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ = Bᴴ * G :=
  Matrix.inv_eq_left_inv hB

theorem mul_inv' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B * B⁻¹ = 1 := by
  rw [inv_eq hB]; exact mul_eq_one_comm.mp hB

theorem inv_mul' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ * B = 1 := by
  rw [inv_eq hB]; exact hB

theorem gB {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : Gᴴ * B * Bᴴ = 1 := by
  have h := congrArg Matrix.conjTranspose hB
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
  exact mul_eq_one_comm.mp h

theorem conj_unitary {G B g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, inv_eq hB]
  have e : (Bᴴ * G * g * B)ᴴ * (Bᴴ * G * g * B) = Bᴴ * gᴴ * (Gᴴ * B * Bᴴ) * G * g * B := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, gB hB, Matrix.mul_one]
  calc Bᴴ * gᴴ * G * g * B = Bᴴ * (gᴴ * G * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hB]

theorem back_unitary {G B u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1)
    (hu : u ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) : (B * u * B⁻¹)ᴴ * G * (B * u * B⁻¹) = G := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  rw [inv_eq hB]
  have e : (B * u * (Bᴴ * G))ᴴ * G * (B * u * (Bᴴ * G)) = Gᴴ * B * uᴴ * (Bᴴ * G * B) * u * Bᴴ * G := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, hB, Matrix.mul_one]
  calc Gᴴ * B * uᴴ * u * Bᴴ * G = Gᴴ * B * (uᴴ * u) * Bᴴ * G := by simp only [Matrix.mul_assoc]
    _ = (Gᴴ * B * Bᴴ) * G := by rw [hu, Matrix.mul_one]
    _ = G := by rw [gB hB, Matrix.one_mul]


open Formalism.IndefR.Eqv in
theorem psiT_continuous (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have hsum : ∀ x : AE D, psiT D τ x = ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) *
      psiT D τ (basAF D c) := by
    intro x
    conv_lhs => rw [← (basAF D).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, map_mul]
  have hc : ∀ c, Continuous fun x : AE D => (basAF D).repr x c := fun c =>
    (continuous_apply c).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
  have halg : Continuous fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a) := by
    have e : (fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)) =
        fun a => thetaC D τ ((fstA D.host.F a) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      funext a
      simp only [psiT, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, infPart,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [e]
    exact ((isInfFam_thetaC D) τ).2.comp continuous_fst
  have hfun : (⇑(psiT D τ) : AE D → ℂ) = fun x => ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D)
      ((basAF D).repr x c)) * psiT D τ (basAF D c) := funext hsum
  rw [hfun]
  exact continuous_finsetSum _ fun c _ => (halg.comp (hc c)).mul continuous_const

open Formalism.IndefR.Eqv in
theorem inB_eq (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) (τ : D.what₂.Tau) :
    inB (thetaC D) V B g τ = (B τ)⁻¹ * infMat D.sp.cm.sig V.gram (thetaC D τ) g * B τ := by
  rw [infMat_thetaC]; rfl

end GlobalTheory.SeeSaw.KUni


open GlobalTheory.SeeSaw.KUni Formalism.IndefR.Eqv in
theorem GlobalTheory.SeeSaw.ontoUni_inB : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsInfFam θ → (∀ τ, (B τ)ᴴ * gramAt D V τ * B τ = 1) → OntoUni fun k : GinfC V => inB θ V B k.1 := by
  intro D θ V B hθ hB
  obtain rfl := eq_thetaC D hθ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun τ => ?_
    have hm : Continuous fun g : GA D V => mt V g := Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous fun k : GinfC V => (mt V k.1).map (psiT D τ) :=
      (hm.comp continuous_subtype_val).matrix_map (psiT_continuous τ)
    exact (continuous_const.matrix_mul h1).matrix_mul continuous_const
  · intro k k' τ
    rw [inB_eq, inB_eq, inB_eq]
    simp only [Subgroup.coe_mul, infMat_thetaC, matA_mul, Matrix.map_mul]
    calc (B τ)⁻¹ * ((matA D V k).map (psiT D τ) * (matA D V k').map (psiT D τ)) * B τ
        = (B τ)⁻¹ * (matA D V k).map (psiT D τ) * (B τ * (B τ)⁻¹) * (matA D V k').map (psiT D τ) * B τ := by
          rw [mul_inv' (hB τ)]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  · intro k τ
    rw [inB_eq]
    exact conj_unitary (hB τ) (infMat_unitary' D V k.1 τ)
  · intro u hu
    have hgs : IsUnitFam D V fun τ => B τ * u τ * (B τ)⁻¹ := fun τ => back_unitary (hB τ) (hu τ)
    refine ⟨⟨famH D V _ hgs, famH_mem_GinfC D V _ hgs⟩, ?_⟩
    funext τ
    rw [inB_eq, infMat_famH]
    calc (B τ)⁻¹ * (B τ * u τ * (B τ)⁻¹) * B τ = ((B τ)⁻¹ * B τ) * u τ * ((B τ)⁻¹ * B τ) := by
          simp only [Matrix.mul_assoc]
      _ = u τ := by rw [inv_mul' (hB τ), Matrix.one_mul, Matrix.mul_one]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjStabilizersSelfDualLatticesUnramified
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SelfDualStabConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_sq_conj_sub (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (x : 𝓞 E) (d : 𝓞 F), d ∉ v.asIdeal ∧ algebraMap F E d = ((x : E) - σ x) ^ 2 := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have := v.isMaximal
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (E ≃ₐ[F] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcard
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => GlobalTheory.LFun.InertChart.conj_ne h fun x => congrArg (fun t : E ≃ₐ[F] E => t x) hs
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, s • x - x ∉ Q := by
    by_contra hn
    push Not at hn
    have hs : s ∈ Q.inertia (E ≃ₐ[F] E) := AddSubgroup.mem_inertia.2 hn
    rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
    exact hs1 hs
  have hfix : ∀ t : E ≃ₐ[F] E, t (((x : E) - σ x) ^ 2) = ((x : E) - σ x) ^ 2 := fun t => by
    have hc : Nat.card (E ≃ₐ[F] E) = 2 := (IsGalois.card_aut_eq_finrank F E).trans h.2.2.1
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hc
    by_cases ht : t = 1
    · rw [ht]; rfl
    · rw [(hu t ht).trans (hu s hs1).symm]
      change σ _ = _
      rw [map_pow, map_sub, hσ]; ring
  obtain ⟨d, hd⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  have e : (((s • x - x) ^ 2 : 𝓞 E) : E) = ((x : E) - σ x) ^ 2 := by
    change (σ x - (x : E)) ^ 2 = _
    ring
  have hi : IsIntegral ℤ d := by
    rw [← isIntegral_algebraMap_iff (B := E), hd, ← e]
    exact RingOfIntegers.isIntegral_coe _
  refine ⟨x, ⟨d, hi⟩, fun hm => hx (hQ.isPrime.mem_of_pow_mem 2 ?_), hd⟩
  have : (s • x - x) ^ 2 = algebraMap (𝓞 F) (𝓞 E) ⟨d, hi⟩ := RingOfIntegers.ext (e.trans hd.symm)
  rw [this]
  rwa [hQv.over] at hm

def conjInt (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : intLoc F E v →+* intLoc F E v :=
  (sigR (Fv F v) σ).restrict _ _ fun _ => sigR_mem_intLoc σ

theorem exists_isUnit_sub_conj (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E))
    (v : HeightOneSpectrum (𝓞 F)) : ∃ ω : intLoc F E v, IsUnit (ω - conjInt σ v ω) := by
  obtain ⟨x, d, hd, e⟩ := exists_sq_conj_sub h hU v
  have hd0 : (d : F) ≠ 0 := fun h0 => hd (by
    rw [show d = 0 from RingOfIntegers.coe_injective (by simpa using h0)]; exact zero_mem _)
  have ha : algebraMap F (Fv F v) (d : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : v.valuation F (d : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 hd
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (d : F)⁻¹
    exact le_of_eq (h2.trans (by rw [map_inv₀, h1, inv_one]))
  refine ⟨⟨_, tmul_mem_intLoc (one_mem _) x⟩, (isUnit_pow_iff two_ne_zero).1
    (IsUnit.of_mul_eq_one ⟨_, tmul_mem_intLoc ha 1⟩ (Subtype.ext ?_))⟩
  change (inclR (Fv F v) (x : E) - inclR (Fv F v) (σ x)) ^ 2 * (algebraMap F (Fv F v) (d : F)⁻¹ ⊗ₜ[F] (1 : E)) = 1
  rw [← map_sub, ← map_pow, ← e, Algebra.algebraMap_eq_smul_one (d : F)⁻¹, TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one]
  change inclR (Fv F v) _ * inclR (Fv F v) _ = 1
  rw [← map_mul, ← map_mul, mul_inv_cancel₀ hd0, map_one, map_one]

theorem exists_norm (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    {n : ℕ} {B : Matrix (Fin n) (Fin n) (intLoc F E v)} (hB : cT (conjInt σ v) B = B) (hu : IsUnit B) :
    ∃ u : GL (Fin n) (intLoc F E v), cT (conjInt σ v) u.1 * u.1 = B := by
  let O := intLoc F E v
  let _ := (GlobalTheory.Orb.intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) O := GlobalTheory.Orb.finite_intLocMap v
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing (v.adicCompletionIntegers F) O
  let s : O →+* O := conjInt σ v
  have hs : ∀ y : O, s (s y) = y := fun y =>
    Subtype.ext (GlobalTheory.Doubling.sigR_invol (GlobalTheory.LFun.InertChart.conj_conj h) y.1)
  have hk : ∀ c, s (algebraMap (v.adicCompletionIntegers F) O c) = algebraMap (v.adicCompletionIntegers F) O c :=
    fun c => Subtype.ext (by
      change sigR (Fv F v) σ ((c : Fv F v) ⊗ₜ[F] (1 : E)) = (c : Fv F v) ⊗ₜ[F] (1 : E)
      simp [sigR])
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).map (algebraMap (v.adicCompletionIntegers F) O)
  have hI : I ≤ I.comap s := Ideal.map_le_iff_le_comap.2 fun c hc => by
    rw [Ideal.mem_comap, Ideal.mem_comap, hk]
    exact Ideal.mem_map_of_mem _ hc
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hs
    (GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X O I s hs (fun y hy => hI hy) (exists_isUnit_sub_conj h hU v)) hB hu
  have h2 : IsUnit (Polynomial.aeval B p) := isUnit_of_mul_isUnit_right (hp ▸ hu)
  exact ⟨h2.unit, hp⟩

theorem cT_mul {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} (P Q : Matrix (Fin n) (Fin n) A) :
    cT s (P * Q) = cT s Q * cT s P := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} : cT s (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem exists_orthonormal_frame (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} (hL : IsSelfDualAt σ J L v) :
    ∃ b : GL (Fin n) (Fv F v ⊗[F] E), cT (sigR _ σ) b.1 * JR (Fv F v) J * b.1 = 1 ∧
      ∀ y, (∀ i, y i ∈ intLoc F E v) ↔ b.1 *ᵥ y ∈ latLoc F L v := by
  obtain ⟨a₀, ha₀⟩ := Frames.exists_isLatticeFrame (F := F) L
  have ha := ha₀ v
  generalize bc (compFin F E v) a₀ = a at ha
  have hσ := GlobalTheory.Doubling.sigR_invol (R := Fv F v) (GlobalTheory.LFun.InertChart.conj_conj h)
  have hJu : IsUnit (JR (F := F) (Fv F v) J) := (Matrix.isUnit_iff_isUnit_det _).2 (GlobalTheory.Doubling.isUnit_det_JR hJ.2)
  have hJh : cT (sigR _ σ) (JR (F := F) (Fv F v) J) = JR (Fv F v) J := by
    ext i j; exact congrArg (fun x => (1 : Fv F v) ⊗ₜ[F] x) (hJ.1 i j)
  have hau : IsUnit (cT (sigR _ σ) a.1) := IsUnit.of_mul_eq_one (cT (sigR _ σ) (a⁻¹).1) (by
    rw [← cT_mul, Units.inv_mul, cT_one])
  obtain ⟨H, hH⟩ := (hau.mul hJu).mul a.isUnit
  obtain ⟨h1, h2⟩ := GlobalTheory.StdUnn.Unimod.gram_int (sigR _ σ) (intLoc F E v) (fun _ => sigR_mem_intLoc σ)
    (JR (Fv F v) J) a.1 (a⁻¹).1 (H⁻¹).1 (fun y => y ∈ latLoc F L v) a.mul_inv (hH ▸ H.mul_inv) ha
    (fun y => SetLike.ext_iff.1 hL y)
  let ι := (intLoc F E v).subtype
  have hinj : ∀ {M N : Matrix (Fin n) (Fin n) (intLoc F E v)}, M.map ι = N.map ι → M = N :=
    fun e => Matrix.map_injective Subtype.val_injective e
  have hcT : ∀ M : Matrix (Fin n) (Fin n) (intLoc F E v), (cT (conjInt σ v) M).map ι = cT (sigR _ σ) (M.map ι) :=
    fun _ => rfl
  let B : Matrix (Fin n) (Fin n) (intLoc F E v) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let B' : Matrix (Fin n) (Fin n) (intLoc F E v) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have eB : B.map ι = cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1 := rfl
  obtain ⟨u, hu⟩ := exists_norm h hU v (B := B)
    (hinj (by rw [hcT, eB, cT_mul, cT_mul, hJh, GlobalTheory.UnitaryDoubleCoset.cT_cT hσ, Matrix.mul_assoc]))
    (IsUnit.of_mul_eq_one B' (hinj (by
      rw [Matrix.map_mul, eB, ← hH, Matrix.map_one _ (map_zero ι) (map_one ι)]; exact H.mul_inv)))
  have hu' : cT (sigR _ σ) (bc ι u).1 * (bc ι u).1 = cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1 := by
    rw [← eB, ← hu, Matrix.map_mul]; rfl
  have hm : ∀ (k : GL (Fin n) (intLoc F E v)) (y : Fin n → Fv F v ⊗[F] E), (∀ i, y i ∈ intLoc F E v) →
      ∀ i, ((bc ι k).1 *ᵥ y) i ∈ intLoc F E v := fun k y hy i => by
    rw [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (k.1 i j).2 (hy j)
  refine ⟨a * (bc ι u)⁻¹, ?_, fun y => ?_⟩
  · have : cT (sigR _ σ) (a * (bc ι u)⁻¹).1 * JR (Fv F v) J * (a * (bc ι u)⁻¹).1 =
        cT (sigR _ σ) ((bc ι u)⁻¹).1 * (cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1) * ((bc ι u)⁻¹).1 := by
      simp only [Units.val_mul, cT_mul, Matrix.mul_assoc]
    rw [this, ← hu', ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul, Units.mul_inv]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha]
    refine ⟨fun hy => by rw [← map_inv]; exact hm _ y hy, fun hy => ?_⟩
    have := hm u _ hy
    rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this

theorem exists_conj_stabLoc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    IsHermND σ J → ∀ (L L' : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → Submodule.IsFullLattice E L' →
    ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt σ J L v → IsSelfDualAt σ J L' v →
    ∃ g : GLoc σ J v, ∀ k : GLoc σ J v, k ∈ stabLoc σ J L' v ↔ g⁻¹ * k * g ∈ stabLoc σ J L v := by
  intro F E _ _ _ _ _ σ h hU n J hJ L L' _ _ v hL hL'
  obtain ⟨b, hb, fb⟩ := exists_orthonormal_frame h hU hJ L hL
  obtain ⟨c, hc, fc⟩ := exists_orthonormal_frame h hU hJ L' hL'
  have hg : cT (sigR _ σ) (c * b⁻¹).1 * JR (Fv F v) J * (c * b⁻¹).1 = JR (Fv F v) J := by
    have : cT (sigR _ σ) (c * b⁻¹).1 * JR (Fv F v) J * (c * b⁻¹).1 =
        cT (sigR _ σ) (b⁻¹).1 * (cT (sigR _ σ) c.1 * JR (Fv F v) J * c.1) * (b⁻¹).1 := by
      simp only [Units.val_mul, cT_mul, Matrix.mul_assoc]
    rw [this, hc, ← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul,
      Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let g : GLoc σ J v := ⟨c * b⁻¹, hg⟩
  have eg : matHom _ σ J g = c * b⁻¹ := rfl
  have hm : ∀ y, y ∈ latLoc F L v ↔ (matHom _ σ J g).1 *ᵥ y ∈ latLoc F L' v := fun y => by
    rw [eg, Units.val_mul, ← Matrix.mulVec_mulVec, ← fc, fb, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hact : ∀ (p q : GLoc σ J v) y,
      (matHom _ σ J p).1 *ᵥ ((matHom _ σ J q).1 *ᵥ y) = (matHom _ σ J (p * q)).1 *ᵥ y := fun p q y => by
    rw [Matrix.mulVec_mulVec, map_mul, Units.val_mul]
  refine ⟨g, fun k => ?_⟩
  rw [mem_stabLoc, mem_stabLoc]
  refine ⟨fun hk y => ?_, fun hk y => ?_⟩
  · rw [hm, hm, hk, hact, hact, ← mul_assoc, mul_inv_cancel_left]
  · have := hk ((matHom _ σ J g⁻¹).1 *ᵥ y)
    rwa [hm, hm, hact, hact, hact, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec, mul_assoc,
      mul_inv_cancel_right, mul_inv_cancel_left] at this

end GlobalTheory.SelfDualStabConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanIn
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanIn
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CartanPt

variable {R : Type} [CommRing R] {n : ℕ}

theorem block_matrix_map {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4; rw [← Matrix.fromBlocks_map]; rfl

theorem blkJ_mul : (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  have h : Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) R) 0 0 (-1) = (-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]
  rw [h]
  change -((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = _
  rw [Matrix.submatrix_one_equiv]

theorem blkJ_transpose : (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0)ᵀ = -blk4 0 1 (-1) 0 := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.transpose_neg]
  change _ = (-(Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)).submatrix _ _
  rw [Matrix.fromBlocks_neg, neg_zero, neg_neg]

theorem blkJ_map {S : Type} [CommRing S] (f : R →+* S) :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map f = blk4 0 1 (-1) 0 := by
  rw [block_matrix_map, Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f) (map_one f),
    Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]

def mixJ (n : ℕ) (a j : R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  a • (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) + j • blk4 0 1 (-1) 0

theorem mixJ_mul (a j a' j' : R) :
    mixJ n a j * mixJ n a' j' = mixJ n (a * a' - j * j') (a * j' + j * a') := by
  simp only [mixJ, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, blkJ_mul]
  module

theorem mixJ_one : mixJ n (1 : R) 0 = 1 := by simp [mixJ]

theorem mixJ_J : mixJ n (0 : R) 1 = blk4 0 1 (-1) 0 := by simp [mixJ]

theorem mixJ_map {S : Type} [CommRing S] (f : R →+* S) (a j : R) :
    (mixJ n a j).map f = mixJ n (f a) (f j) := by
  unfold mixJ
  rw [← blkJ_map f, ← Matrix.map_one f (map_zero f) (map_one f)]
  ext p q
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul]

theorem mixJ_transpose (a j : R) : (mixJ n a j)ᵀ = mixJ n a (-j) := by
  simp [mixJ, Matrix.transpose_add, Matrix.transpose_smul, blkJ_transpose]

theorem cT_mixJ (σ : R →+* R) (a j : R) : Formalism.UG.cT σ (mixJ n a j) = mixJ n (σ a) (-σ j) := by
  rw [Formalism.UG.cT, mixJ_map, mixJ_transpose]

theorem phase (A B t : ℂ) (hB : B ≠ 0) (h1 : A * B * conj B = t) (h2 : A * conj A = 4) :
    A * (1 / 2) = t / (‖t‖ : ℂ) := by
  have hA : ‖A‖ = 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖A‖ ^ 2 = 2 ^ 2 := by
      have : ‖A‖ ^ 2 = 4 := by exact_mod_cast h2
      linarith
    exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 h3
  have hn : (‖B‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hB
  have ht : ‖t‖ = 2 * ‖B‖ ^ 2 := by
    rw [← h1, norm_mul, norm_mul, Complex.norm_conj, hA]; ring
  rw [ht, ← h1, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp

theorem four_iff {S : Type} [CommRing S] (f : R →+* S) (z : R) : f (z - 4) = 0 ↔ f z = 4 := by
  rw [map_sub, map_ofNat, sub_eq_zero]

theorem four_left {S : Type} [CommRing S] (f : R →+* S) {e : R} (z : R) (h : f e = 0) : f (e * (z - 4)) = 0 := by
  rw [map_mul, h, zero_mul]

theorem four_right {S : Type} [CommRing S] (f : R →+* S) (e : R) {z : R} (h : f z = 4) : f (e * (z - 4)) = 0 := by
  rw [map_mul, (four_iff f z).2 h, mul_zero]

theorem alg_phase (c : R →+* R) (hc : ∀ z, c (c z) = z) {e h m : R} {u ε : Rˣ} (he : e * e = e) (hce : c e = e)
    (hε : (ε : R) * u * c u = m) (hm : c m = -m) (hh : 2 * h = 1) (h4 : e * (ε * c ε - 4) = 0) :
    e * (e * ε * h) = e * ε * h ∧ (e * ε * h) * (e * ε * h) = -e ∧ c (e * ε * h) = -(e * ε * h) := by
  have hcε : c ε = -(ε : R) := by
    rw [← hε, map_mul, map_mul, hc] at hm
    have hu : IsUnit ((u : R) * c u) := u.isUnit.mul (u.isUnit.map c)
    refine hu.mul_right_cancel ?_
    linear_combination hm
  have hch : c h = h := by
    have := congrArg c hh
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination h * this - c h * hh
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ((ε : R) * h) * he
  · linear_combination ((ε : R) ^ 2 * h ^ 2) * he + (e * ε * h ^ 2) * hcε - h ^ 2 * h4 - e * (2 * h + 1) * hh
  · rw [map_mul, map_mul, hce, hcε, hch]; ring

theorem cx_phase (c : R →+* R) (φ : R →+* ℂ) (hφ : ∀ z, φ (c z) = conj (φ z)) {e h m : R} {u ε : Rˣ} (he : φ e = 1)
    (hε : (ε : R) * u * c u = m) (hh : 2 * h = 1) (h4 : φ (ε * c ε) = 4) :
    φ (e * ε * h) = φ m / (‖φ m‖ : ℂ) := by
  have e1 : φ h = 1 / 2 := by
    have := congrArg φ hh
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination (1 / 2) * this
  rw [map_mul, map_mul, he, one_mul, e1]
  refine phase _ (φ u) _ (u.isUnit.map φ).ne_zero ?_ ?_
  · rw [← hφ, ← map_mul, ← map_mul, hε]
  · rw [← hφ, ← map_mul, h4]

theorem mixJ_real (φ : R →+* ℂ) {e j : R} (he : φ e = 1) :
    (mixJ n (1 - e) j).map φ = φ j • blk4 0 1 (-1) 0 := by
  rw [mixJ_map, map_sub, map_one, he, sub_self, mixJ, zero_smul, zero_add]

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

omit [NumberField F] [NumberField E] in
theorem sigR_sigR (A : Type) [CommRing A] [Algebra F A] (hσ : ∀ x, σ (σ x) = x) (z : A ⊗[F] E) :
    sigR A σ (sigR A σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[F] σ (σ x) = _
    rw [hσ]

omit [NumberField E] in
theorem sigR_compInf (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    sigR w.Completion σ (compInf F E w z) = compInf F E w (sigR (AF F) σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => rfl

omit [NumberField F] [NumberField E] in
theorem incl_half [CharZero E] (A : Type) [CommRing A] [Algebra F A] : 2 * inclR (F := F) (E := E) A (1 / 2) = 1 := by
  rw [← map_ofNat (inclR (F := F) (E := E) A) 2, ← map_mul]
  norm_num

theorem exists_point (n : ℕ) {e j : AF F ⊗[F] E} (hee : e * e = e) (hej : e * j = j) (hjj : j * j = -e)
    (hce : sigR (AF F) σ e = e) (hcj : sigR (AF F) σ j = -j) (hef : ∀ v, compFin F E v e = 0) :
    ∃ k ∈ levelAll σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) (stdLattice E (n + n)) 1,
      (AdelicU.matHom _ σ _ k).1 = mixJ n (1 - e) j := by
  have hkk : mixJ n (1 - e) j * mixJ n (1 - e) j = 1 := by
    rw [mixJ_mul, ← mixJ_one]
    congr 1
    · linear_combination hee - hjj
    · linear_combination (-2) * hej
  have hcT : Formalism.UG.cT (sigR (AF F) σ) (mixJ n (1 - e) j) = mixJ n (1 - e) j := by
    rw [cT_mixJ, map_sub, map_one, hce, hcj, neg_neg]
  let kU : GL (Fin (n + n)) (AF F ⊗[F] E) := ⟨mixJ n (1 - e) j, mixJ n (1 - e) j, hkk, hkk⟩
  have hmem : kU ∈ HR (AF F) σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) := by
    change Formalism.UG.cT (sigR (AF F) σ) (mixJ n (1 - e) j) * (blk4 0 1 (-1) 0).map (inclR (AF F)) * mixJ n (1 - e) j =
      (blk4 0 1 (-1) 0).map (inclR (AF F))
    rw [hcT, blkJ_map, ← mixJ_J, mixJ_mul, mixJ_mul]
    congr 1
    · linear_combination 2 * hej
    · linear_combination hee - hjj
  let k : GAd σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) := (⟨kU, hmem⟩ : HR (AF F) σ _)
  refine ⟨k, mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩, rfl⟩
  · have h : (AdelicU.matHom _ σ _ (proj σ _ v k)).1 = 1 := by
      change (mixJ n (1 - e) j).map (compFin F E v) = 1
      rw [mixJ_map, map_sub, map_one, hef, sub_zero, ← hej, map_mul, hef, zero_mul, mixJ_one]
    refine mem_stabLoc.2 fun y => ?_
    rw [h, Matrix.one_mulVec]
  · rw [mem_stabArch, map_one, inv_one, one_mul, mul_one]
    change Formalism.UG.cT (sigR w.Completion σ) ((mixJ n (1 - e) j).map (compInf F E w)) * 1 *
      (mixJ n (1 - e) j).map (compInf F E w) = 1
    rw [Matrix.mul_one]
    nth_rewrite 1 [mixJ_map]
    rw [cT_mixJ, sigR_compInf, sigR_compInf, hcj, map_neg, neg_neg, map_sub (sigR (AF F) σ), map_one, hce,
      ← mixJ_map, ← Matrix.map_mul, hkk, Matrix.map_one _ (map_zero _) (map_one _)]

end Adelic

theorem real_four (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (z : AE D)
    (hz : ∀ w, compInf D.host.F D.host.E w z = 4) (τ : D.what₂.Tau) : ((θ τ).comp (infPart D)) z = 4 :=
  (four_iff ((θ τ).comp (infPart D)) z).1
    (((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (z - 4)).1
      (fun w => (four_iff (compInf D.host.F D.host.E w) z).2 (hz w)) τ)

theorem idem_four (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) {e z : AE D} (he : finPart D e = 0)
    (hz : ∀ τ, ((θ τ).comp (infPart D)) z = 4) : e * (z - 4) = 0 :=
  (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _
    (fun τ => four_right ((θ τ).comp (infPart D)) e (hz τ)) (four_left (finPart D) z he)

theorem cA_skew (D : D7) (μ : D.host.E) (hμ : IsSkew μ) : cA D (incA D μ) = -incA D μ :=
  (show cA D (incA D μ) = incA D (star μ) from rfl).trans ((congrArg (incA D) hμ.2).trans ((incA D).map_neg μ))

theorem cA_cA (D : D7) (z : AE D) : cA D (cA D z) = z := sigR_sigR D.sp.cm.sig _ (fun x => star_star x) z

theorem exists_phase_adele (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (μ : D.host.E) (hμ : IsSkew μ) :
    ∃ e j : AE D, e * e = e ∧ e * j = j ∧ j * j = -e ∧ cA D e = e ∧ cA D j = -j ∧
      (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ τ, ((θ τ).comp (infPart D)) e = 1) ∧
      ∀ τ, ((θ τ).comp (infPart D)) j = tauE D τ μ / (‖tauE D τ μ‖ : ℂ) := by
  obtain ⟨e, hee, hce, hef, -, hfp, hip⟩ := GlobalTheory.StdUnn.realIdem_exists D
  obtain ⟨-, L2, L3, -⟩ := GlobalTheory.StdUnn.RealComp.real_components D θ hθ
  obtain ⟨u, ε, hεu, -, hε4⟩ := GlobalTheory.StdUnn.exists_scal_real D μ hμ 1
  have h4 := real_four D θ hθ _ hε4
  have hh : 2 * incA D (1 / 2) = 1 := incl_half _
  have h := alg_phase (cA D) (cA_cA D) hee hce hεu (cA_skew D μ hμ) hh (idem_four D θ hθ hfp h4)
  have he1 : ∀ τ, ((θ τ).comp (infPart D)) e = 1 := fun τ => (congrArg (θ τ) hip).trans (θ τ).map_one
  refine ⟨e, _, hee, h.1, h.2.1, hce, h.2.2, hef, he1, fun τ => ?_⟩
  have h2 : ((θ τ).comp (infPart D)) (incA D μ) = tauE D τ μ := L3 μ τ
  exact (cx_phase (cA D) ((θ τ).comp (infPart D)) (fun z => L2 z τ) (he1 τ) hεu hh (h4 τ)).trans
    (congrArg (fun t : ℂ => t / (‖t‖ : ℂ)) h2)

theorem exists_mem_K_compAt_eq_stdInv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (n : ℕ) (μ : D.host.E), IsSkew μ →
    ∃ k ∈ K D n, ∀ τ, compAt θ τ (mat k) = stdInv n μ τ := by
  intro D θ hθ n μ hμ
  obtain ⟨e, j, hee, hej, hjj, hce, hcj, hef, he1, hj⟩ := exists_phase_adele D θ hθ μ hμ
  obtain ⟨k, hk, hmat⟩ := exists_point D.sp.cm.sig n hee hej hjj hce hcj hef
  refine ⟨k, hk, fun τ => ?_⟩
  have h0 : mat (D := D) (n := n) k = mixJ n (1 - e) j := hmat
  have h1 : compAt θ τ (mixJ n (1 - e) j) = (mixJ n (1 - e) j).map ((θ τ).comp (infPart D)) := rfl
  rw [h0, h1, mixJ_real _ (he1 τ), hj]
  rfl

end GlobalTheory.CartanPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanInStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximalCompactUnn_component_standardCartanInv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (n : ℕ) (μ : D.host.E), IsSkew μ → ∃ k ∈ K D n, ∀ τ, compAt θ τ (mat k) = stdInv n μ τ := by
  first | exact @GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv | exact GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv | (intros; apply GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatIffMemAdelicMatrixSchwartzSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatIffMemAdelicMatrixSchwartzSpace
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

theorem GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA :
    ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ ↔ φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  intro D θ hθ m n φ
  exact ⟨fun h => GlobalTheory.SchwartzBruhatTensor.mem_schwartzA_of_isSchwartzBruhat D θ hθ m n φ h,
    fun h => GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ m n φ h⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatIffMemAdelicMatrixSchwartzSpaceStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhat_iff_mem_adelicMatrixSchwartzSpace : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ ↔ φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  first | exact @GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA | exact GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA | (intros; apply GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA <;> assumption)
end
end
