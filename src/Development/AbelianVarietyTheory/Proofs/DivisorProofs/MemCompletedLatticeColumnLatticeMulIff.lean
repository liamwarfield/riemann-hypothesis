module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatMulAd

variable {D : D7}

theorem mulVec_map_mem_hatL {n : ℕ} (g : Matrix (Fin n) (Fin n) D.host.E)
    (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hg : ∀ x ∈ Λ, g *ᵥ x ∈ Λ') (y : Fin n → EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    g.map (eToEAf D) *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨g *ᵥ x, hg x hx, ?_⟩
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul r a _ ha =>
    have : g.map (eToEAf D) *ᵥ (r • a) = r • (g.map (eToEAf D) *ᵥ a) := by
      show _ = (r : EAf D) • (g.map (eToEAf D) *ᵥ a)
      rw [← Matrix.mulVec_smul]
      rfl
    rw [this]; exact Submodule.smul_mem _ r ha

theorem mem_hatL_colLat_mul (D : D7) {n : ℕ} (γ B : GL (Fin n) D.host.E) : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (γ * B)) ↔
      (γ⁻¹).1.map (eToEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) := by
  intro v
  have h1 : ∀ x ∈ colLat B, (γ : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x ∈ colLat (γ * B) := by
    intro x hx
    rw [colLat_mul]
    exact ⟨x, hx, rfl⟩
  have h2 : ∀ x ∈ colLat (γ * B), ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x ∈ colLat B := by
    intro x hx
    rw [colLat_mul] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ ((γ : Matrix (Fin n) (Fin n) D.host.E) *ᵥ y) ∈ _
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy
  constructor
  · intro hv
    exact mulVec_map_mem_hatL _ _ _ h2 v hv
  · intro hv
    have := mulVec_map_mem_hatL _ _ _ h1 _ hv
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec] at this

end GlobalTheory.LatMulAd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedLattice_columnLattice_mul_iff : ∀ (D : D7) {n : ℕ} (γ B : GL (Fin n) D.host.E), ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (γ * B)) ↔
      (γ⁻¹).1.map (eToEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) := by
  first | exact @GlobalTheory.LatMulAd.mem_hatL_colLat_mul | exact GlobalTheory.LatMulAd.mem_hatL_colLat_mul | (intros; apply GlobalTheory.LatMulAd.mem_hatL_colLat_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

def eqvM (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) : Submodule ℂ (G → V) where
  carrier := {φ | (∀ h x, φ (ι h * x) = ρ h (φ x)) ∧ ∀ k ∈ K, ∀ x, φ (x * k) = φ x}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun h x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.add_apply, ha.1 h x, hb.1 h x, map_add (f := _)]
    · simp only [Pi.add_apply, ha.2 k hk x, hb.2 k hk x]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun h x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 h x, map_smul]
    · simp only [Pi.smul_apply, ha.2 k hk x]

def stabCard (ι : H →* G) (K : Subgroup G) (x : G) : ℕ :=
  Nat.card (ι.range ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)

def secM (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x : G) : V →ₗ[ℂ] (G → V) where
  toFun v y := ((stabCard ι K x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) v
  map_add' a b := by
    funext y
    simp only [map_add (f := _), smul_add, Pi.add_apply]
  map_smul' c a := by
    funext y
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_comm c]

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPtHom : UE E n →* finU (E := E) (n := n) where
  toFun := finPt
  map_one' := by
    apply Subtype.ext
    rw [FinPtLoc.finPt_eq]
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, FinPtLoc.finPt_eq, FinPtLoc.finPt_eq, FinPtLoc.finPt_eq]
    apply Subtype.ext
    exact (congrArg (finGL E n) (map_mul (ratF E n) a.1 b.1)).trans (map_mul _ _ _)

theorem finPtHom_apply (γ : UE E n) : finPtHom γ = finPt γ := rfl

theorem wAt_mul (lam : InfinitePlace E → DomWeight n) (a b : UE E n) :
    GlobalTheory.BCT.TrKer.wAt lam (a * b) = GlobalTheory.BCT.TrKer.wAt lam a ∘ₗ GlobalTheory.BCT.TrKer.wAt lam b := by
  unfold GlobalTheory.BCT.TrKer.wAt
  rw [← PiTensorProduct.map_comp]
  refine congrArg PiTensorProduct.map (funext fun v => ?_)
  change GlobalTheory.Branching.sqRep ℂ n (lam v) (GeneralLinearGroup.map v.embedding (a.1 * b.1)) = _
  rw [map_mul, map_mul, Module.End.mul_eq_comp]

theorem wAt_one (lam : InfinitePlace E → DomWeight n) : GlobalTheory.BCT.TrKer.wAt lam 1 = LinearMap.id := by
  unfold GlobalTheory.BCT.TrKer.wAt
  simp only [OneMemClass.coe_one, map_one]
  exact PiTensorProduct.map_id

def wDual (lam : InfinitePlace E → DomWeight n) : Representation ℂ (UE E n) (Module.Dual ℂ (GlobalTheory.BCT.TrKer.Wsp lam)) where
  toFun γ := (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹).dualMap
  map_one' := by
    rw [inv_one, wAt_one]
    rfl
  map_mul' a b := by
    rw [_root_.mul_inv_rev, wAt_mul, ← LinearMap.dualMap_comp_dualMap]
    rfl

end GlobalTheory.BCT.TraceBlocks
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWeylCellTranslate
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory.UnipShiftU

variable {L : Type} [Field L]

theorem unipB_mul_apply_succ {n : ℕ} {X Y : GL (Fin n) L} (hX : X ∈ unipB L (Fin n)) (hY : Y ∈ unipB L (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X * Y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' =
      (X : Matrix (Fin n) (Fin n) L) a a' + (Y : Matrix (Fin n) (Fin n) L) a a' := by
  rw [mem_unipB] at hX hY
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [hX.2 a, hY.2 a', one_mul, mul_one, add_comm]
  · intro c _ hc
    have h1 := Fin.val_injective.ne hc.1
    have h2 := Fin.val_injective.ne hc.2
    by_cases hca : c < a
    · rw [hX.1 a c hca, zero_mul]
    · have : a' < c := by rw [Fin.lt_iff_val_lt_val] at hca ⊢; omega
      rw [hY.1 c a' this, mul_zero]

theorem unipB_inv_apply_succ {n : ℕ} {X : GL (Fin n) L} (hX : X ∈ unipB L (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' = -(X : Matrix (Fin n) (Fin n) L) a a' := by
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  have e := unipB_mul_apply_succ hX (inv_mem hX) h
  rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_ne hne] at e
  linear_combination -e

theorem conj_apply {n : ℕ} {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y)
    (X : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * X * (y : Matrix (Fin n) (Fin n) L)) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * X (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
  have hi := hy.inv
  rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · intro b _ hb
      rw [hi i b (by intro e; apply hb; rw [e]; simp), zero_mul]
    · simp
  · intro b _ hb; rw [hy b j hb, mul_zero]
  · simp

theorem inv_mul_diag {n : ℕ} {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y) (i : Fin n) :
    ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * (y : Matrix (Fin n) (Fin n) L) (s i) i = 1 := by
  have h : ((y⁻¹ * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (s i), Units.val_one, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rw [hy.inv i b (by intro e; apply hb; rw [e]; simp), zero_mul]
  · simp

theorem swap_inversion {n : ℕ} {a a' p q : Fin n} (h : a'.val = a.val + 1) (hpq : p < q)
    (hs : Equiv.swap a a' q < Equiv.swap a a' p) : p = a ∧ q = a' := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def] at hs
  rw [Fin.lt_iff_val_lt_val] at hpq
  split_ifs at hs with h1 h2 h3 h4 h5 h6 <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem transvection_apply' {n : ℕ} (a a' : Fin n) (d : L) (i j : Fin n) :
    Matrix.transvection a a' d i j = (if i = j then 1 else 0) + (if i = a ∧ j = a' then d else 0) := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  congr 1
  by_cases h1 : a = i <;> by_cases h2 : a' = j <;> simp [h1, h2, eq_comm]

theorem ordL_one [Valued L (WithZero (Multiplicative ℤ))] : ordL (1 : L) = 0 := by
  unfold ordL
  rw [dite_eq_right (by simp)]
  simp
  rfl

end GlobalTheory.UnipShiftU

namespace GlobalTheory.UnipShiftU

end GlobalTheory.UnipShiftU

namespace GlobalTheory.UnipShiftU

end GlobalTheory.UnipShiftU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEvalSubTopLe
namespace GlobalTheory

theorem abs_factorial_mul_eval_sub_top_le (d : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ d) :
    ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℚ) * p.eval (m : ℚ) - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d|
      ≤ C * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
  obtain ⟨C, hC⟩ := exists_nat_ge ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|)
  refine ⟨C, fun m => ?_⟩
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hf : (0 : ℚ) ≤ d.factorial := Nat.cast_nonneg _
  rw [Polynomial.eval_eq_sum_range' (n := d + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ]
  have e : (d.factorial : ℚ) * (∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i + p.coeff d * (m : ℚ) ^ d)
      - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d
      = (d.factorial : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i := by ring
  rw [e, abs_mul, abs_of_nonneg hf]
  have hX : (0 : ℚ) ≤ (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1) := by positivity
  have h1 : |∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i|
      ≤ (∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i < d := Finset.mem_range.mp hi
    rw [abs_mul, abs_of_nonneg (pow_nonneg hm i)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have a1 : (m : ℚ) ^ i ≤ ((m : ℚ) + 1) ^ i := pow_le_pow_left₀ hm (by linarith) i
    have a2 : ((m : ℚ) + 1) ^ i ≤ ((m : ℚ) + 1) ^ (d - 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have a3 : (1 : ℚ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have a4 : (0 : ℚ) ≤ ((m : ℚ) + 1) ^ (d - 1) := by positivity
    exact a1.trans (a2.trans (le_mul_of_one_le_left a4 a3))
  calc _ ≤ (d.factorial : ℚ) * ((∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left h1 hf
    _ = ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC hX

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLe
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem abs_factorial_mul_chi_twist_lbPow_sub_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, L.IsLB → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * chi k (twist F (lbPow L m)) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  intro k _ _ X _ hproj d F _ hsupp L hL
  have hv : DiffVanish (d + 1) (chiPic k F) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) F hproj hsupp
  obtain ⟨p, hpdeg, hpeval, hpcoeff⟩ := hv.exists_polynomial_int ℚ (cls L hL) 0
  obtain ⟨C, hC⟩ := abs_factorial_mul_eval_sub_top_le d p hpdeg
  refine ⟨C, fun m => ?_⟩
  have hmd : multiDiff (fun _ : Fin d => cls L hL) (chiPic k F) 0 =
      interNum k F (fun _ : Fin d => L) :=
    hv.multiDiff_chiPic (L := fun _ : Fin d => L) (by simp) (fun _ => hL) 0
  have hchi : chi k (twist F (lbPow L m)) = chiPic k F ((m : ℤ) • cls L hL) := by
    rw [← twistZ_natCast]
    exact chi_twistZ k F hL (m : ℤ)
  have heval : p.eval (m : ℚ) = (chi k (twist F (lbPow L m)) : ℚ) := by
    have e := hpeval (m : ℤ)
    rw [zero_add, ← hchi, Int.cast_natCast] at e
    exact e
  have hfac : (d.factorial : ℚ) * p.coeff d = (interNum k F (fun _ : Fin d => L) : ℚ) := by
    rw [hpcoeff, hmd, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast d.factorial_ne_zero), one_mul]
  have h := hC m
  rw [heval, hfac] at h
  have h' : ((|(d.factorial : ℤ) * chi k (twist F (lbPow L m)) -
      interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| : ℤ) : ℚ) ≤
      ((C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) : ℤ) : ℚ) := by
    push_cast
    exact h
  exact_mod_cast h'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLeStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, L.IsLB → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * chi k (twist F (lbPow L m)) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  first | exact @GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le | exact GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le | (intros; apply GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointTrivialOfGeometric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointTrivialOfGeometric
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRigid

theorem eq_one_of_geometric (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (T : Over S) (x : T ⟶ A) (c : ℕ) (hc : IsUnit (c : Γ(T.left, ⊤)))
    (hx : x ^ c = 1)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S)
      (g : Over.mk z ⟶ T), g ≫ x = 1) : x = 1 := by
  have := hA.smooth
  let AT := (Over.pullback T.hom).obj A
  have hft : LocallyOfFiniteType AT.hom := by
    change LocallyOfFiniteType (pullback.snd A.hom T.hom); infer_instance
  let f := ((Over.pullback T.hom).map (mulN A c)).left
  have hfu : FormallyUnramified f := by
    have h := GlobalTheory.GrpTangent.formallyUnramified_mulN AT hc
    rw [← GlobalTheory.GrpTangent.pullback_map_mulN] at h
    exact h
  have hff : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ AT.hom) := by
      rw [show f ≫ AT.hom = AT.hom from Over.w ((Over.pullback T.hom).map (mulN A c))]
      infer_instance
    exact locallyOfFiniteType_of_comp f AT.hom
  let sec : (T ⟶ A) → (T.left ⟶ AT.left) := fun y =>
    pullback.lift y.left (𝟙 T.left) (by rw [Over.w y, Category.id_comp])
  have sec_fst : ∀ y : T ⟶ A, sec y ≫ pullback.fst A.hom T.hom = y.left := fun y =>
    pullback.lift_fst _ _ _
  have sec_snd : ∀ y : T ⟶ A, sec y ≫ pullback.snd A.hom T.hom = 𝟙 _ := fun y =>
    pullback.lift_snd _ _ _
  have f_fst : f ≫ pullback.fst A.hom T.hom = pullback.fst A.hom T.hom ≫ (mulN A c).left :=
    pullback.lift_fst _ _ _
  have f_snd : f ≫ pullback.snd A.hom T.hom = pullback.snd A.hom T.hom :=
    pullback.lift_snd _ _ _
  have sec_f : ∀ y : T ⟶ A, sec y ≫ f = sec (y ^ c) := by
    intro y
    apply pullback.hom_ext
    · rw [Category.assoc, f_fst, ← Category.assoc, sec_fst, sec_fst,
        ← GlobalTheory.GrpTangent.comp_mulN]
      rfl
    · rw [Category.assoc, f_snd, sec_snd, sec_snd]
  have key : sec x ≫ f = sec 1 ≫ f := by rw [sec_f, sec_f, hx, one_pow]
  let Y : Over AT.left := Over.mk f
  let X : Over AT.left := Over.mk (sec 1 ≫ f)
  let fx : X ⟶ Y := Over.homMk (sec x) key
  let f1 : X ⟶ Y := Over.homMk (sec 1) rfl
  haveI : LocallyOfFiniteType Y.hom := hff
  haveI : FormallyUnramified Y.hom := hfu
  have hpt : ∀ t : T.left, t ∈ Set.range (GlobalTheory.FinEt.agreeι fx f1) := by
    intro t
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point T.left t
    have hk : (c : k) ≠ 0 := (GlobalTheory.GrpTangent.isUnit_natCast_of_point hc a).ne_zero
    have h1 := H k hk (a ≫ T.hom) (Over.homMk a rfl)
    have h2 : a ≫ x.left = a ≫ (1 : T ⟶ A).left := by
      have := congrArg CommaMorphism.left
        (h1.trans (comp_one (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)).symm)
      exact this
    have h3 : a ≫ fx.left = a ≫ f1.left := by
      change a ≫ sec x = a ≫ sec 1
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, sec_fst, sec_fst, h2]
      · rw [Category.assoc, Category.assoc, sec_snd, sec_snd]
    have h4 := (GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 a).mp h3
    apply h4
    rw [ha]; rfl
  have hsec : sec x = sec 1 := by
    have := (GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 (𝟙 _)).mpr (by
      rintro _ ⟨t, rfl⟩; exact hpt _)
    simpa [fx, f1] using this
  ext1
  rw [← sec_fst x, hsec, sec_fst]

end GlobalTheory.TorsionRigid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointTrivialOfGeometricStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_torsionPoint_trivial_of_geometric : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (T : Over S) (x : T ⟶ A) (c : ℕ), IsUnit (c : Γ(T.left, ⊤)) → x ^ c = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S) (g : Over.mk z ⟶ T), g ≫ x = 1) → x = 1 := by
  first | (exact @GlobalTheory.TorsionRigid.eq_one_of_geometric) | (exact GlobalTheory.TorsionRigid.eq_one_of_geometric) | (intros; apply GlobalTheory.TorsionRigid.eq_one_of_geometric  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolEqIdxRatio
noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount.OrbKProd

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd

theorem finsum_prod_mul {α β : Type} (u : α → ℂ) (v : β → ℂ) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  by_cases hu : (Function.support u).Finite
  · by_cases hv : (Function.support v).Finite
    · exact finsum_prod_mul_of_finite u v hu hv
    · rw [finsum_of_infinite_support hv, mul_zero]
      by_cases h0 : ∀ a, u a = 0
      · simp [h0]
      · push_neg at h0
        obtain ⟨a, ha⟩ := h0
        apply finsum_of_infinite_support
        intro hfin
        apply hv
        refine (hfin.image Prod.snd).subset ?_
        intro b hb
        exact ⟨(a, b), by simp only [Function.mem_support] at hb ⊢; exact mul_ne_zero ha hb, rfl⟩
  · rw [finsum_of_infinite_support hu, zero_mul]
    by_cases h0 : ∀ b, v b = 0
    · simp [h0]
    · push_neg at h0
      obtain ⟨b, hb⟩ := h0
      apply finsum_of_infinite_support
      intro hfin
      apply hu
      refine (hfin.image Prod.fst).subset ?_
      intro a ha
      exact ⟨(a, b), by simp only [Function.mem_support] at ha ⊢; exact mul_ne_zero ha hb, rfl⟩

section Vol

variable {G : Type} [Group G]

theorem vol_eq_idxRatio (C H : Subgroup G) : vol C H = GlobalTheory.FunObj.idxRatio H C := rfl

theorem vol_prod {G' : Type} [Group G'] (C H : Subgroup G) (C' H' : Subgroup G') :
    vol (C.prod C') (H.prod H') = vol C H * vol C' H' := by
  unfold vol
  rw [relIndex_prod_prod, relIndex_prod_prod]
  push_cast
  exact mul_div_mul_comm _ _ _ _

theorem map_conj_mul (K : Subgroup G) (t x : G) :
    K.map (MulAut.conj (t * x)).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  have h := map_conj_mul_three_subgroup_of_mem K K.one_mem t x
  rwa [mul_one] at h

theorem inf_map_conj (T A : Subgroup G) {t : G} (ht : t ∈ T) :
    T ⊓ A.map (MulAut.conj t).toMonoidHom = (T ⊓ A).map (MulAut.conj t).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, map_conj_self _ ht]

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Vol

section Term

variable {G : Type} [Group G]

def oTerm (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) (x : G) : ℂ :=
  ((vol C (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom) : ℚ) : ℂ)⁻¹ * f (x⁻¹ * δ * θ x)

theorem orbC_eq (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) :
    orbC θ K C δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), oTerm θ K C δ f (Quotient.out q) :=
  rfl

theorem f_inv (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * θ k) = f y)
    {t k : G} (ht : t ∈ twCent θ δ) (hk : k ∈ K) (x : G) :
    f ((t * x * k)⁻¹ * δ * θ (t * x * k)) = f (x⁻¹ * δ * θ x) := by
  have ht0 : t * δ = δ * θ t := ht
  have ht' : θ t = δ⁻¹ * (t * δ) := eq_inv_mul_of_mul_eq ht0.symm
  rw [← hf k hk (x⁻¹ * δ * θ x)]
  congr 1
  simp only [map_mul, _root_.mul_inv_rev, ht']
  group

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Term

end GlobalTheory.LKCount.OrbKProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemULOfSplit
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_UL_of_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) (x : GLw n w) : x ∈ UL n w := by
  rw [UL, if_pos hw]; exact Subgroup.mem_top x

theorem toSub_eq {G : Type} [Group G] (H : Subgroup G) (g : G) (hg : g ∈ H) : toSub H g = ⟨g, hg⟩ := by
  simp [toSub, hg]

theorem ct_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (F : GLw n w → ℂ)
    (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (hF : ∀ y ∈ N, ∀ x, F (y * x) = F x ∧ F (x * y) = F x)
    (k : GLw a w × GLw b w) (hk1 : k.1 ∈ GlobalTheory.LFun.KGL w (n := a)) (hk2 : k.2 ∈ GlobalTheory.LFun.KGL w (n := b)) (hkN : dgM h w k ∈ N)
    (m : GLw a w × GLw b w) : ct h w F (k * m) = ct h w F m ∧ ct h w F (m * k) = ct h w F m := by
  have hab := GlobalTheory.T.absHalf_blockDet_integralGL_invariant E a b w m k hk1 hk2
  constructor
  · unfold ct
    rw [hab.1]
    congr 2
    funext X
    congr 1
    funext κ
    rw [(GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal E a b n h w m k _).1]
    have e : (κ : GLw n w)⁻¹ * (dgM h w k * blk h w m (Multiplicative.toAdd X)) * κ =
        ((κ : GLw n w)⁻¹ * dgM h w k * κ) * ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * κ) := by group
    rw [e, (hF _ (hNn _ κ.2 _ hkN) _).1]
  · unfold ct
    have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        avg fun κ : GlobalTheory.LFun.KGL w (n := n) => F ((κ : GLw n w)⁻¹ * blk h w (m * k) (Multiplicative.toAdd X) * κ)) =
        fun X => avg fun κ : GlobalTheory.LFun.KGL w (n := n) => F ((κ : GLw n w)⁻¹ *
          blk h w m (Multiplicative.toAdd (Multiplicative.ofAdd (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val))) * κ) := by
      funext X
      congr 1
      funext κ
      rw [(GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal E a b n h w m k _).2]
      have e : (κ : GLw n w)⁻¹ * (blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * dgM h w k) * κ =
          ((κ : GLw n w)⁻¹ * blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * κ) *
            ((κ : GLw n w)⁻¹ * dgM h w k * κ) := by group
      rw [e, (hF _ (hNn _ κ.2 _ hkN) _).2]
      rfl
    have hh := GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul E a b w (fun Y => avg fun κ : GlobalTheory.LFun.KGL w (n := n) =>
      F ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd Y) * κ)) k.1 k.2⁻¹ hk1 (inv_mem hk2)
    rw [hab.2, e, hh]

theorem ctMu_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (N : Subgroup (GLw n w))
    (K' : Subgroup (UL n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (hf : IsHecke K' f)
    (hNK : N ≤ K'.map (UL n w).subtype) (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (k : GLw a w × GLw b w) (hk : k ∈ (lev₁ h w N μ).prod (lev₂ h w N μ)) (m : GLw a w × GLw b w) :
    ctMu h w μ f (k * m) = ctMu h w μ f m ∧ ctMu h w μ f (m * k) = ctMu h w μ f m := by
  obtain ⟨⟨⟨hk1, hkN1⟩, hkμ1⟩, ⟨⟨hk2, hkN2⟩, hkμ2⟩⟩ := hk
  have hkN : dgM h w k ∈ N := by
    have e : k = (k.1, 1) * (1, k.2) := by ext <;> simp
    rw [e, map_mul]
    exact N.mul_mem hkN1 hkN2
  have hF : ∀ y ∈ N, ∀ x, (fun y => f (toSub (UL n w) y)) (y * x) = (fun y => f (toSub (UL n w) y)) x ∧
      (fun y => f (toSub (UL n w) y)) (x * y) = (fun y => f (toSub (UL n w) y)) x := by
    intro y hy x
    obtain ⟨y', hy', rfl⟩ := hNK hy
    have e1 : toSub (UL n w) ((UL n w).subtype y' * x) = y' * toSub (UL n w) x := by
      rw [toSub_eq _ _ (mem_UL_of_split hw _), toSub_eq _ _ (mem_UL_of_split hw x)]; rfl
    have e2 : toSub (UL n w) (x * (UL n w).subtype y') = toSub (UL n w) x * y' := by
      rw [toSub_eq _ _ (mem_UL_of_split hw _), toSub_eq _ _ (mem_UL_of_split hw x)]; rfl
    exact ⟨by simp only; rw [e1]; exact (hf.2 y' hy' _).1, by simp only; rw [e2]; exact (hf.2 y' hy' _).2⟩
  have hc := ct_inv h w N (fun y => f (toSub (UL n w) y)) hNn hF k hk1 hk2 hkN m
  have hμ1 : μ (GeneralLinearGroup.det k.1) = 1 := hkμ1
  have hμ2 : μ (GeneralLinearGroup.det k.2) = 1 := hkμ2
  unfold ctMu
  rw [hc.1, hc.2]
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow, map_pow, hμ1, hμ2, one_pow, mul_one, one_mul]
  constructor <;> trivial

theorem ctMu_hecke : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen {x | μ x = 1} → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw (n - a) w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ ∧ IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n := (n - a))) K₂ ∧ ((K' = KL n w ∧ ∀ u ∈ (GlobalTheory.LFun.KGL w (n := 1)), μ (GeneralLinearGroup.det u) = 1) → K₁ = GlobalTheory.LFun.KGL w (n := a) ∧ K₂ = GlobalTheory.LFun.KGL w (n := (n - a))) ∧ ∀ f, IsHecke K' f → IsHecke (K₁.prod K₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) ∧ ((∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a (n - a) w (ctMu (Nat.add_sub_cancel' ha) w μ f)) := by
  intro E _ _ _ _ n a ha w hw μ hμ K' hK'
  obtain ⟨N, hNo, hNK, hNn, hNf⟩ := GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel E n w K' hw hK'
  have hlev := GlobalTheory.T.isLevel_blockLevels_splitPlace E a (n - a) n (Nat.add_sub_cancel' ha) w N μ hw hNo hμ
  refine ⟨lev₁ (Nat.add_sub_cancel' ha) w N μ, lev₂ (Nat.add_sub_cancel' ha) w N μ, hlev.1, hlev.2, ?_,
    fun f hf => ⟨⟨GlobalTheory.T.hasCompactSupport_twistedConstantTermSplitPlace E a (n - a) n _ w μ f hw hf.1, fun k hk m =>
      ctMu_inv _ w hw N K' μ f hf hNK hNn k hk m⟩, GlobalTheory.T.twistedConstantTermSplitPlace_regular E a (n - a) n _ w μ f hw⟩⟩
  rintro ⟨hK'e, hμ1⟩
  rw [hNf hK'e]
  exact GlobalTheory.T.blockLevels_eq_integralGL_of_unramified E a (n - a) n _ w μ hμ1

end GlobalTheory.BCT.CtLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliOperatorAlgebraStableUnderComplexConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliOperatorAlgebraStableUnderComplexConj
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.ConjZalg

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem map_qdet_semilinear {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →+* B) (σ : ℂ →+* ℂ)
    (hf : ∀ c, f (algebraMap ℂ A c) = algebraMap ℂ B (σ c)) (X : Fin a → Fin a → A) (u : ℂ) :
    f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) (σ u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 3
  funext k
  by_cases h : s k = k <;> simp [Formalism.REAL.Tm, h, map_add, hf, map_sub, map_natCast]

def conjBy (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) : Module.End ℂ (Sm E a) →+* Module.End ℂ (Sm E a) where
  toFun z :=
    { toFun := fun φ => C.symm (z (C φ))
      map_add' := fun φ ψ => by simp
      map_smul' := fun c φ => by
        rw [LinearEquiv.map_smulₛₗ, LinearMap.map_smul, LinearEquiv.map_smulₛₗ]; simp }
  map_one' := LinearMap.ext fun φ => by simp
  map_mul' z w := LinearMap.ext fun φ => by simp
  map_zero' := LinearMap.ext fun φ => by simp
  map_add' z w := LinearMap.ext fun φ => by simp

theorem conjBy_apply (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjBy C z φ = C.symm (z (C φ)) := rfl

theorem conjBy_algebraMap (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (c : ℂ) :
    conjBy C (algebraMap ℂ (Module.End ℂ (Sm E a)) c) = algebraMap ℂ _ (starRingEnd ℂ c) :=
  LinearMap.ext fun φ => by
    rw [conjBy_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearEquiv.map_smulₛₗ]; simp

theorem C_Eop (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (i j : Fin a)
    (φ : Sm E a) : C (Eop τ i j φ) = Eop (ComplexEmbedding.conjugate τ) i j (C φ) := by
  have hl : ∀ x φ, C (lieS E a i j x φ) = lieS E a i j x (C φ) := fun x φ => (hC (Op.lie _) φ).symm
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, map_smulₛₗ, map_sub, hl, atEmb_conj, map_one,
    Complex.conj_I, e, map_neg, LinearMap.neg_apply]
  have h2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by simp [map_div₀, map_ofNat]
  rw [h2]
  congr 1
  simp [sub_eq_add_neg, neg_smul, smul_neg]

theorem conjBy_Eop (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (i j : Fin a) :
    conjBy C (Eop τ i j) = Eop (ComplexEmbedding.conjugate τ) i j :=
  LinearMap.ext fun φ => by
    apply C.injective
    have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [conjBy_apply, LinearEquiv.apply_symm_apply, C_Eop C hC, hcc]

theorem conjBy_cap (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (u : ℂ) :
    conjBy C (cap τ u) = cap (ComplexEmbedding.conjugate τ) (starRingEnd ℂ u) := by
  rw [cap, map_qdet_semilinear (conjBy C) (starRingEnd ℂ) (conjBy_algebraMap C)]
  simp only [conjBy_Eop C hC, cap]
  congr 1
  simp [map_div₀, map_ofNat, map_sub, map_natCast]

theorem conjBy_mem_Zalg (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ))
    {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) : conjBy C z ∈ Zalg E a := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | conjBy C z ∈ Zalg E a}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul] at *; exact Subalgebra.mul_mem _ hx hy
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at *; exact Subalgebra.add_mem _ hx hy
      algebraMap_mem' := fun c => by
        simp only [Set.mem_setOf_eq, conjBy_algebraMap]; exact Subalgebra.algebraMap_mem _ _ }
  refine (Algebra.adjoin_le (S := S) ?_) hz
  rintro _ ⟨τ, u, rfl⟩
  change conjBy C (cap τ u) ∈ Zalg E a
  rw [conjBy_cap C hC]
  exact Algebra.subset_adjoin ⟨_, _, rfl⟩

theorem conj_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a),
    (∀ o φ, act o (C φ) = C (act o φ)) → ∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ) := by
  intro E _ _ _ a C hC z hz
  exact ⟨conjBy C z, conjBy_mem_Zalg C hC hz, fun φ => by rw [conjBy_apply, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.CuspRep.ConjZalg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliOperatorAlgebraStableUnderComplexConjStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_operator_algebra_stable_under_complex_conj : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a), (∀ o φ, act o (C φ) = C (act o φ)) → ∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ) := by
  first | exact @GlobalTheory.CuspRep.ConjZalg.conj_Zalg | exact GlobalTheory.CuspRep.ConjZalg.conj_Zalg | (intros; apply GlobalTheory.CuspRep.ConjZalg.conj_Zalg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimLeOfIsClosedImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimLeOfIsClosedImmersion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relDim_le_of_formallyUnramified (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C] [Nontrivial C]
    [Algebra.FormallyUnramified B C] (g g' : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension g R B]
    [Algebra.IsStandardSmoothOfRelativeDimension g' R C] : g' ≤ g := by
  have : Nontrivial B := (algebraMap B C).domain_nontrivial
  have : Algebra.IsStandardSmooth R B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Module.Free B Ω[B⁄R] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange R B C) := fun x =>
    (KaehlerDifferential.exact_mapBaseChange_map R B C x).mp (Subsingleton.elim _ _)
  have h1 := LinearMap.rank_le_of_surjective _ hs
  rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g', Module.rank_baseChange,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g] at h1
  simpa using h1

end GlobalTheory

namespace GlobalTheory

theorem relDim_le_of_surjective_away {R B A L : Type} [CommRing R] [CommRing B] [CommRing A] [CommRing L]
    [Algebra A L] (t : A) [IsLocalization.Away t L] [Nontrivial L] (φ : R →+* B) (ψ : B →+* A)
    (hψ : Function.Surjective ψ) (g g' : ℕ) (hφ : RingHom.IsStandardSmoothOfRelativeDimension g φ)
    (hL : RingHom.IsStandardSmoothOfRelativeDimension g' ((algebraMap A L).comp (ψ.comp φ))) :
    g' ≤ g := by
  letI : Algebra R B := φ.toAlgebra
  letI : Algebra B A := ψ.toAlgebra
  letI : Algebra B L := ((algebraMap A L).comp ψ).toAlgebra
  letI : Algebra R L := ((algebraMap A L).comp (ψ.comp φ)).toAlgebra
  haveI : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyUnramified B A := Algebra.FormallyUnramified.of_surjective (Algebra.ofId B A) hψ
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.FormallyUnramified B L := Algebra.FormallyUnramified.comp B A L
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g' R L := hL
  exact relDim_le_of_formallyUnramified R B L g g'

end GlobalTheory

namespace GlobalTheory

theorem relDim_le_of_isClosedImmersion : ∀ (k : Type) [Field k] (N G : Over (Sp k)) (ν : N ⟶ G),
    IsClosedImmersion ν.left → Nonempty N.left → ∀ g g' : ℕ, SmoothOfRelativeDimension g G.hom →
    SmoothOfRelativeDimension g' N.hom → g' ≤ g := by
  intro k _ N G ν hν ⟨x⟩ g g' hG hN
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hG.exists_isStandardSmoothOfRelativeDimension (ν.left x)
  let V' : N.left.Opens := ν.left ⁻¹ᵁ V
  have hV' : IsAffineOpen V' := hV.preimage ν.left
  have hN' : SmoothOfRelativeDimension g' (ν.left ≫ G.hom) := by rw [Over.w ν]; exact hN
  have e' : V' ≤ (ν.left ≫ G.hom) ⁻¹ᵁ U := fun y hy => e hy
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g') _ hN' ⟨U, hU⟩ ⟨V', hV'⟩ e'
  have : Nonempty V' := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(N.left, V')
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1
      (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  have hψ : Function.Surjective (ν.left.appLE V V' le_rfl).hom := by
    have := ν.left.app_surjective V hV
    rw [Scheme.Hom.app_eq_appLE] at this
    exact this
  refine relDim_le_of_surjective_away (L := Localization.Away t) t (G.hom.appLE U V e).hom
    (ν.left.appLE V V' le_rfl).hom hψ g g' h ?_
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE ν.left G.hom U V V' e le_rfl]
  exact h₁

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimLeOfIsClosedImmersionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relDim_le_of_smooth_of_isClosedImmersion : ∀ (k : Type) [Field k] (N G : Over (Sp k)) (ν : N ⟶ G), IsClosedImmersion ν.left → Nonempty N.left → ∀ g g' : ℕ, SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g' N.hom → g' ≤ g := by
  first | exact @GlobalTheory.relDim_le_of_isClosedImmersion | exact GlobalTheory.relDim_le_of_isClosedImmersion | (intros; apply GlobalTheory.relDim_le_of_isClosedImmersion <;> assumption)
end
end
