module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MemSEOfFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.ModulusFactorDefinition

abbrev dC (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin n) R :=
  ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) R).submatrix finSumFinEquiv.symm id)

def mfac (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nT : ℕ} (nS : ℕ)
    (t : GL (Fin nT) (AF F ⊗[F] E)) : ℝ :=
  (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
    (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ)

end PositivityTheory.ThKW.ModulusFactorDefinition

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.GoodLat
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hRatF (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : Matrix (Fin nT) (Fin nS) E) : E :=
  ∑ a, ∑ b, ∑ c, ∑ d, JS⁻¹ a b * σ (y c b) * JT c d * x d a

structure GoodLat {nS nT : ℕ} (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : Prop where
  fg : Λ.FG
  den : ∀ M : Matrix (Fin nT) (Fin nS) E, ∃ N : ℕ, 0 < N ∧ N • M ∈ Λ

def RatSD (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : Prop :=
  ∀ M, M ∈ Λ ↔ ∀ M' ∈ Λ, ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT M M') = n

end PositivityTheory.ThKW

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def dC (n : ℕ) : Matrix (Fin (n + n)) (Fin n) (AF F ⊗[F] E) :=
  ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)


variable (F E) in
def aC (n : ℕ) : Matrix (Fin (n + n)) (Fin n) (AF F ⊗[F] E) :=
  ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (-1)).submatrix finSumFinEquiv.symm id)

def prof (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (f : WOF F E nS (nT + nT) → ℂ) (y : WOF F E nS nT) : ℂ :=
  GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT)
    (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ (aC F E nT * y) f)

end GlobalTheory.SplitLagrF

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SumFourEqTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSelfOfTrivial
noncomputable section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.LatticeRep

variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ]

def Transl (W : X → M →ₗ[ℂ] M) (A : Submodule R X) : Set M := {m | ∃ x v, Fixes W A v ∧ m = W x v}

def IsLatSystem (σ : R →+* R) (w : R) (γ : X → X → ℂ) (W : X → M →ₗ[ℂ] M) (lam : ℕ →* ℂ) (A : Submodule R X)
    (ρ : Γ →* Module.End R X) : Prop :=
  IsHeis σ w γ W ∧ GoodNorm σ lam ∧ SelfDual γ A ∧ Submodule.span ℂ (Transl W A) = ⊤ ∧
    (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) ∧ ∀ g, idx A (A.map (ρ g)) ≠ 0

def IsLatRep (W : X → M →ₗ[ℂ] M) (lam : ℕ →* ℂ) (A : Submodule R X) (ρ : Γ →* Module.End R X)
    (Om : Γ →* Module.End ℂ M) : Prop :=
  (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧ ∀ g v, Fixes W A v → Om g v = normOp lam W A (A.map (ρ g)) v

variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M}

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
theorem _root_.GlobalTheory.LatticeRep.transl_induction (hs : Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A) = ⊤) {p : M → Prop}
    (mem : ∀ x v, _root_.GlobalTheory.FinWeil.Fixes W A v → p (W x v)) (zero : p 0) (add : ∀ a b, p a → p b → p (a + b))
    (smul : ∀ (c : ℂ) a, p a → p (c • a)) (m : M) : p m := by
  have hm : m ∈ Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A) := by
    rw [hs]; exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, v, hv, rfl⟩ := hy
    exact mem x v hv
  | zero => exact zero
  | add a b _ _ ha hb => exact add a b ha hb
  | smul c a _ ha => exact smul c a ha

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
private theorem sumOp_eq_self_of_le {B : Submodule R X} (hBA : B ≤ A) {v : M}
    (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) : _root_.GlobalTheory.FinWeil.sumOp W A B v = v := by
  unfold _root_.GlobalTheory.FinWeil.sumOp
  have hz : ∀ q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H b => exact (QuotientAddGroup.eq_zero_iff b).mpr (hBA b.2)
  rw [finsum_eq_single _ 0 (fun q hq => absurd (hz q) hq)]
  exact hv _ (hBA (Quotient.out (0 : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)).2)


open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
theorem _root_.GlobalTheory.LatticeRep.IsLatRep.fix_of_map_le (h : _root_.GlobalTheory.LatticeRep.IsLatSystem σ w γ W lam A ρ) (hO : _root_.GlobalTheory.LatticeRep.IsLatRep W lam A ρ Om) {g : Γ}
    (hg : A.map (ρ g) ≤ A) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) : Om g v = v := by
  rw [hO.2 g v hv]
  unfold _root_.GlobalTheory.FinWeil.normOp _root_.GlobalTheory.FinWeil.idx
  have hidx : A.toAddSubgroup.relIndex (A.map (ρ g)).toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.mpr hg
  rw [hidx, map_one, inv_one, one_smul]
  exact sumOp_eq_self_of_le hg hv

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
private theorem map_sumOp_of_commute {B : Submodule R X} (φ : M →ₗ[ℂ] M)
    (h : _root_.GlobalTheory.FinWeil.idx A B ≠ 0) (hφ : ∀ x m, φ (W x m) = W x (φ m)) (v : M) :
    φ (_root_.GlobalTheory.FinWeil.sumOp W A B v) = _root_.GlobalTheory.FinWeil.sumOp W A B (φ v) := by
  unfold _root_.GlobalTheory.FinWeil.idx at h
  have : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) :=
    AddSubgroup.index_ne_zero_iff_finite.mp h
  unfold _root_.GlobalTheory.FinWeil.sumOp
  rw [map_finsum φ (Set.toFinite _)]
  simp only [hφ]


open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
theorem _root_.GlobalTheory.LatticeRep.IsLatRep.comm (h : _root_.GlobalTheory.LatticeRep.IsLatSystem σ w γ W lam A ρ) (hO : _root_.GlobalTheory.LatticeRep.IsLatRep W lam A ρ Om) (φ : M →ₗ[ℂ] M)
    (hφ : ∀ x m, φ (W x m) = W x (φ m)) (g : Γ) (m : M) : Om g (φ m) = φ (Om g m) := by
  refine _root_.GlobalTheory.LatticeRep.transl_induction (p := fun m => Om g (φ m) = φ (Om g m))
    h.2.2.2.1 (fun x v hv => ?_) ?_
    (fun a b ha hb => ?_) (fun c a ha => ?_) m
  · have hφv : _root_.GlobalTheory.FinWeil.Fixes W A (φ v) := fun a ha => by rw [← hφ, hv a ha]
    rw [hφ, hO.1, hO.1, hO.2 g _ hφv, hO.2 g _ hv, hφ]
    congr 1
    unfold _root_.GlobalTheory.FinWeil.normOp
    rw [map_smul, map_sumOp_of_commute φ (h.2.2.2.2.2 g) hφ]
  · simp
  · simp only [map_add (f := _), ha, hb]
  · simp only [map_smul, ha]

end GlobalTheory.LatticeRep

end
end

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
open GlobalTheory.FinLatF

namespace PositivityTheory.ThKW.LatA

theorem sum_four_eq_trace {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (P : Matrix (Fin n) (Fin n) A)
    (Q : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a = (P * (y.map σ)ᵀ * Q * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Eq.symm ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_unitary {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (Q g : Matrix (Fin m) (Fin m) A)
    (P P' k : Matrix (Fin n) (Fin n) A) (hP : P * P' = 1) (hg : (g.map σ)ᵀ * Q * g = Q)
    (hk : (k.map σ)ᵀ * P' * k = P') (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ ((g * y * k) c b) * Q c d * (g * x * k) d a =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a := by
  have h1 : (P * (k.map σ)ᵀ * P') * k = 1 := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc P, hk, hP]
  have h2 : k * (P * (k.map σ)ᵀ * P') = 1 := mul_eq_one_comm.1 h1
  have hP' : P' * P = 1 := mul_eq_one_comm.1 hP
  have hk' : k * P * (k.map σ)ᵀ = P := by
    calc k * P * (k.map σ)ᵀ = k * P * (k.map σ)ᵀ * (P' * P) := by rw [hP', Matrix.mul_one]
      _ = (k * (P * (k.map σ)ᵀ * P')) * P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [h2, Matrix.one_mul]
  have e : P * ((g * y * k).map σ)ᵀ * Q * (g * x * k) =
      (P * (k.map σ)ᵀ * ((y.map σ)ᵀ * ((g.map σ)ᵀ * Q * g) * x)) * k := by
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [sum_four_eq_trace, sum_four_eq_trace, e, hg, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc k, hk']
  simp only [Matrix.mul_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ}

theorem sig_sig {B : Base F E} (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hS.2)]
    exact Matrix.map_one _ (incAF F E).map_zero (incAF F E).map_one
  exact sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E)) (JS.map (incAF F E)) (mtF σ JS g⁻¹)
    h1 h.2 (g⁻¹).2 x y

theorem symplOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [hOF_actOF hS]

theorem gamFF_rhoFF (hS : IsHermND σ JS) (p : GAF σ JS × GAF σ JT) (x y : XFF F E nS nT) :
    gamFF σ JS JT ξ₀ ψ (rhoFF σ JS JT p x) (rhoFF σ JS JT p y) = gamFF σ JS JT ξ₀ ψ x y := by
  rw [gamFF, gamFF, coe_rhoFF, coe_rhoFF, symplOF_actOF hS]

theorem idem_add : pairA F 1 0 + pairA F 0 1 = 1 := by
  refine Prod.ext ?_ ?_
  · show (1 : Ainf F) + 0 = 1
    rw [add_zero]
  · show (0 : Af F) + 1 = 1
    rw [zero_add]

theorem dec (u : WOF F E nS nT) : u = pairA F 1 0 • u + pairA F 0 1 • u := by
  rw [← add_smul, idem_add, one_smul]

theorem map_sub' {R : Type} [CommRing R] (φ : AEF F E →+* R) (u v : WOF F E nS nT) :
    (u - v).map φ = u.map φ - v.map φ := by
  ext i j
  exact φ.map_sub _ _

theorem real_eq {u v : WOF F E nS nT} (h : u.map (infPartF F E) = v.map (infPartF F E)) :
    pairA F 1 0 • u = pairA F 1 0 • v := by
  rw [← sub_eq_zero, ← smul_sub]
  exact GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (by rw [map_sub', h, sub_self])

theorem fin_eq {u v : WOF F E nS nT} (h : u.map (finPartF F E) = v.map (finPartF F E)) :
    pairA F 0 1 • u = pairA F 0 1 • v := by
  rw [← sub_eq_zero, ← smul_sub]
  exact GlobalTheory.HeisThetaF.smul_eq_zero_of_map_finPartF (by rw [map_sub', h, sub_self])

theorem map_act_fin {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS) (hh : h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT)
    (u : WOF F E nS nT) : (actOF σ JS JT g h u).map (finPartF F E) = u.map (finPartF F E) := by
  have h1 : (mtF σ JS g⁻¹).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h2 : (mtF σ JT h).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  unfold actOF
  rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem rhoFF_real {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS) (hh : h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT)
    (x : XFF F E nS nT) : rhoFF σ JS JT (g, h) x = x := by
  apply XFF.ext
  rw [dec (rhoFF σ JS JT (g, h) x : WOF F E nS nT), real_eq ((rhoFF σ JS JT (g, h) x).fin.trans x.fin.symm), coe_rhoFF,
    fin_eq (map_act_fin hg hh _), ← dec]

variable {hc : HeisClosedF σ JS JT ξ₀ ψ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {w : 𝓞 E}
  {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)}

theorem sys (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (h : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om) :
    GlobalTheory.LatticeRep.IsLatSystem (sgOF σ) w (gamFF σ JS JT ξ₀ ψ) (opFF hc w) lam (latF F E nS nT Λ) (rhoFF σ JS JT) :=
  ⟨isHeis_opFF hσ hS hT hξ hc h.hw, h.good, h.sd, h.span, gamFF_rhoFF hS, h.fin⟩

theorem rep (h : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om) :
    GlobalTheory.LatticeRep.IsLatRep (opFF hc w) lam (latF F E nS nT Λ) (rhoFF σ JS JT) Om :=
  ⟨h.op, h.vac⟩

theorem eventually_fix (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (h : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om) (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) :
    ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f := by
  have hs := sys hσ hS hT hξ h
  have H := hs.1
  refine GlobalTheory.LatticeRep.transl_induction hs.2.2.2.1 (p := fun f => ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f)
    (fun x e he => ?_) (Filter.Eventually.of_forall fun p => map_zero _) (fun u v hu hv => ?_) (fun c u hu => ?_) f
  · obtain ⟨N, hN, hNU⟩ := h.lev (w • x)
    filter_upwards [h.near, h.near' x N hN] with p hp hp'
    obtain ⟨l, hl, e1⟩ := hp'
    have e2 : gamFF σ JS JT ξ₀ ψ (w • x) (N • l) = 1 := by
      rw [gamFF, ← symplOHF_add_self, AddChar.map_add_eq_mul, XFF.coe_nsmul, hNU l hl, one_mul]
    have e4 := H.comp x (N • l) e
    rw [he _ (nsmul_mem hl N), e2, one_smul] at e4
    rw [h.op, (rep h).fix_of_map_le hs (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he, e1, ← e4]
  · filter_upwards [hu, hv] with p h3 h4 using by rw [map_add (f := _), h3, h4]
  · filter_upwards [hu] with p h3 using by rw [map_smul, h3]

end PositivityTheory.ThKW.LatA

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.FixedOfMem
noncomputable section

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Formalism.IndefR.LiftF
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeExtend GlobalTheory.HeckeExtend.AtInf GlobalTheory.SplitDetCharF

namespace PositivityTheory.ThKW.Eta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def UI (σ : E →ₐ[F] E) : Subgroup (AF F ⊗[F] E)ˣ where
  carrier := {x | x ∈ GF F E ∧ (∀ e, IsSplitIdemF σ e → e * (x : AF F ⊗[F] E) = e) ∧
    (x : AF F ⊗[F] E) ∈ SE F E ∧ ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) ∈ SE F E}
  one_mem' := ⟨one_mem _, fun e _ => mul_one e, one_mem_SE, by rw [inv_one]; exact one_mem_SE⟩
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1,
    fun e he => by rw [Units.val_mul, ← mul_assoc, hx.2.1 e he, hy.2.1 e he],
    SE_mul hx.2.2.1 hy.2.2.1, by rw [mul_inv_rev]; exact SE_mul hy.2.2.2 hx.2.2.2⟩
  inv_mem' {x} hx := ⟨inv_mem hx.1, fun e he => by
    conv_lhs => rw [← hx.2.1 e he]
    rw [mul_assoc, Units.mul_inv, mul_one], hx.2.2.2, by rw [inv_inv]; exact hx.2.2.1⟩

theorem eta_fin {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {η : (AF F ⊗[F] E)ˣ →* Circle} (hη : ResEtaF η 1)
    (a : (AF F)ˣ) (h1 : (idFF F E a : AF F ⊗[F] E) ∈ SE F E) (h2 : (idFF F E a⁻¹ : AF F ⊗[F] E) ∈ SE F E) :
    η (idFF F E (finU F (sndU F a))) = 1 := by
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := hB.cm.2.2.1 }
  have hint : ∀ t : AF F, algebraMap (AF F) (AF F ⊗[F] E) t ∈ SE F E → ∀ v : HeightOneSpectrum (𝓞 F),
      2 * t.2 v ∈ v.adicCompletionIntegers F := by
    intro t ht v
    have := GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence F E 1 t (CE_one ht)
    rw [hB.cm.2.2.1] at this
    obtain ⟨c, hc, e⟩ := this
    have e2 : evalV F v (2 • t.2) = evalV F v (1 • c) := congrArg (evalV F v) e
    rw [one_smul, map_nsmul, nsmul_eq_mul, Nat.cast_ofNat] at e2
    have e3 : 2 * t.2 v = c v := e2
    rw [e3]
    exact hc v
  have hn : finU F (sndU F a) ∈ GlobalTheory.QuadSymbol.normGroup F E (AF F) := by
    refine (GlobalTheory.IdeleNormChar.mem_normGroup_iff_everywhereNorm E _).2 ⟨fun v => ?_, fun w => ?_⟩
    · exact local_norm hB v _ (hint _ h1 v) (hint _ h2 v)
    · have : GlobalTheory.IdeleNormChar.infComp (finU F (sndU F a)) w = 1 := Units.ext rfl
      rw [this]
      exact one_mem _
  obtain ⟨x, hx⟩ := hn
  obtain ⟨⟨η₀, h0⟩, h⟩ := hη
  rw [h η₀ h0, ← hx, h0.2.2.1 x, one_pow]

theorem fixed_of_mem {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v)
    {M N : ℕ} (hN : ∀ y : F, IsIntegral ℤ y → (∀ φ : F →+* ℂ, ‖φ y‖ ≤ 8) →
      ∀ c ∈ v.adicCompletionIntegers F, algebraMap F (Fv F v) y = N • c → y = 0)
    {x w : (AF F ⊗[F] E)ˣ} (hx : x ∈ UI σ) (hw : w ∈ WE F E (M * N)) (k : Eˣ) (a : (AF F)ˣ)
    (h : Units.map (incAF F E).toMonoidHom k * idFF F E a * w = x) : σ k = (k : E) := by
  obtain ⟨hσσ, hfix⟩ := GlobalTheory.T.cmExtension_conjugation_involutive_fixedField F E σ hcm
  let cU : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (cA σ).toMonoidHom
  have hcW : cU w ∈ WE F E (M * N) := by
    refine ⟨?_, ?_⟩
    · have := CE_cA σ hw.1
      rwa [map_sub, map_one] at this
    · have := CE_cA σ hw.2
      rw [map_sub, map_one] at this
      rw [← map_inv]
      exact this
  have hfixa : cU (idFF F E a) = idFF F E a := Units.ext ((cA σ).commutes (a : AF F))
  have hcinc : cU (Units.map (incAF F E).toMonoidHom k) =
      Units.map (incAF F E).toMonoidHom (Units.map σ.toMonoidHom k) := Units.ext rfl
  let ζ : Eˣ := Units.map σ.toMonoidHom k * k⁻¹
  have hw' : w * (cU w)⁻¹ ∈ WE F E (M * N) := mul_mem hw (inv_mem hcW)
  have hζ : Units.map (incAF F E).toMonoidHom ζ = cU x * x⁻¹ * (w * (cU w)⁻¹) := by
    rw [← h]
    simp only [ζ, map_mul, map_inv, hfixa, hcinc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hζ' : incAF F E (ζ : E) = cA σ (x : AF F ⊗[F] E) * ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) *
      ((w * (cU w)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := congrArg Units.val hζ
  have hζS : incAF F E (ζ : E) ∈ SE F E := by
    rw [hζ']
    exact SE_mul (SE_mul (cA_mem_SE σ hx.2.2.1) hx.2.2.2) (mem_SE_of_CE hw'.1)
  have hζS' : incAF F E (σ ζ) ∈ SE F E := cA_mem_SE σ hζS
  obtain ⟨e, he, he', hcc, hφ⟩ := exists_idem hcm τ
  have q1 : phi τ ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 := by
    have := congrArg (phi τ) ((inv_mem hx).2.1 e he)
    rwa [map_mul, hφ, one_mul] at this
  have q2 : phi τ (cA σ (x : AF F ⊗[F] E)) = 1 := by
    have h1 := congrArg (cAF σ) (hx.2.1 _ he')
    rw [map_mul, hcc] at h1
    have := congrArg (phi τ) h1
    rwa [map_mul, hφ, one_mul] at this
  obtain ⟨s, hs, es⟩ := mem_CE.1 hw'.1
  have q3 : τ (ζ : E) - 1 = (M * N) • phi τ s := by
    rw [← phi_inc, hζ', map_mul, map_mul, q1, q2, one_mul, one_mul, ← map_nsmul, es, map_sub, map_one]
  have hζv : (ζ : E) = σ k * (k : E)⁻¹ := by simp [ζ]
  obtain ⟨y, hy⟩ := hfix (((ζ : E) - 1) * σ ((ζ : E) - 1)) (by rw [map_mul, hσσ, mul_comm])
  have hyS : algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) ∈ SE F E := by
    rw [← incAF_algebraMap, hy, map_mul, map_sub σ, map_one, map_sub, map_sub, map_one]
    exact SE_mul (sub_mem hζS one_mem_SE) (sub_mem hζS' one_mem_SE)
  have hy2 := GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence F E 1 _ (CE_one hyS)
  rw [hcm.2.2.1, ← map_nsmul] at hy2
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_integer_of_algebraMap_mem_adelesFiniteMultiple F _ 1 one_pos hy2
  have hy0 : 2 • y = 0 := by
    refine hN (2 • y) ?_ (fun φ => ?_) (2 * (M • phi τ s) * (phi τ (incAF F E (σ ζ)) - 1)) ?_ ?_
    · rw [hr, Nat.cast_one, one_mul]
      exact r.2
    · obtain ⟨τ', hτ⟩ := exists_emb_ext (E := E) φ
      have hφ : φ y = τ' (algebraMap F E y) := by rw [← hτ]; rfl
      have hτσ := hcm.2.2.2 τ'
      have hk0 : τ' (k : E) ≠ 0 := (map_ne_zero τ').2 k.ne_zero
      have hζn : ‖τ' (ζ : E)‖ = 1 := by
        rw [hζv, map_mul, map_inv₀, hτσ, norm_mul, norm_inv, norm_star]
        exact mul_inv_cancel₀ (norm_ne_zero_iff.2 hk0)
      have hxn : ‖τ' ((ζ : E) - 1)‖ ≤ 2 := by
        calc ‖τ' ((ζ : E) - 1)‖ = ‖τ' (ζ : E) - 1‖ := by rw [map_sub, map_one]
        _ ≤ ‖τ' (ζ : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hζn, norm_one]; norm_num
      rw [map_nsmul, nsmul_eq_mul, norm_mul, hφ, hy, map_mul, hτσ, norm_mul, norm_star]
      have : ‖((2 : ℕ) : ℂ)‖ = 2 := by simp
      rw [this]
      nlinarith [norm_nonneg (τ' ((ζ : E) - 1))]
    · refine mul_mem (mul_mem ?_ (nsmul_mem (phi_mem τ hs) M)) (sub_mem (phi_mem τ hζS') (one_mem _))
      rw [← one_add_one_eq_two]
      exact add_mem (one_mem _) (one_mem _)
    · rw [map_nsmul, ← τ.commutes, hy, map_mul, map_sub, map_one, q3, map_sub σ, map_one, map_sub, map_one, phi_inc]
      simp only [nsmul_eq_mul]
      push_cast
      ring
  have hy1 : y = 0 := by simpa using hy0
  rw [hy1, map_zero] at hy
  have hζ1 : (ζ : E) = 1 := by
    rcases mul_eq_zero.1 hy.symm with h | h
    · exact sub_eq_zero.1 h
    · exact sub_eq_zero.1 ((map_eq_zero σ).1 h)
  rw [hζv] at hζ1
  exact (mul_inv_eq_one₀ k.ne_zero).1 hζ1

theorem key {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {η : (AF F ⊗[F] E)ˣ →* Circle} (hc : Continuous η)
    (hη : ResEtaF η 1) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ UI σ,
      x ∈ ((Units.map (incAF F E).toMonoidHom).range ⊔ (idFF F E).range) ⊔ WE F E N → η x = 1 := by
  obtain ⟨M, hM, hMk⟩ := exists_level η hc
  obtain ⟨N, hN, hNk⟩ := exists_sep B.v₁
  refine ⟨M * N, Nat.mul_pos hM hN, fun x hx hV => ?_⟩
  obtain ⟨y, hy, w, hw, hyw⟩ := Subgroup.mem_sup.1 hV
  obtain ⟨_, ⟨k, rfl⟩, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hy
  have hk := fixed_of_mem hB.cm B.τ₁ hNk hx hw k a hyw
  obtain ⟨f, hf⟩ := (GlobalTheory.T.cmExtension_conjugation_involutive_fixedField F E σ hB.cm).2 k hk
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact k.ne_zero hf.symm
  let fU : (AF F)ˣ := Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 f hf0)
  have hinc : Units.map (incAF F E).toMonoidHom k = idFF F E fU := by
    apply Units.ext
    show incAF F E (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) f)
    rw [← hf, incAF_algebraMap]
  rw [hinc, ← map_mul] at hyw
  generalize fU * a = a' at hyw
  have e1 : idFF F E a' = x * w⁻¹ := by rw [← hyw, mul_inv_cancel_right]
  have e2 : idFF F E a'⁻¹ = x⁻¹ * w := by rw [map_inv, e1, mul_inv, inv_inv]
  have h1 := eta_fin hB hη a' (by rw [e1]; exact SE_mul hx.2.2.1 (mem_SE_of_CE hw.2))
    (by rw [e2]; exact SE_mul hx.2.2.2 (mem_SE_of_CE hw.1))
  let p : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (cut (fI F E) fI_idem)
  have hp : ∀ z : (AF F ⊗[F] E)ˣ, (p z : AF F ⊗[F] E) = (1 - fI F E) + fI F E * z := fun _ => rfl
  have px : p x = x := Units.ext (by
    have : (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E := hx.1
    rw [hp]
    linear_combination -this)
  have pa : p (idFF F E a') = idFF F E (finU F (sndU F a')) := Units.ext (by
    rw [hp]
    show 1 - algebraMap (AF F) (AF F ⊗[F] E) (uFin F) + algebraMap (AF F) (AF F ⊗[F] E) (uFin F) *
      algebraMap (AF F) (AF F ⊗[F] E) (a' : AF F) = algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 (a' : AF F).2)
    rw [← map_mul, ← map_one (algebraMap (AF F) (AF F ⊗[F] E)), ← map_sub, ← map_add (f := _), uFin_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) - 0 + 0 = 1
      simp
    · show (1 : Af F) - 1 + (a' : AF F).2 = (a' : AF F).2
      simp)
  have pC : ∀ z : (AF F ⊗[F] E)ˣ, (z : AF F ⊗[F] E) - 1 ∈ CE F E (M * N) → (p z : AF F ⊗[F] E) - 1 ∈ CE F E M := by
    intro z hz
    obtain ⟨s, hs, e⟩ := mem_CE.1 (CE_mul hz)
    refine mem_CE.2 ⟨fI F E * s, SE_mul fI_mem hs, ?_⟩
    rw [← mul_smul_comm, e, hp]
    ring
  have h2 : η (p w) = 1 := by
    refine hMk _ ⟨pC w hw.1, by rw [← map_inv]; exact pC _ hw.2⟩ ?_
    show (1 - fI F E) * (p w : AF F ⊗[F] E) = 1 - fI F E
    rw [hp]
    linear_combination (1 - (w : AF F ⊗[F] E)) * (fI_idem (F := F) (E := E))
  rw [← px, ← hyw, map_mul, map_mul, pa, h1, h2, mul_one]

end PositivityTheory.ThKW.Eta

namespace PositivityTheory.ThKW

open Eta

theorem exists_eta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∃ η : (AF F ⊗[F] E)ˣ →* Circle,
      IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) ∧ UnramInert σ η := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨η, h1, h2, h3⟩ := GlobalTheory.EtaCMType.exists_eta_cmType F E σ B hB
  obtain ⟨N, hN, hk⟩ := key hB h1.1 h2
  obtain ⟨ν, hV, hU⟩ := exists_ext _ _ η hk
  have hW : ∀ z ∈ WE F E N, ν z = 1 := fun z hz => hV z (Subgroup.mem_sup_right hz)
  have hWo : IsOpen (WE F E N : Set (AF F ⊗[F] E)ˣ) := by
    have ho := CE_isOpen F E N hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hν : Continuous ν := by
    refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hWo.mem_nhds (one_mem _)] with z hz
    exact (hW z hz).symm
  refine ⟨η * ν⁻¹, ⟨h1.1.mul hν.inv, fun x => ?_⟩, ⟨h2.1, fun e he a => ?_⟩, fun z hz => ?_, fun x a b c d => ?_⟩
  · change η _ * (ν _)⁻¹ = 1
    rw [h1.2, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨x, rfl⟩)), inv_one, one_mul]
  · change η _ * (ν _)⁻¹ = _
    rw [h2.2 e he, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨a, rfl⟩)), inv_one, mul_one]
  · change ((η z * (ν z)⁻¹ : Circle) : ℂ) = _
    have : z ∈ WE F E N := by
      refine ⟨mem_CE_of_atInf F E _ hN _ hz, mem_CE_of_atInf F E _ hN _ ?_⟩
      intro u hu
      have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 =
          -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
        rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
      rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]
    rw [hW z this, inv_one, mul_one]
    exact h3 z hz
  · change η _ * (ν _)⁻¹ = 1
    have hx : x ∈ UI σ := by
      refine ⟨?_, b, mem_SE_of_fin c, mem_SE_of_fin d⟩
      show (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E
      rw [← sub_eq_zero, ← mul_sub_one]
      refine adele_tensor_ext _ ?_ ?_
      · rw [map_mul, map_sub _ (x : AF F ⊗[F] E), a, map_one, sub_self, mul_zero]
      · rw [map_mul, map_sub, map_one, fin_fI, sub_self, zero_mul]
    rw [hU x hx, mul_inv_cancel]

end PositivityTheory.ThKW

end
end
