module

public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriContraction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetAdjointForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetOppositeNeg
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetOppositeNeg
open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliAntipode

theorem unop_ofFn_prod {A : Type*} [Ring A] : ∀ {t : ℕ} (f : Fin t → Aᵐᵒᵖ),
    MulOpposite.unop (List.ofFn f).prod = (List.ofFn fun i => MulOpposite.unop (f i.rev)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul, unop_ofFn_prod (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => MulOpposite.unop (f i.rev)), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]

theorem ofFn_prod_neg {A : Type*} [Ring A] [Algebra ℂ A] : ∀ {t : ℕ} (g : Fin t → A),
    (List.ofFn fun k => -g k).prod = ((-1 : ℂ) ^ t) • (List.ofFn g).prod
  | 0, g => by simp
  | t + 1, g => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_neg (fun k => g k.succ), List.ofFn_succ (f := g),
      List.prod_cons, pow_succ, mul_comm, mul_smul, neg_mul, mul_smul_comm, neg_one_smul]

theorem Tm_op_neg {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ)
    (i j : Fin n) :
    Tm (fun i j => MulOpposite.op (-X i j)) w i j = MulOpposite.op (-(Tm X (-w) i j)) := by
  unfold Tm
  by_cases h : i = j
  · simp [h, MulOpposite.algebraMap_apply, add_comm]
  · simp [h]

theorem arg_rev {t : ℕ} (v : ℂ) (j : Fin t) :
    -(v - (((Fin.rev j : Fin t) : ℕ) : ℂ)) = ((t : ℂ) - 1 - v) - ((j : ℕ) : ℂ) := by
  have hj := j.isLt
  rw [Fin.val_rev, Nat.cast_sub (by omega : (j : ℕ) + 1 ≤ t)]
  push_cast
  ring

theorem unop_term {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (v : ℂ)
    (σ : Equiv.Perm (Fin n)) :
    MulOpposite.unop ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Aᵐᵒᵖ) *
        (List.ofFn fun k : Fin n =>
          Tm (fun i j => MulOpposite.op (-X i j)) (v - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod) =
      ((-1 : ℂ) ^ n) • ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun j : Fin n =>
          Tm X (((n : ℂ) - 1 - v) - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod) := by
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast, unop_ofFn_prod]
  simp only [Tm_op_neg, MulOpposite.unop_op, id, arg_rev]
  rw [ofFn_prod_neg, smul_mul_assoc, ← Int.cast_comm]

theorem qminor_id_rev {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ) :
    qminor X id (id ∘ (Fin.revPerm : Equiv.Perm (Fin n))) w =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
        ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
          (List.ofFn fun j : Fin n => Tm X (w - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod := by
  unfold qminor
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ (fun σ => ?_)).symm
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Equiv.Perm.mul_apply, Fin.revPerm_apply,
    Function.comp_apply, id, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, Int.cast_comm]

theorem unop_qdet_op_neg (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (v : ℂ) :
    MulOpposite.unop (qdet (fun i j => MulOpposite.op (-X i j)) v) =
      ((-1 : ℂ) ^ n) • qdet X ((n : ℂ) - 1 - v) := by
  have hs := quantumMinorColSkew_holds A n n X hX id id (Fin.revPerm : Equiv.Perm (Fin n)) ((n : ℂ) - 1 - v)
  rw [qminor_id_rev] at hs
  have hu : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have h2 := congrArg (fun x => (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) * x) hs
  simp only [← mul_assoc, hu, one_mul] at h2
  have h3 : qdet X ((n : ℂ) - 1 - v) = _ := h2.symm
  rw [h3]
  unfold qdet qminor
  rw [Finset.unop_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun σ _ => unop_term X v σ

end GlobalTheory.CompanionTheory.CapelliAntipode
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetOppositeNegStatement
open Formalism.REAL
alias GlobalTheory.T.quantum_det_opposite_neg := GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetAdjointForm
open Formalism.REAL

namespace GlobalTheory.CompanionTheory.CapelliAdj

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def HasAdj (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (T S : Module.End ℂ V) : Prop :=
  ∀ φ ψ : V, B (T φ) ψ = B φ (S ψ)

theorem HasAdj.mul {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {T T' S S' : Module.End ℂ V}
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T * T') (S' * S) := by
  intro φ ψ
  show B (T (T' φ)) ψ = B φ (S' (S ψ))
  rw [h (T' φ) ψ, h' φ (S ψ)]

theorem HasAdj.one (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : HasAdj B 1 1 := by
  intro φ ψ
  rfl

theorem HasAdj.add {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {T T' S S' : Module.End ℂ V}
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T + T') (S + S') := by
  intro φ ψ
  simp only [LinearMap.add_apply, map_add (f := _), h φ ψ, h' φ ψ]

theorem HasAdj.zero (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : HasAdj B 0 0 := by
  intro φ ψ
  simp

theorem HasAdj.ofFn {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} :
    ∀ (t : ℕ) (f : Fin t → Module.End ℂ V) (g : Fin t → (Module.End ℂ V)ᵐᵒᵖ),
      (∀ k, HasAdj B (f k) (MulOpposite.unop (g k))) →
      HasAdj B (List.ofFn f).prod (MulOpposite.unop (List.ofFn g).prod) := by
  intro t
  induction t with
  | zero =>
    intro f g _
    simpa using HasAdj.one B
  | succ t ih =>
    intro f g hk
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul]
    exact (hk 0).mul (ih _ _ fun k => hk k.succ)

private theorem hasAdj_algebraMap_lemma (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (u : ℂ) :
    HasAdj B (algebraMap ℂ (Module.End ℂ V) u) (algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u)) := by
  intro φ ψ
  simp [Module.algebraMap_end_apply]

theorem HasAdj.tm {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {n : ℕ} {X Y : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (u : ℂ) (i j : Fin n) :
    HasAdj B (Tm X u i j)
      (MulOpposite.unop (Tm (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) u) i j)) := by
  have h1 : HasAdj B (if i = j then algebraMap ℂ (Module.End ℂ V) u else 0)
      (if i = j then algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u) else 0) := by
    split_ifs
    · exact hasAdj_algebraMap_lemma B u
    · exact HasAdj.zero B
  have h2 : HasAdj B (X i j) (-Y i j) := by
    intro φ ψ
    rw [h i j φ ψ, LinearMap.neg_apply, map_neg]
  have e1 : Tm X u i j = (if i = j then algebraMap ℂ (Module.End ℂ V) u else 0) + X i j := rfl
  have e2 : MulOpposite.unop (Tm (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) u) i j)
      = (if i = j then algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u) else 0) + -Y i j := by
    unfold Tm
    split_ifs <;> simp [MulOpposite.algebraMap_apply]
  rw [e1, e2]
  exact h1.add h2

theorem HasAdj.intCast (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (z : ℤ) :
    HasAdj B (z : Module.End ℂ V) (z : Module.End ℂ V) := by
  intro φ ψ
  simp [Module.End.intCast_apply]

theorem HasAdj.sum {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {ι : Type*} (s : Finset ι)
    (f g : ι → Module.End ℂ V) (h : ∀ i ∈ s, HasAdj B (f i) (g i)) :
    HasAdj B (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasAdj.zero B
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem hasAdj_qdet {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {n : ℕ} {X Y : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) :
    HasAdj B (qdet X v)
      (MulOpposite.unop (qdet (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) v))) := by
  unfold qdet qminor
  have e : ∀ (F : Equiv.Perm (Fin n) → (Module.End ℂ V)ᵐᵒᵖ),
      MulOpposite.unop (∑ σ, F σ) = ∑ σ, MulOpposite.unop (F σ) := fun F =>
    map_sum (MulOpposite.opAddEquiv.symm : (Module.End ℂ V)ᵐᵒᵖ ≃+ Module.End ℂ V) F Finset.univ
  rw [e]
  refine HasAdj.sum _ _ _ fun σ _ => ?_
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast]
  refine (HasAdj.intCast B _).mul ?_
  apply HasAdj.ofFn
  intro k
  have hk := HasAdj.tm h (v - ((k : ℕ) : ℂ)) (σ k) k
  simpa [map_sub, map_natCast] using hk

theorem adj_qdet (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ)
    (X Y : Fin n → Fin n → Module.End ℂ V) (hY : GlRel Y)
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) (φ ψ : V) :
    B (qdet X v φ) ψ =
      B φ ((((-1 : ℂ) ^ n) • qdet Y ((n : ℂ) - 1 - (starRingEnd ℂ) v)) ψ) := by
  rw [hasAdj_qdet h v φ ψ, GlobalTheory.T.quantum_det_opposite_neg (Module.End ℂ V) n Y hY ((starRingEnd ℂ) v)]

end GlobalTheory.CompanionTheory.CapelliAdj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetAdjointFormStatement
open Formalism.REAL
alias GlobalTheory.T.quantum_det_adjoint_form := GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GLTransitiveNonzeroVectors
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GLTransitiveNonzeroVectors
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

namespace GlobalTheory.CompanionTheory.TyFin.RowTrans

theorem exists_linearEquiv_apply_eq_of_ne_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : ∃ e : V ≃ₗ[K] V, e x = y := by
  have hx1 : (LinearEquiv.toSpanNonzeroSingleton K V x hx).symm
      ⟨x, Submodule.mem_span_singleton_self x⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton K V x hx).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton K V y hy))
  refine ⟨g, ?_⟩
  have h := hg ⟨x, Submodule.mem_span_singleton_self x⟩
  rw [LinearEquiv.trans_apply, hx1, LinearEquiv.toSpanNonzeroSingleton_one] at h
  exact h.symm

theorem gl_transitive_rows : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by
  intro K _ _ _ j r r' hr hr'
  obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.TyFin.RowTrans.exists_linearEquiv_apply_eq_of_ne_zero (K := K) hr hr'
  have h1 : (e.symm : (Fin j → K) →ₗ[K] Fin j → K) ∘ₗ (e : (Fin j → K) →ₗ[K] Fin j → K) =
      LinearMap.id := LinearMap.ext fun v => by simp
  have h2 : (e : (Fin j → K) →ₗ[K] Fin j → K) ∘ₗ (e.symm : (Fin j → K) →ₗ[K] Fin j → K) =
      LinearMap.id := LinearMap.ext fun v => by simp
  refine ⟨⟨(LinearMap.toMatrix' (e : (Fin j → K) →ₗ[K] Fin j → K)).transpose,
    (LinearMap.toMatrix' (e.symm : (Fin j → K) →ₗ[K] Fin j → K)).transpose, ?_, ?_⟩, ?_⟩
  · rw [← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  · change Matrix.vecMul r (LinearMap.toMatrix' (e : (Fin j → K) →ₗ[K] Fin j → K)).transpose = r'
    rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
    exact he

end GlobalTheory.CompanionTheory.TyFin.RowTrans
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GLTransitiveNonzeroVectorsStatement
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
alias GlobalTheory.T.GL_transitive_nonzero_vectors := GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitDivisibleOfVanishingLevel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitDivisibleOfVanishingLevel
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.Tower

theorem rho_lim {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W} (L : LSeq l S S') (x : S.lim)
    (b c : ℕ) (h : b ≤ c) : L.ρ c b (x.1 c) = x.1 b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact L.ρ_self b _
  | succ d ih =>
    have h' := L.ρ_succ (b + d) b (Nat.le_add_right _ _) (x.1 (b + d + 1))
    rw [x.2 (b + d), ih (Nat.le_add_right _ _)] at h'
    exact h'

theorem lim_eq_pow_smul : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'),
    (∀ n, IsArtinian W (S.M n)) → ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y := by
  intro W _ l S S' L hA n x hx
  have hex : ∀ a, ∃ y, L.ν a (n + a) y = x.1 (n + a) := fun a =>
    L.ex₁ a n (n + a) (Nat.add_comm _ _) _ (by rw [rho_lim L x n (n + a) (Nat.le_add_right _ _), hx])
  choose y hy using hex
  have hN : ∀ a w, w ∈ LinearMap.ker (L.ν (a + 1) (n + (a + 1))) →
      S.r a w ∈ LinearMap.ker (L.ν a (n + a)) := by
    intro a w hw
    have hw' : L.ν (a + 1) (n + a + 1) w = 0 := hw
    rw [LinearMap.mem_ker, ← L.ν_r a (n + a) (Nat.le_add_left _ _), hw', map_zero]
  have hc : ∀ a, S.r a (y (a + 1)) - y a ∈ LinearMap.ker (L.ν a (n + a)) := by
    intro a
    have h1 : L.ν (a + 1) (n + a + 1) (y (a + 1)) = x.1 (n + a + 1) := hy (a + 1)
    rw [LinearMap.mem_ker, map_sub, ← L.ν_r a (n + a) (Nat.le_add_left _ _), h1, x.2 (n + a), hy a,
      sub_self]
  obtain ⟨z, hz⟩ := GlobalTheory.T.artinian_limit_lift_of_compatible W S hA (fun a => LinearMap.ker (L.ν a (n + a))) y hN hc
  have key : ∀ a, ((l : W) ^ n) • z.1 (n + a) = x.1 (n + a) := by
    intro a
    have h1 := L.ν_ρ a (n + a) (Nat.le_add_left _ _) (z.1 (n + a))
    have h2 : L.ν a (n + a) (z.1 a) = x.1 (n + a) := by
      have h3 : L.ν a (n + a) (z.1 a - y a) = 0 := hz a
      rw [map_sub, hy a, sub_eq_zero] at h3
      exact h3
    rw [rho_lim L z a (n + a) (Nat.le_add_left _ _), h2, Nat.add_sub_cancel] at h1
    exact h1.symm
  refine ⟨z, Subtype.ext (funext fun c => ?_)⟩
  calc x.1 c = L.ρ (n + c) c (x.1 (n + c)) := (rho_lim L x c (n + c) (Nat.le_add_left _ _)).symm
    _ = L.ρ (n + c) c (((l : W) ^ n) • z.1 (n + c)) := by rw [key]
    _ = ((l : W) ^ n) • L.ρ (n + c) c (z.1 (n + c)) := map_smul _ _ _
    _ = ((l : W) ^ n) • z.1 c := by rw [rho_lim L z c (n + c) (Nat.le_add_left _ _)]

end GlobalTheory.CompanionTheory.Tower
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitDivisibleOfVanishingLevelStatement
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
alias GlobalTheory.T.limit_divisible_of_vanishing_level := GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdditiveCharacterSumOrthogonality
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdditiveCharacterSumOrthogonality
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

namespace GlobalTheory.CompanionTheory.TyFin.Orth

theorem sum_inv_addChar_mul_left (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : K) :
    (∑ t : K, (ψ₀ (t * x))⁻¹) = if x = 0 then (Fintype.card K : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx]
    have hbij : Function.Bijective (fun t : K => -(t * x)) := by
      refine ⟨fun a b h => ?_, fun b => ⟨-(b * x⁻¹), ?_⟩⟩
      · exact mul_right_cancel₀ hx (neg_injective h)
      · simp [hx]
    have h1 : (∑ t : K, (ψ₀ (t * x))⁻¹) = ∑ t : K, ψ₀ (-(t * x)) :=
      Finset.sum_congr rfl fun t _ => (AddChar.map_neg_eq_inv ψ₀ (t * x)).symm
    rw [h1, hbij.sum_comp (fun u => ψ₀ u)]
    exact AddChar.sum_eq_zero_of_ne_one hψ

theorem sum_inv_addChar_dot (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : Fin j → K) :
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹)
      = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by
  have h1 : ∀ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹ = ∏ i, (ψ₀ (r i * x i))⁻¹ := by
    intro r
    have hs : ∀ s : Finset (Fin j), ψ₀ (∑ i ∈ s, r i * x i) = ∏ i ∈ s, ψ₀ (r i * x i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
    rw [hs, Finset.prod_inv_distrib]
  have h2 : (∑ r : Fin j → K, ∏ i, (ψ₀ (r i * x i))⁻¹)
      = ∏ i, ∑ t : K, (ψ₀ (t * x i))⁻¹ := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [h1]
  rw [h2]
  simp_rw [sum_inv_addChar_mul_left K ψ₀ hψ]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem orth : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ),
    ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 :=
  fun K _ _ _ j ψ₀ hψ x => sum_inv_addChar_dot K j ψ₀ hψ x

end GlobalTheory.CompanionTheory.TyFin.Orth
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdditiveCharacterSumOrthogonalityStatement
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
alias GlobalTheory.T.additive_character_sum_orthogonality := GlobalTheory.CompanionTheory.TyFin.Orth.orth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducible
open CategoryTheory ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.FinRep

variable {Γ : Type} [Group Γ] [Fintype Γ]

def leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) : Representation ℂ Γ N where
  toFun g :=
    { toFun := fun n => MonoidAlgebra.of ℂ Γ g • n
      map_add' := smul_add _
      map_smul' := fun c n => smul_comm _ c n }
  map_one' := by
    ext n
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro n
    change MonoidAlgebra.of ℂ Γ (g * h) • n = MonoidAlgebra.of ℂ Γ g • MonoidAlgebra.of ℂ Γ h • n
    rw [map_mul, mul_smul]

theorem leftRep_apply (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) (g : Γ) (n : N) :
    leftRep N g n = MonoidAlgebra.of ℂ Γ g • n := rfl

theorem asAlgebraHom_leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ))
    (x : MonoidAlgebra ℂ Γ) (n : N) : Representation.asAlgebraHom (leftRep N) x n = x • n := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simp [Representation.asAlgebraHom_of, leftRep_apply]
  | add a b ha hb => simp [map_add (f := _), add_smul, ha, hb]
  | smul c a ha => simp [map_smul, ha]

instance finiteDimensional_leftIdeal (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) :
    FiniteDimensional ℂ N :=
  inferInstanceAs (FiniteDimensional ℂ (N.restrictScalars ℂ))

theorem isIrr_leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ))
    [IsSimpleModule (MonoidAlgebra ℂ Γ) N] : IsIrr (leftRep N) := by
  refine ⟨IsSimpleModule.nontrivial (MonoidAlgebra ℂ Γ) N, fun W hW => ?_⟩
  have hmem : ∀ (x : MonoidAlgebra ℂ Γ), ∀ w ∈ W, x • w ∈ W := by
    intro x w hw
    rw [← asAlgebraHom_leftRep]
    induction x using MonoidAlgebra.induction_on with
    | of g => simpa [Representation.asAlgebraHom_of] using hW g w hw
    | add a b ha hb => simpa [map_add (f := _)] using W.add_mem ha hb
    | smul c a ha => simpa [map_smul] using W.smul_mem c ha
  let W' : Submodule (MonoidAlgebra ℂ Γ) N :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun x w hw => hmem x w hw }
  rcases IsSimpleOrder.eq_bot_or_eq_top W' with h | h
  · left
    ext w
    have := congrArg (fun S : Submodule (MonoidAlgebra ℂ Γ) N => w ∈ S) h
    simpa [W'] using this
  · right
    ext w
    have := congrArg (fun S : Submodule (MonoidAlgebra ℂ Γ) N => w ∈ S) h
    simpa [W'] using this

theorem sepIrr : ReciprocityTheory.Ty.Fin.St.SepIrr := by
  intro Γ _ _ x hx
  have hsimple : ∀ N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ),
      IsSimpleModule (MonoidAlgebra ℂ Γ) N → ∀ n ∈ N, x * n = 0 := by
    intro N hN n hn
    have hS : Simple (FDRep.of (leftRep N)) :=
      (GlobalTheory.T.simple_iff_irreducible.1 Γ (FDRep.of (leftRep N))).2 (by
        simpa using isIrr_leftRep N)
    have h0 := hx _ hS
    have h1 : Representation.asAlgebraHom (leftRep N) x = 0 := by
      simpa using h0
    have h2 := asAlgebraHom_leftRep N x ⟨n, hn⟩
    rw [h1] at h2
    have h3 := congrArg Subtype.val h2
    simpa using h3.symm
  let J : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ) :=
    { carrier := {n | ∀ a, x * (a * n) = 0}
      add_mem' := fun {u v} hu hv a => by
        rw [mul_add, mul_add, hu a, hv a, add_zero]
      zero_mem' := fun a => by simp
      smul_mem' := fun c n hn a => by
        simpa [mul_assoc] using hn (a * c) }
  have hJ : (⊤ : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) ≤ J := by
    rw [← IsSemisimpleModule.sSup_simples_eq_top (R := MonoidAlgebra ℂ Γ)]
    refine sSup_le fun N hN n hn a => ?_
    exact hsimple N hN _ (by simpa using N.smul_mem a hn)
  have h1 : (1 : MonoidAlgebra ℂ Γ) ∈ J := hJ Submodule.mem_top
  simpa using h1 1

end GlobalTheory.CompanionTheory.FinRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducibleStatement
open ReciprocityTheory.Ty.Fin
alias GlobalTheory.T.separable_irreducible := GlobalTheory.CompanionTheory.FinRep.sepIrr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedCokernelLimitToLevel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedCokernelLimitToLevel
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TwCok

theorem pow_torsion_bounded {W : Type} [CommRing W] [IsNoetherianRing W] (r : W) (T : Type 1)
    [AddCommGroup T] [Module W T] [Module.Finite W T] :
    ∃ c : ℕ, ∀ (k : ℕ) (t : T), r ^ k • t = 0 → r ^ c • t = 0 := by
  haveI := isNoetherian_of_isNoetherianRing_of_finite W T
  let f : ℕ →o Submodule W T :=
    ⟨fun k => LinearMap.ker ((r ^ k) • LinearMap.id : T →ₗ[W] T), fun a b hab t ht => by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at ht ⊢
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [pow_add, mul_comm, mul_smul, ht, smul_zero]⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance f
  refine ⟨n, fun k t ht => ?_⟩
  rcases le_total k n with hkn | hnk
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [pow_add, mul_comm, mul_smul, ht, smul_zero]
  · have h1 : t ∈ f k := by
      simp only [f, OrderHom.coe_mk, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact ht
    rw [← hn k hnk] at h1
    have h2 : t ∈ LinearMap.ker ((r ^ n) • LinearMap.id : T →ₗ[W] T) := h1
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at h2
    exact h2

variable {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W}

def conn (Q : LSeq l S S') (n : ℕ) (x : S.M n) : S'.lim :=
  ⟨fun a => Q.δ n a x, fun a => Q.δ_r n a x⟩

theorem conn_smul (Q : LSeq l S S') (n : ℕ) (s : W) (x : S.M n) :
    s • conn Q n x = conn Q n (s • x) := by
  apply Subtype.ext
  funext a
  simp [conn]

theorem conn_kill (Q : LSeq l S S') (n : ℕ) (x : S.M n) : ((l : W) ^ n) • conn Q n x = 0 := by
  rw [conn_smul, Q.kill n x]
  apply Subtype.ext
  funext a
  simp [conn]

theorem lift_of_conn_zero (Q : LSeq l S S') (hA : ∀ n, IsArtinian W (S.M n)) (n : ℕ) (x : S.M n)
    (h : ∀ a, Q.δ n a x = 0) : ∃ y : S.lim, y.1 n = x := by
  classical
  have hy : ∀ m, n ≤ m → ∃ u : S.M m, Q.ρ m n u = x := fun m hm =>
    Q.ex₂ (m - n) n m (by omega) x (h _)
  let y : ∀ m, S.M m := fun m => if hm : n ≤ m then (hy m hm).choose else 0
  have hyx : ∀ m (hm : n ≤ m), Q.ρ m n (y m) = x := by
    intro m hm
    simp only [y, dif_pos hm]
    exact (hy m hm).choose_spec
  let N : ∀ m, Submodule W (S.M m) := fun m => if n ≤ m then LinearMap.ker (Q.ρ m n) else ⊤
  have hN : ∀ m (hm : n ≤ m), N m = LinearMap.ker (Q.ρ m n) := fun m hm => if_pos hm
  have hN' : ∀ m (hm : ¬ n ≤ m), N m = ⊤ := fun m hm => if_neg hm
  have hNr : ∀ m, ∀ u ∈ N (m + 1), S.r m u ∈ N m := by
    intro m u hu
    by_cases hm : n ≤ m
    · rw [hN (m + 1) (by omega), LinearMap.mem_ker] at hu
      rw [hN m hm, LinearMap.mem_ker, ← Q.ρ_succ m n hm]
      exact hu
    · rw [hN' m hm]
      exact Submodule.mem_top
  have hyr : ∀ m, S.r m (y (m + 1)) - y m ∈ N m := by
    intro m
    by_cases hm : n ≤ m
    · rw [hN m hm, LinearMap.mem_ker, map_sub, ← Q.ρ_succ m n hm, hyx (m + 1) (by omega), hyx m hm,
        sub_self]
    · rw [hN' m hm]
      exact Submodule.mem_top
  obtain ⟨z, hz⟩ := GlobalTheory.T.artinian_limit_lift_of_compatible W S hA N y hNr hyr
  refine ⟨z, ?_⟩
  have h1 := hz n
  rw [hN n le_rfl, LinearMap.mem_ker, map_sub, Q.ρ_self, Q.ρ_self, sub_eq_zero] at h1
  have h2 := hyx n le_rfl
  rw [Q.ρ_self] at h2
  rw [← h2]
  exact h1

theorem lim_cokernel_bounded : ∀ (W : Type) [CommRing W] [IsNoetherianRing W] (l : ℕ) (S S' : Sys.{1} W)
    (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → Module.Finite W S'.lim →
    ∃ c : ℕ, ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x := by
  intro W _ _ l S S' Q hA hF
  obtain ⟨c, hc⟩ := pow_torsion_bounded ((l : W)) S'.lim
  refine ⟨c, fun n x => lift_of_conn_zero Q hA n _ (fun a => ?_)⟩
  have h0 : conn Q n ((l : W) ^ c • x) = 0 := by
    rw [← conn_smul]
    exact hc n _ (conn_kill Q n x)
  have h3 := congrArg (fun v : S'.lim => (v : ∀ m, S'.M m) a) h0
  simpa [conn] using h3

end GlobalTheory.CompanionTheory.TwCok
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedCokernelLimitToLevelStatement
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
alias GlobalTheory.T.bounded_cokernel_limit_to_level := GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexAnnihilatorsDuality
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexAnnihilatorsDuality
open Matrix
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.IndexDuality

theorem relIndex_le_of_pairing {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (b : X → Y → Circle)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (H₀ H : AddSubgroup Y) (R₀ R : AddSubgroup X)
    (hfin : H₀.relIndex H ≠ 0)
    (hann : ∀ x ∈ R₀, ∀ y ∈ H₀, b x y = 1)
    (hsep : ∀ x ∈ R₀, (∀ y ∈ H, b x y = 1) → x ∈ R) :
    R.relIndex R₀ ≠ 0 ∧ R.relIndex R₀ ≤ H₀.relIndex H := by
  classical
  have hQfin : Finite (H ⧸ H₀.addSubgroupOf H) := Nat.finite_of_card_ne_zero hfin
  have hb0 : ∀ x, b x 0 = 1 := by
    intro x
    have h := hr x 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (a := b x 0) (by rw [mul_one]; exact h)).symm
  have hb0' : ∀ y, b 0 y = 1 := by
    intro y
    have h := hl 0 0 y
    rw [add_zero] at h
    exact (mul_left_cancel (a := b 0 y) (by rw [mul_one]; exact h)).symm
  let f : R₀ → H →+ Additive Circle := fun x =>
    { toFun := fun y => Additive.ofMul (b x y)
      map_zero' := by simp [hb0]
      map_add' := fun y y' => by simp [hr] }
  have hker : ∀ x : R₀, ∀ y ∈ H₀.addSubgroupOf H, f x y = 0 := by
    intro x y hy
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    simp [f, hann x x.2 y hy]
  let g : R₀ → (H ⧸ H₀.addSubgroupOf H) →+ Additive Circle := fun x =>
    QuotientAddGroup.lift (H₀.addSubgroupOf H) (f x) (hker x)
  let χ : R₀ → AddChar (H ⧸ H₀.addSubgroupOf H) Circle := fun x =>
    { toFun := fun q => Additive.toMul (g x q)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun q q' => by simp [map_add (f := _)] }
  have hχ : ∀ (x : R₀) (y : H), χ x (QuotientAddGroup.mk y) = b x y := fun x y => rfl
  let Ψ : R₀ →+ AddChar (H ⧸ H₀.addSubgroupOf H) Circle :=
    { toFun := χ
      map_zero' := by
        ext1 q
        induction q using QuotientAddGroup.induction_on with
        | H y =>
          rw [hχ]
          exact hb0' y
      map_add' := fun x x' => by
        ext1 q
        induction q using QuotientAddGroup.induction_on with
        | H y =>
          rw [hχ]
          change b (x + x') y = (χ x * χ x') (QuotientAddGroup.mk y)
          rw [AddChar.mul_apply, hχ, hχ]
          exact hl x x' y }
  have hkerle : Ψ.ker ≤ R.addSubgroupOf R₀ := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddSubgroup.mem_addSubgroupOf]
    refine hsep x x.2 (fun y hy => ?_)
    have := congrArg (fun φ : AddChar (H ⧸ H₀.addSubgroupOf H) Circle => φ (QuotientAddGroup.mk ⟨y, hy⟩)) hx
    simpa [Ψ, hχ] using this
  have : Fintype (H ⧸ H₀.addSubgroupOf H) := Fintype.ofFinite _
  have hinjC : Function.Injective fun φ : AddChar (H ⧸ H₀.addSubgroupOf H) Circle => Circle.coeHom.compAddChar φ :=
    MonoidHom.compAddChar_injective_right _ Circle.coe_injective
  have : Finite (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) := Finite.of_injective _ hinjC
  have hcardC : Nat.card (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) ≤ H₀.relIndex H := by
    have h1 := Nat.card_le_card_of_injective _ hinjC
    rw [Nat.card_eq_fintype_card (α := AddChar (H ⧸ H₀.addSubgroupOf H) ℂ), AddChar.card_eq,
      ← Nat.card_eq_fintype_card] at h1
    exact h1
  have : Finite (R₀ ⧸ Ψ.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective Ψ)
  have hkerfin : Ψ.ker.index ≤ Nat.card (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) :=
    Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective Ψ)
  have hker0 : Ψ.ker.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have hdvd := AddSubgroup.index_dvd_of_le hkerle
  have hR0 : (R.addSubgroupOf R₀).index ≠ 0 := fun h0 => hker0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  refine ⟨hR0, ?_⟩
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hker0) hdvd).trans (hkerfin.trans hcardC)

theorem relIndex_annihilator_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A₀ A P₀ P : AddSubgroup (Fin n → k)), IsCompact (A₀ : Set (Fin n → k)) →
    IsOpen (A₀ : Set (Fin n → k)) → IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → A₀ ≤ A → (∀ ξ, ξ ∈ P₀ ↔ ∀ a ∈ A₀, ψ (ξ ⬝ᵥ a) = 1) →
    (∀ ξ, ξ ∈ P ↔ ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1) → P.relIndex P₀ = A₀.relIndex A := by
  intro k _ _ _ _ ψ hψc hψ1 n A₀ A P₀ P hA₀c hA₀o hAc hAo hle hP₀ hP
  have hfin : A₀.relIndex A ≠ 0 :=
    GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen A A₀ hAc hA₀o hle
  have h1 := relIndex_le_of_pairing (fun ξ a : Fin n → k => ψ (ξ ⬝ᵥ a))
    (fun ξ ξ' a => by simp [add_dotProduct, AddChar.map_add_eq_mul])
    (fun ξ a a' => by simp [dotProduct_add, AddChar.map_add_eq_mul])
    A₀ A P₀ P hfin (fun ξ hξ a ha => (hP₀ ξ).mp hξ a ha) (fun ξ _ h => (hP ξ).mpr h)
  have h2 := relIndex_le_of_pairing (fun a ξ : Fin n → k => ψ (ξ ⬝ᵥ a))
    (fun a a' ξ => by simp [dotProduct_add, AddChar.map_add_eq_mul])
    (fun a ξ ξ' => by simp [add_dotProduct, AddChar.map_add_eq_mul])
    P P₀ A A₀ h1.1 (fun a _ ξ hξ => (hP ξ).mp hξ a ‹_›) (fun a _ h => by
      by_contra hna
      obtain ⟨η, hη, hne⟩ := GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne k ψ hψc hψ1 n A₀ hA₀c hA₀o a hna
      exact hne (h η ((hP₀ η).mpr hη)))
  exact le_antisymm h1.2 h2.2

end GlobalTheory.CompanionTheory.IndexDuality
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexAnnihilatorsDualityStatement
open Matrix
open scoped Topology
alias GlobalTheory.T.relIndex_annihilators_duality := GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq
end
end
