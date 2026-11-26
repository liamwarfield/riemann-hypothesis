module

public import Formalism.MahlerMeasure.StatementD
public import Formalism.SmithDeterminants.StatementGram
public import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelAct

@[expose] public section

section -- merged from Formalism.MahlerMeasure.MahlerMeasureProofs.SmithZp
section -- merged from Formalism.SmithDeterminants.TruncationChainBoundNonnegExponents
section -- merged from Formalism.SmithDeterminants.DivisibilityChains.SmithExists
section -- merged from Formalism.SmithDeterminants.StatementDVR
open Finset

noncomputable section

namespace Formalism.A

structure SmithData {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (y : M →ₗ[R] M) (d : ℕ) where
  b : Module.Basis (Fin d) R M
  b' : Module.Basis (Fin d) R M
  a : Fin d → R
  hy : ∀ i, y (b i) = a i • b' i



def SmithExists : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (y : M →ₗ[R] M),
    Nonempty (SmithData y (Module.finrank R M))

end Formalism.A
end
end

namespace Formalism.A

open Module

theorem nonempty_smith_normal_form {R M : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (y : M →ₗ[R] M) :
    Nonempty (SmithData y (Module.finrank R M)) := by
  classical

  let b0 : Module.Basis (Fin (Module.finrank R M)) R M := Module.finBasis R M
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm b0 (LinearMap.range y)
  obtain ⟨k, bK⟩ := Submodule.basisOfPid b0 (LinearMap.ker y)

  have hx : ∀ i, ∃ x : M, y x = (snf.bN i : M) := fun i => LinearMap.mem_range.mp (snf.bN i).2
  choose x hx using hx
  let s : LinearMap.range y →ₗ[R] M := snf.bN.constr R x
  have hys : y ∘ₗ s = (LinearMap.range y).subtype := by
    refine snf.bN.ext fun i => ?_
    simp [s, hx]
  have hyS : ∀ z : LinearMap.range y, y (s z) = z := fun z => by
    simpa using LinearMap.congr_fun hys z
  have hrr : ∀ m : M, (y.rangeRestrict m : M) = y m := fun m => rfl
  let pK : M →ₗ[R] M := LinearMap.id - s ∘ₗ y.rangeRestrict
  have hpK : ∀ m : M, pK m = m - s (y.rangeRestrict m) := fun m => rfl
  have hker : ∀ m : M, pK m ∈ LinearMap.ker y := by
    intro m
    rw [LinearMap.mem_ker, hpK, map_sub, hyS, hrr, sub_self]
  have hrz : ∀ (c : LinearMap.ker y) (z : LinearMap.range y),
      y.rangeRestrict ((c : M) + s z) = z := by
    intro c z
    apply Subtype.ext
    rw [hrr, map_add (f := _), LinearMap.mem_ker.mp c.2, zero_add, hyS]

  let fwd : (LinearMap.ker y × LinearMap.range y) →ₗ[R] M := (LinearMap.ker y).subtype.coprod s
  let bwd : M →ₗ[R] (LinearMap.ker y × LinearMap.range y) :=
    LinearMap.prod (LinearMap.codRestrict (LinearMap.ker y) pK hker)
      y.rangeRestrict
  have hf : ∀ (c : LinearMap.ker y) (z : LinearMap.range y), fwd (c, z) = (c : M) + s z := by
    intro c z
    simp [fwd]
  have h1 : fwd ∘ₗ bwd = LinearMap.id := by
    refine LinearMap.ext fun m => ?_
    show fwd (bwd m) = m
    have hb : bwd m = (⟨m - s (y.rangeRestrict m), hker m⟩, y.rangeRestrict m) := rfl
    rw [hb, hf]
    exact sub_add_cancel m _
  have h2 : bwd ∘ₗ fwd = LinearMap.id := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨c, z⟩ := p
    show bwd (fwd (c, z)) = (c, z)
    rw [hf]
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show (c : M) + s z - s (y.rangeRestrict ((c : M) + s z)) = c
      rw [hrz]
      exact add_sub_cancel_right _ _
    · exact hrz c z
  let e : (LinearMap.ker y × LinearMap.range y) ≃ₗ[R] M := LinearEquiv.ofLinear fwd bwd h1 h2

  let B : Module.Basis (Fin k ⊕ Fin n) R M := (bK.prod snf.bN).map e
  have hB1 : ∀ l, y (B (Sum.inl l)) = 0 := by
    intro l
    have : B (Sum.inl l) = bK l := by
      simp [B, e, hf]
    rw [this]
    exact LinearMap.mem_ker.mp (bK l).2
  have hB2 : ∀ i, y (B (Sum.inr i)) = snf.a i • snf.bM (snf.f i) := by
    intro i
    have : B (Sum.inr i) = s (snf.bN i) := by
      simp [B, e, hf]
    rw [this, hyS, snf.snf i]

  have hcard : k + n = Module.finrank R M := by
    simpa using (Module.finrank_eq_card_basis B).symm
  have hcompl : Fintype.card (Fin k) = Fintype.card ↥(Set.range snf.f)ᶜ := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective snf.f.injective, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin]
    omega
  let τ : Fin k ≃ ↥(Set.range snf.f)ᶜ := Fintype.equivOfCardEq hcompl
  let σ : Fin k ⊕ Fin n ≃ Fin (Module.finrank R M) :=
    (Equiv.sumComm _ _).trans ((Equiv.sumCongr (Equiv.ofInjective snf.f snf.f.injective) τ).trans
      (Equiv.Set.sumCompl (Set.range snf.f)))
  have hσ : ∀ i, σ (Sum.inr i) = snf.f i := by
    intro i
    simp [σ]
  refine ⟨SmithData.mk (B.reindex σ) snf.bM (fun j => Sum.elim (fun _ => 0) snf.a (σ.symm j)) ?_⟩
  intro j
  obtain ⟨z, rfl⟩ := σ.surjective j
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  rcases z with l | i
  · rw [hB1 l, Sum.elim_inl, zero_smul]
  · rw [hB2 i, hσ i, Sum.elim_inr]

theorem smith_form_exists : SmithExists := by
  unfold SmithExists
  intro R M _ _ _ _ _ _ _ y
  exact nonempty_smith_normal_form y

end Formalism.A
end

namespace Formalism.A

theorem smithExists : SmithExists := smith_form_exists

end Formalism.A
end

namespace Formalism.GM

open Matrix

theorem smith_form_p_adic_integers : SmithZp := by
  intro p _ n M
  classical
  let y : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ℤ_[p]) := Matrix.toLin' M
  obtain ⟨S⟩ := Formalism.A.smithExists ℤ_[p] (Fin n → ℤ_[p]) y
  have hfr : Module.finrank ℤ_[p] (Fin n → ℤ_[p]) = n := Module.finrank_fin_fun ℤ_[p]
  let e : Fin (Module.finrank ℤ_[p] (Fin n → ℤ_[p])) ≃ Fin n := finCongr hfr
  let b := S.b.reindex e
  let b' := S.b'.reindex e
  let a : Fin n → ℤ_[p] := S.a ∘ e.symm
  have hy : ∀ j, M.mulVec (b j) = a j • b' j := by
    intro j
    have := S.hy (e.symm j)
    simpa [b, b', a, y, Matrix.toLin'_apply] using this
  let std := Pi.basisFun ℤ_[p] (Fin n)
  let Q := std.toMatrix b
  let P := std.toMatrix b'
  let V := b.toMatrix std
  have hQV : Q * V = 1 := Module.Basis.toMatrix_mul_toMatrix_flip std b
  have hPW : P * (b'.toMatrix std) = 1 := Module.Basis.toMatrix_mul_toMatrix_flip std b'
  have hMQ : M * Q = P * Matrix.diagonal a := by
    ext i j
    have h1 := congrFun (hy j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Q, P, std, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h1]; ring
  refine ⟨P, V, a, Matrix.isUnit_det_of_right_inverse hPW, Matrix.isUnit_det_of_left_inverse hQV, ?_⟩
  calc M = M * (Q * V) := by rw [hQV, Matrix.mul_one]
    _ = (M * Q) * V := by rw [Matrix.mul_assoc]
    _ = P * Matrix.diagonal a * V := by rw [hMQ]

end Formalism.GM
end

section -- merged from Formalism.MahlerMeasure.MahlerMeasureProofs.LevelDecomp
namespace Formalism.GM

open MvPolynomial Finset

section
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}

theorem ld_biHom_of_euler [CharZero k] {a b : ℕ} {g : MvPolynomial σ k}
    (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g)
    (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) : BiHom w e a b g := by
  classical
  unfold BiHom
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  have hterm : ∀ i : σ, AddMonoidAlgebra.coeff (X i * pderiv i g) m = (m i : k) * AddMonoidAlgebra.coeff g m := by
    intro i
    rw [MvPolynomial.coeff_X_mul']
    split_ifs with hs
    · have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)
      have e1 : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hmi)
      have e2 : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : k) + 1 = (m i : k) := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same, ← Nat.cast_add_one, Nat.sub_add_cancel hmi]
      rw [MvPolynomial.coeff_pderiv, e1, e2, mul_comm]
    · simp at hs
      simp [hs]
  have key : ∀ (v : Fin r → σ) (n : ℕ), ∑ c, X (v c) * pderiv (v c) g = (n : k) • g → ∑ c, m (v c) = n := by
    intro v n hv
    have hcoef := congrArg (AddMonoidAlgebra.coeff · m) hv
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at hcoef
    simp only [hterm] at hcoef
    rw [← Finset.sum_mul] at hcoef
    have hc := mul_right_cancel₀ hm hcoef
    exact_mod_cast hc
  exact ⟨key w a hW, key e b hE⟩

end

section fockSec
open Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {σ : Type}

end fockSec

section
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}

end

section fockSec
open Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ} {w e : Fin r → σ}

end fockSec

end Formalism.GM
end
