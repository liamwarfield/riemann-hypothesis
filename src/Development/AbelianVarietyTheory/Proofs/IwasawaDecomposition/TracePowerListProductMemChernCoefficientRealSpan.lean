module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreDescriptionLevelMoveMarkingComp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieTensorProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieTensorProduct
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PolyRep

theorem lie_tensor {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R]
    (A : Mat m R) :
    (ρ.tensor σ).lie A = kron (ρ.lie A) 1 + kron 1 (σ.lie A) := by
  ext i j
  obtain ⟨⟨a, c⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨b, d⟩, rfl⟩ := finProdFinEquiv.surjective j
  set X : Mat m (DualNumber R) := fun τ => Matrix.of fun a b =>
    TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b) with hX
  have h := ev_dual_model (ρ.tensor σ) A (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d))
  have hk : (ρ.tensor σ).ev X = kron (ρ.ev X) (σ.ev X) := evEnt_kron ρ.ent σ.ent X
  rw [hk] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h2
  have hr : (kron (ρ.lie A) (1 : Matrix (Fin σ.M) (Fin σ.M) R) + kron (1 : Matrix (Fin ρ.M) (Fin ρ.M) R) (σ.lie A))
      (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d))
      = ρ.lie A a b * (1 : Matrix (Fin σ.M) (Fin σ.M) R) c d + (1 : Matrix (Fin ρ.M) (Fin ρ.M) R) a b * σ.lie A c d := by
    simp [kron]
  have hl : kron (ρ.ev X) (σ.ev X) (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d)) = ρ.ev X a b * σ.ev X c d := by
    simp [kron]
  rw [hl, ev_dual_model ρ A a b, ev_dual_model σ A c d] at h2
  rw [← h2]
  refine Eq.trans ?_ hr.symm
  simp [TrivSqZeroExt.snd_mul]
  ring

end GlobalTheory.GoodMetric.PolyRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieTensorProductStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_tensorProduct : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), (ρ.tensor σ).lie A = kron (ρ.lie A) 1 + kron 1 (σ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_tensor | exact GlobalTheory.GoodMetric.PolyRep.lie_tensor | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepCombinationPurePowerTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulTraceExteriorSquareDerivationPow
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulTraceExteriorSquareDerivationPow
set_option autoImplicit false

noncomputable section

open scoped Matrix
open Finset

namespace GlobalTheory.GoodMetric.ChernSpan.TraceWedgeSq

variable {R : Type} [CommRing R] {M : ℕ}

theorem trace_reindex_self {m n : Type} [Fintype m] [Fintype n] (e : m ≃ n) (A : Matrix m m R) :
    (Matrix.reindex e e A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diag]
  exact e.symm.sum_comp (fun x => A x x)

theorem reindex_pow_self {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m R) (k : ℕ) :
    (Matrix.reindex e e A) ^ k = Matrix.reindex e e (A ^ k) := by
  induction k with
  | zero => simp [Matrix.submatrix_one_equiv]
  | succ k ih =>
    rw [pow_succ, pow_succ, ih]
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

def embF (x : Fin M × Fin M) (a b : Fin M) : R :=
  (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 b -
    (1 : Matrix (Fin M) (Fin M) R) x.1 b * (1 : Matrix (Fin M) (Fin M) R) x.2 a

def emb (R : Type) [CommRing R] (M : ℕ) : Matrix (Fin M × Fin M) (Pair M) R :=
  Matrix.of fun x r => embF x r.1.1 r.1.2

theorem sum_mul_embF (A : Fin M × Fin M → R) (a b : Fin M) :
    ∑ y, A y * embF y a b = A (a, b) - A (b, a) := by
  simp [embF, Fintype.sum_prod_type, Matrix.one_apply, mul_sub, Finset.sum_sub_distrib, mul_ite]

theorem sum_emb_mul (x : Fin M × Fin M) (G : Fin M → Fin M → R) (hG : ∀ a b, G b a = - G a b)
    (hG0 : ∀ a, G a a = 0) :
    ∑ q : Pair M, emb R M x q * G q.1.1 q.1.2 = G x.1 x.2 := by
  have h := sum_sum_eq_sum_pair (fun a b =>
    (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 b * G a b)
  have hl : ∑ a, ∑ b, (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 b * G a b
      = G x.1 x.2 := by
    simp [Matrix.one_apply]
  have hd : ∑ a, (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 a * G a a = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hG0, mul_zero]
  rw [hl, hd, add_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [emb, embF, Matrix.of_apply, hG q.1.1 q.1.2]
  ring

theorem mul_emb_apply {n : Type} (A : Matrix n (Fin M × Fin M) R) (x : n) (r : Pair M) :
    (A * emb R M) x r = A x (r.1.1, r.1.2) - A x (r.1.2, r.1.1) := by
  rw [Matrix.mul_apply]
  exact sum_mul_embF (fun y => A x y) r.1.1 r.1.2

def wedgeLieExt (L : Matrix (Fin M) (Fin M) R) (a b : Fin M) (r : Pair M) : R :=
  L a r.1.1 * (1 : Matrix (Fin M) (Fin M) R) b r.1.2 + (1 : Matrix (Fin M) (Fin M) R) a r.1.1 * L b r.1.2 -
    L b r.1.1 * (1 : Matrix (Fin M) (Fin M) R) a r.1.2 - (1 : Matrix (Fin M) (Fin M) R) b r.1.1 * L a r.1.2

def tensorLie (L : Matrix (Fin M) (Fin M) R) : Matrix (Fin M × Fin M) (Fin M × Fin M) R :=
  Matrix.kroneckerMap (· * ·) L 1 + Matrix.kroneckerMap (· * ·) 1 L

theorem tensorLie_mul_emb (L : Matrix (Fin M) (Fin M) R) :
    tensorLie L * emb R M = emb R M * wedgeLieRaw L := by
  ext x r
  rw [mul_emb_apply, Matrix.mul_apply]
  have h := sum_emb_mul x (fun a b => wedgeLieExt L a b r)
    (fun a b => by simp only [wedgeLieExt]; ring) (fun a => by simp only [wedgeLieExt]; ring)
  rw [show (∑ q : Pair M, emb R M x q * wedgeLieRaw L q r) =
      ∑ q : Pair M, emb R M x q * wedgeLieExt L q.1.1 q.1.2 r from rfl, h]
  simp only [tensorLie, wedgeLieExt, Matrix.add_apply, Matrix.kroneckerMap_apply]
  ring

theorem tensorLie_pow_mul_emb (L : Matrix (Fin M) (Fin M) R) (n : ℕ) :
    tensorLie L ^ n * emb R M = emb R M * wedgeLieRaw L ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, tensorLie_mul_emb, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem emb_transpose_mul_emb :
    (emb R M)ᵀ * emb R M = (2 : R) • (1 : Matrix (Pair M) (Pair M) R) := by
  ext ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩
  rw [mul_emb_apply]
  simp only [Matrix.transpose_apply, emb, embF, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
    Subtype.mk.injEq, Prod.mk.injEq, smul_eq_mul]
  simp only at hij hkl
  have h0 : ¬ (k = j ∧ l = i) := fun h => by
    rcases h with ⟨rfl, rfl⟩; exact absurd (hij.trans hkl) (lt_irrefl _)
  by_cases h1 : k = i <;> by_cases h2 : l = j
  · subst h1; subst h2; simp [hkl.ne, hkl.ne']; ring
  · have : ¬ (i = k ∧ j = l) := fun h => h2 h.2.symm
    by_cases h3 : k = j <;> by_cases h4 : l = i <;> simp_all
  · have : ¬ (i = k ∧ j = l) := fun h => h1 h.1.symm
    by_cases h3 : k = j <;> by_cases h4 : l = i <;> simp_all
  · have : ¬ (i = k ∧ j = l) := fun h => h1 h.1.symm
    by_cases h3 : k = j <;> by_cases h4 : l = i <;> simp_all

theorem emb_mul_transpose_apply (x y : Fin M × Fin M) :
    (emb R M * (emb R M)ᵀ) x y = embF x y.1 y.2 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  simp only [mul_comm (emb R M x _)]
  exact sum_emb_mul y (fun a b => embF x a b) (fun a b => by simp only [embF]; ring)
    (fun a => by simp only [embF]; ring)

theorem trace_mul_emb_mul_transpose (A : Matrix (Fin M × Fin M) (Fin M × Fin M) R) :
    (A * (emb R M * (emb R M)ᵀ)).trace = A.trace - ∑ x : Fin M × Fin M, A x (x.2, x.1) := by
  simp only [Matrix.trace, Matrix.diag]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_apply]
  simp only [emb_mul_transpose_apply]
  exact sum_mul_embF (fun y => A x y) x.1 x.2

theorem sum_kron_swap (P Q : Matrix (Fin M) (Fin M) R) :
    ∑ x : Fin M × Fin M, Matrix.kroneckerMap (· * ·) P Q x (x.2, x.1) = (P * Q).trace := by
  simp [Fintype.sum_prod_type, Matrix.trace, Matrix.mul_apply]

theorem kron_left_pow (L : Matrix (Fin M) (Fin M) R) (m : ℕ) :
    (Matrix.kroneckerMap (· * ·) L (1 : Matrix (Fin M) (Fin M) R)) ^ m =
      Matrix.kroneckerMap (· * ·) (L ^ m) (1 : Matrix (Fin M) (Fin M) R) := by
  induction m with
  | zero => simp [Matrix.one_kronecker_one]
  | succ m ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, Matrix.mul_one, pow_succ]

theorem kron_right_pow (L : Matrix (Fin M) (Fin M) R) (m : ℕ) :
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) L) ^ m =
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) (L ^ m) := by
  induction m with
  | zero => simp [Matrix.one_kronecker_one]
  | succ m ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, Matrix.mul_one, pow_succ]

theorem sum_tensorLie_pow_swap (L : Matrix (Fin M) (Fin M) R) (n : ℕ) :
    ∑ x : Fin M × Fin M, (tensorLie L ^ n) x (x.2, x.1) = 2 ^ n * (L ^ n).trace := by
  have hc : Commute (Matrix.kroneckerMap (· * ·) L (1 : Matrix (Fin M) (Fin M) R))
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) L) := by
    show _ * _ = _ * _
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hterm : ∀ m ∈ Finset.range (n + 1), ∀ x : Fin M × Fin M,
      (Matrix.kroneckerMap (· * ·) L (1 : Matrix (Fin M) (Fin M) R) ^ m *
        Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) L ^ (n - m) *
        ((n.choose m : ℕ) : Matrix (Fin M × Fin M) (Fin M × Fin M) R)) x (x.2, x.1) =
      (n.choose m : R) * Matrix.kroneckerMap (· * ·) (L ^ m) (L ^ (n - m)) x (x.2, x.1) := by
    intro m _ x
    rw [kron_left_pow, kron_right_pow, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul]
  have htr : ∀ m ∈ Finset.range (n + 1), (L ^ m * L ^ (n - m)).trace = (L ^ n).trace := by
    intro m hm
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
  rw [tensorLie, hc.add_pow]
  simp only [Matrix.sum_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun m hm => (Finset.sum_congr rfl fun x _ => hterm m hm x)]
  simp only [← Finset.mul_sum, sum_kron_swap]
  rw [Finset.sum_congr rfl fun m hm => by rw [htr m hm], ← Finset.sum_mul]
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

end GlobalTheory.GoodMetric.ChernSpan.TraceWedgeSq

namespace GlobalTheory.GoodMetric.ChernSpan

open TraceWedgeSq

theorem two_mul_trace_wedge2Lie_pow {R : Type} [CommRing R] {M : ℕ} (L : Matrix (Fin M) (Fin M) R) (i : ℕ) :
    2 * ((wedge2Lie L) ^ i).trace = ((kron L 1 + kron 1 L) ^ i).trace - 2 ^ i * (L ^ i).trace := by
  have hW : ((wedge2Lie L) ^ i).trace = ((wedgeLieRaw L) ^ i).trace := by
    rw [wedge2Lie, reindex_pow_self, trace_reindex_self]
  have hK : kron L 1 + kron 1 L = Matrix.reindex finProdFinEquiv finProdFinEquiv (tensorLie L) := by
    ext a b
    simp [kron, tensorLie]
  rw [hW, hK, reindex_pow_self, trace_reindex_self]
  have key : (2 : R) • (wedgeLieRaw L ^ i) = (emb R M)ᵀ * (tensorLie L ^ i * emb R M) := by
    rw [tensorLie_pow_mul_emb, ← Matrix.mul_assoc, emb_transpose_mul_emb, Matrix.smul_mul, Matrix.one_mul]
  calc 2 * (wedgeLieRaw L ^ i).trace = ((2 : R) • (wedgeLieRaw L ^ i)).trace := by
        rw [Matrix.trace_smul, smul_eq_mul]
    _ = (tensorLie L ^ i * emb R M * (emb R M)ᵀ).trace := by rw [key, Matrix.trace_mul_comm]
    _ = _ := by rw [Matrix.mul_assoc, trace_mul_emb_mul_transpose, sum_tensorLie_pow_swap]

end GlobalTheory.GoodMetric.ChernSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulTraceExteriorSquareDerivationPowStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_trace_exteriorSquareDerivation_pow : ∀ {R : Type} [CommRing R] {M : ℕ} (L : Matrix (Fin M) (Fin M) R) (i : ℕ), 2 * ((wedge2Lie L) ^ i).trace = ((kron L 1 + kron 1 L) ^ i).trace - 2 ^ i * (L ^ i).trace := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow | exact GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow | (intros; apply GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieExteriorSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieExteriorSquare
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.PolyRep

theorem snd_wedge2_dual {M : ℕ} {R : Type} [CommRing R] (L : Matrix (Fin M) (Fin M) R) (p q : Fin (pairCard M)) :
    TrivSqZeroExt.snd (ChernSpan.wedge2 (Matrix.of fun a b =>
        (TrivSqZeroExt.inl ((1 : Matrix (Fin M) (Fin M) R) a b) + TrivSqZeroExt.inr (L a b) : DualNumber R)) p q)
      = wedge2Lie L p q := by
  simp only [ChernSpan.wedge2, wedge2Lie, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    wedgeRaw, wedgeLieRaw, Matrix.of_apply]
  simp only [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
    smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add]
  ring

theorem lie_wedge2 {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) :
    ρ.wedge2.lie A = wedge2Lie (ρ.lie A) := by
  ext p q
  have h := ev_dual_model ρ.wedge2 A p q
  have e : ∀ D : Mat m (DualNumber R), ρ.wedge2.ev D = ChernSpan.wedge2 (ρ.ev D) :=
    fun D => evEnt_wedge2 ρ.ent D
  have e2 : ρ.ev (R := DualNumber R) (fun τ => Matrix.of fun a b =>
        TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b))
      = Matrix.of fun a b => (TrivSqZeroExt.inl ((1 : Matrix (Fin ρ.M) (Fin ρ.M) R) a b)
        + TrivSqZeroExt.inr (ρ.lie A a b) : DualNumber R) := by
    ext a b : 1
    exact ev_dual_model ρ A a b
  rw [e, e2] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h2
  exact h2.symm.trans (snd_wedge2_dual (ρ.lie A) p q)

end GlobalTheory.GoodMetric.PolyRep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieExteriorSquareStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_exteriorSquare : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), ρ.wedge2.lie A = wedge2Lie (ρ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_wedge2 | exact GlobalTheory.GoodMetric.PolyRep.lie_wedge2 | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_wedge2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepCombinationPurePowerTrace
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.PureVirt

variable {ι : Type} [Fintype ι] {m : ι → ℕ} {S : Type} [CommRing S] [Algebra ℝ S]

def Virt (m : ι → ℕ) (g : ℕ → Mat m S → S) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ),
    ∀ (A : Mat m S) (b : ℕ), ∑ j, c j • (ρ j).ptr b A = g b A

theorem virt_smul (r : ℝ) {g : ℕ → Mat m S → S} (hg : Virt m g) : Virt m (fun b A => r • g b A) := by
  obtain ⟨J, _, ρ, c, hc⟩ := hg
  refine ⟨J, inferInstance, ρ, fun j => r * c j, fun A b => ?_⟩
  simp only [← hc, Finset.smul_sum, smul_smul]

theorem virt_fsum {α : Type} [Fintype α] (g : α → ℕ → Mat m S → S) (hg : ∀ a, Virt m (g a)) :
    Virt m (fun b A => ∑ a, g a b A) := by
  choose J hJ ρ c hc using hg
  refine ⟨Σ a, J a, inferInstance, fun x => ρ x.1 x.2, fun x => c x.1 x.2, fun A b => ?_⟩
  rw [Fintype.sum_sigma]
  simp only [hc]

theorem ptr_tensor_sub_wedge2 (ρ : PolyRep m) (A : Mat m S) (b : ℕ) :
    (ρ.tensor ρ).ptr b A - 2 * ρ.wedge2.ptr b A = 2 ^ b * ρ.ptr b A := by
  have h := GlobalTheory.T.two_mul_trace_exteriorSquareDerivation_pow (ρ.lie A) b
  have e1 : (ρ.tensor ρ).ptr b A = ((kron (ρ.lie A) 1 + kron 1 (ρ.lie A)) ^ b).trace :=
    congrArg (fun L => (L ^ b).trace) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_tensorProduct ρ ρ A)
  have e2 : ρ.wedge2.ptr b A = ((wedge2Lie (ρ.lie A)) ^ b).trace :=
    congrArg (fun L => (L ^ b).trace) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_exteriorSquare ρ A)
  have e3 : ρ.ptr b A = ((ρ.lie A) ^ b).trace := rfl
  linear_combination e1 - 2 * e2 - h - 2 ^ b * e3

theorem virt_double {g : ℕ → Mat m S → S} (hg : Virt m g) :
    Virt m (fun b A => (2 : ℝ) ^ b • g b A) := by
  obtain ⟨J, _, ρ, c, hc⟩ := hg
  refine ⟨J ⊕ J, inferInstance, Sum.elim (fun j => (ρ j).tensor (ρ j)) (fun j => (ρ j).wedge2),
    Sum.elim c (fun j => -2 * c j), fun A b => ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := ptr_tensor_sub_wedge2 (ρ j) A b
  simp only [Algebra.smul_def, map_mul, map_neg, map_pow, map_ofNat]
  linear_combination (algebraMap ℝ S (c j)) * h

theorem virt_proj (τ : ι) : Virt m (fun b (A : Mat m S) => ((A τ) ^ b).trace) := by
  refine ⟨Unit, inferInstance, fun _ => proj m τ, fun _ => 1, fun A b => ?_⟩
  simp only [PolyRep.ptr, lie_proj_model, one_smul, Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem virt_pow (τ : ι) (a : ℕ) :
    Virt m (fun b (A : Mat m S) => ((2 : ℝ) ^ a) ^ b • ((A τ) ^ b).trace) := by
  induction a with
  | zero => simpa using virt_proj (m := m) (S := S) τ
  | succ a ih =>
    have e : (fun b (A : Mat m S) => ((2 : ℝ) ^ (a + 1)) ^ b • ((A τ) ^ b).trace)
        = fun b A => (2 : ℝ) ^ b • (((2 : ℝ) ^ a) ^ b • ((A τ) ^ b).trace) := by
      funext b A
      rw [smul_smul, pow_succ, mul_pow, mul_comm]
    rw [e]
    exact virt_double ih

theorem exists_vandermonde_solution (n i : ℕ) : ∃ x : Fin (n + 1) → ℝ, ∀ b : Fin (n + 1),
    ∑ a, x a * ((2 : ℝ) ^ (a : ℕ)) ^ (b : ℕ) = if (b : ℕ) = i then 1 else 0 := by
  set V := Matrix.vandermonde (fun a : Fin (n + 1) => (2 : ℝ) ^ (a : ℕ)) with hV
  have hinj : Function.Injective (fun a : Fin (n + 1) => (2 : ℝ) ^ (a : ℕ)) := by
    intro a a' h
    exact Fin.ext ((pow_right_strictMono₀ one_lt_two).injective h)
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  set δ : Fin (n + 1) → ℝ := fun b => if (b : ℕ) = i then 1 else 0 with hδ
  refine ⟨δ ᵥ* V⁻¹, fun b => ?_⟩
  have h : (δ ᵥ* V⁻¹) ᵥ* V = δ := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  exact congrFun h b

theorem exists_pure_power_trace {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S]
    [Algebra ℝ S] (τ : ι) (i : ℕ) (_hi : 1 ≤ i) :
    ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ), ∀ (A : Mat m S) (b : ℕ), b ≤ n →
      ∑ j, c j • (ρ j).ptr b A = if b = i then ((A τ) ^ i).trace else 0 := by
  obtain ⟨x, hx⟩ := exists_vandermonde_solution n i
  obtain ⟨J, hJ, ρ, c, hc⟩ := virt_fsum (m := m) (S := S)
    (fun a : Fin (n + 1) => fun b A => x a • (((2 : ℝ) ^ (a : ℕ)) ^ b • ((A τ) ^ b).trace))
    (fun a => virt_smul (x a) (virt_pow τ a))
  refine ⟨J, hJ, ρ, c, fun A b hb => ?_⟩
  rw [hc]
  have h := hx ⟨b, Nat.lt_succ_of_le hb⟩
  simp only [smul_smul, ← Finset.sum_smul] at h ⊢
  rw [h]
  split_ifs with hbi
  · subst hbi; exact one_smul ℝ _
  · exact zero_smul ℝ _

end GlobalTheory.GoodMetric.PureVirt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepCombinationPurePowerTraceStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polyRep_combination_pure_power_trace : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι) (i : ℕ), 1 ≤ i → ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ), ∀ (A : Mat m S) (b : ℕ), b ≤ n → ∑ j, c j • (ρ j).ptr b A = if b = i then ((A τ) ^ i).trace else 0 := by
  first | exact @GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace | exact GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace | (intros; apply GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowFinProdKroneckerAddBinomial
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowFinProdKroneckerAddBinomial
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.ChernSpan

theorem kron_pow' {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) (n : ℕ) : kron a b ^ n = kron (a ^ n) (b ^ n) := by
  induction n with
  | zero => simp [kron_one]
  | succ n ih => rw [pow_succ, ih, ← kron_mul, pow_succ, pow_succ]

theorem trace_kron' {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (kron a b).trace = a.trace * b.trace := by
  rw [kron, ← Matrix.trace_kronecker]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finProdFinEquiv.symm fun x => Matrix.kroneckerMap (· * ·) a b x x

theorem trace_pow_kron_add {R : Type} [CommRing R] {M N : ℕ} (L : Matrix (Fin M) (Fin M) R)
    (L' : Matrix (Fin N) (Fin N) R) (i : ℕ) :
    ((kron L 1 + kron 1 L') ^ i).trace =
      ∑ a ∈ Finset.range (i + 1), (i.choose a : R) * (L ^ a).trace * (L' ^ (i - a)).trace := by
  have hc : Commute (kron L (1 : Matrix (Fin N) (Fin N) R)) (kron (1 : Matrix (Fin M) (Fin M) R) L') := by
    unfold Commute SemiconjBy
    rw [← kron_mul, ← kron_mul, mul_one, one_mul, mul_one, one_mul]
  rw [hc.add_pow, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [kron_pow', kron_pow', one_pow, one_pow, ← kron_mul, mul_one, one_mul, ← Nat.cast_comm,
    ← nsmul_eq_mul, Matrix.trace_smul, nsmul_eq_mul, trace_kron', mul_assoc]

end GlobalTheory.GoodMetric.ChernSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowFinProdKroneckerAddBinomialStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pow_finProdKronecker_add_binomial : ∀ {R : Type} [CommRing R] {M N : ℕ} (L : Matrix (Fin M) (Fin M) R) (L' : Matrix (Fin N) (Fin N) R) (i : ℕ), ((kron L 1 + kron 1 L') ^ i).trace = ∑ a ∈ Finset.range (i + 1), (i.choose a : R) * (L ^ a).trace * (L' ^ (i - a)).trace := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trace_pow_kron_add | exact GlobalTheory.GoodMetric.ChernSpan.trace_pow_kron_add | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trace_pow_kron_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevNegFinSumBlockDiagonalMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevNegFinSumBlockDiagonalMatrix
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem det_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (blockSum a b).det = a.det * b.det := by
  rw [blockSum, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem neg_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : -(blockSum a b) = blockSum (-a) (-b) := by
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.neg_apply]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;> simp

theorem one_sub_smul_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) :
    (1 - (Polynomial.X : Polynomial R) • (blockSum a b).map Polynomial.C) =
      blockSum (1 - (Polynomial.X : Polynomial R) • a.map Polynomial.C)
        (1 - (Polynomial.X : Polynomial R) • b.map Polynomial.C) := by
  rw [blockSum_map]
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply]
  rw [show (1 : Matrix (Fin (M + N)) (Fin (M + N)) (Polynomial R)) i j =
      (1 : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) (Polynomial R)) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) by
    simp [Matrix.one_apply]]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;>
    simp [Matrix.one_apply]

theorem charpolyRev_neg_blockSum : ∀ {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R), Matrix.charpolyRev (-(blockSum a b)) = Matrix.charpolyRev (-a) * Matrix.charpolyRev (-b) := by
  intro R _ M N a b
  rw [neg_blockSum, Matrix.charpolyRev, Matrix.charpolyRev, Matrix.charpolyRev, one_sub_smul_blockSum, det_blockSum]

end GlobalTheory.GoodMetric.ChernSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevNegFinSumBlockDiagonalMatrixStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpolyRev_neg_finSumBlockDiagonalMatrix : ∀ {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R), Matrix.charpolyRev (-(blockSum a b)) = Matrix.charpolyRev (-a) * Matrix.charpolyRev (-b) := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum | exact GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum | (intros; apply GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieDirectSum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieDirectSum
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PolyRep

theorem lie_sum {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R]
    (A : Mat m R) :
    (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  ext i j
  simp only [lie, Matrix.of_apply]
  change Fin (ρ.M + σ.M) at i j
  change ∑ v : EntIx m, aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2)
      (pderiv v (blockSum ρ.ent σ.ent i j)) * A v.1 v.2.1 v.2.2 = _
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rcases x with x | x <;> rcases y with y | y <;> simp [lie, sum, blockSum]

end GlobalTheory.GoodMetric.PolyRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieDirectSumStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_directSum : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_sum | exact GlobalTheory.GoodMetric.PolyRep.lie_sum | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowEqSumSmulCoeffCharpolyRevPow
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowEqSumSmulCoeffCharpolyRevPow
set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory

namespace LogTrace

theorem coeff_sub_one_pow {S : Type} [CommRing S] [Algebra ℝ S] (f : S[X]) (s n : ℕ) (hs : s ≤ n) :
    ((f - 1) ^ s).coeff n =
      ∑ k ∈ Finset.range (n + 1), ((-1 : ℝ) ^ (s - k) * (s.choose k : ℝ)) • (f ^ k).coeff n := by
  rw [sub_eq_add_neg, add_pow, finsetSum_coeff]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : s + 1 ≤ n + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [show f ^ k * (-1) ^ (s - k) * ((s.choose k : ℕ) : S[X]) =
        C ((-1 : S) ^ (s - k) * (s.choose k : S)) * f ^ k by simp [map_mul, map_pow, map_neg]; ring]
    rw [coeff_C_mul, Algebra.smul_def]
    simp
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem coeff_zero_charpolyRev {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) :
    M.charpolyRev.coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

def newtonPoly {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (m : ℕ) : R[X] :=
  ∑ i ∈ Finset.range (m + 1), C (-(M ^ (i + 1)).trace) * X ^ i

theorem coeff_newtonPoly {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (m k : ℕ)
    (hk : k ≤ m) : (newtonPoly M m).coeff k = -(M ^ (k + 1)).trace := by
  simp only [newtonPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_of_le hk]

theorem X_pow_dvd_derivative_sub {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (m : ℕ) :
    (X : R[X]) ^ (m + 1) ∣ derivative M.charpolyRev - newtonPoly M m * M.charpolyRev := by
  rw [X_pow_dvd_iff]
  intro d hd
  have hN := GlobalTheory.natCast_mul_coeff_charpolyRev M (d + 1)
  rw [coeff_sub, coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [coeff_newtonPoly M m k (by simp only [Finset.mem_range] at hk; omega)])]
  simp only [Nat.add_sub_cancel, neg_mul, Finset.sum_neg_distrib] at hN ⊢
  push_cast at hN
  linear_combination hN

def logTrunc {S : Type} [CommRing S] [Algebra ℝ S] (m : ℕ) (f : S[X]) : S[X] :=
  ∑ s ∈ Finset.range (m + 1), C (algebraMap ℝ S ((-1) ^ s / ((s : ℝ) + 1))) * (f - 1) ^ (s + 1)

theorem mul_derivative_logTrunc {S : Type} [CommRing S] [Algebra ℝ S] (m : ℕ) (f : S[X]) :
    f * derivative (logTrunc m f) = derivative f * (1 - (-(f - 1)) ^ (m + 1)) := by
  have hs : ∀ s : ℕ, C (algebraMap ℝ S ((-1) ^ s / ((s : ℝ) + 1))) * C ((s : S) + 1) = (-1) ^ s := by
    intro s
    rw [← C_mul, show ((s : S) + 1) = algebraMap ℝ S ((s : ℝ) + 1) by simp, ← map_mul,
      div_mul_cancel₀ _ (by positivity)]
    simp
  have hD : derivative (logTrunc m f) = (∑ s ∈ Finset.range (m + 1), (-(f - 1)) ^ s) * derivative f := by
    simp only [logTrunc, derivative_sum, derivative_C_mul, derivative_pow_succ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [derivative_sub, derivative_one, sub_zero, neg_pow (f - 1) s]
    linear_combination ((f - 1) ^ s * derivative f) * hs s
  have hg := mul_neg_geom_sum (-(f - 1)) (m + 1)
  rw [hD]
  linear_combination (derivative f) * hg

theorem coeff_logTrunc_charpolyRev {S : Type} [CommRing S] [Algebra ℝ S] {N : ℕ}
    (L : Matrix (Fin N) (Fin N) S) (m : ℕ) :
    ((m : S) + 1) * (logTrunc m (Matrix.charpolyRev (-L))).coeff (m + 1) =
      (-1) ^ m * (L ^ (m + 1)).trace := by
  set f := Matrix.charpolyRev (-L) with hf
  have hX : (X : S[X]) ∣ f - 1 := by
    simp [X_dvd_iff, hf, coeff_zero_charpolyRev]
  have h1 := X_pow_dvd_derivative_sub (-L) m
  rw [← hf] at h1
  have h2 : (X : S[X]) ^ (m + 1) ∣ derivative f * (-(f - 1)) ^ (m + 1) :=
    Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (dvd_neg.2 hX) (m + 1)) _
  have h3 : (X : S[X]) ^ (m + 1) ∣ f * (derivative (logTrunc m f) - newtonPoly (-L) m) := by
    have e : f * (derivative (logTrunc m f) - newtonPoly (-L) m) =
        (derivative f - newtonPoly (-L) m * f) - derivative f * (-(f - 1)) ^ (m + 1) := by
      linear_combination mul_derivative_logTrunc m f
    rw [e]
    exact dvd_sub h1 h2
  have hcop : IsCoprime (X : S[X]) f := by
    obtain ⟨h, hh⟩ := hX
    exact ⟨-h, 1, by linear_combination hh⟩
  have h4 := (X_pow_dvd_iff.1 (hcop.pow_left.dvd_of_dvd_mul_left h3)) m (by omega)
  rw [coeff_sub, coeff_derivative, coeff_newtonPoly (-L) m m le_rfl] at h4
  have ht : ((-L) ^ (m + 1)).trace = -((-1) ^ m * (L ^ (m + 1)).trace) := by
    rw [show -L = (-1 : S) • L by simp, _root_.smul_pow, Matrix.trace_smul, smul_eq_mul, pow_succ]
    ring
  linear_combination h4 - ht

end LogTrace


open LogTrace in
theorem trace_pow_eq_sum_smul_coeff_charpolyRev_pow :
    ∀ n : ℕ, 1 ≤ n → ∃ c : ℕ → ℝ, ∀ (S : Type) [CommRing S] [Algebra ℝ S] (N : ℕ)
      (L : Matrix (Fin N) (Fin N) S),
      ∑ k ∈ Finset.range (n + 1), c k • ((Matrix.charpolyRev (-L)) ^ k).coeff n = (L ^ n).trace := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨fun k => ∑ s ∈ Finset.range (m + 1),
    ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) *
      ((-1 : ℝ) ^ (s + 1 - k) * ((s + 1).choose k : ℝ)), ?_⟩
  intro S _ _ N L
  have key := coeff_logTrunc_charpolyRev L m
  set f := Matrix.charpolyRev (-L)
  have hsq : ((-1 : S) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  calc ∑ k ∈ Finset.range (m + 1 + 1), (∑ s ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) *
          ((-1 : ℝ) ^ (s + 1 - k) * ((s + 1).choose k : ℝ))) • (f ^ k).coeff (m + 1)
      = ∑ s ∈ Finset.range (m + 1), ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) •
          ∑ k ∈ Finset.range (m + 1 + 1),
            ((-1 : ℝ) ^ (s + 1 - k) * ((s + 1).choose k : ℝ)) • (f ^ k).coeff (m + 1) := by
        simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
    _ = ∑ s ∈ Finset.range (m + 1), ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) •
          ((f - 1) ^ (s + 1)).coeff (m + 1) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [coeff_sub_one_pow f (s + 1) (m + 1) (by simp only [Finset.mem_range] at hs; omega)]
    _ = ((-1 : ℝ) ^ m * ((m : ℝ) + 1)) • (logTrunc m f).coeff (m + 1) := by
        simp only [logTrunc, finsetSum_coeff, coeff_C_mul, Finset.smul_sum, ← Algebra.smul_def,
          smul_smul]
    _ = (L ^ (m + 1)).trace := by
        rw [Algebra.smul_def]
        simp only [map_mul, map_pow, map_neg, map_one, map_add (f := _), map_natCast]
        linear_combination (-1 : S) ^ m * key + (L ^ (m + 1)).trace * hsq

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowEqSumSmulCoeffCharpolyRevPowStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_pow_eq_sum_smul_coeff_charpolyRev : ∀ n : ℕ, 1 ≤ n → ∃ c : ℕ → ℝ, ∀ (S : Type) [CommRing S] [Algebra ℝ S] (N : ℕ) (L : Matrix (Fin N) (Fin N) S), ∑ k ∈ Finset.range (n + 1), c k • ((Matrix.charpolyRev (-L)) ^ k).coeff n = (L ^ n).trace := by
  first | exact @GlobalTheory.trace_pow_eq_sum_smul_coeff_charpolyRev_pow | exact GlobalTheory.trace_pow_eq_sum_smul_coeff_charpolyRev_pow | (intros; apply GlobalTheory.trace_pow_eq_sum_smul_coeff_charpolyRev_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpan
set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

variable {ι : Type} [Fintype ι] {m : ι → ℕ}

theorem charpolyRev_neg_lie_nsum (ρ : PolyRep m) (k : ℕ) {S : Type} [CommRing S] (A : Mat m S) :
    Matrix.charpolyRev (-((ρ.nsum k).lie A)) = (Matrix.charpolyRev (-(ρ.lie A))) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, Matrix.charpolyRev]
    haveI : IsEmpty (Fin (ρ.nsum 0).M) := inferInstanceAs (IsEmpty (Fin 0))
    exact Matrix.det_isEmpty
  | succ k ih =>
    rw [pow_succ, ← ih, ← GlobalTheory.T.charpolyRev_neg_finSumBlockDiagonalMatrix]
    exact congrArg (fun L => Matrix.charpolyRev (-L)) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_directSum (ρ.nsum k) ρ A)

theorem chern_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (ρ : PolyRep m) :
    (fun A : Mat m S => (Matrix.charpolyRev (-(ρ.lie A))).coeff n) ∈ Reach m n S :=
  Submodule.subset_span ⟨ρ, rfl⟩

theorem ptr_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (ρ : PolyRep m) :
    (fun A : Mat m S => ρ.ptr n A) ∈ Reach m n S := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := (Reach m 0 S).smul_mem (ρ.M : ℝ) (chern_mem_reach 0 S ρ)
    convert h using 1
    funext A
    have h0 : (Matrix.charpolyRev (-(ρ.lie A))).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    simp [PolyRep.ptr, h0, Algebra.smul_def]
  · obtain ⟨c, hc⟩ := GlobalTheory.T.exists_trace_pow_eq_sum_smul_coeff_charpolyRev n hn
    have h := (Reach m n S).sum_mem (t := Finset.range (n + 1))
      (fun k _ => (Reach m n S).smul_mem (c k) (chern_mem_reach n S (ρ.nsum k)))
    convert h using 1
    funext A
    rw [Finset.sum_apply, PolyRep.ptr, ← hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, charpolyRev_neg_lie_nsum]

theorem ptr_tensor (ρ σ : PolyRep m) (N : ℕ) {S : Type} [CommRing S] (A : Mat m S) :
    (ρ.tensor σ).ptr N A =
      ∑ a ∈ Finset.range (N + 1), (N.choose a : S) * ρ.ptr a A * σ.ptr (N - a) A := by
  simp only [PolyRep.ptr]
  rw [← GlobalTheory.T.trace_pow_finProdKronecker_add_binomial]
  exact congrArg (fun L => (L ^ N).trace) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_tensorProduct ρ σ A)

theorem ptr_mul_trProd_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (l : List (ι × ℕ)) :
    (∀ x ∈ l, 1 ≤ x.2) → ∀ r : ℕ, r + (l.map Prod.snd).sum = n → ∀ ρ : PolyRep m,
      (fun A : Mat m S => ρ.ptr r A * trProd l A) ∈ Reach m n S := by
  induction l with
  | nil =>
    intro _ r hr ρ
    have hr' : r = n := by simpa using hr
    subst hr'
    simpa [trProd] using ptr_mem_reach r S ρ
  | cons x l ih =>
    obtain ⟨τ, i⟩ := x
    intro hl r hr ρ
    have hi : 1 ≤ i := hl (τ, i) (by simp)
    have hr' : (r + i) + (l.map Prod.snd).sum = n := by
      simp only [List.map_cons, List.sum_cons] at hr
      omega
    obtain ⟨J, _, σ, c, hσ⟩ := GlobalTheory.T.exists_polyRep_combination_pure_power_trace m n S τ i hi
    have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (r + i) hr'
    have h := (Reach m n S).smul_mem (((r + i).choose r : ℝ)⁻¹)
      ((Reach m n S).sum_mem (t := Finset.univ)
        (fun j _ => (Reach m n S).smul_mem (c j) (ih' (ρ.tensor (σ j)))))
    convert h using 1
    funext A
    have hne : (((r + i).choose r : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right r i)).ne'
    have key : ∑ j, c j • (ρ.tensor (σ j)).ptr (r + i) A =
        (((r + i).choose r : ℕ) : ℝ) • (ρ.ptr r A * ((A τ) ^ i).trace) := by
      simp only [ptr_tensor, Finset.smul_sum]
      rw [Finset.sum_comm]
      have e : ∀ a ∈ Finset.range (r + i + 1),
          ∑ j, c j • ((((r + i).choose a : ℕ) : S) * ρ.ptr a A * (σ j).ptr (r + i - a) A) =
            (((r + i).choose a : ℕ) : S) * ρ.ptr a A *
              (if r + i - a = i then ((A τ) ^ i).trace else 0) := by
        intro a _
        rw [← hσ A (r + i - a) (by omega), Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
      rw [Finset.sum_congr rfl e, Finset.sum_eq_single r]
      · rw [if_pos (by omega), Algebra.smul_def, map_natCast, mul_assoc]
      · intro a ha har
        rw [Finset.mem_range] at ha
        rw [if_neg (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    simp only [Pi.smul_apply, Finset.sum_apply]
    have e2 : ∑ j, c j • ((ρ.tensor (σ j)).ptr (r + i) A * trProd l A) =
        (∑ j, c j • (ρ.tensor (σ j)).ptr (r + i) A) * trProd l A := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => (smul_mul_assoc _ _ _).symm
    rw [e2, key, smul_mul_assoc, smul_smul, inv_mul_cancel₀ hne, one_smul]
    simp only [trProd, List.map_cons, List.prod_cons, mul_assoc]

theorem trProd_mem_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (l : List (ι × ℕ)) (hl : ∀ x ∈ l, 1 ≤ x.2) (hs : (l.map Prod.snd).sum = n) :
    (fun A : Mat m S => trProd l A) ∈ Reach m n S := by
  have h := ptr_mul_trProd_mem_reach n S l hl 0 (by simpa using hs) (PolyRep.triv m)
  convert h using 2 with A
  have : (PolyRep.triv m).ptr 0 A = 1 := by
    rw [PolyRep.ptr, pow_zero, Matrix.trace_one, Fintype.card_fin]
    exact Nat.cast_one
  rw [this, one_mul]

end GlobalTheory.GoodMetric.ChernSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpanStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (l : List (ι × ℕ)), (∀ x ∈ l, 1 ≤ x.2) → (l.map Prod.snd).sum = n → (fun A : Mat m S => trProd l A) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach <;> assumption)
end
