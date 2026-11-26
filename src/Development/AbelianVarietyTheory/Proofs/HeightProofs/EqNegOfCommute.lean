module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanish
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FrameBasisMatrixOrthogonalProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ComplexStructureOfInvolutionsProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ComplexStructureOfInvolutionsProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCxAlg

variable {D : D7}

theorem actC_actC (V W : HSp D) (g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h h' : Matrix (Fin W.rank) (Fin W.rank) ℂ) (x : WC V W) :
    actC V W g h (actC V W g' h' x) = actC V W (g * g') (h * h') x := by
  unfold actC
  split_ifs <;> simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem actC_smul (V W : HSp D) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : Matrix (Fin W.rank) (Fin W.rank) ℂ) (c : ℂ) (x : WC V W) :
    actC V W g h (c • x) = c • actC V W g h x := by
  unfold actC
  split_ifs <;> simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem actC_one (V W : HSp D) (x : WC V W) : actC V W 1 1 x = x := by
  unfold actC
  split_ifs <;> simp

theorem hC_actC (V W : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : Matrix (Fin W.rank) (Fin W.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ)
    (hh : hᴴ * gramAt D W τ * h = gramAt D W τ) (x y : WC V W) :
    hC V W τ (actC V W g h x) (actC V W g h y) = hC V W τ x y := by
  unfold hC actC
  split_ifs with hr
  · rw [GlobalTheory.DualPairCheck.sum_small, GlobalTheory.DualPairCheck.sum_small]
    exact GlobalTheory.DualPairCheck.inv_small (starRingEnd ℂ) Complex.conj_conj _ _ _ _ hg hh x y
  · rw [GlobalTheory.DualPairCheck.sum_large, GlobalTheory.DualPairCheck.sum_large]
    exact GlobalTheory.DualPairCheck.inv_large (starRingEnd ℂ) Complex.conj_conj _ _ _ _ hg hh x y

theorem I_smul_unitary {n : ℕ} {G t : Matrix (Fin n) (Fin n) ℂ} (h : tᴴ * G * t = G) :
    (Complex.I • t)ᴴ * G * (Complex.I • t) = G := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h]
  simp

theorem cx_alg : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → (∀ x, jAt V W τ s s' (jAt V W τ s s' x) = -x) ∧ (∀ x y, symplC V W τ (jAt V W τ s s' x) (jAt V W τ s s' y) = symplC V W τ x y) ∧ (∀ g h, Commute g (thAt V τ s) → Commute h (thAt W τ s') → ∀ x, jAt V W τ s s' (actC V W g h x) = actC V W g h (jAt V W τ s s' x)) ∧ ∃ g ∈ KAt V τ s, ∃ h ∈ KAt W τ s', ∀ x, jAt V W τ s s' x = actC V W g h x := by
  intro D V W τ s s' hV hW
  refine ⟨fun x => ?_, fun x y => ?_, fun g h hg hh x => ?_, ?_⟩
  · unfold jAt
    rw [actC_smul, actC_actC, hV.1, hW.1, actC_one, smul_smul, Complex.I_mul_I, neg_one_smul]
  · unfold symplC jAt
    rw [hC_smul_left, hC_smul_right, hC_actC V W τ _ _ hV.2.1 hW.2.1, ← mul_assoc (starRingEnd ℂ Complex.I),
      Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  · unfold jAt
    rw [actC_smul, actC_actC, actC_actC, hg.eq, hh.eq]
  · by_cases hr : V.rank ≤ W.rank
    · refine ⟨thAt V τ s, ⟨hV.2.1, rfl⟩, Complex.I • thAt W τ s',
        ⟨I_smul_unitary hW.2.1, by rw [Matrix.smul_mul, Matrix.mul_smul]⟩, fun x => ?_⟩
      unfold jAt actC
      rw [if_pos hr, if_pos hr, Matrix.transpose_smul, Matrix.mul_smul]
    · refine ⟨Complex.I • thAt V τ s,
        ⟨I_smul_unitary hV.2.1, by rw [Matrix.smul_mul, Matrix.mul_smul]⟩, thAt W τ s', ⟨hW.2.1, rfl⟩, fun x => ?_⟩
      unfold jAt actC
      rw [if_neg hr, if_neg hr, Matrix.smul_mul, Matrix.smul_mul]

end GlobalTheory.FockCxAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ComplexStructureOfInvolutionsPropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexStructureOfInvolutions_properties : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → (∀ x, jAt V W τ s s' (jAt V W τ s s' x) = -x) ∧ (∀ x y, symplC V W τ (jAt V W τ s s' x) (jAt V W τ s s' y) = symplC V W τ x y) ∧ (∀ g h, Commute g (thAt V τ s) → Commute h (thAt W τ s') → ∀ x, jAt V W τ s s' (actC V W g h x) = actC V W g h (jAt V W τ s s' x)) ∧ ∃ g ∈ KAt V τ s, ∃ h ∈ KAt W τ s', ∀ x, jAt V W τ s s' x = actC V W g h x := by
  first | exact @GlobalTheory.FockCxAlg.cx_alg | exact GlobalTheory.FockCxAlg.cx_alg | (intros; apply GlobalTheory.FockCxAlg.cx_alg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.JpqMulMonomialEqMulSignDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.JpqMulMonomialEqMulSignDiagonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MonomialSign

theorem diagonal_mul_eq {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hcard : Fintype.card κ = Fintype.card ι) (ε : ι → ℝ) (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (M : Matrix ι κ ℂ) (d : κ → ℝ) (hd : ∀ i, d i ≠ 0)
    (hM : Mᴴ * Matrix.diagonal (fun a => (ε a : ℂ)) * M = Matrix.diagonal (fun i => (d i : ℂ)))
    (hrow : ∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) :
    Matrix.diagonal (fun a => (ε a : ℂ)) * M
      = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  have hsum : ∀ i, d i = ∑ a, ε a * Complex.normSq (M a i) := by
    intro i
    have h := congrFun (congrFun hM i) i
    rw [Matrix.diagonal_apply_eq, Matrix.mul_apply] at h
    apply Complex.ofReal_injective
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self,
      Complex.star_def]
    ring
  have hex : ∀ i, ∃ a, M a i ≠ 0 := by
    intro i
    by_contra hne
    push Not at hne
    apply hd i
    rw [hsum i]
    simp [hne]
  choose r hr using hex
  have hinj : Function.Injective r := fun i j hij => hrow (r i) i j (hr i) (hij ▸ hr j)
  have hbij : Function.Bijective r :=
    (Fintype.bijective_iff_injective_and_card r).2 ⟨hinj, hcard⟩
  have huniq : ∀ a i, M a i ≠ 0 → a = r i := by
    intro a i h
    obtain ⟨j, rfl⟩ := hbij.2 a
    rw [hrow (r j) i j h (hr j)]
  ext a i
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : M a i = 0
  · simp [h]
  · have ha := huniq a i h
    have hdi : d i = ε a * Complex.normSq (M a i) := by
      rw [hsum i]
      refine Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)
      have : M b i = 0 := by
        by_contra hb'
        exact hb ((huniq b i hb').trans ha.symm)
      simp [this]
    have hpos : 0 < Complex.normSq (M a i) := Complex.normSq_pos.2 h
    rcases hε a with h1 | h1
    · have : 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]
    · have : ¬ 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]

theorem Jpq_mul_eq : ∀ (n p q : ℕ), p + q = n → ∀ (M : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) → Mᴴ * Formalism.UG.Jpq p q * M = Matrix.diagonal (fun i => (d i : ℂ)) → (∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) → Formalism.UG.Jpq p q * M = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  intro n p q hn M d hd hM hrow
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal
      (fun a => ((Sum.elim (fun _ => 1) (fun _ => -1) a : ℝ) : ℂ)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hJ] at hM ⊢
  refine diagonal_mul_eq (by simp [hn]) _ ?_ M d hd hM hrow
  rintro (a | a) <;> simp

end GlobalTheory.MonomialSign
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.JpqMulMonomialEqMulSignDiagonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Jpq_mul_monomial_eq_mul_sign_diagonal : ∀ (n p q : ℕ), p + q = n → ∀ (M : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) → Mᴴ * Formalism.UG.Jpq p q * M = Matrix.diagonal (fun i => (d i : ℂ)) → (∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) → Formalism.UG.Jpq p q * M = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  first | exact @GlobalTheory.MonomialSign.Jpq_mul_eq | exact GlobalTheory.MonomialSign.Jpq_mul_eq | (intros; apply GlobalTheory.MonomialSign.Jpq_mul_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HermitianMajorantIsCartanInvolutionAndCommuteIff
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HermitianMajorantIsCartanInvolutionAndCommuteIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.CartanRel

theorem J_mul_J (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem J_conjTranspose (p q : ℕ) : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem isKC_iff {p q : ℕ} (b : Mat p q) : IsKC b ↔ b * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * b := by
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hJ]
  constructor
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases i with i | i <;> rcases j with j | j
    · simp
    · simp [h (Sum.inl i) (Sum.inr j) (by simp [sameBlock])]
    · simp [h (Sum.inr i) (Sum.inl j) (by simp [sameBlock])]
    · simp
  · intro h i j hij
    have e := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    rcases i with i | i <;> rcases j with j | j
    · simp [sameBlock] at hij
    · simp only [Sum.elim_inl, Sum.elim_inr] at e
      linear_combination (-1 / 2 : ℂ) * e
    · simp only [Sum.elim_inl, Sum.elim_inr] at e
      linear_combination (1 / 2 : ℂ) * e
    · simp [sameBlock] at hij

theorem cartan_rel : ∀ (n p q : ℕ), p + q = n → ∀ (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (G t : Matrix (Fin n) (Fin n) ℂ), G.det ≠ 0 → Aᴴ * Formalism.UG.Jpq p q * A = G → Formalism.UG.Jpq p q * A = A * t → IsCart G t ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, (∃ b : Mat p q, IsKC b ∧ b * A = A * g) ↔ Commute g t := by
  intro n p q hn A G t hG hA ht
  have hJ := J_mul_J p q
  have hJc := J_conjTranspose p q
  generalize hJdef : Formalism.UG.Jpq p q = J at hJ hJc hA ht
  obtain ⟨B, hBA, hAB⟩ : ∃ B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ, B * A = 1 ∧ A * B = 1 := by
    have h1 : (G⁻¹ * (Aᴴ * J)) * A = 1 := by
      rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ (Ne.isUnit hG)]
    exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 h1⟩
  have cancel : ∀ x y : Matrix (Fin n) (Fin n) ℂ, A * x = A * y → x = y := by
    intro x y h
    have := congrArg (B * ·) h
    simpa only [← Matrix.mul_assoc, hBA, Matrix.one_mul] using this
  have hJJ : J * (J * A) = A := by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hGt : G * t = Aᴴ * A := by
    rw [← hA, Matrix.mul_assoc, ← ht, Matrix.mul_assoc, hJJ]
  refine ⟨⟨?_, ?_, ?_⟩, fun g => ⟨?_, ?_⟩⟩
  · apply cancel
    rw [← Matrix.mul_assoc, ← ht, Matrix.mul_assoc, ← ht, hJJ, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hGt, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, ← ht,
      Matrix.conjTranspose_mul, hJc, hA]
  · rw [hGt]
    refine Matrix.PosDef.conjTranspose_mul_self A ?_
    intro x y h
    have := congrArg (B.mulVec) h
    simpa only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] using this
  · rintro ⟨b, hb, hbA⟩
    rw [isKC_iff, hJdef] at hb
    apply cancel
    calc A * (g * t) = b * (J * A) := by rw [← Matrix.mul_assoc, ← hbA, Matrix.mul_assoc, ← ht]
      _ = J * (A * g) := by rw [← Matrix.mul_assoc, hb, Matrix.mul_assoc, hbA]
      _ = A * (t * g) := by rw [← Matrix.mul_assoc, ht, Matrix.mul_assoc]
  · intro h
    refine ⟨A * g * B, ?_, ?_⟩
    · rw [isKC_iff, hJdef]
      have hBJ : B * J = t * B := by
        calc B * J = B * (J * A) * B := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc, hAB, Matrix.mul_one]
          _ = t * B := by rw [ht, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
      calc A * g * B * J = A * (g * t) * B := by
            rw [Matrix.mul_assoc, hBJ]; simp only [Matrix.mul_assoc]
        _ = A * t * (g * B) := by rw [h.eq]; simp only [Matrix.mul_assoc]
        _ = J * (A * g * B) := by rw [← ht]; simp only [Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, hBA, Matrix.mul_one]

end GlobalTheory.FockCompare.CartanRel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HermitianMajorantIsCartanInvolutionAndCommuteIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMajorant_isCartanInvolution_and_commute_iff : ∀ (n p q : ℕ), p + q = n → ∀ (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (G t : Matrix (Fin n) (Fin n) ℂ), G.det ≠ 0 → Aᴴ * Formalism.UG.Jpq p q * A = G → Formalism.UG.Jpq p q * A = A * t → IsCart G t ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, (∃ b : Mat p q, IsKC b ∧ b * A = A * g) ↔ Commute g t := by
  first | exact @GlobalTheory.FockCompare.CartanRel.cartan_rel | exact GlobalTheory.FockCompare.CartanRel.cartan_rel | (intros; apply GlobalTheory.FockCompare.CartanRel.cartan_rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKilledByOperatorProductsSuccCreationApply
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKilledByOperatorProductsSuccCreationApply
namespace GlobalTheory.FockCompare.WeylCreate

open GlobalTheory.FockCompare

variable {I M : Type} [AddCommGroup M] [Module ℂ M] {a : I → Module.End ℂ M}

theorem killed_succ_iff (N : ℕ) (m : M) : Killed a (N + 1) m ↔ ∀ i, Killed a N (a i m) := by
  constructor
  · intro h i l hl
    have := h (l ++ [i]) (by simp [hl])
    simpa [List.foldr_append] using this
  · intro h l hl
    rcases List.eq_nil_or_concat l with rfl | ⟨l', i, rfl⟩
    · simp at hl
    · have := h i l' (by simpa using hl)
      simpa [List.foldr_append] using this

theorem foldr_add_smul (l : List I) (β : ℂ) (x y : M) :
    l.foldr (fun i x => a i x) (x + β • y) =
      l.foldr (fun i x => a i x) x + β • l.foldr (fun i x => a i x) y := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, map_add (f := _), map_smul]

theorem foldr_zero (l : List I) : l.foldr (fun i x => a i x) (0 : M) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, map_zero]

theorem killed_create : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a : I → Module.End ℂ M) (c : Module.End ℂ M),
    (∀ i, ∃ β : ℂ, a i * c - c * a i = β • (1 : Module.End ℂ M)) →
    ∀ (N : ℕ) (m : M), Killed a N m → Killed a (N + 1) (c m) := by
  intro I M _ _ a c hc N
  induction N with
  | zero =>
    intro m hm l _
    have h0 : m = 0 := hm [] rfl
    rw [h0, map_zero]
    exact foldr_zero l
  | succ N ih =>
    intro m hm
    rw [killed_succ_iff]
    intro i
    obtain ⟨β, hβ⟩ := hc i
    have e : a i (c m) = c (a i m) + β • m := by
      have := LinearMap.congr_fun hβ m
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      rw [← this]; abel
    have h1 := ih (a i m) ((killed_succ_iff N m).1 hm i)
    intro l hl
    rw [e, foldr_add_smul, h1 l hl, hm l hl, smul_zero, add_zero]

end GlobalTheory.FockCompare.WeylCreate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKilledByOperatorProductsSuccCreationApplyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKilledByOperatorProducts_succ_creation_apply : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a : I → Module.End ℂ M) (c : Module.End ℂ M), (∀ i, ∃ β : ℂ, a i * c - c * a i = β • (1 : Module.End ℂ M)) → ∀ (N : ℕ) (m : M), Killed a N m → Killed a (N + 1) (c m) := by
  first | exact @GlobalTheory.FockCompare.WeylCreate.killed_create | exact GlobalTheory.FockCompare.WeylCreate.killed_create | (intros; apply GlobalTheory.FockCompare.WeylCreate.killed_create <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeQuasiInvariantAndLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeQuasiInvariantAndLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem dRho_quasi_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ), ((∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) → ∀ γ w, dRho ψ V W L f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * dRho ψ V W L f w) ∧ ∀ u : WA V W, (∀ t, symplH V W u (L t) = 0 ∧ symplH V W (L t) u = 0) → Heisenberg₂ ψ V W u f = f → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
  intro D ψ V W L f
  refine ⟨fun hf γ w => ?_, fun u hu hf => ?_⟩
  · unfold dRho
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    exact GlobalTheory.DualPairCheck.heis_quasi ψ V W (L t) f hf γ w
  · funext w
    have key : ∀ t, Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) = Heisenberg₂ ψ V W (L t) f := by
      intro t
      conv_rhs => rw [← hf]
      rw [GlobalTheory.DualPairCheck.heis_heis, GlobalTheory.DualPairCheck.heis_heis, (hu t).1, (hu t).2, add_comm]
    have : (fun t => Heisenberg₂ ψ V W (L t) f w) = fun t => Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) w := by
      funext t; rw [key]
    conv_rhs => unfold dRho; rw [this]
    unfold dRho
    rw [Heisenberg₂, ← deriv_const_mul_field]
    rfl

end GlobalTheory.FockCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeQuasiInvariantAndLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_quasiInvariant_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ), ((∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) → ∀ γ w, dRho ψ V W L f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * dRho ψ V W L f w) ∧ ∀ u : WA V W, (∀ t, symplH V W u (L t) = 0 ∧ symplH V W (L t) u = 0) → Heisenberg₂ ψ V W u f = f → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
  first | exact @GlobalTheory.FockCompare.dRho_quasi_and_level | exact GlobalTheory.FockCompare.dRho_quasi_and_level | (intros; apply GlobalTheory.FockCompare.dRho_quasi_and_level <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem exists_chart (hθ : IsInfFam θ) : ∃ σ, Chart θ σ := by
  obtain ⟨ρ, h1, h2, h3⟩ := GlobalTheory.T.exists_real_chart_infiniteAdeles_cmType D θ hθ (GlobalTheory.T.cmType_restrict_realSubfield_infinitePlace_bijective D)
  exact GlobalTheory.T.exists_isArchimedeanAdeleChart_of_real_chart D θ hθ ρ h1 h2 h3

theorem valTau_sympl (hθ : IsInfFam θ) (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W) :
    valTau θ τ (sympl V W x y) = symplC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := GlobalTheory.T.symplectic_val_tau_compat D θ hθ V W τ x y

theorem valTau_sub (τ : D.what₂.Tau) (a b : AF D.host.F) : valTau θ τ (a - b) = valTau θ τ a - valTau θ τ b := by
  unfold valTau
  rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_sub, Complex.sub_re]

theorem valTau_neg (τ : D.what₂.Tau) (a : AF D.host.F) : valTau θ τ (-a) = -valTau θ τ a := by
  unfold valTau
  rw [RingHom.map_neg, RingHom.map_neg, RingHom.map_neg, Complex.neg_re]

theorem Chart.wAt_iota (h : Chart θ σ) (V W : HSp D) (z : RW V W) (τ : D.what₂.Tau) :
    wAt θ V W τ (iotaW σ V W z) = z τ := congrFun (h.pi_iota V W z) τ

theorem Chart.omR_skew (h : Chart θ σ) (V W : HSp D) (u v : RW V W) : omR V W v u = -omR V W u v := by
  rw [omR_apply, omR_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← h.wAt_iota V W u τ, ← h.wAt_iota V W v τ, ← valTau_sympl h.inf, ← valTau_sympl h.inf,
    GlobalTheory.DualPairCheck.sympl_skew, valTau_neg]

theorem isRealW_neg {V W : HSp D} {x : WA V W} (hx : IsRealW V W x) : IsRealW V W (-x) := by
  ext i j
  have h1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show finPart D (-(x i j)) = 0
  rw [RingHom.map_neg, h1, neg_zero]

theorem Rel.cart {V : HSp D} (hV : V.SigOK) {τ : D.what₂.Tau} {A s} (h : Rel V τ A s) :
    IsCart (gramAt D V τ) (thAt V τ s) ∧ ∀ g : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (∃ b : Mat (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2, IsKC b ∧ b * A = A * g) ↔ Commute g (thAt V τ s) := by
  refine GlobalTheory.T.hermitianMajorant_isCartanInvolution_and_commute_iff _ _ _ ?_ A _ _ ?_ h.1 h.2
  · have := (Formalism.UG.P.sig_data _ _ _ (hV (tauE D τ))).1
    rw [Fintype.card_fin] at this
    exact this.symm
  · have : (gramAt D V τ).det = tauE D τ V.gram.det := ((tauE D τ).map_det V.gram).symm
    rw [this]
    exact (map_ne_zero _).2 (gram_det_ne V)

theorem isKinf_iff {V : HSp D} (hV : V.SigOK) {A} {s : InvFam V} (h : ∀ τ, Rel V τ (A τ) (s τ)) (g : GA D V) :
    IsKinf θ V A g ↔ g ∈ Kinf θ V s :=
  and_congr Iff.rfl (forall_congr' fun τ => ((h τ).cart hV).2 _)

theorem eq_neg_of_commute {R : Type} [AddCommGroup R] (J j : R →+ R) (hJ : ∀ z, J (J z) = -z) (hj : ∀ z, j (j z) = -z)
    (hc : ∀ z, J (j z) = j (J z)) (h0 : ∀ y, J y = j y → y = 0) (z : R) : J z = -j z := by
  rw [eq_neg_iff_add_eq_zero]
  apply h0
  rw [map_add (f := _), map_add (f := _), hJ, hj, hc, add_comm]

section Cx

variable {V W : HSp D} {s : InvFam V} {s' : InvFam W}
  (hs : ∀ τ, IsCart (gramAt D V τ) (thAt V τ (s τ))) (hs' : ∀ τ, IsCart (gramAt D W τ) (thAt W τ (s' τ)))
include hs hs'

theorem jR_jR (z : RW V W) : jR V W s s' (jR V W s s' z) = -z :=
  funext fun τ => (GlobalTheory.T.complexStructureOfInvolutions_properties D V W τ _ _ (hs τ) (hs' τ)).1 (z τ)

theorem omR_jR (u v : RW V W) : omR V W (jR V W s s' u) (jR V W s s' v) = omR V W u v :=
  Finset.sum_congr rfl fun τ _ => (GlobalTheory.T.complexStructureOfInvolutions_properties D V W τ _ _ (hs τ) (hs' τ)).2.1 (u τ) (v τ)

theorem symplC_jAt_le (τ : D.what₂.Tau) (x : WC V W) : symplC V W τ (jAt V W τ (s τ) (s' τ) x) x ≤ 0 := by
  by_cases hx : x = 0
  · have := symplC_smul_right V W τ 0 (jAt V W τ (s τ) (s' τ) x) x
    rw [zero_smul, zero_mul] at this
    rw [hx] at this ⊢
    exact this.le
  · have := GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos D V W τ _ _ (hs τ) (hs' τ) x hx
    linarith

theorem Chart.omR_pos (h : Chart θ σ) (u : RW V W) (hu : u ≠ 0) : 0 < omR V W u (jR V W s s' u) := by
  rw [h.omR_skew, omR_apply, ← Finset.sum_neg_distrib]
  obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hu
  exact Finset.sum_pos' (fun τ _ => neg_nonneg.2 (symplC_jAt_le hs hs' τ _))
    ⟨τ, Finset.mem_univ _, GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos D V W τ _ _ (hs τ) (hs' τ) (u τ) hτ⟩

end Cx

theorem isFockCx_sign (h : Chart θ σ) {V W : HSp D} (hV : V.SigOK) (hW : W.SigOK) {A B} {s : InvFam V} {s' : InvFam W}
    (hA : ∀ τ, Rel V τ (A τ) (s τ)) (hB : ∀ τ, Rel W τ (B τ) (s' τ)) {J : WA V W →+ WA V W}
    (hJ : IsFockCx θ V W A B J) :
    (∀ x, IsRealW V W x → piW θ V W (J x) = jR V W s s' (piW θ V W x)) ∨
      ∀ x, IsRealW V W x → piW θ V W (J x) = (-jR V W s s') (piW θ V W x) := by
  have hs := fun τ => ((hA τ).cart hV).1
  have hs' := fun τ => ((hB τ).cart hW).1
  choose g hg g' hg' hgj using fun τ => (GlobalTheory.T.complexStructureOfInvolutions_properties D V W τ _ _ (hs τ) (hs' τ)).2.2.2
  obtain ⟨k, hk, hkg⟩ := GlobalTheory.T.exists_real_point_unitary_with_components D θ σ h V g fun τ => (hg τ).1
  obtain ⟨k', hk', hkg'⟩ := GlobalTheory.T.exists_real_point_unitary_with_components D θ σ h W g' fun τ => (hg' τ).1
  have hK : IsKinf θ V A k := (isKinf_iff hV hA k).2 ⟨hk, fun τ => by rw [hkg]; exact (hg τ).2⟩
  have hK' : IsKinf θ W B k' := (isKinf_iff hW hB k').2 ⟨hk', fun τ => by rw [hkg']; exact (hg' τ).2⟩
  have hact := (GlobalTheory.T.adelicUnitary_action_at_real_place D θ h.inf).2 V W k k'
  have hT : ∀ x, piW θ V W (actHom V W k k' x) = jR V W s s' (piW θ V W x) := fun x => funext fun τ => by
    rw [piW_apply, (hact x).1, hkg, hkg']
    exact (hgj τ _).symm
  let J' : RW V W →+ RW V W := (piW θ V W).comp (J.comp (iotaW σ V W))
  have hJ' : ∀ z, J' z = piW θ V W (J (iotaW σ V W z)) := fun _ => rfl
  have h1 : ∀ z, J' (J' z) = -z := fun z => by
    rw [hJ', hJ', h.iota_pi (hJ.real _ (h.real_iota V W z)), hJ.sq _ (h.real_iota V W z), map_neg, h.pi_iota]
  have h2 : ∀ z, J' (jR V W s s' z) = jR V W s s' (J' z) := fun z => by
    have e : iotaW σ V W (jR V W s s' z) = actHom V W k k' (iotaW σ V W z) :=
      h.real_ext (h.real_iota V W _) ((hact _).2 (h.real_iota V W z)) (by rw [hT, h.pi_iota, h.pi_iota])
    rw [hJ', hJ', e, hJ.kcomm k k' hK hK' _ (h.real_iota V W z), hT]
  have h3 : ∀ z τ, valTau θ τ (sympl V W (J (iotaW σ V W z)) (iotaW σ V W z)) = symplC V W τ (J' z τ) (z τ) :=
    fun z τ => by rw [valTau_sympl h.inf, h.wAt_iota]; rfl
  have h4 : ∀ y : RW V W, (∀ τ, 0 ≤ symplC V W τ (jR V W s s' y τ) (y τ)) → y = 0 := fun y hy => funext fun τ => by
    by_contra hne
    have := GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos D V W τ _ _ (hs τ) (hs' τ) (y τ) hne
    have h5 := hy τ
    rw [jR_apply] at h5
    linarith
  obtain ⟨ε, hε | hε, hd⟩ := hJ.defin
  · refine Or.inr fun x hx => ?_
    have := eq_neg_of_commute J' (jR V W s s').toAddMonoidHom h1 (jR_jR hs hs') h2 (fun y hy => h4 y fun τ => by
      have h5 := (hd _ (h.real_iota V W y)).1 τ
      rw [hε, one_mul, h3, hy] at h5
      exact h5) (piW θ V W x)
    rw [hJ', h.iota_pi hx] at this
    exact this
  · refine Or.inl fun x hx => ?_
    have := eq_neg_of_commute J' (-jR V W s s').toAddMonoidHom h1 (fun z => by
        show -jR V W s s' (-jR V W s s' z) = -z
        rw [map_neg, neg_neg, jR_jR hs hs']) (fun z => by
        show J' (-jR V W s s' z) = -jR V W s s' (J' z)
        rw [map_neg, h2]) (fun y hy => h4 y fun τ => by
      have h5 := (hd _ (h.real_iota V W y)).1 τ
      have h6 : J' y τ = (-1 : ℝ) • jR V W s s' y τ := by rw [hy, neg_one_smul]; rfl
      have h7 := symplC_smul_left V W τ (-1) (jR V W s s' y τ) (y τ)
      rw [hε, h3, h6] at h5
      have h8 := h5.trans_eq (congrArg (fun r : ℝ => -1 * r) h7)
      linarith) (piW θ V W x)
    rw [hJ', h.iota_pi hx] at this
    rw [this]
    exact neg_neg _

theorem actC_smul (V W : HSp D) (g h) (c : ℝ) (x : WC V W) : actC V W g h (c • x) = c • actC V W g h x := by
  unfold actC
  split_ifs <;> simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem isFockCx_of_sign (h : Chart θ σ) {V W : HSp D} (hV : V.SigOK) (hW : W.SigOK) {A B} {s : InvFam V} {s' : InvFam W}
    (hA : ∀ τ, Rel V τ (A τ) (s τ)) (hB : ∀ τ, Rel W τ (B τ) (s' τ)) {J : WA V W →+ WA V W} (hc : Continuous J)
    (hr : ∀ x, IsRealW V W x → IsRealW V W (J x)) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hJ : ∀ x, IsRealW V W x → ∀ τ, wAt θ V W τ (J x) = ε • jAt V W τ (s τ) (s' τ) (wAt θ V W τ x)) :
    IsFockCx θ V W A B J := by
  have hs := fun τ => ((hA τ).cart hV).1
  have hs' := fun τ => ((hB τ).cart hW).1
  have hal := fun τ => GlobalTheory.T.complexStructureOfInvolutions_properties D V W τ _ _ (hs τ) (hs' τ)
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  refine ⟨hc, hr, fun x hx => ?_, fun x y hx hy => ?_, fun k k' hk hk' x hx => ?_, -ε, ?_, fun x hx => ⟨fun τ => ?_, fun h0 => ?_⟩⟩
  · refine h.real_ext (hr _ (hr _ hx)) (isRealW_neg hx) (funext fun τ => ?_)
    rw [map_neg, piW_apply, hJ _ (hr _ hx), hJ _ hx, jAt_smul, smul_smul, hεε, one_smul, (hal τ).1]
    rfl
  · rw [← sub_eq_zero]
    refine (GlobalTheory.T.realAdele_ext_and_standardCharacter_formula D θ σ h _ ?_).1 fun τ => ?_
    · rw [map_sub, (GlobalTheory.T.symplectic_real_part_vanish D V W _ _).1 (Or.inl (hr _ hx)), (GlobalTheory.T.symplectic_real_part_vanish D V W _ _).1 (Or.inl hx), sub_zero]
    · rw [valTau_sub, valTau_sympl h.inf, valTau_sympl h.inf, hJ _ hx, hJ _ hy, symplC_smul_left, symplC_smul_right,
        ← mul_assoc, hεε, one_mul, (hal τ).2.1, sub_self]
  · have hact := (GlobalTheory.T.adelicUnitary_action_at_real_place D θ h.inf).2 V W k k'
    refine h.real_ext (hr _ ((hact x).2 hx)) ((hact _).2 (hr _ hx)) (funext fun τ => ?_)
    rw [piW_apply, piW_apply, hJ _ ((hact x).2 hx), (hact _).1, (hact _).1, hJ _ hx,
      (hal τ).2.2.1 _ _ (((isKinf_iff hV hA k).1 hk).2 τ) (((isKinf_iff hW hB k').1 hk').2 τ)]
    exact (actC_smul V W _ _ ε _).symm
  · rcases hε with h | h <;> rw [h] <;> norm_num
  · rw [valTau_sympl h.inf, hJ _ hx, symplC_smul_left, ← mul_assoc, neg_mul, hεε]
    have := symplC_jAt_le hs hs' τ (wAt θ V W τ x)
    linarith
  · rw [← h.iota_pi hx, ← (iotaW σ V W).map_zero]
    congr 1
    funext τ
    by_contra hne
    have h1 := GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos D V W τ _ _ (hs τ) (hs' τ) (wAt θ V W τ x) hne
    have h2 := h0 τ
    rw [valTau_sympl h.inf, hJ _ hx, symplC_smul_left] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · rw [h3] at hεε; norm_num at hεε
    · rw [h3] at h1; norm_num at h1

section Killed

variable {I M : Type} [AddCommGroup M] [Module ℂ M] {a : I → Module.End ℂ M}

theorem foldr_lin (a : I → Module.End ℂ M) (l : List I) (m : M) :
    l.foldr (fun i x => a i x) m = (l.map a).prod m := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons, Module.End.mul_apply]

theorem Killed.succ {N : ℕ} {m : M} (h : Killed a N m) : Killed a (N + 1) m := by
  intro l hl
  obtain _ | ⟨i, l⟩ := l
  · simp at hl
  · rw [List.foldr_cons, h l (by simpa using hl), map_zero]

theorem Killed.mono {N N' : ℕ} {m : M} (h : Killed a N m) (hN : N ≤ N') : Killed a N' m := by
  induction hN with
  | refl => exact h
  | step _ ih => exact ih.succ

def nilSub (a : I → Module.End ℂ M) : Submodule ℂ M where
  carrier := {m | ∃ N, Killed a N m}
  zero_mem' := ⟨0, fun l _ => by rw [foldr_lin, map_zero]⟩
  add_mem' := fun {x y} ⟨N, hN⟩ ⟨N', hN'⟩ => ⟨max N N', fun l hl => by
    have h1 := hN.mono (le_max_left N N') l hl
    have h2 := hN'.mono (le_max_right N N') l hl
    rw [foldr_lin] at h1 h2 ⊢
    rw [map_add (f := _), h1, h2, add_zero]⟩
  smul_mem' := fun c x ⟨N, hN⟩ => ⟨N, fun l hl => by
    have h1 := hN l hl
    rw [foldr_lin] at h1 ⊢
    rw [map_smul, h1, smul_zero]⟩

end Killed

section Fock

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}

theorem Chart.psi_symplH (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (w : WA V W) (x : RW V W) :
    ψ (symplH V W w (iotaW σ V W x)) =
      Complex.exp (-(Real.pi * Complex.I) * (omR V W (piW θ V W w) x : ℝ)) := by
  unfold symplH
  rw [(GlobalTheory.T.realAdele_ext_and_standardCharacter_formula D θ σ h _ ((GlobalTheory.T.symplectic_real_part_vanish D V W _ _).1 (Or.inr (h.real_iota V W x)))).2 ψ hψ, omR_apply]
  congr 3
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [valTau_sympl h.inf, h.wAt_iota]
  rfl

theorem Chart.dRho_eq_hD (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WA V W} (hL : IsRealDir V W L)
    (f : WA V W → ℂ) : dRho ψ V W L f = hD (iotaW σ V W) (piW θ V W) (omR V W) (piW θ V W (L 1)) f := by
  funext w
  unfold dRho hD Heisenberg₂
  congr 1
  funext t
  rw [(GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines D θ σ h V W).2.1 L hL t, h.psi_symplH hψ]

theorem Chart.exists_line (h : Chart θ σ) (u : RW V W) : ∃ L : ℝ →+ WA V W, IsRealDir V W L ∧ piW θ V W (L 1) = u := by
  obtain ⟨L, hL, e⟩ := (GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines D θ σ h V W).2.2 u
  exact ⟨L, hL, by rw [e, one_smul, h.pi_iota]⟩

theorem Chart.pi_line (h : Chart θ σ) {L : ℝ →+ WA V W} (hL : IsRealDir V W L) (t : ℝ) :
    piW θ V W (L t) = t • piW θ V W (L 1) := by
  rw [(GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines D θ σ h V W).2.1 L hL t, h.pi_iota]

theorem Chart.isJPair_iff (h : Chart θ σ) (s : InvFam V) (s' : InvFam W) (L L' : ℝ →+ WA V W) :
    IsJPair θ V W s s' L L' ↔ IsRealDir V W L ∧ IsRealDir V W L' ∧ piW θ V W (L' 1) = jR V W s s' (piW θ V W (L 1)) := by
  refine ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, funext fun τ => h3 1 τ⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun t τ => ?_⟩⟩
  have : piW θ V W (L' t) = jR V W s s' (piW θ V W (L t)) := by
    rw [h.pi_line h1, h.pi_line h2, map_smul, h3]
  exact congrFun this τ

theorem Chart.sm (h : Chart θ σ) {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f) : Sm (iotaW σ V W) f :=
  ((GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines D θ σ h V W).1 f).1 hf.smooth

theorem Chart.theta_hD (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f)
    (u : RW V W) : IsThetaFun ψ V W (hD (iotaW σ V W) (piW θ V W) (omR V W) u f) := by
  have hsm := (GlobalTheory.T.heisenbergDirectionalDeriv_formula_and_smooth _ _ (iotaW σ V W) (piW θ V W) (omR V W) (h.pi_iota V W) f (h.sm hf) u).2
  obtain ⟨L, hL, rfl⟩ := h.exists_line u
  rw [← h.dRho_eq_hD hψ hL] at hsm ⊢
  have hd := GlobalTheory.T.heisenbergDerivative_quasiInvariant_and_level D ψ V W L f
  have hlev : ∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
    obtain ⟨U, hU, hl⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => hd.2 u (fun t => ?_) (hl u hu h0)⟩
    have h1 : sympl V W u (L t) = 0 :=
      Prod.ext ((GlobalTheory.T.symplectic_real_part_vanish D V W _ _).2 (Or.inl h0)) ((GlobalTheory.T.symplectic_real_part_vanish D V W _ _).1 (Or.inr (hL.2 t)))
    have h2 : sympl V W (L t) u = 0 :=
      Prod.ext ((GlobalTheory.T.symplectic_real_part_vanish D V W _ _).2 (Or.inr h0)) ((GlobalTheory.T.symplectic_real_part_vanish D V W _ _).1 (Or.inl (hL.2 t)))
    unfold symplH
    rw [h1, h2, mul_zero]
    exact ⟨rfl, rfl⟩
  exact ⟨hd.1 hf.quasi, hlev, GlobalTheory.T.continuous_of_heisenberg_level_and_smooth D θ σ h ψ hψ.1.1 V W _ hlev hsm,
    ((GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines D θ σ h V W).1 _).2 hsm⟩

theorem Chart.bounded (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f)
    (w : WA V W) : ∃ C : ℝ, ∀ x, ‖f (w + iotaW σ V W x)‖ ≤ C := by
  refine GlobalTheory.T.exists_le_of_continuous_of_spanning_periods _ (fun x => ‖f (w + iotaW σ V W x)‖) (h.sm hf w).continuous.norm _
    (GlobalTheory.T.span_realProjection_rationalPoints_eq_top D θ σ h V W) ?_
  rintro _ ⟨γ, rfl⟩
  obtain ⟨N, hN, e⟩ := GlobalTheory.T.norm_thetaFunction_periodic_real_variables D θ σ h ψ hψ.1.2.1 (GlobalTheory.T.exists_pos_nat_mem_open_adele_subgroup D.host.F) V W f hf γ
  exact ⟨N, hN, fun x => by rw [map_add (f := _), ← add_assoc, e]⟩

theorem Chart.killed_iff (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : Submodule ℂ (WA V W → ℂ)}
    {Dop : RW V W → Module.End ℂ M}
    (hD1 : ∀ u (f : M), ((Dop u f : M) : WA V W → ℂ) = hD (iotaW σ V W) (piW θ V W) (omR V W) u f)
    {J : WA V W →+ WA V W} (hc : Continuous J) (hr : ∀ x, IsRealW V W x → IsRealW V W (J x))
    (j : RW V W →ₗ[ℝ] RW V W) (hj : ∀ x, IsRealW V W x → piW θ V W (J x) = j (piW θ V W x)) (N : ℕ) (m : M) :
    (∀ Ls : Fin N → (ℝ →+ WA V W), (∀ i, IsRealDir V W (Ls i)) →
      (List.ofFn Ls).foldr (fun L g => annOp ψ V W J L g) m = 0) ↔
      Killed (fun u => Dop u + Complex.I • Dop (j u)) N m := by
  have key : ∀ l : List (ℝ →+ WA V W), (∀ L ∈ l, IsRealDir V W L) →
      l.foldr (fun L g => annOp ψ V W J L g) m =
        ((l.map fun L => piW θ V W (L 1)).foldr (fun u x => (Dop u + Complex.I • Dop (j u)) x) m : M) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons L l ih =>
      have hL := hl L List.mem_cons_self
      have hL' : IsRealDir V W (J.comp L) := ⟨hc.comp hL.1, fun t => hr _ (hL.2 t)⟩
      rw [List.foldr_cons, ih fun L' h' => hl L' (List.mem_cons_of_mem _ h'), List.map_cons, List.foldr_cons,
        LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hD1, hD1, ← hj _ (hL.2 1),
        ← h.dRho_eq_hD hψ hL]
      erw [← h.dRho_eq_hD hψ hL']
      rfl
  constructor
  · intro H l hl
    choose Lf hLf e using fun u : RW V W => h.exists_line u
    subst hl
    have h1 := H (fun i => Lf (l.get i)) fun i => hLf _
    have h2 : (List.ofFn fun i => Lf (l.get i)) = l.map Lf := by
      rw [show (fun i => Lf (l.get i)) = Lf ∘ l.get from rfl, ← List.map_ofFn, List.ofFn_get]
    rw [h2, key _ (by
      intro L hL
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hL
      exact hLf u), List.map_map] at h1
    have h3 : ((fun L : ℝ →+ WA V W => piW θ V W (L 1)) ∘ Lf) = id := funext e
    rw [h3, List.map_id] at h1
    exact Subtype.ext h1
  · intro H Ls hLs
    rw [key _ (by
      intro L hL
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hL
      exact hLs i), H _ (by simp)]
    rfl

theorem isPolFock_iff (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (hV : V.SigOK) (hW : W.SigOK) {A B}
    {s : InvFam V} {s' : InvFam W} (hA : ∀ τ, Rel V τ (A τ) (s τ)) (hB : ∀ τ, Rel W τ (B τ) (s' τ))
    {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f) : IsPolFock ψ θ V W A B f ↔ f ∈ polFun ψ θ V W s s' := by
  obtain ⟨σ, h⟩ := exists_chart hθ
  have hs := fun τ => ((hA τ).cart hV).1
  have hs' := fun τ => ((hB τ).cart hW).1
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_submodule_thetaFunctions D ψ V W
  have hform := fun f hf u => (GlobalTheory.T.heisenbergDirectionalDeriv_formula_and_smooth _ _ (iotaW σ V W) (piW θ V W) (omR V W) (h.pi_iota V W) f hf u).1
  obtain ⟨Dop, hD1, hD2, hD3⟩ := GlobalTheory.T.exists_heisenberg_derivative_linear_operators _ _ (iotaW σ V W) (piW θ V W) (omR V W) (h.pi_iota V W) hform M
    (fun f hf => h.sm ((hM f).1 hf)) fun u f hf => (hM _).2 (h.theta_hD hψ ((hM f).1 hf) u)
  have hκ : -(2 * Real.pi * Complex.I : ℂ) ≠ 0 := neg_ne_zero.2 Complex.two_pi_I_ne_zero
  have hcomm : ∀ u v, Dop u * Dop v - Dop v * Dop u =
      (-(2 * Real.pi * Complex.I) * (omR V W u v : ℝ) : ℂ) • (1 : Module.End ℂ M) := fun u v => by
    refine LinearMap.ext fun m => Subtype.ext ?_
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, hD1, hD1, hD1, hD1,
      GlobalTheory.T.heisenbergDerivative_commutator_relation _ _ (iotaW σ V W) (piW θ V W) (omR V W) (h.pi_iota V W) hform (h.omR_skew V W) _
        (h.sm ((hM _).1 m.2))]
    rfl
  set j := jR V W s s' with hjdef
  obtain ⟨hβ, n, e, lam, hlam, hE⟩ := GlobalTheory.T.canonicalCommutationRelations_weylNumber M _ Dop (omR V W) _ j hD2 hD3 hκ hcomm (h.omR_skew V W)
    (jR_jR hs hs') (omR_jR hs hs') (h.omR_pos hs hs')
  have hann : ∀ L L', IsJPair θ V W s s' L L' → ∀ m : M, ann ψ V W L L' m =
      ((Dop (piW θ V W (L 1)) + Complex.I • Dop (j (piW θ V W (L 1)))) m : M) := fun L L' hp m => by
    obtain ⟨h1, h2, h3⟩ := (h.isJPair_iff s s' L L').1 hp
    rw [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hD1, hD1, ← h3,
      ← h.dRho_eq_hD hψ h1, ← h.dRho_eq_hD hψ h2]
    rfl
  have hcre : ∀ L L', IsJPair θ V W s s' L L' → ∀ m : M, cre ψ V W L L' m =
      ((Dop (piW θ V W (L 1)) - Complex.I • Dop (j (piW θ V W (L 1)))) m : M) := fun L L' hp m => by
    obtain ⟨h1, h2, h3⟩ := (h.isJPair_iff s s' L L').1 hp
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_smul, hD1, hD1, ← h3,
      ← h.dRho_eq_hD hψ h1, ← h.dRho_eq_hD hψ h2]
    rfl
  have hpair : ∀ u, ∃ L L', IsJPair θ V W s s' L L' ∧ piW θ V W (L 1) = u := fun u => by
    obtain ⟨L, hL, e1⟩ := h.exists_line u
    obtain ⟨L', hL', e2⟩ := h.exists_line (j u)
    exact ⟨L, L', (h.isJPair_iff s s' L L').2 ⟨hL, hL', by rw [e1, e2]⟩, e1⟩
  have hnil : ∀ (N : ℕ) (m : M), Killed (fun u => Dop u + Complex.I • Dop (j u)) N m →
      (m : WA V W → ℂ) ∈ polFun ψ θ V W s s' := fun N m hm => by
    have := GlobalTheory.T.mem_of_isKilledByOperatorProducts_vacuum_creation _ M (fun u => Dop u + Complex.I • Dop (j u)) (fun u => Dop u - Complex.I • Dop (j u)) n e lam
      hlam hE (Submodule.span ℂ {m : M | IsFockMon ψ θ V W s s' m}) (fun m hm => Submodule.subset_span
        (IsFockMon.vac _ ⟨(hM _).1 m.2, fun L L' hp => by rw [hann L L' hp, hm]; rfl⟩)) (fun u m hm => by
        obtain ⟨L, L', hp, rfl⟩ := hpair u
        refine Submodule.map_span_le _ _ _ |>.2 (fun m' hm' => Submodule.subset_span ?_) (Submodule.mem_map_of_mem hm)
        show IsFockMon ψ θ V W s s' _
        rw [← hcre L L' hp]
        exact IsFockMon.cre L L' _ hp hm') N m hm
    exact Submodule.map_span_le M.subtype _ _ |>.2 (fun m' hm' => Submodule.subset_span hm')
      (Submodule.mem_map_of_mem this)
  constructor
  · rintro ⟨J, hJ, N, hN⟩
    rcases isFockCx_sign h hV hW hA hB hJ with hj | hj
    · exact hnil N ⟨f, (hM f).2 hf⟩ ((h.killed_iff hψ hD1 hJ.cont hJ.real j hj N ⟨f, (hM f).2 hf⟩).1 hN)
    · have hk := (h.killed_iff hψ hD1 hJ.cont hJ.real (-j) hj N ⟨f, (hM f).2 hf⟩).1 hN
      by_cases h0 : ∀ u : RW V W, u = 0
      · have : -j = j := LinearMap.ext fun u => by rw [h0 (j u), h0 ((-j) u)]
        rw [this] at hk
        exact hnil N _ hk
      · obtain ⟨u, hu⟩ := not_forall.1 h0
        obtain ⟨-, n', e', lam', hlam', hE'⟩ := GlobalTheory.T.canonicalCommutationRelations_weylNumber M _ Dop (-omR V W) (2 * Real.pi * Complex.I) (-j) hD2 hD3
          Complex.two_pi_I_ne_zero (fun u v => by rw [hcomm]; simp)
          (fun u v => by simp only [LinearMap.neg_apply]; rw [h.omR_skew])
          (fun u => by simp only [LinearMap.neg_apply, map_neg, neg_neg]; exact jR_jR hs hs' u)
          (fun u v => by simp only [LinearMap.neg_apply, map_neg, neg_neg]; rw [omR_jR hs hs'])
          (fun u hu => by simp only [LinearMap.neg_apply, map_neg, neg_neg]; exact h.omR_pos hs hs' u hu)
        have := GlobalTheory.T.mem_of_isKilledByOperatorProducts_vacuum_creation _ M (fun u => Dop u + Complex.I • Dop ((-j) u)) (fun u => Dop u - Complex.I • Dop ((-j) u))
          n' e' lam' hlam' hE' ⊥ (fun m hm => by
            rw [Submodule.mem_bot]
            refine Subtype.ext (GlobalTheory.T.eq_zero_of_hD_sub_I_smul_hD_eq_zero_of_bounded _ _ (iotaW σ V W) (piW θ V W) (omR V W) (h.pi_iota V W) hform
              (h.omR_skew V W) m (h.sm ((hM _).1 m.2)) (h.bounded hψ ((hM _).1 m.2)) u (j u) (h.omR_pos hs hs' u hu) ?_)
            have h3 : (Dop u + Complex.I • Dop ((-j) u)) m = 0 := hm u
            have h2 : Dop ((-j) u) = -Dop (j u) := by
              have := hD3 (-1) (j u)
              rw [neg_one_smul] at this
              rw [LinearMap.neg_apply, this]; simp
            rw [h2] at h3
            have h1 := congrArg Subtype.val h3
            simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, smul_neg, Submodule.coe_add,
              Submodule.coe_neg, Submodule.coe_smul, hD1] at h1
            rw [sub_eq_add_neg]
            exact h1)
          (fun i m hm => by rw [(Submodule.mem_bot _).1 hm, map_zero]; exact Submodule.zero_mem _) N _ hk
        have hf0 : f = 0 := congrArg Subtype.val ((Submodule.mem_bot _).1 this)
        rw [hf0]
        exact Submodule.zero_mem _
  · intro hp
    let J : WA V W →+ WA V W := (iotaW σ V W).comp (j.toAddMonoidHom.comp (piW θ V W))
    have hc : Continuous J := (h.continuous_iota V W).comp
      (j.continuous_of_finiteDimensional.comp (continuous_pi' hθ V W))
    have hr : ∀ x, IsRealW V W x → IsRealW V W (J x) := fun x _ => h.real_iota V W _
    have hj : ∀ x, IsRealW V W x → piW θ V W (J x) = j (piW θ V W x) := fun x _ => h.pi_iota V W _
    refine ⟨J, isFockCx_of_sign h hV hW hA hB hc hr (Or.inl rfl)
      (fun x hx τ => by rw [one_smul]; exact congrFun (hj x hx) τ), ?_⟩
    have hle : polFun ψ θ V W s s' ≤ (nilSub fun u => Dop u + Complex.I • Dop (j u)).map M.subtype := by
      refine Submodule.span_le.2 fun g hg => ?_
      induction hg with
      | vac g hg =>
        refine ⟨⟨g, (hM g).2 hg.1⟩, ⟨1, fun l hl => ?_⟩, rfl⟩
        obtain ⟨u, rfl⟩ := List.length_eq_one_iff.1 hl
        obtain ⟨L, L', hp, rfl⟩ := hpair u
        exact Subtype.ext ((hann L L' hp ⟨g, (hM g).2 hg.1⟩).symm.trans (hg.2 L L' hp))
      | cre L L' g hp _ ih =>
        obtain ⟨m, ⟨N, hN⟩, rfl⟩ := ih
        exact ⟨_, ⟨N + 1, GlobalTheory.T.isKilledByOperatorProducts_succ_creation_apply _ M _ _ (fun u => hβ u (piW θ V W (L 1))) N m hN⟩, (hcre L L' hp m).symm⟩
    obtain ⟨m, ⟨N, hN⟩, rfl⟩ := hle hp
    exact ⟨N, (h.killed_iff hψ hD1 hc hr j hj N m).2 hN⟩

end Fock

variable {X : ThetaX D} {T : ThetaTied D X}

theorem sig_add {V : HSp D} (hV : V.SigOK) (τ : D.what₂.Tau) :
    (V.sig (tauE D τ)).1 + (V.sig (tauE D τ)).2 = V.rank := by
  have := (Formalism.UG.P.sig_data _ _ _ (hV (tauE D τ))).1
  rw [Fintype.card_fin] at this
  exact this.symm

theorem rel_of_monomial {V : HSp D} (hV : V.SigOK) (τ : D.what₂.Tau) (b : Module.Basis (Fin V.rank) D.host.E V.V)
    (hb : ∀ i j, i ≠ j → V.hT (b i) (b j) = 0) {s : Module.End D.host.E V.V}
    (hs : ∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i)
    {A : Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ}
    (hA : Aᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * A = gramAt D V τ)
    (hm : ∀ a i j, (A * (V.frame.toMatrix b).map (tauE D τ)) a i ≠ 0 →
      (A * (V.frame.toMatrix b).map (tauE D τ)) a j ≠ 0 → i = j) : Rel V τ A s := by
  obtain ⟨hu, -, h3⟩ := (GlobalTheory.T.frame_basis_matrix_orthogonal_properties D V).2 b
  obtain ⟨hd, hdiag, hth⟩ := h3 hb τ
  set Q := (V.frame.toMatrix b).map (tauE D τ) with hQ
  have hQu : IsUnit Q.det := by
    rw [hQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hu.map _
  have h1 := GlobalTheory.T.Jpq_mul_monomial_eq_mul_sign_diagonal _ _ _ (sig_add hV τ) (A * Q) _ hd (by
    rw [← hdiag, ← hA, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]) hm
  refine ⟨hA, ?_⟩
  rw [Matrix.mul_assoc, ← hth s hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc] at h1
  have h2 := congrArg (· * Q⁻¹) h1
  simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hQu] using h2

end GlobalTheory.FockCompare

end
