module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem rootSum_isAdditive_and_pow_X_sub_one :
    ∀ (F : Type) [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ),
      IsAdditive (rootSum θ k) ∧ ∀ j : ℕ, rootSum θ k ((X - C 1 : F[X]) ^ j) = j := by
  intro F _ θ k
  refine ⟨fun P Q hP hQ => ?_, fun j => ?_⟩
  · unfold rootSum
    rw [Polynomial.map_mul, Polynomial.roots_mul ((hP.map _).mul (hQ.map _)).ne_zero,
      Multiset.map_add, Multiset.sum_add]
  · unfold rootSum
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.map_nsmul, Multiset.sum_nsmul]
    simp

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow : ∀ (F : Type) [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ), IsAdditive (rootSum θ k) ∧ ∀ j : ℕ, rootSum θ k ((X - C 1 : F[X]) ^ j) = j := by
  first | exact @GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one | exact GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one | (intros; apply GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj {F : Type} [Field F]
    (s : F[X] → ℂ) (n : ℕ) :
    ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V']
      [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V),
      _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V' (e.conj g) =
        _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V g := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro V V' _ _ _ _ _ _ e g
    rw [_root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ,
      e.charpoly_conj]
    congr 1
    let σ : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} ≃
        {W : Submodule F V' // W ≠ ⊤ ∧ ∀ x ∈ W, e.conj g x ∈ W} :=
      (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv fun W => by
        change _ ↔ (Submodule.orderIsoMapComap e W ≠ ⊤ ∧
          ∀ y ∈ W.map (e : V →ₗ[F] V'), e.conj g y ∈ W.map (e : V →ₗ[F] V'))
        refine and_congr ?_ ⟨fun h y hy => ?_, fun h x hx => ?_⟩
        · exact ((Submodule.orderIsoMapComap e).injective.ne_iff' (map_top _)).symm
        · obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
          simpa [LinearEquiv.conj_apply] using
            Submodule.mem_map_of_mem (f := (e : V →ₗ[F] V')) (h x hx)
        · have := h (e x) (Submodule.mem_map_of_mem hx)
          simpa [LinearEquiv.conj_apply, Submodule.mem_map_equiv] using this
    rw [← finsum_comp_equiv σ]
    refine finsum_congr fun W => ?_
    rw [← ih W.1 (W.1.map (e : V →ₗ[F] V')) (e.submoduleMap W.1)]
    show _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n (W.1.map (e : V →ₗ[F] V')) _ = _
    congr 1

theorem _root_.GlobalTheory.CuspGL.psi_conj (F : Type) [Field F]
    (s : F[X] → ℂ) (V V' : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
    (e : V ≃ₗ[F] V') (g : Module.End F V) :
    _root_.GlobalTheory.CuspGL.psi s V' (e.conj g) =
      _root_.GlobalTheory.CuspGL.psi s V g := by
  unfold _root_.GlobalTheory.CuspGL.psi
  rw [← e.finrank_eq]
  exact _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj s _ V V' e g

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj : ∀ (F : Type) [Field F] (s : F[X] → ℂ) (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), psi s V' (e.conj g) = psi s V g := by
  first | exact @GlobalTheory.CuspGL.psi_conj | exact GlobalTheory.CuspGL.psi_conj | (intros; apply GlobalTheory.CuspGL.psi_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic
open Polynomial GlobalTheory.CuspGL Module.Basis

namespace GlobalTheory.CuspGL

open Module Module.Basis in
theorem charpoly_eq_restrict_mul_mapQ {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A) :
    LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) *
      LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) := by
  classical
  let bA := Module.finBasis F A
  let bQ := Module.finBasis F (V ⧸ A)
  let b := sumQuot bA bQ
  have hmat : LinearMap.toMatrix b b g = Matrix.fromBlocks (LinearMap.toMatrix bA bA (g.restrict hg))
      (Matrix.of fun i j => b.repr (g (b (Sum.inr j))) (Sum.inl i)) 0
      (LinearMap.toMatrix bQ bQ (A.mapQ A g (fun x hx => hg x hx))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₁, b, sumQuot_inl]
      rw [sumQuot_repr_inl_of_mem bA bQ _ (hg _ (bA j).2)]
      rfl
    · simp [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, b]
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₁, b, sumQuot_inl,
        Matrix.zero_apply]
      exact sumQuot_repr_inr_of_mem bA bQ _ (hg _ (bA j).2) i
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₂, b]
      rw [sumQuot_repr_inr, ← sumQuot_inr bA bQ j, Submodule.mapQ_apply]
      rfl
  rw [← LinearMap.charpoly_toMatrix g b, hmat, Matrix.charpoly_fromBlocks_zero₂₁,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

theorem charpoly_block : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A),
    LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) *
      LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) ∧
    ∀ h ∈ nilRad A, LinearMap.charpoly (g + h) = LinearMap.charpoly g := by
  intro F _ V _ _ _ A g hg
  refine ⟨charpoly_eq_restrict_mul_mapQ A g hg, ?_⟩
  rintro h ⟨himg, hker⟩
  have hgh : ∀ x ∈ A, (g + h) x ∈ A := fun x hx => by
    simpa [LinearMap.add_apply, hker x hx] using hg x hx
  have hres : (g + h).restrict hgh = g.restrict hg := by
    ext x
    simp [LinearMap.restrict_apply, hker x x.2]
  have hquot : A.mapQ A (g + h) (fun x hx => hgh x hx) = A.mapQ A g (fun x hx => hg x hx) := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simpa [LinearMap.add_apply] using himg x
  rw [charpoly_eq_restrict_mul_mapQ A (g + h) hgh, charpoly_eq_restrict_mul_mapQ A g hg, hres, hquot]

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) * LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) ∧ ∀ h ∈ nilRad A, LinearMap.charpoly (g + h) = LinearMap.charpoly g := by
  first | exact @GlobalTheory.CuspGL.charpoly_block | exact GlobalTheory.CuspGL.charpoly_block | (intros; apply GlobalTheory.CuspGL.charpoly_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

section
variable {K G V W : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def transportRep (ρ : Representation K G V) (e : V ≃ₗ[K] W) : Representation K G W where
  toFun g := e.conj (ρ g)
  map_one' := by ext w; simp
  map_mul' a b := by ext w; simp

theorem transportRep_apply (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) (w : W) :
    transportRep ρ e g w = e (ρ g (e.symm w)) := rfl

theorem character_transportRep [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) :
    (transportRep ρ e).character g = ρ.character g :=
  LinearMap.trace_conj' (ρ g) e

def transportSubOrderIso (ρ : Representation K G V) (e : V ≃ₗ[K] W) :
    Subrepresentation (transportRep ρ e) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule.comap e.toLinearMap, fun g v hv => by
    have := S.apply_mem_toSubmodule g (v := e v) hv
    simpa [transportRep_apply] using this⟩
  invFun S := ⟨S.toSubmodule.comap e.symm.toLinearMap, fun g w hw => by
    have := S.apply_mem_toSubmodule g (v := e.symm w) hw
    simpa [transportRep_apply] using this⟩
  left_inv S := by ext w; simp
  right_inv S := by ext v; simp
  map_rel_iff' {S T} := by
    constructor
    · intro h w hw
      have h1 : e.symm w ∈ S.toSubmodule.comap e.toLinearMap := by
        show e (e.symm w) ∈ S.toSubmodule
        rw [e.apply_symm_apply]; exact hw
      have h2 : e (e.symm w) ∈ T.toSubmodule := h h1
      rw [e.apply_symm_apply] at h2
      exact h2
    · intro h v hv
      exact h (show e v ∈ S from hv)

end

theorem _root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type)
      [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V),
      _root_.GlobalTheory.BI.IsChar K L (fun g => algebraMap K L (ρ.character g)) ∧
        (ρ.IsIrreducible →
          _root_.GlobalTheory.BI.IsIrrChar K L (fun g => algebraMap K L (ρ.character g))) := by
  intro K L _ _ _ G _ V _ _ _ ρ
  set e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) := (Module.finBasis K V).equivFun
  have hchar : ∀ g, (_root_.GlobalTheory.BI.transportRep ρ e).character g = ρ.character g := by
    intro g
    exact LinearMap.trace_conj' (ρ g) e
  refine ⟨⟨Module.finrank K V, _root_.GlobalTheory.BI.transportRep ρ e, fun g => ?_⟩, fun hρ => ?_⟩
  · rw [hchar]
  · refine ⟨Module.finrank K V, _root_.GlobalTheory.BI.transportRep ρ e, ?_, fun g => ?_⟩
    · have hs : IsSimpleOrder (Subrepresentation ρ) := hρ
      exact (_root_.GlobalTheory.BI.transportSubOrderIso ρ e).isSimpleOrder_iff.mpr hs
    · rw [hchar]

end GlobalTheory.BI
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentationStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_of_representation : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V), IsChar K L (fun g => algebraMap K L (ρ.character g)) ∧ (ρ.IsIrreducible → IsIrrChar K L (fun g => algebraMap K L (ρ.character g))) := by
  first | exact @GlobalTheory.BI.isChar_and_isIrrChar_of_rep | exact GlobalTheory.BI.isChar_and_isIrrChar_of_rep | (intros; apply GlobalTheory.BI.isChar_and_isIrrChar_of_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CharpolyPow

variable {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}

lemma card_roots_charpoly (M : Matrix (Fin n) (Fin n) k) : Multiset.card M.charpoly.roots = n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

lemma det_scalar_sub (M : Matrix (Fin n) (Fin n) k) (t : k) :
    (Matrix.scalar (Fin n) t - M).det = (M.charpoly.roots.map (fun z => t - z)).prod := by
  have hroots : Multiset.card M.charpoly.roots = M.charpoly.natDegree := by
    rw [card_roots_charpoly, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [← Matrix.eval_charpoly,
    ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic M) hroots,
    eval_multiset_prod, Multiset.map_map]
  simp

lemma det_aeval_prod (M : Matrix (Fin n) (Fin n) k) (s : Multiset k) :
    (aeval M (s.map (fun a => C a - X)).prod).det
      = (M.charpoly.roots.map (fun z => eval z (s.map (fun a => C a - X)).prod)).prod := by
  have key : ∀ a : k, (aeval M (C a - X)).det = (M.charpoly.roots.map (fun z => a - z)).prod := by
    intro a
    rw [← det_scalar_sub]
    congr 1
    simp [Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Matrix.det_mul, key, ih,
      ← Multiset.prod_map_mul]
    congr 1
    apply Multiset.map_congr rfl
    intro z _
    simp

lemma det_aeval (M : Matrix (Fin n) (Fin n) k) (q : k[X]) :
    (aeval M q).det = (M.charpoly.roots.map (fun z => eval z q)).prod := by
  set m := Multiset.card q.roots
  set c := q.leadingCoeff * (-1) ^ m
  have hq : q = C c * (q.roots.map (fun a => C a - X)).prod := by
    have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := q) IsAlgClosed.card_roots_eq_natDegree
    have hneg : (q.roots.map (fun a => C a - X)).prod
        = (-1) ^ m * (q.roots.map (fun a => X - C a)).prod := by
      have : (fun a : k => C a - X) = fun a => (-1) * (X - C a) := by
        funext a; ring
      rw [this, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
    rw [hneg, C_mul, C_pow, C_neg, C_1]
    calc q = C q.leadingCoeff * (q.roots.map (fun a => X - C a)).prod := hsplit.symm
      _ = C q.leadingCoeff * (-1) ^ m * ((-1) ^ m * (q.roots.map (fun a => X - C a)).prod) := by
        rw [← mul_assoc, mul_assoc (C q.leadingCoeff), ← pow_add, ← two_mul, pow_mul]
        simp
  have hcard : Multiset.card M.charpoly.roots = n := card_roots_charpoly M
  conv_lhs => rw [hq]
  conv_rhs => rw [hq]
  rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.det_smul,
    Fintype.card_fin, det_aeval_prod]
  simp only [eval_mul, eval_C]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]

theorem roots_charpoly_pow (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ)
    (M : Matrix (Fin n) (Fin n) k) :
    (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly M).roots.map (· ^ r) := by
  have hinf : Infinite k := IsAlgClosed.instInfinite
  have hcard : Multiset.card (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly (M ^ r)).natDegree := by
    exact IsAlgClosed.card_roots_eq_natDegree
  have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic (M ^ r)) hcard
  suffices h : Matrix.charpoly (M ^ r) = (((Matrix.charpoly M).roots.map (· ^ r)).map fun a => X - C a).prod by
    rw [h, roots_multiset_prod_X_sub_C]
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  have h1 : Matrix.scalar (Fin n) t - M ^ r = aeval M (C t - X ^ r) := by
    simp [Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]
  rw [h1, GlobalTheory.CharpolyPow.det_aeval]
  simp [Function.comp_def]

end GlobalTheory.CharpolyPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPowStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_charpoly_pow_eq_map_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (M : Matrix (Fin n) (Fin n) k), (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly M).roots.map (· ^ r) := by
  first | exact @GlobalTheory.CharpolyPow.roots_charpoly_pow | exact GlobalTheory.CharpolyPow.roots_charpoly_pow | (intros; apply GlobalTheory.CharpolyPow.roots_charpoly_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
open GlobalTheory.BI
namespace GlobalTheory

theorem isChar_restrict_conj_one : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (χ : G → L), IsChar K L χ → (∀ (H : Type) [Group H] (f : H →* G), IsChar K L (fun h => χ (f h))) ∧ (∀ g x : G, χ (x⁻¹ * g * x) = χ g) ∧ ∃ n : ℕ, χ 1 = (n : L) ∧ (n = 0 → χ = 0) := by
  intro K L _ _ _ G _ χ hχ
  obtain ⟨n, ρ, hρ⟩ := hχ
  refine ⟨?_, ?_, n, ?_, ?_⟩
  · intro H _ f
    exact ⟨n, ρ.comp f, fun h => hρ (f h)⟩
  · intro g x
    rw [hρ, hρ]
    have hc := ρ.char_conj g x⁻¹
    rw [inv_inv] at hc
    rw [hc]
  · rw [hρ, Representation.char_one]
    simp
  · rintro rfl
    funext g
    have hz : ρ g = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hρ, Pi.zero_apply, Representation.character, hz, map_zero, map_zero]
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOneStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_restrict_classFunction_one : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (χ : G → L), IsChar K L χ → (∀ (H : Type) [Group H] (f : H →* G), IsChar K L (fun h => χ (f h))) ∧ (∀ g x : G, χ (x⁻¹ * g * x) = χ g) ∧ ∃ n : ℕ, χ 1 = (n : L) ∧ (n = 0 → χ = 0) := by
  first | exact @GlobalTheory.isChar_restrict_conj_one | exact GlobalTheory.isChar_restrict_conj_one | (intros; apply GlobalTheory.isChar_restrict_conj_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.GeneralLinearFunctionExtendZeroEndProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.GeneralLinearFunctionExtendZeroEndProperties
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] {d : ℕ}

theorem extZero_toLin_injective :
    Function.Injective fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := fun _ _ h => Units.ext (Matrix.toLin'.injective h)

theorem extZero_isUnit_iff (g : Module.End F (Fin d → F)) :
    IsUnit g ↔ ∃ x : GL (Fin d) F, Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := LinearMap.isUnit_toMatrix'_iff.mpr h
    exact ⟨u, by rw [hu, Matrix.toLin'_toMatrix']⟩
  · rintro ⟨x, rfl⟩
    exact Matrix.isUnit_toLin'_iff.mpr x.isUnit

theorem extZero_toLin (χ : GL (Fin d) F → ℂ) (x : GL (Fin d) F) :
    extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x := by
  unfold extZero
  have hs : {y : GL (Fin d) F | Matrix.toLin' (y : Matrix (Fin d) (Fin d) F) =
      Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)} = {x} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact extZero_toLin_injective.eq_iff
  rw [hs, finsum_mem_singleton]

theorem extZero_of_not_isUnit (χ : GL (Fin d) F → ℂ) (g : Module.End F (Fin d → F))
    (hg : ¬ IsUnit g) : extZero χ g = 0 := by
  unfold extZero
  have hs : {x : GL (Fin d) F | Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact hg ((extZero_isUnit_iff _).mpr ⟨x, rfl⟩)
  rw [hs, finsum_mem_empty]

theorem ipGL_eq_finsum_GL (φ φ' : Module.End F (Fin d → F) → ℂ) :
    ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) *
      star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) := by
  unfold ipGL
  have hs : {g : Module.End F (Fin d → F) | IsUnit g} =
      Set.range fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by
    ext g
    exact extZero_isUnit_iff g
  rw [hs, finsum_mem_range extZero_toLin_injective]

theorem isClassFn_extZero (χ : GL (Fin d) F → ℂ)
    (hχ : ∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) : IsClassFn (extZero χ) := by
  intro e g

  let Φ : GL (Fin d) F ≃* (Module.End F (Fin d → F))ˣ :=
    Units.mapEquiv (Matrix.toLinAlgEquiv' (R := F) (n := Fin d)).toMulEquiv
  have hcoe : ∀ x : GL (Fin d) F, ((Φ x : (Module.End F (Fin d → F))ˣ) : Module.End F (Fin d → F)) =
      Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by
    intro x
    refine LinearMap.ext fun v => ?_
    change Matrix.toLinAlgEquiv' (x : Matrix (Fin d) (Fin d) F) v = _
    rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

  let E : (Module.End F (Fin d → F))ˣ :=
    ⟨e.toLinearMap, e.symm.toLinearMap, LinearMap.ext fun v => e.apply_symm_apply v,
      LinearMap.ext fun v => e.symm_apply_apply v⟩
  have hconj : ∀ f : Module.End F (Fin d → F),
      e.conj f = (E : Module.End F (Fin d → F)) * f * ((E⁻¹ : (Module.End F (Fin d → F))ˣ) :
        Module.End F (Fin d → F)) := by
    intro f
    exact LinearMap.ext fun v => rfl
  by_cases hg : IsUnit g
  · obtain ⟨y, rfl⟩ := (extZero_isUnit_iff g).mp hg
    have hy : e.conj (Matrix.toLin' (y : Matrix (Fin d) (Fin d) F)) =
        Matrix.toLin' ((Φ.symm E * y * (Φ.symm E)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
      rw [← hcoe (Φ.symm E * y * (Φ.symm E)⁻¹), map_mul, map_mul, map_inv, Φ.apply_symm_apply, Units.val_mul, Units.val_mul,
        hcoe y, hconj]
    rw [hy, extZero_toLin, extZero_toLin]
    simpa using hχ y (Φ.symm E)⁻¹
  · have hg' : ¬ IsUnit (e.conj g) := by
      rw [hconj, Units.isUnit_mul_units, Units.isUnit_units_mul]
      exact hg
    rw [extZero_of_not_isUnit χ _ hg', extZero_of_not_isUnit χ _ hg]

theorem extZero_spec : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), (∀ x : GL (Fin d) F, extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x) ∧ (∀ g, ¬ IsUnit g → extZero χ g = 0) ∧ (∀ φ φ' : Module.End F (Fin d → F) → ℂ, ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) * star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)))) ∧ ((∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) → IsClassFn (extZero χ)) := by
  intro F _ _ d χ
  exact ⟨fun x => extZero_toLin χ x, fun g hg => extZero_of_not_isUnit χ g hg,
    fun φ φ' => ipGL_eq_finsum_GL φ φ', fun h => isClassFn_extZero χ h⟩

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.GeneralLinearFunctionExtendZeroEndPropertiesStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), (∀ x : GL (Fin d) F, extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x) ∧ (∀ g, ¬ IsUnit g → extZero χ g = 0) ∧ (∀ φ φ' : Module.End F (Fin d → F) → ℂ, ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) * star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)))) ∧ ((∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) → IsClassFn (extZero χ)) := by
  first | exact @GlobalTheory.CuspGL.extZero_spec | exact GlobalTheory.CuspGL.extZero_spec | (intros; apply GlobalTheory.CuspGL.extZero_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimary
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsConjEqAddOfIsCoprime
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem intertwine_aeval_apply {F : Type} [Field F] {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] (f : V →ₗ[F] W) (a : Module.End F V) (b : Module.End F W) (h : ∀ x, f (a x) = b (f x))
    (p : F[X]) (x : V) : f (aeval a p x) = aeval b p (f x) := by
  have hpow : ∀ (n : ℕ) (x : V), f ((a ^ n) x) = (b ^ n) (f x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp [aeval_monomial, hpow]

theorem nilRad_eq_zero_of_commute {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A)
    (hc : IsCoprime (LinearMap.charpoly (g.restrict hg))
      (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))))
    (u : Module.End F V) (hu : u ∈ nilRad A) (hug : ∀ x, u (g x) = g (u x)) : u = 0 := by
  obtain ⟨a, b, hab⟩ := hc
  set p₁ := LinearMap.charpoly (g.restrict hg) with hp₁
  set p₂ := LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) with hp₂
  have h1 : ∀ y ∈ A, aeval g p₁ y = 0 := by
    intro y hy
    have := intertwine_aeval_apply A.subtype (g.restrict hg) g (fun x => rfl) p₁ ⟨y, hy⟩
    rw [hp₁, LinearMap.aeval_self_charpoly] at this
    simpa using this.symm
  have h2 : ∀ y, aeval g p₂ y ∈ A := by
    intro y
    have := intertwine_aeval_apply A.mkQ g (A.mapQ A g (fun x hx => hg x hx)) (fun x => rfl) p₂ y
    rw [hp₂, LinearMap.aeval_self_charpoly] at this
    simpa using this
  ext x
  have hx : x = aeval g p₁ (aeval g a x) + aeval g p₂ (aeval g b x) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← LinearMap.add_apply, ← map_add (f := _),
      mul_comm p₁, mul_comm p₂, hab]
    simp
  rw [hx, map_add (f := _), hu.2 _ (h2 _), intertwine_aeval_apply u g g hug, h1 _ (hu.1 _)]
  simp

theorem exists_conj_eq_add_of_isCoprime : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A),
    IsCoprime (LinearMap.charpoly (g.restrict hg)) (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) →
    ∀ h ∈ nilRad A, ∃ e : V ≃ₗ[F] V, e.conj g = g + h := by
  intro F _ _ V _ _ _ A g hg hc h hh
  let N : Submodule F (Module.End F V) :=
    { carrier := nilRad A
      add_mem' := fun {a b} ha hb => ⟨fun x => A.add_mem (ha.1 x) (hb.1 x), fun x hx => by
        simp [ha.2 x hx, hb.2 x hx]⟩
      zero_mem' := ⟨fun x => A.zero_mem, fun x _ => rfl⟩
      smul_mem' := fun c a ha => ⟨fun x => A.smul_mem c (ha.1 x), fun x hx => by simp [ha.2 x hx]⟩ }
  let D : Module.End F V →ₗ[F] Module.End F V := LinearMap.mulRight F g - LinearMap.mulLeft F g
  have hD : ∀ u x, D u x = u (g x) - g (u x) := fun u x => rfl
  have hDN : ∀ u ∈ N, D u ∈ N := by
    intro u hu
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [hD]; exact A.sub_mem (hu.1 _) (hg _ (hu.1 _))
    · rw [hD, hu.2 _ hx, hu.2 _ (hg _ hx)]; simp
  have hinj : Function.Injective (D.restrict hDN) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    apply Subtype.ext
    refine nilRad_eq_zero_of_commute A g hg hc u.1 u.2 fun x => ?_
    have h0 : D u.1 = 0 := congrArg Subtype.val hu
    have := hD u.1 x
    rw [h0] at this
    exact sub_eq_zero.1 this.symm
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hinj ⟨h, hh⟩
  have hu' : D u.1 = h := congrArg Subtype.val hu
  obtain ⟨u, huA, hu0⟩ := u
  have huu : ∀ x, u (u x) = 0 := fun x => hu0 _ (huA x)
  refine ⟨LinearEquiv.ofLinearMap (1 + u) (1 - u) ?_ ?_, ?_⟩
  · ext x; simp [huu]
  · ext x; simp [huu]
  · ext x
    have h3 : u (g (u x)) = 0 := hu0 _ (hg _ (huA x))
    have h4 : h x = u (g x) - g (u x) := by rw [← hu']; rfl
    simp [LinearEquiv.conj_apply, h3, h4]
    abel

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimary
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (T : Module.End F V) (p q : F[X]) (hp : Irreducible p)
    (hd : p ∣ LinearMap.charpoly T) (hq : aeval T q = 0) : p ∣ q := by
  have : Fact (Irreducible p) := ⟨hp⟩
  have hroot : (LinearMap.charpoly (T.baseChange (AdjoinRoot p))).IsRoot (AdjoinRoot.root p) := by
    rw [LinearMap.charpoly_baseChange]
    obtain ⟨r, hr⟩ := hd
    rw [hr, Polynomial.map_mul, IsRoot, eval_mul, AdjoinRoot.algebraMap_eq,
      (AdjoinRoot.isRoot_root p).eq_zero, zero_mul]
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot).exists_hasEigenvector
  have h0 : aeval (T.baseChange (AdjoinRoot p)) (q.map (algebraMap F (AdjoinRoot p))) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    change aeval (Module.End.baseChangeHom F (AdjoinRoot p) V T) q = 0
    rw [Polynomial.aeval_algHom_apply, hq, map_zero]
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map (algebraMap F (AdjoinRoot p))) hv
  rw [h0, LinearMap.zero_apply] at h1
  have hz : (q.map (algebraMap F (AdjoinRoot p))).eval (AdjoinRoot.root p) = 0 := by
    rcases smul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hv.2
  rw [Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at hz
  exact hz

theorem eq_zero_of_not_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V →
    ∀ g : Module.End F V, (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧
      LinearMap.charpoly g = f ^ m) → φ g = 0 := by
  intro F _ _ V _ _ _ φ hcl hpr hdim g hg
  have hmon : (LinearMap.charpoly g).Monic := LinearMap.charpoly_monic g
  have hne0 : LinearMap.charpoly g ≠ 0 := hmon.ne_zero
  have hnu : ¬ IsUnit (LinearMap.charpoly g) := by
    intro hu
    have h := LinearMap.charpoly_natDegree g
    rw [Polynomial.natDegree_eq_zero_of_isUnit hu] at h
    omega
  obtain ⟨f, hfm, hf, hfd⟩ := Polynomial.exists_monic_irreducible_factor _ hnu
  obtain ⟨m, Q, hnd, hfac⟩ := WfDvdMonoid.max_power_factor hne0 hf
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero, one_mul] at hfac
      exact absurd (hfac ▸ hfd) hnd
    · exact h
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hfac
    exact hne0 hfac
  have hQ : ¬ IsUnit Q := by
    intro hu
    have hQm : Q.Monic := (hfm.pow m).of_mul_monic_left (hfac ▸ hmon)
    have h1 : Q = 1 := hQm.eq_one_of_isUnit hu
    exact hg ⟨f, m, hfm, hf, hm, by rw [hfac, h1, mul_one]⟩
  have hcop : IsCoprime (f ^ m) Q := ((hf.coprime_iff_not_dvd).mpr hnd).pow_left
  have hPQ : aeval g (f ^ m) * aeval g Q = 0 := by
    rw [← map_mul, ← hfac, LinearMap.aeval_self_charpoly]
  have hgA : ∀ x ∈ LinearMap.ker (aeval g (f ^ m)), g x ∈ LinearMap.ker (aeval g (f ^ m)) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hc : aeval g (f ^ m) * g = g * aeval g (f ^ m) := by
      calc aeval g (f ^ m) * g = aeval g (f ^ m * X) := by rw [map_mul, aeval_X]
        _ = aeval g (X * f ^ m) := by rw [mul_comm]
        _ = g * aeval g (f ^ m) := by rw [map_mul, aeval_X]
    have h := congrArg (fun u : Module.End F V => u x) hc
    simp only [Module.End.mul_apply] at h
    rw [h, hx, map_zero]
  set A := LinearMap.ker (aeval g (f ^ m)) with hAdef
  have hPA : aeval (g.restrict hgA) (f ^ m) = 0 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have h := intertwine_aeval_apply A.subtype (g.restrict hgA) g (fun _ => rfl) (f ^ m) x
    rw [Submodule.subtype_apply, Submodule.subtype_apply] at h
    rw [h, LinearMap.zero_apply, Submodule.coe_zero]
    exact LinearMap.mem_ker.mp x.2
  have hQq : aeval (A.mapQ A g (fun x hx => hgA x hx)) Q = 0 := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := A.mkQ_surjective y
    have h := intertwine_aeval_apply A.mkQ g (A.mapQ A g (fun x hx => hgA x hx)) (fun _ => rfl) Q x
    rw [← h, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      hAdef, LinearMap.mem_ker, ← Module.End.mul_apply, hPQ, LinearMap.zero_apply]
  have hcp : IsCoprime (LinearMap.charpoly (g.restrict hgA))
      (LinearMap.charpoly (A.mapQ A g (fun x hx => hgA x hx))) := by
    refine isCoprime_of_irreducible_dvd (fun h => (LinearMap.charpoly_monic _).ne_zero h.1) ?_
    intro z hz hzA hzQ
    have h1 : z ∣ f ^ m :=
      irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero (g.restrict hgA) z (f ^ m) hz hzA hPA
    have h2 : z ∣ Q := irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ z Q hz hzQ hQq
    exact hz.not_isUnit (hcop.isUnit_of_dvd' h1 h2)
  have hAbot : A ≠ ⊥ := by
    intro hA
    have hsup := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime g hcop
    rw [← hAdef, hA, bot_sup_eq, ← hfac, LinearMap.aeval_self_charpoly, LinearMap.ker_zero] at hsup
    have hQ0' : aeval g Q = 0 := LinearMap.ker_eq_top.mp hsup
    exact hnd (irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero g f Q hf hfd hQ0')
  have hAtop : A ≠ ⊤ := by
    intro hA
    have hP0 : aeval g (f ^ m) = 0 := LinearMap.ker_eq_top.mp hA
    obtain ⟨z, hz, hzQ⟩ := WfDvdMonoid.exists_irreducible_factor hQ hQ0
    have hzc : z ∣ LinearMap.charpoly g := hzQ.trans ⟨f ^ m, by rw [hfac, mul_comm]⟩
    have h1 : z ∣ f ^ m := irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero g z (f ^ m) hz hzc hP0
    exact hz.not_isUnit (hcop.isUnit_of_dvd' h1 hzQ)
  have hconj := exists_conj_eq_add_of_isCoprime F V A g hgA hcp
  have hsum := hpr A hAbot hAtop g hgA
  have hconst : ∀ h ∈ nilRad A, φ (g + h) = φ g := by
    intro h hh
    obtain ⟨e, he⟩ := hconj h hh
    rw [← he, hcl]
  rw [finsum_mem_congr rfl hconst] at hsum
  have : Finite V := Module.finite_of_finite F
  have : Finite (Module.End F V) :=
    Finite.of_injective (fun u : Module.End F V => (u : V → V)) DFunLike.coe_injective
  have hfin : (nilRad A).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul] at hsum
  have h0 : (0 : Module.End F V) ∈ nilRad A := ⟨fun _ => A.zero_mem, fun _ _ => rfl⟩
  have hcard : (hfin.toFinset.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨0, hfin.mem_toFinset.mpr h0⟩)
  exact (mul_eq_zero.mp hsum).resolve_left hcard

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimaryStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ g : Module.End F V, (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ LinearMap.charpoly g = f ^ m) → φ g = 0 := by
  first | exact @GlobalTheory.CuspGL.eq_zero_of_not_primary | exact GlobalTheory.CuspGL.eq_zero_of_not_primary | (intros; apply GlobalTheory.CuspGL.eq_zero_of_not_primary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduci
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduci
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem psi_of_finrank_eq_zero {F : Type} [Field F] (s : F[X] → ℂ) (hs : IsAdditive s)
    (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V)
    (h : Module.finrank F V = 0) : psi s V g = 0 := by
  have hsub : Subsingleton V := Module.finrank_zero_iff.mp h
  have h1 : LinearMap.charpoly g = 1 := by
    apply (LinearMap.charpoly_monic g).natDegree_eq_zero.mp
    rw [LinearMap.charpoly_natDegree, h]
  have h0 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    rw [one_mul] at this
    linear_combination -this
  have : IsEmpty {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} :=
    ⟨fun W => W.2.1 (Subsingleton.elim _ _)⟩
  rw [psi_eq, h1, h0, finsum_of_isEmpty, sub_zero]

theorem coe_aeval_restrict_apply {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : F[X]) (x : W) :
    ((aeval (g.restrict hW : Module.End F W) p x : W) : V) = aeval g p x := by
  induction p using Polynomial.induction_on generalizing x with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval g), aeval_X, aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

theorem finrank_eq_zero_of_irreducible_charpoly {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V) (hg : Irreducible (LinearMap.charpoly g))
    (W : Submodule F V) (hne : W ≠ ⊤) (hW : ∀ x ∈ W, g x ∈ W) : Module.finrank F W = 0 := by
  by_contra h0
  have hnt : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (Nat.pos_of_ne_zero h0)
  set f : Module.End F W := g.restrict hW with hf
  have hz : aeval f (LinearMap.charpoly g) = 0 := by
    ext x
    rw [hf, coe_aeval_restrict_apply, LinearMap.aeval_self_charpoly]
    simp
  have hd : minpoly F f ∣ LinearMap.charpoly g := minpoly.dvd F f hz
  have hnu : ¬ IsUnit (minpoly F f) := minpoly.not_isUnit F f
  have hd' : LinearMap.charpoly g ∣ minpoly F f := ((hg.dvd_iff.mp hd).resolve_left hnu).dvd
  have hd'' : LinearMap.charpoly g ∣ LinearMap.charpoly f := hd'.trans (LinearMap.minpoly_dvd_charpoly f)
  have hle := natDegree_le_of_dvd hd'' (LinearMap.charpoly_monic f).ne_zero
  rw [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree] at hle
  have := Submodule.finrank_lt hne
  omega

theorem psi_of_irreducible_charpoly : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ g : Module.End F V, Irreducible (LinearMap.charpoly g) → psi s V g = s (LinearMap.charpoly g) := by
  intro F _ _ V _ _ _ s hs g hg
  rw [psi_eq, finsum_eq_zero_of_forall_eq_zero, sub_zero]
  intro W
  exact psi_of_finrank_eq_zero s hs _ _ (finrank_eq_zero_of_irreducible_charpoly g hg W.1 W.2.1 W.2.2)

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ g : Module.End F V, Irreducible (LinearMap.charpoly g) → psi s V g = s (LinearMap.charpoly g) := by
  first | exact @GlobalTheory.CuspGL.psi_of_irreducible_charpoly | exact GlobalTheory.CuspGL.psi_of_irreducible_charpoly | (intros; apply GlobalTheory.CuspGL.psi_of_irreducible_charpoly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem pair_self_of_isIrrChar_algClosed (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G]
    (χ : G → L) (h : IsIrrChar L L χ) : pair χ χ = 1 := by
  classical
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : ρ.IsIrreducible := hρ

  have key := ρ.card_inv_mul_sum_char_mul_char_eq_finrank ρ
  rw [Representation.IsIrreducible.finrank_intertwiningMap_self] at key
  unfold pair
  rw [finsum_eq_sum_of_fintype]
  simp only [hχ, Algebra.algebraMap_self, RingHom.id_apply]
  simpa using key
end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), IsIrrChar L L χ → pair χ χ = 1 := by
  first | exact @GlobalTheory.BI.pair_self_of_isIrrChar_algClosed | exact GlobalTheory.BI.pair_self_of_isIrrChar_algClosed | (intros; apply GlobalTheory.BI.pair_self_of_isIrrChar_algClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem pair_eq_zero_of_isIrrChar_ne : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ),
    IsIrrChar ℂ ℂ a → IsIrrChar ℂ ℂ b → a ≠ b → pair a b = 0 := by
  intro G _ _ a b ha hb hab
  obtain ⟨n, ρ, hρ, ha⟩ := ha
  obtain ⟨m, σ, hσ, hb⟩ := hb
  have := hρ
  have := hσ
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have ha' : a = ρ.character := funext fun g => by simp [ha]
  have hb' : b = σ.character := funext fun g => by simp [hb]
  have hne : ¬ Nonempty (Representation.Equiv σ ρ) := by
    rintro ⟨φ⟩
    exact hab (by rw [ha', hb', Representation.char_iso φ])
  have h := Representation.char_orthonormal ρ σ
  rw [if_neg hne] at h
  unfold pair
  rw [finsum_eq_sum_of_fintype, ha', hb']
  simpa using h
end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrreduStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_eq_zero_of_distinct_irreducible : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ), IsIrrChar ℂ ℂ a → IsIrrChar ℂ ℂ b → a ≠ b → pair a b = 0 := by
  first | exact @GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne | (intros; apply GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingCharacterEqFinrankInte
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingCharacterEqFinrankInte
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.pair_character_eq_finrank : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W), _root_.GlobalTheory.BI.pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g)) = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  intro K L _ _ _ _ _ G _ _ V _ _ _ W _ _ _ ρ σ
  classical
  haveI := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h := congrArg (algebraMap K L)
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ)
  unfold _root_.GlobalTheory.BI.pair
  rw [finsum_eq_sum_of_fintype]
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_mul, map_sum, map_inv₀, map_natCast] using h

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingCharacterEqFinrankInteStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_character_eq_finrank_intertwining : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W), pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g)) = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  first | exact @GlobalTheory.BI.pair_character_eq_finrank | exact GlobalTheory.BI.pair_character_eq_finrank | (intros; apply GlobalTheory.BI.pair_character_eq_finrank <;> assumption)
end
end
