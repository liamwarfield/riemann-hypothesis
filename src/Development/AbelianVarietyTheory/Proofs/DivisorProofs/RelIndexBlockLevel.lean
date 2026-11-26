module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralPointSkewLatticeUnitVectorSameEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockEmb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxLevelUnitaryCongrModIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxLevelUnitaryCongrModIdeal
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.MaxLevelLift

theorem exists_intG_cong : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (N : ℕ)
    (g : Matrix (Fin N) (Fin N) (𝓞 D.host.E)), IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det →
      ∃ k : GA D N, k ∈ intG D N ∧ ∀ i j : Fin N,
        ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D ((g i j : 𝓞 D.host.E) : D.host.E) ∈ hatId D 𝔪 := by
  intro D 𝔪 _ hcop N g hg
  have hcc : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z
  have e : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by rw [smul_smul, hcc, one_smul]
  have hdet : (g.map (Ideal.Quotient.mk 𝔪)).det = Ideal.Quotient.mk 𝔪 g.det :=
    ((Ideal.Quotient.mk 𝔪).map_det g).symm
  rw [hdet] at hg
  obtain ⟨v, hv⟩ := hg.exists_right_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq] at hv
  have key : inc D ((g.det * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • D.host.conj • 𝔪) := by
    rw [e]
    exact AddSubgroup.subset_closure ⟨g.det * u - 1, hv, 1, one_mem _, by simp⟩
  obtain ⟨f, hf, w, hw, hff, hfs, hfw, h1f⟩ :=
    GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit GlobalTheory.AlgIntIdem.idem D (D.host.conj • 𝔪)
      (by rw [e, sup_comm]; exact hcop) _ _ key
  rw [e] at h1f
  obtain ⟨k, hk, hkc⟩ := GlobalTheory.GlueUnitary.glue_unitary D 𝔪 N g f w hf hw hff hfs hfw h1f
  refine ⟨k⁻¹, inv_mem hk, fun i j => ?_⟩
  have := neg_mem (hkc i j)
  rwa [Matrix.sub_apply, neg_sub, Matrix.map_apply] at this

end GlobalTheory.MaxLevelLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxLevelUnitaryCongrModIdealStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (N : ℕ)
    (g : Matrix (Fin N) (Fin N) (𝓞 D.host.E)), IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det →
      ∃ k : GA D N, k ∈ intG D N ∧ ∀ i j : Fin N,
        ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D ((g i j : 𝓞 D.host.E) : D.host.E) ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.MaxLevelLift.exists_intG_cong | exact GlobalTheory.MaxLevelLift.exists_intG_cong | (intros; apply GlobalTheory.MaxLevelLift.exists_intG_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionMaxLevelUnitaryModIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionMaxLevelUnitaryModIdeal
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.LevelRed

open GlobalTheory.BotPairSmall.BlockIdx

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))

theorem mk_eq_iff (h𝔪 : 𝔪 ≠ ⊥) (r b : 𝓞 D.host.E) :
    Ideal.Quotient.mk 𝔪 r = Ideal.Quotient.mk 𝔪 b ↔
      inc D (r : D.host.E) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
  have e : inc D (r : D.host.E) - inc D (b : D.host.E) = inc D ((r - b : 𝓞 D.host.E) : D.host.E) := by
    push_cast
    rw [map_sub]
  rw [Ideal.Quotient.eq, e]
  constructor
  · intro h
    simpa using gen_mem_hatId D 𝔪 h (one_mem (OhE D))
  · intro h
    obtain ⟨c, hc, e'⟩ := (FractionalIdeal.mem_coeIdeal _).1 (GlobalTheory.HeisTranslate.mem_of_inc_mem_hatId h𝔪 h)
    have : c = r - b := RingOfIntegers.coe_injective e'
    exact this ▸ hc

theorem exists_redHom (h𝔪 : 𝔪 ≠ ⊥) : ∃ red : OhE D →+* 𝓞 D.host.E ⧸ 𝔪, ∀ (x : OhE D) (b : 𝓞 D.host.E),
    red x = Ideal.Quotient.mk 𝔪 b ↔ (x : AE D) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
  choose r hr using fun x : OhE D => exists_red D 𝔪 h𝔪 (x : AE D) x.2
  have key : ∀ (x : OhE D) (b : 𝓞 D.host.E), Ideal.Quotient.mk 𝔪 (r x) = Ideal.Quotient.mk 𝔪 b ↔
      (x : AE D) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
    intro x b
    rw [mk_eq_iff D 𝔪 h𝔪]
    constructor
    · intro h
      have := add_mem (hr x) h
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h (hr x)
      rwa [sub_sub_sub_cancel_left] at this
  refine ⟨{ toFun := fun x => Ideal.Quotient.mk 𝔪 (r x)
            map_one' := ?_
            map_mul' := fun x y => ?_
            map_zero' := ?_
            map_add' := fun x y => ?_ }, key⟩
  · rw [← map_one (Ideal.Quotient.mk 𝔪), key]
    simp
  · rw [← map_mul, key]
    have := add_mem (mul_mem_hatId D 𝔪 y.2 (hr x))
      (mul_mem_hatId D 𝔪 (VacMove.inc_int D (r x)) (hr y))
    convert this using 1
    push_cast
    rw [map_mul]
    ring
  · rw [← map_zero (Ideal.Quotient.mk 𝔪), key]
    simp
  · rw [← map_add (f := _), key]
    have := add_mem (hr x) (hr y)
    convert this using 1
    push_cast
    rw [map_add (f := _)]
    ring

def intMat (N : ℕ) : ↥(intG D N) →* Matrix (Fin N) (Fin N) (OhE D) where
  toFun k := Matrix.of fun i j =>
    ⟨(((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j, (((mem_intG _).1 k.2) i j).1⟩
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  map_mul' x y := by
    ext i j
    simp [Matrix.mul_apply]

theorem exists_levelRed : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    ∃ ρ : ↥(intG D N) →* GL (Fin N) (𝓞 D.host.E ⧸ 𝔪), ∀ (k : ↥(intG D N)) (i j : Fin N) (b : 𝓞 D.host.E),
      ((ρ k : Matrix (Fin N) (Fin N) (𝓞 D.host.E ⧸ 𝔪)) i j = Ideal.Quotient.mk 𝔪 b ↔
        (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D (b : D.host.E) ∈ hatId D 𝔪) := by
  intro D 𝔪 h𝔪 N
  obtain ⟨red, hred⟩ := exists_redHom D 𝔪 h𝔪
  exact ⟨((red.mapMatrix (m := Fin N)).toMonoidHom.comp (intMat D N)).toHomUnits,
    fun k i j b => hred (intMat D N k i j) b⟩

end GlobalTheory.LevelRed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionMaxLevelUnitaryModIdealStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduction_maxLevel_unitary_mod_ideal : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    ∃ ρ : ↥(intG D N) →* GL (Fin N) (𝓞 D.host.E ⧸ 𝔪), ∀ (k : ↥(intG D N)) (i j : Fin N) (b : 𝓞 D.host.E),
      ((ρ k : Matrix (Fin N) (Fin N) (𝓞 D.host.E ⧸ 𝔪)) i j = Ideal.Quotient.mk 𝔪 b ↔
        (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D (b : D.host.E) ∈ hatId D 𝔪) := by
  first | exact @GlobalTheory.LevelRed.exists_levelRed | exact GlobalTheory.LevelRed.exists_levelRed | (intros; apply GlobalTheory.LevelRed.exists_levelRed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBlockParabolicSubgroupGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBlockParabolicSubgroupGL
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

noncomputable section

namespace GlobalTheory.StdLoc

def blockMat {R : Type} [CommRing R] {a b : ℕ} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin b) R)
    (D : Matrix (Fin b) (Fin b) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D)

theorem det_blockMat {R : Type} [CommRing R] {a b : ℕ} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin b) R)
    (D : Matrix (Fin b) (Fin b) R) : (blockMat A B D).det = A.det * D.det := by
  rw [blockMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

def blockParMk {R : Type} [CommRing R] {a b : ℕ}
    (x : GL (Fin a) R × GL (Fin b) R × Matrix (Fin a) (Fin b) R) : blockPar R a (a + b) :=
  ⟨Matrix.GeneralLinearGroup.mk'' (blockMat x.1.1 x.2.2 x.2.1.1) (by
      rw [det_blockMat]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 x.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 x.2.1.isUnit)), by
    rw [mem_blockPar]
    intro i j hj hi
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    show blockMat x.1.1 x.2.2 x.2.1.1 _ _ = 0
    rcases i with i | i
    · exact absurd hi (by simp)
    rcases j with j | j
    · simp only [blockMat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    · exact absurd hj (by simp)⟩

theorem blockParMk_val {R : Type} [CommRing R] {a b : ℕ}
    (x : GL (Fin a) R × GL (Fin b) R × Matrix (Fin a) (Fin b) R) :
    ((blockParMk x).1 : Matrix (Fin (a + b)) (Fin (a + b)) R) = blockMat x.1.1 x.2.2 x.2.1.1 := rfl

theorem blockParMk_bijective {R : Type} [CommRing R] {a b : ℕ} :
    Function.Bijective (blockParMk (R := R) (a := a) (b := b)) := by
  constructor
  · rintro ⟨A, D, B⟩ ⟨A', D', B'⟩ h
    have h1 : blockMat A.1 B D.1 = blockMat A'.1 B' D'.1 := by
      have := congrArg (fun g : blockPar R a (a + b) => (g.1 : Matrix (Fin (a + b)) (Fin (a + b)) R)) h
      simpa only [blockParMk_val] using this
    have h2 := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h1
    obtain ⟨hA, hB, -, hD⟩ := Matrix.fromBlocks_inj.1 h2
    exact Prod.ext (Units.ext hA) (Prod.ext (Units.ext hD) hB)
  · rintro ⟨g, hg⟩
    set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R :=
      (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm (g : Matrix (Fin (a + b)) (Fin (a + b)) R) with hM
    have h0 : M.toBlocks₂₁ = 0 := by
      ext i j
      exact (mem_blockPar g).1 hg (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) (by simp) (by simp)
    have hb : blockMat M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂ = g := by
      rw [blockMat, ← h0, Matrix.fromBlocks_toBlocks, hM, Equiv.apply_symm_apply]
    have hu : IsUnit (M.toBlocks₁₁.det * M.toBlocks₂₂.det) := by
      rw [← det_blockMat _ M.toBlocks₁₂, hb]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    refine ⟨(Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_left hu),
      Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_right hu), M.toBlocks₁₂), ?_⟩
    exact Subtype.ext (Units.ext hb)

theorem card_blockPar (R : Type) [CommRing R] [Finite R] (a d : ℕ) (h : a ≤ d) :
    Nat.card (blockPar R a d) =
      Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, ← Nat.card_eq_of_bijective _ blockParMk_bijective, Nat.card_prod, Nat.card_prod,
    mul_assoc]
  congr 2
  show Nat.card (Fin a → Fin b → R) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp [mul_comm]

end GlobalTheory.StdLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBlockParabolicSubgroupGLStatement
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_blockParabolicSubgroupGL : ∀ (R : Type) [CommRing R] [Finite R] (a d : ℕ), a ≤ d →
    Nat.card (blockPar R a d) = Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  first | exact @GlobalTheory.StdLoc.card_blockPar | exact GlobalTheory.StdLoc.card_blockPar | (intros; apply GlobalTheory.StdLoc.card_blockPar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGLRingOfIntegersQuotientProdFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGLRingOfIntegersQuotientProdFactors
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

noncomputable section

namespace GlobalTheory.CardGLQuot

theorem card_GL_field_real (κ : Type) [Field κ] [Finite κ] (n : ℕ) :
    (Nat.card (GL (Fin n) κ) : ℝ) = (Nat.card κ : ℝ) ^ (n ^ 2) * glVol (Nat.card κ) n := by
  haveI := Fintype.ofFinite κ
  have hq1 : 1 ≤ Nat.card κ := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos).ne'
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [glVol, hIcc]
  rw [Matrix.card_GL_field, Nat.cast_prod, ← Nat.card_eq_fintype_card]
  rw [Fin.prod_univ_eq_prod_range (fun i => ((Nat.card κ ^ n - Nat.card κ ^ i : ℕ) : ℝ)) n]
  rw [← Finset.prod_range_reflect]
  have hIoc : Finset.Ioc 0 n = (Finset.range n).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩; omega
  rw [hIoc, Finset.prod_map, sq, pow_mul,
    show ((Nat.card κ : ℝ) ^ n) ^ n = ∏ _j ∈ Finset.range n, (Nat.card κ : ℝ) ^ n by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hj' : j < n := Finset.mem_range.mp hj
  have hle : Nat.card κ ^ (n - 1 - j) ≤ Nat.card κ ^ n := Nat.pow_le_pow_right hq1 (by omega)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
  congr 1
  have hsplit : (Nat.card κ : ℝ) ^ n = (Nat.card κ : ℝ) ^ (n - 1 - j) * (Nat.card κ : ℝ) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]


open Classical in
theorem card_GL_eq_card_isUnit (S : Type) [CommRing S] [Fintype S] (n : ℕ) :
    Nat.card (GL (Fin n) S) =
      (Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) S => IsUnit A)).card := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.ofBijective (fun u => ⟨(u : Matrix (Fin n) (Fin n) S), u.isUnit⟩) ⟨?_, ?_⟩)
  · intro u v h; exact Units.ext (congrArg Subtype.val h)
  · rintro ⟨A, hA⟩; exact ⟨hA.unit, rfl⟩

theorem card_GL_of_residue {R k : Type} [CommRing R] [Finite R] [Field k] (π : R →+* k)
    (hπ : Function.Surjective π) (hu : ∀ x, IsUnit x ↔ π x ≠ 0) (n : ℕ) :
    (Nat.card (GL (Fin n) R) : ℝ) = (Nat.card R : ℝ) ^ (n ^ 2) * glVol (Nat.card k) n := by
  classical
  haveI := Fintype.ofFinite R
  haveI : Finite k := Finite.of_surjective π hπ
  haveI := Fintype.ofFinite k
  let φ : Matrix (Fin n) (Fin n) R →+ Matrix (Fin n) (Fin n) k := (π.mapMatrix).toAddMonoidHom
  have hφ : ∀ A, φ A = A.map π := fun A => rfl
  have hsurj : Function.Surjective φ := by
    intro B
    refine ⟨Matrix.of fun i j => (hπ (B i j)).choose, ?_⟩
    ext i j
    exact (hπ (B i j)).choose_spec
  have hunit : ∀ A, IsUnit A ↔ IsUnit (φ A) := by
    intro A
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, hu, isUnit_iff_ne_zero, hφ,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  set K := (Finset.univ.filter (fun A => φ A = 0)).card with hK
  have hfib : ∀ B, (Finset.univ.filter (fun A => φ A = B)).card = K :=
    fun B => AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj B) (hsurj 0)
  have h1 : (Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) R => IsUnit A)).card =
      (Finset.univ.filter (fun B : Matrix (Fin n) (Fin n) k => IsUnit B)).card * K := by
    rw [Finset.card_eq_sum_card_fiberwise (f := φ)
      (t := Finset.univ.filter (fun B : Matrix (Fin n) (Fin n) k => IsUnit B))]
    · rw [Finset.sum_congr rfl (g := fun _ => K), Finset.sum_const, smul_eq_mul]
      intro B hB
      rw [← hfib B, Finset.filter_filter]
      congr 1
      refine Finset.filter_congr (fun A _ => ?_)
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨(hunit A).2 ?_, h⟩
        rw [h]; exact (Finset.mem_filter.1 hB).2
    · intro A hA
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢
      exact (hunit A).1 hA
  have h2 : Fintype.card (Matrix (Fin n) (Fin n) R) = Fintype.card (Matrix (Fin n) (Fin n) k) * K := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)]
    · rw [Finset.sum_congr rfl (g := fun _ => K), Finset.sum_const, smul_eq_mul, Finset.card_univ]
      intro B _
      exact hfib B
    · intro A _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  have hcard : ∀ (S : Type) [Fintype S],
      (Fintype.card (Matrix (Fin n) (Fin n) S) : ℝ) = (Nat.card S : ℝ) ^ (n ^ 2) := by
    intro S _
    rw [← Nat.card_eq_fintype_card, show Nat.card (Matrix (Fin n) (Fin n) S) = Nat.card (Fin n → Fin n → S) from rfl,
      Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul, ← sq]
    push_cast; rfl
  have hR : (Nat.card R : ℝ) ^ (n ^ 2) = (Nat.card k : ℝ) ^ (n ^ 2) * K := by
    rw [← hcard R, ← hcard k, h2, Nat.cast_mul]
  rw [card_GL_eq_card_isUnit, h1, Nat.cast_mul, ← card_GL_eq_card_isUnit, card_GL_field_real]
  linear_combination (-(glVol (Nat.card k) n)) * hR

theorem isUnit_quot_pow_iff {A : Type} [CommRing A] {w : Ideal A} (hw : w.IsMaximal) {c : ℕ} (hc : c ≠ 0)
    (x : A ⧸ w ^ c) : IsUnit x ↔ Ideal.Quotient.factor (Ideal.pow_le_self hc) x ≠ 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ne, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h ha
    have hU := h.map (Ideal.Quotient.factor (Ideal.pow_le_self hc))
    rw [Ideal.Quotient.factor_mk, (Ideal.Quotient.eq_zero_iff_mem).2 ha] at hU
    haveI := hw.isPrime
    exact not_isUnit_zero hU
  · intro ha
    obtain ⟨y, i, hi, hyx⟩ := hw.exists_inv ha
    have hnil : IsNilpotent (Ideal.Quotient.mk (w ^ c) i) :=
      ⟨c, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi c⟩
    have hu : IsUnit (Ideal.Quotient.mk (w ^ c) (y * a)) := by
      have := hnil.isUnit_one_sub
      rwa [← map_one (Ideal.Quotient.mk (w ^ c)), ← map_sub,
        show (1 : A) - i = y * a by rw [← hyx]; ring] at this
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu

theorem natCard_quot {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) :
    Nat.card (𝓞 E ⧸ I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem card_GL_quot (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥) (n : ℕ) :
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n := by
  classical
  let e := IsDedekindDomain.quotientEquivPiFactors h𝔪
  have h1 : Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) = Nat.card (∀ P : (factors 𝔪).toFinset,
      GL (Fin n) (𝓞 E ⧸ (P : Ideal (𝓞 E)) ^ (factors 𝔪).count ↑P)) :=
    Nat.card_congr ((Units.mapEquiv ((e.mapMatrix).trans Matrix.piRingEquiv).toMulEquiv).trans
      MulEquiv.piUnits).toEquiv
  rw [h1, Nat.card_pi, Nat.cast_prod, ← factors_eq_normalizedFactors]
  rw [← Finset.prod_coe_sort (factors 𝔪).toFinset (fun w => (Ideal.absNorm w : ℝ) ^ ((factors 𝔪).count w * n ^ 2) *
    glVol (Ideal.absNorm w : ℝ) n)]
  refine Finset.prod_congr rfl (fun P _ => ?_)
  have hmem : (P : Ideal (𝓞 E)) ∈ factors 𝔪 := Multiset.mem_toFinset.1 P.2
  have hprime : Prime (P : Ideal (𝓞 E)) := prime_of_factor _ hmem
  have hbot : (P : Ideal (𝓞 E)) ≠ ⊥ := hprime.ne_zero
  have hmax : (P : Ideal (𝓞 E)).IsMaximal :=
    ((Ideal.isPrime_of_prime hprime)).isMaximal hbot
  have hc : (factors 𝔪).count (P : Ideal (𝓞 E)) ≠ 0 := (Multiset.count_pos.2 hmem).ne'
  letI : Field (𝓞 E ⧸ (P : Ideal (𝓞 E))) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ (P : Ideal (𝓞 E)) ^ (factors 𝔪).count ↑P) := by
    apply Nat.finite_of_card_ne_zero
    rw [natCard_quot, Ne, Ideal.absNorm_eq_zero_iff]
    exact pow_ne_zero _ hbot
  rw [card_GL_of_residue (Ideal.Quotient.factor (Ideal.pow_le_self hc)) (Ideal.Quotient.factor_surjective _)
    (isUnit_quot_pow_iff hmax hc) n, natCard_quot, natCard_quot, map_pow, Nat.cast_pow, ← pow_mul]

theorem card_GL_quot_prod : ∀ (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → ∀ n : ℕ,
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n :=
  fun E _ _ 𝔪 h𝔪 n => card_GL_quot E 𝔪 h𝔪 n

end GlobalTheory.CardGLQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGLRingOfIntegersQuotientProdFactorsStatement
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors : ∀ (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → ∀ n : ℕ,
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n := by
  first | exact @GlobalTheory.CardGLQuot.card_GL_quot_prod | exact GlobalTheory.CardGLQuot.card_GL_quot_prod | (intros; apply GlobalTheory.CardGLQuot.card_GL_quot_prod <;> assumption)
end
end

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.StdLoc

theorem idx_alg (q : ℝ) (hq : q ≠ 0) (c a a' : ℕ) :
    q ^ (c * (a + a') ^ 2) * glVol q (a + a') /
      (q ^ (c * a ^ 2) * glVol q a * (q ^ (c * a' ^ 2) * glVol q a') * (q ^ c) ^ (a * a')) = blockIdx q c a a' := by
  rw [blockIdx]
  have e : c * (a + a') ^ 2 = c * a ^ 2 + c * a' ^ 2 + c * a * a' + c * a * a' := by ring
  have e2 : (q ^ c) ^ (a * a') = q ^ (c * a * a') := by rw [← pow_mul, mul_assoc]
  rw [e, pow_add, pow_add, pow_add, e2]
  have h1 : q ^ (c * a ^ 2) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ (c * a' ^ 2) ≠ 0 := pow_ne_zero _ hq
  have h3 : q ^ (c * a * a') ≠ 0 := pow_ne_zero _ hq
  by_cases ha : glVol q a = 0
  · simp [ha]
  by_cases hb : glVol q a' = 0
  · simp [hb]
  field_simp

end GlobalTheory.StdLoc

namespace GlobalTheory.StdLoc

theorem glVol_add (q : ℝ) (a' a : ℕ) :
    glVol q (a' + a) = glVol q a' * ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, glVol, Finset.prod_Icc_succ_top (by omega), ← glVol, ih, Finset.prod_Icc_succ_top (by omega), mul_assoc, add_assoc]

theorem glVol_pos {q : ℝ} (hq : 1 < q) (n : ℕ) : 0 < glVol q n :=
  Finset.prod_pos fun i hi => sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by simp at hi; omega)))

theorem stdLoc_product {q : ℝ} (hq : 1 < q) (c a a' : ℕ) :
    (∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹))⁻¹ * blockIdx q c a a' * ((q ^ (c * a * a'))⁻¹ * glVol q a) = 1 := by
  have h1 := glVol_pos hq a
  have h2 := glVol_pos hq a'
  have h3 : (0 : ℝ) < q ^ (c * a * a') := pow_pos (by linarith) _
  have h4 : 0 < ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) := by
    have := glVol_add q a' a
    have h5 := glVol_pos hq (a' + a)
    rw [this] at h5
    exact pos_of_mul_pos_right h5 h2.le
  rw [blockIdx, add_comm a a', glVol_add]
  generalize ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) = P at h4 ⊢
  field_simp

end GlobalTheory.StdLoc

namespace GlobalTheory.StdLoc

open UniqueFactorizationMonoid

theorem absNorm_eq_prod {E : Type} [Field E] [NumberField E] {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥) :
    (Ideal.absNorm 𝔪 : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset, (Ideal.absNorm w : ℝ) ^ (normalizedFactors 𝔪).count w := by
  have h1 : (normalizedFactors 𝔪).prod = 𝔪 := by
    have := prod_normalizedFactors h𝔪
    exact associated_iff_eq.1 this
  conv_lhs => rw [← h1]
  rw [map_multiset_prod, Nat.cast_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
  simp

theorem relIndex_blockLevel {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (𝔪 : Ideal (𝓞 D.host.E)) (a : ℕ)
    (h𝔪 : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (ha : a ≤ P.d) (hJ : IsBlockLevel P 𝔪 a) :
    ((P.J.relIndex (intG D P.d) : ℕ) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      blockIdx (Ideal.absNorm w : ℝ) ((normalizedFactors 𝔪).count w) a (P.d - a) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_reduction_maxLevel_unitary_mod_ideal D 𝔪 h𝔪 P.d
  have hsurj : Function.Surjective ρ := by
    intro g'
    choose g hg using fun i j => Ideal.Quotient.mk_surjective (I := 𝔪) (((g' : GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin P.d) (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) i j)
    have hgm : (Matrix.of g).map (Ideal.Quotient.mk 𝔪) = ((g' : GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin P.d) (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) := by
      ext i j; simp [hg]
    have h2 := GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal D 𝔪 h𝔪 hcop P.d (Matrix.of g) (by rw [hgm]; exact Matrix.isUnits_det_units g')
    obtain ⟨k, hk, hk'⟩ := h2
    simp only [Matrix.of_apply] at hk'
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Units.ext
    ext i j
    exact ((hρ ⟨k, hk⟩ i j (g i j)).2 (hk' i j)).trans (hg i j)
  have hsub : P.J.subgroupOf (intG D P.d) = (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).comap ρ := by
    have h0 : ∀ x : AE D, x - inc D ((0 : 𝓞 D.host.E) : D.host.E) = x := fun x => by simp
    refine Subgroup.ext fun k => ⟨fun h => ?_, fun h => ?_⟩
    · have h' : (k : GA D P.d) ∈ P.J := h
      show ρ k ∈ blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d
      refine (mem_blockPar _).2 fun i j hj hi => ?_
      have h1 := ((hJ _).1 h').2 i j hj hi
      rw [← h0 ((((k : GA D P.d) : GL (Fin P.d) (AE D)) : Matrix (Fin P.d) (Fin P.d) (AE D)) i j)] at h1
      exact ((hρ k i j 0).2 h1).trans (map_zero _)
    · have h' : ρ k ∈ blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d := h
      show (k : GA D P.d) ∈ P.J
      refine (hJ _).2 ⟨k.2, fun i j hj hi => ?_⟩
      have h1 := (hρ k i j 0).1 (((mem_blockPar _).1 h' i j hj hi).trans (map_zero _).symm)
      rwa [h0] at h1
  have hR : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) :=
    Nat.finite_of_card_ne_zero (by rw [hR]; simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  have hidx : P.J.relIndex (intG D P.d) = (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).index := by
    show (P.J.subgroupOf (intG D P.d)).index = _
    rw [hsub, Subgroup.index_comap_of_surjective _ hsurj]
  have hcm := (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).card_mul_index
  have hP0 : (Nat.card (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hI : ((blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).index : ℝ) =
      (Nat.card (GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : ℝ) / (Nat.card (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d) : ℝ) := by
    rw [eq_div_iff hP0, mul_comm]; exact_mod_cast hcm
  rw [hidx, hI, GlobalTheory.T.card_blockParabolicSubgroupGL _ a P.d ha, hR]
  push_cast
  rw [GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪, GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪, GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪, absNorm_eq_prod h𝔪, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hq : (Ideal.absNorm w : ℝ) ≠ 0 := by
    have hw0 : w ≠ ⊥ := fun h => by
      rw [h] at hw; exact zero_notMem_normalizedFactors _ (Multiset.mem_toFinset.1 hw)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hw0)
  obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le ha
  rw [ha', Nat.add_sub_cancel_left]
  exact idx_alg _ hq _ _ _

end GlobalTheory.StdLoc
