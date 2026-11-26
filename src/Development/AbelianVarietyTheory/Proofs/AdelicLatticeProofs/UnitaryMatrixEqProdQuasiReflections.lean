module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRational
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexTopOfGroupFg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLocalNonnormOfNonsquareAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexUnitsLocalSquaresFiniteRealPlacesLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsQuasiReflectionProdMulVecEq
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsQuasiReflectionProdMulVecEq
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ReflStep

variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)

theorem herm_sub_smul_left (z x w : Fin n → E) (e : E) :
    hermE c G (z - e • x) w = hermE c G z w - e * hermE c G x w := by
  simp only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_sub_smul_right (z x w : Fin n → E) (e : E) :
    hermE c G w (z - e • x) = hermE c G w z - c e * hermE c G w x := by
  simp only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    map_sub, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_smul_left (x w : Fin n → E) (e : E) :
    hermE c G (e • x) w = e * hermE c G x w := by
  simp only [hermE, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_conj (h : IsHermForm c G) (x y : Fin n → E) : c (hermE c G x y) = hermE c G y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermE, map_sum, map_mul, h.1, h.2.2.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem refl_mulVec (x v : Fin n → E) (u : E) :
    refl c G x u *ᵥ v = v + ((u - 1) * hermE c G v x / hermE c G x x) • x := by
  have hd : (G *ᵥ fun b => c (x b)) ⬝ᵥ v = hermE c G v x := by
    simp only [hermE, dotProduct, Matrix.mulVec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [refl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hd]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

theorem exists_refl (h : IsHermForm c G) (x z : Fin n → E) (hz : hermE c G z z = hermE c G x x) (e : E)
    (he : c e = e) (he2 : e * e = 1) (hy : hermE c G (z - e • x) (z - e • x) ≠ 0) :
    ∃ u : E, u * c u = 1 ∧ refl c G (z - e • x) u *ᵥ z = e • x := by
  obtain ⟨a, ha⟩ : ∃ a, a = hermE c G z (z - e • x) := ⟨_, rfl⟩
  have hyy : hermE c G (z - e • x) (z - e • x) = a + c a := by
    rw [ha, herm_conj c G h, herm_sub_smul_left c G z x (z - e • x), herm_sub_smul_left c G z x z,
      herm_sub_smul_right c G z x x, he, hz]
    linear_combination (hermE c G x x) * he2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hy (by simpa using hyy)
  have hca : c a ≠ 0 := by simpa using ha0
  refine ⟨-c a / a, ?_, ?_⟩
  · rw [map_div₀, map_neg, h.1]
    field_simp
  · rw [refl_mulVec, ← ha]
    have : (-c a / a - 1) * a / hermE c G (z - e • x) (z - e • x) = -1 := by
      rw [div_eq_iff hy, hyy]
      field_simp
      ring
    rw [this]
    simp

end GlobalTheory.UnRep.ReflStep

open GlobalTheory.UnRep.ReflStep in
theorem GlobalTheory.UnRep.exists_refl_prod_mulVec_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x z : Fin n → E, hermE c G x x ≠ 0 → hermE c G z z = hermE c G x x → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1 ∧ p.1 ∈ Submodule.span E {x, z}) ∧ (l.map fun p => refl c G p.1 p.2).prod *ᵥ z = x := by
  intro F E _ _ _ _ _ c n G h x z hx hz
  have hxs : x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hzs : z ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hmem : ∀ e : E, z - e • x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := fun e =>
    Submodule.sub_mem _ hzs (Submodule.smul_mem _ _ hxs)
  by_cases h1 : hermE c G (z - (1 : E) • x) (z - (1 : E) • x) = 0
  · have h2 : hermE c G (z - (-1 : E) • x) (z - (-1 : E) • x) ≠ 0 := by
      intro h2
      rw [herm_sub_smul_left, herm_sub_smul_right, herm_sub_smul_right] at h1 h2
      simp only [map_one, map_neg, hz] at h1 h2
      apply hx
      have h4 : (4 : E) * hermE c G x x = 0 := by linear_combination h1 + h2
      exact (mul_eq_zero.1 h4).resolve_left (by norm_num)
    obtain ⟨u, hu, hu'⟩ := exists_refl c G h x z hz (-1) (by simp) (by simp) h2
    refine ⟨[(x, -1), (z - (-1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨hx, by simp, hxs⟩
      · exact ⟨h2, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← Matrix.mulVec_mulVec, hu', refl_mulVec, herm_smul_left, ← add_smul]
      have : (-1 : E) + (-1 - 1) * (-1 * hermE c G x x) / hermE c G x x = 1 := by
        field_simp
        ring
      rw [this, one_smul]
  · obtain ⟨u, hu, hu'⟩ := exists_refl c G h x z hz 1 (by simp) (by simp) h1
    refine ⟨[(z - (1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact ⟨h1, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [hu', one_smul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsQuasiReflectionProdMulVecEqStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiReflection_prod_mulVec_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x z : Fin n → E, hermE c G x x ≠ 0 → hermE c G z z = hermE c G x x → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1 ∧ p.1 ∈ Submodule.span E {x, z}) ∧ (l.map fun p => refl c G p.1 p.2).prod *ᵥ z = x := by
  first | exact @GlobalTheory.UnRep.exists_refl_prod_mulVec_eq | exact GlobalTheory.UnRep.exists_refl_prod_mulVec_eq | (intros; apply GlobalTheory.UnRep.exists_refl_prod_mulVec_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ReflGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}

omit [NumberField F] [NumberField E] in
theorem isUnE_mul {a b : Matrix (Fin n) (Fin n) E} (ha : IsUnE c G a) (hb : IsUnE c G b) :
    IsUnE c G (a * b) := by
  intro x y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]

theorem isUnE_prod (hG : IsHermForm c G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) :
    IsUnE c G (l.map fun p => refl c G p.1 p.2).prod := by
  induction l with
  | nil => intro x y; simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons]
    have hp := hl p List.mem_cons_self
    exact isUnE_mul ((GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).2.2.2 p.2 hp.2)
      (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem exists_inv (hG : IsHermForm c G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) :
    ∃ l' : List ((Fin n → E) × E), (∀ p ∈ l', hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧
      (l'.map fun p => refl c G p.1 p.2).prod * (l.map fun p => refl c G p.1 p.2).prod = 1 := by
  induction l with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    obtain ⟨-, r1, r2, -⟩ := GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1
    refine ⟨l' ++ [(p.1, c p.2)], ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact h1 q hq
      · rw [List.mem_singleton] at hq
        subst hq
        refine ⟨hp.1, ?_⟩
        show c p.2 * c (c p.2) = 1
        rw [hG.1, mul_comm]
        exact hp.2
    · rw [List.map_append, List.prod_append, List.map_cons, List.map_cons, List.prod_cons,
        List.prod_cons, List.map_nil, List.prod_nil, mul_one, mul_assoc,
        ← mul_assoc (refl c G p.1 (c p.2)), r2, mul_comm (c p.2), hp.2, r1, one_mul, h2]

theorem prod_fix (hG : IsHermForm c G) (v : Fin n → E) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ hermE c G v p.1 = 0) :
    (l.map fun p => refl c G p.1 p.2).prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
      (GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).1, hp.2]
    simp

omit [NumberField F] [NumberField E] in
theorem herm_span {v x z y : Fin n → E} (hx : hermE c G v x = 0) (hz : hermE c G v z = 0)
    (hy : y ∈ Submodule.span E {x, z}) : hermE c G v y = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hy
  have : hermE c G v (a • x + b • z) = c a * hermE c G v x + c b * hermE c G v z := by
    simp only [hermE, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, map_add, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, hx, hz]
  simp

theorem exists_fix (hG : IsHermForm c G) {γ : Matrix (Fin n) (Fin n) E} (hγ : IsUnE c G γ)
    (x : Fin n → Fin n → E) (h1 : ∀ i, hermE c G (x i) (x i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) (k : ℕ) :
    ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧
      ∀ i : Fin n, i.val < k → ((l.map fun p => refl c G p.1 p.2).prod * γ) *ᵥ x i = x i := by
  induction k with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    obtain ⟨l, hl, hfix⟩ := ih
    by_cases hk : k < n
    · have hU := isUnE_mul (isUnE_prod hG l hl) hγ
      set δ := (l.map fun p => refl c G p.1 p.2).prod * γ with hδ
      obtain ⟨m, hm, hmx⟩ := GlobalTheory.T.exists_quasiReflection_prod_mulVec_eq F E c n G hG (x ⟨k, hk⟩) (δ *ᵥ x ⟨k, hk⟩) (h1 _) (hU _ _)
      refine ⟨m ++ l, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨(hm p hp).1, (hm p hp).2.1⟩
        · exact hl p hp
      · intro i hi
        rw [List.map_append, List.prod_append, mul_assoc, ← hδ, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · have hne : i ≠ ⟨k, hk⟩ := fun h => by simp [h] at hi
          rw [hfix i hi]
          refine prod_fix hG _ m fun p hp => ⟨(hm p hp).1, herm_span (h2 _ _ hne) ?_ (hm p hp).2.2⟩
          rw [← h2 _ _ hne, ← hU (x i) (x ⟨k, hk⟩), hfix i hi]
        · have : i = ⟨k, hk⟩ := Fin.ext hi
          rw [this]
          exact hmx
    · exact ⟨l, hl, fun i _ => hfix i (lt_of_lt_of_le i.2 (not_lt.1 hk))⟩

end GlobalTheory.UnRep.ReflGen

theorem GlobalTheory.UnRep.isUnE_eq_prod_refl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ γ, IsUnE c G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧ γ = (l.map fun p => refl c G p.1 p.2).prod := by
  intro F E _ _ _ _ _ c n G hG γ hγ
  obtain ⟨x, h1, h2, h3⟩ := GlobalTheory.T.exists_anisotropic_orthogonal_basis_hermitian F E c n G hG
  obtain ⟨l, hl, hfix⟩ := ReflGen.exists_fix hG hγ x h1 h2 n
  obtain ⟨l', hl', hinv⟩ := ReflGen.exists_inv hG l hl
  refine ⟨l', hl', ?_⟩
  have hone : (l.map fun p => refl c G p.1 p.2).prod * γ = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range h3 fun i => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix i i.2, Matrix.one_mulVec]
  rw [← one_mul γ, ← hinv, mul_assoc, hone, mul_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflectionsStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryMatrix_eq_prod_quasiReflections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ γ, IsUnE c G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧ γ = (l.map fun p => refl c G p.1 p.2).prod := by
  first | exact @GlobalTheory.UnRep.isUnE_eq_prod_refl | exact GlobalTheory.UnRep.isUnE_eq_prod_refl | (intros; apply GlobalTheory.UnRep.isUnE_eq_prod_refl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem _root_.GlobalTheory.CNorm.kummer_basic : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.CNorm.IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ (∀ y : E, σ^[p] y = y) ∧ (∀ y : E, σ y = y → ∃ a : F, y = algebraMap F E a) ∧ (∀ y : E, ∏ i ∈ Finset.range p, σ^[i] y = 1 → ∃ z : E, z ≠ 0 ∧ y = σ z / z) ∧ (∀ (u : F) (y : E), y ^ p = algebraMap F E u → ∃ (k : ℕ) (r : F), u = δ ^ k * r ^ p) ∧ ∀ x : Fˣ, x ∈ _root_.GlobalTheory.CNorm.kNorm p (RingHom.id F) δ ↔ ∃ y : E, ∏ i ∈ Finset.range p, σ^[i] y = algebraMap F E (x : F) := by
  intro p F E _ _ _ _ ζ δ θ σ h
  obtain ⟨hfd, hrank, hgal, hord, hgen, ⟨e⟩, -⟩ :=
    _root_.GlobalTheory.CNorm.kummer_galois p F E ζ δ θ σ h
  have hp := h.prime
  classical
  have hprod : ∀ y : E, algebraMap F E (Algebra.norm F y) = ∏ i ∈ Finset.range p, σ^[i] y := by
    intro y
    rw [Algebra.norm_eq_prod_automorphisms]
    have huniv : (Finset.univ : Finset Gal(E/F)) = (Finset.range p).image (σ ^ ·) := by
      ext τ
      simp only [Finset.mem_univ, true_iff]
      rw [← hord]
      exact mem_zpowers_iff_mem_range_orderOf.1 (hgen τ)
    rw [huniv, Finset.prod_image]
    · exact Finset.prod_congr rfl fun i _ => by rw [AlgEquiv.coe_pow]
    · intro i hi j hj hij
      exact pow_injOn_Iio_orderOf (by rw [hord]; simpa using hi) (by rw [hord]; simpa using hj) hij
  have hfix : ∀ y : E, σ y = y → ∃ a : F, y = algebraMap F E a := by
    intro y hy
    have hmem : y ∈ (⊥ : IntermediateField F E) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro τ
      have hσ : σ ∈ MulAction.stabilizer Gal(E/F) y := MulAction.mem_stabilizer_iff.2 hy
      exact MulAction.mem_stabilizer_iff.1 ((Subgroup.zpowers_le.2 hσ) (hgen τ))
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hmem
    exact ⟨a, ha.symm⟩
  refine ⟨hfd, hrank, ?_, hfix, ?_, ?_, ?_⟩
  · intro y
    rw [← AlgEquiv.coe_pow, ← hord, pow_orderOf_eq_one]
    rfl
  · intro y hy
    haveI : IsCyclic Gal(E/F) := ⟨⟨σ, fun τ => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen τ)
      exact ⟨k, hk⟩⟩⟩
    have hn : Algebra.norm F y = 1 :=
      (algebraMap F E).injective (by rw [hprod, hy, map_one])
    obtain ⟨z, hz⟩ := groupCohomology.exists_div_of_norm_eq_one hgen hn
    refine ⟨(z : E)⁻¹, inv_ne_zero z.ne_zero, ?_⟩
    rw [map_inv₀, inv_div_inv, hz]
  · intro u y hy
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hζ := h.root.map_of_injective (algebraMap F E).injective
    by_cases hy0 : y = 0
    · refine ⟨1, 0, ?_⟩
      subst hy0
      rw [zero_pow hp.ne_zero] at hy
      have hu : u = 0 := (algebraMap F E).injective (by rw [← hy, map_zero])
      simp [hu, hp.ne_zero]
    · have hσy : (σ y / y) ^ p = 1 := by
        rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, ← hy]
        exact div_self (pow_ne_zero _ hy0)
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hσy
      have hσy' : σ y = algebraMap F E ζ ^ j * y := by
        rw [hj]; field_simp
      have hδ : δ ≠ 0 := by
        intro hδ
        exact h.nonpow 0 (by rw [hδ, zero_pow hp.ne_zero])
      have hθ : θ ≠ 0 := by
        intro hθ
        have := h.pow
        rw [hθ, zero_pow hp.ne_zero, eq_comm, map_eq_zero] at this
        exact hδ this
      have hζ0 : algebraMap F E ζ ≠ 0 := hζ.ne_zero hp.ne_zero
      have hw : σ (y / θ ^ j) = y / θ ^ j := by
        rw [map_div₀, map_pow, h.conj, hσy', mul_pow]
        field_simp
      obtain ⟨a, ha⟩ := hfix _ hw
      have hy' : y = algebraMap F E a * θ ^ j := by
        rw [← ha]; field_simp
      refine ⟨j, a, (algebraMap F E).injective ?_⟩
      rw [← hy, hy', mul_pow, ← pow_mul, mul_comm j p, pow_mul, h.pow]
      simp only [map_mul, map_pow]
      ring
  · intro x
    rw [_root_.GlobalTheory.CNorm.mem_kNorm]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨e.symm w, ?_⟩
      rw [← hprod, Algebra.norm_eq_of_algEquiv, hw]
      rfl
    · rintro ⟨y, hy⟩
      have hn : Algebra.norm F y = x := (algebraMap F E).injective (by rw [hprod, hy])
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [Algebra.norm_zero] at hn
        exact x.ne_zero hn.symm
      refine ⟨Units.map (e : E →* AdjoinRoot (X ^ p - C δ)) (Units.mk0 y hy0), ?_⟩
      simp only [Units.coe_map, Units.val_mk0, MonoidHom.coe_coe, RingHom.id_apply]
      rw [Algebra.norm_eq_of_algEquiv, hn]

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90Statement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ (∀ y : E, σ^[p] y = y) ∧ (∀ y : E, σ y = y → ∃ a : F, y = algebraMap F E a) ∧ (∀ y : E, ∏ i ∈ Finset.range p, σ^[i] y = 1 → ∃ z : E, z ≠ 0 ∧ y = σ z / z) ∧ (∀ (u : F) (y : E), y ^ p = algebraMap F E u → ∃ (k : ℕ) (r : F), u = δ ^ k * r ^ p) ∧ ∀ x : Fˣ, x ∈ kNorm p (RingHom.id F) δ ↔ ∃ y : E, ∏ i ∈ Finset.range p, σ^[i] y = algebraMap F E (x : F) := by
  first | exact @GlobalTheory.CNorm.kummer_basic | exact GlobalTheory.CNorm.kummer_basic | (intros; apply GlobalTheory.CNorm.kummer_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexSqsTopOfFg
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexSqsTopOfFg
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem index_double_prod (L T : Type) [AddCommGroup L] [AddCommGroup T] [Module.Free ℤ L]
    [Module.Finite ℤ L] [Finite T] :
    (nsmulAddMonoidHom (α := L × T) 2).range.index =
      2 ^ Module.finrank ℤ (L × T) * Nat.card (nsmulAddMonoidHom (α := L × T) 2).ker := by
  have h1 : (nsmulAddMonoidHom (α := L × T) 2).range =
      ((nsmulAddMonoidHom (α := L) 2).range).prod (nsmulAddMonoidHom (α := T) 2).range := by
    ext ⟨x, y⟩
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_prod, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨⟨a, b⟩, h⟩
      exact ⟨⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a, b), Prod.ext ha hb⟩
  have h2 : (nsmulAddMonoidHom (α := L × T) 2).ker =
      (⊥ : AddSubgroup L).prod (nsmulAddMonoidHom (α := T) 2).ker := by
    ext ⟨x, y⟩
    have hx : 2 • x = 0 ↔ x = 0 := by
      rw [← natCast_zsmul, smul_eq_zero]; simp
    simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, hx]
  have h3 : Module.finrank ℤ (L × T) = Module.finrank ℤ L := by
    have hT : Module.rank ℤ T = 0 := by
      rw [rank_eq_zero_iff]
      intro x
      refine ⟨(Nat.card T : ℤ), by exact_mod_cast Nat.card_pos.ne', ?_⟩
      simp
    have hq := Submodule.rank_quotient_add_rank (LinearMap.ker (LinearMap.fst ℤ L T))
    have e1 := (LinearMap.quotKerEquivOfSurjective (LinearMap.fst ℤ L T)
      LinearMap.fst_surjective).rank_eq
    have e2 : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ L T)) = 0 := by
      rw [LinearMap.ker_fst, rank_range_of_injective _ LinearMap.inr_injective, hT]
    unfold Module.finrank
    rw [← hq, e1, e2, add_zero]
  have h4 : (nsmulAddMonoidHom (α := T) 2).range.index =
      Nat.card (nsmulAddMonoidHom (α := T) 2).ker := by
    have a := AddSubgroup.card_mul_index (nsmulAddMonoidHom (α := T) 2).range
    have b := AddSubgroup.card_mul_index (nsmulAddMonoidHom (α := T) 2).ker
    rw [AddSubgroup.index_ker] at b
    have hpos : 0 < Nat.card (nsmulAddMonoidHom (α := T) 2).range := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [a, mul_comm, b]
  rw [h1, h2, h3, AddSubgroup.index_prod, AddSubgroup.index_range_nsmul, h4,
    Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  simp

theorem index_double_of_fg (M : Type) [AddCommGroup M] [AddGroup.FG M] :
    (nsmulAddMonoidHom (α := M) 2).range.index =
      2 ^ Module.finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) 2).ker := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ (DFinsupp.equivFunOnFintype).symm
  have h := index_double_prod (Fin n →₀ ℤ) (DirectSum ι fun i => ZMod (p i ^ e i))
  rw [← AddSubgroup.index_map_equiv _ f, AddEquiv.map_range_nsmulAddMonoidHom, h,
    f.toIntLinearEquiv.finrank_eq]
  congr 1
  refine Nat.card_congr (f.toEquiv.subtypeEquiv ?_).symm
  intro a
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  change _ ↔ 2 • f a = 0
  rw [← map_nsmul, f.map_eq_zero_iff]

theorem index_sqs_top_of_fg : ∀ (G : Type) [CommGroup G] [Group.FG G],
    (sqs (⊤ : Subgroup G)).index =
      2 ^ Module.finrank ℤ (Additive G) * Nat.card {a : G // a ^ 2 = 1} := by
  intro G _ _
  have h := index_double_of_fg (Additive G)
  have h1 : (sqs (⊤ : Subgroup G)).toAddSubgroup =
      (nsmulAddMonoidHom (α := Additive G) 2).range := by
    ext x
    simp only [sqs, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨Additive.ofMul y, hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨Additive.toMul y, trivial, hy⟩
  rw [← Subgroup.index_toAddSubgroup, h1, h]
  congr 1

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexSqsTopOfFgStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_sqs_of_fg : ∀ (G : Type) [CommGroup G] [Group.FG G], (sqs (⊤ : Subgroup G)).index = 2 ^ Module.finrank ℤ (Additive G) * Nat.card {a : G // a ^ 2 = 1} := by
  first | exact @GlobalTheory.QNorm.index_sqs_top_of_fg | exact GlobalTheory.QNorm.index_sqs_top_of_fg | (intros; apply GlobalTheory.QNorm.index_sqs_top_of_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberField
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sqs_subgroupOf_self {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs U).subgroupOf U = sqs (⊤ : Subgroup U) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_top _, Subtype.ext h⟩
  · rintro ⟨y, -, h⟩
    exact ⟨y.1, y.2, congrArg Subtype.val h⟩

theorem card_sq_eq_one_sUnits (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Nat.card {a : sUnits F S // a ^ 2 = 1} = 2 := by
  have hm : (-1 : Fˣ) ∈ sUnits F S := by
    rw [mem_sUnits]; intro v _; simp
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, by simp⟩, ⟨⟨-1, hm⟩, Subtype.ext (by simp)⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun a : {a : sUnits F S // a ^ 2 = 1} => ((a.1.1 : Fˣ) : F)) h
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_neg] at h1
    norm_num at h1
  · rw [Set.eq_univ_iff_forall]
    rintro ⟨⟨a, ha⟩, h⟩
    have h1 : (a : F) ^ 2 = 1 := by
      have := congrArg (fun a : sUnits F S => ((a.1 : Fˣ) : F)) h
      simpa using this
    rcases sq_eq_one_iff.mp h1 with h2 | h2
    · left
      exact Subtype.ext (Subtype.ext (Units.ext h2))
    · right
      exact Subtype.ext (Subtype.ext (Units.ext h2))

theorem relIndex_sqs_sUnits : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  haveI := GlobalTheory.T.sUnitsNumberField_fg F S
  rw [Subgroup.relIndex, sqs_subgroupOf_self, GlobalTheory.T.index_sqs_of_fg, card_sq_eq_one_sUnits,
    ← GlobalTheory.T.finrank_sUnitsNumberField_add_one F S, pow_succ]

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberFieldStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_squares_sUnitsNumberField : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  first | exact @GlobalTheory.QNorm.relIndex_sqs_sUnits | exact GlobalTheory.QNorm.relIndex_sqs_sUnits | (intros; apply GlobalTheory.QNorm.relIndex_sqs_sUnits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowLeIndexLocalNormsSqrtExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowCardLeIndexIInf
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowCardLeIndexIInf
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_pow_card_le_index_iInf :
    ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G),
      (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 →
        2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  intro G ι _ _ K h hidx
  classical
  choose x hx hx' using h
  have key : ∀ (A : Finset ι) (j : ι), (∏ i ∈ A, x i) ∈ K j ↔ j ∉ A := by
    intro A j
    constructor
    · intro hm hj
      rw [← Finset.mul_prod_erase A x hj] at hm
      have h2 : (∏ i ∈ A.erase j, x i) ∈ K j :=
        Subgroup.prod_mem _ fun i hi => hx' i j (Finset.ne_of_mem_erase hi).symm
      exact hx j ((Subgroup.mul_mem_cancel_right _ h2).1 hm)
    · intro hj
      exact Subgroup.prod_mem _ fun i hi => hx' i j (fun e => hj (e ▸ hi))
  haveI : Finite (G ⧸ ⨅ i, K i) := Nat.finite_of_card_ne_zero hidx
  have inj : Function.Injective
      (fun A : Finset ι => ((∏ i ∈ A, x i : G) : G ⧸ ⨅ i, K i)) := by
    intro A B hAB
    have hm : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ ⨅ i, K i := QuotientGroup.eq.1 hAB
    ext j
    have hj : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ K j := (Subgroup.mem_iInf.1 hm) j
    have hiff : (∏ i ∈ A, x i) ∈ K j ↔ (∏ i ∈ B, x i) ∈ K j := by
      constructor
      · intro ha
        exact (Subgroup.mul_mem_cancel_left _ (inv_mem ha)).1 hj
      · intro hb
        exact inv_mem_iff.1 ((Subgroup.mul_mem_cancel_right _ hb).1 hj)
    rw [key, key] at hiff
    exact not_iff_not.1 hiff
  have := Nat.card_le_card_of_injective _ inj
  rwa [Nat.card_eq_fintype_card, Fintype.card_finset] at this

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowCardLeIndexIInfStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_pow_card_le_index_iInf_of_independent : ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 → 2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  first | exact @GlobalTheory.QNorm.two_pow_card_le_index_iInf | exact GlobalTheory.QNorm.two_pow_card_le_index_iInf | (intros; apply GlobalTheory.QNorm.two_pow_card_le_index_iInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowLeIndexLocalNormsSqrtExtension
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem norm_of_isSquare_mul {L : Type} [Field L] {x y δ : L} (hx : x ≠ 0)
    (h : IsSquare (x * y)) (hn : ∃ a b : L, x = a ^ 2 - δ * b ^ 2) :
    ∃ a b : L, y = a ^ 2 - δ * b ^ 2 := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨a, b, hab⟩ := hn
  refine ⟨a * s / x, b * s / x, ?_⟩
  field_simp
  linear_combination x * hs + s ^ 2 * hab

theorem mem_normSub_real_of_pos {F : Type} [Field F] (σ : F →+* ℝ) (δ : F) (x : Fˣ)
    (h : 0 < σ (x : F)) : x ∈ normSub σ δ :=
  ⟨Real.sqrt (σ (x : F)), 0, by rw [Real.sq_sqrt h.le]; ring⟩

theorem locSq_le_locNorm_of_delta (F : Type) [Field F] [NumberField F] (δ : F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : locSq F S ≤ locNorm F δ S := by
  unfold locSq locNorm finSq
  exact inf_le_inf (iInf_mono fun v => iInf_mono fun _ => sqSub_le_normSub _ _)
    (iInf_mono fun σ => sqSub_le_normSub _ _)

theorem two_pow_le_index_locNorm :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))),
      δ ≠ 0 → (locNorm F δ S).index ≠ 0 ∧
        2 ^ (tFin F δ S + tReal F δ) ≤ (locNorm F δ S).index := by
  intro F _ _ δ S hδ
  classical
  have h0 : (locNorm F δ S).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (GlobalTheory.T.index_unitsLocalSquaresFiniteRealPlaces_le F S).1
      (Subgroup.index_dvd_of_le (locSq_le_locNorm_of_delta F δ S))
  refine ⟨h0, ?_⟩
  set A : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ S ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) δ)} with hA
  set B : Set (F →+* ℝ) := {σ | σ δ < 0} with hB
  have hAf : A.Finite := S.finite_toSet.subset fun v hv => hv.1
  have hBf : B.Finite := Set.toFinite _
  letI : Fintype A := hAf.fintype
  letI : Fintype B := hBf.fintype
  let K : A ⊕ B → Subgroup Fˣ := Sum.elim
    (fun v => normSub (algebraMap F (v.1.adicCompletion F)) δ) (fun σ => normSub σ.1 δ)
  have hle : locNorm F δ S ≤ ⨅ i, K i := by
    refine le_iInf ?_
    rintro (v | σ)
    · exact inf_le_left.trans (iInf₂_le v.1 v.2.1)
    · exact inf_le_right.trans (iInf_le _ σ.1)
  have hdvd := Subgroup.index_dvd_of_le hle
  have hcard : Fintype.card (A ⊕ B) = tFin F δ S + tReal F δ := by
    rw [Fintype.card_sum, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rfl
  rw [← hcard]
  refine le_trans (GlobalTheory.T.two_pow_card_le_index_iInf_of_independent Fˣ (A ⊕ B) K ?_ (ne_zero_of_dvd_ne_zero h0 hdvd))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)
  rintro (v | σ)
  · obtain ⟨y, hy0, hy⟩ := GlobalTheory.T.exists_local_nonnorm_of_nonsquare_adicCompletion F v.1 (algebraMap F _ δ) (by simpa using hδ) v.2.2
    obtain ⟨x, hx0, hxv, hxσ⟩ := GlobalTheory.T.exists_approx_mod_local_squares F S
      (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1 y)
      (fun _ => 1) (by
        intro w
        by_cases hw : w = v.1
        · subst hw; simpa using hy0
        · simp [Function.update_of_ne hw]) (by simp)
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · intro hm
      have h1 := hxv v.1 v.2.1
      rw [Function.update_self] at h1
      exact hy (norm_of_isSquare_mul (by simpa using hx0) h1 hm)
    · rintro (w | τ) hj
      · have hw : w.1 ≠ v.1 := fun h => hj (congrArg Sum.inl (Subtype.ext h))
        have h1 := hxv w.1 w.2.1
        rw [Function.update_of_ne hw, mul_one] at h1
        exact sqSub_le_normSub _ _ h1
      · exact mem_normSub_real_of_pos _ _ _ (by simpa using hxσ τ.1)
  · obtain ⟨x, hx0, hxv, hxσ⟩ := GlobalTheory.T.exists_approx_mod_local_squares F S (fun _ => 1)
      (fun τ => if τ = σ.1 then -1 else 1) (by simp) (by
        intro τ
        split_ifs <;> simp)
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · rintro ⟨a, b, hab⟩
      have h1 := hxσ σ.1
      have h2 : σ.1 δ < 0 := σ.2
      simp only [if_true] at h1
      have h3 : σ.1 x = a ^ 2 - σ.1 δ * b ^ 2 := hab
      nlinarith [sq_nonneg a, mul_nonneg (neg_nonneg.2 h2.le) (sq_nonneg b)]
    · rintro (w | τ) hj
      · have h1 := hxv w.1 w.2.1
        rw [mul_one] at h1
        exact sqSub_le_normSub _ _ h1
      · have hw : τ.1 ≠ σ.1 := fun h => hj (congrArg Sum.inr (Subtype.ext h))
        exact mem_normSub_real_of_pos _ _ _ (by simpa [hw] using hxσ τ.1)

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowLeIndexLocalNormsSqrtExtensionStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension : ∀ (F : Type) [Field F] [NumberField F] (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), δ ≠ 0 → (locNorm F δ S).index ≠ 0 ∧ 2 ^ (tFin F δ S + tReal F δ) ≤ (locNorm F δ S).index := by
  first | exact @GlobalTheory.QNorm.two_pow_le_index_locNorm | exact GlobalTheory.QNorm.two_pow_le_index_locNorm | (intros; apply GlobalTheory.QNorm.two_pow_le_index_locNorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowsSubgroupOfSelfSPow
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem _root_.GlobalTheory.CNorm.pTor_pIdx_sUnits : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F]
    (ζ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p →
    _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) = p ∧
      _root_.GlobalTheory.CNorm.pIdx p (_root_.GlobalTheory.QNorm.sUnits F S) =
        p ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro p F _ _ ζ S hp hζ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Group.FG (_root_.GlobalTheory.QNorm.sUnits F S) := _root_.GlobalTheory.QNorm.sUnits_fg F S
  obtain ⟨-, h2⟩ := _root_.GlobalTheory.CNorm.pIdx_top_of_fg p (_root_.GlobalTheory.QNorm.sUnits F S) hp.pos
  have hroots : ∀ x : Fˣ, x ^ p = 1 → x ∈ _root_.GlobalTheory.QNorm.sUnits F S := by
    intro x hx
    rw [_root_.GlobalTheory.QNorm.mem_sUnits]
    intro v _
    have h := congrArg (fun y : Fˣ => HeightOneSpectrum.valuation F v (y : F)) hx
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h
    exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne_zero).mp h
  have htor : _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) = p := by
    unfold _root_.GlobalTheory.CNorm.pTor
    refine (Nat.card_congr ?_).trans hζ.card_rootsOfUnity
    exact
      { toFun := fun x => ⟨x.1, (mem_rootsOfUnity p x.1).mpr x.2.2⟩
        invFun := fun y => ⟨y.1, hroots y.1 ((mem_rootsOfUnity p y.1).mp y.2),
          (mem_rootsOfUnity p y.1).mp y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have htorTop : _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup (_root_.GlobalTheory.QNorm.sUnits F S)) =
      _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) := by
    unfold _root_.GlobalTheory.CNorm.pTor
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, by rw [← Subgroup.coe_pow, x.2.2, OneMemClass.coe_one]⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subgroup.mem_top _, Subtype.ext y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hidxTop : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (_root_.GlobalTheory.QNorm.sUnits F S)) =
      _root_.GlobalTheory.CNorm.pIdx p (_root_.GlobalTheory.QNorm.sUnits F S) := by
    unfold _root_.GlobalTheory.CNorm.pIdx _root_.GlobalTheory.CNorm.pows
    rw [Subgroup.relIndex_top_right]
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply,
      Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, by rw [← hy]; rfl⟩
    · rintro ⟨y, hyH, hy⟩
      exact ⟨⟨y, hyH⟩, Subtype.ext hy⟩
  refine ⟨htor, ?_⟩
  rw [← hidxTop, h2, htorTop, htor, ← _root_.GlobalTheory.QNorm.sUnits_rank F S, pow_succ]

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRatPolysVanishingOfAutStable
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRatPolysVanishingOfAutStable
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem evC_map_ringEquiv {ι : Type} (σ : ℂ ≃+* ℂ) (f : MvPolynomial (ι × ι) ℂ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (σ : ℂ →+* ℂ) f) g = σ (evC f (g.map σ.symm)) := by
  unfold evC
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp]; simp

theorem evC_map_rat {ι : Type} (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  unfold evC ev
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

theorem mem_span_vanI_of_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ) := by
  intro ι _ _ Γ hΓ f hf
  let W : Submodule ℂ (MvPolynomial (ι × ι) ℂ) :=
    { carrier := {f | ∀ g ∈ Γ, evC f g = 0}
      add_mem' := by
        intro a b ha hb g hg
        have h1 := ha g hg
        have h2 := hb g hg
        unfold evC at *
        rw [map_add (f := _), h1, h2, add_zero]
      zero_mem' := by
        intro g hg
        simp [evC]
      smul_mem' := by
        intro c a ha g hg
        have h1 := ha g hg
        unfold evC at *
        rw [MvPolynomial.smul_eval, h1, mul_zero] }
  have hrepr : ∀ (p : MvPolynomial (ι × ι) ℂ) k,
      (MvPolynomial.basisMonomials (ι × ι) ℂ).repr p k = AddMonoidAlgebra.coeff p k := fun p k => rfl
  have key := GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ) W (by
    intro σ w hw
    refine ⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, ?_, ?_⟩
    · intro g hg
      rw [evC_map_ringEquiv, hw _ (hΓ σ.symm g hg), map_zero]
    · intro k
      rw [hrepr, hrepr, MvPolynomial.coeff_map]
      rfl)
  refine Submodule.span_mono ?_ (key (show f ∈ W from hf))
  rintro w ⟨hw, hq⟩
  have hl : w ∈ Set.range (MvPolynomial.map (σ := ι × ι) (algebraMap ℚ ℂ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    simp only [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hc
    obtain ⟨k, -, rfl⟩ := hc
    obtain ⟨q, hq⟩ := hq k
    exact ⟨q, by rw [← hrepr, hq]; rfl⟩
  obtain ⟨w₀, rfl⟩ := hl
  refine ⟨w₀, ?_, rfl⟩
  intro g hg
  rw [← evC_map_rat]
  exact hw g hg

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRatPolysVanishingOfAutStableStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_ratPolysVanishing_of_autStable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ) := by
  first | exact @GlobalTheory.ClassFin.mem_span_vanI_of_vanish | exact GlobalTheory.ClassFin.mem_span_vanI_of_vanish | (intros; apply GlobalTheory.ClassFin.mem_span_vanI_of_vanish <;> assumption)
end
end
