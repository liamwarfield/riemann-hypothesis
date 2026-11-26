module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatio
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory

open TensorProduct

theorem tensor_padic_cls_eq {G : Type} [CommGroup G] (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : G)
    (h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul f' - (1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul f) ∈
      ((Ideal.span {(l : ℤ_[l])}) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] Additive G)))) :
    ∃ u : G, f' = f * u ^ (l ^ n) := by
  classical
  let M := Additive G
  let ψ : M →ₗ[ℤ] M := {
    toFun := fun x : M => (((l : ℤ) ^ n) • x)
    map_add' := fun x y => by simp
    map_smul' := fun (k : ℤ) x => by simp [smul_smul, mul_comm]
  }
  let P : Submodule ℤ M := LinearMap.range ψ
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hkill : ∀ q : M ⧸ P, (l ^ n) • q = 0 := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨m, by change ((l : ℤ) ^ n) • m = l ^ n • m; rw [← Nat.cast_pow, natCast_zsmul]⟩
  letI : Module (ZMod (l ^ n)) (M ⧸ P) := AddCommGroup.zmodModule hkill
  let B : ℤ_[l] →ₗ[ℤ] M →ₗ[ℤ] M ⧸ P :=
    LinearMap.mk₂ ℤ (fun c m => (PadicInt.toZModPow n c) • P.mkQ m)
      (fun c c' m => by simp [add_smul])
      (fun k c m => by
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)), ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)),
          smul_smul, smul_eq_mul])
      (fun c m m' => by simp [smul_add])
      (fun k c m => by
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)), ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)),
          smul_smul, smul_smul, mul_comm])
  let φ : ℤ_[l] ⊗[ℤ] M →ₗ[ℤ] M ⧸ P := TensorProduct.lift B
  have hφ : ∀ c m, φ (c ⊗ₜ m) = (PadicInt.toZModPow n c) • P.mkQ m := fun c m => by
    exact TensorProduct.lift.tmul (f' := B) c m
  have hI : (Ideal.span {(l : ℤ_[l])}) ^ n = RingHom.ker (PadicInt.toZModPow (p := l) n) := by
    rw [PadicInt.ker_toZModPow, Ideal.span_singleton_pow]
  have hzero : ∀ x ∈ ((Ideal.span {(l : ℤ_[l])}) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] M))), φ x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero])
    rw [hI, RingHom.mem_ker] at hr
    clear hy
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, hφ, map_mul, hr, zero_mul, zero_smul]
    | add a b ha hb => rw [smul_add, map_add (f := _), ha, hb, add_zero]
  have h0 := hzero _ h
  rw [map_sub, hφ, hφ, map_one, one_smul, one_smul, sub_eq_zero, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq] at h0
  obtain ⟨y, hy⟩ := h0
  refine ⟨Additive.toMul y, ?_⟩
  have hy' : Additive.toMul (((l : ℤ) ^ n) • y) = f' / f := by
    have hy2 : ((l : ℤ) ^ n) • y = Additive.ofMul f' - Additive.ofMul f := hy
    rw [hy2]; rfl
  rw [toMul_zsmul] at hy'
  rw [← div_eq_iff_eq_mul', ← hy']
  norm_cast

theorem Tower.cls_eq_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (f f' : X.Kˣ) (h : X.cls l n f = X.cls l n f') :
    ∃ u : X.Kˣ, (f' : X.K) = f * (u : X.K) ^ (l ^ n) := by
  unfold Tower.cls at h
  rw [Submodule.Quotient.eq'] at h
  obtain ⟨u, hu⟩ := tensor_padic_cls_eq l n f f' (by simpa [neg_add_eq_sub] using h)
  exact ⟨u, by rw [hu]; push_cast; rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatioStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_class_eq_imp_pow_ratio : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : X.Kˣ), X.cls l n f = X.cls l n f' → ∃ u : X.Kˣ, (f' : X.K) = f * (u : X.K) ^ (l ^ n) := by
  first | exact @GlobalTheory.Tower.cls_eq_pow | exact GlobalTheory.Tower.cls_eq_pow | (intros; apply GlobalTheory.Tower.cls_eq_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLaws
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.SlPLaws
open MvPolynomial

variable {R : Type} [CommRing R]

theorem slP_X (m : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    slP (R := R) m (X i) = (m i 0 : R) • X 0 + (m i 1 : R) • X 1 := by
  simp [slP]

theorem polySlash_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    slP (m * m') p = slP m' (slP m p) := by
  have h : (slP (R := R) (m * m')) = (slP m').comp (slP m) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, slP_X, map_add (f := _), map_smul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    simp only [smul_add, add_smul, smul_smul, mul_comm]
    abel
  rw [h]; rfl

theorem polySlash_one' (p : MvPolynomial (Fin 2) R) : slP 1 p = p := by
  have h : (slP (R := R) 1) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [slP_X]
  rw [h]; rfl

theorem polySlash_isHomogeneous (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R)
    (hp : p.IsHomogeneous w) : (slP m p).IsHomogeneous w := by
  have := IsHomogeneous.aeval (τ := Fin 2) (S := R) (n := 1) hp (fun i => (m i 0 : R) • X 0 + (m i 1 : R) • X 1) (fun i => by
    apply IsHomogeneous.add
    · rw [smul_eq_C_mul]; exact (isHomogeneous_X R 0).C_mul _
    · rw [smul_eq_C_mul]; exact (isHomogeneous_X R 1).C_mul _)
  rw [one_mul] at this
  simpa [slP] using this

theorem eval_slP (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    eval u (slP m p) = eval (m.map (Int.castRingHom R) *ᵥ u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, eval_X]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem map_slP {S : Type} [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, map_X, map_add (f := _)]
    simp [MvPolynomial.smul_eq_C_mul]

theorem polySlash_congr (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R)
    (h : ∀ i j, (m i j : R) = (m' i j : R)) : slP m p = slP m' p := by
  simp only [slP, h]

theorem polySlash_neg_one (w : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p.IsHomogeneous w) :
    slP (-1) p = (-1 : R) ^ w • p := by
  have e : (slP (R := R) (-1)) = aeval fun i => (-1 : R) • X i := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [slP_X]
  rw [e]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hw := hp (mem_support_iff.mp hv)
  rw [aeval_monomial]
  simp only [smul_pow, Finsupp.prod_pow]
  have hw' : v 0 + v 1 = w := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]; simp
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, ← hw']
  simp only [smul_eq_C_mul, algebraMap_eq, pow_add, map_mul, map_pow, map_neg, map_one]
  ring

end GlobalTheory.KZ.SlPLaws

namespace GlobalTheory.KZ

theorem polySlash_laws : ∀ (R : Type) [CommRing R], (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), slP (m * m') p = slP m' (slP m p)) ∧ (∀ p : MvPolynomial (Fin 2) R, slP 1 p = p) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → (slP m p).IsHomogeneous w) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R), MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p)) ∧ (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), (∀ i j, (m i j : R) = (m' i j : R)) → slP m p = slP m' p) ∧ (∀ (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → slP (-1) p = (-1 : R) ^ w • p) := by
  intro R _
  exact ⟨SlPLaws.polySlash_mul, SlPLaws.polySlash_one', SlPLaws.polySlash_isHomogeneous, SlPLaws.eval_slP, fun S _ f => SlPLaws.map_slP f,
    fun m m' p h => SlPLaws.polySlash_congr m m' p h, fun w p hp => SlPLaws.polySlash_neg_one w p hp⟩

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoVarPolySubstMatrix_basic_laws : ∀ (R : Type) [CommRing R], (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), slP (m * m') p = slP m' (slP m p)) ∧ (∀ p : MvPolynomial (Fin 2) R, slP 1 p = p) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → (slP m p).IsHomogeneous w) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R), MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p)) ∧ (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), (∀ i j, (m i j : R) = (m' i j : R)) → slP m p = slP m' p) ∧ (∀ (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → slP (-1) p = (-1 : R) ^ w • p) := by
  first | exact @GlobalTheory.KZ.polySlash_laws | exact GlobalTheory.KZ.polySlash_laws | (intros; apply GlobalTheory.KZ.polySlash_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumSubgroupCharacterProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumSubgroupCharacterProperties
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.LevGroup

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

theorem isUp_one : IsUp g N 1 :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne']⟩

theorem isUp_mul {u v : GG g N} (hu : IsUp g N u) (hv : IsUp g N v) : IsUp g N (u * v) := by
  refine ⟨fun a => ?_, fun a c h => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hu.1, hv.1, mul_one]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hu.2 a b h, zero_mul]
      · rw [hv.2 b a h, mul_zero]
    · simp
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases lt_or_ge b a with h' | h'
    · rw [hu.2 a b h', zero_mul]
    · rw [hv.2 b c (lt_of_lt_of_le h h'), mul_zero]

theorem mul_entry {u v : GG g N} (hu : IsUp g N u) (hv : IsUp g N v) {a c : Fin N} (hac : a < c)
    (h : ∀ b, a < b → b < c → u.val a b * v.val b c = 0) : (u * v).val a c = u.val a c + v.val a c := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a c (Finset.mem_univ _) (Finset.mem_univ _) hac.ne]
  · rw [hu.1, hv.1, one_mul, mul_one, add_comm]
  · rintro b _ ⟨h1, h2⟩
    rcases lt_or_gt_of_ne h1 with h1 | h1
    · rw [hu.2 a b h1, zero_mul]
    rcases lt_or_gt_of_ne h2 with h2 | h2
    · exact h b h1 h2
    · rw [hv.2 b c h2, mul_zero]

theorem isNilpotent_of_isUp {u : GG g N} (hu : IsUp g N u) : IsNilpotent (u.val - 1) := by
  have ht : (u.val - 1).BlockTriangular id := by
    intro a b h
    have h' : b < a := h
    simp [Matrix.sub_apply, hu.2 a b h', Matrix.one_apply_ne h'.ne']
  have hc := Matrix.aeval_self_charpoly (u.val - 1)
  rw [Matrix.charpoly_of_upperTriangular _ ht] at hc
  refine ⟨N, ?_⟩
  simpa [Matrix.sub_apply, hu.1] using hc

theorem edge_lt (L : Lev g N) {a b : Fin N} (h : L.Edge a b) : a < b := by
  unfold Lev.Edge at h
  rw [Fin.lt_def]
  split_ifs at h <;> omega

theorem mem_one (L : Lev g N) : L.Mem 1 := by
  refine ⟨isUp_one, fun _ a b _ h2 h3 => ?_⟩
  have : a ≠ b := fun h => by subst h; omega
  simp [Matrix.one_apply_ne this]

theorem mem_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) : L.Mem (u * v) := by
  refine ⟨isUp_mul hu.1 hv.1, fun hs a c h1 h2 h3 => ?_⟩
  rw [mul_entry hu.1 hv.1 (by rw [Fin.lt_def]; omega), hu.2 hs a c h1 h2 h3, hv.2 hs a c h1 h2 h3, add_zero]
  intro b hb hc
  rw [Fin.lt_def] at hb hc
  rw [hv.2 hs b c (by omega) (by omega) h3, mul_zero]

theorem edge_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) {a c : Fin N} (h : L.Edge a c) :
    (u * v).val a c = u.val a c + v.val a c := by
  refine mul_entry hu.1 hv.1 (edge_lt L h) fun b hb hc => ?_
  rw [Fin.lt_def] at hb hc
  unfold Lev.Edge at h
  split_ifs at h with hs
  · rcases h with h | h
    · omega
    · rw [hv.2 hs b c (by omega) (by omega) h.2, mul_zero]
  · omega

theorem chi_one (L : Lev g N) : L.chi 1 = 1 := by
  unfold Lev.chi
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one]
  refine fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · simp [Matrix.one_apply_ne (edge_lt L h).ne]
  · rfl

theorem chi_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) : L.chi (u * v) = L.chi u * L.chi v := by
  unfold Lev.chi
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [edge_mul L hu hv h, mul_add]
  · simp

theorem lev_group : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, L.Mem 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.Mem (u * v)) ∧ L.chi 1 = 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.chi (u * v) = L.chi u * L.chi v) ∧ ∀ u, L.Mem u → IsNilpotent (u.val - 1) :=
  fun _ _ _ L => ⟨mem_one L, fun _ _ => mem_mul L, chi_one L, fun _ _ => chi_mul L, fun _ hu => isNilpotent_of_isUp hu.1⟩

end GlobalTheory.BadShare.LevGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumSubgroupCharacterPropertiesStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, L.Mem 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.Mem (u * v)) ∧ L.chi 1 = 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.chi (u * v) = L.chi u * L.chi v) ∧ ∀ u, L.Mem u → IsNilpotent (u.val - 1) := by
  first | exact @GlobalTheory.BadShare.LevGroup.lev_group | exact GlobalTheory.BadShare.LevGroup.lev_group | (intros; apply GlobalTheory.BadShare.LevGroup.lev_group <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariant
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.TInv

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue

theorem const_of_pow_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {L : ℕ} (hL : 0 < L) {x : X.K} (hx : x ^ L = 1) : ∃ c : Ω, algebraMap Ω X.K c = x := by
  have hint : IsIntegral Ω x := IsIntegral.of_pow hL (by rw [hx]; exact isIntegral_one)
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one (hx := hdeg))
  exact ⟨c, hc⟩

theorem cast_eq_of_dvd {d : ℕ} {y c : ℤ} (h : (d : ℤ) ∣ y - c) : (y : ZMod d) = (c : ZMod d) := ((ZMod.intCast_eq_intCast_iff_dvd_sub c y d).mpr h).symm

theorem exists_sl2_scalar_mod_coprime (A₁ A₂ : ℕ) (hcop : Nat.Coprime A₁ A₂) :
    ∃ δ : SL(2, ℤ), (A₁ : ℤ) ∣ δ 0 0 - 1 ∧ (A₁ : ℤ) ∣ δ 1 1 - 1 ∧ ((A₁ : ℤ) * A₂) ∣ δ 1 0 ∧
      ((A₁ : ℤ) * A₂) ∣ δ 0 1 ∧ (A₂ : ℤ) ∣ δ 0 0 + 1 ∧ (A₂ : ℤ) ∣ δ 1 1 + 1 ∧ ((A₁ : ℤ) * A₂) ∣ δ 0 0 - δ 1 1 := by
  obtain ⟨u, v, huv⟩ : IsCoprime ((A₁ : ℤ) ^ 2) ((A₂ : ℤ) ^ 2) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).pow
  refine ⟨⟨!![v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2, (A₁ : ℤ) * A₂;
      -4 * u * v * ((A₁ : ℤ) * A₂), v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2], ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination (u * (A₁ : ℤ) ^ 2 + v * (A₂ : ℤ) ^ 2 + 1) * huv
  · exact ⟨-2 * u * A₁, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - 1 = _
      linear_combination huv⟩
  · exact ⟨-2 * u * A₁, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - 1 = _
      linear_combination huv⟩
  · exact ⟨-4 * u * v, by
      show -4 * u * v * ((A₁ : ℤ) * A₂) = _
      ring⟩
  · exact ⟨1, by
      show (A₁ : ℤ) * A₂ = _
      ring⟩
  · exact ⟨2 * v * A₂, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 + 1 = _
      linear_combination (-1 : ℤ) * huv⟩
  · exact ⟨2 * v * A₂, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 + 1 = _
      linear_combination (-1 : ℤ) * huv⟩
  · exact ⟨0, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - (v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2) = _
      ring⟩

private lemma t_inv_mul_mul_t_mul_inv_mem_gamma {M : ℕ} (δ : SL(2, ℤ)) (hc : (M : ℤ) ∣ δ 1 0) (had : (M : ℤ) ∣ δ 0 0 - δ 1 1) :
    ModularGroup.T⁻¹ * δ * ModularGroup.T * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  have hc' : ((δ 1 0 : ℤ) : ZMod M) = 0 := by
    simpa using cast_eq_of_dvd (d := M) (c := 0) (by simpa using hc)
  have had' : ((δ 0 0 : ℤ) : ZMod M) = ((δ 1 1 : ℤ) : ZMod M) := cast_eq_of_dvd had
  rw [CongruenceSubgroup.Gamma_mem', map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
    mul_assoc, inv_mul_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, hc', had'] <;> ring

theorem exists_delta (N M l n : ℕ) (hl : l.Prime) (hlN : ¬ l ∣ N) (hN : 1 ≤ N) (hM : 0 < M) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma1 N ∧ -δ ∈ CongruenceSubgroup.Gamma (l ^ n) ∧
      ModularGroup.T⁻¹ * δ * ModularGroup.T * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  obtain ⟨e, m, hlm, hM'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.one_lt.ne'
  have hcl : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).mpr hlm
  have hcN : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).mpr hlN
  have hcop : Nat.Coprime (N * m) (l ^ (n + e)) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.mul_left hcN.symm hcl.symm)
  obtain ⟨δ, h1, h2, h3, h4, h5, h6, h7⟩ := exists_sl2_scalar_mod_coprime (N * m) (l ^ (n + e)) hcop
  have hN1 : (N : ℤ) ∣ ((N * m : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr (Dvd.intro m rfl)
  have hln : ((l ^ n : ℕ) : ℤ) ∣ ((l ^ (n + e) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (pow_dvd_pow l (Nat.le_add_right n e))
  have hln' : ((l ^ n : ℕ) : ℤ) ∣ ((N * m : ℕ) : ℤ) * ((l ^ (n + e) : ℕ) : ℤ) := Dvd.dvd.mul_left hln _
  have hMd : (M : ℤ) ∣ ((N * m : ℕ) : ℤ) * ((l ^ (n + e) : ℕ) : ℤ) := by
    have : M ∣ (N * m) * l ^ (n + e) := by
      rw [hM']
      exact ⟨N * l ^ n, by ring⟩
    exact_mod_cast this
  refine ⟨δ, ?_, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · simpa using cast_eq_of_dvd (d := N) (dvd_trans hN1 h1)
    · simpa using cast_eq_of_dvd (d := N) (dvd_trans hN1 h2)
    · simpa using cast_eq_of_dvd (d := N) (c := 0) (by rw [sub_zero]; exact dvd_trans (hN1.mul_right _) h3)
  · rw [CongruenceSubgroup.Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 0 0) (c := 1) (by rw [← neg_add']; exact (dvd_trans hln h5).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 0 1) (c := 0) (by rw [sub_zero]; exact (dvd_trans hln' h4).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 1 0) (c := 0) (by rw [sub_zero]; exact (dvd_trans hln' h3).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 1 1) (c := 1) (by rw [← neg_add']; exact (dvd_trans hln h6).neg_right)
  · exact t_inv_mul_mul_t_mul_inv_mem_gamma δ (dvd_trans hMd h3) (dvd_trans hMd h7)

private lemma sl_eq_self_of_pow_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {L : ℕ} (hL : 0 < L) {x : X.K} (hx : x ^ L = 1) (g : GQ) : X.sl g x = x := by
  obtain ⟨c, rfl⟩ := const_of_pow_eq_one X hL hx
  exact (X.sl g).commutes c

theorem sl_T_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l n : ℕ)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hN : 1 ≤ N) (u : X.K) (hu : u ≠ 0)
    (hinv : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (u ^ (l ^ n)))
    (hδ : ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (u * X.sl (ofSL δ) u) ^ (l ^ n) = g ^ (l ^ n)) :
    X.sl (ofSL ModularGroup.T) u = u := by
  have hL : 0 < l ^ n := pow_pos hl.pos n
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (N * l ^ n) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  have huL : u ^ (l ^ n) ≠ 0 := pow_ne_zero _ hu
  obtain ⟨ζ, hTu⟩ : ∃ ζ : X.K, X.sl (ofSL ModularGroup.T) u = ζ * u :=
    ⟨X.sl (ofSL ModularGroup.T) u / u, (div_mul_cancel₀ _ hu).symm⟩
  have hζL : ζ ^ (l ^ n) = 1 := by
    have h1 : X.sl (ofSL ModularGroup.T) (u ^ (l ^ n)) = u ^ (l ^ n) := hinv _ hT
    rw [map_pow, hTu, mul_pow] at h1
    exact mul_right_cancel₀ huL (h1.trans (one_mul _).symm)
  have hζfix : ∀ h : GQ, X.sl h ζ = ζ := fun h => sl_eq_self_of_pow_eq_one X hL hζL h
  obtain ⟨M, hM, hMu⟩ := X.level u
  obtain ⟨δ, hδ1, hδl, hδM⟩ := exists_delta N M l n hl hlN hN hM
  obtain ⟨g, hg, hgL⟩ := hδ δ hδ1 hδl
  have hsu : X.sl (ofSL δ) u ≠ 0 := fun h =>
    hu ((X.sl (ofSL δ)).injective (h.trans (map_zero _).symm))
  have hP0 : u * X.sl (ofSL δ) u ≠ 0 := mul_ne_zero hu hsu
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hL.ne'] at hgL
    exact hP0 ((pow_eq_zero_iff hL.ne').mp hgL)
  have hw : (u * X.sl (ofSL δ) u / g) ^ (l ^ n) = 1 := by
    rw [div_pow, hgL, div_self (pow_ne_zero _ hg0)]
  have hTP : X.sl (ofSL ModularGroup.T) (u * X.sl (ofSL δ) u) = u * X.sl (ofSL δ) u := by
    rw [← div_mul_cancel₀ (u * X.sl (ofSL δ) u) hg0, map_mul, sl_eq_self_of_pow_eq_one X hL hw, hg _ hT]
  obtain ⟨γ, hγ, hγeq⟩ : ∃ γ ∈ CongruenceSubgroup.Gamma M,
      δ * ModularGroup.T = ModularGroup.T * γ * δ := ⟨_, hδM, by group⟩
  have hTδ : X.sl (ofSL ModularGroup.T) (X.sl (ofSL δ) u) = ζ * X.sl (ofSL δ) u := by
    rw [← X.sl_mul, ← map_mul ofSL δ ModularGroup.T, hγeq, map_mul, map_mul, X.sl_mul, X.sl_mul, hTu,
      map_mul (X.sl (ofSL γ)), hζfix, hMu γ hγ, map_mul (X.sl (ofSL δ)), hζfix]
  have hsq : ζ ^ 2 = 1 := by
    have h := hTP
    rw [map_mul, hTu, hTδ] at h
    have h2 : ζ ^ 2 * (u * X.sl (ofSL δ) u) = 1 * (u * X.sl (ofSL δ) u) := by
      linear_combination h
    exact mul_right_cancel₀ hP0 h2
  have hodd : Odd (l ^ n) := (hl.odd_of_ne_two hl2).pow
  obtain ⟨k, hk⟩ := hodd
  have hζ1 : ζ = 1 := by
    have h3 : ζ ^ (l ^ n) = ζ := by rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [← h3, hζL]
  rw [hTu, hζ1, one_mul]

end GlobalTheory.TInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariantStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_rootOfInvariant_T_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l n : ℕ), l.Prime → l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ∀ (u : X.K), u ≠ 0 → Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (u ^ (l ^ n)) → (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) → ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (u * X.sl (ofSL δ) u) ^ (l ^ n) = g ^ (l ^ n)) → X.sl (ofSL ModularGroup.T) u = u := by
  first | exact @GlobalTheory.TInv.sl_T_eq | exact GlobalTheory.TInv.sl_T_eq | (intros; apply GlobalTheory.TInv.sl_T_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoxInvariantSnd
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitDict

section Partial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}

theorem bijOn_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Set.BijOn (fun f : Y → ℂ => f ∘ e) {f | f ∈ SB Y} {f | f ∈ SB X} := by
  refine ⟨fun f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩,
    fun f _ g _ hfg => ?_, fun g hg => ⟨g ∘ e.symm, ⟨hg.1.comp_continuous e.symm.continuous,
      hg.2.comp_homeomorph e.symm⟩, ?_⟩⟩
  · funext y
    simpa using congrFun hfg (e.symm y)
  · funext x
    simp


omit [DecidableEq n] [T2Space T] in
theorem exists_box_invariant_snd {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) :
    ∃ s : kˣ, ∀ u ∈ box n s, ∀ z : T × (n → k), f (z.1, z.2 + u) = f z := by
  obtain ⟨hlc, hcs⟩ := hf
  have hlc2 : IsLocallyConstant fun p : (T × (n → k)) × (n → k) => f (p.1.1, p.1.2 + p.2) - f p.1 :=
    (hlc.comp_continuous (by fun_prop)).sub (hlc.comp_continuous continuous_fst)
  have hW : IsOpen {p : (T × (n → k)) × (n → k) | f (p.1.1, p.1.2 + p.2) - f p.1 = 0} :=
    hlc2.isOpen_fiber 0
  obtain ⟨U, V, -, hV, hKU, h0V, hUV⟩ := generalized_tube_lemma hcs.isCompact (isCompact_singleton (x := (0 : n → k))) hW (by
    rintro ⟨z, u⟩ ⟨-, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    simp [hu])
  obtain ⟨s, hs⟩ := exists_box_subset (hV.mem_nhds (h0V rfl))
  have key : ∀ z ∈ tsupport f, ∀ u ∈ box n s, f (z.1, z.2 + u) = f z := by
    intro z hz u hu
    have hm : (z, u) ∈ {p : (T × (n → k)) × (n → k) | f (p.1.1, p.1.2 + p.2) - f p.1 = 0} :=
      hUV ⟨hKU hz, hs hu⟩
    exact sub_eq_zero.mp hm
  refine ⟨s, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact key z hz u hu
  · by_cases hz' : (z.1, z.2 + u) ∈ tsupport f
    · have hneg : -u ∈ box n s := fun i _ => neg_mem_cball (hu i (Set.mem_univ i))
      have := key _ hz' (-u) hneg
      simp only [add_neg_cancel_right, Prod.mk.eta] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

omit [DecidableEq n] [T2Space T] [Fintype n] in
theorem slice_mem_SB {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (t : T) :
    (fun x => f (t, x)) ∈ SB (n → k) := by
  haveI := t2Space k
  refine ⟨hf.1.comp_continuous (by fun_prop),
    HasCompactSupport.intro (hf.2.isCompact.image continuous_snd) fun x hx => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩

variable [MeasurableSpace k] [BorelSpace k]

def pf (ψ : AddChar k Circle) (μ : Measure (n → k)) (f : T × (n → k) → ℂ) : T × (n → k) → ℂ :=
  fun z => ∫ x, f (z.1, x) * (ψ (x ⬝ᵥ z.2) : ℂ) ∂μ

private theorem exists_isOpen_nhd_eq_of_mem_SB {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (t₀ : T) :
    ∃ V : Set T, IsOpen V ∧ t₀ ∈ V ∧ ∀ t ∈ V, ∀ x, f (t, x) = f (t₀, x) := by
  obtain ⟨hlc, hcs⟩ := hf
  have hW : IsOpen {p : T × (n → k) | f p - f (t₀, p.2) = 0} :=
    (hlc.sub (hlc.comp_continuous (by fun_prop))).isOpen_fiber 0
  obtain ⟨U, V, hU, -, ht₀U, hLV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := t₀))
    (hcs.isCompact.image continuous_snd) hW (by
      rintro ⟨t, x⟩ ⟨ht, -⟩
      simp only [Set.mem_singleton_iff] at ht
      simp [ht])
  refine ⟨U, hU, ht₀U rfl, fun t ht x => ?_⟩
  by_cases hx : x ∈ Prod.snd '' tsupport f
  · have hm : (t, x) ∈ {p : T × (n → k) | f p - f (t₀, p.2) = 0} := hUV ⟨ht, hLV hx⟩
    exact sub_eq_zero.mp hm
  · have h1 : (t, x) ∉ tsupport f := fun h => hx ⟨_, h, rfl⟩
    have h2 : (t₀, x) ∉ tsupport f := fun h => hx ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem pf_mem_SB (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c)
    {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) : pf ψ μ f ∈ SB (T × (n → k)) := by
  obtain ⟨s, hs⟩ := exists_box_invariant_snd hf
  have hslice : ∀ t, (fun y => ∫ x, f (t, x) * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (n → k) :=
    fun t => fourier_mem_SB μ h (slice_mem_SB hf t)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    rintro ⟨t₀, y₀⟩
    obtain ⟨V, hV, ht₀, hVf⟩ := exists_isOpen_nhd_eq_of_mem_SB hf t₀
    obtain ⟨O, hO, hy₀, hOf⟩ := (IsLocallyConstant.iff_exists_open _).mp (hslice t₀).1 y₀
    refine ⟨V ×ˢ O, hV.prod hO, ⟨ht₀, hy₀⟩, ?_⟩
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have e1 : pf ψ μ f (t, y) = pf ψ μ f (t₀, y) := by
      simp only [pf]
      congr 1
      funext x
      rw [hVf t ht x]
    rw [e1]
    exact hOf y hy
  · haveI := t2Space k
    refine HasCompactSupport.intro
      ((hf.2.isCompact.image continuous_fst).prod (isCompact_box (c * s⁻¹))) ?_
    rintro ⟨t, y⟩ hty
    rw [Set.mem_prod, not_and_or] at hty
    rcases hty with ht | hy
    · have h0 : ∀ x, f (t, x) = 0 := fun x =>
        image_eq_zero_of_notMem_tsupport fun hx => ht ⟨_, hx, rfl⟩
      simp [pf, h0]
    · show ∫ x, f (t, x) * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0
      exact fourier_eq_zero_pi μ h (f := fun x => f (t, x)) (fun u hu x => hs u hu (t, x)) hy

theorem inversion_const (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => m)) ∂(Measure.pi fun _ => m) =
      (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  obtain ⟨s, hs⟩ := fourier_inversion_pi (Measure.pi fun _ : n => m) h hf
  have hbox : ∀ r : kˣ, (Measure.pi fun _ : n => m).real (box n r) =
      (nabs k r * m.real (𝒪[k] : Set k)) ^ Fintype.card n := by
    intro r
    have hc := measureReal_cball m r
    simp only [Measure.real] at hc ⊢
    rw [box, Measure.pi_pi, ENNReal.toReal_prod, hc, Finset.prod_const, Finset.card_univ]
  have h1 : nabs k s * nabs k (c * s⁻¹) = nabs k c := by
    rw [nabs_mul k, mul_left_comm, ← nabs_mul k, mul_inv_cancel, nabs_one k, mul_one]
  have h2 : nabs k s * m.real (𝒪[k] : Set k) * (nabs k (c * s⁻¹) * m.real (𝒪[k] : Set k)) =
      m.real (𝒪[k] : Set k) ^ 2 * nabs k c := by
    rw [← h1]; ring
  rw [hs, hbox, hbox, ← mul_pow, h2]

omit [T2Space T] in
theorem pf_pf (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (z : T × (n → k)) :
    pf ψ (Measure.pi fun _ => m) (pf ψ (Measure.pi fun _ => m) f) z =
      (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) * f (z.1, -z.2) := by
  haveI := secondCountable k
  obtain ⟨t, y⟩ := z
  have hsl := slice_mem_SB hf t
  have hg : (fun w => f (t, w - y)) ∈ SB (n → k) :=
    ⟨hsl.1.comp_continuous (continuous_sub_right y), hsl.2.comp_homeomorph (Homeomorph.subRight y)⟩
  have hinv := inversion_const m h hg
  simp only [zero_sub] at hinv
  show ∫ x, (∫ w, f (t, w) * (ψ (w ⬝ᵥ x) : ℂ) ∂(Measure.pi fun _ => m)) * (ψ (x ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => m) = _ * f (t, -y)
  rw [← hinv]
  congr 1
  funext x
  rw [← integral_mul_const]
  have e := integral_sub_right_eq_self (μ := Measure.pi fun _ : n => m)
    (fun u => f (t, u) * (ψ ((u + y) ⬝ᵥ x) : ℂ)) y
  simp only [sub_add_cancel] at e
  rw [e]
  congr 1
  funext u
  rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dotProduct_comm y x]
  ring

theorem pf_bijOn (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c) :
    Set.BijOn (pf ψ (Measure.pi fun _ => m)) {f | f ∈ SB (T × (n → k))} {f | f ∈ SB (T × (n → k))} := by
  haveI := secondCountable k
  set C : ℂ := (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) with hC
  have hC0 : C ≠ 0 := by
    have h1 : 0 < m.real (𝒪[k] : Set k) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos ((isOpen_int k).measure_ne_zero m ⟨0, by simp⟩)
        (isCompact_int k).measure_lt_top.ne
    have h2 := nabs_pos k c
    rw [hC]
    exact Complex.ofReal_ne_zero.mpr (pow_pos (mul_pos (pow_pos h1 2) h2) _).ne'
  have hsmul : ∀ (a : ℂ) (g : T × (n → k) → ℂ), pf ψ (Measure.pi fun _ : n => m) (a • g) = a • pf ψ (Measure.pi fun _ : n => m) g := by
    intro a g
    funext z
    simp only [pf, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul a _
  have hpp : ∀ g ∈ SB (T × (n → k)), ∀ z, pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) g) z = C * g (z.1, -z.2) :=
    fun g hg z => pf_pf m h hg z
  refine ⟨fun g hg => pf_mem_SB (Measure.pi fun _ : n => m) h hg, fun g hg g' hg' hgg => ?_, fun g hg => ?_⟩
  · funext z
    have e1 := hpp g hg (z.1, -z.2)
    have e2 := hpp g' hg' (z.1, -z.2)
    rw [hgg] at e1
    simp only [neg_neg, Prod.mk.eta] at e1 e2
    exact mul_left_cancel₀ hC0 (e1.symm.trans e2)
  · have h2 := pf_mem_SB (Measure.pi fun _ : n => m) h (pf_mem_SB (Measure.pi fun _ : n => m) h hg)
    refine ⟨(C ^ 2)⁻¹ • pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) g)), (SB _).smul_mem _ (pf_mem_SB (Measure.pi fun _ : n => m) h h2), ?_⟩
    rw [hsmul]
    funext z
    rw [Pi.smul_apply, hpp _ h2, hpp _ hg]
    simp only [neg_neg, Prod.mk.eta, smul_eq_mul]
    field_simp

end Partial

section Matrices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable [MeasurableSpace k] [BorelSpace k]

end Matrices

section Homeos

variable (k : Type) [TopologicalSpace k] (ρ v τ w W : Type)

end Homeos

section Main

variable {k : Type} [Field k]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

variable (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w] [Fintype W] [DecidableEq W]



end Main

end GlobalTheory.SplitDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntExponentCongrCyclotomicCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntExponentCongrCyclotomicCharacter
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exists_int_exponent_cyclotomic {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (n M : ℕ) (hM : 0 < M) (hd : l ^ n ∣ M) :
    ∃ e : ℤ, (∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e) ∧
      (e : ℤ_[l]) - (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ∈ (idl l) ^ n := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := algebraRat.charZero Ω
  have : NeZero M := ⟨hM.ne'⟩
  have : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.mpr hM.ne'⟩
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨e, he⟩ := rootsOfUnity.integer_power_of_ringEquiv M s.toRingEquiv
  have hs : ∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e := by
    intro ζ hζ
    have h := he hζ.toRootsOfUnity
    simpa [Units.val_zpow_eq_zpow_val] using h
  refine ⟨e, hs, ?_⟩
  obtain ⟨k, hk⟩ := hd
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hη : IsPrimitiveRoot (ζ ^ k) (l ^ n) := hζ.pow hM (by rw [hk, mul_comm])
  have hsη : s (ζ ^ k) = (ζ ^ k) ^ e := by
    rw [map_pow, hs ζ hζ, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  set c := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hc
  have hpow : (ζ ^ k) ^ (l ^ n) = 1 := hη.pow_eq_one
  have hspec := cyclotomicCharacter.spec (L := Ω) l s.toRingEquiv (ζ ^ k) hpow
  have heq : (ζ ^ k) ^ e = (ζ ^ k) ^ (((cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n).val : ℤ) := by
    rw [← hsη, zpow_natCast]
    exact hspec
  have hdvd : ((l ^ n : ℕ) : ℤ) ∣ e - (((cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n).val : ℤ) := by
    rw [← hη.zpow_eq_one_iff_dvd, zpow_sub₀ (hη.ne_zero (NeZero.ne _)), heq, div_self]
    exact zpow_ne_zero _ (pow_ne_zero _ (hζ.ne_zero (NeZero.ne _)))
  have hz : (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) ((e : ℤ_[l]) - c) = 0 := by
    rw [map_sub, map_intCast, hc]
    rw [sub_eq_zero]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l ^ n)).mpr hdvd
    rw [Int.cast_sub, sub_eq_zero] at this
    rw [this]
    simp
  have hmem : (e : ℤ_[l]) - c ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := hz
  rw [PadicInt.ker_toZModPow, ← Ideal.span_singleton_pow] at hmem
  exact hmem

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntExponentCongrCyclotomicCharacterStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_exponent_congr_cyclotomicCharacter : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (n M : ℕ), 0 < M → l ^ n ∣ M → ∃ e : ℤ, (∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e) ∧ (e : ℤ_[l]) - (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ∈ (idl l) ^ n := by
  first | exact @GlobalTheory.KZ.exists_int_exponent_cyclotomic | exact GlobalTheory.KZ.exists_int_exponent_cyclotomic | (intros; apply GlobalTheory.KZ.exists_int_exponent_cyclotomic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfSlTwoIntInvariantBoundedUpperHalfPlane
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfSlTwoIntInvariantBoundedUpperHalfPlane
open scoped MatrixGroups
open GlobalTheory.KZ

open UpperHalfPlane ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.KZ.LevelOne

theorem const_of_invariant_bounded :
    ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs → (∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) →
      (∃ M t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z‖ ≤ M) → ∃ c : ℂ, ∀ z ∈ Hs, φ z = c := by
  intro φ hd hinv hb
  let f : ℍ → ℂ := fun τ => φ τ
  have hfinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ := fun γ τ => by
    simp only [f]
    rw [← GlobalTheory.KZ.SiegelModel.mob_ofSL]
    exact hinv γ τ τ.2
  have hs (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f := by
    ext τ; simpa [SL_slash_apply] using hfinv γ τ
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine hd.congr fun z hz => ?_
    simp only [Function.comp_apply, f]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hbdd : IsBoundedAtImInfty f := by
    obtain ⟨M, t, h⟩ := hb
    refine isBoundedAtImInfty_iff.2 ⟨M, t + 1, fun τ hτ => ?_⟩
    exact h τ τ.2 (by rw [UpperHalfPlane.coe_im]; linarith [hτ])
  let F : ModularForm 𝒮ℒ 0 :=
    { toFun := f
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
      holo' := hholo
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hs γ]
        exact hbdd }
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  refine ⟨c, fun z hz => ?_⟩
  have := congrFun hc ⟨z, hz⟩
  exact this

end GlobalTheory.KZ.LevelOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfSlTwoIntInvariantBoundedUpperHalfPlaneStatement
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane : ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs → (∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) → (∃ M t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z‖ ≤ M) → ∃ c : ℂ, ∀ z ∈ Hs, φ z = c := by
  first | exact @GlobalTheory.KZ.LevelOne.const_of_invariant_bounded | exact GlobalTheory.KZ.LevelOne.const_of_invariant_bounded | (intros; apply GlobalTheory.KZ.LevelOne.const_of_invariant_bounded <;> assumption)
end
end
