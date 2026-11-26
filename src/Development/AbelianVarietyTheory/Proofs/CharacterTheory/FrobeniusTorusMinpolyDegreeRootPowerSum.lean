module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] [Finite F]

theorem _root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow (α : AlgebraicClosure F) (m : ℕ) :
    (minpoly F α).natDegree ∣ m ↔ α ^ Nat.card F ^ m = α := by
  rw [(minpoly.irreducible (Algebra.IsIntegral.isIntegral α)).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X,
    minpoly.dvd_iff]
  simp [sub_eq_zero]

theorem _root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range (α : AlgebraicClosure F) :
    ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots =
      (Multiset.range (minpoly F α).natDegree).map fun i => α ^ Nat.card F ^ i := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F)
  have hσ : ∀ (i : ℕ) (x : AlgebraicClosure F), (σ ^ i) x = x ^ Nat.card F ^ i := fun i x => by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Nat.card_eq_fintype_card]
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hne : (minpoly F α).map (algebraMap F (AlgebraicClosure F)) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  have key : ∀ i j, i < j → j < (minpoly F α).natDegree →
      α ^ Nat.card F ^ i = α ^ Nat.card F ^ j → False := by
    intro i j hij hj h
    have hfix : α ^ Nat.card F ^ (j - i) = α := by
      apply (σ ^ i).injective
      rw [hσ, hσ, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
      exact h.symm
    have hdvd := (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α (j - i)).mpr hfix
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hnodup : ((Multiset.range (minpoly F α).natDegree).map
      fun i => α ^ Nat.card F ^ i).Nodup := by
    refine (Multiset.nodup_range _).map_on ?_
    intro i hi j hj hij
    rw [Multiset.mem_range] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj hij).elim
    · exact h
    · exact (key j i h hi hij.symm).elim
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · rw [Multiset.le_iff_subset hnodup]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    rw [mem_roots hne, IsRoot, eval_map_algebraMap, ← hσ, aeval_algHom_apply, minpoly.aeval,
      map_zero]
  · calc ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots.card
        ≤ ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).natDegree := card_roots' _
      _ = (minpoly F α).natDegree := natDegree_map _
      _ = _ := by simp

private theorem sum_range_mul_eq_nsmul_of_periodic {M : Type} [AddCommMonoid M] (f : ℕ → M) (d : ℕ)
    (hf : ∀ i j, f (d * j + i) = f i) (e : ℕ) :
    ∑ i ∈ Finset.range (d * e), f i = e • ∑ i ∈ Finset.range d, f i := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hf i e

theorem _root_.GlobalTheory.CuspGL.torus_minpoly : ∀ (F : Type) [Field F] [Finite F]
    (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n →
    ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
      (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧
        ∀ k : ℕ, _root_.GlobalTheory.CuspGL.rootSum θ k
            (minpoly F α ^ (n / (minpoly F α).natDegree)) =
          ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by
  intro F _ _ θ n hn α hα
  rw [Set.mem_setOf_eq] at hα
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqn : 1 < Nat.card F ^ n := Nat.one_lt_pow (by omega) hq
  have hfix : α ^ Nat.card F ^ n = α := by
    calc α ^ Nat.card F ^ n = α ^ (Nat.card F ^ n - 1) * α := by
          rw [← pow_succ, Nat.sub_add_cancel hqn.le]
      _ = α := by rw [hα, one_mul]
  have hd := (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α n).mpr hfix
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hα
    exact zero_ne_one hα
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  refine ⟨hd, minpoly.coeff_zero_ne_zero hint hα0, fun k => ?_⟩
  obtain ⟨e, he⟩ := hd
  have hdpos : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hint
  have hper : ∀ i j, α ^ Nat.card F ^ ((minpoly F α).natDegree * j + i) =
      α ^ Nat.card F ^ i := fun i j => by
    rw [pow_add, pow_mul,
      (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α _).mp (dvd_mul_right _ _)]
  rw [he, Nat.mul_div_cancel_left e hdpos,
    sum_range_mul_eq_nsmul_of_periodic (fun i => θ (α ^ Nat.card F ^ i) ^ k) _
      (fun i j => by simp only [hper]) e]
  unfold _root_.GlobalTheory.CuspGL.rootSum
  rw [Polynomial.map_pow, roots_pow, _root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range, Multiset.map_nsmul,
    Multiset.sum_nsmul, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSumStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧ ∀ k : ℕ, rootSum θ k (minpoly F α ^ (n / (minpoly F α).natDegree)) = ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by
  first | exact @GlobalTheory.CuspGL.torus_minpoly | exact GlobalTheory.CuspGL.torus_minpoly | (intros; apply GlobalTheory.CuspGL.torus_minpoly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplex
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem matrixChar_iff_isChar : ∀ (G : Type) [Group G] (χ : G → ℂ),
    (∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)) ↔
      IsChar ℂ ℂ χ := by
  intro G _ χ
  constructor
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨n, (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom _).comp ρ), fun g => ?_⟩
    rw [hρ g]
    show _ = Representation.character _ g
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    change _ = (LinearMap.toMatrix' (Matrix.toLin' _)).trace
    rw [LinearMap.toMatrix'_toLin']
    rfl
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨n, Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp ρ.asGroupHom, fun g => ?_⟩
    rw [hρ g]
    show Representation.character _ g = _
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    rfl

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplexStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex : ∀ (G : Type) [Group G] (χ : G → ℂ), (∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)) ↔ IsChar ℂ ℂ χ := by
  first | exact @GlobalTheory.BI.matrixChar_iff_isChar | exact GlobalTheory.BI.matrixChar_iff_isChar | (intros; apply GlobalTheory.BI.matrixChar_iff_isChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteField
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteField
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL.TeichEmb

open Polynomial IntermediateField in
private theorem exists_pow_eq_one_algebraicClosure_of_finite (F : Type) [Field F] [Finite F]
    (x : AlgebraicClosure F) (hx : x ≠ 0) : ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  have hfin : FiniteDimensional F F⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : Finite F⟮x⟯ := Module.finite_of_finite F
  have hne : (⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : F⟮x⟯) ≠ 0 := by
    intro h; exact hx (congrArg Subtype.val h)
  obtain ⟨n, hn, hpow⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite (Units.mk0 _ hne))
  refine ⟨n, hn, ?_⟩
  have := congrArg (fun u : (F⟮x⟯)ˣ => ((u : F⟮x⟯) : AlgebraicClosure F)) hpow
  simpa using this

open Polynomial IntermediateField in
theorem _root_.GlobalTheory.CuspGL.TeichEmb.exists_teichmuller :
    ∀ (F : Type) [Field F] [Finite F], ∃ θ : AlgebraicClosure F →* ℂ,
      ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y := by
  intro F _ _
  set p := ringChar F
  have : Fact p.Prime :=
    ⟨(CharP.char_is_prime_or_zero F p).resolve_right (CharP.char_ne_zero_of_finite F p)⟩
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have : PerfectRing (AlgebraicClosure F) p := inferInstance
  let W := WittVector p (AlgebraicClosure F)
  have : IsDomain W := inferInstance
  letI : Algebra (ZMod p) (AlgebraicClosure F) := ZMod.algebra _ p
  have hW : CharZero W := by
    let f : ℤ_[p] →+* W := (WittVector.map (algebraMap (ZMod p) (AlgebraicClosure F))).comp
      (WittVector.equiv p).symm.toRingHom
    have hf : Function.Injective f :=
      (WittVector.map_injective _ (algebraMap (ZMod p) (AlgebraicClosure F)).injective).comp
        (WittVector.equiv p).symm.injective
    exact (RingHom.charZero_iff hf).mp inferInstance
  let Ω := AlgebraicClosure (FractionRing W)
  have : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  have : CharZero Ω := inferInstance
  let g : W →+* Ω := (algebraMap (FractionRing W) Ω).comp (algebraMap W (FractionRing W))
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))
  let ι : AlgebraicClosure F →* Ω := (g : W →* Ω).comp (WittVector.teichmuller p)
  have hι : Function.Injective ι := by
    intro x y h
    have h1 : WittVector.teichmuller p x = WittVector.teichmuller p y := hg h
    simpa using congrArg (fun w : W => w.coeff 0) h1
  have hmem : ∀ x, ι x ∈ algebraicClosure ℚ Ω := by
    intro x
    rw [mem_algebraicClosure_iff]
    by_cases hx : x = 0
    · subst hx
      have : ι 0 = 0 := by
        show g (WittVector.teichmuller p 0) = 0
        rw [WittVector.teichmuller_zero, map_zero]
      rw [this]; exact isAlgebraic_zero
    · obtain ⟨n, hn, hpow⟩ := exists_pow_eq_one_algebraicClosure_of_finite F x hx
      refine (IsIntegral.of_pow hn ?_).isAlgebraic
      rw [← map_pow, hpow, map_one]; exact isIntegral_one
  have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ Ω) := algebraicClosure.isAlgebraic ℚ Ω
  let φ : algebraicClosure ℚ Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨{ toFun := fun x => φ ⟨ι x, hmem x⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact (congrArg φ (Subtype.ext (map_one ι) : (⟨ι 1, hmem 1⟩ : algebraicClosure ℚ Ω) = 1)).trans
      (map_one φ)
  · intro x y
    rw [← map_mul]; exact congrArg φ (Subtype.ext (map_mul ι x y))
  · intro x y _ _ h
    exact hι (congrArg Subtype.val (φ.injective h))

end GlobalTheory.CuspGL.TeichEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField : ∀ (F : Type) [Field F] [Finite F], ∃ θ : AlgebraicClosure F →* ℂ, ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y := by
  first | exact @GlobalTheory.CuspGL.TeichEmb.exists_teichmuller | exact GlobalTheory.CuspGL.TeichEmb.exists_teichmuller | (intros; apply GlobalTheory.CuspGL.TeichEmb.exists_teichmuller <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.RegularIffNatDegreeAndExistsEllipticGL
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.RegularIffNatDegreeAndExistsEllipticGL
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem pow_card_pow_eq_iff_natDegree_minpoly_dvd (F : Type) [Field F] [Finite F]
    (α : AlgebraicClosure F) (e : ℕ) :
    α ^ Nat.card F ^ e = α ↔ (minpoly F α).natDegree ∣ e := by
  classical
  have := Fintype.ofFinite F
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have : FiniteDimensional F (IntermediateField.adjoin F {α}) := IntermediateField.adjoin.finiteDimensional hx
  have : Finite (IntermediateField.adjoin F {α}) := Module.finite_of_finite F
  have hgen : ∀ m : ℕ, (FiniteField.frobeniusAlgEquivOfAlgebraic F (IntermediateField.adjoin F {α}) ^ m)
      (IntermediateField.AdjoinSimple.gen F α) =
      IntermediateField.AdjoinSimple.gen F α ^ (Fintype.card F ^ m) := by
    intro m
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [← IntermediateField.adjoin.finrank hx,
    ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F (IntermediateField.adjoin F {α}), orderOf_dvd_iff_pow_eq_one,
    Nat.card_eq_fintype_card]
  constructor
  · intro h
    apply AlgEquiv.coe_toAlgHom_injective
    apply (IntermediateField.adjoin.powerBasis hx).algHom_ext
    rw [IntermediateField.adjoin.powerBasis_gen hx]
    simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.one_apply]
    rw [hgen]
    apply Subtype.ext
    simpa using h
  · intro h
    have key := congrArg (fun f => ((f (IntermediateField.AdjoinSimple.gen F α) : (IntermediateField.adjoin F {α})) :
      AlgebraicClosure F)) h
    simp only [hgen, AlgEquiv.one_apply] at key
    simpa using key

theorem exists_GL_charpoly_eq_minpoly (F K : Type) [Field F] [Field K] [Algebra F K]
    (α : K) (hx : IsIntegral F α) (h0 : α ≠ 0) (n : ℕ) (hn : (minpoly F α).natDegree = n) :
    ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α := by
  subst hn
  have hdim : (IntermediateField.adjoin.powerBasis hx).dim = (minpoly F α).natDegree :=
    IntermediateField.adjoin.powerBasis_dim hx
  have hg : (IntermediateField.adjoin.powerBasis hx).gen ≠ 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen hx]
    intro h
    apply h0
    have := congrArg (algebraMap (IntermediateField.adjoin F {α}) K) h
    simpa using this
  let f : (IntermediateField.adjoin F {α}) →ₐ[F] Matrix (Fin (minpoly F α).natDegree) (Fin (minpoly F α).natDegree) F :=
    (Matrix.reindexAlgEquiv F F (finCongr hdim)).toAlgHom.comp
      (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hx).basis)
  refine ⟨Units.map (f : (IntermediateField.adjoin F {α}) →* Matrix _ _ F) (Units.mk0 _ hg), ?_⟩
  rw [Units.coe_map, Units.val_mk0]
  change (Matrix.reindexAlgEquiv F F (finCongr hdim)
      (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hx).basis
        (IntermediateField.adjoin.powerBasis hx).gen)).charpoly = _
  rw [Matrix.coe_reindexAlgEquiv, Matrix.charpoly_reindex, charpoly_leftMulMatrix,
    IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]

theorem regular_iff_natDegree_and_exists_elliptic :
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((∀ e : ℕ, 0 < e → e < n → α ^ Nat.card F ^ e ≠ α) ↔ (minpoly F α).natDegree = n) ∧ ((minpoly F α).natDegree = n → ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α) := by
  intro F _ _ n hn α hα
  have hα' : α ^ (Nat.card F ^ n - 1) = 1 := hα
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have h0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.sub_ne_zero_of_lt hq)] at hα'
    exact zero_ne_one hα'
  have hfix : α ^ Nat.card F ^ n = α := by
    have hsplit : Nat.card F ^ n = (Nat.card F ^ n - 1) + 1 := (Nat.sub_add_cancel hq.le).symm
    rw [hsplit, pow_succ, hα', one_mul]
  have hdvd := (pow_card_pow_eq_iff_natDegree_minpoly_dvd F α n).1 hfix
  have hdpos : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hx
  refine ⟨⟨fun h => ?_, fun h e he1 he2 heq => ?_⟩,
    fun h => exists_GL_charpoly_eq_minpoly F (AlgebraicClosure F) α hx h0 n h⟩
  · by_contra hne
    have hlt : (minpoly F α).natDegree < n := lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) hne
    exact h _ hdpos hlt ((pow_card_pow_eq_iff_natDegree_minpoly_dvd F α _).2 dvd_rfl)
  · have hd := (pow_card_pow_eq_iff_natDegree_minpoly_dvd F α e).1 heq
    rw [h] at hd
    exact absurd (Nat.le_of_dvd he1 hd) (not_le.2 he2)

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.RegularIffNatDegreeAndExistsEllipticGLStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_iff_natDegree_and_exists_elliptic_GL : ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((∀ e : ℕ, 0 < e → e < n → α ^ Nat.card F ^ e ≠ α) ↔ (minpoly F α).natDegree = n) ∧ ((minpoly F α).natDegree = n → ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α) := by
  first | exact @GlobalTheory.CuspGL.regular_iff_natDegree_and_exists_elliptic | exact GlobalTheory.CuspGL.regular_iff_natDegree_and_exists_elliptic | (intros; apply GlobalTheory.CuspGL.regular_iff_natDegree_and_exists_elliptic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardSubspacesOfFinrankMulCardBases
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardSubspacesOfFinrankMulCardBases
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.SubspaceNumber

theorem card_fibre {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (a : ℕ) (W : Submodule F V) (hW : Module.finrank F W = a) :
    Nat.card {s : {s : Fin a → V // LinearIndependent F s} //
      Submodule.span F (Set.range s.1) = W} = Nat.card {t : Fin a → W // LinearIndependent F t} := by
  symm
  have hspan : ∀ t : Fin a → W, LinearIndependent F t →
      Submodule.span F (Set.range (W.subtype ∘ t)) = W := by
    intro t ht
    have h1 : Submodule.span F (Set.range t) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card ht, Fintype.card_fin, hW]
    rw [Set.range_comp, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_subtype]
  refine Nat.card_congr (Equiv.ofBijective
    (fun t => ⟨⟨W.subtype ∘ t.1, t.2.map' _ W.ker_subtype⟩, hspan t.1 t.2⟩) ⟨?_, ?_⟩)
  · intro t u h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun (congrArg (fun x => x.1.1) h) i
  · rintro ⟨⟨s, hs⟩, h⟩
    have hm : ∀ i, s i ∈ W := fun i => by
      rw [← h]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨⟨fun i => ⟨s i, hm i⟩, LinearIndependent.of_comp W.subtype hs⟩, rfl⟩

theorem card_subspaces_mul :
    ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V →
      Nat.card {W : Submodule F V // Module.finrank F W = a} *
        ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) =
      ∏ i ∈ Finset.range a, (Nat.card F ^ Module.finrank F V - Nat.card F ^ i) := by
  intro F _ _ V _ _ _ a ha
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective
  haveI : Fintype {W : Submodule F V // Module.finrank F W = a} := Fintype.ofFinite _
  let f : {s : Fin a → V // LinearIndependent F s} →
      {W : Submodule F V // Module.finrank F W = a} := fun s =>
    ⟨Submodule.span F (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩
  have hfib : ∀ W, Nat.card {s // f s = W} =
      ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) := by
    rintro ⟨W, hW⟩
    have e : {s // f s = ⟨W, hW⟩} ≃ {s : {s : Fin a → V // LinearIndependent F s} //
      Submodule.span F (Set.range s.1) = W} :=
      Equiv.subtypeEquivRight (fun s => Subtype.ext_iff)
    rw [Nat.card_congr e, card_fibre a W hW, card_linearIndependent hW.ge, hW,
      Finset.prod_range, Nat.card_eq_fintype_card]
  have h := card_linearIndependent (K := F) (V := V) ha
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma] at h
  simp_rw [hfib] at h
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  rw [h, Finset.prod_range]

end GlobalTheory.SubspaceNumber
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardSubspacesOfFinrankMulCardBasesStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → Nat.card {W : Submodule F V // Module.finrank F W = a} * ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) = ∏ i ∈ Finset.range a, (Nat.card F ^ Module.finrank F V - Nat.card F ^ i) := by
  first | exact @GlobalTheory.SubspaceNumber.card_subspaces_mul | exact GlobalTheory.SubspaceNumber.card_subspaces_mul | (intros; apply GlobalTheory.SubspaceNumber.card_subspaces_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradical
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradical
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL.UnipNilRad

variable {F : Type} [Field F]

def lowSub (F : Type) [Field F] (d a : ℕ) : Submodule F (Fin d → F) :=
  LinearMap.ker (LinearMap.funLeft F F (Subtype.val : {i : Fin d // a ≤ i.val} → Fin d))

def unip {d : ℕ} (A : Submodule F (Fin d → F)) : Subgroup (GL (Fin d) F) where
  carrier := {u | Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 ∈ nilRad A}
  one_mem' := by
    refine ⟨fun x => ?_, fun x _ => ?_⟩ <;> simp
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := A.add_mem (hu1 (Matrix.toLin' (v : Matrix (Fin d) (Fin d) F) x)) (hv1 x)
      simpa [Matrix.toLin'_mul] using this
    · have h1 := hu2 x hx
      have h2 := hv2 x hx
      simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1 h2 ⊢
      rw [Units.val_mul, Matrix.toLin'_mul, LinearMap.comp_apply, h2, h1]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have e1 : ∀ x, Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)
        (Matrix.toLin' ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) x) = x := fun x => by
      rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]
    have e2 : ∀ x, Matrix.toLin' ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
        (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) x) = x := fun x => by
      rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := A.neg_mem (hu1 (Matrix.toLin' ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) x))
      rw [LinearMap.sub_apply, e1, neg_sub] at this
      exact this
    · have h1 := hu2 x hx
      simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1 ⊢
      conv_lhs => rw [← h1]
      exact e2 x

private lemma card_fin_le_val_eq_sub (d a : ℕ) : Fintype.card {i : Fin d // a ≤ i.val} = d - a := by
  rw [Fintype.card_subtype, ← Finset.card_map Fin.valEmbedding, ← Nat.card_Ico a d]
  congr 1
  ext n
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, i.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨n, h2⟩, h1, rfl⟩

private lemma finrank_lowSub_of_le {d a : ℕ} (had : a ≤ d) :
    Module.finrank F (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a) = a := by
  have hs := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft F F (Subtype.val : {i : Fin d // a ≤ i.val} → Fin d))
  rw [LinearMap.range_eq_top.mpr
    (LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective),
    finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    card_fin_le_val_eq_sub, Fintype.card_fin] at hs
  rw [_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub]
  omega

private lemma mem_lowSub_iff_apply_eq_zero {d a : ℕ} (v : Fin d → F) :
    v ∈ _root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a ↔ ∀ i : Fin d, a ≤ i.val → v i = 0 := by
  rw [_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub, LinearMap.mem_ker]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.1 i.2

private lemma toLin'_mem_nilRad_lowSub_iff {d a : ℕ} (N : Matrix (Fin d) (Fin d) F) :
    Matrix.toLin' N ∈ _root_.GlobalTheory.CuspGL.nilRad (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a) ↔
      ∀ i j : Fin d, N i j = 0 ∨ (i.val < a ∧ a ≤ j.val) := by
  show ((∀ x, Matrix.toLin' N x ∈ _) ∧ ∀ x ∈ _, Matrix.toLin' N x = 0) ↔ _
  simp only [Matrix.toLin'_apply, mem_lowSub_iff_apply_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩ i j
    by_cases hi : a ≤ i.val
    · left
      have := h1 (Pi.single j 1) i hi
      simpa [Matrix.mulVec_single_one] using this
    by_cases hj : a ≤ j.val
    · exact Or.inr ⟨by omega, hj⟩
    · left
      have hx : ∀ k : Fin d, a ≤ k.val → (Pi.single j (1 : F) : Fin d → F) k = 0 := by
        intro k hk
        have : k ≠ j := fun h => hj (h ▸ hk)
        simp [Pi.single_apply, this]
      have := congrFun (h2 _ hx) i
      simpa [Matrix.mulVec_single_one] using this
  · intro h
    refine ⟨fun x i hi => ?_, fun x hx => ?_⟩
    · rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases h i j with h0 | ⟨hlt, _⟩
      · simp [h0]
      · omega
    · funext i
      rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases h i j with h0 | ⟨_, hj⟩
      · simp [h0]
      · simp [hx j hj]

theorem _root_.GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad :
    ∀ (F : Type) [Field F] [Finite F] (d a : ℕ), a ≤ d → ∃ (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F)), Module.finrank F A = a ∧ (H : Set (GL (Fin d) F)) = {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)} ∧ Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1) (H : Set (GL (Fin d) F)) (_root_.GlobalTheory.CuspGL.nilRad A) := by
  intro F _ _ d a had
  refine ⟨_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a,
    _root_.GlobalTheory.CuspGL.UnipNilRad.unip (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a),
    finrank_lowSub_of_le had, ?_, ?_⟩
  · ext u
    show Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 ∈
      _root_.GlobalTheory.CuspGL.nilRad (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a) ↔ _
    have hsub : Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 =
        Matrix.toLin' ((u : Matrix (Fin d) (Fin d) F) - 1) := by
      rw [map_sub, Matrix.toLin'_one]
      rfl
    rw [hsub, toLin'_mem_nilRad_lowSub_iff, Set.mem_setOf_eq]
    simp only [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
  · refine ⟨fun u hu => hu, fun u _ v _ h => ?_, fun f hf => ?_⟩
    · exact Units.ext (Matrix.toLin'.injective (sub_left_injective h))
    · set N := LinearMap.toMatrix' f with hNdef
      have hNf : Matrix.toLin' N = f := Matrix.toLin'_toMatrix' f
      have hN : N * N = 0 := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun x => ?_
        rw [Matrix.toLin'_mul, LinearMap.comp_apply, hNf, map_zero, LinearMap.zero_apply]
        exact hf.2 _ (hf.1 x)
      let u : GL (Fin d) F := ⟨1 + N, 1 - N, by noncomm_ring; rw [hN]; simp,
        by noncomm_ring; rw [hN]; simp⟩
      have hu : Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 = f := by
        show Matrix.toLin' (1 + N) - 1 = f
        rw [map_add (f := _), Matrix.toLin'_one, hNf]
        exact add_sub_cancel_left (1 : Module.End F (Fin d → F)) f
      refine ⟨u, ?_, hu⟩
      show Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 ∈
        _root_.GlobalTheory.CuspGL.nilRad (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a)
      rw [hu]
      exact hf

end GlobalTheory.CuspGL.UnipNilRad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradicalStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical : ∀ (F : Type) [Field F] [Finite F] (d a : ℕ), a ≤ d → ∃ (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F)), Module.finrank F A = a ∧ (H : Set (GL (Fin d) F)) = {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)} ∧ Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1) (H : Set (GL (Fin d) F)) (nilRad A) := by
  first | exact @GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad | exact GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad | (intros; apply GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterExtendScalarsRep
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

def extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type} [Group G] {n : ℕ}
    (ρ : Representation K G (Fin n → K)) : Representation L G (Fin n → L) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L))
  map_one' := by
    rw [map_one, LinearMap.toMatrix'_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

theorem character_extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type}
    [Group G] {n : ℕ} (ρ : Representation K G (Fin n → K)) (g : G) :
    (extendScalarsRep K L ρ).character g = algebraMap K L (ρ.character g) := by
  have h1 : (extendScalarsRep K L ρ).character g
      = ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L)).trace := by
    change LinearMap.trace L _ (Matrix.toLin' _) = _
    exact Matrix.trace_toLin'_eq _
  have h2 : ρ.character g = (LinearMap.toMatrix' (ρ g)).trace := by
    change LinearMap.trace K _ (ρ g) = _
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  rw [h1, h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

theorem isChar_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G]
    (χ : G → L), IsChar K L χ → IsChar L L χ := by
  intro K L _ _ _ G _ χ ⟨n, ρ, h⟩
  refine ⟨n, extendScalarsRep K L ρ, fun g => ?_⟩
  rw [h g, character_extendScalarsRep]
  rfl

end GlobalTheory.BI
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldZeroAndAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldZeroAndAdd
open GlobalTheory.BI
namespace GlobalTheory.BI

private theorem exists_representation_character_eq_add (K : Type) [Field K] (G : Type) [Group G]
    (n m : ℕ) (ρ : Representation K G (Fin n → K)) (σ : Representation K G (Fin m → K)) :
    ∃ τ : Representation K G (Fin (n + m) → K),
      ∀ g, τ.character g = ρ.character g + σ.character g := by
  let e : ((Fin n → K) × (Fin m → K)) ≃ₗ[K] (Fin (n + m) → K) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) K K).symm ≪≫ₗ
      LinearEquiv.funCongrLeft K K finSumFinEquiv.symm
  refine ⟨{ toFun := fun g => e.conj ((ρ g).prodMap (σ g)), map_one' := ?_, map_mul' := ?_ },
    fun g => ?_⟩
  · simp only [map_one, LinearMap.prodMap_one]
    exact e.conj_id
  · intro g h
    simp only [map_mul]
    rw [← LinearMap.prodMap_mul]
    exact e.conj_comp _ _
  · simp only [Representation.character]
    show LinearMap.trace K _ (e.conj _) = _
    rw [LinearMap.trace_conj', LinearMap.trace_prodMap']

theorem _root_.GlobalTheory.BI.isChar_zero_and_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    (G : Type) [Group G], _root_.GlobalTheory.BI.IsChar K L (0 : G → L) ∧
      ∀ a b : G → L, _root_.GlobalTheory.BI.IsChar K L a → _root_.GlobalTheory.BI.IsChar K L b →
        _root_.GlobalTheory.BI.IsChar K L (a + b) := by
  intro K L _ _ _ G _
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.BI.IsChar
    refine ⟨0, 1, fun g => ?_⟩
    simp [Representation.character]
  · intro a b ha hb
    unfold _root_.GlobalTheory.BI.IsChar at ha hb ⊢
    obtain ⟨n, ρ, hρ⟩ := ha
    obtain ⟨m, σ, hσ⟩ := hb
    obtain ⟨τ, hτ⟩ := exists_representation_character_eq_add K G n m ρ σ
    refine ⟨n + m, τ, fun g => ?_⟩
    rw [Pi.add_apply, hρ g, hσ g, hτ g, map_add (f := _)]

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldZeroAndAddStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_zero_and_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G], IsChar K L (0 : G → L) ∧ ∀ a b : G → L, IsChar K L a → IsChar K L b → IsChar K L (a + b) := by
  first | exact @GlobalTheory.BI.isChar_zero_and_add | exact GlobalTheory.BI.isChar_zero_and_add | (intros; apply GlobalTheory.BI.isChar_zero_and_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterCosetSumEqZeroOfSubgroupSum
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterCosetSumEqZeroOfSubgroupSum
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.char_coset_sum_eq_zero :
    ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ χ → ∀ H : Subgroup G,
      ∑ᶠ u : H, χ u = 0 → ∀ g : G, ∑ᶠ u : H, χ (g * u) = 0 := by
  intro G _ _ χ hχc H hH g
  obtain ⟨n, ρ, hρ⟩ := hχc
  have := Fintype.ofFinite H
  have hχ : ∀ x, χ x = LinearMap.trace ℂ _ (ρ x) := fun x => by
    simp [hρ, Representation.character]
  rw [finsum_eq_sum_of_fintype] at hH ⊢
  simp only [hχ] at hH ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum] at hH
  set S : Module.End ℂ (Fin n → ℂ) := ∑ u : H, ρ u with hS
  have habs : ∀ v : H, ρ v * S = S := by
    intro v
    rw [hS, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun u => ?_)
    simp [map_mul]
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hSS : S * S = (Fintype.card H : ℂ) • S := by
    conv_lhs => arg 1; rw [hS]
    rw [Finset.sum_mul]
    simp only [habs, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hidem : IsIdempotentElem ((Fintype.card H : ℂ)⁻¹ • S) := by
    unfold IsIdempotentElem
    rw [smul_mul_smul, hSS, smul_smul]
    congr 1
    field_simp
  have hP : (Fintype.card H : ℂ)⁻¹ • S = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff hidem).1 (by rw [map_smul, hH, smul_zero])
  have hS0 : S = 0 := by simpa [hcard] using hP
  have hsum : ∑ u : H, LinearMap.trace ℂ _ (ρ (g * u)) = LinearMap.trace ℂ _ (ρ g * S) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    simp [map_mul]
  rw [hsum, hS0, mul_zero, map_zero]

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterCosetSumEqZeroOfSubgroupSumStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_coset_sum_eq_zero_of_subgroup_sum : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), IsChar ℂ ℂ χ → ∀ H : Subgroup G, ∑ᶠ u : H, χ u = 0 → ∀ g : G, ∑ᶠ u : H, χ (g * u) = 0 := by
  first | exact @GlobalTheory.BI.char_coset_sum_eq_zero | exact GlobalTheory.BI.char_coset_sum_eq_zero | (intros; apply GlobalTheory.BI.char_coset_sum_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingAddNatPosSymm
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingAddNatPosSymm
open GlobalTheory.BI
namespace GlobalTheory.BI

private theorem character_pairing_eq_finrank_hom (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K]
    (G : Type) [Group G] [Finite G] {n m : ℕ} (ρ : Representation K G (Fin n → K))
    (σ : Representation K G (Fin m → K)) :
    pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g))
      = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hK := congrArg (algebraMap K L)
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ)
  rw [map_natCast] at hK
  rw [← hK]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pair, finsum_eq_sum_of_fintype, map_mul, map_inv₀, map_natCast, map_sum]

theorem pair_add_nat_pos_symm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ a b c : G → L, pair (a + b) c = pair a c + pair b c) ∧ (∀ a b : G → L, IsChar K L a → IsChar K L b → ∃ n : ℕ, pair a b = (n : L)) ∧ (∀ φ : G → L, IsIrrChar K L φ → ∃ n : ℕ, 0 < n ∧ pair φ φ = (n : L)) ∧ ∀ a b : G → L, pair a b = pair b a := by
  intro K L _ _ _ _ _ G _ _
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c
    simp only [pair, finsum_eq_sum_of_fintype, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      mul_add]
  · rintro a b ⟨n, ρ, hρ⟩ ⟨m, σ, hσ⟩
    refine ⟨Module.finrank K (Representation.IntertwiningMap σ ρ), ?_⟩
    rw [show a = fun g => algebraMap K L (ρ.character g) from funext hρ,
      show b = fun g => algebraMap K L (σ.character g) from funext hσ]
    exact character_pairing_eq_finrank_hom K L G σ ρ
  · rintro φ ⟨n, ρ, hirr, hρ⟩
    refine ⟨Module.finrank K (Representation.IntertwiningMap ρ ρ), ?_, ?_⟩
    · have : IsSimpleModule (MonoidAlgebra K G) ρ.asModule :=
        (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
      have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra K G) _
      obtain ⟨v, hv⟩ : ∃ v : Fin n → K, v ≠ 0 := exists_ne (0 : ρ.asModule)
      have : Nontrivial (Representation.IntertwiningMap ρ ρ) :=
        ⟨⟨Representation.IntertwiningMap.id ρ, 0, fun h => hv (by
          have hv0 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) h
          rwa [Representation.IntertwiningMap.id_apply, Representation.IntertwiningMap.coe_zero,
            Pi.zero_apply] at hv0)⟩⟩
      have : Module.Finite K (Representation.IntertwiningMap ρ ρ) :=
        Module.Finite.equiv (Representation.invariantsEquivIntertwiningMap ρ ρ)
      exact Module.finrank_pos
    · rw [show φ = fun g => algebraMap K L (ρ.character g) from funext hρ]
      exact character_pairing_eq_finrank_hom K L G ρ ρ
  · intro a b
    simp only [pair, finsum_eq_sum_of_fintype]
    congr 1
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by simp [mul_comm])
end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingAddNatPosSymmStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ a b c : G → L, pair (a + b) c = pair a c + pair b c) ∧ (∀ a b : G → L, IsChar K L a → IsChar K L b → ∃ n : ℕ, pair a b = (n : L)) ∧ (∀ φ : G → L, IsIrrChar K L φ → ∃ n : ℕ, 0 < n ∧ pair φ φ = (n : L)) ∧ ∀ a b : G → L, pair a b = pair b a := by
  first | exact @GlobalTheory.BI.pair_add_nat_pos_symm | exact GlobalTheory.BI.pair_add_nat_pos_symm | (intros; apply GlobalTheory.BI.pair_add_nat_pos_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IndMulClassFunEqIndMulRestrict
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

theorem ind_mul_classFun_eq_ind_mul_restrict :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → ℂ) (φ : G → ℂ),
      (∀ g x : G, φ (x⁻¹ * g * x) = φ g) → ind H ψ * φ = ind H (fun h => ψ h * φ h) := by
  intro G _ _ H ψ φ hφ
  funext g
  have key : ∀ x : G, ext0 H (fun h => ψ h * φ h) (x⁻¹ * g * x) = ext0 H ψ (x⁻¹ * g * x) * φ g := by
    intro x
    rw [← hφ g x]
    simp [ext0]
  simp only [Pi.mul_apply, ind]
  simp_rw [key]
  rw [mul_assoc, finsum_mul]

end GlobalTheory.BI
end
