module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.PhiXFinrankRange
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.FiberCard
namespace PI.DensSplitW

def FiberCard : Prop :=
  ∀ (K V U : Type) [Field K] [Fintype K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U), Function.Surjective φ →
    ∀ (k : ℕ) (g : Fin k → U),
      Nat.card {z : Fin k → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} =
        Fintype.card K ^ (Module.finrank K (Submodule.span K (Set.range g)) *
            Module.finrank K (LinearMap.ker φ)) *
          ∏ i ∈ Finset.range (k - Module.finrank K (Submodule.span K (Set.range g))),
            (Fintype.card K ^ Module.finrank K (LinearMap.ker φ) - Fintype.card K ^ i)

end PI.DensSplitW
end

open Finset Formalism.L2.SG.DensExact

namespace PI.DensSplitW

noncomputable def phiX {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (X : Fin m → Fin n → K) : (Fin n → K) →ₗ[K] (Fin m → K) :=
  Matrix.mulVecLin (Matrix.of X * Ph)

theorem phiX_apply {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (X : Fin m → Fin n → K) (y : Fin n → K) (i : Fin m) :
    phiX Ph X y i = ∑ k, ∑ l, X i k * Ph k l * y l := by
  simp only [phiX, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.of_apply]
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem cond_iff {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (Gm : Matrix (Fin m) (Fin m) K) (X Y : Fin m → Fin n → K) :
    (∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j) ↔ ∀ j, phiX Ph X (Y j) = Gm.transpose j := by
  constructor
  · intro h j
    funext i
    rw [phiX_apply, Matrix.transpose_apply]
    exact h i j
  · intro h i j
    have := congrFun (h j) i
    rwa [phiX_apply, Matrix.transpose_apply] at this

theorem phiX_finrank_range {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (hPh : IsUnit Ph.det) (X : Fin m → Fin n → K) (hX : LinearIndependent K X) :
    Module.finrank K (LinearMap.range (phiX Ph X)) = m := by
  have h1 : (Matrix.of X * Ph).rank = m := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det Ph _ hPh, Matrix.rank_eq_finrank_span_row]
    exact (finrank_span_eq_card hX).trans (Fintype.card_fin m)
  exact h1

theorem phiX_surj {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (hPh : IsUnit Ph.det) (X : Fin m → Fin n → K) (hX : LinearIndependent K X) :
    Function.Surjective (phiX Ph X) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [phiX_finrank_range Ph hPh X hX, Module.finrank_fin_fun]

theorem phiX_finrank_ker {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (hPh : IsUnit Ph.det) (X : Fin m → Fin n → K) (hX : LinearIndependent K X) :
    Module.finrank K (LinearMap.ker (phiX Ph X)) = n - m := by
  have h := LinearMap.finrank_range_add_finrank_ker (phiX Ph X)
  rw [phiX_finrank_range Ph hPh X hX, Module.finrank_fin_fun] at h
  omega

theorem count_eq (hF : FiberCard) (K : Type) [Field K] [Fintype K] (n m : ℕ)
    (Ph : Matrix (Fin n) (Fin n) K) (Gm : Matrix (Fin m) (Fin m) K) (hPh : IsUnit Ph.det) :
    countSplit K n m Ph Gm = Nat.card {X : Fin m → Fin n → K // LinearIndependent K X} *
      (Fintype.card K ^ (Gm.rank * (n - m)) *
        ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i)) := by
  classical
  have hfib : ∀ X : {X : Fin m → Fin n → K // LinearIndependent K X},
      Nat.card {Y : Fin m → Fin n → K // LinearIndependent K Y ∧
        ∀ i j, ∑ k, ∑ l, X.1 i k * Ph k l * Y j l = Gm i j} =
      Fintype.card K ^ (Gm.rank * (n - m)) *
        ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i) := by
    intro X
    have e : {Y : Fin m → Fin n → K // LinearIndependent K Y ∧
          ∀ i j, ∑ k, ∑ l, X.1 i k * Ph k l * Y j l = Gm i j} ≃
        {Y : Fin m → Fin n → K // LinearIndependent K Y ∧ ∀ j, phiX Ph X.1 (Y j) = Gm.transpose j} :=
      Equiv.subtypeEquivRight (fun Y => and_congr_right_iff.mpr (fun _ => cond_iff Ph Gm X.1 Y))
    rw [Nat.card_congr e, hF K (Fin n → K) (Fin m → K) (phiX Ph X.1) (phiX_surj Ph hPh X.1 X.2)
      m Gm.transpose, phiX_finrank_ker Ph hPh X.1 X.2]
    have hr : Module.finrank K (Submodule.span K (Set.range (Gm.transpose : Fin m → Fin m → K))) =
        Gm.rank := by
      rw [Matrix.rank_eq_finrank_span_cols]
      rfl
    rw [hr]
  unfold countSplit
  rw [← Nat.card_coe_set_eq]
  have e2 : ↥{XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
        LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j} ≃
      Σ X : {X : Fin m → Fin n → K // LinearIndependent K X},
        {Y : Fin m → Fin n → K // LinearIndependent K Y ∧
          ∀ i j, ∑ k, ∑ l, X.1 i k * Ph k l * Y j l = Gm i j} :=
    { toFun := fun s =>
        have hs : LinearIndependent K s.1.1 ∧ LinearIndependent K s.1.2 ∧
            ∀ i j, ∑ k, ∑ l, s.1.1 i k * Ph k l * s.1.2 j l = Gm i j := s.2
        ⟨⟨s.1.1, hs.1⟩, ⟨s.1.2, hs.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), by exact ⟨s.1.2, s.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e2, Nat.card_sigma, Finset.sum_congr rfl (fun X _ => hfib X),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem sub_factor (q N i : ℕ) (hq : 0 < q) (hi : i ≤ N) :
    ((q ^ N - q ^ i : ℕ) : ℝ) = (q : ℝ) ^ N * (1 - ((q : ℝ) ^ (N - i))⁻¹) := by
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq hi), Nat.cast_pow, Nat.cast_pow]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h : (q : ℝ) ^ N = (q : ℝ) ^ i * (q : ℝ) ^ (N - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  have hne : (q : ℝ) ^ (N - i) ≠ 0 := by positivity
  rw [h]
  field_simp

theorem prod_factor (q b c : ℕ) (hq : 0 < q) (hc : c ≤ b) :
    ((∏ i ∈ range c, (q ^ b - q ^ i) : ℕ) : ℝ) =
      (q : ℝ) ^ (b * c) * ∏ i ∈ range c, (1 - ((q : ℝ) ^ (b - i))⁻¹) := by
  rw [Nat.cast_prod]
  rw [Finset.prod_congr rfl (fun i hi => sub_factor q b i hq
    (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hc)))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]

theorem exp_eq (n m r : ℕ) (hmn : m ≤ n) (hrm : r ≤ m) :
    n * m + r * (n - m) + (n - m) * (m - r) = 2 * n * m - m ^ 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hrm
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  apply (Nat.sub_eq_of_eq_add _).symm
  ring

theorem densExactSplit_of (hF : FiberCard) : DensExactSplit := by
  intro K _ _ n m Ph Gm hPh
  rw [count_eq hF K n m Ph Gm hPh]
  have hrm : Gm.rank ≤ m := Matrix.rank_le_width Gm
  have hq0 : 0 < Fintype.card K := Fintype.card_pos
  have hqR : (0 : ℝ) < Fintype.card K := by exact_mod_cast hq0
  by_cases hmc : m + (m - Gm.rank) ≤ n
  · have hmn : m ≤ n := by omega
    rw [card_linearIndependent (K := K) (V := Fin n → K) (by rw [Module.finrank_fin_fun]; exact hmn),
      Module.finrank_fin_fun]
    rw [← densSplitDisplay_holds (Fintype.card K) n m (m - Gm.rank) hq0 hmc]
    rw [Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ n - Fintype.card K ^ i) m]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
      prod_factor _ n m hq0 hmn, prod_factor _ (n - m) (m - Gm.rank) hq0 (by omega)]
    have hD : (Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2) =
        (Fintype.card K : ℝ) ^ (2 * n * m - m ^ 2) := by
      rw [pow_sub₀ _ hqR.ne' (by nlinarith : m ^ 2 ≤ 2 * n * m), div_eq_mul_inv]
    rw [hD, ← exp_eq n m Gm.rank hmn hrm]
    rw [pow_add, pow_add]
    have h1 : (Fintype.card K : ℝ) ^ (n * m) ≠ 0 := by positivity
    have h2 : (Fintype.card K : ℝ) ^ (Gm.rank * (n - m)) ≠ 0 := by positivity
    have h3 : (Fintype.card K : ℝ) ^ ((n - m) * (m - Gm.rank)) ≠ 0 := by positivity
    field_simp
  · have hR : densProd (Fintype.card K) 1 n m (m - Gm.rank) = 0 := by
      unfold densProd
      apply Finset.prod_eq_zero (i := 0)
      · simp only [Finset.mem_Icc]; omega
      · simp
    rw [hR]
    have hL : Nat.card {X : Fin m → Fin n → K // LinearIndependent K X} *
        (Fintype.card K ^ (Gm.rank * (n - m)) *
          ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i)) = 0 := by
      by_cases hmn : m ≤ n
      · have : ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i) = 0 :=
          Finset.prod_eq_zero (i := n - m) (Finset.mem_range.mpr (by omega)) (by simp)
        rw [this, mul_zero, mul_zero]
      · have : IsEmpty {X : Fin m → Fin n → K // LinearIndependent K X} := by
          refine ⟨fun X => ?_⟩
          have := X.2.fintype_card_le_finrank
          simp only [Fintype.card_fin, Module.finrank_fin_fun] at this
          omega
        rw [Nat.card_of_isEmpty, zero_mul]
    rw [hL]
    simp

end PI.DensSplitW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.CardFibreCompl
open Module Submodule

namespace FibreCount

theorem card_fibre {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U) (a : U) (x0 : V)
    (hx0 : φ x0 = a) :
    Nat.card {x : V // φ x = a} = Fintype.card K ^ finrank K (LinearMap.ker φ) := by
  have e : {x : V // φ x = a} ≃ LinearMap.ker φ :=
    { toFun := fun x => ⟨x.1 - x0, by rw [LinearMap.mem_ker, map_sub, x.2, hx0, sub_self]⟩
      invFun := fun y => ⟨y.1 + x0, by rw [map_add (f := _), LinearMap.mem_ker.mp y.2, zero_add, hx0]⟩
      left_inv := fun x => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun y => Subtype.ext (add_sub_cancel_right _ _) }
  haveI : Finite V := Module.finite_of_finite K
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]


open scoped Classical in
open Classical in
theorem card_fibre_compl {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U)
    (hφ : Function.Surjective φ) {k : ℕ} (z : Fin k → V) (hz : LinearIndependent K z)
    (a : U) :
    Nat.card {x : V // x ∉ span K (Set.range z) ∧ φ x = a} =
      if a ∈ span K (Set.range (fun j => φ (z j))) then
        Fintype.card K ^ finrank K (LinearMap.ker φ) -
          Fintype.card K ^ (k - finrank K (span K (Set.range (fun j => φ (z j)))))
      else Fintype.card K ^ finrank K (LinearMap.ker φ) := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V

  let ψ : (Fin k → K) →ₗ[K] U :=
    { toFun := fun c => φ (∑ j, c j • z j)
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _)]
      map_smul' := fun t c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul,
          RingHom.id_apply] }
  have hψ : LinearMap.range ψ = span K (Set.range (fun j => φ (z j))) := by
    ext u
    rw [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
    refine exists_congr fun c => ?_
    show φ (∑ j, c j • z j) = u ↔ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]

  have hin : Nat.card {x : V // x ∈ span K (Set.range z) ∧ φ x = a} = Nat.card {c : Fin k → K // ψ c = a} := by
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective (fun c => ⟨∑ j, c.1 j • z j, ?_, c.2⟩) ⟨?_, ?_⟩
    · exact (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨c.1, rfl⟩
    · intro c d hcd
      have h := congrArg Subtype.val hcd
      simp only at h
      have h0 : ∑ j, (c.1 j - d.1 j) • z j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
      exact Subtype.ext (funext fun j => sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hz _ h0 j))
    · intro x
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp x.2.1
      refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
      show φ (∑ j, c j • z j) = a
      rw [hc]; exact x.2.2

  have hsplit : Nat.card {x : V // x ∉ span K (Set.range z) ∧ φ x = a} =
      Nat.card {x : V // φ x = a} - Nat.card {x : V // x ∈ span K (Set.range z) ∧ φ x = a} := by
    have e : {x : V // φ x = a} ≃
        {x : V // x ∈ span K (Set.range z) ∧ φ x = a} ⊕ {x : V // x ∉ span K (Set.range z) ∧ φ x = a} :=
      { toFun := fun x => if h : x.1 ∈ span K (Set.range z) then Sum.inl ⟨x.1, h, x.2⟩
          else Sum.inr ⟨x.1, h, x.2⟩
        invFun := fun s => Sum.elim (fun y => ⟨y.1, y.2.2⟩) (fun y => ⟨y.1, y.2.2⟩) s
        left_inv := fun x => by
          by_cases h : x.1 ∈ span K (Set.range z) <;> simp [h]
        right_inv := fun s => by
          rcases s with y | y <;> simp [y.2.1] }
    have h := Nat.card_congr e
    rw [Nat.card_sum] at h
    omega
  obtain ⟨x0, hx0⟩ := hφ a
  rw [hsplit, card_fibre φ a x0 hx0, hin]
  split_ifs with ha
  · rw [← hψ] at ha
    obtain ⟨c0, hc0⟩ := ha
    rw [card_fibre ψ a c0 hc0]
    congr 2
    have hrk := LinearMap.finrank_range_add_finrank_ker ψ
    rw [Module.finrank_fin_fun, hψ] at hrk
    omega
  · have h0 : Nat.card {c : Fin k → K // ψ c = a} = 0 := by
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun c => ha ?_⟩
      rw [← hψ]
      exact ⟨c.1, c.2⟩
    rw [h0, Nat.sub_zero]

theorem fiber_card {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U)
    (hφ : Function.Surjective φ) {k : ℕ} (g : Fin k → U) :
    Nat.card {z : Fin k → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} =
      Fintype.card K ^ (Module.finrank K (Submodule.span K (Set.range g)) *
        Module.finrank K (LinearMap.ker φ)) *
      ∏ i ∈ Finset.range (k - Module.finrank K (Submodule.span K (Set.range g))),
        (Fintype.card K ^ Module.finrank K (LinearMap.ker φ) - Fintype.card K ^ i) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V
  induction k with
  | zero =>
    have h1 : Nat.card {z : Fin 0 → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
        ⟨⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩⟩⟩
    rw [h1, Set.range_eq_empty, Submodule.span_empty, finrank_bot]
    simp
  | succ k ih =>
    set gk : Fin k → U := fun j => g (Fin.castSucc j) with hgk
    set e := Module.finrank K (LinearMap.ker φ) with he
    set r := Module.finrank K (span K (Set.range gk)) with hr
    set q := Fintype.card K with hq
    have hstep : ∀ z' : {z' : Fin k → V // LinearIndependent K z' ∧ ∀ j, φ (z' j) = gk j},
        Nat.card {x : V // x ∉ span K (Set.range z'.1) ∧ φ x = g (Fin.last k)} =
          if g (Fin.last k) ∈ span K (Set.range gk) then q ^ e - q ^ (k - r) else q ^ e := by
      intro z'
      have h := card_fibre_compl φ hφ z'.1 z'.2.1 (g (Fin.last k))
      have hfz : (fun j => φ (z'.1 j)) = gk := funext z'.2.2
      rw [hfz] at h
      exact h
    have hequiv : {z : Fin (k + 1) → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} ≃
        Σ z' : {z' : Fin k → V // LinearIndependent K z' ∧ ∀ j, φ (z' j) = gk j},
          {x : V // x ∉ span K (Set.range z'.1) ∧ φ x = g (Fin.last k)} :=
      { toFun := fun z =>
          have hs := linearIndependent_finSnoc.mp (by rw [Fin.snoc_init_self]; exact z.2.1)
          ⟨⟨Fin.init z.1, hs.1, fun j => z.2.2 _⟩, ⟨z.1 (Fin.last k), hs.2, z.2.2 _⟩⟩
        invFun := fun p => ⟨Fin.snoc p.1.1 p.2.1, linearIndependent_finSnoc.mpr ⟨p.1.2.1, p.2.2.1⟩,
          fun j => by
            refine Fin.lastCases ?_ (fun i => ?_) j
            · rw [Fin.snoc_last]; exact p.2.2.2
            · rw [Fin.snoc_castSucc]; exact p.1.2.2 i⟩
        left_inv := fun z => Subtype.ext (Fin.snoc_init_self z.1)
        right_inv := fun p => by
          rcases p with ⟨⟨z', h1, h2⟩, ⟨x, h3, h4⟩⟩
          simp [Fin.init_snoc, Fin.snoc_last]
          exact (Subtype.heq_iff_coe_eq (fun y => by simp [Fin.init_snoc])).mpr rfl }
    rw [Nat.card_congr hequiv, Nat.card_sigma, Finset.sum_congr rfl (fun z' _ => hstep z'),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, ih gk]

    have hrange : Set.range g = insert (g (Fin.last k)) (Set.range gk) := by
      ext u
      simp only [Set.mem_range, Set.mem_insert_iff]
      constructor
      · rintro ⟨j, rfl⟩
        refine Fin.lastCases (Or.inl rfl) (fun i => Or.inr ⟨i, rfl⟩) j
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    have hle : r ≤ k := by
      rw [hr]
      exact (finrank_span_le_card (Set.range gk)).trans
        (by simp only [Set.toFinset_range]; exact Finset.card_image_le.trans (by simp))
    split_ifs with hmem
    · have hspan : span K (Set.range g) = span K (Set.range gk) := by
        rw [hrange, Submodule.span_insert_eq_span hmem]
      rw [hspan, ← hr, show k + 1 - r = (k - r) + 1 by omega, Finset.prod_range_succ]
      ring
    · have hspan : Module.finrank K (span K (Set.range g)) = r + 1 := by
        rw [hrange, Submodule.span_insert]
        haveI : FiniteDimensional K (span K (Set.range gk)) :=
          FiniteDimensional.span_of_finite K (Set.finite_range _)
        have hx0 : g (Fin.last k) ≠ 0 := fun h0 => hmem (h0 ▸ Submodule.zero_mem _)
        have hdis : span K {g (Fin.last k)} ⊓ span K (Set.range gk) = ⊥ := by
          rw [inf_comm, ← disjoint_iff]
          exact (Submodule.disjoint_span_singleton' hx0).mpr hmem
        have h := Submodule.finrank_sup_add_finrank_inf_eq (span K {g (Fin.last k)})
          (span K (Set.range gk))
        rw [hdis, finrank_bot, finrank_span_singleton hx0] at h
        omega
      rw [hspan, show k + 1 - (r + 1) = k - r by omega, ← hr]
      ring

end FibreCount
end

namespace PI.DensSplitW

theorem fiberCard_holds : FiberCard := by
  intro K V U _ _ _ _ _ _ _ φ hφ k g
  exact FibreCount.fiber_card φ hφ g

end PI.DensSplitW
