module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualInterEqSum
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta.DualLat

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

def tw (σ : L →+* L) (x : Fin N → L) : Fin N → L := fun j => σ (x j.rev)

def IntT (t : L) (x : Fin N → L) : Prop := ∀ i, t * x i ∈ intL L

theorem IntT.add {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x + y) := fun i => by
  simp only [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)

theorem IntT.neg {t : L} {x : Fin N → L} (hx : IntT t x) : IntT t (-x) := fun i => by
  simp only [Pi.neg_apply, mul_neg]; exact neg_mem (hx i)

theorem IntT.sub {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem IntT.mulVec {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hM : IsInt M) (hx : IntT t x) :
    IntT t (M *ᵥ x) := fun i => by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Subring.sum_mem _ fun k _ => by
    rw [mul_left_comm]; exact mul_mem (hM i k) (hx k)

theorem IntT.vecMul {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hx : IntT t x) (hM : IsInt M) :
    IntT t (x ᵥ* M) := fun j => by
  simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
  exact Subring.sum_mem _ fun k _ => by
    rw [← mul_assoc]; exact mul_mem (hx k) (hM k j)

theorem IntT.twist {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {t : L} {x : Fin N → L} (hx : IntT t x) :
    IntT t (tw σ x) := fun j => by
  show Valued.v (t * σ (x j.rev)) ≤ 1
  rw [map_mul, hσ, ← map_mul]; exact hx j.rev

theorem tw_tw {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (x : Fin N → L) : tw σ (tw σ x) = x := by
  ext j; simp [tw, hσσ]

theorem tw_add (σ : L →+* L) (x y : Fin N → L) : tw σ (x + y) = tw σ x + tw σ y := by
  ext j; simp [tw]

theorem tw_neg (σ : L →+* L) (x : Fin N → L) : tw σ (-x) = -tw σ x := by
  ext j; simp [tw]

theorem tw_vecMul {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (g : GU σ N) (x : Fin N → L) :
    tw σ x ᵥ* mat g = tw σ (mat g⁻¹ *ᵥ x) := by
  ext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [tw, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mat_inv_apply, hσσ, Fin.rev_rev]
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans ?_
  simp [mul_comm]

end GlobalTheory.InertZeta.DualLat

namespace GlobalTheory.InertZeta

open DualLat

theorem dual_inter_eq_sum : Dual := by
  intro L _ _ ϖ σ q N hU g U V C hF r b t hr
  obtain ⟨hσσ, hσ, -⟩ := hU
  obtain ⟨hUi, hVi, hCi, hgC, e⟩ := hF
  have e' : C * (U + V * mat g) = 1 := mul_eq_one_comm.1 e
  have hr' : r = -tw σ b := by ext j; simp [tw, hr]
  have m1 : C * V * mat g = 1 - C * U := by
    rw [Matrix.mul_assoc, ← e', Matrix.mul_add]; abel
  have m2 : C * V * mat g * mat g⁻¹ = C * V := by rw [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]
  have hCU : C * U = 1 - C * V * mat g := by rw [m1]; abel
  have m3 : mat g * C * U * mat g⁻¹ = 1 - mat g * C * V := by
    rw [Matrix.mul_assoc (mat g) C U, hCU]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, mat_mul_inv]
  change IntT t (r ᵥ* C) ↔ IntT t ((C * V * mat g) *ᵥ b) ∧ IntT t ((mat g * C * U) *ᵥ b)
  constructor
  · intro hρ
    have h1 : r = (r ᵥ* C) ᵥ* U + ((r ᵥ* C) ᵥ* V) ᵥ* mat g := by
      rw [Matrix.vecMul_vecMul (r ᵥ* C) V, ← Matrix.vecMul_add, Matrix.vecMul_vecMul, e', Matrix.vecMul_one]
    have hl₁ : IntT t (-tw σ ((r ᵥ* C) ᵥ* U)) := ((hρ.vecMul hUi).twist hσ).neg
    have hl₂ : IntT t (-tw σ ((r ᵥ* C) ᵥ* V)) := ((hρ.vecMul hVi).twist hσ).neg
    have htw : tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V)) = -r := by
      rw [tw_add, ← tw_vecMul hσσ, tw_neg, tw_neg, tw_tw hσσ, tw_tw hσσ, Matrix.neg_vecMul]
      conv_rhs => rw [h1]
      abel
    have hb : b = -tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V) := by
      calc b = tw σ (tw σ b) := (tw_tw hσσ b).symm
        _ = tw σ (tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V))) := by
          rw [htw, hr', neg_neg]
        _ = _ := tw_tw hσσ _
    rw [hb]
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m2, m1, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (hl₁.sub (IntT.mulVec (hCi.mul hUi) hl₁)).add (IntT.mulVec (hCi.mul hVi) hl₂)
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m3, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (IntT.mulVec (hgC.mul hUi) hl₁).add (hl₂.sub (IntT.mulVec (hgC.mul hVi) hl₂))
  · rintro ⟨h1, h2⟩
    have hb : b = (C * V * mat g) *ᵥ b + (C * U) *ᵥ b := by
      rw [← Matrix.add_mulVec, m1, sub_add_cancel, Matrix.one_mulVec]
    have key : ∀ b₁ b₂ : Fin N → L,
        -tw σ (b₁ + b₂) ᵥ* C = -(tw σ b₁ ᵥ* C) - tw σ (mat g *ᵥ b₂) ᵥ* (mat g * C) := by
      intro b₁ b₂
      rw [← Matrix.vecMul_vecMul, tw_vecMul hσσ, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec, tw_add,
        Matrix.neg_vecMul, Matrix.add_vecMul]
      abel
    have h2' : IntT t (mat g *ᵥ ((C * U) *ᵥ b)) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]; exact h2
    rw [hr', hb, key]
    exact ((h1.twist hσ).vecMul hCi).neg.sub ((h2'.twist hσ).vecMul hgC)

end GlobalTheory.InertZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthCountGeneratingSeriesFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthCountGeneratingSeriesFormula
open GlobalTheory.InertZeta

noncomputable section

namespace GlobalTheory.InertZeta

theorem genFun_counts_hasSum {𝕜 : Type} [NormedField 𝕜] [CompleteSpace 𝕜] (c q N : ℕ) (x : 𝕜)
    (hx : ‖(q : 𝕜) ^ (N + 1) * x‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j)
      (c * (1 + q * x) / (1 - ((q : 𝕜) ^ (N + 1) * x) ^ 2)) := by
  set y := (q : 𝕜) ^ (N + 1) * x with hy
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg y]
  have hg := hasSum_geometric_of_norm_lt_one hy2
  have fe : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k) / 2) + 2 * k) : ℕ) : 𝕜) * x ^ (2 * k)) =
      fun k => (c : 𝕜) * (y ^ 2) ^ k := by
    funext k
    rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
    push_cast
    rw [hy]; ring
  have fo : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k + 1) / 2) + (2 * k + 1)) : ℕ) : 𝕜) * x ^ (2 * k + 1)) =
      fun k => ((c : 𝕜) * q * x) * (y ^ 2) ^ k := by
    funext k
    rw [show (2 * k + 1) / 2 = k by omega]
    push_cast
    rw [hy]; ring
  have he := hg.mul_left (c : 𝕜)
  have ho := hg.mul_left ((c : 𝕜) * q * x)
  rw [← fe] at he
  rw [← fo] at ho
  have := HasSum.even_add_odd (f := fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j) he ho
  rw [show (c : 𝕜) * (1 + q * x) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * x * (1 - y ^ 2)⁻¹ by
    rw [div_eq_mul_inv]; ring]
  exact this

theorem genFun_diff_hasSum {𝕜 : Type} [NormedField 𝕜] (C d : ℕ → ℕ) (x S : 𝕜)
    (h0 : d 0 = C 0) (hs : ∀ j, C (j + 1) = C j + d (j + 1))
    (hA : HasSum (fun j => (C j : 𝕜) * x ^ j) S) :
    HasSum (fun j => (d j : 𝕜) * x ^ j) ((1 - x) * S) := by
  let h : ℕ → 𝕜 := fun j => if j = 0 then 0 else (C (j - 1) : 𝕜) * x ^ j
  have hsh : (fun n => h (n + 1)) = fun n => x * ((C n : 𝕜) * x ^ n) := by
    funext n
    simp only [h, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero n)]
    ring
  have h1 : HasSum (fun n => h (n + 1)) (x * S) := by rw [hsh]; exact hA.mul_left x
  have hh : HasSum h (x * S) := by
    have := (hasSum_nat_add_iff (f := h) 1).1 h1
    simpa [h] using this
  have hd : (fun j => (d j : 𝕜) * x ^ j) = fun j => (C j : 𝕜) * x ^ j - h j := by
    funext j
    rcases j with _ | j
    · simp [h, h0]
    · simp only [h, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hs j]
      push_cast; ring
  rw [hd, show (1 - x) * S = S - x * S by ring]
  exact hA.sub hh

theorem genFun_fibre_hasSum {ι 𝕜 : Type} [NormedField 𝕜] (f : ι → ℕ) (l j : ℕ) (x : 𝕜)
    (hfin : Set.Finite {i | f i - l = j}) (hl : ∀ i, l ≤ f i) :
    HasSum (fun y : {i // f i - l = j} => x ^ f y.1) ((Set.ncard {i | f i - l = j} : 𝕜) * x ^ (l + j)) := by
  haveI : Finite {i // f i - l = j} := hfin.to_subtype
  haveI : Fintype {i // f i - l = j} := Fintype.ofFinite _
  have hc : ∀ y : {i // f i - l = j}, x ^ f y.1 = x ^ (l + j) := fun y => by
    have := hl y.1; have := y.2
    rw [show f y.1 = l + j by omega]
  have e : Nat.card {i // f i - l = j} = Set.ncard {i | f i - l = j} := Nat.card_coe_set_eq {i : ι | f i - l = j}
  have h := hasSum_fintype (fun y : {i // f i - l = j} => x ^ f y.1)
  rw [Finset.sum_congr rfl (fun y _ => hc y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, e] at h
  exact h

theorem genFun_holds : GenFun := by
  intro ι f l c q N X hc hq hl hcard hX
  let C : ℕ → ℕ := fun j => c * q ^ (2 * N * (j / 2) + j)
  let g : ι → ℕ := fun i => f i - l
  have hCpos : ∀ j, C j ≠ 0 := fun j =>
    Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hle : ∀ j, {i | g i ≤ j} = {i | f i ≤ l + j} := fun j => by
    ext i; simp only [Set.mem_setOf_eq, g]; have := hl i; omega
  have hcum : ∀ j, Set.ncard {i | g i ≤ j} = C j := fun j => by
    rw [hle, ← Nat.card_coe_set_eq]; exact hcard j
  have hfin : ∀ j, Set.Finite {i | g i ≤ j} := fun j => by
    apply Set.finite_of_ncard_ne_zero; rw [hcum]; exact hCpos j
  have hfin' : ∀ j, Set.Finite {i | f i - l = j} := fun j =>
    (hfin j).subset fun i hi => by simp only [Set.mem_setOf_eq, g] at hi ⊢; omega
  let d : ℕ → ℕ := fun j => Set.ncard {i | f i - l = j}
  have h0 : d 0 = C 0 := by
    rw [← hcum 0]
    show Set.ncard {i | f i - l = 0} = _
    congr 1; ext i; simp only [Set.mem_setOf_eq, g]; omega
  have hs : ∀ j, C (j + 1) = C j + d (j + 1) := fun j => by
    have hdis : Disjoint {i | g i ≤ j} {i | f i - l = j + 1} :=
      Set.disjoint_left.2 fun i h1 h2 => by simp only [Set.mem_setOf_eq, g] at h1 h2; omega
    have hun : {i | g i ≤ j + 1} = {i | g i ≤ j} ∪ {i | f i - l = j + 1} := by
      ext i; simp only [Set.mem_setOf_eq, Set.mem_union, g]; omega
    rw [← hcum, ← hcum, hun, Set.ncard_union_eq hdis (hfin j) (hfin' (j + 1))]
  let e := Equiv.sigmaFiberEquiv g
  have hr : ‖(q : ℝ) ^ (N + 1) * ‖X‖‖ < 1 := by
    rw [norm_mul, norm_pow, Real.norm_natCast, norm_norm]
    rwa [norm_mul, norm_pow, Complex.norm_natCast] at hX
  have hRB := (genFun_diff_hasSum C d ‖X‖ _ h0 hs (genFun_counts_hasSum c q N ‖X‖ hr)).mul_left (‖X‖ ^ l)
  have hsumR : Summable (fun i => ‖X‖ ^ f i) := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (f := (fun i => ‖X‖ ^ f i) ∘ e) (fun _ => pow_nonneg (norm_nonneg _) _)).2 ⟨fun j => (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).summable, ?_⟩
    refine hRB.summable.congr fun j => ?_
    have ht : ∑' (y : {x // g x = j}), ((fun i => ‖X‖ ^ f i) ∘ e) ⟨j, y⟩ = (d j : ℝ) * ‖X‖ ^ (l + j) :=
      (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).tsum_eq
    rw [ht, pow_add]
    ring
  have hsumC : Summable (fun i => X ^ f i) := Summable.of_norm (by simpa [norm_pow] using hsumR)
  have hB := (genFun_diff_hasSum C d X _ h0 hs (genFun_counts_hasSum c q N X hX)).mul_left (X ^ l)
  have hBC : HasSum (fun j => (d j : ℂ) * X ^ (l + j)) (c * X ^ l * jFac q N X) := by
    have e1 : (fun j => (d j : ℂ) * X ^ (l + j)) = fun j => X ^ l * ((d j : ℂ) * X ^ j) := by
      funext j; rw [pow_add]; ring
    rw [e1, show (c : ℂ) * X ^ l * jFac q N X =
      X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]
    exact hB
  have hsig := HasSum.sigma_of_hasSum (f := (fun i => X ^ f i) ∘ e) hBC
    (fun j => genFun_fibre_hasSum f l j X (hfin' j) hl) (e.summable_iff.2 hsumC)
  exact e.hasSum_iff.1 hsig

end GlobalTheory.InertZeta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthCountGeneratingSeriesFormulaStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_count_generating_series_formula : GenFun := by
  first | exact @GlobalTheory.InertZeta.genFun_holds | exact GlobalTheory.InertZeta.genFun_holds | (intros; apply GlobalTheory.InertZeta.genFun_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalInductionTransitivityOfLeviExists
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalInductionTransitivityOfLeviExists
noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem blk_mono {i j : Fin (N + 2)} (h : j ≤ i) : blk N j ≤ blk N i := by
  rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;> simp
  all_goals first
    | (rw [Fin.le_iff_val_le_val] at h; have := i'.2; simp at h; omega)
    | (rw [Fin.le_iff_val_le_val] at h; simp at h; done)
    | (rw [Fin.le_iff_val_le_val] at h; simp at h; omega)

theorem levi_ext {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g₀ m)
    (h' : IsLeviElt ϖ a g₀ m') : m = m' := by
  apply mat_injective
  funext i j
  by_cases hij : blk N i = blk N j
  · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
      simp at hij
    · rw [h.2.1, h'.2.1]
    · rw [h.2.2.2 i' j', h'.2.2.2 i' j']
    · rw [h.2.2.1, h'.2.2.1]
  · rw [h.1 i j hij, h'.1 i j hij]

theorem levi_mul {ϖ : L} (hϖ : ϖ ≠ 0) {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g m)
    (h' : IsLeviElt ϖ a' g' m') : IsLeviElt ϖ (a + a') (g * g') (m * m') := by
  have e : ∀ i j, mat (m * m') i j = mat m i 0 * mat m' 0 j + ∑ l, mat m i (mid l) * mat m' (mid l) j +
      mat m i (Fin.last (N + 1)) * mat m' (Fin.last (N + 1)) j := fun i j => by
    rw [mat_mul, Matrix.mul_apply, sum_idx (fun l => mat m i l * mat m' l j)]
  have z : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := h.1
  have z' : ∀ i j, blk N i ≠ blk N j → mat m' i j = 0 := h'.1
  refine ⟨mul_mem h.1 h'.1, ?_, ?_, fun i j => ?_⟩
  · rw [e, h.2.1, h'.2.1, z 0 (Fin.last (N + 1)) (by simp), zero_mul, add_zero,
      Finset.sum_eq_zero (fun l _ => by rw [z 0 (mid l) (by simp), zero_mul]), add_zero, zpow_add₀ hϖ]
  · rw [e, h.2.2.1, h'.2.2.1, z (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
      Finset.sum_eq_zero (fun l _ => by rw [z (Fin.last (N + 1)) (mid l) (by simp), zero_mul]), zero_add,
      neg_add, zpow_add₀ hϖ]
  · rw [e, z (mid i) 0 (by simp), z (mid i) (Fin.last (N + 1)) (by simp), zero_mul, zero_mul, zero_add, add_zero,
      mat_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.2.2.2, h'.2.2.2]

end

theorem sphTrans (hL : LeviExists) : SphTrans := by
  intro L _ _ ϖ σ q N r hU hr α φ φ₀ hα hsph h1 hsph₀ h10 a g₀ m hm u hu
  have hϖ : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact WithZero.zero_ne_coe this
  obtain ⟨b₀, k₀, hb₀, hk₀, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g₀
  obtain ⟨mb, hmb⟩ := hL L ϖ σ q N hU a b₀
  obtain ⟨mk, hmk⟩ := hL L ϖ σ q N hU 0 k₀
  have hm' : m = mb * mk := by
    have := levi_mul hϖ hmb hmk
    rw [add_zero] at this
    exact levi_ext hm this
  subst hm'

  have hmkK : mk ∈ KU σ (N + 2) := by
    rw [mem_KU_iff hU.2.1]
    intro i j
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
        simp at hij
      · rw [hmk.2.1, zpow_zero]; exact one_mem _
      · rw [hmk.2.2.2 i' j']; exact P.fSatake_K_int hk₀ i' j'
      · rw [hmk.2.2.1, neg_zero, zpow_zero]; exact one_mem _
    · rw [hmk.1 i j hij]; exact zero_mem _
  set v := mk * u * mk⁻¹ with hv
  have hvR : v ∈ radQ σ N := (leviRad L σ (N + 2) (blk N) hU.2.1 mk hmk.1 u hu).1
  have hdiag : ∀ i j, blk N j ≤ blk N i → mat (mb * v) i j = mat mb i j :=
    fun i j h => levi_mul_rad_apply hmb.1 hvR h
  have hB : IsBorelU (mb * v) := by
    intro i j hji
    show mat (mb * v) i j = 0
    rw [hdiag i j (blk_mono hji.le)]
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
        simp at hij
      · exact absurd hji (lt_irrefl _)
      · rw [hmb.2.2.2 i' j']
        exact hb₀ i' j' (by rw [Fin.lt_iff_val_lt_val] at hji ⊢; simpa using hji)
      · exact absurd hji (lt_irrefl _)
    · exact hmb.1 i j hij
  have e1 : mb * mk * u = (mb * v) * 1 * mk := by rw [hv]; group
  have hφ : φ (mb * mk * u) = chiDeltaU q α (mb * v) := by
    rw [e1, hsph _ _ _ hB hmkK, h1, mul_one]
  have hφ₀ : φ₀ (b₀ * k₀) = chiDeltaU q (Fin.tail α) b₀ := by
    have := hsph₀ b₀ 1 k₀ hb₀ hk₀
    rwa [mul_one, h10, mul_one] at this
  rw [hφ, hφ₀]
  unfold chiDeltaU
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [dite_eq_left (by simp)]
    have e0 : (⟨(0 : Fin (r + 1)).val, by simp⟩ : Fin (N + 2)) = 0 := rfl
    rw [e0]
    show α 0 ^ ordL (mat (mb * v) 0 0) * (q : ℂ) ^ (-ordL (mat (mb * v) 0 0) * (((N + 2 : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ))) = _
    rw [hdiag 0 0 le_rfl, hmb.2.1, P.fSatake_ord_zpow hU.2.2.2.1]
    congr 2
    push_cast
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hiN : i.val < N := by have := i.2; omega
    rw [dite_eq_left (by simp; omega), dite_eq_left hiN]
    have ei : (⟨(Fin.succ i).val, by simp; omega⟩ : Fin (N + 2)) = mid ⟨i.val, hiN⟩ := by
      ext; simp
    rw [ei]
    show α i.succ ^ ordL (mat (mb * v) (mid ⟨i.val, hiN⟩) (mid ⟨i.val, hiN⟩)) *
      (q : ℂ) ^ (-ordL (mat (mb * v) (mid ⟨i.val, hiN⟩) (mid ⟨i.val, hiN⟩)) *
        (((N + 2 : ℕ) : ℤ) - 1 - 2 * ((i.succ.val : ℕ) : ℤ))) = _
    rw [hdiag _ _ le_rfl, hmb.2.2.2]
    show _ = Fin.tail α i ^ ordL (mat b₀ ⟨i.val, hiN⟩ ⟨i.val, hiN⟩) *
      (q : ℂ) ^ (-ordL (mat b₀ ⟨i.val, hiN⟩ ⟨i.val, hiN⟩) * ((N : ℤ) - 1 - 2 * ((i.val : ℕ) : ℤ)))
    congr 2
    simp only [Fin.val_succ]
    push_cast
    ring

end GlobalTheory.InertZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalInductionTransitivityOfLeviExistsStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalInductionTransitivity_of_leviExists : LeviExists → SphTrans := by
  first | exact @GlobalTheory.InertZeta.sphTrans | exact GlobalTheory.InertZeta.sphTrans | (intros; apply GlobalTheory.InertZeta.sphTrans <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHeisenbergRadicalCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHeisenbergRadicalCoordinates
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta.HeisCoord

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

def Shape (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (r b : Fin N → L) (c : L) : Prop :=
  M 0 0 = 1 ∧ (∀ j, M 0 (mid j) = r j) ∧ M 0 (Fin.last (N + 1)) = c ∧ (∀ i, M (mid i) 0 = 0) ∧
  (∀ i j, M (mid i) (mid j) = if i = j then 1 else 0) ∧ (∀ i, M (mid i) (Fin.last (N + 1)) = b i) ∧
  M (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, M (Fin.last (N + 1)) (mid j) = 0) ∧
  M (Fin.last (N + 1)) (Fin.last (N + 1)) = 1

theorem form_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ M * antiJ L n * M) i j = ∑ l, σ (M l.rev i) * M l j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [P.fSatake_cTJ]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem antiJ_eq {n : ℕ} (a b : Fin n) : antiJ L n a b = if a = b.rev then 1 else 0 := by
  simp only [antiJ, P.fSatake_rev_iff]

theorem shape_of_mem {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : Shape (mat u) (rowOf u) (colOf u) (cornerOf u) := by
  have h : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  refine ⟨?_, fun j => rfl, rfl, fun i => ?_, fun i j => ?_, fun i => rfl, ?_, fun j => ?_, ?_⟩
  · rw [h 0 0 le_rfl, Matrix.one_apply_eq]
  · rw [h _ _ (by simp), Matrix.one_apply_ne (mid_ne_zero i)]
  · rw [h _ _ (by simp)]; simp [Matrix.one_apply, mid_injective.eq_iff]
  · rw [h _ _ (by simp), Matrix.one_apply_ne last_ne_zero]
  · rw [h _ _ (by simp), Matrix.one_apply_ne (mid_ne_last j).symm]
  · rw [h _ _ le_rfl, Matrix.one_apply_eq]

theorem sum_rev_ite {M : Type} [AddCommMonoid M] (f : Fin N → M) (j : Fin N) :
    (∑ x, if x.rev = j then f x else 0) = f j.rev := by
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro x _ hx
    rw [if_neg fun e => hx (by rw [← e, Fin.rev_rev])]
  · simp

theorem form_mid_last {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L} (h : Shape M r b c)
    (j : Fin N) : (cT σ M * antiJ L (N + 2) * M) (mid j) (Fin.last (N + 1)) = b j.rev + σ (r j) := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  rw [form_apply, sum_idx]
  simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite]

theorem form_last_last {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L} (h : Shape M r b c) :
    (cT σ M * antiJ L (N + 2) * M) (Fin.last (N + 1)) (Fin.last (N + 1)) = c + ∑ k, σ (b k.rev) * b k + σ c := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  rw [form_apply, sum_idx]
  simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite]

theorem zero_ne_mid (i : Fin N) : (0 : Fin (N + 2)) ≠ mid i := (mid_ne_zero i).symm
theorem last_ne_mid (i : Fin N) : Fin.last (N + 1) ≠ mid i := (mid_ne_last i).symm

theorem form_eq_of (hσσ : ∀ x, σ (σ x) = x) {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L}
    (h : Shape M r b c) (h1 : ∀ j, b j.rev + σ (r j) = 0) (h2 : c + ∑ k, σ (b k.rev) * b k + σ c = 0) :
    cT σ M * antiJ L (N + 2) * M = antiJ L (N + 2) := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  ext i j
  rw [form_apply, sum_idx, antiJ_eq]
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite,
      mid_ne_zero, mid_ne_last, zero_ne_mid, last_ne_mid, mid_injective.eq_iff]
  · by_cases e : i = j.rev
    · subst e; simp
    · rw [if_neg e, if_neg fun e' => e e'.symm]
  · exact h1 i
  · have := congrArg σ (h1 j)
    simp only [map_add (f := _), hσσ, map_zero] at this
    linear_combination this
  · exact h2

def heisMat (r b : Fin N → L) (c : L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L := fun i j =>
  if i = j then 1
  else if i = 0 ∧ j = Fin.last (N + 1) then c
  else if h : i = 0 ∧ 0 < j.val ∧ j.val < N + 1 then r ⟨j.val - 1, by omega⟩
  else if h : j = Fin.last (N + 1) ∧ 0 < i.val ∧ i.val < N + 1 then b ⟨i.val - 1, by omega⟩
  else 0

theorem shape_heisMat (r b : Fin N → L) (c : L) : Shape (heisMat r b c) r b c := by
  refine ⟨by simp [heisMat], fun j => ?_, by simp [heisMat, last_ne_zero.symm], fun i => ?_, fun i j => ?_,
    fun i => ?_, by simp [heisMat, last_ne_zero], fun j => ?_, by simp [heisMat]⟩
  · have := j.2
    simp [heisMat, zero_ne_mid, mid_ne_last]
  · simp [heisMat, mid_ne_zero, last_ne_zero.symm]
  · simp [heisMat, mid_injective.eq_iff, mid_ne_zero, mid_ne_last]
  · have := i.2
    simp [heisMat, mid_ne_zero, mid_ne_last]
  · simp [heisMat, last_ne_mid, last_ne_zero]

theorem mem_radQ_of_shape {u : GU σ (N + 2)} {r b : Fin N → L} {c : L} (h : Shape (mat u) r b c) :
    u ∈ radQ σ N := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  intro i j hij
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Matrix.one_apply, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, mid_ne_zero, mid_ne_last, zero_ne_mid,
      last_ne_mid, mid_injective.eq_iff] at hij ⊢

theorem mul_coords {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u' := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := shape_of_mem hu
  obtain ⟨h00', h0m', h0l', hm0', hmm', hml', hl0', hlm', hll'⟩ := shape_of_mem hu'
  refine ⟨funext fun j => ?_, funext fun i => ?_, ?_⟩
  · simp only [rowOf, mat_mul, Matrix.mul_apply, sum_idx, Pi.add_apply]
    simp [h00, h0m, h0l, hmm', hl0', hlm', h0m']
    ring
  · simp only [colOf, mat_mul, Matrix.mul_apply, sum_idx, Pi.add_apply]
    simp [hm0, hmm, hml, hml', hll', h0l']
    ring
  · simp only [cornerOf, mat_mul, Matrix.mul_apply, sum_idx, dotProduct]
    simp [h00, h0m, h0l, hml', hll', h0l']
    ring

theorem Heisenberg₂ : Heis := by
  intro L _ _ ϖ σ q N hU
  obtain ⟨hσσ, hv, -⟩ := hU
  have hσint : ∀ x, x ∈ intL L → σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [hv]; exact hx
  refine ⟨fun u hu => ?_, fun u hu u' hu' => mul_coords hu hu', fun r c hc => ?_⟩
  · have hs := shape_of_mem hu
    have hf : cT σ (mat u) * antiJ L (N + 2) * mat u = antiJ L (N + 2) := u.2
    have h1 : ∀ j, colOf u j.rev + σ (rowOf u j) = 0 := fun j => by
      have := congrFun (congrFun hf (mid j)) (Fin.last (N + 1))
      rwa [form_mid_last hs, antiJ_eq, if_neg (by rw [Fin.rev_last]; exact mid_ne_zero j)] at this
    have h2 : cornerOf u + ∑ k, σ (colOf u k.rev) * colOf u k + σ (cornerOf u) = 0 := by
      have := congrFun (congrFun hf (Fin.last (N + 1))) (Fin.last (N + 1))
      rwa [form_last_last hs, antiJ_eq, if_neg (by rw [Fin.rev_last]; exact last_ne_zero)] at this
    have hr : ∀ j, rowOf u j = -σ (colOf u j.rev) := fun j => by
      have := congrArg σ (h1 j)
      simp only [map_add (f := _), hσσ, map_zero] at this
      linear_combination this
    refine ⟨hr, ?_, ?_⟩
    · simp only [dotProduct, hr, neg_mul, Finset.sum_neg_distrib]
      linear_combination h2
    · rw [mem_KU_iff hv]
      constructor
      · intro h
        exact ⟨fun j => h _ _, h _ _⟩
      · rintro ⟨hr', hc'⟩ i j
        obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := hs
        have hb : ∀ i, colOf u i ∈ intL L := fun i => by
          have e := hr i.rev
          rw [Fin.rev_rev] at e
          have h' : colOf u i = -σ (rowOf u i.rev) := by rw [e, map_neg, hσσ, neg_neg]
          rw [h']
          exact neg_mem (hσint _ (hr' _))
        rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
          simp only [h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll] <;>
          first | exact one_mem _ | exact zero_mem _ | exact hr' _ | exact hc' | exact hb _ |
            (split_ifs <;> first | exact one_mem _ | exact zero_mem _)
  · let b : Fin N → L := fun i => -σ (r i.rev)
    have h1 : ∀ j, b j.rev + σ (r j) = 0 := fun j => by simp [b]
    have h2 : c + ∑ k, σ (b k.rev) * b k + σ c = 0 := by
      simp only [b, Fin.rev_rev, map_neg, hσσ, neg_mul_neg]
      linear_combination hc
    obtain ⟨g, hg⟩ := exists_mat (σ := σ) (heisMat r b c) (form_eq_of hσσ (shape_heisMat r b c) h1 h2)
    have hs : Shape (mat g) r b c := hg ▸ shape_heisMat r b c
    exact ⟨g, mem_radQ_of_shape hs, funext hs.2.1, hs.2.2.1⟩

end GlobalTheory.InertZeta.HeisCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHeisenbergRadicalCoordinatesStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_heisenberg_radical_coordinates : Heis := by
  first | exact @GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ | exact GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ | (intros; apply GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLatticeInverseIndexOfElementaryDivisors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLatticeInverseIndexOfElementaryDivisors
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem relIndex_pi_univ {ι : Type} [Fintype ι] {G : Type} [AddCommGroup G] (I J : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ J).relIndex (AddSubgroup.pi Set.univ I) = ∏ a, (J a).relIndex (I a) := by
  classical
  let φ : (AddSubgroup.pi Set.univ I) →+ ∀ a, (I a ⧸ (J a).addSubgroupOf (I a)) :=
    { toFun := fun x a => QuotientAddGroup.mk (⟨(x : ι → G) a, x.2 a (Set.mem_univ a)⟩ : I a)
      map_zero' := by funext a; rfl
      map_add' := fun x y => by funext a; rfl }
  have hsurj : Function.Surjective φ := by
    intro c
    choose y hy using fun a => QuotientAddGroup.mk_surjective (c a)
    refine ⟨⟨fun a => (y a : G), fun a _ => (y a).2⟩, ?_⟩
    funext a
    show QuotientAddGroup.mk (⟨(y a : G), _⟩ : I a) = c a
    rw [← hy a]
  have hker : φ.ker = (AddSubgroup.pi Set.univ J).addSubgroupOf (AddSubgroup.pi Set.univ I) := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h a _
      have := congrFun h a
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf] at this
      exact this
    · intro h
      funext a
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf]
      exact h a (Set.mem_univ a)
  unfold AddSubgroup.relIndex AddSubgroup.index
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, Nat.card_pi]

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def scaledInt (c : L) : AddSubgroup L := (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft c)

theorem mem_scaledInt {c x : L} : x ∈ scaledInt c ↔ c * x ∈ intL L := Iff.rfl

theorem mulLeft_surjective {c : L} (hc : c ≠ 0) : Function.Surjective (AddMonoidHom.mulLeft c) :=
  fun y => ⟨c⁻¹ * y, by simp [AddMonoidHom.mulLeft, mul_inv_cancel_left₀ hc]⟩

theorem mulLeft_injective {c : L} (hc : c ≠ 0) : Function.Injective (AddMonoidHom.mulLeft c) :=
  fun x y h => mul_left_cancel₀ hc h

theorem relIndex_scaledInt {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (d : ℕ) :
    (intL L).toAddSubgroup.relIndex (scaledInt (ϖ ^ d)) = q ^ (2 * d) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hϖ : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

  have h1 : (intL L).toAddSubgroup.relIndex (scaledInt ϖ) = q ^ 2 := by
    have hm : ((scaledInt ϖ).map (AddMonoidHom.mulLeft ϖ)) = (intL L).toAddSubgroup :=
      AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective h0) _
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (mulLeft_injective h0), hm]
    exact intIndex L ϖ σ q hU
  induction d with
  | zero =>
    have : scaledInt (ϖ ^ 0) = (intL L).toAddSubgroup := by
      ext x; simp [mem_scaledInt]
    rw [this, AddSubgroup.relIndex_self]; simp
  | succ d ih =>
    have hle1 : (intL L).toAddSubgroup ≤ scaledInt (ϖ ^ d) := fun x hx =>
      mul_mem (pow_mem hϖ d) hx
    have hle2 : scaledInt (ϖ ^ d) ≤ scaledInt (ϖ ^ (d + 1)) := fun x hx => by
      rw [mem_scaledInt] at hx ⊢
      rw [pow_succ, mul_comm _ ϖ, mul_assoc]
      exact mul_mem hϖ hx
    have hc : scaledInt (ϖ ^ (d + 1)) = (scaledInt ϖ).comap (AddMonoidHom.mulLeft (ϖ ^ d)) := by
      ext x
      simp only [AddSubgroup.mem_comap, mem_scaledInt]
      rw [pow_succ, mul_comm _ ϖ, mul_assoc]
      exact Iff.rfl
    have hstep : (scaledInt (ϖ ^ d)).relIndex (scaledInt (ϖ ^ (d + 1))) = q ^ 2 := by
      rw [hc, scaledInt, AddSubgroup.relIndex_comap,
        AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective (pow_ne_zero d h0)), h1]
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, ih, hstep]
    ring

end

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem intV_vecMul {r : Fin n → L} {M : Matrix (Fin n) (Fin n) L} (hr : r ∈ intV L n) (hM : IsInt M) :
    r ᵥ* M ∈ intV L n := by
  rw [mem_intV] at hr ⊢
  intro j
  simp only [Matrix.vecMul, dotProduct]
  exact Subring.sum_mem _ fun i _ => mul_mem (hr i) (hM i j)

theorem preLat_diagonal (ϖ : L) (d : Fin n → ℕ) :
    preLat (Matrix.diagonal fun i => ϖ ^ d i) = AddSubgroup.pi Set.univ fun i => scaledInt (ϖ ^ d i) := by
  ext r
  rw [mem_preLat, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_scaledInt, Matrix.vecMul_diagonal, mul_comm (r _)]

theorem latIndex_diagonal {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (d : Fin n → ℕ) :
    (intV L n).relIndex (preLat (Matrix.diagonal fun i => ϖ ^ d i)) = q ^ (2 * ∑ i, d i) := by
  rw [preLat_diagonal, intV, relIndex_pi_univ]
  simp only [relIndex_scaledInt hU, Finset.mul_sum, Finset.prod_pow_eq_pow_sum]

theorem relIndex_preLat_mul {A D a a' : Matrix (Fin n) (Fin n) L} (ha : IsInt a) (ha' : IsInt a') (ea : a' * a = 1)
    (hpre : ∀ r, r ∈ preLat A ↔ r ᵥ* a ∈ preLat D) :
    (intV L n).relIndex (preLat A) = (intV L n).relIndex (preLat D) := by
  have ea2 : a * a' = 1 := mul_eq_one_comm.1 ea
  let f : (Fin n → L) →+ (Fin n → L) := a.vecMulLinear.toAddMonoidHom
  have hf : ∀ r, f r = r ᵥ* a := fun r => rfl
  have hsurj : Function.Surjective f := fun y => ⟨y ᵥ* a', by rw [hf, Matrix.vecMul_vecMul, ea, Matrix.vecMul_one]⟩
  have h1 : preLat A = (preLat D).comap f := by
    ext r; rw [AddSubgroup.mem_comap, hf]; exact hpre r
  have h2 : intV L n = (intV L n).comap f := by
    ext r
    rw [AddSubgroup.mem_comap, hf]
    refine ⟨fun h => intV_vecMul h ha, fun h => ?_⟩
    have := intV_vecMul h ha'
    rwa [Matrix.vecMul_vecMul, ea2, Matrix.vecMul_one] at this
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj, ← h2]

end

theorem latIndex_of_smith : Smith → LatIndex := by
  intro hS L _ _ ϖ σ q n hU A k hA hdet
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hA0 : A.det ≠ 0 := fun h => by
    rw [h, map_zero] at hdet; exact WithZero.exp_ne_zero hdet.symm
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hv A hA0
  set D := Matrix.diagonal fun i => ϖ ^ d i with hD
  have ea2 : a * a' = 1 := mul_eq_one_comm.1 ea
  have eb2 : b' * b = 1 := mul_eq_one_comm.1 eb

  have hDint : IsInt D := by
    have : D = a' * (a * D * b) * b' := by
      rw [show a' * (a * D * b) * b' = (a' * a) * D * (b * b') by simp only [Matrix.mul_assoc], ea, eb,
        Matrix.one_mul, Matrix.mul_one]
    rw [this]
    exact (ha'.mul hA).mul hb'
  have hvz : ∀ z : ℤ, Valued.v (ϖ ^ z) = WithZero.exp (-z) := fun z => by
    rw [map_zpow₀, hv, ← WithZero.exp_zsmul]; congr 1; simp
  have hd : ∀ i, 0 ≤ d i := fun i => by
    have h := hDint i i
    rw [hD, Matrix.diagonal_apply_eq] at h
    have h' : Valued.v (ϖ ^ d i) ≤ 1 := h
    rw [hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at h'
    omega
  set e : Fin n → ℕ := fun i => (d i).toNat with he
  have hde : ∀ i, d i = (e i : ℤ) := fun i => (Int.toNat_of_nonneg (hd i)).symm
  have hDe : D = Matrix.diagonal fun i => ϖ ^ e i := by
    rw [hD]; congr 1; funext i; rw [hde i, zpow_natCast]

  have hk : k = ∑ i, e i := by
    have hva : Valued.v a.det = 1 := v_det_eq_one ha ha' ea2
    have hvb : Valued.v b.det = 1 := v_det_eq_one hb hb' eb
    rw [Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, hva, hvb, one_mul, mul_one, hDe,
      Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, ← zpow_natCast, hvz, WithZero.exp_inj] at hdet
    exact_mod_cast (neg_inj.1 hdet).symm

  have hpre : ∀ r, r ∈ preLat (a * D * b) ↔ r ᵥ* a ∈ preLat D := fun r => by
    show r ᵥ* (a * D * b) ∈ intV L n ↔ (r ᵥ* a) ᵥ* D ∈ intV L n
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    refine ⟨fun h => ?_, fun h => intV_vecMul h hb⟩
    have := intV_vecMul h hb'
    rwa [Matrix.vecMul_vecMul, eb, Matrix.vecMul_one] at this
  rw [relIndex_preLat_mul ha ha' ea hpre, hDe, latIndex_diagonal hU, hk]

end GlobalTheory.InertZeta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLatticeInverseIndexOfElementaryDivisorsStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralLatticeInverseIndex_of_elementaryDivisors : Smith → LatIndex := by
  first | exact @GlobalTheory.InertZeta.latIndex_of_smith | exact GlobalTheory.InertZeta.latIndex_of_smith | (intros; apply GlobalTheory.InertZeta.latIndex_of_smith <;> assumption)
end
end
