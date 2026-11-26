module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ReflectionMemGlevCastSucc
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeight

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ThresholdPowerBoundOfCounts
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem threshold_arith_letter_case (k Ns c q bo : ℝ) (hk5 : 5 ≤ k) (hN : 1 ≤ Ns) (hc : 40 * (k * Ns) ≤ c) (hq : 9 / 10 * c ≤ q)
    (hb : q - k < bo) : c / 2 ≤ 2 / 3 * bo - k * Ns := by
  have hkN : k ≤ k * Ns := by nlinarith
  linarith

theorem threshold_arith_w_case (k Ns c q fl r : ℝ) (hk5 : 5 ≤ k) (hN : 1 ≤ Ns) (hr : r ≤ k) (hc : 40 * (k * Ns) ≤ c)
    (hq : 9 / 10 * c ≤ q) (hfl : q - 1 < fl) :
    c / 2 ≤ 2 / 3 * (fl - (k + r + 1) - (k * Ns + 1)) - k * Ns := by
  have hkN : k ≤ k * Ns := by nlinarith
  linarith

theorem natDiv_gt (n m : ℕ) (hm : 0 < m) : (n : ℝ) / (m : ℝ) - 1 < ((n / m : ℕ) : ℝ) := by
  have h := Nat.div_add_mod n m
  have hr := Nat.mod_lt n hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have e1 : (n : ℝ) = (m : ℝ) * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by exact_mod_cast h.symm
  have e2 : ((n % m : ℕ) : ℝ) < m := by exact_mod_cast hr
  rw [div_sub_one hm'.ne', div_lt_iff₀ hm']
  linarith

theorem threshold_power_bound_of_counts (C₀ : ℝ) (h41 : TopCountLowerBounds C₀) (hOld : OldestLetterInSegment) : ThresholdPowerLowerBound C₀ := by
  unfold ThresholdPowerLowerBound
  intro p n' r K _ _ _ X hX hC1 hC2 j bb hS x hx
  have b0 := basics hX
  have hO := hOld p n' r K X hX j x hx
  have hob := mem_letters_bounds hO.1
  have h41' := (h41 p n' r K X hX hC1 hC2).1 _ hob.2.2
  have hdeg := (hX.degs _ hob.2.2).1
  have hk : Dat.k (r := r) K = ((r : ℝ) + (K : ℝ)) := by unfold Dat.k; push_cast; rfl
  have hk5 : (5 : ℝ) ≤ ((r : ℝ) + (K : ℝ)) := hk ▸ b0.k5
  have hN := b0.Ns1
  have hY := b0.Y1
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := b0.p1.le
  have hRT := pow_Rj_le hX j
  have hRp : (0 : ℝ) ≤ (p : ℝ) ^ (X.Rj p K j) := by positivity
  have hTp : (0 : ℝ) ≤ Tj X p K j := hRp.trans hRT
  have hden := den_pos hX j
  have hTa : 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j = X.a := by
    rw [← hk]
    unfold Tj
    exact mul_div_cancel₀ _ hden.ne'
  have hEW : (X.F.dist j (X.F.oldest j x)) ≤ (X.F.dist j (X.F.fr (j - 1) 0)) := by
    unfold Frames.dist
    omega
  have hPe : (p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) ≤ (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) := pow_le_pow_right₀ hP1 hEW
  have hDpos : 0 < ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) := by positivity
  have hc : 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) ≤ (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by
    rw [le_div_iff₀ hDpos, pow_add]
    have hkN : 0 ≤ ((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ) := by positivity
    have h40 : (40 : ℝ) ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) := by nlinarith
    have h1 : 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right h40 hkN]
    have hq0 : 0 ≤ (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j := by positivity
    calc 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) * ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) * (p : ℝ) ^ (X.Rj p K j))
        ≤ 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) * ((p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hPe hRT hRp (by positivity)) (by positivity)
      _ ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j) := mul_le_mul_of_nonneg_right h1 hq0
      _ = X.a := by rw [← hTa]; ring
      _ ≤ ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) := hdeg
  have hq : 9 / 10 * (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) ≤ (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by
    calc 9 / 10 * (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) = (9 / 10 * ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ)) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) := by ring
      _ ≤ (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by gcongr
  have hsplit : ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / (p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) / 2 = (p : ℝ) ^ (X.Rj p K j) * ((((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) / 2) := by
    rw [pow_add]
    field_simp
  unfold Dat.th Dat.Bo Dat.thc
  rw [hsplit]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ hRp
  split_ifs with hW
  · have hfl := natDiv_gt (X.a' p K (posOf n' (X.F.oldest j x))) (p ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) (pow_pos (by have := hX.p13; omega) _)
    push_cast at hfl
    have := threshold_arith_w_case ((r : ℝ) + (K : ℝ)) (X.Ns : ℝ) (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) _ (r : ℝ) hk5 hN (by linarith) hc hq hfl
    unfold Dat.Bw Dat.m0
    push_cast
    have hcast : ((((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℤ) / ((p : ℤ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) : ℤ) : ℝ) = (((X.a' p K (posOf n' (X.F.oldest j x))) / p ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, ← Int.natCast_div, Int.cast_natCast]
    rw [hcast]
    linarith
  · have hb := hS _ (hO.2 hW)
    rw [hk] at hb
    have := threshold_arith_letter_case ((r : ℝ) + (K : ℝ)) (X.Ns : ℝ) (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) _ hk5 hN hc hq hb
    linarith

theorem order_numeric_bound_of_oldest (C₀ : ℝ) (hOld : OldestLetterInSegment) : OrderNumericBound C₀ := by
  unfold OrderNumericBound
  intro p n' r K _ _ _ X hX _ _ j x hx
  have b := basics hX
  have hO := hOld p n' r K X hX j x hx
  simp only [Dat.toLate, Finset.mem_filter] at hx
  have hxb := mem_letters_bounds hx.1
  have hob := mem_letters_bounds hO.1
  have hL : (X.L₁ : ℤ) < x - X.F.oldest j x := hX.valid.2.2.2.2.2.2.2.2 j x hx.1 hx.2
  have hde : X.F.dist j x + X.L₁ + 1 ≤ X.F.dist j (X.F.oldest j x) := by
    unfold Frames.dist
    omega
  have hew : X.F.dist j (X.F.oldest j x) ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    omega
  have hP : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hP0 : (0 : ℝ) < p := by linarith
  have hP1 : (1 : ℝ) ≤ p := by linarith
  have hk : (5 : ℝ) ≤ Dat.k (r := r) K := b.k5
  have hY := b.Y1
  have hNs := b.Ns1
  have hden := den_pos hX j
  have hTa : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j = X.a := by
    unfold Tj
    exact mul_div_cancel₀ _ hden.ne'
  have hRT := pow_Rj_le hX j
  have hRp : (0 : ℝ) ≤ (p : ℝ) ^ X.Rj p K j := by positivity
  have hTp : (0 : ℝ) ≤ Tj X p K j := hRp.trans hRT
  have ha : 0 ≤ X.a := hTa ▸ mul_nonneg hden.le hTp
  have hLd : (p : ℝ) ^ (X.L₁ + X.F.dist j x) ≤ (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) :=
    pow_le_pow_right₀ hP1 (by omega)
  have hLe : (p : ℝ) * (p : ℝ) ^ (X.L₁ + X.F.dist j x) ≤ (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hP1 (by omega)
  have hLpos : (0 : ℝ) < (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by positivity
  have hEpos : (0 : ℝ) < (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by positivity
  have hA : Dat.k (r := r) K * (p : ℝ) ^ X.Rj p K j ≤ X.a / (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by
    rw [le_div_iff₀ hLpos]
    have h8 : 1 ≤ 8 * X.Y * Dat.k (r := r) K * (X.Ns : ℝ) := by
      have : (1 : ℝ) ≤ X.Y * Dat.k (r := r) K := by nlinarith
      have : (1 : ℝ) ≤ X.Y * Dat.k (r := r) K * (X.Ns : ℝ) := by nlinarith
      linarith
    have hq : 0 ≤ Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by positivity
    calc Dat.k (r := r) K * (p : ℝ) ^ X.Rj p K j * (p : ℝ) ^ (X.L₁ + X.F.dist j x)
        ≤ Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hRT (by linarith)) hLd hLpos.le (by positivity)
      _ ≤ (8 * X.Y * Dat.k (r := r) K * (X.Ns : ℝ)) * (Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0)) := le_mul_of_one_le_left hq h8
      _ = X.a := by rw [← hTa]; ring
  have hB : (p : ℝ) ^ X.Rj p K j * (4 * X.a * ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x) + X.Rj p K j))⁻¹) ≤ X.a / (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by
    rw [pow_add, mul_inv, le_div_iff₀ hLpos]
    have hRpos : (0 : ℝ) < (p : ℝ) ^ X.Rj p K j := by positivity
    have e : (p : ℝ) ^ X.Rj p K j * (4 * X.a * (((p : ℝ) ^ X.F.dist j (X.F.oldest j x))⁻¹ * ((p : ℝ) ^ X.Rj p K j)⁻¹)) = 4 * X.a / (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by
      field_simp
    rw [e, div_mul_eq_mul_div, div_le_iff₀ hEpos]
    nlinarith [mul_le_mul_of_nonneg_left hLe ha, mul_nonneg (mul_nonneg ha hLpos.le) (by linarith : (0 : ℝ) ≤ p - 4)]
  have z1 : (p : ℝ) ^ (-((X.F.dist j (X.F.oldest j x) : ℤ) + (X.Rj p K j : ℤ))) = ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x) + X.Rj p K j))⁻¹ := by
    rw [← Nat.cast_add, zpow_neg, zpow_natCast]
  have z2 : (p : ℝ) ^ (-((X.L₁ : ℤ) + (X.F.dist j x : ℤ))) = ((p : ℝ) ^ (X.L₁ + X.F.dist j x))⁻¹ := by
    rw [← Nat.cast_add, zpow_neg, zpow_natCast]
  have hkne : Dat.k (r := r) K ≠ 0 := by linarith
  have hT1 : (p : ℝ) ^ X.Rj p K j * (X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j))) = X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ X.F.dist j x) := by
    rw [pow_add]
    field_simp
  rw [div_eq_mul_inv] at hA hB
  have hI : 0 ≤ X.a * ((p : ℝ) ^ (X.L₁ + X.F.dist j x))⁻¹ := mul_nonneg ha (inv_nonneg.mpr hLpos.le)
  unfold Dat.oc Dat.o
  push_cast
  rw [z1, z2, mul_add, hT1]
  split_ifs <;> linarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FiniteRestrictSupport
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem finite_restrictSupport' (R : Type) [CommRing R] (σ : Type) (s : Set (σ →₀ ℕ)) (hs : s.Finite) :
    (restrictSupport R s : Submodule R (MvPolynomial σ R)).FG := by
  have heq : (restrictSupport R s : Submodule R (MvPolynomial σ R)) =
      Submodule.span R ((fun m => (monomial m (1 : R) : MvPolynomial σ R)) '' s) := by
    apply le_antisymm
    · intro P hP
      rw [MvPolynomial.mem_restrictSupport_iff] at hP
      rw [P.as_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      have : (monomial m (AddMonoidAlgebra.coeff P m) : MvPolynomial σ R) = AddMonoidAlgebra.coeff P m • monomial m (1 : R) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hP (by exact_mod_cast hm), rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
      intro m' hm'
      have := MvPolynomial.support_monomial_subset (by exact_mod_cast hm')
      rw [Finset.mem_singleton] at this
      rw [this]; exact hm
  rw [heq]
  exact Submodule.fg_span (hs.image _)

theorem segDegSet_finite {r : ℕ} (K : ℕ) (b : ℤ → ℕ) (L : Finset ℤ) (hb : ∀ x, x ∉ L → b x = 0) :
    (Dat.segDegSet (r := r) K b).Finite := by
  classical
  let B : ℤ × Fin (r + K) →₀ ℕ := Finsupp.onFinset (L ×ˢ Finset.univ) (fun v => b v.1) (by
    intro v hv
    by_contra h
    apply hv
    apply hb
    intro hL
    exact h (Finset.mem_product.mpr ⟨hL, Finset.mem_univ _⟩))
  refine (Set.finite_Iic B).subset ?_
  intro m hm v
  have h := hm v.1
  have : m (v.1, v.2) ≤ ∑ c : Fin (r + K), m (v.1, c) :=
    Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
  rw [h] at this
  simpa [B] using this

theorem restFin : RestFin := by
  intro p n' r K _ _ _ X O _ _ _ j b hb
  have hfg := finite_restrictSupport' O (ℤ × Fin (r + K)) _ (segDegSet_finite (r := r) K b (X.F.letters j) hb)
  have hN : IsNoetherian O (restrictSupport O (Dat.segDegSet (r := r) K b) : Submodule O (SegRing O r K)) :=
    isNoetherian_of_fg_of_noetherian _ hfg
  have hle : X.Mj p K O j b ≤ restrictSupport O (Dat.segDegSet (r := r) K b) := by
    intro P hP
    exact hP.1.2
  have : IsNoetherian O (X.Mj p K O j b) := isNoetherian_of_le hle
  infer_instance

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AtypicalPathSmallWeight
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def beA (n0 : ℕ) (B : Fin N → ℕ) : ℕ := ∑ i : Fin N, if i.val < n0 then B i else 0

structure IsPATHa (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ)
    (dd : Fin N → ℕ) : Prop where
  path : ∃ P : PPath (r + K) N LL dd, P.mu = μ
  degs : ∀ i : Fin N, i.val < n0 → dd i = B i
  head : ∀ (i : Fin N) (m : Fin (r + K)), n0 ≤ i.val → m.val ≤ i.val - n0 → μ i.succ m = (beA n0 B : ℤ)

def posS {n : ℕ} (la : Fin n → ℤ) : ℤ := ∑ m, max (la m) 0

def negS {n : ℕ} (la : Fin n → ℤ) : ℤ := ∑ m, max (-la m) 0

def Xi (r K : ℕ) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ) (i : Fin N) : ℝ := La * bb i / ((p : ℝ) * ((r + K : ℕ) : ℝ))

def Typ [NeZero r] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ)
    (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin N,
    (LL.vec i = false → ((posS (μ i.castSucc) - posS (μ i.succ) : ℤ) : ℝ) ≤ Xi r K bb La p i) ∧
    (LL.vec i = true → r ≤ i.val → ((negS (μ i.castSucc) - negS (μ i.succ) : ℤ) : ℝ) ≤ Xi r K bb La p i) ∧
    (r ≤ i.val → (2 / 3 : ℝ) * (B (od i) : ℝ) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ))

def GoodA [NeZero r] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ)
    (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin N, r ≤ i.val →
    (2 / 3 : ℝ) * (B (od i) : ℝ) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ) ∧
    (LL.vec i = true → ((∑ c, (tanPart μ i.succ c - tanPart μ i.castSucc c) : ℤ) : ℝ) ≤
      Xi r K bb La p i + 2 * (B (od i) : ℝ)) ∧
    (LL.vec i = false → ((∑ c, (plPart μ i.castSucc c - plPart μ i.succ c) : ℤ) : ℝ) ≤ Xi r K bb La p i)

def rkA (r K n0 : ℕ) (B : Fin N → ℕ) : ℕ :=
  ∏ i : Fin N, if i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1

structure HypT (N n0 r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ) : Prop where
  hN : N = n0 + r
  r1 : 1 ≤ r
  a3 : 3 ≤ a
  p13 : 13 ≤ p
  H1 : ∀ i : Fin N, i.val < n0 → ((r + K : ℕ) : ℝ) ≤ (B i : ℝ) ∧ (B i : ℝ) ≤ 2 * a
  H2 : ∀ i i' : Fin N, i < i' → i'.val < n0 → LL.vec i = LL.vec i' → (p : ℝ) ^ 2 / 5 * (B i : ℝ) ≤ (B i' : ℝ)
  vec_true_of_early : ∀ i : Fin N, i.val < r → LL.vec i = true
  vec_true_of_late : ∀ i : Fin N, n0 ≤ i.val + r → LL.vec i = true
  two_r_le_n0 : 2 * r ≤ n0
  N_add_r_le_K : N + r ≤ K
  H4 : ((r + K : ℕ) : ℝ) / 2 ≤ (K : ℝ) - 2 * (N : ℝ)
  N_le_a : (N : ℝ) ≤ a
  od_lt : ∀ i : Fin N, r ≤ i.val → od i < i
  od_vec : ∀ i : Fin N, r ≤ i.val → LL.vec (od i) = true
  od_card : ∀ i : Fin N, r ≤ i.val →
    (Finset.univ.filter fun l : Fin N => od i ≤ l ∧ l < i ∧ LL.vec l = true).card = r
  bb_pos : ∀ i : Fin N, r ≤ i.val → 0 < bb i
  bb_le : ∀ i l : Fin N, r ≤ i.val → l < i → l.val < n0 → (B l : ℝ) ≤ 4 * bb i / (p : ℝ)
  La_pos : 0 < La

def ell0 (N : ℕ) (a : ℝ) : ℝ := Real.log (1 + 2 * a * (N : ℝ))

abbrev QT (N r K : ℕ) := (Fin (N + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K))

def SP (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) : Set (Fin (N + 1) → Fin (r + K) → ℤ) :=
  {μ | ∃ dd, IsPATHa LL n0 B μ dd}

def SAll (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) : Set (QT N r K) :=
  {q | q.1 ∈ SP LL n0 B ∧ IsSt (tanPart q.1) q.2}

def SGood [NeZero r] (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ)
    (p : ℕ) : Set (QT N r K) :=
  {q | q.1 ∈ SP LL n0 B ∧ GoodA LL B od bb La p q.1 ∧ IsSt (tanPart q.1) q.2}

def PathWeightEqRank : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SAll (r := r) (K := K) LL n0 B).Finite ∧ (SAll (r := r) (K := K) LL n0 B).ncard = rkA r K n0 B

def PathCountFinite : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SP (r := r) (K := K) LL n0 B).Finite ∧
      ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) ≤ Real.exp (2 * (N : ℝ) ^ 2 * ell0 N a)

def AtypicalPathSmallWeight : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    ∀ μ ∈ SP (r := r) (K := K) LL n0 B, ¬ Typ LL B od bb La p μ →
      (({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).ncard : ℝ) ≤
        Real.exp (9 * (N : ℝ) ^ 2 * ell0 N a -
          min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12)) * (rkA r K n0 B : ℝ)

def TypicalPathOrdersSmall : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    ∀ μ ∈ SP (r := r) (K := K) LL n0 B, Typ LL B od bb La p μ → GoodA LL B od bb La p μ

def LemT : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SGood (r := r) (K := K) LL n0 B od bb La p).Finite ∧
      (1 - Real.exp (11 * (N : ℝ) ^ 2 * ell0 N a - min La ((r + K : ℕ) : ℝ) / 32)) * (rkA r K n0 B : ℝ) ≤
        ((SGood (r := r) (K := K) LL n0 B od bb La p).ncard : ℝ)

theorem lemT_of (ha : PathWeightEqRank) (hb : PathCountFinite) (hc : AtypicalPathSmallWeight) (hd : TypicalPathOrdersSmall) : LemT := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  obtain ⟨hfin, hcard⟩ := ha N n0 r K LL B od bb a La p H
  obtain ⟨hPfin, hPcard⟩ := hb N n0 r K LL B od bb a La p H
  have hc' := hc N n0 r K LL B od bb a La p H
  have hd' := hd N n0 r K LL B od bb a La p H
  set SA := SAll (r := r) (K := K) LL n0 B with hSA
  set SG := SGood (r := r) (K := K) LL n0 B od bb La p with hSG
  have hGA : SG ⊆ SA := fun q hq => ⟨hq.1, hq.2.2⟩
  have hGfin : SG.Finite := hfin.subset hGA
  refine ⟨hGfin, ?_⟩
  let SB : Set (QT N r K) := {q | q ∈ SA ∧ ¬ Typ LL B od bb La p q.1}
  have hBfin : SB.Finite := hfin.subset fun q hq => hq.1
  have hcov : SA ⊆ SG ∪ SB := by
    intro q hq
    by_cases ht : Typ LL B od bb La p q.1
    · exact Or.inl ⟨hq.1, hd' q.1 hq.1 ht, hq.2⟩
    · exact Or.inr ⟨hq, ht⟩
  have h1 : SA.ncard ≤ SG.ncard + SB.ncard :=
    le_trans (Set.ncard_le_ncard hcov (hGfin.union hBfin)) (Set.ncard_union_le _ _)
  set cR : ℝ := Real.exp (9 * (N : ℝ) ^ 2 * ell0 N a -
          min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12)) * (rkA r K n0 B : ℝ) with hcR
  have hcR0 : 0 ≤ cR := by positivity

  have h2 : (SB.ncard : ℝ) ≤ ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) * cR := by
    rw [Set.ncard_eq_toFinset_card _ hBfin, Set.ncard_eq_toFinset_card _ hPfin]
    have hmaps : ∀ q ∈ hBfin.toFinset, q.1 ∈ hPfin.toFinset := by
      intro q hq
      rw [Set.Finite.mem_toFinset] at hq ⊢
      exact hq.1.1
    have hfib : ∀ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ) ≤ cR := by
      intro μ hμ
      rw [Set.Finite.mem_toFinset] at hμ
      by_cases ht : Typ LL B od bb La p μ
      · have : hBfin.toFinset.filter (fun q => q.1 = μ) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro q hq hqμ
          rw [Set.Finite.mem_toFinset] at hq
          exact hq.2 (hqμ ▸ ht)
        rw [this]; simpa using hcR0
      · refine le_trans ?_ (hc' μ hμ ht)
        have hIfin : ({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).Finite := by
          refine (hfin.image Prod.snd).subset ?_
          intro I hI
          exact ⟨(μ, I), ⟨hμ, hI⟩, rfl⟩
        rw [Set.ncard_eq_toFinset_card _ hIfin]
        have : (hBfin.toFinset.filter fun q => q.1 = μ).card ≤ hIfin.toFinset.card := by
          refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
          · intro q hq
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.Finite.mem_toFinset] at hq
            simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
            have := hq.1.1.2
            rwa [hq.2] at this
          · intro q hq q' hq' hqq
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hq'
            exact Prod.ext (hq.2.trans hq'.2.symm) hqq
        exact_mod_cast this
    have hsum : (hBfin.toFinset.card : ℝ) =
        ∑ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := hBfin.toFinset) (t := hPfin.toFinset)
        (fun q hq => hmaps q hq)
      rw [this]; push_cast; rfl
    rw [hsum]
    calc ∑ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ)
        ≤ ∑ _μ ∈ hPfin.toFinset, cR := Finset.sum_le_sum hfib
      _ = (hPfin.toFinset.card : ℝ) * cR := by rw [Finset.sum_const, nsmul_eq_mul]

  have hk0 : (0 : ℝ) < ((r + K : ℕ) : ℝ) := by
    have : 0 < r + K := by have := H.r1; omega
    exact_mod_cast this
  have hmin : min La ((r + K : ℕ) : ℝ) / 32 ≤
      min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12) := by
    have hH4 := H.H4
    refine le_min ?_ ?_
    · have h3 : La / 32 ≤ La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have := mul_le_mul_of_nonneg_left hH4 H.La_pos.le
        nlinarith
      exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) h3
    · have h3 : ((r + K : ℕ) : ℝ) / 32 ≤ ((K : ℝ) - 2 * N) / 12 := by linarith
      exact le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) h3
  have hrk0 : (0 : ℝ) ≤ (rkA r K n0 B : ℝ) := Nat.cast_nonneg _
  have h3 : (SB.ncard : ℝ) ≤
      Real.exp (11 * (N : ℝ) ^ 2 * ell0 N a - min La ((r + K : ℕ) : ℝ) / 32) * (rkA r K n0 B : ℝ) := by
    refine le_trans h2 (le_trans (mul_le_mul_of_nonneg_right hPcard hcR0) ?_)
    rw [hcR, ← mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hrk0
    linarith
  have h1' : (rkA r K n0 B : ℝ) ≤ (SG.ncard : ℝ) + (SB.ncard : ℝ) := by
    rw [← hcard]; exact_mod_cast h1
  linarith

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end
