module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLe

@[expose] public section

section -- merged from Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLp
noncomputable section

namespace Formalism.MainNotions.J

open Finset Matrix

section Pattern

variable {n : ℕ} {F : Type} [Field F]

def Pat (S : Finset (Fin n × Fin n)) (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, (i, j) ∉ S → A i j = if i = j then 1 else 0

theorem pat_det (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) (A : Matrix (Fin n) (Fin n) F)
    (h : Pat S A) : A.det = 1 := by
  have ht : A.BlockTriangular id := by
    intro i j hij
    have hn : (i, j) ∉ S := fun hm => absurd (hS _ hm) (not_lt.mpr (le_of_lt hij))
    have hij' : j < i := hij
    rw [h i j hn, if_neg (ne_of_gt hij')]
  rw [Matrix.det_of_isUpperTriangular ht]
  refine Finset.prod_eq_one fun i _ => ?_
  have hn : (i, i) ∉ S := fun hm => lt_irrefl _ (hS _ hm)
  rw [h i i hn, if_pos rfl]

def patMat (S : Finset (Fin n × Fin n)) (φ : S → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if h : (i, j) ∈ S then φ ⟨(i, j), h⟩ else if i = j then 1 else 0

theorem patMat_pat (S : Finset (Fin n × Fin n)) (φ : S → F) : Pat S (patMat S φ) := fun i j h => by
  simp [patMat, h]

def patEquiv (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) :
    {A : GL (Fin n) F // Pat S (A : Matrix (Fin n) (Fin n) F)} ≃ (S → F) where
  toFun A := fun p => (A.1 : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2
  invFun φ := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (patMat S φ)
    (by rw [pat_det S hS _ (patMat_pat S φ)]; exact one_ne_zero), patMat_pat S φ⟩
  left_inv A := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    show patMat S (fun p => (A.1 : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2) i j = (A.1 : Matrix (Fin n) (Fin n) F) i j
    by_cases h : (i, j) ∈ S
    · simp [patMat, h]
    · simp [patMat, h, A.2 i j h]
  right_inv φ := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    show patMat S φ i j = _
    simp [patMat, h]

theorem card_pat [Finite F] (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) :
    Nat.card {A : GL (Fin n) F // Pat S (A : Matrix (Fin n) (Fin n) F)} = Nat.card F ^ S.card := by
  rw [Nat.card_congr (patEquiv S hS), Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]

end Pattern

def upS (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

theorem card_upS (n : ℕ) : (upS n).card = n * (n - 1) / 2 := by
  unfold upS
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have : ∀ j : Fin n, (∑ i : Fin n, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have : (univ.filter fun i : Fin n => i < j) = Finset.Iio j := by ext; simp
    rw [this, Fin.card_Iio]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

def rowS (k rS n : ℕ) : Finset (Fin n × Fin n) :=
  (upS n).filter fun p => ¬ (p.2.val = rS + k ∧ rS ≤ p.1.val)

theorem card_rowS (k rS n : ℕ) (hn : rS + k < n) : (rowS k rS n).card + k = n * (n - 1) / 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := upS n)
    (fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val)
  rw [card_upS] at h
  have hk : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val).card = k := by
    have : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val) =
        (univ : Finset (Fin k)).image fun i => ((⟨rS + i.val, by omega⟩ : Fin n), (⟨rS + k, hn⟩ : Fin n)) := by
      ext ⟨a, b⟩
      simp only [upS, mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨hab, hb, ha⟩
        have hab' : a.val < b.val := hab
        exact ⟨⟨a.val - rS, by omega⟩, Fin.ext (by simp; omega), Fin.ext (by simp [hb])⟩
      · rintro ⟨i, rfl, rfl⟩
        refine ⟨?_, rfl, by simp⟩
        show rS + i.val < rS + k
        omega
    rw [this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro i j hij
    have := congrArg (fun p : Fin n × Fin n => p.1.val) hij
    simp at this
    exact Fin.ext this
  unfold rowS
  omega

theorem isUnitri_iff {n : ℕ} {F : Type} [Field F] (A : Matrix (Fin n) (Fin n) F) :
    StandardLattice.IsUnitri A ↔ Pat (upS n) A := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    simp only [upS, mem_filter, mem_univ, true_and, not_lt] at hij
    rcases eq_or_lt_of_le hij with h | h
    · subst h; simp [h2]
    · rw [h1 i j h, if_neg (ne_of_gt h)]
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [h i j (by simp [upS, le_of_lt hij]), if_neg (ne_of_gt hij)]
    · rw [h i i (by simp [upS]), if_pos rfl]

theorem isRowLev_iff {n : ℕ} {F : Type} [Field F] (k rS : ℕ) (A : Matrix (Fin n) (Fin n) F) :
    StandardLattice.IsRowLev k rS A ↔ Pat (rowS k rS n) A := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ i j hij
    by_cases e : i = j
    · subst e; simp [h2]
    rw [if_neg e]
    have e' : i.val ≠ j.val := fun h => e (Fin.ext h)
    simp only [rowS, upS, mem_filter, mem_univ, true_and, not_and] at hij
    by_cases hlt : i < j
    · obtain ⟨hj, hi⟩ : j.val = rS + k ∧ rS ≤ i.val := by
        by_contra hc
        exact hij hlt (fun a b => hc ⟨a, b⟩)
      have hlt' : i.val < j.val := hlt
      exact h4 i j hj e (by unfold StandardLattice.blk; split_ifs <;> omega)
    · have hlt' : j.val < i.val := by
        have : ¬ i.val < j.val := hlt
        omega
      by_cases hb : StandardLattice.blk rS k j.val < StandardLattice.blk rS k i.val
      · exact h1 i j hb
      · refine h3 i j ?_ hlt'
        revert hb
        unfold StandardLattice.blk
        split_ifs <;> omega
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hb hij => ?_, fun i j hj hne hb => ?_⟩
    · have hlt : j.val < i.val := by
        revert hij
        unfold StandardLattice.blk
        split_ifs <;> omega
      have hlt2 : ¬ i < j := fun hh => by
        have : i.val < j.val := hh
        omega
      rw [h i j (by simp [rowS, upS, hlt2]), if_neg (fun e => by subst e; omega)]
    · rw [h i i (by simp [rowS, upS]), if_pos rfl]
    · have hlt2 : ¬ i < j := not_lt.mpr (le_of_lt hij)
      rw [h i j (by simp [rowS, upS, hlt2]), if_neg (ne_of_gt hij)]
    · have hi : rS ≤ i.val := by
        revert hb
        unfold StandardLattice.blk
        split_ifs <;> omega
      rw [h i j (by simp [rowS, hj, hi]), if_neg hne]

end Formalism.MainNotions.J

end
end

noncomputable section

namespace Formalism.MainNotions.J

open Finset NumberField IsDedekindDomain Formalism.BasicNotions

theorem card_GL_real (g n : ℕ) [Fact g.Prime] :
    (Nat.card (GL (Fin n) (ZMod g)) : ℝ) = LocalBesselAndTopKernel.cardGL (g : ℝ) n := by
  rw [Matrix.card_GL_field, ZMod.card]
  unfold LocalBesselAndTopKernel.cardGL
  rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => ((g ^ n - g ^ i : ℕ) : ℝ)) n]
  refine prod_congr rfl fun i hi => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right (Fact.out : g.Prime).pos (le_of_lt (mem_range.mp hi)))]
  push_cast
  rfl

theorem cardGL_factor (q : ℝ) (k : ℕ) :
    LocalBesselAndTopKernel.cardGL q k = q ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 1 k, (q ^ i - 1) := by
  unfold LocalBesselAndTopKernel.cardGL
  have h1 : ∀ i ∈ range k, q ^ k - q ^ i = q ^ i * (q ^ (k - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := mem_range.mp hi
    have : k = i + (k - 1 - i + 1) := by omega
    conv_lhs => rw [this, pow_add]
    ring
  rw [prod_congr rfl h1, prod_mul_distrib, prod_pow_eq_pow_sum, sum_range_id,
    prod_range_reflect (fun j => q ^ (j + 1) - 1) k]
  congr 1
  rw [range_eq_Ico, prod_Ico_add' (fun j => q ^ j - 1) 0 k 1]
  refine prod_congr ?_ fun _ _ => rfl
  ext x
  simp only [mem_Ico, mem_Icc]
  omega

theorem idxColLoc_eq (g k : ℕ) [Fact g.Prime] :
    StandardLattice.idxColLoc g k = ∏ i ∈ Finset.Icc 1 k, ((g : ℝ) ^ i - 1) := by
  unfold StandardLattice.idxColLoc StandardLattice.idxLoc
  have hc : Nat.card {A : GL (Fin k) (ZMod g) // StandardLattice.IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      g ^ (k * (k - 1) / 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun A : GL (Fin k) (ZMod g) =>
      isUnitri_iff (A : Matrix (Fin k) (Fin k) (ZMod g))), card_pat _ (by simp [upS]), card_upS, Nat.card_zmod]
  have hg : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  rw [card_GL_real, hc, cardGL_factor, Nat.cast_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hg)]

theorem dim_arith (k r c : ℕ) (h : c + k = (k + 2 * r + 1) * (k + 2 * r + 1 - 1) / 2) :
    c = r * (2 * k + 2 * r + 1) + k * (k - 1) / 2 := by
  rcases k with _ | k
  · have e : (0 + 2 * r + 1) * (0 + 2 * r + 1 - 1) = 2 * (r * (2 * 0 + 2 * r + 1)) + 0 := by
      simp only [Nat.add_sub_cancel]; ring
    rw [e, Nat.mul_add_div (by norm_num)] at h
    omega
  · have e : (k + 1 + 2 * r + 1) * (k + 1 + 2 * r + 1 - 1) =
        2 * (r * (2 * (k + 1) + 2 * r + 1) + (k + 1)) + (k + 1) * (k + 1 - 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [e, Nat.mul_add_div (by norm_num)] at h
    omega

theorem idxRowLoc_eq (g k m : ℕ) [Fact g.Prime] (hm : Even m) (h2 : 2 ≤ m) :
    StandardLattice.idxRowLoc g k m = LocalBesselAndTopKernel.cardGL (g : ℝ) (k + m - 1) /
      ((g : ℝ) ^ ((m / 2 - 1) * (2 * k + 2 * (m / 2 - 1) + 1)) * (g : ℝ) ^ (k * (k - 1) / 2)) := by
  unfold StandardLattice.idxRowLoc StandardLattice.idxLoc
  obtain ⟨a, rfl⟩ := hm
  have ha : (a + a) / 2 - 1 = a - 1 := by omega
  have hn : k + (a + a) - 1 = k + 2 * (a - 1) + 1 := by omega
  have hc : Nat.card {A : GL (Fin (k + (a + a) - 1)) (ZMod g) //
      StandardLattice.IsRowLev k ((a + a) / 2 - 1) (A : Matrix (Fin (k + (a + a) - 1)) (Fin (k + (a + a) - 1)) (ZMod g))} =
      g ^ (((a + a) / 2 - 1) * (2 * k + 2 * ((a + a) / 2 - 1) + 1) + k * (k - 1) / 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun A : GL (Fin (k + (a + a) - 1)) (ZMod g) =>
      isRowLev_iff k ((a + a) / 2 - 1) (A : Matrix (Fin (k + (a + a) - 1)) (Fin (k + (a + a) - 1)) (ZMod g))),
      card_pat _ (by simp only [rowS, upS, mem_filter, mem_univ, true_and]; exact fun p hp => hp.1), Nat.card_zmod]
    congr 1
    have h := card_rowS k ((a + a) / 2 - 1) (k + (a + a) - 1) (by omega)
    rw [ha] at h ⊢
    rw [hn] at h ⊢
    exact dim_arith k (a - 1) _ h
  rw [card_GL_real, hc, Nat.cast_pow, pow_add]

theorem finprod_typed (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) (φ : ℕ → ℝ) :
    ∏ᶠ p ∈ S.typedPl D, φ (Ideal.absNorm p.asIdeal) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  have hf : D.R.f ≠ 0 := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hfin : ∀ i, ({p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}).Finite := by
    intro i
    have hc := (h i).1
    have hF : Finite {p : HeightOneSpectrum (𝓞 D.host.F) // ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact hf)
    exact Set.finite_coe_iff.mp hF
  have hone : ∀ i, ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal) = φ (D.host.g i) ^ D.R.f := by
    intro i
    have e : ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
        φ (Ideal.absNorm p.asIdeal) =
        ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
          φ (D.host.g i) :=
      finprod_mem_congr rfl fun p hp => by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, (h i).2 p hp]
    rw [e, finprod_mem_eq_finite_toFinset_prod _ (hfin i), Finset.prod_const,
      ← Set.ncard_eq_toFinset_card _ (hfin i), ← Nat.card_coe_set_eq]
    exact congrArg _ (h i).1
  have hdis : Disjoint {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}
      {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} := by
    refine Set.disjoint_left.mpr fun p h0 h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
      (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).mpr D.host.g_ne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hab' : (a : 𝓞 D.host.F) * ((D.host.g 0 : ℕ) : 𝓞 D.host.F) + (b : 𝓞 D.host.F) * ((D.host.g 1 : ℕ) : 𝓞 D.host.F) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.F) hab
    rw [← hab']
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)
  have hU : S.typedPl D = {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} ∪
      {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} := rfl
  rw [hU, finprod_mem_union hdis (hfin 0) (hfin 1), hone 0, hone 1]

theorem idxColTie_of (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) : IdxColTie D := by
  have : ∀ i, Fact (D.host.g i).Prime := fun i => ⟨D.host.g_prime i⟩
  unfold IdxColTie StandardLattice.idxPi S.gaG
  rw [finprod_typed D h (fun N => ∏ i ∈ Finset.Icc 1 D.R.k, ((N : ℝ) ^ i - 1)), idxColLoc_eq, idxColLoc_eq]

theorem idxRowTie_of (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) : IdxRowTie D := by
  have : ∀ i, Fact (D.host.g i).Prime := fun i => ⟨D.host.g_prime i⟩
  unfold IdxRowTie StandardLattice.idxSig LocalBesselAndTopKernel.idxRows
  rw [finprod_typed D h (fun N => LocalBesselAndTopKernel.cardGL (N : ℝ) D.R.r /
    ((N : ℝ) ^ LocalBesselAndTopKernel.dimNS D * (N : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))),
    idxRowLoc_eq _ _ _ D.R.m_even D.R.two_le_m, idxRowLoc_eq _ _ _ D.R.m_even D.R.two_le_m]
  rfl

end Formalism.MainNotions.J

end
