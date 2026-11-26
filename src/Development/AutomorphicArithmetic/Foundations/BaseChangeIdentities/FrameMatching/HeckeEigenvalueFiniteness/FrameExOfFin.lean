module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ChoiceT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsolateRepresentationAtCharacter
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.MuVal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IsHeckeFsum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.InertInSecAlt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.ExTbOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.FrameInertAll
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertEigenvalues.EigInert
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryModelHolds

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.SumPairSignEqRho
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F

namespace PositivityTheory.Rg.BcB.F.Choice.IndefiniteRowSideFullHecke

theorem coneTwo' : ConeTwo := by
  intro n x _ hx
  have hx' : ∀ i j : Fin n, i < j → x j + 2 ≤ x i := hx
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hi := i.isLt
    have hj := j.isLt
    have h1 := hx' ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (by show i.val < j.val; omega)
    have h2 := hx' ⟨n - 1 - j.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩ (by show n - 1 - j.val < n - 1 - i.val; omega)
    simp only [lOf]
    omega
  · have hi := i.isLt
    have h1 := hx' ⟨i.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩ (by show i.val < n - 1 - i.val; omega)
    simp only [lOf]
    omega

theorem shufStd' : ShufStd := by
  intro E _ _ _ w n a s h e he k
  rfl

theorem shufEx' : ShufEx := by
  intro n a s h
  have hp := h.1.2.2
  constructor
  · rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at h1 h2
    have := k.isLt
    rcases h1 with ⟨p, hp1⟩ | ⟨p, hp1⟩ | ⟨m1, m2, m3⟩ <;> rcases h2 with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q1, q2, q3⟩ <;>
      first | omega | exact hq hp1
  · ext k
    simp only [symIdx, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, iff_true]
    have := k.isLt
    by_cases h1 : k.val < n / 2
    · by_cases h2 : (⟨k.val, h1⟩ : Fin (n / 2)) ∈ s
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · by_cases h3 : n - 1 - k.val < n / 2
      · by_cases h2 : (⟨n - 1 - k.val, h3⟩ : Fin (n / 2)) ∈ s
        · exact Or.inl (Or.inr (Or.inl ⟨h3, h2⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨h3, h2⟩))
      · have hk : k.val = n / 2 := by omega
        have hn : n % 2 = 1 := by omega
        by_cases ha : a % 2 = 1
        · exact Or.inl (Or.inr (Or.inr ⟨ha, hn, hk⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, hn, hk⟩))

def sgn2 {N : ℕ} (i j : Fin N) : ℤ := (if i < j then 1 else 0) - (if j < i then 1 else 0)

theorem pair_sign_antisymm {N : ℕ} (i j : Fin N) : sgn2 i j = - sgn2 j i := by
  unfold sgn2; ring

theorem sum_pair_sign_eq_rho {N : ℕ} (i : Fin N) : ∑ j, sgn2 i j = rh N i := by
  unfold sgn2 rh
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio,
    Fin.card_Ioi, Fin.card_Iio]
  have := i.isLt
  omega

theorem pair_sign_strictMono {N M : ℕ} {f : Fin N → Fin M} (hf : StrictMono f) (i j : Fin N) : sgn2 (f i) (f j) = sgn2 i j := by
  unfold sgn2; simp only [hf.lt_iff_lt]

def lo (n : ℕ) (i : Fin (n / 2)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def hi (n : ℕ) (i : Fin (n / 2)) : Fin n := ⟨n - 1 - i.val, by have := i.isLt; omega⟩
def md (n : ℕ) (t : Fin (n % 2)) : Fin n := ⟨n / 2 + t.val, by have := t.isLt; omega⟩

theorem sum_split {n : ℕ} (f : Fin n → ℤ) :
    ∑ k, f k = ∑ i, (f (lo n i) + f (hi n i)) + ∑ t, f (md n t) := by
  let φ : Fin (n / 2) ⊕ (Fin (n / 2) ⊕ Fin (n % 2)) → Fin n := Sum.elim (lo n) (Sum.elim (hi n) (md n))
  have hφ : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩
    rintro (i | i | t) (j | j | u) h <;>
      simp only [φ, Sum.elim_inl, Sum.elim_inr, lo, hi, md, Fin.ext_iff, Fin.val_mk, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at h ⊢ <;>
      first
      | omega
      | (have := i.isLt; have := j.isLt; omega)
      | (have := i.isLt; have := u.isLt; omega)
      | (have := t.isLt; have := j.isLt; omega)
      | (have := t.isLt; have := u.isLt; omega)
  rw [← Fintype.sum_bijective φ hφ (fun p => f (φ p)) f (fun _ => rfl), Fintype.sum_sum_type, Fintype.sum_sum_type,
    Finset.sum_add_distrib, add_assoc]
  rfl

theorem mem_lo {n : ℕ} (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) (i : Fin (n / 2)) :
    lo n i ∈ symIdx n mid s ↔ i ∈ s := by
  have := i.isLt
  simp only [symIdx, lo, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, _⟩ | ⟨_, _, h⟩)
    · exact h
    · omega
    · omega
  · intro h; exact Or.inl ⟨i.isLt, h⟩

theorem mem_hi {n : ℕ} (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) (i : Fin (n / 2)) :
    hi n i ∈ symIdx n mid s ↔ i ∈ s := by
  have := i.isLt
  simp only [symIdx, hi, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, h⟩ | ⟨_, _, h⟩)
    · omega
    · have e : (⟨n - 1 - (n - 1 - i.val), h1⟩ : Fin (n / 2)) = i := Fin.ext (by show n - 1 - (n - 1 - i.val) = i.val; omega)
      rwa [e] at h
    · omega
  · intro h
    refine Or.inr (Or.inl ⟨by omega, ?_⟩)
    convert h using 1
    exact Fin.ext (by show n - 1 - (n - 1 - i.val) = i.val; omega)

theorem mem_md {n : ℕ} (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) (t : Fin (n % 2)) :
    md n t ∈ symIdx n mid s ↔ mid := by
  have := t.isLt
  simp only [symIdx, md, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h, _, _⟩)
    · omega
    · omega
    · exact h
  · intro h; exact Or.inr (Or.inr ⟨h, by omega, by omega⟩)

theorem sum_oe {n m : ℕ} (S : Finset (Fin n)) (h : S.card = m) (g : Fin n → ℤ) :
    ∑ i, g (S.orderEmbOfFin h i) = ∑ k ∈ S, g k := by
  rw [← Finset.sum_coe_sort S g]
  exact Fintype.sum_equiv (S.orderIsoOfFin h).toEquiv _ _ (fun i => rfl)

theorem blocks {n a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) (hL : StrictMono fun i => e (Sum.inl i))
    (hR : StrictMono fun j => e (Sum.inr j)) (x : Fin n → ℤ) :
    ∑ k : Fin n, (rh n k - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin b => rh b j) (e.symm k)) * x k =
      ∑ i, ∑ j, (x (e (Sum.inl i)) - x (e (Sum.inr j))) * sgn2 (e (Sum.inl i)) (e (Sum.inr j)) := by
  have hn : ∀ k : Fin n, rh n k = ∑ i, sgn2 k (e (Sum.inl i)) + ∑ j, sgn2 k (e (Sum.inr j)) := by
    intro k
    rw [← sum_pair_sign_eq_rho k, ← Fintype.sum_sum_type (f := fun p => sgn2 k (e p))]
    exact (Fintype.sum_equiv e (fun p => sgn2 k (e p)) (fun j => sgn2 k j) (fun _ => rfl)).symm
  have ha : ∀ i : Fin a, rh a i = ∑ i', sgn2 (e (Sum.inl i)) (e (Sum.inl i')) := fun i => by
    rw [← sum_pair_sign_eq_rho i]; exact Finset.sum_congr rfl (fun i' _ => (pair_sign_strictMono hL i i').symm)
  have hb : ∀ j : Fin b, rh b j = ∑ j', sgn2 (e (Sum.inr j)) (e (Sum.inr j')) := fun j => by
    rw [← sum_pair_sign_eq_rho j]; exact Finset.sum_congr rfl (fun j' _ => (pair_sign_strictMono hR j j').symm)
  rw [← Fintype.sum_equiv e (fun p => (rh n (e p) - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin b => rh b j)
      (e.symm (e p))) * x (e p))
    (fun k : Fin n => (rh n k - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin b => rh b j) (e.symm k)) * x k) (fun _ => rfl)]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hn, ha, hb, add_sub_cancel_left, add_sub_cancel_right, Finset.sum_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin b))), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pair_sign_antisymm (e (Sum.inr j))]; ring

theorem sum_ind {α : Type} [Fintype α] [DecidableEq α] (S : Finset α) (g : α → ℤ) :
    ∑ k ∈ S, g k = ∑ k, if k ∈ S then g k else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem lo_lt_lo {n : ℕ} (i j : Fin (n / 2)) : lo n i < lo n j ↔ i < j := by
  simp only [Fin.lt_def, lo]

theorem hi_lt_hi {n : ℕ} (i j : Fin (n / 2)) : hi n i < hi n j ↔ j < i := by
  have := i.isLt; have := j.isLt
  simp only [Fin.lt_def, hi]; omega

theorem lo_lt_hi {n : ℕ} (i j : Fin (n / 2)) : lo n i < hi n j := by
  have := i.isLt; have := j.isLt
  simp only [Fin.lt_def, lo, hi]; omega

theorem not_hi_lt_lo {n : ℕ} (i j : Fin (n / 2)) : ¬ hi n i < lo n j := by
  have := i.isLt; have := j.isLt
  simp only [Fin.lt_def, lo, hi]; omega

theorem lo_lt_md {n : ℕ} (i : Fin (n / 2)) (t : Fin (n % 2)) : lo n i < md n t := by
  have := i.isLt; have := t.isLt
  simp only [Fin.lt_def, lo, md]; omega

theorem not_md_lt_lo {n : ℕ} (i : Fin (n / 2)) (t : Fin (n % 2)) : ¬ md n t < lo n i := by
  have := i.isLt; have := t.isLt
  simp only [Fin.lt_def, lo, md]; omega

theorem md_lt_hi {n : ℕ} (i : Fin (n / 2)) (t : Fin (n % 2)) : md n t < hi n i := by
  have := i.isLt; have := t.isLt
  simp only [Fin.lt_def, hi, md]; omega

theorem not_hi_lt_md {n : ℕ} (i : Fin (n / 2)) (t : Fin (n % 2)) : ¬ hi n i < md n t := by
  have := i.isLt; have := t.isLt
  simp only [Fin.lt_def, hi, md]; omega

theorem lOf_eq {n : ℕ} (x : Fin n → ℤ) (i : Fin (n / 2)) : lOf x i = x (lo n i) - x (hi n i) := rfl

theorem pt4 {n : ℕ} (x : Fin n → ℤ) (hx : ∀ i j : Fin n, i < j → x j + 2 ≤ x i) (i j : Fin (n / 2)) (hij : i ≠ j) :
    (x (lo n i) - x (lo n j)) * sgn2 (lo n i) (lo n j) + (x (lo n i) - x (hi n j)) * sgn2 (lo n i) (hi n j) +
      (x (hi n i) - x (lo n j)) * sgn2 (hi n i) (lo n j) + (x (hi n i) - x (hi n j)) * sgn2 (hi n i) (hi n j) =
      2 * max (lOf x i) (lOf x j) := by
  simp only [sgn2, lo_lt_lo, hi_lt_hi, lo_lt_hi, not_hi_lt_lo, lOf_eq, ↓reduceIte]
  rcases lt_or_gt_of_ne hij with h | h
  · have h1 := hx _ _ ((lo_lt_lo i j).mpr h)
    have h2 := hx _ _ ((hi_lt_hi j i).mpr h)
    simp only [h, not_lt.mpr h.le, ↓reduceIte]
    rw [max_eq_left (by linarith)]; ring
  · have h1 := hx _ _ ((lo_lt_lo j i).mpr h)
    have h2 := hx _ _ ((hi_lt_hi i j).mpr h)
    simp only [h, not_lt.mpr h.le, ↓reduceIte]
    rw [max_eq_right (by linarith)]; ring

theorem half {n a : ℕ} (s : Finset (Fin (n / 2))) (hp : a % 2 + (n - a) % 2 = n % 2) (x : Fin n → ℤ)
    (hx : ∀ i j : Fin n, i < j → x j + 2 ≤ x i) :
    ∑ k ∈ symIdx n (a % 2 = 1) s, ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k' =
      - vRes n a (lOf x) s := by
  set T : Fin n → Fin n → ℤ := fun k k' => if k ∈ symIdx n (a % 2 = 1) s then
    (if k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ then (x k - x k') * sgn2 k k' else 0) else 0 with hT
  have s1 : ∑ k ∈ symIdx n (a % 2 = 1) s, ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k' =
      ∑ k, ∑ k', T k k' := by
    rw [sum_ind (symIdx n (a % 2 = 1) s)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_ind (symIdx n ((n - a) % 2 = 1) sᶜ)]
    by_cases hk : k ∈ symIdx n (a % 2 = 1) s
    · simp only [hT, hk, ↓reduceIte]
    · simp only [hT, hk, ↓reduceIte, Finset.sum_const_zero]
  have s2 : ∑ k, ∑ k', T k k' =
      ∑ i, ∑ j, (T (lo n i) (lo n j) + T (lo n i) (hi n j) + T (hi n i) (lo n j) + T (hi n i) (hi n j)) +
      ∑ i, ∑ u, (T (lo n i) (md n u) + T (hi n i) (md n u) + T (md n u) (lo n i) + T (md n u) (hi n i)) +
      ∑ t, ∑ u, T (md n t) (md n u) := by
    simp only [sum_split (n := n)]
    simp only [Finset.sum_add_distrib]
    have c1 : ∑ t, ∑ j, T (md n t) (lo n j) = ∑ j, ∑ t, T (md n t) (lo n j) := Finset.sum_comm
    have c2 : ∑ t, ∑ j, T (md n t) (hi n j) = ∑ j, ∑ t, T (md n t) (hi n j) := Finset.sum_comm
    rw [c1, c2]; ring
  have s3 : ∑ i, ∑ j, (T (lo n i) (lo n j) + T (lo n i) (hi n j) + T (hi n i) (lo n j) + T (hi n i) (hi n j)) =
      2 * ∑ i ∈ s, ∑ j ∈ sᶜ, max (lOf x i) (lOf x j) := by
    rw [Finset.mul_sum, sum_ind s]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases his : i ∈ s
    · rw [if_pos his, Finset.mul_sum, sum_ind sᶜ]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjs : j ∈ sᶜ
      · have hij : i ≠ j := by rintro rfl; exact (Finset.mem_compl.mp hjs) his
        simp only [hT, mem_lo, mem_hi, his, hjs, ↓reduceIte]
        exact pt4 x hx i j hij
      · simp only [hT, mem_lo, mem_hi, his, hjs, ↓reduceIte, add_zero]
    · rw [if_neg his]
      simp only [hT, mem_lo, mem_hi, his, ↓reduceIte, add_zero, Finset.sum_const_zero]
  have q : ∀ i u, T (lo n i) (md n u) + T (hi n i) (md n u) + T (md n u) (lo n i) + T (md n u) (hi n i) =
      if a % 2 = 1 then (if i ∈ sᶜ then lOf x i else 0) else (if i ∈ s then lOf x i else 0) := by
    intro i u
    have hu := u.isLt
    simp only [hT, mem_lo, mem_hi, mem_md, sgn2, lo_lt_md, not_md_lt_lo, md_lt_hi, not_hi_lt_md, lOf_eq, ↓reduceIte]
    by_cases ha : a % 2 = 1
    · have hb : ¬ (n - a) % 2 = 1 := by omega
      by_cases his : i ∈ sᶜ <;> simp [ha, hb, his] <;> ring
    · have hb : (n - a) % 2 = 1 := by omega
      by_cases his : i ∈ s <;> simp [ha, hb, his] <;> ring
  have s4 : ∑ i, ∑ u, (T (lo n i) (md n u) + T (hi n i) (md n u) + T (md n u) (lo n i) + T (md n u) (hi n i)) =
      if n % 2 = 1 then (if a % 2 = 1 then ∑ j ∈ sᶜ, lOf x j else ∑ j ∈ s, lOf x j) else 0 := by
    simp only [q, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · simp [h]
    · simp only [h, one_smul, ↓reduceIte]
      by_cases ha : a % 2 = 1
      · simp only [ha, ↓reduceIte]; rw [sum_ind sᶜ]
      · simp only [ha, ↓reduceIte]; rw [sum_ind s]
  have s5 : ∑ t, ∑ u, T (md n t) (md n u) = 0 := by
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun u _ => ?_
    have htu : md n t = md n u := by
      have := t.isLt; have := u.isLt
      ext; simp only [md]; omega
    simp only [hT, htu, sub_self, zero_mul, ite_self]
  rw [s1, s2, s3, s4, s5]
  simp only [vRes]
  ring

theorem neg_one_pow_eq (N : ℕ) (d t : ℤ) (h : d = N + 2 * t) : ((-1 : ℂˣ) ^ N) = (-1) ^ d := by
  subst h
  rw [_root_.zpow_add, _root_.zpow_mul, zpow_natCast]
  have h2 : ((-1 : ℂˣ) ^ (2 : ℤ)) = 1 := by rw [zpow_two, neg_one_mul, neg_neg]
  rw [h2, _root_.one_zpow, mul_one]

theorem vResStd' : VResStd := by
  intro E _ _ _ w n a s h e he x hx
  have hx' : ∀ i j : Fin n, i < j → x j + 2 ≤ x i := hx
  have han : a ≤ n := by
    have h1 := h.2.1
    have h2 := Finset.card_le_univ (symIdx n (a % 2 = 1) s)
    rw [Fintype.card_fin] at h2
    omega
  refine ⟨?_, funext fun i => congrArg x (he.1 i).symm, funext fun j => congrArg x (he.2 j).symm⟩
  have heps : ∀ k, (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)).eps k =
      (-Units.mk0 (qh w) (qh_ne_zero' w)) ^ (rh n k - Sum.elim (fun i : Fin a => rh a i)
        (fun j : Fin (n - a) => rh (n - a) j) (e.symm k)) := by
    intro k
    show Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k) *
      qU w (rh n k - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin (n - a) => rh (n - a) j) (e.symm k)) = _
    rw [unit_power_eq_residue_power, ← neg_one_mul (Units.mk0 (qh w) (qh_ne_zero' w)), mul_zpow]
    congr 1
    generalize e.symm k = p
    rcases p with i | j
    · simp only [Sum.elim_inl]
      exact neg_one_pow_eq (n - a) _ (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) (by simp only [rh]; omega)
    · simp only [Sum.elim_inr]
      exact neg_one_pow_eq a _ (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) (by simp only [rh]; omega)
  simp only [heps, ← _root_.zpow_mul]
  rw [← zpow_finsum', Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_mk0]
  congr 1
  rw [blocks e (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)).monoL
    (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)).monoR x]
  have hAB : ∑ i, ∑ j, (x (e (Sum.inl i)) - x (e (Sum.inr j))) * sgn2 (e (Sum.inl i)) (e (Sum.inr j)) =
      ∑ k ∈ symIdx n (a % 2 = 1) s, ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k' := by
    simp only [he.1, he.2]
    rw [← sum_oe _ h.2.1 (fun k => ∑ k' ∈ symIdx n ((n - a) % 2 = 1) sᶜ, (x k - x k') * sgn2 k k')]
    exact Finset.sum_congr rfl fun i _ => sum_oe _ h.2.2 (fun k' => (x _ - x k') * sgn2 _ k')
  rw [hAB, half s h.1.2.2 x hx']

end PositivityTheory.Rg.BcB.F.Choice.IndefiniteRowSideFullHecke

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.KUEqKLOfNotMemBad
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.FX
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

def GcHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
  ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (c : (Fin n → ℤ) →₀ ℂ), IsHecke (iwU n w b) (gc w b ϖ c)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (T' : Finset (Pl E)) (c : Pl E → (Fin n → ℤ) →₀ ℂ) (e : ∀ w : Pl E, GLw n w → ℂ)
  (b : ∀ w : Pl E, GLw n w)

theorem loc_KU_eq_iwU_of_mem {w : Pl E} (hw : w ∈ T') : (F₀.loc T' c e b).KU w = iwU n w (b w) := if_pos hw

theorem KU_off {w : Pl E} (hw : w ∉ T') : (F₀.loc T' c e b).KU w = F₀.d₀.KU w := by
  have h0 : w ∉ F₀.d₀.T := by rw [F₀.T₀]; exact Finset.notMem_empty w
  unfold LocData.KU
  rw [if_neg hw, if_neg h0]

theorem KU_eq_KL_of_not_mem_bad {w : Pl E} (h1 : w ∉ F₀.d₀.S₀) (h2 : w ∉ F₀.d₀.Bad) : F₀.d₀.KU w = KL n w := by
  have h0 : w ∉ F₀.d₀.T := by rw [F₀.T₀]; exact Finset.notMem_empty w
  unfold LocData.KU
  rw [if_neg h0, if_neg h1, if_neg h2]

theorem levOff (hT : ∀ w ∈ T', w ∈ F₀.Sec ∧ IsWitt n w (b w)) :
    U.LevelOff F₀.Sec (F₀.loc T' c e b).B (F₀.loc T' c e b).KU := by
  refine ⟨fun w hw => ?_, ⟨fun w => ?_, ?_⟩, fun w hw => ?_⟩
  · rcases Finset.mem_union.1 (Finset.mem_coe.1 hw) with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact (hT w h).1
      · exact (F₀.S₀ w h).1
    · exact (F₀.bad w h).1
  · by_cases hw : w ∈ T'
    · rw [loc_KU_eq_iwU_of_mem F₀ T' c e b hw]
      exact ⟨GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w _, GlobalTheory.CompanionTheory.IwLevels.iwU_le_KL n w _ (hT w hw).2.1, fun k hk => hk⟩
    · rw [KU_off F₀ T' c e b hw]
      exact F₀.levFam.1 w
  · filter_upwards [F₀.levFam.2, T'.finite_toSet.compl_mem_cofinite] with w h1 h2
    rw [KU_off F₀ T' c e b h2, h1]
  · have h1 : w ∉ T' := fun h => hw (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have h2 : w ∉ F₀.d₀.S₀ := fun h => hw (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have h3 : w ∉ F₀.d₀.Bad := fun h => hw (Finset.mem_union_right _ h)
    rw [KU_off F₀ T' c e b h1, KU_eq_KL_of_not_mem_bad F₀ h2 h3]

theorem hasLevel (hT : ∀ w ∈ T', IsWitt n w (b w) ∧ w ∉ F₀.d₀.S₀ ∧ w ∉ F₀.d₀.Bad) :
    HasLevel F₀.Sec π (F₀.loc T' c e b).KU := by
  refine F₀.level _ fun w => ?_
  by_cases hw : w ∈ T'
  · rw [loc_KU_eq_iwU_of_mem F₀ T' c e b hw, KU_eq_KL_of_not_mem_bad F₀ (hT w hw).2.1 (hT w hw).2.2]
    exact GlobalTheory.CompanionTheory.IwLevels.iwU_le_KL n w _ (hT w hw).1.1
  · rw [KU_off F₀ T' c e b hw]

theorem loc_ok (hT : ∀ w ∈ T', w ∉ F₀.d₀.S₀ ∧ w ∉ F₀.d₀.Bad)
    (hc : ∀ w ∈ T', (↑(c w).support : Set (Fin n → ℤ)) ⊆ coneGL n 2) (he : ∀ w ∈ F₀.d₀.S₀, IsHk (F₀.d₀.K' w) (e w)) :
    (F₀.loc T' c e b).Ok :=
  ⟨⟨Finset.disjoint_left.2 fun w hw => (hT w hw).1, Finset.disjoint_left.2 fun w hw => (hT w hw).2, F₀.ok₀.disj.2.2⟩,
    F₀.ok₀.unif, hc, fun w hw => ⟨(F₀.ok₀.K' w hw).1, (F₀.ok₀.K' w hw).2.1, (F₀.ok₀.K' w hw).2.2.1, (F₀.ok₀.K' w hw).2.2.2.1,
      (F₀.ok₀.K' w hw).2.2.2.2.1, he w hw⟩, F₀.ok₀.L, F₀.ok₀.LS, F₀.ok₀.fix⟩

theorem loc_mok (hCone : ConeTwo) (h0 : MLM.MOk F₀.d₀) (hT : ∀ w ∈ T', ¬ IsSplitAt w ∧ IsWitt n w (b w))
    (hc : ∀ w ∈ T', (↑(c w).support : Set (Fin n → ℤ)) ⊆ coneGL n 2) : MLM.MOk (F₀.loc T' c e b) := by
  refine ⟨fun w hw => ⟨(hT w hw).1, (hT w hw).2, (F₀.unif w).1, fun x hx => ⟨fun i j hij => ?_, ?_⟩⟩, h0.S, h0.badS, h0.badI⟩
  · have := hc w hw hx i j hij
    omega
  · by_cases hn : 2 ≤ n
    · exact hCone n x hn (hc w hw hx)
    · exact ⟨fun i => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega)⟩

theorem eig_B (hG : GcHecke) (hP : PowEig) (hA : LocAlg) (hdis : ∀ w ∈ T', ¬ IsSplitAt w ∧ w ∉ F₀.d₀.S₀)
    (hlev : ∀ w, GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) ((F₀.loc T' c e b).KU w))
    (σ : ∀ w : Pl E, SmIrr (UL n w)) (hne : ∀ w ∈ F₀.d₀.Bad, fixed (σ w).ρ ((F₀.loc T' c e b).KU w) ≠ ⊥)
    (hT : ∀ w ∈ T', ∃ y : fixed (σ w).ρ (iwU n w (b w)), y ≠ 0 ∧ locOp (σ w) (iwU n w (b w)) (gc w (b w) (F₀.d₀.ϖ w) (c w)) y = y)
    (hS : ∀ w ∈ F₀.d₀.S₀, IsHecke ((F₀.d₀.K' w).subgroupOf (UL n w)) (fun y => e w y.1) ∧
      ∃ y : fixed (σ w).ρ ((F₀.d₀.K' w).subgroupOf (UL n w)), y ≠ 0 ∧
        locOp (σ w) ((F₀.d₀.K' w).subgroupOf (UL n w)) (fun y => e w y.1) y = y) (m : ℕ) :
    ∀ w ∈ (F₀.loc T' c e b).B, ∃ y, y ≠ 0 ∧ locOp (σ w) ((F₀.loc T' c e b).KU w) ((F₀.loc T' c e b).gU m w) y = y := by
  intro w hw
  have key : ∀ (K' : Subgroup (UL n w)) (g : UL n w → ℂ), (F₀.loc T' c e b).KU w = K' → (F₀.loc T' c e b).g₀ w = g →
      IsHecke K' g → (∃ y : fixed (σ w).ρ K', y ≠ 0 ∧ locOp (σ w) K' g y = y) →
      ∃ y, y ≠ 0 ∧ locOp (σ w) ((F₀.loc T' c e b).KU w) ((F₀.loc T' c e b).gU m w) y = y := by
    rintro K' g rfl rfl hH ⟨y, hy0, hy⟩
    exact ⟨y, hy0, hP E n w (σ w) _ (hlev w) _ hH y hy m⟩
  by_cases h1 : w ∈ T'
  · exact key _ _ (if_pos h1) (if_pos h1) (hG E n w (hdis w h1).1 _ _ _) (hT w h1)
  by_cases h2 : w ∈ F₀.d₀.S₀
  · exact key _ _ ((if_neg h1).trans (if_pos h2)) ((if_neg h1).trans (if_pos h2)) (hS w h2).1 (hS w h2).2
  have h3 : w ∈ F₀.d₀.Bad := by
    rcases Finset.mem_union.1 hw with h | h
    · exact absurd (Finset.mem_union.1 h) (not_or.2 ⟨h1, h2⟩)
    · exact h
  have h0 : IsHecke ((F₀.loc T' c e b).KU w) (0 : UL n w → ℂ) := ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have hL := (hA E n w (σ w) _ (hlev w) 0 0 h0 h0).2.2.2.2.2.2
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (hne w h3)
  refine key _ (U.lone ((F₀.loc T' c e b).KU w)) rfl ((if_neg h1).trans (if_neg h2)) hL.1
    ⟨⟨y, hy⟩, fun h => hy0 (congrArg Subtype.val h), ?_⟩
  exact (LinearMap.congr_fun hL.2 _).trans rfl

end UpperTheory.HeckeLevelFrameExistence

namespace UpperTheory.HeckeLevelFrameExistence

set_option maxHeartbeats 1000000 in
theorem frameEx_of (hUS : USide) (hSph : SphOne) (hSpec : SpecTrace) (hA : LocAlg) (hTb : ExTb) (hSat : Inert.SatEx)
    (hUnif : Inert.UnifOf) (hCE : ConeEig) (hSC : SatCompAt) (hCI : CandIndep) (hCF : CandFin) (hM0 : FrameBoundModuleCondition)
    (hCone : ConeTwo) (hG : GcHecke) (hC : LocC) (hLE : LocE) (hMu : MuVal) (hP : PowEig) : FrameEx := by
  intro hR E _ _ _ hE n hn π hπ S F₀ T
  obtain ⟨T', b, hne, hT', -, hTle⟩ := hTb hR E hE n hn π hπ S F₀ T
  have hL : ∀ c e, U.LevelOff F₀.Sec (F₀.loc T' c e b).B (F₀.loc T' c e b).KU := fun c e =>
    levOff F₀ T' c e b fun w hw => ⟨(hT' w hw).1, (hT' w hw).2.2.2.1⟩
  obtain ⟨fam⟩ := U.uFam_of hUS hE hn F₀.hSec F₀.lam (hL 0 0).2.1
  obtain ⟨i₀, hi₀⟩ := fam.all π hπ F₀.hlam
    (hasLevel F₀ T' 0 0 b fun w hw => ⟨(hT' w hw).2.2.2.1, (hT' w hw).2.2.2.2⟩)
  obtain ⟨hZ, hD, m₀, hm₀⟩ := hCF hR E hE n hn π hπ S F₀ T' 0 0 b fun w hw => ⟨(hT' w hw).2.1, (hT' w hw).2.2.2.2⟩
  choose Z hZf hZ using hZ

  have hT : ∀ w, ∃ cw : (Fin n → ℤ) →₀ ℂ, w ∈ T' → (↑cw.support : Set (Fin n → ℤ)) ⊆ coneGL n 2 ∧
      (∃ y : fixed (fam.σ i₀ w).ρ (iwU n w (b w)), y ≠ 0 ∧
        locOp (fam.σ i₀ w) (iwU n w (b w)) (gc w (b w) (F₀.d₀.ϖ w) cw) y = y) ∧
      ∀ i s (h : LocData.admitted n (F₀.C.a i) s) ξa ξb, (ξa, ξb) ∈ Z i w →
        (cw.sum fun x t => t * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf x) s) * ev2 w ξa ξb (restr x _ h.2.1) (restr x _ h.2.2)) ≠ 0 →
        PositivityTheory.Rg.BcB.N3.Mono ξa ∧ PositivityTheory.Rg.BcB.N3.Mono ξb ∧ ∀ (ϖ : w.adicCompletion E) (q : ℕ), IsUnramInv ϖ (cj w) q →
          ∀ α, HasSatAt π w (cj w) ϖ q α →
            (Finset.univ.val.map ξa).map (· * (F₀.μ ^ (n - F₀.C.a i)).val w) +
              (Finset.univ.val.map ξb).map (· * (F₀.μ ^ F₀.C.a i).val w) = GlobalTheory.LGrp.bcParam n α := by
    intro w
    by_cases hw : w ∈ T'
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    obtain ⟨hsec, hs, hu, hb, -⟩ := hT' w hw
    obtain ⟨q', hq'⟩ := hUnif E hE w hs _ (F₀.unif w).1
    have hadm : IsAdmissible (fam.σ i₀ w).ρ :=
      ⟨(fam.σ i₀ w).smooth, fun K hK _ => ((fam.comp i₀).2.2.2 w hsec).2.2 K hK⟩
    obtain ⟨α', hα'⟩ := hSat E n w hs (b w) _ q' hb (F₀.unif w).1 hq' _ hadm (GlobalTheory.T.unramifiedVector_gives_localComponent_sphericalVector E hE n π hπ w _ (hi₀ w hsec) hu)
    obtain ⟨ξ, hξm, hξ, y, hy0, hy⟩ := hCE E n w hs (b w) _ q' _ α' hb (F₀.unif w).1 hq' hadm hα'
    obtain ⟨cw, h1, h2, h3⟩ := hC E n w F₀.C.ι F₀.C.a (fun i => Z i w) ξ F₀.C.le (fun i => hZf i w) hξm
    refine ⟨cw, fun _ => ⟨h1, ⟨y, hy0, by rw [hy cw h1, h2, one_smul]⟩, fun i s h ξa ξb hz h0 => ?_⟩⟩
    obtain ⟨a1, a2, a3⟩ := h3 i s h ξa ξb hz h0
    refine ⟨a1, a2, fun ϖ q hq α hα => ?_⟩
    have hϖ : ϖ ≠ 0 := by
      rintro rfl
      have := hq.2.2.2.1
      rw [map_zero] at this
      exact WithZero.coe_ne_zero this.symm
    rw [hMu E _ _ F₀.hμ w hs, hMu E _ _ F₀.hμ w hs, a3, hξ]
    exact (hSC E n π hπ w hs _ (b w) (Units.mk0 ϖ hϖ) _ q q' α α' (hi₀ w hsec) hb (F₀.unif w).1 hq hq' hα hα').symm
  choose c hc using hT

  have hS : ∀ w, ∃ (ew : GLw n w → ℂ) (mw : ℕ), w ∈ F₀.d₀.S₀ → IsHk (F₀.d₀.K' w) ew ∧
      (IsHecke ((F₀.d₀.K' w).subgroupOf (UL n w)) (fun y => ew y.1) ∧
        ∃ y : fixed (fam.σ i₀ w).ρ ((F₀.d₀.K' w).subgroupOf (UL n w)), y ≠ 0 ∧
          locOp (fam.σ i₀ w) ((F₀.d₀.K' w).subgroupOf (UL n w)) (fun y => ew y.1) y = y) ∧
      (∃ P : SmIrr (GLw n w), IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ ∧
        ∀ i s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' 0 0 b) i s₁ s₂ Pa Pb D → ∀ τ : SmIrr (GLw n w),
          GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) →
            ∀ y ∈ fixed τ.ρ (F₀.d₀.K' w), hk τ.ρ (F₀.d₀.K' w) ew y = 0) ∧
      ∀ i s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' 0 0 b) i s₁ s₂ Pa Pb D →
        Module.finrank ℂ ↥(fixed (prodAt D w) (F₀.d₀.K' w)) < mw := by
    intro w
    by_cases hw : w ∈ F₀.d₀.S₀
    swap
    · exact ⟨0, 0, fun h => absurd h hw⟩
    obtain ⟨k, Dl, hDl⟩ := hD w hw
    have hwT : w ∉ T' := fun h => (hT' w h).2.2.2.2.1 hw
    have hK : (F₀.loc T' 0 0 b).KU w = (F₀.d₀.K' w).subgroupOf (UL n w) := (if_neg hwT).trans (if_pos hw)
    have hfix := ((fam.comp i₀).2.2.2 w (F₀.S₀ w hw).1).2.1
    rw [hK] at hfix
    obtain ⟨ew, P, h1, h2, h3, h4, h5⟩ := hLE E n w (F₀.S₀ w hw).2 _ (F₀.ok₀.K' w hw).1 (F₀.ok₀.K' w hw).2.1 (F₀.K'_lev w hw)
      _ hfix k Dl
    refine ⟨ew, (Finset.univ.sup fun j => Module.finrank ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w))) + 1, fun _ =>
      ⟨h1, ⟨h2, h4⟩, ⟨P, h3 π (hi₀ w (F₀.S₀ w hw).1), fun i s₁ s₂ Pa Pb D hcand τ hτ => ?_⟩, fun i s₁ s₂ Pa Pb D hcand => ?_⟩⟩
    · obtain ⟨j, hj, -⟩ := hDl i s₁ s₂ Pa Pb D hcand
      exact h5 j τ ((hj τ).1 hτ)
    · obtain ⟨j, -, hj, -⟩ := hDl i s₁ s₂ Pa Pb D hcand
      rw [hj]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j => Module.finrank ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w)))
        (Finset.mem_univ j))
  choose e mS he using hS
  have hcand : ∀ {i s₁ s₂ Pa Pb D}, F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D → F₀.Cand (F₀.loc T' 0 0 b) i s₁ s₂ Pa Pb D :=
    fun h => (hCI hR E n π S F₀ T' c 0 e 0 b b _ _ _ _ _ _).1 h
  let m : ℕ := m₀ + F₀.d₀.S₀.sup mS + 1
  let fam' : U.UFam F₀.Sec F₀.lam (F₀.loc T' c e b).KU := fam
  obtain ⟨R⟩ := U.uMod_of hSph hSpec hE fam' (hL c e) ((F₀.loc T' c e b).gU m)
  obtain ⟨v, hv0, hv1, hv2⟩ := R.eig i₀ (eig_B F₀ T' c e b hG hP hA (fun w hw => ⟨(hT' w hw).2.1, (hT' w hw).2.2.2.2.1⟩)
    (hL c e).2.1.1 (fam.σ i₀) (fun w hw => ((fam.comp i₀).2.2.2 w (F₀.bad w hw).1).2.1) (fun w hw => (hc w hw).2.1)
    (fun w hw => (he w hw).2.1) m)
  exact ⟨{
    d := F₀.loc T' c e b
    same := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    m := m
    m_pos := Nat.succ_le_succ (Nat.zero_le _)
    ok := loc_ok F₀ T' c e b (fun w hw => (hT' w hw).2.2.2.2) (fun w hw => (hc w hw).1) fun w hw => (he w hw).1
    mok := loc_mok F₀ T' c e b hCone (hM0 hR E hE n hn π S F₀) (fun w hw => ⟨(hT' w hw).2.1, (hT' w hw).2.2.2.1⟩)
      fun w hw => (hc w hw).1
    T_ne := hne
    T_in := fun w hw => ⟨(hT' w hw).1, (hT' w hw).2.1, (hT' w hw).2.2.1, (hT' w hw).2.2.2.1⟩
    T_le := hTle
    levOff := hL c e
    fam := fam'
    R := R
    i₀ := i₀
    comp := hi₀
    v := v
    v_ne := hv0
    uv := hv1
    vblk := hv2
    choiceT := fun i s₁ s₂ Pa Pb D h w hw s ha ξa ξb hj h0 =>
      (hc w hw).2.2 i s ha ξa ξb (hZ i w s₁ s₂ Pa Pb D (hcand h) hw ξa ξb hj) h0
    choiceS := fun w hw => by
      obtain ⟨P, h1, h2⟩ := (he w hw).2.2.1
      exact ⟨P, h1, fun i s₁ s₂ Pa Pb D h => h2 i s₁ s₂ Pa Pb D (hcand h)⟩
    choiceM := fun i s₁ s₂ Pa Pb D h => ⟨fun w hw => by
        have h1 := (he w hw).2.2.2 i s₁ s₂ Pa Pb D (hcand h)
        have h2 : mS w ≤ F₀.d₀.S₀.sup mS := Finset.le_sup hw
        omega, fun w hw => by
        have h1 := hm₀ i s₁ s₂ Pa Pb D (hcand h) w hw
        omega⟩ }⟩

end UpperTheory.HeckeLevelFrameExistence

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Mok0
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

theorem mok0 {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) : MLM.MOk F₀.d₀ := by
  have h0 : ∀ w, w ∉ F₀.d₀.T := fun w => by rw [F₀.T₀]; exact Finset.notMem_empty w
  have hlev : ∀ w ∈ F₀.d₀.Bad, GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) (F₀.d₀.KB w) := fun w hw => by
    have h := F₀.levFam.1 w
    have e : F₀.d₀.KU w = F₀.d₀.KB w :=
      (if_neg (h0 w)).trans ((if_neg fun h' => Finset.disjoint_left.1 F₀.ok₀.disj.2.2 h' hw).trans (if_pos hw))
    rwa [e] at h
  refine ⟨fun w hw => absurd hw (h0 w), fun w hw => ⟨(F₀.S₀ w hw).2, fun g => ?_, F₀.K'_lev w hw⟩,
    fun w hw hs => ⟨hlev w hw, fun a ha => ?_⟩, fun w hw hs => ⟨F₀.kB w, F₀.kB_pos w hw hs, hlev w hw, fun γ => ?_, fun a ha => ?_⟩⟩
  · unfold UL
    rw [if_pos (F₀.S₀ w hw).2]
    exact Subgroup.mem_top g
  · rw [F₀.fix_def a ha w, if_pos hw, if_pos hs]
  · have e : {γ : UL n w | γ.1 ∈ MB.congK n w (F₀.kB w)} =
        (((GlobalTheory.PrincCong.congSub w n (F₀.kB w)).subgroupOf (UL n w) : Subgroup (UL n w)) : Set (UL n w)) :=
      Set.ext fun x => (GlobalTheory.PrincCong.mem_congSub_iff w n (F₀.kB w) x.1).symm
    rw [F₀.KB_def w, if_pos hw, if_neg hs, e, Subgroup.closure_eq]
    exact GlobalTheory.PrincCong.mem_congSub_iff w n (F₀.kB w) γ.1
  · rw [F₀.fix_def a ha w, if_pos hw, if_neg hs]

end UpperTheory.HeckeLevelFrameExistence

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.MapSplit
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_ex (hE : ShufEx) (n a : ℕ) (s : Finset (Fin (n / 2))) (h : LocData.admitted n a s) :
    ∃ e : Fin a ⊕ Fin (n - a) ≃ Fin n,
      (∀ i, e (.inl i) = (symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1 i) ∧
      ∀ j, e (.inr j) = (symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2 j := by
  obtain ⟨hdisj, hcov⟩ := hE n a s h
  let f : Fin a ⊕ Fin (n - a) → Fin n :=
    Sum.elim ((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1) ((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2)
  have hf : Function.Bijective f := by
    constructor
    · rintro (i | i) (j | j) hij
      · simp only [f, Sum.elim_inl] at hij
        exact congrArg Sum.inl (((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1).injective hij)
      · exfalso
        simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact Finset.disjoint_left.1 hdisj (Finset.orderEmbOfFin_mem _ h.2.1 i)
          (hij ▸ Finset.orderEmbOfFin_mem _ h.2.2 j)
      · exfalso
        simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact Finset.disjoint_left.1 hdisj (Finset.orderEmbOfFin_mem _ h.2.1 j)
          (hij ▸ Finset.orderEmbOfFin_mem _ h.2.2 i)
      · simp only [f, Sum.elim_inr] at hij
        exact congrArg Sum.inr (((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2).injective hij)
    · intro k
      have hk : k ∈ symIdx n (a % 2 = 1) s ∪ symIdx n ((n - a) % 2 = 1) sᶜ := hcov ▸ Finset.mem_univ k
      rcases Finset.mem_union.1 hk with hk | hk
      · have hr : k ∈ Set.range ((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1) := by
          rw [Finset.range_orderEmbOfFin]
          exact hk
        obtain ⟨i, hi⟩ := hr
        exact ⟨.inl i, hi⟩
      · have hr : k ∈ Set.range ((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2) := by
          rw [Finset.range_orderEmbOfFin]
          exact hk
        obtain ⟨j, hj⟩ := hr
        exact ⟨.inr j, hj⟩
  exact ⟨Equiv.ofBijective f hf, fun i => rfl, fun j => rfl⟩

private theorem map_split {α β : Type} [Fintype α] [Fintype β] {n : ℕ} (e : α ⊕ β ≃ Fin n) (f : Fin n → ℂˣ) :
    Finset.univ.val.map (fun i => f (e (.inl i))) + Finset.univ.val.map (fun j => f (e (.inr j))) =
      Finset.univ.val.map f := by
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map, ← Finset.univ_disjSum_univ]
  simp [Finset.disjSum, Multiset.disjSum, Multiset.map_add (f := _), Multiset.map_map, Function.comp_def]

private theorem finish (hT : TargetAlg) (hM : MonoRes) {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E)
    (n a : ℕ) (s : Finset (Fin (n / 2))) (h : LocData.admitted n a s) (e : Fin a ⊕ Fin (n - a) ≃ Fin n)
    (he : (∀ i, e (.inl i) = (symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1 i) ∧
      ∀ j, e (.inr j) = (symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2 j)
    (ξ : Fin n → ℂˣ) (ξa : Fin a → ℂˣ) (ξb : Fin (n - a) → ℂˣ) (hmono : PositivityTheory.Rg.BcB.N3.Mono ξ)
    (hstd : IsStd w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a))
      (fun k => Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k)))
    (hchi : chiOf w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) ξa ξb = chiN w ξ) :
    PositivityTheory.Rg.BcB.N3.Mono ξa ∧ PositivityTheory.Rg.BcB.N3.Mono ξb ∧
      (Finset.univ.val.map ξa).map (· * (-1 : ℂˣ) ^ (n - a)) + (Finset.univ.val.map ξb).map (· * (-1 : ℂˣ) ^ a) =
        Finset.univ.val.map ξ := by
  obtain ⟨hA, hB⟩ := hT E n w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) _ ξ ξa ξb hstd hchi
  have hnorm : ∀ k : Fin n,
      ‖((Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k) : ℂˣ) : ℂ)‖ = 1 := by
    intro k
    cases e.symm k <;> simp
  obtain ⟨mA, mB⟩ := hM n (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) _ ξ hmono hnorm
  have e1 : ξa = fun i => _ := funext hA
  have e2 : ξb = fun j => _ := funext hB
  refine ⟨by rw [e1]; exact mA, by rw [e2]; exact mB, ?_⟩
  rw [Multiset.map_map, Multiset.map_map, ← map_split e ξ]
  congr 1
  · congr 1
    funext i
    rw [Function.comp_apply, hA i]
    show ξ (e (.inl i)) * (Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm (e (.inl i))))⁻¹ *
      (-1) ^ (n - a) = ξ (e (.inl i))
    rw [Equiv.symm_apply_apply, Sum.elim_inl, inv_mul_cancel_right]
  · congr 1
    funext j
    rw [Function.comp_apply, hB j]
    show ξ (e (.inr j)) * (Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm (e (.inr j))))⁻¹ *
      (-1) ^ a = ξ (e (.inr j))
    rw [Equiv.symm_apply_apply, Sum.elim_inr, inv_mul_cancel_right]

theorem UpperTheory.HeckeLevelFrameExistence.locC :
    PositivityTheory.Rg.BcB.F.Choice.ShufEx → PositivityTheory.Rg.BcB.F.Choice.VResStd → PositivityTheory.Rg.BcB.F.Choice.ShufStd → PositivityTheory.Rg.BcB.F.Tail.TargetAlg → PositivityTheory.Rg.BcB.F.Tail.MonoRes → UpperTheory.HeckeLevelFrameExistence.LocC := by
  intro hE hV hS hT hM E _ _ _ n w ι _ a Z ξ ha hZ hmono
  let J := Σ i : ι, {s : Finset (Fin (n / 2)) // LocData.admitted n (a i) s}
  let ee : (j : J) → Fin (a j.1) ⊕ Fin (n - a j.1) ≃ Fin n :=
    fun j => Classical.choose (exists_ex hE n (a j.1) j.2.1 j.2.2)
  have hee := fun j : J => Classical.choose_spec (exists_ex hE n (a j.1) j.2.1 j.2.2)
  let S : J → Shuf n := fun j =>
    shufOf w n (a j.1) j.2.1 j.2.2 (ee j) (hee j) ((-1) ^ (n - a j.1)) ((-1) ^ a j.1)
  let Z' : (j : J) → Set ((Fin (S j).a → ℂˣ) × (Fin (S j).b → ℂˣ)) := fun j => Z j.1
  obtain ⟨c, hc1, hc2, hc3⟩ := choiceT E n w J S Z' (chiN w ξ) (fun j => hZ j.1)
  refine ⟨c, hc1, hc2, ?_⟩
  intro i s h ξa ξb hmem hne
  let j : J := ⟨i, s, h⟩
  have hchi : chiOf w (S j) ξa ξb = chiN w ξ := by
    refine hc3 j (ξa, ξb) hmem ?_
    convert hne using 1
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun x hx => ?_)
    obtain ⟨h1, h2, h3⟩ := hV E w n (a i) s h (ee j) (hee j) x (hc1 hx)
    dsimp only
    rw [h1, h2, h3]
    rfl
  exact finish hT hM w n (a i) s h (ee j) (hee j) ξ ξa ξb hmono (hS E w n (a i) s h (ee j) (hee j)) hchi
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.HkConstMul
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hk_const_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (c : ℂ) (e : GL ι F → ℂ) (v : V) :
    PositivityTheory.Rg.BcN.F2.hk ρ K (fun g => c * e g) v = c • PositivityTheory.Rg.BcN.F2.hk ρ K e v := by
  unfold PositivityTheory.Rg.BcN.F2.hk
  rw [smul_finsum]
  exact finsum_congr fun q => mul_smul _ _ _

theorem UpperTheory.HeckeLevelFrameExistence.locE :
    UpperTheory.HeckeLevelFrameExistence.LocE := by
  intro E _ _ _ n w hw K' hKo hKle hlev σ hσ k D
  have hUL : UL n w = ⊤ := by unfold UL; rw [if_pos hw]
  have hmap : (K'.subgroupOf (UL n w)).map (UL n w).subtype = K' := by
    rw [Subgroup.subgroupOf_map_subtype, hUL, inf_top_eq]
  have hKc : IsCompact (K' : Set (GLw n w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K' hKo) hKle
  obtain ⟨P, T, hT, hcomp, hdict⟩ := GlobalTheory.CompanionTheory.SplitPlace.splitDict E n w hw σ
  have hd := hdict (K'.subgroupOf (UL n w)) hlev
  rw [hmap] at hd
  obtain ⟨y₀, hy₀, hy₀0⟩ := (Submodule.ne_bot_iff _).1 hσ
  have hz : PositivityTheory.Rg.BcN.F2.IsHk K' (0 : GLw n w → ℂ) :=
    ⟨hKo, hKc, HasCompactSupport.zero, fun _ _ _ _ _ => rfl⟩
  have hP0 : ∃ v ∈ fixed P.ρ K', v ≠ 0 :=
    ⟨T y₀, ((hd 0 hz).2 y₀ hy₀).1, fun h => hy₀0 (T.map_eq_zero_iff.1 h)⟩
  have hchoice : PositivityTheory.Rg.BcB.F.Choice.ChoiceS :=
    PositivityTheory.Rg.BcB.F.Choice.choiceS_of
      (fun E _ _ _ n w => GlobalTheory.T.isolate_representation_at_character (w.adicCompletion E) (Fin n))
      (fun E _ _ _ n w => GlobalTheory.T.finite_subquotients (w.adicCompletion E) (Fin n))
      (fun E _ _ _ n w => GlobalTheory.T.finite_length_of_products (w.adicCompletion E) (Fin n))
  obtain ⟨e₀, hIk, ⟨v₀, hv₀, l, hl1, hl⟩, hkill⟩ :=
    hchoice E n w K' hKo hKc P hP0 k D
  set r : ℂ := (((K'.subgroupOf (UL n w)).relIndex (KL n w) : ℕ) : ℂ) with hr
  have hIk' : PositivityTheory.Rg.BcN.F2.IsHk K' (fun g => r * e₀ g) :=
    ⟨hIk.1, hIk.2.1, hIk.2.2.1.mul_left, fun k₁ h₁ k₂ h₂ g => by
      simp only [hIk.2.2.2 k₁ h₁ k₂ h₂ g]⟩
  have hH := (hd _ hIk').1
  refine ⟨fun g => r * e₀ g, P, hIk', hH, hcomp, ?_, ?_⟩
  · have hy : T.symm v₀ ∈ fixed σ.ρ (K'.subgroupOf (UL n w)) := by
      rintro ⟨x, hx⟩
      apply T.injective
      have h1 := hv₀ ⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩
      rw [map_smul, hT, T.apply_symm_apply]
      simpa using h1
    refine ⟨⟨T.symm v₀, hy⟩, fun h => ?_, ?_⟩
    · have h0 : T.symm v₀ = 0 := congrArg Subtype.val h
      have h1 : v₀ = 0 := T.symm.map_eq_zero_iff.1 h0
      rw [h1, map_zero] at hl1
      exact zero_ne_one hl1
    · apply Subtype.ext
      rw [(GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ _ hlev _ _ hH hH).2.1]
      apply T.injective
      have h2 := ((hd e₀ hIk).2 _ hy).2
      rw [T.apply_symm_apply, hl v₀ hv₀, hl1, one_smul] at h2
      rw [h2, T.apply_symm_apply]
  · intro j τ hs hne v hv
    rw [hk_const_mul, hkill j τ hs hne v hv, smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEig
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.HeckeLevelFrameExistence.powEig :
    UpperTheory.HeckeLevelFrameExistence.PowEig := by
  intro E _ _ _ n w σ K' hlev g hg y hy m
  have key : ∀ k : ℕ, IsHecke K' (U.lpow K' g k) ∧ locOp σ K' (U.lpow K' g k) y = y := by
    intro k
    induction k with
    | zero =>
      obtain ⟨-, -, -, -, -, -, h1, h2⟩ := GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ K' hlev g g hg hg
      refine ⟨h1, ?_⟩
      show locOp σ K' ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) y = y
      rw [h2]
      rfl
    | succ k ih =>
      obtain ⟨-, -, h3, -, h5, -⟩ := GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ K' hlev g _ hg ih.1
      refine ⟨h3, ?_⟩
      show locOp σ K' (lconv g (U.lpow K' g k)) y = y
      rw [h5, Module.End.mul_apply, ih.2, hy]
  exact (key m).2
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.FX
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

theorem gcHecke : GcHecke := by
  intro E _ _ _ n w hw b ϖ c
  have hg : gc w b ϖ c = ∑ x ∈ c.support,
      (c x * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)) • fU n w b ϖ (lOf x) := by
    funext γ
    simp only [gc, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hg]
  exact isHecke_fsum _ _ _ _ fun x => GlobalTheory.CompanionTheory.MatchPow.fU_hecke hw b ϖ _ (GlobalTheory.LocFinU.continuous_cj w)

theorem frameEx_of_fin (hUS : USide) (hCF : CandFin) : FrameEx :=
  frameEx_of hUS (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.CompanionTheory.LocHecke.locAlg) (GlobalTheory.T.spectral_trace_of_model_algebra GlobalTheory.T.unitary_model_holds GlobalTheory.CompanionTheory.LocHecke.locAlg)
    GlobalTheory.CompanionTheory.LocHecke.locAlg (exTbOf Inert.frameInert_all.1 Inert.frameInert_all.2.1 inertInSec) Inert.frameInert_all.2.2.2.1
    Inert.frameInert_all.2.2.2.2.1 (coneEigOf eigInert LemB.bcWeyl) satCompAt candIndep hCF
    (fun _ _ _ _ _ _ _ _ _ _ F₀ => mok0 F₀) IndefiniteRowSideFullHecke.coneTwo' gcHecke
    (locC IndefiniteRowSideFullHecke.shufEx' IndefiniteRowSideFullHecke.vResStd' IndefiniteRowSideFullHecke.shufStd' targetAlg monoRes) locE muVal powEig

end UpperTheory.HeckeLevelFrameExistence

end
