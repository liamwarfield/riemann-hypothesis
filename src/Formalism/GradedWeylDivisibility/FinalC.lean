module

public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSYTPeel

@[expose] public section

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.EvalDeg
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem evalDegree : EvalDeg := by
  intro B _ τ _ x y c _ _ _ p
  apply lcdeg_degreeOf_aeval_le
  intro m hm
  have hf : ∀ v, degreeOf c ((fun v : τ => if v = x then (1 : MvPolynomial τ B)
      else if v = y then -X c else X v) v) ≤ (if v = y then 1 else 0) + (if v = c then 1 else 0) := by
    intro v
    by_cases hvx : v = x
    · subst hvx
      simp only [if_true]
      have h1 : degreeOf c (1 : MvPolynomial τ B) = 0 := by rw [← C_1, degreeOf_C]
      rw [h1]
      exact Nat.zero_le _
    · by_cases hvy : v = y
      · subst hvy
        simp only [hvx, if_false, if_true, degreeOf_neg]
        have h2 := lcdeg_degreeOf_X_le (R := B) c c
        simp only [if_true] at h2
        omega
      · simp only [hvx, hvy, if_false, zero_add]
        exact lcdeg_degreeOf_X_le (R := B) c v
  refine le_trans (Finset.sum_le_sum (g := fun v => m v * (if v = y then 1 else 0) +
    m v * (if v = c then 1 else 0)) fun v _ => ?_) ?_
  · rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (hf v)
  · rw [Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq]
    have hy := monomial_le_degreeOf y hm
    have hc := monomial_le_degreeOf c hm
    split_ifs <;> omega

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LeadInterlaced
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lclint_degreeOf_none_rename_some {B : Type*} [CommRing B] {σ : Type*}
    (p : MvPolynomial σ B) : degreeOf none (rename (some : σ → Option σ) p) = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero ((degreeOf_le_iff).2 ?_)
  intro m hm
  rw [support_rename_of_injective (Option.some_injective σ)] at hm
  obtain ⟨m', -, rfl⟩ := Finset.mem_image.1 hm
  exact (Finsupp.mapDomain_of_notMem_range m' none (by simp)).le

private theorem colAddGen_eq_rename_some_of_mem_dualWeyl {B : Type*} [CommRing B] {r n : ℕ}
    {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) B} (hf : f ∈ dualWeyl B r n ν)
    {l j : Fin n} (hlj : l < j) :
    colAddGen B l j f = rename some f := by
  unfold dualWeyl at hf
  rw [Submodule.mem_inf] at hf
  have h := hf.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply] at h
  exact sub_eq_zero.mp (h l j hlj)

theorem leadInterlaced_of (h1 : CompDeg) (h2 : LeadComp) (h3 : TwoColumn) : LeadInterlaced := by
  intro B _ _ r n ν f hf hf0
  intro l j hlj
  have hlt : l < j := Fin.lt_def.mpr (by omega)
  have hdeg : (colLex r n).degree
      (weightedHomogeneousComponent (pairW (r := r) l j)
        (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f) =
      (colLex r n).degree f :=
    h2 B r n (Fin r × Fin n →₀ ℕ) (pairW (r := r) l j) f
  have hcoeff : AddMonoidAlgebra.coeff (weightedHomogeneousComponent (pairW (r := r) l j)
        (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f)
      ((colLex r n).degree f) =
      AddMonoidAlgebra.coeff f ((colLex r n).degree f) := by
    simp only [coeff_weightedHomogeneousComponent, ↓reduceIte]
  have hg0 : weightedHomogeneousComponent (pairW (r := r) l j)
      (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f ≠ 0 := by
    intro h
    have hne : AddMonoidAlgebra.coeff f ((colLex r n).degree f) ≠ 0 :=
      (colLex r n).coeff_degree_ne_zero_iff.mpr hf0
    apply hne
    rw [← hcoeff, h]
    rfl
  have hcol : degreeOf none (colAddGen B l j f) ≤ 0 := by
    rw [colAddGen_eq_rename_some_of_mem_dualWeyl hf hlt, lclint_degreeOf_none_rename_some]
  have hcomp := h1 B r n l j
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) 0 f hcol
  have hhom := weightedHomogeneousComponent_isWeightedHomogeneous
    (w := pairW (r := r) l j)
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f
  have key := h3 B r n l j hlt 0 0
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) _ hg0 hhom
    (fun b hb => absurd hb (Nat.not_lt_zero _)) hcomp
  rw [hdeg] at key
  exact key

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.CompDeg
section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCcompLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lccompW {r n : ℕ} (l j : Fin n) : Option (Fin r × Fin n) → (Fin r × Fin n →₀ ℕ) :=
  fun o => match o with
    | none => 0
    | some v => pairW l j v

theorem lccomp_pairW_col {r n : ℕ} (l j : Fin n) (b : Fin r) :
    pairW (r := r) l j (b, l) = Finsupp.single (b, l) 1 := by
  unfold pairW
  split_ifs <;> rfl

theorem lccomp_image_var_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    IsWeightedHomogeneous (lccompW l j)
      ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) B)) (pairW l j v) := by
  split_ifs with h
  · refine IsWeightedHomogeneous.add (isWeightedHomogeneous_X B (lccompW l j) (some v)) ?_
    have hm := (isWeightedHomogeneous_X B (lccompW l j) none).mul
      (isWeightedHomogeneous_X B (lccompW l j) (some (v.1, l)))
    convert hm using 1
    show pairW l j v = 0 + pairW l j (v.1, l)
    rw [lccomp_pairW_col, zero_add]
    simp only [pairW, if_pos h]
  · exact isWeightedHomogeneous_X B (lccompW l j) (some v)

theorem lccomp_colAddGen_monomial_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (d : Fin r × Fin n →₀ ℕ) (a : B) :
    IsWeightedHomogeneous (lccompW l j) (colAddGen B l j (monomial d a))
      (Finsupp.weight (pairW l j) d) := by
  classical
  have hp : IsWeightedHomogeneous (lccompW l j)
      (∏ v ∈ d.support, ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) B)) ^ d v)
      (∑ v ∈ d.support, d v • pairW l j v) :=
    IsWeightedHomogeneous.prod _ _ _ fun v _ => (lccomp_image_var_homog l j v).pow _
  have hc : IsWeightedHomogeneous (lccompW l j) (C a : MvPolynomial (Option (Fin r × Fin n)) B) 0 :=
    isWeightedHomogeneous_C _ a
  have h := hc.mul hp
  rw [zero_add] at h
  rw [colAddGen, aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.weight_apply]
  exact h

theorem lccomp_colAddGen_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (ω : Fin r × Fin n →₀ ℕ) (f : MvPolynomial (Fin r × Fin n) B)
    (hf : IsWeightedHomogeneous (pairW l j) f ω) :
    IsWeightedHomogeneous (lccompW l j) (colAddGen B l j f) ω := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have h := lccomp_colAddGen_monomial_homog (B := B) l j d (AddMonoidAlgebra.coeff f d)
  rwa [hf (mem_support_iff.mp hd)] at h

theorem lccomp_sum_components {R : Type*} [CommRing R] {σ M : Type*} [AddCommMonoid M] [DecidableEq M]
    (w : σ → M) (f : MvPolynomial σ R) (T : Finset M)
    (hT : ∀ d ∈ f.support, Finsupp.weight w d ∈ T) :
    f = ∑ ω' ∈ T, weightedHomogeneousComponent w ω' f := by
  classical
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hT d (mem_support_iff.mpr hne))

private lemma weightedHomogeneousComponent_self_of_isWH_ring {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {m : M}
    {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hne
    exact hd (h (Ne.symm hne))

private lemma weightedHomogeneousComponent_eq_zero_of_ne_isWH {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {m n : M}
    {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w p m) (hn : n ≠ m) :
    weightedHomogeneousComponent w n p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with hd
  · by_contra hne
    exact hn (hd.symm.trans (h hne))
  · rfl

theorem lccomp_component_colAddGen {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (ω : Fin r × Fin n →₀ ℕ) (f : MvPolynomial (Fin r × Fin n) B) :
    weightedHomogeneousComponent (lccompW l j) ω (colAddGen B l j f) =
      colAddGen B l j (weightedHomogeneousComponent (pairW l j) ω f) := by
  classical
  have hf := lccomp_sum_components (pairW l j) f (f.support.image (Finsupp.weight (pairW l j)))
    (fun d hd => Finset.mem_image_of_mem _ hd)
  conv_lhs => rw [hf]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  by_cases hω : ω ∈ f.support.image (Finsupp.weight (pairW l j))
  · rw [Finset.sum_eq_single ω]
    · exact weightedHomogeneousComponent_self_of_isWH_ring
        (lccomp_colAddGen_homog l j ω _ (weightedHomogeneousComponent_isWeightedHomogeneous ω f))
    · intro b _ hb
      exact weightedHomogeneousComponent_eq_zero_of_ne_isWH
        (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f))
        (Ne.symm hb)
    · intro h
      exact absurd hω h
  · rw [Finset.sum_eq_zero]
    · have h0 : weightedHomogeneousComponent (pairW l j) ω f = 0 := by
        ext d
        rw [coeff_weightedHomogeneousComponent]
        simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
        split_ifs with h
        · by_contra hne
          exact hω (h ▸ Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
        · rfl
      rw [h0, map_zero]
    · intro b hb
      refine weightedHomogeneousComponent_eq_zero_of_ne_isWH
        (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f)) ?_
      rintro rfl
      exact hω hb

theorem lccomp_degreeOf_component_le {R : Type*} [CommRing R] {σ M : Type*} [AddCommMonoid M]
    (w : σ → M) (ω : M) (p : MvPolynomial σ R) (i : σ) :
    degreeOf i (weightedHomogeneousComponent w ω p) ≤ degreeOf i p := by
  classical
  rw [degreeOf_le_iff]
  intro m hm
  apply monomial_le_degreeOf i
  rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact mem_support_iff.mpr hm
  · exact absurd rfl hm

end Formalism.GradedWeylDivisibility
end
end

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem componentDegree : CompDeg := by
  intro B _ r n l j ω s f hf
  rw [← lccomp_component_colAddGen]
  exact (lccomp_degreeOf_component_le _ _ _ _).trans hf

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColLexInitMinor
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem lcminor_initMinor_eq (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs = ∑ σ : Equiv.Perm (Fin s),
      monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
        (((Equiv.Perm.sign σ : ℤ) : R)) := by
  rw [initMinor, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply]
  rw [← mul_one (((Equiv.Perm.sign σ : ℤ) : R)), ← C_mul_monomial, monomial_sum_one,
    Units.smul_def, zsmul_eq_mul]
  congr 1

theorem colLexInitMinor_of (h : MinorExpLt) : ColLexInitMinor := by
  intro R _ _ r n s I hs hI
  rw [lcminor_initMinor_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin s)))]
  simp only [Equiv.Perm.one_apply, Equiv.Perm.sign_one, Units.val_one, Int.cast_one]
  set g := ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin s)),
    monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
      (((Equiv.Perm.sign σ : ℤ) : R)) with hg_def
  set e := ∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 with he
  have hdf : (colLex r n).degree (monomial e (1 : R)) = e := by
    classical
    rw [MonomialOrder.degree_monomial]
    simp
  by_cases hg : g = 0
  · rw [hg, add_zero, hdf, MonomialOrder.leadingCoeff_monomial]
    exact ⟨rfl, rfl⟩
  · have hne : (Finset.univ.erase (1 : Equiv.Perm (Fin s))).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      apply hg
      rw [hg_def, h0, Finset.sum_empty]
    have hlt : (colLex r n).toSyn ((colLex r n).degree g) <
        (colLex r n).toSyn ((colLex r n).degree (monomial e (1 : R))) := by
      rw [hdf]
      refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
      obtain ⟨σ0, hσ0⟩ := hne
      rw [Finset.sup_lt_iff (lt_of_le_of_lt bot_le (h r n s I hs hI σ0 (Finset.ne_of_mem_erase hσ0)))]
      intro σ hσ
      exact lt_of_le_of_lt (MonomialOrder.degree_monomial_le _) (h r n s I hs hI σ (Finset.ne_of_mem_erase hσ))
    rw [MonomialOrder.degree_add_of_lt hlt, MonomialOrder.leadingCoeff_add_of_lt hlt, hdf,
      MonomialOrder.leadingCoeff_monomial]
    exact ⟨rfl, rfl⟩

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColumnLexBideterminant
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem columnLexBideterminant_of_initialMinor (h : ColLexInitMinor) : ColumnLexBideterminant := by
  intro R _ _ r n K sz hsz I hI
  have hm : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      (colLex r n).leadingCoeff (initMinor R (I k) (hsz k)) = 1 :=
    fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).2
  have hreg : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      IsRegular ((colLex r n).leadingCoeff (initMinor R (I k) (hsz k))) := by
    intro k hk
    rw [hm k hk]
    exact isRegular_one
  refine ⟨?_, ?_⟩
  · unfold bideterminant bidetExp
    rw [MonomialOrder.degree_prod_of_regular hreg]
    exact Finset.sum_congr rfl fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).1
  · unfold bideterminant
    rw [MonomialOrder.leadingCoeff_prod_of_regular hreg]
    exact Finset.prod_eq_one hm

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.TwoColumn
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem apply_mul_le_weight_apply {σ : Type*} (w : σ → (σ →₀ ℕ)) (d : σ →₀ ℕ) (v x : σ) :
    d v * w v x ≤ Finsupp.weight w d x := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul]
  by_cases hv : v ∈ d.support
  · exact Finset.single_le_sum (f := fun i => d i * w i x) (fun i _ => Nat.zero_le _) hv
  · have h0 : d v = 0 := by
      by_contra h
      exact hv (Finsupp.mem_support_iff.mpr h)
    rw [h0, zero_mul]
    exact Nat.zero_le _

theorem lctwo_le_weight {r n : ℕ} {l j : Fin n} (hlj : l ≠ j) (d : Fin r × Fin n →₀ ℕ) (b : Fin r) :
    d (b, l) ≤ Finsupp.weight (pairW l j) d (b, l) ∧ d (b, j) ≤ Finsupp.weight (pairW l j) d (b, l) := by
  have hl : pairW (r := r) l j (b, l) = Finsupp.single (b, l) 1 := by
    simp [pairW, hlj]
  have hj : pairW (r := r) l j (b, j) = Finsupp.single (b, l) 1 := by
    simp [pairW]
  constructor
  · have h := apply_mul_le_weight_apply (pairW l j) d (b, l) (b, l)
    rwa [hl, Finsupp.single_eq_same, mul_one] at h
  · have h := apply_mul_le_weight_apply (pairW l j) d (b, j) (b, l)
    rwa [hj, Finsupp.single_eq_same, mul_one] at h

theorem lctwo_le_of_mem {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n} (hlj : l ≠ j)
    {ω : Fin r × Fin n →₀ ℕ} {p : MvPolynomial (Fin r × Fin n) B}
    (hp : IsWeightedHomogeneous (pairW l j) p ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ p.support) (b : Fin r) :
    m (b, l) ≤ ω (b, l) ∧ m (b, j) ≤ ω (b, l) := by
  have h := hp (MvPolynomial.mem_support_iff.mp hm)
  rw [← h]
  exact lctwo_le_weight hlj m b

theorem lctwo_sum_ite {r : ℕ} (a : Fin r) (e : ℕ) (f : Fin r → ℕ) (P : Fin r → Prop) [DecidablePred P] :
    (∑ b : Fin r with P b, ((if a = b then e else 0) + f b)) =
      (if P a then e else 0) + ∑ b : Fin r with P b, f b := by
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq]

theorem lctwo_main (h1 : PeelDecomp) (h2 : PeelHomog) (h3 : PeelLead) (h4 : PeelDegBound)
    (B : Type) [CommRing B] [IsDomain B] (r n : ℕ) (l j : Fin n) (hlj : l < j) :
    ∀ (d a0 s : ℕ) (ω : Fin r × Fin n →₀ ℕ) (g : MvPolynomial (Fin r × Fin n) B), r - a0 = d →
    g ≠ 0 → IsWeightedHomogeneous (pairW l j) g ω → (∀ b : Fin r, b.val < a0 → ω (b, l) = 0) →
    degreeOf none (colAddGen B l j g) ≤ s → InterlacedAt s l j ((colLex r n).degree g) := by
  intro d
  induction d with
  | zero =>
    intro a0 s ω g hd hg hω h0 _
    unfold InterlacedAt
    intro a
    have hmg := (colLex r n).degree_mem_support hg
    have hz : (∑ b : Fin r with b ≤ a, (colLex r n).degree g (b, j)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      have hb := b.isLt
      have hle := (lctwo_le_of_mem hlj.ne hω hmg b).2
      rw [h0 b (by omega)] at hle
      omega
    rw [hz]
    exact Nat.zero_le _
  | succ d ih =>
    classical
    intro a0 s ω g hd hg hω h0 hdeg
    have ha0 : a0 < r := by omega
    obtain ⟨A0, hA0⟩ : ∃ A0 : Fin r, A0.val = a0 := ⟨⟨a0, ha0⟩, rfl⟩
    have hmg := (colLex r n).degree_mem_support hg
    have hm_low : ∀ b : Fin r, b.val < a0 → (colLex r n).degree g (b, j) = 0 := by
      intro b hb
      have hle := (lctwo_le_of_mem hlj.ne hω hmg b).2
      rw [h0 b hb] at hle
      omega
    have hlow : ∀ b : Fin r, b < A0 → ω (b, l) = 0 := fun b hb =>
      h0 b (by rw [Fin.lt_def] at hb; omega)
    have hdec := h1 B r n l j hlj.ne A0 ω g hω
    have hvan : ∀ k, ω (A0, l) < k → peel l j A0 k g = 0 := by
      intro k hk
      unfold peel
      apply Finset.sum_eq_zero
      intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hle := (lctwo_le_of_mem hlj.ne hω hm'.1 A0).1
      exfalso
      omega
    have hex : ∃ k ∈ Finset.range (ω (A0, l) + 1), peel l j A0 k g ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hg (hdec.trans (Finset.sum_eq_zero fun k hk => by rw [hne k hk, mul_zero]))
    obtain ⟨k0, hk0, hk00⟩ := hex
    obtain ⟨K, hKT, hKmax⟩ := Finset.exists_max_image
      ((Finset.range (ω (A0, l) + 1)).filter (fun k => peel l j A0 k g ≠ 0)) id
      ⟨k0, Finset.mem_filter.mpr ⟨hk0, hk00⟩⟩
    obtain ⟨hKr, hK0⟩ := Finset.mem_filter.mp hKT
    have hKle : K ≤ ω (A0, l) := by
      have := Finset.mem_range.mp hKr
      omega
    have habove : ∀ k, K < k → peel l j A0 k g = 0 := by
      intro k hk
      by_contra hne
      by_cases hkω : k ≤ ω (A0, l)
      · have hkK := hKmax k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hne⟩)
        exact absurd (show k ≤ K from hkK) (by omega)
      · exact hne (hvan k (by omega))
    have hgK : g = ∑ k ∈ Finset.range (K + 1),
        X (A0, l) ^ k * X (A0, j) ^ (ω (A0, l) - K + (K - k)) * peel l j A0 k g := by
      have hsub : Finset.range (K + 1) ⊆ Finset.range (ω (A0, l) + 1) := by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      calc g = ∑ k ∈ Finset.range (ω (A0, l) + 1),
            X (A0, l) ^ k * X (A0, j) ^ (ω (A0, l) - k) * peel l j A0 k g := hdec
        _ = ∑ k ∈ Finset.range (K + 1),
            X (A0, l) ^ k * X (A0, j) ^ (ω (A0, l) - k) * peel l j A0 k g := by
          symm
          apply Finset.sum_subset hsub
          intro k _ hkK
          simp only [Finset.mem_range, not_lt] at hkK
          rw [habove k (by omega), mul_zero]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          have := Finset.mem_range.mp hk
          rw [show ω (A0, l) - K + (K - k) = ω (A0, l) - k by omega]
    have hdeg' : degreeOf none (colAddGen B l j (∑ k ∈ Finset.range (K + 1),
        X (A0, l) ^ k * X (A0, j) ^ (ω (A0, l) - K + (K - k)) * peel l j A0 k g)) ≤ s := by
      rw [← hgK]
      exact hdeg
    have hslice_supp : ∀ k, ∀ m ∈ (peel l j A0 k g).support, m (A0, l) = 0 ∧ m (A0, j) = 0 :=
      fun k => (h2 B r n l j hlj.ne A0 ω k g hω).2
    obtain ⟨he, hdegK⟩ := h4 B r n l j hlj.ne A0 K (ω (A0, l) - K) s
      (fun k => peel l j A0 k g) hslice_supp hK0 hdeg'
    have hlead := h3 B r n l j hlj A0 ω g K hω hlow hK0 habove
    have hhomK := (h2 B r n l j hlj.ne A0 ω K g hω).1
    have h0' : ∀ b : Fin r, b.val < a0 + 1 → (ω.erase (A0, l)) (b, l) = 0 := by
      intro b hb
      rw [Finsupp.erase_apply]
      split_ifs with hbA
      · rfl
      · apply h0 b
        have hne : b ≠ A0 := fun h => hbA (by rw [h])
        have hne' : b.val ≠ A0.val := fun h => hne (Fin.ext h)
        omega
    have hIH := ih (a0 + 1) (s - (ω (A0, l) - K) + K) (ω.erase (A0, l)) (peel l j A0 K g)
      (by omega) hK0 hhomK h0' hdegK
    have hmK := (colLex r n).degree_mem_support hK0
    have hm'_low : ∀ b : Fin r, b.val < a0 + 1 →
        (colLex r n).degree (peel l j A0 K g) (b, j) = 0 := by
      intro b hb
      have hle := (lctwo_le_of_mem hlj.ne hhomK hmK b).2
      rw [h0' b hb] at hle
      omega
    have hjx : ∀ b : Fin r, (colLex r n).degree g (b, j) =
        (if A0 = b then ω (A0, l) - K else 0) +
          (colLex r n).degree (peel l j A0 K g) (b, j) := by
      intro b
      rw [hlead]
      by_cases hb : A0 = b <;> simp [hlj.ne', hb]
    have hlx : ∀ b : Fin r, (colLex r n).degree g (b, l) =
        (if A0 = b then K else 0) + (colLex r n).degree (peel l j A0 K g) (b, l) := by
      intro b
      rw [hlead]
      by_cases hb : A0 = b <;> simp [hlj.ne, hb]
    unfold InterlacedAt at hIH ⊢
    intro a
    have hIa := hIH a
    by_cases haA : a.val < a0
    · have hz : (∑ b : Fin r with b ≤ a, (colLex r n).degree g (b, j)) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hba := Fin.le_iff_val_le_val.mp (Finset.mem_filter.mp hb).2
        exact hm_low b (by omega)
      rw [hz]
      exact Nat.zero_le _
    · have hsj : (∑ b : Fin r with b ≤ a, (colLex r n).degree g (b, j)) =
          (if A0 ≤ a then ω (A0, l) - K else 0) +
            ∑ b : Fin r with b ≤ a, (colLex r n).degree (peel l j A0 K g) (b, j) := by
        simp only [hjx]
        exact lctwo_sum_ite A0 (ω (A0, l) - K) _ (fun b => b ≤ a)
      have hsl : (∑ b : Fin r with b < a, (colLex r n).degree g (b, l)) =
          (if A0 < a then K else 0) +
            ∑ b : Fin r with b < a, (colLex r n).degree (peel l j A0 K g) (b, l) := by
        simp only [hlx]
        exact lctwo_sum_ite A0 K _ (fun b => b < a)
      have hAa : A0 ≤ a := Fin.le_iff_val_le_val.mpr (by omega)
      rw [hsj, hsl, if_pos hAa]
      by_cases hEq : a.val = a0
      · have hAa' : ¬ A0 < a := by
          rw [Fin.lt_def]
          omega
        have hz : (∑ b : Fin r with b ≤ a,
            (colLex r n).degree (peel l j A0 K g) (b, j)) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          have hba := Fin.le_iff_val_le_val.mp (Finset.mem_filter.mp hb).2
          exact hm'_low b (by omega)
        rw [if_neg hAa', hz]
        omega
      · have hAa' : A0 < a := by
          rw [Fin.lt_def]
          omega
        rw [if_pos hAa']
        omega

theorem twoColumn_of (h1 : PeelDecomp) (h2 : PeelHomog) (h3 : PeelLead) (h4 : PeelDegBound) : TwoColumn := by
  unfold TwoColumn
  intro B _ _ r n l j hlj a0 s ω g hg hω h0 hdeg
  exact lctwo_main h1 h2 h3 h4 B r n l j hlj (r - a0) a0 s ω g rfl hg hω h0 hdeg

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.MinorExpLt
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

private theorem cmIdx_val_eq {r n : ℕ} (v : Fin r × Fin n) :
    ((cmIdx r n v : Fin (n * r)) : ℕ) = v.1.val + r * v.2.val := by
  first
  | rfl
  | (simp only [cmIdx, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap,
      Prod.snd_swap, finProdFinEquiv_apply_val]; done)
  | (simp [cmIdx, finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]; done)
  | (simp [cmIdx]; ring)

private theorem col_lt_or_col_eq_row_lt_of_cmIdx_lt {r n : ℕ} {v w : Fin r × Fin n}
    (h : cmIdx r n v < cmIdx r n w) :
    v.2.val < w.2.val ∨ (v.2 = w.2 ∧ v.1 < w.1) := by
  have h0 : ((cmIdx r n v : Fin (n * r)) : ℕ) < ((cmIdx r n w : Fin (n * r)) : ℕ) := h
  rw [cmIdx_val_eq, cmIdx_val_eq] at h0
  have hv1 := v.1.isLt
  have hw1 := w.1.isLt
  rcases lt_trichotomy v.2.val w.2.val with h1 | h1 | h1
  · exact Or.inl h1
  · refine Or.inr ⟨Fin.ext h1, ?_⟩
    rw [h1] at h0
    show v.1.val < w.1.val
    omega
  · exfalso
    have hm : r * (w.2.val + 1) ≤ r * v.2.val := by
      first
      | exact Nat.mul_le_mul_left r h1
      | exact Nat.mul_le_mul_left h1 r
      | exact Nat.mul_le_mul (le_refl r) h1
    rw [Nat.mul_add, Nat.mul_one] at hm
    first
    | omega
    | linarith

private theorem domCongr_cmIdx_apply_cmIdx {r n : ℕ} (x : Fin r × Fin n →₀ ℕ) (v : Fin r × Fin n) :
    (Finsupp.domCongr (cmIdx r n) x) (cmIdx r n v) = x v := by
  first
  | (simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]; done)
  | (rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply])
  | (simp; done)

private theorem sum_single_castLE_apply' {r n s : ℕ} (τ : Fin s → Fin r) (hs : s ≤ n) (b : Fin r) (t : Fin n) :
    (∑ q : Fin s, Finsupp.single (τ q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
      if h : t.val < s then (if τ ⟨t.val, h⟩ = b then 1 else 0) else 0 := by
  rw [Finsupp.finsetSum_apply]
  by_cases h : t.val < s
  · rw [dite_eq_left h, Finset.sum_eq_single ⟨t.val, h⟩]
    · rw [Finsupp.single_apply]
      by_cases hb : τ ⟨t.val, h⟩ = b
      · have hp : (τ ⟨t.val, h⟩, Fin.castLE hs ⟨t.val, h⟩) = (b, t) := by
          first
          | exact Prod.ext hb (Fin.ext rfl)
          | exact Prod.ext_iff.2 ⟨hb, Fin.ext rfl⟩
          | (subst hb; rfl)
        rw [if_pos hp, if_pos hb]
      · rw [if_neg, if_neg hb]
        intro he
        exact hb (congrArg Prod.fst he)
    · intro q _ hq
      rw [Finsupp.single_apply, if_neg]
      intro he
      apply hq
      apply Fin.ext
      have h2 : (Fin.castLE hs q).val = t.val := congrArg (fun x => (x.2 : ℕ)) he
      exact h2
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro q _
    rw [Finsupp.single_apply, if_neg]
    intro he
    apply h
    have h2 : (Fin.castLE hs q).val = t.val := congrArg (fun x => (x.2 : ℕ)) he
    have h3 := q.isLt
    have h4 : (Fin.castLE hs q).val = q.val := rfl
    omega

private theorem toLex_lt_of_eq_below_of_apply_lt {N : ℕ} (x y : Fin N →₀ ℕ) (i : Fin N)
    (h1 : ∀ j, j < i → x j = y j) (h2 : x i < y i) : toLex x < toLex y := by
  first
  | exact ⟨i, h1, h2⟩
  | exact Finsupp.Lex.lt_of_forall_lt_of_lt _ _ i h1 h2
  | (show Finsupp.Lex (· < ·) (· < ·) x y; exact ⟨i, h1, h2⟩)
  | (show Pi.Lex (· < ·) (· < ·) x y; exact ⟨i, h1, h2⟩)
  | (rw [Finsupp.lex_def]; exact ⟨i, h1, h2⟩)

private theorem colLex_lt_of_toLex_domCongr_cmIdx_lt {r n : ℕ} {c d : Fin r × Fin n →₀ ℕ}
    (h : toLex (Finsupp.domCongr (cmIdx r n) c) <
      toLex (Finsupp.domCongr (cmIdx r n) d)) :
    c ≺[colLex r n] d := h

theorem minorExponentLt : MinorExpLt := by
  intro r n s I hs hI σ hσ
  have hex : ∃ q, σ q ≠ q := by
    by_contra h
    push_neg at h
    apply hσ
    ext x
    first
    | (rw [h x]; rfl)
    | simp [h x]
  obtain ⟨q0, hq0, hmin⟩ := (wellFounded_lt (α := Fin s)).has_min {q | σ q ≠ q} hex
  have hq0' : σ q0 ≠ q0 := hq0
  have hfix : ∀ q, q < q0 → σ q = q := fun q hq => by
    by_contra h
    exact hmin q h hq
  have hgt : q0 < σ q0 := by
    rcases lt_trichotomy (σ q0) q0 with h | h | h
    · exact absurd (σ.injective (hfix _ h)) h.ne
    · exact absurd h hq0'
    · exact h
  have hIlt : I q0 < I (σ q0) := hI hgt
  have hA : ∀ (b : Fin r) (t : Fin n),
      (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
        if h : t.val < s then (if I (σ ⟨t.val, h⟩) = b then 1 else 0) else 0 :=
    fun b t => sum_single_castLE_apply' (fun q => I (σ q)) hs b t
  have hB : ∀ (b : Fin r) (t : Fin n),
      (∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
        if h : t.val < s then (if I ⟨t.val, h⟩ = b then 1 else 0) else 0 :=
    fun b t => sum_single_castLE_apply' I hs b t
  have hcq : (Fin.castLE hs q0).val = q0.val := rfl
  have ht0 : (Fin.castLE hs q0).val < s := q0.isLt
  have e1 : (⟨(Fin.castLE hs q0).val, ht0⟩ : Fin s) = q0 := Fin.ext rfl
  apply colLex_lt_of_toLex_domCongr_cmIdx_lt
  apply toLex_lt_of_eq_below_of_apply_lt _ _ (cmIdx r n (I q0, Fin.castLE hs q0))
  · intro j hj
    obtain ⟨v, rfl⟩ := (cmIdx r n).surjective j
    rw [domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx]
    obtain ⟨b, t⟩ := v
    rw [hA, hB]
    have hlt := col_lt_or_col_eq_row_lt_of_cmIdx_lt hj
    try dsimp only at hlt
    rcases hlt with hlt | ⟨rfl, hb⟩
    · have ht : t.val < s := by
        have := q0.isLt
        omega
      have hlt' : (⟨t.val, ht⟩ : Fin s) < q0 := by
        show t.val < q0.val
        omega
      rw [dite_eq_left ht, dite_eq_left ht, hfix _ hlt']
    · rw [dite_eq_left ht0, dite_eq_left ht0, e1, if_neg (lt_trans hb hIlt).ne', if_neg hb.ne']
  · rw [domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx, hA, hB]
    rw [dite_eq_left ht0, dite_eq_left ht0, e1, if_neg hIlt.ne', if_pos (rfl : I q0 = I q0)]
    exact Nat.zero_lt_one

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LeadComp
open MvPolynomial

open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem leadingComponent : LeadComp := by
  intro R _ r n M _ w f
  classical
  by_cases hf : f = 0
  · subst hf; simp
  have hd : (colLex r n).degree f ∈
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f).support := by
    rw [mem_support_iff, coeff_weightedHomogeneousComponent, if_pos rfl]
    exact (colLex r n).coeff_degree_ne_zero_iff.mpr hf
  have hg0 : weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f ≠ 0 := by
    intro h; rw [h] at hd; simp at hd
  have h1 := (colLex r n).le_degree hd
  have h2 : (colLex r n).toSyn ((colLex r n).degree
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f)) ≤
      (colLex r n).toSyn ((colLex r n).degree f) := by
    apply (colLex r n).le_degree
    have h3 := (colLex r n).degree_mem_support hg0
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at h3
    split_ifs at h3 with h
    · exact mem_support_iff.mpr h3
    · exact absurd rfl h3
  exact (colLex r n).toSyn.injective (le_antisymm h2 h1)

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.StandardMonomialSpanOf
namespace Formalism.GradedWeylDivisibility

theorem standardMonomialSpanOf : StandardMonomialSpanOf := by
  intro h r n ν _
  exact h ℤ r n ν

end Formalism.GradedWeylDivisibility
end

namespace Formalism.GradedWeylDivisibility

theorem minorExpLt : MinorExpLt := minorExponentLt
theorem colLexInitMinor : ColLexInitMinor := colLexInitMinor_of minorExpLt
theorem column_lex_bideterminant : ColumnLexBideterminant := columnLexBideterminant_of_initialMinor colLexInitMinor
theorem colSums : ColSums := columnSums_holds
theorem sSYTPeel : SSYTPeel := semistandardPeel
theorem sSYTExists : SSYTExists := sSYTExists_of sSYTPeel
theorem compDeg : CompDeg := componentDegree
theorem leadComp : LeadComp := leadingComponent
theorem peelDecomp : PeelDecomp := peelDecomposition
theorem peelHomog : PeelHomog := sliceHomogeneous
theorem peelLead : PeelLead := sliceLeading
theorem evalDeg : EvalDeg := evalDegree
theorem peelDegBound : PeelDegBound := peelDegBound_of evalDeg
theorem twoColumn : TwoColumn := twoColumn_of peelDecomp peelHomog peelLead peelDegBound
theorem leadInterlaced : LeadInterlaced := leadInterlaced_of compDeg leadComp twoColumn
theorem standardMonomialSpanDomain : StandardMonomialSpanDomain :=
  semistandard_module_assembly column_lex_bideterminant colSums sSYTExists leadInterlaced

theorem standardMonomialSpan : StandardMonomialSpan :=
  standardMonomialSpanOf standardMonomialSpanDomain

private theorem bidet_rowPart_lemma {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) (k : ℕ) :
    ∀ (s : Finset (Fin K)) (m : Fin r × Fin n →₀ ℕ),
      m ∈ (∏ j ∈ s, initMinor ℤ (I j) (hsz j)).support → rowPart k m ≤ ∑ j ∈ s, min k (sz j) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    simp only [Finset.prod_empty] at hm
    have hm0 : m = 0 := by
      by_contra h
      apply (MvPolynomial.mem_support_iff.mp hm)
      rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)]
    subst hm0
    simp [rowPart_zero]
  | @insert j s hj ih =>
    intro m hm
    rw [Finset.prod_insert hj] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [rowPart_add, Finset.sum_insert hj]
    exact Nat.add_le_add ((initMinor_support (I j) (hsz j) m1 hm1).1 k) (ih m2 hm2)

private theorem sum_rowNu_lemma_2 {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ j, sz j ≤ n) (hnr : n ≤ r)
    (k : ℕ) :
    ∑ j : Fin K, min k (sz j) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) (shapeDeg (n := n) sz) a := by
  classical
  have h1 : ∀ a : Fin r, rowNu (r := r) (shapeDeg (n := n) sz) a =
      ∑ j : Fin K, if a.val < sz j then 1 else 0 := by
    intro a
    unfold rowNu
    split_ifs with h
    · unfold shapeDeg
      rw [Finset.card_filter]
    · symm
      apply Finset.sum_eq_zero
      intro j _
      have := hsz j
      exact if_neg (by omega)
  have h2 : ∀ j : Fin K, min k (sz j) = ∑ a : Fin r with a.val < k, if a.val < sz j then 1 else 0 := by
    intro j
    have hj : sz j ≤ r := (hsz j).trans hnr
    rw [← Finset.card_filter, Finset.filter_filter]
    have hset : (Finset.univ.filter fun a : Fin r => a.val < k ∧ a.val < sz j).map Fin.valEmbedding =
        Finset.range (min k (sz j)) := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨a, ha, rfl⟩
        omega
      · intro hx
        exact ⟨⟨x, by omega⟩, by simp only; omega, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hset, Finset.card_range]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_comm]
  exact le_of_eq (Finset.sum_congr rfl (fun j _ => h2 j))

theorem dualWeylDominanceZ :
    ∀ (r n : ℕ) (ν : Fin n → ℕ), n ≤ r → Antitone ν → ∀ f ∈ dualWeyl ℤ r n ν, ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a) ∧
      ∑ a : Fin r, rowDeg m a = ∑ a : Fin r, rowNu (r := r) ν a := by
  intro r n ν hnr hν f hf m hm
  have hcol := colSums ℤ r n ν f hf m hm
  refine ⟨fun k => ?_, ?_⟩
  · rw [standardMonomialSpan r n ν hν] at hf
    clear hcol
    show rowPart k m ≤ _
    induction hf using Submodule.span_induction generalizing m with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hν', rfl⟩ := hx
      subst hν'
      exact (bidet_rowPart_lemma sz hsz I k Finset.univ m hm).trans (sum_rowNu_lemma_2 sz hsz hnr k)
    | zero => simp at hm
    | add x y _ _ ihx ihy =>
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · exact ihx m h
      · exact ihy m h
    | smul a x _ ihx =>
      exact ihx m (MvPolynomial.support_smul hm)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnr
    have hL : ∑ a : Fin (n + d), rowDeg m a = ∑ s : Fin n, ν s := by
      unfold rowDeg
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun s _ => hcol s)
    rw [hL, Fin.sum_univ_add]
    simp [rowNu]

end Formalism.GradedWeylDivisibility
