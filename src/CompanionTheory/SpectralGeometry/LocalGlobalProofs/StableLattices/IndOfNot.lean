module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IndOfNot
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSNormLt

open CompanionTheory.D.DSIC

variable {n : ℕ}

def sig (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0

theorem sig_anti (a b : Fin n) : sig b a = - sig a b := by
  unfold sig
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.not_gt]
  · simp [h]
  · simp [h, h.not_gt]

theorem sig_mul {y : Fin n → ℝ} (hy : Antitone y) (a b : Fin n) : sig a b * (y a - y b) = |y a - y b| := by
  unfold sig
  rcases lt_trichotomy a b with h | h | h
  · rw [if_pos h, one_mul, abs_of_nonneg (sub_nonneg.2 (hy h.le))]
  · simp [h]
  · rw [if_neg h.not_gt, if_pos h, abs_of_nonpos (sub_nonpos.2 (hy h.le))]; ring

theorem pair_eq (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (x : Fin n → ℝ) :
    4 * ∑ a, x a * ((∑ b, t a b) / 2) = ∑ a, ∑ b, t a b * (x a - x b) := by
  have h1 : ∑ a, ∑ b, t a b * x b = - ∑ a, ∑ b, t a b * x a := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ht a b]; ring
  have h2 : ∑ a, x a * ((∑ b, t a b) / 2) = (∑ a, ∑ b, t a b * x a) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul]; ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2]; ring

theorem term_le {s z : ℝ} (hs : |s| ≤ 1) : s * z ≤ |z| := by
  calc s * z ≤ |s * z| := le_abs_self _
    _ = |s| * |z| := abs_mul _ _
    _ ≤ 1 * |z| := by gcongr
    _ = |z| := one_mul _

theorem normSq_le (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (h1 : ∀ a b, |t a b| ≤ 1) :
    ∑ a, ((∑ b, t a b) / 2) ^ 2 ≤ ∑ a : Fin n, ((∑ b, sig a b) / 2) ^ 2 := by
  set x : Fin n → ℝ := fun a => (∑ b, t a b) / 2 with hx
  set r : Fin n → ℝ := fun a => (∑ b, sig a b) / 2 with hr
  let τ : Equiv.Perm (Fin n) := Tuple.sort (fun a => - x a)
  have hτ : Antitone (fun a => x (τ a)) := by
    intro a b hab
    have := Tuple.monotone_sort (fun a => - x a) hab
    simpa using this
  have e1 : 4 * ∑ a, x a ^ 2 ≤ 4 * ∑ a, x (τ a) * r a := by
    have := pair_eq t ht x
    have h2 := pair_eq sig sig_anti (fun a => x (τ a))
    calc 4 * ∑ a, x a ^ 2 = ∑ a, ∑ b, t a b * (x a - x b) := by
          rw [← this]; simp only [hx, sq]
      _ ≤ ∑ a, ∑ b, |x a - x b| :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => term_le (h1 a b)
      _ = ∑ a, ∑ b, |x (τ a) - x (τ b)| := by
          rw [← Equiv.sum_comp τ]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Equiv.sum_comp τ]
      _ = ∑ a, ∑ b, sig a b * (x (τ a) - x (τ b)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (sig_mul hτ a b).symm
      _ = _ := h2.symm
  have e2 : 2 * ∑ a, x (τ a) * r a ≤ ∑ a, x (τ a) ^ 2 + ∑ a, r a ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => by nlinarith [sq_nonneg (x (τ a) - r a)]
  have e3 : ∑ a, x (τ a) ^ 2 = ∑ a, x a ^ 2 := Equiv.sum_comp τ (fun a => x a ^ 2)
  show ∑ a, x a ^ 2 ≤ ∑ a, r a ^ 2
  linarith

theorem pair_lt (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (h1 : ∀ a b, |t a b| ≤ 1)
    {lam : Fin n → ℝ} (hl : StrictAnti lam) (c d : Fin n) (hcd : c ≠ d) (hne : t c d = - sig c d) :
    ∑ a, lam a * ((∑ b, t a b) / 2) < ∑ a, lam a * ((∑ b, sig a b) / 2) := by
  have e1 := pair_eq t ht lam
  have e2 := pair_eq sig sig_anti lam
  have hle : ∀ a b, t a b * (lam a - lam b) ≤ sig a b * (lam a - lam b) := fun a b => by
    rw [sig_mul hl.antitone]; exact term_le (h1 a b)
  have : ∑ a, ∑ b, t a b * (lam a - lam b) < ∑ a, ∑ b, sig a b * (lam a - lam b) := by
    refine Finset.sum_lt_sum (fun a _ => Finset.sum_le_sum fun b _ => hle a b) ⟨c, mem_univ _, ?_⟩
    refine Finset.sum_lt_sum (fun b _ => hle c b) ⟨d, mem_univ _, ?_⟩
    rw [hne, neg_mul, sig_mul hl.antitone]
    have : 0 < |lam c - lam d| := abs_pos.2 (sub_ne_zero.2 fun h => hcd (hl.injective h))
    linarith
  linarith


open Classical in
def ind {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : ℝ :=
  if ∃ h : ε a = true ∧ ε b = false, (⟨(a, b), h⟩ : NC ε) ∈ A then 1 else 0

theorem wtA_eq {ε : Fin n → Bool} (A : Finset (NC ε)) (c : Fin n) :
    wtA A c = ∑ b, (ind A c b - ind A b c) := by
  classical
  rw [Finset.sum_sub_distrib]
  unfold wtA ind
  rw [Finset.sum_boole, Finset.sum_boole]
  congr 2
  · refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · rintro ⟨⟨a, b⟩, h⟩ hi
      simp only [mem_filter] at hi
      obtain ⟨hi, rfl⟩ := hi
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨h, hi⟩
    · rintro ⟨⟨a, b⟩, h⟩ hi ⟨⟨a', b'⟩, h'⟩ hi' e
      simp only [mem_filter] at hi hi' e
      obtain ⟨_, rfl⟩ := hi
      obtain ⟨_, rfl⟩ := hi'
      subst e
      rfl
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      obtain ⟨h, hb⟩ := hb
      exact ⟨⟨(c, b), h⟩, mem_filter.2 ⟨hb, rfl⟩, rfl⟩
  · refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · rintro ⟨⟨a, b⟩, h⟩ hi
      simp only [mem_filter] at hi
      obtain ⟨hi, rfl⟩ := hi
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨h, hi⟩
    · rintro ⟨⟨a, b⟩, h⟩ hi ⟨⟨a', b'⟩, h'⟩ hi' e
      simp only [mem_filter] at hi hi' e
      obtain ⟨_, rfl⟩ := hi
      obtain ⟨_, rfl⟩ := hi'
      subst e
      rfl
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      obtain ⟨h, hb⟩ := hb
      exact ⟨⟨(b, c), h⟩, mem_filter.2 ⟨hb, rfl⟩, rfl⟩

theorem ind_of_not {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ¬ (ε a = true ∧ ε b = false)) :
    ind A a b = 0 := by
  unfold ind
  rw [if_neg]
  rintro ⟨h', _⟩
  exact h h'

theorem ind_of {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ε a = true ∧ ε b = false) :
    ind A a b = if (⟨(a, b), h⟩ : NC ε) ∈ A then 1 else 0 := by
  unfold ind
  congr 1
  simp [h]

def tt {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : ℝ :=
  sig a b + 2 * ((ind (A1 ε) a b - ind (A1 ε) b a) - (ind A a b - ind A b a))

theorem tt_anti {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : tt A b a = - tt A a b := by
  unfold tt; rw [sig_anti a b]; ring

theorem tt_of {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ε a = true ∧ ε b = false) :
    tt A a b = if ((⟨(a, b), h⟩ : NC ε) ∈ A ↔ (⟨(a, b), h⟩ : NC ε) ∈ A1 ε) then sig a b else - sig a b := by
  have h' : ¬ (ε b = true ∧ ε a = false) := by simp [h.1]
  have hab : a ≠ b := by rintro rfl; simp [h.1] at h
  unfold tt
  rw [ind_of_not _ h', ind_of_not _ h', ind_of _ h, ind_of _ h]
  have hm : (⟨(a, b), h⟩ : NC ε) ∈ A1 ε ↔ b < a := by simp [A1]
  simp only [hm]
  unfold sig
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> by_cases h2 : (⟨(a, b), h⟩ : NC ε) ∈ A <;>
    simp [h1, h1.not_gt, h2] <;> norm_num

theorem abs_sig (a b : Fin n) : |sig a b| ≤ 1 := by
  unfold sig; split_ifs <;> simp

theorem abs_tt {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : |tt A a b| ≤ 1 := by
  have key : ∀ a b : Fin n, (ε a = true ∧ ε b = false) → |tt A a b| ≤ 1 := fun a b h => by
    rw [tt_of A h]
    split_ifs
    · exact abs_sig a b
    · rw [abs_neg]; exact abs_sig a b
  by_cases h : ε a = true ∧ ε b = false
  · exact key a b h
  by_cases h' : ε b = true ∧ ε a = false
  · rw [tt_anti, abs_neg]; exact key b a h'
  unfold tt
  rw [ind_of_not _ h', ind_of_not _ h', ind_of_not _ h, ind_of_not _ h]
  simpa using abs_sig a b

theorem rho_eq (ε : Fin n → Bool) (a : Fin n) :
    PI.UpqRep.rhoC ε a + PI.UpqRep.rhoN ε a = (∑ b, sig a b) / 2 := by
  unfold PI.UpqRep.rhoC PI.UpqRep.rhoN
  rw [← add_div]
  congr 1
  simp only [Finset.card_filter, Nat.cast_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold sig
  rcases lt_trichotomy a b with h | h | h
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2]
  · simp [h]
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2]

theorem normLt : CompanionTheory.D.DSIC.NormLt := by
  intro n ε lam hl A hA
  obtain ⟨⟨⟨c, d⟩, h⟩, hi⟩ : ∃ i : NC ε, ¬ (i ∈ A ↔ i ∈ A1 ε) := by
    by_contra hc
    push Not at hc
    exact hA (Finset.ext fun i => by simpa using hc i)
  have hcd : c ≠ d := by rintro rfl; simp [h.1] at h
  have hne : tt A c d = - sig c d := by rw [tt_of A h, if_neg hi]
  have i1 := pair_lt (tt A) (tt_anti A) (abs_tt A) hl c d hcd hne
  have i2 := normSq_le (tt A) (tt_anti A) (abs_tt A)
  have f1 : ∀ a, (gam ε lam - wtA A + (2 : ℝ) • PI.UpqRep.rhoC ε) a = lam a + (∑ b, tt A a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [gam, PI.UpqRep.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, wtA_eq, tt,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_sub_distrib (f := fun b => ind (A1 ε) a b - ind (A1 ε) b a)]
    linarith
  have f2 : ∀ a, (PI.UpqRep.lowK ε lam + (2 : ℝ) • PI.UpqRep.rhoC ε) a = lam a + (∑ b, sig a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [PI.UpqRep.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have ex : ∀ y : Fin n → ℝ, ∑ a, (lam a + y a) * (lam a + y a) =
      ∑ a, lam a ^ 2 + 2 * ∑ a, lam a * y a + ∑ a, y a ^ 2 := fun y => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  unfold PI.UpqRep.vNormSq PI.UpqRep.nsq PI.UpqRep.dot
  simp only [f1, f2]
  rw [ex, ex]
  linarith

end GlobalTheory.CompanionTheory.DSNormLt
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WlemOfGfacts
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICWLem

open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)

def ht {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - (c : ℕ)) * w c

theorem ht_add_root {n : ℕ} (w : Fin n → ℝ) (c d : Fin n) (h : c < d) :
    ht w < ht (w + Pi.single c 1 - Pi.single d 1) := by
  have hcd : ((c : ℕ) : ℝ) < ((d : ℕ) : ℝ) := by exact_mod_cast h
  have : ht (w + Pi.single c 1 - Pi.single d 1) =
      ht w + ((n : ℝ) - (c : ℕ)) - ((n : ℝ) - (d : ℕ)) := by
    simp [ht, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
  rw [this]
  linarith

theorem wlem_of_gfacts (hG : GFacts) : WLem := by
  intro n ε V _ _ E γ x hx hK
  obtain ⟨g, hg, -, hwt, hdiag, -⟩ := hG n ε
  classical
  have hne : (univ.filter fun A : Finset (NC ε) => x A ≠ 0).Nonempty := by
    by_contra hc
    apply hx
    funext A
    by_contra hA
    exact hc ⟨A, by simpa using hA⟩
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image _ (fun A : Finset (NC ε) => ht (wtA A)) hne
  have hA0 : x A ≠ 0 := by simpa using hA
  refine ⟨A, hA0, ?_⟩
  have hF : ∀ c d, Fop ε E c d x A = E c d (x A) + ∑ B, (g c d A B : ℂ) • x B := by
    intro c d
    rw [← hg V c d x A]
    rfl
  refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
  · have h1 := congrFun (hK.1 a) A
    rw [hF] at h1
    have h2 : ∑ B, (g a a A B : ℂ) • x B = (wtA A a : ℂ) • x A := by
      rw [Finset.sum_eq_single A]
      · simp [hdiag]
      · intro B _ hB
        simp [hdiag, Ne.symm hB]
      · simp
    rw [h2, Pi.smul_apply] at h1
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h1, add_sub_cancel_right]
  · have h1 := congrFun (hK.2 a b hab hε) A
    rw [hF] at h1
    have h2 : ∑ B, (g a b A B : ℂ) • x B = 0 := by
      refine Finset.sum_eq_zero fun B _ => ?_
      by_cases hgB : g a b A B = 0
      · simp [hgB]
      by_cases hxB : x B = 0
      · simp [hxB]
      exfalso
      have h3 := hmin B (by simpa using hxB)
      have h4 := ht_add_root (wtA B) a b hab
      rw [← (hwt a b A B hgB).2] at h4
      exact absurd h3 (not_le.mpr h4)
    rw [h2, add_zero] at h1
    exact h1

end GlobalTheory.CompanionTheory.DSICWLem
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NotCdomAddRoot
open Finset

namespace GlobalTheory.CompanionTheory.DSHighestOfKType

open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)

variable {n : ℕ}

theorem height_root (a b : Fin n) : ∑ i : Fin n, ((i : ℕ) : ℝ) * root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem not_cdom_add_root (ε : Fin n → Bool) (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ CDom ε (μ + root a b) μ := by
  rintro ⟨c, hc, h⟩
  have h1 : ∑ i : Fin n, ((i : ℕ) : ℝ) * (μ - (μ + root a b)) i = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    have : ∀ i : Fin n, ((i : ℕ) : ℝ) * (μ - (μ + root a b)) i = -(((i : ℕ) : ℝ) * root a b i) := by
      intro i; simp
    simp only [this, Finset.sum_neg_distrib, height_root]; ring
  have h2 : ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ x, ∑ y, (c x y : ℝ) • root x y) i
      = ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) := by
    simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h3 : ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have hxy : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast (hc x y h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  rw [h, h2] at h1
  linarith

theorem isWeight_apply {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {μ : Fin n → ℝ} {v : V} (hv : IsWeight E μ v) (a b : Fin n) :
    IsWeight E (μ + root a b) (E a b v) := by
  intro c
  have h := LinearMap.congr_fun (hE c c a b) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [root]
  · subst h1; simp [root, h2, Ne.symm h2, add_smul, add_comm]
  · subst h2; simp [root, h1, add_smul, add_comm]
  · simp [root, h1, h2, Ne.symm h2]

theorem hwOfType : CompanionTheory.D.DSIC.StabLink → CompanionTheory.D.DSIC.WtLink → CompanionTheory.D.DSIC.HWofType := by
  intro hS hW n ε H _ _ σ S E hσ hm μ T hT hTS
  obtain ⟨hfin, hst, -, ⟨v, hvT, hv0, hvw⟩, hdom⟩ := hT
  have hmap : (T.comap S.subtype).map S.subtype = T := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hTS
  have hfinU : FiniteDimensional ℂ (T.comap S.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hTS).symm.finiteDimensional
  have hU := (hS n ε H σ S E hσ hm _ hfinU).2 (by rw [hmap]; exact hst)
  have hw : IsWeight E μ (⟨v, hTS hvT⟩ : S) := (hW n ε H σ S E hσ hm μ _).2 hvw
  refine ⟨⟨v, hTS hvT⟩, fun h => hv0 (congrArg Subtype.val h), hvT, hw, fun a b hab hε => ?_⟩
  by_contra hne
  have hmem := hU a b hε ⟨v, hTS hvT⟩ hvT
  have hw' := (hW n ε H σ S E hσ hm _ _).1 (isWeight_apply hm.gl hw a b)
  exact not_cdom_add_root ε μ hab (hdom _ _ hmem (fun h => hne (Subtype.ext h)) hw')

end GlobalTheory.CompanionTheory.DSHighestOfKType
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExt
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmBracket

open CompanionTheory.D.Upq.Sm
open PI.UpqRep (UJset IsURepOn inG)
open PI.PhMeasCore (dsig smoothVecs)

theorem fderiv_comm {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {x : E} (hF : ContDiffAt ℝ ∞ F x) (L M : E →L[ℝ] E) {a b c : E}
    (ha : M x = a) (hb : L x = b) (hc : L a - M b = c) :
    fderiv ℝ (fun g => fderiv ℝ F g (L g)) x a - fderiv ℝ (fun g => fderiv ℝ F g (M g)) x b =
      fderiv ℝ F x c := by
  subst ha hb hc
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).differentiableAt (by simp)
  have hs : IsSymmSndFDerivAt ℝ F x :=
    hF.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  rw [(hD.hasFDerivAt.clm_apply L.hasFDerivAt).fderiv, (hD.hasFDerivAt.clm_apply M.hasFDerivAt).fderiv]
  simp [hs (M x) (L x)]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem lie_bracket {J X Y : Mat n} (hX : Xᴴ * J + J * X = 0) (hY : Yᴴ * J + J * Y = 0) :
    (X * Y - Y * X)ᴴ * J + J * (X * Y - Y * X) = 0 := by
  have hLX : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have hLY : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * J = J * (Y * X) := by
    rw [Matrix.mul_assoc, hLX, Matrix.mul_neg, ← Matrix.mul_assoc, hLY, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have e2 : Xᴴ * Yᴴ * J = J * (X * Y) := by
    rw [Matrix.mul_assoc, hLY, Matrix.mul_neg, ← Matrix.mul_assoc, hLX, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem hasDerivAt_ext (h : RepOn G σ) {X g : Mat n} (hX : ∀ t, ex X t ∈ G) (hg : g ∈ G) {f F : Mat n → H}
    {U : Set (Mat n)} (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ G → f x = F x) :
    HasDerivAt (fun t => f (g * ex X t)) (fderiv ℝ F g (g * X)) 0 :=
  hasDerivAt_local (A := G) (γ := fun t => g * ex X t) (fun t => h.mul_mem _ hg _ (hX t))
    (by simp [ex_zero]) (hasDerivAt_mul_ex g X) hU hgU hF hfF

theorem ds_ds (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G) {v : H}
    (hv : IsSm G σ v) {F : Mat n → H} {U : Set (Mat n)} (hU : IsOpen U) (h1 : (1 : Mat n) ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ x ∈ U, x ∈ G → σ x v = F x) (L : Mat n →L[ℝ] Mat n)
    (hL : ∀ x, L x = x * Y) :
    ds σ X (ds σ Y v) = fderiv ℝ (fun g => fderiv ℝ F g (L g)) 1 X := by
  have hG : ContDiffOn ℝ ∞ (fun g => fderiv ℝ F g (L g)) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply L.contDiff.contDiffOn
  have hGe : ∀ g ∈ U, g ∈ G → σ g (ds σ Y v) = fderiv ℝ F g (L g) := by
    intro g hg hgG
    rw [apply_ds h hY hgG (hv.differentiableAt h hY), hL]
    exact (hasDerivAt_ext h (f := fun x => σ x v) hY hgG hU hg hF hfF).deriv
  have h2 := hasDerivAt_ext h (f := fun g => σ g (ds σ Y v)) hX h.one_mem hU h1 hG hGe
  simp only [Matrix.one_mul] at h2
  exact h2.deriv

theorem ds_bracket (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G)
    (hXY : ∀ t, ex (X * Y - Y * X) t ∈ G) {v : H} (hv : IsSm G σ v) :
    ds σ X (ds σ Y v) - ds σ Y (ds σ X v) = ds σ (X * Y - Y * X) v := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 h.one_mem
  have h2 := hasDerivAt_ext h (f := fun x => σ x v) hXY h.one_mem hU h1 hF hfF
  simp only [Matrix.one_mul] at h2
  have e : ds σ (X * Y - Y * X) v = fderiv ℝ F 1 (X * Y - Y * X) := h2.deriv
  let L : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ Y).toContinuousLinearMap
  have hL : ∀ x, L x = x * Y := by intro x; simp [L]
  let M : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hM : ∀ x, M x = x * X := by intro x; simp [M]
  rw [ds_ds h hX hY hv hU h1 hF hfF L hL, ds_ds h hY hX hv hU h1 hF hfF M hM, e]
  exact fderiv_comm (hF.contDiffAt (hU.mem_nhds h1)) L M ((hM 1).trans (Matrix.one_mul X))
    ((hL 1).trans (Matrix.one_mul Y)) (congrArg₂ (· - ·) (hL X) (hM Y))

theorem smBracket : CompanionTheory.D.DSIC.SmBracket := by
  intro n ε H _ _ σ hσ X Y hX hY v hv
  have h : RepOn (UJset ε) σ :=
    ⟨by simp [UJset, PI.UpqRep.inUJ], fun a ha b hb => Formalism.REAL.indefinite_unitary_mul_mem ε ha hb, hσ.1.1, hσ.1.2⟩
  have hex : ∀ Z, inG ε Z → ∀ t, ex Z t ∈ UJset ε := fun Z hZ t => Formalism.REAL.exp_indefinite_unitary_holds n ε Z hZ t
  exact ds_bracket h (hex X hX) (hex Y hY) (hex _ (lie_bracket hX hY)) hv

theorem smBracket_of : CompanionTheory.D.DSIC.SmLin → CompanionTheory.D.DSIC.SmBracket := fun _ => smBracket

end GlobalTheory.CompanionTheory.SmBracket
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumInsertErase
open Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DSChainAdj

open CompanionTheory.D.DSIC

variable {n : ℕ} {ε : Fin n → Bool}

theorem sg_insert (i : NC ε) (A : Finset (NC ε)) : sg i (insert i A) = sg i A := by
  unfold sg
  rw [Finset.filter_insert, if_neg (lt_irrefl _)]

theorem conj_sg (i : NC ε) (A : Finset (NC ε)) : (starRingEnd ℂ) (sg i A) = sg i A := by
  unfold sg
  simp

theorem sum_insert_erase (i : NC ε) (f : Finset (NC ε) → Finset (NC ε) → ℂ) :
    (∑ A : Finset (NC ε), if i ∈ A then 0 else f (insert i A) A) =
      ∑ B : Finset (NC ε), if i ∈ B then f B (B.erase i) else 0 := by
  have h1 : (∑ A : Finset (NC ε), if i ∈ A then 0 else f (insert i A) A) =
      ∑ A ∈ univ.filter (fun A : Finset (NC ε) => i ∉ A), f (insert i A) A := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases h : i ∈ A <;> simp [h]
  rw [h1, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun A => insert i A) (fun B => B.erase i) ?_ ?_ ?_ ?_ ?_
  · intro A _
    simp
  · intro B _
    simp
  · intro A hA
    have hA' : i ∉ A := by simpa using hA
    exact Finset.erase_insert hA'
  · intro B hB
    have hB' : i ∈ B := by simpa using hB
    exact Finset.insert_erase hB'
  · intro A hA
    have hA' : i ∉ A := by simpa using hA
    simp only [Finset.erase_insert hA']

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem term_adj (i : NC ε) (T T' : Module.End ℂ V) (h : ∀ x y : V, ⟪T x, y⟫_ℂ = -⟪x, T' y⟫_ℂ) (w x : Ch ε V) :
    ip (lift ε T (ann i w)) x = -ip w (lift ε T' (cre i x)) := by
  unfold ip
  have key := sum_insert_erase i (fun B A => sg i B * ⟪T (w B), x A⟫_ℂ)
  have hL : (∑ A, ⟪lift ε T (ann i w) A, x A⟫_ℂ) =
      ∑ A : Finset (NC ε), if i ∈ A then 0 else sg i (insert i A) * ⟪T (w (insert i A)), x A⟫_ℂ := by
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases hA : i ∈ A
    · simp [ann, hA]
    · simp [ann, hA, conj_sg, sg_insert, mul_comm]
  have hR : -(∑ A, ⟪w A, lift ε T' (cre i x) A⟫_ℂ) =
      ∑ B : Finset (NC ε), if i ∈ B then sg i B * ⟪T (w B), x (B.erase i)⟫_ℂ else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases hA : i ∈ A
    · simp [cre, hA, h]
    · simp [cre, hA]
  rw [hL, hR, key]

theorem ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Ch ε V) (x : Ch ε V) :
    ip (∑ i ∈ s, f i) x = ∑ i ∈ s, ip (f i) x := by
  unfold ip
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_apply, sum_inner]

theorem ip_sum_right {ι : Type} (s : Finset ι) (f : ι → Ch ε V) (w : Ch ε V) :
    ip w (∑ i ∈ s, f i) = ∑ i ∈ s, ip w (f i) := by
  unfold ip
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_apply, inner_sum]

theorem adj : CompanionTheory.D.DSIC.Adj := by
  intro n ε V _ _ E hE w x
  unfold bd bdA cob
  rw [LinearMap.sum_apply, LinearMap.sum_apply, ip_sum_left, ip_sum_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  refine term_adj i _ _ (fun a b => ?_) w x
  have h := hE i.1.1 i.1.2 a b
  have h1 := i.2.1
  have h2 := i.2.2
  rw [h]
  simp [Formalism.REAL.sgn, h1, h2]

end GlobalTheory.CompanionTheory.DSChainAdj
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreApply
open Finset CompanionTheory.D.DSIC

noncomputable section

namespace GlobalTheory.CompanionTheory.ChainCAR

variable {n : ℕ} {ε : Fin n → Bool}

theorem key_inj {i j : NC ε} (h : key i = key j) : i = j := by
  unfold key at h
  have hi := i.1.2.2
  have hj := j.1.2.2
  have hn : 0 < n := by omega
  have h2 : (i.1.2 : ℕ) = j.1.2 := by
    have := congrArg (· % n) h
    simpa [Nat.mul_add_mod_of_lt hi, Nat.mul_add_mod_of_lt hj] using this
  have h1 : (i.1.1 : ℕ) = j.1.1 := by
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right hn (Nat.add_right_cancel h)
  exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))

def tw (i j : NC ε) : ℂ := if key j < key i then -1 else 1

theorem tw_self (i : NC ε) : tw i i = 1 := by simp [tw]

theorem tw_mul_self (i j : NC ε) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_swap {i j : NC ε} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : key i ≠ key j := fun e => h (key_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

theorem sg_mul_self (i : NC ε) (A : Finset (NC ε)) : sg i A * sg i A = 1 := by
  unfold sg
  rw [← mul_pow]; simp

theorem sg_insert (i : NC ε) {j : NC ε} {A : Finset (NC ε)} (h : j ∉ A) :
    sg i (insert j A) = tw i j * sg i A := by
  unfold sg tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

theorem sg_erase (i : NC ε) {j : NC ε} {A : Finset (NC ε)} (h : j ∈ A) :
    sg i (A.erase j) = tw i j * sg i A := by
  have h1 := sg_insert i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_apply (i : NC ε) (x : Ch ε V) (A : Finset (NC ε)) :
    ann i x A = if i ∈ A then 0 else sg i A • x (insert i A) := rfl

theorem cre_apply (i : NC ε) (x : Ch ε V) (A : Finset (NC ε)) :
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := rfl

theorem ann_ann (i j : NC ε) : (ann i * ann j + ann j * ann i : Module.End ℂ (Ch ε V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    ann_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert j hi, sg_insert i hj, tw_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]

theorem cre_cre (i j : NC ε) : (cre i * cre j + cre j * cre i : Module.End ℂ (Ch ε V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    cre_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sg_erase j hi, sg_erase i hj, tw_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]

theorem ann_cre (i j : NC ε) :
    (ann i * cre j + cre j * ann i : Module.End ℂ (Ch ε V)) = if i = j then 1 else 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, ann_apply, cre_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ A
    · simp [hi, sg_erase i hi, tw_self, smul_smul, sg_mul_self, Finset.insert_erase hi]
    · simp [hi, sg_insert i hi, tw_self, smul_smul, sg_mul_self, Finset.erase_insert hi]
  have hji : j ≠ i := fun e => hij e.symm
  rw [if_neg hij, LinearMap.zero_apply, Pi.zero_apply]
  by_cases hi : i ∈ A
  · simp [hi, hij]
  by_cases hj : j ∈ A
  swap
  · simp [hj, hji]
  simp only [hi, hj, Finset.mem_insert, Finset.mem_erase, or_true, and_false, if_true, if_false]
  rw [sg_insert j hi, sg_erase i hj, tw_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul,
    ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]

theorem car : CompanionTheory.D.DSIC.CAR := fun _ _ _ _ _ i j => ⟨ann_ann i j, cre_cre i j, ann_cre i j⟩

end GlobalTheory.CompanionTheory.ChainCAR
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CardOther
open Finset
open CompanionTheory.D.DSIC

namespace GlobalTheory.CompanionTheory.GamDomProof

variable {n : ℕ}

theorem card_four (ε : Fin n → Bool) (a : Fin n) :
    ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card + 1 = n := by
  have h1 : (1 : ℝ) = ∑ b : Fin n, if b = a then (1 : ℝ) else 0 := by simp
  have h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ) := by simp
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [h2]
  nth_rewrite 5 [h1]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne', e]
  · simp [h]
  · by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne, e]

theorem card_fst (ε : Fin n → Bool) (a : Fin n) :
    ((A1 ε).filter fun i => i.1.1 = a).card =
      if ε a = true then (univ.filter fun b => b < a ∧ ε b ≠ ε a).card else 0 := by
  split_ifs with h
  · refine card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢
      obtain ⟨h1, rfl⟩ := hi
      exact ⟨h1, by simp [hx, hy]⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e
      simp only [A1, mem_filter, mem_univ, true_and] at hi hi' e
      apply Subtype.ext
      simp [hi.2, hi'.2, e]
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      refine ⟨⟨(a, b), h, by simpa [h] using hb.2⟩, ?_, rfl⟩
      simp [A1, hb.1]
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨x, y⟩, hx, hy⟩ _ e
    simp only at e hx
    exact h (e ▸ hx)

theorem card_snd (ε : Fin n → Bool) (a : Fin n) :
    ((A1 ε).filter fun i => i.1.2 = a).card =
      if ε a = true then 0 else (univ.filter fun b => a < b ∧ ε b ≠ ε a).card := by
  split_ifs with h
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨x, y⟩, hx, hy⟩ _ e
    simp only at e hy
    rw [e, h] at hy
    exact absurd hy (by simp)
  · have h' : ε a = false := by simpa using h
    refine card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢
      obtain ⟨h1, rfl⟩ := hi
      exact ⟨h1, by simp [hx, hy]⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e
      simp only [A1, mem_filter, mem_univ, true_and] at hi hi' e
      apply Subtype.ext
      simp [hi.2, hi'.2, e]
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      refine ⟨⟨(b, a), by simpa [h'] using hb.2, h'⟩, ?_, rfl⟩
      simp [A1, hb.1]

theorem card_other (ε : Fin n → Bool) (a : Fin n) (h : ε a = true) :
    (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = nb ε false := by
  simp only [nb, card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h' | h' | h'
  · cases e : ε b <;> simp [h, h', h'.not_gt]
  · simp [← h', h]
  · cases e : ε b <;> simp [h, h', h'.not_gt]

theorem gam_eq (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    gam ε lam a = lam a - ((n : ℝ) - 1) / 2 + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (if ε a = true then (nb ε false : ℝ) else 0) := by
  have h4 := card_four ε a
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, wtA, Pi.add_apply, Pi.sub_apply,
    card_fst, card_snd]
  split_ifs with h
  · rw [← card_other ε a h]
    push_cast
    linarith
  · push_cast
    linarith

theorem pos_le (ε : Fin n → Bool) (m : Fin n → ℤ) (hm : StrictAnti m) (c d : Fin n) (hcd : c < d)
    (e : ε c = ε d) :
    m d + (univ.filter fun b => b < d ∧ ε b = ε d).card ≤
      m c + (univ.filter fun b => b < c ∧ ε b = ε c).card := by
  have h1 : (univ.filter fun b => b < d ∧ ε b = ε d).card ≤
      (univ.filter fun b => b < c ∧ ε b = ε c).card + (Ico c d).card := by
    refine le_trans (card_le_card ?_) (card_union_le _ _)
    intro b hb
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_Ico] at hb ⊢
    rcases lt_or_ge b c with h | h
    · exact Or.inl ⟨h, hb.2.trans e.symm⟩
    · exact Or.inr ⟨h, hb.1⟩
  have h2 : (Ico c d).card ≤ (Ioc (m d) (m c)).card := by
    refine card_le_card_of_injOn m ?_ hm.injective.injOn
    intro b hb
    simp only [coe_Ico, coe_Ioc, Set.mem_Ico, Set.mem_Ioc] at hb ⊢
    exact ⟨hm hb.2, hm.antitone hb.1⟩
  rw [Int.card_Ioc] at h2
  have h3 := hm hcd
  omega

theorem gamDom : CompanionTheory.D.DSIC.GamDom := by
  intro n ε lam ⟨hanti, hint⟩
  choose m hm using hint
  have hm' : StrictAnti m := by
    intro a b hab
    have := hanti hab
    have h : (m b : ℝ) < m a := by rw [← hm, ← hm]; linarith
    exact_mod_cast h
  refine ⟨fun a => m a + (univ.filter fun b => b < a ∧ ε b = ε a).card
    + (if ε a = true then (nb ε false : ℤ) else 0), fun a => ?_, fun c d hcd e => ?_⟩
  · rw [gam_eq, hm]
    push_cast
    rfl
  · have := pos_le ε m hm' c d hcd e
    have h2 : (if ε d = true then (nb ε false : ℤ) else 0) = (if ε c = true then (nb ε false : ℤ) else 0) := by
      rw [e]
    simp only [h2]
    linarith

end GlobalTheory.CompanionTheory.GamDomProof
end
