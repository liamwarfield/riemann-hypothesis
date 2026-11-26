module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertEigenvalues.AbsEigB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertEigenvalues.AdmissibleTransport

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertEigenvalues.IndexUA
noncomputable section

open Matrix Formalism.UG GlobalTheory.BCT GlobalTheory.BorelUMod GlobalTheory.LGrp

namespace PositivityTheory.Rg.BcB.F.Eig.IndexUAAux

theorem cone_anti {m : ℕ} {l : Fin m → ℤ} (hl : Cone l) {i j : Fin m} (h : i ≤ j) : l j ≤ l i := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (j : ℕ) = i + k := ⟨j - i, by have := Fin.le_def.1 h; omega⟩
  induction k generalizing j with
  | zero =>
    have hji : j = i := Fin.ext (by omega)
    exact le_of_eq (congrArg l hji)
  | succ k ih =>
    have hj1 : (j : ℕ) - 1 < m := by omega
    have h1 : 2 ≤ l ⟨(j : ℕ) - 1, hj1⟩ - l j := hl.1 ⟨(j : ℕ) - 1, hj1⟩ j (by show (j : ℕ) = (j : ℕ) - 1 + 1; omega)
    have h2 : l ⟨(j : ℕ) - 1, hj1⟩ ≤ l i :=
      ih (Fin.le_def.2 (by show (i : ℕ) ≤ (j : ℕ) - 1; omega)) (by show (j : ℕ) - 1 = (i : ℕ) + k; omega)
    linarith

theorem wexp_anti {n : ℕ} {l : Fin (n / 2) → ℤ} (hl : Cone l) {i j : Fin n} (h : i ≤ j) :
    wexp n l j ≤ wexp n l i := by
  have hij : (i : ℕ) ≤ j := Fin.le_def.1 h
  have hP' : ∀ x : Fin (n / 2), 0 < l x := fun x => by linarith [hl.2 x]
  have hA : ∀ a b : ℕ, ∀ (ha : a < n / 2) (hb : b < n / 2), a ≤ b → l ⟨b, hb⟩ ≤ l ⟨a, ha⟩ :=
    fun a b ha hb hab => cone_anti hl (Fin.le_def.2 hab)
  delta wexp
  beta_reduce
  split_ifs
  all_goals first
    | omega
    | exact hA _ _ _ _ (by omega)
    | exact neg_le_neg (hA _ _ _ _ (by omega))
    | exact (neg_nonpos.2 (hP' _).le).trans (hP' _).le
    | exact (hP' _).le
    | exact neg_nonpos.2 (hP' _).le
    | exact le_rfl

theorem wexp_rev {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) : wexp n l i.rev = -wexp n l i := by
  have hr : (i.rev : ℕ) = n - (i + 1) := Fin.val_rev i
  have hl' : ∀ a b : ℕ, ∀ (ha : a < n / 2) (hb : b < n / 2), a = b → l ⟨a, ha⟩ = l ⟨b, hb⟩ := by
    rintro a b ha hb rfl
    rfl
  delta wexp
  beta_reduce
  split_ifs
  all_goals first
    | omega
    | exact hl' _ _ _ _ (by omega)
    | exact congrArg Neg.neg (hl' _ _ _ _ (by omega))
    | (rw [neg_neg]; exact hl' _ _ _ _ (by omega))
    | simp

theorem wexp_castLE {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin (n / 2)) :
    wexp n l (Fin.castLE (Nat.div_le_self n 2) i) = l i := by
  delta wexp
  beta_reduce
  rw [dite_eq_left (by rw [Fin.val_castLE]; exact i.2)]
  rfl

theorem wexp_nonneg {n : ℕ} {l : Fin (n / 2) → ℤ} (hl : Cone l) {i j : Fin n} (h : i < j) :
    0 ≤ wexp n l i - wexp n l j := by
  exact sub_nonneg.2 (wexp_anti hl h.le)

theorem relIndex_transfer {G : Type*} [Group G] {X Y H : Subgroup G} (hYX : Y ≤ X)
    (h : ∀ x ∈ X, ∃ y ∈ Y, ∃ z ∈ H, x = y * z) : H.relIndex X = H.relIndex Y := by
  show (H.subgroupOf X).index = (H.subgroupOf Y).index
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  let f : Y ⧸ H.subgroupOf Y → X ⧸ H.subgroupOf X :=
    Quotient.map' (fun y : Y => (⟨y.1, hYX y.2⟩ : X)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact hab)
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have hab' : ((⟨a.1, hYX a.2⟩ : X) : X ⧸ H.subgroupOf X) = ((⟨b.1, hYX b.2⟩ : X) : X ⧸ H.subgroupOf X) := hab
    rw [QuotientGroup.eq] at hab' ⊢
    exact hab'
  have hsurj : Function.Surjective f := by
    intro xb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    obtain ⟨y, hy, z, hz, hxyz⟩ := h x.1 x.2
    refine ⟨((⟨y, hy⟩ : Y) : Y ⧸ H.subgroupOf Y), ?_⟩
    show ((⟨y, hYX hy⟩ : X) : X ⧸ H.subgroupOf X) = (x : X ⧸ H.subgroupOf X)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show y⁻¹ * x.1 ∈ H
    rw [hxyz, inv_mul_cancel_left]
    exact hz
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem v_zpow {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (k : ℤ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hU.2.2.2.1]
  show ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k =
    ((Multiplicative.ofAdd (-k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  rw [← WithZero.coe_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_neg, mul_one]

theorem unif_ne_zero {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) : ϖ ≠ 0 := by
  intro h0
  have hv := hU.2.2.2.1
  rw [h0, map_zero] at hv
  exact WithZero.zero_ne_coe hv

theorem ordL_zpow {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (k : ℤ) : ordL (ϖ ^ k) = k := by
  have h1 := GlobalTheory.BorelUMod.v_eq_exp (zpow_ne_zero k (unif_ne_zero hU))
  rw [v_zpow hU] at h1
  have h2 := WithZero.exp_injective h1
  omega

theorem mul_exp_le_one_iff (y : WithZero (Multiplicative ℤ)) (c : ℤ) :
    y * WithZero.exp c ≤ 1 ↔ y ≤ WithZero.exp (-c) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.1 hy
    rw [show WithZero.exp c = ((Multiplicative.ofAdd c : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
      show WithZero.exp (-c) = ((Multiplicative.ofAdd (-c) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
      ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe, WithZero.coe_le_coe,
      ← Multiplicative.toAdd_le, ← Multiplicative.toAdd_le, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_one]
    omega

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem unip_iff {σ : L →+* L} (g : GU σ n) :
    IsUnipU g ↔ ∀ i j, j ≤ i → ((((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) - 1) i j = 0 := by
  constructor
  · rintro ⟨hB, hD⟩ i j hji
    rcases hji.lt_or_eq with hlt | rfl
    · rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hlt), hB i j hlt, sub_zero]
    · rw [Matrix.sub_apply, Matrix.one_apply_eq, hD _, sub_self]
  · intro h
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · have h1 := h i j hji.le
      rwa [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hji), sub_zero] at h1
    · have h1 := h i i le_rfl
      rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h1

theorem mem_IwU_iff {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) (hg : IsUnipU g) :
    g ∈ PositivityTheory.SphericalProduct.IwU σ n ↔
      (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) - 1 ∈ upLat L (fun _ _ : Fin n => (0 : ℤ)) := by
  have hu := (unip_iff g).1 hg
  have hlow : ∀ i j, j < i → (((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) i j = 0 := fun i j hji => by
    have h1 := hu i j hji.le
    rwa [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hji), sub_zero] at h1
  have hdiag : ∀ i, (((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) i i = 1 := fun i => by
    have h1 := hu i i le_rfl
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h1
  have hinv : ∀ i j, ((((g : GL (Fin n) L))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      σ ((((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) j.rev i.rev) :=
    (GlobalTheory.LGrp.mem_GU_iff σ n (g : GL (Fin n) L)).1 g.2
  show (g : GL (Fin n) L) ∈ PositivityTheory.SphericalProduct.IwGL L n ↔ _
  rw [GlobalTheory.CompanionTheory.DomGLVal.mem_IwGL_iff]
  constructor
  · rintro ⟨⟨hv, -⟩, -⟩
    show _ ∧ _
    refine ⟨hu, fun i j hij => ?_⟩
    simp only [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), sub_zero, neg_zero, WithZero.exp_zero]
    exact hv i j
  · rintro ⟨-, hup⟩
    have hall : ∀ i j, Valued.v ((((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 := by
      intro i j
      rcases lt_trichotomy i j with hij | rfl | hij
      · have h1 := hup i j hij
        simp only [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), sub_zero, neg_zero,
          WithZero.exp_zero] at h1
        exact h1
      · rw [hdiag, map_one]
      · rw [hlow i j hij, map_zero]
        exact zero_le
    refine ⟨?_, ?_⟩
    · show _ ∧ _
      refine ⟨hall, fun i j hji => ?_⟩
      rw [hlow i j hji, map_zero]
      exact zero_lt_one
    · show _ ∧ _
      refine ⟨fun i j => ?_, fun i j hji => ?_⟩
      · rw [hinv, hσ]
        exact hall _ _
      · rw [hinv, hlow j.rev i.rev (Fin.rev_lt_rev.2 hji), map_zero, map_zero]
        exact zero_lt_one

end Val

section Steps

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem step1 [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (t : GU σ n)
    (ht : PositivityTheory.SphericalProduct.IsDiagM (t : GL (Fin n) L))
    (hdom : ∀ i j : Fin n, i ≤ j → ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) ≤
      ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)) :
    ((PositivityTheory.SphericalProduct.IwU σ n).map (MulAut.conj t).toMonoidHom).relIndex (PositivityTheory.SphericalProduct.IwU σ n) =
      ((PositivityTheory.SphericalProduct.IwU σ n).map (MulAut.conj t).toMonoidHom).relIndex
        (PositivityTheory.SphericalProduct.IwU σ n ⊓ (borelU σ n).U) := by
  obtain ⟨D, hJ, hN, hNm, hT⟩ := PositivityTheory.SphericalProduct.iwahori_u L ϖ σ q hU n
  obtain ⟨d, hTd, hTne⟩ : ∃ d : Fin n → L, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal d ∧ ∀ i, d i ≠ 0 := ⟨_, GlobalTheory.CompanionTheory.DomGLVal.diag_data ht⟩
  have hdom' : ∀ i j : Fin n, i ≤ j → ordL (d j) ≤ ordL (d i) := fun i j hij => by
    have h1 := hdom i j hij
    rwa [hTd, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h1
  have hTinv : ((((t : GL (Fin n) L))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => (d i)⁻¹) := GlobalTheory.CompanionTheory.DomGLVal.val_inv_diag hTne hTd
  have hmap : ∀ z : GU σ n, t⁻¹ * z * t ∈ PositivityTheory.SphericalProduct.IwU σ n →
      z ∈ (PositivityTheory.SphericalProduct.IwU σ n).map (MulAut.conj t).toMonoidHom := fun z hz =>
    (Subgroup.mem_map).2 ⟨_, hz, show t * (t⁻¹ * z * t) * t⁻¹ = z by group⟩
  refine relIndex_transfer inf_le_left fun x hx => ?_
  rw [← hJ] at hx
  obtain ⟨c, hc, b, hb, a, ha, rfl⟩ := D.fact_up x hx
  have hc' := Subgroup.mem_inf.1 hc
  have hb' := Subgroup.mem_inf.1 hb
  have ha' := Subgroup.mem_inf.1 ha
  have hcJ : c ∈ PositivityTheory.SphericalProduct.IwU σ n := hJ ▸ hc'.1
  have hbJ : b ∈ PositivityTheory.SphericalProduct.IwU σ n := hJ ▸ hb'.1
  have haJ : a ∈ PositivityTheory.SphericalProduct.IwU σ n := hJ ▸ ha'.1
  have hbT : t⁻¹ * b * t = b := by
    obtain ⟨db, hBd, -⟩ : ∃ db : Fin n → L, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        Matrix.diagonal db ∧ ∀ i, db i ≠ 0 := ⟨_, GlobalTheory.CompanionTheory.DomGLVal.diag_data ((hT b).1 hb'.2)⟩
    apply Subtype.ext
    apply Units.ext
    show ((((t : GL (Fin n) L))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    rw [hTinv, hBd, hTd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_comm (d i)⁻¹ (db i), mul_assoc, inv_mul_cancel₀ (hTne i), mul_one]
  have haI : ((a : GL (Fin n) L)) ∈ PositivityTheory.SphericalProduct.IwGL L n := haJ
  have hInt := (GlobalTheory.CompanionTheory.DomGLVal.mem_IwGL_iff _).1 haI
  have hg : PositivityTheory.SphericalProduct.IsLowUniM (a : GL (Fin n) L) := (hNm a).1 ha'.2
  have hg' : PositivityTheory.SphericalProduct.IsLowUniM ((a : GL (Fin n) L))⁻¹ :=
    (hNm a⁻¹).1 (Subgroup.mem_inf.1 ((D.J ⊓ D.Nm).inv_mem ha)).2
  have hratio : ∀ i j : Fin n, j < i → Valued.v ((d i)⁻¹) * Valued.v (((d j)⁻¹)⁻¹) ≤ 1 := by
    intro i j hji
    have h1 := GlobalTheory.CompanionTheory.DomGLVal.v_le_of_ordL_le (hTne i) (hTne j) (hdom' j i hji.le)
    have h2 := GlobalTheory.CompanionTheory.DomGLVal.ratio_le (hTne i) h1
    rw [inv_inv, mul_comm]
    exact h2
  have hlow := GlobalTheory.CompanionTheory.DomGLVal.low_mem (s := ((t : GL (Fin n) L))⁻¹) (e := fun i => (d i)⁻¹)
    (fun i => inv_ne_zero (hTne i)) hTinv hg hg'
    (fun i j hji => GlobalTheory.CompanionTheory.DomGLVal.valuation_triple_mul_lt_one (hratio i j hji) (hInt.1.2 i j hji))
    (fun i j hji => GlobalTheory.CompanionTheory.DomGLVal.valuation_triple_mul_lt_one (hratio i j hji) (hInt.2.2 i j hji))
  have hta : t⁻¹ * a * t ∈ PositivityTheory.SphericalProduct.IwU σ n := by
    have e : (((t⁻¹ * a * t : GU σ n)) : GL (Fin n) L) =
        ((t : GL (Fin n) L))⁻¹ * (a : GL (Fin n) L) * (((t : GL (Fin n) L))⁻¹)⁻¹ := by
      rw [inv_inv]
      rfl
    show (((t⁻¹ * a * t : GU σ n)) : GL (Fin n) L) ∈ PositivityTheory.SphericalProduct.IwGL L n
    rw [e]
    exact hlow.1
  refine ⟨c, Subgroup.mem_inf.2 ⟨hcJ, (GlobalTheory.LGrp.mem_borelU_U σ n c).2 ((hN c).1 hc'.2)⟩, b * a,
    hmap _ ?_, mul_assoc c b a⟩
  have e2 : t⁻¹ * (b * a) * t = (t⁻¹ * b * t) * (t⁻¹ * a * t) := by group
  rw [e2, hbT]
  exact (PositivityTheory.SphericalProduct.IwU σ n).mul_mem hbJ hta

theorem step3 {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {d : Fin n → Fin n → ℤ} (hd : IsWeight d)
    (hd0 : ∀ i j, i < j → 0 ≤ d i j) :
    (unipLat hU.2.1 hd).relIndex (unipLat hU.2.1 (n := n) isWeight_zero) =
      q ^ ∑ p ∈ upPairs n, (d p.1 p.2).toNat := by
  have hmono : ∀ {c C : Fin n → Fin n → ℤ} (hc : IsWeight c) (hC : IsWeight C),
      (∀ i j, i < j → c i j ≤ C i j) → unipLat hU.2.1 hC ≤ unipLat hU.2.1 hc := by
    intro c C hc hC hcC u hu
    obtain ⟨h1, h2⟩ := hu
    show _ ∧ _
    exact ⟨h1, fun i j hij => (h2 i j hij).trans (WithZero.exp_le_exp.2 (neg_le_neg (hcC i j hij)))⟩
  obtain ⟨C, hC, hdC, h0C⟩ := exists_idealWeight (c := d)
  have e1 := relIndex_unipLat hU hd hC hdC
  have e2 := relIndex_unipLat hU (isWeight_zero (n := n)) hC h0C
  have hle1 : unipLat hU.2.1 hC ≤ unipLat hU.2.1 hd := hmono hd hC hdC.1
  have hle2 : unipLat hU.2.1 hd ≤ unipLat hU.2.1 (n := n) isWeight_zero :=
    hmono isWeight_zero hd (fun i j hij => hd0 i j hij)
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  rw [e1, e2] at hmul
  simp only [sub_zero] at hmul
  have hsplit : ∑ p ∈ upPairs n, (C p.1 p.2).toNat =
      ∑ p ∈ upPairs n, (C p.1 p.2 - d p.1 p.2).toNat + ∑ p ∈ upPairs n, (d p.1 p.2).toNat := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2) := hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.1 hp').2
    have h1 := hdC.1 p.1 p.2 hlt
    have h2 := hd0 p.1 p.2 hlt
    omega
  rw [hsplit, pow_add] at hmul
  have hq : 0 < q ^ ∑ p ∈ upPairs n, (C p.1 p.2 - d p.1 p.2).toNat :=
    pow_pos (by have := hU.2.2.2.2.2.1; omega) _
  exact Nat.eq_of_mul_eq_mul_left hq hmul

end Steps

section Conj

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem isWeight_wexp (l : Fin (n / 2) → ℤ) : IsWeight (fun i j : Fin n => wexp n l i - wexp n l j) := by
  refine ⟨fun i j => ?_, fun i j k _ _ => ?_⟩
  · show wexp n l j.rev - wexp n l i.rev = wexp n l i - wexp n l j
    rw [wexp_rev, wexp_rev]
    ring
  · show wexp n l i - wexp n l k ≤ (wexp n l i - wexp n l j) + (wexp n l j - wexp n l k)
    linarith

theorem conj_entry_alt {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (e : Fin n → ℤ) (t : GU σ n)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ e i)) (u : GU σ n)
    (i j : Fin n) :
    ((((t⁻¹ * u * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j =
      ϖ ^ (-e i) * ((((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) - 1) i j * ϖ ^ e j := by
  have hϖ := unif_ne_zero hU
  have htinv : (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ϖ ^ (-e i)) := by
    rw [Subgroup.coe_inv]
    apply Units.inv_eq_of_mul_eq_one_right
    rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    rw [_root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hϖ)]
  have hmat : ((((t⁻¹ * u * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) =
      Matrix.diagonal (fun i => ϖ ^ (-e i)) * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Matrix.diagonal (fun i => ϖ ^ e i) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, htinv, ht]
  rw [hmat]
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases eq_or_ne i j with rfl | hij
  · have h1 : ϖ ^ (-e i) * ϖ ^ e i = 1 := by
      rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hϖ)]
    rw [Matrix.one_apply_eq]
    linear_combination h1
  · rw [Matrix.one_apply_ne hij]
    ring

theorem conj_val (y : WithZero (Multiplicative ℤ)) (a b : ℤ) :
    WithZero.exp a * y * WithZero.exp (-b) ≤ 1 ↔ y ≤ WithZero.exp (-(a - b)) := by
  have e : WithZero.exp a * y * WithZero.exp (-b) = y * WithZero.exp (a - b) := by
    rw [sub_eq_add_neg, WithZero.exp_add, mul_comm (WithZero.exp a) y, mul_assoc]
  rw [e, mul_exp_le_one_iff]

theorem comap_eq {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {l : Fin (n / 2) → ℤ} (hl : Cone l)
    (t : GU σ n)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ wexp n l i)) :
    ((PositivityTheory.SphericalProduct.IwU σ n).map (MulAut.conj t).toMonoidHom).comap (borelU σ n).U.subtype ⊓
      unipLat hU.2.1 (n := n) isWeight_zero = unipLat hU.2.1 (isWeight_wexp l) := by
  ext u
  have hv : IsUnipU (u : GU σ n) := (GlobalTheory.LGrp.mem_borelU_U σ n _).1 u.2
  have hw_ent : ∀ i j, ((((t⁻¹ * (u : GU σ n) * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j =
      ϖ ^ (-wexp n l i) * (((((u : GU σ n) : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) - 1) i j *
        ϖ ^ wexp n l j := conj_entry_alt hU (wexp n l) t ht (u : GU σ n)
  have hvz := (unip_iff (u : GU σ n)).1 hv
  have hw : IsUnipU (t⁻¹ * (u : GU σ n) * t) := (unip_iff _).2 fun i j hji => by
    rw [hw_ent, hvz i j hji, mul_zero, zero_mul]
  have hc : u ∈ ((PositivityTheory.SphericalProduct.IwU σ n).map (MulAut.conj t).toMonoidHom).comap (borelU σ n).U.subtype ↔
      t⁻¹ * (u : GU σ n) * t ∈ PositivityTheory.SphericalProduct.IwU σ n := by
    show (u : GU σ n) ∈ (PositivityTheory.SphericalProduct.IwU σ n).map (MulAut.conj t).toMonoidHom ↔ _
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxv⟩
      have e : t⁻¹ * (u : GU σ n) * t = x := by
        rw [← hxv]
        show t⁻¹ * (t * x * t⁻¹) * t = x
        group
      rw [e]
      exact hx
    · intro h
      refine ⟨_, h, ?_⟩
      show t * (t⁻¹ * (u : GU σ n) * t) * t⁻¹ = (u : GU σ n)
      group
  have hv0 : ∀ i, Valued.v (ϖ ^ (-wexp n l i)) = WithZero.exp (wexp n l i) := fun i => by
    rw [v_zpow hU, neg_neg]
  have hkey : ∀ i j, (Valued.v (ϖ ^ (-wexp n l i) * (((((u : GU σ n) : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) - 1) i j *
      ϖ ^ wexp n l j) ≤ 1 ↔ Valued.v ((((((u : GU σ n) : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) - 1) i j) ≤
        WithZero.exp (-(wexp n l i - wexp n l j))) := fun i j => by
    rw [map_mul, map_mul, hv0, v_zpow hU]
    exact conj_val _ _ _
  rw [Subgroup.mem_inf, hc, mem_IwU_iff hU.2.1 _ hw]
  constructor
  · rintro ⟨⟨-, h1⟩, ⟨h2, -⟩⟩
    show _ ∧ _
    refine ⟨h2, fun i j hij => ?_⟩
    have h3 := h1 i j hij
    simp only [neg_zero, WithZero.exp_zero] at h3
    rw [hw_ent] at h3
    exact (hkey i j).1 h3
  · rintro ⟨h2, h1⟩
    refine ⟨?_, ?_⟩
    · show _ ∧ _
      refine ⟨(unip_iff _).1 hw, fun i j hij => ?_⟩
      simp only [neg_zero, WithZero.exp_zero]
      rw [hw_ent]
      exact (hkey i j).2 (h1 i j hij)
    · show _ ∧ _
      refine ⟨h2, fun i j hij => (h1 i j hij).trans ?_⟩
      simp only [neg_zero]
      exact WithZero.exp_le_exp.2 (by linarith [wexp_nonneg hl hij])

theorem step2 {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {l : Fin (n / 2) → ℤ} (hl : Cone l)
    (t : GU σ n)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ wexp n l i)) :
    ((PositivityTheory.SphericalProduct.IwU σ n).map (MulAut.conj t).toMonoidHom).relIndex (PositivityTheory.SphericalProduct.IwU σ n ⊓ (borelU σ n).U) =
      (unipLat hU.2.1 (isWeight_wexp l)).relIndex (unipLat hU.2.1 (n := n) isWeight_zero) := by
  have hIw : (PositivityTheory.SphericalProduct.IwU σ n ⊓ (borelU σ n).U).subgroupOf (borelU σ n).U =
      unipLat hU.2.1 (n := n) isWeight_zero := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hv : IsUnipU (u : GU σ n) := (GlobalTheory.LGrp.mem_borelU_U σ n _).1 u.2
    rw [mem_IwU_iff hU.2.1 _ hv]
    exact ⟨fun h => h.1, fun h => ⟨h, u.2⟩⟩
  rw [← Subgroup.relIndex_subgroupOf
      (inf_le_right : PositivityTheory.SphericalProduct.IwU σ n ⊓ (borelU σ n).U ≤ (borelU σ n).U), hIw,
    ← Subgroup.inf_relIndex_right, ← Subgroup.comap_subtype, comap_eq hU hl t ht]

theorem sum_wexp {l : Fin (n / 2) → ℤ} (hl : Cone l) :
    ((∑ p ∈ upPairs n, (wexp n l p.1 - wexp n l p.2).toNat : ℕ) : ℤ) =
      2 * ∑ i : Fin (n / 2), (((n : ℤ) - 1 - 2 * (i : ℕ)) * l i) := by
  rw [Nat.cast_sum]
  have h1 : ∀ p ∈ upPairs n, (((wexp n l p.1 - wexp n l p.2).toNat : ℕ) : ℤ) =
      wexp n l p.1 - wexp n l p.2 := by
    intro p hp
    have hp' : p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2) := hp
    exact Int.toNat_of_nonneg (wexp_nonneg hl (Finset.mem_filter.1 hp').2)
  rw [Finset.sum_congr rfl h1, sum_upPairs, sum_half _ (wexp_rev l)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [wexp_castLE]
  ring

end Conj

end PositivityTheory.Rg.BcB.F.Eig.IndexUAAux

namespace PositivityTheory.Rg.BcB.F.Eig

open IndexUAAux in
theorem indexU : IndexU := by
  intro L _ _ _ ϖ σ q n hU l hl t ht
  have hdiag : PositivityTheory.SphericalProduct.IsDiagM (t : GL (Fin n) L) := fun i j hij => by
    show ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0
    rw [ht, Matrix.diagonal_apply_ne _ hij]
  have hdom : ∀ i j : Fin n, i ≤ j → ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) ≤
      ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) := by
    intro i j hij
    rw [ht, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ordL_zpow hU, ordL_zpow hU]
    exact wexp_anti hl hij
  rw [step1 hU t hdiag hdom, step2 hU hl t ht,
    step3 hU (isWeight_wexp l) (fun i j hij => wexp_nonneg hl hij), Nat.cast_pow, ← sum_wexp hl,
    Int.toNat_natCast]

end PositivityTheory.Rg.BcB.F.Eig
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertEigenvalues.HeckeSumP
noncomputable section

open GlobalTheory.PRep GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Eig

namespace HeckeFixedSubspaceSpan

section Gen

variable {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]

def fixSub (ρ : Representation ℂ H V) (P : Set V) : Subgroup H where
  carrier := {g | ∀ v ∈ P, ρ g v = v}
  one_mem' := by intro v _; simp
  mul_mem' := by
    intro a b ha hb v hv
    rw [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
  inv_mem' := by
    intro a ha v hv
    have h := ha v hv
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [h]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_fixSub (ρ : Representation ℂ H V) (P : Set V) (g : H) :
    g ∈ fixSub ρ P ↔ ∀ v ∈ P, ρ g v = v := Iff.rfl

theorem fixSub_open [TopologicalSpace H] (ρ : Representation ℂ H V)
    (hρ : ∀ v : V, IsOpen {g : H | ρ g v = v}) (P : Set V) (hP : P.Finite) :
    IsOpen (fixSub ρ P : Set H) := by
  have e : (fixSub ρ P : Set H) = ⋂ v ∈ P, {g : H | ρ g v = v} := by
    ext g
    simp only [SetLike.mem_coe, mem_fixSub, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  exact hP.isOpen_biInter (fun v _ => hρ v)

theorem avg_left (ρ : Representation ℂ H V) (S : Subgroup H) [Fintype (H ⧸ S)] (z : V)
    (hz : ∀ h ∈ S, ρ h z = z) (j : H) :
    ρ j (∑ r : H ⧸ S, ρ r.out z) = ∑ r : H ⧸ S, ρ r.out z := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm j) _ _ (fun r => ?_)
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (j * r.out)
  have e : (MulAction.toPerm j r : H ⧸ S) = (QuotientGroup.mk (j * r.out) : H ⧸ S) := by
    rw [MulAction.toPerm_apply]
    exact (congrArg (j • ·) (QuotientGroup.out_eq' r)).symm.trans (MulAction.Quotient.smul_mk S j r.out)
  rw [e, hs, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz s s.2]

theorem avg_right (ρ : Representation ℂ H V) (S : Subgroup H) [S.Normal] [Fintype (H ⧸ S)] (x : V)
    (hx : ∀ h ∈ S, ρ h x = x) (j : H) :
    ∑ r : H ⧸ S, ρ r.out (ρ j x) = ∑ r : H ⧸ S, ρ r.out x := by
  refine Fintype.sum_equiv (Equiv.mulRight (j : H ⧸ S)) _ _ (fun r => ?_)
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (r.out * j)
  have e : (r * (j : H ⧸ S)) = (QuotientGroup.mk (r.out * j) : H ⧸ S) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  show _ = ρ ((r * (j : H ⧸ S)).out) x
  rw [e, hs, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx s s.2]

theorem avg_fixed (ρ : Representation ℂ H V) (S : Subgroup H) [Fintype (H ⧸ S)] (w : V)
    (hw : ∀ h, ρ h w = w) : ∑ r : H ⧸ S, ρ r.out w = Fintype.card (H ⧸ S) • w := by
  simp [hw]

theorem sep_span [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (ρ : Representation ℂ H V) (hρ : ∀ v : V, IsOpen {g : H | ρ g v = v}) (w : V) (hw : ∀ h, ρ h w = w)
    (hwM : w ∈ Submodule.span ℂ {u | ∃ (j : H) (v : V), u = ρ j v - v}) : w = 0 := by
  obtain ⟨n, f, g, hg⟩ := (Submodule.mem_span_set').1 hwM
  have hg' : ∀ i, ∃ (a : H) (b : V), (g i : V) = ρ a b - b := fun i => (g i).2
  choose j v hjv using hg'
  have hO := fixSub_open ρ hρ (Set.range v) (Set.finite_range v)
  haveI : Finite (H ⧸ fixSub ρ (Set.range v)) := Subgroup.quotient_finite_of_isOpen _ hO
  haveI : (fixSub ρ (Set.range v)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  letI : Fintype (H ⧸ (fixSub ρ (Set.range v)).normalCore) := Fintype.ofFinite _
  have hfix : ∀ i, ∀ h ∈ (fixSub ρ (Set.range v)).normalCore, ρ h (v i) = v i := fun i h hh =>
    (mem_fixSub ρ _ h).1 (Subgroup.normalCore_le _ hh) (v i) ⟨i, rfl⟩
  have h0 : ∑ r : H ⧸ (fixSub ρ (Set.range v)).normalCore, ρ r.out w = 0 := by
    rw [← hg]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [← Finset.smul_sum, hjv i]
    simp only [map_sub, Finset.sum_sub_distrib]
    rw [avg_right ρ _ (v i) (hfix i) (j i), sub_self, smul_zero]
  rw [avg_fixed ρ _ w hw, ← Nat.cast_smul_eq_nsmul ℂ] at h0
  rcases smul_eq_zero.mp h0 with h | h
  · exact absurd (Nat.cast_eq_zero.mp h) Fintype.card_ne_zero
  · exact h

theorem sep [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (ρ : Representation ℂ H V) (hρ : ∀ v : V, IsOpen {g : H | ρ g v = v}) (w : V) (hw : ∀ h, ρ h w = w)
    (hφ : ∀ φ : Module.Dual ℂ V, (∀ h, φ ∘ₗ ρ h = φ) → φ w = 0) : w = 0 := by
  by_cases hwM : w ∈ Submodule.span ℂ {u | ∃ (j : H) (v : V), u = ρ j v - v}
  · exact sep_span ρ hρ w hw hwM
  · obtain ⟨φ, hφw, hφM⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hwM inferInstance
    exfalso
    apply hφw
    apply hφ
    intro h
    ext v
    have hm : ρ h v - v ∈ Submodule.span ℂ {u | ∃ (j : H) (v : V), u = ρ j v - v} :=
      Submodule.subset_span ⟨h, v, rfl⟩
    have h1 : φ (ρ h v - v) = 0 := by
      have h2 := Submodule.mem_map_of_mem (f := φ) hm
      rw [hφM] at h2
      exact (Submodule.mem_bot ℂ).mp h2
    rw [map_sub, sub_eq_zero] at h1
    simpa using h1

end Gen

section Main

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem fix_apply {ρ : Representation ℂ G V} {J : Subgroup G} (y : fixed ρ J) {k : G} (hk : k ∈ J) :
    ρ k (y : V) = y := by
  have h : ∀ h : J, ρ h (y : V) = ((1 : J →* ℂˣ) h : ℂ) • (y : V) := y.2
  simpa using h ⟨k, hk⟩

def Dsub (J : Subgroup G) (t : G) : Subgroup J := (J.map (MulAut.conj t).toMonoidHom).subgroupOf J

theorem mem_Dsub (J : Subgroup G) (t : G) (d : J) : d ∈ Dsub J t ↔ t⁻¹ * (d : G) * t ∈ J := by
  rw [Dsub, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxd⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxd
    rw [← hxd]
    simpa [mul_assoc] using hx
  · intro h
    refine ⟨t⁻¹ * d * t, h, ?_⟩
    simp [mul_assoc]

def iota (J : Subgroup G) (t : G) (r : J ⧸ Dsub J t) : G ⧸ J := (((r.out : G) * t : G) : G ⧸ J)

theorem out_iota (J : Subgroup G) (t : G) (r : J ⧸ Dsub J t) :
    ∃ k ∈ J, (iota J t r).out = (r.out : G) * t * k := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul J ((r.out : G) * t)
  exact ⟨k, k.2, hk⟩

theorem iota_inj (J : Subgroup G) (t : G) : Function.Injective (iota J t) := by
  intro r1 r2 h
  unfold iota at h
  rw [QuotientGroup.eq] at h
  rw [← QuotientGroup.out_eq' r1, ← QuotientGroup.out_eq' r2, QuotientGroup.eq, mem_Dsub]
  simpa [mul_assoc] using h

theorem mem_range_iota (J : Subgroup G) (t : G) (q : G ⧸ J)
    (h : ∃ x ∈ J, ∃ z ∈ J, q.out = x * t * z) : ∃ r, iota J t r = q := by
  obtain ⟨x, hx, z, hz, hq⟩ := h
  refine ⟨(QuotientGroup.mk ⟨x, hx⟩ : J ⧸ Dsub J t), ?_⟩
  obtain ⟨d, hd⟩ := QuotientGroup.mk_out_eq_mul (Dsub J t) (⟨x, hx⟩ : J)
  have hd' := (mem_Dsub J t d).1 d.2
  rw [← QuotientGroup.out_eq' q]
  unfold iota
  rw [hd, QuotientGroup.eq, hq]
  have e : ((((⟨x, hx⟩ : J) * (d : J) : J) : G) * t)⁻¹ * (x * t * z) = (t⁻¹ * ((d : J) : G) * t)⁻¹ * z := by
    simp only [Subgroup.coe_mul]
    group
  rw [e]
  exact J.mul_mem (J.inv_mem hd') hz

theorem levOp_eq (ρ : Representation ℂ G V) (K J : Subgroup G) (t : G) [Fintype (J ⧸ Dsub J t)]
    (y : fixed ρ J) :
    levOp ρ K J (fun g => if ∃ x ∈ J, ∃ z ∈ J, g = x * t * z then 1 else 0) LinearMap.id (y : V) =
      (((J.relIndex K : ℕ) : ℂ)⁻¹) • ∑ r : J ⧸ Dsub J t, ρ (r.out : G) (ρ t y) := by
  unfold levOp
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image (iota J t)) _ ?hs]
  · rw [Finset.sum_image (fun a _ b _ hab => iota_inj J t hab), LinearMap.smul_apply, LinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    obtain ⟨k, hk, hout⟩ := out_iota J t r
    have hmem : ∃ x ∈ J, ∃ z ∈ J, (iota J t r).out = x * t * z := ⟨r.out, (r.out).2, k, hk, hout⟩
    beta_reduce
    rw [if_pos hmem, one_smul, LinearMap.comp_id, hout, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, fix_apply y hk]
  · intro q hq
    rw [Function.mem_support] at hq
    by_cases h : ∃ x ∈ J, ∃ z ∈ J, q.out = x * t * z
    · obtain ⟨r, hr⟩ := mem_range_iota J t q h
      rw [Finset.coe_image]
      exact ⟨r, by simp, hr⟩
    · exact absurd (by simp [h]) hq

theorem key [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (J : Subgroup G) [CompactSpace J] (t : G) (U : Module.End ℂ (fixed ρ J))
    (hU : PositivityTheory.Lbc.IsHeckeOpG ρ J t U) (y : fixed ρ J) [Fintype (J ⧸ Dsub J t)] :
    ∑ r : J ⧸ Dsub J t, ρ (r.out : G) (ρ t y) = Fintype.card (J ⧸ Dsub J t) • (U y : V) := by
  let ρJ : Representation ℂ J V := ρ.comp J.subtype
  have hsm : ∀ v : V, IsOpen {g : J | ρJ g v = v} := fun v => (hρ v).preimage continuous_subtype_val
  have hinv : ρ t⁻¹ (ρ t (y : V)) = y := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hz : ∀ h ∈ Dsub J t, ρJ h (ρ t y) = ρ t y := by
    intro h hh
    have h1 := (mem_Dsub J t h).1 hh
    show ρ (h : G) (ρ t y) = ρ t y
    have e : (h : G) = t * (t⁻¹ * h * t) * t⁻¹ := by group
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hinv, fix_apply y h1]
  show ∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) = _
  have hw : ∀ g : J, ρJ g (∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) - Fintype.card (J ⧸ Dsub J t) • (U y : V)) =
      ∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) - Fintype.card (J ⧸ Dsub J t) • (U y : V) := by
    intro g
    rw [map_sub, map_nsmul, avg_left ρJ (Dsub J t) (ρ t y) hz g]
    congr 2
    exact fix_apply (U y) g.2
  have hφ : ∀ φ : Module.Dual ℂ V, (∀ h, φ ∘ₗ ρJ h = φ) →
      φ (∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) - Fintype.card (J ⧸ Dsub J t) • (U y : V)) = 0 := by
    intro φ hφ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_nsmul, map_sum]
    have e1 : ∀ r : J ⧸ Dsub J t, φ (ρJ r.out (ρ t y)) = φ (ρ t y) := fun r => by
      rw [← LinearMap.comp_apply, hφ]
    simp only [e1, Finset.sum_const, Finset.card_univ]
    rw [hU y φ (fun x hx => hφ ⟨x, hx⟩), sub_self]
  exact sub_eq_zero.mp (sep ρJ hsm _ hw hφ)

end Main

end HeckeFixedSubspaceSpan

open HeckeFixedSubspaceSpan in
theorem heckeSum : HeckeSum := by
  intro G _ _ _ V _ _ ρ hρ K J hJ hK hJK t U hU y
  haveI : CompactSpace J :=
    isCompact_iff_compactSpace.mp (hK.of_isClosed_subset (J.isClosed_of_isOpen hJ) (fun x hx => hJK hx))
  have hDo : IsOpen ((Dsub J t : Subgroup J) : Set J) := by
    have e : ((Dsub J t : Subgroup J) : Set J) = (fun d : J => t⁻¹ * (d : G) * t) ⁻¹' (J : Set G) := by
      ext d
      simp only [SetLike.mem_coe, mem_Dsub, Set.mem_preimage]
    rw [e]
    exact hJ.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  haveI : Finite (J ⧸ Dsub J t) := Subgroup.quotient_finite_of_isOpen _ hDo
  letI : Fintype (J ⧸ Dsub J t) := Fintype.ofFinite _
  rw [levOp_eq ρ K J t y, key ρ hρ J t U hU y, mul_smul, ← Nat.cast_smul_eq_nsmul ℂ, Fintype.card_eq_nat_card]
  rfl

end PositivityTheory.Rg.BcB.F.Eig

end
end

namespace PositivityTheory.Rg.BcB.F.Eig

theorem eigInert : EigInert := eigInertOf absEig heckeSum indexU

end PositivityTheory.Rg.BcB.F.Eig
