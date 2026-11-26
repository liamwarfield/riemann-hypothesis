module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CardIcutFilter
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DplusLeBeS
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.PsiCutSupported
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.KillOfEmpty
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem kill_rename {R σ τ : Type} [CommRing R] (f : σ → τ) (S : Set τ) (P : MvPolynomial σ R) :
    kill S (rename f P) = rename f (kill (f ⁻¹' S) P) := by
  have h : (kill S).comp (rename f) = (rename f).comp (kill (f ⁻¹' S) : MvPolynomial σ R →ₐ[R] _) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rename_X, kill, aeval_X]
    by_cases h1 : f i ∈ S
    · have h2 : i ∈ f ⁻¹' S := h1
      rw [if_pos h1, if_pos h2, map_zero]
    · have h2 : i ∉ f ⁻¹' S := h1
      rw [if_neg h1, if_neg h2, rename_X]
  exact AlgHom.congr_fun h P

theorem kill_of_empty {R σ : Type} [CommRing R] (S : Set σ) (hS : S = ∅) (P : MvPolynomial σ R) : kill S P = P := by
  subst hS
  have h : (kill (∅ : Set σ) : MvPolynomial σ R →ₐ[R] _) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [kill]
  rw [h]
  rfl

theorem li_mono_words {R σ ι α : Type} [CommRing R] [IsDomain R] (Tset : Set σ) (w : α → MvPolynomial σ R)
    (hw : LinearIndependent R w) (M : ι → σ →₀ ℕ) (x : ι → α) (hM : ∀ q, ∀ v, M q v ≠ 0 → v ∈ Tset)
    (hsup : ∀ q, w (x q) ∈ supported R Tsetᶜ) (hinj : ∀ q q', M q = M q' → x q = x q' → q = q') :
    LinearIndependent R fun q => monomial (M q) (1 : R) * w (x q) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum q₀ hq₀
  obtain ⟨Φ, hΦmono⟩ : ∃ Φ : MvPolynomial σ R →ₗ[R] MvPolynomial σ R, ∀ (n : σ →₀ ℕ) (a : R),
      Φ (monomial n a) = if n.filter (· ∈ Tset) = M q₀ then monomial (n.filter (· ∉ Tset)) a else 0 := by
    refine ⟨(MvPolynomial.basisMonomials σ R).constr R (fun n : σ →₀ ℕ =>
      if n.filter (· ∈ Tset) = M q₀ then monomial (n.filter (· ∉ Tset)) (1 : R) else 0), fun n a => ?_⟩
    have e : monomial n a = a • (MvPolynomial.basisMonomials σ R) n := by
      simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Module.Basis.constr_basis]
    split_ifs
    · rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    · rw [smul_zero]
  have hkey : ∀ q, Φ (monomial (M q) (1 : R) * w (x q)) = if M q = M q₀ then w (x q) else 0 := by
    intro q
    have hwsup := hsup q
    rw [mem_supported] at hwsup
    have hT : ∀ n ∈ (w (x q)).support, (M q + n).filter (· ∈ Tset) = M q ∧
        (M q + n).filter (· ∉ Tset) = n := by
      intro n hn
      have hnv : ∀ v, n v ≠ 0 → v ∉ Tset := fun v hv =>
        hwsup ((mem_vars_iff_mem_support v).2 ⟨n, hn, Finsupp.mem_support_iff.2 hv⟩)
      constructor
      · ext v
        rw [Finsupp.filter_apply, Finsupp.add_apply]
        by_cases hv : v ∈ Tset
        · rw [if_pos hv]
          have : n v = 0 := by
            by_contra h
            exact hnv v h hv
          rw [this, add_zero]
        · rw [if_neg hv]
          by_contra h
          exact hv (hM q v (Ne.symm h))
      · ext v
        rw [Finsupp.filter_apply, Finsupp.add_apply]
        by_cases hv : v ∈ Tset
        · rw [if_neg (not_not.2 hv)]
          by_contra h
          exact hnv v (Ne.symm h) hv
        · rw [if_pos hv]
          have : M q v = 0 := by
            by_contra h
            exact hv (hM q v h)
          rw [this, zero_add]
    conv_lhs => rw [(w (x q)).as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    simp only [monomial_mul, one_mul, hΦmono]
    split_ifs with hMq
    · conv_rhs => rw [(w (x q)).as_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [(hT n hn).1, (hT n hn).2, if_pos hMq]
    · refine Finset.sum_eq_zero fun n hn => ?_
      rw [(hT n hn).1, if_neg hMq]
  have hxinj : Function.Injective (fun q : {q // M q = M q₀} => x q.1) := by
    intro a b h
    exact Subtype.ext (hinj a.1 b.1 (a.2.trans b.2.symm) h)
  have hfib : LinearIndependent R (w ∘ fun q : {q // M q = M q₀} => x q.1) := hw.comp _ hxinj
  have h2 : ∑ q ∈ s, g q • (if M q = M q₀ then w (x q) else 0) = 0 := by
    have h := congrArg Φ hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h
    calc ∑ q ∈ s, g q • (if M q = M q₀ then w (x q) else 0)
        = ∑ q ∈ s, Φ (g q • (monomial (M q) (1 : R) * w (x q))) :=
          Finset.sum_congr rfl fun q _ => by rw [map_smul, hkey]
      _ = 0 := h
  have h3 : ∑ q ∈ s.subtype (fun q => M q = M q₀), g q.1 • (w ∘ fun q : {q // M q = M q₀} => x q.1) q = 0 := by
    simp only [Function.comp_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun q => g q • w (x q)), Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h2
    split_ifs <;> simp
  exact linearIndependent_iff'.1 hfib (s.subtype (fun q => M q = M q₀)) (fun q => g q.1) h3 ⟨q₀, rfl⟩
    (Finset.mem_subtype.2 hq₀)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Dict

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ}

theorem kfr_lt (hV : F.Valid L₁ N₁) (j : ℤ) {a b : ℕ} (hab : a < b) (hb : b < r) : F.fr j a < F.fr j b := by
  induction b with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · exact (ih h (by omega)).trans (hV.2.2.1 j k hb)
    · subst h
      exact hV.2.2.1 j a hb

theorem kfr_le (hV : F.Valid L₁ N₁) (j : ℤ) {a b : ℕ} (hab : a ≤ b) (hb : b < r) : F.fr j a ≤ F.fr j b := by
  rcases hab.lt_or_eq with h | h
  · exact (kfr_lt F hV j h hb).le
  · subst h
    exact le_rfl

theorem k_mem_letters (j x : ℤ) :
    x ∈ F.letters j ↔ (F.fr (j - 1) 0 ≤ x ∧ x ≤ F.fr j (r - 1)) ∧ posOf n' x ∈ F.TT := by
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]

theorem k_fr_mem_letters (hV : F.Valid L₁ N₁) (j : ℤ) {t : ℕ} (ht : t < r) : F.fr j t ∈ F.letters j := by
  rw [k_mem_letters]
  have h4 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h4
  have h5 := (hV.2.2.2.2.1 j t ht).1
  have a1 := kfr_le F hV (j - 1) (Nat.zero_le (r - 1)) (by omega)
  have a2 := kfr_le F hV j (Nat.zero_le t) ht
  have a3 := kfr_le F hV j (by omega : t ≤ r - 1) (by omega)
  exact ⟨⟨by omega, a3⟩, h5⟩

private theorem card_filter_lt_orderIsoOfFin_eq (s : Finset ℤ) {n : ℕ} (h : s.card = n) (i : Fin n) :
    (s.filter (fun y => y < ((s.orderIsoOfFin h i : s) : ℤ))).card = i.val := by
  set e := s.orderIsoOfFin h with he_def
  have hs : s.filter (fun y => y < ((e i : s) : ℤ)) =
      (Finset.Iio i).image (fun k => ((e k : s) : ℤ)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hy, hlt⟩
      obtain ⟨k, hk⟩ := e.surjective ⟨y, hy⟩
      refine ⟨k, ?_, by rw [hk]⟩
      have hkl : ((e k : s) : ℤ) < ((e i : s) : ℤ) := by
        rw [hk]
        exact hlt
      exact e.lt_iff_lt.mp (Subtype.coe_lt_coe.mp hkl)
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(e k).2, Subtype.coe_lt_coe.mpr (e.lt_iff_lt.mpr hk)⟩
  rw [hs, Finset.card_image_of_injective _ (fun a b hab => e.injective (Subtype.ext hab)), Fin.card_Iio]

private theorem filter_fr_le_letters_eq_image_Ico (hV : F.Valid L₁ N₁) (j : ℤ) {t : ℕ} (ht : t < r) :
    (F.letters j).filter (fun y => F.fr j t ≤ y) = (Finset.Ico t r).image (F.fr j) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨hx, htx⟩
    rw [k_mem_letters] at hx
    obtain ⟨⟨_, hxr⟩, hxT⟩ := hx
    have key : ∀ d u, r - 1 - u = d → u < r → F.fr j u ≤ x → ∃ a, (u ≤ a ∧ a < r) ∧ F.fr j a = x := by
      intro d
      induction d with
      | zero =>
        intro u hu hur hux
        have hu' : u = r - 1 := by omega
        subst hu'
        exact ⟨r - 1, ⟨le_rfl, hur⟩, le_antisymm hux hxr⟩
      | succ d ih =>
        intro u hu hur hux
        rcases hux.lt_or_eq with hlt | heq
        · have hu1 : u + 1 < r := by
            by_contra hc
            have hu2 : u = r - 1 := by omega
            subst hu2
            exact absurd hxr (not_le.mpr hlt)
          by_cases hnext : F.fr j (u + 1) ≤ x
          · obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := ih (u + 1) (by omega) hu1 hnext
            exact ⟨a, ⟨by omega, ha2⟩, ha3⟩
          · exact absurd hxT (hV.2.2.2.2.2.1 j u x hu1 hlt (not_le.mp hnext))
        · exact ⟨u, ⟨le_rfl, hur⟩, heq⟩
    exact key _ t rfl ht htx
  · rintro ⟨a, ⟨hta, har⟩, rfl⟩
    exact ⟨k_fr_mem_letters F hV j har, kfr_le F hV j hta har⟩

private theorem card_filter_lt_fr_add_sub_eq_segN (hV : F.Valid L₁ N₁) (j : ℤ) {t : ℕ} (ht : t < r) :
    ((F.letters j).filter (fun y => y < F.fr j t)).card + (r - t) = segN F j := by
  have h1 := Finset.card_filter_add_card_filter_not (s := F.letters j) (fun y => y < F.fr j t)
  have h2 : (F.letters j).filter (fun y => ¬ y < F.fr j t) =
      (F.letters j).filter (fun y => F.fr j t ≤ y) := by
    apply Finset.filter_congr
    intro y _
    exact not_lt
  rw [h2, filter_fr_le_letters_eq_image_Ico F hV j ht, Finset.card_image_of_injOn, Nat.card_Ico] at h1
  · exact h1
  · intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact (kfr_lt F hV j h hb.2).ne hab
    · exact (kfr_lt F hV j h ha.2).ne' hab

private theorem segE_eq_fr_iff' (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) {t : ℕ} (ht : t < r) :
    segE F j i = F.fr j t ↔ i.val = segN F j - r + t := by
  have hcnt := card_filter_lt_fr_add_sub_eq_segN F hV j ht
  have h0 := card_filter_lt_fr_add_sub_eq_segN F hV j (t := 0) (by omega)
  have hA := card_filter_lt_orderIsoOfFin_eq (F.letters j) (rfl : (F.letters j).card = segN F j) i
  constructor
  · intro h
    have hE : segE F j i = (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) i :
        F.letters j) : ℤ) := rfl
    rw [← hE, h] at hA
    omega
  · intro h
    obtain ⟨k, hk⟩ := ((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j)).surjective
      ⟨F.fr j t, k_fr_mem_letters F hV j ht⟩
    have hB := card_filter_lt_orderIsoOfFin_eq (F.letters j) (rfl : (F.letters j).card = segN F j) k
    rw [hk] at hB
    dsimp only at hB
    have hki : k = i := Fin.ext (by omega)
    have hk2 : segE F j k = F.fr j t := by
      show (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) k : F.letters j) : ℤ) = _
      rw [hk]
    rw [← hki]
    exact hk2

theorem k_r_le_segN (hV : F.Valid L₁ N₁) (hr : 0 < r) (j : ℤ) : r ≤ segN F j := by
  have h0 := card_filter_lt_fr_add_sub_eq_segN F hV j (t := 0) hr
  omega

theorem segE_eq_fr_iff (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) {t : ℕ} (ht : t < r) :
    segE F j i = F.fr j t ↔ i.val = segN F j - r + t := segE_eq_fr_iff' F hV j i ht

theorem segE_lt_fr_iff (hV : F.Valid L₁ N₁) (hr : 0 < r) (j : ℤ) (i : Fin (segN F j)) :
    segE F j i < F.fr j 0 ↔ i.val < segN F j - r := by
  obtain ⟨k, hk⟩ := ((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j)).surjective
    ⟨F.fr j 0, k_fr_mem_letters F hV j hr⟩
  have hseg : segE F j k = F.fr j 0 := by
    show (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) k : F.letters j) : ℤ) = _
    rw [hk]
  have hkv := (segE_eq_fr_iff' F hV j k hr).mp hseg
  rw [← hseg]
  refine (Subtype.coe_lt_coe.trans ((OrderIso.lt_iff_lt
    ((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j))).trans
      Fin.lt_iff_val_lt_val)).trans ?_
  constructor <;> intro h <;> omega

end Dict

section Supp

variable {R : Type} [CommRing R] {N r : ℕ}

theorem Kcol_supported (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, ∀ J, Kcol R ν c j J ∈ supported R {v : Fin N × Fin r | v.1.val < j} := by
  intro j
  induction j with
  | zero =>
    intro _ J
    rw [Kcol.eq_1]
    unfold extOne
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ j ih =>
    intro hj J
    have hS : ∀ J', Kcol R ν c j J' ∈ supported R {v : Fin N × Fin r | v.1.val < j + 1} := by
      intro J'
      refine supported_mono (fun v hv => ?_) (ih (by omega) J')
      simp only [Set.mem_setOf_eq] at hv ⊢
      omega
    have hx : ∀ m, letVec R ⟨j, by omega⟩ m ∈ supported R {v : Fin N × Fin r | v.1.val < j + 1} := by
      intro m
      show X ((⟨j, by omega⟩ : Fin N), m) ∈ Algebra.adjoin R (X '' _)
      exact Algebra.subset_adjoin ⟨((⟨j, by omega⟩ : Fin N), m), by simp, rfl⟩
    rw [Kcol_succ ν c j (by omega)]
    unfold colStep wedgeR contrR
    split_ifs <;> first
      | exact hS J
      | exact sum_mem (fun m _ => mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (hx m)) (hS _))

theorem Psi_cut_supported (n0 : ℕ) (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) (I : ℤ → Finset (Fin r)) :
    Psi R (cutPath n0 ν) I ∈ supported R {v : Fin N × Fin r | v.1.val < n0} := by
  unfold Psi
  refine prod_mem (fun c _ => ?_)
  rw [Kcol_cut n0 ν c N le_rfl, min_eq_right hn]
  exact Kcol_supported ν c n0 hn (I c)

end Supp

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Gen6

variable {N r : ℕ}

theorem stg_castSucc (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.castSucc = stg ν l.val := by
  unfold stg
  rw [dite_eq_left (by have := l.isLt; omega)]
  rfl

theorem stg_succ (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.succ = stg ν (l.val + 1) := by
  unfold stg
  rw [dite_eq_left (by have := l.isLt; omega)]
  rfl

theorem stg_plPart {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) (i : ℕ) (m : Fin r) :
    stg (plPart μ) i m = stg μ i (Fin.castAdd K m) := by
  unfold stg
  split_ifs <;> rfl

theorem colH_step {ν ν' : Fin r → ℤ} (hν : Antitone ν) (hν' : Antitone ν') (ha : ∀ a, ν a ≤ ν' a)
    (hb : ∀ (a : Fin r) (h : a.val + 1 < r), ν' ⟨a.val + 1, h⟩ ≤ ν a) (c : ℤ) :
    colH ν c ≤ colH ν' c ∧ colH ν' c ≤ colH ν c + 1 := by
  constructor
  · unfold colH
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact le_trans hm (ha m)
  · unfold colH
    set S := Finset.univ.filter fun m => c ≤ ν m with hS
    set S' := Finset.univ.filter fun m => c ≤ ν' m with hS'
    have hsub : S'.image Fin.val ⊆ insert 0 (S.image fun a => a.val + 1) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S', S, Finset.mem_insert] at hx ⊢
      obtain ⟨m, hm, rfl⟩ := hx
      rcases Nat.eq_zero_or_pos m.val with h0 | hpos
      · left
        exact h0
      · right
        have hlt : m.val - 1 < r := by omega
        have h1 : (m.val - 1) + 1 < r := by omega
        have hm' : (⟨(m.val - 1) + 1, h1⟩ : Fin r) = m := Fin.ext (by simp; omega)
        refine ⟨⟨m.val - 1, hlt⟩, ?_, by simp; omega⟩
        have h2 := hb ⟨m.val - 1, hlt⟩ h1
        rw [hm'] at h2
        exact le_trans hm h2
    calc S'.card = (S'.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (insert 0 (S.image fun a => a.val + 1)).card := Finset.card_le_card hsub
      _ ≤ (S.image fun a => a.val + 1).card + 1 := Finset.card_insert_le _ _
      _ ≤ S.card + 1 := by
        have := Finset.card_image_le (s := S) (f := fun a : Fin r => a.val + 1)
        omega

theorem cut_ppath {LL : Letters (Fin N)} {b' : Fin N → ℕ} (P1 : PPath r N LL b') (n0 : ℕ) :
    ∃ bc, ∃ Pc : PPath r N LL bc, Pc.mu = cutPath n0 P1.mu := by
  classical
  have hdom : ∀ k, k < N + 1 → Antitone (stg P1.mu k) := by
    intro k hk
    rw [← stg_eq P1.mu k hk]; exact P1.dom _
  refine ⟨fun i => if i.val < n0 then b' i else 0, ⟨cutPath n0 P1.mu, ?_, ?_, ?_⟩, rfl⟩
  · show stg P1.mu (min (0 : Fin (N + 1)).val n0) = 0
    simp only [Fin.val_zero, Nat.zero_min]
    rw [← stg_eq P1.mu 0 (by omega)]
    exact P1.zero
  · intro i
    exact hdom _ (lt_of_le_of_lt (min_le_left _ _) i.isLt)
  · intro i
    have hi := i.isLt
    by_cases h : i.val < n0
    · have e1 : cutPath n0 P1.mu i.castSucc = P1.mu i.castSucc := by
        show stg P1.mu (min i.val n0) = _
        rw [min_eq_left (by omega), stg_castSucc P1.mu]
      have e2 : cutPath n0 P1.mu i.succ = P1.mu i.succ := by
        show stg P1.mu (min (i.val + 1) n0) = _
        rw [min_eq_left (by omega), stg_succ P1.mu]
      rw [e1, e2]
      simp only [h, if_true]
      exact P1.step i
    · have e1 : cutPath n0 P1.mu i.castSucc = stg P1.mu n0 := by
        show stg P1.mu (min i.val n0) = _
        rw [min_eq_right (by omega)]
      have e2 : cutPath n0 P1.mu i.succ = stg P1.mu n0 := by
        show stg P1.mu (min (i.val + 1) n0) = _
        rw [min_eq_right (by omega)]
      rw [e1, e2]
      simp only [h, if_false]
      have hs : HStrip (stg P1.mu n0) (stg P1.mu n0) 0 :=
        ⟨fun _ => le_rfl, fun a h' => hdom n0 (by omega) (by rw [Fin.le_def]; simp), by simp⟩
      split_ifs <;> exact hs

theorem joinPT_parts {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) : joinPT (plPart μ) (tanPart μ) = μ := by
  funext i
  exact Fin.append_castAdd_natAdd

end Gen6

section Dat6

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

theorem dplus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) (hs : s ≤ segN X.F j - r) :
    T.dplus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  unfold T.dplus Dat.beS
  have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
      (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2 h2
  · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

theorem plHyp_of (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) :
    PlHyp (segN X.F j - r) (X.beS p K j b : ℤ) (plPart μ) := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  obtain ⟨P, hPμ⟩ := hP.path
  have hrN : r ≤ segN X.F j := k_r_le_segN X.F hV hr j
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK

  have htau : ∀ t (ht : t < r), ∃ l : Fin (segN X.F j), l.val = segN X.F j - r + t ∧
      segE X.F j l = X.F.fr j t ∧ HStrip (stg μ (segN X.F j - r + t)) (stg μ (segN X.F j - r + t + 1)) (dd l) := by
    intro t ht
    let l : Fin (segN X.F j) := ⟨segN X.F j - r + t, by omega⟩
    have hl : segE X.F j l = X.F.fr j t := (segE_eq_fr_iff X.F hV j l ht).mpr rfl
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hl]; exact (hV.2.2.2.2.1 j t ht).2
    have hs := T.step_vec P l hvec
    rw [hPμ, stg_castSucc μ, stg_succ μ] at hs
    exact ⟨l, rfl, hl, hs⟩
  have hlow : ∀ i ≤ segN X.F j - r, ∀ m, stg μ i m ≤ (X.beS p K j b : ℤ) := by
    intro i hi m
    have h1 := T.mu_le_dplus P i (by omega) m
    rw [hPμ, stg_eq μ i (by omega)] at h1
    have h2 := dplus_le_beS X p K hX j b μ dd hP i hi
    exact le_trans h1 (by exact_mod_cast h2)
  have hup : ∀ t ≤ r, ∀ m, stg μ (segN X.F j - r + t) m ≤ (X.beS p K j b : ℤ) := by
    intro t
    induction t with
    | zero => intro _ m; exact hlow _ le_rfl m
    | succ t ih =>
      intro ht m
      obtain ⟨l, hlv, hl, hs⟩ := htau t (by omega)
      rw [show segN X.F j - r + (t + 1) = segN X.F j - r + t + 1 by ring]
      by_cases hm : m.val = 0
      · have := hP.head l ⟨t, by omega⟩ hl m (by omega)
        rw [stg_succ μ, hlv] at this
        rw [this]
      · have hm' := m.isLt
        have h2 := hs.2.1 ⟨m.val - 1, by omega⟩ (by simp only []; omega)
        have e : (⟨(⟨m.val - 1, by omega⟩ : Fin (r + K)).val + 1, by simp only []; omega⟩ : Fin (r + K)) = m :=
          Fin.ext (by simp only []; omega)
        rw [e] at h2
        exact le_trans h2 (ih (by omega) _)
  have hdom : ∀ k, k < segN X.F j + 1 → Antitone (stg (plPart μ) k) := by
    intro k hk a a' haa
    rw [stg_plPart, stg_plPart, ← stg_eq μ k hk, ← hPμ]
    exact P.dom _ (by rw [Fin.le_def]; simpa using haa)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi m
    rw [stg_plPart]
    constructor
    · have h1 := T.mu_nonneg P i (by omega) (Fin.castAdd K m) (by
        have := m.isLt
        simp only [Fin.val_castAdd]; omega)
      rwa [hPμ, stg_eq μ i (by omega)] at h1
    · by_cases h : i ≤ segN X.F j - r
      · exact hlow i h _
      · have := hup (i - (segN X.F j - r)) (by omega) (Fin.castAdd K m)
        rwa [show segN X.F j - r + (i - (segN X.F j - r)) = i by omega] at this
  · intro m
    rw [stg_plPart]
    obtain ⟨l, hlv, hl, -⟩ := htau (r - 1) (by omega)
    have := hP.head l ⟨r - 1, by omega⟩ hl (Fin.castAdd K m) (by
      have := m.isLt
      simp only [Fin.val_castAdd]; omega)
    rw [stg_succ μ, hlv, show segN X.F j - r + (r - 1) + 1 = segN X.F j by omega] at this
    exact this
  · intro t ht c
    obtain ⟨l, hlv, hl, hs⟩ := htau t ht
    refine colH_step (hdom _ (by omega)) (hdom _ (by omega)) ?_ ?_ c
    · intro a
      rw [stg_plPart, stg_plPart]
      exact hs.1 _
    · intro a h
      rw [stg_plPart, stg_plPart]
      have := hs.2.1 (Fin.castAdd K a) (by simp only [Fin.val_castAdd]; omega)
      exact this

end Dat6

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem rename_mem_supported {R σ τ : Type} [CommRing R] {f : σ → τ} {S : Set σ} {S' : Set τ}
    (h : ∀ v ∈ S, f v ∈ S') {P : MvPolynomial σ R} (hP : P ∈ supported R S) : rename f P ∈ supported R S' := by
  classical
  rw [mem_supported] at hP ⊢
  intro v hv
  have h1 := vars_rename f P (Finset.mem_coe.mp hv)
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h1
  exact h u (hP (Finset.mem_coe.mpr hu))

theorem sum_single_apply_zero {σ ι : Type} (s : Finset ι) (a : ι → σ) (k : ι → ℕ) (v : σ) (h : ∀ i ∈ s, a i ≠ v) :
    (∑ i ∈ s, Finsupp.single (a i) (k i)) v = 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finsupp.single_apply, if_neg (h i hi)]

section Fin7

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (K : ℕ)

def gp (j : ℤ) : Fin (segN X.F j) × Fin r → ℤ × Fin (r + K) := fun v => (segE X.F j v.1, Fin.castAdd K v.2)

def gt (j : ℤ) : Fin (segN X.F j) × Fin K → ℤ × Fin (r + K) := fun v => (segE X.F j v.1, Fin.natAdd r v.2)

theorem segRen_PsiPl (O : Type) [CommRing O] (j : ℤ) (ν : Fin (segN X.F j + 1) → Fin r → ℤ)
    (I : ℤ → Finset (Fin r)) :
    segRen X.F j O (r + K) (PsiPl O ν I) = rename (gp X K j) (Psi O ν I) := by
  unfold segRen PsiPl
  rw [rename_rename]
  rfl

theorem segRen_PsiTan (O : Type) [CommRing O] (j : ℤ) (κ : Fin (segN X.F j + 1) → Fin K → ℤ)
    (I : ℤ → Finset (Fin K)) :
    segRen X.F j O (r + K) (PsiTan O κ I) = rename (gt X K j) (Psi O κ I) := by
  unfold segRen PsiTan
  rw [rename_rename]
  rfl

def tauSet (j : ℤ) : Set (ℤ × Fin (r + K)) := {v | ∃ t c : Fin r, v = (X.F.fr j t.val, Fin.castAdd K c)}

theorem castAdd_ne_natAdd (a : Fin r) (c : Fin K) : Fin.castAdd K a ≠ Fin.natAdd r c := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  have := a.isLt
  omega

theorem gp_preimage {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ) :
    (gp X K j) ⁻¹' (X.offSet K j) = offN (segN X.F j - r) := by
  have hrN := k_r_le_segN X.F hV (NeZero.pos r) j
  ext v
  have hv1 := v.1.isLt
  constructor
  · rintro ⟨t, c, hc, hv⟩
    simp only [gp, Prod.mk.injEq] at hv
    have h1 := (segE_eq_fr_iff X.F hV j v.1 t.isLt).mp hv.1
    have h2 : v.2 = c := Fin.castAdd_injective _ _ hv.2
    refine ⟨by omega, fun h3 => hc ?_⟩
    apply Fin.ext
    rw [Fin.val_rev, ← h2]
    omega
  · rintro ⟨h1, h2⟩
    have ht : v.1.val - (segN X.F j - r) < r := by omega
    refine ⟨⟨v.1.val - (segN X.F j - r), ht⟩, v.2, ?_, ?_⟩
    · intro h3
      apply h2
      have := congrArg Fin.val h3
      rw [Fin.val_rev] at this
      simp only [] at this
      omega
    · simp only [gp, Prod.mk.injEq, and_true]
      exact (segE_eq_fr_iff X.F hV j v.1 ht).mpr (by omega)

theorem gt_preimage (j : ℤ) : (gt X K j) ⁻¹' (X.offSet K j) = ∅ := by
  ext v
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  rintro ⟨t, c, -, hv⟩
  simp only [gt, Prod.mk.injEq] at hv
  exact castAdd_ne_natAdd K c v.2 hv.2.symm

def dgT (j : ℤ) (n0 : ℕ) (hN : n0 + r = segN X.F j) (be : ℤ) (ν : Fin (segN X.F j + 1) → Fin r → ℤ) :
    ℤ × Fin (r + K) →₀ ℕ :=
  ∑ c ∈ Finset.Icc 1 be, ∑ m ∈ riseA n0 ν c r, Finsupp.single (gp X K j (tauI n0 hN m, m)) 1

theorem kill_wordEl (O : Type) [CommRing O] {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ)
    (hN : segN X.F j - r + r = segN X.F j) (be : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ))
    (H : PlHyp (segN X.F j - r) be (plPart q.1)) :
    ∃ e : ℕ, kill (X.offSet K j) (X.wordEl K O j q) =
      (-1) ^ e * monomial (dgT X K j (segN X.F j - r) hN be (plPart q.1)) (1 : O) *
        segRen X.F j O (r + K) (PsiPl O (cutPath (segN X.F j - r) (plPart q.1)) (Icut (segN X.F j - r) (plPart q.1)) *
          PsiTan O (tanPart q.1) q.2.1) := by
  classical
  obtain ⟨e, he⟩ := kill_Psi (R := O) hN H
  refine ⟨e, ?_⟩
  unfold Dat.wordEl
  rw [map_mul, map_mul, map_mul, segRen_PsiPl, segRen_PsiTan, segRen_PsiPl, kill_rename, kill_rename,
    gp_preimage X K hV j, kill_of_empty _ (gt_preimage X K j), he]
  simp only [map_mul, map_pow, map_neg, map_one, map_prod, rename_X]
  unfold dgT
  rw [MvPolynomial.monomial_sum_one]
  have : ∀ c ∈ Finset.Icc 1 be,
      monomial (∑ m ∈ riseA (segN X.F j - r) (plPart q.1) c r,
        Finsupp.single (gp X K j (tauI (segN X.F j - r) hN m, m)) 1) (1 : O) =
      ∏ m ∈ riseA (segN X.F j - r) (plPart q.1) c r, MvPolynomial.X (gp X K j (tauI (segN X.F j - r) hN m, m)) := by
    intro c _
    rw [MvPolynomial.monomial_sum_one]
    rfl
  rw [Finset.prod_congr rfl this]
  ring

theorem monTau_apply {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ) (u : Fin r × Fin r → ℕ) (t c : Fin r) :
    X.monTau K j u (X.F.fr j t.val, Fin.castAdd K c) = u (t, c) := by
  classical
  unfold Dat.monTau
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (t, c)]
  · simp
  · intro v _ hv
    rw [Finsupp.single_apply, if_neg]
    intro h
    simp only [Prod.mk.injEq] at h
    exact hv (Prod.ext (fr_injective X.F hV j h.1) (Fin.castAdd_injective _ _ h.2))
  · intro h; exact absurd (Finset.mem_univ _) h

end Fin7

theorem restKey_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestKey C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hB
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have hN : segN X.F j - r + r = segN X.F j := Nat.sub_add_cancel hrN
  have h10 : BracketPolynomialSpan D := hAdm.2.2.2.2.2.2.2.2.2.1
  have h12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := (h12 p O S n' r K X.F X.L₁ X.N₁ j (fun _ => 0) (fun _ => 0) (fun _ => 0) hV hNK
    (fun _ => le_rfl)).2.1
  have hH : ∀ q : X.Idx p K j (X.restr j b),
      PlHyp (segN X.F j - r) (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) := by
    intro q
    obtain ⟨dd, hP, -⟩ := q.2
    exact plHyp_of X p K hX j _ _ dd hP
  have hpair : ∀ q : X.Idx p K j (X.restr j b), ∃ b' b'' : Fin (segN X.F j) → ℕ,
      (∃ P1 : PPath r (segN X.F j) (segLL X.F j) b', P1.mu = plPart q.1.1) ∧
      (∃ P2 : PPath K (segN X.F j) (segLL X.F j) b'', P2.mu = tanPart q.1.1) := by
    intro q
    obtain ⟨dd, hP, -⟩ := q.2
    obtain ⟨P, hPμ⟩ := hP.path
    obtain ⟨b', b'', -, h1, h2, -⟩ := (h10 (segN X.F j) r K (segLL X.F j) dd hNK (plPart q.1.1) (tanPart q.1.1)).mp
      ⟨P, by rw [hPμ, joinPT_parts]⟩
    exact ⟨b', b'', h1, h2⟩
  have hx : ∀ q : X.Idx p K j (X.restr j b),
      ((cutPath (segN X.F j - r) (plPart q.1.1), tanPart q.1.1) ∈ segPairsAll X.F j K) ∧
      IsSt (cutPath (segN X.F j - r) (plPart q.1.1)) (Icut (segN X.F j - r) (plPart q.1.1)) ∧
      IsSt (tanPart q.1.1) q.1.2.1 := by
    intro q
    obtain ⟨b', b'', ⟨P1, h1⟩, h2⟩ := hpair q
    obtain ⟨bc, Pc, hPc⟩ := cut_ppath P1 (segN X.F j - r)
    obtain ⟨dd, -, -, hSt, -⟩ := q.2
    exact ⟨⟨bc, b'', ⟨Pc, by rw [hPc, h1]⟩, h2⟩, isSt_cut hN (hH q), hSt⟩
  let x : X.Idx p K j (X.restr j b) →
      {x : ((Fin (segN X.F j + 1) → Fin r → ℤ) × (Fin (segN X.F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll X.F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} := fun q =>
    ⟨((cutPath (segN X.F j - r) (plPart q.1.1), tanPart q.1.1),
      (Icut (segN X.F j - r) (plPart q.1.1), q.1.2.1)), hx q⟩
  let M : X.Idx p K j (X.restr j b) → (ℤ × Fin (r + K) →₀ ℕ) := fun q =>
    X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)
  have htauI : ∀ m : Fin r, gp X K j (tauI (segN X.F j - r) hN m, m) ∈ tauSet X K j := by
    intro m
    have hm := m.isLt
    refine ⟨⟨r - 1 - m.val, by omega⟩, m, ?_⟩
    simp only [gp, Prod.mk.injEq, and_true]
    exact (segE_eq_fr_iff X.F hV j _ (by omega)).mpr rfl
  have hM : ∀ q, ∀ v, M q v ≠ 0 → v ∈ tauSet X K j := by
    intro q v hv
    by_contra hnot
    apply hv
    show (X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q.1.1)) v = 0
    rw [Finsupp.add_apply]
    have h1 : X.monTau K j q.1.2.2 v = 0 := by
      unfold Dat.monTau
      exact sum_single_apply_zero _ _ _ v fun i _ h => hnot ⟨i.1, i.2, h.symm⟩
    have h2 : dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) v = 0 := by
      unfold dgT
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      exact sum_single_apply_zero _ _ _ v fun m _ h => hnot (h ▸ htauI m)
    rw [h1, h2]
  have hsup : ∀ q, segRen X.F j O (r + K) (PsiPl O (x q).1.1.1 (x q).1.2.1 * PsiTan O (x q).1.1.2 (x q).1.2.2) ∈
      supported O (tauSet X K j)ᶜ := by
    intro q
    rw [map_mul, segRen_PsiPl, segRen_PsiTan]
    refine Subalgebra.mul_mem _ ?_ ?_
    · refine rename_mem_supported ?_ (Psi_cut_supported (segN X.F j - r) (by omega) (plPart q.1.1) _)
      rintro v hv ⟨t, c, h⟩
      simp only [gp, Prod.mk.injEq] at h
      have := (segE_eq_fr_iff X.F hV j v.1 t.isLt).mp h.1
      have hv' : v.1.val < segN X.F j - r := hv
      omega
    · refine rename_mem_supported (S := Set.univ) ?_ (by rw [supported_univ]; exact Algebra.mem_top)
      rintro v - ⟨t, c, h⟩
      simp only [gt, Prod.mk.injEq] at h
      exact castAdd_ne_natAdd K c v.2 h.2.symm
  have hinj : ∀ q q', M q = M q' → x q = x q' → q = q' := by
    intro q q' hMq hxq
    have hx' := congrArg Subtype.val hxq
    simp only [x, Prod.mk.injEq] at hx'
    obtain ⟨⟨hcut, hκ⟩, hI, hI''⟩ := hx'
    obtain ⟨b1, -, ⟨P1, h1⟩, -⟩ := hpair q
    obtain ⟨b2, -, ⟨P2, h2⟩, -⟩ := hpair q'
    have hν : plPart q.1.1 = plPart q'.1.1 :=
      path_eq_of_cut hN (hH q) (hH q') (fun i => by rw [← h1]; exact P1.dom i) (fun i => by rw [← h2]; exact P2.dom i)
        hcut hI
    have hμ : q.1.1 = q'.1.1 := by
      rw [← joinPT_parts q.1.1, ← joinPT_parts q'.1.1, hν, hκ]
    have hu0 : X.monTau K j q.1.2.2 = X.monTau K j q'.1.2.2 := by
      have h3 : X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q.1.1) =
          X.monTau K j q'.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q'.1.1) := hMq
      rw [hν] at h3
      exact add_right_cancel h3
    have hu : q.1.2.2 = q'.1.2.2 := by
      funext v
      rw [← monTau_apply X K hV j q.1.2.2 v.1 v.2, ← monTau_apply X K hV j q'.1.2.2 v.1 v.2, hu0]
    exact Subtype.ext (Prod.ext hμ (Prod.ext hI'' hu))
  have hli := li_mono_words (tauSet X K j) _ hw M x hM hsup hinj
  have hkill := fun q : X.Idx p K j (X.restr j b) =>
    kill_wordEl X K O hV j hN (X.beS p K j (X.restr j b) : ℤ) q.1 (hH q)
  choose e he using hkill
  have hli2 := hli.units_smul fun q => (-1 : Oˣ) ^ e q
  have heq : (fun q : X.Idx p K j (X.restr j b) =>
      monomial (X.monTau K j q.1.2.2) (1 : O) * kill (X.offSet K j) (X.wordEl K O j q.1)) =
      ((fun q => (-1 : Oˣ) ^ e q) • fun q => monomial (M q) (1 : O) *
        segRen X.F j O (r + K) (PsiPl O (x q).1.1.1 (x q).1.2.1 * PsiTan O (x q).1.1.2 (x q).1.2.2)) := by
    funext q
    rw [he q]
    simp only [Pi.smul_apply']
    rw [Units.smul_def, MvPolynomial.smul_eq_C_mul]
    have hmm : monomial (M q) (1 : O) = monomial (X.monTau K j q.1.2.2) (1 : O) *
        monomial (dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)) (1 : O) := by
      rw [monomial_mul, one_mul]
    rw [hmm]
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, map_pow, map_neg, map_one]
    ring
  rw [heq]
  exact hli2

end Formalism.MainNotions.SelectionLemmas.Pf
