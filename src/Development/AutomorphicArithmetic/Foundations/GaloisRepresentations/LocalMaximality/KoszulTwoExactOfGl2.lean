module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulTwoExactOfGl2
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.WH

namespace UpperTheory.Gal.productCup_of_system

private theorem wd_single {σ E : Type} [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (T : Finset σ) (v : E) :
    wd w (Pi.single T v) =
      ∑ i ∈ Tᶜ, Pi.single (insert i T) (GlobalTheory.cubeSign (insert i T) i • w i v) := by
  funext t
  have hl : wd w (Pi.single T v) t =
      ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ((Pi.single T v : Finset σ → E) (t.erase i)) := by
    simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]
  have L : ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ((Pi.single T v : Finset σ → E) (t.erase i)) =
      ∑ i, if i ∈ t ∧ t.erase i = T then GlobalTheory.cubeSign t i • w i v else 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by simp [hi])]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h : t.erase i = T
    · simp [hi, h]
    · simp [hi, h, Pi.single_eq_of_ne h]
  have Rr : (∑ i ∈ Tᶜ, (Pi.single (insert i T) (GlobalTheory.cubeSign (insert i T) i • w i v) :
      Finset σ → E)) t =
      ∑ i, if i ∉ T ∧ t = insert i T then GlobalTheory.cubeSign t i • w i v else 0 := by
    rw [Finset.sum_apply, ← Finset.sum_subset (Finset.subset_univ Tᶜ)
      (fun i _ hi => by simp at hi; simp [hi])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ∉ T := by simpa using hi
    by_cases h : t = insert i T
    · subst h; simp [hi']
    · simp [hi', h, Pi.single_eq_of_ne h]
  rw [hl, L, Rr]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (i ∈ t ∧ t.erase i = T) ↔ (i ∉ T ∧ t = insert i T) := by
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨Finset.notMem_erase _ _, (Finset.insert_erase h1).symm⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨Finset.mem_insert_self _ _, Finset.erase_insert h1⟩
  simp only [this]

private theorem sm_dec {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) {x : E}
    (hx : x ∈ sm act M (Set.range f)) :
    ∃ g : Fin d → E, (∀ j, g j ∈ M) ∧ x = ∑ j, act (f j) (g j) := by
  unfold sm at hx
  rw [iSup_range] at hx
  refine Submodule.iSup_induction _ (motive := fun x => ∃ g : Fin d → E, (∀ j, g j ∈ M) ∧
    x = ∑ j, act (f j) (g j)) hx ?_ ?_ ?_
  · intro j x hx
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨Pi.single j m, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using hm
      · simp [Pi.single_eq_of_ne h]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  · exact ⟨0, fun _ => M.zero_mem, by simp⟩
  · rintro x y ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
    exact ⟨g + g', fun j => M.add_mem (hg j) (hg' j), by
      simp [Finset.sum_add_distrib]⟩

private theorem single_mem {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (M : Submodule ℂ E) (w : σ → Module.End ℂ E) {T : Finset σ} {v : E} {d : ℕ}
    (hT : T.card = d) (hv : v ∈ M) :
    (Pi.single T v : Finset σ → E) ∈ (acx (fun _ => M) w).C d := by
  simp only [acx, Submodule.mem_pi]
  intro s _
  by_cases h : s = T
  · subst h; simp [hT, hv]
  · simp [Pi.single_eq_of_ne h]

theorem koszulTwoExact_of_gl2 : FiltrationCocycleLiftCriterion → SubQEx → KoszulCocycleExistsWithPrescribedComponent := by
  intro gl2 subq S E _ _ _ _ act κ _ _ R M r d e hst hr hke m hm hsm
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = img e := ⟨_, rfl⟩
  have hcard : Q.card = d := by simp [hQ, img]
  have hQmem : ∀ j, e j ∈ Q := fun j => by simp [hQ, img]
  have qex : QEx (fun _ => M) (fun l => act (r l)) Q d := hQ ▸ subq S E act κ M r d e hke
  have wok : WOk (fun _ : Finset κ => M) (fun l => act (r l)) :=
    ⟨fun i j => by
      show act (r i) * act (r j) = act (r j) * act (r i)
      rw [← map_mul, ← map_mul, mul_comm], fun s i _ x hx => hst _ (hr i) _ hx⟩
  choose g hgM hg using fun l => sm_dec act M (fun j => r (e j)) (hsm l)
  have hTcard : ∀ l, l ∉ Q → ∀ j, ((insert l Q).erase (e j)).card = d := fun l hl j => by
    rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem (hQmem j)), Finset.card_insert_of_notMem hl,
      hcard]
    rfl
  have hTQ : ∀ l, l ∉ Q → ∀ j, ((insert l Q).erase (e j)) ∩ Q = Q.erase (e j) := fun l hl j => by
    ext i
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, Or.inr h2⟩, h2⟩
  have hterm : ∀ l, l ∉ Q → ∀ j (v : E),
      wd (wOn Q fun l => act (r l)) (Pi.single ((insert l Q).erase (e j)) v) =
        Pi.single (insert l Q) (GlobalTheory.cubeSign (insert l Q) (e j) • act (r (e j)) v) := by
    intro l hl j v
    have hmem : e j ∈ insert l Q := Finset.mem_insert_of_mem (hQmem j)
    rw [wd_single, Finset.sum_eq_single (e j)]
    · rw [Finset.insert_erase hmem]
      simp [wOn, hQmem j]
    · intro i hi hne
      have hiQ : i ∉ Q := by
        intro h
        apply (Finset.mem_compl.1 hi)
        exact Finset.mem_erase.2 ⟨hne, Finset.mem_insert_of_mem h⟩
      simp [wOn, hiQ]
    · intro h
      exact absurd (Finset.mem_compl.2 (Finset.notMem_erase _ _)) h
  have hsum : ∀ (t : Finset κ) (f : Fin d → E),
      (Pi.single t (∑ j, f j) : Finset κ → E) = ∑ j, Pi.single t (f j) := fun t f =>
    map_sum (AddMonoidHom.single (fun _ : Finset κ => E) t) f Finset.univ
  have hy : ∃ y ∈ (acx (fun _ => M) (fun l => act (r l))).C d, Lev Q (· = (d : ℤ) - 1) y ∧
      wd (wOn Q fun l => act (r l)) y = wd (wOn Qᶜ fun l => act (r l)) (Pi.single Q m) := by
    refine ⟨∑ l ∈ Qᶜ, ∑ j, Pi.single ((insert l Q).erase (e j))
        ((GlobalTheory.cubeSign (insert l Q) l * GlobalTheory.cubeSign (insert l Q) (e j)) • g l j), ?_, ?_, ?_⟩
    · refine Submodule.sum_mem _ fun l hl => Submodule.sum_mem _ fun j _ => ?_
      have hl' : l ∉ Q := by simpa using hl
      exact single_mem M _ (hTcard l hl' j) (Submodule.smul_of_tower_mem _ _ (hgM l j))
    · intro s hs
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hl' : l ∉ Q := by simpa using hl
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : s ≠ (insert l Q).erase (e j) := by
        rintro rfl
        apply hs
        rw [hTQ l hl' j, Finset.card_erase_of_mem (hQmem j), hcard]
        have : 1 ≤ d := by
          rw [← hcard]
          exact Finset.card_pos.2 ⟨_, hQmem j⟩
        omega
      exact Pi.single_eq_of_ne this _
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [wd_single, map_sum]
        refine Finset.sum_congr rfl fun l hl => ?_
        have hl' : l ∉ Q := by simpa using hl
        have hlc : l ∈ Qᶜ := hl
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [hterm l hl']
        rw [← hsum]
        congr 1
        have hw : wOn Qᶜ (fun l => act (r l)) l m = ∑ j, act (r (e j)) (g l j) := by
          simpa [wOn, hl'] using hg l
        rw [hw, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, smul_smul, mul_comm, mul_assoc, GlobalTheory.cubeSign_mul_self, mul_one]
  obtain ⟨c, hc, hlev⟩ := gl2 κ E (fun _ => M) (fun l => act (r l)) Q d d wok qex
    (Pi.single Q m) (single_mem M _ hcard hm)
    (by
      intro s hs
      have : s ≠ Q := by
        rintro rfl
        simp [hcard] at hs
      exact Pi.single_eq_of_ne this _)
    (by
      rw [wd_single]
      refine Finset.sum_eq_zero fun i hi => ?_
      have : i ∉ Q := by simpa using hi
      simp [wOn, this])
    hy
  refine ⟨c, hc, ?_⟩
  have h := hlev Q (by simp [hcard])
  rw [hQ] at h
  have h' : c (img e) - (Pi.single (img e) m : Finset κ → E) (img e) = 0 := h
  simpa [sub_eq_zero] using h'

end UpperTheory.Gal.productCup_of_system

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.MemUniInr
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private def phiT {d : ℕ} : Fin (d + 1) ⊕ₗ Fin d → Fin (d + 1) := fun t => Sum.elim id Fin.succ (ofLex t)

private def cT {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E) :
    Fin (d + 1) ⊕ₗ Fin d → S :=
  app (fun _ => 1) (fun l : Fin d => (T.X l.succ : S))

private lemma rowT_eq {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (t : Fin (d + 1) ⊕ₗ Fin d) : T.rowT t = Pi.single (phiT t) (cT T t) := by
  rcases t with i | l <;> rfl

private lemma det_single {S : Type} [CommRing S] {n : ℕ} (g : Fin n → Fin n) (v : Fin n → S) :
    (Matrix.of fun a b => (Pi.single (g a) (v a) : Fin n → S) b).det = 0 ∨
      (Function.Bijective g ∧ ∃ ε : ℤˣ,
        (Matrix.of fun a b => (Pi.single (g a) (v a) : Fin n → S) b).det = ε • ∏ a, v a) := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply, Pi.single_apply]
  rw [Finset.sum_congr rfl fun σ _ => by rw [Fintype.prod_ite_zero]]
  by_cases hg : Function.Bijective g
  · right
    refine ⟨hg, Equiv.Perm.sign (Equiv.ofBijective g hg), ?_⟩
    rw [Finset.sum_eq_single (Equiv.ofBijective g hg)]
    · rw [if_pos (show ∀ i, (Equiv.ofBijective g hg) i = g i from fun i => rfl)]
    · intro σ _ hσ
      rw [if_neg, smul_zero]
      intro h
      exact hσ (Equiv.ext fun i => h i)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · left
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg, smul_zero]
    intro h
    have hgσ : g = σ := funext fun i => (h i).symm
    exact hg (hgσ ▸ σ.bijective)

private lemma detC_eq {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin d)) (h : s.card = d + 1) :
    detC T.rowT s = (Matrix.of fun a b => (Pi.single (phiT (s.orderEmbOfFin h a)) (cT T (s.orderEmbOfFin h a)) :
      Fin (d + 1) → S) b).det := by
  simp only [detC, dif_pos h, rowT_eq]

private lemma detC_id {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin d)) (h : s.card = d + 1) (f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d)
    (hfs : ∀ a, f a ∈ s) (hf : StrictMono f) (hφ : ∀ a, phiT (f a) = a) :
    detC T.rowT s = ∏ a, cT T (f a) := by
  have hf' : ∀ a, s.orderEmbOfFin h a = f a := fun a =>
    (congrFun (Finset.orderEmbOfFin_unique h hfs hf) a).symm
  rw [detC_eq T s h]
  simp only [hf', hφ]
  rw [show (Matrix.of fun a b => (Pi.single a (cT T (f a)) : Fin (d + 1) → S) b) =
      Matrix.diagonal (fun a => cT T (f a)) from ?_]
  · exact Matrix.det_diagonal
  · ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.diagonal_apply_ne _ hab, Pi.single_apply, Ne.symm hab]

private lemma mem_uni_inl {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) (i : Fin (d + 1)) :
    toLex (Sum.inl i) ∈ uni I L ↔ i ∈ I := by
  simp [uni]

private lemma mem_uni_inr {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) (l : Fin d) :
    toLex (Sum.inr l) ∈ uni I L ↔ l ∈ L := by
  simp [uni]

private lemma card_uni' {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) :
    (uni I L).card = I.card + L.card := by
  simp [uni]

private lemma prod_uni' {d : ℕ} {S : Type} [CommMonoid S] (I : Finset (Fin (d + 1))) (L : Finset (Fin d))
    (c : Fin (d + 1) ⊕ₗ Fin d → S) :
    ∏ t ∈ uni I L, c t = (∏ i ∈ I, c (toLex (Sum.inl i))) * ∏ l ∈ L, c (toLex (Sum.inr l)) := by
  rw [uni, Finset.prod_map, Finset.prod_disjSum]
  rfl

private lemma prod_emb {α M : Type} [LinearOrder α] [CommMonoid M] (s : Finset α) {k : ℕ} (h : s.card = k) (c : α → M) :
    ∏ a, c (s.orderEmbOfFin h a) = ∏ t ∈ s, c t := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ s h]
  rw [Finset.prod_map]
  rfl

private theorem wd_lmul_app_detC_eq_zero_of_det (hD : Det) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E]
    [Module ℂ E] (T : Sys d S E) :
    (wd fun t => (Algebra.lmul ℂ S) (app (fun _ => (1 : S)) (fun l : Fin d => (T.X l.succ : S)) t))
      (detC T.rowT) = 0 := by
  have key := hD S S (Algebra.lmul ℂ S) (Fin (d + 1) ⊕ₗ Fin d) (d + 1) T.rowT (fun _ => 1) 1
  have h1 : (fun l => Algebra.lmul ℂ S (∑ b, T.rowT l b * 1)) =
      fun t => Algebra.lmul ℂ S (app (fun _ => (1 : S)) (fun l : Fin d => (T.X l.succ : S)) t) := by
    funext t
    rw [show (∑ b, T.rowT t b * 1) = cT T t by simp [rowT_eq]]
    rfl
  have h2 : (fun s => Algebra.lmul ℂ S (detC T.rowT s) 1) = detC T.rowT := by
    funext s
    simp
  rw [h1, h2] at key
  exact key

private theorem detC_uni_univ_empty {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) : detC T.rowT (uni Finset.univ ∅) = 1 := by
  rw [detC_id T (uni Finset.univ ∅) (by simp [card_uni']) (fun a => toLex (Sum.inl a))
    (fun a => (mem_uni_inl _ _ a).2 (Finset.mem_univ a)) Sum.Lex.inl_strictMono (fun a => rfl)]
  simp [cT, app]

private theorem detC_uni_singleton_zero_univ {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) : detC T.rowT (uni {0} Finset.univ) = ∏ l : Fin d, (T.X l.succ : S) := by
  let f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d := fun a =>
    Fin.cases (motive := fun _ => Fin (d + 1) ⊕ₗ Fin d) (toLex (Sum.inl 0)) (fun l => toLex (Sum.inr l)) a
  have hfs : ∀ a, f a ∈ uni {0} Finset.univ := by
    intro a
    cases a using Fin.cases with
    | zero => exact (mem_uni_inl _ _ 0).2 (Finset.mem_singleton_self 0)
    | succ l => exact (mem_uni_inr _ _ l).2 (Finset.mem_univ l)
  have hf : StrictMono f := by
    intro a b hab
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact absurd hab (lt_irrefl _)
      | succ l => exact Sum.Lex.inl_lt_inr _ _
    | succ i =>
      cases b using Fin.cases with
      | zero => exact absurd hab (Fin.not_lt_zero _)
      | succ l => exact Sum.Lex.inr_strictMono (Fin.succ_lt_succ_iff.1 hab)
  have hφ : ∀ a, phiT (f a) = a := by
    intro a
    cases a using Fin.cases <;> rfl
  have hcard : (uni ({0} : Finset (Fin (d + 1))) (Finset.univ : Finset (Fin d))).card = d + 1 := by
    rw [card_uni', Finset.card_singleton, Finset.card_univ, Fintype.card_fin, add_comm]
  rw [detC_id T _ hcard f hfs hf hφ, Fin.prod_univ_succ]
  simp [f, cT, app]

private theorem detC_uni_eq_zero_or_eq_unit_smul_prod_compl {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) :
    detC T.rowT (uni I L) = 0 ∨
      0 ∈ I ∧ I.card + L.card = d + 1 ∧ ∃ ε : ℤˣ, detC T.rowT (uni I L) = ε • ∏ m ∈ Iᶜ, (T.X m : S) := by
  by_cases hc : (uni I L).card = d + 1
  swap
  · left
    simp only [detC, dif_neg hc]
  rcases det_single (fun a => phiT ((uni I L).orderEmbOfFin hc a))
      (fun a => cT T ((uni I L).orderEmbOfFin hc a)) with h0 | ⟨hbij, ε, hε⟩
  · left
    rw [detC_eq T _ hc]
    exact h0
  · right
    have hdet := (detC_eq T _ hc).trans hε
    have hmem : ∀ t, t ∈ uni I L ↔ ∃ a, (uni I L).orderEmbOfFin hc a = t := by
      intro t
      rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (uni I L) hc, Set.mem_range]
    have h0I : 0 ∈ I := by
      obtain ⟨a, ha⟩ := hbij.2 0
      replace ha : phiT ((uni I L).orderEmbOfFin hc a) = 0 := ha
      have hA : (uni I L).orderEmbOfFin hc a ∈ uni I L := Finset.orderEmbOfFin_mem _ hc a
      generalize (uni I L).orderEmbOfFin hc a = t at ha hA
      rcases t with i | l
      · change i = 0 at ha
        subst ha
        exact (mem_uni_inl I L _).1 hA
      · exact absurd ha (Fin.succ_ne_zero l)
    have hcard : I.card + L.card = d + 1 := by
      rw [← card_uni']
      exact hc
    have hcompl : Iᶜ = L.map (Fin.succEmb d) := by
      ext m
      simp only [Finset.mem_compl, Finset.mem_map, Fin.coe_succEmb]
      constructor
      · intro hm
        obtain ⟨a, ha⟩ := hbij.2 m
        replace ha : phiT ((uni I L).orderEmbOfFin hc a) = m := ha
        have hA : (uni I L).orderEmbOfFin hc a ∈ uni I L := Finset.orderEmbOfFin_mem _ hc a
        generalize (uni I L).orderEmbOfFin hc a = t at ha hA
        rcases t with i | l
        · change i = m at ha
          subst ha
          exact absurd ((mem_uni_inl I L _).1 hA) hm
        · exact ⟨l, (mem_uni_inr I L l).1 hA, ha⟩
      · rintro ⟨l, hl, rfl⟩ hI
        obtain ⟨a, ha⟩ := (hmem (toLex (Sum.inl l.succ))).1 ((mem_uni_inl I L _).2 hI)
        obtain ⟨b, hb⟩ := (hmem (toLex (Sum.inr l))).1 ((mem_uni_inr I L _).2 hl)
        have hab : a = b := hbij.1 (by
          show phiT ((uni I L).orderEmbOfFin hc a) = phiT ((uni I L).orderEmbOfFin hc b)
          rw [ha, hb]
          rfl)
        rw [hab, hb] at ha
        exact Sum.inl_ne_inr (toLex.injective ha.symm)
    refine ⟨h0I, hcard, ε, ?_⟩
    rw [hdet, prod_emb (uni I L) hc (cT T), prod_uni', hcompl, Finset.prod_map]
    simp [cT, app]

theorem UpperTheory.Gal.productCup_of_system.thT_of :
    Det → ThT := by
  intro hD d S E _ _ _ _ T
  exact ⟨wd_lmul_app_detC_eq_zero_of_det hD T, detC_uni_univ_empty T, detC_uni_singleton_zero_univ T, detC_uni_eq_zero_or_eq_unit_smul_prod_compl T⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.MapUnitEq
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocDAux
variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]

private lemma geo_mem {W : Type} [AddCommGroup W] [Module ℂ W] (φ : S →+* Module.End ℂ W)
    (R : Subalgebra ℂ S) (P : Submodule ℂ W) (hP : ∀ s ∈ R, ∀ x ∈ P, φ s x ∈ P) {a b : S}
    (ha : a ∈ R) (hb : b ∈ R) (x : W) (h1 : φ (1 - a * b) x ∈ P) (N : ℕ)
    (hN : φ (a ^ N) x ∈ P) : x ∈ P := by
  have key : (1 : S) = b ^ N * a ^ N + (∑ i ∈ Finset.range N, (a * b) ^ i) * (1 - a * b) := by
    rw [geom_sum_mul_neg, mul_pow]; ring
  have hx : x = φ (b ^ N) (φ (a ^ N) x) +
      φ (∑ i ∈ Finset.range N, (a * b) ^ i) (φ (1 - a * b) x) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      ← LinearMap.add_apply, ← map_add, ← key]
    simp
  rw [hx]
  exact P.add_mem (hP _ (R.pow_mem hb N) _ hN)
    (hP _ (R.sum_mem fun i _ => R.pow_mem (R.mul_mem ha hb) i) _ h1)

private def pwR (act : S →ₐ[ℂ] Module.End ℂ E) (ι : Type) : S →+* Module.End ℂ (ι → E) where
  toFun s := LinearMap.pi fun t => act s ∘ₗ LinearMap.proj t
  map_one' := LinearMap.ext fun c => funext fun t => by simp
  map_mul' s s' := LinearMap.ext fun c => funext fun t => by simp
  map_zero' := LinearMap.ext fun c => funext fun t => by simp
  map_add' s s' := LinearMap.ext fun c => funext fun t => by simp

private lemma pwR_apply (act : S →ₐ[ℂ] Module.End ℂ E) (ι : Type) (s : S) (c : ι → E) (t : ι) :
    pwR act ι s c t = act s (c t) := rfl

private lemma act_comm (act : S →ₐ[ℂ] Module.End ℂ E) (s s' : S) (x : E) :
    act s (act s' x) = act s' (act s x) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

variable {κ : Type} [LinearOrder κ]

private lemma kos_mem_C (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) (r : κ → S) (n : ℤ)
    (c : Finset κ → E) :
    c ∈ (kos act M r).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then M else ⊥ : Submodule ℂ E) := by
  simp [kos, acx, Submodule.mem_pi]

private lemma wd_pw (act : S →ₐ[ℂ] Module.End ℂ E) (r : κ → S) (s : S) (y : Finset κ → E) :
    wd (fun l => act (r l)) (pwR act _ s y) = pwR act _ s (wd (fun l => act (r l)) y) := by
  funext t
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pwR_apply, wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_zsmul, act_comm act s]

private lemma kos_B_stab (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)
    (r : κ → S) (hSt : Stab act R M) (n : ℤ) (s : S) (hs : s ∈ R) (x : Finset κ → E)
    (hx : x ∈ (kos act M r).B n) : pwR act _ s x ∈ (kos act M r).B n := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨pwR act _ s y, ?_, wd_pw act r s y⟩
  rw [SetLike.mem_coe, kos_mem_C] at hy ⊢
  intro t
  have := hy t
  rw [pwR_apply]
  split_ifs at this ⊢ with h
  · exact hSt s hs _ this
  · simp only [Submodule.mem_bot] at this ⊢
    rw [this, map_zero]

private lemma sm_stab (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)
    (T : Set S) (hSt : Stab act R M) (s : S) (hs : s ∈ R) (x : E) (hx : x ∈ sm act M T) :
    act s x ∈ sm act M T := by
  have hle : sm act M T ≤ (sm act M T).comap (act s) := by
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨m, hm, rfl⟩
    rw [Submodule.mem_comap, act_comm]
    exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) t ht le_rfl : _ ≤ sm act M T)
      ⟨_, hSt s hs m hm, rfl⟩
  exact hle hx

private lemma unif_pow (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M M' : Submodule ℂ E)
    (hSt : Stab act R M) {a : S} (ha : a ∈ R) (hloc : ∀ m ∈ M', ∃ N : ℕ, act (a ^ N) m ∈ M)
    {ι : Type} [Fintype ι] (f : ι → E) (hf : ∀ i, f i ∈ M') :
    ∃ N : ℕ, ∀ i, act (a ^ N) (f i) ∈ M := by
  choose n hn using fun i => hloc (f i) (hf i)
  refine ⟨∑ i, n i, fun i => ?_⟩
  have h : ∑ i, n i = (∑ i, n i - n i) + n i := (Nat.sub_add_cancel
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm
  rw [h, pow_add, map_mul, Module.End.mul_apply]
  exact hSt _ (R.pow_mem ha _) _ (hn i)

private lemma map_unit_eq (act : S →ₐ[ℂ] Module.End ℂ E) (M' : Submodule ℂ E) (v : Sˣ)
    (hv : ∀ m ∈ M', act v m ∈ M' ∧ act (v⁻¹ : Sˣ) m ∈ M') (k : ℕ) :
    M'.map (act ((v ^ k : Sˣ) : S)) = M' := by
  have hP : ∀ k : ℕ, ∀ m ∈ M', act ((v ^ k : Sˣ) : S) m ∈ M' ∧ act (((v ^ k)⁻¹ : Sˣ) : S) m ∈ M' := by
    intro k
    induction k with
    | zero => intro m hm; simpa using hm
    | succ k ih =>
      intro m hm
      constructor
      · rw [pow_succ, Units.val_mul, map_mul, Module.End.mul_apply]
        exact (ih _ (hv m hm).1).1
      · rw [pow_succ, mul_inv_rev, Units.val_mul, map_mul, Module.End.mul_apply]
        exact (hv _ (ih m hm).2).2
  refine le_antisymm ?_ fun m hm => ?_
  · rintro _ ⟨m, hm, rfl⟩
    exact (hP k m hm).1
  · refine ⟨_, (hP k m hm).2, ?_⟩
    change act ((v ^ k : Sˣ) : S) (act (((v ^ k)⁻¹ : Sˣ) : S) m) = m
    rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one]
    rfl

end LocDAux

theorem UpperTheory.Gal.productCup_of_system.locD_of :
    RS → Htpy → LocD := by
  intro hRS hH S E _ _ _ _ act κ _ _ R M M' r v a b l0 d hSt hr ha hb hl0 hMM hloc hv
  refine ⟨fun hKE m hm c hc => ?_, fun m hm hsm => ?_⟩
  · have hcC := hc.1
    have hcD : wd (fun l => act (r l)) c = 0 := hc.2

    let u : κ → Sˣ := fun _ => v
    let z : κ → S := fun l => r l * v
    have hrz : ∀ l, r l = z l * ((u l)⁻¹ : Sˣ) := by
      intro l
      simp [z, u, mul_assoc]
    have hmap : ∀ L : Finset κ, M'.map (act ((∏ l ∈ L, u l : Sˣ) : S)) = M' := by
      intro L
      simp only [u, Finset.prod_const]
      exact map_unit_eq act M' v hv _
    have hT : kosT act M' u z = kos act M' z := by
      unfold kosT kos
      simp only [hmap]
    have hR := fun n c => hRS S E act κ M' u r z hrz n c
    have hcC' := (kos_mem_C act M r m c).1 hcC
    have hcZ' : c ∈ (kos act M' r).Z m := by
      refine ⟨(kos_mem_C act M' r m c).2 fun t => ?_, hc.2⟩
      have := hcC' t
      split_ifs at this ⊢ with h
      · exact hMM this
      · exact this
    have hinv : unsc act u (unsc act u⁻¹ c) = c := (hR m c).2.2.2.2
    have hZ : unsc act u⁻¹ c ∈ (kosT act M' u z).Z m :=
      (hR m (unsc act u⁻¹ c)).2.1.2 (by rw [hinv]; exact hcZ')
    have hB : unsc act u⁻¹ c ∈ (kosT act M' u z).B m := by
      rw [hT] at hZ ⊢
      exact hKE m hm hZ
    have hcB : c ∈ (kos act M' r).B m := by
      have := (hR m (unsc act u⁻¹ c)).2.2.1.1 hB
      rwa [hinv] at this
    obtain ⟨y, hy, hyc⟩ := hcB
    have hy' := (kos_mem_C act M' r (m - 1) y).1 hy
    have hyM : ∀ L, y L ∈ M' := by
      intro L
      have := hy' L
      split_ifs at this with h
      · exact this
      · rw [Submodule.mem_bot] at this
        rw [this]
        exact M'.zero_mem
    obtain ⟨N, hN⟩ := unif_pow act R M M' hSt ha hloc y hyM
    refine geo_mem (pwR act _) R ((kos act M r).B m)
      (fun s hs x hx => kos_B_stab act R M r hSt m s hs x hx) ha hb c ?_ N ?_
    · rw [← hl0]
      refine hH S E act κ R M r hSt m c hc (r l0) ⟨Pi.single l0 1, fun l => ?_, ?_⟩
      · by_cases h : l = l0
        · subst h
          simpa using R.one_mem
        · simpa [Pi.single_apply, h] using R.zero_mem
      · simp [Pi.single_apply]
    · refine ⟨pwR act _ (a ^ N) y, (kos_mem_C act M r (m - 1) _).2 fun t => ?_, ?_⟩
      · have := hy' t
        rw [pwR_apply]
        split_ifs at this ⊢ with h
        · exact hN t
        · rw [Submodule.mem_bot] at this ⊢
          rw [this, map_zero]
      · have e := wd_pw act r (a ^ N) y
        change wd (fun l => act (r l)) (pwR act _ (a ^ N) y) = pwR act _ (a ^ N) c
        rw [e]
        rw [← hyc]
        rfl
  · let T : Set S := Set.range r
    let Pn : Submodule ℂ E :=
      { carrier := {x | ∃ N : ℕ, act (a ^ N) x ∈ sm act M T}
        add_mem' := by
          rintro x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
          refine ⟨N₁ + N₂, ?_⟩
          rw [map_add (f := _)]
          refine Submodule.add_mem _ ?_ ?_
          · rw [add_comm, pow_add, map_mul, Module.End.mul_apply]
            exact sm_stab act R M T hSt _ (R.pow_mem ha _) _ h₁
          · rw [pow_add, map_mul, Module.End.mul_apply]
            exact sm_stab act R M T hSt _ (R.pow_mem ha _) _ h₂
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro k x ⟨N, h⟩
          refine ⟨N, ?_⟩
          rw [map_smul]
          exact Submodule.smul_mem _ k h }
    have hle : sm act M' (Set.range fun l => r l * v) ≤ Pn := by
      refine iSup₂_le fun t ht => ?_
      obtain ⟨l, rfl⟩ := ht
      rintro _ ⟨m', hm', rfl⟩
      obtain ⟨N, hN⟩ := hloc _ (hv m' hm').1
      refine ⟨N, ?_⟩
      have e : act (a ^ N) (act (r l * v) m') = act (r l) (act (a ^ N) (act v m')) := by
        rw [map_mul, Module.End.mul_apply, act_comm act (a ^ N) (r l)]
      rw [e]
      exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) (r l) ⟨l, rfl⟩ le_rfl :
        _ ≤ sm act M T) ⟨_, hN, rfl⟩
    obtain ⟨N, hN⟩ := hle hsm
    refine geo_mem act.toRingHom R (sm act M T)
      (fun s hs x hx => sm_stab act R M T hSt s hs x hx) ha hb m ?_ N hN
    change act (1 - a * b) m ∈ sm act M T
    rw [← hl0]
    exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) (r l0) ⟨l0, rfl⟩ le_rfl :
      _ ≤ sm act M T) ⟨_, hm, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ProjectiveLineTwo
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system.ProjectiveLineTwo

variable {E : Type} [AddCommGroup E] [Module ℂ E]

private lemma mem_acxC {σ : Type} [LinearOrder σ] (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E)
    (n : ℤ) (c : Finset σ → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) := by
  show c ∈ Submodule.pi Set.univ _ ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]

private lemma val_zero {σ : Type} [LinearOrder σ] {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {n : ℤ} {c : Finset σ → E} (h : c ∈ (acx A w).C n) (s : Finset σ) (hs : (s.card : ℤ) ≠ n) : c s = 0 := by
  have := (mem_acxC A w n c).1 h s
  rw [if_neg hs] at this
  simpa using this

private lemma val_mem {σ : Type} [LinearOrder σ] {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {n : ℤ} {c : Finset σ → E} (h : c ∈ (acx A w).C n) (s : Finset σ) (hs : (s.card : ℤ) = n) : c s ∈ A s := by
  have := (mem_acxC A w n c).1 h s
  rwa [if_pos hs] at this

private lemma wd_apply' {σ : Type} [LinearOrder σ] (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private lemma wd_congr' {σ : Type} [LinearOrder σ] (w : σ → Module.End ℂ E) (c c' : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, c (t.erase i) = c' (t.erase i)) : wd w c t = wd w c' t := by
  rw [wd_apply', wd_apply']
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

private lemma wd_zero' {σ : Type} [LinearOrder σ] (c : Finset σ → E) (t : Finset σ) :
    wd (fun _ => (0 : Module.End ℂ E)) c t = 0 := by
  rw [wd_apply']
  simp

private lemma inter_card {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (s : Finset (β ⊕ₗ κ)) :
    (s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = (rgt s).card := by
  have h : s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding = (rgt s).map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
    ext t
    obtain ⟨t, rfl⟩ := toLex.surjective t
    rcases t with t | t <;> simp [rgt, inrE]
  rw [h, Finset.card_map]

end UpperTheory.Gal.productCup_of_system.ProjectiveLineTwo

open UpperTheory.Gal.productCup_of_system.ProjectiveLineTwo in
theorem UpperTheory.Gal.productCup_of_system.localTwo_of_gl2 :
    FiltrationCocycleLiftCriterion → ColQEx → WdUni → L2 := by
  intro hG hC hU β κ E _ _ _ _ _ _ A w d n hW hK c0 hZ hB
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := ⟨_, rfl⟩
  have hQex : QEx A w Q d := by rw [hQ]; exact hC β κ E A w d hK
  have hcap : ∀ s : Finset (β ⊕ₗ κ), (s ∩ Q).card = (rgt s).card := fun s => by rw [hQ]; exact inter_card s
  have hinl : ∀ i : β, (inlE i : β ⊕ₗ κ) ∉ Q := fun i => by simp [hQ, inlE, inrE]
  have hinr : ∀ l : κ, (inrE l : β ⊕ₗ κ) ∈ Q := fun l => by simp [hQ]
  have hl : ∀ (b : Finset β) (L : Finset κ), lft (uni b L) = b := fun b L => (hU β κ E w 0 b L).2.1
  have hr : ∀ (b : Finset β) (L : Finset κ), rgt (uni b L) = L := fun b L => (hU β κ E w 0 b L).2.2.1
  have hcd : ∀ (b : Finset β) (L : Finset κ), (uni b L).card = b.card + L.card :=
    fun b L => (hU β κ E w 0 b L).2.2.2.1
  have hs : ∀ s : Finset (β ⊕ₗ κ), uni (lft s) (rgt s) = s := (hU β κ E w 0 ∅ ∅).2.2.2.2
  have hsc : ∀ s : Finset (β ⊕ₗ κ), s.card = (lft s).card + (rgt s).card := fun s => by
    conv_lhs => rw [← hs s]
    exact hcd _ _
  have wdQ : ∀ (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ), wd (wOn Q w) c (uni b L) =
      ((-1 : ℤ) ^ b.card) • wd (fun l => w (inrE l)) (fun L' => c (uni b L')) L := by
    intro c b L
    rw [(hU β κ E (wOn Q w) c b L).1]
    have h1 : (fun i => wOn Q w (inlE i)) = fun _ => (0 : Module.End ℂ E) := by
      funext i; simp [wOn, hinl]
    have h2 : (fun l => wOn Q w (inrE l)) = fun l => w (inrE l) := by
      funext l; simp [wOn, hinr]
    rw [h1, h2, wd_zero', zero_add]
  have wdQc : ∀ (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ), wd (wOn Qᶜ w) c (uni b L) =
      wd (fun i => w (inlE i)) (fun b' => c (uni b' L)) b := by
    intro c b L
    rw [(hU β κ E (wOn Qᶜ w) c b L).1]
    have h1 : (fun i => wOn Qᶜ w (inlE i)) = fun i => w (inlE i) := by
      funext i; simp [wOn, hinl]
    have h2 : (fun l => wOn Qᶜ w (inrE l)) = fun _ => (0 : Module.End ℂ E) := by
      funext l; simp [wOn, hinr]
    rw [h1, h2, wd_zero', smul_zero, add_zero]
  have hc0 : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d → (L.card : ℤ) ≠ d → c0 b L = 0 :=
    fun b L hb hL => val_zero (Submodule.mem_inf.1 (hZ b hb)).1 L hL
  have hc0m : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d → (L.card : ℤ) = d → c0 b L ∈ A (uni b L) :=
    fun b L hb hL => val_mem (Submodule.mem_inf.1 (hZ b hb)).1 L hL
  let c' : Finset (β ⊕ₗ κ) → E := fun s => if ((lft s).card : ℤ) = n - d then c0 (lft s) (rgt s) else 0
  have hcu : ∀ (b : Finset β) (L : Finset κ), c' (uni b L) = if (b.card : ℤ) = n - d then c0 b L else 0 := by
    intro b L; simp only [c', hl, hr]
  have hc'C : c' ∈ (acx A w).C n := by
    rw [mem_acxC]
    intro s
    have hcs := hsc s
    by_cases hsn : (s.card : ℤ) = n
    · rw [if_pos hsn]
      simp only [c']
      split_ifs with hb
      · have := hc0m (lft s) (rgt s) hb (by omega)
        rwa [hs] at this
      · exact zero_mem _
    · rw [if_neg hsn]
      simp only [c']
      split_ifs with hb
      · rw [hc0 _ _ hb (by omega)]; exact zero_mem _
      · exact zero_mem _
  have hc'L : Lev Q (· = d) c' := by
    intro s hs'
    rw [hcap] at hs'
    simp only [c']
    split_ifs with hb
    · exact hc0 _ _ hb hs'
    · rfl
  have hQ0 : wd (wOn Q w) c' = 0 := by
    funext s
    obtain ⟨b, L, rfl⟩ : ∃ b L, s = uni b L := ⟨_, _, (hs s).symm⟩
    rw [wdQ]
    simp only [hcu]
    by_cases hb : (b.card : ℤ) = n - d
    · simp only [if_pos hb]
      have h0 : wd (fun l => w (inrE l)) (c0 b) = 0 := (Submodule.mem_inf.1 (hZ b hb)).2
      have h1 : (fun L' => c0 b L') = c0 b := rfl
      rw [h1, h0]; simp
    · simp only [if_neg hb]
      have h1 : (fun _ : Finset κ => (0 : E)) = 0 := rfl
      rw [h1, map_zero]; simp
  have hy : ∀ b : Finset β, ∃ y : Finset κ → E, (b.card : ℤ) = n - d + 1 →
      y ∈ (colA A w b).C (d - 1) ∧
        wd (fun l => w (inrE l)) y = fun L => wd (fun i => w (inlE i)) (fun b' => c0 b' L) b := by
    intro b
    by_cases hb : (b.card : ℤ) = n - d + 1
    · obtain ⟨y, hy1, hy2⟩ := hB b hb
      exact ⟨y, fun _ => ⟨hy1, hy2⟩⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose yb hyb using hy
  let y : Finset (β ⊕ₗ κ) → E := fun s =>
    if ((lft s).card : ℤ) = n - d + 1 then ((-1 : ℤ) ^ (lft s).card) • yb (lft s) (rgt s) else 0
  have hyu : ∀ (b : Finset β) (L : Finset κ), y (uni b L) =
      if (b.card : ℤ) = n - d + 1 then ((-1 : ℤ) ^ b.card) • yb b L else 0 := by
    intro b L; simp only [y, hl, hr]
  have hyz : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d + 1 → (L.card : ℤ) ≠ d - 1 → yb b L = 0 :=
    fun b L hb hL => val_zero (hyb b hb).1 L hL
  have hym : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d + 1 → (L.card : ℤ) = d - 1 →
      yb b L ∈ A (uni b L) := fun b L hb hL => val_mem (hyb b hb).1 L hL
  have hyC : y ∈ (acx A w).C n := by
    rw [mem_acxC]
    intro s
    have hcs := hsc s
    by_cases hsn : (s.card : ℤ) = n
    · rw [if_pos hsn]
      simp only [y]
      split_ifs with hb
      · have := hym (lft s) (rgt s) hb (by omega)
        rw [hs] at this
        exact (A s).smul_of_tower_mem _ this
      · exact zero_mem _
    · rw [if_neg hsn]
      simp only [y]
      split_ifs with hb
      · rw [hyz _ _ hb (by omega), smul_zero]; exact zero_mem _
      · exact zero_mem _
  have hyL : Lev Q (· = d - 1) y := by
    intro s hs'
    rw [hcap] at hs'
    simp only [y]
    split_ifs with hb
    · rw [hyz _ _ hb hs', smul_zero]
    · rfl
  have hyE : wd (wOn Q w) y = wd (wOn Qᶜ w) c' := by
    funext s
    obtain ⟨b, L, rfl⟩ : ∃ b L, s = uni b L := ⟨_, _, (hs s).symm⟩
    rw [wdQ, wdQc]
    by_cases hb : (b.card : ℤ) = n - d + 1
    · have h1 : (fun L' => y (uni b L')) = ((-1 : ℤ) ^ b.card) • yb b := by
        funext L'; rw [hyu, if_pos hb]; rfl
      rw [h1, map_zsmul, Pi.smul_apply, smul_smul, (hyb b hb).2, ← mul_pow]
      simp only [neg_mul, one_mul, neg_neg, one_pow, one_smul]
      refine wd_congr' _ _ _ _ fun i hi => ?_
      rw [hcu, if_pos]
      rw [Finset.card_erase_of_mem hi]
      have : 0 < b.card := Finset.card_pos.2 ⟨i, hi⟩
      omega
    · have h1 : (fun L' => y (uni b L')) = 0 := by
        funext L'; rw [hyu, if_neg hb]; rfl
      rw [h1, map_zero, Pi.zero_apply, smul_zero]
      symm
      have h2 : wd (fun i => w (inlE i)) (fun b' => c' (uni b' L)) b = wd (fun i => w (inlE i)) 0 b := by
        refine wd_congr' _ _ _ _ fun i hi => ?_
        rw [hcu, if_neg, Pi.zero_apply]
        rw [Finset.card_erase_of_mem hi]
        have : 0 < b.card := Finset.card_pos.2 ⟨i, hi⟩
        omega
      rw [h2, map_zero, Pi.zero_apply]
  obtain ⟨c, hcZ, hcl⟩ := hG (β ⊕ₗ κ) E A w Q d n hW hQex c' hc'C hc'L hQ0 ⟨y, hyC, hyL, hyE⟩
  have hcC : c ∈ (acx A w).C n := (Submodule.mem_inf.1 hcZ).1
  have hlev : ∀ (b : Finset β) (L : Finset κ), d ≤ (L.card : ℤ) → c (uni b L) = c' (uni b L) := by
    intro b L hL
    have := hcl (uni b L) (by
      intro h
      beta_reduce at h
      have h' : (((uni b L ∩ Q).card : ℕ) : ℤ) < d := by convert h
      rw [hcap, hr] at h'
      omega)
    exact sub_eq_zero.1 this
  refine ⟨c, hcZ, ?_, ?_⟩
  · intro b hb
    funext L
    show c (uni b L) = c0 b L
    by_cases hL : d ≤ (L.card : ℤ)
    · rw [hlev b L hL, hcu, if_pos hb]
    · rw [val_zero hcC _ (by rw [hcd]; push_cast; omega), hc0 b L hb (by omega)]
  · intro b L hL
    rw [hlev b L hL.le, hcu]
    split_ifs with hb
    · exact hc0 b L hb (by omega)
    · rfl
end
