module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PThMuLat
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma det_form {S : Type} [CommRing S] [Algebra ℂ S] (R : Subalgebra ℂ S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (P I : Finset (Fin n)) (f : Fin n → Fin n) (D : Fin n → S) (w : S)
    (t : Fin n → Fin n → S)
    (hP : ∀ a ∈ P, ∀ m, A a m = if m = f a then 1 else 0)
    (hI : ∀ a ∈ P, f a ∈ I)
    (hI' : ∀ m ∈ I, ∃ a ∈ P, f a = m)
    (hA : ∀ a, a ∉ P → ∀ m, m ∉ I → A a m = D m * w * t a m)
    (ht : ∀ a m, t a m ∈ R) :
    ∃ s ∈ R, A.det = s * (∏ m ∈ Iᶜ, D m) * w ^ (Pᶜ).card := by
  refine ⟨∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : S) *
      ((∏ a ∈ P, A a (σ a)) * ∏ a ∈ Pᶜ, t a (σ a)), ?_, ?_⟩
  · refine Subalgebra.sum_mem _ (fun σ _ => Subalgebra.mul_mem _ (intCast_mem R _)
      (Subalgebra.mul_mem _ (Subalgebra.prod_mem _ (fun a ha => ?_)) (Subalgebra.prod_mem _ (fun a _ => ht _ _))))
    rw [hP a ha]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  · rw [← Matrix.det_transpose, Matrix.det_apply', Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Matrix.transpose_apply]
    rw [← Finset.prod_mul_prod_compl P]
    by_cases hσ : ∀ a ∈ P, σ a = f a
    · have hout : ∀ a ∉ P, σ a ∉ I := by
        intro a ha hm
        obtain ⟨b, hb, hfb⟩ := hI' _ hm
        have hba : σ b = σ a := by rw [hσ b hb, hfb]
        apply ha
        rw [← σ.injective hba]
        exact hb
      have hD : ∏ a ∈ Pᶜ, D (σ a) = ∏ m ∈ Iᶜ, D m := by
        refine Finset.prod_nbij σ (fun a ha => Finset.mem_compl.2 (hout a (Finset.mem_compl.1 ha)))
          (fun a _ b _ hab => σ.injective hab) ?_ (fun a _ => rfl)
        intro m hm
        have hm' : m ∉ I := Finset.mem_compl.1 hm
        refine ⟨σ.symm m, Finset.mem_coe.2 (Finset.mem_compl.2 (fun hp => ?_)), σ.apply_symm_apply m⟩
        have h1 := hσ _ hp
        rw [σ.apply_symm_apply] at h1
        exact hm' (h1 ▸ hI _ hp)
      have hprod : ∏ a ∈ Pᶜ, A a (σ a) = (∏ m ∈ Iᶜ, D m) * w ^ Pᶜ.card * ∏ a ∈ Pᶜ, t a (σ a) := by
        rw [Finset.prod_congr rfl (fun a ha => hA a (Finset.mem_compl.1 ha) (σ a) (hout a (Finset.mem_compl.1 ha)))]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, hD]
      rw [hprod]
      ring
    · push_neg at hσ
      obtain ⟨a, ha, hne⟩ := hσ
      have h0 : ∏ a ∈ P, A a (σ a) = 0 := Finset.prod_eq_zero ha (by rw [hP a ha, if_neg hne])
      rw [h0]
      ring

theorem UpperTheory.Gal.productCup_of_system.thMuLat_of :
    ThMuLat := by
  unfold ThMuLat
  intro d S E _ _ _ _ T hT
  refine ⟨?_, ?_⟩
  · unfold Sys.admitted
    intro i j l
    have hx : ∀ a, ((T.X a * (T.X i)⁻¹ : Sˣ) : S) ∈ T.R {i} {j} := fun a =>
      hT.memX {i} {j} (Finset.singleton_nonempty j) i (Finset.mem_singleton_self i) a
    have hy : ∀ a, ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) ∈ T.R {i} {j} := fun a =>
      hT.memY {i} {j} (Finset.singleton_nonempty i) j (Finset.mem_singleton_self j) a
    have key := sub_mem (mul_mem (hx (ofLex l).1) (hy (ofLex l).2))
      (mul_mem (hx (ofLex l).2) (hy (ofLex l).1))
    simp only [Units.val_mul] at key
    convert key using 1
    simp only [Sys.r, Sys.u, Sys.mu, n11, pow_one, mul_inv, Units.val_mul]
    ring
  · intro I J L hI j hj
    unfold detC
    by_cases h : (uni I L).card = d + 1
    · classical
      rw [dite_eq_left h]
      set e := (uni I L).orderEmbOfFin h with he
      have mem_e : ∀ a, e a ∈ uni I L := fun a => Finset.orderEmbOfFin_mem _ h a
      have mem_l : ∀ i : Fin (d + 1), (toLex (Sum.inl i : Fin (d + 1) ⊕ Mi d) ∈ uni I L) ↔ i ∈ I := by
        intro i
        simp [uni]
      have inl_mem : ∀ a i, ofLex (e a) = Sum.inl i → i ∈ I := by
        intro a i hai
        have h2 : e a = toLex (Sum.inl i) := by rw [← hai]; rfl
        exact (mem_l i).1 (h2 ▸ mem_e a)
      obtain ⟨P, hPm⟩ : ∃ P : Finset (Fin (d + 1)), ∀ a, a ∈ P ↔ ∃ i, ofLex (e a) = Sum.inl i :=
        ⟨Finset.univ.filter fun a => ∃ i, ofLex (e a) = Sum.inl i, fun a => by simp⟩
      obtain ⟨f, hf⟩ : ∃ f : Fin (d + 1) → Fin (d + 1), ∀ a i, ofLex (e a) = Sum.inl i → f a = i :=
        ⟨fun a => Sum.elim id (fun _ => 0) (ofLex (e a)), fun a i hai => by simp [hai]⟩
      have hfI : ∀ a ∈ P, f a ∈ I := by
        intro a ha
        obtain ⟨i, hi⟩ := (hPm a).1 ha
        rw [hf a i hi]
        exact inl_mem a i hi
      have hIf : ∀ m ∈ I, ∃ a ∈ P, f a = m := by
        intro m hm
        have hr : toLex (Sum.inl m : Fin (d + 1) ⊕ Mi d) ∈ Set.range e := by
          rw [he, Finset.range_orderEmbOfFin]
          exact (mem_l m).2 hm
        obtain ⟨a, ha⟩ := hr
        have ha' : ofLex (e a) = Sum.inl m := by rw [ha]; rfl
        exact ⟨a, (hPm a).2 ⟨m, ha'⟩, hf a m ha'⟩
      have hPcard : P.card = I.card := by
        refine Finset.card_nbij f hfI ?_ (fun m hm => ?_)
        · intro a ha b hb hab
          obtain ⟨i, hi⟩ := (hPm a).1 ha
          obtain ⟨i', hi'⟩ := (hPm b).1 hb
          rw [hf a i hi, hf b i' hi'] at hab
          apply e.injective
          have h1 : e a = toLex (Sum.inl i) := by rw [← hi]; rfl
          have h2 : e b = toLex (Sum.inl i') := by rw [← hi']; rfl
          rw [h1, h2, hab]
        · obtain ⟨a, ha, hfa⟩ := hIf m hm
          exact ⟨a, ha, hfa⟩
      have hcard : Pᶜ.card = L.card := by
        have hu : (uni I L).card = I.card + L.card := by simp [uni]
        rw [Finset.card_compl, Fintype.card_fin, hPcard]
        omega
      have hu := Units.mul_inv (T.Y j)
      have hsplit : ∀ (c1 c2 : Prop) [Decidable c1] [Decidable c2] (x y1 y2 : S),
          ((if c1 then x * y1 else 0) - if c2 then x * y2 else 0) =
            x * ((if c1 then y1 else 0) - if c2 then y2 else 0) := by
        intros
        split_ifs <;> ring
      obtain ⟨s, hs, hdet⟩ := det_form (T.R I J) (Matrix.of fun a b => T.rowMu (e a) b) P I f
        (fun m => (T.X m : S)) (T.Y j : S)
        (fun a m => Sum.elim (fun _ => (0 : S)) (fun l => ((if m = (ofLex l).1 then (T.Y (ofLex l).2 : S) else 0) -
          if m = (ofLex l).2 then (T.Y (ofLex l).1 : S) else 0) * (((T.Y j)⁻¹ : Sˣ) : S)) (ofLex (e a)))
        (by
          intro a ha m
          obtain ⟨i, hi⟩ := (hPm a).1 ha
          simp only [Matrix.of_apply, Sys.rowMu, hi, Sum.elim_inl, Pi.single_apply, hf a i hi])
        hfI hIf
        (by
          intro a ha m hm
          rcases hx : ofLex (e a) with i | l
          · exact absurd ((hPm a).2 ⟨i, hx⟩) ha
          · simp only [Matrix.of_apply, Sys.rowMu, hx, Sum.elim_inr]
            rw [hsplit]
            linear_combination (-((T.X m : S) * ((if m = (ofLex l).1 then (T.Y (ofLex l).2 : S) else 0) -
              if m = (ofLex l).2 then (T.Y (ofLex l).1 : S) else 0))) * hu)
        (by
          intro a m
          rcases hx : ofLex (e a) with i | l
          · simp only [hx, Sum.elim_inl]
            exact zero_mem _
          · simp only [hx, Sum.elim_inr, sub_mul, ite_mul, zero_mul]
            rw [← Units.val_mul, ← Units.val_mul]
            refine sub_mem ?_ ?_
            · split_ifs
              · exact hT.memY I J hI j hj _
              · exact zero_mem _
            · split_ifs
              · exact hT.memY I J hI j hj _
              · exact zero_mem _)
      beta_reduce at hdet
      refine ⟨s, hs, ?_⟩
      rw [hdet, hcard]
    · rw [dite_eq_right h]
      exact ⟨0, zero_mem _, by ring⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PEdgeInj
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma wd_apply' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private lemma wd_one_eq {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (c : Finset ι → E) : wd (fun _ => (1 : Module.End ℂ E)) c = deltaL ℂ ι E c := by
  funext t
  rw [wd_apply']
  simp [deltaL, GlobalTheory.DI.delta]

private lemma wd_tail {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (v : E) (L : Finset ι)
    (hL : L.Nonempty) :
    wd (fun _ => (1 : Module.End ℂ E)) (fun L' : Finset ι => if L' = ∅ then v else 0) L =
      if L.card = 1 then v else 0 := by
  rw [wd_apply']
  split_ifs with h
  · obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h
    simp [GlobalTheory.cubeSign, Finset.filter_singleton]
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : L.erase i ≠ ∅ := by
      intro h0
      apply h
      have := Finset.card_erase_of_mem hi
      rw [h0, Finset.card_empty] at this
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [this]

theorem UpperTheory.Gal.productCup_of_system.edgeInj_of :
    WdUni → EdgeInj := by
  intro hU ι E _ _ _ _ G d x hx hB
  obtain ⟨y, hyC, hy⟩ := hB
  have hxC := hx.1
  have hxd : deltaL ℂ ι E x = 0 := hx.2
  have hy' : wd (fun _ => (1 : Module.End ℂ E)) y = edge1 x := hy
  have hyC' : ∀ s, y s ∈ (if (s.card : ℤ) = ((d : ℤ) + 2 - 1) then
      mixF (fun I J => G (uni I J)) s else ⊥) := fun s => hyC s (Set.mem_univ s)
  have hxC' : ∀ I, x I ∈ (if I.Nonempty ∧ (I.card : ℤ) = (d : ℤ) + 1 then G (uni I ∅) else ⊥) :=
    fun I => hxC I (Set.mem_univ I)
  have hUn := hU ι ι E (fun _ => 1)
  have hl : ∀ (b L : Finset ι), lft (uni b L) = b := fun b L => (hUn y b L).2.1
  have hr : ∀ (b L : Finset ι), rgt (uni b L) = L := fun b L => (hUn y b L).2.2.1
  have hc : ∀ (b L : Finset ι), (uni b L).card = b.card + L.card := fun b L => (hUn y b L).2.2.2.1
  have hs : ∀ s : Finset (ι ⊕ₗ ι), uni (lft s) (rgt s) = s := (hUn y ∅ ∅).2.2.2.2
  have hx0 : ∀ I : Finset ι, (I.card : ℤ) ≠ (d : ℤ) + 1 → x I = 0 := by
    intro I hI
    have := hxC' I
    rw [if_neg (fun h => hI h.2)] at this
    simpa using this
  have hy0 : ∀ s, ¬ ((lft s).Nonempty ∧ (rgt s).Nonempty) → y s = 0 := by
    intro s h
    have := hyC' s
    split_ifs at this
    · simpa [mixF, h] using this
    · simpa using this
  let e : Finset (ι ⊕ₗ ι) → E := fun s => if rgt s = ∅ then x (lft s) else 0
  have he : ∀ b L, e (uni b L) = if L = ∅ then x b else 0 := by
    intro b L
    simp only [e, hl, hr]
  have hwe : ∀ s, wd (fun _ => (1 : Module.End ℂ E)) e s = (-((-1 : ℤ) ^ d)) • edge1 x s := by
    intro s
    rw [← hs s]
    generalize lft s = b
    generalize rgt s = L
    have h1 := (hU ι ι E (fun _ => 1) e b L).1
    simp only [he] at h1
    rw [h1]
    by_cases hL : L = ∅
    · subst hL
      have : edge1 (κ := ι) x (uni b ∅) = 0 := by simp [edge1, hr]
      rw [this, smul_zero]
      have hd : wd (fun _ => (1 : Module.End ℂ E)) x = 0 := by rw [wd_one_eq, hxd]
      have e1 : (fun b' : Finset ι => if (∅ : Finset ι) = ∅ then x b' else 0) = x := by
        funext b'
        simp
      rw [e1, hd]
      simp [wd_apply']
    · have hLn : L.Nonempty := Finset.nonempty_iff_ne_empty.2 hL
      simp only [hL, if_false]
      have h0 : wd (fun _ => (1 : Module.End ℂ E)) (fun _ : Finset ι => (0 : E)) b = 0 := by
        simp [wd_apply']
      have h2 := wd_tail (x b) L hLn
      rw [h0, h2, zero_add]
      simp only [edge1, hl, hr]
      split_ifs with h1c
      · by_cases hb : (b.card : ℤ) = (d : ℤ) + 1
        · have hb' : b.card = d + 1 := by exact_mod_cast hb
          rw [hb', pow_succ]
          simp
        · simp [hx0 b hb]
      · simp
  refine ⟨e + ((-1 : ℤ) ^ d) • y, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro s _
    change (e + ((-1 : ℤ) ^ d) • y) s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (d : ℤ) + 1 then G s else ⊥)
    by_cases hr0 : rgt s = ∅
    · have hys : y s = 0 := hy0 s (fun h => h.2.ne_empty hr0)
      have hs' : uni (lft s) ∅ = s := by
        have := hs s
        rwa [hr0] at this
      have hcard : s.card = (lft s).card := by
        have := hc (lft s) ∅
        rw [hs'] at this
        simpa using this
      have hval : (e + ((-1 : ℤ) ^ d) • y) s = x (lft s) := by
        simp [e, hr0, hys]
      rw [hval]
      split_ifs with h
      · have := hxC' (lft s)
        have hlc : ((lft s).card : ℤ) = (d : ℤ) + 1 := by rw [← hcard]; exact h.2
        have hne : (lft s).Nonempty := by
          apply Finset.card_pos.1
          omega
        rw [if_pos ⟨hne, hlc⟩, hs'] at this
        exact this
      · have : x (lft s) = 0 := by
          apply hx0
          intro hlc
          apply h
          have hsc : (s.card : ℤ) = (d : ℤ) + 1 := by rw [hcard]; exact hlc
          refine ⟨Finset.card_pos.1 ?_, hsc⟩
          omega
        simp [this]
    · have hval : (e + ((-1 : ℤ) ^ d) • y) s = ((-1 : ℤ) ^ d) • y s := by
        simp [e, hr0]
      rw [hval]
      by_cases hcs : (s.card : ℤ) = (d : ℤ) + 2 - 1
      · by_cases hlr : (lft s).Nonempty ∧ (rgt s).Nonempty
        · have := hyC' s
          rw [if_pos hcs] at this
          simp only [mixF, if_pos hlr, hs s] at this
          have hsc : (s.card : ℤ) = (d : ℤ) + 1 := by omega
          rw [if_pos ⟨Finset.card_pos.1 (by omega), hsc⟩]
          exact zsmul_mem this _
        · simp [hy0 s hlr]
      · have := hyC' s
        rw [if_neg hcs] at this
        have h0 : y s = 0 := by simpa using this
        simp [h0]
  · change deltaL ℂ (ι ⊕ₗ ι) E (e + ((-1 : ℤ) ^ d) • y) = 0
    rw [← wd_one_eq, map_add (f := _), map_zsmul, hy']
    funext s
    simp [hwe]
  · intro J
    have h1 : y (uni ∅ J) = 0 := hy0 _ (fun h => by
      have := h.1
      rw [hl] at this
      simp at this)
    have h2 : x ∅ = 0 := hx0 ∅ (by simp; omega)
    simp [he, h1, h2]
  · intro I
    have h1 : y (uni I ∅) = 0 := hy0 _ (fun h => by
      have := h.2
      rw [hr] at this
      simp at this)
    simp [he, h1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.EuclideanHeightMul
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.productCup_of_system

section SlopeTestRemainingChoices

variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)

@[reducible] private def modR (h : Stab act R M) : Module R M where
  smul r m := ⟨act r m, h r r.2 m m.2⟩
  one_smul m := Subtype.ext (by
    change act ((1 : R) : S) (m : E) = m
    simp)
  mul_smul a b m := Subtype.ext (by
    change act ((a * b : R) : S) (m : E) = act a (act b m)
    simp [Module.End.mul_apply])
  smul_zero a := Subtype.ext (by
    change act a ((0 : M) : E) = 0
    simp)
  smul_add a m m' := Subtype.ext (by
    change act a ((m + m' : M) : E) = act a m + act a m'
    simp)
  add_smul a b m := Subtype.ext (by
    change act ((a + b : R) : S) (m : E) = act a m + act b m
    simp)
  zero_smul m := Subtype.ext (by
    change act ((0 : R) : S) (m : E) = 0
    simp)

variable {act R M}

private theorem mem_ofList_iff [Module R M] [IsScalarTower ℂ R M] (hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m)
    {d : ℕ} (f : Fin d → R) (k : ℕ) (x : M) :
    x ∈ (Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M) ↔
      (x : E) ∈ sm act M ((fun j => (f j : S)) '' {j | j.val < k}) := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha n _
      have : ∀ n : M, ((a • n : M) : E) ∈ sm act M ((fun j => (f j : S)) '' {j | j.val < k}) := by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
        · intro b hb n
          obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 hb
          have hi' : i < k := lt_of_lt_of_le hi (min_le_left _ _)
          have hid : i < d := by
            have := lt_of_lt_of_le hi (min_le_right _ _)
            simpa using this
          rw [hsm]
          refine Submodule.mem_iSup_of_mem ((f ⟨i, hid⟩ : S)) (Submodule.mem_iSup_of_mem
            ⟨⟨i, hid⟩, hi', rfl⟩ ?_)
          simpa using ⟨n, n.2, rfl⟩
        · intro n
          simp
        · intro a b _ _ ha hb n
          rw [add_smul]
          simpa using Submodule.add_mem _ (ha n) (hb n)
        · intro a b _ hb n
          rw [smul_eq_mul, mul_comm, mul_smul]
          exact hb (a • n)
      exact this n
    · intro a b ha hb
      simpa using Submodule.add_mem _ ha hb
  · intro hx
    have hle : sm act M ((fun j => (f j : S)) '' {j | j.val < k}) ≤
        ((Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M).restrictScalars ℂ).map M.subtype := by
      refine iSup₂_le ?_
      rintro _ ⟨j, hj, rfl⟩ _ ⟨m, hm, rfl⟩
      have hmem : f j • (⟨m, hm⟩ : M) ∈ (Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M) := by
        refine Submodule.smul_mem_smul (Ideal.subset_span ?_) Submodule.mem_top
        refine List.mem_take_iff_getElem.2 ⟨j.val, ?_, by simp⟩
        simpa using hj
      exact Submodule.mem_map.2 ⟨_, (Submodule.restrictScalars_mem ℂ _ _).2 hmem, hsm _ _⟩
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (hle hx)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact (Submodule.restrictScalars_mem ℂ _ _).1 hy

private theorem wd_coe [Module R M] [IsScalarTower ℂ R M]
    (hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m) {κ : Type} [LinearOrder κ] (r : κ → R)
    (c : Finset κ → M) (t : Finset κ) :
    ((wd (fun l => Algebra.lsmul ℂ ℂ M (r l)) c t : M) : E) =
      wd (fun l => act (r l)) (fun s => (c s : E)) t := by
  simp [wd, hsm]

private theorem koszulExact_of_regular (hK : KoszulExactBelowLengthOfWeaklyRegular) {κ : Type} [LinearOrder κ] [Fintype κ] (r : κ → S) {d : ℕ}
    (f : Fin d → S) (hS : Stab act R M) (hr : ∀ l, r l ∈ R) (hReg : Reg act M f)
    (hf : ∀ j, InSp R r (f j)) : KE (kos act M r) d := by
  letI := modR act R M hS
  have hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m := fun _ _ => rfl
  haveI : IsScalarTower ℂ R M := ⟨fun c a m => Subtype.ext (by
    change act ((c • a : R) : S) (m : E) = c • act a m
    simp)⟩
  have hfR : ∀ j, f j ∈ R := by
    intro j
    obtain ⟨a, ha, h⟩ := hf j
    rw [h]
    exact sum_mem fun l _ => R.mul_mem (ha l) (hr l)
  let r' : κ → R := fun l => ⟨r l, hr l⟩
  let f' : Fin d → R := fun j => ⟨f j, hfR j⟩
  have hreg : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f') := by
    refine ⟨fun i hi => ?_⟩
    have hid : i < d := by simpa using hi
    rw [isSMulRegular_on_quot_iff_lsmul_comap_le]
    intro x hx
    rw [Submodule.mem_comap, LinearMap.lsmul_apply, mem_ofList_iff hsm] at hx
    rw [mem_ofList_iff hsm]
    have hget : (List.ofFn f')[i] = f' ⟨i, hid⟩ := by simp
    rw [hget, hsm] at hx
    exact hReg ⟨i, hid⟩ x x.2 hx
  have hsp : ∀ g ∈ List.ofFn f', InSp (⊤ : Subalgebra ℂ R) r' g := by
    intro g hg
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    obtain ⟨a, ha, h⟩ := hf j
    refine ⟨fun l => ⟨a l, ha l⟩, fun _ => trivial, Subtype.ext ?_⟩
    simpa [f', r'] using h
  have key := hK d R M κ r' (List.ofFn f') (by simp) hreg hsp
  intro m hm c hc
  obtain ⟨hcC, hcD⟩ := hc
  have hcM : ∀ s, c s ∈ M := by
    intro s
    have : c s ∈ if (s.card : ℤ) = m then M else ⊥ := hcC s (Set.mem_univ s)
    split_ifs at this with h
    · exact this
    · rw [Submodule.mem_bot] at this
      exact this ▸ M.zero_mem
  let c' : Finset κ → M := fun s => ⟨c s, hcM s⟩
  have hc' : c' ∈ (kos (Algebra.lsmul ℂ ℂ M) (⊤ : Submodule ℂ M) r').Z m := by
    constructor
    · intro s _
      have : c s ∈ if (s.card : ℤ) = m then M else ⊥ := hcC s (Set.mem_univ s)
      change c' s ∈ if (s.card : ℤ) = m then (⊤ : Submodule ℂ M) else ⊥
      split_ifs at this ⊢ with h
      · trivial
      · rw [Submodule.mem_bot] at this ⊢
        exact Subtype.ext this
    · refine LinearMap.mem_ker.2 (funext fun t => Subtype.ext ?_)
      have := wd_coe hsm r' c' t
      exact this.trans (congrFun (LinearMap.mem_ker.1 hcD) t)
  obtain ⟨y, hy, hyc⟩ := key m hm hc'
  refine ⟨fun s => (y s : E), ?_, ?_⟩
  · intro s _
    have : y s ∈ if (s.card : ℤ) = m - 1 then (⊤ : Submodule ℂ M) else ⊥ := hy s (Set.mem_univ s)
    change (y s : E) ∈ if (s.card : ℤ) = m - 1 then M else ⊥
    split_ifs at this ⊢ with h
    · exact (y s).2
    · rw [Submodule.mem_bot] at this ⊢
      rw [this]
      rfl
  · funext t
    have h1 := wd_coe hsm r' y t
    have h2 : ((wd (fun l => Algebra.lsmul ℂ ℂ M (r' l)) y t : M) : E) = c t :=
      congrArg (fun z : Finset κ → M => ((z t : M) : E)) hyc
    exact h1.symm.trans h2

end SlopeTestRemainingChoices

end UpperTheory.Gal.productCup_of_system

end

theorem UpperTheory.Gal.productCup_of_system.firstCohomologyBound_of_boundaryBound :
    KoszulExactBelowLengthOfWeaklyRegular → K1 := by
  intro hK S E _ _ _ _ act κ _ _ R M r d f hS hr hReg hf
  exact koszulExact_of_regular hK r f hS hr hReg hf
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PSysOk
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section SlopeTestRemainingChoices

private lemma mem_lft' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (s : Finset (ι ⊕ₗ κ)) (a : ι) :
    a ∈ lft s ↔ toLex (Sum.inl a) ∈ s := by
  simp [lft, Finset.mem_toLeft]

private lemma mem_rgt' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (s : Finset (ι ⊕ₗ κ)) (a : κ) :
    a ∈ rgt s ↔ toLex (Sum.inr a) ∈ s := by
  simp [rgt, Finset.mem_toRight]

private lemma lft_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s s' : Finset (ι ⊕ₗ κ)} (h : s ⊆ s') :
    lft s ⊆ lft s' := fun a ha => (mem_lft' _ _).2 (h ((mem_lft' _ _).1 ha))

private lemma rgt_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s s' : Finset (ι ⊕ₗ κ)} (h : s ⊆ s') :
    rgt s ⊆ rgt s' := fun a ha => (mem_rgt' _ _).2 (h ((mem_rgt' _ _).1 ha))

private lemma pk_mem' {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  unfold pk
  rw [dite_eq_left h]
  exact Finset.min'_mem _ _

variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  {κ : Type} [LinearOrder κ]

private lemma u_quot (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (l : κ) :
    ((T.u n a b l * (T.u n a' b' l)⁻¹ : Sˣ) : S) ∈ T.R I J := by
  have e : T.u n a b l * (T.u n a' b' l)⁻¹ =
      (T.X a * (T.X a')⁻¹) ^ (n l).1 * (T.Y b * (T.Y b')⁻¹) ^ (n l).2 := by
    simp only [Sys.u, mul_inv, mul_pow, inv_pow]
    ac_rfl
  rw [e, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact mul_mem (pow_mem (hT.memX I J hJ a' ha' a) _) (pow_mem (hT.memY I J hI b' hb' b) _)

private lemma prod_quot (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (L : Finset κ) :
    (((∏ l ∈ L, T.u n a b l) * (∏ l ∈ L, T.u n a' b' l)⁻¹ : Sˣ) : S) ∈ T.R I J := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
  exact Subalgebra.prod_mem _ (fun l _ => u_quot T hT n hI hJ ha' hb' l)

private lemma lat_le (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n a b l : Sˣ) : S)) ≤
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n a' b' l : Sˣ) : S)) := by
  rintro y ⟨m, hm, rfl⟩
  have hr := prod_quot T hT n hI hJ (a := a) (b := b) ha' hb' L
  refine ⟨T.act (((∏ l ∈ L, T.u n a b l) * (∏ l ∈ L, T.u n a' b' l)⁻¹ : Sˣ) : S) m,
    hT.stab I J hI hJ _ hr m hm, ?_⟩
  rw [← Module.End.mul_apply, ← map_mul, ← Units.val_mul, mul_comm (∏ l ∈ L, T.u n a b l),
    mul_inv_cancel_left]

private lemma lat_eq (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha : a ∈ I) (ha' : a' ∈ I) (hb : b ∈ J) (hb' : b' ∈ J) (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n a b l : Sˣ) : S)) =
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n a' b' l : Sˣ) : S)) :=
  le_antisymm (lat_le T hT n hI hJ ha' hb' L) (lat_le T hT n hI hJ ha hb L)

private lemma lat_mono (hT : T.Good) (n : κ → ℕ × ℕ) {I I' J J' : Finset (Fin (d + 1))} (hI : I.Nonempty)
    (hJ : J.Nonempty) (hII : I ⊆ I') (hJJ : J ⊆ J') (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) ≤
      (T.M I' J').map (T.act ((∏ l ∈ L, T.u n (pk I') (pk J') l : Sˣ) : S)) := by
  have hI' := Finset.Nonempty.mono hII hI
  have hJ' := Finset.Nonempty.mono hJJ hJ
  calc (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))
      ≤ (T.M I' J').map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) :=
        Submodule.map_mono (hT.monoM I I' J J' hI hJ hII hJJ)
    _ = _ := lat_eq T hT n hI' hJ' (hII (pk_mem' hI)) (pk_mem' hI') (hJJ (pk_mem' hJ)) (pk_mem' hJ') L

private lemma r_mem (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) (hA : T.admitted n z) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) (l : κ) : T.r n z i j l ∈ T.R I J :=
  hT.monoR {i} I {j} J (Finset.singleton_nonempty i) (Finset.singleton_nonempty j)
    (Finset.singleton_subset_iff.2 hi) (Finset.singleton_subset_iff.2 hj) (hA i j l)

private lemma col_eq (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) :
    T.colCx n z I J = kosT T.act (T.M I J) (T.u n i j) z := by
  unfold Sys.colCx kosT
  congr 1
  funext L
  exact lat_eq T hT n ⟨i, hi⟩ ⟨j, hj⟩ (pk_mem' ⟨i, hi⟩) hi (pk_mem' ⟨j, hj⟩) hj L

private lemma mix_mono (hT : T.Good) (n : κ → ℕ × ℕ) (L : Finset κ) {s s' : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1))}
    (hs : s ⊆ s') {m : E}
    (hm : m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s) :
    m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s' := by
  unfold mixF at hm ⊢
  by_cases h : (lft s).Nonempty ∧ (rgt s).Nonempty
  · have h' : (lft s').Nonempty ∧ (rgt s').Nonempty :=
      ⟨Finset.Nonempty.mono (lft_mono' hs) h.1, Finset.Nonempty.mono (rgt_mono' hs) h.2⟩
    rw [if_pos h] at hm
    rw [if_pos h']
    exact lat_mono T hT n h.1 h.2 (lft_mono' hs) (rgt_mono' hs) L hm
  · rw [if_neg h, Submodule.mem_bot] at hm
    subst hm
    exact zero_mem _

private lemma mix_step (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) (hA : T.admitted n z) (L : Finset κ) {l : κ} (hl : l ∉ L)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1))) {m : E}
    (hm : m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s) :
    T.act (z l) m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ insert l L, T.u n (pk I) (pk J) l : Sˣ) : S))) s := by
  unfold mixF at hm ⊢
  by_cases h : (lft s).Nonempty ∧ (rgt s).Nonempty
  · rw [if_pos h] at hm ⊢
    rw [Submodule.mem_map] at hm ⊢
    obtain ⟨m0, hm0, rfl⟩ := hm
    refine ⟨T.act (T.r n z (pk (lft s)) (pk (rgt s)) l) m0,
      hT.stab _ _ h.1 h.2 _ (r_mem T hT n z hA (pk_mem' h.1) (pk_mem' h.2) l) m0 hm0, ?_⟩
    have e : ((∏ k ∈ insert l L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S) *
        T.r n z (pk (lft s)) (pk (rgt s)) l =
        z l * ((∏ k ∈ L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S) := by
      have hu := Units.mul_inv (T.u n (pk (lft s)) (pk (rgt s)) l)
      rw [Finset.prod_insert hl, Units.val_mul]
      simp only [Sys.r]
      linear_combination (z l * ((∏ k ∈ L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S)) * hu
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
  · rw [if_neg h, Submodule.mem_bot] at hm
    rw [if_neg h, hm, map_zero]
    exact zero_mem _

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.productCup_of_system.sysOk_of :
    WdUni → SysOk := by
  intro _
  unfold SysOk
  intro d S E _ _ _ _ T κ _ _ n z hT hA
  refine ⟨⟨?_, ?_⟩, fun I J i hi j hj => ⟨fun l => r_mem T hT n z hA hi hj l, col_eq T hT n z hi hj⟩, ?_⟩
  · intro i j
    unfold Sys.wt
    rcases ofLex i with a | a <;> rcases ofLex j with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact Commute.one_left _
    · exact Commute.one_left _
    · exact Commute.one_right _
    · exact (Commute.all (z a) (z b)).map T.act
  · intro s t ht m hm
    obtain ⟨x, rfl⟩ : ∃ x : Two d ⊕ κ, toLex x = t := ⟨ofLex t, rfl⟩
    beta_reduce at hm ⊢
    rcases x with a | l
    · have hw : T.wt z (toLex (Sum.inl a)) = 1 := rfl
      rw [hw, Module.End.one_apply]
      have gen : ∀ s1 : Finset (Two d ⊕ₗ κ), lft s ⊆ lft s1 → rgt s1 = rgt s →
          m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s1, T.u n (pk I) (pk J) l : Sˣ) : S)))
            (lft s1) := by
        intro s1 h1 h2
        rw [h2]
        exact mix_mono T hT n (rgt s) h1 hm
      refine gen _ ?_ ?_
      · intro b hb
        rw [mem_lft'] at hb ⊢
        simp [hb]
      · ext b
        simp [mem_rgt']
    · have hl : l ∉ rgt s := fun h => ht ((mem_rgt' s l).1 h)
      have key := mix_step T hT n z hA (rgt s) hl (lft s) hm
      have hw : T.wt z (toLex (Sum.inr l)) = T.act (z l) := rfl
      rw [hw]
      have gen : ∀ s1 : Finset (Two d ⊕ₗ κ), lft s1 = lft s → rgt s1 = insert l (rgt s) →
          T.act (z l) m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s1, T.u n (pk I) (pk J) l : Sˣ) : S)))
            (lft s1) := by
        intro s1 h1 h2
        rw [h1, h2]
        exact key
      refine gen _ ?_ ?_
      · ext b
        simp [mem_lft']
      · ext b
        simp [mem_rgt']
  · intro I I' J J' hI hJ hII hJJ m x hx
    simp only [Cx.Z, Sys.colCx, kosT, acx, Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ,
      true_implies] at hx ⊢
    refine ⟨fun L => ?_, hx.2⟩
    have hxL := hx.1 L
    split_ifs at hxL ⊢
    · exact lat_mono T hT n hI hJ hII hJJ L hxL
    · exact hxL
end
