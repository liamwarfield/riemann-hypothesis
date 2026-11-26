module

public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CupProductFiltrationBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingProductIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorFormsSpanOfSetsMulSmulMono
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorFormsSpanOfSetsMulSmulMono
set_option autoImplicit false

namespace GlobalTheory.DI

section
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem forms_gen_mem {B : Set K} {L : Set V} {q : ℕ} {b : K} (hb : b ∈ B) (v : Fin q → V)
    (hv : ∀ k, v k ∈ L) : b • ExteriorAlgebra.ιMulti K q v ∈ forms B L q :=
  AddSubgroup.subset_closure ⟨b, hb, v, hv, rfl⟩

theorem forms_le_comap_of_gen {B B' : Set K} {L L' : Set V} {q q' : ℕ}
    (φ : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (h : ∀ b ∈ B, ∀ v : Fin q → V, (∀ k, v k ∈ L) →
      φ (b • ExteriorAlgebra.ιMulti K q v) ∈ forms B' L' q') :
    forms B L q ≤ (forms B' L' q').comap φ := by
  show AddSubgroup.closure _ ≤ _
  rw [AddSubgroup.closure_le]
  rintro x ⟨b, hb, v, hv, rfl⟩
  exact h b hb v hv

theorem ι_mul_ιMulti_eq (u : V) {q : ℕ} (w : Fin q → V) :
    ExteriorAlgebra.ι K u * ExteriorAlgebra.ιMulti K q w =
      ExteriorAlgebra.ιMulti K (q + 1) (Fin.cons u w) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  rfl

theorem ιMulti_one_eq (u : Fin 1 → V) : ExteriorAlgebra.ιMulti K 1 u = ExteriorAlgebra.ι K (u 0) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

theorem forms_mul_smul_mono (A : Subring K) (L : Set V) :
    (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧
    (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q →
      x * y ∈ forms (A : Set K) L (q + 1)) ∧
    (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧
    (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧
    ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := forms_gen_mem (B := (A : Set K)) (L := L) A.one_mem (Fin.elim0 : Fin 0 → V)
      (fun k => k.elim0)
    simpa using h
  · intro q x y hx hy

    have key : ∀ a ∈ (A : Set K), ∀ u : Fin 1 → V, (∀ k, u k ∈ L) →
        a • ExteriorAlgebra.ιMulti K 1 u * y ∈ forms (A : Set K) L (q + 1) := by
      intro a ha u hu
      have := forms_le_comap_of_gen (B := (A : Set K)) (L := L) (B' := (A : Set K)) (L' := L)
        (q := q) (q' := q + 1) (AddMonoidHom.mulLeft (a • ExteriorAlgebra.ιMulti K 1 u)) ?_ hy
      · exact this
      intro b hb w hw
      show a • ExteriorAlgebra.ιMulti K 1 u * (b • ExteriorAlgebra.ιMulti K q w) ∈ _
      rw [smul_mul_smul_comm, ιMulti_one_eq, ι_mul_ιMulti_eq]
      refine forms_gen_mem (A.mul_mem ha hb) _ ?_
      intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hu 0
      · simpa using hw k
    exact forms_le_comap_of_gen (B' := (A : Set K)) (L' := L) (q' := q + 1)
      (AddMonoidHom.mulRight y) (fun a ha u hu => key a ha u hu) hx
  · intro q c y hc hy
    refine forms_le_comap_of_gen (B' := (A : Set K)) (L' := L) (q' := q)
      (DistribSMul.toAddMonoidHom _ c) ?_ hy
    intro b hb v hv
    show c • b • ExteriorAlgebra.ιMulti K q v ∈ _
    rw [smul_smul]
    exact forms_gen_mem (A.mul_mem hc hb) v hv
  · intro B q c y hy
    refine forms_le_comap_of_gen (B' := (fun b => c * b) '' B) (L' := L) (q' := q)
      (DistribSMul.toAddMonoidHom _ c) ?_ hy
    intro b hb v hv
    show c • b • ExteriorAlgebra.ιMulti K q v ∈ _
    rw [smul_smul]
    exact forms_gen_mem (B := (fun b => c * b) '' B) (Set.mem_image_of_mem _ hb) v hv
  · intro B B' L' q hB hL
    refine (forms_le_comap_of_gen (B' := B') (L' := L') (q' := q) (AddMonoidHom.id _) ?_)
    intro b hb v hv
    exact forms_gen_mem (hB hb) v (fun k => hL (hv k))

end

end GlobalTheory.DI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorFormsSpanOfSetsMulSmulMonoStatement
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] (A : Subring K) (L : Set V), (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧ (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q → x * y ∈ forms (A : Set K) L (q + 1)) ∧ (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧ (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧ ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by
  first | exact @GlobalTheory.DI.forms_mul_smul_mono | exact GlobalTheory.DI.forms_mul_smul_mono | (intros; apply GlobalTheory.DI.forms_mul_smul_mono <;> assumption)
end
end

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem prodL_mem_forms_and_vanish {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    {ι : Type} [LinearOrder ι]
    (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι)
    (hf : ∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1)
    (hh : ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) :
    ∀ (vs : List V), (∀ w ∈ vs, w ∈ L) → ∀ t : Finset ι,
      (t ⊆ s → ∀ q, q + t.card = vs.length + 1 → prodL f h vs t ∈ forms (A : Set K) L q) ∧
      (vs.length + 1 < t.card → prodL f h vs t = 0) := by
  obtain ⟨hone, hmul, hsmul, -, -⟩ := GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono A L
  intro vs
  induction vs with
  | nil =>
    intro _ t
    simp only [prodL, List.foldr_nil, oneC, List.length_nil]
    refine ⟨fun _ q hq => ?_, fun ht => ?_⟩
    · split_ifs with h1t
      · have hq0 : q = 0 := by omega
        subst hq0
        exact hone
      · exact zero_mem _
    · rw [if_neg (by omega)]
  | cons w vs ih =>
    intro hvs t
    have hw : w ∈ L := hvs w (List.mem_cons_self ..)
    have hvs' : ∀ u ∈ vs, u ∈ L := fun u hu => hvs u (List.mem_cons_of_mem _ hu)
    have key : prodL f h (w :: vs) t = Lop f h w (prodL f h vs) t := rfl
    rw [key, List.length_cons]
    refine ⟨fun hts q hq => ?_, fun hlt => ?_⟩
    · simp only [Lop]
      by_cases ht : t.Nonempty
      · rw [dite_eq_left ht]
        have hm : t.min' ht ∈ s := hts (t.min'_mem ht)
        refine add_mem ?_ ?_
        · refine zsmul_mem ?_ _
          rcases q with _ | q
          · rw [(ih hvs' t).2 (by omega), mul_zero]
            exact zero_mem _
          · exact hmul q _ _ (hf _ hm w hw) ((ih hvs' t).1 hts q (by omega))
        · split_ifs with h2
          · have hm' : (t.erase (t.min' ht)).min' h2 ∈ s :=
              hts (Finset.mem_of_mem_erase ((t.erase _).min'_mem h2))
            have hcard : (t.erase (t.min' ht)).card = t.card - 1 :=
              Finset.card_erase_of_mem (t.min'_mem ht)
            have hpos : 0 < t.card := ht.card_pos
            exact hsmul q _ _ (hh _ hm _ hm' w hw)
              ((ih hvs' _).1 ((Finset.erase_subset _ _).trans hts) q (by omega))
          · exact zero_mem _
      · rw [dite_eq_right ht]
        exact zero_mem _
    · simp only [Lop]
      by_cases ht : t.Nonempty
      · rw [dite_eq_left ht]
        have hcard : (t.erase (t.min' ht)).card = t.card - 1 :=
          Finset.card_erase_of_mem (t.min'_mem ht)
        rw [(ih hvs' t).2 (by omega), mul_zero, smul_zero, zero_add]
        split_ifs with h2
        · rw [(ih hvs' _).2 (by omega), smul_zero]
        · rfl
      · rw [dite_eq_right ht]

theorem alt_mem_forms : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι),
    (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) →
    (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) →
    ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), (∀ k, v k ∈ L) → t ⊆ s →
      ∀ q, q + t.card = a + 1 → alt f h a v t ∈ forms (A : Set K) L q := by
  intro K _ V _ _ ι _ f h A L s hf hh a v t hv hts q hq
  rw [alt, Finset.sum_apply]
  refine AddSubgroup.sum_mem _ fun σ _ => ?_
  rw [Pi.smul_apply]
  refine zsmul_mem ?_ _
  refine (prodL_mem_forms_and_vanish f h A L s hf hh _ ?_ t).1 hts q (by rw [List.length_ofFn]; exact hq)
  intro w hw
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hw
  exact hv _

end GlobalTheory.DI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductLeadingTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductLeadingTerm
open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI.PhiLead
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem prodL_single (f : ι → V →+ V) (h : ι → ι → V →+ K) (j : ι) (vs : List V) :
    prodL f h vs {j} = ((-1 : ℤ) ^ vs.length) • (vs.map (fun v => ExteriorAlgebra.ι K (f j v))).prod := by
  induction vs with
  | nil => simp [prodL, oneC]
  | cons v vs ih =>
    have e : prodL f h (v :: vs) = Lop f h v (prodL f h vs) := rfl
    rw [e]
    simp only [Lop, Finset.singleton_nonempty, dite_true, Finset.min'_singleton, Finset.erase_singleton,
      Finset.not_nonempty_empty, dite_false, add_zero, Finset.card_singleton, ih, List.length_cons,
      List.map_cons, List.prod_cons, pow_succ]
    rw [mul_smul_comm, smul_smul]
    ring_nf

theorem alt_single (f : ι → V →+ V) (h : ι → ι → V →+ K) (a : ℕ) (v : Fin a → V) (j : ι) :
    alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
  have key : ∀ σ : Equiv.Perm (Fin a), prodL f h (List.ofFn (v ∘ σ)) {j} =
      ((-1 : ℤ) ^ a * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
    intro σ
    rw [prodL_single, List.length_ofFn, List.map_ofFn]
    have h1 : (List.ofFn ((fun v => ExteriorAlgebra.ι K (f j v)) ∘ v ∘ σ)).prod =
        ExteriorAlgebra.ιMulti K a ((fun k => f j (v k)) ∘ σ) := by
      rw [ExteriorAlgebra.ιMulti_apply]; rfl
    rw [h1, AlternatingMap.map_perm, mul_smul]
    simp [Units.smul_def]
  simp only [alt, Finset.sum_apply, Pi.smul_apply, key, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have hs : ∀ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ((-1 : ℤ) ^ a * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) = (-1 : ℤ) ^ a := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> simp [hσ]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

theorem gamma_iMulti (p : ℕ) (g : V →+ V) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V)
    (hγ : IsGamma p g γ) (a : ℕ) (v : Fin a → V) :
    γ (ExteriorAlgebra.ιMulti K a v) = ExteriorAlgebra.ιMulti K a (fun k => g (v k)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.mpr (funext fun k => hγ.2 (v k))

theorem leading_term : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (j : ι), alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k))) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (j : ι) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V), IsPhi p f h Φ → IsGamma p (f j) γ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, Φ x {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x := by
  intro K _ V _ _ ι _ p f h
  refine ⟨fun a v j => alt_single f h a v j, ?_⟩
  intro Φ j γ hΦ hγ a x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    have hg : γ (b • ExteriorAlgebra.ιMulti K a v) = b ^ p • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
      rw [Algebra.smul_def, map_mul, hγ.1, gamma_iMulti p (f j) γ hγ, ← Algebra.smul_def]
    rw [hΦ, Pi.smul_apply, alt_single, hg, smul_comm]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy, smul_add]
  | neg x _ hx => simp [hx, smul_neg]
end GlobalTheory.DI.PhiLead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductLeadingTermStatement
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechAntisymmetrizedCupProduct_leading_term : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (j : ι), alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k))) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (j : ι) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V), IsPhi p f h Φ → IsGamma p (f j) γ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, Φ x {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x := by
  first | exact @GlobalTheory.DI.PhiLead.leading_term | exact GlobalTheory.DI.PhiLead.leading_term | (intros; apply GlobalTheory.DI.PhiLead.leading_term <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingIntegralFormsBound
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AlternatingProductIntegral
open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.alternating_product_integral : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι), (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), (∀ k, v k ∈ L) → t ⊆ s → ∀ q, q + t.card = a + 1 → alt f h a v t ∈ forms (A : Set K) L q := by
  first | exact @_root_.GlobalTheory.DI.alt_mem_forms | exact _root_.GlobalTheory.DI.alt_mem_forms | (intros; apply _root_.GlobalTheory.DI.alt_mem_forms <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingIntegralFormsBound
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem pow_smul_mem_forms_powMul {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (p : ℕ) (A B : Set K) (L : Set V) (q : ℕ) (b : K) (hb : b ∈ B) (y : ExteriorAlgebra K V)
    (hy : y ∈ forms A L q) : b ^ p • y ∈ forms {z | ∃ c ∈ B, ∃ a ∈ A, z = c ^ p * a} L q := by
  unfold forms at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', v, hv, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    exact ⟨b ^ p * a', ⟨b, hb, a', ha', rfl⟩, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem phi_mem_forms : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (A : Subring K) (B : Set K) (L : Set V) (s : Finset ι), IsPhi p f h Φ → (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a q : ℕ) (t : Finset ι), t ⊆ s → q + t.card = a + 1 → ∀ x ∈ forms B L a, Φ x t ∈ forms {z | ∃ c ∈ B, ∃ b ∈ A, z = c ^ p * b} L q := by
  intro K _ V _ _ ι _ p f h Φ A B L s hΦ hf hh a q t hts hq x hx
  unfold forms at hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [show Φ (c • ExteriorAlgebra.ιMulti K a v) = c ^ p • alt f h a v from hΦ c a v, Pi.smul_apply]
    exact pow_smul_mem_forms_powMul p (A : Set K) B L q c hc _
      (GlobalTheory.T.alternating_product_integral f h A L s hf hh a v t hv hts q hq)
  | zero =>
    rw [map_zero, Pi.zero_apply]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add (f := _), Pi.add_apply]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [map_neg, Pi.neg_apply]
    exact neg_mem hx

end GlobalTheory.DI
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingIntegralFormsBoundStatement
open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.splitting_integral_forms_bound : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (A : Subring K) (B : Set K) (L : Set V) (s : Finset ι), IsPhi p f h Φ → (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a q : ℕ) (t : Finset ι), t ⊆ s → q + t.card = a + 1 → ∀ x ∈ forms B L a, Φ x t ∈ forms {z | ∃ c ∈ B, ∃ b ∈ A, z = c ^ p * b} L q := by
  first | exact @_root_.GlobalTheory.DI.phi_mem_forms | exact _root_.GlobalTheory.DI.phi_mem_forms | (intros; apply _root_.GlobalTheory.DI.phi_mem_forms <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusSplittingClosed
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AlternatingProductCocycle
set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.AltClosed

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem dtot_add {E : Type} [AddCommGroup E] (d : E →+ E) (c c' : Finset ι → E) :
    Dtot d (c + c') = Dtot d c + Dtot d c' := by
  funext t
  simp only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add (f := _)]
  abel

def dtotHom {E : Type} [AddCommGroup E] (d : E →+ E) : (Finset ι → E) →+ (Finset ι → E) :=
  AddMonoidHom.mk' (Dtot d) (dtot_add d)


omit [LinearOrder ι] in
theorem oneC_empty : (oneC : Finset ι → ExteriorAlgebra K V) ∅ = 0 := by
  simp [oneC]

theorem d_one (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) : d 1 = 0 := by
  have h1 := hd.mul 1 1
  simp only [mul_one, map_one, one_mul] at h1
  exact add_left_cancel (a := d 1) (by rw [add_zero]; exact h1.symm)

theorem delta_oneC_pair {x y : ι} (h : x < y) :
    delta (oneC : Finset ι → ExteriorAlgebra K V) {x, y} = 0 := by
  have hne : x ≠ y := ne_of_lt h
  simp only [delta]
  rw [Finset.sum_pair hne]
  have e1 : ({x, y} : Finset ι).erase x = {y} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hz' | hz'⟩
      · exact absurd hz' hz
      · exact hz'
    · rintro rfl
      exact ⟨hne.symm, Or.inr rfl⟩
  have e2 : ({x, y} : Finset ι).erase y = {x} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hz' | hz'⟩
      · exact hz'
      · exact absurd hz' hz
    · rintro rfl
      exact ⟨hne, Or.inl rfl⟩
  have s1 : GlobalTheory.cubeSign ({x, y} : Finset ι) x = 1 := by
    unfold GlobalTheory.cubeSign
    have : ({z ∈ ({x, y} : Finset ι) | z < x}) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) hz
      · exact lt_irrefl _ hz
      · exact lt_asymm h hz
    rw [this]
    simp
  have s2 : GlobalTheory.cubeSign ({x, y} : Finset ι) y = -1 := by
    unfold GlobalTheory.cubeSign
    have : ({z ∈ ({x, y} : Finset ι) | z < y}) = {x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz (lt_irrefl _)
      · rintro rfl
        exact ⟨Or.inl rfl, h⟩
    rw [this]
    simp
  rw [e1, e2, s1, s2]
  simp [oneC]

theorem delta_oneC (t : Finset ι) : delta (oneC : Finset ι → ExteriorAlgebra K V) t = 0 := by
  by_cases h2 : t.card = 2
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact delta_oneC_pair hlt
    · rw [Finset.pair_comm]
      exact delta_oneC_pair hlt
  · simp only [delta]
    apply Finset.sum_eq_zero
    intro i hi
    have hpos := Finset.card_pos.mpr ⟨i, hi⟩
    have hc : ¬ (t.erase i).card = 1 := by
      rw [Finset.card_erase_of_mem hi]
      omega
    simp [oneC, hc]

theorem dtot_oneC (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) :
    Dtot d (oneC : Finset ι → ExteriorAlgebra K V) = 0 := by
  funext t
  simp only [Dtot, delta_oneC, zero_add, Pi.zero_apply]
  unfold oneC
  split_ifs <;> simp [d_one d hd]

private theorem cubeSign_min_eq_one (s : Finset ι) (hs : s.Nonempty) : GlobalTheory.cubeSign s (s.min' hs) = 1 := by
  unfold GlobalTheory.cubeSign
  have e : ({x ∈ s | x < s.min' hs}) = ∅ := by
    apply Finset.filter_false_of_mem
    intro x hx
    exact not_lt.mpr (s.min'_le x hx)
  rw [e]
  simp

private theorem cubeSign_eq_neg_cubeSign_erase_min (s : Finset ι) (hs : s.Nonempty) (i : ι) (hi : i ∈ s.erase (s.min' hs)) :
    GlobalTheory.cubeSign s i = -GlobalTheory.cubeSign (s.erase (s.min' hs)) i := by
  have hne : i ≠ s.min' hs := Finset.ne_of_mem_erase hi
  have his : i ∈ s := Finset.mem_of_mem_erase hi
  have hlt : s.min' hs < i := lt_of_le_of_ne (s.min'_le i his) hne.symm
  unfold GlobalTheory.cubeSign
  have hfil : ({x ∈ s | x < i}) = insert (s.min' hs) ({x ∈ s.erase (s.min' hs) | x < i}) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hxs, hxi⟩
      by_cases hx : x = s.min' hs
      · exact Or.inl hx
      · exact Or.inr ⟨⟨hx, hxs⟩, hxi⟩
    · rintro (hx | ⟨⟨_, hxs⟩, hxi⟩)
      · rw [hx]
        exact ⟨s.min'_mem hs, hlt⟩
      · exact ⟨hxs, hxi⟩
  rw [hfil, Finset.card_insert_of_notMem (by simp), pow_succ]
  ring

private theorem delta_eq_erase_min_sub_sum_cubeSign {E : Type} [AddCommGroup E] (c : Finset ι → E) (s : Finset ι) (hs : s.Nonempty) :
    delta c s = c (s.erase (s.min' hs)) -
      ∑ i ∈ s.erase (s.min' hs), GlobalTheory.cubeSign (s.erase (s.min' hs)) i • c (s.erase i) := by
  unfold delta
  rw [← Finset.add_sum_erase s _ (s.min'_mem hs), cubeSign_min_eq_one s hs, one_smul, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [cubeSign_eq_neg_cubeSign_erase_min s hs i hi, neg_smul]

private theorem Lop_apply_of_min_eq (f : ι → V →+ V) (h : ι → ι → V →+ K) (v : V)
    (y : Finset ι → ExteriorAlgebra K V) (t : Finset ι) (m0 : ι) (ht : t.Nonempty) (hm : t.min' ht = m0) :
    Lop f h v y t = (-1 : ℤ) ^ t.card • (ExteriorAlgebra.ι K (f m0 v) * y t) +
      (if h2 : (t.erase m0).Nonempty then h m0 ((t.erase m0).min' h2) v • y (t.erase m0) else 0) := by
  subst hm
  unfold Lop
  rw [dite_eq_left ht]

private theorem neg_one_pow_card_erase_of_mem (t : Finset ι) (i : ι) (hi : i ∈ t) :
    (-1 : ℤ) ^ (t.erase i).card = -(-1) ^ t.card := by
  rw [Finset.card_erase_of_mem hi]
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by have := Finset.card_pos.mpr ⟨i, hi⟩; omega⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  ring

private theorem Dtot_Lop_eq_zero_of_Dtot_eq_zero_of_empty_eq_zero (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (v : V)
    (y : Finset ι → ExteriorAlgebra K V) (hy : Dtot d y = 0) (hy0 : y ∅ = 0) :
    Dtot d (Lop f h v y) = 0 := by
  have hys : ∀ s : Finset ι, d (y s) = -((-1 : ℤ) ^ s.card • delta y s) := by
    intro s
    have e0 := congrFun hy s
    simp only [Dtot, Pi.zero_apply] at e0
    have e2 : (-1 : ℤ) ^ s.card • d (y s) = -delta y s := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact e0
    have e1 : ((-1 : ℤ) ^ s.card * (-1) ^ s.card) = 1 := by
      rw [← mul_pow]
      simp
    calc d (y s) = ((-1 : ℤ) ^ s.card * (-1) ^ s.card) • d (y s) := by rw [e1, one_smul]
      _ = (-1 : ℤ) ^ s.card • ((-1 : ℤ) ^ s.card • d (y s)) := mul_smul _ _ _
      _ = -((-1 : ℤ) ^ s.card • delta y s) := by rw [e2, smul_neg]
  have dsm : ∀ (k : K) (x : ExteriorAlgebra K V), d (k • x) = d (algebraMap K _ k) * x + k • d x := by
    intro k x
    rw [Algebra.smul_def, hd.mul, AlgHom.commutes, ← Algebra.smul_def]
  have dω : ∀ (i : ι) (x : ExteriorAlgebra K V),
      d (ExteriorAlgebra.ι K (f i v) * x) = -(ExteriorAlgebra.ι K (f i v) * d x) := by
    intro i x
    rw [hd.mul, hD.closed, zero_mul, zero_add]
    rw [show CliffordAlgebra.involute (ExteriorAlgebra.ι K (f i v)) = -ExteriorAlgebra.ι K (f i v) from
      CliffordAlgebra.involute_ι _, neg_mul]
  have hε : ∀ (n : ℕ) (x : ExteriorAlgebra K V), (-1 : ℤ) ^ n • ((-1 : ℤ) ^ n • x) = x := by
    intro n x
    rw [← mul_smul, ← mul_pow]
    simp
  funext s
  simp only [Dtot, Pi.zero_apply]
  by_cases hs : s.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp [delta, Lop]
  · rw [delta_eq_erase_min_sub_sum_cubeSign _ s hs]
    have hdy := delta_eq_erase_min_sub_sum_cubeSign y s hs
    set m := s.min' hs
    set s' := s.erase m
    have hms : m ∈ s := s.min'_mem hs
    have hLs := Lop_apply_of_min_eq f h v y s m hs rfl
    have hLi : ∀ i ∈ s', Lop f h v y (s.erase i) =
        -((-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * y (s.erase i))) +
        (if h2 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h2) v • y (s'.erase i) else 0) := by
      intro i hi
      have hne : i ≠ m := Finset.ne_of_mem_erase hi
      have his : i ∈ s := Finset.mem_of_mem_erase hi
      have hmi : m ∈ s.erase i := Finset.mem_erase.mpr ⟨hne.symm, hms⟩
      have hmin : (s.erase i).min' ⟨m, hmi⟩ = m :=
        le_antisymm ((s.erase i).min'_le m hmi)
          (Finset.le_min' _ _ _ (fun z hz => s.min'_le z (Finset.mem_of_mem_erase hz)))
      rw [Lop_apply_of_min_eq f h v y (s.erase i) m ⟨m, hmi⟩ hmin, neg_one_pow_card_erase_of_mem s i his, neg_smul,
        Finset.erase_right_comm]
    have hsum : ∑ i ∈ s', GlobalTheory.cubeSign s' i • Lop f h v y (s.erase i) =
        -((-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * ∑ i ∈ s', GlobalTheory.cubeSign s' i • y (s.erase i))) +
        ∑ i ∈ s', GlobalTheory.cubeSign s' i •
          (if h2 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h2) v • y (s'.erase i) else 0) := by
      rw [Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hLi i hi, smul_add, smul_neg, mul_smul_comm, smul_comm (GlobalTheory.cubeSign s' i)]
    have hX : ∑ i ∈ s', GlobalTheory.cubeSign s' i • y (s.erase i) = y s' - delta y s := by
      rw [hdy]
      abel
    have hLs2 : Lop f h v y s = (-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * y s) +
        (if h2 : s'.Nonempty then h m (s'.min' h2) v • y s' else 0) := hLs
    rw [hsum, hLs2, hX, map_add (f := _), map_zsmul, dω, hys s]
    by_cases h2 : s'.Nonempty
    · set n := s'.min' h2 with hn_eq
      have hns : n ∈ s' := s'.min'_mem h2
      have hLs' : Lop f h v y s' = (-1 : ℤ) ^ s'.card • (ExteriorAlgebra.ι K (f n v) * y s') +
          (if h3 : (s'.erase n).Nonempty then h n ((s'.erase n).min' h3) v • y (s'.erase n) else 0) :=
        Lop_apply_of_min_eq f h v y s' n h2 rfl
      have hc : (-1 : ℤ) ^ s'.card = -(-1) ^ s.card := neg_one_pow_card_erase_of_mem s m hms
      have hSh : ∑ i ∈ s', GlobalTheory.cubeSign s' i •
          (if h3 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h3) v • y (s'.erase i) else 0) =
          (if h3 : (s'.erase n).Nonempty then h n ((s'.erase n).min' h3) v • y (s'.erase n) else 0) +
            h m n v • delta y s' := by
        rw [← sub_eq_iff_eq_add]
        unfold delta
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single n]
        · rw [show GlobalTheory.cubeSign s' n = 1 from cubeSign_min_eq_one s' h2]
          simp only [one_smul]
          by_cases h3 : (s'.erase n).Nonempty
          · rw [dite_eq_left h3, dite_eq_left h3, ← sub_smul]
            congr 1
            rw [← hD.cocycle m n ((s'.erase n).min' h3) v]
            ring
          · rw [dite_eq_right h3, dite_eq_right h3, Finset.not_nonempty_iff_eq_empty.mp h3, hy0]
            simp
        · intro b hb hbn
          have hnb : n ∈ s'.erase b := Finset.mem_erase.mpr ⟨fun e => hbn e.symm, hns⟩
          have hmin : (s'.erase b).min' ⟨n, hnb⟩ = n :=
            le_antisymm ((s'.erase b).min'_le n hnb)
              (Finset.le_min' _ _ _ (fun z hz => s'.min'_le z (Finset.mem_of_mem_erase hz)))
          rw [dite_eq_left ⟨n, hnb⟩, hmin, smul_comm (h m n v) (GlobalTheory.cubeSign s' b), sub_self]
        · intro hn
          exact absurd hns hn
      have hcomm : ∀ x : ExteriorAlgebra K V,
          h m n v • ((-1 : ℤ) ^ s.card • x) = (-1 : ℤ) ^ s.card • (h m n v • x) :=
        fun x => smul_comm _ _ _
      rw [dite_eq_left h2, ← hn_eq, hSh, hLs', dsm, hD.dh, hys s', hc]
      simp only [neg_smul, smul_neg, neg_neg, mul_neg, mul_sub, sub_mul, smul_add, smul_sub,
        mul_smul_comm, hε, hcomm]
      abel
    · have hs'e : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h2
      have hdy0 : delta y s = 0 := by
        rw [hdy, hs'e]
        simp [hy0]
      rw [dite_eq_right h2, hdy0, hs'e]
      simp [Lop, hy0]

theorem prodL_closed (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (vs : List V) :
    Dtot d (prodL f h vs) = 0 ∧ prodL f h vs ∅ = 0 := by
  induction vs with
  | nil => exact ⟨dtot_oneC d hd, oneC_empty (ι := ι)⟩
  | cons v vs ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · exact Dtot_Lop_eq_zero_of_Dtot_eq_zero_of_empty_eq_zero p d f h hd hD v _ h1 h2
    · simp [prodL, Lop]

theorem alt_closed (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (a : ℕ) (v : Fin a → V) :
    Dtot d (alt f h a v) = 0 ∧ alt f h a v ∅ = 0 := by
  have hp := fun vs => prodL_closed p d f h hd hD vs
  constructor
  · change dtotHom d (alt f h a v) = 0
    unfold alt
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply Finset.sum_eq_zero
    intro σ _
    rw [map_zsmul]
    change _ • Dtot d _ = 0
    rw [(hp _).1, smul_zero]
  · simp only [alt, Finset.sum_apply, Pi.smul_apply, (hp _).2, smul_zero, Finset.sum_const_zero]

end GlobalTheory.DI.AltClosed

theorem GlobalTheory.DI.prodL_alt_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsOddDer d → IsDatum p d f h → (∀ vs : List V, Dtot d (prodL f h vs) = 0 ∧ prodL f h vs ∅ = 0) ∧ ∀ (a : ℕ) (v : Fin a → V), Dtot d (alt f h a v) = 0 ∧ alt f h a v ∅ = 0 := by
  intro K _ V _ _ ι _ p d f h hd hD
  exact ⟨fun vs => AltClosed.prodL_closed p d f h hd hD vs,
    fun a v => AltClosed.alt_closed p d f h hd hD a v⟩
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusSplittingClosed
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.PhiClosed

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem d_alg_pow (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) (c : K) (n : ℕ) :
    d (algebraMap K (ExteriorAlgebra K V) c ^ (n + 1)) =
      (n + 1) • (algebraMap K (ExteriorAlgebra K V) c ^ n * d (algebraMap K (ExteriorAlgebra K V) c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' _ (n + 1), hd.mul, ih, AlgHom.commutes]
    have hc : d (algebraMap K (ExteriorAlgebra K V) c) * algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) =
        algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) * d (algebraMap K (ExteriorAlgebra K V) c) := by
      rw [← map_pow]
      exact (Algebra.commutes _ _).symm
    rw [hc, mul_smul_comm, ← mul_assoc, ← pow_succ', succ_nsmul' _ (n + 1)]

theorem d_alg_pow_char (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) : d (algebraMap K (ExteriorAlgebra K V) (c ^ p)) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).one_lt; omega⟩
  rw [map_pow, hk, d_alg_pow d hd c k, ← hk, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

theorem d_smul_pow (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) (y : ExteriorAlgebra K V) : d (c ^ p • y) = c ^ p • d y := by
  rw [Algebra.smul_def, hd.mul, AlgHom.commutes, d_alg_pow_char p d hd c, zero_mul, zero_add,
    ← Algebra.smul_def]

theorem Dtot_add (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (a b : Finset ι → ExteriorAlgebra K V) :
    Dtot d (a + b) = Dtot d a + Dtot d b := by
  funext t
  simp only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add (f := _)]
  abel

theorem Dtot_smul_pow (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) (a : Finset ι → ExteriorAlgebra K V) :
    Dtot d (c ^ p • a) = c ^ p • Dtot d a := by
  funext t
  simp only [Dtot, delta, Pi.smul_apply, d_smul_pow p d hd, Finset.smul_sum, smul_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · exact smul_comm _ _ _

end GlobalTheory.DI.PhiClosed

open GlobalTheory.DI.PhiClosed in
theorem GlobalTheory.DI.phi_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → IsPhi p f h Φ → (∀ x, Φ x ∅ = 0) ∧ ∀ x, Dtot d (Φ x) = 0 := by
  intro K _ V _ _ ι _ p _ _ d f h Φ hd hD hΦ
  have hA := (prodL_alt_closed p d f h hd hD).2
  have hz0 : Dtot d (0 : Finset ι → ExteriorAlgebra K V) = 0 := by
    funext t
    simp [Dtot, delta]
  have key : ∀ x : ExteriorAlgebra K V, ∀ c : K, Φ (c • x) ∅ = 0 ∧ Dtot d (Φ (c • x)) = 0 := by
    intro x
    have hx : x ∈ Submodule.span K
        (Set.range fun x : (n : ℕ) × (Fin n → V) => ExteriorAlgebra.ιMulti K x.1 x.2) := by
      rw [ExteriorAlgebra.ιMulti_span]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨a, v⟩, rfl⟩ := hy
      intro c
      rw [hΦ c a v]
      exact ⟨by rw [Pi.smul_apply, (hA a v).2, smul_zero],
        by rw [PhiClosed.Dtot_smul_pow p d hd, (hA a v).1, smul_zero]⟩
    | zero =>
      intro c
      simp [hz0]
    | add y z _ _ hy hz =>
      intro c
      rw [smul_add, map_add (f := _)]
      exact ⟨by rw [Pi.add_apply, (hy c).1, (hz c).1, add_zero],
        by rw [PhiClosed.Dtot_add, (hy c).2, (hz c).2, add_zero]⟩
    | smul a y _ hy =>
      intro c
      rw [smul_smul]
      exact hy (c * a)
  exact ⟨fun x => by simpa using (key x 1).1, fun x => by simpa using (key x 1).2⟩
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusSplittingClosedStatement
open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.frobenius_splitting_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → IsPhi p f h Φ → (∀ x, Φ x ∅ = 0) ∧ ∀ x, Dtot d (Φ x) = 0 := by
  first | exact @_root_.GlobalTheory.DI.phi_closed | exact _root_.GlobalTheory.DI.phi_closed | (intros; apply _root_.GlobalTheory.DI.phi_closed <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsFrobeniusSplittingDatum
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsFrobeniusSplittingDatum
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem exists_isPhi : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsDatum p d f h → ∃ Φ, IsPhi p f h Φ := by
  intro K _ V _ _ ι _ p _ _ d f h hD
  have lopAddV : ∀ (x x' : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h (x + x') y = Lop f h x y + Lop f h x' y := by
    intro x x' y
    funext t
    simp only [Lop, Pi.add_apply]
    split_ifs <;> simp only [map_add (f := _), add_mul, smul_add, add_smul, add_zero] <;> abel
  have lopAddY : ∀ (x : V) (y y' : Finset ι → ExteriorAlgebra K V),
      Lop f h x (y + y') = Lop f h x y + Lop f h x y' := by
    intro x y y'
    funext t
    simp only [Lop, Pi.add_apply]
    split_ifs <;> simp only [mul_add, smul_add, add_zero] <;> abel
  have lopSmulV : ∀ (c : K) (x : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h (c • x) y = c ^ p • Lop f h x y := by
    intro c x y
    funext t
    simp only [Lop, Pi.smul_apply]
    split_ifs <;>
      simp only [hD.f_smul, hD.h_smul, map_smul, smul_mul_assoc, mul_smul, smul_add, smul_zero,
        smul_comm ((-1 : ℤ) ^ t.card) (c ^ p)]
  have lopSmulY : ∀ (k : K) (x : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h x (k • y) = k • Lop f h x y := by
    intro k x y
    funext t
    simp only [Lop, Pi.smul_apply]
    split_ifs <;>
      simp only [mul_smul_comm, smul_add, smul_zero, smul_comm ((-1 : ℤ) ^ t.card) k, smul_comm _ k]
  have hcons : ∀ (x : V) (l : List V), prodL f h (x :: l) = Lop f h x (prodL f h l) := fun _ _ => rfl
  have hupd0 : ∀ {a : ℕ} (v : Fin (a + 1) → V) (z : V),
      (fun k : Fin a => Function.update v 0 z k.succ) = fun k => v k.succ := by
    intro a v z
    funext k
    exact Function.update_of_ne (Fin.succ_ne_zero k) _ _
  have hupds : ∀ {a : ℕ} (v : Fin (a + 1) → V) (j : Fin a) (z : V),
      (fun k : Fin a => Function.update v j.succ z k.succ) = Function.update (fun k => v k.succ) j z := by
    intro a v j z
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · rw [Function.update_of_ne hk, Function.update_of_ne (fun e => hk (Fin.succ_injective _ e))]
  have hPadd : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (x x' : V),
      prodL f h (List.ofFn (Function.update v i (x + x'))) =
        prodL f h (List.ofFn (Function.update v i x)) + prodL f h (List.ofFn (Function.update v i x')) := by
    intro a
    induction a with
    | zero => intro v i; exact i.elim0
    | succ a ih =>
      intro v i x x'
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp only [List.ofFn_succ, hcons, Function.update_self, hupd0]
        exact lopAddV _ _ _
      · simp only [List.ofFn_succ, hcons, hupds,
          Function.update_of_ne (Fin.succ_ne_zero j).symm]
        rw [ih, lopAddY]
  have hPsmul : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (c : K) (x : V),
      prodL f h (List.ofFn (Function.update v i (c • x))) =
        c ^ p • prodL f h (List.ofFn (Function.update v i x)) := by
    intro a
    induction a with
    | zero => intro v i; exact i.elim0
    | succ a ih =>
      intro v i c x
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp only [List.ofFn_succ, hcons, Function.update_self, hupd0]
        exact lopSmulV _ _ _
      · simp only [List.ofFn_succ, hcons, hupds,
          Function.update_of_ne (Fin.succ_ne_zero j).symm]
        rw [ih, lopSmulY]
  have key : ∃ Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V),
      (∀ (c : K) (x : ExteriorAlgebra K V), Φ (c • x) = c ^ p • Φ x) ∧
        ∀ (a : ℕ) (v : Fin a → V), Φ (ExteriorAlgebra.ιMulti K a v) = alt f h a v := by
    letI tw : Module K (Finset ι → ExteriorAlgebra K V) := Module.compHom _ (frobenius K p)
    let P : ∀ a : ℕ, (Fin a → V) →ₘₗ[K] (Finset ι → ExteriorAlgebra K V) := fun a =>
      { toFun := fun v => prodL f h (List.ofFn v)
        map_update_add' := fun v i x x' => by
          obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
          exact hPadd a v i x x'
        map_update_smul' := fun v i c x => by
          obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
          exact hPsmul a v i c x }
    let A : ∀ a : ℕ, V [⋀^Fin a]→ₗ[K] (Finset ι → ExteriorAlgebra K V) := fun a =>
      MultilinearMap.alternatization (P a)
    let Φ0 := ExteriorAlgebra.liftAlternating (R := K) A
    refine ⟨Φ0.toAddMonoidHom, fun c x => ?_, fun a v => ?_⟩
    · exact Φ0.map_smul c x
    · show Φ0 (ExteriorAlgebra.ιMulti K a v) = _
      rw [ExteriorAlgebra.liftAlternating_apply_ιMulti]
      show (MultilinearMap.alternatization (P a)) v = alt f h a v
      rw [MultilinearMap.alternatization_apply]
      unfold alt
      apply Finset.sum_congr rfl
      intro σ _
      rw [Units.smul_def]
      rfl
  obtain ⟨Φ, h1, h2⟩ := key
  exact ⟨Φ, fun c a v => by rw [h1, h2]⟩

end GlobalTheory.DI
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsFrobeniusSplittingDatumStatement
open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.exists_frobenius_splitting_datum : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsDatum p d f h → ∃ Φ, IsPhi p f h Φ := by
  first | exact @_root_.GlobalTheory.DI.exists_isPhi | exact _root_.GlobalTheory.DI.exists_isPhi | (intros; apply _root_.GlobalTheory.DI.exists_isPhi <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingLocalIntegrality
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

private theorem forms_mono' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    {B B' : Set K} {L L' : Set V} (hB : B ⊆ B') (hL : L ⊆ L') (q : ℕ) :
    forms B L q ≤ forms B' L' q := by
  unfold forms
  apply AddSubgroup.closure_mono
  rintro x ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, hB hb, v, fun k => hL (hv k), rfl⟩

private theorem iota_mem_forms_one' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (A : Subring K) (w : V) : ExteriorAlgebra.ι K w ∈ forms (A : Set K) (Set.univ : Set V) 1 := by
  unfold forms
  apply AddSubgroup.subset_closure
  refine ⟨1, A.one_mem, fun _ => w, fun _ => trivial, ?_⟩
  rw [one_smul, ExteriorAlgebra.ιMulti_apply]
  simp

private theorem psmul_zero' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (p : ℕ) [CharP K p] (x : ExteriorAlgebra K V) : p • x = 0 := by
  rw [nsmul_eq_mul, ← map_natCast (algebraMap K (ExteriorAlgebra K V)), CharP.cast_eq_zero, map_zero,
    zero_mul]

theorem decomp_pointwise : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (γ : ι → ExteriorAlgebra K V →+* ExteriorAlgebra K V) {P : Type} (U : Finset ι → Set P) (A : P → Subring K) (B : P → Set K) (L : P → Set V) (N T : ℕ → Finset ι → AddSubgroup (ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → (∀ i, IsGamma p (f i) (γ i)) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ a s, s.Nonempty → N a s ≤ forms (Set.univ : Set K) (Set.univ : Set V) a) → (∀ a s, s.Nonempty → p ≤ a → N a s = ⊥) → (∀ a s, s.Nonempty → ∀ y ∈ U s, N a s ≤ forms (B y) (L y) a) → (∀ q s x, s.Nonempty → x ∈ forms (Set.univ : Set K) (Set.univ : Set V) q → (∀ y ∈ U s, x ∈ forms {z | ∃ c ∈ B y, ∃ b ∈ A y, z = c ^ p * b} (L y) q) → x ∈ T q s) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ v ∈ L y, ExteriorAlgebra.ι K (f i v) ∈ forms (A y : Set K) (L y) 1) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L y, h i j v ∈ A y) → (∀ s, ∀ j ∈ s, CartierAt d (γ j) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  intro K _ V _ _ ι _ p _ _ d f h γ P U A B L N T hd hD hγ hNm hTm hTd hNu hNp hNU hT hfA hhA hC
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_frobenius_splitting_datum p d f h hD
  obtain ⟨h0, hcl⟩ := GlobalTheory.T.frobenius_splitting_closed p d f h Φ hd hD hΦ
  have hvan := (GlobalTheory.T.cechAntisymmetrizedCupProduct_vanish_above_degree p f h).2 Φ hΦ
  apply GlobalTheory.T.cechZero_of_hypZero_of_cartier d N T Φ hd.sq hNm hTm hTd h0 hcl
  · intro a u t x hu htu hx
    have hxu : x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a := hNu a u hu hx
    refine ⟨fun q hq => ?_, fun hlt => hvan a x hxu t hlt⟩
    apply hT q u _ hu
    · have := GlobalTheory.T.splitting_integral_forms_bound p f h Φ (⊤ : Subring K) Set.univ Set.univ t hΦ
        (fun i _ v _ => iota_mem_forms_one' ⊤ (f i v)) (fun _ _ _ _ _ _ => Subring.mem_top _) a q t
        subset_rfl hq x hxu
      exact forms_mono' (Set.subset_univ _) subset_rfl q this
    · intro y hy
      exact GlobalTheory.T.splitting_integral_forms_bound p f h Φ (A y) (B y) (L y) u hΦ (hfA u y hy) (hhA u y hy) a q t htu hq x
        (hNU a u hu y hy hx)
  · intro s j hj
    have hs : s.Nonempty := ⟨j, hj⟩
    exact GlobalTheory.T.cartierPropertyAt_sign_mul_factorial_scaling p d (γ j).toAddMonoidHom (fun x => Φ x {j}) (fun a => N a s) (fun a => T a s)
      (psmul_zero' p) (fun a ha => hNp a s hs ha)
      (fun a x hx => (GlobalTheory.T.cechAntisymmetrizedCupProduct_leading_term p f h).2 Φ j (γ j) hΦ (hγ j) a x (hNu a s hs hx)) (hC s j hj)

end GlobalTheory.DI
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingLocalIntegralityStatement
open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.splitting_local_integrality : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (γ : ι → ExteriorAlgebra K V →+* ExteriorAlgebra K V) {P : Type} (U : Finset ι → Set P) (A : P → Subring K) (B : P → Set K) (L : P → Set V) (N T : ℕ → Finset ι → AddSubgroup (ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → (∀ i, IsGamma p (f i) (γ i)) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ a s, s.Nonempty → N a s ≤ forms (Set.univ : Set K) (Set.univ : Set V) a) → (∀ a s, s.Nonempty → p ≤ a → N a s = ⊥) → (∀ a s, s.Nonempty → ∀ y ∈ U s, N a s ≤ forms (B y) (L y) a) → (∀ q s x, s.Nonempty → x ∈ forms (Set.univ : Set K) (Set.univ : Set V) q → (∀ y ∈ U s, x ∈ forms {z | ∃ c ∈ B y, ∃ b ∈ A y, z = c ^ p * b} (L y) q) → x ∈ T q s) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ v ∈ L y, ExteriorAlgebra.ι K (f i v) ∈ forms (A y : Set K) (L y) 1) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L y, h i j v ∈ A y) → (∀ s, ∀ j ∈ s, CartierAt d (γ j) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  first | exact @_root_.GlobalTheory.DI.decomp_pointwise | exact _root_.GlobalTheory.DI.decomp_pointwise | (intros; apply _root_.GlobalTheory.DI.decomp_pointwise <;> assumption)
end
