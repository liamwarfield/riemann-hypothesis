module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllC
section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllB
section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllA
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem qdet_map' {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  simp [qdet, qminor, Tm, map_list_prod, List.map_ofFn, Function.comp_def, apply_ite φ]

theorem qdet_commute {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (u : ℂ) (Z : A)
    (h : ∀ a b, Commute (E a b) Z) : Commute (qdet E u) Z := by
  unfold qdet qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine Commute.mul_left (Int.cast_commute _ _) (Commute.list_prod_left _ _ ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Commute.add_left ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_left _ _
  · exact Commute.zero_left _

theorem glRel_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (h : GlRel E) : GlRel fun a b => φ (E a b) := by
  intro a b c d
  dsimp only
  rw [← map_mul, ← map_mul, ← map_sub, h a b c d]
  split_ifs <;> simp

theorem comm_of_mem_adjoin {A : Type*} [Ring A] [Algebra ℂ A] {s : Set A} {X Z : A}
    (hX : X ∈ Algebra.adjoin ℂ s) (h : ∀ T ∈ s, Commute T Z) : Commute X Z := by
  have hs : s ⊆ Subalgebra.centralizer ℂ {Z} := fun T hT => by
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (h T hT).symm.eq
  have hX' := Algebra.adjoin_le hs hX
  rw [Subalgebra.mem_centralizer_iff] at hX'
  exact (hX' Z rfl).symm

variable {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
@[simp] theorem liftA_apply (B : Module.End ℂ M) : liftA n M P B = lift B := rfl

omit [Fintype P] [DecidableEq P] in
theorem qdet_lift (F : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) (h : HasChar F l) :
    HasChar (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) l := by
  intro u
  have e : (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) = fun a b => liftA n M P (F a b) := by
    funext a b
    rw [liftA_apply]
  rw [e, ← qdet_map', h u, AlgHom.commutes]

omit [Fintype P] in
theorem tE_empty (F : Fin n → Fin n → Module.End ℂ M) :
    (tE (∅ : Finset P) F : Fin n → Fin n → Module.End ℂ (TV n M P)) = fun a b => lift (F a b) := by
  funext a b
  simp [tE]

omit [Fintype P] in
theorem tE_comm_lift (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (B : Module.End ℂ M)
    (h : ∀ c d, Commute (F c d) B) (a b : Fin n) :
    Commute (tE S F a b : Module.End ℂ (TV n M P)) (lift B) := by
  unfold tE
  refine Commute.add_left ?_ (Commute.sum_left _ _ _ fun p _ => ?_)
  · have hc := (h a b).map (liftA n M P)
    simpa only [liftA_apply] using hc
  · unfold Commute SemiconjBy
    refine LinearMap.ext fun x => funext fun I => ?_
    simp only [Module.End.mul_apply, eAt, lift, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    split_ifs <;> simp

theorem cA_lift {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) (B : Module.End ℂ M) :
    cA col b ∘ₗ lift B = B ∘ₗ (cA col b : TV n M P →ₗ[ℂ] M) := by
  refine LinearMap.ext fun x => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp [cA, alt, pm, lift, LinearMap.sum_apply, map_sum, map_zsmul]

def cj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ W →ₐ[ℂ] Module.End ℂ V where
  toFun X := e.symm.toLinearMap ∘ₗ X ∘ₗ e.toLinearMap
  map_one' := LinearMap.ext fun v => by simp
  map_mul' X Y := LinearMap.ext fun v => by simp
  map_zero' := LinearMap.ext fun v => by simp
  map_add' X Y := LinearMap.ext fun v => by simp
  commutes' r := LinearMap.ext fun v => by simp

theorem cj_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (X : Module.End ℂ W) (v : V) : cj e X v = e.symm (X (e v)) := rfl

end PositivityTheory.Rg.Cz.TA

end
end

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]

def merge (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) : P → Fin n :=
  fun p => if h : q p then J ⟨p, h⟩ else I ⟨p, h⟩

omit [Fintype P] [DecidableEq P] in
theorem merge_left (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // q p}) :
    merge q J I x.1 = J x := by simp [merge, x.2]

omit [Fintype P] [DecidableEq P] in
theorem merge_right (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) :
    merge q J I x.1 = I x := by simp [merge, x.2]

omit [Fintype P] in
theorem merge_upd_left (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // q p}) (c : Fin n) :
    merge q (Function.update J x c) I = Function.update (merge q J I) x.1 c := by
  funext p
  by_cases h : q p
  · by_cases hp : p = x.1
    · subst hp
      simp [merge, h]
    · have hx : (⟨p, h⟩ : {p // q p}) ≠ x := fun e => hp (congrArg Subtype.val e)
      simp [merge, h, hp, Function.update_of_ne hx]
  · have hp : p ≠ x.1 := fun e => h (e ▸ x.2)
    simp [merge, h, hp]

omit [Fintype P] in
theorem merge_upd_right (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) (c : Fin n) :
    merge q J (Function.update I x c) = Function.update (merge q J I) x.1 c := by
  funext p
  by_cases h : q p
  · have hp : p ≠ x.1 := fun e => x.2 (e ▸ h)
    simp [merge, h, hp]
  · by_cases hp : p = x.1
    · subst hp
      simp [merge, h]
    · have hx : (⟨p, h⟩ : {p // ¬ q p}) ≠ x := fun e => hp (congrArg Subtype.val e)
      simp [merge, h, hp, Function.update_of_ne hx]

def spl : TV n M P ≃ₗ[ℂ] TV n (TV n M {p // ¬ q p}) {p // q p} where
  toFun F J I := F (merge q J I)
  invFun G K := G (fun x => K x.1) (fun x => K x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := by
    funext K
    show F (merge q _ _) = F K
    congr 1
    funext p
    by_cases h : q p <;> simp [merge, h]
  right_inv G := by
    funext J I
    show G (fun x => merge q J I x.1) (fun x => merge q J I x.1) = G J I
    congr 1 <;> funext x
    · exact merge_left q J I x
    · exact merge_right q J I x

omit [Fintype P] [DecidableEq P] in
theorem spl_apply (F : TV n M P) (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) :
    spl q F J I = F (merge q J I) := rfl

omit [Fintype P] in
theorem spl_tE (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) :
    spl q (tE S F a b f) =
      tE (S.subtype q) (fun a b => tE (S.subtype fun p => ¬ q p) F a b) a b (spl q f) := by
  funext J I
  simp only [spl_apply, tE, lift, eAt, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.add_apply]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not S q, add_comm]
  congr 1
  · rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : I x = a
    · simp [h, merge_right, spl_apply, merge_upd_right]
    · simp [h, merge_right]
  · rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : J x = a
    · simp [h, merge_left, spl_apply, merge_upd_left]
    · simp [h, merge_left]

omit [DecidableEq P] in
theorem card_sub (r : P → Prop) [DecidablePred r] :
    (Finset.univ.filter fun x : {p // q p} => r x.1).card = (Finset.univ.filter fun p => q p ∧ r p).card := by
  rw [← Finset.card_map (Function.Embedding.subtype q)]
  congr 1
  ext p
  simp [and_comm]

private theorem subtypePerm_subtypeCongr_eq {q : P → Prop} [DecidablePred q] (σ : Equiv.Perm P)
    (h0 : ∀ x, q (σ x) ↔ q x) (h1 : ∀ x, ¬ q (σ x) ↔ ¬ q x) :
    (σ.subtypePerm h0).subtypeCongr (σ.subtypePerm (p := fun x => ¬ q x) h1) = σ := by
  ext x
  by_cases hx : q x
  · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
    rfl
  · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
    rfl

theorem cA_split {C : Type} [DecidableEq C] (col : P → C) (hq : ∀ p p', col p = col p' → (q p ↔ q p'))
    (b : P → Fin n) (F : TV n M P) :
    cA col b F = cA (fun x : {p // ¬ q p} => col x.1) (fun x => b x.1)
      (cA (fun x : {p // q p} => col x.1) (fun x => b x.1) (spl q F)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cA, alt, colG, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, map_sum, map_smul, pm, LinearMap.pi_apply]
  simp_rw [Finset.smul_sum, smul_smul, spl_apply]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun τ _ => τ.1.subtypeCongr τ.2) ?_ ?_ ?_ ?_
  · rintro ⟨σ0, σ1⟩ hτ
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    intro x
    by_cases hx : q x
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      exact hτ.1 ⟨x, hx⟩
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
      exact hτ.2 ⟨x, hx⟩
  · rintro ⟨σ0, σ1⟩ _ ⟨σ0', σ1'⟩ _ he
    simp only at he
    have e0 : σ0 = σ0' := by
      ext x
      have := congrArg (fun σ : Equiv.Perm P => σ x.1) he
      simp only [Equiv.Perm.subtypeCongr.left_apply _ _ x.2] at this
      exact this
    have e1 : σ1 = σ1' := by
      ext x
      have := congrArg (fun σ : Equiv.Perm P => σ x.1) he
      simp only [Equiv.Perm.subtypeCongr.right_apply _ _ x.2] at this
      exact this
    rw [e0, e1]
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have h0 : ∀ x, q (σ x) ↔ q x := fun x => hq _ _ (hσ x)
    have h1 : ∀ x, ¬ q (σ x) ↔ ¬ q x := fun x => not_congr (h0 x)
    refine ⟨(σ.subtypePerm h0, σ.subtypePerm (p := fun x => ¬ q x) h1), ?_, subtypePerm_subtypeCongr_eq σ h0 h1⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun x => hσ x.1, fun x => hσ x.1⟩
  · rintro ⟨σ0, σ1⟩ _
    simp only
    rw [Equiv.Perm.sign_subtypeCongr]
    congr 1
    · push_cast
      ring
    · congr 1
      funext x
      by_cases hx : q x
      · simp [merge, hx, Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      · simp [merge, hx, Equiv.Perm.subtypeCongr.right_apply _ _ hx]

end PositivityTheory.Rg.Cz.TA

end
end

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  {ι : Type} [DecidableEq ι] (lab : P → ι) (τ₀ : ι)

def labR : {p // ¬ lab p = τ₀} → {τ // τ ≠ τ₀} := fun p => ⟨lab p.1, p.2⟩

theorem conj_tensor_entry_base (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (tE Finset.univ (fun a b => lift (F a b)) c d) =
      tE (fib lab τ₀) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ₀) = Finset.univ := by
    ext x
    simp [fib, Finset.mem_subtype, x.2]
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ₀) = ∅ := by
    ext x
    simp [fib, Finset.mem_subtype, x.2]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]

theorem conj_tensor_entry_fibre (τ : {τ // τ ≠ τ₀}) (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (lift (tE (fib (labR lab τ₀) τ) F c d)) =
      tE (fib lab τ.1) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ.1) = ∅ := by
    ext x
    simp only [Finset.mem_subtype, fib, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    rw [x.2]
    exact fun h => τ.2 h.symm
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ.1) = fib (labR lab τ₀) τ := by
    ext x
    simp [fib, labR, Finset.mem_subtype, Subtype.ext_iff]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]

omit [DecidableEq P] in
theorem card_R (τ : {τ // τ ≠ τ₀}) (co : P → Fin n) (k : Fin n) :
    (Finset.univ.filter fun p : {p // ¬ lab p = τ₀} => labR lab τ₀ p = τ ∧ co p.1 = k).card =
      (Finset.univ.filter fun p => lab p = τ.1 ∧ co p = k).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff] at hp ⊢
    exact hp
  · intro p _ q _ h
    exact Subtype.ext h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨⟨p, fun h => τ.2 (hp.1.symm.trans h)⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff]
    exact hp

omit [Fintype P] in
theorem base (E : ι → Fin n → Fin n → Module.End ℂ M) (l : ι → Fin n → ℤ)
    (hl : ∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) [Fintype P] [IsEmpty P]
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin n) :
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) •
          (ℓ ∘ₗ cA col b ∘ₗ S) := by
  have hfib : ∀ τ, fib lab τ = ∅ := fun τ => Finset.eq_empty_of_isEmpty _
  have hG : colG col = {1} := by
    ext σ
    simp [colG, Subsingleton.elim σ 1]
  obtain ⟨m, hm⟩ : ∃ m, ℓ m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  refine ⟨1, Subalgebra.one_mem _, ?_, ?_⟩
  · intro h
    apply hm
    have := LinearMap.congr_fun h (fun _ => m)
    simpa [cA, alt, hG, pm] using this
  · intro τ u
    have hc := qdet_lift (P := P) (E τ) (fun k => (l τ k : ℂ)) (hl τ) u
    simp only [hfib, tE_empty]
    rw [hc, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul]
    simp
    rfl

end PositivityTheory.Rg.Cz.TA

end
end

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TA

def TAk (N : ℕ) : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (E : ι → Fin n → Fin n → Module.End ℂ M), (∀ τ, GlRel (E τ)) →
  (∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) →
  ∀ (l : ι → Fin n → ℤ), (∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → (∀ τ, IsWh (E τ) ℓ) →
  ∀ (P : Type) [Fintype P] [DecidableEq P], Fintype.card P = N →
  ∀ (lab : P → ι) (C : Type) [DecidableEq C] (col : P → C) (b co : P → Fin n),
    (∀ p q, col p = col q → lab p = lab q) → IsTab col b → (∀ p q, col p = col q → co p = co q → p = q) →
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S)

theorem main (hT : Trans) (N : ℕ) : TAk N := by
  refine Nat.strong_induction_on N ?_
  intro N ih
  intro n M _ _ ι _ _ E hG hC l hl ℓ hℓ hW P _ _ hN lab C _ col b co hcl htab hinj
  rcases isEmpty_or_nonempty P with hP | ⟨⟨p0⟩⟩
  · exact base lab E l hl ℓ hℓ col b co
  obtain ⟨τ0, hp0⟩ : ∃ τ0, lab p0 = τ0 := ⟨_, rfl⟩
  have hcard : Fintype.card {p : P // ¬ lab p = τ0} < N := by
    rw [← hN]
    exact Fintype.card_subtype_lt (p := fun p => ¬ lab p = τ0) (x := p0) (fun h => h hp0)
  obtain ⟨S1, hS1, hne1, hev1⟩ := ih _ hcard n M {τ : ι // τ ≠ τ0} (fun τ => E τ) (fun τ => hG τ)
    (fun τ τ' h => hC τ τ' (fun e => h (Subtype.ext e))) (fun τ => l τ) (fun τ => hl τ) ℓ hℓ
    (fun τ => hW τ) {p : P // ¬ lab p = τ0} rfl (labR lab τ0) C (fun p => col p) (fun p => b p)
    (fun p => co p) (fun p q h => Subtype.ext (hcl p q h))
    ⟨fun p q h1 h2 => Subtype.ext (htab.1 _ _ h1 h2), fun p i hi => by
      obtain ⟨r, hr1, hr2⟩ := htab.2 p i hi
      exact ⟨⟨r, by rw [hcl r p hr1]; exact p.2⟩, hr1, hr2⟩⟩
    (fun p q h1 h2 => Subtype.ext (hinj _ _ h1 h2))
  unfold envAlg at hS1
  have hWh1 : IsWh (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c))
      (ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) := by
    obtain ⟨ψ, h1, h2, h3⟩ := hW τ0
    refine ⟨ψ, h1, h2, fun a c hac => ?_⟩
    have hcomm : Commute S1 (lift (E τ0 a c)) := comm_of_mem_adjoin hS1 (by
      rintro T ⟨τ, c', d', rfl⟩
      exact tE_comm_lift _ _ _ (fun x y => hC τ τ0 τ.2 x y a c) c' d')
    have e2 := cA_lift (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) (E τ0 a c)
    apply LinearMap.ext
    intro F
    have := LinearMap.congr_fun hcomm.eq F
    have h3' := LinearMap.congr_fun (h3 a c hac)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.mul_apply] at this h3' ⊢
    rw [this, ← LinearMap.comp_apply (cA _ _) (lift _), e2, LinearMap.comp_apply, h3']
  have hWh1' := hWh1
  obtain ⟨S0, hS0, hne0, hev0⟩ := hT n (TV n M {p : P // ¬ lab p = τ0})
    (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c))
    (by have := glRel_map (liftA n M {p : P // ¬ lab p = τ0}) (E τ0) (hG τ0); simpa only [liftA_apply] using this)
    (l τ0) (qdet_lift _ _ (hl τ0)) _ hne1 hWh1 {p : P // lab p = τ0} C (fun p => col p) (fun p => b p) (fun p => co p)
    ⟨fun p q h1 h2 => Subtype.ext (htab.1 _ _ h1 h2), fun p i hi => by
      obtain ⟨r, hr1, hr2⟩ := htab.2 p i hi
      exact ⟨⟨r, by rw [hcl r p hr1]; exact p.2⟩, hr1, hr2⟩⟩
    (fun p q h1 h2 => Subtype.ext (hinj _ _ h1 h2))
  unfold envAlg at hS0
  have hcAl : ∀ (B : Module.End ℂ (TV n M {p : P // ¬ lab p = τ0})) (z : TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}),
      cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) (lift B z) = B (cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) z) := fun B z => LinearMap.congr_fun (cA_lift _ _ B) z
  have hkey : ∀ Y : Module.End ℂ (TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}),
      (ℓ ∘ₗ cA col b ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0)) ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) Y =
        (((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ Y) ∘ₗ (spl (n := n) (M := M) (fun p : P => lab p = τ0)).toLinearMap := by
    intro Y
    apply LinearMap.ext
    intro F
    simp only [LinearMap.comp_apply, cj_apply, LinearEquiv.apply_symm_apply, Module.End.mul_apply, LinearEquiv.coe_coe]
    rw [cA_split (fun p => lab p = τ0) col (fun p p' h => by rw [hcl p p' h]) b]
    simp only [LinearEquiv.apply_symm_apply, Module.End.mul_apply]
    rw [hcAl]
  have hkey0 : ℓ ∘ₗ cA col b ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0) =
        ((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ (spl (n := n) (M := M) (fun p : P => lab p = τ0)).toLinearMap := by
    apply LinearMap.ext
    intro F
    simp only [LinearMap.comp_apply, cj_apply, LinearEquiv.apply_symm_apply, Module.End.mul_apply, LinearEquiv.coe_coe]
    rw [cA_split (fun p => lab p = τ0) col (fun p p' h => by rw [hcl p p' h]) b]
    simp only [LinearEquiv.apply_symm_apply, Module.End.mul_apply]
    rw [hcAl]
  refine ⟨cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0), ?_, ?_, ?_⟩
  · unfold envAlg
    rw [map_mul]
    apply Subalgebra.mul_mem
    · have hsub : Algebra.adjoin ℂ {T : Module.End ℂ (TV n M {p : P // ¬ lab p = τ0}) | ∃ (τ : {τ : ι // τ ≠ τ0}) (a c : Fin n),
          T = tE (fib (labR lab τ0) τ) (E τ) a c} ≤
          (Algebra.adjoin ℂ {T : Module.End ℂ (TV n M P) | ∃ (τ : ι) (a c : Fin n), T = tE (fib lab τ) (E τ) a c}).comap
            ((cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))).comp (liftA n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0})) := by
        apply Algebra.adjoin_le
        rintro T ⟨τ, c, d, rfl⟩
        simp only [SetLike.mem_coe, Subalgebra.mem_comap, AlgHom.comp_apply, liftA_apply]
        rw [conj_tensor_entry_fibre]
        exact Algebra.subset_adjoin ⟨τ, c, d, rfl⟩
      have := hsub hS1
      simpa only [Subalgebra.mem_comap, AlgHom.comp_apply, liftA_apply] using this
    · have hsub : Algebra.adjoin ℂ {T : Module.End ℂ (TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}) | ∃ (_ : Unit) (a c : Fin n),
          T = tE Finset.univ (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c)) a c} ≤
          (Algebra.adjoin ℂ {T : Module.End ℂ (TV n M P) | ∃ (τ : ι) (a c : Fin n), T = tE (fib lab τ) (E τ) a c}).comap
            (cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))) := by
        apply Algebra.adjoin_le
        rintro T ⟨_, c, d, rfl⟩
        simp only [SetLike.mem_coe, Subalgebra.mem_comap]
        rw [conj_tensor_entry_base]
        exact Algebra.subset_adjoin ⟨τ0, c, d, rfl⟩
      exact hsub hS0
  · rw [hkey0]
    intro h
    apply hne0
    apply LinearMap.ext
    intro G
    have := LinearMap.congr_fun h ((spl (n := n) (M := M) (fun p : P => lab p = τ0)).symm G)
    simpa using this
  · intro τ u
    by_cases hτ : τ = τ0
    · subst hτ
      have hq : qdet (tE (fib lab τ) (E τ)) u =
          cj (spl (n := n) (M := M) (fun p : P => lab p = τ)) (qdet (tE Finset.univ (fun a c => lift (P := {p : P // ¬ lab p = τ}) (E τ a c))) u) := by
        rw [qdet_map']
        simp only [conj_tensor_entry_base]
      rw [hq, hkey, hev0 u, LinearMap.smul_comp, ← hkey0]
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      congr 2
      exact card_sub (fun p : P => lab p = τ) (fun p => co p = k)
    · have hq : qdet (tE (fib lab τ) (E τ)) u =
          cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) := by
        have := qdet_map' ((cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))).comp (liftA n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0})) (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u
        simp only [AlgHom.comp_apply, liftA_apply, conj_tensor_entry_fibre] at this
        exact this.symm
      have hcQ : Commute S0 (lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) :=
        comm_of_mem_adjoin hS0 (by
          rintro T ⟨_, c, d, rfl⟩
          exact tE_comm_lift _ _ _ (fun x y => (qdet_commute _ u _ (fun a' c' =>
            tE_comm_lift _ _ _ (fun x' y' => hC τ τ0 hτ x' y' x y) a' c')).symm) c d)
      have hmid : (((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) =
          ((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0 := by
        apply LinearMap.ext
        intro F
        have := LinearMap.congr_fun hcQ.eq F
        simp only [LinearMap.comp_apply, Module.End.mul_apply] at this ⊢
        rw [this, hcAl]
      rw [hq, hkey, hmid, hev1 ⟨τ, hτ⟩ u, LinearMap.smul_comp, LinearMap.smul_comp, ← hkey0]
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      rw [card_R]

end TA

theorem transAll_of (_h1 : TensorGl) (h2 : Trans) : TransAll := by
  intro n M _ _ ι _ _ E hE hC l hl ℓ hℓ hW P _ _ lab C _ col b co h1' h2' h3'
  exact TA.main h2 (Fintype.card P) n M ι E hE hC l hl ℓ hℓ hW P rfl lab C col b co h1' h2' h3'

end PositivityTheory.Rg.Cz

end
