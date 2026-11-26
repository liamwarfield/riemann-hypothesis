module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntitoneFiltrationExistsAdaptedLinearIndepSet
namespace GlobalTheory

open Submodule

theorem antitone_filtration_exists_adapted_linearIndep_set {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hi : ℤ) (hhi : A hi = ⊥) (n : ℕ) :
    ∃ (s : Set M) (k : M → ℤ), LinearIndepOn L id s ∧ (∀ x ∈ s, hi - n ≤ k x) ∧
      ∀ a, hi - n ≤ a → A a = span L {x | x ∈ s ∧ a ≤ k x} := by
  classical
  induction n with
  | zero =>
    refine ⟨∅, fun _ => hi, linearIndepOn_empty L id, fun x hx => hx.elim, fun a ha => ?_⟩
    simp only [Set.mem_empty_iff_false, false_and, Set.ofPred_false, Submodule.span_empty]
    rw [eq_bot_iff, ← hhi]
    exact hA (by simpa using ha)
  | succ n ih =>
    obtain ⟨s, k, hs, hk, hspan⟩ := ih
    have hsA : s ⊆ A (hi - (n + 1 : ℕ)) := by
      intro x hx
      have hx' : x ∈ A (hi - n) := by
        rw [hspan _ le_rfl]
        exact Submodule.subset_span ⟨hx, hk x hx⟩
      exact hA (by push_cast; omega) hx'
    obtain ⟨t, htA, hst, hAt, ht⟩ := exists_linearIndepOn_id_extension hs hsA
    have hkt : ∀ x ∈ t, hi - ((n + 1 : ℕ) : ℤ) ≤ (if x ∈ s then k x else hi - (n + 1 : ℕ)) := by
      intro x _
      split_ifs with h
      · have := hk x h
        push_cast at this ⊢
        omega
      · exact le_rfl
    refine ⟨t, fun x => if x ∈ s then k x else hi - (n + 1 : ℕ), ht, hkt, fun a ha => ?_⟩
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have hset : {x | x ∈ t ∧ hi - ((n + 1 : ℕ) : ℤ) ≤
          (if x ∈ s then k x else hi - (n + 1 : ℕ))} = t := by
        ext x
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, hkt x hx⟩⟩
      rw [hset]
      exact le_antisymm (fun x hx => hAt hx) (Submodule.span_le.2 htA)
    · have ha' : hi - (n : ℤ) ≤ a := by
        push_cast at h
        omega
      rw [hspan a ha']
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hx, hkx⟩
        exact ⟨hst hx, by rw [if_pos hx]; exact hkx⟩
      · rintro ⟨hx, hkx⟩
        split_ifs at hkx with hxs
        · exact ⟨hxs, hkx⟩
        · push_cast at h hkx
          omega

theorem filtration_adapted_basis {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hfd : FiniteDimensional L ↥(⨆ a, A a))
    (hsep : ∀ x, (∀ a, x ∈ A a) → x = 0) :
    ∃ (m : ℕ) (d : Fin m → M) (k : Fin m → ℤ), LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {i | a ≤ k i}) := by
  classical
  have hle : ∀ a, A a ≤ ⨆ b, A b := fun a => le_iSup A a
  have hfa : ∀ a, FiniteDimensional L (A a) := fun a => Submodule.finiteDimensional_of_le (hle a)
  obtain ⟨a0, ha0⟩ : ∃ a0, ∀ a, Module.finrank L (A a0) ≤ Module.finrank L (A a) := by
    have hex : ∃ m, ∃ a, Module.finrank L (A a) = m := ⟨_, 0, rfl⟩
    obtain ⟨a0, h0⟩ := Nat.find_spec hex
    refine ⟨a0, fun a => ?_⟩
    have h := Nat.find_min' hex ⟨a, rfl⟩
    rw [← h0] at h
    exact h
  have hbot : A a0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply hsep
    intro a
    rcases le_total a a0 with h | h
    · exact hA h hx
    · rw [Submodule.eq_of_le_of_finrank_le (hA h) (ha0 a)]
      exact hx
  obtain ⟨a1, ha1⟩ : ∃ a1, ∀ a, Module.finrank L (A a) ≤ Module.finrank L (A a1) := by
    have hex : ∃ m, ∃ a, Module.finrank L ↥(⨆ b, A b) - Module.finrank L (A a) = m := ⟨_, 0, rfl⟩
    obtain ⟨a1, h1⟩ := Nat.find_spec hex
    refine ⟨a1, fun a => ?_⟩
    have h2 := Nat.find_min' hex ⟨a, rfl⟩
    rw [← h1] at h2
    have h3 := Submodule.finrank_mono (hle a)
    have h4 := Submodule.finrank_mono (hle a1)
    omega
  have htop : ⨆ b, A b = A a1 := by
    refine le_antisymm (iSup_le fun a => ?_) (hle a1)
    rcases le_total a1 a with h | h
    · exact hA h
    · exact (Submodule.eq_of_le_of_finrank_le (hA h) (ha1 a)).symm.le
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a0 - n ≤ a1 := ⟨(a0 - a1).toNat, by omega⟩
  obtain ⟨s, k, hs, hk, hspan⟩ := antitone_filtration_exists_adapted_linearIndep_set A hA a0 hbot n
  have hlow : ∀ a, a ≤ a0 - n → A a = A (a0 - n) := by
    intro a ha
    refine le_antisymm ?_ (hA ha)
    calc A a ≤ ⨆ c, A c := hle a
      _ = A a1 := htop
      _ ≤ A (a0 - n) := hA hn
  have hsU : ∀ x ∈ s, x ∈ (⨆ b, A b : Submodule L M) := by
    intro x hx
    have hx' : x ∈ A (a0 - n) := by
      rw [hspan _ le_rfl]
      exact Submodule.subset_span ⟨hx, hk x hx⟩
    exact hle _ hx'
  have hli : LinearIndependent L (fun x : s => (⟨x, hsU x x.2⟩ : (⨆ b, A b : Submodule L M))) :=
    LinearIndependent.of_comp (⨆ b, A b).subtype hs
  have hfin : s.Finite := Set.finite_coe_iff.1 hli.finite
  have _ := hfin.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => (e.symm i : M), fun i => k (e.symm i),
    LinearIndependent.comp hs e.symm e.symm.injective, fun a => ?_⟩
  show A a = Submodule.span L ((fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)})
  have himg : (fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)} = {x | x ∈ s ∧ a ≤ k x} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(e.symm i).2, hi⟩
    · rintro ⟨hx, hkx⟩
      exact ⟨e ⟨x, hx⟩, by simpa using hkx, by simp⟩
  rw [himg]
  rcases le_or_gt (a0 - n) a with h | h
  · exact hspan a h
  · rw [hlow a h.le, hspan _ le_rfl]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, -⟩
      exact ⟨hx, by have := hk x hx; omega⟩
    · rintro ⟨hx, -⟩
      exact ⟨hx, hk x hx⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBilinCyclic
open Polynomial

namespace GlobalTheory.SimilarTranspose

theorem _root_.GlobalTheory.SimilarTranspose.exists_form {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ l : k[X] →ₗ[k] k, (∀ a, f ∣ a → l a = 0) ∧ ∀ a, (∀ b, l (a * b) = 0) → f ∣ a := by
  set g := f * C f.leadingCoeff⁻¹ with hg
  have hgm : g.Monic := monic_mul_leadingCoeff_inv hf
  have hdvd : ∀ a, f ∣ a ↔ g ∣ a := fun a =>
    (associated_mul_unit_right f _
      (isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hf))))).dvd_iff_dvd_left
  let l : k[X] →ₗ[k] k := (lcoeff k (g.natDegree - 1)).comp (modByMonicHom g)
  refine ⟨l, fun a ha => ?_, fun a ha => ?_⟩
  · simp [l, (modByMonic_eq_zero_iff_dvd hgm).2 ((hdvd a).1 ha)]
  · rw [hdvd, ← modByMonic_eq_zero_iff_dvd hgm]
    by_contra hr
    have hg1 : g ≠ 1 := by
      rintro h
      apply hr
      rw [h, modByMonic_one]
    have hlt := natDegree_modByMonic_lt a hgm hg1
    set r := a %ₘ g with hrdef
    set m := g.natDegree - 1 - r.natDegree with hm
    have hsub : (a * X ^ m) %ₘ g = (r * X ^ m) %ₘ g := by
      apply modByMonic_eq_of_dvd_sub hgm
      refine ⟨(a /ₘ g) * X ^ m, ?_⟩
      have := modByMonic_add_div a g
      rw [hrdef]
      linear_combination -(X ^ m) * this
    have hdeg : (r * X ^ m).natDegree = g.natDegree - 1 := by
      rw [natDegree_mul_X_pow m hr]
      omega
    have hself : (r * X ^ m) %ₘ g = r * X ^ m := by
      rw [modByMonic_eq_self_iff hgm]
      apply degree_lt_degree
      omega
    have h := ha (X ^ m)
    simp only [l, LinearMap.comp_apply, modByMonicHom_apply, lcoeff_apply] at h
    rw [hsub, hself] at h
    have hidx : g.natDegree - 1 = r.natDegree + m := by omega
    rw [hidx, coeff_mul_X_pow] at h
    exact hr (leadingCoeff_eq_zero.1 h)

private theorem exists_nondegenerate_X_symmetric_form_quotient {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ G : (k[X] ⧸ (k[X] ∙ f)) →ₗ[k] (k[X] ⧸ (k[X] ∙ f)) →ₗ[k] k,
      (∀ x y, G ((X : k[X]) • x) y = G x ((X : k[X]) • y)) ∧ ∀ x, (∀ y, G x y = 0) → x = 0 := by
  obtain ⟨l, h1, h2⟩ := _root_.GlobalTheory.SimilarTranspose.exists_form f hf
  have hsurj := Submodule.Quotient.mk_surjective (k[X] ∙ f)
  let rep := Function.surjInv hsurj
  have hrep : ∀ x, Submodule.Quotient.mk (p := k[X] ∙ f) (rep x) = x := Function.surjInv_eq hsurj
  have hdiff : ∀ a a' : k[X], Submodule.Quotient.mk (p := k[X] ∙ f) a =
      Submodule.Quotient.mk (p := k[X] ∙ f) a' → f ∣ a - a' := by
    intro a a' h
    rw [Submodule.Quotient.eq, Submodule.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩
  let g : (k[X] ⧸ (k[X] ∙ f)) → (k[X] ⧸ (k[X] ∙ f)) → k := fun x y => l (rep x * rep y)
  have hg : ∀ a b, g (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = l (a * b) := by
    intro a b
    have ha := hdiff _ _ (hrep (Submodule.Quotient.mk a))
    have hb := hdiff _ _ (hrep (Submodule.Quotient.mk b))
    have : rep (Submodule.Quotient.mk a) * rep (Submodule.Quotient.mk b) - a * b =
        (rep (Submodule.Quotient.mk a) - a) * rep (Submodule.Quotient.mk b) +
          a * (rep (Submodule.Quotient.mk b) - b) := by ring
    have h0 := h1 _ (this ▸ dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hb _))
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  refine ⟨LinearMap.mk₂ k g ?_ ?_ ?_ ?_, ?_, ?_⟩
  · intro x y z
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hsurj z
    rw [← Submodule.Quotient.mk_add, hg, hg, hg, add_mul, map_add (f := _)]
  · intro c x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← Submodule.Quotient.mk_smul, hg, hg, smul_mul_assoc, map_smul]
  · intro x y z
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hsurj z
    rw [← Submodule.Quotient.mk_add, hg, hg, hg, mul_add, map_add (f := _)]
  · intro c x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← Submodule.Quotient.mk_smul, hg, hg, mul_smul_comm, map_smul]
  · intro x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    simp only [LinearMap.mk₂_apply]
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hg, hg, smul_eq_mul,
      smul_eq_mul, mul_assoc, mul_left_comm]
  · intro x hx
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨c, hc⟩ := h2 a fun b => by
      have := hx (Submodule.Quotient.mk b)
      rw [LinearMap.mk₂_apply, hg] at this
      exact this
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩

private theorem exists_nondegenerate_X_symmetric_form_torsion {k : Type} [Field k] {M : Type} [AddCommGroup M]
    [Module k[X] M] [Module k M] [IsScalarTower k k[X] M] [Module.Finite k[X] M]
    (hM : Module.IsTorsion k[X] M) :
    ∃ B : M →ₗ[k] M →ₗ[k] k, (∀ m n, B ((X : k[X]) • m) n = B m ((X : k[X]) • n)) ∧
      ∀ m, (∀ n, B m n = 0) → m = 0 := by
  classical
  obtain ⟨ι, _, p, hp, e, ⟨φ⟩⟩ := Module.equiv_directSum_of_isTorsion hM
  have hne : ∀ i, p i ^ e i ≠ 0 := fun i => pow_ne_zero _ (hp i).ne_zero
  choose G hGX hGn using fun i => exists_nondegenerate_X_symmetric_form_quotient (p i ^ e i) (hne i)
  let ψ : M →ₗ[k] (DirectSum ι fun i => k[X] ⧸ k[X] ∙ p i ^ e i) :=
    φ.toLinearMap.restrictScalars k
  have hψ : ∀ m, ψ m = φ m := fun m => rfl
  have happ : ∀ m n, (∑ i, (G i).compl₁₂ ((DirectSum.component k ι _ i).comp ψ)
      ((DirectSum.component k ι _ i).comp ψ)) m n = ∑ i, G i (φ m i) (φ n i) := by
    intro m n
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply, hψ]
    rfl
  refine ⟨∑ i, (G i).compl₁₂ ((DirectSum.component k ι _ i).comp ψ)
      ((DirectSum.component k ι _ i).comp ψ), ?_, ?_⟩
  · intro m n
    rw [happ, happ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, DirectSum.smul_apply, DirectSum.smul_apply, hGX]
  · intro m hm
    apply φ.injective
    rw [map_zero]
    refine DFinsupp.ext fun i => ?_
    apply hGn i
    intro y
    have h := hm (φ.symm (DirectSum.of _ i y))
    rw [happ, LinearEquiv.apply_symm_apply, Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hji
      rw [DirectSum.of_eq_of_ne _ _ _ hji, map_zero]
    · simp

theorem _root_.GlobalTheory.SimilarTranspose.main : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k),
    ∃ P : Matrix ι ι k, IsUnit P ∧ P * A = A.transpose * P := by
  intro k ι _ _ _ A
  have hT := Module.AEval.isTorsion_of_finiteDimensional k (ι → k) (Matrix.toLin' A)
  obtain ⟨B, hBX, hBn⟩ := exists_nondegenerate_X_symmetric_form_torsion (M := Module.AEval' (Matrix.toLin' A)) hT
  let o := Module.AEval'.of (Matrix.toLin' A)
  let Q : (ι → k) →ₗ[k] (ι → k) →ₗ[k] k := B.compl₁₂ o.toLinearMap o.toLinearMap
  have hQ : Q.compl₁₂ (Matrix.toLin' A) LinearMap.id = Q.compl₁₂ LinearMap.id (Matrix.toLin' A) := by
    refine LinearMap.ext₂ fun v w => ?_
    simp only [Q, LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearEquiv.coe_coe, o]
    rw [← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of, hBX]
  have hQP : ∀ v w, Q v w = Matrix.vecMul v (LinearMap.toMatrix₂' k Q) ⬝ᵥ w := by
    intro v w
    rw [← Matrix.dotProduct_mulVec, ← Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_toMatrix']
  refine ⟨LinearMap.toMatrix₂' k Q, ?_, ?_⟩
  · rw [← Matrix.vecMul_injective_iff_isUnit]
    intro v w hvw
    have h0 : ∀ u, Q (v - w) u = 0 := by
      intro u
      rw [hQP, Matrix.sub_vecMul]
      simp only at hvw
      rw [hvw, sub_self, zero_dotProduct]
    have := hBn (o (v - w)) fun n => by
      have := h0 (o.symm n)
      simpa [Q] using this
    rw [map_eq_zero_iff _ o.injective, sub_eq_zero] at this
    exact this
  · have := congrArg (LinearMap.toMatrix₂' k) hQ
    rw [LinearMap.toMatrix₂'_compl₁₂, LinearMap.toMatrix₂'_compl₁₂] at this
    simpa [LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] using this.symm

end GlobalTheory.SimilarTranspose
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLinearEquivOfCharpolyEq
noncomputable section

namespace GlobalTheory.TraceIso

open Module

variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def tr (k : Type) [Field k] {A : Type} [Ring A] [Algebra k A] (V : Type) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] (a : A) : k :=
  LinearMap.trace k V (Algebra.lsmul k k V a)

section

variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

theorem tr_congr (e : V ≃ₗ[A] W) (a : A) : tr k V a = tr k W a := by
  have h : Algebra.lsmul k k W a = (e.restrictScalars k).conj (Algebra.lsmul k k V a) := by
    ext w
    simp [LinearEquiv.conj_apply]
  rw [tr, tr, h, LinearMap.trace_conj']

theorem tr_prod [FiniteDimensional k V] [FiniteDimensional k W] (a : A) :
    tr k (V × W) a = tr k V a + tr k W a := by
  have h : Algebra.lsmul k k (V × W) a = (Algebra.lsmul k k V a).prodMap (Algebra.lsmul k k W a) := by
    ext <;> simp
  rw [tr, h, LinearMap.trace_prodMap']
  rfl

theorem finiteDimensional_sub [FiniteDimensional k V] (P : Submodule A V) : FiniteDimensional k P := inferInstanceAs (FiniteDimensional k (P.restrictScalars k))

theorem finrank_eq_zero_of_hom [CharZero k] [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (h : ∀ a : A, tr k V a = tr k W a)
    (h₁ : ∀ f : V →ₗ[A] W, f = 0) (h₂ : ∀ f : W →ₗ[A] V, f = 0) : finrank k V = 0 := by
  classical
  let p : End A (V × W) := (LinearMap.inl A V W).comp (LinearMap.fst A V W)
  let F : End (End A (V × W)) (V × W) :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := by
        rintro φ ⟨v, w⟩
        have e₁ := LinearMap.congr_fun
          (h₁ ((LinearMap.snd A V W).comp (φ.comp (LinearMap.inl A V W)))) v
        have e₂ := LinearMap.congr_fun
          (h₂ ((LinearMap.fst A V W).comp (φ.comp (LinearMap.inr A V W)))) w
        have e₃ : φ (v, w) = φ (v, 0) + φ (0, w) := by rw [← map_add (f := _)]; simp
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.snd_apply,
          LinearMap.fst_apply, LinearMap.zero_apply] at e₁ e₂
        change ((φ (v, w)).1, (0 : W)) = φ (v, 0)
        rw [e₃]
        ext
        · simp [e₂]
        · exact e₁.symm }
  let b := Module.finBasis k (V × W)
  haveI : IsSemisimpleModule A (V × W) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A V W))
      (IsSemisimpleModule.range (LinearMap.inr A V W))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have hall : (p.restrictScalars k) = Algebra.lsmul k k (V × W) r :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hV : Algebra.lsmul k k V r = 1 := by
    ext v
    exact (congrArg Prod.fst (LinearMap.congr_fun hall (v, 0))).symm
  have hW : Algebra.lsmul k k W r = 0 := by
    ext w
    exact (congrArg Prod.snd (LinearMap.congr_fun hall (0, w))).symm
  have := h r
  unfold tr at this
  rw [hV, hW, LinearMap.trace_one, map_zero] at this
  exact_mod_cast this

theorem split_of_hom [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (f : V →ₗ[A] W) (hf : f ≠ 0) :
    ∃ (P : Submodule A V) (Q S : Submodule A W), Nonempty (V ≃ₗ[A] P × S) ∧ Nonempty (W ≃ₗ[A] Q × S) ∧
      finrank k P < finrank k V ∧ finrank k Q < finrank k W := by
  obtain ⟨P', hP'⟩ := exists_isCompl (LinearMap.ker f)
  obtain ⟨Q, hQ⟩ := exists_isCompl (LinearMap.range f)
  let e₁ : V ≃ₗ[A] (LinearMap.ker f) × (LinearMap.range f) :=
    (Submodule.prodEquivOfIsCompl _ _ hP').symm.trans
      ((LinearEquiv.refl A _).prodCongr
        ((Submodule.quotientEquivOfIsCompl _ _ hP').symm.trans f.quotKerEquivRange))
  let e₂ : W ≃ₗ[A] Q × (LinearMap.range f) := (Submodule.prodEquivOfIsCompl _ _ hQ.symm).symm
  haveI := finiteDimensional_sub (k := k) (LinearMap.ker f)
  haveI := finiteDimensional_sub (k := k) (LinearMap.range f)
  haveI := finiteDimensional_sub (k := k) Q
  haveI : Nontrivial (LinearMap.range f) :=
    Submodule.nontrivial_iff_ne_bot.2 fun h => hf (LinearMap.range_eq_bot.1 h)
  have hpos : 0 < finrank k (LinearMap.range f) := Module.finrank_pos
  refine ⟨_, Q, _, ⟨e₁⟩, ⟨e₂⟩, ?_, ?_⟩
  · rw [(e₁.restrictScalars k).finrank_eq, finrank_prod]; omega
  · rw [(e₂.restrictScalars k).finrank_eq, finrank_prod]; omega

end

theorem nonempty_linear_equiv_of_charpoly_eq [CharZero k] (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
    finrank k V + finrank k W ≤ n → (∀ a : A, tr k V a = tr k W a) → Nonempty (V ≃ₗ[A] W) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have step : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
      [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
      finrank k V + finrank k W ≤ n → (∀ a : A, tr k V a = tr k W a) → ∀ f : V →ₗ[A] W, f ≠ 0 →
      Nonempty (V ≃ₗ[A] W) := by
    intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h f hf
    obtain ⟨P, Q, S, ⟨e₁⟩, ⟨e₂⟩, hP, hQ⟩ := split_of_hom (k := k) f hf
    haveI := finiteDimensional_sub (k := k) P
    haveI := finiteDimensional_sub (k := k) Q
    haveI := finiteDimensional_sub (k := k) S
    obtain ⟨e⟩ := ih (finrank k P + finrank k Q) (by omega) P Q le_rfl fun a => by
      have := h a
      rw [tr_congr e₁, tr_congr e₂, tr_prod, tr_prod] at this
      exact add_right_cancel this
    exact ⟨e₁.trans ((e.prodCongr (LinearEquiv.refl A _)).trans e₂.symm)⟩
  intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h
  by_cases h₁ : ∀ f : V →ₗ[A] W, f = 0
  · by_cases h₂ : ∀ f : W →ₗ[A] V, f = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom h h₁ h₂)
      haveI : Subsingleton W :=
        Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom (fun a => (h a).symm) h₂ h₁)
      exact ⟨LinearEquiv.ofSubsingleton V W⟩
    · push_neg at h₂
      obtain ⟨f, hf⟩ := h₂
      obtain ⟨e⟩ := step W V (by omega) (fun a => (h a).symm) f hf
      exact ⟨e.symm⟩
  · push_neg at h₁
    obtain ⟨f, hf⟩ := h₁
    exact step V W hn h f hf

theorem exists_equiv_of_trace_eq [CharZero k] {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) (hρ : ρ.IsSemisimpleRepresentation)
    (hσ : σ.IsSemisimpleRepresentation)
    (h : ∀ g, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1 hρ
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 hσ
  have key : ∀ a : MonoidAlgebra k Γ, tr k ρ.asModule a = tr k σ.asModule a := by
    intro a
    unfold tr
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      have e₁ : LinearMap.trace k _ (Algebra.lsmul k k ρ.asModule (MonoidAlgebra.of k Γ g)) =
          LinearMap.trace k V (ρ g) := by
        rw [← LinearMap.trace_conj' (ρ g) ρ.asModuleEquiv.symm]
        congr 1
        ext v
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
        rfl
      have e₂ : LinearMap.trace k _ (Algebra.lsmul k k σ.asModule (MonoidAlgebra.of k Γ g)) =
          LinearMap.trace k W (σ g) := by
        rw [← LinearMap.trace_conj' (σ g) σ.asModuleEquiv.symm]
        congr 1
        ext v
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
        rfl
      rw [e₁, e₂, h]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | smul c a ha => simp only [map_smul, ha]
  obtain ⟨e⟩ := nonempty_linear_equiv_of_charpoly_eq (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule σ.asModule le_rfl key
  refine ⟨ρ.asModuleEquiv.symm.trans ((e.restrictScalars k).trans σ.asModuleEquiv), fun g v => ?_⟩
  change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
    σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul]
  simp

end GlobalTheory.TraceIso

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

variable {E : Type} [Field E] [NumberField E]

def Bnd (p : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Prop :=
  ∃ m : ℕ, m.Coprime p ∧ ∀ (i j : Fin n) (Q : HeightOneSpectrum (𝓞 E)),
    Valued.v ((((m : FiniteAdeleRing (𝓞 E) E) * A i j)) Q) ≤ 1

theorem bnd_mul (p n : ℕ) (A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hA : Bnd p A) (hB : Bnd p B) :
    Bnd p (A * B) := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨b, hb, hB⟩ := hB
  refine ⟨a * b, Nat.Coprime.mul_left ha hb, fun i j Q => ?_⟩
  let φ : FiniteAdeleRing (𝓞 E) E →+* _ := RestrictedProduct.evalRingHom _ Q
  have hφ : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = φ x := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hφ, Matrix.mul_apply, Finset.mul_sum, map_sum]
  apply Valuation.map_sum_le
  intro k _
  have hsplit : ((a * b : ℕ) : FiniteAdeleRing (𝓞 E) E) * (A i k * B k j) =
      ((a : FiniteAdeleRing (𝓞 E) E) * A i k) * ((b : FiniteAdeleRing (𝓞 E) E) * B k j) := by
    push_cast; ring
  rw [hsplit, map_mul, Valuation.map_mul, ← hφ, ← hφ]
  exact mul_le_one' (hA i k Q) (hB k j Q)

end GlobalTheory.StdAtPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLengthEqAndCardEqPowOfIsFiniteLength
namespace GlobalTheory

private lemma card_eq_card_residueField_of_isSimpleModule' (O : Type) [CommRing O]
    [IsLocalRing O] (S : Type) [AddCommGroup S] [Module O S] [IsSimpleModule O S] :
    Nat.card S = Nat.card (IsLocalRing.ResidueField O) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := O) (M := S)).mp ‹_›
  have hI' : I = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  subst hI'
  exact Nat.card_congr e.toEquiv

theorem _root_.GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength (O : Type) [CommRing O] [IsLocalRing O]
    (M : Type) [AddCommGroup M] [Module O M] (h : IsFiniteLength O M) :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨0, ?_, ?_⟩
    · simpa using (Module.length_eq_zero_iff (R := O) (M := M)).mpr ‹_›
    · simp [Nat.card_of_subsingleton (0 : M)]
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨n, hl, hc⟩ := ih
    refine ⟨n + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hl, Module.length_eq_one_iff.mpr ‹_›]
      push_cast
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      change Nat.card (M ⧸ N) * Nat.card N = _
      rw [card_eq_card_residueField_of_isSimpleModule' O (M ⧸ N), hc, pow_succ, mul_comm]

theorem _root_.GlobalTheory.exists_length_eq_and_card_eq_pow (O : Type) [CommRing O] [IsLocalRing O]
    (M : Type) [AddCommGroup M] [Module O M] [Finite M] :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n :=
  _root_.GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength O M
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLeMul
open MeasureTheory

namespace GlobalTheory

theorem norm_integral_star_mul_sq_le {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ)
    (hff : Integrable (fun x => star (f x) * f x) μ) (hhh : Integrable (fun x => star (h x) * h x) μ) :
    ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re := by
  have key : ∀ g : X → ℂ, (fun x => star (g x) * g x) = fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
    intro g; funext x; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have re_eq : ∀ g : X → ℂ, (∫ x, star (g x) * g x ∂μ).re = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    intro g; rw [key g, integral_complex_ofReal]; rfl
  have int_sq : ∀ g : X → ℂ, Integrable (fun x => star (g x) * g x) μ → Integrable (fun x => ‖g x‖ ^ 2) μ := by
    intro g hg; rw [key g] at hg; have hr := hg.re; simp only [RCLike.re_to_complex, Complex.ofReal_re] at hr; exact hr
  have mf : MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hf).mpr (int_sq f hff)
  have mh : MemLp h (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hh).mpr (int_sq h hhh)
  have hold := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) Real.HolderConjugate.two_two mf mh
  simp only [Real.rpow_two] at hold
  rw [re_eq f, re_eq h]
  have A0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have B0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have n1 : ‖∫ x, star (f x) * h x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖h x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext x; rw [norm_mul, norm_star]
  have n0 : 0 ≤ ‖∫ x, star (f x) * h x ∂μ‖ := norm_nonneg _
  have hsq : ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2
      = (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖h x‖ ^ 2 ∂μ) := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt A0, Real.sq_sqrt B0]
  calc ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2 :=
        pow_le_pow_left₀ n0 (n1.trans hold) 2
    _ = _ := hsq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLeMulStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_integral_star_mul_sq_le_mul : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ), AEStronglyMeasurable f μ → AEStronglyMeasurable h μ → Integrable (fun x => star (f x) * f x) μ → Integrable (fun x => star (h x) * h x) μ → ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re := by
  first | exact @GlobalTheory.norm_integral_star_mul_sq_le | exact GlobalTheory.norm_integral_star_mul_sq_le | (intros; apply GlobalTheory.norm_integral_star_mul_sq_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnit
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem eq_of_root_congr_of_deriv_unit {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Polynomial ℤ) (β β' : Ω)
    (hβ : A.valuation β ≤ 1) (hβ' : A.valuation β' ≤ 1) (h0 : Polynomial.aeval β f = 0) (h0' : Polynomial.aeval β' f = 0)
    (hd : ¬ A.valuation (Polynomial.aeval β (Polynomial.derivative f)) < 1) (hs : A.valuation (β - β') < 1) : β = β' := by
  by_contra hne
  have hb : β ∈ A := (A.valuation_le_one_iff β).mp hβ
  have hb' : β' ∈ A := (A.valuation_le_one_iff β').mp hβ'
  set b : A := ⟨β, hb⟩
  set b' : A := ⟨β', hb'⟩
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map (algebraMap ℤ A)) b (b' - b)
  rw [add_sub_cancel, derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap] at hk
  have hc := congrArg (fun x : A => (x : Ω)) hk
  have e : ∀ (p : ℤ[X]) (x : A), ((aeval x p : A) : Ω) = aeval (x : Ω) p := by
    intro p x
    exact (aeval_algebraMap_apply Ω x p).symm
  push_cast at hc
  rw [e, e, e] at hc
  have hβ0 : (b : Ω) = β := rfl
  have hβ1 : (b' : Ω) = β' := rfl
  rw [hβ0, hβ1, h0, h0'] at hc
  have hne' : β' - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hD : aeval β (derivative f) = -((k : Ω) * (β' - β)) := by
    have : (β' - β) * (aeval β (derivative f) + (k : Ω) * (β' - β)) = 0 := by linear_combination -hc
    have := (mul_eq_zero.mp this).resolve_left hne'
    linear_combination this
  apply hd
  rw [hD, Valuation.map_neg, Valuation.map_mul, Valuation.map_sub_swap]
  have hk1 : A.valuation (k : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr k.2
  calc A.valuation (k : Ω) * A.valuation (β - β') ≤ 1 * A.valuation (β - β') := by gcongr
    _ = A.valuation (β - β') := one_mul _
    _ < 1 := hs

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnitStatement
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_roots_congr_of_derivative_unit : ∀ {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Polynomial ℤ) (β β' : Ω),
    A.valuation β ≤ 1 → A.valuation β' ≤ 1 → Polynomial.aeval β f = 0 → Polynomial.aeval β' f = 0 →
    ¬ A.valuation (Polynomial.aeval β (Polynomial.derivative f)) < 1 → A.valuation (β - β') < 1 → β = β' := by
  first | exact @GlobalTheory.eq_of_root_congr_of_deriv_unit | exact GlobalTheory.eq_of_root_congr_of_deriv_unit | (intros; apply GlobalTheory.eq_of_root_congr_of_deriv_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrime
open scoped PowerSeries Pointwise

namespace GlobalTheory

theorem numerical_bounds_of_forty_mul_lt : ∀ (l H N η r : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r ≤ N ^ 2 →
    40 * (H * N ^ 2 + N ^ 3) < l →
    2 * (H + η + 2 * (N - 1) * r + 1) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧
      8 * H + 1 < l ∧ 4 * η * r + 4 < l ∧ (r + 2) * η < l + 1 := by
  intro l H N η r hN hη hηH hr hl
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hH : 2 ≤ H := by omega
  have hHN : 4 * H ≤ H * N ^ 2 := by nlinarith
  have hN3 : 8 ≤ N ^ 3 := by
    have : N ^ 3 = N * N ^ 2 := by ring
    nlinarith
  have hNr : 4 * (N * r) ≤ N ^ 3 := by
    have : N ^ 3 = N * N ^ 2 := by ring
    rw [this]; nlinarith
  have hsub : (N - 1) * r ≤ N * r := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hηr : 4 * (η * r) ≤ H * N ^ 2 := by
    have : η * r ≤ H * r := Nat.mul_le_mul_right _ hηH.le
    nlinarith
  have hNη : (N + 2) * η ≤ H * N ^ 2 := by
    have h1 : (N + 2) * η ≤ (N + 2) * H := Nat.mul_le_mul_left _ hηH.le
    have h2 : N + 2 ≤ N ^ 2 := by nlinarith
    have h3 : (N + 2) * H ≤ N ^ 2 * H := Nat.mul_le_mul_right _ h2
    nlinarith
  have hrη : r * η ≤ H * N ^ 2 := by
    have : r * η ≤ r * H := Nat.mul_le_mul_left _ hηH.le
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 2 * (N - 1) * r = 2 * ((N - 1) * r) := by ring
    rw [this]; nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · have : 4 * η * r = 4 * (η * r) := by ring
    rw [this]; nlinarith
  · have : (r + 2) * η = r * η + 2 * η := by ring
    rw [this]; nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrimeStatement
open scoped PowerSeries Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_conditions_theorem_T_large_prime : ∀ (l H N η r : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r ≤ N ^ 2 → 40 * (H * N ^ 2 + N ^ 3) < l → 2 * (H + η + 2 * (N - 1) * r + 1) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧ 8 * H + 1 < l ∧ 4 * η * r + 4 < l ∧ (r + 2) * η < l + 1 := by
  first | exact @GlobalTheory.numerical_bounds_of_forty_mul_lt | exact GlobalTheory.numerical_bounds_of_forty_mul_lt | (intros; apply GlobalTheory.numerical_bounds_of_forty_mul_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfIsHausdorff
namespace GlobalTheory.PowerSeriesAdicEval

open PowerSeries

theorem exists_algHom_apply_X {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) [h : IsAdicComplete I A] {y : A} (hy : y ∈ I) :
    ∃ ev : PowerSeries R →ₐ[R] A, ev PowerSeries.X = y := by
  let _ : WithIdeal A := ⟨I⟩
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval y := WithIdeal.isTopologicallyNilpotent_of_mem hy
  have _ : ContinuousSMul R A := DiscreteTopology.instContinuousSMul R A
  refine ⟨PowerSeries.aeval ha, ?_⟩
  rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]

theorem algHom_coe {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (f : PowerSeries R →ₐ[R] A) (p : Polynomial R) :
    f (p : PowerSeries R) = Polynomial.aeval (f PowerSeries.X) p := by
  have : f.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (f PowerSeries.X) := by
    apply Polynomial.algHom_ext
    simp
  have h := DFunLike.congr_fun this p
  simpa using h

theorem algHom_ext_of_isHausdorff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) [h : IsHausdorff I A] (f f' : PowerSeries R →ₐ[R] A)
    (hX : f PowerSeries.X = f' PowerSeries.X) (hy : f PowerSeries.X ∈ I) : f = f' := by
  apply AlgHom.ext
  intro F
  rw [← sub_eq_zero]
  refine IsHausdorff.haus h _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have e := F.eq_X_pow_mul_shift_add_trunc n
  set G : PowerSeries R := PowerSeries.mk fun i => PowerSeries.coeff (i + n) F
  have : f F - f' F = f PowerSeries.X ^ n * (f G - f' G) := by
    conv_lhs => rw [e]
    rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, algHom_coe, algHom_coe, ← hX]
    ring
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hy n)

theorem exists_eval_and_unique :
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (y : A),
      IsAdicComplete (Ideal.span {y}) A →
        (∃ ev : PowerSeries R →ₐ[R] A, ev PowerSeries.X = y) ∧
          ∀ f f' : PowerSeries R →ₐ[R] A, f PowerSeries.X = f' PowerSeries.X →
            y ∣ f PowerSeries.X → f = f' := by
  intro R A _ _ _ y h
  exact ⟨exists_algHom_apply_X (Ideal.span {y}) (Ideal.mem_span_singleton_self y),
    fun f f' h1 h2 => algHom_ext_of_isHausdorff (Ideal.span {y}) f f' h1
      (Ideal.mem_span_singleton.2 h2)⟩

end GlobalTheory.PowerSeriesAdicEval
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleSeqOfFiniteNonempty
open CategoryTheory

namespace GlobalTheory

theorem exists_compatible_seq_of_finite_nonempty
    (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n))
    (hfin : ∀ n, (Y n).Finite) (hne : ∀ n, (Y n).Nonempty)
    (hmap : ∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) :
    ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by
  classical
  let g : ∀ n, ((Y (n + 1) : Set (X (n + 1))) : Type) ⟶ ((Y n : Set (X n)) : Type) :=
    fun n => TypeCat.ofHom (fun x => ⟨f n x.1, hmap n x.1 x.2⟩)
  let F : ℕᵒᵖ ⥤ Type := Functor.ofOpSequence (X := fun n => ((Y n : Set (X n)) : Type)) g
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => (u (Opposite.op n)).1, fun n => ⟨(u (Opposite.op n)).2, ?_⟩⟩
  have h := hu (homOfLE (Nat.le_add_right n 1)).op
  have hm : F.map (homOfLE (Nat.le_add_right n 1)).op = g n :=
    Functor.ofOpSequence_map_homOfLE_succ (X := fun n => ((Y n : Set (X n)) : Type)) g n
  rw [hm] at h
  exact congrArg Subtype.val h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeDualRep
noncomputable section

namespace GlobalTheory.MonoConj

def dualRep {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (r : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k where
  toFun g := ⟨((r g⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose,
    ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose, by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.transpose_one], by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' g h := by
    apply Units.ext
    simp [mul_inv_rev, Matrix.transpose_mul]

theorem coe_dualRep {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (r : Γ →* GL (Fin a) k) (g : Γ) :
    ((dualRep r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((r g⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose := rfl

end GlobalTheory.MonoConj

end
end
