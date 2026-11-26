module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem rearr_gap (n : ℕ) (a b : Fin n) : rhoV n a - rhoV n b = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
  simp only [rhoV]
  ring

private theorem sum_mul_perm_le_and_eq_one_of_antitone {n : ℕ} (x y : Fin n → ℝ) (hx : Antitone x) (hy : Antitone y) (w : Equiv.Perm (Fin n)) :
    ∑ a, x a * y (w a) ≤ ∑ a, x a * y a ∧
      (StrictAnti x → StrictAnti y → ∑ a, x a * y (w a) = ∑ a, x a * y a → w = 1) := by
  have hm : Monovary x y := hx.monovary hy
  refine ⟨hm.sum_mul_comp_perm_le_sum_mul, fun sx sy he => ?_⟩
  have h2 := hm.sum_mul_comp_perm_eq_sum_mul_iff.1 he
  have hmono : StrictMono w := by
    intro i j hij
    by_contra hc
    push_neg at hc
    rcases hc.lt_or_eq with hlt | heq
    · exact absurd (h2 (show y (w i) < y (w j) from sy hlt)) (not_le.2 (sx hij))
    · exact absurd (w.injective heq) (ne_of_gt hij)
  have := hmono.eq_id
  ext i
  simp [this]

private theorem rearr_lemma_2 {n : ℕ} (x : Fin n → ℝ) :
    Antitone (domC x) ∧ (∃ w : Equiv.Perm (Fin n), domC x = x ∘ w) ∧ (Antitone x → domC x = x) ∧
      (∀ w : Equiv.Perm (Fin n), domC (x ∘ w) = domC x) ∧ nsq (domC x) = nsq x := by
  refine ⟨?_, ⟨_, rfl⟩, fun hx => ?_, fun w => ?_, ?_⟩
  · intro a b hab
    have := Tuple.monotone_sort (fun a => -x a) hab
    simpa [domC] using this
  · have : Tuple.sort (fun a => -x a) = Equiv.refl (Fin n) :=
      Tuple.sort_eq_refl_iff_monotone.2 (fun a b hab => neg_le_neg (hx hab))
    simp [domC, this]
  · have h := Tuple.comp_perm_comp_sort_eq_comp_sort (f := fun a => -x a) (σ := w)
    funext a
    show (x ∘ w) ((Tuple.sort ((fun a => -x a) ∘ w)) a) = x ((Tuple.sort fun a => -x a) a)
    have := congrFun h a
    simp only [Function.comp_apply, neg_inj] at this
    exact this
  · unfold nsq domC
    exact Equiv.sum_comp (Tuple.sort fun a => -x a) (fun a => x a ^ 2)

private theorem strictAnti_rhoV_and_dom_rhoV (n : ℕ) : StrictAnti (rhoV n) ∧ Dom (rhoV n) := by
  constructor
  · intro a b hab
    have h1 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith [rearr_gap n a b]
  · unfold Dom
    intro a b hab
    refine ⟨(b : ℕ) - (a : ℕ), ?_⟩
    rw [rearr_gap, Nat.cast_sub (Fin.lt_def.mp hab).le]

private theorem antitone_and_dom_domC_sub_rhoV_of_dom (n : ℕ) (x : Wt n) (hx : Dom x) : Antitone x ∧ Dom (domC (x - rhoV n)) := by
  unfold Dom at hx
  have hint : ∀ a b, ∃ k : ℤ, (x - rhoV n) a - (x - rhoV n) b = k := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · obtain ⟨m, hm⟩ := hx a b h
      refine ⟨(m : ℤ) - ((b : ℕ) : ℤ) + ((a : ℕ) : ℤ), ?_⟩
      simp only [Pi.sub_apply]
      push_cast
      linarith [rearr_gap n a b]
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨m, hm⟩ := hx b a h
      refine ⟨-(m : ℤ) + ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ), ?_⟩
      simp only [Pi.sub_apply]
      push_cast
      linarith [rearr_gap n b a]
  refine ⟨fun a b hab => ?_, ?_⟩
  · rcases hab.lt_or_eq with h | h
    · obtain ⟨m, hm⟩ := hx a b h
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · rw [h]
  · unfold Dom
    intro a b hab
    obtain ⟨w, hw⟩ := (rearr_lemma_2 (x - rhoV n)).2.1
    have hanti := (rearr_lemma_2 (x - rhoV n)).1
    obtain ⟨k, hk⟩ := hint (w a) (w b)
    have hk0 : (0 : ℝ) ≤ k := by
      have := hanti hab.le
      rw [hw] at this
      simp only [Function.comp_apply] at this
      linarith
    have hk1 : (0 : ℤ) ≤ k := by exact_mod_cast hk0
    refine ⟨k.toNat, ?_⟩
    rw [hw]
    simp only [Function.comp_apply]
    rw [hk, ← Int.cast_natCast, Int.toNat_of_nonneg hk1]

private theorem nsq_le_and_eq_of_nsq_le_sum_mul {n : ℕ} (x y : Fin n → ℝ) (h : nsq x ≤ ∑ a, x a * y a) :
    nsq x ≤ nsq y ∧ (nsq y ≤ nsq x → x = y) := by
  have hsq : 0 ≤ ∑ a, (x a - y a) ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hexp : ∑ a, (x a - y a) ^ 2 = nsq x - 2 * ∑ a, x a * y a + nsq y := by
    unfold nsq
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  refine ⟨by linarith, fun h2 => ?_⟩
  have h0 : ∑ a, (x a - y a) ^ 2 = 0 := by linarith
  funext a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (x a - y a))).1 h0 a (Finset.mem_univ a)
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

theorem UpperTheory.RealTr.rearr :
    ∀ n : ℕ, (∀ x y : Wt n, Antitone x → Antitone y → ∀ w : Equiv.Perm (Fin n), ∑ a, x a * y (w a) ≤ ∑ a, x a * y a ∧
        (StrictAnti x → StrictAnti y → ∑ a, x a * y (w a) = ∑ a, x a * y a → w = 1)) ∧
      (∀ x : Wt n, Antitone (domC x) ∧ (∃ w : Equiv.Perm (Fin n), domC x = x ∘ w) ∧ (Antitone x → domC x = x) ∧
        (∀ w : Equiv.Perm (Fin n), domC (x ∘ w) = domC x) ∧ nsq (domC x) = nsq x) ∧
      StrictAnti (rhoV n) ∧ Dom (rhoV n) ∧ (∀ x : Wt n, Dom x → Antitone x ∧ Dom (domC (x - rhoV n))) ∧
      ∀ x y : Wt n, nsq x ≤ ∑ a, x a * y a → nsq x ≤ nsq y ∧ (nsq y ≤ nsq x → x = y) := by
  intro n
  exact ⟨fun x y hx hy w => sum_mul_perm_le_and_eq_one_of_antitone x y hx hy w, fun x => rearr_lemma_2 x, (strictAnti_rhoV_and_dom_rhoV n).1, (strictAnti_rhoV_and_dom_rhoV n).2,
    fun x hx => antitone_and_dom_domC_sub_rhoV_of_dom n x hx, fun x y h => nsq_le_and_eq_of_nsq_le_sum_mul x y h⟩
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TraceRestrictSupDisjoint
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem trace_restrict_sup_disjoint {V : Type} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V)
    (S S' : Submodule ℂ V) (hF : FiniteDimensional ℂ S) (hF' : FiniteDimensional ℂ S')
    (hd : Disjoint S S') (hS : ∀ x ∈ S, f x ∈ S) (hS' : ∀ x ∈ S', f x ∈ S')
    (hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S') :
    LinearMap.trace ℂ ↥(S ⊔ S') (f.restrict hT) =
      LinearMap.trace ℂ S (f.restrict hS) + LinearMap.trace ℂ S' (f.restrict hS') := by
  let φ : (S × S') →ₗ[ℂ] ↥(S ⊔ S') :=
    ((S.subtype.coprod S'.subtype).codRestrict (S ⊔ S') (fun p => by
      simpa using Submodule.add_mem_sup p.1.2 p.2.2))
  have hφ : ∀ p, (φ p : V) = (p.1 : V) + (p.2 : V) := fun p => by simp [φ]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ h
    have h0 : (a : V) + (b : V) = 0 := by simpa [hφ] using congrArg Subtype.val h
    have ha : (a : V) ∈ S' := by
      have : (a : V) = -(b : V) := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact S'.neg_mem b.2
    have ha0 : (a : V) = 0 := (Submodule.disjoint_def.1 hd) _ a.2 ha
    have hb0 : (b : V) = 0 := by simpa [ha0] using h0
    ext <;> simp [ha0, hb0]
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (hφ _)⟩
  let e : (S × S') ≃ₗ[ℂ] ↥(S ⊔ S') := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ p, (e p : V) = (p.1 : V) + (p.2 : V) := fun p => hφ p
  have hconj : f.restrict hT = e.conj ((f.restrict hS).prodMap (f.restrict hS')) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨p, rfl⟩ := e.surjective x
    have hc : e.conj ((f.restrict hS).prodMap (f.restrict hS')) (e p) =
        e ((f.restrict hS).prodMap (f.restrict hS') p) := by
      simp [LinearEquiv.conj_apply]
    rw [hc]
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply, he, he, map_add (f := _)]
    rfl
  rw [hconj, LinearMap.trace_conj', LinearMap.trace_prodMap']

theorem UpperTheory.RealTr.trAdd :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V),
      (∀ S S' : Submodule ℂ V, FiniteDimensional ℂ S → FiniteDimensional ℂ S' → Disjoint S S' → (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S', f x ∈ S') →
        trOn (S ⊔ S') f = trOn S f + trOn S' f) ∧
      (∀ (S : Submodule ℂ V) (g : Module.End ℂ V) (c : ℂ), (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S, g x ∈ S) →
        trOn S (f + g) = trOn S f + trOn S g ∧ trOn S (c • f) = c * trOn S f ∧ ((∀ x ∈ S, f x = g x) → trOn S f = trOn S g)) ∧
      (∀ (S S' : Submodule ℂ V) (g : Module.End ℂ V), FiniteDimensional ℂ S → FiniteDimensional ℂ S' → (∀ x ∈ S, f x ∈ S') → (∀ x ∈ S', g x ∈ S) →
        trOn S (g * f) = trOn S' (f * g)) ∧
      ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → trOn S (1 : Module.End ℂ V) = Module.finrank ℂ S := by
  intro V _ _ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S S' hF hF' hd hS hS'
    have hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S' := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hS a ha) (hS' b hb)
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dite_eq_left hT, dite_eq_left hS, dite_eq_left hS']
    exact trace_restrict_sup_disjoint f S S' hF hF' hd hS hS' hT
  · intro S g c hf hg
    have hfg : ∀ x ∈ S, (f + g) x ∈ S := fun x hx => S.add_mem (hf x hx) (hg x hx)
    have hcf : ∀ x ∈ S, (c • f) x ∈ S := fun x hx => S.smul_mem c (hf x hx)
    refine ⟨?_, ?_, ?_⟩
    · unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dite_eq_left hfg, dite_eq_left hf, dite_eq_left hg, ← map_add (f := _)]
      congr 1
    · unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dite_eq_left hcf, dite_eq_left hf]
      have : (c • f).restrict hcf = c • f.restrict hf := by ext x; simp
      rw [this, map_smul, smul_eq_mul]
    · intro he
      unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dite_eq_left hf, dite_eq_left hg]
      congr 1
      ext x
      simp [he x x.2]
  · intro S S' g hF hF' hf hg
    have h1 : ∀ x ∈ S, (g * f) x ∈ S := fun x hx => hg _ (hf x hx)
    have h2 : ∀ x ∈ S', (f * g) x ∈ S' := fun x hx => hf _ (hg x hx)
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dite_eq_left h1, dite_eq_left h2]
    let a : S →ₗ[ℂ] S' := f.restrict hf
    let b : S' →ₗ[ℂ] S := g.restrict hg
    have e1 : (g * f).restrict h1 = b ∘ₗ a := by ext x; rfl
    have e2 : (f * g).restrict h2 = a ∘ₗ b := by ext x; rfl
    rw [e1, e2]
    exact LinearMap.trace_comp_comm' a b
  · intro S hF
    have h1 : ∀ x ∈ S, (1 : Module.End ℂ V) x ∈ S := fun x hx => hx
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dite_eq_left h1]
    have : (1 : Module.End ℂ V).restrict h1 = LinearMap.id := by ext x; rfl
    rw [this, LinearMap.trace_id]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Sl2Core
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem sl2Core {V : Type} [AddCommGroup V] [Module ℂ V] (E G A B : Module.End ℂ V)
    (S : Submodule ℂ V) (hfin : FiniteDimensional ℂ S)
    (hEG : ∀ v, E (G v) = G (E v) + A v - B v)
    (hAG : ∀ v, A (G v) = G (A v) - G v)
    (hBG : ∀ v, B (G v) = G (B v) + G v)
    (hS : ∀ v ∈ S, G v ∈ S) (α β : ℂ) (x : V) (hxS : x ∈ S) (hx : x ≠ 0)
    (hA : A x = α • x) (hB : B x = β • x) (hE : E x = 0) :
    ∃ m : ℕ, α - β = (m : ℂ) := by
  classical
  let v : ℕ → V := fun k => (G ^ k) x
  have hv0 : v 0 = x := by simp [v]
  have hv : ∀ k, v (k + 1) = G (v k) := by
    intro k
    simp [v, pow_succ', Module.End.mul_apply]
  have hvS : ∀ k, v k ∈ S := by
    intro k
    induction k with
    | zero => simpa [hv0] using hxS
    | succ k ih => rw [hv]; exact hS _ ih
  have hAk : ∀ k : ℕ, A (v k) = (α - k) • v k := by
    intro k
    induction k with
    | zero => simp [hv0, hA]
    | succ k ih =>
      rw [hv, hAG, ih, map_smul]
      push_cast
      module
  have hBk : ∀ k : ℕ, B (v k) = (β + k) • v k := by
    intro k
    induction k with
    | zero => simp [hv0, hB]
    | succ k ih =>
      rw [hv, hBG, ih, map_smul]
      push_cast
      module
  have hEk : ∀ k : ℕ, E (v (k + 1)) = (((k : ℂ) + 1) * (α - β - k)) • v k := by
    intro k
    induction k with
    | zero =>
      rw [hv, hEG, hv0, hE, hA, hB, map_zero]
      push_cast
      module
    | succ k ih =>
      rw [hv (k + 1), hEG, ih, map_smul, ← hv, hAk, hBk]
      push_cast
      module
  have hex : ∃ k, v k = 0 := by
    by_contra hne
    push_neg at hne
    have hli : LinearIndependent ℂ v := by
      apply Module.End.eigenvectors_linearIndependent' A (fun k : ℕ => α - k)
      · intro i j hij
        have : (i : ℂ) = j := by simpa using hij
        exact_mod_cast this
      · intro i
        rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
        exact ⟨hAk i, hne i⟩
    let w : ℕ → S := fun k => ⟨v k, hvS k⟩
    have hliw : LinearIndependent ℂ w := by
      apply LinearIndependent.of_comp S.subtype
      exact hli
    have : Finite ℕ := hliw.finite
    exact not_finite ℕ
  have hk : v (Nat.find hex) = 0 := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hx
    rw [← hv0, ← h0]
    exact hk
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hvm : v m ≠ 0 := Nat.find_min hex (by omega)
  have hvm1 : v (m + 1) = 0 := by
    rw [show m + 1 = Nat.find hex by omega]
    exact hk
  have h := hEk m
  rw [hvm1, map_zero] at h
  have hc : ((m : ℂ) + 1) * (α - β - m) = 0 := by
    by_contra hc
    exact hvm ((smul_eq_zero.mp h.symm).resolve_left hc)
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine ⟨m, ?_⟩
  have := (mul_eq_zero.mp hc).resolve_left hm1
  linear_combination this

theorem UpperTheory.RealTr.hwDom :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ (ν : Wt n), ∀ x ∈ S, x ≠ 0 → x ∈ hw F ν → Dom ν := by
  intro n V _ _ F hUF S hfin hStb ν x hxS hx hxw
  have hk : KHighest (fun _ => true) F ν x := hxw
  have hgl : GlRel F := hUF.gl
  intro a b hab
  have hne : a ≠ b := ne_of_lt hab
  have hEG : ∀ v, F a b (F b a v) = F b a (F a b v) + F a a v - F b b v := by
    intro v
    have h := LinearMap.congr_fun (hgl a b b a) v
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hAG : ∀ v, F a a (F b a v) = F b a (F a a v) - F b a v := by
    intro v
    have h := LinearMap.congr_fun (hgl a a b a) v
    simp only [if_neg hne, if_true, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hBG : ∀ v, F b b (F b a v) = F b a (F b b v) + F b a v := by
    intro v
    have h := LinearMap.congr_fun (hgl b b b a) v
    simp only [if_neg hne, if_neg hne.symm, if_true, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.zero_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hS : ∀ v ∈ S, F b a v ∈ S := fun v hv => hStb b a v hv
  obtain ⟨m, hm⟩ := sl2Core (F a b) (F b a) (F a a) (F b b) S hfin hEG hAG hBG hS
    (ν a : ℂ) (ν b : ℂ) x hxS hx (hk.1 a) (hk.1 b) (hk.2 a b hab rfl)
  refine ⟨m, ?_⟩
  apply Complex.ofReal_injective
  push_cast
  exact hm
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnRel
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem tri {A : Type} [Ring A] (x y z p q : A) (h1 : y * z + z * y = p)
    (h2 : x * z + z * x = q) : x * y * z - z * (x * y) = x * p - q * y := by
  rw [← h1, ← h2]
  noncomm_ring

private theorem leib {A : Type} [Ring A] (X u v : A) :
    X * (u * v) - u * v * X = (X * u - u * X) * v + u * (X * v - v * X) := by
  noncomm_ring

private theorem spn_comm {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (hc : Clif c) (a b d e : Fin n) :
    spn c a b * c d e - c d e * spn c a b =
      (if b = d then c a e else 0) - (if e = a then c d b else 0) := by
  have hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t :=
    fun t r => (Algebra.commutes r t).symm
  have hsum : spn c a b * c d e - c d e * spn c a b =
      ∑ f, (c a f * c f b * c d e - c d e * (c a f * c f b)) := by
    unfold spn
    rw [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    split_ifs
    · rw [hs]
      abel
    · simp
  rw [hsum]
  have hterm : ∀ f, c a f * c f b * c d e - c d e * (c a f * c f b) =
      c a f * (if b = d ∧ f = e then 1 else 0) - (if f = d ∧ a = e then 1 else 0) * c f b := by
    intro f
    exact tri _ _ _ _ _ (hc f b d e) (hc a f d e)
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases hbd : b = d
    · simp [hbd]
    · simp [hbd]
  · by_cases hea : e = a
    · subst hea
      simp
    · have : ∀ f : Fin n, ¬ (f = d ∧ a = e) := fun f h => hea h.2.symm
      simp [this, hea]

theorem UpperTheory.RealTr.spnRel :
    ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A), Clif c → GlRel (spn c) ∧
      ∀ a b d e, spn c a b * c d e - c d e * spn c a b = (if b = d then c a e else 0) - (if e = a then c d b else 0) := by
  intro n A _ _ c hc
  refine ⟨?_, fun a b d e => spn_comm c hc a b d e⟩
  intro a b g h
  have hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t :=
    fun t r => (Algebra.commutes r t).symm
  have expand : ∀ X : A, X * spn c g h - spn c g h * X =
      ∑ f, (X * (c g f * c f h) - c g f * c f h * X) := by
    intro X
    unfold spn
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
    split_ifs
    · rw [hs]
      abel
    · simp
  rw [expand]
  simp_rw [leib, spn_comm c hc]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  unfold spn
  by_cases hbg : b = g <;> by_cases hha : h = a
  · subst hbg
    subst hha
    simp
  · simp [hbg, hha, Ne.symm hha]
  · simp [hbg, hha, Ne.symm hbg]
    abel
  · simp [hbg, hha, Ne.symm hbg, Ne.symm hha]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WspOrth
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem wsp_orth {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hF : UF F) {μ ν : Wt n} (h : μ ≠ ν) {x y : V}
    (hx : x ∈ wsp F μ) (hy : y ∈ wsp F ν) : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 h
  have h1 := hF.unit a a x y
  have hx' : F a a x = (μ a : ℂ) • x := hx a
  have hy' : F a a y = (ν a : ℂ) • y := hy a
  rw [hx', hy', inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
  have h2 : ((μ a : ℂ) - (ν a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
  have h3 : (μ a : ℂ) - (ν a : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun e => ha (Complex.ofReal_injective e)
  exact (mul_eq_zero.1 h2).resolve_left h3

theorem UpperTheory.RealTr.wtDec :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∃ s : Finset (Wt n), (∀ μ ∉ s, wsp F μ ⊓ S = ⊥) ∧ (⨆ μ ∈ s, wsp F μ ⊓ S) = S ∧ iSupIndep fun μ => wsp F μ ⊓ S := by
  intro n V _ _ F hF S hSfin hS
  have hind : iSupIndep fun μ => wsp F μ ⊓ S := by
    refine OrthogonalFamily.independent (OrthogonalFamily.of_pairwise fun μ ν hne => ?_)
    show (wsp F μ ⊓ S) ⟂ (wsp F ν ⊓ S)
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    exact wsp_orth hF hne hx.1 hy.1
  let T : Fin n → Module.End ℂ S := fun a => (F a a).restrict (fun x hx => hS a a x hx)
  have hT : ∀ a, (T a).IsSymmetric := by
    intro a x y
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact hF.unit a a x y
  have hcomm : Pairwise fun a b => Commute (T a) (T b) := by
    intro a b hab
    have h0 : F a a * F b b = F b b * F a a := by
      have := hF.gl a a b b
      rw [if_neg hab, if_neg (Ne.symm hab), sub_zero, sub_eq_zero] at this
      exact this
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show F a a (F b b (x : V)) = F b b (F a a (x : V))
    exact LinearMap.congr_fun h0 (x : V)
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hcomm
  have hkey : ∀ χ : Fin n → ℂ, ∀ v : S, v ∈ (⨅ i, Module.End.eigenspace (T i) (χ i)) →
      (v : V) ∈ wsp F (fun i => (χ i).re) ⊓ S := by
    intro χ v hv
    refine ⟨?_, v.2⟩
    show ∀ i, F i i (v : V) = (((χ i).re : ℝ) : ℂ) • (v : V)
    intro i
    have hvi : T i v = χ i • v := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv i)
    by_cases h0 : v = 0
    · subst h0
      simp
    · have hre : (((χ i).re : ℝ) : ℂ) = χ i := by
        have hs := hT i v v
        rw [hvi, inner_smul_left, inner_smul_right] at hs
        have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr h0
        exact Complex.conj_eq_iff_re.mp (mul_right_cancel₀ hvv hs)
      rw [hre]
      exact congrArg Subtype.val hvi
  have hspan : S ≤ ⨆ μ : Wt n, wsp F μ ⊓ S := by
    have hle : Submodule.map S.subtype (⨆ χ : Fin n → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i))
        ≤ ⨆ μ : Wt n, wsp F μ ⊓ S := by
      rw [Submodule.map_iSup]
      refine iSup_le fun χ => ?_
      rintro _ ⟨v, hv, rfl⟩
      exact le_iSup (fun μ : Wt n => wsp F μ ⊓ S) (fun i => (χ i).re) (hkey χ v hv)
    rw [htop, Submodule.map_top, Submodule.range_subtype] at hle
    exact hle
  have hfin : Set.Finite {μ : Wt n | wsp F μ ⊓ S ≠ ⊥} := by
    let W' : Wt n → Submodule ℂ S := fun μ => (wsp F μ).comap S.subtype
    have hind' : iSupIndep W' := by
      refine OrthogonalFamily.independent (OrthogonalFamily.of_pairwise fun μ ν hne => ?_)
      show W' μ ⟂ W' ν
      rw [Submodule.isOrtho_iff_inner_eq]
      intro x hx y hy
      rw [Submodule.coe_inner]
      exact wsp_orth hF hne hx hy
    haveI := hind'.fintypeNeBotOfFiniteDimensional
    refine (Set.finite_range (fun i : {μ // W' μ ≠ ⊥} => (i : Wt n))).subset ?_
    intro μ hμ
    refine ⟨⟨μ, fun h => hμ ?_⟩, rfl⟩
    rw [inf_comm, ← Submodule.map_comap_subtype]
    change Submodule.map S.subtype (W' μ) = ⊥
    rw [h, Submodule.map_bot]
  refine ⟨hfin.toFinset, ?_, ?_, hind⟩
  · intro μ hμ
    by_contra h
    exact hμ (hfin.mem_toFinset.mpr h)
  · apply le_antisymm
    · exact iSup₂_le fun μ _ => inf_le_right
    · refine hspan.trans (iSup_le fun μ => ?_)
      by_cases h : wsp F μ ⊓ S = ⊥
      · rw [h]
        exact bot_le
      · exact le_iSup₂_of_le μ (hfin.mem_toFinset.mpr h) le_rfl
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IsoFacts
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem dot_rt {n : ℕ} (x : Wt n) (a b : Fin n) : ∑ c, x c * rt a b c = x a - x b := by
  simp [rt, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

private theorem dot_add {n : ℕ} (x u v : Wt n) :
    ∑ c, x c * (u + v) c = ∑ c, x c * u c + ∑ c, x c * v c := by
  simp [mul_add, Finset.sum_add_distrib]

private theorem wt_shift {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hg : GlRel F) {μ : Wt n} {y : V}
    (hy : IsWeight F μ y) (a b : Fin n) : IsWeight F (μ + rt a b) (F a b y) := by
  intro c
  have h := LinearMap.congr_fun (hg c c a b) y
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hy c, map_smul, sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb
    simp [rt]
  · subst hca
    simp [rt, Pi.single_apply, hcb, Ne.symm hcb, add_smul]
    abel
  · subst hcb
    simp [rt, Pi.single_apply, hca, Ne.symm hca, add_smul, sub_smul]
    abel
  · simp [rt, Pi.single_apply, hca, hcb, Ne.symm hcb]

private theorem wt_word {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hg : GlRel F) {μ : Wt n} {x : V}
    (hx : IsWeight F μ x) (w : List (Fin n × Fin n)) :
    IsWeight F (μ + (w.map fun p => rt p.1 p.2).sum) (Formalism.REAL.ew F w x) := by
  induction w with
  | nil => simpa [Formalism.REAL.ew] using hx
  | cons p w ih =>
    have h := wt_shift hg ih p.1 p.2
    rw [Formalism.REAL.ew.eq_2]
    simp only [List.map_cons, List.sum_cons, Module.End.mul_apply]
    rwa [show ∀ u v : Wt n, μ + (u + v) = (μ + v) + u from fun u v => by abel]

private theorem maj_word {n : ℕ} (ν x : Wt n) (hx : Antitone x) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, p.2 < p.1) :
    ∑ a, x a * (ν + (w.map fun p => rt p.1 p.2).sum) a ≤ ∑ a, x a * ν a := by
  induction w with
  | nil => simp
  | cons p w ih =>
    have hp := hw p (by simp)
    have ih' := ih (fun q hq => hw q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons]
    rw [show ∀ u v : Wt n, ν + (u + v) = (ν + v) + u from fun u v => by abel, dot_add, dot_rt]
    have := hx hp.le
    linarith

private theorem rhoC_true (n : ℕ) : Formalism.REAL.rhoC (fun _ : Fin n => true) = rhoV n := by
  funext a
  simp only [Formalism.REAL.rhoC, rhoV]
  simp only [and_true, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  have ha := a.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

private theorem nsq_eq {n : ℕ} (u : Fin n → ℝ) : Formalism.REAL.nsq u = nsq u := by
  simp [Formalism.REAL.nsq, Formalism.REAL.dot, nsq, sq]

private theorem rhoV_anti (n : ℕ) : Antitone (rhoV n) := by
  intro a b hab
  have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [rhoV]
  linarith

theorem UpperTheory.RealTr.isoFacts :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ ν : Wt n, (∀ μ, μ ≠ ν → hw F μ ⊓ S = ⊥) →
      (∀ x ∈ S, Cas F x = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • x) ∧ (∀ μ, wsp F μ ⊓ S ≠ ⊥ → Maj μ ν) ∧ wsp F ν ⊓ S = hw F ν ⊓ S := by
  intro n V _ _ F hF S hS hst ν hν
  have hK : Formalism.REAL.KRel (fun _ : Fin n => true) F := Formalism.REAL.glRel_kRel _ F hF.gl
  have hU : Formalism.REAL.KUnit (fun _ : Fin n => true) F := fun a b _ x y => hF.unit a b x y
  have hSt : Formalism.REAL.KStable (fun _ : Fin n => true) F S := fun a b _ x hx => hst a b x hx
  obtain ⟨m, x, μ, hx, horth, hsup⟩ := Formalism.REAL.kDecomp V n (fun _ => true) F S hS hK hU hSt
  have hμ : ∀ i, μ i = ν := by
    intro i
    by_contra h
    have h0 := hν (μ i) h
    have hi : x i ∈ hw F (μ i) ⊓ S := Submodule.mem_inf.mpr ⟨(hx i).2.2, (hx i).1⟩
    rw [h0] at hi
    exact (hx i).2.1 ((Submodule.mem_bot ℂ).mp hi)
  have hC : ∀ y ∈ S, Cas F y = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • y := by
    have hCas : Formalism.REAL.CasK (fun _ : Fin n => true) F = Cas F := by
      simp [Formalism.REAL.CasK, Formalism.REAL.Cas]
    have hck : Formalism.REAL.ckv (fun _ : Fin n => true) ν = nsq (ν + rhoV n) - nsq (rhoV n) := by
      simp only [Formalism.REAL.ckv, rhoC_true, nsq_eq]
    intro y hy
    rw [← hsup] at hy
    refine Submodule.iSup_induction _ (motive := fun y => Cas F y = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • y) hy ?_ ?_ ?_
    · intro i z hz
      have hz' := Formalism.REAL.kCasSpan V n _ F (μ i) (x i) hK (hx i).2.2 z hz
      rw [hCas, hμ i, hck] at hz'
      exact hz'
    · simp
    · intro a b ha hb
      rw [map_add (f := _), ha, hb, smul_add]
  have hM : ∀ μ', wsp F μ' ⊓ S ≠ ⊥ → Maj μ' ν := by
    intro μ' hne
    by_contra hnot
    apply hne
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
    rw [Submodule.mem_bot]
    have hle : S ≤ LinearMap.ker (innerₛₗ ℂ y) := by
      rw [← hsup]
      apply iSup_le
      intro i
      rw [(Formalism.REAL.kLow V n _ F (μ i) (x i) hK (hx i).2.2).1, Formalism.REAL.lowSpan, Submodule.span_le]
      rintro z ⟨w, hwl, rfl⟩
      have hwt := wt_word hF.gl (hx i).2.2.1 w
      rw [hμ i] at hwt
      have hne' : μ' ≠ ν + (w.map fun p => rt p.1 p.2).sum := by
        rintro rfl
        exact hnot (fun t ht => maj_word ν t ht w (fun p hp => (hwl p hp).2))
      simp only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]
      exact Formalism.REAL.kWtOrth V n _ F μ' _ y _ hU hyw hwt hne'
    have h0 := hle hyS
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at h0
    exact h0
  refine ⟨hC, hM, ?_⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
    have hk : KHighest (fun _ : Fin n => true) F ν y := by
      refine ⟨hyw, ?_⟩
      intro a b hab _
      by_contra hne
      have hmem : F a b y ∈ wsp F (ν + rt a b) ⊓ S :=
        Submodule.mem_inf.mpr ⟨wt_shift hF.gl hyw a b, hst a b y hyS⟩
      have hM' := hM (ν + rt a b) (by
        intro h
        rw [h] at hmem
        exact hne ((Submodule.mem_bot ℂ).mp hmem))
      have h1 := hM' (rhoV n) (rhoV_anti n)
      rw [dot_add, dot_rt] at h1
      have hlt : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
      have h2 : rhoV n b < rhoV n a := by
        simp only [rhoV]
        linarith
      linarith
    exact Submodule.mem_inf.mpr ⟨hk, hyS⟩
  · intro y hy
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hy
    exact Submodule.mem_inf.mpr ⟨(show KHighest (fun _ : Fin n => true) F ν y from h1).1, h2⟩
end
end
