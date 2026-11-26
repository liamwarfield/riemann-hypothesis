module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruence
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruence
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.TorusConj

theorem conj_sub_one_mem {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι]
    {P : ι → E} (hP : GlobalTheory.CompanionTheory.Iwahori.IsPieces P) {J : AddSubgroup E}
    (hJ : GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P)
    (hc : ∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J)
    {S S' : E} {σ ρ : ι → L} (hS : ∀ i, P i * S = σ i • P i)
    (hS' : ∀ j, S' * P j = ρ j • P j) (hSS : S * S' = 1) {a : E} (ha : a - 1 ∈ J)
    (h : ∀ i j, ‖σ i * ρ j‖ ≤ 1 ∨ (i ≠ j ∧ P i * a * P j = 0)) :
    S * a * S' - 1 ∈ J := by
  have e1 : S * a * S' - 1 = ∑ i, ∑ j, P i * (S * (a - 1) * S') * P j := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [hP.sum]
    simp [mul_sub, sub_mul, hSS]
  rw [e1]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  have e2 : P i * (S * (a - 1) * S') * P j = (σ i * ρ j) • (P i * (a - 1) * P j) := by
    calc P i * (S * (a - 1) * S') * P j = (P i * S) * (a - 1) * (S' * P j) := by
          simp only [mul_assoc]
      _ = (σ i * ρ j) • (P i * (a - 1) * P j) := by
          rw [hS, hS']
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
          rw [mul_comm]
  rw [e2]
  rcases h i j with hn | ⟨hij, hz⟩
  · exact hc _ hn _ (hJ.right_mem j _ (hJ.left_mem i _ ha))
  · have : P i * (a - 1) * P j = 0 := by
      rw [mul_sub, sub_mul, hz, mul_one, hP.orth i j hij, sub_zero]
    rw [this, smul_zero]
    exact J.zero_mem

theorem conj_congruence {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι]
    (wt : ι → ℕ) (P : ι → E) (hP : GlobalTheory.CompanionTheory.Iwahori.IsPieces P) (J : AddSubgroup E)
    (hJ : GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P)
    (hc : ∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J) (T T' : E) (τ : ι → L)
    (hτ : ∀ i, τ i ≠ 0) (hTT : T * T' = 1) (hTT' : T' * T = 1)
    (hl : ∀ i, T * P i = τ i • P i) (hr : ∀ i, P i * T = τ i • P i)
    (hw : ∀ i j, wt i ≤ wt j → ‖τ i‖ ≤ ‖τ j‖) (a b : E) (ha : a - 1 ∈ J) (hb : b - 1 ∈ J)
    (hU : GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a) (hL : GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b) :
    T * a * T' - 1 ∈ J ∧ T' * b * T - 1 ∈ J := by
  have hl' : ∀ j, T' * P j = (τ j)⁻¹ • P j := by
    intro j
    have e : T' * (T * P j) = T' * (τ j • P j) := by rw [hl]
    rw [← mul_assoc, hTT', one_mul, mul_smul_comm] at e
    rw [eq_inv_smul_iff₀ (hτ j)]
    exact e.symm
  have hr' : ∀ j, P j * T' = (τ j)⁻¹ • P j := by
    intro j
    have e : (P j * T) * T' = (τ j • P j) * T' := by rw [hr]
    rw [mul_assoc, hTT, mul_one, smul_mul_assoc] at e
    rw [eq_inv_smul_iff₀ (hτ j)]
    exact e.symm
  constructor
  · refine conj_sub_one_mem hP hJ hc hr hl' hTT ha fun i j => ?_
    by_cases hij : wt j < wt i
    · exact Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hU i j hij⟩
    · left
      have hn := hw i j (not_lt.mp hij)
      have hpos : 0 < ‖τ j‖ := norm_pos_iff.mpr (hτ j)
      rw [norm_mul, norm_inv, ← div_eq_mul_inv]
      exact (div_le_one hpos).mpr hn
  · refine conj_sub_one_mem hP hJ hc hr' hl hTT' hb fun i j => ?_
    by_cases hij : wt i < wt j
    · exact Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hL i j hij⟩
    · left
      have hn := hw j i (not_lt.mp hij)
      have hpos : 0 < ‖τ i‖ := norm_pos_iff.mpr (hτ i)
      rw [norm_mul, norm_inv, inv_mul_eq_div]
      exact (div_le_one hpos).mpr hn

end GlobalTheory.CompanionTheory.Iwahori.TorusConj
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruenceStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_conjugation_preserves_congruence : ∀ {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E, GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → (∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J) → ∀ (T T' : E) (τ : ι → L), (∀ i, τ i ≠ 0) → T * T' = 1 → T' * T = 1 → (∀ i, T * P i = τ i • P i) → (∀ i, P i * T = τ i • P i) → (∀ i j, wt i ≤ wt j → ‖τ i‖ ≤ ‖τ j‖) → ∀ a b : E, a - 1 ∈ J → b - 1 ∈ J → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → T * a * T' - 1 ∈ J ∧ T' * b * T - 1 ∈ J := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence | exact GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence | (intros; apply GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExists
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExists
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

theorem exists_adjoint_herm : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h →
    ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by
  intro L V _ _ _ _ s hs h hh g
  obtain ⟨hadd2, hsmul2, hsymm, hnd⟩ := hh
  have hss := hs.1
  have hadd1 : ∀ x x' y, h (x + x') y = h x y + h x' y := by
    intro x x' y
    rw [hsymm y (x + x'), hadd2, map_add (f := _), ← hsymm, ← hsymm]
  have hsmul1 : ∀ (a : L) x y, h (a • x) y = s a * h x y := by
    intro a x y
    rw [hsymm y (a • x), hsmul2, map_mul, ← hsymm]

  let ψ₀ : V → Module.Dual L V := fun x =>
    { toFun := h x
      map_add' := hadd2 x
      map_smul' := fun a y => by simpa using hsmul2 a x y }
  have ψ₀_apply : ∀ x y, ψ₀ x y = h x y := fun _ _ => rfl
  let ψ : V →+ Module.Dual L V := AddMonoidHom.mk' ψ₀ (fun x x' => by
    ext y
    simp [ψ₀_apply, hadd1])
  have ψ_apply : ∀ x y, ψ x y = h x y := fun _ _ => rfl
  have ψ_smul : ∀ (a : L) x, ψ (a • x) = s a • ψ x := by
    intro a x
    ext y
    simp [ψ_apply, hsmul1]
  have ψ_inj : ∀ x, ψ x = 0 → x = 0 := by
    intro x hx
    exact hnd x (fun y => by rw [← ψ_apply, hx]; rfl)
  have ψ_inj' : ∀ x x', ψ x = ψ x' → x = x' := by
    intro x x' hxx
    exact sub_eq_zero.mp (ψ_inj _ (by rw [map_sub, hxx, sub_self]))

  let b := Module.finBasis L V
  have hli : LinearIndependent L (fun i => ψ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ψ (∑ j, s (c j) • b j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ψ_smul, hss]
    have h1 := ψ_inj _ h0
    have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
    have h3 := congrArg s h2
    rwa [hss, map_zero] at h3
  have hspan : Submodule.span L (Set.range fun i => ψ (b i)) = ⊤ := by
    refine hli.span_eq_top_of_card_eq_finrank' ?_
    rw [Subspace.dual_finrank_eq]
    simp
  have ψ_surj : ∀ f : Module.Dual L V, ∃ z, ψ z = f := by
    intro f
    have hf : f ∈ Submodule.span L (Set.range fun i => ψ (b i)) := by
      rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hf
    refine ⟨∑ j, s (c j) • b j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hc]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ψ_smul, hss]
  choose z hz using fun y => ψ_surj ((ψ y).comp g)
  have hz' : ∀ y x, h (z y) x = h y (g x) := by
    intro y x
    rw [← ψ_apply, hz]
    rfl
  refine ⟨{ toFun := z, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro y y'
    apply ψ_inj'
    rw [hz, map_add (f := _), map_add (f := _), hz, hz]
    rfl
  · intro a y
    apply ψ_inj'
    rw [hz, RingHom.id_apply, ψ_smul, ψ_smul, hz]
    rfl
  · intro x y
    show h (g x) y = h x (z y)
    rw [hsymm (z y) x, hz', ← hsymm]

end GlobalTheory.CompanionTheory.Iwahori
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExistsStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_adjoint_exists : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h → ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm | exact GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm | (intros; apply GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntiInvolutionSwapsUpperLower
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntiInvolutionSwapsUpperLower
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.Unitary

variable {E ι : Type} [Ring E] [Fintype ι]

theorem piece_mul_mul {P : ι → E} (hP : IsPieces P) (x y : E) (i j : ι) :
    P i * (x * y) * P j = ∑ k, (P i * x * P k) * (P k * y * P j) := by
  have h : x * y = ∑ k, x * P k * y := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP.sum, mul_one]
  rw [h, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := hP.idem k
  calc P i * (x * P k * y) * P j = P i * x * P k * y * P j := by simp only [mul_assoc]
    _ = P i * x * (P k * P k) * y * P j := by rw [hk]
    _ = _ := by simp only [mul_assoc]

theorem upper_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) {x y : E}
    (hx : IsUpper wt P x) (hy : IsUpper wt P y) : IsUpper wt P (x * y) := by
  intro i j hij
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (wt k) (wt i) with h | h
  · rw [hx i k h, zero_mul]
  · rw [hy k j (lt_of_lt_of_le hij h), mul_zero]

theorem lower_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) {x y : E}
    (hx : IsLower wt P x) (hy : IsLower wt P y) : IsLower wt P (x * y) := by
  intro i j hij
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (wt i) (wt k) with h | h
  · rw [hx i k h, zero_mul]
  · rw [hy k j (lt_of_le_of_lt h hij), mul_zero]

theorem diag_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {x y : E} (hx : IsLower wt P x) (hy : IsLower wt P y) (i : ι) :
    P i * (x * y) * P i = (P i * x * P i) * (P i * y * P i) := by
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_trichotomy (wt i) (wt k) with h | h | h
  · rw [hx i k h, zero_mul]
  · exact absurd (hw h).symm hk
  · rw [hy k i h, mul_zero]

theorem lowerUni_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {x y : E} (hx : IsLowerUni wt P x) (hy : IsLowerUni wt P y) : IsLowerUni wt P (x * y) :=
  ⟨lower_mul hP hx.1 hy.1, fun i => by
    rw [diag_mul hP hw hx.1 hy.1, hx.2, hy.2, hP.idem]⟩

theorem lowerUni_of_inv {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {b b' : E} (hb : IsLowerUni wt P b) (hb' : IsLower wt P b') (h : b * b' = 1) :
    IsLowerUni wt P b' := by
  refine ⟨hb', fun i => ?_⟩
  have h1 := diag_mul hP hw hb.1 hb' i
  rw [h, mul_one, hP.idem, hb.2] at h1
  calc P i * b' * P i = P i * (P i * b' * P i) := by simp only [← mul_assoc, hP.idem]
    _ = P i := h1.symm

theorem eq_one_of_upper_lowerUni {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P)
    (hw : Function.Injective wt) {c : E} (hu : IsUpper wt P c) (hl : IsLowerUni wt P c) :
    c = 1 := by
  have h : c = ∑ i, ∑ j, P i * c * P j := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hP.sum, mul_one, one_mul]
  rw [h, ← hP.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_eq_single i (fun j _ hj => ?_)
    (fun h => absurd (Finset.mem_univ i) h)).trans (hl.2 i)
  rcases lt_trichotomy (wt i) (wt j) with h | h | h
  · exact hl.1 i j h
  · exact absurd (hw h).symm hj
  · exact hu i j h

section Anti

variable {wt : ι → ℕ} {P : ι → E} {rev : ι → ι} {st : E → E}

theorem st_block (hrev : ∀ i, rev (rev i) = i) (hmul : ∀ a b, st (a * b) = st b * st a)
    (hst : ∀ i, st (P i) = P (rev i)) (x : E) (i j : ι) :
    P i * st x * P j = st (P (rev j) * x * P (rev i)) := by
  rw [hmul, hmul, hst, hst, hrev, hrev, mul_assoc]

theorem st_upper (hrev : ∀ i, rev (rev i) = i) (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsUpper wt P x) : IsUpper wt P (st x) := by
  intro i j hij
  rw [st_block hrev hmul hst, hx (rev j) (rev i) (hord j i hij), h0]

theorem st_lower (hrev : ∀ i, rev (rev i) = i) (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsLower wt P x) : IsLower wt P (st x) := by
  intro i j hij
  rw [st_block hrev hmul hst, hx (rev j) (rev i) (hord i j hij), h0]

theorem st_lowerUni (hrev : ∀ i, rev (rev i) = i)
    (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsLowerUni wt P x) :
    IsLowerUni wt P (st x) :=
  ⟨st_lower hrev hord hmul h0 hst hx.1, fun i => by
    rw [st_block hrev hmul hst, hx.2, hst, hrev]⟩

end Anti

theorem st_mul_self_of_factor : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ (rev : ι → ι), (∀ i, rev (rev i) = i) → (∀ i j, wt i < wt j → wt (rev j) < wt (rev i)) → Function.Injective wt → ∀ (st : E → E), (∀ a b, st (a * b) = st b * st a) → st 1 = 1 → st 0 = 0 → (∀ i, st (P i) = P (rev i)) → (∀ a a' : E, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a') → (∀ b b' : E, b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b') → ∀ a a' b b' : E, a * a' = 1 → a' * a = 1 → b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b → st (a * b) * (a * b) = 1 → (a * b) * st (a * b) = 1 → st a * a = 1 ∧ st b * b = 1 := by
  intro E ι _ _ wt P hP rev hrev hord hw st hmul h1 h0 hst hU hL a a' b b' haa' ha'a hbb' hb'b ha hb hs hs'
  have ha'U : IsUpper wt P a' := hU a a' haa' ha'a ha
  have hb'Uni : IsLowerUni wt P b' := lowerUni_of_inv hP hw hb (hL b b' hbb' hb'b hb.1) hbb'
  have ha2U : IsUpper wt P (st a') := st_upper hrev hord hmul h0 hst ha'U
  have hstb : IsLowerUni wt P (st b) := st_lowerUni hrev hord hmul h0 hst hb

  have e1 : st a * st a' = 1 := by rw [← hmul, ha'a, h1]
  have e2 : st b' * st b = 1 := by rw [← hmul, hbb', h1]
  have e3 : st b * st b' = 1 := by rw [← hmul, hb'b, h1]

  have e4 : st a' * st b' = a * b := by
    have h2 : st (a * b) * (st a' * st b') = 1 := by
      rw [hmul a b, mul_assoc (st b), ← mul_assoc (st a), e1, one_mul, e3]
    calc st a' * st b' = (a * b) * st (a * b) * (st a' * st b') := by rw [hs', one_mul]
      _ = a * b := by rw [mul_assoc, h2, mul_one]
  have e5 : st a' = a * b * st b := by
    rw [← e4, mul_assoc, e2, mul_one]

  have e6 : a' * st a' = b * st b := by
    have h3 : a' * (a * b * st b) = (a' * a) * b * st b := by simp only [mul_assoc]
    rw [e5, h3, ha'a, one_mul]
  have hc : a' * st a' = 1 :=
    eq_one_of_upper_lowerUni hP hw (upper_mul hP ha'U ha2U)
      (e6 ▸ lowerUni_mul hP hw hb hstb)
  have e7 : st a' = a := by
    calc st a' = a * a' * st a' := by rw [haa', one_mul]
      _ = a := by rw [mul_assoc, hc, mul_one]
  have e8 : st b' = b := by
    have : a * st b' = a * b := by rw [← e4, e7]
    calc st b' = a' * a * st b' := by rw [ha'a, one_mul]
      _ = a' * a * b := by rw [mul_assoc, this, mul_assoc]
      _ = b := by rw [ha'a, one_mul]
  rw [e7] at e1
  rw [e8] at e3
  exact ⟨e1, e3⟩

end GlobalTheory.CompanionTheory.Iwahori.Unitary
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntiInvolutionSwapsUpperLowerStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_factors_of_unitary_upper_mul_lowerUni : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ (rev : ι → ι), (∀ i, rev (rev i) = i) → (∀ i j, wt i < wt j → wt (rev j) < wt (rev i)) → Function.Injective wt → ∀ (st : E → E), (∀ a b, st (a * b) = st b * st a) → st 1 = 1 → st 0 = 0 → (∀ i, st (P i) = P (rev i)) → (∀ a a' : E, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a') → (∀ b b' : E, b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b') → ∀ a a' b b' : E, a * a' = 1 → a' * a = 1 → b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b → st (a * b) * (a * b) = 1 → (a * b) * st (a * b) = 1 → st a * a = 1 ∧ st b * b = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor | exact GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor | (intros; apply GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor <;> assumption)
end
end
