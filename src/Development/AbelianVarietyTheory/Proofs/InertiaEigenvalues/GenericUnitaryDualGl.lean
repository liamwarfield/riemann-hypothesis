module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentLinkedShift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardModuleProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardModuleProperties
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.LocGL.IrrProdL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_eq_of_isL {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {𝔪 : Multiset (Segment k)} (h : IsL 𝔪 π) : (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, ⟨Δ, ⟨rfl, -⟩, hΔ⟩, -⟩ := h
  rw [← hd, Multiset.map_map]
  exact Finset.sum_congr rfl fun i _ => (hΔ i).deg_eq

theorem isL_add [CharZero k] (H : GlobalTheory.Published.LanglandsMultisegments) {𝔪 𝔫 : Multiset (Segment k)} (x t y : IrrGL (k := k))
    (hx : IsL 𝔪 x.rep) (ht : IsL 𝔫 t.rep) (hy : IsL (𝔪 + 𝔫) y.rep)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (x.1 + t.1)) k) V)
    (hπ : π.IsIrreducible) (φ : π.Equiv (prod₂ x.rep t.rep)) : IsL (𝔪 + 𝔫) π := by
  have e : y.1 = x.1 + t.1 := by
    rw [← deg_eq_of_isL hy, ← deg_eq_of_isL hx, ← deg_eq_of_isL ht, Multiset.map_add (f := _), Multiset.sum_add]
  obtain ⟨n, c⟩ := y
  dsimp only at e
  subst e
  have hd : ∑ a, (![x, t] a).1 = x.1 + t.1 := Fin.sum_univ_two _
  have hs := (H k).2 𝔪 𝔫 ![x, t] ⟨x.1 + t.1, c⟩ hd hx ht hy
  obtain ⟨ψ⟩ := nonempty_prod₂_equiv_prodIrr_pair x t hd
  let χ := φ.trans ψ
  have hs' := hs.trans (IsSubquotient.of_surjective χ.toIntertwiningMap χ.toLinearEquiv.surjective)
  obtain ⟨ω⟩ := IsSubquotient.nonempty_equiv hs' hy.irr_smooth.1 hπ
  exact hy.of_equiv ω.symm

theorem isL_sum_of_isIrreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π := by
  intro k _ _ _ _ _ H P hP h
  induction h with
  | zero =>
    rintro N x hd 𝔪 - - V _ _ π hπ ⟨φ⟩
    refine ⟨0, x, hd, ⟨Fin.elim0, ⟨by simp, fun i => i.elim0⟩, fun i => i.elim0⟩, ?_⟩
    exact (isCosocle_self hπ).of_equiv (.refl _) φ
  | succ h ih =>
    rintro N x hd 𝔪 hL hm V _ _ π hπ ⟨φ⟩
    have e : N = (x 0).1 + ∑ i : Fin h, (x i.succ).1 := hd.symm.trans (Fin.sum_univ_succ _)
    subst e
    obtain ⟨ψ⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ (fun a => (x a).1) hd fun a => (x a).rep
    let τ := prodIrr (fun i : Fin h => x i.succ) rfl
    have hτs : IsSmooth τ := isSmooth_prodIrr _ _
    have χ : π.Equiv (prod₂ (x 0).rep τ) := φ.trans ψ.symm
    have hτi : τ.IsIrreducible := GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ k _ _ _ _ _ (x 0).rep τ π
      (x 0).2.rep.smooth (x 0).2.rep.irr hτs hπ ⟨χ⟩
    have hτ : IsL (∑ i : Fin h, 𝔪 i.succ) τ :=
      ih _ (fun i => x i.succ) rfl (fun i => 𝔪 i.succ) (fun i => hL _) (fun i => hm _) _ τ hτi ⟨.refl _⟩
    obtain ⟨y, hy⟩ := hP (∑ j, 𝔪 j) fun Δ hΔ => by
      obtain ⟨j, -, hj⟩ := Multiset.mem_sum.1 hΔ
      exact hm j Δ hj
    rw [Fin.sum_univ_succ] at hy ⊢
    exact isL_add H (x 0) (IrrGL.of τ hτs hτi) y (hL 0) (hτ.of_equiv (IrrGL.equivOf τ hτs hτi)) hy π hπ
      (χ.trans (prod₂Equiv (.refl _) (IrrGL.equivOf τ hτs hτi)))

end GlobalTheory.LocGL.IrrProdL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardModulePropertiesStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_module_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π := by
  first | exact @GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible | exact GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible | (intros; apply GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationUnitary
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.LocGL

theorem exists_isL_of_unitary_twists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (hS : GlobalTheory.Published.StandardCosocleGL)
    (hP : ∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y)
    (𝔫 : Multiset (Segment k))
    (h𝔫 : ∀ Δ ∈ 𝔫, ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) : ∃ y : IrrGL (k := k), IsL 𝔫 y.rep := by
  classical
  have h' : ∀ Δ ∈ 𝔫, ∃ (t : ℝ) (δ : IrrGL (k := k)) (Γ : Segment k), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ) := fun Δ h =>
    let ⟨δ, Γ, t, h⟩ := h𝔫 Δ h
    ⟨t, δ, Γ, h⟩
  choose! t ht using h'
  let r : Segment k → Segment k → Prop := fun a b => t b ≤ t a
  haveI : IsTrans (Segment k) r := ⟨fun a b c h1 h2 => le_trans h2 h1⟩
  haveI : Std.Total r := ⟨fun a b => le_total _ _⟩
  obtain ⟨l, hl, hs⟩ : ∃ l : List (Segment k), (l : Multiset (Segment k)) = 𝔫 ∧ l.Pairwise r :=
    ⟨𝔫.toList.insertionSort r,
      (Multiset.coe_eq_coe.2 (List.perm_insertionSort r _)).trans (Multiset.coe_toList 𝔫),
      List.pairwise_insertionSort r _⟩
  have hm : ∀ i : Fin l.length, l.get i ∈ 𝔫 := fun i => by
    rw [← hl]; exact List.get_mem l i
  choose δ Γ hL hU hE using fun i : Fin l.length => ht _ (hm i)
  have hF : LFactors 𝔫 (fun i : Fin l.length => (δ i).nu (t (l.get i))) := by
    refine ⟨fun i => (Γ i).nu (t (l.get i)), ⟨?_, fun i j hij h => ?_⟩, fun i => ?_⟩
    · rw [← hl, ← funext hE]
      simp
    · have h1 : t (l.get j) ≤ t (l.get i) := List.pairwise_iff_get.1 hs i j hij
      have := hP _ _ _ _ (hL i) (hU i) (hL j) (hU j) _ _ h
      linarith
    · exact ((hL i).tw _ (isSmoothChar_absPow _)).of_equiv ((δ i).twEquiv _ _)
  obtain ⟨π, hπ⟩ := hS k 𝔫 _ _ _ rfl hF
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, _, _, rfl, hF, hπ.of_equiv (IrrGL.equivOf _ _ _) (.refl _)⟩

end GlobalTheory.LocGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationUnitaryStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_classification_unitary : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep := by
  first | exact @GlobalTheory.LocGL.exists_isL_of_unitary_twists | exact GlobalTheory.LocGL.exists_isL_of_unitary_twists | (intros; apply GlobalTheory.LocGL.exists_isL_of_unitary_twists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGl
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel GlobalTheory.UnitaryDual GlobalTheory.GenericUnitary

namespace GlobalTheory.GenericUnitaryBridge

theorem eq_of_isSpeh_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ w : IrrGL (k := k)} (h : IsSpeh δ 1 w.rep) : w = δ := by
  obtain ⟨n, c⟩ := w
  obtain ⟨n', c'⟩ := δ
  obtain ⟨hd1, hc1⟩ := h
  obtain ⟨hd2, hc2⟩ := isSpeh_one (⟨n', c'⟩ : IrrGL (k := k))
  obtain rfl : n = n' := hd1.symm.trans hd2
  obtain ⟨φ⟩ := hc2.unique hc1
  exact ((IrrGL.of_rep _).symm.trans (IrrGL.of_eq_of.2 ⟨φ⟩)).trans (IrrGL.of_rep _)

theorem of_lemmas (hA : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) (hB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π) (hD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (δ x : IrrGL (k := k)) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep) (hF : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ), (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ))) :
    GlobalTheory.Published.UnitaryDualGL → GlobalTheory.Published.SquareIntegrableSegment → GlobalTheory.Published.GenericUnlinkedGL →
      GlobalTheory.Published.LanglandsMultisegments → GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.GenericUnitaryDualGL := by
  intro hU hSq hGen hLM hSC k _ _ _ _ _ N V _ _ π hs hi hu hg
  have ord := GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes k
  let Good : Segment k → Prop := fun Δ => ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)
  have key : ∀ (w : IrrGL (k := k)) (r : ℝ), IsUnitarySpeh w → ∃ 𝔫 : Multiset (Segment k), IsL 𝔫 (w.nu (r : ℂ)).rep ∧
      (∀ Γ ∈ 𝔫, Good Γ) ∧ (IsUnitaryLSeg w ∨ ∃ (Γ : Segment k) (t : ℝ), Γ.nu (t : ℂ) ∈ 𝔫 ∧
        Γ.nu ((t - 1 : ℝ) : ℂ) ∈ 𝔫) := by
    rintro w r ⟨δ, m, hsq, hm, hsp⟩
    obtain ⟨Δ, hΔ⟩ := hSq k δ hsq
    refine ⟨_, hD k ord δ w Δ m hΔ hsq.2.1 hsp r, ?_, ?_⟩
    · intro Γ hΓ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hΓ)
      exact ⟨δ, Δ, _, hΔ, hsq.2.1, rfl⟩
    · rcases Nat.lt_or_ge m 2 with h2 | h2
      · left
        obtain rfl : m = 1 := by omega
        obtain rfl := eq_of_isSpeh_one hsp
        exact ⟨⟨Δ, hΔ⟩, hsq.2.1⟩
      · right
        refine ⟨Δ, r + ((m : ℝ) - 1) / 2, Multiset.mem_coe.2 (List.mem_ofFn.2 ⟨⟨0, by omega⟩, ?_⟩),
          Multiset.mem_coe.2 (List.mem_ofFn.2 ⟨⟨1, by omega⟩, ?_⟩)⟩
        · simp
        · congr 2
          push_cast
          ring
  obtain ⟨u, τ, hu1, hτ1, h, x, hd, hx, ⟨φ⟩⟩ := hU k N V π hs hi hu
  have hfac : ∀ j, ∃ (y : IrrGL (k := k)) (s : ℝ), IsUnitarySpeh y ∧ x j = y.nu (s : ℂ) := by
    intro j
    have hm : x j ∈ factors u τ := hx ▸ List.mem_ofFn.2 ⟨j, rfl⟩
    rcases List.mem_append.1 hm with hm | hm
    · exact ⟨x j, 0, hu1 _ hm, by simp⟩
    · obtain ⟨p, hp, hm⟩ := List.mem_flatMap.1 hm
      rcases List.mem_pair.1 hm with e | e
      · exact ⟨p.1, p.2, (hτ1 p hp).1, e⟩
      · exact ⟨p.1, -p.2, (hτ1 p hp).1, e⟩
  choose y s hy hxs using hfac
  have h𝔪 : ∀ j, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 (x j).rep ∧ ∀ Γ ∈ 𝔪, Good Γ := fun j => by
    obtain ⟨𝔪, h1, h2, -⟩ := key (y j) (s j) (hy j)
    exact ⟨𝔪, hxs j ▸ h1, h2⟩
  choose 𝔪 h𝔪L h𝔪G using h𝔪
  have hL : IsL (∑ j, 𝔪 j) π :=
    hB k hLM Good (fun 𝔫 h𝔫 => hA k hSC ord 𝔫 h𝔫) h N x hd 𝔪 h𝔪L h𝔪G V π hi ⟨φ⟩
  obtain ⟨h', Δ', z, hd', hunl, hz, ⟨ψ⟩⟩ := hGen k N V π hs hi hg
  have hL' : IsL (Finset.univ.val.map Δ') π :=
    ⟨h', z, hd', ⟨Δ', ⟨rfl, fun i j hij hP => hunl i j hij.ne hP.1⟩, hz⟩,
      (isCosocle_self hi).of_equiv (.refl _) ψ⟩
  have heq : ∑ j, 𝔪 j = Finset.univ.val.map Δ' :=
    (hLM k).1 _ _ (IrrGL.of π hs hi) (hL.of_equiv (IrrGL.equivOf π hs hi)) (hL'.of_equiv (IrrGL.equivOf π hs hi))
  have hno : ∀ Γ ∈ ∑ j, 𝔪 j, ∀ Γ' ∈ ∑ j, 𝔪 j, ¬ Γ.Linked Γ' := by
    rw [heq]
    intro Γ hΓ Γ' hΓ' hl
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hΓ
    obtain ⟨i', -, rfl⟩ := Multiset.mem_map.1 hΓ'
    by_cases e : i = i'
    · subst e
      exact Segment.not_linked_self _ hl
    · exact hunl i i' e hl
  have hgood : ∀ (w : IrrGL (k := k)) (r : ℝ), IsUnitarySpeh w → w.nu (r : ℂ) ∈ List.ofFn x → IsUnitaryLSeg w := by
    intro w r hw hmem
    obtain ⟨j, hj⟩ := List.mem_ofFn.1 hmem
    obtain ⟨𝔫, h1, -, h3⟩ := key w r hw
    rcases h3 with h3 | ⟨Γ, t, h4, h5⟩
    · exact h3
    · have e : 𝔫 = 𝔪 j := (hLM k).1 _ _ (x j) (hj ▸ h1) (h𝔪L j)
      subst e
      exact absurd (hF k Γ t) (hno _ (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h4⟩) _
        (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h5⟩))
  refine ⟨u, τ, fun w hw => hgood w 0 (hu1 w hw) ?_, fun p hp => ⟨hgood p.1 p.2 (hτ1 p hp).1 ?_, (hτ1 p hp).2⟩,
    h, x, hd, hx, ⟨φ⟩⟩
  · rw [hx]
    simp only [Complex.ofReal_zero, IrrGL.nu_zero]
    exact List.mem_append_left _ hw
  · rw [hx]
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, by simp⟩)

theorem genericUnitaryDualGL_of_hypotheses : GlobalTheory.Published.UnitaryDualGL → GlobalTheory.Published.SquareIntegrableSegment →
    GlobalTheory.Published.GenericUnlinkedGL → GlobalTheory.Published.LanglandsMultisegments → GlobalTheory.Published.StandardCosocleGL →
    GlobalTheory.Published.GenericUnitaryDualGL :=
  of_lemmas GlobalTheory.T.langlands_classification_unitary GlobalTheory.T.standard_module_properties GlobalTheory.T.speh_langlands_quotient GlobalTheory.T.segment_linked_shift

end GlobalTheory.GenericUnitaryBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGlStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_unitary_dual_gl : GlobalTheory.Published.UnitaryDualGL → GlobalTheory.Published.SquareIntegrableSegment → GlobalTheory.Published.GenericUnlinkedGL → GlobalTheory.Published.LanglandsMultisegments → GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.GenericUnitaryDualGL := by
  first | exact @GlobalTheory.GenericUnitaryBridge.genericUnitaryDualGL_of_hypotheses | exact GlobalTheory.GenericUnitaryBridge.genericUnitaryDualGL_of_hypotheses | (intros; apply GlobalTheory.GenericUnitaryBridge.genericUnitaryDualGL_of_hypotheses <;> assumption)
end
