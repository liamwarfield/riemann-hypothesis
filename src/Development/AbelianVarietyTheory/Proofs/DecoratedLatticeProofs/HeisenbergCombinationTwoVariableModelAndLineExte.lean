module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceSourceLine
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOConstMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
namespace GlobalTheory.BiComb

variable {D : D7}

theorem heisO_resS_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (F : WO V S → ℂ)
    (w u : WO A S) (v : WO L S) :
    heisO ψ V S ((o.resS S).symm (w, 0)) F ((o.resS S).symm (u, v)) =
      heisO ψ A S w (fun u' => F ((o.resS S).symm (u', v))) u := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem heisO_resT_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (F : WO S V → ℂ)
    (w u : WO S A) (v : WO S L) :
    heisO ψ S V ((o.resT S).symm (w, 0)) F ((o.resT S).symm (u, v)) =
      heisO ψ S A w (fun u' => F ((o.resT S).symm (u', v))) u := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem comb_resS_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (c : WO A S →₀ ℂ)
    (F : WO V S → ℂ) (u : WO A S) (v : WO L S) :
    comb ψ V S (c.mapDomain fun w => (o.resS S).symm (w, 0)) F ((o.resS S).symm (u, v)) =
      comb ψ A S c (fun u' => F ((o.resS S).symm (u', v))) u := by
  classical
  have hinj : Function.Injective fun w : WO A S => (o.resS S).symm (w, 0) := fun a b h => by
    have := congrArg (o.resS S) h
    simp only [AddEquiv.apply_symm_apply, Prod.mk.injEq, and_true] at this
    exact this
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hinj, heisO_resS_slice]

theorem comb_resT_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (c : WO S A →₀ ℂ)
    (F : WO S V → ℂ) (u : WO S A) (v : WO S L) :
    comb ψ S V (c.mapDomain fun w => (o.resT S).symm (w, 0)) F ((o.resT S).symm (u, v)) =
      comb ψ S A c (fun u' => F ((o.resT S).symm (u', v))) u := by
  classical
  have hinj : Function.Injective fun w : WO S A => (o.resT S).symm (w, 0) := fun a b h => by
    have := congrArg (o.resT S) h
    simp only [AddEquiv.apply_symm_apply, Prod.mk.injEq, and_true] at this
    exact this
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hinj, heisO_resT_slice]

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isOne (Y Y' : Type) [Fintype Y] [Fintype Y'] : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} := GlobalTheory.SplitFlip.isCompact_intMatrix
  exact ⟨⟨_, GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB hc ⟨hc.isClosed, GlobalTheory.SplitFlip.isOpen_intMatrix⟩⟩, rfl⟩

end Loc

theorem source_slice_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := GlobalTheory.T.exists_local_model_slice_source_line

theorem target_slice_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := GlobalTheory.T.exists_local_model_slice_target_line

theorem comb_bimodel_and_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''], (∀ (A S A' : HSp D) (FA : Frame k A.rank n') (FS : Frame k S.rank n) (FA' : Frame k A'.rank n'') Λ c c' (Ξ₁ O₁ : SB (Matrix n n' k)) (Ξ₂ O₂ : SB (Matrix n'' n k)) (Ξ O : SB (Matrix n n' k × Matrix n'' n k)), p.IsBiModel ψ FA FS FA' Λ → p.IsCombAt ψ FA FS c Ξ₁.1 → p.IsCombAt ψ FS FA' c' Ξ₂.1 → IsOne O₁ → IsOne O₂ → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → (∀ q, O.1 q = O₁.1 q.1 * O₂.1 q.2) → Λ Ξ = biComb ψ A S A' c c' (Λ O)) ∧ ∀ (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), IsStdChar D ψ (-1) → p.IsCoreFrame B s FA F₀ → (∀ T₀ c (Ξ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ F₀ FS T₀ → p.IsCombAt ψ FA FS c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toCols₁ * a fun r => x r (Sum.inr ())) → (∀ x, O.1 x = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ * a fun r => x r (Sum.inr ())) → T₀ Ψ = comb ψ B.V₀ S (c.mapDomain fun w => (B.o.resS S).symm (w, 0)) (T₀ O)) ∧ ∀ T₀ c (Ξ : Matrix n' n k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ FS F₀ T₀ → p.IsCombAt ψ FS FA c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toRows₁ * a (x (Sum.inr ()))) → (∀ x, O.1 x = Set.indicator {x : Matrix n' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toRows₁ * a (x (Sum.inr ()))) → T₀ Ψ = comb ψ S B.V₀ (c.mapDomain fun w => (B.o.resT S).symm (w, 0)) (T₀ O) := by
  intro D k _ _ _ _ p ψ n n' n'' _ _ _ _ _ _
  refine ⟨?_, ?_⟩
  · intro A S A' FA FS FA' Λ c c' Ξ₁ O₁ Ξ₂ O₂ Ξ O hΛ hc hc' hO₁ hO₂ hΞ hO
    funext u v
    obtain ⟨T₁, hT₁, e₁⟩ := hΛ.1 Ξ₂ v
    let P : SB (Matrix n n' k × Matrix n'' n k) := ⟨_, GlobalTheory.LocFlat.CFac.prodFn_mem_SB O₁.2 Ξ₂.2⟩
    rw [e₁ Ξ₁ Ξ hΞ u, hc.2 T₁ hT₁ O₁ Ξ₁ hO₁ rfl]
    have hf : T₁ O₁ = fun u' => comb ψ S A' c' (Λ O u') v := by
      funext u'
      rw [← e₁ O₁ P (fun q => rfl) u']
      obtain ⟨T₂, hT₂, e₂⟩ := hΛ.2 O₁ u'
      rw [e₂ Ξ₂ P (fun q => rfl) v, hc'.2 T₂ hT₂ O₂ Ξ₂ hO₂ rfl]
      have hg : T₂ O₂ = Λ O u' := funext fun v' => (e₂ O₂ O hO v').symm
      rw [hg]
    rw [hf]
    rfl
  · intro ρ B S s FA F₀ FS _ hF
    refine ⟨?_, ?_⟩
    · intro T₀ c Ξ a Ψ O hT hc hΞ ha hΨ hO
      funext x
      obtain ⟨T₁, hT₁, e⟩ := source_slice_model D k p ψ n n' ρ B S s FA F₀ FS hF T₀ hT a ha (B.o.resS S x).2
      obtain ⟨O₁, hO₁⟩ := exists_isOne (k := k) n n'
      have h1 := hc.2 T₁ hT₁ O₁ ⟨Ξ, hΞ⟩ hO₁ rfl
      have hx : x = (B.o.resS S).symm ((B.o.resS S x).1, (B.o.resS S x).2) := by simp
      rw [hx, e ⟨Ξ, hΞ⟩ Ψ hΨ, h1, comb_resS_slice]
      have hg : T₁ O₁ = fun u' => T₀ O ((B.o.resS S).symm (u', (B.o.resS S x).2)) :=
        funext fun u' => (e O₁ O (fun y => by rw [hO₁]; exact hO y) u').symm
      rw [hg]
    · intro T₀ c Ξ a Ψ O hT hc hΞ ha hΨ hO
      funext x
      obtain ⟨T₁, hT₁, e⟩ := target_slice_model D k p ψ n n' ρ B S s FA F₀ FS hF T₀ hT a ha (B.o.resT S x).2
      obtain ⟨O₁, hO₁⟩ := exists_isOne (k := k) n' n
      have h1 := hc.2 T₁ hT₁ O₁ ⟨Ξ, hΞ⟩ hO₁ rfl
      have hx : x = (B.o.resT S).symm ((B.o.resT S x).1, (B.o.resT S x).2) := by simp
      rw [hx, e ⟨Ξ, hΞ⟩ Ψ hΨ, h1, comb_resT_slice]
      have hg : T₁ O₁ = fun u' => T₀ O ((B.o.resT S).symm (u', (B.o.resT S x).2)) :=
        funext fun u' => (e O₁ O (fun y => by rw [hO₁]; exact hO y) u').symm
      rw [hg]

end GlobalTheory.BiComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCombination_twoVariableModel_and_lineExtension : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''], (∀ (A S A' : HSp D) (FA : Frame k A.rank n') (FS : Frame k S.rank n) (FA' : Frame k A'.rank n'') Λ c c' (Ξ₁ O₁ : SB (Matrix n n' k)) (Ξ₂ O₂ : SB (Matrix n'' n k)) (Ξ O : SB (Matrix n n' k × Matrix n'' n k)), p.IsBiModel ψ FA FS FA' Λ → p.IsCombAt ψ FA FS c Ξ₁.1 → p.IsCombAt ψ FS FA' c' Ξ₂.1 → IsOne O₁ → IsOne O₂ → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → (∀ q, O.1 q = O₁.1 q.1 * O₂.1 q.2) → Λ Ξ = biComb ψ A S A' c c' (Λ O)) ∧ ∀ (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), IsStdChar D ψ (-1) → p.IsCoreFrame B s FA F₀ → (∀ T₀ c (Ξ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ F₀ FS T₀ → p.IsCombAt ψ FA FS c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toCols₁ * a fun r => x r (Sum.inr ())) → (∀ x, O.1 x = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ * a fun r => x r (Sum.inr ())) → T₀ Ψ = comb ψ B.V₀ S (c.mapDomain fun w => (B.o.resS S).symm (w, 0)) (T₀ O)) ∧ ∀ T₀ c (Ξ : Matrix n' n k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ FS F₀ T₀ → p.IsCombAt ψ FS FA c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toRows₁ * a (x (Sum.inr ()))) → (∀ x, O.1 x = Set.indicator {x : Matrix n' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toRows₁ * a (x (Sum.inr ()))) → T₀ Ψ = comb ψ S B.V₀ (c.mapDomain fun w => (B.o.resT S).symm (w, 0)) (T₀ O) := by
  first | exact @GlobalTheory.BiComb.comb_bimodel_and_line | exact GlobalTheory.BiComb.comb_bimodel_and_line | (intros; apply GlobalTheory.BiComb.comb_bimodel_and_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndicatorVac

theorem splitC (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : IsSplitIdem D (cA D q.e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := q.split
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩
  · rw [GlobalTheory.LatVac.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.LatVac.cA_cA, add_comm, h3]

theorem e_eq (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : q.sec 1 = q.e := by
  have := q.sec_pr 1; rw [map_one, mul_one] at this; exact this

theorem mul_e (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (e' : Formalism.L2.Theta.AE D) (he : e' * e' = e') : q.e * e' = 0 ∨ q.e * e' = q.e := by
  have hp : q.pr e' * q.pr e' = q.pr e' := by rw [← map_mul, he]
  rcases (IsIdempotentElem.iff_eq_zero_or_one.1 hp) with h | h
  · left; rw [← q.sec_pr, h, map_zero]
  · right; rw [← q.sec_pr, h, e_eq]

set_option maxHeartbeats 1600000 in
theorem cases (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (e' : Formalism.L2.Theta.AE D) (he' : IsSplitIdem D e') {m n : ℕ} (u : Mx D m n)
    (hsupp : ∀ i j, (q.e + cA D q.e) * u i j = u i j) (hu : IsHalf e' u) :
    u = 0 ∨ IsHalf q.e u ∨ IsHalf (cA D q.e) u := by
  obtain ⟨h1, h2, -⟩ := he'
  have hc1 : cA D e' * cA D e' = cA D e' := by rw [← map_mul, h1]
  have hA := mul_e D k q e' h1
  have hB : cA D q.e * e' = 0 ∨ cA D q.e * e' = cA D q.e := by
    rcases mul_e D k q (cA D e') hc1 with h | h
    · left; have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA, map_zero] at this
    · right; have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA] at this
  have hu' : ∀ i j, u i j = q.e * e' * u i j + cA D q.e * e' * u i j := fun i j => by
    rw [mul_assoc, mul_assoc, hu i j, ← add_mul, hsupp i j]
  have hee : q.e * q.e = q.e := q.split.1
  have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, hee]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · left; ext i j; rw [hu' i j, hA, hB]; simp
  · right; right; intro i j; rw [hu' i j, hA, hB, zero_mul, zero_add, ← mul_assoc, hce]
  · right; left; intro i j; rw [hu' i j, hA, hB, zero_mul, add_zero, ← mul_assoc, hee]
  · exfalso
    have hpe : q.pr q.e = 1 := by rw [← e_eq D k q, q.pr_sec]
    have h7 : q.e = 0 := by
      rcases mul_e D k q (cA D e') hc1 with h | h
      · have h5 : cA D q.e * e' = 0 := by
          have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA, map_zero] at this
        have h6 : cA D q.e = 0 := hB.symm.trans h5
        have := congrArg (cA D) h6; rwa [GlobalTheory.LatVac.cA_cA, map_zero] at this
      · calc q.e = q.e * cA D e' := h.symm
          _ = q.e * e' * cA D e' := by rw [hA]
          _ = 0 := by rw [mul_assoc, h2, mul_zero]
    rw [h7, map_zero] at hpe
    exact zero_ne_one hpe

end GlobalTheory.IndicatorVac


open GlobalTheory.IndicatorVac in
theorem GlobalTheory.LocMod.indicator_vac : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → (∀ Tm O, (ofSplit q).IsModel ψ FS FT Tm → IsOne O → GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) (Tm O)) ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ O, IsOne O → Tm O = f := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ ψk hψ hc hcond LS LT hS hT hFS hFT
  have hmono : ∀ u, u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) → u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    fun u hu => AddSubgroup.closure_mono (fun w hw => by
      obtain ⟨α, h1, _, h3⟩ := hw
      exact ⟨α, h1, fun v hv => absurd trivial hv, h3⟩) hu
  have hsy : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v),
      ψ (symplO S T ((ofSplit q).up FS FT x) u) = 1 := fun x hx u hu =>
    GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (hmono _ (GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx)) (hmono _ hu)
  constructor
  · intro Tm O hTm hO
    have hE : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf q.e u → heisO ψ S T u (Tm O) = Tm O := by
      intro u hu he
      obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT u hu he
      refine (hTm.trans x O O fun t => ?_).symm
      rw [hO]
      have hh : (∀ r s, (t + x) r s ∈ 𝒪[k]) ↔ ∀ r s, t r s ∈ 𝒪[k] := by
        refine ⟨fun h r s => ?_, fun h r s => ?_⟩
        · have := sub_mem (h r s) (hx r s); simpa using this
        · exact add_mem (h r s) (hx r s)
      by_cases ht : ∀ r s, t r s ∈ 𝒪[k]
      · rw [Set.indicator_of_mem (show t ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht),
          Set.indicator_of_mem (show t + x ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hh.2 ht)]
      · rw [Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht),
          Set.indicator_of_notMem (show t + x ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from fun h => ht (hh.1 h))]
    have hC : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf (cA D q.e) u → heisO ψ S T u (Tm O) = Tm O := by
      intro u hu he
      refine (hTm.modul u he O O fun t => ?_).symm
      rw [hO]
      by_cases ht : ∀ r s, t r s ∈ 𝒪[k]
      · rw [hsy t ht u hu, one_mul]
      · rw [Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht), mul_zero]
    refine ⟨hTm.theta O, ?_, ?_⟩
    · intro u hu
      obtain ⟨ha, hsupp⟩ := GlobalTheory.T.completed_hom_lattice_stable_split_idempotent D k q S T LS LT u hu
      set a : WO S T := Matrix.of fun i j => q.e * u i j with ha_def
      have hb : u - a ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) := sub_mem hu ha
      have hee : q.e * q.e = q.e := q.split.1
      have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, hee]
      have haH0 : IsHalf q.e a := fun i j => by
        simp only [ha_def, Matrix.of_apply]; rw [← mul_assoc, hee]
      have hbH0 : IsHalf (cA D q.e) (u - a) := fun i j => by
        have h1 : (u - a) i j = cA D q.e * u i j := by
          simp only [Matrix.sub_apply, ha_def, Matrix.of_apply]
          have := hsupp i j
          linear_combination -this
        rw [h1, ← mul_assoc, hce]
      have haH : IsHalf q.e (a + a) := fun i j => by rw [Matrix.add_apply, mul_add, haH0 i j]
      have hbH : IsHalf (cA D q.e) ((u - a) + (u - a)) := fun i j => by rw [Matrix.add_apply, mul_add, hbH0 i j]
      have h2 : (2 • u : WO S T) = (a + a) + ((u - a) + (u - a)) := by rw [two_nsmul]; abel
      have key := GlobalTheory.LatVac.heisO_heisO ψ (a + a) ((u - a) + (u - a)) (Tm O)
      rw [hC _ (add_mem hb hb) hbH, hE _ (add_mem ha ha) haH, ← h2] at key
      have hph : ψ (symplOH S T (a + a) ((u - a) + (u - a))) = 1 := by
        obtain ⟨x, hx, hxa⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT a ha haH0
        have h3 : symplOH S T (a + a) ((u - a) + (u - a)) = symplO S T a ((u - a) + (u - a)) := by
          rw [symplOH, GlobalTheory.LatVac.symplO_add_left, mul_add, ← add_mul, ← RingHom.map_add (f := _), add_halves,
            RingHom.map_one, one_mul]
        rw [h3]
        have := hsy x hx _ (add_mem hb hb)
        rwa [← hxa] at this
      rw [hph, one_smul] at key
      exact key.symm
    · intro e' he' u hu hue
      rcases cases D k q e' he' u (GlobalTheory.T.completed_hom_lattice_stable_split_idempotent D k q S T LS LT u hu).2 hue with h | h | h
      · subst h; exact GlobalTheory.LatVac.heisO_zero ψ _
      · exact hE u hu h
      · exact hC u hu h
  · intro f hf
    have h78 := GlobalTheory.T.heisenberg_frame_half_inverse D k (ofSplit q) Y Y' S T FS FT ψ ψk hc
    have hth : IsThetaFunO ψ S T f := hf.1
    have hlv : IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) (· = q.v)) f := hf.2
    have h1 : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → heisO ψ S T ((ofSplit q).up FS FT x) f = f :=
      fun x hx => hlv.2 q.e q.split _ (GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx) (h78.1 x).1
    have h2 : ∀ y : WO S T, IsHalf (cA D (ofSplit q).e) y →
        (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) →
        heisO ψ S T y f = f := fun y hy hann =>
      hlv.2 (cA D q.e) (splitC D k q) y
        (GlobalTheory.T.conjugate_half_annihilator_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT ψ ψk hψ hc hcond y hy hann) hy
    obtain ⟨T₁, hT₁, hT₁O⟩ := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k (ofSplit q) Y Y' S T FS FT ψ hψ).2.2 f hth h1 h2
    exact ⟨T₁, hT₁, fun O hO => hT₁O O hO⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → (∀ Tm O, (ofSplit q).IsModel ψ FS FT Tm → IsOne O → GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) (Tm O)) ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ O, IsOne O → Tm O = f := by
  first | exact @GlobalTheory.LocMod.indicator_vac | exact GlobalTheory.LocMod.indicator_vac | (intros; apply GlobalTheory.LocMod.indicator_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocComb

variable {D : D7}

theorem comb_add (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (c + c') f = comb ψ S T c f + comb ψ S T c' f :=
  Finsupp.sum_add_index' (h := fun u (a : ℂ) => a • heisO ψ S T u f) (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • c) f = a • comb ψ S T c f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, GlobalTheory.HeisComb.comb_eq_sum,
    Finsupp.sum_smul_index' (h := fun u (a : ℂ) => a • heisO ψ S T u f) fun _ => zero_smul _ _, Finsupp.smul_sum]
  simp only [smul_eq_mul, mul_smul]

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single y 1) f = heisO ψ S T y f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_single_index (h := fun u (a : ℂ) => a • heisO ψ S T u f) (zero_smul _ _),
    one_smul]

theorem heis_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {e : AE D} {y : WO S T} (hy : IsHalf e y) {c : WO S T →₀ ℂ}
    (hc : ∀ w ∈ c.support, IsHalf e w) :
    ∃ c' : WO S T →₀ ℂ, (∀ w ∈ c'.support, IsHalf e w) ∧ ∀ f, comb ψ S T c' f = heisO ψ S T y (comb ψ S T c f) := by
  obtain ⟨c', h1, h2⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (Finsupp.single y 1) c
  refine ⟨c', fun w hw => ?_, fun f => by rw [h2, comb_single]⟩
  obtain ⟨x, hx, z, hz, rfl⟩ := h1 w hw
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx), add_comm]
  exact (Witness.half_add hy).2 (hc z hz)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']


omit [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] in
theorem trans_mem_SB {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (x : Matrix Y Y' k) :
    (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) :=
  ⟨hΦ.1.comp_continuous (continuous_add_const x), hΦ.2.comp_homeomorph (Homeomorph.addRight x)⟩


omit [DecidableEq Y] [DecidableEq Y'] in
theorem modul_mem_SB {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {Φ : Matrix Y Y' k → ℂ}
    (hΦ : Φ ∈ SB (Matrix Y Y' k)) (b : Matrix Y Y' k) : (fun t => Inhab.pairing ψ t b * Φ t) ∈ SB (Matrix Y Y' k) := by
  have hψ : IsLocallyConstant ψ := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    filter_upwards [((isOpen_cball d).preimage (continuous_sub_right x)).mem_nhds
      (show x - x ∈ cball d by simp [cball])] with z hz
    rw [← add_sub_cancel x z, AddChar.map_add_eq_mul, (hd d).2 le_rfl _ hz, mul_one]
  have h2 : IsLocallyConstant fun t : Matrix Y Y' k => Inhab.pairing ψ t b :=
    (hψ.comp_continuous (f := fun t : Matrix Y Y' k => ∑ r, ∑ q, b r q * t r q) (by fun_prop)).comp fun z : Circle => (z : ℂ)
  exact ⟨h2.mul hΦ.1, hΦ.2.mul_left⟩

theorem exists_comb : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ Φ₀ Φ : SB (Matrix Y Y' k), Φ₀ ≠ 0 → ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧ ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = comb ψ S T c (Tm Φ₀) := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ Φ₀ Φ hΦ₀
  classical
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψk hcont hne
  obtain ⟨hup, -, -, hsymk, hsurj⟩ := GlobalTheory.LocSympl.halves_at_split D k p Y Y' S T FS FT ψ ψk hψk
  obtain ⟨-, hec, -⟩ := p.split
  have hce : cA D p.e * p.e = 0 := by rw [mul_comm, hec]
  have half1 : ∀ u : WO S T, IsHalf p.e u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have half2 : ∀ u : WO S T, IsHalf (cA D p.e) u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  let M : Submodule ℂ (SB (Matrix Y Y' k)) :=
    { carrier := {Ψ | ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧
        ∀ Tm, p.IsModel ψ FS FT Tm → Tm Ψ = comb ψ S T c (Tm Φ₀)}
      zero_mem' := ⟨0, by simp, fun Tm _ => by simp [comb]⟩
      add_mem' := by
        rintro a b ⟨c, h1, h2⟩ ⟨c', h1', h2'⟩
        refine ⟨c + c', fun w hw => ?_, fun Tm h => by rw [map_add (f := _), comb_add, h2 Tm h, h2' Tm h]⟩
        exact (Finset.mem_union.1 (Finsupp.support_add hw)).elim (h1 w) (h1' w)
      smul_mem' := by
        rintro a b ⟨c, h1, h2⟩
        exact ⟨a • c, fun w hw => h1 w (Finsupp.support_smul hw), fun Tm h => by rw [map_smul, comb_smul, h2 Tm h]⟩ }
  have key : SB (Matrix Y Y' k) ≤ M.map (SB (Matrix Y Y' k)).subtype := by
    refine Inhab.sb_le hd ?_ ?_ Φ₀.2 (fun h => hΦ₀ (Subtype.ext h)) ⟨Φ₀, ⟨Finsupp.single 0 1, fun w hw => ?_, fun Tm _ => ?_⟩, rfl⟩
    · rintro x _ ⟨Ψ, ⟨c, h1, h2⟩, rfl⟩
      obtain ⟨c', h3, h4⟩ := heis_comb ψ S T (half1 _ (hup x).1) h1
      exact ⟨⟨_, trans_mem_SB Ψ.2 x⟩, ⟨c', h3, fun Tm h => by rw [h4, ← h2 Tm h]; exact h.trans x Ψ _ fun _ => rfl⟩, rfl⟩
    · rintro b _ ⟨Ψ, ⟨c, h1, h2⟩, rfl⟩
      obtain ⟨y, hy, hyb⟩ := hsurj b
      obtain ⟨c', h3, h4⟩ := heis_comb ψ S T (half2 _ hy) h1
      refine ⟨⟨_, modul_mem_SB hd Ψ.2 b⟩, ⟨c', h3, fun Tm h => ?_⟩, rfl⟩
      rw [h4, ← h2 Tm h]
      refine h.modul y hy Ψ _ fun t => ?_
      rw [hsymk t y hy, hyb t]
      rfl
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]
      exact fun i j => mul_zero _
    · rw [comb_single]
      funext w
      show _ = ψ (symplOH S T w 0) * Tm Φ₀ (w + 0)
      rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]
  obtain ⟨Ψ, hΨ, e⟩ := key Φ.2
  rw [← show Ψ = Φ from Subtype.ext e]
  exact hΨ

end GlobalTheory.LocComb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenberg_combination_split_place_datum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ Φ₀ Φ : SB (Matrix Y Y' k), Φ₀ ≠ 0 → ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧ ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = comb ψ S T c (Tm Φ₀) := by
  first | exact @GlobalTheory.LocComb.exists_comb | exact GlobalTheory.LocComb.exists_comb | (intros; apply GlobalTheory.LocComb.exists_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw
namespace GlobalTheory.Core.Rk.SWLaw
variable {D : D7}

theorem scalar_eq (A B : HSp D) (χB : (AE D)ˣ →* Circle) (a : GL (Fin A.rank) (AE D)) :
    (((χB (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod B.rank a : ℝ) : ℂ) =
      ((χB⁻¹ (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (sZero A B + (A.rank : ℂ) / 2) := by
  rw [MonoidHom.inv_apply, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, npow, sZero, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  congr 2
  push_cast
  ring

theorem siegel_decomp (A : HSp D) (p : siegel A) :
    ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c :=
  GlobalTheory.T.doublingSiegel_eq_levi_mul_unipotent D A p

theorem aP_decomp (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank)
    (h : (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c) : aP A p = Matrix.GeneralLinearGroup.det a :=
  GlobalTheory.T.doublingSiegelLeviDetHom_levi_mul_unipotent D A p a c h

theorem zero_datum (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
    (omh : WRep (dblSp A) B) (hW : IsWeilDatumO ψ (dblSp A) B 1 χB omh) (hP : GlobalTheory.Published.WeilRepresentationUnitaryPair) :
    ∃ om₀ : GA D (zeroSp D) × GA D B →* Module.End ℂ (WO (zeroSp D) B → ℂ), IsWeilDatumO ψ (zeroSp D) B 1 χB om₀ := by
  refine hP D ψ (zeroSp D) B 1 χB hW.std hW.hecS hW.hecT ?_ hW.resT
  exact ⟨hW.resS.1, fun η _ a => by rw [show (zeroSp D).rank = 0 from rfl, pow_zero]; rfl⟩

theorem swSec_law : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ (p : siegel A) (g : GA D (dblSp A)), swSec A B omh ν 𝓕 φ (p * g) = (χB⁻¹ (aP A p) : Circle) * npow (absA D (aP A p)) (sZero A B + (A.rank : ℂ) / 2) * swSec A B omh ν 𝓕 φ g := by
  intro hP D ψ A B χB omh hW ν 𝓕 hν φ hφ p g
  obtain ⟨om₀, h₀⟩ := zero_datum ψ A B χB omh hW hP
  obtain ⟨a, c, hp⟩ := siegel_decomp A p
  have haP := aP_decomp A p a c hp
  have hν' : IsCovolOne (ratMx D B.rank A.rank) ν 𝓕 := hν
  have hF := hW.om_pres (g, 1) φ hφ
  set F := omh (g, 1) φ with hFdef
  have hF' := hW.om_pres ((dblDec A).nC c, 1) F hF
  have hM := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ (dblSp A) (zeroSp D) B A.rank (dblDec A) 1 χB omh om₀ hW h₀ ν 𝓕 hν'
  have h1 := (hM _ hF').levi a 0
  have h2 := (hM F hF).centre c 0
  change (dblDec A).mixS B ψ ν 𝓕 (omh ((dblDec A).levi a, 1) (omh ((dblDec A).nC c, 1) F)) 0 =
    ((((χB (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod B.rank a : ℂ)) •
      (dblDec A).mixS B ψ ν 𝓕 (omh ((dblDec A).nC c, 1) F) (0 * a.1) at h1
  change (dblDec A).mixS B ψ ν 𝓕 (omh ((dblDec A).nC c, 1) F) 0 =
    ψ (symplOH (dblSp A) B ((dblDec A).extX B 0) ((dblDec A).extY B (0 * c.1))) •
      (dblDec A).mixS B ψ ν 𝓕 F 0 at h2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec
  have e1 : omh (↑p * g, 1) φ = omh ((dblDec A).levi a, 1) (omh ((dblDec A).nC c, 1) F) := by
    rw [hp, hFdef, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    simp [Prod.mk_mul_mk, mul_assoc]
  rw [e1, ← mixS_dblDec_zero A B ψ ν 𝓕 _ 0, ← mixS_dblDec_zero A B ψ ν 𝓕 F 0, congrFun h1 0, Matrix.zero_mul, Pi.smul_apply, congrFun h2 0, map_zero, symplOH_zero_left, AddChar.map_zero_eq_one, one_smul, haP, smul_eq_mul]
  rw [scalar_eq A B χB a]

end GlobalTheory.Core.Rk.SWLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLawStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilSection_degeneratePrincipalSeries_law : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ (p : siegel A) (g : GA D (dblSp A)), swSec A B omh ν 𝓕 φ (p * g) = (χB⁻¹ (aP A p) : Circle) * npow (absA D (aP A p)) (sZero A B + (A.rank : ℂ) / 2) * swSec A B omh ν 𝓕 φ g := by
  first | exact @GlobalTheory.Core.Rk.SWLaw.swSec_law | exact GlobalTheory.Core.Rk.SWLaw.swSec_law | (intros; apply GlobalTheory.Core.Rk.SWLaw.swSec_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeLatFrameOfEq
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.AdForm.VacStd

theorem coe_latFrame_of_eq {D : D7} (S : HSp D) (hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (h : S = Formalism.BasicNotions.Examples₂.posSpace hs N) :
    (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank := by
  subst h
  ext x
  show x ∈ GlobalTheory.PlaceModel.latFrame _ ↔ ∀ k, IsIntegral ℤ (x k)
  rw [GlobalTheory.PlaceModel.mem_latFrame]
  exact Formalism.IndefR.Seed.FrmC.stdLat_std hs N (fun _ => false) N 0 x

theorem gram_of_eq {D : D7} (S : HSp D) (hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (h : S = Formalism.BasicNotions.Examples₂.posSpace hs N) : S.gram = 1 := by
  subst h
  refine Matrix.ext fun a b => ?_
  exact (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs N (fun _ => false) N 0 a b).trans
    (by
      by_cases hab : a = b
      · subst hab
        rw [Matrix.one_apply_eq]
        exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn])
      · rw [Matrix.one_apply_ne hab]
        exact if_neg hab)

theorem cartan_of_gram {D : D7} {S : HSp D} (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have e : gramAt D S τ = 1 := by rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e]
  exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩

end GlobalTheory.AdForm.VacStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HatCPhiHat
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts GlobalTheory.AdTh
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh

theorem unr_of {D : D7} {χ : (AE D)ˣ →* Circle} (h : UnramEverywhere D χ) {v ε} (hε : IsPlaceIdem D v ε) : UnramAt ε χ := by
  intro x hx h1 h2
  refine h x ?_ h1 h2
  obtain ⟨α, rfl, -⟩ := hε
  have h3 := congrArg (infPart D) hx
  have h4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    have e2 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    have e3 := Algebra.TensorProduct.map_tmul (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α) 1
    rw [e2, TensorProduct.zero_tmul] at e3
    exact e3
  rw [map_mul, h4, zero_mul, map_sub, map_one] at h3
  exact (sub_eq_zero.1 h3.symm)

theorem hatC_phiHat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {n : ℕ} (φ : (Fin n → LevQc Dw l) → c.F) (hf : Finite (Fin n → LevQc Dw l)) (q : Fin n → LevQ Dw l) :
    hatC l (fun x => (φ x : ℂ)) q = ((phiHat c φ q : c.F) : ℂ) := by
  have hz : ((zetaM c : c.F) : ℂ) = Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) := by
    have hM : (l.M : ℂ) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
    have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by rintro rfl; simp at hk; exact hM' hk : k ≠ 0)
    simp only [zetaM, SubmonoidClass.coe_pow, zeta]
    rw [← Complex.exp_nat_mul, hk, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)]
    congr 1; push_cast; field_simp
  have := Fintype.ofFinite (Fin n → LevQc Dw l)
  unfold hatC phiHat
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← hz]
  show _ = c.F.val _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_zpow₀]
  rfl

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

open GlobalTheory.StepLaw


open Classical in
theorem levRes_step : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, (∀ PP ∈ c.Pg, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (c.chi (k + 1) PP)⁻¹ ∧ GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (c.chi (k + 1) PP)⁻¹) ∧ GlobalTheory.StepLaw.UnrOff (c.chS (k + 1)) c.Pg ∧ GlobalTheory.StepLaw.UnrOff (c.chT (k + 1)) c.Pg := by
  intro D c hc k hk
  obtain ⟨H, hEq, hres⟩ := hc.res ⟨k, hk⟩
  have hμR : ∀ PP ∈ c.Pg, ResAt (c.μ (k + 1)) PP (c.chi (k + 1) PP)⁻¹ := fun PP hP =>
    (GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D _ H hEq PP).1 _ (GlobalTheory.T.heckeChar_tameAt_of_factors_through_residue D H PP _ (hres PP hP)) (hres PP hP)
  have hμU : UnrOff (c.μ (k + 1)) c.Pg := fun v ε hε hv =>
    GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ H hEq v ε hε fun P hP =>
      (GlobalTheory.ChrTie.unrAt_iff_and_val_eq D _ H hEq P).1.1 (hc.unr ⟨k, hk⟩ P fun hm => by
        obtain ⟨PP, hPP, he⟩ := Finset.mem_image.1 hm
        exact hv PP hPP (he.trans hP))
  have hη : UnramEverywhere D c.η := hc.chars.2.1
  have hηR : ∀ PP, ResAt c.η⁻¹ PP 1 := fun PP => by
    have := (GlobalTheory.ExportSeries.TupleChars.resAt_of_unramEverywhere hη PP).inv
    rwa [inv_one] at this
  have hηU : UnrOff c.η⁻¹ c.Pg := UnrOff.inv fun v ε hε _ => GlobalTheory.AdTh.unr_of hη hε
  have hmR : ∀ PP ∈ c.Pg, ResAt (c.μ (k + 1) * c.η⁻¹) PP (c.chi (k + 1) PP)⁻¹ := fun PP hP => by
    have := (hμR PP hP).mul (hηR PP)
    rwa [mul_one] at this
  have hmU : UnrOff (c.μ (k + 1) * c.η⁻¹) c.Pg := hμU.mul hηU
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs
  · exact ⟨fun PP hP => ⟨hmR PP hP, hμR PP hP⟩, hmU, hμU⟩
  · exact ⟨fun PP hP => ⟨hμR PP hP, hmR PP hP⟩, hμU, hmU⟩

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, (∀ PP ∈ c.Pg, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (c.chi (k + 1) PP)⁻¹ ∧ GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (c.chi (k + 1) PP)⁻¹) ∧ GlobalTheory.StepLaw.UnrOff (c.chS (k + 1)) c.Pg ∧ GlobalTheory.StepLaw.UnrOff (c.chT (k + 1)) c.Pg := by
  first | exact @GlobalTheory.ChainOnto.levRes_step | exact GlobalTheory.ChainOnto.levRes_step | (intros; apply GlobalTheory.ChainOnto.levRes_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastBiTheta

variable {D : D7}

theorem sOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  simp [symplOH, symplO, hO]

theorem sOH_zero_right (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem sOH_resS_symm {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) (a a' : WO A S) (b b' : WO L S) :
    symplOH V₀ S ((o.resS S).symm (a, b)) ((o.resS S).symm (a', b')) = symplOH A S a a' + symplOH L S b b' := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem quasi_of_mem {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (h : IsThetaFunO ψ S T f)
    {x : WO S T} (hx : x ∈ ratMx D T.rank S.rank) (w : WO S T) : f (x + w) = ψ (-(symplOH S T x w)) * f w := by
  obtain ⟨γ, rfl⟩ := hx
  exact h.quasi γ w

theorem resS_symm_mem {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) {a : WO A S} {b : WO L S}
    (ha : a ∈ ratMx D S.rank A.rank) (hb : b ∈ ratMx D S.rank L.rank) :
    (o.resS S).symm (a, b) ∈ ratMx D S.rank V₀.rank := by
  rw [OrthDec.resS_symm_apply]
  exact add_mem (ratMx_mul ha (rat_mem _)) (ratMx_mul hb (rat_mem _))

theorem resS_symm_map {B : Type} [CommRing B] (φ : AE D →+* B) {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D)
    {a : WO A S} {b : WO L S} (ha : a.map φ = 0) (hb : b.map φ = 0) : ((o.resS S).symm (a, b)).map φ = 0 := by
  rw [OrthDec.resS_symm_apply, Matrix.map_add φ (map_add φ), map_mul_eq_zero_left φ ha, map_mul_eq_zero_left φ hb,
    add_zero]


set_option maxHeartbeats 1000000 in
theorem isBiTheta_lastBi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ → IsBiTheta ψ A S X (lastBi o o'' τ Ξ Φ₂) := by
  intro D ψ _ V₀ A L S X T L'' o o'' τ hτ Ξ Φ₂ hΞ hΦ
  obtain ⟨kadd, kcont, krat, -, ksympl, kpart⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)
  have kH : ∀ w w', symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [ksympl]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_neg]
  have hC : ∀ u v, lastBi o o'' τ Ξ Φ₂ u v =
      Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := fun _ _ => rfl
  let K : WO S L'' →+ WO L S := AddMonoidHom.mk' (kap τ S) kadd
  let P1 : WO S X →+ WO S T := (AddMonoidHom.fst _ _).comp (o''.resT S).toAddMonoidHom
  let P2 : WO S X →+ WO S L'' := (AddMonoidHom.snd _ _).comp (o''.resT S).toAddMonoidHom
  have cP1 : Continuous fun b : WO S X => (o''.resT S b).1 := continuous_fst.comp (o''.continuous_resT S)
  have cP2 : Continuous fun b : WO S X => (o''.resT S b).2 := continuous_snd.comp (o''.continuous_resT S)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show Continuous fun p : WO A S × WO S X =>
      Φ₂ (o''.resT S p.2).1 * Ξ ((o.resS S).symm (p.1, kap τ S (o''.resT S p.2).2))
    exact (hΦ.cont.comp (cP1.comp continuous_snd)).mul
      (hΞ.cont.comp ((o.continuous_resS_symm S).comp (continuous_fst.prodMk (kcont.comp (cP2.comp continuous_snd)))))
  ·
    intro n L₁ L₂ hL₁ hL₂ hf₁ hf₂ u v
    let M₁ : (Fin n → ℝ) →+ WO S T := P1.comp L₂
    let M₂ : (Fin n → ℝ) →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.prod L₁ (K.comp (P2.comp L₂)))
    have cM₁ : Continuous M₁ := cP1.comp hL₂
    have cM₂ : Continuous M₂ := (o.continuous_resS_symm S).comp (hL₁.prodMk (kcont.comp (cP2.comp hL₂)))
    have fM₁ : ∀ t, (M₁ t).map (finPart D) = 0 := fun t => map_mul_eq_zero_right (finPart D) _ (hf₂ t)
    have fM₂ : ∀ t, (M₂ t).map (finPart D) = 0 := fun t =>
      resS_symm_map (finPart D) o S (hf₁ t) ((kpart _).2 (map_mul_eq_zero_right (finPart D) _ (hf₂ t)))
    have e : (fun t => lastBi o o'' τ Ξ Φ₂ (u + L₁ t) (v + L₂ t)) = fun t =>
        Φ₂ ((o''.resT S v).1 + M₁ t) * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2) + M₂ t) := by
      funext t
      rw [hC]
      show Φ₂ (o''.resT S (v + L₂ t)).1 * Ξ ((o.resS S).symm (u + L₁ t, kap τ S (o''.resT S (v + L₂ t)).2)) =
        Φ₂ ((o''.resT S v).1 + (o''.resT S (L₂ t)).1) *
          Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2) + (o.resS S).symm (L₁ t, kap τ S (o''.resT S (L₂ t)).2))
      rw [map_add (f := _), Prod.fst_add, Prod.snd_add, kadd, ← map_add (f := _), Prod.mk_add_mk]
    rw [e]
    exact (hΦ.smooth n M₁ cM₁ fM₁ _).mul (hΞ.smooth n M₂ cM₂ fM₂ _)
  ·
    intro γ u v
    rw [hC, hC]
    have e : (o.resS S).symm (ratW S A γ + u, kap τ S (o''.resT S v).2) =
        (o.resS S).symm (ratW S A γ, 0) + (o.resS S).symm (u, kap τ S (o''.resT S v).2) := by
      rw [← map_add (f := _), Prod.mk_add_mk, zero_add]
    have hγ : ratW S A γ ∈ ratMx D S.rank A.rank := rat_mem γ
    rw [e, quasi_of_mem hΞ (resS_symm_mem o S hγ (zero_mem _)), sOH_resS_symm, sOH_zero_left, add_zero]
    ring
  ·
    intro γ u v
    rw [hC, hC]
    have h1 : (o''.resT S (ratW X S γ)).1 ∈ ratMx D T.rank S.rank := ratMx_mul (rat_mem _) (rat_mem γ)
    have h2 : (o''.resT S (ratW X S γ)).2 ∈ ratMx D L''.rank S.rank := ratMx_mul (rat_mem _) (rat_mem γ)
    have e : (o.resS S).symm (u, kap τ S ((o''.resT S (ratW X S γ)).2 + (o''.resT S v).2)) =
        (o.resS S).symm (0, kap τ S (o''.resT S (ratW X S γ)).2) + (o.resS S).symm (u, kap τ S (o''.resT S v).2) := by
      rw [kadd, ← map_add (f := _), Prod.mk_add_mk, zero_add]
    have ph : ψ (-symplOH S X (ratW X S γ) v) = ψ (-symplOH S T (o''.resT S (ratW X S γ)).1 (o''.resT S v).1) *
        ψ (-symplOH S L'' (o''.resT S (ratW X S γ)).2 (o''.resT S v).2) := by
      rw [← AddChar.map_add_eq_mul, o''.symplOH_resT S (ratW X S γ) v]
      exact congrArg ψ (neg_add _ _)
    rw [map_add (f := _), Prod.fst_add, Prod.snd_add, e, quasi_of_mem hΦ h1,
      quasi_of_mem hΞ (resS_symm_mem o S (zero_mem _) (krat _ h2)), sOH_resS_symm, sOH_zero_left, zero_add, kH, ph]
    ring
  ·
    obtain ⟨U, hUo, hU⟩ := hΞ.level
    let iA : WO A S →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)
    have ciA : Continuous fun a : WO A S => (o.resS S).symm (a, 0) :=
      (o.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)
    refine ⟨U.comap iA, hUo.preimage ciA, fun a ha hinf v => ?_⟩
    funext u
    have h1 := congrFun (hU (iA a) ha (resS_symm_map (infPart D) o S hinf (by simp)))
      ((o.resS S).symm (u, kap τ S (o''.resT S v).2))
    have e : (o.resS S).symm (u + a, kap τ S (o''.resT S v).2) =
        (o.resS S).symm (u, kap τ S (o''.resT S v).2) + iA a := by
      show _ = _ + (o.resS S).symm (a, 0)
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero]
    have ph : symplOH V₀ S ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) (iA a) = symplOH A S u a := by
      show symplOH V₀ S ((o.resS S).symm (u, _)) ((o.resS S).symm (a, 0)) = _
      rw [sOH_resS_symm, sOH_zero_right, add_zero]
    simp only [heisO] at h1 ⊢
    rw [ph] at h1
    rw [hC, hC, e, ← h1]
    ring
  ·
    obtain ⟨UΞ, hUΞo, hUΞ⟩ := hΞ.level
    obtain ⟨UΦ, hUΦo, hUΦ⟩ := hΦ.level
    let jL : WO S X →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp ((AddMonoidHom.inr _ _).comp (K.comp P2))
    have cjL : Continuous fun b : WO S X => (o.resS S).symm (0, kap τ S (o''.resT S b).2) :=
      (o.continuous_resS_symm S).comp (continuous_const.prodMk (kcont.comp cP2))
    refine ⟨UΦ.comap P1 ⊓ UΞ.comap jL, (hUΦo.preimage cP1).inter (hUΞo.preimage cjL), fun b hb hinf u => ?_⟩
    have hT : (o''.resT S b).1.map (infPart D) = 0 := map_mul_eq_zero_right (infPart D) _ hinf
    have hJ : (jL b).map (infPart D) = 0 :=
      resS_symm_map (infPart D) o S (by simp) ((kpart _).1 (map_mul_eq_zero_right (infPart D) _ hinf))
    show heisO ψ S X b (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))) =
      o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))
    rw [o''.heisO_boxT, hUΦ (o''.resT S b).1 hb.1 hT]
    congr 1
    funext w
    have h2 := congrFun (hUΞ (jL b) hb.2 hJ) ((o.resS S).symm (u, kap τ S w))
    have e : (o.resS S).symm (u, kap τ S (w + (o''.resT S b).2)) = (o.resS S).symm (u, kap τ S w) + jL b := by
      show _ = _ + (o.resS S).symm (0, kap τ S (o''.resT S b).2)
      rw [kadd, ← map_add (f := _), Prod.mk_add_mk, add_zero]
    have ph : symplOH V₀ S ((o.resS S).symm (u, kap τ S w)) (jL b) = symplOH S L'' w (o''.resT S b).2 := by
      show symplOH V₀ S ((o.resS S).symm (u, _)) ((o.resS S).symm (0, kap τ S (o''.resT S b).2)) = _
      rw [sOH_resS_symm, sOH_zero_right, zero_add, kH]
    simp only [heisO] at h2 ⊢
    rw [ph] at h2
    rw [e]
    exact h2

end GlobalTheory.LastBiTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSaw_datum_isTwoVariableThetaFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ → IsBiTheta ψ A S X (lastBi o o'' τ Ξ Φ₂) := by
  first | exact @GlobalTheory.LastBiTheta.isBiTheta_lastBi | exact GlobalTheory.LastBiTheta.isBiTheta_lastBi | (intros; apply GlobalTheory.LastBiTheta.isBiTheta_lastBi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DStepCell

variable {D : D7}

def integ {c : Comm D} (v : VCom c) {t : Tup c} (w : VTup t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ)
    (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ)
    (q₁ : GA D (c.V (j + 1))) (q₂ : GA D (c.V (j + 1 + 1))) : ℂ :=
  ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
    (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h)
      (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))
      (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁ q₂) (rTrans q₂ f)

end GlobalTheory.DStepCell

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatMulVecSec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreFrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rat_mulVec_sec (q : SplitPt D k) {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) (w : Fin b → k) :
    rat Q *ᵥ (fun i => q.sec (w i)) =
      fun i => q.sec ((Q.map (GlobalTheory.SliceModel.prH (GlobalTheory.LocMod.ofSplit q)) *ᵥ w) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.SliceModel.ι_mul_left (GlobalTheory.LocMod.ofSplit q) (w j) (incA D (Q i j))

end GlobalTheory.CoreFrameLat
end
end
