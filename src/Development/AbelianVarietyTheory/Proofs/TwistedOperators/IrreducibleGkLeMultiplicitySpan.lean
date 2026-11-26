module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacesDistinctTranslationsDerivativesCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacesDistinctTranslationsDerivativesCommute
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.PlaceComm

theorem place_comm : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    IsInfFam (D := D) θ → ∀ τ τ' : D.what₂.Tau, τ ≠ τ' →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), ∀ f : GA D V → ℂ,
      rTr V (atTau θ V τ g) (rTr V (atTau θ V τ' h) f) = rTr V (atTau θ V τ' h) (rTr V (atTau θ V τ g) f)) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ X ∈ lieAt V τ', ∀ f : GA D V → ℂ,
      Rder θ V τ' X (rTr V (atTau θ V τ g) f) = rTr V (atTau θ V τ g) (Rder θ V τ' X f)) ∧
    (∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ', ∀ f : GA D V → ℂ, IsAutFunSm θ V f →
      Rder θ V τ X (Rder θ V τ' Y f) = Rder θ V τ' Y (Rder θ V τ X f)) := by
  intro D θ V hθ τ τ' hne
  refine ⟨fun g hg h hh f => ?_, fun g hg X hX f => ?_, fun X hX Y hY f hf => ?_⟩
  · funext x
    simp only [rTr]
    rw [mul_assoc, mul_assoc, GlobalTheory.AvgOtherPlace.atTau_comm hθ (Ne.symm hne) hg hh]
  · rw [GlobalTheory.Mem.RealTranslate.Rder_rTr hθ (GlobalTheory.Mem.RealTranslate.isRealPt_atTau hθ τ hg) hX,
      GlobalTheory.AvgOtherPlace.adAt_atTau_of_ne hθ (Ne.symm hne) hg]
  · exact GlobalTheory.DerBracket.Rder_comm hθ hf.smooth hne hX hY

end GlobalTheory.PlaceComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacesDistinctTranslationsDerivativesCommuteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaces_distinct_translations_derivatives_commute : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    IsInfFam (D := D) θ → ∀ τ τ' : D.what₂.Tau, τ ≠ τ' →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), ∀ f : GA D V → ℂ,
      rTr V (atTau θ V τ g) (rTr V (atTau θ V τ' h) f) = rTr V (atTau θ V τ' h) (rTr V (atTau θ V τ g) f)) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ X ∈ lieAt V τ', ∀ f : GA D V → ℂ,
      Rder θ V τ' X (rTr V (atTau θ V τ g) f) = rTr V (atTau θ V τ g) (Rder θ V τ' X f)) ∧
    (∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ', ∀ f : GA D V → ℂ, IsAutFunSm θ V f →
      Rder θ V τ X (Rder θ V τ' Y f) = Rder θ V τ' Y (Rder θ V τ X f)) := by
  first | exact @GlobalTheory.PlaceComm.place_comm | exact GlobalTheory.PlaceComm.place_comm | (intros; apply GlobalTheory.PlaceComm.place_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocSubLocGen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

structure IsLocSub (τ : D.what₂.Tau) (B : Submodule ℂ (GA D V → ℂ)) : Prop where
  k : ∀ g, GlobalTheory.CuspGK.InK M τ g → ∀ f ∈ B, rTr V (atTau θ V τ g) f ∈ B
  lie : ∀ X ∈ lieAt V τ, ∀ f ∈ B, Rder θ V τ X f ∈ B

def locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  sInf {B | ψ ∈ B ∧ IsLocSub θ M τ B}

theorem mem_locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : ψ ∈ locGen θ M τ ψ :=
  Submodule.mem_sInf.2 fun _ h => h.1

theorem isLocSub_locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : IsLocSub θ M τ (locGen θ M τ ψ) := by
  constructor
  · intro g hg f hf
    exact Submodule.mem_sInf.2 fun B hB => hB.2.k g hg f (Submodule.mem_sInf.1 hf B hB)
  · intro X hX f hf
    exact Submodule.mem_sInf.2 fun B hB => hB.2.lie X hX f (Submodule.mem_sInf.1 hf B hB)

theorem locGen_le {τ : D.what₂.Tau} {ψ : GA D V → ℂ} {B : Submodule ℂ (GA D V → ℂ)} (hψ : ψ ∈ B)
    (hB : IsLocSub θ M τ B) : locGen θ M τ ψ ≤ B :=
  sInf_le ⟨hψ, hB⟩

end GlobalTheory.CuspGKId

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubmodulePowSimpleEqSumEquivValues
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubmodulePowSimpleEqSumEquivValues
open Submodule

namespace GlobalTheory.SubmodulePowSimple

variable {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type}

def equivValues (a : ι → Module.End ℂ P) (m : ℕ) (N : Submodule ℂ (Fin m → P)) :
    Set (Fin m → P) :=
  {v | ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
    (∀ p, S p ∈ N) ∧ ∃ q, v = S q}

def snocZero (m : ℕ) : (Fin m → P) →ₗ[ℂ] (Fin (m+1) → P) where
  toFun z := Fin.snoc (α := fun _ => P) z 0
  map_add' x y := by
    funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  map_smul' c x := by
    funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

lemma snocZero_diag {m : ℕ} (b : Module.End ℂ P) (z : Fin m → P) :
    snocZero m (fun j => b (z j)) = fun j => b (snocZero m z j) := by
  funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [snocZero]

lemma single_diag {m : ℕ} (b : Module.End ℂ P) (p : P) :
    (Pi.single (Fin.last m) (b p) : Fin (m+1) → P) = fun j => b ((Pi.single (Fin.last m) p : Fin (m+1) → P) j) := by
  funext j
  by_cases h : j = Fin.last m
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem mem_span_equivValues (a : ι → Module.End ℂ P)
    (hs : ∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) :
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, y ∈ span ℂ (equivValues a m N) := by
  intro m
  induction m with
  | zero =>
    intro N _ y _
    rw [Subsingleton.elim y 0]; exact zero_mem _
  | succ m ih =>
    intro N hN y hy
    let B : Submodule ℂ P := N.comap (LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m))
    have hBmem : ∀ p, p ∈ B ↔ (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N := fun p => by
      simp [B]
    have hBst : ∀ i, ∀ p ∈ B, a i p ∈ B := by
      intro i p hp
      rw [hBmem] at hp ⊢
      rw [single_diag]; exact hN i _ hp
    by_cases hB : B = ⊥
    · let I : (Fin (m+1) → P) →ₗ[ℂ] (Fin m → P) := LinearMap.funLeft ℂ P Fin.castSucc
      have hinj : ∀ x₁ ∈ N, ∀ x₂ ∈ N, I x₁ = I x₂ → x₁ = x₂ := by
        intro x₁ h₁ x₂ h₂ he
        have hd : x₁ - x₂ ∈ N := N.sub_mem h₁ h₂
        have hs' : x₁ - x₂ = Pi.single (Fin.last m) ((x₁ - x₂) (Fin.last m)) := by
          funext j; refine Fin.lastCases ?_ (fun j => ?_) j
          · simp
          · have h := congrFun he j
            change x₁ (Fin.castSucc j) = x₂ (Fin.castSucc j) at h
            rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne]
            simp [h]
        have hB' : (x₁ - x₂) (Fin.last m) ∈ B := by
          rw [hBmem, ← hs']; exact hd
        rw [hB, Submodule.mem_bot] at hB'
        rw [hB', Pi.single_zero] at hs'
        exact sub_eq_zero.mp hs'
      let N0 := N.map I
      have hN0 : ∀ i, ∀ w ∈ N0, (fun j => a i (w j)) ∈ N0 := by
        intro i w hw
        obtain ⟨x, hx, rfl⟩ := hw
        exact ⟨_, hN i x hx, rfl⟩
      have lift : ∀ S : P →ₗ[ℂ] (Fin m → P), (∀ p, S p ∈ N0) →
          ∃ S' : P →ₗ[ℂ] (Fin (m+1) → P), (∀ p, S' p ∈ N) ∧ ∀ p, I (S' p) = S p := by
        intro S hS
        let J : N →ₗ[ℂ] (Fin m → P) := I ∘ₗ N.subtype
        have hJ : Function.Injective J := by
          intro u v huv; exact Subtype.ext (hinj u u.2 v v.2 huv)
        have hS' : ∀ p, S p ∈ LinearMap.range J := by
          intro p; obtain ⟨x, hx, hxe⟩ := hS p; exact ⟨⟨x, hx⟩, hxe⟩
        have key : ∀ v, J ((LinearEquiv.ofInjective J hJ).symm v) = v := fun v => by
          have h := congrArg Subtype.val ((LinearEquiv.ofInjective J hJ).apply_symm_apply v)
          rw [LinearEquiv.ofInjective_apply] at h
          exact h
        refine ⟨N.subtype ∘ₗ (LinearEquiv.ofInjective J hJ).symm.toLinearMap ∘ₗ
          S.codRestrict _ hS', fun p => Subtype.property _, fun p => ?_⟩
        exact key ⟨S p, hS' p⟩
      have h1 := ih N0 hN0 (I y) ⟨y, hy, rfl⟩
      obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').mp h1
      have hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
          (∀ p, S p ∈ N0) ∧ ∃ q, (g k : Fin m → P) = S q := fun k => (g k).2
      choose S hSa hSN q hq using hg
      choose S' hS'N hS'I using fun k => lift (S k) (hSN k)
      have hS'a : ∀ k i p, S' k (a i p) = fun j => a i (S' k p j) := by
        intro k i p
        apply hinj _ (hS'N k _) _ (hN i _ (hS'N k p))
        rw [hS'I, hSa, ← hS'I k p]; rfl
      have hy_eq : y = ∑ k, f k • S' k (q k) := by
        apply hinj _ hy _ (sum_mem fun k _ => N.smul_mem _ (hS'N k _))
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hfg, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, hS'I, hq]
      rw [hy_eq]
      exact sum_mem fun k _ => smul_mem _ _ (subset_span ⟨S' k, hS'a k, hS'N k, q k, rfl⟩)
    · have hBt := hs B hBst hB
      have hmem : ∀ p, (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N := fun p => by
        rw [← hBmem, hBt]; exact Submodule.mem_top
      obtain ⟨y', hy'⟩ : ∃ y', y' = y - Pi.single (Fin.last m) (y (Fin.last m)) := ⟨_, rfl⟩
      have hy'N : y' ∈ N := hy' ▸ N.sub_mem hy (hmem _)
      have hy'last : y' (Fin.last m) = 0 := by simp [hy']
      let N' := N.comap (snocZero m)
      have hN' : ∀ i, ∀ z ∈ N', (fun j => a i (z j)) ∈ N' := by
        intro i z hz
        show snocZero m _ ∈ N
        rw [snocZero_diag]; exact hN i _ hz
      let z : Fin m → P := fun j => y' (Fin.castSucc j)
      have hz : snocZero m z = y' := by
        funext j; refine Fin.lastCases ?_ (fun j => ?_) j
        · simp [snocZero, hy'last]
        · simp [snocZero, z]
      have hzN' : z ∈ N' := show snocZero m z ∈ N from hz ▸ hy'N
      have h1 := ih N' hN' z hzN'
      have h2 : y' ∈ span ℂ (equivValues a (m+1) N) := by
        rw [← hz]
        have h := Submodule.mem_map_of_mem (f := snocZero m) h1
        rw [Submodule.map_span] at h
        refine Submodule.span_mono ?_ h
        rintro _ ⟨v, ⟨S, hSa, hSN, q, rfl⟩, rfl⟩
        refine ⟨snocZero m ∘ₗ S, ?_, fun p => hSN p, q, rfl⟩
        intro i p; simp only [LinearMap.comp_apply, hSa, snocZero_diag]
      have h3 : (Pi.single (Fin.last m) (y (Fin.last m)) : Fin (m+1) → P) ∈
          span ℂ (equivValues a (m+1) N) := by
        refine Submodule.subset_span
          ⟨LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m), ?_, ?_, y (Fin.last m), rfl⟩
        · intro i p; simp only [LinearMap.single_apply]; exact single_diag _ _
        · intro p; simpa using hmem p
      have : y = y' + Pi.single (Fin.last m) (y (Fin.last m)) := by simp [hy']
      rw [this]; exact add_mem h2 h3

end GlobalTheory.SubmodulePowSimple

namespace GlobalTheory

theorem submodule_pow_simple_eq_sum_equiv_values :
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧
        y = ∑ l, Sm l (q l) := by
  intro P _ _ ι a hs m N hN y hy
  obtain ⟨n, f, g, hfg⟩ :=
    (Submodule.mem_span_set').mp (SubmodulePowSimple.mem_span_equivValues a hs m N hN y hy)
  have hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
      (∀ p, S p ∈ N) ∧ ∃ q, (g k : Fin m → P) = S q := fun k => (g k).2
  choose S hSa hSN q hq using hg
  refine ⟨n, S, fun k => f k • q k, hSa, hSN, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hq, map_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubmodulePowSimpleEqSumEquivValuesStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_intertwined_of_mem_invariant_submodule : ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧ y = ∑ l, Sm l (q l) := by
  first | exact @GlobalTheory.submodule_pow_simple_eq_sum_equiv_values | exact GlobalTheory.submodule_pow_simple_eq_sum_equiv_values | (intros; apply GlobalTheory.submodule_pow_simple_eq_sum_equiv_values <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.CuspGKId

theorem sub_pow_sum : ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧ y = ∑ l, Sm l (q l) := GlobalTheory.T.exists_sum_intertwined_of_mem_invariant_submodule

theorem place_comm : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    IsInfFam (D := D) θ → ∀ τ τ' : D.what₂.Tau, τ ≠ τ' →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), ∀ f : GA D V → ℂ,
      rTr V (atTau θ V τ g) (rTr V (atTau θ V τ' h) f) = rTr V (atTau θ V τ' h) (rTr V (atTau θ V τ g) f)) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ X ∈ lieAt V τ', ∀ f : GA D V → ℂ,
      Rder θ V τ' X (rTr V (atTau θ V τ g) f) = rTr V (atTau θ V τ g) (Rder θ V τ' X f)) ∧
    (∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ', ∀ f : GA D V → ℂ, IsAutFunSm θ V f →
      Rder θ V τ X (Rder θ V τ' Y f) = Rder θ V τ' Y (Rder θ V τ X f)) := GlobalTheory.T.realPlaces_distinct_translations_derivatives_commute

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}


variable (M) in
abbrev Tup : Type := ∀ τ : D.what₂.Tau, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)


variable (M) in
abbrev MMK : Type := Tup M →ₘₗ[ℂ] (GA D V → ℂ)


variable (θ M) in
structure IsPartMult (A : Submodule ℂ (GA D V → ℂ)) (s : Finset D.what₂.Tau) (p0 : Tup M)
    (lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ) (F : MMK M) : Prop where
  mem : ∀ u, F u ∈ A
  equivK : ∀ τ ∈ s, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
    ∀ (u : Tup M) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), (w : M.H τ) = M.rep τ g (u τ) →
      F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)
  equivLie : ∀ τ ∈ s, ∀ X ∈ lieAt V τ, ∀ (u : Tup M) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
    HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
      F (Function.update u τ w) = Rder θ V τ X (F u)
  other : ∀ τ ∉ s, ∀ (u : Tup M) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
    F (Function.update u τ w) = lam τ w • F (Function.update u τ (p0 τ))


variable (θ M) in
def partSub (A : Submodule ℂ (GA D V → ℂ)) (hsm : ∀ f ∈ A, IsAutFunSm θ V f) (s : Finset D.what₂.Tau) (p0 : Tup M)
    (lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ) : Submodule ℂ (MMK M) where
  carrier := {F | IsPartMult θ M A s p0 lam F}
  zero_mem' :=
    { mem := fun _ => A.zero_mem
      equivK := fun _ _ _ _ _ _ _ _ => rfl
      equivLie := fun τ _ X _ _ _ _ => (Formalism.IndefR.Mult.rder_zero θ V τ X).symm
      other := fun _ _ _ _ => (smul_zero _).symm }
  add_mem' := by
    intro F G hF hG
    refine ⟨fun u => A.add_mem (hF.mem u) (hG.mem u), fun τ hτ g hg hk u w hw => ?_,
      fun τ hτ X hX u w hw => ?_, fun τ hτ u w => ?_⟩
    · simp only [add_apply, hF.equivK τ hτ g hg hk u w hw, hG.equivK τ hτ g hg hk u w hw]
      rfl
    · simp only [add_apply, hF.equivLie τ hτ X hX u w hw, hG.equivLie τ hτ X hX u w hw]
      exact (GlobalTheory.Mem.AutSpace.Rder_add (hsm _ (hF.mem u)).smooth (hsm _ (hG.mem u)).smooth hX).symm
    · simp only [add_apply, hF.other τ hτ u w, hG.other τ hτ u w, smul_add]
  smul_mem' := by
    intro c F hF
    refine ⟨fun u => A.smul_mem c (hF.mem u), fun τ hτ g hg hk u w hw => ?_,
      fun τ hτ X hX u w hw => ?_, fun τ hτ u w => ?_⟩
    · simp only [smul_apply, hF.equivK τ hτ g hg hk u w hw]
      rfl
    · simp only [smul_apply, hF.equivLie τ hτ X hX u w hw]
      exact (GlobalTheory.Mem.AutSpace.Rder_smul c _ τ X).symm
    · simp only [smul_apply, hF.other τ hτ u w]
      exact smul_comm _ _ _

def evAt (p0 : Tup M) : MMK M →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := F p0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


variable (V) in
def rTrL (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def postRder (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (F : MMK M)
    (hF : ∀ u, IsAutFunSm θ V (F u)) : MMK M where
  toFun u := Rder θ V τ X (F u)
  map_update_add' u i a b := by
    rw [F.map_update_add, GlobalTheory.Mem.AutSpace.Rder_add (hF _).smooth (hF _).smooth hX]
  map_update_smul' u i c a := by
    rw [F.map_update_smul, GlobalTheory.Mem.AutSpace.Rder_smul]

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem Rder_sum {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {n : ℕ}
    (f : Fin n → GA D V → ℂ) (hf : ∀ j, IsAutFunSm θ V (f j)) :
    Rder θ V τ X (∑ j, f j) = ∑ j, Rder θ V τ X (f j) := by
  classical
  have key : ∀ t : Finset (Fin n), Rder θ V τ X (∑ j ∈ t, f j) = ∑ j ∈ t, Rder θ V τ X (f j) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using Formalism.IndefR.Mult.rder_zero θ V τ X
    | insert j t hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, GlobalTheory.Mem.AutSpace.Rder_add (hf j).smooth
        ((GlobalTheory.Mem.AutSpace.SmFun θ V).sum_mem fun j _ => (hf j).smooth) hX, ih]
  exact key Finset.univ

theorem isAutFunSm_sum {n : ℕ} (f : Fin n → GA D V → ℂ) (hf : ∀ j, IsAutFunSm θ V (f j)) :
    IsAutFunSm θ V (∑ j, f j) := by
  classical
  have key : ∀ t : Finset (Fin n), IsAutFunSm θ V (∑ j ∈ t, f j) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      exact Formalism.IndefR.Mult.isAutFunSm_zero θ V
    | insert j t hj ih =>
      rw [Finset.sum_insert hj]
      exact GlobalTheory.Mem.AutSpace.isAutFunSm_add (hf j) ih
  exact key Finset.univ

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}

theorem IsPartMult.eq_zero {A : Submodule ℂ (GA D V → ℂ)} {s : Finset D.what₂.Tau} {p0 : Tup M}
    {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} {F : MMK M} (hF : IsPartMult θ M A s p0 lam F)
    (hp0 : ∀ τ, p0 τ ≠ 0)
    (hsimple : ∀ τ, ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤)
    (h0 : F p0 = 0) : F = 0 := by
  have key : ∀ t : Finset D.what₂.Tau, ∀ u : Tup M, (∀ τ ∉ t, u τ = p0 τ) → F u = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro u hu
      have : u = p0 := funext fun τ => hu τ (Finset.notMem_empty τ)
      rw [this, h0]
    | insert τ t hτt ih =>
      intro u hu
      have h1 : F (Function.update u τ (p0 τ)) = 0 := ih _ fun τ' h' => by
        by_cases e : τ' = τ
        · subst e
          simp
        · rw [Function.update_of_ne e]
          exact hu τ' (by simp [e, h'])
      by_cases hs : τ ∈ s
      · let B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) :=
          { carrier := {w | F (Function.update u τ w) = 0}
            zero_mem' := by
              show F (Function.update u τ 0) = 0
              exact F.map_coord_zero τ (by simp)
            add_mem' := by
              intro a b ha hb
              show F (Function.update u τ (a + b)) = 0
              rw [F.map_update_add]
              rw [show F (Function.update u τ a) = 0 from ha, show F (Function.update u τ b) = 0 from hb, add_zero]
            smul_mem' := by
              intro c a ha
              show F (Function.update u τ (c • a)) = 0
              rw [F.map_update_smul, show F (Function.update u τ a) = 0 from ha, smul_zero] }
        have hB : B = ⊤ := by
          refine hsimple τ B ?_ ?_
          · intro e
            have : p0 τ ∈ B := h1
            rw [e, Submodule.mem_bot] at this
            exact hp0 τ this
          · intro X hX v w hv hd
            show F (Function.update u τ w) = 0
            have := hF.equivLie τ hs X hX (Function.update u τ v) w (by simpa using hd)
            rw [Function.update_idem] at this
            rw [this, show F (Function.update u τ v) = 0 from hv]
            exact Formalism.IndefR.Mult.rder_zero θ V τ X
        have : u τ ∈ B := hB ▸ Submodule.mem_top
        have e : F (Function.update u τ (u τ)) = 0 := this
        rwa [Function.update_eq_self] at e
      · rw [← Function.update_eq_self τ u, hF.other τ hs, h1, smul_zero]
  ext u : 1
  exact key Finset.univ u fun τ h => absurd (Finset.mem_univ τ) h

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}

theorem IsPartMult.rTr_comp (hθ : IsInfFam (D := D) θ) {A : Submodule ℂ (GA D V → ℂ)}
    (hA : GlobalTheory.CuspGK.IsGKSub θ M A) {s : Finset D.what₂.Tau} {p0 : Tup M}
    {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} {F : MMK M} (hF : IsPartMult θ M A s p0 lam F)
    {τ : D.what₂.Tau} (hτ : τ ∉ s) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : GlobalTheory.CuspGK.InK M τ g) :
    IsPartMult θ M A s p0 lam ((rTrL V (atTau θ V τ g)).compMultilinearMap F) := by
  refine ⟨fun u => hA.k τ g hg _ (hF.mem u), fun τ' hτ' h hh hk u w hw => ?_, fun τ' hτ' Y hY u w hw => ?_,
    fun τ' hτ' u w => ?_⟩
  · have hne : τ ≠ τ' := fun e => hτ (e ▸ hτ')
    simp only [LinearMap.compMultilinearMap_apply, rTrL]
    rw [hF.equivK τ' hτ' h hh hk u w hw]
    exact (place_comm θ V hθ τ τ' hne).1 g hg.1 h hh _
  · have hne : τ ≠ τ' := fun e => hτ (e ▸ hτ')
    simp only [LinearMap.compMultilinearMap_apply, rTrL]
    rw [hF.equivLie τ' hτ' Y hY u w hw]
    exact ((place_comm θ V hθ τ τ' hne).2.1 g hg.1 Y hY _).symm
  · simp only [LinearMap.compMultilinearMap_apply, hF.other τ' hτ' u w, map_smul]

theorem IsPartMult.postRder_comp (hθ : IsInfFam (D := D) θ) {A : Submodule ℂ (GA D V → ℂ)}
    (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (hsm : ∀ f ∈ A, IsAutFunSm θ V f) {s : Finset D.what₂.Tau} {p0 : Tup M}
    {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} {F : MMK M} (hF : IsPartMult θ M A s p0 lam F)
    {τ : D.what₂.Tau} (hτ : τ ∉ s) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    IsPartMult θ M A s p0 lam (postRder (θ := θ) τ X hX F fun u => hsm _ (hF.mem u)) := by
  refine ⟨fun u => hA.lie τ X hX _ (hF.mem u), fun τ' hτ' h hh hk u w hw => ?_, fun τ' hτ' Y hY u w hw => ?_,
    fun τ' hτ' u w => ?_⟩
  · have hne : τ' ≠ τ := fun e => hτ (e ▸ hτ')
    show Rder θ V τ X (F _) = rTr V _ (Rder θ V τ X (F u))
    rw [hF.equivK τ' hτ' h hh hk u w hw]
    exact (place_comm θ V hθ τ' τ hne).2.1 h hh X hX _
  · have hne : τ ≠ τ' := fun e => hτ (e ▸ hτ')
    show Rder θ V τ X (F _) = Rder θ V τ' Y (Rder θ V τ X (F u))
    rw [hF.equivLie τ' hτ' Y hY u w hw]
    exact (place_comm θ V hθ τ τ' hne).2.2 X hX Y hY _ (hsm _ (hF.mem u))
  · show Rder θ V τ X (F _) = lam τ' w • Rder θ V τ X (F _)
    rw [hF.other τ' hτ' u w, GlobalTheory.Mem.AutSpace.Rder_smul]

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}

def glue (τ : D.what₂.Tau) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M)
    (p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) : MMK M where
  toFun u := T (u τ) (Function.update u τ p)
  map_update_add' := by
    intro inst u i a b
    obtain rfl : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
    by_cases h : i = τ
    · subst h
      simp only [Function.update_self, Function.update_idem, map_add (f := _), add_apply]
    · simp only [Function.update_of_ne (Ne.symm h), Function.update_comm h]
      exact (T (u τ)).map_update_add _ i a b
  map_update_smul' := by
    intro inst u i c a
    obtain rfl : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
    by_cases h : i = τ
    · subst h
      simp only [Function.update_self, Function.update_idem, map_smul, smul_apply, RingHom.id_apply]
    · simp only [Function.update_of_ne (Ne.symm h), Function.update_comm h]
      exact (T (u τ)).map_update_smul _ i c a

theorem glue_apply (τ : D.what₂.Tau) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M)
    (p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (u : Tup M) : glue τ T p u = T (u τ) (Function.update u τ p) := rfl

theorem isPartMult_glue {A : Submodule ℂ (GA D V → ℂ)} {s : Finset D.what₂.Tau} {p0 : Tup M}
    {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} {τ : D.what₂.Tau} (hτ : τ ∉ s)
    {T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M} (hT : ∀ p, IsPartMult θ M A s p0 lam (T p))
    (hK : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), (w : M.H τ) = M.rep τ g v →
          ∀ u, T w u = rTr V (atTau θ V τ g) (T v u))
    (hL : ∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 →
          ∀ u, T w u = Rder θ V τ X (T v u)) :
    IsPartMult θ M A (insert τ s) p0 lam (glue τ T (p0 τ)) := by
  refine ⟨fun u => (hT _).mem _, fun τ' hτ' g hg hk u w hw => ?_, fun τ' hτ' X hX u w hw => ?_,
    fun τ' hτ' u w => ?_⟩
  · rw [glue_apply, glue_apply]
    by_cases e : τ' = τ
    · subst e
      simp only [Function.update_self, Function.update_idem]
      exact hK g hg hk _ _ hw _
    · have hs : τ' ∈ s := (Finset.mem_insert.1 hτ').resolve_left e
      rw [Function.update_of_ne (Ne.symm e), Function.update_comm e]
      refine (hT (u τ)).equivK τ' hs g hg hk _ w ?_
      rwa [Function.update_of_ne e]
  · rw [glue_apply, glue_apply]
    by_cases e : τ' = τ
    · subst e
      simp only [Function.update_self, Function.update_idem]
      exact hL X hX _ _ hw _
    · have hs : τ' ∈ s := (Finset.mem_insert.1 hτ').resolve_left e
      rw [Function.update_of_ne (Ne.symm e), Function.update_comm e]
      refine (hT (u τ)).equivLie τ' hs X hX _ w ?_
      rwa [Function.update_of_ne e]
  · have e : τ' ≠ τ := fun h => hτ' (h ▸ Finset.mem_insert_self τ s)
    have hs : τ' ∉ s := fun h => hτ' (Finset.mem_insert_of_mem h)
    rw [glue_apply, glue_apply, Function.update_of_ne (Ne.symm e), Function.update_comm e,
      (hT (u τ)).other τ' hs, Function.update_of_ne (Ne.symm e), Function.update_comm e]

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

end GlobalTheory.CuspGKId
