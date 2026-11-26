module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TermVolumeClassSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSteps
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim.StepsModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}


theorem exists_isTermVol {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}
    (hL : L.Is μ₀) (t : T) (Φ : G.Datum) (β : CosFam G t) : ∃ M, IsTermVol t S Φ β M := by
  obtain ⟨M₀, -⟩ := exists_vol G hL t
  have H : ∀ X : Node, ∃ (μ : Measure (GA D (G.V X))) (𝓕 : Set (GA D (G.V X))), (∀ j (h : j < D.R.m) (e : X = .top j), by
        subst e; exact if (Node.top j).neg D.R.m = 0 then IsMeasDef _ (S.levTop t Φ β j h) μ 𝓕
          else Lev.IsMeasFD _ (S.levTop t Φ β j h) μ 𝓕) ∧
      ∀ i (h : i ≤ D.R.m) (e : X = .grid i D.R.m), by
        subst e; exact if (Node.grid i D.R.m).neg D.R.m = 0 then IsMeasDef _ (S.levRow t i h) μ 𝓕
          else Lev.IsMeasFD _ (S.levRow t i h) μ 𝓕 := fun X => by
    by_cases h1 : ∃ j, j < D.R.m ∧ X = .top j
    · obtain ⟨j, hj, rfl⟩ := h1
      have hV := node_isV G hL (X := .top j) hj.le
      obtain ⟨μ, 𝓕, e⟩ := exists_meas _ hV.sigOK (fun τ => congrArg Prod.snd (hV.sig τ)) _ (S.isCO_levTop W t Φ β hj)
      refine ⟨μ, 𝓕, fun j' h e' => ?_, fun _ _ e' => by cases e'⟩
      cases e'; exact e
    · by_cases h2 : ∃ i, i ≤ D.R.m ∧ X = .grid i D.R.m
      · obtain ⟨i, hi, rfl⟩ := h2
        have hV := node_isV G hL (X := .grid i D.R.m) ⟨hi, le_rfl⟩
        obtain ⟨μ, 𝓕, e⟩ := exists_meas _ hV.sigOK (fun τ => congrArg Prod.snd (hV.sig τ)) _ (S.isCO_levRow W t hi)
        refine ⟨μ, 𝓕, fun _ _ e' => (by cases e'), fun j' h e' => ?_⟩
        cases e'; exact e
      · exact ⟨0, ∅, fun j h e => absurd ⟨j, h, e⟩ h1, fun i h e => absurd ⟨i, h, e⟩ h2⟩
  choose ν fd hν using H
  exact ⟨⟨ν, fd, M₀.νN, M₀.fdN⟩, fun j h => (hν _).1 j h rfl, fun i h => (hν _).2 i h rfl⟩

end GlobalTheory.RowClaim.StepsModel

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowClaim.JetsAssembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem defTot_eq_sum {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    (M : Vol G) (σ : PolCol G × PolRow G →₀ ℂ) (τ : PureDat G t →₀ ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) :
    defTot t S M σ τ φ F = σ.sum fun P c => c * defTot t S M (Finsupp.single P 1) τ φ F := by
  unfold defTot
  refine Finsupp.sum_congr fun P _ => ?_
  rw [Finsupp.sum_single_index (by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun d _ => ?_
  ring

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetsOne (ch : Choice R) : Prop :=
  ∀ P : PolCol ch.G × PolRow ch.G, ∃ κ : ℂ, ∀ t a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M τ,
    IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y,
      defTot t ch.S.toGridChoice M (Finsupp.single P 1) τ (colFn ch a) (formTop ch t y) =
        κ * ch.S.classSum (ch.Phi a) β τ (psiC (ch.Psi a)) (ch.S.formC t y)

theorem jetsAt_of_one (ch : Choice R) (hL : R.toLevCh.Is A.μ0) (h : JetsOne ch) : JetsAt ch := by
  refine ⟨fun t Φ β => StepsModel.exists_isTermVol ch.S.toGridChoice hL t Φ β, fun σ => ?_⟩
  choose κ hκ using h
  refine ⟨σ.sum fun P c => c * κ P, fun t a β hβ M τ hM hτ y => ?_⟩
  rw [defTot_eq_sum, Finsupp.sum_mul]
  refine Finsupp.sum_congr fun P _ => ?_
  rw [hκ P t a β hβ M τ hM hτ y, mul_assoc]

end GlobalTheory.RowClaim.JetsAssembly

end
