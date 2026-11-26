module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterSpaces.HasInfCharGLSpace
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.InfTreeP

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasInfCharGL_tw {N : ℕ} {V : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (z : ℂ) : HasInfCharGL (tw V z) τ (m.map (· + z)) := by
  have hW := GlobalTheory.NormIndCap.hasInfCharGL_map_mulChi h (GlobalTheory.CuspRep.Model.absC E z)
  rw [GlobalTheory.CuspRep.Model.expo_absC] at hW
  exact hW

theorem prod_cancel (m₁ m₂ : Multiset ℂ) (u : ℂ) (r s : ℕ) :
    ((m₁.map (· + (s : ℂ) / 2)).map (u - (s : ℂ) / 2 + ·)).prod *
        ((m₂.map (· + -(r : ℂ) / 2)).map (u + (r : ℂ) / 2 + ·)).prod = ((m₁ + m₂).map (u + ·)).prod := by
  rw [Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_map, Multiset.map_map]
  congr 2
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

theorem hasInfCharGL_node {r s : ℕ} {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {τ : E →+* ℂ}
    {m₁ m₂ : Multiset ℂ} (P : Sm E (r + s) → Prop) (h₁ : HasInfCharGL U₁ τ m₁) (h₂ : HasInfCharGL U₂ τ m₂) :
    HasInfCharGL (Submodule.span ℂ {φ | MemInd2 (tw U₁ ((s : ℂ) / 2)) (tw U₂ (-(r : ℂ) / 2)) φ ∧ P φ}) τ
      (m₁ + m₂) := by
  refine ⟨by rw [Multiset.card_add, h₁.1, h₂.1], fun u φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem F hF =>
    have hc : cap τ u F = (((m₁.map (· + (s : ℂ) / 2)).map (u - (s : ℂ) / 2 + ·)).prod *
        ((m₂.map (· + -(r : ℂ) / 2)).map (u + (r : ℂ) / 2 + ·)).prod) • F :=
      PositivityTheory.Rg.Rs.PInfInd2A.casimir_on_parabolic_induction (n := ![r, s]) (tw U₁ ((s : ℂ) / 2)) (tw U₂ (-(r : ℂ) / 2)) τ _ _
        (hasInfCharGL_tw h₁ _) (hasInfCharGL_tw h₂ _) u F hF.1
    rw [hc, prod_cancel]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem hasInfCharGL_space {N : ℕ} (t : Tr E N) (τ : E →+* ℂ) (m : Multiset ℂ) (h : t.InfOf τ m) :
    HasInfCharGL t.space τ m := by
  induction t generalizing m with
  | leaf V z =>
    obtain ⟨m₀, h₀, rfl⟩ := h
    exact hasInfCharGL_tw h₀ z
  | node t₁ t₂ ih₁ ih₂ =>
    obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := h
    exact hasInfCharGL_node _ (ih₁ m₁ h₁) (ih₂ m₂ h₂)

theorem infTree_holds : InfTree := fun _ _ _ _ _ t τ m h => hasInfCharGL_space t τ m h

end PositivityTheory.Rg.BcB.SpectralAccumulation.InfTreeP

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.LemDd

def InfUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)) (τ : E →+* ℂ)
  (m m' : Multiset ℂ), V ≠ ⊥ → HasInfCharGL V τ m → HasInfCharGL V τ m' → m = m'

def InfParts : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : PositivityTheory.Rg.BcB.F.Pre E N)
  (τ : E →+* ℂ), t.Good → t.Untw → TreeParts t P → t.InfOf τ (∑ i, P.m i τ)

def PairNe : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (U₁ : Submodule ℂ (Sm E a))
  (U₂ : Submodule ℂ (Sm E b)) (G : PositivityTheory.Rg.BcB.E.H E a b → ℂ), G ∈ pairSpace U₁ U₂ → G ≠ 0 → U₁ ≠ ⊥ ∧ U₂ ≠ ⊥

def LemD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : PositivityTheory.Rg.BcB.F.Pre E N)
  (τ : E →+* ℂ) (m : Multiset ℂ), t.Good → t.Untw → TreeParts t P → HasInfCharGL t.space τ m → t.space ≠ ⊥ →
    ∑ i, P.m i τ = m

theorem lemD_of (h1 : InfUniq) (h2 : InfParts) (h3 : InfTree) : LemD := by
  intro E _ _ _ N t P τ m hg hu hp hm h0
  exact h1 E N t.space τ _ _ h0 (h3 E N t τ _ (h2 E N t P τ hg hu hp)) hm

end PositivityTheory.Rg.BcB.F.LemDd

end
