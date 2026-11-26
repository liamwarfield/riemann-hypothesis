module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CandSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.InfUniq

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LemDCand
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.PairNe
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.LemDd.PairSpaceNonzero

theorem pairSpace_left_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (U₂ : Submodule ℂ (Sm E b)) : pairSpace (⊥ : Submodule ℂ (Sm E a)) U₂ = ⊥ := by
  unfold pairSpace
  rw [Submodule.span_eq_bot]
  rintro F ⟨φ₁, h₁, φ₂, -, rfl⟩
  rw [Submodule.mem_bot] at h₁
  subst h₁
  funext x
  simp

theorem pairSpace_right_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (U₁ : Submodule ℂ (Sm E a)) : pairSpace U₁ (⊥ : Submodule ℂ (Sm E b)) = ⊥ := by
  unfold pairSpace
  rw [Submodule.span_eq_bot]
  rintro F ⟨φ₁, -, φ₂, h₂, rfl⟩
  rw [Submodule.mem_bot] at h₂
  subst h₂
  funext x
  simp

end PositivityTheory.Rg.BcB.F.LemDd.PairSpaceNonzero

namespace PositivityTheory.Rg.BcB.F.LemDd

theorem PairNe_holds : PairNe := by
  intro E _ _ _ a b U₁ U₂ G hG hne
  refine ⟨fun h => hne ?_, fun h => hne ?_⟩
  · subst h
    rw [PairSpaceNonzero.pairSpace_left_bot, Submodule.mem_bot] at hG
    exact hG
  · subst h
    rw [PairSpaceNonzero.pairSpace_right_bot, Submodule.mem_bot] at hG
    exact hG

end PositivityTheory.Rg.BcB.F.LemDd

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.InfPartsHolds
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.LemDd.InfinitesimalSumDecomposition

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem top_zero (τ : E →+* ℂ) : HasInfCharGL (⊤ : Submodule ℂ (Sm E 0)) τ 0 := by
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor]

theorem forall₂_ofFn {α β : Type*} {R : α → β → Prop} :
    ∀ {c : ℕ} (f : Fin c → α) (g : Fin c → β), (∀ i, R (f i) (g i)) → List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | c + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (forall₂_ofFn _ _ fun i => h i.succ)

theorem infOf_sum (τ : E →+* ℂ) {N : ℕ} (t : Tr E N) (hg : t.Good) (hu : t.Untw) (ms : List (Multiset ℂ))
    (hms : List.Forall₂ (fun (x : Σ M : ℕ, Submodule ℂ (Sm E M)) m => HasInfCharGL x.2 τ m)
      (t.leafList.filter fun x => 0 < x.1) ms) : t.InfOf τ ms.sum := by
  induction t generalizing ms with
  | @leaf M V z =>
    have hz : z = 0 := hu z (by simp [Tr.twists])
    subst hz
    rcases hg with ⟨rfl, rfl, -⟩ | ⟨hM, -, -⟩
    · have h0 : ms = [] := by simpa [Tr.leafList] using hms
      subst h0
      exact ⟨0, top_zero τ, by simp⟩
    · have h1 : List.Forall₂ (fun (x : Σ M : ℕ, Submodule ℂ (Sm E M)) m => HasInfCharGL x.2 τ m) [⟨M, V⟩] ms := by
        simpa [Tr.leafList, hM] using hms
      rcases h1 with _ | ⟨hx, hnil⟩
      rename_i m ms'
      cases hnil
      exact ⟨m, hx, by simp⟩
  | @node r s t₁ t₂ ih₁ ih₂ =>
    have hu₁ : t₁.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    have hu₂ : t₂.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    simp only [Tr.leafList, List.filter_append] at hms
    have hd := List.forall₂_drop (List.filter (fun x => decide (0 < x.1)) t₁.leafList).length hms
    rw [List.drop_left] at hd
    have ht := List.forall₂_take (List.filter (fun x => decide (0 < x.1)) t₁.leafList).length hms
    rw [List.take_left] at ht
    refine ⟨_, _, ih₁ hg.1 hu₁ _ ht, ih₂ hg.2 hu₂ _ hd, ?_⟩
    rw [← List.sum_append, List.take_append_drop]

end PositivityTheory.Rg.BcB.F.LemDd.InfinitesimalSumDecomposition

namespace PositivityTheory.Rg.BcB.F.LemDd.Tw

theorem InfParts_holds : InfParts := by
  intro E _ _ _ N t P τ hg hu hp
  have h := InfinitesimalSumDecomposition.infOf_sum τ t hg hu (List.ofFn fun i => P.m i τ) (by
    unfold TreeParts at hp
    rw [← hp]
    exact InfinitesimalSumDecomposition.forall₂_ofFn _ _ fun i => P.inf i τ)
  rwa [List.sum_ofFn] at h

end PositivityTheory.Rg.BcB.F.LemDd.Tw

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PLemD
theorem PositivityTheory.Rg.BcB.F.LemDd.lemD : PositivityTheory.Rg.BcB.F.LemDd.LemD :=
  PositivityTheory.Rg.BcB.F.LemDd.lemD_of PositivityTheory.Rg.BcB.F.LemDd.InfUniq_holds PositivityTheory.Rg.BcB.F.LemDd.Tw.InfParts_holds
    PositivityTheory.Rg.BcB.SpectralAccumulation.InfTreeP.infTree_holds
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical
set_option synthInstance.maxHeartbeats 200000
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.LemDd

theorem cand_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} {F₀ : Frame0 hR π S} {d} {i} {s₁ s₂ Pa Pb D} (c : F₀.Cand d i s₁ s₂ Pa Pb D) :
    (∀ τ, ∑ j, Pa.m j τ = mOf (F₀.A i).χa τ) ∧ (∀ τ, ∑ j, Pb.m j τ = mOf (F₀.A i).χb τ) := by
  obtain ⟨G, hG, h0, -⟩ := c.vec
  have h := PairNe_holds _ _ _ _ _ G hG h0
  exact ⟨fun τ => lemD _ _ s₁ Pa τ _ c.ctx.g₁ c.ctx.u₁ c.ctx.t₁ (c.inf₁ τ) h.1,
    fun τ => lemD _ _ s₂ Pb τ _ c.ctx.g₂ c.ctx.u₂ c.ctx.t₂ (c.inf₂ τ) h.2⟩

end PositivityTheory.Rg.BcB.F.LemDd

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def SIso (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) : Prop := ∃ h : x.1 = y.1, IsoV (h ▸ x.2) y.2

def Strict {n : ℕ} (P P' : Pre E n) : Prop :=
  List.Forall₂ SIso (parts P) (parts P') ∧ ∃ h : P.c = P'.c, ∀ i, P.m i = P'.m (Fin.cast h i)

def FinStrict : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ)
  (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))),
  Levels E Θ → KTypes E Ω → ∀ m₀ : (E →+* ℂ) → Multiset ℂ,
  ∃ (k : ℕ) (Pl : Fin k → Pre E a), ∀ P : Pre E a,
    (∀ j, ∃ K' ∈ Θ (P.N j), ∃ W' ∈ Ω (P.N j), HasType K' W' (P.V j)) → (∀ τ, ∑ j, P.m j τ = m₀ τ) →
      ∃ i, Strict P (Pl i)

def StrictEqv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P P' P'' : Pre E n),
  (Strict P P' → Strict P' P) ∧ (Strict P P' → Strict P' P'' → Strict P P'')

def StrictPre : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P P' : Pre E n),
  Strict P P' → PreEquiv P P'

def StrictProd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P P' : Pre E n),
  Strict P P' → ∀ w : Pl E, Nonempty ((prodAt P w).Equiv (prodAt P' w))

def StrictJoin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (χ₁ χ₂ : HChar E)
  (Pa Pa' : Pre E a) (Pb Pb' : Pre E b) (D D' : Pre E n), IsJoin χ₁ χ₂ Pa Pb D → IsJoin χ₁ χ₂ Pa' Pb' D' →
    Strict Pa Pa' → Strict Pb Pb' → Strict D D'

def CandParts : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (d : LocData E n) i s₁ s₂ Pa Pb D,
  F₀.Cand d i s₁ s₂ Pa Pb D →
    (∀ j, ∃ K' ∈ rlΘ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) (Pa.N j),
      ∃ W' ∈ rlΩ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (Pa.N j), HasType K' W' (Pa.V j)) ∧
    (∀ j, ∃ K' ∈ rlΘ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) (Pb.N j),
      ∃ W' ∈ rlΩ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (Pb.N j), HasType K' W' (Pb.V j))

def LevOpen : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T' : Finset (Pl E)) c e b (a : ℕ), a ≤ n →
  IsOpen (lev₁ F₀.Sec (F₀.loc T' c e b) a : Set (GL (Fin a) (Af E))) ∧
    IsOpen (lev₂ F₀.Sec (F₀.loc T' c e b) a : Set (GL (Fin (n - a)) (Af E)))

def IsoInv : Prop := ∀ (G V V' : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V'), Nonempty (ρ.Equiv ρ') → ∀ K : Subgroup G,
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W),
      GlobalTheory.SmGL.IsSubquotient τ ρ ↔ GlobalTheory.SmGL.IsSubquotient τ ρ') ∧
    Module.finrank ℂ (fixed ρ K) = Module.finrank ℂ (fixed ρ' K) ∧
    (FiniteDimensional ℂ (fixed ρ K) ↔ FiniteDimensional ℂ (fixed ρ' K))

def AdmProd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Pre E n) (w : Pl E)
  (K : Subgroup (GLw n w)), IsOpen (K : Set (GLw n w)) → K ≤ GlobalTheory.LFun.KGL w (n := n) → FiniteDimensional ℂ (fixed (prodAt P w) K)

def CandFinOf : Prop :=
  JEigFin → FinStrict → StrictEqv → StrictPre → StrictProd → StrictJoin → CandParts → LevOpen → IsoInv → AdmProd → FX.CandFin

end PositivityTheory.Rg.BcB.F.FX.Bo

end
