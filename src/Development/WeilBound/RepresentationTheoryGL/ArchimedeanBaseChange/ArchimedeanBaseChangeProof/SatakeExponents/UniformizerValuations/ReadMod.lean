module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SatIndepOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.RunFinOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PeakTraceBound

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

abbrev lp (P : Pre E n) (w : Pl E) := locProd P.h w (P.σ · w)

def SmVec {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V) : Prop :=
  ∃ U : Subgroup G, IsOpen (U : Set G) ∧ x ∈ fixed ρ U

def Sep {G V X : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G V) (S : Submodule ℂ V) (τ : Representation ℂ G X) : Prop :=
  (∀ g, ∀ x ∈ S, ρ g x ∈ S) ∧ ∃ (J : Type) (L : J → V →ₗ[ℂ] X),
    (∀ j g, ∀ x ∈ S, SmVec ρ x → L j (ρ g x) = τ g (L j x)) ∧ ∀ x ∈ S, SmVec ρ x → (∀ j, L j x = 0) → x = 0

def LeafMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)) (w : Pl E)
  (σ : SmIrr (GLw N w)), IsDiscrete V → IsLocCompGL V w σ → Sep ((finRep E N).comp (locGL E N w)) V σ.ρ

def NodeMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (t₁ : Tr E r) (t₂ : Tr E s) (w : Pl E)
  (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ₁ : Representation ℂ (GLw r w) X)
  (τ₂ : Representation ℂ (GLw s w) Y), Sep ((finRep E r).comp (locGL E r w)) t₁.space τ₁ →
  Sep ((finRep E s).comp (locGL E s w)) t₂.space τ₂ →
  Sep ((finRep E (r + s)).comp (locGL E (r + s) w)) (Tr.node t₁ t₂).space
    (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.extTensor τ₁ τ₂))

def JoinMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (χ₁ χ₂ : HChar E)
  (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n) (w : Pl E), IsJoin χ₁ χ₂ Pa Pb D →
  Nonempty ((lp D w).Equiv (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h)
    (GlobalTheory.SmGL.extTensor (twRep (lp Pa w) ((χ₁.loc w).comp GeneralLinearGroup.det))
      (twRep (lp Pb w) ((χ₂.loc w).comp GeneralLinearGroup.det)))))

def TreeMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : Pre E N) (w : Pl E),
  t.Good → t.Untw → TreeParts t P → Sep ((finRep E N).comp (locGL E N w)) t.space (lp P w)

def ReadMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (s₁ : Tr E a) (s₂ : Tr E b)
  (Pa : Pre E a) (Pb : Pre E b) (w : Pl E), s₁.Good → s₂.Good → s₁.Untw → s₂.Untw → TreeParts s₁ Pa → TreeParts s₂ Pb →
  Sep (pairRt a b w) (pairSpace s₁.space s₂.space) (GlobalTheory.SmGL.extTensor (lp Pa w) (lp Pb w))

def TreeModOf : Prop := LeafMod → NodeMod → JoinMod → TreeMod

def ReadModOf : Prop := TreeMod → ReadMod

def TreeSatOf : Prop := TreeMod → TreeSat

end PositivityTheory.Rg.BcB.F.RS

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEx
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataFinite
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.One

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def RunOut (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (HeightOneSpectrum (𝓞 E))) (D : Pre E n) : Prop :=
  Base π D ∧ (∀ w ∈ S, IsSplitAt w → D.SplitAt π w) ∧ ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w

def RunOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S T : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ D : Pre E n, RunOut π S T D

def Pre.Agree (D D' : Pre E n) : Prop :=
  (∃ e : Fin D.c ≃ Fin D'.c, ∀ i w, D.cls i w = D'.cls (e i) w) ∧ ∀ τ, ∑ i, D.m i τ = ∑ i, D'.m i τ

def DataFinite : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ (k : ℕ) (L : Fin k → Pre E n), ∀ (T : Finset (HeightOneSpectrum (𝓞 E))) (D : Pre E n), RunOut π S T D →
      ∃ j, D.Agree (L j)

def RunAgree : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (HeightOneSpectrum (𝓞 E))) (D D' : Pre E n), D.Agree D' → RunOut π S T D → RunOut π S T D'

theorem runFin_of (h1 : RunOne) (h2 : DataFinite) (h3 : RunAgree) : RunFin := by
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨k, L, hL⟩ := h2 E hE n hn π hπ S hS
  classical

  let good : Fin k → Prop := fun j => ∃ T D, RunOut π S T D ∧ D.Agree (L j)
  have hg : ∀ j, good j → RunOut π S ∅ (L j) := fun j ⟨T, D, hD, hA⟩ =>
    let h := h3 E n π S T D (L j) hA hD
    ⟨h.1, h.2.1, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  let idx := {j : Fin k // good j}
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin idx
  refine ⟨m, fun i => L (e.symm i).1, fun i => ⟨(hg _ (e.symm i).2).1, (hg _ (e.symm i).2).2.1⟩, fun T => ?_⟩
  obtain ⟨D, hD⟩ := h1 E hE n hn π hπ S T hS
  obtain ⟨j, hj⟩ := hL T D hD
  refine ⟨e ⟨j, T, D, hD, hj⟩, ?_⟩
  show ∀ w ∈ T, IsUnramU π w → ¬IsSplitAt w → InertAt π (L (e.symm (e ⟨j, T, D, hD, hj⟩)).1) w
  rw [Equiv.symm_apply_apply]
  exact (h3 E n π S T D (L j) hj hD).2.2

end PositivityTheory.Rg.BcB.F

end
end

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5

namespace PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def TOut (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (HeightOneSpectrum (𝓞 E)))
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (D : Pre E n) : Prop :=
  Base π D ∧ (∀ w ∈ S, IsSplitAt w → D.SplitAt π w) ∧ (∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w) ∧
    (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D.h w (D.σ · w)) (K w)) ∧ ∀ i, HasKType (W (D.N i)) (D.V i)

structure Setup (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (HeightOneSpectrum (𝓞 E)))
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) where
  A : Type
  [cr : CommRing A]
  [sr : StarRing A]
  [al : Algebra ℂ A]
  [sm : StarModule ℂ A]
  ι : Type
  [ft : Fintype ι]
  [ne : Nonempty ι]
  H : ι → Type
  [ng : ∀ s, NormedAddCommGroup (H s)]
  [ip : ∀ s, InnerProductSpace ℂ (H s)]
  [cs : ∀ s, CompleteSpace (H s)]
  R : ∀ s, A →⋆ₐ[ℂ] (H s →L[ℂ] H s)
  β : ∀ s, H s →L[ℂ] H s
  m : ℕ
  V : Type
  [ag : AddCommGroup V]
  [md : Module ℂ V]
  [fd : FiniteDimensional ℂ V]
  ρ : A →ₐ[ℂ] Module.End ℂ V
  u : Module.End ℂ V
  p : A →⋆ₐ[ℂ] ℂ
  a₀ : A
  pa₀ : p a₀ ≠ 0
  comm : ∀ s g, Commute (β s) (R s g)
  commU : ∀ g, Commute u (ρ g)
  bound : ∀ g ∈ Ideal.span {a₀}, ∃ (C : ℝ) (N j : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖LinearMap.trace ℂ V ((u * ρ g) ^ k)‖ ≤ C * (1 + k) ^ N *
      Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * R s g) ^ (k - j)‖)
  eig : ∃ v : V, v ≠ 0 ∧ u v = v ∧ ∀ g, ρ g v = p g • v
  read : ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (R s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
    (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) →
    (∀ g, χ ⟨R s g, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ = p g) →
    χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0 → ∃ D : Pre E n, TOut π S T K W D

def SetupEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
      (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)), IsLevel K ∧ (∀ N, FiniteDimensional ℂ (W N)) ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 E)), Nonempty (Setup π S T K W)

theorem runT_of (h1 : PeakTraceBound) (h2 : SetupEx) : RunT := by
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨K, W, hK, hW, hX⟩ := h2 E hE n hn π hπ S hS
  refine ⟨K, W, hK, hW, fun T => ?_⟩
  obtain ⟨X⟩ := hX T
  letI := X.cr; letI := X.sr; letI := X.al; letI := X.sm; letI := X.ft; letI := X.ne; letI := X.ng; letI := X.ip
  letI := X.cs; letI := X.ag; letI := X.md; letI := X.fd
  obtain ⟨s, χ, h1', h2', h3'⟩ := h1 X.A X.ι X.H X.R X.β X.m X.V X.ρ X.u X.p X.a₀ X.comm X.commU X.pa₀ X.bound X.eig
  exact X.read s χ h1' h2' h3'

end PositivityTheory.Rg.BcB.F

end
end
