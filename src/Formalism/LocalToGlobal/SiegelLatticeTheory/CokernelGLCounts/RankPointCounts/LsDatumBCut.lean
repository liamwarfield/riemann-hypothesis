module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBDefs
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumB
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open scoped BigOperators
open Classical

section Abstract

theorem hasSum_of_fiber {P G : Type*} [Finite P] (c : P → ℂ) (cls : P → G) (F : G → ℂ)
    (hF : ∀ g, HasSum (fun x : {x : P // cls x = g} => c x.1) (F g)) {s : ℂ} (hs : HasSum F s) :
    HasSum c s := by
  haveI := Fintype.ofFinite P
  have h1 : HasSum c (∑ x, c x) := hasSum_fintype c
  have h2 := h1.tsum_fiberwise cls
  have e : F = fun g => ∑' x : ↑(cls ⁻¹' {g}), c x := funext fun g => ((hF g).tsum_eq).symm
  have h4 : HasSum F (∑ x, c x) := by
    rw [e]
    exact h2
  rw [hs.unique h4]
  exact h1

variable {ι : Type*} {X : ι → Type*}

def Rst (x0 : ∀ p, X p) : Type _ := {x : ∀ p, X p // {p | x p ≠ x0 p}.Finite}

theorem hasSum_rst (x0 : ∀ p, X p) (f : ∀ p, X p → ℂ) (a : ι → ℂ) (S : Finset ι)
    (hoff : ∀ p ∉ S, ∀ x, f p x = if x = x0 p then 1 else 0)
    (hf : ∀ p ∈ S, HasSum (f p) (a p)) (hn : ∀ p ∈ S, Summable fun x => ‖f p x‖) :
    HasSum (fun x : Rst x0 => ∏ᶠ p, f p (x.1 p)) (∏ p ∈ S, a p) := by
  have h0 := (Formalism.L2.SG.Pf.hasSum_prod_offS x0 f a S hf hn).1
  let j : Formalism.L2.SG.Pf.OffS x0 S → Rst x0 := fun θ =>
    ⟨θ.1, (S.finite_toSet).subset fun p hp => by
      by_contra h
      exact hp (θ.2 p h)⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (congrArg (fun x : Rst x0 => x.1) h)
  have hsupp : ∀ x : Rst x0, (Function.mulSupport fun p => f p (x.1 p)) ⊆ (S : Set ι) ∪ {p | x.1 p ≠ x0 p} := by
    intro x p hp
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
    exact (Function.mem_mulSupport.1 hp) (by rw [hoff p hc.1, if_pos hc.2])
  have hfin : ∀ x : Rst x0, (Function.mulSupport fun p => f p (x.1 p)).Finite := fun x =>
    ((S.finite_toSet).union x.2).subset (hsupp x)
  have hzero : ∀ x ∉ Set.range j, (∏ᶠ p, f p (x.1 p)) = 0 := by
    intro x hx
    have : ∃ p ∉ S, x.1 p ≠ x0 p := by
      by_contra h
      push_neg at h
      exact hx ⟨⟨x.1, h⟩, rfl⟩
    obtain ⟨p, hpS, hp⟩ := this
    exact finprod_eq_zero _ p (by rw [hoff p hpS, if_neg hp]) (hfin x)
  rw [← hj.hasSum_iff hzero]
  convert h0 using 1
  funext θ
  apply finprod_eq_prod_of_mulSupport_subset
  intro p hp
  by_contra hS
  exact (Function.mem_mulSupport.1 hp) (by rw [hoff p hS, if_pos (θ.2 p hS)])

theorem hasSum_passage {P G : Type*} [Finite P] (c : P → ℂ) (cls : P → G) (F : G → ℂ)
    (hF : ∀ g, HasSum (fun x : {x : P // cls x = g} => c x.1) (F g))
    (x0 : ∀ p, X p) (loc : G ≃ Rst x0) (f : ∀ p, X p → ℂ) (a : ι → ℂ) (S : Finset ι)
    (hFp : ∀ g, F g = ∏ᶠ p, f p ((loc g).1 p))
    (hoff : ∀ p ∉ S, ∀ x, f p x = if x = x0 p then 1 else 0)
    (hf : ∀ p ∈ S, HasSum (f p) (a p)) (hn : ∀ p ∈ S, Summable fun x => ‖f p x‖) :
    HasSum c (∏ p ∈ S, a p) := by
  have h1 := hasSum_rst x0 f a S hoff hf hn
  have h2 : HasSum F (∏ p ∈ S, a p) := by
    have e : F = (fun x : Rst x0 => ∏ᶠ p, f p (x.1 p)) ∘ loc := funext fun g => hFp g
    rw [e]
    exact (loc.hasSum_iff).2 h1
  exact hasSum_of_fiber c cls F hF h2

end Abstract

end Formalism.L2.SG.LsDatumB
end
end

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Local

variable {D : Formalism.BasicNotions.D7}

abbrev MatP (D : Formalism.BasicNotions.D7) (p : PlF D) : Type :=
  Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ)

def kkOrb (p : PlF D) (Y : MatP D p) : Set (MatP D p) :=
  {Y' | ∃ l ρ : MatP D p, Formalism.MainNotions.S.TieN.IntLow (M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (M p) ρ ∧ Y' = l * Y * ρ}

def IntP (p : PlF D) (Y : MatP D p) : Prop := ∀ a b, Y a b ∈ (M p).R

def InOrbP (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : Prop :=
  ∃ w₀, modPt δ T T' p w = some w₀ ∧
    ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
      Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2

def phL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : ℂ :=
  match modPt δ T T' p w with
  | none => 0
  | some w₀ =>
    if h : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
        Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 then
      dfac M δ T T' p w *
        (M p).psiR (Loc.simpleLow (Loc.uLow h.choose.1) + Loc.simpleUp (Loc.uUp w₀ h.choose.2))
    else 0

def wtL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : ℝ :=
  match modPt δ T T' p w with
  | none => 0
  | some w₀ =>
    (((Measure.pi fun _ : Loc.IL (D.R.rS + 1) => (M p).mu).prod (Measure.pi fun _ : Loc.IN w₀ => (M p).mu))
      {xy | Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y}).toReal

def thL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : Option ((M p).Cls D.R.rS) :=
  clsOf (M p) (Y + Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ T T' p w else 0)

def nIsoO (p : PlF D) (o o' : Option ((M p).Cls D.R.rS)) : ℕ :=
  match o, o' with
  | some c, some c' => (M p).nIso (Quotient.out c) (Quotient.out c')
  | _, _ => 0

def IsLCls (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : Prop :=
  ∃ Y, IntP M p Y ∧ InOrbP δ T T' p w Y ∧ O = kkOrb M p Y

def repL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : MatP D p :=
  if h : IsLCls M δ T T' p w O then h.choose else 0

def fL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ) *
      (nIsoO M p τ (thL M δ T T' p w (repL M δ T T' p w O)) : ℂ)
  else 0

def gL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O ∧ thL M δ T T' p w (repL M δ T T' p w O) = τ then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ)
  else 0

def hL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ)
  else 0

def kL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then (nIsoO M p τ (thL M δ T T' p w (repL M δ T T' p w O)) : ℂ) else 0

def eL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O ∧ thL M δ T T' p w (repL M δ T T' p w O) = τ then 1 else 0

def sgnP (p : PlF D) : MatP D p := Matrix.diagonal fun b : Fin (D.R.rS + 1) => (-1) ^ (D.R.rS - b.val)

def x0L (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : Set (MatP D p) := kkOrb M p (modMat δ T T' p w)

end Local

section Glob

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def nrep (γ : TermDef.Term D u u' F0 what₂) :
    Option (Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D) :=
  if h : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 then some h.choose else none

def zT (γ : TermDef.Term D u u' F0 what₂) : PairVal.MatR D :=
  match nrep γ with
  | some x => ZhatL (lf D F0) x.2.1
  | none => 0

def ptT (γ : TermDef.Term D u u' F0 what₂) : Point D.host.E (D.R.rS + 1) :=
  match nrep γ with
  | some x => x.1
  | none => PairVal.junkPoint D u u'

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)

def thT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : Option ((M p).Cls D.R.rS) :=
  thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (CntLocal.ZZP (M := M) δ u u' p (zT γ))

def locT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : Set (MatP D p) :=
  kkOrb M p (CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p)

def dnT (L : CntLocal.LocSp D M) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (γ : TermDef.Term D u u' F0 what₂) : ℝ :=
  ∏' p, CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') (zT γ) p

end Glob

end Formalism.L2.SG.LsDatumB
end
end

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Cut

variable {D : Formalism.BasicNotions.D7}

def LocOrbSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (p : PlF D) (τ : Option ((M p).Cls D.R.rS)),
    HasSum (fL M δ (D.mem u).A.T (D.mem u').A.T p w τ) (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ) ∧
    Summable (fun O => ‖fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O‖) ∧
    (τ ≠ none → HasSum (gL M δ (D.mem u).A.T (D.mem u').A.T p w τ)
      (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ / Pf.autP M p τ) ∧
    Summable (fun O => ‖gL M δ (D.mem u).A.T (D.mem u').A.T p w τ O‖))

def LocUnram (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∃ S : Finset (PlF D), ∀ p ∉ S, Pf.autP M p (θ0 p) = 1 ∧
    ∀ (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)),
      fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
          (if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w ∧ τ = θ0 p then 1 else 0) ∧
      gL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
          (if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w ∧ τ = θ0 p then 1 else 0)

def ThRestricted (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → Pf.Restricted θ0 (thT M δ γ)

def ThSome (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p, thT M δ γ p ≠ none

def ScalKind (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ γ' : TermDef.Term D u u' F0 what₂) (w w' : Point D.host.E (D.R.rS + 1)), EligAt γ w → EligAt γ' w' →
    Corank.TermScal D γ γ' → kind w = kind w'

def EligFinite (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), {γ : TermDef.Term D u u' F0 what₂ | EligAt γ w}.Finite

def AtPtG (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), γ.atPt w →
    Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0

def PartnerTupleSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
    (∀ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' → EligAt γ' w' →
      {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
          (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
          PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ'.1 w')
        (∏ᶠ p, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p))

def FiberTupleSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ → kind w = kind w₀ →
    (∀ γ : TermDef.Term D u u' F0 what₂, EligAt γ w →
      {p | locT M δ γ p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
          (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ.1 w)
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p))

def CoefProd (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ w =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (locT M δ γ p)) *
        ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ)

def PartnerCount (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
    (∀ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' → EligAt γ' w' →
      {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
          (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
          ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ))
        (∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p))

def FiberCount (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ → kind w = kind w₀ →
    (∀ γ : TermDef.Term D u u' F0 what₂, EligAt γ w →
      {p | locT M δ γ p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
          (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p))

def DnInDens (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∃ Λ ∈ what₂, (CntLocal.EZ (CntLocal.Tn u') F0 Λ (zT γ)).Nonempty

def NormRepElig (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2

def CutAt (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  LocOrbSum M δ u u' ∧ ScalKind u u' F0 what₂ ∧
    CoefProd M δ u u' F0 what₂ ∧ PartnerCount M δ u u' F0 what₂ ∧ FiberCount M δ L u u' F0 what₂ ∧
    NormRepElig u u' F0 what₂ ∧ ThSome M δ u u' F0 what₂ ∧
    ∃ θ0 : ∀ p, Option ((M p).Cls D.R.rS), LocUnram M δ u u' θ0 ∧ ThRestricted M δ u u' F0 what₂ θ0

end Cut

end Formalism.L2.SG.LsDatumB
