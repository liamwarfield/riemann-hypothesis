module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.FrameWordLengthEqOneOfHyp
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.PLocWord
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.PLocMatch
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.FrameBoundOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.HM2

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PTraceword
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.traceword_pf :
    U.UWord → LocMatch → ChainSc → FBL.EllHom → AdelWord → ArchSc → USph → UOk → FrFacts → TraceWord := by
  intro hUW hLM hCS hEH hAW hAS hUS hUO hFF hR E _ _ _ n π S T F₀ F hE hF ws hws
  obtain ⟨hμ, hnorm, hgood, hP⟩ := hFF hR E n π S T F₀ F
  obtain ⟨hcnt, hsph⟩ := hUS hR E n π S T F₀ F ws
  have hk : 1 ≤ ws.length := List.length_pos_iff.2 hws
  obtain ⟨hHecke, hsep, hall⟩ := hLM E hE n F.d F.ok F.mok F₀.Sec F₀.hSec F.levOff F.T_ne hnorm hgood (lw F ws) F.m ws.length
    F.m_pos hk hcnt (ws.flatten.map (ul F)) (fun w _ => hsph w)
  have hlU : ∀ x ∈ ws.flatten.map (ul F), U.UGen.Ok F₀.Sec F.d.B x := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    exact (hUO hR E n π S T F₀ F hE p).1
  obtain ⟨hT, htr⟩ := hUW E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff hHecke ws.length _ hlU
  rw [htr hsep]
  have hch := hCS E n F₀.μ F₀.e F₀.lam F₀.C F₀.Sec F₀.hSec F.d.KU _ F.levOff.2.1 hT F₀.u₁ F₀.u₂ F₀.hu
    (fun a => (prodL F.d (lw F ws) a).tr F.d.P F.d.one) (fun a => (prodL F.d (lw F ws) a).t)
    (fun a ha => by
      obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hall a ha
      refine ⟨h1, h2, h3, fun w hw => ?_⟩
      rw [← hμ w]
      exact h4 w hw)
    (fun i => by
      obtain ⟨-, w, hw, hns, hreg⟩ := hall (F₀.C.a i) (F₀.C.le i)
      refine ⟨w, hw, ?_⟩
      have : seen ((prodL F.d (lw F ws) (F₀.C.a i)).tr F.d.P F.d.one) (prodL F.d (lw F ws) (F₀.C.a i)).t w =
          (prodL F.d (lw F ws) (F₀.C.a i)).tr F.d.P F.d.one w := by
        funext y
        simp [seen, hns]
      rw [this]
      exact hreg)
    (fun i v => (tw F i ws).va v ((F₀.A i).χa v) * (tw F i ws).vb v ((F₀.A i).χb v))
    (fun i => (tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb)
    (fun i v => ((hAW hR E n π S T F₀ F hF i ws).2.2 v))
    (fun i => BGen.sc (ws.map (bw F i)).flatten) (U.UGen.sc (ws.flatten.map (ul F)))
    (fun i => by
      rw [Finset.prod_mul_distrib]
      exact hAS hR E n π S T F₀ F hF i ws)
  rw [hch]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h1, h2, -⟩ := hAW hR E n π S T F₀ F hF i ws
  rw [h1, hEH]
  field_simp

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PFrfacts
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem val_one_of_ordL {E : Type} [Field E] [NumberField E] {w : Pl E} (u : (w.adicCompletion E)ˣ)
    (hu : ordL (u : w.adicCompletion E) = 0) : Valued.v (u : w.adicCompletion E) = 1 := by
  have h1 : Valued.v (u : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  unfold ordL at hu
  rw [dite_eq_right h1] at hu
  rw [← WithZero.coe_unzero h1]
  have e : Multiplicative.toAdd (WithZero.unzero h1) = 0 := by omega
  have e' : WithZero.unzero h1 = 1 := by
    rw [← ofAdd_toAdd (WithZero.unzero h1), e]; rfl
  rw [e']; rfl

theorem frfacts_pf : FrFacts := by
  intro hR E _ _ _ n π S T F₀ F
  have hsame := F.same
  unfold RF_same at hsame
  obtain ⟨hS₀, hBad, hμ, -⟩ := hsame
  have hloc : ∀ w, F.d.μ w = F₀.μ.loc w := fun w => by rw [hμ]; exact F₀.μloc w
  refine ⟨hloc, fun w u => ?_, fun w hw hB hs => ?_, ?_⟩
  · rw [hloc]
    exact F₀.hμ.1 _
  · have hT : w ∉ F.d.T := fun h => hB (by simp [LocData.B, h])
    have hS : w ∉ F.d.S₀ := fun h => hB (by simp [LocData.B, h])
    have hb : w ∉ F.d.Bad := fun h => hB (by simp [LocData.B, h])
    refine ⟨hs, hT, hS, hb, fun u hu => ?_⟩
    rw [hloc]
    exact (F₀.good w hw (hS₀ ▸ hS) (hBad ▸ hb)).2 u (val_one_of_ordL u hu)
  · intro w hw
    have hw' : w ∈ F.d.T ∪ F.d.S₀ := by simpa [LocData.P] using hw
    rcases Finset.mem_union.mp hw' with h | h
    · exact (F.T_in w h).1
    · exact (F₀.S₀ w (hS₀ ▸ h)).1

end UpperTheory.BaseChangeIdentities.FrameWordIdentity

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PTestword
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.testword_pf :
    PTTest → LocMatch → PsiWord → ProdOk → USph → TwOk → FrFacts → LocOk → TestWord := by
  intro hPT hLM hPsi hProd hSph hTw hFr hLoc hR E _ _ _ n π S T F₀ F hE hF i
  obtain ⟨c₀, hc₀, H⟩ := hPT E (F.B i)
  refine ⟨c₀, hc₀, fun ws hws => ?_⟩
  obtain ⟨-, hnorm, hgood, hP⟩ := hFr hR E n π S T F₀ F
  obtain ⟨hcount, hsph⟩ := hSph hR E n π S T F₀ F ws
  have hk : 1 ≤ ws.length := List.length_pos_iff.2 hws
  have hL := hLM E hE n F.d F.ok F.mok F₀.Sec F₀.hSec F.levOff F.T_ne hnorm hgood (lw F ws) F.m ws.length
    F.m_pos hk hcount (ws.flatten.map (ul F)) (fun w _ => hsph w)
  have hle := F₀.C.le i
  have hreg := (hL.2.2 (F₀.C.a i) hle).2
  exact H F.d.kap F₀.Sec F.d.P (Equiv.refl _) F₀.hSec hP (fun w _ => (hLoc E n F.d F.ok _ hle).1 w)
    (F₀.u₁ _) (F₀.u₂ _) (F₀.hu _).1 (F₀.hu _).2 (F₀.A i).Ta (F₀.A i).Tb F.d.one (tw F i ws)
    (prodL F.d (lw F ws) (F₀.C.a i)) ⟨(F₀.A i).vca, (F₀.A i).vcb⟩ ((hTw hR E n π S T F₀ F hF i).2.2 ws)
    (hProd E n F.d F.ok _ _ hle) (hPsi hR E n π S T F₀ F i ws) hreg

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PPsiword
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.psiword_pf :
    PsiGen → PsiLet → heckeLevelWordBase → LocOk → MLM.MatchLMId → FrFacts → PsiWord := by
  intro hG hPL hW hLO hId hFF hR E _ _ _ n π S T F₀ F i ws
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  have hE := hW E n F.d F.ok (F₀.C.a i) ha (.inr (.inl ()))
  have hB := hW E n F.d F.ok (F₀.C.a i) ha (.inl ())
  have hFx : (F.d.fixL (F₀.C.a i)).Ok F.d.P := (hLO E n F.d F.ok (F₀.C.a i) ha).2.2.1
  have hFe : ((F.d.eL (F₀.C.a i)).mul (F.d.fixL (F₀.C.a i))).Eqv F.d.P (F.d.fixL (F₀.C.a i)) :=
    (hId E n F.d F.ok (F₀.C.a i) ha _ (Or.inr (Or.inl rfl))).2
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := (hFF hR E n π S T F₀ F).2.2.2
  let l : List (BGen (F.B i) × LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) :=
    (Sum.inr (F.t₁ i), F.d.fixL (F₀.C.a i)) ::
      (ws.map fun w => List.replicate F.m
          ((Sum.inr (F.β i), F.d.betaL (F₀.C.a i) ha) : BGen (F.B i) × LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) ++
        w.map fun p => (gl F i p, locL F.d (F₀.C.a i) ha (lt F p))).flatten
  have e1 : l.map Prod.fst = Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten := by
    simp only [l, bw, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
    rfl
  have e2 : (l.map Prod.snd).foldr LM.mul (F.d.eL (F₀.C.a i)) = prodL F.d (UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw F ws) (F₀.C.a i) := by
    have : l.map Prod.snd = F.d.fixL (F₀.C.a i) :: (UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw F ws).map (locL F.d (F₀.C.a i) ha) := by
      simp only [l, UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
      rfl
    rw [this, prodL, dite_eq_left ha]
  have hl : ∀ x ∈ l, x.2.Ok F.d.P ∧ ((F.d.eL (F₀.C.a i)).mul x.2).Eqv F.d.P x.2 ∧
      ((∃ c, x.1 = Sum.inl c ∧ x.2 = F.d.eL (F₀.C.a i)) ∨
        ∃ s, x.1 = Sum.inr s ∧ s.ψ = fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) x.2) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hFx, hFe, Or.inr ⟨_, rfl, rfl⟩⟩
    · obtain ⟨y, hy, hxy⟩ := List.mem_flatten.1 hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
      rcases List.mem_append.1 hxy with h | h
      · rw [List.eq_of_mem_replicate h]
        exact ⟨hB.1, hB.2.1, Or.inr ⟨_, rfl, rfl⟩⟩
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 h
        have hp := hW E n F.d F.ok (F₀.C.a i) ha (lt F p)
        refine ⟨hp.1, hp.2.1, ?_⟩
        rcases hPL hR E n π S T F₀ F i p with ⟨c, h1, h2⟩ | ⟨s, h1, h2⟩
        · exact Or.inl ⟨c, h1, h2⟩
        · exact Or.inr ⟨s, h1, h2⟩
  have key := hG E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) F₀.hSec hP (F₀.u₁ _) (F₀.u₂ _)
    (F.d.eL (F₀.C.a i)) (F.t₂ i) hE.1 hE.2.1 rfl l hl
  rw [e1, e2] at key
  exact key

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PArchlet
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a}
  {l₂ : InfinitePlace E → DomWeight b} {μ₁ : Measure (GA E a)} {μ₂ : Measure (GA E b)} {μa : Measure (G a)}
  {μb : Measure (G b)} (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb)

private theorem val_pt {κ : Type} [Fintype κ] (wa wb : InfinitePlace E → List (Bool × ℕ))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (r : ℝ) :
    (A.pt wa wb ψ r).val A.χa A.χb = (∏ v, zVal (wa v) (A.χa v)) * ∏ v, zVal (wb v) (A.χb v) := by
  have h1 : (∏ v, coshT A.bump (cas (A.χa v))) * ∏ v, coshT A.bump (cas (A.χb v)) = 1 := A.one
  show (∏ v, A.valW (wa v) (A.χa v)) * (∏ v, A.valW (wb v) (A.χb v)) = _
  simp only [Arch.valW, Finset.prod_mul_distrib]
  linear_combination ((∏ v, zVal (wa v) (A.χa v)) * ∏ v, zVal (wb v) (A.χb v)) * h1

private theorem zVal_nil {m : ℕ} (χ : Inf m) : zVal [] χ = 1 := rfl

private theorem zVal_ite {m : ℕ} (c : Prop) [Decidable c] (L : List (Bool × ℕ)) (χ : Inf m) :
    zVal (if c then L else []) χ = if c then zVal L χ else 1 := by
  split_ifs <;> rfl

private theorem val_nil {κ : Type} [Fintype κ] (ψ : Matrix κ κ (Hf E a b → ℂ)) (r : ℝ) :
    (A.pt (fun _ => []) (fun _ => []) ψ r).val A.χa A.χb = 1 := by
  rw [val_pt]
  simp [zVal_nil]

private theorem val_der {κ : Type} [Fintype κ] (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool)
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (r : ℝ) :
    (A.pt (fun v' => if v' = v ∧ side = false then [(s, m)] else [])
      (fun v' => if v' = v ∧ side = true then [(s, m)] else []) ψ r).val A.χa A.χb =
      if side then zVal [(s, m)] (A.χb v) else zVal [(s, m)] (A.χa v) := by
  rw [val_pt]
  simp only [zVal_ite]
  cases side <;> simp

end Val

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.archlet_pf :
    BlockOperatorsProductAdjoint → FBL.HermInf → ArchLet := by
  intro hO hH hR E _ _ _ n π S T F₀ F hS i
  have ha : ∀ v, IsHerm ((F₀.A i).χa v) := fun v => hH _ _
  have hb : ∀ v, IsHerm ((F₀.A i).χb v) := fun v => hH _ _
  have base : ∀ x, Sum.elim id (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) (F.g x i) =
      Sum.elim id (fun _ => 1) (F.ug x) := by
    intro x
    rcases x with u | y | y
    · exact val_nil (F₀.A i) _ _
    · rcases y with ⟨j, v, s, m, side⟩
      by_cases hij : i = j
      · subst hij
        simp only [RunFrame.g, RunFrame.ug, if_true, Sum.elim_inr, Sum.elim_inl, id, RunFrame.tD, RunFrame.dval]
        exact val_der (F₀.A i) v s m side _ _
      · simp only [RunFrame.g, RunFrame.ug, hij, if_false, Sum.elim_inl, id]
    · exact val_nil (F₀.A i) _ _
  refine ⟨fun p => ?_, val_nil (F₀.A i) _ _, val_nil (F₀.A i) _ _, val_nil (F₀.A i) _ _⟩
  rcases p with ⟨x, s⟩
  cases s
  · simpa [gl, ul] using base x
  · have hadj : ∀ (g : BGen (F.B i)), g.Ok → Sum.elim id (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) g.adj =
        starRingEnd ℂ (Sum.elim id (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) g) := by
      rintro (c | t) hg
      · simp [BGen.adj]
      · have ht : t.Ok := hg
        simpa [BGen.adj] using (hO E (F.B i) t t ht ht).2.2.2.2.2.2.2 _ _ ha hb
    have huadj : ∀ (u : U.UGen E n), Sum.elim id (fun _ => (1 : ℂ)) (U.UGen.adj u) =
        starRingEnd ℂ (Sum.elim id (fun _ => (1 : ℂ)) u) := by
      rintro (c | y) <;> simp [U.UGen.adj]
    simp only [gl, ul, if_true]
    rw [hadj _ (hS.ok x i), huadj, base]

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.AtPlaceAppend
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit}
  {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)

private theorem lw_cons (w : List (F.Γ × Bool)) (ws : List (List (F.Γ × Bool))) :
    lw F (w :: ws) = (List.replicate F.m (Sum.inl ()) ++ w.map (lt F)) ++ lw F ws := by
  simp [UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw]

private theorem count_lt (w : List (F.Γ × Bool)) : (w.map (lt F)).countP Sum.isLeft = 0 := by
  rw [List.countP_eq_zero]
  intro a ha
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
  rcases p with ⟨(_ | _ | x), b⟩ <;> simp [lt]

private theorem count_lw (ws : List (List (F.Γ × Bool))) :
    (lw F ws).countP Sum.isLeft = F.m * ws.length := by
  induction ws with
  | nil => simp [UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw]
  | cons w ws ih =>
    rw [lw_cons, List.countP_append, List.countP_append, ih, count_lt, List.countP_replicate]
    simp <;> ring

private theorem atPlace_append (w : Pl E) (l₁ l₂ : List (LL F.d)) :
    atPlace F.d w (l₁ ++ l₂) = atPlace F.d w l₁ ++ atPlace F.d w l₂ := by
  simp [atPlace, List.filterMap_append]

private theorem atPlace_rep (w : Pl E) (k : ℕ) :
    atPlace F.d w (List.replicate k (Sum.inl ())) = [] := by
  induction k with
  | zero => simp [atPlace]
  | succ k ih => simpa [atPlace, List.replicate_succ] using ih

private theorem atPlace_lw (w : Pl E) (ws : List (List (F.Γ × Bool))) :
    atPlace F.d w (lw F ws) = atPlace F.d w (ws.flatten.map (lt F)) := by
  induction ws with
  | nil => simp [UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw, atPlace]
  | cons v ws ih =>
    rw [lw_cons, atPlace_append, atPlace_append, ih, atPlace_rep, List.flatten_cons, List.map_append,
      atPlace_append, List.nil_append]

private theorem sph_word (w : Pl E) (l : List (F.Γ × Bool)) :
    U.UGen.sph (l.map (ul F)) w = MLM.wordUS F.d w (atPlace F.d w (l.map (lt F))) := by
  induction l with
  | nil => simp [U.UGen.sph, MLM.wordUS, atPlace]
  | cons p l ih =>
    have hs : ∀ (x : U.UGen E n) (l' : List (U.UGen E n)), U.UGen.sph (x :: l') w =
        Sum.elim (fun _ => U.UGen.sph l' w) (fun y : Σ w : Pl E, UL n w → ℂ =>
          if h : y.1 = w then lconv (h ▸ y.2) (U.UGen.sph l' w) else U.UGen.sph l' w) x := fun _ _ => rfl
    rcases p with ⟨(u | y | x), b⟩
    · have h1 : atPlace F.d w (lt F (Sum.inl u, b) :: l.map (lt F)) = atPlace F.d w (l.map (lt F)) := by
        simp [atPlace, lt]
      rw [List.map_cons, List.map_cons, h1, ← ih, hs]
      cases b <;> simp [ul, RunFrame.ug, U.UGen.adj]
    · have h1 : atPlace F.d w (lt F (Sum.inr (Sum.inl y), b) :: l.map (lt F)) = atPlace F.d w (l.map (lt F)) := by
        simp [atPlace, lt]
      rw [List.map_cons, List.map_cons, h1, ← ih, hs]
      cases b <;> simp [ul, RunFrame.ug, U.UGen.adj]
    · rw [List.map_cons, List.map_cons, hs]
      by_cases h : x.1.1 = w
      · subst h
        have h1 : atPlace F.d x.1.1 (lt F (Sum.inr (Sum.inr x), b) :: l.map (lt F)) =
            (x.2.1, x.2.2, b) :: atPlace F.d x.1.1 (l.map (lt F)) := by
          simp [atPlace, lt]
        rw [h1]
        have h2 : MLM.wordUS F.d x.1.1 ((x.2.1, x.2.2, b) :: atPlace F.d x.1.1 (l.map (lt F))) =
            lconv (if b then lstar (F.d.hU x.1.1 x.2.1) else F.d.hU x.1.1 x.2.1)
              (MLM.wordUS F.d x.1.1 (atPlace F.d x.1.1 (l.map (lt F)))) := rfl
        rw [h2, ← ih]
        cases b <;> simp [ul, RunFrame.ug, U.UGen.adj]
      · have h1 : atPlace F.d w (lt F (Sum.inr (Sum.inr x), b) :: l.map (lt F)) =
            atPlace F.d w (l.map (lt F)) := by
          simp [atPlace, lt, h]
        rw [h1, ← ih]
        cases b <;> simp [ul, RunFrame.ug, U.UGen.adj, h]

end

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.usph_pf :
    USph := by
  intro hR E _ _ _ n π S T F₀ F ws
  refine ⟨count_lw F ws, fun w => ?_⟩
  rw [atPlace_lw, sph_word]

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PAdelword
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.adelWord_of_parts :
    AdelRep → FinConv → PsiWord → ProdOk → LocOk → FrFacts → TwOk → AdelWord := by
  intro hAR hFC hPW hPO hLO hFR hTw hR E _ _ _ n π S T F₀ F hS i ws
  have hle := F₀.C.le i
  have hsec := F₀.hSec
  have hP := (hFR hR E n π S T F₀ F).2.2.2
  have hne : ∀ w ∈ F.d.P, Nonempty (F.d.kap w) := fun w _ => (hLO E n F.d F.ok _ hle).1 w
  have hL0 := hPO E n F.d F.ok (lw F ws) _ hle
  have ht := hPW hR E n π S T F₀ F i ws
  have hok := (hTw hR E n π S T F₀ F hS i).2.2 ws
  have key := hAR E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) hsec hP hne (F₀.u₁ _) (F₀.u₂ _)
    (F₀.A i).Ta (F₀.A i).Tb F.d.one (fun _ => F.d.eL _) [] (tw F i ws)
    (prodL F.d (lw F ws) (F₀.C.a i)) (by simp) hL0 ht
  refine ⟨key.2.2, (hFC E (F.B i) F₀.Sec hsec).1, fun v => ?_⟩
  exact (F₀.A i).lef v _ _ _ _ _ (hok.ka v) (hok.kb v)

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.UokPf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.uok_pf :
    U.UAdj → HuHecke → UOk := by
  intro hA hH hR E _ _ _ n π S T F₀ F hE p
  have hB : ∀ {w : Pl E}, F.d.Good w → w ∉ F.d.B := by
    intro w hw
    obtain ⟨-, hT, hS, hB, -⟩ := hw
    simp [LocData.B, hT, hS, hB]
  have hok : ∀ x, (F.ug x).Ok F₀.Sec F.d.B := by
    intro x
    rcases x with _ | x | x
    · exact trivial
    · exact trivial
    · exact ⟨x.1.2.1, hB x.1.2.2, hH E n F.d F.ok _ x.1.2.2 x.2.1⟩
  obtain ⟨x, b⟩ := p
  have hadj := hA E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff (F.ug x) (hok x)
  cases b
  · simpa [ul] using hok x
  · simpa [ul] using hadj

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.TwokPf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (l : List (BGen B)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s, Sum.inr s ∈ l → s.T ≤ R ∧ s.r + B.c ≤ R := by
  induction l with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons g l ih =>
    obtain ⟨R, hR, hs⟩ := ih
    rcases g with c | t
    · refine ⟨R, hR, fun s hm => ?_⟩
      rcases List.mem_cons.1 hm with h | h
      · cases h
      · exact hs s h
    · refine ⟨max R (max t.T (t.r + B.c)), le_max_of_le_left hR, fun s hm => ?_⟩
      rcases List.mem_cons.1 hm with h | h
      · cases h
        exact ⟨le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
      · exact ⟨(hs s h).1.trans (le_max_left _ _), (hs s h).2.trans (le_max_left _ _)⟩

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.twok_pf :
    BlockWordOperators → TwOk := by
  intro hW hR E _ _ _ n π S T F₀ F h i
  have hadj := (hW E (F.B i) [] (F.t₂ i) 0 (by simp) (h.tok i).2 le_rfl (by simp)).2.2.2.2.1
  have hgl : ∀ p, (gl F i p).Ok ∧ (gl F i p).op = if p.2 then star (F.g p.1 i).op else (F.g p.1 i).op := by
    rintro ⟨x, s⟩
    cases s with
    | false => exact ⟨h.ok x i, rfl⟩
    | true =>
      refine ⟨(hadj _ (h.ok x i)).1, ?_⟩
      show (F.g x i).adj.op = star (F.g x i).op
      rw [(hadj _ (h.ok x i)).2, ContinuousLinearMap.star_eq_adjoint]
  have hbw : ∀ w, ∀ g ∈ bw F i w, g.Ok := by
    intro w g hg
    rcases List.mem_append.1 hg with hg | hg
    · rw [List.eq_of_mem_replicate hg]
      exact h.βok i
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg
      exact (hgl p).1
  refine ⟨hgl, hbw, fun ws => ?_⟩
  obtain ⟨R, hR0, hRs⟩ := exists_bound (Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten)
  refine (hW E (F.B i) _ (F.t₂ i) R ?_ (h.tok i).2 hR0 hRs).1
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact (h.tok i).1
  · obtain ⟨l, hl, hgl'⟩ := List.mem_flatten.1 hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
    exact hbw w g hgl'

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PPsilet
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.psilet_pf :
    FmAlg → LocOk → FrFacts → PsiLet := by
  intro hA hO hF hR E _ _ _ n π S T F₀ F i p
  obtain ⟨g, b⟩ := p
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := (hF hR E n π S T F₀ F).2.2.2
  have hok : ∀ L, F.d.IsGen (F₀.C.a i) (F₀.C.le i) L → L.Ok F.d.P := fun L hL =>
    (hO E n F.d F.ok (F₀.C.a i) (F₀.C.le i)).2.2.2 L hL
  have hadj : ∀ L, F.d.IsGen (F₀.C.a i) (F₀.C.le i) L → adjF (F.ψ i L) = F.ψ i L.adj := fun L hL =>
    (hA E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) F₀.hSec hP L L (hok L hL) (hok L hL)).2.2.2.2
  have heL : (F.d.eL (F₀.C.a i)).adj = F.d.eL (F₀.C.a i) := by
    have hm := LocComm.adj_m F.d (a := F₀.C.a i) (ha := F₀.C.le i) (L := F.d.eL (F₀.C.a i)) (Or.inl rfl)
    have hs : (F.d.eL (F₀.C.a i)).adj.s = (F.d.eL (F₀.C.a i)).s := by
      funext w
      exact LocComm.lfStar_idem _
    have ht : (F.d.eL (F₀.C.a i)).adj.t = (F.d.eL (F₀.C.a i)).t := by
      funext w
      exact LocComm.lfStar_idem _
    cases h : F.d.eL (F₀.C.a i) with
    | mk m s t =>
      rw [h] at hm hs ht
      simp only [LM.adj] at hm hs ht ⊢
      rw [LM.mk.injEq]
      exact ⟨hm, hs, ht⟩
  have heψ : adjF (F.ψ i (F.d.eL (F₀.C.a i))) = F.ψ i (F.d.eL (F₀.C.a i)) := by
    rw [hadj _ (Or.inl rfl), heL]
  rcases g with _ | x | x
  · refine Or.inr ?_
    cases b
    · exact ⟨F.t₀ i, rfl, rfl⟩
    · exact ⟨(F.t₀ i).adj, rfl, heψ⟩
  · by_cases hi : i = x.1
    · refine Or.inr ?_
      cases b
      · exact ⟨F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2, by simp [gl, RunFrame.g, hi], rfl⟩
      · refine ⟨(F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).adj, by simp [gl, RunFrame.g, hi, BGen.adj], heψ⟩
    · refine Or.inl ?_
      cases b
      · exact ⟨F.dval x, by simp [gl, RunFrame.g, hi], rfl⟩
      · exact ⟨starRingEnd ℂ (F.dval x), by simp [gl, RunFrame.g, hi, BGen.adj], rfl⟩
  · refine Or.inr ?_
    cases b
    · exact ⟨F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2), rfl, by simp [lt, locL]; rfl⟩
    · exact ⟨(F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)).adj, rfl,
        (hadj _ (Or.inr ⟨x.1.1, x.2.1, x.2.2, x.1.2.2, rfl⟩)).trans (by simp [lt, locL])⟩

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PProdok
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.prodok_pf :
    TMul → LocOk → heckeLevelWordBase → ProdOk := by
  intro hT hL hW E _ _ _ n d hd ls a ha
  have hk := (hL E n d hd a ha).1
  have hbase : LM.Ok d.P (d.eL a) := (hL E n d hd a ha).2.2.2 _ (Or.inl rfl)
  have hfix := (hL E n d hd a ha).2.2.1
  have hrest : LM.Ok d.P (List.foldr LM.mul (d.eL a) (List.map (locL d a ha) ls)) := by
    induction ls with
    | nil => simpa using hbase
    | cons p ls ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact hT E a (n - a) d.kap d.P hk _ _ (hW E n d hd a ha p).1 ih
  rw [prodL, dite_eq_left ha, List.foldr_cons]
  exact hT E a (n - a) d.kap d.P hk _ _ hfix hrest

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PChainsc
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lefAt_smul {a b : ℕ} [MeasurableSpace (GL (Fin a) ℂ)] [MeasurableSpace (GL (Fin b) ℂ)]
    {ν₁ : Measure (GL (Fin a) ℂ)} {ν₂ : Measure (GL (Fin b) ℂ)} {l₁ : DomWeight a} {l₂ : DomWeight b}
    {val : ℂ} {ψ : GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ} (c : ℂ) (h : LefAt ν₁ ν₂ l₁ l₂ val ψ) :
    LefAt ν₁ ν₂ l₁ l₂ (c * val) (c • ψ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.const_smul c, h2.mono (Function.support_const_smul_subset c ψ), ?_⟩
  intro d₁ d₂ e₁ e₂
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, h3 d₁ d₂ e₁ e₂]
  ring

private theorem prod_update_mul {V : Type*} [Fintype V] [DecidableEq V] (g : V → ℂ) (v₀ : V) (c : ℂ) :
    ∏ v, Function.update g v₀ (c * g v₀) v = c * ∏ v, g v := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v₀),
    ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ v₀), Function.update_self, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun v hv => Function.update_of_ne (Finset.ne_of_mem_erase hv) _ _

private theorem adel_update {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (S : Set (Pl E))
    (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E) (ψ : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (v₀ : InfinitePlace E) (c : ℂ) :
    adel S u₁ u₂ (Function.update ψ v₀ (c • ψ v₀)) φ₁ φ₂ = c • adel S u₁ u₂ ψ φ₁ φ₂ := by
  funext x
  simp only [adel, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  rw [← prod_update_mul (fun v => ψ v (GeneralLinearGroup.map (cV v) x.1, GeneralLinearGroup.map (cV v) x.2)) v₀ c]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v = v₀
  · subst hv
    simp
  · simp [Function.update_of_ne hv]

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.chainsc_pf :
    FBL.EllHom → ChainSc := by
  intro hE E _ _ _ n μ e lam C S hS K' f hK hf u₁ u₂ hu φ₁ φ₂ hφ hreg val ψ hL s z hz
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hL' : ∀ i v, LefAt (C.νC (C.a i)) (C.νC (n - C.a i)) (C.l₁ i v) (C.l₂ i v)
      (Function.update (val i) v₀ (s i * val i v₀) v) (Function.update (ψ i) v₀ (s i • ψ i v₀) v) := by
    intro i v
    by_cases hv : v = v₀
    · subst hv
      simpa using lefAt_smul (s i) (hL i v)
    · simpa [Function.update_of_ne hv] using hL i v
  have hz' : ∀ i, ∏ v, Function.update (val i) v₀ (s i * val i v₀) v = z := fun i => by
    rw [prod_update_mul, hz i]
  have key := C.eq S hS K' f hK hf u₁ u₂ hu φ₁ φ₂ hφ hreg _ _ hL' z hz'
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [adel_update, hE]

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.TmulPf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.tmul_pf :
    TMul := by
  intro E _ _ _ a b κ _ P _ L L' hL hL'
  refine ⟨fun X Y => ?_, FinConv.isTestFunction_mulConvolution hL.2 hL'.2⟩
  have hoff : IsTestP (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w)) :=
    FinConv.isTestFunction_mulConvolution (hL.1 X X) (hL'.1 Y Y)
  refine Fm.isTestFunction_linearCombination (J := Option (Σ i : P, κ i))
    (fun j => j.elim (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w))
      fun q w => mconv (L.ent P X (Function.update X q.1 q.2) w) (L'.ent P (Function.update X q.1 q.2) Y w))
    (fun j => ?_) _ (fun w => ?_) ?_
  · cases j with
    | none => exact hoff
    | some q => exact FinConv.isTestFunction_mulConvolution (hL.1 _ _) (hL'.1 _ _)
  · by_cases hw : w ∈ P
    · exact ⟨κ w, inferInstance, fun z => some ⟨⟨w, hw⟩, z⟩, fun _ => 1, by simp [LM.mul, LM.ent, hw]⟩
    · exact ⟨Unit, inferInstance, fun _ => none, fun _ => 1, by simp [LM.mul, LM.ent, hw]⟩
  · exact Fm.cof_off P hoff fun w hw => by simp [LM.mul, LM.ent, hw]

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PHuhecke
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.huhecke_pf :
    HuHecke := by
  intro E _ _ _ n d hd w hw k
  have hU : UL n w = ⊤ := if_pos hw.1
  exact GlobalTheory.CompanionTheory.MatchWord.isHecke_hU d hd hU k

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PPsigen
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fm_of_eqv {E : Type} [Field E] [NumberField E] [IsCMField E] {κ : Pl E → Type} [∀ w, Fintype (κ w)]
    (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w) {L L' : LM κ B.a B.b}
    (h : L.Eqv P L') : fm S P B e L = fm S P B e L' := by
  have hent : ∀ x y, L.ent P x y = L'.ent P x y := by
    intro x y
    funext w
    unfold LM.ent
    split_ifs with hw
    · rw [h.1 w hw]
    · rw [h.2.1 w hw]
  funext x y g
  simp only [fm, hent, h.2.2]

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.psiGen_of_algebras :
    FmAlg → RtAlg → BlockProductLevels → PsiGen := by
  intro hFm hRt hLev E _ _ _ κ _ S P B e hS hPS u₁ u₂ L₀ t₀ hL₀ hid ht₀ l hl
  have alg := fun L L' (h : L.Ok P) (h' : L'.Ok P) => hFm E κ S P B e hS hPS L L' h h'
  have hrt := (hRt E B u₁ u₂).1
  have key : ∀ l : List (BGen B × LM κ B.a B.b), (∀ x ∈ l, x.2.Ok P ∧ (L₀.mul x.2).Eqv P x.2 ∧
      ((∃ c, x.1 = Sum.inl c ∧ x.2 = L₀) ∨ ∃ s, x.1 = Sum.inr s ∧ s.ψ = fm S P B e x.2)) →
      ((l.map Prod.snd).foldr LM.mul L₀).Ok P ∧
      (BGen.wd (l.map Prod.fst) t₀).ψ = rt u₁ u₂ (fm S P B e ((l.map Prod.snd).foldr LM.mul L₀)) ∧
      mulF B.ν (fm S P B e L₀) (fm S P B e ((l.map Prod.snd).foldr LM.mul L₀)) =
        fm S P B e ((l.map Prod.snd).foldr LM.mul L₀) := by
    intro l
    induction l with
    | nil =>
      intro _
      refine ⟨hL₀, ht₀, ?_⟩
      simp only [List.map_nil, List.foldr_nil]
      rw [(alg L₀ L₀ hL₀ hL₀).2.2.1]
      exact fm_of_eqv S P B e hid
    | cons x l ih =>
      intro hx
      obtain ⟨hX, hψ, hu⟩ := ih fun y hy => hx y (List.mem_cons_of_mem _ hy)
      obtain ⟨hxO, hxE, hxc⟩ := hx x List.mem_cons_self
      simp only [List.map_cons, List.foldr_cons]
      set X := (l.map Prod.snd).foldr LM.mul L₀ with hXdef
      have hOk : (x.2.mul X).Ok P := (alg x.2 X hxO hX).2.1
      have hmul : mulF B.ν (fm S P B e x.2) (fm S P B e X) = fm S P B e (x.2.mul X) := (alg x.2 X hxO hX).2.2.1
      have hunit : mulF B.ν (fm S P B e L₀) (fm S P B e (x.2.mul X)) = fm S P B e (x.2.mul X) := by
        rw [← hmul, ← (hLev E B _ _ _ (alg L₀ x.2 hL₀ hxO).1 (alg x.2 X hxO hX).1 (alg X X hX hX).1).2.2.1,
          (alg L₀ x.2 hL₀ hxO).2.2.1, fm_of_eqv S P B e hxE]
      refine ⟨hOk, ?_, hunit⟩
      rcases hxc with ⟨c, h1, h2⟩ | ⟨s, h1, h2⟩
      · have hwd : BGen.wd (x.1 :: l.map Prod.fst) t₀ = BGen.wd (l.map Prod.fst) t₀ := by
          simp [BGen.wd, h1]
        rw [hwd, hψ, ← hmul, h2, hu]
      · have hwd : BGen.wd (x.1 :: l.map Prod.fst) t₀ = s.mul (BGen.wd (l.map Prod.fst) t₀) := by
          simp [BGen.wd, h1]
        rw [hwd]
        show mulF B.ν s.ψ (BGen.wd (l.map Prod.fst) t₀).ψ = _
        rw [hψ, h2, hrt, hmul]
  exact (key l hl).2.1

end
end

namespace UpperTheory.BaseChangeIdentities.FrameWordIdentity

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.BlockFiniteConvolution

theorem wordId (hW : LocWord) (hM : LocMatch) : WordId := by
  have l1 := frameWord_length_eq_one_of_hyp hW
  have po := prodok_pf tmul_pf locOk₀ l1
  have pw := psiword_pf (psiGen_of_algebras fmAlg' rtAlg' blkLevel) (psilet_pf fmAlg' locOk₀ frfacts_pf) l1 locOk₀
    MatchAll.matchLMId frfacts_pf
  have tw := twok_pf blkWord₀
  have aw := adelWord_of_parts adelRep' finConv' pw po locOk₀ frfacts_pf tw
  have sc := archsc_pf blkWord₀ tw (archlet_pf blkOp₀ FBL.hermInf_holds)
  exact wordId_of (testword_pf pTTest₀ hM pw po usph_pf tw frfacts_pf locOk₀)
    (traceword_pf U.unitary_words_holds hM (chainsc_pf FBL.ellHom_holds) FBL.ellHom_holds aw sc usph_pf
      (uok_pf U.unitary_adjoint_holds huhecke_pf) frfacts_pf)

theorem frameBound : FrameBound :=
  frameBound_of (wordId locWord (locMatch locWord MatchAll.matchLMB2₀ MatchAll.matchLMWordS₀ MatchAll.matchLMUnit₀))

end UpperTheory.BaseChangeIdentities.FrameWordIdentity
