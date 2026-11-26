module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormFieldSquareClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Transport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalFormsLinkedConstructionStatesIdentified

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroIndexPlacesAdelicDataResizedEq
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
namespace GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}




variable {hX : B.fields.Ok} {Wt W₁ : Set B.places.Pl}


theorem ExtModel.sign_at_base_place_eq_embedding (z : Dat (w.st Z) w.I hX T Wt) :
    sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A = (w.st Z).toD7.what₂.embLL :=
  if_pos z.R.hv0




end GlobalTheory.Mem.R3.Rw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesTuplePlacesOverFixedCharacterPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesTuplePlacesOverFixedCharacterPrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.Places

theorem sel_eq_of_conj {X : Formalism.L2.Col.Fields} (hX : X.Ok) {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    (hs : Formalism.L2.Col.IsSel X sel) {u u' : HeightOneSpectrum (𝓞 X.F)}
    (h : letI := X.starE; ∀ c ∈ (sel u).asIdeal, ∃ c' ∈ (sel u').asIdeal, (c' : X.E) = star (c : X.E)) : sel u = sel u' := by
  have hle : u.asIdeal ≤ u'.asIdeal := fun y hy => by
    rw [← hs u] at hy
    rw [← hs u']
    obtain ⟨c', hc', e⟩ := h _ hy
    have : c' = algebraMap (𝓞 X.F) (𝓞 X.E) y := RingOfIntegers.ext (e.trans (hX.star_F (y : X.F)))
    rw [this] at hc'
    exact hc'
  rw [HeightOneSpectrum.ext (u.isMaximal.eq_of_le u'.isPrime.ne_top hle)]

theorem unrAt_mul_iff {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h' : χ'.UnrAt v) :
    (χ * χ').UnrAt v ↔ χ.UnrAt v :=
  forall₂_congr fun x hx => by
    change (χ.loc v x * χ'.loc v x = 1 ↔ χ.loc v x = 1)
    rw [h' x hx, mul_one]

def delAt {P : Pre} (f : Top.Fr P) (n : ℕ) : HChar P.host.E := if n = P.host.pde then f.del' else f.del

def OverDel {P : Pre} (Q : HeightOneSpectrum (𝓞 P.host.E)) : Prop :=
  ((P.host.pde : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal ∨ ((P.host.pde' : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal

theorem unrAt_xiTw_iff {B : Base} (T : TwDat B) (f : Top.Fr B.toPre) (v : B.places.Pl) {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hQ : OverDel (P := B.toPre) Q) : (T.xiTw f v).UnrAt Q ↔ (delAt f (B.places.resChar v)).UnrAt Q := by
  refine unrAt_mul_iff ?_
  by_contra h
  obtain ⟨-, hpr, -, hnot⟩ := (T.psi_tw v).2.2.2 Q h
  rcases hQ with hQ | hQ
  · by_cases e : Ideal.absNorm Q.asIdeal = B.host.pde
    · exact hnot (Or.inr (Or.inr (Or.inl e)))
    · exact GlobalTheory.RowEx.DatTw.not_two_primes Q.asIdeal hpr B.host.pde_prime e (Ideal.absNorm_mem _) hQ
  · by_cases e : Ideal.absNorm Q.asIdeal = B.host.pde'
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inl e))))
    · exact GlobalTheory.RowEx.DatTw.not_two_primes Q.asIdeal hpr B.host.pde'_prime e (Ideal.absNorm_mem _) hQ

theorem transport {P P' : Pre} (h : P' = P) {f : Top.Fr P} {f' : Top.Fr P'} (hf : HEq f' f)
    {sel : HeightOneSpectrum (𝓞 P.host.F) → HeightOneSpectrum (𝓞 P.host.E)}
    {sel' : HeightOneSpectrum (𝓞 P'.host.F) → HeightOneSpectrum (𝓞 P'.host.E)} (hs : HEq sel' sel) (n : ℕ)
    {Q' : HeightOneSpectrum (𝓞 P'.host.E)} (h1 : OverDel Q') (h2 : ¬ (delAt f' n).UnrAt Q') (h3 : ∃ u, sel' u = Q') :
    ∃ Q : HeightOneSpectrum (𝓞 P.host.E), HEq Q Q' ∧ OverDel Q ∧ ¬ (delAt f n).UnrAt Q ∧ ∃ u, sel u = Q := by
  subst h
  cases hf
  cases hs
  exact ⟨Q', HEq.rfl, h1, h2, h3⟩

variable {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

theorem exists_of_mem_Q (z : Dat (w.st Z) w.I hX T Wt) {t : TupU w.I (usedOf w.I T Wt)} {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hQ : Q ∈ z.R.Q t) : (∃ v ∈ Wt, ¬ (T.xiTw f v).UnrAt Q) ∧ ∃ u, w.I.sel u = Q := by
  have hr := (z.lev.is.Q_ram t Q).2 (Or.inl hQ)
  have hq : Q ∈ w.I.Q (ixOf w.I (usedOf w.I T Wt) t) := (iff_of_eq (congrArg (Q ∈ ·) (z.lev.Q t))).1 hQ
  refine ⟨?_, (w.I.exists_of_mem_Q hq).imp fun u hu => hu.2.1⟩
  rcases (mem_range_ixOf w.I).1 ⟨t, rfl⟩ with h | ⟨v, hv, h⟩
  · rw [h, w.I.twistPrimes_reference_tuple_eq_empty] at hq
    exact absurd hq (Finset.notMem_empty _)
  · refine ⟨v, hv, fun hu => hr ?_⟩
    have e : z.R.xiH t = T.xiTw f v := (z.lev.xiH t).trans (h.trans (congrArg (T.xiTw · v) w.C_eq))
    exact (iff_of_eq (congrArg (fun c : HChar B.host.E => c.UnrAt Q) e)).2 hu

theorem exists_mem_Q (z : Dat (w.st Z) w.I hX T Wt) {v : B.places.Pl} (hv : v ∈ Wt) {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hr : ¬ (T.xiTw f v).UnrAt Q) (hu : ∃ u, w.I.sel u = Q) : ∃ t, Q ∈ z.R.Q t := by
  obtain ⟨a, ha⟩ : T.xiTw f v ∈ Set.range w.I.xi := by
    rw [w.xi_range]
    exact Or.inr ⟨v, rfl⟩
  obtain ⟨t, ht⟩ := (mem_range_ixOf w.I (U := usedOf w.I T Wt) (a := a)).2
    (Or.inr ⟨v, hv, ha.trans (congrArg (T.xiTw · v) w.C_eq.symm)⟩)
  have e : z.R.xiH t = T.xiTw f v := (z.lev.xiH t).trans ((congrArg w.I.xi ht).trans ha)
  refine ⟨t, ?_⟩
  rcases (z.lev.is.Q_ram t Q).1 (fun h => hr ((iff_of_eq (congrArg (fun c : HChar B.host.E => c.UnrAt Q) e)).1 h)) with
    h | ⟨Q₁, h, hc⟩
  · exact h
  · obtain ⟨u₁, -, rfl, -⟩ := w.I.exists_of_mem_Q ((iff_of_eq (congrArg (Q₁ ∈ ·) (z.lev.Q t))).1 h)
    obtain ⟨u, rfl⟩ := hu
    exact (iff_of_eq (congrArg (· ∈ z.R.Q t) (sel_eq_of_conj hX w.ok.sel_ok hc))).1 h

theorem plCl_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), PlCl (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' i' t' Q' hQ hD
  have h1 : Q' ∈ x'.m.z.R.Q t' := hQ
  obtain ⟨⟨v', hv', hr⟩, hu⟩ := exists_of_mem_Q x'.m.z h1
  have hD' : OverDel (P := B'.toPre) Q' := by
    have h2 := (iff_of_eq (congrArg (Q' ∈ ·) ((Dof x').ntw.pD_eq i'))).1 hD
    split_ifs at h2
    · exact Or.inr h2
    · exact Or.inl h2
  obtain ⟨Q, hh, h2, h3, h4⟩ := transport l.enl.1 l.fr l.sel (B'.places.resChar v') hD'
    (fun h => hr ((unrAt_xiTw_iff T' f' v' hD').2 h)) hu
  rw [← GlobalTheory.Mem.Top.TwChar.resChar_plUnder l.enl v'] at h3
  obtain ⟨t, ht⟩ := exists_mem_Q x.m.z ((GlobalTheory.HeightCounting.Up.CopyEx.mem_Wt_iff l.enl l.ext v').2 hv')
    (fun h => h3 ((unrAt_xiTw_iff T f _ h2).1 h)) h4
  exact ⟨t, Q, ht, hh⟩

end GlobalTheory.HeightCounting.SerMove.Places

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesTuplePlacesOverFixedCharacterPrimeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedStates_tuplePlaces_over_fixedCharacterPrime : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), PlCl (sideAt x g hg a) (sideAt x' g' hg' a') := by
  exact @GlobalTheory.HeightCounting.SerMove.Places.plCl_of_link
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedConstructionStatesCharactersAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedConstructionStatesCharactersAgree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.LevExt

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove

theorem frat_delAt_heq {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'} (hP : B'.toPre = B.toPre)
    {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) (l : ℕ) :
    HEq ((Top.Fr.at a'.st f').delAt l) ((Top.Fr.at a.st f).delAt l) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).delAt l)) :))


set_option maxHeartbeats 4000000 in
theorem chars_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Chars (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hP : B'.toPre = B.toPre := l.enl.1
  have hC : x.m.z.R.toLevCh.C = Top.Fr.at (w.st x.o.Z) f := x.m.z.lev.C.trans (by rw [w.C_eq])
  have hC' : x'.m.z.R.toLevCh.C = Top.Fr.at (w'.st x'.o.Z) f' := x'.m.z.lev.C.trans (by rw [w'.C_eq])
  have hs := x.m.z.lev.is
  have hs' := x'.m.z.lev.is
  have hm : (Dof x').R.m = (Dof x).R.m := by
    exact congrArg (fun p : Pre => p.R.m) hP
  have hmu0 : ∀ (i : Fin (Dof x).R.m) (i' : Fin (Dof x').R.m), (i : ℕ) = i' →
      HEq (x'.m.z.R.toLevCh.C.mu0 i') (x.m.z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr h
  refine ⟨?_, fun j => ?_, fun j j' h => ?_, fun l0 => ?_⟩
  · have heta : HEq x'.m.z.R.toLevCh.C.eta x.m.z.R.toLevCh.C.eta := by
      rw [hC, hC']
      exact frat_eta_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP heta hs.eta hs'.eta).symm
  · let j' : Fin (Dof x').R.m := ⟨j, lt_of_lt_of_eq j.2 hm.symm⟩
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP (hmu0 j j' rfl) (hs.mu0 j) (hs'.mu0 j')).symm
  · exact (hmu0 j j' h).symm
  · show HEq (x.m.z.R.toLevCh.C.delAt l0) (x'.m.z.R.toLevCh.C.delAt l0)
    rw [hC, hC']
    exact (frat_delAt_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr l0).symm

end GlobalTheory.HeightCounting.SerMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedConstructionStatesCharactersAgreeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_construction_states_characters_agree : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Chars (sideAt x g hg a) (sideAt x' g' hg' a') := by
  first | exact @GlobalTheory.HeightCounting.SerMove.chars_of_link | exact GlobalTheory.HeightCounting.SerMove.chars_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.chars_of_link <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupsLevelsCorrespond
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupsLevelsCorrespond
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem eG_heq (B B' : Base) (h : B'.toPre = B.toPre) (px : PreX B.toPre) (px' : PreX B'.toPre) (hp : HEq px' px)
    (Pg : Finset (Formalism.L2.DIV.Pl B.host.E)) (Pg' : Finset (Formalism.L2.DIV.Pl B'.host.E)) (hPg : HEq Pg' Pg)
    (eG : Gc B px ≃* Formalism.L2.DIV.G0 Pg B.R.r) (eG' : Gc B' px' ≃* Formalism.L2.DIV.G0 Pg' B'.R.r) (he : HEq eG' eG)
    (u : Gc B px) (u' : Gc B' px') (hu : HEq u' u) : HEq (eG u) (eG' u') := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h px px' hp Pg Pg' hPg eG eG' he u u' hu ⊢
  subst h
  cases hp
  cases hPg
  cases he
  cases hu
  rfl

end GlobalTheory.HeightCounting.SerMove.GrpsPf

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem cG_heq (B B' : Base) (h : B'.toPre = B.toPre) (Pg : Finset (Formalism.L2.DIV.Pl B.host.E)) (Pg' : Finset (Formalism.L2.DIV.Pl B'.host.E))
    (hPg : HEq Pg' Pg) (Q Q' : Fin 2 → Type) (hQ : Q = Q') (pw : ∀ k, Q k → Formalism.L2.DIV.Pl B.host.E)
    (pw' : ∀ k, Q' k → Formalism.L2.DIV.Pl B'.host.E) (hpw : HEq pw pw')
    (c : Formalism.L2.DIV.G0 Pg B.R.r ≃* ∀ kv : (Σ k : Fin 2, Q k), GL (Fin B.R.r) (ZMod (B.host.g kv.1)))
    (c' : Formalism.L2.DIV.G0 Pg' B'.R.r ≃* ∀ kv : (Σ k : Fin 2, Q' k), GL (Fin B'.R.r) (ZMod (B'.host.g kv.1)))
    (hc : ∃ (plg : (Σ k : Fin 2, Q k) ≃ Pg) (iso : ∀ kv, ZMod (B.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : Pg) : Formalism.L2.DIV.Pl B.host.E) = pw kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (B.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (c y kv))
    (hc' : ∃ (plg : (Σ k : Fin 2, Q' k) ≃ Pg') (iso : ∀ kv, ZMod (B'.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : Pg') : Formalism.L2.DIV.Pl B'.host.E) = pw' kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (B'.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (c' y kv)) :
    HEq c c' := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h Pg Pg' hPg pw pw' hpw c c' hc hc' ⊢
  subst h
  cases hPg
  subst hQ
  cases hpw
  apply heq_of_eq
  obtain ⟨p, i, h1, h2⟩ := hc
  obtain ⟨p', i', h1', h2'⟩ := hc'
  obtain rfl : p = p' := Equiv.ext fun kv => Subtype.ext ((h1 kv).trans (h1' kv).symm)
  refine MulEquiv.ext fun y => funext fun kv => ?_
  have h3 := (h2 y kv).symm.trans (h2' y kv)
  refine Units.ext (Matrix.ext fun a b => (i' kv).injective ?_)
  have h4 : (i kv) ((c y kv).1 a b) = (i' kv) ((c' y kv).1 a b) := congrArg (fun m : GL _ _ => m.1 a b) h3
  have h5 : (i kv) ((c y kv).1 a b) = (i' kv) ((c y kv).1 a b) :=
    RingHom.congr_fun (Subsingleton.elim (i kv).toRingHom (i' kv).toRingHom) _
  exact h5.symm.trans h4

end GlobalTheory.HeightCounting.SerMove.GrpsPf

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem cG_read {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : TwDat X.B} {Wt : Set X.B.places.Pl}
    (z : Dat X I hX T Wt) :
    ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ z.R.Pg) (iso : ∀ kv, ZMod (X.toD7.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : z.R.Pg) : Formalism.L2.DIV.Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (z.cG y kv) := by
  obtain ⟨plg, iso, h1, -, -, h4⟩ := z.pins.keep.grp
  refine ⟨plg, iso, h1, fun y kv => ?_⟩
  obtain ⟨u, rfl⟩ := z.R.eG.surjective y
  exact h4 u kv

theorem grps_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → Grps (sideAt x g hg a) (sideAt x' g' hg' a') ι γ := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ
  refine ⟨fun u => ?_, ?_, fun u => ?_, fun u u' hu => ?_⟩
  · exact eG_heq B B' l.enl.1 w.px w'.px l.px x.m.z.R.Pg x'.m.z.R.Pg l.extN.Pg x.m.z.R.eG x'.m.z.R.eG l.extN.eG u (γ u) (hγ u)
  · exact cG_heq B B' l.enl.1 x.m.z.R.Pg x'.m.z.R.Pg l.extN.Pg (Dof x).nd.PlG (Dof x').nd.PlG (eq_of_heq l.gal.gal.PlG)
      (Dof x).naut.plGw (Dof x').naut.plGw l.gal.pl x.m.z.cG x'.m.z.cG (cG_read x.m.z) (cG_read x'.m.z)
  · exact (GlobalTheory.Mem.R3.LevBC.lev_bc B B' l.enl.1 w.px w'.px l.px w.I w'.I w.ok w'.ok ι l.cp.embLL u (γ u) (hγ u)).1.symm
  · have h : HEq (u' : (sideAt x' g' hg' a').Γ) (u : (sideAt x g hg a).Γ) := hu ▸ hγ u
    exact (GlobalTheory.Mem.R3.LevBC.lev_bc B B' l.enl.1 w.px w'.px l.px w.I w'.I w.ok w'.ok ι l.cp.embLL u.1 u'.1 h).2 u.2 u'.2

end GlobalTheory.HeightCounting.SerMove.GrpsPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupsLevelsCorrespondStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedStates_finiteGroups_levels_correspond : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → Grps (sideAt x g hg a) (sideAt x' g' hg' a') ι γ := by
  first | exact @GlobalTheory.HeightCounting.SerMove.GrpsPf.grps_of_link | exact GlobalTheory.HeightCounting.SerMove.GrpsPf.grps_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.GrpsPf.grps_of_link <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFramesLatticesModelsAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFramesLatticesModelsAgree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.SerMove.FrameValuesAtLevel
variable {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}


set_option maxHeartbeats 4000000 in
theorem ΛV_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.ΛV i) (z'.R.ΛV i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.ΛV) i).symm


set_option maxHeartbeats 4000000 in
theorem ΛW_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.ΛW i) (z'.R.ΛW i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.ΛW) i).symm


set_option maxHeartbeats 4000000 in
theorem βV_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.βV i) (z'.R.βV i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.βV) i).symm


set_option maxHeartbeats 4000000 in
theorem βW_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.βW i) (z'.R.βW i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.βW) i).symm


set_option maxHeartbeats 4000000 in
theorem sameVec_gen (q : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → Formalism.BasicNotions.TH.SPar} {S' : (w'.st Z').toD7.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (M : Formalism.IndefR.Mult.DSModel (Formalism.IndefR.Links.Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Formalism.IndefR.Links.Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (g : HEq M'.fr M.fr)
    (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v) : GlobalTheory.TwInputs.Move.SameVec v v' := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d g
  cases a; cases b; cases c; cases d; cases g
  intro τ τ' hτ
  cases hτ
  have e := eq_of_heq hv
  subst e
  rfl


set_option maxHeartbeats 4000000 in
theorem v₀_of_extN (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    GlobalTheory.TwInputs.Move.SameVec (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) (z'.geo.v₀ i' (w'.st Z').toD7.what₂.embLL) :=
  have h := hx.MW i i' hi
  sameVec_gen q i i' hi _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2.1 _ _ h.2.2.2.2.2.2.2.2.2.1

end GlobalTheory.HeightCounting.SerMove.FrameValuesAtLevel

namespace GlobalTheory.HeightCounting.SerMove


set_option maxHeartbeats 4000000 in
theorem frames_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Frames (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have q : B'.toPre = B.toPre := l.enl.1
  have hx := l.extN
  refine ⟨hx.Pg.symm, hx.ψ.symm, hx.θ.symm, fun j j' h => FrameValuesAtLevel.ΛV_at q hx j j' h, fun j j' h => FrameValuesAtLevel.ΛW_at q hx j j' h,
    fun j j' h => FrameValuesAtLevel.βV_at q hx j j' h, fun j j' h => FrameValuesAtLevel.βW_at q hx j j' h,
    fun j j' h => ((hx.BV j j' h).2.2.2.2.2).symm, fun j j' h => ((hx.BV j j' h).2.2.1).symm, fun j j' h => ?_, fun j j' h => ?_⟩
  · show GlobalTheory.TwInputs.Move.SameModel (x.m.z.R.MW j (Formalism.IndefR.Links.sg0 (Dof x) (sideAt x g hg a).A3.A)) (x'.m.z.R.MW j' (Formalism.IndefR.Links.sg0 (Dof x') (sideAt x' g' hg' a').A3.A))
    rw [GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a), GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a')]
    have m := hx.MW j j' h
    exact ⟨m.1.symm, m.2.1.symm, m.2.2.1.symm, m.2.2.2.1.symm, m.2.2.2.2.1.symm, m.2.2.2.2.2.1.symm, m.2.2.2.2.2.2.1.symm⟩
  · show GlobalTheory.TwInputs.Move.SameVec (g.v₀ j (Formalism.IndefR.Links.sg0 (Dof x) (sideAt x g hg a).A3.A)) (g'.v₀ j' (Formalism.IndefR.Links.sg0 (Dof x') (sideAt x' g' hg' a').A3.A))
    rw [GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a), GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a')]
    exact FrameValuesAtLevel.v₀_of_extN q hx j j' h

end GlobalTheory.HeightCounting.SerMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFramesLatticesModelsAgreeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedStates_frames_lattices_models_agree : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Frames (sideAt x g hg a) (sideAt x' g' hg' a') := by
  first | exact @GlobalTheory.HeightCounting.SerMove.frames_of_link | exact GlobalTheory.HeightCounting.SerMove.frames_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.frames_of_link <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCoefficientFieldFiniteGroupEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCoefficientFieldFiniteGroupEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.Ids

theorem coeffF_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H'}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l'}
    (hH : H' = H) (hl : HEq l' l) (hc : HEq c' c) : c'.F = c.F := by
  subst hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  rfl

theorem gc_equiv {B B' : Base} {px : PreX B.toPre} {px' : PreX B'.toPre} (h : Enl B B') (hp : HEq px' px) :
    ∃ γ : GlobalTheory.Mem.R3.Gc B px ≃* GlobalTheory.Mem.R3.Gc B' px', ∀ u, HEq (γ u) u := by
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  cases hp
  exact ⟨MulEquiv.refl _, fun _ => HEq.rfl⟩

theorem dat_F_eq {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (h : Enl B B') (e : ExtN z z') : z'.core.Q.c.F = z.core.Q.c.F := by
  have hH := e.H
  have hl := e.l
  have hc := e.c
  clear e
  obtain ⟨e0, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e0
  subst e0
  exact coeffF_eq (eq_of_heq hH) hl hc

theorem field_group_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∃ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) ∧ ∀ u, HEq (γ u) u := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hc := l.extN.c
  have hH := l.extN.H
  have hl := l.extN.l
  show ∃ (eK : x.m.z.core.Q.c.F ≃+* x'.m.z.core.Q.c.F) (γ : GlobalTheory.Mem.R3.Gc B w.px ≃* GlobalTheory.Mem.R3.Gc B' w'.px), _
  obtain ⟨γ, hγ⟩ := gc_equiv l.enl l.px
  have hF : x'.m.z.core.Q.c.F = x.m.z.core.Q.c.F := dat_F_eq (z := datAt x g) (z' := datAt x' g') l.enl l.extN
  exact ⟨(IntermediateField.equivOfEq hF.symm).toRingEquiv, γ, fun y => rfl, hγ⟩

end GlobalTheory.HeightCounting.SerMove.Ids
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCoefficientFieldFiniteGroupEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedStates_coefficientField_finiteGroup_eq : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∃ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) ∧ ∀ u, HEq (γ u) u := by
  first | exact @GlobalTheory.HeightCounting.SerMove.Ids.field_group_of_link | exact GlobalTheory.HeightCounting.SerMove.Ids.field_group_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.Ids.field_group_of_link <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFockPolynomialsAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFockPolynomialsAgree
set_option autoImplicit false

noncomputable section

section Lemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.SerMove.Io

theorem cx_form {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (hp : (lv (fc X.zs) b).Pos) (h2 : X.H2 cr b) (h5 : X.H5 cr b)
    (hE : X.PartsE b) (hD : X.DimParts b) (j : Bs.J) : ∃ x : A.FL j Bs.μ0, x ≠ 0 := by
  by_contra hn
  push Not at hn
  have ht : X.tC cr b j Bs.μ0 = 0 := by
    have e : (fun k => X.θ' j Bs.μ0 (X.jL j Bs.μ0 (cr.toL X.zs b j Bs.μ0 (Pi.single k 1)))) = fun _ => 0 :=
      funext fun k => by rw [hn (cr.toL X.zs b j Bs.μ0 _), map_zero, map_zero]
    unfold CxData.tC
    rw [e]
    ext k
    simp [lin]
  have hw : LinearMap.range (X.w0C b j) = ⊥ := by rw [← (h5 j Bs.μ0).2, ht, LinearMap.range_zero]
  have hE0 : X.EEl b = ⊥ := by
    rw [← hE.2, iSup_eq_bot]
    intro p
    rw [← Submodule.finrank_eq_zero, ← hD j p, hw, inf_bot_eq, finrank_bot]
  have h0 : X.iC cr b Bs.μ0 = 0 := LinearMap.range_eq_bot.1 (h2.2.2.trans hE0)
  have h1 : (fun _ => 1 : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) = 0 := h2.1 (by rw [h0]; rfl)
  exact one_ne_zero (congrFun h1 ⟨0, hp⟩)

theorem exists_form {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (hP : Pins R F cG) (hH : Holds R F) (i : Fin D.R.m) :
    ∃ x : A3.A.fam.amb.FL i A3.A.μ0, x ≠ 0 :=
  have hRw := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  cx_form (R.toCx3 F) F.cr false (hH.prim.pos false) (hRw.what₂ false).1 hRw.lifts0.1 (hH.prim.sumE false) hH.prim.dimParts i


set_option maxHeartbeats 1000000 in
theorem coefFam_roots {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, Formalism.IndefR.FWT.VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (hc : OmExt.CoefFam R c0L) (a : Fin D.R.m → D.what₂.LL) (n : Fin D.R.m → ℕ) (hn : ∀ i, n i ≠ 0) (ha : ∀ i, a i ^ n i = 1) :
    OmExt.CoefFam R fun i => D.what₂.embLL (a i) • c0L i := by
  choose u hu h1 h2 using fun i => OmExt.RootUpd.exists_unit_of_pow (a i) (n i) (hn i) (ha i)
  obtain ⟨gramR, c0R, ht⟩ := hc
  exact ⟨gramR, c0R, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, ht.ok, ht.gramR_eq, ht.mapR,
    fun j => OmExt.RootUpd.coefMapTie_smul (ht.mapL j) ((map_ne_zero _).2 (right_ne_zero_of_mul_eq_one (h2 j))),
    ht.coefR, fun j t => OmExt.RootUpd.coefTie_smul (ht.coefL j t) (a j) (u j) (hu j) (h1 j) (h2 j)⟩⟩

theorem sameModel_of_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) {σ σ' : D.what₂.LL →+* ℂ} (h : σ = σ') :
    GlobalTheory.TwInputs.Move.SameModel (R.MW i σ) (R.MW i σ') := by
  subst h
  exact .refl _

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}


set_option maxHeartbeats 4000000 in
theorem heq_io (q : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (hM : GlobalTheory.TwInputs.Move.SameModel M M') {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W]
    [nW' : NormedAddCommGroup W'] [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hiW : HEq iW' iW)
    (io : LowT M →ₗ[ℂ] W →ₗ[ℂ] PolF (w.st Z).toD7 (Wc (w.st Z).toD7 i).rank (Vc (w.st Z).toD7 i).rank)
    (io' : LowT M' →ₗ[ℂ] W' →ₗ[ℂ] PolF (w'.st Z').toD7 (Wc (w'.st Z').toD7 i').rank (Vc (w'.st Z').toD7 i').rank)
    (hio : HEq io' io) (u : ∀ τ, lowT M τ) (u' : ∀ τ, lowT M' τ)
    (hu : GlobalTheory.TwInputs.Move.SameVec (M := M) (M' := M') (fun τ => u τ) (fun τ => u' τ)) (y : W) (y' : W') (hy : HEq y' y) :
    HEq (io (PiTensorProduct.tprod ℂ u) y) (io' (PiTensorProduct.tprod ℂ u') y') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  subst hW
  cases hn
  cases hiW
  cases hy
  obtain ⟨a, b, c, d, l, e, g⟩ := hM
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e1 : u = u' := funext fun τ => Subtype.ext (Subtype.ext (eq_of_heq (hu τ τ HEq.rfl)))
  have e2 : io' = io := eq_of_heq hio
  subst e1
  subst e2
  exact HEq.rfl


set_option maxHeartbeats 4000000 in
theorem heq_pol (q : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    (ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hι : ∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y)
    (F : Formalism.L2.DIV.Pol (w.st Z).toD7.what₂.LL (w.st Z).toD7.what₂.Tau (Vc (w.st Z).toD7 i).rank)
    (F' : Formalism.L2.DIV.Pol (w'.st Z').toD7.what₂.LL (w'.st Z').toD7.what₂.Tau (Vc (w'.st Z').toD7 i').rank)
    (hF : HEq (MvPolynomial.map ι F) F') :
    HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL F') (MvPolynomial.map (w.st Z).toD7.what₂.embLL F) := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  have e1 : MvPolynomial.map ι F = F' := eq_of_heq hF
  subst e1
  exact heq_of_eq ((MvPolynomial.map_map _ _ _).trans (congrArg (fun s => MvPolynomial.map s F) (RingHom.ext hι)))

section Lift
open OmExt LiftUnit Formalism.DivisionValues _root_.Formalism.L2.Col


set_option maxHeartbeats 4000000 in
theorem coef_schur (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hN : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hii : (i : ℕ) = i')
    (c0L) (hc : OmExt.CoefFam z.R.toRealDat c0L) (c0L'') (hc'' : OmExt.CoefFam z'.R.toRealDat c0L'') :
    ∃ μ : ℂ, ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L'' i' v') (μ • c0L i v) := by
  obtain ⟨gR, c0R, ht⟩ := hc
  obtain ⟨gR', c0R', ht'⟩ := hc''
  obtain ⟨hW, hρ, -⟩ := hN.BV i i' hii
  obtain ⟨hnW, hiW⟩ := hN.cV i i' hii
  have hcI := z.pins.char.base.models.cV i
  have hmapL := ht.mapL i
  have hmapL' := ht'.mapL i'
  have htau := ht.tauL_ok
  have htau' := ht'.tauL_ok
  clear hN
  obtain ⟨hpre, -, -, hR⟩ := hE
  cases B with | mk P => cases B' with | mk P' =>
  dsimp only at hpre
  subst hpre
  obtain rfl : i = i' := Fin.ext hii
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL := (by with_unfolding_all exact ((enlEmb hR) :))
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := (by with_unfolding_all exact ((enlEmb_spec hR) :))
  let c'' : CoefA (Vc (w.st Z).toD7 i) :=
    { W := (z'.R.cV i).W, nW := (z'.R.cV i).nW, iW := (z'.R.cV i).iW, fW := (z'.R.cV i).fW, ρ := (z'.R.cV i).ρ }
  have hcc : c'' = z.R.cV i := coefA_eq _ _ hW hρ hnW hiW
  obtain ⟨μ, hμ⟩ := exists_smul_eq_enl (z.R.cV i) hcI ι (w'.st Z').toD7.what₂.embLL hι (labLL (w.st Z).toD7)
    (labLL (w'.st Z').toD7) (fun τ => (htau' τ).trans (htau τ).symm) (c0L i) hmapL c'' hcc (c0L'' i) hmapL'.1
  exact ⟨μ, fun v v' hv => hμ v v' (eq_of_heq hv)⟩


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem agree_root (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (hstd : z.Std) (hB : z'.Std) (hN : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hii : (i : ℕ) = i')
    (c0L) (hc : OmExt.CoefFam z.R.toRealDat c0L) (c0L'') (hc'' : OmExt.CoefFam z'.R.toRealDat c0L'')
    (x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (hx : x ≠ 0) :
    ∃ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL)
      (u : (w.st Z).toD7.what₂.LL) (u' : (w'.st Z').toD7.what₂.LL) (n n' : ℕ), n ≠ 0 ∧ u ^ n = 1 ∧ n' ≠ 0 ∧ u' ^ n' = 1 ∧
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) ∧ c0L i v ≠ 0 ∧
      HEq ((w'.st Z').toD7.what₂.embLL u' • c0L'' i' v') ((w.st Z).toD7.what₂.embLL u • c0L i v) := by
  obtain ⟨φ, rfl⟩ := ((mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1
    ((i : ℕ) + 1)).res (mtKOk _ _ _ _ hX _)).surjective x
  have hφ : φ ≠ 0 := fun h0 => hx (h0 ▸ map_zero _)
  obtain ⟨h, hh⟩ : ∃ h, z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))
      ((mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1
        ((i : ℕ) + 1)).res (mtKOk _ _ _ _ hX _) φ) h ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (GlobalTheory.PresBasic.extL_injective (z.R.B.L i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))).pres
      ((funext hn).trans (map_zero _).symm))
  obtain ⟨φ', hφφ⟩ := exists_form_enl w w' Wt Wt' hE hf hpx ((i : ℕ) + 1) ((i' : ℕ) + 1) (by rw [hii]) φ
  have hj := hN.jL i i' hii (mtKOk _ _ _ _ hX _) (mtKOk _ _ _ _ hX' _) φ φ' hφφ
  have hW := (hN.BV i i' hii).1
  obtain ⟨u, n, hn, hu, H⟩ := exists_root_reading (w.st Z) w.I hX _ z.Xg z.tr z.R.toRealDat w.ok z.lev i
    (z.pins.char.base.models.cV i) c0L hc (hstd.2 i) _ φ hφ
  obtain ⟨y, hy⟩ := RowCoord.exists_matEq (D := (w.st Z).toD7) (Vc (w.st Z).toD7 i) (LiftBrg.rkEq (w.st Z) i).symm
    (gram_eq_one (w.st Z) w.I w.ok i) h
  obtain ⟨v, hv1, hv2⟩ := H φ h y hy
  have H' := exists_root_reading (w'.st Z') w'.I hX' _ z'.Xg z'.tr z'.R.toRealDat w'.ok z'.lev i'
    (z'.pins.char.base.models.cV i') c0L'' hc'' (hB.2 i') _ φ'
  have hS := rowLevelPrimes_colTuples_eq_vGs w Wt
  have hS' := rowLevelPrimes_colTuples_eq_vGs w' Wt'
  clear H hN hB hstd hc hc''
  obtain ⟨hpre, -, -, -⟩ := hE
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  obtain rfl : i' = i := Fin.ext hii.symm
  have ep : w'.px = w.px := eq_of_heq hpx
  have hvG : ((baseOfColW w').primes w'.px).vGs = ((baseOfColW w).primes w.px).vGs := by
    rw [ep]
    rfl
  have hjh := heq_apply (eq_of_heq hW) hj h
  have hSS := hS'.trans (hvG.trans hS.symm)
  have hd := hφφ _ _ (heq_decoOf (X := (baseOfColW w).fields) hSS y.1)
  have h0 : c0L i' v ≠ 0 := fun e => hh (hv2.trans ((congrArg _ e).trans (smul_zero (A := (z.R.cV i').W) _)))
  have hφ' : φ' ≠ 0 := fun e => hφ (Subtype.ext (funext fun d => Subtype.ext (by
    have e1 := eq_of_heq (hφφ d (cast (congrArg (DecoSet (baseOfColW w).fields.E (baseOfColW w).R.nV ∅) hSS.symm) d) (cast_heq _ _))
    rw [e] at e1
    exact MvPolynomial.map_injective _ (baseOfColW w).embLL.injective (e1.symm.trans ((map_zero _).trans (map_zero _).symm)))))
  obtain ⟨u', n', hn', hu', H⟩ := H' hφ'
  obtain ⟨v', hv1', hv2'⟩ := H φ' h y hy
  exact ⟨v, v', u, u', n, n', hn, hu, hn', hu', hv1'.trans (hd.trans hv1.symm), h0,
    (heq_of_eq hv2'.symm).trans (hjh.trans (heq_of_eq hv2))⟩


set_option maxHeartbeats 4000000 in
theorem one_lift (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (hstd : z.Std) (hB : z'.Std) (hN : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hii : (i : ℕ) = i')
    (c0L) (hc : OmExt.CoefFam z.R.toRealDat c0L) (c0L'') (hc'' : OmExt.CoefFam z'.R.toRealDat c0L'')
    (x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (hx : x ≠ 0) :
    ∃ (a : (w'.st Z').toD7.what₂.LL) (n : ℕ), n ≠ 0 ∧ a ^ n = 1 ∧
      ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
        HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) →
          HEq ((w'.st Z').toD7.what₂.embLL a • c0L'' i' v') (c0L i v) := by
  obtain ⟨μ, hμ⟩ := coef_schur z z' hE hN i i' hii c0L hc c0L'' hc''
  obtain ⟨v, v', u, u', n, n', hn, hun, hn', hun', hvv, hv0, hrel⟩ :=
    agree_root z z' hE hf hpx hstd hB hN i i' hii c0L hc c0L'' hc'' x hx
  have hW := (hN.BV i i' hii).1
  obtain ⟨hnW, hiW⟩ := hN.cV i i' hii
  have key := OmCoef.smul_eq_of_heq (eq_of_heq hW) hnW hiW (hμ v v' hvv) hrel
  have hμe : (w'.st Z').toD7.what₂.embLL u' * μ = (w.st Z).toD7.what₂.embLL u := smul_left_injective ℂ hv0 key
  have hu0 : (w.st Z).toD7.what₂.embLL u ≠ 0 := (map_ne_zero _).2 fun h => by
    rw [h, zero_pow hn] at hun
    exact zero_ne_one hun
  obtain ⟨b, hb⟩ : (w.st Z).toD7.what₂.embLL u ∈ Set.range (w'.st Z').toD7.what₂.embLL := hE.2.2.2 ⟨u, rfl⟩
  have hb1 : b ^ n = 1 := (w'.st Z').toD7.what₂.embLL.injective (by rw [map_pow, hb, ← map_pow, hun, map_one, map_one])
  have ha : (u' * b⁻¹) ^ (n * n') = 1 := by
    have e1 : u' ^ (n * n') = 1 := by rw [mul_comm, pow_mul, hun', one_pow]
    have e2 : b ^ (n * n') = 1 := by rw [pow_mul, hb1, one_pow]
    rw [mul_pow, inv_pow, e1, e2, inv_one, mul_one]
  refine ⟨u' * b⁻¹, n * n', mul_ne_zero hn hn', ha, fun v1 v1' h => ?_⟩
  refine (OmCoef.heq_smul (eq_of_heq hW) hnW hiW (hμ v1 v1' h) _).trans (heq_of_eq ?_)
  have e1 : (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = 1 := by
    calc (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = ((w'.st Z').toD7.what₂.embLL u' * μ) * ((w.st Z).toD7.what₂.embLL u)⁻¹ := by
          rw [map_mul, map_inv₀, hb]; ring
      _ = 1 := by rw [hμe, mul_inv_cancel₀ hu0]
  rw [e1, one_smul]

end Lift


set_option maxHeartbeats 2000000 in
theorem exists_roots (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (hstd : z.Std) (hB : z'.Std) (hN : ExtN z z') (hH : Holds z.R z.F)
    (c0L) (hc : OmExt.CoefFam z.R.toRealDat c0L) (c0L'') (hc'' : OmExt.CoefFam z'.R.toRealDat c0L'') (i' : Fin (w'.st Z').toD7.R.m) :
    ∃ (a : (w'.st Z').toD7.what₂.LL) (n : ℕ), n ≠ 0 ∧ a ^ n = 1 ∧
      ∀ i : Fin (w.st Z).toD7.R.m, (i : ℕ) = i' → ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
        HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) →
          HEq ((w'.st Z').toD7.what₂.embLL a • c0L'' i' v') (c0L i v) := by
  by_cases h : ∃ i : Fin (w.st Z).toD7.R.m, (i : ℕ) = i'
  · refine h.elim fun i hi => (exists_form z.pins hH i).elim fun x hx => ?_
    refine (one_lift z z' hE hf hpx hstd hB hN i i' hi c0L hc c0L'' hc'' x hx).imp fun a h1 => h1.imp fun n h2 =>
      ⟨h2.1, h2.2.1, fun j hj => ?_⟩
    have e : j = i := Fin.ext (hj.trans hi.symm)
    subst e
    exact h2.2.2
  · exact ⟨1, 1, one_ne_zero, one_pow _, fun i hi => absurd ⟨i, hi⟩ h⟩


set_option maxHeartbeats 2000000 in
theorem sameModel_extN (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hN : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    GlobalTheory.TwInputs.Move.SameModel (z.R.MW i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) (z'.R.MW i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') z'.Xg z'.tr).A)) := by
  have s := sameModel_of_eq z.R.toRealDat i (ExtModel.sign_at_base_place_eq_embedding z)
  have s' := sameModel_of_eq z'.R.toRealDat i' (ExtModel.sign_at_base_place_eq_embedding z')
  have m := hN.MW i i' hi
  exact ⟨s.H.trans (m.1.symm.trans s'.H.symm), s.nacg.trans (m.2.1.symm.trans s'.nacg.symm), s.ips.trans (m.2.2.1.symm.trans s'.ips.symm),
    s.σ.trans (m.2.2.2.1.symm.trans s'.σ.symm), s.lam.trans (m.2.2.2.2.1.symm.trans s'.lam.symm),
    s.ε.trans (m.2.2.2.2.2.1.symm.trans s'.ε.symm), s.fr.trans (m.2.2.2.2.2.2.1.symm.trans s'.fr.symm)⟩


set_option maxHeartbeats 2000000 in
theorem io_at (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hN : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    (u : ∀ τ, lowT (z.R.MW i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) τ) (u' : ∀ τ, lowT (z'.R.MW i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') z'.Xg z'.tr).A)) τ)
    (hu : GlobalTheory.TwInputs.Move.SameVec (M := z.R.MW i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) (M' := z'.R.MW i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') z'.Xg z'.tr).A)) (fun τ => u τ) (fun τ => u' τ))
    (y : (z.R.cV i).W) (y' : (z'.R.cV i').W) (hy : HEq y' y) :
    HEq (z.R.ioP i (PiTensorProduct.tprod ℂ u) y) (z'.R.ioP i' (PiTensorProduct.tprod ℂ u') y') := by
  have hM := sameModel_extN z z' hN i i' hi
  have h1 := hN.BV i i' hi
  have h2 := hN.cV i i' hi
  have k := @heq_io B B' f f' T T' w w' Z Z' hE.1 i i' hi _ _ _ _ hM (z.R.cV i).W (z'.R.cV i').W (z.R.cV i).nW (z.R.cV i).iW
    (z'.R.cV i').nW (z'.R.cV i').iW (eq_of_heq h1.1) h2.1 h2.2 ((by with_unfolding_all exact ((z.R.ioP i) :))) ((by with_unfolding_all exact ((z'.R.ioP i') :))) ((by with_unfolding_all exact (h1.2.2.2.1 :))) u u' ((by with_unfolding_all exact (hu :))) y y' hy
  exact (by with_unfolding_all exact (k :))


set_option maxHeartbeats 4000000 in
theorem io_of_extN (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (hstd : z.Std) (hB : z'.Std) (hN : ExtN z z') (hH : Holds z.R z.F)
    (ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hι : ∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) :
    ∃ c0L c0L', OmExt.CoefFam z.R.toRealDat c0L ∧ OmExt.CoefFam z'.R.toRealDat c0L' ∧
      ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
        ∀ (u : ∀ τ, lowT (z.R.MW i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) τ)
          (u' : ∀ τ, lowT (z'.R.MW i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') z'.Xg z'.tr).A)) τ),
          GlobalTheory.TwInputs.Move.SameVec (M := z.R.MW i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A))
            (M' := z'.R.MW i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') z'.Xg z'.tr).A)) (fun τ => u τ) (fun τ => u' τ) →
        ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
          HEq (MvPolynomial.map ι v.1) v'.1 →
          HEq (z.R.ioP i (PiTensorProduct.tprod ℂ u) (c0L i v)) (z'.R.ioP i' (PiTensorProduct.tprod ℂ u') (c0L' i' v')) := by
  refine z.pins.char.base.fam.tie.elim fun g₁ h => h.elim fun c₁ h => h.elim fun c0L hT => ?_
  refine z'.pins.char.base.fam.tie.elim fun g₂ h => h.elim fun c₂ h => h.elim fun c0L'' hT'' => ?_
  have hc : OmExt.CoefFam z.R.toRealDat c0L := ⟨g₁, c₁, hT⟩
  have hc'' : OmExt.CoefFam z'.R.toRealDat c0L'' := ⟨g₂, c₂, hT''⟩
  have key := exists_roots z z' hE hf hpx hstd hB hN hH c0L hc c0L'' hc''
  choose a n hn ha H using key
  refine ⟨c0L, fun i => (w'.st Z').toD7.what₂.embLL (a i) • c0L'' i, hc, coefFam_roots z'.R.toRealDat c0L'' hc'' a n hn ha,
    fun i i' hi u u' hu v v' hv => ?_⟩
  have hy := H i' i hi v v' (heq_pol (w := w) (w' := w') (Z := Z) (Z' := Z') hE.1 i i' hi ι hι v.1 v'.1 hv)
  exact (by with_unfolding_all exact ((io_at z z' hE hN i i' hi u u' hu (c0L i v) ((w'.st Z').toD7.what₂.embLL (a i') • c0L'' i' v') hy) :))

end GlobalTheory.HeightCounting.SerMove.Io

end Lemmas

section Main

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr

theorem GlobalTheory.HeightCounting.SerMove.ioCl_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), IoCl (sideAt x g hg a) (sideAt x' g' hg' a') ι := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  exact (by with_unfolding_all exact (Io.io_of_extN (datAt x g) (datAt x' g') (isBaseEnlargementFixedCoefField_of_coeffEnlargement l.enl) l.fr l.px (StateChecks.St.std x) (StateChecks.St.std x') l.extN
    x.m.intersectionNumber_baseChange ι l.cp.embLL :))

end Main

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFockPolynomialsAgreeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedStates_fockPolynomials_agree : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), IoCl (sideAt x g hg a) (sideAt x' g' hg' a') ι := by
  first | exact @GlobalTheory.HeightCounting.SerMove.ioCl_of_link | exact GlobalTheory.HeightCounting.SerMove.ioCl_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.ioCl_of_link <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove

theorem realMove_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Nonempty (GlobalTheory.TwInputs.Move.RealMove (sideAt x g hg a) (sideAt x' g' hg' a') ι) :=
  fun x x' ι e g g' l hg hg' a a' =>
    let ⟨eK, γ, h1, h2⟩ := GlobalTheory.T.linkedStates_coefficientField_finiteGroup_eq x x' ι e g g' l hg hg' a a'
    realMove_of_parts (GlobalTheory.T.linkedStates_frames_lattices_models_agree x x' ι e g g' l hg hg' a a') (GlobalTheory.T.linked_construction_states_characters_agree x x' ι e g g' l hg hg' a a')
      (GlobalTheory.T.linkedStates_finiteGroups_levels_correspond x x' ι e g g' l hg hg' a a' γ h2) (GlobalTheory.T.linkedStates_tuplePlaces_over_fixedCharacterPrime x x' ι e g g' l hg hg' a a')
      (GlobalTheory.T.linkedStates_fockPolynomials_agree x x' ι e g g' l hg hg' a a') (GlobalTheory.T.rationalForms_linkedConstructionStates_identified x x' ι e g g' l hg hg' a a' eK γ h1 h2)

end GlobalTheory.HeightCounting.SerMove
