module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
noncomputable section

namespace GlobalTheory.Mem.Top.GroupRetwisting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

abbrev BaseP : Type 1 := ∀ B : Base, Fr B.toPre → Prop

structure BaseCond (KP : BaseP) : Prop where
  ex : EvG fun K => ∃ (P : Pre) (f₀ : Fr P), K.Over P ∧ ∀ (S₁ : IntermediateField ℚ ℂ → Finset ℂ)
    (S₂ : IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℂ), (∀ F, ∀ z ∈ S₁ F, IsAlgebraic ℚ z) →
    (∀ F F₀, ∀ z ∈ S₂ F F₀, IsAlgebraic ℚ z) →
    ∃ (B : Base) (f : Fr B.toPre), B.toPre = P ∧ HEq f f₀ ∧ KP B f ∧ Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex)
  enl : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre), Enl B B' → HEq f' f → KP B f → KP B' f'

def RetwistG (Q Q' : V4.Slot) : Prop :=
  EvG fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c → ExportAt X.toD7 c.O.nch c.O.xd →
    ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ B : Pre, Fr B → Set (HChar B.host.E) → Finset ℂ), (∀ B f Ξ, ∀ z ∈ S₂ B f Ξ, IsAlgebraic ℚ z) →
      ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl X.B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
        (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧
        ∀ (C : Cols B') (W : RowsRest B' C) (V : DivStage B' C W) (S : SStage B' C W) (N : NStage B' C W) (G : GJStage B' C)
          (c' : V4.Core K ⟨B', C, W, V, S, N, G⟩ f' T'), Q K ⟨B', C, W, V, S, N, G⟩ f' T' c' →
          DQ.TwAllAt (assemble B' C W V S N G) c'.O.nch c'.O.xd ∧ Q' K ⟨B', C, W, V, S, N, G⟩ f' T' c'

def FromCoreAt (Q : V4.Slot) (K : Ctx) (D : D7) (Y : Lay D) : Prop :=
  ∃ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c ∧
    (⟨D, layObj Y⟩ : Σ D : D7, Obj2 D) = ⟨X.toD7, c.O⟩

def Forced (K : Ctx) (B : Base) (T : TwDat B) : Prop :=
  ∀ p : ℕ, p.Prime → ((∃ i, p = B.host.g i) ∨ p = B.host.d ∨ (p : ℝ) ≤ K.s.X'' B.R.n) → p ∈ T.pl

abbrev AtP : Type 1 := ∀ (_ : Ctx) (B : Base), Fr B.toPre → TwDat B → Prop

def Step (KP : BaseP) (p q : AtP) : Prop := EvLgG fun K B f T => KP B f → Forced K B T → p K B f T → q K B f T

def HasCore (Q : V4.Slot) : AtP := fun K B f T =>
  ∃ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c

def FirstG (KP : BaseP) (Q : V4.Slot) : Prop := Step KP (fun _ B _ T => T = TwDat.untw B T.pl) (HasCore Q)

def ExportF (KP : BaseP) (Q : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → T = TwDat.untw B T.pl → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    ExportAt (assemble B C W V S N G) c.O.nch c.O.xd

def Pass (KP : BaseP) (Q : V4.Slot) (r : AtP) : Prop :=
  EvLgG fun K B f T => KP B f → T = TwDat.untw B T.pl → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    ExportAt (assemble B C W V S N G) c.O.nch c.O.xd →
    ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ), (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) →
      ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
        (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ r K B' f' T'

def SecondG (KP : BaseP) (Q Q' : V4.Slot) : Prop :=
  Pass KP Q (HasCore fun K X f T c => Q K X f T c ∧ DQ.TwAllAt X.toD7 c.O.nch c.O.xd ∧ Q' K X f T c)

def LargeBaseConditionG (KP : BaseP) (Q R : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

theorem evG_all {p : Ctx → Prop} (h : ∀ K, p K) : EvG p := evG_good.imp fun K _ _ _ _ _ => h K

theorem baseCond_of {KP : BaseP} (h : V4.KsCond KP) {PP : ∀ P : Pre, Fr P → Prop}
    (hP : EvG fun K => ∃ (P : Pre) (f : Fr P), K.Over P ∧ PP P f) : BaseCond fun B f => KP B f ∧ PP B.toPre f := by
  refine ⟨((evG_of_ev h.ex).inter hP).imp ?_, fun B B' f f' e hf hk => ⟨h.enl B B' f f' e hf hk.1, ?_⟩⟩
  · rintro K _ _ _ _ ⟨hk, P, f₀, hO, hp⟩
    obtain ⟨B₀, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
    refine ⟨_, f₀, hO, fun S₁ S₂ a₁ a₂ => ?_⟩
    obtain ⟨B, f, e, hf, k, H⟩ := hk B₀ f₀ S₁ S₂ hO a₁ a₂
    refine ⟨B, f, e, hf, ⟨k, ?_⟩, H⟩
    generalize B₀.toPre = P₀ at *
    subst e
    cases hf
    exact hp
  · have e1 := e.1
    have h2 := hk.2
    clear hk e
    generalize B.toPre = P at *
    generalize B'.toPre = P' at *
    subst e1
    cases hf
    exact h2

theorem lg_forced (K : Ctx) : large₂ K fun B _ T => Forced K B T := by
  have h : ∀ P : Pre, ∃ S : Finset ℕ,
      ∀ p : ℕ, p.Prime → ((∃ i, p = P.host.g i) ∨ p = P.host.d ∨ (p : ℝ) ≤ K.s.X'' P.R.n) → p ∈ S := fun P => by
    refine ⟨{P.host.g 0, P.host.g 1, P.host.d} ∪ Finset.range (⌊K.s.X'' P.R.n⌋₊ + 1), ?_⟩
    rintro p - (⟨i, rfl⟩ | rfl | h)
    · fin_cases i <;> simp
    · simp
    · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h)))
  choose S hS using h
  exact ⟨fun _ _ _ => ∅, fun P _ _ _ => S P, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B _ _ _ _ h _ p hp h' => h (hS _ p hp h')⟩

theorem lg_all (K : Ctx) {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, K.Over B.toPre → p B f T) : large₂ K p :=
  (lg_forced K).imp fun B f T hO _ => h B f T hO

section Steps
variable {KP : BaseP} {p q r : AtP}

theorem Step.of_evG (h : EvG fun K => ∀ B f T, K.Over B.toPre → KP B f → Forced K B T → p K B f T → q K B f T) : Step KP p q :=
  EvG.imp h fun K _ _ _ _ H => lg_all K H

theorem Step.of_all (h : ∀ K B f T, K.Over B.toPre → KP B f → Forced K B T → p K B f T → q K B f T) : Step KP p q :=
  Step.of_evG (evG_all h)

theorem Step.trans (h : Step KP p q) (h' : Step KP q r) : Step KP p r :=
  (EvG.inter h h').imp fun _ _ _ _ _ H => (H.1.inter H.2).imp fun _ _ _ _ G a b c => G.2 a b (G.1 a b c)

theorem Step.and (h : Step KP p q) (h' : Step KP p r) : Step KP p fun K B f T => q K B f T ∧ r K B f T :=
  (EvG.inter h h').imp fun _ _ _ _ _ H => (H.1.inter H.2).imp fun _ _ _ _ G a b c => ⟨G.1 a b c, G.2 a b c⟩

theorem Step.of_evLgG (h : EvLgG q) : Step KP p q := EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G _ _ _ => G

end Steps

section Tests
variable (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM)
include hH hLP h2b

end Tests

end GlobalTheory.Mem.Top.GroupRetwisting

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TilX Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopPtModel

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_mul {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (a b : GL (Fin N) (AfE F E)) :
    ((a * b : GL (Fin N) (AfE F E)).1).map (adAt F P) = a.1.map (adAt F P) * b.1.map (adAt F P) := by
  rw [Units.val_mul, Matrix.map_mul]

theorem adAt_of_prV {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) {k : GL (Fin N) (AfE F E)}
    (h1 : bc (prV (E := E) (P.under (𝓞 F))) k = 1) : k.1.map (adAt F P) = 1 := by
  refine Matrix.ext fun i j => ?_
  have h2 : prV (E := E) (P.under (𝓞 F)) (k.1 i j - (1 : Matrix (Fin N) (Fin N) (AfE F E)) i j) = 0 := by
    have h3 := congrArg (fun g : GL (Fin N) _ => g.1 i j) h1
    simp only [Units.val_one] at h3
    have h4 : prV (E := E) (P.under (𝓞 F)) (k.1 i j) = (1 : Matrix (Fin N) (Fin N) _) i j := h3
    rw [map_sub, h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 := adAt_eq_zero_of_prV P _ h2
  rw [map_sub, sub_eq_zero] at h3
  refine h3.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

theorem topPt_base {u : B.Word} {a : I.ι} {k : GA B (B.R.N B.R.m)} [NeZero (B.R.N B.R.m - 1)] (h : I.TopPt l Z u a k) :
    PtOf k (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u (DecoF.base _ _ _ _ _)) := by
  have := h (DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _) ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rwa [one_mul] at this

end GlobalTheory.Mem.Col2.TopPtModel

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.TrueColsTest

attribute [local instance] GlobalTheory.Mem.Col2.starE

section Normal

variable {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)

end Normal

variable {B : Base} {X : PreX B.toPre} {I : TC B X}


section Gen
variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem mt_finite {R : Ranks} {J : ChainIn E K ι R} (Q : PerIn J) (h : Q.Ok) (hH : ∀ b, Q.H b = ⊤) :
    FiniteDimensional ℂ (Q.Mt emb σ) := by
  letI := Q.clFin h
  haveI : FiniteDimensional ℂ (VV ℂ Q.sgT) := Module.Finite.of_basis (bVV ℂ Q.sgT)
  let r : Q.Mt emb σ →ₗ[ℂ] (Q.S'.Cl → VV ℂ Q.sgT) :=
    { toFun := fun F c => ⟨F.1 c.1 (Q.S'.rep c), (F.2 c.1 _).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective r ((injective_iff_map_eq_zero r).2 fun F hF => ?_)
  apply Subtype.ext
  funext b d
  have h0 : F.1 b (Q.S'.rep (Q.S'.cl b d)) = 0 := congrArg Subtype.val (congrFun hF (Q.S'.cl b d))
  have h1 := (F.2 b (Q.S'.rep (Q.S'.cl b d))).2 (Q.S'.mv b d) (by rw [hH]; trivial)
  rw [h0, map_zero, smul_zero] at h1
  exact (congrArg (F.1 b) (Q.S'.mv_smul b d)).symm.trans h1
end Gen


theorem ipC_herm (l : I.Laws) (u : B.Word) (x y) :
    starRingEnd ℂ (((I.cols l).fm u).ipC 0 y x) = ((I.cols l).fm u).ipC 0 x y := by
  unfold MemberForms.ipC
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul]
  congr 1
  · simp [ColumnChain.wt]
  · exact (ClassSumPos.ipVal_herm _ _ _ _ _).symm

theorem ipC_pos (l : I.Laws) (u : B.Word) (x) (hx : x ∈ ((I.cols l).mem u).A.Mu0) (h0 : x ≠ 0) :
    0 < (((I.cols l).fm u).ipC 0 x x).re := by
  letI := (I.chIn u I.mu0).clFin (l.ch u _) 0
  exact (ClassSumPos.classSum_pos_herm (I.stp u I.mu0 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (base_fOk B) ((l.ch u _).step 0)).1 x hx h0

theorem fits (l : I.Laws) : RowsRestModel.Fits (I.cols l)
    fun a => Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL) := by
  have key : ∀ u a, Nonempty (((I.cols l).PTw u a).Mt ≃ₗ[ℂ]
      RowsRestModel.Eu (Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL))) := fun u a => by
    haveI := mt_finite B.fields.emb B.embLL (I.perIn B.u₀ a) (l.per _ a) fun _ => rfl
    have key : Nonempty ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL ≃ₗ[ℂ]
        RowsRestModel.Eu (Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL))) :=
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq finrank_euclideanSpace_fin.symm
    exact key
  refine ⟨fun u => key u I.mu0, key, fun u x y => ipC_herm l u _ _, fun u x => ?_, fun u x hx => ?_⟩
  · by_cases h0 : x.1 = 0
    · simp [h0, MemberForms.ipC]
    · exact (ipC_pos l u x.1 x.2.1 h0).le
  · by_contra h0
    have := ipC_pos l u x.1 x.2.1 fun e => h0 (Subtype.ext e)
    rw [hx] at this
    simp at this

theorem later (l : I.Laws) (hB : StagesInhab.HasLetters B.toPre) : Nonempty (TC.Later B (I.cols l)) := by
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  let W := RowsRestModel.model (fits l) 1 1 1
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => ipC_herm l u x y) (fun u x hx h => ipC_pos l u x hx h) (show 1 ≤ 2 * 1 by omega)
  obtain ⟨G⟩ := GJInhab.nonempty_stage B (I.cols l)
  exact ⟨⟨GaloisStage.adapt W, V, S, N, G⟩⟩

theorem kStd_spec (X : PreX B.toPre) (u : B.Word) (n : ℕ) :
    (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (kStd X u n) p ∧ p.deco.1.N = stdLat B.fields.E n) ∧
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) (kStd X u n) = 1) ∧
    ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 (((kStd X u n)⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) :=
  Classical.epsilon_spec (BasePoint.exists_kStd X (base_fields_primes_ok B X).2.1 u n)

end GlobalTheory.Mem.Col2.TrueColsTest

end
end
