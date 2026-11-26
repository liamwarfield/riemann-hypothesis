module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntMulMemInvHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsAll

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory.KerT



open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
theorem hyp_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (a : I.ι) (u : B.Word) :
    Hyp I.dat (seamOf B C W V S N G) ⊤ I.J.δ I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u := by
  have hJ := (I.J.ok_iff B C W V S N G).1 h.amb_ok
  refine ⟨GlobalTheory.T.definiteBaseData_admissible B X I.Ch h.ch_ok h.fromHecke, ⟨seamOf_ok B C W V S N G, rfl, ⟨top_ne_bot, by simp⟩, hJ.1,
    ChiIdeal.isChi_chiId _ _ I.C.isChi, hJ.2⟩, fun 𝔞 _ => (ChiVal.chi_values B X I h).2 𝔞, h.sel_ok, ?_, fun _ hl => h.small_mem hl, fun _ _ => by simp,
    (h.idx_ok a).cst_ok, I.C.mu0, I.C.eta, h.ch_tied, (h.idx_ok a).muqG⟩
  rintro p ((rfl | rfl | rfl | rfl | rfl) | ⟨u, rfl⟩)
  exacts [h.two_q_d_mem.1, h.two_q_d_mem.2.1, h.two_q_d_mem.2.2, h.g_mem 0, h.g_mem 1, h.T_mem u]


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
theorem jetsAll_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn) (a : I.ι) (u : B.Word) {i : ℕ} (hi : i < B.R.m) :
    JetsAll (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B C W V S N G) (I.J.toRec B C W V S N G) I.chi I.J.cD) u i (i + 1) := by
  have hP := (hyp_of_colIn B C W V S N G I h a u).ok.primes
  rw [← AmbIn.amb_eq_ambOf]
  intro L L' hL hL'
  exact (GlobalTheory.MoveCompare.jetsIn_iff _ _ _ _ _ _ _ (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi) L L').2
    (GlobalTheory.MoveCompare.jetsAll_of_deg _ _ _ _ _ (hJ a u i hi) (GlobalTheory.MoveCompare.cBof_pos hP _ _ _ u) hL hL')

end GlobalTheory.KerT
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsRecordDat
noncomputable section

namespace GlobalTheory.LvT.Built.Inh

open NumberField IsDedekindDomain Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2
open Formalism.MainNotions.product_first_zeroth_parts (Ow)

theorem val_tauAt {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) (hX : X.AbelianUnramifiedExtensionConditions) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal) (P : Pr.vT u) (s : Bool) (hs : s = true ↔ seenC Pr u w) (x : X.E) :
    X.emb (tauAt hPr u w P) (if s then x else star x) ∈ GlobalTheory.LvT.Inh.valO w ↔ P.1.valuation X.E x ≤ 1 := by
  rw [GlobalTheory.LvT.Inh.mem_valO_of_below (X.emb (tauAt hPr u w P)) w (pullW (tauAt hPr u w P) w) (fun _ => Iff.rfl), GlobalTheory.LvT.Inh.mem_valO]
  by_cases h : s = true
  · rw [if_pos h, show pullW _ w = P.1 from seesP_tauAt hPr u hX (hs.1 h) P]
  · rw [if_neg h, show pullW _ w = conjPrime₂ P.1 from seesPbar_tauAt hPr u hX hw (mt hs.2 h) P,
      GlobalTheory.CharVal.valuation_conjP, star_star]

local instance starHost (B : Base) : StarRing B.host.E := B.fields.starE

variable (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W) (G : GJStage B C)
  (u : B.Word)

def ofOk (I : ChainIn B.fields.E B.fields.K B.fields.Tau B.R) (J : AtIn I) (Q : PerIn I)
    (Z : FmIn J (assemble B C W V S N G).what₂.places) (hI : I.Ok) (hJ : J.Ok) (hQ : Q.Ok) (hT : Q.Over J) :
    Dat (assemble B C W V S N G) u where
  E := B.fields.E
  sE := B.fields.starE
  emb := B.fields.emb
  fok := base_fOk B
  I := I
  J := J
  Q := Q
  Z := Z
  hI := hI
  hJ := hJ
  hQ := hQ
  l := (laws_all I J _ _ _ (base_fOk B) hI hJ Q hQ (assemble B C W V S N G).what₂.places).1
  lf := (laws_all I J _ _ _ (base_fOk B) hI hJ Q hQ (assemble B C W V S N G).what₂.places).2
  hT := hT

theorem sees_ofOk (X : PreX B.toPre) (I : ChainIn B.fields.E B.fields.K B.fields.Tau B.R) (J : AtIn I) (Q : PerIn I)
    (Z : FmIn J (assemble B C W V S N G).what₂.places) (hI : I.Ok) (hJ : J.Ok) (hQ : Q.Ok) (hT : Q.Over J)
    (eT : J.T = B.T u) (eS : ∀ P ∈ J.ST, P ∈ (B.primes X).vT u)
    (eZ : ∀ w (P : J.ST), Z.tauOf w P = tauAt (GlobalTheory.BasePrimes.primes_ok B X).1 u w ⟨P.1, eS P.1 P.2⟩)
    (eF : ∀ w, Z.seenP w = true ↔ seenC (B.primes X) u w) :
    (ofOk B C W V S N G u I J Q Z hI hJ hQ hT).Sees := by
  intro w hw P x
  have h1 := GlobalTheory.LvT.Inh.resChar_mem_plEq (assemble B C W V S N G) w
  rw [show (assemble B C W V S N G).what₂.places.resChar w = B.T u from hw.trans eT] at h1
  refine (GlobalTheory.LvT.Inh.mem_Ow_iff_valO (assemble B C W V S N G) w _).trans ?_
  have h2 := val_tauAt (GlobalTheory.BasePrimes.primes_ok B X).1 u (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1 h1 ⟨P.1, eS P.1 P.2⟩ _ (eF w) x
  exact (iff_of_eq (congrArg (fun τ => B.fields.emb τ (if Z.seenP w then x else star x) ∈ GlobalTheory.LvT.Inh.valO w) (eZ w P))).trans h2

end GlobalTheory.LvT.Built.Inh
end
end
