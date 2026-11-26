module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.FacWithCsNonneg
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants Formalism.HN
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open Formalism.L2.Pj hiding kap
open GlobalTheory.CompHt hiding rhoB

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P) {T : Par D} {j : ℕ} {l : Level T.H}
  {Xo : Moduli (T.Dw j) l} {c : Coeff l} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
  (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r)

abbrev gKap (T : Par D) (j : ℕ) : WTZ D.host.E := thetaExp D (T.Dw j) (kap D j)

abbrev gKapMinus (T : Par D) (j : ℕ) : WTZ D.host.E := thetaExp D (T.Dw j) (kapMinus D j)

abbrev gTw (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (twW D j)

abbrev gMinus (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uMinus D j)

abbrev gOne (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uOne Q j)

abbrev gTop (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uTop Q j)

abbrev nrmAt (G : WTZ D.host.E) : (c.F →+* ℂ) → cuspW Xo c U G → ℝ := normW U (xiR D) (fun _ => D.sp.W j) dict G

def refConst : ℝ := 1 / 2500

def ccOf : ℝ := (refSum U refConst (gOne Q T j)).toReal + aSum Q j + cInf Q j

theorem comp_nonempty (h : T.Pins) (hj : InR D j) : Nonempty (Comp Xo c) :=
  (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo c (by
    rw [(sig_eq h hj).2.2]
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega)).1

set_option synthInstance.maxHeartbeats 100000

variable [StarRing c.F] (h : T.Pins) (hj : InR D j) (CI C2 : ℝ) (Vs : ValFam Xo c) (Hb : Type) [Fintype Hb]
  (NN : Submodule (𝓞 c.F) (cuspW Xo c U (gKap T j)))
  (Ph : cuspW Xo c U (gKapMinus T j) →ₗ[c.F] (Hb → cuspW Xo c U (gKap T j)))
  (e : cuspW Xo c U (gKap T j) →ₗ[c.F] cuspW Xo c U (gKap T j)) (g : ℕ)

def facWith : SlopeBoundLiftData c.F (pageOf Q) where
  w τ := wAn D j τ
  w0 τ := wj D j τ
  c1 τ := GlobalTheory.FlatLine.c1 U (xiR D) (psiOf h.1 τ)
  ua τ := nrm D (uAn D j τ)
  kap := nKap D j
  q' := qq D j
  pq := (pp D j : ℝ) - qq D j
  ι := Comp Xo c
  fι := haveI := CompFin.finite_comp Xo c; Fintype.ofFinite _
  nι := comp_nonempty h hj
  DY := dY D
  A := cA Q j
  cs := cStarInf U (xiR D) (fun _ => D.sp.W j) dict (gOne Q T j)
  X := CI * placeRankTwoOne.LL0 D L * nPrW Q j
  cc := ccOf Q U
  E0 := eZero D j
  Qcc := (numAt Q j).Qc
  ρ := rhoB Q j
  R1 := rOne Q C2 j
  R2 := rTwo Q j
  Bn := ((tN Q - 1).choose (placeRankTwoOne.dimY D) : ℕ)
  δ' := compMean fun Z => delPrime U Z (toWt (T.Dw j) (uOne Q j))
  h Z := compHeight U (xiR D) (fun _ => D.sp.W j) dict Z (gOne Q T j)
  sl Z := (compVolSlope U (xiR D) 8 Vs Z (toWt (T.Dw j) (uPr Q j))).toReal
  δc Z := compDeg U Z (gOne Q T j)
  dc Z := rankOn U Z (gTop Q T j)
  degc Z := degOn U (xiR D) (fun _ => D.sp.W j) dict Z (gTop Q T j)
  PPf := (numAt Q j).Pfl
  mv := shift D
  muU := slopeW_sq U (xiR D) (fun _ => D.sp.W j) dict (gMinus T j)
  nA := cDim (nrmAt U dict (gKapMinus T j))
  nB := cDim (piNorm Hb (nrmAt U dict (gKap T j)))
  nN := cDim (nrmAt U dict (gKap T j))
  XA := frameCo _
  XB := frameCo _
  XN := frameCo _
  LA := latCo _ (latW U (gKapMinus T j))
  LB := latCo _ (piLat Hb NN)
  NN := latCo _ NN
  Mk := latCo _ (latW U (gKap T j))
  φ := mapCo _ _ Ph
  e := mapCo _ _ e
  g := g
  PPh := 3 / 2 * Real.log (Fintype.card Hb) + (numAt Q j).U0
  abelian₂ := lamKap Q j + Real.log (Fintype.card Hb)
  δ := GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants.del D
  o' := GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.ringCost c.F
  n2 := measureMove D L

variable {U dict}

end GlobalTheory.SlopeRec
end
end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants Formalism.HN
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open Formalism.L2.Pj hiding kap
open GlobalTheory.CompHt hiding rhoB
open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

section Deep

variable (T : CoreJ D) (j : ℕ) {l : Level T.Q.H} (Xo : Moduli (T.Q.Dw j) l) (c : Coeff l)
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r)



variable {Q T j Xo c U dict}

end Deep

section Restrict

variable {K M M' : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M']


open Classical in
def restrictOr (φ : M →ₗ[K] M') (C : Submodule K M) (C' : Submodule K M') : C →ₗ[K] C' :=
  if h : ∀ x ∈ C, φ x ∈ C' then φ.restrict h else 0

end Restrict

section Keeps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem mul_mem_cuspW {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) {f g : Rul Xo c} (hf : f ∈ cuspW Xo c U G)
    (hg : g ∈ cuspW Xo c U G') : f * g ∈ cuspW Xo c U (G + G') := by
  rw [mem_cuspW] at hf hg ⊢
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [show exZ Dw (G + G') = exZ Dw G + exZ Dw G' from funext fun i => exZ_add _ _ _]
    exact mul_mem_secZ hf.1 hg.1
  · rw [AllWt.rdU_mul, show modelWt (U σ) (G + G') = fun k => modelWt (U σ) G k + modelWt (U σ) G' k from
      funext (modelWt_add (U σ) hG hG')]
    exact holSub_mul siegelSpaceAlgebra_holds (hf.2 σ hσ) (hg.2 σ hσ)

theorem levPh_mem_cuspW {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) (hK : KeepsCusp U (G + G'))
    (hK' : KeepsCusp U G') {S : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut Dw l)} (χ : S →* (c.F)ˣ) {u f : Rul Xo c}
    (hu : u ∈ cuspW Xo c U G') (hf : f ∈ cuspW Xo c U G) (h : S) : levPh Xo c S χ u f h ∈ cuspW Xo c U (G + G') := by
  rw [levPh_apply, levTr_apply]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hK _ _ (mul_mem_cuspW hG hG' hf (hK' _ _ hu)))


end Keeps


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure LiftData (T : CoreJ D) (i : Fin D.R.m) : Type 1 where

  l : Level T.Q.H
  typeLevel : IsTypeLevel l

  Xo : Moduli (T.Q.Dw ((i : ℕ) + 1)) l

  c : Coeff l

  U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r

  dict : ∀ σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U σ).X k).Ψ D.R.r

  fr : TypeFrame (T.Q.Dw ((i : ℕ) + 1)) l

  ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) c.F

  om : ∀ k : Fin 2, (ZMod (D.host.g k))ˣ →* (c.F)ˣ

  u₀ : cuspW Xo c U (gTw T.Q ((i : ℕ) + 1))

theorem inR_succ (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

namespace LiftData

variable {T : CoreJ D} {i : Fin D.R.m} (Y : LiftData T i)

abbrev Hb : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.l) := grpHR Y.fr

abbrev V (G : WTZ D.host.E) : Submodule Y.c.F (Rul Y.Xo Y.c) := cuspW Y.Xo Y.c Y.U G

def NN : Submodule (𝓞 Y.c.F) (Y.V (gKap T.Q ((i : ℕ) + 1))) := latN Y.fr Y.U _ Y.ψ

set_option synthInstance.maxHeartbeats 400000 in
def Ph : Y.V (gKapMinus T.Q ((i : ℕ) + 1)) →ₗ[Y.c.F] (Y.Hb → Y.V (gKap T.Q ((i : ℕ) + 1))) :=
  LinearMap.pi fun h => restrictOr (LinearMap.proj h ∘ₗ levPh Y.Xo Y.c Y.Hb (chiHR Y.fr Y.ψ) Y.u₀) _ _

set_option synthInstance.maxHeartbeats 400000 in
def eGood : Y.V (gKap T.Q ((i : ℕ) + 1)) →ₗ[Y.c.F] Y.V (gKap T.Q ((i : ℕ) + 1)) :=
  restrictOr (goodOp Y.Xo Y.c Y.typeLevel Y.fr Y.om i) _ _

variable (h : T.Q.Pins) (hK : KeepsCusp Y.U (gKap T.Q ((i : ℕ) + 1))) (he : IsIdempotentElem (goodIdemTw Y.om i))
include h hK he

end LiftData

variable {T : CoreJ D} (h : T.Q.Pins) {i : Fin D.R.m} (Y : LiftData T i) [StarRing Y.c.F] (CI C2 : ℝ)

def facOf : SlopeBoundLiftData Y.c.F (pageOf Q) :=
  facWith Q Y.U Y.dict h (inR_succ i) CI C2 (mixVals Y.Xo Y.c (bZero Q ((i : ℕ) + 1))) Y.Hb Y.NN Y.Ph Y.eGood
    (Nat.card (LevelGroup D.host))


open Classical in
def LiftData.ofCore (hT : LawsJ T) (i : Fin D.R.m) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) T.Q.c.F)
    (om : ∀ k : Fin 2, (ZMod (D.host.g k))ˣ →* (T.Q.c.F)ˣ)
    (u₀ : cuspW (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (gTw T.Q ((i : ℕ) + 1))) : LiftData T i where
  l := T.Q.l
  typeLevel := (isTypeLevel_of_pin hT.pins.2.1).1
  Xo := T.Q.Xo _
  c := T.Q.c
  U := T.U _
  dict σ g := if hσ : GoodEmb T.Q.c σ then T.dict _ σ (cast (congrArg (GA D) (hT.spaceW _ (inR_succ i) σ hσ)).symm g)
    else T.dict _ σ 1
  fr := ((isTypeLevel_of_pin hT.pins.2.1).1.nonempty_typeFrame (sig_eq hT.pins (inR_succ i)).2.2).some
  ψ := ψ
  om := om
  u₀ := u₀

end GlobalTheory.SlopeRec
