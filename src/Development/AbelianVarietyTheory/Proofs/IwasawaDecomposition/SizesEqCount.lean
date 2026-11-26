module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MkDetPtEqRelDetQ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdHstar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top

def duPre (B : Pre) (u : B.Word) : ℝ :=
  (letI := B.host.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm B.host.E B.R.k) (StandardLattice.stdLat B.host.E B.R.k)) *
    (StandardLattice.idxColLoc (B.host.g 0) B.R.k ^ B.R.f * StandardLattice.idxColLoc (B.host.g 1) B.R.k ^ B.R.f) *
    ∏ τ : Tau B.R, StandardLattice.dimV (fun i : Fin B.R.k => (((B.hcW u τ).u i : ℚ) : ℝ))

def DsPre (B : Pre) : ℝ :=
  (letI := B.host.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm B.host.E B.R.r) (StandardLattice.stdLat B.host.E B.R.r)) *
    (StandardLattice.idxRowLoc (B.host.g 0) B.R.k B.R.m ^ B.R.f * StandardLattice.idxRowLoc (B.host.g 1) B.R.k B.R.m ^ B.R.f) *
    ∏ τ : Tau B.R, Vol.trueDsig B.R (B.hc τ)

theorem Ctx.Over.sizes {K : Ctx} {B : Pre} (h : K.Over B) :
    (∀ u, (B.duStar u : ℝ) = duPre B u) ∧ B.Dstar = DsPre B := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  exact ⟨fun u => K.du_eq u, K.Ds_eq⟩

theorem sigYD_zero (R : Ranks) : 2 ≤ (sigYD R 0).1 ∧ (sigYD R 0).1 + (sigYD R 0).2 = R.r := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  simp only [sigYD, Ranks.rankY, Ranks.r]
  omega

theorem sizes_eq_count (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre) (hv : StandardLattice.VolumeEqMass₂ X.toD7)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    (∀ u, ((X.toD7.mem u).A.duStar : ℝ) = StandardLattice.duStarU X.toD7 u) ∧ X.toD7.what₂.Dstar = StandardLattice.DstarD X.toD7 := by
  obtain ⟨h1, h2⟩ := hO.sizes
  refine ⟨fun u => ?_, ?_⟩
  · have e : (X.toD7.mem u).A.duStar = X.B.duStar u := X.C.A_duStar u
    rw [e]
    refine (h1 u).trans ?_
    unfold duPre StandardLattice.duStarU StandardLattice.duStarP
    congr 1
  · have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
    rw [e, h2]
    have hvol : StandardLattice.volY0 X.toD7 = StandardLattice.massI X.toD7 X.B.R.r := by
      letI := X.toD7.host.cmStar
      have := hv.2 (X.toD7.sp.Y 0) (sigYD X.B.R 0).1 (sigYD X.B.R 0).2 (X.toD7.sp.Y_sig 0)
        (fun τ => X.toD7.Y_sigval 0 (Nat.zero_le _) τ) (sigYD_zero _).1
      rw [(sigYD_zero _).2] at this
      exact this
    unfold DsPre StandardLattice.DstarD StandardLattice.DstarP
    rw [hvol]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

end GlobalTheory.Mem.Top

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def latSD (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : (letI := B.host.cmStar; SDLat B.host.E (B.R.N i)) :=
  letI := B.host.cmStar
  ⟨((I.stp u a i).rep c).1.1.deco.1.N, GlobalTheory.SeamSelfDual.isSDLat_of_isSdLat _
    ⟨((I.stp u a i).rep c).1.1.deco.2.lat, ((I.stp u a i).rep c).1.1.deco.2.uni⟩⟩

def mtOf (a : I.ι) (j : ℕ) : (I.rec7 l Z).Dt →* ℂˣ :=
  if 1 ≤ j ∧ j ≤ B.R.m then
    (I.rec7 l Z).muTil j * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) else (I.rec7 l Z).muTil j

theorem mtOf_factors (u : B.Word) (a : I.ι) : GL3Theta.CarriesTupleCharacters (I.rec7 l Z) ((I.rec7 l Z).chTw u a) (I.mtOf l Z a)
    (fun i c => detPt B.host I.SQ ((I.stp u a i).rep c).1.1) := by
  intro i hi
  have hm : 1 ≤ i + 1 ∧ i + 1 ≤ B.R.m := ⟨by omega, hi⟩
  refine ⟨fun c => ?_, fun c => ?_⟩
  · show ((rhoAt I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ) = _
    rw [rhoAt_eq]
    simp only [GL3Theta.rhoOf, mtOf, if_pos hm]
    rfl
  · show ((rhoAt' I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ) = _
    rw [rhoAt'_eq]
    simp only [GL3Theta.rhoOf', mtOf, if_pos hm]
    rfl

def objOf (hok : I.Ok) (Qp : I.ι → Finset ℕ) (u : B.Word) (a : I.ι) : GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a) :=
  letI := B.host.cmStar
  { mt := I.mtOf l Z a
    L0 := fun i => ⟨GlobalTheory.Glob.IntegralWittCoefficients.Model.stdLat _ _, GlobalTheory.Glob.IntegralWittCoefficients.Model.isSDLat_std _ _⟩
    lattice_integral_coordinates := fun i x => GlobalTheory.Glob.IntegralWittCoefficients.Model.mem_stdLat x
    lat := fun i c => I.latSD u a i c
    dt := fun i c => detPt B.host I.SQ ((I.stp u a i).rep c).1.1
    dt_lat := fun i c => GlobalTheory.Mem.Col2.mk_detPt_eq_relDetQ B.R B.host _ _ _ _ I.SQ _ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).1
    c13 := I.mtOf_factors l Z u a
    frm := fun i y => y.1
    frm_inj := fun i _ => Subtype.val_injective
    frm_range := fun i _ f => ⟨by
        rintro ⟨y, rfl⟩ τ
        exact (y.2 τ).ne_zero, fun h => ⟨⟨f, fun τ => isUnit_iff_ne_zero.2 (h τ)⟩, rfl⟩⟩
    frm_de := fun _ _ _ _ => rfl
    dgen := I.J.cD
    dgen_gen := hok.amb_ok.dgen
    S := insert (B.T u) ({B.host.g 0, B.host.g 1} ∪ Qp a)
    Th := fun i c c' => I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') }

theorem objOf_unf (hok : I.Ok) (Qp : I.ι → Finset ℕ) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) :
    UnfIsAll (I.objOf l Z hok Qp u a) i := by
  intro c c' Q
  have e0 : ∀ (n : ℕ) (P : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N n)) ℂ),
      frPoly (I.objOf l Z hok Qp u a) n P = fnOf (Gr B.fields.emb B.embLL (B.R.N n)) 0 1 P := by
    intro n P
    funext y
    simp [frPoly, GL3Theta.evFr, fnOf, objOf]
    rfl
  have e1 : frInv (I.objOf l Z hok Qp u a) i (frPoly (I.objOf l Z hok Qp u a) i Q) = Q :=
    LinearMap.congr_fun (frInv_spec (I.objOf l Z hok Qp u a) hi) Q
  show fnOf _ 0 1 (jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 _ _)) 0 (polOf _ 0 (fr0 _ _ _) (frPoly (I.objOf l Z hok Qp u a) i Q))) =
    frPoly (I.objOf l Z hok Qp u a) (i + 1) (jetMap _ _ (frInv (I.objOf l Z hok Qp u a) i (frPoly (I.objOf l Z hok Qp u a) i Q)))
  have e2 : polOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i))
      (frPoly (I.objOf l Z hok Qp u a) i Q) = Q :=
    (congrArg _ (e0 i Q)).trans (GlobalTheory.TilClass.polOf_fnOf_one B.fields.emb B.embLL 0 Q)
  refine (congrArg (fun P => fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1
    (jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))) 0 P)) e2).trans ?_
  rw [e1, e0 (i + 1)]
  rfl

theorem lift_objects : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ Qp : I.ι → Finset ℕ, ∃ O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a), I.StdO l Z Qp O ∧ ∀ u a i, i < B.R.m → UnfIsAll (O u a) i := by
  intro B X I hok _ l Z Qp
  refine ⟨I.objOf l Z hok Qp, ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩, fun u a i hi => I.objOf_unf l Z hok Qp u a i hi.le⟩

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargets
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargets
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowSmooth

open GlobalTheory.ConjDS GlobalTheory.ConjExt Formalism.MainNotions.S

variable {D : D7} {V : HSp D}

def glue {S : D.what₂.Tau → D.what₂.Tau → SPar} (N : ∀ τ, DSModel V (S τ)) : DSModel V fun τ => S τ τ where
  H τ := (N τ).H τ
  σ τ := (N τ).σ τ
  lam τ := (N τ).lam τ
  ε τ := (N τ).ε τ
  fr τ := (N τ).fr τ
  enum τ := (N τ).enum τ
  ds τ := (N τ).ds τ
  fr_unit τ := (N τ).fr_unit τ
  fr_gram τ := (N τ).fr_gram τ

theorem dualPar_dualPar (S : SPar) : dualPar (dualPar S) = S := by
  unfold dualPar
  ext x
  simp only [Finset.mem_image]
  exact ⟨fun ⟨_, ⟨y, hy, e⟩, e'⟩ => by subst e e'; simpa using hy,
    fun hx => ⟨(-x.1, x.2), ⟨x, hx, rfl⟩, by simp⟩⟩

theorem low_of_conj {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (h : lowKSub ((conjModel M).ε τ) ((conjModel M).lam τ) ((conjModel M).σ τ) ≤ (conjModel M).sm τ) :
    lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
  intro w hw
  let c : (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := cj (M.H τ)
  have h1 := h (lowKSub_transfer (ε := M.ε τ) (ε' := (conjModel M).ε τ) (σ' := (conjModel M).σ τ) (fun _ => rfl) c
    (fun _ _ => rfl) hw)
  have h2 : ∀ y ∈ (conjModel M).sm τ, c y ∈ M.sm τ := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (smoothVec_map c (conj_rep M τ) hy)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearIsometryEquiv.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have h3 := h2 _ h1
  simpa using h3

theorem shape_at {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (h : HCParam D.R) {p q : ℕ}
    (hn : V.rank = D.R.r) (hpq : p + q = V.rank)
    (hS : S τ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) :
    Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ p ≤ V.rank, ∀ a, M.ε τ a = decide ((a : ℕ) < p) := by
  have key := GlobalTheory.HolDict.isEnum_holPar_kapW h hn hpq (hS ▸ M.enum τ)
  refine ⟨⟨(M.enum τ).1, fun a => ?_⟩, p, by omega, fun a => (key a).2⟩
  obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int h a
  obtain ⟨s, hs⟩ := Formalism.L2.NTheta.odd_r D.R
  refine ⟨z - s, ?_⟩
  have hr : ((V.rank : ℕ) : ℝ) = 2 * s + 1 := by rw [hn, hs]; push_cast; rfl
  rw [(key a).1, hz, hr]
  push_cast
  ring

theorem lowSm_MW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i σ, LowSm (R.MW i σ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i σ
  have key : ∀ τ, ∃ (S : D.what₂.Tau → SPar) (N : DSModel (Wc D i) S),
      (Formalism.QuantumDeterminants.IsHCParam (N.lam τ) ∧ ∃ p ≤ (Wc D i).rank, ∀ a, N.ε τ a = decide ((a : ℕ) < p)) ∧
      (lowKSub (N.ε τ) (N.lam τ) (N.σ τ) ≤ N.sm τ →
        lowKSub ((R.MW i σ).ε τ) ((R.MW i σ).lam τ) ((R.MW i σ).σ τ) ≤ (R.MW i σ).sm τ) := fun τ => by
    have hpq := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i τ
    by_cases hb : labE σ (lab σ τ) = tauE D τ
    · exact ⟨_, R.MW i σ, shape_at _ τ (D.hc (lab σ τ)) (rank_Wc i) hpq (if_pos hb), id⟩
    · refine ⟨_, conjModel (R.MW i σ), shape_at _ τ (D.hc (lab σ τ)) (rank_Wc i) hpq ?_, low_of_conj _ τ⟩
      unfold Links.parAt
      rw [if_neg hb, dualPar_dualPar]
      rfl
  choose S N hN hL using key
  exact fun τ => hL τ ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ (glue N) hN).1 τ)

end GlobalTheory.LowSmooth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargetsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_kType_smooth_models_on_theta_targets : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i σ, LowSm (R.MW i σ) := by
  first | exact @GlobalTheory.LowSmooth.lowSm_MW | exact GlobalTheory.LowSmooth.lowSm_MW | (intros; apply GlobalTheory.LowSmooth.lowSm_MW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageLoc
noncomputable section

namespace GlobalTheory.Mem.SProv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

theorem delv_pos (s : Scale) (cD : ℝ) : (0 : ℚ) < (Delv s cD : ℚ) := by
  have h : 0 < s.x ^ cD := Real.rpow_pos_of_pos (lt_trans one_pos s.one_lt_alt) _
  exact_mod_cast Nat.ceil_pos.2 h

theorem code_of_over (K : Ctx) (B : Pre) (h : K.Over B) :
    ∃ letter : B.Word → Fin (B.R.k - 2) → Bool, Function.Injective letter ∧
      (∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l + 1 < B.R.k - 1),
        (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * (Delv K.s K.cD : ℚ)) ∧
      ∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l < B.R.k - 2),
        (B.hcW w τ).u ⟨l + 1, by omega⟩ =
          (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then (Delv K.s K.cD : ℚ) else 0) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  refine ⟨K.c, K.ok.inj, fun w τ l h => ?_, K.ok.code⟩
  have h' : l + 1 < K.P.R.k - 1 := h
  have a := (K.ok.hc w).1 τ ⟨l, by omega⟩
  have b := (K.ok.hc w).1 τ ⟨l + 1, h'⟩
  have e : K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1 := by omega
  show (K.P.hcW w τ).v ⟨l, _⟩ - (K.P.hcW w τ).v ⟨l + 1, h'⟩ = _
  rw [a, b]
  simp only [e]
  push_cast
  ring

theorem exists_split (B : Pre) (p : HeightOneSpectrum (𝓞 B.host.F)) (L : LocAt B.host.F B.host.E B.conjF p) :
    ∃ s : Option (SplitAt L.Fp L.Ep L.cj (resChar p)),
      (s.isSome ↔ resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  letI := B.host.cmStar
  by_cases h : resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · have hk : ∃ k, resChar p = B.host.g k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> exact ⟨_, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt B.host.F B.host.E B.conjF B.sp.cm.deg2 (SpectralModel.conjF_ne B) p L
      (by rw [hk, SpectralModel.ncard_primesOver _ _ (B.host.g_prime k), B.g_split])
    exact ⟨some S, by simpa using h⟩
  · exact ⟨none, by simp [h]⟩

theorem exists_sStage_loc (K : Ctx) (B : Base) (C : Cols B) (W : RowsRest B C) (cd : CDHaar) (h : K.Over B.toPre)
    (h2 : SpectralModel.ColsPos C) (h3 : W.Drows ≤ W.Dall)
    (L : ∀ p : HeightOneSpectrum (𝓞 B.host.F), LocAt B.host.F B.host.E B.toPre.conjF p) :
    ∃ S : SStage B C W, S.s.Del = (Delv K.s K.cD : ℚ) ∧ S.s.cdScale = Vol.trueScale cd ∧
      (∀ τ, S.dsig τ = Vol.trueDsig B.R (B.hc τ)) ∧
      ∀ p, ∃ s, S.s.atP p = { L p with split := s } := by
  obtain ⟨letter, hl, hg, hu⟩ := code_of_over K B.toPre h
  obtain ⟨S, hd, -⟩ := SpectralModel.exists_sStage W ⟨_, letter, delv_pos K.s K.cD, hl, hg, hu⟩ h2 h3
    (fun τ => Vol.trueDsig B.R (B.hc τ)) (fun τ => (Vol.lamSH_isHCParam_and_trueDsig_pos B.R (B.hc τ)).2) (fun _ => 0)
  choose sp hsp using fun p => exists_split B.toPre p (L p)
  exact ⟨{ S with
      s := { S.s with
        cdScale := Vol.trueScale cd
        cdScale_pos := Vol.trueScale_pos cd
        Del := (Delv K.s K.cD : ℚ)
        Del_pos := delv_pos K.s K.cD
        cloud_gap := hg
        letter := letter
        letter_inj := hl
        u_letter := hu
        atP := fun p => { L p with split := sp p } }
      s_split := hsp
      s_HH := S.s_HH
      s_Cu := S.s_Cu
      s_PlF := S.s_PlF
      s_Cu_isom := S.s_Cu_isom
      sEE := S.sEE },
    rfl, rfl, fun τ => congrFun hd τ, fun p => ⟨sp p, rfl⟩⟩

end GlobalTheory.Mem.SProv

end
end

noncomputable section

namespace GlobalTheory.Mem.SProv

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top

theorem conjF_invol (B : Pre) (x : B.host.E) : B.conjF (B.conjF x) = x := by
  rw [B.conjF_eq, B.conjF_eq]
  simpa [Examples₂.conjF_apply] using Examples₂.conjF_conjF B.host x

theorem exists_sStage_true : ∀ (K : Ctx) (B : Base) (C : Cols B) (W : RowsRest B C) (cd : CDHaar), K.Over B.toPre →
    SpectralModel.ColsPos C → W.Drows ≤ W.Dall → ∃ S : SStage B C W, S.s.Del = (Delv K.s K.cD : ℚ) ∧
      S.s.cdScale = Vol.trueScale cd ∧ (∀ τ, S.dsig τ = Vol.trueDsig B.R (B.hc τ)) ∧
      ∀ (V : DivStage B C W) (N : NStage B C W) (G : GJStage B C) p,
        Nonempty (Formalism.L2.S.LocIso ((assemble B C W V S N G).s.atP p) (Formalism.L2.S.locC (assemble B C W V S N G) p)) := by
  intro K B C W cd h h2 h3
  obtain ⟨S, a, b, c, d⟩ := exists_sStage_loc K B C W cd h h2 h3
    (fun p => Examples₂.locAtC B.toPre.conjF (conjF_invol B.toPre) (Examples₂.finrank_FE B.host) p)
  exact ⟨S, a, b, c, fun V N G => Formalism.L2.S.loc_of_adj (assemble B C W V S N G) d⟩

end GlobalTheory.Mem.SProv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.BaseEnl

open GlobalTheory.Mem.BaseExt

section map

variable {L L' : Type} [Field L] [Field L'] [CharZero L] [CharZero L'] (ι : L →ₐ[ℚ] L')
  (K : IntermediateField ℚ L)

def toMap : K →+* K.map ι := (K.equivMap ι).toRingEquiv.toRingHom

theorem coe_toMap (x : K) : (toMap ι K x : L') = ι x := rfl

theorem toMap_surj : Function.Surjective (toMap ι K) := (K.equivMap ι).surjective

theorem image_map {E : Type} [Field E] (𝔞 : Ideal (𝓞 E)) (e : E → L) :
    extend (toMap ι K) (Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : L) = e (a : E)}) =
      Submodule.span (𝓞 (K.map ι)) {x : K.map ι | ∃ a ∈ 𝔞, (x : L') = ι (e (a : E))} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, by rw [coe_toMap, hy]⟩
  · rintro ⟨a, ha, hx⟩
    obtain ⟨y, rfl⟩ := toMap_surj ι K x
    exact ⟨y, ⟨a, ha, ι.injective hx⟩, rfl⟩

end map

theorem exists_enl : ∀ (B : Base) (S : Finset ℂ), (∀ z ∈ S, IsAlgebraic ℚ z) →
    ∃ B' : Base, Enl B B' ∧ ∀ z ∈ S, ∃ x : B'.LL, B'.embLL x = z := by
  classical
  intro B S h
  obtain ⟨SE, hSE, hE⟩ := exists_gens B.LL
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable (S ∪ SE) (by
    intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [h z hz, hSE z hz])
  have hEK := hE K (fun z hz => hS z (Finset.mem_union_right _ hz)) B.embLL
  have : NumberField K := {}
  let ι : B.LL →ₐ[ℚ] K := (B.embLL.codRestrict K hEK).toRatAlgHom
  have hι : ∀ x, K.val (ι x) = B.embLL x := fun _ => rfl
  have tr : ∀ (F : IntermediateField ℚ B.LL) (w : ℂ), (∃ z ∈ F, B.embLL z = w) →
      ∃ z ∈ F.map ι, K.val z = w := by
    rintro F w ⟨z, hz, rfl⟩
    exact ⟨ι z, ⟨z, hz, rfl⟩, rfl⟩
  have im : ∀ F : IntermediateField ℚ B.LL,
      (K.val : K →+* ℂ) '' (F.map ι : Set K) = B.embLL '' (F : Set B.LL) := by
    intro F
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · exact tr F w
  have hg0 := B.coeffGaloisSubfield_isGalois
  let f := toMap ι B.Ks
  refine ⟨{ toPre := B.toPre
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := (ι : B.LL →+* K).comp B.embE
            embE_φ₀ := by rw [← B.embE_φ₀]; rfl
            LL0 := B.LL0.map ι
            coeffGaloisSubfield_isGalois := @IsGalois.of_algEquiv ℚ B.LL0 _ _ (B.LL0.map ι) _ _ _ hg0 (B.LL0.equivMap ι)
            Ks := B.Ks.map ι
            Ks_le := IntermediateField.map_mono ι B.Ks_le
            E_le_Ks := fun x => ⟨B.embE x, B.E_le_Ks x, rfl⟩
            roots_Ks := fun N hN => tr _ _ (B.roots_Ks N hN)
            roots_Ks' := fun N hN => tr _ _ (B.roots_Ks' N hN)
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := tr _ _ B.rootOfUnity_eightQ_mem_coeffGaloisSubfield
            roots_LL := fun u => ?_ }, ⟨rfl, im _, im _, ?_⟩, ?_⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := B.capit 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_map ι B.Ks 𝔞 B.embE)
  · intro j hj1 hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := B.kPsi j hj1 hj 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_map ι B.Ks 𝔞 (fun a => B.embE (B.host.sigmaOf g a))
    have e2 := image_map ι B.Ks 𝔞 (fun a => B.embE (B.host.sigmaOf g (B.host.conj a)))
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · obtain ⟨z, hz⟩ := B.roots_LL u
    exact ⟨ι z, hz⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨ι z, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (Finset.mem_union_left _ hz)⟩, rfl⟩

end GlobalTheory.Mem.BaseEnl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.DilPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_mk_iff {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} (r : 𝓞 E) :
    HasRes P z (Ideal.Quotient.mk P.asIdeal r) ↔ Valued.v (z - algebraMap E _ (algebraMap (𝓞 E) E r)) < 1 := by
  constructor
  · rintro ⟨r', hr', h⟩
    have hm : r' - r ∈ P.asIdeal := Ideal.Quotient.eq.1 hr'
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r' - r))) < 1 := by
      rw [valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hm
    have e : z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) =
        (z - algebraMap E _ (algebraMap (𝓞 E) E r')) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r' - r)) := by
      simp only [map_sub]
      ring
    rw [e]
    exact Valuation.map_add_lt _ h h2
  · intro h
    exact ⟨r, rfl, h⟩

theorem hasRes_le_one {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P z c) : Valued.v z ≤ 1 := by
  obtain ⟨r, -, hr⟩ := h
  have h1 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 := by
    rw [valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one _ _
  have e : z = (z - algebraMap E _ (algebraMap (𝓞 E) E r)) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) := by
    ring
  rw [e]
  exact Valuation.map_add_le _ hr.le h1

theorem hasRes_lt_one {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} (h : HasRes P z 0) : Valued.v z < 1 := by
  have := (hasRes_mk_iff (P := P) (z := z) 0).1 (by simpa using h)
  simpa using this

theorem last_sub_lt {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (r : Fin n) (Ki : Fin n → P.adicCompletion E)
    (D : Fin n → Fin n → P.adicCompletion E) (U : Fin n → P.adicCompletion E) (C : P.adicCompletion E)
    (hK : ∀ j, Valued.v (Ki j) ≤ 1) (hK' : ∀ j, j ≠ r → Valued.v (Ki j) < 1)
    (hD : ∀ j l, Valued.v (D j l) ≤ 1) (hDr : ∀ l, Valued.v (D r l - if l = r then C else 0) < 1)
    (hU : ∀ l, Valued.v (U l) ≤ 1) (hC : Valued.v C ≤ 1) :
    Valued.v ((∑ j, Ki j * ∑ l, D j l * U l) - C * ∑ j, Ki j * U j) < 1 := by
  have e : (∑ j, Ki j * ∑ l, D j l * U l) - C * ∑ j, Ki j * U j =
      ∑ j, Ki j * ((∑ l, D j l * U l) - C * U j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
  rw [map_mul]
  by_cases hj : j = r
  · subst hj
    have e2 : (∑ l, D j l * U l) - C * U j = ∑ l, (D j l - if l = j then C else 0) * U l := by
      simp only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e2]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' (hK j)) ?_
    exact Valuation.map_sum_lt _ one_ne_zero fun l _ => by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hU l)) (hDr l)
  · refine lt_of_le_of_lt (mul_le_of_le_one_right' ?_) (hK' j hj)
    refine Valuation.map_sub _ _ _ |>.trans (max_le ?_ ?_)
    · exact Valuation.map_sum_le _ fun l _ => by
        rw [map_mul]
        exact mul_le_one' (hD j l) (hU l)
    · rw [map_mul]
      exact mul_le_one' hC (hU j)

theorem pullbackVector_triple_mul {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (y * δ * k) x =
      ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV y x) := by
  unfold GlobalTheory.Mem.Col2.pullV
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem pullbackVector_mul_right {n : ℕ} (y k : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (y * k) x =
      ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV y x := by
  unfold GlobalTheory.Mem.Col2.pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]

theorem adAt_pullV_triv {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (w : HeightOneSpectrum (𝓞 E))
    (ht : ∀ i j, adAt F w ((δ⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0) (x : Sp E n) (i : Fin n) :
    adAt F w (GlobalTheory.Mem.Col2.pullV (y * δ * k) x i) = adAt F w (GlobalTheory.Mem.Col2.pullV (y * k) x i) := by
  rw [pullbackVector_triple_mul, pullbackVector_mul_right]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ht, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem adeleComponentAt_triple_mul_dilation_trivial {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (w : HeightOneSpectrum (𝓞 E))
    (ht : ∀ i j, adAt F w ((δ⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0) (i j : Fin n) :
    adAt F w ((y * δ * k : GL (Fin n) (AfE F E)).1 i j) = adAt F w ((y * k : GL (Fin n) (AfE F E)).1 i j) := by
  have h1 : ((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
    ext a b
    rw [Matrix.map_apply, ht, Matrix.one_apply]
  have h2 : (δ : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
    have e : (δ : Matrix (Fin n) (Fin n) (AfE F E)) * ((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have := congrArg (fun M : Matrix (Fin n) (Fin n) (AfE F E) => M.map (adAt F w)) e
    simp only [Matrix.map_mul, h1, mul_one, Matrix.map_one (adAt F w) (map_zero _) (map_one _)] at this
    exact this
  have e : ((y * δ * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) =
      ((y * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) := by
    simp only [Units.val_mul, Matrix.map_mul, h2, mul_one]
  exact congrArg (fun M => M i j) e

theorem isPointOf_last_coordinate_dilation_one_prime_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (y δ k : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (P : ST) (c : (𝓞 E ⧸ P.1.asIdeal)ˣ) (b : 𝓞 E ⧸ P.1.asIdeal), IsPtOf hc (y * k) p → k ∈ Formalism.L2.Herm.UstdAf hc n → δ ∈ Formalism.L2.Herm.UstdAf hc n → Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) → (∀ i j, δ.1 i j ∈ RInt F E) → (∀ i j, (δ⁻¹).1 i j ∈ RInt F E) → (∀ w : HeightOneSpectrum (𝓞 E), (w ∈ SG ∨ w ∈ Q ∨ (w ∈ ST ∧ w ≠ P.1)) → ∀ i j, adAt F w ((δ⁻¹).1 i j) = if i = j then 1 else 0) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹).1 r j)) (if j = r then b else 0)) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((δ⁻¹).1 r j)) (if j = r then (c : 𝓞 E ⧸ P.1.asIdeal) else 0)) → p'.deco = DecoSet.dia1 P c p.deco → p'.fr = p.fr → IsPtOf hc (y * δ * k) p' := by
  intro F E _ _ _ _ _ _ hc n ST SG Q y δ k p p' P c b h hk hδ hkc hδi hδi' htriv hkr hδr hdeco hfr
  classical
  have hy : y ∈ Formalism.L2.Herm.UstdAf hc n := by
    have := mul_mem h.uni (inv_mem hk)
    rwa [mul_inv_cancel_right] at this
  have hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E :=
    fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))
  have hδI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E := by
    intro z
    constructor
    · intro hz i
      exact PtExist.mulVec_int hδi' hz i
    · intro hz i
      have := PtExist.mulVec_int hδi hz i
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  have hN : p'.deco.1.N = p.deco.1.N := by rw [hdeco]; rfl
  have hbe : p'.deco.1.be = p.deco.1.be := by rw [hdeco]; rfl
  have hf : ∀ (P' : ST) (x : Sp E n), p'.deco.1.f P' x =
      ((Pi.mulSingle (M := fun Q : ST => (𝓞 E ⧸ Q.1.asIdeal)ˣ) P c P' : (𝓞 E ⧸ P'.1.asIdeal)ˣ) : 𝓞 E ⧸ P'.1.asIdeal) * p.deco.1.f P' x := by
    intro P' x
    rw [hdeco]
    rfl
  have hu : ∀ x ∈ p.deco.1.N, ∀ l, GlobalTheory.Mem.Col2.pullV y x l ∈ RInt F E := by
    intro x hx
    refine (hkI _).2 ?_
    rw [← pullbackVector_mul_right]
    exact (mem_latS_std _).1 ((h.lat _).1 (Submodule.subset_span ⟨x, hx, rfl⟩))
  refine ⟨mul_mem (mul_mem hy hδ) hk, fun z => ?_, fun P' x hx i hi => ?_, fun w x hx i => ?_, fun P' i j => ?_⟩
  · rw [hN]
    refine (h.lat z).trans ((mem_latS_std _).trans (Iff.trans ?_ (mem_latS_std _).symm))
    have e1 : ((y * k : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ z =
        ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) := by
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
    have e2 : ((y * δ * k : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ z =
        ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z)) := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    rw [e1, e2]
    exact (hkI _).symm.trans ((hδI _).trans (hkI _))
  · rw [hN] at hx
    have hv := h.f P' x hx i hi
    rw [hf]
    by_cases hPP : P' = P
    · subst hPP
      rw [Pi.mulSingle_eq_same]
      obtain ⟨s, hs, hv'⟩ := hv
      obtain ⟨cr, hcr⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 E ⧸ P'.1.asIdeal)
      rw [← hs, ← hcr, ← map_mul, hasRes_mk_iff]
      have hint : ∀ a ∈ RInt F E, Valued.v (adAt F P'.1 a) ≤ 1 := fun a ha => (mem_rInt_iff F E a).1 ha P'.1
      have hCle : Valued.v (algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr)) ≤ 1 := by
        rw [valued_algebraMap]
        exact HeightOneSpectrum.valuation_le_one _ _
      have key := last_sub_lt i (fun j => adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j))
        (fun j l => adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l))
        (fun l => adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) (algebraMap E _ (algebraMap (𝓞 E) E cr))
        (fun j => hasRes_le_one (hkr i j hi))
        (fun j hj => by
          have := hkr i j hi
          rw [if_neg hj] at this
          exact hasRes_lt_one this)
        (fun j l => hint _ (hδi' j l))
        (fun l => by
          have := hδr i l hi
          by_cases hl : l = i
          · rw [if_pos hl, ← hcr, hasRes_mk_iff] at this
            rw [if_pos hl]
            exact this
          · rw [if_neg hl] at this
            rw [if_neg hl, sub_zero]
            exact hasRes_lt_one this)
        (fun l => hint _ (hu x hx l)) hCle
      rw [pullbackVector_mul_right] at hv'
      rw [pullbackVector_triple_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at hv' key ⊢
      have e : (∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) *
            ∑ l, adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) -
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E s) =
          ((∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) *
            ∑ l, adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) -
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            ∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x j)) +
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            ((∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x j)) -
              algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E s)) := by ring
      rw [e]
      refine Valuation.map_add_lt _ key ?_
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hCle) hv'
    · rw [Pi.mulSingle_eq_of_ne hPP, Units.val_one, one_mul,
        adAt_pullV_triv y δ k P'.1 (htriv P'.1 (Or.inr (Or.inr ⟨P'.2, fun e => hPP (Subtype.ext e)⟩))) x i]
      exact hv
  · rw [hN] at hx
    rw [hbe, adAt_pullV_triv y δ k w.1 (htriv w.1 (Or.inl w.2)) x i]
    exact h.be w x hx i
  · rw [hfr, adeleComponentAt_triple_mul_dilation_trivial y δ k P'.1 (htriv P'.1 (Or.inr (Or.inl P'.2))) i j]
    exact h.fr P' i j

end GlobalTheory.Mem.Col2.DilPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPointOf_last_coordinate_dilation_one_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (y δ k : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (P : ST) (c : (𝓞 E ⧸ P.1.asIdeal)ˣ) (b : 𝓞 E ⧸ P.1.asIdeal), IsPtOf hc (y * k) p → k ∈ Formalism.L2.Herm.UstdAf hc n → δ ∈ Formalism.L2.Herm.UstdAf hc n → Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) → (∀ i j, δ.1 i j ∈ RInt F E) → (∀ i j, (δ⁻¹).1 i j ∈ RInt F E) → (∀ w : HeightOneSpectrum (𝓞 E), (w ∈ SG ∨ w ∈ Q ∨ (w ∈ ST ∧ w ≠ P.1)) → ∀ i j, adAt F w ((δ⁻¹).1 i j) = if i = j then 1 else 0) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹).1 r j)) (if j = r then b else 0)) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((δ⁻¹).1 r j)) (if j = r then (c : 𝓞 E ⧸ P.1.asIdeal) else 0)) → p'.deco = DecoSet.dia1 P c p.deco → p'.fr = p.fr → IsPtOf hc (y * δ * k) p' := by
  first | exact @GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt | exact GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt | (intros; apply GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df

theorem toCx_smul {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (c : B.LL) (x : (MtHL I hX a).V) :
    toCx I hX a (c • x) = B.embLL c • toCx I hX a x := by
  have h1 : toCx I hX a (c • x) = toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
      (c • (show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from x)) := rfl
  rw [h1, LinearMap.map_smulₛₗ]
  rfl

theorem toCx_add {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x y : (MtHL I hX a).V) :
    toCx I hX a (x + y) = toCx I hX a x + toCx I hX a y := by
  have h1 : toCx I hX a (x + y) = toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
      ((show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from x) + (show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from y)) := rfl
  rw [h1, map_add (f := _)]
  rfl

noncomputable def toCxₛₗ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a where
  toFun := toCx I hX a
  map_add' := toCx_add I hX a
  map_smul' := toCx_smul I hX a

theorem toCx_linearIndependent {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) :
    LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) :=
  toMtilde_linearIndependent _ _ _ _ _ _ (MtHL I hX a).b.linearIndependent

theorem toCx_span {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) :
    Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  rw [eq_top_iff, ← toMtilde_span B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL hX, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hle : Submodule.span B.LL (Set.range (MtHL I hX a).b) ≤
      Submodule.comap (toCxₛₗ I hX a) (Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [(MtHL I hX a).b.span_eq] at hle
  exact hle (Submodule.mem_top (x := (x : (MtHL I hX a).V)))

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem mtHL_good {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) : (MtHL I hX a).Good :=
  MtildeH_good _ _ _ _ _ _
end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem mtHL_good_basis : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι), (MtHL I hX a).Good ∧ (∃ j : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a, ∀ x, j x = toCx I hX a x) ∧ LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) ∧ Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  intro B X I hX a
  refine ⟨?_, ⟨{ toFun := toCx I hX a, map_add' := fun x y => ?_, map_smul' := fun c x => ?_ }, fun _ => rfl⟩,
    toCx_linearIndependent I hX a, toCx_span I hX a⟩
  · exact mtHL_good I hX a
  · exact toCx_add I hX a x y
  · exact toCx_smul I hX a c x

end GlobalTheory.Mem.Df
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι), (MtHL I hX a).Good ∧ (∃ j : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a, ∀ x, j x = toCx I hX a x) ∧ LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) ∧ Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  first | exact @GlobalTheory.Mem.Df.mtHL_good_basis | exact GlobalTheory.Mem.Df.mtHL_good_basis | (intros; apply GlobalTheory.Mem.Df.mtHL_good_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DsPPosAndLower
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.DsLow

theorem dimV_cast {n n' : ℕ} (h : n = n') (x : Fin n' → ℝ) :
    StandardLattice.dimV (fun i : Fin n => x (Fin.cast h i)) = StandardLattice.dimV x := by
  subst h; rfl

theorem trueDsig_eq_dimV (R : Ranks) (p : HCParam R) :
    Vol.trueDsig R p =
      StandardLattice.dimV (Fin.append (fun i => ((p.v i : ℚ) : ℝ)) (fun j => -((p.b j : ℚ) : ℝ))) := by
  have hk := R.m_add_three_le_k
  have hd : 2 * R.rS + R.k + 1 = R.k - 1 + R.m := by
    rw [Formalism.MainNotions.S.dimS_eq R]; simp only [Ranks.r]; omega
  unfold Vol.trueDsig
  rw [← StandardLattice.dimV_eq_fdegHC _ (Vol.lamSH_isHCParam R p).1, ← dimV_cast hd]
  congr 1
  funext a
  have key : ∀ (c : Fin (R.k - 1 + R.m)) (d : Fin R.r), d.val = c.val → Formalism.MainNotions.S.lamS R p d =
      Fin.append (fun i => ((p.v i : ℚ) : ℝ)) (fun j => -((p.b j : ℚ) : ℝ)) c := by
    intro c d hcd
    unfold Formalism.MainNotions.S.lamS
    induction c using Fin.addCases with
    | left i =>
      have hi : d.val = i.val := hcd
      have h1 : d.val < R.k - 1 := hi ▸ i.2
      rw [Fin.append_left, dite_eq_left h1]
      have e : (⟨d.val, h1⟩ : Fin (R.k - 1)) = i := Fin.ext hi
      rw [e]
    | right j =>
      have hj : d.val = R.k - 1 + j.val := hcd
      have h1 : ¬ d.val < R.k - 1 := by omega
      have h2 : d.val - (R.k - 1) < R.m := by have := j.2; omega
      rw [Fin.append_right, dite_eq_right h1, dite_eq_left h2]
      have e : (⟨d.val - (R.k - 1), h2⟩ : Fin R.m) = j := Fin.ext (by simp only; omega)
      rw [e]
  exact key _ _ rfl

theorem idxRowLoc_pos (g k m : ℕ) (hg : g.Prime) : 0 < StandardLattice.idxRowLoc g k m := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold StandardLattice.idxRowLoc StandardLattice.idxLoc
  haveI : Nonempty {A : GL (Fin (k + m - 1)) (ZMod g) //
      StandardLattice.IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} := by
    refine ⟨⟨1, ?_, ?_, ?_, ?_⟩⟩
    · intro i j h
      have : i ≠ j := by rintro rfl; exact lt_irrefl _ h
      simp [Matrix.one_apply_ne this]
    · intro i; simp
    · intro i j _ h
      simp [Matrix.one_apply_ne h.ne']
    · intro i j _ h _
      simp [Matrix.one_apply_ne h]
  apply div_pos
  · exact_mod_cast Nat.card_pos
  · exact_mod_cast Nat.card_pos

theorem DsP_pos_and_lower : ∀ P : PreCh, 0 < DsP P ∧ (2 / 3 : ℝ) ^ P.R.f * (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)) * (StandardLattice.idxRowLoc (P.H.g 0) P.R.k P.R.m ^ P.R.f * StandardLattice.idxRowLoc (P.H.g 1) P.R.k P.R.m ^ P.R.f) * ∏ τ : Tau P.R, StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ)) (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) ≤ DsP P := by
  intro P
  have hm : 0 < (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)) := by
    letI := P.H.cmStar
    show 0 < Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)
    rw [StandardLattice.standard_form_eq_telescope_form, StandardLattice.standard_lattice_eq_telescope_lattice]
    exact Formalism.HermitianLatticesTheory.massTelescope_std_pos P.H.E (host_cmData P.R P.H).cmUnram _
  have h0 := idxRowLoc_pos _ P.R.k P.R.m (P.H.g_prime 0)
  have h1 := idxRowLoc_pos _ P.R.k P.R.m (P.H.g_prime 1)
  have hp : 0 < ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ) :=
    Finset.prod_pos fun τ _ => (Vol.lamSH_isHCParam_and_trueDsig_pos _ _).2
  have hD : 0 < DsP P := by
    unfold DsP
    exact mul_pos (mul_pos hm (mul_pos (pow_pos h0 _) (pow_pos h1 _))) hp
  refine ⟨hD, ?_⟩
  have hc : (2 / 3 : ℝ) ^ P.R.f ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have he : ∏ τ : Tau P.R, StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ))
      (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) = ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ) :=
    Finset.prod_congr rfl fun τ _ => (trueDsig_eq_dimV _ _).symm
  rw [he]
  calc _ = (2 / 3 : ℝ) ^ P.R.f * DsP P := by unfold DsP; ring
    _ ≤ DsP P := mul_le_of_le_one_left hD.le hc

end GlobalTheory.Mem.Top.DsLow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOneMemOfIsRayFieldIn
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.RayRoots

theorem rootOne_mem_of_isRayFieldIn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ)
    (N n : ℕ) (M : IntermediateField ℚ ℂ), N ≠ 0 → n ∣ N → IsRayFieldIn φ (natIdeal E N) M → rootOne n ∈ M :=
  fun _ _ _ _ φ _ _ _ hN hn hM => GlobalTheory.Mem.FieldsEx.rootOne_mem_ray φ hN hn hM

end GlobalTheory.Mem.RayRoots
end
