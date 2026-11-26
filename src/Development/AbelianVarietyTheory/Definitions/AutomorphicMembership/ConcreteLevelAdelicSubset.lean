module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  MeasureTheory NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev JR (R : RealDat D A Ks) (F : Face D A) : Set (GA D (Yc D 0)) := levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))

abbrev chiR (R : RealDat D A Ks) (F : Face D A) : GA D (Yc D 0) → ℂ := levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))

abbrev MultR (R : RealDat D A Ks) (F : Face D A) : Submodule ℂ (MMap (MP R)) := Mult R.θ (R.MY 0) (JR R F) (chiR R F)

def DallTie (R : RealDat D A Ks) (F : Face D A) : Prop := D.what₂.Dall = Module.finrank ℂ (MultR R F)

def concreteLevelAdelicSubset (X : HidaSetting D) : Set X.B.I.GA := {x | x.1 = 1 ∧ x.2 ∈ X.K2}

def adelicCharacterOfHidaSetting (X : HidaSetting D) : X.B.I.GA → ℂ := fun x => star (X.chi2 x.2)

def GrpPin (R : RealDat D A Ks) : Prop :=
  ∃ (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff (eR g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧
      ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)

structure SeeAt (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) : Prop where

  fin : t ∈ GfC (Yc D 0)

  conj : ConjLevel t⁻¹ (JR R F) (chiR R F) (iotaX X h ⁻¹' concreteLevelAdelicSubset X) (fun k => adelicCharacterOfHidaSetting X (iotaX X h k))

  mat : RowLevelMatchAt R F X h t

def conjRows (X : HidaSetting D) : Submodule ℂ (L2X X) := (HHX X).comap (conjL (muX X)).toLinearEquiv.toLinearMap

def EvalOn (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (v₀ : (MP R).Vec) (c : ℝ) (E : Submodule ℂ (MMap (MP R))) (E' : Submodule ℂ (L2X X)) : Prop :=
  ∃ J : E ≃ₗ[ℂ] E', ∀ S : E,
    ((J S : E') : L2X X) =ᵐ[muX X] (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) ∧
      ‖((J S : E') : L2X X)‖ ^ 2 = c * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re

def RowJ (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (G : GoodOp X) (t : GA D (D.sp.Y 0)) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) : Prop :=
  ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ a : ℝ, 0 < a ∧ ∀ x : D.what₂.EE,
    ((j x : EEC X G) : L2X X) =ᵐ[muX X] fun g => (a : ℂ) * ev (MP R) v₀ (R.HE.e (eE x)) ((iotaX X h).symm g * t)

theorem SeeAt.levelMatchA {R : RealDat D A Ks} {F : Face D A} {X : HidaSetting D}
    {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {t : GA D (D.sp.Y 0)} (hs : SeeAt R F X h t) : LevelMatchA R F X h t := by
  intro k hk
  have e : (t⁻¹⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ : GA D (D.sp.Y 0)) = (iotaX X h).symm (1, k) := by group
  obtain ⟨h1, h2⟩ := hs.conj (t⁻¹ * (iotaX X h).symm (1, k) * t)
  rw [e] at h1 h2
  have hm := h1.2 (by simp [concreteLevelAdelicSubset, hk])
  refine ⟨hm, ?_⟩
  have := h2 hm
  simp only [adelicCharacterOfHidaSetting, ContinuousMulEquiv.apply_symm_apply] at this
  exact this.symm

theorem exists_rowJ_of_evalOn {R : RealDat D A Ks} {F : Face D A} {X : HidaSetting D}
    {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {G : GoodOp X} {t : GA D (D.sp.Y 0)} {v₀ : (MP R).Vec} {c : ℝ}
    {eE : D.what₂.EE →ₗ[ℂ] R.HE.H} (hc : 0 < c) (hv₀ : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) (hE : R.models_HE)
    (hrange : LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e)
    (hnorm : ∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) (hle : R.EEat (R.levR F true) ≤ R.EEat R.triv)
    (hJ2 : EvalOn R X h t v₀ c (EP R F) (EEC X G)) : ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  obtain ⟨J2, hJ2⟩ := hJ2
  obtain ⟨he_inj, he_range, he_ip⟩ := hE
  have hnP : 0 < RealDat.nP F true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have heE_inj : Function.Injective eE := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hnorm x
    rw [hx, norm_zero] at h1
    have h2 : RealDat.nP F true * ‖x‖ ^ 2 = 0 := by rw [← h1]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hnP.ne'
    · exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  have hmem : ∀ x, (R.HE.e ∘ₗ eE) x ∈ EP R F := fun x => by
    have : eE x ∈ (R.EEat (R.levR F true)).comap R.HE.e := hrange ▸ LinearMap.mem_range_self eE x
    exact this
  let k : D.what₂.EE →ₗ[ℂ] EP R F := LinearMap.codRestrict (EP R F) (R.HE.e ∘ₗ eE) hmem
  have hk : Function.Bijective k := by
    constructor
    · intro x y hxy
      exact heE_inj (he_inj (congrArg Subtype.val hxy))
    · rintro ⟨y, hy⟩
      have hy' : y ∈ LinearMap.range R.HE.e := he_range ▸ hle hy
      obtain ⟨z, rfl⟩ := hy'
      have hz : z ∈ LinearMap.range eE := by rw [hrange]; exact hy
      obtain ⟨x, rfl⟩ := hz
      exact ⟨x, rfl⟩
  let L : D.what₂.EE ≃ₗ[ℂ] EEC X G := (LinearEquiv.ofBijective k hk).trans J2
  have hLn : ∀ x, ‖L x‖ ^ 2 = (c * RealDat.nP F true) * ‖x‖ ^ 2 := by
    intro x
    have h1 := (hJ2 (k x)).2
    have h2 : ((k x : EP R F) : MMap (MP R)) = R.HE.e (eE x) := rfl
    have h3 : (ipM (MP R) R.ν0 R.fd0 (R.HE.e (eE x)) (R.HE.e (eE x))).re = ‖eE x‖ ^ 2 := by
      calc (ipM (MP R) R.ν0 R.fd0 (R.HE.e (eE x)) (R.HE.e (eE x))).re
          = (inner ℂ (eE x) (eE x)).re := by rw [he_ip]; rfl
        _ = ‖eE x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (eE x)
    show ‖((J2 (k x) : EEC X G) : L2X X)‖ ^ 2 = _
    rw [h1, h2, h3, hnorm x]
    ring
  set a : ℝ := (Real.sqrt (c * RealDat.nP F true))⁻¹ with ha_def
  have hs : 0 < Real.sqrt (c * RealDat.nP F true) := Real.sqrt_pos.mpr (mul_pos hc hnP)
  have ha : 0 < a := inv_pos.mpr hs
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G :=
    { toLinearEquiv := L.trans (LinearEquiv.smulOfNeZero ℂ (EEC X G) (a : ℂ) haC)
      norm_map' := fun x => by
        show ‖(a : ℂ) • L x‖ = ‖x‖
        have hL : ‖L x‖ = Real.sqrt (c * RealDat.nP F true) * ‖x‖ := by
          rw [← Real.sqrt_sq (norm_nonneg (L x)), hLn x, Real.sqrt_mul' _ (sq_nonneg _),
            Real.sqrt_sq (norm_nonneg x)]
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ha.le, hL, ← mul_assoc, ha_def,
          inv_mul_cancel₀ hs.ne', one_mul] }
  refine ⟨j, v₀, hv₀, a, ha, fun x => ?_⟩
  have h1 : ((j x : EEC X G) : L2X X) = (a : ℂ) • ((J2 (k x) : EEC X G) : L2X X) := rfl
  rw [h1]
  filter_upwards [Lp.coeFn_smul (a : ℂ) ((J2 (k x) : EEC X G) : L2X X), (hJ2 (k x)).1] with g h2 h3
  rw [h2, Pi.smul_apply, h3, smul_eq_mul]
  rfl

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.L2.Host NumberField IsDedekindDomain

def rowsEta {R : Ranks} (what₂ : Rows.Data R) (η : ℕ → what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w) : Rows.Data R :=
  { what₂ with etaJ := η, etaJ_nonneg := hη }

structure NLay0 (R : Ranks) (H : Host R) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) where
  loc : LocTheory
  locA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (loc l)
  locT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (loc l) (locA l)
  nd : NData R H what₂
  ntw : NTw R H what₂ LL0 nd
  naut : NAut nd
  nbc : NBC naut
  nexp : NExp R H what₂ LL0 nd ntw
  ntypes : NTypes naut
  nStage_trivialCharacter_compat : ntypes.IdempotentMatchesAction
  nStage_trivialCharacter_coeff_eq : ∀ g : G0g nd, what₂.embLL ((nexp.eLL0 g : ↥LL0) : what₂.LL) = ntypes.e0.coeff g
  nth : NTh R H what₂ LL0 nd ntw nexp
  nbr : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)), w ∈ Formalism.BasicNotions.placesOver H.E (nd.l i) →
    Formalism.BasicNotions.LocBridge (nd.l i) H.E nd.Om (ReciprocityTheory.Gal.Dec (F := H.E) (nd.plOm.1 w)) (nd.O i)
  nbr_ind : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (nd.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(nbr i w hw).j x‖ ≤ 1
  self_good : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (nd.l i)),
    Formalism.BasicNotions.Loc.GoodCoef H.condN (nbr i w hw).LL
  ntwbr : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 H.E)), w ∈ Formalism.BasicNotions.placesOver H.E (ntw.l i) →
    Formalism.BasicNotions.LocBridge (ntw.l i) H.E nd.Om (ReciprocityTheory.Gal.Dec (F := H.E) (nd.plOm.1 w)) (ntw.O0 i)
  ntwbr_ind : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (ntw.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(ntwbr i w hw).j x‖ ≤ 1
  loc_tie : Formalism.MainNotions.N.LocTie nd naut loc nbr
  bc_tie : Formalism.MainNotions.N.BcTie nd naut ntypes
  rbar_tie : Formalism.MainNotions.N.RbarTie nd naut ntypes
  mtpar_tie : Formalism.MainNotions.N.MtParTie nd naut ntypes

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    {LL0 : IntermediateField ℚ what₂.LL}

def NLay0.ZOk (L : NLay0 R H what₂ LL0) : Prop :=
  (∀ i x, x ∈ L.nd.Z i ↔ x ∈ Formalism.MainNotions.N.ZN L.nd L.naut i) ∧ ∀ i x, x ∈ L.nd.Zgood i ↔ x ∈ Formalism.MainNotions.N.ZgoodN L.nd L.naut i

def ndZ (N : NData R H what₂) (Z Zg : ∀ i, Finset (N.X i)) : NData R H what₂ := { N with Z := Z, Zgood := Zg }


set_option maxHeartbeats 2000000 in
def NLay0.setZ (L : NLay0 R H what₂ LL0) (Z Zg : ∀ i, Finset (L.nd.X i)) : NLay0 R H what₂ LL0 :=
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := ndZ L.nd Z Zg, ntw := { L.ntw with }, naut := { L.naut with }
    nbc := { L.nbc with }, nexp := { L.nexp with }, ntypes := { L.ntypes with }, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq
    nth := { L.nth with }, nbr := L.nbr, nbr_ind := L.nbr_ind, self_good := L.self_good, ntwbr := L.ntwbr
    ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie, rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie }


open Classical in
def NLay0.fixZ (L : NLay0 R H what₂ LL0) : NLay0 R H what₂ LL0 :=
  L.setZ (fun i => Finset.univ.filter fun x => x ∈ Formalism.MainNotions.N.ZN L.nd L.naut i)
    (fun i => Finset.univ.filter fun x => x ∈ Formalism.MainNotions.N.ZgoodN L.nd L.naut i)


set_option maxHeartbeats 2000000 in
def NLay0.reEta (L : NLay0 R H what₂ LL0) (η : ℕ → what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w) :
    @NLay0 R H (rowsEta what₂ η hη) ‹NumberField what₂.LL› ‹StarRing what₂.LL› LL0 :=
  letI : NumberField (rowsEta what₂ η hη).LL := ‹NumberField what₂.LL›
  letI : StarRing (rowsEta what₂ η hη).LL := ‹StarRing what₂.LL›
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := { L.nd with }, ntw := { L.ntw with }, naut := { L.naut with }
    nbc := { L.nbc with }, nexp := { L.nexp with }, ntypes := { L.ntypes with }, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq
    nth := { L.nth with }, nbr := L.nbr, nbr_ind := L.nbr_ind, self_good := L.self_good, ntwbr := L.ntwbr
    ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie, rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie }


open Classical in
def NLay0.eta (L : NLay0 R H what₂ LL0) (j : ℕ) (w : what₂.places.Pl) : ℚ :=
  if 1 ≤ j ∧ j ≤ R.m then ∑ i ∈ L.nd.locs j w, L.nd.etaLoc i else what₂.etaJ j w

theorem NLay0.eta_nonneg (L : NLay0 R H what₂ LL0) (j : ℕ) (w : what₂.places.Pl) : 0 ≤ L.eta j w := by
  unfold NLay0.eta
  split_ifs
  · exact Finset.sum_nonneg fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact what₂.etaJ_nonneg j w

theorem NLay0.zOk_fixZ (L : NLay0 R H what₂ LL0) : L.fixZ.ZOk := by
  classical
  refine ⟨fun i x => ?_, fun i x => ?_⟩
  · exact ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).trans (and_iff_right (Finset.mem_univ _)))
  · exact ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).trans (and_iff_right (Finset.mem_univ _)))

set_option maxHeartbeats 1000000 in
theorem NLay0.ZOk.reEta {L : NLay0 R H what₂ LL0} (h : L.ZOk) (η : ℕ → what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w) :
    @NLay0.ZOk R H (rowsEta what₂ η hη) ‹NumberField what₂.LL› ‹StarRing what₂.LL› LL0 (L.reEta η hη) := h

def NLay0.EtaOk (L : NLay0 R H what₂ LL0) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ R.m → what₂.etaJ j w = ∑ i ∈ L.nd.locs j w, L.nd.etaLoc i

set_option maxHeartbeats 1000000 in
theorem NLay0.etaOk_reEta (L : NLay0 R H what₂ LL0) :
    @NLay0.EtaOk R H (rowsEta what₂ L.eta L.eta_nonneg) ‹NumberField what₂.LL› ‹StarRing what₂.LL› LL0
      (L.reEta L.eta L.eta_nonneg) := fun _ _ h1 h2 => if_pos ⟨h1, h2⟩

end

abbrev Lay0 (D : D7) : Type _ := NLay0 D.R D.host D.what₂ D.LL0


set_option maxHeartbeats 1000000 in
def setRaw (D : D7) (η : ℕ → D.what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w)
    (P : @NLay0 D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0)
    (hZ : @NLay0.ZOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P)
    (hE : @NLay0.EtaOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P) : D7 :=
  letI : NumberField (rowsEta D.what₂ η hη).LL := D.nfLL
  letI : StarRing (rowsEta D.what₂ η hη).LL := D.starLL
  { D with
    what₂ := rowsEta D.what₂ η hη
    loc := P.loc, locA := P.locA, locT := P.locT, nd := P.nd, ntw := P.ntw, naut := P.naut, nbc := P.nbc, nexp := P.nexp
    ntypes := P.ntypes, nStage_trivialCharacter_compat := P.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := P.nStage_trivialCharacter_coeff_eq, nth := P.nth, nbr := P.nbr, nbr_ind := P.nbr_ind
    self_good := P.self_good, ntwbr := P.ntwbr, ntwbr_ind := P.ntwbr_ind, loc_tie := P.loc_tie, bc_tie := P.bc_tie
    rbar_tie := P.rbar_tie, mtpar_tie := P.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

def setN (D : D7) (L : Lay0 D) : D7 :=
  setRaw D L.fixZ.eta L.fixZ.eta_nonneg (L.fixZ.reEta L.fixZ.eta L.fixZ.eta_nonneg) (L.zOk_fixZ.reEta _ _) L.fixZ.etaOk_reEta

def setK (D : D7) (P : Lay0 D) (hZ : P.ZOk) (hE : P.EtaOk) : D7 :=
  { D with
    loc := P.loc, locA := P.locA, locT := P.locT, nd := P.nd, ntw := P.ntw, naut := P.naut, nbc := P.nbc, nexp := P.nexp
    ntypes := P.ntypes, nStage_trivialCharacter_compat := P.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := P.nStage_trivialCharacter_coeff_eq, nth := P.nth, nbr := P.nbr, nbr_ind := P.nbr_ind
    self_good := P.self_good, ntwbr := P.ntwbr, ntwbr_ind := P.ntwbr_ind, loc_tie := P.loc_tie, bc_tie := P.bc_tie
    rbar_tie := P.rbar_tie, mtpar_tie := P.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

def cfK {D : D7} (P : Lay0 D) (hZ : P.ZOk) (hE : P.EtaOk) (c : CharFrame D) : CharFrame (setK D P hZ hE) :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

def cfTr {D : D7} (L : Lay0 D) (c : CharFrame D) : CharFrame (setN D L) :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

def lay0 (D : D7) : Lay0 D :=
  { loc := D.loc, locA := D.locA, locT := D.locT, nd := D.nd, ntw := D.ntw, naut := D.naut, nbc := D.nbc, nexp := D.nexp
    ntypes := D.ntypes, nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq, nth := D.nth, nbr := D.nbr, nbr_ind := D.nbr_ind
    self_good := D.self_good, ntwbr := D.ntwbr, ntwbr_ind := D.ntwbr_ind, loc_tie := D.loc_tie, bc_tie := D.bc_tie
    rbar_tie := D.rbar_tie, mtpar_tie := D.mtpar_tie }

end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RefilledStagesRecord
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

structure SNew (D : D7) : Type 1 where
  s : Formalism.MainNotions.S.Draft.SData D.R D.host.F D.host.E D.conjF D.what₂.Word D.what₂.Tau D.hcW
  s_HH : Module.finrank ℂ s.HH = D.what₂.Dall
  s_Cu : ∀ u, s.Cu u ≃ₗ[ℂ] (D.mem u).A.Mu0
  s_PlF : s.PlF ≃ HeightOneSpectrum (𝓞 D.host.F)
  s_Cu_isom : ∀ u (x y : s.Cu u), inner ℂ x y =
    (D.fm u).ipC 0 ((s_Cu u x : (D.mem u).A.Mu0) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
      ((s_Cu u y : (D.mem u).A.Mu0) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
  sEE : D.what₂.EE →ₗᵢ⋆[ℂ] s.HH

def mix {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    {Word Tau : Type} {hc : Word → Tau → HCParam R} (s t : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc) :
    Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc :=
  { t with
    cdScale := s.cdScale, cdScale_pos := s.cdScale_pos, Del := s.Del, Del_pos := s.Del_pos, cloud_gap := s.cloud_gap
    letter := s.letter, letter_inj := s.letter_inj, u_letter := s.u_letter, atP := s.atP }

def reS (D : D7) (Z : SNew D) : D7 :=
  { D with
    s := mix D.s Z.s
    s_split := D.s_split
    s_HH := Z.s_HH
    s_Cu := Z.s_Cu
    s_PlF := Z.s_PlF
    s_Cu_isom := Z.s_Cu_isom
    sEE := Z.sEE }

def SNew.self (D : D7) : SNew D := ⟨D.s, D.s_HH, D.s_Cu, D.s_PlF, D.s_Cu_isom, D.sEE⟩

def reStage (X : Stages) (Z : SNew X.toD7) : SStage X.B X.C X.W where
  dsig := X.S.dsig
  dsig_pos := X.S.dsig_pos
  s := mix X.S.s Z.s
  s_split := X.S.s_split
  s_HH := Z.s_HH
  s_Cu := Z.s_Cu
  s_PlF := Z.s_PlF
  s_Cu_isom := Z.s_Cu_isom
  sEE := Z.sEE

section
variable (D : D7) (Z : SNew D)

end

end GlobalTheory.Mem.SRe

end
end
