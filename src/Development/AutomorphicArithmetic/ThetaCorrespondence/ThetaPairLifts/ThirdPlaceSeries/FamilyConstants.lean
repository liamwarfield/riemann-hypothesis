module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Formalism.LocalToGlobal.IndefiniteRealisationChoice

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (a : _root_.GlobalTheory.Fam.GeometricFamily W u)
structure FamilyConstants where
  ε : ℕ → a.ι → 𝓀[a.k]ˣ
  op : ∀ j, BiOp (D.sp.X j) (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1))
  r : ℕ → a.ι → ℝ
  e : ℕ → a.ι → ℤ
  cG : ℕ → ℂ
  sc : W.P.T → ℕ → ℂ
variable {a} (k : _root_.GlobalTheory.Fam.FamilyConstants a)
abbrev FamilyConstants.v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g) := (a.v.withT (a.o.S k.ε) k.op).withCG k.cG
variable {row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t} {col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))}
structure ColumnOutputCondition (w₀ w : ∀ t, VTup ((a.fam row col).t t))
    (F : ∀ t, GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) : Prop where
  ok : (a.fam row col).ColOK
  pins : ∀ t, (F t).Pins (w₀ t)
  same : ∀ t, (w t).Q = (w₀ t).Q ∧ (w t).eQ = (w₀ t).eQ ∧ (w t).eQT = (w₀ t).eQT ∧ (w t).cQ = (w₀ t).cQ ∧ (w t).FY = (w₀ t).FY ∧
    (w t).FT = (w₀ t).FT
  laws : ∀ t, QLaw a.v (w t) ∧ QLast a.v (w t) ∧ QFin a.v (w t)
  lev : ∀ t, _root_.GlobalTheory.Fam.QLevAlt (a.fam row col) (F t)
  vec : ∀ t, _root_.GlobalTheory.Fam.RationalVectorCondition (a.fam row col) (w₀ t)
  FY : ∀ t j f, f ∈ (w₀ t).FY j ↔ ∀ i, ((F t).Q i).Typed j f
  FT : ∀ t f, f ∈ (w₀ t).FT
  FX : ∀ t j, j + 2 ≤ D.R.m → ∀ ψ ∈ (col t).Ram j, ∀ α y, (col t).rd j α ψ y ∈ (w t).FX j α
  atQ : ∀ t j, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w₀ t).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w₀ t).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w t).dQ j α γ)
  e : ∀ t j α, (col t).e j α = ((w t).ε j α).mapDomain (· * a.g.b j) ∧
    ∀ g ∈ ((w t).ε j α).support, g ∈ GlobalTheory.FinPl.grpAt (Yc D j) (· ∈ (w₀ t).Q)
  eT : ∀ t n h β, (col t).eT n h β = ((w t).εT n h β).mapDomain (· * a.g.bT) ∧
    ∀ g ∈ ((w t).εT n h β).support, g ∈ GlobalTheory.FinPl.grpAt D.sp.X' (· ∈ (w₀ t).Q)
  dd : ∀ t j, j < D.R.m → ∀ α γ f, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ f → comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((col t).dd j α γ) f =
    comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((w t).dQ j α γ) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) f))
  read : ∀ t, ∃ S₀, ReadS a.o ((a.fam row col).t t) k.ε S₀
  sc : ∀ t, (w t).sc = k.sc t
  cT : ∀ t j ρ h, (w t).cT j = a.o.mono (k.r j) (k.e j) ((row t).sBF j ρ h).χW
  cv : ∀ t, CVEq k.v (w t)
  cK : ∀ t j, j < D.R.m → UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W t) ((col t).cK j) ((col W.P.A3.A.μ0).cK j)
  cP : ∀ t, UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W t) (col t).cP (col W.P.A3.A.μ0).cP
  zero : _root_.GlobalTheory.MiTop.ChartAtZeroCondition (a.fam row col)
end Gen
section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
def LevelCondition' (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg ∧ (∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ↔ PP ∈ (B.primes X).vGs) ∧ ∀ t, (_root_.GlobalTheory.Fam.pk_z W).xiH t = I.xi (W.P.I.tup t)
structure AllFamilyConditions (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop where
  pk : _root_.GlobalTheory.Fam.PackageHypotheses W
  tr : _root_.GlobalTheory.Fam.ValidRealPackage W
  tq : _root_.GlobalTheory.Fam.GeometricFamilyConditions W
  tw : _root_.GlobalTheory.AdForm.TwStdAlt W
  lev : _root_.GlobalTheory.Fam.LevelCondition' W
  rc : Nonempty (_root_.Formalism.IndefR.IndefiniteRealisationRecursion W.Q)
end True
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
abbrev chrK_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (j : ℕ) : (AE (I.rec7 l Z))ˣ →* Circle := (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1)
set_option maxHeartbeats 1000000 in
structure QuadraticExtensionData (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (t : W.P.T) where
  Ch₀ : ℕ → Type
  A : TwDat I l Z u (W.P.I.tup t) Ch₀
  r : ℕ
  pl : Fin r → Pl (I.rec7 l Z).host.E
  mem : ∀ i, pl i ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t
  E : ∀ i, QExt (a.Q (pl i) ⟨t, mem i⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)
  P : Fin r → BadPr I (W.P.I.tup t)
  hψ : ∀ i, Continuous (a.Q (pl i) ⟨t, mem i⟩).ψk
  sg : Fin r → ℂ
  π : ∀ i j, Ch₀ j → (E i).Ch j
  ι : ∀ j, (∀ i, (E i).Ch j) → Ch₀ j
variable {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t)
abbrev QuadraticExtensionData.G (i : Fin J.r) := a.Q (J.pl i) ⟨t, J.mem i⟩
abbrev QuadraticExtensionData.Ch (j : ℕ) : Type := ∀ i, (J.E i).Ch j
def QuadraticExtensionData.wt (j : ℕ) (α : J.Ch j) : ℂ := ∏ i, (J.E i).wt j (α i)
def QuadraticExtensionData.dQ (s : ∀ j, J.Ch j → ℂ) (j : ℕ) (α : J.Ch j) (γ : J.Ch (j + 1)) :
    WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ :=
  (s j α * (s (j + 1) γ)⁻¹) • (J.wt j α • aconv (List.ofFn fun i => (J.E i).dL j (α i) (γ i)))
structure QuadraticExtensionData.Reads : Prop where
  is : J.A.Is
  inj : Function.Injective J.pl
  surj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, J.pl i = PP
  chr : ∀ j, j < B.R.m → J.A.chr (j + 1) = _root_.GlobalTheory.Fam.chrK_alt W t j
  res : ∀ i, (J.G i).Res (J.E i).δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t (J.pl i))
  eq : ∀ i, (J.P i).1 = J.pl i
  sg : ∀ i, J.sg i = 1 ∨ J.sg i = -1
  tw : ∀ i, GlobalTheory.TwBridge.AtTwist (R := B.R) (k := (J.G i).k) I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
    ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i))
  M : ∀ i, (J.E i).M = (I.cst (W.P.I.tup t)).M
  rep : ∀ i j d (h : j + d = (J.G i).s) (hj : j < B.R.m) β,
    GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := (J.G i).k) ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) ((J.E i).rep j d h (J.π i j β))
  cos : ∀ i β (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → (J.E i).cos (J.π i ((J.G i).s + 1) β) =
      Submodule.Quotient.mk fun r => (ofSplit (J.G i).q).pr (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2 (e r))
  std : ∀ j, j + 1 < B.R.m → ∀ β, J.A.kb j β = TC.kStd X u (B.R.N j)
  pen : ∀ j (hj : j + 1 = B.R.m) β, ∃ k₀ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j),
    k₀ ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) k₀ = (TC.kStd X u (B.R.N j)).1 ∧ J.A.kA j β = k₀ * h ∧
    h ∈ GlobalTheory.FinPl.grpAt _ (fun p => ∃ i, (J.G i).q.v = p) ∧
    ∀ i (e : (J.G i).s + 1 = j), ∃ g ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J,
      (mt _ (e ▸ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1)))).map (J.G i).q.pr =
        ((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁ * ((J.G i).FX ((J.G i).s + 1) le_rfl).γ
  last : Nonempty (Unique (J.Ch₀ B.R.m))
  sec : ∀ j, j ≤ B.R.m → ∀ y i, J.π i j (J.ι j y) = y i
  cosG : ∀ (n : Fin a.n) y (e : XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ r,
      (ofSplit (a.G n).q).pr (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ y)).1.2 (e r)) - (a.G n).S.y0 (Fin B.R.t) r ∈ 𝒪[(a.G n).k]
  live : J.A.Live J.ι
def QuadraticExtensionData.Vol (V : ℕ → ℂ) : Prop :=
  ∀ j, j < B.R.m → ∀ α, (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = V j
def QuadraticExtensionData.Dat (C : ℕ → ℂ) (s : ∀ j, J.Ch j → ℂ) (ζ : ∀ j, J.Ch j → J.Ch (j + 1) → ℂ) (ρ : ℕ → ℂ) : Prop :=
  (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) ∧ (∀ α, s 0 α = 1) ∧ (∀ j, ∃ n : ℕ, 0 < n ∧ ρ j ^ n = 1) ∧
    ∀ j (hj : j + 1 ≤ B.R.m) α γ,
      IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ J.A.e (fun z => C j * J.wt j α * ζ j α γ * J.A.xi j hj (J.ι j α) (J.ι (j + 1) γ) z) (a.g.vac j)
        (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (J.dQ s j α γ) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)))) ∧
      ζ j α γ * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ) * (J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ)⁻¹ = ρ j
def QuadraticExtensionData.VolT (VT : ℂ) : Prop :=
  ∃ UT : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'),
    (∀ h, h ∈ UT ↔ a.g.bT⁻¹ * h * a.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) ∧
    ∀ β, (GlobalTheory.SeeSaw.volLev a.g.volT UT : ℂ) * J.wt B.R.m β = VT
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
namespace GlobalTheory.CovTop.Sizes
theorem hostN_alt : ∀ M : ℝ, _root_.GlobalTheory.CovTop.HostNAlt M := by
  intro M
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := eventually_scale he (22 + |Fm.Ct|) M
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 5)
  refine ⟨22 + |Fm.Ct|, by positivity, max x0 x2, fun x hx hle ι p _ _ => ?_⟩
  obtain ⟨a1, a2, a3, a4, -, a6⟩ := hx0 x ((le_max_left _ _).trans hle)
  have a5 : 5 ≤ x ^ (Fm.ez / 5) := hx2 x ((le_max_right _ _).trans hle)
  have hsz : (Fm.L x ι).sc.ez = Fm.ez := Fm.toFamCore.L_ez x ι
  have hsx : (Fm.L x ι).sc.x = x := Fm.L_x x ι hx
  have hse : (Fm.L x ι).sc.eps = eps := Fm.L_eps x ι
  have hsL : (Fm.L x ι).sc.L = x ^ eps := by unfold Scale.L; rw [hsx, hse]
  have hg : ∀ k, Real.log ((Fm.D x ι).host.g k) ≤ 9 * (Fm.L x ι).sc.L + 1 := fun k => by
    have hlo : 0 < ((((Fm.D x ι).host.g k : ℕ)) : ℝ) := by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
    have := (Real.log_le_iff_le_exp hlo).2 ((hF.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1 k)
    linarith
  refine hostNum_of_sizes (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) hg ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Fm.Ct_eq]; linarith [le_abs_self Fm.Ct]
  · rwa [hsL]
  · rwa [hsL]
  · rwa [hsx]
  · unfold Scale.b; rwa [hsL, hsx]
  · rwa [hsx, hsz]
  · rwa [hsx]
end GlobalTheory.CovTop.Sizes
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostNStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostN_forall : ∀ M : ℝ, _root_.GlobalTheory.CovTop.HostNAlt M := by
  first | exact @_root_.GlobalTheory.CovTop.Sizes.hostN_alt | exact _root_.GlobalTheory.CovTop.Sizes.hostN_alt | (intros; apply _root_.GlobalTheory.CovTop.Sizes.hostN_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.WtShape
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem wtN_z : _root_.GlobalTheory.CovTop.LiftWeightNumerator := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, le_rfl, max 8 ((3 : ℝ) ^ (4 / eps)), fun x hx hle ι p _ i => ?_⟩⟩⟩
  refine wtNum_at p i (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) ?_ ?_
  · rw [Fm.L_x x ι hx]; exact (le_max_left _ _).trans hle
  · rw [Fm.L_x x ι hx, Fm.L_eps x ι]
    have h3 : ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) = 3 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 4 / eps * (eps / 4) = 1 := by field_simp
      rw [this, Real.rpow_one]
    calc (3 : ℝ) = ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) := h3.symm
      _ ≤ x ^ (eps / 4) := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hle) (by positivity)
end GlobalTheory.CovTop.WtShape
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_weight_numerator : _root_.GlobalTheory.CovTop.LiftWeightNumerator := by
  first | exact @_root_.GlobalTheory.CovTop.WtShape.wtN_z | exact _root_.GlobalTheory.CovTop.WtShape.wtN_z | (intros; apply _root_.GlobalTheory.CovTop.WtShape.wtN_z <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top
namespace GlobalTheory.Cp
section Cls
open Formalism.MainNotions.Pk
end Cls
section IndefiniteRowSideFullHecke
open _root_.Formalism _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Rows _root_.Formalism.L2.Indef NumberField IsDedekindDomain
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
end IndefiniteRowSideFullHecke
section At
open _root_.Formalism
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : _root_.Formalism.L2.RecTAlt ex} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
structure IndefiniteRealisationConstantBounds (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (C CH : ℝ) (hN hO : Prop) : Prop where
  w1 : ∀ w, (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w → w ∈ Q.Rl.twPl
  covol : ((Q.Rl.toCx3 Q.F).data Q.F.cr false).L3 (Q.Rl.num Q.F C CH)
  onto : hN → ((Q.Rl.toCx3 Q.F).data Q.F.cr false).ON (Q.Rl.num Q.F C CH)
  lamLow : hO → ((Q.Rl.toCx3 Q.F).data Q.F.cr true).L6 (Q.Rl.num Q.F C CH)
  seeIso : (Q.Rl.toCx3 Q.F).SEEIso Q.sEE
  miStar : (Q.Rl.toCx3 Q.F).MIstar2 (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE
  fun0 : hN → ((Q.Rl.toCx3 Q.F).data Q.F.cr false).FUN (Q.Rl.num Q.F C CH)
  pass : Formalism.IndefR.Links.PassIn3 Q.Rl Q.F C CH
  kap : Formalism.L2.Rows.RowsHoldKap3 P
end At
section Serv
open Formalism.MainNotions.Pk _root_.Formalism.L2
structure SelectionServed (𝒞 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒞) : Prop where
  twU : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ LC, WeilJacquetShalikaLaw.CmpV (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw (reW (Fm.Gy x i) LC) ∧ SysTw (Fm.D x i) (Fm.L x i)
      (Fm.Gx x i) Fm.GK (Fm.X x i) (reW (Fm.Gy x i) LC) (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err 1
  pdv : Closed 𝒞 fun Fm _ => ∀ (hc : 𝒞 Fm) (x : ℝ) (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    ((((sel Fm hc).2 x hx h0 i).T.ker.ent.UnUnit ∧ OrbitPlaces.KmapRat ((sel Fm hc).2 x hx h0 i).T.ker.ent ∧
        OrbitPlaces.KFi (Fm.D x i) (Fm.ex x hx i).tw ∧ OrbitPlaces.Stab0 (Fm.D x i)) ∧
      ∃ (ep : _) (be : _) (sg : _),
        OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.Gx x i) Fm.GK ∧
        OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i)
          (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg))
end Serv
end GlobalTheory.Cp
namespace GlobalTheory.Fc.R1
open GlobalTheory.Fc GlobalTheory.Cp
def P_hRB_alt : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows b.B
def SlotRowBoundCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.P_hRB_alt)
def TwistBundleCondition : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  Formalism.L2.DIV.TieTwRec O.L b.P.S0.Tw
def SlotTwistCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.TwistBundleCondition)
def PrimitivityBundleCondition : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3
def SlotPrimitivityCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition)
def LambdaPrimeBundleCondition : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  Formalism.L2.Rows.RowsHoldLam3 b.P
def SlotLambdaPrimeCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.LambdaPrimeBundleCondition)
def DivisorBundleCondition : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  DivRows3G b.P
def SlotDivisorCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.DivisorBundleCondition)
def DecompositionPointBundle : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  DcPtG b.P
def SlotDecompositionPointCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.DecompositionPointBundle)
def SelectionJumpBundleCondition : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin (R := b.R) (S := b.S) (Q := b.B.Q))
def SlotSelectionJumpCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.SelectionJumpBundleCondition)
def LeafUniqueMap {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : Prop :=
  ∀ j, Formalism.IndefR.FWT.OneMapRowR b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ b.B.O (Formalism.IndefR.phEff b.B.Q.Rl) j
abbrev DefiniteSideType : Type 1 := ∀ (D : D7) (O : Obj D) (c : ℝ), _root_.GlobalTheory.Fc.BundleCondition D O c → ℝ → ℝ → Prop
def SelectionDefiniteRows (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Prop :=
  Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, ∃ C : ℝ, 0 ≤ C ∧ _root_.GlobalTheory.Cp.EventuallyAlongSelection (_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc) fun x hx _ i =>
    _root_.GlobalTheory.Cp.IndefiniteRealisationConstantBounds (σ Fm (d3_a hc) x hx i).B.Q C CH (DIVinN Fm) (_root_.GlobalTheory.Fc.R1.LeafUniqueMap (σ Fm (d3_a hc) x hx i)) ∧ DR _ _ _ (σ Fm (d3_a hc) x hx i) C CH
def SlotDefiniteRowsCondition (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (_root_.GlobalTheory.Fc.R1.SelectionDefiniteRows DR)
def SelectionLpBound (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Prop :=
  Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨((_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)).1, fun x hx h i => ((_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) Fm (d3_a hc) x hx h i).toSTies⟩)
def SlotLpCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (_root_.GlobalTheory.Fc.R1.SelectionLpBound)
def SelectionOrderBound (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Prop :=
  Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨((_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)).1, fun x hx h i => ((_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) Fm (d3_a hc) x hx h i).toSTies⟩
def SlotOrderCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (_root_.GlobalTheory.Fc.R1.SelectionOrderBound)
def SelectionServesFamily (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Prop :=
  _root_.GlobalTheory.Cp.SelectionServed (D3 3 𝒜) fun Fm hc => (_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)
def SlotServiceCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (_root_.GlobalTheory.Fc.R1.SelectionServesFamily)
def SelectionZeroLocus (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Prop :=
  Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : ((_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.A3.A ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.P0
          ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.ψ0 (((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.Zs) k
          ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec
def SlotZeroLocusCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (_root_.GlobalTheory.Fc.R1.SelectionZeroLocus)
def SlotTorsionFreeCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk fun 𝒜 _ => H_hTF 𝒜
def CountsIrreducibilityConstants' (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := ∃ (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants) (cIc : ℝ),
  (∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A) ∧ 0 < cIc ∧
  Row Q Lk fun 𝒜 _ => (Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb) ∧
    (Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f))
def SlotNormCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) (N : FamClass → Prop) : Prop := Row Q Lk fun 𝒜 _ => N (D3 3 𝒜)
end GlobalTheory.Fc.R1
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ)
def extensionWithList : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c ×
  PLift (ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep K.s.b)
def SettingsFormsExistList' : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x') ∧ ListSt cDep x'
def SeriesExistList' : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x') ∧ (ListSt cDep x → ListSt cDep x')
def ModuliPointsExistList' : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x') ∧ (ListSt cDep x → ListSt cDep x')
def FinitenessListStatement : Prop := AllSt fun K _ _ _ w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (S : SExt) (Γ : GeoP), ListSt cDep x →
  ∃ (Z : w.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch
end GlobalTheory.HeightCounting.Up
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB
namespace GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {O : Obj D} {c : ℝ}
def BundleCondition.TiePins (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion b.B.Q) : Prop :=
  PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG ∧ _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree b.B.Q ∧ ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q, _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr
abbrev BundleCondition.Comparison₂ (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : Type 1 := {Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion b.B.Q // b.TiePins Rr}
theorem BundleCondition.Comparison₂.psi {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG := t.2.1
theorem BundleCondition.Comparison₂.pins3 {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree b.B.Q := t.2.2.1
theorem BundleCondition.Comparison₂.pins {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := let ⟨h, _⟩ := t.2.2.2; h
theorem BundleCondition.Comparison₂.recPins {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationCompatible t.pins t.1 := let ⟨_, h⟩ := t.2.2.2; h
@[reducible] def BundleCondition.part (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (t : b.Comparison₂) : _root_.GlobalTheory.Fc.Ind.PointSummands D O c where
  R := b.R
  S := b.S
  P := b.P
  pin := b.pin
  DH := b.DH
  Dcf := b.C.c.face
  Spf := b.C.Sp
  ok1 := b.C.ok1
  B := b.B
  Rr := t.1
  psi := t.psi
  pins := t.pins
  muDef := t.pins3.muDef
  recPins := t.recPins
end Point
def HasCompatibility : BdP _root_.GlobalTheory.Fc.BundleCondition := fun _ _ _ b => Nonempty b.Comparison₂
section Sel
variable {𝒜 : FamClass}
abbrev CompatibleSelection (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Type 1 :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), (σ Fm hc x hx i).Comparison₂
def summandSelection (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) (τ : _root_.GlobalTheory.Fc.CompatibleSelection σ) : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜 :=
  fun Fm hc x hx i => (σ Fm hc x hx i).part (τ Fm hc x hx i)
end Sel
section Construction₂
end Construction₂
end GlobalTheory.Fc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def SizeAtAlt : Prop := Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows (Fm.L x i)
def SettingAtPoint : Prop := Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i p =>
  GlobalTheory.GLq.ESerTie (Fm.D x i) → HidaSetting (Fm.L x i) p.R.toRealDat p.F.lv2
def CharacterAtPoint (Q : ChP) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p =>
  ∀ (G : Grid p CF) (W : G.Weil) (n : ℕ) (a : SlopeTestRemainingChoices p G W n), a.OK → Q a.ch
theorem SettingAtPoint.atPt (h : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint) {Q : ChP} (hQ : Big Q) : _root_.GlobalTheory.BigTop.Fun.CharacterAtPoint Q := by
  obtain ⟨c, hQ⟩ := hQ
  refine ⟨c, fun CF hCF => h.imp fun {eps} Fm _ _ a => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hQ eps CF hCF
  obtain ⟨x₁, a⟩ := a
  refine ⟨max x₀ x₁, fun x hx hle i p hp G W n b hb => ?_⟩
  exact hx₀ _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _
    (a x hx (le_of_max_le_right hle) i p hp hb.eser) b.ch hb.is b.atScale
end GlobalTheory.BigTop.Fun
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
def PlacedAlt : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
    (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg),
    f.c.Is ∧ v.Is ∧ _root_.GlobalTheory.Fam.CommutingVectorTie f v ∧ ShapeOff v o ∧ GPin G ∧ _root_.GlobalTheory.Fam.LocalGroupReading f G pl ∧ _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G
def translationElement (a₀ a : GA D (D.sp.X 0)) : GA D (D.sp.Y 0) :=
  ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0)
def IsTranslate' (a₀ a : GA D (D.sp.X 0)) : Prop :=
  IsTransportAdelicCorrection (W.S.tr u) a₀ ∧ a ∈ GfC (D.sp.X 0) ∧ a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧
    Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeHasSmallGenerators
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
def ReadInjAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ), ν ≠ 0 →
  Function.Injective (rdAt p w j hρ ν)
def LatticeHasSmallGenerators : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw), ρ.Good → RealPin p.R p.cG ρ →
  ∀ (h : GA (Fm.D x i) (Vc (Fm.D x i) j)) (P : PolF (Fm.D x i) (Wc (Fm.D x i) j).rank (Vc (Fm.D x i) j).rank),
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
      (ρ.eO ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w)).range h →
    P ∈ Submodule.span (ρ.eO ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w)).range
      (ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h :
        Set (PolF (Fm.D x i) (Wc (Fm.D x i) j).rank (Vc (Fm.D x i) j).rank))
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefiniteRealisationChoice
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTP
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
namespace RealT
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks)
theorem _root_.Formalism.IndefR.IndefiniteRealisation.rows_transport {Z Z' : DefSub P.A3.fam3.amb3} (h : Z = Z') (R0 : IndefRows (P.A3.side3 P.P0 P.ψ0 Z))
    (S : IndefData (P.A3.side3 P.P0 P.ψ0 Z')) (hS : HEq R0.toIndefData S) :
    ∃ R0' : IndefRows (P.A3.side3 P.P0 P.ψ0 Z'), R0'.toIndefData = S := by
  subst h
  exact ⟨R0, eq_of_heq hS⟩
theorem _root_.Formalism.IndefR.IndefiniteRealisation.rowsHold0 {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (hP : PrimRows3 R.Rl R.F) :
    RowsHold0_3 P := by
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hsep R.charW hP
  refine ⟨R.zs ▸ hR.stable, R.zs ▸ hR.inBlock, ?_, ⟨s, hOk⟩, hsep⟩
  exact _root_.Formalism.IndefR.IndefiniteRealisation.rows_transport R.zs (primRows3 hOk hsep R.Rl R.F R.charW hP) P.S0 (by
    rw [primRows3_data]
    exact R.s0)
end RealT
end Formalism.IndefR
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
namespace Formalism.L2.Top4
open Formalism.L2.Top3
abbrev BaseLevelTiedChoiceAlt (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {P : Formalism.L2.Rows.RowSideFamily (Fm.ex x hx i) // _root_.Formalism.L2.Rows.RowSideDeterminedAlt ((sel Fm hc).2 x hx h i).T P}
section SelTieS
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
end SelTieS
abbrev ColumnChoiceCompatibleSelection (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.L2.DIV.SquareIntegrableColumns ((sel Fm hc).2 x hx h i).T (selP Fm hc x hx h i).1
abbrev SelectionSpectralCondition (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt ((sel Fm hc).2 x hx h i)
def IndefiniteScaleAtPoint {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) :
    Formalism.L2.Indef.DefSub (selP Fm hc x hx h i).1.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale (selP Fm hc x hx h i).1.A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2) (Equiv.refl _) (Fm.L x i).Nc Zs
    { z with l6m := fun j => z.l6m j - Fm.Csz * z.l6u, l6u := 0 }
abbrev KernelSelection (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), KsChoice (Fm.D x i)
abbrev IndefiniteRealisationChoice' (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel) (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP) (selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.IndefR.IndefiniteRealisation ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i) (selK Fm hc x hx h i).Ks
def AllRealisationsPrimitive {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
    {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel} (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.IndefR.Links.PrimRows3 (selI Fm hc x hx h i).Rl (selI Fm hc x hx h i).F ∧ (selP Fm hc x hx h i).1.A3.fam3.TypesSep3
theorem selP_condition_zero_of_primAll {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
    {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel} {selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK} (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel selI)
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) :
    Formalism.L2.Rows.RowsHold0_3 (selP Fm hc x hx h i).1 := by
  obtain ⟨hP, hsep⟩ := hPA Fm hc x hx h i
  exact (selI Fm hc x hx h i).rowsHold0 (selC Fm hc x hx h i).ok1 hsep hP
def RankOfDivisionKernel {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel) (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel) (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel) (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel selI) :
    ∀ {eps : ℝ} (Fm : FamP eps), D3 3 𝒜 Fm →
      Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.DIV.DivisionKernelData (Fm.ex x hx i) :=
  fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i =>
    (selC Fm (d3_a hc) x hx h i).toK (_root_.Formalism.L2.Top4.selP_condition_zero_of_primAll hPA Fm (d3_a hc) x hx h i) (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm (d3_a hc) x hx h i)⟩
def EventuallyAlongSelection {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x), x0 ≤ x → ∀ i : Fm.Ix x, Q x hx h i
section At
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : _root_.Formalism.L2.RecTAlt ex} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
structure IndefiniteRealisationConstantBounds (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (C CH : ℝ) (hN hO : Prop) : Prop where
  w1 : ∀ w, (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w → w ∈ Q.Rl.twPl
  covol : ((Q.Rl.toCx3 Q.F).data Q.F.cr false).L3 (Q.Rl.num Q.F C CH)
  onto : hN → ((Q.Rl.toCx3 Q.F).data Q.F.cr false).ON (Q.Rl.num Q.F C CH)
  lamLow : hO → ((Q.Rl.toCx3 Q.F).data Q.F.cr true).L6 (Q.Rl.num Q.F C CH)
  seeIso : (Q.Rl.toCx3 Q.F).SEEIso Q.sEE
  miStar : (Q.Rl.toCx3 Q.F).MIstar2 (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE
  fun0 : hN → ((Q.Rl.toCx3 Q.F).data Q.F.cr false).FUN (Q.Rl.num Q.F C CH)
  pass : Formalism.IndefR.Links.PassIn3 Q.Rl Q.F C CH
  kap : Formalism.L2.Rows.RowsHoldKap3 P
end At
def RowsAtSelAlt {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
    {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel} (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK)
    (DefRows4 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) (C CH : ℝ), Prop)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (CH : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc fun x hx h i =>
    _root_.Formalism.L2.Top4.IndefiniteRealisationConstantBounds (selI Fm hc x hx h i) C CH (DIVinN Fm) (OneMapRow Fm hc x hx h i) ∧ DefRows4 Fm hc x hx h i C CH
def Wire4Alt {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel) (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel) (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP) (selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel)
    (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel selI)
    (DefRows4 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) (C CH : ℝ), Prop)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    (Cabs : ℝ) : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : D3 3 𝒜 Fm) (CH : ℝ), 0 ≤ Fm.Csz → DGamSize Fm →
    _root_.Formalism.L2.Top4.RowsAtSelAlt sel selI DefRows4 OneMapRow Fm (d3_a hc) CH → _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm (d3_a hc) (OneMapRow Fm (d3_a hc)) →
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational) → DIVinN Fm →
    ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : (_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC selK selI hPA Fm hc).1 ≤ x) (i : Fm.Ix x),
      Nonempty (_root_.Formalism.L2.DIV.DivisionPackageKernel' ((_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC selK selI hPA Fm hc).2 x hx h i) C Cabs)
open Formalism.L2.DIV in
theorem RemainingDivisionBounds.toRows_alt {eps : ℝ} {Fm : FamP eps} {Rt : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.DIV.DivisionKernelData (Fm.ex x hx i)}
    {Cabs CH : ℝ} (r : RemainingDivisionBounds Fm Cabs CH)
    (pkg : DIVinN Fm → ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Rt.1 ≤ x) (i : Fm.Ix x), Nonempty (_root_.Formalism.L2.DIV.DivisionPackageKernel' (Rt.2 x hx h i) C Cabs))
    (cut : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ μ, Formalism.BasicNotions.DV.Used (Fm.D x i) μ → Formalism.L2.G.ServJoint.CutUp (Fm.D x i) μ)
    (a : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i))
    (c2 : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm) (c5 : Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm) :
    _root_.Formalism.L2.DIV.DivisionKernelConstantBounds Fm Rt Cabs CH := by
  refine {
    pkg := pkg
    adm2 := ?_
    cut := cut
    c3 := Formalism.MainNotions.DIV.HookProducts.RBCompl3.rbCompl3 Fm
    hh := r.hh c2
    c2 := c2
    c5 := c5
    bu := r.bu
    rr := r.rr
    la := r.la }
  obtain ⟨x0, a⟩ := a
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i => a x (le_trans (le_max_left _ _) hx) ?_ i⟩
  have := le_trans (le_max_right _ _) hx
  linarith
end Formalism.L2.Top4
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem lowAt_holds_alt : _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  refine ⟨0, fun x hx _ i p hp _ w _ _ P hP => ?_⟩
  obtain ⟨Rc, -⟩ := hp.ties.real
  exact GlobalTheory.TwInputs.JoinModel.low_of_tied Rc.T.toTiedDataS.n.tw (GlobalTheory.TwInputs.JoinModel.q_dvd_discr _) _ P hP
end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.MiS
namespace GlobalTheory.Fam
@[reducible] def packB_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : _root_.GlobalTheory.MiS.RealPackAlt O.ex :=
  letI := b.B.alg
  { R := b.R, S := b.S, P := b.P, Dcf := b.C.c.face, Spf := b.C.Sp, Zscf := GlobalTheory.Fc.zsc b.P b.DH.1.1 b.DH.1.2 c,
    Ks := b.B.T.Q.c.F, Q := b.B.Q }
structure BundlePointConditions {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : Prop where
  join : Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S b.B.Q)
  dc : DcPtG b.P
  frames : _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx b.B.Q
  see : _root_.Formalism.IndefR.IndefiniteRealisationExtends b.B.Q
  ex : b.B.Q.Rl.toRealDat.ExAt
  prim : Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3
  fin : Formalism.L2.SG.PackageTie2.FinX b.S.Y
  gapS : GlobalTheory.Count.GapGe b.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  gap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D
  rS : 1 ≤ D.R.rS
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdm
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp.TwAdmProof
end GlobalTheory.BigOn.Exp.TwAdmProof
namespace GlobalTheory.BigOn.Exp.TwAdmProof
variable {D : D7}
end GlobalTheory.BigOn.Exp.TwAdmProof
namespace GlobalTheory.BigOn.Exp.TwAdmProof
variable {D : D7}
end GlobalTheory.BigOn.Exp.TwAdmProof
open GlobalTheory.BigOn.Exp.TwAdmProof in
theorem GlobalTheory.BigOn.Exp.twAdm_alt : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.TwAdmAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p hR _ w hw _ => ?_⟩⟩
  have hmu := (p.tw_iff w).1 hw
  obtain ⟨-, N0, S, hG⟩ := hR.ties.twist
  obtain ⟨-, hall⟩ := hG w hmu
  have h1 := hall 1 (by simp)
  rw [zpow_one] at h1
  have hpsi := h1.1
  refine ⟨?_, ?_, GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice _ _ (Fm.ex x hx i).nch_tie (Fm.ties x i).baseField_isGalois w hmu⟩
  · have h2 := Formalism.MainNotions.IntegralHeckeForms.TwOK_psiAt ((Fm.ex x hx i).nch.sd w) (Formalism.MainNotions.IntegralHeckeForms.TwOK_of_PsiOk hpsi)
    rw [psiAt_comp, Formalism.MainNotions.psiAt_psiAt] at h2
    exact h2
  · intro P hP
    obtain ⟨-, hin, he⟩ := hpsi.1 P hP
    exact exists_splitK_of P hin he
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmbeddingAtLocalFactor
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
noncomputable section
namespace GlobalTheory.Fam.TopLoc
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
def embeddingAtLocalFactor (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (n : Fin a.n) : B.fields.E →+* (a.G n).k := (a.G n).q.pr.comp (incA (I.rec7 l Z))
def standardXi (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (n : Fin a.n)
    (z : Matrix (Fin ((I.rec7 l Z).sp.X ((a.G n).s + 1 + 1)).rank) (Fin ((I.rec7 l Z).sp.X ((a.G n).s + 1)).rank) (I.rec7 l Z).host.E) : ℂ :=
  ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1)
    (Submodule.Quotient.mk ((a.G n).S.y0 (Fin B.R.t)))
    ((a.G n).FM.γ * z.map (ofSplit (a.G n).q).pr * ((a.G n).FX ((a.G n).s + 1) le_rfl).β)
end GlobalTheory.Fam.TopLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KeepsPairs
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace
variable {D : D7} {c : Comm D} {v : VCom c}
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
def KeepsPairsAlt (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (κ : GA D (D.sp.X 0)) : Prop :=
  ∀ i (g : GL (Fin (D.sp.X 0).rank) a.k), (mt (D.sp.X 0) κ).map (a.o.p i).pr = (a.o.β 0 i).b * g.val * (a.o.β 0 i).b' →
    g • a.o.Q 0 i = a.o.Q 0 i
def TraceAtElement (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (κ : GA D (D.sp.X 0)) : Prop :=
  ∀ i g, IsMatrixInFrameOfXZero (a.G i) κ g → GlobalTheory.RootEx.embX ((a.G i).s + 1) g ∈ (((a.G i).S.T (Fin D.R.t)).lev 0 ((a.G i).s + 1) (Nat.zero_add _)).J
def InLevelGroup (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (κ : GA D (D.sp.X 0)) : Prop :=
  GlobalTheory.FinPl.Moves (D.sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => True) ∧ _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ ∧ _root_.GlobalTheory.FamTrace.TraceAtElement a κ
def LevelAtElement (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (x : GA D (Yc D 0)) : Prop :=
  ∀ i m, (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m → m ∈ (((a.G i).S.T (Fin D.R.t)).lev 0 ((a.G i).s + 1) (Nat.zero_add _)).J
def InLevelGroupOfY (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (x : GA D (Yc D 0)) : Prop :=
  GlobalTheory.FinPl.Moves (Yc D 0) x (a.v.N 0) (a.v.N 0) (fun p => p ∉ a.v.gP) ∧ _root_.GlobalTheory.FamTrace.LevelAtElement a x
end GlobalTheory.FamTrace
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
end Point
def KerOfAtAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => KerOf p w j
def TraceAt' : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => TraceOf p w j
def KernelRationalAt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => KerRat p w j
def LatticeInclusionAt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => LatIo p w j
def ReadComparisonAt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => ReadCmp p w j
end GlobalTheory.BigOn.Exp.SerBase
end
end
end
