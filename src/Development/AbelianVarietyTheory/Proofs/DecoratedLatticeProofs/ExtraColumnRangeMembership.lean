module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementProperty
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFramesNormalAtLevelPlacesOfCharFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheorems
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralAdaptedElement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairProperty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraColumnRangeMembership
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopStep

open GlobalTheory.Fam.Inhab GlobalTheory.Fam.FamInhab

section
variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ)

theorem lift_lev_pt (hl : R.toLevCh.Is A.μ0) (hθ : IsInfFam R.θ) (t : T) (k : ℕ) (hk : k < D.R.m) {V : HSp D} (hV : V.SigOK)
    (hr : V.rank = D.R.r + (k + 1) * D.R.t) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)} {N : ℕ} (hβ : IsSDFrame V β Λ N)
    {om : Om (Yc D k) V} (hom : IsWeilDatumO R.ψ (Yc D k) V (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 om) {f₀ f f' : WO (Yc D k) V → ℂ}
    (hf : IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (R.ΛY k) Λ (R.βY k) β (R.datYt t k R.triv) (R.chi (k + 1))
      (R.Q t) (R.xiR t) f₀ f)
    (hf' : IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (R.ΛY k) Λ (R.βY k) β (R.datYt t k P) (R.chi (k + 1))
      (R.Q t) (R.xiR t) f₀ f') (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (F : GA D V → ℂ) (φ : PolF D V.rank (Yc D k).rank)
    (hi : ∀ g, IntegrableOn (fun h => thetaKO om g h
      (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f φ) * F h) 𝓕 ν)
    (U : GA D (Yc D k) → ℂ)
    (hU : ∀ κ ∈ levS (Yc D k) (R.βY k) (R.datYt t k P), ∀ g, U (g * κ) = levChi (Yc D k) (R.βY k) (R.datYt t k P) κ * U g)
    (he : ∀ g, Lift.liftInt ν 𝓕 (thetaKO om)
      (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f φ) F g = U g) :
    liftS om ν 𝓕 F (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f' φ) =
      (Nat.card P.H : ℂ) • U := by
  haveI := finite_H P
  haveI : Fintype P.H := Fintype.ofFinite _
  choose κ hκ using fun p : P.H => GlobalTheory.ChainEquiv.lifts_chain R.toLevCh _ hl t k hk p.1
  obtain ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩ := GlobalTheory.StepVecLaw.levRes_chrStep hl t ⟨k, hk⟩
  have s1 := sd (hl.βY k hk)
  have s2 := sd hβ
  have hs := @GlobalTheory.StepVecSum.stepVec_eq_sum D R.ψ R.θ (Yc D k) V _ _ om _ _ _ _ _ _ f₀ f f' hom (D.sp.Y_sig _) hV
    (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MY k)) (GlobalTheory.Chain.VacVec.cart_isCartanInv M) s1.1 s2.1 s1.2 s2.2 D.R.r D.R.t k (r_le_Y k)
    (rankY hk.le) hr R.Pg (R.Q t) (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2 R.chi (R.xiR t) P _ hf hf'
    (fun PP hP => ⟨a1 PP hP, b1 PP hP⟩) (fun PP hP => ⟨a2 PP hP, b2 PP hP⟩) a3 b3 κ hκ
  have hth : IsThetaFunO R.ψ (Yc D k) V f := (GlobalTheory.Chain.StepVac.stepVec_vac s1.1 s2.1 (by
    rw [rankY hk.le, hr]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _) hf).1
  exact (lift_sum hom hθ _ _ _ _ hth κ (fun p => (hκ p).1) _ (fun p => levChi_ne_zero _ _) hs ν 𝓕 F φ hi U he
    fun p g => hU _ (levChi_lift (L := R.datYt t k R.triv) P p (hκ p)) g).2

theorem lift_ioX_pt (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T) (j : ℕ)
    (h : j + 2 * 0 + 2 = D.R.m) (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e))
    (hF : ∀ κ ∈ levS (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P), ∀ φ x g,
      (R.ioX t F).1 (R.ItX φ x) (g * κ) = levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ *
        (R.ioX t F).1 (R.ItX φ x) g)
    {v : WO (Yc D (j + 1)) D.sp.X' → ℂ}
    (hv : IsStepVecOf R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (R.βY (j + 1)) R.βX
      (R.datYt t (j + 1) P) (R.chi D.R.m) (R.Q t) (R.xiR t) (vacT R j h) v) (Q x) :
    liftS (omT R t j h) (R.νX t) (R.fdX t) (F.1 x) (pureTensorO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX)
      (onb (R.MY (j + 1))) (onb R.MX) v Q) = (Nat.card P.H : ℂ) • (ioXT R t j h F).1 (itXT R j h Q x) := by
  have e : R.chi D.R.m = R.chi (j + 1 + 1) := congrArg R.chi (show j + 1 + 1 = D.R.m from h).symm
  have h1 := top_vec hc t j h
  rw [e] at h1 hv
  have key : ∀ n (e : D.R.m - 1 = n), ∀ κ ∈ levS (Yc D n) (R.βY n) (R.datYt t n P), ∀ φ x g,
      ((Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n)
        (R.ioX t) e : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) F).1
        ((Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX e :
          PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) φ x) (g * κ) =
      levChi (Yc D n) (R.βY n) (R.datYt t n P) κ *
        ((Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n)
        (R.ioX t) e : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) F).1
        ((Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX e :
          PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) φ x) g := by
    intro n e; subst e; exact hF
  exact lift_lev_pt P hl hm.inf t (j + 1) (by omega) D.sp.X'_sig (rank_top h) R.MX hl.βX (top_weil hc t j h) h1 hv
    _ _ _ Q ((top_io hc t j h).integ F Q x) _ (fun κ hκ g => key _ (idx_top h) κ hκ Q x g) ((top_io hc t j h).eq F Q x)

end

end GlobalTheory.TopStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfRepresentationTheoryOfHyp
section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinned0OfGap
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.SG.PackageTie2 Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.ConcreteSettingExists

namespace GlobalTheory.Core.Rk

theorem finX_of_gap : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC :=
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc⟩
  Formalism.L2.SG.Pf.finXC_of GlobalTheory.wuDecayOfGap CompanionTheory.D.gk.RF.automorphic_forms_finite_dimensional

section Worlds

open GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

end Worlds

end GlobalTheory.Core.Rk

end
end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.PtRowsAt

section General

open NumberField IsDedekindDomain MeasureTheory
open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe

def Placed {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u} (P : SPack D F0) (S : SRest P) (t : GA D (D.sp.Y 0)) (c : ℝ) : Prop :=
  SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧
    RowJ R eE P.X P.inst P.G t S.j

theorem Placed.of_heq {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {eE : D.what₂.EE →ₗ[ℂ] R.HE.H}
    {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F0 = F0') {P : SPack D F0} {S : SRest P} {P' : SPack D F0'} {S' : SRest P'}
    (hP : HEq P P') (hS : HEq S S') {t : GA D (D.sp.Y 0)} {c : ℝ} (h : Placed R F eE P' S' t c) : Placed R F eE P S t c := by
  subst hF
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hS
  exact h


set_option maxHeartbeats 1000000 in
theorem placed_upd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (k : ℝ) (lam : type_of% R.lam3) (e : type_of% (R.updS k lam).err0) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u} (P : SPack D F0) (S : SRest P) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (h : Placed R.toRealDat F.lv2 eE P S t c) :
    Placed ((R.updS k lam).withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 eE P S t c :=
  ⟨⟨h.1.fin, h.1.conj, h.1.mat⟩, h.2.1, h.2.2⟩


set_option maxHeartbeats 1000000 in
theorem exAt_upd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (k : ℝ) (lam : type_of% R.lam3) (e : type_of% (R.updS k lam).err0) (h : R.toRealDat.ExAt) :
    ((R.updS k lam).withErr e).toRealDat.ExAt :=
  ⟨h.ItY, h.ItX, h.ioY, h.ioX, h.Th, h.ioP, h.thF, h.thG⟩

section Args

open GlobalTheory.Mem.Top.Bl

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}


set_option maxHeartbeats 1000000 in
theorem exAt_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x) : x.R.toRealDat.ExAt := by
  obtain rfl := eq_of_heq hx
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => R.toRealDat.ExAt) a.pack
  exact e.mpr (exAt_upd _ _ _ _ t.exAt)


set_option maxHeartbeats 1000000 in
theorem placed_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 (w.st Z).toD7 u} (P : SPack (w.st Z).toD7 F0) (S : SRest P)
    (g : GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0)) (c : ℝ)
    (h : Placed (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y.eE P S g c) :
    Placed x.R.toRealDat x.F.lv2 x.Y.eE P S g c := by
  obtain rfl := eq_of_heq hx
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, F, _⟩ => ∀ eE : (w.st Z).toD7.what₂.EE →ₗ[ℂ] R.HE.H, HEq eE t.r.Y.eE →
        Placed R.toRealDat F.lv2 eE P S g c) a.pack
  refine e.mpr (fun eE he => ?_) _ a.eE
  obtain rfl : eE = t.r.Y.eE := eq_of_heq he
  exact placed_upd _ _ _ _ _ _ _ _ _ _ _ _ _ h

end Args


end General

theorem gapHyp_of_hd {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hCl : 1801 ≤ Cl) (H : GlobalTheory.Core.Rk.HD D L C' Cl Cg cb Cu cT CT) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  have HL := H.2.2.1
  obtain ⟨hS, hr⟩ := GlobalTheory.Core.Rk.HdGap.scale_of hCl HL
  have hr0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  refine ⟨hr, fun τ j hj => ?_⟩
  have := GlobalTheory.Core.Rk.HdGap.gap_of HL τ j.1 hj
  simp only [Fin.eta] at this
  have key : (((16 : ℚ) * (D.R.r : ℚ) ^ 19 : ℚ) : ℝ) ≤
      (((D.hc τ).b ⟨j.1 + 1, hj⟩ - (D.hc τ).b j : ℚ) : ℝ) := by
    rw [Rat.cast_sub]; push_cast; linarith
  exact_mod_cast key

end GlobalTheory.Fam.PtRowsAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlacedBesselPoints
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem oneBlock_lev {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : LevDat D.host.E ℂ V.rank)
    (hn : V.rank ≤ Λ.r) (hs : Λ.s = 0) (hQ : Λ.Q = ∅) (κ : GA D V) :
    (κ ∈ levS V β Λ ↔ κ ∈ GfC V ∧ Lev.finE V κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) β ∧
      Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) β Λ (Lev.finE V κ) ∈ Λ.P.H) ∧
    Lev.levChi V β Λ κ = ((Formalism.L2.DIV.ext1 Λ.P.H Λ.P.chi
      (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) β Λ (Lev.finE V κ)) : ℂˣ) : ℂ) := by
  refine ⟨⟨fun h => ?_, fun h => ⟨h.1, ?_⟩⟩, ?_⟩
  · have hl := mem_lev.1 h.2
    exact ⟨h.1, (mem_parLev.1 hl.1).2.1, hl.2⟩
  · refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, h.2.1,
      fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _, fun PP hPP => ?_⟩, h.2.2⟩
    rw [hQ] at hPP
    exact absurd hPP (Finset.notMem_empty _)
  · unfold Lev.levChi levFn
    simp only [hs, hQ, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]


end GlobalTheory.MiTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam

theorem comb_smul_coef {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (κ : ℂ) (d : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (κ • d) f = κ • comb ψ S T d f := by
  by_cases hκ : κ = 0
  · subst hκ; simp [comb]
  · unfold comb
    rw [Finsupp.support_smul_eq hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, mul_smul]

theorem isRatDatum_const_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D}
    {Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ} {f₀ f : WO S T → ℂ} (h : IsRatDatum ψ S T e Ξ f₀ f) (κ : ℂ) :
    IsRatDatum ψ S T e (fun z => κ * Ξ z) f₀ (κ • f) := by
  obtain ⟨Φ, hSB, hval, hth⟩ := h
  refine ⟨κ • Φ, ?_, fun γ => by simp [hval γ], ?_⟩
  · obtain ⟨hs, k, hk, hinv, hsupp⟩ := hSB
    refine ⟨fun t ht => hs t fun h0 => ht (by simp [h0]), k, hk, fun v hv hv' t => by simp [hinv v hv hv' t],
      fun t ht => hsupp t fun h0 => ht (by simp [h0])⟩
  · unfold IsThetaAt AllSome at hth ⊢
    refine ⟨hth.1, fun T hT => ?_⟩
    have h := hth.2 T hT
    simp only at h ⊢
    rw [h, map_smul]

def chartRescale {Ch : ℕ → Type} (m : ℕ) (cc : ℕ → ℂ) (b : ∀ j, Ch (j + 1) → ℂ) : ∀ j, Ch j → ℂ
  | 0 => fun _ => 1
  | j + 1 => fun γ => if j < m then cc j * b j γ else 1

theorem datRoot_ne_zero {x : ℂ} (h : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) : x ≠ 0 := by
  obtain ⟨n, hn, hx⟩ := h
  rintro rfl
  simp [zero_pow hn.ne'] at hx

theorem datRoot_mul {x y : ℂ} (hx : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) (hy : ∃ n : ℕ, 0 < n ∧ y ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (x * y) ^ n = 1 := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
  rw [mul_pow, pow_mul, hxa, one_pow, mul_comm a b, pow_mul, hyb, one_pow, one_mul]

theorem datRoot_prod {ι : Type*} (s : Finset ι) (x : ι → ℂ) (h : ∀ i ∈ s, ∃ n : ℕ, 0 < n ∧ x i ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (∏ i ∈ s, x i) ^ n = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact datRoot_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GlobalTheory.Fam

end
end
