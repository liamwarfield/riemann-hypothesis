module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodRationalEigenformHittingCarriedPart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormula

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTop
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem span_preimage_eq_top {L V W ι : Type*} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module ℂ W]
    (e : L →+* ℂ) (f : V →ₛₗ[e] W) (b : Module.Basis ι L V)
    (hli : LinearIndependent ℂ (fun i => f (b i))) (hsp : Submodule.span ℂ (Set.range (fun i => f (b i))) = ⊤)
    (S : Set W) (hS : Submodule.span ℂ S = ⊤) (hsub : ∀ y ∈ S, y ∈ Set.range f) :
    Submodule.span L {x | f x ∈ S} = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let B : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  let Φ : W →ₗ[ℂ] ℂ := B.constr ℂ (fun i => e (φ (b i)))
  have key : ∀ x, Φ (f x) = e (φ x) := by
    intro x
    have hx : x ∈ Submodule.span L (Set.range b) := b.mem_span x
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have : f (b i) = B i := (Module.Basis.mk_apply hli hsp.ge i).symm
      rw [this]
      exact B.constr_basis ℂ _ i
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul, hx, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  have hΦ : Φ = 0 := by
    refine LinearMap.ext_on hS fun y hy => ?_
    obtain ⟨x, rfl⟩ := hsub y hy
    have : φ x = 0 := hφ (Submodule.subset_span hy)
    rw [key, this, map_zero, LinearMap.zero_apply]
  apply hφ0
  ext x
  have := key x
  rw [hΦ, LinearMap.zero_apply] at this
  exact e.injective (by rw [← this, LinearMap.zero_apply, map_zero])

theorem span_latS : ∀ (D : D7) (w : D.what₂.places.Pl) (j : ℕ), Submodule.span D.what₂.LL (latS (D := D) w j) = ⊤ := by
  intro D w j
  have h := D.what₂.jMt_basis (D.what₂.muTw w) j (Module.Free.chooseBasis _ _)
  exact span_preimage_eq_top D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) _ h.1 h.2 _
    (D.what₂.MtLat (D.what₂.muTw w) j).span_top (fun y hy => D.what₂.MtLat_sub _ _ y hy)

end GlobalTheory.PlaceRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTopStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLatticeTwistedTuple_span_top : ∀ (D : D7) (w : D.what₂.places.Pl) (j : ℕ), Submodule.span D.what₂.LL (latS (D := D) w j) = ⊤ := by
  first | exact @GlobalTheory.PlaceRead.span_latS | exact GlobalTheory.PlaceRead.span_latS | (intros; apply GlobalTheory.PlaceRead.span_latS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScaleTwistedPlaceCoefficientMap
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScaleTwistedPlaceCoefficientMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceScale

theorem pow_eq_of_isScale {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := GlobalTheory.CoefRoot.coef_root _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := by
    have h3 : D.what₂.embLL a * c * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x =
        c' * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x := by
      rw [mul_assoc]; exact e2
    exact (mul_right_cancel₀ hx h3).symm
  refine ⟨k, hk, ?_⟩
  rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]

theorem coefFn_map {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n)
    (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) : coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  simp only [coefFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, RingHom.id_comp]


set_option maxHeartbeats 4000000 in
theorem exists_scale : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∃ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u ∧ ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc ∧ κ ≠ 0 ∧
    (∀ x, X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x) ∈ (baseOf Z c w j).valSpace) ∧
    (∀ x : VsV D j ℂ, harmFn (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x)) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) ∧
    IsScale X.R X.geo.v₀ (baseOf Z c w j) κ ∧ IsRoot1 (Z.ν (c.twI w) j (c.sd w) / κ) := by
  intro D X X0 Y S YS Z c w j H
  have hch := X.char
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 := ⟨hch.lev, hch.grp, hch.fam, hch.models, hch.chain, hch.thP⟩
  have hio : IoExt X.R.toRealDat := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  obtain ⟨ν', hν', -⟩ := H.rat
  obtain ⟨hν0, c₀, hsc, n, hn, hνn⟩ := (Z.scalar (c.twI w) j (c.sd w)).norm ⟨ν', hν'⟩
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hsc
  obtain ⟨cc, hc⟩ := GlobalTheory.ExtCoeff.exists_extC _ _ _ _ _ _ _ j Unit (fun _ => X.A3.A.μ0) (X.geo.O j)
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo := GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hch.lev Z.good Z.pin (c.twI w) j (c.sd w)
  have hO := X.geo.pins j
  obtain ⟨κ, hκ0, hval, hκ⟩ := GlobalTheory.CoefLatConj.exists_coef_scale D _ _ _ X.A3.A X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O
    hC ⟨X.geo.fw⟩ hio j hO cc hc u hu _ hB hBo
  have hfield := hO.2.lift.field
  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hO.2.lift.c0
  have hcL : ∀ F : VV D.what₂.LL (lamV D j), cc (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D j) F) = c0L j F := fun F => by
    obtain ⟨v', hv', hv0⟩ := hbc F
    refine (hc v' _ ?_).trans hv0
    change MvPolynomial.map D.what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]
  have hκs : IsScale X.R X.geo.v₀ (baseOf Z c w j) κ := ⟨gramR, c0R, c0L, hft, u, hu, fun F =>
    (congrArg (fun z => harmFn _ _ _ (X.R.ioP j (PiTensorProduct.tprod ℂ u) z)) (hcL F)).symm.trans
      ((hκ _).trans (congrArg (κ • ·) (coefFn_map _ _ _)))⟩
  obtain ⟨k, hk, hkk⟩ := pow_eq_of_isScale X.R X.geo.v₀ _ hsc hκs
  refine ⟨u, cc, κ, hu, hc, hκ0, hval, hκ, hκs, n * k, Nat.pos_of_ne_zero (Nat.mul_ne_zero hn hk), ?_⟩
  rw [X.phs j, map_one, one_mul] at hνn
  have e : Z.ν (c.twI w) j (c.sd w) ^ (n * k) = κ ^ (n * k) := by
    rw [pow_mul, hνn, ← pow_mul, mul_comm n k, pow_mul c₀, pow_mul κ, hkk]
  rw [div_pow, e, div_self (pow_ne_zero _ hκ0)]

end GlobalTheory.PlaceScale

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScaleTwistedPlaceCoefficientMapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scale_twisted_place_coefficient_map : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∃ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u ∧ ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc ∧ κ ≠ 0 ∧
    (∀ x, X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x) ∈ (baseOf Z c w j).valSpace) ∧
    (∀ x : VsV D j ℂ, harmFn (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x)) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) ∧
    IsScale X.R X.geo.v₀ (baseOf Z c w j) κ ∧ IsRoot1 (Z.ν (c.twI w) j (c.sd w) / κ) := by
  first | exact @GlobalTheory.PlaceScale.exists_scale | exact GlobalTheory.PlaceScale.exists_scale | (intros; apply GlobalTheory.PlaceScale.exists_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointThetaKillsReferenceTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointThetaKillsReferenceTuple
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev

noncomputable section
open scoped TensorProduct InnerProductSpace
open Formalism.L2.Rows GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThetaRead3


set_option maxHeartbeats 4000000 in
theorem thetaP_read_plain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i t x
  have hE : R.toRealDat.IsThP := RealDat.thP_of_weak hP.char.base.thP hH.aux.ex
  have hM := hP.char.base.models
  have hμ : Used0 D (Y.tup t) := by
    rcases hP.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h, Y.tup0]
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  set xM := D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x) with hxM
  set zt := R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x) with hzt
  obtain ⟨w, hwM, hwK, hwW⟩ := GlobalTheory.T.thetaAdjoint_at_lift_eq_lowestKType_restriction R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hP.char.base.lev
    hP.char.base.grp hM hE R.hv0 Y.IL (Y.tup t) hμ i xM
  have hth := Y.tied.lift.theta (Y.tup t) hμ i xM w
    (GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hE.thF (Y.tup t) i) hwM hwK hwW
  set u := Y.tupT (Y.tup t) with hu
  set a := Y.IL.jMt (Y.tup t) hμ i xM with ha
  set z' : (R.HV i u).H := (LinearEquiv.ofInjective (R.extV i u) (Y.hinj i u)).symm
    (Submodule.inclusion inf_le_left a) with hz'
  have hz'1 : R.extV i u z' = R.extV i t zt := by
    rw [hz', ofInjective_symm_eq]
    exact Y.mtRead i t hμ x
  have hzz : R.thF i u z' = R.thF i t zt := thF_congr R.toRealDat Y.hinj i t u (Y.tupT_tup t) zt z' hz'1
  let w' : (⨂[ℂ] τ, (R.MW i (sg0 D A3.A)).sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap (R.MW i (sg0 D A3.A)) := PiTensorProduct.lift.symm w'
  have hU : U ∈ R.Wall i (sg0 D A3.A) :=
    GlobalTheory.HeckeParts.mult_le_triv _ ((Mult.mem_multT _ _ _ _ w').1 hwM)
  have hlow : ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A3.A)) ρ, U (fun ρ => v ρ) = R.thF i u z' (fun ρ => v ρ) := by
    intro v
    have e := LinearMap.congr_fun hwK (PiTensorProduct.tprod ℂ v)
    have e2 : w' (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) =
        PiTensorProduct.lift (R.thF i u z')
          (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) := e
    rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod] at e2
    exact e2
  have hw0 : U - R.thF i t zt = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A3.A)) R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _ (Submodule.sub_mem _ hU (hE.thF_mem i t zt)) (fun v => by
        show U (fun ρ => v ρ) - R.thF i t zt (fun ρ => v ρ) = 0
        rw [hlow v, hzz, sub_self])
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  have h1 := (Y.mjRead i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) xM)).symm.trans hth
  change PiTensorProduct.lift _ = R.eWf i (sg0 D A3.A) ∘ₗ w' at h1
  rw [← hUw, sub_eq_zero.1 hw0, ← lift_postOn, ← hE.thG i t zt] at h1
  exact (hM.HW i (sg0 D A3.A)).1 (PiTensorProduct.lift.injective h1)

end GlobalTheory.Mem.ThetaRead3

namespace GlobalTheory.Mem.AdjLevel


set_option maxHeartbeats 4000000 in
theorem adjoint_eW_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → ∀ (i : Fin D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = 0 → LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y) = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i σ y _hy hT
  have hread := GlobalTheory.Mem.ThetaRead3.thetaP_read_plain D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH i A3.A.μ0
  have hT' : D.what₂.thetaT (Y.tup A3.A.μ0) ((i : ℕ) + 1) y = 0 := by rw [Y.tup0]; exact hT
  have hw : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) ∈
      R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := by
    have h0 : Y.mj.eW i y ∈ LinearMap.range (Y.mj.eW i) := ⟨y, rfl⟩
    rw [Y.mj.eW_range] at h0
    exact h0
  have ha := GlobalTheory.CarriedPart.adjoint_mem_span R F hH.ok hP.char hH.prim.unif hH.prim.gUnit hH.prim.gEquiv hH.prim.levW i _ hw
  have horth : ∀ f ∈ BlockGood.goodR (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0),
      ⟪Y.mj.eW i y, R.thG i A3.A.μ0 (R.jV i A3.A.μ0 f)⟫_ℂ = 0 := by
    intro f hf
    rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq] at hf
    have hfl : f ∈ lvlForms (A3.A.fam.L i A3.A.μ0).S (A3.A.fam.L i A3.A.μ0).r (A3.A.fam.lvlA F.P0 F.ψ0).P
        (A3.A.fam.lvlA F.P0 F.ψ0).ψ := fun h =>
      Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type _ _ hH.ok.ok2.irr _ _ h f hf
    rw [← GlobalTheory.Mem.LiftForms.range_lvlForm] at hfl
    obtain ⟨x, rfl⟩ := hfl
    have hx : GlobalTheory.Mem.LiftForms.lvlForm (A3.A.fam.L i A3.A.μ0).S (A3.A.fam.L i A3.A.μ0).r (A3.A.fam.lvlA F.P0 F.ψ0).P
        (A3.A.fam.lvlA F.P0 F.ψ0).ψ x = liftForm A3.A F.P0 F.ψ0 i A3.A.μ0 x := rfl
    rw [hx, ← hread x, GlobalTheory.Mem.LiftForms.inner_of_norm_sq (Y.mj.eW i) (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i),
      ← LinearMap.adjoint_inner_left]
    show _ * ⟪D.what₂.thetaT (Y.tup A3.A.μ0) ((i : ℕ) + 1) y, _⟫_ℂ = 0
    rw [hT', inner_zero_left, mul_zero]
  have hall : ∀ v ∈ Submodule.span ℂ (R.jV i A3.A.μ0 '' (BlockGood.goodR (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) :
      Set (A3.A.fam.L i A3.A.μ0).S.Forms)), ⟪Y.mj.eW i y, R.thG i A3.A.μ0 v⟫_ℂ = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨f, hf, rfl⟩ := hz
      exact horth f hf
    | zero => rw [map_zero, inner_zero_right]
    | add a b _ _ ha hb => rw [map_add (f := _), inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, inner_smul_right, ha, mul_zero]
  have h0 : ⟪LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y), LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y)⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left]
    exact hall _ ha
  exact inner_self_eq_zero.1 h0

end GlobalTheory.Mem.AdjLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointThetaKillsReferenceTupleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointTheta_kills_referenceTuple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → ∀ (i : Fin D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = 0 → LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y) = 0 := by
  first | exact @GlobalTheory.Mem.AdjLevel.adjoint_eW_eq_zero | exact GlobalTheory.Mem.AdjLevel.adjoint_eW_eq_zero | (intros; apply GlobalTheory.Mem.AdjLevel.adjoint_eW_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingOkClassAtPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.PlaceRead.TupAt

section General

open Formalism.IndefR Formalism.IndefR.Links _root_.Formalism.L2.DIV GlobalTheory.SeriesTie Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {D : D7}

theorem splitK_of_prime (P : PlE D.host) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hn : ¬ Ideal.absNorm P.asIdeal ∣ 30 * D.host.condN) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal) := by
  have := P.isPrime
  have h2 : Ideal.absNorm P.asIdeal = normV P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have h1 : P.asIdeal.inertiaDeg ℤ = 1 :=
    Nat.Prime.eq_one_of_pow (Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal ▸ hp)
  have key : ∀ r : ℕ, r.Prime → ((r : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = r := fun r hr hm => by
    by_contra hne
    have hc : IsCoprime ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) (r : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hp hr).2 hne)
    obtain ⟨a, b, e⟩ := hc
    exact this.ne_top ((Ideal.eq_top_iff_one _).2
      (e ▸ add_mem (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _)) (Ideal.mul_mem_left _ _ hm)))
  have hN : ¬ Ideal.absNorm P.asIdeal ∣ D.host.condN := fun h => hn (h.mul_left _)
  have hF : Fact (Ideal.absNorm P.asIdeal).Prime := ⟨hp⟩
  have hsp := Formalism.L2.Host.span_isPrime (Ideal.absNorm P.asIdeal)
  have hmax : (Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : ℤ)}).IsMaximal :=
    hsp.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero)
  have hlo : P.asIdeal.LiesOver (Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  refine GlobalTheory.TwistDet.exists_splitK h1 (Formalism.L2.Host.ramificationIdx_eq_one D.host _ hN P.asIdeal) ?_
    (fun h => Formalism.HC.HostRaw.ne_q_of_not_dvd hN (key _ D.host.hyp.1 h))
    (fun h => Formalism.HC.HostRaw.ne_d_of_not_dvd hN (key _ D.host.hyp.2.1 h))
  rw [← h2]
  exact hp.eq_two_or_odd'.resolve_left (Formalism.HC.HostRaw.ne_two_of_not_dvd hN)

theorem isDelta_delAt (cf : CharFrame D) (i : D.ntw.Tw) : ∃ q : ℕ, IsDelta q (cf.delAt (D.ntw.l i)) ∧
    (∀ P : Pl D.host.E, P ∈ D.ntw.pD i ↔ (q : 𝓞 D.host.E) ∈ P.asIdeal) ∧ (q = D.host.pde ∨ q = D.host.pde') := by
  refine ⟨if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, fun P => ?_, ?_⟩
  · unfold CharFrame.delAt
    split_ifs
    exacts [cf.isDel', cf.isDel]
  · rw [← Finset.mem_coe, D.ntw.pD_eq]
    rfl
  · split_ifs
    exacts [Or.inr rfl, Or.inl rfl]

theorem ram_mul (cf : CharFrame D) (i : D.ntw.Tw) {Q : Finset (Pl D.host.E)} {ψ : HChar D.host.E} (hψ : IsPsi (D.ntw.l i) Q ψ)
    (P : Pl D.host.E) : ¬ (cf.delAt (D.ntw.l i) * ψ).UnrAt P ↔ P ∈ D.ntw.pD i ∨ P ∈ Q := by
  obtain ⟨q, hδ, hq, -⟩ := isDelta_delAt cf i
  have hm : ∀ x, (cf.delAt (D.ntw.l i) * ψ).loc P x = (cf.delAt (D.ntw.l i)).loc P x * ψ.loc P x := fun _ => rfl
  by_cases hP : P ∈ D.ntw.pD i
  · refine iff_of_true (fun hu => ?_) (Or.inl hP)
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 := (hδ.ine P ((hq P).1 hP) (D.ntw.l i ^ a)).1 fun x hx => by
      have h3 : ψ.loc P x ^ (D.ntw.l i ^ a) = 1 :=
        (MonoidHom.pow_apply ..).symm.trans (congrArg (fun χ : HChar D.host.E => χ.loc P x) ha)
      rw [eq_inv_of_mul_eq_one_left ((hm x).symm.trans (hu x hx)), inv_pow, h3, inv_one]
    have hl : (D.ntw.l i).Prime := (D.ntw.lPrime _).out
    have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1 (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hl).1 (Nat.prime_five.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    omega
  · have hd := hδ.unr P fun h => hP ((hq P).2 h)
    rw [or_iff_right hP, ← not_iff_not, not_not, ← hψ.ram]
    exact forall₂_congr fun x hx => by rw [hm, hd x hx, one_mul]

theorem chrEq_twVia {cf : CharFrame D} {c : NChoice D} {tp : TupTied D cf c} (h : PsiChoiceCompatible D cf c tp) {w : D.what₂.places.Pl}
    (hw : D.what₂.muAt w ≠ D.what₂.mu0) (hψ : IntegralHeckeForms.TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w)) {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hv : ∀ P, P ∉ c.Q w → P ∉ D.ntw.pD (c.twI w) → ∃ y, D.what₂.embLL y = (((tp.psi w).val P : ℂˣ) : ℂ))
    (ι : KE c w →+* ℂ) (hι : ∀ y, ι (c.embW w y) = D.what₂.embLL y) : ChrEq (twVia ρ ι).chi (tp.psi w) := by
  classical
  obtain ⟨-, -, hopen, -, hzk, -, -⟩ := hψ
  have hl : D.ntw.l (c.twI w) ≠ 0 := (D.ntw.lPrime _).out.ne_zero
  have hz : D.ntw.zk (c.twI w) (c.k' w) ^ (D.ntw.l (c.twI w) ^ c.k' w) = 1 :=
    Units.ext (by simpa using (D.ntw.zk_prim (c.twI w) (c.k' w)).pow_eq_one)
  have hfin := GlobalTheory.TwistChr.finite_placesOver D.host.E (l := D.what₂.places.resChar w) (c.twI_l w ▸ hl)
  refine GlobalTheory.TwistChr.chrEq_charOf hρ.rc _ _ hopen (pow_ne_zero (c.k' w) hl) (fun σ => ?_) _
    ((c.Q w ∪ D.ntw.pD (c.twI w)) ∪ hfin.toFinset)
    (fun v hv => ((tp.psi_is w hw).ram v).2 fun hQ => hv (Finset.mem_union_left _ (Finset.mem_union_left _ hQ)))
    fun v hv' A hA σ hσ => ?_
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · have h1 : v ∉ c.Q w := fun hQ => hv' (Finset.mem_union_left _ (Finset.mem_union_left _ hQ))
    obtain ⟨y, hy⟩ := hv v h1 fun hQ => hv' (Finset.mem_union_left _ (Finset.mem_union_right _ hQ))
    have hy' : D.what₂.embLL y⁻¹ = (((tp.psi w).val v)⁻¹ : ℂˣ).1 := by rw [map_inv₀, hy, Units.val_inv_eq_inv_val]
    have e := h w hw v h1 (fun hQ => hv' (Finset.mem_union_right _ (hfin.mem_toFinset.2 hQ))) A σ hA hσ _ hy'
    rw [← hy', ← hι, e, ← IsScalarTower.algebraMap_apply]
    rfl

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}

theorem isTupOf {μ0 : T0} (hL : Rl.toRealDat.toLevCh.Is μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) {Q : Finset (Pl D.host.E)} {ψ : HChar D.host.E} (hψ : IsPsi (D.ntw.l i) Q ψ) {t : T0}
    (ht : Rl.xiH t = Rl.C.delAt (D.ntw.l i) * ψ) (hch : ∀ P ∈ Rl.Q t, P ∈ ρ.ch i) (τ : GlobalTheory.ExportSeries.Twist D Circle)
    (hc : ChrEq τ.chi ψ) (hQ : τ.Q = half (ρ.ch i) Q) : GlobalTheory.ConjTwist.IsTupOf Rl.toRealDat (ρ.B i j b) τ t := by
  classical
  refine ⟨GlobalTheory.ChrEqUnique.idc_unique D _ _ _ (hL.xi t) (ht ▸ GlobalTheory.TwistChr.chrEq_mul (hp.delta i j b) hc), ?_⟩
  have key : ∀ P, (P ∈ Rl.Q t ∨ ∃ P' ∈ Rl.Q t, Lev.IsConjPl P' P) ↔ P ∈ D.ntw.pD i ∨ P ∈ Q := fun P =>
    (hL.Q_ram t P).symm.trans (ht ▸ ram_mul Rl.C i hψ P)
  ext P
  rw [Finset.mem_union, hρ.delta, hQ]
  refine Iff.trans ?_ (or_congr mem_half mem_half).symm
  rw [← or_and_right, ← key]
  refine ⟨fun h => ⟨Or.inl h, hch P h⟩, fun ⟨h1, h2⟩ => h1.elim id fun ⟨P', h3, h4⟩ => ?_⟩
  by_cases e : P' = P
  · exact e ▸ h3
  · exact absurd h2 (((hρ.ch i).pair _ _ (GlobalTheory.BigOn.Exp.isConjPl_of_lev h4) e).1 (hch P' h3))

end General

theorem val_delAt {D : D7} {cf : CharFrame D} (h : ValLL0 D cf) (i : D.ntw.Tw) (P : PlE D.host) (hP : P ∉ D.ntw.pD i) :
    ∃ y, D.what₂.embLL y = (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) := by
  obtain ⟨q, hδ, hq, -⟩ := isDelta_delAt cf i
  have hu := hδ.unr P fun e => hP ((hq P).2 e)
  have hv : (cf.delAt (D.ntw.l i)).ValuesIn 0 D.what₂.embLL := by
    unfold CharFrame.delAt
    split_ifs
    exacts [h.toLL.del', h.toLL.del]
  obtain ⟨y, hy⟩ := hv P hu
  exact ⟨y, by simpa [HChar.valTw] using hy⟩

section State

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  (x : St P)

theorem mem_Wt {v : B.places.Pl} (hv : TwistedAt (Dof x) v) : v ∈ P.Wt := by_contra fun h => hv (P.q.mu.off v h)

theorem tupT_muTw {v : B.places.Pl} (hv : TwistedAt (Dof x) v) :
    x.r.Y.tupT ((Dof x).what₂.muTw v) = x.m.z.R.mu ((Dof x).plEq v) := by
  rw [← ((Dof x).what₂.muAt_or v).resolve_left hv, x.r.Y.muAt v, x.r.Y.tupT_tup]

theorem xi_mu (ch : NChoice (Dof x)) {v : B.places.Pl} (hv : TwistedAt (Dof x) v) {ψ : HChar (Dof x).host.E} (e : ψ = T.psi v) :
    x.m.z.R.xiH (x.m.z.R.mu ((Dof x).plEq v)) = x.m.z.R.C.delAt ((Dof x).ntw.l (ch.twI v)) * ψ := by
  have h1 := (x.m.z.mu v).2
  rw [if_pos (mem_Wt x hv)] at h1
  refine ((x.m.z.lev.xiH _).trans h1).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ CharFrame.delAt x.m.z.lev.C (ch.twI_l v)) e).symm
  rfl

end State

end GlobalTheory.PlaceRead.TupAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelTwistCharacterMemCoefficientIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelTwistCharacterMemCoefficientIntegers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceRead.LevVal

variable {D : D7}

theorem mem_intLL_of_pow {z : ℂ} {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) (hz : ∃ y, D.what₂.embLL y = z) : z ∈ intLL D := by
  obtain ⟨y, rfl⟩ := hz
  have h1 : y ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, h, map_one])
  have hi : IsIntegral ℤ y := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h1]⟩
  exact ⟨⟨y, hi⟩, rfl⟩

theorem mem_range_of_pow_of_fixed {K : Type} [Field K] [Countable K] [CharZero K] (f : K →+* ℂ) {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (h : z ^ n = 1) (hf : ∀ τ : ℂ ≃+* ℂ, (∀ x, τ (f x) = f x) → τ z = z) : ∃ y, f y = z := by
  letI : Algebra K ℂ := f.toAlgebra
  have hi : IsIntegral K z := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h]⟩
  let L := IntermediateField.adjoin K {z}
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hi
  haveI : Countable L := (Module.finBasis K L).equivFun.toEquiv.injective.countable
  let r : L := ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
  obtain ⟨y, hy⟩ := GlobalTheory.CompRat.FixedConst.mem_range_of_fixed (K := K) L.val (r := r) (IsIntegral.of_finite K r) hf
  exact ⟨y, congrArg Subtype.val hy⟩

theorem twistOf_good {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hψ : TwOK i k Q ψ) (f : D.ntw.Ok i k →+* ℂ) :
    (twistOf ρ.rc f (ρ.ch i) Q ψ).Good ∧
      ∀ x, ∃ σ, (((twistOf ρ.rc f (ρ.ch i) Q ψ).chi x : Circle) : ℂ) = f (ψ σ : (D.ntw.Ok i k)ˣ) ∧ ∃ n ≠ 0, ψ σ ^ n = 1 := by
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := GlobalTheory.T.chosenPlaces_admissible_goodSetup D D.nd D.ntw ρ hρ i j b Q hsplit hdisj
  let g : (D.ntw.Ok i k)ˣ →* Circle := unitPart.comp (Units.map f.toMonoidHom)
  have hkey : charOf ρ.rc f ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (D.ntw.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, ?_⟩
  · show (⟨half (ρ.ch i) Q, charOf ρ.rc f ψ, resOf (charOf ρ.rc f ψ)⟩ : Twist D Circle).Good
    rw [hkey]
    refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D D.nd D.ntw ρ.rc hρ.rc Circle (g.comp ψ) (D.ntw.l i) (D.ntw.lPrime i).out
      (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
    · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
        rw [MonoidHom.mem_ker] at hx ⊢
        rw [MonoidHom.comp_apply, hx, map_one]) hopen
    · intro x x' hx
      show g (ψ x') = (g (ψ x))⁻¹
      rw [hanti x x' hx, map_inv]
    · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
      exact h3.mono (Finset.subset_union_right.trans h2)
    · intro P hP hl
      exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (D.ntw.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (D.ntw.l i) from hl))
    · intro v hv hnc B hB σ hσ
      have hvQ : v ∉ Q := by
        intro hvQ
        by_cases hc : v ∈ ρ.ch i
        · exact hv (mem_half.2 ⟨hvQ, hc⟩)
        · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
          have hv'Q : v' ∈ Q := GlobalTheory.TwistGood.ramExactly_conj D.ntw ψ _ hanti hram v hvQ v' hv'
          have hne := ne_of_split (hsplit v hvQ) hv'
          have hv'c : v' ∈ ρ.ch i := by
            by_contra h
            exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
          exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
      have h1 : ψ σ = 1 := by
        by_contra h
        exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
      rw [MonoidHom.comp_apply, h1, map_one]
  · intro x
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
    exact ⟨σ, charOf_eq ρ.rc f hopen hσ (pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero) (hpow σ), _,
      pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero, hpow σ⟩

theorem de_chi_eq_pow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) ∧
      ∃ n ≠ 0, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ n = 1 := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  refine ⟨σ, ?_, _, Subgroup.FiniteIndex.index_ne_zero, hpow σ⟩
  rw [hρ.delta i j b]
  exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)

variable {X : RealSide D} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} (Z : ExportTie YS X.geo.v₀)

theorem de_mem_intLL (hX : FieldOk X) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    (((Z.ρ.B i j b).de.chi x : Circle) : ℂ) ∈ intLL D := by
  obtain ⟨σ, hσ, n, hn, hp⟩ := de_chi_eq_pow Z.good i j b x
  have hz : (((Z.ρ.B i j b).de.chi x : Circle) : ℂ) ^ n = 1 := by
    rw [hσ, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hp, Units.val_one, map_one, map_one]
  haveI : Countable D.what₂.LL := (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.injective.countable
  obtain ⟨y, hy⟩ := mem_range_of_pow_of_fixed (embLL0 D) hn hz fun τ hτ => by
    rw [hσ]
    refine GlobalTheory.DeltaFixed.aut_fixes_delta_values Z.ρ Z.good i j b (X.R.C.delAt (D.ntw.l i)) (Z.pin.delta i j b) ?_ τ hτ σ
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [hX.vals.del', hX.vals.del]
  exact mem_intLL_of_pow hn hz ⟨y, hy⟩

theorem muC_mem_intLL (hX : FieldOk X) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {PP : Pl D.host.E}
    (hPP : PP ∈ (Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) : (((Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ intLL D := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, PP ∈ placesOver D.host.E (D.host.g k) := Z.good.Pg i j b PP hPP
  have hw : w ^ (D.host.g k - 1) = 1 := by
    rw [← card_residueField_of_type hk, ← Nat.card_units]
    exact pow_card_eq_one'
  have hz : (((Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ^ (D.host.g k * (D.host.g k - 1)) = 1 := by
    rw [mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one, one_pow]
  obtain ⟨x, hx⟩ := hX.roots k _ hz
  have h2 := (D.host.g_prime k).two_le
  exact mem_intLL_of_pow (Nat.mul_ne_zero (by omega) (by omega)) hz ⟨x, hx⟩

theorem levLam_twVia_mem_intLL : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ k : (baseOf Z c w j).levJ (twVia Z.ρ ι), (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) ∈ intLL D := by
  intro D X X0 Y S YS Z c w j H ι hι x
  obtain ⟨hg, hv⟩ := twistOf_good Z.good (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) H.ok (viaOk ι)
  have htw : ∀ z, (((twVia Z.ρ ι).chi z : Circle) : ℂ) ∈ intLL D := fun z => by
    obtain ⟨σ, hσ, n, hn, hp⟩ := hv z
    obtain ⟨y, hy⟩ : ∃ y : D.what₂.LL, c.embW w y = algebraMap _ (KE c w) ((chr c w σ : (D.ntw.Ok (c.twI w) (c.k' w))ˣ) : D.ntw.Ok (c.twI w) (c.k' w)) := H.val σ
    refine mem_intLL_of_pow hn ?_ ⟨y, ?_⟩
    · refine (congrArg (· ^ n) hσ).trans ?_
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hp, Units.val_one, map_one]
    · rw [← hι, hy]
      exact hσ.symm
  have hext : ∀ g : G0 (Z.ρ.B (c.twI w) j (c.sd w)).G.Pg (Wc D j).rank,
      ((ext1 (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H (⇑(Z.ρ.B (c.twI w) j (c.sd w)).G.P.chi) g : ℂˣ) : ℂ) ∈ intLL D := fun g => by
    unfold ext1
    split_ifs with h
    · obtain ⟨g', rfl⟩ := (Z.ρ.eG (c.twI w) j (c.sd w)).surjective g
      obtain ⟨g₀, rfl⟩ := (X.R.eG.trans X.cG).surjective g'
      have hu : X.cG (X.R.eG g₀) ∈ D.nexp.U := ((Z.tie (c.twI w) j (c.sd w)).U_eq _).1 h
      have e1 := ((Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hu⟩ h).trans (H.psi_eq (c.twI w) (c.sd w) ⟨g₀, (H.U_eq g₀).1 hu⟩ hu)
      refine mem_intLL_of_pow (n := Nat.card (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H) Nat.card_pos.ne' ?_ ⟨_, (map_inv₀ _ _).trans e1.symm⟩
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
    · exact one_mem _
  have e : (baseOf Z c w j).levLam (twVia Z.ρ ι) x =
      levFn (baseOf Z c w j).F.βS ((baseOf Z c w j).levS (twVia Z.ρ ι)) (Formalism.UG.bc (Lev.swapAE D) x.1.1) := by
    unfold Base.levLam Lev.levCharAfE
    rfl
  rw [e]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  refine mul_mem (mul_mem (hext _) (prod_mem fun PP hPP => prod_mem fun _ _ => muC_mem_intLL Z H.field _ j _ hPP _))
    (prod_mem fun PP _ => ?_)
  rw [MonoidHom.mul_apply, Units.val_mul]
  exact mul_mem (locC_mem (Z.good.base _ j _).de (de_mem_intLL Z H.field _ j _) PP _) (locC_mem (t := twVia Z.ρ ι) hg htw PP _)

end GlobalTheory.PlaceRead.LevVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelTwistCharacterMemCoefficientIntegersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_twist_character_mem_coefficientIntegers : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ k : (baseOf Z c w j).levJ (twVia Z.ρ ι), (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) ∈ intLL D := by
  first | exact @GlobalTheory.PlaceRead.LevVal.levLam_twVia_mem_intLL | exact GlobalTheory.PlaceRead.LevVal.levLam_twVia_mem_intLL | (intros; apply GlobalTheory.PlaceRead.LevVal.levLam_twVia_mem_intLL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralUnitOfIsUnitAwayFromLevelEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralUnitOfIsUnitAwayFromLevelEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem unit_of_unitOff : ∀ (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (ε : FractionRing O →+* ℂ) (N : ℕ) (t : FractionRing O), IsUnit (N : O) → UnitOff N (ε t) → ∃ u : Oˣ, t = algebraMap O (FractionRing O) u := by
  intro O _ _ _ ε N t hN ⟨ht0, n, h1, h2⟩
  have hε : Function.Injective ε := ε.injective
  have key : ∀ s : FractionRing O, IsIntegral ℤ (ε s) → ∃ a : O, algebraMap O (FractionRing O) a = s := by
    intro s hs
    letI : Algebra ℤ (FractionRing O) := Ring.toIntAlgebra _
    have hs' : IsIntegral ℤ s := (isIntegral_algHom_iff (ε.toIntAlgHom) hε).mp hs
    have hO : IsIntegral O s := by
      have := IsIntegral.map_of_comp_eq (Int.castRingHom O) (RingHom.id (FractionRing O)) (RingHom.ext_int _ _) hs'
      simpa using this
    exact IsIntegrallyClosed.isIntegral_iff.mp hO
  have ht : t ≠ 0 := by rintro rfl; simp at ht0
  obtain ⟨a, ha⟩ := key (((N : FractionRing O)) ^ n * t) (by simpa [map_mul, map_pow, map_natCast] using h1)
  obtain ⟨b, hb⟩ := key (((N : FractionRing O)) ^ n * t⁻¹) (by simpa [map_mul, map_pow, map_natCast, map_inv₀] using h2)
  have hN' : (N : FractionRing O) ≠ 0 := by
    have := (hN.map (algebraMap O (FractionRing O))).ne_zero
    simpa using this
  have hab : a * b = (N : O) ^ (2 * n) := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, ha, hb, map_pow, map_natCast]
    field_simp
    ring
  have hua : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ hN.pow _)
  have hinv : algebraMap O (FractionRing O) ((hN.unit⁻¹ : Oˣ) : O) = (N : FractionRing O)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_natCast (algebraMap O (FractionRing O)) N, ← map_mul, IsUnit.val_inv_mul, map_one]
  refine ⟨hua.unit * hN.unit⁻¹ ^ n, ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_mul, map_pow, hinv, ha]
  rw [mul_comm (_ ^ n) t, mul_assoc, ← mul_pow, mul_inv_cancel₀ hN', one_pow, mul_one]

end GlobalTheory.PlaceRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralUnitOfIsUnitAwayFromLevelEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unit_of_isUnitAwayFromLevel_embedding : ∀ (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (ε : FractionRing O →+* ℂ) (N : ℕ) (t : FractionRing O), IsUnit (N : O) → UnitOff N (ε t) → ∃ u : Oˣ, t = algebraMap O (FractionRing O) u := by
  first | exact @GlobalTheory.PlaceRead.unit_of_unitOff | exact GlobalTheory.PlaceRead.unit_of_unitOff | (intros; apply GlobalTheory.PlaceRead.unit_of_unitOff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirichletSeriesExponentialSumConverges
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirichletSeriesExponentialSumConverges
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

namespace GlobalTheory.RSNonvan

theorem units_coe_multiset (A : Multiset ℂˣ) :
    (do let a ← A; pure (a : ℂ) : Multiset ℂ) = A.map (fun α : ℂˣ => (α : ℂ)) := by
  show A.bind (fun a => {(a : ℂ)}) = _
  exact Multiset.bind_singleton A _

theorem powSum_conj (B : Multiset ℂ) (r : ℕ) :
    (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum = starRingEnd ℂ ((B.map fun β => β ^ (r + 1)).sum) := by
  rw [map_multiset_sum, Multiset.map_map]
  simp [Function.comp_def, map_pow]

theorem natCast_cpow_eq_exp (q : ℕ) (hq : 1 < q) (r : ℕ) (x : ℝ) :
    (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) = Complex.exp (-((((r : ℝ) + 1) * Real.log q : ℝ) : ℂ) * (x : ℂ)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem four_terms (A B : Multiset ℂ) (q : ℕ) (hq : 1 < q) (r : ℕ) (x : ℝ) :
    (A.map fun α => α ^ (r + 1)).sum * (A.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (B.map fun α => α ^ (r + 1)).sum * (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (A.map fun α => α ^ (r + 1)).sum * (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (B.map fun α => α ^ (r + 1)).sum * (A.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) =
    ((‖((A + B).map (· ^ (r + 1))).sum‖ ^ 2 / ((r : ℝ) + 1) : ℝ) : ℂ) *
      Complex.exp (-((((r : ℝ) + 1) * Real.log q : ℝ) : ℂ) * (x : ℂ)) := by
  rw [powSum_conj A, powSum_conj B, natCast_cpow_eq_exp q hq, Multiset.map_add (f := _), Multiset.sum_add]
  set PA := (A.map fun α => α ^ (r + 1)).sum
  set PB := (B.map fun α => α ^ (r + 1)).sum
  have hn : ((‖PA + PB‖ ^ 2 : ℝ) : ℂ) = (PA + PB) * starRingEnd ℂ (PA + PB) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.ofReal_pow, hn, map_add (f := _)]
  ring

theorem fourProd_eq_exp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a)
    (σ' : CG E b) (hσ : σ.IsUnitary) (hσ' : σ'.IsUnitary) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hT : UnrOutside T σ) (hT' : UnrOutside T σ') (x : ℝ) (hx : 1 < x) :
    ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ =>
        ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧
      (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ' (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1) = Complex.exp g := by
  have L := GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E
  obtain ⟨s1, p1⟩ := L a a σ σ hσ hσ T hT hT x hx
  obtain ⟨s2, p2⟩ := L b b σ' σ' hσ' hσ' T hT' hT' x hx
  obtain ⟨s3, p3⟩ := L a b σ σ' hσ hσ' T hT hT' x hx
  obtain ⟨s4, p4⟩ := L b a σ' σ hσ' hσ T hT' hT x hx
  have h := (((s1.of_norm.hasSum.add s2.of_norm.hasSum).add s3.of_norm.hasSum).add s4.of_norm.hasSum)
  refine ⟨?g, ?hs, ?hp⟩
  case hp =>
    simp only [lfac]
    rw [p1.tprod_eq, p2.tprod_eq, p3.tprod_eq, p4.tprod_eq, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
  case hs =>
    refine (congrArg (fun f => HasSum f _) (funext fun p => ?_)).mpr h
    simp only [Pi.add_apply, units_coe_multiset]
    rw [four_terms _ _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1)]
    rfl

end GlobalTheory.RSNonvan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirichletSeriesExponentialSumConvergesStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichlet_series_exponential_sum_converges : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧ (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ (x : ℂ) w.1) * (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ' (x : ℂ) w.1) * (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) * (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1) = Complex.exp g := by
  first
  | exact @GlobalTheory.RSNonvan.fourProd_eq_exp
  | exact GlobalTheory.RSNonvan.fourProd_eq_exp
  | (intros; apply GlobalTheory.RSNonvan.fourProd_eq_exp <;> assumption)
end
end
