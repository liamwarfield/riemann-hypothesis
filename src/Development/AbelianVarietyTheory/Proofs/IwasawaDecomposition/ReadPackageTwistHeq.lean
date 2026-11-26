module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Extension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheorems

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up.LiTw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

section Gen

open Formalism.BasicNotions.TH _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem eigAd_of {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {Sb eig} (h : EigAd Y Sb eig)
    (v : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) → (R.HW i (sg0 D A3.A)).H) (H : ∀ i y, Y.mj.eW i y = v i y)
    (i : Fin D.R.m) (σ k P α Rr) (hd : HkDat R Sb i k P α Rr) (hg : D.nd.goodRow σ) (y) (hy : y ∈ D.what₂.isot (i.1 + 1) σ) :
    hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e (v i y)) =
      D.what₂.embLL ((eig (i.1 + 1) σ k P : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e (v i y) := by
  rw [← H]
  exact h i σ k P α Rr hd hg y hy

end Gen

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} {N : TwNew (Dof x)}

abbrev RdTw (x : St P) (N : TwNew (Dof x)) : Type 1 :=
  R3.Read (datTw x N).R.toRealDat (datTw x N).F.lv2 (sideTw x N).p0

noncomputable def jMtB (Y : RdTw x N) (μ h i y) : type_of% (x.r.Y.IL.jMt μ h i y).1 := (by with_unfolding_all exact ((Y.IL.jMt ((μ)) ((h)) ((i)) ((y))).1 : _))

noncomputable def mtAd (Y : RdTw x N) (H : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB Y μ h i y) {M : MtFam (Dof x)} (a : MtAd x.r.Y M) :
    MtAd Y ((fun μ j h1 h2 => { M μ j h1 h2 with })) where
  PV i := ⟨(by with_unfolding_all exact ((a.PV ((i))).ψ : _)), (by with_unfolding_all exact ((a.PV ((i))).inj : _)), (by with_unfolding_all exact ((a.PV ((i))).into : _)), (by with_unfolding_all exact ((a.PV ((i))).onto : _))⟩
  std := (by with_unfolding_all exact (a.std :))
  eW := (by with_unfolding_all exact (a.eW :))
  read μ h i y g := (by with_unfolding_all exact (((a.read ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (g :)))).trans
    (congrFun (H ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :)))) ((by with_unfolding_all exact (((a.PV ((i))).ψ ((g))) : _))))) :))
  rat := (by with_unfolding_all exact (a.rat :))
  wt := (by with_unfolding_all exact (a.wt :))
  id := (by with_unfolding_all exact (a.id :))

noncomputable def eWB (Y : RdTw x N) (i y) : type_of% (x.r.Y.mj.eW i y) := (by with_unfolding_all exact ((Y.mj.eW ((i)) ((y))) : _))

theorem hkDat {Sb i k Q α Rr} (h : HkDat (datTw x N).R Sb i k Q α Rr) :
    HkDat x.m.z.R ((Sb)) ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.offS :)), (by with_unfolding_all exact (h.odd :)), (by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.elt :)), (by with_unfolding_all exact (h.reps :))⟩

theorem eigAd (Y : RdTw x N) (H : ∀ i y, x.r.Y.mj.eW i y = eWB Y i y) {Sb eig} (h : EigAd x.r.Y Sb eig) :
    EigAd Y ((Sb)) ((eig)) := fun i σ k Q α Rr hd hg y hy =>
  (by with_unfolding_all exact ((eigAd_of h (((eWB Y))) ((H)) ((i)) ((σ)) k ((Q)) ((α)) ((Rr)) (((hkDat hd))) ((hg)) ((y)) ((hy))) : _))

noncomputable def ratInTw (n : InRat x.r.Y x.m.z.cG) : RatIn (w.st (oTw x N).Z).toD7
    (ratDatR (datTw x N).R (datTw x N).cG n.kKs n.hk) where
  Sb := n.In.Sb
  rho := n.In.rho
  chi := n.In.chi
  ks := n.In.ks
  fd := n.In.fd
  mk_fg := n.In.mk_fg
  hL := n.In.hL
  hs := n.In.hs
  hL_zero := n.In.hL_zero
  θ := n.In.θ
  θ_ne := n.In.θ_ne
  eig := n.In.eig
  span := (by with_unfolding_all exact ((ratIn N n.In).span : _))
  hL_int := (by with_unfolding_all exact ((ratIn N n.In).hL_int : _))

noncomputable def inRat (Y : RdTw x N) (H : ∀ i y, x.r.Y.mj.eW i y = eWB Y i y) (n : InRat x.r.Y x.m.z.cG) : InRat Y (datTw x N).cG where
  kKs := (by with_unfolding_all exact (n.kKs :))
  hk := (by with_unfolding_all exact (n.hk :))
  In := (by with_unfolding_all exact ((ratInTw (N := N) n) :))
  rat :=
    { hecke := fun j k Q α Rr h1 h2 hd y => (by with_unfolding_all exact ((n.rat.hecke j k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (α :))) ((by with_unfolding_all exact (Rr :))) h1 ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact ((hkDat hd) :))) ((by with_unfolding_all exact (y :)))) :))
      eig := (by with_unfolding_all exact ((eigAd Y H n.rat.eig) :))
      Sb_le := (by with_unfolding_all exact (n.rat.Sb_le :))
      lvl := (by with_unfolding_all exact (n.rat.lvl :))
      psi := (by with_unfolding_all exact (n.rat.psi :)) }

noncomputable def inMt (Y : RdTw x N) (H : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB Y μ h i y) (n : InMt x.r.Y (cfOf x) w.I.xi (QOf P)) :
    InMt Y (⟨(cfOf x).P, (cfOf x).W, (cfOf x).mu0, (cfOf x).eta, (cfOf x).chiPsi, (cfOf x).del, (cfOf x).del', (cfOf x).isMu0, (cfOf x).isEta, (cfOf x).isChi, (cfOf x).isDel, (cfOf x).isDel'⟩) w.I.xi (QOf P) where
  M := (fun μ j h1 h2 => { n.M μ j h1 h2 with })
  ad := (by with_unfolding_all exact ((mtAd Y H n.ad) :))
  mt :=
    { prod := by with_unfolding_all exact n.mt.prod
      para := by with_unfolding_all exact n.mt.para
      uni := by with_unfolding_all exact n.mt.uni
      hyp := by with_unfolding_all exact n.mt.hyp
      wt := by with_unfolding_all exact n.mt.wt
      rat := by with_unfolding_all exact n.mt.rat
      int := by with_unfolding_all exact n.mt.int
      full := by with_unfolding_all exact n.mt.full }

end GlobalTheory.HeightCounting.Up.LiTw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZetaUniformOfExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IotaStarProjectionQsp
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

theorem iota_starProjection_Qsp (D : D7) (μ : D.what₂.Tup) (F : D.what₂.Amb μ) (hF : F ∈ D.what₂.V0 μ) :
    D.what₂.iota μ ((D.what₂.Qsp μ).starProjection F) = D.what₂.iota μ F := by
  set a := (D.what₂.Usp μ).starProjection F with ha
  have haU : a ∈ D.what₂.Usp μ := Submodule.starProjection_apply_mem _ _
  have hb : F - a ∈ D.what₂.Qsp μ := ⟨Submodule.sub_mem _ hF haU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have haQ : (D.what₂.Qsp μ).starProjection a = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact (Submodule.mem_orthogonal _ _).2 fun q hq => Submodule.inner_left_of_mem_orthogonal haU hq.2
  have e : (D.what₂.Qsp μ).starProjection F = F - a := by
    have h := map_add (D.what₂.Qsp μ).starProjection a (F - a)
    rw [add_sub_cancel, haQ, zero_add, Submodule.starProjection_eq_self_iff.2 hb] at h
    exact h
  rw [e, map_sub, LinearMap.mem_ker.1 haU.2, sub_zero]

theorem zeTied_of_read : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y), Pins R F cG → Holds R F → D.BuRational → ZetaCompatible D := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C hP hH hB u μ c hfac hnz
  refine Y.ze u μ c hfac hnz ?_
  by_cases hU : Used0 D μ
  swap
  · exfalso
    obtain ⟨φ, x, hx, hne⟩ := hnz
    apply hne
    rw [hfac φ x hx, Y.junk μ hU, LinearMap.zero_apply, (D.Bu_linR u φ).map_zero, mul_zero]
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨Y.tupT μ, Y.tupTie μ hU⟩
  have hRS := (GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH).1
  have hFo := Y.formsA t
  have hR : LinearMap.range (rE D A3.A F.P1 F.ψ1 t).mulVecLin = LinearMap.range (rV0 D A3.A F.P1 F.ψ1 t).mulVecLin :=
    GlobalTheory.range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E _ _ _ _ _
  have hmem : ∀ f, Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f) ∈ D.what₂.V0 (Y.tup t) := by
    intro f
    have h1 : (rV0 D A3.A F.P1 F.ψ1 t).mulVec f ∈ LinearMap.range (rE D A3.A F.P1 F.ψ1 t).mulVecLin := by
      rw [hR]; exact ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := h1
    refine ⟨Y.jA t g, ?_⟩
    exact (hFo.op_eq g).trans (congrArg (Y.jA t) hg)
  have hQ : ∃ x f, D.what₂.Bu u (D.jN u (C.eNu u x))
      (D.what₂.iota (Y.tup t) (Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f))) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨φ0, F0, hF0, hne⟩ := hnz
    apply hne
    rw [hfac φ0 F0 hF0, iota_starProjection_Qsp D _ F0 hF0]
    have h1 : ∀ x, ∀ F ∈ D.what₂.V0 (Y.tup t), D.what₂.Bu u (D.jN u (C.eNu u x)) (D.what₂.iota (Y.tup t) F) = 0 := by
      intro x F hF
      obtain ⟨y, rfl⟩ := hF
      let L : D.what₂.Amb (Y.tup t) →ₗ[ℂ] ℂ :=
        ((D.Bu_linR u (D.jN u (C.eNu u x))).mk' _) ∘ₗ D.what₂.iota (Y.tup t) ∘ₗ D.what₂.eOp (Y.tup t)
      have hL : L = 0 := by
        refine LinearMap.ext_on_range hFo.span fun i => ?_
        have h2 : (rE D A3.A F.P1 F.ψ1 t).mulVec (Pi.single i 1) ∈ LinearMap.range (rV0 D A3.A F.P1 F.ψ1 t).mulVecLin := by
          rw [← hR]; exact ⟨_, rfl⟩
        obtain ⟨f, hf⟩ := h2
        have e1 : D.what₂.eOp (Y.tup t) (Y.jA t (Pi.single i 1)) = Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f) :=
          (hFo.op_eq _).trans (congrArg (Y.jA t) hf.symm)
        show D.what₂.Bu u (D.jN u (C.eNu u x)) (D.what₂.iota (Y.tup t) (D.what₂.eOp (Y.tup t) (Y.jA t (Pi.single i 1)))) = 0
        rw [e1]
        exact hcon x f
      exact LinearMap.congr_fun hL y
    let M : D.what₂.Mu u →ₗ[ℂ] ℂ := (D.Bu_linL u (D.what₂.iota (Y.tup t) F0)).mk' _
    have hM : M = 0 := by
      refine LinearMap.ext_on_range (D.jN_basis u).2 fun i => ?_
      have h3 := h1 ((C.eNu u).symm ((D.div.Nu u).b i)) F0 hF0
      rw [LinearEquiv.apply_symm_apply] at h3
      exact h3
    rw [show D.what₂.Bu u φ0 (D.what₂.iota (Y.tup t) F0) = 0 from LinearMap.congr_fun hM φ0, mul_zero]
  obtain ⟨x, f, hx⟩ := hQ
  have hpt := C.pt u t x f
  have hf := hfac (D.jN u (C.eNu u x)) _ (hmem f)
  rw [iota_starProjection_Qsp D _ _ (hmem f)] at hf
  obtain ⟨w, hw⟩ : ∃ w : D.div.RR.V,
      D.what₂.iota (Y.tup t) (Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) = D.jEE w :=
    ⟨_, by rw [← Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_iota]; exact hRS.iota t f⟩
  rw [hw, hB] at hx hf
  refine ⟨(F.Dc (R.toCx3 F).zs).Pt (C.wU u) t x f / D.div.Bk u (C.eNu u x) w, ?_⟩
  rw [map_div₀, hpt, hf]
  exact mul_div_cancel_right₀ c hx

end GlobalTheory.Mem.R3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceScalarsErrorsReadings
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3


set_option maxHeartbeats 4000000 in
theorem reFace_scalars_errors_readings : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), (∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨ ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v)) → Pins R F cG → Holds R F → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.Wp3 i p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Z'.jW Z.jW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Dc Sp Zsc hl6 hP hH
  refine ⟨R.kap, R.lam3, reFaceErr R F Dc Sp Zsc, ?_⟩
  exact ⟨reFace_pins R F cG Dc Sp Zsc _ hl6 hP,
    ⟨reFace_prim R F Dc Sp Zsc _ hH.prim, further_face_statements_independent_of_error R F Dc Sp Zsc _ hH.aux, hH.ok, hH.sep⟩,
    reFace_errEq R F Dc Sp Zsc, rfl, fun _ _ _ _ _ => rfl,
    reFaceRead R F Dc Sp Zsc _ X0 Y, reFaceReadL R F Dc Sp Zsc _ X0 Y Z,
    rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.Mem.R3

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3

open _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem readC_reFace_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp Sp' : ∀ Zs, SPer (Dc Zs))
    (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (kap : ℝ) (lam : type_of% R.lam3)
    (err : type_of% (R.updS kap lam).err0) {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
    (C : ReadC R (reFace F Dc Sp Zsc) X0 Y)
    (Y₁ : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat F.lv2 X0) (h1 : Y₁.tup = Y.tup) (h2 : HEq Y₁.jA Y.jA) :
    Nonempty (ReadC ((R.updS kap lam).withErr err) (reFace F Dc Sp' Zsc') X0 Y₁) := by
  have hzs : (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp' Zsc')).zs = (R.toCx3 (reFace F Dc Sp Zsc)).zs :=
    (congrArg CxData.zs (toCx3_upd_reFace R F kap lam err Dc Sp' Zsc')).trans (cx_zs_scal (R.toCx3 F) _ _ _)
  have aux : ∀ (R' : RealDat3 D A3 Ks)
      (Y' : Read (A3 := A3) R'.toRealDat (reFace F Dc Sp' Zsc').lv2 X0),
      (R'.toCx3 (reFace F Dc Sp' Zsc')).zs = (R.toCx3 (reFace F Dc Sp Zsc)).zs →
      Y'.tup = Y.tup → HEq Y'.jA Y.jA →
      Nonempty (ReadC R' (reFace F Dc Sp' Zsc') X0 Y') := by
    intro R' Y' hzs' htup hjA
    have key : ∀ (s : DefSub A3.fam3.amb3) (tp : T → D.what₂.Tup)
        (j : ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tp t)),
        s = (R.toCx3 (reFace F Dc Sp Zsc)).zs → tp = Y.tup → HEq j Y.jA →
        ∃ (wU : D.what₂.Word → (Dc s).Mem) (_ : Function.Bijective wU)
          (eNu : ∀ u, (Fin ((Dc s).a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V)
          (NuC : ∀ x, Submodule (𝓞 D.what₂.LL) (Fin ((Dc s).a x) → D.what₂.LL)),
          (∀ u, HLatTie (D.div.Nu u) (NuC (wU u)) ((Dc s).Xc (wU u)) (eNu u)) ∧
          ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc s).a (wU u)) → D.what₂.LL)
            (f : Fin ((A3.side3 F.P1 F.ψ1 s).nV t) → D.what₂.LL),
            D.what₂.embLL ((Dc s).Pt (wU u) t x f) =
              D.what₂.perCol u (tp t) (D.jN u (eNu u x)) (j t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) := by
      intro s tp j hs ht hj
      subst hs; subst ht; cases hj
      exact ⟨C.wU, C.bij, C.eNu, C.NuC, C.nu, C.pt⟩
    obtain ⟨wU, bij, eNu, NuC, nu, pt⟩ := key (R'.toCx3 (reFace F Dc Sp' Zsc')).zs Y'.tup Y'.jA hzs' htup hjA
    exact ⟨⟨wU, bij, eNu, NuC, nu, pt⟩⟩
  exact aux ((R.updS kap lam).withErr err) Y₁ hzs h1 h2

end GlobalTheory.Mem.R3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceOfLocalAdmissible
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HeightCounting.FirstFacts

theorem pair_of_over (D : D7) {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host}
    (hPq : ∀ v, NG.OverPl (Pq v) v) (P P' : PlE D.host) (hc : IsConjPl D.host P P') (hne : P ≠ P') :
    P ∈ Set.range Pq ↔ P' ∉ Set.range Pq := by
  have e := (GlobalTheory.PlacePair.comap_eq_iff D P P').2 (Or.inr hc)
  constructor
  · rintro ⟨v, rfl⟩ ⟨v', rfl⟩
    obtain rfl : v = v' := HeightOneSpectrum.ext ((hPq v).symm.trans (e.trans (hPq v')))
    exact hne rfl
  · intro h
    let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := P.under _
    have hv : NG.OverPl P v := rfl
    rcases (GlobalTheory.PlacePair.comap_eq_iff D P (Pq v)).1 (hv.trans (hPq v).symm) with e1 | e1
    · exact ⟨v, e1.symm⟩
    · exact absurd ⟨v, GlobalTheory.GalChar.isConjPl_unique e1 hc⟩ h

theorem vstd_of_over {K : GlobalTheory.Mem.Top.Ctx} (X : GlobalTheory.Mem.Stages) (hX : K.Over X.B.toPre) (i : Fin X.toD7.R.m) :
    FWT.VStd X.toD7 i := by
  obtain ⟨-, -, -, -, -, hVf, -⟩ := GlobalTheory.Mem.HostFrames.frames_of_over K X hX
  obtain ⟨h1, h2⟩ := hVf i
  rw [GlobalTheory.StdFrameCounterexample.vstd_iff]
  refine ⟨Matrix.ext fun a b => ?_, fun x => ?_⟩
  · rw [HSpace.gram, h1, Matrix.one_apply]
  · rw [h2, Module.Basis.mem_span_iff_repr_mem, Module.Basis.repr_sum_self]
    refine forall_congr' fun a => ?_
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]; exact y.2
    · intro h
      exact ⟨⟨x a, h⟩, rfl⟩

theorem mem_range_of_mem_QE {X : Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {Q : HeightOneSpectrum (𝓞 X.E)} : ∀ {ξ}, Q ∈ Col.QE sel ξ → Q ∈ Set.range sel := by
  classical
  intro ξ h
  unfold Col.QE at h
  split_ifs at h
  · obtain ⟨v, -, e⟩ := Finset.mem_image.1 h
    exact ⟨v, e⟩
  · exact absurd h (Finset.notMem_empty _)

end GlobalTheory.HeightCounting.FirstFacts

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr Formalism.IndefR.Datum
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.SerCopy

variable {B : GlobalTheory.Mem.Base} {C : Cols B} {a : Late B C} (b : Late B C)

noncomputable def twT {A : Type} [CommGroup A] (t : Twist a.D A) : Twist b.D A := ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

noncomputable def unT {A : Type} [AddCommGroup A] (t : UnivTwist a.D A) : UnivTwist b.D A := ⟨(by with_unfolding_all exact (t.del :)), (by with_unfolding_all exact (t.kap :))⟩

noncomputable def wtT {n : ℕ} (w : ExportSeries.Weight a.D n) : ExportSeries.Weight b.D n := ⟨(by with_unfolding_all exact (w.p :)), (by with_unfolding_all exact (w.q :)), (by with_unfolding_all exact (w.ap :)), (by with_unfolding_all exact (w.am :)), (by with_unfolding_all exact (w.c :)), (by with_unfolding_all exact (w.lam :))⟩

noncomputable def tyT {n : ℕ} (g : TypeDat a.D n) : TypeDat b.D n := ⟨(by with_unfolding_all exact (g.Pg :)), (by with_unfolding_all exact (g.P :)), (by with_unfolding_all exact (g.mu :))⟩

variable {S T : HSp a.D}

noncomputable def frT (F : Frame S T) : @Frame b.D ((S)) ((T)) :=
  ⟨(by with_unfolding_all exact (F.ψ :)), (by with_unfolding_all exact (F.θ :)), (by with_unfolding_all exact (F.sT :)), (by with_unfolding_all exact (F.BS :)), (by with_unfolding_all exact (F.BT :)), (by with_unfolding_all exact (F.ΛS :)), (by with_unfolding_all exact (F.ΛT :)), (by with_unfolding_all exact (F.βS :)), (by with_unfolding_all exact (F.βT :)), (by with_unfolding_all exact (F.f₀ :))⟩

noncomputable def baT (X : ExportSeries.Base S T) : @ExportSeries.Base b.D ((S)) ((T)) :=
  ⟨(by with_unfolding_all exact (X.hr :)), frT b X.F, (by with_unfolding_all exact ((tyT b X.G) :)), twT b X.de, (by with_unfolding_all exact ((wtT b X.w) :)), (by with_unfolding_all exact (X.mu0 :)), (by with_unfolding_all exact (X.eta :))⟩

theorem twGood {A : Type} [CommGroup A] {t : Twist a.D A} (h : t.Good) : (twT b t).Good :=
  ⟨(by with_unfolding_all exact (h.isOpen :)), (by with_unfolding_all exact (h.rat :)), (by with_unfolding_all exact (h.real :)), (by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.unram :)), (by with_unfolding_all exact (h.res :))⟩

theorem placesOK {Pg Q : Finset (Pl a.D.host.E)} (h : PlacesOK (D := a.D) Pg Q) : PlacesOK (D := b.D) ((by with_unfolding_all exact (Pg :))) ((by with_unfolding_all exact (Q :))) :=
  ⟨(by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.disj :)), (by with_unfolding_all exact (h.prime :))⟩

theorem frGood {F : Frame S T} (h : F.Good) : (frT b F).Good :=
  ⟨(by with_unfolding_all exact (h.rank_le :)), (by with_unfolding_all exact (h.onbS :)), (by with_unfolding_all exact (h.cartT :)), (by with_unfolding_all exact (h.onbT :)), (by with_unfolding_all exact (h.sdS :)), (by with_unfolding_all exact (h.sdT :)), (by with_unfolding_all exact (h.frS :)), (by with_unfolding_all exact (h.frT :)),
    ⟨(by with_unfolding_all exact (h.vac.1 :)), by rewrite [vacuum_eq a b, thetaFun_eq a b]; exact (by with_unfolding_all exact (h.vac.2 :))⟩⟩

theorem baGood {X : ExportSeries.Base S T} (h : X.Good) : (baT b X).Good :=
  { even := (by with_unfolding_all exact (h.even :))
    odd := (by with_unfolding_all exact (h.odd :))
    frame := frGood b h.frame
    de := twGood b h.de
    places := (by with_unfolding_all exact ((placesOK b h.places) :))
    wt := ⟨(by with_unfolding_all exact (h.wt.le :)), (by with_unfolding_all exact (h.wt.lam_eq :))⟩
    sig := (by with_unfolding_all exact (h.sig :))
    sigOK := (by with_unfolding_all exact (h.sigOK :))
    eta := (by with_unfolding_all exact (h.eta :))
    hecke := (by with_unfolding_all exact (h.hecke :))
    real := (by with_unfolding_all exact (h.real :))
    unram := (by with_unfolding_all exact (h.unram :))
    tame := (by with_unfolding_all exact (h.tame :))
    inf := (by with_unfolding_all exact (h.inf :)) }

theorem baWeil {X : ExportSeries.Base S T} {ν ω} (h : X.IsWeil ν ω) : (baT b X).IsWeil ((ν)) ((ω)) :=
  (by with_unfolding_all exact ((weilDatum_imp b _ _ _ _ _ _ h) :))

theorem baAdm {X : ExportSeries.Base S T} {Q} (h : X.admitted Q) : (baT b X).admitted ((Q)) :=
  ⟨(by with_unfolding_all exact ((placesOK b h.1) :)), (by with_unfolding_all exact (h.2 :))⟩

theorem classSys {V : HSp a.D} {J} {I : Type} {r : I → GA a.D V} (h : IsClassSystem V J r) :
    @IsClassSystem b.D ((V)) ((J)) I ((r)) := ⟨(h.fin), (h.reps), (h.stab)⟩

theorem placeMap_eq (F : Frame S T) : (frT b F).placeMap = (F.placeMap) := by
  funext e
  delta Frame.placeMap
  rewrite [placeModel_eq a b]
  exact (by with_unfolding_all exact ((Eq.refl (F.placeMap ((by with_unfolding_all exact (e :))))) :))

open Classical in
theorem vecAt_eq (X : ExportSeries.Base S T) : (baT b X).vecAt = (X.vecAt) := by
  delta ExportSeries.Base.vecAt Frame.vec
  rewrite [show (baT b X).F.placeMap = (by with_unfolding_all exact (X.F.placeMap :)) from (by with_unfolding_all exact ((placeMap_eq b X.F) :))]
  exact (by with_unfolding_all exact ((Eq.refl X.vecAt) :))

theorem theta_eq (X : ExportSeries.Base S T) : (baT b X).theta = (X.theta) := by
  delta ExportSeries.Base.theta ExportSeries.Base.vecBase
  rewrite [vecAt_eq b X]
  exact (by with_unfolding_all exact ((Eq.refl X.theta) :))

theorem genSet_eq (X : ExportSeries.Base S T) (ω) (t : Twist a.D Circle) :
    (baT b X).genSet (((ω : PairRep S T))) (twT b t) = ((X.genSet ω t : GA b.D S → PolF b.D T.rank S.rank → Set (GA b.D T → ℂ))) := by
  delta ExportSeries.Base.genSet ExportSeries.Base.gen ExportSeries.Base.vecFlat
  rewrite [vecAt_eq b X]
  exact (by with_unfolding_all exact ((Eq.refl (X.genSet ω t)) :))

theorem xiCoef_eq {A : Type} [AddCommGroup A] [Fintype A] (X : ExportSeries.Base S T) (ω) (u : UnivTwist a.D A) :
    (baT b X).xiCoef (((ω : PairRep S T))) (unT b u) = ((X.xiCoef ω u : (Q : Finset (Pl b.D.host.E)) → ((PP : Pl b.D.host.E) → A → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) → GA b.D S → PolF b.D T.rank S.rank → (↥Q → A) → GA b.D T → ℂ)) := by
  delta ExportSeries.Base.xiCoef ExportSeries.Base.xi ExportSeries.Base.vecFam
  rewrite [vecAt_eq b X]
  exact (by with_unfolding_all exact ((Eq.refl (X.xiCoef ω u)) :))

theorem classSum_eq (X : ExportSeries.Base S T) (ω) (t : Twist a.D Circle) {I : Type} [Fintype I] (r : I → GA a.D S) :
    (baT b X).classSum (((ω : PairRep S T))) (twT b t) (I := I) (((r : I → GA b.D S))) = ((X.classSum ω t r : (↥(Bridge.Gf S) → PolF b.D T.rank S.rank) →ₗ[ℂ] GA b.D T → ℂ)) := by
  delta ExportSeries.Base.classSum ExportSeries.Base.vecFlat
  rewrite [vecAt_eq b X]
  exact (by with_unfolding_all exact ((Eq.refl (X.classSum ω t r)) :))

noncomputable def rcT {Ω : Type} [Field Ω] [i : Algebra a.D.host.E Ω] (r : Recip a.D Ω) : @Recip b.D Ω _ ((i)) :=
  @Recip.mk b.D Ω _ ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (r.κ :))) ((by with_unfolding_all exact (r.art :)))

theorem rcGood {Ω : Type} [Field Ω] [i : Algebra a.D.host.E Ω] {r : Recip a.D Ω} (h : r.Good) :
    @Recip.Good b.D Ω _ ((i)) (@rcT B C a b Ω _ i r) := @Recip.Good.mk b.D Ω _ ((i)) _ ((by with_unfolding_all exact (h.cont :))) ((by with_unfolding_all exact (h.rat :))) ((by with_unfolding_all exact (h.loc :))) ((by with_unfolding_all exact (h.artin :)))

theorem choiceT {ch : Set (Pl a.D.host.E)} (h : IsChoice (D := a.D) ch) : IsChoice (D := b.D) ((by with_unfolding_all exact (ch :))) :=
  ⟨(by with_unfolding_all exact (h.pair :)), (by with_unfolding_all exact (h.one :))⟩

section Setup

structure Oth {B : GlobalTheory.Mem.Base} {C : Cols B} (W : RowsRest B C) where
  V : DivStage B C W
  S : SStage B C W
  N : NStage B C W
  G : GJStage B C

variable {B : GlobalTheory.Mem.Base} {C : Cols B} {W : RowsRest B C}

noncomputable def Oth.L (o : Oth W) : Late B C := ⟨W, o.V, o.S, o.N, o.G⟩

variable {o : Oth W} (o' : Oth W) {N : NData o.L.D.R o.L.D.host o.L.D.what₂} {X : NTw o.L.D.R o.L.D.host o.L.D.what₂ o.L.D.LL0 N}

noncomputable def seT (ρ : Setup X) : @Setup o'.L.D ((N)) ((X)) :=
  @Setup.mk o'.L.D ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (X :))) ((by with_unfolding_all exact ((rcT o'.L ρ.rc) :))) ((by with_unfolding_all exact (ρ.ch :))) ((by with_unfolding_all exact (ρ.bad :))) ((by with_unfolding_all exact (ρ.e :))) ((by with_unfolding_all exact (ρ.ek :)))
    (fun i j b => (by with_unfolding_all exact ((baT o'.L (ρ.B ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)) :))) ((by with_unfolding_all exact (ρ.om :)))
    (fun i j b t => ρ.Cl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twT o.L t)) (fun i j b t => ρ.finCl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twT o.L t))
    (fun i j b t => (by with_unfolding_all exact ((ρ.rep ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twT o.L t)) :))) ((by with_unfolding_all exact (ρ.β :))) ((by with_unfolding_all exact (ρ.eG :)))

variable {ρ : Setup X}

theorem seGood (h : ρ.Good) : (seT o' ρ).Good :=
  { rc := (by with_unfolding_all exact ((rcGood o'.L h.rc) :))
    ch := fun i => (by with_unfolding_all exact ((choiceT o'.L (h.ch ((by with_unfolding_all exact (i :))))) :))
    bad_ne := (by with_unfolding_all exact (h.bad_ne :))
    goodSetup_bad_mem_badPlaces := (by with_unfolding_all exact (h.goodSetup_bad_mem_badPlaces :))
    goodSetup_badPlaces_conj := (by with_unfolding_all exact (h.goodSetup_badPlaces_conj :))
    goodSetup_placesOverTwo_subset := (by with_unfolding_all exact (h.goodSetup_placesOverTwo_subset :))
    goodSetup_count_eq_zero_off_badPlaces := (by with_unfolding_all exact (h.goodSetup_count_eq_zero_off_badPlaces :))
    e_LL0 := (by with_unfolding_all exact (h.e_LL0 :))
    ek_e := (by with_unfolding_all exact (h.ek_e :))
    base := fun i j b => (by with_unfolding_all exact ((baGood o'.L (h.base ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)) :))
    latS := (by with_unfolding_all exact (h.latS :))
    latT := (by with_unfolding_all exact (h.latT :))
    Pg := (by with_unfolding_all exact (h.Pg :))
    delta := fun i j b => (by with_unfolding_all exact ((congrArg (twT o'.L) (h.delta ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)) :))
    weil := fun i j b t ht => (by with_unfolding_all exact ((baWeil o'.L (h.weil ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twT o.L t) (twGood o.L ht))) :))
    classes := fun i j b t ht ha => (by with_unfolding_all exact ((classSys o'.L (h.classes ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twT o.L t) (twGood o.L ht) ((by with_unfolding_all exact ((baAdm o.L ha) :))))) :)) }

variable (ρ) (i : X.Tw) (j : Fin o.L.D.R.m) (b : Bool)

theorem se_theta : (seT o' ρ).theta ((i)) ((j)) b = (ρ.theta i j b) := by
  funext h P
  have e : @Eq (type_of% (ρ.B i j b).theta) ((by with_unfolding_all exact ((baT o'.L (ρ.B i j b)).theta :))) (ρ.B i j b).theta :=
    (by with_unfolding_all exact ((theta_eq o'.L (ρ.B i j b)) :))
  exact (by with_unfolding_all exact ((congrArg (fun t : type_of% (ρ.B i j b).theta => t (ρ.om i j b 1) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (P :)))) e) :))

theorem se_gens : (seT o' ρ).gens ((i)) ((j)) b = (ρ.gens i j b) := by
  funext k Q ψ
  exact (by with_unfolding_all exact ((genSet_eq o'.L (ρ.B i j b) (ρ.om i j b 1) (ρ.tw i b k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))))) :))

theorem se_sum : (seT o' ρ).sum ((i)) ((j)) b = (ρ.sum i j b) := by
  funext k Q ψ
  exact (by with_unfolding_all exact ((classSum_eq o'.L (ρ.B i j b) (ρ.om i j b (ρ.tw i b k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :)))).chi) (ρ.tw i b k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))))
    (ρ.rep i j b (ρ.tw i b k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :)))))) :))

theorem se_xi (Y : NExp o.L.D.R o.L.D.host o.L.D.what₂ o.L.D.LL0 N X) :
    (seT o' ρ).xi ((i)) ((j)) b ((Y)) = (ρ.xi i j b Y) := by
  funext Q M
  exact (by with_unfolding_all exact ((congrFun (congrFun (xiCoef_eq o'.L (ρ.B i j b) (ρ.om i j b 1) (univOf Y i (admissibleConjugatePairPlaces X i ((by with_unfolding_all exact (Q :))) M) M ρ.rc))
    ((by with_unfolding_all exact ((half (ρ.ch i) (admissibleConjugatePairPlaces X i ((Q)) M)) : _))))
    ((by with_unfolding_all exact ((ExportSeries.Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i ((Q)) M) M ρ.rc) (ρ.β j)) : _)))) :))

variable {ρ i j b}

theorem se_datum {s h P} (d : ρ.IsDatum i j b s h P) : (seT o' ρ).IsDatum ((i)) ((j)) b ((s)) ((h)) ((P)) :=
  ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (d.mem :))⟩

theorem se_datum' {s h P} (d : (seT o' ρ).IsDatum ((i)) ((j)) b s h P) : ρ.IsDatum i j b ((s)) ((h)) ((P)) :=
  ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (d.mem :))⟩

theorem se_hk {k P α R z} (d : ρ.IsHeckeDatum i j b k P α R z) :
    (seT o' ρ).IsHeckeDatum ((i)) ((j)) b k ((P)) ((α)) ((R)) ((z)) := ⟨(d.elt), (d.reps), (d.det)⟩

theorem se_hk' {k P α R z} (d : (seT o' ρ).IsHeckeDatum ((i)) ((j)) b k P α R z) :
    ρ.IsHeckeDatum i j b k ((P)) ((α)) ((R)) ((z)) := ⟨(d.elt), (d.reps), (d.det)⟩

variable {Y : NExp o.L.D.R o.L.D.host o.L.D.what₂ o.L.D.LL0 N X}

noncomputable def rdT (rd : Rd ρ Y i j b) : @Rd o'.L.D ((N)) ((X)) (@seT B C W o o' N X ρ) ((Y)) ((i)) ((j)) b := (rd)

variable {rd : Rd ρ Y i j b}

theorem heckeTieT (h : HeckeTie rd) : @HeckeTie o'.L.D ((N)) ((X)) (@seT B C W o o' N X ρ) ((Y)) ((i)) ((j)) b (@rdT B C W o o' N X ρ i j b Y rd) := fun k P hk f hg α R z d =>
  (by with_unfolding_all exact ((h k ((by with_unfolding_all exact (P :))) ((by with_unfolding_all exact (hk :))) ((by with_unfolding_all exact (f :))) (hg.elim fun g e => ⟨(by with_unfolding_all exact (g :)), fun α R z d => (by with_unfolding_all exact ((e _ _ _ (se_hk o' d)) :))⟩) ((by with_unfolding_all exact (α :))) ((by with_unfolding_all exact (R :))) ((by with_unfolding_all exact (z :)))
    (se_hk' o' d)) :))

variable {hρ : ρ.Good}

theorem ratT (h : SeriesTie.Rat hρ rd) : SeriesTie.Rat (@seGood B C W o o' N X ρ hρ) (@rdT B C W o o' N X ρ i j b Y rd) := by
  refine ⟨fun s g P d => ?_, fun k Q ψ h1 h2 s g P d => ?_, fun Q M h1 s g P d h2 a => ?_⟩
  · rewrite [se_theta o' ρ i j b]
    exact (by with_unfolding_all exact ((h.1 _ _ _ (se_datum' o' d)) :))
  · rewrite [se_gens o' ρ i j b]
    exact (by with_unfolding_all exact ((h.2.1 k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h2 :))) _ _ _ (se_datum' o' d)) :))
  · rewrite [se_xi o' ρ i j b Y]
    exact (by with_unfolding_all exact ((h.2.2 ((by with_unfolding_all exact (Q :))) M ((by with_unfolding_all exact (h1 :))) _ _ _ (se_datum' o' d) ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact (a :)))) :))

theorem ratT' (h : SeriesTie.Rat (@seGood B C W o o' N X ρ hρ) (@rdT B C W o o' N X ρ i j b Y rd)) : SeriesTie.Rat hρ rd := (by with_unfolding_all exact ((ratT (o := o') o h) :))

noncomputable def cellT (t : CellTie hρ Y rd) : CellTie (@seGood B C W o o' N X ρ hρ) _ (@rdT B C W o o' N X ρ i j b Y rd) where
  supp := (by with_unfolding_all exact (t.supp :))
  cls := (by with_unfolding_all exact (t.cls :))
  coef := (by with_unfolding_all exact (t.coef :))
  rdV := (by with_unfolding_all exact (t.rdV :))
  U_eq := (by with_unfolding_all exact (t.U_eq :))
  psiU_eq := (by with_unfolding_all exact (t.psiU_eq :))
  dat := fun d => (by with_unfolding_all exact ((se_datum o' (t.dat ((by with_unfolding_all exact (d :))))) :))
  dat_onto := fun s g P d => by
    rewrite [se_theta o' ρ i j b]
    exact (by with_unfolding_all exact ((t.dat_onto _ _ _ (se_datum' o' d)) :))
  lev_iff := (by with_unfolding_all exact (t.lev_iff :))
  th_eq := by
    rewrite [se_theta o' ρ i j b]
    exact (by with_unfolding_all exact (t.th_eq :))
  thPsi_iff := by
    rewrite [se_gens o' ρ i j b]
    exact (by with_unfolding_all exact (t.thPsi_iff :))
  thU_eq := by
    rewrite [se_xi o' ρ i j b Y]
    exact (by with_unfolding_all exact (t.thU_eq :))
  thU_off := by
    rewrite [se_xi o' ρ i j b Y]
    exact (by with_unfolding_all exact (t.thU_off :))
  rdV_inj := (by with_unfolding_all exact (t.rdV_inj :))
  mtLat_iff := (by with_unfolding_all exact (t.mtLat_iff :))
  thP_eq := by
    rewrite [se_sum o' ρ i j b]
    exact (by with_unfolding_all exact (t.thP_eq :))

end Setup

end GlobalTheory.HeightCounting.SerCopy

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelIffUnipotentAtTypePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelIffUnipotentAtTypePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevUniLoc

theorem mem_iff_uniRT : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ, TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      (κ ∈ M.J ↔ NG.UniRT (M.sp (NX.pG D kv0)) D.R.r ((M.sp (NX.pG D kv0)).loc D.R.nV κ)) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M kv0 hG hQ hD κ hκ
  rw [M.J_mem κ]
  constructor
  · rintro ⟨hU, hL, -, -⟩
    obtain ⟨⟨_, hll⟩, huni⟩ := hL kv0
    exact ⟨⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).2 hU, hll⟩, huni⟩
  · rintro ⟨⟨hGL, hll⟩, huni⟩
    refine ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).1 hGL, fun kv => ?_, fun P hP => ?_, fun P hP => ?_⟩
    · by_cases hk : kv = kv0
      · subst hk
        exact ⟨⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hGL).1 a b, hll⟩, huni⟩
      · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hG kv hk)]; exact NX.inLevG_one _ _
    · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hQ P hP)]; exact NX.inParah_one _ _
    · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hD P hP)]; exact NX.inParah_one _ _

end GlobalTheory.LevUniLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelIffUnipotentAtTypePlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_iff_unipotent_at_typePlace : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ, TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      (κ ∈ M.J ↔ NG.UniRT (M.sp (NX.pG D kv0)) D.R.r ((M.sp (NX.pG D kv0)).loc D.R.nV κ)) := by
  first | exact @GlobalTheory.LevUniLoc.mem_iff_uniRT | exact GlobalTheory.LevUniLoc.mem_iff_uniRT | (intros; apply GlobalTheory.LevUniLoc.mem_iff_uniRT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionCompatibleAtReadIdentifications
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalPairingEqColumnPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalPairingEqColumnPairing
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem bk_eq_of_coordinates (D : D7) (μ : D.what₂.Tup) (hμ : μ = D.what₂.mu0) {n nV d a : ℕ}
    (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) (V : Matrix (Fin n) (Fin nV) D.what₂.LL)
    (Pq : Matrix (Fin d) (Fin nV) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V) (u : D.what₂.Word)
    (eN : (Fin a → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (P : (Fin a → D.what₂.LL) → (Fin nV → D.what₂.LL) → D.what₂.LL)
    (hB : Formalism.BasicNotions.Rows.BuDefQ D.what₂) (hBR : D.BuRational)
    (hV : D.what₂.V0 μ = Submodule.span ℂ (Set.range fun G => jA (V.mulVec G)))
    (hι : ∀ G, D.what₂.iota μ (jA (V.mulVec G)) = D.jEE (eRR (Pq.mulVec G)))
    (hper : ∀ x G, D.what₂.embLL (P x G) = D.what₂.perCol u μ (D.jN u (eN x)) (jA (V.mulVec G)))
    (hvan : ∀ x G, Pq.mulVec G = 0 → P x G = 0) :
    ∀ x G, D.div.Bk u (eN x) (eRR (Pq.mulVec G)) = P x G := by
  subst hμ
  intro x G
  have key := GlobalTheory.span_range_inf_ker_le_of_basis D.what₂.embLL D.div.RR.b (jA.comp V.mulVecLin) D.jEE
    (D.what₂.iota D.what₂.mu0) (eRR.toLinearMap ∘ₗ Pq.mulVecLin) D.jEE_basis.1 hι
  have hU : D.what₂.Usp D.what₂.mu0 = Submodule.span ℂ ((jA.comp V.mulVecLin) ''
      {x | (eRR.toLinearMap ∘ₗ Pq.mulVecLin) x = 0}) := by
    rw [← key, Formalism.BasicNotions.Rows.Data.Usp, hV]
    rfl
  have hK : ∀ F ∈ D.what₂.Usp D.what₂.mu0, D.what₂.perCol u D.what₂.mu0 (D.jN u (eN x)) F = 0 := by
    intro F hF
    rw [hU] at hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨G', hG', rfl⟩ := hF
      have hG'' : Pq.mulVec G' = 0 := eRR.map_eq_zero_iff.1 hG'
      refine (hper x G').symm.trans ?_
      rw [hvan x G' hG'', map_zero]
    | zero => exact D.perCol_zero u _
    | add F G _ _ hF hG => rw [D.perCol_add, hF, hG, add_zero]
    | smul c F _ hF => rw [GlobalTheory.perCol_base_smul_form, hF, mul_zero]
  have hmem : jA (V.mulVec G) ∈ D.what₂.V0 D.what₂.mu0 := by
    rw [hV]
    exact Submodule.subset_span ⟨G, rfl⟩
  apply D.what₂.embLL.injective
  rw [← hBR u (eN x) (eRR (Pq.mulVec G)), ← hι G, hper x G]
  exact (GlobalTheory.perCol_eq_pairing_of_kills D hB u _ hK _ hmem).symm

theorem pairing_eq_colPairing : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH), Pins R F cG → Holds R F → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → ∀ u x y, D.div.Bk u (C.eNu u x) (Z.eRR y) = (colOf R F sEE).B (C.wU u) x y := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C sEE hPins hHolds hBR hBt u x y
  have hR := complex_data_conditions_base_level_of_primitive_links hHolds.ok hHolds.sep hPins.char hHolds.prim
  have hW := hR.wf true
  have h2 := (hR.what₂ true).1
  have hI := (GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds).1
  have hPq := hW.Pq_surj A3.fam3.base3.μ0
  have hRi := CxData.rinv_spec _ hPq
  have hV := GlobalTheory.range_op_eq_span_of_formsTie D.what₂.embLL (Y.jA A3.fam3.base3.μ0) _ _ _
      (rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0) (Y.formsA A3.fam3.base3.μ0)
      (GlobalTheory.range_goodProjector_eq_range_goodCoordinates D A3.A 1 hHolds.ok.ok2 F.P1 F.ψ1 A3.fam3.base3.μ0)
  have hι : ∀ G0, D.what₂.iota (Y.tup A3.fam3.base3.μ0) (Y.jA A3.fam3.base3.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0).mulVec G0)) =
      D.jEE (Z.eRR (((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0).mulVec G0)) := by
    intro G0
    have h := hI.iota A3.fam3.base3.μ0 G0
    rw [Formalism.BasicNotions.Examples₂.NZ.sharp_iota] at h
    refine h.trans ?_
    show D.jEE (Z.eRR (((R.toCx3 F).rowMat F.cr true A3.fam3.base3.μ0).mulVec _)) = _
    rw [CxData.rowMat_base _ F.cr true h2]
    exact congrArg (fun v => D.jEE (Z.eRR v)) (Matrix.one_mulVec _)
  have key := bk_eq_of_coordinates D (Y.tup A3.fam3.base3.μ0) Y.tup0 (Y.jA A3.fam3.base3.μ0)
    (rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0) ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0) Z.eRR u (C.eNu u)
    (fun x G0 => (F.Dc (R.toCx3 F).zs).Pt (C.wU u) A3.fam3.base3.μ0 x G0) Y.bu hBR hV hι
    (fun x G0 => C.pt u A3.fam3.base3.μ0 x G0) ?_
  · have hy : ∀ v : Fin ((lv (F.fc (R.toCx3 F).zs) true).dQ A3.fam3.base3.μ0) → D.what₂.LL,
        ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0).mulVec
          ((CxData.rinv ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0)).mulVec v) = v := by
      intro v
      refine (Matrix.mulVec_mulVec _ _ _).trans ?_
      exact (congrArg (fun M => Matrix.mulVec M v) hRi).trans (Matrix.one_mulVec v)
    refine Eq.trans ?_ (key x ((CxData.rinv ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0)).mulVec y))
    exact congrArg (fun v => D.div.Bk u (C.eNu u x) (Z.eRR v)) (hy y).symm
  · intro x G0 hG0
    apply hBt (C.wU u) x G0
    exact LinearMap.mem_ker.2 hG0

end GlobalTheory.Mem.R3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalPairingEqColumnPairingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPairing_eq_columnPairing : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH), Pins R F cG → Holds R F → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → ∀ u x y, D.div.Bk u (C.eNu u x) (Z.eRR y) = (colOf R F sEE).B (C.wU u) x y := by
  first | exact @GlobalTheory.Mem.R3.pairing_eq_colPairing | exact GlobalTheory.Mem.R3.pairing_eq_colPairing | (intros; apply GlobalTheory.Mem.R3.pairing_eq_colPairing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionCompatibleAtReadIdentifications
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.divTied3_read : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → (Fintype.card G = D.what₂.restRowsFiniteGroupCard → Nat.card F.P0 = Nat.card F.P1 * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) → GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)) → DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C) ∧ (MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C)) := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C sEE Xd JM hP hH hGrp
  obtain ⟨hcard, hidx, hr, ht, hv0⟩ := GlobalTheory.Mem.R3.pins_card_index_ranks D G Pl0 I0 T A3 Ks R F cG hP
  obtain ⟨hsh, hba⟩ := GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  obtain ⟨hth, hthT⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  refine ⟨?_, ?_⟩
  · refine
      { ranks := ⟨rfl, hr, ht⟩
        grp := hGrp hcard hidx
        tup := ⟨Y.tup0, Y.muAt, hv0, Function.LeftInverse.injective (g := Y.tupT) Y.tupT_tup⟩
        mu1 := rfl
        sharp := hsh
        base := hba
        mt := ⟨Y.formsL, Y.latL⟩
        th := hth
        cols := ⟨C.bij, C.nu⟩ }
  · intro hMj hIdx hBu hBt
    obtain ⟨hRR1, hRR0⟩ := GlobalTheory.T.rowLattices_metrics_agree_of_realGroupTheorems hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
    exact
      { sharpRR := hRR1
        baseRR := hRR0
        divisionRows_rationalLift := GlobalTheory.T.zeroSubspace_spanned_by_dataZeroSubspace_lifts D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
        thTheta := hthT
        num := GlobalTheory.T.numbers_eq_concreteNumbers_at_baseLevel D G Pl0 I0 T A3 Ks R F cG X0 Y Z Xd JM hP hH hMj hIdx
        colsBk := GlobalTheory.T.rationalPairing_eq_columnPairing hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z C sEE hP hH hBu hBt }
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionCompatibleAtReadIdentificationsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionCompatible_at_readIdentifications : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → (Fintype.card G = D.what₂.restRowsFiniteGroupCard → Nat.card F.P0 = Nat.card F.P1 * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) → GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)) → DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C) ∧ (MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C)) := by
  first | exact @GlobalTheory.divTied3_read | exact GlobalTheory.divTied3_read | (intros; apply GlobalTheory.divTied3_read <;> assumption)
end
end
