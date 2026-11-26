module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfCore

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsRationalIffRecord
noncomputable section

open Module NumberField
open scoped InnerProductSpace

namespace GlobalTheory.LiftTestCompare

section Lin

open Matrix

variable {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

end Lin

section Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem liftTest_of_liftTestB {b : Bool} (h : LiftTestB X b) : LiftTest X := fun j => by
  obtain ⟨N, ψ, h1, h2, -⟩ := h j
  exact ⟨N, ψ, h1, h2⟩

end Cx

section Real

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

end Real

section ArchimedeanLeafBounds

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem toCx3_liftTestB (b : Bool) :
    LiftTestB (R.toCx3 F) b ↔ LiftTestB (cxPhase R.toRealDat F.lv2 fun j => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j)) b := by
  rw [cxPhase_eq]
  simp only [cj_cj]
  exact Iff.rfl

end ArchimedeanLeafBounds

end GlobalTheory.LiftTestCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfClassSumsSpan
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.LiftSpan

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}




end GlobalTheory.LiftSpan

namespace GlobalTheory.LiftSpan

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples GlobalTheory.OneMapAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


section Guard

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}


set_option maxHeartbeats 1000000 in
theorem lam_geo_mem_span {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {lam : AutQ (Wc D i) → ℂ} {z : G} {c0 : ℂ} (hid : PtIdent O κ lam z c0) :
    ∀ f ∈ cuspOver O κ, (fun q => lam q * geo O (fun _ => 1) z f q) ∈ Submodule.span ℂ (Set.range (liftQ R i v₀ A.μ0)) := by
  obtain ⟨ζ, -, hζ, h⟩ := hid ()
  intro f hf
  have hf' := hspan hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨hg, x, hx, hgx⟩ := hg
    obtain ⟨y, hy⟩ := lift_of_plc hP hx
    have e : (fun q => lam q * geo O (fun _ => 1) z g q) = (c0 / ζ) • liftQ R i v₀ A.μ0 y := by
      funext q
      rw [Pi.smul_apply, smul_eq_mul, ← hy, div_mul_eq_mul_div, eq_div_iff (ne_zero_of_root hζ),
        h x hx g ((mem_cusp _ _ _ _ _ _).1 hg).1 hgx q]
      show lam q * (1 * rdQ O z g q) * _ = _
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  | zero =>
    have e : (fun q => lam q * geo O (fun _ => 1) z 0 q) = 0 := funext fun q => by
      have := geo_smul O (fun _ => 1) z 0 0 q
      rw [zero_smul] at this
      rw [this]
      simp
    rw [e]
    exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    convert Submodule.add_mem _ hf hg using 1
    funext q
    rw [geo_add, mul_add, Pi.add_apply]
  | smul a f _ hf =>
    convert Submodule.smul_mem _ (a : ℂ) hf using 1
    funext q
    rw [geo_smul, mul_left_comm, Pi.smul_apply, smul_eq_mul]


set_option maxHeartbeats 1000000 in
theorem liftsSpan_of_ptIdent {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {O' : OMDat T.toCore R i T0 id} (hP' : O'.Pins κ v₀ ι x₀) (hlev : O'.lev = O.lev) (hex : ClsEx O' κ)
    {lam : AutQ (Wc D i) → ℂ} {z : G} {c0 c1 : ℂ} (hc1 : c1 ≠ 0) (hid : PtIdent O κ lam z c0) (hid' : PtIdent O' κ lam z c1) :
    LiftsSpan R i v₀ := by
  intro t y
  have e2 : O'.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  obtain ⟨x, hx, e⟩ := plc_of_lift hP' t y
  obtain ⟨f, hf, hfx, -⟩ := hex t x hx
  obtain ⟨s, -, -, h⟩ := hid' t
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O'.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hf
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have key : liftQ R i v₀ t y = ∑ k, (s / c1 * (as k : ℂ)) •
      fun q => lam q * geo O (fun _ => 1) z (GlobalTheory.FieldBC.rulBC O.hle (fs k)) q := by
    funext q
    have h1 : c1 * O'.thAd t x q = s * lam q * rdQ O' z f q := h x hx f hf' hfx q
    have h2 : 1 * rdQ O' z f q = _ := geo_of_isBC O' hP'.act.1 (fun _ => 1) z hf' hs hBC q
    rw [phi_eq O' O (fun _ _ => 1), e2, one_mul] at h2
    have h3 : ∀ k, geo O (fun _ => 1) z (GlobalTheory.FieldBC.rulBC O.hle (fs k)) q =
        O.phi (fun _ => 1) (actLev T.Q.c O.lev2 z (fs k)) q.out := fun k => by
      have hs1 : ∀ k', ![fs k] k' ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k' => by
        rw [Subsingleton.elim k' 0]; exact hs k
      rw [geo_of_isBC O hP.act.1 _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec O.hle (hs k)) hs1
        (GlobalTheory.FieldBCModel.isBC_rulBC O.hle (hs k).1)]
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero, OneMemClass.coe_one, one_mul]
    refine mul_left_cancel₀ hc1 ?_
    rw [show liftQ R i v₀ t y = O'.thAd t x from e.symm, h1, h2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [key]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (lam_geo_mem_span hP hspan hid _
    (((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ O.hle _ (T.U ((i : ℕ) + 1)) _ _ _ (hs k)).2).2 (hfs k)))

end Guard


end GlobalTheory.LiftSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftTestBOfRatG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open GlobalTheory.LiftTestCompare GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.LiftRat Formalism.IndefR.Cx Formalism.IndefR.Rat

namespace GlobalTheory.TwistField

section Read

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def readBasis (hU : R.LUnif) (i : Fin D.R.m) :
    Module.Basis (Fin (R.nW i)) ℂ (Tw (twAt D.what₂.embLL A.v0) (R.HW i (sg0 D A)).H) :=
  Module.Basis.mk (Tw.linInd _ ((hU i (sg0 D A)).1 _ _ (Pi.basisFun D.what₂.LL (Fin (R.nW i))).linearIndependent))
    (Tw.span_top _ (span_basis R hU i (sg0 D A))).ge

theorem readBasis_coord (hU : R.LUnif) (i : Fin D.R.m) (y : Fin (R.nW i) → D.what₂.LL) (k : Fin (R.nW i)) :
    (readBasis R hU i).coord k (Tw.mk (twAt D.what₂.embLL A.v0) ((R.FW i).j (sg0 D A) y)) = A.v0.embedding (y k) := by
  have h1 : Tw.mk (twAt D.what₂.embLL A.v0) ((R.FW i).j (sg0 D A) y) = ∑ l, A.v0.embedding (y l) • readBasis R hU i l := by
    rw [j_eq_sum]
    refine Finset.sum_congr (M := (R.HW i (sg0 D A)).H) rfl fun l _ => ?_
    rw [readBasis, Module.Basis.mk_apply]
    show _ = cj (twAt D.what₂.embLL A.v0) (A.v0.embedding (y l)) •
      (R.FW i).j (sg0 D A) (Pi.basisFun D.what₂.LL (Fin (R.nW i)) l)
    rw [emb_eq D.what₂.embLL A.v0, cj_cj]
  rw [h1, Module.Basis.coord_apply, Module.Basis.repr_sum_self]

end Read

theorem liftTestB_of_ratG : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool), R.toRealDat.LUnif → GlobalTheory.TwistField.RatG R.toRealDat (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) b := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F b hU hG
  rw [toCx3_liftTestB]
  intro j
  refine ⟨R.toRealDat.nW j, fun k => (readBasis R.toRealDat hU j).coord k,
    fun w hw => (readBasis R.toRealDat hU j).forall_coord_eq_zero_iff.1 hw, ?_, ?_⟩
  · intro t k x
    obtain ⟨y, hy⟩ := hG j t x
    refine ⟨y k, ?_⟩
    show _ = (readBasis R.toRealDat hU j).coord k (Tw.mk (twAt D.what₂.embLL A3.A.v0)
      (cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.toRealDat.thG j t (R.toRealDat.jV j t x)))
    rw [← hy, readBasis_coord]
    rfl
  · intro k (l : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b j)))
    refine ⟨R.toRealDat.bL F.lv2 b j l k, ?_⟩
    have hc : cpt A3.A.v0.embedding (Pi.single l (1 : D.what₂.LL)) = Pi.single l 1 := by
      funext r
      by_cases h : r = l
      · subst h; simp [cpt]
      · simp [cpt, Pi.single_apply, h]
    have h : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.toRealDat.HW j (sg0 D A3.A)).H)
        ((R.toRealDat.toCx F.lv2).w0C b j (Pi.single l 1)) = (R.toRealDat.FW j).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b j l) := by
      have h0 := liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 b j (Pi.single l 1)
      have e1 : ∑ k, (Pi.single l (1 : D.what₂.LL) : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b j)) → D.what₂.LL) k • R.toRealDat.bL F.lv2 b j k = R.toRealDat.bL F.lv2 b j l := by
        simp [Pi.single_apply]
      rw [e1] at h0
      refine Eq.trans ?_ h0
      erw [hc] <;> rfl
    show _ = (readBasis R.toRealDat hU j).coord k (Tw.mk (twAt D.what₂.embLL A3.A.v0)
      (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.toRealDat.HW j (sg0 D A3.A)).H)
        ((R.toRealDat.toCx F.lv2).w0C b j (Pi.single l 1))))
    rw [h, readBasis_coord]
    rfl

end GlobalTheory.TwistField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovarianceAtConstantXi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovarianceAtConstantXi
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtIdCore

theorem exists_scalar_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W), ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0' → GlobalTheory.PtId.IoAt O (v₀ i (sg0 D A)) ka := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT hI i c0L
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧ CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0'
  swap
  · exact ⟨1, norm_one, fun Tp tup O h1 h2 => absurd ⟨Tp, tup, O, h1, h2⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀, hB₀⟩ := hex
  obtain ⟨ka₀, hn₀, hk₀⟩ := GlobalTheory.AdTh.PhaseMap.io_eq_phase_smul_ofCore D G Pl0 T0 A T R F κ v₀ hC hT hI i Tp₀ tup₀ O₀ hP₀
  refine ⟨ka₀, hn₀, fun Tp tup O hP hB => ?_⟩
  obtain ⟨ka, -, hk⟩ := GlobalTheory.AdTh.PhaseMap.io_eq_phase_smul_ofCore D G Pl0 T0 A T R F κ v₀ hC hT hI i Tp tup O hP
  intro lt hlt u hu
  suffices h : ka = ka₀ by
    subst h
    exact hk lt hlt u hu
  have e1 := hk lt hlt u hu A.μ0 O.hw
  have e2 := hk₀ lt hlt u hu A.μ0 O₀.hw
  obtain ⟨hw1, cga, -, hinj, -, -, -, -, hio, -⟩ := hP.io
  obtain ⟨hw2, cga', -, -, -, -, -, -, hio₀, -⟩ := hP₀.io
  have hne : O.io O.hw ≠ 0 := by
    intro h0
    have h1 : O.hw = 0 := hinj (h0.trans (map_zero _).symm)
    have h2 := (GlobalTheory.AdTh.coefMap_norm_equivariant_basis_ofCore D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP).1
    rw [h1, map_zero, norm_zero] at h2
    exact zero_ne_one h2
  rw [GlobalTheory.PtId.OneScalar.coefficientMap_extremalTensor_baseChange O hw1 hB] at e1
  rw [GlobalTheory.PtId.OneScalar.coefficientMap_extremalTensor_baseChange O₀ hw2 hB₀, hio₀, GlobalTheory.PtId.OneScalar.map_pG_eq O₀.c' O.c' (inC O₀.c') (inC O.c'), ← hio, e1] at e2
  have hV := hP.lift.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := GlobalTheory.AdTh.VecFock.vec_fock_ofCore D G Pl0 T0 A T.Q.c.F R F hC i A.μ0 hV
  have hON : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ => by
    refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩
    · simp [gramAt, hV.1]
    · simp
  have hinjP := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hC.thP.ωP i A.μ0).std hC.models.inf
    (fun _ => 1) (fun _ => 1) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ f4 f3 hON f5
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) f1 f2 (GlobalTheory.AdTh.VecNe.thetaVector_ne_zero_of_core D G Pl0 T0 A T.Q.c.F R F hC i hV)
  have hlti : Function.Injective lt := GlobalTheory.PtId.OneScalar.lt_injective (fun ρ => hT.laws.pins.1.2.2.2 ρ) lt hlt
  refine smul_left_injective ℂ (fun h0 => hne ?_) e2
  have h1 := hinjP (h0.trans (map_zero _).symm)
  have h2 := MvPolynomial.rename_injective lt hlti (h1.trans (map_zero _).symm)
  exact MvPolynomial.map_injective _ (inC O.c').injective (h2.trans (map_zero _).symm)


open GlobalTheory.AdTh.CoverVal in
theorem covAt_of_xiConst_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ c0 : ℂ, GlobalTheory.OneMapTuples.XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → GlobalTheory.PtId.CovAt O c0 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup O hO c0 hc
    t X g bas idx e k xk mk hX hp hs hi hL hxk hmk hk y₂ A₂ hA₂
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc t
  obtain ⟨hlev, hA, -⟩ := hO.cov t
  obtain ⟨hX₀, hon₀, -, hp₀, -, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_ofCore D G Pl0 T0 A T R F κ v₀ hR hT i O.s0
    (sOv_eq _ _ _) (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ t).c₂ ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ t).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ t).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  obtain ⟨Wt⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU)
  obtain ⟨hon, γ, ⟨hγ, hl, hf⟩, hma, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (O.U₂ t) hσ hU h1 hA R.θ (Wc D i)
    (rank_Wc i) (O.dict₂ t) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt k
  obtain ⟨hd, hpt⟩ := point_eq (Formalism.L2.PjFree.Unf.ofPj (O.U₂ t)) hσ hU h1 hA hR.models.inf (Wc D i) (rank_Wc i) (iotaW T i)
    _ Wt (O.dict₂ t k).1 (O.dict₂ t k).2 γ k hγ (hmod _) hl hf hon hma X g bas idx e mk hX hp hs hi hL hmk hk y₂ A₂ hA₂
  obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 k
  obtain ⟨-, -, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  obtain ⟨a, ha⟩ := hrat γ' hγ'
  have hv := hval k γ' ⟨hγ', h2, h3⟩
  rw [(hO.tuple t).xi _ _ (hmul _ _ _ _ ha hxk), map_mul, (hR.lev.xi (tup t)).1.2 a, _root_.one_mul] at hv
  exact (evR_eq_of_point _ hlev.2.2.2.2.2.2.2.1 _ y₂ hpt).trans ((dif_pos hd).symm.trans hv)


set_option maxHeartbeats 2000000 in
open Formalism.L2.DIV GlobalTheory.OneMapTuples GlobalTheory.PtId in
theorem point_identity_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → IoExt R → ∀ (i : Fin D.R.m) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ (lam : AutQ (Wc D i) → ℂ) (z : G), (∀ q, lam q ≠ 0) ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → O.lev = lev → CoefficientBaseChange R i O.jL (inC O.c') (c0L i) O.c0' → ∀ c0 : ℂ, XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → PtIdent O (κ i) lam z c0 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ _ ⟨tie⟩ _ hio i lev gramR c0R c0L _
  have hT : TieIn T R κ v₀ := ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)
  swap
  · exact ⟨fun _ => 1, 1, fun _ => one_ne_zero, fun Tp tup O _ hP => absurd ⟨Tp, tup, O, hP⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀⟩ := hex
  obtain ⟨ka, hka1, hka⟩ := exists_scalar_core D G Pl0 T0 A T R F κ v₀ hC hT hio i (c0L i)
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.AdTh.CcEx.exists_ccIs_ofCore GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R F κ v₀ hC hT i Tp₀ tup₀ O₀ hP₀
  have hs₀ : O₀.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hemb, hiso, -⟩ := dict_cast T hT.laws _ (inR i) O₀.s0 (hs₀ ▸ T.toCore.good_σ₀) (Wc D i) O₀.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.AdTh.ShortSeries.thetaKO_eq_short_series_ofCore D G Pl0 T0 A _ R F hC i hP₀.lift.std _ _ (iotaW T i) hemb hiso
  refine ⟨fun q => cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * c₀ (O₀.dict q.out).1, 1, fun q => ?_, ?_⟩
  · exact mul_ne_zero (cmpConst_ne_zero (norm_ne_zero_iff.1 (hka1 ▸ one_ne_zero)) _ _)
      (norm_ne_zero_iff.1 (hc₀.1 _ ▸ one_ne_zero))
  intro Tp tup O _ hP _ hbc c0 hxi t
  obtain ⟨cst, hcst, hceq⟩ := ccIs_transport (hs₀.trans (sOv_eq _ O.c' O.hle).symm) O₀.hV O.hV hc₀
  refine ⟨1, one_mem _, ⟨1, Nat.one_pos, one_pow _⟩, fun x hx f hf hcl q => ?_⟩
  obtain ⟨h, J', hR, -, hA, hPl⟩ := (hP.tuple t).reps
  obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
  have hL := hP.act.2
  have h1 : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2 1 f = f :=
    actL_one _ _ _ hL.total hL.func hL.one hf.1
  have h2 := exact_identity_ofCore hC hT O hP (hka Tp tup O hP hbc) hδ
    (covAt_of_xiConst_core D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP c0 hxi) hcst t h J' hR _ x hx₀ f hcl q.out
  rw [rdQ, h1, hA _ x hx₀, one_mul]
  exact h2.trans (congrArg (fun z => _ * z * _) (hceq q.out))

end GlobalTheory.PtIdCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovarianceAtConstantXiStatement
open NumberField Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj GlobalTheory.OneMapTuples
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLift_eq_factor_mul_geometricClassSum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → IoExt R → ∀ (i : Fin D.R.m) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ (lam : AutQ (Wc D i) → ℂ) (z : G), (∀ q, lam q ≠ 0) ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → O.lev = lev → CoefficientBaseChange R i O.jL (inC O.c') (c0L i) O.c0' → ∀ c0 : ℂ, XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → PtIdent O (κ i) lam z c0 := by
  first | exact @GlobalTheory.PtIdCore.point_identity_core | exact GlobalTheory.PtIdCore.point_identity_core | (intros; apply GlobalTheory.PtIdCore.point_identity_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceTupleLiftsSpanAllTuples
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceTupleLiftsSpanAllTuples
noncomputable section

namespace GlobalTheory.LiftSpanClauses

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.OneMapTuples GlobalTheory.OneMapAll
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cls

open GlobalTheory.PinnedClassSum GlobalTheory.GeoLevel GlobalTheory.Member Formalism.L2.Host


set_option maxHeartbeats 2000000 in
theorem clsEx_of_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsFam → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → GlobalTheory.OneMapTuples.ClsEx O (κ i) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hF ⟨tie⟩ _ i Tp tup O hLL hO t x _
  have hT := tie.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hr : 1 ≤ D.R.r := by
    have h1 := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2.1
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  obtain ⟨hd, hA₂, hnab⟩ := hO.cov t
  obtain ⟨-, -, hxi, ⟨e, -, hφ⟩, hMb, hQ, -⟩ := hO.tuple t
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hO.cxi
  obtain ⟨n, hn, ho⟩ := hL.xi_fin (tup t)
  obtain ⟨xi', hx1, -, hx3, hx4⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi (tup t)) (R.xiH (tup t)) (hL.xi _) n hn ho
    (hL.xi_triv _) (hL.xi_tame _)
  have hxx : ∀ g : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) =
      xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) := fun g => by
    obtain ⟨z, hz⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 g
    exact Units.ext ((hxi g z hz).trans (hx1 g z hz).symm)
  have hxN : ∀ g : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) ^ (m * n) = 1 := fun g => by
    rw [hxx, mul_comm, pow_mul, hx4, one_pow]
  have hcN : c0 ^ (m * n) = 1 := by rw [pow_mul, hc0, one_pow]
  obtain ⟨gramR, c0R, c0L, hfam⟩ := hF.tie
  obtain ⟨ψ, hψ⟩ := exists_psi (Wc D i) (O.dδ t) (iotaW T i) hio.emb (hpq.trans (rank_Wc i).symm) hpos hd (R.Q (tup t)) hQ
    (R.xiR (tup t)) fun P hP z =>
      hLL (GlobalTheory.RationalValues.xiR_mem R hL hF.pl_onto hF.muVal hfam.ok i (tup t) P hP z)
  have htie : (O.dδ t).PsiTie ψ := by
    refine psiTie_of_values (Wc D i) (O.dδ t) (rank_Wc i) _ hio hpos _ hx₀ hd hA₂ (O.xi t) _ (Nat.mul_pos hm hn) hxN
      (fun γ hγ => (hxx γ).trans (hx3 γ hγ)) _ _ c0 hcN (hv t) ψ fun k s u hu₀ hu hk hlift => ?_
    obtain ⟨y, -, hdet⟩ := exists_int_matrix (hL.βW i) hu
    have hres : ∀ P : R.Q (tup t), ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc (resS D.host.F P.1) y) : (kP P.1)ˣ) : kP P.1) =
        resS D.host.F P.1 y.1.det := fun P => ((resS D.host.F P.1).map_det _).symm
    obtain ⟨z, hz, hval⟩ := exists_root_value (O.dδ t).l₂ hu₀ (hL.xi (tup t)) (hL.xi_tame _) (R.Q (tup t)) (R.xiR (tup t))
      (hL.xiR _) (fun P hP => (hd.2.2.2.1.le.trans Ideal.mul_le_right).trans (hQ P hP)) (fun P => (hL.Q_ram _ P).1) _ hdet _ hres
    exact (hψ k s u _ hk hlift hdet _ hres).trans (hval.symm.trans (hxi u z hz).symm)
  have hτ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n
    have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos
    omega)
  obtain ⟨τ₀⟩ := hτ
  have hnV : (κ i).n = (Vc D i).rank := (tie.kap i τ₀).2.2.trans (D.sp.V_rank _ hj.1 hj.2).symm
  have hlast : (κ i).LastPos := fun τ k hk => by
    rw [(tie.kap i τ).1 k, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    refine GlobalTheory.LiftWeight.one_le_aPl_last D i τ _ _ ?_ hk
    simp only [Ranks.sigW]
    omega
  obtain ⟨-, cga, -, -, hrange, -⟩ := hO.io
  exact GlobalTheory.ClsVal.exists_cusp_isThClsD_unique GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ (O.dδ t) _ _ hr
    (fun σ hσ' => GlobalTheory.OneMapAll.isUnf_unfExt O.hle σ (fun _ => rfl) (hT.unf _ hj (σ.comp (incF T.Q.c O.c' O.hle)) hσ')) hT.pins.2.1.2
    (fun _ => ⟨hd, hA₂, hnab⟩)
    (GlobalTheory.OneMapTuples.unitC_of_cXiAt D _ _ (Wc D i) _ _ _ _ _ (O.dδ t) (rank_Wc i) _ hio hpos _ hx₀ hd hA₂ (O.xi t) _ (Nat.mul_pos hm hn) hxN
      _ _ c0 hcN (hv t))
    ψ htie _ (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.bad t) (O.vol t) (O.ep t) _ O.io (wtA (κ i)) (hnV ▸ dom_wtA (κ i))
    (GlobalTheory.lastPos_wtA_of_pins D T.Q hT.pins _ hj _ hlast)
    (fun k => datEq_of_values (Vc D i) (Wc D i) (R.βV i) (R.βW i) (hL.βW i) e (O.dδ t) hd _ hio R.Pg (R.Q (tup t))
      (fun P hP => hMb.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hP))) hQ _ (O.φ t) _ (hO.w t k)
      (fun z => (hφ z).1) (fun z => (hφ z).2) ψ hψ)
    (hO.reps t).1 hrange.le x

end Cls

section Retie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem placeEx_core {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    {v₀ : (R.MW i (sg0 D A)).Vec} {c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W}
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {M : ℕ} {Mh : Ideal (𝓞 D.host.E)} {lev : G → La →ₗ[𝓞 D.host.E] La} (hP : ThPinsR R i jL σ' v₀ c0' ι M Mh lev)
    (t : T0) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i)) : PlaceEx R i t h c0' := by
  obtain ⟨_, _, _, hT, hc⟩ := hP.c0
  exact GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hR.models.jV hT hc hR.lev hR.grp.chiW hR.fam.pl_onto hR.fam.muVal

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}


set_option maxHeartbeats 1600000 in
theorem exists_retie_core {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (hP : O.Pins κ v₀ ι x₀)
    (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
    (hlev : LevIs R i ι C.Q.l.M (Mfr C.Q.l) lev)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c fun g => (lev g, LinearMap.id)) {gramR c0R c0L}
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L) :
    ∃ O' : OMDat C R i Tp tup, O'.c' = O.c' ∧ O'.Pins κ v₀ ι x₀ ∧ O'.lev = lev ∧ CoefficientBaseChange R i O'.jL (inC O'.c') (c0L i) O'.c0' := by
  classical
  obtain ⟨c1, hc1⟩ := exists_coef_ext (W := (R.cV i).W) O.jL hP.lift.field (lamV D i) (c0L i)
  choose h J' h1 h2 h3 h4 using fun t => (hP.tuple t).reps
  have hL : ThPinsR R i O.jL (inC O.c') v₀ c1 ι C.Q.l.M (Mfr C.Q.l) lev :=
    ⟨hP.lift.field, hP.lift.std, hP.lift.v0, ⟨_, _, _, hT, hc1⟩, hlev⟩
  have h0 : ∀ t y, (∀ k, (R.HV i (tup t)).e y (fin _ (h t k)) = 0) → onQ (Wc D i) (R.thF i (tup t) y v₀) = 0 := fun t y hy => by
    have e1 := h3 t y 0 fun k => (hy k).trans (map_zero _).symm
    have e2 := h3 t 0 0 fun k => by rw [map_zero]; exact (map_zero _).symm
    rw [← e1, e2, map_zero]
    rfl
  refine ⟨{ O with
    c0' := c1, lev := lev
    thAd := fun t x => if hx : ∃ y, Place R i (tup t) (h t) c1 y x then onQ (Wc D i) (R.thF i (tup t) hx.choose v₀) else 0
    Plc := fun t x => ∃ x₀, Place R i (tup t) (h t) c1 (jVx R i (tup t) x₀) x }, rfl,
    ⟨hL, fun t => ⟨⟨h t, J' t, h1 t, placeEx_core R F hR i _ _ hL _ _, fun y x hy => ?_, fun x => Iff.rfl⟩,
      (hP.tuple t).B, (hP.tuple t).xi, (hP.tuple t).phi, (hP.tuple t).half⟩,
      ⟨hact, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).1⟩,
      hP.bad, hP.reps, hP.ep, hP.io, hP.w, hP.cov, hP.cxi, hP.model₂⟩, rfl, hc1⟩
  have hx : ∃ y, Place R i (tup t) (h t) c1 y x := ⟨y, hy⟩
  refine (dif_pos hx).trans ?_
  have h5 := h0 t (hx.choose - y) fun k => by
    rw [map_sub, Pi.sub_apply, hx.choose_spec k, hy k, sub_self]
  rw [map_sub] at h5
  exact sub_eq_zero.1 h5

end Retie

def PointIdentCore : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → IoExt R → ∀ (i : Fin D.R.m) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ (lam : AutQ (Wc D i) → ℂ) (z : G), (∀ q, lam q ≠ 0) ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → O.lev = lev → CoefficientBaseChange R i O.jL (inC O.c') (c0L i) O.c0' → ∀ c0 : ℂ, XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → PtIdent O (κ i) lam z c0

section Guard

open GlobalTheory.LiftSpan

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


set_option maxHeartbeats 2000000 in
theorem liftsSpan_of_guard_core (hPI : PointIdentCore) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) (hR : GlobalTheory.Hk3.Core R F) (h1 : R.tup_mu_off) (h2 : R.tup_mu_used) (hW : Nonempty (FWTie T R κ v₀))
    (hpb : T.pb = R.C.P.pb) (hio : IoExt R) (hO : OMPins T R κ v₀ O i) (hex : PinsExist T R κ v₀ i) (hG : QGuard R)
    (hspan : ClassSumsSpan (O i) (κ i)) : LiftsSpan R i (v₀ i (sg0 D A)) := by
  have hP : (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hO.2
  obtain ⟨gramR, c0R, c0L, hFT, hc⟩ := hP.lift.c0
  obtain ⟨lam, z₀, -, hU⟩ := hPI D G Pl0 T0 A T R F κ v₀ hR h1 h2 hW hpb hio i (O i).lev gramR c0R c0L hFT
  obtain ⟨O₀, hle₀, hP₀⟩ := hex hG
  obtain ⟨O₁, e₁, hP₁, hlev₁, hc₁⟩ := exists_retie_core O₀ hR
    (show O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) from hP₀) (O i).lev hP.lift.lev hP.act.1 hFT
  have hle₁ : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O₁.c'.F := e₁ ▸ hle₀
  obtain ⟨c0, -, hx⟩ := hP.cxi
  obtain ⟨c1, hr₁, hx₁⟩ := hP₁.cxi
  exact liftsSpan_of_ptIdent hP hspan hP₁ hlev₁ (clsEx_of_core D G Pl0 T0 A T R κ v₀ hR.lev hR.fam hW hpb i _ _ O₁ hle₁ hP₁)
    (ne_zero_of_root hr₁) (hU _ _ (O i) hO.1.ge hP rfl hc c0 hx) (hU _ _ O₁ hle₁ hP₁ hlev₁ hc₁ c1 hx₁)

end Guard

end GlobalTheory.LiftSpanClauses

namespace GlobalTheory.LiftSpanClauses

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem liftsSpan_all_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i → QGuard R → GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hsz hC h1 h2 hW hio hO h0 hG
  obtain ⟨fw⟩ := id hW
  have hpb : T.pb = R.C.P.pb := GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R fw.laws.toLawsM hC.lev (hO.2.tuple ()).half
  have hex : GlobalTheory.OneMapTuples.PinsExist T R κ v₀ i := fun hG' => by
    obtain ⟨O', a, b, -⟩ := GlobalTheory.PinnedTuples.exists_pins_of_base D G Pl0 T0 A T R κ v₀ O hC.lev hC.grp.chiW hC.fam hC.models
      hC.thP.vP h1 h2 hW i hO hG'
    exact ⟨O', a, b⟩
  exact liftsSpan_of_guard_core GlobalTheory.T.adelicLift_eq_factor_mul_geometricClassSum T R F κ v₀ O i hC h1 h2 hW hpb hio hO hex hG
    (GlobalTheory.ClassSumSpanCore.classSumsSpan_core D G Pl0 T0 A T R F κ v₀ O hsz hC hW hio i hO h0)

end GlobalTheory.LiftSpanClauses
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceTupleLiftsSpanAllTuplesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_lifts_span_all_tuples : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i → QGuard R → GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) := by
  first | exact @GlobalTheory.LiftSpanClauses.liftsSpan_all_clauses | exact GlobalTheory.LiftSpanClauses.liftsSpan_all_clauses | (intros; apply GlobalTheory.LiftSpanClauses.liftsSpan_all_clauses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftsOfRationalFormsRationalOfClauses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapAllTuplesCoeffFieldOfClauses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapAllTuplesCoeffFieldOfClauses
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.TwistField

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem oneMapOverL_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)
    (hC : GlobalTheory.Hk3.Core R F) (h1 : R.tup_mu_off) (h2 : R.tup_mu_used) (hW : Nonempty (FWTie T R κ v₀)) (hpb : T.pb = R.C.P.pb)
    (hO : OMPins T R κ v₀ O i) (hph : PhaseTie T R κ v₀ O ph i) (hio : IoExt R) (h0 : OneMapRow0 T R κ v₀ O i)
    (hex : PinsOverL T R κ v₀ i) (hsp : LiftsSpan R i (v₀ i (sg0 D A))) : OneMapOverL T R κ v₀ (ph i) i := by
  have hrow := hph h0
  obtain ⟨w⟩ := id hW
  have hT := w.laws
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := (O i).hV
  have hn : (κ i).n = (Vc D i).rank :=
    (w.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have hP : (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hO.2
  obtain ⟨gramR, c0R, c0L, hFT, hc⟩ := hP.lift.c0
  obtain ⟨lam, z₀, hlam, hU⟩ := GlobalTheory.T.adelicLift_eq_factor_mul_geometricClassSum D G Pl0 T0 A T R F κ v₀ hC h1 h2 hW hpb hio i (O i).lev gramR c0R c0L hFT
  obtain ⟨O₀, hF₀, hP₀⟩ := hex
  obtain ⟨O₁, e₁, hP₁, hlev₁, hc₁⟩ := GlobalTheory.LiftSpanClauses.exists_retie_core O₀ hC
    (show O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) from hP₀) (O i).lev hP.lift.lev hP.act.1 hFT
  have hF₁ : O₁.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange := e₁ ▸ hF₀
  have hle₁ : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O₁.c'.F := hF₁.ge
  obtain ⟨c0, hr, hx⟩ := hP.cxi
  obtain ⟨c1, hr₁, hx₁⟩ := hP₁.cxi
  have hid := hU _ _ (O i) hO.1.ge hP rfl hc c0 hx
  have hid₁ := hU _ _ O₁ hle₁ hP₁ hlev₁ hc₁ c1 hx₁
  have hE₁ := GlobalTheory.LiftSpanClauses.clsEx_of_core D G Pl0 T0 A T R κ v₀ hC.lev hC.fam hW hpb i _ _ O₁ hle₁ hP₁
  have n0 := ne_zero_of_root hr
  have n1 := ne_zero_of_root hr₁
  by_cases hz : ∀ y, liftQ R i (v₀ i (sg0 D A)) A.μ0 y = 0
  · exact ⟨O₁, hF₁, hP₁, oneMapOf_of_ptIdent hT hV hn hP hrow hle₁ hP₁ hlev₁ hE₁ hsp hlam n0 n1 hid hid₁ (Or.inr hz)⟩
  · obtain ⟨y, hy⟩ := not_forall.1 hz
    have hu := const_ratio_mem hT hV hn hO.1 hP hrow hle₁ hP₁ hlev₁ hE₁ hlam n1 hid hid₁ hy
    have e : ((⟨c0 / c1, hu⟩ : O₁.c'.F) : ℂ) * c1 = c0 := div_mul_cancel₀ _ n1
    have hx₂ := xiConst_scaleXi O₁ ⟨c0 / c1, hu⟩ hx₁
    have hP₂ := pins_scaleXi O₁ ⟨c0 / c1, hu⟩ (fun h => div_ne_zero n0 n1 (congrArg Subtype.val h)) hx₁ (e.symm ▸ hr) hP₁
    rw [e] at hx₂
    exact ⟨scaleXi O₁ ⟨c0 / c1, hu⟩, hF₁, hP₂, oneMapOf_of_ptIdent (O' := scaleXi O₁ ⟨c0 / c1, hu⟩) hT hV hn hP hrow hle₁ hP₂ hlev₁
      (GlobalTheory.LiftSpanClauses.clsEx_of_core D G Pl0 T0 A T R κ v₀ hC.lev hC.fam hW hpb i _ _ (scaleXi O₁ ⟨c0 / c1, hu⟩) hle₁ hP₂) hsp hlam n0 n0 hid
      (hU _ _ (scaleXi O₁ ⟨c0 / c1, hu⟩) hle₁ hP₂ hlev₁ hc₁ c0 hx₂) (Or.inl rfl)⟩

end GlobalTheory.TwistField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapAllTuplesCoeffFieldOfClausesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneFormMap_allTuples_coeffField_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → IoExt R → OneMapRow0 T R κ v₀ O i → GlobalTheory.TwistField.PinsOverL T R κ v₀ i → GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) → GlobalTheory.TwistField.OneMapOverL T R κ v₀ (ph i) i := by
  first | exact @GlobalTheory.TwistField.oneMapOverL_of_clauses | exact GlobalTheory.TwistField.oneMapOverL_of_clauses | (intros; apply GlobalTheory.TwistField.oneMapOverL_of_clauses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataOverRowFieldConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataOverRowFieldConditions
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinsOverClauses

open GlobalTheory.CoverHalf GlobalTheory.TwistField GlobalTheory.PinnedData GlobalTheory.PinsOverField
open scoped nonZeroDivisors

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (R : RealDat D A Ks) (i : Fin D.R.m)


set_option maxHeartbeats 1000000 in
theorem exists_phi_core {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (hV : VStd D i) (t : T0) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (hι : LatEmb (Wc D i) ι)
    (M : IntermediateField ℚ ℂ) (hM : M = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (J : Ideal (𝓞 D.host.E))
    (hJ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) :
    ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M, PhiIs R i M.val.toRingHom t ι (J • ⊤) φ := by
  have hv : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y ∈ M := fun y => by
    refine mul_mem ?_ ?_
    · unfold omegaK
      split_ifs
      exacts [one_mem _, zero_mem _]
    · unfold omegaQ
      split_ifs
      · exact prod_mem fun PP _ => zpow_mem (hM ▸ xiR_mem R hR.lev hR.fam t PP.1 PP.2 _) _
      · exact zero_mem _
  obtain ⟨-, e, he, -⟩ := hR.thP.vP i t
  have hβ := GlobalTheory.T.inverse_selfDual_frame_standard_space_integral D i _ _ hV (hR.lev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hR.lev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hv fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out)⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)


set_option maxHeartbeats 2000000 in
theorem pinsOverL_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hR _hoff _hused hfw hO hG hC
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  have hpb : T.pb = R.C.P.pb := GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hR.lev (hO.2.tuple ()).half
  obtain ⟨hc', hP⟩ := hO
  have hV : VStd D i := hP.lift.std
  have hB0 := (hP.tuple ()).B
  have hb0 := hP.bad ()
  have hjL := hP.lift.field
  have hlev := hP.lift.lev
  have hio := hP.io
  have hact := hP.act
  choose l₂ hl₁ hl₂ using exists_half_tupPrime T.toCore R hT.toLawsM hR.lev hpb hG
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ :=
    GlobalTheory.CoverOverField.coversAt D G Pl0 T0 A T R hT hR.lev hR.fam.roots
      (GlobalTheory.TwistValues.xiVal D G Pl0 T0 A _ R hR.lev hR.fam) hC i (Vc D i).rank _ l₂ hl₁ hl₂ (O i).c' (O i).hle hc'
  obtain ⟨gramR, c0R, c0L, hTie⟩ := hR.fam.tie
  obtain ⟨c0', hcb, hplace⟩ := GlobalTheory.Div.CoefExtension.exists_ext_placeEx D G Pl0 T0 A _ R hR.lev hR.grp.chiW hR.fam hR.models
    gramR c0R c0L hTie i (O i).c'.F (O i).jL (inC (O i).c') hjL
  have hc0 : ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i (O i).jL (inC (O i).c') (c0L i) c0' :=
    ⟨gramR, c0R, c0L, hTie, hcb⟩
  choose Cl fCl h J' bad Lh gam vol La Nc hrep hdv hvol hok hlat using fun t =>
    GlobalTheory.SplitReps.exists_repsR_repsOK R i (hR.lev.βV i) hV (O i).c'.F t (dδ t).l₂ hb0.1
  have hbad : ∀ t, 0 < bad t ∧ BadPin (bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1) := fun t =>
    ⟨Nat.pos_of_ne_zero (hrep t).1, hb0.2.1.trans (hdv t), hb0.2.2.1.trans (hdv t), hb0.2.2.2.1.trans (hdv t),
      hb0.2.2.2.2.trans (hdv t)⟩
  choose B hBis using fun t => exists_BIs R i hR.lev hR.fam (O i).c'.F hc' hB0 t (hdv t)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  choose φ hφis using fun t => exists_phi_core R i hR hV t (iotaW T i) (latEmb_iotaW T hT i) (O i).c'.F hc'
    (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => GlobalTheory.AdelicSide.exists_thAd_of_models D G Pl0 T0 A _ R hR.models i t _ _ c0' _ (h t) _
    (hrep t).2.2.1 (hrep t).2.2.2.2.2.1 (v₀ i (sg0 D A))
  refine ⟨{ c' := (O i).c', hle := (O i).hle, jL := (O i).jL, hV := (O i).hV, c0' := c0', lev := (O i).lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := (O i).io, hw := (O i).hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hc',
    ⟨hjL, hV, fw.hv₀ i _, hc0, hlev⟩,
    fun t => ⟨⟨h t, J' t, hrep t, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    hact, hbad, fun t => ⟨hok t, hlat t⟩, fun t => ⟨fun _ => rfl, hepF t⟩, hio,
    fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩

end GlobalTheory.PinsOverClauses
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataOverRowFieldConditionsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedTupleData_over_rowField_conditions : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  first | exact @GlobalTheory.PinsOverClauses.pinsOverL_of_clauses | exact GlobalTheory.PinsOverClauses.pinsOverL_of_clauses | (intros; apply GlobalTheory.PinsOverClauses.pinsOverL_of_clauses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftsOfRationalFormsRationalOfClauses
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField


set_option maxHeartbeats 2000000 in
theorem ratG_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → (∀ i, OMPins T R κ v₀ O i) → (∀ i, PhaseTie T R κ v₀ O ph i) → IoExt R → (∀ i, OneMapRow0 T R κ v₀ O i) → QGuard R → R.LUnif → EvInj T R v₀ → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.RatG R ph := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hC hoff hused hW hO hph hio h0 hQ hU hinj hcov i t x
  obtain ⟨fw⟩ := id hW
  have hpb : T.pb = R.C.P.pb := GlobalTheory.PinsFixHalf.pb_eq_of_pins T R κ v₀ O hC.lev fw.laws hO
  have hex : PinsOverL T R κ v₀ i := GlobalTheory.T.exists_normalisedTupleData_over_rowField_conditions D G Pl0 T0 A T R F κ v₀ O i hC hoff hused hW (hO i) hQ hcov
  have hsp : GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) :=
    GlobalTheory.T.referenceTuple_lifts_span_all_tuples D G Pl0 T0 A T R F κ v₀ O i hnV hC hoff hused hW hio (hO i) (h0 i) hQ
  have hone : OneMapOverL T R κ v₀ (ph i) i :=
    GlobalTheory.T.oneFormMap_allTuples_coeffField_of_clauses D G Pl0 T0 A T R F κ v₀ O ph i hC hoff hused hW hpb (hO i) (hph i) hio (h0 i) hex hsp
  have hev : fw.Evaluates := GlobalTheory.evaluates_of_unif D G Pl0 T0 A T R F κ v₀ fw hU
  have hrat := GlobalTheory.TwistField.Read.rat_of_oneMapOverL D G Pl0 T0 A T R F κ v₀ fw (ph i) i hC.lev hC.grp hC.models hC.thP hU
    hev hinj hone t x
  obtain ⟨y, -, hy⟩ := hrat
  exact ⟨_, hy.symm⟩

end GlobalTheory.TwistField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftsOfRationalFormsRationalOfClausesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLifts_of_rationalForms_rational_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → (∀ i, OMPins T R κ v₀ O i) → (∀ i, PhaseTie T R κ v₀ O ph i) → IoExt R → (∀ i, OneMapRow0 T R κ v₀ O i) → QGuard R → R.LUnif → EvInj T R v₀ → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.RatG R ph := by
  first | exact @GlobalTheory.TwistField.ratG_of_clauses | exact GlobalTheory.TwistField.ratG_of_clauses | (intros; apply GlobalTheory.TwistField.ratG_of_clauses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MLat3OfTie
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodLat.Obj3

theorem mLat3_of_tie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (fw : FWTie T R.toRealDat κ v₀) : (R.toCx3 F).MLat false :=
  fun j => GlobalTheory.GoodLat.Obj.mLat_of_tie fw F.lv2 false j

end GlobalTheory.GoodLat.Obj3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestsModularLatticeOfCoreCompatibility
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem liftTests_and_mLat_of_ties : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) ∧ Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false ∧ (R.toCx3 F).MLat false := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O hB hG
  obtain ⟨hCore, hOff, hUsed⟩ :=
    GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D G Pl0 I0 T0 A3 _ R F hB.char hB.ex
  obtain ⟨fw, -⟩ := hG.fw
  have hM : R.toRealDat.IsModels := hB.char.base.models
  have hEv : EvInj T R.toRealDat v₀ := GlobalTheory.EvalAtUnitVectorFinal.evInj_of_isModels_of_tie T R.toRealDat κ v₀ hM fw
  have hRat : GlobalTheory.TwistField.RatG R.toRealDat (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) :=
    GlobalTheory.T.thetaLifts_of_rationalForms_rational_of_clauses D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O _ hB.nV hCore hOff hUsed ⟨fw⟩ hG.pins
      (fun i => hG.phase i hG.unif) hG.ioExt (fun i => (hG.oneMap i).1) hB.guard hG.unif hEv hG.cover
  have hLB : Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false :=
    GlobalTheory.TwistField.liftTestB_of_ratG D G Pl0 I0 T0 A3 _ R F false hG.unif hRat
  exact ⟨GlobalTheory.LiftTestCompare.liftTest_of_liftTestB _ hLB, hLB,
    GlobalTheory.GoodLat.Obj3.mLat3_of_tie T R F κ v₀ fw⟩

end GlobalTheory.PrimIn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestsModularLatticeOfCoreCompatibilityStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) ∧ Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false ∧ (R.toCx3 F).MLat false := by
  first | exact @GlobalTheory.PrimIn.liftTests_and_mLat_of_ties | exact GlobalTheory.PrimIn.liftTests_and_mLat_of_ties | (intros; apply GlobalTheory.PrimIn.liftTests_and_mLat_of_ties <;> assumption)
end
