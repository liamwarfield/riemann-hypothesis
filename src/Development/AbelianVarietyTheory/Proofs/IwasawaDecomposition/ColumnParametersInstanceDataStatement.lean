module

public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScalarsZeroPartConventionFixedPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3

section Gen

theorem majAt_eq_zero_of_self {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {x : V}
    (h : Formalism.HermitianLatticesTheory.majAt b X v x x = 0) (y : V) : Formalism.HermitianLatticesTheory.majAt b X v x y = 0 := by
  unfold Formalism.HermitianLatticesTheory.majAt at h ⊢
  have hz : ∀ i, Formalism.HermitianLatticesTheory.fcoord b X v x i = 0 := by
    have h1 : ∀ i, star (Formalism.HermitianLatticesTheory.fcoord b X v x i) * Formalism.HermitianLatticesTheory.fcoord b X v x i =
        ((Complex.normSq (Formalism.HermitianLatticesTheory.fcoord b X v x i) : ℝ) : ℂ) := fun i => by
      rw [mul_comm]; exact Complex.mul_conj _
    simp only [h1] at h
    have h2 : ∑ i, Complex.normSq (Formalism.HermitianLatticesTheory.fcoord b X v x i) = 0 := by exact_mod_cast h
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 h2 i (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  simp [hz]

theorem partPr_of_bot {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Df : DefSide Bs) (t : Bs.Tup) (p : Bs.Ix)
    (h : Df.Qp t p = ⊥) : partPr Df t p = 0 := by
  unfold partPr
  split_ifs with hc
  · have hz : ∀ z ∈ Df.Qp t p, z = 0 := fun z hz => by
      rw [h] at hz
      exact (Submodule.mem_bot K).1 hz
    ext i j
    rw [LinearMap.toMatrix'_apply, LinearMap.comp_apply, Submodule.subtype_apply, hz _ (Submodule.coe_mem _)]
    rfl
  · rfl

theorem rowXE_congr {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Df : DefSide Bs)
    (Y : Matrix (Fin (Df.dQ Bs.μ0)) (Fin (Df.dQ Bs.μ0)) ℂ) (κ : InfinitePlace K → ℝ) (lam lam' : Bs.J → Bs.Ix → InfinitePlace K → ℝ)
    (h : ∀ p, partPr Df Bs.μ0 p ≠ 0 → ∀ j v, lam j p v = lam' j p v) : rowXE Df Y κ lam = rowXE Df Y κ lam' := by
  have hw : weightMet (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0) =
      weightMet (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam' j p v) (Df.XQ Bs.μ0) := by
    funext v
    unfold weightMet
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : partPr Df Bs.μ0 p = 0
    · rw [hp]
      simp [restrMetC]
    · simp only [h p hp]
  unfold rowXE rowFrame weightFrame
  rw [hw]

end Gen

section GenCx2
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs}

theorem cx_XE_scal (Y : CxData A) (cr : Crd A fc) (lam : type_of% Y.lam) (b : Bool)
    (h : ∀ p, partPr (lv (fc Y.zs) b) Bs.μ0 p ≠ 0 → ∀ j v, lam j Bs.μ0 p v = Y.lam j Bs.μ0 p v) :
    ((reScal Y Y.κ lam).data cr b).XE = (Y.data cr b).XE :=
  rowXE_congr _ _ _ _ _ h

theorem cx_galD_scal (Y : CxData A) (cr : Crd A fc) (κ : InfinitePlace K → ℝ) (lam : type_of% Y.lam)
    (hlam : ∀ j p v, v ≠ Bs.v0 → (∃ x, Y.tC cr false j Bs.μ0 (cpt Bs.v0.embedding x) ∈ Y.Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x ≠ 0) → lam j Bs.μ0 p v = Y.lam j Bs.μ0 p v)
    (h : Y.GalD cr false) : (reScal Y κ lam).GalD cr false := by
  intro j v hv p x hx y
  change Fin ((lv (fc Y.zs) false).dZ j Bs.μ0) → K at x y
  change Y.tC cr false j Bs.μ0 (cpt Bs.v0.embedding x) ∈ Y.Wp j p at hx
  have h0 := h j v hv p x hx y
  refine h0.trans ?_
  show _ = ((lam j Bs.μ0 p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x y
  by_cases hp : ∃ x, Y.tC cr false j Bs.μ0 (cpt Bs.v0.embedding x) ∈ Y.Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x ≠ 0
  · rw [hlam j p v hv hp]
  · have hxx : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x = 0 := by
      by_contra hne
      exact hp ⟨x, hx, hne⟩
    rw [majAt_eq_zero_of_self _ _ v hxx y, mul_zero, mul_zero]

end GenCx2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) : type_of% R.lam3 :=
  fun i t p v => if (v = A3.A.v0 ∧ R.Wp3 i p = ⊥) ∨ (v ≠ A3.A.v0 ∧ ¬ R.PartAt F i p v) then Real.exp (c i) else R.lam3 i t p v

theorem zeroLam_of_ne (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (h1 : R.Wp3 i p ≠ ⊥) (h2 : v ≠ A3.A.v0 → R.PartAt F i p v) : zeroLam R F c i t p v = R.lam3 i t p v := by
  unfold zeroLam
  rw [if_neg]
  rintro (⟨_, h⟩ | ⟨hv, h⟩)
  · exact h1 h
  · exact h (h2 hv)

theorem scalarsZeroPartConvention_fixedPlace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p}
    (h1 : R.Wp3 i p ≠ ⊥) : zeroLam R F c i t p A3.A.v0 = R.lam3 i t p A3.A.v0 :=
  zeroLam_of_ne R F c h1 fun h => absurd rfl h

theorem zeroLam_off (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (hv : v ≠ A3.A.v0) (h2 : R.PartAt F i p v) : zeroLam R F c i t p v = R.lam3 i t p v := by
  unfold zeroLam
  rw [if_neg]
  rintro (⟨h, _⟩ | ⟨_, h⟩)
  · exact hv h
  · exact h h2

theorem zeroLam_of_zero (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (h : (v = A3.A.v0 ∧ R.Wp3 i p = ⊥) ∨ (v ≠ A3.A.v0 ∧ ¬ R.PartAt F i p v)) : zeroLam R F c i t p v = Real.exp (c i) := by
  unfold zeroLam
  rw [if_pos h]

theorem zeroLam_pos (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (h : ∀ i t p v, 0 < R.lam3 i t p v) (i t p v) :
    0 < zeroLam R F c i t p v := by
  unfold zeroLam
  split_ifs
  · exact Real.exp_pos _
  · exact h i t p v


set_option maxHeartbeats 4000000 in
theorem qp_bot (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) (hOk : A3.fam3.Ok3 1)
    (hsep : A3.fam3.TypesSep3) {p : A3.fam3.base3.Ix} (hp : R.EEp3 p = ⊥) (b : Bool) :
    (lv (F.fc (R.toCx3 F).zs) b).Qp A3.fam3.base3.μ0 p = ⊥ := by
  have kR := RealDat3.kFormR_of (F := F) hC.base.models
  have hst := (subspaces_stable_in_block (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP)).1
  have hH := hP.hecke.1.choose_spec
  have key : ∀ ℓ y, y ∈ (A3.fam3.RI A3.fam3.F.μ0).part3 ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) p.1 → y = 0 := by
    intro ℓ y hy
    have h1 := (part_iff_rows3 kR hst hOk hH p ℓ y).1 hy
    have h2 : (R.toCx3 F).Θ A3.fam3.F.μ0 ((R.toCx3 F).jR A3.fam3.F.μ0
        ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) y)) = 0 := by
      have h3 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).Θ A3.fam3.F.μ0 ((R.toCx3 F).jR A3.fam3.F.μ0
          ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) y))) ∈ R.EEp3 p := h1
      rw [hp] at h3
      have h5 := (Submodule.mem_bot ℂ).1 h3
      exact h5
    have h4 := CxData.theta_jR_inj (R.toCx3 F) kR _ _ (coordinates_mem_subspace ℓ _ y) h2
    exact BlockDat.toF_injective _ ℓ _ (h4.trans (map_zero _).symm)
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  cases b
  · exact key _ y hy
  · exact key _ y hy

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XEUpdSZeroLam
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 2000000 in
theorem XE_updS_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) (hOk : A3.fam3.Ok3 1) (hsep : A3.fam3.TypesSep3)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) (b : Bool) :
    (((R.updS R.kap (zeroLam R F c)).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE := by
  have h := cx_XE_scal (R.toCx3 F) F.cr (zeroLam R F c) b fun p hp j v => by
    by_cases he : R.EEp3 p = ⊥
    · exact absurd (partPr_of_bot _ _ _ (qp_bot R F hC hP hOk hsep he b)) hp
    · exact zeroLam_of_ne R F c (hZ p he j).1 fun hv => (hZ p he j).2 v hv
  exact (by with_unfolding_all exact (h :))


set_option maxHeartbeats 2000000 in
def scalReadL (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) : ReadL (R.updS R.kap lam) F X0 Y :=
  { Z with
    met := fun v hv x y => (Z.met v hv x y).trans (by rw [hX true]; rfl)
    met0 := fun v hv x y => (Z.met0 v hv x y).trans (by rw [hX false]; rfl) }


end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnParamsInstanceData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceZeroPartConventionsChosenAgain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadUpdSKeep
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem read_updS_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (err : type_of% R.err0)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ∃ (Y' : Read (A3 := A3) ((R.updS R.kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS R.kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  refine ⟨reFaceRead (R.updS R.kap lam) F Dc Sp Zsc err X0 Y,
    reFaceReadL (R.updS R.kap lam) F Dc Sp Zsc err X0 Y (scalReadL R F lam hX X0 Y Z),
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (HEq.refl Y.jA :))
  · exact (by with_unfolding_all exact (HEq.refl Y.jA0 :))
  · exact (by with_unfolding_all exact (HEq.refl Y.eMt :))
  · exact (by with_unfolding_all exact (HEq.refl Y.PY :))
  · exact (by with_unfolding_all exact (HEq.refl Y.eFT :))
  · exact (by with_unfolding_all exact (HEq.refl Y.IL :))
  · exact (by with_unfolding_all exact (HEq.refl Y.PW :))
  · exact (by with_unfolding_all exact (HEq.refl Y.eE :))
  · exact (by with_unfolding_all exact (HEq.refl Y.mj.eW :))
  · exact (by with_unfolding_all exact (HEq.refl Z.eRR :))
  · exact (by with_unfolding_all exact (HEq.refl Z.jW :))

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherRowsUpdatedScalars
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem prim_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3) (h : PrimRows3 R F)
    (h1 : ∀ i t p v, 0 < lam i t p v) (h2 : (R.updS R.kap lam).PThmB) (h3 : (R.updS R.kap lam).PThmA)
    (h4 : ((R.updS R.kap lam).toCx3 F).GalD F.cr false) : PrimRows3 (R.updS R.kap lam) F := by
  obtain ⟨⟨hE, hR⟩, ⟨hW, hL⟩⟩ := h.hecke
  exact
  { heckeR := h.heckeR
    heckeL := h.heckeL
    hecke := ⟨⟨hE, ⟨hR.intw, hR.comm, hR.parts⟩⟩, ⟨hW, ⟨hL.intw, hL.comm, hL.parts⟩⟩⟩
    gUnit := h.gUnit
    gEquiv := h.gEquiv
    block := h.block
    rowTest := h.rowTest
    liftTest := h.liftTest
    liftTestB := h.liftTestB
    liftOnto := fun hW' hh => h.liftOnto hW' ⟨hh.intw, hh.comm, hh.parts⟩
    pos := h.pos
    posScal := ⟨h.posScal.1, h1⟩
    levE := h.levE
    h2P := h.h2P
    thmB := h2
    sumE := h.sumE
    unif := h.unif
    mLat := h.mLat
    levW := h.levW
    thmA := h3
    sumW := h.sumW
    scalConj := h4
    dimParts := h.dimParts }


set_option maxHeartbeats 4000000 in
theorem pins_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (hP : Pins R F cG)
    (hs : (R.updS R.kap lam).IsScal (reFace F Dc Sp Zsc)) : Pins ((R.updS R.kap lam).withErr e) (reFace F Dc Sp Zsc) cG := by
  have h := hP.char
  have hC : (R.updS R.kap lam).WeakCharacterisation (reFace F Dc Sp Zsc) :=
    ⟨h.base, ⟨h.inert.tie, h.inert.onto, h.inert.hR, h.inert.hL, h.inert.SF⟩, h.fullY, h.fullX, h.fullP, hs,
      ⟨h.tup.mu_off, h.tup.mu_used, h.tup.mu_ne, h.tup.mu_conj, h.tup.mu_on⟩, h.phase, h.allPl⟩
  exact ⟨RealDat3.weak_characterisation_with_error hC e, reFace_keep (R.updS R.kap lam) F cG Dc Sp Zsc e hP.keep, hP.phs, hP.trSem⟩


set_option maxHeartbeats 4000000 in
theorem furtherRows_updatedScalars (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3) (h : UnusedChoiceStatements R F) :
    UnusedChoiceStatements (R.updS R.kap lam) F := ⟨h.ex, h.conj, h.levelW, h.integral⟩

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartAtUpdSReFace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lamN_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (kap : ℝ)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) {p} (hp : R.EEp3 p ≠ ⊥) (t j) :
    (R.updS kap (zeroLam R F c)).lamN t j p = R.lamN t j p := by
  unfold RealDat3.lamN
  split_ifs with h
  · exact scalarsZeroPartConvention_fixedPlace R F c ((hZ p hp _).1)
  · rfl

theorem isKap_congr {N Tup Sig : Type} [AddCommGroup N] [Module ℂ N] {m : ℕ} {dnup : Tup → N →ₗ[ℂ] N} {partE : Sig → Submodule ℂ N}
    {lam lam' : Tup → ℕ → Sig → ℝ} {κ : ℝ} (h : Lift.IsKap m dnup partE lam κ)
    (hl : ∀ μ j σ, partE σ ≠ ⊥ → lam' μ j σ = lam μ j σ) : Lift.IsKap m dnup partE lam' κ := by
  intro μ σ x hx
  by_cases hσ : partE σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp
  · rw [Finset.prod_congr rfl fun j _ => hl μ j σ hσ]
    exact h μ σ x hx

theorem isLamP_congr {A Amb Sig : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb] {thW : A →ₗ[ℂ] Amb}
    {adj : Amb →ₗ[ℂ] A} {part : Sig → Submodule ℂ Amb} {lam lam' : Sig → ℝ} (h : Lift.IsLamP thW adj part lam)
    (hl : ∀ σ, part σ ≠ ⊥ → lam' σ = lam σ) : Lift.IsLamP thW adj part lam' := by
  intro σ x hx
  by_cases hσ : part σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp
  · rw [hl σ hσ]
    exact h σ x hx


set_option maxHeartbeats 1000000 in
theorem thmB_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hB : R.PThmB) : (R.updS R.kap (zeroLam R F c)).PThmB := by
  have h := isKap_congr (lam' := (R.updS R.kap (zeroLam R F c)).lamN) hB
    fun μ j σ hσ => lamN_zeroLam R F c R.kap hZ hσ μ j
  exact (by with_unfolding_all exact (h :))


set_option maxHeartbeats 1000000 in
theorem thmA_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hA : R.PThmA) : (R.updS R.kap (zeroLam R F c)).PThmA := by
  have h := fun i t => isLamP_congr (lam' := fun p => zeroLam R F c i t p A3.A.v0) (hA i t)
    fun σ hσ => scalarsZeroPartConvention_fixedPlace R F c hσ
  exact (by with_unfolding_all exact (h :))


set_option maxHeartbeats 1000000 in
theorem galD_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hG : (R.toCx3 F).GalD F.cr false) : ((R.updS R.kap (zeroLam R F c)).toCx3 F).GalD F.cr false := by
  have h := cx_galD_scal (R.toCx3 F) F.cr (fun _ => R.kap) (zeroLam R F c) (fun j p v hv hp => zeroLam_off R F c hv hp) hG
  exact (by with_unfolding_all exact (h :))

theorem partAt_updS_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (i p v) :
    (R.updS kap lam).PartAt (reFace F Dc Sp Zsc) i p v ↔ R.PartAt F i p v :=
  (RealDat3.partAt_updS kap lam i p v).trans Iff.rfl


set_option maxHeartbeats 4000000 in
theorem scal_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hs : R.IsScal F) :
    (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)).IsScal (reFace F Dc Sp Zsc) := by
  refine ⟨fun i t p l hp hl => ?_, fun κ hk hne => ?_, fun i p v l hv hp he => ?_, fun i t p hp => ?_,
    fun i p v hv hp => ?_, fun i t p v hv => ?_⟩
  · exact (scalarsZeroPartConvention_fixedPlace R F _ hp).trans (hs.lam0 i t p l hp hl)
  · refine hs.kap κ (fun μ σ x hx => ?_) ?_
    · by_cases hσ : R.EEp3 σ = ⊥
      · rw [hσ, Submodule.mem_bot] at hx
        subst hx
        simp
      · have e := hk μ σ x hx
        rw [Finset.prod_congr rfl fun j _ => lamN_zeroLam R F _ R.kap hZ hσ μ j] at e
        exact e
    · obtain ⟨t, p, hp, hne⟩ := hne
      exact ⟨t, p, hp, by rwa [Finset.prod_congr rfl fun j _ => lamN_zeroLam R F _ R.kap hZ hp t j] at hne⟩
  · have hp' : R.PartAt F i p v := (partAt_updS_reFace R F _ _ Dc Sp Zsc i p v).1 hp
    exact (zeroLam_off R F _ hv hp').trans (hs.off i p v l hv hp' he)
  · exact zeroLam_of_zero R F _ (Or.inl ⟨rfl, hp⟩)
  · exact zeroLam_of_zero R F _ (Or.inr ⟨hv, fun h => hp ((partAt_updS_reFace R F _ _ Dc Sp Zsc i p v).2 h)⟩)
  · show zeroLam R F _ i t p v = zeroLam R F _ i A3.A.μ0 p v
    unfold zeroLam
    split_ifs with h
    · rfl
    · exact hs.tup i t p v hv

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceZeroPartConventionsChosenAgain
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3


set_option maxHeartbeats 1000000 in
theorem reFace_zero_parts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), Pins R F cG → Holds R F → (∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.EEp3 p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Dc Sp Zsc hP hH hZ
  have h1 := pins_updS R F cG (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) hP (scal_zeroLam R F Dc Sp Zsc hZ hP.char.scal)
  have h2 := prim_updS R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) hH.prim (zeroLam_pos R F (Zsc (R.toCx3 F).zs).l6m hH.prim.posScal.2)
    (thmB_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hZ hH.prim.thmB) (thmA_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hH.prim.thmA) (galD_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hH.prim.scalConj)
  have h3 := Holds.mk (reFace_prim (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) h2)
    (further_face_statements_independent_of_error (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) (furtherRows_updatedScalars R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) hH.aux)) hH.ok hH.sep
  have h4 := reFace_errEq (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc
  have h5 : ∀ i t p v, R.EEp3 p ≠ ⊥ → zeroLam R F (Zsc (R.toCx3 F).zs).l6m i t p v = R.lam3 i t p v :=
    fun i t p v hp => zeroLam_of_ne R F _ (hZ p hp i).1 fun hv => (hZ p hp i).2 v hv
  have h6 := read_updS_keep R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc)
    (XE_updS_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hP.char hH.prim hH.ok hH.sep hZ) X0 Y Z
  refine ⟨R.kap, (zeroLam R F (Zsc (R.toCx3 F).zs).l6m), (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc), ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h3 :))
  · exact (by with_unfolding_all exact (h4 :))
  · exact (by with_unfolding_all exact (h5 :))
  · exact (by with_unfolding_all exact (h6 :))

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceZeroPartConventionsChosenAgainStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reFace_zero_part_conventions_chosen_again : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), Pins R F cG → Holds R F → (∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.EEp3 p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  first | exact @GlobalTheory.Mem.R3.reFace_zero_parts | exact GlobalTheory.Mem.R3.reFace_zero_parts | (intros; apply GlobalTheory.Mem.R3.reFace_zero_parts <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.TwistedScalarIndependence

theorem dep_imp {α : Sort _} {β : α → Sort _} (P : ∀ a, β a → Prop) {a a' : α} {b : β a} {b' : β a'} (h : a' = a) (hb : HEq b' b)
    (H : P a b) : P a' b' := by
  subst h
  cases hb
  exact H

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}

section Field

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
  (lam : type_of% R.lam3) (err : type_of% R.err0)

abbrev newR : RealDat3 D A3 Ks := (R.updS R.kap lam).withErr err

variable {R F} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp₀ Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc₀ Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {Y' : Read (A3 := A3) (newR R lam err).toRealDat (reFace F Dc Sp Zsc).lv2 X0}


set_option maxHeartbeats 4000000 in
def newC (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) X0 Y) (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA) :
    ReadC (newR R lam err) (reFace F Dc Sp Zsc) X0 Y' where
  wU := (by with_unfolding_all exact (C₀.wU :))
  bij := (by with_unfolding_all exact (C₀.bij :))
  eNu := (by with_unfolding_all exact (C₀.eNu :))
  NuC := (by with_unfolding_all exact (C₀.NuC :))
  nu := (by with_unfolding_all exact (C₀.nu :))
  pt := by
    have h := dep_imp (β := fun tup : T → D.what₂.Tup =>
        ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tup t))
      (fun tup jA => ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc (zsOf R F)).a (C₀.wU u)) → D.what₂.LL)
        (f : Fin ((A3.side3 F.P1 F.ψ1 (zsOf R F)).nV t) → D.what₂.LL),
        D.what₂.embLL ((Dc (zsOf R F)).Pt (C₀.wU u) t x f) =
          D.what₂.perCol u (tup t) (D.jN u (C₀.eNu u x)) (jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)))
      (b := Y.jA) (b' := (by with_unfolding_all exact (Y'.jA :))) ht ((by with_unfolding_all exact (hj :))) ((by with_unfolding_all exact (C₀.pt :)))
    with_unfolding_all exact (h :)


set_option maxHeartbeats 4000000 in
theorem rationalFormsComparison_baseLevel_indep_scalars {a0 : AmbForm D X0.s} (h : ∃ J, AmbTie D A3.A X0.s a0 F.P0 F.ψ0 Y.tup Y.jA0 J) (ht : Y'.tup = Y.tup)
    (hj : HEq Y'.jA0 Y.jA0) :
    ∃ J, AmbTie D A3.A X0.s a0 (reFace F Dc Sp Zsc).P0 (reFace F Dc Sp Zsc).ψ0 Y'.tup Y'.jA0 J := by
  have h' := dep_imp (β := fun tup : T → D.what₂.Tup =>
      ∀ t, (Fin (rDim D A3.A F.P0 F.ψ0 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X0.s.Amb (tup t))
    (fun tup jA => ∃ J, AmbTie D A3.A X0.s a0 F.P0 F.ψ0 tup jA J) (b := Y.jA0) (b' := (by with_unfolding_all exact (Y'.jA0 :))) ht ((by with_unfolding_all exact (hj :))) h
  exact (by with_unfolding_all exact (h' :))


set_option maxHeartbeats 4000000 in
theorem mj_new {Z : ReadL R F X0 Y} {Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) X0 Y'} {Xd : DivX D} (h : MjAre Z Xd)
    (hj : HEq Z'.jW Z.jW) : MjAre Z' Xd := by
  obtain ⟨J, hJ⟩ := h
  have e : Z'.jW = (by with_unfolding_all exact (Z.jW :)) := eq_of_heq ((by with_unfolding_all exact (hj :)))
  refine ⟨⟨(by with_unfolding_all exact (J.eW :))⟩, ?_, (by with_unfolding_all exact (hJ.hlat :))⟩
  rewrite [e]
  exact (by with_unfolding_all exact (hJ.j_eq :))

end Field


set_option maxHeartbeats 4000000 in
def newGeo {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} (lam : type_of% R.lam3)
    (err : type_of% R.err0) (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) :
    GlobalTheory.RealGeo.GeoHalf C (GlobalTheory.RealGeo.Upd.upE C R.toRealDat R.kap R.lam err) fun _ => 1 :=
  ⟨g.κ, g.v₀, GlobalTheory.RealGeo.Upd.updFWT C R.toRealDat R.kap R.lam err g.fw, g.bar,
    fun i => GlobalTheory.RealGeo.Upd.updO C R.toRealDat R.kap R.lam err (g.O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE R.kap R.lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩


set_option maxHeartbeats 4000000 in
theorem inGeo_new {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} (lam : type_of% R.lam3)
    (err : type_of% R.err0) {g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} (h : GlobalTheory.RealGeo.InGeo g) :
    GlobalTheory.RealGeo.InGeo (newGeo lam err g) :=
  ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩

section Tw

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL]
  {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (lam : type_of% R.lam3) (err : type_of% R.err0)
  {Y : Read (A3 := A3) R.toRealDat F.lv2 ex.p0} {Z : ReadL R F ex.p0 Y}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp₀ Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc₀ Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {Y' : Read (A3 := A3) (newR R lam err).toRealDat (reFace F Dc Sp Zsc).lv2 ex.p0}


set_option maxHeartbeats 4000000 in
def newTw (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) ex.p0 Y')
    (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) ex.p0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (Sp (zsOf R F)).HH)
    (hP : Pins (newR R lam err) (reFace F Dc Sp Zsc) cG) (hH : Holds (newR R lam err) (reFace F Dc Sp Zsc))
    (hE : ErrEq (newR R lam err) (reFace F Dc Sp Zsc))
    (hG : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG))
    (hA : ∃ J, AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 J) (hM : MjAre Z Yd)
    (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA) (hj0 : HEq Y'.jA0 Y.jA0) (hW : HEq Z'.jW Z.jW) : TwIn ex where
  G := G
  Pl0 := Pl0
  I0 := I0
  T := T
  A3 := A3
  core := C
  R := newR R lam err
  F := reFace F Dc Sp Zsc
  cG := cG
  geo := (by with_unfolding_all exact ((newGeo lam err g) :))
  pins := hP
  err := hE
  Y := Y'
  Z := Z'
  C := newC lam err C₀ ht hj
  sEE := (by with_unfolding_all exact (sEE :))
  div := (GlobalTheory.T.divisionCompatible_at_readIdentifications hC D G Pl0 I0 T A3 C.Q.c.F (newR R lam err) (reFace F Dc Sp Zsc) cG ex.p0 Y' Z' (newC lam err C₀ ht hj)
    (by with_unfolding_all exact (sEE :)) Yd (mj_new lam err hM hW).choose hP hH (fun _ _ => (by with_unfolding_all exact (hG :)))).1
  JA := (rationalFormsComparison_baseLevel_indep_scalars lam err hA ht hj0).choose
  amb0 := (rationalFormsComparison_baseLevel_indep_scalars lam err hA ht hj0).choose_spec
  JM := (mj_new lam err hM hW).choose
  mjH := (mj_new lam err hM hW).choose_spec

-- Check the dependent column projections before specializing the ambient data to a row.
set_option maxHeartbeats 4000000 in
private theorem newTw_preserves_columns
    (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧
      GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧
      GlobalTheory.Published.CuspRapidDecay)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1)
    (Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) ex.p0 Y')
    (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) ex.p0 Y)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (Sp (zsOf R F)).HH)
    (hP : Pins (newR R lam err) (reFace F Dc Sp Zsc) cG)
    (hH : Holds (newR R lam err) (reFace F Dc Sp Zsc))
    (hE : ErrEq (newR R lam err) (reFace F Dc Sp Zsc))
    (hG : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG))
    (hA : ∃ J, AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 J)
    (hM : MjAre Z Yd) (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA)
    (hj0 : HEq Y'.jA0 Y.jA0) (hW : HEq Z'.jW Z.jW) (hg : GlobalTheory.RealGeo.InGeo g) :
    let x := newTw (R := R) (F := F) (cG := cG) (Y := Y) (Z := Z) (Dc := Dc)
      (Sp₀ := Sp₀) (Sp := Sp) (Zsc₀ := Zsc₀) (Zsc := Zsc) (Y' := Y')
      lam err hC g Z' C₀ sEE hP hH hE hG hA hM ht hj hj0 hW
    HEq x.sEE sEE ∧ HEq x.C.wU C₀.wU ∧ HEq x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo x.geo := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · with_unfolding_all exact (HEq.refl sEE :)
  · with_unfolding_all exact (HEq.refl C₀.wU :)
  · with_unfolding_all exact (HEq.refl C₀.eNu :)
  · with_unfolding_all exact (inGeo_new lam err hg :)

end Tw

end GlobalTheory.Mem.R3.TwistedScalarIndependence

namespace GlobalTheory.Mem.R3

open TwistedScalarIndependence


set_option maxHeartbeats 8000000 in
theorem twArgs_exists : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0), AmbAre t.r.Z ex.amb ex.amb0 → MjAre t.r.Z Yd → GrpTie (w.st Z).toD7 (famT t).A t.r.z.F.P0 t.r.z.F.ψ0 t.r.z.F.P1 t.r.z.F.ψ1 (t.r.z.R.eG.trans t.r.z.cG) → (∀ p, t.r.z.R.EEp3 p ≠ ⊥ → ∀ i, t.r.z.R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ (famT t).A.v0 → t.r.z.R.PartAt t.r.z.F i p v) → ∀ Dc Sp₀ Zsc₀ (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((t.r.Y))) (Sp : ∀ Zs, SPer (Dc Zs)) Zsc (sEE : (t.r.z.R.toCx3 t.r.z.F).EE →ₗ⋆[ℂ] (Sp (zsOf t.r.z.R t.r.z.F)).HH), ∃ a : TwArgs ex t, a.Dc = Dc ∧ HEq a.Sp Sp ∧ a.Zsc = Zsc ∧ HEq a.x.sEE sEE ∧ HEq a.x.C.wU C₀.wU ∧ HEq a.x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo a.x.geo := by
  intro hC K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t hA hM hG hp Dc Sp₀ Zsc₀ C₀ Sp Zsc sEE
  obtain ⟨kap, lam, err, hP, hH, hE, rfl, hl, Y', Z', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    GlobalTheory.T.reFace_zero_part_conventions_chosen_again (w.st Z).toD7 _ _ _ _ (famT t) _ t.r.z.R t.r.z.F t.r.z.cG ex.p0 t.r.Y t.r.Z Dc Sp Zsc t.r.z.pins t.r.intersectionNumber_baseChange hp
  let x : TwIn ex := newTw (R := t.r.z.R) (F := t.r.z.F) (cG := t.r.z.cG) (Y := t.r.Y) (Z := t.r.Z) (Dc := Dc) (Sp₀ := Sp₀) (Sp := Sp)
    (Zsc₀ := Zsc₀) (Zsc := Zsc) (Y' := Y') lam err hC t.r.z.geo Z' C₀ sEE hP hH hE hG hA.2 hM h1 h3 h4 h13
  let a : TwArgs ex t :=
    { Dc := Dc, Sp := Sp, Zsc := Zsc, lam := lam, err := err, lam_eq := hl, x := x
      pack := rfl
      intersectionNumber_baseChange := (by with_unfolding_all exact (hH :))
      κ := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.κ) :))
      v₀ := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.v₀) :))
      fw := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.fw.e) :))
      tup := (by with_unfolding_all exact ((heq_of_eq h1) :))
      tupT := (by with_unfolding_all exact ((heq_of_eq h2) :))
      jA := (by with_unfolding_all exact (h3 :))
      jA0 := (by with_unfolding_all exact (h4 :))
      eMt := (by with_unfolding_all exact (h5 :))
      PY := (by with_unfolding_all exact (h6 :))
      PW := (by with_unfolding_all exact (h9 :))
      eFT := (by with_unfolding_all exact (h7 :))
      IL := (by with_unfolding_all exact (h8 :))
      eE := (by with_unfolding_all exact (h10 :))
      eW := (by with_unfolding_all exact (h11 :))
      jW := (by with_unfolding_all exact (h13 :))
      eRR := (by with_unfolding_all exact (h12 :)) }
  have hCols := newTw_preserves_columns (R := t.r.z.R) (F := t.r.z.F) (cG := t.r.z.cG)
    (Y := t.r.Y) (Z := t.r.Z) (Dc := Dc) (Sp₀ := Sp₀) (Sp := Sp) (Zsc₀ := Zsc₀)
    (Zsc := Zsc) (Y' := Y') lam err hC t.r.z.geo Z' C₀ sEE hP hH hE hG hA.2 hM h1 h3 h4 h13 t.inGeo
  refine ⟨a, rfl, HEq.rfl, rfl, ?_⟩
  change HEq x.sEE sEE ∧ HEq x.C.wU C₀.wU ∧ HEq x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo x.geo
  exact hCols

end GlobalTheory.Mem.R3

end
end

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.column_params_instance_data : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0), AmbAre t.r.Z ex.amb ex.amb0 → MjAre t.r.Z Yd → GrpTie (w.st Z).toD7 (famT t).A t.r.z.F.P0 t.r.z.F.ψ0 t.r.z.F.P1 t.r.z.F.ψ1 (t.r.z.R.eG.trans t.r.z.cG) → (∀ p, t.r.z.R.EEp3 p ≠ ⊥ → ∀ i, t.r.z.R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ (famT t).A.v0 → t.r.z.R.PartAt t.r.z.F i p v) → ∀ Dc Sp₀ Zsc₀ (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((t.r.Y))) (Sp : ∀ Zs, SPer (Dc Zs)) Zsc (sEE : (t.r.z.R.toCx3 t.r.z.F).EE →ₗ⋆[ℂ] (Sp (zsOf t.r.z.R t.r.z.F)).HH), ∃ a : TwArgs ex t, a.Dc = Dc ∧ HEq a.Sp Sp ∧ a.Zsc = Zsc ∧ HEq a.x.sEE sEE ∧ HEq a.x.C.wU C₀.wU ∧ HEq a.x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo a.x.geo := by
  first | exact @GlobalTheory.Mem.R3.twArgs_exists | exact GlobalTheory.Mem.R3.twArgs_exists | (intros; apply GlobalTheory.Mem.R3.twArgs_exists <;> assumption)
