module

public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import ReciprocityTheory.AnalyticForms.LeviForms.Energy
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtPlacesFromComparison
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiLinear
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstDeform

theorem act_const : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), ∀ a, (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF a
  haveI := Xo.univ.t.act.hom a
  have wβ : (π ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A.hom ≫ y.x := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ.1.w]
  let β : A ⟶ A := Over.homMk (hπ.1.lift _ A.hom wβ) (hπ.1.lift_snd _ _ _)
  have hβ : β.left ≫ π = π ≫ (Xo.univ.t.act.act a).left := hπ.1.lift_fst _ _ _
  haveI : IsMonHom β := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ hπ (Xo.univ.t.act.act a) β hβ
  have wα : (π' ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A'.hom ≫ x' := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ'.1.w]
  let α : A' ⟶ A' := Over.homMk (hπ'.1.lift _ A'.hom wα) (hπ'.1.lift_snd _ _ _)
  have hα : α.left ≫ π' = π' ≫ (Xo.univ.t.act.act a).left := hπ'.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ' hπ' (Xo.univ.t.act.act a) α hα
  have wδ : (q ≫ β.left) ≫ A.hom = A'.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w β, hq.1.w]
  let δ : A' ⟶ A' := Over.homMk (hq.1.lift _ A'.hom wδ) (hq.1.lift_snd _ _ _)
  have hδ : δ.left ≫ q = q ≫ β.left := hq.1.lift_fst _ _ _
  haveI : IsMonHom δ := GlobalTheory.UU.isMonHom_of_over_isMonHom hq hq β δ hδ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have LH := (hGD.at_dualNumber K).2.2
  have e1 : i ≫ α.left = β.left ≫ i := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, reassoc_of% hiπ, hiπ, hβ]
    · simp only [Category.assoc]
      rw [Over.w α, hi.1.w, reassoc_of% (Over.w β)]
  have e2 : i ≫ δ.left = β.left ≫ i := by
    apply hq.1.hom_ext
    · simp only [Category.assoc]
      rw [hδ, reassoc_of% hiq, hiq, Category.comp_id]
    · simp only [Category.assoc]
      rw [Over.w δ, hi.1.w, reassoc_of% (Over.w β)]
  have hαδ : α = δ := GlobalTheory.Published.GrothendieckMessing.LiftHom.unique LH hi hA' gA' hi hA' gA' β e1 e2
  have hga : (o.t.act.act a).left ≫ g = g ≫ α.left := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, hg, reassoc_of% hg]
      exact m.act a
    · simp only [Category.assoc]
      rw [hgw, Over.w α, hgw, Over.w (o.t.act.act a)]
  calc (o.t.act.act a).left ≫ (g ≫ q ≫ π) = g ≫ α.left ≫ q ≫ π := by rw [reassoc_of% hga]
    _ = g ≫ q ≫ π ≫ (Xo.univ.t.act.act a).left := by rw [hαδ, reassoc_of% hδ, hβ]
    _ = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by simp only [Category.assoc]

end GlobalTheory.ConstDeform
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiLinearStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_lift_tangent_Phi_linear : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), ∀ a, (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  first | exact @GlobalTheory.ConstDeform.act_const | exact GlobalTheory.ConstDeform.act_const | (intros; apply GlobalTheory.ConstDeform.act_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfWeightLocPot
noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ArInt GlobalTheory.Mean4O GlobalTheory.CxPts

namespace GlobalTheory.Mean4O.ReadsProj

section Local

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} (σ : k →+* ℂ)

def HalfWeight (L : HermLB p) (g : CxPts p σ → CxPts p σ → ℝ) : Prop :=
  ∀ x, ∃ i, x ∈ ptsIn p σ (L.B.U i) ∧ ∀ z, (L.φ σ).φ i z / 2 = g x z

variable {σ} {L L' : HermLB p} {g g' : CxPts p σ → CxPts p σ → ℝ}

theorem HalfWeight.congr (h : HalfWeight σ L g) (e : ∀ x z, g x z = g' x z) : HalfWeight σ L g' := by
  rwa [← show g = g' from funext₂ e]

theorem halfWeight_locPot (L : HermLB p) : HalfWeight σ L (L.φ σ).locPot.φ :=
  fun x => ⟨_, (L.φ σ).locPot.mem_U x, fun _ => rfl⟩

theorem halfWeight_triv : HalfWeight σ (HermLB.triv p) fun _ _ => 0 :=
  fun _ => ⟨PUnit.unit, mem_ptsIn_top, fun _ => zero_div _⟩

theorem HalfWeight.tens (h : HalfWeight σ L g) (h' : HalfWeight σ L' g') :
    HalfWeight σ (L.tens L') fun x z => g x z + g' x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  obtain ⟨j, hj, e'⟩ := h' x
  exact ⟨(i, j), mem_ptsIn_inf.2 ⟨hi, hj⟩, fun z => (add_div _ _ _).trans (congrArg₂ (· + ·) (e z) (e' z))⟩

theorem HalfWeight.dual (h : HalfWeight σ L g) : HalfWeight σ L.dual fun x z => -g x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  exact ⟨i, hi, fun z => (neg_div _ _).trans (congrArg (-·) (e z))⟩

theorem HalfWeight.pow (h : HalfWeight σ L g) (m : ℕ) : HalfWeight σ (L.pow m) fun x z => m * g x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  refine ⟨fun _ => i, CxPts.mem_pow_iff.2 hi, fun z => ?_⟩
  refine (congrArg (· / 2) ((L.φ σ).zpow_φ m _ z)).trans ?_
  simp only [← e z, mul_div_assoc, Int.cast_natCast]

theorem HalfWeight.zp (h : HalfWeight σ L g) (n : ℤ) : HalfWeight σ (zp L n) fun x z => n * g x z :=
  ((h.pow n.toNat).tens (h.pow (-n).toNat).dual).congr fun x z => by
    have e : ((n.toNat : ℤ) : ℝ) - ((-n).toNat : ℤ) = n := by exact_mod_cast Int.toNat_sub_toNat_neg n
    rw [← e]
    simp only [Int.cast_natCast]
    ring

theorem halfWeight_comb {ι : Type} [Fintype ι] {L : ι → HermLB p} {g : ι → CxPts p σ → CxPts p σ → ℝ}
    (h : ∀ i, HalfWeight σ (L i) (g i)) (n : ι → ℤ) :
    HalfWeight σ (ArInt.comb L n) fun x z => ∑ i, n i * g i x z := by
  have key (l : List ι) : HalfWeight σ (l.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p))
      fun x z => (l.map fun i => n i * g i x z).sum := by
    induction l with
    | nil => exact halfWeight_triv
    | cons i l ih => exact ((h i).zp (n i)).tens ih
  exact (key _).congr fun x z => Finset.sum_map_toList _ _

end Local

open ProjSpace

variable (N : ℕ)

end GlobalTheory.Mean4O.ReadsProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullTopInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullBig

open GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 Filter

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (σ : X ⟶ Y)
    (hσ : DenseRange σ) : σ (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image σ.continuous
  rw [Set.image_univ, hσ.closure_range] at h
  exact h.eq (genericPoint_spec Y)

theorem pull_top_injective {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : Y ⟶ Sp k} (σ : X ⟶ Y) (hσ : DenseRange σ) (B : LB Y) :
    Function.Injective (H0.pull (p := p) (B := B) (O := ⊤) σ (W := ⊤) le_top) := by
  have hη := map_genericPoint σ hσ
  have hF : IsField (Y.presheaf.stalk (σ (genericPoint X))) := by
    rw [hη]; exact Field.toIsField Y.functionField
  refine (injective_iff_map_eq_zero _).2 fun f hf => LB.sec_ext fun i => fun_ext_ger fun y hy => ?_
  have hηi : genericPoint Y ∈ B.U i :=
    ((genericPoint_spec Y).mem_open_set_iff (B.U i).isOpen).2 ⟨y, Set.mem_univ _, hy.2⟩
  have hxi : σ (genericPoint X) ∈ B.U i := hη ▸ hηi
  have h0 : germ (p := p) (O := ⊤) i (σ (genericPoint X)) trivial hxi f = 0 := by
    have e := congrArg (germ (p := σ ≫ p) (B := B.pull σ) (O := ⊤) (fun _ => i) (genericPoint X) trivial (mem_pull.2 hxi)) hf
    have e' := (germ_pull (p := p) (B := B) (O := ⊤) σ (W := ⊤) le_top (fun _ => i) (genericPoint X) trivial
      (mem_pull.2 hxi) f).symm.trans (e.trans (map_zero _))
    by_contra hne
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
    have := congrArg (σ.stalkMap (genericPoint X)).hom hb
    rw [map_mul, e', zero_mul, map_one] at this
    exact zero_ne_one this
  have hloc : f.loc i = 0 :=
    germ_injective_of_isIntegral Y (U := ⊤ ⊓ B.U i) (σ (genericPoint X)) ⟨trivial, hxi⟩
      (h0.trans (map_zero _).symm)
  exact congrArg _ hloc

theorem isBig_pull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y), IsProjOver p → IsProjOver (σ ≫ p) →
    topologicalKrullDim X = topologicalKrullDim Y → DenseRange σ → ∀ L : LB Y,
    (letI := algebraΓOfHom p; IsBig k L) → (letI := algebraΓOfHom (σ ≫ p); IsBig k (L.pull σ)) := by
  intro k _ X Y _ _ p σ hp hq hdim hσ L hL
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (σ ≫ p)
  obtain ⟨D, hD, c, hc, hm⟩ := hL.growth
  have hL' := LB.isLB_pull hL.isLB σ
  have key (m : ℕ) : lbH0 k (lbPow L m) ≤ lbH0 k (lbPow (L.pull σ) m) := by
    have hLm := isLB_lbPow hL.isLB m
    have hP := LB.isLB_pull hLm σ
    haveI := finite_top hq hP
    calc lbH0 k (lbPow L m) = Module.finrank k (H0 p (lbPow L m) ⊤) := (H0.finrank_top p _).symm
      _ ≤ Module.finrank k (H0 (σ ≫ p) ((lbPow L m).pull σ) ⊤) :=
        LinearMap.finrank_le_finrank_of_injective (pull_top_injective σ hσ _)
      _ = lbH0 k ((lbPow L m).pull σ) := H0.finrank_top _ _
      _ = lbH0 k (lbPow (L.pull σ) m) := lineBundleGlobalSectionsDim_congr_picardClass hP (isLB_lbPow hL' m) (by
        rw [cls_pull hLm, cls_lbPow hL.isLB, cls_lbPow hL', cls_pull hL.isLB, map_nsmul])
  refine (isBig_iff (fun _ => rfl) hq (hdim.trans hD)).2 ⟨hL', c, hc, hm.mono fun m hm' => ?_⟩
  exact hm'.trans (by exact_mod_cast key m)

end GlobalTheory.PullBig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientLatticeSpan
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.Exp


open GlobalTheory.TraceIncl in
theorem clSum_equiv_of_lift {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : (∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')) (g : G) (f : (A.MtCSD i t).Forms) :
    clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g f) = actS R i g (clSum (presV R i t) (kern R i t) f) := by
  refine clSum_act (presV R i t) (kernelLaws hS.models hS.thP hS.typ) (R.B.L i t).act_tie (envV R i t).J_le (actS R i)
    (fun q y w => funext fun v => ?_) g f
  exact (GlobalTheory.T.thetaKernelFiniteAdelic_laws R i t hS.models.inf hS.models.cV hS.thP.ωP hS.thP.pt_theta hS.thP.ioP hS.typ).2.2.2 _ q (hS.red i t q)
    (hl _) y w v


open GlobalTheory.TraceIncl in
theorem clSum_trU_of_lift {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : (∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (f : (A.MtCSD i t).Forms)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    clSum (presV R i t) (kern R i t) (trU (A.leftGroupActionLift i t) U ψ f) v =
      levelTrace R i U ψ (clSum (presV R i t) (kern R i t) f v) := by
  unfold levelTrace gaL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [trU_apply, map_sum, Finset.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smulₛₗ, clSum_equiv_of_lift hS hl, LinearMap.smul_apply, invChar, apply_dite D.what₂.embLL, map_zero]
  rfl


open GlobalTheory.TraceIncl in
set_option maxHeartbeats 4000000 in
theorem exists_adForm_levelTrace {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : ∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (hχ : ∀ k, ∃ a : D.what₂.LL, D.what₂.embLL a = (((envV R i t).χ k : ℂˣ) : ℂ))
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {θ : (Fin (srcDim A i t U ψ) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : IsClassSum R i t U ψ 1 θ) {h : GA D (Vc D i)} (hh : h ∈ GfC (Vc D i)) {w : (R.cV i).W} (hw : InCoefLat R i h w) :
    ∃ y ∈ LinearMap.range θ, ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
      adForm R i y (fun ρ => v ρ) = levelTrace R i U ψ (singleSeries R i (R.ωP i t) (R.vP i t) h w v) := by
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  obtain ⟨e, r, h1, hL⟩ := exists_latSys (i := i) (t := t) hS.lev hT
  obtain ⟨f, hf, j, hj⟩ := hL.exists_trace (GlobalTheory.LevelCharOrder.levEnv_chi_isOfFinOrder _ _ _)
    (kernelLaws hS.models hS.thP hS.typ) (h := fin _ h) (x := e.symm P)
    (Submodule.mem_comap.2 ((e.apply_symm_apply P).symm ▸ hP : e (e.symm P) ∈ nabAtr (labLL D) (lamV D i) _))
  obtain ⟨y, -, ey⟩ := exists_src_trU i t U ψ hS.act hf
  have hcw : (presV R i t).coef (e.symm P) = c0L i P := (h1 _).trans (congrArg (c0L i) (e.apply_symm_apply P))
  obtain ⟨a, ha⟩ := hχ j
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  refine ⟨θ (a⁻¹ • y), LinearMap.mem_range_self _ _, fun v => ?_⟩
  have e1 : singleSeries R i (R.ωP i t) (R.vP i t) h (c0L i P) v =
      ((((envV R i t).χ j)⁻¹ : ℂˣ) : ℂ) • clSum (presV R i t) (kern R i t) f v :=
    (hS.kern_fin hh _ v).symm.trans ((congrArg (fun w' => kern R i t (fin _ h) w' v) hcw.symm).trans (congrFun hj v))
  have e2 : adForm R i (θ y) (fun ρ => v ρ) = (1 : ℂ) • levelTrace R i U ψ (clSum (presV R i t) (kern R i t) f v) := by
    rw [hS.adForm_theta hθ y v, ey, clSum_trU_of_lift hS hl]
  have e3 : adForm R i (θ (a⁻¹ • y)) (fun ρ => v ρ) = D.what₂.embLL a⁻¹ • adForm R i (θ y) (fun ρ => v ρ) := by
    rw [map_smul, adForm_smul]
    rfl
  rw [e3, e2, one_smul, e1, (levelTrace R i U ψ).map_smul, map_inv₀, ha, Units.val_inv_eq_inv_val]

end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSet
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompConstMulMemHolSub
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRat

theorem const_of_idem_on {Y : Type} [TopologicalSpace Y] {s : Set Y} (hs : IsPreconnected s) {g : Y → ℂ}
    (hg : ContinuousOn g s) (hi : ∀ x ∈ s, g x * g x = g x) : ∃ w : ℂ, ∀ x ∈ s, g x = w := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · exact ⟨0, fun _ h => h.elim⟩
  refine ⟨g x0, fun x hx => ?_⟩
  have hfin : (g '' s).Finite := by
    refine (Set.toFinite ({0, 1} : Set ℂ)).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    have h := hi y hy
    have : g y * (g y - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  exact hs.constant_of_mapsTo hfin.isDiscrete hg (Set.mapsTo_image g s) hx hx0

theorem rdU_mul_apply' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f f' : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU U (f * f') k x = rdU U f k x * rdU U f' k x := by
  by_cases h : x ∈ (U.X k).dom
  · have e1 : ∀ g : Rul Xo c, rdU U g k x = toC (evR Xo c g (U.un k ⟨x, h⟩)) := fun g => dif_pos h
    rw [e1, e1, e1]
    exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f f' (U.un k ⟨x, h⟩)
  · rw [rdU_mem_offZero U _ k x h, rdU_mem_offZero U f k x h, zero_mul]

end GlobalTheory.CompRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSet
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.FramesUnion

theorem framesOn_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ), IsUnf (U σ) → ∀ (Z : Comp Xo c) (k : (U σ).Comp) (y y' : Frame ((U σ).X k).Ψ r), y' ∈ ((U σ).X k).dom → (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z → (⟨k, y'⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by
  intro E _ _ _ H Dw l Xo c r U σ hU Z k y y' hy' hyZ
  obtain ⟨hy, hZ⟩ := hyZ
  have hd : Dom (E := E) 0 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩
  have hsec := hU.2.2.2.2.1 0 0 hd (GlobalTheory.FlatLine.idem Z) (GlobalTheory.CompRestr.idem_mem_sec Z) k
  obtain ⟨w, hw⟩ := GlobalTheory.CompRat.const_of_idem_on
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r ((U σ).X k)).isPreconnected hsec.1.continuousOn fun x _ => by
      rw [← GlobalTheory.CompRat.rdU_mul_apply', GlobalTheory.FlatLine.idem_mul_idem]
  have hA : AllTest Xo c := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1.test
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have e1 : ∀ (g : Rul Xo c) (x : Frame ((U σ).X k).Ψ r) (h : x ∈ ((U σ).X k).dom),
      rdU (U σ) g k x = toC (evR Xo c g ((U σ).un k ⟨x, h⟩)) := fun g x h => dif_pos h
  have h1 : rdU (U σ) (GlobalTheory.FlatLine.idem Z) k y = 1 := by
    rw [e1 _ _ hy, GlobalTheory.FlatLine.evR_idem hZ (hA _ _)]
    rfl
  have h1' : rdU (U σ) (GlobalTheory.FlatLine.idem Z) k y' = 1 := (hw y' hy').trans ((hw y hy).symm.trans h1)
  refine ⟨hy', ?_⟩
  by_contra hn
  have hoff : LiesOff Z ((U σ).un k ⟨y', hy'⟩) := by
    intro s hs
    apply hn
    intro s'
    have : s = s' := Subsingleton.elim (α := PrimeSpectrum ℂ) s s'
    exact this ▸ hs
  have h0 := GlobalTheory.FlatLine.idem_mem_suppOn Z (CAt σ) _ hoff
  rw [e1 _ _ hy', h0] at h1'
  exact zero_ne_one (α := ℂ) h1'

end GlobalTheory.FramesUnion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSetStatement
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePointsOverComponent_open_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ), IsUnf (U σ) → ∀ (Z : Comp Xo c) (k : (U σ).Comp) (y y' : Frame ((U σ).X k).Ψ r), y' ∈ ((U σ).X k).dom → (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z → (⟨k, y'⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by
  first | exact @GlobalTheory.FramesUnion.framesOn_of_mem | exact GlobalTheory.FramesUnion.framesOn_of_mem | (intros; apply GlobalTheory.FramesUnion.framesOn_of_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosed
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixExp

theorem pow_mul_le_of_cls_eq {k : Type} [Field k] {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)]
    (h : Published.NefProductNonneg) (hp : IsProjOver (strHom k (X := Y))) {e : ℕ}
    (hD : topologicalKrullDim Y = e) {N N' N₀ : LB Y} (hN : IsNef k N) (hN' : IsNef k N')
    (h₀ : N₀.IsLB) (a b : ℕ) (hc : cls N₀ h₀ = a • cls N hN.isLB + b • cls N' hN'.isLB) :
    (a : ℤ) ^ e * interNum k (structureModule Y) (fun _ : Fin e => N) ≤
      interNum k (structureModule Y) (fun _ : Fin e => N₀) := by
  have := isNoetherian_of_isProjOver hp
  have H := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k Y) (structureModule Y) hp
    (d := e) (by rw [suppDim_structureModule, hD])
  have hL : ∀ j, IsNef k ((![N, N'] : Fin 2 → LB Y) j) := fun j => by
    fin_cases j
    exacts [hN, hN']
  have e₁ := H.interNum_of_cls_eq_sum (L := ![N, N']) (fun j => (hL j).isLB)
    (Q := fun _ => N₀) (fun _ => h₀) (fun _ => ![(a : ℤ), (b : ℤ)])
    (fun _ => by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, natCast_zsmul]
      exact hc)
  have e₂ := Finset.single_le_sum
    (f := fun c : Fin e → Fin 2 =>
      (∏ i, (![(a : ℤ), (b : ℤ)] : Fin 2 → ℤ) (c i)) *
        interNum k (structureModule Y) (![N, N'] ∘ c))
    (fun c _ => mul_nonneg (Finset.prod_nonneg fun i _ => by
        generalize c i = j
        fin_cases j <;> simp)
      (h.interNum_nonneg (N := ![N, N'] ∘ c) hp hD fun i => hL (c i)))
    (Finset.mem_univ fun _ => 0)
  rw [e₁]
  refine le_trans (le_of_eq ?_) e₂
  simp only [Matrix.cons_val_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end GlobalTheory.MixExp


open GlobalTheory.MixExp in
theorem GlobalTheory.mixExp_interNumRed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' N₀ : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (h₀ : N₀.IsLB) (a b : ℕ) (Z : Closeds X) (e : ℕ), IsNef k N → IsNef k N' → cls N₀ h₀ = a • cls N hN + b • cls N' hN' → topologicalKrullDim (Z : Set X) = e → (a : ℤ) ^ e * interNumRed k Z (fun _ : Fin e => N) ≤ interNumRed k Z (fun _ : Fin e => N₀) := by
  intro h k _ X q hq
  letI := algebraΓOfHom q
  intro N N' N₀ hN hN' h₀ a b Z e hnef hnef' hc hZ
  have hp : IsProjOver (strHom k (X := X)) := by rwa [strHom_eq (f := q) fun _ => rfl]
  letI := algebraΓAlong k (redι Z)
  have hi := appTop_algebraMap_along k (redι Z)
  have hpZ : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    obtain ⟨n, f, hf, hs⟩ := hp
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩
  change (a : ℤ) ^ e * interNumOn k (redι Z) (fun _ : Fin e => N) ≤
    interNumOn k (redι Z) (fun _ : Fin e => N₀)
  rw [interNumOn_eq_interNum_pull hi fun _ => hN, interNumOn_eq_interNum_pull hi fun _ => h₀]
  refine pow_mul_le_of_cls_eq h.1 hpZ ((topologicalKrullDim_red Z).trans hZ)
    (hnef.pull_of_isClosedImmersion (redι Z) hi) (hnef'.pull_of_isClosedImmersion (redι Z) hi)
    (LB.isLB_pull h₀ (redι Z)) a b ?_
  rw [cls_pull h₀, cls_pull hN, cls_pull hN', hc, map_add (f := _), map_nsmul, map_nsmul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_intersection_le_of_nef_class_on_closed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' N₀ : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (h₀ : N₀.IsLB) (a b : ℕ) (Z : Closeds X) (e : ℕ), IsNef k N → IsNef k N' → cls N₀ h₀ = a • cls N hN + b • cls N' hN' → topologicalKrullDim (Z : Set X) = e → (a : ℤ) ^ e * interNumRed k Z (fun _ : Fin e => N) ≤ interNumRed k Z (fun _ : Fin e => N₀) := by
  first | exact @GlobalTheory.mixExp_interNumRed | exact GlobalTheory.mixExp_interNumRed | (intros; apply GlobalTheory.mixExp_interNumRed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInfiniteScaling
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInfiniteScaling
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusTheta

variable (F : Type) [Field F] [NumberField F]

theorem infScale_mul' (a b : ℝ) : infScale F a * infScale F b = infScale F (a * b) := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ = _
    rw [← map_mul, ← map_mul]
    rfl
  · show (1 : FiniteAdeleRing (𝓞 F) F) * 1 = 1
    exact mul_one 1

theorem infScale_one' : infScale F 1 = 1 := by
  simp only [infScale, map_one]
  rfl

theorem norm_infScale_fst (t : ℝ) (w : InfinitePlace F) : ‖(infScale F t).1 w‖ = |t| := by
  rw [← GroundTheory.Global.normAtPlace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply]
  simp only [infScale, RingEquiv.apply_symm_apply]
  exact mixedEmbedding.normAtPlace_real w t

theorem distribHaarChar_infScale (t : ℝ) (ht : 0 < t) (a : (AF F)ˣ) (ha : (a : AF F) = infScale F t) :
    (distribHaarChar (AF F) a : ℝ) = t ^ Module.finrank ℚ F := by
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖((a : AdeleRing (𝓞 F) F)).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [show (a : AdeleRing (𝓞 F) F) = infScale F t from ha]
    simp [infScale]
  rw [h2, mul_one]
  simp_rw [show (a : AdeleRing (𝓞 F) F) = infScale F t from ha, norm_infScale_fst, abs_of_pos ht]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

theorem lintegral_infScale_pi : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (u : κ → ℝ), (∀ j, 0 < u j) →
    ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (f : (κ → AF F) → ℝ≥0∞), ∫⁻ x, f (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) ∂μ =
      (ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F))⁻¹ * ∫⁻ x, f x ∂μ := by
  intro F _ _ κ _ u hu μ hμ f
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  let s : (κ → AF F)ˣ :=
    { val := fun j => infScale F (u j)
      inv := fun j => infScale F (u j)⁻¹
      val_inv := funext fun j => by
        show infScale F (u j) * infScale F (u j)⁻¹ = 1
        rw [infScale_mul', mul_inv_cancel₀ (hu j).ne', infScale_one']
      inv_val := funext fun j => by
        show infScale F (u j)⁻¹ * infScale F (u j) = 1
        rw [infScale_mul', inv_mul_cancel₀ (hu j).ne', infScale_one'] }
  have hχ : ((distribHaarChar (κ → AF F) s : ℝ≥0) : ℝ) = ∏ j, u j ^ Module.finrank ℚ F := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : κ => AF F), NNReal.coe_prod]
    exact Finset.prod_congr rfl fun j _ => distribHaarChar_infScale F (u j) (hu j) _ rfl
  have h1 : μ.map (fun x => s • x) = DomMulAct.mk s⁻¹ • μ := by
    ext A hA
    rw [Measure.map_apply (measurable_const_smul s) hA, Measure.domSMul_apply, Equiv.symm_apply_apply,
      Set.preimage_smul]
  have h2 : μ.map (fun x => s • x) = ((distribHaarChar (κ → AF F) s)⁻¹ : ℝ≥0) • μ := by
    rw [h1, Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk s⁻¹ • μ) μ,
      addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]
  have h3 : ∫⁻ x, f (fun j => infScale F (u j) * x j) ∂μ = ∫⁻ y, f y ∂(μ.map (fun x => s • x)) :=
    (lintegral_map_equiv f (Homeomorph.smul s).toMeasurableEquiv).symm
  rw [h3, h2, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul, ← hχ, ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_inv (distribHaarChar_pos).ne']

end GlobalTheory.TorusTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInfiniteScalingStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_infinite_scaling : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (u : κ → ℝ), (∀ j, 0 < u j) →
    ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (f : (κ → AF F) → ℝ≥0∞), ∫⁻ x, f (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) ∂μ =
      (ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F))⁻¹ * ∫⁻ x, f x ∂μ := by
  first | exact @GlobalTheory.TorusTheta.lintegral_infScale_pi | exact GlobalTheory.TorusTheta.lintegral_infScale_pi | (intros; apply GlobalTheory.TorusTheta.lintegral_infScale_pi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankInfRangeAddInfKer
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadOnRec

theorem finrank_inf_range_add_inf_ker {K M : Type} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (e : M →ₗ[K] M) (he : ∀ x, e (e x) = e x) (V : Submodule K M) (hV : ∀ x ∈ V, e x ∈ V) :
    finrank K (V ⊓ LinearMap.range e : Submodule K M) + finrank K (V ⊓ LinearMap.ker e : Submodule K M) = finrank K V := by
  let f : V →ₗ[K] V := e.restrict hV
  have h1 : (LinearMap.range f).map V.subtype = V ⊓ LinearMap.range e := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨hV x x.2, x, rfl⟩
    · rintro ⟨hy, z, rfl⟩
      exact ⟨⟨e z, hy⟩, ⟨⟨e z, hy⟩, Subtype.ext (he z)⟩, rfl⟩
  have h2 : (LinearMap.ker f).map V.subtype = V ⊓ LinearMap.ker e := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, congrArg Subtype.val hx⟩
    · rintro ⟨hy, hk⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hk, rfl⟩
  rw [← h1, ← h2, Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq]
  exact LinearMap.finrank_range_add_finrank_ker f

theorem finrank_eq_of_bij {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (hf : Function.Bijective f) (p : Submodule K M) (q : Submodule K N) (h : ∀ x, x ∈ p ↔ f x ∈ q) :
    finrank K p = finrank K q := by
  have e : p.map f = q := by
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    constructor
    · rintro ⟨x', hx', e'⟩
      exact hf.1 e' ▸ (h x').1 hx'
    · intro hy
      exact ⟨x, (h x).2 hy, rfl⟩
  rw [← e]
  exact (Submodule.equivMapOfInjective f hf.1 p).finrank_eq

end GlobalTheory.BadOnRec

namespace GlobalTheory.BadOnRec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance runAlgBad {D : D7} {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] (r : OnTies.RunData J) :
    Algebra r.full.J.Q.c.F D.what₂.LL := inst

section General

open scoped TensorProduct

attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)}

theorem mem_eig_iff (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ F.P0 F.ψ0⁻¹ ph y) (ha : ActionPin h fw ι ℓ)
    (hG : R.IsGrp F) (hinc : F.P0 ≤ inc.range) (x : Fin (O.nZ i) → D.what₂.LL) :
    x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ ↔ GlobalTheory.OnTies.toForms h fw ι z x ∈ GlobalTheory.CovTop.spType R F ι := by
  have hb := GlobalTheory.OnTies.toForms_bijective h fw ι z
  have e1 : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ ↔ ∀ u : O.U, O.ρ i u x = ((O.ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold Formalism.EigenvalueLevelCeiling.eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  have e2 : ∀ (g : P) (hg : inc g ∈ F.P0), O.ρ i g x = ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) • x ↔
      (R.FW ι).ρ (inc g) (GlobalTheory.OnTies.toForms h fw ι z x) =
        (((R.FW ι).chi (inc g) * F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) • GlobalTheory.OnTies.toForms h fw ι z x :=
    fun g hg => by
      rw [← t.rho_eq_of_actionPin ha, GlobalTheory.OnCoord.chi_eq_one hG ι hg, one_mul, ← t.ψ_eq g hg, ← map_smul, hb.1.eq_iff]
  refine e1.trans ⟨fun hx => ?_, fun hx u => ?_⟩
  · rintro ⟨g, hg⟩
    obtain ⟨u, rfl⟩ := hinc hg
    exact (e2 u hg).1 (hx ⟨u, t.U_eq.ge hg⟩)
  · exact (e2 u (t.U_eq.le u.2)).2 (hx ⟨inc u, t.U_eq.le u.2⟩)

end General

end GlobalTheory.BadOnRec

namespace GlobalTheory.BadOnRec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance] runAlgBad

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}

end Point

end GlobalTheory.BadOnRec

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.BigOn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponents
noncomputable section

namespace GlobalTheory.CuspSplit

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem idem_mul_mem_cuspOn (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G : WTZ D.host.E}
    (F : cuspW Xo c U G) : idem Z * (F : Rul Xo c) ∈ cuspOn U Z G := by
  refine ⟨GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2, ?_⟩
  rw [mul_comm]
  exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem idem_mul_of_mem_cuspOn {Z : Comp Xo c} {G : WTZ D.host.E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) :
    idem Z * f = f :=
  (mem_suppOn_iff_idem_mul (cuspW_le_secZ G hf.1) Z).1 hf.2

theorem idem_mul_eq_zero {Z Z' : Comp Xo c} (h : Z ≠ Z') {G : WTZ D.host.E} {f : Rul Xo c}
    (hf : f ∈ cuspOn U Z' G) : idem Z * f = 0 := by
  calc idem Z * f = idem Z * (idem Z' * f) := by rw [idem_mul_of_mem_cuspOn hf]
    _ = 0 := by rw [← mul_assoc, idem_mul_idem_of_ne h, zero_mul]

theorem finsum_parts (f : Rul Xo c) : ∑ᶠ Z : Comp Xo c, idem Z * f = f := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [finsum_eq_sum_of_fintype, sum_idem_mul]

theorem mem_latOn_part (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G : WTZ D.host.E} (F : cuspW Xo c U G)
    (hF : F ∈ latW U G) (Z : Comp Xo c) :
    (⟨_, idem_mul_mem_cuspOn hU Z F⟩ : cuspOn U Z G) ∈ latOn U Z G := by
  rw [latOn, mem_supLat_iff (idem_mul_mem_cuspOn hU Z F).2]
  intro la v hv
  show 0 ≤ v (idem Z * (F : Rul Xo c))
  rw [(isVal_valOn hv).mul, val_idem hv, zero_add]
  exact (mem_supLat.1 hF) la v (valOn_subset Z la hv)

theorem mem_latW_of_parts (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G : WTZ D.host.E} (F : cuspW Xo c U G)
    (h : ∀ Z, (⟨_, idem_mul_mem_cuspOn hU Z F⟩ : cuspOn U Z G) ∈ latOn U Z G) : F ∈ latW U G := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  refine mem_supLat.2 ?_
  intro la v hv
  have hval := isVal_valSet la v hv
  rw [← sum_idem_mul (F : Rul Xo c)]
  refine Finset.sum_induction _ (fun x => 0 ≤ v x) (fun a b ha hb => (le_min ha hb).trans (hval.add a b))
    (by rw [hval.zero]; exact le_top) fun Z _ => ?_
  exact (mem_supLat.1 ((mem_latOn U).1 (h Z))) la v hv

theorem cuspOn_indep (G : WTZ D.host.E) : iSupIndep (fun Z : Comp Xo c => cuspOn U Z G) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), cuspOn U j G) ≤ LinearMap.ker (LinearMap.mulLeft c.F (idem Z)) :=
    iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
      exact idem_mul_eq_zero (Ne.symm hj) hy
  have h0 : idem Z * x = 0 := by
    have := hle hx'
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply] at this
  calc x = idem Z * x := (idem_mul_of_mem_cuspOn hx).symm
    _ = 0 := h0

theorem iSup_cuspOn (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G : WTZ D.host.E) :
    ⨆ Z : Comp Xo c, cuspOn U Z G = cuspW Xo c U G := by
  refine le_antisymm (iSup_le fun Z => cuspOn_le U Z G) fun F hF => ?_
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [← sum_idem_mul F]
  exact Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z (idem_mul_mem_cuspOn hU Z ⟨F, hF⟩)

theorem coe_mem_of_mem_partLat {Z : Comp Xo c} {G : WTZ D.host.E} {g : cuspW Xo c U G}
    (hg : g ∈ partLat U Z G) : (g : Rul Xo c) ∈ cuspOn U Z G := by
  obtain ⟨f, -, rfl⟩ := hg
  exact f.2

theorem partLat_indep (G : WTZ D.host.E) : iSupIndep (fun Z : Comp Xo c => partLat U Z G) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), partLat U j G) ≤
      (LinearMap.ker ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype)).restrictScalars (𝓞 c.F) :=
    iSup₂_le fun j hj y hy => by
      rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.mulLeft_apply]
      exact idem_mul_eq_zero (Ne.symm hj) (coe_mem_of_mem_partLat hy)
  have h0 : idem Z * (x : Rul Xo c) = 0 := by
    have := hle hx'
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.mulLeft_apply] at this
  apply Subtype.ext
  calc (x : Rul Xo c) = idem Z * x := (idem_mul_of_mem_cuspOn (coe_mem_of_mem_partLat hx)).symm
    _ = 0 := h0

theorem iSup_partLat (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G : WTZ D.host.E) :
    ⨆ Z : Comp Xo c, partLat U Z G = latW U G := by
  refine le_antisymm (iSup_le fun Z => partLat_le U Z G) fun F hF => ?_
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  have hF' : F = ∑ Z : Comp Xo c,
      (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U G) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_idem_mul _).symm
  rw [hF']
  refine Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z ?_
  exact ⟨⟨_, idem_mul_mem_cuspOn hU Z F⟩, mem_latOn_part hU F hF Z, rfl⟩

theorem splits : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ G : WTZ D.host.E, Splits U G :=
  fun _ _ _ _ _ _ _ _ _ _ hU G =>
    ⟨fun F => ⟨(finsum_parts _).symm, fun Z => idem_mul_mem_cuspOn hU Z F,
        ⟨fun hF Z => mem_latOn_part hU F hF Z, mem_latW_of_parts hU F⟩⟩,
      ⟨cuspOn_indep G, iSup_cuspOn hU G⟩, partLat_indep G, iSup_partLat hU G⟩

end GlobalTheory.CuspSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponentsStatement
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_supLattice_split_over_components : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ G : WTZ D.host.E, Splits U G := by
  first | exact @GlobalTheory.CuspSplit.splits | exact GlobalTheory.CuspSplit.splits | (intros; apply GlobalTheory.CuspSplit.splits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqTopOfNotMemSupport
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem idlAlong_eq_top_of_notMem_support (X : Scheme.{0}) (I : X.IdealSheafData) (R : Type) [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ X) (h : ξ (closedPoint R) ∉ I.support) : idlAlong I ξ = ⊤ := by
  have e : FinalTheorems.stalkId I (ξ (closedPoint R)) = ⊤ :=
    not_not.1 fun h' => h ((mem_support_iff_stalkId I _).2 h')
  rw [idlAlong, e, Ideal.map_top]

end GlobalTheory.LocM
end
