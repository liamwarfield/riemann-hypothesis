module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundParameterRequirementsEventuallyFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartRealisationWithScalarsCharOfWeak
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRationalOfOneMapOverL
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoRunDatumBoundUnitAtIndefinitePoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Div.CoordOpp

theorem piW_inclR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (e : E) :
    piW t (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = t e := by
  have h1 : compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Fv F v) e := by
    simp [compFin, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  simp only [piW, RingHom.comp_apply, h1]
  exact splitProj_inclR t e

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW t (cA σ z) = piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [piW, cA, compFin, splitProj]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem incM_map_piW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {m k : Type} (J : Matrix m k E) :
    (incM F J).map (piW t) = J.map t := by
  ext i j
  simp [incM, piW_inclR]

theorem unit_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) :
    ((mat g).map (piW t))ᵀ * J.map t * (mat g).map (piW (t.comp σ)) = J.map t := by
  have hg := g.2
  change ((mat g))ᵀ * incM F J * (mat g).map (cA σ) = incM F J at hg
  have := congrArg (fun M => M.map (piW t)) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, incM_map_piW] at this
  have e2 : ((mat g).map (cA σ)).map (piW t) = (mat g).map (piW (t.comp σ)) := by
    ext i j; simp [piW_cA]
  rw [e2] at this
  simpa [Matrix.transpose_map] using this

end GlobalTheory.Div.CoordOpp

open GlobalTheory.Div.CoordOpp in
theorem GlobalTheory.Div.CoordOpp.coord_opp_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (g : UA σ X.J) (h : UA σ W.J)
    (x : Matrix (Fin n) (Fin d) (AE F E)),
    ((mat g).map (piW t))ᵀ * -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (mat g * x * (mat h)ᵀ).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) * (mat h).map (piW t) = -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) := by
  intro F E _ _ _ _ _ σ n d X W v t g h x
  have hg := unit_map σ g t
  have hh := unit_map σ h t
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.map_mul,
    Matrix.transpose_map, Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  set gt := (mat g).map (piW t)
  set gb := (mat g).map (piW (t.comp σ))
  set ht := (mat h).map (piW t)
  set hb := (mat h).map (piW (t.comp σ))
  set xb := x.map (piW (t.comp σ))
  have hh' : hbᵀ * (W.J.map t)ᵀ * ht = (W.J.map t)ᵀ := by
    have := congrArg Matrix.transpose hh
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  calc gtᵀ * (X.J.map t * (gb * xb * ((mat h)ᵀ).map (piW (t.comp σ))) * (W.J.map t)ᵀ) * ht
      = (gtᵀ * X.J.map t * gb) * xb * (hbᵀ * (W.J.map t)ᵀ * ht) := by
        simp only [hb, Matrix.transpose_map, Matrix.mul_assoc]
    _ = X.J.map t * xb * (W.J.map t)ᵀ := by rw [hg, hh']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransformStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_moment_matrix_transform : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (g : UA σ X.J) (h : UA σ W.J)
    (x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ((mat g).map (piW t))ᵀ * -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (mat g * x * (mat h)ᵀ).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) * (mat h).map (piW t) = -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) := by
  first | exact @GlobalTheory.Div.CoordOpp.coord_opp_conj | exact GlobalTheory.Div.CoordOpp.coord_opp_conj | (intros; apply GlobalTheory.Div.CoordOpp.coord_opp_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RowsOfPageFix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize Formalism.MainNotions.WeightAlgebra

theorem rows_of_pageFix : ∀ (eps : ℝ) (Fm : FamP eps), DC.PageFix Fm → 1000 ≤ Fm.CP → ∃ x₁ : ℝ, ∀ x (hx : Fm.x1 < x), x₁ ≤ x → ∀ i : Fm.Ix x, SizesAt (Fm.L x i) ∧ (Fm.params x hx i).CnW = 10 ∧ (∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1) ∧ 1000 ≤ (Fm.parT x hx i).CP ∧ (Fm.parT x hx i).CP ^ 20 ≤ zBase (Fm.L x i) ∧ DV.KapDef (Fm.D x i) ∧ Nonempty (ErrX (Fm.D x i)) ∧ (Fm.L x i).sc.x = x ∧ (JointQ (Fm.D x i) → FieldSmall (Fm.D x i) (Fm.L x i)) := by
  intro eps Fm hP hCP
  refine ⟨max ((10 : ℝ) ^ 60) (Fm.CP ^ 20), ?_⟩
  intro x hx hx₁ i
  have hS : SizesAt (Fm.L x i) := Fm.sizes x hx i
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hCnW : (Fm.params x hx i).CnW = 10 := (Fm.fixed.2.2.2.2.2.2.2 x hx i).1

  have hg : ∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1 := by
    intro k
    have hpr := (Fm.D x i).host.g_prime k
    have hpos : (0 : ℝ) < ((Fm.D x i).host.g k : ℝ) := by exact_mod_cast hpr.pos
    have hle := (hP.2.2.2.2.2.2.2.2 x hx i).2.2.1 k
    have := (Real.log_le_iff_le_exp hpos).2 hle
    linarith
  have h60 : (10 : ℝ) ^ 60 ≤ (Fm.L x i).sc.x := by
    rw [hLx]; exact le_trans (le_max_left _ _) hx₁
  obtain ⟨hH, hF⟩ := hostSz_of_sizes (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) hS hg h60

  have hCPeq : (Fm.parT x hx i).CP = Fm.CP := by
    unfold FamP.CP
    rw [← Fm.parT_K x hx i]
    rfl
  have hL4 : (4 : ℝ) ≤ (Fm.L x i).sc.L := hH.len

  have hf : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have hK := hS.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    rcases Nat.eq_zero_or_pos (Fm.D x i).R.f with h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero, zero_mul] at hK
      have hxpos : 0 < (Fm.L x i).sc.x ^ szTh (Fm.L x i) :=
        Real.rpow_pos_of_pos (by linarith [(Fm.L x i).sc.one_lt_alt]) _
      have := mul_pos hxpos (by linarith : (0 : ℝ) < (Fm.L x i).sc.L)
      linarith
    · exact_mod_cast hpos
  refine ⟨hS, hCnW, hg, ?_, ?_, (Fm.ex x hx i).kap_def, ⟨(Fm.ex x hx i).errX⟩, hLx, ?_⟩
  · rw [hCPeq]; exact hCP
  ·
    unfold zBase
    rw [hCPeq]
    have hr : x ≤ ((Fm.D x i).R.r : ℝ) := by
      have h := scale_le_rank hS
      rw [hLx] at h
      exact h
    have hr0 : (0 : ℝ) ≤ ((Fm.D x i).R.r : ℝ) := Nat.cast_nonneg _
    have h1 : ((Fm.D x i).R.r : ℝ) ≤ (Fm.D x i).R.f * (Fm.D x i).R.r := le_mul_of_one_le_left hr0 hf
    have h2 : ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.r ≤ (Fm.D x i).R.f * (Fm.D x i).R.r * (Fm.L x i).sc.L :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith [le_trans (le_max_right _ _) hx₁]
  · intro hJ
    exact hF (hJ.2.2.2.2 _ hH)

end GlobalTheory.FinalRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamily
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.OntoNum

theorem pageNum_along : ∀ x₁ : ℝ, Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    PageNum (Fm.parT x hx ι) x₁ ∧ 3 ≤ (Fm.L x ι).sc.x ∧ ((Fm.D x ι).R.k : ℝ) * (Fm.L x ι).sc.b' ≤ (Fm.L x ι).sc.b ∧
      3 ≤ (Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 5) ∧ 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (Fm.D x ι).R.nV := by
  intro x₁
  obtain ⟨ε1, hε1, hS⟩ := GlobalTheory.T.indexBoundParameterRequirements_eventually_family
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := hS eps he hle
  refine ⟨K.sup ⟨1000, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL
  have hCP : (1000 : ℝ) ≤ Fm.CP := hL2.1 Fm.CP (by simp [FamP.cPre])
  obtain ⟨xa, hxa⟩ := hK Fm CH hc hL1
  obtain ⟨xb, hxb⟩ := GlobalTheory.FinalRows.rows_of_pageFix eps Fm hc.1 hCP
  refine ⟨max (max xa xb) x₁, fun x hx hx0 ι => ?_⟩
  have hs := hxa x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0) ι
  obtain ⟨hSz, hCnW, hg, hCP', hz, -, -, hsx, -⟩ := hxb x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0) ι
  have hx1 : x₁ ≤ (Fm.L x ι).sc.x := by rw [hsx]; exact le_trans (le_max_right _ _) hx0
  exact ⟨⟨hSz, hCnW, hg, hCP', hz, hx1⟩, GlobalTheory.IndexAssembly.three_le_scale_of_pow_bound hs.2.1, hs.2.2.2.2.2.2.2.2.1, by linarith [hs.2.1],
    (Fm.parT x hx ι).nV_ge⟩

end GlobalTheory.OntoNum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamilyStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.runNumericalConditions_hold_along_family : ∀ x₁ : ℝ, Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, PageNum (Fm.parT x hx ι) x₁ ∧ 3 ≤ (Fm.L x ι).sc.x ∧ ((Fm.D x ι).R.k : ℝ) * (Fm.L x ι).sc.b' ≤ (Fm.L x ι).sc.b ∧ 3 ≤ (Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 5) ∧ 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (Fm.D x ι).R.nV := by
  first | exact @GlobalTheory.OntoNum.pageNum_along | exact GlobalTheory.OntoNum.pageNum_along | (intros; apply GlobalTheory.OntoNum.pageNum_along <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEstimateStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassSumsRationalOfRayClassFields
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassSumsRationalOfRayClassFields
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OntoChain
set_option autoImplicit false
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistedRatBase

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem exists_base_lift (hU : R.LUnif) (hB : GlobalTheory.BigOn.BaseLinks R F)
    (hRk : Formalism.L2.Indef.Tree.RankRows ((R.toCx F).data F.cr false)) (i : Fin D.R.m) :
    ∃ (x₀ : A.fam.amb.FL i A.μ0) (y : Fin (R.nW i) → D.what₂.LL),
      (R.FW i).j (sg0 D A) y = R.thG i A.μ0 (R.jV i A.μ0 x₀) ∧ (R.FW i).j (sg0 D A) y ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  have hd : 0 < Module.finrank D.what₂.LL (R.WL F false i) := hRk.1.trans_eq (hRk.2 i).symm
  obtain ⟨y, hy⟩ : ∃ y, (GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y = fun _ => 1 :=
    ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false) (RealDat.ewNorm false) (RealDat.nP_pos false) hB.1
      hB.2.1 i A.μ0).2 _
  have h1 := GlobalTheory.BigOnBase.j_thetaMat_base hB i A.μ0 y
  refine hn ⟨(A.fam.L i A.μ0).toF (GlobalTheory.OntoChain.liftLvl F) (GlobalTheory.OntoChain.liftSub R F i A.μ0) y,
    GlobalTheory.OntoChain.coordMap R F i ((GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y), h1, fun h0 => ?_⟩
  have h2 : GlobalTheory.OntoChain.coordMap R F i ((GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y) = 0 :=
    (injective_iff_map_eq_zero _).1 (j_injective hU i) _ h0
  have h3 := (injective_iff_map_eq_zero _).1 (GlobalTheory.OntoChain.coordMap_injective (R := R) (F := F) i) _ h2
  exact one_ne_zero (congrFun (hy.symm.trans h3) ⟨0, hd⟩)

theorem baseLiftNeZero (hU : R.LUnif) (hB : GlobalTheory.BigOn.BaseLinks R F)
    (hRk : Formalism.L2.Indef.Tree.RankRows ((R.toCx F).data F.cr false)) :
    ∀ i, ∃ x₀ : A.fam.amb.FL i A.μ0, R.thG i A.μ0 (R.jV i A.μ0 x₀) ≠ 0 := fun i =>
  (exists_base_lift hU hB hRk i).imp fun _ h => h.elim fun _ h => h.1.symm.trans_ne h.2

theorem twistedRational_of_rayField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), R.Char F → IoExt R → R.LUnif → (∀ i, OMPins J R κ v₀ O i) → QGuard R → (∀ i, OneMapRowR J R κ v₀ O (fun _ => 1) i) → BaseLinks R F → RankRows ((R.toCx F).data F.cr false) → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → TwistedRational R F (fun _ => 1) := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw O hC hio hU hO hQ hrow hB hRk hray
  exact GlobalTheory.TwistedClassSum.twistedRational hC fw hio hU hO hQ hrow
    (GlobalTheory.TwistField.coverField_of_containsRayField D G Pl0 T0 A J R fw.laws hC.lev hQ hray) (baseLiftNeZero hU hB hRk)

end GlobalTheory.TwistedRatBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassSumsRationalOfRayClassFieldsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OntoChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedClassSums_rational_of_rayClassFields : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), R.Char F → IoExt R → R.LUnif → (∀ i, OMPins J R κ v₀ O i) → QGuard R → (∀ i, OneMapRowR J R κ v₀ O (fun _ => 1) i) → BaseLinks R F → RankRows ((R.toCx F).data F.cr false) → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → TwistedRational R F (fun _ => 1) := by
  first | exact @GlobalTheory.TwistedRatBase.twistedRational_of_rayField | exact GlobalTheory.TwistedRatBase.twistedRational_of_rayField | (intros; apply GlobalTheory.TwistedRatBase.twistedRational_of_rayField <;> assumption)
end
end

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}


set_option maxHeartbeats 1000000 in
theorem oneMapRowR_charOf (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : Fin D.R.m → ℂ)
    (i : Fin D.R.m) (h : OneMapRowR J R κ v₀ O ph i) :
    OneMapRowR J (charOf R F) κ v₀ (fun k => reOM (O k) F) ph i := by
  refine ⟨?_, fun hq => ?_⟩
  · obtain ⟨cc, ph', h0⟩ := h.1
    exact ⟨cc, ph', h0⟩
  · obtain ⟨O', h1, h2, h3⟩ := h.2 hq
    refine ⟨{ O' with }, h1, ⟨⟨h2.lift.field, h2.lift.std, h2.lift.v0, h2.lift.c0, h2.lift.lev⟩,
      fun t => ⟨(h2.tuple t).reps, (h2.tuple t).B, (h2.tuple t).xi, (h2.tuple t).phi, (h2.tuple t).half⟩,
      h2.act, h2.bad, h2.reps, h2.ep, h2.io, h2.w, h2.cov, h2.cxi, h2.model₂⟩, h3⟩

end Gen

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem phEff_eq_one : phEff p.R = fun _ => 1 := by
  funext i
  simp [phEff, p.phsOne i]

theorem splitPartRealisation_satisfies_qGuard : QGuard (R2 p) := p.qGuard

end Point

end GlobalTheory.BigOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPair
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.ShareOn.WhitBase

section SlopeTestRemainingChoices

open Formalism.L2.DIV

variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}

theorem isUniUp_map_iff (f : κ ≃+* κ') (M : GL (Fin r) κ) :
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp ((Matrix.GeneralLinearGroup.map f.toRingHom M : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') ↔
      M ∈ unip κ r := by
  have hc : ∀ a b, ((Matrix.GeneralLinearGroup.map f.toRingHom M : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') a b =
      f ((M : Matrix (Fin r) (Fin r) κ) a b) := fun a b => rfl
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := (h i j).1 hij
      rw [hc] at this
      exact f.injective (by rw [this, map_zero])
    · have := (h i i).2 rfl
      rw [hc] at this
      exact f.injective (by rw [this, map_one])
  · intro h a b
    refine ⟨fun hab => ?_, fun hab => ?_⟩
    · rw [hc, unip_lower h hab, map_zero]
    · subst hab
      rw [hc, unip_diag h, map_one]

theorem edgeSum_supEdge_eq (M : GL (Fin r) κ) :
    edgeSum supEdge M = ∑ i ∈ Finset.range (r - 1), Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) i (i + 1) := by
  classical
  have h1 : ∀ i : Fin r, (∑ j : Fin r, if supEdge i j then (M : Matrix (Fin r) (Fin r) κ) i j else 0) =
      Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) i.val (i.val + 1) := by
    intro i
    unfold Formalism.MainNotions.ArithmeticCylinders.entN
    by_cases hi : i.val + 1 < r
    · rw [Finset.sum_eq_single ⟨i.val + 1, hi⟩]
      · rw [if_pos (show supEdge i ⟨i.val + 1, hi⟩ from rfl), dite_eq_left ⟨i.isLt, hi⟩]
      · intro j _ hj
        rw [if_neg (show ¬ supEdge i j from fun e => hj (Fin.ext e))]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dite_eq_right (by omega)]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg (show ¬ supEdge i j from fun e => by
        have := j.isLt
        unfold supEdge at e
        omega)]
  unfold edgeSum
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) i (i + 1)) r]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Finset.sum_range_succ, Nat.add_sub_cancel]
    have : Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) s (s + 1) = 0 := by
      unfold Formalism.MainNotions.ArithmeticCylinders.entN
      rw [dite_eq_right (by omega)]
    rw [this, add_zero]

theorem entN_map (f : κ ≃+* κ') (M : GL (Fin r) κ) (a b : ℕ) :
    Formalism.MainNotions.ArithmeticCylinders.entN ((Matrix.GeneralLinearGroup.map f.toRingHom M : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') a b =
      f (Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) a b) := by
  unfold Formalism.MainNotions.ArithmeticCylinders.entN
  split_ifs
  · rfl
  · rw [map_zero]

end SlopeTestRemainingChoices

section Comparison₂

open Formalism.L2.DIV Formalism.BasicNotions

variable {D : D7} {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G}
  {ψs : Ps →* D.what₂.LLˣ} {eG : G ≃* G0g D.nd} {Pg : Finset (Pl D.host.E)}
  {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg} {res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
  {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC : G ≃* G0 Pg D.R.r}

theorem mem_iff_of_lvlTie (h : LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC) (g : G) :
    g ∈ P0 ↔ ∀ kv, Formalism.MainNotions.ArithmeticCylinders.IsUniUp ((eG g kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  rw [h.p0 g]
  show eC g ∈ Subgroup.pi Set.univ _ ↔ _
  rw [Subgroup.mem_pi]
  constructor
  · intro hx kv
    rw [h.comp g kv, isUniUp_map_iff]
    exact hx (pl kv) (Set.mem_univ _)
  · intro hx PP _
    obtain ⟨kv, rfl⟩ := pl.surjective PP
    have := hx kv
    rw [h.comp g kv, isUniUp_map_iff] at this
    exact this

theorem chi_of_lvlTie (h : LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC) (g : P0)
    (hg : eC g ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ).H) :
    ((ψ0 g : D.what₂.LLˣ) : D.what₂.LL) = ∏ PP : ↥Pg, ψ PP.1 (edgeSum supEdge (eC g PP)) := by
  rw [h.chi0 g hg]
  unfold Formalism.L2.DIV.P0 LevelP.ofLocal
  dsimp only
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  exact Finset.prod_congr rfl fun PP _ => rfl

end Comparison₂

end GlobalTheory.ShareOn.WhitBase

namespace GlobalTheory.ShareOn

open GlobalTheory.ShareOn.WhitBase


end GlobalTheory.ShareOn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.ExpTie

def parOf {D : D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) : Par where
  k := D.R.k
  m := D.R.m
  t := D.R.t
  f := D.R.f
  n := D.R.n
  Nr := (Vc D j).rank
  L := L.sc.L
  x := L.sc.x
  b' := L.sc.b'
  η := L.etaSz
  S := L.Sc

end GlobalTheory.ExpTie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SympInv
open Matrix
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_eq_trace (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB x y = trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ i : α, ∑ k : α, ∑ l : β, x i j * JA i k * JB j l * c (y k l) =
      ∑ l : β, ∑ k : α, x i j * JA i k * c (y k l) * JB j l := fun i => by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Finset.sum_comm

theorem hTens_act (JA : Matrix α α E) (JB : Matrix β β E) (G : Matrix α α E) (H : Matrix β β E)
    (hG : Gᵀ * JA * G.map c = JA) (hH : Hᵀ * JB * H.map c = JB) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB (G * x * Hᵀ) (G * y * Hᵀ) = GlobalTheory.WeilM.hTens c JA JB x y := by
  rw [hTens_eq_trace, hTens_eq_trace]
  have e1 : (G * y * Hᵀ).map c = G.map c * y.map c * (H.map c)ᵀ := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum, map_mul]
  have e2 : (H.map c)ᵀ * JBᵀ * H = JBᵀ := by
    conv_rhs => rw [← hH]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [show H * (xᵀ * Gᵀ) * JA * (G.map c * y.map c * (H.map c)ᵀ) * JBᵀ =
      H * (xᵀ * (Gᵀ * JA * G.map c) * y.map c * ((H.map c)ᵀ * JBᵀ)) by simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, hG, Matrix.mul_assoc _ _ H, e2]

end GlobalTheory.SympInv

namespace GlobalTheory.SympInv

theorem symp_act : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (g : UA σ X.J) (h : UA σ W.J) (x u : Matrix (Fin n) (Fin d) (AE F E)),
    symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u := by
  intro F E _ _ _ _ _ σ n d X W g h x u
  have hg : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
  have hh : (mat h)ᵀ * incM F W.J * (mat h).map (cA σ) = incM F W.J := h.2
  unfold GlobalTheory.WeilM.symp
  rw [hTens_act (cA σ) (incM F X.J) (incM F W.J) (mat g) (mat h) hg hh x u]

end GlobalTheory.SympInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariantStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_unitary_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (g : UA σ X.J) (h : UA σ W.J) (x u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
      symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) x u := by
  first | exact @GlobalTheory.SympInv.symp_act | exact GlobalTheory.SympInv.symp_act | (intros; apply GlobalTheory.SympInv.symp_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamily
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadNumOnto

open GlobalTheory.BadShare

theorem tieAdmG_of_record (D : Formalism.BasicNotions.D7) : TieAdmG D :=
  fun k => ⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩

theorem wg_le_badBound (g m N q : ℝ) (n : ℕ) (r : ℝ) (hg : 2 ≤ g) (hm : 0 ≤ m) (hr : 100 ≤ r) (hrN : r ≤ N) :
    3 * (n : ℝ) / g + 23 * (n : ℝ) * Real.log g / Real.sqrt g +
        2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log r) / (g - 1)) + r / 2 * (7 / 8 : ℝ) ^ n +
        Real.exp (-(n : ℝ) / (5 * Real.log r)) ≤ badBound g n m N q := by
  unfold badBound
  have hf : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr0 : 0 < r := by linarith
  have hlr : 0 < Real.log r := Real.log_pos (by linarith)
  have hlN : Real.log r ≤ Real.log N := Real.log_le_log hr0 hrN
  have hg1 : 0 < g - 1 := by linarith
  have t3 : 2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log r) / (g - 1)) ≤
      2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) := by
    have : (1 + Real.log r) / (g - 1) ≤ (1 + Real.log N) / (g - 1) :=
      div_le_div_of_nonneg_right (by linarith) hg1.le
    have h0 : 0 ≤ 2 * (n : ℝ) * m := by positivity
    nlinarith
  have t4 : r / 2 * (7 / 8 : ℝ) ^ n ≤ N / 2 * (7 / 8 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]
    have : 0 ≤ (7 / 8 : ℝ) ^ n := by positivity
    nlinarith
  have t5 : Real.exp (-(n : ℝ) / (5 * Real.log r)) ≤ Real.exp (-((n : ℝ) / (10 * Real.log N))) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hf (by positivity) (by linarith)
  linarith

end GlobalTheory.BadNumOnto

namespace GlobalTheory.BadNumOnto

open GlobalTheory.BadShare

theorem badShare_numbers_onto : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ), Fm.x1 < x → x0 ≤ x → ∀ (ι : Fm.Ix x), 100 ≤ (Fm.D x ι).R.r ∧ TieAdmG (Fm.D x ι) ∧ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) ≤ 1 / 4 ∧ ∀ k : Fin 2, 2 ^ 12 ≤ (Fm.D x ι).host.g k ∧ 4 * (3 * ((Fm.D x ι).R.f : ℝ) / ((Fm.D x ι).host.g k : ℝ) + 23 * ((Fm.D x ι).R.f : ℝ) * Real.log ((Fm.D x ι).host.g k : ℝ) / Real.sqrt ((Fm.D x ι).host.g k : ℝ) + 2 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.m : ℝ) * (1 / (4 * ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ)) + (1 + Real.log ((Fm.D x ι).R.r : ℝ)) / (((Fm.D x ι).host.g k : ℝ) - 1)) + ((Fm.D x ι).R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ (Fm.D x ι).R.f + Real.exp (-((Fm.D x ι).R.f : ℝ) / (5 * Real.log ((Fm.D x ι).R.r : ℝ)))) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  refine ⟨1, one_pos, fun eps he he1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  obtain ⟨xs, hs⟩ := GlobalTheory.family_eventually_size_bounds eps Fm 5 (by norm_num)
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  have hezle : Fm.ez ≤ eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.ez_le
    rwa [Fm.L_ez 0 i, Fm.L_eps 0 i] at this
  obtain ⟨xb, hb⟩ := badBound_numbers Fm.ez 5 hez (hezle.trans he1)
  have he7 : 0 < Fm.ez / 7 := by positivity
  obtain ⟨xe, hxe⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop he7).eventually_ge_atTop (4 : ℝ)).and
      (((tendsto_rpow_atTop he).eventually_ge_atTop (512 : ℝ)).and (Filter.eventually_ge_atTop (1 : ℝ))))
  refine ⟨max (max xs xb) xe, fun x hx1 hx ι => ?_⟩
  have hxs : xs ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxb : xb ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  obtain ⟨h7, h512, hx1'⟩ := hxe x ((le_max_right _ _).trans hx)
  rw [Fm.L_x x ι hx1, Fm.L_ez x ι]
  have hE : Real.exp (-(x ^ (Fm.ez / 7))) ≤ 1 / 4 := by
    have h1 : (4 : ℝ) ≤ Real.exp (x ^ (Fm.ez / 7)) := by
      have := Real.add_one_le_exp (x ^ (Fm.ez / 7)); linarith
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h1
  have hr100 : 100 ≤ (Fm.D x ι).R.r := (hs x hxs ι 0).2.2.2.2.1
  refine ⟨hr100, tieAdmG_of_record _, hE, fun k => ?_⟩
  obtain ⟨hg, hf2, hf5, hm5, -, hr5, hq⟩ := hs x hxs ι k
  have hg12 : (2 : ℝ) ^ 12 ≤ ((Fm.D x ι).host.g k : ℝ) := by
    refine le_trans ?_ hg
    have := Real.add_one_le_exp (8 * x ^ eps)
    norm_num
    linarith
  refine ⟨by exact_mod_cast hg12, ?_⟩
  have hr100' : (100 : ℝ) ≤ ((Fm.D x ι).R.r : ℝ) := by exact_mod_cast hr100
  have hepsC : x ^ Fm.ez ≤ x ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hgz : Real.exp (8 * x ^ Fm.ez) ≤ ((Fm.D x ι).host.g k : ℝ) := by
    refine le_trans (Real.exp_le_exp.2 ?_) hg
    have := Real.rpow_le_rpow_of_exponent_le hx1' hezle
    linarith
  obtain ⟨-, hbb0, hbb⟩ := hb x hxb ((Fm.D x ι).host.g k) ((Fm.D x ι).R.f) ((Fm.D x ι).R.m)
    (max ((Fm.D x ι).R.r : ℝ) (x ^ Fm.ez)) ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ) hgz
    (by rw [Real.rpow_two]; exact hf2) hf5 (Nat.cast_nonneg _) hm5 (le_max_right _ _) (max_le hr5 hepsC) hq
  have hW := wg_le_badBound ((Fm.D x ι).host.g k) ((Fm.D x ι).R.m)
    (max ((Fm.D x ι).R.r : ℝ) (x ^ Fm.ez)) ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ) ((Fm.D x ι).R.f)
    ((Fm.D x ι).R.r) (by linarith) (Nat.cast_nonneg _) hr100' (le_max_left _ _)
  linarith

end GlobalTheory.BadNumOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamilyStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.badShareSize_bounds_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ), Fm.x1 < x → x0 ≤ x → ∀ (ι : Fm.Ix x), 100 ≤ (Fm.D x ι).R.r ∧ TieAdmG (Fm.D x ι) ∧ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) ≤ 1 / 4 ∧ ∀ k : Fin 2, 2 ^ 12 ≤ (Fm.D x ι).host.g k ∧ 4 * (3 * ((Fm.D x ι).R.f : ℝ) / ((Fm.D x ι).host.g k : ℝ) + 23 * ((Fm.D x ι).R.f : ℝ) * Real.log ((Fm.D x ι).host.g k : ℝ) / Real.sqrt ((Fm.D x ι).host.g k : ℝ) + 2 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.m : ℝ) * (1 / (4 * ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ)) + (1 + Real.log ((Fm.D x ι).R.r : ℝ)) / (((Fm.D x ι).host.g k : ℝ) - 1)) + ((Fm.D x ι).R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ (Fm.D x ι).R.f + Real.exp (-((Fm.D x ι).R.f : ℝ) / (5 * Real.log ((Fm.D x ι).R.r : ℝ)))) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  first | exact @GlobalTheory.BadNumOnto.badShare_numbers_onto | exact GlobalTheory.BadNumOnto.badShare_numbers_onto | (intros; apply GlobalTheory.BadNumOnto.badShare_numbers_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

def ArcZero (X : FlagCover Y) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ)
    (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)) : Prop :=
  ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι), W ≤ (L₀ X Z la).U i →
    ∀ (ψ : ℂ → (Γ(Y₀ X Z, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r →
      (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z =
        spMap σ) →
      (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) s ∈ bd₀ X Z) →
      (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 →
        ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ U₀ X Z) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ u in 𝓝[≠] (0 : ℂ),
        ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ U₀ X Z)
          (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ X Z la).U i),
          ‖H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) i hO hi m‖ < ε

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PageEstimateStatement
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn.PageNumbers

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem le_sup_fin (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (k : ℕ) (hk : k < D.R.m) :
    WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK (k + 1)) ≤
      Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1)) := by
  have h := Finset.le_sup (f := fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1)))
    (Finset.mem_univ (⟨k, hk⟩ : Fin D.R.m))
  exact h

theorem sup_fin_eq_topDeg (Tp : ParamsT D L Pm) (hK : DV.KapDef D) :
    (Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1))) = GlobalTheory.IndexAssembly.topDeg Tp hK := by
  apply le_antisymm
  · exact Finset.sup_le fun j _ => GlobalTheory.IndexAssembly.le_topDeg Tp hK ⟨by omega, by omega⟩
  · refine Finset.sup_le fun j hj => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact le_sup_fin Tp hK k (by omega)

end GlobalTheory.BigOn.PageNumbers

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.BigOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzAction
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.IntertwLocal.local_intertw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ (v : Pl (F := F)) (x : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (φ φ₁ φ₂ φ₃ φ₄ : (Fin n × Fin d → Fv F v) → ℂ), φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
    φ₂ ∈ SB (Fin n × Fin d → Fv F v) → Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → Acts (evFin F v) (om x) φ φ₂ →
    Acts (evFin F v) (om x) φ₁ φ₃ → Acts (evFin F v) (M.co.rho B.ψ (mat x.1 * u * (mat x.2)ᵀ)) φ₂ φ₄ → φ₄ = φ₃ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v x u φ φ₁ φ₂ φ₃ φ₄ hφ hφ₁ hφ₂ h1 h2 h3 h4
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  have hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := (hR φ hφ).2
  have himpl := hW.impl x u (tens (evFin F v) φ R) hΦ
  have hact : GlobalTheory.WeilM.actAB (cA σ) x u = mat x.1 * u * (mat x.2)ᵀ := rfl
  rw [hact] at himpl
  have key : tens (evFin F v) φ₄ R = tens (evFin F v) φ₃ R := by
    rw [← h4 R (hR φ₂ hφ₂), ← h2 R (hR φ hφ), ← himpl, h1 R (hR φ hφ), h3 R (hR φ₁ hφ₁)]
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro u' hu'; funext i; exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    simpa using (hR φ hφ).1 0 _ hz
  have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
  exact mul_right_cancel₀ hR0 this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzActionStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_local_schwartz_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ (v : Pl (F := F)) (x : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (φ φ₁ φ₂ φ₃ φ₄ : (Fin n × Fin d → Fv F v) → ℂ), φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
    φ₂ ∈ SB (Fin n × Fin d → Fv F v) → Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → Acts (evFin F v) (om x) φ φ₂ →
    Acts (evFin F v) (om x) φ₁ φ₃ → Acts (evFin F v) (M.co.rho B.ψ (mat x.1 * u * (mat x.2)ᵀ)) φ₂ φ₄ → φ₄ = φ₃ := by
  first | exact @GlobalTheory.IntertwLocal.local_intertw | exact GlobalTheory.IntertwLocal.local_intertw | (intros; apply GlobalTheory.IntertwLocal.local_intertw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section RunModelSec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def RunModel (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type} [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r) : Prop :=
  ∃ (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp),

    (∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) ∧

    (∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) ∧

    (∃ a : p.P.Gp → C → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp) (c : C)
      (x : Frame M.Ψ D.R.r), x ∈ M.dom →
      ∀ (h1 : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ)
        (h2 : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e (g • c))).Ψ),
        rdU ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀)
            (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (r.lev i g⁻¹) F.1)
            (e c) (castFrame h1 x) =
          (a g c : ℂ) * rdU ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀) F.1 (e (g • c))
            (castFrame h2 (lact (M.tr g c) x))) ∧

    (∀ c, ∀ γ ∈ (M.comp c).Γ, ∀ w ∈ (M.comp c).L',
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • (M.comp c).L') ∧

    ∃ φ : ∀ c, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
        ((M.comp c).L' ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (M.comp c).L'))),
      ∀ (c : C) (u : p.P.Gp), u • c = c → ∃ n : ℤ, ∀ w : (M.comp c).L',
        ∃ hw : Matrix.mulVec (M.tr u c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L',
          Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (M.comp c).L')) ⟨_, hw⟩ =
            φ c ((r.lev i u ^ n) ((φ c).symm (Submodule.Quotient.mk w)))

end RunModelSec

end GlobalTheory.ShareOn

end
end
