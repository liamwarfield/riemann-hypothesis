module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubgroupIsUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop

namespace GlobalTheory.LawsDeep

theorem goodAt_of_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l l₂ : Level H) (b : ℕ) (hM : l₂.M = l.M * b) (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) (p : ℕ) (hp : p.Prime) :
    l₂.GoodAt p := by
  rw [GlobalTheory.HostProbe.goodAt_iff l₂ hp]
  intro k hk
  have hdvd : l.M ∣ p ^ k := ⟨b, by rw [← hk]; exact hM⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact (GlobalTheory.HostProbe.goodAt_iff l hp).1 (hl p hp) i hi

theorem levLaws (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (hT : LawsJ T) (hj : InR D j)
    (hG : Y.Good e o) : GlobalTheory.LevGeo.Laws D j Y.d.Xo₂ Y.d.c₂ Y.U Y.dict := by
  refine
    { inR := hj
      host := hT.toLawsM.pins.1
      dat := hT.toLawsM.pins.2.2.2 j hj
      levA := hG.lev.2
      unf := hG.unf
      chiTriv := hG.chiTriv
      dictU := ?_
      modelW := hG.modelW }
  intro σ hσ
  obtain ⟨th, hr, hth, hd⟩ := hG.dictU σ hσ
  refine ⟨Y.Kf, th, hr, ?_, hth, hd, hG.unit σ hσ⟩
  have h₁ := hG.lev.1
  unfold DeltaDat.IsLev at h₁
  have h₂ := hT.toLawsM.pins.2.1
  unfold Par.PinLevel at h₂
  rw [h₁.2.1, h₂.1]
  exact hG.levelK

theorem laws_deep : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ),
    LawsJ T → InR D j → Y.Good e o → Laws Y.U (xiR D) := by
  intro D T j Y e o hT hj hG
  have hM : Y.d.l₂.M = T.Q.l.M * Y.d.pd := by
    have h₁ := hG.lev.1
    unfold DeltaDat.IsLev at h₁
    exact h₁.2.1
  have hgood : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := fun p hp =>
    goodAt_of_mul T.Q.l Y.d.l₂ Y.d.pd hM (GlobalTheory.RecDict.level_good_and_sign D T.Q hT.toLawsM.pins).1 p hp
  exact (GlobalTheory.T.moduliLaws_of_principalLevel_fieldOfDefinition D j T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ Y.U Y.dict
    (levLaws D T j Y e o hT hj hG) hG.geo hgood).1

end GlobalTheory.LawsDeep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCoverStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → Laws Y.U (xiR D) := by
  first | exact @GlobalTheory.LawsDeep.laws_deep | exact GlobalTheory.LawsDeep.laws_deep | (intros; apply GlobalTheory.LawsDeep.laws_deep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
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

abbrev smallInt (D : D7) : Subring ℂ := ((Formalism.L2.Host.embLL0 D).comp (algebraMap (𝓞 ↥D.LL0) ↥D.LL0)).range

theorem span_mono_subring {M : Type} [AddCommGroup M] [Module ℂ M] {O O' : Subring ℂ} (hO : O ≤ O') (S : Set M) {x : M}
    (hx : x ∈ Submodule.span O S) : x ∈ Submodule.span O' S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul a y _ h => exact Submodule.smul_mem _ (⟨a, hO a.2⟩ : O') h

theorem lat_mono {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X) (i : X.Tw) (j : Fin D.R.m)
    (b : Bool) {O O' : Subring ℂ} (hO : O ≤ O') (h : GA D (Vc D j)) {P : PolF D (Wc D j).rank (Vc D j).rank}
    (hP : P ∈ ρ.lat i j b O h) : P ∈ ρ.lat i j b O' h :=
  ⟨hP.1, span_mono_subring hO _ hP.2⟩

theorem smallInt_le {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X} (hρ : ρ.Good) (i : X.Tw)
    (b : Bool) : smallInt D ≤ (ρ.eO i b).range := by
  rintro _ ⟨a, rfl⟩
  exact (hρ.isCoefRing i b).int a

theorem exists_inv_of_root {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (u : FractionRing O) (n : ℕ) (hn : n ≠ 0)
    (hu : u ^ n = 1) : ∃ o : O, algebraMap O (FractionRing O) o = u⁻¹ := by
  have h1 : IsIntegral O (u⁻¹ ^ n) := by rw [inv_pow, hu, inv_one]; exact isIntegral_one
  exact IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) h1)

end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToRatHyp0
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie

namespace GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

structure RatHyp0 (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (F : Face D A3.A)
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (i : D.ntw.Tw) (j : Fin D.R.m) : Prop where
  size : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV
  host : HostHyp D
  std : VStd D j
  laws : LawsJ T
  core : GlobalTheory.Hk3.Core Rl.toRealDat F
  unif : Rl.toRealDat.LUnif
  fw : Nonempty (FWTie T Rl.toRealDat κ v₀)
  tieIn : TieIn T Rl.toRealDat κ v₀
  io : IoExt Rl.toRealDat
  guard : QGuard Rl.toRealDat
  fin : Finite T0
  pins : OMPins T Rl.toRealDat κ v₀ O j
  phase : PhaseTie T Rl.toRealDat κ v₀ O (fun j => cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)) j
  galois : IsGalois ℚ D.LL0
  small : SmallHas D Rl.C
  inUse : D.ntw.NonzeroIndexPlace i
  low : ∀ P : Pl D.host.E, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK *
    (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i

end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryInjAtPlace

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    compFin F E v (cA σ x) = sigR (Fv F v) σ (compFin F E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem compFin_inclR (v : Pl (F := F)) (x : E) :
    compFin F E v (inclR (F := F) (AF F) x) = inclR (Fv F v) x := by
  change evFin F v 1 ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] x
  rw [map_one]

theorem eq_tensAt_of_at (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hx : At (evFin F v) x) :
    x = tensAt E v (compFin F E v x) := by
  have h0 : evFin F v (1 - atPlace v 1) = 0 := by rw [map_sub, map_one, evFin_atPlace, sub_self]
  have h1 := hx _ h0
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  have h2 : tensAt E v 1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (atPlace v 1) := by
    rw [Algebra.TensorProduct.one_def, tensAt_tmul, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [← one_mul (compFin F E v x), ← tensAt_mul_right, h2, ← Algebra.smul_def]
  exact h1

theorem mat_eq_zero_of_at {n : ℕ} (v : Pl (F := F)) (z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hz : At (evFin F v) z)
    (h0 : z.map (compFin F E v) = 0) : z = 0 := by
  ext i j
  have hij : At (evFin F v) (z i j) := fun u hu => by
    have := congrFun (congrFun (hz u hu) i) j
    simpa using this
  rw [eq_tensAt_of_at v _ hij]
  have := congrFun (congrFun h0 i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at this
  rw [this, map_zero, Matrix.zero_apply]

theorem unitary_at_components {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : Pl (F := F))
    (t : E →ₐ[F] Fv F v) (h : UA σ J) :
    ((mat h).map (piW t))ᵀ * J.map t * (mat h).map (piW (t.comp σ)) = J.map t := by
  have hm : (mat h)ᵀ * incM F J * (mat h).map (cA σ) = incM F J := h.2
  have h1 := congrArg (fun M => (M.map (compFin F E v)).map (splitProj t)) hm
  simp only [Matrix.map_mul, Matrix.transpose_map] at h1
  have e1 : ((incM F J).map (compFin F E v)).map (splitProj t) = J.map t := by
    ext i j
    simp only [incM, Matrix.map_apply]
    rw [compFin_inclR, splitProj_inclR]
  have e2 : (((mat h).map (cA σ)).map (compFin F E v)).map (splitProj t) = (mat h).map (piW (t.comp σ)) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [compFin_cA, ← splitProj_comp]
    rfl
  have e3 : ((mat h)ᵀ.map (compFin F E v)).map (splitProj t) = ((mat h).map (piW t))ᵀ := by
    ext i j
    rfl
  rw [e1, e2] at h1
  rw [← e3]
  exact h1

theorem eq_of_piW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t h₁ hh₁ h₂ hh₂ heq
  have hcm := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  have u₁ := unitary_at_components v t h₁
  have u₂ := unitary_at_components v t h₂
  rw [heq] at u₁
  set A := ((mat h₂).map (piW t))ᵀ * G.W.J.map t with hA
  have hAu : IsUnit A.det := by
    have hd := congrArg Matrix.det u₂
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_left (hd ▸ hJ)
  have hQ : (mat h₁).map (piW (t.comp σ)) = (mat h₂).map (piW (t.comp σ)) := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₁).map (piW (t.comp σ))) hAu,
      ← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₂).map (piW (t.comp σ))) hAu, u₁, u₂]
  have hpi : ∀ (h : UA σ G.W.J) (τ : E →ₐ[F] Fv F v),
      (mat h).map (piW τ) = ((mat h).map (compFin F E v)).map (splitProj τ) := by
    intro h τ; rw [Matrix.map_map]; rfl
  have hY : (mat h₁).map (compFin F E v) = (mat h₂).map (compFin F E v) := by
    refine mat_split_ext hcm t ?_ ?_
    · rw [← hpi, ← hpi, heq]
    · rw [← hpi, ← hpi, hQ]
  have hz : At (evFin F v) (mat h₁ - mat h₂) := by
    intro u hu
    have e : mat h₁ - mat h₂ = (mat h₁ - 1) - (mat h₂ - 1) := by abel
    rw [e, smul_sub, hh₁ u hu, hh₂ u hu, sub_zero]
  have h0 : (mat h₁ - mat h₂).map (compFin F E v) = 0 := by
    rw [Matrix.map_sub _ (fun x y => map_sub _ x y), hY, sub_self]
  have hm := mat_eq_zero_of_at v _ hz h0
  exact Subtype.ext (Units.ext (sub_eq_zero.1 hm))

end GlobalTheory.UnitaryInjAtPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImageStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_determined_by_split_image : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  first | exact @GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq | exact GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq | (intros; apply GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValue
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SchurCharV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem two_ne_zero_Fv (v : Pl (F := F)) : (2 : Fv F v) ≠ 0 := by
  have h := (algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))
  rwa [map_ofNat, map_zero] at h

theorem eq_liftU_of_UAt {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {n : ℕ}
    (X : Spc F E n) (herm : ∀ i j, σ (X.J j i) = algebraMap F E 1 * X.J i j) (hJ : IsUnit (X.J.map t).det)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) :
    g = GlobalTheory.SplitUnitLift.liftU h t X.J 1 herm hJ (Matrix.GeneralLinearGroup.map (piW t) g.1) := by
  set g' := Matrix.GeneralLinearGroup.map (piW t) g.1 with hg'
  have hv : g'.val = (mat g).map (piW t) := rfl
  set L := GlobalTheory.SplitUnitLift.liftU h t X.J 1 herm hJ g' with hL
  have hU : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
  have tr : ∀ (A B C : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      (Aᵀ * B * C).map (piW t) = (A.map (piW t))ᵀ * B.map (piW t) * C.map (piW t) := fun A B C => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hJm : (incM F X.J).map (piW t) = X.J.map t := by
    unfold incM
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => GlobalTheory.SplitGLLift.piW_inclR t (X.J i j)
  have hcm : ((mat g).map (cA σ)).map (piW t) = (mat g).map (piW (t.comp σ)) := by
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => GlobalTheory.VacIso.piW_cA σ t _
  have hUt : ((mat g)ᵀ * incM F X.J * (mat g).map (cA σ)).map (piW t) = (incM F X.J).map (piW t) := by rw [hU]
  rw [tr, hJm, hcm, ← hv] at hUt
  set gs := (mat g).map (piW (t.comp σ)) with hgs
  have hσ : gs = (X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * X.J.map t := by
    have e : gs = ((X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ) * ((g'.val)ᵀ * X.J.map t * gs) := by
      rw [show ((X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ) * ((g'.val)ᵀ * X.J.map t * gs) =
          (X.J.map t)⁻¹ * (((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * (g'.val)ᵀ) * X.J.map t * gs by
            simp only [Matrix.mul_assoc],
        ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one,
        Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
    rw [e, hUt]
  have hgA : At (evFin F v) (mat g - 1) := hg
  have hLA : At (evFin F v) (mat L - 1) := GlobalTheory.SplitUnitLift.liftU_mem_UAt h t X 1 herm hJ g'
  have hLt : (mat L).map (piW t) = g'.val := GlobalTheory.SplitUnitLift.liftU_piW h t X.J 1 herm hJ g'
  have hLs : (mat L).map (piW (t.comp σ)) = (X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * X.J.map t :=
    GlobalTheory.SplitUnitLift.liftU_piW_comp h t X.J 1 herm hJ g'
  apply Subtype.ext
  apply Units.ext
  show mat g = mat L
  ext i j
  rw [← sub_eq_zero]
  have hz : mat g i j - mat L i j = (mat g - 1) i j - (mat L - 1) i j := by
    simp only [Matrix.sub_apply]; ring
  refine GlobalTheory.VacIso.eq_zero_of_at_split h t ?_ ?_ ?_
  · intro u hu
    have e1 := congrFun (congrFun (hgA u hu) i) j
    have e2 := congrFun (congrFun (hLA u hu) i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply] at e1 e2
    rw [hz, smul_sub, e1, e2, sub_zero]
  · have e1 := congrFun (congrFun hLt i) j
    have e2 := congrFun (congrFun hv i) j
    simp only [Matrix.map_apply] at e1 e2
    rw [map_sub, e1, ← e2, sub_self]
  · have e1 := congrFun (congrFun hLs i) j
    have e2 := congrFun (congrFun hσ i) j
    simp only [hgs, Matrix.map_apply] at e1 e2
    rw [map_sub, e1, e2, sub_self]

end GlobalTheory.SchurCharV


open GlobalTheory.SchurCharV in
theorem GlobalTheory.SchurCharV.exists_char_of_schur : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v _ t ι hι H
  have hcm : IsCMExt F E σ := hT.base.cm
  have herm : ∀ i j, σ (G.V.J j i) = algebraMap F E 1 * G.V.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV.herm i j
  have hJ : IsUnit (G.V.J.map t).det := by
    have w := Classical.arbitrary (InfinitePlace F)
    exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V.J t (B.emb w).1 1 one_ne_zero (G.V.θ w)
      (by rw [one_smul]; exact hT.geo.hV.cartan w)
  set L := GlobalTheory.SplitUnitLift.liftU hcm t G.V.J 1 herm hJ with hLdef
  have hLmem : ∀ x, L x ∈ UAt σ G.V (evFin F v) := fun x => GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V 1 herm hJ x
  have hLt : ∀ x, (mat (L x)).map (piW t) = x.val := fun x => GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V.J 1 herm hJ x
  have hEx := (GlobalTheory.T.theta_action_exists hP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1
  have h1mem : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.W.J) - 1) = 0
    rw [show mat (1 : UA σ G.W.J) = 1 from rfl, sub_self, smul_zero]
  have hpres : ∀ p : UA σ G.V.J × UA σ G.W.J, ∀ Φ ∈ schA F (Fin a × Fin (a + a')),
      om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun p Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).pres p Φ hΦ
  have hvac := hT.geo.hM.vac v
  set φv := G.M.vac v
  have hφv : φv ∈ SB (Fin a × Fin (a + a') → Fv F v) := hvac.1
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hιv : ι φv ≠ 0 := fun h0 => hvac.2.1 (hbij.injOn hφv (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  choose c hc using fun x : GL (Fin a) (Fv F v) => H (L x) (hLmem x)
  have hrel : ∀ x, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (L x, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c x * ι φ ((x⁻¹ : GL (Fin a) (Fv F v)).val * Y) := by
    intro x φ hφ φ₁ hφ₁ hA Y
    rw [hc x φ hφ φ₁ hφ₁ hA Y, hLt x, Matrix.coe_units_inv]
  have hmul : ∀ x y, c (x * y) = c x * c y := by
    intro x y
    obtain ⟨φ₂, ⟨hφ₂, hA₂⟩, -⟩ := hEx (L y) (hLmem y) 1 h1mem φv hφv
    obtain ⟨φ₃, ⟨hφ₃, hA₃⟩, -⟩ := hEx (L x) (hLmem x) 1 h1mem φ₂ hφ₂
    have hA : Acts (evFin F v) (om (L (x * y), 1)) φv φ₃ := by
      have e : ((L (x * y), 1) : UA σ G.V.J × UA σ G.W.J) = (L x, 1) * (L y, 1) := by
        rw [Prod.mk_mul_mk, map_mul, one_mul]
      rw [e, map_mul]
      exact GlobalTheory.InertAvgDual.acts_comp v _ _ (hpres _) hA₂ hA₃
    have e1 := hrel (x * y) φv hφv φ₃ hφ₃ hA ((x * y).val * Y₀)
    have e2 := hrel x φ₂ hφ₂ φ₃ hφ₃ hA₃ ((x * y).val * Y₀)
    have e3 := hrel y φv hφv φ₂ hφ₂ hA₂ (y.val * Y₀)
    have k1 : ((x * y)⁻¹ : GL (Fin a) (Fv F v)).val * ((x * y).val * Y₀) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have k2 : (x⁻¹ : GL (Fin a) (Fv F v)).val * ((x * y).val * Y₀) = y.val * Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel_left]
    have k3 : (y⁻¹ : GL (Fin a) (Fv F v)).val * (y.val * Y₀) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [k1] at e1
    rw [k2] at e2
    rw [k3] at e3
    rw [e2, e3] at e1
    exact mul_right_cancel₀ hY₀ (e1.symm.trans (mul_assoc _ _ _).symm)
  have hone : c 1 = 1 := by
    have hA : Acts (evFin F v) (om (L 1, 1)) φv φv := by
      rw [map_one, show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]
      exact GlobalTheory.InertAvgDual.acts_one v φv
    have e := hrel 1 φv hφv φv hφv hA Y₀
    rw [inv_one, Units.val_one, Matrix.one_mul] at e
    exact (mul_eq_right₀ hY₀).mp e.symm
  let cH : GL (Fin a) (Fv F v) →* ℂ := ⟨⟨c, hone⟩, hmul⟩
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (two_ne_zero_Fv v) cH.toHomUnits
  have hcχ : ∀ x, c x = (χ (Matrix.GeneralLinearGroup.det x) : ℂ) := fun x => by rw [← hχ x]; rfl
  let A : (Fv F v)ˣ →* ℂˣ :=
    { toFun := fun x => Units.mk0 (GlobalTheory.SplitFlip.apow x (((a + a' : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.apow_ne_zero _ _)
      map_one' := Units.ext (GlobalTheory.SplitFlip.apow_one _)
      map_mul' := fun x y => Units.ext (GlobalTheory.SplitFlip.apow_mul x y _) }
  refine ⟨(χ * A)⁻¹, ?_⟩
  intro g hg
  set g' := Matrix.GeneralLinearGroup.map (piW t) g.1 with hg'
  refine ⟨g', rfl, ?_⟩
  intro φ hφ φ₁ hφ₁ hA
  have hgL : g = L g' := eq_liftU_of_UAt hcm t G.V herm hJ g hg
  rw [hgL] at hA
  funext Y
  rw [hrel g' φ hφ φ₁ hφ₁ hA Y, hcχ g']
  have hpow : ∀ d : (Fv F v)ˣ, GlobalTheory.SplitFlip.apow d (((a + a' : ℕ) : ℂ) / 2) *
      GlobalTheory.SplitFlip.apow d (-((a + a' : ℕ) : ℂ) / 2) = 1 := fun d => by
    rw [← GlobalTheory.SplitFlip.apow_add, show ((a + a' : ℕ) : ℂ) / 2 + -((a + a' : ℕ) : ℂ) / 2 = 0 by ring,
      GlobalTheory.SplitFlip.apow_zero]
  simp only [GlobalTheory.SplitFlip.omA, MonoidHom.inv_apply, inv_inv, MonoidHom.mul_apply, Units.val_mul, map_one,
    MonoidHom.one_apply, Units.val_one, GlobalTheory.SplitFlip.apow_one, Matrix.mul_one, mul_one, Fintype.card_fin]
  have hAv : ∀ d, ((A d : ℂˣ) : ℂ) = GlobalTheory.SplitFlip.apow d (((a + a' : ℕ) : ℂ) / 2) := fun d => rfl
  rw [hAv]
  linear_combination (-(χ (GlobalTheory.SplitFlip.gdet g') : ℂ) * ι φ ((g'⁻¹ : GL (Fin a) (Fv F v)).val * Y)) * hpow (GlobalTheory.SplitFlip.gdet g')
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValueStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_weil_functional_spherical_value : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) := by
  first | exact @GlobalTheory.SchurCharV.exists_char_of_schur | exact GlobalTheory.SchurCharV.exists_char_of_schur | (intros; apply GlobalTheory.SchurCharV.exists_char_of_schur <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScal

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) : Type := UG (cA σ) (dbl (incM F J))

def UDAt {R : Type} [Zero R] (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (ev : AF F → R) : Set (UD σ J) :=
  {p | At ev (((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) - 1)}

def dsum {k : Type} [CommRing k] {d : ℕ} (c : GL (Fin d) k) : GL (Fin d ⊕ Fin d) k where
  val := Matrix.fromBlocks c.val 0 0 c.val
  inv := Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

def locMatD {σ : E →ₐ[F] E} {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (c : GL (Fin d) (Fv F v)) : UD σ J →* GL (Fin d ⊕ Fin d) (Fv F v) where
  toFun p := (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * dsum c
  map_one' := by simp
  map_mul' p q := by simp [mul_assoc]

abbrev DblCo (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) : Type :=
  Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d)

abbrev DblRep (σ : E →ₐ[F] E) {n d : ℕ} (W : Spc F E d) : Type :=
  UD σ W.J →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)

structure IsLinD {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (ψ : AddChar (AF F) ℂ) (dd : DblCo σ X W)
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (ιd : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ)) :
    Prop where
  bij : Set.BijOn ιd (SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) : Set _)
    (SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) : Set _)
  trans : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 →
    ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      Acts (evFin F v) (dd.rho ψ u) φ φ₁ →
      ∀ Y, ιd φ₁ Y = ιd φ (Y + (b⁻¹).val * u.map (piW t) * ((dsum c)⁻¹).valᵀ)
  mult : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → u.map (piW t) = 0 →
    ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      Acts (evFin F v) (dd.rho ψ u) φ φ₁ →
      ∀ x : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
        ιd φ₁ ((b⁻¹).val * x.map (piW t) * ((dsum c)⁻¹).valᵀ) =
          ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u) * ιd φ ((b⁻¹).val * x.map (piW t) * ((dsum c)⁻¹).valᵀ)

def LocOps {σ : E →ₐ[F] E} {n d : ℕ} {W : Spc F E d} (omd : DblRep σ (n := n) W) (v : Pl (F := F)) : Prop :=
  ∀ p ∈ UDAt σ W.J (evFin F v), ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
    ∃ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ φ₁

def IsShapeD {σ : E →ₐ[F] E} {n d : ℕ} {W : Spc F E d} (omd : DblRep σ (n := n) W) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (c : GL (Fin d) (Fv F v))
    (ιd : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ))
    (cd : UD σ W.J → ℂ) : Prop :=
  ∀ p ∈ UDAt σ W.J (evFin F v), ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
    ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ φ₁ →
      ιd φ₁ = cd p • fun Y => ιd φ (Y * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val)

theorem exists_diag_one {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (h : UA σ J) :
    ∃ gd : UD σ J, ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
      Matrix.fromBlocks (mat h) 0 0 1 := by
  let A : Matrix (Fin d) (Fin d) (AE F E) := mat h
  let Ai : Matrix (Fin d) (Fin d) (AE F E) := (((h : GL (Fin d) (AE F E))⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _)
  have h1 : A * Ai = 1 := (h : GL (Fin d) (AE F E)).mul_inv
  have h2 : Ai * A = 1 := (h : GL (Fin d) (AE F E)).inv_mul
  let G : GL (Fin d ⊕ Fin d) (AE F E) :=
    ⟨Matrix.fromBlocks A 0 0 1, Matrix.fromBlocks Ai 0 0 1, by simp [fromBlocks_multiply, h1],
      by simp [fromBlocks_multiply, h2]⟩
  have hu : Aᵀ * incM F J * A.map (cA σ) = incM F J := h.2
  refine ⟨⟨G, ?_⟩, rfl⟩
  show (Matrix.fromBlocks A 0 0 1)ᵀ * dbl (incM F J) * (Matrix.fromBlocks A 0 0 1).map (cA σ) = dbl (incM F J)
  rw [fromBlocks_transpose, fromBlocks_map, dbl, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_zero, transpose_one, Matrix.map_zero _ (map_zero (cA σ)), Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, hu]

theorem gdet_locMatD_diag {σ : E →ₐ[F] E} {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (c : GL (Fin d) (Fv F v)) (h : UA σ J) (gd : UD σ J)
    (hgd : ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
      Matrix.fromBlocks (mat h) 0 0 1) :
    GlobalTheory.SplitFlip.gdet (locMatD t c gd) = GlobalTheory.SplitFlip.gdet (locMat t c h) := by
  apply Units.ext
  have e : (locMatD t c gd).val =
      Matrix.fromBlocks (locMat t c h).val 0 0 1 := by
    show ((dsum c)⁻¹).val * (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _).map (piW t)) * (dsum c).val = _
    rw [hgd, locMat_val, fromBlocks_map]
    simp only [dsum, Units.inv_mk, fromBlocks_multiply, Matrix.map_zero _ (map_zero (piW t)),
      Matrix.map_one _ (map_zero (piW t)) (map_one (piW t)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    simp [Units.mul_inv]
  simp only [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, e, det_fromBlocks_zero₂₁, det_one, mul_one]

def fixDiag {k : Type} [CommRing k] {d : ℕ} (A : GL (Fin d) k) : GL (Fin d ⊕ Fin d) k where
  val := Matrix.fromBlocks A.val (1 - A.val) 0 1
  inv := Matrix.fromBlocks (A⁻¹).val (1 - (A⁻¹).val) 0 1
  val_inv := by simp [fromBlocks_multiply, Matrix.mul_sub]
  inv_val := by simp [fromBlocks_multiply, Matrix.mul_sub]

theorem fixDiag_diag {k : Type} [CommRing k] {d : ℕ} (A : GL (Fin d) k) :
    ((fixDiag A).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) k) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) k) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) k) * (1 : Matrix (Fin d) (Fin d) k) := by
  simp only [fixDiag, diagCols, Matrix.mul_one]
  rw [← fromCols_fromRows_eq_fromBlocks, fromCols_mul_fromRows, fromRows_mul, fromRows_mul]
  ext (i | i) j <;> simp

theorem gdet_fixDiag {k : Type} [Field k] {d : ℕ} (A : GL (Fin d) k) :
    GlobalTheory.SplitFlip.gdet (fixDiag A) = GlobalTheory.SplitFlip.gdet A := by
  apply Units.ext
  simp [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, fixDiag, det_fromBlocks_zero₂₁]

theorem fromBlocks_sub_one {R : Type} [CommRing R] {d : ℕ} (A : Matrix (Fin d) (Fin d) R) :
    Matrix.fromBlocks A (0 : Matrix (Fin d) (Fin d) R) 0 (1 : Matrix (Fin d) (Fin d) R) - 1 =
      Matrix.fromBlocks (A - 1) (0 : Matrix (Fin d) (Fin d) R) 0 0 := by
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

end GlobalTheory.DblScal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtin
set_option autoImplicit false

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie

namespace GlobalTheory.TwistChr

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem hecke_eq_of_frob {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (r : Formalism.ConjugateSelfDual.G E Ω →* ℂˣ) (hr : IsOpen (r.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) (χ : HChar E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hu : ∀ v ∉ S, χ.UnrAt v)
    (hf : ∀ v ∉ S, ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G E Ω, IsFrob (F := E) A (normV v) σ → r σ = (χ.val v)⁻¹)
    (x : Ideles E) (σ : Formalism.ConjugateSelfDual.G E Ω) (hx : art x = toAb E Ω σ) : χ.1 x = r σ := by
  have hc := continuous_of_isOpen_ker' r hr
  have h : (liftAb r hc).comp art * χ.1⁻¹ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away _ (((continuous_liftAb r hc).comp ha.quot.continuous).mul χ.2.1.inv) (fun k => ?_) S
      fun v hv => ?_
    · have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, χ.2.2, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one, inv_one, one_mul]
    · refine GlobalTheory.FrobDense.eq_one_of_unif (((liftAb r hc).comp art * χ.1⁻¹).comp (localIdele E v)) fun y hy => ?_
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      obtain ⟨τ, hτ, e⟩ := (ha.frob v A hA _).mp ⟨y, hy, rfl⟩
      have h1 : χ.1 (localIdele E v y) = χ.val v := χ.val_eq (hu v hv) y hy
      rw [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, ← e, liftAb_toAb, map_inv,
        hf v hv A hA τ hτ, inv_inv, h1, mul_inv_cancel]
  have h2 := DFunLike.congr_fun h x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hx, liftAb_toAb, MonoidHom.one_apply, mul_inv_eq_one] at h2
  exact h2.symm

theorem chrEq_charOf {D : D7} {Ω : Type} [Field Ω] [Algebra D.host.E Ω] [IsAlgClosure D.host.E Ω] {a : Recip D Ω} (ha : a.Good)
    {R : Type} [CommRing R] (f : R →+* ℂ) (ψ : Formalism.ConjugateSelfDual.G D.host.E Ω →* Rˣ) (hψ : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E Ω))) {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ σ, ψ σ ^ n = 1) (χ : HChar D.host.E) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hu : ∀ v ∉ S, χ.UnrAt v)
    (hf : ∀ v ∉ S, ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E Ω, IsFrob (F := D.host.E) A (normV v) σ →
      f (ψ σ : Rˣ) = (((χ.val v)⁻¹ : ℂˣ) : ℂ)) : ChrEq (charOf a f ψ) χ := by
  have key : ∀ x, ((charOf a f ψ x : Circle) : ℂ) = ((χ.1 (Units.map a.κ.toMonoidHom x) : ℂˣ) : ℂ) := fun x => by
    obtain ⟨σ, hσ⟩ := a.exists_sym x
    rw [charOf_eq a f hψ hσ hn (hp σ), hecke_eq_of_frob ha.artin ((Units.map f.toMonoidHom).comp ψ)
      (Subgroup.isOpen_mono (H₁ := ψ.ker) (fun g hg => by
        rw [MonoidHom.mem_ker] at hg ⊢
        rw [MonoidHom.comp_apply, hg, map_one]) hψ) χ S hu (fun v hv A hA τ hτ => Units.ext (hf v hv A hA τ hτ)) _ σ hσ]
    rfl
  refine ⟨⟨?_, fun k => ?_⟩, fun P e he k x hx => ?_⟩
  · refine continuous_induced_rng.2 ?_
    exact (Units.continuous_val.comp (χ.2.1.comp (Continuous.units_map _ ha.cont))).congr fun x => (key x).symm
  · refine Circle.ext ?_
    rw [key, show Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k from Units.ext (ha.rat k), χ.2.2]
    rfl
  · rw [key, show Units.map a.κ.toMonoidHom x = localIdele D.host.E P (atFin P k) from Units.ext (by
      change a.κ (x : AE D) = _
      rw [hx, ha.loc P e he k])]
    rfl

theorem chrEq_mul {D : D7} {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx]
    rfl

theorem finite_placesOver (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l ≠ 0) : (Formalism.BasicNotions.placesOver E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}

theorem chrEq_tw (h : RecTies p) (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (hψ : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hA : Adapted p w ρ) :
    ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w) := by
  classical
  obtain ⟨-, -, hopen, -, hzk, -, -⟩ := hψ
  obtain ⟨-, e, he, he'⟩ := hA
  have hl : D.ntw.l (ex.nch.twI w) ≠ 0 := (D.ntw.lPrime _).out.ne_zero
  have hz : D.ntw.zk (ex.nch.twI w) (ex.nch.k' w) ^ (D.ntw.l (ex.nch.twI w) ^ ex.nch.k' w) = 1 :=
    Units.ext (by simpa using (D.ntw.zk_prim (ex.nch.twI w) (ex.nch.k' w)).pow_eq_one)
  have hfin := finite_placesOver D.host.E (l := D.what₂.places.resChar w) (ex.nch.twI_l w ▸ hl)
  refine chrEq_charOf hρ.rc _ _ hopen (pow_ne_zero (ex.nch.k' w) hl) (fun σ => ?_) _ (ex.nch.Q w ∪ hfin.toFinset)
    (fun v hv => ((p.Tp.psi_is w hw).ram v).2 fun hQ => hv (Finset.mem_union_left _ hQ)) fun v hv A hA σ hσ => ?_
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · obtain ⟨y, hy, hy'⟩ := h.psi_read w hw v (fun hQ => hv (Finset.mem_union_left _ hQ))
      (fun hQ => hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hQ))) A σ hA hσ
    rw [← he', ← hy', he, hy]

theorem xi_eq (hw : D.what₂.muAt w ≠ D.what₂.mu0) {ρ : Setup D.ntw} (hP : RealPin p.R p.cG ρ) (j : Fin D.R.m) (b : Bool)
    {c : (AE D)ˣ →* Circle} (hc : ChrEq c (p.Tp.psi w)) :
    p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j b).de.chi * c := by
  have h1 := p.charW.base.lev.xi (p.R.mu (D.plEq w))
  have h2 : p.R.toRealDat.toLevCh.xiH (p.R.mu (D.plEq w)) = p.R.C.delAt (D.ntw.l (ex.nch.twI w)) * p.Tp.psi w := by
    rw [← p.tupAt w, p.tupXi _ (Or.inr ⟨w, rfl⟩), (D.what₂.muAt_or w).resolve_left hw, p.Tp.xi_tw, ex.nch.twI_l]
  exact GlobalTheory.ChrEqUnique.idc_unique D _ _ _ h1 (h2 ▸ chrEq_mul (hP.delta _ j b) hc)

end Point

end GlobalTheory.TwistChr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine AlgebraicGeometry GlobalTheory.CompHt GlobalTheory.FlatCore

theorem framesOn_eq_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∃ k, framesOn (U σ) Z = {z | z.1 = k ∧ z.2 ∈ ((U σ).X z.1).dom} := by
  intro E _ _ _ H Dw l Xo c r U x hL Z σ hσ
  obtain ⟨q, hq⟩ : ∃ q : (U σ).Comp ≃ Comp Xo c, ∀ k (y : ((U σ).X k).dom) (s : Sp (CAt σ)),
      ptF ((U σ).un k y) s ∈ (q k).1 :=
    GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj (U σ)) hσ (hL.unf σ hσ)
      (fun k => GlobalTheory.CompBij.frames_nonempty _) hL.geo
  refine ⟨q.symm Z, Set.ext fun ⟨k, y⟩ => ⟨?_, ?_⟩⟩
  · rintro ⟨hy, hl⟩
    refine ⟨?_, hy⟩
    have hk : q k = Z := by
      by_contra hne
      let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) (hq k ⟨y, hy⟩ s) (hl s)
    exact (Equiv.eq_symm_apply q).2 hk
  · rintro ⟨hk, hy⟩
    obtain rfl : k = q.symm Z := hk
    refine ⟨hy, fun s => ?_⟩
    have := hq (q.symm Z) ⟨y, hy⟩ s
    rwa [Equiv.apply_symm_apply] at this

end GlobalTheory.FlatCore

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRowFiresOfWeakCharacterisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFiringRowAtConcreteLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFiringRowAtConcreteLifts
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFireAssembly

theorem thetaFireRow_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → R.ExAt → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ IL : RecTie.LiftIds (RecTie.toLiftReal R F tupT hm hTop hinj), RecTie.ThetaFireRow (RecTie.toLiftReal R F tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj h e hv IL
  have hP : R.IsThP := RealDat.thP_of_weak h.thP e
  refine ⟨fun μ _ i => GlobalTheory.ThetaPRead.isThetaP_toLiftReal R F tupT hm hTop hinj hP.thF μ i, ?_, ?_⟩
  · exact GlobalTheory.T.thetaAdjoint_at_lift_eq_lowestKType_restriction R F tupT hm hTop hinj h.lev h.grp h.models hP hv IL
  · exact GlobalTheory.LiftResInj.resInjL_toLiftReal R F tupT hm hTop hinj h.models.inf

end GlobalTheory.ThetaFireAssembly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFiringRowAtConcreteLiftsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFiringRow_at_concreteLifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → R.ExAt → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ IL : RecTie.LiftIds (RecTie.toLiftReal R F tupT hm hTop hinj), RecTie.ThetaFireRow (RecTie.toLiftReal R F tupT hm hTop hinj) IL := by
  first | exact @GlobalTheory.ThetaFireAssembly.thetaFireRow_toLiftReal | exact GlobalTheory.ThetaFireAssembly.thetaFireRow_toLiftReal | (intros; apply GlobalTheory.ThetaFireAssembly.thetaFireRow_toLiftReal <;> assumption)
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaLiftRow_fires_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → A3.A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R.toRealDat) (hinj : ∀ i t, Function.Injective (R.toRealDat.extV i t)) (IL : RecTie.LiftIds (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj)), RecTie.ThetaFireRow (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC e hv tupT hm hTop hinj IL
  exact GlobalTheory.T.thetaFiringRow_at_concreteLifts R.toRealDat F.lv2 tupT hm hTop hinj hC.base e hv IL

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtComp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.TwAdmProof

theorem not_mem_sq_of_eWL {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hv : (p : 𝓞 E) ∈ w.asIdeal) (he : eWL E w = 1) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨P, hP, hP0⟩ := w
  have he' : P.ramificationIdx ℤ = 1 := he
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he'
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he'
  rw [hmap, Ideal.span_le]
  simpa using h2

end GlobalTheory.BigOn.Exp.TwAdmProof

namespace GlobalTheory.BigOn.Exp.TwAdmProof

variable {D : D7}

theorem not_mem_of_dvd (P : PlE D.host) (he : eWL D.host.E P = 1) {p : ℕ} (hp : p.Prime)
    (h : p ∣ D.host.QS * D.host.q * D.host.d) : (p : 𝓞 D.host.E) ∉ P.asIdeal := fun hv =>
  not_mem_sq_of_eWL hp P hv he (UpperTheory.Ram.mem_sq_of_dvd_condN D.host hp h _ P.isPrime hv)

theorem two_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he Nat.prime_two ((((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd).mul_right _).mul_right _)

theorem d_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((D.host.d : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he D.host.hyp.2.1 (dvd_mul_left _ _)

theorem q_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he D.host.hyp.1 ((dvd_mul_left _ _).mul_right _)

end GlobalTheory.BigOn.Exp.TwAdmProof

namespace GlobalTheory.BigOn.Exp.TwAdmProof

variable {D : D7}

theorem exists_splitK_of (P : PlE D.host) (h1 : P.asIdeal.inertiaDeg ℤ = 1) (he : eWL D.host.E P = 1) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal) := by
  have hp := GlobalTheory.TwistDet.prime_normV h1
  have hmem : ((Formalism.ConjugateSelfDual.normV P : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h2 : Ideal.absNorm P.asIdeal = Formalism.ConjugateSelfDual.normV P := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    exact h2 ▸ Ideal.absNorm_mem P.asIdeal
  have hodd : Odd (Formalism.ConjugateSelfDual.normV P) := by
    refine hp.eq_two_or_odd'.resolve_left fun e => two_not_mem P he ?_
    rw [e] at hmem; exact hmem
  refine GlobalTheory.TwistDet.exists_splitK h1 he hodd (fun h => q_not_mem P he h) (fun h => d_not_mem P he h)

theorem psiAt_comp {Γ Γ' A : Type} [Group Γ] [Group Γ'] [CommGroup A] (b : Bool) (ψ : Γ →* A) (f : Γ' →* Γ) :
    (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b ψ).comp f = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ.comp f) := by
  cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.inv_comp]

end GlobalTheory.BigOn.Exp.TwAdmProof
end
