module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledEigenfunctionsLineVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenInertPlaceLatticeStabiliser
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenInertPlaceLatticeStabiliser
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VDblEig

theorem boxFun_mem_SB' {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem star_mem_SB' {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => star (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (star_zero _)⟩

theorem vdbl_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr g hg
  obtain ⟨hvSB, -, θ, hθ, hvac⟩ := hT.geo.hM.vac v
  set φ := G.M.vac v with hφ
  set vD := boxFun φ (fun x => star (φ x)) with hvD
  set RD := boxFun r (fun x => star (r x)) with hRD
  have hvDSB : vD ∈ SB _ := boxFun_mem_SB' hvSB (star_mem_SB' hvSB)
  have hS : boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x)) = tens (evFin F v) vD RD := by
    funext x
    simp only [tens, boxFun, hvD, hRD, Function.comp_def, star_mul']
    ring
  have hRest : Rest (evFin F v) vD RD := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      show r ((x + z) ∘ Sum.inl) * star (r ((x + z) ∘ Sum.inr)) = r (x ∘ Sum.inl) * star (r (x ∘ Sum.inr))
      rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
        show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hr.1 _ _ hz1, hr.1 _ _ hz2]
    · rw [← hS]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hr.2 _ (GlobalTheory.ConjSch.star_mem_schA _ _ hr.2)

  have hU := hsp.2.1
  obtain ⟨φ₁, hφ₁, hA⟩ : ∃ φ₁ ∈ SB _, Acts (evFin F v) (omd g) vD φ₁ := by
    refine GlobalTheory.DblActs.acts_of_comm v B.ψ hT.base.std (omd g) (fun Φ hΦ => hU.pres g Φ hΦ)
      (fun μ hμ Φ hΦ => hU.unit μ hμ g Φ hΦ) ?_ vD hvDSB
    intro u hu x y Φ hΦ
    set z := dd.e.symm (x, y) with hz
    have he : dd.e (u • z) = (u • x, u • y) := by
      rw [LinearEquiv.map_smul, hz, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h2 := hg.1 u hu
    have e2 : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g (u • z) = u • z := by
      simp only [actB]
      set P := GlobalTheory.DblVac.matD g with hP
      set c : AE F E := algebraMap (AF F) (AE F E) u with hc
      have hs1 : u • z = c • z := (algebraMap_smul (AE F E) u z).symm
      have hs2 : u • (P - 1) = c • (P - 1) := (algebraMap_smul (AE F E) u (P - 1)).symm
      have h2' : c • (P - 1) = 0 := hs2 ▸ h2
      have : (c • z) * Pᵀ - c • z = z * (c • (P - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2'] at this
      simp only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      rw [hs1]
      exact this
    have h3 := hU.impl g (u • z) Φ hΦ
    simp only [Darboux.rho] at h3
    set_option backward.isDefEq.respectTransparency false in
      rw [e2, he] at h3
    exact h3
  have hE0 := GlobalTheory.T.doubledVacuum_heisenbergEigen_doubledLattice F E σ B a a' G X om om' hT v w hw hv d' hd' dd hdc θ hθ hvac
  have hE1 := GlobalTheory.T.doubledStabilizer_weilOperator_transports_latticeEigen F E σ B a a' G X om om' hT v w hw hv d' hd' dd hdc θ hθ hvac omd hsp g hg vD hvDSB φ₁ hφ₁ hE0 hA
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.inertPlace_doubledEigenfunctions_line_vacuum F E σ B a a' G X om om' hT v w hw hv d' hd' dd hdc θ hθ hvac φ₁ hφ₁ hE1
  refine ⟨μ, ?_⟩
  rw [hS, hA RD hRest, hμ]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.VDblEig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenInertPlaceLatticeStabiliserStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  first | exact @GlobalTheory.VDblEig.vdbl_eigen | exact GlobalTheory.VDblEig.vdbl_eigen | (intros; apply GlobalTheory.VDblEig.vdbl_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPointDimOne
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.TorusTateLie
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointMap

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}
  (α : P.A.A ⟶ P'.A.A) [IsMonHom α]

section Lattices

variable [Algebra ℤ_[p] C]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

end Lattices

variable [IsAlgClosed C] [CharZero C]

theorem pairV_mapV [Algebra ℤ_[p] C] (x : P.V) (y : P'.V) :
    P'.pairV (mapV P P' α x) y = P.pairV x (adjV P P' α y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, hx, hx']
  | tmul c s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
    | tmul d t => exact congrArg (· • (c * d)) (pairT_mapT P P' α s t)

theorem weil_adjT (he : P'.eps = P.eps) (t : P'.T) {n : ℕ} {z : ChTor.Pts P.A.A} (hz : z ^ p ^ n = 1) :
    weil P'.A (p ^ n) (z ≫ α) (t.lev n) = weil P.A (p ^ n) z ((adjT P P' α t).lev n) := by
  obtain ⟨s, rfl⟩ := (tate_free_of_card p _ _ P.card_torsion).2.1 n z hz
  rw [← pow_pairT P.A P.eps, ← pairT_mapT, ← he, pow_pairT, lev_mapT]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  (β : P.Gt ⟶ P'.Gt) [IsMonHom β] (he : P'.eps = P.eps) (hβ : ∀ x, P'.toA (x ≫ β) = P.toA x ≫ α)

include he hβ

theorem weilChar_adjT (t : P'.T) (n : ℕ) : (P.weilChar (adjT P P' α t)).χ n =
    ExtensionTorsion.torsionHom β (p ^ n) ≫ (P'.weilChar t).χ n := P.char_ext fun w => by
  rw [← Category.assoc, P.isWeilChar_weilChar, P'.isWeilChar_weilChar, Category.assoc,
    ExtensionTorsion.torsionHom_ι, ← Category.assoc, hβ, weil_adjT α he t (P.toA_pow w)]

variable [Algebra ℤ_[p] O]

theorem al₀_adjT (t : P'.T) (x : LieG P.Gt) :
    (P.al₀ (adjT P P' α t)).1 x = (P'.al₀ t).1 (lieMap β x) := by
  refine HodgeTateImage.eq_of_forall (p := p) fun n => ?_
  have hR := HodgeTateImage.pow_quot (O := O) (p := p) n
  have h1 := isAl_dlogTv (P.weilChar (adjT P P' α t)) n _ hR x _ (HodgeTateImage.lift_ι hR x)
  have h2 := isAl_dlogTv (P'.weilChar t) n _ hR (lieMap β x)
    (HodgeTateImage.lift hR x ≫ ExtensionTorsion.torsionHom β (p ^ n)) (by
      rw [Category.assoc, ExtensionTorsion.torsionHom_ι, ← Category.assoc, HodgeTateImage.lift_ι]
      exact Category.assoc _ _ _)
  rw [Category.assoc, ← weilChar_adjT α β he hβ, h1] at h2
  change algebraMap O _ ((dlogTv (P.weilChar (adjT P P' α t))).1 x) =
    algebraMap O _ ((dlogTv (P'.weilChar t)).1 (lieMap β x))
  simpa [Algebra.algebraMap_eq_smul_one] using congrArg TrivSqZeroExt.snd h2

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

theorem mapV_bLie (x : LieG P.Gt) : mapV P P' α (P.bLie x) = P'.bLie (lieMap β x) :=
  P'.eq_of_pairV fun t => by
    rw [pairV_mapV, adjV_tmul, Point.pairV_bLie, Point.pairV_bLie, al₀_adjT α β he hβ]

end General

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ] {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type}
  [CommRing R] (j : R →+* O) {B B' B'' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ) (o'' : B''.OAct Λ)

theorem homT_act (a : Λ) [IsMonHom (o.act a)] : homT hv ε j o o (o.act a) = (goodPoint hv ε j B o).actT a :=
  LinearMap.ext fun t => Tate.ext fun n => congrArg (t.lev n ≫ ·) (goodPoint_oA hv ε j o a).symm

theorem homT_id : homT hv ε j o o (𝟙 B.A) = LinearMap.id :=
  LinearMap.ext fun t => Tate.ext fun n =>
    (congrArg (t.lev n ≫ ·) ((congrArg _ ((Over.pullback _).map_id _)).trans ((Over.pullback _).map_id _))).trans
      (Category.comp_id _)

section Linear

variable {f : B.A ⟶ B'.A} [IsMonHom f]

variable [Algebra ℤ_[p] C]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

end Linear

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem toG_goodPoint (x : specO O O ⟶ (goodPoint hv ε j B o).Gt) : (goodPoint hv ε j B o).toG x = x :=
  (goodPoint hv ε j B o).hom_ext_red fun m => (goodPoint hv ε j B o).red_toG x m

theorem toA_homO (f : B.A ⟶ B'.A) (x : specO O O ⟶ (goodPoint hv ε j B o).Gt) :
    (goodPoint hv ε j B' o').toA (x ≫ homO hv ε j o o' f) = (goodPoint hv ε j B o).toA x ≫ homC hv ε j o o' f := by
  have h1 := ((goodPoint hv ε j B o).eq_toA_iff x _).1 rfl
  have h2 : (homC hv ε j o o' f).left ≫ (goodPoint hv ε j B' o').gen =
      (goodPoint hv ε j B o).gen ≫ (homO hv ε j o o' f).left := pullback.lift_fst _ _ _
  rw [toG_goodPoint] at h1
  symm
  rw [Point.eq_toA_iff, toG_goodPoint, Over.comp_left, Category.assoc, h2]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (homO hv ε j o o' f).left) h1).trans (Category.assoc _ _ _))

variable [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

theorem homV_bLie (f : B.A ⟶ B'.A) [IsMonHom f] (x : LieG (goodPoint hv ε j B o).Gt) :
    homV hv ε j o o' f ((goodPoint hv ε j B o).bLie x) = (goodPoint hv ε j B' o').bLie (homLie hv ε j o o' f x) :=
  mapV_bLie _ (homO hv ε j o o' f) rfl (toA_homO hv ε j o o' f) x

variable {f : B.A ⟶ B'.A} [IsMonHom f]


end Good

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] {ℓ : ℕ} [Fact ℓ.Prime]
  {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O)
  (ε : Eps ℓ C) (i : K →+* C) {T T' : PAT H (Sp (𝓞 K))} {f g : T.t.G ⟶ T'.t.G}
  (hf : Serre.IsLinearHom T.t.act T'.t.act f) (hg : Serre.IsLinearHom T.t.act T'.t.act g)

variable [Algebra ℤ_[ℓ] C]

variable [Algebra ℤ_[ℓ] O] [IsScalarTower ℤ_[ℓ] O C]

variable [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [IsAlgClosed C] [CharZero C]

theorem patV_bLie : letI := H.starRing
    ∀ x, patV hv ε i hf ((patPoint hv ε i T).bLie x) = (patPoint hv ε i T').bLie (patLie hv ε i hf x) :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homV_bLie (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

end Triples

end GlobalTheory.PointMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatible
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LieBasisRing

open GlobalTheory.KSExist.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isSplitting_embS {l : Level H} (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => (algebraMap c.F S).comp (embK c σ) := by
  refine EigenSplit.isSplitting_of_isDomain (S := c.F) (σ := fun σ : E →+* ℂ => embK c σ) (fun σ σ' e => ?_)
    (NumberField.Embeddings.card E ℂ) _ ?_
  · have e' : embF c σ = embF c σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e
    ext x
    have := congrArg (fun f : E →+* c.F => ((f x : c.F) : ℂ)) e'
    exact this
  · have : IsUnit ((NumberField.discr E : ℤ) : c.F) :=
      isUnit_iff_ne_zero.2 (by exact_mod_cast NumberField.discr_ne_zero E)
    simpa using this.map (algebraMap c.F S)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
  {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}

theorem isCombAt_of_isLieComb (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR S ⟶ A))
    (cf : Fin n → S) (w : epsR S ⟶ A) (h : IsLieComb cf v w) :
    IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => pushHom hπ (epsR S) (u i), fun i => ?_, (push_prod hπ u).symm⟩
  show (u i).left ≫ π = _
  rw [hu i, Category.assoc]
  rfl

end GlobalTheory.LieBasisRing

namespace GlobalTheory.LieBasisRing

theorem span_eq_top {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O]
    (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* S} (hχ : EigenSplit.IsSplitting χ)
    {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR S ⟶ A)) (hub : ∀ σ k, IsTangent (ub σ k))
    (hbasis : ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w) :
    Submodule.span S (Set.range fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)) = ⊤ := by
  let ρ : O →+* Module.End S (Serre.Lie a) := Module.toModuleEnd S (S := O) (Serre.Lie a)
  rw [eq_top_iff]
  intro x _
  rw [← EigenSplit.sum_proj hχ ρ x]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hx := EigenSplit.proj_mem hχ ρ σ x
  obtain ⟨cf, hcf⟩ := hbasis σ (EigenSplit.proj hχ ρ σ x).hom (EigenSplit.proj hχ ρ σ x).isTangent fun z =>
    congrArg Serre.Lie.hom (EigenSplit.mem_eigenSub.1 hx z)
  have e : EigenSplit.proj hχ ρ σ x = ∑ i, cf i • Serre.Lie.mk a (ub σ i) (hub σ i) :=
    Serre.Lie.ext ((Serre.Lie.isLieComb_iff cf (fun i => Serre.Lie.mk a (ub σ i) (hub σ i)) _).1 hcf)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, i⟩, rfl⟩)

theorem linearIndependent {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] [IsCommMonObj A] {O : Type}
    [CommRing O] (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* S}
    (hχ : EigenSplit.IsSplitting χ) {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR S ⟶ A))
    (hub : ∀ σ k, IsTangent (ub σ k))
    (heig : ∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ ub σ k)
    (huniq : ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∀ cf cf', IsLieComb cf (ub σ) w → IsLieComb cf' (ub σ) w → cf = cf') :
    LinearIndependent S fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _) := by
  let ρ : O →+* Module.End S (Serre.Lie a) := Module.toModuleEnd S (S := O) (Serre.Lie a)
  let v : (Σ σ, Fin (m σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)
  have hmem : ∀ k, v k ∈ EigenSplit.eigenSub ρ (χ k.1) := fun k =>
    EigenSplit.mem_eigenSub.2 fun z => Serre.Lie.ext (heig k.1 k.2 z)
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  obtain ⟨σ, i⟩ := k
  have h1 := congrArg (EigenSplit.proj hχ ρ σ) hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, Fintype.sum_sigma] at h1
  have h2 : ∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩ = 0 := by
    rw [← h1, Finset.sum_eq_single σ]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, EigenSplit.proj_of_mem hχ (hmem ⟨σ, j⟩)]
    · intro σ' _ hσ'
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, EigenSplit.proj_of_mem_ne hχ hσ' (hmem ⟨σ', j⟩), smul_zero]
    · intro h; exact absurd (Finset.mem_univ σ) h
  have hw : ∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩ ∈ EigenSplit.eigenSub ρ (χ σ) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem ⟨σ, j⟩)
  have c1 : IsLieComb (fun j => g ⟨σ, j⟩) (ub σ) (∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩).hom :=
    (Serre.Lie.isLieComb_iff _ (fun j => v ⟨σ, j⟩) _).2 rfl
  have c0 : IsLieComb (0 : Fin (m σ) → S) (ub σ) (∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩).hom :=
    (Serre.Lie.isLieComb_iff _ (fun j => v ⟨σ, j⟩) _).2 (by rw [h2]; simp)
  have := huniq σ _ (Serre.Lie.isTangent _) (fun z => congrArg Serre.Lie.hom (EigenSplit.mem_eigenSub.1 hw z))
    _ _ c1 c0
  exact congrFun this i

end GlobalTheory.LieBasisRing

namespace GlobalTheory.LieBasisRing

open GlobalTheory.KSExist.FrameLift

theorem lifts_basis_mod_fil : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left},
    IsGrpPullback A Xo.univ.t.G y.x π →
    ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) →
    ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) →
    Submodule.span S (Set.range hb) ⊔ Fil A = ⊤ ∧
      LinearIndependent S (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  intro P E _ _ _ H Dw l Xo c S _ _ y A _ π hπ ub hub hb hhb
  classical
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have : IsCommMonObj A := hA.comm
  obtain ⟨a, ha⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback Xo.univ.t.act hπ
  have htan : ∀ σ k, IsTangent (ub σ k) := fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k)
  have heig : ∀ σ k z, ub σ k ≫ a.act z =
      GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ ub σ k := fun σ k z =>
    (eig_iff hπ (ha z) _ _).1 (by rw [hub]; exact y.eig σ k z)
  have eu : ∀ σ, y.u σ = fun i => (ub σ i).left ≫ π := fun σ => funext fun i => (hub σ i).symm
  have hbasis : ∀ σ (w : epsR S ⟶ A), IsTangent w →
      (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w := by
    intro σ w ht he
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [eu σ] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩
  have huniq : ∀ σ (w : epsR S ⟶ A), IsTangent w →
      (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ w) →
      ∀ cf cf', IsLieComb cf (ub σ) w → IsLieComb cf' (ub σ) w → cf = cf' := by
    intro σ w ht he cf cf' h h'
    obtain ⟨cf₀, -, hu⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    have k := isCombAt_of_isLieComb hπ _ cf w h
    have k' := isCombAt_of_isLieComb hπ _ cf' w h'
    rw [← eu σ] at k k'
    exact (hu cf k).trans (hu cf' k').symm
  have L := (P.2.1 S A _ hA gA).1
  let v : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub k.1 k.2) (htan _ _)
  have hχ := isSplitting_embS (E := E) c S
  have hspan : Submodule.span S (Set.range v) = ⊤ := span_eq_top a hχ ub htan hbasis
  have hind : LinearIndependent S v := linearIndependent a hχ ub htan heig huniq
  have hv : (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = (L.quotEquiv a).symm ∘ v := by
    funext k
    rw [Function.comp_apply, LinearEquiv.eq_symm_apply, LieExact.quotEquiv_mk, L.toLie_eq_iff]
    exact hhb k
  refine ⟨?_, hv ▸ hind.map' _ (L.quotEquiv a).symm.ker⟩
  have h1 : Submodule.map (Fil A).mkQ (Submodule.span S (Set.range hb)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span S (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = ⊤
    rw [hv, Set.range_comp, eq_top_iff]
    intro q _
    have hq : (L.quotEquiv a) q ∈ Submodule.span S (Set.range v) := hspan ▸ Submodule.mem_top
    simpa using hq
  have h2 := congrArg (Submodule.comap (Fil A).mkQ) h1
  rwa [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] at h2

end GlobalTheory.LieBasisRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatibleStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grp_pullback_basis_lift_compatible : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) → ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) → Submodule.span S (Set.range hb) ⊔ Fil A = ⊤ ∧ LinearIndependent S (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  first | exact @GlobalTheory.LieBasisRing.lifts_basis_mod_fil | exact GlobalTheory.LieBasisRing.lifts_basis_mod_fil | (intros; apply GlobalTheory.LieBasisRing.lifts_basis_mod_fil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowWeightGramAlgebraic
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelUnip

theorem pow_apply_eq_zero {R : Type} [CommRing R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (hN : ∀ i j : Fin n, (j : ℕ) ≤ i → N i j = 0) :
    ∀ k : ℕ, ∀ i j : Fin n, (j : ℕ) < i + k → (N ^ k) i j = 0 := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply_ne]
    intro h; subst h; omega
  | succ k ih =>
    intro i j hij
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) ≤ i
    · rw [hN i l hl, zero_mul]
    · rw [ih l j (by omega), mul_zero]

theorem sub_one_pow_eq_zero' {κ : Type} [CommRing κ] {n : ℕ} (X : Matrix (Fin n) (Fin n) κ)
    (h0 : ∀ i j : Fin n, (j : ℕ) < i → X i j = 0) (h1 : ∀ i, X i i = 1) : (X - 1) ^ n = 0 := by
  have hN : ∀ i j : Fin n, (j : ℕ) ≤ i → (X - 1) i j = 0 := by
    intro i j hij
    rcases Nat.lt_or_eq_of_le hij with h | h
    · have h' : j ≠ i := fun e => by subst e; omega
      rw [Matrix.sub_apply, Matrix.one_apply_ne h'.symm, h0 i j h, sub_zero]
    · have e : j = i := Fin.ext h
      subst e
      rw [Matrix.sub_apply, Matrix.one_apply_eq, h1 j, sub_self]
  ext i j
  rw [pow_apply_eq_zero _ hN n i j (by omega), Matrix.zero_apply]

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_matrix_pow (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {y : GL (Fin n) (Formalism.L2.Herm.intAf F E)} {r : ℕ}
    (h : ∀ P ∈ T, (((Formalism.UG.bc (resS F P) y : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) - 1) ^ r = 0)
    {b : 𝓞 E} (hb : b ∈ J) :
    ∃ s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E), oToS F E b • ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r = M • s := by
  have key : ∀ i j, ∃ c, oToS F E b * ((((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) i j) = M • c := by
    intro i j
    have h0 : ∀ P ∈ T, resS F P ((((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) i j) = resS F P 0 := by
      intro P hP
      have e : (resS F P).mapMatrix (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) =
          (((Formalism.UG.bc (resS F P) y : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) - 1) ^ r := by
        rw [map_pow, map_sub, map_one]; rfl
      have := congrFun (congrFun (e.trans (h P hP)) i) j
      rw [map_zero]
      exact this
    have h1 : (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) i j ∈ (∏ P ∈ T, P.asIdeal).map (oToS F E) := by
      have := GlobalTheory.LevelUnique.mem_map_prod (oToS F E) T fun P hP => GlobalTheory.LevelUnique.sub_mem_idS (h0 P hP)
      simpa using this
    have h2 := Ideal.mul_mem_mul h1 (Ideal.mem_map_of_mem (oToS F E) hb)
    rw [← Ideal.map_mul, hJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton'] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [mul_comm, ← hc, nsmul_eq_mul, mul_comm]⟩
  choose c hc using key
  exact ⟨Matrix.of c, Matrix.ext fun i j => by rw [Matrix.smul_apply, smul_eq_mul, hc i j]; rfl⟩

end Res

theorem keeps_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, (β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), K *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have hN := fun z hz => (hfr _).2 (GlobalTheory.LevelUnique.conj_mulVec_mem _ β s z ((hfr z).1 hz))
  generalize β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 = N at hN hK
  intro z hz
  have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ (hN _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
  convert h4 using 1
  ext i
  simp [Matrix.mulVec, dotProduct, hK, map_sum, map_mul]

theorem exists_pow_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) {r : ℕ}
    (h : ∀ P ∈ T, (((redFn β P x : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) - 1) ^ r = 0) {b : 𝓞 E} (hb : b ∈ J)
    {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - 1) ^ r = M • N := by
  obtain ⟨y, rfl⟩ := hx
  simp only [redFn_frGL] at h
  obtain ⟨s, hs⟩ := exists_matrix_pow T hJ h hb
  have e0 : ((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) * (β⁻¹).1 := rfl
  have e2 : (((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) ^ r =
      β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) * (β⁻¹).1 := by
    have e1 : ((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
        β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) * (β⁻¹).1 := by
      rw [e0, map_sub, map_one, mul_sub, sub_mul, mul_one, Units.mul_inv]
    rw [e1, Units.conj_pow, map_pow]
  have e4 : ((oToS F E b : Formalism.L2.Herm.intAf F E) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) •
      (Formalism.L2.Herm.intAf F E).subtype.mapMatrix (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) =
      M • (Formalism.L2.Herm.intAf F E).subtype.mapMatrix s := by
    ext i j
    have := congrArg (fun m : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) => (Formalism.L2.Herm.intAf F E).subtype (m i j)) hs
    simp only [Matrix.smul_apply, map_nsmul, smul_eq_mul, map_mul] at this
    simpa [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul] using this
  have e3 : ((oToS F E b : Formalism.L2.Herm.intAf F E) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) •
      ((((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) ^ r) =
      M • (β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix s * (β⁻¹).1) := by
    rw [e2, ← smul_mul_assoc, ← mul_smul_comm, e4, mul_smul_comm, smul_mul_assoc]
  refine ⟨(β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix s * (β⁻¹).1).map (Algebra.TensorProduct.comm F _ E).symm,
    keeps_hat hfr s (fun i j => by rw [Matrix.map_apply, AlgEquiv.apply_symm_apply]; rfl), Matrix.ext fun i j => ?_⟩
  apply (Algebra.TensorProduct.comm F _ E).injective
  have hm : ((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (Algebra.TensorProduct.comm F _ E).toRingHom.mapMatrix K := Matrix.ext fun i j => hK i j
  have hpow : ((((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) ^ r) i j =
      Algebra.TensorProduct.comm F _ E (((K - 1) ^ r) i j) := by
    rw [hm, ← map_one (Algebra.TensorProduct.comm F _ E).toRingHom.mapMatrix, ← map_sub, ← map_pow]
    rfl
  rw [Matrix.smul_apply, Matrix.smul_apply, map_nsmul, Matrix.map_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, map_mul,
    ← hpow]
  exact congrFun (congrFun e3 i) j

variable {D : D7}

theorem sub_one_mulVec_mem {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {k : GA D V} (hk : Lev.finE V k ∈ St β) :
    ∀ z ∈ latGHat V 1, ((finHom V k : Matrix (Fin V.rank) (Fin V.rank) _) - 1) *ᵥ z ∈ latGHat V 1 := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨y, hy⟩ := hk
  have hN : ∀ z ∈ latHat V, (finHom V k : Matrix (Fin V.rank) (Fin V.rank) _) *ᵥ z ∈ latHat V := by
    rw [hl]
    exact keeps_hat hfr (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
      (fun i j => by
        have := congrArg (fun x : GL (Fin V.rank) (Lev.EAf D) => (x : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j) hy
        exact this)
  intro z hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact sub_mem (GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz) hz

theorem exists_pow_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k : GA D V} (hk : Lev.finE V k ∈ St β) {r : ℕ}
    (h : ∀ P ∈ T, (((redFn β P (Lev.finE V k) : GL (Fin V.rank) (kP P)) : Matrix (Fin V.rank) (Fin V.rank) (kP P)) - 1) ^ r = 0)
    {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) •
        ((((finHom V k : Matrix (Fin V.rank) (Fin V.rank) _) - 1) ^ r) *ᵥ z -
          (0 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ z) = M • w := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_pow_hat hfr T hJ hk h hb (K := (finHom V k : Matrix (Fin V.rank) (Fin V.rank) _))
    (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [Matrix.zero_mulVec, sub_zero, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem step {R : Type} [CommRing R] {n : ℕ} (K P : Matrix (Fin n) (Fin n) R) (y₀ y₁ v w₁ w₂ : Fin n → R) (M : ℕ)
    (e₁ : y₁ - K *ᵥ y₀ = M • w₁) (e₂ : y₀ - P *ᵥ v = M • w₂) :
    (y₁ - y₀) - ((K - 1) * P) *ᵥ v = M • (w₁ + (K - 1) *ᵥ w₂) := by
  have e₂' := eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp e₂).symm
  have e₁' := sub_eq_iff_eq_add.mp e₁
  rw [← Matrix.mulVec_mulVec, e₂', e₁', Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, smul_add]
  abel

theorem approx_pow {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    {K : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (hK : ∀ z ∈ latGHat V 1, (K - 1) *ᵥ z ∈ latGHat V 1) {f : La →ₗ[𝓞 D.host.E] La}
    (hf : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - K *ᵥ finVec V (ι a) = M • w) :
    ∀ n : ℕ, ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (((f - 1) ^ n) a)) - ((K - 1) ^ n) *ᵥ finVec V (ι a) = M • w := by
  have hm : ∀ a, finVec V (ι a) ∈ latGHat V 1 := fun a =>
    (GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hι.2 ▸ LinearMap.mem_range_self ι a)
  have hJ : ∀ (g : La →ₗ[𝓞 D.host.E] La) a, a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) →
      g a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) := by
    intro g a ha
    have : g a ∈ (J • (⊤ : Submodule (𝓞 D.host.E) La)).map g := Submodule.mem_map_of_mem ha
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  intro n
  induction n with
  | zero =>
    intro a _
    exact ⟨0, zero_mem _, by rw [pow_zero, pow_zero, Matrix.one_mulVec, Module.End.one_apply, sub_self, smul_zero]⟩
  | succ n ih =>
    intro a ha
    obtain ⟨w₂, hw₂, e₂⟩ := ih a ha
    obtain ⟨w₁, hw₁, e₁⟩ := hf _ (hJ ((f - 1) ^ n) a ha)
    refine ⟨w₁ + (K - 1) *ᵥ w₂, add_mem hw₁ (hK _ hw₂), ?_⟩
    have ex : ((f - 1) ^ (n + 1)) a = f (((f - 1) ^ n) a) - ((f - 1) ^ n) a := by
      rw [pow_succ', Module.End.mul_apply]; rfl
    have hsub : ∀ u v : Fin V.rank → D.host.E, finVec V (u - v) = finVec V u - finVec V v := fun u v => by
      funext i; simp [finVec, TensorProduct.tmul_sub]
    rw [ex, pow_succ', map_sub ι, hsub]
    exact step _ _ _ _ _ _ _ _ e₁ e₂

end GlobalTheory.LevelUnip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantOfModular
noncomputable section

open GlobalTheory.WeilM MeasureTheory MeasureTheory.Measure
open scoped Matrix NNReal

namespace GlobalTheory.ParAvg

theorem isMulRightInvariant_of_modular {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (h : ∀ g : G, modularCharacterFun g = 1) : μ.IsMulRightInvariant :=
  ⟨fun g => by rw [map_right_mul_eq_modularCharacterFun_smul μ g, h g, one_smul]⟩

theorem modularCharacterFun_GL {r : ℕ} {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    [LocallyCompactSpace (GL (Fin r) E)] (a : GL (Fin r) E) : modularCharacterFun a = 1 := by
  borelize (GL (Fin r) E)
  refine GlobalTheory.SplitFlip.hom_eq_one_of_center (modularCharacter : GL (Fin r) E →* ℝ≥0) (fun z hz => ?_) a
  change modularCharacterFun z = 1
  have e : map (fun x : GL (Fin r) E => x * z) (haar : Measure (GL (Fin r) E)) = haar := by
    rw [show (fun x : GL (Fin r) E => x * z) = fun x => z * x from funext fun x => (hz x).symm,
      map_mul_left_eq_self]
  rw [modularCharacterFun_eq_haarScalarFactor (haar : Measure (GL (Fin r) E)) z]
  simp only [e, haarScalarFactor_self]

end GlobalTheory.ParAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecNonzeroOnFiniteOfGenerated
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory


open GlobalTheory.ZeroDimSystem in
theorem exists_sec_nonzero_on_finite_of_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∀ S : Set X, S.Finite → ∃ s : L.Sec, ∀ x ∈ S, x ∈ nonzeroLocus s := by
  intro k _ _ X _ p L _ n u hu S hS
  classical
  letI : Algebra k Γ(X, ⊤) := (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have hne : ∀ x ∈ hS.toFinset, vanishAt (k := k) u x ≠ ⊤ := fun x _ h => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
    exact single_notMem_vanishAt (k := k) u hi (h.symm ▸ Submodule.mem_top)
  have h := Subspace.biUnion_ne_univ_of_top_notMem (k := k) (E := Fin n → k)
    (s := hS.toFinset.image (vanishAt (k := k) u)) (by
      rw [Finset.mem_image]
      rintro ⟨x, hx, h⟩
      exact hne x hx h)
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem _).1 h
  refine ⟨comb u c, fun x hx => ?_⟩
  by_contra hxc
  exact hc (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hS.mem_toFinset.2 hx)))
    ((mem_vanishAt u x c).2 hxc))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockDecomposition
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameLab

variable {D : D7}

theorem cO_cO (x : 𝓞 D.host.E) : Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E x) = x :=
  RingOfIntegers.ext (star_star (x : D.host.E))

theorem mem_conjPl_of_fixed (P : HeightOneSpectrum (𝓞 D.host.E)) {x : 𝓞 D.host.E} (hx : Formalism.DivisionValues.cO D.host.E x = x) :
    x ∈ (Formalism.DivisionValues.conjPl P).asIdeal ↔ x ∈ P.asIdeal := by
  change x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := by rw [← cO_cO y, e, hx]
    rwa [← this]
  · exact fun h => ⟨x, h, hx⟩

theorem under_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl P).under (𝓞 (maximalRealSubfield D.host.E)) = P.under (𝓞 (maximalRealSubfield D.host.E)) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  exact mem_conjPl_of_fixed P (x := algebraMap _ (𝓞 D.host.E) x)
    (RingOfIntegers.ext (IsCMField.complexConj_apply_eq_self D.host.E (x : maximalRealSubfield D.host.E)))

theorem absNorm_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl P).asIdeal = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal _ (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

end GlobalTheory.FrameLab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillation
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
namespace GlobalTheory.RefSum

theorem nuBetween_sum_and_eLoc_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (cx : Lt1 Dw → ℕ), (∀ A B : Lt1 Dw → ℝ, (∀ f, FacBetween Xo la f (cx f) (A f) (B f)) → NuBetween Xo la cx (∑ f, A f) (∑ f, B f) ∧ ∃ n : ℕ, NuBetween Xo la cx n (n + (∑ f, (B f - A f) + 1))) ∧ ∀ b : ℝ, OscLe Xo c p cx b → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Comp Xo c), (letI := H.starRing; eLoc Y Z la cx ≤ (b : EReal)) := by
  intro E _ _ _ H Dw l Xo c p _ la cx
  letI := H.starRing
  have hcs : ∀ g : Lt1 Dw → ℝ, (((∑ f, g f : ℝ)) : EReal) = ∑ f, ((g f : ℝ) : EReal) := fun g =>
    map_sum (⟨⟨((↑) : ℝ → EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) g Finset.univ
  refine ⟨fun A B hAB => ⟨fun T io e ho y => ⟨?_, fun ha => ?_⟩, ?_⟩, ?_⟩
  · rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).1
  · rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).2 ha
  · set s : ℝ := ∑ f, A f with hs
    refine ⟨⌊max 0 s⌋₊, fun T io e ho y => ⟨?_, fun ha => ?_⟩⟩
    · have h0 : (0 : EReal) ≤ nuP p y cx := Finset.sum_nonneg fun f _ =>
        (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y |>.1 |> fun h => by simpa using h
      have h1 : ((s : ℝ) : EReal) ≤ nuP p y cx := by
        rw [hs, hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).1
      have hn : ((⌊max 0 s⌋₊ : ℕ) : ℝ) ≤ max 0 s := Nat.floor_le (le_max_left _ _)
      rcases le_total 0 s with h | h
      · exact (EReal.coe_le_coe_iff.2 (hn.trans (max_eq_right h).le)).trans h1
      · exact (EReal.coe_le_coe_iff.2 (hn.trans (max_eq_left h).le)).trans (by simpa using h0)
    · have hu : nuP p y cx ≤ ((∑ f, B f : ℝ) : EReal) := by
        rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).2 ha
      refine hu.trans (EReal.coe_le_coe_iff.2 ?_)
      have hlt : max 0 s < ((⌊max 0 s⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have hsd : ∑ f, (B f - A f) = ∑ f, B f - s := by rw [Finset.sum_sub_distrib]
      have hm : s ≤ max 0 s := le_max_right _ _
      linarith
  · intro b hb O _ β Y Z
    obtain ⟨A, hA⟩ := hb la
    calc eLoc Y Z la cx ≤ ((((A : ℝ) + b : ℝ)) : EReal) - (((A : ℝ)) : EReal) :=
          EReal.sub_le_sub (nuPSup_le fun T io e ho y hy => (hA T io e ho y).2 hy.2)
            (le_nuPInf fun T io e ho y _ => (hA T io e ho y).1)
      _ = (b : EReal) := by rw [← EReal.coe_sub]; congr 1; ring

end GlobalTheory.RefSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillationStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productDepth_sum_rounding_oscillation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (cx : Lt1 Dw → ℕ), (∀ A B : Lt1 Dw → ℝ, (∀ f, FacBetween Xo la f (cx f) (A f) (B f)) → NuBetween Xo la cx (∑ f, A f) (∑ f, B f) ∧ ∃ n : ℕ, NuBetween Xo la cx n (n + (∑ f, (B f - A f) + 1))) ∧ ∀ b : ℝ, OscLe Xo c p cx b → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Comp Xo c), (letI := H.starRing; eLoc Y Z la cx ≤ (b : EReal)) := by
  first | exact @GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le | exact GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le | (intros; apply GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le <;> assumption)
end
end
