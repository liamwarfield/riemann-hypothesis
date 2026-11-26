module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldOfTangentVectorOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelEqUnitNormMulTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRouteDatumTranslationCombinationGoodPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsThetaShiftTriple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section
namespace GlobalTheory.VertCoeffRing

theorem isLieBasis_tvE : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)), IsLieBasis (fun a => GlobalTheory.VertCoeffRing.tvE (v a)) := by
  intro R _ G _ _ n v
  have hE : (overAt (𝟙 (Sp R)) (DualNumber R)).hom = (epsR R).hom := by
    simp [epsR, overAt]
  let e : epsR R ⟶ overAt (𝟙 (Sp R)) (DualNumber R) := Over.homMk (𝟙 _) (by simp [hE])
  let f : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ epsR R := Over.homMk (𝟙 _) (by simp [hE])
  have hfe : f ≫ e = 𝟙 _ := Over.OverMorphism.ext (by simp [e, f])
  have hef : e ≫ f = 𝟙 _ := Over.OverMorphism.ext (by simp [e, f])

  have htv : ∀ x : TanM (𝟙 (Sp R)) G, tvE x = e ≫ tv x := by
    intro x
    apply Over.OverMorphism.ext
    first
    | (simp only [e, Over.comp_left, Over.homMk_left, Category.id_comp]; exact tvE_left x)
    | simp [e, tvE_left x]
  have hadd : ∀ x y : TanM (𝟙 (Sp R)) G, tvE (x + y) = tvE x * tvE y := by
    intro x y; rw [htv, htv, htv, PullbackSections.tv_add, MonObj.comp_mul]
  have hzero : tvE (0 : TanM (𝟙 (Sp R)) G) = 1 := by
    rw [htv, PullbackSections.tv_zero, MonObj.comp_one]

  have hsmul : ∀ (a : R) (x : TanM (𝟙 (Sp R)) G),
      (tvE (a • x)).left = spMap (epsScaleR a) ≫ (tvE x).left := by
    intro a x; rw [tvE_left, tvE_left, PullbackSections.tv_smul]
    first
    | rfl
    | (simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)
  have hinj : ∀ x y : TanM (𝟙 (Sp R)) G, tvE x = tvE y → x = y := by
    intro x y h
    apply PullbackSections.tanM_ext
    have h' := congrArg (fun t => f ≫ t) h
    simpa [htv, ← Category.assoc, hfe] using h'
  have hsum : ∀ (c : Fin n → R) (s : Finset (Fin n)),
      tvE (∑ i ∈ s, c i • v i) = ∏ i ∈ s, tvE (c i • v i) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]

  have hcomb : ∀ (c : Fin n → R) (w : epsR R ⟶ G),
      IsLieComb c (fun a => tvE (v a)) w ↔ w = tvE (∑ i, c i • v i) := by
    intro c w
    rw [IsLieComb.eq_1, hsum]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [List.prod_ofFn]
      refine Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext ?_
      rw [hu i, hsmul]
    · rintro rfl
      exact ⟨fun i => tvE (c i • v i), fun i => hsmul _ _, by rw [List.prod_ofFn]⟩

  have hfa : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp
  have hdual : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    simp only [spMap.eq_1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id]
    all_goals rfl
  have hz : spMap (epsScaleR (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have h0 : epsScaleR (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
      refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
      all_goals first
        | (simp [epsScaleR]; done)
        | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done)
        | (simp [epsScaleR.eq_1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fstHom_apply,
            TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]; done)
        | rfl
        | (simp [epsScaleR]; rfl)
    rw [h0]
    simp only [spMap.eq_1, CommRingCat.ofHom_comp, Spec.map_comp]
  have hu : (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left = spMap (algebraMap R (DualNumber R)) := by
    first
    | simp [overAt]
    | (have h := Over.w (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))); simpa [overAt] using h)
  have hone : (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left =
      spMap (algebraMap R (DualNumber R)) ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left := by
    calc (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left
        = (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left := rfl
      _ = _ := by rw [hu]

  have key : ∀ g : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, smT (𝟙 (Sp R)) 0 g = 1 ↔ IsTangent (e ≫ g) := by
    intro g
    rw [IsTangent.eq_1]
    have hl : (smT (𝟙 (Sp R)) 0 g).left = spMap (algebraMap R (DualNumber R)) ≫
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g.left := by
      rw [← Category.assoc, ← hz]
      first
      | rfl
      | (simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)
    have he : ∀ t : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (e ≫ t).left =
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t.left := by
      intro t; simp [e]
    rw [he]
    constructor
    · intro h
      have h2 := congrArg Over.Hom.left h
      rw [hl, hone] at h2
      have h3 := congrArg (fun t => spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t) h2
      simpa only [← Category.assoc, hdual, Category.id_comp] using h3
    · intro h
      apply Over.OverMorphism.ext
      rw [hl, hone, h]
  have htan : ∀ x, IsTangent (tvE x) := fun x => by
    rw [htv]; exact (key (tv x)).1 (PullbackSections.tv_mem x)
  have hsurj : ∀ w : epsR R ⟶ G, IsTangent w → ∃ x, tvE x = w := by
    intro w hw
    have hw' : IsTangent (e ≫ (f ≫ w)) := by rwa [← Category.assoc, hef, Category.id_comp]
    refine ⟨PullbackSections.mkT (f ≫ w) ((key _).2 hw'), ?_⟩
    rw [htv, PullbackSections.tv_mkT, ← Category.assoc, hef, Category.id_comp]
  rw [IsLieBasis.eq_1]
  refine ⟨fun i => htan (v i), fun w hw => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj w hw
  refine ⟨⇑(v.repr x), (hcomb _ _).2 ?_, fun c hc => ?_⟩
  · rw [v.sum_repr]
  · have h := hinj _ _ ((hcomb c _).1 hc)
    rw [h, v.repr_sum_self]

end GlobalTheory.VertCoeffRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasisStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLieBasis_dualPoints_of_tangentModule_basis : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ} (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)), IsLieBasis (fun a => GlobalTheory.VertCoeffRing.tvE (v a)) := by
  first | exact @GlobalTheory.VertCoeffRing.isLieBasis_tvE | exact GlobalTheory.VertCoeffRing.isLieBasis_tvE | (intros; apply GlobalTheory.VertCoeffRing.isLieBasis_tvE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieBasisCoeffsOfDerivationAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieBasisCoeffsOfDerivationAffineOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.VertCoeffRing

open TrivSqZeroExt (inl inr)

theorem existsUnique_coeff_alg {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) {dd : Fin n → Fld G.left}
    (hdd : ∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0)
      (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f))
    {C : Type} [CommRing C] [Algebra R C] (y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) C ⟶ G)
    {V : G.left.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ y.left ⁻¹ᵁ V) (δ : Γ(G.left, V) → C)
    (hadd : ∀ f f', δ (f + f') = δ f + δ f')
    (hmul : ∀ f f', δ (f * f') = evalPt y.left V h f * δ f' + evalPt y.left V h f' * δ f)
    (hbase : ∀ r, δ (constFn G.hom V r) = 0) :
    ∃! c : Fin n → C, ∀ f, δ f = ∑ a, c a * evalPt y.left V h (dd a V f) := by
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C) ⟶ G :=
    ReciprocityTheory.ChartRestriction.G.Chart.spMap (TrivSqZeroExt.inlAlgHom R C C) ≫ y
  have hz : ⊤ ≤ z.left ⁻¹ᵁ V := fun t _ => h (Set.mem_univ _)
  have ez : ∀ s, evalPt z.left V hz s = inl (evalPt y.left V h s) := fun s =>
    evalPt_spMap_comp (TrivSqZeroExt.inlAlgHom R C C).toRingHom y.left V h hz s
  obtain ⟨ψ, hψ⟩ := GlobalTheory.InvFieldBasis.exists_dualHom (evalPt y.left V h) δ hadd hmul
  obtain ⟨x, hx, ex⟩ := exists_evalPt_eq hV ψ
  have hxp : x ≫ G.hom = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C)).hom := by
    refine (eq_spMap_of_evalPt _ (algebraMap R (DualNumber C)) fun a => ?_).trans rfl
    rw [← evalPt_constFn G.hom x V hx, ex, hψ, hbase, evalPt_constFn G.hom y.left V h a,
      GlobalTheory.InvFieldBasis.evalPt_congr (Over.w y) ⊤ le_rfl le_rfl]
    have e2 : evalPt (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) C).hom ⊤ le_rfl
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = algebraMap R C a :=
      evalPt_spMap (algebraMap R C) a
    rw [e2, TrivSqZeroExt.inr_zero, add_zero]
    exact (TrivSqZeroExt.algebraMap_eq_inl' R C C _).symm
  let w : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C) ⟶ G := Over.homMk x hxp
  have ext : ∀ {B : Type} [CommRing B] [Algebra R B] (u u' : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G),
      u.left = u'.left → u = u' := fun u u' e => Over.OverMorphism.ext e
  let fstR : DualNumber C →ₐ[R] C := TrivSqZeroExt.fstHom R C C
  let J : Ideal (DualNumber C) := RingHom.ker fstR
  have memJ : ∀ a : DualNumber C, a ∈ J ↔ a.fst = 0 := fun a => RingHom.mem_ker
  have hJ : J ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    rw [Ideal.mem_bot]
    have ea : a = inr a.snd := TrivSqZeroExt.ext ((memJ a).1 ha) rfl
    have eb : b = inr b.snd := TrivSqZeroExt.ext ((memJ b).1 hb) rfl
    rw [ea, eb, TrivSqZeroExt.inr_mul_inr]
  let g : C →ₐ[R] DualNumber C ⧸ J := (Ideal.Quotient.mkₐ R J).comp (TrivSqZeroExt.inlAlgHom R C C)
  have hg : Ideal.Quotient.mkₐ R J = g.comp fstR := by
    refine AlgHom.ext fun a => ?_
    change Ideal.Quotient.mk J a = Ideal.Quotient.mk J (inl a.fst)
    refine Ideal.Quotient.eq.2 ((memJ _).2 ?_)
    simp
  have t1 : ReciprocityTheory.ChartRestriction.G.Chart.spMap fstR ≫ z = y := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp]
    have : fstR.comp (TrivSqZeroExt.inlAlgHom R C C) = AlgHom.id R C := AlgHom.ext fun _ => rfl
    rw [this, ReciprocityTheory.ChartRestriction.G.Chart.spMap_id, Category.id_comp]
  have t2 : ReciprocityTheory.ChartRestriction.G.Chart.spMap fstR ≫ w = y := by
    refine ext _ _ ?_
    rw [Over.comp_left]
    have h' : ⊤ ≤ (spMap fstR.toRingHom ≫ x) ⁻¹ᵁ V := fun t _ => hx (Set.mem_univ _)
    refine ext_evalPt hV h' h (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ x V hx h' f).trans ?_
    rw [ex, hψ]
    exact add_zero _
  have hred : ReciprocityTheory.ChartRestriction.G.Chart.spMap (Ideal.Quotient.mkₐ R J) ≫ z =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (Ideal.Quotient.mkₐ R J) ≫ w := by
    rw [hg, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, Category.assoc, t1, t2]
  obtain ⟨c, hc, hcu⟩ := GlobalTheory.SqZero.existsUnique_eq_lieExp_mul hv hJ hred
  have key : ∀ c' : Fin n → C, (w = GlobalTheory.SqZero.lieExp v (fun i => inr (c' i))
      (fun i => TrivSqZeroExt.inr_mul_inr _ _ _) * z) ↔
      ∀ f, δ f = ∑ a, c' a * evalPt y.left V h (dd a V f) := by
    intro c'
    obtain ⟨h₁, H₁⟩ := hdd (DualNumber C) (fun i => inr (c' i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _) z V hz
    constructor
    · intro e f
      have := H₁ f
      rw [← GlobalTheory.InvFieldBasis.evalPt_congr (show x = _ from congrArg (fun u => u.left) e) V hx h₁,
        ex, hψ] at this
      simp only [ez] at this
      exact (GlobalTheory.InvFieldBasis.dual_eq_iff _ _ _ _).1 this
    · intro e
      refine ext _ _ (ext_evalPt hV hx h₁ (RingHom.ext fun f => ?_))
      rw [H₁]
      change evalPt x V hx f = _
      rw [ex, hψ]
      simp only [ez]
      exact (GlobalTheory.InvFieldBasis.dual_eq_iff _ _ _ _).2 (e f)
  have hinr : ∀ a : J, (a : DualNumber C) = inr (a : DualNumber C).snd := fun a =>
    TrivSqZeroExt.ext ((memJ _).1 a.2) rfl
  refine ⟨fun i => (c i : DualNumber C).snd, (key _).1 (hc.trans ?_), fun c' hc' => ?_⟩
  · rw [GlobalTheory.SqZero.lieExp_congr v (fun i => hinr (c i)) _ (fun i => TrivSqZeroExt.inr_mul_inr _ _ _)]
  · have hmem : ∀ i, inr (c' i) ∈ J := fun i => (memJ _).2 rfl
    have := hcu (fun i => ⟨inr (c' i), hmem i⟩) ((key c').2 hc')
    funext i
    exact congrArg (fun d : Fin n → J => (d i : DualNumber C).snd) this

theorem existsUnique_coeff_affine_ring : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (v : Fin n → (epsR R ⟶ G)), IsLieBasis v → ∀ (dd : Fin n → Fld G.left),
    (∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + ∑ i, e i * GlobalTheory.TangentOrigin.evalPt z.left O h (dd i O f)) →
    ∀ (V V' : G.left.Opens), IsAffineOpen V → IsAffineOpen V' → V' ≤ V → ∀ (δ : Γ(G.left, V) → Γ(G.left, V')),
    (∀ f f', δ (f + f') = δ f + δ f') → (∀ f f', δ (f * f') = rsT f V' * δ f' + rsT f' V' * δ f) →
    (∀ r, δ (constFn G.hom V r) = 0) →
    ∃! c : Fin n → Γ(G.left, V'), ∀ f, δ f = ∑ a, c a * rsT (dd a V f) V' := by
  intro R _ G _ _ _ n v hv dd hdd V V' hV hV' hle δ hadd hmul hbase
  obtain ⟨t, ht, et⟩ := exists_evalPt_eq (R := Γ(G.left, V')) hV' (RingHom.id _)
  letI : Algebra R Γ(G.left, V') := (Spec.preimage (t ≫ G.hom)).hom.toAlgebra
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) Γ(G.left, V') ⟶ G :=
    Over.homMk t (Spec.map_preimage (t ≫ G.hom)).symm
  have h : ⊤ ≤ y.left ⁻¹ᵁ V := fun s hs => hle (ht hs)
  have ev : ∀ s, evalPt y.left V h s = rsT s V' := fun s => by
    refine (evalPt_res t hle h ht s).symm.trans ?_
    rw [et, GlobalTheory.KS.rsT, dite_eq_left hle]
    rfl
  have := existsUnique_coeff_alg hv hdd y hV h δ hadd (by simpa only [ev] using hmul) hbase
  simpa only [ev] using this

end GlobalTheory.VertCoeffRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieBasisCoeffsOfDerivationAffineOpenStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_lieBasis_coeffs_of_derivation_affineOpen : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (v : Fin n → (epsR R ⟶ G)), IsLieBasis v → ∀ (dd : Fin n → Fld G.left),
    (∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + ∑ i, e i * GlobalTheory.TangentOrigin.evalPt z.left O h (dd i O f)) →
    ∀ (V V' : G.left.Opens), IsAffineOpen V → IsAffineOpen V' → V' ≤ V → ∀ (δ : Γ(G.left, V) → Γ(G.left, V')),
    (∀ f f', δ (f + f') = δ f + δ f') → (∀ f f', δ (f * f') = rsT f V' * δ f' + rsT f' V' * δ f) →
    (∀ r, δ (constFn G.hom V r) = 0) →
    ∃! c : Fin n → Γ(G.left, V'), ∀ f, δ f = ∑ a, c a * rsT (dd a V f) V' := by
  first | exact @GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring | exact GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring | (intros; apply GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearChangeEulerProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.DualHomPull

theorem exists_dual_hom : ∀ (Y : Scheme.{0}) (A G : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (χ : A ⟶ G) (P'' : LB (G2 G).left), IsAbelianScheme A → IsAbelianScheme G → IsMonHom χ → P''.IsLB → (∃ t : (P''.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P''.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ∃ (D : Over Y) (_ : GrpObj D) (Q : LB (A ⊗ D).left) (h : A ⟶ D), IsAbelianScheme D ∧ GlobalTheory.AbDual.IsDual A D Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (P''.pull (χ ⊗ₘ χ).left) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) := by
  intro Y A G _ _ _ _ χ P'' hA hG hχ hP h₁ h₂
  obtain ⟨D, _, Q, hD, -, q, q'⟩ := GlobalTheory.dualAbelianScheme Y A hA
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeAxes.additive_of_triv_axes hG hP h₁ h₂
  have eχ : χ ⊗ₘ χ = lift (fst A A ≫ χ) (snd A A ≫ χ) := by ext <;> simp
  rw [eχ]
  have hE : (ev P'' (fst A A ≫ χ) (snd A A ≫ χ)).IsLB := pull_isLB hP _
  have k : ∀ {T : Over Y} (a t : T ⟶ A), evc hE a t = evc hP (a ≫ χ) (t ≫ χ) := fun a t ↦ by
    rw [evc_ev hP _ _ hE, lift_fst_assoc, lift_snd_assoc]
  have b₁ : IsAdditive (ev P'' (fst A A ≫ χ) (snd A A ≫ χ)) := (isAdditive_iff hE).2 fun T a a' t ↦ by
    haveI := hχ
    rw [k, k, k, MonObj.mul_comp]
    exact (isAdditive_iff hP).1 a₁ _ _ _ _
  have b₂ : IsAdditive (swap (ev P'' (fst A A ≫ χ) (snd A A ≫ χ))) :=
    (GlobalTheory.BirigidLift.isAdditive_swap_iff hE).2 fun T a t t' ↦ by
      haveI := hχ
      rw [k, k, k, MonObj.mul_comp]
      exact (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂ _ _ _ _
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hE b₁ b₂
  exact ⟨D, inferInstance, Q, x, hD, q, q'.additive, hx, (cls_eq_iff hE (pull_isLB q.isLB _)).1 e⟩

end GlobalTheory.DualHomPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantTangentBasisRaynaudExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteBasisTangentModuleSmoothCommGroupSch
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteBasisTangentModuleSmoothCommGroupSch
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanBasis

theorem exists_basis_tanM : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) := by
  intro R _ _ G _ _ hG
  exact GlobalTheory.RayBasis.exists_basis hG

end GlobalTheory.TanBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteBasisTangentModuleSmoothCommGroupSchStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_basis_tangentModule_smooth_commGroupScheme : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) := by
  first | exact @GlobalTheory.TanBasis.exists_basis_tanM | exact GlobalTheory.TanBasis.exists_basis_tanM | (intros; apply GlobalTheory.TanBasis.exists_basis_tanM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantTangentBasisRaynaudExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayTan

theorem smooth_H : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Smooth Y.H.hom := by
  intro R _ _ Q O _ _ _ oa Y
  have h1 : Smooth Y.q.left := Y.smooth_q
  have := Q.P.smoothDim
  have h2 : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
  rw [← Over.w Y.q]
  infer_instance

theorem exists_basis_isInv : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  intro R _ _ _ _ Q O _ _ _ oa Y
  obtain ⟨n, ⟨v⟩⟩ := GlobalTheory.T.exists_finite_basis_tangentModule_smooth_commGroupScheme R Y.H (smooth_H R Q O oa Y)
  choose dd hdd using fun a => GlobalTheory.T.exists_invariantVectorField_of_tangentVector_origin R Y.H (v a)
  exact ⟨n, v, dd, hdd⟩

end GlobalTheory.RayTan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantTangentBasisRaynaudExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_tangent_basis_raynaudExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  first | exact @GlobalTheory.RayTan.exists_basis_isInv | exact GlobalTheory.RayTan.exists_basis_isInv | (intros; apply GlobalTheory.RayTan.exists_basis_isInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationVectorBundleAbelianPullback
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt.Fibre

section Frames

variable {X Y : Scheme.{0}} {I : Type} [Fintype I] {k : Type} [CommRing k]

theorem frame_pb (f : Y ⟶ X) {F : X.Modules} [F.IsQuasicoherent] {U : X.Opens} {e : I → Γ(F, U)} (he : IsFrame e)
    {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) : IsFrame fun i => pullbackSections f F h (e i) := by
  have := (he.pullback f).res h
  exact (funext fun l => QCoh.res_pullbackSections f F le_rfl h (e l)) ▸ this

end Frames

section Reads

variable {X T : Scheme.{0}} {R K : Type} [CommRing R] [Field K] [Algebra R K] {f : Sp R ⟶ X} {f₀ : T ⟶ X}
  {ξ : Sp K ⟶ T} (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) {I : Type} [Fintype I] {U : X.Opens} {V : T.Opens}
  (hU : ⊤ ≤ f ⁻¹ᵁ U) (hVU : V ≤ f₀ ⁻¹ᵁ U) (hξ : ⊤ ≤ ξ ⁻¹ᵁ V)


variable {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]

variable {A B : X.Modules} {D : T.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent] [D.IsQuasicoherent]
  {a : (Scheme.Modules.pullback f₀).obj A ⟶ D} {b : D ⟶ (Scheme.Modules.pullback f₀).obj B} {z : a ≫ b = 0}


end Reads

section Tangent

open GlobalTheory.TanFibre GlobalTheory.Conormal
open GlobalTheory.DeRhamSheaf (onAff)
open GlobalTheory.Published.AbelianDeRham (bcMor)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

theorem omegaBase_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (h' : IsGrpPullback G'' G' f' φ') {f'' : S'' ⟶ S} {φ'' : G''.left ⟶ G.left}
    (h'' : IsGrpPullback G'' G f'' φ'') (e : f' ≫ f = f'') (e' : φ' ≫ φ = φ'') {U : S.Opens} {V : S'.Opens}
    {W : S''.Opens} (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ f' ⁻¹ᵁ V) (hW' : W ≤ f'' ⁻¹ᵁ U) (s : Γ(omega G, U)) :
    (omegaBase h').app W (pullbackSections f' _ hW ((omegaBase h).app V (pullbackSections f _ hV s))) =
      (omegaBase h'').app W (pullbackSections f'' _ hW' s) := by
  subst e e'
  have k {U : S.Opens} {V : S'.Opens} {W : S''.Opens} (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ f' ⁻¹ᵁ V)
      (hW' : W ≤ (f' ≫ f) ⁻¹ᵁ U) (s : Γ(omega G, U)) :
      ((Scheme.Modules.pullbackComp f' f).inv.app (omega G) ≫ (Scheme.Modules.pullback f').map (omegaBase h) ≫
        omegaBase h').app W (pullbackSections (f' ≫ f) _ hW' s) =
      (omegaBase h').app W (pullbackSections f' _ hW ((omegaBase h).app V (pullbackSections f _ hV s))) := by
    rw [← QCoh.app_app, ← QCoh.app_app, Vert.DivPull.pullbackComp_inv_app f' f _ hV hW]
    exact congrArg _ (QCoh.pullback_map_app_pullbackSections f' _ _ _)
  have : (Scheme.Modules.pullbackComp f' f).inv.app (omega G) ≫ (Scheme.Modules.pullback f').map (omegaBase h) ≫
      omegaBase h' = omegaBase h'' := by
    refine pullback_hom_ext (sec_hom η[G]) fun W a => ?_
    have k₁ := le_of_sq (unitSec_comp h) (le_refl (unitSec G ⁻¹ᵁ W)) le_rfl
    have k₂ := le_of_sq (unitSec_comp h') k₁ le_rfl
    refine (k le_rfl le_rfl le_rfl (dUnit G le_rfl a)).trans ?_
    rw [omegaBase_dUnit h le_rfl le_rfl k₁ le_rfl, omegaBase_dUnit h' k₁ le_rfl k₂ le_rfl]
    exact (congrArg _ (appLE_appLE rfl _ _ le_rfl a)).trans (omegaBase_dUnit h'' le_rfl le_rfl k₂ le_rfl a).symm
  rw [← this, k hV hW]

variable {k : Type} [CommRing k] {C : Scheme.{0}} {G : Over C} [GrpObj G] {x : Sp k ⟶ C} {B : Over (Sp k)} [GrpObj B]
  {ψ : B.left ⟶ G.left}

end Tangent

section Pairing

open GlobalTheory.Published.AbelianDeRham (bcMor)

end Pairing

open GlobalTheory.DeRhamSheaf (onAff)
open GlobalTheory.Published.AbelianDeRham (bcMor)
open GlobalTheory.DualPull (theta dualApp_theta)


end GlobalTheory.BadPt.Fibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedKernelLeThetaFunctionRouteBigVertex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedKernelLeThetaFunctionRouteBigVertex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.ZConvIdent
open GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem conjU_mul {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) (g k : GA D V) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h (g * k) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h k := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_mul]

theorem thetaSum_finset_sum {F : Type} [Field F] [NumberField F] {κ ι : Type} [Fintype κ] (s : Finset ι)
    (f : ι → (κ → AdeleRing (𝓞 F) F) → ℂ) (hf : ∀ k ∈ s, f k ∈ schA F κ) :
    thetaSum F (∑ k ∈ s, f k) = ∑ k ∈ s, thetaSum F (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      thetaSum_add F (hf a (Finset.mem_insert_self a s)) (Submodule.sum_mem _ fun k hk => hf k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]

theorem translates_kerSmall_le_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ (z : GA D (G.V (.grid i j)) →₀ ℂ) (Φ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank +
        (G.V (.grid i j)).rank) → AF D.host.F) → ℂ) (a : GA D (G.V (.grid i j)) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB Γ.V'.J) (C₀ : ℝ),
      zdeg z ≠ 0 ∧ Φ ∈ Γ.M'.So Bs.ψ Bs.τ₁ ∧
      ∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
        C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁))‖ := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ΦB, hB, z, hz, hS⟩ := GlobalTheory.T.exists_routeDatum_translationCombination_goodPlace hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ξ, hξ, hk⟩ := GlobalTheory.T.small_route_kernel_eq_unit_norm_mul_theta hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv ΦB hB
  refine ⟨z, _, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁, 1, hz, hS, fun g u => le_of_eq ?_⟩
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have hpres : ∀ p φ, φ ∈ schA D.host.F _ → om' p φ ∈ schA D.host.F _ := fun p φ hφ => hW.pres p φ hφ
  have hB0 := hB.1
  set a := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁
  set hh := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)
  have ha : ∀ x y, a (x * y) = a x * a y := conjU_mul _ _ _
  have e1 : translates z (kerSmall W Θ' g g₁) u =
      ξ (g, g₁) * z.sum fun k c => c * thetaSum D.host.F (om' (a u, hh) (om' (a k, 1) ΦB)) := by
    rw [translates, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [hk, ha, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    ring
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' (z.sum fun k c => c • om' (a k, 1) ΦB) (a u) hh =
      z.sum fun k c => c * thetaSum D.host.F (om' (a u, hh) (om' (a k, 1) ΦB)) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_finsuppSum, Finsupp.sum, thetaSum_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, thetaSum_smul]
    · intro k _
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hpres _ _ (hpres _ _ hB0))
  rw [e1, e2, norm_mul, hξ, one_mul]

end GlobalTheory.ZConvIdent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedKernelLeThetaFunctionRouteBigVertexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedKernel_le_thetaFunction_routeBigVertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ (z : GA D (G.V (.grid i j)) →₀ ℂ) (Φ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank +
        (G.V (.grid i j)).rank) → AF D.host.F) → ℂ) (a : GA D (G.V (.grid i j)) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB Γ.V'.J) (C₀ : ℝ),
      zdeg z ≠ 0 ∧ Φ ∈ Γ.M'.So Bs.ψ Bs.τ₁ ∧
      ∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
        C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁))‖ := by
  first | exact @GlobalTheory.ZConvIdent.translates_kerSmall_le_theta | exact GlobalTheory.ZConvIdent.translates_kerSmall_le_theta | (intros; apply GlobalTheory.ZConvIdent.translates_kerSmall_le_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundary
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartAbLocus

theorem mem_abLocus_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m d))), SABMap t Y.t (ξ ≫ genι Y) → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal := by
  intro E _ _ _ H Dw l Xo c Y k _ m d ξ t φ hbd p
  rw [← hbd, mem_genBd_iff, not_not, ← abLocus_pullback abLocusOne Y.t.semi φ.cart.1 p]
  rfl

end GlobalTheory.ChartAbLocus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundaryStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_abelianLocus_toricChart_iff_not_mem_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m d))), SABMap t Y.t (ξ ≫ genι Y) → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal := by
  first | exact @GlobalTheory.ChartAbLocus.mem_abLocus_iff | exact GlobalTheory.ChartAbLocus.mem_abLocus_iff | (intros; apply GlobalTheory.ChartAbLocus.mem_abLocus_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAddEpsMulOnDualNumberThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAddEpsMulOnDualNumberThickening
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EpsThick

theorem existsUnique_add_eps_mul_of_field : ∀ (k : Type) [Field k] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp k) (π : Y' ⟶ Sp (DualNumber k)) (ρ : Y' ⟶ Y), IsPullback ρ π q (spMap (algebraMap k (DualNumber k))) → ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro k _ Y Y' q π ρ H O F
  obtain ⟨ab, hab⟩ := comb_surjective H O F
  exact ⟨ab, hab.symm, fun y hy => comb_injective H O (hy.symm.trans hab.symm)⟩

end GlobalTheory.EpsThick
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAddEpsMulOnDualNumberThickeningStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_add_eps_mul_on_dualNumber_thickening : ∀ (k : Type) [Field k] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp k) (π : Y' ⟶ Sp (DualNumber k)) (ρ : Y' ⟶ Y), IsPullback ρ π q (spMap (algebraMap k (DualNumber k))) → ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  first | exact @GlobalTheory.EpsThick.existsUnique_add_eps_mul_of_field | exact GlobalTheory.EpsThick.existsUnique_add_eps_mul_of_field | (intros; apply GlobalTheory.EpsThick.existsUnique_add_eps_mul_of_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalars
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalars
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem scalar_pullback_spec_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of A)) (x y : A) :
    scal p (x * y) = scal p x * scal p y := by
  unfold scal; rw [map_mul, map_mul]

theorem Trait.exp_mul_left : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b c : W), T.Exp a b s F → T.Exp (c * a) (c * b) s F := by
  intro R _ _ _ D C W _ _ _ T k s F a b c ⟨σ, ⟨σ', f', hC, hP, hE⟩, hs⟩
  refine ⟨DVR.SecOps.secScale (scal T.G.hom c) σ, ⟨σ', f', ?_, hP, hE⟩, ?_⟩
  · intro Z r z J J' hJ hJ'
    rw [GlobalTheory.IntegralFamTriple.sval_secScale _ _ _ _ hJ, hC Z r z J J' hJ hJ', scalar_pullback_spec_mul, gs_mul _ z ⊤ trivial]
    ring
  · intro Z p p' hp z J hJ
    rw [GlobalTheory.IntegralFamTriple.sval_secScale _ _ _ _ hJ, hs Z p p' hp z J hJ, scalar_pullback_spec_mul, gs_mul _ z ⊤ trivial]
    ring

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalarsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverTrait_expansion_scale_both_scalars : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b c : W), T.Exp a b s F → T.Exp (c * a) (c * b) s F := by
  first | exact @GlobalTheory.Mum.Trait.exp_mul_left | exact GlobalTheory.Mum.Trait.exp_mul_left | (intros; apply GlobalTheory.Mum.Trait.exp_mul_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfToricChartToGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfToricChartToGenericFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem charZero_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y), CharZero k := by
  intro E _ _ _ H Dw l Xo c Y k _ m d ξ
  have : CharZero (ChartRing k m d) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  exact (algebraMap k (ChartRing k m d)).charZero_iff (RingHom.injective _) |>.2 this

end GlobalTheory.LocReg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfToricChartToGenericFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charZero_of_toricChart_to_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y), CharZero k := by
  first | exact @GlobalTheory.LocReg.charZero_of_chart | exact GlobalTheory.LocReg.charZero_of_chart | (intros; apply GlobalTheory.LocReg.charZero_of_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMa
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMa
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocReg

theorem comp_genι_eq_spMap_chartHom (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) :
    ξ ≫ genι Y = spMap (GlobalTheory.LocReg.chartHom Y U ξ hx) ≫ chart U := by
  have hx' : (ξ ≫ genι Y) (closedPoint (ChartRing k m d)) ∈ U.1 := hx
  have e1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (ξ ≫ genι Y)
  have e2 : Y.X.fromSpecStalk ((ξ ≫ genι Y) (closedPoint (ChartRing k m d))) =
      Spec.map (Y.X.presheaf.germ U.1 _ hx') ≫ U.2.fromSpec :=
    (U.2.fromSpecStalk_eq_fromSpecStalk hx').symm
  rw [e2, ← Spec.map_comp_assoc, Scheme.stalkClosedPointTo_comp] at e1
  rw [← e1, chart]
  congr 2
  exact (Scheme.Hom.germ_stalkMap_assoc (genι Y) U.1 (ξ (closedPoint _)) hx (Scheme.stalkClosedPointTo ξ)).trans rfl

end GlobalTheory.LocReg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricChart_comp_genericFibreInclusion_eq_spec_chartMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), ξ ≫ genι Y = spMap (GlobalTheory.LocReg.chartHom Y U ξ hx) ≫ chart U := by
  first | exact @GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom | exact GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom | (intros; apply GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom <;> assumption)
end
end
