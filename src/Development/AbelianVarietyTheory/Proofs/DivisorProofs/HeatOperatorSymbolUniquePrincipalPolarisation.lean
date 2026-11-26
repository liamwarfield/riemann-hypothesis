module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationValueSpacesGenericPointDictionary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSecondOrderSymbolVanishesOfPolarisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSymbolZeroOfBracketPreserving
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreInvariantVectorFieldsAtGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreInvariantVectorFieldsAtGenericPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFields

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => by ext <;> simp [dualMap]

theorem dualMapR_eq {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : Chart.dualMapR f = dualMap f :=
  RingHom.ext fun z => by ext <;> simp [dualMap, Chart.dualMapR]

theorem one_left {S : Scheme.{0}} (X G : Over S) [GrpObj G] : (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  rw [Hom.one_def]; rfl

theorem red_of_isTr {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]
    {φ : R →+* S} {g : Sp S ⟶ G.left} {v : TanM (𝟙 (Sp R)) G} {w : Sp (DualNumber S) ⟶ G.left}
    (hg : g ≫ G.hom = spMap φ) (h : IsTr G φ g v w) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g := by
  obtain ⟨g', v', h₁, h₂, rfl⟩ := h
  have e0 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [sp_comp]
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact Spec.map_id _
  let red : Over.mk (g ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      change _ ≫ spMap (algebraMap S (DualNumber S)) ≫ g ≫ G.hom = g ≫ G.hom
      rw [← Category.assoc, e0, Category.id_comp])
  have ef : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap φ) = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    exact RingHom.ext fun z => by simp [dualMap]
  have hv : red ≫ v' = 1 := by
    apply Over.OverMorphism.ext
    have hr := congrArg (fun q => q.left) (GlobalTheory.InvFieldBase.redPt_tv G v)
    simp only [Over.comp_left] at hr
    rw [Over.comp_left, one_left, h₂, ← Category.assoc]
    change (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) ≫ _ = _
    rw [sp_comp, ef, ← sp_comp, Category.assoc]
    change spMap φ ≫ ((GlobalTheory.InvFieldBase.redPt R).left ≫ (tv v).left) = _
    rw [hr, one_left]
    change spMap φ ≫ 𝟙 _ ≫ _ = (g ≫ G.hom) ≫ _
    rw [Category.id_comp, hg]
  have k := congrArg (fun q => q.left) (MonObj.comp_mul red g' v')
  simp only [hv, _root_.mul_one, Over.comp_left] at k
  change red.left ≫ _ = g
  rw [k, h₁, ← Category.assoc]
  change (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S))) ≫ g = g
  rw [e0, Category.id_comp]

theorem isTr_push {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left)
    (hm : IsGrpPullback A G (spMap x₀) m) (w₀ : TanM (𝟙 (Sp R)) G) (v : TanM (𝟙 (Sp K)) A)
    (hv : (tv v).left ≫ m = spMap (dualMap x₀) ≫ (tv w₀).left) {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (y : Sp (DualNumber B) ⟶ A.left) (hy : IsTr A φ x v y) :
    IsTr G (φ.comp x₀) (x ≫ m) w₀ (y ≫ m) := by
  obtain ⟨g', v', h₁, h₂, rfl⟩ := hy
  obtain ⟨p, q, hp, hq, hpq⟩ := GlobalTheory.CechKS.exists_mul_of_isGrpPullback hm (tEpsG (x ≫ A.hom)) g' v'
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ G.hom) (by
      change _ = (spMap (algebraMap B (DualNumber B)) ≫ x ≫ A.hom) ≫ spMap x₀
      rw [Category.assoc x m, hm.1.w]
      simp only [Category.assoc])
  refine ⟨p, q, ?_, ?_, hpq⟩
  · simp only [hp, h₁, Category.assoc]
  · rw [hq, h₂, Category.assoc (spMap (dualMap φ)), hv, ← Category.assoc, sp_comp, dualMap_comp]

def epsOf {L : Type} [CommRing L] (D : L → L) (h1 : D 1 = 0) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = x * D y + y * D x) : L →+* DualNumber L where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (D s)
  map_one' := by ext <;> simp [h1]
  map_zero' := by
    have h0 : D 0 = 0 := by have := ha 0 0; simp at this; exact this
    ext <;> simp [h0]
  map_add' a b := by ext <;> simp [ha]
  map_mul' a b := by ext <;> simp [hm]; ring

theorem eq_of_isTr {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {v : TanM (𝟙 (Sp R)) G} {dd : Fld G.left} (hd : IsInv G v dd) {L : Type} [CommRing L] (φ : R →+* L)
    (y : Sp L ⟶ G.left) (hy : y ≫ G.hom = spMap φ) (D : L → L) (h1 : D 1 = 0) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = x * D y + y * D x) (U : G.left.Opens) (hU : IsAffineOpen U)
    (hyU : ⊤ ≤ y ⁻¹ᵁ U) (hD : ∀ f, valR y U (dd U f) = D (valR y U f)) {w : Sp (DualNumber L) ⟶ G.left}
    (hw : IsTr G φ y v w) : w = spMap (epsOf D h1 ha hm) ≫ y := by
  have r1 := red_of_isTr hy hw
  have e1 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ spMap (epsOf D h1 ha hm) = 𝟙 _ := by
    rw [sp_comp]
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (epsOf D h1 ha hm) = RingHom.id L := by
      ext r; simp [epsOf]
    rw [this]; exact Spec.map_id _
  have r2 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ (spMap (epsOf D h1 ha hm) ≫ y) = y := by
    rw [← Category.assoc, e1, Category.id_comp]
  have hwU := GlobalTheory.CechKS.le_preimage_of_red r1 hyU
  refine GlobalTheory.Points.ext_of_valR hU hwU (GlobalTheory.CechKS.le_preimage_of_red r2 hyU) fun f => ?_
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hyU]
  have h0 := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom L L L).toRingHom w U hwU f
  rw [r1] at h0
  ext
  · rw [h0]; simp [epsOf]
  · rw [hd.2 L φ y w U f hy hyU hw, hD]; simp [epsOf]

theorem exists_affine {Ω : Type} [CommRing Ω] [IsLocalRing Ω] {X : Scheme.{0}} (x : Sp Ω ⟶ X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show x.base (IsLocalRing.closedPoint Ω) ∈ (⊤ : X.Opens) from trivial)
  refine ⟨U, hU, fun p _ => ?_⟩
  exact ((IsLocalRing.specializes_closedPoint (R := Ω) p).map x.base.hom.continuous).mem_open U.isOpen hx

theorem exists_basis_bc {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left)
    (hm : IsGrpPullback A G (spMap x₀) m) (hs : Smooth G.hom) {n : ℕ}
    (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) :
    ∃ v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) A),
      ∀ a, (tv (v a)).left ≫ m = spMap (dualMap x₀) ≫ (tv (v' a)).left := by
  obtain ⟨u', hu', hu'l⟩ := GlobalTheory.Heat.CoeffWt.exists_isLieBasis v'
  obtain ⟨u, hu, hul⟩ := GlobalTheory.exists_isLieBasis_baseChange R K x₀ G A m hm hs n u' hu'
  have h := GlobalTheory.Heat.CoeffWt.isGrpPullback_self A
  let b : Fin n → TanM (𝟙 (Sp K)) A := fun j =>
    PullbackSections.mkT (pushHom h (epsR K) (u j)) ((PullbackSections.isTangent_iff h _).1 (hu.1 j))
  have ts : ∀ f : Fin n → TanM (𝟙 (Sp K)) A, tv (∑ i, f i) = ∏ i, tv (f i) := fun f => by
    simp [tv, toMul_sum]
  have hcomb : ∀ (c : Fin n → K) (w : epsR K ⟶ A), IsLieComb c u w ↔
      pushHom h (epsR K) w = tv (∑ i, c i • b i) := fun c w => by
    rw [PullbackSections.isLieComb_iff h, ts]
    rfl
  have hbij : Function.Bijective (Fintype.linearCombination K b) := by
    rw [Function.bijective_iff_existsUnique]
    intro W
    obtain ⟨p, hp⟩ := PullbackSections.push_surj h (tv W)
    have ht : IsTangent p := (PullbackSections.isTangent_iff h p).2 (by rw [hp]; exact PullbackSections.tv_mem W)
    refine (existsUnique_congr fun c => ?_).1 (hu.2 p ht)
    rw [hcomb, hp, Fintype.linearCombination_apply]
    exact ⟨fun e => (PullbackSections.tanM_ext e).symm, fun e => by rw [e]⟩
  refine ⟨(Pi.basisFun K (Fin n)).map (LinearEquiv.ofBijective _ hbij), fun a => ?_⟩
  have e : (Pi.basisFun K (Fin n)).map (LinearEquiv.ofBijective _ hbij) a = b a := by
    simp [Module.Basis.map_apply, Fintype.linearCombination_apply_single]
  rw [e]
  change ((u a).left ≫ 𝟙 _) ≫ m = _
  rw [Category.comp_id, hul a, hu'l a, dualMapR_eq]

theorem der_frac {R : Type} [CommRing R] [IsDomain R] {L : Type} [Field L] (ψ : FractionRing R →+* L)
    (D : L → L) (hl : ∀ x y, D (x * y) = x * D y + y * D x) (h : ∀ r, D (ψ (algebraMap R (FractionRing R) r)) = 0)
    (k : FractionRing R) :
    D (ψ k) = 0 := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  have hy0 : algebraMap R (FractionRing R) y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hψ0 : ψ (algebraMap R (FractionRing R) y) ≠ 0 := (map_ne_zero ψ).2 hy0
  have e : ψ (algebraMap R (FractionRing R) x / algebraMap R (FractionRing R) y) * ψ (algebraMap R (FractionRing R) y) =
      ψ (algebraMap R (FractionRing R) x) := by rw [← map_mul, div_mul_cancel₀ _ hy0]
  have k2 := congrArg D e
  rw [hl, h, h, mul_zero, zero_add] at k2
  exact (mul_eq_zero.1 k2).resolve_left hψ0

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (v : Module.Basis (Fin n) (FractionRing R) (TanM (𝟙 (Sp (FractionRing R))) P.A.A)) (dd : Fin n → Fld P.A.A.left), (∀ a, IsInv P.A.A (v a) (dd a)) ∧ ∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δL a (valR ξ O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx' hinv hδ hval _ g _ δL hδL ψ ξ
    hψ hξA hξ _
  have hm : IsGrpPullback P.A.A t.G (spMap (algebraMap R (FractionRing R)))
      (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  obtain ⟨v, hv⟩ := exists_basis_bc (algebraMap R (FractionRing R)) t.G P.A.A _ hm t.semi.smooth v'
  choose dd hdd using fun a => GlobalTheory.InvFieldBase.exists_isInv (FractionRing R) P.A.A (v a)
  refine ⟨v, dd, hdd, fun a O f hO => ?_⟩
  obtain ⟨U, hU, hxU⟩ := exists_affine x'
  have hyU : ⊤ ≤ (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ⁻¹ᵁ U := by
    rw [hξ]
    exact fun p _ => hxU (Set.mem_univ ((spMap (algebraMap Ω (FractionRing Ω))).base p))
  have hyG : (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ≫ t.G.hom =
      spMap (ψ.comp (algebraMap R (FractionRing R))) := by
    rw [Category.assoc, hm.1.w, ← Category.assoc, hξA, sp_comp]
  have hl : ∀ x y, δL a (x * y) = x * δL a y + y * δL a x := fun x y => by
    rw [(δL a).leibniz, smul_eq_mul, smul_eq_mul]
  have hDy : ∀ f, valR (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) U (dd' a U f) =
      δL a (valR (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) U f) := by
    intro f
    rw [hξ, GlobalTheory.Points.valR_spMap_comp _ _ _ hxU, GlobalTheory.Points.valR_spMap_comp _ _ _ hxU, hval a U _ hxU, hδL]
  have hc : ∀ k, δL a (ψ k) = 0 := der_frac ψ (δL a) hl fun r => by rw [hψ, hδL, hδ, map_zero]
  have hdual : (dualMap ψ).comp (algebraMap (FractionRing R) (DualNumber (FractionRing R))) =
      (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))).comp ψ := by
    ext k <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let g' : tEpsG (ξ ≫ P.A.A.hom) ⟶ P.A.A :=
    Over.homMk (spMap (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))) ≫ ξ) (Category.assoc _ _ _)
  let w' : tEpsG (ξ ≫ P.A.A.hom) ⟶ P.A.A :=
    Over.homMk (spMap (dualMap ψ) ≫ (tv (v a)).left) (by
      rw [Category.assoc, Over.w (tv (v a)), hξA]
      change spMap (dualMap ψ) ≫ spMap (algebraMap _ _) ≫ 𝟙 _ = spMap _ ≫ spMap ψ
      rw [Category.comp_id, sp_comp, sp_comp, hdual])
  have htr : IsTr P.A.A ψ ξ (v a) (g' * w').left := ⟨g', w', rfl, rfl, rfl⟩
  have key : (g' * w').left = spMap (epsOf (δL a) (δL a).map_one_eq_zero (map_add _) hl) ≫ ξ := by
    refine hm.1.hom_ext ?_ ?_
    · rw [eq_of_isTr (hinv a) _ _ hyG (δL a) (δL a).map_one_eq_zero (map_add _) hl U hU hyU hDy
        (isTr_push _ _ hm (v' a) (v a) (hv a) ψ ξ _ htr), Category.assoc]
    · rw [Over.w (g' * w')]
      change spMap (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))) ≫ ξ ≫ P.A.A.hom =
        (spMap _ ≫ ξ) ≫ P.A.A.hom
      rw [Category.assoc, hξA, sp_comp, sp_comp]
      congr 1
      ext k
      · simp [epsOf, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [epsOf, TrivSqZeroExt.algebraMap_eq_inl, hc]
  rw [← (hdd a).2 (FractionRing Ω) ψ ξ _ O f hξA hO htr, key, GlobalTheory.Points.valR_spMap_comp _ _ _ hO]
  simp [epsOf]

end GlobalTheory.GenFields
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreInvariantVectorFieldsAtGenericPointStatement
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
theorem _root_.GlobalTheory.T.generic_fibre_invariant_vectorFields_at_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (v : Module.Basis (Fin n) (FractionRing R) (TanM (𝟙 (Sp (FractionRing R))) P.A.A)) (dd : Fin n → Fld P.A.A.left), (∀ a, IsInv P.A.A (v a) (dd a)) ∧ ∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δL a (valR ξ O f) := by
  first | exact @GlobalTheory.GenFields.main | exact GlobalTheory.GenFields.main | (intros; apply GlobalTheory.GenFields.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointAbelianVarietyThroughFormalPoi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointAbelianVarietyThroughFormalPoi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifGenPoint

theorem valR_constFn {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (p : X ⟶ Sp B) (x : Sp A ⟶ X)
    (χ : B →+* A) (hx : x ≫ p = spMap χ) (a : B) : valR x ⊤ (constFn p ⊤ a) = χ a := by
  have h : ⊤ ≤ x ⁻¹ᵁ (⊤ : X.Opens) := fun _ _ => trivial
  unfold constFn
  refine (GlobalTheory.ZH.CrdMove.valR_appLE x p ⊤ ⊤ _ h _).trans ?_
  rw [hx]
  have h' : ⊤ ≤ (spMap χ) ⁻¹ᵁ (⊤ : (Sp B).Opens) := fun _ _ => trivial
  rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ h']
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a)) n
  refine Eq.trans ?_ (this.trans (congrArg χ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv_hom_id_apply a)))
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end GlobalTheory.UnifGenPoint


open GlobalTheory.UnifGenPoint in
theorem GlobalTheory.UnifGenPoint.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) ∧ ξ ≫ P.A.A.hom = spMap ψ ∧ ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' ∧ ∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0 := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx _ _ _ hinj g _ δL _

  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun r hr => ?_
    have h1 : valR x' ⊤ (constFn t.G.hom ⊤ r) = 0 := (valR_constFn t.G.hom x' φ hx r).trans hr
    have h2 := hinj ⊤ (constFn t.G.hom ⊤ r) (fun _ _ => trivial) h1
    have h3 := valR_constFn t.G.hom (eSec t.G) (RingHom.id R) (by
      rw [eSec, Over.w]; simp [spMap]) r
    rw [h2, GlobalTheory.ZH.CrdCalc.valR_eq (eSec t.G) ⊤ (fun _ _ => trivial), map_zero] at h3
    exact h3.symm

  set L := FractionRing Ω
  have hinjL : Function.Injective ((algebraMap Ω L).comp φ) :=
    (IsFractionRing.injective Ω L).comp hφ
  let ψ : FractionRing R →+* L := IsFractionRing.lift (K := FractionRing R) hinjL
  have hψ : ∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω L (φ r) := fun r => by
    simp [ψ, IsFractionRing.lift_algebraMap]
  let u : Sp L ⟶ t.G.left := spMap (algebraMap Ω L) ≫ x'
  have hu : u ≫ t.G.hom = spMap ψ ≫ jK R := by
    simp only [u, Category.assoc, hx, spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => (hψ r).symm
  let ξ₀ : Sp L ⟶ pullback t.G.hom (jK R) := pullback.lift u (spMap ψ) hu
  let ξ : Sp L ⟶ P.A.A.left := ξ₀ ≫ P.U.gen.hom.left
  have n₁ : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.hom_inv_id, Over.id_left]
  have hξ1 : ξ ≫ P.A.A.hom = spMap ψ := by
    simp only [ξ, Category.assoc, Over.w]
    exact pullback.lift_snd _ _ _
  have hξ2 : ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = u := by
    simp only [ξ, Category.assoc]
    rw [← Category.assoc P.U.gen.hom.left, n₁, Category.id_comp]
    exact pullback.lift_fst _ _ _
  refine ⟨ψ, ξ, hψ, hξ1, hξ2, ?_⟩

  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : GeometricallyConnected t.G.hom := t.semi.geomConnected
  haveI : IrreducibleSpace t.G.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R t.G inferInstance inferInstance
      ⟨x' (IsLocalRing.closedPoint Ω)⟩
  set q := u (IsLocalRing.closedPoint L) with hq
  have hqg : q = genericPoint t.G.left := by
    have h1 : q ⤳ genericPoint t.G.left := by
      refine specializes_iff_forall_open.2 fun s hs hgs => ?_
      obtain ⟨V, hVa, hpV, -⟩ := exists_isAffineOpen_mem_and_subset
        (U := ⊤) (x := x' (IsLocalRing.closedPoint Ω)) trivial
      have hV : ⊤ ≤ x' ⁻¹ᵁ V := (GlobalTheory.ZH.CrdCalc.top_le_iff x' V).2 hpV
      have hgV : genericPoint t.G.left ∈ V :=
        ((genericPoint_spec t.G.left).mem_open_set_iff V.isOpen).2 ⟨_, trivial, hpV⟩
      let W : t.G.left.Opens := V ⊓ ⟨s, hs⟩
      obtain ⟨b, hbW, hgb⟩ := hVa.exists_basicOpen_le (V := W) ⟨genericPoint t.G.left, hgV, hgs⟩ hgV
      have hb : b ≠ 0 := by
        rintro rfl
        rw [Scheme.basicOpen_zero] at hgb
        exact hgb
      have hv : valR x' V b ≠ 0 := fun h => hb (hinj V b hV h)
      obtain ⟨hV', hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω L) x' V hV
      have hu : IsUnit (valR u V b) := by
        rw [hval]
        exact (Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective Ω L)).2 hv))
      have := ((GlobalTheory.ZH.CrdCalc.isUnit_valR_iff u V hV' b).1 hu) (Set.mem_univ (IsLocalRing.closedPoint L))
      exact (hbW this).2
    exact (h1.antisymm (genericPoint_specializes q)).eq

  haveI : Smooth P.A.A.hom := P.A.isAb.smooth
  haveI : GeometricallyConnected P.A.A.hom := P.A.isAb.geomConnected
  haveI : IrreducibleSpace P.A.A.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain (FractionRing R) P.A.A inferInstance
      inferInstance ⟨ξ (IsLocalRing.closedPoint L)⟩
  haveI : IsIntegral P.A.A.left := GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace P.A.A.hom
  set y := ξ (IsLocalRing.closedPoint L) with hy
  let mm : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)
  haveI : IsIso P.U.gen.inv.left := ⟨⟨P.U.gen.hom.left, by
    rw [← Over.comp_left, P.U.gen.inv_hom_id, Over.id_left], n₁⟩⟩
  haveI : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  haveI : IsPreimmersion (pullback.fst t.G.hom (jK R)) := MorphismProperty.of_isPullback (IsPullback.of_hasPullback t.G.hom (jK R)).flip inferInstance
  haveI : IsPreimmersion mm := inferInstance
  have hmy : mm y = q := by
    rw [hq, ← hξ2]
    rfl
  have hyg : y = genericPoint P.A.A.left := by
    apply (Scheme.Hom.isEmbedding mm).injective
    have h1 : mm (genericPoint P.A.A.left) ⤳ mm y :=
      (genericPoint_specializes y).map (Scheme.Hom.continuous mm)
    rw [hmy, hqg] at h1 ⊢
    exact ((genericPoint_specializes _).antisymm h1).eq
  intro O f hO hf
  by_contra hne
  have hne' : P.A.A.left.basicOpen f ≠ ⊥ := fun h => hne ((basicOpen_eq_bot_iff f).1 h)
  have hgen : genericPoint P.A.A.left ∈ P.A.A.left.basicOpen f := by
    refine ((genericPoint_spec P.A.A.left).mem_open_set_iff (P.A.A.left.basicOpen f).isOpen).2 ?_
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne'
    exact ⟨z, trivial, hz⟩
  have hu : IsUnit (valR ξ O f) :=
    (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff ξ O hO f).2
      ((GlobalTheory.ZH.CrdCalc.top_le_iff ξ _).2 (by rw [← hy, hyg]; exact hgen))
  exact hu.ne_zero hf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointAbelianVarietyThroughFormalPoiStatement
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
theorem _root_.GlobalTheory.T.exists_genericPoint_abelianVariety_through_formalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) ∧ ξ ≫ P.A.A.hom = spMap ψ ∧ ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' ∧ ∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0 := by
  first | exact @GlobalTheory.UnifGenPoint.main | exact GlobalTheory.UnifGenPoint.main | (intros; apply GlobalTheory.UnifGenPoint.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondOrderSymbolBracketRescaleByUnitPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondOrderSymbolBracketRescaleByUnitPow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem bracket_symbol_rescale_twist : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (q b c : FractionRing Ω) (k : ℕ), q ≠ 0 → (k : FractionRing Ω) * (q ^ k * b) * ((q ^ k * b) * δ₀ (q ^ k * c) - (q ^ k * c) * δ₀ (q ^ k * b)) - ∑ a, ∑ e, Λ a e * δL a (q ^ k * b) * ((q ^ k * b) * δL e (q ^ k * c) - (q ^ k * c) * δL e (q ^ k * b)) = q ^ (3 * k) * ((k : FractionRing Ω) * b * (b * (δ₀ c - ∑ a, ∑ e, Λ a e * δL a q / q * δL e c) - c * (δ₀ b - ∑ a, ∑ e, Λ a e * δL a q / q * δL e b)) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
  intro Ω _ _ n δ₀ δL Λ q b c k hq
  have hpow : ∀ (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (x : FractionRing Ω),
      d (q ^ k * x) = q ^ k * (d x + (k : FractionRing Ω) * x * (d q / q)) := by
    intro d x
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    cases k with
    | zero => simp
    | succ k =>
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      field_simp
      ring
  have hbr : ∀ d : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      (q ^ k * b) * d (q ^ k * c) - (q ^ k * c) * d (q ^ k * b)
        = q ^ k * q ^ k * (b * d c - c * d b) := by
    intro d
    rw [hpow d b, hpow d c]
    ring
  have h3 : q ^ (3 * k) = q ^ k * q ^ k * q ^ k := by ring
  simp only [hbr]
  simp only [hpow _ b]
  have hs : ∑ a, ∑ e, Λ a e * (q ^ k * (δL a b + (k : FractionRing Ω) * b * (δL a q / q))) *
        (q ^ k * q ^ k * (b * δL e c - c * δL e b))
      = q ^ k * q ^ k * q ^ k * ((k : FractionRing Ω) * b *
          (b * (∑ a, ∑ e, Λ a e * δL a q / q * δL e c)
            - c * (∑ a, ∑ e, Λ a e * δL a q / q * δL e b))
          + ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hs, h3]
  ring

end GlobalTheory.Heat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondOrderSymbolBracketRescaleByUnitPowStatement
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
theorem _root_.GlobalTheory.T.secondOrderSymbol_bracket_rescale_by_unit_pow : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (q b c : FractionRing Ω) (k : ℕ), q ≠ 0 → (k : FractionRing Ω) * (q ^ k * b) * ((q ^ k * b) * δ₀ (q ^ k * c) - (q ^ k * c) * δ₀ (q ^ k * b)) - ∑ a, ∑ e, Λ a e * δL a (q ^ k * b) * ((q ^ k * b) * δL e (q ^ k * c) - (q ^ k * c) * δL e (q ^ k * b)) = q ^ (3 * k) * ((k : FractionRing Ω) * b * (b * (δ₀ c - ∑ a, ∑ e, Λ a e * δL a q / q * δL e c) - c * (δ₀ b - ∑ a, ∑ e, Λ a e * δL a q / q * δL e b)) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
  first | exact @GlobalTheory.Heat.bracket_symbol_rescale_twist | exact GlobalTheory.Heat.bracket_symbol_rescale_twist | (intros; apply GlobalTheory.Heat.bracket_symbol_rescale_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSymbolZeroOfBracketPreserving
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

def GlobalTheory.HeatSym.derOfFun {F : Type} [Field F] (d : F → F) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = x * d y + y * d x) : Derivation ℤ F F :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' d hadd)) fun x y => by
    simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul]
    exact hmul x y

theorem GlobalTheory.HeatSym.derOfFun_apply {F : Type} [Field F] (d : F → F) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = x * d y + y * d x) (x : F) : GlobalTheory.HeatSym.derOfFun d hadd hmul x = d x := rfl

theorem GlobalTheory.HeatSym.vertical_symbol_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Λᵀ = Λ → (∀ r, δ₀ ((algebraMap Ω (FractionRing Ω)) (φ r)) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ b c : FractionRing Ω, GlobalTheory.HeatSym.VS φ t.PP.L x' g k b → GlobalTheory.HeatSym.VS φ t.PP.L x' g k c → GlobalTheory.HeatSym.VS φ t.PP.L x' g (3 * k) ((k : FractionRing Ω) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b))) → Λ = 0 := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hloc n v' D Ω _ _ _ φ x' δ dd' hcomp hx' hinv hδ hval
    hsep g hg δL hδL δ₀ Λ hΛ hδ₀ hbr

  obtain ⟨ψ, ξ, hψ, hξ, hξ', hξsep⟩ := GlobalTheory.T.exists_genericPoint_abelianVariety_through_formalPoint E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL
  obtain ⟨v, dd, hinv₂, hval₂⟩ := GlobalTheory.T.generic_fibre_invariant_vectorFields_at_generic_point E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL ψ ξ hψ hξ hξ' hξsep
  obtain ⟨j₀, q, hj₀, hq, hVS⟩ := GlobalTheory.T.polarisation_value_spaces_generic_point_dictionary E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL ψ ξ hψ hξ hξ' hξsep

  have hker : ∀ D' : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      (∀ r, D' (algebraMap Ω (FractionRing Ω) (φ r)) = 0) → ∀ s, D' (ψ s) = 0 := by
    intro D' hD' s
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective R s
    rw [map_div₀, hψ, hψ, Derivation.leibniz_div, hD', hD']
    simp
  have hδL₀ : ∀ a r, δL a (algebraMap Ω (FractionRing Ω) (φ r)) = 0 := by
    intro a r
    rw [hδL, hδ, map_zero]

  have hadd : ∀ x y : FractionRing Ω,
      (δ₀ (x + y) - ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x + y)) =
        (δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) + (δ₀ y - ∑ a, ∑ e, Λ a e * δL a q / q * δL e y) := by
    intro x y
    have : ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x + y) =
        ∑ a, ∑ e, Λ a e * δL a q / q * δL e x + ∑ a, ∑ e, Λ a e * δL a q / q * δL e y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_add (f := _), mul_add]
    rw [map_add (f := _), this]
    ring
  have hmul : ∀ x y : FractionRing Ω,
      (δ₀ (x * y) - ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x * y)) =
        x * (δ₀ y - ∑ a, ∑ e, Λ a e * δL a q / q * δL e y) + y * (δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) := by
    intro x y
    have : ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x * y) =
        x * ∑ a, ∑ e, Λ a e * δL a q / q * δL e y + y * ∑ a, ∑ e, Λ a e * δL a q / q * δL e x := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, this]
    ring
  let δ₁ := GlobalTheory.HeatSym.derOfFun (fun x => δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) hadd hmul
  have hδ₁ : ∀ x, δ₁ x = δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x := fun x =>
    GlobalTheory.HeatSym.derOfFun_apply _ hadd hmul x
  have hδ₁ψ : ∀ r, δ₁ (ψ r) = 0 := by
    intro r
    rw [hδ₁, hker δ₀ hδ₀ r]
    simp [hker (δL _) (hδL₀ _) r]
  have : CharZero R := algebraRat.charZero R
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))

  let δL' := fun a : Fin n =>
    GlobalTheory.HeatSym.derOfFun (δL a) (fun x y => map_add _ x y)
      (fun x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
  have hδL' : ∀ a x, δL' a x = δL a x := fun a x => GlobalTheory.HeatSym.derOfFun_apply _ _ _ x
  have hval₃ : ∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δL' a (valR ξ O f) := by
    intro a O f h
    rw [hδL']
    exact hval₂ a O f h

  refine GlobalTheory.T.verticalSecondOrderSymbol_vanishes_of_polarisation (FractionRing R) P.A n v dd hinv₂ (FractionRing Ω) ψ ξ hξ hξsep δL' hval₃ j₀ hj₀ δ₁ Λ hΛ
    hδ₁ψ ?_
  intro k hk σ τ
  have hb := (hVS k _ hk).2 ⟨σ, rfl⟩
  have hc := (hVS k _ hk).2 ⟨τ, rfl⟩
  have h3 := hbr k hk _ _ hb hc
  rw [GlobalTheory.T.secondOrderSymbol_bracket_rescale_by_unit_pow Ω n δ₀ δL Λ q _ _ k hq] at h3
  obtain ⟨ρ, hρ⟩ := (hVS (3 * k) _ (by omega)).1 h3
  refine ⟨ρ, ?_⟩
  rintro b c rfl rfl
  simp only [hδ₁, hδL']
  exact mul_left_cancel₀ (pow_ne_zero _ hq) hρ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSymbolZeroOfBracketPreservingStatement
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
theorem _root_.GlobalTheory.T.verticalSymbol_zero_of_bracket_preserving : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Λᵀ = Λ → (∀ r, δ₀ ((algebraMap Ω (FractionRing Ω)) (φ r)) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ b c : FractionRing Ω, GlobalTheory.HeatSym.VS φ t.PP.L x' g k b → GlobalTheory.HeatSym.VS φ t.PP.L x' g k c → GlobalTheory.HeatSym.VS φ t.PP.L x' g (3 * k) ((k : FractionRing Ω) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b))) → Λ = 0 := by
  first | exact @GlobalTheory.HeatSym.vertical_symbol_zero | exact GlobalTheory.HeatSym.vertical_symbol_zero | (intros; apply GlobalTheory.HeatSym.vertical_symbol_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOfScaledSectionValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOfScaledSectionValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatSym
open GlobalTheory.HeatMod

theorem VS.sub : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (p : Y ⟶ Sp R) (L : LB Y) (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)), x ≫ p = spMap φ → ∀ (k : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g k s' → GlobalTheory.HeatSym.VS φ L x g k (s - s') := by
  intro R Ω _ _ _ _ φ Y p L x g hxp k s s' ⟨r, σ, ω, hr, hv, he⟩ ⟨r', σ', ω', hr', hv', he'⟩
  refine ⟨r * r', constFn p ⊤ r' • σ - constFn p ⊤ r • σ', φ r' * ω - φ r * ω', mul_ne_zero hr hr', ?_, ?_⟩
  · intro Z t z J hJ
    have e : ∀ a : R, ((spMap φ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) =
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (φ a) := by
      intro a
      have := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
      exact this.symm
    have key : ∀ a : R, germConstHom ((t ≫ x) ≫ p) z a =
        gs t z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (φ a)) := by
      intro a
      rw [Category.assoc, hxp, gs_eq t z ⊤ trivial, ← e]; rfl
    have hm := hJ.mem (fun _ : Fin 1 => 𝟙 Y) (t ≫ x)
    have h2 : ∀ (a : R) (τ : SecM (𝟙 Y) L k), sval (constFn p ⊤ a • τ) (t ≫ x) z J =
        germConstHom ((t ≫ x) ≫ p) z a * sval τ (t ≫ x) z J := fun a τ =>
      (gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·)
        ((gs_res _ z le_top hm _).trans (gs_constFn_eq_germConstHom p _ z a)) rfl)
    rw [sval_sub_constFn_smul p _ _ r (t ≫ x) z hJ, h2, hv Z t z J hJ, hv' Z t z J hJ, key, key]
    simp only [gs_eq t z ⊤ trivial, map_sub, map_mul]
    ring
  · rw [map_sub, map_mul, map_mul, he, he', map_mul, map_mul]
    ring

end GlobalTheory.HeatSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOfScaledSectionValuesStatement
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
theorem _root_.GlobalTheory.T.sub_of_scaled_section_values : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (p : Y ⟶ Sp R) (L : LB Y) (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)), x ≫ p = spMap φ → ∀ (k : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g k s' → GlobalTheory.HeatSym.VS φ L x g k (s - s') := by
  first | exact @GlobalTheory.HeatSym.VS.sub | exact GlobalTheory.HeatSym.VS.sub | (intros; apply GlobalTheory.HeatSym.VS.sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfScaledSectionValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfScaledSectionValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

theorem VS.mul : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y), L.IsLB → ∀ (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k l : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g l s' → GlobalTheory.HeatSym.VS φ L x g (k + l) (s * s') := by
  intro R Ω _ _ _ φ Y L hL x g k l s s' h h'
  obtain ⟨r, σ, ω, hr, hv, he⟩ := h
  obtain ⟨r', σ', ω', hr', hv', he'⟩ := h'
  have hF : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 Y) (fun _ : Fin 1 => 𝟙 Y))
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) (fun _ : Fin 1 => (l : ℤ)))
      (fun _ : Fin 1 => 𝟙 Y) (fun _ => ((k + l : ℕ) : ℤ)) := by
    intro U _ f
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.prod_singleton]
    push_cast
    rw [zpow_add]
  obtain ⟨σ'', hσ''⟩ := exists_sec hL hF (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec σ σ')
  refine ⟨r * r', σ'', ω * ω', mul_ne_zero hr hr', ?_, ?_⟩
  · intro Z q z J hJ
    rw [hσ'' Z (q ≫ x) z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec σ σ' (q ≫ x) z hJ, hv Z q z J hJ, hv' Z q z J hJ,
      map_mul, gs_mul q z ⊤ trivial, pow_add, Units.val_mul]
    ring
  · rw [map_mul, map_mul, map_mul, he, he']
    ring

end GlobalTheory.HeatSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfScaledSectionValuesStatement
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
theorem _root_.GlobalTheory.T.mul_of_scaled_section_values : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y), L.IsLB → ∀ (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k l : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g l s' → GlobalTheory.HeatSym.VS φ L x g (k + l) (s * s') := by
  first | exact @GlobalTheory.HeatSym.VS.mul | exact GlobalTheory.HeatSym.VS.mul | (intros; apply GlobalTheory.HeatSym.VS.mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolUniquePrincipalPolarisation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

theorem symbol_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Λ₁ Λ₂ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (d₁ d₂ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u₁ u₂ : Fin n → (FractionRing Ω)) (p₁ p₁' p₂ p₂' : (FractionRing Ω)), Λ₁ᵀ = Λ₁ → Λ₂ᵀ = Λ₂ → (∀ r, d₁ ((algebraMap Ω (FractionRing Ω)) (φ r)) = d₂ ((algebraMap Ω (FractionRing Ω)) (φ r))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₁ (fun a => ⇑(δL a)) Λ₁ u₁ p₁ p₁' k s))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₂ (fun a => ⇑(δL a)) Λ₂ u₂ p₂ p₂' k s))) → Λ₁ = Λ₂ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab n v' D Ω _ _ _ φ x' δ dd' hcomp hx hinv hδ hval hinj g hg δL hδL
    Λ₁ Λ₂ d₁ d₂ u₁ u₂ p₁ p₁' p₂ p₂' hΛ₁ hΛ₂ hd h₁ h₂
  have sub := fun j s s' (hs : GlobalTheory.HeatSym.VS φ t.PP.L x' g j s) (hs' : GlobalTheory.HeatSym.VS φ t.PP.L x' g j s') =>
    GlobalTheory.T.sub_of_scaled_section_values φ t.G.hom t.PP.L x' g hx j s s' hs hs'
  have mul := fun j j' s s' (hs : GlobalTheory.HeatSym.VS φ t.PP.L x' g j s) (hs' : GlobalTheory.HeatSym.VS φ t.PP.L x' g j' s') =>
    GlobalTheory.T.mul_of_scaled_section_values φ t.PP.L t.PP.isLB x' g j j' s s' hs hs'
  have hQ : ∀ (j : ℕ), 1 ≤ j → ∀ s, GlobalTheory.HeatSym.VS φ t.PP.L x' g j s →
      GlobalTheory.HeatSym.VS φ t.PP.L x' g j (ringOp ⇑d₁ (fun a => ⇑(δL a)) Λ₁ u₁ p₁ p₁' j s -
        ringOp ⇑d₂ (fun a => ⇑(δL a)) Λ₂ u₂ p₂ p₂' j s) :=
    fun j hj s hs => sub j _ _ (h₁ j hj s hs) (h₂ j hj s hs)
  have hsym : (Λ₁ - Λ₂)ᵀ = Λ₁ - Λ₂ := by rw [Matrix.transpose_sub, hΛ₁, hΛ₂]
  have hcoe : (fun y => d₁ y - d₂ y) = ⇑(d₁ - d₂) := rfl
  refine sub_eq_zero.mp (GlobalTheory.T.verticalSymbol_zero_of_bracket_preserving E H R t P m tt gam hmon htt hab n v' D Ω φ x' δ dd' hcomp hx hinv hδ hval hinj g hg δL hδL
    (d₁ - d₂) (Λ₁ - Λ₂) hsym (fun r => by rw [Derivation.sub_apply, hd, sub_self]) ?_)
  intro k hk b c hb hc
  have hk2 : 1 ≤ k + k := le_add_right hk
  have hbc := hQ (k + k) hk2 _ (mul k k b c hb hc)
  have hbb := hQ (k + k) hk2 _ (mul k k b b hb hb)
  have hBc := sub _ _ _ (sub _ _ _ hbc (mul k k _ _ hb (hQ k hk c hc))) (mul k k _ _ hc (hQ k hk b hb))
  have hBb := sub _ _ _ (sub _ _ _ hbb (mul k k _ _ hb (hQ k hk b hb))) (mul k k _ _ hb (hQ k hk b hb))
  have hX := sub _ _ _ (mul k (k + k) _ _ hb hBc) (mul k (k + k) _ _ hc hBb)
  simp only [GlobalTheory.HeatSym.ringOp_sub, hcoe] at hX
  have key := GlobalTheory.HeatSym.bracket ⇑(d₁ - d₂) (fun a => ⇑(δL a))
    (fun x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
    (fun a x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
    (fun a x y => map_add _ x y) (Λ₁ - Λ₂) hsym (u₁ - u₂) (p₁ - p₂) (p₁' - p₂') k b c
  rw [key] at hX
  have e3 : 3 * k = k + (k + k) := by ring
  rw [e3]
  exact GlobalTheory.HeatSym.VS.half φ hX

end GlobalTheory.HeatSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolUniquePrincipalPolarisationStatement
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
theorem _root_.GlobalTheory.T.heatOperator_symbol_unique_principalPolarisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Λ₁ Λ₂ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (d₁ d₂ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u₁ u₂ : Fin n → (FractionRing Ω)) (p₁ p₁' p₂ p₂' : (FractionRing Ω)), Λ₁ᵀ = Λ₁ → Λ₂ᵀ = Λ₂ → (∀ r, d₁ ((algebraMap Ω (FractionRing Ω)) (φ r)) = d₂ ((algebraMap Ω (FractionRing Ω)) (φ r))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₁ (fun a => ⇑(δL a)) Λ₁ u₁ p₁ p₁' k s))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₂ (fun a => ⇑(δL a)) Λ₂ u₂ p₂ p₂' k s))) → Λ₁ = Λ₂ := by
  first | exact @GlobalTheory.HeatSym.symbol_unique | exact GlobalTheory.HeatSym.symbol_unique | (intros; apply GlobalTheory.HeatSym.symbol_unique <;> assumption)
end
