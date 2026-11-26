module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleOnCoverExtendsUpToCoboundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernRepresentativeContractionOfOrthogonal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackPrimitiveCrystallineClassEpsPartI
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackPrimitiveCrystallineClassEpsPartI
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem snd_epsHom {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z : DualNumber D) : (epsHom φ z).snd = φ z.snd := by
  simp only [epsHom, DualNumber.lift_apply_apply, AlgHom.comp_apply,
    TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_add, DualNumber.snd_mul,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, DualNumber.fst_eps, DualNumber.snd_eps,
    _root_.mul_one, mul_zero, add_zero, zero_add]

theorem epsHom_comp_inl {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ := by
  exact DualNumber.lift_comp_inlHom _

theorem epsHom_comp_epsMap {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' := by
  apply DualNumber.algHom_ext
  simp only [AlgHom.comp_apply, epsHom, EpsWeil.epsMap, DualNumber.lift_apply_eps]

theorem ptV_eq {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D]
    (x : Pt A D) : ptV v x =
      (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x : Pt (A ⊗ B) (DualNumber D)) *
      (spOver (EpsWeil.epsMap R D) ≫ CartesianMonoidalCategory.lift 1 v) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [ptV, pt0, MonObj.mul_comp, comp_lift, MonObj.comp_one]

theorem specOverOfAlgHom_comp_pointWithZeroSecondCoord {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {D D' : Type} [CommRing D] [Algebra R D] [CommRing D']
    [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    (spOver φ ≫ pt0 B x : Pt (A ⊗ B) D') = pt0 B (spOver φ ≫ x : Pt A D') := by
  simp [pt0, comp_lift]

theorem cohom_sndPull_zero : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (f : Z1 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) →
    ∀ v : epsR R ⟶ B, Cohom (whole A) (sndPull (fv f) v) (Fn1.zero A) := by
  intro R _ A B _ _ f hf v
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R (A ⊗ B) f hf
  have hc := (fv_isCoc_and_ev_eq R (A ⊗ B) f).1
  let V1 : Pt (A ⊗ B) (DualNumber R) := CartesianMonoidalCategory.lift 1 v
  refine ⟨fun D _ _ x ↦ (g (DualNumber D) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
      (spOver (EpsWeil.epsMap R D) ≫ V1) +
      fv f D (DualNumber D) (TrivSqZeroExt.inlAlgHom R D D) (pt0 B x) +
      fv f (DualNumber R) (DualNumber D) (EpsWeil.epsMap R D) V1).snd, ?_⟩
  intro D _ _ D' _ _ φ x _
  have e1 := hg (DualNumber D) (DualNumber D') (epsHom φ) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
    (spOver (EpsWeil.epsMap R D) ≫ V1)
  rw [← ptV_eq] at e1
  have hX : (spOver (epsHom φ) ≫ spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x :
      Pt (A ⊗ B) (DualNumber D')) =
      spOver (TrivSqZeroExt.inlAlgHom R D' D') ≫ pt0 B (spOver φ ≫ x : Pt A D') := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_inl, ← spOver_comp, Category.assoc, specOverOfAlgHom_comp_pointWithZeroSecondCoord]
  have hV : (spOver (epsHom φ) ≫ spOver (EpsWeil.epsMap R D) ≫ V1 :
      Pt (A ⊗ B) (DualNumber D')) = spOver (EpsWeil.epsMap R D') ≫ V1 := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_epsMap]
  rw [hX, hV] at e1
  have c1 := hc D (DualNumber D) (DualNumber D') (TrivSqZeroExt.inlAlgHom R D D) (epsHom φ) (pt0 B x)
    (sm_whole _)
  have c2 := hc D D' (DualNumber D') φ (TrivSqZeroExt.inlAlgHom R D' D') (pt0 B x) (sm_whole _)
  rw [epsHom_comp_inl, c2, specOverOfAlgHom_comp_pointWithZeroSecondCoord] at c1
  have c3 := hc (DualNumber R) (DualNumber D) (DualNumber D') (EpsWeil.epsMap R D) (epsHom φ) V1 (sm_whole _)
  rw [epsHom_comp_epsMap] at c3
  have s1 := congrArg TrivSqZeroExt.snd e1
  have s2 := congrArg TrivSqZeroExt.snd c1
  have s3 := congrArg TrivSqZeroExt.snd c3
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, snd_epsHom,
    TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_inl, zero_add] at s1 s2 s3
  simp only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, neg_zero, add_zero, TrivSqZeroExt.snd_add, map_add (f := _)]
  linear_combination -s1 - s2 - s3

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackPrimitiveCrystallineClassEpsPartIStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentPullback_primitiveCrystallineClass_epsPart_isCob : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (f : Z1 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) → ∀ v : epsR R ⟶ B, Cohom (whole A) (sndPull (fv f) v) (Fn1.zero A) := by
  first | exact @GlobalTheory.PtExt.cohom_sndPull_zero | exact GlobalTheory.PtExt.cohom_sndPull_zero | (intros; apply GlobalTheory.PtExt.cohom_sndPull_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocCocOf
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type}

abbrev SmallCat (W : K → X.left.Opens) : Type 1 := (IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).FullSubcategory

abbrev smallAt (W : K → X.left.Opens) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) (h : Sm W x) :
    SmallCat W := ⟨trivAt x, h⟩

theorem Sm.map {W : K → X.left.Opens} {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') {x : Pt X D} (h : Sm W x) : Sm W (D := D') (spOver φ ≫ x) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, (trivMap φ x).le_preimage hi⟩


open Classical in
def cocOf (W : K → X.left.Opens) (n : C1 ((IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _))) :
    Fn1 X := fun _ _ _ _ _ _ φ x ↦
  if h : Sm W x then n (smallAt W x h) (smallAt W _ (h.map φ)) (ObjectProperty.homMk (trivMap φ x)) else 0

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt
variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type}

private theorem thickHom_ext {T T' : Thick (dp0 R) (X.hom ≫ 𝟙 _)}
    {f g : Thick.Hom T T'} (h : ∀ b, f.φ b = g.φ b) : f = g := by
  rcases f with ⟨φ, φ₀, comm, dp, pt⟩
  rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
  obtain rfl : φ = ψ := AlgHom.ext h
  obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := T.surj c
    rw [comm, comm']
  rfl

theorem isCoc_cocOf (W : K → X.left.Opens)
    (n : C1 ((IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _)))
    (hn : ∀ (T T' T'' : SmallCat W) (a : T ⟶ T') (b : T' ⟶ T''), T.obj.J = ⊥ → T'.obj.J = ⊥ →
      T''.obj.J = ⊥ → d1 _ n T T' T'' a b = 0) : IsCoc W (cocOf W n) := by
  intro D _ _ D' _ _ D'' _ _ φ ψ x hx
  have tr : ∀ (y y' : Pt X D'') (e : y = y') (h : Sm W y) (h' : Sm W y')
      (f : smallAt W x hx ⟶ smallAt W y h) (f' : smallAt W x hx ⟶ smallAt W y' h'),
      (∀ r, f.hom.φ r = f'.hom.φ r) → n _ _ f = n _ _ f' := by
    rintro y _ rfl h h' f f' hf
    have : f = f' := ObjectProperty.hom_ext _ (thickHom_ext hf)
    subst this; rfl
  have key := hn (smallAt W x hx) (smallAt W _ (hx.map φ)) (smallAt W _ ((hx.map φ).map ψ))
    (ObjectProperty.homMk (trivMap φ x)) (ObjectProperty.homMk (trivMap ψ _)) rfl rfl rfl
  rw [d1_apply] at key
  simp only [cocOf, dite_eq_left hx, dite_eq_left (hx.map φ)]
  have e := tr (spOver (ψ.comp φ) ≫ x) (spOver ψ ≫ spOver φ ≫ x)
    (by rw [← spOver_comp, Category.assoc]) (hx.map (ψ.comp φ)) ((hx.map φ).map ψ)
    (ObjectProperty.homMk (trivMap (ψ.comp φ) x))
    ((ObjectProperty.homMk (trivMap φ x) : smallAt W x hx ⟶ smallAt W _ (hx.map φ)) ≫
      (ObjectProperty.homMk (trivMap ψ (spOver φ ≫ x)) : smallAt W _ (hx.map φ) ⟶ smallAt W _ ((hx.map φ).map ψ)))
    (fun _ ↦ rfl)
  rw [e]
  change ψ _ - _ + _ = 0 at key
  linear_combination -key
end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartCocycleCoboundaryOfHodgeDeRham
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndPullCohomZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem spOver_epsHom_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B)
    {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    (spOver (epsHom φ) ≫ ptV v x : Pt (A ⊗ B) (DualNumber D')) =
      ptV v (spOver φ ≫ x : Pt A D') := by
  have h1 : (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ :=
    AlgHom.ext fun a ↦ by simp [epsHom]
  have h2 : (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' :=
    DualNumber.algHom_ext (by simp [epsHom, EpsWeil.epsMap, DualNumber.lift_apply_apply])
  simp only [ptV, comp_lift, ← Category.assoc, spOver_comp, h1, h2]

theorem fst_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {v : epsR R ⟶ B} (hv : IsTangent v)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x : Pt (A ⊗ B) D) = pt0 B x := by
  have h1 : (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D :=
    AlgHom.ext fun _ ↦ rfl
  have h2 : (TrivSqZeroExt.fstHom R D D).comp (EpsWeil.epsMap R D) =
      (Algebra.ofId R D).comp (TrivSqZeroExt.fstHom R R R) :=
    DualNumber.algHom_ext (by simp [EpsWeil.epsMap, DualNumber.lift_apply_apply])
  rw [ptV, pt0, comp_lift, ← Category.assoc, spOver_comp, h1, spOver_id, Category.id_comp,
    ← Category.assoc, spOver_comp, h2, ← spOver_comp, Category.assoc]
  congr 1
  ext1
  rw [Over.comp_left, Over.comp_left, spOver_left, spOver_left, Hom.one_def, Over.comp_left, Over.toUnit_left]
  have := hv
  unfold IsTangent at this
  erw [this]
  rfl

theorem sm_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) {v : epsR R ⟶ B}
    (hv : IsTangent v) {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}
    (hx : Sm (chartsA (A := A) (B := B) P) x) : Sm (X := A ⊗ B) P.U (ptV v x) := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  have hsurj : Surjective (spOver (TrivSqZeroExt.fstHom R D D)).left := by
    rw [spOver_left]
    refine GlobalTheory.TorusLift.surjective_specMap _ (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩) ⟨2, ?_⟩
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']
  have e : (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x : Pt (A ⊗ B) D).left =
      x.left ≫ (AbDual.inl A B).left := by
    rw [fst_ptV hv, ← Over.comp_left, pt0, AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]
  have := GlobalTheory.TorusLift.preimage_eq_top_of_surjective (spOver (TrivSqZeroExt.fstHom R D D)).left
    (ptV v x).left (U := P.U i) (by
      rw [← Over.comp_left, e, Scheme.Hom.comp_preimage]
      exact top_unique hi)
  exact this.ge

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartCocycleCoboundaryOfHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem sndPull_cohom_zero_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ u : Fn1 (A ⊗ B), IsCoc P.U u → Cohom (chartsA P) (sndPull u v) (Fn1.zero A) := by
  intro hHDR R _ A B _ _ g hA hB hgA hgB P hP v hv u hu
  have hFree : GlobalTheory.Published.AbelianDeRham.Free := (GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange hHDR).1
  have hAB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have hgAB : SmoothOfRelativeDimension (g + g) (A ⊗ B).hom := AbDual.smooth_prod hgA hgB
  obtain ⟨u', hu', hExt⟩ :=
    GlobalTheory.T.pointwise_cocycle_on_cover_extends_up_to_coboundary R (A ⊗ B) P.ι P.U hP.cover u hu
  have hSurj := GlobalTheory.T.de_rham_to_h1_structure_surjective_abelian hHDR R (A ⊗ B) (g + g) hAB hgAB
  obtain ⟨f, hLift⟩ := GlobalTheory.T.cocycle_cohomologous_of_de_rham_surjective R (A ⊗ B) hSurj u' hu'
  have hprim : CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) := by
    have h : AllPrim (dp0 R) (𝟙 _) (A ⊗ B) := (hFree R (A ⊗ B) (g + g) hAB hgAB).1
    rw [primDR, h]; trivial
  have hTan := GlobalTheory.T.tangentPullback_primitiveCrystallineClass_epsPart_isCob R A B f hprim v
  unfold Cohom at hExt hLift hTan ⊢
  obtain ⟨k1, c1⟩ := hExt
  obtain ⟨k2, c2⟩ := hLift
  obtain ⟨k3, c3⟩ := hTan
  refine ⟨fun D _ _ x ↦ (k1 (DualNumber D) (ptV v x)).snd + (k2 (DualNumber D) (ptV v x)).snd + k3 D x, ?_⟩
  intro D _ _ D' _ _ φ x hx
  have e1 := congrArg TrivSqZeroExt.snd (c1 _ _ (epsHom φ) (ptV v x) (sm_ptV P hv hx))
  have e2 := congrArg TrivSqZeroExt.snd (c2 _ _ (epsHom φ) (ptV v x) (sm_whole _))
  have e3 := c3 D D' φ x (sm_whole _)
  simp only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_neg,
    TrivSqZeroExt.snd_sub, spOver_epsHom_ptV, snd_epsHom] at e1 e2 e3 ⊢
  rw [map_add (f := _), map_add (f := _)]
  linear_combination e1 + e2 + e3

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartCocycleCoboundaryOfHodgeDeRhamStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eps_part_cocycle_coboundary_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ u : Fn1 (A ⊗ B), IsCoc P.U u → Cohom (chartsA P) (sndPull u v) (Fn1.zero A) := by
  first | exact @GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham | exact GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham | (intros; apply GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassContractionTangentEqTorsorCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCocycleTangentContractionCohomologousTorsor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCocycleTangentContractionCohomologousTorsor
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ChernContr

section Dl

variable {R : Type} [CommRing R] {D D' : Type} [CommRing D] [CommRing D']

theorem dl_mul (u u' : DualNumber D) (hu : IsUnit u.fst) (hu' : IsUnit u'.fst) :
    dl (u * u') = dl u + dl u' := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hu'
  have e1 : (↑a : D) * ↑a⁻¹ = 1 := Units.mul_inv a
  have e2 : (↑b : D) * ↑b⁻¹ = 1 := Units.mul_inv b
  have e3 : Ring.inverse ((↑a : D) * ↑b) = ↑b⁻¹ * ↑a⁻¹ := by
    rw [← Units.val_mul, Ring.inverse_unit, mul_inv_rev, Units.val_mul]
  simp only [dl, TrivSqZeroExt.fst_mul, DualNumber.snd_mul, ← ha, ← hb, e3,
    Ring.inverse_unit]
  linear_combination (u'.snd * ↑b⁻¹) * e1 + (u.snd * ↑a⁻¹) * e2

theorem dl_one_add (l : DualNumber D) (h : l.fst = 0) : dl (1 + l) = l.snd := by
  simp [dl, h]

theorem dl_inl (c : D) : dl (TrivSqZeroExt.inl c : DualNumber D) = 0 := by
  simp [dl]

theorem fst_epsHom [Algebra R D] [Algebra R D'] (φ : D →ₐ[R] D') (z : DualNumber D) :
    (epsHom φ z).fst = φ z.fst := by
  simp [epsHom, DualNumber.lift_apply_apply]

theorem snd_epsHom' [Algebra R D] [Algebra R D'] (φ : D →ₐ[R] D') (z : DualNumber D) :
    (epsHom φ z).snd = φ z.snd := by
  simp [epsHom, DualNumber.lift_apply_apply]

theorem dl_epsHom [Algebra R D] [Algebra R D'] (φ : D →ₐ[R] D') (z : DualNumber D) (hz : IsUnit z.fst) :
    dl (epsHom φ z) = φ (dl z) := by
  obtain ⟨a, ha⟩ := hz
  have e : Ring.inverse (φ (a : D)) = φ (↑a⁻¹ : D) := by
    rw [show φ (a : D) = ((Units.map (φ : D →* D') a : D'ˣ) : D') from rfl, Ring.inverse_unit]
    rfl
  simp only [dl, fst_epsHom, snd_epsHom', ← ha, e, Ring.inverse_unit, map_mul]

theorem snd_of_exp (l a b c : DualNumber D) (hl : l.fst = 0) (ha : IsUnit a.fst) (hb : IsUnit b.fst)
    (hc : IsUnit c.fst) (h : (1 + l) * c = a * b) : l.snd = dl a + dl b - dl c := by
  have e := congrArg dl h
  rw [dl_mul _ _ (by simp [hl]) hc, dl_mul _ _ ha hb, dl_one_add _ hl] at e
  linear_combination e

theorem isUnit_fst {u : DualNumber D} (h : IsUnit u) : IsUnit u.fst := h.map (TrivSqZeroExt.fstHom D D D)

end Dl

section Pts

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

omit [GrpObj A] in
theorem pointWithZeroSecondCoord_left {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (pt0 B x).left = x.left ≫ (AbDual.inl A B).left := by
  rw [← Over.comp_left, pt0, AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]

omit [GrpObj A] in
theorem pointWithZeroSecondCoord_mem_chart_of_restricted (P : LB (A ⊗ B).left) {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {c : P.ι}
    (h : ⊤ ≤ x.left ⁻¹ᵁ chartsA P c) : ⊤ ≤ (pt0 B x).left ⁻¹ᵁ P.U c := by
  rw [pointWithZeroSecondCoord_left, Scheme.Hom.comp_preimage]
  exact h

omit [GrpObj A] in
theorem ptV_mem (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {D : Type} [CommRing D]
    [Algebra R D] {x : Pt A D} {c : P.ι} (h : ⊤ ≤ x.left ⁻¹ᵁ chartsA P c) : ⊤ ≤ (ptV v x).left ⁻¹ᵁ P.U c := by
  have hsurj : Surjective (spOver (TrivSqZeroExt.fstHom R D D)).left := by
    rw [spOver_left]
    refine GlobalTheory.TorusLift.surjective_specMap _ (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩) ⟨2, ?_⟩
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']
  have e : (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x).left = (pt0 B x).left := by
    rw [ContrMor.spOver_fst_ptV v hv x]
  have := GlobalTheory.TorusLift.preimage_eq_top_of_surjective (spOver (TrivSqZeroExt.fstHom R D D)).left
    (ptV v x).left (U := P.U c) (by
      rw [← Over.comp_left, e]
      exact top_unique (pointWithZeroSecondCoord_mem_chart_of_restricted P h))
  exact this.ge

end Pts

section Ev

variable {X : Scheme.{0}}

theorem evalAt_res' {C : Type} [CommRing C] (x : Sp C ⟶ X) {V U : X.Opens} (hVU : V ≤ U)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    evalAt x U hU f = evalAt x V hV ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  simp only [evalAt, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem evalAt_spMap' {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') (x : Sp C ⟶ X)
    (x' : Sp C' ⟶ X) (e : spMap φ ≫ x = x') {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U)
    (f : Γ(X, U)) : φ (evalAt x U h f) = evalAt x' U h' f := by
  subst e
  have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C')).hom =
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫ CommRingCat.ofHom φ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
    congr 2
  exact (congrArg (fun t ↦ t.hom f) e).symm

abbrev gv (L : LB X) {C : Type} [CommRing C] (x : Sp C ⟶ X) (a b : L.ι) : C :=
  evU x (L.U a ⊓ L.U b) (L.g a b).val

theorem gv_eq (L : LB X) {C : Type} [CommRing C] (x : Sp C ⟶ X) {a b : L.ι}
    (h : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U b)) : gv L x a b = evalAt x (L.U a ⊓ L.U b) h (L.g a b).val := dite_eq_left h

theorem isUnit_gv (L : LB X) {C : Type} [CommRing C] (x : Sp C ⟶ X) {a b : L.ι}
    (ha : ⊤ ≤ x ⁻¹ᵁ L.U a) (hb : ⊤ ≤ x ⁻¹ᵁ L.U b) : IsUnit (gv L x a b) := by
  rw [gv_eq L x (le_inf ha hb)]
  exact (L.g a b).isUnit.map _

theorem gv_cocycle (L : LB X) (hL : L.IsLB) {C : Type} [CommRing C] (x : Sp C ⟶ X) {a b c : L.ι}
    (ha : ⊤ ≤ x ⁻¹ᵁ L.U a) (hb : ⊤ ≤ x ⁻¹ᵁ L.U b) (hc : ⊤ ≤ x ⁻¹ᵁ L.U c) :
    gv L x a b * gv L x b c = gv L x a c := by
  have h₁ : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U b) := le_inf ha hb
  have h₂ : ⊤ ≤ x ⁻¹ᵁ (L.U b ⊓ L.U c) := le_inf hb hc
  have h₃ : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U c) := le_inf ha hc
  have hW : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c) := le_inf h₁ hc
  have e := congrArg (fun u : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ ↦ evalAt x _ hW u.val) (hL.cocycle a b c)
  simp only [Units.val_mul, map_mul] at e
  rw [gv_eq L x h₁, gv_eq L x h₂, gv_eq L x h₃, evalAt_res' x inf_le_left h₁ hW,
    evalAt_res' x (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h₂ hW,
    evalAt_res' x (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h₃ hW]
  exact e

theorem dl_gv {R : Type} [CommRing R] {D D' : Type} [CommRing D] [CommRing D'] [Algebra R D] [Algebra R D']
    (φ : D →ₐ[R] D') (L : LB X) (hL : L.IsLB) (y : Sp (DualNumber D) ⟶ X) (y' : Sp (DualNumber D') ⟶ X)
    (e : spMap (epsHom φ : DualNumber D →+* DualNumber D') ≫ y = y') {a b a' b' : L.ι}
    (ha : ⊤ ≤ y ⁻¹ᵁ L.U a) (hb : ⊤ ≤ y ⁻¹ᵁ L.U b) (ha' : ⊤ ≤ y' ⁻¹ᵁ L.U a') (hb' : ⊤ ≤ y' ⁻¹ᵁ L.U b') :
    dl (gv L y' a' a) = dl (gv L y' b' b) + φ (dl (gv L y b a)) - dl (gv L y' b' a') := by
  have ka : ⊤ ≤ y' ⁻¹ᵁ L.U a := by
    rw [← e]; exact fun p _ ↦ ha (Set.mem_univ _)
  have kb : ⊤ ≤ y' ⁻¹ᵁ L.U b := by
    rw [← e]; exact fun p _ ↦ hb (Set.mem_univ _)
  have e1 := congrArg dl (gv_cocycle L hL y' hb' ha' ka)
  have e2 := congrArg dl (gv_cocycle L hL y' hb' kb ka)
  rw [dl_mul _ _ (isUnit_fst (isUnit_gv L _ hb' ha')) (isUnit_fst (isUnit_gv L _ ha' ka))] at e1
  rw [dl_mul _ _ (isUnit_fst (isUnit_gv L _ hb' kb)) (isUnit_fst (isUnit_gv L _ kb ka))] at e2
  have e3 : gv L y' b a = epsHom φ (gv L y b a) := by
    rw [gv_eq L y' (le_inf kb ka), gv_eq L y (le_inf hb ha)]
    exact (evalAt_spMap' (epsHom φ : DualNumber D →+* DualNumber D') y y' e _ _ _).symm
  rw [e3, dl_epsHom φ _ (isUnit_fst (isUnit_gv L _ hb ha))] at e2
  linear_combination e1 - e2

end Ev

end GlobalTheory.PtExt.ChernContr

namespace GlobalTheory.PtExt.ChernContr
open ContrMor


set_option maxHeartbeats 1000000 in
theorem contr_cohom : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB →
    ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j →
    ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)),
    (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ →
      T''.J = ⊥ → w.1 T T' T'' a b = 0) →
    ∀ (i : (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).FullSubcategory → P.ι)
      (hi : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ P.U (i T))
      (U : ∀ T T' : (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).FullSubcategory, (T ⟶ T') → T'.obj.B)
      (ℓ : Z2 ((IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι ⋙ O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))),
    (∀ T T' φ, T'.obj.π (U T T' φ) = evalAt T'.obj.x (P.U (i T') ⊓ P.U (i T))
      (le_inf (hi T') (φ.hom.le_preimage (hi T))) (P.g (i T') (i T)).val) →
    (∀ T T' T'' φ ψ, (ℓ.1 T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (ℓ.1 T T' T'' φ ψ) * U T T'' (φ ≫ ψ) = ψ.hom.φ (U T T' φ) * U T' T'' ψ) →
    ∀ n : C1 ((IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι ⋙ O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)),
    d1 _ n = ((CoefMap.restrict (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))
      (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι).pullbackTwoCocycle w).1 - ℓ.1 →
    ∀ κ : Fn1 A, IsContr w.1 v κ → Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull (cocOf P.U n) v)) := by
  classical
  intro R _ A B _ _ P hP v hv j hj w _ i hi U ℓ hU hℓ n hn κ hκ
  have s0 : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → Sm P.U (pt0 B x) :=
    fun ⟨c, h⟩ ↦ ⟨c, pointWithZeroSecondCoord_mem_chart_of_restricted P h⟩
  have sV : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → Sm P.U (ptV v x) :=
    fun ⟨c, h⟩ ↦ ⟨c, ptV_mem P hv h⟩
  let T0 : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → SmallCat P.U :=
    fun {_} _ _ {x} h ↦ ⟨trivAt (pt0 B x), s0 h⟩
  let TV : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → SmallCat P.U :=
    fun {_} _ _ {x} h ↦ ⟨trivAt (ptV v x), sV h⟩
  let TT : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → SmallCat P.U :=
    fun {_} _ _ {x} h ↦ ⟨thickAt B x, s0 h⟩
  let sM : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} (h : Sm (chartsA P) x), T0 h ⟶ TT h :=
    fun {_} _ _ {x} _ ↦ ObjectProperty.homMk (sHom x)
  let iM : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} (h : Sm (chartsA P) x), TV h ⟶ TT h :=
    fun {_} _ _ {x} _ ↦ ObjectProperty.homMk (iHom v hv x)
  let k : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → D :=
    fun {D} _ _ {x} h ↦ TrivSqZeroExt.snd (R := D) (n _ _ (sM h)) - TrivSqZeroExt.snd (R := D) (n _ _ (iM h)) +
      (dl (U _ _ (sM h)) - dl (U _ _ (iM h))) + dl (gv P (ptV v x).left (j D x) (i (TV h)))
  refine ⟨fun D _ _ x ↦ if h : Sm (chartsA P) x then -k h else 0, ?_⟩
  intro D _ _ D' _ _ φ x hx
  let x' : Pt A D' := spOver φ ≫ x
  have hx' : Sm (chartsA P) (D := D') (spOver φ ≫ x) := hx.map φ
  simp only [dite_eq_left hx, dite_eq_left hx', Fn1.add, Fn1.neg]
  let aM : T0 hx ⟶ T0 hx' := ObjectProperty.homMk (aHom φ x)
  let bM : TV hx ⟶ TV hx' := ObjectProperty.homMk (bHom v φ x)
  let tM : TT hx ⟶ TT hx' := ObjectProperty.homMk (τHom φ x)
  have c1 : sM hx ≫ tM = aM ≫ sM hx' := ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext fun r ↦ by
    change epsHom φ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r)
    ext
    · exact fst_epsHom φ _
    · exact (snd_epsHom' φ _).trans (map_zero φ)))
  have c2 : iM hx ≫ tM = bM ≫ iM hx' := ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext fun r ↦ rfl))
  have uU : ∀ (S S' : SmallCat P.U) (f : S ⟶ S'), IsUnit (S'.obj.π (U S S' f)) := fun S S' f ↦ by
    rw [hU]; exact (P.g _ _).isUnit.map _
  have key : ∀ (S S' : SmallCat P.U) (f : S ⟶ S') (g : S' ⟶ TT hx'),
      IsUnit (TrivSqZeroExt.fst (R := D') (M := D') (g.hom.φ (U _ _ f))) →
      TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ f.hom g.hom) =
        TrivSqZeroExt.snd (R := D') (M := D') (g.hom.φ (n _ _ f)) -
          TrivSqZeroExt.snd (R := D') (M := D') (n _ _ (f ≫ g)) + TrivSqZeroExt.snd (R := D') (M := D') (n _ _ g) +
        (dl (D := D') (g.hom.φ (U _ _ f)) + dl (D := D') (U _ _ g) - dl (D := D') (U _ _ (f ≫ g))) := by
    intro S S' f g hu
    obtain ⟨hm, he⟩ := hℓ S S' (TT hx') f g
    have e1 : dpExp (TT hx').obj.δ (ℓ.1 _ _ _ f g) = @HAdd.hAdd (DualNumber D') (DualNumber D') (DualNumber D') _ 1 (ℓ.1 _ _ _ f g) :=
      dpExp_sqDP (epsExt R D').sq hm
    have e2 := snd_of_exp (D := D') (ℓ.1 _ _ _ f g) (g.hom.φ (U _ _ f)) (U _ _ g) (U _ _ (f ≫ g)) hm hu
      (uU _ _ g) (uU _ _ (f ≫ g)) ((congrArg (· * U _ _ (f ≫ g)) e1).symm.trans he)
    have e3 := congrArg (TrivSqZeroExt.snd (R := D') (M := D'))
      (congrFun (congrFun (congrFun (congrFun (congrFun hn S) S') (TT hx')) f) g)
    change TrivSqZeroExt.snd (R := D') (M := D') (g.hom.φ (n _ _ f)) -
          TrivSqZeroExt.snd (R := D') (M := D') (n _ _ (f ≫ g)) + TrivSqZeroExt.snd (R := D') (M := D') (n _ _ g) =
      TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ f.hom g.hom) -
        TrivSqZeroExt.snd (R := D') (M := D') (ℓ.1 _ _ _ f g) at e3
    linear_combination e2 - e3
  have us : IsUnit (TrivSqZeroExt.fst (R := D) (M := D) (U _ _ (sM hx))) := uU _ _ (sM hx)
  have ui : IsUnit (TrivSqZeroExt.fst (R := D) (M := D) (U _ _ (iM hx))) := uU _ _ (iM hx)
  have k1 := key _ _ (sM hx) tM (((fst_epsHom φ _).symm ▸ us.map φ :
    IsUnit (epsHom φ (U _ _ (sM hx))).fst))
  have k2 := key _ _ aM (sM hx') (uU _ _ aM)
  have k3 := key _ _ (iM hx) tM (((fst_epsHom φ _).symm ▸ ui.map φ :
    IsUnit (epsHom φ (U _ _ (iM hx))).fst))
  have k4 := key _ _ bM (iM hx') (isUnit_fst (D := D') (uU _ _ bM))
  rw [c1] at k1
  rw [c2] at k3
  have a1 : TrivSqZeroExt.snd (R := D') (M := D') (tM.hom.φ (n _ _ (sM hx))) =
    φ (TrivSqZeroExt.snd (R := D) (n _ _ (sM hx))) := snd_epsHom' φ _
  have a2 : TrivSqZeroExt.snd (R := D') (M := D') ((sM hx').hom.φ (n _ _ aM)) = 0 := rfl
  have a3 : TrivSqZeroExt.snd (R := D') (M := D') (tM.hom.φ (n _ _ (iM hx))) =
    φ (TrivSqZeroExt.snd (R := D) (n _ _ (iM hx))) := snd_epsHom' φ _
  have a4 : TrivSqZeroExt.snd (R := D') (M := D') ((iM hx').hom.φ (n _ _ bM)) =
      sndPull (cocOf P.U n) v D D' φ x := by
    have tr : ∀ (y y' : Pt (A ⊗ B) (DualNumber D')) (_ : y = y') (h : Sm P.U y) (h' : Sm P.U y')
        (f : TV hx ⟶ smallAt P.U y h) (f' : TV hx ⟶ smallAt P.U y' h'),
        (∀ r, f.hom.φ r = f'.hom.φ r) → n _ _ f = n _ _ f' := by
      rintro y _ rfl h h' f f' hf
      have : f = f' := ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext hf))
      subst this; rfl
    simp only [sndPull, cocOf, dite_eq_left (sV hx)]
    exact congrArg (TrivSqZeroExt.snd (R := D') (M := D'))
      (tr _ _ (spOver_epsHom_ptV v φ x).symm (sV hx') ((sV hx).map (epsHom φ)) bM
        (ObjectProperty.homMk (trivMap (epsHom φ) (ptV v x))) fun _ ↦ rfl)
  have b1 : dl (D := D') (tM.hom.φ (U _ _ (sM hx))) = φ (dl (U _ _ (sM hx))) := dl_epsHom φ _ us
  have b2 : dl (D := D') ((sM hx').hom.φ (U _ _ aM)) = 0 := dl_inl _
  have b3 : dl (D := D') (tM.hom.φ (U _ _ (iM hx))) = φ (dl (U _ _ (iM hx))) := dl_epsHom φ _ ui
  have b4 : dl (D := D') ((iM hx').hom.φ (U _ _ bM)) = tanCoc P j v D D' φ x +
      φ (dl (gv P (ptV v x).left (j D x) (i (TV hx)))) -
      dl (gv P (ptV v x').left (j D' x') (i (TV hx'))) := by
    have e : (iM hx').hom.φ (U _ _ bM) = gv P (ptV v x').left (i (TV hx')) (i (TV hx)) :=
      (hU _ _ bM).trans (gv_eq P _ _).symm
    have e' : spMap (epsHom φ : DualNumber D →+* DualNumber D') ≫ (ptV v x).left =
        (ptV v x').left := (bHom v φ x).pt
    exact (congrArg (dl (D := D')) e).trans (dl_gv φ P hP _ _ e' (hi (TV hx)) (ptV_mem P hv (hj D x hx))
      (hi (TV hx')) (ptV_mem P hv (hj D' _ hx')))
  have hk := hκ D D' φ x (sHom x) (iHom v hv x) (sHom _) (iHom v hv _) (aHom φ x) (bHom v φ x) (τHom φ x)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  change _ = TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ (sM hx).hom tM.hom) -
    TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ aM.hom (sM hx').hom) -
    TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ (iM hx).hom tM.hom) +
    TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ bM.hom (iM hx').hom) at hk
  simp only [k, map_neg, map_add (f := _), map_sub]
  linear_combination hk + k1 - k2 - k3 + k4 + a1 - a2 - a3 + a4 + b1 - b2 - b3 + b4

end GlobalTheory.PtExt.ChernContr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCocycleTangentContractionCohomologousTorsorStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCocycle_tangentContraction_cohomologous_torsor : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB →
    ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j →
    ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)),
    (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ →
      T''.J = ⊥ → w.1 T T' T'' a b = 0) →
    ∀ (i : (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).FullSubcategory → P.ι)
      (hi : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ P.U (i T))
      (U : ∀ T T' : (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).FullSubcategory, (T ⟶ T') → T'.obj.B)
      (ℓ : Z2 ((IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι ⋙ O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))),
    (∀ T T' φ, T'.obj.π (U T T' φ) = evalAt T'.obj.x (P.U (i T') ⊓ P.U (i T))
      (le_inf (hi T') (φ.hom.le_preimage (hi T))) (P.g (i T') (i T)).val) →
    (∀ T T' T'' φ ψ, (ℓ.1 T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (ℓ.1 T T' T'' φ ψ) * U T T'' (φ ≫ ψ) = ψ.hom.φ (U T T' φ) * U T' T'' ψ) →
    ∀ n : C1 ((IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι ⋙ O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)),
    d1 _ n = ((CoefMap.restrict (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))
      (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι).pullbackTwoCocycle w).1 - ℓ.1 →
    ∀ κ : Fn1 A, IsContr w.1 v κ → Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull (cocOf P.U n) v)) := by
  first | exact @GlobalTheory.PtExt.ChernContr.contr_cohom | exact GlobalTheory.PtExt.ChernContr.contr_cohom | (intros; apply GlobalTheory.PtExt.ChernContr.contr_cohom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassContractionTangentEqTorsorCocycle
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem contr_chern_eq_tanCoc : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) → (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) → ∀ κ : Fn1 A, IsContr w.1 v κ → ∃ u : Fn1 (A ⊗ B), IsCoc P.U u ∧ Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull u v)) := by
  intro R _ A B _ _ P hP v hv j hj w hch hw κ hκ
  obtain ⟨i, hi, U, ℓ, hU, hℓ, hcl⟩ := hch
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hcl
  obtain ⟨n, hn⟩ := hcl
  refine ⟨cocOf P.U n, ?_, ?_⟩
  · apply GlobalTheory.PtExt.isCoc_cocOf
    intro T T' T'' a b h h' h''
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hn T) T') T'') a) b
    rw [e]
    have h0 : ℓ.1 T T' T'' a b = 0 := by
      have hm := (hℓ T T' T'' a b).1
      rw [h''] at hm
      exact Ideal.mem_bot.mp hm
    change w.1 _ _ _ _ _ - ℓ.1 T T' T'' a b = 0
    rw [h0, sub_zero]
    exact hw _ _ _ _ _ h h' h''
  · exact GlobalTheory.T.chernCocycle_tangentContraction_cohomologous_torsor
      R A B P hP v hv j hj w hw i hi U ℓ hU hℓ n hn κ hκ

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassContractionTangentEqTorsorCocycleStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernClass_contraction_tangent_eq_torsorCocycle : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) → (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) → ∀ κ : Fn1 A, IsContr w.1 v κ → ∃ u : Fn1 (A ⊗ B), IsCoc P.U u ∧ Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull u v)) := by
  first | exact @GlobalTheory.PtExt.contr_chern_eq_tanCoc | exact GlobalTheory.PtExt.contr_chern_eq_tanCoc | (intros; apply GlobalTheory.PtExt.contr_chern_eq_tanCoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologousNegTorsorCocycleOfOrthogonal
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → Cohom (chartsA P) (fv f) (tanCoc P j v).neg := by
  intro H2' R _ A B _ _ g hA hB sA sB P hL φ hφ hO h' v hv c hc f hf j hj
  have hT : IsTangent v := hv.1
  obtain ⟨w, hw, hw0, hκ⟩ := GlobalTheory.T.exists_chernRepresentative_contraction_of_orthogonal H2' R A B g hA hB sA sB P hL φ hφ hO h' v hv c hc f hf
  obtain ⟨κ, hκc⟩ : ∃ κ : Fn1 A, IsContr w.1 v κ :=
    (GlobalTheory.PtExt.ContrMor.exists_contr R A B v hT).2 w.1
  obtain ⟨k1, h1⟩ := hκ κ hκc
  obtain ⟨u, hu, k2, h2⟩ := GlobalTheory.T.chernClass_contraction_tangent_eq_torsorCocycle R A B P hL v hT j hj w hw hw0 κ hκc
  obtain ⟨k3, h3⟩ := GlobalTheory.T.eps_part_cocycle_coboundary_of_hodgeDeRham H2' R A B g hA hB sA sB P hL v hT u hu
  refine ⟨fun D _ _ x ↦ k1 D x - k2 D x - k3 D x, fun D _ _ D' _ _ ψ x hx ↦ ?_⟩
  have e1 := h1 D D' ψ x (sm_whole x)
  have e2 := h2 D D' ψ x hx
  have e3 := h3 D D' ψ x hx
  simp only [Fn1.add, Fn1.neg, Fn1.zero, map_sub] at e1 e2 e3 ⊢
  linear_combination e1 - e2 - e3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologousNegTorsorCocycleOfOrthogonalStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologous_neg_torsor_cocycle_of_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → Cohom (chartsA P) (fv f) (tanCoc P j v).neg := by
  first | exact @GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal | exact GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal | (intros; apply GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal <;> assumption)
end
