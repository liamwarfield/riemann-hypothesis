module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTripleLinearTorsionIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDense
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerShapeDependsOnlyOnMatrices
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfFlatDedekindTangentLe
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaFamilyOverOpenClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueMapToThetaFamilyOpenPart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassE8Sharp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpObjectFibreFromComplexCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyOverThetaPointScheme

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LN

theorem _root_.GlobalTheory.LN.pelSt_holds : _root_.GlobalTheory.LN.PelSt := by
  obtain ⟨hLaws, hTwist, hTheta, hTorsion, hRank⟩ := _root_.GlobalTheory.lawsAndExpansions
  exact _root_.GlobalTheory.PELOfUnif.main hLaws hTwist hTheta hTorsion hRank

end GlobalTheory.LN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearUniformisation_triples_torsion : GlobalTheory.LN.PelSt := by
  first | exact @GlobalTheory.LN.pelSt_holds | exact GlobalTheory.LN.pelSt_holds | (intros; apply GlobalTheory.LN.pelSt_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBase
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelArithFamily

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [spMap, spMap, ← Spec.map_comp]; rfl

theorem comp_spMap_id {A : Type} [CommRing A] {S : Scheme.{0}} (s : S ⟶ Sp A) : s ≫ spMap (RingHom.id A) = s := by
  have : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _
  rw [this, Category.comp_id]

theorem locallyOfFiniteType_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  infer_instance

theorem charZero_residueField {o : Type} [CommRing o] [CharZero o] {S : Scheme.{0}} (s : S ⟶ Sp o) (p : S)
    (hp : (s p).asIdeal = ⊥) : CharZero (S.residueField p) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S.fromSpecResidueField p ≫ s)
  have h1 : (Spec.map φ) (⊥ : PrimeSpectrum (S.residueField p)) = s p := by
    rw [hφ]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg s (Scheme.fromSpecResidueField_apply p _))
  have h2 : Ideal.comap φ.hom ⊥ = ⊥ := by
    rw [← hp, ← h1]; rfl
  have h3 : Function.Injective φ.hom := (RingHom.injective_iff_ker_eq_bot _).2 h2
  exact charZero_of_injective_ringHom (R := o) h3

theorem dir_over {o K : Type} [CommRing o] [Field K] {r : ℕ} (β : o →+* K) (lam : (Fin r → K) →ₗ[K] K) :
    spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      constPt (spMap (dirMap lam)) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) := by
  rw [constPt, spMap_comp_spMap, spMap_comp_spMap, spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_matrices {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) :
    ∃ (a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ) (w w' : (Fin 8 × Fin 8) ⊕ Bool),
      (W + W.transpose) * a w = W ∧ (W + W.transpose) * a w' = W.transpose ∧
        ∀ u v, ∃ j, a j = Matrix.single u v 1 := by
  refine ⟨Sum.elim (fun uv => Matrix.single uv.1 uv.2 1)
    (fun c => (W + W.transpose).adjugate * (if c then W else W.transpose)), .inr true, .inr false, ?_, ?_,
    fun u v => ⟨.inl (u, v), rfl⟩⟩
  · simp only [Sum.elim_inr, if_true]
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hW.2, one_smul, Matrix.one_mul]
  · simp only [Sum.elim_inr, Bool.false_eq_true, if_false]
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hW.2, one_smul, Matrix.one_mul]

theorem nonempty_sFam : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h n : ℕ), 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ), ArBase em → Nonempty (SFam h ((n ^ j) ^ 2) (b.ζ : o)) := by
  intro L1 L2 hT hU h n hh hn hodd
  obtain ⟨W, hW, hbas⟩ := exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas h
  obtain ⟨a, w, w', hw, hw', hu⟩ := exists_matrices hW
  obtain ⟨Mat, κ, hgood⟩ := GlobalTheory.T.isGoodThetaComplexClass_E8Sharp L1 L2 hT hU h _ W _ a w w' bas hW hb hw hw' hu
  obtain ⟨j₁, hj₁⟩ := hgood n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.nonempty_thetaFamily_over_open_closure L1 L2 _ _ Mat κ n w w' hn hodd
  obtain ⟨j₃, hj₃⟩ := GlobalTheory.T.existsUnique_map_to_thetaFamily_openPart L1 L2 _ _ Mat κ n w w' hn hodd
  refine ⟨max (max j₁ 1) (max j₂ j₃), fun j hj o _ b em hem => ?_⟩
  have hj1 : j ≥ j₁ := by omega
  have hj0 : j ≠ 0 := by omega
  have hj2 : j ≥ j₂ := by omega
  have hj3 : j ≥ j₃ := by omega
  have h3 : 3 ≤ n ^ j := by
    have h2 := hn.two_le
    have : n ≠ 2 := fun e => by rw [e] at hodd; exact absurd hodd (by decide)
    exact le_trans (by omega) (Nat.le_self_pow hj0 n)
  have hoN : Odd (n ^ j) := hodd.pow
  have hok : Odd ((n ^ j) ^ 2) := hoN.pow
  have h3k : 3 ≤ (n ^ j) ^ 2 := h3.trans (Nat.le_self_pow two_ne_zero _)
  have hζ : b.ζ ^ ((n ^ j) ^ 2) = 1 := by
    refine Units.ext (hem.2.2 ?_)
    rw [Units.val_pow_eq_pow_val, map_pow, (b.prim ℂ em).pow_eq_one, Units.val_one, map_one]
  have hG := hj₁ j hj1 _ rfl o b em
  obtain ⟨F⟩ := hj₂ j hj2 o b em _ _ hem hG
  obtain ⟨hq, hflat, hred, hinj⟩ := GlobalTheory.T.thetaClosureOpenFamily_qproj_flat_reduced_ext L1 L2 o _ n _ _ b em _ Mat κ F hoN
  haveI := hem.1
  haveI : CharZero o := em.charZero
  have hq : IsQProjOver (F.U.ι ≫ F.Y.s) := hq.resolve_right (not_not.2 inferInstance)
  have hft := locallyOfFiniteType_of_qproj hq
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨c, hc, hsc⟩ := GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense L1 L2 hT h _ W _ a bas hW hb hu _ o b em _ _ F.univ hok F.dense

  have pull : ∀ (S' : Scheme.{0}) (s' : S' ⟶ Sp o) (f : S' ⟶ F.U.toScheme), f ≫ F.U.ι ≫ F.Y.s = s' →
      ∃ (c' : SiegPre h ((n ^ j) ^ 2) (b.ζ : o) s') (t : TObj (8 * h) ((n ^ j) ^ 2) _ b s'),
        SiegPB c' c f ∧ c'.Principal ∧ IsSharp W a bas t c' := by
    intro S' s' f hf
    obtain ⟨p1, p2, -⟩ := GlobalTheory.T.siegelPre_pullback_principal_ringChange h ((n ^ j) ^ 2) o o (b.ζ : o) (b.ζ : o) (RingHom.id o) _ S' _ s' f rfl
      (hf.trans (comp_spMap_id s').symm)
    obtain ⟨c', hc'⟩ := p1 c
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h _ W _ a bas hW hb _ o b S' s' c' hok h3k hζ (p2 c c' hc' hc)
    exact ⟨c', t, hc', p2 c c' hc' hc, ht⟩
  refine ⟨⟨F.U.toScheme, F.U.ι ≫ F.Y.s, ?_, hq, c, hc, ?_, ?_⟩⟩
  · refine GlobalTheory.T.smoothOfRelativeDimension_of_flat_dedekind_tangent_le o _ _ _ hem.2.1 hflat hft
      (fun R _ _ x hx hs => GlobalTheory.T.le_ringKrullDim_thetaFamily_genericFibre L1 L2 _ n _ _ Mat κ w w' o b em _ _ F h3 hoN hem hG R x hx hs) ?_
    intro K _ _ r β x hx hlam
    obtain ⟨c', t, hp, hc', ht⟩ := pull _ _ x hx
    have htx : TMap t F.univ x :=
      (GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t x hc hc' hsc ht).1 hp
    refine GlobalTheory.T.siegelFamily_tangent_dimension_bound L1 L2 hT h _ W _ a bas hW hb w w' hw hw' _ o b K r β t c' hc' ht fun lam t' h1 h2 => hlam lam ?_
    have e : constPt (spMap (dirMap lam) ≫ x) = constPt (spMap (dirMap lam)) ≫ x := by
      simp only [constPt, Category.assoc]
    rw [e]
    refine hinj _ _ _ _ t' ?_ (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o _ _ _ b _ _ _ _ _ _ F.univ t t').2 x _ htx).1 h1)
      (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o _ _ _ b _ _ _ _ _ _ F.univ t t').2 x _ htx).1 h2)
    rw [Category.assoc, Category.assoc, hx]
    exact dir_over β lam
  · intro S s' c' hS hd hc'
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h _ W _ a bas hW hb _ o b S s' c' hok h3k hζ hc'
    have hfrom : ∀ p : S, (s' p).asIdeal = ⊥ →
        FromC em (SharpClass (b := b) W a bas em) t (K := S.residueField p) (S.fromSpecResidueField p) := by
      intro p hp
      haveI := charZero_residueField s' p hp
      exact GlobalTheory.T.fromC_sharpClass_fibre_of_charZero L1 L2 h _ W _ a w w' bas hW hb hw hw' hu _ o b em hem S s' t c' hc' ht _ _
    have hdense : Dense (fromSet em (SharpClass (b := b) W a bas em) t) :=
      hd.mono fun p hp => ⟨S.residueField p, inferInstance, S.fromSpecResidueField p,
        ⟨default, Scheme.fromSpecResidueField_apply p _⟩, hfrom p hp⟩
    have hshape : t.FibShape Mat κ := by
      intro K _ _ x t' ht'
      have : Nonempty S := ⟨x (⊥ : PrimeSpectrum K)⟩
      obtain ⟨p, hp⟩ := hd.nonempty
      obtain ⟨_, _, _, _, _, _, _, tc, -, -, -, -, -, htc⟩ := hfrom p hp
      have hsh := (hG.shape tc htc).1
      obtain ⟨cc, hcc, hscc⟩ := htc
      exact (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o _ _ _ b Mat κ w w' _ _ _ _ x t t' ht').1
        (GlobalTheory.T.eighthPower_shape_depends_only_on_matrices L1 L2 h _ W _ a bas hW hb _ o b Mat κ _ _ _ _ cc c' tc t hh ⟨(⊥ : PrimeSpectrum ℂ)⟩ hcc hc' hscc ht hsh)
    obtain ⟨f, ⟨hf, htf⟩, -⟩ := hj₃ j hj3 o b em _ _ hem hG F S s' t hS hdense hshape
    exact ⟨f, hf, (GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t f hc hc' hsc ht).2 hu htf⟩
  · intro R _ _ x y s' c₀ hxy hx hy
    obtain ⟨c', t, hp, hc', ht⟩ := pull _ _ x rfl
    have h1 : SiegPB c' c₀ (𝟙 _) :=
      ((GlobalTheory.SiegelPullComp.id_comp_cancel h _ o o o _ _ _ _ _ _ _ _ _ c c₀ c' x (𝟙 _)).2 hx).2
        (by rwa [Category.id_comp])
    have h2 : SiegPB c' c y := by
      have := ((GlobalTheory.SiegelPullComp.id_comp_cancel h _ o o o _ _ _ _ _ _ _ _ _ c c₀ c' y (𝟙 _)).2 hy).1 h1
      rwa [Category.id_comp] at this
    exact hinj R x y _ t hxy
      ((GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t x hc hc' hsc ht).1 hp)
      ((GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t y hc hc' hsc ht).1 h2)

end GlobalTheory.ZM.SiegelArithFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_siegelFamily_over_arithmetic_base : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h n : ℕ), 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ), ArBase em → Nonempty (SFam h ((n ^ j) ^ 2) (b.ζ : o)) := by
  first | exact @GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam | exact GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam | (intros; apply GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartImagePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GenTorsMap

theorem exists_factor {K : Type} [Field K] (X : Over (Sp K)) (hX : IsFinite X.hom) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra K F] (x : Sp F ⟶ X.left) (hx : x ≫ X.hom = spMap (algebraMap K F)) :
    ∃ (σ : AlgebraicClosure K →ₐ[K] F) (x' : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X),
      x = spMap σ.toRingHom ≫ x'.left := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ X.left.isoSpec.hom)
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  have hfin : c.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hc]; infer_instance
  have e : c ≫ φ = CommRingCat.ofHom (algebraMap K F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hc, Category.assoc, Iso.hom_inv_id_assoc, hx]
  let σ : AlgebraicClosure K →ₐ[K] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hr : ∀ b, φ.hom b ∈ σ.range := fun b => by
    have hi : IsIntegral K (φ.hom b) := by
      obtain ⟨p, hp, h0⟩ := hfin.to_isIntegral b
      refine ⟨p, hp, ?_⟩
      have := congrArg φ.hom h0
      rw [Polynomial.hom_eval₂, map_zero] at this
      have e' : φ.hom.comp c.hom = algebraMap K F := congrArg CommRingCat.Hom.hom e
      rwa [e'] at this
    exact hi.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) σ
  have hσ : Function.Injective σ := σ.toRingHom.injective
  let φ' : Γ(X.left, ⊤) →+* AlgebraicClosure K :=
    (AlgEquiv.ofInjective σ hσ).symm.toRingEquiv.toRingHom.comp (φ.hom.codRestrict σ.range hr)
  have h1 : ∀ b, σ (φ' b) = φ.hom b := fun b =>
    congrArg Subtype.val ((AlgEquiv.ofInjective σ hσ).apply_symm_apply ⟨φ.hom b, hr b⟩)
  refine ⟨σ, Over.homMk (Spec.map (CommRingCat.ofHom φ') ≫ X.left.isoSpec.inv) ?_, ?_⟩
  · refine (Category.assoc _ _ _).trans ?_
    erw [← hc]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    apply hσ
    refine (h1 _).trans ?_
    refine Eq.trans ?_ (σ.commutes a).symm
    exact congrArg (fun g => CommRingCat.Hom.hom g a) e
  · show x = _ ≫ _ ≫ _
    rw [← Category.assoc, Iso.eq_comp_inv, ← hφ, ← Spec.map_comp]
    congr 1
    ext b
    exact (h1 b).symm

theorem hom_ext_points {K : Type} [Field K] {X Y : Over (Sp K)} (hX : IsFinite X.hom) (hE : Etale X.hom)
    (hY : IsSeparated Y.hom) (u v : X ⟶ Y)
    (h : ∀ x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X, x ≫ u = x ≫ v) : u = v := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  haveI : IsReduced X.left := by
    obtain ⟨c, hc⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
    have he : c.hom.Etale := by
      rw [← HasRingHomProperty.Spec_iff (P := @Etale), hc]; infer_instance
    letI := c.hom.toAlgebra
    haveI : Algebra.Etale K Γ(X.left, ⊤) := he
    haveI : _root_.IsReduced Γ(X.left, ⊤) := Algebra.FormallyUnramified.isReduced_of_field K _
    exact isReduced_of_isAffine_isReduced _
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq _ _ Y.hom Set.univ dense_univ (fun z _ => ?_) (by simp)
  let F := AlgebraicClosure (X.left.residueField z)
  let i := spMap (algebraMap (X.left.residueField z) F)
  obtain ⟨c, hc⟩ := Spec.map_surjective ((i ≫ X.left.fromSpecResidueField z) ≫ X.hom)
  letI : Algebra K F := c.hom.toAlgebra
  obtain ⟨σ, x', e⟩ := exists_factor X hX F _ hc.symm
  have : Epi i := by
    have : Flat i := inferInstance
    have : Surjective i :=
      ⟨fun _ => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum (X.left.residueField z)) _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi i, ← Category.assoc, ← Category.assoc]
  erw [e]
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun g => _ ≫ g.left) (h x')

variable {R : Type} [CommRing R] [IsDomain R]

end GlobalTheory.GenTorsMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaObjectFamilyOpenClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentVectorZeroOfObjectConstantAlong
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentVectorZeroOfObjectConstantAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem tangent_eq_constPt_of_tMap : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (u : TObj g (N' ^ 2) J b Y.s), Odd N' → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ Y.MM) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), x ≫ Y.s = constPt x ≫ Y.s → TMap t u x → TMap t u (constPt x) → x = constPt x := by
  intro hL hL2 o _ g n N' J b I Y u hN hu K _ x t hs h1 h2
  have hsub : Subsingleton (PrimeSpectrum (DualNumber K)) := by
    have key : ∀ p : PrimeSpectrum (DualNumber K),
        p.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom := by
      intro p
      have hp := p.isPrime
      have hle : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom ≤ p.asIdeal := by
        intro a ha
        have ha' : a.fst = 0 := ha
        apply hp.mem_of_pow_mem 2
        have : a ^ 2 = 0 := by
          rw [sq]; ext <;> simp [ha']
        rw [this]; exact p.asIdeal.zero_mem
      have hmax : (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).IsMaximal :=
        RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨TrivSqZeroExt.inl c, rfl⟩)
      exact (hmax.eq_of_le hp.ne_top hle).symm
    exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩
  have hsub' : Subsingleton (Sp (DualNumber K)) := hsub
  obtain ⟨p⟩ : Nonempty (Sp (DualNumber K)) := inferInstanceAs (Nonempty (PrimeSpectrum (DualNumber K)))
  obtain ⟨R, _, j, v, hj, ⟨q, _⟩, hv⟩ := GlobalTheory.T.exists_thetaConstants_locally_on_base hL hL2 o g N' J b _ _ t hN p
  have hsurj : Function.Surjective j := fun y => ⟨q, Subsingleton.elim _ _⟩
  have hiso : IsIso j := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext y
    simpa using hsurj y
  have c1 := (hu R _ v).1 ((GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ u _ _ t x R j v h1).1 hv)
  have c2 := (hu R _ v).1 ((GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ u _ _ t (constPt x) R j v h2).1 hv)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (R := CommRingCat.of o) (S := CommRingCat.of R) (j ≫ x ≫ Y.s)
  have e1 : (j ≫ x) ≫ Y.s = spMap β.hom := by
    rw [Category.assoc]; exact hβ.symm
  have e2 : (j ≫ constPt x) ≫ Y.s = spMap β.hom := by
    rw [Category.assoc, ← hs]; exact hβ.symm
  have h := (Y.pts R β.hom v (Y.loc R β.hom _ v e1 c1)).unique ⟨e1, c1⟩ ⟨e2, c2⟩
  exact (cancel_epi j).1 h

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentVectorZeroOfObjectConstantAlongStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVector_zero_of_object_constant_along : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (u : TObj g (N' ^ 2) J b Y.s), Odd N' → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ Y.MM) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), x ≫ Y.s = constPt x ≫ Y.s → TMap t u x → TMap t u (constPt x) → x = constPt x := by
  first | exact @GlobalTheory.ZM.tangent_eq_constPt_of_tMap | exact GlobalTheory.ZM.tangent_eq_constPt_of_tMap | (intros; apply GlobalTheory.ZM.tangent_eq_constPt_of_tMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaObjectFamilyOpenClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.ThetaFamily

theorem exists_coord_of_isLocalRing {X : Scheme.{0}} {M : LB X} {σ : Type} (th : σ → M.Sec) (hM : M.IsLB)
    {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X) : ∃ v, SecCoord M th x v := by
  obtain ⟨k, hk⟩ : ∃ k, x (IsLocalRing.closedPoint R) ∈ M.U k :=
    TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge trivial)
  refine GlobalTheory.SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  exact ((IsLocalRing.specializes_closedPoint y).map x.continuous).mem_open (M.U k).isOpen hk

theorem nonempty_thetaFam : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → Nonempty (ThetaFam n em C) := by
  intro h₁ h₂ hcrit g J _ Mat κ n w w' hn hodd
  obtain ⟨j₁, hglue⟩ := GlobalTheory.T.exists_thetaFamily_over_thetaPointScheme h₁ h₂ hcrit g J Mat κ n w w' hn hodd
  obtain ⟨j₂, hrep⟩ := GlobalTheory.T.thetaIdealFamily_universal_property h₁ h₂ g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em C d hb hC => ?_⟩
  have := hb.1
  obtain ⟨i₁, i₂, i₃⟩ := GlobalTheory.T.thetaPointsVanishingIdeal_radical_homogeneous o g (n ^ j) J b em C hb.2.2
  obtain ⟨Y⟩ := GlobalTheory.ZM.nonempty_MMPre o g n (n ^ j) (thIdeal em C) (pow_pos hn.pos j) i₁ i₂ i₃
  obtain ⟨t, hd, -, hth, hfib⟩ := hglue j (le_of_max_le_left hj) o b em C d hb hC Y
  refine ⟨{ MM := Y.MM
            s := Y.s
            qproj := Y.qproj
            flat := Y.flat
            reduced := Y.reduced
            univ := t
            dense := hd
            loc := fun R _ _ β x hx => ?_
            pts := fun R _ β v hv => ?_
            rep := hrep j (le_of_max_le_right hj) o b em C d hb hC Y t hth hfib
            unram := GlobalTheory.T.tangentVector_zero_of_object_constant_along h₁ h₂ o g n (n ^ j) J b _ Y t hodd.pow hth }⟩
  · obtain ⟨v, hv⟩ := exists_coord_of_isLocalRing Y.th Y.isLB x
    exact ⟨v, (hth R x v).2 hv, Y.loc R β x v hx hv⟩
  · simpa only [hth] using Y.pts R β v hv

end GlobalTheory.ZM.ThetaFamily
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaObjectFamilyOpenClosureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_thetaObject_family_open_closure : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → Nonempty (ThetaFam n em C) := by
  first | exact @GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam | exact GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam | (intros; apply GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam <;> assumption)
end
end
