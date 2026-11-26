module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNull
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNull
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf : ∀ (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp ℤ) (σ : ℤ →+* ℂ) (D : ℕ) (c : GlobalTheory.AlgChart q σ D) (W : X.Opens)
    (h : genericPoint X ∈ W) (g : Γ(X, W)), fnOf W h g ≠ 0 →
    volume (c.e.target ∩ c.e.symm ⁻¹' {y | y ∈ ptsIn q σ W ∧ ev q σ W g y = 0}) = 0 := by
  intro X _ q σ D c W h g hg
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · have ht : c.e.target = ∅ := by rw [← c.e.image_source_eq_target, hs, Set.image_empty]
    simp [ht]
  have sectionFrameQuotient := mem_ptsIn.1 (c.source_subset hy0)
  haveI : Nonempty c.U := ⟨⟨_, sectionFrameQuotient⟩⟩
  have hgU : genericPoint X ∈ c.U := gen_mem sectionFrameQuotient
  haveI := functionField_isFractionRing_of_isAffineOpen X c.U c.affine
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, c.U)) (fnOf W h g)
  have hal : ∀ t : Γ(X, c.U), algebraMap Γ(X, c.U) X.functionField t = fnOf c.U hgU t :=
    fun _ => rfl
  rw [hal, hal] at hab
  have hb0 : fnOf c.U hgU b ≠ 0 := fun e =>
    nonZeroDivisors.ne_zero hb ((map_eq_zero_iff _ (fnOf_injective _ _)).1 e)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hg
    rw [← hab, map_zero, zero_div]
  have hrel : fnOf W h g * fnOf c.U hgU b = fnOf c.U hgU a := by
    rw [← hab, div_mul_cancel₀ _ hb0]
  have hI : genericPoint X ∈ W ⊓ c.U := ⟨h, hgU⟩
  have hres : resG X (inf_le_left : W ⊓ c.U ≤ W) g * resG X (inf_le_right : W ⊓ c.U ≤ c.U) b =
      resG X (inf_le_right : W ⊓ c.U ≤ c.U) a := by
    apply fnOf_injective _ hI
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG]
    exact hrel
  obtain ⟨Q, hQ, r, hQr⟩ := GlobalTheory.ChernNull.exists_poly_dvd _ c.etale a ha0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ (RingHom.injective_int σ) (by rw [e, map_zero]))
  refine measure_mono_null ?_ (GlobalTheory.ChernNull.volume_poly_zero D _ hP)
  rintro v ⟨hv, hyW, hyz⟩
  have hys : c.e.symm v ∈ c.e.source := c.e.map_target hv
  have hyU := c.source_subset hys
  have hyI : c.e.symm v ∈ ptsIn q σ (W ⊓ c.U) := mem_ptsIn_inf.2 ⟨hyW, hyU⟩
  have hay : ev q σ c.U a (c.e.symm v) = 0 := by
    rw [← ev_res inf_le_right hyI, ← hres, ev_mul, ev_res inf_le_left hyI, hyz, zero_mul]
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun i => c.e (c.e.symm v) i) := by
    refine MvPolynomial.ringHom_ext (fun i => ?_) (fun i => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq _ hys]
  have hQy := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at hQy
  show MvPolynomial.eval (fun i => v i) (MvPolynomial.map σ Q) = 0
  rw [c.e.right_inv hv] at hQy
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← hQy, hQr, map_mul, ← ev_eq hyU, hay,
    zero_mul]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNullStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zero_locus_regular_function_null : ∀ (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp ℤ) (σ : ℤ →+* ℂ) (D : ℕ) (c : GlobalTheory.AlgChart q σ D) (W : X.Opens)
    (h : genericPoint X ∈ W) (g : Γ(X, W)), fnOf W h g ≠ 0 →
    volume (c.e.target ∩ c.e.symm ⁻¹' {y | y ∈ ptsIn q σ W ∧ ev q σ W g y = 0}) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf | exact GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf | (intros; apply GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibres
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibres
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AbFibre

theorem isPullback_baseChange {S T : Scheme.{0}} (s : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((Over.pullback s).map f).left (pullback.fst X.hom s) (pullback.fst Y.hom s) f.left := by
  have h1 : ((Over.pullback s).map f).left ≫ pullback.snd Y.hom s = pullback.snd X.hom s := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  have h2 : ((Over.pullback s).map f).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ f.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hX : f.left ≫ Y.hom = X.hom := Over.w f
  refine IsPullback.of_right ?_ h2 (IsPullback.of_hasPullback Y.hom s).flip
  rw [h1, hX]
  exact (IsPullback.of_hasPullback X.hom s).flip

theorem exists_geometric_point {S : Scheme.{0}} (Y : Over S) (y : Y.left) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (s : Spec (.of Ω) ⟶ S) (w : ↥(pullback Y.hom s)),
      pullback.fst Y.hom s w = y := by
  let Ω := AlgebraicClosure (Y.left.residueField y)
  let g : Spec (.of Ω) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) Ω)) ≫ Y.left.fromSpecResidueField y
  let L : Spec (.of Ω) ⟶ pullback Y.hom (g ≫ Y.hom) := pullback.lift g (𝟙 _) (by simp)
  let pt : ↥(Spec (.of Ω)) := IsLocalRing.closedPoint Ω
  refine ⟨Ω, inferInstance, inferInstance, g ≫ Y.hom, L pt, ?_⟩
  change (L ≫ pullback.fst Y.hom (g ≫ Y.hom)) pt = y
  rw [pullback.lift_fst]
  exact Scheme.fromSpecResidueField_apply y _

theorem finiteOfFibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  intro R _ A B _ _ l hA hB _ hfib
  haveI := hA
  haveI := hB
  have hcomp : l.left ≫ B.hom = A.hom := Over.w l
  haveI : IsProper A.hom := IsAbelianScheme.proper (A := A)
  haveI : IsProper B.hom := IsAbelianScheme.proper (A := B)
  haveI : IsProper (l.left ≫ B.hom) := by rw [hcomp]; infer_instance
  haveI : IsProper l.left := IsProper.of_comp l.left B.hom
  have lift : ∀ {T : Scheme.{0}} (s : T ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (x : ↥A.left)
      (w : ↥(pullback B.hom s)), pullback.fst B.hom s w = l.left x →
      ∃ v, ((Over.pullback s).map l).left v = w ∧ pullback.fst A.hom s v = x := by
    intro T s x w hxw
    have h := isPullback_baseChange s l
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := pullback.fst B.hom s) (g := l.left) w x hxw
    refine ⟨h.isoPullback.inv z, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
    · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]
  have hfin : ∀ y : ↥B.left, (l.left ⁻¹' {y}).Finite := by
    intro y
    obtain ⟨Ω, _, _, s, w, hw⟩ := exists_geometric_point B y
    have hF : IsFinite ((Over.pullback s).map l).left := (hfib Ω s).1
    refine ((Scheme.Hom.finite_preimage_singleton ((Over.pullback s).map l).left w).image
      (pullback.fst A.hom s)).subset ?_
    intro x hx
    have hx' : l.left x = y := hx
    obtain ⟨v, hv1, hv2⟩ := lift s x w (by rw [hw, hx'])
    exact ⟨v, hv1, hv2⟩
  have hsurj : Surjective l.left := by
    refine ⟨fun y => ?_⟩
    obtain ⟨Ω, _, _, s, w, hw⟩ := exists_geometric_point B y
    have hS : Surjective ((Over.pullback s).map l).left := (hfib Ω s).2
    obtain ⟨v, hv⟩ := hS.surj w
    refine ⟨pullback.fst A.hom s v, ?_⟩
    have hsq := (isPullback_baseChange s l).w
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply, hv, hw]
  haveI : LocallyQuasiFinite l.left := LocallyQuasiFinite.of_finite_preimage_singleton l.left hfin
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite l.left, hsurj⟩

end GlobalTheory.CompanionTheory.AbFibre
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibresStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_finite_fibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  first | exact @GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | exact GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | (intros; apply GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFiniteFlat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFiniteFlat
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open GlobalTheory.CompanionTheory.Ar.GR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.KerFF

variable {R : Type} [CommRing R]

theorem exists_sp_iso (X : Over (Sp R)) [IsFinite X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom] :
    ∃ (F : Type) (_ : CommRing F) (_ : Algebra R F) (_ : Nonempty (sp (R₀ := R) F ≅ X)),
      Module.Finite R F ∧ Module.Projective R F := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  have f₁ : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have f₂ : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have f₃ : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at f₁
  rw [Flat.SpecMap_iff] at f₂
  rw [LocallyOfFinitePresentation.SpecMap_iff] at f₃
  letI : Algebra R Γ(X.left, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite R Γ(X.left, ⊤) := RingHom.finite_algebraMap.1 f₁
  haveI : Module.Flat R Γ(X.left, ⊤) := RingHom.flat_algebraMap_iff.1 f₂
  haveI : Algebra.FinitePresentation R Γ(X.left, ⊤) := RingHom.finitePresentation_algebraMap.1 f₃
  haveI : Module.FinitePresentation R Γ(X.left, ⊤) := Module.FinitePresentation.of_finite_of_finitePresentation _ _
  refine ⟨Γ(X.left, ⊤), inferInstance, inferInstance,
    ⟨Over.isoMk X.left.isoSpec.symm ?_⟩, inferInstance, Module.Flat.projective_of_finitePresentation⟩
  exact hφ.symm

theorem mul_comp_hom {A B T : Over (Sp R)} [GrpObj A] [GrpObj B] (u v : T ⟶ A) (l : A ⟶ B) [IsMonHom l] :
    (u * v) ≫ l = (u ≫ l) * (v ≫ l) := by
  rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem one_comp_hom {A B T : Over (Sp R)} [GrpObj A] [GrpObj B] (l : A ⟶ B) [IsMonHom l] :
    (1 : T ⟶ A) ≫ l = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem kernelFinFlat : PositivityTheory.Tls2.Zar3.Ch1.KernelFinFlat := by
  intro R _ A B _ _ l hA hB hl hfin hflat
  haveI := hA.smooth
  haveI := hB.smooth
  haveI : IsFinite l.left := hfin
  haveI : Flat l.left := hflat
  haveI : IsMonHom l := hl
  have hw : l.left ≫ B.hom = A.hom := Over.w l
  haveI : LocallyOfFinitePresentation (l.left ≫ B.hom) := by rw [hw]; infer_instance
  haveI : LocallyOfFinitePresentation l.left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp l.left B.hom
  let e : Sp R ⟶ B.left := (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left
  have he : e ≫ B.hom = 𝟙 _ := Over.w (η[B] : 𝟙_ (Over (Sp R)) ⟶ B)
  haveI : Mono e := mono_of_mono_fac he
  let X : Over (Sp R) := Over.mk (pullback.snd l.left e)
  haveI : IsFinite X.hom := inferInstanceAs (IsFinite (pullback.snd l.left e))
  haveI : Flat X.hom := inferInstanceAs (Flat (pullback.snd l.left e))
  haveI : LocallyOfFinitePresentation X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd l.left e))
  have hf : pullback.fst l.left e ≫ A.hom = X.hom := by
    rw [← hw, pullback.condition_assoc, he, Category.comp_id]
    rfl
  let f : X ⟶ A := Over.homMk (pullback.fst l.left e) hf
  have key : ∀ (T : Over (Sp R)) (z : T ⟶ A), z ≫ l = 1 ↔ ∃ t : T ⟶ X, t ≫ f = z := by
    intro T z
    have one_left : (1 : T ⟶ B).left = T.hom ≫ e := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    constructor
    · intro h
      have h' : z.left ≫ l.left = T.hom ≫ e := by
        rw [← one_left, ← h, Over.comp_left]
      refine ⟨Over.homMk (pullback.lift z.left T.hom h') (pullback.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    · rintro ⟨t, rfl⟩
      apply Over.OverMorphism.ext
      rw [one_left, ← Over.w t]
      change (t.left ≫ pullback.fst l.left e) ≫ l.left = (t.left ≫ pullback.snd l.left e) ≫ e
      rw [Category.assoc, Category.assoc, pullback.condition]
  have fmono : ∀ {T : Over (Sp R)} (t t' : T ⟶ X), t ≫ f = t' ≫ f → t = t' := by
    intro T t t' h
    apply Over.OverMorphism.ext
    rw [← cancel_mono (pullback.fst l.left e)]
    exact congrArg (fun u => u.left) h
  obtain ⟨F, iF, aF, ⟨ee⟩, hfinF, hproj⟩ := exists_sp_iso X
  have ker : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
      z ≫ l = 1 ↔ ∃ φ : F →ₐ[R] S, spMap φ ≫ (ee.hom ≫ f) = z := by
    intro S _ _ z
    rw [key]
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨φ, hφ⟩ := GlobalTheory.NatFun.spMap_surjective (k := R) (A := F) (B := S) (t ≫ ee.inv)
      exact ⟨φ, by rw [hφ]; simp⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨spMap φ ≫ ee.hom, by simp⟩
  refine ⟨F, iF, aF, ee.hom ≫ f, ⟨hproj, hfinF, ?_, ?_, ?_, ?_⟩, ker⟩
  · intro S _ _ φ φ' h
    apply GlobalTheory.NatFun.spMap_injective (k := R) (A := F) (B := S)
    have h₁ : (spMap φ ≫ ee.hom) ≫ f = (spMap φ' ≫ ee.hom) ≫ f := by simpa using h
    exact (cancel_mono ee.hom).1 (fmono _ _ h₁)
  · intro S _ _
    exact (ker S 1).1 (one_comp_hom l)
  · intro S _ _ φ φ'
    exact (ker S _).1 (by
      rw [mul_comp_hom, (ker S _).2 ⟨φ, rfl⟩, (ker S _).2 ⟨φ', rfl⟩, _root_.mul_one])
  · intro S _ _ φ
    have hz := (ker S _).2 ⟨φ, rfl⟩
    have h₂ : (spMap φ ≫ ee.hom ≫ f)⁻¹ ≫ l = 1 := by
      have h₃ := mul_comp_hom (spMap φ ≫ ee.hom ≫ f)⁻¹ (spMap φ ≫ ee.hom ≫ f) l
      rw [inv_mul_cancel, one_comp_hom, hz, _root_.mul_one] at h₃
      exact h₃.symm
    obtain ⟨χ, hχ⟩ := (ker S _).1 h₂
    exact ⟨χ, by rw [hχ, inv_mul_cancel]⟩

end GlobalTheory.CompanionTheory.Ar.KerFF
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFiniteFlatStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.KernelFinFlat := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat | exact GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat | (intros; apply GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat <;> assumption)
end
end
