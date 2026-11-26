module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRootOfExp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DefRead

variable {K : Type} [Field K]

def VC (σ : K →+* ℂ) (W : Type) [AddCommGroup W] [Module K W] : Type :=
  @TensorProduct K _ ℂ W _ _ (σ.toAlgebra.toModule) _

variable (σ : K →+* ℂ) (W : Type) [AddCommGroup W] [Module K W]

instance : AddCommGroup (VC σ W) := @TensorProduct.addCommGroup K _ ℂ W _ _ (σ.toAlgebra.toModule) _

instance : Module ℂ (VC σ W) := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact (TensorProduct.leftModule : Module ℂ (ℂ ⊗[K] W))

instance [FiniteDimensional K W] : FiniteDimensional ℂ (VC σ W) := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact (inferInstance : FiniteDimensional ℂ (ℂ ⊗[K] W))

variable {W}

def bcLin (f : W →ₗ[K] W) : VC σ W →ₗ[ℂ] VC σ W := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact LinearMap.baseChange ℂ f

def tm1 (w : W) : VC σ W := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact (1 : ℂ) ⊗ₜ[K] w

theorem complexificationBaseChangeLinear_one_tmul (f : W →ₗ[K] W) (w : W) : bcLin σ f (tm1 σ w) = tm1 σ (f w) := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact LinearMap.baseChange_tmul (A := ℂ) f 1 w

theorem bcLin_one : bcLin σ (1 : W →ₗ[K] W) = 1 := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact LinearMap.baseChange_id (R := K) (A := ℂ) (M := W)

theorem bcLin_mul (f g : W →ₗ[K] W) : bcLin σ (f * g) = bcLin σ f * bcLin σ g := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact LinearMap.baseChange_comp (A := ℂ) g f

variable {G : Type} [Group G]

def twBC (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) : Representation ℂ G (VC σ W) where
  toFun g := σ (((χ g)⁻¹ : Kˣ) : K) • bcLin σ (ρ0 g)
  map_one' := by simp [bcLin_one]
  map_mul' g h := by
    rw [map_mul, map_mul, bcLin_mul, smul_mul_smul_comm, mul_inv_rev, Units.val_mul, map_mul, mul_comm (σ _)]

theorem twBC_apply (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) (g : G) :
    twBC σ ρ0 χ g = σ (((χ g)⁻¹ : Kˣ) : K) • bcLin σ (ρ0 g) := rfl

end GlobalTheory.DefRead

namespace GlobalTheory.DefRead

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

abbrev VAt (p : PtAt ex Csz) (i : Fin D.R.m) : Type := VC D.what₂.embLL (Fin (p.R.nW i) → D.what₂.LL)

def repAt (p : PtAt ex Csz) (i : Fin D.R.m) : Representation ℂ (G0g D.nd) (VAt p i) :=
  (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi).comp (p.R.eG.trans p.cG).symm.toMonoidHom

theorem repAt_apply (p : PtAt ex Csz) (i : Fin D.R.m) (g : G0g D.nd) :
    repAt p i g = twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi ((p.R.eG.trans p.cG).symm g) := rfl

end GlobalTheory.DefRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveField
noncomputable section

namespace GlobalTheory.FixedPoint

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.CompRat GlobalTheory.CompRat.FixedConst
  GlobalTheory.AllWt GlobalTheory.FlatLine

theorem exists_descent {Y : Scheme.{0}} (K : IntermediateField ℚ ℂ) (x : Sp ℂ ⟶ Y)
    (hx : ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ K, τ a = a) → spMap (τ : ℂ →+* ℂ) ≫ x = x) :
    ∃ g : Sp K ⟶ Y, spMap (algebraMap K ℂ) ≫ g = x := by
  classical
  obtain ⟨⟨y, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField ℂ Y).symm.surjective x
  have hfix : ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ K, τ a = a) → φ ≫ CommRingCat.ofHom (τ : ℂ →+* ℂ) = φ := by
    intro τ hτ
    have e : spMap (τ : ℂ →+* ℂ) ≫ (Scheme.SpecToEquivOfField ℂ Y).symm ⟨y, φ⟩ =
        (Scheme.SpecToEquivOfField ℂ Y).symm ⟨y, φ ≫ CommRingCat.ofHom (τ : ℂ →+* ℂ)⟩ := by
      change Spec.map _ ≫ Spec.map φ ≫ _ = Spec.map (φ ≫ _) ≫ _
      rw [Spec.map_comp, Category.assoc]
    have h2 := (Scheme.SpecToEquivOfField ℂ Y).symm.injective (e.symm.trans (hx τ hτ))
    exact eq_of_heq (Sigma.mk.inj_iff.mp h2).2
  have hmem : ∀ r, φ.hom r ∈ K := by
    intro r
    obtain ⟨a, ha⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := K) (φ.hom r) (fun σ => by
      have h := hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩)
      exact congrArg (fun f => f.hom r) h)
    rw [← ha]
    exact a.2
  let ψ : Y.residueField y →+* K := φ.hom.codRestrict K hmem
  refine ⟨Spec.map (CommRingCat.ofHom ψ : Y.residueField y ⟶ CommRingCat.of K) ≫ Y.fromSpecResidueField y, ?_⟩
  have hc : (CommRingCat.ofHom ψ : Y.residueField y ⟶ CommRingCat.of K) ≫ CommRingCat.ofHom (algebraMap K ℂ) = φ := by
    ext r
    rfl
  exact (Spec.map_comp_assoc _ _ _).symm.trans (congrArg (· ≫ Y.fromSpecResidueField y) (congrArg Spec.map hc))

theorem ev_eq_of_restrict {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (W : Y.Opens) (p : Sp ℂ) (hp : x p ∈ W) (f : Γ(Y, ⊤))
    (n : ℕ) (hf : Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op f = n) : ev x f = n := by
  have hr : Set.range x ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q p]
  have hf' : (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom f = n := hf
  have hle : W.ι ''ᵁ ⊤ ≤ W := (Scheme.Opens.ι_image_top W).le
  have e : (homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)).op = (homOfLE (le_top : W ≤ ⊤)).op ≫ (homOfLE hle).op := rfl
  have key : (Y.presheaf.map (homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)).op).hom f = n := by
    rw [e, Functor.map_comp]
    exact (congrArg (Y.presheaf.map (homOfLE hle).op).hom hf').trans (map_natCast _ n)
  rw [← IsOpenImmersion.lift_fac W.ι x hr, ev_comp, Scheme.Opens.ι_appTop]
  exact (congrArg _ key).trans (map_natCast _ n)

theorem exists_indicator {Y : Scheme.{0}} {Z : Set Y} (hZ : IsClopen Z) :
    ∃ f : Γ(Y, ⊤), ∀ (x : Sp ℂ ⟶ Y) (p : Sp ℂ), (x p ∈ Z → ev x f = 1) ∧ (x p ∉ Z → ev x f = 0) := by
  let V : Y.Opens := ⟨Z, hZ.isOpen⟩
  let W : Y.Opens := ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩
  have hVW : V ⊔ W = ⊤ := by
    apply TopologicalSpace.Opens.ext
    simp [V, W, Set.union_compl_self]
  have hdis : Disjoint V W := by
    rw [disjoint_iff]
    apply TopologicalSpace.Opens.ext
    simp [V, W]
  obtain ⟨f, hfV, hfW⟩ := exists_extension_zero V W hVW hdis 1
  refine ⟨f, fun x p => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have h := ev_eq_of_restrict x V p hp f 1 (by rw [hfV, Nat.cast_one])
    simpa using h
  · have h := ev_eq_of_restrict x W p hp f 0 (by rw [hfW, Nat.cast_zero])
    simpa using h

private theorem exists_isTypeFn' {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q : ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, fun τ => ?_⟩
  have hcard : Nat.card {i // (e.symm i).1 = τ} = m τ := by
    rw [Nat.card_congr (e.symm.subtypeEquiv (p := fun i => (e.symm i).1 = τ) (q := fun s => s.1 = τ)
      (fun _ => Iff.rfl)), Nat.card_congr (Equiv.sigmaSubtype τ), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]; simp [m, h]
  · rw [hcard]; simp [m, h]

private theorem spMap_comp_spMap_divisor {R₀ R R' : Type} [CommRing R₀] [CommRing R] [CommRing R'] (f : R →+* R')
    (g : R₀ →+* R) : spMap f ≫ spMap g = spMap (f.comp g) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_fixed_point (hD : 1 ≤ Dw.p + Dw.q)
    (hsig : Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) (Z : Comp Xo c) :
    ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ strK = spMap (algebraMap c.F ℂ) ∧ (∀ p, x p ∈ (Z : Set (Xo.XF c))) ∧
      ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ c.F, τ a = a) → FixesCurve H τ l.M' → spMap (τ : ℂ →+* ℂ) ≫ x = x := by
  classical
  obtain ⟨g, ty, hty⟩ := exists_isTypeFn' H Dw.p Dw.q
  let σ₀ : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  have hσ₀ : σ₀ (baseKA l).ρ = H.rt0 := rfl
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo σ₀ g ty hD hσ₀ hty

  obtain ⟨L, _, _, j, g₀, hg₀, hZ₀⟩ := GlobalTheory.FlatLine.exists_numberField_point Z
  letI : Algebra c.F L := j.toAlgebra
  haveI : IsScalarTower ℚ c.F L := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ c.F), eq_ratCast (algebraMap ℚ L), map_ratCast])
  haveI : Algebra.IsAlgebraic c.F L := Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let φ : L →ₐ[c.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hφ : (φ : L →+* ℂ).comp j = algebraMap c.F ℂ := RingHom.ext fun a => φ.commutes a
  obtain ⟨hx₀, hZx₀⟩ := GlobalTheory.FlatLine.point_ext hg₀ hZ₀ (φ : L →+* ℂ)
  rw [hφ] at hx₀
  set x₀ : Sp ℂ ⟶ Xo.XF c := spMap (φ : L →+* ℂ) ≫ g₀ with hx₀def
  have hover : x₀ ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap σ₀ := by
    rw [pullback.condition, ← Category.assoc]
    erw [hx₀]
    rw [spMap_comp_spMap_divisor]
  obtain ⟨i, P, hP, hPx⟩ := F.onto _ (by rw [Category.assoc]; exact hover)
  obtain ⟨P', hP', hs⟩ := GlobalTheory.CompRat.exists_isSplit_period_anyLevel E H Dw l Xo σ₀ g ty F hD hσ₀ hty hsig i
  have hcond : F.u i P' ≫ Xo.s = spMap (algebraMap c.F ℂ) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.over_σ i P' hP', spMap_comp_spMap_divisor]
  let xs : Sp ℂ ⟶ Xo.XF c := pullback.lift (F.u i P') (spMap (algebraMap c.F ℂ)) hcond
  have hxs₁ : xs ≫ pullback.fst _ _ = F.u i P' := pullback.lift_fst _ _ _
  have hxs₂ : xs ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) := pullback.lift_snd _ _ _

  obtain ⟨f, hf⟩ := exists_indicator (GlobalTheory.TrivOrderTieCompare.isClopen_comp Z)
  have hvals : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      valAt' x ⊤ f ∈ ({0, 1} : Set ℂ) := by
    intro x _
    rw [valAt'_top]
    by_cases hx : x default ∈ (Z : Set (Xo.XF c))
    · simp [(hf x default).1 hx]
    · simp [(hf x default).2 hx]
  have heq := GlobalTheory.CompRat.valAt_eq_of_finite_values_anyLevel E H Dw l Xo σ₀ g ty F hD hσ₀ hty c
    (algebraMap c.F ℂ) f _ (Set.toFinite _) hvals i P P' hP hP' x₀ xs hPx.symm hx₀ hxs₁ hxs₂
  rw [valAt'_top, valAt'_top, (hf x₀ default).1 (hZx₀ default)] at heq
  refine ⟨xs, hxs₂, fun p => ?_, fun τ hτ hfix => ?_⟩
  · by_contra hp
    rw [(hf xs p).2 hp] at heq
    exact one_ne_zero heq
  · have hτσ : (τ : ℂ →+* ℂ).comp σ₀ = σ₀ := RingHom.ext fun a => hτ _ (IntermediateField.inclusion c.le a).2
    have hfixed := GlobalTheory.CompRat.AnyLevel.conj_point_eq_of_isSplit F hD hσ₀ hty τ hτσ hfix i P' hP' hs
    apply pullback.hom_ext
    · rw [Category.assoc, hxs₁, hfixed]
    · rw [Category.assoc, hxs₂, spMap_comp_spMap_divisor]
      congr 1
      exact RingHom.ext fun a => hτ a a.2

end GlobalTheory.FixedPoint

namespace GlobalTheory.FixedPoint

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
open AlgebraicGeometry CategoryTheory

theorem exists_frPt_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (hle : c.F ≤ K), GlobalTheory.CompRat.CurveOver H K l.M' → ∀ Z : Comp Xo c, (letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra; ∃ y : FrPt Xo c K, LiesOn Z y) := by
  intro E _ _ _ H Dw l Xo c hD hsig K _ hle hK Z
  letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  obtain ⟨x, _, hxZ, hxfix⟩ := exists_fixed_point (H := H) (Xo := Xo) (c := c) hD hsig Z
  obtain ⟨g, hg⟩ := exists_descent K x (fun τ hτ => hxfix τ (fun a ha => hτ a (hle ha)) (hK τ hτ))
  have hcancel : ∀ a b : Sp K ⟶ Sp c.F, spMap (algebraMap K ℂ) ≫ a = spMap (algebraMap K ℂ) ≫ b → a = b := by
    intro a b hab
    rw [← Spec.map_preimage a, ← Spec.map_preimage b] at hab ⊢
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hab
    congr 1
    ext r
    exact congrArg (fun f => f.hom r) hab
  have hgK : g ≫ strK = spMap (algebraMap c.F K) := by
    apply hcancel
    rw [← Category.assoc, hg, ‹x ≫ strK = spMap (algebraMap c.F ℂ)›, spMap_comp_spMap_divisor]
    rfl
  have hfr : ∀ (x : Sp K ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c K), ∃ y : FrPt Xo c K, y.x = x := by
    intro x hx
    choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
    obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist x
    exact ⟨⟨x, hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl⟩
  obtain ⟨y, hy⟩ := hfr (g ≫ GlobalTheory.FlatLine.prX Xo c) (GlobalTheory.FlatLine.prX_over hgK)
  refine ⟨y, fun s => ?_⟩
  rw [GlobalTheory.FlatLine.ptF_eq hgK hy]
  have hs : s = spMap (algebraMap K ℂ) default := Subsingleton.elim _ _
  have h1 := hxZ default
  rw [← hg] at h1
  rw [hs]
  exact h1

end GlobalTheory.FixedPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveFieldStatement
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoint_liesOn_component_cmCurve_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (hle : c.F ≤ K), GlobalTheory.CompRat.CurveOver H K l.M' → ∀ Z : Comp Xo c, (letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra; ∃ y : FrPt Xo c K, LiesOn Z y) := by
  first | exact @GlobalTheory.FixedPoint.exists_frPt_liesOn | exact GlobalTheory.FixedPoint.exists_frPt_liesOn | (intros; apply GlobalTheory.FixedPoint.exists_frPt_liesOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedPointCompletionIndexOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedPointCompletionIndexOne
open AlgebraicGeometry CategoryTheory
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.CompletionPoint

theorem exists_intFr_index_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ (Z : Comp Xo c) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (w : HeightOneSpectrum (𝓞 c.F)) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ a : c.F, vLa 𝔭 (algebraMap c.F K a) = vLa w a) → ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y' : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y' := by
  intro E _ _ _ H Dw l Xo c hpq hg Z K _ _ _ y hy w 𝔭 hv
  classical
  obtain ⟨hP, hN⟩ := GlobalTheory.Moduli.jointExistence_and_moduliScheme
  obtain ⟨O, _, β, Y, -, hPI, hbase⟩ := GlobalTheory.Frames.modelAtSt_of_good hP hN E H Dw l Xo c hpq hg w
  obtain ⟨T, k, hk, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K 𝔭
  have ho : OverLa w T.V (k.comp (algebraMap c.F K)) 1 :=
    ⟨Nat.one_pos, fun a => by rw [← hv a]; exact hk.2 _⟩
  obtain ⟨b, hb⟩ := hbase T _ 1 ho
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hIF : IntFramesSt Xo c := GlobalTheory.intFrames_of_laws GlobalTheory.abelianSchemeLaws_all.1.secBaseChange hT E H Dw l Xo c
  let _ := (k.comp (algebraMap c.F K)).toAlgebra
  have hz : ptF y ≫ Limits.pullback.snd _ _ = spMap (algebraMap c.F K) := Limits.pullback.lift_snd _ _ _
  have hs : (spMap k ≫ ptF y) ≫ Limits.pullback.snd _ _ = spMap (k.comp (algebraMap c.F K)) := by
    rw [Category.assoc, ← GlobalTheory.EtaVal.spMap_comp_spMap]
    exact congrArg _ hz
  have hx : ((spMap k ≫ ptF y) ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs, GlobalTheory.EtaVal.spMap_comp_spMap]
    rfl
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) _ hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y', t, hbor⟩ := intFr_of_model hIF T (k.comp (algebraMap c.F K)) Y hPI b hb y₀
  refine ⟨T, k.comp (algebraMap c.F K), y', ho, hfin, fun q => ?_⟩
  have h1 : y'.1.x = y₀.x := hbor.1
  have h2 : ptF y'.1 = spMap k ≫ ptF y := by
    apply Limits.pullback.hom_ext
    · exact (Limits.pullback.lift_fst _ _ _).trans (h1.trans h0)
    · exact (Limits.pullback.lift_snd _ _ _).trans hs.symm
  rw [h2]
  exact hy (spMap k q)

end GlobalTheory.CompletionPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedPointCompletionIndexOneStatement
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFramedPoint_completion_index_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ (Z : Comp Xo c) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (w : HeightOneSpectrum (𝓞 c.F)) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ a : c.F, vLa 𝔭 (algebraMap c.F K a) = vLa w a) → ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y' : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y' := by
  first | exact @GlobalTheory.CompletionPoint.exists_intFr_index_one | exact GlobalTheory.CompletionPoint.exists_intFr_index_one | (intros; apply GlobalTheory.CompletionPoint.exists_intFr_index_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnramifiedCurve
set_option autoImplicit false

namespace GlobalTheory.RefSum.UnramCurveField

section
open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.FieldSize.RayExistCurve
open scoped IntermediateField

theorem not_dvd_discr_of_unramIn (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {n q : ℕ} (hq : q.Prime) (hn : ¬ q ∣ n) (hK : ¬ (q : ℤ) ∣ discr K)
    (hL : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} → GlobalTheory.NT.UnramIn L 𝔭) :
    ¬ (q : ℤ) ∣ discr L := by
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  refine (not_dvd_discr_iff_forall_mem L (𝓞 L) hqz).2 fun P hP hqP => ?_
  have hqp : ((q : ℤ) : 𝓞 K) ∈ P.under (𝓞 K) := by
    rw [Ideal.mem_under, map_intCast]; exact hqP
  have hp0 : P.under (𝓞 K) ≠ ⊥ := fun e => by
    rw [e, Ideal.mem_bot] at hqp
    exact hq.ne_zero (by exact_mod_cast hqp)
  have h1 : Algebra.IsUnramifiedAt ℤ (P.under (𝓞 K)) :=
    (not_dvd_discr_iff_forall_mem K (𝓞 K) hqz).1 hK _ inferInstance hqp
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), inferInstance, hp0⟩
  have hnd : ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} := by
    rw [Ideal.dvd_span_singleton]
    intro hnp
    obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
    have h2 : ((a * q + b * n : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
      exact add_mem (Ideal.mul_mem_left _ _ hqp) (Ideal.mul_mem_left _ _ (by rwa [Int.cast_natCast]))
    rw [hab, Int.cast_one] at h2
    exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have : P.LiesOver 𝔭.asIdeal := ⟨rfl⟩
  have h3 : Algebra.IsUnramifiedAt (𝓞 K) P := GlobalTheory.NT.isUnramifiedAt_of_unramIn (hL 𝔭 hnd) P
  exact Algebra.IsUnramifiedAt.comp (P.under (𝓞 K)) P

theorem exists_field_of_rayField (hRF : GlobalTheory.NT.RayField) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n q : ℕ) (hn : 3 ≤ n) (hq : q.Prime) (hqn : ¬ q ∣ n) (hqd : ¬ q ∣ H.d) :
    ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ GlobalTheory.CompRat.CurveOver H F' n := by
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  obtain ⟨hfin, h2⟩ := finrank_adjoin hd0 H.sqrt_neg_disc_sq
  have hr0 : H.rt0 ∈ ℚ⟮H.rt0⟯ := IntermediateField.mem_adjoin_simple_self ℚ H.rt0
  generalize ℚ⟮H.rt0⟯ = K₀ at hfin h2 hr0
  have hNF : NumberField K₀ := NumberField.mk
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let φ : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : φ w = (1 + H.rt0) / 2 := by
    have := congrArg φ hw
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, φ ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  have hn0 : (n : 𝓞 K₀) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨L, _, _, _, hL⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hRF K₀ (Ideal.span {(n : 𝓞 K₀)})
    (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let ψ : L →ₐ[K₀] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e₀ : L ≃ₐ[K₀] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  have hfR : FiniteDimensional K₀ ψ.fieldRange := e₀.toLinearEquiv.finiteDimensional
  have hLR := fun (_ : NumberField ψ.fieldRange) => hL.of_algEquiv e₀
  generalize ψ.fieldRange = R at hfR hLR
  have hNR : NumberField R := NumberField.of_module_finite K₀ R
  obtain ⟨hab, hR⟩ := hLR hNR
  change IsRay R (Ideal.span {(n : 𝓞 K₀)}) at hR
  have hdR : ¬ (q : ℤ) ∣ discr R :=
    not_dvd_discr_of_unramIn K₀ R hq hqn (by rwa [hD, dvd_neg, Int.natCast_dvd_natCast]) hR.1
  refine ⟨R.restrictScalars ℚ, hNR, hdR, ?_⟩
  refine (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn E H _ n (by omega)).1
    (R.algebraMap_mem (⟨H.rt0, hr0⟩ : K₀)) fun P hP => ?_
  have hW := GlobalTheory.FieldSize.InRayAny.weberSet_subset K₀ h2 (by omega) P (fun z => ?_) n hn R hR
  · exact ⟨hW (Set.mem_insert _ _), fun s hs => hW (Set.mem_insert_of_mem _
      ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩
  · rw [hP]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, hc s.1 s.2⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a, b, rfl⟩ := hgen a
      exact ⟨(a, b), hc a b⟩

end

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

end GlobalTheory.RefSum.UnramCurveField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

section Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure TwLev (R : RealDat D A Ks) (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E))
    (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop where
  xi : ChrEq xi χ
  xi_fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  xi_triv : χ.TrivOn D.host.F
  xi_tame : ∀ v, χ.TameAt v
  Q_pl : IsTwistPlaces D.host.g Q
  Q_off : ∀ PP ∈ Q, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
    ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
  Q_de : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
    (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
      ∀ PP ∈ Q, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭
  Q_ram : ∀ PP, ¬ χ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP
  xiR : ∀ PP ∈ Q, IsRes χ PP (xiR PP)
  roots : ∀ PP ∈ Q, ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP))
  muVal : ∀ (i : Fin D.R.m) (P : Pl0), Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (Q : Set (Pl D.host.E))) →
    ∃ a : D.what₂.LLˣ, D.what₂.embLL (a : D.what₂.LL) = (((R.C.mu0 i * χ).val (R.pl P) : ℂˣ) : ℂ)
  half : ∀ PP ∈ Q, ∀ PP' ∈ Q, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
    PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))
  guard : ∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

theorem twLev_of_core {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (hG : QGuard R) (t : T0) :
    TwLev R (R.xiH t) (R.xi t) (R.Q t) (R.xiR t) :=
  { xi := hC.lev.xi t
    xi_fin := hC.lev.xi_fin t
    xi_triv := hC.lev.xi_triv t
    xi_tame := hC.lev.xi_tame t
    Q_pl := hC.lev.Q_pl t
    Q_off := hC.lev.Q_off t
    Q_de := fun p hp => by
      obtain ⟨𝔭, h𝔭⟩ := hC.lev.Q_de p hp
      exact ⟨𝔭, h𝔭, h𝔭 t⟩
    Q_ram := hC.lev.Q_ram t
    xiR := hC.lev.xiR t
    roots := fun PP hPP => hC.fam.roots t PP (Or.inr hPP)
    muVal := fun i P hP => by
      obtain ⟨g, c0R, c0L, ht⟩ := hC.fam.tie
      exact ⟨A.muVal i t P, hC.fam.muVal i t P ((ht.ok t P).2 hP)⟩
    half := hG.1 t
    guard := hG.2 t }

end Lev

section Laws

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def Laws (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)) : Prop :=
  GlobalTheory.Hk3.Core R F ∧ Finite T0 ∧ Nonempty (FWTie T R κ v₀) ∧ IoExt R ∧ QGuard R ∧ OMPins T R κ v₀ O j ∧ PhaseTie T R κ v₀ O ph j ∧
    BaseOf R j B

def Ext (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (j : Fin D.R.m)
    {T0' : Type} {A' : FamIn D.what₂.LL G Pl0 T0' D.R.m} (R' : RealDat D A' T.Q.c.F)
    (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)) : Prop :=
  (∀ τ, FixBase T R j τ → FixBase T R' j τ) ∧
    (∀ τ ζ Φ Φ', ConjFun (O' j) (κ j) τ ζ Φ Φ' → ConjFun (O j) (κ j) τ ζ Φ Φ') ∧
    (∀ (c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W) (u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ), ExtC R j (inC (O j).c') (O j).c0' c →
      (∀ ρ, (u ρ : (R.MW j (sg0 D A)).sm ρ) = v₀ j (sg0 D A) ρ) →
      ∃ (c' : VsV D j ℂ →ₗ[ℂ] (R'.cV j).W) (u' : ∀ ρ, lowT (R'.MW j (sg0 D A')) ρ), ExtC R' j (inC (O' j).c') (O' j).c0' c' ∧
        (∀ ρ, (u' ρ : (R'.MW j (sg0 D A')).sm ρ) = v₀' j (sg0 D A') ρ) ∧
        ∀ x, R'.ioP j (PiTensorProduct.tprod ℂ u') (c' x) = R.ioP j (PiTensorProduct.tprod ℂ u) (c x))

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} {j : Fin D.R.m}

theorem Ext.refl : Ext T R κ v₀ O j R v₀ O :=
  ⟨fun _ h => h, fun _ _ _ _ h => h, fun c u hc hu => ⟨c, u, hc, hu, fun _ => rfl⟩⟩

theorem Ext.trans {T1 T2 : Type} {A1 : FamIn D.what₂.LL G Pl0 T1 D.R.m} {A2 : FamIn D.what₂.LL G Pl0 T2 D.R.m}
    {R1 : RealDat D A1 T.Q.c.F} {R2 : RealDat D A2 T.Q.c.F} {v1 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R1.MW i σ).Vec}
    {v2 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R2.MW i σ).Vec} {O1 : ∀ i, OMDat T.toCore R1 i Unit (fun _ => A1.μ0)}
    {O2 : ∀ i, OMDat T.toCore R2 i Unit (fun _ => A2.μ0)} (h1 : Ext T R κ v₀ O j R1 v1 O1) (h2 : Ext T R1 κ v1 O1 j R2 v2 O2) :
    Ext T R κ v₀ O j R2 v2 O2 := by
  refine ⟨fun τ h => h2.1 τ (h1.1 τ h), fun τ ζ Φ Φ' h => h1.2.1 τ ζ Φ Φ' (h2.2.1 τ ζ Φ Φ' h), fun c u hc hu => ?_⟩
  obtain ⟨c1, u1, hc1, hu1, e1⟩ := h1.2.2 c u hc hu
  obtain ⟨c2, u2, hc2, hu2, e2⟩ := h2.2.2 c1 u1 hc1 hu1
  exact ⟨c2, u2, hc2, hu2, fun x => (e2 x).trans (e1 x)⟩

theorem hasTuples_of_laws {ph : Fin D.R.m → ℂ} {B : Base (Vc D j) (Wc D j)} {ψ ψ' : Twist D Circle} {T0' : Type}
    {A' : FamIn D.what₂.LL G Pl0 T0' D.R.m} {R' : RealDat D A' T.Q.c.F} {F' : Face D A'}
    {v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec} {O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)}
    (hL : Laws T R' F' κ v₀' O' ph j B) (hE : Ext T R κ v₀ O j R' v₀' O') {t t' : T0'} (ht : IsTupOf R' B ψ t)
    (ht' : IsTupOf R' B ψ' t') : HasTuples T R κ v₀ O ph j B ψ ψ' :=
  ⟨T0', A', R', F', v₀', O', hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1, hL.2.2.2.2.1, hL.2.2.2.2.2.1, hL.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2,
    hE.1, hE.2.1, hE.2.2, t, t', ht, ht'⟩

end Laws

section Point


end Point

end GlobalTheory.BigOn.Exp.TwConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneOfGapNonneg
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CompHS.WeightGapAntitone

theorem antitone_of_gap_nonneg {N : ℕ} (v : Fin N → ℤ) (h : ∀ k, k + 1 < N → 0 ≤ gap v k) : Antitone v := by
  cases N with
  | zero => exact fun a => a.elim0
  | succ n =>
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have := h i (by omega)
    rw [gap, dite_eq_left (by omega)] at this
    have e1 : (⟨(i : ℕ), by omega⟩ : Fin (n + 1)) = Fin.castSucc i := rfl
    have e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 1)) = i.succ := rfl
    rw [e1, e2] at this
    omega

end GlobalTheory.CompHS.WeightGapAntitone

theorem GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (P : WtPar Dw) (j : ℕ), (∀ τ, StrictAnti (P.u₁ τ)) →
    2 ≤ GlobalTheory.FlagTan.dimFlag Dw + j → 1 ≤ Dw.p → 1 ≤ Dw.q →
    ∀ τ, Antitone (P.wt j τ) ∧ 1 ≤ GlobalTheory.CompHS.gap (P.wt j τ) (Dw.p - 1) := by
  intro E _ _ _ H Dw P j hu hD hp hq τ
  have key : ∀ k (h : k + 1 < Dw.p + Dw.q), 1 ≤ gap (P.wt j τ) k := by
    intro k h
    have hr := (P.gap_rem τ k).1
    have hu1 : P.u₁ τ ⟨k + 1, h⟩ < P.u₁ τ ⟨k, by omega⟩ := hu τ (Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
    have hk : -2 ≤ FlagTan.kap Dw τ ⟨k, by omega⟩ - FlagTan.kap Dw τ ⟨k + 1, h⟩ := by
      simp only [FlagTan.kap, Fin.val_mk]
      split_ifs <;> push_cast <;> omega
    rw [gap, dite_eq_left h] at hr ⊢
    simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply] at hr ⊢
    simp only [nsmul_eq_mul] at hr ⊢
    have hD' : (2 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + (j : ℤ) := by exact_mod_cast hD
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + j - 2 by linarith)
      (show (0 : ℤ) ≤ P.u₁ τ ⟨k, by omega⟩ - P.u₁ τ ⟨k + 1, h⟩ - 1 by linarith)]
  exact ⟨WeightGapAntitone.antitone_of_gap_nonneg _ fun k h => by have := key k h; omega, key _ (by omega)⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def mvLev {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : FrPt Xo c S :=
  mvPt (K := c.F) (fun S _ _ => FrPt Xo c S)
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (y y' : FrPt Xo c S) =>
      levActR (Xo := Xo) (c := c) (levFull Dw l) g' y y') γ y

abbrev latQ (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (k : (uAt r v i).Comp) : Type :=
  lattice₂ D ((uAt r v i).X k).Λ ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k).Λ)))

def IsTransp (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k)
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) : Prop :=
  ∃ hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a,
    (∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom),
      ∃ (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _),
        FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩) (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩))) ∧
    ∀ w : lattice₂ D ((uAt r v i).X k).Λ,
      ∃ hw : Matrix.mulVec (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (w : Fin D.R.r → D.host.E) ∈
          lattice₂ D ((uAt r v i).X k').Λ,
        Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k').Λ))) ⟨_, hw⟩ =
          ψ k' (γ.symm ((ψ k).symm (Submodule.Quotient.mk w)))

theorem IsTransp.eq_of_eq {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
    {r : TwoRuns p.T p.P.Gp} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k}
    {γ γ' : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l}
    {k k' : (uAt r v i).Comp} {a : GL (Fin D.R.r) D.host.E}
    (h₁ : IsTransp p r i v ψ γ k k' a) (h₂ : IsTransp p r i v ψ γ' k k' a) : γ = γ' := by
  obtain ⟨-, -, m₁⟩ := h₁
  obtain ⟨-, -, m₂⟩ := h₂
  have hs : γ.symm = γ'.symm := by
    ext u
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (ψ k u)
    obtain ⟨hw₁, e₁⟩ := m₁ w
    obtain ⟨hw₂, e₂⟩ := m₂ w
    have := e₁.symm.trans e₂
    simp only [hw, LinearEquiv.symm_apply_apply] at this
    exact (ψ k').injective this
  have := congrArg LinearEquiv.symm hs
  simpa using this

end GlobalTheory.ShareOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpConjOfOne
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

theorem conj_sum_zero (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type)
    (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (j : Fin D.R.m)
    (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _))
    (hK : (S.A ((j : ℕ) + 1)).IsKsForm) (τ : ℂ ≃+* ℂ) (hτ : ∀ y, τ (Formalism.L2.Host.embLL0 D y) = Formalism.L2.Host.embLL0 D y)
    (n : ℕ) (c : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1))
    (h0 : ∑ k, c k • evW YS v₀ j (g k).val = 0) : ∑ k, τ (c k) • evW YS v₀ j (g k).val = 0 := by
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let σ : S.Ks → ℂ := fun r => D.what₂.embLL (algebraMap S.Ks D.what₂.LL r)
  have hσ : ∀ r, τ (σ r) = σ r := fun r => by
    have := hτ (S.kKs r)
    simp only [σ, ← S.kKs_spec]
    exact this
  have hg : ∀ k, evW YS v₀ j (g k).val = ∑ a, σ (bK.repr (g k) a) • φ a := fun k => by
    conv_lhs => rw [← bK.sum_repr (g k)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul D.what₂.LL, evW_smul, hbK]
  have hexp : ∀ d : Fin n → ℂ, ∑ k, d k • evW YS v₀ j (g k).val =
      ∑ a, (∑ k, d k * σ (bK.repr (g k) a)) • φ a := fun d => by
    simp only [hg, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hz : ∀ a, ∑ k, c k * σ (bK.repr (g k) a) = 0 := fun a =>
    Fintype.linearIndependent_iff.1 hφ _ ((hexp c).symm.trans h0) a
  rw [hexp]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : ∑ k, τ (c k) * σ (bK.repr (g k) a) = τ (∑ k, c k * σ (bK.repr (g k) a)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hσ]
  rw [this, hz a, map_zero, zero_smul]

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrBelow
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDown

section Integral

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem integral_below (T : CDVR) (io : c.F →+* T.Fr) (io₂ : d.c₂.F →+* T.Fr) (hio : ∀ a : c.F, io₂ (d.eF a) = io a)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (y₂ : letI := io₂.toAlgebra; FrPt d.Xo₂ d.c₂ T.Fr)
    (hy : letI := io.toAlgebra; letI := io₂.toAlgebra; FrOver d y₂ y) (h : Integral T io₂ y₂) : Integral T io y := by
  letI := io.toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, b1, b2, b3, b4⟩, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, p2, hg⟩ := h
  obtain ⟨e, hu, w, p, hw, p₁, p₂, R⟩ := (FrameLift.frOver_iff d y₂ y).1 hy
  obtain ⟨m', e₁⟩ := LiftBaseChange.exists_comp' d.m m1 y.x e.symm
  have eig : ∀ τ v, Formalism.L2.Pj.IsEigV d.c₂ io₂ G τ v ↔ Formalism.L2.Pj.IsEigV c io G τ v := fun τ v =>
    forall_congr' fun a => forall_congr' fun z => by rw [← FrameLift.embK_eF d τ a, hio]
  obtain ⟨w', r', tri⟩ := LiftBaseChange.rigIso_comp d.m m1 m' e.symm e₁ (w := w) hw r1
  obtain ⟨s', hs'⟩ := thf_secUp ((isGen_iff w').1 r'.1) Xo.univ.t.PP.isLB t'.PP.isLB σ
  refine ⟨G, t', m', m2, ⟨ub, b1, fun τ i => (eig τ _).1 (b2 τ i), fun τ v h1 h2 => b3 τ v h1 ((eig τ v).2 h2),
    fun τ i => ?_⟩, θ, hθ, w', w2, σ, s', θ2, r', r2,
    (ArcQ.FrUniq.isoMaps_iff w' σ s').2 fun Z r z j k hj hk => hs' Z r z (fun _ => j) k (mem_pull.2 hj) hk,
    i2, p2, ?_⟩
  · obtain ⟨q, h2, h3⟩ := b4 τ i
    exact ⟨q, by rw [e₁, ← Category.assoc, h2, hu], h3⟩
  · intro g g₁ g₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    obtain ⟨g', a₁, a₂⟩ := FrameLift.exists_pm (G := d.Xo₂.univ.t.G) (x := y₂.x) t'.G.hom m1.φ m1.cart.1.w.symm
    have eg : g' ≫ p = g := by
      refine FrameLift.pm_ext ?_ ?_
      · rw [Category.assoc, p₁, ← Category.assoc, a₁, g₁, e₁]
      · rw [Category.assoc, p₂, a₂, g₂]
    refine fn_ext fun z hz => ?_
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB z
    obtain ⟨i, hi⟩ := exists_chart d.Xo₂.univ.t.PP.isLB (m1.φ z)
    have hj : m'.φ z ∈ Xo.univ.t.PP.L.U (J PUnit.unit) := mem_pull.1 hz
    have hj' : d.m.φ (m1.φ z) ∈ Xo.univ.t.PP.L.U (J PUnit.unit) :=
      (congrArg (· ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) (FrameLift.pt_eq e₁ z)).mp hj
    have le : (d.Xo₂.univ.t.PP.L.pull m1.φ).U (fun _ => i) ≤ g' ⁻¹ᵁ (PPx y₂.x).U (fun _ => i) := fun q hq =>
      Set.mem_iInter.2 fun _ => (congrArg (· ∈ d.Xo₂.univ.t.PP.L.U i) (FrameLift.pt_eq a₁ q)).mpr (mem_pull.1 hq)
    have u₁ := (ArcQ.FrUniq.isoMaps_iff w1 σ s1).1 i1 _ (𝟙 _) z i k hi hk
    rw [hg g' a₁ a₂ (fun _ => i) le, gs_appLE g' _ _ le (𝟙 _) z (mem_pull.2 hi), Category.id_comp] at u₁
    have u₂ := R _ g' z (J PUnit.unit) i
      ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) (FrameLift.pt_eq a₁ z)).mpr hj')
      ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U i) (FrameLift.pt_eq a₁ z)).mpr hi)
    rw [a₁, eg] at u₂
    have u₃ := tri _ (𝟙 _) z (J PUnit.unit) i k hj' hi hk
    rw [Category.id_comp] at u₃
    rw [hs' _ (𝟙 _) z J k hz hk, gs_appLE _ _ _ hJ (𝟙 _) z hz, Category.id_comp]
    refine Eq.trans ?_ (u₂.trans (congrArg _ u₁)).symm
    rw [← _root_.mul_assoc, ← Units.val_mul, ← u₃]

theorem evR_eq_of_pull {d : DeltaDat Xo c 0} {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂}
    (hf : f ∈ sec Xo c a m) (hg : g ∈ sec d.Xo₂ d.c₂ a m) (h : GlobalTheory.LevPull.Pull d f g) {K : Type} [Field K]
    [Algebra c.F K] [Algebra d.c₂.F K] (hc : ∀ a : c.F, algebraMap d.c₂.F K (d.eF a) = algebraMap c.F K a)
    {y₂ : FrPt d.Xo₂ d.c₂ K} {y : FrPt Xo c K} (hy : FrOver d y₂ y) : evR d.Xo₂ d.c₂ g y₂ = evR Xo c f y := by
  let j : K →+* AlgebraicClosure K := algebraMap _ _
  letI : Algebra c.F (AlgebraicClosure K) := (j.comp (algebraMap c.F K)).toAlgebra
  letI : Algebra d.c₂.F (AlgebraicClosure K) := (j.comp (algebraMap d.c₂.F K)).toAlgebra
  let ψ : K →ₐ[c.F] AlgebraicClosure K := ⟨j, fun _ => rfl⟩
  let ψ₂ : K →ₐ[d.c₂.F] AlgebraicClosure K := ⟨j, fun _ => rfl⟩
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c K _ ψ y
  obtain ⟨z₂, hz₂⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ K _ ψ₂ y₂
  have e := h (AlgebraicClosure K) (fun a => congrArg j (hc a)) z₂ z
    (GlobalTheory.FrameLift.frOver_map d (ψ := ψ) (ψ₂ := ψ₂) rfl hy hz hz₂)
  rw [GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 ψ y
      (GlobalTheory.TransferCompare.allTest_framed Xo c K y) z hz,
    GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed d.Xo₂ d.c₂) g hg.1 ψ₂ y₂
      (GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂ K y₂) z₂ hz₂] at e
  exact j.injective e

end Integral

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem exists_intFr_below : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ((Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d) → ∀ (T : CDVR) (io₂ : d.c₂.F →+* T.Fr) (y₂ : IntFr d.Xo₂ d.c₂ T io₂), y₂.IsAlg → ∃ y : IntFr Xo c T (io₂.comp (d.eF : c.F →+* d.c₂.F)), y.IsAlg ∧ (∀ φ : ℝ, HasPhi y₂ φ → HasPhi y φ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, GlobalTheory.LevPull.Pull d f g → evI y₂ g = evI y f := by
  intro E _ _ _ H Dw l Xo c d _ hlev hO T io₂ y₂ halg
  have hO' : GlobalTheory.ClsVal.Cmp.OverBase d := hO.elim (fun h => GlobalTheory.ClsVal.Cmp.overBase_of_ne h.1 h.2 d) id
  letI := io₂.toAlgebra
  letI := (io₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  obtain ⟨y, hy⟩ := GlobalTheory.CovPull.below_exists d hO' (GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.KA_le hlev.1) (S := T.Fr) (fun _ => rfl) y₂.1
  refine ⟨⟨y, GlobalTheory.TransferCompare.allTest_framed Xo c T.Fr y,
    integral_below d T _ io₂ (fun _ => rfl) y y₂.1 hy y₂.2.2⟩, halg, ?_, fun a n f hf g hg h => ?_⟩
  · rintro φ ⟨G, t', m1, m2, h⟩
    obtain ⟨m', -⟩ := LiftBaseChange.exists_comp' d.m m1 y.x hy.1.symm
    exact ⟨G, t', m', m2, h⟩
  · exact evR_eq_of_pull hf hg h (fun _ => rfl) hy

end GlobalTheory.CoverDown
end
end
