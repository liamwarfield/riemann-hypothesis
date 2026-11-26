module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepRosatiOrderActionsSiegel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepresentingLinearLevelsAbelianSchem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearOfBasisProductsAdditivePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearOfBasisProductsAdditivePoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory

theorem basisLin_oLinear : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (H : Scheme.{0}) (Y AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → ∀ (ιO ιL : Type) (bO : Module.Basis ιO ℤ D.O) (bL : Module.Basis ιL ℤ D.La), (∀ j i, u (bO j • bL i) = u (bL i) ≫ actH.act (bO j)) → ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c := by
  intro p _ D H Y AH _ _ actH u hu ιO ιL bO bL hb

  have hcomp : ∀ (f : Y ⟶ AH) (b c : D.O), f ≫ actH.act (b + c) = (f ≫ actH.act b) * (f ≫ actH.act c) := by
    intro f b c
    rw [actH.add, MonObj.comp_mul]

  have u0 : u 0 = 1 := by
    have h := hu 0 0
    simp only [add_zero] at h
    have := congrArg (fun t => t * (u 0)⁻¹) h
    simpa using this.symm
  let U : D.La →+ Additive (Y ⟶ AH) :=
    { toFun := fun x => Additive.ofMul (u x)
      map_zero' := by simp [u0]
      map_add' := fun x y => by simp [hu] }

  have step1 : ∀ i (c : D.O), u (c • bL i) = u (bL i) ≫ actH.act c := by
    intro i
    let F : D.O →+ Additive (Y ⟶ AH) := U.comp ((LinearMap.toSpanSingleton D.O D.La (bL i)).toAddMonoidHom)
    let G : D.O →+ Additive (Y ⟶ AH) :=
      { toFun := fun c => Additive.ofMul (u (bL i) ≫ actH.act c)
        map_zero' := by
          have h := hcomp (u (bL i)) 0 0
          simp only [add_zero] at h
          have : u (bL i) ≫ actH.act 0 = 1 := by
            have := congrArg (fun t => t * (u (bL i) ≫ actH.act 0)⁻¹) h
            simpa using this.symm
          simp [this]
        map_add' := fun b c => by simp [hcomp] }
    have hFG : F.toIntLinearMap = G.toIntLinearMap := bO.ext fun j => by
      simp [F, G, U, hb]
    intro c
    have := congrArg (fun L => L c) hFG
    simpa [F, G, U] using this
  intro c
  let F : D.La →+ Additive (Y ⟶ AH) := U.comp (DistribSMul.toAddMonoidHom D.La c)
  let G : D.La →+ Additive (Y ⟶ AH) :=
    { toFun := fun x => Additive.ofMul (u x ≫ actH.act c)
      map_zero' := by
        haveI := actH.hom c
        simp [u0, MonObj.one_comp]
      map_add' := fun x y => by
        haveI := actH.hom c
        simp [hu, MonObj.mul_comp] }
  have hFG : F.toIntLinearMap = G.toIntLinearMap := bL.ext fun i => by
    simp [F, G, U, step1]
  intro x
  have := congrArg (fun L => L x) hFG
  simpa [F, G, U] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearOfBasisProductsAdditivePointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oLinear_of_basis_products_additive_points : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (H : Scheme.{0}) (Y AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → ∀ (ιO ιL : Type) (bO : Module.Basis ιO ℤ D.O) (bL : Module.Basis ιL ℤ D.La), (∀ j i, u (bO j • bL i) = u (bL i) ≫ actH.act (bO j)) → ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c := by
  first | (exact @GlobalTheory.basisLin_oLinear) | (exact GlobalTheory.basisLin_oLinear) | (intros; apply GlobalTheory.basisLin_oLinear  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAgreementLocusSeparated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAgreementLocusSeparated
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.EqLocus

theorem exists_fin (H : Scheme.{0}) (G : Over H) [IsSeparated G.hom] :
    ∀ (n : ℕ) (Z : Over H), IsFinite Z.hom → ∀ (a b : Fin n → (Z ⟶ G)),
      ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧ (∀ k, i ≫ a k = i ≫ b k) ∧
        ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) → ∃! h' : T ⟶ Y, h' ≫ i = h := by
  intro n
  induction n with
  | zero =>
    intro Z hZ a b
    refine ⟨Z, 𝟙 Z, hZ, fun k => k.elim0, fun T h _ => ⟨h, by simp, fun g hg => by simpa using hg⟩⟩
  | succ n ih =>
    intro Z hZ a b
    let e := equalizer.ι (a 0) (b 0)
    have hE : IsFinite (equalizer (a 0) (b 0)).hom := by
      rw [← Over.w e]
      infer_instance
    obtain ⟨Y, i', hY, hi', hu⟩ := ih _ hE (fun k => e ≫ a k.succ) (fun k => e ≫ b k.succ)
    refine ⟨Y, i' ≫ e, hY, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp only [Category.assoc]
        rw [equalizer.condition]
      · simpa only [Category.assoc] using hi' k
    · intro T h hh
      let l : T ⟶ equalizer (a 0) (b 0) := equalizer.lift h (hh 0)
      have hl : l ≫ e = h := equalizer.lift_ι _ _
      obtain ⟨h'', hh'', hu''⟩ := hu T l (fun k => by
        simp only [← Category.assoc, hl]
        exact hh k.succ)
      refine ⟨h'', show h'' ≫ i' ≫ e = h by rw [← Category.assoc, hh'', hl], fun g hg => hu'' g ?_⟩
      change g ≫ i' ≫ e = h at hg
      change g ≫ i' = l
      apply (cancel_mono e).1
      rw [Category.assoc, hg, hl]

theorem exists_finite_eqLocus : ∀ (H : Scheme.{0}) (Z G : Over H), IsFinite Z.hom → IsSeparated G.hom →
    ∀ (Ix : Type) [Finite Ix] (a b : Ix → (Z ⟶ G)), ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧
      (∀ k, i ≫ a k = i ≫ b k) ∧ ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) →
        ∃! h' : T ⟶ Y, h' ≫ i = h := by
  intro H Z G hZ hG Ix _ a b
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin Ix
  obtain ⟨Y, i, hY, hi, hu⟩ := exists_fin H G n Z hZ (fun k => a (σ.symm k)) (fun k => b (σ.symm k))
  refine ⟨Y, i, hY, fun k => by simpa using hi (σ k), fun T h hh => hu T h (fun k => hh _)⟩

end GlobalTheory.EqLocus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAgreementLocusSeparatedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_agreementLocus_separated : ∀ (H : Scheme.{0}) (Z G : Over H), IsFinite Z.hom → IsSeparated G.hom → ∀ (Ix : Type) [Finite Ix] (a b : Ix → (Z ⟶ G)), ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧ (∀ k, i ≫ a k = i ≫ b k) ∧ ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) → ∃! h' : T ⟶ Y, h' ≫ i = h := by
  first | (exact @GlobalTheory.EqLocus.exists_finite_eqLocus) | (exact GlobalTheory.EqLocus.exists_finite_eqLocus) | (intros; apply GlobalTheory.EqLocus.exists_finite_eqLocus  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearLevelPullbackUniversalFactorisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearLevelPullbackUniversalFactorisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem comp_one₂ {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

theorem pullUnivP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)) (AE : Over Y.left) [GrpObj AE] (φE : AE.left ⟶ AH.left) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE → (∀ y, (ηE y).left ≫ φE = (u y).left) → (∀ (T : Over H) (u' : D.La → (T ⟶ AH)), (∀ x y, u' (x + y) = u' x * u' y) → (∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c) → (∀ x, u' (N • x) = 1) → ∃! h : T ⟶ Y, ∀ x, h ≫ u x = u' x) → ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ Y.left, z ≫ Y.hom = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  intro p _ D N H AH _ actH Y u AE _ φE ηE hE hηu huniv T g AT _ φ act eta hT hact heta
  let Tg : Over H := Over.mk g
  let e : Tg ⟶ Over.mk ((𝟙_ (Over T)).hom ≫ g) := Over.homMk (𝟙 T) (by simp [Tg])
  let u' : D.La → (Tg ⟶ AH) := fun x => e ≫ pushHom hT (𝟙_ (Over T)) (eta x)
  have hu'l : ∀ x, (u' x).left = (eta x).left ≫ φ := fun x => by
    show 𝟙 T ≫ (eta x).left ≫ φ = _
    rw [Category.id_comp]
  have hadd : ∀ x y, u' (x + y) = u' x * u' y := fun x y => by
    show e ≫ pushHom hT _ (eta (x + y)) = (e ≫ pushHom hT _ (eta x)) * (e ≫ pushHom hT _ (eta y))
    rw [heta.1, map_mul, MonObj.comp_mul]
  have hlin : ∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c := fun c x => by
    apply Over.OverMorphism.ext
    show (u' (c • x)).left = (u' x ≫ actH.act c).left
    rw [hu'l, Over.comp_left, hu'l, heta.2.1, Over.comp_left, Category.assoc, hact, Category.assoc]
  have hker : ∀ x, u' (N • x) = 1 := fun x => by
    show e ≫ pushHom hT _ (eta (N • x)) = 1
    rw [heta.2.2, map_one, comp_one₂]
  obtain ⟨h, hh, hun⟩ := huniv Tg u' hadd hlin hker
  have hz : h.left ≫ Y.hom = g := Over.w h
  have hw : φ ≫ AH.hom = (AT.hom ≫ h.left) ≫ Y.hom := by rw [hT.1.w, Category.assoc, hz]
  let ψ : AT.left ⟶ AE.left := hE.1.lift φ (AT.hom ≫ h.left) hw
  have hψ₁ : ψ ≫ φE = φ := hE.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ AE.hom = AT.hom ≫ h.left := hE.1.lift_snd _ _ _
  have hhl : ∀ y, h.left ≫ (u y).left = (eta y).left ≫ φ := fun y => by
    rw [← Over.comp_left, hh y, hu'l]
  refine ⟨h.left, ⟨hz, ψ, ?_, hψ₁, fun y => ?_⟩, ?_⟩
  · exact IsGrpPullback.cancel hE (hT.congr hz.symm hψ₁.symm) hψ₂
  · apply hE.1.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, hηu, hhl]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (eta y), Category.assoc, Over.w (ηE y)]
      rfl
  · rintro z₂ ⟨hz₂, ψ₂, -, hψ₂₁, he₂⟩
    let h₂ : Tg ⟶ Y := Over.homMk z₂ hz₂
    have : h₂ = h := hun h₂ fun x => by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hu'l]
      show z₂ ≫ (u x).left = _
      rw [← hηu, ← Category.assoc, ← he₂, Category.assoc, hψ₂₁]
    exact congrArg (fun k => k.left) this

end GlobalTheory.UPel.HT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearLevelPullbackUniversalFactorisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oLinearLevel_pullback_universal_factorisation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)) (AE : Over Y.left) [GrpObj AE] (φE : AE.left ⟶ AH.left) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE → (∀ y, (ηE y).left ≫ φE = (u y).left) → (∀ (T : Over H) (u' : D.La → (T ⟶ AH)), (∀ x y, u' (x + y) = u' x * u' y) → (∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c) → (∀ x, u' (N • x) = 1) → ∃! h : T ⟶ Y, ∀ x, h ≫ u x = u' x) → ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ Y.left, z ≫ Y.hom = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.pullUnivP) | (exact GlobalTheory.UPel.HT.pullUnivP) | (intros; apply GlobalTheory.UPel.HT.pullUnivP  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGroupOLinearTorsionLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGroupOLinearTorsionLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.UPel.HT.LevPull

theorem exists_pull_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → (∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c) → (∀ x, u (N • x) = 1) → ∃ (AE : Over Y.left) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ y, (ηE y).left ≫ φE = (u y).left := by
  intro p _ D N H AH _ _ actH Y u hadd hlin htor
  let AE : Over Y.left := (Over.pullback Y.hom).obj AH
  letI iG : GrpObj AE := Functor.grpObjObj
  letI iC : IsCommMonObj AE := Functor.isCommMonObj_obj
  let φE : AE.left ⟶ AH.left := pullback.fst AH.hom Y.hom
  have hg : IsGrpPullback AE AH Y.hom φE := isGrpPullback_pullback AH Y.hom
  have inj : ∀ {T : Over Y.left} {x y : T ⟶ AE}, x.left ≫ φE = y.left ≫ φE → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext h (by rw [Over.w, Over.w]))
  have pm : ∀ {T : Over Y.left} (x y : T ⟶ AE), (x * y).left ≫ φE = (pushPt hg.1.w x * pushPt hg.1.w y).left :=
    fun x y => (hg.2 _ x y _ _ rfl rfl).symm

  let act' : D.O → (AE ⟶ AE) := fun a => Over.homMk (hg.1.lift (φE ≫ (actH.act a).left) AE.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φE = φE ≫ (actH.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over Y.left} (x : T ⟶ AE) a, pushPt hg.1.w (x ≫ act' a) = pushPt hg.1.w x ≫ actH.act a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have injP : ∀ {T : Over Y.left} {x y : T ⟶ AE}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun h =>
    inj (congrArg (fun q => q.left) h)
  have pm' : ∀ {T : Over Y.left} (x y : T ⟶ AE), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y :=
    fun x y => map_mul (pushHom hg _) x y
  let actE : OActN D.O AE :=
    { act := act'
      hom := fun a => isMonHom_of_mul _ fun T x y => injP (by
        have := actH.hom a
        rw [pa, pm', pm', pa, pa, MonObj.mul_comp])
      one := injP (by rw [← Category.id_comp (act' 1), pa, actH.one, Category.comp_id])
      mul := fun a b => injP (by
        rw [← Category.id_comp (act' (a * b)), pa, pa, actH.mul, ← Category.id_comp (act' b), pa, Category.assoc])
      add := fun a b => injP (by
        refine Eq.trans ?_ (pm' (act' a) (act' b)).symm
        rw [← Category.id_comp (act' (a + b)), ← Category.id_comp (act' a), ← Category.id_comp (act' b), pa, pa, pa,
          actH.add]
        exact MonObj.comp_mul _ _ _) }

  let ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE) := fun y =>
    Over.homMk (hg.1.lift (u y).left (𝟙_ (Over Y.left)).hom (by rw [Over.w (u y)]; simp)) (hg.1.lift_snd _ _ _)
  have hη : ∀ y, (ηE y).left ≫ φE = (u y).left := fun y => hg.1.lift_fst _ _ _
  have hT : (𝟙_ (Over Y.left)).hom ≫ Y.hom = Y.hom := by simp
  have one_congr : ∀ {a b : Y.left ⟶ H}, a = b → (1 : Over.mk a ⟶ AH).left = (1 : Over.mk b ⟶ AH).left := by
    intro a b h; subst h; rfl
  refine ⟨AE, inferInstance, inferInstance, φE, actE, ηE, hg, ha, ⟨fun x y => inj ?_, fun c x => inj ?_,
    fun x => inj ?_⟩, hη⟩
  · rw [hη, pm, hadd]
    exact (mul_left_congr hT (pushPt hg.1.w (ηE x)) (pushPt hg.1.w (ηE y)) (u x : Over.mk Y.hom ⟶ AH) (u y) (hη x) (hη y)).symm
  · show (ηE (c • x)).left ≫ φE = ((ηE x).left ≫ (act' c).left) ≫ φE
    rw [hη, hlin, Category.assoc, ha, ← Category.assoc, hη]; rfl
  · rw [hη, htor]
    have e := congrArg (fun q => q.left) (map_one (pushHom hg (𝟙_ (Over Y.left))))
    refine Eq.trans ?_ e.symm
    exact (one_congr hT).symm

end GlobalTheory.UPel.HT.LevPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGroupOLinearTorsionLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_group_oLinear_torsion_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → (∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c) → (∀ x, u (N • x) = 1) → ∃ (AE : Over Y.left) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ y, (ηE y).left ≫ φE = (u y).left := by
  first | (exact @GlobalTheory.UPel.HT.LevPull.exists_pull_level) | (exact GlobalTheory.UPel.HT.LevPull.exists_pull_level) | (intros; apply GlobalTheory.UPel.HT.LevPull.exists_pull_level  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepresentingLinearLevelsAbelianSchem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

theorem exists_finite_rep_linLevel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH], IsAbelianScheme AH → IsUnit ((N : ℕ) : Γ(H, ⊤)) → ∀ (actH : OActN D.O AH), ∃ (E : Scheme.{0}) (πE : E ⟶ H) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsFinite πE ∧ IsGrpPullback AE AH πE φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  intro p _ D N H AH _ _ hab hN actH
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  haveI : IsSeparated AH.hom := by haveI := hab.proper; infer_instance
  obtain ⟨Z, et, hZf, -, eadd, epow, huniv⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom H AH N D.La hab hN
  let bO := Module.Free.chooseBasis ℤ D.O
  let bL := Module.Free.chooseBasis ℤ D.La
  obtain ⟨Y, i, hYf, hieq, hiu⟩ := GlobalTheory.T.exists_finite_agreementLocus_separated H Z AH hZf inferInstance
    (Module.Free.ChooseBasisIndex ℤ D.O × Module.Free.ChooseBasisIndex ℤ D.La)
    (fun k => et (bO k.1 • bL k.2)) (fun k => et (bL k.2) ≫ actH.act (bO k.1))
  let u : D.La → (Y ⟶ AH) := fun x => i ≫ et x
  have uadd : ∀ x y, u (x + y) = u x * u y := fun x y => by
    simp only [u, eadd, MonObj.comp_mul]
  have ulin : ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c :=
    GlobalTheory.T.oLinear_of_basis_products_additive_points p D H Y AH actH u uadd _ _ bO bL fun j k => by
      have := hieq (j, k)
      simp only [u]
      rw [this, Category.assoc]
  have ukill : ∀ x, u (N • x) = 1 := fun x => by
    simp only [u]
    rw [GlobalTheory.LevCover.add_map_nsmul eadd, epow, MonObj.comp_one]
  have uuniv : ∀ (T : Over H) (u' : D.La → (T ⟶ AH)), (∀ x y, u' (x + y) = u' x * u' y) →
      (∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c) → (∀ x, u' (N • x) = 1) →
      ∃! h : T ⟶ Y, ∀ x, h ≫ u x = u' x := by
    intro T u' hadd hlin hkill
    have hpow : ∀ x, u' x ^ N = 1 := fun x => by rw [← GlobalTheory.LevCover.add_map_nsmul hadd, hkill]
    obtain ⟨h₀, hh₀, hu₀⟩ := huniv T u' hadd hpow
    have heq : ∀ k, h₀ ≫ (fun k : _ × _ => et (bO k.1 • bL k.2)) k =
        h₀ ≫ (fun k : _ × _ => et (bL k.2) ≫ actH.act (bO k.1)) k := by
      rintro ⟨j, k⟩
      simp only
      rw [hh₀, hlin, ← Category.assoc, hh₀]
    obtain ⟨h, hh, hu⟩ := hiu T h₀ heq
    refine ⟨h, fun x => by simp only [u]; rw [← Category.assoc, hh, hh₀], fun h' hh' => hu h' ?_⟩
    exact hu₀ _ fun x => by rw [Category.assoc]; exact hh' x
  obtain ⟨AE, _, _, φE, actE, ηE, hE, hact, heta, hηu⟩ := GlobalTheory.T.exists_pullback_group_oLinear_torsion_level p D N H AH actH Y u uadd ulin ukill
  exact ⟨Y.left, Y.hom, AE, inferInstance, inferInstance, φE, actE, ηE, hYf, hE, hact, heta,
    fun T g AT _ φ act eta hT hTact hTeta =>
      GlobalTheory.T.oLinearLevel_pullback_universal_factorisation p D N H AH actH Y u AE φE ηE hE hηu uuniv T g AT φ act eta hT hTact hTeta⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepresentingLinearLevelsAbelianSchemStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_representing_linearLevels_abelianScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH], IsAbelianScheme AH → IsUnit ((N : ℕ) : Γ(H, ⊤)) → ∀ (actH : OActN D.O AH), ∃ (E : Scheme.{0}) (πE : E ⟶ H) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsFinite πE ∧ IsGrpPullback AE AH πE φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_linLevel) | (exact GlobalTheory.UPel.HT.exists_finite_rep_linLevel) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_linLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionOfGrpPullbackSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionOfGrpPullbackSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.RosatiPull

theorem sq_left_ext {H : Scheme.{0}} {G : Over H} {Z : Scheme.{0}} {a b : Z ⟶ (G ⊗ G).left}
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h1 h2

theorem rosatiFor_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (S H E : Scheme.{0}) (A₀ : Over S) [GrpObj A₀] (P : LB (G2 A₀).left), P.IsLB → ∀ (AH : Over H) [GrpObj AH] (AE : Over E) [GrpObj AE] (f : E ⟶ H) (φ : AE.left ⟶ AH.left) (φ₂ : (G2 AE).left ⟶ (G2 AH).left) (φ₂H : (G2 AH).left ⟶ (G2 A₀).left) (actH : OActN D.O AH) (actE : OActN D.O AE), IsGrpPullback AE AH f φ → IsSquare φ φ₂ → (∀ a : D.O, (actE.act a).left ≫ φ = φ ≫ (actH.act a).left) → RosatiFor D actH (P.pull φ₂H) → RosatiFor D actE (P.pull (φ₂ ≫ φ₂H)) := by
  intro p _ D S H E A₀ _ P hP AH _ AE _ f φ φ₂ φ₂H actH actE _ hsq hact hR c
  have hu : (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH ≫ actH.act c) (snd AH AH)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.1, Category.assoc]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
  have hv : (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH) (snd AH AH ≫ actH.act (D.star c).unop)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.2, Category.assoc]
  have hQ : (P.pull φ₂H).IsLB := pull_isLB hP _
  have hR' : (P.pull (φ₂ ≫ φ₂H)).IsLB := pull_isLB hP _
  have e3 := GlobalTheory.GenSpread.lbIso_pull_comp (L := P.pull φ₂H) (M := P.pull φ₂H) φ₂ hu hv (hR c)
  have e1u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left (a := φ₂ ≫ φ₂H) rfl
  have e2u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  have e1v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left (a := φ₂ ≫ φ₂H) rfl
  have e2v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  exact LBIso.trans (pull_isLB hR' _) (pull_isLB hP _) (pull_isLB hR' _) e1u.symm
    (LBIso.trans (pull_isLB hP _) (pull_isLB hQ _) (pull_isLB hR' _) e2u
      (LBIso.trans (pull_isLB hQ _) (pull_isLB hQ _) (pull_isLB hR' _) e3
        (LBIso.trans (pull_isLB hQ _) (pull_isLB hP _) (pull_isLB hR' _) e2v.symm e1v)))

end GlobalTheory.RosatiPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionOfGrpPullbackSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiCondition_of_grpPullback_square : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (S H E : Scheme.{0}) (A₀ : Over S) [GrpObj A₀] (P : LB (G2 A₀).left), P.IsLB → ∀ (AH : Over H) [GrpObj AH] (AE : Over E) [GrpObj AE] (f : E ⟶ H) (φ : AE.left ⟶ AH.left) (φ₂ : (G2 AE).left ⟶ (G2 AH).left) (φ₂H : (G2 AH).left ⟶ (G2 A₀).left) (actH : OActN D.O AH) (actE : OActN D.O AE), IsGrpPullback AE AH f φ → IsSquare φ φ₂ → (∀ a : D.O, (actE.act a).left ≫ φ = φ ≫ (actH.act a).left) → RosatiFor D actH (P.pull φ₂H) → RosatiFor D actE (P.pull (φ₂ ≫ φ₂H)) := by
  first | (exact @GlobalTheory.RosatiPull.rosatiFor_pull) | (exact GlobalTheory.RosatiPull.rosatiFor_pull) | (intros; apply GlobalTheory.RosatiPull.rosatiFor_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepAdjointActionLevelSiegelPullback
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem exists_finite_rep_rosati_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (E : Scheme.{0}) (πE : E ⟶ S) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ c.A.left) (φ₂E : (G2 AE).left ⟶ (G2 c.A).left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsLocallyNoetherian E ∧ IsFinite πE ∧ IsGrpPullback AE c.A πE φE ∧ IsSquare φE φ₂E ∧ RosatiFor D actE (c.P.pull φ₂E) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ (∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actE.act a).left) ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  intro p _ D R _ b N hNp h M B _ ζ S _ s₁ t c e he hc
  obtain ⟨H, πH, AH, _, _, φH, φ₂H, actH, hHf, hHab, pbH, sqH, rosH, univH⟩ := GlobalTheory.T.exists_finite_rep_rosati_orderActions_siegel p D h M B ζ S s₁ c hc.1
  have hNH : IsUnit ((N : ℕ) : Γ(H, ⊤)) := by
    have h0 : IsUnit ((N : ℕ) : Γ(Sp R, ⊤)) := by
      have := (b.unit N hNp).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this
    have := h0.map (πH ≫ t).appTop.hom
    simpa using this
  obtain ⟨E, πE, AE, _, _, φE, actE, ηE, hEf, pbE, actEc, etaE, univE⟩ := GlobalTheory.T.exists_finite_representing_linearLevels_abelianScheme p D N H AH hHab hNH actH
  let x₁ : Over.mk ((G2 AE).hom ≫ πE) ⟶ AH :=
    Over.homMk ((fst AE AE).left ≫ φE) (by rw [Category.assoc, pbE.1.w, ← Category.assoc, Over.w]; rfl)
  let x₂ : Over.mk ((G2 AE).hom ≫ πE) ⟶ AH :=
    Over.homMk ((snd AE AE).left ≫ φE) (by rw [Category.assoc, pbE.1.w, ← Category.assoc, Over.w]; rfl)
  let φ₂ : (G2 AE).left ⟶ (G2 AH).left := (lift x₁ x₂).left
  have sq : IsSquare φE φ₂ := by
    constructor
    · show (lift x₁ x₂).left ≫ (fst AH AH).left = _
      rw [← Over.comp_left, lift_fst]; rfl
    · show (lift x₁ x₂).left ≫ (snd AH AH).left = _
      rw [← Over.comp_left, lift_snd]; rfl
  haveI : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian πH
  haveI : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian πE
  refine ⟨E, πE ≫ πH, AE, inferInstance, inferInstance, φE ≫ φH, φ₂ ≫ φ₂H, actE, ηE, inferInstance,
    inferInstance, pbE.comp pbH, ?_, GlobalTheory.T.rosatiCondition_of_grpPullback_square p D S H E c.A c.P c.isLB AH AE πE φE φ₂ φ₂H actH actE pbE sq actEc rosH,
    etaE, ?_⟩
  · constructor
    · rw [Category.assoc, sqH.1, ← Category.assoc, sq.1, Category.assoc]
    · rw [Category.assoc, sqH.2, ← Category.assoc, sq.2, Category.assoc]
  intro T g AT _ φ φ₂' act eta pbT sqT rosT etaT
  obtain ⟨z₁, ⟨hz₁, ψ₁, pb₁, hψ₁, act₁⟩, uniq₁⟩ := univH T g AT φ φ₂' act pbT sqT rosT
  obtain ⟨z, ⟨hz, ψ, pb, hψ, heta⟩, uniq⟩ := univE T z₁ AT ψ₁ act eta pb₁ act₁ etaT
  refine ⟨z, ⟨by rw [← Category.assoc, hz, hz₁], ψ, pb, by rw [← Category.assoc, hψ, hψ₁], fun a => ?_, heta⟩, ?_⟩
  · apply pbE.1.hom_ext
    · rw [Category.assoc, hψ, act₁, Category.assoc, actEc, ← Category.assoc, hψ]
    · rw [Category.assoc, pb.1.w, Category.assoc, Over.w (actE.act a), pb.1.w, ← Category.assoc, Over.w (act.act a)]
  · rintro z' ⟨hz', ψ', pb', hψ', act', eta'⟩
    have e₁ : z' ≫ πE = z₁ := uniq₁ (z' ≫ πE) ⟨by rw [Category.assoc]; exact hz', ψ' ≫ φE, pb'.comp pbE,
      by rw [Category.assoc]; exact hψ', fun a => by
        rw [← Category.assoc, act' a, Category.assoc, actEc, Category.assoc]⟩
    have e₂ : ψ' ≫ φE = ψ₁ := by
      apply pbH.1.hom_ext
      · rw [Category.assoc, hψ', hψ₁]
      · rw [Category.assoc, pbE.1.w, ← Category.assoc, pb'.1.w, Category.assoc, e₁, pb₁.1.w]
    exact uniq z' ⟨e₁, ψ', pb', e₂, eta'⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepAdjointActionLevelSiegelPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_adjointAction_level_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (E : Scheme.{0}) (πE : E ⟶ S) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ c.A.left) (φ₂E : (G2 AE).left ⟶ (G2 c.A).left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsLocallyNoetherian E ∧ IsFinite πE ∧ IsGrpPullback AE c.A πE φE ∧ IsSquare φE φ₂E ∧ RosatiFor D actE (c.P.pull φ₂E) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ (∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actE.act a).left) ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_rosati_level) | (exact GlobalTheory.UPel.HT.exists_finite_rep_rosati_level) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_rosati_level  <;> assumption)
end
