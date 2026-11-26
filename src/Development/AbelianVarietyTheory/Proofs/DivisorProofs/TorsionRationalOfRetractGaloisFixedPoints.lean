module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacks
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorsDescent

theorem descend_point {K : Type} [Field K] [CharZero K] (X : Scheme.{0}) [IsAffine X]
    (f : Sp (AlgebraicClosure K) ⟶ X)
    (hf : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, spMap σ.toAlgHom.toRingHom ≫ f = f) :
    ∃ g : Sp K ⟶ X, spMap (algebraMap K (AlgebraicClosure K)) ≫ g = f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (f ≫ X.isoSpec.hom)
  have hfix : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) a, σ (φ a) = φ a := by
    intro σ a
    have h1 : Spec.map (φ ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom) = Spec.map φ := by
      rw [Spec.map_comp, hφ, ← Category.assoc]
      exact congrArg (· ≫ X.isoSpec.hom) (hf σ)
    exact congrArg (fun g => g.hom a) (Spec.map_injective h1)
  have hmem : ∀ a, φ a ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    intro a
    have hb := InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))
    have h2 : φ a ∈ IntermediateField.fixedField (⊥ : IntermediateField K (AlgebraicClosure K)).fixingSubgroup :=
      (IntermediateField.mem_fixedField_iff _ _).2 fun σ _ => hfix σ a
    rw [hb] at h2
    exact IntermediateField.mem_bot.1 h2
  let jb := algebraMap K (AlgebraicClosure K)
  let e := RingEquiv.ofBijective jb.rangeRestrict
    ⟨fun a b h => jb.injective (congrArg Subtype.val h), jb.rangeRestrict_surjective⟩
  let ψ : Γ(X, ⊤) →+* K := e.symm.toRingHom.comp (φ.hom.codRestrict jb.range hmem)
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom jb = φ := by
    ext r
    exact congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict jb.range hmem r))
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_⟩
  rw [← Category.assoc, spMap, ← Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem torsRat_of_retract_galoisFixed : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G' ≅ A.A) (inc : G ⟶ G') (pr : G' ⟶ G) (n : ℕ), IsMonHom gen.hom → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → 1 ≤ n → (∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left) → TorsRat G n := by
  have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
      {X : Scheme} (y y' : Sp K ⟶ X)
      (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
    obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
    obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
    simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
    have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
        spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
          (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
      intro q ψ
      simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
    rw [e, e] at h
    have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
    simp only [Sigma.mk.inj_iff] at h2
    obtain ⟨rfl, h3⟩ := h2
    have h4 : φ = φ' := by
      have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
      ext x
      apply gam.injective
      have := congrArg (fun f => f.hom x) h5
      simpa using this
    rw [h4]
  intro R _ _ _ G _ _ G' _ _ A gen inc pr n hgen hinc hpr hret hn hfix
  haveI := hgen
  haveI := hinc
  haveI := hpr
  intro Ω _ _ κ x hx
  letI : Algebra (FractionRing R) Ω := κ.toAlgebra
  let jb := algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))
  let i₁ : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hκ : κ = i₁.toRingHom.comp jb := by
    ext a
    exact (i₁.commutes a).symm
  have hκs : spMap κ = spMap i₁.toRingHom ≫ spMap jb := by
    rw [hκ, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hip : inc.left ≫ pr.left = 𝟙 _ := by rw [← Over.comp_left, hret, Over.id_left]

  have hpb := isGrpPullback_pullback G' (jK R)
  let T : Over (Sp (FractionRing R)) := Over.mk (spMap κ)
  let x1 : Over.mk (T.hom ≫ jK R) ⟶ G' := x ≫ inc
  have hx1 : x1 ^ n = 1 := by
    show (x ≫ inc) ^ n = 1
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  let x2 := (ObjPull.pushEquiv hpb T).symm x1
  have hx2 : x2 ^ n = 1 := by simp only [x2, ← map_pow, hx1, map_one]
  have hx2l : x2.left ≫ pullback.fst G'.hom (jK R) = x.left ≫ inc.left := ObjPull.pushEquiv_symm_left hpb T x1
  let x3 := x2 ≫ gen.hom
  have hx3 : x3 ^ n = 1 := by rw [← MonObj.pow_comp, hx2, MonObj.one_comp]
  have hmul : x3 ≫ mulN A.A n = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx3, Hom.one_def]
  let t : T ⟶ torsion A.A n := pullback.lift x3 (toUnit _) hmul
  have ht : t ≫ torsion.ι A.A n = x3 := pullback.lift_fst _ _ _

  have hfin := (AbTorsionAnyBase.isFinite_and_flat_torsion _ A.A A.isAb n hn).1
  obtain ⟨K', _, _, _, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A n) hfin
  let i' : K' →ₐ[FractionRing R] AlgebraicClosure (FractionRing R) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra K' (AlgebraicClosure (FractionRing R)) := i'.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) K' (AlgebraicClosure (FractionRing R)) :=
    IsScalarTower.of_algebraMap_eq fun a => (i'.commutes a).symm
  obtain ⟨w, hw⟩ := H (AlgebraicClosure (FractionRing R)) Ω i₁.toRingHom t.left (by
    rw [Over.w t]
    show spMap κ = _
    rw [hκ])
  have hw2 : w ≫ (torsion A.A n).hom = spMap jb := by
    refine spec_map_field_cancel i₁.toRingHom _ _ ?_
    rw [← Category.assoc, hw, Over.w t]
    exact hκs
  let Tb : Over (Sp (FractionRing R)) := Over.mk (spMap jb)
  let t₀ : Tb ⟶ torsion A.A n := Over.homMk w hw2
  let g₀ : Tb ⟶ (Over.pullback (jK R)).obj G' := t₀ ≫ torsion.ι A.A n ≫ gen.inv
  let y₁ := ObjPull.pushEquiv hpb Tb g₀
  have hy₁l : y₁.left = w ≫ (torsion.ι A.A n).left ≫ gen.inv.left ≫ pullback.fst G'.hom (jK R) := by
    rw [ObjPull.pushEquiv_left]
    simp only [g₀, t₀, Over.comp_left, Over.homMk_left, Category.assoc]
  have hkey : spMap i₁.toRingHom ≫ y₁.left = x.left ≫ inc.left := by
    have hgh : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    rw [hy₁l, ← Category.assoc, hw, ← hx2l, ← Category.assoc, ← Over.comp_left, ht]
    show (x2.left ≫ gen.hom.left) ≫ gen.inv.left ≫ _ = _
    rw [Category.assoc, ← Category.assoc gen.hom.left, hgh, Category.id_comp]

  let y₀ : Over.mk (Tb.hom ≫ jK R) ⟶ G := y₁ ≫ pr
  have hy₀ : y₀ ^ n = 1 := by
    have h0 : (t₀ ≫ torsion.ι A.A n) ≫ mulN A.A n = toUnit _ ≫ η := by
      have hc : torsion.ι A.A n ≫ mulN A.A n = pullback.snd (mulN A.A n) η[A.A] ≫ η := pullback.condition
      rw [Category.assoc, hc]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ η) (toUnit_unique _ _))
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id] at h0
    have h1 : g₀ ^ n = 1 := by
      show (t₀ ≫ torsion.ι A.A n ≫ gen.inv) ^ n = 1
      rw [← Category.assoc, ← MonObj.pow_comp, h0, ← Hom.one_def, MonObj.one_comp]
    show (y₁ ≫ pr) ^ n = 1
    rw [← MonObj.pow_comp, ← map_pow, h1, map_one, MonObj.one_comp]
  have hy₁inc : y₁.left ≫ pr.left ≫ inc.left = y₁.left := by
    refine spec_map_field_cancel i₁.toRingHom _ _ ?_
    rw [← Category.assoc, hkey, Category.assoc, reassoc_of% hip]
  have hy₁fix : ∀ σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R),
      spMap σ.toAlgHom.toRingHom ≫ y₁.left = y₁.left := by
    intro σ
    calc spMap σ.toAlgHom.toRingHom ≫ y₁.left = spMap σ.toAlgHom.toRingHom ≫ (y₁.left ≫ pr.left) ≫ inc.left := by
          rw [Category.assoc, hy₁inc]
      _ = (y₁.left ≫ pr.left) ≫ inc.left := by
          rw [← Category.assoc]
          exact congrArg (· ≫ inc.left) (hfix σ y₀ hy₀)
      _ = y₁.left := by rw [Category.assoc, hy₁inc]
  haveI : Mono (torsion.ι A.A n) := inferInstanceAs (Mono (pullback.fst _ _))
  have hwfix : ∀ σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R),
      spMap σ.toAlgHom.toRingHom ≫ w = w := by
    intro σ
    have hσ : spMap σ.toAlgHom.toRingHom ≫ Tb.hom = Tb.hom := by
      show spMap _ ≫ spMap jb = spMap jb
      rw [spMap, spMap, ← Spec.map_comp]
      congr 2
      ext a
      exact σ.commutes a
    let eσ : Tb ⟶ Tb := Over.homMk (spMap σ.toAlgHom.toRingHom) hσ
    have h1 : eσ ≫ g₀ = g₀ := by
      apply (ObjPull.pushEquiv hpb Tb).injective
      apply Over.OverMorphism.ext
      rw [ObjPull.pushEquiv_left, ObjPull.pushEquiv_left, Over.comp_left, Category.assoc]
      exact hy₁fix σ
    have h2 : eσ ≫ t₀ = t₀ := by
      rw [← cancel_mono (torsion.ι A.A n ≫ gen.inv)]
      simpa only [Category.assoc] using h1
    exact congrArg (fun f => f.left) h2

  haveI := hfin
  haveI : IsAffine (torsion A.A n).left := isAffine_of_isAffineHom (torsion A.A n).hom
  obtain ⟨w₁, hw₁⟩ := descend_point (torsion A.A n).left w hwfix
  have hw₁s : w₁ ≫ (torsion A.A n).hom = 𝟙 _ := by
    refine spec_map_field_cancel jb _ _ ?_
    rw [← Category.assoc, hw₁, hw2, Category.comp_id]
  let z : Sp (FractionRing R) ⟶ G'.left :=
    w₁ ≫ (torsion.ι A.A n).left ≫ gen.inv.left ≫ pullback.fst G'.hom (jK R)
  have hz : z ≫ G'.hom = jK R := by
    simp only [z, Category.assoc]
    have hgi : gen.inv.left ≫ pullback.snd G'.hom (jK R) = A.A.hom := Over.w gen.inv
    rw [pullback.condition, ← Category.assoc gen.inv.left, hgi, ← Category.assoc (torsion.ι A.A n).left,
      Over.w (torsion.ι A.A n), ← Category.assoc w₁, hw₁s, Category.id_comp]
  refine ⟨Over.homMk z hz ≫ pr, ?_⟩
  have hz' : spMap κ ≫ z = x.left ≫ inc.left := by
    have e1 : spMap κ ≫ z = spMap i₁.toRingHom ≫ y₁.left := by
      show spMap κ ≫ (w₁ ≫ _ ≫ _ ≫ _) = _
      rw [hκs, Category.assoc, ← Category.assoc (spMap jb), hw₁, hy₁l]
    rw [e1, hkey]
  show x.left = spMap κ ≫ z ≫ pr.left
  rw [← Category.assoc, hz', Category.assoc, hip, Category.comp_id]

end GlobalTheory.TorsDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionRational_of_retract_galoisFixed_points : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G' ≅ A.A) (inc : G ⟶ G') (pr : G' ⟶ G) (n : ℕ), IsMonHom gen.hom → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → 1 ≤ n → (∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left) → TorsRat G n := by
  first | exact @GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed | exact GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed | (intros; apply GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListRealisedSystemUpToRootsOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantKthRootLabelledPointUpToRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantKthRootLabelledPointUpToRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaAtRoot

section
variable {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A)))

theorem val_powFrame' {T : Over S} (x : T ⟶ P.A) (e) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) :
    val (powFrame P.A P.L x e k) r z J = val e r z J ^ k :=
  map_zpow _ _ _

theorem isThetaConst_of_thG (hrig : rig.IsGen) {m : ℕ} {T : Over S} {th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)}
    {x : T ⟶ P.A} {c : Γ(T.left, ⊤)} (H : ThG P.A P.L rig m th x c) :
    ∃ (s₁ s₂ : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)) (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T),
      GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsMulPull P rig m ((m ^ 2 : ℕ) : ℤ) th s₁ ∧ SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U ∧
      IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s₁ s₂ ∧ GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsValueZero P rig ((m ^ 2 : ℕ) : ℤ) s₂ c := by
  obtain ⟨-, t, α, s₁, θ, hα, h₂, h₃, h₄, h₅, h₆⟩ := H
  refine ⟨s₁, t, θ, ⟨α, hα, corr_of_val P.isLB fun y J hJ => ?_, h₃⟩, h₄, h₅,
    ⟨rigT P.A P.L rig T ((m ^ 2 : ℕ) : ℤ), GlobalTheory.ThetaReal.NormMul.rigT_isGen hrig _, corr_of_val P.isLB fun _ _ _ => rfl,
      GlobalTheory.ThetaPtMove.isValueAt_of_sv P.isLB fun y J hJ => by rw [Category.id_comp]; exact h₆ y J hJ⟩⟩
  refine (val_corr hJ h₂ (𝟙 _)).trans ?_
  rw [val_mul hJ, val_inv, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ,
    GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, zpow_sub_one, zpow_one]

theorem frame_pull {n : ℕ} {T T₀ : Over S} (u : T ⟶ T₀) {x₀ : T₀ ⟶ P.A}
    {e₀ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => 1))}
    (H : IsTorsFrame P rig n x₀ e₀) :
    IsTorsFrame P rig n (u ≫ x₀) (LB.pullGen P.L (fun _ => x₀.left) (fun _ => 1) e₀ u.left) := by
  obtain ⟨h₁, h₂, α, hα, hN, hc⟩ := H
  refine ⟨by rw [← MonObj.comp_pow, h₁, MonObj.comp_one], LB.isGen_pullGen _ _ _ _ h₂ _, α, hα, hN,
    corr_of_val P.isLB fun y J hJ => ?_⟩
  have q := val_corr hJ hc u.left
  rw [val_powFrame', val_mul hJ, val_pull hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, Over.w u] at q
  rw [val_powFrame', val_pull hJ, val_mul hJ, val_pull hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, Category.id_comp,
    Category.id_comp, Category.id_comp, Over.comp_left]
  exact q

theorem value_pull {T T₀ : Over S} (u : T ⟶ T₀) {x₀ : T₀ ⟶ P.A}
    {e₀ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => 1))}
    {th : LB.Sec (LPow P.A P.L 1 T₀)} {c : Γ(T₀.left, ⊤)} (H : IsValueAt P.A P.L 1 th x₀ e₀ c) :
    IsValueAt P.A P.L 1 (VVRank.pullS P.A 1 u th) (u ≫ x₀)
      (LB.pullGen P.L (fun _ => x₀.left) (fun _ => 1) e₀ u.left) (u.left.appTop.hom c) := by
  refine GlobalTheory.ThetaPtMove.isValueAt_of_sv P.isLB fun y J hJ => ?_
  have e : (ptSecT P.A (u ≫ x₀)) ≫ (u ▷ P.A) = u ≫ ptSecT P.A x₀ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e' : (𝟙 _ ≫ (ptSecT P.A (u ≫ x₀)).left) ≫ (u ▷ P.A).left = u.left ≫ (ptSecT P.A x₀).left := by
    rw [Category.id_comp, ← Over.comp_left, e, Over.comp_left]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, e', GlobalTheory.ThetaPtMove.sv_of_isValueAt H u.left y hJ, val_pull hJ, Category.id_comp]
  exact congrArg (· * _) (gs_pull (𝟙 _) u.left y ⊤ trivial c).symm

end

end GlobalTheory.ThetaAtRoot

namespace GlobalTheory


open GlobalTheory.ThetaAtRoot in
theorem thetaConst_pow_eq_at_root : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (b : S.Gam) (y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A) (v : K), y ^ (S.r * S.N) = (Over.homMk (spMap i) (by simp) : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R)) ≫ ρ.pt b → ThG ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) y (GlobalTheory.ZH.fn v) → v ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ K _ i b y v hy H
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hk : Odd (S.r * S.N) := by
    obtain ⟨j, -, hj⟩ := ρ.r_eq
    rw [hj, ρ.N_eq]
    exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow
  let u : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk (spMap i) (by simp)
  have hfr := frame_pull ρ.P ρ.rig u (ρ.fr_tors b)
  have ht := value_pull ρ.P u (ρ.th_val b)
  obtain ⟨s₁, s₂, U, h₁, hU, hs, h₃⟩ := isThetaConst_of_thG ρ.P ρ.rig ρ.rig_gen H
  let z : Sp K := (⊥ : PrimeSpectrum K)
  obtain ⟨ξ, hξ, e⟩ := GlobalTheory.ThetaCompare.normalised_root_stalk hL.globalFns ρ.P hk hy hfr ht _
    (Nat.cast_pow (S.r * S.N) 2) h₁ hU hs h₃ z
  have ec : u.left.appTop.hom (GlobalTheory.ZH.fn (⟨S.th b, S.th_mem b⟩ : S.R)) = GlobalTheory.ZH.fn (i ⟨S.th b, S.th_mem b⟩) :=
    (congrArg (fun q => q.hom (⟨S.th b, S.th_mem b⟩ : S.R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
  rw [ec] at e
  let iso := Scheme.ΓSpecIso (CommRingCat.of K)
  let g : K →+* (Sp K).presheaf.stalk z := ((Sp K).presheaf.germ ⊤ z trivial).hom.comp iso.inv.hom
  have hg : Function.Injective g :=
    (germ_injective_of_isIntegral (Sp K) (U := ⊤) z trivial).comp (ConcreteCategory.bijective_of_isIso iso.inv).1
  have hgs : ∀ a : K, gs (𝟙 (Over.mk (spMap i ≫ 𝟙 (Sp S.R))).left) z ⊤ (GlobalTheory.ZH.fn a) = g a :=
    fun a => gs_eq _ z ⊤ trivial _
  apply hg
  rw [map_pow, map_pow, ← hgs, ← hgs, e, mul_pow, ← Units.val_pow_eq_pow_val, hξ, Units.val_one, _root_.one_mul]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantKthRootLabelledPointUpToRootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (b : S.Gam) (y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A) (v : K), y ^ (S.r * S.N) = (Over.homMk (spMap i) (by simp) : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R)) ≫ ρ.pt b → ThG ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) y (GlobalTheory.ZH.fn v) → v ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  first | exact @GlobalTheory.thetaConst_pow_eq_at_root | exact GlobalTheory.thetaConst_pow_eq_at_root | (intros; apply GlobalTheory.thetaConst_pow_eq_at_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListRealisedSystemUpToRootsOfUnity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.RealTh

theorem exists_pow_eq (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    {k : ℕ} (hk : (k : K) ≠ 0) (z : Over.mk x ⟶ P.A) (hz : z ^ k = 1) : ∃ y : Over.mk x ⟶ P.A, y ^ k = z := by
  have := P.isAb.comm
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have hk2 : ((k ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hk
  have c₁ := TorsionFieldExt.card_torsion hL P x hk
  have c₂ := TorsionFieldExt.card_torsion hL P x hk2
  let H₁ := (powMonoidHom k : (Over.mk x ⟶ P.A) →* (Over.mk x ⟶ P.A)).ker
  let H₂ := (powMonoidHom (k ^ 2) : (Over.mk x ⟶ P.A) →* (Over.mk x ⟶ P.A)).ker
  have e₁ : Nat.card H₁ = k ^ (2 * P.g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H₁, MonoidHom.mem_ker])).trans c₁
  have e₂ : Nat.card H₂ = (k ^ 2) ^ (2 * P.g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H₂, MonoidHom.mem_ker])).trans c₂
  have : Finite H₂ := Nat.finite_of_card_ne_zero (by rw [e₂]; positivity)
  have : Finite H₁ := Nat.finite_of_card_ne_zero (by rw [e₁]; positivity)
  let ψ : H₂ →* (Over.mk x ⟶ P.A) := (powMonoidHom k).comp H₂.subtype
  have hker : Nat.card ψ.ker = k ^ (2 * P.g) := by
    rw [← e₁]
    refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨y.1.1, ?_⟩) ⟨fun a b h => ?_, fun a => ?_⟩)
    · exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 y.2)
    · apply Subtype.ext; apply Subtype.ext; exact congrArg (fun q : H₁ => (q : Over.mk x ⟶ P.A)) h
    · refine ⟨⟨⟨a.1, ?_⟩, ?_⟩, rfl⟩
      · have := a.2
        simp only [H₁, MonoidHom.mem_ker, powMonoidHom_apply] at this
        simp [H₂, MonoidHom.mem_ker, sq, pow_mul, this]
      · exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 a.2)
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker, e₂, ← pow_mul, mul_comm 2, pow_mul,
    sq, mul_comm] at hmul
  have hrange : Nat.card ψ.range = Nat.card H₁ := by
    rw [e₁]
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) hmul).symm
  have hle : ψ.range ≤ H₁ := by
    rintro _ ⟨y, rfl⟩
    have := y.2
    simp only [H₂, MonoidHom.mem_ker, powMonoidHom_apply] at this
    simp [ψ, H₁, MonoidHom.mem_ker, ← pow_mul, ← sq, this]
  have heq := Subgroup.eq_of_le_of_card_ge hle hrange.ge
  have hzm : z ∈ ψ.range := heq ▸ (show z ∈ H₁ by simpa [H₁, MonoidHom.mem_ker] using hz)
  obtain ⟨y, hy⟩ := hzm
  exact ⟨y.1, hy⟩

end GlobalTheory.UMin.RealTh


open GlobalTheory.UMin.RealTh in
theorem GlobalTheory.UMin.thList_real : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A)) (c : Fin N → K), ThList ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) pt c → (∀ x, ∃ b, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ K _ i N pt c H
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hkK : ((S.r * S.N : ℕ) : K) ≠ 0 := by
    have := S.unit.map (i.comp (algebraMap o S.R))
    rw [map_natCast] at this
    exact this.ne_zero
  let β : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk (spMap i) (by simp)
  let j : K →+* AlgebraicClosure K := algebraMap _ _
  let u : Over.mk (spMap j ≫ spMap i ≫ 𝟙 (Sp S.R)) ⟶ Over.mk (spMap i ≫ 𝟙 (Sp S.R)) := Over.homMk (spMap j) rfl
  have hkK' : ((S.r * S.N : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast j]; exact (map_ne_zero j).2 hkK
  have down : ∀ y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A, y ^ (S.r * S.N) = 1 → ∃ b, y = β ≫ ρ.pt b := by
    intro y hy
    obtain ⟨b, hb, -⟩ := ρ.pt_bij (AlgebraicClosure K) (spMap j ≫ spMap i ≫ 𝟙 _) (u ≫ y)
      (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
    refine ⟨b, TorsionFieldExt.comp_injective u _ ?_⟩
    refine hb.symm.trans (Over.OverMorphism.ext ?_)
    simp [u, β]
  constructor
  · intro x
    have h := H.2.1 x
    obtain ⟨b, hb⟩ := down (pt x ^ (S.r * S.N)) (by rw [← pow_mul, ← sq]; exact h.1)
    exact ⟨b, GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root o Ω S ρ K i b (pt x) (c x) hb h⟩
  · intro b
    have tb : ρ.pt b ^ (S.r * S.N) = 1 := (ρ.fr_tors b).1
    obtain ⟨y, hy⟩ := exists_pow_eq hL ρ.P (spMap j ≫ spMap i ≫ 𝟙 _) hkK' (u ≫ β ≫ ρ.pt b)
      (by rw [← MonObj.comp_pow, ← MonObj.comp_pow, tb, MonObj.comp_one, MonObj.comp_one])
    obtain ⟨a, ha⟩ := H.2.2 (AlgebraicClosure K) j y
      (by rw [sq, pow_mul, hy, ← MonObj.comp_pow, ← MonObj.comp_pow, tb, MonObj.comp_one, MonObj.comp_one])
    have e1 : u ≫ pt a = y := Over.OverMorphism.ext ha.symm
    have e2 : pt a ^ (S.r * S.N) = β ≫ ρ.pt b :=
      TorsionFieldExt.comp_injective u _ (by
        show u ≫ _ = u ≫ _
        rw [MonObj.comp_pow, e1, hy])
    exact ⟨a, GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root o Ω S ρ K i b (pt a) (c a) e2 (H.2.1 a)⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListRealisedSystemUpToRootsOfUnityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A)) (c : Fin N → K), ThList ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) pt c → (∀ x, ∃ b, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  first | exact @GlobalTheory.UMin.thList_real | exact GlobalTheory.UMin.thList_real | (intros; apply GlobalTheory.UMin.thList_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.DetHT

namespace GlobalTheory.DetHT.RegLoc

theorem mem_basicOpen_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (c : Γ(X, U)) :
    x ∈ X.basicOpen c ↔ c ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h₂ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen c ↔ c ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    change hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  rwa [hU.fromSpec_primeIdealOf] at h₂

theorem eval_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R]
    (κ : Γ(X, U) →+* R) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) ⁻¹ᵁ U) (s : Γ(X, U)) :
    (((Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec).appLE U ⊤ h) ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom s = κ s := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have e1 : (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec).appLE U ⊤ h =
      hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom κ)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have e2 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have e3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom κ)).appTop =
      CommRingCat.ofHom κ ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom κ)).symm
  rw [e1, e2, e3]
  simp

theorem ideal_ne_top {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (hN : IsIntegrallyClosed (X.presheaf.stalk x)) {𝔪 : Ideal Γ(X, U)} (h𝔪 : 𝔪 ≠ ⊤)
    (hP : (hU.primeIdealOf ⟨x, hx⟩).asIdeal ≤ 𝔪) {g : X.functionField} (hg : g ≠ 0) (hreg : ¬ RegAt x g) :
    𝔪.map (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) {g⁻¹})) ⊔
      Ideal.span {(⟨g⁻¹, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin Γ(X, U) {g⁻¹})} ≠ ⊤ := by
  intro heq
  letI := invertibleOfNonzero (inv_ne_zero hg)
  obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top g⁻¹ 𝔪 h𝔪 heq
  rw [invOf_eq_inv, inv_inv] at hpx
  have hlc : p.leadingCoeff ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := fun h =>
    h𝔪 ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem (hP h) hp))
  have hu : IsUnit (X.presheaf.germ U x hx p.leadingCoeff) :=
    (X.mem_basicOpen _ _ hx).1 ((mem_basicOpen_iff hU hx _).2 hlc)
  have hgm : ∀ a : Γ(X, U), algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx a) =
      algebraMap Γ(X, U) X.functionField a := fun a => algebraMap_germ hx a
  let q := p.map (X.presheaf.germ U x hx).hom
  have hq : Polynomial.aeval g q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    convert hpx using 1
    rw [Polynomial.aeval_def]
    congr 1
    ext a
    exact hgm a
  have hlq : q.leadingCoeff = X.presheaf.germ U x hx p.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hu.ne_zero
  have hint : IsIntegral (X.presheaf.stalk x) g := by
    refine ⟨Polynomial.C (hu.unit⁻¹ : (X.presheaf.stalk x)ˣ).1 * q,
      Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlq]; simp), ?_⟩
    rw [← Polynomial.aeval_def, map_mul, hq, mul_zero]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk x) (K := X.functionField)).1 hint
  exact hreg ⟨y, hy⟩

theorem valAt_chart {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) {K : Type} [Field K]
    (κ : Γ(X, U) →+* K) (s : Γ(X, U)) :
    RegAt (below (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec)) (algebraMap Γ(X, U) X.functionField s) ∧
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) (algebraMap Γ(X, U) X.functionField s) = κ s := by
  have ht : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) ⁻¹ᵁ U := fun x _ =>
    (Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩
  have hb : below (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) ∈ U := ht trivial
  refine ⟨⟨_, algebraMap_germ hb s⟩, ?_⟩
  rw [← eval_fromSpec hU κ ht s, ← OfModel.valAt_fnOf _ hb ht]
  rfl

theorem valAt_div {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) {K : Type} [Field K]
    (κ : Γ(X, U) →+* K) (a b : Γ(X, U)) (hb : κ b ≠ 0) {g : X.functionField}
    (hg : g * algebraMap Γ(X, U) X.functionField b = algebraMap Γ(X, U) X.functionField a) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) g * κ b = κ a := by
  set y : Sp K ⟶ X := Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec with hy
  obtain ⟨⟨b', hb'⟩, hvb⟩ := valAt_chart hU κ b
  obtain ⟨⟨a', ha'⟩, hva⟩ := valAt_chart hU κ a
  rw [← hy] at hvb hva
  have hb1 : (Scheme.stalkClosedPointTo y).hom b' = κ b := by rw [← hvb, ← hb', Base.valAt_stalk]
  have ha1 : (Scheme.stalkClosedPointTo y).hom a' = κ a := by rw [← hva, ← ha', Base.valAt_stalk]
  have hu : IsUnit b' := (isUnit_map_iff (Scheme.stalkClosedPointTo y).hom b').1 (by rw [hb1]; exact hb.isUnit)
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have hg' : g = algebraMap _ X.functionField (a' * c) := by
    rw [map_mul, ha', ← hg, ← hb', mul_assoc, ← map_mul, hc, map_one, mul_one]
  rw [hg', Base.valAt_stalk, ← hb1, ← ha1, ← map_mul, mul_assoc, mul_comm c, hc, mul_one]

theorem place_eq {F : Type} [Field F] [NumberField F] {v v' : HeightOneSpectrum (𝓞 F)} (e : Ext v')
    (h : ∀ a ∈ v.asIdeal, ∃ c : e.O, (c : AlgebraicClosure F) = algebraMap F _ (algebraMap (𝓞 F) F a) ∧ ¬ IsUnit c) :
    v' = v := by
  have hle : v.asIdeal ≤ v'.asIdeal := fun a ha => by
    obtain ⟨c, hc, hu⟩ := h a ha
    have h1 : e.w c < 1 := not_le.1 fun h' => hu (RegCrit.isUnit_of_one_le e c h')
    rw [hc, e.w_alg] at h1
    rw [← FinitePlace.norm_lt_one_iff_mem F v' a, FinitePlace.norm_embedding]
    exact h1
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle).symm

theorem exists_hom (F : Type) [Field F] [NumberField F] (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (hinj : Function.Injective (algebraMap A K)) [Algebra (𝓞 F) A] [Algebra.FiniteType (𝓞 F) A] [CharZero A]
    (𝔪 : Ideal A) (t : K)
    (hne : 𝔪.map (algebraMap A (Algebra.adjoin A {t})) ⊔
      Ideal.span {(⟨t, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {t})} ≠ ⊤) (c : A) (hc : c ≠ 0) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : A →+* e.O) (τ : e.O),
      (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) A a) : e.O) : AlgebraicClosure F) =
        algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (∀ m ∈ 𝔪, ¬ IsUnit (φ m)) ∧ φ c ≠ 0 ∧ ¬ IsUnit τ ∧
      ∀ a b : A, t * algebraMap A K a = algebraMap A K b → τ * φ a = φ b := by
  let B := Algebra.adjoin A {t}
  have hB : Function.Injective (algebraMap A B) := fun a b h => hinj (congrArg Subtype.val h)
  let _ : Algebra (𝓞 F) B := ((algebraMap A B).comp (algebraMap (𝓞 F) A)).toAlgebra
  have : IsScalarTower (𝓞 F) A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : Algebra.FiniteType A B := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton t)
  have : Algebra.FiniteType (𝓞 F) B := Algebra.FiniteType.trans (S := A) inferInstance h1
  have : CharZero B := charZero_of_injective_algebraMap hB
  obtain ⟨𝔫, h𝔫, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F B 𝔫 h𝔫 (algebraMap A B c) fun h => hc (hB (by rw [h, map_zero]))
  have hn : ∀ s ∈ 𝔫, ¬ IsUnit (φ s) := fun s hs => by
    rw [← h₂] at hs
    exact hs
  refine ⟨v, e, φ.comp (algebraMap A B), φ ⟨t, Algebra.subset_adjoin rfl⟩, h₁,
    fun m hm => hn _ (hle (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hm))), h₃,
    hn _ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))), fun a b hab => ?_⟩
  simp only [RingHom.comp_apply]
  rw [← map_mul]
  exact congrArg φ (Subtype.ext hab)


open GlobalTheory.TrueGeo.HorizPt in
theorem main : RegLocSt := by
  intro F _ _ Y V U₀ W hW v g hf x hx hxv
  by_contra hreg
  have hg0 : g ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : U ≤ U₀ := hUW
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (GlobalTheory.TrueGeo.HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  have := functionField_isFractionRing_of_isAffineOpen V.X U hU
  obtain ⟨w, hw⟩ := hW
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le ⟨_, gen_mem hw⟩ (gen_mem hxU)
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hh
    exact hh
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨x, hxU⟩).isPrime.ne_top
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(V.X, U)) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj := IsFractionRing.injective Γ(V.X, U) V.X.functionField
  have hb1 : algebraMap Γ(V.X, U) V.X.functionField b ≠ 0 := fun h => hb0 (hinj (by rw [h, map_zero]))
  have hgb : g * algebraMap Γ(V.X, U) V.X.functionField b = algebraMap Γ(V.X, U) V.X.functionField a := by
    rw [← hab, div_mul_cancel₀ _ hb1]
  obtain ⟨v', e, φ, τ, h₁, h₂, h₃, h₄, h₅⟩ := exists_hom F Γ(V.X, U) V.X.functionField hinj 𝔪 g⁻¹
    (ideal_ne_top hU hxU (V.normal x).2 h𝔪.ne_top hle' hg0 hreg) (b * h) (mul_ne_zero hb0 hh0)
  obtain rfl : v' = v := place_eq e fun c hc => by
    refine ⟨_, h₁ c, h₂ _ (hle' ?_)⟩
    have hx' : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
    have hc' : c ∈ ((hU.fromSpec ≫ V.p) (hU.primeIdealOf ⟨x, hxU⟩)).asIdeal := by
      change c ∈ (V.p (hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩))).asIdeal
      rw [hx', hxv]
      exact hc
    rw [fromSpec_str] at hc'
    exact hc'
  have hτ : τ * φ a = φ b := h₅ a b (by rw [← hgb, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul])
  rw [map_mul] at h₃
  let κ : Γ(V.X, U) →+* AlgebraicClosure F := e.O.subtype.comp φ
  have hκ : ∀ s, φ s ≠ 0 → κ s ≠ 0 := fun s hs h => hs (Subtype.ext h)
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hyt : spMap e.O.subtype ≫ yt = Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec := by
    simp only [yt]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  have hval := hf e (V.pb.lift _ _ hw) yt (V.pb.lift_snd _ _ hw) hy.symm
    (fun x _ => hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)) (by
      rw [hy, hyt]
      refine hhW ?_
      change PrimeSpectrum.comap κ (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen h
      rw [hU.fromSpec_preimage_basicOpen]
      intro h'
      have h'' : κ h ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h'
      rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h''
      exact hκ h (right_ne_zero_of_mul h₃) h'')
  rw [hy, hyt] at hval
  have hκb := hκ b (left_ne_zero_of_mul h₃)
  have hdiv := valAt_div hU κ a b hκb hgb
  have hτ' : (τ : AlgebraicClosure F) * κ a = κ b := congrArg Subtype.val hτ
  rw [← hdiv, ← mul_assoc] at hτ'
  have hone := congrArg e.w (mul_right_cancel₀ hκb (hτ'.trans (one_mul _).symm))
  rw [map_mul, map_one] at hone
  exact h₄ (RegCrit.isUnit_of_one_le e τ (hone.ge.trans (mul_le_of_le_one_right (e.w.nonneg _) hval)))

end GlobalTheory.DetHT.RegLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatLinearCombination
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem chernMat_tens (L M : HermLB p) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    chernMat ((L.tens M).φ σ) c y = chernMat (L.φ σ) c y + chernMat (M.φ σ) c y := by
  have ha := mem_pick (L.φ σ).isLB y
  have hb := mem_pick (M.φ σ).isLB y
  unfold chernMat
  rw [c.hess_eq ((L.tens M).cInf σ) hy (i := (pick (L.φ σ).isLB y, pick (M.φ σ).isLB y))
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y)]
  change c.hess ((L.φ σ).tens (M.φ σ)) _ y = _
  exact FlatMass.hess_tens (L.cInf σ) (M.cInf σ) hy ha hb

def chernHom (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    HermLB.IsomClass p →+ Matrix (Fin D) (Fin D) ℂ :=
  AddMonoidHom.mk' (M := HermLB.IsomClass p)
    (Quotient.lift (s := HermLB.isometrySetoid p) (fun L => chernMat (L.φ σ) c y)
    fun _ _ h => chernMat_congr h c hy) (by rintro ⟨L⟩ ⟨M⟩; exact chernMat_tens L M c hy)

theorem chernHom_icls (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) (L : HermLB p) :
    chernHom c hy L.icls = chernMat (L.φ σ) c y := rfl

theorem chernMat_comb : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (κ : Type)
    [Fintype κ] (L : κ → HermLB p) (n : κ → ℤ) (c : AlgChart p σ D), ∀ y ∈ c.e.source,
    chernMat ((ArInt.comb L n).φ σ) c y = ∑ j, (n j : ℂ) • chernMat ((L j).φ σ) c y := by
  intro k _ X p σ D κ _ L n c y hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← chernHom_icls c hy, icls_comb, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, chernHom_icls, Int.cast_smul_eq_zsmul]

end GlobalTheory.MixDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

variable {S : Scheme.{0}} (G : Over S) (L : LB G.left)

abbrev LocSec (N : S.Opens) : Type := ∀ i : L.ι, Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ N)

variable {G L}

def IsLocSec {N : S.Opens} (s : LocSec G L N) : Prop :=
  ∀ i j, resG _ (fun _ hx => ⟨hx.1.1, hx.2⟩ : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
    resG _ (fun _ hx => hx.1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U i ⊓ L.U j) (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) *
      resG _ (fun _ hx => ⟨hx.1.2, hx.2⟩ : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U j ⊓ G.hom ⁻¹ᵁ N) (s j)

theorem lpow_U_le [GrpObj G] {K : Type} [Field K] {ξ : Sp K ⟶ S} {N : S.Opens} (hξ : Set.range ξ ⊆ N)
    (j : Fin 1 → L.ι) :
    (LPow G L 1 (Over.mk ξ)).U j ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ N) := by
  intro y hy
  refine ⟨Set.mem_iInter.1 hy 0, ?_⟩
  have e : (snd (Over.mk ξ) G).left ≫ G.hom = (fst (Over.mk ξ) G).left ≫ ξ :=
    (Over.w (snd (Over.mk ξ) G)).trans (Over.w (fst (Over.mk ξ) G)).symm
  show G.hom ((snd (Over.mk ξ) G).left y) ∈ N
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact hξ ⟨_, rfl⟩

def genPull [GrpObj G] {K : Type} [Field K] {ξ : Sp K ⟶ S} {N : S.Opens} (hξ : Set.range ξ ⊆ N)
    (s : LocSec G L N) (j : Fin 1 → L.ι) : Γ((Over.mk ξ ⊗ G).left, (LPow G L 1 (Over.mk ξ)).U j) :=
  ((snd (Over.mk ξ) G).left.appLE _ _ (lpow_U_le hξ j)).hom (s (j 0))

def GenIs [GrpObj G] {K : Type} [Field K] (ξ : Sp K ⟶ S) {N : S.Opens} (s : LocSec G L N)
    (v : SecM G L 1 (Over.mk ξ)) : Prop :=
  ∃ hξ : Set.range ξ ⊆ N, genPull hξ s = v.1

def FibNz {N : S.Opens} (s : LocSec G L N) (W : S.Opens) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), Set.range x ⊆ W →
    ∃ (y : Sp K ⟶ G.left) (i : L.ι), y ≫ G.hom = x ∧ Set.range y ⊆ (L.U i ⊓ G.hom ⁻¹ᵁ N : G.left.Opens) ∧
      valF y _ (s i) ≠ 0

theorem isLocSec_zero {N : S.Opens} : IsLocSec (0 : LocSec G L N) := fun i j => by
  simp [Pi.zero_apply, map_zero, mul_zero]

end GlobalTheory.UMin.ThBdl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismClosedFibreTorusCharac
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismClosedFibreTorusCharac
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.Eq8

theorem eq_torusMap_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] (h : X →+ X)
    (t : splitTorus S X ⟶ splitTorus S X) (ht : TorusEndOf X h t) : t = GlobalTheory.SplitTorus.torusMap S h := by
  refine (GlobalTheory.SplitTorus.eq_torusMap_iff t h).2 fun b => ?_
  have e := congrArg Units.val (ht b)
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X b)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X b).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val] at e
  exact e

theorem endChar_endU : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (E : EndU U.toUnifPre), EndChar U E.aG E.h := by
  intro V₁ _ _ _ _ D P G _ _ _ U E κ _ a ha G₀ _ φ h f₀ hf
  obtain ⟨t, ht, hi⟩ := E.i_lin 0
  have htm := eq_torusMap_of_torusEndOf E.h t ht
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift ha h
  have e : f₀.left ≫ GlobalTheory.TorusPart.thickLift ha h =
      GlobalTheory.TorusPart.thickLift ha h ≫ ((Over.pullback (thick V₁ (maximalIdeal V₁) 0)).map E.aG).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, hf, Category.assoc]
      simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
      rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, Over.w]
  have hc := GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e (U.gt 0).i
  unfold GlobalTheory.TorusPart.gtTorus
  rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

end GlobalTheory.Poinc.Eq8
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismClosedFibreTorusCharacStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_endomorphism_closedFibreTorus_characterMap : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (E : EndU U.toUnifPre), EndChar U E.aG E.h := by
  first | exact @GlobalTheory.Poinc.Eq8.endChar_endU | exact GlobalTheory.Poinc.Eq8.endChar_endU | (intros; apply GlobalTheory.Poinc.Eq8.endChar_endU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

variable {X Z : Scheme.{0}} {k : ℕ}

def GermRatioAgree {L : LB X} (v v' : Z ⟶ X) (s₀ : H0 L k) (i i'' : Fin 1 → L.ι) (z : Z) : Prop :=
  v z ∈ secChart L i ∧ v' z ∈ secChart L i'' ∧
    IsUnit (secGerm v z s₀ i) ∧ IsUnit (secGerm v' z s₀ i'') ∧
    ∀ s₁ : H0 L k, secGerm v z s₁ i * secGerm v' z s₀ i'' = secGerm v z s₀ i * secGerm v' z s₁ i''

end GlobalTheory.Mum
end
end
