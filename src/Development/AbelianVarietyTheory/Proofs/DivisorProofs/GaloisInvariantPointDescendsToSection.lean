module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantPointDescendsToSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfGaloisFixed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GaloisFixedSectionExtension

theorem extend_section {V : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] (X : Scheme.{0})
    (p : X ⟶ Spec (CommRingCat.of V)) [IsFinite p] (g : Spec (CommRingCat.of (FractionRing V)) ⟶ X)
    (hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :
    ∃ s : Spec (CommRingCat.of V) ⟶ X, s ≫ p = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ s = g := by
  haveI : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ X.isoSpec.hom)
  obtain ⟨π, hπ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  have hfin : π.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hπ]
    infer_instance
  have hcomp : π ≫ φ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hπ, Category.assoc, Iso.hom_inv_id_assoc, hg]
  have hc : ∀ v : V, φ.hom (π.hom v) = algebraMap V (FractionRing V) v := fun v =>
    congrArg (fun f => f.hom v) hcomp
  have hmem : ∀ a, φ.hom a ∈ (algebraMap V (FractionRing V)).range := by
    intro a
    obtain ⟨q, hq, hqa⟩ := hfin.to_isIntegral a
    have hint : IsIntegral V (φ.hom a) := by
      refine ⟨q, hq, ?_⟩
      have h1 := Polynomial.hom_eval₂ q π.hom φ.hom a
      rw [hqa, map_zero] at h1
      have h2 : φ.hom.comp π.hom = algebraMap V (FractionRing V) := RingHom.ext hc
      rw [h2] at h1
      exact h1.symm
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V _
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap V (FractionRing V)).rangeRestrict_surjective⟩
  let ψ : Γ(X, ⊤) →+* V := e.symm.toRingHom.comp (φ.hom.codRestrict _ hmem)
  have hψ : ∀ a, algebraMap V (FractionRing V) (ψ a) = φ.hom a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict _ hmem a))
  have hψφ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V (FractionRing V)) = φ := by
    ext a
    exact hψ a
  have hπψ : π ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
    ext v
    exact hinj ((hψ _).trans (hc v))
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hπ, ← Spec.map_comp, hπψ, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hψφ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem exists_section_of_galoisFixed : ∀ (V : Type) [inst : CommRing V] [inst_1 : IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : CategoryTheory.Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V)), AlgebraicGeometry.IsFinite (CategoryTheory.Over.hom N) → ∀ (nb : ReciprocityTheory.ChartRestriction.G.Out.TF (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ (σ : Gal(AlgebraicClosure (FractionRing V)/FractionRing V)), CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (AlgHom.toRingHom (↑σ : AlgebraicClosure (FractionRing V) →ₐ[FractionRing V] AlgebraicClosure (FractionRing V)))) (CategoryTheory.Over.Hom.left nb) = CategoryTheory.Over.Hom.left nb) → ∃ (s : CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V)) ⟶ N), nb = CategoryTheory.CategoryStruct.comp (CategoryTheory.SemiCartesianMonoidalCategory.toUnit (ReciprocityTheory.ChartRestriction.G.Out.TF (AlgebraicClosure (FractionRing V)))) s := by
  intro V _ _ _ hV N hN nb hfix
  haveI := hV
  haveI := hN
  haveI : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨g, hg⟩ := GlobalTheory.TorsDescent.descend_point (K := FractionRing V) N.left nb.left hfix
  have hg' : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫ g =
      nb.left := hg
  have hw : nb.left ≫ N.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := Over.w nb
  have hgp : g ≫ N.hom = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (g ≫ N.hom)
    rw [← hχ]
    congr 1
    have h1 : χ ≫ CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        CommRingCat.ofHom (algebraMap V (FractionRing V)) ≫
          CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, hχ, ← hw, ← hg', Category.assoc]
    ext v
    exact (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective
      (congrArg (fun f => f.hom v) h1)
  obtain ⟨s, hs, hsg⟩ := extend_section N.left N.hom g hgp
  refine ⟨Over.homMk s hs, ?_⟩
  apply Over.OverMorphism.ext
  show nb.left = (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) ≫ s
  rw [Category.assoc, hsg, hg']

end GlobalTheory.GaloisFixedSectionExtension
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantPointDescendsToSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FinDescent

theorem galoisFixed_point_of_finite : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : Over (Sp V)), IsFinite N.hom → ∀ (nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V), spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left) → ∃ s : 𝟙_ (Over (Sp V)) ⟶ N, nb = toUnit _ ≫ s := by
  first
  | exact @_root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed
  | exact _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed
  | (apply _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed ..)

end GlobalTheory.FinDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantPointDescendsToSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_invariant_point_descends_to_section : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : Over (Sp V)), IsFinite N.hom → ∀ (nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V), spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left) → ∃ s : 𝟙_ (Over (Sp V)) ⟶ N, nb = toUnit _ ≫ s := by
  first | exact @GlobalTheory.FinDescent.galoisFixed_point_of_finite | exact GlobalTheory.FinDescent.galoisFixed_point_of_finite | (intros; apply GlobalTheory.FinDescent.galoisFixed_point_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBimultiplicativeWeilPairingTorsionAxes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBimultiplicativeWeilPairingTorsionAxes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCommPairing

open GlobalTheory.CechPic

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  ext
  have := congrArg (fun u : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u.val) h
  simpa [unitOn] using this

theorem unitOn_surj {R : Type} [CommRing R] (c : (Γ(Sp R, ⊤))ˣ) : ∃ z : Rˣ, unitOn z = c := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom c, ?_⟩
  ext
  simp [unitOn]

theorem unitOn_mul {R : Type} [CommRing R] (a b : Rˣ) : unitOn (a * b) = unitOn a * unitOn b :=
  map_mul _ a b

theorem theta_lbPow {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (k : ℕ)
    {T : Over S} (θ : Out.ThetaGrp B L (k : ℤ) T) :
    ∃ θ' : Out.ThetaGrp B (Hecke.lbPow L k) 1 T, θ'.pt = θ.pt := by
  have hQ : (Hecke.lbPow L k).IsLB := LB.isLB_linComb hL _ _
  have hcls : cls _ hQ = k • cls L hL := by
    refine (cls_linComb hL (K := Fin k) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _ : (Out.thetaLB B L (k : ℤ) θ.pt).IsLB)).2 ⟨θ.φ, θ.isGen⟩
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB B (Hecke.lbPow L k) 1 θ.pt), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hQ _ _)).1 ?_
    rw [cls_linComb hQ, Fin.sum_univ_two, hcls]
    rw [cls_linComb hL, Fin.sum_univ_two] at h0
    simp at h0 ⊢
    exact h0
  exact ⟨⟨_, u, hu⟩, rfl⟩

theorem exists_weilIs_lbPow {S : Scheme.{0}} {B : Over S} [GrpObj B] (hB : IsAbelianScheme B) {L : LB B.left}
    (hL : L.IsLB) (k : ℕ) {T : Over S} {x y : T ⟶ B} {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs B L (k : ℤ) x y c) :
    ∃ c' : Γ(T.left, ⊤)ˣ, Out.WeilIs B (Hecke.lbPow L k) 1 x y c' := by
  have hQ : (Hecke.lbPow L k).IsLB := LB.isLB_linComb hL _ _
  refine CommutatorPairing.exists_weilIs GlobalTheory.globalFns_holds hB hQ (fun p => ?_) (fun p => ?_)
  · obtain ⟨V, hV, ⟨θx, -, hx, -⟩, -⟩ := h p
    obtain ⟨θ, hθ⟩ := theta_lbPow hL k θx
    exact ⟨V, hV, θ, hθ.trans hx⟩
  · obtain ⟨V, hV, ⟨-, θy, -, hy⟩, -⟩ := h p
    obtain ⟨θ, hθ⟩ := theta_lbPow hL k θy
    exact ⟨V, hV, θ, hθ.trans hy⟩

theorem lift_mul_lift {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x x' : T ⟶ A) (y y' : T ⟶ B) :
    lift x y * lift x' y' = lift (x * x') (y * y') := by
  ext1 <;> simp only [MonObj.mul_comp, lift_fst, lift_snd]

theorem lift_pow {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x : T ⟶ A) (y : T ⟶ B) (m : ℕ) :
    lift x y ^ m = lift (x ^ m) (y ^ m) := by
  ext1 <;> simp only [MonObj.pow_comp, lift_fst, lift_snd]

theorem lift_one_one {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] :
    (1 : T ⟶ A ⊗ B) = lift (1 : T ⟶ A) (1 : T ⟶ B) := by
  ext1 <;> simp only [MonObj.one_comp, lift_fst, lift_snd]

theorem exists_pairing : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (c : ℕ), (c : κ) ≠ 0 → ∃ e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ, (∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') u ↔ u = unitOn (e g g')) ∧ (∀ g₁ g₂ g' : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 → e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧ (∀ g g₁ g₂ : Over.mk x ⟶ A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 → e g (g₁ * g₂) = e g g₁ * e g g₂) := by
  intro S A _ _ P hA hP κ _ _ x c hc
  classical
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hQ : (Hecke.lbPow P c).IsLB := LB.isLB_linComb hP _ _
  have hc0 : 0 < c := Nat.pos_of_ne_zero fun h => hc (by rw [h, Nat.cast_zero])
  have ex : ∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 →
      ∃ z : κˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') (unitOn z) := by
    intro g g' hg hg'
    have hx : (lift g 1 : Over.mk x ⟶ G2 A) ^ c = 1 := by rw [lift_pow, hg, one_pow, lift_one_one]
    have hy : (lift 1 g' : Over.mk x ⟶ G2 A) ^ c = 1 := by rw [lift_pow, hg', one_pow, lift_one_one]
    obtain ⟨u, hu⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 A) P hAA hP κ x c hc0 hc _ _ hx hy
    obtain ⟨u', hu'⟩ := exists_weilIs_lbPow hAA hP c hu
    obtain ⟨z, rfl⟩ := unitOn_surj u'
    exact ⟨z, hu'⟩
  let e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ := fun g g' =>
    if h : g ^ c = 1 ∧ g' ^ c = 1 then (ex g g' h.1 h.2).choose else 1
  have he : ∀ g g' : Over.mk x ⟶ A, ∀ hg : g ^ c = 1, ∀ hg' : g' ^ c = 1,
      Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') (unitOn (e g g')) := by
    intro g g' hg hg'
    simp only [e, dif_pos (And.intro hg hg')]
    exact (ex g g' hg hg').choose_spec
  have hmulc : ∀ g₁ g₂ : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → (g₁ * g₂) ^ c = 1 := by
    intro g₁ g₂ h₁ h₂
    rw [mul_pow, h₁, h₂, _root_.one_mul]
  refine ⟨e, fun g g' hg hg' u => ⟨fun h => CommutatorPairing.weilIs_unique hG hAA hQ h (he g g' hg hg'),
    fun h => h ▸ he g g' hg hg'⟩, ?_, ?_⟩
  · intro g₁ g₂ g' h₁ h₂ h'
    have hm := DiagPairing.weilIs_mul_left hG hAA hQ (he g₁ g' h₁ h') (he g₂ g' h₂ h')
    rw [lift_mul_lift, _root_.mul_one] at hm
    apply unitOn_inj
    rw [unitOn_mul]
    exact CommutatorPairing.weilIs_unique hG hAA hQ (he _ _ (hmulc g₁ g₂ h₁ h₂) h') hm
  · intro g g₁ g₂ hg h₁ h₂
    have hm := CommPairing.weilIs_symm hQ (DiagPairing.weilIs_mul_left hG hAA hQ
      (CommPairing.weilIs_symm hQ (he g g₁ hg h₁)) (CommPairing.weilIs_symm hQ (he g g₂ hg h₂)))
    rw [lift_mul_lift, _root_.mul_one, mul_inv, inv_inv, inv_inv] at hm
    apply unitOn_inj
    rw [unitOn_mul]
    exact CommutatorPairing.weilIs_unique hG hAA hQ (he _ _ hg (hmulc g₁ g₂ h₁ h₂)) hm

end GlobalTheory.TorsionCommPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBimultiplicativeWeilPairingTorsionAxesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bimultiplicative_weilPairing_torsion_axes : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (c : ℕ), (c : κ) ≠ 0 → ∃ e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ, (∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') u ↔ u = unitOn (e g g')) ∧ (∀ g₁ g₂ g' : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 → e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧ (∀ g g₁ g₂ : Over.mk x ⟶ A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 → e g (g₁ * g₂) = e g g₁ * e g g₂) := by
  first | (exact @GlobalTheory.TorsionCommPairing.exists_pairing) | (exact GlobalTheory.TorsionCommPairing.exists_pairing) | (intros; apply GlobalTheory.TorsionCommPairing.exists_pairing  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfTorusHomOfZero
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

section SlopeTestRemainingChoices

variable {S T : Scheme.{0}} (f : T ⟶ S)

theorem pullback_prod_hom_ext {X Y : Over S} {W : Over T}
    {u v : W ⟶ (Over.pullback f).obj (X ⊗ Y)}
    (h₁ : u ≫ (Over.pullback f).map (fst X Y) = v ≫ (Over.pullback f).map (fst X Y))
    (h₂ : u ≫ (Over.pullback f).map (snd X Y) = v ≫ (Over.pullback f).map (snd X Y)) : u = v :=
  BinaryFan.IsLimit.hom_ext ((isLimitMapConeBinaryFanEquiv (Over.pullback f) _ _)
    (isLimitOfPreserves (Over.pullback f) (tensorProductIsBinaryProduct X Y))) h₁ h₂

theorem pullback_map_one {X G : Over S} [MonObj G] :
    (Over.pullback f).map (1 : X ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, Functor.map_comp]
  change _ = toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[G]
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (Functor.OplaxMonoidal.η (Over.pullback f))]
  exact toUnit_unique _ _

end SlopeTestRemainingChoices

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

section Torus

variable {S : Scheme.{0}} {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂]

theorem torusHomOf_iff_appTop' (h : X₂ → X₁) (t : splitTorus S X₁ ⟶ splitTorus S X₂) : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X₂ χ).val = (charUnit S X₁ (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X₂ χ)) : Γ((splitTorus S X₁).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X₂ χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusHomOf_unique {h : X₂ → X₁} {t t' : splitTorus S X₁ ⟶ splitTorus S X₂}
    (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (GlobalTheory.splitTorusPointsEquiv S X₂ _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop' _ _).1 ht,
    (torusHomOf_iff_appTop' _ _).1 ht']

theorem eq_one_of_torusHomOf_zero {t : splitTorus S X₁ ⟶ splitTorus S X₂}
    (ht : TorusHomOf (fun _ => (0 : X₁)) t) : t = 1 := by
  refine (GlobalTheory.splitTorusPointsEquiv S X₂ _).injective ?_
  rw [map_one]
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  have k : ∀ χ : X₂, (GlobalTheory.splitTorusPointsEquiv S X₂ _ t (Multiplicative.ofAdd χ)).val =
      (charUnit S X₁ 0).val := fun χ => by
    rw [GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop' _ _).1 ht]
  rw [k χ, ← k 0, ofAdd_zero, map_one]
  rfl

theorem torusHomOf_torusMap (q : X₂ →+ X₁) : TorusHomOf q (GlobalTheory.SplitTorusPow.torusMap S q) :=
  (torusHomOf_iff_appTop' _ _).2 fun χ => GlobalTheory.SplitTorusPow.torusMap_char q χ

end Torus

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem IsProdUnif.linHom_inl : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → LinHom U₁ U i₁ q₁ (lift (𝟙 G₁) 1) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₁ hi₁ hi₂
  have h1 : IsMonHom (1 : G₁ ⟶ G₂) := inferInstanceAs (IsMonHom (toUnit G₁ ≫ η[G₂]))
  have hi₂' : i₁ ≫ p₂ = 1 := hi₂.trans Hom.one_def.symm
  have hlim := hD.lim
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  ·
    have := (U₂.gt e).q_hom
    rw [← cancel_mono ((Over.pullback (thick R I e)).map (lift p₁ p₂))]
    refine pullback_prod_hom_ext _ ?_ ?_
    · simp only [Category.assoc, ← Functor.map_comp, lift_fst]
      rw [hU.q_pr₁ e, ← Category.assoc, ← Functor.map_comp, lift_fst, hi₁, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · simp only [Category.assoc, ← Functor.map_comp, lift_snd]
      rw [hU.q_pr₂ e, ← Category.assoc, ← Functor.map_comp, lift_snd, hi₂', pullback_map_one,
        pullback_map_one, MonObj.one_comp, MonObj.comp_one]
  ·
    have := (U₂.gt e).i_hom
    let E := Equiv.ofBijective _ hD.xsum
    let j₁ : D₁.toPre.X → D.toPre.X := fun y => E.symm (y, 0)
    let j₂ : D₂.toPre.X → D.toPre.X := fun y => E.symm (0, y)
    have hj₁ : ∀ y, q₁ (j₁ y) = y ∧ q₂ (j₁ y) = 0 := fun y => by
      have := E.apply_symm_apply (y, 0)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    have hj₂ : ∀ y, q₁ (j₂ y) = 0 ∧ q₂ (j₂ y) = y := fun y => by
      have := E.apply_symm_apply (0, y)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    obtain ⟨t₁, ht₁, hf⟩ := hU.i_pr₁ e j₁ (fun y => (hj₁ y).1) (fun y => (hj₁ y).2)
    obtain ⟨t₂, ht₂, hs⟩ := hU.i_pr₂ e j₂ (fun y => (hj₂ y).1) (fun y => (hj₂ y).2)
    let t := GlobalTheory.SplitTorusPow.torusMap (Sp (R ⧸ I ^ (e + 1))) q₁
    have ht : TorusHomOf q₁ t := torusHomOf_torusMap q₁
    have e₁ : t ≫ t₁ = 𝟙 _ := by
      have k := ht.comp ht₁
      simp only [fun y => (hj₁ y).1] at k
      exact torusHomOf_unique k (TorusHomOf.id _)
    have e₂ : t ≫ t₂ = 1 := by
      have k := ht.comp ht₂
      simp only [fun y => (hj₂ y).1] at k
      exact eq_one_of_torusHomOf_zero k
    refine ⟨t, ht, pullback_prod_hom_ext _ ?_ ?_⟩
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id, hf,
        ← Category.assoc, e₁, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp, lift_snd, hs, ← Category.assoc, e₂,
        pullback_map_one, MonObj.one_comp, MonObj.comp_one]

end GlobalTheory.MumProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSemiAbelianEndoTorsionExtend
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSemiAbelianEndoTorsionExtend
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat

theorem genFibre_endo_torsion : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∃ (A₀ : Over (Sp Ω)) (_ : GrpObj A₀) (a₀ : A₀.left ⟶ ρ.P.A.left) (ψ : A₀.left ⟶ FinalForm.G.left), IsGrpPullback A₀ ρ.P.A (spMap S.R.val.toRingHom) a₀ ∧ IsGrpPullback A₀ FinalForm.G M.pt ψ ∧ (∀ e : ρ.P.A ⟶ ρ.P.A, IsMonHom e → ∃ F : FinalForm.G ⟶ FinalForm.G, IsMonHom F ∧ ∀ e₀ : A₀ ⟶ A₀, e₀.left ≫ a₀ = a₀ ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left) ∧ ∀ b : S.Gam, ∃ gγ : Over.mk M.pt ⟶ FinalForm.G, gγ ^ (S.r * S.N) = 1 ∧ (∀ w : Sp Ω ⟶ A₀.left, w ≫ A₀.hom = 𝟙 _ → w ≫ a₀ = spMap S.R.val.toRingHom ≫ (ρ.pt b).left → w ≫ ψ = gγ.left) ∧ ∀ z, b ∈ S.HH M z → ExtNear gγ z := by
  intro o Ω _ _ _ S ρ M U₀ EE FinalForm hU
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x)
             (by rw [pullback.condition, Category.assoc, hx])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x := FinalForm.cart.1.lift_snd _ _ _
  have gA := isGrpPullback_pullback FinalForm.G M.pt
  have gη : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) FinalForm.G (x ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    gA.congr hx.symm hν₁.symm
  have gν : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) Q x ν := FinalForm.cart.cancel gη hν₂
  have gψ := gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)
  have gψ' : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) ρ.P.A (spMap S.R.val.toRingHom)
      (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := gψ.congr (FinalForm.u₀_gen x hx) rfl
  refine ⟨(Over.pullback M.pt).obj FinalForm.G, inferInstance, ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀,
    pullback.fst FinalForm.G.hom M.pt, gψ', gA, ?_, ?_⟩
  · intro e he
    haveI := he
    obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo gψ' e
    obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
    refine ⟨F, hF, fun e₀ he₀ => ?_⟩
    have hw'l : w'.left ≫ (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) = (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ e.left := by
      have := congrArg (fun z => z.left) (pa (𝟙 _))
      simpa [pushPt] using this
    have he₀w : e₀ = w' := hom_ext_of_pullback gψ' (he₀.trans hw'l.symm)
    rw [he₀w, ← hFw]
    simp only [Over.pullback_map_left, pullback.lift_fst]
  · intro b
    have hb : (spMap S.R.val.toRingHom ≫ (ρ.pt b).left) ≫ ρ.P.A.hom = 𝟙 _ ≫ spMap S.R.val.toRingHom := by
      rw [Category.assoc, Over.w (ρ.pt b)]; simp
    let w₀ := gψ'.1.lift _ _ hb
    have hw₁ : w₀ ≫ (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) = spMap S.R.val.toRingHom ≫ (ρ.pt b).left :=
      gψ'.1.lift_fst _ _ _
    have hw₂ : w₀ ≫ pullback.snd FinalForm.G.hom M.pt = 𝟙 _ := gψ'.1.lift_snd _ _ _
    let sec0 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G := Over.homMk w₀ hw₂
    let V : Over.mk M.pt ⟶ Over.mk (𝟙 (Sp Ω) ≫ M.pt) := Over.homMk (𝟙 _) (by simp)
    let gγ : Over.mk M.pt ⟶ FinalForm.G := V ≫ pushPt gA.1.w sec0
    have hgl : gγ.left = w₀ ≫ pullback.fst FinalForm.G.hom M.pt := by simp [gγ, V, pushPt, sec0]
    refine ⟨gγ, ?_, ?_, ?_⟩
    · have h0 : ρ.pt 0 = 1 := by
        have := ρ.pt_add 0 0
        rw [add_zero] at this
        exact mul_eq_left.1 this.symm
      have hpt : ∀ n : ℕ, (ρ.pt b) ^ n = ρ.pt (n • b) := by
        intro n
        induction n with
        | zero => simp [h0]
        | succ k ih => rw [pow_succ, ih, ← ρ.pt_add, succ_nsmul]
      have hrN : (S.r * S.N) • b = 0 := by
        funext i
        simp
      let U : Over.mk (𝟙 (Sp Ω) ≫ spMap S.R.val.toRingHom) ⟶ baseOver (Sp S.R) :=
        Over.homMk (spMap S.R.val.toRingHom) (by simp)
      have hs : pushPt gψ'.1.w sec0 = U ≫ ρ.pt b := by
        apply Over.OverMorphism.ext
        simp [pushPt, sec0, U, hw₁]
      have hsec : sec0 ^ (S.r * S.N) = 1 := by
        apply GlobalTheory.SymBaseChange.pushPt_injective gψ'
        have e1 : pushPt gψ'.1.w (sec0 ^ (S.r * S.N)) = (pushPt gψ'.1.w sec0) ^ (S.r * S.N) :=
          map_pow (pushHom gψ' _) sec0 _
        have e2 : pushPt gψ'.1.w (1 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G) = 1 :=
          map_one (pushHom gψ' _)
        have e3 : (U ≫ ρ.pt b) ^ (S.r * S.N) = U ≫ (ρ.pt b) ^ (S.r * S.N) :=
          (map_pow (preHom U) (ρ.pt b) _).symm
        have e4 : U ≫ (1 : baseOver (Sp S.R) ⟶ ρ.P.A) = 1 := map_one (preHom U)
        rw [e1, e2, hs, e3, hpt, hrN, h0, e4]
      have f1 : gγ ^ (S.r * S.N) = V ≫ (pushPt gA.1.w sec0) ^ (S.r * S.N) :=
        map_pow (preHom V) _ _
      have f2 : (pushPt gA.1.w sec0) ^ (S.r * S.N) = pushPt gA.1.w (sec0 ^ (S.r * S.N)) :=
        (map_pow (pushHom gA _) sec0 _).symm
      have f3 : pushPt gA.1.w (1 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G) = 1 :=
        map_one (pushHom gA _)
      have f4 : V ≫ (1 : Over.mk (𝟙 (Sp Ω) ≫ M.pt) ⟶ FinalForm.G) = 1 := map_one (preHom V)
      rw [f1, f2, hsec, f3, f4]
    · intro w h1 h2
      have : w = w₀ := gψ'.1.hom_ext (by rw [h2, hw₁]) (by
        show w ≫ pullback.snd FinalForm.G.hom M.pt = w₀ ≫ pullback.snd FinalForm.G.hom M.pt
        rw [hw₂]; exact h1)
      rw [this, hgl]
    · intro z hz
      obtain ⟨W, h, hzW, hh, hx'⟩ := FinalForm.sec z b hz
      refine ⟨W, h, hzW, hh, fun y hy => ?_⟩
      rw [hgl, hx' y (w₀ ≫ ν) hy ?_ ?_, Category.assoc, hν₁]
      · rw [Category.assoc, ← Category.assoc ν, hν₁, pullback.condition, ← Category.assoc, hw₂, Category.id_comp]
      · rw [Category.assoc]; exact hw₁

end GlobalTheory.Poinc.FibLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSemiAbelianEndoTorsionExtendStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_semiAbelian_endo_torsion_extend : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∃ (A₀ : Over (Sp Ω)) (_ : GrpObj A₀) (a₀ : A₀.left ⟶ ρ.P.A.left) (ψ : A₀.left ⟶ FinalForm.G.left), IsGrpPullback A₀ ρ.P.A (spMap S.R.val.toRingHom) a₀ ∧ IsGrpPullback A₀ FinalForm.G M.pt ψ ∧ (∀ e : ρ.P.A ⟶ ρ.P.A, IsMonHom e → ∃ F : FinalForm.G ⟶ FinalForm.G, IsMonHom F ∧ ∀ e₀ : A₀ ⟶ A₀, e₀.left ≫ a₀ = a₀ ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left) ∧ ∀ b : S.Gam, ∃ gγ : Over.mk M.pt ⟶ FinalForm.G, gγ ^ (S.r * S.N) = 1 ∧ (∀ w : Sp Ω ⟶ A₀.left, w ≫ A₀.hom = 𝟙 _ → w ≫ a₀ = spMap S.R.val.toRingHom ≫ (ρ.pt b).left → w ≫ ψ = gγ.left) ∧ ∀ z, b ∈ S.HH M z → ExtNear gγ z := by
  first | exact @GlobalTheory.Poinc.FibLat.genFibre_endo_torsion | exact GlobalTheory.Poinc.FibLat.genFibre_endo_torsion | (intros; apply GlobalTheory.Poinc.FibLat.genFibre_endo_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineThetaRootTwistTwistingSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedWeightDegree
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Proof.TwistedWeightDegree

theorem degW_twist : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ (G₀ G : WTZ D.host.E) (s : ∀ Z : Comp Xo c, TwSec U (xiR D) Z G₀) (B : Finset ℕ) (τ : ℝ), Even G.2 → (∀ p ∈ B, p.Prime) → (∀ Z, IntOff B (s Z).lo) → (∀ Z, τ ≤ (s Z).degLo) → GoodW U (xiR D) V dict G → GoodW U (xiR D) V dict (G + G₀) ∧ rankW U (G + G₀) = rankW U G ∧ degW U (xiR D) V dict G + (rankW U G : ℝ) * (τ - logSum B) ≤ degW U (xiR D) V dict (G + G₀) := by
  intro D H Dw l Xo c r U V dict hC G₀ G s B τ hev hB hint hτ hG
  have hU : ∀ σ, GoodEmb c σ → IsUnf (U σ) := fun σ hσ => (hC.2 σ hσ).1
  have hA : ∀ G' : WTZ D.host.E, Adds U V dict G' := fun G' =>
    GlobalTheory.T.component_ranks_degrees_add_with_masses D H Dw l Xo c r U V dict G' (GlobalTheory.T.cuspForms_supLattice_split_over_components D H Dw l Xo c r U V dict hU G')
      ((GlobalTheory.T.components_peterssonOrthogonal_and_masses D H Dw l Xo c r U V dict hC G').1)
  have hOn : ∀ Z, GoodOn U (xiR D) V dict Z G := (hA G).1.1 hG
  have hgr : ∀ Z, GoodOn U (xiR D) V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := fun Z =>
    GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G hU hev (hOn Z)
  have hG' : GoodW U (xiR D) V dict (G + G₀) := (hA (G + G₀)).1.2 (fun Z => (hgr Z).1)
  obtain ⟨-, hr1, -, -, hd1⟩ := (hA G).2 hG
  obtain ⟨-, hr2, -, -, hd2⟩ := (hA (G + G₀)).2 hG'
  have hrank : rankW U (G + G₀) = rankW U G := by
    rw [hr1, hr2]; exact finsum_congr fun Z => (hgr Z).2
  refine ⟨hG', hrank, ?_⟩
  haveI : Finite (Comp Xo c) := finite_comp
  letI := Fintype.ofFinite (Comp Xo c)
  have hZ : ∀ Z, degOn U (xiR D) V dict Z G + (rankOn U Z G : ℝ) * (τ - logSum B) ≤
      degOn U (xiR D) V dict Z (G + G₀) := fun Z => by
    have h1 := GlobalTheory.T.cuspForm_supLattice_degree_twist_lower_bound D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G B hU hev hB (hint Z) (hOn Z)
    have h2 : (rankOn U Z G : ℝ) * (τ - logSum B) ≤ (rankOn U Z G : ℝ) * ((s Z).degLo - logSum B) :=
      mul_le_mul_of_nonneg_left (by linarith [hτ Z]) (Nat.cast_nonneg _)
    linarith
  rw [hd1, hd2, hr1]
  simp only [finsum_eq_sum_of_fintype, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro Z _
  rw [(hgr Z).2]
  linarith [hZ Z]

end GlobalTheory.Proof.TwistedWeightDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineThetaRootTwistTwistingSection
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

noncomputable section

namespace GlobalTheory.FlatRootTwist

theorem intOff_nsmul {K : Type} [Field K] [NumberField K] {B : Finset ℕ} {ρ : HeightOneSpectrum (𝓞 K) → ℝ}
    (h : IntOff B ρ) (n : ℕ) : IntOff B (n • ρ) := by
  intro v hv
  obtain ⟨k, hk⟩ := h v hv
  refine ⟨n * k, ?_⟩
  simp [hk]

theorem twSec_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {x : ℝ} {Z : Comp Xo c} {G G' : WTZ E} (hG : G = G') (s : TwSec U x Z G) :
    ∃ t : TwSec U x Z G', t.lo = s.lo ∧ t.degLo = s.degLo := by
  subst hG
  exact ⟨s, rfl, rfl⟩

theorem flat_root_twist : GlobalTheory.Published.AbelianDeRham → ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → FlatExists U (xiR D) → UnramPts Xo c (badPrimes H l) → ∀ (w : Psi H → ℤ) (m : ℕ), (∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m), IntOff (badPrimes H l) t.lo ∧ (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) ≤ t.degLo) ∧ ∀ (u : GlobalTheory.AllWt.Weight Dw) (n : ℤ), (∀ Z : Comp Xo c, GoodOn U (xiR D) V dict Z (wtOf Dw u n) → GoodOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankOn U Z (wtOf Dw (u + parWt Dw w) (n + m)) = rankOn U Z (wtOf Dw u n) ∧ degOn U (xiR D) V dict Z (wtOf Dw u n) + (rankOn U Z (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m))) ∧ (GoodW U (xiR D) V dict (wtOf Dw u n) → GoodW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankW U (wtOf Dw (u + parWt Dw w) (n + m)) = rankW U (wtOf Dw u n) ∧ degW U (xiR D) V dict (wtOf Dw u n) + (rankW U (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m))) := by
  intro _ D H Dw l Xo c r U V dict hC hF hpq hg hflat hB w m
  have hU : ∀ σ, GoodEmb c σ → IsUnf (U σ) := fun σ hσ => (hC.2 σ hσ).1
  have hξ : ∀ σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D :=
    fun σ hσ => (hC.2 σ hσ).2.2.2
  obtain ⟨hK, hroot⟩ :=
    GlobalTheory.KeyRootTw.exists_twSec_keyRoot _ H Dw l Xo c r U (xiR D) hU hξ hF hpq hg hB

  set b : ℝ := (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) -
    (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) *
      (Real.log (2 * Real.pi) / 2 + lrd D.host.E) with hb

  have hW : wtOf Dw (parWt Dw w) 0 + m • wtOf Dw 0 1 = wtOf Dw (parWt Dw w) m := by
    rw [GlobalTheory.CompHt.nsmul_wtOf, ← wtOf_add]
    simp
  have hsec : ∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m),
      IntOff (badPrimes H l) t.lo ∧ b ≤ t.degLo := by
    intro Z
    obtain ⟨t₁, h₁I, -, h₁d⟩ :=
      (GlobalTheory.FlatTwisting.twSec_of_flat _ H Dw l Xo c r U (xiR D) (badPrimes H l) hK hU hpq hB).2 hflat Z w
        (GlobalTheory.FlatLine.hasPts U hpq hg hU Z)
    obtain ⟨t₂, h₂I, h₂d⟩ := hroot Z
    have hmp := GlobalTheory.FlatTw.twSec_mul_pow _ H Dw l Xo c r U (xiR D) Z
    obtain ⟨t₃, h₃lo, h₃d⟩ := hmp.2 _ t₂ m
    obtain ⟨t₄, -, -, h₄lo, h₄d⟩ := hmp.1 _ _ t₁ t₃
    obtain ⟨t, htlo, htd⟩ := twSec_congr hW t₄
    refine ⟨t, ?_, ?_⟩
    · rw [htlo, h₄lo, h₃lo]
      exact h₁I.add (intOff_nsmul h₂I m)
    · rw [htd, h₄d, h₃d]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have := mul_le_mul_of_nonneg_left h₂d hm
      rw [hb]
      nlinarith
  choose s hsI hsd using hsec
  have hBp : ∀ p ∈ badPrimes H l, p.Prime := fun p hp => badPrimes_prime p hp
  have hadd : ∀ (u : GlobalTheory.AllWt.Weight Dw) (n : ℤ),
      wtOf Dw u n + wtOf Dw (parWt Dw w) m = wtOf Dw (u + parWt Dw w) (n + m) :=
    fun u n => (wtOf_add u (parWt Dw w) n m).symm
  refine ⟨fun Z => ⟨s Z, hsI Z, hsd Z⟩, fun u n => ⟨fun Z hZ => ?_, fun hW' => ?_⟩⟩
  · obtain ⟨hgood, hrank⟩ := GlobalTheory.FlatTw.Good.twist_goodOn _ H Dw l Xo c r U (xiR D) D V dict Z _ (s Z)
      (wtOf Dw u n) hU (even_wtOf u n) hZ
    have hdeg := GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le _ H Dw l Xo c r U (xiR D) D V dict Z _ (s Z)
      (wtOf Dw u n) (badPrimes H l) hU (even_wtOf u n) hBp (hsI Z) hZ
    rw [hadd] at hgood hrank hdeg
    refine ⟨hgood, hrank, ?_⟩
    have hr : (0 : ℝ) ≤ (rankOn U Z (wtOf Dw u n) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right (hsd Z) (logSum (badPrimes H l))) hr
    linarith
  · obtain ⟨hgood, hrank, hdeg⟩ := GlobalTheory.Proof.TwistedWeightDegree.degW_twist D H Dw l Xo c r U V dict hC _ (wtOf Dw u n) s
      (badPrimes H l) b (even_wtOf u n) hBp hsI hsd hW'
    rw [hadd] at hgood hrank hdeg
    exact ⟨hgood, hrank, hdeg⟩

end GlobalTheory.FlatRootTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineThetaRootTwistTwistingSectionStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection : GlobalTheory.Published.AbelianDeRham → ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → FlatExists U (xiR D) → UnramPts Xo c (badPrimes H l) → ∀ (w : Psi H → ℤ) (m : ℕ), (∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m), IntOff (badPrimes H l) t.lo ∧ (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) ≤ t.degLo) ∧ ∀ (u : Weight Dw) (n : ℤ), (∀ Z : Comp Xo c, GoodOn U (xiR D) V dict Z (wtOf Dw u n) → GoodOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankOn U Z (wtOf Dw (u + parWt Dw w) (n + m)) = rankOn U Z (wtOf Dw u n) ∧ degOn U (xiR D) V dict Z (wtOf Dw u n) + (rankOn U Z (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m))) ∧ (GoodW U (xiR D) V dict (wtOf Dw u n) → GoodW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankW U (wtOf Dw (u + parWt Dw w) (n + m)) = rankW U (wtOf Dw u n) ∧ degW U (xiR D) V dict (wtOf Dw u n) + (rankW U (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m))) := by
  first | exact @GlobalTheory.FlatRootTwist.flat_root_twist | exact GlobalTheory.FlatRootTwist.flat_root_twist | (intros; apply GlobalTheory.FlatRootTwist.flat_root_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsLevelChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelChangePairing

open GlobalTheory.CechPic

section Lift

variable {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B]

theorem lift_mul_lift' (x x' : T ⟶ A) (y y' : T ⟶ B) : lift x y * lift x' y' = lift (x * x') (y * y') := by
  ext1 <;> simp only [MonObj.mul_comp, lift_fst, lift_snd]

theorem lift_pow_eq (x : T ⟶ A) (y : T ⟶ B) (m : ℕ) : lift x y ^ m = lift (x ^ m) (y ^ m) := by
  ext1 <;> simp only [MonObj.pow_comp, lift_fst, lift_snd]

theorem lift_one_one : (1 : T ⟶ A ⊗ B) = lift (1 : T ⟶ A) (1 : T ⟶ B) := by
  ext1 <;> simp only [MonObj.one_comp, lift_fst, lift_snd]

end Lift

theorem isMonHom_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (m : ℕ) :
    IsMonHom ((𝟙 A) ^ m : A ⟶ A) := by
  induction m with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem pc_mul_right {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {P : LB (G2 A).left} (hP : P.IsLB)
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (T : Over S) (x y y' : T ⟶ A) :
    DiagPairing.pc hP x (y * y') = DiagPairing.pc hP x y + DiagPairing.pc hP x y' := by
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have z₁ : ∀ z : T ⟶ A, DiagPairing.pc hP 1 z = 0 := fun z => by
    obtain ⟨t, ht⟩ := h₁
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨t, ht⟩
    rw [cls_pull hP] at e
    have q : lift (1 : T ⟶ A) z = z ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [q, Over.comp_left, pull_comp, e, map_zero]
  have z₂ : ∀ z : T ⟶ A, DiagPairing.pc hP z 1 = 0 := fun z => by
    obtain ⟨t, ht⟩ := h₂
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨t, ht⟩
    rw [cls_pull hP] at e
    have q : lift z (1 : T ⟶ A) = z ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [q, Over.comp_left, pull_comp, e, map_zero]
  have h := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hAA P hP T (lift 1 y) (lift 1 y') (lift x 1)
  have hl := LB.isLB_linComb hP (fun k : Fin 8 ↦ (![lift 1 y * lift 1 y' * lift x 1, lift 1 y * lift 1 y',
    lift 1 y * lift x 1, lift 1 y' * lift x 1, lift 1 y, lift 1 y', lift x 1, 1] k).left) ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (cls_eq_zero_iff hl).2 h
  rw [cls_linComb hP _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  simp only [lift_mul_lift', _root_.mul_one, _root_.one_mul, ← lift_one_one] at e
  have o : (1 : T ⟶ G2 A) = lift (1 : T ⟶ A) 1 := lift_one_one
  rw [o] at e
  have a1 := z₁ (y * y')
  have a2 := z₁ y
  have a3 := z₁ y'
  have a4 := z₂ x
  have a5 := z₁ 1
  unfold DiagPairing.pc at a1 a2 a3 a4 a5 ⊢
  rw [a1, a2, a3, a4, a5] at e
  rw [← sub_eq_zero, ← e]
  abel

theorem weilIs_pow_pos {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hG : Out.GlobalFnsSt)
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L k x y c) {j : ℕ} (hj : 0 < j) :
    Out.WeilIs A L k (x ^ j) y (c ^ j) := by
  induction j with
  | zero => exact absurd hj (lt_irrefl 0)
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · simpa using h
    · rw [pow_succ x j, pow_succ c j]
      exact DiagPairing.weilIs_mul_left hG hA hL (ih hj') h

theorem weilIs_levelChange : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N m : ℕ), 0 < N → 0 < m → ((N * m : ℕ) : κ) ≠ 0 → ∀ (a b : Over.mk y ⟶ A), a ^ (N * m) = 1 → b ^ (N * m) = 1 → ∀ (c : (Γ((Over.mk y).left, ⊤))ˣ), Out.WeilIs (G2 A) P ((N * m : ℕ) : ℤ) (lift a 1) (lift 1 b) c → Out.WeilIs (G2 A) P N (lift (a ^ m) 1) (lift 1 (b ^ m)) (c ^ m) := by
  intro S A _ _ hA P hP h₁ h₂ κ _ _ y N m hN hm hNm a b ha hb c hc
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hB' := pc_mul_right A hA hP h₁ h₂
  haveI := isMonHom_id_pow A m
  let ψ : G2 A ⟶ G2 A := lift (fst A A) (snd A A ≫ (𝟙 A) ^ m)
  have e : ∀ {T : Over S} (u v : T ⟶ A), lift u v ≫ ψ = lift u (v ^ m) := fun u v => by
    simp only [ψ, comp_lift, ← Category.assoc, MonObj.comp_pow, Category.comp_id, lift_fst, lift_snd]
  have hψ' : ψ = lift (fst A A) (snd A A ^ m) := by
    rw [← e (fst A A) (snd A A), lift_fst_snd, Category.id_comp]
  have hL : (lbPow P m).IsLB := LB.isLB_linComb hP _ _
  have hiso : LBIso (lbPow P m) (P.pull ψ.left) := by
    refine (cls_eq_iff hL (pull_isLB hP _)).1 ?_
    rw [cls_lbPow hP, cls_pull hP, hψ']
    have e' := DiagPairing.pc_pow_right hP hB' (fst A A) (snd A A) m
    unfold DiagPairing.pc at e'
    rw [e', lift_fst_snd]
    exact congrArg (m • ·) (pull_id _).symm
  have hNκ : (N : κ) ≠ 0 := by
    rw [Nat.cast_mul] at hNm
    exact left_ne_zero_of_mul hNm
  have hx : (lift (a ^ m) 1 : Over.mk y ⟶ G2 A) ^ N = 1 := by
    rw [lift_pow_eq, ← pow_mul, mul_comm m N, ha, one_pow, lift_one_one]
  have hy : (lift 1 (b ^ m) : Over.mk y ⟶ G2 A) ^ N = 1 := by
    rw [lift_pow_eq, ← pow_mul, mul_comm m N, hb, one_pow, lift_one_one]
  obtain ⟨c₀, h₀⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 A) P hAA hP κ y N hN hNκ _ _ hx hy
  have h₀' : Out.WeilIs (G2 A) P (N : ℤ) (lift (a ^ m) 1 ≫ ψ) (lift 1 b ≫ ψ) c₀ := by
    rw [e, e, one_pow]; exact h₀
  have h₁' : Out.WeilIs (G2 A) P ((N : ℤ) * (m : ℕ)) (lift (a ^ m) 1) (lift 1 b) c₀ :=
    GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hAA hP hP ψ hiso h₀'
  have h₂' : Out.WeilIs (G2 A) P ((N * m : ℕ) : ℤ) (lift (a ^ m) 1) (lift 1 b) (c ^ m) := by
    have := weilIs_pow_pos hG hAA hP hc hm
    rwa [lift_pow_eq, one_pow] at this
  have hc₀ : c₀ = c ^ m :=
    GlobalTheory.CommutatorPairing.weilIs_unique hG hAA hP (by rw [Nat.cast_mul]; exact h₁') h₂'
  rw [← hc₀]
  exact h₀

end GlobalTheory.LevelChangePairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSwapSymmetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSwapSymmetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.DescSymm

open GlobalTheory.CechPic

theorem eSec_swap {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec (A ⊗ A) ≫ (lift (snd A A) (fst A A)).left = eSec (A ⊗ A) := by
  apply GlobalTheory.SquareDescent.square_hom_ext A
  · rw [Category.assoc, ← Over.comp_left, lift_fst, GlobalTheory.SquareDescent.eSec_snd, GlobalTheory.SquareDescent.eSec_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, GlobalTheory.SquareDescent.eSec_fst, GlobalTheory.SquareDescent.eSec_snd]

theorem lbIso_swap : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hπ hA hA₀ gp hsq hP hP₀ iP ⟨r, hr⟩ iS
  have := hπ.fin
  have := hπ.etale
  have := hπ.onto
  have hA₂₀ : IsAbelianScheme (G2 A₀) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA₀ hA₀
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsq
  have hsw : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A₀ A₀) (fst A₀ A₀)).left := by
    apply GlobalTheory.SquareDescent.square_hom_ext A₀
    · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
        lift_fst, hsq.2]
    · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
        lift_snd, hsq.1]
  have h₂ := LB.isLB_pull hP₀ (lift (snd A₀ A₀) (fst A₀ A₀)).left
  have hN := LB.isLB_div h₂ hP₀
  have cN := (CechPic.cls_div h₂ hP₀ hN).trans (by rw [CechPic.cls_pull hP₀ _ h₂])
  have z₀ : CechPic.pull (eSec (G2 A₀)) (CechPic.cls _ hP₀) = 0 :=
    (CechPic.cls_eq_zero_iff (LB.isLB_pull hP₀ _)).2 ⟨r, hr⟩
  have c₁ : CechPic.cls _ hP = CechPic.pull φ₂ (CechPic.cls _ hP₀) :=
    (CechPic.cls_eq_iff hP (LB.isLB_pull hP₀ _)).2 iP
  have c₂ : CechPic.cls _ hP = CechPic.pull (lift (snd A A) (fst A A)).left (CechPic.cls _ hP) :=
    ((CechPic.cls_eq_iff hP (LB.isLB_pull hP _)).2 iS).trans (CechPic.cls_pull hP _ _)
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π (G2 A₀) _ hA₂₀ hN
    inferInstance inferInstance inferInstance ((CechPic.cls_eq_zero_iff (LB.isLB_pull hN _)).1 ?_)
    ((CechPic.cls_eq_zero_iff (LB.isLB_pull hN _)).1 ?_)
  · rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, eSec_swap, z₀, sub_zero]
  · rw [CechPic.cls_pull hN, cN, ← hpb.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp φ₂,
      ← hsw, CechPic.pull_comp, ← c₁, ← c₂, sub_self, map_zero]

end GlobalTheory.DescSymm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSwapSymmetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_birigidified_bundle_swap_symmetric : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
  first | exact @GlobalTheory.DescSymm.lbIso_swap | exact GlobalTheory.DescSymm.lbIso_swap | (intros; apply GlobalTheory.DescSymm.lbIso_swap; all_goals assumption)
end
end
