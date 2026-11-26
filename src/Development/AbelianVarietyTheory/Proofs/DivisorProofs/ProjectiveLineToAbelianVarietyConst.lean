module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedOfHasGoodReduction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineChartFamiliesAgreeOnOverlap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineChartFamiliesAgreeOnOverlap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LineConst

noncomputable section

namespace GlobalTheory.LineConst
open Polynomial

variable {k : Type} [Field k]

private theorem scaleX_isUnit (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    IsUnit ((algebraMap (Polynomial R) (Localization.Away (X : Polynomial R))).comp (scaleHom k R u) X) := by
  simp only [RingHom.comp_apply, scaleHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_mul]
  refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)
  exact ((isUnit_iff_exists_inv.mpr ⟨v, huv⟩).map Polynomial.C).map _

private def psiHom (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    Localization.Away (X : Polynomial k) →+* Localization.Away (X : Polynomial R) :=
  IsLocalization.Away.lift (X : Polynomial k) (scaleX_isUnit R huv)

private theorem psi_loc (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    (algebraMap (Polynomial R) (Localization.Away (X : Polynomial R))).comp (scaleHom k R u) =
      (psiHom R huv).comp (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k))) :=
  RingHom.ext fun a => by simp only [RingHom.comp_apply, psiHom, IsLocalization.Away.lift_eq]

private theorem psi_inv (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
        Localization.Away (X : Polynomial R))).toRingHom.comp (scaleHom k R v) =
      (psiHom R huv).comp (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial k) :
        Localization.Away (X : Polynomial k))).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    have e : (algebraMap k (Localization.Away (X : Polynomial k))) a =
        algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (X : Polynomial k))]
      rfl
    have e2 : (algebraMap R (Localization.Away (X : Polynomial R))) (algebraMap k R a) =
        algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C (algebraMap k R a)) := by
      rw [IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away (X : Polynomial R))]
      rfl
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C, e, psiHom,
      IsLocalization.Away.lift_eq]
    simp [scaleHom, e2]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
    have hb : psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) =
        algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C u) *
          algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) X := by
      simp [psiHom, IsLocalization.Away.lift_eq, scaleHom]
    have hc : psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) *
        psiHom R huv (IsLocalization.Away.invSelf (X : Polynomial k) : Localization.Away (X : Polynomial k)) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have hl : (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
        Localization.Away (X : Polynomial R))) (scaleHom k R v X) *
        psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) = 1 := by
      rw [hb]
      have hv : (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
          Localization.Away (X : Polynomial R))) (scaleHom k R v X) =
          algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C v) *
            IsLocalization.Away.invSelf (X : Polynomial R) := by
        simp [scaleHom, Polynomial.aeval_def, Polynomial.eval₂_mul]
        congr 1
      rw [hv]
      calc _ = algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C (v * u)) *
            (algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) X *
              IsLocalization.Away.invSelf (X : Polynomial R)) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [IsLocalization.Away.mul_invSelf, mul_comm v u, huv, map_one, map_one, _root_.one_mul]
    exact left_inv_eq_right_inv hl hc

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem scaled_loc (B : Over (Sp k)) (f₀ f₁ : Sp (Polynomial k) ⟶ B.left)
    (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)))
    (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)))
    (hyp : spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁)
    (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ (scaled B f₀ h0 R u).left =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ (scaled B f₁ h1 R v).left := by
  change _ ≫ spMap (scaleHom k R u) ≫ f₀ = _ ≫ spMap (scaleHom k R v) ≫ f₁
  rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, psi_loc R huv, psi_inv R huv,
    ← sp_comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) (psiHom R huv),
    Category.assoc, hyp, ← Category.assoc, sp_comp]

private def locOver (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) :=
  Over.mk (spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R))))

private def locIncl (R : Type) [CommRing R] [Algebra k R] : locOver (k := k) R ⟶ lineOver k R :=
  Over.homMk (spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)))) (by
    change spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫
      spMap (algebraMap k (Polynomial R)) = spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R)))
    rw [sp_comp, ← IsScalarTower.algebraMap_eq])

private def locInv (R : Type) [CommRing R] [Algebra k R] : locOver (k := k) R ⟶ lineOver k R :=
  Over.homMk (spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
      Localization.Away (Polynomial.X : Polynomial R))).toRingHom) (by
    change spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
      Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫
      spMap (algebraMap k (Polynomial R)) = spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R)))
    have e : (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom.comp (algebraMap k (Polynomial R)) =
        algebraMap k (Localization.Away (Polynomial.X : Polynomial R)) := by
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.algebraMap_apply,
        Polynomial.aeval_C]
      exact (IsScalarTower.algebraMap_apply k R (Localization.Away (Polynomial.X : Polynomial R)) a).symm
    rw [sp_comp, e])

theorem famMap_loc_eq : ∀ {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f₀ f₁ : Sp (Polynomial k) ⟶ B.left) (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k))) (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k))), spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ (R : Type) [CommRing R] [Algebra k R] (u v : R), u * v = 1 → spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ famMap B f₀ h0 R u = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ famMap B f₁ h1 R v := by
  intro k _ B _ f₀ f₁ h0 h1 hyp R _ _ u v huv
  have hs : ∀ {a b : R}, a * b = 1 → locIncl (k := k) R ≫ scaled B f₀ h0 R a = locInv R ≫ scaled B f₁ h1 R b := by
    intro a b hab
    ext1
    exact scaled_loc B f₀ f₁ h0 h1 hyp R hab
  have h := congrArg CommaMorphism.left
    (show locIncl (k := k) R ≫ (scaled B f₀ h0 R u * (scaled B f₀ h0 R 1)⁻¹) =
        locInv R ≫ (scaled B f₁ h1 R v * (scaled B f₁ h1 R 1)⁻¹) by
      rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_mul, GrpObj.comp_inv, hs huv, hs (_root_.one_mul 1)])
  exact h

end GlobalTheory.LineConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineChartFamiliesAgreeOnOverlapStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LineConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap : ∀ {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f₀ f₁ : Sp (Polynomial k) ⟶ B.left) (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k))) (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k))), spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ (R : Type) [CommRing R] [Algebra k R] (u v : R), u * v = 1 → spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ famMap B f₀ h0 R u = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ famMap B f₁ h1 R v := by
  first | exact @GlobalTheory.LineConst.famMap_loc_eq | exact GlobalTheory.LineConst.famMap_loc_eq | (intros; apply GlobalTheory.LineConst.famMap_loc_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartMapIntoAffineConst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartMapIntoAffineConst
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open Polynomial in
theorem poly_eq_C_of_eq_aeval_invSelf {K : Type} [CommRing K] (p q : K[X])
    (h : algebraMap K[X] (Localization.Away (X : K[X])) p =
      aeval (IsLocalization.Away.invSelf (X : K[X]) : Localization.Away (X : K[X])) q) :
    p = C (p.eval 0) := by
  set L := Localization.Away (X : K[X])
  set n := q.natDegree
  letI : Invertible (algebraMap K[X] L X) :=
    ⟨IsLocalization.Away.invSelf (X : K[X]),
      by rw [mul_comm]; exact IsLocalization.Away.mul_invSelf _, IsLocalization.Away.mul_invSelf _⟩
  have hr : (q.reflect n).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
  have key := eval₂_reflect_mul_pow (algebraMap K L) (algebraMap K[X] L X) n (q.reflect n) hr
  rw [reflect_reflect] at key
  have hev : ∀ r : K[X], eval₂ (algebraMap K L) (algebraMap K[X] L X) r = algebraMap K[X] L r :=
    fun r => eval₂_algebraMap_X r (IsScalarTower.toAlgHom K K[X] L)
  have h2 : algebraMap K[X] L (p * X ^ n) = algebraMap K[X] L (q.reflect n) := by
    rw [map_mul, map_pow, h, aeval_def, ← hev (q.reflect n)]
    exact key
  have hinj : Function.Injective (algebraMap K[X] L) :=
    IsLocalization.injective L (Submonoid.powers_le.2 X_mem_nonzeroDivisors)
  have h3 := hinj h2
  have hdeg : (p * X ^ n).natDegree ≤ n := h3 ▸ hr
  have hp0 : p.natDegree = 0 := by
    by_cases hp : p = 0
    · simp [hp]
    have hc : (p * X ^ n).coeff (p.natDegree + n) ≠ 0 := by
      rw [coeff_mul_X_pow]; exact mt leadingCoeff_eq_zero.mp hp
    have := le_natDegree_of_ne_zero hc
    omega
  rw [← coeff_zero_eq_eval_zero]
  exact eq_C_of_natDegree_eq_zero hp0

end GlobalTheory

namespace GlobalTheory

theorem chart_map_into_affine_const (K : Type) [CommRing K] (Y : Scheme.{0}) (W : Y.Opens)
    (hW : IsAffineOpen W) (g₀ g₁ : Sp (Polynomial K) ⟶ Y) (h₀ : ∀ x, g₀ x ∈ W) (h₁ : ∀ x, g₁ x ∈ W)
    (h : spMap (algebraMap (Polynomial K) (Localization.Away (Polynomial.X : Polynomial K))) ≫ g₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial K) :
        Localization.Away (Polynomial.X : Polynomial K))).toRingHom ≫ g₁) :
    g₀ = spMap (algebraMap K (Polynomial K)) ≫ spMap (Polynomial.evalRingHom 0) ≫ g₀ := by
  haveI := hW.isOpenImmersion_fromSpec
  have r₀ : Set.range g₀.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h₀ x
  have r₁ : Set.range g₁.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h₁ x
  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec g₀ r₀)
  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec g₁ r₁)
  have e₀ : Spec.map φ₀ ≫ hW.fromSpec = g₀ := by rw [hφ₀]; exact IsOpenImmersion.lift_fac _ _ _
  have e₁ : Spec.map φ₁ ≫ hW.fromSpec = g₁ := by rw [hφ₁]; exact IsOpenImmersion.lift_fac _ _ _
  rw [← e₀, ← e₁] at h
  simp only [spMap, ← Category.assoc, ← Spec.map_comp, cancel_mono] at h
  rw [Spec.map_inj] at h
  have key : ∀ a, φ₀ a = Polynomial.C ((φ₀ a).eval 0) := fun a =>
    poly_eq_C_of_eq_aeval_invSelf (φ₀ a) (φ₁ a) (congrArg (fun f => f.hom a) h)
  rw [← e₀]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact key a

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartMapIntoAffineConstStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq : ∀ (K : Type) [CommRing K] (Y : Scheme.{0}) (W : Y.Opens), IsAffineOpen W → ∀ (g₀ g₁ : Sp (Polynomial K) ⟶ Y), (∀ x, g₀ x ∈ W) → (∀ x, g₁ x ∈ W) → spMap (algebraMap (Polynomial K) (Localization.Away (Polynomial.X : Polynomial K))) ≫ g₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial K) : Localization.Away (Polynomial.X : Polynomial K))).toRingHom ≫ g₁ → g₀ = spMap (algebraMap K (Polynomial K)) ≫ spMap (Polynomial.evalRingHom 0) ≫ g₀ := by
  first | exact @GlobalTheory.chart_map_into_affine_const | exact GlobalTheory.chart_map_into_affine_const | (intros; apply GlobalTheory.chart_map_into_affine_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineLineMorphismConstantOfConstOnNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineLineMorphismConstantOfConstOnNonzero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstAffineLine

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem spMap_section {k : Type} [Field k] (φ : Polynomial k →+* k)
    (hφ : φ.comp (algebraMap k (Polynomial k)) = RingHom.id k) :
    spMap φ ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ := by
  rw [spMap_comp', hφ, spMap_id']

theorem eq_of_const_nonzero : ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsSeparated q] [LocallyOfFiniteType q] (f : Sp (Polynomial k) ⟶ Y), f ≫ q = spMap (algebraMap k (Polynomial k)) → (∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f = spMap (Polynomial.evalRingHom 1) ≫ f) → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f = spMap b.toRingHom ≫ f := by
  intro k _ _ Y q _ _ f hq hc a b
  have h1 : (Polynomial.evalRingHom (1 : k)).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
    ext x; simp
  have hs1 := spMap_section _ h1
  set f' := spMap (algebraMap k (Polynomial k)) ≫ spMap (Polynomial.evalRingHom (1 : k)) ≫ f with hf'
  have hlft : LocallyOfFiniteType (f ≫ q) := by
    rw [hq]; exact HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  have key : f = f' := by
    refine ext_of_apply_eq (K := k) q
      ((PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) : Set (PrimeSpectrum (Polynomial k))))
      (PrimeSpectrum.basicOpen _).isOpen.isLocallyClosed ?_ ?_ ?_
    · refine IsOpen.dense (X := PrimeSpectrum (Polynomial k)) (PrimeSpectrum.basicOpen _).isOpen
        ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
      simp [PrimeSpectrum.mem_basicOpen, Polynomial.X_ne_zero]
    · intro x hx hcl
      have hp := pointOfClosedPoint_comp (f ≫ q) x hcl
      have hpx := pointOfClosedPoint_apply (f ≫ q) x hcl (IsLocalRing.closedPoint k)
      generalize pointOfClosedPoint (f ≫ q) x hcl = p at hp hpx
      rw [hq] at hp
      obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = p := ⟨Spec.preimage p, Spec.map_preimage p⟩
      have hφ : φ.hom.comp (algebraMap k (Polynomial k)) = RingHom.id k := by
        have := Spec.map_injective (show Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫ φ)
          = Spec.map (𝟙 _) by rw [Spec.map_comp, Spec.map_id]; exact hp)
        simpa using congrArg CommRingCat.Hom.hom this
      have hev : φ = CommRingCat.ofHom (Polynomial.evalRingHom (φ.hom Polynomial.X)) := by
        apply CommRingCat.hom_ext
        apply Polynomial.ringHom_ext
        · intro a
          rw [Polynomial.algebraMap_eq] at hφ
          simpa using RingHom.congr_fun hφ a
        · simp
      have hc0 : φ.hom Polynomial.X ≠ 0 := by
        intro h0
        rw [← hpx] at hx
        apply (PrimeSpectrum.mem_basicOpen _ _).1 hx
        show φ.hom Polynomial.X ∈ IsLocalRing.maximalIdeal k
        rw [h0]; exact zero_mem _
      have e : Spec.map φ ≫ f = Spec.map φ ≫ f' := by
        rw [hf', reassoc_of% hp, hev]
        exact hc _ hc0
      rw [← hpx]
      exact congrArg (fun g : Sp k ⟶ Y => g (IsLocalRing.closedPoint k)) e
    · rw [hf', Category.assoc, Category.assoc, hq, hs1, Category.comp_id]
  have ha : ∀ a : Polynomial k →ₐ[k] k,
      spMap a.toRingHom ≫ f = spMap (Polynomial.evalRingHom (1 : k)) ≫ f := by
    intro a
    have hsa : spMap a.toRingHom ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ :=
      spMap_section _ (by
        ext x; have := a.commutes x; rw [Polynomial.algebraMap_eq] at this; simpa using this)
    conv_lhs => rw [key]
    rw [hf', reassoc_of% hsa]
  rw [ha a, ha b]

end GlobalTheory.ConstAffineLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineLineMorphismConstantOfConstOnNonzeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineLine_morphism_constant_of_const_on_nonzero : ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsSeparated q] [LocallyOfFiniteType q] (f : Sp (Polynomial k) ⟶ Y), f ≫ q = spMap (algebraMap k (Polynomial k)) → (∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f = spMap (Polynomial.evalRingHom 1) ≫ f) → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f = spMap b.toRingHom ≫ f := by
  first | exact @GlobalTheory.ConstAffineLine.eq_of_const_nonzero | exact GlobalTheory.ConstAffineLine.eq_of_const_nonzero | (intros; apply GlobalTheory.ConstAffineLine.eq_of_const_nonzero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSetOfChartsMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSetOfChartsMem
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjLineOpen
open GlobalTheory.ProjSpace

variable (R : Type) [CommRing R]

def vec (i : Fin 2) : Fin 2 → Polynomial R := fun j => if j = i then 1 else Polynomial.X

theorem span_vec (i : Fin 2) : Ideal.span (Set.range (vec R i)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, by simp [vec]⟩) isUnit_one

def cmap (i : Fin 2) : Sp (Polynomial R) ⟶ PSpace R 1 := pt Polynomial.C (vec R i) (span_vec R i)

def toPoly (i : Fin 2) : MvPolynomial {j : Fin 2 // j ≠ i} R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C fun _ => Polynomial.X

theorem ne_rev (i : Fin 2) : Fin.rev i ≠ i := by fin_cases i <;> decide

instance (i : Fin 2) : Subsingleton {j : Fin 2 // j ≠ i} :=
  ⟨fun a b => Subtype.ext (Fin.ext (by
    have h1 := Fin.val_ne_of_ne a.2; have h2 := Fin.val_ne_of_ne b.2
    have := a.1.2; have := b.1.2; have := i.2; omega))⟩

def fromPoly (i : Fin 2) : Polynomial R →+* MvPolynomial {j : Fin 2 // j ≠ i} R :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X ⟨Fin.rev i, ne_rev i⟩)

def polyEquiv (i : Fin 2) : MvPolynomial {j : Fin 2 // j ≠ i} R ≃+* Polynomial R :=
  RingEquiv.ofRingHom (toPoly R i) (fromPoly R i)
    (Polynomial.ringHom_ext (fun r => by simp [fromPoly, toPoly]) (by simp [fromPoly, toPoly]))
    (MvPolynomial.ringHom_ext (fun r => by simp [fromPoly, toPoly]) (fun t => by
      simp [fromPoly, toPoly]; exact congrArg _ (Subsingleton.elim _ _)))

instance (i : Fin 2) : IsIso (spMap (toPoly R i)) :=
  inferInstanceAs (IsIso (Spec.map (polyEquiv R i).toCommRingCatIso.hom))

theorem toPoly_dehom (i : Fin 2) :
    (toPoly R i).comp (RingHomClass.toRingHom (dehom R 1 i)) =
      MvPolynomial.eval₂Hom Polynomial.C (vec R i) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · simp [toPoly]
  · by_cases h : j = i
    · subst h; simp [vec]
    · have := dehom_X_of_ne R 1 i ⟨j, h⟩
      simp only [RingHom.comp_apply, RingHom.coe_coe] at this ⊢
      rw [this]; simp [toPoly, vec, h]

theorem chartι_eq (i : Fin 2) : spMap (toPoly R i) ≫ chartι R 1 i = cmap R i := by
  have hu : IsUnit (MvPolynomial.eval₂Hom Polynomial.C (vec R i) (MvPolynomial.X i)) := by
    simp [vec]
  rw [cmap, pt, ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem R 1 i) hu, chartι, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine ProjPoint.eq_awayLift _ _ hu (X_mem R 1 i) _ fun n a ha => ?_
  rw [RingHom.comp_apply, awayToPoly_mk R 1 i n a ha]
  have := congrArg (fun φ => φ a) (toPoly_dehom R i)
  simp only [RingHom.comp_apply, RingHom.coe_coe] at this
  rw [this]
  simp [vec]

instance (i : Fin 2) : IsOpenImmersion (cmap R i) := by
  rw [← chartι_eq]; infer_instance

theorem range_cmap (i : Fin 2) : Set.range (cmap R i) = (chart R 1 i : Set (PSpace R 1)) := by
  have e := congrArg (fun U : (PSpace R 1).Opens => (U : Set (PSpace R 1)))
    ((Scheme.Hom.opensRange_comp_of_isIso (spMap (toPoly R i)) (chartι R 1 i)).trans (opensRange_chartι R 1 i))
  simp only [Scheme.Hom.coe_opensRange] at e
  rwa [chartι_eq] at e

theorem cmap_str (i : Fin 2) : cmap R i ≫ PSpace.str R 1 = spMap (algebraMap R (Polynomial R)) := by
  rw [cmap, pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext fun r => by simp [Polynomial.algebraMap_eq]

theorem cmap_preimage (i : Fin 2) : cmap R i ⁻¹ᵁ chart R 1 (Fin.rev i) = spOpen (Polynomial.X : Polynomial R) := by
  rw [cmap, pt_preimage_chart]; simp [vec, ne_rev i]

theorem pt_congr {A : Type} [CommRing A] {c c' : R →+* A} (hc : c = c') {v v' : Fin 2 → A}
    (hv : Ideal.span (Set.range v) = ⊤) (hv' : Ideal.span (Set.range v') = ⊤) (u : Aˣ) (h : v' = u • v) :
    pt c v hv = pt c' v' hv' := by
  subst hc; exact (pt_eq_pt_iff c hv hv').2 ⟨u, h⟩

theorem overlap_eq :
    spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ cmap R 0 =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ cmap R 1 := by
  set L := Localization.Away (Polynomial.X : Polynomial R)
  set s : L := IsLocalization.Away.invSelf (Polynomial.X : Polynomial R)
  have hs : algebraMap (Polynomial R) L Polynomial.X * s = 1 := IsLocalization.Away.mul_invSelf _
  have hmap {B : Type} [CommRing B] (ψ : Polynomial R →+* B) (i : Fin 2) :
      spMap ψ ≫ pt Polynomial.C (vec R i) (span_vec R i) =
        pt (ψ.comp Polynomial.C) (ψ ∘ vec R i) (span_range_comp_eq_top _ (span_vec R i) ψ) := by
    refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun j => by simp)
  rw [cmap, cmap, hmap, hmap]
  refine pt_congr R (RingHom.ext fun r => ?_) _ _ (Units.mkOfMulEqOne s _ (by rw [mul_comm]; exact hs)) ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← Polynomial.algebraMap_eq]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply R (Polynomial R) L r).symm
  · refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp [vec, s, Units.smul_def]
    · have h1 : vec R 1 1 = 1 := by simp [vec]
      have h2 : vec R 0 1 = Polynomial.X := by simp [vec]
      simp only [Units.smul_def, Units.val_mkOfMulEqOne, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
        h1, h2, map_one]
      rw [mul_comm]; exact hs.symm

theorem exists_of_cmap_eq {x x' : Sp (Polynomial R)} (h : cmap R 0 x = cmap R 1 x') :
    ∃ u : Sp (Localization.Away (Polynomial.X : Polynomial R)),
      spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) u = x ∧
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom u = x' := by
  have h1 : cmap R 0 x ∈ (chart R 1 1 : Set (PSpace R 1)) := by
    rw [← range_cmap R 1, h]; exact ⟨x', rfl⟩
  have h2 : x ∈ cmap R 0 ⁻¹ᵁ chart R 1 (Fin.rev 0) := h1
  rw [cmap_preimage] at h2
  have h3 : (x : PrimeSpectrum (Polynomial R)) ∈
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) : Set (PrimeSpectrum (Polynomial R))) := h2
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (Polynomial.X : Polynomial R))] at h3
  obtain ⟨u, hu⟩ := h3
  refine ⟨u, hu, (cmap R 1).isOpenEmbedding.injective ?_⟩
  have e := congrArg (fun φ => φ u) (overlap_eq R)
  exact (e.symm.trans (congrArg (cmap R 0) hu)).trans h

theorem isClosedMap_str : IsClosedMap (PSpace.str R 1) := by
  haveI := isProper_str R 1
  exact (PSpace.str R 1).isClosedMap

theorem str_cmap (i : Fin 2) (x : Sp (Polynomial R)) :
    PSpace.str R 1 (cmap R i x) = spMap (algebraMap R (Polynomial R)) x :=
  congrArg (fun φ => φ x) (cmap_str R i)

end GlobalTheory.ProjLineOpen


open GlobalTheory.ProjLineOpen GlobalTheory.ProjSpace in
theorem GlobalTheory.isOpen_setOf_charts_mem (R : Type) [CommRing R] (Y : Scheme.{0}) (g₀ g₁ : Sp (Polynomial R) ⟶ Y)
    (hg : spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ g₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ g₁)
    (W : Y.Opens) :
    IsOpen {τ : Sp R | ∀ x : Sp (Polynomial R), spMap (algebraMap R (Polynomial R)) x = τ →
      g₀ x ∈ W ∧ g₁ x ∈ W} := by
  set O : Set (PSpace R 1) := cmap R 0 '' (g₀ ⁻¹ᵁ W : Set _) ∪ cmap R 1 '' (g₁ ⁻¹ᵁ W : Set _) with hOdef
  have hO : IsOpen O := ((cmap R 0).isOpenEmbedding.isOpenMap _ (g₀ ⁻¹ᵁ W).isOpen).union
    ((cmap R 1).isOpenEmbedding.isOpenMap _ (g₁ ⁻¹ᵁ W).isOpen)
  have hgu : ∀ u, g₀ (spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) u) =
      g₁ (spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom u) := fun u => congrArg (fun φ => φ u) hg
  have key : {τ : Sp R | ∀ x : Sp (Polynomial R), spMap (algebraMap R (Polynomial R)) x = τ →
      g₀ x ∈ W ∧ g₁ x ∈ W} = (PSpace.str R 1 '' Oᶜ)ᶜ := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro H q hq hτ
      obtain ⟨i, hi⟩ := exists_mem_chart R 1 q
      rw [← SetLike.mem_coe, ← range_cmap R i] at hi
      obtain ⟨x, rfl⟩ := hi
      have hx := (str_cmap R i x).symm.trans hτ
      refine hq ?_
      fin_cases i
      · exact Or.inl ⟨x, (H x hx).1, rfl⟩
      · exact Or.inr ⟨x, (H x hx).2, rfl⟩
    · intro H x hx
      have c0 : cmap R 0 x ∈ O := by
        by_contra hc; exact H _ hc ((str_cmap R 0 x).trans hx)
      have c1 : cmap R 1 x ∈ O := by
        by_contra hc; exact H _ hc ((str_cmap R 1 x).trans hx)
      constructor
      · rcases c0 with ⟨x', hx', e⟩ | ⟨x', hx', e⟩
        · rw [← (cmap R 0).isOpenEmbedding.injective e]; exact hx'
        · obtain ⟨u, rfl, rfl⟩ := exists_of_cmap_eq R e.symm
          show _ ∈ W
          rw [hgu]; exact hx'
      · rcases c1 with ⟨x', hx', e⟩ | ⟨x', hx', e⟩
        · obtain ⟨u, rfl, rfl⟩ := exists_of_cmap_eq R e
          show _ ∈ W
          rw [← hgu]; exact hx'
        · rw [← (cmap R 1).isOpenEmbedding.injective e]; exact hx'
  rw [key]
  exact (isClosedMap_str R _ hO.isClosed_compl).isOpen_compl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSetOfChartsMemStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_setOf_fibre_charts_mem : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (g₀ g₁ : Sp (Polynomial R) ⟶ Y), spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ g₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ g₁ → ∀ (W : Y.Opens), IsOpen {τ : Sp R | ∀ x : Sp (Polynomial R), spMap (algebraMap R (Polynomial R)) x = τ → g₀ x ∈ W ∧ g₁ x ∈ W} := by
  first | exact @GlobalTheory.isOpen_setOf_charts_mem | exact GlobalTheory.isOpen_setOf_charts_mem | (intros; apply GlobalTheory.isOpen_setOf_charts_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PuncturedLineOpenCofinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PuncturedLineOpenCofinite
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem punctured_line_open_cofinite : ∀ (k : Type) [Field k] (V : Set (Sp (Localization.Away (Polynomial.X : Polynomial k)))), IsOpen V → ∀ (χ₁ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k), spMap χ₁.toRingHom (IsLocalRing.closedPoint k) ∈ V → Set.Finite {c : k | c ≠ 0 ∧ ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ Polynomial.X) = c → spMap χ.toRingHom (IsLocalRing.closedPoint k) ∉ V} := by
  intro k _ V hV χ₁ h₁
  classical

  have key : ∀ (χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k)
      (g : Localization.Away (Polynomial.X : Polynomial k)),
      g ∉ PrimeSpectrum.asIdeal (spMap χ.toRingHom (IsLocalRing.closedPoint k)) ↔ χ g ≠ 0 := by
    intro χ g
    rw [Spec.map_base]
    change g ∉ (PrimeSpectrum.comap χ.toRingHom (IsLocalRing.closedPoint k)).asIdeal ↔ _
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hb : (IsLocalRing.closedPoint k).asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    rw [hb, Ideal.mem_bot]
    rfl
  have hV' : IsOpen (V : Set (PrimeSpectrum (Localization.Away (Polynomial.X : Polynomial k)))) := hV
  obtain ⟨_, ⟨g, rfl⟩, hg, hgV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens).exists_subset_of_mem_open h₁ hV'
  have hg₁ : χ₁ g ≠ 0 := (key χ₁ g).1 hg
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (Polynomial.X : Polynomial k) g
  have hXu : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0 := fun χ =>
    ((IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k)).map χ).ne_zero
  have hev : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, ∀ q : Polynomial k,
      χ (algebraMap (Polynomial k) _ q) = q.eval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
    intro χ q
    have : χ.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)))
        = Polynomial.aeval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
      apply Polynomial.algHom_ext
      simp
    have h2 := congrArg (fun φ => φ q) this
    simpa [Polynomial.coe_aeval_eq_eval] using h2
  have hχp : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ p) = χ g * (χ (algebraMap (Polynomial k) _ Polynomial.X)) ^ n := by
    intro χ
    rw [← hp, map_mul, map_pow]
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := hχp χ₁
    rw [map_zero, map_zero] at this
    exact mul_ne_zero hg₁ (pow_ne_zero _ (hXu χ₁)) this.symm
  refine (Polynomial.finite_setOf_isRoot hp0).subset ?_
  rintro c ⟨hc0, hcall⟩
  by_contra hroot
  have hunit : ∀ y : Submonoid.powers (Polynomial.X : Polynomial k),
      IsUnit (Polynomial.aeval c (y : Polynomial k)) := by
    rintro ⟨_, m, rfl⟩
    simp [hc0]
  let χc : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (Polynomial.X : Polynomial k)) hunit
  have hχc : χc (algebraMap (Polynomial k) _ Polynomial.X) = c := by
    simp [χc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  apply hcall χc hχc
  apply hgV
  refine (key χc g).2 ?_
  intro h0
  apply hroot
  have := hχp χc
  rw [h0, zero_mul, hev, hχc] at this
  exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PuncturedLineOpenCofiniteStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_compl_punctured_line_open : ∀ (k : Type) [Field k] (V : Set (Sp (Localization.Away (Polynomial.X : Polynomial k)))), IsOpen V → ∀ (χ₁ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k), spMap χ₁.toRingHom (IsLocalRing.closedPoint k) ∈ V → Set.Finite {c : k | c ≠ 0 ∧ ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ Polynomial.X) = c → spMap χ.toRingHom (IsLocalRing.closedPoint k) ∉ V} := by
  first | exact @GlobalTheory.punctured_line_open_cofinite | exact GlobalTheory.punctured_line_open_cofinite | (intros; apply GlobalTheory.punctured_line_open_cofinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreLineOverSurjection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreLineOverSurjection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open PrimeSpectrum in
theorem prime_line_mem_range_comap_mapRingHom {R K : Type} [CommRing R] [Field K] (χ : R →+* K)
    (hχ : Function.Surjective χ) (P : PrimeSpectrum (Polynomial R))
    (hP : PrimeSpectrum.comap (algebraMap R (Polynomial R)) P = PrimeSpectrum.comap χ (IsLocalRing.closedPoint K)) :
    P ∈ Set.range (PrimeSpectrum.comap (Polynomial.mapRingHom χ)) := by
  have hker : RingHom.ker χ ≤ Ideal.comap Polynomial.C P.asIdeal := by
    intro a ha
    have h1 := congrArg PrimeSpectrum.asIdeal hP
    simp only [PrimeSpectrum.comap_asIdeal] at h1
    have : a ∈ Ideal.comap (algebraMap R (Polynomial R)) P.asIdeal := by
      rw [h1, Ideal.mem_comap, RingHom.mem_ker.mp ha]
      exact Ideal.zero_mem _
    exact this
  rw [range_comap_of_surjective _ _ (Polynomial.map_surjective χ hχ), PrimeSpectrum.mem_zeroLocus,
    Polynomial.ker_mapRingHom, SetLike.coe_subset_coe]
  exact Ideal.map_le_iff_le_comap.mpr hker

theorem fibre_line_over_surjection : ∀ (R K : Type) [CommRing R] [Field K] (χ : R →+* K), Function.Surjective χ → ∀ (x : Sp (Polynomial R)), spMap (algebraMap R (Polynomial R)) x = spMap χ (IsLocalRing.closedPoint K) → x ∈ Set.range (spMap (Polynomial.mapRingHom χ)) := by
  intro R K _ _ χ hχ x hx
  exact prime_line_mem_range_comap_mapRingHom χ hχ x hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreLineOverSurjectionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_spMap_mapRingHom_of_fibre_closedPoint : ∀ (R K : Type) [CommRing R] [Field K] (χ : R →+* K), Function.Surjective χ → ∀ (x : Sp (Polynomial R)), spMap (algebraMap R (Polynomial R)) x = spMap χ (IsLocalRing.closedPoint K) → x ∈ Set.range (spMap (Polynomial.mapRingHom χ)) := by
  first | exact @GlobalTheory.fibre_line_over_surjection | exact GlobalTheory.fibre_line_over_surjection | (intros; apply GlobalTheory.fibre_line_over_surjection <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineToAbelianVarietyConst
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineConst
open Polynomial

theorem projLine_map_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (f₀ f₁ : Sp (Polynomial k) ⟶ B.left), f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f₀ = spMap b.toRingHom ≫ f₀ := by
  intro k _ _ B _ hB f₀ f₁ h0 h1 h01 a b
  have := hB.proper
  haveI hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let pt : Sp k := IsLocalRing.closedPoint k
  let e : B.left := (η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left pt
  obtain ⟨_, ⟨W, hW, rfl⟩, heW, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ e) isOpen_univ
  let L := Localization.Away (X : Polynomial k)
  let t : L := algebraMap (Polynomial k) L X
  let ti : L := IsLocalization.Away.invSelf (X : Polynomial k)
  have hti : t * ti = 1 := IsLocalization.Away.mul_invSelf (X : Polynomial k)
  let g₀ := famMap B f₀ h0 L t
  let g₁ := famMap B f₁ h1 L ti
  have hc := GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap B f₀ f₁ h0 h1 h01 L t ti hti
  let V : Set (Sp L) := {τ | ∀ x : Sp (Polynomial L), spMap (algebraMap L (Polynomial L)) x = τ → g₀ x ∈ W ∧ g₁ x ∈ W}
  have hV : IsOpen V := GlobalTheory.T.isOpen_setOf_fibre_charts_mem L _ g₀ g₁ hc W

  have hfib : ∀ (χ : L →ₐ[k] k) (x' : Sp (Polynomial k)),
      spMap (algebraMap L (Polynomial L)) (spMap (Polynomial.mapRingHom (χ : L →+* k)) x') = spMap χ.toRingHom pt := by
    intro χ x'
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.mapRingHom (χ : L →+* k)).comp (algebraMap L (Polynomial L)) =
        (algebraMap k (Polynomial k)).comp (χ : L →+* k) := by
      ext z; simp [Polynomial.algebraMap_apply]
    rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Scheme.Hom.comp_apply]
    congr 1
    exact hsub.elim _ _
  have hW₀ : ∀ χ : L →ₐ[k] k, spMap χ.toRingHom pt ∈ V →
      (∀ x', famMap B f₀ h0 k (χ t) x' ∈ W) ∧ (∀ x', famMap B f₁ h1 k (χ ti) x' ∈ W) := by
    intro χ hχ
    constructor
    · intro x'
      rw [← famMap_base B f₀ h0 χ t, Scheme.Hom.comp_apply]
      exact (hχ _ (hfib χ x')).1
    · intro x'
      rw [← famMap_base B f₁ h1 χ ti, Scheme.Hom.comp_apply]
      exact (hχ _ (hfib χ x')).2
  have hinW : ∀ R : Type, ∀ _ : CommRing R, ∀ _ : Algebra k R, ∀ (f : Sp (Polynomial k) ⟶ B.left)
      (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (x : Sp (Polynomial R)), famMap B f hf R 1 x ∈ W := by
    intro R _ _ f hf x
    rw [famMap_one, Scheme.Hom.comp_apply]
    have hx : (spMap (algebraMap k (Polynomial R))) x = pt := hsub.elim _ _
    rw [hx]
    exact heW

  let χ₁ : L →ₐ[k] k := IsLocalization.liftAlgHom (M := Submonoid.powers (X : Polynomial k))
    (f := Polynomial.aeval (1 : k)) (by
      rintro ⟨_, n, rfl⟩
      simp)
  have hχ₁t : χ₁ t = 1 := by simp [χ₁, t]
  have hχ₁ti : χ₁ ti = 1 := by
    have := congrArg χ₁ hti
    rw [map_mul, hχ₁t, _root_.one_mul, map_one] at this
    exact this
  have h1V : spMap χ₁.toRingHom pt ∈ V := by
    intro x hx
    obtain ⟨x', rfl⟩ := GlobalTheory.T.mem_range_spMap_mapRingHom_of_fibre_closedPoint L k χ₁.toRingHom
      (fun z => ⟨algebraMap k L z, by simp⟩) x hx
    constructor
    · have := famMap_base B f₀ h0 χ₁ t
      rw [hχ₁t] at this
      rw [← Scheme.Hom.comp_apply]
      erw [this]
      exact hinW k _ _ f₀ h0 x'
    · have := famMap_base B f₁ h1 χ₁ ti
      rw [hχ₁ti] at this
      rw [← Scheme.Hom.comp_apply]
      erw [this]
      exact hinW k _ _ f₁ h1 x'
  have hF := GlobalTheory.T.finite_compl_punctured_line_open k V hV χ₁ h1V
  set F := {c : k | c ≠ 0 ∧ ∀ χ : L →ₐ[k] k, χ (algebraMap (Polynomial k) _ X) = c → spMap χ.toRingHom pt ∉ V}

  have hscale : ∀ c : k, c ≠ 0 → c ∉ F → ∀ a : k,
      spMap (Polynomial.evalRingHom (c * a)) ≫ f₀ = spMap (Polynomial.evalRingHom a) ≫ f₀ := by
    intro c hc0 hcF
    simp only [F, Set.mem_setOf_eq, not_and, not_forall, not_not] at hcF
    obtain ⟨χ, hχt, hχV⟩ := hcF hc0
    obtain ⟨hA, hB'⟩ := hW₀ χ hχV
    have hu : χ t * χ ti = 1 := by rw [← map_mul, hti, map_one]
    have hcmp := GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap B f₀ f₁ h0 h1 h01 k (χ t) (χ ti) hu
    have key := GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq k B.left W hW _ _ hA hB' hcmp
    have := scale_inv_of_famMap B f₀ h0 (χ t) key
    simpa [t, hχt] using this
  have hunit : ∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f₀ = spMap (Polynomial.evalRingHom 1) ≫ f₀ := by
    intro c hc
    have hfin : ((F ∪ {0}) ∪ (fun d => c / d) '' F).Finite :=
      (hF.union (Set.finite_singleton 0)).union (hF.image _)
    obtain ⟨d, hd⟩ := hfin.infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_image, not_or, not_exists,
      not_and] at hd
    obtain ⟨⟨hdF, hd0⟩, hd'⟩ := hd
    have hcd0 : c / d ≠ 0 := div_ne_zero hc hd0
    have hcdF : c / d ∉ F := fun h => hd' (c / d) h (by field_simp)
    have e1 := hscale d hd0 hdF (c / d * 1)
    have e2 := hscale (c / d) hcd0 hcdF 1
    rw [_root_.mul_one] at e1 e2
    rw [show d * (c / d) = c by field_simp] at e1
    rw [e1, e2]
  exact GlobalTheory.T.affineLine_morphism_constant_of_const_on_nonzero k B.left B.hom f₀ h0 hunit a b

end GlobalTheory.LineConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineToAbelianVarietyConstStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveLine_to_abelianVariety_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (f₀ f₁ : Sp (Polynomial k) ⟶ B.left), f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f₀ = spMap b.toRingHom ≫ f₀ := by
  first | exact @GlobalTheory.LineConst.projLine_map_const | exact GlobalTheory.LineConst.projLine_map_const | (intros; apply GlobalTheory.LineConst.projLine_map_const <;> assumption)
end
