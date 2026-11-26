module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndoEqOfSections
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.AutUniq

theorem hom_eq_of_sval {X X' Y B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (X ⟶ Y)} {ε : K → ℤ}
    {M : ℕ} (s : Fin (M + 1) → LB.Sec (LB.LinComb L φ ε)) (f : X ⟶ B) (p q : X' ⟶ X) (hf : p ≫ f = q ≫ f)
    (hcov : ⨆ i, nonzeroLocus (s i) = ⊤) (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (M + 1) → Γ(X, nonzeroLocus (s i))) (hr : ∀ i j, AmpleSpan.IsRatio (s j) (s i) (r i j))
    (hsurj : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom (r i)))
    (h : ∀ z : X', ∃ J, Good L z J ∧ ∃ u : (X'.presheaf.stalk z)ˣ, ∀ j, sval (s j) q z J = u.val * sval (s j) p z J) :
    p = q := by
  have mem : ∀ (χ : X' ⟶ X) i z J, Good L z J → (χ z ∈ nonzeroLocus (s i) ↔ IsUnit (sval (s i) χ z J)) :=
    fun χ i z J hJ => AmpleSpan.mem_nonzeroLocus_iff_gs (s i) χ z (hJ.mem φ χ)
  have rat : ∀ (χ : X' ⟶ X) i j z J, Good L z J → χ z ∈ nonzeroLocus (s i) →
      sval (s j) χ z J = gs χ z _ (r i j) * sval (s i) χ z J :=
    fun χ i j z J hJ hz => (hr i j).gs χ z hz (hJ.mem φ χ)
  have hm : ∀ i z, p z ∈ nonzeroLocus (s i) → q z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨J, hJ, u, hu⟩ := h z
    rw [mem q i z J hJ, hu]
    exact u.isUnit.mul ((mem p i z J hJ).1 hz)
  refine MapUniq.hom_ext_of_gs (fun i => nonzeroLocus (s i)) haff hcov p q hm fun i z hz a => ?_
  have hz' := hm i z hz
  obtain ⟨J, hJ, u, hu⟩ := h z
  have hrr : ∀ j, gs p z _ (r i j) = gs q z _ (r i j) := fun j => by
    have e := rat q i j z J hJ hz'
    rw [hu, hu, rat p i j z J hJ hz, mul_left_comm] at e
    have e' := (Units.mul_right_inj _).1 ((mul_left_comm _ _ _).trans e |>.trans (mul_left_comm _ _ _))
    exact ((mem p i z J hJ).1 hz).mul_right_cancel e'
  have cst : ∀ (χ : X' ⟶ X), χ z ∈ nonzeroLocus (s i) → ∀ c : Γ(B, ⊤),
      gs χ z _ ((f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom c) = gs (χ ≫ f) z ⊤ c := fun χ hχ c =>
    (gs_res χ z le_top hχ _).trans (gs_pull χ f z ⊤ trivial _)
  obtain ⟨P, rfl⟩ := hsurj i a
  induction P using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, cst p hz, cst q hz', hf]
  | add P Q hP hQ => rw [map_add (f := _), gs_add p z _ hz, gs_add q z _ hz', hP, hQ]
  | mul_X P j hP => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul p z _ hz, gs_mul q z _ hz', hP, hrr]

theorem eq_of_twistPull {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hS : IsAffineOpen (⊤ : S.Opens)) {n : ℕ} (hV : VeryAmpleAt A L n) {T : Over S} (ψ ψ' : T ⊗ A ⟶ T ⊗ A)
    (h₁ : ψ ≫ fst _ _ = fst _ _) (h₂ : ψ' ≫ fst _ _ = fst _ _)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![(n : ℤ), -(n : ℤ)]))
    (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ' ≫ snd _ _).left] ![(n : ℤ), -(n : ℤ)]))
    (hα : α.IsGen) (hα' : α'.IsGen) (c : Γ(T.left, ⊤)ˣ)
    (H : ∀ t t₁ t₂ : LB.Sec (LPow A L n T), IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t t₁ →
      IsTwistPull A L ψ' (ψ' ≫ snd _ _) rfl n n α' t t₂ → ∀ j, t₂.f j = liftFun A _ c.val * t₁.f j) : ψ = ψ' := by
  obtain ⟨M, s, hcov, haff⟩ := hV ⊤ hS
  choose r hr hsurj using fun i => (haff i).2
  obtain ⟨i', hi⟩ : ∃ i' : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id⟩
  have sec : ∀ j, ∃ v : LB.Sec (LPow A L n T), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → VVRank.sv A v r z J =
        sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
          (r ≫ (snd T A).left ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ := fun _ : Fin n => (snd T A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => (n : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd T A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (VVRank.sval_pullTo _ _ _ r z hJ)⟩
  choose v hv using sec
  have key : ψ.left ≫ (snd T A).left ≫ i' = ψ'.left ≫ (snd T A).left ≫ i' := by
    refine hom_eq_of_sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s (A.hom ∣_ ⊤) _ _ ?_
      hcov (fun i => (haff i).1) r hr hsurj fun y => ?_
    · rw [← cancel_mono (⊤ : S.Opens).ι]
      simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hi, Over.w]
    · choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
      refine ⟨J, hJ, (val α' (𝟙 _) y J)⁻¹ * gm (𝟙 _ ≫ (fst T A).left) y ⊤ c * val α (𝟙 _) y J, fun j => ?_⟩
      obtain ⟨t₁, ht₁⟩ := VVRank.exists_isTwistPull A (hm := rfl) hL hα (v j)
      obtain ⟨t₂, ht₂⟩ := VVRank.exists_isTwistPull A (hm := rfl) hL hα' (v j)
      have e₁ := VVRank.sv_of_isTwistPull A ht₁ (𝟙 _) y hJ
      have e₂ := VVRank.sv_of_isTwistPull A ht₂ (𝟙 _) y hJ
      have hy := Good.mem hJ (fun _ : Fin 1 => (snd T A).left) (𝟙 (T ⊗ A).left)
      have e₃ : VVRank.sv A t₂ (𝟙 _) y J =
          (gm (𝟙 _ ≫ (fst T A).left) y ⊤ c).val * VVRank.sv A t₁ (𝟙 _) y J :=
        (congrArg (gs (𝟙 _) y _) (H _ _ _ ht₁ ht₂ _)).trans ((gs_mul _ y _ hy _ _).trans
          (congrArg (· * _) ((gs_res _ y le_top hy _).trans ((gs_pull _ _ y ⊤ trivial _).trans
            (gs_unit _ y ⊤ trivial c)))))
      rw [hv _ _ _ _ _ hJ, Category.id_comp] at e₁ e₂
      rw [Units.val_mul, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← e₁, ← e₃, e₂, Units.inv_mul_cancel_left]
  refine CartesianMonoidalCategory.hom_ext _ _ (h₁.trans h₂.symm) (Over.OverMorphism.ext ?_)
  have := congrArg (fun q => q ≫ (A.hom ⁻¹ᵁ ⊤).ι) key
  simpa only [Category.assoc, hi, Category.comp_id, Over.comp_left] using this

theorem endo_eq_of_sections : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ), 4 ≤ N → ∀ (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), ψ ≫ fst _ _ = fst _ _ → ψ' ≫ fst _ _ = fst _ _ → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (ψ ≫ snd _ _).left] ![(N : ℤ), -(N : ℤ)])) (α' : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (ψ' ≫ snd _ _).left] ![(N : ℤ), -(N : ℤ)])), α.IsGen → α'.IsGen → ∀ c : Γ((TFK (R := R) F).left, ⊤)ˣ, (∀ t t₁ t₂ : SecA A F N, IsTwistPull A.A A.L ψ (ψ ≫ snd _ _) rfl N N α t t₁ → IsTwistPull A.A A.L ψ' (ψ' ≫ snd _ _) rfl N N α' t t₂ → ∀ j, t₂.f j = liftFun A.A _ c.val * t₁.f j) → ψ = ψ' := by
  intro hL R _ _ A F _ _ N hN ψ ψ' h₁ h₂ α α' hα hα' c H
  exact eq_of_twistPull A.isLB (isAffineOpen_top _) (hL.1.ample _ A N hN).2 ψ ψ' h₁ h₂ α α' hα hα' c H

end GlobalTheory.AutUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StabFlat

theorem localization_of_isStandardSmooth_ideal {V R A : Type} [CommRing V] [IsNoetherianRing V] [CommRing R]
    [CommRing A] (m : Ideal V) [m.IsMaximal] {g : ℕ} {ρ : V →+* R}
    (hρ : ρ.IsStandardSmoothOfRelativeDimension g) (n : Ideal R) [n.IsMaximal] [Algebra R A]
    [IsLocalization.AtPrime A n] (hn : m.map ρ ≤ n) :
    IsNoetherianRing A ∧ ((algebraMap R A).comp ρ).Flat ∧
      IsRegularLocalRing (A ⧸ m.map ((algebraMap R A).comp ρ)) ∧
      ringKrullDim (A ⧸ m.map ((algebraMap R A).comp ρ)) = g := by
  have hq : (Ideal.quotientMap (m.map ρ) ρ Ideal.le_comap_map).IsStandardSmoothOfRelativeDimension g := by
    have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange.{0} g)
    exact MorphismProperty.of_isPushout
      (P := RingHom.toMorphismProperty (@RingHom.IsStandardSmoothOfRelativeDimension g))
      (NilpotentLift.isPushout_quotient_map m (CommRingCat.ofHom ρ)).flip hρ
  letI := ρ.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension g V R := hρ
  have : Algebra.IsStandardSmooth V R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing V R
  refine ⟨IsLocalization.isNoetherianRing n.primeCompl A inferInstance, ?_, ?_⟩
  · have h₁ : ρ.Flat := (inferInstance : Module.Flat V R)
    have h₂ : (algebraMap R A).Flat :=
      RingHom.flat_algebraMap_iff.2 (IsLocalization.flat A n.primeCompl)
    exact h₁.comp h₂
  letI := Ideal.Quotient.field m
  rw [← Ideal.map_map]
  set J := m.map ρ with hJ
  obtain ⟨φ, -, hφ⟩ := hq.exists_etale_mvPolynomial
  have hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n := by
    rwa [Ideal.mk_ker]
  letI := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin g) (V ⧸ m)) (R ⧸ J) := hφ.toAlgebra
  have : IsRegularRing (R ⧸ J) := isRegularRing_of_etale (MvPolynomial (Fin g) (V ⧸ m)) _
  have hm : (n.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hJn
  have hle : J ≤ (J.map (algebraMap R A)).comap (algebraMap R A) := Ideal.le_comap_map
  letI : Algebra (R ⧸ J) (A ⧸ J.map (algebraMap R A)) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ J.map (algebraMap R A))
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x', hx', e⟩ hx
      exact hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))
    · exact fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  refine ⟨?_, (IsLocalization.AtPrime.ringKrullDim_eq_height (n.map (Ideal.Quotient.mk J)) _).trans
    (height_of_etale_mvPolynomial (V ⧸ m) (R ⧸ J) g _)⟩
  have := IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv

theorem stalk_of_smooth_local : ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ x : X, IsClosed ({x} : Set X) → ∀ σ : V →+* X.presheaf.stalk x, X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → IsNoetherianRing (X.presheaf.stalk x) ∧ σ.Flat ∧ IsRegularLocalRing (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal V).map σ) ∧ ringKrullDim (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal V).map σ) = g := by
  intro V _ _ _ X f g hg x hx σ hσ hn
  obtain ⟨U, hU, W, hW, hxW, e, H⟩ := hg.exists_isStandardSmoothOfRelativeDimension x
  have hfx : f x = IsLocalRing.closedPoint V :=
    ((congrArg f Scheme.fromSpecStalk_closedPoint.symm).trans
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) hσ)).trans (IsLocalRing.comap_closedPoint σ)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 (hfx ▸ e hxW)
  let ρ := (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ f.appLE ⊤ W e
  have hρ : ρ.hom.IsStandardSmoothOfRelativeDimension g :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).2 H
  have hc : ρ ≫ X.presheaf.germ W x hxW = CommRingCat.ofHom σ := by
    apply Spec.map_injective
    rw [← hσ, ← hW.fromSpecStalk_eq_fromSpecStalk hxW, Spec.map_comp, Spec.map_comp, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hW e, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  have hl : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  haveI := hW.primeIdealOf_isMaximal_of_isClosed ⟨x, hxW⟩ hx
  have hs : (algebraMap Γ(X, W) (X.presheaf.stalk x)).comp ρ.hom = σ := congrArg (fun q => q.hom) hc
  have key := localization_of_isStandardSmooth_ideal (A := X.presheaf.stalk x) (IsLocalRing.maximalIdeal V) hρ
    (hW.primeIdealOf ⟨x, hxW⟩).asIdeal (by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      by_contra hm
      have hu := IsLocalization.map_units (X.presheaf.stalk x)
        (⟨_, hm⟩ : (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl)
      have hu' : IsUnit (σ a) := hs ▸ hu
      exact ha (hn.map_nonunit a hu'))
  rw [hs] at key
  exact key

end GlobalTheory.StabFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocalStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_regular_flat_of_smooth : ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ x : X, IsClosed ({x} : Set X) → ∀ σ : V →+* X.presheaf.stalk x, X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → IsNoetherianRing (X.presheaf.stalk x) ∧ σ.Flat ∧ IsRegularLocalRing (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal V).map σ) ∧ ringKrullDim (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal V).map σ) = g := by
  first | exact @GlobalTheory.StabFlat.stalk_of_smooth_local | exact GlobalTheory.StabFlat.stalk_of_smooth_local | (intros; apply GlobalTheory.StabFlat.stalk_of_smooth_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalWeilPairingEqAbelianPartImage
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalWeilPairingEqAbelianPartImage
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.ImagePairing

theorem eq_map_of_isCPMap {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {N : ℕ} {T' : Over S'} {T : Over S} (r : T'.left ⟶ T.left)
    (hr : r ≫ T.hom = T'.hom ≫ f) {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : x'.left ≫ F = r ≫ x.left)
    (hy : y'.left ≫ F = r ≫ y.left) {ζ' ζ} (h' : CubWeil P'.c N x' y' ζ') (h₀ : CubWeil P.c N x y ζ) :
    ζ' = Units.map r.appTop.hom.toMonoidHom ζ := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk r hr
  have a := cubWeil_map S S' f G G' P P' F hw w h N T' x' y' ζ' h'
  have ex : toBase hw x' = ρ ≫ x := Over.OverMorphism.ext hx
  have ey : toBase hw y' = ρ ≫ y := Over.OverMorphism.ext hy
  rw [ex, ey] at a
  exact a.unique (h₀.comp ρ)

theorem pow_eq_one_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {N : ℕ} {T' : Over S'}
    {T : Over S} (r : T'.left ⟶ T.left) (hr : r ≫ T.hom = T'.hom ≫ f) {x' : T' ⟶ (Over.pullback f).obj G}
    {x : T ⟶ G} (hx : x'.left ≫ pullback.fst G.hom f = r ≫ x.left) (h : x ^ N = 1) : x' ^ N = 1 := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk r hr
  let β : (T' ⟶ (Over.pullback f).obj G) →* (Over.mk (T'.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition)
      (toBase_mul_pullback G f T')
  have ex : β x' = ρ ≫ x := Over.OverMorphism.ext hx
  have e : β (x' ^ N) = β 1 := by rw [map_pow, map_one, ex, ← MonObj.comp_pow, h, MonObj.comp_one]
  refine Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e) ?_)
  exact (Over.w (x' ^ N)).trans (Over.w (1 : T' ⟶ (Over.pullback f).obj G)).symm

theorem fn_eq_of_thick {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (a b : Γ(Spec (CommRingCat.of R), ⊤))
    (h : ∀ e, (thick R I e).appTop.hom a = (thick R I e).appTop.hom b) : a = b := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have key : ∀ (e : ℕ) (c : Γ(Spec (CommRingCat.of R), ⊤)),
      Ideal.Quotient.mk (I ^ (e + 1)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) =
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom ((thick R I e).appTop.hom c) := fun e c =>
    (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))).symm
  have := IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)
    (fun n _ => (key n a).trans ((congrArg _ (h n)).trans (key n b).symm))
  exact congrFun this ()

theorem exists_thick_hom {V W : Type} [CommRing V] [CommRing W] [Algebra V W] (I : Ideal V) (e : ℕ) :
    ∃ φ : Spec (CommRingCat.of (W ⧸ (I.map (algebraMap V W)) ^ (e + 1))) ⟶ Spec (CommRingCat.of (V ⧸ I ^ (e + 1))),
      thick W (I.map (algebraMap V W)) e ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) = φ ≫ thick V I e := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap V W) ?_)), ?_⟩
  · rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  · simp only [thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

theorem cubWeil_image : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ (N : ℕ) (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B) (ζ), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → b ^ N = 1 → b' ^ N = 1 → CubWeil s.P.c N x x' ζ → CubWeil a.M.c N b b' ζ := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ N x x' b b' ζ hx hx' hb hb' h
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil a.M.c hb hb'
  suffices e : ζ = ξ from e ▸ hξ
  refine Units.ext (fn_eq_of_thick ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) _ _ fun e => ?_)
  obtain ⟨φ, hφ⟩ := exists_thick_hom (W := W) (IsLocalRing.maximalIdeal V) e
  let r := thick W ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) e
  have lifts : ∀ y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G,
      ∃ ye : Over.mk φ ⟶ thickObj V (IsLocalRing.maximalIdeal V) e G,
        ye.left ≫ pullback.fst G.hom (thick V _ e) = r ≫ y.left := fun y =>
    ⟨Over.homMk (pullback.lift (r ≫ y.left) φ ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (Over.w y)).trans hφ)))
      (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  obtain ⟨y, hy⟩ := lifts x
  obtain ⟨y', hy'⟩ := lifts x'
  obtain ⟨θ, hθ, -⟩ := existsUnique_cubWeil (t.l e).Pe.c
    (pow_eq_one_of_pullback (T' := Over.mk φ) (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))))
      _ r hφ hy h.1)
    (pow_eq_one_of_pullback (T' := Over.mk φ) (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))))
      _ r hφ hy' h.2.1)
  obtain ⟨w, hw⟩ := (t.l e).lev
  obtain ⟨hp, v, hv⟩ := a.b_pb e
  have e₁ := eq_map_of_isCPMap hw (T' := Over.mk φ)
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) r hφ hy hy' hθ h
  obtain ⟨u, -, hu⟩ := hv.exists_comp (t.l e).D.map (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w, Category.id_comp])
  have e₂ := eq_map_of_isCPMap hu (T' := Over.mk φ)
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) r
    (hφ.trans (congrArg (φ ≫ ·) (Category.id_comp _).symm)) (hx e _ r y.left hy) (hx' e _ r y'.left hy') hθ hξ
  exact congrArg Units.val (e₁.symm.trans e₂)

end GlobalTheory.UU.ImagePairing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalWeilPairingEqAbelianPartImageStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.cubicalWeilPairing_eq_abelianPart_image : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ (N : ℕ) (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B) (ζ), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → b ^ N = 1 → b' ^ N = 1 → CubWeil s.P.c N x x' ζ → CubWeil a.M.c N b b' ζ := by
  first | exact @GlobalTheory.UU.ImagePairing.cubWeil_image | exact GlobalTheory.UU.ImagePairing.cubWeil_image | (intros; apply GlobalTheory.UU.ImagePairing.cubWeil_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfPowEqOneOfLocalHom
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem eq_one_of_pow_eq_one_of_localHom {W Ω : Type} [CommRing W] [IsLocalRing W] [Field Ω] (f : W →+* Ω)
    [IsLocalHom f] {N : ℕ} (hN : IsUnit (N : W)) {ζ : W} (h : ζ ^ N = 1) (hf : f ζ = 1) : ζ = 1 := by
  have hu : IsUnit (∑ i ∈ Finset.range N, ζ ^ i) := by
    refine isUnit_of_map_unit f _ ?_
    have := hN.map f
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, hf] using this
  have := geom_sum_mul ζ N
  rw [h, sub_self] at this
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 this)

theorem unit_eq_one_of_localHom {W Ω : Type} [CommRing W] [IsLocalRing W] [Field Ω] (f : W →+* Ω)
    [IsLocalHom f] {N : ℕ} (hN : IsUnit (N : W)) {ζ : Γ(Spec (CommRingCat.of W), ⊤)ˣ} (h : ζ ^ N = 1)
    (hf : Units.map (Spec.map (CommRingCat.ofHom f)).appTop.hom.toMonoidHom ζ = 1) : ζ = 1 := by
  have nat := congrArg (fun q => q.hom ζ.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  have hf' : (Spec.map (CommRingCat.ofHom f)).appTop.hom ζ.val = 1 := congrArg Units.val hf
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, hf', map_one, CommRingCat.hom_ofHom] at nat
  have h1 := eq_one_of_pow_eq_one_of_localHom f hN
    (ζ := (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom ζ.val)
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]) nat.symm
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact h1

theorem IsCPMap.cubWeil_iff {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {N : ℕ} {T : Over S'} {x y : T ⟶ G'} (hx : x ^ N = 1) (hy : y ^ N = 1)
    (ζ : Γ(T.left, ⊤)ˣ) : CubWeil P'.c N x y ζ ↔ CubWeil P.c N (toBase hw x) (toBase hw y) ζ := by
  refine ⟨cubWeil_map _ _ _ _ _ _ _ _ _ _ h N T x y ζ, fun h' => ?_⟩
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil P'.c hx hy
  have := (cubWeil_map _ _ _ _ _ _ _ _ _ _ h N T x y ξ hξ).unique h'
  exact this ▸ hξ

theorem TQ.Desc.cubWeil_one_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
    {Q : TQ G X} {P : CP G} (D : Q.Desc P) {N : ℕ} {T : Over S} {x y : T ⟶ G} (hx : x ^ N = 1) (hy : y ^ N = 1) :
    CubWeil P.c N x y 1 ↔ CubWeil D.M.c N (x ≫ Q.q) (y ≫ Q.q) 1 := by
  rw [D.map.cubWeil_iff hx hy]
  let ρ : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 T.left) (by simp)
  let ρ' : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have hw : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S := by simp
  have e : ∀ a : T ⟶ G, ρ ≫ toBase hw a = a ≫ Q.q := fun a =>
    Over.OverMorphism.ext (Category.id_comp (a.left ≫ Q.q.left))
  have e' : ∀ a : T ⟶ G, ρ' ≫ (a ≫ Q.q) = toBase hw a := fun a =>
    Over.OverMorphism.ext (Category.id_comp (a.left ≫ Q.q.left))
  constructor
  · intro h
    have := h.comp ρ
    rwa [e, e, map_one] at this
  · intro h
    have := h.comp ρ'
    rwa [e', e', map_one] at this

theorem cubWeil_one_iff_closedFibre : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (W Ω : Type) [CommRing W] [IsLocalRing W] [Algebra V W] [Field Ω] (f' : W →+* Ω), IsLocalHom f' → ∀ (p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1)))) (N : ℕ), IsUnit (N : V) → ∀ (y y' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (x x' : Over.mk p ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G), y ^ N = 1 → y' ^ N = 1 → x.left ≫ (fstG _ 0 G).left = (Spec.map (CommRingCat.ofHom f')) ≫ y.left → x'.left ≫ (fstG _ 0 G).left = (Spec.map (CommRingCat.ofHom f')) ≫ y'.left → (CubWeil s.P.c N y y' 1 ↔ CubWeil (t.l 0).D.M.c N (x ≫ (t.l 0).Q.q) (x' ≫ (t.l 0).Q.q) 1) := by
  intro V _ _ _ A G _ _ s t W Ω _ _ _ _ f' hf' p N hN y y' x x' hy hy' hx hx'
  let I := IsLocalRing.maximalIdeal V
  have hw : pullback.fst G.hom (thick V I 0) ≫ G.hom = (thickObj V I 0 G).hom ≫ thick V I 0 := pullback.condition
  obtain ⟨w, hl⟩ := (t.l 0).lev
  have hρ : Spec.map (CommRingCat.ofHom f') ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) =
      (Over.mk p).hom ≫ thick V I 0 := by
    have a := Over.w (toBase hw x)
    have b := Over.w y
    exact (congrArg (Spec.map (CommRingCat.ofHom f') ≫ ·) b).symm.trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) hx).symm.trans a))
  let ρ : Over.mk ((Over.mk p).hom ≫ thick V I 0) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom f')) hρ
  have e : ρ ≫ y = toBase hw x := Over.OverMorphism.ext hx.symm
  have e' : ρ ≫ y' = toBase hw x' := Over.OverMorphism.ext hx'.symm
  have inj : ∀ a b : Over.mk p ⟶ thickObj V I 0 G, toBase hw a = toBase hw b → a = b := fun a b h =>
    Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h) ((Over.w a).trans (Over.w b).symm))
  have tor : ∀ (a : Over.mk p ⟶ thickObj V I 0 G) (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G),
      b ^ N = 1 → ρ ≫ b = toBase hw a → a ^ N = 1 := fun a b hb h => by
    refine inj _ _ ((map_pow (toBaseHom hl.mul _) a N).trans (Eq.trans ?_ (map_one (toBaseHom hl.mul _)).symm))
    exact (congrArg (· ^ N) h.symm).trans (by rw [← MonObj.comp_pow, hb, MonObj.comp_one])
  have hxN := tor x y hy e
  have hxN' := tor x' y' hy' e'
  refine Iff.trans ?_ ((t.l 0).D.cubWeil_one_iff hxN hxN')
  refine Iff.trans ?_ (hl.cubWeil_iff hxN hxN' 1).symm
  constructor
  · intro h
    have := h.comp ρ
    rw [e, e', map_one] at this
    exact this
  · intro h
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil s.P.c hy hy'
    have c := hζ.comp ρ
    rw [e, e'] at c
    have hNW : IsUnit (N : W) := by simpa using hN.map (algebraMap V W)
    have : ζ = 1 := unit_eq_one_of_localHom f' hNW hζ.pow_eq_one (c.unique h)
    exact this ▸ hζ

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubmoduleEqTopOfSupSmulOfIsNilpotent
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem submodule_eq_top_of_sup_smul_of_isNilpotent {A B : Type} [CommRing A] [AddCommGroup B] [Module A B]
    {J : Ideal A} (hJ : IsNilpotent J) {N : Submodule A B} (h : ⊤ ≤ N ⊔ J • ⊤) : N = ⊤ := by
  have key : ∀ n : ℕ, ⊤ ≤ N ⊔ J ^ n • (⊤ : Submodule A B) := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul]; exact le_sup_right
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ((Submodule.smul_mono le_rfl h).trans ?_))
      rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
      exact sup_le_sup_right Submodule.smul_le_right _
  obtain ⟨n, hn⟩ := hJ
  have := key n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  exact top_unique this

theorem surjective_eval₂Hom_of_isPushout {A B C P : CommRingCat.{0}} {α : A ⟶ B} {β : A ⟶ C} {c' : B ⟶ P}
    {d' : C ⟶ P} (h : IsPushout α β c' d') (hβ : Function.Surjective β) (hJ : IsNilpotent (RingHom.ker β.hom))
    {σ : Type} (r : σ → B) (hr : Function.Surjective (MvPolynomial.eval₂Hom d'.hom fun j => c'.hom (r j))) :
    Function.Surjective (MvPolynomial.eval₂Hom α.hom r) := by
  letI : Algebra A B := α.hom.toAlgebra
  have hN : Subalgebra.toSubmodule (MvPolynomial.aeval (R := A) r).range = ⊤ := by
    refine submodule_eq_top_of_sup_smul_of_isNilpotent hJ fun b _ => ?_
    obtain ⟨p, hp⟩ := hr (c'.hom b)
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective β.hom hβ p
    have e : c'.hom (MvPolynomial.eval₂Hom α.hom r q) = c'.hom b := by
      rw [← hp, MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
      exact congrArg (fun c => MvPolynomial.eval₂Hom c _ q) (congrArg CommRingCat.Hom.hom h.w)
    have hk : b - MvPolynomial.eval₂Hom α.hom r q ∈ RingHom.ker c'.hom := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    rw [PrimeSection.ker_eq_map_of_isPushout h hβ] at hk
    refine Submodule.mem_sup.2 ⟨MvPolynomial.eval₂Hom α.hom r q, ⟨q, rfl⟩, _, ?_, add_sub_cancel _ _⟩
    rw [Ideal.smul_top_eq_map]
    exact hk
  intro b
  exact (hN.ge (Submodule.mem_top : b ∈ ⊤) :)

theorem surjective_specMap_of_isNilpotent {R R₀ : Type} [CommRing R] [CommRing R₀] (g : R →+* R₀)
    (hg : Function.Surjective g) (hJ : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := ⟨fun x => by
  obtain ⟨n, hn⟩ := hJ
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g : Set R) := fun a ha =>
    x.isPrime.mem_of_pow_mem n (by
      have := Ideal.pow_mem_pow ha n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      rw [this]
      exact zero_mem _)
  rw [← range_comap_of_surjective _ g hg] at hx
  exact hx⟩

theorem veryAmpleBy_of_isNilpotent : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (g : R →+* R₀), Function.Surjective g → IsNilpotent (RingHom.ker g) → ∀ (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (f₀ : X₀ ⟶ Spec (CommRingCat.of R₀)) (j₀ : X₀ ⟶ X), IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g)) → ∀ (H : LB X) (H₀ : LB X₀) (w : LB.Iso H₀ (H.pull j₀)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s₀ : Fin (n + 1) → LB.Sec H₀), H.IsLB → H₀.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (j₀) z ∈ (H).U k → z ∈ (H₀).U k' → gs (j₀) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → VeryAmpleBy f₀ H₀ s₀ → VeryAmpleBy f H s := by
  intro R R₀ _ _ g hg hJ X X₀ f f₀ j₀ h H H₀ w n s s₀ hH hH₀ _ hs ⟨hcov, hva⟩
  have hsurj : Surjective j₀ :=
    MorphismProperty.of_isPullback h.flip (surjective_specMap_of_isNilpotent g hg hJ)
  have loc : ∀ i, nonzeroLocus (s₀ i) = j₀ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (mem_nonzeroLocus _ (j₀ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hH (j₀ y)
      have e := hs i y j k hj hk
      rw [gs_stalkMap j₀ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (j₀.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hH₀ y
      have e := hs i y j k hj hk
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap j₀ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨top_le_iff.1 fun x _ => ?_, fun i => ?_⟩
  · obtain ⟨y, rfl⟩ := j₀.surjective x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (loc i).le hi⟩
  obtain ⟨haff₀, r₀, hr₀, hs₀⟩ := hva i
  have haff : IsAffineOpen (nonzeroLocus (s i)) :=
    AffineThickening.isAffine_of_isPullback_of_isNilpotent (RingHom.ker g) hJ (CommRingCat.ofHom g) hg rfl
      ((isPullback_morphismRestrict j₀ (nonzeroLocus (s i))).paste_vert h) (loc i ▸ haff₀ :)
  have hr := fun j => ProjSpace.secRatio_spec (s i) (s j)
  refine ⟨haff, fun j => ProjSpace.secRatio (s i) (s j), hr, ?_⟩
  have e₀ : r₀ = fun j => (j₀.appLE _ _ (loc i).le).hom (ProjSpace.secRatio (s i) (s j)) := funext fun j => by
    refine (ProjSpace.eq_secRatio _ _ (hr₀ j)).trans (ProjSpace.eq_secRatio _ _ fun k => fn_ext fun y hy => ?_).symm
    obtain ⟨l, hl⟩ := exists_chart hH (j₀ y)
    have hm : j₀ y ∈ nonzeroLocus (s i) ⊓ H.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs j₀ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs j y l k hl hy.2
    have e₂ := hs i y l k hl hy.2
    have e₃ := (Geo.Tor.gw w (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    exact (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE j₀ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  subst e₀
  have po := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
    (UY := nonzeroLocus (s₀ i)) (by rw [loc]; simp)).1
    (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
  have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ (nonzeroLocus (s i)) le_top)
      (CommRingCat.ofHom g) (j₀.appLE _ _ (loc i).le)
      ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ f₀.appLE ⊤ (nonzeroLocus (s₀ i)) le_top) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact surjective_eval₂Hom_of_isPushout po' hg hJ _ hs₀

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAbelianPartDimAddTorusRank
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAbelianPartDimAddTorusRank
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem HidaSetting.smoothDim_model : AllSet fun {_} _ _ _ {A} {G} _ _ _ => SmoothOfRelativeDimension A.g G.hom := by
  intro V _ _ _ A G _ _ s
  have hs : Smooth G.hom := s.semi.smooth
  have : GeometricallyConnected G.hom := s.semi.geomConnected
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group _ G).1
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have a := A.smoothDim
  have b : SmoothOfRelativeDimension (0 + A.g) ((Over.pullback (jK V)).obj G).hom := by
    have : IsIso s.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map s.gen.hom))
    rw [← Over.w s.gen.hom]; infer_instance
  have c : SmoothOfRelativeDimension n ((Over.pullback (jK V)).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hn
  have h₁ : n = A.g :=
    (H1.dim_unique _ c b (eSec _ (Classical.arbitrary (Spec (CommRingCat.of (FractionRing V)))))).trans (zero_add _)
  exact h₁ ▸ hn

theorem Tower.dim_eq_add_finrank : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (g' : ℕ), (SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X) ∧ ∀ a : t.Alg, SmoothOfRelativeDimension g' a.B.hom → A.g = g' + Module.finrank ℤ s.X := by
  intro V _ _ _ A G _ _ s t g'
  have hG : SmoothOfRelativeDimension A.g G.hom := HidaSetting.smoothDim_model V A G s
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by simpa using (IsLocalRing.maximalIdeal.isMaximal V).ne_top)
  have h₀ : SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X := fun h =>
    TQ.dim_eq_add_finrank _ s.X _ (t.l 0).Q A.g g'
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG) h
  refine ⟨h₀, fun a ha => h₀ ?_⟩
  obtain ⟨h, -⟩ := a.b_pb 0
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 ha

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAbelianPartDimAddTorusRankStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.dim_eq_abelianPart_dim_add_torus_rank : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (g' : ℕ), (SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X) ∧ ∀ a : t.Alg, SmoothOfRelativeDimension g' a.B.hom → A.g = g' + Module.finrank ℤ s.X := by
  first | exact @GlobalTheory.UU.Tower.dim_eq_add_finrank | exact GlobalTheory.UU.Tower.dim_eq_add_finrank | (intros; apply GlobalTheory.UU.Tower.dim_eq_add_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open scoped TensorProduct in
theorem flat_SpecMap_of_flat_localization_maximal (V : Type) [CommRing V] (C : CommRingCat.{0})
    (f : CommRingCat.of V ⟶ C)
    (h : ∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd (Spec.map f)
      (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m)))))) :
    Flat (Spec.map f) := by
  rw [Flat.SpecMap_iff]
  letI : Algebra V C := f.hom.toAlgebra
  have key : Module.Flat V C := by
    refine Module.flat_of_isLocalized_maximal V C (fun P _ => Localization.AtPrime P ⊗[V] C)
      (fun P _ => TensorProduct.mk V (Localization.AtPrime P) C 1) fun P _ => ?_
    have sq := (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct V (Localization.AtPrime P) C)).flip
    have h1 := h P
    have h2 := sq.isoPullback_hom_snd
    have h3 : Flat (sq.isoPullback.hom ≫ pullback.snd _ _) := by
      haveI : Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V C)))
        (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime P))))) := h1
      infer_instance
    rw [h2, Flat.SpecMap_iff] at h3
    haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime P ⊗[V] C) :=
      RingHom.flat_algebraMap_iff.mp h3
    exact Module.Flat.trans V (Localization.AtPrime P) _
  exact key

theorem flat_of_isFinite_of_flat_localization_maximal :
    ∀ (V : Type) [CommRing V] (H : Over (Sp V)), IsFinite H.hom → (∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd H.hom (spMap (algebraMap V (Localization.AtPrime m))))) → Flat H.hom := by
  intro V _ H hfin h
  haveI : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨f, hf⟩ := Spec.map_surjective (H.left.isoSpec.inv ≫ H.hom)
  have hf' : H.hom = H.left.isoSpec.hom ≫ Spec.map f := by rw [hf]; simp
  have : Flat (Spec.map f) := by
    refine flat_SpecMap_of_flat_localization_maximal V _ f fun m _ => ?_
    have h1 := h m
    rw [hf, ← pullbackRightPullbackFstIso_inv_snd_snd]
    haveI : Flat (pullback.snd H.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m))))) := h1
    infer_instance
  rw [hf']
  infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximalStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_isFinite_of_flat_at_maximal : ∀ (V : Type) [CommRing V] (H : Over (Sp V)), IsFinite H.hom → (∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd H.hom (spMap (algebraMap V (Localization.AtPrime m))))) → Flat H.hom := by
  first | exact @GlobalTheory.flat_of_isFinite_of_flat_localization_maximal | exact GlobalTheory.flat_of_isFinite_of_flat_localization_maximal | (intros; apply GlobalTheory.flat_of_isFinite_of_flat_localization_maximal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageOneMulInv
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageOneMulInv
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

section

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B T : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj B] [GrpObj G']
  [GrpObj B'] {φ : G'.left ⟶ G.left} {β : B'.left ⟶ B.left}

theorem exists_imageHom (hG : IsGrpPullback G' G f φ) (hB : IsGrpPullback B' B f β) (q : G' ⟶ B') [IsMonHom q]
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (xe : Z ⟶ G'.left) (x₀ : T ⟶ G) (h₀ : xe ≫ φ = r ≫ x₀.left) :
    ∃ (Y : Over S) (R : Y ⟶ T) (Φ : (T ⟶ G) → (Y ⟶ B)), Φ 1 = 1 ∧ (∀ x y, Φ (x * y) = Φ x * Φ y) ∧
      (∀ x, Φ x⁻¹ = (Φ x)⁻¹) ∧
      (∀ x b, (∀ ye : Z ⟶ G'.left, ye ≫ φ = r ≫ x.left → ye ≫ q.left ≫ β = r ≫ b.left) → Φ x = R ≫ b) ∧
      ∀ b, Φ x₀ = R ≫ b → xe ≫ q.left ≫ β = r ≫ b.left := by
  have hc : r ≫ T.hom = (xe ≫ G'.hom) ≫ f := by
    rw [Category.assoc, ← hG.1.w, reassoc_of% h₀, Over.w]
  obtain ⟨eG, heG⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hG _ _ hc
  obtain ⟨eB, heB⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc
  let R : Over.mk (r ≫ T.hom) ⟶ T := Over.homMk r rfl
  refine ⟨_, R, fun x => eB (eG.symm (R ≫ x) ≫ q), ?_, fun x y => ?_, fun x => ?_, fun x b h => ?_,
    fun b h => ?_⟩
  · simp only [MonObj.comp_one, map_one, MonObj.one_comp]
  · simp only [MonObj.comp_mul, map_mul, MonObj.mul_comp]
  · simp only [GrpObj.comp_inv, map_inv, GrpObj.inv_comp]
  · apply Over.OverMorphism.ext
    refine (heB _).trans ((Category.assoc _ _ _).trans (h _ ?_))
    refine (heG _).symm.trans ?_
    rw [MulEquiv.apply_symm_apply]
    rfl
  · let xe' : Over.mk (xe ≫ G'.hom) ⟶ G' := Over.homMk xe rfl
    have h₁ : eG xe' = R ≫ x₀ := Over.OverMorphism.ext ((heG _).trans h₀)
    have h₂ : eB (xe' ≫ q) = R ≫ b := by
      rw [← h]
      beta_reduce
      rw [← h₁, MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans ((heB (xe' ≫ q)).symm.trans (congrArg (fun z => z.left) h₂))

end

theorem image_one_mul_inv : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [Algebra V W] (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G)).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ∧ ((∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x * x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b * b').left) ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x⁻¹).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b⁻¹).left)) := by
  intro V _ _ _ A G _ _ s t a W _ _ x x' b b'
  have hG := fun e => isGrpPullback_pullback G (thick V (IsLocalRing.maximalIdeal V) e)
  have hB := fun e => (a.b_pb e).1
  have hq := fun e => (t.l e).Q.q_hom
  refine ⟨fun e Z r xe h => ?_, fun h₁ h₂ => ⟨fun e Z r xe h => ?_, fun e Z r xe h => ?_⟩⟩
  · obtain ⟨Y, R, Φ, e₁, -, -, -, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k 1 (by rw [e₁, MonObj.comp_one])
  · obtain ⟨Y, R, Φ, -, e₂, -, l, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k _ (by rw [e₂, l x b (h₁ e Z r), l x' b' (h₂ e Z r), MonObj.comp_mul])
  · obtain ⟨Y, R, Φ, -, -, e₃, l, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k _ (by rw [e₃, l x b (h₁ e Z r), GrpObj.comp_inv])

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageOneMulInvStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.abelianPart_image_one_mul_inv : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [Algebra V W] (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G)).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ∧ ((∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x * x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b * b').left) ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x⁻¹).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b⁻¹).left)) := by
  first | exact @GlobalTheory.UU.image_one_mul_inv | exact GlobalTheory.UU.image_one_mul_inv | (intros; apply GlobalTheory.UU.image_one_mul_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericFibreCardTorsionCubicalPairingPerfect
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericFibreCardTorsionCubicalPairingPerfect
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem card_and_nondeg_of_pullback (hL : Laws) {S S' : Scheme.{0}} [IsLocallyNoetherian S'] (f : S' ⟶ S)
    (A : PolAV S') {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) (φ : A.A.left ⟶ G.left)
    (hφ : IsPullback φ A.A.hom G.hom f)
    (mul : ∀ (T : Over S') (x y : T ⟶ A.A), toBase hφ.w (x * y) = toBase hφ.w x * toBase hφ.w y)
    (hw : LBIso A.L (P.L.L.pull φ)) {F : Type} [Field F] [IsAlgClosed F] (q : Spec (CommRingCat.of F) ⟶ S')
    {N : ℕ} (h1 : 1 ≤ N) (hN : (N : F) ≠ 0) :
    Nat.card {x : Over.mk (q ≫ f) ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧
      ∀ x : Over.mk (q ≫ f) ⟶ G, x ^ N = 1 →
        (∀ y : Over.mk (q ≫ f) ⟶ G, y ^ N = 1 → CubWeil P.c N x y 1) → x = 1 := by
  haveI := A.isAb.comm
  obtain ⟨w, hg⟩ := hw
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, hm⟩ := exists_isCPMap P mul A.L A.isLB w hg
  let β : (Over.mk q ⟶ A.A) →* (Over.mk (q ≫ f) ⟶ G) := toBaseHom mul (Over.mk q)
  have hβ : ∀ y, (β y).left = y.left ≫ φ := fun y => rfl
  have inj : Function.Injective β := fun a b e => Over.OverMorphism.ext (hφ.hom_ext
    ((hβ a).symm.trans ((congrArg CommaMorphism.left e).trans (hβ b))) ((Over.w a).trans (Over.w b).symm))
  have surj : Function.Surjective β := fun x =>
    ⟨Over.homMk (hφ.lift x.left q (Over.w x)) (hφ.lift_snd _ _ _),
      Over.OverMorphism.ext ((hβ _).trans (hφ.lift_fst _ _ _))⟩
  have hp : ∀ y, y ^ N = 1 ↔ β y ^ N = 1 := fun y => by
    rw [← map_pow, ← map_one β, inj.eq_iff]
  refine ⟨?_, fun x hx h => ?_⟩
  · rw [← (hL.mulN S' A N h1).2.2.2.2 F q hN]
    exact (Nat.card_congr ((Equiv.ofBijective β ⟨inj, surj⟩).subtypeEquiv hp)).symm
  · obtain ⟨x, rfl⟩ := surj x
    have hx' := (hp x).2 hx
    rw [GlobalTheory.ThetaRep.eq_one_of_weilIs hL A q hN x hx' fun y hy => ?_, map_one]
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil c hx' hy
    have e := (cubWeil_map _ _ f G A.A P ⟨_, c, s, h₁, h₂, h₃⟩ φ _ w hm N (Over.mk q) x y ζ hζ).unique (h _ ((hp y).1 hy))
    exact (cubWeil_iff_weilIs hL.globalFns A.isAb hx' hy 1).1 (e ▸ hζ)

theorem generic_card_and_nondeg : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → Nat.card {x : TF (R := V) F ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧ ∀ x : TF (R := V) F ⟶ G, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ G, y ^ N = 1 → CubWeil s.P.c N x y 1) → x = 1 := by
  intro hL V _ _ _ A G _ _ s F _ _ _ N h1
  haveI := s.gen_hom
  haveI : CharZero V := s.cdvr.2.2
  haveI : CharZero (FractionRing V) := charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap (FractionRing V) F).injective
  let φ : A.A.left ⟶ G.left := s.gen.inv.left ≫ pullback.fst G.hom (jK V)
  haveI : IsIso s.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map s.gen.inv))
  have hφ : IsPullback φ A.A.hom G.hom (jK V) := by
    have a : IsPullback s.gen.inv.left A.A.hom (pullback.snd G.hom (jK V)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w s.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using a.paste_horiz (IsPullback.of_hasPullback G.hom (jK V))
  refine card_and_nondeg_of_pullback hL (jK V) A s.P φ hφ (fun T x y => ?_) ?_ (jFK F) h1
    (Nat.cast_ne_zero.2 (by omega))
  · have e : ∀ a : T ⟶ A.A, toBase hφ.w a = toBase (A := G) (A' := (Over.pullback (jK V)).obj G)
        (g := pullback.fst G.hom (jK V)) pullback.condition (a ≫ s.gen.inv) := fun a =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, e, e, MonObj.mul_comp, toBase_mul_pullback]
  · exact LBIso.chartPull (chartPullSec A.L s.gen.hom.left s.gen.inv.left
      (congrArg CommaMorphism.left s.gen.inv_hom_id)) (chartPullSame s.P.L.L _ _ _ _ fun _ => rfl) ⟨s.wA, s.wA_gen⟩

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericFibreCardTorsionCubicalPairingPerfectStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.generic_fibre_card_torsion_cubical_pairing_perfect : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → Nat.card {x : TF (R := V) F ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧ ∀ x : TF (R := V) F ⟶ G, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ G, y ^ N = 1 → CubWeil s.P.c N x y 1) → x = 1 := by
  first | exact @GlobalTheory.UU.generic_card_and_nondeg | exact GlobalTheory.UU.generic_card_and_nondeg | (intros; apply GlobalTheory.UU.generic_card_and_nondeg <;> assumption)
end
end
