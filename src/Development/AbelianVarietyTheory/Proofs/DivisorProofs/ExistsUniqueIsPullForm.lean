module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocycles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoFormExistsPowSmulEqZeroOfIsLocalization
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechDR

theorem mOm_two_eq_exteriorPowerMapOver {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] (x : Om R A 2) :
    (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x =
      GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) x := by
  set h := SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)
  let L : Om R A 2 →ₗ[A] Om R B 2 :=
    { toFun := h.mOm 2
      map_add' := map_add _
      map_smul' := fun a y ↦ by
        rw [h.mOm_smul, RingHom.id_apply]; exact algebraMap_smul B a _ }
  have e : L = GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      GlobalTheory.exteriorPowerMapOver_ιMulti, hv, ← wedge_eq_ιMulti]
    change h.mOm 2 _ = _
    rw [h.mOm_wedge, h.oneFormMap_eq_kaehlerDifferential_map (fun _ ↦ rfl), h.oneFormMap_eq_kaehlerDifferential_map (fun _ ↦ rfl), wedge_eq_ιMulti]
    congr 1
    ext i; fin_cases i <;> rfl
  exact LinearMap.congr_fun e x

theorem twoForm_exists_pow_smul_eq_zero_of_isLocalization {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] (c : A)
    [IsLocalization.Away c B] (x : Om R A 2)
    (hx : (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x = 0) :
    ∃ n : ℕ, c ^ n • x = 0 := by
  haveI : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c)
  have hb := GlobalTheory.TopForm.isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale R A B) 2
  haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers c) B _).2 hb
  rw [mOm_two_eq_exteriorPowerMapOver, ← map_zero (GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B))] at hx
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (r := c) hx
  exact ⟨n, hn.trans (smul_zero _)⟩

theorem twoForm_exists_pow_smul_eq_zero_of_algHom {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (c : A)
    (hc : @IsLocalization.Away A _ c B _ f.toRingHom.toAlgebra) (x : Om R A 2)
    (hx : (SemiHom.of_algHom f).mOm 2 x = 0) : ∃ n : ℕ, c ^ n • x = 0 := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact twoForm_exists_pow_smul_eq_zero_of_isLocalization c x hx

theorem twoForm_sep_of_basis : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : AffOp X') (η : Om R' ((OAff s').obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm (OAff s') 2 u η = 0) → η = 0) := by
  intro R' _ X' s' C' _ G hcov T η hη
  obtain ⟨n, b, hb, hf⟩ := hcov T
  have key : ∀ i, ∃ m : ℕ, b i ^ m • η = 0 := by
    intro i
    let U : X'.affineOpens := T.unop
    let c : Γ(X', U.1) := b i
    let V : X'.affineOpens := ⟨X'.basicOpen c, U.2.basicOpen c⟩
    have hle : V ≤ U := X'.basicOpen_le c
    let u : T ⟶ Opposite.op V := (homOfLE hle).op
    have hu : IsUnit (mp (OAff s') u (b i)) := X'.toRingedSpace.isUnit_res_basicOpen c
    obtain ⟨t, v, w, hvw⟩ := hf i (Opposite.op V) u hu
    have h0 : pOm (OAff s') 2 u η = 0 := by rw [← hvw, pOm_comp, hη t v, map_zero]
    exact twoForm_exists_pow_smul_eq_zero_of_algHom (mp (OAff s') u) (b i)
      (U.2.isLocalization_basicOpen c) η h0
  choose m hm using key
  have hN : ∀ i, b i ^ (∑ j, m j) • η = 0 := fun i ↦ by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (m j))
      (Finset.mem_univ i))
    rw [hk, pow_add, mul_comm, mul_smul, hm i, smul_zero]
  have := Ideal.span_pow_eq_top _ hb (∑ j, m j)
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at this
  obtain ⟨r, hr⟩ := this
  rw [← one_smul ((OAff s').obj T) η, ← hr, Finset.sum_smul]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [Function.comp_apply, mul_smul, hN i, smul_zero]

end GlobalTheory.CechDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairBelowTwo
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR

theorem exists_pair_below_two : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R'), (∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) → ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S')) := by
  intro R' _ X X' φ s' t₁ t₂ S h₁ h₂
  have hS₁ : S.unop.1 ≤ t₁.unop.1.1.1 := leOfHom h₁.unop
  have hS₂ : S.unop.1 ≤ t₂.unop.1.1.1 := leOfHom h₂.unop
  let B : Set Γ(X', S.unop.1) := {g | ∃ W : X.affineOpens, W.1 ≤ t₁.unop.1.2.1 ∧
    W.1 ≤ t₂.unop.1.2.1 ∧ X'.basicOpen g ≤ φ ⁻¹ᵁ W.1}
  have hB : Ideal.span B = ⊤ := by
    refine (S.unop.2.self_le_iSup_basicOpen_iff).1 fun x hx ↦ ?_
    have hx₁ : φ.base x ∈ t₁.unop.1.2.1 := t₁.unop.2 (hS₁ hx)
    have hx₂ : φ.base x ∈ t₂.unop.1.2.1 := t₂.unop.2 (hS₂ hx)
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
      (U := t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨hx₁, hx₂⟩
    obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := S.unop.1 ⊓ φ ⁻¹ᵁ W)
      ⟨x, hx, hxW⟩ hx
    have hfB : f ∈ B := ⟨⟨W, hW⟩, fun y hy ↦ (hWV hy).1, fun y hy ↦ (hWV hy).2,
      hf.trans inf_le_right⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfB⟩, hxf⟩
  obtain ⟨s0, hs0, hspan⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
  refine ⟨s0.card, fun i ↦ (s0.equivFin.symm i).1, ?_, fun i S' u hu ↦ ?_⟩
  · have hsp : Ideal.span (Set.range fun i ↦ ((s0.equivFin.symm i).1 : Γ(X', S.unop.1))) = ⊤ := by
      rw [eq_top_iff, ← hspan]
      exact Ideal.span_mono fun x hx ↦ ⟨s0.equivFin ⟨x, hx⟩, by simp⟩
    exact hsp
  · have hbB : (s0.equivFin.symm i).1 ∈ B := hs0 (s0.equivFin.symm i).2
    obtain ⟨W, hW₁, hW₂, hW⟩ := hbB
    set g : Γ(X', S.unop.1) := (s0.equivFin.symm i).1 with hg
    change IsUnit (X'.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu
    have hS' : S'.unop.1 ≤ X'.basicOpen g := by
      have := Scheme.basicOpen_of_isUnit X' hu
      rw [Scheme.basicOpen_res] at this
      rw [← this]; exact inf_le_right
    let t₃ : Pair φ := ⟨(⟨X'.basicOpen g, S.unop.2.basicOpen g⟩, W), hW⟩
    refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩⟩
    · exact ⟨(X'.basicOpen_le g).trans hS₁, hW₁⟩
    · exact ⟨(X'.basicOpen_le g).trans hS₂, hW₂⟩
    · exact hS'

end GlobalTheory.CechDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullHyp1RestrictSurjective
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp1_restrict_surjective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hO : Function.Surjective (CoefMap.restrict F G).pull1)
    (hc : ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
        κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) →
      ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
        κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) →
      ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T))
    (hf : Function.Surjective (pullGlob1 (CoefMap.restrict F G)))
    (hs : ∀ (T : C) (η : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u η = 0) → η = 0) :
    Function.Surjective (pullHyp1 (CoefMap.restrict F G)) := by
  intro c'
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective _ c'
  obtain ⟨h0, hh⟩ := hO (toO _ (Hyp1.mk _ c'))
  obtain ⟨f, rfl⟩ := H1.mk_surjective F h0
  rw [toO_mk, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hh
  obtain ⟨g', hg'⟩ := hh
  let g : ∀ t, F.obj (G.obj t) := g'
  let f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t') := c'.1.1
  let ω' : ∀ t, Ω[F.obj (G.obj t)⁄R] := c'.1.2
  have hga : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) - f' t t' a := fun t t' a ↦
    congrFun (congrFun (congrFun hg' t) t') a
  have hκ : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      D R _ (f.1 T T'' (φ ≫ ψ)) = p1 F ψ (D R _ (f.1 T T' φ)) + D R _ (f.1 T' T'' ψ) := by
    intro T T' T'' φ ψ
    rw [Z1.comp f φ ψ, map_add (f := _), p1_D]
  let θ' : ∀ t, Ω[F.obj (G.obj t)⁄R] := fun t ↦ ω' t + D R _ (g t)
  have hθ' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      D R _ (f.1 _ _ (G.map a)) = θ' t' - p1 F (G.map a) (θ' t) := by
    intro t t' a
    have e1 : ω' t' = p1 F (G.map a) (ω' t) + D R _ (f' t t' a) := cechDeRhamTotalCocyclesOne.conn c' a
    have e2 : f.1 _ _ (G.map a) = g t' - mp F (G.map a) (g t) + f' t t' a :=
      (sub_eq_iff_eq_add.1 (hga a).symm)
    simp only [θ']
    rw [e1, e2]
    simp only [map_add (f := _), map_sub, p1_D]
    abel
  obtain ⟨θ, hθ⟩ := hc (fun T T' φ ↦ D R _ (f.1 T T' φ)) hκ θ' hθ'
  have hθ2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), D R _ (f.1 T T' φ) = θ T' - p1 F φ (θ T) := hθ
  let ψ0 : Glob1 (G ⋙ F) := ⟨fun t ↦ θ' t - θ (G.obj t), fun t t' a ↦ by
    change θ' t' - θ (G.obj t') = p1 F (G.map a) (θ' t - θ (G.obj t))
    have e := (hθ2 (G.map a)).symm.trans (hθ' a)
    rw [map_sub]
    rw [← sub_eq_zero] at e ⊢
    rw [← neg_eq_zero, ← e]
    abel⟩
  obtain ⟨ψ, hψ⟩ := hf ψ0
  have hψG : ∀ t, ψ.1 (G.obj t) = θ' t - θ (G.obj t) := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun z : Glob1 (G ⋙ F) ↦ z.1 t) hψ)
  let ω : A0 F := fun T ↦ θ T + ψ.1 T
  have hωG : ∀ t, ω (G.obj t) = θ' t := fun t ↦ by
    change θ (G.obj t) + ψ.1 (G.obj t) = _
    rw [hψG]; abel
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T) + D R _ (f.1 T T' φ) := by
    intro T T' φ
    change θ T' + ψ.1 T' = p1 F φ (θ T + ψ.1 T) + D R _ (f.1 T T' φ)
    rw [map_add (f := _), ← ψ.2 φ, hθ2 φ]; abel
  have hclosed : ∀ T, dOne R _ (ω T) = 0 := by
    intro T
    refine hs T _ fun t u ↦ ?_
    have e : p1 F u (ω T) = ω' t + D R _ (g t) - D R _ (f.1 _ _ u) := by
      rw [eq_sub_iff_add_eq, ← hconn u, hωG]
    rw [pOm_dOne, e, map_sub, map_add (f := _), dOne_D, dOne_D]
    have e3 : dOne R _ (ω' t) = 0 := cechDeRhamTotalCocyclesOne.closed c' t
    rw [e3]; simp
  let c : cechDeRhamTotalCocyclesOne F := ⟨(f.1, ω), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hconn, hclosed⟩⟩
  refine ⟨Hyp1.mk F c, ?_⟩
  rw [pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨g', Tot1.ext (fun t t' a ↦ hga a) fun t ↦ ?_⟩
  have e4 : q1 (CoefMap.restrict F G) t (ω (G.obj t)) = θ' t := (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).trans (hωG t)
  change D R _ (g t) = q1 (CoefMap.restrict F G) t (ω (G.obj t)) - c'.1.2 t
  rw [e4]
  change _ = ω' t + D R _ (g t) - ω' t
  abel

end GlobalTheory.CechDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictGlob1Bijective
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem restrict_glob1_bijective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (ω : Ω[F.obj T⁄R]), (∀ t (u : T ⟶ G.obj t), p1 F u ω = 0) → ω = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → Ω[F.obj (G.obj t)⁄R]), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 F (G.map a) (s t u)) → ∃ ω : Ω[F.obj T⁄R], ∀ t u, p1 F u ω = s t u) → Function.Bijective (pullGlob1 (CoefMap.restrict F G)) := by
  intro R _ C _ C' _ F G hsep hglue
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    apply Subtype.ext
    funext T
    refine hsep T (ω.1 T) fun t u ↦ ?_
    have h1 := congrArg (fun x : Glob1 (G ⋙ F) ↦ x.1 t) hω
    have h2 : (pullGlob1 (CoefMap.restrict F G) ω).1 t = ω.1 (G.obj t) := cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _
    rw [← ω.2 u, ← h2, h1]
    rfl
  · intro ω'
    have hc : ∀ (T : C), ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t), p1 F u ω = ω'.1 t :=
      fun T ↦ hglue T (fun t _ ↦ ω'.1 t) fun t t' u a ↦ ω'.2 a
    choose ω hω using hc
    have hglob : ω ∈ Glob1 F := by
      intro T T' φ
      rw [← sub_eq_zero]
      refine hsep T' _ fun t u ↦ ?_
      rw [map_sub, ← oneFormsMapOfFunctorMorphism_comp, hω, hω, sub_self]
    refine ⟨⟨ω, hglob⟩, Subtype.ext (funext fun t ↦ ?_)⟩
    change q1 (CoefMap.restrict F G) t (ω (G.obj t)) = ω'.1 t
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, ← hω (G.obj t) t (𝟙 _), oneFormsMapOfFunctorMorphism_id]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullHyp1RestrictInjective
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp1_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h1 : Function.Injective (CoefMap.restrict F G).pull1)
    (h0 : ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) →
      ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t)
    (hf : Function.Injective (pullGlob1 (CoefMap.restrict F G))) :
    Function.Injective (pullHyp1 (CoefMap.restrict F G)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, rfl⟩ := Hyp1.mk_surjective F c
  have ht : toO F (Hyp1.mk F x) = 0 := h1 (by rw [← toO_pullHyp1, hc, map_zero, map_zero])
  rw [pullHyp1_mk, Hyp1.mk_eq_zero] at hc
  obtain ⟨g, hg'⟩ := hc
  obtain ⟨g', rfl⟩ : ∃ g' : ∀ t, F.obj (G.obj t), (g' : Tot0 (G ⋙ F)) = g := ⟨g, rfl⟩
  have hf' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' - mp F (G.map a) (g' t) = x.1.1 _ _ (G.map a) :=
    fun t t' a ↦ congrArg (fun y : Tot1 (G ⋙ F) ↦ y.1 t t' a) hg'
  have hω : ∀ t, D R _ (g' t) = x.1.2 (G.obj t) := fun t ↦
    (congrArg (fun y : Tot1 (G ⋙ F) ↦ y.2 t) hg').trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _)
  rw [toO_mk, H1.mk_eq_zero] at ht
  obtain ⟨g₀, hg₀⟩ := ht
  have hg0 : ∀ (T T' : C) (φ : T ⟶ T'), g₀ T' - mp F φ (g₀ T) = x.1.1 T T' φ := fun T T' φ ↦
    congrFun (congrFun (congrFun hg₀ T) T') φ
  obtain ⟨h, hh, hhG⟩ := h0 (fun t ↦ g' t - g₀ (G.obj t)) (fun t t' a ↦ by
    have e1 := hf' a
    have e2 := hg0 _ _ (G.map a)
    rw [map_sub]
    linear_combination e1 - e2)
  let θ : Glob1 F := ⟨fun T ↦ x.1.2 T - D R _ (g₀ T), fun T T' φ ↦ by
    show x.1.2 T' - D R _ (g₀ T') = p1 F φ (x.1.2 T - D R _ (g₀ T))
    rw [map_sub, p1_D, cechDeRhamTotalCocyclesOne.conn x φ, ← hg0 T T' φ, map_sub]; abel⟩
  let ψ : Glob1 F := ⟨fun T ↦ D R _ (h T), fun T T' φ ↦ by
    show D R _ (h T') = p1 F φ (D R _ (h T))
    rw [p1_D, ← hh φ]⟩
  have hθψ : θ = ψ := hf (Subtype.ext (funext fun t ↦ by
    change q1 (CoefMap.restrict F G) t (θ.1 (G.obj t)) = q1 (CoefMap.restrict F G) t (ψ.1 (G.obj t))
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, cechDeRhamCoefMapOneForms_restrictAlongFunctor]
    show x.1.2 (G.obj t) - D R _ (g₀ (G.obj t)) = D R _ (h (G.obj t))
    rw [hhG, map_sub, hω]))
  refine Hyp1.mk_eq_zero.2 ⟨g₀ + h, Tot1.ext (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · rw [dTot0_f]
    simp only [Pi.add_apply, map_add (f := _)]
    linear_combination hh φ + hg0 T T' φ
  · have e : x.1.2 T - D R _ (g₀ T) = D R _ (h T) := congrArg (fun ω : Glob1 F ↦ ω.1 T) hθψ
    rw [dTot0_ω, Pi.add_apply, map_add (f := _), ← e]
    abel

end GlobalTheory.CechDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleOneFormsCoboundaryOfRestrict
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory

theorem cocycle_one_forms_coboundary_of_restrict : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (ω : Ω[F.obj T⁄R]), (∀ t (u : T ⟶ G.obj t), p1 F u ω = 0) → ω = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → Ω[F.obj (G.obj t)⁄R]), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 F (G.map a) (s t u)) → ∃ ω : Ω[F.obj T⁄R], ∀ t u, p1 F u ω = s t u) → ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) → ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T) := by
  intro R _ C _ C' _ F G hSep hGlue κ hκ θ' hθ'
  have key : ∀ T : C, ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t),
      p1 F u ω = θ' t - κ T (G.obj t) u := by
    intro T
    refine hGlue T (fun t u ↦ θ' t - κ T (G.obj t) u) ?_
    intro t t' u a
    simp only [map_sub]
    rw [hκ u (G.map a), hθ' a]
    abel
  choose θ hθ using key
  refine ⟨θ, fun T T' φ ↦ ?_⟩
  have h0 : κ T T' φ - θ T' + p1 F φ (θ T) = 0 := by
    refine hSep T' _ (fun t u ↦ ?_)
    have e1 := hκ φ u
    have e2 := hθ T' t u
    have e3 := hθ T t (φ ≫ u)
    rw [oneFormsMapOfFunctorMorphism_comp] at e3
    simp only [map_add (f := _), map_sub, e2, e3]
    rw [e1]
    abel
  rw [← sub_eq_zero]
  rw [← h0]
  abel

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverAffine
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR

theorem pair_cover_affine {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u := by
  intro T
  have hT : IsAffineOpen T.unop.1 := T.unop.2
  let G : Set Γ(X', T.unop.1) :=
    {f | ∃ V : X.affineOpens, X'.basicOpen f ≤ φ ⁻¹ᵁ V.1}
  have hG : Ideal.span G = ⊤ := by
    rw [← hT.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (φ x)) isOpen_univ
    obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := φ ⁻¹ᵁ V) ⟨x, hxV⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨⟨V, hV⟩, hf⟩⟩, hxf⟩
  obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
  · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X', T.unop.1)) := by
      ext f
      constructor
      · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
      · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
    exact hR ▸ hF
  · intro i S u hu
    obtain ⟨V, hV⟩ := hFG (F.equivFin.symm i).2
    set f : Γ(X', T.unop.1) := (F.equivFin.symm i).1
    have hW : IsAffineOpen (X'.basicOpen f) := hT.basicOpen f
    have hWT : X'.basicOpen f ≤ T.unop.1 := X'.basicOpen_le f
    let t : Pair φ := ⟨(⟨_, hW⟩, V), hV⟩
    have hSW : S.unop.1 ≤ X'.basicOpen f := by
      have h1 : X'.basicOpen (X'.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
        X'.basicOpen_of_isUnit hu
      rw [Scheme.basicOpen_res] at h1
      rw [← h1]; exact inf_le_right
    refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X'.affineOpens) ≤ T.unop from hWT)).op,
      (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X'.affineOpens) from hSW)).op, ?_⟩
    exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

end GlobalTheory.CechDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPowSmulEqZeroOfResBasicOpen
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem form_pow_smul_eq_zero_of_res_basicOpen {R' : Type} [CommRing R'] {X' : Scheme.{0}}
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (f : Γ(X', W.1)) (hU : IsAffineOpen (X'.basicOpen f))
    (hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : p1 (OAff s') (homOfLE hle).op ω = 0) :
    ∃ n : ℕ, ((show (OAff s').obj (op W) from f) ^ n) • ω = 0 := by
  let A := (OAff s').obj (op W)
  let B := (OAff s').obj (op (⟨X'.basicOpen f, hU⟩ : X'.affineOpens))
  let ψ : A →ₐ[R'] B := mp (OAff s') (homOfLE hle).op
  letI : Algebra A B := (ψ : A →+* B).toAlgebra
  haveI : IsScalarTower R' A B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  haveI : IsLocalization.Away (show A from f) B := W.2.isLocalization_basicOpen f
  have e := (semiHom_mp (OAff s') (homOfLE hle).op).oneFormMap_eq_kaehlerDifferential_map (R := R') (B := A) (B' := B)
    (fun b ↦ rfl) ω
  have h' : KaehlerDifferential.map R' R' A B ω = 0 := e.symm.trans h
  obtain ⟨⟨c, hc⟩, hc0⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (show A from f))
    (f := KaehlerDifferential.map R' R' A B)).1 h'
  obtain ⟨n, rfl⟩ := hc
  exact ⟨n, hc0⟩

theorem form_eq_zero_of_basis_cover : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : AffOp X') (ω : Ω[(OAff s').obj T⁄R']), (∀ t (u : T ⟶ G.obj t), p1 (OAff s') u ω = 0) → ω = 0) := by
  intro R' _ X' s' C' _ G hcov T ω hω
  obtain ⟨n, b, hspan, hb⟩ := hcov T
  let A := (OAff s').obj T
  let J : Ideal A := (Submodule.span A {ω}).annihilator
  have hpow : ∀ i, ∃ m : ℕ, b i ^ m ∈ J := by
    intro i
    have hU : IsAffineOpen (X'.basicOpen (show Γ(X', T.unop.1) from b i)) :=
      T.unop.2.basicOpen _
    have hle : (⟨X'.basicOpen (show Γ(X', T.unop.1) from b i), hU⟩ : X'.affineOpens) ≤ T.unop :=
      X'.basicOpen_le _
    have hunit : IsUnit (mp (OAff s') (homOfLE hle).op (b i)) :=
      X'.toRingedSpace.isUnit_res_basicOpen (show Γ(X', T.unop.1) from b i)
    obtain ⟨t, v, w, hvw⟩ := hb i _ (homOfLE hle).op hunit
    have h0 : p1 (OAff s') (homOfLE hle).op ω = 0 := by
      rw [← hvw, oneFormsMapOfFunctorMorphism_comp, hω t v, map_zero]
    obtain ⟨m, hm⟩ := form_pow_smul_eq_zero_of_res_basicOpen s' T.unop _ hU hle ω h0
    exact ⟨m, (Submodule.mem_annihilator_span_singleton ω _).2 hm⟩
  choose m hm using hpow
  have hJ : J = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_pow_eq_top _ hspan (∑ i, m i), Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hmi : m i ≤ ∑ j, m j :=
      Finset.single_le_sum (f := m) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    change b i ^ (∑ j, m j) ∈ J
    rw [← Nat.add_sub_cancel' hmi, pow_add]
    exact J.mul_mem_right _ (hm i)
  have h1 : (1 : A) ∈ J := hJ ▸ Submodule.mem_top
  simpa using (Submodule.mem_annihilator_span_singleton _ _).1 h1

end GlobalTheory.CechDR
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CechDR

open CatCoh

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem pairRes_bijective (φ : X' ⟶ X) (s' : X' ⟶ Sp R') :
    Function.Bijective (pairRes φ s').pull1 ∧ Function.Bijective (pullGlob1 (pairRes φ s')) ∧
      Function.Bijective (pullHyp1 (pairRes φ s')) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  have b1 : Function.Bijective (pairRes φ s').pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg, _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  exact ⟨b1, bg, _root_.GlobalTheory.CechDR.pullHyp1_restrict_injective _ _ b1.1 (_root_.GlobalTheory.compat_family_extend _ _ hs hg) bg.1,
    _root_.GlobalTheory.CechDR.pullHyp1_restrict_surjective _ _ b1.2 (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2⟩

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

theorem existsUnique_isPull1 (c : HH1 s) : ∃! c', IsPull1 h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective φ s').2.2.existsUnique (pullHyp1 (pairPull h) c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

theorem existsUnique_isPullO (c : HO1 s) : ∃! c', IsPullO h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective φ s').1.existsUnique ((pairPull h).pull1 c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

theorem existsUnique_isPullForm (ω : GlobForm s) : ∃! ω', IsPullForm h ω ω' := by
  obtain ⟨ω', hω, hu⟩ := (pairRes_bijective φ s').2.1.existsUnique (pullGlob1 (pairPull h) ω)
  exact ⟨ω', hω.symm, fun y hy ↦ hu y hy.symm⟩

def pairResEquiv1 (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HH1 s' ≃ₗ[R'] Hyp1 (OPair φ s') :=
  LinearEquiv.ofBijective (pullHyp1 (pairRes φ s')) (pairRes_bijective φ s').2.2

def pairResEquivO (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HO1 s' ≃ₗ[R'] CatCoh.H1 (OPair φ s') :=
  LinearEquiv.ofBijective (pairRes φ s').pull1 (pairRes_bijective φ s').1

def pairResEquivForm (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : GlobForm s' ≃ₗ[R'] Glob1 (OPair φ s') :=
  LinearEquiv.ofBijective (pullGlob1 (pairRes φ s')) (pairRes_bijective φ s').2.1

def pullHH1 : HH1 s →ₛₗ[σ] HH1 s' :=
  (pairResEquiv1 φ s').symm.toLinearMap.comp (pullHyp1 (pairPull h))

def pullHO1 : HO1 s →ₛₗ[σ] HO1 s' :=
  (pairResEquivO φ s').symm.toLinearMap.comp (pairPull h).pull1

def pullForm : GlobForm s →ₛₗ[σ] GlobForm s' :=
  (pairResEquivForm φ s').symm.toLinearMap.comp (pullGlob1 (pairPull h))

theorem isPull1_pullHH1 (c : HH1 s) : IsPull1 h c (pullHH1 h c) :=
  ((pairResEquiv1 φ s').apply_symm_apply _).symm

theorem isPullO_pullHO1 (c : HO1 s) : IsPullO h c (pullHO1 h c) :=
  ((pairResEquivO φ s').apply_symm_apply _).symm

theorem isPullForm_pullForm (ω : GlobForm s) : IsPullForm h ω (pullForm h ω) :=
  ((pairResEquivForm φ s').apply_symm_apply _).symm

theorem IsPull1.eq_pullHH1 {c : HH1 s} {c' : HH1 s'} (e : IsPull1 h c c') : c' = pullHH1 h c :=
  (existsUnique_isPull1 h c).unique e (isPull1_pullHH1 h c)

theorem IsPullO.eq_pullHO1 {c : HO1 s} {c' : HO1 s'} (e : IsPullO h c c') : c' = pullHO1 h c :=
  (existsUnique_isPullO h c).unique e (isPullO_pullHO1 h c)

theorem IsPullForm.eq_pullForm {ω : GlobForm s} {ω' : GlobForm s'} (e : IsPullForm h ω ω') :
    ω' = pullForm h ω :=
  (existsUnique_isPullForm h ω).unique e (isPullForm_pullForm h ω)

end GlobalTheory.CechDR
