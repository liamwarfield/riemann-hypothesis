module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import GroundTheory.AutomorphicForms.Reduction
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomothetyLatSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCover
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverO

def counitCoef {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) {G : C' ⥤ C} {H : C ⥤ C'} (adj : G ⊣ H) :
    CoefMap (RingHom.id R) (G ⋙ F) F where
  G := H
  α V := (mp F (adj.counit.app V)).toRingHom
  naturality {V V'} φ b := by
    change mp F (adj.counit.app V') (mp F (G.map (H.map φ)) b) = mp F φ (mp F (adj.counit.app V) b)
    rw [← mp_comp, ← mp_comp]
    have e := adj.counit.naturality φ
    simp only [Functor.comp_map, Functor.id_map] at e
    rw [e]
  smul V r b := by
    change mp F (adj.counit.app V) (r • b) = r • mp F (adj.counit.app V) b
    exact map_smul _ r b

theorem restrict_pull1_bijective_of_adj {R : Type} [CommRing R] {C C' : Type} [Category.{0} C]
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C') (adj : G ⊣ H) :
    Function.Bijective (CoefMap.restrict F G).pull1 := by
  have hl : ∀ c, (counitCoef F adj).pull1 ((CoefMap.restrict F G).pull1 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyOne_comp]
    exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id F) adj.counit (fun T b ↦ rfl) c).trans
      (CoefMap.pullCohomologyOne_id c)
  have hr : ∀ c, (CoefMap.restrict F G).pull1 ((counitCoef F adj).pull1 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyOne_comp]
    refine ((CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.id (G ⋙ F))
      ((counitCoef F adj).comp (CoefMap.restrict F G)) adj.unit (fun T b ↦ ?_) c).symm.trans
      (CoefMap.pullCohomologyOne_id c))
    change mp F (adj.counit.app (G.obj T)) (mp F (G.map (adj.unit.app T)) b) = b
    exact (mp_comp F (G.map (adj.unit.app T)) (adj.counit.app (G.obj T)) b).symm.trans
      ((congrArg (fun ξ ↦ mp F ξ b) (adj.left_triangle_components T)).trans (mp_id F (G.obj T) b))
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

theorem restrict_cover_affine_pull1_bijective (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (J : Type) (U : J → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (OAff s) (Monotone.functor
      (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op).pull1 := by
  let G : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ ⥤ AffOp X := (Monotone.functor
      (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ) (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let Gs : Set Γ(X, T.unop.1) := {f | ∃ j, X.basicOpen f ≤ U j}
    have hG : Ideal.span Gs = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := U j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite Gs).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      have hW : IsAffineOpen (X.basicOpen f) := hT.basicOpen f
      have hWT : X.basicOpen f ≤ T.unop.1 := X.basicOpen_le f
      have hSW : S.unop.1 ≤ X.basicOpen f := by
        have h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          X.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let t : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨⟨_, hW⟩, j, hj⟩
      refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X.affineOpens) ≤ T.unop from hWT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X.affineOpens) from hSW)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ) (S : AffOp X), (G.obj t₁ ⟶ S) →
      (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop ≤ S.unop := leOfHom u.unop
      have hS1 : S.unop ≤ t₁.unop.1 := leOfHom h₁.unop
      have hS2 : S.unop ≤ t₂.unop.1 := leOfHom h₂.unop
      let t₃ : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨S'.unop, j, le_trans (hS'S.trans hS1) hj⟩
      refine ⟨Opposite.op t₃, ⟨(homOfLE (show t₃ ≤ t₁.unop from hS'S.trans hS1)).op⟩,
        ⟨(homOfLE (show t₃ ≤ t₂.unop from hS'S.trans hS2)).op⟩, ⟨𝟙 _⟩⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

theorem restrict_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull1 := by
  intro R _ X s J _ _ U hU hinf hcov
  classical
  haveI := Fintype.ofFinite J
  let B : Type := {V : X.affineOpens // ∃ i, V.1 ≤ (U i).1}
  have hne : ∀ V : B, (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).Nonempty := fun V => by
    obtain ⟨i, hi⟩ := V.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let σ : B → J := fun V => (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).inf' (hne V) id
  let u : J → B := fun i => ⟨U i, i, le_rfl⟩
  have hσ : ∀ V : B, V.1.1 ≤ (U (σ V)).1 := fun V =>
    Finset.inf'_induction (p := fun i => V.1.1 ≤ (U i).1) (hne V) id
      (fun a ha b hb => by rw [hinf]; exact le_inf ha hb) fun i hi => (Finset.mem_filter.1 hi).2
  have gc : GaloisConnection σ u := fun V i =>
    ⟨fun h => (hσ V).trans (hU h), fun h =>
      Finset.inf'_le (s := Finset.univ.filter fun i : J => V.1.1 ≤ (U i).1) (id : J → J)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩
  let incl : Bᵒᵖ ⥤ AffOp X := (Monotone.functor (f := (Subtype.val : B → X.affineOpens)) fun _ _ h ↦ h).op
  have b1 : Function.Bijective (CoefMap.restrict (OAff s) incl).pull1 :=
    restrict_cover_affine_pull1_bijective R X s J (fun i => (U i).1) hcov
  have b2 := restrict_pull1_bijective_of_adj (incl ⋙ OAff s) gc.monotone_u.functor.op
    gc.monotone_l.functor.op gc.adjunction.op
  have e : ∀ c, (CoefMap.restrict (OAff s) hU.functor.op).pull1 c =
      (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op).pull1
        ((CoefMap.restrict (OAff s) incl).pull1 c) := fun c =>
    (CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (CoefMap.pullCohomologyOne_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this

end GlobalTheory.CoverO
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_pull_one_bijective_lattice_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull1 := by
  first | exact @GlobalTheory.CoverO.restrict_bijective | exact GlobalTheory.CoverO.restrict_bijective | (intros; apply GlobalTheory.CoverO.restrict_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetDiagNormOne
open NumberField MeasureTheory Matrix
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

noncomputable section

namespace GlobalTheory.SiegelDiagNormOne

theorem exists_siegelSet_diag_normOne : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ ω : Set (AdelicGLn.AdelicGL K n),
    IsCompact ω ∧ ω ⊆ ((adelicBorel (K := K) (n := n) : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)) ∧
    (∀ b ∈ ω, ∀ i, ∃ u : IdeleGroup K, (b : Matrix (Fin n) (Fin n) 𝔸[K]) i i = u ∧ (ideleModule K u : ℝ) = 1) ∧
    ∃ t : ℝ, 0 < t ∧ ∀ g : AdelicGLn.AdelicGL K n, ∃ γ : GL (Fin n) K,
      AdelicGLn.diagonal K n γ * g ∈ Reduction.siegelSet n ω t := by
  intro K _ _ n
  classical
  obtain ⟨t₀, ht₀, hred⟩ := exists_reduced (K := K)
  obtain ⟨D, hD, hDmem⟩ := exists_isCompact_add_mem (K := K)
  obtain ⟨S, hS, hS1, hSmem⟩ := exists_isCompact_normOneSubgroup K
  set d : ℕ := Module.finrank ℚ K with hd
  have hd0 : 0 < d := Module.finrank_pos
  set FN : Set (AdelicGLn.AdelicGL K n) :=
    unitriangularGL n '' (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => D) with hFN
  set FT : Set (AdelicGLn.AdelicGL K n) := diagUnits n '' (Set.pi Set.univ fun _ => S) with hFT
  have hFNc : IsCompact FN := (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hD).image
    (continuous_unitriangularGL n)
  have hFTc : IsCompact FT := (isCompact_univ_pi fun _ => hS).image (continuous_diagUnits n)
  refine ⟨FN * FT, hFNc.mul hFTc, ?_, ?_, t₀ ^ ((d : ℝ)⁻¹), Real.rpow_pos_of_pos ht₀ _, fun g => ?_⟩
  · rintro _ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, -, rfl⟩, rfl⟩
    exact mul_mem (unitriangularGL_mem_adelicBorel n p) (diagUnits_mem_adelicBorel n e)
  · rintro _ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, he, rfl⟩, rfl⟩ i
    refine ⟨e i, ?_, ?_⟩
    · rw [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal]
      change unitriangular p i i * _ = _
      simp [unitriangular]
    · have h1 := hS1 (he i (Set.mem_univ _))
      rw [normOneSubgroup, SetLike.mem_coe, MonoidHom.mem_ker] at h1
      rw [h1]
      rfl
  obtain ⟨γ, b, hb, k, hk, hγ, hratio⟩ := hred n g
  set B : Matrix (Fin n) (Fin n) 𝔸[K] := (b : Matrix (Fin n) (Fin n) 𝔸[K]) with hB
  set dU : Fin n → IdeleGroup K := fun i => (isUnit_apply_self_of_mem_adelicBorel hb i).unit
    with hdU
  have hdUv : ∀ i, ((dU i : IdeleGroup K) : 𝔸[K]) = B i i := fun i => IsUnit.unit_spec _
  set r : Fin n → ℝ := fun i => (ideleModule K (dU i) : ℝ) ^ ((d : ℝ)⁻¹) with hr
  have hrpos : ∀ i, 0 < r i := fun i => Real.rpow_pos_of_pos (ideleModule K (dU i)).2 _
  have hrd : ∀ i, r i ^ d = ideleModule K (dU i) := fun i =>
    Real.rpow_inv_natCast_pow (ideleModule K (dU i)).2.le hd0.ne'
  have heqmod : ∀ i, ideleModule K (dU i) = ideleModule K (posIdele (r i) (hrpos i)) := fun i =>
    Subtype.ext (by rw [ideleModule_posIdele, ← hd, hrd i])
  have hnorm : ∀ i, dU i * (posIdele (r i) (hrpos i))⁻¹ ∈ normOneSubgroup K := fun i => by
    rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, heqmod i, mul_inv_cancel]
  choose c hc using fun i => hSmem _ (hnorm i)
  set σ : Fin n → IdeleGroup K :=
    fun i => IdeleGroup.diagonal K (c i) * (dU i * (posIdele (r i) (hrpos i))⁻¹) with hσ
  set e : Fin n → IdeleGroup K := fun i => IdeleGroup.diagonal K (c i) with he
  set δA : AdelicGLn.AdelicGL K n := diagUnits n e with hδA
  have hδ : AdelicGLn.diagonal K n (diagUnits n c) = δA := diagonal_diagUnits n c
  set u : AdelicGLn.AdelicGL K n := δA * b * (diagUnits n dU)⁻¹ * δA⁻¹ with hu
  have hu_apply : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝔸[K]) i j =
      (e i : 𝔸[K]) * B i j * (((dU j)⁻¹ : IdeleGroup K) : 𝔸[K]) * (((e j)⁻¹ : IdeleGroup K) : 𝔸[K]) := by
    intro i j
    rw [hu, ← map_inv, ← map_inv]
    simp only [Units.val_mul, hδA, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.inv_apply]
    rfl
  have huu : IsUnitriangular (u : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hu_apply, show B i j = 0 from hb hij]
      simp
    · rw [hu_apply, ← hdUv i]
      calc (e i : 𝔸[K]) * (dU i : 𝔸[K]) * (((dU i)⁻¹ : IdeleGroup K) : 𝔸[K]) *
            (((e i)⁻¹ : IdeleGroup K) : 𝔸[K])
          = ((e i * dU i * (dU i)⁻¹ * (e i)⁻¹ : IdeleGroup K) : 𝔸[K]) := by simp [Units.val_mul]
        _ = 1 := by rw [mul_inv_cancel_right, mul_inv_cancel, Units.val_one]
  obtain ⟨ν, hν, hνD⟩ := exists_unitriangular_mul_mem hDmem n _ huu
  set νGL : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero ν
    (by rw [hν.det_eq_one]; exact one_ne_zero) with hνGL
  set νA : AdelicGLn.AdelicGL K n := AdelicGLn.diagonal K n νGL with hνA
  have hνAmat : (νA : Matrix (Fin n) (Fin n) 𝔸[K]) = ν.map (algebraMap K 𝔸[K]) := rfl
  obtain ⟨d₀, hd₀⟩ : D.Nonempty := let ⟨k₀, hk₀⟩ := hDmem 0; ⟨_, hk₀⟩
  set p : Fin n → Fin n → 𝔸[K] := fun i j =>
    if i < j then ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) i j else d₀
    with hp
  have hpD : p ∈ Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => D := by
    intro i _ j _
    simp only [hp]
    split_ifs with hij
    · rw [Units.val_mul, hνAmat]
      exact hνD i j hij
    · exact hd₀
  have hνu : νA * u = unitriangularGL n p := by
    refine Units.ext ?_
    have h1 : IsUnitriangular ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
      rw [Units.val_mul, hνAmat]
      exact IsUnitriangular.mul ⟨fun i j hij => by simp [hν.1 hij],
        fun i => by simp [hν.2 i]⟩ huu
    rw [h1.eq_unitriangular]
    change unitriangular _ = unitriangular p
    ext i j
    simp only [unitriangular, of_apply, hp]
    split_ifs <;> rfl
  have hdiag : δA * diagUnits n dU = diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) := by
    rw [hδA, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp [hσ, he, mul_assoc]
  refine ⟨νGL * diagUnits n c * γ, unitriangularGL n p * diagUnits n σ,
    ⟨_, ⟨p, hpD, rfl⟩, _, ⟨σ, fun i _ => hc i, rfl⟩, rfl⟩,
    diagUnits n (fun i => posIdele (r i) (hrpos i)), ⟨r, hrpos, fun i j hij => ?_, rfl⟩, k, hk, ?_⟩
  · have h := hratio i j hij
    rw [← hdUv j, ← hdUv i, adeleAbs_units, adeleAbs_units, ← hrd i, ← hrd j] at h
    have hrj := (hrpos j).le
    have hri := (hrpos i).le
    have ht : (t₀ ^ ((d : ℝ)⁻¹)) ^ d = t₀ := Real.rpow_inv_natCast_pow ht₀.le hd0.ne'
    have htn : 0 ≤ t₀ ^ ((d : ℝ)⁻¹) := (Real.rpow_pos_of_pos ht₀ _).le
    rw [← pow_le_pow_iff_left₀ (mul_nonneg htn hrj) hri hd0.ne', mul_pow, ht]
    exact h
  · have h1 : δA * b = u * (δA * diagUnits n dU) := by
      rw [hu]; group
    calc AdelicGLn.diagonal K n (νGL * diagUnits n c * γ) * g
        = νA * δA * (AdelicGLn.diagonal K n γ * g) := by
          rw [map_mul, map_mul, hδ, ← hνA]; simp only [mul_assoc]
      _ = νA * (δA * b) * k := by rw [hγ]; simp only [mul_assoc]
      _ = νA * u * (δA * diagUnits n dU) * k := by rw [h1]; simp only [mul_assoc]
      _ = (νA * u) * diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) * k := by
          rw [hdiag]; simp only [mul_assoc]
      _ = _ := by rw [hνu]

end GlobalTheory.SiegelDiagNormOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.EulerLocVol

noncomputable def invPowHom (i : ℕ) : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ i)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_pow, mul_inv]

theorem inv_zeta_le_prod_primes : ∀ (i : ℕ), 2 ≤ i → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i)⁻¹ ≤ ∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹) := by
  intro i hi P hP
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
    simpa using this
  have hs' : Summable (invPowHom i) := by
    have := Real.summable_one_div_nat_pow.2 (by omega : 1 < i)
    simpa [invPowHom] using this
  have hlt : ∀ {p : ℕ}, p.Prime → ‖invPowHom i p‖ < 1 := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ i := one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega)
    simp only [invPowHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, norm_pow, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ h1
  have hE := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hlt P).2
  have hfilt : P.filter Nat.Prime = P := Finset.filter_true_of_mem hP
  rw [hfilt] at hE
  have hfac : ∀ p ∈ P, 0 < 1 - ((p : ℝ) ^ i)⁻¹ := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ i := one_lt_pow₀ (by exact_mod_cast (hP p hp).one_lt) (by omega)
    exact sub_pos.2 (inv_lt_one_of_one_lt₀ h1)
  have hpos : 0 < ∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹) := Finset.prod_pos hfac
  have hle : ∏ p ∈ P, (1 - invPowHom i p)⁻¹ ≤ ∑' n : ℕ, invPowHom i n := by
    rw [← hE.tsum_eq]
    exact Summable.tsum_subtype_le (⇑(invPowHom i)) _ (fun n => by change 0 ≤ ((n : ℝ) ^ i)⁻¹; positivity) hs'
  have hz : ∑' n : ℕ, invPowHom i n = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    rw [hs'.tsum_eq_zero_add]
    simp [invPowHom, show i ≠ 0 by omega]
  rw [hz, Finset.prod_inv_distrib] at hle
  simp only [invPowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hle
  calc (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i)⁻¹ ≤ ((∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹))⁻¹)⁻¹ :=
        inv_anti₀ (inv_pos.2 hpos) hle
    _ = _ := inv_inv _

theorem le_locFactor_of_not_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    ¬ (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  intro E _ _ _ r v hr hnp
  let _ : Field (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hc : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h := GlobalTheory.FiniteOrders.card_specialLinearGroup hc (Fin r) (Fintype.card_fin r) hr
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  unfold locFactor resOrder
  rw [if_neg hnp]
  have h' : (Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) h
    push_cast at this
    exact this
  rw [h', mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]

theorem tprod_locFactor_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r →
    Multipliable (locFactor E r) → 0 < ∏' v, locFactor E r v ∧
      (∏' v, locFactor E r v)⁻¹ ≤ (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E := by
  intro E _ _ _ r hr hm
  let g : ℝ → ℝ := fun x => ∏ i ∈ Finset.Icc 2 r, (1 - (x ^ i)⁻¹)
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZdef
  have hzeta : ∀ i ∈ Finset.Icc 2 r, 1 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
      simpa using this
    have := hs.le_tsum 0 (fun j _ => by positivity)
    simpa using this
  have hZ : 0 < Z := Finset.prod_pos fun i hi => lt_of_lt_of_le one_pos (hzeta i hi)
  have hf : fdeg E = Module.finrank ℚ (maximalRealSubfield E) := by
    have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
      Algebra.IsQuadraticExtension.finrank_eq_two _ _
    unfold fdeg
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E), h2]
    omega
  have g_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x := fun x hx =>
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))
  have g_le_one : ∀ x : ℝ, 1 ≤ x → g x ≤ 1 := fun x hx =>
    Finset.prod_le_one₀ (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_self _ (by positivity)
  have g_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → g x ≤ g y := fun x y hx hxy =>
    Finset.prod_le_prod₀ (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_sub_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hxy i)) _
  have hloc : ∀ v, g (Ideal.absNorm v.asIdeal) ≤ locFactor E r v := by
    intro v
    by_cases hp : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime
    · exact GlobalTheory.T.local_factor_lower_bound E r v (by omega) hp
    · exact le_locFactor_of_not_prime E r v (by omega) hp
  let pv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow
  have hN : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      (pv v).Prime ∧ pv v ≤ Ideal.absNorm v.asIdeal := by
    intro v
    have hp := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime v
    obtain ⟨f, hfv⟩ := ReciprocityTheory.Neutral.Bridge.absNorm_eq_ratPrimeBelow_pow v
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hf0 : f ≠ 0 := by rintro rfl; rw [pow_zero] at hfv; exact h1 hfv
    refine ⟨hp, ?_⟩
    rw [hfv]
    exact Nat.le_self_pow hf0 _
  have key : ∀ s : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
      (Z ^ fdeg E)⁻¹ ≤ ∏ v ∈ s, locFactor E r v := by
    intro s
    set T := s.image pv
    have hp1 : ∀ p ∈ T, (1 : ℝ) ≤ p := by
      intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact_mod_cast (hN v).1.one_lt.le
    have s1 : ∏ v ∈ s, g (pv v) ≤ ∏ v ∈ s, locFactor E r v := by
      refine Finset.prod_le_prod₀ (fun v _ => g_nonneg _ (by exact_mod_cast (hN v).1.one_lt.le))
        fun v _ => (g_mono _ _ (by exact_mod_cast (hN v).1.one_lt.le) (by exact_mod_cast (hN v).2)).trans (hloc v)
    have s2 : ∏ v ∈ s, g (pv v) = ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      rw [Finset.prod_comp (fun p : ℕ => g p) pv]
    have s3 : ∏ p ∈ T, g p ^ fdeg E ≤ ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      refine Finset.prod_le_prod₀ (fun p hp => pow_nonneg (g_nonneg _ (hp1 p hp)) _) fun p hp => ?_
      refine pow_le_pow_of_le_one (g_nonneg _ (hp1 p hp)) (g_le_one _ (hp1 p hp)) ?_
      rw [hf]
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le id Function.injective_id s (pv v) (hN v).1
    have s4 : Z⁻¹ ≤ ∏ p ∈ T, g p := by
      rw [Finset.prod_comm, hZdef, ← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => ?_
      refine inv_zeta_le_prod_primes i (Finset.mem_Icc.1 hi).1 T fun p hp => ?_
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact (hN v).1
    calc (Z ^ fdeg E)⁻¹ = (Z⁻¹) ^ fdeg E := (inv_pow Z _).symm
      _ ≤ (∏ p ∈ T, g p) ^ fdeg E := pow_le_pow_left₀ (by positivity) s4 _
      _ = ∏ p ∈ T, g p ^ fdeg E := (Finset.prod_pow _ _ _).symm
      _ ≤ _ := s3
      _ = _ := s2.symm
      _ ≤ _ := s1
  have hle : (Z ^ fdeg E)⁻¹ ≤ ∏' v, locFactor E r v :=
    ge_of_tendsto hm.hasProd (Filter.Eventually.of_forall key)
  have hpos : 0 < (Z ^ fdeg E)⁻¹ := by positivity
  refine ⟨hpos.trans_le hle, ?_⟩
  calc (∏' v, locFactor E r v)⁻¹ ≤ ((Z ^ fdeg E)⁻¹)⁻¹ := inv_anti₀ hpos hle
    _ = Z ^ fdeg E := inv_inv _

end GlobalTheory.EulerLocVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBoundStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_product_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r → Multipliable (locFactor E r) → 0 < ∏' v, locFactor E r v ∧ (∏' v, locFactor E r v)⁻¹ ≤ (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E := by
  first | exact @GlobalTheory.EulerLocVol.tprod_locFactor_bound | exact GlobalTheory.EulerLocVol.tprod_locFactor_bound | (intros; apply GlobalTheory.EulerLocVol.tprod_locFactor_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfSplitInjectiveFgProjectiveConstantRan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfSplitInjectiveFgProjectiveConstantRan
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem bijective_of_split_of_FP : ∀ (R : Type) [CommRing R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ), FP R M n → FP R N n → ∀ (f : M →ₗ[R] N) (r : N →ₗ[R] M), (∀ x, r (f x) = x) → Function.Bijective f := by
  intro R _ M N _ _ _ _ n hM hN f r hrf
  obtain ⟨hMf, hMp, hMr⟩ := hM
  obtain ⟨hNf, hNp, hNr⟩ := hN
  have hinj : Function.Injective f := fun a b h => by
    have := congrArg r h; rwa [hrf, hrf] at this
  let K := LinearMap.ker r
  let π : N →ₗ[R] K := LinearMap.codRestrict K (LinearMap.id - f ∘ₗ r) (fun x => by
    show r (x - f (r x)) = 0
    simp [hrf])
  have hπ : ∀ k : K, π (k : N) = k := fun k => by
    ext; simp [π, LinearMap.mem_ker.1 k.2]
  haveI : Module.Finite R K := Module.Finite.of_surjective π (fun k => ⟨k, hπ k⟩)
  haveI : Module.Projective R K := Module.Projective.of_split K.subtype π (by ext k; simp [hπ])
  let e : N ≃ₗ[R] M × K :=
    { toFun := fun x => (r x, π x)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp
      invFun := fun p => f p.1 + (p.2 : N)
      left_inv := fun x => by simp [π]
      right_inv := fun p => by
        obtain ⟨m, k⟩ := p
        have hk : r (k : N) = 0 := k.2
        ext
        · simp [hrf, hk]
        · simp [π, hrf, hk] }
  have hK : Module.rankAtStalk (R := R) K = 0 := by
    have h1 := Module.rankAtStalk_eq_of_equiv e
    rw [Module.rankAtStalk_prod] at h1
    funext p
    have h2 := congrFun h1 p
    simp only [Pi.add_apply, hMr p, hNr p] at h2
    simp only [Pi.zero_apply]; omega
  haveI : Subsingleton K := Module.rankAtStalk_eq_zero_iff_subsingleton.1 hK
  refine ⟨hinj, fun y => ⟨r y, ?_⟩⟩
  have : π y = 0 := Subsingleton.elim _ _
  have h3 := congrArg Subtype.val this
  simp [π, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfSplitInjectiveFgProjectiveConstantRanStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank : ∀ (R : Type) [CommRing R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ), FP R M n → FP R N n → ∀ (f : M →ₗ[R] N) (r : N →ₗ[R] M), (∀ x, r (f x) = x) → Function.Bijective f := by
  first | exact @GlobalTheory.AbCoh.bijective_of_split_of_FP | exact GlobalTheory.AbCoh.bijective_of_split_of_FP | (intros; apply GlobalTheory.AbCoh.bijective_of_split_of_FP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjective
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

namespace GlobalTheory.FieldDimCoheight

theorem coheight_add_dim_closure_eq (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp F) [LocallyOfFiniteType p] (z : X) :
    (Order.coheight z : WithBot ℕ∞) + topologicalKrullDim (closure ({z} : Set X)) =
      topologicalKrullDim X := by
  refine le_antisymm ?_ ?_
  · rw [add_comm]
    haveI : QuasiSober (closure ({z} : Set X)) :=
      isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
    exact DimCodim.dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective _
      fun w => Order.coheight_anti (specializes_iff_mem_closure.2 w.2)
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(X, U), hU.fromSpec P = z := by
    have : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hzU
    exact this
  let φ := Spec.preimage (hU.fromSpec ≫ p)
  have hφ : Spec.map φ = hU.fromSpec ≫ p := Spec.map_preimage _
  let _ : Algebra F Γ(X, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have : Nonempty (Spec Γ(X, U)) := ⟨P⟩
  have hA : ringKrullDim Γ(X, U) = topologicalKrullDim X := by
    rw [← OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion F X _ p hU.fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
  have h2 := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F) P.asIdeal
  let x : Spec Γ(X, U) := P
  have eS := (asIso (hU.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(X, U) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight z := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight]
    rw [← hP]
  have h3 : ringKrullDim (Γ(X, U) ⧸ P.asIdeal) ≤ topologicalKrullDim (closure ({z} : Set X)) := by
    rw [← topologicalKrullDim_range_inter_closure_eq (B := Γ(X, U)) hU.fromSpec P, hP]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [← hA, ← h2, hPh]
  exact add_le_add le_rfl h3

theorem eq_one_iff_of_add_eq {c : ℕ∞} {t : WithBot ℕ∞} {e : ℕ}
    (h : (c : WithBot ℕ∞) + t = (e + 1 : ℕ)) : c = 1 ↔ t = e := by
  induction t using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h; exact absurd h.symm (WithBot.natCast_ne_bot _)
  | coe t =>
    have h' : c + t = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have hc : c ≠ ⊤ := by rintro rfl; rw [top_add] at h'; exact ENat.natCast_ne_top _ h'.symm
    have ht : t ≠ ⊤ := by rintro rfl; rw [add_top] at h'; exact ENat.natCast_ne_top _ h'.symm
    lift c to ℕ using hc
    lift t to ℕ using ht
    have h'' : c + t = e + 1 := by exact_mod_cast h'
    constructor
    · intro h1
      have : c = 1 := by exact_mod_cast h1
      have : t = e := by omega
      exact_mod_cast this
    · intro h1
      have : t = e := by exact_mod_cast h1
      have : c = 1 := by omega
      exact_mod_cast this

theorem coheight_eq_one_iff : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F)
    (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ z : X,
    Order.coheight z = 1 ↔ topologicalKrullDim (closure ({z} : Set X)) = e := by
  intro F _ X _ p e hp hd z
  have : IsProper p := by
    obtain ⟨N, c, hc, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  exact eq_one_iff_of_add_eq ((coheight_add_dim_closure_eq F X p z).trans hd)

end GlobalTheory.FieldDimCoheight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.SplitPair

variable {E : Type} [Field E] [NumberField E]

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m) (h' : ¬ x ≤ WithZero.exp (m - 1)) :
    x = WithZero.exp m := by
  refine le_antisymm h (not_lt.1 fun h1 => h' ?_)
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, sub_add_cancel]
  exact h1

theorem exists_int_cong (P : HeightOneSpectrum (𝓞 E)) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ b : 𝓞 E, Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap E P).mem_nhds (OrderUnits.ball_mem_nhds P 1 z)
  have hk' : Valued.v (algebraMap E (P.adicCompletion E) k - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hk
  have hval : ∀ x : E, Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x
  have h1 : P.valuation E k ≤ 1 := by
    have h2 : WithZero.exp (-((1 : ℕ) : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have := Valuation.map_add_le _ (hk'.trans h2) hz
    rwa [sub_add_cancel, hval] at this
  obtain ⟨b, hb⟩ := P.exists_valuation_sub_lt_of_integer h1 (Units.mk0 (WithZero.exp (-((1 : ℕ) : ℤ))) WithZero.exp_ne_zero)
  refine ⟨b, ?_⟩
  rw [← hval, map_sub] at hb
  have := Valuation.map_add_le _ hb.le hk'
  rw [sub_add_sub_cancel] at this
  exact this

def unitF (a : OF E) (ha : a ≠ 0) : (maximalRealSubfield E)ˣ :=
  Units.mk0 (a : maximalRealSubfield E) (fun h => ha (RingOfIntegers.ext h))

def locF (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (P.adicCompletion E)ˣ :=
  Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) (unitF a ha))

theorem coe_locF (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (locF P a ha : P.adicCompletion E) = iota a P := rfl

theorem loc_mul_loc {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} {P P' : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (hP' : Over P' v) (hne : P ≠ P') (h2 : ∀ R, Over R v → R = P ∨ R = P') (a : OF E) (ha : a ≠ 0) :
    χ.loc P (locF P a ha) * χ.loc P' (locF P' a ha) = 1 := by
  classical
  have hS : Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v = {P, P'} := by
    ext R
    rw [mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨h2 R, ?_⟩
    rintro (rfl | rfl)
    · exact hP
    · exact hP'
  have h := hF.1 v (unitF a ha)
  unfold Formalism.L2.Host.HChar.resFin at h
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h
  exact h

theorem unrAt_and_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (v : HeightOneSpectrum (OF E))
    (P P' : HeightOneSpectrum (𝓞 E)), TrivOnF χ → Splits v → Over P v → Over P' v → P ≠ P' → LevelLe χ P' 1 → UnrAt χ P →
    UnrAt χ P' ∧ val χ P' = (val χ P)⁻¹ := by
  intro E _ _ _ χ v P P' hF hs hP hP' hne hlev hun
  obtain ⟨h2, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  have hmul := loc_mul_loc hF hP hP' hne (h2 P P' hP hP' hne)
  have hval : ∀ R, Over R v → ∀ (n : ℕ) (a : OF E), a ∈ v.asIdeal ^ n → a ∉ v.asIdeal ^ (n + 1) →
      Valued.v (iota a R) = WithZero.exp (-(n : ℤ)) := fun R hR n a h h' => by
    refine eq_exp_of_le (val_iota_le_of_mem hR n h) fun h3 => h' ?_
    rw [← (hef R hR).2.1, ← val_iota_le_iff]
    convert h3 using 2
    push_cast; ring
  have hun' : UnrAt χ P' := by
    intro u hu
    have hu1 : Valued.v (u : P'.adicCompletion E) = 1 := hu
    obtain ⟨b, hb⟩ := exists_int_cong P' u hu1.le
    obtain ⟨a, ha⟩ := (hef P' hP').2.2 b
    have h3 := OrderUnits.val_int_le P' 1 _ (by simpa using ha)
    have h4 : Valued.v (iota a P' - u) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      rw [map_sub (algebraMap (𝓞 E) E), map_sub (algebraMap E (Af E)), sub_coord] at h3
      have := Valuation.map_sub_le _ hb h3
      rw [sub_sub_sub_cancel_left] at this
      exact this
    have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h5 : Valued.v (iota a P') = 1 := by
      rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ h4.trans_lt hlt), hu1]
    have hav : a ∉ v.asIdeal ^ (0 + 1) := fun h => (h5 ▸ val_iota_le_of_mem hP' 1 h).not_gt hlt
    have ha0 : a ≠ 0 := fun h => hav (h ▸ zero_mem _)
    have h6 : χ.loc P (locF P a ha0) = 1 := hun _ (by
      show Valued.v (iota a P) = 1
      simpa using hval P hP 0 a (by simp) hav)
    have h7 := hmul a ha0
    rw [h6, one_mul] at h7
    have h8 : χ.loc P' (locF P' a ha0 / u) = 1 := by
      refine hlev _ ?_ ?_
      · show Valued.v ((locF P' a ha0 / u : (P'.adicCompletion E)ˣ) : P'.adicCompletion E) = 1
        rw [Units.val_div_eq_div_val, map_div₀, coe_locF, h5, hu1, div_one]
      · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, coe_locF]
        exact h4
    rw [map_div, div_eq_one, h7] at h8
    exact h8.symm
  refine ⟨hun', ?_⟩
  obtain ⟨a, ha, ha'⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  have ha0 : a ≠ 0 := fun h => ha' (h ▸ zero_mem _)
  have h7 := hmul a ha0
  have hunif : ∀ R, Over R v → Formalism.L2.Host.IsUnifAt R (locF R a ha0) := fun R hR => by
    show Valued.v (iota a R) = WithZero.exp (-1 : ℤ)
    simpa using hval R hR 1 a ha ha'
  rw [χ.val_eq hun _ (hunif P hP), χ.val_eq hun' _ (hunif P' hP')] at h7
  exact eq_inv_of_mul_eq_one_right h7

end GlobalTheory.CMVal.Euler.SplitPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPairStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_inverse_split_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (v : HeightOneSpectrum (OF E)) (P P' : HeightOneSpectrum (𝓞 E)), TrivOnF χ → Splits v → Over P v → Over P' v → P ≠ P' → LevelLe χ P' 1 → UnrAt χ P → UnrAt χ P' ∧ val χ P' = (val χ P)⁻¹ := by
  first | exact @GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val | exact GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val | (intros; apply GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoeth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoeth
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isLocallyNoetherian_of_isQProjOver_noeth :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (f : X ⟶ Sp R),
      IsQProjOver f → IsLocallyNoetherian X := by
  intro R _ _ X f h
  obtain ⟨N, i, hi, -, e⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  have : LocallyOfFiniteType f := by
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  exact LocallyOfFiniteType.isLocallyNoetherian f

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoethStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsQProjOver f → IsLocallyNoetherian X := by
  first | exact @GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | exact GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | (intros; apply GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallAevalLineVanishingIdealIff
set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

theorem aeval_smul_of_isHomogeneous {k K : Type} [Field k] [Field K] [Algebra k K] {N d : ℕ}
    {g : MvPolynomial (Fin N) k} (hg : g.IsHomogeneous d) (t : K) (z : Fin N → K) :
    aeval (t • z) g = t ^ d * aeval z g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h := hg (mem_support_iff.1 hs)
  have hd : ∑ i, s i = d := by
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring



end GlobalTheory.ChowHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClosedFormClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClosedFormClass
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHH1_clAll : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (hc : Closed1 (OAff s) = ⊤) (hc' : Closed1 (OAff s') = ⊤) (w : GlobForm s), pullHH1 h (clAll (OAff s) hc w) = clAll (OAff s') hc' (GlobalTheory.CechDR.pullForm h w) := by
  intro R R' _ _ X X' s s' σ φ h hc hc' w
  let ω : ClosedForm s := ⟨w, by rw [show ClosedForm s = ⊤ from hc]; exact Submodule.mem_top⟩
  let ω' : ClosedForm s' := ⟨GlobalTheory.CechDR.pullForm h w, by rw [show ClosedForm s' = ⊤ from hc']; exact Submodule.mem_top⟩
  have e : IsPull1 h (clForm s ω) (clForm s' ω') := IsPullForm.cl (isPullForm_pullForm h w)
  have k : clAll (OAff s) hc w = clForm s ω := rfl
  have k' : clAll (OAff s') hc' (GlobalTheory.CechDR.pullForm h w) = clForm s' ω' := rfl
  rw [k, k']
  exact e.eq_pullHH1.symm

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClosedFormClassStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_closed_form_class : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (hc : Closed1 (OAff s) = ⊤) (hc' : Closed1 (OAff s') = ⊤) (w : GlobForm s), pullHH1 h (clAll (OAff s) hc w) = clAll (OAff s') hc' (GlobalTheory.CechDR.pullForm h w) := by
  first | exact @GlobalTheory.AbCoh.pullHH1_clAll | exact GlobalTheory.AbCoh.pullHH1_clAll | (intros; apply GlobalTheory.AbCoh.pullHH1_clAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply
noncomputable section

open NumberField

namespace GlobalTheory.HeckePoisson

variable {K : Type} [Field K] [NumberField K] {I : Type}

def embA (φ : I → K →+* ℂ) : 𝓞 K →+ EuclideanSpace ℂ I where
  toFun α := WithLp.toLp 2 (GlobalTheory.HeckeTheta.emb φ (α : K))
  map_zero' := by ext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by ext i; simp [GlobalTheory.HeckeTheta.emb]

def lat (φ : I → K →+* ℂ) (M : Ideal (𝓞 K)) : Submodule ℤ (EuclideanSpace ℂ I) :=
  AddSubgroup.toIntSubmodule (M.toAddSubgroup.map (embA φ))

theorem embA_apply (φ : I → K →+* ℂ) (α : 𝓞 K) (i : I) : embA φ α i = φ i (α : K) := rfl

theorem mem_lat {φ : I → K →+* ℂ} {M : Ideal (𝓞 K)} {x : EuclideanSpace ℂ I} :
    x ∈ lat φ M ↔ ∃ μ ∈ M, embA φ μ = x := by
  show x ∈ M.toAddSubgroup.map (embA φ) ↔ _
  rw [AddSubgroup.mem_map]
  rfl

def kappa [Fintype I] (n : I → ℤ) : ℂ := ((2 : ℂ) ^ Fintype.card I)⁻¹ * (-Complex.I) ^ (∑ i, (n i).natAbs)

end GlobalTheory.HeckePoisson
end
end
