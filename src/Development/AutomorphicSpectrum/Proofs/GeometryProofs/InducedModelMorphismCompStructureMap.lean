module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart
public import Development.WeilBound.CoreStatements.AmpleLineBundles.IntersectionNumberEqLineHeight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem embedding_const_preconnected {F : Type} [Field F] [NumberField F] {m : ℕ} {B : Set (Fin m → ℂ)} (hpre : IsPreconnected B)
    (κ : (Fin m → ℂ) → (F →+* ℂ))
    (hd : ∀ a : 𝓞 F, DifferentiableOn ℂ (fun b => κ b (a : F)) B) {b b' : Fin m → ℂ} (hb : b ∈ B) (hb' : b' ∈ B) :
    κ b = κ b' := by
  have key : ∀ x : 𝓞 F, κ b (x : F) = κ b' (x : F) := by
    intro x
    have hT : IsDiscrete (Set.range fun s : F →+* ℂ => s (x : F)) :=
      (Set.finite_range _).isDiscrete
    have hmaps : Set.MapsTo (fun c => κ c (x : F)) B (Set.range fun s : F →+* ℂ => s (x : F)) :=
      fun c _ => ⟨κ c, rfl⟩
    exact hpre.constant_of_mapsTo hT (hd x).continuousOn hmaps hb hb'
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
  ext x
  exact key x

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjective
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjective
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.CptLift

theorem isCptGen_of_smooth_of_surjective : ∀ (K : Type) [Field K] (X₀ X' : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀)
    (s' : X' ⟶ Spec (CommRingCat.of K)), Smooth s' → ξ' ≫ π = ξ → IsCptGen ξ →
    Function.Surjective (π.stalkMap (genPt ξ')).hom → IsCptGen ξ' := by
  intro K _ X₀ X' Ω _ ξ ξ' π s' hs hc hξ hsurj
  subst hc
  have hd : ∀ x : X', IsDomain (X'.presheaf.stalk x) := fun x =>
    GroundTheory.Arith.SchemeCoh.isDomain_stalk_of_smooth_field s' x
  have hcomp : (Scheme.stalkClosedPointTo (ξ' ≫ π)).hom =
      (Scheme.stalkClosedPointTo ξ').hom.comp (π.stalkMap (genPt ξ')).hom :=
    congrArg (fun t => t.hom) (Scheme.stalkClosedPointTo_comp ξ' π)
  have hbij : Function.Bijective (Scheme.stalkClosedPointTo ξ').hom := by
    have hb := hξ.bij
    rw [hcomp] at hb
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · obtain ⟨a', rfl⟩ := hsurj a
      obtain ⟨b', rfl⟩ := hsurj b
      exact congrArg _ (hb.1 hab)
    · obtain ⟨a, ha⟩ := hb.2 c
      exact ⟨_, ha⟩
  refine ⟨hbij, fun p => ?_⟩
  have hinj : Function.Injective (X'.presheaf.stalkSpecializes p.2).hom := by
    haveI := hd (genPt ξ')
    exact GlobalTheory.PushInv.stalkSpecializes_injective p.2
  intro a b hab
  exact hinj (hbij.1 hab)

end GlobalTheory.CompanionTheory.Ar.CptLift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjectiveStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_of_smooth_surjective : ∀ (K : Type) [Field K] (X₀ X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀) (s' : X' ⟶ Spec (CommRingCat.of K)), Smooth s' → ξ' ≫ π = ξ → IsCptGen ξ → Function.Surjective (π.stalkMap (genPt ξ')).hom → IsCptGen ξ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective | exact GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOfZeroDimVariety
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOfZeroDimVariety
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht

theorem height_eq_intersection_number :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ W : Ideal (MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 1 → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (w : (Σ k, ι k) → L), W = mCoordIdeal w ∧ w ∈ ptsOver L W ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι W 1 ![A] / (degC W : ℝ) = lineHt A L w := by
  exact @CoverDenseAlt.intersection_number_eq_line_height

end GlobalTheory.CompanionTheory.Ar.Ht
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOfZeroDimVarietyStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_of_zero_dim_variety : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ W : Ideal (MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 1 → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (w : (Σ k, ι k) → L), W = mCoordIdeal w ∧ w ∈ ptsOver L W ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι W 1 ![A] / (degC W : ℝ) = lineHt A L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.height_eq_intersection_number | exact GlobalTheory.CompanionTheory.Ar.Ht.height_eq_intersection_number | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.height_eq_intersection_number <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetLeftMem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem gs_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (y : Y) (hy : y ∈ V)
    (a : Γ(X, U)) : gs (𝟙 Y) y V ((f.appLE U V e).hom a) = gs f y U a := by
  have hf : f y ∈ U := e hy
  have key := Y.presheaf.germ_res_apply (homOfLE e) y hy ((f.app U).hom a)
  unfold gs
  rw [dite_eq_left hf]
  split_ifs with h1
  · exact key
  · exact absurd hy h1

theorem gm_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (z : Sp B) :
    gm (spMap f) z ⊤ (unitΓ u) = gm (𝟙 _) z ⊤ (unitΓ (Units.map (f : A →* B) u)) := by
  have key := congrArg (fun g => (CommRingCat.Hom.hom g) (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  unfold gm
  rw [dite_eq_left (show (spMap f) z ∈ (⊤ : (Sp A).Opens) from trivial)]
  rw [dite_eq_left (show (𝟙 (Sp B)) z ∈ (⊤ : (Sp B).Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, pullU, unitΓ, toΓ, MonoidHom.coe_coe, Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply]
  erw [key]
  rfl

theorem val_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u c) r z J = gm r z ⊤ u * val c r z J := by
  have hz : r z ∈ t.PP.L.wchart φ (fun k => J (r ≫ φ k)) := by
    show r z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k)))
    refine Set.mem_iInter.2 fun k => ?_
    have := hJ (r ≫ φ k)
    simpa [Scheme.Hom.comp_apply] using this
  unfold val scaleGenG
  erw [map_mul, gm_res r z _ hz]

theorem val_genPow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (genPowG t φ ε c n) r z J = val c r z J ^ n :=
  map_pow _ _ _

theorem jet_left_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {k : Type} [Field k] (x : Sp k ⟶ X0) {κ : Type} {n : ℕ} (j₀ : t.PP.L.ι)
    (hj₀ : ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀) (ψ : overAt x (Jet k κ n) ⟶ t.G)
    (h : homAt x (jetAug : Jet k κ n →ₐ[k] k) ≫ ψ = 1) (q : Sp (Jet k κ n)) : ψ.left q ∈ t.PP.L.U j₀ := by
  have hsurj : Function.Surjective (jetAug : Jet k κ n →ₐ[k] k).toRingHom :=
    fun c => ⟨algebraMap k _ c, (jetAug : Jet k κ n →ₐ[k] k).commutes c⟩
  have hnil : ∀ a : Jet k κ n, jetAug a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff P = 0 := by
      have : jetAug (Ideal.Quotient.mk _ P : Jet k κ n) = MvPolynomial.aeval (fun _ : κ => (0 : k)) P := rfl
      rw [this] at ha
      simpa [MvPolynomial.aeval_zero'] using ha
    have hP : P ∈ orig k κ := by
      have : P ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set κ)) := by
        rw [MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        by_contra hc
        push_neg at hc
        have hm0 : m = 0 := by ext i; exact hc i (Set.mem_univ i)
        subst hm0
        rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq] at hm
        exact hm h0
      simpa [orig, Set.image_univ] using this
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hP _
  have hrange := range_comap_of_surjective _ _ hsurj
  have huniv : PrimeSpectrum.zeroLocus (RingHom.ker (jetAug : Jet k κ n →ₐ[k] k).toRingHom : Set (Jet k κ n)) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro a ha
    exact mem_nilradical.2 (hnil a (RingHom.mem_ker.1 ha))
  obtain ⟨p, hp⟩ : q ∈ Set.range (PrimeSpectrum.comap (jetAug : Jet k κ n →ₐ[k] k).toRingHom) := by
    rw [hrange, huniv]; trivial
  have hl := congrArg (fun g => Over.Hom.left g) h
  simp only [Over.comp_left] at hl
  have hq : ψ.left q = (1 : overAt x k ⟶ t.G).left p := by
    rw [← hl, ← hp]
    rfl
  rw [hq]
  exact hj₀ (show p ∈ (⊤ : (Sp k).Opens) from trivial)

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLineBundleGauge
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLineBundleGauge
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

abbrev sqU : Over.mk ((GF t x ⊗ GF t x).hom ≫ x) ⟶ t.G ⊗ t.G :=
  lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _))

theorem sqPt_left_fst (a : t.G ⊗ t.G ⟶ t.G) :
    (sqPt t x a).left ≫ pullback.fst t.G.hom x = sqMap t x ≫ a.left :=
  pullback.lift_fst _ _ _

theorem fib_ext {T : Over (Sp k)} {a b : T ⟶ GF t x}
    (h : a.left ≫ pullback.fst t.G.hom x = b.left ≫ pullback.fst t.G.hom x) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w a).trans (Over.w b).symm

theorem sqPt_psum {n : ℕ} (xs : Fin n → (t.G ⊗ t.G ⟶ t.G)) (I : Finset (Fin n)) :
    sqPt t x (psum t.G xs I) = psum (GF t x) (fun i => sqPt t x (xs i)) I := by
  apply fib_ext
  rw [sqPt_left_fst]
  refine Eq.symm (psum_push (isGrpPullback_pullback t.G x) _ xs (sqU t x) (fun i => ?_) I)
  apply Over.OverMorphism.ext
  exact sqPt_left_fst t x (xs i)

theorem sqPt_fst : sqPt t x (fst t.G t.G) = fst (GF t x) (GF t x) := by
  apply fib_ext
  rw [sqPt_left_fst]
  show (sqU t x ≫ fst t.G t.G).left = _
  rw [lift_fst]
  rfl

theorem sqPt_snd : sqPt t x (snd t.G t.G) = snd (GF t x) (GF t x) := by
  apply fib_ext
  rw [sqPt_left_fst]
  show (sqU t x ≫ snd t.G t.G).left = _
  rw [lift_snd]
  rfl

theorem sqPt_comp (b : t.G ⊗ t.G ⟶ t.G) (c : t.G ⟶ t.G) :
    sqPt t x (b ≫ c) = sqPt t x b ≫ (Over.pullback x).map c := by
  apply fib_ext
  rw [sqPt_left_fst, Over.comp_left, Over.comp_left, Category.assoc]
  have A : ((Over.pullback x).map c).left ≫ pullback.fst t.G.hom x = pullback.fst t.G.hom x ≫ c.left :=
    pullback.lift_fst _ _ _
  rw [A, ← Category.assoc (Over.Hom.left (sqPt t x b)), sqPt_left_fst]
  simp only [Category.assoc]

theorem psum_comp_hom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (q : A ⟶ B) [IsMonHom q] {T : Over S} {n : ℕ} (ys : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    psum A ys I ≫ q = psum B (fun i => ys i ≫ q) I :=
  psum_hom (MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b q) ys I

theorem comp_psum {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    {T T' : Over S} (U : T' ⟶ T) {n : ℕ} (ys : Fin n → (T ⟶ B)) (I : Finset (Fin n)) :
    U ≫ psum B ys I = psum B (fun i => U ≫ ys i) I :=
  psum_hom (Formalism.L2.Pj.preHom U) ys I

section Quot

variable {t x} (Q : AbQuot t x)

abbrev qL : GF t x ⊗ GF t x ⟶ Q.tB.G ⊗ Q.tB.G :=
  lift (fst (GF t x) (GF t x) ≫ Q.q) (snd (GF t x) (GF t x) ≫ Q.q)

theorem sqPt_psum_q {n : ℕ} (xs : Fin n → (t.G ⊗ t.G ⟶ t.G)) (ys : Fin n → (Q.tB.G ⊗ Q.tB.G ⟶ Q.tB.G))
    (h : ∀ i, sqPt t x (xs i) ≫ Q.q = qL Q ≫ ys i) (I : Finset (Fin n)) :
    (sqPt t x (psum t.G xs I)).left ≫ Q.q.left = qq Q ≫ (psum Q.tB.G ys I).left := by
  haveI := Q.q_hom
  have e : sqPt t x (psum t.G xs I) ≫ Q.q = qL Q ≫ psum Q.tB.G ys I := by
    rw [sqPt_psum, psum_comp_hom, comp_psum]
    exact congrArg (fun z => psum Q.tB.G z I) (funext h)
  exact congrArg (fun z => z.left) e

theorem sqPt_fst_q : sqPt t x (fst t.G t.G) ≫ Q.q = qL Q ≫ fst Q.tB.G Q.tB.G := by
  rw [sqPt_fst, lift_fst]

theorem sqPt_snd_q : sqPt t x (snd t.G t.G) ≫ Q.q = qL Q ≫ snd Q.tB.G Q.tB.G := by
  rw [sqPt_snd, lift_snd]

theorem sqPt_act_q {b : t.G ⊗ t.G ⟶ t.G} {b' : Q.tB.G ⊗ Q.tB.G ⟶ Q.tB.G}
    (h : sqPt t x b ≫ Q.q = qL Q ≫ b') (a : 𝓞 E) :
    sqPt t x (b ≫ t.act.act a) ≫ Q.q = qL Q ≫ b' ≫ Q.tB.act.act a := by
  rw [sqPt_comp, Category.assoc, Q.act_q, ← Category.assoc, h, Category.assoc]

end Quot

theorem adF_fst (a : 𝓞 E) (i : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2))) :
    adF t x a i ≫ pullback.fst t.G.hom x = sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i := by
  rcases i with I | I
  · exact sqPt_left_fst t x _
  · exact sqPt_left_fst t x _

theorem adF_q {t : SAB H X} {x : Sp k ⟶ X} (Q : AbQuot t x) (a : 𝓞 E) (i : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2))) :
    adF t x a i ≫ Q.q.left = qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)])
      (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i := by
  rcases i with I | I
  · refine sqPt_psum_q Q _ _ (fun i => ?_) I.down
    fin_cases i
    · exact sqPt_fst_q Q
    · exact sqPt_act_q Q (sqPt_snd_q Q) _
  · refine sqPt_psum_q Q _ _ (fun i => ?_) I.down
    fin_cases i
    · exact sqPt_act_q Q (sqPt_fst_q Q) _
    · exact sqPt_snd_q Q

theorem adjunction_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → ∃ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u := by
  intro E _ _ _ H _ _ X t k _ _ p _ _ x Q d d' g gB w hw a wL wB hL hB
  exact GlobalTheory.T.generator_ratio_unit_exists t.G.left Q.tB.G.left (GF t x).left t.PP.L Q.tB.PP.L (pullback.fst t.G.hom x) Q.q.left
    t.PP.isLB Q.tB.PP.isLB w hw _ _ (adF t x a) _ _ _ _ _ (adF_fst t x a) (adF_q Q a)
    (LB.isGen_pullGen _ _ _ _ hL _) (LB.isGen_pullGen _ _ _ _ hB _)

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLineBundleGaugeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_line_bundle_gauge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → ∃ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootHeightDifferenceBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootHeightDifferenceBound
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.CloseHt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

section Places

variable {L : Type} [Field L] [NumberField L]

lemma log_sup_support {ι : Type} [Fintype ι] (x : ι → L) (hx : ∃ i, x i ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (⨆ i, v (x i))).Finite := by
  classical
  obtain ⟨i₀, hi₀⟩ := hx
  haveI : Nonempty ι := ⟨i₀⟩
  have hS : (⋃ i ∈ Finset.univ.filter (fun i => x i ≠ 0),
      Function.mulSupport fun v : FinitePlace L => v (x i)).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun i hi => ?_
    exact FinitePlace.hasFiniteMulSupport (by simpa using hi)
  refine hS.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ i, x i ≠ 0 → v (x i) = 1 := by
    intro i hi
    by_contra h
    exact hn (Set.mem_biUnion (by simpa using hi) h)
  have h2 : ∀ i, v (x i) ≤ 1 := by
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · exact (h1 i hi).le
  have h3 : (⨆ i, v (x i)) = 1 := by
    have hle : (⨆ i, v (x i)) ≤ 1 := ciSup_le h2
    have hge : (1 : ℝ) ≤ ⨆ i, v (x i) := by
      have hb : BddAbove (Set.range fun i => v (x i)) := (Set.finite_range _).bddAbove
      calc (1 : ℝ) = v (x i₀) := (h1 i₀ hi₀).symm
        _ ≤ _ := le_ciSup hb i₀
    exact le_antisymm hle hge
  simp [h3]

lemma block_support {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (a : K → ℝ)
    (x : ∀ k, ι k → L) (hx : ∀ k, ∃ i, x k i ≠ 0) :
    (Function.support fun v : FinitePlace L => ∑ k, a k * Real.log (⨆ i, v (x k i))).Finite := by
  refine (Set.finite_iUnion fun k => log_sup_support (x k) (hx k)).subset fun v hv => ?_
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact Set.mem_iUnion.2 ⟨k, right_ne_zero_of_mul hk⟩

lemma avg_mem (S : (L →+* ℂ) → ℝ) {lo hi : ℝ} (h : ∀ σ, S σ ∈ Set.Icc lo hi) :
    (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ, S σ ∈ Set.Icc lo hi := by
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hc : ∀ r : ℝ, ∑ _σ : L →+* ℂ, r = Module.finrank ℚ L * r := fun r => by
    simp [Finset.card_univ, Embeddings.card L ℂ]
  have h1 : Module.finrank ℚ L * lo ≤ ∑ σ, S σ := by
    rw [← hc]
    exact Finset.sum_le_sum fun σ _ => (h σ).1
  have h2 : ∑ σ, S σ ≤ Module.finrank ℚ L * hi := by
    rw [← hc]
    exact Finset.sum_le_sum fun σ _ => (h σ).2
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hd]
    linarith
  · rw [inv_mul_eq_div, div_le_iff₀ hd]
    linarith

end Places

section Join

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)]

lemma ptHt_sub_join (a₁ : K₁ → ℝ) (a₂ : K₂ → ℝ) (φ₁ : ((Σ k, ι₁ k) → ℂ) → ℝ) (φ₂ : ((Σ k, ι₂ k) → ℂ) → ℝ)
    (L : Type) [Field L] [NumberField L] (z : (Σ k, joinIdx ι₁ ι₂ k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ptHt a₁ φ₁ L (fun p => z (joinInl ι₁ ι₂ p)) - ptHt a₂ φ₂ L (fun p => z (joinInr ι₁ ι₂ p)) =
      ptHt (Sum.elim a₁ (-a₂))
        (fun Z => φ₁ (fun p => Z (joinInl ι₁ ι₂ p)) - φ₂ (fun p => Z (joinInr ι₁ ι₂ p))) L z := by
  unfold ptHt
  rw [← mul_sub]
  congr 1
  have s₁ := block_support (L := L) (ι := ι₁) a₁ (fun k i => z (joinInl ι₁ ι₂ ⟨k, i⟩))
    (fun k => hz (Sum.inl k))
  have s₂ := block_support (L := L) (ι := ι₂) a₂ (fun k i => z (joinInr ι₁ ι₂ ⟨k, i⟩))
    (fun k => hz (Sum.inr k))
  have e : (∑ᶠ v : FinitePlace L, ∑ k, Sum.elim a₁ (-a₂) k * Real.log (⨆ i, v (z ⟨k, i⟩))) =
      (∑ᶠ v : FinitePlace L, ∑ k, a₁ k * Real.log (⨆ i, v (z (joinInl ι₁ ι₂ ⟨k, i⟩)))) -
        ∑ᶠ v : FinitePlace L, ∑ k, a₂ k * Real.log (⨆ i, v (z (joinInr ι₁ ι₂ ⟨k, i⟩))) := by
    rw [← finsum_sub_distrib s₁ s₂]
    refine finsum_congr fun v => ?_
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rfl
  rw [e]
  simp only [Finset.sum_sub_distrib]
  simp only [joinInl, joinInr]
  ring

end Join

section Embed

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {L : Type} [Field L]

lemma aeval_emb (σ : L →+* ℂ) (z : (Σ k, ι k) → L) (f : MRing ι) :
    aeval (fun p => σ (z p)) f = σ (aeval z f) :=
  (comp_aeval_apply (R := ℤ) (f := z) σ.toIntAlgHom f).symm

lemma ptsOver_emb (σ : L →+* ℂ) {P : Ideal (MRing ι)} {z : (Σ k, ι k) → L} (hz : z ∈ ptsOver L P) :
    (fun p => σ (z p)) ∈ ptsOver ℂ P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · rw [aeval_emb, hz.2 f hf, map_zero]

lemma hasVal_emb (σ : L →+* ℂ) {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} {z : (Σ k, ι k) → L} {w : L}
    (h : HasVal y a u z w) : HasVal y a u (fun p => σ (z p)) (σ w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, h0, h1⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩
  · rw [aeval_emb]
    exact (map_ne_zero σ).2 h0
  · rw [aeval_emb, aeval_emb, h1, map_mul]

end Embed

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

lemma line_a (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : (M.line t j).a = (M.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp [RootModel.line, M.x_deg]

lemma coef_eq {M R : RootModel Ψ N} (h : M.kA = R.kA) (lam : Wt Ψ N) (s : ℝ) (j : Option (Ψ × Fin N)) :
    M.coef lam s j = R.coef lam s j := by
  cases j with
  | none => simp [RootModel.coef, h]
  | some r => rfl

lemma sum_abs_coef (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ) :
    ∑ j, |M.coef lam s j| ≤ l1 lam + |s| := by
  rw [Fintype.sum_option, add_comm]
  have h1 : |M.coef lam s none| ≤ |s| := by
    have hk : (1 : ℝ) ≤ M.kA := by exact_mod_cast M.kA_pos
    simp only [RootModel.coef]
    rw [abs_div, Nat.abs_cast]
    exact div_le_self (abs_nonneg s) hk
  have h2 : ∑ r : Ψ × Fin N, |M.coef lam s (some r)| = l1 lam := by
    simp [RootModel.coef, l1, Fintype.sum_prod_type]
  linarith

def lineDefect (M R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    ((Σ k, joinIdx M.ι R.ι k) → ℂ) → ℝ := fun Z =>
  Real.log ((M.line t j).h fun p => Z (joinInl M.ι R.ι p)) -
    Real.log ((R.line 1 j).h fun p => Z (joinInr M.ι R.ι p))

lemma lineHt_sub (M R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) (L : Type) [Field L] [NumberField L]
    (z : (Σ k, joinIdx M.ι R.ι k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    lineHt (M.line t j) L (fun p => z (joinInl M.ι R.ι p)) -
        lineHt (R.line 1 j) L (fun p => z (joinInr M.ι R.ι p)) =
      ptHt (fun k => (joinDeg M R j k : ℝ)) (lineDefect M R t j) L z := by
  unfold lineHt
  rw [ptHt_sub_join _ _ _ _ L z hz]
  have e : (Sum.elim (fun k => ((M.line t j).a k : ℝ)) (-fun k => ((R.line 1 j).a k : ℝ))) =
      fun k => (joinDeg M R j k : ℝ) := by
    funext k
    cases k with
    | inl k => simp [joinDeg, line_a M t j]
    | inr k => simp [joinDeg]
  rw [e]
  rfl

theorem close_ht (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω)
    (u : Option (Ψ × Fin N) → M.Ω) (c t s lo hi : ℝ) (lam : Wt Ψ N) (hC : Close M R i u c)
    (hA : ArchBetween M R i u t lam s lo hi) (L : Type) [Field L] [NumberField L]
    (z) (hz : z ∈ ptsOver L (mCoordIdeal (joinOf M R i))) :
    rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) - rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) ∈
      Set.Icc (lo - (l1 lam + |s|) * c) (hi + (l1 lam + |s|) * c) := by
  obtain ⟨harith, hbir, -, -⟩ := GlobalTheory.T.join_model_points_project Ψ N M R i
  choose val hval0 hval using fun j => hC.unit j L z hz
  have hc : 0 ≤ c := by
    obtain ⟨-, q, m, hq, -, hlog, -, -⟩ := hC.vert none
    have h0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    exact (mul_nonneg_iff_of_pos_left hq').1 (h0.trans hlog)

  let E : Option (Ψ × Fin N) → ℝ := fun j => (Module.finrank ℚ L : ℝ)⁻¹ *
    ∑ σ : L →+* ℂ, (lineDefect M R t j (fun p => σ (z p)) - Real.log ‖σ (val j)‖)
  let D : Option (Ψ × Fin N) → ℝ := fun j => lineHt (M.line t j) L (fun p => z (joinInl M.ι R.ι p)) -
    lineHt (R.line 1 j) L (fun p => z (joinInr M.ι R.ι p))
  have hD : ∀ j, |D j - E j| ≤ c := by
    intro j
    have := GlobalTheory.T.vertical_bound_height_compare (M.K ⊕ R.K) (joinIdx M.ι R.ι) M.Ω (joinOf M R i) (dimFl Ψ N + 1) harith hbir
      (joinDeg M R j) (u j) c (hC.vert j) (lineDefect M R t j) L z hz (val j) (hval0 j) (hval j)
    simp only [D, E]
    rw [lineHt_sub M R t j L z hz.1]
    exact this
  have hE : ∑ j, M.coef lam s j * E j ∈ Set.Icc lo hi := by
    have e : ∑ j, M.coef lam s j * E j = (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ : L →+* ℂ, ∑ j, M.coef lam s j *
        (lineDefect M R t j (fun p => σ (z p)) - Real.log ‖σ (val j)‖) := by
      simp only [E]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [e]
    refine avg_mem _ fun σ => ?_
    exact hA _ (ptsOver_emb σ hz) (fun j => σ (val j)) fun j => hasVal_emb σ (hval j)
  have hsplit : rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) -
      rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) =
      ∑ j, M.coef lam s j * E j + ∑ j, M.coef lam s j * (D j - E j) := by
    unfold rootHt
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← coef_eq hC.kA lam s j]
    simp only [D]
    ring
  have hb : |∑ j, M.coef lam s j * (D j - E j)| ≤ (l1 lam + |s|) * c := by
    calc |∑ j, M.coef lam s j * (D j - E j)| ≤ ∑ j, |M.coef lam s j * (D j - E j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |M.coef lam s j| * c := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hD j) (abs_nonneg _)
      _ = (∑ j, |M.coef lam s j|) * c := by rw [Finset.sum_mul]
      _ ≤ (l1 lam + |s|) * c := mul_le_mul_of_nonneg_right (sum_abs_coef M lam s) hc
  rw [hsplit]
  have := abs_le.1 hb
  exact ⟨by linarith [hE.1, this.1], by linarith [hE.2, this.2]⟩

end GlobalTheory.CompanionTheory.Ar.Ht.CloseHt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootHeightDifferenceBoundStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_height_difference_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (c t s lo hi : ℝ) (lam : Wt Ψ N), Close M R i u c → ArchBetween M R i u t lam s lo hi → ∀ (L : Type) [Field L] [NumberField L], ∀ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) - rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) ∈ Set.Icc (lo - (l1 lam + |s|) * c) (hi + (l1 lam + |s|) * c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht | exact GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionValueOnChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem exists_unitΓ_eq {A : Type} [CommRing A] (u : Γ(Sp A, ⊤)ˣ) : ∃ e : Aˣ, unitΓ e = u := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom u, Units.ext ?_⟩
  exact congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id

theorem val_eq_unit_of_red : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (B : Type) [CommRing B] (p : ℕ) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (Jet B Unit p) ⟶ Y) (j₀ : L.ι), (∀ κ q, (r ≫ φ κ) q ∈ L.U j₀) → (∀ (z' : Sp B) (J' : (Sp B ⟶ X) → L.ι), Good L z' J' → (∀ κ, J' (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) = j₀) → val t (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r) z' J' = 1) → ∃ e₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) e₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ X) → L.ι), Good L z J → (∀ κ, J (r ≫ φ κ) = j₀) → val t r z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
  intro X Y L hL B _ p K _ φ ε t r j₀ h₁ h₂
  have hW : (⊤ : (Sp (Jet B Unit p)).Opens) ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j₀) :=
    fun q _ => Set.mem_iInter.2 fun κ => h₁ κ q
  obtain ⟨e₀, he₀⟩ := exists_unitΓ_eq (res hW (pullU r _ (t.s fun _ => j₀)))
  have key : ∀ (Z : Scheme.{0}) (f : Z ⟶ Sp (Jet B Unit p)) (z : Z),
      gm f z ⊤ (unitΓ e₀) = gm (f ≫ r) z (LB.wchart L φ (fun _ => j₀)) (t.s fun _ => j₀) := by
    intro Z f z
    rw [he₀, gm_res f z hW (Set.mem_univ _)]
    exact gm_pull f r z _ (hW (Set.mem_univ _)) _
  refine ⟨e₀, ?_, ?_⟩
  · have hv : pullU (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) ⊤ (unitΓ e₀) = 1 := by
      apply unit_ext
      intro z' _
      obtain ⟨J', hJ', e⟩ := exists_good L hL z'
        (fun κ => spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) (fun _ => j₀)
        (fun _ _ _ => rfl) (fun κ => h₁ κ _)
      have hv := h₂ z' J' hJ' e
      rw [val_of t _ z' J' (fun _ => j₀) (fun κ => by rw [Category.assoc]; exact e κ), ← key] at hv
      have hp := gm_pull (𝟙 _) (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) z' ⊤ (Set.mem_univ _)
        (unitΓ e₀)
      rw [Category.id_comp] at hp
      rw [map_one]
      exact hp.trans hv
    apply toΓ_inj
    rw [map_one]
    exact (spMap_toΓ _ _).symm.trans (congrArg Units.val hv)
  · intro z J _ hc
    rw [val_of t r z J (fun _ => j₀) hc, key, Category.id_comp]

end GlobalTheory.CompanionTheory.Ar.Coc
end
end
