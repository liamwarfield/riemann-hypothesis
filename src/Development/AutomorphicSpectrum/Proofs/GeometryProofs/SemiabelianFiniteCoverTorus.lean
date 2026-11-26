module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectors
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.StratumGenericTorsionPoints
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CoordinateMapFiniteType

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TwoTorsionRankBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.ToricTorsionRankBounds

theorem card_toric_torsion (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    (E : TorusExtension G) (N : ℕ) (hN : (N : k) ≠ 0) :
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ E.i} =
      N ^ @Module.finrank ℤ E.X _ E.addCommGroup.toAddCommMonoid _ := by
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.i_hom
  have hk := E.isKernel
  obtain ⟨e⟩ := GlobalTheory.SemiAbTorsionCount.nonempty_torus_points_mulEquiv k E.X
  obtain ⟨-, hcard⟩ := GlobalTheory.SemiAbTorsionCount.divisible_and_card e N hN
  let i := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  rw [← hcard]
  refine (Nat.card_eq_of_bijective
    (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩).symm
  · intro a b h
    exact Subtype.ext (hi (congrArg Subtype.val h))
  · rintro ⟨x, hx, t, rfl⟩
    have hx₁ : i t ^ N = 1 := hx
    exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩

theorem bound_algClosed (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    (E : TorusExtension G) (g N : ℕ) (hG : IsSemiAbelian G) (hg : SmoothOfRelativeDimension g G.hom)
    (hN : (N : k) ≠ 0) (m : ℕ) (P : Fin m → (𝟙_ (Over (Sp k)) ⟶ G)) (hP : Function.Injective P)
    (hP' : ∀ i, P i ^ N = 1) :
    m * N ^ @Module.finrank ℤ E.X _ E.addCommGroup.toAddCommMonoid _ ≤ N ^ (2 * g) := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have h := GlobalTheory.card_torsion_mul_card_toric_torsion k G E g N hG hg hN
  rw [card_toric_torsion k G E N hN] at h
  have hne : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1} ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact pow_ne_zero _ hN0 h.symm
  haveI := Nat.finite_of_card_ne_zero hne
  have hm : m ≤ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1} := by
    have := Nat.card_le_card_of_injective
      (fun i : Fin m => (⟨P i, hP' i⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1}))
      (fun a b hab => hP (congrArg Subtype.val hab))
    simpa using this
  rw [← h]
  exact Nat.mul_le_mul_right _ hm

end PositivityTheory.Xgn.ToricTorsionRankBounds

theorem PositivityTheory.Xgn.two_torsion_rank_bound : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) := by
  intro S G _ hG g hg k _ h2 x Gk _ ψ hψ τ m Q hQ hQ2
  let Ω := AlgebraicClosure k
  let f : Sp Ω ⟶ Sp k := spMap (algebraMap k Ω)
  haveI : Flat f := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField k) _
  haveI : Surjective f := ⟨fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  haveI : Epi f := Flat.epi_of_flat_of_surjective f
  have hp := isGrpPullback_pullback G (f ≫ x)
  obtain ⟨e, he, -⟩ := grpPullback_iso ((isGrpPullback_pullback Gk f).comp hψ) hp
  haveI := he
  let E : TorusExtension ((Over.pullback (f ≫ x)).obj G) :=
    torusExtOfIso e (GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.torusExtBC f τ)
  have hg' : SmoothOfRelativeDimension g ((Over.pullback (f ≫ x)).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  have h2' : ((2 : ℕ) : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap k Ω)]
    exact (map_ne_zero _).2 h2
  have hinj : Function.Injective (pushHom hp (𝟙_ (Over (Sp Ω)))) := by
    intro a b hab
    have e : a.left ≫ pullback.fst G.hom (f ≫ x) = b.left ≫ pullback.fst G.hom (f ≫ x) :=
      congrArg (fun z => z.left) hab
    exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w a).trans (Over.w b).symm))
  let U : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ f ≫ x) ⟶ Over.mk x :=
    Over.homMk f (Category.id_comp (f ≫ x)).symm
  let P : Fin m → (𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback (f ≫ x)).obj G) := fun i =>
    Over.homMk (hp.1.lift (U ≫ Q i).left (𝟙_ (Over (Sp Ω))).hom (Over.w (U ≫ Q i))) (hp.1.lift_snd _ _ _)
  have hP : ∀ i, pushHom hp (𝟙_ (Over (Sp Ω))) (P i) = preHom U (Q i) := fun i =>
    Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  refine PositivityTheory.Xgn.ToricTorsionRankBounds.bound_algClosed Ω _ E g 2 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (f ≫ x) G hG) hg' h2' m P ?_ ?_
  · intro a b hab
    have h1 : preHom U (Q a) = preHom U (Q b) := by rw [← hP, ← hP, hab]
    have h3 : f ≫ (Q a).left = f ≫ (Q b).left := congrArg (fun z => z.left) h1
    exact hQ (Over.OverMorphism.ext ((cancel_epi f).1 h3))
  · intro i
    apply hinj
    rw [map_pow, hP, ← map_pow, hQ2, map_one, map_one]
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MaximalTorusInFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.MaximalTorusFibre

open GlobalTheory.TorusToProper ReciprocityTheory.ChartRestriction.G.Out.GtBCPf ReciprocityTheory.ChartRestriction.G.Out.PullGtPf

variable {K : Type} [Field K] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

theorem pt_inj (R : Type) [CommRing R] [Algebra K R] : Function.Injective (pt K X R) := by
  intro θ θ' h
  have h1 : Spec.map (CommRingCat.ofHom (charRing X R θ)) =
      Spec.map (CommRingCat.ofHom (charRing X R θ')) := by
    rw [← ptFun_fst (K := K), ← ptFun_fst (K := K)]
    exact congrArg (fun t => Over.Hom.left t ≫ Rosenlicht.torusFst _ X) h
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  ext x
  have h3 := congrArg (fun f => f (AddMonoidAlgebra.single x 1)) h2
  simpa [charRing_single] using h3

theorem pt_surj (R : Type) [CommRing R] [Algebra K R] : Function.Surjective (pt K X R) := by
  intro t
  obtain ⟨f, hf⟩ := Spec.map_surjective
    (Over.Hom.left t ≫ Rosenlicht.torusFst (Spec (CommRingCat.of K)) X)
  let θ : Multiplicative X →* Rˣ :=
    (Units.map (f.hom : AddMonoidAlgebra (ULift.{0} ℤ) X →+* R).toMonoidHom).comp
      (AddMonoidAlgebra.of (ULift.{0} ℤ) X).toHomUnits
  refine ⟨θ, torus_ext ?_⟩
  show Over.Hom.left (ptFun K X R θ) ≫ _ = _
  rw [ptFun_fst, ← hf]
  congr 1
  ext1
  have hU : ∀ (a b : ULift.{0} ℤ →+* R), a = b := by
    intro a b
    ext r
    obtain ⟨n⟩ := r
    have e : (ULift.up n : ULift.{0} ℤ) = (n : ULift.{0} ℤ) := by ext; simp
    rw [e, map_intCast, map_intCast]
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    exact congrArg (fun g : ULift.{0} ℤ →+* R => g r)
      (hU ((charRing X R θ).comp AddMonoidAlgebra.singleZeroRingHom)
        ((f.hom : AddMonoidAlgebra (ULift.{0} ℤ) X →+* R).comp AddMonoidAlgebra.singleZeroRingHom))
  · intro m
    simp [charRing_single, θ]

theorem pt_eq_spm (R : Type) [CommRing R] [Algebra K R] (θ : Multiplicative X →* Rˣ) :
    (Units.map ((AddMonoidAlgebra.lift K R X ((Units.coeHom R).comp θ) : AddMonoidAlgebra K X →ₐ[K] R) :
      AddMonoidAlgebra K X →* R)).comp (univ K X) = θ := by
  ext x
  simp [univ]

theorem exists_char [Module.Free ℤ X] [Module.Finite ℤ X]
    (w : splitTorus (Sp K) X ⟶ splitTorus (Sp K) Y) (hw : (1 : sp K K ⟶ _) ≫ w = 1) :
    ∃ φ : Y →+ X, ∀ (R : Type) [CommRing R] [Algebra K R] (θ : Multiplicative X →* Rˣ),
      pt K X R θ ≫ w = pt K Y R (θ.comp (AddMonoidHom.toMultiplicative φ)) := by
  classical
  obtain ⟨ψ, hψ⟩ := pt_surj (K := K) (X := Y) (AddMonoidAlgebra K X)
    (pt K X (AddMonoidAlgebra K X) (univ K X) ≫ w)
  have hunit : ∀ y : Y, ∃ (a : X) (c : K), IsUnit c ∧
      ((ψ (Multiplicative.ofAdd y) : (AddMonoidAlgebra K X)ˣ) : AddMonoidAlgebra K X) =
        AddMonoidAlgebra.single a c :=
    fun y => Rosenlicht.isUnit_eq_single (Units.isUnit _)
  choose f c hc hfc using hunit
  let ε : AddMonoidAlgebra K X →ₐ[K] K :=
    AddMonoidAlgebra.lift K K X ((Units.coeHom K).comp (1 : Multiplicative X →* Kˣ))
  have hε1 : (Units.map (ε : AddMonoidAlgebra K X →* K)).comp (univ K X) = 1 :=
    pt_eq_spm (K := K) (X := X) K 1
  have h1 : spm ε ≫ pt K X (AddMonoidAlgebra K X) (univ K X) = 1 := by
    rw [← pt_nat, hε1, map_one]
  have hε : (Units.map (ε : AddMonoidAlgebra K X →* K)).comp ψ = 1 := by
    apply pt_inj (K := K) (X := Y) K
    rw [pt_nat, hψ, ← Category.assoc, h1, map_one]
    exact hw
  have hc1 : ∀ y, c y = 1 := by
    intro y
    have h2 := congrArg (fun g => ((g (Multiplicative.ofAdd y) : Kˣ) : K)) hε
    simpa [ε, hfc, AddMonoidAlgebra.lift_single] using h2
  have hψs : ∀ y, ((ψ (Multiplicative.ofAdd y) : (AddMonoidAlgebra K X)ˣ) : AddMonoidAlgebra K X) =
      AddMonoidAlgebra.single (f y) 1 := fun y => by rw [hfc, hc1]
  have hadd : ∀ y y', f (y + y') = f y + f y' := by
    intro y y'
    have h := congrArg (fun u : (AddMonoidAlgebra K X)ˣ => (u : AddMonoidAlgebra K X))
      (map_mul ψ (Multiplicative.ofAdd y) (Multiplicative.ofAdd y'))
    simp only [Units.val_mul, ← ofAdd_add, hψs, AddMonoidAlgebra.single_mul_single] at h
    rw [show (1 : K) * 1 = 1 from mul_one 1] at h
    exact (AddMonoidAlgebra.single_left_inj (one_ne_zero (α := K))).mp h
  refine ⟨AddMonoidHom.mk' f hadd, ?_⟩
  intro R _ _ θ
  let L : AddMonoidAlgebra K X →ₐ[K] R := AddMonoidAlgebra.lift K R X ((Units.coeHom R).comp θ)
  have hL : (Units.map (L : AddMonoidAlgebra K X →* R)).comp (univ K X) = θ := pt_eq_spm R θ
  have e1 : pt K X R θ = spm L ≫ pt K X (AddMonoidAlgebra K X) (univ K X) := by
    rw [← pt_nat, hL]
  rw [e1, Category.assoc, ← hψ, ← pt_nat]
  congr 1
  ext y
  simp [L, hψs, AddMonoidAlgebra.lift_single]

theorem surj_of_inj (φ : Y →+ X)
    (h : ∀ (R : Type) [CommRing R] [Algebra K R] (θ : Multiplicative X →* Rˣ),
      θ.comp (AddMonoidHom.toMultiplicative φ) = 1 → θ = 1) : Function.Surjective φ := by
  classical
  let Q := X ⧸ φ.range
  let θ : Multiplicative X →* (AddMonoidAlgebra K Q)ˣ :=
    (univ K Q).comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' φ.range))
  have hθ : θ = 1 := by
    refine h (AddMonoidAlgebra K Q) θ ?_
    refine MonoidHom.ext fun y => Units.ext ?_
    have hy : (QuotientAddGroup.mk' φ.range) (φ (Multiplicative.toAdd y)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨_, rfl⟩
    simp [θ, univ, AddMonoidAlgebra.one_def, AddMonoidAlgebra.of_apply, hy]
  intro x
  have h3 := congrArg (fun f => ((f (Multiplicative.ofAdd x) : (AddMonoidAlgebra K Q)ˣ) :
    AddMonoidAlgebra K Q)) hθ
  simp only [θ, univ, MonoidHom.comp_apply, MonoidHom.one_apply, Units.val_one,
    MonoidHom.coe_toHomUnits, AddMonoidAlgebra.of_apply, AddMonoidAlgebra.one_def] at h3
  have h4 : (QuotientAddGroup.mk' φ.range) x = 0 :=
    (AddMonoidAlgebra.single_left_inj (one_ne_zero (α := K))).mp h3
  obtain ⟨y, hy⟩ := (QuotientAddGroup.eq_zero_iff x).mp h4
  exact ⟨y, hy⟩

theorem inj_of_surj [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (φ : Y →+ X) (hφ : Function.Surjective φ) (hr : Module.finrank ℤ Y ≤ Module.finrank ℤ X) :
    Function.Injective φ := by
  have hle : Module.finrank ℤ X ≤ Module.finrank ℤ Y :=
    LinearMap.finrank_le_finrank_of_surjective (f := φ.toIntLinearMap) hφ
  let e : X ≃ₗ[ℤ] Y := LinearEquiv.ofFinrankEq X Y (le_antisymm hle hr)
  have hs : Function.Surjective (e.toLinearMap ∘ₗ φ.toIntLinearMap) :=
    e.surjective.comp hφ
  have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs
  intro a b hab
  exact hi (by simp [hab])

theorem field_case [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over (Sp K)} [GrpObj G]
    (v : splitTorus (Sp K) X ⟶ G) [IsMonHom v]
    (hv : ∀ (A : Type) [CommRing A] [Algebra K A] (t : sp K A ⟶ splitTorus (Sp K) X), t ≫ v = 1 → t = 1)
    (τ : TorusExtension G) (hr : letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X)
    (A : Type) [CommRing A] [Algebra K A] (p : sp K A ⟶ G) :
    letI := τ.grpB; p ≫ τ.q = 1 ↔ ∃ t : sp K A ⟶ splitTorus (Sp K) X, t ≫ v = p := by
  letI := τ.addCommGroup
  haveI := τ.free
  haveI := τ.finite
  letI := τ.grpB
  haveI := τ.q_hom
  haveI := τ.i_hom
  haveI : IsProper τ.B.hom := τ.isAbelian.proper
  have hvq : v ≫ τ.q = toUnit _ ≫ η :=
    GlobalTheory.splitTorus_hom_proper_trivial_field K X τ.B (v ≫ τ.q) inferInstance
  let w := τ.isKernel.lift v (toUnit _) hvq
  have hwv : w ≫ τ.i = v := τ.isKernel.lift_fst _ _ _
  haveI : Mono τ.i := τ.isKernel.mono_fst_of_mono
  have hw1 : (1 : sp K K ⟶ _) ≫ w = 1 := by
    apply (cancel_mono τ.i).mp
    rw [Category.assoc, hwv, MonObj.one_comp, MonObj.one_comp]
  obtain ⟨φ, hφ⟩ := exists_char w hw1
  have hsurj : Function.Surjective φ := by
    apply surj_of_inj (K := K) φ
    intro R _ _ θ hθ
    apply pt_inj (K := K) (X := X) R
    rw [map_one]
    apply hv R
    rw [← hwv, ← Category.assoc, hφ, hθ, map_one, MonObj.one_comp]
  have hinj := inj_of_surj φ hsurj hr
  constructor
  · intro hp
    let s := τ.isKernel.lift p (toUnit _) hp
    have hs : s ≫ τ.i = p := τ.isKernel.lift_fst _ _ _
    obtain ⟨σ, hσ⟩ := pt_surj (K := K) (X := τ.X) A s
    let e : τ.X ≃+ X := AddEquiv.ofBijective φ ⟨hinj, hsurj⟩
    have he : ∀ y, e.symm (φ y) = y := fun y => e.symm_apply_apply y
    refine ⟨pt K X A (σ.comp (AddMonoidHom.toMultiplicative (e.symm : X →+ τ.X))), ?_⟩
    have hcomp : (σ.comp (AddMonoidHom.toMultiplicative (e.symm : X →+ τ.X))).comp
        (AddMonoidHom.toMultiplicative φ) = σ := by
      ext y
      simp [he]
    rw [← hwv, ← Category.assoc, hφ, hcomp, hσ, hs]
  · rintro ⟨t, rfl⟩
    rw [Category.assoc, hvq]
    exact MonObj.comp_one t

end PositivityTheory.Xgn.MaximalTorusFibre

open PositivityTheory.Xgn.MaximalTorusFibre GlobalTheory.TorusToProper ReciprocityTheory.ChartRestriction.G.Out.GtBCPf ReciprocityTheory.ChartRestriction.G.Out.PullGtPf in
theorem PositivityTheory.Xgn.maximal_torus_in_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ := by
  intro S G _ X _ _ _ u _ k _ x hu Gk _ ψ hψ τ hr A _ g p
  letI : Algebra k A := g.toAlgebra
  have one_left : ∀ {T : Scheme.{0}} (Z M : Over T) [GrpObj M],
      (1 : Z ⟶ M).left = Z.hom ≫ (η : 𝟙_ (Over T) ⟶ M).left := by
    intro T Z M _
    show (toUnit Z ≫ η).left = _
    rw [Over.comp_left, toUnit_left']
  have gT := grpT x X
  have hTsnd := hT_snd x X
  have hcond : (hT x X ≫ u.left) ≫ G.hom = (splitTorus (Sp k) X).hom ≫ x := by
    rw [Category.assoc, Over.w u, hTsnd]
  let v : splitTorus (Sp k) X ⟶ Gk :=
    Over.homMk (hψ.1.lift (hT x X ≫ u.left) (splitTorus (Sp k) X).hom hcond) (hψ.1.lift_snd _ _ _)
  have hvψ : v.left ≫ ψ = hT x X ≫ u.left := hψ.1.lift_fst _ _ _
  haveI : IsMonHom v := isMonHom_of_grpPullback gT hψ u v hvψ
  have toS : ∀ (B : Type) [CommRing B] [Algebra k B] (t' : sp k B ⟶ splitTorus (Sp k) X),
      (t'.left ≫ hT x X) ≫ (splitTorus S X).hom =
        (Over.mk (spMap (algebraMap k B) ≫ x)).hom := by
    intro B _ _ t'
    rw [Category.assoc, hTsnd, ← Category.assoc, Over.w t']
    rfl
  have hv : ∀ (B : Type) [CommRing B] [Algebra k B] (t' : sp k B ⟶ splitTorus (Sp k) X),
      t' ≫ v = 1 → t' = 1 := by
    intro B _ _ t' ht'
    let t : Over.mk (spMap (algebraMap k B) ≫ x) ⟶ splitTorus S X :=
      Over.homMk (t'.left ≫ hT x X) (toS B t')
    have ht1 : t ≫ u = 1 := by
      ext1
      rw [Over.comp_left, one_left]
      show (t'.left ≫ hT x X) ≫ u.left = _
      rw [Category.assoc, ← hvψ, ← Category.assoc, ← Over.comp_left, ht', one_left,
        Category.assoc, IsGrpPullback.one_left hψ]
      simp only [Over.mk_hom, Category.assoc]
    have ht := hu B (algebraMap k B) t ht1
    ext1
    apply gT.1.hom_ext
    · have h2 := congrArg (fun s => Over.Hom.left s) ht
      rw [show t'.left ≫ hT x X = t.left from rfl, h2, one_left, one_left, Category.assoc,
        IsGrpPullback.one_left gT]
      simp only [Over.mk_hom, Category.assoc]
    · rw [Over.w t', Over.w (1 : sp k B ⟶ splitTorus (Sp k) X)]
  have key := field_case (K := k) v hv τ hr A p
  rw [key]
  constructor
  · rintro ⟨t', rfl⟩
    refine ⟨Over.homMk (t'.left ≫ hT x X) (toS A t'), ?_⟩
    rw [Over.comp_left, Over.comp_left]
    show (t'.left ≫ hT x X) ≫ u.left = (t'.left ≫ v.left) ≫ ψ
    rw [Category.assoc, Category.assoc, hvψ]
  · rintro ⟨t, ht⟩
    let L := gT.1.lift t.left (spMap g) (Over.w t)
    have hL1 : L ≫ hT x X = t.left := gT.1.lift_fst _ _ _
    have hL2 : L ≫ (splitTorus (Sp k) X).hom = spMap g := gT.1.lift_snd _ _ _
    refine ⟨Over.homMk L hL2, ?_⟩
    ext1
    apply hψ.1.hom_ext
    · show (L ≫ v.left) ≫ ψ = p.left ≫ ψ
      rw [Category.assoc, hvψ, ← Category.assoc, hL1, ← Over.comp_left, ht]
    · show (L ≫ v.left) ≫ Gk.hom = p.left ≫ Gk.hom
      rw [Category.assoc, Over.w v, hL2]
      exact (Over.w p).symm
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FiniteSurjectiveImageOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem PositivityTheory.Xgn.finite_surjective_image_open : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V := by
  intro Z Z' _ _ π hπ _ V hV
  haveI : IsFinite π := hπ
  have hCc : IsClosed ((V : Set Z')ᶜ) := V.isOpen.isClosed_compl
  refine ⟨⟨(π '' (V : Set Z')ᶜ)ᶜ, (π.isClosedMap _ hCc).isOpen_compl⟩, ⟨genericPoint Z, ?_⟩, ?_⟩
  · show genericPoint Z ∉ π '' (V : Set Z')ᶜ
    rintro ⟨x, hxC, hx⟩
    have h1 : genericPoint Z' ⤳ x := (genericPoint_spec Z').specializes (Set.mem_univ x)
    have h2 : π (genericPoint Z') = genericPoint Z := by
      have a : π (genericPoint Z') ⤳ π x := h1.map π.continuous
      rw [hx] at a
      exact (a.antisymm ((genericPoint_spec Z).specializes (Set.mem_univ _))).eq
    haveI hd := (π.isDiscrete_preimage_singleton (genericPoint Z)).to_subtype
    have m2 : genericPoint Z' ∈ (π ⁻¹' {genericPoint Z} : Set Z') := h2
    have mx : x ∈ (π ⁻¹' {genericPoint Z} : Set Z') := hx
    have h3 : (⟨genericPoint Z', m2⟩ : (π ⁻¹' {genericPoint Z} : Set Z')) ⤳ ⟨x, mx⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp h1
    have h4 : genericPoint Z' = x := congrArg Subtype.val (specializes_iff_eq.mp h3)
    apply hxC
    rw [← h4]
    exact ((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsPreimmersionToNormalization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.StratumOpenCover

theorem isPreimmersion_val (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    (L : Type) [Field L] [Algebra A L] [Algebra.IsAlgebraic A L]
    (hinj : Function.Injective (algebraMap A L)) (e : L ≃ₐ[A] B) :
    IsPreimmersion (Spec.map (CommRingCat.ofHom (integralClosure A B).val.toRingHom)) := by
  have hB : IsField B := MulEquiv.isField (Field.toIsField L) e.symm.toMulEquiv
  let : Field B := hB.toField
  have : Algebra.IsAlgebraic A B := e.isAlgebraic
  have : IsFractionRing (integralClosure A B) B :=
    integralClosure.isFractionRing_of_algebraic (A := A) (L := B) fun x hx => by
      apply hinj
      apply e.injective
      simpa using hx
  exact IsPreimmersion.of_isLocalization (R := integralClosure A B) (S := B) (nonZeroDivisors _)

theorem isPreimmersion_toNormalization (Z : Scheme.{0}) [IsIntegral Z] {L : Type} [Field L]
    (φ : Z.presheaf.stalk (genericPoint Z) ⟶ .of L) (hφ : φ.hom.Finite) :
    IsPreimmersion (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)).toNormalization := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint Z)) isOpen_univ
  set f := Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) with hf
  have htop : f ⁻¹ᵁ U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    change f x ∈ U
    rw [hf, Scheme.Hom.comp_apply]
    have : Z.fromSpecStalk (genericPoint Z) (Spec.map φ x) ∈
        Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hxU
  let := (f.app U).hom.toAlgebra
  let ψ : CommRingCat.of L ⟶ Γ(Spec (.of L), f ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).presheaf.map (homOfLE le_top).op
  have : IsIso (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)) := ⟨homOfLE htop.ge, rfl, rfl⟩
  have hψ : IsIso ψ := inferInstance
  have happ : f.app U = Z.presheaf.germ U _ hxU ≫ φ ≫ ψ := by
    simp only [f, ψ, Scheme.Hom.comp_app, Scheme.fromSpecStalk_app hxU, Category.assoc]
    rw [Scheme.Hom.naturality, Scheme.ΓSpecIso_inv_naturality_assoc φ]
    rfl
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let : Algebra Z.functionField L := φ.hom.toAlgebra
  let : Algebra Γ(Z, U) L := (Z.presheaf.germ U _ hxU ≫ φ).hom.toAlgebra
  have : IsScalarTower Γ(Z, U) Z.functionField L := .of_algebraMap_eq fun _ => rfl
  have : IsFractionRing Γ(Z, U) Z.functionField := functionField_isFractionRing_of_isAffineOpen Z U hU
  have : Module.Finite Z.functionField L := hφ
  have : Algebra.IsAlgebraic Γ(Z, U) L :=
    (IsFractionRing.comap_isAlgebraic_iff (K := Z.functionField)).mpr inferInstance
  have hinj : Function.Injective (algebraMap Γ(Z, U) L) := by
    rw [IsScalarTower.algebraMap_eq Γ(Z, U) Z.functionField L]
    exact (algebraMap Z.functionField L).injective.comp (IsFractionRing.injective _ _)
  let e : L ≃ₐ[Γ(Z, U)] Γ(Spec (.of L), f ⁻¹ᵁ U) :=
    { (asIso ψ).commRingCatIsoToRingEquiv with
      commutes' := fun a => by
        change ((Z.presheaf.germ U _ hxU ≫ φ) ≫ ψ).hom a = (f.app U).hom a
        rw [happ, Category.assoc] }
  have h1 := isPreimmersion_val Γ(Z, U) Γ(Spec (.of L), f ⁻¹ᵁ U) L hinj e
  have h2 := f.ι_toNormalization ⟨U, hU⟩
  have hW : IsAffineOpen (f ⁻¹ᵁ U) := htop ▸ isAffineOpen_top _
  have h3 : IsIso (f ⁻¹ᵁ U).toSpecΓ := by
    rw [← hW.isoSpec_hom]; infer_instance
  have h4 : IsIso (f ⁻¹ᵁ U).ι := by
    rw [htop]; exact inferInstanceAs (IsIso (Spec (.of L)).topIso.hom)
  have h5 : IsPreimmersion ((f ⁻¹ᵁ U).ι ≫ f.toNormalization) := by
    rw [h2]
    have h7 : IsOpenImmersion (f.normalizationOpenCover.f ⟨U, hU⟩) := f.normalizationOpenCover.map_prop _
    have h8 : IsPreimmersion (f.normalizationOpenCover.f ⟨U, hU⟩) :=
      (fun {X Y : Scheme.{0}} (g : X ⟶ Y) (_ : IsOpenImmersion g) => (inferInstance : IsPreimmersion g)) _ h7
    exact @IsPreimmersion.comp _ _ _ _ _ inferInstance (@IsPreimmersion.comp _ _ _ _ _ h1 h8)
  have h6 : IsPreimmersion (inv (f ⁻¹ᵁ U).ι ≫ (f ⁻¹ᵁ U).ι ≫ f.toNormalization) := inferInstance
  rwa [IsIso.inv_hom_id_assoc] at h6

end PositivityTheory.Xgn.StratumOpenCover

theorem PositivityTheory.Xgn.stratum_finite_normal_cover : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (L : Type) [Field L] (z : Sp L ⟶ Z), GlobalTheory.IsGenericPointHom z → ∀ (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L'], ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (j : Sp L' ⟶ Z'), IsFinite π ∧ Surjective π ∧ IsNormalScheme Z' ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap L L') ≫ z := by
  intro Z _ s _ _ L _ z hz L' _ _ _
  obtain ⟨e, rfl⟩ := hz
  obtain ⟨χ, hχ⟩ := Spec.map_surjective e.hom
  have : IsIso (Spec.map χ) := hχ ▸ inferInstance
  have hχ' : IsIso χ := (isIso_SpecMap_iff).mp this |> (ConcreteCategory.isIso_iff_bijective χ).mpr
  let φ : Z.presheaf.stalk (genericPoint Z) ⟶ .of L' := χ ≫ CommRingCat.ofHom (algebraMap L L')
  have hφ : φ.hom.Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.mpr inferInstance)
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso χ).2)
  have hf : spMap (algebraMap L L') ≫ e.hom ≫ Z.fromSpecStalk (genericPoint Z) =
      Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) := by
    rw [← hχ, Spec.map_comp, Category.assoc]
  rw [hf]
  have : CharZero L' := by
    obtain ⟨ρ, -⟩ := Spec.map_surjective (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) ≫ s)
    exact charZero_of_injective_ringHom (R := ℚ) ρ.hom.injective
  have hfin := GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s (genericPoint Z) φ
    hφ.finiteType.essFiniteType
  have hpre := PositivityTheory.Xgn.StratumOpenCover.isPreimmersion_toNormalization Z φ hφ
  have hdom : IsDominant (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) := by
    refine ⟨?_⟩
    have hx : (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) (IsLocalRing.closedPoint L') =
        genericPoint Z := by
      have : Z.fromSpecStalk (genericPoint Z) (Spec.map φ (IsLocalRing.closedPoint L')) ∈
        Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨_, rfl⟩
      rw [Scheme.range_fromSpecStalk] at this
      exact (Specializes.antisymm this (genericPoint_specializes _)).eq
    refine Dense.mono (Set.singleton_subset_iff.mpr ⟨_, hx⟩) ?_
    exact dense_iff_closure_eq.mpr (genericPoint_spec Z)
  set f := Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)
  have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]; exact hdom
  have : IsDominant f.fromNormalization := .of_comp f.toNormalization _
  refine ⟨f.normalization, inferInstance, f.fromNormalization, f.toNormalization, hfin,
    inferInstance, GlobalTheory.IsNormalScheme.pred _, GlobalTheory.IsGenericPointHom.of_isPreimmersion _,
    Scheme.Hom.toNormalization_fromNormalization _⟩
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsSplitTorusExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.SplitTorusExtension

theorem one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    change ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have h₁ : (e * e).left = e.left := by
    rw [h.2 T 1 1 e e rfl rfl, _root_.mul_one]
    rfl
  have h₂ : e * e = e := Over.OverMorphism.ext h₁
  have h₃ : e = 1 := by simpa using h₂
  rw [← h₃]
  rfl

theorem eq_one {S S' : Scheme.{0}} {G' H' : Over S'} [GrpObj G'] [GrpObj H'] {G H : Over S} [GrpObj G] [GrpObj H]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ)
    (hψ : IsGrpPullback H' H f ψ) (i : G' ⟶ H') [IsMonHom i] [Mono i] (u : G ⟶ H)
    (hu : i.left ≫ ψ = φ ≫ u.left) (T : Over S') (t : Over.mk (T.hom ≫ f) ⟶ G) (ht : t ≫ u = 1) : t = 1 := by
  have hw : t.left ≫ G.hom = T.hom ≫ f := Over.w t
  let s : T.left ⟶ G'.left := hφ.1.lift t.left T.hom hw
  have hs : s ≫ φ = t.left := hφ.1.lift_fst _ _ _
  let s' : T ⟶ G' := Over.homMk s (hφ.1.lift_snd _ _ _)
  have h1 : s' ≫ i = 1 := by
    apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · rw [← one_left hψ T, Over.comp_left, Category.assoc, hu, ← Category.assoc]
      change (s ≫ φ) ≫ u.left = _
      rw [hs, ← Over.comp_left, ht]
    · rw [Over.w, Over.w]
  have h2 : s' = 1 := by
    have h3 : (1 : T ⟶ G') ≫ i = 1 := by simp [Hom.one_def]
    rw [← h3] at h1
    exact (cancel_mono i).mp h1
  apply Over.OverMorphism.ext
  rw [one_left hφ T, ← h2]
  exact hs.symm

end PositivityTheory.Xgn.SplitTorusExtension

theorem PositivityTheory.Xgn.exists_split_torus_extension : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 := by
  intro hext Z' _ _ hnorm G _ hG L' _ j hj τ
  letI := τ.addCommGroup
  haveI := τ.free
  haveI := τ.finite
  haveI := τ.i_hom
  haveI : Mono τ.i := τ.isKernel.mono_fst_of_mono
  have hT : IsSemiAbelian (splitTorus Z' τ.X) :=
    ((GlobalTheory.splitTorus_properties Z').1 τ.X).2.2.2.2.2.2.2.2.1
  obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange Z' (Sp L') j τ.X
  haveI := he
  have hφ : IsGrpPullback (splitTorus (Sp L') τ.X) (splitTorus Z' τ.X) j
      (e.hom.left ≫ pullback.fst (splitTorus Z' τ.X).hom j) := by
    have h0 := (isGrpPullback_of_iso e).comp (isGrpPullback_pullback (splitTorus Z' τ.X) j)
    rwa [Category.id_comp] at h0
  have hψ := isGrpPullback_pullback G j
  obtain ⟨F, ⟨hF, hu⟩, -⟩ :=
    GlobalTheory.Published.SemiAbelianHomExtension.generic_of_isGrpPullback hext hnorm hj hT hG hφ hψ τ.i
  refine ⟨F, hF, fun A _ g t ht => ?_⟩
  haveI := hF
  exact SplitTorusExtension.eq_one hφ hψ τ.i F hu (Over.mk (spMap g)) t ht
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTwoTorsion
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTwoTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.GenTors

theorem exists_finite_ext_torusExtension_two_torsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ ∃ (τ : TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (spMap (algebraMap L L') ≫ z) ⟶ G)), Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) :=
  PositivityTheory.Xgn.stratum_generic_torsion_points

end GlobalTheory.CompanionTheory.Ar.GenTors
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTwoTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_two_torsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ ∃ (τ : TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (spMap (algebraMap L L') ≫ z) ⟶ G)), Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenTors.exists_finite_ext_torusExtension_two_torsion | exact GlobalTheory.CompanionTheory.Ar.GenTors.exists_finite_ext_torusExtension_two_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.GenTors.exists_finite_ext_torusExtension_two_torsion <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionCardBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionCardBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.RankBound

theorem rank_bound_of_points_of_order_two :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) :=
  @PositivityTheory.Xgn.two_torsion_rank_bound

end GlobalTheory.CompanionTheory.Ar.RankBound
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionCardBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_torsion_card_bound : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RankBound.rank_bound_of_points_of_order_two | exact GlobalTheory.CompanionTheory.Ar.RankBound.rank_bound_of_points_of_order_two | (intros; apply GlobalTheory.CompanionTheory.Ar.RankBound.rank_bound_of_points_of_order_two <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelTrivialOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelTrivialOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.KerSpread

theorem injective_on_points_of_generic : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (G : Over Z') [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus Z' X ⟶ G) [IsMonHom u] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → (∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Z'), ⊤ ≤ a ⁻¹ᵁ V → ∀ t : Over.mk a ⟶ splitTorus Z' X, t ≫ u = 1 → t = 1 :=
  @PositivityTheory.Xgn.torus_kernel_trivial_spreads_open

end GlobalTheory.CompanionTheory.Ar.KerSpread
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelTrivialOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_kernel_trivial_open : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (G : Over Z') [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus Z' X ⟶ G) [IsMonHom u] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → (∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Z'), ⊤ ≤ a ⁻¹ᵁ V → ∀ t : Over.mk a ⟶ splitTorus Z' X, t ≫ u = 1 → t = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KerSpread.injective_on_points_of_generic | exact GlobalTheory.CompanionTheory.Ar.KerSpread.injective_on_points_of_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.KerSpread.injective_on_points_of_generic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionSpreadOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionSpreadOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem pts_spread : ∀ (Z' S : Scheme.{0}) [IsIntegral Z'] (c : Z' ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ (m : ℕ) (P : Fin m → (Over.mk (j ≫ c) ⟶ G)), Function.Injective P → (∀ i, P i ^ 2 = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ x ⁻¹ᵁ V → ∃ Q : Fin m → (Over.mk (x ≫ c) ⟶ G), Function.Injective Q ∧ ∀ i, Q i ^ 2 = 1 := by
  exact @PositivityTheory.Xgn.two_torsion_points_spread_open

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionSpreadOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_torsion_spread_open : ∀ (Z' S : Scheme.{0}) [IsIntegral Z'] (c : Z' ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ (m : ℕ) (P : Fin m → (Over.mk (j ≫ c) ⟶ G)), Function.Injective P → (∀ i, P i ^ 2 = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ x ⁻¹ᵁ V → ∃ Q : Fin m → (Over.mk (x ≫ c) ⟶ G), Function.Injective Q ∧ ∀ i, Q i ^ 2 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.pts_spread | exact GlobalTheory.CompanionTheory.Ar.pts_spread | (intros; apply GlobalTheory.CompanionTheory.Ar.pts_spread <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionRankBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionRankBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.MaxTorus

theorem kernel_eq_of_rank_le : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ :=
  @PositivityTheory.Xgn.maximal_torus_in_fibre

end GlobalTheory.CompanionTheory.Ar.MaxTorus
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionRankBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_rank_bound : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MaxTorus.kernel_eq_of_rank_le | exact GlobalTheory.CompanionTheory.Ar.MaxTorus.kernel_eq_of_rank_le | (intros; apply GlobalTheory.CompanionTheory.Ar.MaxTorus.kernel_eq_of_rank_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveOpenImage
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveOpenImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.Strat

theorem preimage_le_of_finite_surjective : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V :=
  PositivityTheory.Xgn.finite_surjective_image_open

end GlobalTheory.CompanionTheory.Ar.Strat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveOpenImageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_surjective_open_image : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Strat.preimage_le_of_finite_surjective | exact GlobalTheory.CompanionTheory.Ar.Strat.preimage_le_of_finite_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.Strat.preimage_le_of_finite_surjective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormalCoverGenericPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormalCoverGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ggeo

theorem normalisation_finite_cover :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (L : Type) [Field L] (z : Sp L ⟶ Z), GlobalTheory.IsGenericPointHom z → ∀ (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L'], ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (j : Sp L' ⟶ Z'), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap L L') ≫ z :=
  @PositivityTheory.Xgn.stratum_finite_normal_cover

end GlobalTheory.CompanionTheory.Ggeo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormalCoverGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_normal_cover_generic_point : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (L : Type) [Field L] (z : Sp L ⟶ Z), GlobalTheory.IsGenericPointHom z → ∀ (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L'], ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (j : Sp L' ⟶ Z'), IsFinite π ∧ Surjective π ∧ IsNormalScheme Z' ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap L L') ≫ z := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.normalisation_finite_cover | exact GlobalTheory.CompanionTheory.Ggeo.normalisation_finite_cover | (intros; apply GlobalTheory.CompanionTheory.Ggeo.normalisation_finite_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionSplitMap
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionSplitMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem torus_extension_generic : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 :=
  @PositivityTheory.Xgn.exists_split_torus_extension

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionSplitMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_split_map : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.torus_extension_generic | exact GlobalTheory.CompanionTheory.Ar.torus_extension_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.torus_extension_generic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianFiniteCoverTorus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.StratOpen

theorem charZero_of_point {k : Type} [Field k] (x : Sp k ⟶ Sp ℚ) : CharZero k :=
  (RingHom.charZero_iff (Spec.preimage x).hom.injective).1 inferInstance

theorem core (hE : GlobalTheory.Published.SemiAbelianHomExtension) (Z : Scheme.{0}) [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
    (s : Z ⟶ Sp ℚ) (G : Over Z) [GrpObj G] (hG : IsSemiAbelian G) (g : ℕ) (hg : SmoothOfRelativeDimension g G.hom)
    (Z' : Scheme.{0}) [IsIntegral Z'] (π : Z' ⟶ Z) (hfin : IsFinite π) (hsurj : Surjective π) (hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z')
    (L' : Type) [Field L'] (j : Sp L' ⟶ Z') (hj : GlobalTheory.IsGenericPointHom j)
    (τ : TorusExtension ((Over.pullback (j ≫ π)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (j ≫ π) ⟶ G))
    (hPi : Function.Injective P) (hP2 : ∀ i, P i ^ 2 = 1)
    (hcount : letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) :
    ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  have hsm := hG.smooth
  have hsep := hG.separated
  have hG' : IsSemiAbelian ((Over.pullback π).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hG.comm
      infer_instance
    · have := hG.smooth
      change Smooth (pullback.snd G.hom π)
      infer_instance
    · have := hG.separated
      change IsSeparated (pullback.snd G.hom π)
      infer_instance
    · have := hG.quasiCompact
      change QuasiCompact (pullback.snd G.hom π)
      infer_instance
    · have := hG.geomConnected
      change GeometricallyConnected (pullback.snd G.hom π)
      infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := hG.fibres Ω (q ≫ π)
      exact ⟨torusExtOfIso (pullCompIso q π G) E⟩
  have hsep' := hG'.separated
  have hLN : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian π
  have hCS : CompactSpace Z' := QuasiCompact.compactSpace_of_compactSpace π
  have hN' : AlgebraicGeometry.IsNoetherian Z' := {}
  let τ' : TorusExtension ((Over.pullback j).obj ((Over.pullback π).obj G)) := torusExtOfIso (pullCompIso j π G) τ
  letI := τ'.addCommGroup
  haveI := τ'.free
  haveI := τ'.finite
  obtain ⟨u, hu, hmono⟩ := GlobalTheory.T.torus_extension_split_map hE Z' hnorm ((Over.pullback π).obj G) hG' L' j hj τ'
  obtain ⟨V₁, hV₁, hC⟩ := GlobalTheory.T.torus_kernel_trivial_open Z' ((Over.pullback π).obj G) τ'.X u L' j hj hmono
  obtain ⟨V₂, hV₂, hD⟩ := GlobalTheory.T.two_torsion_spread_open Z' Z π G L' j hj m P hPi hP2
  have hVne : ((V₁ ⊓ V₂ : Z'.Opens) : Set Z').Nonempty :=
    nonempty_preirreducible_inter V₁.isOpen V₂.isOpen hV₁ hV₂
  obtain ⟨U, hU, hUV⟩ := GlobalTheory.T.finite_surjective_open_image Z Z' π hfin hsurj (V₁ ⊓ V₂) hVne
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd hcount.symm (by simp)
    · exact h
  refine ⟨Z', inferInstance, π, (Over.pullback π).obj G, inferInstance, pullback.fst G.hom π, τ'.X, τ'.addCommGroup, τ'.free, τ'.finite, u, U, hfin, hsurj, hnorm, isGrpPullback_pullback G π, hu, hU, ?_⟩
  intro k _ x hx
  have hxV : ∀ W : Z'.Opens, V₁ ⊓ V₂ ≤ W → ⊤ ≤ x ⁻¹ᵁ W := fun W hW y _ => hW (hUV (hx trivial))
  have mono : ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' τ'.X), t ≫ u = 1 → t = 1 := by
    intro A _ g t ht
    refine hC A (spMap g ≫ x) (fun y _ => ?_) t ht
    have h1 := hxV V₁ inf_le_left (show (spMap g) y ∈ (⊤ : (Sp k).Opens) from trivial)
    simpa using h1
  refine ⟨mono, ?_⟩
  intro Gk _ ψ hψ τk
  letI := τk.grpB
  letI := τk.addCommGroup
  haveI := τk.free
  haveI := τk.finite
  obtain ⟨Q, hQi, hQ2⟩ := hD k x (hxV V₂ inf_le_right)
  have h2 : ((2 : ℕ) : k) ≠ 0 := by
    haveI : CharZero k := charZero_of_point (x ≫ π ≫ s)
    exact Nat.cast_ne_zero.2 two_ne_zero
  have hle := GlobalTheory.T.two_torsion_card_bound Z G hG g hg k h2 (x ≫ π) Gk (ψ ≫ pullback.fst G.hom π) (hψ.comp (isGrpPullback_pullback G π)) τk m Q hQi hQ2
  have hrk : Module.finrank ℤ τk.X ≤ Module.finrank ℤ τ'.X := by
    have h3 : m * 2 ^ Module.finrank ℤ τk.X ≤ m * 2 ^ Module.finrank ℤ τ'.X := hle.trans hcount.ge
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (Nat.le_of_mul_le_mul_left h3 hm)
  intro A _ gg p
  exact GlobalTheory.T.torus_extension_rank_bound Z' ((Over.pullback π).obj G) τ'.X u k x mono Gk ψ hψ τk hrk A gg p

theorem strat_open : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (G : Over Z) [GrpObj G], IsSemiAbelian G → ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  intro hE Z _ s _ _ G _ hG
  have hLN : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have hCS : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  have hN : AlgebraicGeometry.IsNoetherian Z := {}
  have hsm := hG.smooth
  have hsep := hG.separated
  have hfq := hG.quasiCompact
  let z : Sp Z.functionField ⟶ Z := Z.fromSpecStalk (genericPoint Z)
  have hz : GlobalTheory.IsGenericPointHom z := GlobalTheory.IsGenericPointHom.fromSpecStalk Z
  haveI : CharZero Z.functionField := charZero_of_point (z ≫ s)
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim Z Z.functionField z G (fun q => by
    have : genPt z = genericPoint Z := by
      have := hz.range_eq
      have h2 : genPt z ∈ Set.range z := ⟨_, rfl⟩
      rw [this] at h2
      exact h2
    rw [this]
    exact genericPoint_specializes q)
  obtain ⟨L', _, _, hfd, hB⟩ := GlobalTheory.T.torus_extension_two_torsion Z G hG g hg Z.functionField z
  obtain ⟨Z', _, π, j, hfin, hsurj, hnorm, hj, hjπ⟩ := GlobalTheory.T.finite_normal_cover_generic_point Z s Z.functionField z hz L'
  rw [← hjπ] at hB
  obtain ⟨τ, m, P, hPi, hP2, hcount⟩ := hB
  exact core hE Z s G hG g hg Z' π hfin hsurj hnorm L' j hj τ m P hPi hP2 hcount

end GlobalTheory.CompanionTheory.Ar.StratOpen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianFiniteCoverTorusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_finite_cover_torus : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (G : Over Z) [GrpObj G], IsSemiAbelian G → ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.StratOpen.strat_open | exact GlobalTheory.CompanionTheory.Ar.StratOpen.strat_open | (intros; apply GlobalTheory.CompanionTheory.Ar.StratOpen.strat_open <;> assumption)
end
