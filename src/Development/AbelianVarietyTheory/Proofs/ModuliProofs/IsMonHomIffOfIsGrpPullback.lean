module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FieldBaseChange

theorem flat_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Flat (spMap i) := by
  rw [Flat.SpecMap_iff]
  letI := i.toAlgebra
  exact (inferInstance : Module.Flat K₀ K)

theorem surjective_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Surjective (spMap i) := by
  have : Subsingleton (Sp K₀) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  exact ⟨fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

section General

variable {U S : Scheme.{0}} (j : U ⟶ S)

theorem pullback_map_left_fst {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback j).map a).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ a.left :=
  pullback.lift_fst _ _ _

theorem pullback_map_injective [Flat j] [Surjective j] (X Y : Over S) :
    Function.Injective ((Over.pullback j).map : (X ⟶ Y) → _) := fun f g h => by
  have : Epi (pullback.fst X.hom j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j), ← pullback_map_left_fst, ← pullback_map_left_fst, h]

theorem isMonHom_of_pullback [Flat j] [Surjective j] {G H : Over S} [MonObj G] [MonObj H] (f : G ⟶ H)
    (hf : IsMonHom ((Over.pullback j).map f)) : IsMonHom f := by
  constructor
  · apply pullback_map_injective j
    have h := hf.one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at h
    rw [Functor.map_comp, h]
  · apply pullback_map_injective j
    have h := hf.mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.LaxMonoidal.μ_natural_assoc, Category.assoc,
      cancel_epi] at h
    rw [Functor.map_comp, Functor.map_comp, h]

variable {j} in
theorem isMonHom_iff_of_isGrpPullback [Flat j] [Surjective j] {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : IsGrpPullback G' G j φ) (hH : IsGrpPullback H' H j ψ) (f' : G' ⟶ H') (f : G ⟶ H)
    (hf : φ ≫ f.left = f'.left ≫ ψ) : IsMonHom f' ↔ IsMonHom f := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j) hG
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hH (isGrpPullback_pullback H j)
  have e : (Over.pullback j).map f = a.hom ≫ f' ≫ b.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [pullback_map_left_fst, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← hf,
        ← Category.assoc, ha']
    · exact (Over.w _).trans (Over.w _).symm
  constructor
  · intro h
    exact isMonHom_of_pullback j f (by rw [e]; infer_instance)
  · intro h
    have e' : f' = a.inv ≫ (Over.pullback j).map f ≫ b.inv := by simp [e]
    rw [e']
    infer_instance

end General

theorem epi_and_isMonHom_iff : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K), (∀ (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), IsPullback φ p p₀ (spMap i) → Epi φ ∧ Flat φ ∧ Surjective φ ∧ IsAffineHom φ ∧ ∀ U : X₀.Opens, Function.Injective (φ.app U).hom) ∧ ∀ (A₀ B₀ : Over (Sp K₀)) (A B : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] [GrpObj A] [GrpObj B] (φ : A.left ⟶ A₀.left) (ψ : B.left ⟶ B₀.left) (f₀ : A₀ ⟶ B₀) (f : A ⟶ B), IsGrpPullback A A₀ (spMap i) φ → IsGrpPullback B B₀ (spMap i) ψ → φ ≫ f₀.left = f.left ≫ ψ → (IsMonHom f ↔ IsMonHom f₀) := by
  intro K₀ K _ _ i
  have := flat_spMap i
  have := surjective_spMap i
  refine ⟨fun X₀ X p₀ p φ h => ?_, fun A₀ B₀ A B _ _ _ _ φ ψ f₀ f hA hB hf =>
    isMonHom_iff_of_isGrpPullback hA hB f f₀ hf⟩
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip ‹_›
  have : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  have : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact ⟨Flat.epi_of_flat_of_surjective φ, ‹_›, ‹_›, ‹_›, fun U => GlobalTheory.FunDescent.app_injective φ U⟩

end GlobalTheory.FieldBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.LevelTwist

section Identity

variable {X : Scheme.{0}}

def selfIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (show (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2 from
    fun _ hx => ⟨mem_pull (F := 𝟙 X).1 hx.1, hx.2⟩) (L.g (p.1 PUnit.unit) p.2)⟩

theorem gw_selfIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (selfIso L) f y j k = gm f y _ (L.g j k) :=
  gm_res f y _ (show f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k from ⟨mem_pull (F := 𝟙 X).2 hj, hk⟩) _

theorem pgen_selfIso {L : LB X} (hL : L.IsLB) : PGen (selfIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_selfIso L f y j k hj hk, gw_selfIso L f y j' k' hj' hk', Category.comp_id, mul_right_comm,
    gm_cocycle hL f y hj hj' hk', ← gm_cocycle hL f y hj hk hk', mul_inv_cancel_right]

theorem pmaps_selfIso {L : LB X} {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (selfIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩
  have h := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact ((gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp k, hq k⟩ _)).trans
    (gw_selfIso L (r ≫ φ k) z (p k) (q k) (hp k) (hq k)).symm

variable {S : Scheme.{0}}

def cubeMapId (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.id_comp, Category.comp_id]
  psum_comm := fun I => by rw [Category.id_comp, Category.comp_id]

theorem isPullCubical_id {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) :
    (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ c c).2 ⟨selfIso L.L, pgen_selfIso L.isLB, pmaps_selfIso _ _ L.rig L.rigGen,
    pmaps_selfIso _ _ c.t c.isGen⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sabMapId (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl t.G) (inferInstanceAs (IsMonHom (𝟙 t.G)))
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.cub

theorem sabMapId_φ (t : SAB H S) : (sabMapId t).φ = 𝟙 _ := rfl

end Identity

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_congr (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) {a a' : D.La} (h : D.ModN n (a - a')) :
    I.ev n a = I.ev n a' := by
  have : a = (a - a') + a' := (sub_add_cancel a a').symm
  rw [this, I.add, (I.ker n hn _).2 h, _root_.one_mul]

theorem zeta_zpow_congr (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) {i j : ℤ} (h : (n : ℤ) ∣ i - j) :
    I.ζ n ^ i = I.ζ n ^ j := by
  have : i = (i - j) + j := (sub_add_cancel i j).symm
  rw [this, zpow_add, ((I.ζ_prim n hn).zpow_eq_one_iff_dvd _).2 h, _root_.one_mul]

def twist (I : TateIso D k Q act e) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) :
    TateIso D k Q act e where
  ζ n := I.ζ n ^ g.ν n
  ζ_prim n hn := (I.ζ_prim n hn).zpow_of_gcd_eq_one _ (Int.isCoprime_iff_gcd_eq_one.1 (hν n 1 hn one_pos).2)
  ζ_pow n m hn hm := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm (g.ν _), zpow_mul, zpow_natCast, I.ζ_pow n m hn hm]
    exact zeta_zpow_congr I hn (hν n m hn hm).1
  ev n a := I.ev n (g.f n a)
  add n a b := by rw [map_add (f := _), I.add]
  lin n c a := by rw [map_smul, I.lin]
  ker n hn a := by
    rw [I.ker n hn]
    obtain ⟨g', hg'⟩ := g.inv n hn
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨c, hc⟩ := (hg' a).1
      refine ⟨g' b - c, ?_⟩
      rw [smul_sub, ← hc, hb, map_nsmul, sub_sub_cancel]
    · rintro ⟨b, rfl⟩
      exact ⟨g.f n b, map_nsmul _ _ _⟩
  onto n hn x := by
    rw [I.onto n hn]
    obtain ⟨g', hg'⟩ := g.inv n hn
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨g' a, ev_congr I hn (hg' a).2⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
  tower n m hn hm a := by
    rw [I.tower n m hn hm]
    exact ev_congr I hn (g.tower n m hn hm a)
  isom n hn a b := by
    rw [← zpow_mul, ← zeta_zpow_congr I hn (g.mult n hn a b)]
    exact I.isom n hn _ _

@[simp] theorem twist_ζ (I : TateIso D k Q act e) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) (n : ℕ) :
    (twist I g hν).ζ n = I.ζ n ^ g.ν n := rfl

@[simp] theorem twist_ev (I : TateIso D k Q act e) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) (n : ℕ)
    (a : D.La) : (twist I g hν).ev n a = I.ev n (g.f n a) := rfl

theorem map_mem_smul_top (f : D.La →ₗ[𝓞 E] D.La) (J : Ideal (𝓞 E)) {a : D.La}
    (ha : a ∈ J • (⊤ : Submodule (𝓞 E) D.La)) : f a ∈ J • (⊤ : Submodule (𝓞 E) D.La) := by
  have h := Submodule.mem_map_of_mem (f := f) ha
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

def objTwist (o : Obj D l b s) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (hA : (l.A : ℤ) ∣ g.ν l.A - 1) : Obj D l b s where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta a := o.eta (g.f l.M a)
  eta_add a c := by rw [map_add (f := _), o.eta_add]
  eta_ker a ha := o.eta_ker _ (map_mem_smul_top _ _ ha)
  etaA a := o.etaA (g.f l.A a)
  etaA_add a c := by rw [map_add (f := _), o.etaA_add]
  etaA_ker a := by rw [map_nsmul, o.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, hζ, hA', hM⟩ := o.geom k x β hx
    refine ⟨hd, twist I g hν, ?_, fun a => hA' _, fun a ha => hM _ (map_mem_smul_top _ _ ha)⟩
    rw [twist_ζ, zeta_zpow_congr I l.A_pos hA, zpow_one, hζ]

end Twist

end GlobalTheory.LevelTwist

namespace GlobalTheory

theorem exists_obj_twist_by_similitude :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : Sim D), 1 ≤ D.p + D.q → (l.A : ℤ) ∣ g.ν l.A - 1 → ∃ (o' : Obj D l b s) (m : SABMap o'.t o.t (𝟙 S)), (∀ a, (o'.eta a).left ≫ m.φ = (o.eta (g.f l.M a)).left) ∧ ∀ a, (o'.etaA a).left ≫ m.φ = (o.etaA (g.f l.A a)).left := by
  intro h E _ _ _ H D l B _ b S s o g hpq hA
  exact ⟨LevelTwist.objTwist o g ((h E H D hpq).1 g) hA, LevelTwist.sabMapId o.t,
    fun _ => Category.comp_id _, fun _ => Category.comp_id _⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isIntegral_of_densePart {T U : Scheme.{0}} (j : U ⟶ T) [IsIntegral T]
    [GlobalTheory.IsNormalScheme T] [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] :
    IsIntegral U := by
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j
  have : GlobalTheory.IsNormalScheme U := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j
  have hη : genericPoint T ∈ genericPoints T := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨u, hu⟩ := genericPoints_subset_range_of_isDominant j hη
  have hgen : IsGenericPoint u (Set.univ : Set U) := by
    rw [isGenericPoint_iff_specializes]
    refine fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hu]
    exact (genericPoint_spec T).specializes trivial
  have : IrreducibleSpace U := by
    rw [irreducibleSpace_def]
    exact hgen.isIrreducible
  exact GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace U

theorem existsUnique_lift_of_densePart : ∀ (T U X Y : Scheme.{0}) [IsLocallyNoetherian T] (j : U ⟶ T), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (q : Y ⟶ X) (f : T ⟶ X) (g : U ⟶ Y), IsIntegralHom q → g ≫ q = j ≫ f → ∃! h : T ⟶ Y, j ≫ h = g ∧ h ≫ q = f := by
  intro T U Y Z _ j hT _ _ _ _ p b a _ h
  have := GlobalTheory.IsNormalScheme.of_pred hT
  have H (W : irreducibleComponents T) := by
    have : IsDominant (j ∣_ GlobalTheory.IsNormalScheme.component W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j› _
    have : IsIntegral (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).toScheme :=
      isIntegral_of_densePart (j ∣_ GlobalTheory.IsNormalScheme.component W)
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ∣_ GlobalTheory.IsNormalScheme.component W)
    exact existsUnique_lift_of_birational (j ∣_ GlobalTheory.IsNormalScheme.component W) p
      ((j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ a) ((GlobalTheory.IsNormalScheme.component W).ι ≫ b)
      (by rw [Category.assoc, h, morphismRestrict_ι_assoc])
  choose c hc _ using H
  obtain ⟨hT⟩ := GlobalTheory.IsNormalScheme.nonempty_isColimit_component (X := T)
  let c₀ : T ⟶ Z := Cofan.IsColimit.desc hT c
  have hc₀ (W) : (GlobalTheory.IsNormalScheme.component W).ι ≫ c₀ = c W := Cofan.IsColimit.fac hT c W
  have h₂ : c₀ ≫ p = b := Cofan.IsColimit.hom_ext hT _ _ fun W ↦ by
    change (GlobalTheory.IsNormalScheme.component W).ι ≫ _ = (GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [reassoc_of% hc₀ W, (hc W).2]
  have h₁ : j ≫ c₀ = a := by
    refine Scheme.Cover.hom_ext (U.openCoverOfIsOpenCover _
      (.comap (GlobalTheory.IsNormalScheme.iSup_component T) j.base.1)) _ _ fun W ↦ ?_
    change (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _ =
      (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [← morphismRestrict_ι_assoc, hc₀ W, (hc W).1]
  exact ⟨c₀, ⟨h₁, h₂⟩, fun c' hc' ↦
    lift_unique_of_isDominant j p (hc'.1.trans h₁.symm) (hc'.2.trans h₂.symm)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.HomExt

theorem exists_lift_of_range_subset {X U T : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (x : T ⟶ X) (h : Set.range x ⊆ Set.range j) : ∃ y : T ⟶ U, y ≫ j = x := by
  have hs : Function.Surjective (pullback.fst x j) := by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    exact fun t ↦ h ⟨t, rfl⟩
  have hp : IsPreimmersion (pullback.fst x j) := inferInstance
  have : IsIso (pullback.fst x j) := by
    rw [isIso_iff_isIso_stalkMap]
    refine ⟨?_, isIso_stalkMap_of_flat_of_surjectiveOnStalks _⟩
    exact TopCat.isIso_of_bijective_of_isOpenMap _ ⟨hp.isEmbedding.injective, hs⟩
      (hp.isEmbedding.isInducing.isOpenMap (by rw [hs.range_eq]; exact isOpen_univ))
  exact ⟨inv (pullback.fst x j) ≫ pullback.snd x j, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem field_point_comp_eq_iff {Z Y : Scheme.{0}} (g g' : Z ⟶ Y) {k : Type} [Field k]
    (c : Spec (.of k) ⟶ Z) (z : Z) (hz : z ∈ Set.range c) :
    c ≫ g = c ≫ g' ↔ Z.fromSpecResidueField z ≫ g = Z.fromSpecResidueField z ≫ g' := by
  obtain ⟨⟨w, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Z).symm.surjective c
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz ⊢
  obtain rfl : z = w := by
    obtain ⟨t, rfl⟩ := hz
    exact (Scheme.Hom.comp_apply _ _ t).trans (Scheme.fromSpecResidueField_apply w _)
  have : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := φ.hom.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (Spec.map φ) := ⟨fun t ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi (Spec.map φ) := Flat.epi_of_flat_of_surjective _
  rw [Category.assoc, Category.assoc, cancel_epi]

theorem finite_preimage_of_finite_lifts {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (h : Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : (f ⁻¹' Set.range y).Finite := by
  have hP : Finite ↥(pullback f y) := by
    refine finite_of_finite_sections (pullback.snd f y) ?_
    refine Finite.of_injective (β := {x : Spec (.of Ω) ⟶ X // x ≫ f = y})
      (fun x ↦ ⟨x.1 ≫ pullback.fst f y, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_
    intro a b hab
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hab
    · rw [a.2, b.2]
  rw [← Scheme.Pullback.range_fst]
  exact Set.finite_range _

theorem isIso_of_densePart_of_isIntegral {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [LocallyQuasiFinite p] [Surjective p]
    [IsIntegral Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsIso p := by
  obtain ⟨w₀, hw₀⟩ := genericPoints_subset_range_of_isDominant (i ≫ p)
    (show genericPoint Y ∈ genericPoints Y by simp [genericPoints_eq_singleton])
  have hgen : IsGenericPoint (i w₀) (Set.univ : Set Γ) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← i.denseRange.closure_range]
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    have h : w₀ ⤳ w := by
      rw [← (i ≫ p).isEmbedding.isInducing.specializes_iff, hw₀]
      exact genericPoint_specializes _
    exact specializes_iff_mem_closure.mp (h.map i.continuous)
  have : IrreducibleSpace Γ := (irreducibleSpace_def Γ).mpr hgen.isIrreducible
  have : IsIntegral Γ := isIntegral_of_irreducibleSpace_of_isReduced Γ
  have he : i w₀ = genericPoint Γ := hgen.eq (genericPoint_spec Γ)
  have : IsIso (p.stalkMap (genericPoint Γ)) := by
    rw [← he]
    have h₁ := isIso_stalkMap_of_flat_of_surjectiveOnStalks (i ≫ p) w₀
    have h₂ := isIso_stalkMap_of_flat_of_surjectiveOnStalks i w₀
    rw [Scheme.Hom.stalkMap_comp] at h₁
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (i.stalkMap w₀) h₂ h₁
  have := isOpenImmersion_of_quasiFinite_of_isIso_stalkMap p (fun y ↦ inferInstance)
  exact (isIso_iff_isOpenImmersion_and_surjective p).mpr ⟨inferInstance, inferInstance⟩

theorem isIso_of_densePart {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [LocallyQuasiFinite p] [Surjective p]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsIso p := by
  let V : Y → Y.Opens := fun y ↦ ⟨irreducibleComponent y,
    IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (irreducibleComponent_mem_irreducibleComponents y)⟩
  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    exact fun y _ ↦ Opens.mem_iSup.mpr ⟨y, mem_irreducibleComponent⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    V hV).mpr fun y ↦ ?_
  have : IrreducibleSpace (V y).toScheme :=
    Subtype.irreducibleSpace (isIrreducible_irreducibleComponent (x := y))
  have : IsIntegral (V y).toScheme := IsNormalScheme.isIntegral_of_irreducibleSpace _
  have e : (i ≫ p) ∣_ V y = i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y := morphismRestrict_comp _ _ _
  have : IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsDominant (i ∣_ (p ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) := e ▸ IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsDominant (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) := e ▸ IsZariskiLocalAtTarget.restrict ‹_› _
  have : Flat (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) :=
    e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›
  have : QuasiCompact (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) :=
    e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›
  have : Surjective (p ∣_ V y) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : LocallyQuasiFinite (p ∣_ V y) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p (V y)).flip ‹_›
  exact isIso_of_densePart_of_isIntegral (i ∣_ (p ⁻¹ᵁ V y)) (p ∣_ V y)

end GlobalTheory.HomExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem _root_.GlobalTheory.Models.sup_mul_sup_eq_of_coprime {R : Type} [CommRing R] {I J N : Ideal R}
    (h : I ⊔ J = ⊤) (hN : I * J ≤ N) : (I ⊔ N) * (J ⊔ N) = N := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le hN (Ideal.mul_le_inf.trans inf_le_right))
      (sup_le (Ideal.mul_le_inf.trans inf_le_left) (Ideal.mul_le_inf.trans inf_le_left))
  · calc N = N * (I ⊔ J) := by rw [h, Ideal.mul_top]
      _ = N * I ⊔ N * J := Ideal.mul_sup _ _ _
      _ ≤ (I ⊔ N) * (J ⊔ N) := sup_le
          (by rw [mul_comm]; exact Ideal.mul_mono le_sup_left le_sup_right)
          (Ideal.mul_mono le_sup_right le_sup_left)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def divisorLevel (l : Level H) (m : ℕ) (hm : m ∣ l.M) (h3 : 3 ≤ m) : Level H where
  M := m
  three_le := h3
  odd := l.odd.of_dvd_nat hm
  Mb := l.Mb ⊔ Ideal.span {(m : 𝓞 E)}
  fromK := by
    apply le_antisymm
    · apply sup_le
      · refine l.fromK.le.trans (Ideal.span_mono ?_)
        rintro a ⟨ha, ha'⟩
        exact ⟨Ideal.mem_sup_left ha, ha'⟩
      · apply Ideal.span_mono
        rintro a rfl
        exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), natCast_mem _ m⟩
    · exact Ideal.span_le.mpr fun a ha => ha.1
  prod := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
    refine sup_mul_sup_eq_of_coprime l.coprime ?_
    rw [l.prod]
    exact Ideal.span_singleton_le_span_singleton.mpr (Nat.cast_dvd_cast hm)
  coprime := by
    rw [eq_top_iff, ← l.coprime]
    exact sup_le_sup le_sup_left (Ideal.map_mono le_sup_left)
  A := 1
  A_pos := one_pos

private theorem level_ext' {a b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (hM : a.M = b.M) (hMb : a.Mb = b.Mb)
    (hA : a.A = b.A) : a = b := by
  cases a
  cases b
  simp only at hM hMb hA
  subst hM hMb hA
  rfl

theorem _root_.GlobalTheory.Models.primeToPart_spec : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ), p.Prime →
    (∀ l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.GoodAt p → ∃ l₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p) ∧
    (∀ l l₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p → l₀.Dvd l ∧ l₀.M.Coprime p ∧
      ∀ l₀' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀' l p → l₀' = l₀) ∧
    ∀ l l' l₀ l₀' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p → _root_.GlobalTheory.Models.IsPrimeToPart l₀' l' p → l.Dvd l' →
      l₀.Dvd l₀' := by
  intro E _ _ _ H p hp
  refine ⟨fun l hl => ?_, fun l l₀ h₀ => ?_, fun l l' l₀ l₀' h₀ h₀' hd => ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt at hl
    exact ⟨_root_.GlobalTheory.Models.divisorLevel l _ (Nat.ordCompl_dvd _ _) hl, rfl, rfl, rfl⟩
  · unfold _root_.GlobalTheory.Models.IsPrimeToPart at h₀ ⊢
    obtain ⟨hA, hM, hMb⟩ := h₀
    have hl : l.M ≠ 0 := by have := l.three_le; omega
    refine ⟨?_, ?_, fun l₀' ⟨hA', hM', hMb'⟩ => ?_⟩
    · unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.Dvd
      refine ⟨hM ▸ Nat.ordCompl_dvd _ _, hMb ▸ le_sup_left, hA ▸ one_dvd _⟩
    · rw [hM]
      exact (Nat.coprime_ordCompl hp hl).symm
    · have e : l₀'.M = l₀.M := hM'.trans hM.symm
      exact level_ext' e (by rw [hMb', hMb, e]) (hA'.trans hA.symm)
  · unfold _root_.GlobalTheory.Models.IsPrimeToPart at h₀ h₀'
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.Dvd at hd ⊢
    obtain ⟨hA, hM, hMb⟩ := h₀
    obtain ⟨hA', hM', hMb'⟩ := h₀'
    obtain ⟨hdM, hdMb, -⟩ := hd
    have hmd : l₀.M ∣ l₀'.M := by
      rw [hM, hM']
      exact Nat.ordCompl_dvd_ordCompl_of_dvd hdM p
    refine ⟨hmd, ?_, by rw [hA]; exact one_dvd _⟩
    rw [hMb, hMb']
    exact sup_le (hdMb.trans le_sup_left)
      (le_sup_of_le_right (Ideal.span_singleton_le_span_singleton.mpr (Nat.cast_dvd_cast hmd)))

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMonoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.primeToPart_level_exists_unique_mono : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p : ℕ), p.Prime → (∀ l : Level H, l.GoodAt p → ∃ l₀ : Level H, IsPrimeToPart l₀ l p) ∧ (∀ l l₀ : Level H, IsPrimeToPart l₀ l p → l₀.Dvd l ∧ l₀.M.Coprime p ∧ ∀ l₀' : Level H, IsPrimeToPart l₀' l p → l₀' = l₀) ∧ ∀ l l' l₀ l₀' : Level H, IsPrimeToPart l₀ l p → IsPrimeToPart l₀' l' p → l.Dvd l' → l₀.Dvd l₀' := by
  first | exact @GlobalTheory.Models.primeToPart_spec | exact GlobalTheory.Models.primeToPart_spec | (intros; apply GlobalTheory.Models.primeToPart_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangent
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.InvField

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le (f ≫ g) (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  rw [pbT_of_le (𝟙 Y) (O := O) (O₀ := O) le_rfl]
  exact (congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_eq_app (𝟙 Y) (U := O))).trans rfl

theorem pbT_eq_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O : Y.Opens} (s : Γ(Y, O)) :
    pbT f s (f ⁻¹ᵁ O) = (f.app O).hom s := by
  rw [pbT_of_le f le_rfl, Scheme.Hom.appLE_eq_app]

theorem constFn_spMap {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (φ : R →+* S)
    (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  rw [h] at h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  unfold constFn
  rw [← h3, h2]

theorem constFn_mul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R)
    (O : Y.Opens) (a b : R) : constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp [constFn]

theorem constFn_zero {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R)
    (O : Y.Opens) : constFn q O 0 = 0 := by
  simp [constFn]

theorem aux {K : Type} [Field K] {Y Y' : Scheme.{0}} (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ T : Y' ⟶ Y)
    (j : Y ⟶ Y') (hp : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (hρ : j ≫ ρ = 𝟙 Y)
    (hπ : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) (hT : j ≫ T = 𝟙 Y) (hq : T ≫ q = ρ ≫ q)
    (P : (∀ W : Y.Opens, Γ(Y, W) → Γ(Y, W)) → Prop)
    (hP : ∀ dd, P dd ↔ ∀ (W : Y.Opens) (f : Γ(Y, W)), pbT T f (ρ ⁻¹ᵁ W) =
      pbT ρ f (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ (dd W f) (ρ ⁻¹ᵁ W)) :
    (∃ dd, P dd) ∧ ∀ dd, P dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(Y, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn q W a) = 0) ∧ ∀ dd', P dd' → dd' = dd := by
  obtain ⟨hO, -, hex⟩ := GlobalTheory.T.const_thickening_field_structure K Y Y' q π ρ j hp hρ hπ
  have hTW : ∀ W : Y.Opens, ρ ⁻¹ᵁ W ≤ T ⁻¹ᵁ W := fun W => by
    have := hO (T ⁻¹ᵁ W)
    rw [← Scheme.Hom.comp_preimage j T, hT, Scheme.Hom.id_preimage] at this
    exact this.le
  have hjW : ∀ W : Y.Opens, W ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ W) := fun W => by
    rw [← Scheme.Hom.comp_preimage, hρ, Scheme.Hom.id_preimage]
  have uniq : ∀ (W : Y.Opens) (a b b' : Γ(Y, W)),
      pbT ρ a (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ b (ρ ⁻¹ᵁ W) =
      pbT ρ a (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ b' (ρ ⁻¹ᵁ W) → b = b' := by
    intro W a b b' h
    simp only [pbT_eq_app] at h
    have := (hex W _).unique (y₁ := (a, b)) (y₂ := (a, b')) rfl h
    exact congrArg Prod.snd this
  have hee : ∀ O, constFn π O DualNumber.eps * constFn π O DualNumber.eps = 0 := fun O => by
    rw [← constFn_mul, DualNumber.eps_mul_eps, constFn_zero]
  refine ⟨?_, fun dd hd => ?_⟩
  · choose ab hab using fun W (f : Γ(Y, W)) => (hex W (pbT T f (ρ ⁻¹ᵁ W))).exists
    refine ⟨fun W f => (ab W f).2, (hP _).2 fun W f => ?_⟩
    have h := hab W f
    rw [← pbT_eq_app, ← pbT_eq_app] at h
    have h' := congrArg (fun s => pbT j s W) h
    simp only [pbT_add, pbT_mul] at h'
    rw [pbT_pbT j T (hTW W) (hjW W), pbT_pbT j ρ le_rfl (hjW W), hT, hρ, pbT_id, pbT_id,
      pbT_constFn π j (hjW W), hπ, constFn_spMap] at h'
    have e : (TrivSqZeroExt.fstHom K K K).toRingHom DualNumber.eps = 0 := by simp
    rw [e, constFn_zero, zero_mul, add_zero] at h'
    rw [h, ← h']
  · have hd' := (hP _).1 hd
    refine ⟨fun W f f' => uniq W (f + f') _ _ ?_, fun W f f' => uniq W (f * f') _ _ ?_,
      fun W W' f h => uniq W' (rsT f W') _ _ ?_, fun W a => uniq W (constFn q W a) _ _ ?_, fun dd' hd₁ => ?_⟩
    · rw [← hd', pbT_add, hd', hd', pbT_add, pbT_add]; ring
    · rw [← hd', pbT_mul, hd', hd', pbT_add, pbT_mul, pbT_mul, pbT_mul]
      linear_combination (pbT ρ (dd W f) (ρ ⁻¹ᵁ W) * pbT ρ (dd W f') (ρ ⁻¹ᵁ W)) * hee (ρ ⁻¹ᵁ W)
    · have h1 : ρ ⁻¹ᵁ W' ≤ ρ ⁻¹ᵁ W := ρ.preimage_mono h
      rw [← hd', pbT_rsT T h (hTW W'), pbT_rsT ρ h le_rfl, pbT_rsT ρ h le_rfl, ← rsT_pbT T (hTW W) h1, hd',
        rsT_add, rsT_mul, rsT_pbT ρ le_rfl h1, rsT_pbT ρ le_rfl h1, rsT_constFn π h1]
    · rw [← hd', pbT_constFn q T (hTW W), pbT_constFn q ρ le_rfl, hq, pbT_zero, mul_zero, add_zero]
    · funext W f
      exact uniq W f _ _ (((hP _).1 hd₁ W f).symm.trans (hd' W f))

theorem main : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd := by
  intro K _ A₀ _ v hv
  let s : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change spMap _ ≫ spMap _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have hs : s ≫ v = η[A₀] := Over.OverMorphism.ext hv
  let j : A₀ ⟶ epsR K ⊗ A₀ := lift (toUnit A₀ ≫ s) (𝟙 A₀)
  have hT : j ≫ ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀) = 𝟙 A₀ := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.assoc, hs, ← Hom.one_def, _root_.one_mul]
  refine aux A₀.hom (fst (epsR K) A₀).left (snd (epsR K) A₀).left
    ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀).left j.left ?_ ?_ ?_ ?_ ?_ (IsInvDer v) (fun _ => Iff.rfl)
  · exact (IsPullback.of_hasPullback (epsR K).hom A₀.hom).flip
  · rw [← Over.comp_left, lift_snd]; rfl
  · rw [← Over.comp_left, lift_fst, Over.comp_left, Over.toUnit_left]; rfl
  · rw [← Over.comp_left, hT]; rfl
  · rw [Over.w, Over.w]

end GlobalTheory.KS.InvField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_invariantVectorField_of_tangent : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd := by
  first | exact @GlobalTheory.KS.InvField.main | exact GlobalTheory.KS.InvField.main | (intros; apply GlobalTheory.KS.InvField.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ActDescent

variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]

theorem _root_.GlobalTheory.ActDescent.over_hom_ext {X Y : Over S} {X' : Scheme.{0}} {φ : X' ⟶ X.left} {p : X' ⟶ U}
    (h : IsPullback φ p X.hom j) {f g : X ⟶ Y} (hfg : φ ≫ f.left = φ ≫ g.left) : f = g := by
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip ‹Flat j›
  have : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹Surjective j›
  have := Flat.epi_of_flat_of_surjective φ
  exact Over.OverMorphism.ext ((cancel_epi φ).mp hfg)

omit [Flat j] [Surjective j] in
theorem _root_.GlobalTheory.ActDescent.pullback_map_left_fst {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback j).map a).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ a.left := by
  exact pullback.lift_fst _ _ _

variable (j) in
theorem _root_.GlobalTheory.ActDescent.pullback_map_injective (X Y : Over S) :
    Function.Injective ((Over.pullback j).map : (X ⟶ Y) → _) := by
  intro a b hab
  apply _root_.GlobalTheory.ActDescent.over_hom_ext (IsPullback.of_hasPullback X.hom j)
  rw [← _root_.GlobalTheory.ActDescent.pullback_map_left_fst, ← _root_.GlobalTheory.ActDescent.pullback_map_left_fst, hab]

private theorem mul_comp_of_descends_monHom {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ) (hH : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback H' H j ψ) (f' : G' ⟶ H') [IsMonHom f'] (f : G ⟶ H)
    (hf : f'.left ≫ ψ = φ ≫ f.left) (T : Over S) (x y : T ⟶ G) :
    (x * y) ≫ f = x ≫ f * y ≫ f := by
  have hT : IsPullback (pullback.fst T.hom j) (pullback.snd T.hom j) T.hom j :=
    IsPullback.of_hasPullback _ _
  apply _root_.GlobalTheory.ActDescent.over_hom_ext hT
  let T' : Over U := (Over.pullback j).obj T
  let ρ : Over.mk (T'.hom ≫ j) ⟶ T :=
    Over.homMk (pullback.fst T.hom j) (by simp [T', pullback.condition])
  let up : (T ⟶ G) → (T' ⟶ G') := fun z => Over.homMk
    (hG.1.lift (pullback.fst T.hom j ≫ z.left) T'.hom (by simp [T', pullback.condition]))
    (hG.1.lift_snd _ _ _)
  have hup : ∀ z : T ⟶ G, (up z).left ≫ φ = pullback.fst T.hom j ≫ z.left :=
    fun z => hG.1.lift_fst _ _ _
  have hpush : ∀ z : T ⟶ G, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG T' (up z) = ρ ≫ z :=
    fun z => Over.OverMorphism.ext (by exact hup z)
  have hpushH : ∀ z : T ⟶ G, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hH T' (up z ≫ f') = ρ ≫ z ≫ f := by
    intro z
    ext1
    change ((up z).left ≫ f'.left) ≫ ψ = pullback.fst T.hom j ≫ z.left ≫ f.left
    rw [Category.assoc, hf, ← Category.assoc, hup, Category.assoc]
  change (ρ ≫ (x * y) ≫ f).left = (ρ ≫ (x ≫ f * y ≫ f)).left
  rw [MonObj.comp_mul ρ (x ≫ f), ← hpushH x, ← hpushH y, ← map_mul, ← MonObj.mul_comp,
    ← Category.assoc, MonObj.comp_mul ρ x y, ← hpush x, ← hpush y, ← map_mul]
  change ((up x * up y).left ≫ φ) ≫ f.left = ((up x * up y) ≫ f').left ≫ ψ
  rw [Over.comp_left, Category.assoc, Category.assoc, hf]

theorem _root_.GlobalTheory.ActDescent.isMonHom_descend {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ) (hH : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback H' H j ψ) (f' : G' ⟶ H') [IsMonHom f'] (f : G ⟶ H)
    (hf : f'.left ≫ ψ = φ ≫ f.left) : IsMonHom f := by
  have key := mul_comp_of_descends_monHom hG hH f' f hf
  refine ⟨?_, ?_⟩
  · have h1 : (1 : 𝟙_ (Over S) ⟶ G) ≫ f = 1 := by
      have h := key (𝟙_ (Over S)) 1 1
      rw [_root_.one_mul] at h
      exact mul_eq_left.mp h.symm
    simpa [Hom.one_def] using h1
  · have h := key _ (fst G G) (snd G G)
    simpa [Hom.mul_def] using h

theorem _root_.GlobalTheory.ActDescent.exists_oAct {O : Type} [CommRing O] {G : Over S} [GrpObj G]
    {G' : Over U} [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ)
    (i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G') (hi : ∀ x, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) :
    ∃ a : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  choose g hg using hi
  have hpb := hG.1
  have hmon : ∀ x, IsMonHom (g x) := fun x =>
    haveI := i.hom x
    _root_.GlobalTheory.ActDescent.isMonHom_descend hG hG (i.act x) (g x) (hg x)
  refine ⟨⟨g, hmon, ?_, ?_, ?_⟩, hg⟩
  · apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    rw [← hg, i.one]
    simp
  · intro a b
    apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    rw [← hg, i.mul, Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, hg,
      Category.assoc]
  · intro a b
    apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    let ρ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hpb.w
    have hpush : ∀ c, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG G' (i.act c) = ρ ≫ g c :=
      fun c => Over.OverMorphism.ext (by exact hg c)
    change (ρ ≫ g (a + b)).left = (ρ ≫ (g a * g b)).left
    rw [MonObj.comp_mul, ← hpush, ← hpush, ← hpush, ← map_mul, i.add]

end GlobalTheory.ActDescent

namespace GlobalTheory

variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
theorem _root_.GlobalTheory.oAct_descend_of_generators : ∀ (O : Type) [CommRing O] (J : Type) (a : J → O) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K₀)) (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A₀] [GrpObj A] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A) (act₀ : J → (A₀ ⟶ A₀)), Subring.closure (Set.range a) = ⊤ → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A A₀ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → ∃ r : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A₀, (∀ j, r.act (a j) = act₀ j) ∧ ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left := by
  intro O _ J a K₀ K _ _ i A₀ A _ _ _ φ act act₀ hgen hG hact
  haveI : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap; infer_instance
  haveI : Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap; infer_instance
  let ρ : Over.mk (A.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) ⟶ A₀ := Over.homMk φ hG.1.w
  have hiff : ∀ (z : A ⟶ A) (g : A₀ ⟶ A₀), z.left ≫ φ = φ ≫ g.left →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG A z = ρ ≫ g := fun z g h => Over.OverMorphism.ext (by exact h)
  have hback : ∀ (z : A ⟶ A) (g : A₀ ⟶ A₀), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG A z = ρ ≫ g →
      z.left ≫ φ = φ ≫ g.left := fun z g h => by
    have h' := congrArg (fun m => m.left) h
    exact h'
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hD : ∀ c, ∃ g : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ g.left := by
    intro c
    have hc : c ∈ Subring.closure (Set.range a) := hgen ▸ Subring.mem_top c
    induction hc using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨act₀ k, hact k⟩
    | zero =>
      refine ⟨1, hback _ _ ?_⟩
      rw [h0, map_one, MonObj.comp_one]
    | one =>
      exact ⟨𝟙 _, by simp [act.one]⟩
    | add x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      refine ⟨g * g', hback _ _ ?_⟩
      rw [act.add, map_mul, hiff _ _ hg, hiff _ _ hg', MonObj.comp_mul]
    | neg x _ hx =>
      obtain ⟨g, hg⟩ := hx
      have hneg : act.act (-x) = (act.act x)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← act.add, add_neg_cancel, h0]
      refine ⟨g⁻¹, hback _ _ ?_⟩
      rw [hneg, map_inv, hiff _ _ hg, GrpObj.comp_inv]
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      refine ⟨g ≫ g', ?_⟩
      rw [act.mul, Over.comp_left, Over.comp_left, Category.assoc, hg', ← Category.assoc, hg,
        Category.assoc]
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.ActDescent.exists_oAct hG act hD
  refine ⟨r, fun k => ?_, hr⟩
  apply _root_.GlobalTheory.ActDescent.over_hom_ext hG.1
  rw [← hr, hact]

end GlobalTheory
end
end
