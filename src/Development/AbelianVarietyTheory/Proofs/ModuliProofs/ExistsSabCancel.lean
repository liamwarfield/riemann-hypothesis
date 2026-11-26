module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.ObjMaps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab_id {S : Scheme.{0}} (t : SAB H S) : ∃ m : SABMap t t (𝟙 S), m.φ = 𝟙 _ :=
  ⟨ObjComp.sabMapId t, rfl⟩

theorem exists_sab_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m : SABMap t' t f) (m' : SABMap t'' t' g) : ∃ n : SABMap t'' t (g ≫ f), n.φ = m'.φ ≫ m.φ :=
  sabComp pullCubComp E H S S' S'' t t' t'' f g m m'

theorem exists_sab_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m : SABMap t' t f) (n : SABMap t'' t (g ≫ f)) : ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ :=
  sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n

end GlobalTheory.ObjMaps

namespace GlobalTheory

theorem ObjMaps.id_comp_cancel :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ o _ _ =>
    ⟨⟨ObjComp.objMapId o, rfl⟩, fun _ _ m => ⟨ObjComp.objMap_comp m, ObjComp.objMap_cancel m⟩⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LiePull

theorem exists_pushEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f) :
    ∃ e : (T ⟶ G') ≃* (Over.mk g ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  subst hg
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => ?_, fun y => ?_⟩, fun x => rfl⟩
  · have e' : x.left ≫ φ = y.left ≫ φ := congrArg (fun z => z.left) e
    exact Over.OverMorphism.ext (h.1.hom_ext e' ((Over.w x).trans (Over.w y).symm))
  · exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem basis_transport {A B k : Type} [Monoid A] [Monoid B] (e : A ≃* B) {P : A → Prop} {Q : B → Prop}
    {R : k → A → A → Prop} {R' : k → B → B → Prop} (hP : ∀ x, P x ↔ Q (e x))
    (hR : ∀ c x y, R c x y ↔ R' c (e x) (e y)) (n : ℕ)
    (H : ∃ v : Fin n → A, (∀ i, P (v i)) ∧ ∀ w, P w →
      ∃! c : Fin n → k, ∃ u : Fin n → A, (∀ i, R (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod) :
    ∃ v : Fin n → B, (∀ i, Q (v i)) ∧ ∀ w, Q w →
      ∃! c : Fin n → k, ∃ u : Fin n → B, (∀ i, R' (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod := by
  obtain ⟨v, hv, H⟩ := H
  refine ⟨fun i => e (v i), fun i => (hP _).1 (hv i), fun w hw => ?_⟩
  obtain ⟨w, rfl⟩ := e.surjective w
  have pr : ∀ u : Fin n → A, e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  refine (existsUnique_congr fun c => ⟨?_, ?_⟩).1 (H w ((hP _).2 hw))
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
    rw [pr, hw]
    simp

theorem lieMult_pull : ∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n := by
  intro O _ S S' G G' _ _ f φ a a' h hact k _ x τ n
  obtain ⟨e, he⟩ := exists_pushEquiv h (epsPt x) (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : ∀ c : k, spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap k (DualNumber k)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (c : k) (u v : epsPt x ⟶ G'), u.left = spMap (epsScale c) ≫ v.left ↔
      (e u).left = spMap (epsScale c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScale c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc c))
  have hP : ∀ v : epsPt x ⟶ G', IsLieEigen a' x τ v ↔ IsLieEigen a (x ≫ f) τ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
      refine (congrArg (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ ·) (Over.w v)).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
    · have E : e (v ≫ a'.act c) = e v ≫ a.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
      rw [hR, E]
  constructor
  · exact basis_transport e (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left) hP hR n
  · exact basis_transport e.symm (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (fun v => by rw [hP, e.apply_symm_apply])
      (fun c u v => by rw [hR, e.apply_symm_apply, e.apply_symm_apply]) n

end GlobalTheory.LiePull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isDomain_and_isIntegrallyClosed_stalk_Sp (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (y : Sp A) :
    IsDomain ((Sp A).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp A).presheaf.stalk y) := by
  have hy : (y.asIdeal : Ideal A).IsPrime := y.isPrime
  let _ : Algebra A ((Sp A).presheaf.stalk y) := StructureSheaf.stalkAlgebra A y
  have : IsLocalization.AtPrime ((Sp A).presheaf.stalk y) (y.asIdeal : Ideal A) :=
    StructureSheaf.IsLocalization.to_stalk A y
  exact isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (B := A) (y.asIdeal : Ideal A)
    ((Sp A).presheaf.stalk y)

theorem isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s →
      IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X := by
  intro k _ X s hs
  have : Smooth s := hs
  have hN : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (fun y => isDomain_and_isIntegrallyClosed_stalk_Sp k y)
  refine ⟨?_, ⟨fun x => (hN x).1, fun x => (hN x).2⟩, ?_⟩
  · have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hN x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  · have : IsLocallyNoetherian (Sp k) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian s

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LatticeTorsion

variable {S : Scheme.{0}}

theorem prop_powObj (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] (X : Over S) (hX : P X.hom) : ∀ k, P (Out.powObj X k).hom
  | 0 => P.id_mem S
  | k + 1 => by
    change P (pullback.fst X.hom (Out.powObj X k).hom ≫ X.hom)
    exact P.comp_mem _ _ (P.pullback_fst _ _ (prop_powObj P X hX k)) hX

theorem existsUnique_torsion (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} (x : T ⟶ G)
    (hx : x ^ n = 1) : ∃! y : T ⟶ torsion G n, y ≫ torsion.ι G n = x := by
  refine ⟨pullback.lift x (toUnit T) ((GrpTangent.comp_mulN x n).trans hx),
    pullback.lift_fst _ _ _, fun y hy => ?_⟩
  exact pullback.hom_ext (hy.trans (pullback.lift_fst _ _ _).symm) (toUnit_unique _ _)

theorem torsionι_pow_eq_one (G : Over S) [GrpObj G] (n : ℕ) : torsion.ι G n ^ n = 1 := by
  rw [← GrpTangent.comp_mulN]
  refine pullback.condition.trans ?_
  rw [toUnit_unique (pullback.snd _ _) (toUnit _)]
  rfl

theorem eq_prod_zpow {La I A : Type} [AddCommGroup La] [Fintype I] [CommGroup A]
    (b : Module.Basis I ℤ La) (f : La → A) (hf : ∀ a c, f (a + c) = f a * f c) (a : La) :
    f a = ∏ i, f (b i) ^ (b.repr a i) := by
  let φ : Multiplicative La →* A := MonoidHom.mk' (fun x => f x.toAdd) fun x y => hf _ _
  have h : ∀ x, f x = φ (Multiplicative.ofAdd x) := fun _ => rfl
  conv_lhs => rw [← b.sum_repr a]
  simp only [h, ofAdd_sum, ofAdd_zsmul, map_prod, map_zpow]

end GlobalTheory.LatticeTorsion

namespace GlobalTheory


open LatticeTorsion in
theorem exists_finiteEtale_latticeTorsionHom :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → IsUnit (n : Γ(S, ⊤)) → ∃ (Z : Over S) (et : La → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧ ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a + c) = et' a * et' c) → (∀ a, et' a ^ n = 1) → ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a := by
  intro S G _ _ n La _ _ _ hG hn
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  let b := Module.finBasis ℤ La
  let r := Module.finrank ℤ La
  let Z := Out.powObj (torsion G n) r
  let x : Fin r → (Z ⟶ G) := fun i => Out.powPr (torsion G n) i ≫ torsion.ι G n
  have hx : ∀ i, x i ^ n = 1 := fun i => by
    rw [← MonObj.comp_pow, torsionι_pow_eq_one, MonObj.comp_one]
  let et : La → (Z ⟶ G) := fun a => ∏ i, x i ^ (b.repr a i)
  have hadd : ∀ a c, et (a + c) = et a * et c := fun a c => by
    simp only [et, map_add (f := _), Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hb : ∀ i, et (b i) = x i := fun i => by
    simp only [et, Module.Basis.repr_self]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]
    simp
  refine ⟨Z, et, prop_powObj @IsFinite _ hfin r, prop_powObj @Etale _ het r, hadd, fun a => ?_,
    fun T et' hadd' hpow' => ?_⟩
  · simp only [et, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  · choose y hy hyu using fun i : Fin r => existsUnique_torsion G n (et' (b i)) (hpow' _)
    let h : T ⟶ Z := (Out.powIsLimit (torsion G n) r).lift (Fan.mk T y)
    have hh : ∀ i, h ≫ Out.powPr (torsion G n) i = y i := fun i =>
      (Out.powIsLimit (torsion G n) r).fac (Fan.mk T y) ⟨i⟩
    refine ⟨h, fun a => ?_, fun h' hh' => ?_⟩
    · rw [eq_prod_zpow b (fun a => h ≫ et a) (fun a c => by rw [hadd, MonObj.comp_mul]) a,
        eq_prod_zpow b et' hadd' a]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hb, ← hy i, ← hh i, Category.assoc]
    · refine (Out.powIsLimit (torsion G n) r).hom_ext fun ⟨i⟩ => ?_
      refine (hyu i _ ?_).trans (hh i).symm
      have := hh' (b i)
      rw [hb] at this
      exact (Category.assoc _ _ _).trans this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SimAlg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem modN_zero (n : ℕ) : D.ModN n 0 := ⟨0, by simp⟩

theorem modN_add {n : ℕ} {x y : D.La} (hx : D.ModN n x) (hy : D.ModN n y) : D.ModN n (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by rw [smul_add]⟩

theorem modN_neg {n : ℕ} {x : D.La} (hx : D.ModN n x) : D.ModN n (-x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, by rw [smul_neg]⟩

theorem modN_map {n : ℕ} {x : D.La} (f : D.La →ₗ[𝓞 E] D.La) (hx : D.ModN n x) : D.ModN n (f x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨f a, by rw [map_nsmul]⟩

theorem modN_of_mul {n m : ℕ} {x : D.La} (hx : D.ModN (n * m) x) : D.ModN n x := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨m • a, by rw [mul_smul]⟩

theorem dvd_form_sub {n : ℕ} {x x' y y' : D.La} (hx : D.ModN n (x - x')) (hy : D.ModN n (y - y')) :
    (n : ℤ) ∣ D.EF x y - D.EF x' y' := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have h1 : x = x' + n • a := by rw [← ha]; abel
  have h2 : y = y' + n • b := by rw [← hb]; abel
  refine ⟨D.EF x' b + D.EF a y' + n * D.EF a b, ?_⟩
  rw [h1, h2]
  simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
  ring

theorem exists_form_eq_one (h : 1 ≤ D.p + D.q) : ∃ a b : D.La, D.EF a b = 1 := by
  haveI := D.fin
  haveI := D.proj
  haveI : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.IsTorsionFree ℤ D.La :=
    Function.Injective.moduleIsTorsionFree D.EF D.unimod.1 (fun r x => map_smul _ r x)
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis ℤ D.La
  obtain ⟨i⟩ := B.index_nonempty
  obtain ⟨a, ha⟩ := D.unimod.2 (B.coord i)
  exact ⟨a, B i, by rw [ha]; simp⟩

theorem dvd_mult_inv (g : Sim D) {n : ℕ} (hn : 0 < n) {a b : D.La} (hab : D.EF a b = 1)
    (h : D.La →ₗ[𝓞 E] D.La) (hh : ∀ x, D.ModN n (g.f n (h x) - x)) :
    (n : ℤ) ∣ g.ν n * D.EF (h a) (h b) - 1 := by
  have h1 := g.mult n hn (h a) (h b)
  have h2 := dvd_form_sub (hh a) (hh b)
  rw [hab] at h2
  obtain ⟨c, hc⟩ := dvd_sub h2 h1
  exact ⟨c, by linear_combination hc⟩

theorem dvd_mult_tower (g : Sim D) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {a b : D.La} (hab : D.EF a b = 1) :
    (n : ℤ) ∣ g.ν (n * m) - g.ν n := by
  have h1 := g.mult n hn a b
  have h2 : (n : ℤ) ∣ _ := Dvd.dvd.trans (by push_cast; exact Dvd.intro _ rfl) (g.mult (n * m) (Nat.mul_pos hn hm) a b)
  have h3 := dvd_form_sub (g.tower n m hn hm a) (g.tower n m hn hm b)
  rw [hab] at h1 h2
  obtain ⟨c, hc⟩ := dvd_add (dvd_sub h3 h2) h1
  exact ⟨c, by linear_combination hc⟩

def one (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower n _ _ _ a := by simpa using modN_zero n
  inv n _ := ⟨LinearMap.id, fun a => by simpa using modN_zero n⟩
  mult n _ a b := by simp

def mul (g g' : Sim D) : Sim D where
  f n := g.f n ∘ₗ g'.f n
  ν n := g.ν n * g'.ν n
  tower n m hn hm a := by
    have h1 := g.tower n m hn hm (g'.f (n * m) a)
    have h2 := modN_map (g.f n) (g'.tower n m hn hm a)
    convert modN_add h1 h2 using 1
    simp
  inv n hn := by
    obtain ⟨h, hh⟩ := g.inv n hn
    obtain ⟨h', hh'⟩ := g'.inv n hn
    refine ⟨h' ∘ₗ h, fun a => ⟨?_, ?_⟩⟩
    · convert modN_add (modN_map h' (hh (g'.f n a)).1) (hh' a).1 using 1
      simp
    · convert modN_add (modN_map (g.f n) (hh' (h a)).2) (hh a).2 using 1
      simp
  mult n hn a b := by
    have h1 := g.mult n hn (g'.f n a) (g'.f n b)
    have h2 := Dvd.dvd.mul_left (g'.mult n hn a b) (g.ν n)
    obtain ⟨c, hc⟩ := dvd_add h1 h2
    exact ⟨c, by simp only [LinearMap.comp_apply]; linear_combination hc⟩

theorem exists_inv (g : Sim D) {a b : D.La} (hab : D.EF a b = 1) :
    ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧
      (n : ℤ) ∣ g.ν n * g'.ν n - 1 := by
  have hex : ∀ n : ℕ, ∃ h : D.La →ₗ[𝓞 E] D.La, 0 < n →
      ∀ a, D.ModN n (h (g.f n a) - a) ∧ D.ModN n (g.f n (h a) - a) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨h, hh⟩ := g.inv n hn
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose h hh using hex
  have hν : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ g.ν n * D.EF (h n a) (h n b) - 1 := fun n hn =>
    dvd_mult_inv g hn hab (h n) fun x => (hh n hn x).2
  refine ⟨⟨h, fun n => D.EF (h n a) (h n b), ?_, ?_, ?_⟩, fun n hn => ⟨hh n hn, hν n hn⟩⟩
  · intro n m hn hm x
    have h1 := modN_neg (hh n hn (h (n * m) x)).1
    have h2 := modN_neg (modN_map (h n) (g.tower n m hn hm (h (n * m) x)))
    have h3 := modN_map (h n) (modN_of_mul (hh (n * m) (Nat.mul_pos hn hm) x).2)
    convert modN_add (modN_add h1 h2) h3 using 1
    simp only [map_sub]
    abel
  · intro n hn
    exact ⟨g.f n, fun x => ⟨(hh n hn x).2, (hh n hn x).1⟩⟩
  · intro n hn x y
    have h1 := Dvd.dvd.mul_left (g.mult n hn (h n x) (h n y)) (D.EF (h n a) (h n b))
    have h2 := Dvd.dvd.mul_left (dvd_form_sub (hh n hn x).2 (hh n hn y).2) (D.EF (h n a) (h n b))
    have h3 := Dvd.dvd.mul_right (hν n hn) (D.EF (h n x) (h n y))
    obtain ⟨c, hc⟩ := dvd_sub (dvd_sub h2 h1) h3
    exact ⟨c, by linear_combination hc⟩

theorem sim_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1) := by
  intro E _ _ _ H D hpq
  obtain ⟨a, b, hab⟩ := exists_form_eq_one hpq
  refine ⟨fun g n m hn hm => ⟨dvd_mult_tower g hn hm hab, ?_⟩, ⟨one D, fun _ => ⟨rfl, rfl⟩⟩,
    fun g g' => ⟨mul g g', fun _ => ⟨rfl, rfl⟩⟩, fun g => exists_inv g hab⟩
  obtain ⟨h, hh⟩ := g.inv n hn
  obtain ⟨c, hc⟩ := dvd_mult_inv g hn hab h fun x => (hh x).2
  exact ⟨D.EF (h a) (h b), -c, by linear_combination hc⟩

end GlobalTheory.SimAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {S : Scheme.{0}}

def ClopenCond (T : Over S) (P : ∀ T' : Over S, (T' ⟶ T) → Prop) : Prop :=
  ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T), P T' h ↔ Set.range h.left ⊆ U

theorem ClopenCond.congr {T : Over S} {P P' : ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ClopenCond T P)
    (e : ∀ T' h, P' T' h ↔ P T' h) : ClopenCond T P' := by
  obtain ⟨U, hU, H⟩ := h
  exact ⟨U, hU, fun T' h => (e T' h).trans (H T' h)⟩

theorem ClopenCond.and {T : Over S} {P P' : ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ClopenCond T P)
    (h' : ClopenCond T P') : ClopenCond T fun T' h => P T' h ∧ P' T' h := by
  obtain ⟨U, hU, H⟩ := h
  obtain ⟨U', hU', H'⟩ := h'
  refine ⟨U ⊓ U', hU.inter hU', fun T' h => ?_⟩
  beta_reduce
  rw [H, H', TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]

theorem ClopenCond.forall_finite {T : Over S} {J : Type} [Finite J] {P : J → ∀ T' : Over S, (T' ⟶ T) → Prop}
    (h : ∀ i, ClopenCond T (P i)) : ClopenCond T fun T' h => ∀ i, P i T' h := by
  choose U hU H using h
  refine ⟨⟨⋂ i, (U i : Set T.left), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, isClosed_iInter hU,
    fun T' h => ?_⟩
  simp only [H, TopologicalSpace.Opens.coe_mk, Set.subset_iInter_iff]

theorem ClopenCond.forall_of_finite {T : Over S} {J κ : Type} [Finite κ] (q : J → κ)
    {P : J → ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ∀ i, ClopenCond T (P i))
    (hq : ∀ i j, q i = q j → ∀ T' h, P i T' h → P j T' h) : ClopenCond T fun T' h => ∀ i, P i T' h := by
  refine (ClopenCond.forall_finite (J := Set.range q) fun c => h c.2.choose).congr fun T' h => ?_
  exact ⟨fun H c => H _, fun H i => hq _ _ (⟨i, rfl⟩ : q i ∈ Set.range q).choose_spec T' h (H ⟨q i, i, rfl⟩)⟩

theorem exists_finite_mod (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    ∃ (κ : Type) (_ : Finite κ) (q : M → κ), ∀ a a', q a = q a' → ∃ c, a' = a + n • c := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let b := Module.Free.chooseBasis ℤ M
  refine ⟨Module.Free.ChooseBasisIndex ℤ M → ZMod n, inferInstance, fun a i => (b.repr a i : ZMod n),
    fun a a' h => ?_⟩
  have h1 : ∀ i, ∃ c : ℤ, b.repr a' i - b.repr a i = n * c := fun i =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun h i)
  choose c hc using h1
  refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
  rw [map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
  simp only [Module.Basis.equivFun_apply, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  linarith [hc i]

theorem clopenCond_eq {T Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (u u' : T ⟶ Z) :
    ClopenCond T fun _ h => h ≫ u = h ≫ u' := by
  refine ⟨(FinEt.agreeι u u').opensRange, (FinEt.agreeι u u').isClosedEmbedding.isClosed_range, fun T' h => ?_⟩
  refine Iff.trans ?_ (FinEt.comp_eq_comp_iff_range u u' h.left)
  exact ⟨fun e => congrArg CommaMorphism.left e, fun e => Over.OverMorphism.ext e⟩

def RepTors (G : Over S) [GrpObj G] (n : ℕ) (La : Type) [AddCommGroup La] (Z : Over S) (et : La → (Z ⟶ G)) : Prop :=
  IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧
    ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a + c) = et' a * et' c) → (∀ a, et' a ^ n = 1) →
      ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a

theorem RepTors.ext {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S} {et : La → (Z ⟶ G)}
    (R : RepTors G n La Z et) {T : Over S} {u u' : T ⟶ Z} (h : ∀ a, u ≫ et a = u' ≫ et a) : u = u' :=
  (R.2.2.2.2 T (fun a => u' ≫ et a) (fun a c => by rw [R.2.2.1, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one])).unique h fun _ => rfl

theorem RepTors.clopenCond {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S}
    {et : La → (Z ⟶ G)} (R : RepTors G n La Z et) {T : Over S} (x y : La → (T ⟶ G))
    (hx : ∀ a c, x (a + c) = x a * x c) (hx' : ∀ a, x a ^ n = 1)
    (hy : ∀ a c, y (a + c) = y a * y c) (hy' : ∀ a, y a ^ n = 1) :
    ClopenCond T fun _ h => ∀ a, h ≫ x a = h ≫ y a := by
  obtain ⟨u, hu, -⟩ := R.2.2.2.2 T x hx hx'
  obtain ⟨u', hu', -⟩ := R.2.2.2.2 T y hy hy'
  have := R.1
  have := R.2.1
  refine (clopenCond_eq u u').congr fun T' h => ⟨fun H => R.ext fun a => ?_, fun H a => ?_⟩
  · rw [Category.assoc, Category.assoc, hu, hu', H]
  · rw [← hu, ← hu', ← Category.assoc, H, Category.assoc]

theorem exists_lift_geom {W Z : Scheme.{0}} (p : W ⟶ Z) [IsFinite p] {k : Type} [Field k] [IsAlgClosed k]
    (z : Sp k ⟶ Z) (hz : Set.range z ⊆ Set.range p) : ∃ w : Sp k ⟶ W, w ≫ p = z := by
  let pt : Sp k := (⊥ : PrimeSpectrum k)
  have h1 : pt ∈ Set.range (pullback.snd p z) := by
    rw [Scheme.Pullback.range_snd]
    exact hz ⟨pt, rfl⟩
  obtain ⟨y, -⟩ := h1
  have : Nonempty (pullback p z : Scheme) := ⟨y⟩
  have : IsAffine (pullback p z) := isAffine_of_isAffineHom (pullback.snd p z)
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := (pullback p z : Scheme))).exists_closed_singleton Set.univ_nonempty
  refine ⟨pointOfClosedPoint (pullback.snd p z) x hx ≫ pullback.fst p z, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem exists_image {W Z : Over S} [IsFinite W.hom] [Etale W.hom] [IsFinite Z.hom] [Etale Z.hom] (p : W ⟶ Z) :
    ∃ U : Z.left.Opens, IsClosed (U : Set Z.left) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
      (z : Over.mk x ⟶ Z), Set.range z.left ⊆ U ↔ ∃ w : Over.mk x ⟶ W, w ≫ p = z := by
  have := FinEt.isFinite_left p
  have := FinEt.etale_left p
  refine ⟨⟨Set.range p.left, p.left.isOpenMap.isOpen_range⟩, p.left.isClosedMap.isClosed_range,
    fun k _ _ x z => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨w, hw⟩ := exists_lift_geom p.left z.left h
    refine ⟨Over.homMk w ?_, Over.OverMorphism.ext hw⟩
    show w ≫ W.hom = x
    rw [← Over.w p, ← Category.assoc, hw]
    exact Over.w z
  · rintro ⟨w, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨w.left y, by simp⟩

theorem exists_sub {Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (U : Z.left.Opens) (hU : IsClosed (U : Set Z.left)) :
    ∃ (V : Over S) (i : V ⟶ Z), IsFinite V.hom ∧ Etale V.hom ∧ Mono i ∧
      ∀ (T : Over S) (h : T ⟶ Z), Set.range h.left ⊆ U ↔ ∃ h' : T ⟶ V, h' ≫ i = h := by
  have hc : IsClosedImmersion U.ι := .of_isPreimmersion _ (by simpa using hU)
  refine ⟨Over.mk (U.ι ≫ Z.hom), Over.homMk U.ι rfl, inferInstanceAs (IsFinite (U.ι ≫ Z.hom)),
    inferInstanceAs (Etale (U.ι ≫ Z.hom)), ?_, fun T h => ?_⟩
  · have : Mono (Over.homMk U.ι rfl : Over.mk (U.ι ≫ Z.hom) ⟶ Z).left := inferInstanceAs (Mono U.ι)
    exact Over.mono_of_mono_left _
  · rw [FinEt.range_subset_iff_factors]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨Over.homMk t ?_, Over.OverMorphism.ext ht⟩
      show t ≫ U.ι ≫ Z.hom = T.hom
      rw [← Category.assoc, ht, Over.w h]
    · rintro ⟨t, ht⟩
      exact ⟨t.left, congrArg CommaMorphism.left ht⟩

theorem range_subset_of_geom {T Z : Over S} (h : T ⟶ Z) (U : Set Z.left)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ T), Set.range (y ≫ h).left ⊆ U) :
    Set.range h.left ⊆ U := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨k, _, _, a, ha⟩ := FinEt.exists_algClosed_point T.left t
  obtain ⟨p, rfl⟩ : t ∈ Set.range a := by rw [ha]; rfl
  exact H k (a ≫ T.hom) (Over.homMk a rfl) ⟨p, by simp⟩

theorem finiteEtale_tensor (X Y : Over S) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsFinite (X ⊗ Y).hom ∧ Etale (X ⊗ Y).hom :=
  ⟨inferInstanceAs (IsFinite (pullback.fst X.hom Y.hom ≫ X.hom)),
    inferInstanceAs (Etale (pullback.fst X.hom Y.hom ≫ X.hom))⟩

end GlobalTheory.LevCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sab_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) {e : S'' ⟶ S} (he : g ≫ f = e) :
    ∃ n : SABMap t'' t e, n.φ = m'.φ ≫ m.φ := by
  subst he
  exact sabComp pullCubComp E H S S' S'' t t' t'' f g m m'

theorem sab_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {e : S'' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t e) (g : S'' ⟶ S') (he : g ≫ f = e) :
    ∃ m' : SABMap t'' t' g, m'.φ ≫ m.φ = n.φ := by
  subst he
  obtain ⟨m', h⟩ := sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n
  exact ⟨m', h.symm⟩

theorem sec_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) (x : 𝟙_ (Over S'') ⟶ t''.G) (y : 𝟙_ (Over S') ⟶ t'.G)
    (h : x.left ≫ m'.φ ≫ m.φ = g ≫ y.left ≫ m.φ) : x.left ≫ m'.φ = g ≫ y.left := by
  apply m.cart.1.hom_ext
  · simpa only [Category.assoc] using h
  · have a₁ : x.left ≫ t''.G.hom = 𝟙 _ := Over.w x
    have a₂ : y.left ≫ t'.G.hom = 𝟙 _ := Over.w y
    rw [Category.assoc, m'.cart.1.w, ← Category.assoc, a₁, Category.assoc, a₂]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_pow {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (x : 𝟙_ (Over S') ⟶ t'.G) (y : 𝟙_ (Over S) ⟶ t.G)
    (h : x.left ≫ m.φ = f ≫ y.left) (k : ℕ) : (x ^ k).left ≫ m.φ = f ≫ (y ^ k).left := by
  let U : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) :=
    Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e : pushHom m.cart _ x = preHom U y := Over.OverMorphism.ext h
  have e' : pushHom m.cart _ (x ^ k) = preHom U (y ^ k) := by rw [map_pow, map_pow, e]
  exact congrArg (fun z => z.left) e'

theorem zeta_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : zeta a = zeta b ^ (b / a) := by
  obtain ⟨k, rfl⟩ := h
  have ha : a ≠ 0 := by rintro rfl; simp at hb
  have hk : k ≠ 0 := by rintro rfl; simp at hb
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha), zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  push_cast
  field_simp

noncomputable def baseOf (l : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) : Base l F where
  unit n hn := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
  ρ := (IntermediateField.inclusion h).toRingHom (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := (IntermediateField.inclusion h).toRingHom (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective (RingHom.injective _)

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem spMap_inclusion_self {F : IntermediateField ℚ ℂ} (h : F ≤ F) :
    spMap (IntermediateField.inclusion h).toRingHom = 𝟙 (Sp F) := by
  rw [← spMap_id']
  exact congrArg spMap (RingHom.ext fun x => Subtype.ext (IntermediateField.coe_inclusion h x))

theorem baseOf_rho_coe (l : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) :
    (((baseOf l F h).ρ : F) : ℂ) = H.rt0 := IntermediateField.coe_inclusion h (baseKA l).ρ

theorem baseOf_rho (l l₂ : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) (h₂ : KA l₂ ≤ F) :
    (baseOf l F h).ρ = (baseOf l₂ F h₂).ρ :=
  Subtype.ext ((baseOf_rho_coe l F h).trans (baseOf_rho_coe l₂ F h₂).symm)

theorem baseOf_zeta (l l₂ : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) (h₂ : KA l₂ ≤ F) (hd : l.A ∣ l₂.A) :
    (baseOf l F h).ζ = (baseOf l₂ F h₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (IntermediateField.coe_inclusion h _).trans ((zeta_dvd l₂.A_pos hd).trans
    (congrArg (· ^ (l₂.A / l.A)) (IntermediateField.coe_inclusion h₂ (baseKA l₂).ζ).symm)))

def ObjCompSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)

variable {D : Datum H} {l l₂ : Level H}

def Represents {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {s : X ⟶ Sp B} (o : Obj D l b s) : Prop :=
  ∀ (S : Scheme.{0}) (s' : S ⟶ Sp B) (o' : Obj D l b s'), IsReduced S →
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o' o f)

theorem represents_pullback (hC : ObjCompSt) (Xo : Moduli D l) {B : Type} [CommRing B] {b : Base l B} (j : KA l →+* B)
    (hR : ∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S →
      ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f))
    {s : pullback Xo.s (spMap j) ⟶ Sp B} (hs : s = pullback.snd _ _) (o : Obj D l b s)
    (mo : ObjMap o Xo.univ (pullback.fst _ _)) : Represents o := by
  subst hs
  intro S s' o' hS
  obtain ⟨g, ⟨hg, ⟨u⟩⟩, huniq⟩ := hR S s' o' hS
  have hl : pullback.lift g s' hg ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  refine ⟨pullback.lift g s' hg, ⟨pullback.lift_snd _ _ _, ?_⟩, ?_⟩
  · obtain ⟨u', -⟩ := ((hC E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 _ (pullback.lift g s' hg) mo).2
      (hl.symm ▸ u)
    exact ⟨u'⟩
  · rintro f ⟨hf, ⟨v⟩⟩
    apply pullback.hom_ext
    · rw [hl]
      obtain ⟨v', -⟩ := ((hC E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 _ f mo).1 v
      exact huniq _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hf], ⟨v'⟩⟩
    · rw [hf, pullback.lift_snd]

theorem iso_cover (hC : ObjCompSt) {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} (k k' : ℕ)
    {X X₂ Y : Scheme.{0}} {s : X ⟶ Sp B} {r : X₂ ⟶ X} {π : Y ⟶ X} (o : Obj D l b s) (o₂ : Obj D l₂ b₂ (r ≫ s))
    (oc : Obj D l₂ b₂ (π ≫ s)) (o₁ : Obj D l b (π ≫ s)) (n : ObjMap o₁ o π)
    (m : SABMap o₂.t o.t r) (mc : SABMap oc.t o.t π)
    (hm : (∀ a, (o₂.eta a ^ k).left ≫ m.φ = r ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ k').left ≫ m.φ = r ≫ (o.etaA a).left))
    (hmc : (∀ a, (oc.eta a ^ k).left ≫ mc.φ = π ≫ (o.eta a).left) ∧
      (∀ a, (oc.etaA a ^ k').left ≫ mc.φ = π ≫ (o.etaA a).left))
    (hX : Represents o) (hX₂ : Represents o₂) (rX₂ : IsReduced X₂) (rY : IsReduced Y)
    (rig : ∀ m m' : SABMap o₁.t o.t π, (∀ a, ∃ σ, (o₁.eta a).left ≫ m.φ = σ ∧ (o₁.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (univ : ∀ (T : Scheme.{0}) (f : T ⟶ X) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f),
      (∀ a, (o'.eta a ^ k).left ≫ m'.φ = f ≫ (o.eta a).left) ∧
        (∀ a, (o'.etaA a ^ k').left ≫ m'.φ = f ≫ (o.etaA a).left) →
      ∃! h : T ⟶ Y, h ≫ π = f ∧ ∃ u : ObjMap o' oc h, u.toSABMap.φ ≫ mc.φ = m'.φ) :
    ∃ h : X₂ ⟶ Y, IsIso h ∧ h ≫ π = r := by
  obtain ⟨h, ⟨hh, u, hu⟩, -⟩ := univ X₂ r o₂ m hm
  obtain ⟨g, ⟨hg, ⟨w⟩⟩, -⟩ := hX₂ Y (π ≫ s) oc rY
  obtain ⟨v, hv⟩ := sab_cancel mc n.toSABMap (𝟙 Y) (Category.id_comp _)
  have v₁ : ∀ a, (o₁.eta a).left ≫ v.φ = (oc.eta a ^ k).left := fun a =>
    (sec_cancel v mc _ _ (by rw [hv, hmc.1, Category.id_comp]; exact n.eta a)).trans (Category.id_comp _)
  have v₂ : ∀ a, (o₁.etaA a).left ≫ v.φ = (oc.etaA a ^ k').left := fun a =>
    (sec_cancel v mc _ _ (by rw [hv, hmc.2, Category.id_comp]; exact n.etaA a)).trans (Category.id_comp _)
  obtain ⟨vw, hvw⟩ := sab_comp v w.toSABMap (Category.id_comp g)
  have key : ∀ (e : Y ⟶ X) (he : g ≫ r = e), ∃ z : ObjMap o₁ o e, z.toSABMap.φ = v.φ ≫ w.toSABMap.φ ≫ m.φ := by
    intro e he
    obtain ⟨z, hz⟩ := sab_comp vw m he
    rw [hvw, Category.assoc] at hz
    refine ⟨⟨z, fun a => ?_, fun a => ?_⟩, hz⟩
    · show _ ≫ z.φ = _
      rw [hz, ← Category.assoc, v₁, ← Category.assoc, sec_pow w.toSABMap _ _ (w.eta a), Category.assoc, hm.1,
        ← Category.assoc, he]
    · show _ ≫ z.φ = _
      rw [hz, ← Category.assoc, v₂, ← Category.assoc, sec_pow w.toSABMap _ _ (w.etaA a), Category.assoc, hm.2,
        ← Category.assoc, he]
  have hgr : g ≫ r = π := by
    obtain ⟨z, -⟩ := key _ rfl
    exact (hX Y (π ≫ s) o₁ rY).unique ⟨by rw [Category.assoc, hg], ⟨z⟩⟩ ⟨rfl, ⟨n⟩⟩
  obtain ⟨z, hz⟩ := key _ hgr
  have hzn : z.toSABMap.φ = n.toSABMap.φ := rig _ _ fun a => ⟨_, z.eta a, n.eta a⟩
  have : IsIso v.φ := v.cart.1.isIso_fst_of_isIso
  have hwm : w.toSABMap.φ ≫ m.φ = mc.φ := by
    rw [← cancel_epi v.φ, ← hz, hzn, hv]
  refine ⟨h, ⟨g, ?_, ?_⟩, hh⟩
  · obtain ⟨x, -⟩ := ((hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ o₂ oc o₂).2 g h w).1 u
    obtain ⟨y, -⟩ := (hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ o₂ o₂ o₂).1
    exact (hX₂ X₂ (r ≫ s) o₂ rX₂).unique
      ⟨by rw [Category.assoc, hg, ← Category.assoc, hh], ⟨x⟩⟩ ⟨Category.id_comp _, ⟨y⟩⟩
  · obtain ⟨x, hx⟩ := ((hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ oc o₂ oc).2 h g u).1 w
    obtain ⟨y, hy⟩ := (hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ oc oc oc).1
    exact (univ Y π oc mc hmc).unique
      ⟨by rw [Category.assoc, hh, hgr], x, by rw [hx, Category.assoc, hu, hwm]⟩
      ⟨Category.id_comp _, y, by rw [hy, Category.id_comp]⟩

end GlobalTheory.LevelCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.VerticalDeriv

open GlobalTheory.FibreDeriv

variable {g : ℕ} {X Z : Scheme.{0}}

theorem isDerivAt0_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ Z}
    (H : IsDerivAt0 e w v) (H' : IsDerivAt0 e w v') : v = v' := by
  rw [isDerivAt0_iff] at H H'
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have h := (top_le_preimage_eps v _ H.1 U).2 h0
  have h' := (top_le_preimage_eps v' _ H'.1 U).2 h0
  exact TangentOrigin.ext_evalPt hU h h' (RingHom.ext fun f => (H.2 U h f).trans (H'.2 U h' f).symm)

theorem exists_isDerivAt0 {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (hol : IsHolTo Set.univ e) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber ℂ) ⟶ Z, IsDerivAt0 e w v := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have hd := LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0
  let J : Γ(Z, U) →+* DualNumber ℂ :=
    { toFun := fun f => jet w (fun z => valAt' (e z) U f)
      map_one' := by
        have : (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1 := by
          filter_upwards [LocalLift.hol_eventually_mem hol (Set.mem_univ _) h0] with z hz
          exact valAt'_one _ hz.2
        rw [jet_congr w this, jet_const, map_one]
      map_zero' := by
        simp only [valAt'_zero]
        rw [jet_const, map_zero]
      map_add' := fun f f' => by
        simp only [valAt'_add]
        exact jet_add w (hd f) (hd f')
      map_mul' := fun f f' => by
        simp only [valAt'_mul]
        exact jet_mul w (hd f) (hd f') }
  obtain ⟨v, hv, hve⟩ := TangentOrigin.exists_evalPt_eq hU J
  refine ⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩
  refine TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
  refine (TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_
  rw [hve, ← TangentOrigin.valAt'_eq_evalPt]
  exact fst_jet w (fun z => valAt' (e z) U f)

theorem isDerivAt0_vertical (p : Z ⟶ X) (x : Sp ℂ ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (he : ∀ z, e z ≫ p = x)
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z} (H : IsDerivAt0 e w v) :
    v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x := by
  have h1 := isDerivAt0_comp H p
  simp only [he] at h1
  exact isDerivAt0_unique h1 (LocalLift.isDerivAt0_const (fun _ => x) w fun U f _ => by simp)

theorem isDerivAt0_snd {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (hol : IsHolTo Set.univ e) {U : Z.Opens} {n : ℕ}
    (t : Fin n → Γ(Z, U)) (h0 : ⊤ ≤ e 0 ⁻¹ᵁ U) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z}
    (H : IsDerivAt0 e w v) (h : ⊤ ≤ v ⁻¹ᵁ U) (i : Fin n) :
    (TangentOrigin.evalPt v U h (t i)).snd = fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 w i := by
  rw [fderiv_pi fun i => LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0 (t i)]
  exact H.2 U h (t i)

theorem bijective_iff_injective (p : Z ⟶ X) (x : Sp ℂ ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (he : ∀ z, e z ≫ p = x)
    (hol : IsHolTo Set.univ e) (U : Z.Opens) (t : Fin g → Γ(Z, U)) (h0 : ⊤ ≤ e 0 ⁻¹ᵁ U)
    (hun : ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' →
      (∀ i, TangentOrigin.evalPt v U h (t i) = TangentOrigin.evalPt v' U h' (t i)) → v = v') :
    (∀ v : Sp (DualNumber ℂ) ⟶ Z, v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∃! w, IsDerivAt0 e w v) ↔
      Function.Injective (fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0) := by
  set T := fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 with hT
  have key : ∀ (v : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U), v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∀ w,
      (IsDerivAt0 e w v ↔ T w = fun i => (TangentOrigin.evalPt v U h (t i)).snd) := by
    intro v h hv hv0 w
    refine ⟨fun H => funext fun i => (isDerivAt0_snd hol t h0 H h i).symm, fun H => ?_⟩
    obtain ⟨v', H'⟩ := exists_isDerivAt0 hol w
    have h' := (top_le_preimage_eps v' _ H'.1 U).2 h0
    rw [hun v v' h h' (hv.trans (isDerivAt0_vertical p x he H').symm) (hv0.trans H'.1.symm) fun i => ?_]
    · exact H'
    · refine TrivSqZeroExt.ext ((fst_evEps v _ hv0 U h _).trans (fst_evEps v' _ H'.1 U h' _).symm) ?_
      rw [isDerivAt0_snd hol t h0 H' h' i]
      exact (congrFun H i).symm
  constructor
  · intro H w w' hw
    obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    have h := (top_le_preimage_eps v _ Hv.1 U).2 h0
    have hv := isDerivAt0_vertical p x he Hv
    exact (H v hv Hv.1).unique Hv ((key v h hv Hv.1 w').2 (hw.symm.trans ((key v h hv Hv.1 w).1 Hv)))
  · intro H v hv hv0
    have h := (top_le_preimage_eps v _ hv0 U).2 h0
    simp only [key v h hv hv0]
    have hs : Function.Surjective T := (LinearMap.injective_iff_surjective (f := T.toLinearMap)).1 H
    exact (Function.bijective_iff_existsUnique T).1 ⟨H, hs⟩ _

end GlobalTheory.VerticalDeriv

namespace GlobalTheory


open VerticalDeriv in
theorem vertical_derivative_in_coordinates :
    ∀ (X : Scheme.{0}) (G : Over X) (x : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk x ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → (∀ w, ∃! v : epsPt x ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ (U : G.left.Opens) (t : Fin g → Γ(G.left, U)), ⊤ ≤ (show Sp ℂ ⟶ G.left from (e 0).left) ⁻¹ᵁ U → (∀ (v v' : Sp (DualNumber ℂ) ⟶ G.left) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ G.hom = v' ≫ G.hom → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') → ((∀ v : epsPt x ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) ↔ Function.Injective (fderiv ℂ (fun z i => valAt' (e z).left U (t i)) 0)) := by
  intro X G x g e hol
  have he : ∀ z, (show Sp ℂ ⟶ G.left from (e z).left) ≫ G.hom = x := fun z => Over.w (e z)
  refine ⟨fun w => ?_, fun U t h0 hun => ?_⟩
  · obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    exact ⟨Over.homMk v (isDerivAt0_vertical G.hom x he Hv), Hv,
      fun v' Hv' => Over.OverMorphism.ext (isDerivAt0_unique Hv' Hv)⟩
  · refine Iff.trans ?_ (bijective_iff_injective G.hom x he hol U t h0 hun)
    exact ⟨fun H v hv hv0 => H (Over.homMk v hv) hv0, fun H v hv0 => H v.left (Over.w v) hv0⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem abelianScheme_id_pow_finite_etale_surjective :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (m : ℕ), IsAbelianScheme A → IsUnit (m : Γ(S, ⊤)) → IsMonHom ((𝟙 A) ^ m) ∧ IsFinite ((𝟙 A) ^ m).left ∧ Etale ((𝟙 A) ^ m).left ∧ Surjective ((𝟙 A) ^ m).left := by
  intro S A _ m hA hm
  obtain ⟨⟩ := hA
  have hmon : ∀ n : ℕ, IsMonHom ((𝟙 A) ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Hom.one_def]; infer_instance
    | succ n ih => rw [pow_succ, Hom.mul_def]; infer_instance
  have hfin : IsFinite ((𝟙 A) ^ m).left := GrpTangent.isFinite_id_pow A hm
  have het : Etale ((𝟙 A) ^ m).left := GrpTangent.etale_id_pow A hm
  refine ⟨hmon m, hfin, het, ⟨fun x => ?_⟩⟩
  set f := ((𝟙 A) ^ m).left with hf

  have hcl : IsClopen (Set.range f) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩

  have hw : A.hom (f x) = A.hom x := by
    rw [← Scheme.Hom.comp_apply, hf, Over.w]

  have hsub : A.hom ⁻¹' {A.hom x} ⊆ Set.range f :=
    (A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected.subset_isClopen hcl
      ⟨f x, by simp [hw], Set.mem_range_self x⟩
  exact hsub rfl

end GlobalTheory
end
