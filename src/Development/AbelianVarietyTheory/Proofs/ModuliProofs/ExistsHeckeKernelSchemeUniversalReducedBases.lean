module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndEtaleOfCompOfFiniteEtaleCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetDescends
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeomPtRangeEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversal
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelListsModuloPermutations
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleHeckeKernelLists
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleHeckeKernelLists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkTuple

theorem exists_equiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S) (hg : T.hom ≫ f = g) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk g ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  subst hg
  exact GlobalTheory.HkSetPull.exists_equiv h T

theorem exists_tuples {S : Scheme.{0}} (G : Over S) [GrpObj G] (N n : ℕ) (hG : IsAbelianScheme G)
    (hn : IsUnit (N : Γ(S, ⊤))) :
    ∃ (Z : Scheme.{0}) (a : Z ⟶ S) (x : Fin n → (Over.mk a ⟶ G)), IsFinite a ∧ Etale a ∧ (∀ j, x j ^ N = 1) ∧
      ∀ (T : Over S) (y : Fin n → (T ⟶ G)), (∀ j, y j ^ N = 1) → ∃! h : T ⟶ Over.mk a, ∀ j, h ≫ x j = y j := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  have key : ∃ (Z : Over S) (x : Fin n → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ j, x j ^ N = 1) ∧
      ∀ (T : Over S) (y : Fin n → (T ⟶ G)), (∀ j, y j ^ N = 1) → ∃! h : T ⟶ Z, ∀ j, h ≫ x j = y j := by
    refine ⟨Out.powObj (torsion G N) n, fun i => Out.powPr (torsion G N) i ≫ torsion.ι G N,
      LatticeTorsion.prop_powObj @IsFinite _ hfin n, LatticeTorsion.prop_powObj @Etale _ het n, fun i => ?_,
      fun T y' hy' => ?_⟩
    · rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
    · choose y hy hyu using fun i : Fin n => LatticeTorsion.existsUnique_torsion G N (y' i) (hy' i)
      let h : T ⟶ Out.powObj (torsion G N) n := (Out.powIsLimit (torsion G N) n).lift (Fan.mk T y)
      have hh : ∀ i, h ≫ Out.powPr (torsion G N) i = y i := fun i =>
        (Out.powIsLimit (torsion G N) n).fac (Fan.mk T y) ⟨i⟩
      refine ⟨h, fun i => by rw [← hy i, ← hh i, Category.assoc], fun h' hh' => ?_⟩
      refine (Out.powIsLimit (torsion G N) n).hom_ext fun ⟨i⟩ => ?_
      exact (hyu i _ ((Category.assoc _ _ _).trans (hh' i))).trans (hh i).symm
  obtain ⟨Z, x, h⟩ := key
  exact ⟨Z.left, Z.hom, x, h⟩

theorem eq_of_mem_range {S : Scheme.{0}} {G : Over S} (τ : 𝟙_ (Over S) ⟶ G) {k : Type} [Field k] {x : Sp k ⟶ S}
    (z : Over.mk x ⟶ G) (u : Sp k) (hu : z.left u ∈ Set.range τ.left) : z = toUnit _ ≫ τ := by
  have w : τ.left ≫ G.hom = 𝟙 S := Over.w _
  have i₁ : IsImmersion τ.left := by
    have : IsImmersion (τ.left ≫ G.hom) := by rw [w]; exact inferInstanceAs (IsImmersion (𝟙 S))
    exact IsImmersion.of_comp _ G.hom
  have r : Set.range (pullback.fst z.left τ.left) = Set.univ := by
    rw [Scheme.Pullback.range_fst]
    refine Set.eq_univ_of_forall fun v => ?_
    rw [show v = u from Subsingleton.elim (α := PrimeSpectrum k) _ _]
    exact hu
  have i₂ : IsClosedImmersion (pullback.fst z.left τ.left) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [r]; exact isClosed_univ)
  have i₃ : Surjective (pullback.fst z.left τ.left) := ⟨Set.range_eq_univ.1 r⟩
  have i₄ : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have i₅ : IsIso (pullback.fst z.left τ.left) := isIso_of_isClosedImmersion_of_surjective _
  refine Over.OverMorphism.ext ?_
  have tu : (toUnit (Over.mk x)).left = x := by simp
  have wz : z.left ≫ G.hom = x := Over.w _
  rw [Over.comp_left, tu, ← cancel_epi (pullback.fst z.left τ.left)]
  have e : pullback.fst z.left τ.left ≫ z.left ≫ G.hom ≫ τ.left = pullback.fst z.left τ.left ≫ z.left := by
    rw [pullback.condition_assoc, reassoc_of% w, pullback.condition]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ.left) (Category.comp_id _))
  rw [← e, reassoc_of% wz]

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} {n : ℕ} (τ : Fin n → (𝟙_ (Over S) ⟶ G)) {k : Type} [Field k]
    {x : Sp k ⟶ S} (z : Over.mk x ⟶ G) :
    Set.range z.left ⊆ (⋃ j, Set.range (τ j).left) ↔ z ∈ Set.range fun j => toUnit (Over.mk x) ≫ τ j := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨(default : PrimeSpectrum k), rfl⟩)
    exact ⟨j, (eq_of_mem_range (τ j) z _ hj).symm⟩
  · rintro ⟨j, rfl⟩ _ ⟨u, rfl⟩
    refine Set.mem_iUnion.2 ⟨j, (toUnit (Over.mk x)).left u, ?_⟩
    exact (Scheme.Hom.comp_apply _ _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem listed_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (D : Datum H) (P : Ideal (𝓞 E))
    (p i : ℕ) (m : SABMap t' t f) {n : ℕ} (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)) (τ : Fin n → (𝟙_ (Over S') ⟶ t'.G))
    (e : ∀ j, (τ j).left ≫ m.φ = f ≫ (σ j).left) {k : Type} [Field k] (x : Sp k ⟶ S') :
    ((Function.Injective fun j => x ≫ (τ j).left) ∧ ∃ C : Subgroup (Over.mk x ⟶ t'.G),
      (C : Set _) = Set.range (fun j => toUnit (Over.mk x) ≫ τ j) ∧ t'.HeckeKer (Over.mk x) D P p i C) ↔
    ((Function.Injective fun j => (x ≫ f) ≫ (σ j).left) ∧ ∃ C : Subgroup (Over.mk (x ≫ f) ⟶ t.G),
      (C : Set _) = Set.range (fun j => toUnit (Over.mk (x ≫ f)) ≫ σ j) ∧
        t.HeckeKer (Over.mk (x ≫ f)) D P p i C) := by
  obtain ⟨ρ, e₀⟩ := exists_equiv m.cart (Over.mk x) (x ≫ f) rfl
  have tu : (toUnit (Over.mk x)).left = x := by simp
  have tu' : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := by simp
  have l₁ : ∀ j, (toUnit (Over.mk x) ≫ τ j).left = x ≫ (τ j).left := fun j => by rw [Over.comp_left, tu]
  have l₂ : ∀ j, (toUnit (Over.mk (x ≫ f)) ≫ σ j).left = (x ≫ f) ≫ (σ j).left := fun j => by
    rw [Over.comp_left, tu']
  have e₁ : ∀ j, ρ (toUnit (Over.mk x) ≫ τ j) = toUnit (Over.mk (x ≫ f)) ≫ σ j := fun j =>
    Over.OverMorphism.ext (by
      rw [e₀, l₁, l₂]
      exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) (e j)).trans (Category.assoc _ _ _).symm))
  have mem : ∀ u, u ∈ Set.range (fun j => toUnit (Over.mk x) ≫ τ j) ↔
      ρ u ∈ Set.range (fun j => toUnit (Over.mk (x ≫ f)) ≫ σ j) := fun u =>
    exists_congr fun j => by beta_reduce; rw [← e₁]; exact ρ.injective.eq_iff.symm
  have eq : ∀ (u : Over.mk x ⟶ t'.G) (v : Over.mk (x ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → v = ρ u :=
    fun u v h => Over.OverMorphism.ext (h.trans (e₀ u).symm)
  refine and_congr (forall₂_congr fun a b => imp_congr_left ?_) ⟨?_, ?_⟩
  · beta_reduce
    rw [← l₁, ← l₁, ← l₂, ← l₂]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← e₁, ← e₁, Over.OverMorphism.ext h]
    · have := Over.OverMorphism.ext h
      rw [← e₁, ← e₁] at this
      rw [ρ.injective this]
  · rintro ⟨C', h₁, h₂⟩
    refine ⟨C'.comap ρ.symm.toMonoidHom, Set.ext fun v => ?_,
      (GlobalTheory.HkSetPull.heckeKer_iff D P p i m (Over.mk x) C' _ fun u v h => ?_).1 h₂⟩
    · obtain ⟨u, rfl⟩ := ρ.surjective v
      rw [← mem, ← h₁]
      show ρ.symm (ρ u) ∈ C' ↔ _
      rw [ρ.symm_apply_apply]
      rfl
    · rw [eq u v h]
      show _ ↔ ρ.symm (ρ u) ∈ C'
      rw [ρ.symm_apply_apply]
  · rintro ⟨C, h₁, h₂⟩
    refine ⟨C.comap ρ.toMonoidHom, Set.ext fun u => ?_,
      (GlobalTheory.HkSetPull.heckeKer_iff D P p i m (Over.mk x) _ C fun u v h => ?_).2 h₂⟩
    · rw [mem, ← h₁]
      rfl
    · rw [eq u v h]
      rfl

theorem range_subset_of_geom {T Z : Scheme.{0}} (h : T ⟶ Z) (V : Set Z)
    (hV : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), Set.range (x ≫ h) ⊆ V) : Set.range h ⊆ V := by
  rintro _ ⟨y, rfl⟩
  let k := AlgebraicClosure (T.residueField y)
  let z : Sp k ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap (T.residueField y) k)) ≫ T.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  exact hV k z ⟨(default : PrimeSpectrum k), (Scheme.Hom.comp_apply _ _ _).trans (congrArg h (hz _))⟩

end GlobalTheory.HkTuple


open GlobalTheory.HkTuple in
theorem GlobalTheory.exists_finiteEtale_heckeLists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s), admitted l 𝔓 p → ∃ (Y : Scheme.{0}) (a : Y ⟶ S) (oY : Ob D l (a ≫ s)) (m : ObjMap oY o a) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite a ∧ Etale a ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t : SAB H T) (mu : SABMap t o.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃! h : T ⟶ Y, h ≫ a = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  intro E _ _ _ H D l P p i n S s o adm
  have hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have := ((baseKA l).unit (p ^ 2) (pow_pos adm.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  have specMap_id₂ : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  obtain ⟨Z, b, x, hf, he, hx, huniv⟩ := GlobalTheory.HkTuple.exists_tuples o.t.G (p ^ 2) n (GlobalTheory.ObjDim.isAbelianScheme o) hu
  obtain ⟨oZ, ⟨mZ⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S Z s (b ≫ s) b rfl rfl
    (by rw [specMap_id₂, Category.comp_id]) o
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkTuple.exists_equiv mZ.cart (𝟙_ (Over Z)) b (Category.id_comp b)
  let σZ : Fin n → (𝟙_ (Over Z) ⟶ oZ.t.G) := fun j => ρ.symm (x j)
  have eZ : ∀ j, (σZ j).left ≫ mZ.toSABMap.φ = (x j).left := fun j => by
    rw [← e₀, ρ.apply_symm_apply]
  have pZ : ∀ j, σZ j ^ p ^ 2 = 1 := fun j => by rw [← map_pow, hx, map_one]
  obtain ⟨V, hc, hV⟩ := GlobalTheory.T.exists_clopen_locus_torsionSections_heckeKernel E H D l P p i n Z (b ≫ s) oZ σZ adm pZ
  obtain ⟨oY, ⟨mY⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) Z V (b ≫ s) ((V.ι ≫ b) ≫ s) V.ι
    rfl rfl (by rw [specMap_id₂, Category.comp_id, Category.assoc]) oZ
  obtain ⟨m, hm⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o oZ oY).2 b V.ι mZ).1 mY
  obtain ⟨ρ', e₀'⟩ := GlobalTheory.HkTuple.exists_equiv mY.cart (𝟙_ (Over V.toScheme)) V.ι (Category.id_comp _)
  let σ : Fin n → (𝟙_ (Over V.toScheme) ⟶ oY.t.G) := fun j => ρ'.symm (toUnit _ ≫ σZ j)
  have tu : (toUnit (Over.mk V.ι)).left = V.ι := by simp
  have eY : ∀ j, (σ j).left ≫ mY.toSABMap.φ = V.ι ≫ (σZ j).left := fun j => by
    rw [← e₀', ρ'.apply_symm_apply, Over.comp_left, tu]
  have eσ : ∀ j, (σ j).left ≫ m.toSABMap.φ = V.ι ≫ (x j).left := fun j => by
    rw [hm, ← eZ]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ mZ.toSABMap.φ) (eY j)).trans (Category.assoc _ _ _))
  have hY := fun (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ V.toScheme) =>
    (GlobalTheory.HkTuple.listed_iff D P p i mY.toSABMap σZ σ eY y).2 ((hV k (y ≫ V.ι)).1 (by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact (y u).2))
  have ci : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  refine ⟨V, V.ι ≫ b, oY, m, σ, ⋃ j, Set.range (σ j).left, inferInstance, inferInstance,
    ⟨fun j => ?_, rfl, fun k _ _ y => (hY k y).1⟩, fun k _ _ y => ?_, ?_⟩
  · rw [← map_pow, ← MonObj.comp_pow, pZ, MonObj.comp_one, map_one]
  · obtain ⟨C, h₁, h₂⟩ := (hY k y).2
    exact ⟨C, fun z => by rw [GlobalTheory.HkTuple.range_subset_iff, ← h₁]; rfl, h₂⟩
  · rintro T f t mu τ K' ⟨hτ, rfl, hinj⟩ hK
    obtain ⟨ρ₂, e₂⟩ := GlobalTheory.HkTuple.exists_equiv mu.cart (𝟙_ (Over T)) f (Category.id_comp _)
    obtain ⟨h₀, hh₀, hh₀u⟩ := huniv (Over.mk f) (fun j => ρ₂ (τ j)) (fun j => by rw [← map_pow, hτ, map_one])
    have e₃ : ∀ j, h₀.left ≫ (x j).left = (τ j).left ≫ mu.φ := fun j => by
      rw [← e₂, ← hh₀, Over.comp_left]
    have uq : ∀ g : T ⟶ Z, g ≫ b = f → (∀ j, g ≫ (x j).left = (τ j).left ≫ mu.φ) → g = h₀.left := fun g w hg =>
      congrArg (·.left) (hh₀u (Over.homMk g w) fun j => Over.OverMorphism.ext ((hg j).trans (e₂ _).symm))
    obtain ⟨g, w, e₄, uq'⟩ : ∃ g : T ⟶ Z, g ≫ b = f ∧ (∀ j, g ≫ (x j).left = (τ j).left ≫ mu.φ) ∧
        ∀ g' : T ⟶ Z, g' ≫ b = f → (∀ j, g' ≫ (x j).left = (τ j).left ≫ mu.φ) → g' = g :=
      ⟨h₀.left, Over.w h₀, e₃, uq⟩
    clear uq e₃ hh₀u hh₀ h₀ e₂ ρ₂
    subst w
    obtain ⟨mu', hmu⟩ := GlobalTheory.ObjMaps.exists_sab_cancel mZ.toSABMap mu
    have e₅ : ∀ j, (τ j).left ≫ mu'.φ = g ≫ (σZ j).left := fun j => by
      have w₁ : (τ j).left ≫ t.G.hom = 𝟙 T := Over.w _
      have w₂ : (σZ j).left ≫ oZ.t.G.hom = 𝟙 Z := Over.w _
      refine mZ.cart.1.hom_ext ?_ ?_
      · exact (Category.assoc _ _ _).trans ((congrArg ((τ j).left ≫ ·) hmu.symm).trans ((e₄ j).symm.trans
          ((congrArg (g ≫ ·) (eZ j).symm).trans (Category.assoc _ _ _).symm)))
      · exact (Category.assoc _ _ _).trans ((congrArg ((τ j).left ≫ ·) mu'.cart.1.w).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) w₁).trans ((Category.id_comp g).trans
          ((Category.comp_id g).symm.trans ((congrArg (g ≫ ·) w₂.symm).trans (Category.assoc _ _ _).symm))))))
    have hr : Set.range g ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      refine GlobalTheory.HkTuple.range_subset_of_geom g _ fun k _ _ y => (hV k (y ≫ g)).2
        ((GlobalTheory.HkTuple.listed_iff D P p i mu' σZ τ e₅ y).1 ⟨hinj k y, ?_⟩)
      obtain ⟨C, h₁, h₂⟩ := hK k y
      exact ⟨C, Set.ext fun z => (h₁ z).trans (GlobalTheory.HkTuple.range_subset_iff τ z), h₂⟩
    refine ⟨IsOpenImmersion.lift V.ι g hr, ⟨by rw [IsOpenImmersion.lift_fac_assoc], fun j => ?_⟩, ?_⟩
    · exact (congrArg (IsOpenImmersion.lift V.ι g hr ≫ ·) (eσ j)).trans
        ((IsOpenImmersion.lift_fac_assoc _ _ _ _).trans (e₄ j))
    · rintro h ⟨w, hh⟩
      rw [← cancel_mono V.ι, IsOpenImmersion.lift_fac]
      exact uq' _ ((Category.assoc _ _ _).trans w) fun j =>
        (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) (eσ j).symm).trans (hh j))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleHeckeKernelListsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_heckeKernel_lists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s), admitted l 𝔓 p → ∃ (Y : Scheme.{0}) (a : Y ⟶ S) (oY : Ob D l (a ≫ s)) (m : ObjMap oY o a) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite a ∧ Etale a ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t : SAB H T) (mu : SABMap t o.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃! h : T ⟶ Y, h ≫ a = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  first | exact @GlobalTheory.exists_finiteEtale_heckeLists | exact GlobalTheory.exists_finiteEtale_heckeLists | (intros; apply GlobalTheory.exists_finiteEtale_heckeLists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelListsModuloPermutations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkPerm

theorem lists_perm {S : Scheme.{0}} {G : Over S} [GrpObj G] {N n : ℕ} {σ : Fin n → (𝟙_ (Over S) ⟶ G)}
    {K : Set G.left} (h : Lists N σ K) (g : Equiv.Perm (Fin n)) : Lists N (fun j => σ (g j)) K := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨fun j => h₁ _, ?_, fun k _ _ x => (h₃ k x).comp g.injective⟩
  rw [h₂]
  exact (g.surjective.iUnion_comp (fun j => Set.range (σ j).left)).symm

theorem exists_perm {α : Type} {n : ℕ} {u v : Fin n → α} (hu : Function.Injective u) (hv : Function.Injective v)
    (h : Set.range u = Set.range v) : ∃ g : Equiv.Perm (Fin n), ∀ j, u (g j) = v j := by
  have : ∀ j, ∃ i, u i = v j := fun j => by
    have : v j ∈ Set.range u := h ▸ Set.mem_range_self j
    exact this
  choose g hg using this
  have gi : Function.Injective g := fun a b e => hv (by rw [← hg, ← hg, e])
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 gi), hg⟩

theorem exists_lists_mod_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ), admitted l 𝔓 p → ∃ (Y Hk : Scheme.{0}) (q : Y ⟶ Hk) (π₁ : Hk ⟶ Xo.X) (oY : Ob D l ((q ≫ π₁) ≫ Xo.s)) (m : ObjMap oY Xo.univ (q ≫ π₁)) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite q ∧ Etale q ∧ Surjective q ∧ IsFinite π₁ ∧ Etale π₁ ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q ↔ Set.range (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ) = Set.range (fun j => y' ≫ (σ j).left ≫ m.toSABMap.φ) ∧ y ≫ q ≫ π₁ = y' ≫ q ≫ π₁) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ Xo.X) (t : SAB H T) (mu : SABMap t Xo.univ.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃ h : T ⟶ Y, h ≫ q ≫ π₁ = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  intro E _ _ _ H D l Xo P p i n hA
  obtain ⟨Y, a, oY, m, σ, K, fa, ea, hL, hK, hu⟩ := GlobalTheory.T.exists_finiteEtale_heckeKernel_lists E H D l P p i n Xo.X Xo.s Xo.univ hA
  have hρ := fun g : Equiv.Perm (Fin n) => hu Y a oY.t m.toSABMap (fun j => σ (g j)) K (lists_perm hL g) hK
  choose ρ hρ₁ hρ₂ using hρ
  have r₁ : ∀ g, ρ g ≫ a = a := fun g => (hρ₁ g).1
  have r₂ : ∀ g j, ρ g ≫ (σ j).left ≫ m.toSABMap.φ = (σ (g j)).left ≫ m.toSABMap.φ := fun g => (hρ₁ g).2
  have one : ρ 1 = 𝟙 Y := (hρ₂ 1 _ ⟨by simp, fun j => by simp⟩).symm
  have mul : ∀ g c, ρ (g * c) = ρ g ≫ ρ c := fun g c =>
    (hρ₂ (g * c) _ ⟨by rw [Category.assoc, r₁, r₁], fun j => by
      rw [Category.assoc, r₂, r₂]; rfl⟩).symm
  have inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y),
      Function.Injective fun j => y ≫ (σ j).left ≫ m.toSABMap.φ := by
    intro k _ _ y b c e
    apply hL.2.2 k y
    have w : ∀ j, (σ j).left ≫ oY.t.G.hom = 𝟙 Y := fun j => Over.w _
    refine m.toSABMap.cart.1.hom_ext ?_ ?_
    · simpa only [Category.assoc] using e
    · simp only [Category.assoc, w]
  have free : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (g : Equiv.Perm (Fin n)), y ≫ ρ g = y → g = 1 := by
    intro k _ _ y g e
    ext1 j
    apply inj k y
    change y ≫ (σ (g j)).left ≫ m.toSABMap.φ = y ≫ (σ j).left ≫ m.toSABMap.φ
    rw [← r₂, ← Category.assoc, e]
  have uq : ∀ (T : Scheme.{0}) (y y' : T ⟶ Y), y ≫ a = y' ≫ a →
      (∀ j, y ≫ (σ j).left ≫ m.toSABMap.φ = y' ≫ (σ j).left ≫ m.toSABMap.φ) → y = y' := by
    intro T y y' e₁ e₂
    obtain ⟨_, _, _, _, _, m', -⟩ := sabPull Out.CubePf.cubePull y oY.t
    obtain ⟨mu, hmu⟩ := GlobalTheory.ObjMaps.exists_sab_comp m.toSABMap m'
    obtain ⟨τ, hτ, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m'.cart K _ n σ hL
    have hτ' : ∀ j, y ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := fun j => by
      rw [hmu, ← Category.assoc, ← hτ, Category.assoc]
    exact (hu T (y ≫ a) _ mu τ _ hL' (GlobalTheory.HkSetPull.heckeSet_pull D P p i m' K hK)).unique ⟨rfl, hτ'⟩
      ⟨e₁.symm, fun j => (e₂ j).symm.trans (hτ' j)⟩
  have hq := GlobalTheory.isQProjOver_comp_of_isFinite_noetherian (KA l) Y Xo.X a Xo.s fa Xo.qproj
  obtain ⟨Hk, q, sH, hs, hG, sep, lft, -⟩ := GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver (KA l) Y (a ≫ Xo.s)
    (Equiv.Perm (Fin n)) ρ hq one mul (fun g => by rw [← Category.assoc, r₁]) free
  have hd := (GlobalTheory.ZM.galoisCover_descent Y Hk q _ ρ hG).1
  obtain ⟨π₁, rfl, -⟩ := hd Xo.X a r₁
  have hs' : π₁ ≫ Xo.s = sH := (hd _ ((q ≫ π₁) ≫ Xo.s) (fun g => by rw [← Category.assoc, r₁])).unique
    (Category.assoc _ _ _).symm hs
  subst hs'
  have : IsSeparated π₁ := IsSeparated.of_comp π₁ Xo.s
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : LocallyOfFiniteType π₁ := locallyOfFiniteType_of_comp π₁ Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨f₁, e₁⟩ := isFinite_and_etale_of_comp_of_finite_etale_cover Y Hk Xo.X q π₁ hG.fin hG.etale hG.onto fa ea
    inferInstance inferInstance
  refine ⟨Y, Hk, q, π₁, oY, m, σ, K, hG.fin, hG.etale, hG.onto, f₁, e₁, hL, hK, fun k _ _ y y' => ⟨fun e => ?_, fun e => ?_⟩,
    fun T f t mu τ K' h₁ h₂ => (hu T f t mu τ K' h₁ h₂).exists⟩
  · obtain ⟨g, rfl, -⟩ := hG.fibre k y y' e
    refine ⟨?_, by rw [← Category.assoc, e, Category.assoc]⟩
    simp only [Category.assoc, r₂]
    exact (g.surjective.range_comp (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ)).symm
  · obtain ⟨g, hg⟩ := exists_perm (inj k y) (inj k y') e.1
    have : y ≫ ρ g = y' := uq _ _ _ (by rw [Category.assoc, r₁]; exact e.2) fun j => by
      rw [Category.assoc, r₂]; exact hg j
    rw [← this, Category.assoc, hG.inv]

end GlobalTheory.HkPerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelListsModuloPermutationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernelLists_modulo_permutations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ), admitted l 𝔓 p → ∃ (Y Hk : Scheme.{0}) (q : Y ⟶ Hk) (π₁ : Hk ⟶ Xo.X) (oY : Ob D l ((q ≫ π₁) ≫ Xo.s)) (m : ObjMap oY Xo.univ (q ≫ π₁)) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite q ∧ Etale q ∧ Surjective q ∧ IsFinite π₁ ∧ Etale π₁ ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q ↔ Set.range (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ) = Set.range (fun j => y' ≫ (σ j).left ≫ m.toSABMap.φ) ∧ y ≫ q ≫ π₁ = y' ≫ q ≫ π₁) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ Xo.X) (t : SAB H T) (mu : SABMap t Xo.univ.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃ h : T ⟶ Y, h ≫ q ≫ π₁ = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  first | exact @GlobalTheory.HkPerm.exists_lists_mod_perm | exact GlobalTheory.HkPerm.exists_lists_mod_perm | (intros; apply GlobalTheory.HkPerm.exists_lists_mod_perm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam.KerSch

theorem exists_lift_of_finite {k : Type} [Field k] [IsAlgClosed k] {Y Z : Scheme.{0}} (q : Y ⟶ Z)
    [IsFinite q] [Surjective q] (x : Sp k ⟶ Z) : ∃ y : Sp k ⟶ Y, y ≫ q = x := by
  have : CompactSpace ↥(pullback q x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q x)
  obtain ⟨p, -⟩ := (pullback.snd q x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback q x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd q x) z hz ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem exists_lift_ext {k : Type} [Field k] {Y Z : Scheme.{0}} (f : Y ⟶ Z) (u : Sp k ⟶ Z) (t : Sp k) (y₀ : Y)
    (h : f y₀ = u t) : ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (a : Sp k' ⟶ Sp k) (y : Sp k' ⟶ Y),
      Epi a ∧ y ≫ f = a ≫ u := by
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y₀ t h
  obtain ⟨k', _, _, z, -⟩ := exists_geomPt_range_eq (pullback f u) w
  refine ⟨k', inferInstance, inferInstance, z ≫ pullback.snd f u, z ≫ pullback.fst f u, ?_, ?_⟩
  · generalize z ≫ pullback.snd f u = a
    have : Surjective a := ⟨fun x => ⟨(default : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have : Flat a := inferInstance
    exact Flat.epi_of_flat_of_surjective a
  · rw [Category.assoc, Category.assoc, pullback.condition]

section

variable {A X G₁ Z GY Y : Scheme.{0}} {α : A ⟶ X} {g₁ : G₁ ⟶ Z} {gY : GY ⟶ Y} {φ : G₁ ⟶ A} {ψ : GY ⟶ G₁}
  {π : Z ⟶ X} {q : Y ⟶ Z} {n : ℕ} {σ : Fin n → (Y ⟶ GY)}

theorem range_subset_iff (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {k : Type} [Field k] (y : Sp k ⟶ Y) (u : Sp k ⟶ G₁) (hu : u ≫ g₁ = y ≫ q) :
    Set.range u ⊆ ψ '' (⋃ j, Set.range (σ j)) ↔ ∃ j, u = y ≫ σ j ≫ ψ := by
  have hs : ∀ j, σ j ≫ ψ ≫ g₁ = q := fun j => by rw [h₂.w, reassoc_of% hσ j]
  constructor
  · intro h
    obtain ⟨w, hw, e⟩ := h ⟨(default : PrimeSpectrum k), rfl⟩
    obtain ⟨j, y₀, rfl⟩ := Set.mem_iUnion.1 hw
    obtain ⟨k', _, _, a, y', ha, e'⟩ := exists_lift_ext (σ j ≫ ψ) u _ y₀ (by rw [Scheme.Hom.comp_apply]; exact e)
    have e₁ : y' ≫ q = (a ≫ y) ≫ q := by
      rw [Category.assoc, ← hu, ← reassoc_of% e', hs j]
    have e₂ : y' ≫ σ j ≫ ψ ≫ φ ∈ Set.range (fun j => (a ≫ y) ≫ σ j ≫ ψ ≫ φ) := hfib k' _ _ e₁ ▸ ⟨j, rfl⟩
    obtain ⟨j', e₃⟩ := e₂
    refine ⟨j', h₁.hom_ext ?_ ?_⟩
    · rw [← cancel_epi a, ← reassoc_of% e']
      simpa using e₃.symm
    · simp only [Category.assoc, hs, hu]
  · rintro ⟨j, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨σ j (y t), Set.mem_iUnion.2 ⟨j, _, rfl⟩, by simp⟩

theorem preimage_eq (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {GT T : Scheme.{0}} {gT : GT ⟶ T} {ν : GT ⟶ G₁} {h : T ⟶ Y} (h₃ : IsPullback ν gT g₁ (h ≫ q))
    {τ : Fin n → (T ⟶ GT)} (hτ : ∀ j, τ j ≫ gT = 𝟙 T) (hh : ∀ j, τ j ≫ ν = h ≫ σ j ≫ ψ) :
    (⋃ j, Set.range (τ j)) = ν ⁻¹' (ψ '' (⋃ j, Set.range (σ j))) := by
  ext w
  constructor
  · intro hw
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.1 hw
    refine ⟨σ j (h t), Set.mem_iUnion.2 ⟨j, _, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hh]
  · intro hw
    obtain ⟨k, _, _, z, hz⟩ := exists_geomPt_range_eq GT w
    have hzw : ∀ t, z t = w := fun t => by
      have : z t ∈ Set.range z := ⟨_, rfl⟩
      rwa [hz] at this
    obtain ⟨t₀⟩ : Nonempty (Sp k) := ⟨(default : PrimeSpectrum k)⟩
    obtain ⟨j, e⟩ := (range_subset_iff h₁ h₂ hσ hfib (z ≫ gT ≫ h) (z ≫ ν) (by simp [h₃.w])).1 (by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Hom.comp_apply, hzw]
      exact hw)
    have e' : z = z ≫ gT ≫ τ j := h₃.hom_ext (by simp [e, hh]) (by simp [hτ])
    refine Set.mem_iUnion.2 ⟨j, gT w, ?_⟩
    rw [← hzw t₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← e']

theorem range_subset_range (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {k : Type} [Field k] (y y' : Sp k ⟶ Y) (e : y ≫ q ≫ π = y' ≫ q ≫ π)
    (H : ∀ u u' : Sp k ⟶ G₁, u ≫ g₁ = y ≫ q → u' ≫ g₁ = y' ≫ q → u ≫ φ = u' ≫ φ →
      Set.range u ⊆ ψ '' (⋃ j, Set.range (σ j)) → Set.range u' ⊆ ψ '' (⋃ j, Set.range (σ j))) :
    Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) ⊆ Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ) := by
  have hs : ∀ j, σ j ≫ ψ ≫ g₁ = q := fun j => by rw [h₂.w, reassoc_of% hσ j]
  rintro _ ⟨j, rfl⟩
  have w : (y ≫ σ j ≫ ψ ≫ φ) ≫ α = (y' ≫ q) ≫ π := by
    simp only [Category.assoc, h₁.w, reassoc_of% hs, e]
  have hu : (y ≫ σ j ≫ ψ) ≫ g₁ = y ≫ q := by simp only [Category.assoc, hs]
  have := H (y ≫ σ j ≫ ψ) (h₁.lift _ _ w) hu (h₁.lift_snd _ _ _) (by simp)
    ((range_subset_iff h₁ h₂ hσ hfib y _ hu).2 ⟨j, rfl⟩)
  obtain ⟨j', e'⟩ := (range_subset_iff h₁ h₂ hσ hfib y' _ (h₁.lift_snd _ _ w)).1 this
  refine ⟨j', ?_⟩
  have := h₁.lift_fst _ _ w
  rw [e'] at this
  simpa using this

end

end GlobalTheory.HkFam.KerSch

namespace GlobalTheory.HkFam

open KerSch

theorem exists_heckeKernelScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ (Hk : Scheme.{0}) (π₁ : Hk ⟶ Xo.X) (o₁ : Ob D l (π₁ ≫ Xo.s)) (m₁ : ObjMap o₁ Xo.univ π₁) (K : Set o₁.t.G.left), IsFinite π₁ ∧ Etale π₁ ∧ HeckeSet D o₁.t 𝔓 p i K ∧ EtSet o₁.t.G K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Hk) (z' : Sp k ⟶ Hk), z ≫ π₁ = z' ≫ π₁ → (∀ (u : Over.mk z ⟶ o₁.t.G) (u' : Over.mk z' ⟶ o₁.t.G), u.left ≫ m₁.toSABMap.φ = u'.left ≫ m₁.toSABMap.φ → (Set.range u.left ⊆ K ↔ Set.range u'.left ⊆ K)) → z = z') ∧ ∀ (T : Scheme.{0}) (s : T ⟶ Sp (KA l)) (o : Ob D l s) (f : T ⟶ Xo.X) (mu : ObjMap o Xo.univ f) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over T) ⟶ o.t.G)) (K' : Set o.t.G.left), Lists (p ^ 2) τ K' → HeckeSet D o.t 𝔓 p i K' → ∃ (h : T ⟶ Hk) (n : ObjMap o o₁ h), h ≫ π₁ = f ∧ n.toSABMap.φ ≫ m₁.toSABMap.φ = mu.toSABMap.φ ∧ K' = n.toSABMap.φ ⁻¹' K := by
  intro E _ _ _ H D l Xo 𝔓 p i hA
  obtain ⟨Y, Hk, q, π₁, oY, m, σ, K, hqf, hqe, hqs, hπf, hπe, hL, hK, hfib, huniv⟩ :=
    GlobalTheory.T.exists_heckeKernelLists_modulo_permutations E H D l Xo 𝔓 p i (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) hA
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (π₁ ≫ Xo.s) π₁ rfl rfl
    (by simp [spMap]) Xo.univ
  obtain ⟨m', hm'⟩ := ((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ oY).2 π₁ q m₁).2 m
  have h₁ := m₁.cart.1
  have h₂ := m'.cart.1
  have hσ : ∀ j, (σ j).left ≫ oY.t.G.hom = 𝟙 Y := fun j => Over.w (σ j)
  rw [hm'] at hfib
  have hfib' := fun (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y) e => ((hfib k y y').1 e).1
  have hKσ := hL.2.1
  have hpre : K = m'.toSABMap.φ ⁻¹' (m'.toSABMap.φ '' K) := by
    have := preimage_eq (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' (h := 𝟙 Y) (ν := m'.toSABMap.φ)
      (gT := oY.t.G.hom) (by simpa using h₂) (τ := fun j => (σ j).left) hσ (fun j => by simp)
    rw [hKσ]; exact this
  refine ⟨Hk, π₁, o₁, m₁, m'.toSABMap.φ '' K, hπf, hπe, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.heckeSet_descends E H D l 𝔓 p i _ _ _ _ q o₁ oY m' _ hA hqs (hpre ▸ hK)
  · refine etSet_of_lists _ _ q _ _ m'.toSABMap.φ (p ^ 2) _ σ _ (ObjDim.isAbelianScheme o₁) m'.cart ?_ hqf hqe hqs
      (hpre ▸ hL)
    have := ((baseKA l).unit (p ^ 2) (pow_pos hA.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ (π₁ ≫ Xo.s).appTop).hom
    rwa [map_natCast] at this
  · intro k _ _ z z' e h
    obtain ⟨y, rfl⟩ := exists_lift_of_finite q z
    obtain ⟨y', rfl⟩ := exists_lift_of_finite q z'
    rw [Category.assoc, Category.assoc] at e
    rw [hKσ] at h
    refine (hfib k y y').2 ⟨subset_antisymm ?_ ?_, e⟩
    · exact range_subset_range (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' y y' e fun u u' hu hu' e' =>
        (h (Over.homMk u hu) (Over.homMk u' hu') e').1
    · exact range_subset_range (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' y' y e.symm fun u u' hu hu' e' =>
        (h (Over.homMk u' hu') (Over.homMk u hu) e'.symm).2
  · intro T s o f mu τ K' hL' hK'
    obtain ⟨h, hf, hh⟩ := huniv T f o.t mu.toSABMap τ K' hL' hK'
    rw [← Category.assoc] at hf
    subst hf
    obtain ⟨n, hn⟩ := ((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ (h ≫ q) m₁).2 mu
    have h₃ := n.cart.1
    have hτ : ∀ j, (τ j).left ≫ o.t.G.hom = 𝟙 T := fun j => Over.w (τ j)
    refine ⟨h ≫ q, n, rfl, hn.symm, ?_⟩
    rw [hL'.2.1, hKσ]
    refine preimage_eq (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' h₃ (τ := fun j => (τ j).left) hτ fun j => ?_
    refine h₁.hom_ext ?_ ?_
    · have := hh j
      rw [hm', hn] at this
      simpa using this.symm
    · have e₁ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (h ≫ q)) (hτ j))
      have e₂ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) (hσ j))
      simp only [Category.assoc, h₃.w, h₂.w]
      exact (e₁.trans (Category.id_comp _)).trans (congrArg (h ≫ ·) (e₂.trans (Category.id_comp _)).symm)

end GlobalTheory.HkFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernel_scheme_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ (Hk : Scheme.{0}) (π₁ : Hk ⟶ Xo.X) (o₁ : Ob D l (π₁ ≫ Xo.s)) (m₁ : ObjMap o₁ Xo.univ π₁) (K : Set o₁.t.G.left), IsFinite π₁ ∧ Etale π₁ ∧ HeckeSet D o₁.t 𝔓 p i K ∧ EtSet o₁.t.G K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Hk) (z' : Sp k ⟶ Hk), z ≫ π₁ = z' ≫ π₁ → (∀ (u : Over.mk z ⟶ o₁.t.G) (u' : Over.mk z' ⟶ o₁.t.G), u.left ≫ m₁.toSABMap.φ = u'.left ≫ m₁.toSABMap.φ → (Set.range u.left ⊆ K ↔ Set.range u'.left ⊆ K)) → z = z') ∧ ∀ (T : Scheme.{0}) (s : T ⟶ Sp (KA l)) (o : Ob D l s) (f : T ⟶ Xo.X) (mu : ObjMap o Xo.univ f) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over T) ⟶ o.t.G)) (K' : Set o.t.G.left), Lists (p ^ 2) τ K' → HeckeSet D o.t 𝔓 p i K' → ∃ (h : T ⟶ Hk) (n : ObjMap o o₁ h), h ≫ π₁ = f ∧ n.toSABMap.φ ≫ m₁.toSABMap.φ = mu.toSABMap.φ ∧ K' = n.toSABMap.φ ⁻¹' K := by
  first | exact @GlobalTheory.HkFam.exists_heckeKernelScheme | exact GlobalTheory.HkFam.exists_heckeKernelScheme | (intros; apply GlobalTheory.HkFam.exists_heckeKernelScheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversalReducedBases
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem range_subset_iff_of_charts {X Hk S S₁ S₂ U G₀ G G₁ G₂ P : Scheme.{0}} {g₀ : G₀ ⟶ Hk} {gU : U ⟶ X}
    {m₁ : G₀ ⟶ U} {f : S ⟶ X} {g : G ⟶ S} {mu : G ⟶ U} (hmu : IsPullback mu g gU f)
    {K : Set G₀} {K' : Set G}
    {q₁ : S₁ ⟶ S} {g₁ : G₁ ⟶ S₁} {a₁ : G₁ ⟶ G} (ha₁ : a₁ ≫ g = g₁ ≫ q₁) {h₁ : S₁ ⟶ Hk} {n₁ : G₁ ⟶ G₀}
    (hn₁ : IsPullback n₁ g₁ g₀ h₁) (e₁ : n₁ ≫ m₁ = a₁ ≫ mu) (k₁ : a₁ ⁻¹' K' = n₁ ⁻¹' K)
    {q₂ : S₂ ⟶ S} {g₂ : G₂ ⟶ S₂} {a₂ : G₂ ⟶ G} (ha₂ : a₂ ≫ g = g₂ ≫ q₂) {h₂ : S₂ ⟶ Hk} {n₂ : G₂ ⟶ G₀}
    (hn₂ : IsPullback n₂ g₂ g₀ h₂) (e₂ : n₂ ≫ m₁ = a₂ ≫ mu) (k₂ : a₂ ⁻¹' K' = n₂ ⁻¹' K)
    (x₁ : P ⟶ S₁) (x₂ : P ⟶ S₂) (hx : x₁ ≫ q₁ = x₂ ≫ q₂)
    (u₁ u₂ : P ⟶ G₀) (hu₁ : u₁ ≫ g₀ = x₁ ≫ h₁) (hu₂ : u₂ ≫ g₀ = x₂ ≫ h₂) (hu : u₁ ≫ m₁ = u₂ ≫ m₁) :
    (Set.range u₁ ⊆ K ↔ Set.range u₂ ⊆ K) := by
  have key : ∀ {A B : Scheme.{0}} (w : P ⟶ A) (c : A ⟶ B) (L : Set B),
      Set.range (w ≫ c) ⊆ L ↔ Set.range w ⊆ c ⁻¹' L := by
    intro A B w c L
    simp [Set.range_subset_iff]
  obtain ⟨w₁, hw₁, hw₁'⟩ := hn₁.exists_lift u₁ x₁ hu₁
  obtain ⟨w₂, hw₂, hw₂'⟩ := hn₂.exists_lift u₂ x₂ hu₂
  have hw : w₁ ≫ a₁ = w₂ ≫ a₂ := by
    apply hmu.hom_ext
    · rw [Category.assoc, Category.assoc, ← e₁, ← e₂, ← Category.assoc, ← Category.assoc, hw₁, hw₂, hu]
    · rw [Category.assoc, Category.assoc, ha₁, ha₂, ← Category.assoc, ← Category.assoc, hw₁', hw₂', hx]
  rw [← hw₁, ← hw₂, key, key, ← k₁, ← k₂, ← key, ← key, hw]

theorem exists_kerScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ Z : KerScheme Xo 𝔓 p i, EtSet Z.o₁.t.G Z.K := by
  intro E _ _ _ H D l Xo 𝔓 p i hA
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨Hk, π₁, o₁, m₁, K, fin₁, et₁, hK, hE, hpt, hex⟩ := GlobalTheory.T.exists_heckeKernel_scheme_universal E H D l Xo 𝔓 p i hA
  refine ⟨⟨Hk, π₁, fin₁, et₁, o₁, m₁, K, hK, hE, ?_⟩, hE⟩
  intro S s hS o K' hE' hK'
  obtain ⟨f, ⟨hf, ⟨mu⟩⟩, hfu⟩ := Xo.rep S s hS o
  obtain ⟨S', π, o', m, τ, hπ₁, hπ₂, hπ₃, hL⟩ := GlobalTheory.T.hecke_set_etale_level_structure_exists E H D l 𝔓 p i S s o K' hA hE' hK'
  have hK'' := ((GlobalTheory.heckeSets_pull E H D 𝔓 p i S S' o.t o'.t π m.toSABMap o.proper).2 K').1 hK'
  obtain ⟨mu', hmu'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 f π mu).1 m
  obtain ⟨h', n', hh', hn', hKn'⟩ := hex S' (π ≫ s) o' (π ≫ f) mu' τ _ hL hK''
  have cm := m.cart.1
  have cm₁ := m₁.cart.1
  have cn' := n'.cart.1
  haveI : IsReduced S' := GlobalTheory.isReduced_of_smooth_of_isReduced π
  haveI : IsReduced (pullback π π : Scheme.{0}) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst π π)
  have hd : pullback.fst π π ≫ h' = pullback.snd π π ≫ h' := by
    have h0 : (pullback.fst π π ≫ h') ≫ π₁ = (pullback.snd π π ≫ h') ≫ π₁ := by
      rw [Category.assoc, Category.assoc, hh', pullback.condition_assoc]
    refine hom_ext_of_geometric_points _ _ _ π₁ _ _ h0 ?_
    intro k _ _ x
    refine hpt k _ _ (by rw [Category.assoc, Category.assoc x, h0]) ?_
    intro u u' huu
    exact range_subset_iff_of_charts mu.cart.1 cm.w cn' (hn'.trans hmu') hKn' cm.w cn' (hn'.trans hmu') hKn'
      (x ≫ pullback.fst π π) (x ≫ pullback.snd π π) (by rw [Category.assoc, Category.assoc, pullback.condition])
      u.left u'.left (by rw [Category.assoc]; exact Over.w u) (by rw [Category.assoc]; exact Over.w u') huu
  obtain ⟨h, hh⟩ : ∃ h : S ⟶ Hk, π ≫ h = h' := by
    suffices hc : ∀ {Z : Scheme.{0}} (a b : Z ⟶ S'), a ≫ π = b ≫ π → a ≫ h' = b ≫ h' from
      ⟨EffectiveEpi.desc π h' hc, EffectiveEpi.fac π h' hc⟩
    focus
      intro Z a b hab
      have := congrArg (pullback.lift a b hab ≫ ·) hd
      simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  have hhf : h ≫ π₁ = f := by
    rw [← cancel_epi π, ← Category.assoc, hh, hh']
  subst hhf
  obtain ⟨n, hn⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ h m₁).2 mu
  have cn := n.cart.1
  have hmn : m.toSABMap.φ ≫ n.toSABMap.φ = n'.toSABMap.φ := by
    apply cm₁.hom_ext
    · rw [Category.assoc, ← hn]
      exact (hn'.trans hmu').symm
    · rw [Category.assoc, cn.w, cn'.w, ← Category.assoc, cm.w, Category.assoc, hh]
  have hsurj : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback cm.flip hπ₃
  have hKn : K' = n.toSABMap.φ ⁻¹' K := by
    apply hsurj.surj.preimage_injective
    rw [hKn', ← hmn]
    ext y
    simp
  refine ⟨h, ⟨by rw [← Category.assoc, hf], n, hKn⟩, ?_⟩
  rintro h₂ ⟨hs₂, n₂, hKn₂⟩
  obtain ⟨mu₂, hmu₂⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ h₂ m₁).1 n₂
  have h0 : h₂ ≫ π₁ = h ≫ π₁ := hfu _ ⟨by rw [Category.assoc, hs₂], ⟨mu₂⟩⟩
  have hrig : ∀ (f₂ : S ⟶ Xo.X) (mu₂ : ObjMap o Xo.univ f₂), f₂ = h ≫ π₁ → mu₂.toSABMap.φ = mu.toSABMap.φ := by
    intro f₂ mu₂ e
    subst e
    exact GlobalTheory.obj_rigid_closed laws E H D l _ _ _ _ _ _ _ _ Xo.univ o _ (Or.inl hS) _ _
      fun a => ⟨_, mu₂.eta a, mu.eta a⟩
  have e₂ := hmu₂.symm.trans (hrig _ mu₂ h0)
  refine hom_ext_of_geometric_points _ _ _ π₁ _ _ h0 ?_
  intro k _ _ x
  refine hpt k _ _ (by rw [Category.assoc, Category.assoc x, h0]) ?_
  intro u u' huu
  exact range_subset_iff_of_charts (q₁ := 𝟙 S) (q₂ := 𝟙 S) (a₁ := 𝟙 _) (a₂ := 𝟙 _) (K' := K') mu.cart.1 (by simp) n₂.cart.1
    (by rw [Category.id_comp]; exact e₂) (by rw [← hKn₂]; simp) (by simp) cn (by rw [Category.id_comp]; exact hn.symm)
    (by rw [← hKn]; simp) x x rfl u.left u'.left (Over.w u) (Over.w u') huu

end GlobalTheory.HkFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversalReducedBasesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernelScheme_universal_reduced_bases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ Z : KerScheme Xo 𝔓 p i, EtSet Z.o₁.t.G Z.K := by
  first | exact @GlobalTheory.HkFam.exists_kerScheme | exact GlobalTheory.HkFam.exists_kerScheme | (intros; apply GlobalTheory.HkFam.exists_kerScheme <;> assumption)
end
