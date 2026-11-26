module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertDataOfIsoCube
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRing
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

theorem stalkMap_germ_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens) (h : W' ≤ f ⁻¹ᵁ W)
    (z : Z) (hz : z ∈ W') (s : Γ(Y, W)) :
    (f.stalkMap z).hom ((Y.presheaf.germ W (f z) (h hz)).hom s) =
      (Z.presheaf.germ W' z hz).hom ((f.appLE W W' h).hom s) := by
  have e : Y.presheaf.germ W (f z) (h hz) ≫ f.stalkMap z = f.appLE W W' h ≫ Z.presheaf.germ W' z hz := by
    erw [Scheme.Hom.germ_stalkMap]
    rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  exact congrArg (fun g => g.hom s) e

theorem sec_eq_of_openImm {Y : Scheme.{0}} (W : Y.Opens) (s t : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (_ : IsOpenImmersion f) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ (f.appLE W W' h).hom s = (f.appLE W W' h).hom t) : s = t := by
  apply TopCat.Presheaf.section_ext Y.sheaf W s t
  intro p hp
  obtain ⟨Z, f, _, z, W', h, hz, rfl, e⟩ := H p hp
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback (f.stalkMap z))
  have e1 := stalkMap_germ_appLE f W W' h z hz s
  have e2 := stalkMap_germ_appLE f W W' h z hz t
  rw [e] at e1
  exact e1.trans e2.symm

theorem sec_isUnit_of_pull {Y : Scheme.{0}} (W : Y.Opens) (s : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ IsUnit ((f.appLE W W' h).hom s)) : IsUnit s := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ W s
  intro p hp
  obtain ⟨Z, f, z, W', h, hz, rfl, u⟩ := H p hp
  apply isUnit_of_map_unit (f.stalkMap z).hom
  rw [stalkMap_germ_appLE f W W' h z hz]
  exact u.map _

def spConst (R : Type) [CommRing R] (W : (Sp R).Opens) : R →+* Γ(Sp R, W) :=
  (resG (Sp R) (le_top : W ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem appLE_spConst {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (W : (Sp R).Opens)
    (W' : (Sp R').Opens) (h : W' ≤ spMap φ ⁻¹ᵁ W) (r : R) :
    ((spMap φ).appLE W W' h).hom (spConst R W r) = spConst R' W' (φ r) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
      (spMap φ).appLE W W' h =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
        (Sp R').presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  exact congrArg (fun g => g.hom r) key

private theorem mem_pull_U_iff' {X T : Scheme.{0}} (M : LB X) (y : T ⟶ X) (j : PUnit → M.ι) (p : T) :
    p ∈ (M.pull y).U j ↔ y p ∈ M.U (j PUnit.unit) := by
  unfold LB.pull LB.LinComb LB.wchart
  simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage]
  exact ⟨fun h => h _, fun h _ => h⟩

private theorem appLE_appLE_lemma_2 {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (V' : Z.Opens) (hV : V ≤ g ⁻¹ᵁ U) (hV' : V' ≤ f ⁻¹ᵁ V) (h3 : V' ≤ (f ≫ g) ⁻¹ᵁ U) (s : Γ(X, U)) :
    (f.appLE V V' hV').hom ((g.appLE U V hV).hom s) = ((f ≫ g).appLE U V' h3).hom s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

private theorem appLE_resG_eq_resG_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) {V1 V2 : Y.Opens} {W1 W2 : Z.Opens}
    (hV : V1 ≤ V2) (hW : W1 ≤ W2) (h1 : W1 ≤ f ⁻¹ᵁ V1) (h2 : W2 ≤ f ⁻¹ᵁ V2) (s : Γ(Y, V2)) :
    (f.appLE V1 W1 h1).hom (resG Y hV s) = resG Z hW ((f.appLE V2 W2 h2).hom s) := by
  simp only [resG]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]

private theorem pull_g_coe_eq_appLE_g {X T : Scheme.{0}} (M : LB X) (y : T ⟶ X) (j j' : PUnit → M.ι)
    (h : (M.pull y).U j ⊓ (M.pull y).U j' ≤ y ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (((M.pull y).g j j' : (Γ(T, (M.pull y).U j ⊓ (M.pull y).U j'))ˣ) : Γ(T, (M.pull y).U j ⊓ (M.pull y).U j')) =
      (y.appLE _ _ h).hom (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(X, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) := by
  unfold LB.pull LB.LinComb
  simp [pullU, res, Scheme.Hom.appLE]
  rfl

theorem secCoord_of_locally (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R]
    (x : Sp R ⟶ X) (v : I → R) (_hM : M.IsLB) (hv : Ideal.span (Set.range v) = ⊤)
    (H : ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧
      p ∈ Set.range (spMap φ) ∧ SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) :
    SecCoord M th x v := by
  have h1 : (1 : R) ∈ Ideal.span (Set.range v) := by rw [hv]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 h1
  have W1 : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit) :=
    fun j p hp => (mem_pull_U_iff' M x j p).1 hp
  have W2 : ∀ {R' : Type} [CommRing R'] (φ : R →+* R') (j : PUnit → M.ι),
      (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun φ j z hz => (mem_pull_U_iff' M x j _).2 ((mem_pull_U_iff' M _ j z).1 hz)
  let t : ∀ j : PUnit → M.ι, Γ(Sp R, (M.pull x).U j) := fun j =>
    c.sum (fun i a => spConst R _ a * (x.appLE _ _ (W1 j)).hom ((th i).f (j PUnit.unit)))
  have pt : ∀ {R' : Type} [CommRing R'] (φ : R →+* R') (τ' : (M.pull (spMap φ ≫ x)).Gen),
      (∀ i j h, ((spMap φ ≫ x).appLE (M.U (j PUnit.unit)) ((M.pull (spMap φ ≫ x)).U j) h).hom
          ((th i).f (j PUnit.unit)) = spConst R' _ (φ (v i)) * (τ'.s j).val) →
      ∀ j, ((spMap φ).appLE _ _ (W2 φ j)).hom (t j) = (τ'.s j).val := by
    intro R' _ φ τ' hco j
    have e1 : ∀ i, ((spMap φ).appLE _ _ (W2 φ j)).hom
        (spConst R _ (c i) * (x.appLE _ _ (W1 j)).hom ((th i).f (j PUnit.unit))) =
        spConst R' _ (φ (c i) * φ (v i)) * (τ'.s j).val := by
      intro i
      rw [map_mul, appLE_spConst, appLE_appLE_lemma_2 (spMap φ) x _ _ _ (W1 j) (W2 φ j)
        (fun p hp => (mem_pull_U_iff' M _ j p).1 hp), map_mul, _root_.mul_assoc]
      exact congrArg (spConst R' _ (φ (c i)) * ·) (hco i j (fun p hp => (mem_pull_U_iff' M _ j p).1 hp))
    have e2 : ∑ i ∈ c.support, φ (c i) * φ (v i) = 1 := by
      have := congrArg φ hc
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_one, Finsupp.sum, map_sum] at this
      simpa [map_mul] using this
    show ((spMap φ).appLE _ _ (W2 φ j)).hom (∑ i ∈ c.support, _) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_mul, ← map_sum, e2, map_one, _root_.one_mul]
  have hu : ∀ j, IsUnit (t j) := by
    intro j
    apply sec_isUnit_of_pull
    intro p hp
    obtain ⟨R', _, φ, _, ⟨z, rfl⟩, τ', _, hco⟩ := H p
    refine ⟨Sp R', spMap φ, z, (M.pull (spMap φ ≫ x)).U j, W2 φ j, ?_, rfl, ?_⟩
    · exact (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp)
    · rw [pt φ τ' hco j]; exact (τ'.s j).isUnit
  unfold SecCoord
  refine ⟨⟨fun j => (hu j).unit⟩, ?_, ?_⟩
  · intro i j
    apply Units.ext
    show resG _ inf_le_left (t i) = ((M.pull x).g i j).val * resG _ inf_le_right (t j)
    apply sec_eq_of_openImm
    intro p hp
    obtain ⟨R', _, φ, hoi, ⟨z, rfl⟩, τ', hg, hco⟩ := H p
    have Wi : (M.pull (spMap φ ≫ x)).U i ⊓ (M.pull (spMap φ ≫ x)).U j ≤
        spMap φ ⁻¹ᵁ ((M.pull x).U i ⊓ (M.pull x).U j) := fun z hz => ⟨W2 φ i hz.1, W2 φ j hz.2⟩
    refine ⟨Sp R', spMap φ, hoi, z, _, Wi, ?_, rfl, ?_⟩
    · exact ⟨(mem_pull_U_iff' M _ i z).2 ((mem_pull_U_iff' M x i _).1 hp.1),
        (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp.2)⟩
    · rw [map_mul, appLE_resG_eq_resG_appLE (spMap φ) inf_le_left inf_le_left Wi (W2 φ i),
        appLE_resG_eq_resG_appLE (spMap φ) inf_le_right inf_le_right Wi (W2 φ j), pt φ τ' hco i, pt φ τ' hco j]
      have h3 : (M.pull (spMap φ ≫ x)).U i ⊓ (M.pull (spMap φ ≫ x)).U j ≤
          (spMap φ ≫ x) ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
        fun q hq => ⟨(mem_pull_U_iff' M _ i q).1 hq.1, (mem_pull_U_iff' M _ j q).1 hq.2⟩
      rw [pull_g_coe_eq_appLE_g M x i j (fun q hq => ⟨W1 i hq.1, W1 j hq.2⟩)]
      erw [appLE_appLE_lemma_2 (spMap φ) x _ _ _ _ Wi h3, ← pull_g_coe_eq_appLE_g M (spMap φ ≫ x) i j h3]
      exact congrArg Units.val (hg i j)
  · intro i j h
    show _ = spConst R _ (v i) * t j
    apply sec_eq_of_openImm
    intro p hp
    obtain ⟨R', _, φ, hoi, ⟨z, rfl⟩, τ', _, hco⟩ := H p
    refine ⟨Sp R', spMap φ, hoi, z, _, W2 φ j, ?_, rfl, ?_⟩
    · exact (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp)
    · rw [map_mul, appLE_spConst, pt φ τ' hco j, appLE_appLE_lemma_2 (spMap φ) x _ _ _ h (W2 φ j)
        (fun p hp => (mem_pull_U_iff' M _ j p).1 hp)]
      exact hco i j (fun p hp => (mem_pull_U_iff' M _ j p).1 hp)

end GlobalTheory.ZM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), M.IsLB → Ideal.span (Set.range v) = ⊤ → (∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) → SecCoord M th x v := by
  first | exact @GlobalTheory.ZM.secCoord_of_locally | exact GlobalTheory.ZM.secCoord_of_locally | (intros; apply GlobalTheory.ZM.secCoord_of_locally <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreAct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.FibreAct

theorem isGrpPullback_of_iso {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (ψ : G' ⟶ G) [IsIso ψ]
    [IsMonHom ψ] : IsGrpPullback G' G (𝟙 S) ψ.left := by
  haveI : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget S).map ψ))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let U : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = U ≫ x ≫ ψ := Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)
  have ey : y₀ = U ≫ y ≫ ψ := Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)
  rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
  exact Category.id_comp _

theorem exists_lift_act {O : Type} [CommRing O] {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OAct O G) :
    ∃ a' : OAct O G', ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left := by
  have w : ∀ c, (φ ≫ (a.act c).left) ≫ G.hom = G'.hom ≫ f := fun c => by
    rw [Category.assoc, Over.w, h.1.w]
  let r : O → (G' ⟶ G') := fun c => Over.homMk (h.1.lift (φ ≫ (a.act c).left) G'.hom (w c)) (h.1.lift_snd _ _ _)
  have hr : ∀ c, (r c).left ≫ φ = φ ≫ (a.act c).left := fun c => h.1.lift_fst _ _ _
  have key : ∀ T : Over S', ∃ e : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G),
      ∀ x c, e (x ≫ r c) = e x ≫ a.act c := fun T => by
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h T _ rfl
    exact ⟨e, fun x c => Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hr, Category.assoc])⟩
  obtain ⟨e, he⟩ := key G'
  have he' : ∀ c, e (r c) = e (𝟙 G') ≫ a.act c := fun c => by rw [← he, Category.id_comp]
  refine ⟨⟨r, fun c => ?_, e.injective ?_, fun c d => e.injective ?_, fun c d => e.injective ?_⟩, hr⟩
  · haveI := a.hom c
    refine ⟨?_, ?_⟩
    · obtain ⟨e₁, he₁⟩ := key (𝟙_ (Over S'))
      have o : η[G'] = (1 : 𝟙_ (Over S') ⟶ G') := by rw [Hom.one_def]; simp
      apply e₁.injective
      rw [he₁, o, map_one, MonObj.one_comp]
    · obtain ⟨e₂, he₂⟩ := key (G' ⊗ G')
      have m₁ : μ[G'] = fst G' G' * snd G' G' := by rw [Hom.mul_def]; simp
      have m₂ : (r c ⊗ₘ r c) ≫ μ[G'] = (fst G' G' ≫ r c) * (snd G' G' ≫ r c) := by
        rw [Hom.mul_def]; congr 1
      apply e₂.injective
      rw [m₂, he₂, m₁, map_mul, map_mul, he₂, he₂, MonObj.mul_comp]
  · rw [he', a.one, Category.comp_id]
  · rw [he, he', he', a.mul, Category.assoc]
  · rw [map_mul, he', he', he', a.add, MonObj.comp_mul]

theorem exists_fibre_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H S) (x : Sp ℂ ⟶ S) (β : o →+* ℂ) (A₀ : Over (Sp ℂ)) [GrpObj A₀] (m : A₀.left ⟶ t.A.left), IsPEL D a bas ρ t τ → x ≫ s = spMap β → IsGrpPullback A₀ t.A x m → ∃ (act : OAct (𝓞 E) t.A) (act₀ : OAct (𝓞 E) A₀), (∀ c, (act₀.act c).left ≫ m = m ≫ (act.act c).left) ∧ DetCond D act₀ (𝟙 _) (β ρ) := by
  intro E _ _ _ H D g k J a bas o _ b ρ S s t τ x β A₀ _ m hP hx hm
  obtain ⟨φ, hφ, -, -, hd⟩ := hP
  haveI := hφ
  have hi : IsGrpPullback t.A τ.G (𝟙 S) φ.inv.left := isGrpPullback_of_iso φ.inv
  obtain ⟨act, hact⟩ := exists_lift_act hi τ.act
  obtain ⟨act₀, hact₀⟩ := exists_lift_act hm act
  refine ⟨act, act₀, hact₀, fun σ => ?_⟩
  have L : ∀ n, LieMult act₀ (𝟙 _) σ n ↔ LieMult τ.act x σ n := fun n => by
    rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hm hact₀ ℂ (𝟙 _) σ n,
      GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hi hact ℂ _ σ n, Category.id_comp, Category.comp_id]
  rw [L, L]
  exact (hd ℂ x β hx).1 σ

end GlobalTheory.FibreAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLatticeUniformisationOfPrimTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLatticeUniformisationOfPrimTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PrimUnif

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (n : ℕ)
    (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  have hz : u.ex 0 = 1 := by
    have h := u.ex_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  induction n with
  | zero => simpa using hz
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem unitOn_inj' {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := by
  intro a b h
  ext
  have h' := congrArg (fun x : Γ(Sp K, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (x : Γ(Sp K, ⊤))) h
  simpa [unitOn] using h'

theorem unitS_spMap {o K : Type} [CommRing o] [CommRing K] (em : o →+* K) (c : oˣ) :
    unitS (spMap em) c = unitOn (Units.map em.toMonoidHom c) := by
  ext
  simp only [unitS, unitOn, spMap, Units.coe_map]
  have h := congrArg (fun φ => φ.hom (c : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom em))
  exact h.symm

theorem exists_unif_of_prim :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)), t.Prim w w' → ∃ (La : Type) (_ : AddCommGroup La) (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) ∧ (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro hL _ _ hU o _ g k J b em w w' t hP
  have hk : ((k : ℕ) : ℂ) ≠ 0 := by
    have h := b.unit.map em
    rw [map_natCast] at h
    exact h.ne_zero
  obtain ⟨rig, hrig⟩ := t.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, hEnd, -, hEf, hEfb, hWeil⟩ := hU t.pol rig hrig
  choose F hF using fun j => hEnd (t.act j) (t.hom j)
  have hone : ∀ j, (1 : 𝟙_ (Over (Sp ℂ)) ⟶ t.A) ≫ t.act j = 1 := fun j => by
    have := t.hom j
    simp [Hom.one_def]
  have hFm : ∀ j (l : u.Λ), F j l ∈ u.Λ := fun j l => by
    rw [← u.ker, hF, (u.ker _).2 l.2]
    exact hone j
  choose z hz using fun i => u.ex_onto (t.pt i)
  have hlam : ∀ i, ((k : ℕ) : ℂ) • z i ∈ u.Λ := fun i => by
    rw [← u.ker, ex_nsmul, hz]
    exact t.torsion i
  have hlev : ∀ i, u.ex (((k : ℕ) : ℂ)⁻¹ • (((k : ℕ) : ℂ) • z i)) = t.pt i := fun i => by
    rw [inv_smul_smul₀ hk, hz]
  refine ⟨u.Λ, inferInstance, Ef, fun i => ⟨_, hlam i⟩, fun j x => ⟨F j x, hFm j x⟩,
    u.Λ.subtype.toAddMonoidHom, Hm, hEfb, ⟨Subtype.val_injective, ?_, ?_, hAH.1, hAH.2.1,
      fun x y => (hEf x y).symm⟩, ?_, u, χ, hAH, ?_, ?_, ?_, ?_⟩
  · have key : ∀ S : AddSubgroup (Fin g → ℂ), (∀ x, x ∈ S ↔ x ∈ u.Λ) → DiscreteTopology S := by
      intro S hS
      obtain rfl : S = u.Λ.toAddSubgroup := AddSubgroup.ext hS
      exact u.discrete
    refine key _ (fun x => ⟨fun h => ?_, fun h => AddMonoidHom.mem_range.2 ⟨⟨x, h⟩, rfl⟩⟩)
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.1 h
    exact y.2
  · have hs : Set.range (fun x : u.Λ => (x : Fin t.pol.g → ℂ)) = (u.Λ : Set (Fin t.pol.g → ℂ)) :=
      Subtype.range_coe
    have hfull := u.full
    rw [← hs] at hfull
    exact hfull
  · intro i₁ i₂
    have hkpos : 0 < k := Nat.pos_of_ne_zero (fun h => hk (by simp [h]))
    have hW := hWeil k ⟨_, hlam i₁⟩ ⟨_, hlam i₂⟩
      (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (Ef ⟨_, hlam i₁⟩ ⟨_, hlam i₂⟩ : ℂ) / ((k : ℕ) : ℂ))))
      hkpos rfl
    simp only [hlev] at hW
    have hP2 := t.pairing i₁ i₂
    rw [unitS_spMap] at hP2
    have hu := ((hL.weil (Sp ℂ) t.pol k (𝟙_ _)).1 (t.pt i₁) (t.pt i₂) (t.torsion i₁) (t.torsion i₂)).unique hW hP2
    have hpow : ∀ (x : ℂˣ) (n : ℤ), unitOn x ^ n = unitOn (x ^ n) := by
      intro x n
      unfold unitOn
      rw [map_zpow]
    rw [hpow] at hu
    have hc := congrArg Units.val (unitOn_inj' hu)
    simpa [Units.val_zpow_eq_zpow_val] using hc
  · intro x
    refine ⟨fun h => AddMonoidHom.mem_range.2 ⟨⟨x, h⟩, rfl⟩, fun h => ?_⟩
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.1 h
    exact y.2
  · intro x l hl
    have hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) := fun X x => valAt'_rules X x
    have : IsCommMonObj t.pol.A := t.ab.comm
    have hAHd := GlobalTheory.SelfCube.appellHumbert_data_of_iso_cube hv (GlobalTheory.holFamily_lift hv) t.pol u Hm χ Ef
      ⟨hAH.1, hAH.2.2.1, fun a c => hEf a c, hAH.2.2.2⟩ (t.act w) (F w) (fun m hm => hFm w ⟨m, hm⟩) (hF w) hP.2.2
    obtain rfl : l = x := Subtype.ext hl
    exact hAHd.2 l
  · intro i
    exact congrArg (fun p => p.left) (hlev i).symm
  · intro j
    exact ⟨F j, fun x => rfl, hF j⟩

end GlobalTheory.PrimUnif

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLatticeUniformisationOfPrimThetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_uniformisation_of_prim_theta : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)), t.Prim w w' → ∃ (La : Type) (_ : AddCommGroup La) (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) ∧ (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.PrimUnif.exists_unif_of_prim | exact GlobalTheory.PrimUnif.exists_unif_of_prim | (intros; apply GlobalTheory.PrimUnif.exists_unif_of_prim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransportThetaLevelUniformisationCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransportThetaLevelUniformisationCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.UnifTransport

theorem hermForm_smul_left {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm H (c • z) w = c * hermForm H z w := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

theorem hermForm_add_left {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm H (z + z') w = hermForm H z w + hermForm H z' w := by
  simp only [hermForm, add_dotProduct]

theorem hermForm_add_right {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm H z (w + w') = hermForm H z w + hermForm H z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_smul_right {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm H z (c • w) = star c * hermForm H z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hermForm_eq_of_im {g : ℕ} (H H' : Matrix (Fin g) (Fin g) ℂ)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (him : ∀ x ∈ S, ∀ y ∈ S, (hermForm H' (h x) (h y)).im = (hermForm H x y).im) (z w : Fin g → ℂ) :
    hermForm H' (h z) (h w) = hermForm H z w := by
  have first : ∀ y ∈ S, ∀ x, (hermForm H' (h x) (h y)).im = (hermForm H x y).im := by
    intro y hy
    let f₁ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => (hermForm H' (h x) (h y)).im
        map_add' := fun a c => by simp only [map_add (f := _), hermForm_add_left, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, map_smul, hermForm_smul_left, Complex.im_ofReal_mul] }
    let f₂ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => (hermForm H x y).im
        map_add' := fun a c => by simp only [hermForm_add_left, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, hermForm_smul_left, Complex.im_ofReal_mul] }
    have hf : f₁ = f₂ := LinearMap.ext_on hS (fun x hx => him x hx y hy)
    exact fun x => LinearMap.congr_fun hf x
  have both : ∀ x y, (hermForm H' (h x) (h y)).im = (hermForm H x y).im := by
    intro x
    let f₁ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => (hermForm H' (h x) (h y)).im
        map_add' := fun a c => by simp only [map_add (f := _), hermForm_add_right, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, map_smul, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal,
            Complex.im_ofReal_mul] }
    let f₂ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => (hermForm H x y).im
        map_add' := fun a c => by simp only [hermForm_add_right, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal,
            Complex.im_ofReal_mul] }
    have hf : f₁ = f₂ := LinearMap.ext_on hS (fun y hy => first y hy x)
    exact fun y => LinearMap.congr_fun hf y
  apply Complex.ext
  ·
    have hI := both (Complex.I • z) w
    rw [map_smul, hermForm_smul_left, hermForm_smul_left, Complex.I_mul_im, Complex.I_mul_im] at hI
    exact hI
  · exact both z w

theorem transport_uniformisation :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (La' : Type) [AddCommGroup La'] (EF' : LinearMap.BilinForm ℤ La') (lam' : Fin (2 * g) → La') (ac' : J → La' → La') (Q' : La' →+ (Fin g → ℂ)) (Hm' : Matrix (Fin g) (Fin g) ℂ) (e : La ≃+ La') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (Function.Injective Q' ∧ DiscreteTopology (Q').range ∧ Submodule.span ℝ (Set.range Q') = ⊤ ∧ (Hm').IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧ ∀ x y, (hermForm Hm' (Q' x) (Q' y)).im = EF' x y) → (∀ x, Q' (e x) = h (Q x)) → (∀ x y, EF' (e x) (e y) = EF x y) → (∀ j x, e (ac j x) = ac' j (e x)) → (∀ i, ∃ y, e (lam i) = lam' i + k • y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm' χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q').range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q' x → χ' l = (-1) ^ EF' x (ac' w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q' x) = Q' (ac' j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro o _ g k J b em w w' t La _ EF lam ac Q Hm La' _ EF' lam' ac' Q' Hm' e h hA hA' hQ hE hac hlam hU
  obtain ⟨u, χ', hAH, hΛ, hχ, hpt, hact⟩ := hU

  have hsym : ∀ x, h.symm (Q' x) = Q (e.symm x) := by
    intro x
    have hx := hQ (e.symm x)
    rw [e.apply_symm_apply] at hx
    rw [hx, LinearEquiv.symm_apply_apply]

  have him : ∀ x ∈ Set.range Q, ∀ y ∈ Set.range Q,
      (hermForm Hm' ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) x)
        ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) y)).im = (hermForm Hm x y).im := by
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
    simp only [LinearEquiv.coe_coe]
    rw [← hQ, ← hQ, hA'.2.2.2.2.2, hA.2.2.2.2.2, hE]
  have hH : ∀ a c, a ⬝ᵥ Hm'.mulVec (star c) = (h.symm a) ⬝ᵥ Hm.mulVec (star (h.symm c)) := by
    intro a c
    have hac' := hermForm_eq_of_im Hm Hm' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Set.range Q) hA.2.2.1 him
      (h.symm a) (h.symm c)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hac'
    exact hac'

  have hper : ∀ a v, v ∈ u.Λ → u.ex (a - v) = u.ex a := by
    intro a v hv
    have hsplit := u.ex_add (a - v) v
    rw [sub_add_cancel, (u.ker v).2 hv, _root_.mul_one] at hsplit
    exact hsplit.symm
  refine ⟨holUnifReparam u h.symm (fun _ => 1) (differentiable_const 1) (fun _ => one_ne_zero),
    fun l => χ' ⟨h.symm l, l.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold HolUnif.IsAH
    refine ⟨hA'.2.2.2.1, hA'.2.2.2.2.1, fun l => hAH.2.2.1 _, ?_⟩
    intro l i z hz
    simp only [holUnifReparam, div_one, map_add (f := _)]
    rw [hH z l, hH l l]
    exact hAH.2.2.2 ⟨h.symm l, l.2⟩ i (h.symm z) hz
  · intro z
    show h.symm z ∈ u.Λ ↔ z ∈ Q'.range
    rw [hΛ]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨e a, ?_⟩
      rw [hQ, ha, LinearEquiv.apply_symm_apply]
    · rintro ⟨c, rfl⟩
      exact ⟨e.symm c, (hsym c).symm⟩
  · intro x l hl
    have hpos : h.symm (l : Fin g → ℂ) = Q (e.symm x) := by rw [hl, hsym]
    have hform := hE (e.symm x) (ac w (e.symm x))
    rw [hac, e.apply_symm_apply] at hform
    rw [hform]
    exact hχ (e.symm x) ⟨h.symm l, l.2⟩ hpos
  · intro i
    obtain ⟨y, hy⟩ := hlam i
    have hl : lam' i = e (lam i) - k • y := eq_sub_of_add_eq hy.symm
    have hmem : (((k : ℕ) : ℂ)⁻¹ * (k : ℂ)) • Q (e.symm y) ∈ u.Λ := by
      by_cases hk : ((k : ℕ) : ℂ) = 0
      · rw [hk, mul_zero, zero_smul]
        exact zero_mem _
      · rw [inv_mul_cancel₀ hk, one_smul]
        exact (hΛ _).2 ⟨e.symm y, rfl⟩
    have hpt' : h.symm (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i))
        = ((k : ℕ) : ℂ)⁻¹ • Q (lam i) - (((k : ℕ) : ℂ)⁻¹ * (k : ℂ)) • Q (e.symm y) := by
      rw [hl, map_sub, map_nsmul, map_smul, map_sub, map_nsmul, hsym, hsym, e.symm_apply_apply, smul_sub,
        mul_smul, Nat.cast_smul_eq_nsmul]
    show (t.pt i).left = (u.ex (h.symm (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i)))).left
    rw [hpt', hper _ _ hmem, hpt]
  · intro j
    obtain ⟨F, hF1, hF2⟩ := hact j
    refine ⟨(h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) ∘ₗ F ∘ₗ (h.symm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), ?_, ?_⟩
    · intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hsym, hF1, ← hQ, hac, e.apply_symm_apply]
    · intro z
      show u.ex (h.symm (h (F (h.symm z)))) = u.ex (h.symm z) ≫ t.act j
      rw [LinearEquiv.symm_apply_apply, hF2]

end GlobalTheory.UnifTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransportThetaLevelUniformisationCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_thetaLevel_uniformisation_coordinates : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (La' : Type) [AddCommGroup La'] (EF' : LinearMap.BilinForm ℤ La') (lam' : Fin (2 * g) → La') (ac' : J → La' → La') (Q' : La' →+ (Fin g → ℂ)) (Hm' : Matrix (Fin g) (Fin g) ℂ) (e : La ≃+ La') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (Function.Injective Q' ∧ DiscreteTopology (Q').range ∧ Submodule.span ℝ (Set.range Q') = ⊤ ∧ (Hm').IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧ ∀ x y, (hermForm Hm' (Q' x) (Q' y)).im = EF' x y) → (∀ x, Q' (e x) = h (Q x)) → (∀ x y, EF' (e x) (e y) = EF x y) → (∀ j x, e (ac j x) = ac' j (e x)) → (∀ i, ∃ y, e (lam i) = lam' i + k • y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm' χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q').range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q' x → χ' l = (-1) ^ EF' x (ac' w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q' x) = Q' (ac' j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.UnifTransport.transport_uniformisation | exact GlobalTheory.UnifTransport.transport_uniformisation | (intros; apply GlobalTheory.UnifTransport.transport_uniformisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SharpRelations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

noncomputable section
namespace GlobalTheory.SharpRel

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
  [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y := by
  have hl : x.left ≫ φ = y.left ≫ φ := congrArg CommaMorphism.left e
  ext1
  exact h.1.hom_ext hl (by rw [Over.w x, Over.w y])

theorem push_comp (h : IsGrpPullback A' A f φ) {p : A ⟶ A} {p' : A' ⟶ A'}
    (e : p'.left ≫ φ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h T (x ≫ p') = pushHom h T x ≫ p := by
  ext1
  change (x ≫ p').left ≫ φ = (x.left ≫ φ) ≫ p.left
  rw [Over.comp_left, Category.assoc, Category.assoc, e]

end

end GlobalTheory.SharpRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfAffineOpens
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfAffineOpens
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory

theorem smoothOfRelativeDimension_genericFibre_of_affine :
    ∀ (o : Type) [CommRing o] [IsDomain o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)))) → SmoothOfRelativeDimension d (pullback.snd s (spMap (algebraMap o (FractionRing o)))) := by
  intro o _ _ X s d h
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d)
    (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover s
      (spMap (algebraMap o (FractionRing o)))) fun i => ?_
  let R : CommRingCat.{0} := X.affineOpenCover.X i
  let x : Spec R ⟶ X := X.affineOpenCover.f i
  have hx : IsOpenImmersion x := X.affineOpenCover.map_prop i
  let φ : CommRingCat.of o ⟶ R := Spec.preimage (x ≫ s)
  letI : Algebra o R := φ.hom.toAlgebra
  have hφ : x ≫ s = spMap (algebraMap o R) := (Spec.map_preimage (x ≫ s)).symm
  have H := h R x hx hφ
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct o (FractionRing o) R)
  have sq' : IsPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := o) (A := FractionRing o) (B := R)).toRingHom))
      (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) (x ≫ s)
      (spMap (algebraMap o (FractionRing o))) := by
    rw [hφ]
    exact sq.flip
  have e : (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover s
      (spMap (algebraMap o (FractionRing o)))).f i ≫ pullback.snd s _ =
      sq'.isoPullback.inv ≫ spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)) := by
    rw [IsPullback.isoPullback_inv_snd]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e]
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension d) := hloc.1
  exact @MorphismProperty.RespectsIso.precomp _ _ (@SmoothOfRelativeDimension d) this _ _ _
    sq'.isoPullback.inv sq'.isoPullback.isIso_inv _ H

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfAffineOpensStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.smooth_genericFibre_of_affine_opens : ∀ (o : Type) [CommRing o] [IsDomain o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)))) → SmoothOfRelativeDimension d (pullback.snd s (spMap (algebraMap o (FractionRing o)))) := by
  first | exact @GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine | exact GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine | (intros; apply GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescOfIsFiniteOfDensePart
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescOfIsFiniteOfDensePart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isFinite_graphClosure_fst_of_isFinite {S X X' Y : Scheme.{0}} (π : X ⟶ X') (s' : X' ⟶ S)
    (p : Y ⟶ S) (f : X ⟶ Y) (h : π ≫ s' = f ≫ p) [IsFinite π] [IsSeparated p]
    [LocallyOfFiniteType p] : IsFinite (graphClosure.fst s' p π f h) := by
  have e := graphClosure.incl_fst s' p π f h
  have : IsFinite (graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h) := by
    rw [e]; infer_instance
  have : IsFinite (graphClosure.incl s' p π f h) :=
    IsFinite.of_comp _ (graphClosure.fst s' p π f h)
  have : Surjective (graphClosure.incl s' p π f h) :=
    surjective_of_isDominant_of_isClosed_range _
      (graphClosure.incl s' p π f h).isClosedMap.isClosed_range
  have : UniversallyClosed (graphClosure.fst s' p π f h) :=
    .of_comp_surjective (graphClosure.incl s' p π f h) _
  have : IsProper (graphClosure.fst s' p π f h) := {}
  have : LocallyQuasiFinite (graphClosure.fst s' p π f h) := by
    refine .of_finite_preimage_singleton _ fun s ↦ ?_
    refine (((graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h).finite_preimage_singleton
      s).image (graphClosure.incl s' p π f h)).subset fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (graphClosure.incl s' p π f h).surjective x
    exact ⟨y, by simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using hx, rfl⟩
  exact .of_isProper_of_locallyQuasiFinite _

theorem exists_desc_of_isFinite_of_densePart : ∀ (S X X' U U' Y : Scheme.{0}) [IsLocallyNoetherian X'] (π : X ⟶ X') (j : U ⟶ X) (j' : U' ⟶ X') (r : U ⟶ U') (s' : X' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) (f₀ : U' ⟶ Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → IsReduced X → IsFinite π → Surjective π → Surjective r → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsSeparated p → LocallyOfFiniteType p → j ≫ π = r ≫ j' → j ≫ f = r ≫ f₀ → f ≫ p = π ≫ s' → f₀ ≫ p = j' ≫ s' → ∃ f' : X' ⟶ Y, j' ≫ f' = f₀ ∧ π ≫ f' = f := by
  intro S X X' U U' Y _ π j j' r s' p f f₀ hX' _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄
  have := GlobalTheory.IsNormalScheme.of_pred hX'
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j'
  have : GlobalTheory.IsNormalScheme U' := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j'
  have := IsSchemeTheoreticallyDominant.of_isDominant r
  have := isFinite_graphClosure_fst_of_isFinite π s' p f h₃.symm
  let g := graphClosure.lift s' p π f h₃.symm j' f₀ h₄.symm r j h₁.symm h₂.symm
  have hg₁ : g ≫ graphClosure.fst s' p π f h₃.symm = j' := graphClosure.lift_fst ..
  have hg₂ : g ≫ graphClosure.snd s' p π f h₃.symm = f₀ := graphClosure.lift_snd ..
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, -⟩ := existsUnique_lift_of_densePart X' U' X' _ j' hX' ‹_› ‹_› ‹_› ‹_›
    (graphClosure.fst s' p π f h₃.symm) (𝟙 X') g inferInstance (by rw [hg₁, Category.comp_id])
  have h₅ : j' ≫ σ ≫ graphClosure.snd s' p π f h₃.symm = f₀ := by rw [reassoc_of% hσ₁, hg₂]
  refine ⟨σ ≫ graphClosure.snd s' p π f h₃.symm, h₅,
    ext_of_isDominant_of_isSeparated p ?_ j ?_⟩
  · rw [Category.assoc, Category.assoc, ← graphClosure.condition, reassoc_of% hσ₂, h₃]
  · rw [reassoc_of% h₁, h₅, h₂]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescOfIsFiniteOfDensePartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_desc_of_dense_preimmersion : ∀ (S X X' U U' Y : Scheme.{0}) [IsLocallyNoetherian X'] (π : X ⟶ X') (j : U ⟶ X) (j' : U' ⟶ X') (r : U ⟶ U') (s' : X' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) (f₀ : U' ⟶ Y), IsNormalScheme X' → IsReduced X → IsFinite π → Surjective π → Surjective r → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsSeparated p → LocallyOfFiniteType p → j ≫ π = r ≫ j' → j ≫ f = r ≫ f₀ → f ≫ p = π ≫ s' → f₀ ≫ p = j' ≫ s' → ∃ f' : X' ⟶ Y, j' ≫ f' = f₀ ∧ π ≫ f' = f := by
  first | exact @GlobalTheory.exists_desc_of_isFinite_of_densePart | exact GlobalTheory.exists_desc_of_isFinite_of_densePart | (intros; apply GlobalTheory.exists_desc_of_isFinite_of_densePart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackLocalOnBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.GrpLoc

theorem hom_ext_loc {X Y : Scheme.{0}} {f g : X ⟶ Y}
    (h : ∀ p : X, ∃ (W : Scheme.{0}) (a : W ⟶ X), IsOpenImmersion a ∧ p ∈ Set.range a ∧ a ≫ f = a ≫ g) : f = g := by
  choose W a ha hp hfg using h
  exact Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) X W a
    (fun x => by obtain ⟨y, hy⟩ := hp x; exact ⟨x, y, hy⟩) ha) f g hfg

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (x : X) : x ∈ Set.range a ↔ f x ∈ Set.range g := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨b p, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨q, hq₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨h.isoPullback.inv q, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hq₁]

theorem mul_left_pre {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (k : T'.left ⟶ T.left)
    (hk : k ≫ T.hom = T'.hom) (x y : T ⟶ G) (x' y' : T' ⟶ G) (hx : x'.left = k ≫ x.left)
    (hy : y'.left = k ≫ y.left) : (x' * y').left = k ≫ (x * y).left := by
  have ex : x' = Over.homMk k hk ≫ x := by ext; simp [hx]
  have ey : y' = Over.homMk k hk ≫ y := by ext; simp [hy]
  rw [ex, ey, ← MonObj.comp_mul, Over.comp_left]
  rfl

theorem isGrpPullback_id_of_loc {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left) [IsIso φ]
    (w : φ ≫ A'.hom = A.hom)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (B : Over W) (_ : GrpObj B) (a : B.left ⟶ A.left),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) :
    IsGrpPullback A A' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simpa using w⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  apply hom_ext_loc
  intro t
  obtain ⟨W, xS, B, _, a, hxo, ⟨w0, hw0⟩, hB, hB'⟩ := h (T.hom t)
  refine ⟨pullback T.hom xS, pullback.fst T.hom xS, inferInstance,
    (range_of_isPullback (IsPullback.of_hasPullback T.hom xS) t).2 ⟨w0, hw0⟩, ?_⟩
  let TW : Over W := Over.mk (pullback.snd T.hom xS)
  have cx : (pullback.fst T.hom xS ≫ x.left) ≫ A.hom = pullback.snd T.hom xS ≫ xS := by
    rw [Category.assoc, Over.w x, pullback.condition]
  have cy : (pullback.fst T.hom xS ≫ y.left) ≫ A.hom = pullback.snd T.hom xS ≫ xS := by
    rw [Category.assoc, Over.w y, pullback.condition]
  have cx' : (pullback.fst T.hom xS ≫ x.left ≫ φ) ≫ A'.hom = pullback.snd T.hom xS ≫ xS := by
    simpa [w] using cx
  have cy' : (pullback.fst T.hom xS ≫ y.left ≫ φ) ≫ A'.hom = pullback.snd T.hom xS ≫ xS := by
    simpa [w] using cy
  let XB : TW ⟶ B := Over.homMk (hB.1.lift _ _ cx) (hB.1.lift_snd _ _ cx)
  let YB : TW ⟶ B := Over.homMk (hB.1.lift _ _ cy) (hB.1.lift_snd _ _ cy)
  let x' : Over.mk (TW.hom ≫ xS) ⟶ A := Over.homMk (pullback.fst T.hom xS ≫ x.left) cx
  let y' : Over.mk (TW.hom ≫ xS) ⟶ A := Over.homMk (pullback.fst T.hom xS ≫ y.left) cy
  let x₁ : Over.mk (TW.hom ≫ xS) ⟶ A' := Over.homMk (pullback.fst T.hom xS ≫ x.left ≫ φ) cx'
  let y₁ : Over.mk (TW.hom ≫ xS) ⟶ A' := Over.homMk (pullback.fst T.hom xS ≫ y.left ≫ φ) cy'
  have e1 : (x' * y').left = (XB * YB).left ≫ a :=
    hB.2 TW XB YB x' y' (hB.1.lift_fst _ _ cx).symm (hB.1.lift_fst _ _ cy).symm
  have e2 : (x₁ * y₁).left = (XB * YB).left ≫ a ≫ φ := by
    refine hB'.2 TW XB YB x₁ y₁ ?_ ?_
    · simp only [x₁, XB, Over.homMk_left]
      rw [← Category.assoc (hB.1.lift _ _ cx), hB.1.lift_fst, Category.assoc]
    · simp only [y₁, YB, Over.homMk_left]
      rw [← Category.assoc (hB.1.lift _ _ cy), hB.1.lift_fst, Category.assoc]
  have hk : pullback.fst T.hom xS ≫ T.hom = (Over.mk (TW.hom ≫ xS)).hom := by
    simp [TW, pullback.condition]
  have hk' : pullback.fst T.hom xS ≫ (Over.mk (T.hom ≫ 𝟙 S)).hom = (Over.mk (TW.hom ≫ xS)).hom := by
    simp [TW, pullback.condition]
  have m1 := mul_left_pre (pullback.fst T.hom xS) hk x y x' y' rfl rfl
  have m2 := mul_left_pre (pullback.fst T.hom xS) hk' x₀ y₀ x₁ y₁
    (by simp only [x₁, Over.homMk_left, hx]) (by simp only [y₁, Over.homMk_left, hy])
  rw [← m2, e2, ← Category.assoc, ← e1, m1, Category.assoc]

theorem isGrpPullback_local_on_base : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left), IsIso φ → φ ≫ A'.hom = A.hom → (∀ p : S, ∃ (V : Scheme.{0}) (x : V ⟶ S) (B : Over V) (_ : GrpObj B) (a : B.left ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) → IsGrpPullback A A' (𝟙 S) φ := by
  intro S A A' _ _ φ hφ w h
  exact isGrpPullback_id_of_loc φ w h

end GlobalTheory.GrpLoc
end
end
