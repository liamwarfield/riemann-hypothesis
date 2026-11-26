module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftShearMapSquareZeroAbelianSchemes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTrait
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFiel
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorBirationalCompare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSections
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.CubeConst

section General

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem cubV_through (hG : GlobalFnsSt) (hA : IsAbelianScheme G') {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (gp : IsGrpPullback G' G f F) {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L')
    (w : LB.Iso L'.L (L.L.pull F)) (hw : w.IsGen) {T : Over S'} (z : T.left) {J J'} (hJ : Good L.L z J)
    (hJ' : Good L'.L z J') (x y u : T ⟶ G') :
    cubV c (T := Over.mk (T.hom ≫ f)) z J (pushHom gp T x) (pushHom gp T y) (pushHom gp T u) =
      GlobalTheory.ConstFam.wVal w z J J' (x * y * u).left * (GlobalTheory.ConstFam.wVal w z J J' (x * y).left)⁻¹ *
        (GlobalTheory.ConstFam.wVal w z J J' (x * u).left)⁻¹ * (GlobalTheory.ConstFam.wVal w z J J' (y * u).left)⁻¹ *
        GlobalTheory.ConstFam.wVal w z J J' x.left * GlobalTheory.ConstFam.wVal w z J J' y.left * GlobalTheory.ConstFam.wVal w z J J' u.left *
        (GlobalTheory.ConstFam.wVal w z J J' (1 : T ⟶ G').left)⁻¹ * cubV c' z J' x y u := by
  let Y : Over S' := G' ⊗ G' ⊗ G'
  let H : Over.mk (Y.hom ≫ f) ⟶ G ⊗ G ⊗ G :=
    lift (pushHom gp Y (x3 G' 0)) (lift (pushHom gp Y (x3 G' 1)) (pushHom gp Y (x3 G' 2)))
  have hψ : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ F = H.left ≫ thφ G (x3 G) I := fun I => by
    have e₁ := psum_hom (pushHom gp Y) (x3 G') I.down
    have e₂ := psum_hom (preHom H) (x3 G) I.down
    have e₃ : (fun i => pushHom gp Y (x3 G' i)) = fun i => preHom H (x3 G i) :=
      funext fun i => by fin_cases i <;> simp [preHom, x3, H]
    exact congrArg (fun q => q.left) (e₁.trans ((congrArg (fun q => psum G q I.down) e₃).trans e₂.symm))
  obtain ⟨a, ha, hv⟩ := GlobalTheory.ConstFam.exists_gen_through (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε)
    (h := H.left) hw L.isLB L'.isLB hψ c.t c.isGen
  have ev : ∀ {T : Over S'} (z : T.left) {J J'}, Good L.L z J → Good L'.L z J' → ∀ x y u : T ⟶ G',
      cubV c (T := Over.mk (T.hom ≫ f)) z J (pushHom gp T x) (pushHom gp T y) (pushHom gp T u) =
      GlobalTheory.ConstFam.wVal w z J J' (x * y * u).left * (GlobalTheory.ConstFam.wVal w z J J' (x * y).left)⁻¹ *
        (GlobalTheory.ConstFam.wVal w z J J' (x * u).left)⁻¹ * (GlobalTheory.ConstFam.wVal w z J J' (y * u).left)⁻¹ *
        GlobalTheory.ConstFam.wVal w z J J' x.left * GlobalTheory.ConstFam.wVal w z J J' y.left * GlobalTheory.ConstFam.wVal w z J J' u.left *
        (GlobalTheory.ConstFam.wVal w z J J' (1 : T ⟶ G').left)⁻¹ * val a (lift x (lift y u)).left z J' := by
    intro T z J J' hJ hJ' x y u
    have e := hv _ (lift x (lift y u)).left z J J' hJ hJ'
    refine Eq.trans ?_ (e.trans (congrArg (· * _) (prod_cub x y u (GlobalTheory.ConstFam.wVal w z J J'))))
    let R : Over.mk (T.hom ≫ f) ⟶ Over.mk (Y.hom ≫ f) := (Over.map f).map (lift x (lift y u))
    have p : ∀ q : Y ⟶ G', R ≫ pushHom gp Y q = pushHom gp T (lift x (lift y u) ≫ q) := fun q =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    have q : lift (pushHom gp T x) (lift (pushHom gp T y) (pushHom gp T u)) = R ≫ H := by
      simp only [H, comp_lift, p]
      simp [x3]
    exact congrArg (fun r => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t r z J) (congrArg (fun q => q.left) q)
  have sj : Function.Surjective (Y.hom).appTop.hom := by
    have := surj_comp (surj_snd hG hA (G' ⊗ G')) (surj_comp (surj_snd hG hA G') (hG _ _ hA).2)
    rwa [Over.w, Over.w] at this
  have key := gen_unique (φ := thφ G' (x3 G')) (ε := thε) L'.isLB Y.hom
    (lift (1 : 𝟙_ (Over S') ⟶ G') (lift (1 : 𝟙_ (Over S') ⟶ G') (1 : 𝟙_ (Over S') ⟶ G'))).left (Over.w _) sj ha c'.isGen
    (fun y I' hI' => by
      obtain ⟨I, hI⟩ := GlobalTheory.ConstFam.exists_good' L.isLB y
      have E := ev (T := 𝟙_ (Over S')) y hI hI' 1 1 1
      have C : IsCub (cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) y I) := isCub_cubV c hI
      rw [map_one, C.face] at E
      refine Eq.trans ?_ ((isCub_cubV (T := 𝟙_ (Over S')) c' hI').face 1 1).symm
      have fin : ∀ {A U : Type} [Group A] [CommGroup U] (h : A → U) (b : U), 1 = h (1 * 1 * 1) * (h (1 * 1))⁻¹ *
        (h (1 * 1))⁻¹ * (h (1 * 1))⁻¹ * h 1 * h 1 * h 1 * (h 1)⁻¹ * b → b = 1 := fun h b e => by
          simpa using e.symm
      exact fin (fun q : 𝟙_ (Over S') ⟶ G' => GlobalTheory.ConstFam.wVal w y I I' q.left) _ E) _
    (lift x (lift y u)).left z J' hJ'
  exact (ev z hJ hJ' x y u).trans (congrArg _ key)

theorem exists_cube_const {L : RigLB G} (c : CubicalStr G L) {T : Over S} {Γ' : Type} [AddCommGroup Γ']
    (pt : Γ' → (T ⟶ G)) (hadd : ∀ a b, pt (a + b) = pt a * pt b)
    (fr : ∀ a, LB.Gen (LB.LinComb L.L (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1))) (hfr : ∀ a, (fr a).IsGen) (a a' a'' : Γ') :
    ∃ k : Γ(T.left, ⊤), ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J →
      (cubV c z J (ρ ≫ pt a) (ρ ≫ pt a') (ρ ≫ pt a'') * ((val (fr (a + a')) ρ.left z J * val (fr (a + a'')) ρ.left z J *
        val (fr (a' + a'')) ρ.left z J * val (fr 0) ρ.left z J) * (val (fr (a + a' + a'')) ρ.left z J *
          val (fr a) ρ.left z J * val (fr a') ρ.left z J * val (fr a'') ρ.left z J)⁻¹)).val = gs ρ.left z ⊤ k := by
  have h0 : pt 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  have g4 := fun b₁ b₂ b₃ b₄ => mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (hfr b₁) (hfr b₂)) (hfr b₃)) (hfr b₄)
  obtain ⟨k, hk⟩ := H1.exists_const L.L L.isLB (𝟙 T.left) (fun b => ⟨b, rfl⟩) _
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen L.L (thφ G (x3 G)) thε c.t c.isGen
      (lift (pt a) (lift (pt a') (pt a''))).left)
      (mulGen_isGen _ _ _ _ _ _ _ (g4 (a + a') (a + a'') (a' + a'') 0)
        (invGen_isGen _ _ _ _ (g4 (a + a' + a'') a a' a'')))) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_cub (pt a) (pt a') (pt a'') h) rfl)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, hadd, h0, zpow_neg, zpow_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨k, fun T' ρ z J hJ => ?_⟩
  have e := hk _ ρ.left z J hJ
  rw [Category.comp_id] at e
  refine Eq.trans (congrArg Units.val ?_) e
  have v4 := fun b₁ b₂ b₃ b₄ => (val_mul hJ (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (fr b₁) (fr b₂)) (fr b₃)) (fr b₄)
    ρ.left).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans (congrArg (· * _) (val_mul hJ _ _ _))))
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c ρ hJ _ _ _) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (v4 _ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (v4 _ _ _ _))))))).symm

end General

section Torsion

open GlobalTheory.ThetaCompare

variable {S : Scheme.{0}}

theorem reg_cub {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) {y : T.left} {J}
    (hJ : Good L.L y J) (m₁ m₂ m₃ : T ⊗ A ⟶ A) :
    Reg L.L y J (fun _ _ h => h (m₁ * m₂ * m₃) * (h (m₁ * m₂))⁻¹ * (h (m₁ * m₃))⁻¹ * (h (m₂ * m₃))⁻¹ * h m₁ * h m₂ *
      h m₃ * (h 1)⁻¹) (fun z => cubV c y J (ptSecT A z ≫ m₁) (ptSecT A z ≫ m₂) (ptSecT A z ≫ m₃)) :=
  ⟨_, _, _, _, LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift m₁ (lift m₂ m₃)).left,
    pullGen_isGen _ _ _ _ c.isGen _, fun _ _ h => prod_cub m₁ m₂ m₃ h, fun a => val_cub c (ptSecT A a) hJ _ _ _⟩

theorem cube_torsFrame_pow (hG : GlobalFnsSt) (P : PolAV S) [IsCommMonObj P.A] {rig : LB.Gen (P.L.pull (eSec P.A))}
    {hrig : rig.IsGen} (c : CubicalStr P.A ⟨P.L, rig, P.isLB, hrig⟩) {T : Over S} {Γ' : Type} [AddCommGroup Γ']
    (pt : Γ' → (T ⟶ P.A)) (hadd : ∀ a b, pt (a + b) = pt a * pt b) {m : ℕ}
    (fr : ∀ a, LB.Gen (LB.LinComb P.L (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1)))
    (hfr : ∀ a, IsTorsFrame P rig m (pt a) (fr a)) (a a' a'' : Γ') (z : T.left) (J) (hJ : Good P.L z J) :
    (cubV c z J (pt a) (pt a') (pt a'') * ((val (fr (a + a')) (𝟙 _) z J * val (fr (a + a'')) (𝟙 _) z J *
        val (fr (a' + a'')) (𝟙 _) z J * val (fr 0) (𝟙 _) z J) * (val (fr (a + a' + a'')) (𝟙 _) z J *
          val (fr a) (𝟙 _) z J * val (fr a') (𝟙 _) z J * val (fr a'') (𝟙 _) z J)⁻¹)) ^ (m ^ 2) = 1 := by
  have h0 : pt 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P m T
  have rα := Reg.two (y := z) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  obtain ⟨p, hp, hp'⟩ : ∃ p : T ⊗ P.A ⟶ P.A, p ^ m = 1 ∧ ∀ w, ptSecT P.A w ≫ p = pt a :=
    ⟨fst T P.A ≫ pt a, by rw [← SymLiftOdd.comp_pow', (hfr a).1, MonObj.comp_one],
      fun w => by rw [ptSecT, lift_fst_assoc, Category.id_comp]⟩
  obtain ⟨q, hq, hq'⟩ : ∃ q : T ⊗ P.A ⟶ P.A, q ^ m = 1 ∧ ∀ w, ptSecT P.A w ≫ q = pt a' :=
    ⟨fst T P.A ≫ pt a', by rw [← SymLiftOdd.comp_pow', (hfr a').1, MonObj.comp_one],
      fun w => by rw [ptSecT, lift_fst_assoc, Category.id_comp]⟩
  have r := (((reg_cub c hJ p q (snd T P.A)).pow hJ (m ^ 2)).mul hJ
    (((((rα.pull hJ (p * q)).mul hJ (rα.pull hJ (p * snd T P.A))).mul hJ (rα.pull hJ (q * snd T P.A))).mul hJ
      (rα.pull hJ 1)).mul hJ ((((rα.pull hJ (p * q * snd T P.A)).mul hJ (rα.pull hJ p)).mul hJ (rα.pull hJ q)).mul hJ
        rα).inv)).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, mul_pow, hp, hq, one_pow, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (pt a'') 1
  simp only [MonObj.comp_mul, MonObj.comp_one, pt_snd, hp', hq', _root_.mul_one] at r
  have C : IsCub (cubV c (T := T) z J) := isCub_cubV c hJ
  rw [C.face₃] at r
  have t := fun b => congrArg Additive.ofMul (torsFrame_pow hG P hα (hfr b) hJ)
  have t₁ := t (a + a' + a'')
  have t₂ := t (a + a')
  have t₃ := t (a + a'')
  have t₄ := t (a' + a'')
  have t₅ := t a
  have t₆ := t a'
  have t₇ := t a''
  have t₈ := t 0
  simp only [← hadd] at r
  rw [← h0] at r
  generalize val α (ptSecT P.A 1).left z J = e at t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
  apply Additive.ofMul.injective
  replace r := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at r t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ ⊢
  linear_combination (norm := module) r + t₂ + t₃ + t₄ + t₈ - t₁ - t₅ - t₆ - t₇

end Torsion

theorem exists_frame_cube_const : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R, (∀ a a' a'', κ a a' a'' ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val := by
  intro g n F W Z i X₁ z₁ act
  have := X₁.ar.ded
  have : IsNoetherianRing X₁.S.R := isNoetherianRing_of_fg X₁.S.fg
  have : IsLocallyNoetherian (Sp X₁.S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.S.R)))
  have := X₁.ρ.P.isAb.comm
  obtain ⟨c₀⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp X₁.S.R) X₁.ρ.P ⟨X₁.ρ.P.L, X₁.ρ.rig, X₁.ρ.P.isLB, X₁.ρ.rig_gen⟩ rfl).1
  choose k hk using exists_cube_const c₀ X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.fr (fun a => (X₁.ρ.fr_tors a).2.1)
  refine ⟨fun a a' a'' => (Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''), fun a a' a'' => ?_, ?_⟩
  · rw [← map_pow]
    refine Eq.trans (congrArg _ (fn_ext (b := 1) fun y _ => ?_)) (map_one _)
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB y
    have e := hk a a' a'' _ (𝟙 _) y J hJ
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at e
    have e' := congrArg Units.val (cube_torsFrame_pow GlobalTheory.firstFiveLaws.1.globalFns X₁.ρ.P c₀ X₁.ρ.pt X₁.ρ.pt_add
      X₁.ρ.fr X₁.ρ.fr_tors a a' a'' y J hJ)
    have e'' := (congrArg (· ^ ((X₁.S.r * X₁.S.N) ^ 2)) e).symm.trans ((Units.val_pow_eq_pow_val _ _).symm.trans e')
    rw [gs_eq _ y ⊤ trivial, ← map_pow, ← map_pow] at e''
    rw [gs_eq _ y ⊤ trivial, gs_eq _ y ⊤ trivial, map_one, map_one]
    exact e''
  intro V _ _ _ ev X _ m t δ 𝔪 x fr hx hfr ρ hρ c a a' a'' z JA hJA
  have := 𝔪.A.isAb.comm
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB z
  let U : Over.mk ((TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk (spMap 𝔪.yK) (by
      show spMap 𝔪.yK ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp])
  have hp : ∀ b, pushHom 𝔪.cart (TFK (R := V) (FractionRing V)) (x b) = U ≫ X₁.ρ.pt b := fun b =>
    Over.OverMorphism.ext (hx b)
  have hadd : ∀ b b', x (b + b') = x b * x b' := fun b b' =>
    GlobalTheory.Poinc.PtAdd.x_add g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx b b' (x b') (hx b')
  have h0 : x 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  have e₁ := cubV_through GlobalTheory.firstFiveLaws.1.globalFns 𝔪.A.isAb 𝔪.cart c₀ c 𝔪.wl 𝔪.wl_gen
    (T := TFK (R := V) (FractionRing V)) z hJ hJA (x a) (x a') (x a'')
  rw [hp, hp, hp, ← hadd, ← hadd, ← hadd, ← hadd, ← h0] at e₁
  have e₂ := hk a a' a'' _ U z J hJ
  have e₃ : gs U.left z ⊤ (k a a' a'') = GlobalTheory.UT.cst (FractionRing V) z
      (𝔪.yK ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''))) := by
    refine Eq.trans ?_ (Geo.Tor.cst_comp (𝟙 _) 𝔪.yK z _)
    rw [Category.id_comp]
    exact congrArg (gs (spMap 𝔪.yK) z ⊤) ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom_inv_id_apply _).symm
  have alg : ∀ {R : Type} [CommRing R] {κ : R} {c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ : Rˣ},
      c₀ = w₁ * w₂⁻¹ * w₃⁻¹ * w₄⁻¹ * w₅ * w₆ * w₇ * w₈⁻¹ * c →
      (c₀ * ((g₂ * g₃ * g₄ * g₈) * (g₁ * g₅ * g₆ * g₇)⁻¹)).val = κ →
      w₁ * f₁ = g₁ → w₂ * f₂ = g₂ → w₃ * f₃ = g₃ → w₄ * f₄ = g₄ → w₅ * f₅ = g₅ → w₆ * f₆ = g₆ → w₇ * f₇ = g₇ →
      w₈ * f₈ = g₈ → (c * (f₂ * f₃ * f₄ * f₈)).val = κ * (f₁ * f₅ * f₆ * f₇).val := by
    rintro R _ κ c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
    rw [← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact alg e₁ (e₂.trans e₃) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA)

end GlobalTheory.Poinc.CubeConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_frame_cube_constant_root_of_unity : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R, (∀ a a' a'', κ a a' a'' ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val := by
  first | exact @GlobalTheory.Poinc.CubeConst.exists_frame_cube_const | exact GlobalTheory.Poinc.CubeConst.exists_frame_cube_const | (intros; apply GlobalTheory.Poinc.CubeConst.exists_frame_cube_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliMapDescendsGaloisCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliMapDescendsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.MapDesc

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def objMapCongr {S S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {f g : S' ⟶ S} (m : ObjMap o' o f) (h : f = g) : ObjMap o' o g := h ▸ m

end GlobalTheory.UPel.HT.MapDesc


open GlobalTheory.UPel.HT.MapDesc GlobalTheory.UPel.HT.MapComp in
theorem GlobalTheory.UPel.HT.MapDesc.nonempty_objMap_of_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
  (S S₁ Y : Scheme.{0}) (t : S ⟶ Sp R) (sY : Y ⟶ Sp R) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga]
  (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (o : Obj b N t) (o' : Obj b N (π₁ ≫ t)) (u : Obj b N sY),
  3 ≤ N → N.Coprime p → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → ObjMap o' o π₁ → ObjMap o' u (π₁ ≫ f) →
  Nonempty (ObjMap o u f) := by
  intro p _ D R _ b N S S₁ Y t sY π₁ Ga _ ρ₁ f o o' u hN hNp hG m₁ m₂
  let compose : ∀ {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
      {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃},
      ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → ObjMap o₁ o₃ (f ≫ g) := fun {_ _ _} {_ _ _} {o₁ o₂ o₃} {_ _} m₁ m₂ =>
    { φ := m₁.φ ≫ m₂.φ
      φ₂ := m₁.φ₂ ≫ m₂.φ₂
      cart := m₁.cart.comp m₂.cart
      sq := MapComp.isSquare_comp m₁.sq m₂.sq
      act := fun c => by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
      pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol (MapComp.lbIso_pull_comp m₂.pol m₁.φ₂ rfl)
      eta := fun y => by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc] }
  have uniq : ∀ {T T' : Scheme.{0}} {sT : T ⟶ Sp R} {sT' : T' ⟶ Sp R} {x : Obj b N sT} {y : Obj b N sT'}
      {g g' : T ⟶ T'} (_ : g = g') (n : ObjMap x y g) (n' : ObjMap x y g'), n.φ = n'.φ := by
    rintro T T' sT sT' x y g g' rfl n n'
    exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique p D R b N hN hNp T' T sT' sT x y g n n'
  have hw : ∀ a, m₁.φ ≫ o.A.hom = (o'.A.hom ≫ ρ₁ a) ≫ π₁ := fun a => by
    rw [Category.assoc, hG.inv a]; exact m₁.cart.1.w
  let σ : Ga → (o'.A.left ⟶ o'.A.left) := fun a => m₁.cart.1.lift m₁.φ (o'.A.hom ≫ ρ₁ a) (hw a)
  have hσ₁ : ∀ a, σ a ≫ m₁.φ = m₁.φ := fun a => m₁.cart.1.lift_fst _ _ _
  have hσ₂ : ∀ a, σ a ≫ o'.A.hom = o'.A.hom ≫ ρ₁ a := fun a => m₁.cart.1.lift_snd _ _ _
  have hG' : GlobalTheory.ZM.IsGaloisCover Ga σ m₁.φ := hG.of_isPullback m₁.cart.1.flip hσ₂ hσ₁
  have hinv : ∀ a, σ a ≫ m₂.φ = m₂.φ := fun a => by
    obtain ⟨n⟩ := MapComp.cancel (f := ρ₁ a) (g := π₁) (objMapCongr m₁ (hG.inv a).symm) m₁
    have hn₁ : n.φ ≫ m₁.φ = m₁.φ := uniq (hG.inv a) (compose n m₁) m₁
    have hn₂ : n.φ ≫ o'.A.hom = o'.A.hom ≫ ρ₁ a := n.cart.1.w
    have hnσ : n.φ = σ a := m₁.cart.1.hom_ext (by rw [hn₁, hσ₁]) (by rw [hn₂, hσ₂])
    rw [← hnσ]
    exact uniq (show ρ₁ a ≫ (π₁ ≫ f) = π₁ ≫ f by rw [← Category.assoc, hG.inv a]) (compose n m₂) m₂
  obtain ⟨φ, hφ, -⟩ := hG'.existsUnique_desc m₂.φ hinv
  have : Epi m₁.φ := by
    have := hG'.etale; have := hG'.onto
    exact Flat.epi_of_flat_of_surjective _
  have : Epi π₁ := by
    have := hG.etale; have := hG.onto
    exact Flat.epi_of_flat_of_surjective _
  have cart : IsGrpPullback o.A u.A f φ :=
    GlobalTheory.T.isGrpPullback_descent_along_galoisCover S S₁ Y π₁ Ga ρ₁ f o'.A o.A u.A m₁.φ m₂.φ φ hG m₁.cart m₂.cart hφ
  obtain ⟨φ₂, sq⟩ := MapComp.exists_isSquare cart.1.w
  have sq₂ : IsSquare m₂.φ (m₁.φ₂ ≫ φ₂) := by rw [← hφ]; exact MapComp.isSquare_comp m₁.sq sq
  have e₂ : m₂.φ₂ = m₁.φ₂ ≫ φ₂ := MapComp.isSquare_unique m₂.sq sq₂
  have hA₂ : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ o.ab o.ab
  have := hA₂.comm
  obtain ⟨r, hr⟩ : GlobalTheory.AbLaw.Triv (o.P.pull (eSec (G2 o.A))) :=
    GlobalTheory.AbLaw.CubeOpen.triv_comp (eSec o.A) (GlobalTheory.SquareDescent.eSec_lift_one o.A) o.rig₁
  obtain ⟨r', hr'⟩ : GlobalTheory.AbLaw.Triv (u.P.pull (eSec (G2 u.A))) :=
    GlobalTheory.AbLaw.CubeOpen.triv_comp (eSec u.A) (GlobalTheory.SquareDescent.eSec_lift_one u.A) u.rig₁
  let PA : RigLB (G2 o.A) := ⟨o.P, r, o.isLB, hr⟩
  let PB : RigLB (G2 u.A) := ⟨u.P, r', u.isLB, hr'⟩
  have c₁ : IsGrpPullback (G2 o'.A) (G2 o.A) π₁ m₁.φ₂ :=
    GlobalTheory.ShearLift.isGrpPullback_tensor m₁.cart m₁.cart m₁.sq.1 m₁.sq.2
  have c₂ : IsGrpPullback (G2 o.A) (G2 u.A) f φ₂ := GlobalTheory.ShearLift.isGrpPullback_tensor cart cart sq.1 sq.2
  have pol₂ : LBIso o'.P (u.P.pull (m₁.φ₂ ≫ φ₂)) := by rw [← e₂]; exact m₂.pol
  have pol : LBIso o.P (u.P.pull φ₂) :=
    GlobalTheory.T.rigidLineBundleIso_descent_along_galoisCover S S₁ Y π₁ Ga ρ₁ f (G2 o'.A) (G2 o.A) (G2 u.A) m₁.φ₂ φ₂ PA PB o'.P hA₂ hG c₁ c₂ o'.isLB m₁.pol pol₂
  refine ⟨{ φ := φ, φ₂ := φ₂, cart := cart, sq := sq, act := fun c => ?_, pol := pol, eta := fun y => ?_ }⟩
  · rw [← cancel_epi m₁.φ, ← Category.assoc, ← m₁.act c, Category.assoc, hφ, m₂.act c, ← hφ, Category.assoc]
  · rw [← cancel_epi π₁, ← Category.assoc, ← m₁.eta y, Category.assoc, hφ, m₂.eta y, Category.assoc]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliMapDescendsGaloisCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_moduliMap_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
  (S S₁ Y : Scheme.{0}) (t : S ⟶ Sp R) (sY : Y ⟶ Sp R) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga]
  (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (o : Obj b N t) (o' : Obj b N (π₁ ≫ t)) (u : Obj b N sY),
  3 ≤ N → N.Coprime p → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → ObjMap o' o π₁ → ObjMap o' u (π₁ ≫ f) →
  Nonempty (ObjMap o u f) := by
  first | (exact @GlobalTheory.UPel.HT.MapDesc.nonempty_objMap_of_galoisCover) | (exact GlobalTheory.UPel.HT.MapDesc.nonempty_objMap_of_galoisCover) | (intros; apply GlobalTheory.UPel.HT.MapDesc.nonempty_objMap_of_galoisCover  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreThetaConstantsAlgebraicOverCompleteAlgClose
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreThetaConstantsAlgebraicOverCompleteAlgClose
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FibreTheta

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport GlobalTheory.ValuesPullIso GlobalTheory.LabTrans

theorem isThetaPt_of_homMk {S X : Scheme.{0}} {P : PolAV S} {k : ℕ} {h₁ h₂ : X ⟶ S} (e : h₁ = h₂) {I : Type}
    (x : I → (Over.mk h₁ ⟶ P.A)) {v : I → Γ(X, ⊤)}
    (H : IsThetaPt P k (fun i => (Over.homMk (x i).left ((Over.w (x i)).trans e) : Over.mk h₂ ⟶ P.A)) v) :
    IsThetaPt P k x v := by
  subst e
  exact H

theorem pow_homMk {S X : Scheme.{0}} {A : Over S} [GrpObj A] {h₁ h₂ : X ⟶ S} (e : h₁ = h₂) (x : Over.mk h₁ ⟶ A)
    {k : ℕ} (hx : x ^ k = 1) : (Over.homMk x.left ((Over.w x).trans e) : Over.mk h₂ ⟶ A) ^ k = 1 := by
  subst e
  exact hx

theorem theta_consts_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (n : ℕ), n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → ∀ (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → ∀ (B : PolAV (Sp (Kb W))) (b : B.A.left ⟶ A'.A.left), IsGrpPullback B.A A'.A (spMap (algebraMap (FractionRing W) (Kb W))) b → LBIso B.L (A'.L.pull b) → ∀ j : ℕ, 1 ≤ j → ∃ (C : Type) (_ : Field C) (jC : Kb W →+* C) (Ix : Type) (x : Ix → (baseOver (Sp (Kb W)) ⟶ B.A)) (v : Ix → Kb R), (∀ z : baseOver (Sp (Kb W)) ⟶ B.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧ (∀ i, x i ^ ((n ^ j) ^ 2) = 1) ∧ IsThetaPt B (n ^ j) (fun i => (Over.homMk (spMap jC) (Category.comp_id _) : Over.mk (spMap jC) ⟶ baseOver (Sp (Kb W))) ≫ x i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (jC (e₀ (v i)))) := by
  intro R _ _ _ hR D n _ ho hnR W _ _ _ hW φ iφ lφ D' G' _ _ A' hD hG hU e₀ he₀ B b hb hLB j _
  obtain ⟨hD⟩ := hD
  obtain ⟨U'⟩ := hU
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  haveI := lφ
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have b₀ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hm : Odd (n ^ j) := ho.pow
  have hmR : IsUnit (((n ^ j : ℕ)) : R) := by rw [Nat.cast_pow]; exact hnR.pow j
  have hk : 1 ≤ (n ^ j) ^ 2 := pow_pos hm.pos 2
  generalize n ^ j = m at *
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := exists_complete_isAlgClosed_cExt W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((gam.comp e₀).comp (algebraMap (FractionRing R) (Kb R))).toAlgebra
  let em : Kb R →ₐ[FractionRing R] C := { toRingHom := gam.comp e₀, commutes' := fun _ => rfl }
  have cC : Compat φ C := fun r => (congrArg gam (he₀ r)).trans (hgam _)
  have hCR : CExt R (maximalIdeal R) C :=
    ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
  obtain ⟨N', ν', -⟩ := ValuesExist.exists_integral_values hL W D'.toPre D'.psi_even hB' C ⊤ fun _ => trivial
  obtain ⟨J, hJX, hJ⟩ := OneTraitTheta.exists_values_iso hL hD cC ν ν'
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause W _ b₀ D' A' G' hG U' C (m ^ 2) hk
  let f₀ := spMap (algebraMap (FractionRing W) (Kb W))
  let T : Over (Sp (Kb W)) := Over.mk (spMap gam)
  let ιC : T ⟶ baseOver (Sp (Kb W)) := Over.homMk (spMap gam) (Category.comp_id _)
  obtain ⟨e, he⟩ : ∃ e : (T ⟶ B.A) ≃* (Over.mk (T.hom ≫ f₀) ⟶ A'.A), ∀ y, (e y).left = y.left ≫ b :=
    LiePull.exists_pushEquiv hb T _ rfl
  have heq : spMap gam ≫ f₀ = jFK (R := W) C := by
    rw [← Geo.Tor.spMap_comp]
    exact congrArg spMap (RingHom.ext hgam)
  let Ix := {z : baseOver (Sp (Kb W)) ⟶ B.A // z ^ (m ^ 2) = 1}
  have tz : ∀ i : Ix, (ιC ≫ i.1) ^ (m ^ 2) = 1 := fun i => by rw [← MonObj.comp_pow, i.2, MonObj.comp_one]
  let x₀ : Ix → (Over.mk (T.hom ≫ f₀) ⟶ A'.A) := fun i => e (ιC ≫ i.1)
  have tx₀ : ∀ i, x₀ i ^ (m ^ 2) = 1 := fun i => by
    show e (ιC ≫ i.1) ^ (m ^ 2) = 1
    rw [← map_pow, tz, map_one]
  let x' : Ix → (TFK (R := W) C ⟶ A'.A) := fun i => Over.homMk (x₀ i).left ((Over.w (x₀ i)).trans heq)
  have hx' : ∀ i, x' i ^ (m ^ 2) = 1 := fun i => pow_homMk heq _ (tx₀ i)
  choose p' hp' using fun i => hf.2.1 (x' i) (hx' i)
  choose p₁ e₂ using fun i => qkPullExists hGF R W φ D.toPre D'.toPre hD C cC (m ^ 2) (p' i)
  have hQ := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre C em (m ^ 2) hk
  choose p hp using fun i => (hQ.2 (p₁ i)).exists
  have hGt := GlobalTheory.T.torus_torsion_points_correspond_values
  choose q hq using fun i => (((hGt R D.toPre D.psi_even hB C N ν).2.2.2.2 _).1 (p₁ i)).exists
  choose q' hq' using fun i => (((hGt W D'.toPre D'.psi_even hB' C N' ν').2.2.2.2 _).1 (p' i)).exists
  obtain ⟨v, hv⟩ := GlobalTheory.T.degenerationThetaSeries_algebraic_over_fractionField R hR D m hm hmR Ix p
  obtain ⟨s, hs⟩ := hv C hCR em N ν p₁ q hp hq
  have e₅ : ∀ i, QkToAkU U'.toUnifPre C (m ^ 2) (p' i) (x' i) := fun i => (hf.1 _ _).2 (hp' i).symm
  have Q := GlobalTheory.T.theta_constants_eq_degeneration_series hV hGt (GlobalTheory.T.families_values_correspond hL hL₂) W _ hW rfl D' A' G' hG U' C hC N' ν' m hm _ p' q' x' e₅ hq'
  have hval : ∀ i, em (v i) = ((s * J.lam : Cˣ) : C) * N'.tx m (q' i) := fun i => by
    have e := (RelabelCoords.series_iso J hm (p := q' i) (p' := q i) (ν.eX.injective (by
      rw [hJX, (hq i).1, (hq' i).1, (e₂ i).1, AddEquiv.apply_symm_apply])) (hJ _ _ _ _ (hq i).2 (hq' i).2 (e₂ i).2)).1
    rw [e, Units.val_mul, _root_.mul_assoc, Units.mul_inv_cancel_left]
    exact hs i
  have Q₁ : IsThetaPt A' m x' (fun i => fnOf (em (v i))) :=
    GenericObject.isThetaPt_unit_mul A' m x' _ _ (fnOf ((s * J.lam : Cˣ) : C))
      ((Units.isUnit (s * J.lam)).map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
      (fun i => by rw [hval i]; exact map_mul _ _ _) Q
  have Q₂ : IsThetaPt A' m x₀ (fun i => fnOf (em (v i))) := isThetaPt_of_homMk heq x₀ Q₁
  have Q₃ := (ThetaPtUp.isThetaPt_iff hb hLB (x := fun i : Ix => ιC ≫ i.1) (x₀ := x₀) (fun i => he _) tz _).2 Q₂
  exact ⟨C, inferInstance, gam, Ix, Subtype.val, v, fun z hz => ⟨⟨z, hz⟩, rfl⟩, fun i => i.2, Q₃⟩

end GlobalTheory.Mum.FibreTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreThetaConstantsAlgebraicOverCompleteAlgCloseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_thetaConstants_algebraic_over_completeAlgClosed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (n : ℕ), n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → ∀ (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → ∀ (B : PolAV (Sp (Kb W))) (b : B.A.left ⟶ A'.A.left), IsGrpPullback B.A A'.A (spMap (algebraMap (FractionRing W) (Kb W))) b → LBIso B.L (A'.L.pull b) → ∀ j : ℕ, 1 ≤ j → ∃ (C : Type) (_ : Field C) (jC : Kb W →+* C) (Ix : Type) (x : Ix → (baseOver (Sp (Kb W)) ⟶ B.A)) (v : Ix → Kb R), (∀ z : baseOver (Sp (Kb W)) ⟶ B.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧ (∀ i, x i ^ ((n ^ j) ^ 2) = 1) ∧ IsThetaPt B (n ^ j) (fun i => (Over.homMk (spMap jC) (Category.comp_id _) : Over.mk (spMap jC) ⟶ baseOver (Sp (Kb W))) ≫ x i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (jC (e₀ (v i)))) := by
  first | exact @GlobalTheory.Mum.FibreTheta.theta_consts_algebraic | exact GlobalTheory.Mum.FibreTheta.theta_consts_algebraic | (intros; apply GlobalTheory.Mum.FibreTheta.theta_consts_algebraic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyEqFormOrderSubWeightedCoordOrders
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyEqFormOrderSubWeightedCoordOrders
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.ord_zpow_int {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (f : X.functionFieldˣ) (r : ℤ) : E.ord (f ^ r) = r * E.ord f := by
  obtain ⟨m, rfl | rfl⟩ := r.eq_nat_or_neg
  · rw [zpow_natCast, E.ord_pow]
  · rw [zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]; ring

theorem DivOver.ord_finsetProd_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {ι : Type} (s : Finset ι) (f : ι → X.functionFieldˣ)
    (e : ι → ℤ) : E.ord (∏ j ∈ s, f j ^ e j) = ∑ j ∈ s, e j * E.ord (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, E.ord_mul, ih, E.ord_zpow_int]

theorem DivOver.ord_eq_zero_of_unitAt_through {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {y : X} (hE : E.Through y) (v : X.functionFieldˣ)
    (h : UnitAt y (v : X.functionField)) : E.ord v = 0 := by
  obtain ⟨a, ha, e⟩ := h
  have h1 : (v : X.functionField) ∈ E.ring := hE _ ⟨a, e⟩
  have h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring := by
    refine hE _ ⟨(ha.unit⁻¹ : (X.presheaf.stalk y)ˣ), ?_⟩
    rw [Units.val_inv_eq_inv_val, ← e]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  have a1 := (E.ord_nonneg_iff v).2 h1
  have a2 := (E.ord_nonneg_iff v⁻¹).2 h2
  rw [E.ord_inv] at a2
  omega

end GlobalTheory.Discrepancy

namespace GlobalTheory.Discrepancy

theorem IsSncChart.discrep_eq_formOrd_sub_sum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (g : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → (Θ + m • K).IsEqn y g → ∀ E : DivOver q, E.Through y → discrep E η m g = ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * E.ord (u j) := by
  intro Y _ _ q n _ B y U hy z J w u hc η K Θ m g hη hK hm hΘ hg E hE
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  set ω := formOf U (gen_mem hy) (dOn q z) with hω
  have hgen := isFreeGen_formOf (gen_mem hy) hc.frame
  have h0 : ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [← hω, h]))
  obtain ⟨c, hcη⟩ := hgen.2 η
  have hc0 : c ≠ 0 := fun h => hη (by rw [← hcη]; simp [h])
  set k0 : Y.functionFieldˣ := Units.mk0 c hc0 with hk0
  have hηk : η = (k0 : Y.functionField) • ω := by rw [hk0, Units.val_mk0]; exact hcη.symm
  have hKy : K.IsEqn y k0 := hK U (dOn q z) hc.frame y hy k0 hηk
  have hΘy := GlobalTheory.T.snc_chart_divisor_equation ℂ Y q n B y U hy z J w u hc Θ hΘ
  set M : Y.functionFieldˣ := ∏ j ∈ J, u j ^ Θ.mult (w j) with hM
  have hsum : (Θ + m • K).IsEqn y (M * k0 ^ m) := hΘy.add (hKy.nsmul m)
  set v : Y.functionFieldˣ := g * (M * k0 ^ m)⁻¹ with hv
  have hvu : UnitAt y (v : Y.functionField) := by
    have := hsum.iff_unitAt.1 hg
    rwa [hv, Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
  have hv0 : E.ord v = 0 := E.ord_eq_zero_of_unitAt_through hE v hvu
  have hvo : E.ord v = E.ord g - (E.ord M + m * E.ord k0) := by
    rw [hv, E.ord_mul, E.ord_inv, E.ord_mul, E.ord_pow]; ring
  have hMo : E.ord M = ∑ j ∈ J, Θ.mult (w j) * E.ord (u j) := by
    rw [hM, E.ord_finsetProd_zpow]
  have hordg : E.ord g = ∑ j ∈ J, Θ.mult (w j) * E.ord (u j) + m * E.ord k0 := by
    rw [← hMo]; omega
  have hform : E.formOrd η = E.ord k0 + E.formOrd ω := by
    rw [hηk]; exact E.formOrd_smul hn h0 k0
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, hform, hordg]
  push_cast
  have hs : ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * (E.ord (u j) : ℚ) =
      (∑ j ∈ J, (Θ.mult (w j) : ℚ) * E.ord (u j)) / m := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => div_mul_eq_mul_div _ _ _
  rw [hs]
  unfold DivOver.formOrd
  field_simp
  ring

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyEqFormOrderSubWeightedCoordOrdersStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrepancy_eq_formOrder_sub_weighted_coordOrders : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (g : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → (Θ + m • K).IsEqn y g → ∀ E : DivOver q, E.Through y → discrep E η m g = ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * E.ord (u j) := by
  first | exact @GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum | exact GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum | (intros; apply GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopChernDensityHolomorphicChartEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffCurvatureCompHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffCurvatureCompHolomorphic
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexConjugate

namespace GlobalTheory.GoodTop

theorem isSesq_eq_sum_coordVec {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {α : V n → V n → M}
    (hα : IsSesq α) (x y : V n) :
    α x y = ∑ c, ∑ d, (x c * conj (y d)) • α (coordVec c) (coordVec d) := by
  have hex : ∀ w : V n, w = ∑ a, w a • coordVec a := by
    intro w
    ext i
    simp [coordVec, Pi.single_apply]
  have hl : ∀ (s : Finset (Fin n)) (c : Fin n → ℂ) (x : Fin n → V n) (y : V n),
      α (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i • α (x i) y := by
    intro s c x y
    induction s using Finset.induction_on with
    | empty =>
      have := hα.smul_left 0 0 y
      simpa using this
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_left, hα.smul_left, ih]
  have hr : ∀ (s : Finset (Fin n)) (c : Fin n → ℂ) (x : V n) (y : Fin n → V n),
      α x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, conj (c i) • α x (y i) := by
    intro s c x y
    induction s using Finset.induction_on with
    | empty =>
      have := hα.smul_right 0 x 0
      simpa using this
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_right, hα.smul_right, ih]
  calc α x y = α (∑ a, x a • coordVec a) (∑ b, y b • coordVec b) := by rw [← hex x, ← hex y]
    _ = _ := by
      rw [hl]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hr, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul]

theorem det_of_apply_coordVec {n : ℕ} (L : V n →L[ℂ] V n) :
    (Matrix.of fun c a => L (coordVec a) c).det = L.det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  congr 1

theorem mixTop_curvAt_comp_holo : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → MContDiffAt 2 G (φ w) → IsUnit (G (φ w)).det → mixTop (fun _ => curvAt (fun x => G (φ x)) w) = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * mixTop fun _ => curvAt G (φ w) := by
  intro n r _ _ G φ w hφ hG hu
  set J : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => fderiv ℂ φ w (coordVec a) c with hJ
  have h := GlobalTheory.T.polarisedTopChernCoeff_linear_substitution (fun _ : Fin n => curvAt G (φ w)) J (J.map conj)
  have e : (fun _ : Fin n => curvAt (fun x => G (φ x)) w) =
      fun (_ : Fin n) a b => ∑ c, ∑ d, (J c a * (J.map conj) d b) • curvAt G (φ w) c d := by
    funext _ a b
    rw [curvAt, curv_comp_holo hG hu hφ, isSesq_eq_sum_coordVec (isSesq_curv hG hu)]
    rfl
  have hc : (J.map conj).det = conj J.det := by
    rw [RingHom.map_det]; rfl
  rw [e, h, hc, hJ, det_of_apply_coordVec, Complex.mul_conj, Complex.normSq_eq_norm_sq]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffCurvatureCompHolomorphicStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_curvature_comp_holomorphic : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → MContDiffAt 2 G (φ w) → IsUnit (G (φ w)).det → mixTop (fun _ => curvAt (fun x => G (φ x)) w) = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * mixTop fun _ => curvAt G (φ w) := by
  first | exact @GlobalTheory.GoodTop.mixTop_curvAt_comp_holo | exact GlobalTheory.GoodTop.mixTop_curvAt_comp_holo | (intros; apply GlobalTheory.GoodTop.mixTop_curvAt_comp_holo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopChernDensityHolomorphicChartEtale
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem topDens_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ (c : AlgChart X.str σ X.dim) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → y ∈ c.e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → (Real.pi ^ X.dim)⁻¹ * (mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) (e y)).re = ‖transDet e c.e y‖ ^ 2 * topDens E H c y := by
  intro F _ σ X m E O H hM e he c y hy hye hyc A hA
  set G : V X.dim → Matrix (Fin m) (Fin m) ℂ := fun u => H A (c.e.symm u) () with hG
  set φ : V X.dim → V X.dim := c.e ∘ e.symm with hφ
  have ho := isOpen_over e c.e.open_source
  have hm := mem_over e hye hyc
  have hdiff : DifferentiableOn ℂ φ (e.target ∩ e.symm ⁻¹' c.e.source) := holoChart_trans_algChart he c
  have han : AnalyticAt ℂ φ (e y) := GlobalTheory.InjHol.analyticAt_of_differentiableOn_euclidean ho hm hdiff
  have hφy : φ (e y) = c.e y := by simp only [hφ, Function.comp_apply, e.left_inv hye]
  have hG2 : MContDiffAt 2 G (φ (e y)) := hφy ▸ hM.mContDiffAt_chart hy c hyc hA ()
  have hGu : IsUnit (G (φ (e y))).det := hφy ▸ hM.isUnit_det_chart hy c hyc hA ()
  have hger : (fun v => H A (e.symm v) ()) =ᶠ[𝓝 (e y)] fun v => G (φ v) := by
    filter_upwards [ho.mem_nhds hm] with w hw
    simp only [hG, hφ, Function.comp_apply, c.e.left_inv hw.2]
  have hcurv : curvAt (fun v => H A (e.symm v) ()) (e y) = curvAt (fun v => G (φ v)) (e y) := by
    funext a b
    exact curv_congr hger _ _
  have key := GlobalTheory.T.polarisedTopChernCoeff_curvature_comp_holomorphic (G := G) (φ := φ) (w := e y) (han.contDiffAt) hG2 hGu
  rw [hcurv, key, hφy]
  have hfr : topDens E H c y = chernTop (MvPolynomial.X ((), X.dim)) (fun v => H A (c.e.symm v)) (c.e y) :=
    hM.chernTop_frame _ hy c hyc (E.nonempty (under y)).choose_spec hA
  rw [hfr, GlobalTheory.T.chernTopDensity_eq_polarisedTopChern, transDet, Complex.re_ofReal_mul]
  ring

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopChernDensityHolomorphicChartEtaleStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_chern_density_holomorphic_chart_etale : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ (c : AlgChart X.str σ X.dim) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → y ∈ c.e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → (Real.pi ^ X.dim)⁻¹ * (mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) (e y)).re = ‖transDet e c.e y‖ ^ 2 * topDens E H c y := by
  first | exact @GlobalTheory.GoodTop.topDens_holoChart | exact GlobalTheory.GoodTop.topDens_holoChart | (intros; apply GlobalTheory.GoodTop.topDens_holoChart <;> assumption)
end
end
