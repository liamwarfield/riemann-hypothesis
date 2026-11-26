module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.JKAppTopInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordAdditive
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalAdd
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauBalAdd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)

theorem val₂_one (f g : A ⟶ A) (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε))
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L))
    {y : (𝟙_ (Over S)).left} {J} (hJ : Good Lr.L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by
  have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ h₀ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at this
  rw [val₂, e]; exact this

omit [IsCommMonObj A] in
theorem val_pull₂ (f g : A ⟶ A) (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good Lr.L z J) (a b : T ⟶ A) :
    val (LB.pullGen Lr.L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl

theorem ros_sum (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g f' g' : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L))
    (u' : LB.Gen (LB.LinComb Lr.L (rosatiφ A f' g') rosatiε)) (hu' : u'.IsGen)
    (h₀' : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u' (zero2 A)) (LB.oneGen Lr.L))
    (w : LB.Gen (LB.LinComb Lr.L (rosatiφ A (f * f') (g * g')) rosatiε)) (hw : w.IsGen)
    (w₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ w (zero2 A)) (LB.oneGen Lr.L))
    {T : Over S} {z : T.left} {J} (hJ : Good Lr.L z J) (x y : T ⟶ A) :
    val₂ w z J x y * cubV c z J x (y ≫ g) (y ≫ g') =
      cubV c z J (x ≫ f) (x ≫ f') y * (val₂ u z J x y * val₂ u' z J x y) := by
  let p : A ⊗ A ⟶ A := fst A A
  let q : A ⊗ A ⟶ A := snd A A
  let e : 𝟙_ (Over S) ⟶ A ⊗ A := lift 1 1
  have e₀ : e ≫ p = 1 := lift_fst _ _
  have e₁ : e ≫ q = 1 := lift_snd _ _
  have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (hG _ _ hA).2
  have he : e.left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  have ev : ∀ {T' : Over S} (σ : T' ⟶ A ⊗ A) {z : T'.left} {J}, Good Lr.L z J →
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ w (lift p q).left)
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift p (lift (q ≫ g) (q ≫ g'))).left)) σ.left z J =
        val₂ w z J (σ ≫ p) (σ ≫ q) * cubV c z J (σ ≫ p) (σ ≫ q ≫ g) (σ ≫ q ≫ g') ∧
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (p ≫ f) (lift (p ≫ f') q)).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift p q).left) (LB.pullGen Lr.L _ _ u' (lift p q).left)))
        σ.left z J = cubV c z J (σ ≫ p ≫ f) (σ ≫ p ≫ f') (σ ≫ q) *
          (val₂ u z J (σ ≫ p) (σ ≫ q) * val₂ u' z J (σ ≫ p) (σ ≫ q)) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ _ _ w σ hJ _ _) (val_cub c σ hJ _ _ _)),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ _ _ u σ hJ _ _) (val_pull₂ _ _ u' σ hJ _ _))))⟩
  have key := (ev (lift x y) hJ).1.symm.trans (Eq.trans (gen_unique' Lr.isLB (fun V _ k => by
      refine (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := V) _ (prod_cub (p ≫ f) (p ≫ f') q k)
        (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _ (prod_ros f g p q k) (prod_ros f' g' p q k))).trans
        (Eq.trans ?_ (prod_sum₂ (K := Fin 6) (K' := thK) (U := V) _ (prod_ros (f * f') (g * g') p q k)
          (prod_cub p (q ≫ g) (q ≫ g') k)).symm)
      rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc p]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) _ e.left he sj
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hw _) (pullGen_isGen _ _ _ _ c.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _) (mulGen_isGen _ _ _ _ _ _ _
        (pullGen_isGen _ _ _ _ hu _) (pullGen_isGen _ _ _ _ hu' _))) (fun y I hI => by
      have C : IsCub (cubV c y I) := isCub_cubV c hI
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁, val₂_one _ _ w w₀ hI, val₂_one _ _ u h₀ hI, val₂_one _ _ u' h₀' hI, C.face, C.face₃]
      simp) _ (lift x y).left z J hJ) (ev (lift x y) hJ).2)
  have r₀ : lift x y ≫ p = x := lift_fst _ _
  have r₁ : lift x y ≫ q = y := lift_snd _ _
  simp only [← Category.assoc, r₀, r₁] at key
  exact key

end GlobalTheory.TauBalAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionTranslateTorus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ShiftExp

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem gs_scal {Y Z : Scheme.{0}} {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem shift (hG : GlobalFnsSt) (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]
    (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G) (hx : U.TorPt a x) (e : ℕ) (Z : Scheme.{0})
    (y y' : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (TA R W ⊗ G).left)
    (h₁ : rG ≫ (snd _ G).left = y ≫ (fstG I e G).left)
    (h₂ : y' ≫ (fstG I e G).left = rG ≫ (translPt G x).left) :
    y' ≫ (U.gt e).pG.left = y ≫ (U.gt e).pG.left ∧ ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J →
      (val ((U.gt e).t χ) y' z J).val =
        gs (𝟙 Z) z ⊤ (scal (R := W) (rG ≫ (fst (TA R W) G).left) (a (Multiplicative.ofAdd χ)).val) *
          (val ((U.gt e).t χ) y z J).val := by
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let yo : T ⟶ thickObj R I e G := Over.homMk y rfl
  have hb : rG ≫ (TA R W ⊗ G).hom = T.hom ≫ thick R I e := by
    rw [← Over.w (snd (TA R W) G), ← Category.assoc, h₁, Category.assoc, Over.w (fstG I e G)]
    exact (Category.assoc _ _ _).symm
  let ro : Over.mk (T.hom ≫ thick R I e) ⟶ TA R W ⊗ G := Over.homMk rG hb
  let x₀ : Over.mk (T.hom ≫ thick R I e) ⟶ G := ro ≫ fst _ _ ≫ x
  let xe : T ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift x₀.left T.hom (Over.w x₀)) (pullback.lift_snd _ _ _)
  have hxe : xe.left ≫ pullback.fst G.hom (thick R I e) = x₀.left := pullback.lift_fst _ _ _
  have hm := (isGrpPullback_pullback G (thick R I e)).2 T xe yo x₀ (ro ≫ snd _ _) hxe.symm h₁
  have ht : ro ≫ translPt G x = x₀ * (ro ≫ snd _ _) := MonObj.comp_mul ro (fst _ _ ≫ x) (snd _ _)
  have hf : y' ≫ pullback.fst G.hom (thick R I e) = (xe * yo).left ≫ pullback.fst G.hom (thick R I e) :=
    h₂.trans ((congrArg (fun q => q.left) ht).trans hm)
  haveI : Mono (thick R I e) := by
    haveI : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hy : y' = (xe * yo).left := (cancel_mono (pullback.fst G.hom (thick R I e))).1 hf
  obtain ⟨p₁, p₂⟩ := hx e Z (rG ≫ (fst (TA R W) G).left) xe.left (hxe.trans (Category.assoc _ _ _).symm)
  have hone : GlobalTheory.TorusCoord.im (U.gt e) xe = 1 := by
    have : (ro ≫ fst _ _) ≫ (1 : TA R W ⟶ D.P.A) = 1 := MonObj.comp_one _
    exact (Over.OverMorphism.ext p₁).trans this
  subst hy
  refine ⟨?_, fun χ z J hJ => ?_⟩
  · have := GlobalTheory.TorusCoord.im_mul (U.gt e) xe yo
    rw [hone, _root_.one_mul] at this
    exact congrArg (fun q => q.left) this
  · have k := GlobalTheory.TorusCoord.val_t_mul_points (U.gt e) hG χ xe yo z J hJ
    have c : GlobalTheory.TorusCoord.cubeVal (U.gt e) χ z J xe yo = 1 := by
      unfold GlobalTheory.TorusCoord.cubeVal
      rw [hone]
      exact (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ).face₂ _ _
    rw [c, _root_.mul_one] at k
    exact (congrArg Units.val k).trans ((Units.val_mul _ _).trans (congrArg (· * _) (p₂ χ z J hJ)))

end GlobalTheory.UU.ShiftExp

theorem GlobalTheory.UU.expansion_translate_torus : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (W : Type) [CommRing W] [Algebra R W] (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G), U.TorPt a x → ∀ (k : ℕ) (σ : U.SecGT (TA R W) k) (f : ∀ α, SecBT D (TA R W) k α), U.ExpT (TA R W) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ (Z : Scheme.{0}) (y y' : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (TA R W ⊗ G).left) (rB : Z ⟶ (TA R W ⊗ D.P.A).left), rG ≫ (snd _ G).left = y ≫ (fstG I e G).left → rB ≫ (snd _ D.P.A).left = y ≫ (U.gt e).pG.left → rB ≫ (fst _ D.P.A).left = rG ≫ (fst _ G).left → y' ≫ (fstG I e G).left = rG ≫ (translPt G x).left → ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J → (∀ α ∉ s, sval (twist a f α) rB z J = 0) ∧ (U.wv e y' z JG J).val ^ k * sval σ (rG ≫ (translT G x).left) z JG = ∑ α ∈ s, sval (twist a f α) rB z J * (val ((U.gt e).t α) y z J).val := by
  intro hG R _ _ I D A G _ _ U W _ _ a x hx k σ f hf e
  obtain ⟨s, hs⟩ := hf e
  refine ⟨s, fun Z y y' rG rB h₁ h₂ h₃ h₄ z JG J hJG hJ => ?_⟩
  obtain ⟨p₁, p₂⟩ := ShiftExp.shift hG U a x hx e Z y y' rG h₁ h₄
  have e₁ : (translT G x).left ≫ (snd (TA R W) G).left = (translPt G x).left :=
    congrArg (fun q => q.left) (lift_snd (fst (TA R W) G) (translPt G x))
  have e₂ : (translT G x).left ≫ (fst (TA R W) G).left = (fst (TA R W) G).left :=
    congrArg (fun q => q.left) (lift_fst (fst (TA R W) G) (translPt G x))
  obtain ⟨q₁, q₂⟩ := hs Z y' (rG ≫ (translT G x).left) rB (by rw [Category.assoc, e₁, h₄]) (h₂.trans p₁.symm)
    (by rw [Category.assoc, e₂, h₃]) z JG J hJG hJ
  have tw : ∀ α, sval (twist a f α) rB z J =
      gs (𝟙 Z) z ⊤ (scal (R := W) (rG ≫ (fst (TA R W) G).left) (a (Multiplicative.ofAdd α)).val) *
        sval (f α) rB z J := fun α => by
    rw [← h₃]
    exact (ShiftExp.sval_secScale _ _ rB z hJ).trans (congrArg (· * _) (ShiftExp.gs_scal _ rB z _))
  refine ⟨fun α hα => by rw [tw, q₁ α hα, mul_zero], q₂.trans (Finset.sum_congr rfl fun α _ => ?_)⟩
  rw [tw, p₂ α z J hJ]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsZeroOfRed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.RedAdd

open GlobalTheory.FormalPoint GlobalTheory.TorusCoord ReciprocityTheory.ChartRestriction.G.DVR

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)
  {T : Over (Spec (CommRingCat.of R))}

theorem red_iff_over (x : T ⟶ G) (g : GtPt D T) :
    U.Red x g ↔ ∀ (e : ℕ) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (r : (Over.map (thick R I e)).obj Z ⟶ T) (a : Z ⟶ thickObj R I e G),
      (Over.map (thick R I e)).map a ≫ fstG I e G = r ≫ x → im (U.gt e) a = r ≫ g.b ∧
        ∀ χ z J, Good D.P.L z J →
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J = val (g.s χ) r.left z J := by
  constructor
  · intro h e Z r a ha
    obtain ⟨h₁, h₂⟩ := h e _ r.left ((Over.map (thick R I e)).map a).left (congrArg (fun q => q.left) ha)
    exact ⟨Over.OverMorphism.ext h₁, h₂⟩
  · intro h e Z r y hy
    have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
    obtain ⟨h₁, h₂⟩ := h e (Over.mk (y ≫ (thickObj R I e G).hom)) (Over.homMk r w) (Over.homMk y rfl)
      (Over.OverMorphism.ext hy)
    exact ⟨congrArg (fun q => q.left) h₁, h₂⟩

theorem map_one_fstG {e : ℕ} {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    (Over.map (thick R I e)).map (1 : Z ⟶ thickObj R I e G) ≫ fstG I e G = 1 := by
  have := map_mul_fstG (1 : Z ⟶ thickObj R I e G) 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem red_one {g : GtPt D T} (h : g.IsZero) : U.Red 1 g := by
  rw [red_iff_over]
  intro e Z r a ha
  obtain rfl : a = 1 := eq_of_map_fstG (by rw [ha, map_one_fstG, MonObj.comp_one])
  refine ⟨by rw [im_one, h.1]; exact (MonObj.comp_one r).symm, fun χ z J hJ => ?_⟩
  have t₁ := val_unit (U.gt e) χ (Z := Z) (z := z) hJ
  exact t₁.trans ((val_corr hJ (h.2 χ) r.left).trans (val_one _)).symm


variable {U} in
theorem red_mul (hG : GlobalFnsSt) {g g' g'' : GtPt D T} {x x' : T ⟶ G} (hx : U.Red x g)
    (hx' : U.Red x' g') (h : g.IsAdd g' g'') : U.Red (x * x') g'' := by
  rw [red_iff_over] at hx hx' ⊢
  intro e Z r y hy
  obtain ⟨a, ha⟩ := exists_lift_fstG (r ≫ x)
  obtain ⟨b, hb⟩ := exists_lift_fstG (r ≫ x')
  obtain rfl : y = a * b := eq_of_map_fstG (by rw [hy, map_mul_fstG, ha, hb, MonObj.comp_mul])
  obtain ⟨a₁, a₂⟩ := hx e Z r a ha
  obtain ⟨b₁, b₂⟩ := hx' e Z r b hb
  refine ⟨by rw [im_mul, a₁, b₁, h.1]; exact (MonObj.comp_mul _ _ _).symm, fun χ z J hJ => ?_⟩
  have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a * b)).left z J *
      th D z J (cP D _ χ) (im (U.gt e) a) (im (U.gt e) b) =
      val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J *
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map b).left z J :=
    val_t_mul_points (U.gt e) hG χ a b z J hJ
  have e₂ : val (g''.s χ) r.left z J * th D z J (r ≫ cP D T χ) (r ≫ g.b) (r ≫ g'.b) =
      val (g.s χ) r.left z J * val (g'.s χ) r.left z J :=
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub r hJ _ _ _))).symm.trans
      ((val_corr hJ (h.2 χ) r.left).trans (val_mul hJ _ _ _))
  rw [a₁, b₁, a₂ χ z J hJ, b₂ χ z J hJ] at e₁
  rw [comp_cP] at e₂
  exact mul_right_cancel (e₁.trans e₂.symm)

end Level

section Complete

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {S : Type} [CommRing S] {φ : R →+* S} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : PreU I D A G}


variable (I φ) in
abbrev lev (e : ℕ) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (levelMap I φ e)


variable (I φ) in
def levι (e : ℕ) : (Over.map (thick R I e)).obj (lev I φ e) ⟶ Over.mk (spMap φ) :=
  Over.homMk (thick S (I.map φ) e) (levelMap_thick I φ e).symm

variable [IsLocalRing S] [IsHausdorff (I.map φ) S]


omit [IsDomain R] in
theorem pt_ext {B : Over (Spec (CommRingCat.of R))} {b b' : Over.mk (spMap φ) ⟶ B}
    (h : ∀ e, levι I φ e ≫ b = levι I φ e ≫ b') : b = b' :=
  Over.OverMorphism.ext (hom_ext_of_isHausdorff (I.map φ) fun e => congrArg (·.left) (h e))

variable [IsNoetherianRing S]

theorem isAdd_of_red (hG : GlobalFnsSt) {x x' : Over.mk (spMap φ) ⟶ G} {g g' g'' : GtPt D (Over.mk (spMap φ))}
    (h : U.Red x g) (h' : U.Red x' g') (h'' : U.Red (x * x') g'') : GtPt.IsAdd g g' g'' := by
  rw [red_iff_over] at h h' h''
  choose a ha using fun e => exists_lift_fstG (levι I φ e ≫ x)
  choose a' ha' using fun e => exists_lift_fstG (levι I φ e ≫ x')
  have k := fun e => h e _ _ _ (ha e)
  have k' := fun e => h' e _ _ _ (ha' e)
  have k'' := fun e => h'' e _ (levι I φ e) (a e * a' e) (by rw [map_mul_fstG, ha, ha', MonObj.comp_mul])
  have hb : g''.b = g.b * g'.b := pt_ext (I := I) fun e => by
    rw [MonObj.comp_mul, ← (k e).1, ← (k' e).1, ← (k'' e).1, im_mul]
  refine ⟨hb, fun χ => CoordAdd.corr_of_thick (ne_top_of_isHausdorff (I.map φ)) D.P.isLB (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g''.isGen χ) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g.isGen χ) (g'.isGen χ)) fun e z J hJ => ?_⟩
  · refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
    refine (congrArg₂ (· * ·) (CoordAdd.prod_gtφT g''.b χ h) (prod_cub (DegPre.cT D _ χ) g.b g'.b h)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (CoordAdd.prod_gtφT g.b χ h) (CoordAdd.prod_gtφT g'.b χ h)).symm)
    rw [hb, _root_.mul_assoc (DegPre.cT D _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a e * a' e)).left z J *
        th D (T := (Over.map (thick R I e)).obj (lev I φ e)) z J (cP D _ χ) (im (U.gt e) (a e)) (im (U.gt e) (a' e)) =
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a e)).left z J *
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a' e)).left z J :=
      val_t_mul_points (U.gt e) hG χ (a e) (a' e) z J hJ
    rw [(k e).1, (k' e).1, (k e).2 χ z J hJ, (k' e).2 χ z J hJ, (k'' e).2 χ z J hJ,
      ← comp_cP D (levι I φ e)] at e₁
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (levι I φ e) hJ _ _ _))).trans
      (e₁.trans (val_mul hJ _ _ _).symm)

theorem isZero_of_red {g : GtPt D (Over.mk (spMap φ))} (h : U.Red 1 g) : g.IsZero := by
  rw [red_iff_over] at h
  have k := fun e => h e _ (levι I φ e) 1 (by rw [map_one_fstG, MonObj.comp_one])
  have hb : g.b = 1 := pt_ext (I := I) fun e => by rw [MonObj.comp_one, ← (k e).1, im_one]
  refine ⟨hb, fun χ => CoordAdd.corr_of_thick (ne_top_of_isHausdorff (I.map φ)) D.P.isLB (fun U _ h => ?_)
    (g.isGen χ) (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm) fun e z J hJ => ?_⟩
  · refine (CoordAdd.prod_gtφT g.b χ h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
  · exact ((k e).2 χ z J hJ).symm.trans
      ((val_unit (U.gt e) χ (Z := lev I φ e) (z := z) hJ).trans (val_one _).symm)

end Complete

theorem main : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (x x' x'' : TA V W ⟶ G) (g g' g'' : GtPt D (TA V W)), U.Red x g → U.Red x' g' → U.Red x'' g'' → (x'' = x * x' ↔ GtPt.IsAdd g g' g'') ∧ (x = 1 ↔ g.IsZero)) := by
  intro hG V _ _ _ hV D A G _ _ U W _ _ _ hW x x' x'' g g' g'' h h' h''
  have := hV.1
  have := hW.1
  have := hW.2.2.2.2
  have : IsNoetherianRing W := IsNoetherianRing.of_finite V W
  refine ⟨⟨fun e => ?_, fun e => ?_⟩, ⟨fun e => ?_, fun e => ?_⟩⟩
  · exact isAdd_of_red (φ := algebraMap V W) hG h h' (e ▸ h'')
  · exact RedOnto.red_unique (φ := algebraMap V W) h'' (red_mul hG h h' e)
  · exact isZero_of_red (φ := algebraMap V W) (e ▸ h)
  · exact RedOnto.red_unique (φ := algebraMap V W) h (red_one U e)

end GlobalTheory.UU.RedAdd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLimitUnit
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.FormalValue

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NormGen

theorem exists_factor {V W : Type} [CommRing V] [CommRing W] (I : Ideal V) (φ : V →+* W) (e : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ Sp W) (σ : Z ⟶ Sp (V ⧸ I ^ (e + 1))) (h : σ ≫ thick V I e = r ≫ spMap φ) :
    ∃ ρ : Z ⟶ Sp (W ⧸ I.map φ ^ (e + 1)), ρ ≫ thick W (I.map φ) e = r := by
  let ψ : CommRingCat.of W ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop
  have hr : Z.toSpecΓ ≫ Spec.map ψ = r := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hk : I.map φ ^ (e + 1) ≤ RingHom.ker ψ.hom := by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro v hv
    have e₁ : CommRingCat.ofHom φ ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ I ^ (e + 1)))).inv ≫ σ.appTop := by
      rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, h]
    have e₂ := congrArg (fun q => q.hom v) e₁
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      Ideal.Quotient.eq_zero_iff_mem.2 hv, map_zero] at e₂
    exact e₂
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ ψ.hom hk)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← hr]
  rfl

theorem gs_valR {A : Type} [CommRing A] {X Z : Scheme.{0}} (ρ : Z ⟶ Sp A) (y : Sp A ⟶ X) (V : X.Opens)
    (ht : ⊤ ≤ y ⁻¹ᵁ V) (s : Γ(X, V)) (z : Z) :
    gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (valR y V s)) = gs (ρ ≫ y) z V s := by
  rw [valR, dite_eq_left ht, Iso.hom_inv_id_apply, ← gs_pull ρ y z V (ht trivial)]
  exact gs_res ρ z ht trivial _

theorem valR_id {A : Type} [CommRing A] (a : A) :
    valR (𝟙 (Sp A)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a := by
  rw [valR, dite_eq_left (show ⊤ ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ from le_top)]
  have : Scheme.Hom.appLE (𝟙 (Sp A)) ⊤ ⊤ le_top = 𝟙 _ := by
    exact (Category.id_comp _).trans ((Sp A).presheaf.map_id _)
  rw [this]
  exact Iso.inv_hom_id_apply _ _

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_limit_unit (U : PreU I D A G) {W : Type} [CommRing W] [IsLocalRing W] (φ : R →+* W)
    [IsAdicComplete (I.map φ) W] (x : Sp W ⟶ G.left) (hx : x ≫ G.hom = spMap φ) (b : Sp W ⟶ D.P.A.left)
    (hb : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → xe ≫ (U.gt e).pG.left = r ≫ b)
    {jL : U.P.L.L.ι} {jM : D.P.L.ι} (hL : ⊤ ≤ x ⁻¹ᵁ U.P.L.L.U jL) (hM : ⊤ ≤ b ⁻¹ᵁ D.P.L.U jM) :
    ∃ a : Γ(Sp W, ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, gm r z ⊤ a * gw (U.w e) xe z jM (fun _ => jL) = 1 := by
  choose y hy using exists_lift_thick I G φ x hx
  have mL : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (fstG I e G).left (xe z) ∈ U.P.L.L.U jL := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ U.P.L.L.U jL) h).mpr (hL (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  have mM : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (U.gt e).pG.left (xe z) ∈ D.P.L.U jM := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ D.P.L.U jM) (hb e Z r xe h)).mpr (hM (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  let O : ∀ e, (thickObj R I e G).left.Opens := fun e =>
    (D.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓ (U.P.L.L.pull (fstG I e G).left).U (fun _ => jL)
  let s : ∀ e, Γ((thickObj R I e G).left, O e)ˣ := fun e => (U.w e).s (fun _ => jM, fun _ => jL)
  have mO : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, xe z ∈ O e := fun e Z r xe h z =>
    ⟨mem_pull.2 (mM e Z r xe h z), mem_pull.2 (mL e Z r xe h z)⟩
  have ht : ∀ e, ⊤ ≤ y e ⁻¹ᵁ O e := fun e z _ => mO e _ _ _ (hy e) z
  have hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (valR (y (e + 1)) (O (e + 1)) (s (e + 1)).val) = valR (y e) (O e) (s e).val := fun e => by
    have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (I.map φ)) e
    have := fstG_mono (I := I) (G := G) (e + 1)
    have e₁ : thickTrans W (I.map φ) e ≫ y (e + 1) = y e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hy,
        show thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left from thickMap_comp_fGl I e G, hy,
        ← Category.assoc, thickTrans_comp]
    apply toStkA_injective
    refine (toStkA_map_valR _ _ _ _ (ht _) _).trans (Eq.trans ?_ (toStkA_valR_eq_gs _ _ _ (ht _) _).symm)
    refine (gs_unit _ _ _ (mO (e + 1) _ (thickTrans W (I.map φ) e ≫ thick W (I.map φ) (e + 1)) _ (by
      rw [Category.assoc, hy, Category.assoc]) _) _).trans (Eq.trans ?_ (gs_unit _ _ _ (mO e _ _ _ (hy e) _) _).symm)
    refine congrArg Units.val ((congrArg (fun q => gm q _ (O (e + 1)) (s (e + 1))) e₁).trans ?_)
    exact U.w_compat e _ (y e) _ jM jL (mM e _ _ _ (hy e) _) (mL e _ _ _ (hy e) _)
  obtain ⟨a, ha⟩ := exists_unit_limit (I.map φ) _ hc fun e => isUnit_valR _ _ (ht e) _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a, fun e Z r xe h z => ?_⟩
  obtain ⟨ρ, rfl⟩ := exists_factor I φ e r (xe ≫ (thickObj R I e G).hom) (by
    rw [← hx, ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (xe ≫ ·) pullback.condition.symm)
  have := fstG_mono (I := I) (G := G) e
  obtain rfl : xe = ρ ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, hy]
  apply Units.ext
  have H := congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) (ha e)
  simp only [map_mul, map_one] at H
  rw [gs_mul ρ z ⊤ trivial, gs_valR _ _ _ (ht e), gs_unit _ _ _ (mO e _ _ _ h z), gs_eq ρ z ⊤ trivial 1, map_one,
    map_one] at H
  refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) H
  rw [← gs_unit _ z ⊤ trivial, ← gs_valR ρ (thick W (I.map φ) e) ⊤ le_top]
  refine congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) ?_
  have k := valR_spMap (Ideal.Quotient.mk (I.map φ ^ (e + 1))) (𝟙 (Sp W)) ⊤ le_top
    ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a.val)
  rw [valR_id, Category.comp_id] at k
  exact k

theorem one_pG (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left)
    (oe : Z ⟶ (thickObj R I e G).left) (h : oe ≫ (fstG I e G).left = r ≫ (1 : T ⟶ G).left) :
    oe ≫ (U.gt e).pG.left = r ≫ (1 : T ⟶ D.P.A).left := by
  have hf : ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H],
      eSec (thickObj R I e H) ≫ (fstG I e H).left = thick R I e ≫ eSec H := fun H _ => by
    show eSec (thickObj R I e H) ≫ pullback.fst H.hom (thick R I e) = _
    simp [eSec]
  have hp : eSec (thickObj R I e G) ≫ (U.gt e).pG.left = thick R I e ≫ eSec D.P.A := by
    have := (U.gt e).q_hom
    have h : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.P.A) :=
      congrArg (·.left) (IsMonHom.one_hom (U.gt e).q)
    rw [← hf D.P.A, ← h, Category.assoc]
    rfl
  have hσ : (oe ≫ (thickObj R I e G).hom) ≫ thick R I e = r ≫ T.hom := by
    rw [← Over.w (1 : T ⟶ G), ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (oe ≫ ·) pullback.condition.symm
  have := fstG_mono (I := I) (G := G) e
  have ho : oe = (oe ≫ (thickObj R I e G).hom) ≫ eSec (thickObj R I e G) := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc _ (eSec _), hf, ← Category.assoc _ (thick R I e), hσ,
      one_left, Category.assoc]
  rw [ho, Category.assoc _ (eSec _), hp, ← Category.assoc _ (thick R I e), hσ, one_left, Category.assoc]

theorem gw_change (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (xe : Z ⟶ (thickObj R I e G).left) (z : Z)
    {p : Z ⟶ G.left} {q : Z ⟶ D.P.A.left} (hp : xe ≫ (fstG I e G).left = p) (hq : xe ≫ (U.gt e).pG.left = q)
    {j j' : D.P.L.ι} {k k' : U.P.L.L.ι} (hj : q z ∈ D.P.L.U j) (hj' : q z ∈ D.P.L.U j') (hk : p z ∈ U.P.L.L.U k)
    (hk' : p z ∈ U.P.L.L.U k') :
    gw (U.w e) xe z j (fun _ => k) =
      gm q z _ (D.P.L.g j j') * (gm p z _ (U.P.L.L.g k k'))⁻¹ * gw (U.w e) xe z j' (fun _ => k') := by
  subst hp hq
  have w := (isGen_iff _).1 (U.w_gen e) Z xe z j j' (fun _ => k) (fun _ => k') hj hj' (mem_pull.2 hk) (mem_pull.2 hk')
  rw [gm_pull_g _ _ xe z _ _ (mem_pull.2 hk) (mem_pull.2 hk')] at w
  exact w

theorem exists_normAt : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (a : Multiplicative D.X →* Wˣ) (x : TA V W ⟶ G), U.TorPt a x → ∃ ν, U.NormAt x ν := by
  intro V _ _ _ _ D A G _ _ U W _ _ _ hW a x hx
  have := hW.2.2.2.2
  obtain ⟨jx, hjx⟩ := exists_chart U.P.L.isLB (x.left (cpt W))
  obtain ⟨jo, hjo⟩ := exists_chart U.P.L.isLB ((1 : TA V W ⟶ G).left (cpt W))
  obtain ⟨jM, hjM⟩ := exists_chart D.P.isLB ((1 : TA V W ⟶ D.P.A).left (cpt W))
  replace hjx := (top_le_iff_cpt (A := W) x.left _).2 hjx
  replace hjo := (top_le_iff_cpt (A := W) (1 : TA V W ⟶ G).left _).2 hjo
  replace hjM := (top_le_iff_cpt (A := W) (1 : TA V W ⟶ D.P.A).left _).2 hjM
  obtain ⟨α, hα⟩ := exists_limit_unit U (algebraMap V W) x.left (Over.w x) (1 : TA V W ⟶ D.P.A).left
    (fun e Z r xe h => (hx e Z r xe h).1) hjx hjM
  obtain ⟨β, hβ⟩ := exists_limit_unit U (algebraMap V W) (1 : TA V W ⟶ G).left (Over.w _) (1 : TA V W ⟶ D.P.A).left
    (fun e Z r xe h => one_pG U (T := TA V W) e Z r xe h) hjo hjM
  obtain ⟨ν, hν⟩ := exists_gen_of_local (V := W) U.P.L.L U.P.L.isLB (K := Fin 2) ![x.left, (1 : TA V W ⟶ G).left] ![-1, 1]
  have ht : ⊤ ≤ LB.wchart U.P.L.L (K := Fin 2) ![x.left, (1 : TA V W ⟶ G).left] ![jx, jo] := fun y _ =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hjx trivial, hjo trivial]
  obtain ⟨n, hn⟩ : ∃ n : Γ(Sp W, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JG), Good U.P.L.L z JG →
      val ν r z JG = (gm (r ≫ x.left) z _ (U.P.L.L.g (JG (r ≫ x.left)) jx))⁻¹ *
        gm (r ≫ (1 : TA V W ⟶ G).left) z _ (U.P.L.L.g (JG (r ≫ (1 : TA V W ⟶ G).left)) jo) * gm r z ⊤ n := by
    refine ⟨res (X := Sp W) ht (ν.s ![jx, jo]), fun Z r z JG hG => ?_⟩
    refine (gen_trans hν r z (hG.mem _ r) (ht trivial)).trans (congrArg₂ (· * ·) ?_ (gm_res r z ht trivial _).symm)
    rw [trF, Fin.prod_univ_two]
    exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
  refine ⟨UU.scaleGen (β * α⁻¹ * n⁻¹ : Γ(Sp W, ⊤)ˣ) ν, UU.scaleGen_isGen _ hν,
    fun e Z (r : Z ⟶ Sp W) xe oe h₁ h₂ z JG J hG hJ => ?_⟩
  have q₁ := (hx e Z r xe h₁).1
  have q₂ := one_pG U (T := TA V W) e Z r oe h₂
  have m : ∀ {X : Scheme.{0}} {f : Sp W ⟶ X} {O : X.Opens}, ⊤ ≤ f ⁻¹ᵁ O → (r ≫ f) z ∈ O := fun h => h trivial
  have a₁ := eq_inv_of_mul_eq_one_right (hα e Z r xe h₁ z)
  have a₂ := eq_inv_of_mul_eq_one_right (hβ e Z r oe h₂ z)
  have w₁ : U.wv e xe z JG J = _ := (congrArg₂ (fun j k => gw (U.w e) xe z (J j) (fun _ => JG k)) q₁ h₁).trans
    (gw_change U e xe z h₁ q₁ (hJ _) (m hjM) (hG _) (m hjx))
  have w₂ : U.wv e oe z JG J = _ := (congrArg₂ (fun j k => gw (U.w e) oe z (J j) (fun _ => JG k)) q₂ h₂).trans
    (gw_change U e oe z h₂ q₂ (hJ _) (m hjM) (hG _) (m hjo))
  rw [a₁] at w₁
  rw [a₂] at w₂
  have v := val_scaleGen (β * α⁻¹ * n⁻¹) ν r hG
  rw [hn Z r z JG hG, map_mul, map_mul, map_inv, map_inv] at v
  refine (congrArg₂ (· * ·) v w₂).trans (Eq.trans ?_ w₁.symm)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.NormGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Transl

section General
variable {X X' W Y Y₂ : Scheme.{0}} {L : LB X} {L' : LB X'} {K : Type} [Fintype K]

theorem exists_gen_of_iso (hL : L.IsLB) (hL' : L'.IsLB) {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) (y : K → (Y ⟶ W)) (h : Y ⟶ Y₂) {φ : K → (Y₂ ⟶ X)}
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (ha : ∀ k, y k ≫ F' = φ' k) (hb : ∀ k, y k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (J'), Good L z J →
      Good L' z J' → val t (r ≫ h) z J =
        (∏ k, gw w (r ≫ y k) z (J ((r ≫ y k) ≫ F)) (fun _ => J' ((r ≫ y k) ≫ F')) ^ ε k) * val a r z J' := by
  obtain rfl : (fun k => y k ≫ F') = φ' := funext ha
  obtain ⟨a, ga, H⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 hw) hL (pull_isLB hL' F') (φ' := y) h hb t ht
  have le : ∀ j : K → L'.ι, LB.wchart L' (fun k => y k ≫ F') j ≤ LB.wchart (L'.pull F') y (fun k _ => j k) :=
    fun j p hp => Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hp k)
  refine ⟨⟨fun j => res (le j) (a.s fun k _ => j k)⟩, isGen_of_gm _ fun p j j' hj hj' => ?_,
    fun Z r z J J' hJ hJ' => ?_⟩
  · refine (gm_res _ p (le j) hj _).trans ((gen_trans ga (𝟙 Y) p (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ p (le j') hj' _).symm))
    refine (gm_pull_g L' F' (𝟙 Y ≫ y k) p _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans ?_
    rw [Category.assoc]
  · have g' : Good (L'.pull F') z (fun ψ _ => J' (ψ ≫ F')) := fun ψ => mem_pull.2 (hJ' (ψ ≫ F'))
    refine (CubTransport.val_pmaps hb H r hJ g').trans (congrArg (_ * ·) ?_)
    rw [val_of _ r z J' (fun k => J' ((r ≫ y k) ≫ F')) (fun k => by rw [Category.assoc])]
    exact (gm_res r z (le _) (Set.mem_iInter.2 fun k => hJ' ((r ≫ y k) ≫ F')) _).symm

theorem exists_unit_base {S₀ : Scheme.{0}} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (a : Γ(Y, ⊤)ˣ) :
    ∃ c : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), gm r z ⊤ a = gm (r ≫ p) z ⊤ c := by
  obtain ⟨c, hc⟩ := hp a.val
  have e₁ : e.appTop.hom a.val = c := by
    rw [← hc, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]; simp
  refine ⟨Units.map e.appTop.hom.toMonoidHom a, fun Z r z => ?_⟩
  refine Eq.trans (congrArg (gm r z ⊤) (Units.ext ?_)) (gm_pull r p z ⊤ trivial _)
  exact hc.symm.trans (congrArg p.appTop.hom e₁.symm)

theorem surj_fst (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have e : (fst T A).left = (β_ T A).hom.left ≫ (snd A T).left := by
    rw [← Over.comp_left, braiding_hom_snd]
  rw [e]
  have : IsIso (β_ T A).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (β_ T A).hom))
  have : IsIso (β_ T A).hom.left.appTop := inferInstanceAs (IsIso ((β_ T A).hom.left.app ⊤))
  exact surj_comp (ConcreteCategory.bijective_of_isIso (β_ T A).hom.left.appTop).2 (surj_snd hG hA T)

def comb {M : LB Y} (a : Γ(Y, ⊤)) (s t : LB.Sec M) : LB.Sec M where
  f j := (Y.presheaf.map (homOfLE le_top).op).hom a * s.f j + t.f j
  compat i j := by
    have e : ∀ {V : Y.Opens} (h : M.U i ⊓ M.U j ≤ V), (Y.presheaf.map (homOfLE h).op).hom
        ((Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a) = (Y.presheaf.map (homOfLE le_top).op).hom a :=
      fun h => by rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_add (f := _), map_add (f := _), map_mul, map_mul, e, e, s.compat i j, t.compat i j]
    ring

def zeroSec (M : LB Y) : LB.Sec M where
  f _ := 0
  compat i j := by rw [map_zero, map_zero, mul_zero]

theorem sval_zeroSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) :
    sval (zeroSec (LB.LinComb L φ ε)) r z J = 0 := by
  unfold sval gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem gs_scal {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
  gs_pull r p z ⊤ trivial _

end General

theorem cubN_twist {A B C U : Type} [CommGroup A] [CommGroup B] [CommGroup C] [CommGroup U] (β : A →* B) (κ : A →* C)
    (W : A → U) {θ : B → B → B → U} {θ' : C → C → C → U}
    (h : ∀ a b c, θ (β a) (β b) (β c) * W (a * b) * W (a * c) * W (b * c) * W 1 =
      W (a * b * c) * W a * W b * W c * θ' (κ a) (κ b) (κ c)) {N : ℕ} {m : A} (hm : m ^ N = 1) (y : A) :
    cubN θ N 1 (β m) (β y) * W (m * y) ^ N * W 1 ^ N = W y ^ N * W m ^ N * cubN θ' N 1 (κ m) (κ y) := by
  have key : ∀ n : ℕ, cubN θ n 1 (β m) (β y) * W (m ^ n) * W y * W (m * y) ^ n * W 1 ^ n =
      W (m ^ n * y) * W 1 * W y ^ n * W m ^ n * cubN θ' n 1 (κ m) (κ y) := by
    intro n
    induction n with
    | zero => simp [cubN, mul_comm]
    | succ n ih =>
      have c := h (m ^ n) m y
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, map_pow, ← pow_succ m] at ih c ⊢
      simp only [pow_succ (W _)]
      apply Additive.ofMul.injective
      have ih' := congrArg Additive.ofMul ih
      have c' := congrArg Additive.ofMul c
      simp only [ofMul_mul] at ih' c' ⊢
      linear_combination (norm := abel) ih' + c'
  have k := key N
  rw [hm, _root_.one_mul y] at k
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul k
  simp only [ofMul_mul] at k' ⊢
  linear_combination (norm := abel) k'

section Theta
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

theorem exists_thetaGen {T : Over S} (x : T ⟶ G) {N : ℕ} (hx : x ^ N = 1)
    (f : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(1 : T ⟶ G).left, x.left] ![(N : ℤ), -(N : ℤ)])) (hf : f.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T G).left, ((fst T G ≫ x) * snd T G).left] ![(N : ℤ), -(N : ℤ)]),
      t.IsGen ∧ ∀ (T' : Over S) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good L.L z J →
        val t (lift τ y).left z J = cubN (cubV c z J) N 1 (τ ≫ x) y * val f τ.left z J := by
  obtain ⟨n, hn, vn⟩ := exists_cubN c 1 (fst T G ≫ x) (snd T G) N
  have hm : (fst T G ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, vt⟩ := exists_gen L.isLB (φ' := ![(snd T G).left, ((fst T G ≫ x) * snd T G).left])
    (ε' := ![(N : ℤ), -(N : ℤ)]) (fun U _ h => by
      have q : (fst T G).left ≫ (1 : T ⟶ G).left = (1 : T ⊗ G ⟶ G).left :=
        congrArg (fun q : T ⊗ G ⟶ G => q.left) (MonObj.comp_one (M := G) (fst T G))
      have p : ∏ k : Fin 2, h ((fst T G).left ≫ ![(1 : T ⟶ G).left, x.left] k) ^ (![(N : ℤ), -(N : ℤ)] k) =
          h (1 : T ⊗ G ⟶ G).left ^ (N : ℤ) * h (fst T G ≫ x).left ^ (-(N : ℤ)) := by
        rw [Fin.prod_univ_two, ← q]; rfl
      refine (DVR.prod_sum₂ (K := Fin 8) (K' := Fin 2) (U := U) _ rfl p).trans ?_
      rw [hm]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen L.L _ _ _ _ n (LB.pullGen L.L _ _ f (fst T G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hn (DVR.pullGen_isGen _ _ _ _ hf _))
  refine ⟨t, ht, fun T' τ y z J hJ => ?_⟩
  refine (vt _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((vn T' _ z J hJ).trans ?_)
    ((val_pull hJ _ _ _).trans ?_)))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]

end Theta

section ThetaSec
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem exists_translSec (hL : L.IsLB) {T : Over S} (x : T ⟶ G) {N : ℤ}
    (t : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T G).left, ((fst T G ≫ x) * snd T G).left] ![N, -N]))
    (ht : t.IsGen) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ _) G).left) (fun _ => N))) :
    ∃ σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => N)),
      ∀ (T' : Over S) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good L z J →
        sval σ' (lift τ y).left z J =
          sval σ (lift (toUnit T') ((τ ≫ x) * y)).left z J * (val t (lift τ y).left z J).val := by
  obtain ⟨σ', v⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T G).left) (ε' := fun _ => N) (fun U _ h => by
      have q : (lift (toUnit (T ⊗ G)) ((fst T G ≫ x) * snd T G)).left ≫ (snd (𝟙_ _) G).left =
          ((fst T G ≫ x) * snd T G).left := by rw [← Over.comp_left, lift_snd]
      refine (DVR.prod_sum₂ (K := Fin 1) (K' := Fin 2) (U := U) _ (Fin.prod_univ_one _) (Fin.prod_univ_two _)).trans ?_
      rw [Fin.prod_univ_one]
      show h (_ ≫ _) ^ N * (h (snd T G).left ^ N * h ((fst T G ≫ x) * snd T G).left ^ (-N)) = _
      rw [q, zpow_neg, mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec σ (lift (toUnit (T ⊗ G)) ((fst T G ≫ x) * snd T G)).left t ht)
  refine ⟨σ', fun T' τ y z J hJ => (v _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  rw [← Over.comp_left, comp_lift, MonObj.comp_mul, lift_fst_assoc, lift_snd, toUnit_unique (_ ≫ _) (toUnit T')]

end ThetaSec

section Base
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
open ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_famT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T ⊗ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ famφT D T α i) ^ DegPre.famε k i =
      h (ρ ≫ snd _ _).left ^ ((k : ℤ) - 1) * h (cP D T' α * (ρ ≫ snd _ _)).left * (h (cP D T' α).left)⁻¹ *
        h (1 : T' ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ famφT D T α 1 = (cP D T' α * (ρ ≫ snd _ _)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (snd _ _) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ famφT D T α 2 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ famφT D T α 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

def fac {T T' : Over (Spec (CommRingCat.of R))} (g : GtPt D T) (N : ℕ)
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, g.b.left] ![(N : ℤ), -(N : ℤ)])) (α : D.X)
    (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J : (T'.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T'.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) N 1 (τ ≫ g.b) y * val w τ.left z J * val (g.s α) τ.left z J *
    (th D z J (cP D T' α) (τ ≫ g.b) y)⁻¹

theorem exists_translFam {T : Over (Spec (CommRingCat.of R))} (g : GtPt D T) {N : ℕ} (hb : g.b ^ N = 1)
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, g.b.left] ![(N : ℤ), -(N : ℤ)]))
    (hw : w.IsGen) (α : D.X) (f : SecBT D (𝟙_ _) N α) :
    ∃ f' : SecBT D T N α, ∀ (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J),
      Good D.P.L z J → sval f' (lift τ y).left z J =
        sval f (lift (toUnit T') ((τ ≫ g.b) * y)).left z J * (fac g N w α τ y z J).val := by
  obtain ⟨t, ht, vt⟩ := exists_thetaGen D.cub g.b hb w hw
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let m : T ⊗ D.P.A ⟶ D.P.A := fst _ _ ≫ g.b
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t (LB.pullGen D.P.L _ _ (g.s α) (fst T D.P.A).left))
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift m x)).left))
  have hu : u.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ ht (pullGen_isGen _ _ _ _ (g.isGen α) _))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))
  obtain ⟨f', v⟩ := exists_sec D.P.isLB (φ' := famφT D T α) (ε' := DegPre.famε N) (fun U _ h => by
      have p₁ := prod_cub a m x h
      have p₂ := FormalPoint.prod_gtφT (fst T D.P.A) g.b α h
      have p₃ := prod_famT (𝟙 (T ⊗ D.P.A)) α N h
      have p₄ := prod_famT (lift (toUnit (T ⊗ D.P.A)) (m * x)) α N h
      have p₅ : ∏ k : Fin 2, h (![x.left, (m * x).left] k) ^ (![(N : ℤ), -(N : ℤ)] k) =
          h x.left ^ (N : ℤ) * h (m * x).left ^ (-(N : ℤ)) := Fin.prod_univ_two _
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [lift_snd, ← _root_.mul_assoc (cP D _ α)] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := (Fin 2 ⊕ Fin 4) ⊕ thK) (U := U) _ p₄
        (prod_sum₂ (K := Fin 2 ⊕ Fin 4) (K' := thK) (U := U) _
          (prod_sum₂ (K := Fin 2) (K' := Fin 4) (U := U) _ p₅ p₂) (prod_neg _ _ p₁))) (Eq.trans ?_ p₃.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, m, x]
      module)
    (pullMulSec f (lift (toUnit (T ⊗ D.P.A)) (m * x)).left u hu)
  refine ⟨f', fun T' τ y z J hJ => (v _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  have e : val u (lift τ y).left z J = fac g N w α τ y z J := by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (vt T' τ y z J hJ) ((val_pull hJ _ _ _).trans ?_))) ((val_inv _ _).trans (congrArg (·⁻¹)
      ((val_cub D.cub (lift τ y) hJ _ _ _).trans ?_))))
    · rw [← Over.comp_left, lift_fst]
    · rw [comp_cP, lift_fst_assoc, lift_snd]
  rw [e, ← Over.comp_left, comp_lift, MonObj.comp_mul, lift_fst_assoc, lift_snd, toUnit_unique (_ ≫ _) (toUnit T')]

end Base

end GlobalTheory.UU.Transl
end
end
