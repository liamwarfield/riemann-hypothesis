module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
noncomputable section

namespace GlobalTheory.TorusModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusExt GlobalTheory.FormalPoint

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))}

abbrev cv (g : GtPt D T) (χ : D.X) (y : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T.left.presheaf.stalk y)ˣ := val (g.s χ) (𝟙 T.left) y J

theorem pt_ext {g g' : GtPt D T} (hb : g.b = g'.b)
    (h : ∀ χ y J, Good D.P.L y J → cv g χ y J = cv g' χ y J) : g = g' := by
  obtain ⟨b, s, hs, _, _⟩ := g
  obtain ⟨b', s', hs', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ => TorusCoord.gen_eq_of_corr D.P.isLB (hs χ) (hs' χ)
    (corr_of_val D.P.isLB (h χ))
  rfl

theorem prod_pt (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφT D T b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  simp [DegPre.gtφT, DegPre.gtε, Fin.prod_univ_four]
  rfl

theorem val_cubAtT {y : T.left} {J} (hJ : Good D.P.L y J) (x x' w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T x x' w) (𝟙 _) y J = th D y J x x' w := by
  have := val_cub D.cub (𝟙 T) hJ x x' w
  rwa [Category.id_comp, Category.id_comp, Category.id_comp] at this

theorem cv_zero (g : GtPt D T) {y J} (hJ : Good D.P.L y J) : cv g 0 y J = 1 :=
  (val_corr hJ g.s_zero _).trans (val_one _)

theorem cv_add (g : GtPt D T) {y J} (hJ : Good D.P.L y J) (χ χ' : D.X) :
    cv g (χ + χ') y J * th D y J (cP D _ χ) (cP D _ χ') g.b = cv g χ y J * cv g χ' y J :=
  ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).symm.trans
    ((val_corr hJ (g.mult χ χ') _).trans (val_mul hJ _ _ _))

theorem exists_pt (b : T ⟶ D.P.A) {K : Type} [Fintype K] {φ : D.X → K → (T.left ⟶ D.P.A.left)}
    {ε : K → ℤ} (v : ∀ χ, LB.Gen (LB.LinComb D.P.L (φ χ) ε)) (hv : ∀ χ, (v χ).IsGen)
    (hF : ∀ χ, FormEq (φ χ) ε (DegPre.gtφT D T b χ) DegPre.gtε)
    (h₀ : ∀ y J, Good D.P.L y J → val (v 0) (𝟙 _) y J = 1)
    (hm : ∀ χ χ' y J, Good D.P.L y J → val (v (χ + χ')) (𝟙 _) y J * th D y J (cP D _ χ) (cP D _ χ') b =
      val (v χ) (𝟙 _) y J * val (v χ') (𝟙 _) y J) :
    ∃ g : GtPt D T, g.b = b ∧ ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      val (g.s χ) r y J = val (v χ) r y J := by
  choose s hs vs using fun χ => exists_gen D.P.isLB (hF χ) (v χ) (hv χ)
  refine ⟨⟨b, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl,
    fun χ Z r y J hJ => vs χ _ _ y J hJ⟩
  · exact (vs 0 _ _ y J hJ).trans ((h₀ y J hJ).trans (val_one _).symm)
  · exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (vs _ _ _ y J hJ) (val_cubAtT hJ _ _ _)).trans
      ((hm χ χ' y J hJ).trans
      ((congrArg₂ (· * ·) (vs _ _ _ y J hJ) (vs _ _ _ y J hJ)).symm.trans (val_mul hJ _ _ _).symm)))

theorem isAdd_iff (g g' g'' : GtPt D T) : g.IsAdd g' g'' ↔ g''.b = g.b * g'.b ∧ ∀ χ y J, Good D.P.L y J →
    cv g'' χ y J * th D y J (cP D _ χ) g.b g'.b = cv g χ y J * cv g' χ y J :=
  and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ _ hJ =>
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).symm.trans
      ((val_corr hJ h _).trans (val_mul hJ _ _ _)),
    fun h => corr_of_val D.P.isLB fun y J hJ => ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).trans ((h y J hJ).trans (val_mul hJ _ _ _).symm)⟩)

theorem isAdd_unique {g g' h h' : GtPt D T} (e : g.IsAdd g' h) (e' : g.IsAdd g' h') : h = h' := by
  rw [isAdd_iff] at e e'
  exact pt_ext (e.1.trans e'.1.symm) fun χ y J hJ => mul_right_cancel ((e.2 χ y J hJ).trans (e'.2 χ y J hJ).symm)

theorem isPull_iff (k : T' ⟶ T) (g : GtPt D T) (g' : GtPt D T') : GtPt.IsPull k.left g g' ↔
    g'.b = k ≫ g.b ∧ ∀ χ y J, Good D.P.L y J → cv g' χ y J = val (g.s χ) k.left y J :=
  and_congr ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩ (forall_congr' fun _ =>
    ⟨fun h _ _ hJ => (val_corr hJ h _).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])),
      fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans
        ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm⟩)

theorem isPull_unique {k : T' ⟶ T} {g : GtPt D T} {h h' : GtPt D T'} (e : GtPt.IsPull k.left g h)
    (e' : GtPt.IsPull k.left g h') : h = h' := by
  rw [isPull_iff] at e e'
  exact pt_ext (e.1.trans e'.1.symm) fun χ y J hJ => (e.2 χ y J hJ).trans (e'.2 χ y J hJ).symm

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O)

theorem val_smul (a : O) (g : GtPt D T)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (χ : D.X)
    (k : T' ⟶ T) {y J} (hJ : Good D.P.L y J) : val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) k.left y J =
      val (g.s (star a • χ)) k.left y J * val₂ u y J (cP D _ χ) (k ≫ g.b) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull_pair u k hJ _ _).trans (by rw [comp_cP])))

theorem val_smul' (a : O) (g : GtPt D T)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (χ : D.X)
    {y J} (hJ : Good D.P.L y J) : val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 T.left) y J =
      cv g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b := by
  simpa using val_smul oa a g u χ (𝟙 T) hJ

theorem isSmulPt_iff (a : O) (g g' : GtPt D T) :
    IsSmulPt oa a g g' ↔ g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      cv g' χ y J = cv g (star a • χ) y J * val₂ (rosGen hG oa a) y J (cP D _ χ) g.b := by
  refine and_congr Iff.rfl ⟨fun h χ y J hJ => ?_, fun h u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · exact (val_corr hJ (h _ (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ) _).symm.trans
      (val_smul' oa a g _ χ hJ)
  · exact (val_smul' oa a g u χ hJ).trans ((congrArg₂ (· * ·) rfl
      (IsRos.unique hG D.P.isAb D.P.isLB ⟨hu, u₀⟩ (rosGen_isRos hG oa a) hJ _ _)).trans (h χ y J hJ).symm)

include hG in
theorem exists_isSmulPt (a : O) (g : GtPt D T) : ∃ g', IsSmulPt oa a g g' := by
  have := oa.onB.hom (star a)
  have vv := fun χ y J (hJ : Good D.P.L y J) => val_smul' oa a g (rosGen hG oa a) χ hJ
  obtain ⟨g', hb, hv⟩ := exists_pt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
      (LB.pullGen D.P.L _ _ (rosGen hG oa a) (lift (cP D _ χ) g.b).left))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ (rosGen_isRos hG oa a).1 _))
    (fun χ U _ h => by
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_pt g.b (star a • χ) h)
        (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
      rw [prod_pt, cPoint_smul oa]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      have face (x y' : T ⟶ D.P.A) : th D y J 1 x y' = 1 := by
        have e := val_corr hJ (D.cub.face 0) (lift x y').left
        rw [val_one] at e
        refine Eq.trans ?_ e
        refine Eq.trans ?_ (val_cub D.cub (lift x y') hJ (pzero D.P.A _) (x2 D.P.A 0) (x2 D.P.A 1)).symm
        congr 1 <;> simp [x2, pzero, Hom.one_def]
      have e := (rosGen_add hG oa a hJ 1 1 g.b).1
      rw [_root_.mul_one, MonObj.one_comp, face, face, _root_.mul_one, _root_.one_mul] at e
      refine (vv 0 y J hJ).trans ?_
      rw [smul_zero, cPoint_zero, mul_eq_left.1 e.symm, _root_.mul_one, cv_zero g hJ]) (fun χ χ' y J hJ => by
      have e₁ := congrArg Additive.ofMul (rosGen_add hG oa a hJ (cP D _ χ) (cP D _ χ') g.b).1
      have e := cv_add g hJ (star a • χ) (star a • χ')
      rw [cPoint_smul oa, cPoint_smul oa] at e
      have e₂ := congrArg Additive.ofMul e
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      rw [smul_add, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at e₁ e₂ ⊢
      linear_combination (norm := abel) e₁ + e₂)
  exact ⟨g', (isSmulPt_iff hG oa _ _ _).2 ⟨hb, fun χ y J hJ => (hv χ _ _ y J hJ).trans (vv χ y J hJ)⟩⟩

def smulPt (a : O) (g : GtPt D T) : GtPt D T := (exists_isSmulPt hG oa a g).choose

theorem isSmulPt_smulPt (a : O) (g : GtPt D T) : IsSmulPt oa a g (smulPt hG oa a g) :=
  (exists_isSmulPt hG oa a g).choose_spec

theorem smulPt_b (a : O) (g : GtPt D T) : (smulPt hG oa a g).b = g.b ≫ oa.onB.act a :=
  ((isSmulPt_iff hG oa a g _).1 (isSmulPt_smulPt hG oa a g)).1

theorem smulPt_val (a : O) (g : GtPt D T) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    cv (smulPt hG oa a g) χ y J = cv g (star a • χ) y J * val₂ (rosGen hG oa a) y J (cP D _ χ) g.b :=
  ((isSmulPt_iff hG oa a g _).1 (isSmulPt_smulPt hG oa a g)).2 χ y J hJ

theorem smulPt_pull (a : O) (k : T' ⟶ T) {g : GtPt D T} {g' : GtPt D T'} (h : GtPt.IsPull k.left g g') :
    GtPt.IsPull k.left (smulPt hG oa a g) (smulPt hG oa a g') := by
  obtain ⟨b, v⟩ := (isPull_iff _ _ _).1 h
  refine (isPull_iff _ _ _).2 ⟨by rw [smulPt_b, smulPt_b, b, Category.assoc], fun χ y J hJ => ?_⟩
  rw [smulPt_val hG oa a _ χ hJ, v _ y J hJ, b]
  exact (val_smul oa a g _ χ k hJ).symm.trans (val_corr hJ ((isSmulPt_smulPt hG oa a g).2 _
    (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ) _)

theorem smulPt_add (a : O) {g g' g'' : GtPt D T} (h : g.IsAdd g' g'') :
    (smulPt hG oa a g).IsAdd (smulPt hG oa a g') (smulPt hG oa a g'') := by
  have := oa.onB.hom a
  obtain ⟨b, v⟩ := (isAdd_iff _ _ _).1 h
  refine (isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [smulPt_b, smulPt_b, smulPt_b, b, MonObj.mul_comp]
  · have e₁ := congrArg Additive.ofMul (rosGen_add hG oa a hJ g.b g'.b (cP D _ χ)).2
    have e := v (star a • χ) y J hJ
    rw [cPoint_smul oa] at e
    have e₂ := congrArg Additive.ofMul e
    rw [smulPt_val hG oa a _ χ hJ, smulPt_val hG oa a _ χ hJ, smulPt_val hG oa a _ χ hJ, smulPt_b, smulPt_b, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ + e₂

theorem one_smulPt (g : GtPt D T) : smulPt hG oa 1 g = g :=
  pt_ext (by rw [smulPt_b, oa.onB.map_one, Category.comp_id]) fun χ y J hJ => by
    rw [smulPt_val hG oa _ _ χ hJ, IsRos.val_id hG D.P.isAb D.P.isLB (by rw [star_one, oa.onB.map_one])
      oa.onB.map_one (rosGen_isRos hG oa 1) hJ, star_one, one_smul, _root_.mul_one]

theorem mul_smulPt (a a' : O) (g : GtPt D T) : smulPt hG oa (a * a') g = smulPt hG oa a (smulPt hG oa a' g) := by
  have := oa.onB.hom a'
  have := oa.onB.hom (star a)
  refine pt_ext (by rw [smulPt_b, smulPt_b, smulPt_b, oa.onB.map_mul, Category.assoc]) fun χ y J hJ => ?_
  rw [smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ _ hJ,
    IsRos.val_comp hG D.P.isAb D.P.isLB (by rw [star_mul, oa.onB.map_mul]) (oa.onB.map_mul a a')
      (rosGen_isRos hG oa (a * a')) (rosGen_isRos hG oa a) (rosGen_isRos hG oa a') hJ,
    smulPt_b, cPoint_smul oa, star_mul, mul_smul, _root_.mul_assoc]

theorem add_smulPt (a a' : O) (g : GtPt D T) :
    (smulPt hG oa a g).IsAdd (smulPt hG oa a' g) (smulPt hG oa (a + a') g) := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  refine (isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [smulPt_b, smulPt_b, smulPt_b, oa.onB.map_add]; exact MonObj.comp_mul _ _ _
  · have e₁ := congrArg Additive.ofMul (IsRos.val_sum hG D.P.isAb D.cub
      (by rw [star_add]; exact oa.onB.map_add _ _) (oa.onB.map_add a a')
      (rosGen_isRos hG oa (a + a')) (rosGen_isRos hG oa a) (rosGen_isRos hG oa a') hJ (cP D _ χ) g.b)
    have e := cv_add g hJ (star a • χ) (star a' • χ)
    rw [cPoint_smul oa, cPoint_smul oa, ← add_smul, ← star_add] at e
    have e₂ := congrArg Additive.ofMul e
    rw [smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_b, smulPt_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, th] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ + e₂

def Represents {H : Over (Spec (CommRingCat.of R))} [GrpObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T) : Prop :=
  (∀ (T' T : Over (Spec (CommRingCat.of R))) (k : T' ⟶ T) (x : T ⟶ H),
    GtPt.IsPull k.left (Φ T x) (Φ T' (k ≫ x))) ∧
  ∀ (T : Over (Spec (CommRingCat.of R))) (x x' : T ⟶ H), GtPt.IsAdd (Φ T x) (Φ T x') (Φ T (x * x'))

include hG in
theorem exists_ringAct {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H]
    {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T} (h : Represents Φ) :
    ∃ ρ : RingAct H O, ∀ (a : O) (T) (x : T ⟶ H), IsSmulPt oa a (Φ T x) (Φ T (x ≫ ρ.act a)) := by
  let act : O → (H ⟶ H) := fun a => (Φ H).symm (smulPt hG oa a (Φ H (𝟙 H)))
  have key : ∀ (a : O) {T} (x : T ⟶ H), Φ T (x ≫ act a) = smulPt hG oa a (Φ T x) := fun a T x => by
    have e₁ := h.1 T H x (act a)
    have e₂ := smulPt_pull hG oa a x (h.1 T H x (𝟙 H))
    rw [Category.comp_id] at e₂
    rw [Equiv.apply_symm_apply] at e₁
    exact isPull_unique e₁ e₂
  have mul : ∀ (a : O) {T} (x x' : T ⟶ H), (x * x') ≫ act a = (x ≫ act a) * (x' ≫ act a) := fun a T x x' => by
    have e₁ := h.2 T (x ≫ act a) (x' ≫ act a)
    rw [key, key] at e₁
    exact (Φ T).injective ((key a _).trans (isAdd_unique (smulPt_add hG oa a (h.2 T x x')) e₁))
  refine ⟨⟨act, fun a => ⟨?_, ?_⟩, ?_, fun a b => ?_, fun a b => ?_⟩, fun a T x => ?_⟩
  · have e := mul a (1 : 𝟙_ _ ⟶ H) 1
    rw [_root_.mul_one] at e
    have e' := mul_eq_left.1 e.symm
    simpa [Hom.one_def] using e'
  · have e := mul a (fst H H) (snd H H)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e
    rw [e]
    congr 1
  · exact (Φ H).injective (by rw [← Category.id_comp (act 1), key, one_smulPt])
  · exact (Φ H).injective (by
      rw [← Category.id_comp (act (a * b)), key, mul_smulPt, key, ← Category.id_comp (act b), key])
  · have e₁ := h.2 H (act a) (act b)
    have k := fun a => (congrArg (Φ H) (Category.id_comp (act a))).symm.trans (key a (𝟙 H))
    rw [k, k] at e₁
    exact (Φ H).injective ((k _).trans (isAdd_unique (add_smulPt hG oa a b _) e₁))
  · rw [key]
    exact isSmulPt_smulPt hG oa a _

end GlobalTheory.TorusModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TwistUnit

open ReciprocityTheory.ChartRestriction.G.H1.SquareUnits TopologicalSpace

section Field

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)

theorem unitAt_square (hsq : SquareSt) (P : PolAV S) (x₁ x₂ : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := hsq S P (Over.mk t) x₁ x₂ (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by
    have := spec_pt_eq q (IsLocalRing.closedPoint K)
    rw [this]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (Over.mk t ⊗ P.A).left)
    ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨SectionArithmetic.pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [SectionArithmetic.sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem unitAt_iter (hsq : SquareSt) (P : PolAV S) (b : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    ∀ n : ℕ, UnitAt P.L ![(translPt P.A (b ^ (n + 2))).left, (snd (Over.mk t) P.A).left,
      (translPt P.A b).left] ![1, (n : ℤ) + 1, -((n : ℤ) + 2)] y
  | 0 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) (unitAt_square t hsq P b b y)
    simp [Fin.sum_univ_succ, pow_two]
    module
  | n + 1 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((unitAt_iter hsq P b y n).mul (unitAt_square t hsq P (b ^ (n + 2)) b y))
    have e : b ^ (n + 2) * b = b ^ (n + 1 + 2) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

end Field

theorem unitAt_pow (hample : AmpleSt) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) (n : ℕ)
    (hn : 4 ≤ n) {Y : Scheme.{0}} (g : Y ⟶ P.A.left) (y : Y) :
    UnitAt P.L (K := Fin 1) (fun _ => g) (fun _ => (n : ℤ)) y := by
  have : IsIso (P.A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso P.A.left.topIso.hom)
  let h : Y ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme := g ≫ inv (P.A.hom ⁻¹ᵁ ⊤).ι
  have hι : h ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = g := by
    show (g ≫ inv (P.A.hom ⁻¹ᵁ ⊤).ι) ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = g
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨hgen, -⟩ := hample _ P n hn
  obtain ⟨M, s, hcov⟩ := hgen ⊤ (isAffineOpen_top _)
  obtain ⟨i, hi⟩ : ∃ i, h y ∈ nonzeroLocus (s i) := Opens.mem_iSup.1 (by rw [hcov]; trivial)
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hi
  refine UnitAt.congr P.isLB (φ := fun _ : Fin n => h ≫ (P.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1)
    (formEq_of_add fun U _ hh => ?_) ⟨SectionArithmetic.pullSec (s i) h, fun J hJ => ?_⟩
  · simp only [hι]
    simp
  · refine (congrArg IsUnit (SectionArithmetic.sval_pullSec (s i) h (𝟙 _) y hJ)).mpr ?_
    rw [Category.id_comp]
    exact SectionArithmetic.isUnit_sval (s i) h y hJ j hj

theorem unitAt_gen {X Y W : Scheme.{0}} {L : LB X} {I : Type} [Fintype I] {φ : I → (W ⟶ X)} {ε : I → ℤ}
    (G : LB.Gen (LB.LinComb L φ ε)) (hG : G.IsGen) (h : Y ⟶ W) (y : Y) :
    UnitAt L (fun i => h ≫ φ i) ε y :=
  ⟨SectionArithmetic.pullSec (Geo.Tor.genSec G hG) h, fun J hJ => by
    rw [SectionArithmetic.sval_pullSec _ h (𝟙 _) y hJ, sval_genSec G hG _ y hJ]
    exact Units.isUnit _⟩

theorem isUnit_sval_of {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (Y ⟶ X)}
    {ε : I → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (hs : ∀ J, Good L (r z) J → IsUnit (sval s (𝟙 Y) (r z) J)) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    IsUnit (sval s r z J) := by
  choose J' hJ' using fun ψ : Y ⟶ X => exists_chart hL (ψ (r z))
  have hG : Good L (r z) J' := hJ'
  have hm := hG.mem φ (𝟙 Y)
  have hu := hs J' hG
  have hu' := (congrArg IsUnit (gs_eq (𝟙 Y) (r z) _ hm (s.f fun i => J' (𝟙 Y ≫ φ i)))).mp hu
  exact SectionArithmetic.isUnit_sval s r z hJ (fun i => J' (𝟙 Y ≫ φ i)) ((Y.mem_basicOpen _ (r z) hm).2 hu')

theorem exists_ratio_local {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {I : Type} [Fintype I] {φ : I → (Spec (CommRingCat.of R) ⟶ X)} {ε : I → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (G : LB.Gen (LB.LinComb L φ ε)) (hG : G.IsGen) :
    ∃ x : Γ(Spec (CommRingCat.of R), ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J),
      Good L z J → sval s r z J = gs r z ⊤ x * (val G r z J).val := by
  obtain ⟨j, hj⟩ := exists_chart_top L hL φ ε
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart L φ j := hj.ge
  refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE le).op).hom
    ((show Γ(Spec (CommRingCat.of R), LB.wchart L φ j) from s.f j) *
      (show Γ(Spec (CommRingCat.of R), LB.wchart L φ j)ˣ from G.s j)⁻¹.val), fun Z r z J hJ => ?_⟩
  have hz : r z ∈ LB.wchart L φ j := le trivial
  rw [gs_res r z le trivial, gs_mul r z _ hz, gs_unit r z _ hz, map_inv]
  have e₁ : sval s r z J = _ := sec_trans s r z (hJ.mem φ r) hz
  have e₂ : val G r z J = _ := gen_trans hG r z (hJ.mem φ r) hz
  rw [e₁, e₂, Units.val_mul]
  have := Units.inv_mul (gm r z (LB.wchart L φ j) (G.s j))
  linear_combination (-((trF φ ε r z (fun k => J (r ≫ φ k)) j).val * gs r z (LB.wchart L φ j) (s.f j))) * this

theorem exists_div_ext (hmul : MulNSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ) (hn : 1 ≤ n)
    {κ : Type} [Field κ] (t : Spec (CommRingCat.of κ) ⟶ S) (c : Over.mk t ⟶ P.A) :
    ∃ (K : Type) (_ : Field K) (g : κ →+* K) (b : Spec (CommRingCat.of K) ⟶ P.A.left),
      b ≫ (mulA P.A n).left = Spec.map (CommRingCat.ofHom g) ≫ c.left := by
  obtain ⟨-, -, hsurj, -, -⟩ := hmul S P n hn
  let W := pullback (mulA P.A n).left c.left
  obtain ⟨w, -⟩ := Surjective.surj (f := pullback.snd (mulA P.A n).left c.left) (IsLocalRing.closedPoint κ)
  obtain ⟨g, hg⟩ := Spec.map_surjective (R := CommRingCat.of κ) (S := W.residueField w)
    (W.fromSpecResidueField w ≫ pullback.snd (mulA P.A n).left c.left)
  refine ⟨W.residueField w, inferInstance, g.hom, W.fromSpecResidueField w ≫ pullback.fst (mulA P.A n).left c.left, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hg]
  rfl

theorem exists_unit_secB (hLaws : Laws) (hTW : TwistBCSpanStatement) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (k : ℕ) (hk : 4 ≤ k) (χ : D.X)
    {O : Type} [CommRing O] [IsLocalRing O] (f : R →+* O) [IsLocalHom f]
    (m : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ D.P.A) :
    ∃ (σ : D.SecB k χ) (K : Type) (_ : Field K) (g : O →+* K), IsLocalHom g ∧
      ∃ (z : Spec (CommRingCat.of K)) (J : (Spec (CommRingCat.of K) ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J ∧
        IsUnit (sval σ (Spec.map (CommRingCat.ofHom g) ≫ m.left) z J) := by
  have hL := D.P.isLB
  obtain ⟨K, _, g₀, b₀, hb₀⟩ := exists_div_ext hLaws.mulN D.P k (by omega)
    (Spec.map (CommRingCat.ofHom ((residue O).comp f))) (SectionScalarValuation.cQ D _ χ)
  let g : O →+* K := g₀.comp (residue O)
  have hg : IsLocalHom g := inferInstance
  have hgf : IsLocalHom (g.comp f) := inferInstance
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom (g.comp f)))
  let τ₀ : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom ((residue O).comp f))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom g₀)) (by
      show Spec.map (CommRingCat.ofHom g₀) ≫ Spec.map (CommRingCat.ofHom ((residue O).comp f)) =
        Spec.map (CommRingCat.ofHom (g.comp f))
      rw [← Spec.map_comp]; rfl)
  let τ : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom f)) :=
    Over.homMk (Spec.map (CommRingCat.ofHom g)) (by
      show Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom (g.comp f))
      rw [← Spec.map_comp]; rfl)
  have hb₁ : b₀ ≫ (mulA D.P.A k).left = (SectionScalarValuation.cQ D T χ).left :=
    hb₀.trans (congrArg (fun q => q.left) (SectionScalarValuation.comp_cQ D τ₀ χ))
  have hw : b₀ ≫ D.P.A.hom = T.hom := by
    rw [← Over.w (mulA D.P.A k), ← Category.assoc, hb₁, Over.w]
  let b : T ⟶ D.P.A := Over.homMk b₀ hw
  have hb : b ^ k = SectionScalarValuation.cQ D T χ := by
    have e : b ^ k = b ≫ mulA D.P.A k :=
      (congrArg (· ^ k) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 D.P.A) k b).symm
    rw [e]
    exact Over.OverMorphism.ext hb₁
  let ρ : T ⟶ T ⊗ D.P.A := lift (𝟙 T) (τ ≫ m)
  let z : Spec (CommRingCat.of K) := closedPoint K
  obtain ⟨G, hG⟩ := exists_gen_of_local D.P.L hL (K := Fin 2)
    ![(SectionScalarValuation.cQ D T χ).left, (1 : T ⟶ D.P.A).left] ![-1, 1]
  have u₁ := unitAt_iter (Spec.map (CommRingCat.ofHom (g.comp f))) hLaws.square D.P b (ρ.left z) (k - 2)
  have u₂ := unitAt_pow hLaws.ample D.P k hk (translPt D.P.A b).left (ρ.left z)
  have u₃ := unitAt_gen G hG (fst T D.P.A).left (ρ.left z)
  have hk2 : k - 2 + 2 = k := by omega
  have hk2' : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
  rw [hk2, hb, hk2'] at u₁
  have q₁ : translPt D.P.A (SectionScalarValuation.cQ D T χ) = snd T D.P.A * SectionScalarValuation.cQ D (T ⊗ D.P.A) χ := by
    rw [mul_comm, ← SectionScalarValuation.comp_cQ D (fst T D.P.A)]; rfl
  have q₂ : (fst T D.P.A).left ≫ (SectionScalarValuation.cQ D T χ).left = (SectionScalarValuation.cQ D (T ⊗ D.P.A) χ).left :=
    congrArg (fun q => q.left) (SectionScalarValuation.comp_cQ D (fst T D.P.A) χ)
  have q₃ : (fst T D.P.A).left ≫ (1 : T ⟶ D.P.A).left = (1 : T ⊗ D.P.A ⟶ D.P.A).left :=
    congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (fst T D.P.A))
  obtain ⟨s', hs'⟩ : UnitAt D.P.L (fun i => (snd T D.P.A).left ≫ DegPre.famφB D χ i) (DegPre.famε k) (ρ.left z) := by
    refine UnitAt.congr hL (fun U _ h => ?_) ((u₁.mul u₂).mul u₃)
    refine Eq.trans ?_ (SectionScalarValuation.prod_famB D (snd T D.P.A) χ k h).symm
    rw [← q₁, ← q₂, ← q₃, Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_three, Fin.prod_univ_one,
      Fin.prod_univ_two]
    show h (translPt D.P.A (SectionScalarValuation.cQ D T χ)).left ^ (1 : ℤ) * h (snd T D.P.A).left ^ ((k : ℤ) - 2 + 1) *
      h (translPt D.P.A b).left ^ (-((k : ℤ) - 2 + 2)) * h (translPt D.P.A b).left ^ (k : ℤ) *
      (h ((fst T D.P.A).left ≫ (SectionScalarValuation.cQ D T χ).left) ^ (-1 : ℤ) *
        h ((fst T D.P.A).left ≫ (1 : T ⟶ D.P.A).left) ^ (1 : ℤ)) = _
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  choose J hJ using fun ψ : Spec (CommRingCat.of K) ⟶ D.P.A.left => exists_chart hL (ψ z)
  have hJ' : Good D.P.L z J := hJ
  have hu := isUnit_sval_of hL s' ρ.left z hs' J hJ'
  obtain ⟨n, r, σ, hσ⟩ := hTW R D k (by omega) χ K (g.comp f) hgf s'
  have e := SectionScalarValuation.sval_lin (fun l => (fst T D.P.A).left.appTop.hom (r l))
      (fun l => DVR.pullSec D.P.L _ _ (σ l) (snd T D.P.A).left) (fun j => hσ j) ρ.left z hJ'
  rw [e] at hu
  obtain ⟨l, -, hl⟩ := IsLocalRing.exists_of_isUnit_sum hu
  refine ⟨σ l, K, inferInstance, g, hg, z, J, hJ', ?_⟩
  have hl' := isUnit_of_mul_isUnit_right hl
  rw [SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ', ← Over.comp_left, lift_snd] at hl'
  exact hl'

end TwistUnit

open TwistUnit in
theorem exists_integral_section_unit_at : Laws → TwistBCSpanStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (k : ℕ), 4 ≤ k → ∀ (χ : D.toPre.X) (m : TWM.TO hϖ hv ⟶ D.toPre.P.A), ∃ s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)), VGe D F v k χ s 0 ∧ (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m).left ≫ DegPre.famφB D.toPre (χ) i) (DegPre.famε (k))), G₀.IsGen ∧ ∃ x : F, v x = ((0 : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) := by
  intro hLaws hTW V _ _ _ ϖ hϖ D Q _ F _ _ _ v hv k hk χ m
  have hL := D.toPre.P.isLB
  obtain ⟨σ, K, _, g, hg, z₀, J₀, hJ₀, hu⟩ := exists_unit_secB hLaws hTW D.toPre k hk χ (TWO.fO v hϖ hv) m
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F χ) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  obtain ⟨s, hs⟩ := exists_sec hL hformF (SectionArithmetic.pullSec σ (DegPre.prB D.toPre F).left)
  have hs' : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = sval σ (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ =>
    (hs Z ρ z J hJ).trans (SectionArithmetic.sval_pullSec _ _ ρ z hJ)
  obtain ⟨G₀, hG₀⟩ := exists_gen_of_local (V := TWO.Ov v) D.toPre.P.L hL
    (fun i => m.left ≫ DegPre.famφB D.toPre χ i) (DegPre.famε k)
  obtain ⟨x₀, hx₀⟩ := exists_ratio_local (R := TWO.Ov v) hL (SectionArithmetic.pullSec σ m.left) G₀ hG₀
  have key : ∀ {E : Type} [CommRing E] (φ : TWO.Ov v →+* E) (z : Spec (CommRingCat.of E)),
      gs (Spec.map (CommRingCat.ofHom φ)) z ⊤ x₀ = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
        (φ ((Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom x₀))) := fun φ z => by
    have e := gs_pull (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) z ⊤ trivial x₀
    rw [Category.id_comp] at e
    exact e.symm.trans (congrArg (gs (𝟙 _) z ⊤) (TWM.appTop_specMap (CommRingCat.ofHom φ) x₀))
  have hx₀u : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom x₀) := by
    have e := hx₀ _ (Spec.map (CommRingCat.ofHom g)) z₀ J₀ hJ₀
    rw [SectionArithmetic.sval_pullSec _ _ _ z₀ hJ₀] at e
    have h₁ := isUnit_of_mul_isUnit_left ((congrArg IsUnit e).mp hu)
    rw [key] at h₁
    refine isUnit_of_map_unit g _ (IsUnit.mk0 _ fun h0 => ?_)
    rw [h0, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero] at h₁
    exact not_isUnit_zero h₁
  refine ⟨s, ⟨1, fun _ => 1, fun _ => σ, fun _ => s, fun _ => ?_, fun _ => ?_, fun j => ?_⟩, G₀, hG₀,
    TWM.ιr (v := v) x₀, ?_, fun z J hJ => ?_⟩
  · exact SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hs' _ (𝟙 _) y J hJ).symm
  · rw [AddValuation.map_one]; exact le_rfl
  · rw [Fin.sum_univ_one, DVR.constBF_eq, map_one]
    simp [resTop]
  · exact TWO.v_unit v hx₀u.unit
  · rw [hs' _ _ z J hJ, ← Over.comp_left, lift_snd, Over.comp_left, ← SectionArithmetic.sval_pullSec σ m.left _ z hJ]
    exact (hx₀ _ _ z J hJ).trans (congrArg (· * _) (key (algebraMap (TWO.Ov v) F) z))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupBesselGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupBesselGrowth
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomMass

theorem integrand_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {d : ℝ} (hd : 0 ≤ d) (v : Wp) :
    ENNReal.ofReal (1 * (d * ‖v‖ ^ 2)) = ((‖((Real.sqrt d : ℝ) : ℂ) • v‖₊ : ENNReal)) ^ 2 := by
  rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hd, one_mul]

theorem mom_mass : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν ≤ q0 → (∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (‖w‖ ^ 2)) ∧ (NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧ ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν
  obtain ⟨hNum, hFam, hSide, hSF⟩ := hS
  obtain ⟨⟨-, -, -, -, hOK⟩, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  obtain ⟨-, -, hgap, -⟩ := hfam ν hν
  have hDS := hFam ν hν
  obtain ⟨hBe, hpos, hdeg⟩ := hSF ν hν
  have key : NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧
      ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq =
        ENNReal.ofReal (‖w‖ ^ 2) := by
    intro hnz
    have hiso := GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH k r _ _ (h / 2) (R ν) Wp z π u μW μN μG νq (l ν) (dg ν) hDS hgap hOK hSide hBe
      hdeg hnz
    refine ⟨hiso, fun w hw => ?_⟩
    rw [← hiso.2 w hw]
    unfold PI.BesselPeriodGGP.l2SG
    exact lintegral_congr fun x => integrand_eq hpos.le _
  refine ⟨fun w hw => ?_, key⟩
  by_cases hnz : NzOn (R ν) (l ν)
  · exact ((key hnz).2 w hw).le
  · have hz : ∀ v ∈ (R ν).sm, l ν v = 0 := by
      intro v hv
      by_contra hne
      exact hnz ⟨v, hv, hne⟩
    obtain ⟨-, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r _ _ (R ν) hDS
    obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hSide
    obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
    have : ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0 := by
      rw [← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hz _ (hsm _ hx w hw)]
      simp
    rw [this]
    exact bot_le

end GlobalTheory.MomMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupBesselGrowthStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_functional_l2_bound_and_isometry : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν ≤ q0 → (∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (‖w‖ ^ 2)) ∧ (NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧ ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)) := by
  first | exact @GlobalTheory.MomMass.mom_mass | exact GlobalTheory.MomMass.mom_mass | (intros; apply GlobalTheory.MomMass.mom_mass <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsInnerSelfEqNormSq
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wp] in
theorem hsInner_self_eq_normSq (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K]
  simp

omit [FiniteDimensional ℂ Wp] in
theorem hsInner_zero_zero : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
  simp [P.Topx1.hsInner_eq]

theorem levelForm_top_diag (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (a : C.LPt) :
    p.RR H (P.r + 1) w a a = Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w a a := by
  by_cases hg : D.IsLocPt a (P.r + 1) ∧ 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r a
  · unfold KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hg.1, hg.1⟩, dite_eq_right (by omega), if_pos rfl]
    split_ifs with hw
    · subst hw
      exact (Formalism.FourierDecayAlt.P.top_of_empty Formalism.FourierDecayAlt.P.vector_valued_types Wp Wq P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H a a p.hP p.hF
        hg.1 hg.1 hg.2 hg.2).symm
    · rfl
  · have hV : ∀ F, D.vecV p.T.base p.ν' p.m₀ F a = 0 := fun F => by
      unfold D.vecV
      rw [dite_eq_right hg]
    have ht : Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w a a = 0 := by
      simp only [Top.topOf, hV, ContinuousLinearMap.comp_zero, hsInner_zero_zero, mul_zero,
        Finset.sum_const_zero]
    rw [ht]
    unfold KB.Pl.RR D.RRplace
    split_ifs with h1 h2 h3 h4
    · omega
    · rw [hV, hsInner_zero_zero]
    · exact ht
    · rfl
    · rfl

end

theorem Ew_eq_norm_tv_sq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = ‖tv p H w c‖ ^ 2 := by
  intro Wp Wq _ _ _ _ _ _ P p H w c
  have h1 : TBB.normC (fun _ => 1) w = 1 := by simp [TBB.normC]
  unfold TBB.Ew TBB.NP
  rw [levelForm_top_diag, h1, div_one, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  unfold Top.topOf
  simp only [hsInner_self_eq_normSq, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  simp only [tv, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, TBB.TTp, KB.Pl.V]
  ring

end GlobalTheory.TopVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMul
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaMul

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem alg {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (C : IsCub θ) (k : ℕ) (a B b x : A)
    (g₁ g g₂ gs gy w w₁ : U) (h₁ : g₂ * θ a b B = g * g₁) (h₂ : gs * θ a (B ^ k) b = g * gy) :
    hv θ k a B (x * b) * (g₁ * w₁) * (hv θ k (a * B ^ k) b x * (gs * w)) =
      hv θ k a (b * B) x * (g₂ * (cubN θ k 1 B b * gy * (w * w₁))) := by
  have e₁ := UUA.hv_comp C k a B b x
  have e₂ := C.N_split k a B b
  have e₃ : hv θ k a B b = cubN θ k a B b * (θ a b B)⁻¹ := rfl
  rw [mul_comm b B]
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e₃
  have b₁ := congrArg Additive.ofMul h₁
  have b₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ b₁ b₂ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃ - b₁ + b₂

theorem exists_gen_mul {k : ℕ} (p p₁ : QkPt D F k) (b₂ : TF (R := R) F ⟶ D.P.A) (hb : b₂ = p.g.b * p₁.g.b)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w₁ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₁.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw₁ : w₁.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b₂) (DegPre.lineε k)), w₂.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) F) (z : T.left) (J), Good D.P.L z J →
        val w₂ σ.left z J = cubN (th D z J) k 1 (σ ≫ p₁.g.b) (σ ≫ p.g.b) * val (p.g.s p₁.y) σ.left z J *
          (val w σ.left z J * val w₁ σ.left z J) := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (1 : TF (R := R) F ⟶ D.P.A) p₁.g.b p.g.b k
  obtain ⟨w₂, hw₂, v₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b₂) (ε' := DegPre.lineε k) (fun U _ h => by
      have l : ∀ b : TF (R := R) F ⟶ D.P.A, ∏ i, h (DegPre.lineφ D F b i) ^ DegPre.lineε k i =
          h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) := fun b => by
        rw [Fin.prod_univ_two]; rfl
      have g : ∏ i, h (DegPre.gtφ D F p.g.b p₁.y i) ^ DegPre.gtε i =
          h (p₁.g.b ^ k * p.g.b).left ^ (-1 : ℤ) * h (p₁.g.b ^ k).left ^ (1 : ℤ) * h p.g.b.left ^ (1 : ℤ) *
            h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) := by
        rw [Fin.prod_univ_four, ← cPoint_y p₁]; rfl
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ Fin 4) (K' := Fin 2 ⊕ Fin 2) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := Fin 4) (U := U) _ rfl g)
        (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (l _) (l _))) (Eq.trans ?_ (l b₂).symm)
      rw [hb, mul_comm p.g.b p₁.g.b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (p.g.s p₁.y)) (LB.mulGen D.P.L _ _ _ _ w w₁))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (p.g.isGen _)) (mulGen_isGen _ _ _ _ _ _ _ hw hw₁))
  refine ⟨w₂, hw₂, fun T σ z J hJ => ?_⟩
  rw [v₂ _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, vN T σ z J hJ, MonObj.comp_one]

theorem phi_mul_core (hG : GlobalFnsSt) {k : ℕ} (p p₁ p₂ : QkPt D F k) (hy : p₂.y = p.y + p₁.y)
    (hg : p.g.IsAdd p₁.g p₂.g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w₁ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₁.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw₁ : w₁.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₂.g.b) (DegPre.lineε k)), w₂.IsGen ∧
      ∀ s t t' : Fam D F k, PhiRel D F k p₁ w₁ s t → PhiRel D F k p w t t' → PhiRel D F k p₂ w₂ s t' := by
  have hb : p₂.g.b = p.g.b * p₁.g.b := hg.1
  obtain ⟨w₂, hw₂, v₂⟩ := exists_gen_mul p p₁ p₂.g.b hb w w₁ hw hw₁
  refine ⟨w₂, hw₂, fun s t t' h₁ h => ?_⟩
  rw [phiRel_iff hG _ _ hw₁] at h₁
  rw [phiRel_iff hG _ _ hw] at h
  rw [phiRel_iff hG _ _ hw₂]
  intro α β hαβ T ρ z J hJ
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have e := h (α + p₁.y) β (by rw [← hαβ, hy]; abel) T ρ z J hJ
  have e₁ := h₁ α (α + p₁.y) rfl T (ρ ≫ DegPre.trPt D F p.g.b) z J hJ
  have hf : (ρ ≫ DegPre.trPt D F p.g.b) ≫ fst (TF (R := R) F) D.P.A = ρ ≫ fst _ _ := by
    rw [Category.assoc, tr_fst]
  have hp : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, ← Category.assoc]
  have ht : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.trPt D F p₁.g.b = ρ ≫ DegPre.trPt D F p₂.g.b := by
    rw [Category.assoc, trPt_mul, hb]
  have hy₁ : cP D T p₁.y = ((ρ ≫ fst _ _) ≫ p₁.g.b) ^ k := by
    rw [← comp_cP D (ρ ≫ fst (TF (R := R) F) D.P.A), cPoint_y]; exact map_pow (preHom (ρ ≫ fst (TF (R := R) F) D.P.A)) _ _
  have u₁ : uVal D F k α p₁.g.b (ρ ≫ DegPre.trPt D F p.g.b) z J =
      hv (th D z J) k (cP D T α) ((ρ ≫ fst _ _) ≫ p₁.g.b) ((ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ p.g.b)) := by
    rw [uVal, hp, ← Category.assoc (ρ ≫ DegPre.trPt D F p.g.b), hf]; rfl
  have u₂ : uVal D F k (α + p₁.y) p.g.b ρ z J =
      hv (th D z J) k (cP D T α * ((ρ ≫ fst _ _) ≫ p₁.g.b) ^ k) ((ρ ≫ fst _ _) ≫ p.g.b) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, cPoint_add, hy₁, ← Category.assoc]; rfl
  have u₃ : uVal D F k α p₂.g.b ρ z J =
      hv (th D z J) k (cP D T α) (((ρ ≫ fst _ _) ≫ p.g.b) * ((ρ ≫ fst _ _) ≫ p₁.g.b)) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, ← Category.assoc, hb, MonObj.comp_mul]; rfl
  have g₁ : val (p₂.g.s α) (ρ ≫ fst _ _).left z J *
      th D z J (cP D T α) ((ρ ≫ fst _ _) ≫ p.g.b) ((ρ ≫ fst _ _) ≫ p₁.g.b) =
      val (p.g.s α) (ρ ≫ fst _ _).left z J * val (p₁.g.s α) (ρ ≫ fst _ _).left z J := by
    have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hg.2 α) (ρ ≫ fst (TF (R := R) F) D.P.A).left).trans
      (val_mul hJ _ _ _))
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
    refine Eq.trans ?_ (val_cub D.cub (ρ ≫ fst (TF (R := R) F) D.P.A) hJ (cP D _ α) p.g.b p₁.g.b).symm
    rw [comp_cP]
  have g₂ := gt_mul (ρ ≫ fst (TF (R := R) F) D.P.A) hJ p.g α p₁.y
  rw [hy₁] at g₂
  rw [ht, hf, u₁, val_mul hJ] at e₁
  rw [e₁, u₂, val_mul hJ, _root_.mul_assoc, ← Units.val_mul, alg C k _ _ _ _ _ _ _ _ _ _ _ g₁ g₂] at e
  rw [e, u₃, val_mul hJ, v₂ T _ z J hJ]

end GlobalTheory.ThetaMul

namespace GlobalTheory

theorem phi_mul : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p₁ p₂ : QkPt D.toPre F k, p₂.y = p.y + p₁.y → p.g.IsAdd p₁.g p₂.g → ∀ (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε k))), w.IsGen → w₁.IsGen → ∃ w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε k)), w₂.IsGen ∧ ∀ s t t' : Fam D.toPre F k, PhiRel D.toPre F k p₁ w₁ s t → PhiRel D.toPre F k p w t t' → PhiRel D.toPre F k p₂ w₂ s t' := by
  intro hL V _ _ _ D F _ _ k _ p p₁ p₂ hy hg w w₁ hw hw₁
  exact ThetaMul.phi_mul_core hL.globalFns p p₁ p₂ hy hg w w₁ hw hw₁

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitSpecOfIsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FormalPoint

namespace GlobalTheory.AdicColimit

theorem _root_.GlobalTheory.AdicColimit.isAdicColimit_spec_of_isLocalRing (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A]
    [IsLocalRing A] (φ : R →+* A) (hA : IsAdicComplete (I.map φ) A) :
    _root_.GlobalTheory.AdicColimit.IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  have hthick : ∀ e : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1) = _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e := by
    intro e
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans _root_.ReciprocityTheory.ChartRestriction.G.Out.thick
    rw [← Spec.map_comp]
    rfl
  have hPV : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ = Spec.map (CommRingCat.ofHom φ) := rfl
  have hC : ∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) =
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) := fun e => rfl
  have hD_fst : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) =
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) := by
    intro e; exact pullback.lift_fst _ _ _
  have hD_snd : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e := by
    intro e
    exact pullback.lift_snd _ _ _
  have hcond : ∀ e, pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫
      Spec.map (CommRingCat.ofHom φ) =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e :=
    fun e => pullback.condition
  have hq : ∀ e, _root_.GlobalTheory.FormalPoint.levelMap I φ e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e =
      _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) ≫ Spec.map (CommRingCat.ofHom φ) := fun e => by
    rw [_root_.GlobalTheory.FormalPoint.levelMap_thick, hPV]
  obtain ⟨s, hs_fst, hs_snd⟩ : ∃ s : ∀ e : ℕ, Spec (CommRingCat.of (A ⧸ I.map φ ^ (e + 1))) ⟶
      pullback (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e),
      (∀ e, s e ≫ pullback.fst _ _ = _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1)) ∧
      (∀ e, s e ≫ pullback.snd _ _ = _root_.GlobalTheory.FormalPoint.levelMap I φ e) :=
    ⟨fun e => pullback.lift _ _ (hq e).symm, fun e => pullback.lift_fst _ _ _,
      fun e => pullback.lift_snd _ _ _⟩
  have hsec : ∀ e, ∃ l, l ≫ s e = 𝟙 _ := by
    intro e
    obtain ⟨l, hl⟩ := _root_.GlobalTheory.FormalPoint.exists_factor_level I φ
      (pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e))
      (pullback.snd _ _) (by rw [hPV]; exact hcond e)
    refine ⟨l, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hs_fst, Category.id_comp, hl]
    · rw [← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e), Category.assoc, Category.assoc, ← Category.assoc (s e), hs_snd, hq,
        ← Category.assoc, hl, Category.id_comp, hcond]
  intro X f hf
  have hfam : _root_.GlobalTheory.IsAdicFamily (I.map φ) (fun e => s e ≫ f e) := by
    intro n
    have hmap : _root_.GlobalTheory.adicLevelMap (I.map φ) (by omega : n + 1 ≤ n + 1 + 1) ≫ s (n + 1) =
        s n ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
      apply pullback.hom_ext
      · rw [Category.assoc, hs_fst, _root_.GlobalTheory.adicLevelMap_ι, Category.assoc, hD_fst, hs_fst]
      · rw [← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (n + 1))]
        simp only [Category.assoc]
        rw [← Category.assoc (s (n + 1)), hs_snd, hq, _root_.GlobalTheory.adicLevelMap_ι_assoc, ← Category.assoc (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ)))), hD_snd,
          Category.assoc, hthick, ← Category.assoc, hs_snd, hq]
    show _root_.GlobalTheory.adicLevelMap (I.map φ) _ ≫ s (n + 1) ≫ f (n + 1) = s n ≫ f n
    rw [← Category.assoc, hmap, Category.assoc, hf]
  haveI := hA
  obtain ⟨g, hg, hgu⟩ := _root_.GlobalTheory.existsUnique_of_isAdicFamily hfam
  have key : ∀ y : Spec (CommRingCat.of A) ⟶ X,
      (∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫ y = f e) ↔
      (∀ n, _root_.GlobalTheory.adicLevelι (I.map φ) (n + 1) ≫ y = s n ≫ f n) := by
    intro y
    constructor
    · intro hy n
      rw [← hs_fst, Category.assoc, ← hC, hy]
    · intro hy e
      obtain ⟨l, hl⟩ := hsec e
      have h1 : _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) =
          l ≫ _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) := by
        rw [← hs_fst, ← Category.assoc, hl, Category.id_comp, hC]
      rw [h1, Category.assoc, hy, ← Category.assoc, hl]
      exact Category.id_comp _
  exact ⟨g, (key g).2 hg, fun y hy => hgu y ((key y).1 hy)⟩

end GlobalTheory.AdicColimit
end
