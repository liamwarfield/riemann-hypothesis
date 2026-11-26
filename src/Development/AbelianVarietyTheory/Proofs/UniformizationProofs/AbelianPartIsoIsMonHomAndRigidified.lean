module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace AbelianPartIso

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem isMonHom_of_comp {S : Scheme.{0}} {G B B' : Over S} [GrpObj G] [GrpObj B] [GrpObj B']
    (q' : G ⟶ B') (q : G ⟶ B) (β : B' ⟶ B) [IsMonHom q'] [IsMonHom q] [Flat q'.left]
    [Surjective q'.left] (hβ : q' ≫ β = q) : IsMonHom β := by
  refine ⟨?_, ?_⟩
  · rw [← IsMonHom.one_hom q', Category.assoc, hβ, IsMonHom.one_hom]
  · have := FlatQuotient.epi_tensorHom q' q'
    rw [← cancel_epi (q' ⊗ₘ q'), ← IsMonHom.mul_hom_assoc, hβ, tensorHom_comp_tensorHom_assoc, hβ,
      IsMonHom.mul_hom]

theorem hom_eq_of_map_eq {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom]
    [GeometricallyConnected H.hom] {Y : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom]
    (f g : H ⟶ Y)
    (h : ∀ n, (Over.pullback (thick R I n)).map f = (Over.pullback (thick R I n)).map g) : f = g := by
  refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI H).2 Y f g fun n => ?_
  have k : ∀ f : H ⟶ Y, ((Over.pullback (thick R I n)).map f).left ≫ pullback.fst Y.hom (thick R I n) =
      pullback.fst H.hom (thick R I n) ≫ f.left := fun f => pullback.lift_fst _ _ _
  exact (k f).symm.trans ((congrArg (fun φ => φ.left ≫ pullback.fst Y.hom (thick R I n)) (h n)).trans (k g))

theorem isMonHom_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {B B' : Over (Spec (CommRingCat.of R))} [GrpObj B] [GrpObj B']
    (hB : IsAbelianScheme B) (hB' : IsAbelianScheme B') (f : B' ⟶ B)
    (h : ∀ n, IsMonHom ((Over.pullback (thick R I n)).map f)) : IsMonHom f := by
  have := hB.proper
  have := hB'.smooth
  have := hB'.geomConnected
  refine ⟨?_, ?_⟩
  · have : Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (Smooth (𝟙 _))
    have : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of R)))).hom :=
      inferInstanceAs (GeometricallyConnected (𝟙 _))
    refine hom_eq_of_map_eq hI _ _ _ fun n => ?_
    have e := (h n).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi, ← Functor.map_comp] at e
    exact e
  · have : Smooth (B' ⊗ B').hom := inferInstanceAs (Smooth (pullback.fst B'.hom B'.hom ≫ B'.hom))
    have : GeometricallyConnected (B' ⊗ B').hom := by
      change GeometricallyConnected (pullback.fst B'.hom B'.hom ≫ B'.hom)
      exact GeometricallyConnected.comp _ _
    refine hom_eq_of_map_eq hI _ _ _ fun n => ?_
    have e := (h n).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
      cancel_epi, ← Functor.map_comp, ← Functor.map_comp] at e
    exact e

theorem fn_eq_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤)
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of R), W))
    (h : ∀ (e : ℕ) (z), gs (thick R I e) z W a = gs (thick R I e) z W b) : a = b := by
  subst hW
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  apply hinj
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing I hI, Ideal.mem_iInf]
  intro e
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ?_)
  have key : ((thick R I e).app ⊤).hom a = ((thick R I e).app ⊤).hom b := by
    refine fn_ext fun z hz => ?_
    rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp]
    exact h e z
  have nat := fun x => congrArg (fun φ => φ.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  exact (nat a).symm.trans ((congrArg _ key).trans (nat b))

theorem pmaps_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB)
    (hL' : L'.IsLB) {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (hw : w.IsGen)
    (s' : Spec (CommRingCat.of R) ⟶ X') (s : Spec (CommRingCat.of R) ⟶ X) (hs : s' ≫ F = s)
    (a : LB.Gen (L'.pull s')) (ha : a.IsGen) (t : LB.Gen (L.pull s)) (ht : t.IsGen)
    (h : ∀ (e : ℕ) (z) (p : L.ι) (q : L'.ι), (thick R I e ≫ s) z ∈ L.U p →
      (thick R I e ≫ s') z ∈ L'.U q →
      gm (thick R I e) z ((L.pull s).U (fun _ => p)) (t.s (fun _ => p)) =
        gw w (thick R I e ≫ s') z p q *
          gm (thick R I e) z ((L'.pull s').U (fun _ => q)) (a.s (fun _ => q))) :
    PMaps w (K := PUnit) (fun _ => s') (fun _ => s) (fun _ => 1) a t (𝟙 _) := by
  subst hs
  obtain ⟨p₀, hp₀⟩ := exists_chart hL ((s' ≫ F) (IsLocalRing.closedPoint R))
  obtain ⟨q₀, hq₀⟩ := exists_chart hL' (s' (IsLocalRing.closedPoint R))
  have hp : ∀ x, (s' ≫ F) x ∈ L.U p₀ := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := R) x).map (s' ≫ F).continuous).mem_open
      (L.U p₀).isOpen hp₀
  have hq : ∀ x, s' x ∈ L'.U q₀ := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := R) x).map s'.continuous).mem_open
      (L'.U q₀).isOpen hq₀
  have l₁ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (L.pull (s' ≫ F)).U (fun _ => p₀) :=
    fun x _ => mem_pull.2 (hp x)
  have l₂ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (L'.pull s').U (fun _ => q₀) :=
    fun x _ => mem_pull.2 (hq x)
  have l₃ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      s' ⁻¹ᵁ ((L.pull F).U (fun _ => p₀) ⊓ L'.U q₀) :=
    fun x _ => ⟨mem_pull.2 (hp x), hq x⟩
  have ev₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z),
      gm r z ⊤ (res l₁ (t.s (fun _ => p₀))) =
        gm r z ((L.pull (s' ≫ F)).U (fun _ => p₀)) (t.s (fun _ => p₀)) :=
    fun Z r z => gm_res r z l₁ trivial _
  have ev₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z),
      gm r z ⊤ (res l₃ (pullU s' _ (w.s (fun _ => p₀, q₀))) * res l₂ (a.s (fun _ => q₀))) =
        gw w (r ≫ s') z p₀ q₀ * gm r z ((L'.pull s').U (fun _ => q₀)) (a.s (fun _ => q₀)) :=
    fun Z r z => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z l₃ trivial _).trans (gm_pull r s' z _ (l₃ (Set.mem_univ (r z))) _))
      (gm_res r z l₂ trivial _))
  have key : res l₁ (t.s (fun _ => p₀)) =
      res l₃ (pullU s' _ (w.s (fun _ => p₀, q₀))) * res l₂ (a.s (fun _ => q₀)) := by
    refine Units.ext (fn_eq_of_thickenings hI ⊤ rfl _ _ fun e z => ?_)
    rw [gs_unit _ z ⊤ trivial, gs_unit _ z ⊤ trivial, ev₁, ev₂, h e z p₀ q₀ (hp _) (hq _)]
  intro Z r z p q hpz hqz
  have E := (ev₁ Z r z).symm.trans ((congrArg (gm r z ⊤) key).trans (ev₂ Z r z))
  have a₁ := gen_trans ht r z (j := p) (j' := fun _ => p₀) (Set.mem_iInter.2 hpz) (l₁ (Set.mem_univ _))
  have a₂ := gen_trans ha r z (j := q) (j' := fun _ => q₀) (Set.mem_iInter.2 hqz) (l₂ (Set.mem_univ _))
  have a₃ := (isGen_iff w).1 hw Z (r ≫ s') z (p PUnit.unit) p₀ (q PUnit.unit) q₀ (hpz _) (hp _)
    (hqz _) (hq _)
  rw [Category.comp_id, a₁, a₂, Fintype.prod_unique, zpow_one, a₃]
  refine (congrArg _ E).trans ?_
  simp only [trF, Fintype.prod_unique, zpow_one, Category.assoc, PUnit.default_eq_unit]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end AbelianPartIso


open AbelianPartIso ReciprocityTheory.ChartRestriction.G.DVR in
theorem abelianPartIso_isMonHom_and_rigidified : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) → (IsMonHom Φ.hom ∧ Geo.Tor.PMaps w (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D'.toPre.rig D.toPre.rig (𝟙 _)) := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' wL he hwL hrig Φ w ⟨hw, H⟩
  obtain ⟨_, -, -, _⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  have hI' : I ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.1 (h.ge.trans (hI.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).le)))
  have hΦ : IsMonHom Φ.hom := by
    refine isMonHom_of_thickenings hI D.toPre.P.isAb D'.toPre.P.isAb Φ.hom fun e => ?_
    have := (U.gt e).q_hom
    have := (U'.gt e).q_hom
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    refine isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
    refine pullback.hom_ext ?_ ?_
    · have k : ((Over.pullback (thick R I e)).map Φ.hom).left ≫
          pullback.fst D.toPre.P.A.hom (thick R I e) =
          pullback.fst D'.toPre.P.A.hom (thick R I e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
      exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
        ((Category.assoc _ _ _).symm.trans (H e).1))
    · exact (Over.w _).trans (Over.w (U.gt e).q).symm
  refine ⟨hΦ, pmaps_of_thickenings hI' D.toPre.P.isLB D'.toPre.P.isLB w hw _ _
    (congrArg Over.Hom.left hΦ.one_hom) _ D'.toPre.rig_gen _ D.toPre.rig_gen
    fun e z p q hp hq => ?_⟩
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart U.LG.isLB ((UnitValue.thU R I e ≫ eSec G) z)
  obtain ⟨j', hj'⟩ := Geo.Tor.exists_chart U'.LG.isLB ((UnitValue.thU R I e ≫ eSec G) z)
  have e₁ := UnitValue.wv_rig U e z p j hp hj
  have e₂ := UnitValue.wv_rig U' e z q j' hq hj'
  have e₃ := (Geo.Tor.maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (𝟙 _) _
    (rigPull_le (𝟙 G.left) (𝟙 _) he U.LG.L) (fun _ => rfl)).1 hrig _ (UnitValue.thU R I e) z
    (fun _ => j) (fun _ => j') (fun _ => hj) (fun _ => hj')
  have e₄ := (H e).2 _ (eSec (thickObj R I e G)) z p q j j'
    ((congrArg (fun g => g z ∈ D.toPre.P.L.U p) (UnitValue.eSec_pGl U e)).mpr hp)
    ((congrArg (fun g => g z ∈ D'.toPre.P.L.U q) (UnitValue.eSec_pGl U' e)).mpr hq)
    ((congrArg (fun g => g z ∈ U.LG.L.U j) (UnitValue.eSec_fGl (G := G) e)).mpr hj)
    ((congrArg (fun g => g z ∈ U'.LG.L.U j') (UnitValue.eSec_fGl (G := G) e)).mpr hj')
  rw [UnitValue.eSec_pGl U' e, UnitValue.eSec_fGl (G := G) e] at e₄
  rw [Category.comp_id, Fintype.prod_unique, zpow_one] at e₃
  refine e₁.symm.trans ((congrArg _ e₃).trans ((mul_assoc _ _ _).symm.trans ?_))
  exact (congrArg (· * _) e₄.symm).trans ((mul_assoc _ _ _).trans (congrArg _ e₂))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ScalCompSpecMap
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpandsLinear

def scalOn {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) :
    R →+* Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem scalOn_apply {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (W : Y.Opens) (r : R) : resTop W (scal p r) = scalOn p W r := rfl

theorem scal_comp_specMap {R C : Type} [CommRing R] [CommRing C] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (φ : R →+* C) (r : R) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
  unfold scal
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  have := congrArg (fun g => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm

theorem app_resTop_scal {R : Type} [CommRing R] {Y Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) (r : R) :
    (h.app W).hom (resTop W (scal p r)) = resTop _ (scal (h ≫ p) r) := by
  simp only [resTop]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.naturality, CommRingCat.hom_comp,
    RingHom.comp_apply]
  rfl

def secComb {Y : Scheme.{0}} {L : LB Y} {n : ℕ} (a : Fin n → Γ(Y, ⊤)) (s : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (a i) * (s i).f j
  compat := fun j j' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (a i) (s i)).compat j j'

theorem secScal_comb {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {X Y Y' : Scheme.{0}} (L : LB X)
    {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ)
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (h : Y' ⟶ Y) (π : Y' ⟶ Spec (CommRingCat.of C))
    (π' : Y' ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ Spec (CommRingCat.of R))
    (hπ : π' = π ≫ Spec.map (CommRingCat.ofHom φ)) (hp : h ≫ p = π') {n : ℕ}
    (s : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (t : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂))
    (r a : Fin n → R) (d : R) (c : Fin n → C) (hc : ∀ i, φ (a i) * φ (r i) = φ d * c i)
    (H : ∀ i, GeneratorPullback.SecScal L φ₁ ε₁ (s i) φ₂ ε₂ (t i) h (scal π' (r i)))
    (s₀ : LB.Sec (LB.LinComb L φ₁ ε₁)) (hs : ∀ j, s₀.f j = ∑ i, resTop _ (scal π (c i)) * (s i).f j) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₀ φ₂ ε₂ (secComb (fun i => scal p (a i)) t) h (scal π' d) := by
  intro j₁ j₂ hco
  erw [hs]
  dsimp only [secComb]
  erw [map_sum, map_sum, map_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have Hi := H i j₁ j₂ hco
  erw [map_mul, map_mul, map_mul, Hi, app_resTop_scal, SecOps.resTop_res, SecOps.resTop_res]
  rw [hp, hπ, scal_comp_specMap, scal_comp_specMap, scal_comp_specMap, ← _root_.mul_assoc, ← _root_.mul_assoc]
  simp only [scalOn_apply]
  rw [← map_mul, hc, map_mul]

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {N : Type} (S : Finset N) (s : N → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ S, s i).s α).f j = ∑ i ∈ S, ((s i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

end ExpandsLinear


open ExpandsLinear in
theorem expands_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (n : ℕ) (b : Fin n → U.SecK k) (F : Fin n → Fam D.toPre (FractionRing R) k) (c : Fin n → FractionRing R) (s : U.SecK k), (∀ i, U.Expands k (b i) (F i)) → (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) → U.Expands k s (∑ i, c i • F i) := by
  intro R _ _ I _ D A G _ _ _ U k n b F c s hE hs
  choose r hr σ f hσ hf hE using hE
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun i => c i / algebraMap R (FractionRing R) (r i))
  choose a ha using hd
  have hc : ∀ i, algebraMap R (FractionRing R) (a i) * algebraMap R (FractionRing R) (r i) =
      algebraMap R (FractionRing R) d * c i := fun i => by
    have h0 : algebraMap R (FractionRing R) (r i) ≠ 0 :=
      fun h => hr i ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm))
    rw [ha i, Algebra.smul_def, _root_.mul_assoc, div_mul_cancel₀ _ h0]
  refine ⟨d, nonZeroDivisors.ne_zero d.2, ExpandsLinear.secComb (fun i => scal G.hom (a i)) σ,
    fun α => ExpandsLinear.secComb (fun i => scal D.toPre.P.A.hom (a i)) (fun i => f i α), ?_, fun α => ?_, fun e => ?_⟩
  · exact ExpandsLinear.secScal_comb (algebraMap R (FractionRing R)) _ _ _ _ _ _ (pullback.snd G.hom (jK R)) _ G.hom rfl
      pullback.condition b σ r a d c hc hσ s hs
  · refine ExpandsLinear.secScal_comb (algebraMap R (FractionRing R)) _ _ _ _ _ _
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left _ D.toPre.P.A.hom ?_
      (Over.w (DegPre.prB D.toPre (FractionRing R))) (fun i => (F i).s α) (fun i => f i α) r a d c hc
      (fun i => hf i α) _ fun j => ?_
    · rw [← Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)]
      congr 1
      change Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _ = _
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    · rw [ExpandsLinear.fam_sum_f]
      rfl
  · exact expandsAt_linear R I D A G U k e n a σ f _ _ (fun i => hE i e) (fun _ => rfl) (fun _ _ => rfl)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombEqZeroIffExpansionCombEqZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem comb_eq_zero_iff_expansion_comb_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (n : ℕ) (c : Fin n → R) (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f : Fin n → ∀ α, D.toPre.SecB k α), (∀ i e, U.ExpandsAt e k (σ i) (f i)) → ((∀ j, ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j = 0) → ∀ α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j = 0) ∧ (GeometricallyConnected G.hom → (∀ α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j = 0) → ∀ j, ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j = 0) := by
  intro R _ _ I hR D A G _ _ U k n c σ f hE
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  let σ₀ := ExpansionLinear.secComb (fun i => scal G.hom (c i)) σ
  let f₀ : ∀ α, D.toPre.SecB k α := fun α =>
    ExpansionLinear.secComb (fun i => scal D.toPre.P.A.hom (c i)) (fun i => f i α)
  have h₀ : ∀ e, U.ExpandsAt e k σ₀ f₀ := fun e =>
    expandsAt_linear R I D A G U k e n c σ f σ₀ f₀ (fun i => hE i e) (fun _ => rfl) (fun _ _ => rfl)
  refine ⟨fun h α => ?_, fun hG h => ?_⟩
  · have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
      (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (f₀ α) fun e j => ?_
    refine (ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1
      (WeightPf.weightIndep R I D A G U e k σ₀ f₀ (fun j => ?_) (h₀ e) α j)
    exact (congrArg _ (h j)).trans (map_zero _)
  · have := U.smooth
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI G).1 _
      (DVR.linComb_isLB _ U.LG.isLB _ _) σ₀ fun e j => ?_
    exact ClosedFibreTerm.vanish_of_terms_vanish U e k σ₀ f₀ (h₀ e)
      (fun α j => (congrArg _ (h α j)).trans (map_zero _)) j

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AppCompEqZeroOfGermDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecDivOfThickenings
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ThickeningDivisible

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace
open ThickeningDetermines ThickeningClosed

theorem gs_zero {X Z : Scheme.{0}} (q : Z ⟶ X) (z : Z) (U : X.Opens) : gs q z U 0 = 0 := by
  unfold gs
  split_ifs
  · rw [map_zero, map_zero]
  · rfl

theorem cst_comp_eq_zero {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {r : R}
    (hr : φ r = 0) {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R')) (z : Z) :
    cst (q ≫ Spec.map (CommRingCat.ofHom φ)) z r = 0 := by
  have h : ((Spec.map (CommRingCat.ofHom φ)).app ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
    have := congrArg (fun k ↦ k.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [hr, map_zero] at this
    exact this.symm
  rw [cst, ← gs_pull q _ z ⊤ trivial, h, gs_zero]

theorem constFn_dvd_of_mem_ker {R : Type} [CommRing R] {X Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (r : R) (i : Z ⟶ X)
    (l : pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))) ⟶ Z)
    (hl : l ≫ i = pullback.fst _ _) {W : X.Opens} (hW : IsAffineOpen W) {a : Γ(X, W)}
    (ha : a ∈ i.ker.ideal ⟨W, hW⟩) : constFn p W r ∣ a := by
  let φ : CommRingCat.of R ⟶ Γ(X, W) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ W le_top
  have hφ : Spec.map φ = hW.fromSpec ≫ p := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hW le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h, Spec.map_comp]
  have := ker_ideal_le_ker i hW
    (CommRingCat.ofHom (Ideal.Quotient.mk ((Ideal.span {r}).map φ.hom)))
    (pullback.lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((Ideal.span {r}).map φ.hom))) ≫
      hW.fromSpec)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((Ideal.span {r}).map φ.hom) φ.hom
        Ideal.le_comap_map)))
      (by
        rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_comp]
        rfl) ≫ l)
    (by rw [Category.assoc, hl, pullback.lift_fst]) ha
  rw [CommRingCat.hom_ofHom, Ideal.mk_ker, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at this
  exact this

theorem map_le_jacobson {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥) :
    I.map φ ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_jacobson_of_surjective hφ]
  exact hI.trans (Ideal.jacobson_mono bot_le)

end ThickeningDivisible


end GlobalTheory
end

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem app_comp_eq_zero_of_germ_dvd {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (a : Y ⟶ X) (b : Z ⟶ Y) (r : R)
    (hr : ∀ z, cst (b ≫ a ≫ p) z r = 0) (U : X.Opens) (f : Γ(X, U))
    (h : ∀ y, a y ∈ U → cst (a ≫ p) y r ∣ gs a y U f) : ((b ≫ a).app U).hom f = 0 := by
  refine fn_ext fun z hz ↦ ?_
  have hz' : b z ∈ a ⁻¹ᵁ U := hz
  have key : ∀ {W : Scheme.{0}} (c : Y ⟶ W) (V : W.Opens) (g : Γ(W, V)), c (b z) ∈ V →
      gs (b ≫ c) z V g = (b.stalkMap z).hom (gs c (b z) V g) := fun c V g hV ↦ by
    rw [← gs_pull b c z V hV, gs_stalkMap b z _ hV, gs_pull (𝟙 Y) c (b z) V hV, Category.id_comp]
  obtain ⟨t, ht⟩ := h (b z) hz'
  have h0 : (b.stalkMap z).hom (cst (a ≫ p) (b z) r) = 0 :=
    (key (a ≫ p) ⊤ _ trivial).symm.trans (hr z)
  rw [gs_pull (𝟙 Z) (b ≫ a) z U hz, Category.id_comp, key a U f hz', ht, map_mul, h0, zero_mul,
    ThickeningDivisible.gs_zero]


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData ThickeningDetermines
  ThickeningDivisible in
theorem sec_div_of_germ_dvd (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom]
    [GeometricallyConnected H.hom] (N : LB H.left) (hN : N.IsLB) (s : LB.Sec N) (r : R) (hr : r ≠ 0)
    (hs : ∀ (n : ℕ) (j : N.ι) (y : (thickObj R I n H).left), (fstG I n H).left y ∈ N.U j →
      cst (Z := (thickObj R I n H).left) ((fstG I n H).left ≫ H.hom) y r ∣
        gs (Y := (thickObj R I n H).left) (fstG I n H).left y (N.U j) (s.f j)) :
    ∃ s' : LB.Sec N, ∀ j, s.f j = resTop _ (scal H.hom r) * s'.f j := by
  let φ : R →+* R ⧸ Ideal.span {r} := Ideal.Quotient.mk _
  let q := Spec.map (CommRingCat.ofHom φ)
  let H₀ : Over (Spec (CommRingCat.of (R ⧸ Ideal.span {r}))) := (Over.pullback q).obj H
  let π : H₀.left ⟶ H.left := pullback.fst H.hom q
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : Smooth H₀.hom := inferInstanceAs (Smooth (pullback.snd H.hom q))
  have : GeometricallyConnected H₀.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom q))
  have := grpObj_geometricallyIntegral_of_smooth _ H₀
  have key := isIso_of_isClosedImmersion_of_thickenings _ (I.map φ)
    (map_le_jacobson φ Ideal.Quotient.mk_surjective hI) H₀ η[H₀] (fun p ↦ inferInstance)
    _ (pullback.snd (secIdeal hN s).subschemeι π) fun n ↦ by
      have : IsClosedImmersion (thick _ (I.map φ) n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG (I.map φ) n H₀).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H₀.hom (thick _ (I.map φ) n)))
      have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst H.hom q))
      have hπ : π ≫ H.hom = H₀.hom ≫ q := pullback.condition
      let b : (thickObj _ (I.map φ) n H₀).left ⟶ (thickObj R I n H).left :=
        pullback.lift ((fstG (I.map φ) n H₀).left ≫ π)
          (pullback.snd H₀.hom (thick _ (I.map φ) n) ≫
            Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map φ) ^ (n + 1)) φ
            (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))))
          (by
            rw [Category.assoc, hπ, Category.assoc, ← Spec.map_comp, ← Category.assoc]
            erw [pullback.condition]
            rw [Category.assoc, ← Spec.map_comp]
            rfl)
      have hb : b ≫ (fstG I n H).left = (fstG (I.map φ) n H₀).left ≫ π := pullback.lift_fst _ _ _
      have h0 : ∀ j, (((fstG (I.map φ) n H₀).left ≫ π).app _).hom (s.f j) = 0 := fun j ↦ by
        rw [← hb]
        refine app_comp_eq_zero_of_germ_dvd H.hom _ b r (fun z ↦ ?_) _ _ (hs n j)
        rw [← Category.assoc, hb, Category.assoc, hπ, ← Category.assoc]
        exact cst_comp_eq_zero φ
          (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r)) _ z
      exact ⟨pullback.lift (IsClosedImmersion.lift _ ((fstG (I.map φ) n H₀).left ≫ π) (by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ h0)) _ (IsClosedImmersion.lift_fac _ _ _),
        pullback.lift_snd _ _ _⟩
  refine exists_div_sec H.hom hr s fun j x hx ↦ ?_
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := N.U j) hx
  have h1 := constFn_dvd_of_mem_ker H.hom r (secIdeal hN s).subschemeι
    (inv (pullback.snd (secIdeal hN s).subschemeι π) ≫ pullback.fst _ _)
    (by rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]) W.2
    (a := resG _ hW (s.f j)) (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact (ideal_locIdeal _ _ (exists_mem_chart hN) (associated_germ_sec s) W j hW).ge
        (Ideal.mem_span_singleton_self _))
  obtain ⟨c, hc⟩ := h1
  refine ⟨gs (𝟙 _) x W.1 c, ?_⟩
  have h2 := congrArg (gs (𝟙 _) x W.1) hc
  rw [gs_mul _ _ _ hxW, gs_constFn _ _ _ _ hxW, Category.id_comp] at h2
  exact (gs_res _ x hW hxW _).symm.trans h2


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR in
theorem sec_div_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (r : R), r ≠ 0 → ∀ (σ₀ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))), (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) := by
  intro R _ _ I hR D A G _ _ _ U k r hr σ₀ f₀ f hf hE
  have : IsNoetherianRing R := hR.1
  have hI : I ≤ Ideal.jacobson ⊥ := have := hR.2.2.2; IsAdicComplete.le_jacobson_bot I
  have := U.smooth
  refine sec_div_of_germ_dvd R I hI G _ (linComb_isLB _ U.LG.isLB _ _) σ₀ r hr fun e j y hy ↦ ?_
  obtain ⟨S, H⟩ := (expandsAt_iff_stalks U e k σ₀ f₀).1 (hE e)
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left ↦
    exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hc : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  obtain ⟨jL, rfl⟩ : ∃ jL : U.LG.L.ι, j = fun _ ↦ jL :=
    ⟨j 0, funext fun i ↦ congrArg j (Subsingleton.elim i 0)⟩
  have h := (H y J hJ).2 jL (Set.mem_iInter.1 hy 0)
  refine (Units.dvd_mul_left (u := wv U e (𝟙 _) y (J (pGl U e)) jL ^ k)).1 (h.symm ▸ ?_)
  refine Finset.dvd_sum fun α _ ↦ Dvd.dvd.mul_right ⟨sval (f α) (pGl U e) y J, ?_⟩ _
  rw [← hc]
  have := gs_of_eq_sum_scal (n := 1) D.toPre.P.A.hom (pGl U e) y _ (hJ.mem (D.toPre.famφB α) _)
    (fun _ ↦ r) (a := (f₀ α).f _) (b := fun _ ↦ (f α).f _) (by rw [Fin.sum_univ_one]; exact hf α _)
  rw [Fin.sum_univ_one] at this
  exact this

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecRelationDescends
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sec_relation_descends : ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (ψ : T' ⟶ T), Function.Injective ψ.left.appTop.hom → ∀ (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → ((T ⊗ B).left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → ((T ⊗ B).left ⟶ X)) (εu : K'' → ℤ) (τ : (T ⊗ B).left ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ((T ⊗ B).left, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → (∀ (z : (T' ⊗ B).left) (J), Good L z J → gs (ψ ▷ B).left z ⊤ c' * sval s' (ψ ▷ B).left z J = gs (ψ ▷ B).left z ⊤ c * (sval s ((ψ ▷ B).left ≫ τ) z J * (val u (ψ ▷ B).left z J).val)) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val)) := by
  intro S B T T' _ _ _ ψ hψ X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF h Z r z J hJ
  obtain ⟨d, hd⟩ := exists_sec_relation_defect _ X Y₂ L hL K K' K'' φ ε φ' ε' φu εu τ s s' u c c' hu hF
  have h0 := GlobalTheory.T.sec_eq_zero_of_sval_whiskerRight_zero S B T T' ψ hψ X L hL K' φ' ε' d
    (fun z J hJ => (hd _ _ z J hJ).trans (sub_eq_zero.2 (h z J hJ)))
  refine sub_eq_zero.1 ((hd Z r z J hJ).symm.trans ?_)
  refine (congrArg (gs r z _) (h0 _)).trans ((gs_eq r z _ (hJ.mem φ' r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

end GlobalTheory
end
