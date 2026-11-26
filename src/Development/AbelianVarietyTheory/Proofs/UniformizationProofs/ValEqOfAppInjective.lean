module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiEvenPull

theorem val_eq_of_app_injective {X Y Y' : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u κ y J = val u' κ y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good M z J) : val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hM hF u' hu'
  have e : ∀ j, u.s j = t.s j := fun j => by
    have : pullU κ (LB.wchart M φ j) (u.s j) = pullU κ (LB.wchart M φ j) (t.s j) := unit_ext fun y hy => by
      choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
      refine (gm_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') κ y _ hy _).symm)
      rw [Category.id_comp]
      exact (gen_trans hu κ y hy (Good.mem hI φ κ)).trans ((congrArg _ ((h y I hI).trans (hv _ κ y I hI).symm)).trans
        (gen_trans ht κ y hy (Good.mem hI φ κ)).symm)
    exact Units.ext (hκ _ (congrArg Units.val this))
  exact (congrArg (gm r z _) (e _)).trans (hv Z r z J hJ)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem c_neg (D : DegPre R) (χ : D.X) : D.c (-χ) = D.c χ ≫ ι[D.P.A] := by
  have m : ∀ a b, D.c (a + b) = D.c a * D.c b := fun a b => D.c_add a b
  have z : D.c 0 = 1 := mul_eq_left.1 ((m 0 0).symm.trans (congrArg D.c (add_zero 0)))
  rw [← Hom.inv_def]
  exact eq_inv_of_mul_eq_one_left ((m _ _).symm.trans ((congrArg D.c (neg_add_cancel χ)).trans z))

theorem app_injective_generic (W : (Spec (CommRingCat.of R)).Opens) (U : W.toScheme.Opens) :
    Function.Injective ((jK R ∣_ W).app U).hom := by
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (jK R ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (jK R) W).flip
  exact (jK R ∣_ W).app_injective U

theorem even_on (h : D.PsiEven) {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (χ : D.X) {Z : Scheme.{0}}
    (r : Z ⟶ (TW W).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    val (ψW.psi (-χ)) r z J * val D.sym (r ≫ (toUnit (TW W) ≫ D.c χ).left) z J = val (ψW.psi χ) r z J := by
  have cn : (toUnit (TW W) ≫ D.c (-χ)).left = (toUnit (TW W) ≫ D.c χ).left ≫ (ι[D.P.A]).left := by
    rw [c_neg, ← Category.assoc, Over.comp_left]
  have key := val_eq_of_app_injective D.P.isLB (u' := LB.mulGen D.P.L _ _ _ _ (ψW.psi (-χ))
      (LB.pullGen D.P.L _ _ D.sym (toUnit (TW W) ≫ D.c χ).left)) (u := ψW.psi χ) (fun V _ k => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Fintype.prod_unique]
      show k (toUnit (TW W) ≫ D.c (-χ)).left ^ (-1 : ℤ) * (k ((toUnit (TW W) ≫ D.c χ).left ≫ (ι[D.P.A]).left) ^ (1 : ℤ) *
        k ((toUnit (TW W) ≫ D.c χ).left ≫ 𝟙 _) ^ (-1 : ℤ)) = k (toUnit (TW W) ≫ D.c χ).left ^ (-1 : ℤ)
      rw [cn, Category.comp_id]
      simp) (jK R ∣_ W) (app_injective_generic W) (ψW.psi_gen χ)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _) (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)) (fun y I hI => by
      have p : ∀ a, val (ψW.psi a) (jK R ∣_ W) y I = val (D.psi a) (jK R ⁻¹ᵁ W).ι y I := fun a => by
        have := val_corr hI (ψW.psi_eq a) (𝟙 _)
        rwa [val_pull hI, val_pull hI, Category.id_comp, Category.id_comp] at this
      have q : (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ D.xK χ := by
        show (jK R ∣_ W) ≫ W.ι ≫ (D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ jK R ≫ (D.c χ).left
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      have e := val_corr hI (h χ) (jK R ⁻¹ᵁ W).ι
      rw [val_mul hI, val_pull hI] at e
      rw [val_mul hI, val_pull hI, p, p, q]
      exact e.symm) Z r z J hJ
  rw [val_mul hJ, val_pull hJ] at key
  exact key.symm

abbrev proj (hD : IsPullDeg φ D D') : D'.P.A.left ⟶ D.P.A.left :=
  hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)

theorem inv_proj (hD : IsPullDeg φ D D') : (ι[D'.P.A]).left ≫ proj hD = proj hD ≫ (ι[D.P.A]).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom (pull_grp hD) D'.P.A) (𝟙 _))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine e.trans ?_
  show ((𝟙 D'.P.A : D'.P.A ⟶ D'.P.A).left ≫ proj hD) ≫ _ = _
  rw [Over.id_left, Category.id_comp]

theorem sym_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D.sym (r ≫ proj hD) z J =
      gw hD.w (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ proj hD)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw hD.w r z (J (r ≫ proj hD)) (J' r))⁻¹ * val D'.sym r z J' := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB D'.sym D'.sym_gen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J =
      gw hD.w (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ proj hD)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw hD.w r z (J (r ≫ proj hD)) (J' r))⁻¹ * val D'.sym r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
    rw [pw, Fin.prod_univ_two]
    show gw hD.w (r ≫ (ι[D'.P.A]).left) z (J (r ≫ (ι[D'.P.A]).left ≫ proj hD)) (J' (r ≫ (ι[D'.P.A]).left)) ^ (1 : ℤ) *
      gw hD.w (r ≫ 𝟙 _) z (J (r ≫ 𝟙 _ ≫ proj hD)) (J' (r ≫ 𝟙 _)) ^ (-1 : ℤ) = _
    rw [Category.comp_id, Category.id_comp, Category.assoc r, zpow_one, zpow_neg_one]
  have oi : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    have : η[D'.P.A] ≫ ι[D'.P.A] = η[D'.P.A] := by simp
    exact congrArg (fun q => q.left) this
  have key := gen_unique' D.P.isLB
    (φ := fun k => proj hD ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) (ε := ![1, -1])
    (fun V _ k => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      show k ((ι[D'.P.A]).left ≫ proj hD) ^ (1 : ℤ) * k (𝟙 _ ≫ proj hD) ^ (-1 : ℤ) =
        k (proj hD ≫ (ι[D.P.A]).left) ^ (1 : ℤ) * k (proj hD ≫ 𝟙 _) ^ (-1 : ℤ)
      rw [inv_proj, Category.id_comp, Category.comp_id])
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ D.sym_gen (proj hD)) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Spec (CommRingCat.of R')))).left ⟶ D'.P.A.left =>
        exists_chart D'.P.isLB (χ y)
      have a := val_corr hI' D'.sym_rig (𝟙 _)
      rw [val_pull hI', val_one, Category.id_comp] at a
      have b := val_corr hI D.sym_rig (specOf φ)
      rw [val_pull hI, val_one, ← hD.he] at b
      refine ((val_pull hI _ _ _).trans b).trans (Eq.symm ((hv' _ _ y I I' hI hI').trans ?_))
      rw [a, oi, mul_inv_cancel, _root_.one_mul]) Z r z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

theorem psi_pull (hD : IsPullDeg φ D D') (x : D'.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R').left) (z : Z) {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (hD.psiW.psi (hD.xe x)) (r ≫ hD.g) z J =
      (gw hD.w (r ≫ D'.xK x) z (J ((r ≫ D'.xK x) ≫ proj hD)) (J' (r ≫ D'.xK x)))⁻¹ * val (D'.psi x) r z J' := by
  obtain ⟨b, hb, hcorr⟩ := hD.psi_pr x
  have m₁ : r z ∈ D'.xK x ⁻¹ᵁ ((D.P.L.pull (proj hD)).U (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) ⊓
      D'.P.L.U (J' (r ≫ D'.xK x))) := ⟨mem_pull.2 (hJ ((r ≫ D'.xK x) ≫ proj hD)), hJ' (r ≫ D'.xK x)⟩
  have e₁ := congrArg (gm r z (D'.xK x ⁻¹ᵁ ((D.P.L.pull (proj hD)).U (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) ⊓
      D'.P.L.U (J' (r ≫ D'.xK x))))) (hb (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) (J' (r ≫ D'.xK x)))
  have e₁' := (gm_res _ z _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK x) z
      ((D.P.L.pull (proj hD)).U (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) ⊓ D'.P.L.U (J' (r ≫ D'.xK x))) m₁ _)))
      (gm_res _ z _ m₁ _))))
  refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ hcorr r).symm.trans ((val_of b r z J
    (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) (fun _ => by rw [Category.assoc])).trans (e₁'.trans ?_)))
  rw [zpow_neg_one]
  rfl

theorem psiEven_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), D.PsiEven → D'.PsiEven := by
  intro hG R R' _ _ _ _ φ D D' hD h x
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ using fun χ : (TK R').left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have cW : hD.g ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left = D'.xK x ≫ proj hD := by
    have hx : D'.xK x ≫ proj hD = jK R' ≫ specOf φ ≫ (D.c (hD.xe x)).left := by
      rw [← hD.c_pr x, ← Category.assoc]; rfl
    rw [hx, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [c_neg, ← Category.assoc, Over.comp_left]
  have e := even_on h hD.psiW (hD.xe x) (𝟙 _ ≫ hD.g) y J hJ
  rw [← map_neg, psi_pull hD _ _ y hJ hJ', psi_pull hD _ _ y hJ hJ', Category.assoc (𝟙 _) hD.g, cW,
    ← Category.assoc (𝟙 _) (D'.xK x), sym_pull hG hD _ y hJ hJ'] at e
  have c' : 𝟙 _ ≫ D'.xK (-x) = (𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left := by rw [cn, Category.assoc]
  rw [c'] at e
  rw [val_mul hJ', val_pull hJ']
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory.PsiEvenPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
noncomputable section

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CubTransport

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Down

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_down_units {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun Z r z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans
        (congrArg (·⁻¹) (hu p q _ _ z hz))) (gm_res _ z _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)
      (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ z inf_le_right hz s).symm.trans ((congrArg (gm _ z _) (hs p)).trans (hv Z r z p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q h₁ h₂ => ?_⟩
  · choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
    refine (hs j _ (𝟙 Y) y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y p m hj')).symm)
    rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv,
      _root_.mul_assoc]
  · exact (mul_inv_cancel_left _ _).symm.trans (congrArg (pw w φ' ε r z p q * ·) (hs q Z r z p h₁ h₂).symm)

theorem exists_pmaps {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  have key : ∀ (ψ : K → (Y' ⟶ X)) (_ : ∀ k, φ' k ≫ F = ψ k) (t₀ : LB.Gen (LB.LinComb L ψ ε)), t₀.IsGen →
      ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L ψ p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L ψ p) (t₀.s p) = pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
    intro ψ hψ t₀ h₀
    obtain rfl : (fun k => φ' k ≫ F) = ψ := funext hψ
    exact exists_down_units hw hL hL' t₀ h₀
  obtain ⟨a, ha, hv⟩ := key _ hc (LB.pullGen L φ ε t h) (pullGen_isGen _ _ _ _ ht h)
  refine ⟨a, ha, fun Z r z p q hp hq => ?_⟩
  have hm : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 fun k => by
    show φ k (h (r z)) ∈ L.U (p k)
    rw [pt_eq hc]; exact hp k
  refine Eq.trans ?_ (hv Z r z p q hm (Set.mem_iInter.2 hq))
  exact ((gm_res r z _ hm _).trans (gm_pull r h z (LB.wchart L φ p)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)).symm

theorem val_pmaps {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  rw [val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hc])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))

end Down

theorem isCub_of_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] {θ : A → A → A → U}
    (hθ : IsCub θ) (β : A' →* A) (Ω : A' → U) {θ' : A' → A' → A' → U}
    (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
      Ω c * (Ω 1)⁻¹ * θ' a b c) : IsCub θ' := by
  refine ⟨fun x y => ?_, fun x y z => ?_, fun x y z => ?_, fun x x' x'' y => ?_⟩
  · have e := h 1 x y
    rw [map_one, hθ.face] at e
    simp only [_root_.one_mul] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hθ.s01 (β x) (β y) (β z)
    rw [h, h, mul_comm y x] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := hθ.s12 (β x) (β y) (β z)
    rw [h, h, mul_comm z y, mul_right_comm x z y] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := hθ.coc (β x) (β x') (β x'') (β y)
    rw [← map_mul, ← map_mul, h, h, h, h] at e
    simp only [← _root_.mul_assoc x] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'

section Cub

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}

def thV (t : LB.Gen (Theta G L.L)) {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) (x x' y : T ⟶ G) :
    (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (lift x (lift x' y)).left z J

theorem val_thV (t : LB.Gen (Theta G L.L)) {T : Over S} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι}
    (hJ : Good L.L z J) (x x' y : T ⟶ G) :
    val (LB.pullGen L.L (thφ G (x3 G)) thε t (lift x (lift x' y)).left) (𝟙 T.left) z J = thV t z J x x' y := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [Category.id_comp]; rfl

theorem val_id_thV (t : LB.Gen (Theta G L.L)) {z : (G3 G).left} {J : ((G3 G).left ⟶ G.left) → L.L.ι} :
    val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (𝟙 (G3 G).left) z J = thV t z J (x3 G 0) (x3 G 1) (x3 G 2) := by
  have e : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
    ext <;> simp [x3]
  rw [thV, e]; rfl

def cubicalOfVal (t : LB.Gen (Theta G L.L)) (ht : t.IsGen)
    (h : ∀ (T : Over S) (z : T.left) (J), Good L.L z J → IsCub (thV t z J)) : CubicalStr G L where
  t := t
  isGen := ht
  face i := corr_of_val L.isLB fun y J hJ => by
    refine Eq.trans ?_ (val_one _).symm
    have C := h (G2 G) y J hJ
    fin_cases i
    · exact (val_thV t hJ _ _ _).trans (C.face _ _)
    · exact (val_thV t hJ _ _ _).trans (C.face₂ _ _)
    · exact (val_thV t hJ _ _ _).trans (C.face₃ _ _)
  cubeSymmetric_swap_first := corr_of_val L.isLB fun y J hJ =>
    (val_id_thV t).trans (((h (G3 G) y J hJ).s01 _ _ _).trans (val_thV t hJ _ _ _).symm)
  cubeSymmetric_swap_last := corr_of_val L.isLB fun y J hJ =>
    (val_id_thV t).trans (((h (G3 G) y J hJ).s12 _ _ _).trans (val_thV t hJ _ _ _).symm)
  cocycle := corr_of_val L.isLB fun y J hJ =>
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_thV t hJ _ _ _) (val_thV t hJ _ _ _))).trans
      (((h (G4 G) y J hJ).coc _ _ _ _).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_thV t hJ _ _ _) (val_thV t hJ _ _ _))).symm)

end Cub

end CubTransport


open CubTransport ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem cubical_symmetry_transport : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (hgp : Geo.Tor.IsGrpPullback G' G f Ψ) (L : RigLB G) (L' : RigLB G') (wL : LB.Iso L'.L (L.L.pull Ψ)) (he : eSec G' ≫ Ψ = f ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf Ψ f he L.L L.rig) → ∀ (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) → ∃ (c' : CubicalStr G' L') (s' : LB.Gen (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])), s'.IsGen ∧ LB.Gen.Corr L'.L _ _ _ _ (LB.pullGen L'.L _ _ s' (eSec G')) (LB.oneGen L'.L) ∧ Geo.Tor.PMaps wL (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (Geo.Tor.cubeMapOf hgp).F3 ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] s' s Ψ := by
  intro S S' f G _ _ G' _ _ Ψ hgp L L' wL he hw _ c s hs hs1
  have hw' := (isGen_iff wL).1 hw
  have good : ∀ {Z : Scheme.{0}} (z : Z), ∃ J, Good L.L z J := fun {Z} z => by
    choose I hI using fun χ : Z ⟶ G.left => exists_chart L.isLB (χ z)
    exact ⟨I, hI⟩
  have hc : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ Ψ = (cubeMapOf hgp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf hgp).psum_comm I.down
  obtain ⟨t', ht', Ht⟩ := exists_pmaps hw' L.isLB L'.isLB (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε)
    (cubeMapOf hgp).F3 hc c.t c.isGen
  have hι : (ι[G']).left ≫ Ψ = Ψ ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom hgp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ Ψ) ≫ _ = _
    rw [Category.id_comp]
  have hc₂ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ Ψ = Ψ ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', Hs⟩ := exists_pmaps hw' L.isLB L'.isLB Ψ hc₂ s hs
  refine ⟨cubicalOfVal t' ht' fun T z J' hJ' => ?_, s', hs', corr_of_val L'.isLB fun y J' hJ' => ?_, Ht, Hs⟩
  · obtain ⟨J, hJ⟩ := good z
    refine isCub_of_twist (isCub_cubV c (T := Over.mk (T.hom ≫ f)) hJ) (pushHom hgp T)
      (fun x => gw wL x.left z (J (x.left ≫ Ψ)) (J' x.left)) fun a b d => ?_
    have q : (lift a (lift b d)).left ≫ (cubeMapOf hgp).F3 =
        (lift (pushHom hgp T a) (lift (pushHom hgp T b) (pushHom hgp T d))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    have e := val_pmaps hc Ht (lift a (lift b d)).left hJ hJ'
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b d (fun q => gw wL q z (J (q ≫ Ψ)) (J' q))) rfl)
  · obtain ⟨J, hJ⟩ := good y
    have e := val_pmaps hc₂ Hs (eSec G') hJ hJ'
    have e₁ : val s (eSec G' ≫ Ψ) y J = 1 := by
      rw [he]
      exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hs1 f).trans (val_one _))
    have e₂ : eSec G' ≫ (ι[G']).left = eSec G' := by
      rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    rw [e₁, Fin.prod_univ_two] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₂, Category.comp_id, zpow_one, zpow_neg,
      mul_inv_cancel, _root_.one_mul] at e
    refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact e.symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigidIsoCube

theorem surjective_appTop_of_baseChange {Y S Y' S' : Scheme.{0}} {q : Y' ⟶ Y} {p' : Y' ⟶ S'} {p : Y ⟶ S} {j : S' ⟶ S}
    (h : IsPullback q p' p j) [Flat p] [QuasiCompact j] [IsSchemeTheoreticallyDominant j] (e : S ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hs : Function.Surjective p'.appTop.hom) : Function.Surjective p.appTop.hom := by
  have : IsSchemeTheoreticallyDominant q := IsSchemeTheoreticallyDominant.of_isPullback h.flip
  have : QuasiCompact q := MorphismProperty.of_isPullback h.flip ‹_›
  have inj : Function.Injective q.appTop.hom := q.app_injective ⊤
  have cmp : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : Γ(C, ⊤)),
      f.appTop.hom (g.appTop.hom x) = (f ≫ g).appTop.hom x := fun f g x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  intro a
  obtain ⟨c, hc⟩ := hs (q.appTop.hom a)
  let e' : S' ⟶ Y' := h.lift (j ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : e' ≫ q = j ≫ e := h.lift_fst _ _ _
  have h₂ : e' ≫ p' = 𝟙 _ := h.lift_snd _ _ _
  have hc' : c = j.appTop.hom (e.appTop.hom a) := by
    have := congrArg e'.appTop.hom hc
    rw [cmp, cmp, h₁, h₂, Scheme.Hom.id_appTop] at this
    rw [cmp]; exact this
  refine ⟨e.appTop.hom a, inj ?_⟩
  rw [← hc, hc', cmp q p, cmp p' j, h.w]

theorem surjective_snd_of_generic (hG : GlobalFnsSt) {S S' : Scheme.{0}} (k : S' ⟶ S) [QuasiCompact k]
    [IsSchemeTheoreticallyDominant k] (G : Over S) [GrpObj G] [Flat G.hom] {A : Over S'} [GrpObj A]
    (hA : IsAbelianScheme A) {g : A.left ⟶ G.left} (hg : IsPullback g A.hom G.hom k) (T : Over S) [Flat T.hom] :
    Function.Surjective (snd G T).left.appTop.hom := by
  let T' : Over S' := Over.mk (pullback.snd T.hom k)
  have : IsSchemeTheoreticallyDominant (pullback.fst T.hom k) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback T.hom k).flip
  have big : IsPullback (pullback.fst A.hom T'.hom ≫ g) (pullback.snd A.hom T'.hom) G.hom
      (pullback.fst T.hom k ≫ T.hom) := by
    rw [pullback.condition]
    exact (IsPullback.of_hasPullback A.hom T'.hom).paste_horiz hg
  have sq : IsPullback (pullback.lift (pullback.fst A.hom T'.hom ≫ g) (pullback.snd A.hom T'.hom ≫ pullback.fst T.hom k)
      (by rw [big.w, Category.assoc])) (pullback.snd A.hom T'.hom) (pullback.snd G.hom T.hom) (pullback.fst T.hom k) :=
    IsPullback.of_right (by rw [pullback.lift_fst]; exact big) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback G.hom T.hom)
  have : Flat (snd G T).left := inferInstanceAs (Flat (pullback.snd G.hom T.hom))
  refine surjective_appTop_of_baseChange (p := (snd G T).left) sq (lift (1 : T ⟶ G) (𝟙 T)).left ?_ (surj_snd hG hA T')
  exact congrArg (fun q => q.left) (lift_snd (1 : T ⟶ G) (𝟙 T))

theorem pmaps_of_section {X X' Y S₀ : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (hψ : ∀ k, φ' k ≫ F = φ k) (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom)
    (h : ∀ (y : S₀) J J', Good L y J → Good L' y J' → val t e y J =
      (∏ k, gw w (e ≫ φ' k) y (J ((e ≫ φ' k) ≫ F)) (J' (e ≫ φ' k)) ^ ε k) * val a e y J') :
    PMaps w φ' φ ε a t (𝟙 Y) := by
  obtain rfl : φ = fun k => φ' k ≫ F := funext fun k => (hψ k).symm
  obtain ⟨t₁, ht₁, hv⟩ := exists_up hw hL hL' a ha
  have key := gen_unique hL p e he hp ht ht₁ (fun y J hJ => by
    choose J' hJ' using fun ψ : S₀ ⟶ X' => exists_chart hL' (ψ y)
    have v := hv _ e y _ _ (Good.mem hJ _ e) (Good.mem hJ' _ e)
    refine (h y J J' hJ hJ').trans (Eq.trans (congrArg₂ (· * ·) ?_ rfl) v.symm)
    simp only [pw, Category.assoc])
  intro Z r z i q hi hq
  rw [Category.comp_id]
  have hi' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) i := Set.mem_iInter.2 hi
  choose J hJ using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  exact ((gen_trans ht r z hi' (Good.mem hJ _ r)).trans ((congrArg _ (key Z r z J hJ)).trans
    (gen_trans ht₁ r z hi' (Good.mem hJ _ r)).symm)).trans (hv Z r z i q hi' (Set.mem_iInter.2 hq))

end GlobalTheory.RigidIsoCube

namespace GlobalTheory


open RigidIsoCube in
theorem rigidified_iso_respects_cube_and_symmetry : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → (Geo.Tor.PMaps wL (thφ G (x3 G)) (thφ G (x3 G)) thε U'.cubG.t U.cubG.t (𝟙 _) ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] U'.symG U.symG (𝟙 G.left)) := by
  intro hG R _ _ _ I _ D D' A A' G _ _ _ U U' wL _ hw _
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom :=
    surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)
  have pg := (isGen_iff wL).1 hw
  constructor
  · let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
    have he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _ := by
      rw [Over.w, Over.w]; exact Over.w e
    refine pmaps_of_section pg U.LG.isLB U'.LG.isLB (φ' := thφ G (x3 G)) (φ := thφ G (x3 G)) (ε := thε)
      U'.cubG.t U'.cubG.isGen U.cubG.t U.cubG.isGen (fun _ => Category.comp_id _) _ e.left he sj fun y J J' hJ hJ' => ?_
    have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) 1 1
      (fun q => gw wL q y (J (q ≫ 𝟙 _)) (J' q))
    rw [_root_.mul_one, _root_.mul_one] at p
    refine ((isCub_cubV U.cubG hJ).face 1 1).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) p ((isCub_cubV U'.cubG hJ').face 1 1)).symm)
    group
  · have oi : eSec G ≫ (ι[G]).left = eSec G := by
      have : η[G] ≫ ι[G] = η[G] := by simp
      exact congrArg (fun q => q.left) this
    refine pmaps_of_section pg U.LG.isLB U'.LG.isLB U'.symG U'.symG_gen U.symG U.symG_gen
      (fun _ => Category.comp_id _) G.hom (eSec G) (Over.w η[G]) s₁ fun y J J' hJ hJ' => ?_
    have a := val_corr hJ U.symG_rig (𝟙 _)
    rw [val_pull hJ, val_one, Category.id_comp] at a
    have b := val_corr hJ' U'.symG_rig (𝟙 _)
    rw [val_pull hJ', val_one, Category.id_comp] at b
    rw [a, b, Fin.prod_univ_two]
    show 1 = gw wL (eSec G ≫ (ι[G]).left) y (J ((eSec G ≫ (ι[G]).left) ≫ 𝟙 _)) (J' (eSec G ≫ (ι[G]).left)) ^ (1 : ℤ) *
      gw wL (eSec G ≫ 𝟙 _) y (J ((eSec G ≫ 𝟙 _) ≫ 𝟙 _)) (J' (eSec G ≫ 𝟙 _)) ^ (-1 : ℤ) * 1
    simp only [oi, Category.comp_id]
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SymmetricBundle

open Geo.Tor

theorem isSymmetric_of_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (sy : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hsy : sy.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sy (eSec G)) (LB.oneGen L.L)) : L.IsSymmetric := by
  have oi : eSec G ≫ (ι[G]).left = eSec G := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    exact congrArg (fun q => q.left) this
  have mem : ∀ (x : G.left) (a b : L.L.ι), (ι[G]).left x ∈ L.L.U a → x ∈ L.L.U b →
      x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b] := fun x a b ha hb =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [ha, hb]
  have le : ∀ p : (PUnit → L.L.ι) × L.L.ι, (L.L.pull (ι[G]).left).U p.1 ⊓ L.L.U p.2 ≤
      LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![p.1 PUnit.unit, p.2] := fun p x hx =>
    mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso L.L (L.L.pull (ι[G]).left) := ⟨fun p => res (le p) (sy.s ![p.1 PUnit.unit, p.2])⟩
  have hw : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (a b : L.L.ι), (ι[G]).left (f y) ∈ L.L.U a → f y ∈ L.L.U b →
      gw w f y a b = gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b]) (sy.s ![a, b]) :=
    fun Y f y a b ha hb => gm_res f y (le (fun _ => a, b)) ⟨mem_pull.2 ha, hb⟩ _
  have pg : PGen w := by
    intro Y f y j j' k k' hj hj' hk hk'
    rw [hw Y f y j k hj hk, hw Y f y j' k' hj' hk', gen_trans hsy f y (mem _ _ _ hj hk) (mem _ _ _ hj' hk')]
    congr 1
    rw [trF, Fin.prod_univ_two]
    show gm (f ≫ (ι[G]).left) y _ (L.L.g j j') ^ (1 : ℤ) * gm (f ≫ 𝟙 _) y _ (L.L.g k k') ^ (-1 : ℤ) = _
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  refine ⟨oi.trans (Category.id_comp _).symm, w, (isGen_iff w).2 pg, ?_⟩
  refine (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) (oi.trans (Category.id_comp _).symm) L.L j) (fun _ => rfl)).2 ?_
  intro Z r z p q hp hq
  have hp₀ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (p PUnit.unit) := hp PUnit.unit
  have hq₀ : (r ≫ eSec G) z ∈ L.L.U (q PUnit.unit) := hq PUnit.unit
  have ri : (r ≫ eSec G) ≫ (ι[G]).left = r ≫ eSec G := by rw [Category.assoc, oi]
  have hp₁ : (r ≫ eSec G) z ∈ L.L.U (p PUnit.unit) := by rw [← ri]; exact hp₀
  have hq₁ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (q PUnit.unit) := by
    have := hq₀
    rw [← ri] at this; exact this
  have one : gw w (r ≫ eSec G) z (q PUnit.unit) (q PUnit.unit) = 1 := by
    obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB z (K := PUnit) (fun _ => r ≫ eSec G) q (fun _ _ _ => rfl)
      (fun _ => hq₀)
    have a := val_corr hJ hr r
    rw [val_pull hJ, val_one, val_of sy (r ≫ eSec G) z J ![q PUnit.unit, q PUnit.unit] (fun k => by
      fin_cases k
      · exact (congrArg J ri).trans (e PUnit.unit)
      · exact (congrArg J (Category.comp_id _)).trans (e PUnit.unit))] at a
    exact (hw _ _ _ _ _ hq₁ hq₀).trans a
  rw [Category.comp_id, Fintype.prod_unique, zpow_one,
    gen_trans L.rigGen r z (j := p) (j' := q) (Set.mem_iInter.2 fun _ => hp₁) (Set.mem_iInter.2 fun _ => hq₀)]
  congr 1
  have b := pg _ (r ≫ eSec G) z (p PUnit.unit) (q PUnit.unit) (q PUnit.unit) (q PUnit.unit) hp₀ hq₁ hq₀ hq₀
  rw [one, gm_self L.isLB _ z hq₀, ri, inv_one, _root_.mul_one, _root_.mul_one] at b
  rw [trF, Fintype.prod_unique, zpow_one]
  exact b.symm

theorem gen_of_isSymmetric {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (h : L.IsSymmetric) :
    ∃ s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) := by
  obtain ⟨he, w, hw, hm⟩ := h
  have oi : eSec G ≫ (ι[G]).left = eSec G := he.trans (Category.id_comp _)
  have pg := (isGen_iff w).1 hw
  have pm := (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) he L.L j) (fun _ => rfl)).1 hm
  have m₀ : ∀ (j : Fin 2 → L.L.ι) (x : G.left), x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      (ι[G]).left x ∈ L.L.U (j 0) := fun j x hx => Set.mem_iInter.1 hx 0
  have m₁ : ∀ (j : Fin 2 → L.L.ι) (x : G.left), x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      x ∈ L.L.U (j 1) := fun j x hx => Set.mem_iInter.1 hx 1
  have le : ∀ j : Fin 2 → L.L.ι, LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j ≤
      (L.L.pull (ι[G]).left).U (fun _ => j 0) ⊓ L.L.U (j 1) := fun j x hx => ⟨mem_pull.2 (m₀ j x hx), m₁ j x hx⟩
  let s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]) :=
    ⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩
  have hs : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : Fin 2 → L.L.ι),
      f y ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j) (s.s j) = gw w f y (j 0) (j 1) :=
    fun Y f y j hj => gm_res f y (le j) hj _
  refine ⟨s, fun j j' => unit_ext fun x hx => ?_, corr_of_val L.isLB fun y J hJ => ?_⟩
  · refine ((gm_res (𝟙 G.left) x _ hx _).trans (hs _ (𝟙 G.left) x j hx.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L.L _ _ (𝟙 _) x j j' hx.1 hx.2)
        ((gm_res (𝟙 G.left) x _ hx _).trans (hs _ (𝟙 G.left) x j' hx.2)))).symm)
    rw [pg _ (𝟙 _) x (j 0) (j' 0) (j 1) (j' 1) (m₀ _ _ hx.1) (m₀ _ _ hx.2) (m₁ _ _ hx.1) (m₁ _ _ hx.2),
      Fin.prod_univ_two]
    congr 1
    show _ = gm (𝟙 _ ≫ (ι[G]).left) x _ (L.L.g (j 0) (j' 0)) ^ (1 : ℤ) *
      gm (𝟙 _ ≫ 𝟙 _) x _ (L.L.g (j 1) (j' 1)) ^ (-1 : ℤ)
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  · have ri : (𝟙 _ ≫ eSec G) ≫ (ι[G]).left = 𝟙 _ ≫ eSec G := by rw [Category.assoc, oi]
    have hq₀ : (𝟙 _ ≫ eSec G) y ∈ L.L.U (J (𝟙 _ ≫ eSec G)) := hJ _
    have hq₁ : (ι[G]).left ((𝟙 _ ≫ eSec G) y) ∈ L.L.U (J (𝟙 _ ≫ eSec G)) := by
      have := hJ ((𝟙 _ ≫ eSec G) ≫ (ι[G]).left)
      rw [congrArg J ri] at this
      exact this
    rw [val_pull hJ, val_one, val_of s (𝟙 _ ≫ eSec G) y J ![J (𝟙 _ ≫ eSec G), J (𝟙 _ ≫ eSec G)] (fun k => by
      fin_cases k
      · exact congrArg J ri
      · exact congrArg J (Category.comp_id _)), hs _ _ _ _ (Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hq₁, hq₀])]
    have a := pm _ (𝟙 _) y (fun _ => J (𝟙 _ ≫ eSec G)) (fun _ => J (𝟙 _ ≫ eSec G)) (fun _ => hq₁) (fun _ => hq₀)
    rw [Category.comp_id, Fintype.prod_unique, zpow_one] at a
    exact mul_eq_right.1 a.symm

end SymmetricBundle

theorem isSymmetric_iff_exists_gen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), L.IsSymmetric ↔ ∃ s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) :=
  fun _ _ _ _ L => ⟨SymmetricBundle.gen_of_isSymmetric L,
    fun ⟨s, hs, hr⟩ => SymmetricBundle.isSymmetric_of_gen L s hs hr⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinear
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.UT.OLinEnd

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_Oφ (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ p χ i) ^ Oε i =
      h (cP D T χ * p).left * (h (cP D T χ).left)⁻¹ * (h p.left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  rw [Fin.prod_univ_four, _root_.mul_comm (cP D T χ) p]
  show h (p * cP D _ χ).left ^ (1 : ℤ) * h (cP D _ χ).left ^ (-1 : ℤ) * h p.left ^ (-1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_Oφ_inv (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ p χ i) ^ Oinvε i =
      (h (cP D T χ * p).left)⁻¹ * h (cP D T χ).left * h p.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, _root_.mul_comm (cP D T χ) p]
  show h (p * cP D _ χ).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h p.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem exists_u (hG : GlobalFnsSt) (D : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O)
    (a : O) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_Oφ D (𝟙 _) (star a • χ) h)
        (prod_Oφ_inv D (oa.onB.act a) χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k
  refine (val_pull hJ _ _ _).trans (k.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem ros_unique (hG : GlobalFnsSt) (D : DegPre R) {f g : D.P.A ⟶ D.P.A}
    {u u' : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (u₀' : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u' (zero2 D.P.A)) (LB.oneGen D.P.L))
    (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D.P.A).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    val u' r z J = val u r z J := by
  have z2 : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  exact gen_unique D.P.isLB _ (zero2 D.P.A) z2 (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) hu' hu
    (fun y I hI => by
      have a₁ := val_corr hI u₀' (𝟙 _)
      have a₂ := val_corr hI u₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a₁ a₂
      exact a₁.trans a₂.symm) _ _ z J hJ

theorem main : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → ∀ a : O, ∃ E : EndU U.toUnifPre, E.aG = ιG.act a ∧ E.aA = ιA.act a ∧ E.aB = ιD.onB.act a ∧ (∀ χ, E.h χ = star a • χ) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), E.Act g g' ↔ GtAct ιD a g g' := by
  intro hL R _ _ _ I _ D A G _ _ _ U O _ _ _ ιD ιA ιG hO a
  have hG := hL.1.globalFns
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  have hr := ιD.onB.rosati (star a)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr
  choose v hv vv using exists_u hG D.toPre ιD a u hu u₀
  refine ⟨{ aG := ιG.act a, aA := ιA.act a, aB := ιD.onB.act a, homG := ιG.hom a, homA := ιA.hom a,
            homB := ιD.onB.hom a, h := DistribSMul.toAddMonoidHom D.toPre.X (star a), ext := hO.ext a,
            q_lin := fun e => hO.q_lin e a, i_lin := fun e => hO.i_lin e a, u := v, u_norm := hv,
            t_lin := fun e χ Z x z J hJ => ?_ }, rfl, rfl, rfl, fun _ => rfl, fun F _ _ g g' => ?_⟩
  · have e₁ := val_corr hJ (hL.2.2.2.1.tLin R I O D A G U.toUnifPre ιD ιA ιG hO e a u hu u₀ χ) x
    refine ((val_pull hJ _ _ _).symm.trans e₁.symm).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
    exact (val_pull hJ _ _ _).trans (vv χ _ (U.gt e).pG Z x z J hJ).symm
  · have k : ∀ χ z J, Good D.toPre.P.L z J →
        val (v χ) g.b.left z J = val u (𝟙 _ ≫ (lift (cP D.toPre _ χ) g.b).left) z J := fun χ z J hJ =>
      (congrArg (fun q => val (v χ) q z J) (Category.id_comp g.b.left).symm).trans (vv χ _ g.b _ (𝟙 _) z J hJ)
    refine and_congr Iff.rfl ⟨fun H u' hu' u₀' χ => corr_of_val D.toPre.P.isLB fun z J hJ => ?_, fun H χ z J hJ => ?_⟩
    · refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (H χ z J hJ).symm)
      exact (val_pull hJ _ _ _).trans ((ros_unique hG D.toPre hu hu' u₀ u₀' _ _ z J hJ).trans (k χ z J hJ).symm)
    · refine (val_corr hJ (H u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
      exact (val_pull hJ _ _ _).trans (k χ z J hJ).symm

end GlobalTheory.UT.OLinEnd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinearStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.exists_uniformizationEndomorphism_of_linear : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → ∀ a : O, ∃ E : EndU U.toUnifPre, E.aG = ιG.act a ∧ E.aA = ιA.act a ∧ E.aB = ιD.onB.act a ∧ (∀ χ, E.h χ = star a • χ) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), E.Act g g' ↔ GtAct ιD a g g' := by
  first | exact @GlobalTheory.UT.OLinEnd.main | exact GlobalTheory.UT.OLinEnd.main | (intros; apply GlobalTheory.UT.OLinEnd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjMul
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem rosatiAdj_mul : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (c : CubicalStr A L) (f g f' g' : A ⟶ A), RosatiAdj A L.L f g → RosatiAdj A L.L f' g' → RosatiAdj A L.L (f * f') (g * g') := by
  intro S A _ _ L c f g f' g' h h' s
  obtain ⟨U, hs, t, ht⟩ := h s
  obtain ⟨U', hs', t', ht'⟩ := h' s
  refine ⟨U ⊓ U', ⟨hs, hs'⟩, ?_⟩
  let W : (A ⊗ A).left.Opens := (A ⊗ A).hom ⁻¹ᵁ (U ⊓ U')
  have l : W ≤ (A ⊗ A).hom ⁻¹ᵁ U := fun _ hy => hy.1
  have l' : W ≤ (A ⊗ A).hom ⁻¹ᵁ U' := fun _ hy => hy.2
  let T : Over S := Over.mk (W.ι ≫ (A ⊗ A).hom)
  let ρ : T ⟶ A ⊗ A := Over.homMk W.ι rfl
  obtain ⟨x, y, hxy⟩ : ∃ x y : T ⟶ A, (lift x y).left = W.ι :=
    ⟨ρ ≫ fst A A, ρ ≫ snd A A, congrArg (fun q => q.left) (lift_comp_fst_snd ρ)⟩
  have pr : ∀ (a b : A ⟶ A) (V : Type) [CommGroup V] (k : (T.left ⟶ A.left) → V) (Y : Scheme.{0})
      (m : T.left ⟶ Y) (n : Y ⟶ (A ⊗ A).left), m ≫ n = W.ι →
      ∏ i, k (m ≫ n ≫ rosatiφ A a b i) ^ rosatiε i =
      k ((x ≫ a) * y).left * (k (x ≫ a).left)⁻¹ * (k y.left)⁻¹ * (k (x * (y ≫ b)).left)⁻¹ * k x.left *
        k (y ≫ b).left := fun a b V _ k Y m n e =>
    (Finset.prod_congr rfl fun i _ => by rw [← Category.assoc, e, hxy]).trans (prod_ros a b x y k)
  obtain ⟨u, hu, -⟩ := exists_gen L.isLB (φ' := fun i => W.ι ≫ rosatiφ A (f * f') (g * g') i) (ε' := rosatiε)
    (fun V _ k => by
      refine (DVR.prod_sum₂ (K := Fin 6 ⊕ Fin 6) (K' := thK ⊕ thK) (U := V) _
        (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
          (pr f g V k _ _ _ (Scheme.homOfLE_ι _ l)) (pr f' g' V k _ _ _ (Scheme.homOfLE_ι _ l')))
        (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x ≫ f) (x ≫ f') y k)
          (DVR.prod_neg _ _ (prod_cub x (y ≫ g) (y ≫ g') k)))).trans ?_
      refine Eq.trans ?_ ((pr (f * f') (g * g') V k _ (𝟙 _) W.ι (Category.id_comp _)).symm.trans
        (Finset.prod_congr rfl fun i _ => by rw [Category.id_comp]))
      rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L.L _ _ _ _
      (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ t ((A ⊗ A).left.homOfLE l))
        (LB.pullGen L.L _ _ t' ((A ⊗ A).left.homOfLE l')))
      (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (x ≫ f) (lift (x ≫ f') y)).left)
        (LB.invGen L.L _ _ (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift x (lift (y ≫ g) (y ≫ g'))).left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht' _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _))))
  exact ⟨u, hu⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaOfPowEqOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionThetaLocal

theorem exists_theta_of_pow_eq_one : ∀ (S₀ : Scheme.{0}) (G : Over S₀) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (S : Type) [CommRing S] [IsLocalRing S] (t : Spec (CommRingCat.of S) ⟶ S₀) (k : ℕ) (x : Over.mk t ⟶ G), x ^ k = 1 → ∃ θ : ThetaGrp G L.L (k : ℤ) (Over.mk t), θ.pt = x := by
  intro S₀ G _ _ L c S _ _ t k x hx
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_cubN c (1 : Over.mk t ⊗ G ⟶ G) (fst (Over.mk t) G ≫ x) (snd (Over.mk t) G) k
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := S) L.L L.isLB (K := Fin 2)
    ![x.left, (1 : Over.mk t ⟶ G).left] ![-(k : ℤ), k]
  have hm : (fst (Over.mk t) G ≫ x) ^ k = 1 := by
    rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have h1 : (fst (Over.mk t) G).left ≫ (1 : Over.mk t ⟶ G).left = (1 : Over.mk t ⊗ G ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have h2 : (fst (Over.mk t) G).left ≫ x.left = (fst (Over.mk t) G ≫ x).left := rfl
  have h3 : translPt G x = (fst (Over.mk t) G ≫ x) * snd (Over.mk t) G := rfl
  obtain ⟨w, hw, -⟩ := Geo.Tor.exists_gen L.isLB
    (φ' := ![(snd (Over.mk t) G).left, (translPt G x).left]) (ε' := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ]
      erw [h1, h2]
      rw [hm, h3]
      simp only [_root_.one_mul, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ u (LB.pullGen L.L _ _ e (fst (Over.mk t) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ he _))
  exact ⟨⟨x, w, hw⟩, rfl⟩

end GlobalTheory.TorsionThetaLocal
end
