module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiSpread

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_finite_cube_induction (X : Type) [AddCommGroup X] [Module.Finite ℤ X] :
    ∃ S : Set X, S.Finite ∧ ∀ E : X → Prop, (∀ x ∈ S, E x) →
      (∀ a a' b, E a → E a' → E b → E (a + a') → E (a + b) → E (a' + b) → E (a + a' + b)) → ∀ x, E x := by
  have h : AddMonoid.FG X := AddGroup.fg_iff_addMonoid_fg.1 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  obtain ⟨G, hG, hGfin⟩ := AddMonoid.fg_iff.mp h
  refine ⟨insert 0 (G ∪ Set.image2 (· + ·) G G),
    (hGfin.union (hGfin.image2 _ hGfin)).insert _, fun E hS hE x => ?_⟩
  have h₁ : ∀ g ∈ G, E g := fun g hg => hS g (Or.inr (Or.inl hg))
  have key : E x ∧ ∀ g ∈ G, E (g + x) := by
    refine AddSubmonoid.induction_of_closure_eq_top_left (motive := fun x => E x ∧ ∀ g ∈ G, E (g + x))
      hG x ⟨hS 0 (Or.inl rfl), fun g hg => by rw [add_zero]; exact h₁ g hg⟩ fun g hg y hy => ⟨hy.2 g hg, fun g' hg' => ?_⟩
    rw [← add_assoc]
    exact hE g' g y (h₁ _ hg') (h₁ _ hg) hy.1 (hS _ (Or.inr (Or.inr ⟨g', hg', g, hg, rfl⟩))) (hy.2 _ hg') (hy.2 _ hg)
  exact key.1

theorem exists_gen_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (j : K → L.ι) (hj : ∀ y, y ∈ LB.wchart L φ j) (V : Y.Opens) (hV : ∀ y, y ∈ V) (u : Γ(Y, V)ˣ) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j' : K → L.ι),
      r z ∈ LB.wchart L φ j' → gm r z (LB.wchart L φ j') (t.s j') = trF φ ε r z j' j * gm r z V u := by
  let t : LB.Gen (LB.LinComb L φ ε) := ⟨fun j' =>
    res (le_inf le_rfl (fun y _ => hj y) : LB.wchart L φ j' ≤ LB.wchart L φ j' ⊓ LB.wchart L φ j)
      ((LB.LinComb L φ ε).g j' j) * res (fun y _ => hV y : LB.wchart L φ j' ≤ V) u⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j' : K → L.ι),
      r z ∈ LB.wchart L φ j' → gm r z (LB.wchart L φ j') (t.s j') = trF φ ε r z j' j * gm r z V u :=
    fun Z r z j' h => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ h _).trans (gm_linComb L φ ε r z j' j h (hj _))) (gm_res r z _ h _))
  refine ⟨t, fun (i i' : K → L.ι) => unit_ext fun y hy => ?_, key⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i hy.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y i i' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i' hy.2))).trans ?_)
  rw [← trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hj _), _root_.mul_assoc]
  rfl

theorem exists_unit_near {X Y : Scheme.{0}} (f : Y ⟶ X) [IsPreimmersion f] (y : Y) (a : (Y.presheaf.stalk y)ˣ) :
    ∃ (U : X.Opens) (u : Γ(X, U)ˣ), f y ∈ U ∧ gm f y U u = a := by
  obtain ⟨s, hs⟩ := f.stalkMap_surjective y a.val
  obtain ⟨U, hU, g, rfl⟩ := X.presheaf.exists_germ_eq s
  have hu : IsUnit ((X.presheaf.germ U (f y) hU).hom g) :=
    (isUnit_map_iff (f.stalkMap y).hom _).1 (hs ▸ a.isUnit)
  have hm : f y ∈ X.basicOpen g := (X.mem_basicOpen g (f y) hU).2 hu
  refine ⟨X.basicOpen g, (X.toRingedSpace.isUnit_res_basicOpen g).unit, hm, Units.ext ?_⟩
  refine (gs_unit f y _ hm _).symm.trans ((gs_res f y (X.basicOpen_le g) hm g).trans ((gs_eq f y U hU g).trans ?_))
  exact (Scheme.Hom.germ_stalkMap_apply f U y hU g).symm.trans hs

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def Extends {T : Over (Spec (CommRingCat.of R))} (κ : TK R ⟶ T) (χ : D.X) : Prop :=
  ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (cP D T χ).left) (fun _ => -1)), t.IsGen ∧
    ∀ z J, Good D.P.L z J → val t κ.left z J = val (D.psi χ) (𝟙 _) z J

theorem exists_extends (χ : D.X) (z : (TK R).left) : ∃ V : (Spec (CommRingCat.of R)).Opens, jK R z ∈ V ∧
    ∀ W : (Spec (CommRingCat.of R)).Opens, W ≤ V → ∀ κ : TK R ⟶ TW W, Extends D κ χ := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R) (S := FractionRing R)
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  obtain ⟨j, hj⟩ := exists_chart D.P.isLB (D.xK χ z)
  obtain ⟨U, u, hU, e⟩ := exists_unit_near (jK R) z
    (gm (𝟙 (TK R).left) z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => j)) ((D.psi χ).s (fun _ => j)))
  refine ⟨U ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U j, ⟨hU, hj⟩, fun W hW κ => ?_⟩
  have hκ : κ.left ≫ W.ι = jK R := Over.w κ
  obtain ⟨t, ht, vt⟩ := exists_gen_of_chart D.P.isLB (K := PUnit) (fun _ => (cP D (TW W) χ).left) (fun _ => -1)
    (fun _ => j) (fun y => Set.mem_iInter.2 fun _ => (hW y.2).2) (W.ι ⁻¹ᵁ U) (fun y => (hW y.2).1) (pullU W.ι U u)
  refine ⟨t, ht, fun z' J hJ => ?_⟩
  obtain rfl : z = z' := Subsingleton.elim _ _
  have q : κ.left ≫ (cP D (TW W) χ).left = 𝟙 _ ≫ D.xK χ :=
    (congrArg (fun q => q.left) (comp_cP D κ χ)).trans (Category.id_comp _).symm
  refine (vt _ κ.left z _ (hJ.mem _ _)).trans (Eq.trans ?_
    (gen_trans (D.psi_gen χ) (𝟙 _) z (j' := fun _ => j) (hJ.mem _ _) (Set.mem_iInter.2 fun _ => hj)).symm)
  refine congrArg₂ (· * ·) ?_ ((gm_pull κ.left W.ι z U (hW (κ.left z).2).1 u).trans (by rw [hκ]; exact e))
  exact congrArg (fun ψ => ∏ _k : PUnit.{1}, gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U j) (D.P.L.g (J ψ) j) ^ (-1 : ℤ)) q

theorem prod_elim {A U K K' : Type} [CommGroup U] [Fintype K] [Fintype K'] (h : A → U) {φ : K → A} {ε : K → ℤ}
    {φ' : K' → A} {ε' : K' → ℤ} {c c' : U} (e : ∏ k, h (φ k) ^ ε k = c) (e' : ∏ k, h (φ' k) ^ ε' k = c') :
    ∏ k, h (Sum.elim φ φ' k) ^ Sum.elim ε ε' k = c * c' := by
  rw [Fintype.prod_sum_type, ← e, ← e']; rfl

theorem prod_punit {A U : Type} [CommGroup U] (h : A → U) (a : A) (n : ℤ) :
    ∏ k : PUnit.{1}, h ((fun _ => a) k) ^ (fun _ => n) k = h a ^ n := Fintype.prod_unique _

theorem Extends.cube (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (κ : TK R ⟶ T) (a a' b : D.X)
    (h₁ : Extends D κ a) (h₂ : Extends D κ a') (h₃ : Extends D κ b) (h₄ : Extends D κ (a + a'))
    (h₅ : Extends D κ (a + b)) (h₆ : Extends D κ (a' + b)) : Extends D κ (a + a' + b) := by
  obtain ⟨t₁, g₁, v₁⟩ := h₁
  obtain ⟨t₂, g₂, v₂⟩ := h₂
  obtain ⟨t₃, g₃, v₃⟩ := h₃
  obtain ⟨t₄, g₄, v₄⟩ := h₄
  obtain ⟨t₅, g₅, v₅⟩ := h₅
  obtain ⟨t₆, g₆, v₆⟩ := h₆
  obtain ⟨t, gt, vt⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => (cP D T (a + a' + b)).left) (ε' := fun _ => -1)
    (fun U _ h => by
      have p := prod_cub (cP D T a) (cP D T a') (cP D T b) h
      have q : (toUnit T).left ≫ eSec D.P.A = (1 : T ⟶ D.P.A).left := rfl
      refine (prod_elim h (prod_elim h (prod_elim h (prod_punit h _ _) (prod_punit h _ _)) (prod_punit h _ _))
        (prod_neg _ _ (prod_elim h (prod_elim h (prod_elim h (prod_punit h _ _) (prod_punit h _ _)) (prod_punit h _ _))
          (prod_elim h (prod_punit h _ _) p)))).trans (Eq.trans ?_ (prod_punit h _ _).symm)
      rw [q]
      simp only [cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₄ t₅) t₆)
      (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₁ t₂) t₃)
        (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit T).left)
          (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (cP D T a) (lift (cP D T a') (cP D T b))).left)))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₄ g₅) g₆)
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₁ g₂) g₃)
        (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) (pullGen_isGen _ _ _ _ D.cub.isGen _)))))
  refine ⟨t, gt, fun z J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      th D z J (cP D _ a) (cP D _ a') (cP D _ b) :=
    (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).trans (by simp only [comp_cP])
  have vρ : val (LB.pullGen D.P.L _ _ D.rig (toUnit T).left) κ.left z J = val D.rigK (𝟙 _) z J := by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp]
    exact congrArg (fun q => val D.rig q z J) (Over.w κ)
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (cP D T a) (lift (cP D T a') (cP D T b))).left) κ.left z J = th D z J (cP D _ a) (cP D _ a') (cP D _ b) :=
    (val_cub D.cub κ hJ _ _ _).trans (by simp only [comp_cP])
  rw [c, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ] at e
  refine (vt _ _ z J hJ).trans (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (v₄ z J hJ) (v₅ z J hJ))) (v₆ z J hJ)))
    ((val_inv _ _).trans (congrArg (·⁻¹) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (v₁ z J hJ) (v₂ z J hJ))) (v₃ z J hJ)))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) vρ vc)))))))).trans ?_)
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) -e'

theorem nonempty_psiOn {W : (Spec (CommRingCat.of R)).Opens} (κ : TK R ⟶ TW W) (h : ∀ χ, Extends D κ χ) :
    Nonempty (PsiOn D W) := by
  choose t gt vt using h
  refine ⟨⟨t, gt, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  have c : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (t χ) κ.left) (D.psi χ) :=
    corr_of_val D.P.isLB fun z J hJ => (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; exact vt χ z J hJ)
  have q : (jK R ⁻¹ᵁ W).ι ≫ κ.left = jK R ∣_ W := by
    have hκ : κ.left ≫ W.ι = jK R := Over.w κ
    rw [← cancel_mono W.ι, morphismRestrict_ι, Category.assoc, hκ]
  have e := (val_pull hJ _ _ _).symm.trans (val_corr hJ c (jK R ⁻¹ᵁ W).ι)
  rw [q] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  rw [Category.id_comp, Category.id_comp]
  exact e

theorem exists_psiOn (hB : D.TauBimult) : ∃ W : (Spec (CommRingCat.of R)).Opens,
    genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W) := by
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨S, hS, ind⟩ := exists_finite_cube_induction D.X
  choose V hV ext using fun χ => exists_extends D χ z
  let W : (Spec (CommRingCat.of R)).Opens := ⟨⋂ χ ∈ S, V χ, hS.isOpen_biInter fun χ _ => (V χ).isOpen⟩
  have hz : jK R z ∈ W := Set.mem_iInter₂.2 fun χ _ => hV χ
  let κ : TK R ⟶ TW W := Over.homMk (IsOpenImmersion.lift W.ι (jK R) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact TauPull.jK_mem y W ⟨_, hz⟩)) (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨W, ?_, nonempty_psiOn D κ (ind _ (fun χ hχ => ext χ W (fun x hx => Set.mem_iInter₂.1 hx χ hχ) κ)
    (Extends.cube D hB κ))⟩
  exact ((genericPoint_spec (Spec (CommRingCat.of R))).mem_open_set_iff W.isOpen).2 ⟨_, trivial, hz⟩

end PsiSpread

theorem psiOnExists : PsiOnExistsSt := fun _ _ _ _ _ D => PsiSpread.exists_psiOn D.toPre D.tau_bimult

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceThickening
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

namespace EndTorus

theorem idempotent_trivial {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) [IsAdicComplete I R]
    (e : ℕ) (x : R ⧸ I ^ (e + 1)) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hle : I ^ (e + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero e)
  have h0 : a₀ * a₀ - a₀ ∈ I := hle (Ideal.Quotient.eq.1 hx)
  have hm : (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic := by monicity!
  obtain ⟨a, ha, hI⟩ := HenselianRing.is_henselian (I := I) _ hm a₀ (by simpa [sq] using h0) (by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (2 * a₀ - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    convert I.mul_mem_left 4 h0 using 1
    simp
    ring)
  have hnil : ∀ y ∈ I, IsNilpotent (Ideal.Quotient.mk (I ^ (e + 1)) y) := fun y hy =>
    ⟨e + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hy _)⟩
  have ha' : a * (a - 1) = 0 := by
    have := ha.eq_zero
    simp at this
    linear_combination this
  rcases mul_eq_zero.1 ha' with h | h
  · left
    refine hx.eq_zero_of_isNilpotent (hnil _ ?_)
    simpa [h] using hI
  · right
    have h1 : a = 1 := sub_eq_zero.1 h
    have := hx.one_sub.eq_zero_of_isNilpotent (by simpa [h1] using hnil _ hI)
    exact (sub_eq_zero.1 this).symm

theorem connectedSpace_thickening {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)
    [hC : IsAdicComplete I R] (e : ℕ) : ConnectedSpace (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := by
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : PreconnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))) := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    obtain ⟨x, hx, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hU
    rcases idempotent_trivial I e x hx with rfl | rfl <;> simp
  exact ({ toNonempty := inferInstance } : ConnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))))

theorem torusEndOf_iff_appTop {S : Scheme.{0}} {X : Type} [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) : TorusEndOf X h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem isMonHom_of_mono {S : Scheme.{0}} {A B C : Over S} [MonObj A] [MonObj B] [MonObj C]
    (t : A ⟶ B) (i : B ⟶ C) [Mono i] [IsMonHom i] [IsMonHom (t ≫ i)] : IsMonHom t := by
  constructor
  · rw [← cancel_mono i, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end EndTorus

open EndTorus in
theorem gtCoord_end_torus_abelian : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G), IsMonHom a → (∃! h : D.X →+ D.X, ∃ t, TorusEndOf D.X h t ∧ g.i ≫ a = t ≫ g.i) ∧ ∃! b : thickObj R I e D.P.A ⟶ thickObj R I e D.P.A, IsMonHom b ∧ a ≫ g.q = g.q ≫ b := by
  intro _ R _ _ I hR D e G _ _ g a ha
  obtain ⟨hN, -, -, hC⟩ := hR
  have := connectedSpace_thickening I e
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hk := g.isKernel
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D.P.A) :=
    { comm := inferInstance
      smooth := by have := D.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g.i ≫ a ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D.X _ hB (g.i ≫ a ≫ g.q) inferInstance).trans (Hom.one_def)
  have : Mono g.i := by
    have : Mono (η[thickObj R I e D.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  constructor
  · let t := hk.lift (g.i ≫ a) (toUnit _) (by rw [Category.assoc, h1])
    have ht : t ≫ g.i = g.i ≫ a := hk.lift_fst _ _ _
    have : IsMonHom (t ≫ g.i) := ht ▸ inferInstance
    have : IsMonHom t := isMonHom_of_mono t g.i
    obtain ⟨h, hh⟩ := SplitTorusHom.exists_addMonoidHom t
    refine ⟨h, ⟨t, (torusEndOf_iff_appTop _ _).2 hh, ht.symm⟩, ?_⟩
    rintro h' ⟨t', h₁, h₂⟩
    obtain rfl : t' = t := by rw [← cancel_mono g.i, ht, h₂]
    ext χ
    exact SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
      (((torusEndOf_iff_appTop _ _).1 h₁ χ).symm.trans (hh χ))
  · obtain ⟨b, hb, hq⟩ := FlatQuotient.exists_desc g.q g.i (a ≫ g.q) hk h1
    have := FlatQuotient.epi_of_flat_surjective g.q
    refine ⟨b, ⟨hb, hq.symm⟩, ?_⟩
    rintro b' ⟨-, h⟩
    rw [← cancel_epi g.q, ← h, hq]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyLinearEquivOfRel
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamDimension

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem nonempty_linearEquiv_of_rel {F M N : Type*} [Semiring F] [AddCommMonoid M] [AddCommMonoid N] [Module F M]
    [Module F N] (P : M → N → Prop) (h₁ : ∀ m, ∃! n, P m n) (h₂ : ∀ n, ∃! m, P m n)
    (ha : ∀ m n m' n', P m n → P m' n' → P (m + m') (n + n')) (hs : ∀ (c : F) m n, P m n → P (c • m) (c • n)) :
    Nonempty (M ≃ₗ[F] N) := by
  choose f hf hf' using h₁
  let g : M →ₗ[F] N :=
    { toFun := f
      map_add' := fun m m' => (hf' _ _ (ha _ _ _ _ (hf m) (hf m'))).symm
      map_smul' := fun c m => (hf' _ _ (hs c _ _ (hf m))).symm }
  refine ⟨LinearEquiv.ofBijective g ⟨fun m m' e => ?_, fun n => ?_⟩⟩
  · have e' : f m = f m' := e
    exact (h₂ (f m')).unique (e' ▸ hf m) (hf m')
  · obtain ⟨m, hm, -⟩ := h₂ n
    exact ⟨m, (hf' _ _ hm).symm⟩

section Comb

variable {X Y : Scheme.{0}} {n : ℕ}

def IsComb {M : LB Y} (b : Fin n → LB.Sec M) (a : Fin n → Γ(Y, ⊤)) (s : LB.Sec M) : Prop :=
  ∀ j, s.f j = ∑ i, resTop _ (a i) * (b i).f j

theorem exists_isComb {M : LB Y} (b : Fin n → LB.Sec M) (a : Fin n → Γ(Y, ⊤)) : ∃ s, IsComb b a s :=
  ⟨⟨fun j => ∑ i, resTop _ (a i) * (b i).f j, fun j j' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (a i) (b i)).compat j j'⟩, fun _ => rfl⟩

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem isComb_iff_sval (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (a : Fin n → Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) :
    IsComb b a s ↔ ∀ y J, Good L y J →
      sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (a i) * sval (b i) (𝟙 Y) y J := by
  refine ⟨fun h y J hJ => SectionScalarValuation.sval_lin a b h _ y hJ, fun h j => ?_⟩
  obtain ⟨t, ht⟩ := exists_isComb b a
  rw [← ht j]
  exact sec_ext_val hL (fun y J hJ => (h y J hJ).trans (SectionScalarValuation.sval_lin a b ht _ y hJ).symm) j

theorem exists_basis_of_gen (hL : L.IsLB) {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : FormEq (Sum.elim (fun k => 𝟙 Y ≫ φ k) φ₃) (Sum.elim ε ε₃) φ' ε')
    {A : Type} (g : A → Γ(Y, ⊤)) (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ s, ∃! c : Fin n → A, IsComb b (fun i => g (c i)) s) :
    ∃ b' : Fin n → LB.Sec (LB.LinComb L φ' ε'), ∀ s, ∃! c : Fin n → A, IsComb b' (fun i => g (c i)) s := by
  have h' : FormEq (Sum.elim (fun k => 𝟙 Y ≫ φ' k) φ₃) (Sum.elim ε' fun k => -ε₃ k) φ ε := fun U _ w => by
    have := h U w
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp] at this ⊢
    rw [← this]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  choose b' hb' using fun i => exists_sec hL h (pullMulSec (b i) (𝟙 Y) u hu)
  refine ⟨b', fun s => ?_⟩
  have hu' := invGen_isGen L _ _ u hu
  obtain ⟨t, ht⟩ := exists_sec hL h' (pullMulSec s (𝟙 Y) (LB.invGen L _ _ u) hu')
  refine (existsUnique_congr fun c => ?_).1 (hb t)
  rw [isComb_iff_sval hL, isComb_iff_sval hL]
  refine forall₃_congr fun y J hJ => ?_
  rw [ht _ _ y J hJ, sval_pullMulSec _ _ _ hu' _ y hJ, val_inv, Category.id_comp, Units.mul_inv_eq_iff_eq_mul,
    Finset.sum_mul]
  refine Eq.congr_right (Finset.sum_congr rfl fun i _ => ?_)
  rw [hb' i _ _ y J hJ, sval_pullMulSec _ _ _ hu _ y hJ, Category.id_comp, _root_.mul_assoc]

end Comb

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_basis_famSec (hT : SecTwistSt) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ b : Fin (k ^ D.P.g) → FamFree.FamSec D F k α,
      ∀ s, ∃! c : Fin (k ^ D.P.g) → F, IsComb b (fun i => gF D F (c i)) s := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P k hk F (jFK (R := R) F ≫ jK R) (cP D (TF (R := R) F) α)
  let q : (DegPre.BF D F).left ⟶ (TK R).left := (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F
  let u := LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi α) D.rigK) q
  have hu : u.IsGen := pullGen_isGen _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen α) (pullGen_isGen _ _ _ _ D.rig_gen _)) _
  refine exists_basis_of_gen D.P.isLB (φ' := DegPre.famφ D F α) (ε' := DegPre.famε k) u hu (fun U _ h => by
      have p := prod_fam D F (𝟙 _) α k h
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      have a₁ : q ≫ D.xK α = (cP D (DegPre.BF D F) α).left :=
        congrArg (fun x => x.left) (comp_cP D (fst (TF (R := R) F) D.P.A) α)
      have a₂ : q ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left :=
        congrArg (fun x : DegPre.BF D F ⟶ D.P.A => x.left)
          (MonObj.comp_one (M := D.P.A) (fst (TF (R := R) F) D.P.A))
      have a₃ : translPt D.P.A (cP D (TF (R := R) F) α) = cP D (DegPre.BF D F) α * DegPre.prB D F := by
        rw [translPt, comp_cP]; rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Category.id_comp, a₁, a₂, a₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one]
      rw [← _root_.mul_assoc]) (gF D F) b (fun s => ?_)
  exact (Equiv.existsUnique_congr (Equiv.piCongrRight fun _ : Fin (k ^ D.P.g) =>
      (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.toEquiv) fun _ => Iff.rfl).2 (hb s)

theorem nonempty_fam_equiv (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) :
    Nonempty (Fam D F k ≃ₗ[F] (D.X ⧸ FamFree.multiples D k → Fin (k ^ D.P.g) → F)) := by
  let rep : D.X ⧸ FamFree.multiples D k → D.X := Quotient.out
  have hrep : ∀ c, QuotientAddGroup.mk (rep c) = c := fun c => Quotient.out_eq c
  choose b hb using fun c => exists_basis_famSec (D := D) (F := F) hT hk (rep c)
  refine nonempty_linearEquiv_of_rel
    (fun s z => ∀ c, IsComb (b c) (fun i => gF D F (z c i)) (s.s (rep c))) (fun s => ?_) (fun z => ?_) ?_ ?_
  · choose z hz hz' using fun c => hb c (s.s (rep c))
    exact ⟨z, hz, fun z' h => funext fun c => hz' c _ (h c)⟩
  · choose σ hσ using fun c => exists_isComb (b c) (fun i => gF D F (z c i))
    refine (existsUnique_congr fun s => forall_congr' fun c => ?_).1
      (FamFree.existsUnique_fam hG hB hk rep hrep σ)
    exact ⟨fun h => h ▸ hσ c, fun h => SecOps.sec_ext fun j => (h j).trans (hσ c j).symm⟩
  · intro s z s' z' h h' c j
    rw [add_f, h c j, h' c j, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, map_add (f := _), resTop, add_mul]
  · intro a s z h c j
    rw [smul_f, h c j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, resTop, _root_.mul_assoc]

theorem finrank_fam (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) :
    Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.rank + D.P.g) := by
  obtain ⟨e⟩ := nonempty_fam_equiv (D := D) (F := F) hG hT hB hk
  have hc : Nat.card (D.X ⧸ FamFree.multiples D k) = k ^ D.rank := AddSubgroup.index_range_nsmul D.X k
  have : Finite (D.X ⧸ FamFree.multiples D k) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite (D.X ⧸ FamFree.multiples D k)
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Module.finrank_fin_fun, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hc, smul_eq_mul, pow_add]

theorem main : GlobalFnsSt → CubeSt → SquareSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D.toPre F k) ∧ Module.finrank F (Fam D.toPre F k) = k ^ (D.toPre.rank + D.toPre.P.g) :=
  fun hG _ _ hT _ _ _ _ D _ _ _ _ hk => finrank_fam hG hT D.tau_bimult hk

end GlobalTheory.FamDimension
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegDataIsPullDeg
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.exists_degData_isPullDeg : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolBaseChangeSt → _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R'), I.map φ ≤ I' → ∀ (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Out.PsiOn D.toPre W) → (_root_.ReciprocityTheory.ChartRestriction.G.Out.specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R' I') (hD : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPullDeg φ D.toPre D'.toPre), hD.W = W ∧ D'.toPre.P.g = D.toPre.P.g := by
  intro hP hG R R' _ _ _ _ I I' φ hle D W hψ hgen
  obtain ⟨D₀, hE, hT, hI, hF⟩ := D
  obtain ⟨D', hD, hW, hg⟩ :=
    _root_.GlobalTheory.DegPull.exists_isPullDeg hP R R' φ D₀ W hψ hgen
  refine ⟨⟨D', _root_.GlobalTheory.PsiEvenPull.psiEven_pull hG R R' φ D₀ D' hD hE,
    _root_.GlobalTheory.tauBimult_of_isPullDeg hG R R' φ D₀ D' hD hT, ?_, ?_⟩, hD, hW, hg⟩
  · intro χ hχ
    exact _root_.GlobalTheory.psiIn_of_isPullDeg R R' φ D₀ D' hD χ I I' hle
      (hI _ fun h => hχ (hD.xe.map_eq_zero_iff.mp h))
  · intro n
    refine ((hF n).preimage hD.xe.injective.injOn).subset ?_
    intro χ hχ h
    exact hχ (_root_.GlobalTheory.psiIn_of_isPullDeg R R' φ D₀ D' hD χ (I ^ n) (I' ^ n)
      (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hle n) h)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNMul
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefPhi
open GlobalTheory.UT.CoefBasic

theorem cubN_mul {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k n : ℕ) (a m x : A) :
    cubN θ (k * n) a m x = cubN θ n a (m ^ k) x * cubN θ k 1 m x ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e : cubN θ (k * (n + 1)) a m x = cubN θ (k * n) a m x * cubN θ k (a * (m ^ k) ^ n) m x := by
      rw [Nat.mul_succ, cubN, Finset.prod_range_add, cubN, cubN]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_add, pow_mul, _root_.mul_assoc]
    have e' : cubN θ (n + 1) a (m ^ k) x = cubN θ n a (m ^ k) x * θ (a * (m ^ k) ^ n) (m ^ k) x :=
      Finset.prod_range_succ _ _
    rw [e, e', ih, h.N_split k (a * (m ^ k) ^ n), pow_succ (cubN θ k 1 m x)]
    ac_rfl

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frame {k : ℕ} (p : QkPt D F k) (w : Frm D F k p.g.b) (hw : w.IsGen) (g₀ : GtPtF D F)
    (ω₀ : Frm D F k g₀.b) (h₀ : ω₀.IsGen) (b : TF (R := R) F ⟶ D.P.A) (hb : b = g₀.b * p.g.b) :
    ∃ ω₁ : Frm D F k b, ω₁.IsGen ∧ ∀ z J, Good D.P.L z J → val ω₁ (𝟙 _) z J =
      val ω₀ (𝟙 _) z J * val w (𝟙 _) z J * val (g₀.s p.y) (𝟙 _) z J * cubN (th D z J) k 1 p.g.b g₀.b := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (1 : TF (R := R) F ⟶ D.P.A) p.g.b g₀.b k
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      refine Eq.trans (prod_sum₂ (K := (Fin 2 ⊕ Fin 2) ⊕ Fin 4) (K' := Fin 8) (U := U) _
        (prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 4) (U := U) _
          (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_line k g₀.b h) (prod_line k p.g.b h))
          (prod_gt g₀.b p.y h)) rfl) ?_
      rw [prod_line, cPoint_y, hb, mul_comm g₀.b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ ω₀ w) (g₀.s p.y)) N)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ h₀ hw) (g₀.isGen _)) hN)
  refine ⟨u, hu, fun z J hJ => ?_⟩
  have e := vN _ (𝟙 _) z J hJ
  simp only [Category.id_comp, Over.id_left] at e
  exact (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) e))

theorem coef_phi : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (g₀ g₁ : GtPtF D.toPre F), g₀.IsAdd p.g g₁ → ∀ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen → ∃ ω₁ : Frm D.toPre F k g₁.b, ω₁.IsGen ∧ (g₀.IsZero → FrmOne ω₀ → ∀ z J, Good D.toPre.P.L z J → val ω₁ (𝟙 _) z J = val w (𝟙 _) z J) ∧ ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → ∀ (wN : Frm D.toPre F N q.g.b) (w₀ : Frm D.toPre F N g₀.b) (w₁ : Frm D.toPre F N g₁.b), (wN.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val wN (𝟙 _) z J = val w (𝟙 _) z J ^ n) → (w₀.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₀ (𝟙 _) z J = val ω₀ (𝟙 _) z J ^ n) → (w₁.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₁ (𝟙 _) z J = val ω₁ (𝟙 _) z J ^ n) → ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N q wN s s' → ∀ α, coef s' g₀ w₀ (α + q.y) = coef s g₁ w₁ α := by
  intro hL R _ _ _ I _ D F _ _ _ k _ p w hw g₀ g₁ hadd ω₀ h₀
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  obtain ⟨ω₁, h₁, v₁⟩ := exists_frame p w hw g₀ ω₀ h₀ g₁.b hb
  refine ⟨ω₁, h₁, fun hz ho z J hJ => ?_, ?_⟩
  · have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 hz
    have c : cubN (th D.toPre z J) k 1 p.g.b g₀.b = 1 := by rw [z₁, C.N_one]
    rw [v₁ z J hJ, ho.2 z J hJ, z₂ _ z J hJ, c, _root_.one_mul, _root_.mul_one, _root_.mul_one]
  · rintro n _ _ rfl ⟨qy, qg, qe⟩ hy hg wN w₀ w₁ ⟨hN, vN⟩ ⟨-, v₀⟩ ⟨hw₁, vw₁⟩ s s' hΦ α
    dsimp only at hy hg
    subst hy hg
    have H := (phiRel_iff hL.1.globalFns _ wN hN s s').1 hΦ
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    have e₁ := H α _ rfl _ (lift (𝟙 (TF (R := R) F)) g₀.b) z J hJ
    have t : lift (𝟙 (TF (R := R) F)) g₀.b ≫ DegPre.trPt D.toPre F p.g.b = lift (𝟙 (TF (R := R) F)) g₁.b := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
      · rw [lift_snd, hb, Category.assoc]
        refine (congrArg (_ ≫ ·) (tr_pr D.toPre F p.g.b)).trans ?_
        rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
    dsimp only at e₁ vN
    rw [t, uVal, lift_fst_assoc, lift_fst, lift_snd, Category.id_comp, Over.id_left, val_mul hJ, vN z J hJ,
      cubN_mul C] at e₁
    have e₂ := gt_nsmul (𝟙 (TF (R := R) F)) hJ g₀ α p.y n
    rw [Category.id_comp, Over.id_left, cPoint_y] at e₂
    have e₃ := hs α z J hJ
    rw [isCoef_coef g₁ hw₁ α s z J hJ]
    dsimp only
    rw [e₁, v₀ z J hJ, vw₁ z J hJ, v₁ z J hJ]
    simp only [_root_.mul_assoc, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    have a₂ := congrArg Additive.ofMul e₂
    have a₃ := congrArg Additive.ofMul e₃
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂

end GlobalTheory.UT.CoefPhi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValTorusPointAndTranslate
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusCoord

theorem val_torus_point_and_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Geo.Tor.Good D.P.L z J → ∀ χ : D.X, Geo.Tor.val (g.t χ) (τ ≫ g.i).left z J = Geo.Tor.gm τ.left z ⊤ (charUnit _ D.X χ) ∧ Geo.Tor.val (g.t χ) ((τ ≫ g.i) * y).left z J = Geo.Tor.gm τ.left z ⊤ (charUnit _ D.X χ) * Geo.Tor.val (g.t χ) y.left z J := by
  intro R _ _ I D e G _ _ g Z τ y z J hJ χ
  refine ⟨?_, GlobalTheory.TorusCoord.val_torus g χ hJ τ y⟩
  rw [GlobalTheory.TorusCoord.val_congr g χ (_root_.mul_one (τ ≫ g.i)).symm z J, GlobalTheory.TorusCoord.val_torus g χ hJ τ 1,
    GlobalTheory.TorusCoord.val_unit g χ hJ, _root_.mul_one]

end GlobalTheory.TorusCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameOfOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.TorusWeight

theorem gs_map {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)) :
    gs r z U f = (r.stalkMap z).hom (gs (𝟙 X) (r z) U f) := by
  rw [gs_eq r z U h, gs_eq (𝟙 X) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h f).symm

theorem val_const {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (a : Γ(Y, ⊤))
    (h : ∀ y J, Good L y J → (val t (𝟙 _) y J).val = gs (𝟙 _) y ⊤ a) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    (val t r z J).val = gs r z ⊤ a := by
  have hJ' : Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ (r ≫ ψ)
  have e := h (r z) _ hJ'
  rw [val_of t (𝟙 _) (r z) _ (fun k => J (r ≫ φ k)) (fun k => by rw [Category.id_comp])] at e
  have hm := hJ.mem φ r
  refine (gs_unit r z _ hm _).symm.trans ((gs_map r z _ hm _).trans (Eq.trans ?_ (gs_map r z ⊤ trivial a).symm))
  exact congrArg _ ((gs_unit (𝟙 Y) (r z) _ hm _).trans e)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem normd_one {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    {u : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    val u (1 : TF (R := R) F ⟶ D.P.A).left z J = 1 :=
  (val_pull hJ u (eSec D.P.A) (toUnit (TF (R := R) F)).left).symm.trans ((val_corr hJ hu.2 _).trans (val_one _))

theorem psi_zero (hB : D.TauBimult) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi 0) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J = 1 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have z0 : (0 : D.X) + 0 = 0 := add_zero 0
  have hpt : ∀ a b c : D.X, a = b → ∀ (r : (TF (R := R) F).left ⟶ _),
      val (D.tau a c) r z J = val (D.tau b c) r z J := by rintro a b c rfl r; rfl
  have hpp : ∀ a b : D.X, a = b → ∀ (r : (TF (R := R) F).left ⟶ _), val (D.psi a) r z J = val (D.psi b) r z J := by
    rintro a b rfl r; rfl
  have hτ0 := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 0
  rw [hpt _ _ _ z0, cPoint_zero, C.face] at hτ0
  have t00 := (mul_left_cancel hτ0).symm
  have hψ := UUA.psi_add (𝟙 (TF (R := R) F)) hJ (0 : D.X) 0
  rw [hpp _ _ z0, t00, _root_.one_mul, _root_.mul_assoc] at hψ
  have h1 := left_eq_mul.1 hψ
  rw [Over.id_left, Category.id_comp] at h1
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) h1
  exact (val_pull hJ (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (toUnit (TK R)).left (jFK (R := R) F)).symm

theorem txFrame_of_one (hB : D.TauBimult) {N : ℕ} (p : QkPt D F N) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) {w : Frm D F N p.g.b} (hw : FrmOne w) : TXFrame N p w := by
  refine ⟨hw.1, fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
  · have e : val (p.g.s p.y) (𝟙 _) z J = 1 := Units.ext (by
      rw [hτ.2 _ z J hJ, hy, ofAdd_zero, map_one, CoefBasic.cst_eq]; exact map_one _)
    rw [hw.2 z J hJ, e, hτ.1, normd_one hν z hJ, one_pow, _root_.one_mul]
  · rw [hw.2 z J hJ, hτ.1, normd_one hκ z hJ, one_pow, _root_.one_mul, hy, psi_zero hB z hJ]

theorem sval_const {k : ℕ} (α : D.X) (ζ : F) (s s' : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) :
    (∀ j, s'.f j = DegPre.constBF D F ζ _ * s.f j) ↔
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        sval s' ρ.left z J = sval s ρ.left z J *
          gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) j, r z ∈ LB.wchart D.P.L (DegPre.famφ D F α) j →
      gs r z (LB.wchart D.P.L (DegPre.famφ D F α) j) (DegPre.constBF D F ζ _ * s.f j) =
        gs r z (LB.wchart D.P.L (DegPre.famφ D F α) j) (s.f j) *
          gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
    fun Z r z j hm => (gs_mul r z _ hm _ _).trans ((mul_comm _ _).trans (congrArg₂ (· * ·) rfl
      ((gs_res r z le_top hm _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _))))
  constructor
  · intro h T ρ z J hJ
    exact (congrArg (gs ρ.left z _) (h _)).trans (key _ ρ.left z _ (hJ.mem _ _))
  · intro h j
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB y
    have e := h _ (𝟙 _) y J hJ
    refine Eq.trans ?_ (key _ (𝟙 _) y j hy).symm
    refine (sec_trans s' (𝟙 _) y hy (hJ.mem _ (𝟙 _))).trans ?_
    rw [sec_trans s (𝟙 _) y hy (hJ.mem _ (𝟙 _)), _root_.mul_assoc]
    exact congrArg _ e

theorem phiRel_tor (hG : GlobalFnsSt) {N : ℕ} (p : QkPt D F N) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) {w : Frm D F N p.g.b} (hw : FrmOne w) (s s' : Fam D F N) :
    PhiRel D F N p w s s' ↔
      ∀ α j, (s'.s α).f j = DegPre.constBF D F (τ (Multiplicative.ofAdd α)).val _ * (s.s α).f j := by
  have tr : DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.id_comp]; exact tr_fst D F _
    · rw [Category.id_comp]
      refine (tr_pr D F _).trans ?_
      rw [hτ.1, MonObj.comp_one, _root_.mul_one]
  have v : ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      (uVal D F N α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val =
        gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd α)).val) := by
    intro α T ρ z J hJ
    have C : IsCub (th D z J) := isCub_cubV D.cub hJ
    have hu : uVal D F N α p.g.b ρ z J = 1 := by
      rw [uVal, hτ.1]
      simp only [MonObj.comp_one]
      unfold cubN
      simp only [C.face₃, C.face₂, Finset.prod_const_one, inv_one, _root_.mul_one]
    have h₁ := val_const (p.g.s α) _ (hτ.2 α) (ρ ≫ fst _ _).left z hJ
    have h₂ := val_const w 1 (fun y J hJ => by
      rw [hw.2 y J hJ, gs_eq _ _ ⊤ trivial, map_one, map_one]; rfl) (ρ ≫ fst _ _).left z hJ
    rw [gs_eq _ _ ⊤ trivial, map_one, map_one] at h₂
    rw [hu, _root_.one_mul, val_mul hJ, Units.val_mul, h₁, h₂, _root_.mul_one]
  rw [phiRel_iff hG p w hw.1]
  constructor
  · intro H α
    refine (sval_const α _ _ _).2 fun T ρ z J hJ => ?_
    have := H α α (by rw [hy, add_zero]) T ρ z J hJ
    rwa [v α T ρ z J hJ, tr, Category.comp_id] at this
  · intro H α β h T ρ z J hJ
    obtain rfl : α = β := by rw [← h, hy, add_zero]
    rw [v α T ρ z J hJ, tr, Category.comp_id]
    exact (sval_const α _ _ _).1 (H α) T ρ z J hJ

theorem torus_weight : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) τ, p.y = 0 → IsTor τ p.g → ∀ w, TXFrame N p w → FrmOne w ∧ ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N p w s s' ↔ ∀ α j, (s'.s α).f j = DegPre.constBF D.toPre F (τ (Multiplicative.ofAdd α)).val _ * (s.s α).f j := by
  intro hL R _ _ _ I hI D A G _ _ _ U F _ _ _ N hN p τ hy hτ w hw
  obtain ⟨w₀, hw₀⟩ := (CoefBasic.coef_basic R D.toPre F N p.g).2.1 hτ.1
  have h₁ : FrmOne w := ⟨hw.1, fun z J hJ =>
    ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p).2 w w₀ hw (txFrame_of_one D.tau_bimult p hy hτ hw₀) z J hJ).trans (hw₀.2 z J hJ)⟩
  exact ⟨h₁, phiRel_tor hL.1.globalFns p hy hτ h₁⟩

end GlobalTheory.UT.TorusWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaPow
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPow

theorem prod_fam_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) {U : Type} [CommGroup U]
    (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.famφ D F 0 i) ^ DegPre.famε k i = h (DegPre.prB D F).left ^ k := by
  have hmul : ∀ {T : Over (Spec (CommRingCat.of R))} (a b : T ⟶ D.P.A), padd D.P.A a b = a * b := by
    intro T a b
    unfold padd
    rfl
  have hc0 : D.c 0 = 1 := by
    have h2 := D.c_add 0 0
    rw [add_zero, hmul] at h2
    exact mul_eq_left.mp h2.symm
  have h1 : toUnit (DegPre.BF D F) ≫ D.c 0 = toUnit (DegPre.BF D F) ≫ η[D.P.A] := by
    rw [hc0]
    rfl
  have h3 : padd D.P.A (DegPre.prB D F) (toUnit (DegPre.BF D F) ≫ η[D.P.A]) = DegPre.prB D F := by
    rw [hmul]
    exact mul_one _
  have hφ : DegPre.famφ D F 0 = ![(DegPre.prB D F).left, (DegPre.prB D F).left,
      (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left, (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left] := by
    unfold DegPre.famφ
    rw [h1, h3]
  have hε : DegPre.famε k = ![(k : ℤ) - 1, 1, -1, 1] := rfl
  rw [Fin.prod_univ_four, hφ, hε]
  show h (DegPre.prB D F).left ^ ((k : ℤ) - 1) * h (DegPre.prB D F).left ^ (1 : ℤ) *
      h (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left ^ (-1 : ℤ) * h (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left ^ (1 : ℤ) =
      h (DegPre.prB D F).left ^ k
  simp only [zpow_neg, zpow_one]
  rw [_root_.inv_mul_cancel_right, ← zpow_add_one, sub_add_cancel, zpow_natCast]

theorem exists_theta_pow : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∃ (θ : LB.Sec (D.P.L.pull (DegPre.prB D F).left)) (σ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε n))), (∃ j, θ.f j ≠ 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval σ r z J = sval (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left) (ε := fun _ => 1) θ r z J ^ n := by
  intro hT R _ _ D F _ _ n _
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.FamFree.exists_sec_ne_zero (D := D) (F := F) hT (k := 1) le_rfl 0
  have hF₁ : FormEq (DegPre.famφ D F 0) (DegPre.famε 1)
      (fun _ : PUnit => (DegPre.prB D F).left) (fun _ => (1 : ℤ)) := by
    intro U _ h
    rw [prod_fam_zero D F 1 h]
    simp
  obtain ⟨θ, hθ⟩ := exists_sec D.P.isLB hF₁ s₀
  have hθne : ∃ j, θ.f j ≠ 0 := by
    by_contra hc
    push Not at hc
    have g0 : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens), gs f y U 0 = 0 := by
      intro Y X f y U
      unfold gs
      split <;> simp
    apply hs₀
    intro j
    refine (sec_ext_val D.P.isLB (s' := H1.SectionArithmetic.secZero _) (fun y J hJ => ?_) j).trans rfl
    rw [← hθ _ (𝟙 _) y J hJ]
    exact ((congrArg (gs _ y _) (hc _)).trans (g0 _ _ _)).trans (g0 _ _ _).symm
  let P := H1.SectionArithmetic.powSec (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left)
    (ε := fun _ => (1 : ℤ)) (fun _ : Fin n => θ)
  have hFn : FormEq (fun p : Fin n × PUnit => (DegPre.prB D F).left) (fun _ => (1 : ℤ))
      (DegPre.famφ D F 0) (DegPre.famε n) := by
    intro U _ h
    rw [prod_fam_zero D F n h]
    simp
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB hFn P
  refine ⟨θ, σ, hθne, fun Z r z J hJ => ?_⟩
  rw [hσ Z r z J hJ, H1.SectionArithmetic.sval_powSec _ r z hJ]
  simp

end GlobalTheory.ThetaPow
end
end
