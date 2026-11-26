module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionMultiplicationPullbackTraitDegreeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open IsLocalRing

namespace GlobalTheory.NsmulPull

variable {R : Type} [CommRing R] [IsDomain R]

theorem one_left (D : DegPre R) : (1 : D.P.A ⟶ D.P.A).left = D.P.A.hom ≫ eSec D.P.A := by
  have e : (toUnit D.P.A).left = D.P.A.hom := by simpa using Over.w (toUnit D.P.A)
  show (toUnit D.P.A ≫ η[D.P.A]).left = _
  rw [Over.comp_left, e]
  rfl

theorem unit_left (D : DegPre R) : (toUnit D.P.A ≫ η[D.P.A]).left = D.P.A.hom ≫ eSec D.P.A := one_left D

theorem comp_padd (D : DegPre R) (a x : D.P.A ⟶ D.P.A) :
    a ≫ padd D.P.A (𝟙 D.P.A) x = padd D.P.A a (a ≫ x) := by
  simp only [padd, ← Category.assoc, comp_lift, Category.comp_id]

theorem gen_shape (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k' k : ℕ) (hk : k ≤ k') (χ' χ : D.X)
    (κ : LB.Gen (kapLB D a k' k)) (hκ : κ.IsGen)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 D.P.A) χ') (D.Oφ a χ)) (Sum.elim Oε Oinvε))) (hu : u.IsGen) :
    ∃ eB : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB χ') (fun i => a.left ≫ D.famφB χ i))
        (Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i))), eB.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
        val eB r z J = val κ r z J * rigV D (r ≫ D.P.A.hom) z J ^ ((k' : ℤ) - k) * val u r z J := by
  have hL := D.P.isLB
  let ρ := LB.pullGen D.P.L (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom
  have hρ : ρ.IsGen := pullGen_isGen _ _ _ _ D.rig_gen _
  let t := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ κ (GeneratorPullback.powGen D.P.L _ _ ρ (k' - k))) u
  have ht : t.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hκ (powGen_isGen _ _ _ _ hρ _)) hu
  have e₁ := comp_padd D a (toUnit D.P.A ≫ D.c χ)
  have e₂ : a ≫ toUnit D.P.A = toUnit D.P.A := toUnit_unique _ _
  have e₃ : a.left ≫ D.P.A.hom = D.P.A.hom := Over.w a
  obtain ⟨eB, he, hv⟩ := exists_gen hL (φ' := Sum.elim (D.famφB χ') (fun i => a.left ≫ D.famφB χ i))
    (ε' := Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, Finset.univ_unique,
        Finset.prod_singleton, DegPre.famφB, DegPre.famε, DegPre.Oφ, Oε, Oinvε, kapLB, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Category.comp_id, ← Over.comp_left, e₁, ← Category.assoc, e₂, one_left, unit_left, Over.id_left, Nat.cast_sub hk, e₃, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, mul_one, zpow_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) t ht
  refine ⟨eB, he, fun Z r z J hJ => ?_⟩
  rw [hv Z r z J hJ, val_mul hJ, val_mul hJ, val_pow, val_pull hJ, show ((k' : ℤ) - k) = ((k' - k : ℕ) : ℤ) by omega, zpow_natCast]
  rfl

end GlobalTheory.NsmulPull

namespace GlobalTheory.NsmulPull

end GlobalTheory.NsmulPull

namespace GlobalTheory

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionMultiplicationPullbackTraitDegreeOne
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.MulExpand

open ReciprocityTheory.ChartRestriction.G.DVR (mulGen_isGen pullGen_isGen powGen_isGen val_pow cP comp_cP)
open GlobalTheory.UT

section
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}

abbrev prj (hD : IsPullDeg φ D D') : D'.P.A.left ⟶ D.P.A.left := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)

def om (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι) (q : Z ⟶ D'.P.A.left) : (Z.presheaf.stalk z)ˣ :=
  gw hD.w q z (J (q ≫ prj hD)) (J' q)

theorem pullB_val {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)} {b' : D'.SecB k x}
    (H : PullB hD x b b') {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'} (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') :
    sval b (r ≫ prj hD) z J = (∏ κ, om hD z J J' (r ≫ D'.famφB x κ) ^ DegPre.famε k κ).val * sval b' r z J' := by
  rw [sval_of b (r ≫ prj hD) z J (fun κ => J ((r ≫ D'.famφB x κ) ≫ prj hD)) (fun κ => by
    rw [Category.assoc r (prj hD), Category.assoc r _ (prj hD), ExpGTrans.famφB_pull hD x κ])]
  exact H Z r z _ _ (fun κ => hJ ((r ≫ D'.famφB x κ) ≫ prj hD)) (fun κ => hJ' (r ≫ D'.famφB x κ))

theorem prod_fam_unit (D : DegPre R) (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : (Sp R ⟶ D.P.A.left) → U) :
    ∏ κ, h (eSec D.P.A ≫ D.famφB α κ) ^ DegPre.famε k κ = h (eSec D.P.A) ^ (k : ℤ) := by
  have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by rw [Hom.one_def]; simp
  have a₀ : eSec D.P.A ≫ D.famφB α 0 = eSec D.P.A := Category.comp_id _
  have a₁ : eSec D.P.A ≫ D.famφB α 1 = eSec D.P.A ≫ D.famφB α 2 := congrArg (fun z => z.left)
    ((MonObj.comp_mul η[D.P.A] (𝟙 _) (cP D _ α)).trans
      ((congrArg (· * _) ((Category.comp_id _).trans e₁.symm)).trans (_root_.one_mul _)))
  have a₃ : eSec D.P.A ≫ D.famφB α 3 = eSec D.P.A := PullExp.eSec_comp_one
  rw [Fin.prod_univ_four, a₀, a₁, a₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, DegPre.famε, Matrix.cons_val]
  module

theorem mul_val_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') (m k k' : ℕ) (hk : k ≤ k') (x x' : D'.X) (hx : x' = m • x)
    (a : D'.P.A ⟶ D'.P.A) (ha : a = 𝟙 D'.P.A ^ m) (b : D.SecB k (hD.xe x)) (g : ∀ χ, D.SecB k' χ)
    (hM : MulSecB D m (hD.xe x) b (g (m • hD.xe x))) (b' : D'.SecB k x) (hb : PullB hD x b b')
    (c' : D'.SecB k' x') (hc : PullB hD x' (g (hD.xe x')) c')
    (eB : LB.Gen (LB.LinComb D'.P.L (Sum.elim (D'.famφB x') (fun i => a.left ≫ D'.famφB x i))
        (Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)))) (heB : eB.IsGen)
    (hn : ∀ y J, Good D'.P.L y J → val eB (eSec D'.P.A) y J = rigV D' (𝟙 _) y J ^ ((k' : ℤ) - k))
    (y : D'.P.A.left) (J') (hJ' : Good D'.P.L y J') :
    sval c' (𝟙 _) y J' = sval b' (𝟙 _ ≫ a.left) y J' * (val eB (𝟙 _) y J').val := by
  subst hx ha
  obtain ⟨u, hu, hun, hrel⟩ := hM
  have gp := pull_grp hD
  have hm : (mulA D'.P.A m).left ≫ prj hD = prj hD ≫ (mulA D.P.A m).left := GlobalTheory.ZH.TorsFrame.mulA_comm gp m
  have hφ : ∀ i, mulφB D' m x i ≫ prj hD = prj hD ≫ mulφB D m (hD.xe x) i := by
    rintro (i | i)
    · have := ExpGTrans.famφB_pull hD (m • x) i
      rw [map_nsmul] at this
      exact this
    · show ((mulA D'.P.A m).left ≫ D'.famφB x i) ≫ prj hD = prj hD ≫ (mulA D.P.A m).left ≫ D.famφB (hD.xe x) i
      rw [Category.assoc, ExpGTrans.famφB_pull hD x i, ← Category.assoc, hm, Category.assoc]
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB (φ' := mulφB D' m x)
    (ε := mulεB k k') eB heB
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ i, om hD z J J' (r ≫ mulφB D' m x i) ^ mulεB k k' i) * val eB r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [om, Category.assoc]
  have hr : PMaps hD.w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ) :=
    (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (prj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
  have he : eSec D'.P.A ≫ prj hD = spMap φ ≫ eSec D.P.A := hD.he
  have hem : eSec D'.P.A ≫ (mulA D'.P.A m).left = eSec D'.P.A := by
    have e₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) = η[D'.P.A] := by rw [Hom.one_def]; simp
    refine (GlobalTheory.ZH.TorsFrame.comp_mulA η[D'.P.A] m).trans ?_
    rw [← e₁, one_pow, e₁]; rfl
  have key := gen_unique' D.P.isLB (φ := fun i => prj hD ≫ mulφB D m (hD.xe x) i) (ε := mulεB k k')
    (fun V _ h => Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ mulεB k k' i) (hφ i))
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 (pullGen_isGen _ _ _ _ hu (prj hD)) ht (fun y I hI => by
      choose I' hI' using fun χ : Sp R' ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have hI' : Good D'.P.L y I' := hI'
      have p : (∏ i, om hD y I I' (eSec D'.P.A ≫ mulφB D' m x i) ^ mulεB k k' i) =
          om hD y I I' (eSec D'.P.A) ^ ((k' : ℤ) - k) := by
        rw [Fintype.prod_sum_type]
        simp only [mulφB, mulεB, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, hem, zpow_neg, Finset.prod_inv_distrib]
        rw [prod_fam_unit D' _ _ (om hD y I I'), prod_fam_unit D' _ _ (om hD y I I'), zpow_sub]
      have q : rigV D (spMap φ) y I = om hD y I I' (eSec D'.P.A) * rigV D' (𝟙 _) y I' := by
        have := hr _ (𝟙 _) y (fun _ => I (eSec D'.P.A ≫ prj hD)) (fun _ => I' (eSec D'.P.A))
          (fun _ => hI (eSec D'.P.A ≫ prj hD)) (fun _ => hI' (eSec D'.P.A))
        rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at this
        rw [rigV, rigV, val_of (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig _ y I (fun _ => I (eSec D'.P.A ≫ prj hD)) (fun _ => by rw [he]),
          val_of (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig _ y I' (fun _ => I' (eSec D'.P.A)) (fun _ => by rw [Category.id_comp])]
        exact this
      have s := val_corr hI hun (spMap φ)
      rw [val_pull hI, val_pow] at s
      rw [val_pull hI, hv' _ _ y I I' hI hI', p, hn y I' hI', ← mul_zpow, ← q, he, s,
        show ((k' : ℤ) - k) = ((k' - k : ℕ) : ℤ) by omega, zpow_natCast]
      rfl)
  choose J hJ using fun χ : D'.P.A.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ
  have k₁ := (val_pull hJ u (prj hD) (𝟙 _)).symm.trans ((key _ (𝟙 _) y J hJ).trans (hv' _ _ y J J' hJ hJ'))
  have k₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 hrel _ (𝟙 _ ≫ prj hD) y J hJ
  have k₃ := pullB_val hc (𝟙 _) y hJ hJ'
  have k₄ := pullB_val hb (𝟙 _ ≫ (mulA D'.P.A m).left) y hJ hJ'
  have k₅ : sval (g (hD.xe (m • x))) (𝟙 _ ≫ prj hD) y J = sval (g (m • hD.xe x)) (𝟙 _ ≫ prj hD) y J :=
    congrArg (fun χ => sval (g χ) (𝟙 _ ≫ prj hD) y J) (map_nsmul hD.xe m x)
  rw [Category.assoc (𝟙 _) (prj hD), ← hm, ← Category.assoc (𝟙 _) _ (prj hD), k₄, k₁, ← k₅, k₃, Fintype.prod_sum_type] at k₂
  simp only [mulφB, mulεB, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, zpow_neg, Finset.prod_inv_distrib] at k₂
  refine (Units.mul_right_inj _).1 (k₂.trans ?_)
  generalize (∏ κ, om hD y J J' (𝟙 _ ≫ D'.famφB (m • x) κ) ^ DegPre.famε k' κ) = P
  generalize (∏ κ, om hD y J J' ((𝟙 _ ≫ (mulA D'.P.A m).left) ≫ D'.famφB x κ) ^ DegPre.famε k κ) = Q
  rw [Units.val_mul, Units.val_mul]
  linear_combination (P.val * sval b' (𝟙 _ ≫ (mulA D'.P.A m).left) y J' * (val eB (𝟙 _) y J').val) * Q.mul_inv

end

theorem expand : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ), Odd m →
    ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G →
    ∀ (σ' : H0 T.U.LG.L 1) (f' : ∀ x, T.D'.toPre.SecB 1 x), (∀ x, PullB T.hD x (F₁.f (T.hD.xe x)) (f' x)) →
    (∀ e, T.U.ExpandsAt e 1 σ' f') →
    ∀ (f'' : ∀ x, T.D'.toPre.SecB (m ^ 2) x), (∀ x, PullB T.hD x (G.f (T.hD.xe x)) (f'' x)) →
    ∃ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (σ'' : H0 T.U.LG.L (m ^ 2)), uG.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
        sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) ∧
      ∀ e, T.U.ExpandsAt e (m ^ 2) σ'' f'' := by
  intro R _ _ _ _ D C W _ _ _ T m hm F₁ G hFG σ' f' hf' hσ' f'' hf''
  obtain ⟨hd, hV, hz⟩ := T.cdvr
  have hL := GlobalTheory.firstFiveLaws
  have hI : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have hGF := hL.1.globalFns
  have hG : IsSemiAbelian T.G := GlobalTheory.isSemiAbelian_of_unifPre_dvr W T.D' T.A T.G T.U.toUnifPre
  obtain ⟨E, hEG, -, hEB, hEh, -⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL W (maximalIdeal W) hI T.D' T.A T.G hG T.U).1 m
  have := E.homG
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hsm : Function.Injective fun χ : T.D'.toPre.X => m • χ := fun a b h => by
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
    exact smul_right_injective T.D'.toPre.X (Int.natCast_ne_zero.2 hm0) h'
  have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
  obtain ⟨β₀, hβ₀⟩ := ThetaSum.exists_gen_pow T.U.LG T.U.cubG T.U.symG T.U.symG_gen m E.aG hEG
  obtain ⟨β, hβ, hβ'⟩ := PullExp.exists_normalised T.U.LG.isLB E.aG _ _ β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL W (maximalIdeal W) hI T.D' T.A T.G hG T.U E (m ^ 2) 1 β hβ hβ'
  obtain ⟨σ₃, f₃, p₁, p₂, p₃, p₄⟩ := GlobalTheory.T.pullback_section_endomorphism_expansion W (maximalIdeal W) T.D' T.A T.G T.U.toUnifPre E hinj (m ^ 2) 1 β hβ κ₀
    hκ₀.1 hrel σ' f' hσ'
  have hf : f₃ = f'' := funext fun b => ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext (sec_ext_val T.D'.toPre.P.isLB fun y J hJ => by
    by_cases hb : b ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      obtain ⟨eB, heB, hvB⟩ := NsmulPull.gen_shape T.D'.toPre E.aB (m ^ 2) 1 hm2 (E.h χ) χ κ₀ hκ₀.1 (E.u χ) (E.u_norm χ).1
      have h := mul_val_pull hGF T.hD m 1 (m ^ 2) hm2 χ (E.h χ) (hEh χ) E.aB hEB _ G.f (hFG.1 _) _ (hf' χ) _ (hf'' _) eB heB
        (fun y J hJ => by
          have a := val_corr hJ hκ₀.2 (𝟙 _)
          have a' := val_corr hJ (E.u_norm χ).2 (𝟙 _)
          rw [val_pull hJ, Category.id_comp, val_one] at a a'
          rw [hvB _ _ y J hJ, a, a', _root_.one_mul, _root_.mul_one]
          exact congrArg (fun q => rigV T.D'.toPre q y J ^ _) (Over.w η[T.D'.toPre.P.A])) y J hJ
      rw [h, hvB _ _ y J hJ]
      exact p₃ χ _ _ y J hJ
    · choose J₀ hJ₀ using fun χ : T.D'.toPre.P.A.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
      have h := pullB_val (hf'' b) (𝟙 _) y hJ₀ hJ
      rw [GlobalTheory.PullComp.sval_eq_zero _ (hFG.2 _ fun χ e => hb ⟨T.hD.xe.symm χ, by
        rw [hEh, ← map_nsmul, ← e, AddEquiv.symm_apply_apply]⟩)] at h
      rw [GlobalTheory.PullComp.sval_eq_zero _ (p₄ b hb), (Units.mul_right_eq_zero _).1 h.symm])
  subst hf
  let ρ := LB.pullGen T.U.LG.L (K := PUnit) (fun _ => eSec T.G) (fun _ => 1) T.U.LG.rig T.G.hom
  have hρ : ρ.IsGen := pullGen_isGen _ _ _ _ T.U.LG.rigGen _
  obtain ⟨uG, huG, hv⟩ := exists_gen T.U.LG.isLB (K' := Fin 2) (φ' := ![𝟙 T.G.left, (mulA T.G m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]) (fun U _ h => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_three, Fintype.prod_unique]
      show h (𝟙 _) ^ ((m ^ 2 : ℕ) : ℤ) * h E.aG.left ^ (-((1 : ℕ) : ℤ)) * h (1 : T.G ⟶ T.G).left ^ (((1 : ℕ) : ℤ) - (m ^ 2 : ℕ)) *
        h (T.G.hom ≫ eSec T.G) ^ (((m ^ 2 - 1 : ℕ) : ℤ) * 1) = h (𝟙 _) ^ ((m ^ 2 : ℕ) : ℤ) * h (mulA T.G m).left ^ (-((1 : ℕ) : ℤ))
      rw [hEG, GlobalTheory.ZH.TorsFrame.one_left, _root_.mul_assoc, ← zpow_add, Nat.cast_sub hm2]
      simp)
    (LB.mulGen _ _ _ _ _ β (GeneratorPullback.powGen _ _ _ ρ (m ^ 2 - 1))) (mulGen_isGen _ _ _ _ _ _ _ hβ (powGen_isGen _ _ _ _ hρ _))
  refine ⟨uG, σ₃, huG, fun Z r z J hJ => ?_, p₁⟩
  rw [p₂ Z r z J hJ, hv _ _ z J hJ, val_mul hJ, val_pow, val_pull hJ, Category.comp_id, mul_comm,
    show r ≫ E.aG.left = r ≫ (mulA T.G m).left by rw [hEG],
    show (((m ^ 2 : ℕ) : ℤ) - (1 : ℕ)) = ((m ^ 2 - 1 : ℕ) : ℤ) by omega, zpow_natCast]

end GlobalTheory.Mum.MulExpand
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionMultiplicationPullbackTraitDegreeOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_multiplicationPullback_trait_degreeOne : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ), Odd m →
    ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G →
    ∀ (σ' : H0 T.U.LG.L 1) (f' : ∀ x, T.D'.toPre.SecB 1 x), (∀ x, PullB T.hD x (F₁.f (T.hD.xe x)) (f' x)) →
    (∀ e, T.U.ExpandsAt e 1 σ' f') →
    ∀ (f'' : ∀ x, T.D'.toPre.SecB (m ^ 2) x), (∀ x, PullB T.hD x (G.f (T.hD.xe x)) (f'' x)) →
    ∃ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (σ'' : H0 T.U.LG.L (m ^ 2)), uG.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
        sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) ∧
      ∀ e, T.U.ExpandsAt e (m ^ 2) σ'' f'' := by
  first | exact @GlobalTheory.Mum.MulExpand.expand | exact GlobalTheory.Mum.MulExpand.expand | (intros; apply GlobalTheory.Mum.MulExpand.expand <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackTraitGenericCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackTraitGenericCondition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem gs_scal_over_self {W : Type} [CommRing W] {X Z : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of W)) (g : X ⟶ X)
    (hg : g ≫ q = q) (p : Z ⟶ X) (z : Z) (a : W) :
    gs (p ≫ g) z ⊤ (scal q a) = gs p z ⊤ (scal q a) := by
  have e : (g.app ⊤).hom (scal q a) = scal q a := by
    have e' : scal (g ≫ q) a = (g.app ⊤).hom (scal q a) := rfl
    rw [← e', hg]
  exact (gs_pull p g z ⊤ trivial (scal q a)).symm.trans (congrArg (gs p z ⊤) e)

theorem pullMul_trait_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ) (a : W)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J, Good C.P.L.L z J →
      sval S p z J = (val u (p ≫ C.α) z J).val * sval θ₀ (p ≫ (mulA C.A.A m).left) z J) →
    ∀ (σ : SecK C.P.L.L T.β 1) (σ₂ : SecK C.P.L.L T.β (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval θ₀ p' z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ₂ p z J = gs p z ⊤ (scal T.G.hom a) * sval S p' z J := by
  intro R _ _ _ D C W _ _ _ T m a u θ₀ S hS σ σ₂ hσ hσ₂ Z p p' hp z J hJ
  have e1 := GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m
  have e2 := GlobalTheory.ZH.TorsFrame.mulA_comm C.α_cart m
  have h : (p ≫ (mulA T.G m).left) ≫ T.β = (p' ≫ (mulA C.A.A m).left) ≫ C.α := by
    rw [Category.assoc, Category.assoc, e1, e2, ← Category.assoc, hp, Category.assoc]
  rw [hσ₂ Z p z J hJ, hσ Z _ _ h z J hJ, hS Z p' z J hJ, hp,
    gs_scal_over_self T.G.hom _ (Over.w (mulA T.G m)) p z a]
  exact mul_left_comm _ _ _

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackTraitGenericConditionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicationPullback_trait_genericCondition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ) (a : W)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J, Good C.P.L.L z J →
      sval S p z J = (val u (p ≫ C.α) z J).val * sval θ₀ (p ≫ (mulA C.A.A m).left) z J) →
    ∀ (σ : SecK C.P.L.L T.β 1) (σ₂ : SecK C.P.L.L T.β (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval θ₀ p' z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ₂ p z J = gs p z ⊤ (scal T.G.hom a) * sval S p' z J := by
  first | exact @GlobalTheory.Mum.pullMul_trait_generic | exact GlobalTheory.Mum.pullMul_trait_generic | (intros; apply GlobalTheory.Mum.pullMul_trait_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackCommutingEndomorphismGenera
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackCommutingEndomorphismGenera
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_secK_pullMul_gen : ∀ {X Y : Scheme.{0}} (L : LB X), L.IsLB → ∀ (β : Y ⟶ X) (g : Y ⟶ Y) (h : X ⟶ X), g ≫ β = β ≫ h →
    ∀ (k k' : ℕ) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, h] ![(k' : ℤ), -(k : ℤ)])), u.IsGen → ∀ (σ : SecK L β k),
    ∃ σ₂ : SecK L β k', ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval σ₂ r z J = (val u (r ≫ β) z J).val * sval σ (r ≫ g) z J := by
  intro X Y L hL β g h hc k k' u hu σ
  have hu' := DVR.pullGen_isGen L _ _ u hu β
  have hF : FormEq (Sum.elim (fun i => g ≫ (fun _ : Fin 1 => β) i) (fun i => β ≫ (![𝟙 X, h] : Fin 2 → (X ⟶ X)) i))
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) ![(k' : ℤ), -(k : ℤ)]) (fun _ : Fin 1 => β) (fun _ => (k' : ℤ)) := by
    intro U _ f
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id, hc, zpow_neg]
    rw [mul_comm (f β ^ _)]
    exact mul_inv_cancel_left _ _
  obtain ⟨σ₂, hσ₂⟩ := exists_sec hL hF (pullMulSec σ g (LB.pullGen L _ _ u β) hu')
  refine ⟨σ₂, fun Z r z J hJ => ?_⟩
  rw [hσ₂ Z r z J hJ, sval_pullMulSec σ g _ hu' r z hJ, val_pull hJ u β r, mul_comm]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackCommutingEndomorphismGeneraStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pullback_commuting_endomorphism_generator : ∀ {X Y : Scheme.{0}} (L : LB X), L.IsLB → ∀ (β : Y ⟶ X) (g : Y ⟶ Y) (h : X ⟶ X), g ≫ β = β ≫ h →
    ∀ (k k' : ℕ) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, h] ![(k' : ℤ), -(k : ℤ)])), u.IsGen → ∀ (σ : SecK L β k),
    ∃ σ₂ : SecK L β k', ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval σ₂ r z J = (val u (r ≫ β) z J).val * sval σ (r ≫ g) z J := by
  first | exact @GlobalTheory.Mum.exists_secK_pullMul_gen | exact GlobalTheory.Mum.exists_secK_pullMul_gen | (intros; apply GlobalTheory.Mum.exists_secK_pullMul_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbacksDifferByUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbacksDifferByUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Trait.bijective_appTop {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) :
    Function.Bijective T.G.hom.appTop.hom := by
  have hd : IsDiscreteValuationRing W := T.cdvr.1
  have := T.U.smooth
  have := T.U.separated
  have := C.semi.quasiCompact
  have : QuasiCompact T.G.hom := MorphismProperty.of_isPullback (P := @QuasiCompact) T.cart.1 this
  exact GlobalFunctionsDvrGeneric.bij_of_generic T.G
    (GlobalFunctionsDvrPowers.bijective_of_iso T.U.gen (GlobalTheory.allSixLaws.1.globalFns _ T.A.A T.A.isAb))

theorem Trait.exists_unit_scal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (c : Γ(T.G.left, ⊤)ˣ) :
    ∃ v : Wˣ, scal T.G.hom (v : W) = c.val := by
  let e : W ≃+* Γ(T.G.left, ⊤) := RingEquiv.ofBijective
    (T.G.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)
    (T.bijective_appTop.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv))
  exact ⟨Units.map e.symm.toMonoidHom c, e.apply_symm_apply c.val⟩

theorem Trait.carries_mulPull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    u.IsGen →
    ∀ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    uG.IsGen → ∀ (b : W) (σ' : H0 T.U.LG.L 1) (σ : SecK C.P.L.L T.β 1), T.Carries b σ' σ →
    ∀ (σ₂ : SecK C.P.L.L T.β (m ^ 2)) (σ'' : H0 T.U.LG.L (m ^ 2)),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
      sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) →
    ∃ v : Wˣ, T.Carries (b * v) σ'' σ₂ := by
  intro R _ _ _ _ D C W _ _ _ T m u hu uG huG b σ' σ hcar σ₂ σ'' h₂ h''
  have hm := GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m
  obtain ⟨a, ha, hP⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move C.P.L.isLB T.U.LG.isLB T.ℓ ((isGen_iff _).1 T.ℓ_gen)
    (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![𝟙 T.G.left, (mulA T.G m).left]
    ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)] T.β (fun k => by
      fin_cases k
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
      · exact hm) u hu
  obtain ⟨c, hc⟩ := GlobalTheory.ZM.Coord.exists_global_unit (DVR.linComb_isLB _ T.U.LG.isLB _ _) ha huG
  obtain ⟨v, hv⟩ := T.exists_unit_scal c
  refine ⟨v, fun Z r z J J' hJ hJ' => ?_⟩
  have e₁ : (r ≫ T.β) ≫ (mulA C.G m).left = (r ≫ (mulA T.G m).left) ≫ T.β := by
    rw [Category.assoc, Category.assoc, hm]
  have hp : val u (r ≫ T.β) z J = (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ (m ^ 2) *
      (gw T.ℓ (r ≫ (mulA T.G m).left) z (J ((r ≫ (mulA T.G m).left) ≫ T.β)) (J' (r ≫ (mulA T.G m).left)))⁻¹) *
      val a r z J' := by
    refine (hP Z r z _ _ (fun k => ?_) (fun k => hJ' (r ≫ _))).trans ?_
    · fin_cases k
      · exact hJ ((r ≫ T.β) ≫ 𝟙 _)
      · have := hJ ((r ≫ T.β) ≫ (mulA C.G m).left)
        exact (congrArg (fun q => q z ∈ C.P.L.L.U (J ((r ≫ T.β) ≫ (mulA C.G m).left))) e₁).mp this
    · refine congrArg (· * val a r z J') ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e₁, zpow_natCast, zpow_neg, pow_one]
  have hq : val a r z J' = gm r z ⊤ c * val uG r z J' := by
    have hm' := hJ'.mem ![𝟙 T.G.left, (mulA T.G m).left] r
    exact (congrArg (gm r z _) (hc _)).trans ((map_mul _ _ _).trans (congrArg (· * val uG r z J') (gm_res r z _ hm' _)))
  have hs : gs (r ≫ (mulA T.G m).left) z ⊤ (scal T.G.hom b) = gs r z ⊤ (scal T.G.hom b) := by
    refine (gs_pull r (mulA T.G m).left z ⊤ trivial _).symm.trans (congrArg (gs r z ⊤) ?_)
    show ((mulA T.G m).left ≫ T.G.hom).appTop.hom _ = _
    rw [Over.w]; rfl
  have hbv : gs r z ⊤ (scal T.G.hom (b * v)) = gs r z ⊤ (scal T.G.hom b) * (gm r z ⊤ c).val := by
    rw [← gs_unit r z ⊤ trivial, ← hv, ← gs_mul r z ⊤ trivial, scal, scal, scal, map_mul, map_mul]
  rw [h₂ Z r z J hJ, h'' Z r z J' hJ', hcar Z _ z J J' hJ hJ', hp, hq, hs, hbv, Category.comp_id, pow_one]
  generalize gw T.ℓ (r ≫ (mulA T.G m).left) z _ _ = g
  simp only [Units.val_mul]
  linear_combination (gs r z ⊤ (scal T.G.hom b) * (gm r z ⊤ c).val * (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ (m ^ 2)).val *
    (val uG r z J').val * sval σ' (r ≫ (mulA T.G m).left) z J') * g.inv_mul

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbacksDifferByUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicationPullbacks_differ_by_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    u.IsGen →
    ∀ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    uG.IsGen → ∀ (b : W) (σ' : H0 T.U.LG.L 1) (σ : SecK C.P.L.L T.β 1), T.Carries b σ' σ →
    ∀ (σ₂ : SecK C.P.L.L T.β (m ^ 2)) (σ'' : H0 T.U.LG.L (m ^ 2)),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
      sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) →
    ∃ v : Wˣ, T.Carries (b * v) σ'' σ₂ := by
  first | exact @GlobalTheory.Mum.Trait.carries_mulPull | exact GlobalTheory.Mum.Trait.carries_mulPull | (intros; apply GlobalTheory.Mum.Trait.carries_mulPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOddMultiplicationPullbackAtTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exp_mulPull_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)), MulFam m F₁ G → MulSecK C m θ₀ S → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  intro R _ _ _ hR D C m hm F₁ G θ₀ S hMF hMS W _ _ _ T a b ha hE
  obtain ⟨σ, ⟨σ', f', hcar, hpull, hexp⟩, hgen⟩ := hE
  obtain ⟨u, hu, hS⟩ := hMS
  obtain ⟨σ₂, hσ₂⟩ := GlobalTheory.T.exists_section_pullback_commuting_endomorphism_generator C.P.L.L C.P.L.isLB T.β (mulA T.G m).left (mulA C.G m).left
    (GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m) 1 (m ^ 2) u hu σ
  have hgen₂ := GlobalTheory.T.multiplicationPullback_trait_genericCondition R D C W T m a u θ₀ S hS σ σ₂ hgen hσ₂
  obtain ⟨G', hG'⟩ := GlobalTheory.Mum.exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc (m ^ 2) G
  obtain ⟨uG, σ'', huG, hσ'', hexp''⟩ := GlobalTheory.T.expansion_multiplicationPullback_trait_degreeOne R hR D C W T m hm F₁ G hMF σ' f' hpull hexp G'.f hG'
  obtain ⟨v, hv⟩ := GlobalTheory.T.multiplicationPullbacks_differ_by_unit R hR D C W T m u hu uG huG b σ' σ hcar σ₂ σ'' hσ₂ hσ''
  exact ⟨v, σ₂, ⟨σ'', G'.f, hv, hG', hexp''⟩, hgen₂⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOddMultiplicationPullbackAtTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_oddMultiplicationPullback_at_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)), MulFam m F₁ G → MulSecK C m θ₀ S → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  first | exact @GlobalTheory.Mum.exp_mulPull_trait | exact GlobalTheory.Mum.exp_mulPull_trait | (intros; apply GlobalTheory.Mum.exp_mulPull_trait <;> assumption)
end
