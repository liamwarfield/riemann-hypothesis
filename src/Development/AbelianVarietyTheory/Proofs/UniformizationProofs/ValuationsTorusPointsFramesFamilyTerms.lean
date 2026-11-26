module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenV
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
  {X : Scheme.{0}} {L : LB X}

theorem isDominant_ι : IsDominant (ιS hϖ hv).left := by
  refine ⟨?_⟩
  show DenseRange (PrimeSpectrum.comap (algebraMap (Ov v) F))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (Ov v) F)]
  exact bot_le

theorem ι_inj [X.IsSeparated] : Function.Injective fun ψ : (TO hϖ hv).left ⟶ X => (ιS hϖ hv).left ≫ ψ := by
  intro a b h
  have := isDominant_ι hϖ hv
  have : IsReduced (TO hϖ hv).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (Ov v))))
  exact ext_of_isDominant (ιS hϖ hv).left h

theorem gs_ι (z : (TF (R := V) F).left) (a : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) :
    gs (ιS hϖ hv).left z ⊤ a = cst F z (ιr (v := v) a) := by
  rw [cst_eq, gs_eq _ z ⊤ trivial]
  exact congrArg ((TF (R := V) F).left.presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap (Ov v) F)) a)

theorem sec_int [X.IsSeparated] (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → ((TO hϖ hv).left ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε))
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ X) → U), ∏ i, h ((ιS hϖ hv).left ≫ φ i) ^ ε i = 1) :
    ∃ a : F, 0 ≤ v a ∧ ∀ z J, Good L z J → sval s (ιS hϖ hv).left z J = cst F z a := by
  obtain ⟨s₀, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    refine Eq.trans ?_ ((hf U (Function.extend (fun ψ => (ιS hϖ hv).left ≫ ψ) h 1)).trans (Fintype.prod_empty _).symm)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(ι_inj hϖ hv).extend_apply]) s
  have le : (⊤ : (TO hϖ hv).left.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → ((TO hϖ hv).left ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨ιr (v := v) (((TO hϖ hv).left.presheaf.map (homOfLE le).op).hom (s₀.f PEmpty.elim)), v_ιr _,
    fun z J hJ => ?_⟩
  rw [← hs _ _ z J hJ, sval_of s₀ _ z J PEmpty.elim (fun k => k.elim), ← gs_ι hϖ hv]
  exact (gs_res _ z le trivial _).symm

abbrev FS (V F : Type) [CommRing V] [IsDomain V] [Field F] [Algebra (FractionRing V) F] (X : Scheme.{0}) : Type 1 :=
  ∀ (U : Type) [CommGroup U], (((TF (R := V) F).left ⟶ X) → U) → U

def HV (L : LB X) (σ : FS V F X)
    (f : ∀ z : (TF (R := V) F).left, (((TF (R := V) F).left ⟶ X) → L.ι) → (TF (R := V) F).left.presheaf.stalk z)
    (x : F) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((TO hϖ hv).left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ X) → U), ∏ i, h ((ιS hϖ hv).left ≫ φ i) ^ ε i = σ U h) ∧
    ∀ z J, Good L z J → f z J = cst F z x * (val t (ιS hϖ hv).left z J).val

variable {hϖ hv}

theorem HV.mul {σ σ' : FS V F X} {f f'} {x x' : F} (H : HV hϖ hv L σ f x) (H' : HV hϖ hv L σ' f' x') :
    HV hϖ hv L (fun U _ h => σ U h * σ' U h) (fun z J => f z J * f' z J) (x * x') := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_,
    fun z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs U h) (hs' U h)
  · rw [val_mul hJ]
    simp only [e z J hJ, e' z J hJ, cst_eq, map_mul, Units.val_mul]
    ring

theorem HV.one : HV hϖ hv L (fun _ _ _ => 1) (fun _ _ => 1) 1 :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L (Y := (TO hϖ hv).left),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun z J _ => by rw [val_one, cst_eq, map_one, Units.val_one, _root_.mul_one]⟩

theorem HV.congr {σ σ' : FS V F X} {f f'} {x : F} (H : HV hϖ hv L σ f x)
    (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) (hf : ∀ z J, Good L z J → f' z J = f z J) :
    HV hϖ hv L σ' f' x := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hs U h).trans (hσ U h), fun z J hJ => (hf z J hJ).trans (e z J hJ)⟩

theorem HV.pow {σ : FS V F X} {f} {x : F} (H : HV hϖ hv L σ f x) (n : ℕ) :
    HV hϖ hv L (fun U _ h => σ U h ^ n) (fun z J => f z J ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using HV.one
  | succ n ih => simpa only [pow_succ] using ih.mul H

theorem HV.smul {σ : FS V F X} {f} {x : F} (H : HV hϖ hv L σ f x) (c : F) :
    HV hϖ hv L σ (fun z J => cst F z c * f z J) (c * x) := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  refine ⟨K, _, φ, ε, t, ht, hs, fun z J hJ => ?_⟩
  simp only [e z J hJ, cst_eq, map_mul, _root_.mul_assoc]

theorem HV.le [X.IsSeparated] (hL : L.IsLB) {σ : FS V F X} {f} {x x' : F} (H : HV hϖ hv L σ f x)
    (H' : HV hϖ hv L σ f x') : v x ≤ v x' := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  have hu := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht')
  obtain ⟨a, ha, hav⟩ := sec_int hϖ hv hL (Geo.Tor.genSec _ hu) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [hs, hs', mul_inv_cancel])
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have b := hav z J hJ
  rw [sval_genSec _ hu _ z hJ, val_mul hJ, val_inv] at b
  have c : x' = x * a := by
    apply cstH_inj (R := V) z
    have d := (e z J hJ).symm.trans (e' z J hJ)
    rw [map_mul, ← cst_eq, ← cst_eq, ← cst_eq, ← b, Units.val_mul, ← _root_.mul_assoc, d, _root_.mul_assoc,
      Units.mul_inv, _root_.mul_one]
  rw [c, AddValuation.map_mul]
  exact le_add_of_nonneg_right ha

theorem HV.cmp [X.IsSeparated] (hL : L.IsLB) {σ σ' : FS V F X} {f f'} {x x' : F} (H : HV hϖ hv L σ f x)
    (H' : HV hϖ hv L σ' f' x') (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h)
    (hf : ∀ z J, Good L z J → f' z J = f z J) : v x = v x' :=
  le_antisymm ((H.congr hσ hf).le hL H') (H'.le hL (H.congr hσ hf))

variable {K : Type} [Fintype K] {ε : K → ℤ}

theorem hv_gen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r₀ : (TO hϖ hv).left ⟶ Y) {r : (TF (R := V) F).left ⟶ Y} (hr : (ιS hϖ hv).left ≫ r₀ = r) :
    HV hϖ hv L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => (val t r z J).val) 1 := by
  subst hr
  exact ⟨K, _, _, ε, LB.pullGen L φ ε t r₀, pullGen_isGen _ _ _ _ ht _, fun U _ h => by simp only [Category.assoc],
    fun z J hJ => by rw [val_pull hJ, cst_eq, map_one, _root_.one_mul]⟩

theorem hv_sec [X.IsSeparated] (hL : L.IsLB) {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (r₀ : (TO hϖ hv).left ⟶ Y) {r : (TF (R := V) F).left ⟶ Y} (hr : (ιS hϖ hv).left ≫ r₀ = r) :
    ∃ x, 0 ≤ v x ∧ HV hϖ hv L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => sval s r z J) x := by
  subst hr
  obtain ⟨t, ht⟩ := exists_gen_of_local (V := Ov v) L hL (fun i => r₀ ≫ φ i) ε
  have hi := invGen_isGen _ _ _ _ ht
  obtain ⟨a, ha, hav⟩ := sec_int hϖ hv hL (pullMulSec s r₀ _ hi) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, ha, K, _, _, ε, t, ht, fun U _ h => by simp only [Category.assoc], fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_pullMulSec _ _ _ hi _ z hJ, val_inv] at b
  rw [← b, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem hv_of_genV {φ : K → ((TF (R := V) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} {r : ℚ}
    (H : GenV hϖ hv t r) :
    ∃ x, v x = r ∧ HV hϖ hv L (fun _ _ h => ∏ i, h (φ i) ^ ε i) (fun z J => (val t (𝟙 _) z J).val) x := by
  obtain ⟨φ₀, h₀, t₀, ht₀, x, hx, e⟩ := H
  exact ⟨x, hx, K, _, φ₀, ε, t₀, ht₀, fun U _ h => by simp only [h₀], e⟩

theorem genV_unique [X.IsSeparated] (hL : L.IsLB) {φ : K → ((TF (R := V) F).left ⟶ X)}
    {t : LB.Gen (LB.LinComb L φ ε)} {r r' : ℚ} (H : GenV hϖ hv t r) (H' : GenV hϖ hv t r') : r = r' := by
  obtain ⟨x, hx, a⟩ := hv_of_genV H
  obtain ⟨x', hx', a'⟩ := hv_of_genV H'
  have := a.cmp hL a' (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [hx, hx'] at this
  exact_mod_cast this

theorem exists_genV (hL : L.IsLB) {φ : K → ((TF (R := V) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (hφ : ∀ i, ∃ ψ, φ i = (ιS hϖ hv).left ≫ ψ) : ∃ r, GenV hϖ hv t r := by
  choose φ₀ h₀ using hφ
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local (V := Ov v) L hL φ₀ ε
  obtain ⟨c, hc, e⟩ := exists_ratio hL t ht (LB.pullGen L _ _ t₀ (ιS hϖ hv).left) (pullGen_isGen _ _ _ _ ht₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [h₀])
  obtain ⟨q, hq⟩ := wt_coe_of_ne (v := v) hc
  refine ⟨q, φ₀, h₀, t₀, ht₀, c, hq, fun z J hJ => ?_⟩
  have := e (TF (R := V) F).left (𝟙 (TF (R := V) F).left) z J hJ
  rw [val_pull hJ, Category.id_comp] at this
  exact this

end GlobalTheory.UT.CoefVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}

theorem sep (D : DegData V (maximalIdeal V)) : D.toPre.P.A.left.IsSeparated := by
  have := D.toPre.P.isAb.proper
  exact ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩

theorem lift_left (q : TF (R := V) F ⟶ D.toPre.P.A) : ∃ ψ, q.left = (ιS hϖ hv).left ≫ ψ := by
  obtain ⟨m, rfl⟩ := exists_liftO hϖ hv q
  exact ⟨m.left, rfl⟩

theorem exists_genV_gt (g : GtPtF D.toPre F) (χ : D.toPre.X) : ∃ r, GenV hϖ hv (g.s χ) r :=
  exists_genV D.toPre.P.isLB (g.isGen χ) fun i => by fin_cases i <;> exact lift_left _

theorem exists_genV_frm {k : ℕ} {b : TF (R := V) F ⟶ D.toPre.P.A} {w : Frm D.toPre F k b} (hw : w.IsGen) :
    ∃ r, GenV hϖ hv w r :=
  exists_genV D.toPre.P.isLB hw fun i => by fin_cases i <;> exact lift_left _

theorem hv_cub (x x' y : TF (R := V) F ⟶ D.toPre.P.A) :
    HV hϖ hv D.toPre.P.L (fun _ _ h => h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ *
      (h (x' * y).left)⁻¹ * h x.left * h x'.left * h y.left * (h (1 : TF (R := V) F ⟶ D.toPre.P.A).left)⁻¹)
      (fun z J => (th D.toPre z J x x' y).val) 1 := by
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv x
  obtain ⟨m', hm'⟩ := exists_liftO hϖ hv x'
  obtain ⟨n, hn⟩ := exists_liftO hϖ hv y
  exact (hv_gen (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.isGen
    (lift m (lift m' n)).left (r := (lift x (lift x' y)).left)
    (by rw [← Over.comp_left, comp_lift, comp_lift, hm, hm', hn])).congr (fun U _ h => prod_cub x x' y h)
    (fun _ _ _ => rfl)

theorem add_of_cub {g g' g'' : GtPtF D.toPre F} {χ χ' χ'' : D.toPre.X} {x x' y : TF (R := V) F ⟶ D.toPre.P.A}
    {r r' r'' : ℚ} (a : GenV hϖ hv (g.s χ) r) (a' : GenV hϖ hv (g'.s χ') r') (a'' : GenV hϖ hv (g''.s χ'') r'')
    (hσ : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U),
      (∏ i, h (DegPre.gtφ D.toPre F g''.b χ'' i) ^ DegPre.gtε i) * (h (x * x' * y).left * (h (x * x').left)⁻¹ *
        (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left * h y.left *
        (h (1 : TF (R := V) F ⟶ D.toPre.P.A).left)⁻¹) =
      (∏ i, h (DegPre.gtφ D.toPre F g.b χ i) ^ DegPre.gtε i) * ∏ i, h (DegPre.gtφ D.toPre F g'.b χ' i) ^ DegPre.gtε i)
    (hf : ∀ z J, Good D.toPre.P.L z J → val (g''.s χ'') (𝟙 _) z J * th D.toPre z J x x' y =
      val (g.s χ) (𝟙 _) z J * val (g'.s χ') (𝟙 _) z J) : r'' = r + r' := by
  have := sep D
  obtain ⟨c, hc, H⟩ := hv_of_genV a
  obtain ⟨c', hc', H'⟩ := hv_of_genV a'
  obtain ⟨c'', hc'', H''⟩ := hv_of_genV a''
  have e := (H''.mul (hv_cub x x' y)).cmp D.toPre.P.isLB (H.mul H') hσ
    (fun z J hJ => by simpa only [Units.val_mul] using congrArg Units.val (hf z J hJ).symm)
  rw [_root_.mul_one, AddValuation.map_mul, hc, hc', hc''] at e
  exact_mod_cast e

theorem exists_gtV (g : GtPtF D.toPre F) : ∃! l : D.toPre.X →+ ℚ, GtV hϖ hv g l := by
  have := sep D
  choose l hl using exists_genV_gt (hϖ := hϖ) (hv := hv) g
  refine ⟨AddMonoidHom.mk' l fun χ χ' => add_of_cub (x := cP D.toPre _ χ) (x' := cP D.toPre _ χ') (y := g.b)
    (hl χ) (hl χ') (hl (χ + χ')) (fun U _ h => ?_) (fun z J hJ => ?_), hl,
    fun l' hl' => AddMonoidHom.ext fun χ => genV_unique D.toPre.P.isLB (hl' χ) (hl χ)⟩
  · rw [prod_gt, prod_gt, prod_gt, cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have e := gt_mul (𝟙 (TF (R := V) F)) hJ g χ χ'
    rwa [Category.id_comp, Over.id_left] at e

theorem gtV_add {g g' g'' : GtPtF D.toPre F} {l l' : D.toPre.X → ℚ} (h : g.IsAdd g' g'') (a : GtV hϖ hv g l)
    (a' : GtV hϖ hv g' l') : GtV hϖ hv g'' (l + l') := fun χ => by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 h
  obtain ⟨r, hr⟩ := exists_genV_gt (hϖ := hϖ) (hv := hv) g'' χ
  have e := add_of_cub (x := cP D.toPre _ χ) (x' := g.b) (y := g'.b) (a χ) (a' χ) hr (fun U _ h => by
    rw [prod_gt, prod_gt, prod_gt, hb, ← _root_.mul_assoc (cP D.toPre _ χ) g.b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel) (hs χ)
  rwa [e] at hr

theorem genV_frmOne {k : ℕ} {b : TF (R := V) F ⟶ D.toPre.P.A} {w : Frm D.toPre F k b} (hw : FrmOne w) (hb : b = 1) :
    GenV hϖ hv w 0 := by
  have := sep D
  obtain ⟨r, hr⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw.1
  obtain ⟨c, hc, H⟩ := hv_of_genV hr
  have e := H.cmp D.toPre.P.isLB HV.one (fun U _ h => by rw [prod_line, hb, mul_inv_cancel])
    (fun z J hJ => by simp only [hw.2 z J hJ, Units.val_one])
  rw [hc, AddValuation.map_one] at e
  obtain rfl : r = 0 := by exact_mod_cast e
  exact hr

theorem gtV_qk (hVR : VRatioGtStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k)
    (p : QkPt D.toPre F k) : GtV hϖ hv p.g fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / k := fun α => by
  have hL := D.toPre.P.isLB
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv (D := D) p.g.b
  obtain ⟨G₀, hG₀⟩ := exists_gen_of_local D.toPre.P.L hL (gtφO hϖ hv m α) DegPre.gtε
  have hg : ∀ i, DegPre.gtφ D.toPre F p.g.b α i = (ιS hϖ hv).left ≫ gtφO hϖ hv m α i := by
    intro i; fin_cases i
    · show (padd D.toPre.P.A (DegPre.cF D.toPre F α) p.g.b).left = (ιS hϖ hv).left ≫ (cP D.toPre _ α * m).left
      rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hm]; rfl
    · show (DegPre.cF D.toPre F α).left = (ιS hϖ hv).left ≫ (cP D.toPre _ α).left
      rw [← Over.comp_left, comp_cP]; rfl
    · show p.g.b.left = (ιS hϖ hv).left ≫ m.left
      rw [← Over.comp_left, hm]
    · show (DegPre.zeroF D.toPre F).left = (ιS hϖ hv).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left
      rw [← Over.comp_left, MonObj.comp_one]; rfl
  obtain ⟨t, -, ht⟩ := exists_ratio hL (p.g.s α) (p.g.isGen α)
    (LB.pullGen D.toPre.P.L _ _ G₀ (ιS hϖ hv).left) (pullGen_isGen _ _ _ _ hG₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hg])
  have ht' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (val G₀ (r ≫ (ιS hϖ hv).left) z J).val := fun Z r z J hJ => by
    rw [ht Z r z J hJ, val_pull hJ]
  obtain ⟨q, hq, hkq⟩ := hVR V ϖ hϖ D Q hQ F v hv k hk p m hm α G₀ hG₀ t ht'
  refine ⟨gtφO hϖ hv m α, hg, G₀, hG₀, t, ?_, fun z J hJ => ?_⟩
  · simp only [hq, ← hkq, mul_div_cancel_left₀ _ hk0]
  · have e := ht' _ (𝟙 _) z J hJ
    rwa [Category.id_comp] at e

theorem gtV_iota (hVR : VRatioGtStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {g : GtPtF D.toPre F}
    {y : D.toPre.X} (h : GtPtF.IsIota y g) : GtV hϖ hv g fun χ => (QForm.bOf D.toPre Q y χ : ℚ) := by
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨hb, hs⟩ := (isZero_iff o).1 ho
  have hadd : o.IsAdd g g := (isAdd_iff _ _ _).2 ⟨by rw [hb, _root_.one_mul], fun χ z J hJ => by
    have C : IsCub (th D.toPre (T := TF (R := V) F) z J) := isCub_cubV D.toPre.cub hJ
    rw [hs χ z J hJ, hb, C.face₂, mul_comm]⟩
  have hn : GtPtF.IsNsmul 1 g g := by
    refine ⟨![o, g], ?_, fun i => ?_, rfl⟩
    · simpa only [Matrix.cons_val_zero] using ho
    · fin_cases i; exact hadd
  have e := gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ (le_refl 1) ⟨y, g, g, hn, h⟩
  simpa only [Nat.cast_one, div_one] using e

theorem le_v_int {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b} {χ : D.toPre.X} {σ : D.toPre.SecB k χ} {σF}
    (hσ : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) σF
      (D.toPre.famφB χ) (DegPre.famε k) σ (DegPre.prB D.toPre F).left 1) {x : F} (hx : IsCoef k g w χ σF x)
    {l ω : ℚ} (hl : GenV hϖ hv (g.s χ) l) (hω : GenV hϖ hv w ω) : ((l + ω : ℚ) : WithTop ℚ) ≤ v x := by
  have := sep D
  have hL := D.toPre.P.isLB
  obtain ⟨c, hc, H⟩ := hv_of_genV hl
  obtain ⟨c', hc', H'⟩ := hv_of_genV hω
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv g.b
  obtain ⟨a, ha, A⟩ := hv_sec (hϖ := hϖ) (hv := hv) hL σ m.left (r := g.b.left) (by rw [← Over.comp_left, hm])
  have R := ((hv_gen (hϖ := hϖ) (hv := hv) (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1)
    D.toPre.rig_gen (TO hϖ hv).hom (Over.w (ιS hϖ hv))).pow k).smul x
  have e := R.cmp hL ((A.mul H).mul H') (fun U _ h => by
      have e₀ : (TF (R := V) F).hom ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := rfl
      have e₁ : SectionScalarValuation.cQ D.toPre (TF (R := V) F) χ = cP D.toPre _ χ := rfl
      rw [SectionScalarValuation.prod_famB, prod_gt, prod_line, Fintype.prod_unique, e₀, e₁, mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (fun z J hJ => by
      have e₂ := SectionScalarValuation.secScal_sval hσ (lift (𝟙 (TF (R := V) F)) g.b).left z hJ
      rw [← Over.comp_left, lift_snd] at e₂
      have e₃ := hx z J hJ
      rw [← e₂] at e₃
      exact e₃.symm)
  rw [one_pow, _root_.mul_one, AddValuation.map_mul, AddValuation.map_mul, hc, hc'] at e
  rw [e, WithTop.coe_add]
  exact add_le_add_left (le_add_of_nonneg_left ha) _

theorem le_v_coef {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b} (hw : w.IsGen) {χ : D.toPre.X}
    {s : Fam D.toPre F k} {r l ω : ℚ} (hs : VGe D F v k χ (s.s χ) r) (hl : GenV hϖ hv (g.s χ) l)
    (hω : GenV hϖ hv w ω) : ((r + l + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) := by
  obtain ⟨n, a, σ, σF, hσ, ha, hsum⟩ := hs
  choose x hx using fun i => exists_isCoef g hw χ (σF i)
  have e : coef s g w χ = ∑ i, a i * x i := coef_eq fun z J hJ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [SectionScalarValuation.sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) _ z hJ, cst_eq, map_sum, Finset.sum_mul,
      Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have b : gs (lift (𝟙 (TF (R := V) F)) g.b).left z ⊤ (gF D.toPre F (a i)) = cst F z (a i) := by
      refine (gs_pull _ (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    have c := hx i z J hJ
    rw [b, map_mul, ← cst_eq, ← cst_eq, _root_.mul_assoc, c]
    ring
  rw [e]
  refine AddValuation.map_le_sum v fun i _ => ?_
  rw [AddValuation.map_mul, add_assoc, WithTop.coe_add]
  exact add_le_add (ha i) (le_v_int (hσ i) (hx i) hl hω)

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ g : GtPtF D.toPre F, (∃! l : D.toPre.X →+ ℚ, GtV hϖ hv g l) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), w.IsGen → ∃! r, GenV hϖ hv w r) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), FrmOne w → g.b = 1 → GenV hϖ hv w 0) ∧ (∀ (g' g'' : GtPtF D.toPre F) l l', g.IsAdd g' g'' → GtV hϖ hv g l → GtV hϖ hv g' l' → GtV hϖ hv g'' (l + l')) ∧ (∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, GtV hϖ hv p.g fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / k) ∧ (∀ y, GtPtF.IsIota y g → GtV hϖ hv g fun χ => (QForm.bOf D.toPre Q y χ : ℚ)) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (w : Frm D.toPre F k g.b) (s : Fam D.toPre F k), w.IsGen → NullV v (coef s g w) ∧ ∀ l ω r, GtV hϖ hv g l → GenV hϖ hv w ω → NuGe D Q F v k s r → ∀ χ, ((r + (Q χ : ℚ) / k + l χ + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) := by
  intro _ hTW hVR _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv g
  have := sep D
  have bound : ∀ (k : ℕ) (w : Frm D.toPre F k g.b) (s : Fam D.toPre F k), w.IsGen → ∀ l ω r, GtV hϖ hv g l →
      GenV hϖ hv w ω → NuGe D Q F v k s r →
      ∀ χ, ((r + (Q χ : ℚ) / k + l χ + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) :=
    fun k w s hw l ω r hl hω hs χ => le_v_coef hw (hs χ) (hl χ) hω
  refine ⟨exists_gtV g, fun k w hw => ?_, fun k w => genV_frmOne, fun g' g'' l l' => gtV_add,
    fun k hk p => gtV_qk hVR hQ hk p, fun y => gtV_iota hVR hQ, fun k hk w s hw => ⟨fun q => ?_, bound k w s hw⟩⟩
  · obtain ⟨r, hr⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw
    exact ⟨r, hr, fun r' hr' => genV_unique D.toPre.P.isLB hr' hr⟩
  · obtain ⟨l, hl, -⟩ := exists_gtV (hϖ := hϖ) (hv := hv) g
    obtain ⟨ω, hω⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw
    obtain ⟨r, hr⟩ := exists_nuGe hϖ hv hTW hQ hk s
    refine (finite_sublevel hϖ hQ hk l (q - r - ω)).subset fun χ hχ => ?_
    have h : r + (Q χ : ℚ) / k + l χ + ω < q := WithTop.coe_lt_coe.1 ((bound k w s hw l ω r hl hω hr χ).trans_lt hχ)
    show (Q χ : ℚ) / k + l χ ≤ q - r - ω
    linarith

end GlobalTheory.UT.CoefVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTermsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.valuations_torusPoints_frames_familyTerms : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ g : GtPtF D.toPre F, (∃! l : D.toPre.X →+ ℚ, GtV hϖ hv g l) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), w.IsGen → ∃! r, GenV hϖ hv w r) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), FrmOne w → g.b = 1 → GenV hϖ hv w 0) ∧ (∀ (g' g'' : GtPtF D.toPre F) l l', g.IsAdd g' g'' → GtV hϖ hv g l → GtV hϖ hv g' l' → GtV hϖ hv g'' (l + l')) ∧ (∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, GtV hϖ hv p.g fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / k) ∧ (∀ y, GtPtF.IsIota y g → GtV hϖ hv g fun χ => (QForm.bOf D.toPre Q y χ : ℚ)) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (w : Frm D.toPre F k g.b) (s : Fam D.toPre F k), w.IsGen → NullV v (coef s g w) ∧ ∀ l ω r, GtV hϖ hv g l → GenV hϖ hv w ω → NuGe D Q F v k s r → ∀ χ, ((r + (Q χ : ℚ) / k + l χ + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) := by
  first | exact @GlobalTheory.UT.CoefVal.main | exact GlobalTheory.UT.CoefVal.main | (intros; apply GlobalTheory.UT.CoefVal.main <;> assumption)
end
