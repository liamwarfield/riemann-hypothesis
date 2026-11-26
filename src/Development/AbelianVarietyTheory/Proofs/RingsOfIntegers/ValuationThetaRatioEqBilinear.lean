module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatioVal

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

def germConst (F : Type) [Field F] (z : Spec (CommRingCat.of F)) : F →+* (Spec (CommRingCat.of F)).presheaf.stalk z :=
  ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem gs_specMap {A F : Type} [CommRing A] [Field F] (f : A →+* F) (z : Spec (CommRingCat.of F))
    (a : Γ(Spec (CommRingCat.of A), ⊤)) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ a = germConst F z (f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a)) := by
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom (appTop_specMap (CommRingCat.ofHom f) a)

theorem gs_id_const {F : Type} [Field F] (z : Spec (CommRingCat.of F)) (c : F) :
    gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) = germConst F z c := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem gs_scal {A F : Type} [CommRing A] [Field F] (f : A →+* F) (z : Spec (CommRingCat.of F)) (c : A) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ (scal (𝟙 (Spec (CommRingCat.of A))) c) = germConst F z (f c) := by
  rw [gs_specMap]
  congr 2
  simp [scal]

theorem unit_calc {S : Type} [CommRing S] {s G τ C P R E Eψ Er fam u : Sˣ} {T c₀ cψ cr A : S} {k : ℕ}
    (h1 : s.val = T * G.val) (h2 : τ * C = s ^ k) (h3 : fam = τ * (P * R)) (h4 : fam.val = c₀ * E.val)
    (h5 : P.val = cψ * Eψ.val) (h6 : R.val = cr * Er.val) (h8 : u.val = A)
    (hu : u = E * Eψ⁻¹ * Er⁻¹ * C * (G ^ k)⁻¹) : c₀ * A = T ^ k * cψ * cr := by
  have e1 : u * (Eψ * Er * G ^ k) = E * C := by
    rw [hu]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have e2 : fam * C = s ^ k * (P * R) := by rw [h3, ← h2]; ac_rfl
  have e1' := congrArg Units.val e1
  have e2' := congrArg Units.val e2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, h1, h4, h5, h6, h8, mul_pow] at e1' e2'
  apply (Eψ * Er * G ^ k).isUnit.mul_right_cancel
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  linear_combination c₀ * e1' + e2'

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem v_ratio_gt (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = p.g.b)
    (α : D.toPre.X) (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (gtφO hϖ hv m α) DegPre.gtε)) (hG₀ : G₀.IsGen) (t : F)
    (ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (val G₀ (r ≫ (ιS hϖ hv).left) z J).val) :
    ∃ q : ℚ, v t = (q : WithTop ℚ) ∧ (k : ℚ) * q = QForm.bOf D.toPre Q p.y α := by
  have hL := D.toPre.P.isLB
  have hmk : m ^ k = cP D.toPre (TO hϖ hv) p.y := by
    apply liftO_unique hϖ hv
    rw [comp_cP, cPoint_y, ← hm]
    exact map_pow (preHom (ιS hϖ hv)) m k
  obtain ⟨Ix, _, φV, εV, e', he', hfe', c₀, hc₀, hve'⟩ := famMult_data D hϖ hQ k p.y α
  obtain ⟨eψ, heψ, cψ, hcψ, hteψ⟩ := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (hQ p.y) k
  obtain ⟨er, her, cr, hcr, hter⟩ := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (QForm.rigK_val (ϖ := ϖ) D) k
  obtain ⟨tc, htc, hvtc⟩ := exists_cubN D.toPre.cub (1 : TO hϖ hv ⟶ D.toPre.P.A) m (cP D.toPre _ α) k
  let h₀ : (TO hϖ hv).left ⟶ Spec (CommRingCat.of V) := (TO hϖ hv).hom
  let u := LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ e' h₀)
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ eψ h₀)))
    (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ er h₀))) tc)
    (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ G₀ k))
  have hu : u.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ he' _) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ heψ _)))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ her _))) htc) (invGen_isGen _ _ _ _ (powGen_isGen' _ _ _ _ hG₀ k))
  have hsurj : Function.Surjective (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)).hom := fun x => ⟨x, by simp⟩
  have hfs : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      (((((∏ i, h (h₀ ≫ φV i) ^ εV i) * (h (cP D.toPre (TO hϖ hv) p.y).left ^ ((k : ℤ) * -1))⁻¹) *
        (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ ((k : ℤ) * 1))⁻¹) *
        ∏ i, h (![(1 * m ^ k * cP D.toPre _ α).left, (1 * m ^ k).left, (1 * cP D.toPre _ α).left,
          (1 : TO hϖ hv ⟶ D.toPre.P.A).left, (m * cP D.toPre _ α).left, m.left, (cP D.toPre _ α).left,
          (1 : TO hϖ hv ⟶ D.toPre.P.A).left] i) ^ (![1, -1, -1, 1, -k, k, k, -k] : Fin 8 → ℤ) i) *
        (∏ i, h (gtφO hϖ hv m α i) ^ ((k : ℤ) * DegPre.gtε i))⁻¹) = 1 := by
    intro U _ h
    let o : TO hϖ hv ⟶ D.toPre.P.A := 1
    have e := hfe' U (fun q => h (o.left ≫ q))
    have w : o.left ≫ D.toPre.P.A.hom = h₀ := Over.w o
    have q₀ : ∀ i, o.left ≫ D.toPre.P.A.hom ≫ φV i = h₀ ≫ φV i := fun i => by rw [← Category.assoc, w]
    have q₁ : ∀ χ, o.left ≫ (cQ D.toPre D.toPre.P.A χ).left = (cP D.toPre (TO hϖ hv) χ).left := fun χ =>
      congrArg (fun q : TO hϖ hv ⟶ D.toPre.P.A => q.left) (comp_cP D.toPre o χ)
    have q₂ : o.left ≫ (cQ D.toPre D.toPre.P.A α * cQ D.toPre D.toPre.P.A p.y).left =
        (cP D.toPre (TO hϖ hv) α * cP D.toPre (TO hϖ hv) p.y).left :=
      congrArg (fun q : TO hϖ hv ⟶ D.toPre.P.A => q.left) ((MonObj.comp_mul o _ _).trans
        (congrArg₂ (· * ·) (comp_cP D.toPre o α) (comp_cP D.toPre o p.y)))
    have q₃ : o.left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TO hϖ hv ⟶ D.toPre.P.A).left :=
      congrArg (fun q : TO hϖ hv ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) o)
    simp only [q₀, q₁, q₂, q₃] at e
    rw [e, hmk, _root_.one_mul, _root_.one_mul, mul_comm (cP D.toPre (TO hϖ hv) p.y), mul_comm m]
    apply Additive.ofMul.injective
    simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, gtφO, DegPre.gtε]
    module
  have pψ : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      ∏ _i : PUnit.{1}, h (h₀ ≫ (D.toPre.c p.y).left) ^ ((k : ℤ) * -1) =
        h (cP D.toPre (TO hϖ hv) p.y).left ^ ((k : ℤ) * -1) := fun U _ h => by
    rw [Fintype.prod_unique]
    rfl
  have pr : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      ∏ _i : PUnit.{1}, h (h₀ ≫ 𝟙 _ ≫ eSec D.toPre.P.A) ^ ((k : ℤ) * 1) =
        h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ ((k : ℤ) * 1) := fun U _ h => by
    rw [Fintype.prod_unique, Hom.one_def]
    rfl
  obtain ⟨a, ha⟩ : ∃ a : Γ((TO hϖ hv).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TO hϖ hv).left) (z : Z) (J),
      Good D.toPre.P.L z J → (val u r z J).val = gs (r ≫ 𝟙 _) z ⊤ a :=
    ReciprocityTheory.ChartRestriction.G.H1.exists_const D.toPre.P.L hL (𝟙 _) hsurj u hu (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [pψ U h, pr U h]
      exact hfs U h)
  obtain ⟨a', ha'⟩ : ∃ a : Γ((TO hϖ hv).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TO hϖ hv).left) (z : Z) (J),
      Good D.toPre.P.L z J → (val (LB.invGen D.toPre.P.L _ _ u) r z J).val = gs (r ≫ 𝟙 _) z ⊤ a :=
    ReciprocityTheory.ChartRestriction.G.H1.exists_const D.toPre.P.L hL (𝟙 _) hsurj _ (invGen_isGen _ _ _ _ hu) (fun U _ h => by
      refine (prod_neg _ _ ?_).trans inv_one
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [pψ U h, pr U h]
      exact hfs U h)
  let z₀ : Spec (CommRingCat.of F) := default
  choose J₀ hJ₀ using fun χ : (TF (R := V) F).left ⟶ D.toPre.P.A.left => exists_chart hL (χ z₀)
  have hG : Good D.toPre.P.L z₀ J₀ := hJ₀
  have h1 := ht _ (𝟙 _) z₀ J₀ hG
  have h2 := chain_val (𝟙 (TF (R := V) F)) hG p α
  have h3 := val_famMult (𝟙 (TF (R := V) F)) hG k p.y α
  have h4 := hve' F _ (𝟙 _) z₀ J₀ hG
  have h5 := val_genHasVal (hφ := fun _ => QForm.ptK_eq D.toPre p.y) hteψ ((𝟙 _) ≫ jFK (R := V) F) z₀ hG
  have h6 := val_genHasVal (hφ := fun _ => by rw [Category.id_comp]; rfl) hter ((𝟙 _) ≫ jFK (R := V) F) z₀ hG
  have h7 := hvtc (TF (R := V) F) (ιS hϖ hv) z₀ J₀ hG
  have h8 := ha _ (ιS hϖ hv).left z₀ J₀ hG
  have h8' := ha' _ (ιS hϖ hv).left z₀ J₀ hG
  have hι : (ιS hϖ hv).left ≫ (TO hϖ hv).hom = DegPre.jFR (R := V) F := Over.w (ιS hϖ hv)
  have hid : Over.Hom.left (𝟙 (TF (R := V) F)) = 𝟙 (Spec (CommRingCat.of F)) := Over.id_left _
  rw [hid] at h2 h3
  simp only [Category.id_comp] at h1 h2 h3 h4 h5 h6 h8 h8'

  have hu8 : val u (ιS hϖ hv).left z₀ J₀ = val (Z := (TF (R := V) F).left) e' (DegPre.jFR (R := V) F) z₀ J₀ *
      (val (Z := (TF (R := V) F).left) eψ (DegPre.jFR (R := V) F) z₀ J₀)⁻¹ *
      (val (Z := (TF (R := V) F).left) er (DegPre.jFR (R := V) F) z₀ J₀)⁻¹ *
      val tc (ιS hϖ hv).left z₀ J₀ * (val G₀ (ιS hϖ hv).left z₀ J₀ ^ k)⁻¹ := by
    simp only [u, h₀, val_mul hG, val_inv, val_pull hG, val_powGen, hι]
  have h7' : val tc (ιS hϖ hv).left z₀ J₀ = cubN (th D.toPre z₀ J₀) k 1 p.g.b (cP D.toPre (TF (R := V) F) α) := by
    rw [h7, MonObj.comp_one, hm, comp_cP]
  have key := unit_calc h1 (h7' ▸ h2) h3 h4 h5 h6 h8 hu8
  have g1 : gs (𝟙 (TF (R := V) F).left) z₀ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) = germConst F z₀ t :=
    gs_id_const z₀ t
  have g2 : ∀ c : FractionRing V, gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 _) c) =
      germConst F z₀ (algebraMap (FractionRing V) F c) := fun c => gs_scal _ z₀ c
  have g3 : ∀ b : Γ((TO hϖ hv).left, ⊤), gs ((ιS hϖ hv).left ≫ 𝟙 _) z₀ ⊤ b = germConst F z₀ (ιr (v := v) b) := fun b => by
    rw [Category.comp_id]; exact gs_specMap _ z₀ b
  have hinj : Function.Injective (germConst F z₀) := (germConst F z₀).injective
  have k1 : algebraMap (FractionRing V) F c₀ * ιr (v := v) a =
      t ^ k * algebraMap (FractionRing V) F cψ * algebraMap (FractionRing V) F cr := by
    apply hinj
    simp only [map_mul, map_pow]
    rw [← g1, ← g2, ← g2, ← g2, ← g3]
    exact key
  have k2 : ιr (v := v) a * ιr (v := v) a' = 1 := by
    apply hinj
    rw [map_mul, map_one, ← g3, ← g3, ← h8, ← h8', val_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have va : v (ιr (v := v) a) = 0 := by
    have e : v (ιr (v := v) a) + v (ιr (v := v) a') = 0 := by rw [← AddValuation.map_mul, k2, AddValuation.map_one]
    exact le_antisymm (le_zero_of_add_eq_zero_nonneg e (v_ιr a')) (v_ιr a)
  have k3 := congrArg v k1
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, va, hv _ _ hc₀,
    hv _ _ hcψ, hv _ _ hcr] at k3
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [g1, map_zero, zero_mul] at h1
    exact (val (p.g.s α) (𝟙 _) z₀ J₀).ne_zero h1
  obtain ⟨q, hq⟩ := wt_coe_of_ne (v := v) ht0
  refine ⟨q, hq, ?_⟩
  rw [hq] at k3
  have k4 : (((k : ℤ) * Q p.y + QForm.bOf D.toPre Q p.y α : ℤ) : ℚ) + 0 =
      k • q + (((k : ℤ) * Q p.y : ℤ) : ℚ) + (((k : ℤ) * 0 : ℤ) : ℚ) := by exact_mod_cast k3
  rw [nsmul_eq_mul] at k4
  push_cast at k4
  linarith

theorem main : TWM.VRatioGtStatement :=
  fun _ _ _ _ _ hϖ _ _ hQ _ _ _ _ hv _ hk p m hm α G₀ hG₀ t ht => v_ratio_gt hϖ hv hQ hk p m hm α G₀ hG₀ t ht

end GlobalTheory.RatioVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinearStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.valuation_thetaRatio_eq_bilinear : TWM.VRatioGtStatement := by
  first | exact @GlobalTheory.RatioVal.main | exact GlobalTheory.RatioVal.main | (intros; apply GlobalTheory.RatioVal.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowPrimitive

open Geo.Tor

def chartPullSwap {X X' : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K] (F : J → (X' ⟶ X))
    (φ : K → (X ⟶ X)) (ψ : K → (X' ⟶ X')) (ε : K → ℤ) (hc : ∀ k i, ψ k ≫ F i = F i ≫ φ k) :
    ChartPull (LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε) (LB.LinComb (LB.LinComb L φ ε) F (fun _ => 1)) (𝟙 X') :=
  have le : ∀ j : K → J → L.ι, LB.wchart (LB.LinComb L F (fun _ => 1)) ψ j ≤
      (𝟙 X') ⁻¹ᵁ LB.wchart (LB.LinComb L φ ε) F (fun i k => j k i) :=
    fun j y hy => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun k => by
      have h : (ψ k ≫ F i) y ∈ L.U (j k i) := Set.mem_iInter.1 (Set.mem_iInter.1 hy k) i
      rw [hc] at h
      exact h
  { idx := fun j i k => j k i
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 X') y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb (LB.LinComb L φ ε) F (fun _ => 1) (𝟙 X') y _ _ (le j hj) (le j' hj')).symm)
      refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k)
        (gm_linComb L F (fun _ => 1) (𝟙 X' ≫ ψ k) y (j k) (j' k)
          (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k))).trans ?_
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => congrArg (· ^ (1 : ℤ))
        (gm_linComb L φ ε (𝟙 X' ≫ F i) y (fun k => j k i) (fun k => j' k i)
          (Set.mem_iInter.1 (le j hj) i) (Set.mem_iInter.1 (le j' hj') i))).symm
      simp only [zpow_one, Category.id_comp, hc, ← Finset.prod_zpow]
      exact Finset.prod_comm }

theorem lbIso_linComb {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : LBIso (LB.LinComb L φ ε) (LB.LinComb M φ ε) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨LB.linCombIso u φ ε, linCombIso_isGen u hu φ ε⟩

private lemma foldr_padd_comp_eq_comp_foldr_padd {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (h : G' ⟶ G) [IsMonHom h]
    {n : ℕ} (x' : Fin n → (G' ⟶ G')) (x : Fin n → (G ⟶ G)) (hx : ∀ k, x' k ≫ h = h ≫ x k) (l : List (Fin n)) :
    List.foldr (fun k acc => padd G' (x' k) acc) (pzero G' G') l ≫ h =
      h ≫ List.foldr (fun k acc => padd G (x k) acc) (pzero G G) l := by
  induction l with
  | nil =>
    rw [List.foldr_nil, List.foldr_nil, show pzero G' G' = 1 from Over.OverMorphism.ext rfl,
      show pzero G G = 1 from Over.OverMorphism.ext rfl, one_comp, comp_one]
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, show ∀ a b : G' ⟶ G', padd G' a b = a * b from fun _ _ => Over.OverMorphism.ext rfl,
      show ∀ a b : G ⟶ G, padd G a b = a * b from fun _ _ => Over.OverMorphism.ext rfl, mul_comp, comp_mul, hx k, ih]

theorem lbIso_cube_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f : G ⟶ G) (f' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → Geo.Tor.LBIso L (cubeLB G ![𝟙 G, f] L) → Geo.Tor.LBIso L' (cubeLB G' ![𝟙 G', f'] L') := by
  intro S G' G _ _ _ _ j p L L' hL hL' hbox f f' hc hprim
  unfold cubeLB boxLB at *
  have hcomm : ∀ (I : ULift.{0} (Finset (Fin 2))) (i : Fin j),
      (psum G' ![𝟙 G', f'] I.down).left ≫ (p.pr i).left = (p.pr i).left ≫ (psum G ![𝟙 G, f] I.down).left := by
    intro I i
    have := p.hom i
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold psum
    refine foldr_padd_comp_eq_comp_foldr_padd (p.pr i) _ _ (fun k => ?_) _
    fin_cases k
    · simp
    · simpa using hc i
  have hP := linComb_isLB _ hL (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have hQ := linComb_isLB _ (linComb_isLB _ hL (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))) (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have hR := linComb_isLB _ hP (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))
  have h1 := lbIso_linComb hbox (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))
  have h3 := lbIso_linComb hprim (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have cp := chartPullSwap L (fun i => (p.pr i).left) (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
    (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card)) hcomm
  have h2 : LBIso (LB.LinComb (LB.LinComb L (fun i => (p.pr i).left) (fun _ => (1 : ℤ)))
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
      (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card)))
      (LB.LinComb (LB.LinComb L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
        (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))) (fun i => (p.pr i).left) (fun _ => (1 : ℤ))) := by
    have hQQ := LBIso.trans hQ hP hQ (LBIso.symm h3) h3
    exact LBIso.chartPull (h := 𝟙 G'.left) cp (chartPullId _) hQQ
  exact LBIso.trans hL' hQ (linComb_isLB _ hL' _ _) (LBIso.trans hL' hP hQ hbox h3)
    (LBIso.trans hQ hR (linComb_isLB _ hL' _ _) (LBIso.symm h2) (LBIso.symm h1))

end GlobalTheory.PowPrimitive
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PsiZero

theorem cPoint_zero' {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) :
    cP D T 0 = 1 := by
  have := cPoint_add D T 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem val_psi_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {z : (TK R).left}
    {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val (D.psi 0) (𝟙 _) z J = (val D.rig (jK R) z J)⁻¹ := by
  have C : IsCub (th D (T := TK R) z J) := isCub_cubV D.cub hJ
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (jK R) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
    rfl
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) (𝟙 _) z J = 1 := by
    refine (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ 0) (cP D _ 0) (cP D _ 0)).trans ?_
    rw [Category.id_comp, cPoint_zero']
    exact C.face _ _
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB 0 0 0) (𝟙 _)).trans (val_mul hJ _ _ _))
  have hp : ∀ a : D.X, a = 0 → val (D.psi a) (𝟙 _) z J = val (D.psi 0) (𝟙 _) z J := by
    rintro a rfl; rfl
  rw [vc, vτ, vτ, vρ, hp (0 + 0 + 0) (by simp), hp (0 + 0) (by simp), _root_.mul_one, mul_inv_cancel,
    _root_.one_mul] at e
  have e' := mul_eq_left.1 e.symm
  rw [← mul_inv, inv_eq_one] at e'
  exact eq_inv_of_mul_eq_one_left e'

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), (D.TauBimult → D.PsiIn 0 ⊤) ∧ ∀ (χ : D.X) (J J' : Ideal R), J ≤ J' → D.PsiIn χ J → D.PsiIn χ J' := by
  intro R _ _ D
  refine ⟨fun hB j V hV hle h => ?_, fun χ J J' hJ H j V hV hle h => ?_⟩
  · have c0 : (D.c 0).left = eSec D.P.A := by
      have := cPoint_zero' D (𝟙_ _)
      rw [cP, toUnit_unit, Category.id_comp, Hom.one_def, toUnit_unit, Category.id_comp] at this
      rw [this]; rfl
    have hx : D.xK 0 = jK R ≫ eSec D.P.A := by rw [← c0]; rfl
    have hle' : V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => eSec D.P.A) j := fun y hy =>
      Set.mem_iInter.2 fun _ => by rw [← c0]; exact hle hy
    refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.rig.s j)⁻¹.val,
      by rw [Ideal.map_top]; trivial, fn_ext fun y hy => ?_⟩
    have hy' : jK R y ∈ V := hy
    obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (K := PUnit) (fun _ => D.xK 0) j (fun _ _ _ => rfl)
      (fun k => Set.mem_iInter.1 (h hy) k)
    have e := val_psi_zero hB hJ
    rw [val_of (D.psi 0) _ y J j (fun k => (congrArg J (Category.id_comp (D.xK 0))).trans (eJ k)),
      val_of D.rig _ y J j (fun k => (congrArg J hx.symm).trans (eJ k))] at e
    refine (gs_pull (𝟙 _) (jK R) y V hy' _).trans (Eq.trans ?_
      ((gs_res (𝟙 _) y h hy _).trans (gs_unit _ _ _ (h hy) _)).symm)
    rw [Category.id_comp]
    refine (gs_res (jK R) y hle' hy' _).trans ((gs_unit _ _ _ (hle' hy') _).trans ?_)
    exact congrArg Units.val ((map_inv _ _).trans e.symm)
  · obtain ⟨r, hr, e⟩ := H j V hV hle h
    exact ⟨r, Ideal.map_mono hJ hr, e⟩

end GlobalTheory.PsiZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullGenG

theorem hasGen_one {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) :
    HasGen Lr.L (lf (Finsupp.single (1 : G ⟶ G) 1)) := by
  have h0 := (HasGen.of_gen (L := Lr.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) Lr.rig Lr.rigGen).pull G.hom
  have e1 : (1 : G ⟶ G).left = G.hom ≫ eSec G := rfl
  convert h0 using 1
  rw [lf_single, e1]
  simp [fsum, Finsupp.mapDomain_single]

theorem hasGen_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (cub : CubicalStr G Lr)
    {O : Type} [CommRing O] [StarRing O] (ra : RingAct G O) (w0 a : O) (N : ℕ) (hN : a * star a = (N : O))
    (hadj : Geo.Tor.LBIso (cubeLB G ![fst G G ≫ ra.act a, snd G G] Lr.L)
      (cubeLB G ![fst G G, snd G G ≫ ra.act (star a)] Lr.L))
    (hprim : Geo.Tor.LBIso Lr.L (cubeLB G ![𝟙 G, ra.act w0] Lr.L)) (k : ℕ) :
    HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, (ra.act a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := by
  have := ra.hom w0
  obtain ⟨uR, huR⟩ := GlobalTheory.NormRos.exists_gen_rosati Lr.isLB (ra.act a) (ra.act (star a)) hadj
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim S G Lr (ra.act w0) hprim
  have hP : HasGen Lr.L (fsum (GlobalTheory.JetSer.primφ (ra.act w0)) GlobalTheory.JetSer.primε) := HasGen.of_gen ρ hρ
  have h1 := hasGen_one Lr
  obtain ⟨uΨ, huΨ⟩ := HasGen.gen Lr.isLB (h1.sub hP) (K' := Fin 4)
    ![(padd G (𝟙 _) (ra.act w0)).left, 𝟙 G.left, (ra.act w0).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      unfold GlobalTheory.JetSer.primφ GlobalTheory.JetSer.primε
      have e1 : toUnit G ≫ η[G] = (1 : G ⟶ G) := rfl
      rw [padd_eq_mul, e1, lf_single]
      classical
      ext x
      simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
      split_ifs <;> omega)
  have hM := hasGen_pullMul ra w0 a N hN uΨ huΨ uR huR cub.t cub.isGen
  have h2 := (hM.zsmul (-(k : ℤ))).add (h1.zsmul ((k : ℤ) * ((N : ℤ) - 1)))
  convert h2 using 1
  classical
  simp only [lf_add, lf_sub, lf_smul, lf_single]
  ext x
  simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
  split_ifs <;> ring

end GlobalTheory.PullGenG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace SplitTorusPow

variable {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']

noncomputable def torusMap (S : Scheme.{0}) (φ : X →+ X') : splitTorus S X' ⟶ splitTorus S X :=
  (splitTorusPointsEquiv S X (splitTorus S X')).symm
    ((splitTorusPointsEquiv S X' (splitTorus S X') (𝟙 _)).comp (AddMonoidHom.toMultiplicative φ))

theorem torusMap_char (φ : X →+ X') (χ : X) :
    (torusMap S φ).left.appTop.hom (charUnit S X χ).val = (charUnit S X' (φ χ)).val := by
  rw [← splitTorusPointsEquiv_val, torusMap, MulEquiv.apply_symm_apply]
  change (splitTorusPointsEquiv S X' (splitTorus S X') (𝟙 _) (Multiplicative.ofAdd (φ χ))).val = _
  rw [splitTorusPointsEquiv_val]
  simp

theorem points_comp_torusMap (φ : X →+ X') {Z : Over S} (t : Z ⟶ splitTorus S X') :
    splitTorusPointsEquiv S X Z (t ≫ torusMap S φ) =
      (splitTorusPointsEquiv S X' Z t).comp (AddMonoidHom.toMultiplicative φ) := by
  refine MonoidHom.ext fun χ => Units.ext ?_
  change (splitTorusPointsEquiv S X Z (t ≫ torusMap S φ) (Multiplicative.ofAdd χ.toAdd)).val =
    (splitTorusPointsEquiv S X' Z t (Multiplicative.ofAdd (φ χ.toAdd))).val
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, ← torusMap_char, Over.comp_left,
    Scheme.Hom.comp_appTop]
  rfl

theorem mul_comp_torusMap (φ : X →+ X') {Z : Over S} (a b : Z ⟶ splitTorus S X') :
    (a * b) ≫ torusMap S φ = (a ≫ torusMap S φ) * (b ≫ torusMap S φ) := by
  apply (splitTorusPointsEquiv S X Z).injective
  rw [map_mul, points_comp_torusMap, points_comp_torusMap, points_comp_torusMap, map_mul,
    MonoidHom.mul_comp]

theorem isMonHom_torusMap (φ : X →+ X') : IsMonHom (torusMap S φ) := by
  constructor
  · have h : (1 : 𝟙_ (Over S) ⟶ splitTorus S X') ≫ torusMap S φ = 1 := by
      apply (splitTorusPointsEquiv S X _).injective
      rw [points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
    simpa [Hom.one_def] using h
  · simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] using
      mul_comp_torusMap (S := S) φ (fst (splitTorus S X') (splitTorus S X')) (snd _ _)

def incl {j : ℕ} (xe : X' ≃+ (Fin j → X)) (i : Fin j) : X →+ X' :=
  xe.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ => X) i)

theorem incl_apply {j : ℕ} (xe : X' ≃+ (Fin j → X)) (i : Fin j) (χ : X) :
    incl xe i χ = xe.symm (Pi.single i χ) := rfl

theorem sum_incl {j : ℕ} (xe : X' ≃+ (Fin j → X)) (x : X') : ∑ i, incl xe i (xe x i) = x := by
  simp only [incl_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, Finset.univ_sum_single, AddEquiv.symm_apply_apply]

theorem hom_ext_incl {M : Type} [CommGroup M] {j : ℕ} (xe : X' ≃+ (Fin j → X))
    {u v : Multiplicative X' →* M}
    (h : ∀ i, u.comp (AddMonoidHom.toMultiplicative (incl xe i)) =
      v.comp (AddMonoidHom.toMultiplicative (incl xe i))) : u = v := by
  refine MonoidHom.ext fun x => ?_
  have e : x = ∏ i, Multiplicative.ofAdd (incl xe i (xe x.toAdd i)) := by
    rw [← ofAdd_sum, sum_incl]; rfl
  rw [e, map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ =>
    DFunLike.congr_fun (h i) (Multiplicative.ofAdd (xe x.toAdd i))

theorem exists_hom_incl {M : Type} [CommGroup M] {j : ℕ} (xe : X' ≃+ (Fin j → X))
    (w : Fin j → (Multiplicative X →* M)) :
    ∃ u : Multiplicative X' →* M,
      ∀ i, u.comp (AddMonoidHom.toMultiplicative (incl xe i)) = w i := by
  refine ⟨∏ i, (w i).comp (AddMonoidHom.toMultiplicative
    ((Pi.evalAddMonoidHom (fun _ => X) i).comp xe.toAddMonoidHom)), fun i => ?_⟩
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.comp_apply, MonoidHom.finsetProd_apply, Finset.prod_eq_single i]
  · simp [incl_apply]
  · intro k _ hk
    simp [incl_apply, Pi.single_eq_of_ne hk]
  · simp

noncomputable def isPowGrp (S : Scheme.{0}) {j : ℕ} (xe : X' ≃+ (Fin j → X)) :
    IsPowGrp (splitTorus S X') (splitTorus S X) j where
  pr i := torusMap S (incl xe i)
  hom i := isMonHom_torusMap _
  lim := Fan.IsLimit.mk _
    (fun s => (splitTorusPointsEquiv S X' s.pt).symm
      (exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose)
    (fun s i => by
      apply (splitTorusPointsEquiv S X s.pt).injective
      refine (points_comp_torusMap (incl xe i) _).trans ?_
      rw [MulEquiv.apply_symm_apply]
      exact (exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose_spec i)
    (fun s m hm => by
      apply (splitTorusPointsEquiv S X' s.pt).injective
      rw [MulEquiv.apply_symm_apply]
      refine hom_ext_incl xe fun i => ?_
      rw [(exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose_spec i,
        ← hm i]
      exact (points_comp_torusMap (incl xe i) m).symm)

end SplitTorusPow

theorem exists_isPowGrp_splitTorus : ∀ (S : Scheme.{0}) (X X' : Type) [AddCommGroup X] [AddCommGroup X'] (j : ℕ) (xe : X' ≃+ (Fin j → X)), ∃ p : IsPowGrp (splitTorus S X') (splitTorus S X) j, ∀ (i : Fin j) (χ : X), res (fun x _ => show (p.pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU (p.pr i).left ⊤ (charUnit S X χ)) = charUnit S X' (xe.symm (Pi.single i χ)) := by
  intro S X X' _ _ j xe
  refine ⟨SplitTorusPow.isPowGrp S xe, fun i χ => ?_⟩
  ext1
  rw [← SplitTorusPow.incl_apply, ← SplitTorusPow.torusMap_char]
  change ((splitTorus S X').left.presheaf.map (𝟙 _)).hom
    ((SplitTorusPow.torusMap S (SplitTorusPow.incl xe i)).left.appTop.hom (charUnit S X χ).val) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaPowOrder

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

theorem translPt_eq {T : Over S} (x : T ⟶ A) : translPt A x = (fst T A ≫ x) * snd T A := rfl

theorem translT_one (T : Over S) : translT A (1 : T ⟶ A) = 𝟙 _ := by
  unfold translT
  rw [translPt_eq, MonObj.comp_one, _root_.one_mul, lift_fst_snd]

theorem translT_comp {T : Over S} (x y : T ⟶ A) : translT A x ≫ translT A y = translT A (y * x) := by
  unfold translT
  simp only [translPt_eq, comp_lift, lift_fst, MonObj.comp_mul, lift_snd, lift_fst_assoc, _root_.mul_assoc]

theorem translT_comp_left {T : Over S} (x : T ⟶ A) (m : ℕ) :
    (translT A x).left ≫ (translT A (x ^ m)).left = (translT A (x ^ (m + 1))).left := by
  rw [← Over.comp_left, translT_comp, ← pow_succ]

private theorem mem_wchart_of_good {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    r z ∈ L.wchart φ (fun k => J (r ≫ φ k)) := by
  unfold LB.wchart
  simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage]
  intro k
  simpa using hJ (r ≫ φ k)

private theorem germ_presheaf_map_eq_germ {X : Scheme.{0}} {U V : X.Opens} (i : U ⟶ V) (x : X) (hx : x ∈ U) (s : Γ(X, V)) :
    (X.presheaf.germ U x hx).hom ((X.presheaf.map i.op).hom s) = (X.presheaf.germ V x (i.le hx)).hom s :=
  TopCat.Presheaf.germ_res_apply _ i x hx s

private theorem germ_app_eq_stalkMap_germ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (x : X) (hx : f x ∈ U) (y : Γ(Y, U)) :
    (X.presheaf.germ (f ⁻¹ᵁ U) x hx).hom ((f.app U).hom y) =
      (f.stalkMap x).hom ((Y.presheaf.germ U (f x) hx).hom y) :=
  (Scheme.Hom.germ_stalkMap_apply f U x hx y).symm

private theorem sval_lPow_eq_of_index_eq {L : LB A.left} {k : ℤ} {T : Over S} (s : LB.Sec (LPow A L k T)) {Z : Scheme.{0}}
    (p : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (c : L.ι) (hc : J (p ≫ (snd T A).left) = c) :
    sval (L := L) s p z J = gs p z (L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => c)) (s.f (fun _ => c)) := by
  subst hc
  rfl

private theorem mem_wchart_of_good_of_index_eq {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : K → L.ι)
    (hc : ∀ k, J (r ≫ φ k) = c k) : r z ∈ L.wchart φ c := by
  have hm := mem_wchart_of_good L φ r z hJ
  have hfun : (fun k => J (r ≫ φ k)) = c := funext hc
  rw [hfun] at hm
  exact hm

private theorem val_thetaGrp_eq_of_index_eq {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) {Z : Scheme.{0}}
    (p : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (c : Fin 2 → L.ι)
    (hc : (fun b => J (p ≫ ![(snd T A).left, (translPt A θ.pt).left] b)) = c) :
    val (L := L) θ.φ p z J = gm p z (L.wchart ![(snd T A).left, (translPt A θ.pt).left] c) (θ.φ.s c) := by
  subst hc
  rfl

private theorem germ_app_presheaf_map_app_eq_germ_comp_app {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (V V' : Y.Opens)
    (h1 : V ≤ V') (h2 : V' ≤ f ⁻¹ᵁ U) (hz : r z ∈ V) (hz' : (r ≫ f) z ∈ U) (x : Γ(X, U)) :
    (Z.presheaf.germ (r ⁻¹ᵁ V) z hz).hom ((r.app V).hom ((Y.presheaf.map (homOfLE h1).op).hom
        ((Y.presheaf.map (homOfLE h2).op).hom ((f.app U).hom x)))) =
      (Z.presheaf.germ ((r ≫ f) ⁻¹ᵁ U) z hz').hom (((r ≫ f).app U).hom x) := by
  rw [germ_app_eq_stalkMap_germ r V z hz, germ_presheaf_map_eq_germ, germ_presheaf_map_eq_germ, Scheme.Hom.comp_app]
  exact (germ_app_eq_stalkMap_germ r (f ⁻¹ᵁ U) z _ _).symm

variable {A}

theorem act_sval {L : LB A.left} {k : ℤ} {T : Over S} {θ : ThetaGrp A L k T} {s s' : LB.Sec (LPow A L k T)}
    (h : IsActOf A L k θ s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι}
    (hJ : Good L z J) :
    sval (L := L) s' r z J = (val (L := L) θ.φ r z J).val * sval (L := L) s (r ≫ (translT A θ.pt).left) z J := by
  have hpt : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left]
    unfold translT
    rw [lift_snd]
  have e : J ((r ≫ (translT A θ.pt).left) ≫ (snd T A).left) =
      J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] 1) := by
    rw [Category.assoc, hpt]
    rfl
  rw [sval_lPow_eq_of_index_eq A s (r ≫ (translT A θ.pt).left) z J _ e]
  unfold IsActOf IsTwistPull at h
  have hj := h (fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i))
  have m := mem_wchart_of_good L ![(snd T A).left, (translPt A θ.pt).left] r z hJ
  have m0 := mem_wchart_of_good L (fun _ : Fin 1 => (snd T A).left) r z hJ
  have m1 : (r ≫ (translT A θ.pt).left) z ∈ L.wchart (fun _ : Fin 1 => (snd T A).left)
      (fun _ => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] 1)) := by
    rw [← e]
    exact mem_wchart_of_good L (fun _ : Fin 1 => (snd T A).left) (r ≫ (translT A θ.pt).left) z hJ
  have key := congrArg (fun x => ((T ⊗ A).left.presheaf.germ _ (r z) m).hom x) hj
  simp only at key
  erw [TopCat.Presheaf.germ_res_apply, map_mul, TopCat.Presheaf.germ_res_apply] at key
  have key2 := congrArg (r.stalkMap z).hom key
  simp only [map_mul, Scheme.Hom.germ_stalkMap_apply] at key2
  erw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply] at key2
  unfold sval val gs gm
  simp only [m0, m, m1, ↓reduceDIte]
  simp only [Scheme.Hom.comp_app, Scheme.Hom.comp_preimage, CommRingCat.hom_comp]
  convert key2 using 1
  · rfl
  · erw [Units.coe_map]
    rfl

theorem val_powGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    val (Out.powGen A L k θ n) r z J =
      ∏ i ∈ Finset.range n, val (L := L) θ.φ (r ≫ (translT A (θ.pt ^ i)).left) z J := by
  rw [← Fin.prod_univ_eq_prod_range]
  have hmem := mem_wchart_of_good L (powφ A θ.pt n) r z hJ
  have hfac : ∀ i : Fin n, val (L := L) θ.φ (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z J =
      gm (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z
        (L.wchart ![(snd T A).left, (translPt A θ.pt).left] (fun b => J (r ≫ powφ A θ.pt n (i, b))))
        (θ.φ.s (fun b => J (r ≫ powφ A θ.pt n (i, b)))) := by
    intro i
    apply val_thetaGrp_eq_of_index_eq
    funext b
    rw [Category.assoc]
    rfl
  have hmi : ∀ i : Fin n, (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z ∈
      L.wchart ![(snd T A).left, (translPt A θ.pt).left] (fun b => J (r ≫ powφ A θ.pt n (i, b))) := by
    intro i
    apply mem_wchart_of_good_of_index_eq L _ _ z hJ
    intro b
    rw [Category.assoc]
    rfl
  simp only [hfac]
  unfold val Out.powGen LB.pullGen gm
  simp only [hmem, hmi, ↓reduceDIte]
  erw [map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  apply Units.ext
  exact germ_app_presheaf_map_app_eq_germ_comp_app r _ z _ _ _ _ _ _ _ _

theorem iter_sval {L : LB A.left} {k : ℤ} {T : Over S} {θ : ThetaGrp A L k T} {n : ℕ}
    (t : Fin (n + 1) → LB.Sec (LPow A L k T)) (ht : ∀ i : Fin n, IsActOf A L k θ (t i.castSucc) (t i.succ))
    {Z : Scheme.{0}} (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) (m : ℕ) (hm : m < n + 1)
    (r : Z ⟶ (T ⊗ A).left) :
    sval (L := L) (t ⟨m, hm⟩) r z J =
      (∏ i ∈ Finset.range m, val (L := L) θ.φ (r ≫ (translT A (θ.pt ^ i)).left) z J).val *
        sval (L := L) (t 0) (r ≫ (translT A (θ.pt ^ m)).left) z J := by
  induction m generalizing r with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, Units.val_one, _root_.one_mul, pow_zero, translT_one,
      Over.id_left, Category.comp_id]
    rfl
  | succ m ih =>
    have hm' : m < n + 1 := by omega
    have hact : sval (L := L) (t ⟨m + 1, hm⟩) r z J =
        (val (L := L) θ.φ r z J).val * sval (L := L) (t ⟨m, hm'⟩) (r ≫ (translT A θ.pt).left) z J :=
      act_sval (ht ⟨m, by omega⟩) r z hJ
    rw [hact, ih hm' (r ≫ (translT A θ.pt).left)]
    simp only [Category.assoc, translT_comp_left, Finset.prod_range_succ', pow_zero, translT_one, Over.id_left,
      Category.comp_id, Units.val_mul]
    ring

private theorem germ_unit_eq_one_of_map_eq_one {X : Scheme.{0}} {V W : X.Opens} (i : V ⟶ W) (x : X) (hxV : x ∈ V) (hxW : x ∈ W)
    (u : (Γ(X, W))ˣ) (h : Units.map (X.presheaf.map i.op).hom.toMonoidHom u = 1) :
    (X.presheaf.germ W x hxW).hom (u : Γ(X, W)) = 1 := by
  have h2 := congrArg (fun v : (Γ(X, V))ˣ => (X.presheaf.germ V x hxV).hom (v : Γ(X, V))) h
  simp only [Units.coe_map, Units.val_one, map_one] at h2
  rw [← h2]
  exact (germ_presheaf_map_eq_germ i x hxV _).symm

end GlobalTheory.ThetaPowOrder

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ThetaPowOrder in
theorem thetaGrp_act_iterate_eq_of_pow_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (k : ℤ) (T : Over S) (θ : ThetaGrp A L k T) (n : ℕ), θ.pt ^ n = 1 → LB.Gen.Corr L _ _ _ _ (Out.powGen A L k θ n) (LB.oneGen L) → ∀ t : Fin (n + 1) → LB.Sec (LPow A L k T), (∀ i : Fin n, IsActOf A L k θ (t i.castSucc) (t i.succ)) → ∀ j, (t (Fin.last n)).f j = (t 0).f j := by
  intro S A _ _ L hL k T θ n hn hc t ht j
  obtain ⟨c, rfl⟩ : ∃ c, j = fun _ => c := ⟨j 0, funext fun i => by fin_cases i; rfl⟩
  apply TopCat.Presheaf.section_ext (T ⊗ A).left.sheaf
  intro x hx
  classical
  have hcov : ∀ ψ : (T ⊗ A).left ⟶ A.left, ∃ i, ψ x ∈ L.U i := by
    intro ψ
    have h1 : ψ x ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h1
  let J : ((T ⊗ A).left ⟶ A.left) → L.ι := fun ψ => if ψ = (snd T A).left then c else (hcov ψ).choose
  have hJ : Good L x J := by
    intro ψ
    by_cases hψ : ψ = (snd T A).left
    · have hx' : x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => c) := hx
      unfold LB.wchart at hx'
      simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage] at hx'
      simp only [J, hψ, if_true]
      exact hx' 0
    · simp only [J, hψ, if_false]
      exact (hcov ψ).choose_spec
  have hJc : J (𝟙 _ ≫ (snd T A).left) = c := by
    simp [J]
  have hit := iter_sval t ht x hJ n (Nat.lt_succ_self n) (𝟙 _)
  rw [← val_powGen θ n (𝟙 _) x hJ, hn, translT_one, Over.id_left, Category.comp_id] at hit
  have hv : val (L := L) (Out.powGen A L k θ n) (𝟙 _) x J = 1 := by
    have hm := mem_wchart_of_good L (powφ A θ.pt n) (𝟙 _) x hJ
    have hcc := hc (fun kk => J (𝟙 _ ≫ powφ A θ.pt n kk)) (fun e => e.elim)
      (fun k₁ k₂ h => by simp only [h]) (fun k₁ => k₁.elim) (fun _ e => e.elim)
    unfold val gm
    simp only [hm, ↓reduceDIte]
    apply Units.ext
    unfold LB.oneGen at hcc
    erw [map_one] at hcc
    exact germ_unit_eq_one_of_map_eq_one _ x (by exact ⟨hm, by simp [LB.wchart]⟩) hm _ hcc
  rw [hv, Units.val_one, _root_.one_mul] at hit
  rw [sval_lPow_eq_of_index_eq A (t ⟨n, _⟩) (𝟙 _) x J c hJc, sval_lPow_eq_of_index_eq A (t 0) (𝟙 _) x J c hJc] at hit
  unfold gs at hit
  have hx2 : (𝟙 (T ⊗ A).left) x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => c) := hx
  simp only [hx2, ↓reduceDIte] at hit
  exact hit

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isPowGrp_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j), ∃ p' : IsPowGrp ((Over.pullback f).obj G') ((Over.pullback f).obj G) j, ∀ i, p'.pr i = (Over.pullback f).map (p.pr i) := by
  intro S S' f G' G _ _ j p
  refine ⟨⟨fun i => (Over.pullback f).map (p.pr i), fun i => ?_, ?_⟩, fun i => rfl⟩
  · haveI := p.hom i
    infer_instance
  · exact isLimitFanMkObjOfIsLimit (Over.pullback f) _ _ p.lim

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj
namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem smoothOfRelativeDimension_powObj {S : Scheme.{0}} (G : Over S) (g : ℕ)
    (hG : SmoothOfRelativeDimension g G.hom) : ∀ n : ℕ, SmoothOfRelativeDimension (n * g) (powObj G n).hom
  | 0 => by
    have h : SmoothOfRelativeDimension 0 (𝟙 S) := inferInstance
    rw [Nat.zero_mul]
    exact h
  | n + 1 => by
    have ih := smoothOfRelativeDimension_powObj G g hG n
    have h1 : SmoothOfRelativeDimension (n * g) (pullback.fst G.hom (powObj G n).hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _).flip ih
    have h2 : SmoothOfRelativeDimension (n * g + g) (pullback.fst G.hom (powObj G n).hom ≫ G.hom) :=
      inferInstance
    rw [Nat.succ_mul]
    exact h2

theorem polAV_g_of_isPowPolAV : ∀ (K : Type) [Field K] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of K))),
    IsPowPolAV A' A j → A'.g = j * A.g := by
  intro K _ j A A' p
  let e : A'.A ≅ powObj A.A j := p.lim.conePointUniqueUpToIso (powIsLimit A.A j)
  have hw : A'.A.hom = e.hom.left ≫ (powObj A.A j).hom := (Over.w e.hom).symm
  have h1 := smoothOfRelativeDimension_powObj A.A A.g A.smoothDim j
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h2 : SmoothOfRelativeDimension (0 + j * A.g) A'.A.hom := by
    rw [hw]; infer_instance
  have := H1.dim_unique _ A'.smoothDim h2 (eSec A'.A (default : PrimeSpectrum K))
  simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecBGenerates
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IndivisibleSection

theorem exists_secBGenerates : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) (D : DegData R I), ∃ b : D.toPre.SecB 1 0, SecBGenerates (D := D) 1 0 b :=
  fun hS _ _ _ _ _ _ D => exists_generator D.toPre hS

end GlobalTheory.IndivisibleSection
end
