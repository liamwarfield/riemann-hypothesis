module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCoordUnitAndSectionEqExpansion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegral
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistBaseChangeOfFinrankSectionsOne
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MeetsOpensOfSeparatesSections

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaParameterOfThetaParameterMulDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierSeriesProductEqProductSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierSeriesProductEqProductSeries
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesProd

theorem hasSum_of_sumI {R F Ix : Type} [CommRing R] [NormedField F] (φ : R →+* F)
    (h1 : ∀ a, ‖φ a‖ ≤ 1) (I : Ideal R) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (ϖ : R) (hI : I = Ideal.span {ϖ})
    (hϖ : ‖φ ϖ‖ ≤ r) [Module R F] (hs : ∀ (a : R) (x : F), a • x = φ a * x) {x : Ix → F} {s : F}
    (h : GlobalTheory.UT.SumI I x s) : HasSum x s := by
  obtain ⟨N, hN, -, -, h⟩ := h
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y ∈ N, ‖y‖ ≤ C := by
    obtain ⟨T, rfl⟩ := hN
    refine ⟨∑ t ∈ T, ‖t‖, fun y hy => ?_⟩
    obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hy
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [hs, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (h1 _)
  have hb : ∀ (n : ℕ) y, y ∈ I ^ n • N → ‖y‖ ≤ r ^ n * C := by
    intro n y hy
    rw [hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [hs, norm_mul, map_pow, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hϖ n) (hC z hz) (norm_nonneg _) (pow_nonneg hr0 n)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n * C) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const C
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨S, hS⟩ := h n
  refine ⟨S, fun T hT => ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact (hb n _ (hS T hT)).trans_lt hn

theorem hasSum_conv {F X : Type} [NormedField F] [IsUltrametricDist F] [AddCommGroup X] {a b c : X → F} {x y : F}
    (ha : HasSum a x) (hb : HasSum b y) (hc : ∀ α, HasSum (fun χ => a χ * b (α - χ)) (c α)) :
    HasSum c (x * y) := by
  have : NonarchimedeanRing F :=
    { is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup (M := F)).is_nonarchimedean }
  let e : X × X ≃ X × X :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := fun q => by simp
      right_inv := fun q => by simp }
  exact ((e.hasSum_iff.2 (ha.mul_of_nonarchimedean hb))).prod_fiberwise hc

open GlobalTheory.FieldBaseChange GlobalTheory.UT

theorem mul_back {Y Y' X₁ X₂ Z₁ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k k' : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    (hL₂ : L₂.IsLB) (n : Z₁ ⟶ Y') (hn : n ≫ h₁ = 𝟙 _) {a a' a'' b b' b''}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b)
    (h' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k' g₁ h₁ a' (m ≫ f₂) (𝟙 _) b')
    (h'' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m (k + k') g₁ h₁ a'' (m ≫ f₂) (𝟙 _) b'')
    (hb : ∀ j, (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b''.f j) =
      (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b.f j) *
        (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b'.f j))
    (y : Z₁) (i : L₁.ι) (hi : g₁ y ∈ L₁.U i) :
    powVal a'' (𝟙 _) y i = powVal a (𝟙 _) y i * powVal a' (𝟙 _) y i := by
  have e₃ : g₁ = (n ≫ m) ≫ f₁ := by rw [Category.assoc, ← h.1, ← Category.assoc, hn, Category.id_comp]
  obtain ⟨i₂, a₂⟩ := exists_chart hL₂ (f₂ (m (n y)))
  have a₁ : f₁ (m (n y)) ∈ L₁.U i := by rw [e₃] at hi; exact hi
  have v := (isoRelM_iff w m k h₁ h.1 _ h.2.1 a b).1 h _ n y i₂ i a₂ a₁
  have v' := (isoRelM_iff w m k' h₁ h.1 _ h.2.1 a' b').1 h' _ n y i₂ i a₂ a₁
  have v'' := (isoRelM_iff w m (k + k') h₁ h.1 _ h.2.1 a'' b'').1 h'' _ n y i₂ i a₂ a₁
  have e : powVal b'' (n ≫ 𝟙 _) y i₂ = powVal b (n ≫ 𝟙 _) y i₂ * powVal b' (n ≫ 𝟙 _) y i₂ := by
    rw [Category.comp_id]
    exact (congrArg (gs n y _) (hb fun _ => i₂)).trans (gs_mul n y _ (mem_wchart.2 fun _ => a₂) _ _)
  rw [v, v', v'', hn, zpow_natCast, zpow_natCast, zpow_natCast, pow_add, _root_.mul_mul_mul_comm,
    ← Units.val_mul] at e
  exact (Units.mul_right_inj _).1 e

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_frm_mul {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k k' : ℕ}
    {b : TF (R := R) F ⟶ D.P.A} {w : Frm D F k b} {w' : Frm D F k' b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ w'' : Frm D F (k + k') b, w''.IsGen ∧
      ∀ z J, Good D.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J := by
  obtain ⟨w'', h, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε (k + k'))
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [CoefBasic.prod_line, CoefBasic.prod_line, CoefBasic.prod_line, pow_add, pow_add, mul_inv,
        _root_.mul_mul_mul_comm])
    (LB.mulGen D.P.L _ _ _ _ w w') (DVR.mulGen_isGen _ _ _ _ _ _ _ hw hw')
  exact ⟨w'', h, fun z J hJ => (hv _ _ z J hJ).trans (val_mul hJ _ _ _)⟩

theorem exists_back {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (F : Type) [Field F] [Algebra (FractionRing R) F] {w : W0 U} (hw : w.IsGen) {k k' : ℕ}
    {σ : U.SecGF F k} {σ' : U.SecGF F k'} {σ'' : U.SecGF F (k + k')} {s s' s''}
    (h : U.ExpandsG F k σ s) (h' : U.ExpandsG F k' σ' s') (h'' : U.ExpandsG F (k + k') σ'' s'')
    (hb : ∀ j, (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j)
        from σ''.f j) =
      (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j) from σ.f j) *
      (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j) from σ'.f j)) :
    ∃ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F (k + k')), U.ExpandsF F k w t s ∧ U.ExpandsF F k' w t' s' ∧
      U.ExpandsF F (k + k') w t'' s'' ∧
      ∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J := by
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have i₂ := fun k => (isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2
  obtain ⟨t, ht⟩ := (i₂ k σ).exists
  obtain ⟨t', ht'⟩ := (i₂ k' σ').exists
  obtain ⟨t'', ht''⟩ := (i₂ (k + k') σ'').exists
  exact ⟨t, t', t'', ⟨σ, ht, h⟩, ⟨σ', ht', h'⟩, ⟨σ'', ht'', h''⟩, fun z J hJ =>
    mul_back U.LG.isLB n.left (congrArg (fun q => q.left) hn) ht ht' ht'' hb z _ (hJ (𝟙 _ ≫ _))⟩

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k k' : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b) (w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k' g.b) (w'' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (k + k') g.b), 1 ≤ k → 1 ≤ k' → w.IsGen → w'.IsGen → w''.IsGen → ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (σ' : u.U.toUnifPre.SecGF (PadicAlgCl p) k') (σ'' : u.U.toUnifPre.SecGF (PadicAlgCl p) (k + k')) s s' s'', u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → u.U.toUnifPre.ExpandsG (PadicAlgCl p) k' σ' s' → u.U.toUnifPre.ExpandsG (PadicAlgCl p) (k + k') σ'' s'' → (∀ j, (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ''.f j) = σ.f j * (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ'.f j)) → ∀ x x', HasSum (fun χ => GlobalTheory.UT.coef s g w χ) x → HasSum (fun χ => GlobalTheory.UT.coef s' g w' χ) x' → HasSum (fun χ => GlobalTheory.UT.coef s'' g w'' χ) (κ * x * x') := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k k' g w w' w'' hk hk' hw hw' hw''
  obtain ⟨w₃, hw₃, hv⟩ := exists_frm_mul hw hw'
  obtain ⟨c, hc, -, hcoef⟩ :=
    ((CoefBasic.coef_basic _ u.D.toPre (PadicAlgCl p) (k + k') g).2.2 w₃ hw₃).2.2.1 w'' hw''
  refine ⟨c, hc, fun σ σ' σ'' s s' s'' h h' h'' hb x x' hx hx' => ?_⟩
  obtain ⟨w₀, hw₀⟩ := u.U.ext
  obtain ⟨t, t', t'', e, e', e'', hm⟩ := exists_back u.U.toUnifPre (PadicAlgCl p) hw₀ h h' h'' hb
  let φ : u.V →+* PadicAlgCl p :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))
  have : CharZero u.V := φ.charZero
  have hadm : AdmBase u.V (IsLocalRing.maximalIdeal u.V) :=
    ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hS := GlobalTheory.T.product_of_sections_expands_to_convolution hL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) w₀ hw₀ k k' (k + k') hk hk' rfl
    t t' t'' s s' s'' e e' e'' hm g w w' w₃ hw hw' hw₃ hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  have h1 : ∀ a, ‖φ a‖ ≤ 1 := fun a => (u.norm_le _).2 ⟨a, rfl⟩
  have hlt : ‖φ ϖ‖ < 1 := lt_of_le_of_ne (h1 ϖ) fun e1 => by
    obtain ⟨z, hz⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) ϖ)⁻¹).1 (by
      rw [map_inv₀, norm_inv]
      exact (congrArg (·⁻¹) e1).le.trans inv_one.le)
    have h0 : algebraMap u.V (FractionRing u.V) ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective u.V (FractionRing u.V))).2 hϖ.ne_zero
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one z (IsFractionRing.injective u.V (FractionRing u.V) ?_))
    rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]
  have hsum := hasSum_conv hx hx' fun α =>
    letI : Module u.V (PadicAlgCl p) := Module.compHom _ (algebraMap u.V (FractionRing u.V))
    hasSum_of_sumI φ h1 _ (norm_nonneg _) hlt ϖ hϖ.maximalIdeal_eq le_rfl
      (fun a x => Algebra.smul_def (algebraMap u.V (FractionRing u.V) a) x) (hS α)
  simp only [hcoef, _root_.mul_assoc]
  exact hsum.mul_left c

end GlobalTheory.ZH.SeriesProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierSeriesProductEqProductSeriesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierSeries_product_eq_product_series : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k k' : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b) (w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k' g.b) (w'' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (k + k') g.b), 1 ≤ k → 1 ≤ k' → w.IsGen → w'.IsGen → w''.IsGen → ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (σ' : u.U.toUnifPre.SecGF (PadicAlgCl p) k') (σ'' : u.U.toUnifPre.SecGF (PadicAlgCl p) (k + k')) s s' s'', u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → u.U.toUnifPre.ExpandsG (PadicAlgCl p) k' σ' s' → u.U.toUnifPre.ExpandsG (PadicAlgCl p) (k + k') σ'' s'' → (∀ j, (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ''.f j) = σ.f j * (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ'.f j)) → ∀ x x', HasSum (fun χ => GlobalTheory.UT.coef s g w χ) x → HasSum (fun χ => GlobalTheory.UT.coef s' g w' χ) x' → HasSum (fun χ => GlobalTheory.UT.coef s'' g w'' χ) (κ * x * x') := by
  first | exact @GlobalTheory.ZH.SeriesProd.main | exact GlobalTheory.ZH.SeriesProd.main | (intros; apply GlobalTheory.ZH.SeriesProd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableFourierCoefficientsFamilyFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetOfPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdjoin
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefField
open TWM TWO CoefBasic

section
variable (R : Type) [CommRing R] [IsDomain R] (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E]
  [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] {X : Scheme.{0}} {L : LB X}

omit [IsDomain R] in
theorem comp_jFK : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E = jFK (R := R) F := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

def ιE : TF (R := R) F ⟶ TF (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (comp_jFK R E F)))

omit [IsDomain R] in
theorem ι_inj : Function.Injective fun ψ : (TF (R := R) E).left ⟶ X => (ιE R E F).left ≫ ψ := by
  intro a b h
  have : Epi (ιE R E F).left := by
    show Epi (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap E F))) := inferInstance
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap E F))) :=
      ⟨fun u => ⟨IsLocalRing.closedPoint F, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (ιE R E F).left).1 h

omit [IsDomain R] in
theorem gs_ι (z : (TF (R := R) F).left) (a : Γ(Spec (CommRingCat.of E), ⊤)) :
    gs (ιE R E F).left z ⊤ a = cst F z (algebraMap E F ((Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom a)) := by
  rw [cst_eq, gs_eq _ z ⊤ trivial]
  exact congrArg ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap E F)) a)


omit [IsDomain R] in
theorem sec_rat (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → ((TF (R := R) E).left ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε))
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ X) → U), ∏ i, h ((ιE R E F).left ≫ φ i) ^ ε i = 1) :
    ∃ a : E, ∀ z J, Good L z J → sval s (ιE R E F).left z J = cst F z (algebraMap E F a) := by
  obtain ⟨s₀, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    refine Eq.trans ?_ ((hf U (Function.extend (fun ψ => (ιE R E F).left ≫ ψ) h 1)).trans (Fintype.prod_empty _).symm)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(ι_inj R E F).extend_apply]) s
  have le : (⊤ : (TF (R := R) E).left.Opens) ≤
      LB.wchart L (PEmpty.elim : PEmpty → ((TF (R := R) E).left ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom
    (((TF (R := R) E).left.presheaf.map (homOfLE le).op).hom (s₀.f PEmpty.elim)), fun z J hJ => ?_⟩
  rw [← hs _ _ z J hJ, sval_of s₀ _ z J PEmpty.elim (fun k => k.elim), ← gs_ι R E F]
  exact (gs_res _ z le trivial _).symm

def HE (L : LB X) (σ : CoefVal.FS R F X)
    (f : ∀ z : (TF (R := R) F).left, (((TF (R := R) F).left ⟶ X) → L.ι) → (TF (R := R) F).left.presheaf.stalk z)
    (x : F) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((TF (R := R) E).left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ X) → U), ∏ i, h ((ιE R E F).left ≫ φ i) ^ ε i = σ U h) ∧
    ∀ z J, Good L z J → f z J = cst F z x * (val t (ιE R E F).left z J).val

variable {R E F}

theorem HE.mul {σ σ' : CoefVal.FS R F X} {f f'} {x x' : F} (H : HE R E F L σ f x) (H' : HE R E F L σ' f' x') :
    HE R E F L (fun U _ h => σ U h * σ' U h) (fun z J => f z J * f' z J) (x * x') := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_,
    fun z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs U h) (hs' U h)
  · rw [val_mul hJ]
    simp only [e z J hJ, e' z J hJ, cst_eq, map_mul, Units.val_mul]
    ring

theorem HE.one : HE R E F L (fun _ _ _ => 1) (fun _ _ => 1) 1 :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L (Y := (TF (R := R) E).left),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun z J _ => by rw [val_one, cst_eq, map_one, Units.val_one, _root_.mul_one]⟩

theorem HE.congr {σ σ' : CoefVal.FS R F X} {f f'} {x : F} (H : HE R E F L σ f x)
    (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) (hf : ∀ z J, Good L z J → f' z J = f z J) :
    HE R E F L σ' f' x := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hs U h).trans (hσ U h), fun z J hJ => (hf z J hJ).trans (e z J hJ)⟩

theorem HE.pow {σ : CoefVal.FS R F X} {f} {x : F} (H : HE R E F L σ f x) (n : ℕ) :
    HE R E F L (fun U _ h => σ U h ^ n) (fun z J => f z J ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using HE.one
  | succ n ih => simpa only [pow_succ] using ih.mul H

theorem HE.ratio (hL : L.IsLB) {σ σ' : CoefVal.FS R F X} {f f'} {x x' : F} (H : HE R E F L σ f x)
    (H' : HE R E F L σ' f' x') (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) :
    ∃ a : E, ∀ z J, Good L z J → cst F z x' * f z J = cst F z (x * algebraMap E F a) * f' z J := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  have hu := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht')
  obtain ⟨a, hav⟩ := sec_rat R E F hL (Geo.Tor.genSec _ hu) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [hs, hs', hσ, mul_inv_cancel])
  refine ⟨a, fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_genSec _ hu _ z hJ, val_mul hJ, val_inv] at b
  have c : (val t (ιE R E F).left z J).val = cst F z (algebraMap E F a) * (val t' (ιE R E F).left z J).val := by
    rw [← b, Units.val_mul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
  rw [e z J hJ, e' z J hJ, c]
  simp only [cst_eq, map_mul]
  ring

variable {K : Type} [Fintype K] {ε : K → ℤ}

theorem he_gen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r₀ : (TF (R := R) E).left ⟶ Y) {r : (TF (R := R) F).left ⟶ Y} (hr : (ιE R E F).left ≫ r₀ = r) :
    HE R E F L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => (val t r z J).val) 1 := by
  subst hr
  exact ⟨K, _, _, ε, LB.pullGen L φ ε t r₀, pullGen_isGen _ _ _ _ ht _, fun U _ h => by simp only [Category.assoc],
    fun z J hJ => by rw [val_pull hJ, cst_eq, map_one, _root_.one_mul]⟩

theorem he_sec (hL : L.IsLB) {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (r₀ : (TF (R := R) E).left ⟶ Y) {r : (TF (R := R) F).left ⟶ Y} (hr : (ιE R E F).left ≫ r₀ = r) :
    ∃ a : E, HE R E F L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => sval s r z J) (algebraMap E F a) := by
  subst hr
  obtain ⟨t, ht⟩ := exists_gen_of_local (V := E) L hL (fun i => r₀ ≫ φ i) ε
  have hi := invGen_isGen _ _ _ _ ht
  obtain ⟨a, hav⟩ := sec_rat R E F hL (pullMulSec s r₀ _ hi) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, K, _, _, ε, t, ht, fun U _ h => by simp only [Category.assoc], fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_pullMulSec _ _ _ hi _ z hJ, val_inv] at b
  rw [← b, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem exists_he (hL : L.IsLB) {φ : K → ((TF (R := R) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (hφ : ∀ i, ∃ ψ, φ i = (ιE R E F).left ≫ ψ) :
    ∃ x : F, x ≠ 0 ∧ HE R E F L (fun _ _ h => ∏ i, h (φ i) ^ ε i) (fun z J => (val t (𝟙 _) z J).val) x := by
  choose φ₀ h₀ using hφ
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local (V := E) L hL φ₀ ε
  obtain ⟨c, hc, e⟩ := exists_ratio hL t ht (LB.pullGen L _ _ t₀ (ιE R E F).left) (pullGen_isGen _ _ _ _ ht₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [h₀])
  refine ⟨c, hc, K, _, φ₀, ε, t₀, ht₀, fun U _ h => by simp only [h₀], fun z J hJ => ?_⟩
  have := e (TF (R := R) F).left (𝟙 (TF (R := R) F).left) z J hJ
  rw [val_pull hJ, Category.id_comp] at this
  exact this

end

theorem exists_adjoin {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (A : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType A.hom] (b : TF (R := R) F ⟶ A) :
    ∃ (T : Finset F) (b₁ : TF (R := R) (IntermediateField.adjoin (FractionRing R) (T : Set F)) ⟶ A),
      ιE R _ F ≫ b₁ = b := by
  classical
  let a : Spec (CommRingCat.of F) ⟶ A.left := b.left
  obtain ⟨B, i, _, t, ht⟩ : ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ A.left) (_ : IsOpenImmersion i)
      (t : Spec B), i t = a (IsLocalRing.closedPoint F) := by
    obtain ⟨n, t, ht⟩ := A.left.affineCover.exists_eq (a (IsLocalRing.closedPoint F))
    exact ⟨_, A.left.affineCover.f n, A.left.affineCover.map_prop n, t, ht⟩
  have hr : Set.range a ⊆ Set.range i := by
    rintro _ ⟨u, rfl⟩
    exact ⟨t, ht.trans (congrArg a (Subsingleton.elim _ _))⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i a hr)
  have hφa : Spec.map φ ≫ i = a := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (show Spec B ⟶ Spec (CommRingCat.of R) from i ≫ A.hom)
  have h₂ : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₂
  have hc : ψ ≫ φ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) := by
    rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, hφa, Spec.map_comp]
    exact Over.w b
  let : Algebra R B := ψ.hom.toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Subalgebra R B).FG := (show Algebra.FiniteType R B from h₂).out
  let K := IntermediateField.adjoin (FractionRing R) ((s.image φ.hom : Finset F) : Set F)
  have hm : ∀ x : B, φ.hom x ∈ K := fun x => by
    have hx : x ∈ Algebra.adjoin R (s : Set B) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap r =>
      have e : φ.hom (algebraMap R B r) = algebraMap (FractionRing R) F (algebraMap R _ r) := congr($hc r)
      rw [e]; exact K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have e : (ιE R K F).left ≫ Spec.map (CommRingCat.ofHom (φ.hom.codRestrict K hm)) ≫ i = b.left := by
    refine Eq.trans ?_ hφa
    show Spec.map _ ≫ _ = _
    rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨s.image φ.hom, Over.homMk (Spec.map (CommRingCat.ofHom (φ.hom.codRestrict K hm)) ≫ i) ?_,
    Over.OverMorphism.ext e⟩
  apply ι_inj R K F
  show (ιE R K F).left ≫ _ ≫ _ = (ιE R K F).left ≫ _
  rw [← Category.assoc, e, Over.w, Over.w]

end GlobalTheory.UT.CoefField
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefField
open TWM TWO CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {E F : Type} [Field E] [Field F]
  [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem he_cub (x x' y : TF (R := R) E ⟶ D.P.A) :
    HE R E F D.P.L (fun _ _ h => h (ιE R E F ≫ x * ιE R E F ≫ x' * ιE R E F ≫ y).left *
      (h (ιE R E F ≫ x * ιE R E F ≫ x').left)⁻¹ * (h (ιE R E F ≫ x * ιE R E F ≫ y).left)⁻¹ *
      (h (ιE R E F ≫ x' * ιE R E F ≫ y).left)⁻¹ * h (ιE R E F ≫ x).left * h (ιE R E F ≫ x').left *
      h (ιE R E F ≫ y).left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹)
      (fun z J => (th D z J (ιE R E F ≫ x) (ιE R E F ≫ x') (ιE R E F ≫ y)).val) 1 :=
  (he_gen (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
    (lift x (lift x' y)).left (r := (lift (ιE R E F ≫ x) (lift (ιE R E F ≫ x') (ιE R E F ≫ y))).left)
    (by rw [← Over.comp_left, comp_lift, comp_lift])).congr (fun U _ h => prod_cub _ _ _ h)
    (fun _ _ _ => rfl)

theorem exists_gt (g : GtPtF D F) (b₁ : TF (R := R) E ⟶ D.P.A) (hb : ιE R E F ≫ b₁ = g.b) :
    ∃ (x : D.X → F) (S : Finset F), (∀ χ, HE R E F D.P.L (fun _ _ h => ∏ i, h (DegPre.gtφ D F g.b χ i) ^ DegPre.gtε i)
      (fun z J => (val (g.s χ) (𝟙 _) z J).val) (x χ)) ∧
      ∀ K : Subfield F, (∀ a, algebraMap E F a ∈ K) → (S : Set F) ⊆ K → ∀ χ, x χ ∈ K := by
  classical
  have hL := D.P.isLB
  choose x hx0 hx using fun χ => exists_he (R := R) (E := E) (F := F) hL (g.isGen χ) (fun i => by
    fin_cases i
    · refine ⟨(cP D _ χ * b₁).left, ?_⟩
      show (cP D _ χ * g.b).left = _
      rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hb]
    · refine ⟨(cP D _ χ).left, ?_⟩
      show (cP D _ χ).left = _
      rw [← Over.comp_left, comp_cP]
    · refine ⟨b₁.left, ?_⟩
      show g.b.left = _
      rw [← Over.comp_left, hb]
    · refine ⟨(1 : TF (R := R) E ⟶ D.P.A).left, ?_⟩
      show (1 : TF (R := R) F ⟶ D.P.A).left = _
      rw [← Over.comp_left, MonObj.comp_one])
  have hadd : ∀ χ χ', ∃ a : E, x (χ + χ') = x χ * x χ' * algebraMap E F a := fun χ χ' => by
    have C := he_cub (F := F) (cP D _ χ) (cP D _ χ') b₁
    rw [comp_cP, comp_cP, hb] at C
    obtain ⟨a, ha⟩ := ((hx χ).mul (hx χ')).ratio hL ((hx (χ + χ')).mul C) (fun U _ h => by
      rw [prod_gt, prod_gt, prod_gt, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    obtain ⟨z⟩ := exists_pt (R := R) (F := F)
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have e := gt_mul (𝟙 (TF (R := R) F)) hJ g χ χ'
    rw [Category.id_comp, Over.id_left] at e
    have e' := ha z J hJ
    rw [← Units.val_mul, ← Units.val_mul, e, Units.mul_left_inj, _root_.mul_one, cst_eq, cst_eq] at e'
    exact ⟨a, cstH_inj z e'⟩
  obtain ⟨T, hT⟩ : (⊤ : Submodule ℤ D.X).FG := Module.Finite.fg_top
  refine ⟨x, T.image x, hx, fun K hK hS χ => ?_⟩
  have h0 : x 0 ∈ K := by
    obtain ⟨a, ha⟩ := hadd 0 0
    rw [add_zero, _root_.mul_assoc, left_eq_mul₀ (hx0 0)] at ha
    rw [eq_inv_of_mul_eq_one_left ha]
    exact inv_mem (hK a)
  let G : AddSubgroup D.X :=
    { carrier := {χ | x χ ∈ K}
      zero_mem' := h0
      add_mem' := fun {χ χ'} h h' => by
        obtain ⟨a, ha⟩ := hadd χ χ'
        show x _ ∈ K
        rw [ha]; exact mul_mem (mul_mem h h') (hK a)
      neg_mem' := fun {χ} h => by
        obtain ⟨a, ha⟩ := hadd χ (-χ)
        rw [add_neg_cancel] at ha
        have ha0 : algebraMap E F a ≠ 0 := fun h0 => hx0 0 (by rw [ha, h0, MulZeroClass.mul_zero])
        have e : x (-χ) = x 0 * (x χ)⁻¹ * (algebraMap E F a)⁻¹ := by
          have := hx0 χ
          rw [ha]; field_simp
        show x _ ∈ K
        rw [e]; exact mul_mem (mul_mem h0 (inv_mem h)) (inv_mem (hK a)) }
  have hle : Submodule.span ℤ (T : Set D.X) ≤ G.toIntSubmodule :=
    Submodule.span_le.2 fun t ht => hS (by simpa using ⟨t, ht, rfl⟩)
  exact hle (hT ▸ Submodule.mem_top)

theorem fe_at (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (b : TF (R := R) F ⟶ D.P.A) (b₁ : TF (R := R) E ⟶ D.P.A)
    (hb : ιE R E F ≫ b₁ = b) (α mu : D.X) :
    ∃ f, HE R E F D.P.L (fun _ _ h => (h b.left ^ ((k : ℤ) - 1) * h (cP D _ (α + k • mu) * b).left *
        (h (cP D _ (α + k • mu)).left)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left) *
        (h (b * cP D _ mu).left ^ ((k : ℤ) - 1) * h (cP D _ α * (b * cP D _ mu)).left *
        (h (cP D _ α).left)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹) f 1 ∧
      ∀ z J, Good D.P.L z J → sval (s.s (α + k • mu)) (lift (𝟙 (TF (R := R) F)) b).left z J =
        sval (s.s α) (lift (𝟙 (TF (R := R) F)) (b * cP D _ mu)).left z J * f z J := by
  have hL := D.P.isLB
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu α
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := E) hG k mu α
  let ρ' : TF (R := R) F ⟶ DegPre.BF D E := lift (ιE R E F) b
  have hρ : (ιE R E F).left ≫ (lift (𝟙 (TF (R := R) E)) b₁).left = ρ'.left := by
    rw [← Over.comp_left, comp_lift, Category.comp_id, hb]
  have p₁ : ρ' ≫ DegPre.prB D E = b := lift_snd _ _
  have p₂ : (ρ' ≫ DegPre.trF D E mu) ≫ DegPre.prB D E = b * cP D _ mu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, p₁, comp_cP, comp_cP]
  refine ⟨fun z J => (val u' ρ'.left z J).val, (he_gen hu' _ hρ).congr (fun U _ h => ?_) (fun _ _ _ => rfl),
    fun z J hJ => ?_⟩
  · have q₁ := prod_fam D E ρ' (α + k • mu) k h
    have q₂ := prod_fam D E (ρ' ≫ DegPre.trF D E mu) α k h
    rw [p₁] at q₁
    rw [p₂] at q₂
    rw [← q₁, ← prod_neg _ _ q₂, Fintype.prod_sum_type]
    rfl
  · have e := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu α u hu hc) _ (lift (𝟙 (TF (R := R) F)) b).left z J hJ
    have t : lift (𝟙 (TF (R := R) F)) b ≫ DegPre.trF D F mu = lift (𝟙 (TF (R := R) F)) (b * cP D _ mu) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, trF_eq, tr_fst, lift_fst, lift_fst]
      · rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, lift_snd, lift_snd, comp_cP, comp_cP]
    rw [← Over.comp_left, t] at e
    refine e.trans (congrArg₂ (· * ·) rfl (congrArg Units.val ?_))
    rw [hv u hu hc _ (lift (𝟙 (TF (R := R) F)) b) z J hJ, hv' u' hu' hc' _ ρ' z J hJ, val_famMult _ hJ,
      val_famMult _ hJ, uVal, uVal, p₁, lift_snd, lift_fst, lift_fst, comp_cP, comp_cP, comp_cP, comp_cP]
    have j : (ιE R E F).left ≫ jFK (R := R) E = Over.Hom.left (𝟙 (TF (R := R) F)) ≫ jFK (R := R) F :=
      (comp_jFK R E F).trans (Category.id_comp _).symm
    rw [j]

theorem exists_finset_of_point (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (s : Fam D F k) (g : GtPtF D F)
    {w : Frm D F k g.b} (hw : w.IsGen) (b₁ : TF (R := R) E ⟶ D.P.A) (hb : ιE R E F ≫ b₁ = g.b)
    (hs : ∀ α, ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (σF i)
        (D.famφB α) (DegPre.famε k) (σ i) (DegPre.prB D F).left 1) ∧
      ∀ j, (s.s α).f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) :
    ∃ S : Finset F, ∀ K : Subfield F, (∀ a, algebraMap E F a ∈ K) → (S : Set F) ⊆ K → ∀ χ, coef s g w χ ∈ K := by
  classical
  have hL := D.P.isLB
  obtain ⟨x, S, hx, hS⟩ := exists_gt g b₁ hb
  obtain ⟨ω, -, hω⟩ := exists_he (R := R) (E := E) (F := F) hL hw (fun i => by
    fin_cases i
    · refine ⟨(1 : TF (R := R) E ⟶ D.P.A).left, ?_⟩
      show (1 : TF (R := R) F ⟶ D.P.A).left = _
      rw [← Over.comp_left, MonObj.comp_one]
    · refine ⟨b₁.left, ?_⟩
      show g.b.left = _
      rw [← Over.comp_left, hb])
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.X k hk
  choose n a σ σF hσ hsum using hs
  have Rg := (he_gen (R := R) (E := E) (F := F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1)
    D.rig_gen (TF (R := R) E).hom (Over.w (ιE R E F))).pow k
  refine ⟨insert ω (S ∪ Finset.univ.biUnion fun i => Finset.univ.image (a (e i))), fun K hK hSK χ => ?_⟩
  obtain ⟨i₀, ⟨mu, rfl⟩, -⟩ := he χ
  set α := e i₀ with hα
  obtain ⟨f, hf, hfe⟩ := fe_at (E := E) hG s g.b b₁ hb α mu
  have key : ∀ i, ∃ c : F, c ∈ K ∧ ∀ z J, Good D.P.L z J →
      sval (σ α i) (g.b * cP D _ mu).left z J * f z J * (val (g.s (α + k • mu)) (𝟙 _) z J).val * (val w (𝟙 _) z J).val =
        cst F z c * (rigV D (TF (R := R) F).hom z J).val ^ k := fun i => by
    obtain ⟨y, A⟩ := he_sec (R := R) (E := E) (F := F) hL (σ α i) (b₁ * cP D _ mu).left (r := (g.b * cP D _ mu).left)
      (by rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hb])
    obtain ⟨c, hc⟩ := (((A.mul hf).mul (hx (α + k • mu))).mul hω).ratio hL Rg (fun U _ h => by
      have e₀ : (TF (R := R) F).hom ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left := rfl
      have e₁ : SectionScalarValuation.cQ D (TF (R := R) F) α = cP D _ α := rfl
      rw [SectionScalarValuation.prod_famB, prod_gt, prod_line, Fintype.prod_unique, e₀, e₁, mul_comm _ (cP D _ α)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    refine ⟨_, mul_mem (mul_mem (mul_mem (mul_mem (hK y) (one_mem K))
      (hS K hK (fun t ht => hSK (by simp [show t ∈ S from ht])) (α + k • mu))) (show ω ∈ K from hSK (by simp))) (hK c),
      fun z J hJ => ?_⟩
    have := hc z J hJ
    rw [one_pow, cst_eq, map_one, _root_.one_mul] at this
    exact this
  choose c hcK hc using key
  have E₀ : coef s g w (α + k • mu) = ∑ i, a α i * c i := coef_eq fun z J hJ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfe z J hJ, SectionScalarValuation.sval_lin (fun i => gF D F (a α i)) (σF α) (fun j => hsum α j) _ z hJ, cst_eq, map_sum,
      Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have b : gs (lift (𝟙 (TF (R := R) F)) (g.b * cP D _ mu)).left z ⊤ (gF D F (a α i)) = cst F z (a α i) := by
      refine (gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    have e₂ := SectionScalarValuation.secScal_sval (hσ α i) (lift (𝟙 (TF (R := R) F)) (g.b * cP D _ mu)).left z hJ
    rw [← Over.comp_left, lift_snd] at e₂
    rw [b, map_mul, ← cst_eq, ← cst_eq, _root_.mul_assoc, ← hc i z J hJ, ← e₂]
    ring
  rw [E₀]
  exact sum_mem fun i _ => mul_mem (hSK (by
    simp only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union, Finset.mem_coe,
      Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨i₀, i, rfl⟩))) (hcK i)

theorem exists_finset (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (s : Fam D F k) (g : GtPtF D F)
    {w : Frm D F k g.b} (hw : w.IsGen)
    (hs : ∀ α, ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (σF i)
        (D.famφB α) (DegPre.famε k) (σ i) (DegPre.prB D F).left 1) ∧
      ∀ j, (s.s α).f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) :
    ∃ S : Finset F, ∀ K : Subfield F, (∀ a, algebraMap (FractionRing R) F a ∈ K) → (S : Set F) ⊆ K →
      ∀ χ, coef s g w χ ∈ K := by
  classical
  have := D.P.isAb.proper
  obtain ⟨T, b₁, hb⟩ := exists_adjoin D.P.A g.b
  obtain ⟨S, hS⟩ := exists_finset_of_point hG hk s g hw b₁ hb hs
  refine ⟨S ∪ T, fun K hK hST => hS K (fun a => ?_) fun t ht => hST (by simp [show t ∈ S from ht])⟩
  have hle : IntermediateField.adjoin (FractionRing R) (T : Set F) ≤ K.toIntermediateField hK :=
    IntermediateField.adjoin_le_iff.2 fun t ht => hST (by simp [show t ∈ T from ht])
  exact hle a.2

end GlobalTheory.UT.CoefField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableFourierCoefficientsFamilyFiniteExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesConv

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefVal

theorem summable_coef : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (s : Fam u.D.toPre (PadicAlgCl p) k) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), w.IsGen → Summable (fun χ => GlobalTheory.UT.coef s g w χ) ∧ Filter.Tendsto (fun χ => GlobalTheory.UT.coef s g w χ) Filter.cofinite (nhds 0) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ χ, GlobalTheory.UT.coef s g w χ ∈ K := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u _ k hk s g w hw
  have hTW : TwistBCSpanStatement := twistBCSpan_of (GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hLL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using DVR.QForm.exists_QVal hϖ u.D
  have h0 := PsiForm.norm_pos_of_irreducible (F := PadicAlgCl p) hϖ
  have h1 := PsiForm.norm_lt_one_of_irreducible u.norm_le hϖ
  obtain ⟨v, hvn⟩ := PadicVal.exists_addValuation _ h0 h1
  have hv : ValOver ϖ (PadicAlgCl p) v := fun c n hc => by
    have e := PsiForm.norm_of_hasVal u.norm_le hϖ hc
    obtain ⟨q, hq, hq'⟩ := hvn (algebraMap _ _ c) (norm_pos_iff.1 (by rw [e]; exact Real.exp_pos _))
    rw [e, Real.log_exp, neg_mul, neg_neg, mul_comm, mul_left_inj' (Real.log_neg h0 h1).ne] at hq'
    have : q = n := by exact_mod_cast hq'.symm
    rw [hq, this]
  have ht : Filter.Tendsto (fun χ => coef s g w χ) Filter.cofinite (nhds 0) := by
    refine PadicVal.tendsto_of_null h0 h1 hvn fun q => ?_
    obtain ⟨l, hl, -⟩ := exists_gtV (hϖ := hϖ) (hv := hv) g
    obtain ⟨ω, hω⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw
    obtain ⟨r, hr⟩ := exists_nuGe hϖ hv hTW hQ hk s
    refine (finite_sublevel hϖ hQ hk l (q - r - ω)).subset fun χ hχ => ?_
    have h : r + (Q χ : ℚ) / k + l χ + ω < q :=
      WithTop.coe_lt_coe.1 ((le_v_coef hw (hr χ) (hl χ) hω).trans_lt hχ)
    show (Q χ : ℚ) / k + l χ ≤ q - r - ω
    linarith
  obtain ⟨T, hT⟩ := CoefField.exists_finset hLL.1.globalFns hk s g hw fun α => by
    obtain ⟨r, n, a, σ, σF, hσ, -, hsum⟩ := exists_vge hϖ hv hTW hk (s.s α)
    exact ⟨n, a, σ, σF, hσ, hsum⟩
  obtain ⟨-, -, -, K₀, hK₀, hK⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hm : ∀ χ, coef s g w χ ∈ K₀ ⊔ IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p)) :=
    hT (K₀ ⊔ IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p))).toSubfield
      (fun a => (le_sup_left : K₀ ≤ _) (show _ ∈ (K₀ : Set (PadicAlgCl p)) from hK ▸ ⟨a, rfl⟩))
      (fun t h => (le_sup_right : _ ≤ K₀ ⊔ _) (IntermediateField.subset_adjoin _ _ h))
  exact ⟨PadicVal.summable_of_mem _ hm ht, ht, _, inferInstance, hm⟩

end GlobalTheory.ZH.SeriesConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableFourierCoefficientsFamilyFiniteExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_fourierCoefficients_family_finite_extension : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (s : Fam u.D.toPre (PadicAlgCl p) k) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), w.IsGen → Summable (fun χ => GlobalTheory.UT.coef s g w χ) ∧ Filter.Tendsto (fun χ => GlobalTheory.UT.coef s g w χ) Filter.cofinite (nhds 0) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ χ, GlobalTheory.UT.coef s g w χ ∈ K := by
  first | exact @GlobalTheory.ZH.SeriesConv.summable_coef | exact GlobalTheory.ZH.SeriesConv.summable_coef | (intros; apply GlobalTheory.ZH.SeriesConv.summable_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaParameterOfThetaParameterMulDegree
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.ParameterRoot

section Sections

variable {X Y : Scheme.{0}} {L : LB X} {f : Y ⟶ X}

def mulPow {k k' : ℕ} (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => (k : ℤ))))
    (t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => (k' : ℤ)))) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => ((k + k' : ℕ) : ℤ))) where
  f j := @id Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) (s.f j) * @id Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) (t.f j)
  compat i j := by
    let W : Y.Opens := LB.wchart L (fun _ : Fin 1 => f) i ⊓ LB.wchart L (fun _ : Fin 1 => f) j
    let gg : ℕ → Γ(Y, W)ˣ := fun d => (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => (d : ℤ))).g i j
    have e : gg (k + k') = gg k * gg k' := by
      simp only [gg, LB.LinComb, Fin.prod_univ_one, Nat.cast_add, zpow_add]
    let r₁ := (Y.presheaf.map (homOfLE (inf_le_left : W ≤ LB.wchart L (fun _ : Fin 1 => f) i)).op).hom
    let r₂ := (Y.presheaf.map (homOfLE (inf_le_right : W ≤ LB.wchart L (fun _ : Fin 1 => f) j)).op).hom
    have hs : r₁ (s.f i) = (gg k).val * r₂ (s.f j) := s.compat i j
    have ht : r₁ (t.f i) = (gg k').val * r₂ (t.f j) := t.compat i j
    have key : ∀ a a' b b', r₁ a = (gg k).val * r₂ b → r₁ a' = (gg k').val * r₂ b' →
        r₁ (a * a') = (gg (k + k')).val * r₂ (b * b') := by
      intro a a' b b' h h'
      rw [map_mul, map_mul, h, h', e, Units.val_mul]
      ring
    exact key _ _ _ _ hs ht

end Sections

section Algebra

theorem cancel {F T : Type} [Field F] (x v : T → F) (t₀ : T) (κ κ' : F) (m : ℕ) (hκ : κ ≠ 0) (hκ' : κ' ≠ 0)
    (h₀ : v t₀ ≠ 0) (h : ∀ t, κ * x t * x t₀ ^ m = κ' * (v t * v t₀ ^ m)) :
    ∃ c : F, c ≠ 0 ∧ ∀ t, x t = c * v t := by
  have hx : x t₀ ≠ 0 := by
    intro e
    have := h t₀
    rw [e, MulZeroClass.mul_zero, MulZeroClass.zero_mul] at this
    exact mul_ne_zero hκ' (mul_ne_zero h₀ (pow_ne_zero m h₀)) this.symm
  refine ⟨κ' * v t₀ ^ m / (κ * x t₀ ^ m), div_ne_zero (mul_ne_zero hκ' (pow_ne_zero m h₀))
    (mul_ne_zero hκ (pow_ne_zero m hx)), fun t => ?_⟩
  have := h t
  field_simp
  linear_combination this

end Algebra

section Point

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : UnifPre I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_val_ne_zero (hA : AmpleSt) {N : ℕ} (hN : 4 ≤ N) (x : Sp F ⟶ (UnifPre.GF (G := G) F).left)
    (l : U.LG.L.ι) (hl : ⊤ ≤ x ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => l)) :
    ∃ σ : U.SecGF F N, valF x _ (σ.f (fun _ => l)) ≠ 0 := by
  have hm := MatchCoord.mem_of_le hl
  obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB (MatchCoord.pt F)
    (fun _ : Fin 1 => x ≫ UnifPre.gFK (G := G) F) (fun _ => l) (fun _ _ _ => rfl)
    (fun k => Set.mem_iInter.1 hm k)
  obtain ⟨s, hs⟩ := GenericGenerated.exists_secK_isUnit hA R I D A G U N hN _
    (x ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) (MatchCoord.pt F) J hJ
  let σ : U.SecGF F N := H1.SectionArithmetic.pullSec s (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left
  have h₁ : sval σ x (MatchCoord.pt F) J = _ := H1.SectionArithmetic.sval_pullSec s _ x (MatchCoord.pt F) hJ
  have h₂ := sval_of σ x (MatchCoord.pt F) J (fun _ => l) e
  refine ⟨σ, fun h0 => ?_⟩
  have h₃ := MatchCoord.stk_valF hl (σ.f (fun _ => l))
  have h₄ : gs x (MatchCoord.pt F) _ (σ.f (fun _ => l)) = 0 :=
    h₃.symm.trans ((congrArg _ h0).trans (map_zero _))
  exact not_isUnit_zero ((congrArg IsUnit (h₁.symm.trans (h₂.trans h₄))).mp hs)

end Point

theorem parAt_of_parAt_mul : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N k : ℕ) (a : u.PtC) (g : GtPtF u.D.toPre (PadicAlgCl p)), 4 ≤ N → 1 ≤ k → u.ParAt (N * k) a g → u.ParAt N a g := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u lab N k a g hN hk H w hw l hl
  let x : Sp (PadicAlgCl p) ⟶ (UnifPre.GF (G := u.G) (PadicAlgCl p)).left :=
    (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left
  have hx : x ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = u.toG a := by
    have : x ≫ (snd (TFK (R := u.V) (PadicAlgCl p)) ((Over.pullback (jK u.V)).obj u.G)).left = a.left :=
      congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst u.G.hom (jK u.V)) this)
  have hl' : ⊤ ≤ x ⁻¹ᵁ LB.wchart u.U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => l) := by
    intro z _
    refine Set.mem_iInter.2 fun _ => ?_
    have : (x ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p)) z ∈ u.U.LG.L.U l := by
      rw [hx]; exact hl (Set.mem_univ z)
    exact this
  let v : ∀ d : ℕ, u.U.toUnifPre.SecGF (PadicAlgCl p) d → PadicAlgCl p := fun d σ =>
    valF x (LB.wchart u.U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => l))
      (σ.f (fun _ => l))
  have expd : ∀ d : ℕ, 1 ≤ d → ∀ σ : u.U.toUnifPre.SecGF (PadicAlgCl p) d,
      ∃ s, u.U.toUnifPre.ExpandsG (PadicAlgCl p) d σ s := fun d hd σ =>
    ((FieldBaseChange.expandsG_bijective u.U.toUnifPre (PadicAlgCl p) hL.1.globalFns hd (u.U.expand d hd)).1 σ).exists
  have summ : ∀ s : Fam u.D.toPre (PadicAlgCl p) N,
      HasSum (fun χ => GlobalTheory.UT.coef s g w χ) (∑' χ, GlobalTheory.UT.coef s g w χ) := fun s =>
    (GlobalTheory.T.summable_fourierCoefficients_family_finite_extension hL o Ω S ρ p y₀ u lab N (by omega) s g w hw).1.hasSum
  obtain ⟨σ₀, h₀⟩ : ∃ σ, v N σ ≠ 0 := exists_val_ne_zero u.U.toUnifPre hL.1.ample hN x l hl'
  obtain ⟨s₀, hs₀⟩ := expd N (by omega) σ₀
  have key : ∀ (m d : ℕ), d = N * (m + 1) → ∃ w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) d g.b, w'.IsGen ∧
      ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ σ s, u.U.toUnifPre.ExpandsG (PadicAlgCl p) N σ s →
        ∃ τ t, u.U.toUnifPre.ExpandsG (PadicAlgCl p) d τ t ∧ v d τ = v N σ * v N σ₀ ^ m ∧
          HasSum (fun χ => GlobalTheory.UT.coef t g w' χ)
            (κ * (∑' χ, GlobalTheory.UT.coef s g w χ) * (∑' χ, GlobalTheory.UT.coef s₀ g w χ) ^ m) := by
    intro m
    induction m with
    | zero =>
      intro d hd
      obtain rfl : N = d := by omega
      refine ⟨w, hw, 1, one_ne_zero, fun σ s hs => ⟨σ, s, hs, by simp, ?_⟩⟩
      simpa using summ s
    | succ m ih =>
      intro d hd
      obtain ⟨w', hw', κ, hκ, h⟩ := ih _ rfl
      obtain rfl : d = N * (m + 1) + N := hd
      have h1 : 1 ≤ N * (m + 1) := Nat.mul_pos (by omega) (by omega)
      obtain ⟨w'', hw''⟩ : ∃ w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (N * (m + 1) + N) g.b, w.IsGen :=
        DVR.exists_gen_of_local (V := PadicAlgCl p) u.D.toPre.P.L u.D.toPre.P.isLB _ _
      obtain ⟨c, hc, hp⟩ := GlobalTheory.T.fourierSeries_product_eq_product_series hL o Ω S ρ p y₀ u lab (N * (m + 1)) N g w' w w'' h1 (by omega) hw' hw hw''
      refine ⟨w'', hw'', c * κ, mul_ne_zero hc hκ, fun σ s hs => ?_⟩
      obtain ⟨τ, t, hτ, e, hsum⟩ := h σ s hs
      obtain ⟨t', ht'⟩ := expd (N * (m + 1) + N) (by omega) (mulPow τ σ₀)
      refine ⟨mulPow τ σ₀, t', ht', ?_, ?_⟩
      · have : v _ (mulPow τ σ₀) = v _ τ * v _ σ₀ := MatchCoord.valF_mul hl' _ _
        rw [this, e]; ring
      · convert hp τ σ₀ (mulPow τ σ₀) t s₀ t' hτ hs₀ ht' (fun _ => rfl) _ _ hsum (summ s₀) using 1
        ring
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨w', hw', κ, hκ, h⟩ := key m _ rfl
  obtain ⟨κ', hκ', h'⟩ := H w' hw' l hl
  obtain ⟨c, hc, e⟩ := cancel (T := {q : u.U.toUnifPre.SecGF (PadicAlgCl p) N × Fam u.D.toPre (PadicAlgCl p) N //
      u.U.toUnifPre.ExpandsG (PadicAlgCl p) N q.1 q.2}) (fun q => ∑' χ, GlobalTheory.UT.coef q.1.2 g w χ)
    (fun q => v N q.1.1) ⟨(σ₀, s₀), hs₀⟩ κ κ' m hκ hκ' h₀ (fun q => by
      obtain ⟨τ, t, hτ, e, hsum⟩ := h q.1.1 q.1.2 q.2
      exact (hsum.unique (h' τ t hτ)).trans (congrArg (κ' * ·) e))
  refine ⟨c, hc, fun σ s hs => ?_⟩
  have := summ s
  rw [e ⟨(σ, s), hs⟩] at this
  exact this

end GlobalTheory.ParameterRoot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaParameterOfThetaParameterMulDegreeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaParameter_of_thetaParameter_mul_degree : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N k : ℕ) (a : u.PtC) (g : GtPtF u.D.toPre (PadicAlgCl p)), 4 ≤ N → 1 ≤ k → u.ParAt (N * k) a g → u.ParAt N a g := by
  first | exact @GlobalTheory.ParameterRoot.parAt_of_parAt_mul | exact GlobalTheory.ParameterRoot.parAt_of_parAt_mul | (intros; apply GlobalTheory.ParameterRoot.parAt_of_parAt_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionParameterGenericFibrePoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem exists_parAt : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a : u.PtC), ∃ g, u.ParAt S.N a g := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l a
  have hN : 4 ≤ S.N := by
    rw [ρ.N_eq]
    have h1 : 2 ≤ ρ.n ^ ρ.k := le_trans ρ.n_prime.two_le
      (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    nlinarith
  haveI : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  obtain ⟨k, hk, hint⟩ := GlobalTheory.T.theta_test_power_integral hL o Ω S ρ p y₀ u a
  obtain ⟨a₁, ⟨c, hc, hca⟩, hpow⟩ := GlobalTheory.T.exists_integral_nthRoot_testModel_point hL o Ω S ρ p y₀ u (a ^ k) k hk hint
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.exists_torusExtensionPoint_of_integralModelPoint hL o Ω S ρ p y₀ u c hc
  have hpar := (GlobalTheory.T.torusCoord_unit_and_section_eq_expansion hL o Ω S ρ p y₀ u c g₁ a₁ hc hca hg₁).2
  have hNk : 1 ≤ S.N * k := Nat.mul_pos (by omega) hk
  obtain ⟨f, hf, hsurj, -⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.N * k) hNk
  haveI : IsMonHom u.U.gen.hom := u.U.gen_hom
  have hk' : (a₁ ≫ u.U.gen.hom) ^ k = (a ≫ u.U.gen.hom) ^ k := by
    rw [← MonObj.pow_comp, ← MonObj.pow_comp, hpow]
  have hx : ((a ≫ u.U.gen.hom) * (a₁ ≫ u.U.gen.hom)⁻¹) ^ (S.N * k) = 1 := by
    rw [mul_comm S.N k, pow_mul, mul_pow, inv_pow, hk', mul_inv_cancel, one_pow]
  obtain ⟨pk, hpk⟩ := hsurj _ hx
  obtain ⟨g, hg⟩ := (gt_add_iota_sub_exist hL o Ω S ρ p y₀ u).1 pk.g g₁
  refine ⟨g, GlobalTheory.T.thetaParameter_of_thetaParameter_mul_degree hL o Ω S ρ p y₀ u l S.N k a g hN hk ?_⟩
  exact ParTranslate.parAt_translate hL o Ω S ρ p y₀ u (S.N * k) pk _ a₁ a g₁ g hNk
    ((hf pk _).2 hpk.symm) (by rw [inv_mul_cancel_right]) hg (hpar _ hNk)

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionParameterGenericFibrePointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusExtension_parameter_genericFibrePoint : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a : u.PtC), ∃ g, u.ParAt S.N a g := by
  first | exact @GlobalTheory.ZH.exists_parAt | exact GlobalTheory.ZH.exists_parAt | (intros; apply GlobalTheory.ZH.exists_parAt <;> assumption)
end
