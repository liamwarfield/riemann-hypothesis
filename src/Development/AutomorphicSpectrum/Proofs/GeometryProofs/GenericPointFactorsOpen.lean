module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVDesc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalLatticeHeightFormula
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeGeo

theorem exists_factor_XF_of_genericPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X), GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ genericPoints Y.X →
      ∃ y₀ : Sp Ω ⟶ Xo.XF c, ξ = y₀ ≫ Y.j := by
  intro E _ _ _ H D l Xo c Y Ω _ ξ hξ
  obtain ⟨K, _, _, n, x, y, ht, -, he⟩ := GlobalTheory.T.generic_point_normal_coords E H D l Xo c Y _ hξ
  obtain ⟨i, hi⟩ := GlobalTheory.CompanionTheory.Ar.TowerOfTest.factor (y ≫ Y.j) ht.gen ξ he.symm
  exact ⟨Spec.map (CommRingCat.ofHom i) ≫ y, by rw [hi, Category.assoc]⟩

end GlobalTheory.CompanionTheory.Ar.ChangeGeo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_factors_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X), GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ genericPoints Y.X → ∃ y₀ : Sp Ω ⟶ Xo.XF c, ξ = y₀ ≫ Y.j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_factor_XF_of_genericPoint | exact GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_factor_XF_of_genericPoint | (intros; apply GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_factor_XF_of_genericPoint <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueUniqueBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueUniqueBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.TorsExist

open GlobalTheory.CompanionTheory.Ar.Sl.Transl

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem exists_mulGen {P : RigLB G} (c : CubicalStr G P) (hs : P.IsSymmetric) (N : ℕ) :
    ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), w.IsGen := by
  refine (genOf_pow c hs (𝟙 G) N).inv.gen P.isLB fun U _ h => ?_
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, Over.id_left, mul_inv, inv_inv]
  norm_cast
  exact mul_comm _ _

theorem valF_spMap {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens)
    (a : Γ(X, U)) : valF (spMap f ≫ x) U a = f (valF x U a) := by
  have z' : Sp F' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F')
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · have h' : ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U :=
      (top_le_iff_mem _ U z').2 ((top_le_iff_mem x U (spMap f z')).1 h)
    have e₀ : (spMap f).appLE ⊤ ⊤ (by first | exact le_rfl | simp) = (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have e : (spMap f ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap f).appTop := by
      rw [← e₀]
      exact (Scheme.Hom.appLE_comp_appLE (spMap f) x U ⊤ ⊤ h _).symm
    have n := congrArg (fun φ => φ.hom ((x.appLE U ⊤ h).hom a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
    rw [valF, valF, dite_eq_left h, dite_eq_left h', e]
    exact n
  · have h' : ¬ ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U := fun k =>
      h ((top_le_iff_mem x U (spMap f z')).2 ((top_le_iff_mem _ U z').1 k))
    rw [valF, valF, dite_eq_right h, dite_eq_right h', map_zero]

theorem val_ne_zero {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)ˣ)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : valF x U f.val ≠ 0 := by
  unfold valF
  rw [dite_eq_left h]
  exact ((f.isUnit.map _).map _).ne_zero

theorem exists_torsVal {P : RigLB G} (c : CubicalStr G P) (hs : P.IsSymmetric) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F]
    {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) {N : ℕ} (hN : 1 ≤ N) (hy : y ^ N = 1) : ∃ T : F, TorsVal P s y N T := by
  obtain ⟨w, hw⟩ := exists_mulGen c hs N
  have z : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  obtain ⟨i₀, h₀⟩ := exists_chart P.isLB ((1 : Over.mk b ⟶ G).left z)
  obtain ⟨i, hi⟩ := exists_chart P.isLB (y.left z)
  have e₁ : (1 : Over.mk b ⟶ G).left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (1 : Over.mk b ⟶ G).left := by
    rw [left_pow, one_pow]
  have e₂ : b ≫ eSec G = (1 : Over.mk b ⟶ G).left := (one_left (Over.mk b)).symm
  have m₁ : (1 : Over.mk b ⟶ G).left z ∈ LB.wchart P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![i₀, i₀] := by
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show (((1 : Over.mk b ⟶ G).left ≫ ((𝟙 G : G ⟶ G) ^ N).left) z) ∈ P.L.U i₀
      rw [e₁]; exact h₀
    · exact h₀
  have m₂ : b z ∈ LB.wchart P.L (K := PUnit) (fun _ => eSec G) (fun _ => i₀) := by
    refine Set.mem_iInter.2 fun _ => ?_
    show (b ≫ eSec G) z ∈ P.L.U i₀
    rw [e₂]; exact h₀
  have n₁ := val_ne_zero _ _ (w.s ![i₀, i₀]) ((top_le_iff_mem _ _ z).2 m₁)
  have n₂ := val_ne_zero (X := (𝟙_ (Over S)).left) b _ (P.rig.s fun _ => i₀) ((top_le_iff_mem _ _ z).2 m₂)
  refine ⟨valF y.left _ (s.f fun _ => i) ^ (N ^ 2) * valF y.left _ (w.s ![i₀, i]).val ^ n /
    (valF (1 : Over.mk b ⟶ G).left _ (w.s ![i₀, i₀]).val *
        valF (X := (𝟙_ (Over S)).left) b _ (P.rig.s fun _ => i₀).val ^ (N ^ 2)) ^ n, hN, hy, w, i₀, i, hw,
    (top_le_iff_mem _ _ z).2 h₀, (top_le_iff_mem _ _ z).2 hi, ?_⟩
  exact div_mul_cancel₀ _ (pow_ne_zero _ (mul_ne_zero n₁ (pow_ne_zero _ n₂)))

theorem alg {R : Type*} [CommRing R] (t t' s : R) (A Y A' Y' r : Rˣ) (M n : ℕ) (hc : A' * A⁻¹ = Y' * Y⁻¹)
    (e : t * (A.val * r.val ^ M) ^ n = s ^ M * Y.val ^ n) (e' : t' * (A'.val * r.val ^ M) ^ n = s ^ M * Y'.val ^ n) :
    t = t' := by
  obtain ⟨c, rfl⟩ : ∃ c : Rˣ, A' = c * A := ⟨A' * A⁻¹, by simp⟩
  obtain rfl : Y' = c * Y := by
    have : c = Y' * Y⁻¹ := by simpa using hc
    rw [this]; simp
  simp only [Units.val_mul] at e'
  have u : IsUnit ((c.val * (A.val * r.val ^ M)) ^ n) := ((c.isUnit.mul A.isUnit).mul (r.isUnit.pow M)).pow n |>.map (RingHom.id R) |> fun h => by
    simpa [_root_.mul_assoc] using h
  apply u.mul_left_injective
  calc t * (c.val * (A.val * r.val ^ M)) ^ n = c.val ^ n * (t * (A.val * r.val ^ M) ^ n) := by rw [mul_pow]; ring
    _ = c.val ^ n * (s ^ M * Y.val ^ n) := by rw [e]
    _ = s ^ M * (c.val * Y.val) ^ n := by rw [mul_pow]; ring
    _ = t' * (c.val * A.val * r.val ^ M) ^ n := e'.symm
    _ = _ := by rw [_root_.mul_assoc]

theorem torsVal_unique (hp : Function.Surjective G.hom.appTop.hom) (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F]
    {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) {N : ℕ} {T T' : F} (hT : TorsVal P s y N T) (hT' : TorsVal P s y N T') : T = T' := by
  have z : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  choose J hJ using fun χ : Sp F ⟶ G.left => exists_chart P.isLB (χ z)
  obtain ⟨w, hw, e⟩ := torsVal_charts P s y N T hT z J hJ
  obtain ⟨w', hw', e'⟩ := torsVal_charts P s y N T' hT' z J hJ
  have hb : (1 : Over.mk b ⟶ G).left ≫ G.hom = y.left ≫ G.hom := (Over.w (1 : Over.mk b ⟶ G)).trans (Over.w y).symm
  have hc := FG.v_const (z := z) (J := J) P.isLB ((mulFG w' hw').mul (mulFG w hw).inv) (fun U _ h => by
    simp only [FG.sum_mul, FG.sum_inv, sum_mulFG, mul_inv_cancel]) G.hom hp hb hJ
  rw [FG.v_mul hJ, FG.v_mul hJ, FG.v_inv, FG.v_inv] at hc
  exact (toStk z).injective (alg _ _ _ _ _ _ _ _ _ _ hc e e')

theorem torsVal_map {P : RigLB G} {n : ℕ} (s : Out.H0 P.L n) {F F' : Type} [Field F] [Field F'] (f : F →+* F') {b : Sp F ⟶ S}
    (y : Over.mk b ⟶ G) (y' : Over.mk (spMap f ≫ b) ⟶ G) (hy' : y'.left = spMap f ≫ y.left) {N : ℕ} {T : F}
    (hT : TorsVal P s y N T) : TorsVal P s y' N (f T) := by
  obtain ⟨hN, hy, w, i₀, i, hw, h₀, hi, hE⟩ := hT
  let g : Over.mk (spMap f ≫ b) ⟶ Over.mk b := Over.homMk (spMap f) rfl
  have ey : y' = g ≫ y := by ext1; exact hy'
  have e₁ : (1 : Over.mk (spMap f ≫ b) ⟶ G).left = spMap f ≫ (1 : Over.mk b ⟶ G).left := by
    rw [one_left, one_left]
    simp
  have z' : Sp F' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F')
  refine ⟨hN, by rw [ey, ← MonObj.comp_pow, hy, MonObj.comp_one], w, i₀, i, hw, ?_, ?_, ?_⟩
  · rw [e₁]
    exact (top_le_iff_mem _ _ z').2 ((top_le_iff_mem _ _ (spMap f z')).1 h₀)
  · rw [hy']
    exact (top_le_iff_mem _ _ z').2 ((top_le_iff_mem _ _ (spMap f z')).1 hi)
  · have := congrArg f hE
    simp only [map_mul, map_pow] at this
    simp only [e₁, hy', valF_spMap]
    exact this

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem appTop_surjective (D : PPData H L) : Function.Surjective D.t.G.hom.appTop.hom := by
  have cart := D.m.cart.1
  have := D.t.semi.smooth
  have := D.tK.semi.smooth
  have hprop : IsProper D.tK.G.hom := D.princ.1
  have hab := GlobalTheory.globalFns_holds _ D.tK.G (AbelianSchemeGerms.isAbelianScheme_of_proper D.tK.G D.tK.semi)
  have hj : Function.Injective (spMap (algebraMap (𝓞 L) L)).appTop :=
    specMap_appTop_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have hinj := GlobalTheory.ProperFunctions.injective_appTop_of_isPullback cart hj
  have comp : ∀ {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : Γ(Z, ⊤)),
      (a ≫ b).appTop.hom x = a.appTop.hom (b.appTop.hom x) := fun a b x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  let e' : Sp (𝓞 L) ⟶ D.t.G.left := eSec D.t.G
  have he : e' ≫ D.t.G.hom = 𝟙 _ := Over.w (η[D.t.G])
  let sK : Sp L ⟶ D.tK.G.left := cart.lift (spMap (algebraMap (𝓞 L) L) ≫ e') (𝟙 _) (by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : sK ≫ D.m.cm.F = spMap (algebraMap (𝓞 L) L) ≫ e' := cart.lift_fst _ _ _
  have h₂ : sK ≫ D.tK.G.hom = 𝟙 _ := cart.lift_snd _ _ _
  intro f
  obtain ⟨c, hc⟩ := hab.2 (D.m.cm.F.appTop.hom f)
  refine ⟨e'.appTop.hom f, hinj ?_⟩
  show D.m.cm.F.appTop.hom (D.t.G.hom.appTop.hom (e'.appTop.hom f)) = D.m.cm.F.appTop.hom f
  rw [← comp, ← comp, cart.w, Category.assoc, ← h₁, comp, comp, ← hc, ← comp sK, h₂]
  simp

theorem torsVal_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (F : Type) [Field F] (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → (∃! T : F, TorsVal D.t.PP s y N T) ∧ ∀ (F' : Type) [Field F'] (f : F →+* F') (y' : Over.mk (spMap f ≫ b) ⟶ D.t.G) (T : F), y'.left = spMap f ≫ y.left → TorsVal D.t.PP s y N T → TorsVal D.t.PP s y' N (f T) := by
  intro E _ _ _ H L _ _ D n s F _ b y N hN hy
  obtain ⟨T, hT⟩ := exists_torsVal D.t.cub D.t.sym s y hN hy
  exact ⟨⟨T, hT, fun T' hT' => torsVal_unique (appTop_surjective D) _ s y hT' hT⟩,
    fun F' _ f y' T e h => torsVal_map s f y y' e h⟩

end GlobalTheory.CompanionTheory.Ar.Sl.TorsExist
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueUniqueBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_value_unique_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (F : Type) [Field F] (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → (∃! T : F, TorsVal D.t.PP s y N T) ∧ ∀ (F' : Type) [Field F'] (f : F →+* F') (y' : Over.mk (spMap f ≫ b) ⟶ D.t.G) (T : F), y'.left = spMap f ≫ y.left → TorsVal D.t.PP s y N T → TorsVal D.t.PP s y' N (f T) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique | exact GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceOfNotMemGenFibre
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

section Local

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {F : Type} [Field F] [NumberField F]


omit [NumberField F] in
theorem int_mem_regAt (hN : NormalCpt ξ) (φ : F →+* Ω) (a : 𝓞 F) (q : Cpt ξ) : φ (a : F) ∈ regAt ξ q :=
  hN q _ ((map_isIntegral_int φ (RingOfIntegers.isIntegral_coe a)).tower_top)

theorem overInt_of_normalCpt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω}
    (ht : CoordTie ℤ ξ fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) (hN : NormalCpt ξ) (φ : F →+* Ω) :
    OverInt y φ := by
  refine ⟨fun k => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := ht.cover ⟨genPt ξ, specializes_rfl⟩
    exact ⟨c k, fun h0 => hc.1 (Finset.prod_eq_zero (Finset.mem_univ k) h0)⟩
  · have hc' : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
    have h1 := (ht.ring c hc' (φ (a : F))).2 fun p _ => int_mem_regAt hN φ a p
    refine Algebra.adjoin_le ?_ h1
    rintro _ ⟨j, rfl⟩
    show (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c k⟩) ∈ chartRingZ y c
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩

theorem cst_mem_regAt_of_genFibre (hN : NormalCpt ξ) (φ : F →+* Ω) {p : Cpt ξ} (hp : p ∈ genFibre ℤ ξ) (a : F) :
    φ a ∈ regAt ξ p := by
  have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hu := hp n hn
  have h1 : φ (n • a) ∈ regAt ξ p := int_mem_regAt hN φ (⟨n • a, hi⟩ : 𝓞 F) p
  have h2 : φ a = (algebraMap ℤ Ω n)⁻¹ * φ (n • a) := by
    rw [zsmul_eq_mul, map_mul, map_intCast, eq_intCast, inv_mul_cancel_left₀]
    simpa using hu.1
  rw [h2]
  exact mul_mem hu.2.2 h1

theorem exists_place_of_notMem_genFibre (hN : NormalCpt ξ) (φ : F →+* Ω) {p : Cpt ξ} (hp : p ∉ genFibre ℤ ξ) :
    ∃ v : HeightOneSpectrum (𝓞 F), ∀ a : F, v.valuation F a ≤ 1 → φ a ∈ regAt ξ p := by
  have := Centre.Sep.isLocalRing_regAt ξ p
  let f : 𝓞 F →+* regAt ξ p :=
    (φ.comp (algebraMap (𝓞 F) F)).codRestrict (regAt ξ p) fun a => int_mem_regAt hN φ a p
  have hf : ∀ a : 𝓞 F, ((f a : regAt ξ p) : Ω) = φ (a : F) := fun _ => rfl
  have hmem : ∀ a : 𝓞 F, a ∈ (IsLocalRing.maximalIdeal (regAt ξ p)).comap f ↔ ¬ unitAt ξ p (φ (a : F)) := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Centre.Sep.isUnit_regAt_iff, hf]
  obtain ⟨o, ho, hu⟩ : ∃ o : ℤ, o ≠ 0 ∧ ¬ unitAt ξ p (algebraMap ℤ Ω o) := by
    by_contra h
    push_neg at h
    exact hp h
  have hne : (IsLocalRing.maximalIdeal (regAt ξ p)).comap f ≠ ⊥ := by
    intro hbot
    have h1 : (o : 𝓞 F) ∈ (IsLocalRing.maximalIdeal (regAt ξ p)).comap f := by
      rw [hmem]
      simpa using hu
    rw [hbot, Ideal.mem_bot] at h1
    exact ho (by exact_mod_cast h1)
  refine ⟨⟨_, inferInstance, hne⟩, fun a ha => ?_⟩
  obtain ⟨n, d, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha
  have hd : unitAt ξ p (φ ((d : 𝓞 F) : F)) := by
    by_contra h
    exact d.2 ((hmem _).2 h)
  have h2 : φ a = φ (n : F) * (φ ((d : 𝓞 F) : F))⁻¹ := by
    have e' : a * ((d : 𝓞 F) : F) = (n : F) := e
    rw [← e', map_mul, mul_inv_cancel_right₀ hd.1]
  rw [h2]
  exact mul_mem (int_mem_regAt hN φ n p) hd.2.2

end Local

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModuleModNBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModuleModNBasis
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.ModFree

open NumberField Module
open scoped nonZeroDivisors TensorProduct

theorem exists_map_of_basis {O B M Mb : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    (S : Submonoid O) (hS : S ≤ O⁰) [IsLocalization S B] [AddCommGroup M] [Module O M]
    [AddCommGroup Mb] [Module O Mb] [Module B Mb] [IsScalarTower O B Mb] (f : M →ₗ[O] Mb)
    [IsLocalizedModule S f] {n : ℕ} (b : Basis (Fin n) B Mb) :
    ∃ φ : (Fin n → O) →ₗ[O] M, Function.Injective φ ∧
      ∀ m, ∃ s : S, ∃ y, (s : O) • m = φ y := by
  choose p hp using fun i => IsLocalizedModule.surj S f (b i)
  have hinj : Function.Injective (algebraMap O B) := IsLocalization.injective B hS
  refine ⟨Fintype.linearCombination O (fun i => (p i).1), ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [Fintype.linearCombination_apply] at hy
    have h1 : ∑ i, algebraMap O B (y i * (p i).2) • b i = 0 := by
      have h := congrArg f hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hp i, Submonoid.smul_def, algebraMap_smul, mul_smul]
    have h2 := Fintype.linearIndependent_iff.mp b.linearIndependent _ h1
    funext i
    have h3 : y i * (p i).2 = 0 := hinj (by rw [h2 i, map_zero])
    exact (mul_eq_zero.mp h3).resolve_right (nonZeroDivisors.ne_zero (hS (p i).2.2))
  · intro x
    have hx := b.sum_repr (f x)
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples S Finset.univ
      (fun i => b.repr (f x) i * ((IsLocalization.map_units B (p i).2).unit⁻¹ : Bˣ))
    choose a ha using fun i => RingHom.mem_rangeS.mp (ht i (Finset.mem_univ i))
    have hc : ∀ i, algebraMap O B (a i) * algebraMap O B (p i).2 =
        algebraMap O B t * b.repr (f x) i := by
      intro i
      rw [ha i, Algebra.smul_def, mul_assoc, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have key : f ((t : O) • x) = f (Fintype.linearCombination O (fun i => (p i).1) a) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, Fintype.linearCombination_apply, map_sum, ← hx, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hp i, Submonoid.smul_def, ← algebraMap_smul B (a i),
        ← algebraMap_smul B ((p i).2 : O), smul_smul, hc i, mul_smul, algebraMap_smul]
    obtain ⟨c, hc'⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) key
    refine ⟨c * t, (c : O) • a, ?_⟩
    rw [map_smul, Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, hc', Submonoid.smul_def]

theorem exists_free_map_mod (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (𝓞 E) M] : Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M →
    ∀ (n N : ℕ), Module.finrank (𝓞 E) M = n → 0 < N →
    ∃ φ : (Fin n → 𝓞 E) →ₗ[𝓞 E] M, (∀ m, ∃ x b, m = φ x + N • b) ∧
      ∀ x b, φ x = N • b → ∃ x', x = N • x' := by
  intro hfin hproj n N hn hN
  set S := GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N with hSdef
  have hS : S ≤ (𝓞 E)⁰ := by
    rintro s ⟨k, hk0, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hk0)
  have : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  have : IsPrincipalIdealRing (Localization S) :=
    GlobalTheory.PlaceInt.LocBasis.isPrincipalIdealRing_loc E N hN hS (Localization S)
  have hrank : Module.finrank (Localization S) (LocalizedModule S M) = n := by
    rw [IsLocalization.finrank_eq (Localization S) S hS,
      IsLocalizedModule.finrank_eq S (LocalizedModule.mkLinearMap S M) hS, hn]
  let b := Module.finBasisOfFinrankEq (Localization S) (LocalizedModule S M) hrank
  obtain ⟨φ, hφ, hsurj⟩ := exists_map_of_basis S hS (LocalizedModule.mkLinearMap S M) b
  have hunit : ∀ s : S, ∃ k : ℕ, (s : 𝓞 E) = k ∧ ∃ u v : ℤ, u * k + v * N = 1 := by
    rintro ⟨_, k, -, hkc, rfl⟩
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hkc
    exact ⟨k, rfl, u, v, huv⟩
  refine ⟨φ, fun m => ?_, fun x c hxc => ?_⟩
  · obtain ⟨s, y, hs⟩ := hsurj m
    obtain ⟨k, hk, u, v, huv⟩ := hunit s
    rw [hk, Nat.cast_smul_eq_nsmul] at hs
    refine ⟨u • y, v • m, ?_⟩
    calc m = ((u * k + v * N : ℤ)) • m := by rw [huv, one_smul]
      _ = u • ((k : ℤ) • m) + (N : ℤ) • (v • m) := by
        rw [add_smul, mul_smul, mul_comm v, mul_smul]
      _ = φ (u • y) + N • (v • m) := by
        rw [map_zsmul, ← hs, natCast_zsmul, natCast_zsmul]
  · obtain ⟨s, y, hs⟩ := hsurj c
    obtain ⟨k, hk, u, v, huv⟩ := hunit s
    rw [hk, Nat.cast_smul_eq_nsmul] at hs
    have hNy : N • y = k • x := by
      apply hφ
      rw [map_nsmul, map_nsmul, ← hs, hxc, smul_comm]
    refine ⟨u • y + v • x, ?_⟩
    calc x = ((u * k + v * N : ℤ)) • x := by rw [huv, one_smul]
      _ = u • ((k : ℤ) • x) + v • ((N : ℤ) • x) := by
        rw [add_smul, mul_smul, mul_smul]
      _ = N • (u • y + v • x) := by
        rw [natCast_zsmul, natCast_zsmul, ← hNy, smul_add, smul_comm u N y, smul_comm v N x]

end GlobalTheory.CompanionTheory.ModFree
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModuleModNBasisStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_module_mod_N_basis : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M], Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M → ∀ (n N : ℕ), Module.finrank (𝓞 E) M = n → 0 < N → ∃ φ : (Fin n → 𝓞 E) →ₗ[𝓞 E] M, (∀ m, ∃ x b, m = φ x + N • b) ∧ ∀ x b, φ x = N • b → ∃ x', x = N • x' := by
  first | exact @GlobalTheory.CompanionTheory.ModFree.exists_free_map_mod | exact GlobalTheory.CompanionTheory.ModFree.exists_free_map_mod | (intros; apply GlobalTheory.CompanionTheory.ModFree.exists_free_map_mod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmIntegersRegularAtComponent
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmIntegersRegularAtComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem integers_mem_regAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : E →+* Z.Ω), (∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)) →
    ∀ (q : Cpt (Z.ξ₀ ≫ Y.j)) (a : 𝓞 E), σ (a : E) ∈ regAt (Z.ξ₀ ≫ Y.j) q := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ σ _ q a
  have hN : NormalCpt (Z.ξ₀ ≫ Y.j) := XR.normalCpt_of_isCptGen Z.gen Y.normal
  exact hN q _ ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)).tower_top)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmIntegersRegularAtComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_integers_regular_at_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : E →+* Z.Ω), (∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)) →
    ∀ (q : Cpt (Z.ξ₀ ≫ Y.j)) (a : 𝓞 E), σ (a : E) ∈ regAt (Z.ξ₀ ≫ Y.j) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalPointSpecializesComponent
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUnique
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUnique
namespace GlobalTheory.CompanionTheory.Ggeo.TwoMaps

open Polynomial

theorem ringHom_eq_of_comp_eq (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B]
    [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B)
    (h : π.comp s = π.comp t) : s = t := by
  refine RingHom.ext fun a => ?_
  have hsep : (minpoly ℚ a).Separable := Algebra.IsSeparable.isSeparable ℚ a
  obtain ⟨p, hp⟩ : ∃ p : K[X], p = (minpoly ℚ a).map (algebraMap ℚ K) := ⟨_, rfl⟩
  have hpa : p.eval a = 0 := by
    rw [hp, eval_map_algebraMap]
    exact minpoly.aeval ℚ a
  have hpd : p.derivative.eval a ≠ 0 := by
    rw [hp, derivative_map, eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ a)
  have hst : p.map s = p.map t := by
    rw [hp, Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hx : (p.map s).eval (s a) = 0 := by
    rw [eval_map, eval₂_at_apply, hpa, map_zero]
  have hy : (p.map s).eval (t a) = 0 := by
    rw [hst, eval_map, eval₂_at_apply, hpa, map_zero]
  have hdx : (p.map s).derivative.eval (s a) = s (p.derivative.eval a) := by
    rw [derivative_map, eval_map, eval₂_at_apply]
  have hunit : IsUnit ((p.map s).derivative.eval (s a)) := by
    rw [hdx]
    exact (IsUnit.mk0 _ hpd).map s
  obtain ⟨k, hk⟩ := binomExpansion (p.map s) (s a) (t a - s a)
  have hd : ¬ IsUnit (t a - s a) := by
    intro hu
    have h0 : π (t a - s a) = 0 := by
      have := RingHom.congr_fun h a
      simp only [RingHom.comp_apply] at this
      rw [map_sub, this, sub_self]
    exact (hu.map π).ne_zero h0
  have hkd : ¬ IsUnit (-(k * (t a - s a))) := by
    rw [IsUnit.neg_iff]
    exact fun hu => hd (isUnit_of_mul_isUnit_right hu)
  have hu2 : IsUnit ((p.map s).derivative.eval (s a) + k * (t a - s a)) := by
    by_contra hc
    have hsum := IsLocalRing.nonunits_add (R := B) (a := (p.map s).derivative.eval (s a) + k * (t a - s a))
      (b := -(k * (t a - s a))) hc hkd
    apply hsum
    simpa using hunit
  have hmul : (t a - s a) * ((p.map s).derivative.eval (s a) + k * (t a - s a)) = 0 := by
    have e : s a + (t a - s a) = t a := by ring
    rw [e, hy, hx] at hk
    linear_combination -hk
  have hz : t a - s a = 0 := by
    simpa using (hu2.mul_left_eq_zero).1 hmul
  exact (sub_eq_zero.1 hz).symm

end GlobalTheory.CompanionTheory.Ggeo.TwoMaps
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUniqueStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_maps_local_ring_unique : ∀ (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B] [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B), π.comp s = π.comp t → s = t := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | exact GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalPointSpecializesComponent
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Coef

section General

variable {X : Scheme.{0}} {K R : Type} [CommRing K] [CommRing R] [IsLocalRing R]

def cst (g : X ⟶ Sp K) (x : X) : K →+* X.presheaf.stalk x :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp g.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem stalkClosedPointTo_germ_top (z : Sp R ⟶ X) (t : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom t) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom t) := by
  have h : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  exact congrArg (fun q => q.hom t) h

theorem val_cst (z : Sp R ⟶ X) (g : X ⟶ Sp K) (φ : K →+* R) (h : z ≫ g = spMap φ) (k : K) :
    (Scheme.stalkClosedPointTo z).hom (cst g (centre z) k) = φ k := by
  show (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom
    (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k))) = φ k
  rw [stalkClosedPointTo_germ_top]
  have h2 : z.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k)) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := by
    have h' : z ≫ g = Spec.map (CommRingCat.ofHom φ) := h
    rw [← h']; simp only [Scheme.Hom.comp_appTop]; rfl
  rw [h2]
  have h3 := congrArg (fun q => q.hom k) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ k) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := h3
  rw [← h3']
  simp

variable {Ω : Type} [Field Ω]

theorem genMap_cst (ξ : Sp Ω ⟶ X) (g : X ⟶ Sp K) (φ : K →+* Ω) (h : ξ ≫ g = spMap φ) (p : Cpt ξ) (k : K) :
    genMap ξ p (cst g p.1 k) = φ k := by
  have h1 : genMap ξ p (cst g p.1 k) = (Scheme.stalkClosedPointTo ξ).hom (cst g (centre ξ) k) :=
    congrArg (Scheme.stalkClosedPointTo ξ).hom
      (X.presheaf.germ_stalkSpecializes_apply (show p.1 ∈ (⊤ : X.Opens) from trivial) p.2 _)
  rw [h1, val_cst ξ g φ h]

theorem exists_lift {ξ : Sp Ω ⟶ X} {F : Type} [Field F] [NumberField F] (hξ : IsCptGen ξ) (hN : NormalCpt ξ)
    (p : Cpt ξ) (inc : F →+* Ω) (hq : ∀ n : ℕ, 0 < n → IsUnit (n : X.presheaf.stalk p.1)) :
    ∃ κ : F →+* X.presheaf.stalk p.1, (genMap ξ p).comp κ = inc := by
  haveI : CharZero Ω := charZero_of_injective_ringHom inc.injective
  have hinv : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n hn
    obtain ⟨u, hu⟩ := hq n hn
    refine ⟨(u⁻¹ : _ˣ), ?_⟩
    have h1 : genMap ξ p u = (n : Ω) := by rw [hu, map_natCast]
    have h2 : genMap ξ p (u⁻¹ : _ˣ) * genMap ξ p u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hmem : ∀ r : ℚ, Rat.castHom Ω r ∈ regAt ξ p := by
    intro r
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
    exact mul_mem (intCast_mem _ _) (hinv r.den r.den_pos)
  let ψ : ℚ →+* regAt ξ p := (Rat.castHom Ω).codRestrict _ hmem
  have hint : ∀ a : F, inc a ∈ regAt ξ p := by
    intro a
    refine hN p _ ⟨(minpoly ℚ a).map ψ, (minpoly.monic (Algebra.IsIntegral.isIntegral a)).map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (regAt ξ p) Ω).comp ψ = inc.comp (algebraMap ℚ F) := Subsingleton.elim _ _
    rw [e, ← Polynomial.hom_eval₂]
    have := minpoly.aeval ℚ a
    rw [Polynomial.aeval_def] at this
    rw [this, map_zero]
  have hb : Function.Bijective (genMap ξ p).rangeRestrict :=
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩
  refine ⟨(RingEquiv.ofBijective _ hb).symm.toRingHom.comp (inc.codRestrict (genMap ξ p).range hint), ?_⟩
  ext a
  exact congrArg Subtype.val ((RingEquiv.ofBijective _ hb).apply_symm_apply (inc.codRestrict (genMap ξ p).range hint a))

end General

theorem exists_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (T : Type) [CommRing T] [IsLocalRing T] (y : Sp T ⟶ Xo.XF c) (c₀ : c.F →+* T), y ≫ pullback.snd _ _ = spMap c₀ → centre y ∈ U → ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))), (genMap (Z.ξ₀ ≫ Y.j) ⟨_, h⟩).comp κ = Z.inc ∧ (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = c₀ := by
  intro E _ _ _ H D l Xo c U O _ β Y Z T _ _ y c₀ hy hU
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have h0 : genPt Z.ξ₀ ⤳ centre y := (Z.closure _).1 hU
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := h0.map Y.j.continuous
  refine ⟨h, ?_⟩
  have hN : NormalCpt (Z.ξ₀ ≫ Y.j) := XR.normalCpt_of_isCptGen Z.gen Y.normal
  have hq : ∀ n : ℕ, 0 < n → IsUnit (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) := by
    intro n hn
    haveI : IsLocalHom (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom := Scheme.isLocalHom_stalkClosedPointTo _
    have e : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) =
        c₀ (n : c.F) := (map_natCast _ n).trans (map_natCast c₀ n).symm
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom _
      ((congrArg IsUnit e).mpr ((IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')).map c₀))
  obtain ⟨κ, hκ⟩ := exists_lift Z.gen hN ⟨centre (y ≫ Y.j), h⟩ Z.inc hq
  refine ⟨κ, hκ, ?_⟩
  let π := genMap Z.ξ₀ ⟨centre y, h0⟩
  let s : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := (Y.j.stalkMap (centre y)).hom.comp κ
  let t : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := cst (pullback.snd _ _) (centre y)
  have hD : GlobalTheory.CompanionTheory.Ar.Dominates Z.ξ₀ (Z.ξ₀ ≫ Y.j) Y.j (RingHom.id Z.Ω) := by
    show Z.ξ₀ ≫ Y.j = Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) ≫ Z.ξ₀ ≫ Y.j
    have e : CommRingCat.ofHom (RingHom.id Z.Ω) = 𝟙 _ := rfl
    rw [e, Spec.map_id, Category.id_comp]
  have hs : π.comp s = Z.inc := by
    ext a
    exact (PullReg.stalkMap_comp_genMap hD ⟨centre y, h0⟩ h (κ a)).trans (congrArg (fun f => f a) hκ)
  have ht : π.comp t = Z.inc := by
    ext a
    exact genMap_cst Z.ξ₀ (pullback.snd _ _) Z.inc Z.over_inc ⟨centre y, h0⟩ a
  have est : s = t := GlobalTheory.T.number_field_maps_local_ring_unique c.F _ Z.Ω π s t (hs.trans ht.symm)
  have e1 : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = (Scheme.stalkClosedPointTo y).hom.comp s := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  rw [e1, est]
  ext a
  exact val_cst y (pullback.snd _ _) c₀ hy a

end GlobalTheory.CompanionTheory.Ar.LocFn.Coef
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalPointSpecializesComponentStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_point_specializes_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (T : Type) [CommRing T] [IsLocalRing T] (y : Sp T ⟶ Xo.XF c) (c₀ : c.F →+* T), y ≫ pullback.snd _ _ = spMap c₀ → centre y ∈ U → ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))), (genMap (Z.ξ₀ ≫ Y.j) ⟨_, h⟩).comp κ = Z.inc ∧ (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = c₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef | exact GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef <;> assumption)
end
end
