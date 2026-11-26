module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialIntegerExponentDegreeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialIntegerExponentDegreeEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
namespace GlobalTheory.FrameHom

open _root_.Formalism.L2.LamCM GlobalTheory.LamT.FieldPoly

theorem prod_zpow_eq_zpow_sum {K ι : Type} [Field K] {a : K} (ha : a ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ ha]

theorem two_zpow_injective {K : Type} [Field K] [CharZero K] {m n : ℤ} (h : (2 : K) ^ m = 2 ^ n) : m = n := by
  have h' : (((2 : ℚ) ^ m : ℚ) : K) = (((2 : ℚ) ^ n : ℚ) : K) := by
    rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]; exact h
  exact (zpow_right_inj₀ (by norm_num : (0 : ℚ) < 2) (by norm_num)).1 (Rat.cast_injective h')

theorem degree_eq_of_scaling_zpow {K σ : Type} [Field K] [CharZero K] (G P : MvPolynomial σ K) (hP : P ≠ 0) (d : ℤ)
    (h : ∀ x : σ → K, MvPolynomial.eval x P ≠ 0 →
      MvPolynomial.eval (fun v => 2 * x v) G = (2 : K) ^ d * MvPolynomial.eval x G)
    (μ : σ →₀ ℕ) (hμ : AddMonoidAlgebra.coeff G μ ≠ 0) : (μ.degree : ℤ) = d := by
  have h1 : P * (MvPolynomial.aeval (fun v => MvPolynomial.C (2 : K) * MvPolynomial.X v : σ → MvPolynomial σ K) G -
      MvPolynomial.C ((2 : K) ^ d) * G) = 0 := by
    apply MvPolynomial.funext
    intro x
    by_cases hx : MvPolynomial.eval x P = 0
    · simp [hx]
    · have e : MvPolynomial.eval x
          (MvPolynomial.aeval (fun v => MvPolynomial.C (2 : K) * MvPolynomial.X v : σ → MvPolynomial σ K) G) =
          MvPolynomial.eval (fun v => 2 * x v) G := by
        clear h hμ
        induction G using MvPolynomial.induction_on with
        | C r => simp
        | add p q hp hq => simp only [map_add (f := _), hp, hq]
        | mul_X p v hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [map_mul, map_sub, e, h x hx]
      simp
  have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hP)
  have h3 := congrArg (AddMonoidAlgebra.coeff · μ) h2
  rw [LamT.FieldPoly.coeff_aeval_scale, MvPolynomial.coeff_C_mul] at h3
  have h4 : (2 : K) ^ μ.degree = 2 ^ d := mul_right_cancel₀ hμ h3
  rw [← zpow_natCast] at h4
  exact two_zpow_injective h4

theorem frPoly_secZ_degree_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    e none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      (∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
      ∀ μ, AddMonoidAlgebra.coeff G μ ≠ 0 →
        (μ.degree : ℤ) = ∑ b, ((Dw.mult b : ℤ) * (k b : ℤ) + ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k _he0 F hF G hG μ hμ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hev : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K,
      evalFr (∏ b, blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← evalFr_blockDetPoly Dw.mult _ Y]
    simp only [evalFr, map_prod]
  have hDp : (∏ b, blockDetPoly K Dw.mult b) ≠ 0 := fun h0 => by
    have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  refine degree_eq_of_scaling_zpow G _ hDp _ (fun x hx => ?_) μ hμ
  let X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K :=
    fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
  let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.diagonal fun _ => 2
  have hX : ∀ b, (X b).det ≠ 0 := fun b => by
    have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact hx
    exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)
  have hTd : ∀ b, (T b).det ≠ 0 := fun b => by simp [T]
  obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
  obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
  rw [Units.val_one] at h₁ h₂
  have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
  simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
  let t : Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some _ => Units.mk0 2 h2
  have hb : FrBor t z₁ z₂ := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z₁ z₂ z₂).1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => ?_, h₂⟩
    · simp [T, Matrix.transpose_apply, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
    · simp [T, t]
  have e₁ := hG z₁ X hX h₁
  have e₂ := hG z₂ (fun b' => X b' * T b')
    (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
  have e₃ := evR_frBor_of_mem_secZ hS Xo c e hF K t z₁ z₂ hb
  have p₁ : ((∏ i, t i ^ e i : Kˣ) : K) = (2 : K) ^ (∑ b, ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
    rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
    simp only [t, one_zpow, Units.val_one, _root_.one_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [← prod_zpow_eq_zpow_sum h2]
    exact Finset.prod_congr rfl fun b _ => prod_zpow_eq_zpow_sum h2 _ _
  have p₂ : (∏ b, (X b * T b).det ^ k b) = (2 : K) ^ (∑ b, (Dw.mult b : ℤ) * (k b : ℤ)) * ∏ b, (X b).det ^ k b := by
    rw [← prod_zpow_eq_zpow_sum h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Matrix.det_mul]
    simp only [T, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show ((Dw.mult b : ℤ) * (k b : ℤ)) = ((Dw.mult b * k b : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
    ring
  have p₃ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G := by
    unfold evalFr
    congr 2
    funext v
    simp [X, T, Matrix.mul_diagonal, mul_comm]
  have p₄ : evalFr G X = MvPolynomial.eval x G := rfl
  rw [← p₃, ← e₂, p₂, e₃, p₁, ← p₄, ← e₁, Finset.sum_add_distrib, zpow_add₀ h2]
  ring

end GlobalTheory.FrameHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialIntegerExponentDegreeEqStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePolynomial_integerExponent_degree_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    e none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      (∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
      ∀ μ, AddMonoidAlgebra.coeff G μ ≠ 0 →
        (μ.degree : ℤ) = ∑ b, ((Dw.mult b : ℤ) * (k b : ℤ) + ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
  first | exact @GlobalTheory.FrameHom.frPoly_secZ_degree_eq | exact GlobalTheory.FrameHom.frPoly_secZ_degree_eq | (intros; apply GlobalTheory.FrameHom.frPoly_secZ_degree_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBijectiveStalkMapOverDvrPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBijectiveStalkMapOverDvrPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS.Modif

theorem exists_bijective_stalkMap_of_dvr : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F)
    (U : Y.Opens) (d : ℕ) (M : Modif p U d), IsProjOver p → (U : Set Y).Nonempty → ∀ y : Y,
      IsDiscreteValuationRing (Y.presheaf.stalk y) →
      ∃ x : M.X, M.σ x = y ∧ Function.Bijective (M.σ.stalkMap x).hom := by
  intro F _ Y _ p U d M hp hU y hR
  have hprop : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → IsProper s := by
    intro Z s hs
    obtain ⟨N, c, hc, rfl⟩ := hs
    have := isProper_str F N
    infer_instance
  haveI : IsProper p := hprop hp
  haveI : IsProper (M.σ ≫ p) := hprop M.proj
  haveI : IsProper M.σ := IsProper.of_comp M.σ p
  haveI : Nonempty M.X := by
    haveI := M.iso
    obtain ⟨u, hu⟩ := hU
    obtain ⟨z, -⟩ := (M.σ ∣_ U).surjective ⟨u, hu⟩
    exact ⟨z.1⟩
  haveI : IsIntegral M.X := HSApp.ValCrit.isIntegral_X M
  let R := Y.presheaf.stalk y
  haveI : IsDomain R := inferInstanceAs (IsDomain (Y.presheaf.stalk y))
  haveI : IsDiscreteValuationRing R := hR
  let η := genericPoint Y
  have hηU : η ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  let i₂ : Spec R ⟶ Y := Y.fromSpecStalk y

  have hgen : ∀ w : Spec R, (∀ u, w ⤳ u) → i₂ w = η := by
    intro w hw
    have hq : η ∈ Set.range i₂ := by
      rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec Y).specializes (Set.mem_univ y)
    obtain ⟨q, hq⟩ := hq
    have h1 : i₂ w ⤳ η := hq ▸ (hw q).map i₂.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  let K := FractionRing R
  let j : Spec (.of K) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hj : ∀ s : Spec (.of K), ∀ u : Spec R, j s ⤳ u := by
    intro s u
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    change Ideal.comap (algebraMap R K) s.asIdeal ≤ u.asIdeal
    haveI : s.asIdeal.IsPrime := s.isPrime
    rw [Ideal.eq_bot_of_prime s.asIdeal, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  have hKU : ⊤ ≤ (j ≫ i₂) ⁻¹ᵁ U := fun s _ => by
    show i₂ (j s) ∈ U
    rw [hgen (j s) (hj s)]
    exact hηU
  obtain ⟨i₁, hi₁, -⟩ := M.existsUnique_lift (j ≫ i₂) hKU
  have hE : ValuativeCriterion.Existence M.σ := by
    have h : UniversallyClosed M.σ := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨L⟩⟩ := hE (@ValuativeCommSq.mk _ _ M.σ R inferInstance ‹IsDomain R› inferInstance K inferInstance
    inferInstance inferInstance i₁ i₂ ⟨hi₁⟩)
  let c := IsLocalRing.closedPoint R
  have hfr : L.l ≫ M.σ = i₂ := L.fac_right
  refine ⟨L.l c, ?_, ?_⟩
  · show (L.l ≫ M.σ) c = y
    rw [hfr]
    exact Scheme.fromSpecStalk_closedPoint

  have key : ∀ g : Spec R ⟶ Y, g = i₂ → Function.Bijective (g.stalkMap c).hom := by
    rintro _ rfl
    have e : i₂.stalkMap c ≫ (stalkClosedPointIso R).hom = (Y.presheaf.stalkCongr _).hom :=
      Scheme.stalkClosedPointTo_fromSpecStalk y
    haveI : IsIso (i₂.stalkMap c ≫ (stalkClosedPointIso R).hom) := by rw [e]; infer_instance
    haveI : IsIso (i₂.stalkMap c) := IsIso.of_isIso_comp_right _ (stalkClosedPointIso R).hom
    exact ConcreteCategory.bijective_of_isIso _
  have hb := key _ hfr
  have e₀ := Scheme.Hom.stalkMap_comp L.l M.σ c
  have hb2 : Function.Bijective (M.σ.stalkMap (L.l c) ≫ L.l.stalkMap c).hom := by rw [← e₀]; exact hb
  replace hb : Function.Bijective ((L.l.stalkMap c).hom ∘ (M.σ.stalkMap (L.l c)).hom) := hb2

  let t := genericPoint (Spec R)
  have ht : ∀ u : Spec R, t ⤳ u := fun u => (genericPoint_spec (Spec R)).specializes (Set.mem_univ u)
  have hσt : M.σ (L.l t) = η := by
    show (L.l ≫ M.σ) t = η
    rw [hfr]; exact hgen t ht
  have hσg : M.σ (genericPoint M.X) = η := by
    have h1 : M.σ (genericPoint M.X) ⤳ η :=
      hσt ▸ ((genericPoint_spec M.X).specializes (Set.mem_univ (L.l t))).map M.σ.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hlt : L.l t = genericPoint M.X := by
    haveI := M.iso
    have m1 : L.l t ∈ M.opn := show M.σ (L.l t) ∈ U from hσt ▸ hηU
    have m2 : genericPoint M.X ∈ M.opn := show M.σ (genericPoint M.X) ∈ U from hσg ▸ hηU
    have e : (M.σ ∣_ U) ⟨L.l t, m1⟩ = (M.σ ∣_ U) ⟨genericPoint M.X, m2⟩ :=
      Subtype.ext ((morphismRestrict_base_coe M.σ U ⟨L.l t, m1⟩).trans
        ((hσt.trans hσg.symm).trans (morphismRestrict_base_coe M.σ U ⟨genericPoint M.X, m2⟩).symm))
    exact congrArg Subtype.val ((M.σ ∣_ U).isOpenEmbedding.injective e)

  have hBinj : Function.Injective (L.l.stalkMap c).hom := by
    have hsp : t ⤳ c := ht c
    have nat := Scheme.Hom.stalkSpecializes_stalkMap L.l t c hsp
    have hf : IsField (M.X.presheaf.stalk (L.l t)) := by
      rw [hlt]; exact Field.toIsField M.X.functionField
    have i1 : Function.Injective (L.l.stalkMap t).hom := by
      letI := hf.toField
      exact RingHom.injective _
    have i2 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous)).hom := by
      refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      obtain ⟨V, hV, f, rfl⟩ := M.X.presheaf.germ_exist a
      have e := congrArg (fun φ => φ.hom f) (M.X.presheaf.germ_stalkSpecializes hV (hsp.map L.l.continuous))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
      rw [e] at ha
      rw [germ_injective_of_isIntegral M.X _ _ (ha.trans (map_zero _).symm), map_zero]
    have i3 : Function.Injective (((Spec R).presheaf.stalkSpecializes hsp).hom ∘ (L.l.stalkMap c).hom) := by
      have h4 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous) ≫ L.l.stalkMap t).hom :=
        i1.comp i2
      rw [nat] at h4
      exact h4
    exact i3.of_comp
  refine ⟨hb.1.of_comp, fun a => ?_⟩
  obtain ⟨b, hb'⟩ := hb.2 ((L.l.stalkMap c).hom a)
  exact ⟨b, hBinj hb'⟩

end GlobalTheory.CompHS.Modif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBijectiveStalkMapOverDvrPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bijective_stalkMap_over_dvrPoint : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), IsProjOver p → (U : Set Y).Nonempty → ∀ y : Y, IsDiscreteValuationRing (Y.presheaf.stalk y) →
      ∃ x : M.X, M.σ x = y ∧ Function.Bijective (M.σ.stalkMap x).hom := by
  first | exact @GlobalTheory.CompHS.Modif.exists_bijective_stalkMap_of_dvr | exact GlobalTheory.CompHS.Modif.exists_bijective_stalkMap_of_dvr | (intros; apply GlobalTheory.CompHS.Modif.exists_bijective_stalkMap_of_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomologyWedgeCoordinateNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomologyWedgeCoordinateNonzero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.WedgeCoord

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

def hl (w : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun z := herm Hm z w
  map_add' x y := by simp [herm, add_dotProduct]
  map_smul' c x := by simp [herm, smul_dotProduct]

theorem hl_apply (w z : Fin g → ℂ) : hl Hm w z = herm Hm z w := rfl

theorem herm_add_right (z w w' : Fin g → ℂ) : herm Hm z (w + w') = herm Hm z w + herm Hm z w' := by
  simp [herm, Matrix.mulVec_add, dotProduct_add]

theorem herm_smul_right (z w : Fin g → ℂ) (c : ℂ) : herm Hm z (c • w) = star c * herm Hm z w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

theorem herm_zero_right (z : Fin g → ℂ) : herm Hm z 0 = 0 := by
  simp [herm]

theorem herm_eq_zero_of_mem_span {s : Set (Fin g → ℂ)} {z w : Fin g → ℂ}
    (h : ∀ v ∈ s, herm Hm z v = 0) (hw : w ∈ Submodule.span ℂ s) : herm Hm z w = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact herm_zero_right Hm z
  | add x y _ _ hx hy => rw [herm_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [herm_smul_right, hx, mul_zero]

theorem herm_symm (hH : Hm.IsHermitian) (z w : Fin g → ℂ) : herm Hm z w = star (herm Hm w z) := by
  unfold herm
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq,
    Matrix.dotProduct_mulVec]

theorem gram_surj (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) {n : Type} [Fintype n]
    (V : n → Fin g → ℂ) (hV : LinearIndependent ℂ V) (c : n → ℂ) :
    ∃ a : n → ℂ, ∀ i, herm Hm (∑ m, a m • V m) (V i) = c i := by
  classical
  let T : (n → ℂ) →ₗ[ℂ] (n → ℂ) :=
    (LinearMap.pi fun i => hl Hm (V i)) ∘ₗ Fintype.linearCombination ℂ V
  have hT : ∀ a i, T a i = herm Hm (∑ m, a m • V m) (V i) := fun a i => rfl
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h0 : ∑ m, a m • V m = 0 := by
      by_contra hne
      have h1 := hpos _ hne
      have h2 : herm Hm (∑ m, a m • V m) (∑ m, a m • V m) = 0 := by
        refine herm_eq_zero_of_mem_span Hm (s := Set.range V) ?_ ?_
        · rintro _ ⟨i, rfl⟩
          rw [← hT, ha]; rfl
        · exact Submodule.sum_mem _ fun m _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      rw [h2] at h1
      simp at h1
    funext i
    exact Fintype.linearIndependent_iff.1 hV a h0 i
  obtain ⟨a, ha⟩ := LinearMap.surjective_of_injective hinj c
  exact ⟨a, fun i => by rw [← hT, ha]⟩

theorem exists_proj (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) {p : ℕ}
    (V : Fin p → Fin g → ℂ) (y : Fin g → ℂ) :
    ∃ a : Fin p → ℂ, ∀ i, herm Hm (y - ∑ m, a m • V m) (V i) = 0 := by
  classical
  obtain ⟨s, hsV, hspan, hli⟩ := exists_linearIndependent ℂ (Set.range V)
  have hfin : s.Finite := (Set.finite_range V).subset hsV
  haveI := hfin.fintype
  obtain ⟨c, hc⟩ := gram_surj Hm hpos (fun v : s => (v : Fin g → ℂ)) hli (fun v => herm Hm y v)
  have hmem : ∑ m : s, c m • (m : Fin g → ℂ) ∈ Submodule.span ℂ (Set.range V) :=
    Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span (hsV m.2))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨a, fun i => ?_⟩
  rw [ha]
  refine herm_eq_zero_of_mem_span Hm (s := s) ?_ ?_
  · intro v hv
    rw [← hl_apply, map_sub, hl_apply, hl_apply, hc ⟨v, hv⟩, sub_self]
  · rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩

end GlobalTheory.DetLine.WedgeCoord

open GlobalTheory.DetLine.WedgeCoord in
theorem GlobalTheory.DetLine.exists_wedgeCoord : ∀ (g p q : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) → (∀ x, ∃ Δ, IsWedgeCoord Hm V W x Δ) ∧ (LinearIndependent ℂ V → LinearIndependent ℂ W → ∃ x Δ, Δ ≠ 0 ∧ IsWedgeCoord Hm V W x Δ) := by
  intro g p q Hm V W hH hpos
  refine ⟨fun x => ?_, fun hV hW => ?_⟩
  · choose a ha using fun k => exists_proj Hm hpos V (x k)
    exact ⟨_, a, ha, rfl⟩
  · classical
    let P : Type := {z : (Fin g → ℂ) × (Fin p → ℂ) //
      ∀ i, herm Hm (z.1 - ∑ m, z.2 m • V m) (V i) = 0}
    let r : P → (Fin q ⊕ Fin p → ℂ) := fun z =>
      Sum.elim (fun j => -(Real.pi : ℂ) * herm Hm (W j) z.1.1) (fun i => z.1.2 i)
    have key : ∀ z : P, Sum.elim (fun j => -(Real.pi : ℂ) * herm Hm (W j) z.1.1) (0 : Fin p → ℂ) ∈
        Submodule.span ℂ (Set.range r) ∧
        Sum.elim (0 : Fin q → ℂ) z.1.2 ∈ Submodule.span ℂ (Set.range r) := by
      intro z
      let z' : P := ⟨(Complex.I • z.1.1, Complex.I • z.1.2), fun i => by
        have : Complex.I • z.1.1 - ∑ m, (Complex.I • z.1.2) m • V m =
            Complex.I • (z.1.1 - ∑ m, z.1.2 m • V m) := by
          simp only [smul_sub, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, mul_smul]
        show herm Hm (Complex.I • z.1.1 - ∑ m, (Complex.I • z.1.2) m • V m) (V i) = 0
        rw [this, ← hl_apply, map_smul, hl_apply, z.2 i, smul_zero]⟩
      have h1 : r z ∈ Submodule.span ℂ (Set.range r) := Submodule.subset_span ⟨z, rfl⟩
      have h2 : r z' ∈ Submodule.span ℂ (Set.range r) := Submodule.subset_span ⟨z', rfl⟩
      have hI := Complex.I_mul_I
      constructor
      · convert Submodule.smul_mem _ (1/2 : ℂ) (Submodule.add_mem _ h1
          (Submodule.smul_mem _ Complex.I h2)) using 1
        funext k
        rcases k with j | i
        · simp only [r, z', Sum.elim_inl, Pi.smul_apply, Pi.add_apply, smul_eq_mul, herm_smul_right,
            Complex.star_def, Complex.conj_I]
          linear_combination (-(1/2) * (Real.pi : ℂ) * herm Hm (W j) z.1.1) * hI
        · simp only [r, z', Sum.elim_inr, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply]
          linear_combination (-(1/2) * z.1.2 i) * hI
      · convert Submodule.smul_mem _ (1/2 : ℂ) (Submodule.sub_mem _ h1
          (Submodule.smul_mem _ Complex.I h2)) using 1
        funext k
        rcases k with j | i
        · simp only [r, z', Sum.elim_inl, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, herm_smul_right,
            Complex.star_def, Complex.conj_I, Pi.zero_apply]
          linear_combination ((1/2) * (Real.pi : ℂ) * herm Hm (W j) z.1.1) * hI
        · simp only [r, z', Sum.elim_inr, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          linear_combination ((1/2) * z.1.2 i) * hI
    have hspan : Submodule.span ℂ (Set.range r) = ⊤ := by
      rw [eq_top_iff]
      intro u _
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      obtain ⟨c, hc⟩ := gram_surj Hm hpos W hW (fun j => star (u (Sum.inl j) / (-(Real.pi : ℂ))))
      obtain ⟨a, ha⟩ := exists_proj Hm hpos V (∑ m, c m • W m)
      have h1 := (key ⟨(∑ m, c m • W m, a), ha⟩).1
      have h2 := (key ⟨(∑ m, u (Sum.inr m) • V m, fun m => u (Sum.inr m)), fun i => by
        simp [herm]⟩).2
      convert Submodule.add_mem _ h1 h2 using 1
      funext k
      rcases k with j | i
      · simp only [Sum.elim_inl, Pi.add_apply, Pi.zero_apply, add_zero]
        rw [herm_symm Hm hH, hc, star_star]
        field_simp
      · simp
    by_contra hcon
    push_neg at hcon
    have hz : (Matrix.detRowAlternating (n := Fin q ⊕ Fin p) (R := ℂ)).toMultilinearMap = 0 := by
      refine MultilinearMap.ext_of_span_eq_top (g := fun _ => r) (fun _ => hspan) fun s => ?_
      by_contra hne
      exact hcon (fun k => (s k).1.1) _ hne ⟨fun k => (s k).1.2, fun k => (s k).2, rfl⟩
    have := congrArg (fun f => f (1 : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ)) hz
    have h1 : Matrix.det (1 : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) = 0 := this
    simp at h1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomologyWedgeCoordinateNonzeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homologyWedgeCoordinate_nonzero : ∀ (g p q : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) → (∀ x, ∃ Δ, IsWedgeCoord Hm V W x Δ) ∧ (LinearIndependent ℂ V → LinearIndependent ℂ W → ∃ x Δ, Δ ≠ 0 ∧ IsWedgeCoord Hm V W x Δ) := by
  first | exact @GlobalTheory.DetLine.exists_wedgeCoord | exact GlobalTheory.DetLine.exists_wedgeCoord | (intros; apply GlobalTheory.DetLine.exists_wedgeCoord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.SymFrame
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem const_of_periodic {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef)
    {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (hper : ∀ z M N, f (z + perV τ M N) = f z) (z w : Fin g → ℂ) :
    f z = f w := by
  let P : (Fin g → ℤ) × (Fin g → ℤ) →+ (Fin g → ℂ) := AddMonoidHom.mk' (fun a => perV τ a.1 a.2) fun a b => by
    have e : ∀ M N : Fin g → ℤ, cv (M + N) = cv M + cv N := fun M N => by ext i; simp [cv]
    simp only [perV, Prod.fst_add, Prod.snd_add, e, Matrix.mulVec_add]
    abel
  refine periodic_const_range P (eq_top_iff.2 fun v _ => ?_) f hf (fun z a => hper z a.1 a.2) z w
  obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hp.isUnit fun i => (v i).im
  let x : Fin g → ℝ := fun i => (v i).re - (τ.map Complex.re *ᵥ y) i
  have e : v = ∑ i, x i • P (Pi.single i 1, 0) + ∑ i, y i • P (0, Pi.single i 1) := by
    have c0 : cv (0 : Fin g → ℤ) = 0 := by ext i; simp [cv]
    have c1 : ∀ i : Fin g, cv (Pi.single i 1 : Fin g → ℤ) = Pi.single i 1 := fun i => by
      ext k; by_cases h : k = i <;> simp [cv, h, Pi.single_apply]
    ext k
    have hk := congrFun hy k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hk
    simp only [P, AddMonoidHom.mk'_apply, perV, c0, c1, Matrix.mulVec_zero, add_zero, zero_add, Matrix.mulVec_single_one,
      Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    apply Complex.ext
    · simp [x, Matrix.mulVec, dotProduct, mul_comm]
    · simp [← hk, mul_comm]
  rw [e]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem autV_mul_autV {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) {a b : Fin g → ℂ} (ha : Half a) (hb : Half b)
    (M N : Fin g → ℤ) (z : Fin g → ℂ) : autV τ a b M N z * autV τ a b M N (-(z + perV τ M N)) = 1 := by
  have h : ∀ {c : Fin g → ℂ}, Half c → ∀ M : Fin g → ℤ, ∃ n : ℤ, 2 * (c ⬝ᵥ cv M) = n := fun {c} hc M => by
    classical
    refine ⟨∑ i, if c i = 0 then 0 else M i, ?_⟩
    rw [dotProduct, Finset.mul_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hc i with e | e <;> simp [e, cv]
  obtain ⟨m, hm⟩ := h ha M
  obtain ⟨n, hn⟩ := h hb N
  have hk : cv N ⬝ᵥ cv M = ((N ⬝ᵥ M : ℤ) : ℂ) := by simp [dotProduct, cv]
  rw [autV, autV, ← Complex.exp_add, Complex.exp_eq_one_iff]
  refine ⟨m - n + N ⬝ᵥ M, ?_⟩
  rw [dotProduct_neg, dotProduct_add, perV, dotProduct_add, hk]
  push_cast
  rw [← hm, ← hn]
  ring

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
  {ν : NumOf D ℂ N} {d : AB N.toNumB g}

theorem hol_base (G : Geo ν d) (U : D.P.A.left.Opens) (f : Γ(D.P.A.left, U)ˣ) :
    IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ν.eA (d.ex z)).left U f.val) {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ U} := by
  have e : ∀ z, ptB ν d z ≫ (snd (TF (R := R) ℂ) D.P.A).left = (ν.eA (d.ex z)).left := fun z => by
    rw [ptB, ← Over.comp_left, lift_snd]
  have h := G.hol ((snd (TF (R := R) ℂ) D.P.A).left ⁻¹ᵁ U) (pullU _ U f).val
  simp only [← e]
  refine ⟨h.1, h.2.congr fun z _ => ?_⟩
  exact (vtf_val_pullU (ptB ν d z) _ U f).symm

theorem differentiable_gen (G : Geo ν d) (hr : ν.rg ≠ 0) {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (ht : t.IsGen) (w : K → (Fin g → ℂ) → (Fin g → ℂ))
    (hw : ∀ k, Differentiable ℂ (w k)) (hφ : ∀ k z, (ν.eA (d.ex z)).left ≫ φ k = (ν.eA (d.ex (w k z))).left) :
    Differentiable ℂ fun z => vF t (ν.eA (d.ex z)).left ν.J / ∏ k, ((d.fr (w k z) : ℂ) * ν.rg) ^ ε k := by
  intro z₀
  let j : K → D.P.L.ι := fun k => ν.J ((ν.eA (d.ex z₀)).left ≫ φ k)
  obtain ⟨hS, hv⟩ := hol_base G (LB.wchart D.P.L φ j) (t.s j)
  have hJ : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((ν.eA (d.ex z)).left ≫ φ k) :=
    fun z q _ => Set.mem_iInter.2 fun k => ν.good ((ν.eA (d.ex z)).left ≫ φ k) (x := q) trivial
  have hk : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ j → ∀ k,
      ⊤ ≤ (ν.eA (d.ex (w k z))).left ⁻¹ᵁ D.P.L.U (j k) := fun z hz k q _ => by
    rw [← hφ]
    exact Set.mem_iInter.1 (hz (x := q) trivial) k
  have hfr : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ j → ∀ k, (d.fr (w k z) : ℂ) * ν.rg =
      valF ((ν.eA (d.ex z)).left ≫ φ k) _ (D.P.L.g (ν.J ((ν.eA (d.ex z)).left ≫ φ k)) (j k)).val * G.frG (j k) (w k z) :=
    fun z hz k => by
      rw [hφ, G.fr_eq]
      exact G.fr_compat _ _ _ fun q _ => ⟨ν.good _ (x := q) trivial, hk z hz k (x := q) trivial⟩
  have hne : ∀ k z, (d.fr (w k z) : ℂ) * ν.rg ≠ 0 := fun k z => mul_ne_zero (Units.ne_zero _) hr
  have hev : (fun z => vF t (ν.eA (d.ex z)).left ν.J / ∏ k, ((d.fr (w k z) : ℂ) * ν.rg) ^ ε k) =ᶠ[nhds z₀]
      fun z => valF (ν.eA (d.ex z)).left (LB.wchart D.P.L φ j) (t.s j).val / ∏ k, G.frG (j k) (w k z) ^ ε k := by
    filter_upwards [hS.mem_nhds (hJ z₀)] with z hz
    have e : vF t (ν.eA (d.ex z)).left ν.J = (∏ k, valF ((ν.eA (d.ex z)).left ≫ φ k) _
        (D.P.L.g (ν.J ((ν.eA (d.ex z)).left ≫ φ k)) (j k)).val ^ ε k) *
        valF (ν.eA (d.ex z)).left (LB.wchart D.P.L φ j) (t.s j).val :=
      vtf_isGen_val D.P.L φ ε t ht _ _ j fun q _ => ⟨hJ z (x := q) trivial, hz (x := q) trivial⟩
    rw [e]
    simp only [hfr z hz, mul_zpow, Finset.prod_mul_distrib]
    refine mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_)
    exact left_ne_zero_of_mul (hfr z hz k ▸ hne k z)
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have h0 : ∀ k, G.frG (j k) (w k z₀) ≠ 0 := fun k => right_ne_zero_of_mul (hfr z₀ (hJ z₀) k ▸ hne k z₀)
  have h1 : ∀ k, DifferentiableAt ℂ (fun z => G.frG (j k) (w k z)) z₀ := fun k =>
    ((G.fr_hol (j k)).differentiableAt ((hol_base G _ 1).1.mem_nhds (hk z₀ (hJ z₀) k))).comp z₀ (hw k z₀)
  have h2 : DifferentiableAt ℂ (fun z => ∏ k, G.frG (j k) (w k z) ^ ε k) z₀ :=
    by
      have hp : ∀ s : Finset K, DifferentiableAt ℂ (fun z => ∏ k ∈ s, G.frG (j k) (w k z) ^ ε k) z₀ := fun s => by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          simp only [Finset.prod_insert ha]
          exact ((h1 a).zpow (Or.inl (h0 a))).mul ih
      exact hp _
  simp only [div_eq_mul_inv]
  exact (hv.differentiableAt (hS.mem_nhds (hJ z₀))).mul
    (h2.inv (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h0 k)))

theorem rg_ne (ν : NumOf D ℂ N) : ν.rg ≠ 0 := by
  unfold NumOf.rg vF valF
  split_ifs with h
  · exact (((Units.isUnit _).map _).map _).ne_zero
  · exact (h fun q _ => Set.mem_iInter.2 fun _ => ν.good ((TF (R := R) ℂ).hom ≫ eSec D.P.A) (x := q) trivial).elim

end GlobalTheory.MBLow.Cl.SymFrame

namespace GlobalTheory.MBLow.Cl
open SymFrame

theorem sym_of_geo : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → d.Sym := by
  rintro R _ _ _ _ D - - _ N ν g d ⟨G⟩
  have hr := rg_ne ν
  have h0 : d.ex 0 = 1 := by simpa using d.ex_add 0 0
  have hneg : ∀ z, d.ex (-z) = (d.ex z)⁻¹ := fun z =>
    eq_inv_of_mul_eq_one_left (by rw [← d.ex_add, neg_add_cancel, h0])
  have hd := differentiable_gen G hr D.sym D.sym_gen ![fun z => -z, fun z => z]
    (fun k => by fin_cases k <;> simp <;> fun_prop) (fun k z => by
      fin_cases k
      · change _ ≫ (ι[D.P.A]).left = (ν.eA (d.ex (-z))).left
        rw [hneg, map_inv, Hom.inv_def, Over.comp_left]
      · exact Category.comp_id _)
  have hF : Differentiable ℂ fun z => (N.σ (d.ex z) : ℂ) * d.fr z / d.fr (-z) := by
    convert hd using 2 with z
    rw [ν.σ_eq, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, _root_.zpow_neg]
    have := (d.fr z).ne_zero
    have := (d.fr (-z)).ne_zero
    field_simp
  intro x
  have hc := const_of_periodic d.pos hF (fun z M M' => by
    have h1 := d.fr_per M M' z
    have h2 := d.fr_per M M' (-(z + perV d.τ M M'))
    have h3 := autV_mul_autV d.τ d.ha d.hb M M' z
    rw [show -(z + perV d.τ M M') + perV d.τ M M' = -z by abel] at h2
    rw [d.ex_add, (d.ker _).2 ⟨M, M', rfl⟩, _root_.mul_one, div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), h1, h2]
    linear_combination (-(N.σ (d.ex z) : ℂ) * d.fr (z + perV d.τ M M') * d.fr (-z)) * h3) x 0
  rw [h0, N.σ_one, neg_zero, d.fr_zero, div_eq_iff (Units.ne_zero _)] at hc
  ext
  simpa using hc

end GlobalTheory.MBLow.Cl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulEqSumVecMulVecSpanningFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulEqSumVecMulVecSpanningFamily
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
open Matrix

noncomputable section

namespace GlobalTheory.Poinc.SumSq

theorem exists_nat_smul_sub_posDef {ι : Type*} [Fintype ι] {G B : Matrix ι ι ℝ} (hG : G.PosDef)
    (hB : B.IsHermitian) : ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((κ : ℝ) • G - B).PosDef := by
  have hp : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ G *ᵥ x := fun x hx => by
    simpa using hG.dotProduct_mulVec_pos hx
  have hne : ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  have hc : ContinuousOn (fun x : ι → ℝ => (x ⬝ᵥ B *ᵥ x) / (x ⬝ᵥ G *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_)
      fun x hx => (hp x (hne x hx)).ne'
    · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  obtain ⟨C, hC⟩ := ((isCompact_sphere (0 : ι → ℝ) 1).image_of_continuousOn hc).bddAbove
  obtain ⟨κ₀, hκ₀⟩ := exists_nat_gt C
  refine ⟨κ₀, fun κ hκ => ?_⟩
  have hκ' : C < κ := hκ₀.trans_le (by exact_mod_cast hκ)
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · refine IsHermitian.sub ?_ hB
    rw [IsHermitian, conjTranspose_smul, hG.isHermitian.eq, star_trivial]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      simp [norm_smul, hn.ne']
    have h1 := hC ⟨_, hs, rfl⟩
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
    rw [mul_div_mul_left _ _ (inv_pos.2 hn).ne', mul_div_mul_left _ _ (inv_pos.2 hn).ne',
      div_le_iff₀ (hp x hx)] at h1
    have h2 := mul_lt_mul_of_pos_right hκ' (hp x hx)
    rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linarith

theorem posDef_symm {n : Type*} {M : Matrix n n ℝ} (hM : M.PosDef) (i j : n) : M j i = M i j := by
  have := congrFun₂ hM.isHermitian.eq i j
  simpa using this

theorem schur_posDef {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hM : M.PosDef) :
    (Matrix.of fun i j : Fin n => M 0 0 * M i.succ j.succ - M i.succ 0 * M 0 j.succ).PosDef := by
  have hs := posDef_symm hM
  have ha : 0 < M 0 0 := hM.diag_pos
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun y hy => ?_
  · ext i j
    simp [hs]
    ring
  · set B := ∑ j, M 0 j.succ * y j with hB
    set x : Fin (n + 1) → ℝ := Fin.cons (-B / M 0 0) y with hx
    have hx0 : x ≠ 0 := by
      intro h
      apply hy
      funext j
      have := congrFun h j.succ
      simpa [hx] using this
    have h1 := hM.dotProduct_mulVec_pos hx0
    rw [star_trivial] at h1 ⊢
    have e1 : x ⬝ᵥ M *ᵥ x = M 0 0 * (-B / M 0 0) ^ 2 + 2 * (-B / M 0 0) * B +
        ∑ i, y i * ∑ j, M i.succ j.succ * y j := by
      have hc : ∀ i : Fin n, M i.succ 0 = M 0 i.succ := fun i => hs 0 i.succ
      have h3 : ∑ i, y i * (M 0 i.succ * (-B / M 0 0)) = (-B / M 0 0) * B := by
        rw [hB, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [dotProduct, mulVec, Fin.sum_univ_succ, hx, Fin.cons_zero, Fin.cons_succ, hc,
        mul_add, Finset.sum_add_distrib, h3]
      rw [← hB]
      ring
    have e2 : y ⬝ᵥ (Matrix.of fun i j : Fin n => M 0 0 * M i.succ j.succ - M i.succ 0 * M 0 j.succ) *ᵥ y =
        M 0 0 * ∑ i, y i * ∑ j, M i.succ j.succ * y j - B ^ 2 := by
      have hc : ∀ i : Fin n, M i.succ 0 = M 0 i.succ := fun i => hs 0 i.succ
      simp only [dotProduct, mulVec, of_apply, hc, sub_mul, Finset.sum_sub_distrib, mul_sub]
      rw [hB, sq, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    rw [e1] at h1
    field_simp at h1
    nlinarith

theorem exists_smul_eq_sum_vecMulVec : ∀ (r : ℕ) (L : Matrix (Fin r) (Fin r) ℤ),
    (L.map (Int.cast : ℤ → ℝ)).PosDef → ∃ (ι : Type) (_ : Fintype ι) (D : ℕ) (a : ι → Fin r → ℤ),
      1 ≤ D ∧ (D : ℤ) • L = ∑ i, vecMulVec (a i) (a i) := by
  intro r
  induction r with
  | zero =>
    intro L _
    refine ⟨Empty, inferInstance, 1, Empty.elim, le_rfl, ?_⟩
    ext i
    exact i.elim0
  | succ n ih =>
    intro L hL
    have hs := posDef_symm hL
    have hsz : ∀ i j, L j i = L i j := fun i j => by
      have := hs i j
      simp only [Matrix.map_apply] at this
      exact_mod_cast this
    have ha : (0 : ℝ) < (L 0 0 : ℝ) := by simpa using (hL.diag_pos (i := 0))
    have ha' : 0 < L 0 0 := by exact_mod_cast ha
    set S : Matrix (Fin n) (Fin n) ℤ :=
      Matrix.of fun i j => L 0 0 * L i.succ j.succ - L i.succ 0 * L 0 j.succ with hS
    have hSr : (S.map (Int.cast : ℤ → ℝ)).PosDef := by
      have := schur_posDef hL
      convert this using 1
      ext i j
      simp [hS]
    obtain ⟨ι, _, D, y, hD, hy⟩ := ih S hSr
    refine ⟨Fin D ⊕ ι, inferInstance, D * (L 0 0).toNat,
      Sum.elim (fun _ => fun j => L 0 j) (fun i => Fin.cons 0 (y i)), ?_, ?_⟩
    · have : 1 ≤ (L 0 0).toNat := by omega
      nlinarith
    · have hy' : ∀ p q, (D : ℤ) * (L 0 0 * L p.succ q.succ - L p.succ 0 * L 0 q.succ) =
          ∑ i, y i p * y i q := fun p q => by
        have := congrFun₂ hy p q
        simpa [hS, Matrix.sum_apply, vecMulVec_apply] using this
      have hc : ((L 0 0).toNat : ℤ) = L 0 0 := Int.toNat_of_nonneg ha'.le
      ext p q
      simp only [Matrix.smul_apply, Matrix.sum_apply, Fintype.sum_sum_type, Sum.elim_inl,
        Sum.elim_inr, vecMulVec_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, nsmul_eq_mul]
      push_cast
      rw [hc]
      refine Fin.cases ?_ (fun p => ?_) p <;> refine Fin.cases ?_ (fun q => ?_) q
      · simp
        ring
      · simp
        ring
      · simp [hsz 0 p.succ]
        ring
      · simp only [Fin.cons_succ]
        rw [← hy' p q, hsz 0 p.succ]
        ring

theorem exists_smul_eq_sum_vecMulVec_span :
    ∀ (r : ℕ) (L : Matrix (Fin r) (Fin r) ℤ), (L.map (Int.cast : ℤ → ℝ)).PosDef →
      ∃ (D m : ℕ) (a : Fin m → Fin r → ℤ), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧
        (D : ℤ) • L = ∑ i, Matrix.vecMulVec (a i) (a i) := by
  intro r L hL
  obtain ⟨κ₀, hκ⟩ := exists_nat_smul_sub_posDef hL (isHermitian_one (α := ℝ) (n := Fin r))
  set d := max κ₀ 1 with hdd
  have hd1 : 1 ≤ d := le_max_right _ _
  have hd := hκ d (le_max_left _ _)
  set M : Matrix (Fin r) (Fin r) ℤ := (d : ℤ) • L - 1 with hMdef
  have hM : (M.map (Int.cast : ℤ → ℝ)).PosDef := by
    convert hd using 1
    ext i j
    simp only [hMdef, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  obtain ⟨ι, _, D, a, hD, ha⟩ := exists_smul_eq_sum_vecMulVec r M hM
  let b : (Fin r × Fin D) ⊕ ι → Fin r → ℤ := Sum.elim (fun p => Pi.single p.1 1) a
  have hsum : ((D * d : ℕ) : ℤ) • L = ∑ k, vecMulVec (b k) (b k) := by
    rw [Fintype.sum_sum_type]
    simp only [b, Sum.elim_inl, Sum.elim_inr]
    rw [← ha]
    ext i j
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [hMdef, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
      vecMulVec_apply, smul_eq_mul, Matrix.one_apply]
    simp only [nsmul_eq_mul]
    push_cast
    have hδ : ∑ c : Fin r, (Pi.single c (1 : ℤ) : Fin r → ℤ) i * (Pi.single c (1 : ℤ) : Fin r → ℤ) j =
        if i = j then 1 else 0 := by
      by_cases h : i = j
      · subst h
        simp [Pi.single_apply]
      · simp [Pi.single_apply, h]
    rw [← Finset.mul_sum, hδ]
    split_ifs <;> ring
  have hspan : Submodule.span ℤ (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin r)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨Sum.inl (j, ⟨0, hD⟩), by simp [b]⟩
  let e := Fintype.equivFin ((Fin r × Fin D) ⊕ ι)
  refine ⟨D * d, Fintype.card ((Fin r × Fin D) ⊕ ι), b ∘ e.symm, ?_, ?_, ?_⟩
  · nlinarith
  · rw [e.symm.surjective.range_comp]
    exact hspan
  · rw [hsum]
    exact (e.symm.sum_comp (fun k => vecMulVec (b k) (b k))).symm

end GlobalTheory.Poinc.SumSq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulEqSumVecMulVecSpanningFamilyStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_eq_sum_vecMulVec_spanning_family : ∀ (r : ℕ) (L : Matrix (Fin r) (Fin r) ℤ), (L.map (Int.cast : ℤ → ℝ)).PosDef → ∃ (D m : ℕ) (a : Fin m → Fin r → ℤ), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧ (D : ℤ) • L = ∑ i, Matrix.vecMulVec (a i) (a i) := by
  first | exact @GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span | exact GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span | (intros; apply GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span <;> assumption)
end
end
