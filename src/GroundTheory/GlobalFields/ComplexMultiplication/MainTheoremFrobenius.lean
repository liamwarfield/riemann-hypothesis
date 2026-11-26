module

public import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes
public import GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismPoints
public import GroundTheory.GlobalFields.ComplexMultiplication.TorsionReduction

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremReduction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open IsLocalRing WeierstrassCurve GroundTheory.Arith.Abelian

section VariableChange

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  (C : VariableChange 𝒪) [W.IsElliptic] [DecidableEq K]


omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] [W.IsElliptic] [DecidableEq K] in
theorem vcX_notMem_range {X : K} (hX : X ∉ Set.range (algebraMap 𝒪 K)) :
    vcX (C.map (algebraMap 𝒪 K)) X ∉ Set.range (algebraMap 𝒪 K) := by
  rintro ⟨a, ha⟩
  apply hX
  refine ⟨vcX' C a, ?_⟩
  rw [map_vcX', ha]
  exact vcX'_vcX _ X

theorem reducePoint_vcEquivK (P : (curveK K W).Point) :
    reducePoint K (C • W) (vcEquivK K W C P) =
      vcPoint (C.map (residue 𝒪)) (map_vc_eq_residue W C) (reducePoint K W P) := by
  rcases point_cases K W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · rw [vcEquivK_zero, reducePoint_zero, reducePoint_zero]
    rfl
  · rw [vcEquivK_some K W C h (nonsingular_K_vc K W C h),
      reducePoint_some_notMem K (C • W) _ (vcX_notMem_range K C hX), reducePoint_some_notMem K W h hX]
    rfl
  · have n₁ := nonsingular_residue_of_isElliptic K W h.1
    have hx : vcX (C.map (algebraMap 𝒪 K)) (algebraMap 𝒪 K x) = algebraMap 𝒪 K (vcX C x) :=
      (map_vcX C (algebraMap 𝒪 K) x).symm
    have hy : vcY (C.map (algebraMap 𝒪 K)) (algebraMap 𝒪 K x) (algebraMap 𝒪 K y) =
        algebraMap 𝒪 K (vcY C x y) :=
      (map_vcY C (algebraMap 𝒪 K) x y).symm
    have h₂ : (curveK K (C • W)).Nonsingular (algebraMap 𝒪 K (vcX C x))
        (algebraMap 𝒪 K (vcY C x y)) := by
      have := nonsingular_K_vc K W C h
      rwa [hx, hy] at this
    have n₂ := nonsingular_residue_of_isElliptic K (C • W) h₂.1
    have e : vcEquivK K W C (.some _ _ h) = .some _ _ h₂ := by
      rw [vcEquivK_some K W C h (nonsingular_K_vc K W C h), Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
    rw [e, reducePoint_some_integral K (C • W) h₂ n₂, reducePoint_some_integral K W h n₁, vcPoint_some,
      Affine.Point.some.injEq]
    exact ⟨map_vcX C (residue 𝒪) x, map_vcY C (residue 𝒪) x y⟩

theorem reducePoint_vcPoint {W' : WeierstrassCurve 𝒪} (hC : C • W = W') (P : (curveK K W).Point) :
    reducePoint K W' (vcPoint (C.map (algebraMap 𝒪 K)) (by rw [map_vc_eq, hC]) P) =
      vcPoint (C.map (residue 𝒪)) (by rw [map_vc_eq_residue, hC]) (reducePoint K W P) := by
  subst hC
  exact reducePoint_vcEquivK K W C P

end VariableChange

section Frobenius

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField 𝒪) p] {g : 𝒪 →+* 𝒪}

variable [IsLocalHom g]

theorem residueField_map_eq_frobenius (hg : ∀ x, residue 𝒪 (g x) = residue 𝒪 x ^ p) :
    ResidueField.map g = frobenius (ResidueField 𝒪) p := by
  ext y
  obtain ⟨x, rfl⟩ := residue_surjective y
  rw [ResidueField.map_residue, hg, frobenius_def]

theorem map_residue_eq_frobeniusTwist (hg : ∀ x, residue 𝒪 (g x) = residue 𝒪 x ^ p) :
    (W.map (residue 𝒪)).map (frobenius (ResidueField 𝒪) p) = (W.map g).map (residue 𝒪) := by
  rw [← residueField_map_eq_frobenius p hg]
  exact map_curveRed_eq W

variable [W.IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)] {G : K →+* K}
  (hG : G.comp (algebraMap 𝒪 K) = (algebraMap 𝒪 K).comp g)


include hG in
theorem reducePoint_pointMapRing_frobenius (hg : ∀ x, residue 𝒪 (g x) = residue 𝒪 x ^ p)
    (P : (curveK K W).Point) :
    reducePoint K (W.map g) (pointCongr (map_curveK_eq K K hG W)
        (pointMapRing G (W.map (algebraMap 𝒪 K)) P)) =
      pointCongr (map_residue_eq_frobeniusTwist W p hg)
        (pointMapRing (frobenius (ResidueField 𝒪) p) (W.map (residue 𝒪)) (reducePoint K W P)) := by
  rw [reducePoint_pointMapRing K K hG W P,
    pointMapRing_congr (residueField_map_eq_frobenius p hg), pointCongr_pointCongr]

end Frobenius

section NumberField

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  (𝔓 : HeightOneSpectrum (𝓞 L)) {τ : L ≃ₐ[K] L} (hτ : IsArithFrobAt (𝓞 K) τ 𝔓.asIdeal)

include hτ in
theorem mem_localizationAt_of_isArithFrobAt {x : L} (hx : x ∈ localizationAt L 𝔓) :
    τ x ∈ localizationAt L 𝔓 :=
  (Elliptic.residue_apply_of_isArithFrobAt 𝔓 hτ hx).1

def localizationAtRingHom : localizationAt L 𝔓 →+* localizationAt L 𝔓 :=
  ((τ : L →+* L).comp (localizationAt L 𝔓).val.toRingHom).codRestrict (localizationAt L 𝔓).toSubsemiring
    fun x ↦ mem_localizationAt_of_isArithFrobAt 𝔓 hτ x.2

theorem comp_algebraMap_localizationAtRingHom :
    (τ : L →+* L).comp (algebraMap (localizationAt L 𝔓) L) =
      (algebraMap (localizationAt L 𝔓) L).comp (localizationAtRingHom 𝔓 hτ) :=
  rfl

theorem residue_localizationAtRingHom (x : localizationAt L 𝔓) :
    residue (localizationAt L 𝔓) (localizationAtRingHom 𝔓 hτ x) =
      residue (localizationAt L 𝔓) x ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  obtain ⟨h, e⟩ := Elliptic.residue_apply_of_isArithFrobAt 𝔓 hτ x.2
  exact e

theorem residue_localizationAtRingHom_of_absNorm [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal] (x : localizationAt L 𝔓) :
    residue (localizationAt L 𝔓) (localizationAtRingHom 𝔓 hτ x) =
      residue (localizationAt L 𝔓) x ^ Ideal.absNorm 𝔭.asIdeal := by
  rw [residue_localizationAtRingHom]
  congr 1
  rw [← Ideal.LiesOver.over (P := 𝔓.asIdeal) (p := 𝔭.asIdeal), Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

instance : IsLocalHom (localizationAtRingHom 𝔓 hτ) := by
  refine ⟨fun x hx ↦ ?_⟩
  rw [← residue_ne_zero_iff_isUnit] at hx ⊢
  rw [residue_localizationAtRingHom] at hx
  exact fun h ↦ hx (by rw [h, zero_pow hτ.card_pos.ne'])

theorem reducePoint_pointMapRing_localizationAtRingHom [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal] (p : ℕ) [Fact p.Prime] (hp : Ideal.absNorm 𝔭.asIdeal = p)
    [CharP (ResidueField (localizationAt L 𝔓)) p] (W : WeierstrassCurve (localizationAt L 𝔓))
    [W.IsElliptic] [DecidableEq L] [DecidableEq (ResidueField (localizationAt L 𝔓))]
    (P : (curveK L W).Point) :
    reducePoint L (W.map (localizationAtRingHom 𝔓 hτ))
        (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W)
          (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) P)) =
      pointCongr (map_residue_eq_frobeniusTwist W p
          (fun x ↦ by rw [residue_localizationAtRingHom_of_absNorm 𝔓 hτ 𝔭 x, hp]))
        (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p)
          (W.map (residue (localizationAt L 𝔓))) (reducePoint L W P)) :=
  reducePoint_pointMapRing_frobenius L W p (comp_algebraMap_localizationAtRingHom 𝔓 hτ)
    (fun x ↦ by rw [residue_localizationAtRingHom_of_absNorm 𝔓 hτ 𝔭 x, hp]) P

end NumberField

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open Polynomial NumberField IsDedekindDomain IsLocalRing

section Generic

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (f : R →+* S)

theorem isPrimitiveRoot_map_of_natCast_ne_zero {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : (n : S) ≠ 0) : IsPrimitiveRoot (f ζ) n := by
  have : NeZero (n : S) := ⟨hn⟩
  have : NeZero (n : R) := ⟨fun h => hn (by rw [← map_natCast f n, h, map_zero])⟩
  have hr : eval ζ (cyclotomic n R) = 0 := isRoot_cyclotomic_iff.mpr hζ
  apply isRoot_cyclotomic_iff.mp
  show eval (f ζ) (cyclotomic n S) = 0
  rw [← map_cyclotomic n f, eval_map, eval₂_hom, hr, map_zero]

theorem eq_of_map_eq_of_pow_eq_one {ζ : R} {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (hn : (n : S) ≠ 0) {η η' : R} (hη : η ^ n = 1) (hη' : η' ^ n = 1) (h : f η = f η') :
    η = η' := by
  have hf := isPrimitiveRoot_map_of_natCast_ne_zero f hζ hn
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη'
  rw [map_pow, map_pow] at h
  rw [hf.pow_inj hj hk h]

theorem existsUnique_pow_eq_one_of_isPrimitiveRoot {ζ : R} {n : ℕ} [NeZero n]
    (hζ : IsPrimitiveRoot ζ n) (hn : (n : S) ≠ 0) {w : S} (hw : w ^ n = 1) :
    ∃! η : R, η ^ n = 1 ∧ f η = w := by
  have hf := isPrimitiveRoot_map_of_natCast_ne_zero f hζ hn
  obtain ⟨i, -, e⟩ := hf.eq_pow_of_pow_eq_one hw
  have hi : (ζ ^ i) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨ζ ^ i, ⟨hi, by rw [map_pow, e]⟩, ?_⟩
  rintro η ⟨hη, hfη⟩
  exact eq_of_map_eq_of_pow_eq_one f hζ hn hη hi (by rw [hfη, map_pow, e])

end Generic

theorem two_ne_zero_and_three_ne_zero_of_five_le_ringChar {k : Type*} [Field k]
    (h : 5 ≤ ringChar k) : (2 : k) ≠ 0 ∧ (3 : k) ≠ 0 := by
  refine ⟨fun h2 => ?_, fun h3 => ?_⟩
  · have := Nat.le_of_dvd (by norm_num) ((ringChar.spec k 2).mp (by exact_mod_cast h2))
    omega
  · have := Nat.le_of_dvd (by norm_num) ((ringChar.spec k 3).mp (by exact_mod_cast h3))
    omega

section NumberField

variable {L : Type*} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

end NumberField

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremPointHom
section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.ReductionAtPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

section Translate

variable {F : Type u} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]

theorem isGenPt_genericPoint_add_constMap (R : E.toAffine.Point) :
    IsGenPt E (genericPoint E + constMap E E.toAffine.FunctionField R) := by
  have hG : TransOver E F (genericPoint E) := transcendental_genX E
  have := hG.add_left (M := E.toAffine.FunctionField) R
  rw [add_comm]
  exact this.isGenPt

end Translate

section OverF

variable {F : Type u} [Field F] [DecidableEq F] {E E' : WeierstrassCurve F} [E.IsElliptic]
  [E'.IsElliptic] (Ω : Type u) [Field Ω] [Algebra F Ω] [DecidableEq Ω]


omit [DecidableEq F] in
theorem isogBaseChange_app (φ : Isogeny E E')
    (X : ((E.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
    (hX : IsGenPt (E.baseChange Ω) X)
    (hX' : IsGenPt E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)) :
    (isogBaseChange (F' := Ω) φ).app X hX =
      φ.app (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) hX' := by
  have hg : ((genEval (E.baseChange Ω) X hX).restrictScalars F).comp (bcEmb (F' := Ω) E) =
      genEval E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
        hX' := by
    refine eq_genEval E _ ?_ _
    cases X with
    | zero => exact hX.elim
    | some u v hv =>
      simp only [GroundTheory.Arith.Abelian.genericPoint, Point.map_some]
      congr 1
      · show genEval (E.baseChange Ω) _ hX (bcEmb (F' := Ω) E (genX E)) = u
        rw [bcEmb_genX]; exact genEval_genX (E.baseChange Ω) _ hX
      · show genEval (E.baseChange Ω) _ hX (bcEmb (F' := Ω) E (genY E)) = v
        rw [bcEmb_genY]; exact genEval_genY (E.baseChange Ω) _ hX
  unfold Isogeny.app
  rw [isogBaseChange_val, ← hg, ← Point.map_map]
  generalize Point.map (W' := E') (bcEmb (F' := Ω) E) φ.1 = Y
  cases Y <;> rfl


omit [DecidableEq F] [E.IsElliptic] [DecidableEq Ω] in
theorem isGenPt_of_isGenPt_baseChange
    (X : ((E.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
    (h : IsGenPt (E.baseChange Ω) X) :
    IsGenPt E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) := by
  cases X with
  | zero => exact h.elim
  | some x y _ => exact Transcendental.restrictScalars (algebraMap F Ω).injective h


omit [E.IsElliptic] in
theorem constMap_constMap_baseChange (V : WeierstrassCurve F) (R : V.toAffine.Point) :
    (constMap (V.baseChange Ω) (E.baseChange Ω).toAffine.FunctionField (constMap V Ω R) :
      (V.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) =
      constMap V (E.baseChange Ω).toAffine.FunctionField R := by
  cases R <;> rfl

theorem app_genericPoint_add_constMap [PerfectField F] [IsAlgClosed Ω] (φ : Isogeny E E')
    (R : E.toAffine.Point) :
    φ.app (genericPoint E + constMap E E.toAffine.FunctionField R)
        (isGenPt_genericPoint_add_constMap E R) =
      φ.1 + constMap E' E.toAffine.FunctionField (pointHomOver Ω φ R) := by
  set K' := (E.baseChange Ω).toAffine.FunctionField
  set ι := bcEmb (F' := Ω) E
  set Rω := constMap E Ω R
  set φΩ := isogBaseChange (F' := Ω) φ
  have hGΩ : IsGenPt (E.baseChange Ω) (genericPoint (E.baseChange Ω)) :=
    transcendental_genX (E.baseChange Ω)
  have hX := isGenPt_genericPoint_add_constMap (E.baseChange Ω) Rω
  have h1 := φΩ.app_add_constMap hGΩ Rω hX
  rw [φΩ.app_genericPoint hGΩ, ← constMap_pointHomOver] at h1
  have app_eq : ∀ {P P' : (E.baseChange K').toAffine.Point} (h : P = P') (hP : IsGenPt E P)
      (hP' : IsGenPt E P'), φ.app P hP = φ.app P' hP' := by
    intro P P' h hP hP'; subst h; rfl
  have e1 : Point.map ι (genericPoint E + constMap E E.toAffine.FunctionField R) =
      ((genericPoint (E.baseChange Ω) + constMap (E.baseChange Ω) K' Rω :
        ((E.baseChange Ω).baseChange K').toAffine.Point) : (E.baseChange K').toAffine.Point) := by
    rw [map_add (f := _), map_bcEmb_genericPoint, map_constMap, ← constMap_constMap_baseChange Ω E R]
    rfl
  have hX' := isGenPt_of_isGenPt_baseChange Ω _ hX
  apply Point.map_injective (W' := E') ι
  rw [Isogeny.map_app]
  refine (app_eq e1 _ hX').trans ?_
  rw [← isogBaseChange_app Ω φ _ hX hX', h1, map_add (f := _), map_constMap,
    ← constMap_constMap_baseChange Ω (E := E) E' (pointHomOver Ω φ R)]
  rfl

end OverF

section Reduction

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

theorem reduceFF_constMap (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    (c : (V.baseChange K).toAffine.Point) :
    reduceFF K W V (constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField c) =
      constMap (V.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
        (reducePoint K V c) := by
  have hσ : (algebraMap K (W.baseChange K).toAffine.FunctionField).comp (algebraMap 𝒪 K) =
      (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField).comp
        (algebraMap 𝒪 (gaussRing W)) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  cases c with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | some X Y h =>
    by_cases hX : X ∈ Set.range (algebraMap 𝒪 K)
    · obtain ⟨x, rfl⟩ := hX
      obtain ⟨y, rfl⟩ := exists_y_of_equation K V h.1
      obtain ⟨h₁, e₁⟩ : ∃ h₁, constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField
          (Point.some _ _ h) = Point.some (algebraMap K (W.baseChange K).toAffine.FunctionField
            (algebraMap 𝒪 K x)) (algebraMap K (W.baseChange K).toAffine.FunctionField
              (algebraMap 𝒪 K y)) h₁ := ⟨_, rfl⟩
      have hx := RingHom.congr_fun hσ x
      have hy := RingHom.congr_fun hσ y
      simp only [RingHom.comp_apply] at hx hy
      obtain ⟨h₂, e₂⟩ := exists_some_eq h₁ hx hy
      obtain ⟨h₃, e₃⟩ := reduceFF_some K W V h₂
      rw [e₁, e₂, e₃]
      have e₄ := reducePoint_some_integral K V h
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (equation_residue V (equation_of_map K V h.1)))
      refine Eq.trans ?_ (congrArg (constMap (V.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField) e₄).symm
      show _ = Point.some _ _ _
      simp only [Point.some.injEq, gaussResidue_residue_algebraMap]
      exact ⟨rfl, rfl⟩
    · have hX' := map_notMem_range K (W.baseChange K).toAffine.FunctionField
        (f := algebraMap 𝒪 (gaussRing W)) hσ hX
      have e₄ := reducePoint_some_notMem K V h hX
      refine Eq.trans ?_ (congrArg (constMap (V.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField) e₄).symm
      obtain ⟨h₁, e₁⟩ : ∃ h₁, constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField
          (Point.some X Y h) = Point.some (algebraMap K (W.baseChange K).toAffine.FunctionField X)
            (algebraMap K (W.baseChange K).toAffine.FunctionField Y) h₁ := ⟨_, rfl⟩
      rw [e₁, map_zero]
      simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        reductionHom_apply]
      rw [pointCongr_some, reducePoint_some_notMem _ (gaussCurve W V) _ hX', map_zero, map_zero]

variable [W.IsElliptic] [W'.IsElliptic]

theorem reduceFF_genericPoint_add_constMap (R : (W.baseChange K).toAffine.Point) :
    reduceFF K W W (genericPoint (W.baseChange K) +
        constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R) =
      genericPoint (W.map (residue 𝒪)) +
        constMap (W.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
          (reducePoint K W R) := by
  rw [map_add (f := _), reduceFF_genericPoint, reduceFF_constMap]


set_option maxHeartbeats 1000000 in
theorem reduceIsogeny_app_add_constMap (φ : Isogeny (W.baseChange K) (W'.baseChange K))
    (R : (W.baseChange K).toAffine.Point) (S : (W'.baseChange K).toAffine.Point)
    (h : φ.app (genericPoint (W.baseChange K) +
        constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R)
        (isGenPt_genericPoint_add_constMap _ R) =
      φ.1 + constMap (W'.baseChange K) (W.baseChange K).toAffine.FunctionField S) :
    (reduceIsogeny K W W' φ).app (genericPoint (W.map (residue 𝒪)) +
        constMap (W.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
          (reducePoint K W R)) (isGenPt_genericPoint_add_constMap _ _) =
      (reduceIsogeny K W W' φ).1 + constMap (W'.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField (reducePoint K W' S) := by
  have hR' : IsGenPt (W.map (residue 𝒪)) (reduceFF K W W (genericPoint (W.baseChange K) +
      constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R)) := by
    rw [reduceFF_genericPoint_add_constMap]
    exact isGenPt_genericPoint_add_constMap _ _
  have key := reduceFF_map_genEval K W W W' (isGenPt_genericPoint_add_constMap _ R) hR' φ.1
  have h2 := congrArg (reduceFF K W W') h
  rw [map_add (f := _), reduceFF_constMap] at h2
  rw [reduceIsogeny_val, ← h2]
  unfold Isogeny.app at key ⊢
  rw [key, reduceIsogeny_val, genEval_congr _ (reduceFF_genericPoint_add_constMap K W R) hR']

end Reduction

section PointsOverPerfect

universe v w

variable {𝒪 : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type v) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {W W' : WeierstrassCurve 𝒪}
  [W.IsElliptic] [W'.IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [PerfectField K] [PerfectField (ResidueField 𝒪)]
  (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
  (Ωk : Type w) [Field Ωk] [Algebra (ResidueField 𝒪) Ωk] [IsAlgClosed Ωk] [DecidableEq Ωk]

theorem reducePoint_pointHomOver (φ : Isogeny (W.baseChange K) (W'.baseChange K))
    (R : (W.baseChange K).toAffine.Point) :
    reducePoint K W' (pointHomOver Ω φ R) =
      pointHomOver Ωk (reduceIsogeny K W W' φ) (reducePoint K W R) := by
  have h := reduceIsogeny_app_add_constMap K W W' φ R _ (app_genericPoint_add_constMap Ω φ R)
  rw [app_genericPoint_add_constMap Ωk (reduceIsogeny K W W' φ) (reducePoint K W R),
    add_right_inj] at h
  exact (constMap_injective _ _ h).symm

end PointsOverPerfect

end

end GroundTheory.Global
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

section OverF

variable {F : Type u} [Field F] [DecidableEq F] (Ω : Type u) [Field Ω] [Algebra F Ω]
  [DecidableEq Ω] [PerfectField F] [IsAlgClosed Ω]

omit [DecidableEq F] [PerfectField F] in
theorem app_eq_of_eq {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] (φ : Isogeny E E')
    {L : Type*} [Field L] [Algebra F L] [DecidableEq L] {P P' : (E.baseChange L).toAffine.Point}
    (h : P = P') (hP : IsGenPt E P) (hP' : IsGenPt E P') : φ.app P hP = φ.app P' hP' := by
  subst h
  rfl

theorem pointHomOver_comp {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
    [E''.IsElliptic] (ψ : Isogeny E' E'') (φ : Isogeny E E') (R : E.toAffine.Point) :
    pointHomOver Ω (ψ.comp φ) R = pointHomOver Ω ψ (pointHomOver Ω φ R) := by
  apply constMap_injective E'' E.toAffine.FunctionField
  set R' := pointHomOver Ω φ R
  have hX' := isGenPt_genericPoint_add_constMap E' R'
  have e0 := app_genericPoint_add_constMap Ω φ R
  have h1 := app_genericPoint_add_constMap Ω (ψ.comp φ) R

  have e : φ.1 + constMap E' E.toAffine.FunctionField R' =
      Point.map φ.comap (genericPoint E' + constMap E' E'.toAffine.FunctionField R') := by
    rw [map_add (f := _), Isogeny.map_comap_genericPoint, map_constMap]
  have hY : IsGenPt E' (φ.1 + constMap E' E.toAffine.FunctionField R') := by
    rw [e]
    exact isGenPt_map E' φ.comap hX'
  have h2 : ψ.app (φ.1 + constMap E' E.toAffine.FunctionField R') hY =
      Point.map φ.comap (ψ.1 + constMap E'' E'.toAffine.FunctionField (pointHomOver Ω ψ R')) := by
    rw [← app_genericPoint_add_constMap Ω ψ R', Isogeny.map_app]
    exact app_eq_of_eq ψ e _ _
  rw [Isogeny.app_comp, app_eq_of_eq ψ e0 _ hY, h2, map_add (f := _), map_constMap, ← Isogeny.comp_val,
    add_right_inj] at h1
  exact h1.symm

theorem pointHomOver_congr {E E' E₁ E₁' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
    [E₁.IsElliptic] [E₁'.IsElliptic] (φ : Isogeny E E') (hE : E = E₁) (hE' : E' = E₁')
    (R : E.toAffine.Point) :
    pointHomOver Ω (φ.congr hE hE') (pointCongr hE R) = pointCongr hE' (pointHomOver Ω φ R) := by
  subst hE hE'
  rw [Isogeny.congr_rfl]
  rfl

end OverF

section Frobenius

variable {F : Type u} [Field F] [DecidableEq F] (Ω : Type u) [Field Ω] [Algebra F Ω]
  [DecidableEq Ω] [PerfectField F] [IsAlgClosed Ω] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [Fact p.Prime] [CharP F p]

omit [PerfectField F] [E.IsElliptic] in
theorem frobeniusPoint_constMap {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (R : E.toAffine.Point) :
    frobeniusPoint E p L (constMap E L R) =
      constMap (frobeniusTwist E p) L (pointMapRing (frobenius F p) E R) := by
  rcases R with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := pointMapRing_some (frobenius F p) E h
    rw [e]
    show Point.some _ _ _ = Point.some _ _ _
    simp only [Algebra.ofId_apply, frobenius_def, map_pow]

theorem pointHomOver_frobeniusIsogeny (R : E.toAffine.Point) :
    pointHomOver Ω (frobeniusIsogeny E p) R = pointMapRing (frobenius F p) E R := by
  have : CharP E.toAffine.FunctionField p :=
    charP_of_injective_algebraMap (algebraMap F E.toAffine.FunctionField).injective p
  apply constMap_injective (frobeniusTwist E p) E.toAffine.FunctionField
  have hX := isGenPt_genericPoint_add_constMap E R
  have h1 := app_genericPoint_add_constMap Ω (frobeniusIsogeny E p) R
  rw [frobeniusIsogeny_app, frobeniusPoint_add, frobeniusPoint_constMap] at h1
  have h2 : frobeniusPoint E p E.toAffine.FunctionField (genericPoint E) = (frobeniusIsogeny E p).1 :=
    rfl
  rw [h2, add_right_inj] at h1
  exact h1.symm

end Frobenius

end

end GroundTheory.Global
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
  GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Congr

variable {F : Type*} [Field F] [DecidableEq F]

theorem vcPoint_pointCongr {V₁ V₂ : WeierstrassCurve F} (e : V₁ = V₂) (C : VariableChange F)
    (h₁ : C • V₁ = V₁) (h₂ : C • V₂ = V₂) (X : V₁.toAffine.Point) :
    vcPoint C h₂ (pointCongr e X) = pointCongr e (vcPoint C h₁ X) := by
  subst e
  rfl

theorem pointCongr_symm_pointCongr {V₁ V₂ : WeierstrassCurve F} (e : V₁ = V₂)
    (X : V₁.toAffine.Point) : pointCongr e.symm (pointCongr e X) = X := by
  subst e
  rfl

theorem vcPoint_nsmul {V₁ V₂ : WeierstrassCurve F} (C : VariableChange F) (h : C • V₁ = V₂)
    (n : ℕ) (X : V₁.toAffine.Point) : n • vcPoint C h X = vcPoint C h (n • X) := by
  rw [← vcPointEquiv_apply, ← vcPointEquiv_apply, map_nsmul]

omit [DecidableEq F] in
theorem vcPoint_eq_zero_of_eq_zero {V₁ V₂ : WeierstrassCurve F} (C : VariableChange F)
    (h : C • V₁ = V₂) {X : V₁.toAffine.Point} (hX : X = 0) : vcPoint C h X = 0 := by
  subst hX
  rfl

omit [DecidableEq F] in
theorem vcPoint_congr_change {V₁ V₂ : WeierstrassCurve F} {C C' : VariableChange F} (e : C = C')
    (h : C • V₁ = V₂) (h' : C' • V₁ = V₂) (X : V₁.toAffine.Point) :
    vcPoint C h X = vcPoint C' h' X := by
  subst e
  rfl

end Congr

section Scaling

universe u

variable {k : Type u} [Field k] [DecidableEq k] [PerfectField k] (Ω : Type u) [Field Ω]
  [Algebra k Ω] [IsAlgClosed Ω] [DecidableEq Ω]

def scaleChange {R : Type*} [CommRing R] (u : Rˣ) : VariableChange R := ⟨u⁻¹, 0, 0, 0⟩

omit [DecidableEq k] [PerfectField k] in
theorem scaleChange_smul {T : WeierstrassCurve k} (hT : IsShortForm T) (u : kˣ)
    (h4 : T.a₄ = (u : k) ^ 4 * T.a₄) (h6 : T.a₆ = (u : k) ^ 6 * T.a₆) :
    scaleChange u • T = T := by
  ext
  · simp [scaleChange, variableChange_a₁, hT.a₁_eq]
  · simp [scaleChange, variableChange_a₂, hT.a₂_eq, hT.a₁_eq]
  · simp [scaleChange, variableChange_a₃, hT.a₃_eq]
  · simp only [scaleChange, variableChange_a₄, hT.a₁_eq, hT.a₂_eq, hT.a₃_eq, inv_inv]
    linear_combination -h4
  · simp only [scaleChange, variableChange_a₆, hT.a₁_eq, hT.a₂_eq, hT.a₃_eq, inv_inv]
    linear_combination -h6

theorem exists_pointHomOver_eq_vcPoint {T : WeierstrassCurve k} [T.IsElliptic] (hT : IsShortForm T)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (ψ : Isogeny T T) (hψ : ψ.degree = 1) :
    ∃ (u : kˣ) (hu : scaleChange u • T = T), (u : k) ^ 12 = 1 ∧ T.a₄ = (u : k) ^ 4 * T.a₄ ∧
      T.a₆ = (u : k) ^ 6 * T.a₆ ∧ ∀ P, pointHomOver Ω ψ P = vcPoint (scaleChange u) hu P := by
  obtain ⟨u, h4, h6, hP⟩ :=
    pointMap_isogBaseChange_some_of_degree_eq_one (Ω := Ω) h2 h3 hT hT ψ hψ
  have h12 := (pow_eq_one_of_scale hT h4 h6).2
  refine ⟨u, scaleChange_smul hT u h4 h6, h12, h4, h6, fun P ↦ ?_⟩
  apply constMap_injective T Ω
  rw [constMap_pointHomOver]
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : T.toAffine.Point) = 0 from rfl, map_zero, ← Isogeny.pointHom_apply,
      map_zero, vcPoint_zero, map_zero]
  · obtain ⟨h', e⟩ := hP (algebraMap k Ω x) (algebraMap k Ω y)
      ((T.toAffine.baseChange_nonsingular (f := Algebra.ofId k Ω) (algebraMap k Ω).injective x y).2 h)
    refine e.trans ?_
    show _ = Point.some _ _ _
    simp only [vcX, vcY, scaleChange, Point.some.injEq]
    simp

end Scaling

section Main

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K] {L : IntermediateField K ℂ} [NumberField L]


omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] in
theorem isPrimitiveRoot_localizationAt (𝔓 : HeightOneSpectrum (𝓞 L)) {ζ : L}
    (hζ : IsPrimitiveRoot ζ 12) :
    IsPrimitiveRoot (algebraMap (𝓞 L) (localizationAt L 𝔓) hζ.toInteger) 12 :=
  hζ.toInteger_isPrimitiveRoot.map_of_injective (fun a b h ↦ by
    have := congrArg (algebraMap (localizationAt L 𝔓) L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact RingOfIntegers.ext this)


set_option maxHeartbeats 1000000 in
include hK in
theorem exists_vcPoint_pointHomOver_eq (𝔭 : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm 𝔭.asIdeal).Prime) (h5 : 5 ≤ Ideal.absNorm 𝔭.asIdeal)
    (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    {τ : L ≃ₐ[K] L} (hτ : IsArithFrobAt (𝓞 K) τ 𝔓.asIdeal)
    {A : WeierstrassCurve L} [A.IsElliptic]
    (hEA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K))
    (hEA' : Nonempty (isogEnd ((A.map (τ : L →+* L)).baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny A (A.map (τ : L →+* L)))
    (hφ : (homConstSet (A.baseChange ℂ) ((A.map (τ : L →+* L)).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    {W : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic]
    (hW : W.map (algebraMap (localizationAt L 𝔓) L) = A) [W.IsShortNF]
    (ha₄ : W.a₄ = 0 ∨ IsUnit W.a₄) (ha₆ : W.a₆ = 0 ∨ IsUnit W.a₆)
    {ζ₁₂ : L} (hζ : IsPrimitiveRoot ζ₁₂ 12) {m : ℕ} (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
    ∃ (D : VariableChange L) (hD : D • A.map (τ : L →+* L) = A.map (τ : L →+* L)),
      ∀ t : A.toAffine.Point, m • t = 0 →
        pointHomOver ℂ φ t = vcPoint D hD (pointMapRing (τ : L →+* L) A t) := by
  classical
  subst hW
  obtain ⟨p, hpdef⟩ : ∃ p, p = Ideal.absNorm 𝔭.asIdeal := ⟨_, rfl⟩
  have hv₀ := hv
  rw [← hpdef] at hv h5
  have : Fact p.Prime := ⟨hv⟩
  have : CharP (ResidueField (localizationAt L 𝔓)) p := by
    refine charP_residueField_localizationAt 𝔓 hv ?_
    have := algebraMap_mem_of_liesOver (𝔓 := 𝔓) (Ideal.absNorm_mem 𝔭.asIdeal)
    rwa [map_natCast, ← hpdef] at this
  have h23 : (2 : ResidueField (localizationAt L 𝔓)) ≠ 0 ∧ (3 : ResidueField (localizationAt L 𝔓)) ≠ 0 := by
    refine two_ne_zero_and_three_ne_zero_of_five_le_ringChar ?_
    rw [ringChar.eq (ResidueField (localizationAt L 𝔓)) p]
    exact h5
  have hW' : (W.map (localizationAtRingHom 𝔓 hτ)).map (algebraMap (localizationAt L 𝔓) L) =
      (W.map (algebraMap (localizationAt L 𝔓) L)).map (τ : L →+* L) := by
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, comp_algebraMap_localizationAtRingHom]
  have hres : ∀ x, IsLocalRing.residue _ ((localizationAtRingHom 𝔓 hτ) x) = IsLocalRing.residue (localizationAt L 𝔓) x ^ p :=
    fun x ↦ by rw [hpdef]; exact residue_localizationAtRingHom_of_absNorm 𝔓 hτ 𝔭 x
  have htw : (W.map (IsLocalRing.residue (localizationAt L 𝔓))).map
      (frobenius (ResidueField (localizationAt L 𝔓)) p) = (W.map (localizationAtRingHom 𝔓 hτ)).map (IsLocalRing.residue _) :=
    map_residue_eq_frobeniusTwist W p hres
  obtain ⟨-, -, ⟨ψ, hred, hψdeg, -, -⟩, -⟩ :=
    reduceIsogeny_congr_eq_comp_frobeniusIsogeny hK 𝔭 hv₀ 𝔓 hEA hEA' φ hφ rfl hW' p

  have htw' : (W.map (localizationAtRingHom 𝔓 hτ)).map (IsLocalRing.residue (localizationAt L 𝔓)) =
      frobeniusTwist (W.map (IsLocalRing.residue (localizationAt L 𝔓))) p := htw.symm
  have hT : IsShortForm (frobeniusTwist (W.map (IsLocalRing.residue (localizationAt L 𝔓))) p) :=
    ⟨by simp [frobeniusTwist], by simp [frobeniusTwist], by simp [frobeniusTwist]⟩
  have hψ'deg : (ψ.congr rfl htw').degree = 1 := by rw [Isogeny.degree_congr]; exact hψdeg
  obtain ⟨u, hu, hu12, hu4, hu6, hψ'P⟩ :=
    exists_pointHomOver_eq_vcPoint (AlgebraicClosure (ResidueField (localizationAt L 𝔓))) hT
      h23.1 h23.2 (ψ.congr rfl htw') hψ'deg

  have hζ𝒪 := isPrimitiveRoot_localizationAt 𝔓 hζ
  have h12 : ((12 : ℕ) : ResidueField (localizationAt L 𝔓)) ≠ 0 := by
    rw [show ((12 : ℕ) : ResidueField (localizationAt L 𝔓)) = 2 * 2 * 3 by norm_num]
    exact mul_ne_zero (mul_ne_zero h23.1 h23.1) h23.2
  obtain ⟨η, ⟨hη12, hηu⟩, -⟩ :=
    existsUnique_pow_eq_one_of_isPrimitiveRoot (IsLocalRing.residue _) hζ𝒪 h12 hu12
  have hηunit : IsUnit η := IsUnit.of_pow_eq_one hη12 (by norm_num)
  have injRoot : ∀ {a b : localizationAt L 𝔓}, a ^ 12 = 1 → b ^ 12 = 1 →
      IsLocalRing.residue _ a = IsLocalRing.residue _ b → a = b :=
    fun ha hb h ↦ eq_of_map_eq_of_pow_eq_one (IsLocalRing.residue _) hζ𝒪 h12 ha hb h
  have hres_ne : ∀ {a : localizationAt L 𝔓}, IsUnit a → IsLocalRing.residue _ a ≠ 0 := fun ha ↦ by
    rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not]
    exact ha
  have hW'1 : (W.map (localizationAtRingHom 𝔓 hτ)).a₁ = 0 := by simp
  have hW'2 : (W.map (localizationAtRingHom 𝔓 hτ)).a₂ = 0 := by simp
  have hW'3 : (W.map (localizationAtRingHom 𝔓 hτ)).a₃ = 0 := by simp
  have hpow : ∀ {n : ℕ}, n ∣ 12 → (u : ResidueField (localizationAt L 𝔓)) ^ n = 1 → η ^ n = 1 := by
    intro n _ hun
    refine injRoot (by rw [← pow_mul, mul_comm, pow_mul, hη12, one_pow]) (one_pow _) ?_
    rw [map_pow, hηu, hun, map_one]
  have key4 : η ^ 4 * (W.map (localizationAtRingHom 𝔓 hτ)).a₄ = (W.map (localizationAtRingHom 𝔓 hτ)).a₄ := by
    rcases ha₄ with h0 | hunit
    · simp [h0]
    · have hne : (frobeniusTwist (W.map (IsLocalRing.residue (localizationAt L 𝔓))) p).a₄ ≠ 0 := by
        simp only [frobeniusTwist, WeierstrassCurve.map_a₄, frobenius_def]
        exact pow_ne_zero _ (hres_ne hunit)
      have hu4' : (u : ResidueField (localizationAt L 𝔓)) ^ 4 = 1 :=
        mul_right_cancel₀ hne (by rw [one_mul]; exact hu4.symm)
      rw [hpow (by norm_num) hu4', one_mul]
  have key6 : η ^ 6 * (W.map (localizationAtRingHom 𝔓 hτ)).a₆ = (W.map (localizationAtRingHom 𝔓 hτ)).a₆ := by
    rcases ha₆ with h0 | hunit
    · simp [h0]
    · have hne : (frobeniusTwist (W.map (IsLocalRing.residue (localizationAt L 𝔓))) p).a₆ ≠ 0 := by
        simp only [frobeniusTwist, WeierstrassCurve.map_a₆, frobenius_def]
        exact pow_ne_zero _ (hres_ne hunit)
      have hu6' : (u : ResidueField (localizationAt L 𝔓)) ^ 6 = 1 :=
        mul_right_cancel₀ hne (by rw [one_mul]; exact hu6.symm)
      rw [hpow (by norm_num) hu6', one_mul]
  have hηc : ((hηunit.unit : (localizationAt L 𝔓)ˣ) : localizationAt L 𝔓) = η := hηunit.unit_spec
  have hC : scaleChange hηunit.unit • (W.map (localizationAtRingHom 𝔓 hτ)) = (W.map (localizationAtRingHom 𝔓 hτ)) := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · simp [scaleChange, variableChange_a₁]
    · simp [scaleChange, variableChange_a₂]
    · simp [scaleChange, variableChange_a₃]
    · simp only [scaleChange, variableChange_a₄, hW'1, hW'2, hW'3, inv_inv, hηc]
      linear_combination key4
    · simp only [scaleChange, variableChange_a₆, hW'1, hW'2, hW'3, inv_inv, hηc]
      linear_combination key6
  have hD' : ((scaleChange hηunit.unit).map (algebraMap (localizationAt L 𝔓) L)) • (W.map (localizationAtRingHom 𝔓 hτ)).map (algebraMap (localizationAt L 𝔓) L) =
      (W.map (localizationAtRingHom 𝔓 hτ)).map (algebraMap (localizationAt L 𝔓) L) := by
    rw [map_variableChange, hC]
  have hD : ((scaleChange hηunit.unit).map (algebraMap (localizationAt L 𝔓) L)) • (W.map (algebraMap (localizationAt L 𝔓) L)).map (τ : L →+* L) =
      (W.map (algebraMap (localizationAt L 𝔓) L)).map (τ : L →+* L) := by
    rw [← hW']
    exact hD'
  refine ⟨((scaleChange hηunit.unit).map (algebraMap (localizationAt L 𝔓) L)), hD, fun t ht ↦ ?_⟩

  have hm' : (m : ResidueField (localizationAt L 𝔓)) ≠ 0 := by
    rw [← map_natCast (IsLocalRing.residue (localizationAt L 𝔓)), Ne, IsLocalRing.residue_eq_zero_iff,
      ← map_natCast (algebraMap (𝓞 L) (localizationAt L 𝔓)), algebraMap_mem_maximalIdeal_localizationAt_iff]
    intro h
    apply hm
    rw [Ideal.LiesOver.over (P := 𝔓.asIdeal) (p := 𝔭.asIdeal), Ideal.mem_comap, map_natCast]
    exact h
  have e0 : pointHomOver ℂ (φ.congr rfl hW'.symm) t = pointCongr hW'.symm (pointHomOver ℂ φ t) :=
    pointHomOver_congr ℂ φ rfl hW'.symm t
  have hX : m • (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W) (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) t)) = 0 := by rw [← map_nsmul, ← map_nsmul, ht, map_zero, map_zero]
  have hφ0 : m • pointHomOver ℂ (φ.congr rfl hW'.symm) t = 0 := by rw [← map_nsmul, ht, map_zero]
  have hvX : m • vcPoint ((scaleChange hηunit.unit).map (algebraMap (localizationAt L 𝔓) L)) hD' (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W) (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) t)) = 0 := by
    rw [vcPoint_nsmul]
    exact vcPoint_eq_zero_of_eq_zero _ _ hX

  have r1 : reducePoint L (W.map (localizationAtRingHom 𝔓 hτ)) (pointHomOver ℂ (φ.congr rfl hW'.symm) t) =
      pointCongr htw (vcPoint (scaleChange u) hu (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p) (W.map (IsLocalRing.residue (localizationAt L 𝔓))) (reducePoint L W t))) := by
    have hred' : reduceIsogeny L W (W.map (localizationAtRingHom 𝔓 hτ)) (φ.congr rfl hW'.symm) =
        ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue (localizationAt L 𝔓))) p) := hred
    refine (reducePoint_pointHomOver L ℂ (AlgebraicClosure (ResidueField (localizationAt L 𝔓)))
      (φ.congr rfl hW'.symm) t).trans ?_
    rw [hred', pointHomOver_comp, pointHomOver_frobeniusIsogeny]
    have h1 := pointHomOver_congr (AlgebraicClosure (ResidueField (localizationAt L 𝔓))) ψ rfl htw' (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p) (W.map (IsLocalRing.residue (localizationAt L 𝔓))) (reducePoint L W t))
    rw [hψ'P] at h1
    rw [← pointCongr_symm_pointCongr htw'
      (pointHomOver (AlgebraicClosure (ResidueField (localizationAt L 𝔓))) ψ (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p) (W.map (IsLocalRing.residue (localizationAt L 𝔓))) (reducePoint L W t))), ← h1]
    rfl
  have hCres : (scaleChange hηunit.unit).map (IsLocalRing.residue (localizationAt L 𝔓)) =
      scaleChange u := by
    have hu' : Units.map (IsLocalRing.residue (localizationAt L 𝔓) : _ →* _) hηunit.unit = u :=
      Units.ext (by rw [Units.coe_map, hηc]; exact hηu)
    simp only [scaleChange, VariableChange.map, map_zero, map_inv, hu']
  have r2 : reducePoint L (W.map (localizationAtRingHom 𝔓 hτ)) (vcPoint ((scaleChange hηunit.unit).map (algebraMap (localizationAt L 𝔓) L)) hD' (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W) (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) t))) = pointCongr htw (vcPoint (scaleChange u) hu (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p) (W.map (IsLocalRing.residue (localizationAt L 𝔓))) (reducePoint L W t))) := by
    rw [reducePoint_vcPoint L (W.map (localizationAtRingHom 𝔓 hτ)) (scaleChange hηunit.unit) hC (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W) (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) t)),
      reducePoint_pointMapRing_localizationAtRingHom 𝔓 hτ 𝔭 p hpdef.symm W t]
    exact (vcPoint_congr_change hCres _ _ _).trans
      (vcPoint_pointCongr htw (scaleChange u) hu (by rw [← htw]; exact hu) _)
  have heq := eq_of_reductionHom_eq_of_nsmul L (W.map (localizationAtRingHom 𝔓 hτ)) hm' hφ0 hvX
    (by rw [reductionHom_apply, reductionHom_apply, r1, r2])

  have e1 : pointHomOver ℂ φ t = pointCongr hW' (pointHomOver ℂ (φ.congr rfl hW'.symm) t) := by
    rw [e0, pointCongr_symm_pointCongr]
  rw [e1, heq]
  refine (vcPoint_pointCongr hW' _ hD' hD _).symm.trans ?_
  congr 1

end Main

end

end Elliptic
end GroundTheory.Global
