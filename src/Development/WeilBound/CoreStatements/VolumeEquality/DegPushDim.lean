module

public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameChangeUnitary
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTranslatedRiemannLattice
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicAdaptedFrameOnBall
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusHolomorphicPotentialChange
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.Master

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.DegPushDim
noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

section

variable (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]

omit [Fintype K] [∀ b, Fintype (ι b)] in
theorem fnField_toSubfield (y : (Σ b, ι b) → Ω) :
    (fnField k y).toSubfield = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y := by
  rw [fnField, IntermediateField.adjoin_toSubfield]
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField
  congr 2
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    simp only at hpq
    subst hpq
    exact ⟨⟨a, i, j⟩, rfl⟩
  · rintro ⟨⟨a, i, j⟩, rfl⟩
    exact ⟨⟨a, i⟩, ⟨a, j⟩, rfl, rfl⟩

theorem trdeg_eq_of_finite (A : IntermediateField k Ω) [FiniteDimensional A Ω] : Algebra.trdeg k A = Algebra.trdeg k Ω := by
  rw [← trdeg_add_eq k A (A := Ω), trdeg_eq_zero (R := A) (A := Ω), add_zero]

theorem krull_pointIdeal (y : (Σ b, ι b) → Ω) (d : ℕ) (h : IsPt k y d) [(pointIdeal k y).IsPrime] :
    ringKrullDim (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hnz, hfin, htr⟩ := h
  have hcone := ConeTrdegFnField.proof k Ω (algebraMap k Ω).injective K ι y hnz
  have hset : ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω) = ((fnField k y : IntermediateField k Ω) : Set Ω) := by
    rw [← fnField_toSubfield k y]
    rfl
  have hadj : Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) = Algebra.trdeg k (fnField k y) := by
    rw [hset]
    have : Algebra.adjoin k ((fnField k y : IntermediateField k Ω) : Set Ω) = (fnField k y).toSubalgebra :=
      Algebra.adjoin_eq (fnField k y).toSubalgebra
    rw [this]
    rfl
  haveI : FiniteDimensional (fnField k y) Ω := hfin
  have htr' : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have e : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) + (Fintype.card K : Cardinal) := hcone
    rw [e, hadj, trdeg_eq_of_finite k (fnField k y), htr]
    push_cast
    rfl
  exact ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (d + Fintype.card K) htr'

end

theorem ptDim : PtDim := by
  intro k _ Ω _ _ K _ ι _ y d h
  classical
  have hmp : IsMultiProjPrime (pointIdeal k y) := PointIdealMultiProj.proof k Ω K ι y h.1
  have hdim := krull_pointIdeal k y d h
  refine ⟨?_, ?_, ?_⟩
  · convert hmp
  · unfold FieldNumbers.relDim
    rw [hdim]
    have e : (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ)) = (d : ℤ) := by
      push_cast
      ring
    change (WithBot.some (WithTop.some (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ))) : WithBot (WithTop ℤ)) = ((d : ℤ) : WithBot (WithTop ℤ))
    rw [e]
    rfl
  · refine ⟨?_, hdim⟩
    exact (Bridge.isMultiProjPrime_iff _).1 hmp

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.DegPushVal
noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI.I4

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)] {K'' : Type} [Fintype K''] {ι'' : K'' → Type}
  [∀ b, Fintype (ι'' b)]

@[simp] theorem vdeg_zero (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) : vdeg O y 0 = 1 := by simp [vdeg]

theorem vdeg_join (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a a') = vdeg O y a * vdeg O y' a' := by
  unfold vdeg
  rw [Fintype.prod_sum_type]
  rfl

theorem vdeg_join_inl (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a 0) = vdeg O y a := by rw [vdeg_join, vdeg_zero, mul_one]

theorem vdeg_join_inr (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim 0 a') = vdeg O y' a' := by rw [vdeg_join, vdeg_zero, one_mul]

namespace ValEq

variable {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {y'' : (Σ b, ι'' b) → Ω}

theorem of_eq {a : K → ℤ} {a' : K' → ℤ} (h : ∀ O : ValuationSubring Ω, vdeg O y a = vdeg O y' a') : ValEq k y a y' a' :=
  ⟨1, one_ne_zero, fun O _ => by rw [h O, map_one, one_mul]⟩

theorem symm {a : K → ℤ} {a' : K' → ℤ} (h : ValEq k y a y' a') : ValEq k y' a' y a := by
  obtain ⟨ρ, h0, h⟩ := h
  refine ⟨ρ⁻¹, inv_ne_zero h0, fun O hO => ?_⟩
  rw [h O hO, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]

theorem trans {a : K → ℤ} {a' : K' → ℤ} {a'' : K'' → ℤ} (h : ValEq k y a y' a') (h' : ValEq k y' a' y'' a'') :
    ValEq k y a y'' a'' := by
  obtain ⟨ρ, h0, h⟩ := h
  obtain ⟨ρ', h0', h'⟩ := h'
  exact ⟨ρ * ρ', mul_ne_zero h0 h0', fun O hO => by rw [h O hO, h' O hO, map_mul, mul_assoc]⟩

theorem join_inl (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) : ValEq k (joinPt y y') (Sum.elim a 0) y a :=
  of_eq fun O => vdeg_join_inl O y y' a

theorem join_inr (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) : ValEq k (joinPt y y') (Sum.elim 0 a') y' a' :=
  of_eq fun O => vdeg_join_inr O y y' a'

end ValEq

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.DegPushMap
noncomputable section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal pointConeMap intNum)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]

theorem pointIdeal_rat {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] (y : (Σ b, ι b) → Ω) :
    pointIdeal ℚ y = (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  have hcomp : ∀ F : MRing ι, pointConeMap ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = mConeMap y F := by
    intro F
    simp only [pointConeMap, mConeMap, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have key : ∀ G : MvPolynomial (Σ b, ι b) ℚ, ∃ n : ℕ, 0 < n ∧ ∃ F : MRing ι,
      MvPolynomial.map (Int.castRingHom ℚ) F = (n : MvPolynomial (Σ b, ι b) ℚ) * G := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C a =>
      refine ⟨a.den, a.pos, C a.num, ?_⟩
      rw [map_C, ← map_natCast (C : ℚ →+* MvPolynomial (Σ b, ι b) ℚ), ← C_mul, Rat.den_mul_eq_num]
      rfl
    | add p q hp hq =>
      obtain ⟨n, hn, F, hF⟩ := hp
      obtain ⟨n', hn', F', hF'⟩ := hq
      refine ⟨n * n', Nat.mul_pos hn hn', C (n' : ℤ) * F + C (n : ℤ) * F', ?_⟩
      rw [map_add (f := _), map_mul, map_mul, hF, hF', map_C, map_C]
      simp only [eq_intCast, Int.cast_natCast, map_natCast, Nat.cast_mul]
      ring
    | mul_X p j hp =>
      obtain ⟨n, hn, F, hF⟩ := hp
      exact ⟨n, hn, F * X j, by rw [map_mul, map_X, hF, mul_assoc]⟩
  apply le_antisymm
  · intro G hG
    obtain ⟨n, hn, F, hF⟩ := key G
    have hG0 : pointConeMap ℚ y G = 0 := hG
    have hFker : F ∈ mCoordIdeal y := by
      show mConeMap y F = 0
      rw [← hcomp, hF, map_mul, hG0, mul_zero]
    have hGeq : G = C ((n : ℚ)⁻¹) * MvPolynomial.map (Int.castRingHom ℚ) F := by
      rw [hF, ← mul_assoc, ← map_natCast (C : ℚ →+* MvPolynomial (Σ b, ι b) ℚ), ← C_mul,
        inv_mul_cancel₀ (by exact_mod_cast hn.ne'), C_1, one_mul]
    rw [hGeq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hFker)
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    show pointConeMap ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = 0
    rw [hcomp]
    exact hF

omit [Fintype K] [∀ b, Fintype (ι b)] in
theorem pointIdeal_map {R Ω₂ Ω : Type} [CommRing R] [Field Ω₂] [Field Ω] [Algebra R Ω₂] [Algebra R Ω] (i : Ω₂ →ₐ[R] Ω)
    (y : (Σ b, ι b) → Ω₂) : pointIdeal R (fun x => i (y x)) = pointIdeal R y := by
  have h : (MvPolynomial.mapAlgHom i).comp (pointConeMap R y) = pointConeMap R (fun x => i (y x)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap]
  ext F
  change pointConeMap R (fun x => i (y x)) F = 0 ↔ pointConeMap R y F = 0
  rw [← h, AlgHom.comp_apply]
  constructor
  · intro h0
    apply MvPolynomial.map_injective (i : Ω₂ →+* Ω) i.toRingHom.injective
    rw [map_zero]
    exact h0
  · intro h0
    rw [h0, map_zero]

theorem ne_of_arith {Ω : Type} [Field Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (b : K) :
    ∃ j, y ⟨b, j⟩ ≠ 0 := by
  obtain ⟨j, hj⟩ := h.2.1.2.2 b
  refine ⟨j, fun h0 => hj ?_⟩
  show mConeMap y (X ⟨b, j⟩) = 0
  simp [mConeMap, h0]

theorem range_le_fnField {Ω₂ Ω : Type} [Field Ω₂] [Field Ω] (i : Ω₂ →+* Ω) {y : (Σ b, ι b) → Ω₂} (hb : Birational y)
    (hy : ∀ b, ∃ j, y ⟨b, j⟩ ≠ 0) (k : Type) [Field k] [Algebra k Ω] :
    i.fieldRange ≤ (fnField k fun x => i (y x)).toSubfield := by
  choose c hc using hy
  have htop := BirationalRatioClosure.full K ι Ω₂ y c hb hc
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ Subfield.closure (GroundTheory.Heights₂.Heights.coneRatios y c) := htop ▸ Subfield.mem_top s
  have hle : Subfield.closure (GroundTheory.Heights₂.Heights.coneRatios y c) ≤
      (fnField k fun x => i (y x)).toSubfield.comap i := by
    rw [Subfield.closure_le]
    rintro _ ⟨p, rfl⟩
    show i (y p / y ⟨p.1, c p.1⟩) ∈ (fnField k fun x => i (y x)).toSubfield
    rw [map_div₀]
    exact IntermediateField.subset_adjoin k _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  exact hle hs

private theorem finiteDimensional_of_subfield_le {Ω : Type} [Field Ω] (S T : Subfield Ω) (h : S ≤ T) [FiniteDimensional S Ω] :
    FiniteDimensional T Ω := by
  letI : Algebra S T := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower S T Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.Finite.of_restrictScalars_finite S T Ω

private theorem trdeg_eq_of_finrank_fieldRange_pos {Ω₂ Ω : Type} [Field Ω₂] [Field Ω] [Algebra ℚ Ω₂] [Algebra ℚ Ω] (i : Ω₂ →+* Ω)
    (d : ℕ) (hZ : Algebra.trdeg ℤ Ω₂ = d) (hfin : 0 < Module.finrank i.fieldRange Ω) :
    Algebra.trdeg ℚ Ω = d := by
  have hQ : Algebra.trdeg ℚ Ω₂ = d := by
    haveI := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have h := _root_.trdeg_add_eq ℤ ℚ (A := Ω₂)
    rw [_root_.trdeg_eq_zero, zero_add, hZ] at h
    exact h
  letI : Algebra Ω₂ Ω := i.toAlgebra
  haveI : IsScalarTower ℚ Ω₂ Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : Algebra Ω₂ i.fieldRange := i.rangeRestrictField.toAlgebra
  haveI : IsScalarTower Ω₂ i.fieldRange Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite i.fieldRange Ω := Module.finite_of_finrank_pos hfin
  haveI : Module.Finite Ω₂ i.fieldRange := by
    refine Module.Finite.of_surjective (Algebra.linearMap Ω₂ i.fieldRange) ?_
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := RingHom.mem_fieldRange.1 hz
    exact ⟨x, Subtype.ext rfl⟩
  haveI : Module.Finite Ω₂ Ω := Module.Finite.trans i.fieldRange Ω
  have h := _root_.trdeg_add_eq ℚ Ω₂ (A := Ω)
  rw [_root_.trdeg_eq_zero (R := Ω₂) (A := Ω), add_zero, hQ] at h
  exact h.symm

theorem numMap : NumMap := by
  intro Ω₂ _ _ Ω _ _ i K _ ι _ y d hb har hfin
  have hy : ∀ b, ∃ j, y ⟨b, j⟩ ≠ 0 := ne_of_arith har
  have hiy : ∀ b, ∃ j, i (y ⟨b, j⟩) ≠ 0 := fun b => by
    obtain ⟨j, hj⟩ := hy b
    exact ⟨j, (map_ne_zero i).2 hj⟩
  haveI : FiniteDimensional i.fieldRange Ω := Module.finite_of_finrank_pos hfin
  have hFD : ∀ (k : Type) [Field k] [Algebra k Ω], FiniteDimensional (fnField k fun x => i (y x)) Ω := by
    intro k _ _
    haveI := finiteDimensional_of_subfield_le i.fieldRange _ (range_le_fnField i hb hy k)
    exact this
  have heq : (fnField ℚ fun x => i (y x)).toSubfield = i.fieldRange := by
    refine le_antisymm ?_ (range_le_fnField i hb hy ℚ)
    rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨q, rfl⟩ | ⟨p, p', _, rfl⟩)
    · exact RingHom.mem_fieldRange.2 ⟨algebraMap ℚ Ω₂ q, by simp⟩
    · exact RingHom.mem_fieldRange.2 ⟨y p / y p', by rw [map_div₀]⟩
  have hrank : Module.finrank (fnField ℚ fun x => i (y x)) Ω = Module.finrank i.fieldRange Ω := by
    rw [show Module.finrank (fnField ℚ fun x => i (y x)) Ω =
      Module.finrank (fnField ℚ fun x => i (y x)).toSubfield Ω from rfl, heq]
  have hpi : pointIdeal ℚ (fun x => i (y x)) = pointIdeal ℚ y := pointIdeal_map i.toRatAlgHom y
  refine ⟨⟨hiy, hFD ℚ, trdeg_eq_of_finrank_fieldRange_pos i d (FnFieldTrdeg.full K ι Ω₂ y d hb har) hfin⟩, hFD, fun a => ?_, fun a => ?_⟩
  · simp only [num, inum]
    rw [hrank, hpi]
  · simp only [inum, GroundTheory.Heights₂.Heights.HilbertSamuel.genDeg]
    rw [pointIdeal_rat]

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BallVolStdZ
noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas
open scoped ComplexOrder

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem stdZ_perExt_vec (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  let v : Λ →+ (Ψ → Fin (j + j') → ℂ) := AddMonoidHom.mk' C.vec fun a b => by
    funext τ i
    simp [LatEmb.vec]
  have h : ((C.perExt R).toAddMonoidHom.comp v).toIntLinearMap = R.P.toIntLinearMap := by
    refine C.lam.ext fun k => ?_
    have e : C.vec (C.lam k) = C.bas k := by
      funext τ i
      exact (C.bas_eq k τ i).symm
    show C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [e, LatEmb.perExt, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h x

theorem stdZ_sgU (τ : Ψ) {A A' : Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : Aᴴ * C.sgr τ * A = sgI j j')
    (hA' : A'ᴴ * C.sgr τ * A' = sgI j j') : IsSgU (C.cinv A τ * A') := by
  have h1 := (GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ A hA).2.1
  have e : A' = A * (C.cinv A τ * A') := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold IsSgU
  generalize C.cinv A τ * A' = v at e ⊢
  rw [e] at hA'
  refine Eq.trans ?_ hA'
  rw [← hA]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem stdZ_eqvBy_symm {R R' : RiemLat E g Λ} (h : R.EqvBy R' 1) : R'.EqvBy R 1 := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k.symm, fun x => ?_⟩
  have := hk x
  simp only [LinearEquiv.coe_one, id_eq] at this ⊢
  rw [this, LinearEquiv.symm_apply_apply]

omit [Fintype Ψ] in
theorem stdZ_zero_mem (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by
    ext a b
    simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

theorem stdZ_reach (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (hA : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j') :
    ∃ t ∈ ballDom F.q, C.IsAdapted (F.R t) A := by
  have h0 := stdZ_zero_mem F.q
  obtain ⟨A0, hA0⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R 0) (F.form_eq 0) (F.sig 0 h0)
  have f0 := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A0 τ) (hA0.unit τ)
  have f1 := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A τ) (hA τ)
  obtain ⟨R', h1, h2, -, h4⟩ := GlobalTheory.T.exists_translated_riemann_lattice E Ψ j j' n g Λ F C (F.R 0) (fun τ => A τ * C.cinv (A0 τ) τ)
    (fun τ => A0 τ * C.cinv (A τ) τ) (F.form_eq 0) (fun τ => by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C.cinv (A0 τ) τ), (f0 τ).1, Matrix.one_mul, (f1 τ).2.1])
    (fun τ => (f0 τ).2.2.2.2.2 _ (hA τ))
  have h5 := h4 A0 hA0
  have e : (fun τ => A τ * C.cinv (A0 τ) τ * A0 τ) = A := by
    funext τ
    rw [Matrix.mul_assoc, (f0 τ).1, Matrix.mul_one]
  rw [e] at h5
  have hs : R'.HasSig F.σ j j' := by
    have := F.sig 0 h0
    unfold RiemLat.HasSig at this ⊢
    rw [h2]
    exact this
  obtain ⟨t, ht, he⟩ := (F.univ R' (h1.trans (F.form_eq 0)) hs).exists
  exact ⟨t, ht, GlobalTheory.T.adapted_frame_of_equivalent E Ψ j j' n g Λ F C R' (F.R t) A h5 (stdZ_eqvBy_symm he)⟩

end

theorem stdZ : StdZ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  have h0 := stdZ_zero_mem F.q
  obtain ⟨A0, hA0⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R 0) (F.form_eq 0) (F.sig 0 h0)
  have f0 := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A0 τ) (hA0.unit τ)
  obtain ⟨Z, G, hZ, hG, hZeq, hpot⟩ := GlobalTheory.T.holomorphic_adapted_frame_on_ball E Ψ j j' n g Λ F C A0 hA0
  have had : ∀ t ∈ ballDom F.q, ∃ A, C.IsAdapted (F.R t) A := fun t ht =>
    GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R t) (F.form_eq t) (F.sig t ht)
  have hmaps : Set.MapsTo Z (ballDom F.q) (ballDom F.q) := by
    intro t ht
    obtain ⟨A, hA⟩ := had t ht
    rw [hZeq t ht A hA]
    exact (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n F.q _ fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ)).2.1 h0
  have hinj : Set.InjOn Z (ballDom F.q) := by
    intro t ht t' ht' h
    obtain ⟨A, hA⟩ := had t ht
    obtain ⟨A', hA'⟩ := had t' ht'
    rw [hZeq t ht A hA, hZeq t' ht' A' hA'] at h
    have e : (fun τ => C.cinv (A0 τ) τ * A' τ) = fun τ => (C.cinv (A0 τ) τ * A τ) * (C.cinv (A τ) τ * A' τ) := by
      funext τ
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A τ), (GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A τ) (hA.unit τ)).2.1,
        Matrix.one_mul]
    rw [e] at h
    have h1 := (GlobalTheory.T.ball_mobius_zero_eq_iff_unitary Ψ j j' n F.q _ _ (fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ))
      (fun τ => stdZ_sgU C τ (hA.unit τ) (hA'.unit τ))).1 h
    have h2 := (GlobalTheory.T.adapted_frame_change_unitary E Ψ j j' n g Λ F C (F.R t) A A' (F.form_eq t) hA hA'.unit).2 h1
    have h3 := GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C (F.R t) (F.R t') A' (F.form_eq t) (F.form_eq t') h2 hA'
    exact (F.univ (F.R t') (F.form_eq _) (F.sig _ ht')).unique ⟨ht, h3⟩ ⟨ht', LinearEquiv.refl _ _, fun _ => rfl⟩
  have hsurj : Set.SurjOn Z (ballDom F.q) (ballDom F.q) := by
    intro s hs
    obtain ⟨w, hw, hws⟩ := GlobalTheory.T.ball_mobius_transitive Ψ j j' n F.q s hs
    obtain ⟨t, ht, hA⟩ := stdZ_reach C (fun τ => A0 τ * w τ) fun τ => by
      have hw' := hw τ
      unfold IsSgU at hw'
      rw [← hw']
      conv_rhs => rw [← hA0.unit τ]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    refine ⟨t, ht, ?_⟩
    rw [hZeq t ht _ hA, ← hws]
    congr 1
    funext τ
    rw [← Matrix.mul_assoc, (f0 τ).1, Matrix.one_mul]
  refine ⟨A0, hA0.unit, Z, ⟨hmaps, hinj, hsurj⟩, fun S hS hSD => ⟨?_, ?_⟩, ?_⟩
  · exact hS.image_of_continuousOn_injOn (hZ.continuousOn.mono hSD) (hinj.mono hSD)
  · exact ballMeas_image F.q hZ (fun t ht => hmaps ht) hinj
      (fun t ht => ballDens_transform F.q hZ hG (fun t ht => hmaps ht) hpot ht) hS hSD
  intro γ δ hδ _ hu t ht t' ht'
  obtain ⟨A, hA⟩ := had t ht
  let a : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun τ =>
    (γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ))
  let ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun τ =>
    ((γ⁻¹ : GL (Fin (j + j')) E) : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ))
  have hai : ∀ τ, a τ * ai τ = 1 := fun τ => by
    simp only [a, ai]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hia : ∀ τ, ai τ * a τ = 1 := fun τ => mul_eq_one_comm.1 (hai τ)
  obtain ⟨R', h1, -, h3, h4⟩ := GlobalTheory.T.exists_translated_riemann_lattice E Ψ j j' n g Λ F C (F.R t) a ai (F.form_eq t) hai hu
  have h5 := h4 A hA
  have hP : ∀ x, R'.P (δ x) = (F.R t).P x := fun x => by
    rw [h3, ← stdZ_perExt_vec C (F.R t) x]
    congr 1
    funext τ
    have hv : C.vec (δ x) τ = a τ *ᵥ C.vec x τ := by
      funext i
      show embOf (F.σ τ) (C.e (δ x) i) = _
      rw [hδ]
      exact RingHom.map_mulVec _ _ _ i
    rw [hv, Matrix.mulVec_mulVec, hia, Matrix.one_mulVec]
  have hm : moebBall F.q (rho (fun τ => embOf (F.σ τ)) A0 (fun τ => C.cinv (A0 τ) τ) γ) (Z t) =
      moebBall F.q (fun τ => C.cinv (A0 τ) τ * (a τ * A τ)) 0 := by
    have hU : ∀ τ, IsSgU (rho (fun τ => embOf (F.σ τ)) A0 (fun τ => C.cinv (A0 τ) τ) γ τ) := fun τ =>
      ((f0 τ).2.2.2.2.1 _ _ (hai τ) (hu τ)).2.2.1
    rw [hZeq t ht A hA, ← GlobalTheory.T.ball_mobius_mul Ψ j j' n F.q _ _ hU (fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ)) 0 h0]
    congr 1
    funext τ
    show C.cinv (A0 τ) τ * (a τ * A0 τ) * (C.cinv (A0 τ) τ * A τ) = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A0 τ), (f0 τ).2.1, Matrix.one_mul]
  rw [hm]
  constructor
  · rintro ⟨k, hk⟩
    refine hZeq t' ht' _ (GlobalTheory.T.adapted_frame_of_equivalent E Ψ j j' n g Λ F C R' (F.R t') _ h5 ⟨k, fun x => ?_⟩)
    obtain ⟨y, rfl⟩ := δ.surjective x
    exact (hk y).trans (congrArg k (hP y).symm)
  · intro h
    obtain ⟨t'', ht'', hA''⟩ := stdZ_reach C _ h5.unit
    obtain rfl : t'' = t' := hinj ht'' ht' ((hZeq t'' ht'' _ hA'').trans h.symm)
    obtain ⟨k, hk⟩ := GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C R' (F.R t'') _ (h1.trans (F.form_eq t)) (F.form_eq _) h5 hA''
    exact ⟨k, fun x => (hk (δ x)).trans (congrArg k (hP x))⟩

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BallVolMoeb
noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas PositivityTheory.EqVol

namespace Moeb

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem sgI_sq : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply]

def sinv (u : Matrix (Sg j j') (Sg j j') ℂ) : Matrix (Sg j j') (Sg j j') ℂ := sgI j j' * uᴴ * sgI j j'

theorem sinv_mul {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : sinv u * u = 1 := by
  unfold IsSgU at h
  rw [sinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, h, sgI_sq]

theorem mul_sinv {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : u * sinv u = 1 :=
  mul_eq_one_comm.1 (sinv_mul h)

theorem sinv_su {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : IsSgU (sinv u) := by
  have h1 := mul_sinv h
  unfold IsSgU at h ⊢
  conv_lhs => rw [← h]
  have : (sinv u)ᴴ * (uᴴ * sgI j j' * u) * sinv u = (u * sinv u)ᴴ * sgI j j' * (u * sinv u) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [this, h1]
  simp

theorem moeb_one (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : moebBall q (fun _ => 1) t = t := by
  funext k
  have : ∀ W : Matrix (Fin j') (Fin j) ℂ, moebW (1 : Matrix (Sg j j') (Sg j j') ℂ) W = W := fun W => by
    rw [moebW, ← fromBlocks_one, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    simp
  simp [moebBall, ballPt, this, ballMat, Function.swap]

theorem moeb_maps (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    {t : Fin n → ℂ} (ht : t ∈ ballDom q) : moebBall q u t ∈ ballDom q :=
  (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q u hu).2.1 ht

theorem moeb_mul (q : Ψ × Fin j × Fin j' ≃ Fin n) {u v w : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    (hv : ∀ τ, IsSgU (v τ)) (hw : ∀ τ, u τ * v τ = w τ) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    moebBall q u (moebBall q v t) = moebBall q w t := by
  rw [← GlobalTheory.T.ball_mobius_mul Ψ j j' n q u v hu hv t ht, funext hw]

theorem moeb_inv (q : Ψ × Fin j × Fin j' ≃ Fin n) {u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    (hv : ∀ τ, IsSgU (v τ)) (hw : ∀ τ, u τ * v τ = 1) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    moebBall q u (moebBall q v t) = t :=
  (moeb_mul q hu hv hw ht).trans (moeb_one q t)

theorem moeb_injOn (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ)) :
    Set.InjOn (moebBall q u) (ballDom q) := fun t ht t' ht' h => by
  rw [← moeb_inv q (fun τ => sinv_su (hu τ)) hu (fun τ => sinv_mul (hu τ)) ht, h,
    moeb_inv q (fun τ => sinv_su (hu τ)) hu (fun τ => sinv_mul (hu τ)) ht']

theorem moeb_meas (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q) :
    MeasurableSet (moebBall q u '' S) ∧ ballMeas q (moebBall q u '' S) = ballMeas q S := by
  obtain ⟨h1, h2, G, h3, h4⟩ := GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q u hu
  exact ⟨hS.image_of_continuousOn_injOn (h1.continuousOn.mono hSD) ((moeb_injOn q hu).mono hSD),
    ballMeas_image q h1 h2 (moeb_injOn q hu) (fun t ht => ballDens_transform q h1 h3 h2 h4 ht) hS hSD⟩

def ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (q'.symm.trans q)

theorem ren_apply (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (x : Ψ × Fin j × Fin j') :
    ren q q' t (q x) = t (q' x) := by
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ) (q'.symm.trans q) t (q' x)
  simpa [ren] using this

theorem ballMat_ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ballMat q (ren q q' t) = ballMat q' t := by
  funext τ
  ext a b
  simp [ballMat, ren_apply]

theorem ren_mem (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ren q q' t ∈ ballDom q ↔ t ∈ ballDom q' := by
  simp only [ballDom, Set.mem_setOf_eq, ballMat_ren]

theorem moeb_ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (t : Fin n → ℂ) :
    moebBall q u (ren q q' t) = ren q q' (moebBall q' u t) := by
  funext k
  obtain ⟨x, rfl⟩ := q.surjective k
  rw [ren_apply]
  simp [moebBall, ballPt, ballMat_ren]

theorem ren_meas (q q' : Ψ × Fin j × Fin j' ≃ Fin n) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q') :
    ballMeas q (ren q q' '' S) = ballMeas q' S := by
  have hm : MeasurePreserving (ren q q') volume volume := volume_measurePreserving_piCongrLeft (fun _ => ℂ) _
  rw [ballMeas_apply q ((ren q q').measurableSet_image.2 hS) (by rintro _ ⟨t, ht, rfl⟩; exact (ren_mem q q' t).2 (hSD ht)),
    ballMeas_apply q' hS hSD, ← hm.setLIntegral_comp_emb (ren q q').measurableEmbedding]
  simp only [ballDens, ballPot, ballMat_ren]

theorem core (q : Ψ × Fin j × Fin j' ≃ Fin n) {G : Type} [Group G] [Countable G]
    (ρ : G → Ψ → Matrix (Sg j j') (Sg j j') ℂ) (U Γ Γ' : Subgroup G) (S S' : Set (Fin n → ℂ)) (h1 : ∀ τ, ρ 1 τ = 1)
    (hm : ∀ x y τ, ρ (x * y) τ = ρ x τ * ρ y τ) (hU : ∀ γ ∈ U, ∀ τ, IsSgU (ρ γ τ)) (hΓ : Γ ≤ U) (hΓ' : Γ' ≤ U)
    (hI : EqIdx Γ Γ') (hS : MFund q ρ Γ S) (hS' : MFund q ρ Γ' S') : ballMeas q S = ballMeas q S' := by
  have hD : MeasurableSet (ballDom q) := (BallInverse.isOpen_ballDom q).measurableSet
  have hemb : MeasurableEmbedding (Subtype.val : ballDom q → Fin n → ℂ) := MeasurableEmbedding.subtype_coe hD
  letI act : MulAction U (ballDom q) :=
    { smul := fun γ t => ⟨moebBall q (ρ γ) t, moeb_maps q (hU γ γ.2) t.2⟩
      one_smul := fun t => Subtype.ext (by
        show moebBall q (ρ 1) t = t
        rw [funext h1, moeb_one])
      mul_smul := fun a b t => Subtype.ext
        (moeb_mul q (hU a a.2) (hU b b.2) (fun τ => (hm a b τ).symm) t.2).symm }
  have sm : ∀ (γ : U) (t : ballDom q), ((γ • t : ballDom q) : Fin n → ℂ) = moebBall q (ρ γ) t := fun _ _ => rfl
  haveI : MeasurableConstSMul U (ballDom q) := ⟨fun γ =>
    (Continuous.subtype_mk (continuousOn_iff_continuous_restrict.1
      (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q (ρ γ) (hU γ γ.2)).1.continuousOn) _).measurable⟩
  let μ : Measure (ballDom q) := (ballMeas q).comap Subtype.val
  have hμ : ∀ s, μ s = ballMeas q (Subtype.val '' s) := fun s => hemb.comap_apply _ s
  haveI : SMulInvariantMeasure U (ballDom q) μ := ⟨fun γ s hs => by
    rw [hμ, hμ, ← (moeb_meas q (hU _ (γ⁻¹).2) (hemb.measurableSet_image.2 hs) (Subtype.coe_image_subset _ _)).2]
    congr 1
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨γ • x, hx, rfl⟩, by rw [← sm, inv_smul_smul]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨γ⁻¹ • x, by simpa using hx, rfl⟩⟩
  have fd : ∀ (Γ : Subgroup G) (S : Set (Fin n → ℂ)), Γ ≤ U → MFund q ρ Γ S →
      IsFundamentalDomain (Γ.subgroupOf U) (Subtype.val ⁻¹' S : Set (ballDom q)) μ ∧
        μ (Subtype.val ⁻¹' S) = ballMeas q S := fun Γ S hΓ ⟨a1, a2, a3, a4⟩ => by
    refine ⟨IsFundamentalDomain.mk' (hemb.measurable a1).nullMeasurableSet fun x => ?_, ?_⟩
    · obtain ⟨γ, hγ, h⟩ := a3 x x.2
      refine ⟨⟨⟨γ, hΓ hγ⟩, hγ⟩, h, fun g hg => ?_⟩
      have e : (g.1 * (⟨γ, hΓ hγ⟩ : U)⁻¹) • ((⟨γ, hΓ hγ⟩ : U) • x) = g.1 • x := by
        rw [← mul_smul, inv_mul_cancel_right]
      have := a4 _ h (g.1.1 * γ⁻¹) (Γ.mul_mem g.2 (Γ.inv_mem hγ)) (by
        have e' := congrArg Subtype.val e
        rw [sm, sm, sm] at e'
        exact e' ▸ hg)
      exact Subtype.ext (Subtype.ext (mul_inv_eq_one.1 this))
    · rw [hμ, Subtype.image_preimage_coe, Set.inter_eq_right.2 a2]
  obtain ⟨a₁, b₁⟩ := fd Γ S hΓ hS
  obtain ⟨a₂, b₂⟩ := fd Γ' S' hΓ' hS'
  rw [← b₁, ← b₂]
  exact fdEqual _ _ μ _ _ _ _
    (by rw [Subgroup.relIndex_subgroupOf hΓ, Subgroup.relIndex_subgroupOf hΓ']; exact hI.1)
    (by rw [Subgroup.relIndex_subgroupOf hΓ']; exact hI.2) a₁ a₂

end Moeb

open Moeb

theorem moebVol : MoebVol := by
  intro Ψ _ j j' n q q' G _ _ ρ ρ' w U Γ Γ' a S S' h1 hm hU hU' hw hc hΓ hΓ' hI hS ⟨b1, b2, b3, b4⟩
  have r1 : MeasurableSet (ren q q' '' S') := (ren q q').measurableSet_image.2 b1
  have r2 : ren q q' '' S' ⊆ ballDom q := by
    rintro _ ⟨t, ht, rfl⟩
    exact (ren_mem q q' t).2 (b2 ht)
  obtain ⟨m1, m2⟩ := moeb_meas q hw r1 r2
  have key : ∀ γ ∈ Γ', ∀ t ∈ ballDom q', moebBall q (ρ (a * γ * a⁻¹)) (moebBall q w (ren q q' t)) =
      moebBall q w (ren q q' (moebBall q' (ρ' γ) t)) := fun γ hγ t ht => by
    have ht' := (ren_mem q q' t).2 ht
    rw [← moeb_ren, moeb_mul q (hU (a * γ * a⁻¹) (hΓ' ⟨γ, hγ, rfl⟩)) hw (fun _ => rfl) ht',
      moeb_mul q hw (hU' γ hγ) (hc γ) ht']
  rw [← ren_meas q q' b1 b2, ← m2]
  refine core q ρ U Γ _ S _ h1 hm hU hΓ hΓ' hI hS ⟨m1, ?_, fun t ht => ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact moeb_maps q hw (r2 ht)
  · have hi := fun τ => sinv_su (hw τ)
    obtain ⟨s, hs⟩ := (ren q q').surjective (moebBall q (fun τ => sinv (w τ)) t)
    have hs' : s ∈ ballDom q' := (ren_mem q q' s).1 (hs ▸ moeb_maps q hi ht)
    obtain ⟨γ, hγ, h⟩ := b3 s hs'
    refine ⟨a * γ * a⁻¹, ⟨γ, hγ, rfl⟩, _, ⟨_, h, rfl⟩, ?_⟩
    rw [← key γ hγ s hs', hs, moeb_inv q hw hi (fun τ => mul_sinv (hw τ)) ht]
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ _ ⟨γ, hγ, rfl⟩ ⟨_, ⟨s, hs, rfl⟩, e⟩
    replace e : moebBall q w (ren q q' s) = moebBall q (ρ (a * γ * a⁻¹)) (moebBall q w (ren q q' t)) := e
    rw [key γ hγ t (b2 ht)] at e
    have e2 := (ren q q').injective (moeb_injOn q hw ((ren_mem q q' _).2 (b2 hs))
      ((ren_mem q q' _).2 (moeb_maps q' (hU' γ hγ) (b2 ht))) e)
    obtain rfl := b4 t ht γ hγ (e2 ▸ hs)
    exact map_one _

end SheetDecomposition
end
end
