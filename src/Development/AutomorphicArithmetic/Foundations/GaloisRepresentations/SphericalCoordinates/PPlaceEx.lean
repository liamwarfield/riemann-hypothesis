module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsRealPeriodIsoOfPolarizedLattice
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceComplexStructurePlaces
public import Development.AutomorphicArithmetic.CommutativeAlgebra.PositivityIffGramPosDef

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsRationalEquivOfRank
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEquivOfFinrank
open NumberField in
private theorem ext_hom {F : Type} [Field F] [NumberField F] {A : Type} [Ring A] [Algebra ℚ A]
    (φ : RingOfIntegers F →+* A) :
    ∃ ψ : F →+* A, ∀ c : RingOfIntegers F, ψ (algebraMap _ F c) = φ c := by
  haveI : Algebra.IsPushout ℤ (RingOfIntegers F) ℚ F :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors ℤ) ℚ (RingOfIntegers F) F
  refine ⟨(Algebra.pushoutDesc F φ.toIntAlgHom (algebraMap ℚ A).toIntAlgHom
    (fun x y => (Algebra.commutes y (φ x)).symm)).toRingHom, fun c => ?_⟩
  exact Algebra.pushoutDesc_left F _ _ _ c

private theorem tower {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V]
    [Module ℚ V] (ψ : F →+* Module.End ℚ V) :
    letI : Module F V := Module.compHom V ψ
    IsScalarTower ℚ F V := by
  letI : Module F V := Module.compHom V ψ
  refine ⟨fun q a v => ?_⟩
  change ψ (q • a) v = q • ψ a v
  rw [map_rat_smul ψ q a]
  rfl

theorem UpperTheory.Reformulated.B.ExistsEquivOfFinrank.exists_equiv_of_finrank :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    {V V' : Type} [inst_2 : AddCommGroup V] [inst_3 : _root_.Module ℚ V] [FiniteDimensional ℚ V]
    [inst_5 : AddCommGroup V'] [inst_6 : _root_.Module ℚ V'] [FiniteDimensional ℚ V']
    (φ : NumberField.RingOfIntegers F →+* Module.End ℚ V) (φ' : NumberField.RingOfIntegers F →+* Module.End ℚ V'),
    Module.finrank ℚ V = Module.finrank ℚ V' →
      ∃ (e : V ≃ₗ[ℚ] V'),
        ∀ (c : NumberField.RingOfIntegers F) (v : V),
          (e : V → V') (((φ : NumberField.RingOfIntegers F → Module.End ℚ V) c : V → V) v) =
            ((φ' : NumberField.RingOfIntegers F → Module.End ℚ V') c : V' → V') ((e : V → V') v) := by
  intro F _ _ V V' _ _ _ _ _ _ φ φ' h
  obtain ⟨ψ, hψ⟩ := ext_hom φ
  obtain ⟨ψ', hψ'⟩ := ext_hom φ'
  letI : Module F V := Module.compHom V ψ
  letI : Module F V' := Module.compHom V' ψ'
  haveI := tower ψ
  haveI := tower ψ'
  haveI : Module.Finite F V := Module.Finite.of_restrictScalars_finite ℚ F V
  haveI : Module.Finite F V' := Module.Finite.of_restrictScalars_finite ℚ F V'
  have h2 : Module.finrank F V = Module.finrank F V' := by
    rw [← Module.finrank_mul_finrank ℚ F V, ← Module.finrank_mul_finrank ℚ F V'] at h
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h
  let e : V ≃ₗ[F] V' := LinearEquiv.ofFinrankEq V V' h2
  refine ⟨e.restrictScalars ℚ, fun c v => ?_⟩
  rw [← hψ, ← hψ']
  exact e.map_smul (algebraMap _ F c) v
end

open NumberField GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.PELU GlobalTheory.UPel.HT
open scoped Matrix TensorProduct Classical

private theorem exists_equiv_of_finrank {F : Type} [Field F] [NumberField F] {V V' : Type}
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup V'] [Module ℚ V'] [FiniteDimensional ℚ V']
    (φ : 𝓞 F →+* Module.End ℚ V) (φ' : 𝓞 F →+* Module.End ℚ V')
    (h : Module.finrank ℚ V = Module.finrank ℚ V') :
    ∃ e : V ≃ₗ[ℚ] V', ∀ (c : 𝓞 F) (v : V), e (φ c v) = φ' c (e v) :=
  _root_.UpperTheory.Reformulated.B.ExistsEquivOfFinrank.exists_equiv_of_finrank φ φ' h

private def repOn {O M : Type} [Ring O] [AddCommGroup M] [Module O M] :
    O →+* Module.End ℚ (ℚ ⊗[ℤ] M) :=
  ((Module.End.baseChangeHom ℤ ℚ M).toRingHom).comp (Module.toModuleEnd ℤ M)

theorem UpperTheory.exists_rational_equiv_of_rank :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (Y : PLat D.O D.inv), Function.Surjective (algebraMap (𝓞 D.F) D.O) → Module.finrank ℤ Y.La = Module.finrank ℤ D.La → ∃ e : (ℚ ⊗[ℤ] Y.La) ≃ₗ[ℚ] VQ D, ∀ (c : D.O) (u : ℚ ⊗[ℤ] Y.La), e ((DistribSMul.toLinearMap ℤ Y.La c).baseChange ℚ u) = actQ D c (e u) := by
  intro p _ D Y hs hr
  haveI := D.freeLa
  haveI := D.finLa
  have hfin : Module.finrank ℚ (ℚ ⊗[ℤ] Y.La) = Module.finrank ℚ (VQ D) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, hr]
  obtain ⟨e, he⟩ := exists_equiv_of_finrank (F := D.F)
    ((repOn (O := D.O) (M := Y.La)).comp (algebraMap (𝓞 D.F) D.O))
    ((repOn (O := D.O) (M := D.La)).comp (algebraMap (𝓞 D.F) D.O)) hfin
  refine ⟨e, fun c u => ?_⟩
  obtain ⟨c, rfl⟩ := hs c
  exact he c u
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.HermitianCongruentAndPositiveEigenvectorOfSignat
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem form_re_eq {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (H *ᵥ x)).re = ∑ i, hH.eigenvalues i *
      Complex.normSq ((star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hspec : H = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have h0 := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h0
  have hsy : star (star U *ᵥ x) = star x ᵥ* U := by
    rw [star_mulVec, ← star_eq_conjTranspose, star_star]
  have hL : star x ⬝ᵥ (H *ᵥ x) =
      star (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
    rw [hsy, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← hspec]
  rw [hL, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mulVec_diagonal]
  simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  simp [Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem finrank_le_of_coord {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (p : Fin n → Prop)
    [Fintype {i // p i}] (W : Submodule ℂ (Fin n → ℂ)) (h : ∀ x ∈ W, (∀ i, p i → (U *ᵥ x) i = 0) → x = 0) :
    Module.finrank ℂ W ≤ Fintype.card {i // p i} := by
  let f : W →ₗ[ℂ] ({i // p i} → ℂ) :=
    { toFun := fun x i => (U *ᵥ (x : Fin n → ℂ)) i.1
      map_add' := fun x y => by
        ext i
        simp [mulVec_add]
      map_smul' := fun c x => by
        ext i
        simp [mulVec_smul] }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    apply h x x.2
    intro i hi
    exact congrFun hx ⟨i, hi⟩
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi] at h1

private theorem sig_eq_finrank {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (A B : Submodule ℂ (Fin n → ℂ)) (hAB : Module.finrank ℂ A + Module.finrank ℂ B = n)
    (hA : ∀ x ∈ A, x ≠ 0 → 0 < (star x ⬝ᵥ (H *ᵥ x)).re)
    (hB : ∀ x ∈ B, x ≠ 0 → (star x ⬝ᵥ (H *ᵥ x)).re < 0) :
    sigPosH hH = Module.finrank ℂ A := by
  set U : Matrix (Fin n) (Fin n) ℂ := star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hA' : Module.finrank ℂ A ≤ Fintype.card {i // 0 < hH.eigenvalues i} := by
    apply finrank_le_of_coord U (fun i => 0 < hH.eigenvalues i) A
    intro x hx hz
    by_contra hne
    have h1 := hA x hx hne
    rw [form_re_eq hH x] at h1
    have h2 : ∑ i, hH.eigenvalues i * Complex.normSq ((U *ᵥ x) i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      by_cases hi : 0 < hH.eigenvalues i
      · rw [hz i hi]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hi) (Complex.normSq_nonneg _)
    linarith
  have hB' : Module.finrank ℂ B ≤ Fintype.card {i // ¬ 0 < hH.eigenvalues i} := by
    apply finrank_le_of_coord U (fun i => ¬ 0 < hH.eigenvalues i) B
    intro x hx hz
    by_contra hne
    have h1 := hB x hx hne
    rw [form_re_eq hH x] at h1
    have h2 : 0 ≤ ∑ i, hH.eigenvalues i * Complex.normSq ((U *ᵥ x) i) := by
      apply Finset.sum_nonneg
      intro i _
      by_cases hi : 0 < hH.eigenvalues i
      · exact mul_nonneg hi.le (Complex.normSq_nonneg _)
      · rw [hz i hi]
        simp
    linarith
  have hc : Fintype.card {i // ¬ 0 < hH.eigenvalues i} =
      n - Fintype.card {i // 0 < hH.eigenvalues i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
  have hle : Fintype.card {i // 0 < hH.eigenvalues i} ≤ n := by
    simpa using Fintype.card_subtype_le (fun i => 0 < hH.eigenvalues i)
  have hs : sigPosH hH = Fintype.card {i // 0 < hH.eigenvalues i} := by
    unfold sigPosH
    exact Fintype.card_congr' rfl
  rw [hs]
  omega

theorem UpperTheory.hermitian_congruent_and_positive_eigenvector_of_signature :
    ∀ (n δ : ℕ) (H K J : Matrix (Fin n) (Fin n) ℂ) (e : ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian), (e = Complex.I ∨ e = -Complex.I) → J * J = -1 → ((-e) • (H * J)).PosDef → Matrix.trace J = e * (2 * (δ : ℂ) - (n : ℂ)) → K.det ≠ 0 → sigPosH hK = δ → (∃ Z : GL (Fin n) ℂ, H = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * K * (Z : Matrix (Fin n) (Fin n) ℂ)) ∧ (0 < δ → ∃ z : Fin n → ℂ, J *ᵥ z = e • z ∧ 0 < (star z ⬝ᵥ (H *ᵥ z)).re) := by
  intro n δ H K J e hH hK he hJJ hM htr hKdet hKsig
  have he2 : e * e = -1 := by
    rcases he with rfl | rfl <;> simp
  set E : Matrix (Fin n) (Fin n) ℂ := e • J with hEdef
  have hEE : E * E = 1 := by
    rw [hEdef, smul_mul_smul_comm, he2, hJJ, neg_smul, smul_neg, one_smul, neg_neg]
  have hJE : J = (-e) • E := by
    rw [hEdef, smul_smul, neg_mul, he2, neg_neg, one_smul]
  set P : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (1 - E) with hPdef
  have h2 : (1 - E) * (1 - E) = (2 : ℂ) • (1 - E) := by
    rw [sub_mul, mul_sub, mul_sub, _root_.one_mul, _root_.mul_one, _root_.one_mul, hEE, two_smul]
    abel
  have hPP : P * P = P := by
    rw [hPdef, smul_mul_smul_comm, h2, smul_smul]
    norm_num
  have hEP : E * P = -P := by
    rw [hPdef, Matrix.mul_smul, mul_sub, _root_.mul_one, hEE, ← smul_neg, neg_sub]
  set f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Matrix.toLin' P with hfdef
  have hidem : IsIdempotentElem f := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hPP]
  have hJrange : ∀ x ∈ LinearMap.range f, J *ᵥ x = e • x := by
    rintro x ⟨y, rfl⟩
    rw [hfdef, Matrix.toLin'_apply, hJE, smul_mulVec, mulVec_mulVec, hEP, neg_mulVec,
      smul_neg, ← neg_smul, neg_neg]
  have hJker : ∀ x ∈ LinearMap.ker f, J *ᵥ x = (-e) • x := by
    intro x hx
    rw [LinearMap.mem_ker, hfdef, Matrix.toLin'_apply, hPdef, smul_mulVec, sub_mulVec,
      one_mulVec, smul_eq_zero] at hx
    have hx' : x = E *ᵥ x := by
      rcases hx with h | h
      · norm_num at h
      · exact (sub_eq_zero.1 h)
    rw [hJE, smul_mulVec, ← hx']
  have hform : ∀ x c, J *ᵥ x = c • x → ((-e) • (H * J)) *ᵥ x = ((-e) * c) • (H *ᵥ x) := by
    intro x c hx
    rw [smul_mulVec, ← mulVec_mulVec, hx, mulVec_smul, smul_smul]
  have hApos : ∀ x ∈ LinearMap.range f, x ≠ 0 → 0 < (star x ⬝ᵥ (H *ᵥ x)).re := by
    intro x hx hx0
    have h0 := hM.re_dotProduct_pos hx0
    rw [hform x e (hJrange x hx), neg_mul, he2, neg_neg, one_smul] at h0
    simpa using h0
  have hBneg : ∀ x ∈ LinearMap.ker f, x ≠ 0 → (star x ⬝ᵥ (H *ᵥ x)).re < 0 := by
    intro x hx hx0
    have h0 := hM.re_dotProduct_pos hx0
    rw [hform x (-e) (hJker x hx), neg_mul_neg, he2, neg_one_smul, dotProduct_neg] at h0
    have h1 : 0 < -(star x ⬝ᵥ (H *ᵥ x)).re := by simpa using h0
    linarith
  have hAB : Module.finrank ℂ (LinearMap.range f) + Module.finrank ℂ (LinearMap.ker f) = n := by
    rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]
  have htrP : P.trace = (δ : ℂ) := by
    rw [hPdef, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, hEdef, Matrix.trace_smul, htr,
      Fintype.card_fin, smul_eq_mul, smul_eq_mul]
    linear_combination (-(2 * (δ : ℂ) - (n : ℂ)) / 2) * he2
  have hrank : Module.finrank ℂ (LinearMap.range f) = δ := by
    have h0 := (LinearMap.IsIdempotentElem.isProj_range f hidem).trace
    rw [hfdef, Matrix.trace_toLin'_eq, htrP] at h0
    exact_mod_cast h0.symm
  have hsig : sigPosH hH = δ := by
    rw [sig_eq_finrank hH _ _ hAB hApos hBneg, hrank]
  have hHdet : H.det ≠ 0 := by
    intro h0
    have hd := hM.det_pos
    rw [Matrix.det_smul, Matrix.det_mul, h0, zero_mul, mul_zero] at hd
    exact lt_irrefl _ hd
  refine ⟨?_, ?_⟩
  · obtain ⟨Z, hZ⟩ := HermCongruence.congr_of_sigPosH_eq K H hK hH hKdet hHdet (by rw [hKsig, hsig])
    exact ⟨Z, hZ⟩
  · intro hδ
    have hpos : 0 < Module.finrank ℂ (LinearMap.range f) := hrank ▸ hδ
    obtain ⟨⟨z, hzA⟩, hz0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
    have hz0' : z ≠ 0 := fun h => hz0 (Subtype.ext h)
    exact ⟨z, hJrange z hzA, hApos z hzA hz0'⟩
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUnitaryUnitHermitianFormOfCmLattice
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem exists_den {Λ : Type} [AddCommGroup Λ] (t : ℚ ⊗[ℤ] Λ) :
    ∃ (n : ℤ) (z : Λ), n ≠ 0 ∧ n • t = (1 : ℚ) ⊗ₜ[ℤ] z := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q z =>
    refine ⟨(q.den : ℤ), q.num • z, by exact_mod_cast q.den_nz, ?_⟩
    have h : ((q.den : ℤ)) • q = q.num • (1 : ℚ) := by
      rw [zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast, _root_.mul_one]
      exact Rat.den_mul_eq_num q
    rw [TensorProduct.smul_tmul', h, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨n, z, hn, h⟩ := ha
    obtain ⟨m, w, hm, h'⟩ := hb
    refine ⟨n * m, m • z + n • w, mul_ne_zero hn hm, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← h, ← h',
      smul_smul, smul_smul, mul_comm m n]

private theorem sep_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0) (a : ℚ ⊗[ℤ] Λ) (h : ∀ w, B.baseChange ℚ a w = 0) : a = 0 := by
  obtain ⟨n, z, hn, e⟩ := exists_den a
  have hz : z = 0 := by
    apply hB
    intro w
    have h2 : B.baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] z) ((1 : ℚ) ⊗ₜ[ℤ] w) = 0 := by
      rw [← e, map_zsmul, LinearMap.smul_apply, h, smul_zero]
    simpa [LinearMap.BilinForm.baseChange_tmul] using h2
  rw [hz, TensorProduct.tmul_zero] at e
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [← Int.cast_smul_eq_zsmul ℚ] at e
  exact (smul_eq_zero.1 e).resolve_left hn'

private theorem adj_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (f g : Λ →ₗ[ℤ] Λ)
    (h : ∀ x y, B (f x) y = B x (g y)) (u w : ℚ ⊗[ℤ] Λ) :
    B.baseChange ℚ (f.baseChange ℚ u) w = B.baseChange ℚ u (g.baseChange ℚ w) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r y => simp [LinearMap.BilinForm.baseChange_tmul, h]

private theorem anti_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (h : ∀ x, B x x = 0)
    (u w : ℚ ⊗[ℤ] Λ) : B.baseChange ℚ u w = - B.baseChange ℚ w u := by
  have anti : ∀ x y, B x y = - B y x := fun x y => by
    have := h (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, h, zero_add, add_zero] at this
    linarith
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
    | tmul r y =>
      simp only [LinearMap.BilinForm.baseChange_tmul]
      rw [anti x y]
      rw [mul_comm q r, neg_smul]

private theorem exists_rep {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (E F : LinearMap.BilinForm ℚ V) (hE : ∀ a, (∀ w, E a w = 0) → a = 0) :
    ∃ b : Module.End ℚ V, ∀ u w, F u w = 2 * E (b u) w := by
  have inj : Function.Injective (E : V →ₗ[ℚ] Module.Dual ℚ V) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    exact hE a fun w => by rw [ha]; rfl
  let Φ : V ≃ₗ[ℚ] Module.Dual ℚ V :=
    LinearMap.linearEquivOfInjective (E : V →ₗ[ℚ] Module.Dual ℚ V) inj (Subspace.dual_finrank_eq).symm
  refine ⟨(1 / 2 : ℚ) • (Φ.symm.toLinearMap ∘ₗ (F : V →ₗ[ℚ] Module.Dual ℚ V)), fun u w => ?_⟩
  have h : E (Φ.symm (F u)) = F u := Φ.apply_symm_apply (F u)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul, h, smul_eq_mul]
  ring

theorem UpperTheory.exists_unitary_unit_hermitian_form_of_cm_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (Y : PLat D.O D.inv) (j : (ℚ ⊗[ℤ] Y.La) ≃ₗ[ℚ] VQ D), (∀ (c : D.O) (u : ℚ ⊗[ℤ] Y.La), j ((DistribSMul.toLinearMap ℤ Y.La c).baseChange ℚ u) = actQ D c (j u)) → ∃ β : G.Cˣ, sh G β = β ∧ ∀ u w : ℚ ⊗[ℤ] Y.La, Y.EF.baseChange ℚ u w = 2 * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (j u)) (j w) := by
  intro p _ D G L Y j hj
  haveI := D.finLa
  set E := D.EF.baseChange ℚ with hEdef
  have sepE : ∀ a, (∀ w, E a w = 0) → a = 0 := fun a h =>
    sep_bc D.EF (fun x hx => D.nondeg (by rw [map_zero]; ext y; simpa using hx y)) a h
  have sepY : ∀ a, (∀ w, Y.EF.baseChange ℚ a w = 0) → a = 0 := fun a h => sep_bc Y.EF Y.nondeg a h
  have eqE : ∀ a a', (∀ w, E a w = E a' w) → a = a' := fun a a' h => by
    rw [← sub_eq_zero]
    exact sepE _ fun w => by rw [map_sub, LinearMap.sub_apply, h, sub_self]
  let F : LinearMap.BilinForm ℚ (VQ D) :=
    ((Y.EF.baseChange ℚ).compl₁₂ j.symm.toLinearMap j.symm.toLinearMap)
  have hF : ∀ u w, F u w = Y.EF.baseChange ℚ (j.symm u) (j.symm w) := fun u w => rfl
  obtain ⟨b, hb⟩ := exists_rep E F sepE
  have hinj : Function.Injective b := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    have : j.symm u = 0 := sepY _ fun w => by
      have h := hb u (j w)
      rw [hu, map_zero, LinearMap.zero_apply, MulZeroClass.mul_zero, hF, j.symm_apply_apply] at h
      exact h
    simpa using this
  have comm : ∀ c : D.O, b * actQ D c = actQ D c * b := by
    intro c
    refine LinearMap.ext fun u => eqE _ _ fun w => ?_
    have hc : j.symm (actQ D c u) = (DistribSMul.toLinearMap ℤ Y.La c).baseChange ℚ (j.symm u) := by
      rw [LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]
    have hc' : ∀ w, j.symm (actQ D (D.inv c) w) = (DistribSMul.toLinearMap ℤ Y.La (D.inv c)).baseChange ℚ (j.symm w) := fun w => by
      rw [LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]
    have h1 : F (actQ D c u) w = F u (actQ D (D.inv c) w) := by
      rw [hF, hF, hc, hc']
      exact adj_bc Y.EF _ _ (fun x y => Y.adj c x y) _ _
    have h2 : E (actQ D c (b u)) w = E (b u) (actQ D (D.inv c) w) :=
      adj_bc D.EF _ _ (fun x y => D.adj c x y) _ _
    have h3 := hb (actQ D c u) w
    have h4 := hb u (actQ D (D.inv c) w)
    simp only [Module.End.mul_apply]
    rw [h2]
    linarith
  have hsym : ∀ u w, E (b u) w = E u (b w) := by
    intro u w
    have h1 := hb u w
    have h2 := hb w u
    have h3 : F u w = - F w u := by
      rw [hF, hF]
      exact anti_bc Y.EF Y.alt _ _
    have h4 : E (b w) u = - E u (b w) := anti_bc D.EF D.alt _ _
    linarith
  obtain ⟨b₀, hb₀⟩ : ∃ x : G.C, L.rep x = b := (L.rep_range b).2 comm
  let e : VQ D ≃ₗ[ℚ] VQ D := LinearEquiv.ofInjectiveEndo b hinj
  have he : ∀ u, b (e.symm u) = u := fun u => e.apply_symm_apply u
  have he' : ∀ u, e.symm (b u) = u := fun u => e.symm_apply_apply u
  have comm' : ∀ c : D.O, (e.symm.toLinearMap : Module.End ℚ (VQ D)) * actQ D c = actQ D c * e.symm.toLinearMap := by
    intro c
    refine LinearMap.ext fun u => hinj ?_
    have h := LinearMap.congr_fun (comm c) (e.symm u)
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe, he] at h ⊢
    exact h.symm
  obtain ⟨b₁, hb₁⟩ : ∃ x : G.C, L.rep x = e.symm.toLinearMap :=
    (L.rep_range e.symm.toLinearMap).2 comm'
  have h01 : b₀ * b₁ = 1 := by
    apply L.rep_inj
    rw [map_mul, map_one, hb₀, hb₁]
    exact LinearMap.ext fun u => he u
  have h10 : b₁ * b₀ = 1 := by
    apply L.rep_inj
    rw [map_mul, map_one, hb₀, hb₁]
    exact LinearMap.ext fun u => he' u
  have hadj : ∀ x v w, E (L.rep x v) w = E v (L.rep (sh G x) w) := L.adj
  have shsh : sh G (sh G b₀) = b₀ := G.star_star b₀
  have shmul : ∀ x y, sh G (x * y) = sh G y * sh G x := fun x y => by
    unfold sh
    rw [map_mul, MulOpposite.unop_mul]
  have shone : sh G 1 = 1 := by
    unfold sh
    rw [map_one, MulOpposite.unop_one]
  have hs : sh G b₀ = b₀ := by
    apply L.rep_inj
    refine LinearMap.ext fun u => eqE _ _ fun w => ?_
    rw [hadj, shsh, hb₀, hsym]
  have hs1 : sh G b₁ = b₁ := by
    have h : sh G b₁ * b₀ = 1 := by
      have h' := shmul b₀ b₁
      rw [h01, shone, hs] at h'
      exact h'.symm
    calc sh G b₁ = sh G b₁ * (b₀ * b₁) := by rw [h01, _root_.mul_one]
      _ = (sh G b₁ * b₀) * b₁ := (_root_.mul_assoc _ _ _).symm
      _ = b₁ := by rw [h, _root_.one_mul]
  refine ⟨⟨b₁, b₀, h10, h01⟩, hs1, fun u w => ?_⟩
  have h := hb (j u) (j w)
  rw [hF, j.symm_apply_apply, j.symm_apply_apply] at h
  rw [h]
  show _ = 2 * E (L.rep b₀ (j u)) (j w)
  rw [hb₀]
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private def repOnLocal {O M : Type} [Ring O] [AddCommGroup M] [Module O M] :
    O →+* Module.End ℚ (ℚ ⊗[ℤ] M) :=
  ((Module.End.baseChangeHom ℤ ℚ M).toRingHom).comp (Module.toModuleEnd ℤ M)

private theorem rational_equiv_local (p : ℕ) [Fact p.Prime] (D : Datum p)
    (Y : PLat D.O D.inv) (hs : Function.Surjective (algebraMap (𝓞 D.F) D.O))
    (hr : Module.finrank ℤ Y.La = Module.finrank ℤ D.La) :
    ∃ e : (ℚ ⊗[ℤ] Y.La) ≃ₗ[ℚ] VQ D,
      ∀ (c : D.O) (u : ℚ ⊗[ℤ] Y.La),
        e ((DistribSMul.toLinearMap ℤ Y.La c).baseChange ℚ u) = actQ D c (e u) := by
  haveI := D.freeLa
  haveI := D.finLa
  have hfin : Module.finrank ℚ (ℚ ⊗[ℤ] Y.La) = Module.finrank ℚ (VQ D) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, hr]
  obtain ⟨e, he⟩ := UpperTheory.Reformulated.B.ExistsEquivOfFinrank.exists_equiv_of_finrank
    ((repOnLocal (O := D.O) (M := Y.La)).comp (algebraMap (𝓞 D.F) D.O))
    ((repOnLocal (O := D.O) (M := D.La)).comp (algebraMap (𝓞 D.F) D.O)) hfin
  refine ⟨e, fun c u => ?_⟩
  obtain ⟨c, rfl⟩ := hs c
  exact he c u

private theorem typeAt_of {p : ℕ} [Fact p.Prime] (D : Datum p) (ha : D.a = 1) (hm : D.m = 1) (t₀ : D.F →+* ℂ)
    (ht : ∀ i, D.tau i = t₀) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (h : IsSigD D ρ t₀) :
    UpperTheory.ComplexUniformization.TypeAt D ρ := by
  intro c
  have hs : IsSig (algebraMap (𝓞 D.F) D.O) D.inv ρ D.n t₀ (epsD D) := h
  have i0 : Fin D.a := ⟨0, by omega⟩
  have hω : t₀ (D.ω : D.F) = D.ρc := by
    rw [← ht i0]
    exact D.tau_ω i0
  have hre : D.ρc.im ≠ 0 := by
    intro him
    have hr := congrArg Complex.re D.ρc_root
    have hd : ((D.tr : ℝ)) ^ 2 - 4 * (D.nm : ℝ) < 0 := by exact_mod_cast D.disc_neg
    simp [pow_two, him] at hr
    nlinarith [sq_nonneg (2 * D.ρc.re - D.tr)]
  have hsω' : (starRingEnd ℂ) (t₀ (D.ω : D.F)) ≠ D.ρc := by
    rw [hω]
    intro e
    apply hre
    have e2 := congrArg Complex.im e
    simp at e2
    linarith
  have hsω : (ComplexEmbedding.conjugate t₀) (D.ω : D.F) ≠ D.ρc := by
    rwa [ComplexEmbedding.conjugate_coe_eq]
  have hne : t₀ ≠ ComplexEmbedding.conjugate t₀ := fun e => hs.cx t₀ e.symm
  rw [hs.tr c, hm]
  simp only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ha, one_smul, Nat.cast_one, _root_.one_mul]
  rw [Finset.sum_filter, ← ComplexEmbedding.conjugate_coe_eq]
  have key : ∀ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) =
      ((if τ = t₀ then τ (c : D.F) else 0) - (if τ = ComplexEmbedding.conjugate t₀ then τ (c : D.F) else 0)) +
        (if τ (D.ω : D.F) ≠ D.ρc then (D.n : ℂ) * τ (c : D.F) else 0) := by
    intro τ
    by_cases h1 : τ = t₀
    · subst h1
      simp [typeMult, hne, hω]
    by_cases h2 : τ = ComplexEmbedding.conjugate t₀
    · subst h2
      simp [typeMult, h1, hsω', Nat.cast_sub hs.pos]
      ring
    by_cases h3 : τ (D.ω : D.F) = D.ρc
    · simp [typeMult, h1, h2, h3, epsD]
    · simp [typeMult, h1, h2, h3, epsD]
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
  ring

private theorem tens_int (M : Type) [AddCommGroup M] (t : ℚ ⊗[ℤ] M) :
    ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • t = (1 : ℚ) ⊗ₜ[ℤ] u := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q u =>
    refine ⟨q.den, q.num • u, q.den_nz, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    rw [nsmul_eq_mul, zsmul_eq_mul, _root_.mul_one, _root_.mul_comm]
    exact Rat.mul_den_eq_num q
  | add a b ha hb =>
    obtain ⟨m, u, hm, hu⟩ := ha
    obtain ⟨n, w, hn, hw⟩ := hb
    refine ⟨m * n, n • u + m • w, Nat.mul_ne_zero hm hn, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hu, ← hw,
      mul_smul, smul_comm m n a, mul_smul]

private theorem tmul_inj (M : Type) [AddCommGroup M] [Module.Free ℤ M] :
    Function.Injective (fun u : M => (1 : ℚ) ⊗ₜ[ℤ] u) := by
  have hf : Function.Injective (Algebra.linearMap ℤ ℚ) := fun a b h => by
    simpa using h
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap ℤ ℚ) hf
  intro a b hab
  apply (TensorProduct.lid ℤ M).symm.injective
  apply h1
  simpa [TensorProduct.lid_symm_apply] using hab

private theorem rank_of_period {O : Type} [Ring O] {bar : O → O} {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (Y : PLat O bar) (P : Y.La →+ (Fin g → ℂ)) (hP : IsPeriod Y ρ P) : Module.finrank ℤ Y.La = 2 * g := by
  obtain ⟨-, hinj, hdisc, hspan, -⟩ := hP
  let f : Y.La →ₗ[ℤ] (Fin g → ℂ) := P.toIntLinearMap
  have hf : Function.Injective f := hinj
  have hset : ((LinearMap.range f : Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) = Set.range P := by
    ext x
    simp [f]
  haveI : DiscreteTopology (LinearMap.range f) := hdisc
  haveI : IsZLattice ℝ (LinearMap.range f) := ⟨by rw [hset]; exact hspan⟩
  rw [(LinearEquiv.ofInjective f hf).finrank_eq, ZLattice.rank ℝ (LinearMap.range f),
    Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

private theorem rank_datum {p : ℕ} [Fact p.Prime] (D : Datum p) (hm : D.m = 1) : Module.finrank ℤ D.La = 2 * D.g := by
  have hd := NumberField.IsTotallyComplex.finrank D.F
  rw [D.rankLa, Datum.g, hm, hd]
  rw [show 1 * D.n * (2 * NumberField.InfinitePlace.nrComplexPlaces D.F) =
      2 * (D.n * NumberField.InfinitePlace.nrComplexPlaces D.F) by ring, Nat.mul_div_cancel_left _ two_pos]

private theorem sh_mul' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

private theorem sh_one' {p : ℕ} [Fact p.Prime] (G : HTGroup p) : sh G (1 : G.C) = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

private theorem sh_inv_eq {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (h : sh G (β : G.C) = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have h1 : sh G ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by
    rw [← h, ← sh_mul', Units.mul_inv, sh_one']
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * ((β : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [Units.mul_inv, _root_.mul_one]
    _ = ((β⁻¹ : G.Cˣ) : G.C) := by rw [← _root_.mul_assoc, h1, _root_.one_mul]

private theorem herm_sym {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (x : G.C) (h : sh G x = x) :
    (G.gram v * G.psi v x).IsHermitian := by
  have e : G.psi v x = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := by
    have e0 := G.psi_star v x
    rw [show MulOpposite.unop (G.star x) = x from h] at e0
    exact e0
  have hu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, (G.gram_herm v).eq]
  conv_rhs => rw [e]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

private theorem sig_zero {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (ha : D.a = 1)
    (v v' : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (hne : v' ≠ v) : sigPosH (G.gram_herm v') = 0 := by
  rcases G.sig v' with h | h
  · exfalso
    obtain ⟨i, hi⟩ := (L.sig v').1 h.1
    obtain ⟨k, hk⟩ := (L.sig v).1 hv
    have hik : i = k := Fin.ext (by omega)
    subst hik
    exact hne (hi.trans hk.symm)
  · exact h.1

private theorem inv_rel {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β β' y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : (β' : G.C) = algebraMap ℚ G.C s * (y * β * sh G y)) :
    sh G y * ((β'⁻¹ : G.Cˣ) : G.C) * y = algebraMap ℚ G.C s⁻¹ * ((β⁻¹ : G.Cˣ) : G.C) := by
  have hy : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← sh_mul', Units.inv_mul, sh_one']
  have hc : algebraMap ℚ G.C s * algebraMap ℚ G.C s⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hs.ne', map_one]
  have hz : (β' : G.C) * (algebraMap ℚ G.C s⁻¹ *
      (sh G ((y⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C))) = 1 := by
    rw [hβ, _root_.mul_assoc, Algebra.left_comm, ← _root_.mul_assoc (algebraMap ℚ G.C s), hc, _root_.one_mul]
    simp only [_root_.mul_assoc]
    rw [← _root_.mul_assoc (sh G (y : G.C)), hy, _root_.one_mul, Units.mul_inv_cancel_left, Units.mul_inv]
  rw [Units.inv_eq_of_mul_eq_one_right hz, Algebra.left_comm, _root_.mul_assoc (algebraMap ℚ G.C s⁻¹)]
  congr 1
  simp only [_root_.mul_assoc]
  rw [Units.inv_mul, _root_.mul_one, ← _root_.mul_assoc, hy, _root_.one_mul]

private theorem place_move {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {β β' y : G.Cˣ} {s : ℚ}
    {D' : PLat D.O D.inv} {j : D'.La →+ VQ D} (h : IsPlace L β D' j) (hs : 0 < s)
    (hβ : (β' : G.C) = algebraMap ℚ G.C s * (y * β * sh G y)) :
    IsPlace L β' D' ((L.rep (y : G.C)).toAddMonoidHom.comp j) := by
  obtain ⟨hinj, hact, hspan, s0, hs0, hEF⟩ := h
  have hRRi : ∀ w, L.rep (y : G.C) (L.rep ((y⁻¹ : G.Cˣ) : G.C) w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]
  have hRiR : ∀ w, L.rep ((y⁻¹ : G.Cˣ) : G.C) (L.rep (y : G.C) w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
  have key : ∀ a b, formB L β' (L.rep (y : G.C) a) (L.rep (y : G.C) b) = s⁻¹ * formB L β a b := by
    intro a b
    unfold formB
    have hyy : (y : G.C) = sh G (sh G (y : G.C)) := (G.star_star _).symm
    conv_lhs => rw [hyy]
    rw [← L.adj, ← hyy, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      inv_rel G β β' y s hs hβ, map_mul, Module.End.mul_apply, AlgHom.commutes, Module.algebraMap_end_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ⟨s0 * s, mul_pos hs0 hs, fun u u' => ?_⟩⟩
  · intro a b hab
    apply hinj
    have e := congrArg (L.rep ((y⁻¹ : G.Cˣ) : G.C)) hab
    simpa [hRiR] using e
  · intro c u
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, hact]
    exact LinearMap.congr_fun ((L.rep_range _).1 ⟨_, rfl⟩ c) (j u)
  · intro w
    obtain ⟨m, u, hm, hu⟩ := hspan (L.rep ((y⁻¹ : G.Cˣ) : G.C) w)
    refine ⟨m, u, hm, ?_⟩
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ← hu]
    simp [hRRi]
  · simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [hEF, key, ← _root_.mul_assoc, _root_.mul_assoc s0, mul_inv_cancel₀ hs.ne', _root_.mul_one]

theorem UpperTheory.Gal.W2.placeEx_of :
    UpperTheory.Gal.W2.AdCore → UpperTheory.Gal.W2.LatForm → UpperTheory.Gal.W2.PlaceEx := by
  intro hAd _ p _ D G L ha hm v hv t₀ ht ρ hρ N D' t hcls hPe
  obtain ⟨P, hP⟩ := hPe
  haveI := D'.free
  haveI := D'.fin
  have hrk : Module.finrank ℤ D'.La = Module.finrank ℤ D.La := by
    rw [rank_of_period ρ D' P hP, rank_datum D hm]
  have hs : IsSig (algebraMap (𝓞 D.F) D.O) D.inv ρ D.n t₀ (epsD D) := hρ
  obtain ⟨e, he⟩ : ∃ e : (ℚ ⊗[ℤ] D'.La) ≃ₗ[ℚ] VQ D,
      ∀ (c : D.O) (u : ℚ ⊗[ℤ] D'.La),
        e ((DistribSMul.toLinearMap ℤ D'.La c).baseChange ℚ u) = actQ D c (e u) :=
    rational_equiv_local p D D' hs.onto hrk
  obtain ⟨β, hβs, hβf⟩ := UpperTheory.exists_unitary_unit_hermitian_form_of_cm_lattice p D G L D' e he
  let j : D'.La →+ VQ D := e.toAddEquiv.toAddMonoidHom.comp (TensorProduct.mk ℤ ℚ D'.La 1).toAddMonoidHom
  have hj : ∀ u, j u = e (1 ⊗ₜ u) := fun u => rfl
  have hinj : Function.Injective j := e.injective.comp (tmul_inj D'.La)
  have hact : ∀ (c : D.O) (u : D'.La), j (c • u) = actQ D c (j u) := by
    intro c u
    rw [hj, hj, ← he c (1 ⊗ₜ u)]
    simp
  have hsp : ∀ w : VQ D, ∃ (m : ℕ) (u : D'.La), m ≠ 0 ∧ m • w = j u := by
    intro w
    obtain ⟨m, u, hm0, hmu⟩ := tens_int D'.La (e.symm w)
    refine ⟨m, u, hm0, ?_⟩
    rw [hj, ← hmu, map_nsmul, LinearEquiv.apply_symm_apply]
  have hform : ∀ z z' : D'.La, ((D'.EF z z' : ℤ) : ℚ) =
      2 * (LinearMap.BilinForm.baseChange ℚ D.EF) ((L.rep ((β⁻¹ : G.Cˣ) : G.C)) (j z)) (j z') := by
    intro z z'
    have h0 := hβf (1 ⊗ₜ z) (1 ⊗ₜ z')
    rw [hj, hj]
    simpa using h0
  have hplace : IsPlace L β D' j := by
    refine ⟨hinj, hact, ?_, ⟨2, two_pos, fun u u' => ?_⟩⟩
    · intro w
      obtain ⟨m, u, hm0, hmu⟩ := hsp w
      exact ⟨m, u, hm0, hmu⟩
    · rw [hform]
      rfl
  have hspan : Submodule.span ℚ (Set.range j) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨m, u, hm0, hmu⟩ := hsp w
    have hw : w = (m : ℚ)⁻¹ • j u := by
      rw [← hmu, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm0), one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)
  obtain ⟨Φ, Jc, hJ, hΦJ, hΦ, hstar, hpos⟩ := UpperTheory.exists_real_period_iso_of_polarized_lattice p D G L ρ D' P hP j hinj hspan hact β hform
  have hT := typeAt_of D ha hm t₀ ht ρ hρ
  have htr := UpperTheory.trace_complex_structure_places p D G L ρ v ha hT hv Φ Jc hJ hΦ hΦJ
  have hpd := (UpperTheory.positivity_iff_gram_posDef p D G L _ hstar).1 hpos
  have hpsiC : ∀ (v' : InfinitePlace G.F) (x : G.C), G.psiR v' (inC G ℝ x) = G.psi v' x := by
    intro v' x
    show G.psiR v' (1 ⊗ₜ x) = _
    rw [G.psiR_tmul, one_smul]
  have hR : ∃ z, Triv G ℝ (β : G.C) z 1 := by
    apply trivR_of_gram_psi_inv_congr p G β
    intro v'
    have hH := herm_sym G v' _ (sh_inv_eq G β hβs)
    have hJJ : G.psiR v' Jc * G.psiR v' Jc = -1 := by
      rw [← map_mul, hJ, map_neg, map_one]
    have hdelta : sigPosH (G.gram_herm v') = (if v' = v then 1 else 0) := by
      by_cases hvv : v' = v
      · subst hvv
        simpa using hv
      · rw [if_neg hvv]
        exact sig_zero L ha v v' hv hvv
    refine (UpperTheory.hermitian_congruent_and_positive_eigenvector_of_signature G.n (if v' = v then 1 else 0) (G.gram v' * G.psi v' ((β⁻¹ : G.Cˣ) : G.C))
      (G.gram v') (G.psiR v' Jc) (if v'.embedding (L.e D.ω) = D.ρc then Complex.I else -Complex.I) hH
      (G.gram_herm v') (by split_ifs <;> simp) hJJ ?_ ?_ (G.gram_det v') hdelta).1
    · have h1 := hpd v'
      rw [map_mul, hpsiC, ← Matrix.mul_assoc] at h1
      split_ifs at h1 ⊢ <;> simpa using h1
    · rw [htr v']
      split_ifs <;> simp
  obtain ⟨f, ν, -, hw1, hw2⟩ := hcls.1
  have hwit : IsWit D' f ν := by
    refine ⟨hw1, fun n hn hc => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := hw2 n hn hc
    refine ⟨a1, a2, a3, a4, fun a a' => ?_⟩
    have h5 := a5 a a'
    simp only [Datum.plat, LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at h5
    exact h5
  obtain ⟨x, c, htriv, -⟩ := hAd p D G L β D' j hplace f ν hwit
  let F : LKCx.Form G := ⟨β, hβs, ⟨x, c, htriv⟩, hR⟩
  obtain ⟨y, s, hs0, hys⟩ := (LKCx.Form.mk_eq_iff_rel p G F
    (Quot.out (Quot.mk LKCx.Form.Rel F : LKCx.FCls G))).1 (Quot.out_eq _).symm
  exact ⟨Quot.mk LKCx.Form.Rel F, _, place_move L hplace hs0 hys⟩
