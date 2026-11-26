module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.LocalFromCover

theorem trace_conj {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : (starRingEnd ℂ) Z.trace = -Z.trace := by
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ
  have hJ := GlobalTheory.RealPar.KStabLie.Jm_sq p q
  have h2 := congrArg (fun A => (A * Jm p q).trace) h
  simp only [add_mul, Matrix.trace_add, zero_mul, Matrix.trace_zero] at h2
  rw [mul_assoc, hJ, mul_one, Matrix.trace_mul_comm, ← mul_assoc, hJ, one_mul, Matrix.trace_conjTranspose] at h2
  exact eq_neg_of_add_eq_zero_left h2

theorem trace_reindex' {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) : (Matrix.reindex e e Z).trace = Z.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact e.symm.sum_comp fun a => Z a a

theorem exp_plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • plainMat e Z) = plainMat e (NormedSpace.exp (t • Z)) := by
  have h : t • plainMat e Z = Matrix.reindex e e (t • Z) := by
    ext a b; simp [plainMat]
  rw [h]
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) (t • Z)).symm

theorem exp_barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • barMat e Z) = barMat e (NormedSpace.exp (t • Z)) := by
  have h0 : ∀ A : Mat p q, A.map (starRingEnd ℂ) = Aᴴᵀ := fun A => by ext a b; simp
  have h1 := exp_plainMat e (Z.map (starRingEnd ℂ)) t
  have h2 : t • Z.map (starRingEnd ℂ) = (t • Z)ᴴᵀ := by ext a b; simp
  rw [h2, Matrix.exp_transpose, Matrix.exp_conjTranspose, ← h0] at h1
  exact h1

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)

theorem fr_toFrame (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : M.fr τ * toFrame M τ Y * (M.fr τ)⁻¹ = Y := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  rw [toFrame, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul, mul_assoc,
    Matrix.mul_nonsing_inv _ hd, mul_one]

theorem trace_toFrame (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : (toFrame M τ Y).trace = Y.trace := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  rw [toFrame, Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul]

theorem rep_exp (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    M.rep τ (NormedSpace.exp (t • toFrame M τ Y)) = M.σ τ (NormedSpace.exp (t • Y)) := by
  rw [DSModel.rep, ← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul, fr_toFrame]

variable {M τ}

theorem matches_exp {p q : ℕ} {T : GrpData p q} {R : DSRep T}
    {φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ} {m : ℤ} {U : M.H τ → R.U.H} (h : Matches R M τ φ m U)
    (hφ : ∀ (Z : Mat p q) (t : ℝ), NormedSpace.exp (t • φ Z) = φ (NormedSpace.exp (t • Z)))
    {Z : Mat p q} (hZ : Z ∈ upq p q) (t : ℝ) (x : M.H τ) :
    U (M.rep τ (NormedSpace.exp (t • toFrame M τ (φ Z))) x) =
      ((T.sq (T.expt (t • Z)) : ℂˣ) : ℂ) ^ m • R.U.π (T.expt (t • Z)) (U x) := by
  rw [rep_exp, hφ, h.grp, T.expt_cov _ (GlobalTheory.RealPar.KStabLie.smul_mem_upq hZ t), smul_smul,
    ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]

theorem hasDerivAt_sq_zpow {p q : ℕ} (T : GrpData p q) (m : ℤ) {Z : Mat p q} (hZ : Z ∈ upq p q) :
    HasDerivAt (fun t : ℝ => ((T.sq (T.expt (t • Z)) : ℂˣ) : ℂ) ^ m) (m * (Z.trace / 2)) 0 := by
  have h3 := (hasDerivAt_zpow m _ (.inl (Units.ne_zero _))).comp (0 : ℝ)
    (GlobalTheory.RealPar.Cover.hasDerivAt_sq (T := T) hZ)
  refine h3.congr_deriv ?_
  simp [T.expt_zero]

theorem exists_locIt (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H) (hm : (m : ℚ) = 2 * aT) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hN : Nontrivial R₂.HK.V) (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (hB : IsCoverIt R₁ R₂ B) :
    ∃ A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ, LocIt M M' τ aS aT A := by
  let A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ :=
    LinearMap.mk₂ ℂ (fun P y => U.symm (B (κ P) (U' y)))
      (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [LinearIsometryEquiv.map_smulₛₗ, LinearMap.map_smulₛₗ])
  have hA : ∀ P y, A P y = U.symm (B (κ P) (U' y)) := fun _ _ => rfl
  have hmC : (m : ℂ) = 2 * (aT : ℂ) := by exact_mod_cast hm
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  refine ⟨A, fun P y => ?_, ?_, fun P w => ?_, ?_, ?_⟩
  · refine Submodule.subset_span (h₁.smooth _ ?_)
    rw [hA, U.apply_symm_apply]
    exact hB.kfin _ _
  · obtain ⟨v, hv⟩ := exists_ne (0 : R₂.HK.V)
    obtain ⟨P, hP⟩ := hB.ne (R₂.ι v) fun h0 => hv (R₂.ι_inj (by rw [h0, map_zero]))
    refine ⟨κ.symm P, U'.symm (R₂.ι v), Submodule.subset_span (h₂.smooth _ ?_), ?_⟩
    · rw [U'.apply_symm_apply]; exact ⟨v, rfl⟩
    · rw [hA, U'.apply_symm_apply, κ.apply_symm_apply]
      intro h0
      exact hP (U.symm.injective (by rw [h0, map_zero]))
  · haveI : CompleteSpace (M'.H τ) := U'.toIsometryEquiv.completeSpace
    obtain ⟨c, hc⟩ := hB.bdd (κ P)
    let L : M'.H τ →L[ℂ] M.H τ := (A P).mkContinuous c fun y => by
      rw [hA, U.symm.norm_map, ← U'.norm_map y]; exact hc _
    refine ⟨(InnerProductSpace.toDual ℂ (M'.H τ)).symm ((innerSL ℂ w).comp L), fun y => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  · intro X hX P y
    rw [← h₁.lie] at hX
    obtain ⟨Z, hZ, rfl⟩ := hX
    have h1 := (hasDerivAt_sq_zpow T₁ m hZ).fun_smul (hB.src Z hZ (κ P) (U' y))
    have h2 := (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have h3 : (barMat e Z).map (starRingEnd ℂ) = Matrix.reindex e e Z := by ext a b; simp [barMat]
    have h4 : (barMat e Z).trace = -Z.trace := by
      rw [barMat, trace_reindex', ← trace_conj hZ]
      simp [Matrix.trace]
    convert (preTransparency := .reducible) h2 using 1
    · funext t
      apply U.injective
      rw [matches_exp h₁ (exp_barMat e) hZ, hA]
      simp
    · rw [hA, fr_toFrame, trace_toFrame, h3, h4, map_sub, map_smul, hκ.1, hmC,
        show 2 * (aT : ℂ) * (Z.trace / 2) = aT * Z.trace by ring]
      simp [T₁.expt_zero]
  · intro Y hY P y
    rw [← h₂.lie] at hY
    obtain ⟨Z, hZ, rfl⟩ := hY
    have h1 := (hasDerivAt_sq_zpow T₂ m' hZ).star.fun_smul (hB.tgt Z hZ (κ P) (U' y))
    have h2 := (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have h4 : (plainMat e' Z).trace = Z.trace := trace_reindex' e' Z
    have h5 : star ((m' : ℂ) * (Z.trace / 2)) = -((aS : ℂ) * Z.trace) := by
      rw [Complex.star_def, map_mul, map_intCast, map_div₀, trace_conj hZ, map_ofNat, hmC']
      ring
    convert (preTransparency := .reducible) h2 using 1
    · funext t
      rw [hA, matches_exp h₂ (exp_plainMat e') hZ, LinearMap.map_smulₛₗ]
      rfl
    · rw [h5, hA, fr_toFrame, trace_toFrame, h4, map_add (f := _), map_smul, plainMat, hκ.2]
      simp [T₂.expt_zero]
      abel

end GlobalTheory.Chain.RealIt.LocalFromCover

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContraStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localFockIntertwiner_realPlace_of_coverContraction : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s) (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H), (m : ℚ) = 2 * aT → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₁ M τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat e) m U → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₂ M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → Nontrivial R₂.HK.V → IsPolyIso (M.ε τ) (M'.ε τ) e e' κ → IsCoverIt R₁ R₂ B → ∃ A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ, LocIt M M' τ aS aT A := by
  first | exact @GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt | exact GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt | (intros; apply GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResLoc

open GlobalTheory.IdemSupport Formalism.L2.JoinChr Formalism.L2.Host

theorem val_alg {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem le_exp_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem locK_eq_of_tame {E : Type} [Field E] [NumberField E] (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (ht : χ.TameAt P) (k l : Eˣ) (hk : P.valuation E (k : E) = 1) (hl : P.valuation E (l : E) = 1)
    (h : P.valuation E ((k : E) - l) ≤ WithZero.exp (-1 : ℤ)) : χ.locK P k = χ.locK P l := by
  have h1 : χ.locK P (k * l⁻¹) = 1 := by
    refine ht (atFin P (k * l⁻¹)) ?_ ?_
    · change Valued.v (algebraMap E (P.adicCompletion E) ((k * l⁻¹ : Eˣ) : E)) = 1
      rw [val_alg, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hk, hl, inv_one, one_mul]
    · change Valued.v (algebraMap E (P.adicCompletion E) ((k * l⁻¹ : Eˣ) : E) - 1) ≤ _
      have e : ((k * l⁻¹ : Eˣ) : E) - 1 = ((k : E) - l) * (l : E)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ l.ne_zero]
      rw [← map_one (algebraMap E (P.adicCompletion E)), ← map_sub, val_alg, e, map_mul, map_inv₀, hl, inv_one,
        mul_one]
      exact h
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

theorem exists_lift_lt_one {R T O K Γ : Type} [CommRing R] [CommRing T] [CommRing O] [CommRing K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (t : R →+* T) (ev : R →+* K) (S : Subring T) (o : O →+* S)
    (I : Ideal O) (hs : ∀ s : T, ∃ z, t z = s) (hint : ∀ z, t z ∈ S → v (ev z) ≤ 1)
    (hI : ∀ a ∈ I, ∃ z, t z = o a ∧ v (ev z) < 1) (s : S) (h : s ∈ I.map o) : ∃ z, t z = s ∧ v (ev z) < 1 := by
  refine Submodule.span_induction (p := fun (s : S) _ => ∃ z, t z = s ∧ v (ev z) < 1) ?_ ?_ ?_ ?_ h
  · rintro _ ⟨a, ha, rfl⟩
    exact hI a ha
  · exact ⟨0, map_zero _, by rw [map_zero, map_zero]; exact zero_lt_one⟩
  · rintro x y _ _ ⟨z, hz, h⟩ ⟨z', hz', h'⟩
    refine ⟨z + z', by rw [map_add (f := _), hz, hz']; rfl, ?_⟩
    rw [map_add (f := _)]
    exact Valuation.map_add_lt _ h h'
  · rintro c x _ ⟨z, hz, h⟩
    obtain ⟨w, hw⟩ := hs c
    refine ⟨w * z, by rw [map_mul, hz, hw]; rfl, ?_⟩
    rw [map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint w (hw ▸ c.2))) h

theorem map_eq_one_of_supp {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {e x y k : R} (he : f e = 0)
    (hx : e * (x - 1) = x - 1) (hy : x = y * (1 + e * (k - 1))) : f y = 1 := by
  have h1 := congrArg f hx
  have h2 := congrArg f hy
  simp only [map_mul, map_add (f := _), map_sub, map_one, he, zero_mul, add_zero, mul_one] at h1 h2
  rw [← h2, ← sub_eq_zero, ← h1]

theorem map_eq_mul_of_supp {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {e x y k : R} (he : f e = 1)
    (hy : x = y * (1 + e * (k - 1))) : f x = f y * f k := by
  rw [hy]
  simp only [map_mul, map_add (f := _), map_sub, map_one, he]
  ring

theorem exists_units_quot {R : Type} [CommRing R] (x l : Rˣ) {r : R} (hl : (l : R) = r) :
    ∃ y : Rˣ, x = y * l ∧ (x : R) = y * r :=
  ⟨x * l⁻¹, (inv_mul_cancel_right x l).symm, by rw [← hl, ← Units.val_mul, inv_mul_cancel_right]⟩

variable {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

def evAt (Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    AE D →+* Q.adicCompletion D.host.E :=
  (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.adicCompletion D.host.E) Q).comp Φ

theorem ev_sub (a b : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (a - b) Q = Φ a Q - Φ b Q := by rw [map_sub]; rfl

theorem ev_one (Q : HeightOneSpectrum (𝓞 D.host.E)) : Φ 1 Q = 1 := by rw [map_one]; rfl

theorem ev_inc (hΦ : Comp D Φ) (a : D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (incA D a) Q = algebraMap D.host.E (Q.adicCompletion D.host.E) a := by rw [hΦ.inc]; rfl

theorem ev_eq_zero (hΦ : Comp D Φ) {z : AE D} (hz : finPart D z = 0) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ z Q = 0 := by
  let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
  have h0 : finPart D u = 0 := TensorProduct.zero_tmul _ _
  have h1 : infPart D u = 1 := rfl
  have h2 : z = u * z := by
    refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
    · rw [RingHom.map_mul, h1, one_mul]
    · rw [RingHom.map_mul, hz, mul_zero]
  have h3 : Φ u Q = 0 := (hΦ.base _ Q).trans (map_zero _)
  rw [h2, ev_mul, h3, zero_mul]

theorem toEAf_surj (s : Datum.EAf D) : ∃ z : AE D, toEAf D z = s := by
  obtain ⟨y, rfl⟩ := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective s
  obtain ⟨z, -, hz⟩ := GlobalTheory.PlaceIdem.parts_surj D 0 y
  exact ⟨z, congrArg (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) hz⟩

theorem val_le_one (hΦ : Comp D Φ) {z : AE D} (hz : toEAf D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) : Valued.v (Φ z Q) ≤ 1 :=
  (hΦ.int z).1 ((mem_intAE_iff _).2 hz) Q

theorem val_lt_one_of_mem (hΦ : Comp D Φ) (P : HeightOneSpectrum (𝓞 D.host.E))
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (hs : s ∈ idS D.host.F P.asIdeal) :
    ∀ z : AE D, toEAf D z = s → Valued.v (Φ z P) < 1 := by
  have key : ∃ z : AE D, toEAf D z = s ∧ Valued.v (Φ z P) < 1 := by
    refine exists_lift_lt_one Valued.v (toEAf D) (evAt Φ P) (Formalism.L2.Herm.intAf D.host.F D.host.E)
      (oToS D.host.F D.host.E) P.asIdeal toEAf_surj (fun z hz => val_le_one hΦ hz P) (fun a ha => ?_) s hs
    refine ⟨incA D a, rfl, ?_⟩
    change Valued.v (Φ (incA D a) P) < 1
    rw [ev_inc hΦ, val_alg]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) P a).2 ha
  obtain ⟨w, hw, h⟩ := key
  intro z hz
  have h1 : finPart D (z - w) = 0 := by
    apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    change toEAf D (z - w) = _
    rw [RingHom.map_sub, hz, hw, sub_self, map_zero]
  have h2 := ev_eq_zero hΦ h1 P
  rw [ev_sub, sub_eq_zero] at h2
  rwa [h2]

theorem exists_modulus (hΦ : Comp D Φ) (c : (AE D)ˣ →* Circle) (hc : Continuous c) :
    ∃ N : ℕ, 0 < N ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (y : (AE D)ˣ), infPart D (y : AE D) = 1 →
      (∀ Q, Q ≠ P → Φ (y : AE D) Q = 1) → Valued.v (Φ (y : AE D) P) = 1 →
      Valued.v (Φ (y : AE D) P - 1) ≤ P.valuation D.host.E (N : D.host.E) → c y = 1 := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc
  refine ⟨N, hN, fun P y h0 h1 h2 h3 => ?_⟩
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hv : ∀ Q, Valued.v (Φ (y : AE D) Q) = 1 := fun Q => by
    by_cases hQ : Q = P
    · rw [hQ, h2]
    · rw [h1 Q hQ, map_one]
  have hv' : ∀ Q, Valued.v (Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q) = 1 := fun Q => by
    have : Valued.v (Φ (y : AE D) Q) * Valued.v (Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q) = 1 := by
      rw [← map_mul, ← ev_mul, Units.mul_inv, ev_one, map_one]
    rwa [hv, one_mul] at this
  refine hker y ⟨h0, (hΦ.int _).2 fun Q => (hv Q).le, (hΦ.int _).2 fun Q => (hv' Q).le⟩
    ⟨finPart D (incA D (N : D.host.E)⁻¹ * ((y : AE D) - 1)), (hΦ.int _).2 fun Q => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, ev_sub, ev_one, ev_inc hΦ, map_mul, val_alg, map_inv₀]
    by_cases hQ : Q = P
    · subst hQ
      exact (inv_mul_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0))).2 h3
    · rw [h1 Q hQ, sub_self, map_zero, mul_zero]
      exact zero_le
  · have e : (N : AE D) * (incA D (N : D.host.E)⁻¹ * ((y : AE D) - 1)) = (y : AE D) - 1 := by
      rw [← mul_assoc, ← map_natCast (incA D) N, ← RingHom.map_mul, mul_inv_cancel₀ hN0, RingHom.map_one, one_mul]
    rw [nsmul_eq_mul, ← map_natCast (finPart D) N, ← RingHom.map_mul, e, RingHom.map_sub, RingHom.map_one]

theorem val_sub_lt_one (hΦ : Comp D Φ) (P : Pl D.host.E) (x : AE D)
    (hi : toEAf D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (b : 𝓞 D.host.E)
    (hb : resS D.host.F P ⟨toEAf D x, hi⟩ = Ideal.Quotient.mk P.asIdeal b) :
    Valued.v (Φ x P - algebraMap D.host.E (P.adicCompletion D.host.E) (b : D.host.E)) < 1 := by
  have hm : (⟨toEAf D (x : AE D), hi⟩ - oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈
      idS D.host.F P.asIdeal := by
    have h0 : resS D.host.F P (⟨toEAf D (x : AE D), hi⟩ - oToS D.host.F D.host.E b) = 0 := by
      rw [RingHom.map_sub, resS_oToS, hb, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS D.host.F P.asIdeal)
      (cmpS_bij (F := D.host.F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  have h1 := val_lt_one_of_mem hΦ P _ hm ((x : AE D) - incA D b) (by rw [RingHom.map_sub]; rfl)
  rw [ev_sub, ev_inc hΦ] at h1
  exact h1

theorem resAt_of_tame (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ) (P : Pl D.host.E)
    (a : (kP P)ˣ →* ℂˣ) (ht : χ.TameAt P) (ha : IsRes χ P a) : GlobalTheory.StepLaw.ResAt c P a := by
  intro e he x hx hi u hu
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨d0, d1, d2⟩ := delta_of_isIdemAt hΦ he
  obtain ⟨N, hN, hker⟩ := exists_modulus hΦ c hc.1.1
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  have hbP : b ∉ P.asIdeal := fun h => by
    have := P.isPrime
    exact u.ne_zero (hb.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
  have hb0 : (b : D.host.E) ≠ 0 := fun h => hbP (by rw [RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  have hbv : P.valuation D.host.E (b : D.host.E) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := b)).2 hbP
  have h1 := val_sub_lt_one hΦ P x hi b (hu.symm.trans hb.symm)
  have h2 : Valued.v (Φ (x : AE D) P) = 1 := by
    rw [← hbv, ← val_alg]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rwa [val_alg, hbv]
  obtain ⟨k, k1, k2, k3⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (Φ (x : AE D) P) (fun h => by
    rw [h, map_zero] at h2
    exact zero_ne_one h2)
  rw [h2] at k1
  rw [← k1, mul_one] at k2 k3
  have hpl : IsPlIdem D e P := by
    obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := he
    exact ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
  obtain ⟨l, hl⟩ : ∃ l : (AE D)ˣ, (l : AE D) = 1 + e * (incA D (k : D.host.E) - 1) := ⟨locU hpl.1 k, rfl⟩
  obtain ⟨y, hy, hy'⟩ := exists_units_quot x l hl
  have hyP : Φ (x : AE D) P = Φ (y : AE D) P * algebraMap D.host.E _ (k : D.host.E) := by
    rw [← ev_inc hΦ]
    exact map_eq_mul_of_supp (evAt Φ P) d1 hy'
  have hcy : c y = 1 := by
    refine hker P y (map_eq_one_of_supp (infPart D) d0 hx hy')
      (fun Q hQ => map_eq_one_of_supp (evAt Φ Q) (d2 Q hQ) hx hy') ?_ ?_
    · rwa [hyP, map_mul, val_alg, ← k1, mul_one] at h2
    · rwa [hyP, ← sub_one_mul, map_mul, val_alg, ← k1, mul_one] at k2
  have hcx : c x = c l := by rw [hy, map_mul, hcy, one_mul]
  rw [ha b (Units.mk0 _ hb0) u rfl hb.symm, hcx, hc.2 P e hpl k l hl,
    locK_eq_of_tame χ P ht k (Units.mk0 _ hb0) k1.symm hbv]
  have e5 : algebraMap D.host.E (P.adicCompletion D.host.E) ((k : D.host.E) - (b : D.host.E)) =
      (Φ (x : AE D) P - algebraMap D.host.E _ (b : D.host.E)) - (Φ (x : AE D) P - algebraMap D.host.E _ (k : D.host.E)) := by
    rw [map_sub]
    ring
  rw [Units.val_mk0, ← val_alg, e5]
  exact Valuation.map_sub_le _ (le_exp_of_lt_one h1) k3

theorem resAt_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ PP : Pl D.host.E, (∀ a : (kP PP)ˣ →* ℂˣ, χ.TameAt PP → IsRes χ PP a → GlobalTheory.StepLaw.ResAt c PP a) ∧ (χ.UnrAt PP → GlobalTheory.StepLaw.ResAt c PP 1) := by
  intro D c χ hc P
  refine ⟨fun a => resAt_of_tame c χ hc P a, fun h => resAt_of_tame c χ hc P 1 (fun x hx _ => h x hx) ?_⟩
  intro b k u hk hu
  refine (h (atFin P k) ?_).symm
  change Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1
  rw [val_alg, hk]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := b)).2 fun hb => ?_
  have := P.isPrime
  exact u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 hb))

end GlobalTheory.ResLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueCharStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleChar_restrict_localUnits_residueChar : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ PP : Pl D.host.E, (∀ a : (kP PP)ˣ →* ℂˣ, χ.TameAt PP → IsRes χ PP a → GlobalTheory.StepLaw.ResAt c PP a) ∧ (χ.UnrAt PP → GlobalTheory.StepLaw.ResAt c PP 1) := by
  first | exact @GlobalTheory.ResLoc.resAt_of_chrEq | exact GlobalTheory.ResLoc.resAt_of_chrEq | (intros; apply GlobalTheory.ResLoc.resAt_of_chrEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCreaDir

section Mat

variable {m n : ℕ}

theorem eq_sum_unitMap {Bm : Matrix (Fin m) (Fin m) ℂ} {Am : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit Bm.det)
    (hA : IsUnit Am.det) (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ i, ∑ j, (Bm⁻¹ * z * Am) i j • Formalism.IndefR.Datum.unitMap Am Bm i j := by
  have e : z = Bm * (Bm⁻¹ * z * Am) * Am⁻¹ := by
    rw [← Matrix.mul_assoc Bm, ← Matrix.mul_assoc Bm, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hA]
  have e2 := Matrix.matrix_eq_sum_single (Bm⁻¹ * z * Am)
  calc z = Bm * (∑ i, ∑ j, Matrix.single i j ((Bm⁻¹ * z * Am) i j)) * Am⁻¹ := by rw [← e2, ← e]
    _ = _ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have h : Matrix.single i j ((Bm⁻¹ * z * Am) i j) = ((Bm⁻¹ * z * Am) i j) • Matrix.single i j (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [h, Matrix.mul_smul, Matrix.smul_mul, Formalism.IndefR.Datum.unitMap]

theorem Jm_single_Jm (ε : Fin m → Bool) (δ : Fin n → Bool) (i : Fin m) (j : Fin n) :
    Formalism.REAL.Jm ε * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm δ =
      (if (ε i == δ j) then 1 else -1 : ℂ) • Matrix.single i j (1 : ℂ) := by
  ext p q
  rw [Formalism.REAL.Jm, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  by_cases h : i = p ∧ j = q
  · obtain ⟨rfl, rfl⟩ := h
    cases ε i <;> cases δ j <;> simp
  · simp [h]

end Mat

open GlobalTheory.ChainFr

variable {D : D7} {V W : HSp D}

theorem cplxO_unitMap_fr (A : Fr V) (B : Fr W) (τ : D.what₂.Tau) (i : Fin W.rank) (j : Fin V.rank) :
    cplxO (A.cart τ) (B.cart τ) (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) =
      ((if (B.ε τ i == A.ε τ j) then 1 else -1 : ℂ) * Complex.I) •
        Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := by
  have hA := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hB := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
  have h1 : B.cart τ * B.onb τ = B.onb τ * Formalism.REAL.Jm (B.ε τ) := by
    rw [Fr.cart, Fr.onb, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
  have h2 : (A.onb τ)⁻¹ * A.cart τ = Formalism.REAL.Jm (A.ε τ) * (A.onb τ)⁻¹ := by
    rw [Fr.cart, Fr.onb, Matrix.nonsing_inv_nonsing_inv _ hA]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  unfold cplxO Formalism.IndefR.Datum.unitMap
  rw [mul_comm _ Complex.I, ← smul_smul]
  congr 1
  calc B.cart τ * (B.onb τ * Matrix.single i j (1 : ℂ) * (A.onb τ)⁻¹) * A.cart τ
      = (B.cart τ * B.onb τ) * Matrix.single i j (1 : ℂ) * ((A.onb τ)⁻¹ * A.cart τ) := by
        simp only [Matrix.mul_assoc]
    _ = B.onb τ * (Formalism.REAL.Jm (B.ε τ) * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm (A.ε τ)) * (A.onb τ)⁻¹ := by
        rw [h1, h2]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Jm_single_Jm, Matrix.mul_smul, Matrix.smul_mul]

theorem fockScale_ne_zero (D : D7) (τ : D.what₂.Tau) : ((fockScale D τ : ℝ) : ℂ) ≠ 0 := by
  have h0 : 0 < ‖tauE D τ D.host.xi0‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := Formalism.L2.Theta.xi_zero_im_pos D τ
    rw [h] at this
    simp at this
  have : 0 < fockScale D τ := by
    unfold fockScale
    have := Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) h0)
    positivity
  exact_mod_cast this.ne'

end GlobalTheory.FockCreaDir


open GlobalTheory.FockCreaDir in
theorem GlobalTheory.FockCreaDir.crea_ptF : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (P : PolF D W.rank V.rank), ∃ Q : PolF D W.rank V.rank, crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f Q := by
  intro D V W A B θ ψ hψ hθ f hf τ z P
  have hS := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v
        (pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ V W) hadd hsm hth ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ V W (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ V W) hadd hsm hth hf P
  have hdA : IsUnit (A.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  have hdB : IsUnit (B.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  obtain ⟨c, rfl⟩ : ∃ c : Fin W.rank → Fin V.rank → ℂ,
      z = ∑ i, ∑ j, c i j • Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := ⟨_, eq_sum_unitMap hdB hdA z⟩
  refine ⟨((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) •
    (MvPolynomial.X (τ, i, j) * P), ?_⟩
  have h1 : ∀ (y : Matrix (Fin W.rank) (Fin V.rank) ℂ) g,
      crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g =
        ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g := fun y g => by
    rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero D τ), one_smul]
  rw [h1]
  have h2 : GlobalTheory.ChainFr.ptF ψ θ A B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) • (MvPolynomial.X (τ, i, j) * P)) =
      ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) •
        Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ))
          (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) (GlobalTheory.ChainFr.ptF ψ θ A B f P) := by
    unfold GlobalTheory.ChainFr.ptF pureTensorO
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, hX]
    rfl
  rw [h2]
  congr 1
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg (B.ε τ i == A.ε τ j) _ (cplxO_unitMap_fr A B τ i j)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCreation_preserves_fockVectors_two_frames : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (P : PolF D W.rank V.rank), ∃ Q : PolF D W.rank V.rank, crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f Q := by
  first | exact @GlobalTheory.FockCreaDir.crea_ptF | exact GlobalTheory.FockCreaDir.crea_ptF | (intros; apply GlobalTheory.FockCreaDir.crea_ptF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPair
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPair
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.PolyIso

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

theorem sgn_mul_self (x : Bool) : sgn x * sgn x = 1 := by cases x <;> simp [sgn]

variable {p q r s a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b)

def fwd : LPol b a →ₐ[ℂ] Pol p q r s :=
  aeval fun v => sgn (ε v.2) • (X (e.symm v.2, e'.symm v.1) : Pol p q r s)

def bwd : Pol p q r s →ₐ[ℂ] LPol b a :=
  aeval fun l => sgn (ε (e l.1)) • (X (e' l.2, e l.1) : LPol b a)

theorem fwd_X (c : Ix r s) (x : Ix p q) :
    fwd ε e e' (X (e' c, e x)) = sgn (ε (e x)) • (X (x, c) : Pol p q r s) := by
  simp [fwd]

def kap : LPol b a ≃ₐ[ℂ] Pol p q r s :=
  AlgEquiv.ofAlgHom (fwd ε e e') (bwd ε e e')
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨x, c⟩
      simp [fwd, bwd, smul_smul, sgn_mul_self])
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp [fwd, bwd, smul_smul, sgn_mul_self])

theorem pderiv_fwd (c : Ix r s) (x : Ix p q) (P : LPol b a) :
    pderiv (x, c) (fwd ε e e' P) = sgn (ε (e x)) • fwd ε e e' (pderiv (e' c, e x) P) := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [fwd]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P v hP =>
    obtain ⟨i, j⟩ := v
    obtain ⟨d, rfl⟩ := e'.surjective i
    obtain ⟨y, rfl⟩ := e.surjective j
    have h : pderiv (x, c) (fwd ε e e' (X (e' d, e y))) =
        sgn (ε (e x)) • fwd ε e e' (pderiv (e' c, e x) (X (e' d, e y) : LPol b a)) := by
      rw [fwd_X, Derivation.map_smul, pderiv_X, pderiv_X]
      by_cases hx : x = y
      · by_cases hc : c = d
        · subst hx hc; simp
        · simp [Ne.symm hc]
      · simp [Ne.symm hx]
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, h, hP]
    simp only [smul_eq_mul, map_add (f := _), map_mul, smul_add, mul_smul_comm]

variable {ε ε' e e'}

theorem linePos_iff (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) :
    linePos ((x, c) : Ln p q r s) = true ↔ ε' (e' c) = ε (e x) := by
  rw [h x, h' c]
  rcases x with x | x <;> rcases c with c | c <;> simp [linePos]

theorem fwd_mulX (c : Ix r s) (x : Ix p q) (P : LPol b a) :
    fwd ε e e' (sgn (ε (e x)) • (X (e' c, e x) * P)) = X (x, c) * fwd ε e e' P := by
  rw [map_smul, map_mul, fwd_X, smul_mul_assoc, smul_smul, sgn_mul_self, one_smul]

theorem fwd_rai (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) (P : LPol b a) :
    fwd ε e e' (rai ε ε' (e' c) (e x) P) = raiB (x, c) (fwd ε e e' P) := by
  unfold rai raiB
  by_cases hl : ε' (e' c) = ε (e x)
  · rw [if_pos hl, if_pos ((linePos_iff h h' x c).2 hl)]
    exact fwd_mulX c x P
  · rw [if_neg hl, if_neg (mt (linePos_iff h h' x c).1 hl)]
    simp [pderiv_fwd]

theorem fwd_low (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) (P : LPol b a) :
    fwd ε e e' (low ε ε' (e' c) (e x) P) = lowB (x, c) (fwd ε e e' P) := by
  unfold low lowB
  by_cases hl : ε' (e' c) = ε (e x)
  · rw [if_pos hl, if_pos ((linePos_iff h h' x c).2 hl)]
    simp [pderiv_fwd]
  · rw [if_neg hl, if_neg (mt (linePos_iff h h' x c).1 hl)]
    exact fwd_mulX c x P

theorem act_eq_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Mat p q →ₗ[ℂ] V) (Z : Mat p q) :
    f Z = ∑ x, ∑ y, Z x y • f (Eab x y) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, ← map_smul, Eab, Matrix.smul_single, smul_eq_mul, mul_one]

theorem fwd_locS (h : SignCompat ε e) (h' : SignCompat ε' e') (Z : Mat p q) (P : LPol b a) :
    fwd ε e e' (locS ε ε' (Matrix.reindex e e Z) P) = fockAct1 p q r s Z (fwd ε e e' P) := by
  rw [act_eq_sum (fockAct1 p q r s) Z, locS, ← e.sum_comp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [fockAct1_Eab, ← e'.sum_comp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [omE, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, fwd_rai h h', fwd_low h h']
  congr 1
  by_cases hxy : x = y <;> simp [hxy]

theorem fwd_locT (h : SignCompat ε e) (h' : SignCompat ε' e') (Z : Mat r s) (P : LPol b a) :
    fwd ε e e' (locT ε ε' (Matrix.reindex e' e' Z) P) = fockAct2 p q r s Z (fwd ε e e' P) := by
  rw [act_eq_sum (fockAct2 p q r s) Z, locT, ← e'.sum_comp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← e'.sum_comp]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [fockAct2_Eab, ← e.sum_comp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [omE, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, fwd_rai h h', fwd_low h h']
  congr 1
  by_cases hcd : c = d <;> simp [hcd]

theorem exists_isPolyIso : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a)
    (e' : Ix r s ≃ Fin b), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε' e' →
    ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ :=
  fun _ _ _ _ _ _ ε _ e e' h h' =>
    ⟨(kap ε e e').toLinearEquiv, fun Z P => fwd_locS h h' Z P, fun Z P => fwd_locT h h' Z P⟩

end GlobalTheory.Chain.RealIt.PolyIso

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockPolynomialIso_unitaryPair : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ := by
  first | exact @GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso | exact GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso | (intros; apply GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminorms
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminorms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KernelSeminorm

theorem thetaGrowth_onObjects : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D :=
  fun D => GlobalTheory.KernelSeminorm.thetaGrowth D

end GlobalTheory.KernelSeminorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_moderateGrowth_with_seminorms : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D := by
  first | exact @GlobalTheory.KernelSeminorm.thetaGrowth_onObjects | exact GlobalTheory.KernelSeminorm.thetaGrowth_onObjects | (intros; apply GlobalTheory.KernelSeminorm.thetaGrowth_onObjects <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductions
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductions
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRed

theorem frMapO_actO_int_red : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP : Pl D.host.E, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) :=
  frMapO_actO_red

end GlobalTheory.FrameRed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductionsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_movedHom_integral_reductions : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP : Pl D.host.E, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  first | exact @GlobalTheory.FrameRed.frMapO_actO_int_red | exact GlobalTheory.FrameRed.frMapO_actO_int_red | (intros; apply GlobalTheory.FrameRed.frMapO_actO_int_red <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointAction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdjAct

variable {D : D7}

theorem mt_mul_mt_inv (T : HSp D) (g : GA D T) : Formalism.L2.Theta.mt T g * Formalism.L2.Theta.mt T g⁻¹ = 1 := by
  show (matHom T g).1 * (matHom T g⁻¹).1 = 1
  rw [map_inv]; exact (matHom T g).mul_inv

theorem mt_one_inv (S : HSp D) : Formalism.L2.Theta.mt S 1⁻¹ = 1 := by
  show (matHom S 1⁻¹).1 = 1
  simp

theorem cT_mt_gram (T : HSp D) (g : GA D T) : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) =
    T.gram.map (incA D) * Formalism.L2.Theta.mt T g⁻¹ := by
  have hU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) * Formalism.L2.Theta.mt T g =
      T.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig T.gram from g).2
  calc _ = Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) *
        (Formalism.L2.Theta.mt T g * Formalism.L2.Theta.mt T g⁻¹) := by rw [mt_mul_mt_inv, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hU]

theorem finE_inv_val (T : HSp D) (g : GA D T) :
    ((Formalism.IndefR.Lev.finE T g)⁻¹).1 = (Formalism.L2.Theta.mt T g⁻¹).map (toEAf D) := by
  rw [← map_inv]; rfl

theorem conj_inv_val {n : ℕ} (β y : GL (Fin n) (EAf D)) :
    ((β⁻¹ * y * β)⁻¹ : GL (Fin n) (EAf D)).1 = (β⁻¹).1 * (y⁻¹).1 * β.1 := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]

theorem conj_transpose_mul (S T : HSp D) (g : GA D T) (x : WO S T) :
    ((HMul.hMul (Formalism.L2.Theta.mt T g) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :
        Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ =
      HMul.hMul ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ
        (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g)) := by
  rw [Matrix.map_mul, Matrix.transpose_mul]; rfl

theorem assoc_swap {R : Type} [CommRing R] {s t : ℕ} (A : Matrix (Fin s) (Fin s) R) (X : Matrix (Fin s) (Fin t) R)
    (C G N : Matrix (Fin t) (Fin t) R) (h : C * G = G * N) : A * (X * C) * G = A * X * G * N := by
  simp only [Matrix.mul_assoc]
  rw [h]

theorem frame_assoc {R : Type} [CommRing R] {s t : ℕ} (bS : Matrix (Fin s) (Fin s) R) (Y : Matrix (Fin s) (Fin t) R)
    (N bT bTi : Matrix (Fin t) (Fin t) R) (hb : bT * bTi = 1) :
    bS * (Y * N) * bT = bS * Y * bT * (bTi * N * bT) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc bT, hb, Matrix.one_mul]

theorem frMapAdj_actO : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D T) (x : WO S T), frMapAdj S T βS βT (actO S T 1 g x) = HMul.hMul (frMapAdj S T βS βT x) ((βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT)⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  intro D S T βS βT g x
  rw [frMapAdj, frMapAdj, actO, mt_one_inv, Matrix.mul_one, conj_transpose_mul, conj_inv_val, finE_inv_val,
    assoc_swap _ _ _ _ _ (cT_mt_gram T g), Matrix.map_mul]
  exact frame_assoc _ _ _ _ _ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])

end GlobalTheory.AdjAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointActionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrixAdjoint_jointAction : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D T) (x : WO S T), frMapAdj S T βS βT (actO S T 1 g x) = HMul.hMul (frMapAdj S T βS βT x) ((βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT)⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  first | exact @GlobalTheory.AdjAct.frMapAdj_actO | exact GlobalTheory.AdjAct.frMapAdj_actO | (intros; apply GlobalTheory.AdjAct.frMapAdj_actO <;> assumption)
end
end
