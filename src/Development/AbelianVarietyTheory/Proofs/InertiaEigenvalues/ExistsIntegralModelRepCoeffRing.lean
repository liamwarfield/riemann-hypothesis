module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfSaturated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowRamifiedUniformizerFieldZpow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfSaturatedStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRing
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRing
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.IntegralModelOverCoeff

open scoped Matrix

theorem exists_integral_conj {l : ℕ} [Fact l.Prime] {O Γ : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (a : ℕ) (ρ : Γ →* GL (Fin a) (Qbar l))
    (hc : Continuous fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)))
    (hK : ∀ g s t, ∃ x, ι x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t) :
    ∃ (r : Γ →* GL (Fin a) O) (Pm : GL (Fin a) (Qbar l)),
      ∀ g, mapRep (ι.comp (algebraMap O (FractionRing O))) r g = Pm⁻¹ * ρ g * Pm := by
  classical
  set K := FractionRing O
  choose f hf using hK
  have hιi : Function.Injective (ι.mapMatrix : Matrix (Fin a) (Fin a) K →+* Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro A B h
    ext s t
    exact ι.injective (congrFun (congrFun h s) t)
  have hM : ∀ g, ι.mapMatrix (Matrix.of (f g)) = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g; ext s t; exact hf g s t
  let ρ0 : Γ →* Matrix (Fin a) (Fin a) K :=
    { toFun := fun g => Matrix.of (f g)
      map_one' := hιi (by rw [hM, map_one, map_one, Units.val_one])
      map_mul' := fun g h => hιi (by rw [map_mul, hM, hM, hM, map_mul, Units.val_mul]) }
  let ρK : Γ →* GL (Fin a) K := ρ0.toHomUnits
  have hρK : ∀ g, ι.mapMatrix ((ρK g : GL _ _) : Matrix (Fin a) (Fin a) K) =
      ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) := fun g => hM g

  let Int : Set (Matrix (Fin a) (Fin a) (Qbar l)) := {M | ∀ s t, ‖M s t‖ ≤ 1}
  have hInt1 : (1 : Matrix (Fin a) (Fin a) (Qbar l)) ∈ Int := by
    intro s t
    by_cases h : s = t
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hIntMul : ∀ A B, A ∈ Int → B ∈ Int → A * B ∈ Int := by
    intro A B hA hB s t
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hA s k) (norm_nonneg _) (hB k t)
  have hIntOpen : IsOpen Int := by
    have : Int = ⋂ s, ⋂ t, (fun M : Matrix (Fin a) (Fin a) (Qbar l) => M s t) ⁻¹' Metric.closedBall 0 1 := by
      ext M; simp [Int]
    rw [this]
    exact isOpen_iInter_of_finite fun s => isOpen_iInter_of_finite fun t =>
      (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero).preimage (continuous_id.matrix_elem s t)
  let U : Subgroup Γ :=
    { carrier := {g | ((ρ g : GL _ _) : Matrix _ _ _) ∈ Int ∧ ((ρ g⁻¹ : GL _ _) : Matrix _ _ _) ∈ Int}
      one_mem' := by simp [hInt1]
      mul_mem' := by
        rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
        refine ⟨?_, ?_⟩
        · rw [map_mul, Units.val_mul]; exact hIntMul _ _ hg1 hh1
        · rw [mul_inv_rev, map_mul, Units.val_mul]; exact hIntMul _ _ hh2 hg2
      inv_mem' := by
        rintro g ⟨h1, h2⟩
        exact ⟨h2, by rwa [inv_inv]⟩ }
  have hUopen : IsOpen (U : Set Γ) :=
    (hIntOpen.preimage hc).inter (hIntOpen.preimage (hc.comp continuous_inv))
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUopen
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hUint : ∀ h ∈ U, ∀ i j, ((ρK h : GL _ _) : Matrix (Fin a) (Fin a) K) i j ∈ (algebraMap O K).range := by
    intro h hh i j
    rw [GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.mem_range_iff ι hι]
    have := congrFun (congrFun (hρK h) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this]
    exact hh.1 i j
  obtain ⟨P, hP⟩ := GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.exists_conj_integral (O := O) a ρK U hUint
  choose e he using hP
  have hai : Function.Injective ((algebraMap O K).mapMatrix :
      Matrix (Fin a) (Fin a) O →+* Matrix (Fin a) (Fin a) K) := by
    intro A B h
    ext s t
    exact IsFractionRing.injective O K (congrFun (congrFun h s) t)
  have hE : ∀ g, (algebraMap O K).mapMatrix (Matrix.of (e g)) =
      ((P * ρK g * P⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := by
    intro g; ext s t; exact he g s t
  let r0 : Γ →* Matrix (Fin a) (Fin a) O :=
    { toFun := fun g => Matrix.of (e g)
      map_one' := hai (by rw [hE, map_one, map_one, mul_one, mul_inv_cancel, Units.val_one])
      map_mul' := fun g h => hai (by
        rw [map_mul, hE, hE, hE, ← Units.val_mul, map_mul]
        congr 1
        group) }
  refine ⟨r0.toHomUnits, (Units.map (ι.mapMatrix : Matrix (Fin a) (Fin a) K →+* _).toMonoidHom P)⁻¹, fun g => ?_⟩
  ext1
  rw [inv_inv]
  show (ι.comp (algebraMap O K)).mapMatrix (Matrix.of (e g)) = _
  have : (ι.comp (algebraMap O K)).mapMatrix (Matrix.of (e g)) =
      ι.mapMatrix ((algebraMap O K).mapMatrix (Matrix.of (e g))) := by
    ext s t; rfl
  rw [this, hE, Units.val_mul, Units.val_mul, map_mul, map_mul, hρK]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [Units.coe_map_inv]
  rfl

end GlobalTheory.IntegralModelOverCoeff

namespace GlobalTheory.IntegralModelOverCoeff

open Formalism.MainNotions.SumRepresentations

theorem exists_integral_model_rep : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) (a : ℕ) (ρ : GE N →* GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ → (∀ g s t, ∃ x, A.iotaQ i x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) → ∃ (r : GE N →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))), ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  intro R H what₂ N A i a ρ hc hK
  exact exists_integral_conj (A.iotaQ i) (A.iotaQ_alg i) a ρ hc hK

end GlobalTheory.IntegralModelOverCoeff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_model_rep_coeffRing : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) (a : ℕ) (ρ : GE N →* GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ → (∀ g s t, ∃ x, A.iotaQ i x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) → ∃ (r : GE N →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))), ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  first | exact @GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep | exact GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep | (intros; apply GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSaturatedBasisEtaleLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSaturatedBasisEtaleLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.EtaleLattice

theorem exists_frob_matrix {R : Type} [CommRing R] [IsDomain R] (O : Subring R) (φ : R →+* R) (p : R) (hp : p ≠ 0)
    (hφp : φ p = p) (hφO : ∀ w ∈ O, φ w ∈ O) {d : ℕ} (Y A P Y' : Matrix (Fin d) (Fin d) R) (k m : ℕ) (u u' : R)
    (hu' : u' ∈ O) (huu : u * u' = 1) (hA : ∀ i j, A i j ∈ O) (hP : ∀ i j, P i j ∈ O)
    (hφ : (p ^ k * u) • Y.map φ = Y * A) (hY' : p ^ m • Y' = Y * P)
    (hlat : ∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, p ^ n ∣ (Y *ᵥ v) i) →
      ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ p ^ m • v = p ^ n • (P *ᵥ w)) :
    ∃ B : Matrix (Fin d) (Fin d) R, (∀ i j, B i j ∈ O) ∧ Y'.map φ = Y' * B := by
  have cancel : ∀ (n : ℕ) (M N : Matrix (Fin d) (Fin d) R), p ^ n • M = p ^ n • N → M = N := by
    intro n M N h
    refine Matrix.ext fun i j => ?_
    exact mul_left_cancel₀ (pow_ne_zero n hp) (congrFun (congrFun h i) j)
  have h1 : p ^ m • Y'.map φ = Y.map φ * P.map φ := by
    rw [← Matrix.map_mul, ← hY']
    refine Matrix.ext fun i j => ?_
    simp [hφp]
  set V : Matrix (Fin d) (Fin d) R := u' • (A * P.map φ) with hV
  have hVO : ∀ i j, V i j ∈ O := by
    intro i j
    rw [hV, Matrix.smul_apply, Matrix.mul_apply]
    exact O.mul_mem hu' (O.sum_mem fun c _ => O.mul_mem (hA i c) (hφO _ (hP c j)))
  have h2 : Y * V = p ^ (k + m) • Y'.map φ := by
    rw [hV, Matrix.mul_smul, ← Matrix.mul_assoc, ← hφ, Matrix.smul_mul, ← h1, smul_smul, smul_smul]
    congr 1
    linear_combination (p ^ k * p ^ m) * huu
  have h3 : ∀ j, ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ p ^ m • (fun i => V i j) = p ^ (k + m) • (P *ᵥ w) := by
    intro j
    refine hlat _ (fun i => hVO i j) _ fun i => ⟨φ (Y' i j), ?_⟩
    exact congrFun (congrFun h2 i) j
  choose w hwO hw using h3
  refine ⟨Matrix.of fun i j => w j i, fun i j => hwO j i, ?_⟩
  have h4 : p ^ m • V = p ^ (k + m) • (P * Matrix.of fun i j => w j i) := by
    refine Matrix.ext fun i j => ?_
    exact congrFun (hw j) i
  apply cancel (k + m)
  apply cancel m
  rw [← h2, ← Matrix.mul_smul, h4, Matrix.mul_smul, ← Matrix.mul_assoc, ← hY', Matrix.smul_mul, smul_comm]

theorem isUnit_saturated_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), (Y1.map (inclW l)).det ≠ 0 → δ ≠ 0 → bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev → (∀ g : ↥(GK K), bk.FixFlat g → τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • Y1) → ∀ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) → P.det ≠ 0 → (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) → (∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i) → IsUnit Y' := by
  intro l hl K bk τ hτ d N ρ hρ Y1 δ A1 hdet hδ hφ hg m P Y' hP hPdet hY' hlat hsat
  obtain ⟨-, -, h3, -, -, h6, h7⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  obtain ⟨ht1, -, -, ht4⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  haveI : PerfectRing (Cb l) l := by
    refine PerfectRing.ofSurjective _ l fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
    obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
    obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
    exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
      simp [frobenius_def, div_pow, map_pow]⟩
  have hl0 : (l : WCb l) ≠ 0 := WittVector.p_nonzero l (Cb l)
  have hlu : ¬ IsUnit (l : bk.S) := fun h => by
    have := h.map bk.evW
    rw [map_natCast] at this
    exact (WittVector.irreducible l (k := Cb l)).not_isUnit this
  have hev : ∀ s, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨k, δ', hnd, rfl⟩ := WfDvdMonoid.max_power_factor' hδ hlu
  obtain ⟨u', hu', huu⟩ := h3 δ' hnd
  have hφW : ((l : WCb l) ^ k * bk.evW δ') • (Y1.map (inclW l)).map (frobW l).toRingHom =
      Y1.map (inclW l) * A1.map bk.evW := by
    have := congrArg (fun M => Matrix.map M (inclW l)) hφ
    simp only [Matrix.map_mul] at this
    rw [show A1.map bk.evW = (A1.map bk.ev).map (inclW l) from rfl, ← this]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [BK.evW, RingHom.comp_apply, ← GlobalTheory.Prism.frobW_inclW]
    rfl
  obtain ⟨B, hB, hBφ⟩ := exists_frob_matrix bk.OE (frobW l).toRingHom (l : WCb l) hl0 (map_natCast _ _) h7
    (Y1.map (inclW l)) (A1.map bk.evW) P Y' k m (bk.evW δ') u' hu' huu (fun i j => hev _) hP hφW hY' hlat
  refine GlobalTheory.T.isUnit_of_saturated' l K bk d Y' B ?_ hB hBφ ?_ hsat
  · intro h0
    have := congrArg Matrix.det hY'
    rw [Matrix.det_smul, h0, mul_zero, Matrix.det_mul] at this
    exact mul_ne_zero hdet hPdet this.symm
  · intro g hfix
    obtain ⟨t, ht⟩ := ht1
    obtain ⟨s, hs⟩ := ht4 (g : GQ l)
    set Z : Matrix (Fin d) (Fin d) (WCb l) := ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) with hZ
    have hZu : IsUnit Z := ((hρ g).map (algebraMap ℤ_[l] (Ainf l)).mapMatrix).map (inclW l).mapMatrix
    have e1 : (t : WCb l) ^ N • (Z * (Y1.map (inclW l)).map (galW l (g : GQ l))) =
        (s : WCb l) ^ N • Y1.map (inclW l) := by
      have := congrArg (fun M => Matrix.map M (inclW l)) (hg g hfix)
      have e : (Y1.map (inclW l)).map (galW l (g : GQ l)) = (Y1.map (Per.σA (g : GQ l))).map (inclW l) := by
        refine Matrix.ext fun i j => ?_
        exact GlobalTheory.Prism.galW_inclW _ _
      rw [e, hZ, ← Matrix.map_mul, ht, hs]
      refine Matrix.ext fun i j => ?_
      have := congrFun (congrFun this i) j
      simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow] using this
    have e2 : (l : WCb l) ^ m • Y'.map (galW l (g : GQ l)) = (Y1.map (inclW l)).map (galW l (g : GQ l)) * P := by
      have eP : P.map (galW l (g : GQ l)) = P := by
        refine Matrix.ext fun i j => ?_
        exact h6 g hfix _ (hP i j)
      rw [← eP, ← Matrix.map_mul, ← hY']
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    refine ⟨((s⁻¹ * t) ^ N : (WCb l)ˣ) • Z, ?_, ?_⟩
    · exact hZu.smul _
    · have e3 : (l : WCb l) ^ m • ((((s⁻¹ * t) ^ N : (WCb l)ˣ) • Z) * Y'.map (galW l (g : GQ l))) =
          (l : WCb l) ^ m • Y' := by
        rw [← Matrix.mul_smul, e2, hY', ← Matrix.mul_assoc, Units.smul_def, Matrix.smul_mul, Units.val_pow_eq_pow_val,
          Units.val_mul, mul_pow, mul_smul, e1, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
      refine Matrix.ext fun i j => ?_
      exact mul_left_cancel₀ (pow_ne_zero m hl0) (congrFun (congrFun e3 i) j)

end GlobalTheory.EtaleLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSaturatedBasisEtaleLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_saturated_basis_etale_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), (Y1.map (inclW l)).det ≠ 0 → δ ≠ 0 → bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev → (∀ g : ↥(GK K), bk.FixFlat g → τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • Y1) → ∀ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) → P.det ≠ 0 → (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) → (∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i) → IsUnit Y' := by
  first | exact @GlobalTheory.EtaleLattice.isUnit_saturated_basis | exact GlobalTheory.EtaleLattice.isUnit_saturated_basis | (intros; apply GlobalTheory.EtaleLattice.isUnit_saturated_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedTwoVariableSubringSubsetGeneratorSet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedTwoVariableSubringSubsetGeneratorSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism

section Closed

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a]

theorem LTo0_zero {ι : Type} : LTo0 l (0 : ι → Wq l a) :=
  fun _ => Eventually.of_forall fun _ => dvd_zero _

theorem LTo0_add {ι : Type} {w w' : ι → Wq l a} (h : LTo0 l w) (h' : LTo0 l w') : LTo0 l (w + w') :=
  fun r => ((h r).and (h' r)).mono fun _ hp => dvd_add hp.1 hp.2

theorem LTo0_neg {ι : Type} {w : ι → Wq l a} (h : LTo0 l w) : LTo0 l (-w) :=
  fun r => (h r).mono fun _ hp => (dvd_neg).2 hp

theorem LTo0_single : LTo0 l (fun p : ℕ × ℕ => if p = (0, 0) then (1 : Wq l a) else 0) :=
  fun _ => (eventually_cofinite_ne ((0 : ℕ), (0 : ℕ))).mono fun _ hp => by simp [hp]

theorem LTo0_conv {w w' : ℕ × ℕ → Wq l a} (h : LTo0 l w) (h' : LTo0 l w')
    (c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ) :
    LTo0 l (fun p : ℕ × ℕ => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ y ∈ Finset.HasAntidiagonal.antidiagonal p.2,
      (c p.1 p.2 x y : Wq l a) * w (x.1, y.1) * w' (x.2, y.2)) := by
  intro r
  have hB := h r
  have hB' := h' r
  rw [Filter.eventually_cofinite] at hB hB' ⊢
  refine ((hB.prod hB').image fun pq : (ℕ × ℕ) × (ℕ × ℕ) => pq.1 + pq.2).subset ?_
  rintro ⟨i, n⟩ hp
  by_contra hni
  apply hp
  refine Finset.dvd_sum fun x hx => Finset.dvd_sum fun y hy => ?_
  by_cases h1 : (l : Wq l a) ^ r ∣ w (x.1, y.1)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1 _) _
  by_cases h2 : (l : Wq l a) ^ r ∣ w' (x.2, y.2)
  · exact dvd_mul_of_dvd_right h2 _
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  exact (hni ⟨((x.1, y.1), (x.2, y.2)), ⟨h1, h2⟩, by simp [Prod.mk_add_mk, hx, hy]⟩).elim

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem PPSet_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ PPSet t K e :=
  ⟨0, LTo0_zero, fun τ i n => by simp⟩

theorem PPSet_one : (1 : ZMod a → K⟦X⟧⟦X⟧) ∈ PPSet t K e := by
  refine ⟨_, LTo0_single, fun τ i n => ?_⟩
  simp only [Pi.one_apply, coeff_one]
  by_cases hi : i = 0
  · subst hi
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  · simp [hi]

theorem PPSet_add {F G : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) (hG : G ∈ PPSet t K e) :
    F + G ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  refine ⟨w + w', LTo0_add hw hw', fun τ i n => ?_⟩
  simp only [Pi.add_apply, map_add (f := _), mul_add, hF, hG]

theorem PPSet_neg {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) : -F ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨-w, LTo0_neg hw, fun τ i n => ?_⟩
  simp only [Pi.neg_apply, map_neg, mul_neg, hF]

theorem PPSet_mul {F G : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) (hG : G ∈ PPSet t K e) :
    F * G ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  let c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ := fun i n x y =>
    (i.factorial * (n / e).factorial) /
      ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial))
  refine ⟨_, LTo0_conv hw hw' c, fun τ i n => ?_⟩
  have hc : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal i, ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n,
      i.factorial * (n / e).factorial =
        c i n x y * ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial)) := by
    intro x hx y hy
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
    refine (Nat.div_mul_cancel ?_).symm
    rw [mul_mul_mul_comm]
    apply mul_dvd_mul
    · rw [← hx]; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
    · exact (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
        (Nat.factorial_dvd_factorial (by rw [← hy]; exact Nat.add_div_le_add_div _ _ _))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.mul_apply, coeff_mul, map_sum, Finset.mul_sum, map_mul, map_natCast]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [hc x hx y hy, ← hF τ x.1 y.1, ← hG τ x.2 y.2]
  push_cast
  ring

theorem PPd_subset_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∀ F ∈ PPd t K e, F ∈ PPSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF
  let S : Subring (ZMod a → K⟦X⟧⟦X⟧) :=
    { carrier := PPSet t K e
      mul_mem' := PPSet_mul t e
      one_mem' := PPSet_one t e
      add_mem' := PPSet_add t e
      zero_mem' := PPSet_zero t e
      neg_mem' := PPSet_neg t e }
  exact (Subring.closure_le (t := S)).2 le_rfl hF

end Closed

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedTwoVariableSubringSubsetGeneratorSetStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPd t K e, F ∈ PPSet t K e := by
  first | exact @GlobalTheory.CrysPrism.PPd_subset_PPSet | exact GlobalTheory.CrysPrism.PPd_subset_PPSet | (intros; apply GlobalTheory.CrysPrism.PPd_subset_PPSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionFiniteExtensionQl
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionFiniteExtensionQl
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.CoefRetraction

theorem exists_retraction (A K L : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ r : L →ₗ[K] K, r 1 = 1 ∧ ∀ x : L, IsIntegral A x → ∃ a : A, algebraMap A K a = r x := by
  classical
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.Free A (integralClosure A L) :=
    IsIntegralClosure.module_free A K L (integralClosure A L)
  have : Module.Finite A (integralClosure A L) :=
    IsIntegralClosure.finite A K L (integralClosure A L)
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A L) (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A K L (integralClosure A L)

  let b := Module.Free.chooseBasis A (integralClosure A L)
  let bL := b.localizationLocalization K (nonZeroDivisors A) L
  have hrepr : ∀ (z : integralClosure A L) i,
      bL.repr (algebraMap (integralClosure A L) L z) i = algebraMap A K (b.repr z i) :=
    fun z i => b.localizationLocalization_repr_algebraMap K (nonZeroDivisors A) L z i

  have hspan : (1 : A) ∈ Ideal.span (Set.range fun i => b.repr 1 i) := by
    obtain ⟨d, hd⟩ : ∃ d : A, Ideal.span (Set.range fun i => b.repr 1 i) = Ideal.span {d} :=
      ⟨Submodule.IsPrincipal.generator (Ideal.span (Set.range fun i => b.repr 1 i)),
        (Submodule.IsPrincipal.span_singleton_generator _).symm⟩
    have hdiv : ∀ i, ∃ e : A, e * d = b.repr 1 i := fun i => by
      have hi : b.repr 1 i ∈ Ideal.span (Set.range fun i => b.repr 1 i) :=
        Ideal.subset_span ⟨i, rfl⟩
      rw [hd] at hi
      exact Ideal.mem_span_singleton'.mp hi
    choose e he using hdiv
    set β : integralClosure A L := ∑ i, e i • b i with hβ
    have hdβ : d • β = 1 := by
      rw [hβ, Finset.smul_sum]
      conv_rhs => rw [← b.sum_repr 1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm, he i]
    have hL : algebraMap A L d * (β : L) = 1 := by
      have := congrArg (fun z : integralClosure A L => (z : L)) hdβ
      simpa [Algebra.smul_def] using this
    have hK : algebraMap K L (algebraMap A K d) * (β : L) = 1 := by
      rw [← IsScalarTower.algebraMap_apply]; exact hL
    have hd0 : algebraMap A K d ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hK; exact zero_ne_one hK
    have hint : IsIntegral A (algebraMap K L (algebraMap A K d)⁻¹) := by
      rw [map_inv₀, inv_eq_of_mul_eq_one_right hK]
      exact β.2
    have hint' : IsIntegral A (algebraMap A K d)⁻¹ :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L) (algebraMap K L).injective).mp hint
    obtain ⟨u, hu⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint'
    have hud : u * d = 1 := by
      apply IsFractionRing.injective A K
      rw [map_mul, hu, map_one, inv_mul_cancel₀ hd0]
    rw [hd, ← hud]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self d)
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hspan
  refine ⟨∑ i, algebraMap A K (a i) • bL.coord i, ?_, ?_⟩
  · have h1 : (1 : L) = algebraMap (integralClosure A L) L 1 := (map_one _).symm
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul]
    rw [h1]
    simp only [hrepr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one (algebraMap A K), ← ha, map_sum]
    simp only [map_mul]
  · intro x hx
    set z : integralClosure A L := ⟨x, show x ∈ integralClosure A L from hx⟩ with hz
    have hx' : x = algebraMap (integralClosure A L) L z := rfl
    refine ⟨∑ i, a i * b.repr z i, ?_⟩
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul]
    rw [hx']
    simp only [hrepr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul]

theorem exists_retraction_closure (R F K L : Type) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field K] [Algebra F K] [Algebra R K] [IsScalarTower R F K] [FiniteDimensional F K]
    [IsPrincipalIdealRing (integralClosure R K)]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ r : L →ₗ[K] K, r 1 = 1 ∧ ∀ x : L, IsIntegral R x → IsIntegral R (r x) := by
  have : IsScalarTower (integralClosure R K) K L := inferInstance
  have : IsFractionRing (integralClosure R K) K :=
    integralClosure.isFractionRing_of_finite_extension F K
  have : IsScalarTower R (integralClosure R K) L := IsScalarTower.of_algebraMap_eq fun y => by
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply (integralClosure R K) K L]
    rfl
  obtain ⟨r, hr1, hr⟩ := exists_retraction (integralClosure R K) K L
  refine ⟨r, hr1, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hr x (hx.tower_top)
  rw [← ha]
  exact a.2

theorem exists_integral_retraction : ∀ (l : ℕ) [Fact l.Prime] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1),
    ∃ r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ a x, r (incl hL a * x) = a * r x) ∧ r 1 = 1 ∧
      (∀ x ∈ OL LL', r x ∈ OL LL) := by
  intro l _ LL LL' hL
  letI : Algebra ↥LL.1 ↥LL'.1 := (incl hL).toRingHom.toAlgebra
  have hmap : ∀ y : ↥LL.1, algebraMap ↥LL.1 ↥LL'.1 y = incl hL y := fun _ => rfl
  have : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun q => by
    rw [hmap, AlgHom.commutes]
  have : IsScalarTower ℤ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun z => by
    rw [hmap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1, AlgHom.commutes]
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  have : FiniteDimensional ↥LL.1 ↥LL'.1 := FiniteDimensional.right ℚ_[l] ↥LL.1 ↥LL'.1
  have : IsPrincipalIdealRing (integralClosure ℤ_[l] ↥LL.1) := by
    obtain ⟨h, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    exact h.toIsPrincipalIdealRing
  obtain ⟨r, hr1, hr⟩ := exists_retraction_closure ℤ_[l] ℚ_[l] ↥LL.1 ↥LL'.1
  refine ⟨r.restrictScalars ℚ_[l], fun a x => ?_, hr1, fun x hx => hr x hx⟩
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, ← hmap, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.CoefRetraction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionFiniteExtensionQlStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_retraction_finiteExtension_ql : ∀ (l : ℕ) [Fact l.Prime] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1), ∃ r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ a x, r (incl hL a * x) = a * r x) ∧ r 1 = 1 ∧ (∀ x ∈ OL LL', r x ∈ OL LL) := by
  first | exact @GlobalTheory.CoefRetraction.exists_integral_retraction | exact GlobalTheory.CoefRetraction.exists_integral_retraction | (intros; apply GlobalTheory.CoefRetraction.exists_integral_retraction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorShiftFrobeniusMemDividedTwoVariableGenerat
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorShiftFrobeniusMemDividedTwoVariableGenerat
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism.ShMem

theorem coeff_iterate_derivative' {R : Type} [CommRing R] (f : R⟦X⟧) (i n : ℕ) :
    coeff n ((PowerSeries.derivative (R := R))^[i] f) = ((n + i).descFactorial i : R) * coeff (n + i) f := by
  induction i generalizing f with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, PowerSeries.coeff_derivative, ← add_assoc,
      Nat.succ_descFactorial_succ]
    push_cast; ring

theorem charZero_of_ql {l : ℕ} [Fact l.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

theorem coeff_sh {K : Type} [NormedField K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
    (e : ℕ) (f : K⟦X⟧) (i n : ℕ) :
    ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (sh f)) =
      (((n / e).factorial * (n + i).descFactorial i : ℕ) : K) * coeff (n + i) f := by
  have h := congrArg (coeff n) (hsh f i)
  rw [← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul, coeff_iterate_derivative'] at h
  push_cast
  rw [mul_comm (i.factorial : K), mul_assoc, h]; ring

theorem eventually_dvd {l : ℕ} [hl : Fact l.Prime] {e : ℕ} [NeZero e] (r : ℕ) :
    ∀ᶠ p : ℕ × ℕ in cofinite, l ^ r ∣ (p.2 / e).factorial * (p.2 + p.1).descFactorial p.1 := by
  rw [Filter.eventually_cofinite]
  refine ((Set.finite_lt_nat (l ^ r)).prod (Set.finite_lt_nat (e * l ^ r))).subset ?_
  rintro ⟨i, n⟩ h
  simp only [Set.mem_setOf_eq] at h
  refine ⟨?_, ?_⟩
  · show i < l ^ r
    by_contra hi; push_neg at hi
    exact h (Dvd.dvd.mul_left ((Nat.dvd_factorial (pow_pos hl.out.pos r) hi).trans
      (Nat.factorial_dvd_descFactorial _ _)) _)
  · show n < e * l ^ r
    by_contra hn; push_neg at hn
    apply h
    apply Dvd.dvd.mul_right
    apply Nat.dvd_factorial (pow_pos hl.out.pos r)
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne e))).2 (by rw [mul_comm]; exact hn)

theorem dvd_descFactorial {l n i : ℕ} (hi : i ≠ 0) (h : l ∣ n + i) : l ∣ (n + i).descFactorial i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [show n + j.succ = (n + j) + 1 from rfl, Nat.succ_descFactorial_succ]
  exact h.mul_right _

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

def nSh (e : ℕ) (p : ℕ × ℕ) : ℕ := (p.2 / e).factorial * (p.2 + p.1).descFactorial p.1


variable (l a) in
def wSh (e : ℕ) (x : (Wq l a)⟦X⟧) (p : ℕ × ℕ) : Wq l a :=
  (nSh e p : Wq l a) * coeff (p.2 + p.1) (frobS l a x)

def wDiff (e : ℕ) (x : (Wq l a)⟦X⟧) (p : ℕ × ℕ) : Wq l a :=
  if p.1 ≠ 0 ∧ l ∣ nSh e p then ((nSh e p / l : ℕ) : Wq l a) * coeff (p.2 + p.1) (frobS l a x) else 0

theorem coeff_frobS_eq_zero (x : (Wq l a)⟦X⟧) {m : ℕ} (h : ¬ l ∣ m) : coeff m (frobS l a x) = 0 := by
  have : coeff m (frobS l a x) = if l ∣ m then sigma l a (coeff (m / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [this, if_neg h]

theorem tendsToZero_crystallinePrismShiftedFrobeniusCoeff {e : ℕ} [NeZero e] (x : (Wq l a)⟦X⟧) : LTo0 l (wSh l a e x) := fun r =>
  (eventually_dvd (l := l) (e := e) r).mono fun p hp => by
    have h := Nat.cast_dvd_cast (α := Wq l a) hp
    rw [Nat.cast_pow] at h
    exact h.mul_right _

theorem tendsToZero_crystallinePrismShiftedCoeffDivPrime {e : ℕ} [NeZero e] (x : (Wq l a)⟦X⟧) : LTo0 l (wDiff e x) := fun r =>
  (eventually_dvd (l := l) (e := e) (r + 1)).mono fun p hp => by
    unfold wDiff
    split_ifs with h
    · have h2 : l ^ r ∣ nSh e p / l := Nat.dvd_div_of_mul_dvd (by rw [← pow_succ']; exact hp)
      have h3 := Nat.cast_dvd_cast (α := Wq l a) h2
      rw [Nat.cast_pow] at h3
      exact h3.mul_right _
    · exact dvd_zero _

end Main

theorem shP_frob_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ x : (Wq l a)⟦X⟧, shP a sh (inclS t K (frobS l a x)) ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, shP a sh (inclS t K (frobS l a x)) - constP a K (inclS t K (frobS l a x)) = (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t sh hsh x
  haveI : CharZero K := charZero_of_ql (l := l)
  have hkey : ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) *
      coeff n (coeff i (sh (toAc t K (frobS l a x) τ : K⟦X⟧))) = algebraMap O K (emb t τ (wSh l a e x (i, n))) := by
    intro τ i n
    rw [coeff_sh sh hsh e, coeff_toAc]
    simp only [wSh, nSh, map_mul, map_natCast, Nat.cast_mul]
  have hD : ∀ i n : ℕ, ((i.factorial * (n / e).factorial : ℕ) : K) ≠ 0 := fun i n =>
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
  refine ⟨⟨wSh l a e x, tendsToZero_crystallinePrismShiftedFrobeniusCoeff x, fun τ i n => hkey τ i n⟩,
    fun τ => mk fun i => mk fun n => algebraMap O K (emb t τ (wDiff e x (i, n))) /
      ((i.factorial * (n / e).factorial : ℕ) : K), ⟨wDiff e x, tendsToZero_crystallinePrismShiftedCoeffDivPrime x, fun τ i n => ?_⟩, ?_⟩
  · simp only [coeff_mk]; exact mul_div_cancel₀ _ (hD i n)
  · funext τ
    refine PowerSeries.ext fun i => PowerSeries.ext fun n => ?_
    change coeff n (coeff i (sh (toAc t K (frobS l a x) τ : K⟦X⟧) - C (toAc t K (frobS l a x) τ : K⟦X⟧))) =
      coeff n (coeff i ((l : K⟦X⟧⟦X⟧) * mk fun i => mk fun n => algebraMap O K (emb t τ (wDiff e x (i, n))) /
        ((i.factorial * (n / e).factorial : ℕ) : K)))
    rw [← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul,
      coeff_mk, coeff_mk, map_sub, map_sub, coeff_C]
    by_cases hi : i = 0
    · subst hi
      have h0 : wDiff e x (0, n) = 0 := by simp [wDiff]
      rw [if_pos rfl, coeff_zero_eq_constantCoeff_apply, constantCoeff_sh sh hsh, sub_self, h0]
      simp
    · rw [if_neg hi, map_zero, sub_zero]
      apply mul_left_cancel₀ (hD i n)
      rw [hkey, mul_left_comm, mul_div_cancel₀ _ (hD i n)]
      unfold wDiff
      split_ifs with h
      · have h1 : (nSh e (i, n) : Wq l a) = l * ((nSh e (i, n) / l : ℕ) : Wq l a) := by
          rw [← Nat.cast_mul, Nat.mul_div_cancel' h.2]
        simp only [wSh, h1, map_mul, map_natCast]
        ring
      · have hn : ¬ l ∣ n + i := fun hd => h ⟨hi, (dvd_descFactorial hi hd).mul_left _⟩
        simp [wSh, coeff_frobS_eq_zero x hn]

end GlobalTheory.CrysPrism.ShMem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorShiftFrobeniusMemDividedTwoVariableGeneratStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ x : (Wq l a)⟦X⟧, shP a sh (inclS t K (frobS l a x)) ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, shP a sh (inclS t K (frobS l a x)) - constP a K (inclS t K (frobS l a x)) = (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.ShMem.shP_frob_mem | exact GlobalTheory.CrysPrism.ShMem.shP_frob_mem | (intros; apply GlobalTheory.CrysPrism.ShMem.shP_frob_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStableLatticeModIrreducibleEqBot
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsComplOfSaturated
namespace GlobalTheory.SaturatedComplement

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
    (N : Submodule O M) (h : ∀ (a : O) (x : M), a ≠ (0 : O) → a • x ∈ N → x ∈ N) :
    ∃ C : Submodule O M, IsCompl N C := by
  have htf : Module.IsTorsionFree O (M ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro a q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      exact h a x ha hq
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hsec : ∀ q, N.mkQ (s q) = q := fun q => by
    simpa using LinearMap.congr_fun hs q
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hxN ⟨q, rfl⟩
    have hq : q = 0 := by
      rw [← hsec q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxN
    rw [hq, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x - s (N.mkQ x) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply,
        ← Submodule.mkQ_apply, hsec, sub_self]
    have := Submodule.add_mem_sup hx (LinearMap.mem_range_self s (N.mkQ x))
    simpa using this

end GlobalTheory.SaturatedComplement
end

noncomputable section

namespace GlobalTheory.TopSteps.FinSummand

open Module TensorProduct
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (N : Submodule O M)
    (h : ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ N → x ∈ N) : ∃ C : Submodule O M, IsCompl N C := by
  first
  | exact @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | (apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated ..)

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL]

section Rep

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {ρ : Representation LL G V}


variable [Module O V] [IsScalarTower O LL V] [IsDomain O] [IsFractionRing O LL]


omit [TopologicalSpace G] in
theorem invariants_stableLattice_mod_irreducible_eq_bot [IsDiscreteValuationRing O] (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam)
    (h : (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants = ⊥) : H0V ρ = ⊥ := by
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hsm : ∀ (a : O) (x : V), a ≠ 0 → a • x = 0 → x = 0 := fun a x ha hx => by
    rw [← algebraMap_smul LL] at hx
    exact (smul_eq_zero.1 hx).resolve_left (by simpa using ha)
  have hM : (latRep L).invariants = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {lam}) _ (IsNoetherian.noetherian _) ?_ ?_
    · intro x hx
      have h1 : x ⊗ₜ[O] (1 : O ⧸ Ideal.span {lam}) ∈
          (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants := fun g => by
        rw [coefRep_tmul, hx g]
      rw [h, Submodule.mem_bot] at h1
      have h2 := congrArg (TensorProduct.tensorQuotEquivQuotSMul ↥L.T (Ideal.span {lam})) h1
      rw [map_zero, ← map_one (Ideal.Quotient.mk _), TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul] at h2
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x lam ⊤).1 h2
      refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) fun g => Subtype.ext ?_
      have h3 := congrArg Subtype.val (hx g)
      rw [map_smul] at h3
      refine sub_eq_zero.1 (hsm lam _ hlam.ne_zero ?_)
      rw [smul_sub]
      exact sub_eq_zero.2 h3
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hlam.maximalIdeal_eq]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha, hax⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
  have h1 : (⟨a • x, hax⟩ : ↥L.T) ∈ (latRep L).invariants := fun g => Subtype.ext (by
    have := (Submodule.mem_iInf _).1 hx g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    change ρ g (a • x) = a • x
    rw [← algebraMap_smul LL, map_smul, this])
  rw [hM, Submodule.mem_bot] at h1
  exact hsm a x ha (congrArg Subtype.val h1)

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem h1fT_saturated (L : Lattice (O := O) ρ) (a : O) (x : LatticeCohomology L) (ha : a ≠ 0) (hx : a • x ∈ latticeFiniteCohomology PD L) :
    x ∈ latticeFiniteCohomology PD L := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨c', hc', h⟩ := hx
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨b, -, hb⟩ := h
  have h1 : ((c' - a • c : ↥(latticeCocycles L)) : G → V) ∈ finiteCocycles PD ρ := by
    refine ⟨(c' - a • c).2.1, b ⊗ₜ 1, fun g => ?_⟩
    have : ρ g b - b = ((c' - a • c : ↥(latticeCocycles L)) : G → V) g := congrFun hb g
    rw [← this]
    simp [actVB, sub_tmul]
  have h2 : algebraMap O LL a • (c : G → V) ∈ finiteCocycles PD ρ := by
    have := (finiteCocycles PD ρ).sub_mem hc'.2 h1
    rw [algebraMap_smul]
    simpa using this
  have ha' : algebraMap O LL a ≠ 0 := by simpa using ha
  have h3 : (c : G → V) ∈ finiteCocycles PD ρ := (Submodule.smul_mem_iff (finiteCocycles PD ρ) ha').1 h2
  exact ⟨c, ⟨c.2, h3⟩, rfl⟩

theorem finrank_h1fT [CompactSpace G] (L : Lattice (O := O) ρ) (hT : IsOpen (L.T : Set V)) :
    finrank O ↥(latticeFiniteCohomology PD L) = finrank LL (FiniteCohomology PD ρ) := by
  refine congrArg Cardinal.toNat (GlobalTheory.BlochKatoRank.rank_subquotient_eq (K := LL) LinearMap.id (latticeCocycles L) (latticeCoboundaries L)
    (latticeFiniteCocycles PD L) (finiteCocycles PD ρ) (B1 ρ) (fun a ha => ha.2) ?_ ?_ ?_)
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, hx⟩
    obtain ⟨m, hm, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
    refine ⟨m, hm, m • x, h, ?_⟩
    rw [map_smul]
    exact congrArg (m • ·) hx
  · intro c hc
    obtain ⟨a, ha, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_fun_mem L hT c hc.1.1
    have h1 : a • c ∈ (finiteCocycles PD ρ).restrictScalars O :=
      Submodule.smul_mem ((finiteCocycles PD ρ).restrictScalars O) a hc
    exact ⟨a, ha, a • c, ⟨h1.1, fun g _ => h g⟩, ⟨⟨h1.1, fun g _ => h g⟩, h1⟩, rfl⟩

end Rep

end General


end GlobalTheory.TopSteps.FinSummand
end
end
