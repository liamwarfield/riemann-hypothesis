module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntMatrixIsometryPrimeOrderLatticeStability
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQExpansionAffineTranslateCoeff
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.QAff

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rhom_eq (v : InfinitePlace F) (x : F) : rhom x v = reAt v x := (rfl)

theorem sum_reAt (x : F) : ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  have hv : ∀ v : InfinitePlace F, ((reAt v x : ℝ) : ℂ) = v.embedding x := fun v =>
    InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x
  rw [Complex.ofReal_sum, Complex.ofReal_ratCast]
  simp_rw [hv]
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ)]
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x)
    (fun σ : F →ₐ[ℚ] ℂ => σ x) (fun _ => rfl)]
  symm
  refine Fintype.sum_equiv ((Equiv.subtypeUnivEquiv
    (fun φ : F →+* ℂ => IsTotallyReal.complexEmbedding_isReal φ)).symm.trans
    (InfinitePlace.mkReal.trans
      (Equiv.subtypeUnivEquiv (fun v : InfinitePlace F => IsTotallyReal.isReal v)))) _ _ ?_
  intro φ
  simp [InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)]

theorem reAt_mul (v : InfinitePlace F) (x y : F) : reAt v (x * y) = reAt v x * reAt v y := by
  rw [← rhom_eq, ← rhom_eq, ← rhom_eq, map_mul, Pi.mul_apply]

theorem e00 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = reAt v (ε : F) :=
  rhom_eq v _

theorem e01 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = reAt v b :=
  rhom_eq v _

theorem e10 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  simp [cmp, toInf, aff]

theorem e11 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by
  simp [cmp, toInf, aff]

theorem denom_aff (ε : Fˣ) (b : F) (v : InfinitePlace F) (w : ℂ) :
    UpperHalfPlane.denom (cmp v (toInf (aff ε b))) w = 1 := by
  rw [UpperHalfPlane.denom, e10, e11]; simp

theorem act_aff (ε : Fˣ) (b : F) (hε : TP (ε : F)) (z : Hn F) (v : InfinitePlace F) :
    ((act (toInf (aff ε b)) z v : UpperHalfPlane) : ℂ) = (reAt v (ε : F) : ℂ) * (z v : ℂ) + (reAt v b : ℂ) := by
  have hd : 0 < ((Matrix.GeneralLinearGroup.det (cmp v (toInf (aff ε b))) : ℝˣ) : ℝ) := by
    simpa [Matrix.det_fin_two, e00, e01, e10, e11] using hε v
  simp only [act]
  rw [UpperHalfPlane.coe_smul_of_det_pos hd, denom_aff, div_one, UpperHalfPlane.num]
  simp [e00, e01]

theorem ez_aff (ε : Fˣ) (b : F) (hε : TP (ε : F)) (z : Hn F) (η : F) :
    ez η (act (toInf (aff ε b)) z) = ez (η * ε) z * et (η * b) := by
  simp only [ez, et, act_aff ε b hε]
  rw [← Complex.exp_add, ← Complex.ofReal_ratCast, ← sum_reAt]
  congr 1
  simp only [reAt_mul]
  push_cast
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

theorem weightSlash_hilbertAffine_apply (k : ℕ) (f : Hn F → ℂ) (ε : Fˣ) (b : F) (z : Hn F) :
    sl0 k (toInf (aff ε b)) f z = f (act (toInf (aff ε b)) z) := by
  simp only [sl0, denom_aff, Finset.prod_const_one, inv_one, one_pow, one_mul]

omit [IsTotallyReal F] in
theorem exists_den (x : F) : ∃ E : ℕ, 0 < E ∧ IsIntegral ℤ ((E : F) * x) := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  rw [Algebra.smul_def, algebraMap_int_eq, Int.coe_castRingHom] at hint
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rcases le_total 0 y with h | h
  · have e : ((y.natAbs : ℕ) : F) = (y : F) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg h]
    rw [e]
    exact hint
  · have e : ((y.natAbs : ℕ) : F) = -(y : F) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos h, Int.cast_neg]
    rw [e, neg_mul]
    exact hint.neg

theorem hasQ_aff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ) (a : F → ℂ) (ε : Fˣ) (b : F),
    TP (ε : F) → HasQ f a → HasQ (sl0 k (toInf (aff ε b)) f) (fun ξ => a (ξ / ε) * et (ξ / ε * b)) := by
  intro F _ _ _ k f a ε b hε hf
  obtain ⟨⟨D, hD, hDa⟩, hsum⟩ := hf
  obtain ⟨E, hE, hEint⟩ := exists_den (ε : F)
  have hε0 : (ε : F) ≠ 0 := ε.ne_zero
  refine ⟨⟨D * E, by positivity, ?_⟩, ?_⟩
  · intro ξ hξ
    have ha : a (ξ / ε) ≠ 0 := fun h0 => hξ (by simp [h0])
    obtain ⟨h1, h2⟩ := hDa _ ha
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · left
        rwa [div_eq_zero_iff, or_iff_left hε0] at h1
      · right
        intro v
        have hp := mul_pos (h1 v) (hε v)
        rwa [← reAt_mul, div_mul_cancel₀ _ hε0] at hp
    · have hm := h2.mul hEint
      have e : ((D * E : ℕ) : F) * ξ = ((D : F) * (ξ / ε)) * ((E : F) * ε) := by
        push_cast
        field_simp
      rw [e]
      exact hm
  · intro z
    have hs := hsum (act (toInf (aff ε b)) z)
    simp only [ez_aff ε b hε z] at hs
    rw [weightSlash_hilbertAffine_apply]
    have hc := (Equiv.hasSum_iff (Units.mulRight ε⁻¹)).mpr hs
    convert hc using 1
    funext ξ
    simp only [Function.comp_apply, Units.mulRight_apply, Units.val_inv_eq_inv_val]
    rw [← div_eq_mul_inv, div_mul_cancel₀ _ hε0]
    ring

end GlobalTheory.HilbertThetaSeries.QAff

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansion_affineTranslate_coeff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ) (a : F → ℂ) (ε : Fˣ) (b : F), TP (ε : F) → HasQ f a → HasQ (sl0 k (toInf (aff ε b)) f) (fun ξ => a (ξ / ε) * et (ξ / ε * b)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff | exact GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff | (intros; apply GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsAdelicLiftOfHilbertSystem
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.AdelicLift

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem sl_indep {k : ℕ} {Ψ : GL (Fin 2) (Af F) → Hn F → ℂ} (hΨ : Sys k Ψ) (h : GL (Fin 2) (InfinitePlace F → ℝ))
    (g : GL (Fin 2) (Af F)) (τ τ' : GL (Fin 2) F) (hτ : Pos (toInf τ * h)) (hτ' : Pos (toInf τ' * h)) :
    sl k (toInf τ * h) (Ψ (toFin τ * g)) = sl k (toInf τ' * h) (Ψ (toFin τ' * g)) := by
  have hinv : Pos (toInf τ' * h)⁻¹ := (SlashCocycle.slash_cocycle F k _ _ 0 hτ' hτ').2.1
  have hγ : Pos (toInf (τ * τ'⁻¹)) := by
    have e : toInf (τ * τ'⁻¹) = (toInf τ * h) * (toInf τ' * h)⁻¹ := by
      rw [map_mul, map_inv]; group
    rw [e]
    exact (SlashCocycle.slash_cocycle F k _ _ 0 hτ hinv).1
  have hTP : TP (τ * τ'⁻¹).val.det := ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F k 0).2.1 _).1.1 hγ
  have e1 : toInf τ * h = toInf (τ * τ'⁻¹) * (toInf τ' * h) := by
    rw [map_mul, map_inv]; group
  have e2 : toFin τ * g = toFin (τ * τ'⁻¹) * (toFin τ' * g) := by
    rw [map_mul, map_inv]; group
  rw [e1, e2, (SlashCocycle.slash_cocycle F k _ _ _ hγ hτ').2.2.2.1, hΨ.left _ hTP]

theorem map_scalar {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom z) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.GeneralLinearGroup.scalar]
  · simp [Matrix.GeneralLinearGroup.scalar, hij]

theorem scalar_comm {R : Type} [CommRing R] (z : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  exact ((Matrix.scalar_commute (z : R) (fun r => Commute.all _ r) g.val).eq).symm

theorem exists_lift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : GA F 2 → ℂ, IsLift k Ψ φ ∧ (∀ u ∈ KLev F 2 1, ∀ g, φ (g * finGL F 2 u) = φ g) ∧ ∀ (z : Ideles F) (g : GA F 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = φ g := by
  intro F _ _ _ k hk Ψ hΨ
  choose τ hτ using (GlobalTheory.T.rational_GL2_infinite_finite_factor F 1).2
  let G : GL (Fin 2) (InfinitePlace F → ℝ) → GL (Fin 2) (Af F) → Hn F → ℂ :=
    fun h g => sl k (toInf (τ h) * h) (Ψ (toFin (τ h) * g))
  have hG : ∀ h g σ, Pos (toInf σ * h) → G h g = sl k (toInf σ * h) (Ψ (toFin σ * g)) :=
    fun h g σ hσ => sl_indep hΨ h g _ _ (hτ h) hσ
  refine ⟨fun x => G (Matrix.GeneralLinearGroup.map (TR.pInf F) x) (Matrix.GeneralLinearGroup.map (pFin F) x)
    fun _ => UpperHalfPlane.I, ⟨fun γ x => ?_, fun h hh g => ?_⟩, fun u hu x => ?_, fun z x => ?_⟩
  · rw [(GlobalTheory.T.rational_GL2_infinite_finite_factor F γ).1]
    simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, TR.pFin_infGL, pFin_finGL, mul_one, one_mul]
    generalize Matrix.GeneralLinearGroup.map (TR.pInf F) x = h
    generalize Matrix.GeneralLinearGroup.map (pFin F) x = g
    have hp : Pos (toInf (τ (toInf γ * h) * γ) * h) := by
      rw [map_mul, mul_assoc]; exact hτ _
    rw [hG h g _ hp]
    simp only [G, map_mul, mul_assoc]
  · simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, TR.pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hG h g 1 (by simpa using hh)]
    simp only [map_one, one_mul]
  · simp only [map_mul, TR.pInf_finGL, pFin_finGL, mul_one, G]
    rw [← mul_assoc, hΨ.right _ u hu]
  · simp only [map_mul, map_scalar]
    generalize Matrix.GeneralLinearGroup.map (TR.pInf F) x = h
    generalize Matrix.GeneralLinearGroup.map (pFin F) x = g
    generalize Units.map (TR.pInf F).toMonoidHom z = t
    generalize Units.map (pFin F).toMonoidHom z = s
    have e : toInf (τ h) * (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) t * (toInf (τ h) * h) := by
      rw [← mul_assoc, scalar_comm, mul_assoc]
    have e' : toFin (τ h) * (Matrix.GeneralLinearGroup.scalar (Fin 2) s * g) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * (toFin (τ h) * g) := by
      rw [← mul_assoc, scalar_comm, mul_assoc]
    have H := (GlobalTheory.T.hilbert_slash_rational_matrix_properties F k (Ψ (toFin (τ h) * g))).2.2.1 hk t _ (hτ h)
    rw [hG _ _ (τ h) (by rw [e]; exact H.1), e, e', hΨ.cent, H.2]

end GlobalTheory.HilbertThetaSeries.AdelicLift

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_lift_of_hilbert_system : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : GA F 2 → ℂ, IsLift k Ψ φ ∧ (∀ u ∈ KLev F 2 1, ∀ g, φ (g * finGL F 2 u) = φ g) ∧ ∀ (z : Ideles F) (g : GA F 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = φ g := by
  first | exact @GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift | exact GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift | (intros; apply GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Gl2AdelicDoubleCosetDecompositionTotallyReal
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.Reps

variable {F : Type} [Field F] [NumberField F]

theorem aff_mul_aff {R : Type} [CommRing R] (a b : Rˣ) : aff a 0 * aff b 0 = aff (a * b) (0 : R) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

theorem toFin_aff (η : Fˣ) : toFin (aff η 0) = aff (Units.map (algebraMap F (Af F)).toMonoidHom η) 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toFin, aff]

theorem det_aff' {R : Type} [CommRing R] (y : Rˣ) (x : R) : Matrix.GeneralLinearGroup.det (aff y x) = y := by
  ext
  simp [aff, Matrix.det_fin_two]

theorem exists_sl_aff (K : Subgroup (GL (Fin 2) (Af F)))
    (hK : IsOpen (K : Set (GL (Fin 2) (Af F)))) (g : GL (Fin 2) (Af F)) :
    ∃ (σ : GL (Fin 2) F) (y : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ K ∧ Matrix.GeneralLinearGroup.det σ = 1 ∧
      g = toFin σ * (aff y 0 * u) := by
  set y := Matrix.GeneralLinearGroup.det g with hy
  have hs : g * (aff y 0)⁻¹ ∈ GroundTheory.Automorphic.AdelicGLn.finiteSL F 2 := by
    rw [GroundTheory.Automorphic.AdelicGLn.mem_finiteSL, map_mul, map_inv, det_aff', hy, mul_inv_cancel]
  have hcl := GroundTheory.Automorphic.AdelicGLn.finiteSL_le_topologicalClosure F 2 hs
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hcl
  have ho : IsOpen {s : GL (Fin 2) (Af F) | (aff y 0)⁻¹ * s⁻¹ * g ∈ K} :=
    hK.preimage (f := fun s : GL (Fin 2) (Af F) => (aff y 0)⁻¹ * s⁻¹ * g) ((continuous_const.mul continuous_inv).mul continuous_const)
  obtain ⟨_, hu, σ, hσ, rfl⟩ := mem_closure_iff.1 hcl _ ho (by
    rw [Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left, inv_mul_cancel]; exact one_mem K)
  refine ⟨σ, y, _, hu, hσ, ?_⟩
  rw [mul_assoc, mul_inv_cancel_left]
  exact (mul_inv_cancel_left _ g).symm

variable [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply, Complex.ofReal_re]

theorem TP_mul {x y : F} (hx : TP x) (hy : TP y) : TP (x * y) := fun v => by
  have := mul_pos (hx v) (hy v)
  rw [reAt_eq, reAt_eq] at this; rw [reAt_eq, map_mul]; exact this

theorem TP_inv {x : F} (hx : TP x) : TP x⁻¹ := fun v => by
  have := inv_pos.2 (hx v)
  rw [reAt_eq] at this; rw [reAt_eq, map_inv₀]; exact this

end GlobalTheory.HilbertThetaSeries.Reps

open GlobalTheory.HilbertThetaSeries.Reps in
theorem GlobalTheory.HilbertThetaSeries.finite_reps : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∃ Y : Finset (Af F)ˣ, (∀ y ∈ Y, AtP p δ y) ∧ ∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u := by
  intro F _ _ _ p hp δ hδ
  classical
  obtain ⟨Y0, hY0⟩ := (GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares F).1
  choose ξf hξf using (GlobalTheory.T.exists_different_generator_totallyPositive_translate F p hp).2 δ hδ
  set ι := Units.map (algebraMap F (Af F)).toMonoidHom with hι
  refine ⟨Y0.image (fun y => ι (ξf y) * y), ?_, ?_⟩
  · intro z hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact (hξf y).2
  · intro g
    obtain ⟨σ, y, u, hu, hσ, e⟩ := exists_sl_aff (KLev F 2 1) (isOpen_KLev le_rfl) g
    obtain ⟨y0, hy0, ξ, u0, hξ, hu0, hy⟩ := hY0 y
    have hK := (GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.1 u0 0 hu0 (fun w => by simp)
    refine ⟨aff (ξ⁻¹ * ξf y0) 0 * σ⁻¹, ?_, ι (ξf y0) * y0, Finset.mem_image_of_mem _ hy0, aff u0 0 * u, mul_mem hK.1 hu, ?_⟩
    · have hd : (aff (ξ⁻¹ * ξf y0) 0 * σ⁻¹ : GL (Fin 2) F).val.det = ((ξ⁻¹ * ξf y0 : Fˣ) : F) := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, hσ, det_aff', inv_one, mul_one]
      rw [hd, Units.val_mul]
      exact TP_mul (by simpa using TP_inv hξ) (hξf y0).1
    · rw [e, map_mul, map_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel_right, toFin_aff, ← mul_assoc, aff_mul_aff, aff_mul_aff, hy]
      congr 2
      simp only [map_mul, map_inv, hι]
      generalize (Units.map (algebraMap F (Af F)).toMonoidHom) ξ = a
      generalize (Units.map (algebraMap F (Af F)).toMonoidHom) (ξf y0) = b
      rw [mul_comm a⁻¹ b, mul_assoc b, ← mul_assoc a⁻¹, ← mul_assoc a⁻¹, inv_mul_cancel, one_mul, ← mul_assoc]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl2_adelic_double_coset_decomposition_totally_real : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∃ Y : Finset (Af F)ˣ, (∀ y ∈ Y, AtP p δ y) ∧ ∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u := by
  first | exact @GlobalTheory.HilbertThetaSeries.finite_reps | exact GlobalTheory.HilbertThetaSeries.finite_reps | (intros; apply GlobalTheory.HilbertThetaSeries.finite_reps <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FormSystemOfFinitelyManyStabilizerForms
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.SysOfStab

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

lemma pos_iff (γ : GL (Fin 2) F) : Pos (toInf γ) ↔ TP γ.val.det := by
  have h : ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det
      = rhom γ.val.det := by
    rw [RingHom.map_det]; rfl
  unfold Pos TP
  rw [h]
  rfl

lemma scal_comm {R : Type} [CommRing R] (z : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  ext1
  exact ((Matrix.scalar_commute (z : R) (fun _ => Commute.all _ _) g.val).eq).symm

def Rel (g g' : GL (Fin 2) (Af F)) (γ : GL (Fin 2) F) : Prop :=
  TP γ.val.det ∧ ∃ (z : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ KLev F 2 1 ∧
    toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g' * u

lemma tp_mul {γ γ' : GL (Fin 2) F} (h : TP γ.val.det) (h' : TP γ'.val.det) : TP (γ * γ').val.det := by
  rw [← pos_iff] at h h' ⊢
  rw [map_mul]
  exact (SlashCocycle.slash_cocycle F 0 _ _ 0 h h').1

lemma tp_inv {γ : GL (Fin 2) F} (h : TP γ.val.det) : TP (γ⁻¹).val.det := by
  rw [← pos_iff] at h ⊢
  rw [map_inv]
  exact (SlashCocycle.slash_cocycle F 0 _ _ 0 h h).2.1

lemma tp_one : TP (1 : GL (Fin 2) F).val.det := by
  rw [← pos_iff, map_one]
  intro v
  simp

lemma sl_mul (k : ℕ) {γ γ' : GL (Fin 2) F} (h : TP γ.val.det) (h' : TP γ'.val.det) (f : Hn F → ℂ) :
    sl k (toInf (γ * γ')) f = sl k (toInf γ') (sl k (toInf γ) f) := by
  rw [← pos_iff] at h h'
  rw [map_mul]
  exact (SlashCocycle.slash_cocycle F k _ _ f h h').2.2.2.1

lemma sl_one (k : ℕ) (f : Hn F → ℂ) : sl k (toInf (1 : GL (Fin 2) F)) f = f := by
  have h := (pos_iff (1 : GL (Fin 2) F)).2 tp_one
  rw [map_one]
  exact (SlashCocycle.slash_cocycle F k _ _ f h h).2.2.2.2.2

lemma Rel.symm {g g' : GL (Fin 2) (Af F)} {γ : GL (Fin 2) F} (h : Rel g g' γ) : Rel g' g γ⁻¹ := by
  obtain ⟨hγ, z, u, hu, e⟩ := h
  refine ⟨tp_inv hγ, z⁻¹, u⁻¹, inv_mem hu, ?_⟩
  have e' : g' = (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (toFin γ * g) * u⁻¹ := by
    rw [e]; group
  rw [e', map_inv, map_inv, ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)), ← mul_assoc, ← mul_assoc,
    scal_comm]
  group

lemma Rel.trans {g g' g'' : GL (Fin 2) (Af F)} {γ γ' : GL (Fin 2) F} (h : Rel g g' γ) (h' : Rel g' g'' γ') :
    Rel g g'' (γ' * γ) := by
  obtain ⟨hγ, z, u, hu, e⟩ := h
  obtain ⟨hγ', z', u', hu', e'⟩ := h'
  refine ⟨tp_mul hγ' hγ, z * z', u' * u, mul_mem hu' hu, ?_⟩
  rw [map_mul, mul_assoc, e, ← mul_assoc, ← mul_assoc, scal_comm, mul_assoc _ (toFin γ'), e', map_mul]
  group

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Y : Finset (Af F)ˣ) (f : (Af F)ˣ → Hn F → ℂ), (∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u) → (∀ y ∈ Y, Hol (f y) ∧ Gr (f y) ∧ ∀ γ, Stab (aff y 0) γ → sl k (toInf γ) (f y) = f y) → ∃ Ψ : GL (Fin 2) (Af F) → Hn F → ℂ, Sys k Ψ ∧ ∀ g, ∃ (γ : GL (Fin 2) F) (z : (Af F)ˣ), TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y 0 * u ∧ Ψ g = sl k (toInf γ) (f y) := by
  intro F _ _ _ k Y f hcov hf
  let P : GL (Fin 2) (Af F) → (Af F)ˣ → Prop := fun g y => y ∈ Y ∧ ∃ γ, Rel g (aff y 0) γ
  let y : GL (Fin 2) (Af F) → (Af F)ˣ := fun g => Classical.epsilon (P g)
  have hy : ∀ g, P g (y g) := by
    intro g
    apply Classical.epsilon_spec (p := P g)
    obtain ⟨γ, hγ, y, hyY, u, hu, e⟩ := hcov g
    exact ⟨y, hyY, γ, hγ, 1, u, hu, by rw [map_one, one_mul, e]⟩
  have hyeq : ∀ g g' γ, Rel g g' γ → y g = y g' := by
    intro g g' γ h
    have : P g = P g' := by
      funext x
      exact propext ⟨fun ⟨a, δ, b⟩ => ⟨a, _, h.symm.trans b⟩, fun ⟨a, δ, b⟩ => ⟨a, _, h.trans b⟩⟩
    simp only [y, this]
  choose c hc using fun g => (hy g).2
  let Ψ : GL (Fin 2) (Af F) → Hn F → ℂ := fun g => sl k (toInf (c g)) (f (y g))
  have key : ∀ g g' γ, Rel g g' γ → sl k (toInf γ) (Ψ g') = Ψ g := by
    intro g g' γ h
    have h1 : Rel g (aff (y g) 0) (c g' * γ) := by
      rw [hyeq g g' γ h]; exact h.trans (hc g')
    have h2 : Stab (aff (y g) 0) (c g' * γ * (c g)⁻¹) := (hc g).symm.trans h1
    have h3 := (hf _ (hy g).1).2.2 _ h2
    simp only [Ψ]
    rw [← sl_mul k (hc g').1 h.1, ← hyeq g g' γ h]
    conv_rhs => rw [← h3, ← sl_mul k h2.1 (hc g).1, inv_mul_cancel_right]
  refine ⟨Ψ, ⟨fun g => ?_, fun g => ?_, fun γ hγ g => ?_, fun g u hu => ?_, fun z g => ?_⟩, fun g => ?_⟩
  · have h := (hf _ (hy g).1).1
    exact ((HolKeep.main F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2
  · have h := (hf _ (hy g).1).2.1
    exact ((Growth.gr_closed F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2
  · exact key _ _ _ ⟨hγ, 1, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩
  · have := key (g * u) g 1 ⟨tp_one, 1, u, hu, by rw [map_one, map_one, one_mul, one_mul]⟩
    rw [← this, sl_one]
  · have := key (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) g 1
      ⟨tp_one, z, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩
    rw [← this, sl_one]
  · obtain ⟨hγ, z, u, hu, e⟩ := hc g
    exact ⟨c g, z, hγ, y g, (hy g).1, u, hu, e, rfl⟩

end GlobalTheory.HilbertThetaSeries.SysOfStab

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_system_of_finitely_many_stabilizer_forms : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Y : Finset (Af F)ˣ) (f : (Af F)ˣ → Hn F → ℂ), (∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u) → (∀ y ∈ Y, Hol (f y) ∧ Gr (f y) ∧ ∀ γ, Stab (aff y 0) γ → sl k (toInf γ) (f y) = f y) → ∃ Ψ : GL (Fin 2) (Af F) → Hn F → ℂ, Sys k Ψ ∧ ∀ g, ∃ (γ : GL (Fin 2) F) (z : (Af F)ˣ), TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y 0 * u ∧ Ψ g = sl k (toInf γ) (f y) := by
  first | exact @GlobalTheory.HilbertThetaSeries.SysOfStab.main | exact GlobalTheory.HilbertThetaSeries.SysOfStab.main | (intros; apply GlobalTheory.HilbertThetaSeries.SysOfStab.main <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.AdelicLiftKFiniteOfIsLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.LiftCpt

open UpperHalfPlane hiding I

theorem rot_smul_I (x : GL (Fin 2) ℝ) (h1 : x.val 0 0 ^ 2 + x.val 0 1 ^ 2 = 1) (hc : x.val 1 0 = -x.val 0 1)
    (hd : x.val 1 1 = x.val 0 0) : x • UpperHalfPlane.I = UpperHalfPlane.I := by
  have hdet : x.val.det = 1 := by rw [Matrix.det_fin_two, hc, hd]; linear_combination h1
  have hp : 0 < x.val.det := by rw [hdet]; exact one_pos
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by simpa using hp), div_eq_iff (denom_ne_zero _ _), num, denom, hc, hd, coe_I]
  push_cast
  linear_combination (x.val 0 1 : ℂ) * Complex.I_sq

theorem orth_cases {a b c d : ℝ} (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1)
    (h3 : a * c + b * d = 0) : (c = -b ∧ d = a) ∨ (c = b ∧ d = -a) := by
  have hD : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by
    linear_combination (c ^ 2 + d ^ 2) * h1 + h2 - (a * c + b * d) * h3
  rcases mul_eq_zero.1 hD with h | h
  · exact Or.inl ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩
  · exact Or.inr ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩

variable {F : Type} [Field F] [NumberField F]

def sg (s : InfinitePlace F → Bool) : InfinitePlace F → ℝ := fun v => if s v then 1 else -1

omit [NumberField F] in
theorem sg_mul (s : InfinitePlace F → Bool) : sg s * sg s = 1 := by
  funext v
  simp only [sg, Pi.mul_apply, Pi.one_apply]
  split_ifs <;> norm_num

def epsG (s : InfinitePlace F → Bool) : GL (Fin 2) (InfinitePlace F → ℝ) where
  val := !![sg s, 0; 0, 1]
  inv := !![sg s, 0; 0, 1]
  val_inv := by simp [sg_mul, Matrix.one_fin_two]
  inv_val := by simp [sg_mul, Matrix.one_fin_two]

variable [IsTotallyReal F]

theorem rot_rt (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : TR.Sm F 2) (hφ : IsLift k Ψ φ.1)
    (x : GL (Fin 2) (InfinitePlace F → ℝ)) (h1 : ∀ v, x.val 0 0 v ^ 2 + x.val 0 1 v ^ 2 = 1)
    (hc : ∀ v, x.val 1 0 v = -x.val 0 1 v) (hd : ∀ v, x.val 1 1 v = x.val 0 0 v) :
    ∃ c : ℂ, TR.rt F 2 (TR.infGL F 2 x) φ = c • φ := by
  have hp : Pos x := fun v => by
    rw [Matrix.det_fin_two]
    simp only [Pi.sub_apply, Pi.mul_apply, hc v, hd v]
    nlinarith [h1 v]
  have ha : act x (fun _ => UpperHalfPlane.I) = fun _ => UpperHalfPlane.I :=
    funext fun v => rot_smul_I (cmp v x) (h1 v) (hc v) (hd v)
  refine ⟨sl k x (fun _ => 1) (fun _ => UpperHalfPlane.I), Subtype.ext (funext fun g => ?_)⟩
  have hF : ∀ f : Hn F → ℂ, sl k x f (fun _ => UpperHalfPlane.I) =
      sl k x (fun _ => 1) (fun _ => UpperHalfPlane.I) * f (fun _ => UpperHalfPlane.I) := fun f => by
    simp only [sl, sl0, ha]
    ring
  rw [← TR.infGL_mul_finGL g]
  generalize Matrix.GeneralLinearGroup.map (TR.pInf F) g = y
  generalize Matrix.GeneralLinearGroup.map (pFin F) g = u
  obtain ⟨τ, hτ⟩ := (GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin F 1).2 y
  have e : ∀ y : GL (Fin 2) (InfinitePlace F → ℝ), φ.1 (TR.infGL F 2 y * finGL F 2 u) =
      φ.1 (TR.infGL F 2 (toInf τ * y) * finGL F 2 (toFin τ * u)) := fun y => by
    rw [← hφ.1 τ, (GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin F τ).1, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (finGL F 2 (toFin τ)),
      ← TR.infGL_comm, mul_assoc]
  obtain ⟨q1, -, -, q2, -⟩ := SlashCocycle.slash_cocycle F k (toInf τ * y) x (Ψ (toFin τ * u)) hτ hp
  rw [TR.rt_apply]
  change _ = _ * φ.1 _
  rw [mul_assoc, ← TR.infGL_comm, ← mul_assoc, ← map_mul, e, e y, ← mul_assoc, hφ.2 _ q1, hφ.2 _ hτ, q2, hF]

theorem lift_cpt_finite : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : TR.Sm F 2), IsLift k Ψ φ.1 → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun r => TR.cptRep F 2 r φ)) := by
  intro F _ _ _ k Ψ φ hφ
  classical
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s => TR.rt F 2 (TR.infGL F 2 (epsG s)) φ)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℂ (Set.range fun s => TR.rt F 2 (TR.infGL F 2 (epsG s)) φ)) (Submodule.span_le.2 ?_)
  rintro _ ⟨r, rfl⟩
  set x : GL (Fin 2) (InfinitePlace F → ℝ) := Unitary.toUnits r with hx
  have e : TR.cptRep F 2 r φ = TR.rt F 2 (TR.infGL F 2 x) φ := rfl
  have hr : ∀ v i j, x.val i 0 v * x.val j 0 v + x.val i 1 v * x.val j 1 v = if i = j then 1 else 0 := by
    intro v i j
    have h := congrArg (fun m => m i j v) r.2.2
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply, Pi.add_apply, Pi.mul_apply,
      star_trivial] at h
    rw [ite_apply] at h
    exact h
  have h1 : ∀ v, x.val 0 0 v ^ 2 + x.val 0 1 v ^ 2 = 1 := fun v => by
    have := hr v 0 0; simp only [if_true] at this; linear_combination this
  have h2 : ∀ v, x.val 1 0 v ^ 2 + x.val 1 1 v ^ 2 = 1 := fun v => by
    have := hr v 1 1; simp only [if_true] at this; linear_combination this
  have h3 : ∀ v, x.val 0 0 v * x.val 1 0 v + x.val 0 1 v * x.val 1 1 v = 0 := fun v => by simpa using hr v 0 1
  change TR.cptRep F 2 r φ ∈ _
  rw [e]
  clear_value x
  let s : InfinitePlace F → Bool := fun v => decide (x.val 1 0 v = -x.val 0 1 v ∧ x.val 1 1 v = x.val 0 0 v)
  have hv : (epsG s * x).val = !![sg s * x.val 0 0, sg s * x.val 0 1; x.val 1 0, x.val 1 1] := by
    ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [epsG, Matrix.mul_apply, Fin.sum_univ_two]
  have hs : ∀ v, x.val 1 0 v = -(sg s v * x.val 0 1 v) ∧ x.val 1 1 v = sg s v * x.val 0 0 v := fun v => by
    by_cases h : x.val 1 0 v = -x.val 0 1 v ∧ x.val 1 1 v = x.val 0 0 v
    · have : sg s v = 1 := by simp only [sg, s, decide_eq_true_eq]; exact if_pos h
      rw [this, one_mul, one_mul]
      exact h
    · have : sg s v = -1 := by simp only [sg, s, decide_eq_true_eq]; exact if_neg h
      rw [this]
      have := (orth_cases (h1 v) (h2 v) (h3 v)).resolve_left h
      exact ⟨by linear_combination this.1, by linear_combination this.2⟩
  obtain ⟨c, hc⟩ := rot_rt k Ψ φ hφ (epsG s * x)
    (fun v => by
      have q : sg s v * sg s v = 1 := congrFun (sg_mul s) v
      rw [hv]
      change (sg s v * x.val 0 0 v) ^ 2 + (sg s v * x.val 0 1 v) ^ 2 = 1
      linear_combination (x.val 0 0 v ^ 2 + x.val 0 1 v ^ 2) * q + h1 v)
    (fun v => by rw [hv]; exact (hs v).1) (fun v => by rw [hv]; exact (hs v).2)
  have e2 : x = epsG s * (epsG s * x) := by
    rw [← mul_assoc, show epsG s * epsG s = 1 from Units.ext (epsG s).val_inv, one_mul]
  rw [e2, map_mul, map_mul, Module.End.mul_apply, hc, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

end GlobalTheory.HilbertThetaSeries.LiftCpt

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_lift_kFinite_of_isLift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : TR.Sm F 2), IsLift k Ψ φ.1 → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun r => TR.cptRep F 2 r φ)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.LiftCpt.lift_cpt_finite | exact GlobalTheory.HilbertThetaSeries.LiftCpt.lift_cpt_finite | (intros; apply GlobalTheory.HilbertThetaSeries.LiftCpt.lift_cpt_finite <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.AdelicLiftHasModerateGrowth
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.LiftGrowth

open UpperHalfPlane hiding I
open GlobalTheory.HilbertThetaSeries.SlashCocycle

theorem abs_det_le (x : Matrix (Fin 2) (Fin 2) ℝ) (H : ℝ) (hx : ∀ i j, |x i j| ≤ H) : |x.det| ≤ 2 * H ^ 2 := by
  rw [Matrix.det_fin_two]
  have h0 : 0 ≤ H := (abs_nonneg _).trans (hx 0 0)
  have h1 : |x 0 0 * x 1 1| ≤ H * H := by rw [abs_mul]; exact mul_le_mul (hx _ _) (hx _ _) (abs_nonneg _) h0
  have h2 : |x 0 1 * x 1 0| ≤ H * H := by rw [abs_mul]; exact mul_le_mul (hx _ _) (hx _ _) (abs_nonneg _) h0
  have := abs_sub (x 0 0 * x 1 1) (x 0 1 * x 1 0)
  nlinarith

theorem place_bound (x : GL (Fin 2) ℝ) (hp : 0 < (x.det : ℝ)) (H : ℝ) (hx : ∀ i j, |x i j| ≤ H)
    (hy : ∀ i j, |(x⁻¹ : GL (Fin 2) ℝ) i j| ≤ H) :
    |(x.det : ℝ)| ≤ (2 * H) ^ 2 ∧ ‖denom x UpperHalfPlane.I‖⁻¹ ≤ 2 * H ∧
      (1 + ‖((x • UpperHalfPlane.I : ℍ) : ℂ)‖ ^ 2) / (x • UpperHalfPlane.I : ℍ).im ≤ (2 * H) ^ 4 := by
  have h0 : 0 ≤ H := (abs_nonneg _).trans (hx 0 0)
  have hd : 0 < ‖denom x UpperHalfPlane.I‖ := norm_pos_iff.2 (denom_ne_zero x _)
  have hdn : ‖denom x UpperHalfPlane.I‖ ^ 2 = x 1 0 ^ 2 + x 1 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [denom]; ring
  have hnn : ‖num x UpperHalfPlane.I‖ ^ 2 = x 0 0 ^ 2 + x 0 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [num]; ring
  have hsq : ∀ i j, x i j ^ 2 ≤ H ^ 2 := fun i j => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx i j) 2
  refine ⟨?_, ?_, ?_⟩
  · have := abs_det_le x.val H hx
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    nlinarith
  · have e : x 1 0 * (x⁻¹ : GL (Fin 2) ℝ) 0 1 + x 1 1 * (x⁻¹ : GL (Fin 2) ℝ) 1 1 = 1 := by
      have := congrFun (congrFun x.val_inv 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have a1 : |x 1 0| ≤ ‖denom x UpperHalfPlane.I‖ := by
      apply abs_le_of_sq_le_sq _ hd.le |>.trans_eq' rfl
      nlinarith [sq_nonneg (x 1 1)]
    have a2 : |x 1 1| ≤ ‖denom x UpperHalfPlane.I‖ := by
      apply abs_le_of_sq_le_sq _ hd.le |>.trans_eq' rfl
      nlinarith [sq_nonneg (x 1 0)]
    have b1 : |x 1 0 * (x⁻¹ : GL (Fin 2) ℝ) 0 1| ≤ ‖denom x UpperHalfPlane.I‖ * H := by
      rw [abs_mul]; exact mul_le_mul a1 (hy _ _) (abs_nonneg _) hd.le
    have b2 : |x 1 1 * (x⁻¹ : GL (Fin 2) ℝ) 1 1| ≤ ‖denom x UpperHalfPlane.I‖ * H := by
      rw [abs_mul]; exact mul_le_mul a2 (hy _ _) (abs_nonneg _) hd.le
    rw [inv_eq_one_div, div_le_iff₀ hd]
    have c1 := le_abs_self (x 1 0 * (x⁻¹ : GL (Fin 2) ℝ) 0 1)
    have c2 := le_abs_self (x 1 1 * (x⁻¹ : GL (Fin 2) ℝ) 1 1)
    linarith
  · have hi : ((x.det : ℝ))⁻¹ ≤ 2 * H ^ 2 := by
      have := abs_det_le (x⁻¹ : GL (Fin 2) ℝ).val H hy
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val] at this
      exact (le_abs_self _).trans this
    have e : (1 + ‖((x • UpperHalfPlane.I : ℍ) : ℂ)‖ ^ 2) / (x • UpperHalfPlane.I : ℍ).im =
        (‖denom x UpperHalfPlane.I‖ ^ 2 + ‖num x UpperHalfPlane.I‖ ^ 2) * ((x.det : ℝ))⁻¹ := by
      rw [im_smul_eq_div_normSq, coe_smul_of_det_pos hp, abs_of_pos hp, norm_div, ← Complex.sq_norm]
      simp only [I_im]
      field_simp
    rw [e, hdn, hnn]
    have s : x 1 0 ^ 2 + x 1 1 ^ 2 + (x 0 0 ^ 2 + x 0 1 ^ 2) ≤ 4 * H ^ 2 := by
      linarith [hsq 0 0, hsq 0 1, hsq 1 0, hsq 1 1]
    calc _ ≤ (4 * H ^ 2) * (2 * H ^ 2) := mul_le_mul s hi (inv_pos.2 hp).le (by positivity)
      _ ≤ _ := by nlinarith [pow_nonneg h0 4]

variable {F : Type} [Field F] [NumberField F]

theorem sl_bound (k : ℕ) (f : Hn F → ℂ) (hf : Gr f) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ (x : GL (Fin 2) (InfinitePlace F → ℝ)) (H : ℝ), Pos x → 1 ≤ H → (∀ i j v, |x i j v| ≤ H) →
      (∀ i j v, |(x⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) i j v| ≤ H) →
      ‖sl k x f fun _ => UpperHalfPlane.I‖ ≤ C * (2 * H) ^ N := by
  obtain ⟨C, A, hC⟩ := hf
  set n := (Finset.univ : Finset (InfinitePlace F)).card with hnc
  refine ⟨|C|, 2 * n * k + n * k + 4 * n * A, abs_nonneg _, fun x H hp hH hx hy => ?_⟩
  have hb := fun v => place_bound (cmp v x) (by rw [cmp_det]; exact hp v) H (fun i j => hx i j v)
    (fun i j => by rw [← map_inv]; exact hy i j v)
  set K := 2 * H
  have hK : 1 ≤ K := by simp only [K]; linarith
  have h1 : (∏ v, |(x : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) ≤ (K ^ 2) ^ n := by
    rw [hnc, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun v _ => abs_nonneg _) fun v _ => by rw [← cmp_det]; exact (hb v).1
  have h1' : (∏ v, |(x : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) ^ ((k : ℝ) / 2) ≤ K ^ (2 * n * k) := by
    calc _ ≤ ((K ^ 2) ^ n) ^ ((k : ℝ) / 2) :=
          Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => abs_nonneg _) h1 (by positivity)
      _ ≤ ((K ^ 2) ^ n) ^ (k : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (one_le_pow₀ hK)) (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith)
      _ = _ := by rw [Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_assoc]
  have h2 : ‖(∏ v, denom (cmp v x) (UpperHalfPlane.I))⁻¹ ^ k‖ ≤ K ^ (n * k) := by
    rw [norm_pow, pow_mul, norm_inv, norm_prod, ← Finset.prod_inv_distrib]
    refine pow_le_pow_left₀ (Finset.prod_nonneg fun v _ => by positivity) ?_ k
    rw [hnc, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun v _ => by positivity) fun v _ => (hb v).2.1
  have h3 : ‖f (act x fun _ => UpperHalfPlane.I)‖ ≤ |C| * K ^ (4 * n * A) := by
    refine (hC _).trans ?_
    have hn : ∀ v, 0 ≤ (1 + ‖((act x (fun _ => UpperHalfPlane.I) v : ℍ) : ℂ)‖ ^ 2) / (act x (fun _ => UpperHalfPlane.I) v).im :=
      fun v => div_nonneg (by positivity) (im_pos _).le
    refine mul_le_mul (le_abs_self _) ?_ (pow_nonneg (Finset.prod_nonneg fun v _ => hn v) _) (abs_nonneg _)
    rw [pow_mul, pow_mul]
    refine pow_le_pow_left₀ (Finset.prod_nonneg fun v _ => hn v) ?_ A
    rw [hnc, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun v _ => hn v) fun v _ => (hb v).2.2
  have hK0 : 0 ≤ K := by linarith
  simp only [sl, sl0]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (Real.rpow_nonneg (Finset.prod_nonneg fun v _ => abs_nonneg _) _)]
  calc _ ≤ K ^ (2 * n * k) * (K ^ (n * k) * (|C| * K ^ (4 * n * A))) :=
        mul_le_mul h1' (mul_le_mul h2 h3 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
    _ = _ := by rw [pow_add, pow_add]; ring

theorem one_le_height (y : GL (Fin 2) (InfinitePlace F → ℝ)) : 1 ≤ TR.height y := by
  unfold TR.height
  linarith [norm_nonneg (TR.toL y.val), norm_nonneg (TR.toL (y⁻¹).val)]

theorem entry_le_norm (y : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)) (i j : Fin 2) (v : InfinitePlace F) :
    |y i j v| ≤ ‖TR.toL y‖ :=
  (norm_le_pi_norm (TR.toL y i j) v).trans ((norm_le_pi_norm (TR.toL y i) j).trans (norm_le_pi_norm (TR.toL y) i))

theorem entry_le_height (y : GL (Fin 2) (InfinitePlace F → ℝ)) (i j : Fin 2) (v : InfinitePlace F) :
    |y i j v| ≤ TR.height y := by
  unfold TR.height
  linarith [entry_le_norm y.val i j v, norm_nonneg (TR.toL (y⁻¹).val)]

theorem inv_entry_le_height (y : GL (Fin 2) (InfinitePlace F → ℝ)) (i j : Fin 2) (v : InfinitePlace F) :
    |(y⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) i j v| ≤ TR.height y := by
  unfold TR.height
  linarith [entry_le_norm (y⁻¹).val i j v, norm_nonneg (TR.toL y.val)]

theorem mul_entry_le (x y : GL (Fin 2) (InfinitePlace F → ℝ)) (a b : ℝ) (hx : ∀ i j v, |x i j v| ≤ a)
    (hy : ∀ i j v, |y i j v| ≤ b) (i j : Fin 2) (v : InfinitePlace F) :
    |(x * y : GL (Fin 2) (InfinitePlace F → ℝ)) i j v| ≤ 2 * a * b := by
  have e : (x * y : GL (Fin 2) (InfinitePlace F → ℝ)) i j v = x i 0 v * y 0 j v + x i 1 v * y 1 j v := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have ha : 0 ≤ a := (abs_nonneg _).trans (hx i j v)
  have h1 : |x i 0 v * y 0 j v| ≤ a * b := by rw [abs_mul]; exact mul_le_mul (hx _ _ _) (hy _ _ _) (abs_nonneg _) ha
  have h2 : |x i 1 v * y 1 j v| ≤ a * b := by rw [abs_mul]; exact mul_le_mul (hx _ _ _) (hy _ _ _) (abs_nonneg _) ha
  rw [e]
  linarith [abs_add_le (x i 0 v * y 0 j v) (x i 1 v * y 1 j v)]

theorem sl_mul_bound (k : ℕ) (f : Hn F → ℂ) (hf : Gr f) (t : GL (Fin 2) (InfinitePlace F → ℝ)) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ y : GL (Fin 2) (InfinitePlace F → ℝ), Pos (t * y) →
      ‖sl k (t * y) f fun _ => UpperHalfPlane.I‖ ≤ C * TR.height y ^ N := by
  obtain ⟨C, N, hC, h⟩ := sl_bound k f hf
  have ht := one_le_height t
  refine ⟨C * (4 * TR.height t) ^ N, N, by positivity, fun y hp => ?_⟩
  have hy := one_le_height y
  have := h (t * y) (2 * TR.height t * TR.height y) hp (by nlinarith)
    (mul_entry_le t y _ _ (entry_le_height t) (entry_le_height y)) fun i j v => by
      rw [mul_inv_rev]
      exact (mul_entry_le _ _ _ _ (inv_entry_le_height y) (inv_entry_le_height t) i j v).trans_eq (by ring)
  refine this.trans_eq ?_
  rw [mul_assoc C, ← mul_pow]
  congr 2
  ring

theorem det_ne_zero (v : InfinitePlace F) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v ≠ 0 := by
  rw [← cmp_det]; exact Units.ne_zero _

theorem pos_of_sign (t y y' : GL (Fin 2) (InfinitePlace F → ℝ)) (hp : Pos (t * y))
    (hs : ∀ v, 0 < y.val.det v ↔ 0 < y'.val.det v) : Pos (t * y') := by
  intro v
  have h := hp v
  rw [det_mul_apply] at h ⊢
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos h1 ((hs v).1 h2)
  · refine mul_pos_of_neg_of_neg h1 (lt_of_le_of_ne (not_lt.1 fun h3 => ?_) (det_ne_zero v y'))
    exact lt_asymm h2 ((hs v).2 h3)

theorem lift_growth : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ), (∀ g, Gr (Ψ g)) → IsLift k Ψ φ → ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * TR.infGL F 2 y)‖ ≤ C * TR.height y ^ N := by
  intro F _ _ _ k Ψ φ hgr hl g
  classical
  rw [← TR.infGL_mul_finGL g]
  set h := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set u := Matrix.GeneralLinearGroup.map (pFin F) g
  have key : ∀ s : InfinitePlace F → Prop, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ y : GL (Fin 2) (InfinitePlace F → ℝ),
      (∀ v, 0 < y.val.det v ↔ s v) →
      ‖φ (TR.infGL F 2 h * finGL F 2 u * TR.infGL F 2 y)‖ ≤ C * TR.height y ^ N := by
    intro s
    by_cases hs : ∃ y₀ : GL (Fin 2) (InfinitePlace F → ℝ), ∀ v, 0 < y₀.val.det v ↔ s v
    · obtain ⟨y₀, h₀⟩ := hs
      obtain ⟨τ, hτ⟩ := (GlobalTheory.T.rational_GL2_infinite_finite_factor F 1).2 (h * y₀)
      rw [← mul_assoc] at hτ
      obtain ⟨C, N, hC, hb⟩ := sl_mul_bound k (Ψ (toFin τ * u)) (hgr _) (toInf τ * h)
      refine ⟨C, N, hC, fun y hy => ?_⟩
      have hp : Pos (toInf τ * h * y) := pos_of_sign _ y₀ y hτ fun v => (h₀ v).trans (hy v).symm
      have e : ratGL F 2 τ * (TR.infGL F 2 h * finGL F 2 u * TR.infGL F 2 y) =
          TR.infGL F 2 (toInf τ * h * y) * finGL F 2 (toFin τ * u) := by
        rw [(GlobalTheory.T.rational_GL2_infinite_finite_factor F τ).1]
        exact TR.ga_ext (by simp [mul_assoc]) (by simp)
      rw [← hl.1 τ, e, hl.2 _ hp]
      exact hb y hp
    · exact ⟨0, 0, le_rfl, fun y hy => absurd ⟨y, hy⟩ hs⟩
  choose C N hC hb using key
  refine ⟨∑ s, C s, ∑ s, N s, fun y => (hb (fun v => 0 < y.val.det v) y fun _ => Iff.rfl).trans ?_⟩
  have hy := one_le_height y
  exact mul_le_mul (Finset.single_le_sum (fun s _ => hC s) (Finset.mem_univ _))
    (pow_le_pow_right₀ hy (Finset.single_le_sum (fun s _ => Nat.zero_le (N s)) (Finset.mem_univ _)))
    (by positivity) (Finset.sum_nonneg fun s _ => hC s)

end GlobalTheory.HilbertThetaSeries.LiftGrowth

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_lift_has_moderate_growth : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ), (∀ g, Gr (Ψ g)) → IsLift k Ψ φ → ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * TR.infGL F 2 y)‖ ≤ C * TR.height y ^ N := by
  first | exact @GlobalTheory.HilbertThetaSeries.LiftGrowth.lift_growth | exact GlobalTheory.HilbertThetaSeries.LiftGrowth.lift_growth | (intros; apply GlobalTheory.HilbertThetaSeries.LiftGrowth.lift_growth <;> assumption)
end
