module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.OneSubEvTInvInt

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSLocA
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.SigRTmulOne
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PsiInclR
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Apx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem Psi_sigR (v : HeightOneSpectrum (𝓞 F)) (x : Af F ⊗[F] E) :
    Psi v (PI.UJClassFin.sigR (Af F) σ x) = PI.UnitaryApproxDefs.sigR σ (Fv F v) (Psi v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have e1 : PI.UJClassFin.sigR (Af F) σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [PI.UJClassFin.sigR]
    rw [e1, Psi_tmul, Psi_tmul]
    simp [PI.UnitaryApproxDefs.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Psi_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    Psi v (inclR (F := F) (Af F) e) = PI.UnitaryApproxDefs.inclE (F := F) (Fv F v) e := by
  show Psi v ((1 : Af F) ⊗ₜ[F] e) = e ⊗ₜ[F] (1 : Fv F v)
  rw [Psi_tmul]; rfl

def finU (g : HA (AF F) σ J) : GL (Fin M) (Af F ⊗[F] E) :=
  ⟨finMat σ J g, finMat σ J g⁻¹, by rw [← finMat_mul, mul_inv_cancel, finMat_one],
    by rw [← finMat_mul, inv_mul_cancel, finMat_one]⟩

def gLoc (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) : GL (Fin M) (E ⊗[F] Fv F v) :=
  Units.map ((Psi (E := E) v).toRingHom.mapMatrix : Matrix (Fin M) (Fin M) (Af F ⊗[F] E) →+*
    Matrix (Fin M) (Fin M) (E ⊗[F] Fv F v)).toMonoidHom (finU σ J g)

theorem gLoc_val (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) :
    ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) (E ⊗[F] Fv F v)) =
      (finMat σ J g).map (Psi v) := rfl

theorem gLoc_mem (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) :
    gLoc σ J g v ∈ PI.UnitaryApproxDefs.UPts σ J (Fv F v) := by
  show PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (Fv F v)) ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) _) *
      J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v)) * ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) _) =
    J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v))
  rw [gLoc_val]
  have hU := congrArg (fun X => X.map (Psi (E := E) v)) (finMat_unitary σ J g)
  beta_reduce at hU
  rw [mapAlg_mul, mapAlg_mul] at hU
  have hcT : ∀ X : Matrix (Fin M) (Fin M) (Af F ⊗[F] E),
      (PI.UJClassFin.cT (PI.UJClassFin.sigR (Af F) σ) X).map (Psi v) = PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (Fv F v)) (X.map (Psi v)) := by
    intro X; ext i j; simp [PI.UJClassFin.cT, PI.UnitaryApproxDefs.cT, Psi_sigR]
  have hJ : (JR (Af F) J).map (Psi (E := E) v) = J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v)) := by
    ext i j; simp [JR, Psi_inclR]
  rw [hcT, hJ] at hU
  exact hU

theorem approxT (hσσ : ∀ e, σ (σ e) = e) (hθ : ∃ θ, σ θ ≠ θ) (hH : PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J)
    (hdet : IsUnit J.det) (g : HA (AF F) σ J) (T : Finset (HeightOneSpectrum (𝓞 F))) (N0 : ℕ)
    (hN0 : 0 < N0) :
    ∃ γ : PI.UJClassFin.UJ (σ : E →+* E) J, ∀ i j, ∃ o ∈ Oh F E,
      (evT (T : Set (HeightOneSpectrum (𝓞 F))) ⊗ₜ[F] (1 : E)) *
        (finMat σ J g i j - inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j)) =
        N0 • o := by
  classical
  have hD : ((N0 : 𝓞 F)) ≠ 0 := by exact_mod_cast hN0.ne'
  obtain ⟨γ, hγ, hc⟩ := unitary_approximation_finite F E (Fin M) σ J hσσ hθ hH hdet T
    (fun w => gLoc σ J g w) (fun w _ => gLoc_mem σ J g w) (N0 : 𝓞 F) hD
  refine ⟨⟨γ, hγ⟩, fun i j => ?_⟩
  show ∃ o ∈ Oh F E, (evT (T : Set (HeightOneSpectrum (𝓞 F))) ⊗ₜ[F] (1 : E)) *
        (finMat σ J g i j - inclR (F := F) (Af F) ((γ : Matrix (Fin M) (Fin M) E) i j)) = N0 • o
  have hc' : ∀ w : T, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (Fv F w.1) (PI.UnitaryApproxDefs.intOE E) (w.1.adicCompletionIntegers F).toSubring,
      Psi w.1 (finMat σ J g i j) - PI.UnitaryApproxDefs.inclE (F := F) (Fv F w.1) ((γ : Matrix (Fin M) (Fin M) E) i j) =
        PI.UnitaryApproxDefs.inclE (F := F) (Fv F w.1) (algebraMap F E ((N0 : 𝓞 F) : F)) * s := fun w => hc w.1 w.2 i j
  choose s hs hse using hc'
  refine ⟨∑ w : T, (sgl w.1 1 ⊗ₜ[F] (1 : E)) * Phi w.1 (s w),
    AddSubgroup.sum_mem _ fun w _ => Oh_mul (tmul_mem_Oh (sgl_int _ (one_mem _)) isIntegral_one) (Phi_int _ (hs w)), ?_⟩
  rw [evT_eq_sum, TensorProduct.sum_tmul, Finset.sum_mul, ← Finset.sum_coe_sort T, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Phi_Psi, map_sub, Psi_inclR, hse w, Phi_mul, Phi_inclE]
  have e0 : ((N0 : 𝓞 F) : F) = (N0 : F) := by simp
  have e1 : sgl w.1 1 ⊗ₜ[F] (algebraMap F E ((N0 : 𝓞 F) : F)) = N0 • (sgl w.1 1 ⊗ₜ[F] (1 : E)) := by
    rw [e0, show algebraMap F E (N0 : F) = (N0 : F) • (1 : E) by rw [Algebra.smul_def, mul_one],
      TensorProduct.tmul_smul, Nat.cast_smul_eq_nsmul]
  rw [e1, smul_mul_assoc]

end Apx

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {M : ℕ}

theorem stabT (L : Set (Fin M → E)) {u k : ℕ} (hu : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i))
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L) {a : Af F} (ha : a ∈ intAf F)
    (Y : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (hY : ∀ i j, ∃ o ∈ Oh F E, (a ⊗ₜ[F] (1 : E)) * (Y - 1) i j = (u * k) • o)
    {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E L) :
    (a ⊗ₜ[F] (1 : E)) • Y.mulVec y ∈ latHat F E L := by
  choose o ho hoe using hY
  have hYy : Y.mulVec y = y + (Y - 1).mulVec y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have e1 : (a ⊗ₜ[F] (1 : E)) • (Y - 1).mulVec y = k • fun i => ∑ j, o i j * (u • y j) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hoe i j]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [hYy, smul_add, e1]
  exact add_mem (latHat_smul L ha hy)
    (low_vec L hk fun i => AddSubgroup.sum_mem _ fun j _ => Oh_mul (ho i j) (up_Oh L hu hy j))

theorem locCmpT (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) {k : ℕ} (hkpos : 0 < k)
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    (T : Set (HeightOneSpectrum (𝓞 F))) (p : ℕ) (hp0 : p ≠ 0) (hp : p ≠ 1)
    (hpT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → (p : 𝓞 F) ∉ w.asIdeal) (g1 g2 : HA (AF F) σ J)
    (hC : ∀ y ∈ latHat F E L, (evT T ⊗ₜ[F] (1 : E)) • (finMat σ J (g2⁻¹ * g1)).mulVec y ∈ latHat F E L)
    {x : Fin M → E} (hx : x ∈ abelian₂ σ J L g1) : ∃ m2 : ℕ, ¬ p ∣ m2 ∧ (m2 : E) • x ∈ abelian₂ σ J L g2 := by
  classical
  set z := (finMat σ J g2⁻¹).mulVec (vinc (F := F) x) with hz
  have hzC : (evT T ⊗ₜ[F] (1 : E)) • z ∈ latHat F E L := by
    have : z = (finMat σ J (g2⁻¹ * g1)).mulVec ((finMat σ J g1⁻¹).mulVec (vinc (F := F) x)) := by
      rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hC _ hx
  have hden : ∃ m : ℕ, 0 < m ∧ m • z ∈ latHat F E L := by
    choose mf hmf hmO using fun i => den (F := F) (E := E) (z i)
    refine ⟨k * ∏ i, mf i, Nat.mul_pos hkpos (Finset.prod_pos fun i _ => hmf i), ?_⟩
    rw [mul_smul]
    apply low_vec L hk
    intro i
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ i)
    show (∏ i, mf i) • z i ∈ Oh F E
    rw [hq, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (hmO i) _
  obtain ⟨m, hm, hmz⟩ := hden
  obtain ⟨a, m2, hm2, hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp
  refine ⟨m2, hm2, ?_⟩
  show (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) ∈ latHat F E L
  have e2 : (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) = m2 • z := by
    rw [Nat.cast_smul_eq_nsmul, hz]
    have : vinc (F := F) (m2 • x) = m2 • vinc (F := F) x := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_smul]
  rw [e2]
  set c : Af F := (1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) with hc
  have hcI : c ∈ intAf F := one_sub_evT_inv_int T ((p : 𝓞 F) ^ a)
    (fun w hw hpw => hpT w hw (w.isPrime.mem_of_pow_mem a hpw))
  have hpa : algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a) ≠ 0 := by
    rw [map_pow, map_natCast]; exact pow_ne_zero _ (by exact_mod_cast hp0)
  have hA : algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) * ((p : Af F) ^ a) = 1 := by
    rw [show ((p : Af F) ^ a) = algebraMap F (Af F) (algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a)) by simp,
      ← map_mul, inv_mul_cancel₀ hpa, map_one]
  have hsc : (m2 : Af F) = m2 * evT T + c * (m : Af F) := by
    rw [hmeq, hc]; push_cast at hA ⊢
    linear_combination (-(1 - evT T) * (m2 : Af F)) * hA
  have e3 : m2 • z = m2 • ((evT T ⊗ₜ[F] (1 : E)) • z) + (c ⊗ₜ[F] (1 : E)) • (m • z) := by
    have hι := congrArg (Algebra.TensorProduct.includeLeftRingHom : Af F →+* Af F ⊗[F] E) hsc
    simp only [map_add (f := _), map_mul, map_natCast] at hι
    rw [← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2 z, ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2,
      ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m z, smul_smul, smul_smul, ← add_smul]
    congr 1
  rw [e3]
  exact add_mem (AddSubgroup.nsmul_mem _ hzC _) (latHat_smul L hcI hmz)

theorem sigR_tmul_one (σ : E →ₐ[F] E) (e : Af F) :
    PI.UJClassFin.sigR (Af F) σ (e ⊗ₜ[F] (1 : E)) = e ⊗ₜ[F] (1 : E) := by
  simp [PI.UJClassFin.sigR]

theorem invSmall (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) {dI dJ : ℕ}
    (hdI : ∀ i j, IsIntegral ℤ ((dI : E) * J⁻¹ i j)) (hdJ : ∀ i j, IsIntegral ℤ ((dJ : E) * J i j))
    (e : Af F) (kk : HA (AF F) σ J) (N : ℕ)
    (h : ∀ i j, ∃ o ∈ Oh F E, (e ⊗ₜ[F] (1 : E)) * (finMat σ J kk⁻¹ - 1) i j = (dI * dJ * N) • o) :
    ∀ i j, ∃ o ∈ Oh F E, (e ⊗ₜ[F] (1 : E)) * (finMat σ J kk - 1) i j = N • o := by
  choose o ho hoe using h
  set U := finMat σ J kk with hUd
  set W := finMat σ J kk⁻¹ with hWd
  set JI := (J⁻¹).map (inclR (F := F) (Af F)) with hJId
  set JA := JR (F := F) (Af F) J with hJAd
  set sg := PI.UJClassFin.sigR (Af F) σ with hsg
  have hJI : JI * JA = 1 := by
    rw [hJId, hJAd, JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hJ), Matrix.map_one _ (map_zero _) (map_one _)]
  have hWU : W * U = 1 := by rw [hWd, hUd, ← finMat_mul, inv_mul_cancel, finMat_one]
  have hunit : PI.UJClassFin.cT sg W * JA * W = JA := finMat_unitary σ J kk⁻¹
  have hU : U = JI * PI.UJClassFin.cT sg W * JA := by
    calc U = JI * JA * U := by rw [hJI, Matrix.one_mul]
      _ = JI * (PI.UJClassFin.cT sg W * JA * W) * U := by rw [hunit]
      _ = JI * PI.UJClassFin.cT sg W * JA * (W * U) := by simp only [Matrix.mul_assoc]
      _ = JI * PI.UJClassFin.cT sg W * JA := by rw [hWU, Matrix.mul_one]
  have hcs : PI.UJClassFin.cT sg (W - 1) = PI.UJClassFin.cT sg W - 1 := by
    have h1 := PI.UJClassFin.cT_one (n := Fin M) sg
    unfold PI.UJClassFin.cT at h1 ⊢
    rw [Matrix.map_sub _ (map_sub _), Matrix.transpose_sub, h1]
  have hU1 : U - 1 = JI * PI.UJClassFin.cT sg (W - 1) * JA := by
    rw [hU, hcs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJI]
  have key : ∀ a b, (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) = (dI * dJ * N) • sg (o b a) := by
    intro a b
    calc (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) = sg (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) := by
          rw [hsg, sigR_tmul_one]
      _ = sg ((e ⊗ₜ[F] (1 : E)) * (W - 1) b a) := (map_mul _ _ _).symm
      _ = sg ((dI * dJ * N) • o b a) := by rw [hoe b a]
      _ = (dI * dJ * N) • sg (o b a) := map_nsmul _ _ _
  intro i j
  refine ⟨∑ a, ∑ b, inclR (F := F) (Af F) ((dI : E) * J⁻¹ i a) * sg (o b a) *
      inclR (F := F) (Af F) ((dJ : E) * J b j),
    AddSubgroup.sum_mem _ fun a _ => AddSubgroup.sum_mem _ fun b _ =>
      Oh_mul (Oh_mul (incl_mem_Oh (hdI i a)) (sigR_Oh σ (ho b a))) (incl_mem_Oh (hdJ b j)), ?_⟩
  rw [hU1]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hk := key a b
  have hX : PI.UJClassFin.cT sg (W - 1) a b = sg ((W - 1) b a) := rfl
  have hJI' : JI i a = inclR (F := F) (Af F) (J⁻¹ i a) := rfl
  have hJA' : JA b j = inclR (F := F) (Af F) (J b j) := rfl
  rw [hX, hJI', hJA', map_mul, map_mul, map_natCast, map_natCast]
  calc (e ⊗ₜ[F] (1 : E)) * (inclR (F := F) (Af F) (J⁻¹ i a) * sg ((W - 1) b a) * inclR (F := F) (Af F) (J b j))
      = inclR (F := F) (Af F) (J⁻¹ i a) * ((e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a)) *
          inclR (F := F) (Af F) (J b j) := by ring
    _ = _ := by
      rw [hk]
      simp only [nsmul_eq_mul]
      push_cast
      ring

end Loc

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem resChar {E : Type} [Field E] [NumberField E] (P : Ideal (𝓞 E)) (hP : P.IsMaximal) :
    ∃ p : ℕ, p.Prime ∧ ∀ m : ℕ, ¬ p ∣ m → (m : 𝓞 E) ∉ P := by
  letI := Ideal.Quotient.field P
  set p := ringChar (𝓞 E ⧸ P)
  haveI : CharP (𝓞 E ⧸ P) p := ringChar.charP _
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hmem : ((Ideal.absNorm P : ℕ) : 𝓞 E) ∈ P := Ideal.absNorm_mem P
  have hN0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hdvd : p ∣ Ideal.absNorm P := (CharP.cast_eq_zero_iff (𝓞 E ⧸ P) p _).1 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hmem)
  have hp0 : p ≠ 0 := fun h => hN0 (by rw [h] at hdvd; exact zero_dvd_iff.1 hdvd)
  have hpr : p.Prime := (CharP.char_is_prime_or_zero (𝓞 E ⧸ P) p).resolve_right hp0
  refine ⟨p, hpr, fun m hm hmP => hm ?_⟩
  exact (CharP.cast_eq_zero_iff (𝓞 E ⧸ P) p m).1 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hmP)

theorem lsLoc : LSLoc := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig g P hP
  classical
  let J := gramOf h b
  set L := crdOf b L0 with hLd

  have hσσ : ∀ e, σ (σ e) = e := fun e => by rw [hσ, hσ, star_star]
  have hH : PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J := by
    show PI.UnitaryApproxDefs.cT (σ : E →+* E) (gramOf h b) = gramOf h b
    ext i j
    simp only [PI.UnitaryApproxDefs.cT, Matrix.transpose_apply, Matrix.map_apply, gramOf]
    have := hs.eq (b j) (b i)
    rw [starRingEnd_apply] at this
    rw [show (σ : E →+* E) (h (b j) (b i)) = σ (h (b j) (b i)) from rfl, hσ]
    exact this
  have hJdet : J.det ≠ 0 := by
    intro h0
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (posDefOfDefiniteSignature_holds M _ (hsig τ)).isUnit
    have e : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [e, h0, map_zero] at hu'
    exact not_isUnit_zero hu'
  obtain ⟨dJ, hdJ, hdJi⟩ := mat_den J
  obtain ⟨dI, hdI, hdIi⟩ := mat_den J⁻¹

  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL
  obtain ⟨u, hu, hu'⟩ := up_nat L ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat L ⟨c2, hc2, hlow⟩
  obtain ⟨m', hm', hmO'⟩ := den_mat (F := F) (E := E) (finMat σ J g⁻¹)

  obtain ⟨p, hpr, hpm⟩ := resChar P hP
  set T : Set (HeightOneSpectrum (𝓞 F)) := {w | (p : 𝓞 F) ∈ w.asIdeal} with hTd
  have hpF : (p : 𝓞 F) ≠ 0 := by exact_mod_cast hpr.ne_zero
  have hfin : T.Finite := (Ideal.finite_factors (I := Ideal.span {(p : 𝓞 F)})
    (by rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hpF)).subset
      (fun w hw => Ideal.dvd_span_singleton.2 hw)
  have hpT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → (p : 𝓞 F) ∉ w.asIdeal := fun w hw => hw

  set N1 := u * k with hN1
  set N0 := dI * dJ * N1 with hN0
  obtain ⟨γ, hγ⟩ := approxT σ J hσσ hθ hH (isUnit_iff_ne_zero.2 hJdet) g hfin.toFinset (m' * N0)
    (by positivity)
  rw [Set.Finite.coe_toFinset] at hγ
  set ε : Af F ⊗[F] E := evT T ⊗ₜ[F] (1 : E) with hε

  have small1 : ∀ i j, ∃ o ∈ Oh F E,
      ε * (finMat σ J (g⁻¹ * emb σ J γ) - 1) i j = (dI * dJ * N1) • o := by
    choose o ho hoe using hγ
    intro i j
    refine ⟨∑ l, -((m' • finMat σ J g⁻¹ i l) * o l j),
      AddSubgroup.sum_mem _ fun l _ => neg_mem (Oh_mul (hmO' i l) (ho l j)), ?_⟩
    have hPQ : finMat σ J g⁻¹ * finMat σ J g = 1 := by rw [← finMat_mul, inv_mul_cancel, finMat_one]
    have e1 : finMat σ J (g⁻¹ * emb σ J γ) - 1 =
        finMat σ J g⁻¹ * (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (Af F)) - finMat σ J g) := by
      rw [finMat_mul, finMat_emb, Matrix.mul_sub, hPQ]
    rw [e1, Matrix.mul_apply, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hl := hoe l j
    simp only [Matrix.sub_apply, Matrix.map_apply] at hl ⊢
    have e2 : ε * (finMat σ J g⁻¹ i l * (inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) l j) - finMat σ J g l j)) =
        -(finMat σ J g⁻¹ i l * (ε * (finMat σ J g l j - inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) l j)))) := by
      ring
    rw [e2, hl, hN0]
    simp only [nsmul_eq_mul, smul_neg]
    push_cast
    ring
  have small2 := invSmall σ J hJdet hdIi hdJi (evT T) ((emb σ J γ)⁻¹ * g) N1 (by
    rw [mul_inv_rev, inv_inv]; exact small1)
  have hεI : evT T ∈ intAf F := evT_int T
  have condA : ∀ y ∈ latHat F E L, ε • (finMat σ J (g⁻¹ * emb σ J γ)).mulVec y ∈ latHat F E L :=
    fun y hy => stabT L hu' hk' hεI _ (fun i j => by
      obtain ⟨o, ho, hoe⟩ := small1 i j
      exact ⟨(dI * dJ) • o, AddSubgroup.nsmul_mem _ ho _, by rw [hoe, smul_smul]; congr 1; rw [hN1]; ring⟩) hy
  have condB : ∀ y ∈ latHat F E L, ε • (finMat σ J ((emb σ J γ)⁻¹ * g)).mulVec y ∈ latHat F E L :=
    fun y hy => stabT L hu' hk' hεI _ small2 hy

  have hgen : ∀ m : ℕ, ¬ p ∣ m → ((m : 𝓞 E)) ∈ hcompl (K := E) P := fun m hm =>
    Submonoid.subset_closure ⟨hpm m hm, fun t ht => by
      have : t = (m : 𝓞 E) := by
        apply RingOfIntegers.coe_injective
        have ht' : algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E (m : 𝓞 E) := by
          rw [ht, map_natCast, star_natCast]
        simpa using ht'
      rw [this]; exact hpm m hm⟩
  refine ⟨⟨emb σ J γ, emb_mem σ J γ⟩, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨m2, hm2, hmx⟩ := locCmpT σ J L hk hk' T p hpr.ne_zero hpr.one_lt.ne' hpT g (emb σ J γ)
      condB hsx
    refine ⟨s * (m2 : 𝓞 E), Submonoid.mul_mem _ hs (hgen m2 hm2), ?_⟩
    rw [map_mul, map_natCast, mul_comm, mul_smul]
    exact hmx
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨m2, hm2, hmx⟩ := locCmpT σ J L hk hk' T p hpr.ne_zero hpr.one_lt.ne' hpT (emb σ J γ) g
      (fun y hy => by simpa using condA y hy) hsx
    refine ⟨s * (m2 : 𝓞 E), Submonoid.mul_mem _ hs (hgen m2 hm2), ?_⟩
    rw [map_mul, map_natCast, mul_comm, mul_smul]
    exact hmx

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LsLat
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem lsLat : LSLat := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig g
  set L := crdOf b L0 with hLdef
  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL
  obtain ⟨u, hu, hu'⟩ := up_nat L ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat L ⟨c2, hc2, hlow⟩
  set P := finMat σ (gramOf h b) g⁻¹ with hP
  set Q := finMat σ (gramOf h b) g with hQ
  have hQP : Q * P = 1 := by rw [hQ, hP, ← finMat_mul, mul_inv_cancel, finMat_one]

  have hsm : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ abelian₂ σ (gramOf h b) L g, e • x ∈ abelian₂ σ (gramOf h b) L g := by
    intro e he x hx
    show P.mulVec (vinc (F := F) (e • x)) ∈ latHat F E L
    rw [vinc_smul, Matrix.mulVec_smul]
    exact latHat_incl_smul b L0 he hx
  let C : Submodule (𝓞 E) (Fin M → E) :=
    { carrier := abelian₂ σ (gramOf h b) L g
      add_mem' := fun {x y} hx hy => (LamG σ (gramOf h b) L g).add_mem hx hy
      zero_mem' := (LamG σ (gramOf h b) L g).zero_mem
      smul_mem' := fun c x hx => by
        show (algebraMap (𝓞 E) E c) • x ∈ abelian₂ σ (gramOf h b) L g
        exact hsm _ c.isIntegral_coe x hx }

  obtain ⟨m, hm, hmO⟩ := den_mat (F := F) (E := E) Q
  have hupC : ∀ y ∈ C, ∀ j, IsIntegral ℤ (((m * u : ℕ) : E) * y j) := by
    intro y hy j
    apply oh_inter (F := F)
    have hw : P.mulVec (vinc (F := F) y) ∈ latHat F E L := hy
    have ev : vinc (F := F) y = Q.mulVec (P.mulVec (vinc (F := F) y)) := by
      rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
    have e1 : inclR (F := F) (Af F) (((m * u : ℕ) : E) * y j) =
        ∑ l, (m • Q j l) * (u • P.mulVec (vinc (F := F) y) l) := by
      have : inclR (F := F) (Af F) (((m * u : ℕ) : E) * y j) = (m * u) • vinc (F := F) y j := by
        simp [vinc, nsmul_eq_mul]
      have gen : ∀ w : Fin M → Af F ⊗[F] E,
          (m * u) • Q.mulVec w j = ∑ l, (m • Q j l) * (u • w l) := by
        intro w
        simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, nsmul_eq_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        push_cast
        ring
      rw [this, ← gen, ← ev]
    rw [e1]
    exact AddSubgroup.sum_mem _ fun l _ => Oh_mul (hmO j l) (up_Oh L hu' hw l)
  have hCfg : C.FG := fg_of_den C (m * u) (Nat.mul_pos hm hu) hupC

  obtain ⟨m', hm', hmO'⟩ := den_mat (F := F) (E := E) P
  set c : E := ((k * m' : ℕ) : E) with hc
  have hcne : c ≠ 0 := by rw [hc]; exact_mod_cast (Nat.mul_pos hk hm').ne'
  have hlowC : ∀ i, (Pi.single i c : Fin M → E) ∈ abelian₂ σ (gramOf h b) L g := by
    intro i
    show P.mulVec (vinc (F := F) (Pi.single i c)) ∈ latHat F E L
    have e1 : vinc (F := F) (Pi.single i c) = Pi.single i (inclR (F := F) (Af F) c) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [vinc]
      · simp [vinc, Pi.single_apply, hj]
    have e2 : P.mulVec (Pi.single i (inclR (F := F) (Af F) c)) = k • fun l => m' • P l i := by
      rw [mulVec_single']
      funext l
      simp only [Pi.smul_apply, hc, map_natCast, nsmul_eq_mul]
      push_cast
      ring
    rw [e1, e2]
    exact low_vec L hk' fun l => hmO' l i

  let f : (Fin M → E) →ₗ[𝓞 E] V := (b.equivFun.symm : (Fin M → E) →ₗ[E] V).restrictScalars (𝓞 E)
  let N : Submodule (𝓞 E) V := C.map f
  have hNset : (N : Set V) = latSet σ (gramOf h b) b L0 g := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      show b.equivFun (b.equivFun.symm x) ∈ abelian₂ σ (gramOf h b) L g
      rw [LinearEquiv.apply_symm_apply]; exact hx
    · intro hv
      exact ⟨b.equivFun v, hv, by simp [f]⟩
  have hNfull : Submodule.IsFullLattice E N := by
    refine { toIsLattice := Submodule.IsLattice.of_fg E (hCfg.map f), span_eq_top := ?_ }
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hb : c • b i ∈ (N : Set V) := by
      rw [hNset]
      show b.equivFun (c • b i) ∈ abelian₂ σ (gramOf h b) L g
      have hcrd : b.equivFun (c • b i) = Pi.single i c := by
        funext j
        rw [LinearEquiv.map_smul, Pi.smul_apply, b.equivFun_self]
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj, Ne.symm hj]
      rw [hcrd]
      exact hlowC i
    have hi : b i = c⁻¹ • (c • b i) := by rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
    rw [hi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hb)
  exact ⟨N, hNset, hNfull⟩

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem lattice_modification : LatStep := latStep_of_parts lsLat lsOne lsLoc

end PI.UnitaryGroupMassFormula.UJClassMass
