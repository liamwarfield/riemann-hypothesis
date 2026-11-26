module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicNormTransitionDetOne
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameOpen
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenLocalBasisLogNorm
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GOntoKer
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ImHermFormEqCurveForm
public import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsFactorThroughMultiplication
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GIntFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCmPeriodEmbedding

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentTwistedGeneratorExists
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentTwistedGeneratorExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.RelDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt_sq_field (H : Host E) : ((H.rt : E)) ^ 2 = -(H.d : E) := by
  have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  rw [map_pow, map_neg, map_natCast] at h
  exact h

theorem rt_ne_zero (H : Host E) : (H.rt : E) ≠ 0 := by
  intro h
  have h1 := rt_sq_field H
  rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h1
  exact H.d_prime.ne_zero h1

theorem conj_eq_neg_of_sq {z : ℂ} {d : ℝ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero] at hre him
  have h0 : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by nlinarith) with h | h
    · exact h
    · rw [h] at hre
      nlinarith [sq_nonneg z.re]
  apply Complex.ext <;> simp [h0]

theorem conj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  let φ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply conj_eq_neg_of_sq (d := (H.d : ℝ)) (by exact_mod_cast H.d_prime.pos)
  rw [← map_pow, rt_sq_field, map_neg, map_natCast]
  simp

theorem exists_local_generator (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) :
    ∃ δ : E, δ ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ],
      Real.log ‖j δ‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (H.rt : E)‖ ∧
      Real.log ‖j (IsCMField.complexConj E δ)‖ = Real.log ‖j δ‖ := by
  obtain ⟨δ₀, -, hδ₀, hconj, hlog⟩ := GlobalTheory.T.exists_real_different_generator E H.unram ℓ
  have hrt : (H.rt : E) ≠ 0 := rt_ne_zero H
  have hδ₀E : (δ₀ : E) ≠ 0 := by exact_mod_cast hδ₀
  refine ⟨(δ₀ : E) / (H.rt : E), div_ne_zero hδ₀E hrt, fun j => ⟨?_, ?_⟩⟩
  · rw [map_div₀, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hδ₀E))
        (norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hrt)), hlog]
  · rw [map_div₀, hconj, conj_rt H, div_neg, map_neg, norm_neg]

end GlobalTheory.CompanionTheory.Ar.Fl.RelDiff
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentTwistedGeneratorExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_twisted_generator_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes), ∃ δ : E, δ ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j δ‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (H.rt : E)‖ ∧ Real.log ‖j (IsCMField.complexConj E δ)‖ = Real.log ‖j δ‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.exists_local_generator | exact GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.exists_local_generator | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.exists_local_generator <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisCmOrder
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisCmOrder
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : ℕ), ℓ.Prime → ∃ (f : ℕ) (b : Fin f → 𝓞 E), 2 * f = Module.finrank ℚ E ∧ IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b := by
  first | exact @PositivityTheory.Xgf.exists_local_basis_cm_order | exact PositivityTheory.Xgf.exists_local_basis_cm_order
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisCmOrderStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_basis_cm_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : ℕ), ℓ.Prime → ∃ (f : ℕ) (b : Fin f → 𝓞 E), 2 * f = Module.finrank ℚ E ∧ IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order | exact GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Rt0ConjNegNeZero
theorem UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    (starRingEnd ℂ : ℂ → ℂ) H.rt0 =
      -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [sq] at h1 h2
  have hre : H.rt0.re = 0 := by
    by_contra hne
    have him : H.rt0.im = 0 := mul_left_cancel₀ hne (by linarith)
    rw [him] at h1
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [hre]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureNorm
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackProductFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsogenyProductDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNthRootHomomorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNthRootHomomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_nth_root_homomorphism : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n : ℕ) (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A), IsMonHom f → 0 < n → (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A, x ^ n = 1 → x ≫ f = 1) → ∃ f' : A.A ⟶ B.A, IsMonHom f' ∧ f' ^ n = f := by
  first | exact @PositivityTheory.Xgf.exists_nth_root_homomorphism | exact PositivityTheory.Xgf.exists_nth_root_homomorphism
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNthRootHomomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nth_root_homomorphism : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n : ℕ) (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A), IsMonHom f → 0 < n → (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A, x ^ n = 1 → x ≫ f = 1) → ∃ f' : A.A ⟶ B.A, IsMonHom f' ∧ f' ^ n = f := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_nth_root_homomorphism | exact GlobalTheory.CompanionTheory.Relay.exists_nth_root_homomorphism | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_nth_root_homomorphism <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsogenyProductDecomposition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ggeo.GBack

variable {K : Type} [Field K] [NumberField K]

theorem exists_prodFam (B : Out.PolAV (Sp (𝓞 K))) : ∀ (n : ℕ) (C : Fin n → Out.PolAV (Sp (𝓞 K))),
    ∃ (Q : Out.PolAV (Sp (𝓞 K))) (a : ∀ k, Q.A ⟶ (C k).A), (∀ k, IsMonHom (a k)) ∧ Q.g = ∑ k, (C k).g ∧
      (∀ (T : Over (Sp (𝓞 K))) (x : ∀ k, T ⟶ (C k).A), ∃ z : T ⟶ Q.A, ∀ k, z ≫ a k = x k) ∧
      ∀ (T : Over (Sp (𝓞 K))) (z z' : T ⟶ Q.A), (∀ k, z ≫ a k = z' ≫ a k) → z = z' := by
  intro n
  induction n with
  | zero =>
    intro C
    obtain ⟨P, pP, hP⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) B 0
    refine ⟨P, fun k => Fin.elim0 k, fun k => Fin.elim0 k, by simp [hP], fun T x => ?_, fun T z z' _ => ?_⟩
    · exact ⟨pP.lim.lift (Fan.mk T fun i => Fin.elim0 i), fun k => Fin.elim0 k⟩
    · exact pP.lim.hom_ext fun j => Fin.elim0 j.as
  | succ n ih =>
    intro C
    obtain ⟨Q', a', ha', hg', hex', hext'⟩ := ih fun k => C k.succ
    obtain ⟨Q, u, v, hu, hv, huv, hQ⟩ := GlobalTheory.T.exists_prod_polAV_add_g GlobalTheory.CMClaims.laws (𝓞 K) (C 0) Q'
    refine ⟨Q, Fin.cases u fun j => v ≫ a' j, fun k => ?_, ?_, fun T x => ?_, fun T z z' h => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) k
      · exact hu
      · haveI := hv; haveI := ha' j; show IsMonHom (v ≫ a' j); infer_instance
    · rw [hQ, hg', Fin.sum_univ_succ]
    · obtain ⟨z', hz'⟩ := hex' T fun j => x j.succ
      have e1 : inv (lift u v) ≫ u = fst _ _ := by rw [IsIso.inv_comp_eq, lift_fst]
      have e2 : inv (lift u v) ≫ v = snd _ _ := by rw [IsIso.inv_comp_eq, lift_snd]
      refine ⟨lift (x 0) z' ≫ inv (lift u v), fun k => Fin.cases ?_ (fun j => ?_) k⟩
      · show (lift (x 0) z' ≫ inv (lift u v)) ≫ u = x 0
        rw [Category.assoc, e1, lift_fst]
      · show (lift (x 0) z' ≫ inv (lift u v)) ≫ v ≫ a' j = x j.succ
        rw [Category.assoc, reassoc_of% e2, lift_snd_assoc, hz']
    · rw [← cancel_mono (lift u v)]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [Category.assoc, lift_fst]
        exact h 0
      · simp only [Category.assoc, lift_snd]
        exact hext' T _ _ fun j => by
          have := h j.succ
          simp only [Fin.cases_succ] at this
          simpa only [Category.assoc] using this

theorem isMonHom_pow {G H : Over (Sp (𝓞 K))} [GrpObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f] (N : ℕ) :
    IsMonHom (f ^ N) :=
  GlobalTheory.LamF.IsogSum.isMonHom_of_points _ fun T x y => by
    rw [MonObj.comp_pow, MonObj.comp_pow, MonObj.comp_pow, MonObj.mul_comp, mul_pow]

end GlobalTheory.CompanionTheory.Ggeo.GBack

open GlobalTheory.CompanionTheory.Ggeo.GBack in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.isogeny_product_decomposition : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n N : ℕ) (C : Fin n → Out.PolAV (Sp (𝓞 K))) (B : Out.PolAV (Sp (𝓞 K))) (ψ : ∀ k, (C k).A ⟶ B.A), (∀ k, IsMonHom (ψ k)) → 0 < N → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ x : ∀ k, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (C k).A, y = (List.ofFn fun k => x k ≫ ψ k).prod) → (∀ x : ∀ k, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (C k).A, (List.ofFn fun k => x k ≫ ψ k).prod = 1 → ∀ k, x k ^ N = 1) → ∃ χ : ∀ k, B.A ⟶ (C k).A, (∀ k, IsMonHom (χ k)) ∧ (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) ∧ ∀ k k', k ≠ k' → ψ k ≫ χ k' = 1 := by
  intro K _ _ σ n N C B ψ hψ hN hon hker
  have hNo : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  obtain ⟨Q, a, ha, hQg, hex, hext⟩ := exists_prodFam B n C
  have := B.isAb.comm
  have := Q.isAb.comm
  have hCc : ∀ k, IsCommMonObj (C k).A := fun k => (C k).isAb.comm
  let Φ : Q.A ⟶ B.A := ∏ k, a k ≫ ψ k
  have hΦ : ∀ {T : Over (Sp (𝓞 K))} (x : T ⟶ Q.A), x ≫ Φ = ∏ k, (x ≫ a k) ≫ ψ k := by
    intro T x
    simp only [Φ, GlobalTheory.LamF.IsogSum.comp_prod, Category.assoc]
  have hm : IsMonHom Φ := GlobalTheory.LamF.IsogSum.isMonHom_of_points Φ fun T x y => by
    simp only [hΦ, MonObj.mul_comp, Finset.prod_mul_distrib]
  let t : Sp ℂ ⟶ Sp (𝓞 K) := spMap (σ.comp (algebraMap (𝓞 K) K))
  have onto : ∀ y : Over.mk t ⟶ B.A, ∃ z : Over.mk t ⟶ Q.A, y = z ≫ Φ := by
    intro y
    obtain ⟨x, hx⟩ := hon y
    obtain ⟨z, hz⟩ := hex _ x
    refine ⟨z, ?_⟩
    rw [hΦ, hx, List.prod_ofFn]
    simp only [hz]
  have kerN : ∀ z : Over.mk t ⟶ Q.A, z ≫ Φ = 1 → z ^ N = 1 := by
    intro z hz
    have h1 := hker (fun k => z ≫ a k) (by rw [List.prod_ofFn, ← hΦ]; exact hz)
    apply hext
    intro k
    rw [MonObj.pow_comp, h1 k, MonObj.one_comp]
  have hg : Q.g = B.g := by
    let F : (Over.mk t ⟶ Q.A) →* (Over.mk t ⟶ B.A) := MonoidHom.mk' (· ≫ Φ) fun x y => MonObj.mul_comp x y Φ
    obtain ⟨m, hmN⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    have e := GlobalTheory.CMClaims.card_torsion_eq F (fun y => (onto y).imp fun _ h => h.symm) m
      (fun x hx => hmN ▸ kerN x hx)
    have h0 : ((m + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
    rw [(GlobalTheory.CMClaims.laws.mulN _ Q (m + 2) (by omega)).2.2.2.2 ℂ t h0,
      (GlobalTheory.CMClaims.laws.mulN _ B (m + 2) (by omega)).2.2.2.2 ℂ t h0] at e
    have := Nat.pow_right_injective (by omega : 2 ≤ m + 2) e
    omega
  obtain ⟨N₀, ψ₀, hN₀, hψ₀, h1, h2⟩ := GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers GlobalTheory.thetaUnifAV_all
    GlobalTheory.CMClaims.laws GlobalTheory.CMClaims.homExt K σ Q B Φ hg hm onto
  have divQ : ∀ q : Over.mk t ⟶ Q.A, ∃ q', q = q' ≫ (𝟙 Q.A ^ N₀) := by
    intro q
    have := (GlobalTheory.CMClaims.laws.mulN _ Q N₀ hN₀).1
    have := (GlobalTheory.CMClaims.laws.mulN _ Q N₀ hN₀).2.2.1
    exact GlobalTheory.CMClaims.onto_points (𝟙 Q.A ^ N₀) t q
  have cancel : ∀ (Z : Out.PolAV (Sp (𝓞 K))) (X Y : Q.A ⟶ Z.A), (𝟙 Q.A ^ N₀) ≫ X = (𝟙 Q.A ^ N₀) ≫ Y → X = Y := by
    intro Z X Y h
    have := Q.isAb.smooth
    have := Z.isAb.proper
    refine GlobalTheory.CMPointCompare.hom_ext_of_complexPoints (σ.comp (algebraMap (𝓞 K) K))
      (σ.injective.comp (IsFractionRing.injective (𝓞 K) K)) fun q => ?_
    obtain ⟨q', rfl⟩ := divQ q
    rw [Category.assoc, Category.assoc, h]
  have hf : ∀ k, IsMonHom ((ψ₀ ≫ a k) ^ N) := fun k => by
    have := ha k
    exact isMonHom_pow (ψ₀ ≫ a k) N
  have kill : ∀ k (b : Over.mk t ⟶ B.A), b ^ N₀ = 1 → b ≫ (ψ₀ ≫ a k) ^ N = 1 := by
    intro k b hb
    obtain ⟨z, rfl⟩ := onto b
    have e1 : (z ^ N₀) ≫ Φ = 1 := by rw [MonObj.pow_comp, hb]
    have e2 := kerN _ e1
    rw [MonObj.comp_pow]
    simp only [Category.assoc]
    rw [reassoc_of% h1, ← Category.assoc, MonObj.comp_pow, Category.comp_id, ← MonObj.pow_comp, e2, MonObj.one_comp]
  choose χ hχ hχe using fun k => GlobalTheory.T.exists_nth_root_homomorphism K σ N₀ B (C k) ((ψ₀ ≫ a k) ^ N) (hf k) hN₀ (kill k)
  have key : ∀ k, Φ ≫ χ k = a k ^ N := by
    intro k
    apply cancel (C k)
    have := hχ k
    rw [← h1, Category.assoc, ← Category.assoc ψ₀, h2, MonObj.pow_comp, Category.id_comp, hχe k, MonObj.comp_pow,
      ← Category.assoc, h1, MonObj.comp_pow]
  refine ⟨χ, hχ, ?_⟩
  have inc : ∀ k, ∃ z : (C k).A ⟶ Q.A, ∀ j, z ≫ a j = if h : k = j then eqToHom (by rw [h]) else 1 :=
    fun k => hex _ fun j => if h : k = j then eqToHom (by rw [h]) else 1
  choose inc hinc using inc
  have hincPhi : ∀ k, inc k ≫ Φ = ψ k := by
    intro k
    rw [hΦ, Finset.prod_eq_single k]
    · rw [hinc, dite_eq_left rfl, eqToHom_refl, Category.id_comp]
    · intro j _ hj
      rw [hinc, dite_eq_right (Ne.symm hj), MonObj.one_comp]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hψχ : ∀ k k', ψ k ≫ χ k' = (inc k ≫ a k') ^ N := by
    intro k k'
    rw [← hincPhi, Category.assoc, key, MonObj.comp_pow]
  refine ⟨fun k => ?_, fun k k' hk => ?_⟩
  · rw [hψχ, hinc, dite_eq_left rfl, eqToHom_refl]
  · rw [hψχ, hinc, dite_eq_right hk, one_pow]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsogenyProductDecompositionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_product_decomposition : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n N : ℕ) (C : Fin n → Out.PolAV (Sp (𝓞 K))) (B : Out.PolAV (Sp (𝓞 K))) (ψ : ∀ k, (C k).A ⟶ B.A), (∀ k, IsMonHom (ψ k)) → 0 < N → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ x : ∀ k, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (C k).A, y = (List.ofFn fun k => x k ≫ ψ k).prod) → (∀ x : ∀ k, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (C k).A, (List.ofFn fun k => x k ≫ ψ k).prod = 1 → ∀ k, x k ^ N = 1) → ∃ χ : ∀ k, B.A ⟶ (C k).A, (∀ k, IsMonHom (χ k)) ∧ (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) ∧ ∀ k k', k ≠ k' → ψ k ≫ χ k' = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.isogeny_product_decomposition | exact GlobalTheory.CompanionTheory.Relay.isogeny_product_decomposition | (intros; apply GlobalTheory.CompanionTheory.Relay.isogeny_product_decomposition <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackTorsionPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_pack_torsion_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ y : Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ X.B.t.G, ∃ x : ∀ k, Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ (X.C (b k)).P.A, y = (List.ofFn fun k => x k ≫ X.ψ (b k) (a k)).prod) ∧ ∀ x : ∀ k, Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ (X.C (b k)).P.A, (List.ofFn fun k => x k ≫ X.ψ (b k) (a k)).prod = 1 → ∀ k, x k ^ N = 1 := by
  first | exact @PositivityTheory.Xgf.cm_pack_torsion_points | exact PositivityTheory.Xgf.cm_pack_torsion_points
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsogenyDecompositionProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

open PositivityTheory.Xgf.isogeny_decomposition_product in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.isogeny_decomposition_product : ∀ (R V : Type) [CommRing R] [CommRing V] [IsLocalRing V] (f : R →+* V) (n N : ℕ) (C : Fin n → Out.PolAV (Sp R)) (v : ∀ k, epsR R ⟶ (C k).A) (B : Out.PolAV (Sp R)) (ψ : ∀ k, (C k).A ⟶ B.A) (χ : ∀ k, B.A ⟶ (C k).A) (G : Over (Sp V)) [GrpObj G] (π : G.left ⟶ B.A.left), B.g = n → (∀ k, IsLieBasis ![v k]) → (∀ k, IsMonHom (ψ k)) → (∀ k, IsMonHom (χ k)) → (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) → (∀ k k', k ≠ k' → ψ k ≫ χ k' = 1) → IsUnit (N : V) → IsGrpPullback G B.A (spMap f) π → ∃ u : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G), (∀ k, (u k).left ≫ π = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left) ∧ (∀ k, IsTanAt G _ (u k)) ∧ ∀ w, IsTanAt G _ w → ∃! cc : Fin n → V, IsComb cc u w := by
  intro R V _ _ _ f n N C v B ψ χ G _ π hg hv hψ hχ hpc hpo hN hpb
  obtain ⟨EBR, _, _, ⟨MBR⟩⟩ := lieModel_exists (Sp R) B.A R (𝟙 (Sp R))
  obtain ⟨EBV, _, _, ⟨MBV⟩⟩ := lieModel_exists (Sp R) B.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) B.A R V f (𝟙 _) EBR EBV MBR MBV
  have hx : spMap f ≫ 𝟙 (Sp R) = 𝟙 (Sp V) ≫ spMap f := by simp
  obtain ⟨MG, hMG⟩ := (GlobalTheory.T.lie_model_pullback_equivalence (Sp R) (Sp V) B.A G (spMap f) π hpb V (𝟙 (Sp V)) EBV).1 (castM hx MBV)
  have hMG' : ∀ e, (MG.pt e).left ≫ π = (MBV.pt e).left := fun e => (hMG e).trans (castM_left hx MBV e)

  have hvt : ∀ k, IsTanAt B.A (𝟙 (Sp R)) (toAt (v k) ≫ ψ k) := fun k => by
    haveI := hψ k; exact tan_comp _ (toAt_tan (v k) ((hv k).1 0)) (ψ k)
  choose eR heR using fun k => MBR.onto _ (hvt k)
  let EV : Fin n → EBV := fun k => j (eR k)
  have hlift : ∀ e, (MBV.pt (j e)).left = spMap (dualMap f) ≫ (MBR.pt e).left := fun e =>
    (Category.comp_id (MBV.pt (j e)).left).symm.trans (hj e)
  have hEV : ∀ k, (MBV.pt (EV k)).left = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left := fun k => by
    show (MBV.pt (j (eR k))).left = _
    rw [hlift, heR, Over.comp_left, toAt_left]

  choose EC iC mC MC bC hbC using fun k => lc (C k) (v k) (hv k) V f
  have hd : ∀ k, ∃ A : EBV →ₗ[V] EC k, ∀ e, (MC k).pt (A e) = MBV.pt e ≫ χ k := fun k => by
    haveI := hχ k
    exact (GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff (Sp R) B.A (C k).A V (spMap f ≫ 𝟙 (Sp R)) EBV (EC k) MBV (MC k) (χ k)).exists
  choose dχ hdχ using hd
  let fV : Fin n → (EBV →ₗ[V] V) := fun k => ((bC k).coord 0).comp (dχ k)
  have hval : ∀ i k, fV k (EV i) = if i = k then (N : V) else 0 := by
    intro i k
    have hleft : ((MC k).pt (dχ k (EV i))).left = spMap (dualMap f) ≫ (v i).left ≫ (ψ i ≫ χ k).left := by
      rw [hdχ, Over.comp_left, hEV, Over.comp_left]; simp only [Category.assoc]
    split_ifs with hik
    · subst hik
      have e2 : dχ i (EV i) = (N : V) • bC i 0 := by
        apply (MC i).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpc, (MC i).smul, hbC, pow_left (v i) (hv i) N, ← Category.assoc, bc_eps, Category.assoc]
      simp [fV, e2]
    · have e2 : dχ k (EV i) = 0 := by
        apply (MC k).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpo i k hik, pt_zero, ← bc_one f]
        congr 1
        rw [← Over.comp_left, MonObj.comp_one]
      simp [fV, e2]
  obtain ⟨bB⟩ := GlobalTheory.T.lie_model_free_of_smooth (Sp R) B.A n (hg ▸ B.smoothDim) V (spMap f ≫ 𝟙 (Sp R)) EBV MBV
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.dual_family_is_basis V EBV n bB EV fV (N : V) hN hval
  have bridge := (GlobalTheory.T.lie_model_eigenvectors_action (Sp V) V G (𝟙 (Sp V)) EBV MG).1 n
  refine ⟨fun k => MG.pt (EV k), fun k => hMG' (EV k) ▸ hEV k, fun k => MG.tan _, fun w hw => ?_⟩
  obtain ⟨e, rfl⟩ := MG.onto w hw
  have hmem : e ∈ Submodule.span V (Set.range EV) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hmem
  refine ⟨c, (bridge c EV _).2 (by rw [hc]), fun c' hc' => ?_⟩
  have h1 := MG.inj ((bridge c' EV _).1 hc')
  rw [← hc] at h1
  have h2 := Fintype.linearIndependent_iff.1 hli (c' - c) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  funext i
  have := h2 i
  rw [Pi.sub_apply, sub_eq_zero] at this
  exact this
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackProductFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ggeo.IntBasis

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp [spMap, ← Spec.map_comp]

theorem dualMap_comp_alt {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    (dualMap b).comp (dualMap a) = dualMap (b.comp a) := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]

end GlobalTheory.CompanionTheory.Ggeo.IntBasis

open GlobalTheory.CompanionTheory.Ggeo.IntBasis in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (V : Subring X.K) [IsLocalRing V], 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ s : 𝓞 X.K, (s : X.K) ∈ V) → IsUnit (N : V) → ∃ (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (uV : Fin g → (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ k, IsTanAt T.G _ (uV k)) ∧ (∀ w, IsTanAt T.G _ w → ∃! cc : Fin g → V, IsComb cc uV w) ∧ ∀ k u, X.IsImage (b k) (a k) u → ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left, s ≫ X.m.φ = u.left ∧ s ≫ m''.φ = spMap (dualMap (algebraMap V X.K)) ≫ (uV k).left := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X N b a V _ hN hspan hV hNu
  classical
  let f : 𝓞 X.K →+* V := (algebraMap (𝓞 X.K) X.K).codRestrict V hV
  have hf : (algebraMap V X.K).comp f = algebraMap (𝓞 X.K) X.K := by ext; rfl
  obtain ⟨T', m0, hg⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap f) X.B
  have hψ : ∀ k, IsMonHom (X.ψ (b k) (a k)) := fun k => ((X.fam (b k)).1 (a k)).isMonHom
  obtain ⟨hon, hker⟩ := GlobalTheory.CompanionTheory.Relay.cm_pack_torsion_points E H D l Xo c g ty FU i Z P hP X N b a hN hspan
  obtain ⟨χ, hχ, hψχ, hoff⟩ := GlobalTheory.T.isogeny_product_decomposition X.K (algebraMap X.K ℂ) g N (fun k => (X.C (b k)).P) X.B.pol
    (fun k => X.ψ (b k) (a k)) hψ hN hon hker
  obtain ⟨uV, huV, htan, hbasis⟩ := GlobalTheory.CompanionTheory.Relay.isogeny_decomposition_product (𝓞 X.K) V f g N (fun k => (X.C (b k)).P) (fun k => (X.C (b k)).v)
    X.B.pol (fun k => X.ψ (b k) (a k)) χ T'.t.G m0.φ X.dim (fun k => (X.C (b k)).basis) hψ hχ hψχ hoff hNu m0.cart
  have hy : spMap (algebraMap V X.K) ≫ spMap f = spMap (algebraMap (𝓞 X.K) X.K) := by rw [spectrumMap_comp, hf]
  obtain ⟨m'', hm''⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 X.K) V X.K f (algebraMap V X.K)).2
    (Sp (𝓞 X.K)) (spMap f) (spMap (algebraMap (𝓞 X.K) X.K)) X.B.t T'.t X.t m0 X.m' hy
  refine ⟨T'.t, m'', uV, htan, hbasis, fun k u hu => ?_⟩
  obtain ⟨r, hr1, hr2⟩ := hu
  refine ⟨r, hr1, ?_⟩
  apply m0.cart.1.hom_ext
  · rw [Category.assoc, hm'', hr2, Category.assoc, huV k]
    simp only [← Category.assoc]
    congr 2
    rw [spectrumMap_comp, dualMap_comp_alt, hf]
  · have w1 := m''.cart.1.w
    have w2 := X.m'.cart.1.w
    have hmono : Mono (spMap (algebraMap (𝓞 X.K) X.K)) := by
      have : Epi (CommRingCat.ofHom (algebraMap (𝓞 X.K) X.K)) := IsLocalization.epi (nonZeroDivisors (𝓞 X.K)) X.K
      exact (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (𝓞 X.K) X.K)).op))
    have hbase : r ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
      apply hmono.right_cancellation
      rw [Category.assoc, ← w2, ← Category.assoc, hr2]
      simp only [Category.assoc]
      rw [Over.w (X.ψ (b k) (a k)), Over.w ((X.C (b k)).v)]
      simp only [Over.mk_hom, spectrumMap_comp]
      congr 1
      ext x <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]
    rw [Category.assoc, w1, ← Category.assoc, hbase, Category.assoc, Over.w (uV k)]
    simp only [Over.mk_hom, Category.comp_id]
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [spectrumMap_comp, spectrumMap_comp]
    congr 1
    ext x <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackProductFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_pack_product_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (V : Subring X.K) [IsLocalRing V], 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ s : 𝓞 X.K, (s : X.K) ∈ V) → IsUnit (N : V) → ∃ (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (uV : Fin g → (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ k, IsTanAt T.G _ (uV k)) ∧ (∀ w, IsTanAt T.G _ w → ∃! cc : Fin g → V, IsComb cc uV w) ∧ ∀ k u, X.IsImage (b k) (a k) u → ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left, s ≫ X.m.φ = u.left ∧ s ≫ m''.φ = spMap (dualMap (algebraMap V X.K)) ≫ (uV k).left := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame | exact GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame | (intros; apply GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExtendsOverDvr
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExtendsOverDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (K : Type) [Field K] (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))) (U : Type) [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I : Type) [Fintype I] (n r : ℕ) (e : Fin n ≃ I) (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (u : I → U) (v : Fin r → U), M.IsActOf Xo.univ.t.act.act ρ → (∀ a : 𝓞 E, σ (a : E) ∈ V) → (∀ k, IsTanAt T.G _ (uV k)) → (∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w) → (∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left, s ≫ m.φ = (M.pt (u (e k))).left ∧ s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) → LinearIndependent K v → Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range v) → LinearIndependent K u ∧ IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (v a)) := by
  first | exact @PositivityTheory.Xgf.lie_model_extends_over_dvr | exact PositivityTheory.Xgf.lie_model_extends_over_dvr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExtendsOverDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_extends_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (K : Type) [Field K] (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))) (U : Type) [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I : Type) [Fintype I] (n r : ℕ) (e : Fin n ≃ I) (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (u : I → U) (v : Fin r → U), M.IsActOf Xo.univ.t.act.act ρ → (∀ a : 𝓞 E, σ (a : E) ∈ V) → (∀ k, IsTanAt T.G _ (uV k)) → (∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w) → (∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left, s ≫ m.φ = (M.pt (u (e k))).left ∧ s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) → LinearIndependent K v → Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range v) → LinearIndependent K u ∧ IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (v a)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr | exact GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureNorm
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.GFin

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 :=
  _root_.UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero H

theorem card_emb {l : Level H} (c : Coeff l) (K : IntermediateField ℚ ℂ) (hc : c.F ≤ K) :
    Nat.card (E →+* K) = Module.finrank ℚ E := by
  have hm : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ K := fun τ a => hc (c.conj τ a)
  have e : (E →+* K) ≃ (E →+* ℂ) :=
    { toFun := fun φ => (algebraMap K ℂ).comp φ
      invFun := fun τ => τ.codRestrict K.toSubfield (hm τ)
      left_inv := fun φ => by ext a; rfl
      right_inv := fun τ => by ext a; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, NumberField.Embeddings.card]

theorem exists_frame {K : Type} [Field K] (V : Subring K) [IsDomain V] [IsPrincipalIdealRing V]
    [IsFractionRing V K] {U : Type} [AddCommGroup U] [Module K U] {I : Type} [Finite I] (u : I → U)
    (W : Submodule K U) : ∃ (r : ℕ) (v : Fin r → U), LinearIndependent K v ∧
      Submodule.span V (Set.range u) ⊓ W.restrictScalars V = Submodule.span V (Set.range v) := by
  set N : Submodule V U := Submodule.span V (Set.range u) ⊓ W.restrictScalars V with hN
  have hfg : (Submodule.span V (Set.range u)).FG := Submodule.fg_span (Set.finite_range u)
  haveI : Module.Finite V (Submodule.span V (Set.range u)) := Module.Finite.iff_fg.2 hfg
  haveI : IsNoetherian V (Submodule.span V (Set.range u)) := inferInstance
  have hNfg : N.FG := by
    have := IsNoetherian.noetherian (R := V) (M := Submodule.span V (Set.range u))
      (N.comap (Submodule.span V (Set.range u)).subtype)
    have h2 := this.map (Submodule.span V (Set.range u)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 (inf_le_left : N ≤ _)] at h2
  haveI : Module.Finite V N := Module.Finite.iff_fg.2 hNfg
  haveI : Module.IsTorsionFree V U := ⟨fun r hr a b h => by
    have hr0 : (r : K) ≠ 0 := fun e => hr.ne_zero (Subtype.ext e)
    exact smul_right_injective U hr0 h⟩
  haveI : Module.Free V N := Module.free_of_finite_type_torsion_free'
  let bs := Module.finBasis V N
  refine ⟨_, fun i => (bs i : U), ?_, ?_⟩
  · refine (LinearIndependent.iff_fractionRing V K).1 ?_
    exact bs.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  · have h2 : N = Submodule.span V (N.subtype '' Set.range bs) := by
      rw [← Submodule.map_span, bs.span_eq, Submodule.map_top, Submodule.range_subtype]
    refine h2.trans (congrArg _ ?_)
    rw [← Set.range_comp]
    rfl

theorem span_fam {La : Type} [AddCommGroup La] [Module (𝓞 E) La] {ℓ : ℕ} (hℓ : ℓ.Prime) {I J : Type} [Fintype I] [Fintype J]
    (x : I ⊕ J → La) {f : ℕ} (b : Fin f → 𝓞 E)
    (hx : IsLocBasis (𝓞 E) ℓ x) (hb : IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b) :
    ∃ N : ℕ, ¬ ℓ ∣ N ∧ ∀ y : La, N • y ∈ Submodule.span (OK H)
      (Set.range (Sum.elim (fun q : I × Fin f => b q.2 • x (.inl q.1)) (fun q : J × Fin f => b q.2 • x (.inr q.1)))) := by
  classical
  obtain ⟨-, n₁, h₁, hs₁⟩ := hx
  obtain ⟨-, n₂, h₂, hs₂⟩ := hb
  set S : Submodule (OK H) La := Submodule.span (OK H)
      (Set.range (Sum.elim (fun q : I × Fin f => b q.2 • x (.inl q.1)) (fun q : J × Fin f => b q.2 • x (.inr q.1)))) with hS
  have key : ∀ (m : I ⊕ J) (t : 𝓞 E), t ∈ Submodule.span (OK H) (Set.range b) → t • x m ∈ S := by
    intro m t ht
    induction ht using Submodule.span_induction with
    | mem t h =>
      obtain ⟨k, rfl⟩ := h
      refine Submodule.subset_span ?_
      rcases m with a | a
      · exact ⟨.inl (a, k), rfl⟩
      · exact ⟨.inr (a, k), rfl⟩
    | zero => simp
    | add s t _ _ hs ht => rw [add_smul]; exact S.add_mem hs ht
    | smul r t _ ht =>
      have : (r • t) • x m = r • (t • x m) := by
        change ((r : 𝓞 E) * t) • x m = (r : 𝓞 E) • (t • x m)
        rw [mul_smul]
      rw [this]
      exact S.smul_mem r ht
  refine ⟨n₁ * n₂, ?_, fun y => ?_⟩
  · exact fun h => (hℓ.dvd_mul.1 h).elim h₁ h₂
  · obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hs₁ y)
    have : (n₁ * n₂) • y = ∑ m, (n₂ • s m) • x m := by
      rw [mul_comm, mul_smul, ← hs, Finset.smul_sum]
      exact Finset.sum_congr rfl fun m _ => (smul_assoc _ _ _).symm
    rw [this]
    exact S.sum_mem fun m _ => key m _ (hs₂ _)

theorem scaled {S : Scheme.{0}} {K : Type} [Field K] {G : Over S} [GrpObj G] {x : Sp K ⟶ S} {U : Type}
    [AddCommGroup U] [Module K U] {O : Type} [CommRing O] (act : OAct O G) (M : LieModel G x U)
    (ρ : O →+* Module.End K U) (τ : O →+* K) (hact : M.IsActOf act.act ρ) {r : ℕ} (u : Fin r → U) {δ : K}
    (hδ : δ ≠ 0) (hE : IsEigFrame act x τ (fun k => M.pt (u k))) :
    IsEigFrame act x τ (fun k => M.pt (δ • u k)) ∧
      ∀ a, IsComb ((δ • (1 : Matrix (Fin r) (Fin r) K)) a) (fun k => M.pt (u k)) (M.pt (δ • u a)) := by
  obtain ⟨hc, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S K G x U M
  have hf' := (hf O act ρ τ hact).2 r
  obtain ⟨hli, hsp⟩ := (hf' u).1 hE
  refine ⟨(hf' _).2 ⟨?_, ?_⟩, fun a => ?_⟩
  · exact hli.units_smul (fun _ => Units.mk0 δ hδ)
  · rw [← hsp]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have h : u a = δ⁻¹ • (δ • u a) := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
      rw [SetLike.mem_coe, h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [hc]
    congr 1
    simp [Matrix.smul_apply, Matrix.one_apply, ite_smul]

theorem half {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {K : Type} [Field K] [CharZero K]
    (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K]
    (ℓ : Nat.Primes) (j : K →+* ℂ_[ℓ]) (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K))
    (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K)))
    {U : Type} [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U)
    (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K)
    (r r' f n : ℕ) (b : Fin f → 𝓞 E) (u : Fin r → U) (u' : Fin r' → U) (δ : K)
    (e : Fin n ≃ (Fin r × Fin f) ⊕ (Fin r' × Fin f))
    (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G))
    (hact : M.IsActOf Xo.univ.t.act.act ρ)
    (hj : ∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ V)
    (hcard : Nat.card (E →+* K) = Module.finrank ℚ E)
    (hb : IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b)
    (hu : ∀ a, ρ H.rt (u a) = σ (H.rt : E) • u a)
    (hu' : ∀ a, ρ H.rt (u' a) = -σ (H.rt : E) • u' a)
    (hind : LinearIndependent K (Sum.elim (fun q : Fin r × Fin f => ρ (b q.2) (u q.1))
      (fun q : Fin r' × Fin f => ρ (b q.2) (u' q.1))))
    (hδ : δ ≠ 0)
    (hlog : Real.log ‖j δ‖ = logIdeal ((j.comp σ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) -
      Real.log ‖j (σ (H.rt : E))‖)
    (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ V)
    (htan : ∀ k, IsTanAt T.G _ (uV k))
    (hbas : ∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w)
    (hlink : ∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left,
      s ≫ m.φ = (M.pt (Sum.elim (fun q : Fin r × Fin f => ρ (b q.2) (u q.1))
        (fun q : Fin r' × Fin f => ρ (b q.2) (u' q.1)) (e k))).left ∧
      s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) :
    IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (δ • HT.eigProj ρ σ (u a))) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.eigen_local_basis_log_norm E H ℓ K j V U ρ σ (Fin r) (Fin r') u u' f b δ hj hcard hb hu hu' hind hδ hlog
  exact (GlobalTheory.T.lie_model_extends_over_dvr E H D l Xo c K V y T tK m m' U M ρ σ _ n r e uV _ _ hact hσ htan hbas hlink h1 h2).2

theorem intFrames_fin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (τ : E →+* ℂ) (ℓ : Nat.Primes) (j : X.K →+* ℂ_[ℓ]) (v : Vecs X.y D.p) (w : Vecs X.y D.q), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → IsLocBasis (𝓞 E) ℓ x → X.IsCMFrame τ hx v w → ∃ (V : Subring X.K) (_ : IsDiscreteValuationRing V) (_ : IsFractionRing V X.K) (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (δ δ' : X.K) (v' : Vecs X.y D.p) (w' : Vecs X.y D.q), (∀ a : X.K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V X.K).range) ∧ δ ≠ 0 ∧ δ' ≠ 0 ∧ Real.log ‖j δ‖ = logIdeal ((j.comp (X.β.comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (X.β (tauE c τ (H.rt : E)))‖ ∧ Real.log ‖j δ'‖ = Real.log ‖j δ‖ ∧ (∀ a, IsComb ((δ • (1 : Matrix (Fin D.p) (Fin D.p) X.K)) a) v (v' a)) ∧ (∀ a, IsComb ((δ' • (1 : Matrix (Fin D.q) (Fin D.q) X.K)) a) w (w' a)) ∧ IsFramed (Set.range X.y) τ X.β X.y v' w' ∧ IsIntFrame X.m m'' (X.β.comp (tauIn c τ)) v' ∧ IsIntFrame X.m m'' (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w' := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X x hx τ ℓ j v w hty hτ hloc hfr
  obtain ⟨Vs, hdvr, hVj, hOK, hunit⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring X.K ℓ j
  let V : Subring X.K := Vs.toSubring
  haveI : IsDiscreteValuationRing V := hdvr
  haveI : IsFractionRing V X.K := (inferInstance : IsFractionRing Vs X.K)
  have hj : ∀ a : X.K, ‖j a‖ ≤ 1 ↔ a ∈ V := hVj
  have hOK' : ∀ s : 𝓞 X.K, (s : X.K) ∈ V := hOK
  obtain ⟨f, b, hf, hb⟩ := GlobalTheory.T.exists_local_basis_cm_order E H ℓ ℓ.prop
  obtain ⟨M, ρ, lam, hact, hIm, hsm, hadd, hrt, hCM⟩ := GlobalTheory.T.cm_lie_model_action E H D l Xo c g ty FU i Z P hP X
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := GlobalTheory.T.different_twisted_generator_exists E H ℓ
  let σ : E →+* X.K := X.β.comp (tauE c τ)
  let σ' : E →+* X.K := X.β.comp (tauE c (ComplexEmbedding.conjugate τ))
  have hσc : ∀ a, ((σ a : X.K) : ℂ) = τ a := fun _ => rfl
  have hσc' : ∀ a, ((σ' a : X.K) : ℂ) = starRingEnd ℂ (τ a) := fun a =>
    ComplexEmbedding.conjugate_coe_eq τ a
  have hrt1 : ((σ (H.rt : E) : X.K) : ℂ) = H.rt0 := (hσc _).trans hτ
  have hrt2 : ((σ' (H.rt : E) : X.K) : ℂ) = -H.rt0 := by
    rw [hσc', hτ, rt0_conj_neg_ne_zero]
  let u : Fin D.p → Fin g → X.K := fun a => lam true ⟨x (.inl a), hx.1 a⟩
  let u' : Fin D.q → Fin g → X.K := fun a => lam false ⟨x (.inr a), hx.2 a⟩
  have hu1 : ∀ a, ρ H.rt (u a) = σ (H.rt : E) • u a := fun a =>
    hrt true _ _ (by simpa [sgnRt] using hrt1)
  have hu1' : ∀ a, ρ H.rt (u' a) = -σ (H.rt : E) • u' a := fun a =>
    hrt false _ _ (by simpa [sgnRt] using hrt1)
  have hu2 : ∀ a, ρ H.rt (u' a) = σ' (H.rt : E) • u' a := fun a =>
    hrt false _ _ (by simpa [sgnRt] using hrt2)
  have hu2' : ∀ a, ρ H.rt (u a) = -σ' (H.rt : E) • u a := fun a =>
    hrt true _ _ (by simp [sgnRt, hrt2])
  obtain ⟨N, hN, hspan⟩ := span_fam (H := H) ℓ.prop x b hloc hb
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h => hN (h ▸ dvd_zero _)
  obtain ⟨n, hn, hnspan⟩ := hloc.2
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (h ▸ dvd_zero _)
  have hdec := (GlobalTheory.T.pure_family_decomposition E H (FU.Di i) g ty P hP D.p D.q x n hx hnspan).1
  have hg := (GlobalTheory.T.periods_span_pure_decomposition E H (FU.Di i) g ty P hP n hn0 hdec).1
  have hcardI : Fintype.card ((Fin D.p × Fin f) ⊕ (Fin D.q × Fin f)) = g := by
    rw [hg, (FU.sig i).1, (FU.sig i).2, ← hf, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  let e : Fin g ≃ (Fin D.p × Fin f) ⊕ (Fin D.q × Fin f) := (Fintype.equivFinOfCardEq hcardI).symm
  let bI : (Fin D.p × Fin f) ⊕ (Fin D.q × Fin f) → Bool := Sum.elim (fun _ => true) (fun _ => false)
  let aI : ∀ q, PureType.lat hP (sgnRt H (bI q)) := fun q => match q with
    | .inl q => b q.2 • (⟨x (.inl q.1), hx.1 q.1⟩ : PureType.lat hP (sgnRt H true))
    | .inr q => b q.2 • (⟨x (.inr q.1), hx.2 q.1⟩ : PureType.lat hP (sgnRt H false))
  let fam : (Fin D.p × Fin f) ⊕ (Fin D.q × Fin f) → Fin g → X.K :=
    Sum.elim (fun q => ρ (b q.2) (u q.1)) (fun q => ρ (b q.2) (u' q.1))
  let fam' : (Fin D.q × Fin f) ⊕ (Fin D.p × Fin f) → Fin g → X.K :=
    Sum.elim (fun q => ρ (b q.2) (u' q.1)) (fun q => ρ (b q.2) (u q.1))
  have hfam : ∀ q, lam (bI q) (aI q) = fam q := by
    rintro (q | q)
    · exact hsm true (b q.2) _
    · exact hsm false (b q.2) _
  have hswap : ∀ z, fam' (Equiv.sumComm _ _ z) = fam z := by rintro (q | q) <;> rfl
  have hval : (fun k => ((aI (e k) : PureType.lat hP (sgnRt H (bI (e k)))) : (FU.Di i).La)) =
      (Sum.elim (fun q : Fin D.p × Fin f => b q.2 • x (.inl q.1))
        (fun q : Fin D.q × Fin f => b q.2 • x (.inr q.1))) ∘ e := by
    have h0 : ∀ q, ((aI q : PureType.lat hP (sgnRt H (bI q))) : (FU.Di i).La) =
        Sum.elim (fun q : Fin D.p × Fin f => b q.2 • x (.inl q.1))
          (fun q : Fin D.q × Fin f => b q.2 • x (.inr q.1)) q := by
      rintro (q | q) <;> rfl
    funext k
    exact h0 (e k)
  have hspan' : ∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H)
      (Set.range fun k => ((aI (e k) : PureType.lat hP (sgnRt H (bI (e k)))) : (FU.Di i).La)) := by
    intro y
    rw [hval, e.surjective.range_comp]
    exact hspan y
  have hNu : IsUnit (N : V) := by
    have hNK : (N : X.K) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
    have hinv : (N : X.K)⁻¹ ∈ V := by
      refine (hj _).1 ?_
      rw [map_inv₀, norm_inv, hunit N hN, inv_one]
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V) (Subtype.ext ?_)
    simpa using mul_inv_cancel₀ hNK
  obtain ⟨T, m'', uV, htan, hbas, hlink⟩ := GlobalTheory.T.cm_pack_product_frame E H D l Xo c g ty FU i Z P hP X N
    (fun k => bI (e k)) (fun k => aI (e k)) V hN0 hspan' hOK' hNu
  have hlink1 : ∀ k, ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left, s ≫ X.m.φ = (M.pt (fam (e k))).left ∧
      s ≫ m''.φ = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap V X.K)) ≫ (uV k).left := fun k => by
    rw [← hfam]
    exact hlink k _ ((hIm _ _ _).2 rfl)
  have hlink2 : ∀ k, ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left,
      s ≫ X.m.φ = (M.pt (fam' ((e.trans (Equiv.sumComm _ _)) k))).left ∧
      s ≫ m''.φ = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap V X.K)) ≫ (uV k).left := fun k => by
    rw [Equiv.trans_apply, hswap]
    exact hlink1 k
  have hint : ∀ (φ : E →+* X.K) (a : 𝓞 E), φ (a : E) ∈ V := fun φ a =>
    hOK' ⟨φ a, map_isIntegral_int φ (RingOfIntegers.isIntegral_coe a)⟩
  obtain ⟨r0, v0, hv0, hv0s⟩ := exists_frame V fam (HT.eigSp ρ σ)
  have hind : LinearIndependent X.K fam :=
    (GlobalTheory.T.lie_model_extends_over_dvr E H D l Xo c X.K V X.y T X.t X.m m'' (Fin g → X.K) M ρ σ _ g r0 e uV fam v0 hact
      (hint σ) htan hbas hlink1 hv0 hv0s).1
  have hind' : LinearIndependent X.K fam' := by
    have h := hind.comp _ (Equiv.sumComm (Fin D.q × Fin f) (Fin D.p × Fin f)).injective
    have e2 : fam ∘ (Equiv.sumComm (Fin D.q × Fin f) (Fin D.p × Fin f)) = fam' := by
      funext z
      rcases z with q | q <;> rfl
    rwa [e2] at h
  have hcard := card_emb (E := E) c X.K X.hc
  have hconj : σ (IsCMField.complexConj E δ₀) = σ' δ₀ := Subtype.ext
    ((IsCMField.complexEmbedding_complexConj E τ δ₀).trans (hσc' δ₀).symm)
  have hl1 := (hδ₀' (j.comp σ)).1
  have hl2 := (hδ₀' (j.comp σ')).1
  have hl3 := (hδ₀' (j.comp σ)).2
  have hne : σ δ₀ ≠ 0 := (map_ne_zero σ).2 hδ₀
  have hne' : σ' δ₀ ≠ 0 := (map_ne_zero σ').2 hδ₀
  have I1 := half V ℓ j X.y T X.t X.m m'' M ρ σ D.p D.q f g b u u' (σ δ₀) e uV hact hj hcard hb hu1 hu1' hind
    hne hl1 (hint σ) htan hbas hlink1
  have I2 := half V ℓ j X.y T X.t X.m m'' M ρ σ' D.q D.p f g b u' u (σ' δ₀) (e.trans (Equiv.sumComm _ _)) uV
    hact hj hcard hb hu2 hu2' hind' hne' hl2 (hint σ') htan hbas hlink2
  have hFr := (GlobalTheory.T.cm_pack_pure_frame E H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hloc.1).2 v w hfr
  have hv : v = fun a => M.pt (HT.eigProj ρ σ (u a)) := funext fun a => (hCM true τ _ _).1 (hfr.1 a)
  have hw : w = fun a => M.pt (HT.eigProj ρ σ' (u' a)) := funext fun a =>
    (hCM false (ComplexEmbedding.conjugate τ) _ _).1 (hfr.2 a)
  obtain ⟨hy, -, hE1, hE2⟩ := hFr
  rw [hv] at hE1
  rw [hw] at hE2
  obtain ⟨s1, s2⟩ := scaled Xo.univ.t.act M ρ _ hact _ hne hE1
  obtain ⟨s3, s4⟩ := scaled Xo.univ.t.act M ρ _ hact _ hne' hE2
  refine ⟨V, inferInstance, inferInstance, T, m'', σ δ₀, σ' δ₀, _, _, fun a => ?_, hne, hne', hl1, ?_, ?_, ?_,
    ⟨hy, subset_rfl, s1, s3⟩, I1, I2⟩
  · rw [hj]
    exact ⟨fun h => ⟨⟨a, h⟩, rfl⟩, by rintro ⟨t, rfl⟩; exact t.2⟩
  · have := hl3
    simp only [RingHom.comp_apply] at this
    rw [hconj] at this
    exact this
  · intro a
    rw [hv]
    exact s2 a
  · intro a
    rw [hw]
    exact s4 a

end GlobalTheory.CompanionTheory.Ar.Fl.GFin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureNormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_pack_pure_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (τ : E →+* ℂ) (ℓ : Nat.Primes) (j : X.K →+* ℂ_[ℓ]) (v : Vecs X.y D.p) (w : Vecs X.y D.q), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → IsLocBasis (𝓞 E) ℓ x → X.IsCMFrame τ hx v w → ∃ (V : Subring X.K) (_ : IsDiscreteValuationRing V) (_ : IsFractionRing V X.K) (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (δ δ' : X.K) (v' : Vecs X.y D.p) (w' : Vecs X.y D.q), (∀ a : X.K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V X.K).range) ∧ δ ≠ 0 ∧ δ' ≠ 0 ∧ Real.log ‖j δ‖ = logIdeal ((j.comp (X.β.comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (X.β (tauE c τ (H.rt : E)))‖ ∧ Real.log ‖j δ'‖ = Real.log ‖j δ‖ ∧ (∀ a, IsComb ((δ • (1 : Matrix (Fin D.p) (Fin D.p) X.K)) a) v (v' a)) ∧ (∀ a, IsComb ((δ' • (1 : Matrix (Fin D.q) (Fin D.q) X.K)) a) w (w' a)) ∧ IsFramed (Set.range X.y) τ X.β X.y v' w' ∧ IsIntFrame X.m m'' (X.β.comp (tauIn c τ)) v' ∧ IsIntFrame X.m m'' (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.GFin.intFrames_fin | exact GlobalTheory.CompanionTheory.Ar.Fl.GFin.intFrames_fin | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.GFin.intFrames_fin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmHeight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem flatGen_finNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (ℓ : Nat.Primes), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → ∃ t : E, (∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ + Real.log ‖j (IsCMField.complexConj E t)‖ + Real.log ‖j (gramE (FU.Di i) e).det‖ = -((D.p : ℝ) + D.q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) ∧ (IsLocBasis (𝓞 E) ℓ e → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ = 0) ∧ ∀ (j : k →+* ℂ_[ℓ]) (t₀ : ℝ), HasFinNorm U τ φ ℓ (j.comp (IntermediateField.inclusion hc).toRingHom) t₀ → t₀ = Real.log ‖j r‖ - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) t)‖ - D.q * logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((D.q : ℝ) - D.p) * (logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (H.rt : E))‖) := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ k _ hc hM r ℓ hty hrt hmem hline he hconst hr hz
  obtain ⟨P, hP, x, hx, X, v, w, hkK, hxl, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ℓ k inferInstance hty hrt
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, hgram, hdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x e hcard he
  have hT0 : T.det ≠ 0 := hdet hxl.1
  have hge : (gramE (FU.Di i) e).det ≠ 0 := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  have hconj : (T.map (IsCMField.complexConj E)).det = IsCMField.complexConj E T.det :=
    (AlgEquiv.map_det (IsCMField.complexConj E) T).symm
  have hgdet : (gramE (FU.Di i) x).det
      = T.det * (gramE (FU.Di i) e).det * IsCMField.complexConj E T.det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hconj]
  refine ⟨T.det, ?_, ?_, ?_⟩
  · intro j
    have h1 := GlobalTheory.T.gram_determinant_log_different E H (FU.Di i) _ x ℓ hxl j
    have n1 : ‖j T.det‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hT0)
    have n2 : ‖j (gramE (FU.Di i) e).det‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hge)
    have n3 : ‖j (IsCMField.complexConj E T.det)‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j).2 (by simpa using hT0))
    rw [hgdet, map_mul, map_mul, norm_mul, norm_mul, Real.log_mul (mul_ne_zero n1 n2) n3,
      Real.log_mul n1 n2] at h1
    have hc2 : ((Fintype.card (Fin D.p ⊕ Fin D.q) : ℕ) : ℝ) = (D.p : ℝ) + D.q := by simp
    rw [hc2] at h1
    linarith
  · intro hel j
    rw [GlobalTheory.T.padic_norm_transition_det_one E H (FU.Di i) _ x e T ℓ hxl hel hT j, Real.log_one]
  · intro j t₀ hN
    obtain ⟨j', hj'⟩ := GlobalTheory.T.exists_extension_embedding_alg_closed k X.K ℂ_[ℓ] (IntermediateField.inclusion hkK).toRingHom j
    obtain ⟨V, hV, hVf, Tm, m'', δ, δ', v', w', hval, hδ, hδ', hlogδ, hlogδ', hA, hB, hfr', hiv, hiw⟩ :=
      GlobalTheory.T.cm_pack_pure_norm E H D l Xo c g ty FU i Z P hP X x hx τ ℓ j' v w hty hrt hxl hfr
    obtain ⟨hF, hφ⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hrt
      hmem hline he hconst hxl.1 hT hfr
    have hF' : IsFramed U τ X.β X.y v' w' := ⟨hfr'.1, hF.2.1, hfr'.2.2⟩
    have hβ : j'.comp X.β = j.comp (IntermediateField.inclusion hc).toRingHom := by
      rw [← hj']; ext a; rfl
    haveI := hV
    haveI := hVf
    have hfin := hN V X.K j' X.β X.y v' w' Tm X.t X.m m'' hval hβ hF' hiv hiw
    have hchg := hline.chg X.K X.β X.y v w v' w' (δ • (1 : Matrix (Fin D.p) (Fin D.p) X.K))
      (δ' • (1 : Matrix (Fin D.q) (Fin D.q) X.K)) hF hF' hA hB
    simp only [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hchg
    have hφ0 := hline.ne X.K X.β X.y v w hF
    have hφ'0 := hline.ne X.K X.β X.y v' w' hF'
    have horth : ∀ a b, sesq (FU.Di i) (x (.inl a)) (x (.inr b)) = 0 := fun a b =>
      (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
    obtain ⟨hG0, hGlog⟩ := GlobalTheory.T.local_basis_gram_det_log_norm E H (FU.Di i) D.p D.q x ℓ hxl horth
    have hzt : (Z true).z ^ D.p ≠ 0 := pow_ne_zero _ (GlobalTheory.T.curve_z_ne_zero E H _ (Z true))
    have hC : ((φ X.K X.y v w : X.K) : ℂ) * τ T.det = (r : ℂ) * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
      apply mul_right_cancel₀ hzt
      rw [hφ, ← hz]
      ring
    have hK : φ X.K X.y v w * X.β (tauE c τ T.det)
        = (IntermediateField.inclusion hkK).toRingHom r * X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det) :=
      Subtype.ext hC
    have hjE : j'.comp (X.β.comp (tauE c τ))
        = j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) := by
      rw [← RingHom.comp_assoc, hβ, RingHom.comp_assoc]
    have happ : ∀ a : E, j' (X.β (tauE c τ a))
        = j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) a) := fun a =>
      congrArg (fun f : E →+* ℂ_[ℓ] => f a) hjE
    have hjr : j' ((IntermediateField.inclusion hkK).toRingHom r) = j r := by
      rw [← hj']; rfl
    have nφ : ‖j' (φ X.K X.y v w)‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hφ0)
    have nφ' : ‖j' (φ X.K X.y v' w')‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hφ'0)
    have nδ : ‖j' δ‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hδ)
    have nδ' : ‖j' δ'‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hδ')
    have nr : ‖j r‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 (by simpa using hr))
    have nt : ‖j' (X.β (tauE c τ T.det))‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j').2 ((map_ne_zero _).2 ((map_ne_zero _).2 hT0)))
    have nG : ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j').2 ((map_ne_zero _).2 ((map_ne_zero _).2 hG0)))
    have hn : ‖j' (φ X.K X.y v w)‖ * ‖j' (X.β (tauE c τ T.det))‖
        = ‖j r‖ * ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ := by
      have h := congrArg (fun a => ‖j' a‖) hK
      simpa only [map_mul, norm_mul, hjr] using h
    have hl : Real.log ‖j' (φ X.K X.y v w)‖ + Real.log ‖j' (X.β (tauE c τ T.det))‖
        = Real.log ‖j r‖ + Real.log ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ := by
      rw [← Real.log_mul nφ nt, ← Real.log_mul nr nG, hn]
    have hm : ‖j' (φ X.K X.y v' w')‖ * ‖j' δ‖ ^ D.p = ‖j' (φ X.K X.y v w)‖ * ‖j' δ'‖ ^ D.q := by
      have h := congrArg (fun a => ‖j' a‖) hchg
      simp only [map_mul, map_pow, map_one, norm_mul, norm_pow, norm_one] at h
      linear_combination h
    have hlog : Real.log ‖j' (φ X.K X.y v' w')‖ + D.p * Real.log ‖j' δ‖
        = Real.log ‖j' (φ X.K X.y v w)‖ + D.q * Real.log ‖j' δ'‖ := by
      rw [← Real.log_pow, ← Real.log_pow, ← Real.log_mul nφ' (pow_ne_zero _ nδ),
        ← Real.log_mul nφ (pow_ne_zero _ nδ'), hm]
    have hGl := hGlog (j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)))
    rw [RingHom.comp_apply, ← happ] at hGl
    rw [hjE, happ] at hlogδ
    rw [← happ]
    linear_combination -hfin + hlog + hl + hGl + (D.q : ℝ) * hlogδ' + ((D.q : ℝ) - D.p) * hlogδ

end GlobalTheory.CompanionTheory.Ar.Fl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmHeightStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_function_cm_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (ℓ : Nat.Primes), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → ∃ t : E, (∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ + Real.log ‖j (IsCMField.complexConj E t)‖ + Real.log ‖j (gramE (FU.Di i) e).det‖ = -((D.p : ℝ) + D.q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) ∧ (IsLocBasis (𝓞 E) ℓ e → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ = 0) ∧ ∀ (j : k →+* ℂ_[ℓ]) (t₀ : ℝ), HasFinNorm U τ φ ℓ (j.comp (IntermediateField.inclusion hc).toRingHom) t₀ → t₀ = Real.log ‖j r‖ - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) t)‖ - D.q * logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((D.q : ℝ) - D.p) * (logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (H.rt : E))‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.flatGen_finNorm | exact GlobalTheory.CompanionTheory.Ar.Fl.flatGen_finNorm | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.flatGen_finNorm <;> assumption)
end
