module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiAZero
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.HkOfPush
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.EtaleIdempotents.IntegersResidueEqThetaCoeffPowOfTeichmuller
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

private theorem cc_sW {l : ℕ} [Fact l.Prime] (A : PAlg l) (y : Ainf l) :
    WittVector.constantCoeff (A.sW y) = A.s (WittVector.constantCoeff y) :=
  WittVector.map_coeff A.s y 0

private theorem cc_xi {l : ℕ} [Fact l.Prime] (A : PAlg l) :
    WittVector.constantCoeff A.xi = - A.s (pFlat l) := by
  have h : WittVector.constantCoeff (xi0 l) = - pFlat l := by
    rw [xi0, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
    congr 1
  rw [PAlg.xi, cc_sW, h, map_neg]

private theorem cc_of_thetaN {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : A.W) (hz : A.toAcr 1 z ∈ A.PFil 1) :
    WittVector.constantCoeff z ∈ Ideal.span {A.s (pFlat l)} := by
  have hl : (l : A.Acr 1) = 0 := by simpa using A.pow_l_acr 1
  have h1 : A.toAcr 1 z ∈ A.Fil 1 1 := by
    rw [PAlg.PFil, hl, Ideal.span_singleton_eq_bot.2 rfl, bot_sup_eq] at hz
    exact hz
  rw [← A.ker_thetaN, RingHom.mem_ker, A.thetaN_toAcr, Ideal.Quotient.eq_zero_iff_mem] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  obtain ⟨c', rfl⟩ : ∃ c', A.th c' = c := Ideal.Quotient.mk_surjective c
  have h2 : z - c' * (l : A.W) ∈ Ideal.span {A.xi} := by
    apply Ideal.Quotient.eq_zero_iff_mem.1
    change A.th _ = 0
    rw [map_sub, map_mul, map_natCast, ← hc, pow_one, sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 := congrArg (WittVector.constantCoeff (p := l) (R := A.A)) hd
  rw [map_mul, map_sub, map_mul, map_natCast, A.natCast_l, mul_zero, sub_zero, cc_xi] at h3
  rw [← h3]
  exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_span_singleton_self _))

theorem UpperTheory.integersResidue_eq_theta_coeff_pow_of_teichmuller :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (N : ℕ), Pb.Mid.TeichmullerCongruence r N → ∀ (x : OK l K) (w : Ainf l),
        theta0 l w = okToOC l K x → gRes r x = Ideal.Quotient.mk _ (w.coeff 0) ^ l ^ N := by
  intro l _ K r N hT x w hw
  obtain ⟨w', hw'⟩ := WittVector.constantCoeff_surjective (p := l) (R := r.k) (r.ρ x)
  have T := hT 1 x
  rw [Pb.Mid.phiQ_pow] at T
  have e1 : B.κb (okToOC l K) true 1 x =
      Ideal.Quotient.mk _ ((PAlg.base l).toAcr 1 ((PAlg.base l).sW w)) := by
    change B.uJ true (PAlg.base l) 1 ((PAlg.base l).oC (okToOC l K x)) = _
    rw [← hw, PAlg.oC_theta0, B.uJ_th]
  have e2 : Pb.Mid.κm r 1 x =
      Ideal.Quotient.mk _ ((PAlg.base l).toAcr 1 ((PAlg.base l).sW (WittVector.map r.s w'))) := by
    change Ideal.quotientMap _ (Pb.Mid.wn r 1) (Pb.Mid.im_le r 1) (Wc.res l r.k 1 (r.ρ x)) = _
    rw [← hw', Wc.res_coeff, Ideal.quotientMap_mk, Pb.Mid.wn_mk]
    change Ideal.Quotient.mk _ ((PAlg.base l).cris 1 (algebraMap (Ainf l) (Acris l) (WittVector.map r.s w'))) = _
    rw [PAlg.cris_algebraMap]
  rw [e1, e2, ← map_pow] at T
  have hz : (PAlg.base l).toAcr 1 ((PAlg.base l).sW w ^ l ^ N - (PAlg.base l).sW (WittVector.map r.s w')) ∈
      (PAlg.base l).PFil 1 := by
    rw [map_sub, map_pow]
    exact Ideal.Quotient.eq.1 T
  have hc := cc_of_thetaN (PAlg.base l) _ hz
  rw [map_sub, map_pow, cc_sW, cc_sW] at hc
  have e3 : WittVector.constantCoeff (WittVector.map r.s w') = r.s (r.ρ x) := by
    rw [← hw']
    exact WittVector.map_coeff r.s w' 0
  rw [e3] at hc
  change Ideal.Quotient.mk _ (r.s (r.ρ x)) = _
  rw [← map_pow, eq_comm, Ideal.Quotient.eq]
  exact hc
end

section -- merged from Development.AutomorphicArithmetic.EtaleIdempotents.IntegersResidueEqZeroOfNotIsUnit
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

theorem UpperTheory.integersResidue_eq_zero_of_not_isUnit :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (ϖ : OK l K), ¬ IsUnit ϖ → gRes r ϖ = 0 := by
  intro l _ K r ϖ hϖ
  have hu0 : (PreTilt.untilt (0 : Ob l) : OC l) = 0 := by
    rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]
  have hnorm : ∀ x : OK l K, ‖((okToOC l K x : OC l) : ℂ_[l])‖ = ‖((x : K) : PadicAlgCl l)‖ :=
    fun x => norm_clToC _
  have hker : ∀ z : OK l K, r.ρ z = 0 → ‖((z : K) : PadicAlgCl l)‖ < 1 := fun z hz => by
    have h := r.hs z
    rw [hz, map_zero, hu0, zero_sub] at h
    have e : ((-(okToOC l K z) : OC l) : ℂ_[l]) = -((okToOC l K z : OC l) : ℂ_[l]) := rfl
    rw [e, norm_neg, hnorm] at h
    exact h
  have hρ : r.ρ ϖ = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := r.surj (r.ρ ϖ)⁻¹
    have hz : r.ρ (1 - ϖ * y) = 0 := by
      rw [map_sub, map_one, map_mul, hy, mul_inv_cancel₀ hne, sub_self]
    have h1 := hker _ hz
    have hsum : ((ϖ * y : OK l K) : K) = 1 - ((1 - ϖ * y : OK l K) : K) := by
      push_cast; ring
    have hlt : ‖(((ϖ * y : OK l K) : K) : PadicAlgCl l)‖ = 1 := by
      have e : (((ϖ * y : OK l K) : K) : PadicAlgCl l) = 1 - (((1 - ϖ * y : OK l K) : K) : PadicAlgCl l) := by
        rw [hsum]; push_cast; rfl
      refine le_antisymm (by simpa using norm_OK_le (ϖ * y)) ?_
      have h4 : ‖(1 : PadicAlgCl l)‖ ≤ max ‖(((ϖ * y : OK l K) : K) : PadicAlgCl l)‖ ‖(((1 - ϖ * y : OK l K) : K) : PadicAlgCl l)‖ := by
        have e' : (1 : PadicAlgCl l) = (((ϖ * y : OK l K) : K) : PadicAlgCl l) + (((1 - ϖ * y : OK l K) : K) : PadicAlgCl l) := by
          rw [e]; ring
        conv_lhs => rw [e']
        exact IsUltrametricDist.norm_add_le_max _ _
      rw [norm_one] at h4
      rcases le_max_iff.1 h4 with h5 | h5
      · exact h5
      · exact absurd h5 (not_le.2 h1)
    have hmul : ‖((ϖ : K) : PadicAlgCl l)‖ * ‖((y : K) : PadicAlgCl l)‖ = 1 := by
      rw [← norm_mul]; simpa using hlt
    have h2 := norm_OK_le ϖ
    have h3 := norm_OK_le y
    apply hϖ
    rw [isUnit_OK_iff]
    nlinarith [norm_nonneg ((ϖ : K) : PadicAlgCl l), norm_nonneg ((y : K) : PadicAlgCl l)]
  show Ideal.Quotient.mk _ (r.s (r.ρ ϖ)) = 0
  rw [hρ, map_zero, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.EtaleIdempotents.GaloisActionEvalEtaleFamilyExistsDenominator
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

private theorem act_toV {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (j : ℕ)
    (g : K.fixingSubgroup) (x : M.T j) : M.act j g (M.toV j x) = M.toV j (M.actT j g x) :=
  LinearMap.baseChange_tmul _ _ _

private theorem sig_inv {F A C : Type*} [CommRing F] [CommRing A] [CommRing C] [Algebra F C] (c : A →+* C) (σ : C →ₐ[F] C)
    (σA : A →+* A) (hσ : ∀ a, σ (c a) = c (σA a)) (t u : A) (ht : IsUnit (c t)) (hg : σA t = u * t) (r : ℕ) :
    c u ^ r * σ (Ring.inverse (c t)) ^ r = Ring.inverse (c t) ^ r := by
  have hT : c t * Ring.inverse (c t) = 1 := Ring.mul_inverse_cancel _ ht
  have h1 : σ (c t) = c u * c t := by rw [hσ, hg, map_mul]
  have h2 := congrArg σ hT
  rw [map_mul, map_one, h1] at h2
  have h3 : c u * σ (Ring.inverse (c t)) = Ring.inverse (c t) := by
    calc c u * σ (Ring.inverse (c t))
        = (c u * σ (Ring.inverse (c t))) * (c t * Ring.inverse (c t)) := by rw [hT, mul_one]
      _ = (c u * c t * σ (Ring.inverse (c t))) * Ring.inverse (c t) := by ring
      _ = Ring.inverse (c t) := by rw [h2, one_mul]
  rw [← mul_pow, h3]

private theorem rel_of_inv {F A C V T ι : Type*} [Field F] [CommRing A] [CommRing C] [Algebra F C] [AddCommGroup V] [Module F V]
    [Fintype ι] (c : A →+* C) (σ : C →ₐ[F] C) (σA : A →+* A) (hσ : ∀ a, σ (c a) = c (σA a)) (t u : A) (ht : IsUnit (c t))
    (hg : σA t = u * t) (r : ℕ) (act : V →ₗ[F] V) (toV : T → V) (actT : T → T) (hact : ∀ x, act (toV x) = toV (actT x))
    (v : ι → T) (a : ι → A)
    (h : TensorProduct.map act σ.toLinearMap (∑ k, toV (v k) ⊗ₜ[F] (c (a k) * Ring.inverse (c t) ^ r)) =
      ∑ k, toV (v k) ⊗ₜ[F] (c (a k) * Ring.inverse (c t) ^ r)) :
    ∑ k, toV (Sum.elim (fun k => actT (v k)) v k) ⊗ₜ[F]
      (c (Sum.elim (fun k => σA (a k)) (fun k => -(u ^ r * a k)) k) * Ring.inverse (c t) ^ r) = 0 := by
  have hL : TensorProduct.map act σ.toLinearMap (∑ k, toV (v k) ⊗ₜ[F] (c (a k) * Ring.inverse (c t) ^ r)) =
      ∑ k, toV (actT (v k)) ⊗ₜ[F] (c (σA (a k)) * σ (Ring.inverse (c t)) ^ r) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, TensorProduct.map_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hact]
    simp [hσ]
  rw [hL] at h
  have h1 := congrArg (LinearMap.lTensor V (LinearMap.mulLeft F (c u ^ r))) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply] at h1
  have hs := sig_inv c σ σA hσ t u ht hg r
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have e1 : ∀ k, c u ^ r * (c (σA (a k)) * σ (Ring.inverse (c t)) ^ r) =
      c (σA (a k)) * Ring.inverse (c t) ^ r := fun k => by
    rw [← hs]; ring
  simp only [e1] at h1
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← TensorProduct.tmul_add]
  have e2 : c u ^ r * (c (a k) * Ring.inverse (c t) ^ r) +
      c (-(u ^ r * a k)) * Ring.inverse (c t) ^ r = 0 := by
    rw [map_neg, map_mul, map_pow]; ring
  rw [e2, TensorProduct.tmul_zero]

private theorem ev_of_rel {A N T ι : Type*} [CommRing A] [AddCommGroup N] [Module A N] [Fintype ι] (σA : A →+* A)
    (G : N →ₛₗ[σA] N) (E : T → N) (actT : T → T) (hG : ∀ x, G (E x) = E (actT x)) (u s : A) (v : ι → T) (a : ι → A)
    (h : s • ∑ k, (Sum.elim (fun k => σA (a k)) (fun k => -(u * a k)) k) • E (Sum.elim (fun k => actT (v k)) v k) = 0) :
    s • G (∑ k, a k • E (v k)) = (s * u) • ∑ k, a k • E (v k) := by
  have hsplit : ∑ k, (Sum.elim (fun k => σA (a k)) (fun k => -(u * a k)) k) • E (Sum.elim (fun k => actT (v k)) v k) =
      G (∑ k, a k • E (v k)) - u • ∑ k, a k • E (v k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Fintype.sum_sum_type, sub_eq_add_neg, Finset.smul_sum, ← Finset.sum_neg_distrib, map_sum]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, mul_smul, map_smulₛₗ, hG]
  rw [hsplit, smul_sub, sub_eq_zero, ← mul_smul] at h
  exact h

set_option maxHeartbeats 1000000 in
theorem UpperTheory.galoisAction_evalEtaleFamily_exists_denominator :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B₀ : PB l K) (e : E.EtFam l K), e.Good → ∀ (M : Model l K) (j r : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l)
        (g : K.fixingSubgroup) (χ : ℤ_[l]ˣ), galA g (tA l) = zA l χ * tA l → IsInv B₀ M j (vec B₀ M j r v c) →
        ∃ a b : ℕ, ∀ n, ((l : Acris l) ^ a * tA l ^ b) • M.galMH (IntermediateField.fixingSubgroupEquiv K g) n j (evE e M j n v c) =
          ((l : Acris l) ^ a * tA l ^ b * zA l χ ^ r) • evE e M j n v c := by
  intro l _ K B₀ e he M j r ι _ v c g χ hg hinv
  have hvec : vec B₀ M j r (Sum.elim (fun k => M.actT j g (v k)) v)
      (Sum.elim (fun k => galA g (c k)) (fun k => -(zA l χ ^ r * c k))) = 0 :=
    rel_of_inv B₀.c (B₀.σ g) (galA g) (B₀.σ_c g) (tA l) (zA l χ) B₀.t_unit hg r (M.act j g) (M.toV j) (M.actT j g)
      (act_toV M j g) v c (hinv g)
  have hz : ∃ a u : ℕ, ∀ n, ((l : Acris l) ^ a * tA l ^ u) • evE e M j n (Sum.elim (fun k => M.actT j g (v k)) v)
      (Sum.elim (fun k => galA g (c k)) (fun k => -(zA l χ ^ r * c k))) = 0 :=
    vecZero l K B₀ e he M j (ι ⊕ ι) (Sum.elim (fun k => M.actT j g (v k)) v)
      (Sum.elim (fun k => galA g (c k)) (fun k => -(zA l χ ^ r * c k))) r hvec
  obtain ⟨a, b, hab⟩ := hz
  refine ⟨a, b, fun n => ?_⟩
  exact ev_of_rel (galA g) (M.galMH (IntermediateField.fixingSubgroupEquiv K g) n j) (fun x : M.T j => e M n j (x.lev n))
    (M.actT j g) (fun x => (he.equi M n j (IntermediateField.fixingSubgroupEquiv K g) (x.lev n)).symm)
    (zA l χ ^ r) _ v c (hab n)
end

section -- merged from Development.AutomorphicArithmetic.EtaleIdempotents.EvalEtaleFamilyMemLimitOfReduced
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

theorem UpperTheory.evalEtaleFamily_mem_limit_of_reduced :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (e : E.EtFam l K), e.Red → ∀ (M : Model l K) (j : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l),
        (fun n => evE e M j n v c) ∈ (M.MS j).lim := by
  intro l _ K e he M j ι _ v c n
  have h2 : ∀ k, GlobalTheory.EtC.red (l ^ (n + 1)) (l ^ n) M.spc (j : ℤ) 0 ((v k).lev (n + 1)) = (v k).lev n :=
    fun k => (show GlobalTheory.EtC.Hl l M.spc j 0 from v k).2 n
  have h3 : ∀ k, (M.MS j).r n (e M (n + 1) j ((v k).lev (n + 1))) = e M n j ((v k).lev n) :=
    fun k => (he M n j ((v k).lev (n + 1))).trans (congrArg (e M n j) (h2 k))
  have hk : ∀ k, (M.MS j).r n (c k • e M (n + 1) j ((v k).lev (n + 1))) = c k • e M n j ((v k).lev n) := by
    intro k
    exact (LinearMap.map_smul ((M.MS j).r n) (c k) _).trans (congrArg (fun y => c k • y) (h3 k))
  exact (map_sum ((M.MS j).r n) _ _).trans (Finset.sum_congr rfl fun k _ => hk k)
end

section -- merged from Development.AutomorphicArithmetic.EtaleIdempotents.CrisFrobeniusIterateEvalEtaleFamily
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

private theorem iter_gen {A R ι : Type*} (f : A → A) (φ : R → R) (E : (ι → R) → A)
    (h : ∀ c, f (E c) = E (fun k => φ (c k))) (N : ℕ) (c : ι → R) :
    f^[N] (E c) = E (fun k => φ^[N] (c k)) := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih =>
    simp only [Function.iterate_succ_apply]
    rw [h, ih]

private theorem sl_sum {R A ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A] (σ : R →+* R)
    (f : A →ₛₗ[σ] A) [Fintype ι] (c : ι → R) (x : ι → A) (hx : ∀ k, f (x k) = x k) :
    f (∑ k, c k • x k) = ∑ k, σ (c k) • x k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.map_smulₛₗ, hx]

theorem UpperTheory.crisFrobenius_iterate_evalEtaleFamily :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (e : E.EtFam l K), e.Phi → ∀ (M : Model l K) (j n N : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l),
        (phiH M.P n j)^[N] (evE e M j n v c) = evE e M j n v (fun k => (phiA l)^[N] (c k)) := by
  intro l _ K e he M j n N ι _ v c
  exact iter_gen (phiH M.P n j) (phiA l) (fun c => evE e M j n v c)
    (fun c => sl_sum (ACris.phi (K := ℂ_[l]) (p := l)) (M.phiMH n j) c (fun k => e M n j ((v k).lev n))
      (fun k => he M n j _)) N c
end

section -- merged from Development.AutomorphicArithmetic.EtaleIdempotents.GaloisEquivariantTensorDescentOfPrimePowerUnits
open TensorProduct

universe u₁ u₂ u₃ u₄ u₅ u₆

private lemma loc_ker {W A C L : Type*} [CommRing W] [CommRing A] [CommRing C] [Algebra W A]
    [Algebra A C] [Algebra W C] [IsScalarTower W A C] [AddCommGroup L] [Module W L] (t : A)
    [IsLocalization (Submonoid.powers t) C] (x : A ⊗[W] L)
    (hx : LinearMap.rTensor L (IsScalarTower.toAlgHom W A C).toLinearMap x = 0) :
    ∃ b : ℕ, t ^ b • x = 0 := by
  have hbc := TensorProduct.isBaseChange A (A ⊗[W] L) C
  have hl := (isLocalizedModule_iff_isBaseChange (Submonoid.powers t) C _).2 hbc
  have key : ∀ p : A ⊗[W] L, AlgebraTensorModule.cancelBaseChange W A C C L
      ((TensorProduct.mk A C (A ⊗[W] L) 1) p) =
      LinearMap.rTensor L (IsScalarTower.toAlgHom W A C).toLinearMap p := by
    intro p
    induction p with
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | tmul a y => simp [Algebra.algebraMap_eq_smul_one]
  have h0 : (TensorProduct.mk A C (A ⊗[W] L) 1) x = 0 := by
    apply (AlgebraTensorModule.cancelBaseChange W A C C L).injective
    rw [map_zero, key, hx]
  obtain ⟨⟨_, b, rfl⟩, hb⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers t) _).1 h0
  exact ⟨b, hb⟩

private lemma coords (W : Type u₁) (K : Type u₂) (C : Type u₃) (L : Type u₄) [CommRing W] [Field K]
    [Algebra W K] [CommRing C] [Algebra W C] [Algebra K C] [IsScalarTower W K C] [AddCommGroup L]
    [Module W L] :
    ∃ (I : Type (max u₂ u₄)) (b : Module.Basis I K (K ⊗[W] L)) (e : C ⊗[W] L ≃ₗ[C] (I →₀ C)),
      ∀ (x : C) (y : L), e (x ⊗ₜ y) =
        x • Finsupp.mapRange (algebraMap K C) (map_zero _) (b.repr (1 ⊗ₜ y)) := by
  let b := Module.Basis.ofVectorSpace K (K ⊗[W] L)
  refine ⟨_, b, (AlgebraTensorModule.cancelBaseChange W K C C L).symm.trans
    (Algebra.TensorProduct.basis C b).repr, ?_⟩
  intro x y
  simp [Algebra.TensorProduct.basis_repr_tmul]

private lemma aux {W : Type u₁} {K : Type u₂} {A : Type u₅} {C : Type u₃} {Γ : Type u₆} {L : Type u₄}
    (l : ℕ) [CommRing W] [IsDomain W] [Field K] [Algebra W K] [IsFractionRing W K]
    [CommRing A] [Algebra W A] [CommRing C] [Algebra A C] [Algebra W C] [IsScalarTower W A C]
    [Algebra K C] [IsScalarTower W K C] [AddCommGroup L] [Module W L] (t : A)
    [IsLocalization (Submonoid.powers t) C]
    (σA : Γ → A →+* A) (σC : Γ → C →+* C) (χ : Γ → A) (T : Γ → (A ⊗[W] L →+ A ⊗[W] L))
    (z : A ⊗[W] L) (s : ℕ)
    (hW : ∀ y : W, y ≠ 0 → ∃ (m : ℕ) (b : W), y = (l : W) ^ m * b ∧ IsUnit b)
    (hl : IsUnit (l : C))
    (hσ : ∀ g a, σC g (algebraMap A C a) = algebraMap A C (σA g a))
    (hσW : ∀ g (w : W), σA g (algebraMap W A w) = algebraMap W A w)
    (hσt : ∀ g, σA g t = χ g * t)
    (hT : ∀ g (a : A) (y : L), T g (a ⊗ₜ[W] y) = σA g a ⊗ₜ[W] y)
    (hfix : ∀ x : C, (∀ g, σC g x = x) → ∃ (a : ℕ) (w : W), (l : C) ^ a * x = algebraMap W C w)
    (hz : ∀ g, ∃ a b : ℕ, ((l : A) ^ a * t ^ b) • T g z = ((l : A) ^ a * t ^ b * χ g ^ s) • z) :
    ∃ (a b : ℕ) (y : L), ((l : A) ^ a * t ^ b) • z = (t ^ (b + s)) • ((1 : A) ⊗ₜ[W] y) := by
  classical
  obtain ⟨I, b, e, he⟩ := coords W K C L
  obtain ⟨R, hR⟩ : ∃ R : A ⊗[W] L →ₗ[W] C ⊗[W] L,
      R = LinearMap.rTensor L (IsScalarTower.toAlgHom W A C).toLinearMap := ⟨_, rfl⟩
  have hRt : ∀ (a : A) (y : L), R (a ⊗ₜ y) = algebraMap A C a ⊗ₜ y := fun a y => by simp [hR]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : A ⊗[W] L → (I →₀ C), ∀ x, Φ x = e (R x) := ⟨_, fun _ => rfl⟩
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  have hΦadd : ∀ p q, Φ (p + q) = Φ p + Φ q := fun p q => by simp [hΦ]
  have hΦsub : ∀ p q, Φ (p - q) = Φ p - Φ q := fun p q => by simp [hΦ]
  have hΦt : ∀ a y i, Φ (a ⊗ₜ y) i = algebraMap A C a * algebraMap K C (b.repr (1 ⊗ₜ y) i) := by
    intro a y i
    rw [hΦ, hRt, he, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  have hΦs : ∀ (a : A) x i, Φ (a • x) i = algebraMap A C a * Φ x i := by
    intro a x i
    induction x with
    | add p q hp hq =>
      rw [smul_add, hΦadd, hΦadd, Finsupp.add_apply, Finsupp.add_apply, hp, hq, mul_add]
    | tmul a' y => rw [TensorProduct.smul_tmul', hΦt, hΦt, smul_eq_mul, map_mul, mul_assoc]
  have hσK : ∀ g (k : K), σC g (algebraMap K C k) = algebraMap K C k := by
    intro g k
    have h : (σC g).comp (algebraMap K C) = algebraMap K C := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors W)
      ext w
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply W K C, IsScalarTower.algebraMap_apply W A C, hσ, hσW]
    exact RingHom.congr_fun h k
  have hΦT : ∀ g x i, Φ (T g x) i = σC g (Φ x i) := by
    intro g x i
    induction x with
    | add p q hp hq =>
      rw [map_add (f := _), hΦadd, hΦadd, Finsupp.add_apply, Finsupp.add_apply, hp, hq, map_add (f := _)]
    | tmul a y => rw [hT, hΦt, hΦt, map_mul, hσ, hσK]
  have hct : IsUnit (algebraMap A C t) :=
    IsLocalization.map_units C (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t)
  obtain ⟨u, hu⟩ : ∃ u : C, algebraMap A C t ^ s * u = 1 := (hct.pow s).exists_right_inv
  have hy : ∀ i g, σC g (u * Φ z i) = u * Φ z i := by
    intro i g
    obtain ⟨a, b', h⟩ := hz g
    have h1 : Φ (((l : A) ^ a * t ^ b') • T g z) i = Φ (((l : A) ^ a * t ^ b' * χ g ^ s) • z) i := by
      rw [h]
    rw [hΦs, hΦs] at h1
    have hunit : IsUnit (algebraMap A C ((l : A) ^ a * t ^ b')) := by
      rw [map_mul, map_pow, map_pow, map_natCast]
      exact (hl.pow a).mul (hct.pow b')
    have h2 : σC g (Φ z i) = algebraMap A C (χ g) ^ s * Φ z i := by
      rw [← hΦT]
      apply hunit.mul_left_cancel
      rw [h1, map_mul _ _ (χ g ^ s), map_pow, mul_assoc]
    have h3 : σC g (algebraMap A C t ^ s) = algebraMap A C (χ g) ^ s * algebraMap A C t ^ s := by
      rw [map_pow, hσ, hσt, map_mul, mul_pow]
    have h4 : σC g (algebraMap A C t ^ s) * σC g u = 1 := by rw [← map_mul, hu, map_one]
    rw [map_mul, h2]
    calc σC g u * (algebraMap A C (χ g) ^ s * Φ z i)
        = σC g u * (algebraMap A C (χ g) ^ s * ((algebraMap A C t ^ s * u) * Φ z i)) := by
          rw [hu, one_mul]
      _ = (σC g (algebraMap A C t ^ s) * σC g u) * (u * Φ z i) := by rw [h3]; ring
      _ = u * Φ z i := by rw [h4, one_mul]
  choose a₀ w₀ hw₀ using fun i => hfix (u * Φ z i) (hy i)
  obtain ⟨S, hS⟩ : ∃ S, S = (Φ z).support := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = S.sup a₀ := ⟨_, rfl⟩
  let f : I →₀ K := Finsupp.onFinset S
    (fun i => if i ∈ S then algebraMap W K ((l : W) ^ (N - a₀ i) * w₀ i) else 0)
    (by intro i hi; by_contra h; simp [h] at hi)
  have hf : ∀ i, algebraMap K C (f i) = (l : C) ^ N * (u * Φ z i) := by
    intro i
    by_cases hi : i ∈ S
    · have hle : a₀ i ≤ N := hN ▸ Finset.le_sup hi
      simp only [f, Finsupp.onFinset_apply, if_pos hi]
      rw [← IsScalarTower.algebraMap_apply W K C, map_mul, map_pow, map_natCast, ← hw₀ i,
        ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    · have h0 : Φ z i = 0 := by simpa [hS] using hi
      simp [f, hi, h0]
  have hloc : IsLocalizedModule (nonZeroDivisors W) (TensorProduct.mk W K L 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors W) K _).2
      (TensorProduct.isBaseChange W L K)
  obtain ⟨⟨y₀, d⟩, hd⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors W) (TensorProduct.mk W K L 1) (b.repr.symm f)
  obtain ⟨m, β, hdβ, hβ⟩ := hW d (nonZeroDivisors.ne_zero d.2)
  obtain ⟨β', hβ'⟩ := hβ.exists_left_inv
  obtain ⟨y₁, hy₁d⟩ : ∃ y₁, y₁ = β' • y₀ := ⟨_, rfl⟩
  have hy₁ : (1 : K) ⊗ₜ[W] y₁ = ((l : W) ^ m) • b.repr.symm f := by
    have h5 : (d : W) • b.repr.symm f = (1 : K) ⊗ₜ[W] y₀ := hd
    rw [hy₁d, TensorProduct.tmul_smul, ← h5, smul_smul, hdβ]
    congr 1
    calc β' * ((l : W) ^ m * β) = (β' * β) * (l : W) ^ m := by ring
      _ = (l : W) ^ m := by rw [hβ', one_mul]
  have hrep : ∀ i, algebraMap K C (b.repr (1 ⊗ₜ y₁) i) =
      (l : C) ^ m * ((l : C) ^ N * (u * Φ z i)) := by
    intro i
    rw [hy₁, ← algebraMap_smul K, map_smul, LinearEquiv.apply_symm_apply, Finsupp.smul_apply,
      smul_eq_mul, map_mul, hf, ← IsScalarTower.algebraMap_apply, map_pow, map_natCast]
  have hΦx : Φ ((l : A) ^ (m + N) • z - t ^ s • ((1 : A) ⊗ₜ[W] y₁)) = 0 := by
    ext i
    rw [hΦsub, Finsupp.sub_apply, hΦs, hΦs, hΦt, hrep]
    simp only [map_pow, map_natCast, map_one, one_mul, Finsupp.coe_zero, Pi.zero_apply]
    have h6 : algebraMap A C t ^ s * ((l : C) ^ m * ((l : C) ^ N * (u * Φ z i))) =
        (l : C) ^ m * (l : C) ^ N * ((algebraMap A C t ^ s * u) * Φ z i) := by ring
    rw [h6, hu, pow_add]
    ring
  have hRx : R ((l : A) ^ (m + N) • z - t ^ s • ((1 : A) ⊗ₜ[W] y₁)) = 0 := by
    rw [hΦ] at hΦx
    exact e.map_eq_zero_iff.1 hΦx
  obtain ⟨b', hb'⟩ := loc_ker t _ (hR ▸ hRx)
  refine ⟨m + N, b', y₁, ?_⟩
  rw [smul_sub, sub_eq_zero, smul_smul, smul_smul] at hb'
  rw [mul_comm, hb', pow_add]

theorem UpperTheory.galois_equivariant_tensor_descent_of_prime_power_units :
    ∀ (l : ℕ) {W A C Γ : Type} {L : Type 1} [CommRing W] [IsDomain W] [CommRing A] [Algebra W A] [CommRing C]
        [AddCommGroup L] [Module W L] (c : A →+* C) (t : A) (σA : Γ → A →+* A) (σC : Γ → C →+* C) (χ : Γ → A)
        (T : Γ → (A ⊗[W] L →+ A ⊗[W] L)) (z : A ⊗[W] L) (s : ℕ),
        (∀ y : W, y ≠ 0 → ∃ (m : ℕ) (b : W), y = (l : W) ^ m * b ∧ IsUnit b) →
        IsUnit (l : C) → IsUnit (c t) →
        (∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a) →
        (∀ a : A, c a = 0 → ∃ r : ℕ, t ^ r * a = 0) →
        (∀ g a, σC g (c a) = c (σA g a)) →
        (∀ g (w : W), σA g (algebraMap W A w) = algebraMap W A w) →
        (∀ g, σA g t = χ g * t) →
        (∀ g (a : A) (y : L), T g (a ⊗ₜ[W] y) = σA g a ⊗ₜ[W] y) →
        (∀ x : C, (∀ g, σC g x = x) → ∃ (a : ℕ) (w : W), (l : C) ^ a * x = c (algebraMap W A w)) →
        (∀ g, ∃ a b : ℕ, ((l : A) ^ a * t ^ b) • T g z = ((l : A) ^ a * t ^ b * χ g ^ s) • z) →
        ∃ (a b : ℕ) (y : L), ((l : A) ^ a * t ^ b) • z = (t ^ (b + s)) • ((1 : A) ⊗ₜ[W] y) := by
  intro l W A C Γ L _ _ _ _ _ _ _ c t σA σC χ T z s hW hl hct hlocC hker hσ hσW hσt hT hfix hz
  letI : Algebra A C := c.toAlgebra
  letI : Algebra W C := (c.comp (algebraMap W A)).toAlgebra
  haveI : IsScalarTower W A C := IsScalarTower.of_algebraMap_eq' rfl
  have hunit : ∀ y : nonZeroDivisors W, IsUnit (algebraMap W C y) := by
    intro y
    obtain ⟨m, β, h, hβ⟩ := hW y (nonZeroDivisors.ne_zero y.2)
    rw [h, map_mul, map_pow, map_natCast]
    exact (hl.pow m).mul (hβ.map _)
  letI : Algebra (FractionRing W) C := (IsLocalization.lift hunit).toAlgebra
  haveI : IsScalarTower W (FractionRing W) C :=
    IsScalarTower.of_algebraMap_eq (fun w => (IsLocalization.lift_eq hunit w).symm)
  haveI : IsLocalization (Submonoid.powers t) C :=
    { map_units := by
        rintro ⟨_, n, rfl⟩
        exact (map_pow c t n).symm ▸ hct.pow n
      surj := by
        intro x
        obtain ⟨r, a, h⟩ := hlocC x
        refine ⟨(a, ⟨t ^ r, r, rfl⟩), ?_⟩
        change x * c (t ^ r) = c a
        rw [map_pow, mul_comm, h]
      exists_of_eq := by
        intro x y h
        obtain ⟨r, hr⟩ := hker (x - y) (by
          rw [map_sub, sub_eq_zero]
          exact h)
        refine ⟨⟨t ^ r, r, rfl⟩, ?_⟩
        rw [mul_sub, sub_eq_zero] at hr
        exact hr }
  exact aux (K := FractionRing W) l t σA σC χ T z s hW hl hσ hσW hσt hT hfix hz
end

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private theorem gRes_pow (r : Res l K) (f : ℕ) (hk : ∀ x : r.k, x ^ l ^ f = x) (x : OK l K) : gRes r x ^ l ^ f = gRes r x := by
  change (Ideal.Quotient.mk _) (r.s (r.ρ x)) ^ l ^ f = (Ideal.Quotient.mk _) (r.s (r.ρ x))
  rw [← map_pow, ← map_pow, hk]

private theorem galA_tA (g : K.fixingSubgroup) : ∃ χ : ℤ_[l]ˣ, galA g (tA l) = zA l χ * tA l :=
  ⟨cycloChar K (IntermediateField.fixingSubgroupEquiv K g), by
    have := ACris.gal_smul_periodT (K := K) (IntermediateField.fixingSubgroupEquiv K g) (untilt_epsilon (p := l))
    rwa [ACris.gal_smul_def] at this⟩

private theorem phiA_tA : phiA l (tA l) = (l : Acris l) * tA l := ACris.phi_periodT_eq_mul _

private theorem phiA_zA (x : ℤ_[l]) : phiA l (zA l x) = zA l x := by
  change ACris.phi (K := ℂ_[l]) (p := l) (algebraMap (Ainf l) (Acris l) (IsPerfectoidField.padicIntToWitt l x)) = _
  rw [ACris.phi_algebraMap]
  have h := AInf.isAdicComplete_p (K := ℂ_[l]) (p := l)
  have he := RingHom.congr_fun (ringHom_ext_padicInt
    ((WittVector.frobeniusEquiv l (PreTilt (↥(normInteger ℂ_[l])) l)).toRingHom.comp
      (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l))
    (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l)) x
  exact congrArg _ he

private theorem aux_sub {R Mo : Type*} [CommRing R] [AddCommGroup Mo] [Module R Mo] (A X t : R) (u s : ℕ) (G E : Mo)
    (h : A • G = (A * X ^ s) • E) : A • ((X * t) ^ u • G) - (A * X ^ (u + s)) • (t ^ u • E) = 0 := by
  rw [smul_comm A, h, smul_smul, smul_smul, ← sub_smul]
  convert zero_smul R E using 2
  ring

private theorem iter_smul_gen {R Mo : Type*} [SMul R Mo] (φ : R → R) (ϕ : Mo → Mo)
    (h : ∀ (a : R) (x : Mo), ϕ (a • x) = φ a • ϕ x) (N : ℕ) (a : R) (x : Mo) :
    ϕ^[N] (a • x) = (φ^[N] a) • ϕ^[N] x := by
  induction N generalizing a x with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply, h, ih, Function.iterate_succ_apply, Function.iterate_succ_apply]

private theorem phi_iter_smul (P : PAlg l ⥤ Type) (n j N : ℕ) (a : Acris l) (x : MH P n j) :
    (phiH P n j)^[N] (a • x) = ((phiA l)^[N] a) • (phiH P n j)^[N] x :=
  iter_smul_gen (phiA l) (phiH P n j) (fun a x => LinearMap.map_smulₛₗ ((phiMor P n).pull j) a x) N a x

private theorem phiA_iter_l (N : ℕ) : (phiA l)^[N] (l : Acris l) = l := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', ih, map_natCast]

private theorem phiA_iterate_tA (N : ℕ) : (phiA l)^[N] (tA l) = (l : Acris l) ^ N * tA l := by
  induction N with
  | zero => simp
  | succ N ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast, phiA_tA]; ring

private theorem phiA_iterate_zA (N : ℕ) (x : ℤ_[l]) : (phiA l)^[N] (zA l x) = zA l x := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', ih, phiA_zA]

private theorem chain1 {R Q H Γ : Type*} {Mn : ℕ → Type*} [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup H] [Module R H]
    [∀ n, AddCommGroup (Mn n)] [∀ n, Module R (Mn n)] (l : ℕ) (t : R) (φ : R →+* R) (σ : Γ → R →+* R) (X : Γ → R)
    (b : ∀ n, H →ₗ[R] Mn n) (G : Γ → H → H) (γ : ∀ g n, Mn n →ₛₗ[σ g] Mn n) (u s N : ℕ) (α : H →+ Q) (T : Γ → Q →+ Q)
    (hker : ∀ x, (∀ n, b n x = 0) → t ^ u • x = 0) (hgal : ∀ g x n, b n (G g x) = γ g n (b n x))
    (E : ∀ n, Mn n) (h : H) (hh : ∀ n, b n h = t ^ u • E n) (hχ : ∀ g, σ g t = X g * t)
    (hl : φ^[N] (l : R) = l) (ht : φ^[N] t = (l : R) ^ N * t) (hX : ∀ g, φ^[N] (X g) = X g)
    (lin : ∀ (a : R) x, α (a • x) = (φ^[N] a) • α x) (gal : ∀ g x, α (G g x) = T g (α x))
    (hab : ∀ g, ∃ a b' : ℕ, ∀ n, ((l : R) ^ a * t ^ b') • γ g n (E n) = ((l : R) ^ a * t ^ b' * X g ^ s) • E n) (g : Γ) :
    ∃ a b' : ℕ, ((l : R) ^ a * t ^ b') • T g (α h) = ((l : R) ^ a * t ^ b' * X g ^ (u + s)) • α h := by
  obtain ⟨a, c, hac⟩ := hab g
  have h0 := hker (((l : R) ^ a * t ^ c) • G g h - ((l : R) ^ a * t ^ c * X g ^ (u + s)) • h) fun n => by
    rw [map_sub, map_smul, map_smul, hgal, hh]
    have e2 : γ g n (t ^ u • E n) = (X g * t) ^ u • γ g n (E n) := by
      rw [← hχ g, LinearMap.map_smulₛₗ, map_pow]
    rw [e2]
    exact aux_sub _ _ _ _ _ _ _ (hac n)
  rw [smul_sub, smul_smul, smul_smul, sub_eq_zero] at h0
  have h1 := congrArg α h0
  rw [lin, lin, gal] at h1
  have it : ∀ (x y : R), φ^[N] (x * y) = φ^[N] x * φ^[N] y := fun x y => iterate_map_mul φ N x y
  have ip : ∀ (x : R) (k : ℕ), φ^[N] (x ^ k) = (φ^[N] x) ^ k := fun x k => iterate_map_pow φ N x k
  simp only [it, ip, hl, ht, hX] at h1
  refine ⟨a + N * (c + u), c + u, ?_⟩
  convert h1 using 2 <;> ring

private theorem chain2 {R Q H : Type*} {Mn : ℕ → Type*} [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup H] [Module R H]
    [∀ n, AddCommGroup (Mn n)] [∀ n, Module R (Mn n)] (l : ℕ) (t : R) (φ : R →+* R)
    (b : ∀ n, H →ₗ[R] Mn n) (P : H → H) (ϕ : ∀ n, Mn n → Mn n) (u r N e a' b' : ℕ) (α : H → Q) (β : Q →ₗ[R] H) (h : H) (q : Q)
    (E E' : ∀ n, Mn n) (hh : ∀ n, b n h = t ^ u • E n) (hl : φ^[N] (l : R) = l) (ht : φ^[N] t = (l : R) ^ N * t)
    (hy : ((l : R) ^ a' * t ^ b') • α h = t ^ (b' + (u + r)) • q) (fac : β (α h) = (l : R) ^ e • P^[N] h)
    (hphi : ∀ x n, b n (P x) = ϕ n (b n x)) (hit : ∀ n (a : R) x, (ϕ n)^[N] (a • x) = (φ^[N] a) • (ϕ n)^[N] x)
    (hE : ∀ n, (ϕ n)^[N] (E n) = E' n) (n : ℕ) :
    ((l : R) ^ (a' + e + N * u) * t ^ (b' + u)) • E' n = t ^ (b' + u + r) • b n (β q) := by
  have hP : ∀ (k : ℕ) x, b n (P^[k] x) = (ϕ n)^[k] (b n x) := fun k => by
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hphi, ih]
  have h1 := congrArg (fun x => b n (β x)) hy
  simp only [map_smul, fac, smul_smul, hP, hh, hit, hE] at h1
  have ip : ∀ (x : R) (k : ℕ), φ^[N] (x ^ k) = (φ^[N] x) ^ k := fun x k => iterate_map_pow φ N x k
  simp only [ip, ht, smul_smul] at h1
  have e1 : t ^ (b' + u + r) = t ^ (b' + (u + r)) := by rw [add_assoc]
  rw [e1, ← h1]
  congr 1
  ring

private theorem keyStep {r : Res l K} {M : Model l K} {f N j : ℕ} (hk : ∀ x : r.k, x ^ l ^ f = x)
    {Fr : PQ M.p (gRes r) ⟶ PQ M.p (gRes r)} {ρ : M.P ⟶ PQ M.p (gRes r)} (hFr : IsFr f Fr) (hρ : IsRd N ρ)
    (F : Pb.Fac r N) (hPin : Pin F M j) (y : Pb.LW r M j) (n : ℕ) :
    ∃ x : MH (PQ M.p (gRes r)) n j, (phiH _ n j)^[f] x = pullH Fr n j x ∧
      betaM M n j (levH (F.β M j ((1 : Pb.AW r) ⊗ₜ y)) n) = pullH ρ n j x :=
  Exists.elim (hPin n) fun m hm =>
    Exists.elim (absCl l K r M f N n j hk Fr ρ hFr hρ m hm.1 (y.1 n)) fun x hx =>
      ⟨x, hx.1, (congrArg (betaM M n j) (hm.2 y)).trans hx.2⟩

private def bl (M : Model l K) (j n : ℕ) : (M.HS true j).lim →ₗ[Acris l] M.MH n j :=
  (B.β (B.schFn M.p) (okToOC l K) true n j).comp ((LinearMap.proj n).comp (M.HS true j).lim.subtype)

private theorem witt_fac (k : Type) [Field k] [CharP k l] [PerfectRing k l] (y : WittVector l k) (hy : y ≠ 0) :
    ∃ (m : ℕ) (b : WittVector l k), y = (l : WittVector l k) ^ m * b ∧ IsUnit b := by
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' y hy
  exact ⟨m, b, e, b.isUnit⟩

private theorem isUnit_l (B₀ : PB l K) : IsUnit (l : B₀.C) := by
  have h : (l : B₀.C) = algebraMap ℚ_[l] B₀.C (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h]
  exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)).map _

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.absInvOf :
    UpperTheory.Ru.crystallineComparison.AbsInvOf := by
  intro l _ K r B₀ hC e he M hM f N j hk hfN hT F hPin hB ϖ hϖ
  obtain ⟨N', rfl⟩ := hfN
  have hg := gRes_pow r f hk
  obtain ⟨⟨Fr, hFr⟩, hρ', -⟩ := frEx l (OK l K) M.X M.p (okToOC l K) (gRes r) (f * N') f hg
  obtain ⟨ρ, hρ⟩ := hρ' (fun x w h => UpperTheory.integersResidue_eq_theta_coeff_pow_of_teichmuller r _ hT x w h)
  refine ⟨f * N', N', gRes r, Fr, ρ, UpperTheory.integersResidue_eq_zero_of_not_isUnit r ϖ hϖ, hg, hFr, hρ, ?_⟩
  intro ι _ v c s hinv
  obtain ⟨⟨u, hsurj, hker⟩, hphi, hgal⟩ := hB
  have hy := UpperTheory.evalEtaleFamily_mem_limit_of_reduced e he.red M j v c
  refine Exists.elim (hsurj ⟨_, hy⟩) fun h hh => ?_
  choose χ hχ using (galA_tA (K := K))
  letI iQ : Module (Acris l) (Pb.AL r M j) := (inferInstance : Module (per l K).A (Pb.AL r M j))
  have hz := chain1 (R := Acris l) (Q := Pb.AL r M j) (H := (M.HS true j).lim) (Γ := K.fixingSubgroup)
    (Mn := fun n => M.MH n j) l (tA l) (phiA l) galA (fun g => zA l (χ g)) (fun n => bl M j n) (fun g => Pb.galL M j g)
    (fun g n => M.galMH (IntermediateField.fixingSubgroupEquiv K g) n j) u s (f * N') (F.α M j) (F.galT M j)
    hker (fun g x n => hgal g x n) (fun n => evE e M j n v c) h hh hχ (phiA_iter_l _) (phiA_iterate_tA _)
    (fun g => phiA_iterate_zA _ _) (F.lin M hM j) (F.gal M hM j)
    (fun g => UpperTheory.galoisAction_evalEtaleFamily_exists_denominator B₀ e he M j s v c g (χ g) (hχ g) hinv)
  have hd := UpperTheory.galois_equivariant_tensor_descent_of_prime_power_units l (W := WittVector l r.k) (A := Pb.AW r) (C := B₀.C) (Γ := K.fixingSubgroup) (L := Pb.LW r M j)
    B₀.c (tA l) galA (fun g => (B₀.σ g).toRingHom) (fun g => zA l (χ g)) (F.galT M j) (F.α M j h) (u + s)
    (witt_fac r.k) (isUnit_l B₀) B₀.t_unit B₀.loc B₀.ker B₀.σ_c hC.1 hχ (fun g a y => F.galT_tmul M hM j g a y) hC.2 hz
  obtain ⟨a', b', y, hab⟩ := hd
  have key := keyStep hk hFr hρ F hPin y
  choose x hx1 hx2 using key
  refine ⟨a' + F.e M j + f * N' * u, b' + u, x, fun n => ⟨hx1 n, ?_⟩⟩
  have hc := chain2 (R := Acris l) (Q := Pb.AL r M j) (H := (M.HS true j).lim) (Mn := fun n => M.MH n j) l (tA l) (phiA l)
    (fun n => bl M j n) (fun x => Pb.phiL M j x) (fun n => phiH M.P n j) u s (f * N') (F.e M j) a' b' (F.α M j) (F.β M j) h
    ((1 : Pb.AW r) ⊗ₜ y) (fun n => evE e M j n v c) (fun n => evE e M j n v fun k => (phiA l)^[f * N'] (c k)) hh
    (phiA_iter_l _) (phiA_iterate_tA _) hab (F.fac M hM j h) (fun x n => hphi x n) (fun n a x => phi_iter_smul M.P n j _ a x)
    (fun n => UpperTheory.crisFrobenius_iterate_evalEtaleFamily e he.phi M j n _ v c) n
  exact hc.trans (congrArg _ (hx2 n))
