module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadratic
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadratic
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.L2.Host (IsUnifAt atFin)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

namespace InertValue

theorem single_ne' {K : Type} [Field K] [NumberField K] {P Q : HeightOneSpectrum (𝓞 K)} (h : Q ≠ P)
    (u : (P.adicCompletion K)ˣ) : (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 K) K) Q = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem exists_isUnifAt (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    ∃ a : (Fv F v)ˣ, IsUnifAt w (Units.map (complMap h).toMonoidHom a) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 (algebraMap F (Fv F v) π) ((map_ne_zero _).2 hπ0), ?_⟩
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have : w.asIdeal.LiesOver v.asIdeal := ⟨by subst h; rfl⟩
  have he : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [pow_one, hw']
    · exact InertChart.not_map_le_sq hw
  show Valued.v (complMap h (algebraMap F (Fv F v) π)) = WithZero.exp (-1)
  rw [complMap_algebraMap]
  have hvw : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap F E π)) = w.valuation E (algebraMap F E π) := by
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap F E π)
  rw [hvw, ← HeightOneSpectrum.valuation_liesOver E v w,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot, he, pow_one, hπ]

theorem locIdele_complMap (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (a : (Fv F v)ˣ) :
    locIdele F w (Units.map (complMap h).toMonoidHom a) =
      ideleMap F E (GlobalTheory.CMVal.finIdele F (GlobalTheory.CMVal.single v a)) := by
  subst h
  have key : (finAdEquiv F E).symm ((GlobalTheory.CMVal.single w (Units.map (complMap rfl).toMonoidHom a) :
      (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) =
      ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E) := by
    rw [RingEquiv.symm_apply_eq]
    refine FiniteAdeleRing.ext (h := fun u => ?_)
    rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = _)]
    simp only [Algebra.TensorProduct.map_tmul, toCompl_tmul, map_one, mul_one]
    classical
    have same : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (z : (P.adicCompletion K)ˣ),
        ((GlobalTheory.CMVal.single P z : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) P = z :=
      fun K _ _ P z => Pi.mulSingle_eq_same (M := fun R : HeightOneSpectrum (𝓞 K) => R.adicCompletion K) P
        (z : P.adicCompletion K)
    by_cases hu : u = w
    · subst hu
      rw [same]
      exact congrArg (complMap (rfl : u.under (𝓞 F) = _)) (same F _ a).symm
    · have hne : u.under (𝓞 F) ≠ w.under (𝓞 F) := fun h' => hu ((InertChart.under_eq_iff hw u).1 h')
      rw [single_ne' hu]
      have e2 : ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
          FiniteAdeleRing (𝓞 F) F) (u.under (𝓞 F)) = 1 := single_ne' hne a
      exact ((congrArg (complMap (rfl : u.under (𝓞 F) = _)) e2).trans (map_one _)).symm
  apply Units.ext
  show 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm ((GlobalTheory.CMVal.single w
      (Units.map (complMap rfl).toMonoidHom a) : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)) =
    algebraMap (AF F) (AF F ⊗[F] E) ((MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
      ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
  rw [key]
  generalize ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = s
  have h2 : extZero F E 1 = (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) 1)) ⊗ₜ[F] (1 : E) :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ 1 1
  have h3 : extZero F E (s ⊗ₜ[F] (1 : E)) = (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) s)) ⊗ₜ[F] (1 : E) :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ s 1
  have h4 : algebraMap (AF F) (AF F ⊗[F] E) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s) =
      (@id (AF F) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s)) ⊗ₜ[F] (1 : E) := rfl
  have hX : (1 : AF F) - (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) 1)) +
      (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) s)) =
      (@id (AF F) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s)) := by
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) - 0 + 0 = 1
      simp
    · show (1 : Af F) - 1 + s = s
      simp
  rw [h2, h3, h4, ← hX, TensorProduct.add_tmul, TensorProduct.sub_tmul]
  rfl

theorem eta_sq (h2 : Module.finrank F E = 2) {η : (AF F)ˣ →* Circle} (hη : IsEta F E η) (a : (AF F)ˣ) :
    η a ^ 2 = 1 := by
  have hn := hη.2.2.1 (ideleMap F E a)
  have hnorm : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (ideleMap F E a) = a ^ 2 := by
    apply Units.ext
    show Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (a : AF F)) = ((a ^ 2 : (AF F)ˣ) : AF F)
    rw [Units.val_pow_eq_pow_val,
      Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)), Fintype.card_fin, h2]
  rw [hnorm, map_pow] at hn
  exact hn

end InertValue


open InertValue in
theorem val_sq_eq_one_of_isInertAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ) (hμ : ResEta F E μ b)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (hw : IsInertAt F E v w) (hu : UnrAt μ w) :
    val μ w ^ 2 = 1 := by
  obtain ⟨⟨η, hη⟩, hres⟩ := hμ
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have hv : w.under (𝓞 F) = v := by
    ext1
    symm
    refine v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top ?_
    exact Ideal.map_le_iff_le_comap.1 hw'.le
  obtain ⟨a, ha⟩ := exists_isUnifAt hw hv
  rw [← UnrAt.locChar_eq_val hu ha]
  simp only [locChar, MonoidHom.comp_apply]
  rw [locIdele_complMap hw hv a, hres η hη, ← map_pow, ← pow_mul, mul_comm, pow_mul, eta_sq h2 hη, one_pow,
    map_one]

end GlobalTheory.LFun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadraticStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_value_eq_one_at_inert_place_of_restrictsToQuadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), IsInertAt F E v w → UnrAt μ w → val μ w ^ 2 = 1 := by
  first | exact @GlobalTheory.LFun.val_sq_eq_one_of_isInertAt | exact GlobalTheory.LFun.val_sq_eq_one_of_isInertAt | (intros; apply GlobalTheory.LFun.val_sq_eq_one_of_isInertAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterInfiniteOrderAtSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyEquivOfMem
open NumberField IsDedekindDomain
open _root_.Formalism.BasicNotions _root_.Formalism.L2.Host _root_.Formalism.FrobeniusOrbits
open _root_.Formalism.L2.DIV

namespace GlobalTheory.Formalism.L2.Col

namespace HostOk

variable {R : Ranks} {H : _root_.Formalism.BasicNotions.Host R} (T : Frame H)

theorem sigma_conj (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : σ (H.conj x) = H.conj (σ x) := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply (H.φ₀.comp (σ : H.E →+* H.E)) x
  have h2 := H.conjE_apply H.φ₀ (σ x)
  exact h1.trans h2.symm

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  (H.gal).apply_symm_apply g

theorem sigmaOf_b (g : R.Psi) : H.sigmaOf g H.sqrtMinusD = H.sqrtMinusD :=
  (H.galE_mem_Psi_iff _).1 (by rw [galE_sigmaOf]; exact g.2)

theorem d_pos (H : _root_.Formalism.BasicNotions.Host R) : 0 < H.d := H.hyp.2.1.pos

theorem b_sq (H : _root_.Formalism.BasicNotions.Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem conj_b (H : _root_.Formalism.BasicNotions.Host R) : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
  refine h2.trans ?_
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [map_neg, h3]
  simp

theorem b_ne (H : _root_.Formalism.BasicNotions.Host R) : H.sqrtMinusD ≠ -H.sqrtMinusD := by
  intro h
  have h0 : H.sqrtMinusD = 0 := by
    have : (2 : H.E) * H.sqrtMinusD = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have h1 := b_sq H
  rw [h0] at h1
  have h2 : (H.d : H.E) = 0 := by linear_combination h1
  have h3 : H.d = 0 := by exact_mod_cast h2
  exact (d_pos H).ne' h3

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)

end HostOk

end GlobalTheory.Formalism.L2.Col
end

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem val_map_eq_one {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {w : HeightOneSpectrum (𝓞 E)}
    (hN : Ideal.absNorm w.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) {z : E}
    (hz : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ w → Q.valuation E z = 1) (φ : E →+* E) (hφ : φ ≠ RingHom.id E) :
    w.valuation E (φ z) = 1 := by
  obtain ⟨Q, hQ⟩ := exists_pull φ w
  refine val_emb_eq_one hQ (hz Q fun e => hφ ?_)
  subst e
  exact GlobalTheory.ringHom_eq_of_comap_eq_unramified_degree_one E E φ (RingHom.id E) Q Q p hp hN hsq hQ (fun r => Iff.rfl)

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (n : D.R.Psi → ℤ) (p : ℕ), (∀ v, χ.TameAt v) → χ.HasInf (Formalism.L2.Host.embPsi D.host) n → (∀ g, n g ≠ 0) → SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  intro D χ n p ht hinf hn hp w hw hfin
  classical
  obtain ⟨hN, hsq⟩ := hp.2 w hw
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf D.host.E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht w (Formalism.L2.Host.unif w)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val w ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 =
      D.host.φ₀ (∏ g : D.R.Psi, (D.host.sigmaOf g z / D.host.sigmaOf g (D.host.conj z)) ^ n g) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : D.host.φ₀ (D.host.sigmaOf g (D.host.conj z)) = starRingEnd ℂ (D.host.φ₀ (D.host.sigmaOf g z)) := by
      rw [sigma_conj]
      exact D.host.conjE_apply D.host.φ₀ _
    have e' : Formalism.L2.Host.embPsi D.host g z = D.host.φ₀ (D.host.sigmaOf g z) := rfl
    have h0 : D.host.φ₀ (D.host.sigmaOf g z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ g : D.R.Psi, (D.host.sigmaOf g z / D.host.sigmaOf g (D.host.conj z)) ^ n g) ^ a = 1 := by
    apply D.host.φ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := w) ha (by rw [h6, map_one])
  have hc : ∀ g : D.R.Psi, w.valuation _ (D.host.sigmaOf g (D.host.conj z)) = 1 := by
    intro g
    refine val_map_eq_one hp.1 hN hsq h2
      ((D.host.sigmaOf g : D.host.E →+* D.host.E).comp (D.host.conj : D.host.E →+* D.host.E)) fun e => ?_
    have := RingHom.congr_fun e D.host.sqrtMinusD
    change D.host.sigmaOf g (D.host.conj D.host.sqrtMinusD) = D.host.sqrtMinusD at this
    rw [conj_b, map_neg, sigmaOf_b] at this
    exact b_ne D.host this.symm
  have hone : D.host.sigmaOf ((1 : D.R.Psi) : D.R.GG) = 1 :=
    map_one (D.host.gal).symm
  have hg : ∀ g : D.R.Psi, g ≠ 1 → w.valuation _ (D.host.sigmaOf g z) = 1 := by
    intro g hg
    refine val_map_eq_one hp.1 hN hsq h2 (D.host.sigmaOf g : D.host.E →+* D.host.E) fun e => hg ?_
    have e1 : D.host.sigmaOf g = D.host.sigmaOf ((1 : D.R.Psi) : D.R.GG) := by
      rw [hone]
      exact AlgEquiv.ext fun x => RingHom.congr_fun e x
    exact Subtype.ext ((D.host.gal).symm.injective e1)
  rw [map_prod, Finset.prod_eq_single 1 (fun g _ h => by rw [map_zpow₀, map_div₀, hg g h, hc g, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hone, AlgEquiv.one_apply, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn 1 h
  · omega
  · omega

end GlobalTheory.SplitValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqSumWeilComponentsAddTwoSmulLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqSumWeilComponentsAddTwoSmulLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.CompDecomp

open Filter Topology

theorem tendsto_one_sub_sum (F : Type) [Field F] [NumberField F] :
    Tendsto (fun Q : Finset (HeightOneSpectrum (𝓞 F)) => (1 : Af F) - ∑ v ∈ Q, singleV F v 1) atTop (𝓝 0) := by
  classical
  let A : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F) :=
    fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let y : Finset (HeightOneSpectrum (𝓞 F)) → (∀ v, A v) := fun Q v =>
    ⟨if v ∈ Q then 0 else 1, by
      by_cases h : v ∈ Q
      · rw [if_pos h]; exact (v.adicCompletionIntegers F).zero_mem
      · rw [if_neg h]; exact (v.adicCompletionIntegers F).one_mem⟩
  let z : ∀ v, A v := fun v => ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hy : Tendsto y atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro v
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [Filter.eventually_ge_atTop {v}] with Q hQ
    have hv : v ∈ Q := Finset.singleton_subset_iff.mp hQ
    apply Subtype.ext
    show (if v ∈ Q then (0 : v.adicCompletion F) else 1) = 0
    rw [if_pos hv]
  have hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      A Filter.cofinite) := RestrictedProduct.isEmbedding_structureMap.continuous
  have key : ∀ Q, (1 : Af F) - ∑ v ∈ Q, singleV F v 1 =
      RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A Filter.cofinite (y Q) := by
    intro Q
    apply FiniteAdeleRing.ext
    intro w
    have hw : ((1 : Af F) - ∑ v ∈ Q, singleV F v 1) w = evalV F w ((1 : Af F) - ∑ v ∈ Q, singleV F v 1) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sub, map_one, map_sum]
    show _ = (if w ∈ Q then (0 : w.adicCompletion F) else 1)
    by_cases h : w ∈ Q
    · rw [Finset.sum_eq_single_of_mem w h (fun b _ hb => GlobalTheory.LatVac.evalV_singleV_ne F b w (Ne.symm hb)),
        GlobalTheory.LatVac.evalV_singleV_same, if_pos h, sub_self]
    · rw [Finset.sum_eq_zero (fun b hb => GlobalTheory.LatVac.evalV_singleV_ne F b w (by rintro rfl; exact h hb)),
        if_neg h, sub_zero]
  have h0 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A
      Filter.cofinite z = (0 : Af F) :=
    by
      apply FiniteAdeleRing.ext
      intro w
      rfl
  have h1 : Tendsto (fun Q => (1 : Af F) - ∑ v ∈ Q, singleV F v 1) atTop
      (𝓝 (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A
        Filter.cofinite z)) :=
    ((hc.tendsto z).comp hy).congr (fun Q => (key Q).symm)
  rw [h0] at h1
  exact h1

variable {D : D7}

private theorem infComponent_algebraMap_pairA {D : D7} (a : Ainf D.host.F) (b : Af D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F a b)) = a ⊗ₜ[D.host.F] (1 : D.host.E) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

private theorem sum_sgW_plTau_eq_one (D : D7) :
    ∑ τ : D.what₂.Tau, GlobalTheory.AutFunCompare.sgW (plTau D τ) 1 = (1 : Ainf D.host.F) := by
  classical
  have hb := (GlobalTheory.CMTypePlaces.places_bijective D).sum_comp
    (fun w : InfinitePlace D.host.F => GlobalTheory.AutFunCompare.sgW w (1 : w.Completion))
  have h : ∑ w : InfinitePlace D.host.F, GlobalTheory.AutFunCompare.sgW w (1 : w.Completion) = (1 : Ainf D.host.F) := by
    have h' := Finset.univ_sum_single (1 : ∀ w : InfinitePlace D.host.F, w.Completion)
    simp only [Pi.one_apply] at h'
    simp only [GlobalTheory.AutFunCompare.sgW]
    exact h'
  exact hb.trans h

private theorem af_ext_of_fstA_sndA {F : Type} [Field F] [NumberField F] {x y : AF F}
    (h1 : fstA F x = fstA F y) (h2 : sndA F x = sndA F y) : x = y :=
  Prod.ext h1 h2

private theorem fstA_pairA_twisted_operators {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) :
    fstA F (pairA F a b) = a := rfl

private theorem sndA_pairA_twisted_operators {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) :
    sndA F (pairA F a b) = b := rfl

theorem one_sub_sum_idem (P : Finset (Place D)) (hP : P.toRight = Finset.univ) :
    1 - ∑ p ∈ P, idem D p = algebraMap (AF D.host.F) (AE D)
      (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1)) := by
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, hP]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show (1 : AE D) - (∑ v ∈ P.toLeft, idem D (.inl v) + ∑ τ : D.what₂.Tau, idem D (.inr τ)) =
      algebraMap (AF D.host.F) (AE D) (1 - (∑ v ∈ P.toLeft, pairA D.host.F 0 (singleV D.host.F v 1) +
        ∑ τ : D.what₂.Tau, pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0)) by
    rw [map_sub, map_add (f := _), map_one, map_sum, map_sum]
    rfl]
  congr 1
  apply af_ext_of_fstA_sndA
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [fstA_pairA_twisted_operators, map_sum, sum_sgW_plTau_eq_one D]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [sndA_pairA_twisted_operators, map_sum]

theorem exists_eq_sum_wAt_add_two_smul : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : WO S T, ∃ P₀ : Finset (Place D), ∀ P : Finset (Place D), P₀ ⊆ P → ∃ u ∈ (latO S T ΛS ΛT fun _ => True), w = ∑ p ∈ P, wAt p w + 2 • u := by
  intro D S T ΛS ΛT hS hT w
  classical
  have hU := GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 2 two_pos
  let g : Af D.host.F → WO S T := fun e => algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 e) • w
  have hg : Continuous g := by
    have h1 : Continuous fun e : Af D.host.F => pairA D.host.F 0 e :=
      (continuous_const.prodMk continuous_id : Continuous fun e : Af D.host.F => ((0 : Ainf D.host.F), e))
    have h2 : Continuous (algebraMap (AF D.host.F) (AE D)) := by
      have hs : (algebraMap (AF D.host.F) (AE D) : AF D.host.F → AE D) = fun r => r • (1 : AE D) := by
        funext r
        exact Algebra.algebraMap_eq_smul_one r
      rw [hs]
      exact Continuous.smul (f := fun r : AF D.host.F => r) (g := fun _ : AF D.host.F => (1 : AE D))
        continuous_id continuous_const
    exact (h2.comp h1).smul continuous_const
  have hg0 : g 0 = 0 := by
    show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 0) • w = 0
    rw [show pairA D.host.F 0 0 = 0 from rfl, map_zero, zero_smul]
  have hlim : Tendsto (fun Q => g (1 - ∑ v ∈ Q, singleV D.host.F v 1)) atTop (𝓝 0) := by
    have h := (hg.tendsto 0).comp (tendsto_one_sub_sum D.host.F)
    rw [hg0] at h
    exact h
  have hmem : (0 : WO S T) ∈ {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - (2 : ℕ) • l).map (finPart D) = 0} := by
    simp only [Set.mem_ofPred_eq]
    refine ⟨0, zero_mem _, ?_⟩
    simp
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 (hlim.eventually_mem (hU.mem_nhds hmem))
  refine ⟨Q₀.disjSum Finset.univ, fun P hP => ?_⟩
  have hR : P.toRight = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro τ
    rw [Finset.mem_toRight]
    exact hP (Finset.inr_mem_disjSum.2 (Finset.mem_univ τ))
  have hL : Q₀ ⊆ P.toLeft := by
    intro v hv
    rw [Finset.mem_toLeft]
    exact hP (Finset.inl_mem_disjSum.2 hv)
  obtain ⟨l, hl, hfin⟩ := hQ₀ _ hL
  refine ⟨l, hl, ?_⟩
  have hrest : w - ∑ p ∈ P, wAt p w = g (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1) := by
    show w - ∑ p ∈ P, wAt p w =
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1)) • w
    rw [← one_sub_sum_idem P hR, sub_smul, one_smul, Finset.sum_smul]
    congr 1
  have hl0 := GlobalTheory.SplitScalar.latO_fin hl
  have h2l : g (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1) = (2 : ℕ) • l := by
    ext i j
    apply GlobalTheory.SplitScalar.adele_ext
    · have hij := congrFun (congrFun hl0 i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at hij
      show infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1))
        * w i j) = infPart D ((2 : ℕ) • l i j)
      rw [map_mul, infComponent_algebraMap_pairA, TensorProduct.zero_tmul, zero_mul, map_nsmul, hij, smul_zero]
    · have hij := congrFun (congrFun hfin i) j
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply, map_sub] at hij
      exact sub_eq_zero.1 hij
  rw [← h2l, ← hrest]
  exact (add_sub_cancel _ _).symm

end GlobalTheory.PlaceTensor.CompDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqSumWeilComponentsAddTwoSmulLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : WO S T, ∃ P₀ : Finset (Place D), ∀ P : Finset (Place D), P₀ ⊆ P → ∃ u ∈ (latO S T ΛS ΛT fun _ => True), w = ∑ p ∈ P, wAt p w + 2 • u := by
  first | exact @GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul | exact GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul | (intros; apply GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchwartzBruhatHalfIffPullbackMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchwartzBruhatHalfIffPullbackMatrix
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfCoordSB

theorem eventually_pow_nsmul_mem {K M : Type} [NormedField K] [AddCommGroup M] [Module K M] [TopologicalSpace M]
    [ContinuousSMul K M] {p : ℕ} (hp : ‖(p : K)‖ < 1) {C U : Set M} (hC : IsCompact C) (hU : U ∈ 𝓝 (0 : M)) :
    ∀ᶠ n in Filter.atTop, ∀ x ∈ C, p ^ n • x ∈ U := by
  have hsmul : ∀ᶠ c in 𝓝 (0 : K), ∀ x ∈ C, c • x ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun y _ => ?_
    have ht : Filter.Tendsto (fun z : K × M => z.1 • z.2) (𝓝 ((0 : K), y)) (𝓝 (0 : M)) := (continuous_smul (M := K) (X := M)).tendsto' _ _ (by simp)
    exact ht hU
  have hpow : Filter.Tendsto (fun n : ℕ => (p : K) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp
  filter_upwards [hpow.eventually hsmul] with n hn x hx
  have hx' := hn x hx
  rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hx'

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  have hloc : ∀ y, ∀ᶠ z in 𝓝 y, Φ z = Φ y := fun y => (h1.isOpen_fiber (Φ y)).mem_nhds rfl
  have hK : IsCompact (tsupport Φ) := h2
  have hA : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Filter.Tendsto (fun z : M × M => z.2 + z.1) (𝓝 ((0 : M), y)) (𝓝 y) := (show Continuous fun z : M × M => z.2 + z.1 from continuous_snd.add continuous_fst).tendsto' _ _ (by simp)
    have hs : Filter.Tendsto (fun z : M × M => z.2) (𝓝 ((0 : M), y)) (𝓝 y) := continuous_snd.tendsto _
    filter_upwards [hc.eventually (hloc y), hs.eventually (hloc y)] with z h h'
    exact h.trans h'.symm
  have hB : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x - u) = Φ x := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Filter.Tendsto (fun z : M × M => z.2 - z.1) (𝓝 ((0 : M), y)) (𝓝 y) := (show Continuous fun z : M × M => z.2 - z.1 from continuous_snd.sub continuous_fst).tendsto' _ _ (by simp)
    have hs : Filter.Tendsto (fun z : M × M => z.2) (𝓝 ((0 : M), y)) (𝓝 y) := continuous_snd.tendsto _
    filter_upwards [hc.eventually (hloc y), hs.eventually (hloc y)] with z h h'
    exact h.trans h'.symm
  filter_upwards [hA, hB] with u hu hu' x
  by_cases hx : x ∈ tsupport Φ
  · exact hu x hx
  by_cases hxu : x + u ∈ tsupport Φ
  · simpa using (hu' (x + u) hxu).symm
  have h0 : Φ x = 0 := by
    by_contra h
    exact hx (subset_tsupport Φ h)
  have h0' : Φ (x + u) = 0 := by
    by_contra h
    exact hxu (subset_tsupport Φ h)
  rw [h0, h0']

variable {D : D7} {m n : ℕ} {a : AE D}

theorem isHalf_add {x y : Mx D m n} (hx : IsHalf a x) (hy : IsHalf a y) : IsHalf a (x + y) := by
  unfold IsHalf at hx hy ⊢
  intro i j
  rw [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_sub {x y : Mx D m n} (hx : IsHalf a x) (hy : IsHalf a y) : IsHalf a (x - y) := by
  unfold IsHalf at hx hy ⊢
  intro i j
  rw [Matrix.sub_apply, mul_sub, hx i j, hy i j]

theorem isHalf_nsmul {x : Mx D m n} (hx : IsHalf a x) (k : ℕ) : IsHalf a (k • x) := by
  induction k with
  | zero =>
    unfold IsHalf
    intro i j
    simp
  | succ k ih =>
    rw [succ_nsmul]
    exact isHalf_add ih hx

theorem isSBHalf_iff_pull : ∀ (D : D7) (S T : HSp D) (v : FinPl D) (m n : ℕ) (a : AE D) (Λ : AddSubgroup (WO S T)) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a Λ κ → (∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsSBHalf a Λ (pull a κ Φ)) ∧ ∀ Ψ, IsSBHalf a Λ Ψ → ∃ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), Ψ = pull a κ Φ := by
  intro D S T v m n a Λ κ hκ
  unfold IsCoord at hκ
  obtain ⟨hadd, hbij, hopen, hcpt⟩ := hκ
  have h0 : κ 0 = 0 := by simpa using hadd 0 0
  have hns : ∀ (k : ℕ) (t : WO S T), κ (k • t) = k • κ t := by
    intro k t
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [succ_nsmul, succ_nsmul, hadd, ih]
  have hz : IsHalf a (0 : WO S T) := by
    unfold IsHalf
    intro i j
    simp
  have hO0 : κ '' {t | t ∈ Λ ∧ IsHalf a t} ∈ 𝓝 (0 : Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
    hopen.mem_nhds ⟨0, ⟨Λ.zero_mem, hz⟩, h0⟩
  refine ⟨fun Φ hΦ => ?_, fun Ψ hΨ => ?_⟩
  ·
    obtain ⟨p, hp0, hp⟩ : ∃ p : ℕ, 0 < p ∧ ‖(p : Fv D.host.F v)‖ < 1 := by
      refine ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero ?_, ?_⟩
      · rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact v.ne_bot
      · have h := (NumberField.FinitePlace.norm_lt_one_iff_mem D.host.F v
          ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.F)).mpr (Ideal.absNorm_mem v.asIdeal)
        simpa using h
    have hΦ' : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
    obtain ⟨h1, h2⟩ := hΦ'
    have hU := eventually_invariant h1 h2
    have E1 := eventually_pow_nsmul_mem hp hcpt hU
    have E2 := eventually_pow_nsmul_mem hp h2 hO0
    obtain ⟨N, hN1, hN2⟩ := (E1.and E2).exists
    unfold IsSBHalf
    refine ⟨fun t ht => ?_, p ^ N, pow_pos hp0 N, fun u hu hhu t => ?_, fun t ht => ?_⟩
    · by_contra hh
      exact ht (by simp [pull, hh])
    · by_cases htH : IsHalf a t
      · have h' : IsHalf a (t + (p ^ N) • u) := isHalf_add htH (isHalf_nsmul hhu _)
        have hm : ∀ x, Φ (x + (p ^ N) • κ u) = Φ x := hN1 (κ u) ⟨u, ⟨hu, hhu⟩, rfl⟩
        simp only [pull, if_pos htH, if_pos h']
        rw [hadd, hns]
        exact hm (κ t)
      · have h' : ¬ IsHalf a (t + (p ^ N) • u) := by
          intro hc
          apply htH
          have hc' := isHalf_sub hc (isHalf_nsmul hhu (p ^ N))
          simpa using hc'
        simp only [pull, if_neg htH, if_neg h']
    · have htH : IsHalf a t := by
        by_contra hh
        exact ht (by simp [pull, hh])
      have hΦt : Φ (κ t) ≠ 0 := by simpa [pull, htH] using ht
      obtain ⟨s, ⟨hsΛ, hsH⟩, hs⟩ := hN2 (κ t) (subset_tsupport Φ hΦt)
      have hk : IsHalf a ((p ^ N) • t) := isHalf_nsmul htH _
      have hst : s = (p ^ N) • t := hbij.injOn hsH hk (by rw [hs, hns])
      rw [← hst]
      exact hsΛ
  · unfold IsSBHalf at hΨ
    obtain ⟨hsupp, k, hk0, hinv, hΛ⟩ := hΨ

    obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin m) (Fin n) (Fv D.host.F v) → WO S T,
        ∀ x, IsHalf a (g x) ∧ κ (g x) = x :=
      ⟨Function.invFunOn κ {t | IsHalf a t}, fun x =>
        ⟨Function.invFunOn_mem (hbij.surjOn (Set.mem_univ x)), Function.invFunOn_eq (hbij.surjOn (Set.mem_univ x))⟩⟩
    have hgk : ∀ t, IsHalf a t → g (κ t) = t := fun t ht => hbij.injOn (hg _).1 ht (hg _).2
    have : CharZero (Fv D.host.F v) :=
      charZero_of_injective_algebraMap (R := D.host.F) (algebraMap D.host.F (Fv D.host.F v)).injective
    have hkF : ((k : ℕ) : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
    refine ⟨fun x => Ψ (g x), ?_, ?_⟩
    · show IsLocallyConstant (fun x => Ψ (g x)) ∧ HasCompactSupport (fun x => Ψ (g x))
      refine ⟨?_, ?_⟩
      · rw [IsLocallyConstant.iff_eventually_eq]
        intro x
        have hW : (fun z : Matrix (Fin m) (Fin n) (Fv D.host.F v) => (k : Fv D.host.F v) • z) ''
            (κ '' {t | t ∈ Λ ∧ IsHalf a t}) ∈ 𝓝 (0 : Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
          (isOpenMap_smul₀ hkF _ hopen).mem_nhds ⟨0, ⟨0, ⟨Λ.zero_mem, hz⟩, h0⟩, smul_zero _⟩
        have hc : Filter.Tendsto (fun y : Matrix (Fin m) (Fin n) (Fv D.host.F v) => y - x) (𝓝 x) (𝓝 0) :=
          (show Continuous fun y : Matrix (Fin m) (Fin n) (Fv D.host.F v) => y - x from
            continuous_id.sub continuous_const).tendsto' _ _ (by simp)
        filter_upwards [hc.eventually_mem hW] with y hy
        obtain ⟨w, ⟨u, ⟨huΛ, huH⟩, rfl⟩, hw0⟩ := hy
        have hw : (k : Fv D.host.F v) • κ u = y - x := hw0
        have hy' : y = x + κ (k • u) := by
          rw [hns, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v), hw]
          abel
        have hgy : g y = g x + k • u := by
          rw [hy']
          apply hbij.injOn (hg _).1 (isHalf_add (hg x).1 (isHalf_nsmul huH k))
          rw [(hg _).2, hadd, (hg x).2]
        show Ψ (g y) = Ψ (g x)
        rw [hgy]
        exact hinv u huΛ huH (g x)
      · refine HasCompactSupport.intro
          (K := (fun z : Matrix (Fin m) (Fin n) (Fv D.host.F v) => (k : Fv D.host.F v)⁻¹ • z) ''
            (κ '' {t | t ∈ Λ ∧ IsHalf a t}))
          (hcpt.image (continuous_const_smul _)) ?_
        intro x hx
        by_contra hne
        apply hx
        have hm := hΛ (g x) hne
        have hmem : κ (k • g x) ∈ κ '' {t | t ∈ Λ ∧ IsHalf a t} := ⟨_, ⟨hm, isHalf_nsmul (hg x).1 k⟩, rfl⟩
        rw [hns, (hg x).2, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v)] at hmem
        exact ⟨_, hmem, inv_smul_smul₀ hkF x⟩
    · funext t
      by_cases ht : IsHalf a t
      · simp only [pull, if_pos ht]
        rw [hgk t ht]
      · simp only [pull, if_neg ht]
        by_contra hne
        exact ht (hsupp t hne)

end GlobalTheory.HalfCoordSB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchwartzBruhatHalfIffPullbackMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_iff_pullback_matrix : ∀ (D : D7) (S T : HSp D) (v : FinPl D) (m n : ℕ) (a : AE D) (Λ : AddSubgroup (WO S T)) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a Λ κ → (∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsSBHalf a Λ (pull a κ Φ)) ∧ ∀ Ψ, IsSBHalf a Λ Ψ → ∃ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), Ψ = pull a κ Φ := by
  first | exact @GlobalTheory.HalfCoordSB.isSBHalf_iff_pull | exact GlobalTheory.HalfCoordSB.isSBHalf_iff_pull | (intros; apply GlobalTheory.HalfCoordSB.isSBHalf_iff_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniqueIsContr
noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ContrObj

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]

theorem norm_of_isIsoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem exists_riesz [CompleteSpace H₁] {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (φ : FF) (y : H₂) :
    ∃ w : H₁, ∀ x, ⟪x, w⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := by
  let ℓ : H₁ →L[ℂ] ℂ := ((innerₛₗ ℂ φ) ∘ₗ Tm.flip y).mkContinuous (‖φ‖ * ‖y‖) fun x => by
    have := norm_inner_le_norm (𝕜 := ℂ) φ (Tm x y)
    rw [norm_of_isIsoBilin hI] at this
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℂ H₁).surjective ℓ
  refine ⟨w, fun x => ?_⟩
  have h : ⟪w, x⟫_ℂ = ⟪φ, Tm x y⟫_ℂ := by
    have := congrArg (fun f : H₁ →L[ℂ] ℂ => f x) hw
    simpa [ℓ] using this
  rw [← inner_conj_symm, h, inner_conj_symm]

theorem existsUnique_isContr [CompleteSpace H₁] {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃! It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  choose w hw using exists_riesz hI
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) w ?_ ?_ ?_ ?_, fun φ y x => hw φ y x, ?_⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_add_right]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_smul_right]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp [hw, inner_add_right, inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_smul_right, inner_smul_left, mul_comm]
  · intro It hIt
    ext φ y
    exact ext_inner_left ℂ fun x => (hIt φ y x).trans (hw φ y x).symm

end Hilbert

theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  exact ⟨existsUnique_isContr hI, fun It hC => contrProps_of hI hE hC⟩

section Tensor

open MvPolynomial

variable {ι : Type} [Fintype ι] {σ : ι → Type} {Var : Type} (e : (Σ τ, σ τ) ≃ Var)

omit [Fintype ι] in
theorem emb_injective (i : ι) : Function.Injective fun s : σ i => e ⟨i, s⟩ :=
  e.injective.comp sigma_mk_injective

def res (α : Var →₀ ℕ) (i : ι) : σ i →₀ ℕ :=
  Finsupp.comapDomain (fun s : σ i => e ⟨i, s⟩) α (emb_injective e i).injOn

theorem res_sum (a : ∀ i, σ i →₀ ℕ) :
    res e (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) = a := by
  classical
  funext j
  ext s
  change (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) (e ⟨j, s⟩) = a j s
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · exact Finsupp.mapDomain_apply_of_injective (emb_injective e j) _ _
  · intro i _ hi
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨t, ht⟩
    exact hi (congrArg Sigma.fst (e.injective ht))
  · simp

variable {A B : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]

def tens (I : ∀ i, MvPolynomial (σ i) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) :
    MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i :=
  (basisMonomials Var ℂ).constr ℂ fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1)

theorem tens_prod (I : ∀ i, MvPolynomial (σ i) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) (P : ∀ i, MvPolynomial (σ i) ℂ) :
    tens e I (∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i)) = PiTensorProduct.map fun i => I i (P i) := by
  classical
  let pr : MultilinearMap (RingHom.id ℂ) (fun i : ι => MvPolynomial (σ i) ℂ) (MvPolynomial Var ℂ) :=
    (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun i => (rename (fun s : σ i => e ⟨i, s⟩) : MvPolynomial (σ i) ℂ →ₐ[ℂ] _).toLinearMap
  have hpr : ∀ P, pr P = ∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i) := fun P => by simp [pr]
  have key : (tens e I).compMultilinearMap pr
      = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap I := by
    refine Module.Basis.ext_multilinear (fun i => basisMonomials (σ i) ℂ) fun a => ?_
    simp only [LinearMap.compMultilinearMap_apply, hpr, coe_basisMonomials,
      MultilinearMap.compLinearMap_apply, PiTensorProduct.mapMultilinear_apply, rename_monomial]
    rw [← monomial_sum_one]
    have := (basisMonomials Var ℂ).constr_basis ℂ
      (fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1))
      (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i))
    rw [res_sum, coe_basisMonomials] at this
    exact this
  have := congrArg (fun f => f P) key
  simpa [hpr] using this

theorem tprod_ne_zero (v : ∀ i, B i) (hv : ∀ i, v i ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0
  simp [hl] at this

end Tensor

theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ I
  have h : IsTensorIt e I (tens e I) := fun P v => by
    rw [tens_prod, PiTensorProduct.map_tprod]
  refine ⟨tens e I, h, fun hI h0 => ?_⟩
  have hex : ∀ i, ∃ P v, I i P v ≠ 0 := by
    intro i
    by_contra hc
    push Not at hc
    exact hI i (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using hex
  have h1 := h P v
  rw [h0] at h1
  exact tprod_ne_zero _ hPv h1.symm

theorem contraction : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction := ⟨contrHilbert, contrTensor⟩

end GlobalTheory.ContrObj

end
end
