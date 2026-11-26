module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscrete
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.AntiRamConj GlobalTheory.AntiLAdic

namespace GlobalTheory.ConjPoly

theorem charpoly_smul_inv {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) (m : Multiset ℂ) (c : ℂ)
    (hM : M.charpoly = (m.map fun β => X - C β).prod) :
    (c • N).charpoly = (m.map fun β => X - C (c * β⁻¹)).prod := by
  have hcard : Multiset.card m = n := by
    have := congrArg natDegree hM
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card, Fintype.card_fin] at this
    exact this.symm
  have ev : ∀ y : ℂ, (Matrix.scalar (Fin n) y - M).det = (m.map fun β => y - β).prod := fun y => by
    rw [← Matrix.eval_charpoly, hM, eval_multiset_prod, Multiset.map_map]
    simp
  have h0 : (-M).det = (m.map fun β => -β).prod := by simpa using ev 0
  have hne : (-M).det ≠ 0 := by
    intro e
    have : (-M * -N).det = 1 := by rw [neg_mul_neg, h, Matrix.det_one]
    rw [Matrix.det_mul, e, zero_mul] at this
    exact zero_ne_one this
  have hβ : ∀ β ∈ m, β ≠ 0 := by
    rintro β hβ rfl
    apply hne
    rw [h0]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨0, hβ, neg_zero⟩)
  refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono ?_)
  intro x hx
  have hx0 : x ≠ 0 := hx
  show eval x _ = eval x _
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map]
  apply mul_left_cancel₀ hne
  have e1 : -M * (Matrix.scalar (Fin n) x - c • N) = x • (Matrix.scalar (Fin n) (c / x) - M) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, ← Matrix.smul_one_eq_diagonal,
      mul_sub, Matrix.mul_smul, Matrix.mul_smul, neg_mul, neg_mul, h, smul_sub, smul_smul, mul_div_cancel₀ _ hx0]
    simp
    abel
  rw [← Matrix.det_mul, e1, Matrix.det_smul, ev, h0, ← Multiset.prod_map_mul, Fintype.card_fin, ← hcard,
    ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun β hb => ?_
  have := hβ β hb
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  field_simp
  ring

theorem continuous_cyc_val (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous fun g : G F Ω => ((cyc F Ω l g : (Qbar l)ˣ) : Qbar l) := by
  have h1 : Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) := continuous_algebraMap _ _
  have h2 : Continuous fun z : ℤ_[l] => (z : ℚ_[l]) := continuous_subtype_val
  exact h1.comp (h2.comp (Units.continuous_val.comp (continuous_cycZ F Ω l)))

theorem cyc_val_frob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (h : IsPlaceOver A v) {σ : G F Ω} (hσ : IsFrob A (normV v) σ) :
    ((cyc F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
  rw [cyc_eq_map_cycZ, Units.coe_map, cycZ_of_isFrob hl h hσ]
  simp

theorem normV_ne_zero {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : normV v ≠ 0 := by
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  exact Nat.card_pos.ne'

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l ≠ 0) : (placesOver E l).Finite := by
  have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
    simpa using hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton, placesOver] using hv

theorem exists_conj (D : D7) : ∃ bar : PlE D.host → PlE D.host, Function.Injective bar ∧
    ∀ w, IsConjPl D.host w (bar w) ∧ normV (bar w) = normV w ∧ (IsSplitPl D.host w → IsSplitPl D.host (bar w)) := by
  choose bar hbar using fun v => (GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv v).exists
  have hbb : ∀ v, bar (bar v) = v := fun v =>
    (GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv (bar v)).unique (hbar _)
      (conjPl_symm (host_conj_conj D) (hbar v))
  have hc : ∀ v, IsConjPl D.host v (bar v) := fun v => (GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).1 (hbar v)
  refine ⟨bar, Function.LeftInverse.injective hbb, fun w => ⟨hc w, normV_conjPl (hbar w), ?_⟩⟩
  rintro ⟨x, hx, hx'⟩
  let y : 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv x
  have hy : (y : D.host.E) = D.host.conj x := rfl
  refine ⟨y, (hc w x y hy).1 hx, fun z hz hzm => ?_⟩
  rw [hy, host_conj_conj] at hz
  have hzx : z = x := Subtype.ext hz
  rw [hzx] at hzm
  exact hx' y hy ((hc w y x (by rw [hy, host_conj_conj])).2 hzm)

theorem isoLoc_single (D : D7) (π : D.naut.CG D.R.r) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨D.R.r, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem cpow_sq {q : ℂ} (hq : q ≠ 0) (s : ℝ) (k : ℤ) (h : (k : ℝ) = 2 * s) : q ^ k = q ^ (s : ℂ) * q ^ (s : ℂ) := by
  rw [← Complex.cpow_add _ _ hq, ← Complex.cpow_intCast]
  congr 1
  rw [← two_mul]
  exact_mod_cast h

theorem charpoly_conj (D : D7) (hD : FrobDense D) (i : D.nd.Loc) (π : D.naut.CG D.R.r)
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (hπ : D.naut.csd π)
    (hρ : IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ)
    (hc : ∀ x : D.host.E, ∃ y : D.host.E,
      D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y) (g : G D.host.E D.nd.Om) :
    (((ρ (conjHom D.ntw.cc hc g) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
        (iotaOQ D.nd D.naut i)).charpoly =
      ((((cyc D.host.E D.nd.Om (D.nd.l i) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) ^ (1 - (D.R.r : ℤ))) •
        ((ρ g⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaOQ D.nd D.naut i)).charpoly := by
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  obtain ⟨bar, hinj, hbar⟩ := exists_conj D
  obtain ⟨hcont, -, hfr⟩ := hρ
  have hι := (iotaOQ_continuous_injective D i).1
  have hfr' := hinj.tendsto_cofinite.eventually hfr
  have hl := (finite_placesOver D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).compl_mem_cofinite
  have hall := (hfr.and hfr').and ((D.naut.locG_unr_ae π).and hl)
  refine charpoly_eq_of_dense (G D.host.E D.nd.Om) (Qbar (D.nd.l i)) D.R.r
    (fun g => ((ρ (conjHom D.ntw.cc hc g) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
        (iotaOQ D.nd D.naut i))
    (fun g => (((cyc D.host.E D.nd.Om (D.nd.l i) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) ^ (1 - (D.R.r : ℤ))) •
        ((ρ g⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaOQ D.nd D.naut i)) _ (hD _ (Filter.eventually_cofinite.1 hall))
    ((hcont.comp (continuous_conjHom D.ntw.cc hc)).matrix_map hι)
    (((continuous_cyc_val D.host.E D.nd.Om (D.nd.l i)).zpow₀ (1 - (D.R.r : ℤ))
      fun g => Or.inl (Units.ne_zero _)).fun_smul ((hcont.comp continuous_inv).matrix_map hι)) ?_ g
  rintro σ ⟨w, hw, -, B, hB, hσ⟩
  obtain ⟨⟨h1, h2⟩, hu, hwl⟩ := not_not.1 hw
  obtain ⟨hcj, hn, -⟩ := hbar w
  obtain ⟨hu', he⟩ := D.naut.csd_unr π w (bar w) hπ hcj hu
  have e1 := h1 B σ hB hσ
  have e2 := h2 _ _ (isPlaceOver_moveVal D hcj hB) (by rw [hn]; exact isFrob_conjHom D.ntw.cc hc hσ)
  rw [isoLoc_single, galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  rw [isoLoc_single, galPol, D.naut.frobEig_tw _ _ hu', he, hn, ← Matrix.charpoly_map] at e2
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (normV_ne_zero w)
  have e3 := charpoly_smul_inv _
    (((ρ σ⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaO D.nd D.naut i))
    (by rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]) _ (((normV w : ℕ) : ℂ) ^ (1 - (D.R.r : ℤ))) e1
  apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
  beta_reduce
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, cyc_val_frob hwl hB hσ]
  refine e2.trans (Eq.trans ?_ (e3.symm.trans ?_))
  · rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    rw [cpow_sq hq ((1 - (D.R.r : ℝ)) / 2) _ (by push_cast; ring)]
    have : ((normV w : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) ≠ 0 := by
      simp [hq]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel_right₀ this, mul_comm a⁻¹]
  · congr 1
    ext a b
    simp [iotaO, iotaOQ]

theorem chi_conj (D : D7) (hD : FrobDense D) (i : D.nd.Loc)
    (hc : ∀ x : D.host.E, ∃ y : D.host.E,
      D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y) (g : G D.host.E D.nd.Om) :
    iotaOQ D.nd D.naut i (D.nd.chi i 1 (conjHom D.ntw.cc hc g) : (D.nd.O i)ˣ) *
        iotaOQ D.nd D.naut i (D.nd.chi i 1 g : (D.nd.O i)ˣ) =
      ((cyc D.host.E D.nd.Om (D.nd.l i) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) ^ ((D.R.t : ℤ) - (D.R.nV : ℤ)) := by
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  obtain ⟨bar, hinj, hbar⟩ := exists_conj D
  have hι := (iotaOQ_continuous_injective D i).1
  have hl := (finite_placesOver D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).compl_mem_cofinite
  have hout : ∀ᶠ w in Filter.cofinite, w ∉ placesOver D.host.E (D.nd.l i) ∧ w ∉ D.nd.S i ∧ w ∉ D.nd.Q i :=
    Filter.Eventually.and hl ((D.nd.S i).eventually_cofinite_notMem.and (D.nd.Q i).eventually_cofinite_notMem)
  have hall := (hout.and (hinj.tendsto_cofinite.eventually hout)).and (D.naut.locG_unr_ae (D.naut.muC i))
  have hχ := hι.comp (D.nd.chi_cont i 1)
  refine congrFun (Continuous.ext_on (hD _ (Filter.eventually_cofinite.1 hall))
    ((hχ.comp (continuous_conjHom D.ntw.cc hc)).mul hχ)
    ((continuous_cyc_val _ _ _).zpow₀ _ fun g => Or.inl (Units.ne_zero _)) ?_) g
  rintro σ ⟨w, hw, hs, B, hB, hσ⟩
  obtain ⟨⟨h1, h2⟩, hu⟩ := not_not.1 hw
  obtain ⟨hcj, hn, hs'⟩ := hbar w
  obtain ⟨hu', he⟩ := D.naut.csd_unr _ w (bar w) (D.naut.muC_csd i) hcj hu
  obtain ⟨u1, e1⟩ := D.naut.chi_mu i w ⟨hs, h1⟩
  obtain ⟨u2, e2⟩ := D.naut.chi_mu i (bar w) ⟨hs' hs, h2⟩
  have e1 := e1 B σ hB hσ
  have e2 := e2 _ _ (isPlaceOver_moveVal D hcj hB) (by rw [hn]; exact isFrob_conjHom D.ntw.cc hc hσ)
  have one : ∀ (χ : D.naut.CG 1) (v : PlE D.host), D.naut.unr (D.naut.locG χ v) →
      ∃ a, D.naut.frobEig (D.naut.locG χ v) = {a} := fun χ v h =>
    Multiset.card_eq_one.1 ((D.naut.frobEig_card _ h).trans (D.naut.locG_dim χ v))
  obtain ⟨a, ha⟩ := one _ w (D.naut.etaT_unr w)
  obtain ⟨b, hb⟩ := one _ (bar w) (D.naut.etaT_unr (bar w))
  obtain ⟨m, hm⟩ := one _ w hu
  have hab := D.naut.etaT_split w (bar w) hs hcj a b ha hb
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact D.naut.frobEig_ne_zero _ hu (by rw [hm]; exact Multiset.mem_singleton_self _)
  obtain ⟨v1, f1⟩ := D.naut.etaTinv_def w
  obtain ⟨v2, f2⟩ := D.naut.etaTinv_def (bar w)
  rw [ha, Multiset.map_singleton] at f1
  rw [hb, Multiset.map_singleton] at f2
  rw [D.naut.frobEig_tw _ _ u1, D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu v1 (D.naut.locG_dim _ _) f1, hm,
    Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj] at e1
  rw [D.naut.frobEig_tw _ _ u2, D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu' v2 (D.naut.locG_dim _ _) f2, he, hm,
    Multiset.map_singleton, Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj, hn] at e2
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (normV_ne_zero w)
  apply (D.naut.iotaQC i).injective
  simp only [Function.comp_apply, Pi.mul_apply]
  rw [map_mul, cyc_val_frob h1.1 hB hσ, map_zpow₀, map_natCast,
    cpow_sq hq (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) _ (by push_cast; ring)]
  refine (congrArg₂ (· * ·) e2.symm e1.symm).trans ?_
  have hab' : a⁻¹ * b⁻¹ = 1 := by rw [← mul_inv, hab, inv_one]
  have hmm : m⁻¹ * m = 1 := inv_mul_cancel₀ hm0
  generalize ((normV w : ℕ) : ℂ) ^ ((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2 : ℝ) : ℂ) = y
  calc m⁻¹ * b⁻¹ * y * (m * a⁻¹ * y) = (m⁻¹ * m) * (a⁻¹ * b⁻¹) * (y * y) := by ring
    _ = y * y := by rw [hmm, hab', one_mul, one_mul]

theorem conj_inertia : ∀ D : D7, FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ (w : PlE D.host) (B : ValuationSubring D.nd.Om), w ∉ placesOver D.host.E (D.nd.l i) → IsPlaceOver (F := D.host.E) B w → ∀ s ∈ Ine (F := D.host.E) B, ∀ s' : G D.host.E D.nd.Om, (∀ y, s' (D.ntw.cc y) = D.ntw.cc (s y)) → ((ρ s' : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = ((ρ s⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly ∧ D.nd.chi i 1 s' = D.nd.chi i 1 s⁻¹ := by
  intro D hD i π ρ hπ hρ w B hw hB s hs s' hs'
  have hc : ∀ x : D.host.E, ∃ y : D.host.E,
      D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y :=
    fun x => ⟨_, cc_symm_algebraMap_host D x⟩
  obtain rfl : s' = conjHom D.ntw.cc hc s := by
    ext y
    rw [conjHom_apply, ← hs', RingEquiv.apply_symm_apply]
  have hε : cyc D.host.E D.nd.Om (D.nd.l i) s = 1 := cyc_eq_one_of_mem_Ine hw hB hs
  have hι := (iotaOQ_continuous_injective D i).2
  constructor
  · have h := charpoly_conj D hD i π ρ hπ hρ hc s
    rw [hε, Units.val_one, one_zpow, one_smul, Matrix.charpoly_map, Matrix.charpoly_map] at h
    exact Polynomial.map_injective _ hι h
  · have h := chi_conj D hD i hc s
    rw [hε, Units.val_one, one_zpow, ← map_mul, ← map_one (iotaOQ D.nd D.naut i), ← Units.val_mul] at h
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left (Units.ext (hι h))

end GlobalTheory.ConjPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentationStatement
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_compatible_conjugation_representation : ∀ D : D7, FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ (w : PlE D.host) (B : ValuationSubring D.nd.Om), w ∉ placesOver D.host.E (D.nd.l i) → IsPlaceOver (F := D.host.E) B w → ∀ s ∈ Ine (F := D.host.E) B, ∀ s' : G D.host.E D.nd.Om, (∀ y, s' (D.ntw.cc y) = D.ntw.cc (s y)) → ((ρ s' : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = ((ρ s⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly ∧ D.nd.chi i 1 s' = D.nd.chi i 1 s⁻¹ := by
  first | exact @GlobalTheory.ConjPoly.conj_inertia | exact GlobalTheory.ConjPoly.conj_inertia | (intros; apply GlobalTheory.ConjPoly.conj_inertia <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationCoefFieldFiniteRange
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.Proof.CoefField

theorem exists_coefField {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ K : IntermediateField ℚ_[l] (Qbar l), (∀ z, z ∈ K ↔ ∃ x, ι x = z) ∧ FiniteDimensional ℚ_[l] K ∧
      ∀ x : FractionRing O, ‖ι x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  classical
  let φ : O →+* Qbar l := ι.comp (algebraMap O (FractionRing O))
  have hφ : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := hι
  have hQ : ∀ q : ℚ_[l], algebraMap ℚ_[l] (Qbar l) q ∈ ι.fieldRange := by
    intro q
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) q
    rw [map_div₀]
    refine div_mem ?_ ?_
    · exact ⟨_, hι a⟩
    · exact ⟨_, hι b⟩
  let K : IntermediateField ℚ_[l] (Qbar l) := ι.fieldRange.toIntermediateField hQ
  have hK : ∀ z, z ∈ K ↔ ∃ x, ι x = z := fun z => Iff.rfl
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] O).FG)
  let S : Set (Qbar l) := φ '' (s : Set O)
  have hint : ∀ x ∈ S, IsIntegral ℚ_[l] x := by
    rintro _ ⟨y, -, rfl⟩
    obtain ⟨p, hp, hy⟩ : IsIntegral ℤ_[l] y := Algebra.IsIntegral.isIntegral y
    refine ⟨p.map (algebraMap ℤ_[l] ℚ_[l]), hp.map _, ?_⟩
    have := congrArg φ hy
    rw [map_zero, Polynomial.hom_eval₂] at this
    have e : (algebraMap ℚ_[l] (Qbar l)).comp (algebraMap ℤ_[l] ℚ_[l]) = φ.comp (algebraMap ℤ_[l] O) :=
      RingHom.ext fun z => (hφ z).symm
    rw [Polynomial.eval₂_map, e]
    exact this
  have : Finite S := (s.finite_toSet.image φ).to_subtype
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hle : K ≤ IntermediateField.adjoin ℚ_[l] S := by
    have hO : ∀ y : O, φ y ∈ IntermediateField.adjoin ℚ_[l] S := by
      intro y
      have hy : y ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [Algebra.smul_def, map_mul, hφ]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    rw [map_div₀]
    exact div_mem (hO a) (hO b)
  refine ⟨K, hK, ?_, fun x => (GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.mem_range_iff ι hι x).symm⟩
  have hge : IntermediateField.adjoin ℚ_[l] S ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨_, rfl⟩
  have heq : K = IntermediateField.adjoin ℚ_[l] S := le_antisymm hle hge
  rw [heq]
  exact hfd

theorem coefField_range : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc), ∃ K : IntermediateField ℚ_[N.l i] (Qbar (N.l i)), (∀ z, z ∈ K ↔ ∃ x, A.iotaQ i x = z) ∧ FiniteDimensional ℚ_[N.l i] K ∧ ∀ x : FractionRing (N.O i), ‖A.iotaQ i x‖ ≤ 1 ↔ x ∈ (algebraMap (N.O i) (FractionRing (N.O i))).range := by
  intro R H what₂ N A i
  exact exists_coefField (A.iotaQ i) (A.iotaQ_alg i)

end GlobalTheory.Proof.CoefField

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionCuspidalGreenDegreeEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionCuspidalGreenDegreeEqOne
noncomputable section

namespace GlobalTheory.GLq

open Polynomial Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

variable {g : ℕ} [Fact g.Prime]

theorem res_zero_left {d : ℕ} (χ : Gn g d → ℂ) (h : Gn g 0) (y : Gn g d) :
    res 0 d χ h y = χ y := by
  unfold res
  have key : ∀ x : Gn g d, (InPar 0 (x : Mt g d) ∧ tl 0 (x : Mt g d) = (h : Mt g 0) ∧
      br 0 d (x : Mt g d) = (y : Mt g d)) ↔ x = y := by
    intro x
    constructor
    · rintro ⟨-, -, hb⟩
      apply Units.ext
      funext i j
      have := congrFun (congrFun hb i) j
      simpa [br, entN, i.isLt, j.isLt] using this
    · rintro rfl
      refine ⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩
      funext i j
      simp [br, entN, i.isLt, j.isLt]
  simp only [key, Nat.zero_mul, pow_zero, inv_one, one_mul]
  rw [Finset.sum_ite_eq' Finset.univ y]
  simp

theorem der_zero_one (ψ : AddChar (ZMod g) ℂ) {d : ℕ} (χ : Gn g d → ℂ) :
    der ψ 0 χ 1 = wh ψ χ := by
  unfold der
  have : res 0 (d - 0) χ 1 = χ := funext fun y => res_zero_left χ 1 y
  rw [this]

theorem der_cusp_eq_zero (ψ : AddChar (ZMod g) ℂ) {d m : ℕ} {χ : Gn g d → ℂ} (hχ : IsCusp χ)
    (h0 : 0 < m) (hm : m < d) (h : Gn g m) : der ψ m χ h = 0 := by
  unfold der wh tr
  have : res m (d - m) χ h = fun _ => 0 := funext fun y => res_cusp_eq_zero g d m χ hχ h0 hm h y
  rw [this]
  simp

theorem green_deg_ne_zero (d : ℕ) : ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 : i ≠ 0 := by simp at hi; omega
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hlt : 1 < g ^ i := Nat.one_lt_pow hi1 hg
  intro h
  have h' : ((g ^ i : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact sub_eq_zero.mp h
  have := Nat.cast_injective h'
  omega

theorem wh_cusp_eq_one : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ)
    (χ : Gn g d → ℂ), IsCusp χ → χ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) → wh ψ χ = 1 := by
  intro g _ ψ hψ d χ hχ hdeg
  have hd : 0 < d := hχ.1
  have hform := GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (isClass_of_isIrr hχ.2.1)
  rw [Finset.sum_eq_single 0] at hform
  · rw [der_zero_one, zero_add, hdeg] at hform
    have hne := green_deg_ne_zero (g := g) d
    have : (wh ψ χ - 1) * ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) = 0 := by
      rw [sub_mul, ← hform]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
  · intro m hm hm0
    rw [der_cusp_eq_zero ψ hχ (Nat.pos_of_ne_zero hm0) (Finset.mem_range.mp hm), zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr hd) h

end GlobalTheory.GLq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionCuspidalGreenDegreeEqOneStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → χ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) → wh ψ χ = 1 := by
  first | exact @GlobalTheory.GLq.wh_cusp_eq_one | exact GlobalTheory.GLq.wh_cusp_eq_one | (intros; apply GlobalTheory.GLq.wh_cusp_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.FrobRational

theorem core {S A D D' : Type} [CommRing S] [IsDomain S] [CommRing A] [IsDomain A] [CommRing D] [CommRing D']
    (ev : S →+* A) (t : S →+* D) (i : A →+* D') (j : D →+* D') (hi : Function.Injective i)
    (hj : ∀ a, j (t a) = i (ev a)) (φ : A →+* A) (Φ : D' →+* D') (Ψ : D →+* D)
    (hΦ : ∀ a, Φ (i a) = i (φ a)) (hΨ : ∀ x, Φ (j x) = j (Ψ x))
    (disj : ∀ (x y : A) (f g : D), g ≠ 0 → y ≠ 0 → i x * j g = i y * j f →
      ∃ δ a : S, δ ≠ 0 ∧ ev δ * x = ev a * y)
    {d : ℕ} (lam : S) (hlam : lam ≠ 0) (W : Matrix (Fin d) (Fin d) D') (B : Matrix (Fin d) (Fin d) S)
    (hW : i (ev lam) • W.map Φ = W * B.map (i.comp ev))
    (Y : Matrix (Fin d) (Fin d) A) (Z : Matrix (Fin d) (Fin d) D) (hY : Y.det ≠ 0)
    (hYZ : W * Z.map j = Y.map i) :
    ∃ (δ : S) (A1 : Matrix (Fin d) (Fin d) S), δ ≠ 0 ∧ ev δ • Y.map φ = Y * A1.map ev := by
  classical
  set x : Matrix (Fin d) (Fin d) D := B.map t * Z.map Ψ with hx
  set P : Matrix (Fin d) (Fin d) A := ev lam • Y.map φ with hP
  have hPx : P.map i = W * x.map j := by
    have h1 : (Y.map φ).map i = (Y.map i).map Φ := by ext a b; simp [hΦ]
    have h2 : (Z.map j).map Φ = (Z.map Ψ).map j := by ext a b; simp [hΨ]
    have h3 : (B.map t).map j = B.map (i.comp ev) := by ext a b; simp [hj]
    have h4 : P.map i = i (ev lam) • (Y.map φ).map i := by ext a b; simp [hP]
    rw [h4, h1, ← hYZ, Matrix.map_mul, ← Matrix.smul_mul, hW, h2, hx, Matrix.map_mul, h3, Matrix.mul_assoc]
  have hdet : W.det * j Z.det = i Y.det := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hYZ, Matrix.det_mul]
  have hZ : Z.det ≠ 0 := fun h => hY (hi (by rw [← hdet, h, map_zero, mul_zero, map_zero]))
  have hadjY : (Y.adjugate).map i = (Y.map i).adjugate := RingHom.map_adjugate i Y
  have hadjZ : (Z.adjugate).map j = (Z.map j).adjugate := RingHom.map_adjugate j Z
  have key : (Y.adjugate * P).map i = W.det • (Z.adjugate * x).map j := by
    rw [Matrix.map_mul, Matrix.map_mul, hadjY, hadjZ, hPx, ← hYZ, Matrix.adjugate_mul_distrib, Matrix.mul_assoc,
      ← Matrix.mul_assoc W.adjugate, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have hent : ∀ p : Fin d × Fin d, ∃ δ a : S, δ ≠ 0 ∧ ev δ * (Y.adjugate * P) p.1 p.2 = ev a * Y.det := by
    intro p
    refine disj _ _ ((Z.adjugate * x) p.1 p.2) Z.det hZ hY ?_
    have h := congrFun (congrFun key p.1) p.2
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h
    rw [h, ← hdet]; ring
  choose δ a hδ ha using hent
  refine ⟨(∏ p, δ p) * lam, Matrix.of fun r c => (∏ p ∈ Finset.univ.erase (r, c), δ p) * a (r, c),
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun p _ => hδ p) hlam, ?_⟩
  have h5 : ev (∏ p, δ p) • (Y.adjugate * P) =
      Y.det • (Matrix.of fun r c => (∏ p ∈ Finset.univ.erase (r, c), δ p) * a (r, c)).map ev := by
    ext r c
    rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, smul_eq_mul,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ (r, c)), map_mul, map_mul, mul_assoc, ha (r, c)]
    ring
  have h6 := congrArg (fun M => Y * M) h5
  simp only [Matrix.mul_smul] at h6
  rw [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul, smul_comm] at h6
  ext r c
  have h7 := congrFun (congrFun h6 r) c
  rw [Matrix.smul_apply, Matrix.smul_apply Y.det, smul_eq_mul, smul_eq_mul] at h7
  rw [← mul_left_cancel₀ hY h7, hP, smul_smul, map_mul]

theorem isDiscMap_comp {l : ℕ} {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] {u : A} {u' : A'}
    {u'' : A''} {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {g : A' →+* A''} {F : Disc l u ρ →+* Disc l u' ρ'}
    {G : Disc l u' ρ' →+* Disc l u'' ρ''} (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) (hG : IsDiscMap (l := _) (u := _) (ρ := _) g G) :
    IsDiscMap (l := _) (u := _) (ρ := _) (g.comp f) (G.comp F) :=
  ⟨fun a => by rw [RingHom.comp_apply, hF.ext, hG.ext, RingHom.comp_apply],
    fun x => (hG.norm_le _).trans (hF.norm_le x)⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  intro l hl K bk τ hτ d ρ hρ s Y1 Z1 hY hYZ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  have hi : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB bk.ρ₀ h0 h1).1
  haveI : IsDomain (Ainf l) := hi.isDomain _
  obtain ⟨j, hj⟩ := exists_discMap_of_pow_dvd l _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0
    (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Ψ, hΨ⟩ := exists_discMap_of_pow_dvd l _ _ (frobS l bk.a) (X : bk.S) (X : bk.S) bk.ρ₀ bk.ρ₀ l h0
    (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := exists_discMap_of_pow_dvd l _ _ (WittVector.frobenius : Ainf l →+* Ainf l) (bk.ev X) (bk.ev X)
    bk.ρ₀ bk.ρ₀ l h0 (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  have hcomm : Φ.comp j = j.comp Ψ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev = bk.ev.comp (frobS l bk.a) :=
      RingHom.ext fun x => (bk.ev_frob x).symm
    exact (isDiscMap_comp hj hΦ).unique (e ▸ isDiscMap_comp hΨ hj)
  have hlam : bk.iA (bk.ev ((l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N)) =
      (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N := by
    simp only [map_mul, map_pow, map_natCast, RingHom.comp_apply]
  have hu : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (isUnit_toDisc_frobS_E l K bk).map j
    rwa [hj.ext] at h
  have hne : (l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N ≠ 0 := fun h => by
    rw [h, map_zero, map_zero] at hlam
    exact (((isUnit_l_disc l _ _).pow _).mul (hu.pow _)).ne_zero hlam.symm
  exact core bk.ev (toDisc l (X : bk.S) bk.ρ₀) bk.iA j hi hj.ext WittVector.frobenius Φ Ψ hΦ.ext
    (fun x => RingHom.congr_fun hcomm x) (GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries l K bk _ bk.ev ι TB j hj) _ hne s.W _
    (by rw [hlam]; exact GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) Y1 Z1 hY (hYZ j hj)

end GlobalTheory.BSP.FrobRational
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumnsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_frobenius_rational_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  first | exact @GlobalTheory.BSP.FrobRational.main | exact GlobalTheory.BSP.FrobRational.main | (intros; apply GlobalTheory.BSP.FrobRational.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QValPullbackMulRamificationCompleteDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QValPullbackMulRamificationCompleteDvr
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
open ReciprocityTheory.ChartRestriction.G.DVR (HasVal GenHasVal wchart_le_preimage)

noncomputable section

namespace GlobalTheory.QValPull

theorem chart_eq_of_val {V : Type} [CommRing V] [IsDomain V] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {φ : PUnit → (Spec (CommRingCat.of V) ⟶ X)} {φ' : PUnit → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    (hφ : ∀ k, φ' k = jK V ≫ φ k) {ε : PUnit → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)}
    {e : LB.Gen (LB.LinComb L φ ε)} {c : FractionRing V}
    (h : ∀ (z : Spec (CommRingCat.of (FractionRing V))) (J : (Spec (CommRingCat.of (FractionRing V)) ⟶ X) → L.ι),
      Good L z J → (val t (𝟙 _) z J).val =
        gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) * (val e (𝟙 _ ≫ jK V) z J).val)
    (j : PUnit → L.ι) :
    (t.s j).val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j))).val := by
  apply fn_ext
  intro x hx
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL x φ' j (fun a b _ => by cases a; cases b; rfl)
    (fun k => LB.wchart_le L φ' j k hx)
  have h1 : ∀ k, J (𝟙 _ ≫ φ' k) = j k := fun k => by rw [Category.id_comp]; exact hJj k
  have h2 : ∀ k, J ((𝟙 _ ≫ jK V) ≫ φ k) = j k := fun k => by rw [Category.id_comp, ← hφ]; exact hJj k
  have eL : gs (𝟙 _) x _ (t.s j).val = (val t (𝟙 _) x J).val :=
    (gs_unit _ x _ hx _).trans (congrArg Units.val (val_of t (𝟙 _) x J j h1).symm)
  rw [eL, h x J hJ]
  refine Eq.trans ?_ (gs_mul _ x _ hx _ _).symm
  congr 1
  · exact (gs_res _ x _ hx _).symm
  · have hx' : x ∈ LB.wchart L φ' j := hx
    have hxe : x ∈ jK V ⁻¹ᵁ LB.wchart L φ j := wchart_le_preimage L (jK V) φ φ' hφ j hx'
    unfold res pullU
    simp only [Units.coe_map, MonoidHom.coe_coe]
    refine Eq.symm ((gs_res _ x _ hx _).trans ((gs_pull (𝟙 _) (jK V) x _ hxe _).trans
      ((gs_unit (𝟙 _ ≫ jK V) x _ hxe _).trans ?_)))
    exact congrArg Units.val (val_of e _ x J j h2).symm

theorem hasVal_fracMap {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] {g : V →+* V'}
    (hg : Function.Injective g) {ϖ : V} {ϖ' : V'} {e : ℕ} (ha : Associated (g ϖ) (ϖ' ^ e))
    {c : FractionRing V} {n : ℤ} (hc : HasVal ϖ c n) : HasVal ϖ' (ArcPull.fracMap hg c) (e * n) := by
  obtain ⟨u, rfl⟩ := hc
  obtain ⟨v, hv⟩ := ha
  refine ⟨v⁻¹ ^ n * Units.map (g : V →* V') u, ?_⟩
  have hϖ : g ϖ = ϖ' ^ e * ((v⁻¹ : V'ˣ) : V') := by
    rw [← hv, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have key : ∀ (w : V'ˣ) (m : ℤ), algebraMap V' (FractionRing V') ((w ^ m : V'ˣ) : V') =
      algebraMap V' (FractionRing V') (w : V') ^ m := by
    intro w m
    have h1 := Units.coe_map (algebraMap V' (FractionRing V') : V' →* FractionRing V') (w ^ m)
    rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map] at h1
    simpa only [MonoidHom.coe_coe] using h1.symm
  rw [map_mul, map_zpow₀, ArcPull.fracMap_algebraMap, ArcPull.fracMap_algebraMap, hϖ, Units.val_mul, map_mul,
    map_mul, map_pow, key, mul_zpow, ← zpow_natCast, ← zpow_mul]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  ring

theorem gs_scal_spMap {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (z : Spec (CommRingCat.of K')) (c : K) :
    gs (spMap f) z ⊤ (scal (𝟙 (Spec (CommRingCat.of K))) c) =
      gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of K'))) (f c)) := by
  unfold gs scal spMap
  simp only [TopologicalSpace.Opens.mem_top, ↓reduceDIte]
  have hn := congrArg (fun φ => CommRingCat.Hom.hom φ c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  rw [hn]
  rfl

theorem qVal_pull {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    {g : V →+* V'} {D : DegPre V} {D' : DegPre V'} (hD : IsPullDeg g D D') {ϖ : V} {ϖ' : V'} {e : ℕ}
    (hg : Function.Injective g) (ha : Associated (g ϖ) (ϖ' ^ e)) (y : D'.X) (n : ℤ) (h : QVal D ϖ (hD.xe y) n) :
    QVal D' ϖ' y (e * n) := by
  obtain ⟨e0, he0, c0, hc0, hch⟩ := h
  obtain ⟨e', he', hdown⟩ := ArcPull.exists_down_om hD.w_gen D.P.isLB D'.P.isLB (spMap g)
    (fun _ : PUnit => hD.c_pr y) e0 he0
  refine ⟨e', he', ArcPull.fracMap hg c0, hasVal_fracMap hg ha hc0, ?_⟩
  refine chart_eq_of_val D'.P.isLB (fun _ => DVR.QForm.ptK_eq D' y) ?_
  intro z J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good D.P.L D.P.isLB z (fun k : Empty => k.elim) (fun k : Empty => k.elim)
    (fun a => a.elim) (fun k => k.elim)
  have hv := DVR.SectionScalarValuation.val_genHasVal (hφ := fun _ => DVR.QForm.ptK_eq D (hD.xe y)) hch (ArcPull.genMap hg) z hJ
  have hp := ArcPull.psi_val hD (ArcPull.genMap hg) (𝟙 (Spec (CommRingCat.of (FractionRing V')))) (ArcPull.fracMap_sq hg) hJ hJ' y
  have hd := hdown _ (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') z J J' hJ hJ'
  have hr : ArcPull.genMap hg ≫ jK V = (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') ≫ spMap g := by
    rw [← ArcPull.fracMap_sq hg, Category.assoc]
    rfl
  have hxk : (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ D'.xK y) = (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') ≫ (D'.c y).left := by
    rw [Category.assoc]
    exact congrArg _ (DVR.QForm.ptK_eq D' y)
  rw [hp, hr, hd] at hv
  simp only [Fintype.prod_unique, zpow_neg, zpow_one] at hv
  rw [← hxk, show ArcPull.genMap hg = spMap (ArcPull.fracMap hg) from rfl, gs_scal_spMap] at hv
  generalize ArcPull.om hD.w z J J' (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ D'.xK y) = o at hv
  generalize val (D'.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing V')))) z J' = A at hv ⊢
  generalize val e' (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') z J' = E at hv ⊢
  generalize gs (𝟙 (Spec (CommRingCat.of (FractionRing V')))) z ⊤ (scal (𝟙 _) (ArcPull.fracMap hg c0)) = G at hv ⊢
  rw [Units.val_mul, Units.val_mul] at hv
  linear_combination o.val * hv + (G * E.val - A.val) * Units.mul_inv o

theorem main : ∀ (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (D : DegPre T.V) (D' : DegPre T'.V) (hD : IsPullDeg g D D')
    (ϖ : T.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g → Irreducible ϖ → Irreducible ϖ' →
    Associated (g ϖ) (ϖ' ^ e) → ∀ (y : D'.X) (n : ℤ), QVal D ϖ (hD.xe y) n → QVal D' ϖ' y (e * n) := by
  intro T T' g D D' hD ϖ ϖ' e hg _ _ ha y n h
  exact qVal_pull hD hg ha y n h

end GlobalTheory.QValPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QValPullbackMulRamificationCompleteDvrStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qVal_pullback_mul_ramification_complete_dvr : ∀ (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (D : DegPre T.V) (D' : DegPre T'.V) (hD : IsPullDeg g D D') (ϖ : T.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g → Irreducible ϖ → Irreducible ϖ' → Associated (g ϖ) (ϖ' ^ e) → ∀ (y : D'.X) (n : ℤ), QVal D ϖ (hD.xe y) n → QVal D' ϖ' y (e * n) := by
  first | exact @GlobalTheory.QValPull.main | exact GlobalTheory.QValPull.main | (intros; apply GlobalTheory.QValPull.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisMap

variable (l : ℕ) [Fact l.Prime]

theorem unit_l (n : ℕ) : IsUnit ((l : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) := by
  have h : IsUnit (algebraMap (Per.Ainf l) (Per.AinfP l) (l : Per.Ainf l)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have h2 := h.map (Ideal.Quotient.mk (Per.kerP l ^ n))
  rwa [map_natCast, map_natCast] at h2

end GlobalTheory.MemLoc.CrisMap
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

variable {l : ℕ} [Fact l.Prime]

theorem FilD_anti {a b : ℤ} (h : a ≤ b) : Per.FilD l b ≤ Per.FilD l a := by
  obtain ⟨k, rfl⟩ := Int.le.dest h
  clear h
  induction k with
  | zero => simp
  | succ k ih =>
    refine le_trans ?_ ih
    have := (GlobalTheory.MemLoc.filD_laws l).1 (a + k)
    simpa [add_assoc] using this

theorem alg_mem_FilD_iff (n : ℕ) (y : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n :=
  (GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.2 n y

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem tmul_mem_filO {C : GlobalTheory.MemLoc.Core l} {n : ℤ} {β : Per.Bcris l} (h : C.ι β ∈ Per.FilD l n) :
    (1 : O) ⊗ₜ[ℤ_[l]] β ∈ filO O C n :=
  Submodule.subset_span ⟨β, h, rfl⟩

theorem filO_anti {C : GlobalTheory.MemLoc.Core l} {a b : ℤ} (h : a ≤ b) : filO O C b ≤ filO O C a :=
  Submodule.span_mono fun _ ⟨β, hβ, hx⟩ => ⟨β, FilD_anti h hβ, hx⟩

theorem mul_mem_filO {C : GlobalTheory.MemLoc.Core l} {a b : ℤ} {x y : OB l O} (hx : x ∈ filO O C a)
    (hy : y ∈ filO O C b) : x * y ∈ filO O C (a + b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨β', hβ', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      refine tmul_mem_filO ?_
      rw [map_mul]
      exact (GlobalTheory.MemLoc.filD_laws l).2.2.1 a b _ _ hβ hβ'
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | smul o y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ o h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | smul o x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ o h

theorem toOB_tmul_mem_filO {C : GlobalTheory.MemLoc.Core l} {n : ℕ} {c : Per.Acris l} (h : C.j c ∈ Per.FilP l n) :
    toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] c) ∈ filO O C n := by
  refine tmul_mem_filO ?_
  change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) c) ∈ _
  rw [C.ι_j]
  exact (alg_mem_FilD_iff n _).2 h

theorem toOB_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) (x : OCr l O) : toOB l O x ∈ filO O C 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul o c =>
    have : (o ⊗ₜ[ℤ_[l]] c : OCr l O) = o • ((1 : O) ⊗ₜ[ℤ_[l]] c) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ o (toOB_tmul_mem_filO (n := 0) (GlobalTheory.BdRQuot.mem_filtration_zero _))
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem isUnit_l_BdRp : IsUnit (l : Per.BdRp l) := by
  refine (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ ?_
  rw [map_natCast]
  exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem mem_filO_of_pow_mul {C : GlobalTheory.MemLoc.Core l} {n : ℤ} {s : ℕ} {x : OB l O}
    (h : (l : OB l O) ^ s * x ∈ filO O C n) : x ∈ filO O C n := by
  obtain ⟨u, hu⟩ := (GlobalTheory.MemLoc.isUnit_l_Bcris l).exists_right_inv
  have hι : C.ι u ∈ Per.FilD l 0 := by
    obtain ⟨v, hv⟩ := (isUnit_l_BdRp (l := l)).exists_right_inv
    have h1 : C.ι u = algebraMap (Per.BdRp l) (Per.BdR l) v := by
      have h2 : C.ι (l : Per.Bcris l) * C.ι u = 1 := by rw [← map_mul, hu, map_one]
      have h3 : (algebraMap (Per.BdRp l) (Per.BdR l) (l : Per.BdRp l)) * algebraMap _ _ v = 1 := by
        rw [← map_mul, hv, map_one]
      rw [map_natCast] at h2
      rw [map_natCast] at h3
      calc C.ι u = (algebraMap (Per.BdRp l) (Per.BdR l) v * (l : Per.BdR l)) * C.ι u := by
            rw [mul_comm (algebraMap _ _ v), h3, one_mul]
        _ = _ := by rw [mul_assoc, h2, mul_one]
    rw [h1]
    exact (mem_FilD_zero_iff _).2 ⟨v, rfl⟩
  have hU : ((1 : O) ⊗ₜ[ℤ_[l]] u) ^ s ∈ filO O C 0 := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
    refine tmul_mem_filO ?_
    rw [map_pow]
    have hk : ∀ k : ℕ, C.ι u ^ k ∈ Per.FilD l 0 := fun k => by
      induction k with
      | zero => rw [pow_zero]; exact (GlobalTheory.MemLoc.filD_laws l).2.1
      | succ k ih => rw [pow_succ]; simpa using (GlobalTheory.MemLoc.filD_laws l).2.2.1 0 0 _ _ ih hι
    exact hk s
  have h1 : ((1 : O) ⊗ₜ[ℤ_[l]] u) ^ s * ((l : OB l O) ^ s * x) = x := by
    have h2 : ((1 : O) ⊗ₜ[ℤ_[l]] u) * (l : OB l O) = 1 := by
      rw [show (l : OB l O) = (1 : O) ⊗ₜ[ℤ_[l]] (l : Per.Bcris l) from
        (map_natCast (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O) l).symm,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, hu]
      rfl
    rw [← mul_assoc, ← mul_pow, h2, one_pow, one_mul]
  rw [← h1]
  simpa using mul_mem_filO hU h

theorem j_mem_FilP_of_approx (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : Per.Acris l)
    (h : ∀ r : ℕ, ∃ y z : Per.Acris l, x = y + (l : Per.Acris l) ^ r * z ∧ C.j y ∈ Per.FilP l m) :
    C.j x ∈ Per.FilP l m := by
  obtain ⟨N, hN⟩ := C.j_cris.bdd m
  obtain ⟨a, ha⟩ := hN x
  have hq : Ideal.Quotient.mk (Per.kerP l ^ m) (algebraMap (Per.Ainf l) (Per.AinfP l) a) = 0 := by
    refine GlobalTheory.MemLoc.CrisUnique.sep m _ fun r => ?_
    obtain ⟨y, z, hxyz, hy⟩ := h r
    obtain ⟨b, hb⟩ := hN z
    refine ⟨b, ?_⟩
    have hy' : Per.ev l m (C.j y) = 0 := (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).1 hy
    rw [← ha, ← hb, hxyz]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, hy']
    ring
  have h1 : Per.ev l m (C.j x) = 0 := by
    rw [← ha, map_mul, map_pow, map_natCast] at hq
    exact ((GlobalTheory.MemLoc.CrisMap.unit_l l m).pow N).mul_right_eq_zero.1 hq
  exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).2 h1

end GlobalTheory.BKGal.TaylorFil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedAtOfIsUnramifiedInGaloisExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedAtOfIsUnramifiedInGaloisExtension
noncomputable section

namespace GlobalTheory.NT

open NumberField IsDedekindDomain

theorem isUnramifiedAt_of_unramIn {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (h : UnramIn L 𝔭) (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver 𝔭.asIdeal] : Algebra.IsUnramifiedAt (𝓞 K) P := by
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have := 𝔭.isMaximal
  have hu : P.under (𝓞 K) = 𝔭.asIdeal := (Ideal.over_def P 𝔭.asIdeal).symm
  have : (P.under (𝓞 K)).IsMaximal := by rw [hu]; infer_instance
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P)
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => h τ ⟨P, inferInstance, inferInstance, hτ⟩
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P
  rw [h1, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[K] L)] at h2
  exact Ideal.ramificationIdx_eq_one_iff.1 h2.symm

end GlobalTheory.NT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedAtOfIsUnramifiedInGaloisExtensionStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedAt_of_isUnramifiedInGaloisExtension : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)}, GlobalTheory.NT.UnramIn L 𝔭 → ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver 𝔭.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) P := by
  first | exact @GlobalTheory.NT.isUnramifiedAt_of_unramIn | exact GlobalTheory.NT.isUnramifiedAt_of_unramIn | (intros; apply GlobalTheory.NT.isUnramifiedAt_of_unramIn <;> assumption)
end
end
