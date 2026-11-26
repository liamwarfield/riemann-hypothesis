module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExtEmbeddingSplittingStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.FlatDisc
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem exists_eq_add (bk : BK K) : ∃ Q : Polynomial (Wq l bk.a),
    bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * Q := by
  have hd : ∀ i ∈ Finset.range bk.Ep.natDegree, ∃ c, bk.Ep.coeff i = (l : Wq l bk.a) * c :=
    fun i hi => bk.dvd_coeff i (Finset.mem_range.1 hi)
  choose d hd using hd
  refine ⟨∑ i ∈ (Finset.range bk.Ep.natDegree).attach, Polynomial.C (d i.1 i.2) * Polynomial.X ^ i.1, ?_⟩
  refine bk.monic.as_sum.trans (congrArg (Polynomial.X ^ bk.Ep.natDegree + ·) ?_)
  rw [Finset.mul_sum, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i.1 i.2, Polynomial.C_mul, mul_assoc]

theorem exists_E_eq (bk : BK K) : ∃ Q : Polynomial (Wq l bk.a),
    bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * (Q : bk.S) := by
  obtain ⟨Q, hQ⟩ := exists_eq_add bk
  refine ⟨Q, ?_⟩
  change ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
  conv_lhs => rw [hQ]
  rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C, map_natCast]

theorem ev_coe (bk : BK K) (p : Polynomial (Wq l bk.a)) :
    bk.ev (p : bk.S) = p.eval₂ (bk.ev.comp (C (R := Wq l bk.a))) (bk.ev X) := by
  have h : bk.ev.comp (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) =
      Polynomial.eval₂RingHom (bk.ev.comp (C (R := Wq l bk.a))) (bk.ev X) := by
    refine Polynomial.ringHom_ext (fun w => ?_) ?_
    · simp [Polynomial.coeToPowerSeries.ringHom_apply]
    · simp [Polynomial.coeToPowerSeries.ringHom_apply]
  exact RingHom.congr_fun h p

theorem theta_ev_E (bk : BK K) : Per.θ l (bk.ev bk.E) = 0 := by
  have h : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := by
    rw [← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  exact h

theorem natCast_l_ne_zero : ((l : ℕ) : Per.OC l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem flat_ne_zero (bk : BK K) : bk.flat ≠ 0 := by
  intro h0
  have hX : bk.ev X = 0 := by rw [bk.ev_X, h0, WittVector.teichmuller_zero]
  have h := theta_ev_E bk
  rw [BK.E, ev_coe, hX, Polynomial.eval₂_at_zero, RingHom.comp_apply, bk.ev_C] at h
  obtain ⟨w, hw⟩ := bk.coeff_zero
  rw [hw, map_mul, map_natCast, map_mul, map_natCast] at h
  have hu : IsUnit (Per.θ l (wA l bk.a (w : Wq l bk.a))) := (w.isUnit.map (wA l bk.a)).map (Per.θ l)
  exact natCast_l_ne_zero ((mul_eq_zero.1 h).resolve_right hu.ne_zero)

theorem not_isUnit_flat (bk : BK K) : ¬ IsUnit bk.flat := by
  intro hu
  obtain ⟨Q, hQ⟩ := exists_E_eq bk
  have h := theta_ev_E bk
  rw [hQ, map_add (f := _), map_mul, map_pow, map_natCast, bk.ev_X, map_add (f := _), map_mul, map_pow, map_natCast] at h
  have h1 : IsUnit (Per.θ l (WittVector.teichmuller l bk.flat) ^ bk.Ep.natDegree) :=
    ((hu.map (WittVector.teichmuller l)).map (Per.θ l)).pow _
  rw [eq_neg_of_add_eq_zero_left h, IsUnit.neg_iff] at h1
  exact OC_l_not_unit l (isUnit_of_mul_isUnit_left h1)

theorem rho_spec (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
    rw [neg_lt_zero]; positivity), ?_⟩
  rw [BK.ρ₀, ← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he.ne', NNReal.rpow_neg_one]

theorem J_eq (bk : BK K) :
    Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J := by
  obtain ⟨Q, hQ⟩ := exists_E_eq bk
  have hl : (l : bk.S) * (Q : bk.S) ∈ Ideal.span {(l : bk.S)} := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rw [Ideal.span_singleton_le_iff_mem]
    have : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * (Q : bk.S) := by rw [hQ]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hl)
  · rw [Ideal.span_singleton_le_iff_mem, hQ]
    exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hl)

end GlobalTheory.BSP.FlatDisc

theorem GlobalTheory.BSP.flat_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧
    (0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹) ∧
    Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J :=
  fun _ _ _ bk => ⟨FlatDisc.flat_ne_zero bk, FlatDisc.not_isUnit_flat bk, FlatDisc.rho_spec bk, FlatDisc.J_eq bk⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFactsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_flat_radius_ideal_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧ (0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹) ∧ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J := by
  first | exact @GlobalTheory.BSP.flat_disc | exact GlobalTheory.BSP.flat_disc | (intros; apply GlobalTheory.BSP.flat_disc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

section Red

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

def evRed : bk.S →+* OCb l := (WittVector.constantCoeff (p := l) (R := OCb l)).comp bk.ev

theorem evRed_X : bk.evRed X = bk.flat := by
  simp [evRed, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem flat_ne_zero : bk.flat ≠ 0 := by
  intro h0
  have hX : bk.ev X = 0 := by rw [bk.ev_X, h0]; exact WittVector.teichmuller_zero l
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hE : bk.ev bk.E = (l : Ainf l) * wA l bk.a (w : Wq l bk.a) := by
    conv_lhs => rw [eq_X_mul_shift_add_const bk.E]
    rw [map_add (f := _), map_mul, hX, zero_mul, zero_add, bk.ev_C, Polynomial.constantCoeff_coe, hw, map_mul,
      map_natCast]
  have hl' : (l : Ainf l) ∈ RingHom.ker (Per.θ l) := by
    rw [← bk.span_ev, hE, Ideal.span_singleton_mul_right_unit ((w.isUnit).map (wA l bk.a))]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_natCast] at hl'
  exact Nat.cast_ne_zero.2 hl.out.ne_zero hl'

theorem dvd_of_evRed_eq_zero (x : bk.S) (hx : bk.evRed x = 0) : (l : bk.S) ∣ x := by
  set r := WittVector.constantCoeff (p := l) (R := Fq l bk.a) with hr
  by_cases h : PowerSeries.map r x = 0
  · exact dvd_of_map_eq_zero l bk.a x h
  exfalso
  set xb := PowerSeries.map r x with hxb
  set m := xb.order.toNat
  set vb := divXPowOrder xb
  have hvb : constantCoeff vb ≠ 0 := fun h' => h (constantCoeff_divXPowOrder_eq_zero_iff.1 h')
  let v : bk.S := PowerSeries.mk fun n => WittVector.teichmuller l (coeff n vb)
  have hv : PowerSeries.map r v = vb := by
    ext n
    simp [v, hr, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  have hvu : IsUnit v := by
    rw [isUnit_iff_constantCoeff]
    have : constantCoeff v = WittVector.teichmuller l (constantCoeff vb) := by
      simp [v, ← coeff_zero_eq_constantCoeff]
    rw [this]
    exact (Ne.isUnit hvb).map _
  obtain ⟨y, hy⟩ := dvd_of_map_eq_zero l bk.a (x - X ^ m * v) (by
    rw [map_sub, map_mul, map_pow, PowerSeries.map_X, hv, X_pow_order_mul_divXPowOrder, sub_self])
  have h1 : bk.evRed x = bk.flat ^ m * bk.evRed v := by
    have : x = X ^ m * v + (l : bk.S) * y := by linear_combination hy
    rw [this, map_add (f := _), map_mul, map_mul, map_pow, evRed_X, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
  rw [hx] at h1
  exact mul_ne_zero (pow_ne_zero _ bk.flat_ne_zero) (hvu.map bk.evRed).ne_zero h1.symm

theorem dvd_of_dvd_ev (x : bk.S) (h : (l : Ainf l) ∣ bk.ev x) : (l : bk.S) ∣ x := by
  apply bk.dvd_of_evRed_eq_zero
  obtain ⟨z, hz⟩ := h
  simp only [evRed, RingHom.comp_apply, hz, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem eq_zero_of_forall_pow_dvd (w : Wq l bk.a) (h : ∀ n : ℕ, (l : Wq l bk.a) ^ n ∣ w) : w = 0 := by
  by_contra hw
  obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul w hw
  obtain ⟨c, hc⟩ := h (m + 1)
  have hbc : b = (l : Wq l bk.a) * c := by
    apply mul_left_cancel₀ (pow_ne_zero m (WittVector.p_nonzero l (Fq l bk.a)))
    rw [← hb, hc]; ring
  apply hb0
  have := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) hbc
  rwa [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, WittVector.constantCoeff_apply] at this

theorem ev_injective : Function.Injective bk.ev := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have key : ∀ n : ℕ, ∀ x : bk.S, bk.ev x = 0 → (l : bk.S) ^ n ∣ x := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      obtain ⟨x', rfl⟩ := bk.dvd_of_dvd_ev x (by rw [hx]; exact dvd_zero _)
      have h2 : bk.ev x' = 0 := ainf_torsionFree _ (by rw [← map_natCast bk.ev, ← map_mul]; exact hx)
      obtain ⟨z, hz⟩ := ih x' h2
      exact ⟨z, by rw [hz, pow_succ]; ring⟩
  refine PowerSeries.ext fun k => ?_
  rw [map_zero]
  refine bk.eq_zero_of_forall_pow_dvd _ fun n => ?_
  obtain ⟨z, hz⟩ := key n x hx
  refine ⟨coeff k z, ?_⟩
  rw [hz, ← map_natCast (C : Wq l bk.a →+* (Wq l bk.a)⟦X⟧), ← map_pow, coeff_C_mul]

end Red

theorem evW_isUnit_injective_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsUnit (bk.evW bk.E) ∧ Function.Injective bk.evW ∧
      ∀ x : bk.S, ((l : ℕ) : Ainf l) ∣ bk.ev x → ((l : ℕ) : bk.S) ∣ x :=
  fun _ _ _ bk => ⟨isUnit_inclW_of_span bk.span_ev, GlobalTheory.Prism.inclW_injective.comp bk.ev_injective,
    bk.dvd_of_dvd_ev⟩

end GlobalTheory.BSP.BK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvdStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsUnit (bk.evW bk.E) ∧ Function.Injective bk.evW ∧ ∀ x : bk.S, ((l : ℕ) : Ainf l) ∣ bk.ev x → ((l : ℕ) : bk.S) ∣ x := by
  first | exact @GlobalTheory.BSP.BK.evW_isUnit_injective_dvd | exact GlobalTheory.BSP.BK.evW_isUnit_injective_dvd | (intros; apply GlobalTheory.BSP.BK.evW_isUnit_injective_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamAll
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.FontaineAll

noncomputable def extRep {G : Type} [Group G] {LL : Type} [Field LL] (LL' : Type) [Field LL']
    [Algebra LL LL'] {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V) :
    Representation LL' G (LL' ⊗[LL] V) where
  toFun g := (ρ g).baseChange LL'
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one LL V
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem fontCore_of_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.fontCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A
  haveI : FiniteDimensional ℚ_[l] LL := hO.2.1
  obtain ⟨LL', ⟨f⟩, -, -⟩ := GlobalTheory.T.exists_finExt_embedding_splitting' l K LL
  letI : Algebra LL ↥LL'.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL ↥LL'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : FiniteDimensional LL ↥LL'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] LL ↥LL'.1
  obtain ⟨hV, -, ⟨hc, hcf⟩, ⟨hd, hdf⟩, -⟩ :=
    GlobalTheory.T.finrank_periodFunctor_coeff_baseChange (P.PD K) LL ↥LL'.1 A.V (↥LL'.1 ⊗[LL] A.V) A.ρ (extRep ↥LL'.1 A.ρ)
      (TensorProduct.mk LL ↥LL'.1 A.V 1) (TensorProduct.isBaseChange LL A.V ↥LL'.1)
      (fun g x => by simp [extRep])
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.fontaineLe_of_tied l P AI hT K LL'
  obtain ⟨h3, h4⟩ := GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI hT K LL' _ (extRep ↥LL'.1 A.ρ)
  refine ⟨⟨hcf.1 (h2 _ _), ?_⟩, ⟨hdf.1 h3, ?_⟩, fun hcr => ?_⟩
  · rw [← hc, ← hV]; exact h1 _ _
  · rw [← hd, ← hV]; exact h4
  · have h5 : IsCrys (P.PD K) (extRep ↥LL'.1 A.ρ) := by
      unfold IsCrys at hcr ⊢
      rw [hc, hV]; exact hcr
    have h6 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL' _ _ h5).1
    unfold IsDR at h6 ⊢
    rw [← hd, ← hV]; exact h6

theorem fontaine_bounds : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm7 D :=
  fun D l _ K => fontCore_of_tied l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.Per.FontaineAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescent
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CrysWD

theorem exists_descent {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {a : ℕ}
    (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l))
    (hr : Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) :
      Matrix (Fin a) (Fin a) (Om l))))
    (L : FinExt l)
    (hL : ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) :
      Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin a) ↥L.1,
      Continuous (fun g => ((ρ g : Matrix.GeneralLinearGroup (Fin a) ↥L.1) :
        Matrix (Fin a) (Fin a) ↥L.1)) ∧
      mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let M : G →* Matrix (Fin a) (Fin a) ↥L.1 :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hL g i j⟩
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp [Matrix.mul_apply] }
  refine ⟨M.toHomUnits, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Continuous.subtype_mk ((continuous_apply j).comp ((continuous_apply i).comp hr)) _
  · ext g i j
    rfl

theorem crysIffWD (D : D7) : CrysIffWD D.nd D.naut := by
  intro i a r w hw hr
  refine ⟨fun hc => ?_, fun h => (D.naut.wdOf_unrL i r w hw hr h.1).1 h.2⟩
  suffices hd : D.naut.IsdRW i r w from ⟨hd, (D.naut.wdOf_unrL i r w hw hr hd).2 hc⟩
  have := D.nd.lPrime i
  obtain ⟨L, hle, hL⟩ := GlobalTheory.T.compactGroup_rep_defined_over_finite_extension (D.nd.l i) _ a r hr (D.nbr i w hw).LL
  obtain ⟨ρ, hρ, rfl⟩ := exists_descent r hr L hL
  obtain ⟨h1, h2, -⟩ := (D.loc_tie i w hw).2.2 L hle a ρ hρ
  have := L.2
  have h3 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ L _ _ (h1.1 hc)).1
  refine h2.2 ?_
  unfold IsDR at h3
  unfold LocBridge.IsdRE
  simpa using h3

end GlobalTheory.CrysWD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc.FilSeed

variable {l : ℕ} [Fact l.Prime]

theorem mem_filtration_zero' (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  obtain ⟨-, hone, -, -, -, -, hlast⟩ := filD_laws l
  have h1 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := (hlast 0 1).1 (by rw [map_one, Nat.cast_zero]; exact hone)
  simpa using Ideal.mul_mem_left _ y h1

theorem exists_unit (C : Core l) (ξ : Ainf l) (hξ : Ideal.span {ξ} = RingHom.ker (Per.θ l)) :
    ∃ c : (Per.BdRp l)ˣ, aDp l ξ = (c : Per.BdRp l) * aDp l (xi C.ε) := by
  have hreg := (filtration_eq_xi_pow l C.ε (core_isEps l C)).2.1
  rw [C.ker_theta] at hξ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hξ ▸ Ideal.mem_span_singleton_self ξ :
    ξ ∈ Ideal.span {xi C.ε})
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hξ.symm ▸ Ideal.mem_span_singleton_self (xi C.ε) :
    xi C.ε ∈ Ideal.span {ξ})
  have h1 : aDp l a * aDp l b = 1 := by
    have : aDp l (xi C.ε) * (aDp l a * aDp l b - 1) = 0 := by
      have e : aDp l (xi C.ε) = aDp l b * (aDp l a * aDp l (xi C.ε)) := by
        rw [← map_mul, ← map_mul, ha, hb]
      linear_combination -e
    exact sub_eq_zero.1 (hreg _ this)
  refine ⟨⟨aDp l a, aDp l b, h1, by rw [mul_comm, h1]⟩, ?_⟩
  rw [← ha, map_mul]

end GlobalTheory.MemLoc.FilSeed


open GlobalTheory.MemLoc.FilSeed in
theorem GlobalTheory.MemLoc.seed_fil : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → (∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n}) ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a) ∧ (∀ (n : ℕ) (z : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l n ↔ z ∈ Per.FilP l n) ∧ (∀ x : Per.BdR l, ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ))) ∧ (∀ (a : ℤ) (n : ℕ) (x : Per.BdR l), algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ n * x ∈ Per.FilD l (a + n) ↔ x ∈ Per.FilD l a) ∧ Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
  intro l _ C ξ hξ
  obtain ⟨hstep, hone, hmul, hex, -, -, hlast⟩ := filD_laws l
  obtain ⟨hP, hreg, -, -⟩ := filtration_eq_xi_pow l C.ε (core_isEps l C)
  obtain ⟨c, hc⟩ := exists_unit C ξ hξ
  have h1 : ∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n} := by
    intro n
    ext y
    rw [hP, Ideal.mem_span_singleton, hc, mul_pow, ← Units.val_pow_eq_pow_val,
      Units.mul_left_dvd]
  have hanti : ∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a := by
    intro a b hab
    induction b, hab using Int.leInduction with
    | base => exact le_rfl
    | succ b _ ih => exact (hstep b).trans ih
  refine ⟨h1, hmul, hanti, hlast, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := hex x
    exact ⟨(-a).toNat, hanti _ _ (by omega) ha⟩
  · intro a n x
    set w := algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) with hw
    have hwn : w ^ n ∈ Per.FilD l n := by
      rw [hw, ← map_pow, hlast, h1]
      exact Ideal.mem_span_singleton_self _

    have hdvr := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
    obtain ⟨_, _, -, -, -, -, hfr⟩ := hdvr
    have hinj : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
    have hw0 : w ≠ 0 := by
      intro h
      have h0 : aDp l ξ = 0 := hinj (by rw [← hw, h, map_zero])
      rw [hc] at h0
      have h2 : aDp l (xi C.ε) = 0 := (Units.mul_right_eq_zero c).1 h0
      exact one_ne_zero (hreg 1 (by rw [h2, zero_mul]))
    haveI := hfr
    have hne : aDp l ξ ≠ 0 := fun h => hw0 (by rw [hw, h, map_zero])
    obtain ⟨u, hu⟩ : IsUnit w :=
      IsLocalization.map_units (Per.BdR l) (⟨aDp l ξ, mem_nonZeroDivisors_of_ne_zero hne⟩ : nonZeroDivisors _)
    have hv : ((u⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ∈ Per.FilD l (-1) := by
      rw [mem_FilD_iff_xi_pow l C.ε (core_isEps l C)]
      refine ⟨((c⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l), ?_⟩
      have e1 : (- (-1 : ℤ)).toNat = 1 := by norm_num
      have e2 : (-1 : ℤ).toNat = 0 := by norm_num
      have e3 : aDp l (xi C.ε) = aDp l ξ * ((c⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l) := by
        rw [hc, mul_comm (c : Per.BdRp l), mul_assoc, Units.mul_inv, mul_one]
      rw [e1, e2, pow_one, pow_zero, e3, map_mul (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l ξ), ← hw, ← hu,
        ← mul_assoc, Units.inv_mul, one_mul]
      simp
    have hvn : ∀ k : ℕ, ((u⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ k ∈ Per.FilD l (-(k : ℤ)) := by
      intro k
      induction k with
      | zero => simpa using hone
      | succ k ih =>
        rw [pow_succ]
        have := hmul _ _ _ _ ih hv
        rwa [show -(k : ℤ) + -1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
    constructor
    · intro h
      have := hmul _ _ _ _ (hvn n) h
      rwa [← mul_assoc, ← mul_pow, ← hu, Units.inv_mul, one_pow, one_mul,
        show -(n : ℤ) + (a + n) = a by ring] at this
    · intro h
      have := hmul _ _ _ _ hwn h
      rwa [add_comm] at this
  · have hdvr := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
    obtain ⟨_, _, -, -, -, -, hfr⟩ := hdvr
    haveI := hfr
    have hinjD : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
    have hplus : Function.Injective C.jP := (GlobalTheory.MemLoc.AwayT.away_and_inj l C).2.2
    have hloc : Function.Injective (algebraMap (Per.Acris l) (BcrisP l)) := by
      refine IsLocalization.injective (M := Submonoid.powers ((l : ℕ) : Per.Acris l)) (BcrisP l) ?_
      rw [Submonoid.powers_le, mem_nonZeroDivisors_iff]
      have ht := (acris_torsionFree_complete l).1
      exact ⟨ht, fun x hx => ht x (by rw [mul_comm]; exact hx)⟩
    intro x y hxy
    apply hloc
    apply hplus
    apply hinjD
    rw [C.jP_alg, C.jP_alg, ← C.ι_j, ← C.ι_j, hxy]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFactsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdR_filtration_ker_theta_generator_facts : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → (∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n}) ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a) ∧ (∀ (n : ℕ) (z : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l n ↔ z ∈ Per.FilP l n) ∧ (∀ x : Per.BdR l, ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ))) ∧ (∀ (a : ℤ) (n : ℕ) (x : Per.BdR l), algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ n * x ∈ Per.FilD l (a + n) ↔ x ∈ Per.FilD l a) ∧ Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
  first | exact @GlobalTheory.MemLoc.seed_fil | exact GlobalTheory.MemLoc.seed_fil | (intros; apply GlobalTheory.MemLoc.seed_fil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFacts
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP.AinfDiv
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem cc_l : WittVector.constantCoeff (p := l) (R := OCb l) ((l : ℕ) : Ainf l) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem dvd_iff (y : Ainf l) :
    ((l : ℕ) : Ainf l) ∣ y ↔ WittVector.constantCoeff (p := l) (R := OCb l) y = 0 := by
  rw [← RingHom.mem_ker, WittVector.ker_constantCoeff, Ideal.mem_span_singleton]

theorem dvd_E : ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree := by
  have h := bk.monic.as_sum
  have : bk.E = X ^ bk.Ep.natDegree + ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * X ^ i := by
    change ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
    conv_lhs => rw [h]
    rw [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_add (f := _), map_pow, add_sub_cancel_left, map_sum]
  refine Finset.dvd_sum fun i hi => ?_
  obtain ⟨d, hd⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  rw [hd, map_mul, map_mul, map_mul, map_natCast, map_natCast, mul_assoc]
  exact dvd_mul_right _ _

theorem cc_E : WittVector.constantCoeff (p := l) (R := OCb l) (bk.ev bk.E) = bk.flat ^ bk.Ep.natDegree := by
  have h := (dvd_iff _).1 (dvd_E bk)
  rw [map_sub, sub_eq_zero, map_pow, bk.ev_X] at h
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h ⊢
  exact h

theorem cc_E_ne : WittVector.constantCoeff (p := l) (R := OCb l) (bk.ev bk.E) ≠ 0 := by
  intro h
  have hu := (isUnit_inclW_of_span bk.span_ev).map (WittVector.constantCoeff (p := l) (R := Cb l))
  rw [WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, ← WittVector.constantCoeff_apply, h,
    map_zero] at hu
  exact not_isUnit_zero hu

theorem flat_ne : bk.flat ≠ 0 := by
  intro h
  apply cc_E_ne bk
  rw [cc_E, h, zero_pow bk.deg_pos.ne']

theorem flat_not_unit : ¬ IsUnit bk.flat := by
  intro h
  have h1 : IsUnit (bk.ev bk.E) := by
    refine GlobalTheory.Per.AinfComplete.witt_isUnit _ ?_
    rw [cc_E]; exact h.pow _
  have h2 : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have := h1.map (Per.θ l)
  rw [h2] at this
  exact not_isUnit_zero this

theorem flat_nil : IsNilpotent (Perfection.coeff (ModP (OC l) l) l 0 bk.flat) :=
  GlobalTheory.Per.AinfComplete.nilpotent_of_not_isUnit l _ fun h =>
    flat_not_unit bk (GlobalTheory.Per.AinfComplete.perfection_isUnit _ h)

theorem flat_haus (x : OCb l) (hx : ∀ n, bk.flat ^ n ∣ x) : x = 0 :=
  GlobalTheory.Per.AinfComplete.perfection_haus (flat_nil bk) x hx

theorem complete : IsAdicComplete (Ideal.span {bk.flat}) (OCb l) := {
  haus' x hx := by
    refine flat_haus bk x fun n => ?_
    have := hx n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero] at this
    exact Ideal.mem_span_singleton.1 this,
  prec' := (GlobalTheory.Per.AinfComplete.precomplete_of_summ
    (GlobalTheory.Per.AinfComplete.summ_of_tails
      (GlobalTheory.Per.AinfComplete.perfection_tails (flat_nil bk)))).prec' }

theorem dvd_of_dvd_X_mul (y : Ainf l) (h : ((l : ℕ) : Ainf l) ∣ bk.ev X * y) : ((l : ℕ) : Ainf l) ∣ y := by
  rw [dvd_iff] at h ⊢
  rw [map_mul, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (flat_ne bk)

theorem dvd_of_forall (y : Ainf l) (h : ∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) :
    ((l : ℕ) : Ainf l) ∣ y := by
  rw [dvd_iff]
  refine flat_haus bk _ fun m => ?_
  obtain ⟨z, hz⟩ := h m
  rw [dvd_iff, map_sub, sub_eq_zero, map_mul, map_pow, bk.ev_X] at hz
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at hz ⊢
  rw [hz]
  exact dvd_mul_right _ _


include bk in
theorem mem_pow (n : ℕ) (y : Ainf l)
    (h : ((l : ℕ) : Ainf l) * y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2)) :
    y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n := by
  rw [← bk.span_ev] at h ⊢
  have h1 : (Ideal.span {((l : ℕ) : Ainf l)} ⊔ Ideal.span {bk.ev bk.E}) ^ (2 * n + 2) ≤
      Ideal.span {((l : ℕ) : Ainf l)} ^ (n + 1) ⊔ Ideal.span {bk.ev bk.E} ^ (n + 1) := by
    rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring]
    exact Ideal.sup_pow_add_le_pow_sup_pow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (h1 h)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hu hv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  have hb : ((l : ℕ) : Ainf l) ∣ b := by
    rw [dvd_iff]
    have := congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) huv
    simp only [map_add (f := _), map_mul, map_pow, cc_l, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_mul,
      zero_add] at this
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (cc_E_ne bk))
  obtain ⟨b', rfl⟩ := hb
  have hy : y = a * ((l : ℕ) : Ainf l) ^ n + b' * bk.ev bk.E ^ (n + 1) := by
    rw [← sub_eq_zero]
    apply ainf_torsionFree
    linear_combination -huv
  rw [hy]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.pow_right_mono le_sup_left n ?_
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · refine Ideal.pow_right_mono le_sup_right n ?_
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.2 ⟨b' * bk.ev bk.E, by ring⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    (∀ (n : ℕ) (y : Ainf l), ((l : ℕ) : Ainf l) * y ∈
        (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2) →
      y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n) ∧
    (∀ y : Ainf l, ((l : ℕ) : Ainf l) ∣ bk.ev X * y → ((l : ℕ) : Ainf l) ∣ y) ∧
    (∀ y : Ainf l, (∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) → ((l : ℕ) : Ainf l) ∣ y) ∧
    bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧ IsAdicComplete (Ideal.span {bk.flat}) (OCb l) ∧
    ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree :=
  fun _ _ _ bk => ⟨mem_pow bk, dvd_of_dvd_X_mul bk, dvd_of_forall bk, flat_ne bk, flat_not_unit bk,
    complete bk, dvd_E bk⟩

end GlobalTheory.BSP.AinfDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFactsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_divisibility_breuilKisin_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ (n : ℕ) (y : Ainf l), ((l : ℕ) : Ainf l) * y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2) → y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n) ∧ (∀ y : Ainf l, ((l : ℕ) : Ainf l) ∣ bk.ev X * y → ((l : ℕ) : Ainf l) ∣ y) ∧ (∀ y : Ainf l, (∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) → ((l : ℕ) : Ainf l) ∣ y) ∧ bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧ IsAdicComplete (Ideal.span {bk.flat}) (OCb l) ∧ ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree := by
  first | exact @GlobalTheory.BSP.AinfDiv.main | exact GlobalTheory.BSP.AinfDiv.main | (intros; apply GlobalTheory.BSP.AinfDiv.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensional
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DRDual

open GlobalTheory.DRFil

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def twistRep (χ : G →* LLˣ) (ρ : Representation LL G V) : Representation LL G V where
  toFun g := ((χ g : LLˣ) : LL) • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

theorem act_zpow (T : Fˣ) (hT : (T : F) = PD.ι PD.t) (n : ℤ) (g : G) :
    PD.actdR g ((T ^ n : Fˣ) : F) = ((PD.χ g ^ n : Qpˣ) : Qp) • ((T ^ n : Fˣ) : F) := by
  have hsm : ∀ (q : Qp) (b : B), PD.ι (q • b) = q • PD.ι b := fun q b =>
    (PD.ι.toLinearMap.restrictScalars Qp).map_smul q b
  have h1 : Units.map (PD.actdR g : F →* F) T = Units.map (algebraMap Qp F : Qp →* F) (PD.χ g) * T := by
    ext
    have h2 := PD.ι_comm g PD.t
    rw [PD.t_act, hsm, ← hT, Algebra.smul_def] at h2
    exact h2.symm
  have h3 := congrArg (fun x : Fˣ => ((x ^ n : Fˣ) : F)) h1
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h3
  rw [Algebra.smul_def, ← map_zpow]
  exact h3

theorem twist_unit (ρ ρ' : Representation LL G V) (u : Fˣ) (n : ℤ) (ψ : G → Qpˣ)
    (hu : (u : F) ∈ PD.Fil n) (hu' : ((u⁻¹ : Fˣ) : F) ∈ PD.Fil (-n))
    (ha : ∀ g, PD.actdR g (u : F) = (ψ g : Qp) • (u : F))
    (ha' : ∀ g, PD.actdR g ((u⁻¹ : Fˣ) : F) = (((ψ g)⁻¹ : Qpˣ) : Qp) • ((u⁻¹ : Fˣ) : F))
    (hρ : ∀ g x, (ψ g : Qp) • ρ' g x = ρ g x) :
    (IsDR PD ρ → IsDR PD ρ') ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), multV PD ρ' τ (n + a) = multV PD ρ τ a := by
  have hρ' : ∀ g x, (((ψ g)⁻¹ : Qpˣ) : Qp) • ρ g x = ρ' g x := fun g x => by
    rw [← hρ, smul_smul, Units.inv_mul, one_smul]
  let Φ : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V u ∘ₗ ext Qp F LinearMap.id
  let Ψ : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V (u⁻¹ : Fˣ) ∘ₗ ext Qp F LinearMap.id
  have h1 : ∀ x, Φ (Ψ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul v b => simp [Φ, Ψ]
  have h2 : ∀ x, Ψ (Φ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul v b => simp [Φ, Ψ]
  let E : V ⊗[Qp] F ≃ₗ[LL] V ⊗[Qp] F := LinearEquiv.ofLinear Φ Ψ (LinearMap.ext h1) (LinearMap.ext h2)
  have hD : (DdR PD ρ).map E.toLinearMap = DdR PD ρ' := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact twist_mem_DdR PD ρ ρ' LinearMap.id _ _ ha hρ hx
    · exact ⟨Ψ y, twist_mem_DdR PD ρ' ρ LinearMap.id _ _ ha' hρ' hy, h1 y⟩
  have hF : ∀ τ a, (FildR PD ρ τ a).map E.toLinearMap = FildR PD ρ' τ (n + a) := by
    intro τ a
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact twist_mem_FildR PD ρ ρ' LinearMap.id _ _ ha hρ τ hu hx
    · have := twist_mem_FildR PD ρ' ρ LinearMap.id _ _ ha' hρ' τ hu' hy
      rw [neg_add_cancel_left] at this
      exact ⟨Ψ y, this, h1 y⟩
  refine ⟨fun h => ?_, fun τ a => ?_⟩
  · rw [IsDR, ← hD, LinearEquiv.finrank_map_eq, h]
  · unfold multV
    rw [add_assoc, ← hF, ← hF, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

end Generic

theorem twisted_dual_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ), Function.Bijective m → (∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' m j hm hg h
  have := K.2
  have := LL.2
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  have hs := filSpans T K LL ρ h
  let ρ₀ : Representation ↥LL.1 ↥(GK K) V' := twistRep (cycLL (P.PD K) ↥LL.1 ^ (-j)) ρ'
  have hρ₀ : ∀ g y, ρ₀ g y = ((cycLL (P.PD K) ↥LL.1 g ^ (-j) : (↥LL.1)ˣ) : ↥LL.1) • ρ' g y :=
    fun g y => rfl
  have hβ : ∀ g x y, m (ρ g x) (ρ₀ g y) = m x y := fun g x y => by
    rw [hρ₀, map_smul, hg, smul_eq_mul, zpow_neg, Units.inv_mul_cancel_left]
  have hβ' : Function.Bijective m.flip := (LinearEquiv.ofBijective m hm).flip.bijective
  have h₀ : IsDR (P.PD K) ρ₀ := isDR_of_spans T K LL ρ₀
    (spans_dual_of_spans (P.PD K) ρ ρ₀ m (isField_dR T) hβ hβ' (hs.spans _))
  have ht : (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K : P.R.BdR) = (P.PD K).ι (P.PD K).t := rfl
  obtain ⟨h1, h2⟩ := twist_unit (P.PD K) ρ₀ ρ' (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K ^ (-j)) (-j)
    (fun g => (P.PD K).χ g ^ (-j)) (tdR_zpow_mem T K _)
    (by rw [← zpow_neg]; exact tdR_zpow_mem T K _) (act_zpow _ _ ht _)
    (fun g => by rw [← zpow_neg, ← zpow_neg]; exact act_zpow _ _ ht _ g)
    (fun g x => by
      rw [hρ₀, ← algebraMap_smul ↥LL.1]
      congr 1
      exact congrArg Units.val
        (map_zpow (Units.map (algebraMap ℚ_[l] ↥LL.1 : ℚ_[l] →* ↥LL.1)) ((P.PD K).χ g) (-j)))
  refine ⟨h1 h₀, fun τ a _ => ?_⟩
  obtain ⟨n, d, k, had⟩ := exists_adapted (P.PD K) (isField_dR T) ρ hs τ
  obtain ⟨d', had'⟩ := had.dual ρ₀ m hβ hβ'
  rw [show -a - j = -j + -a by ring, h2, had.multV_eq, had'.multV_eq]
  simp only [neg_inj]

end GlobalTheory.DRDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensionalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_representation_hom_finite_dimensional : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ), Function.Bijective m → (∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  first | exact @GlobalTheory.DRDual.twisted_dual_deRham | exact GlobalTheory.DRDual.twisted_dual_deRham | (intros; apply GlobalTheory.DRDual.twisted_dual_deRham <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMap_of_pow_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F := by
  intro l _ A A' _ _ f u u' ρ ρ' k hρ' hdvd hk
  obtain ⟨z, hz⟩ := hdvd
  have h : ‖toDisc l u' ρ' (f u)‖ ≤ ρ := by
    rw [hz, map_mul]
    calc ‖toDisc l u' ρ' (u' ^ k) * toDisc l u' ρ' z‖
        ≤ ‖toDisc l u' ρ' (u' ^ k)‖ * ‖toDisc l u' ρ' z‖ := norm_mul_le _ _
      _ ≤ (ρ' : ℝ) ^ k * 1 :=
          mul_le_mul (norm_toDisc_pow_le k hρ') (norm_toDisc_le z) (norm_nonneg _) (by positivity)
      _ = ((ρ' ^ k : ℝ≥0) : ℝ) := by simp
      _ ≤ ρ := NNReal.coe_le_coe.2 hk
  exact ⟨Disc.map f h, isDiscMap_map f h⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvdStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F := by
  first | exact @GlobalTheory.BSP.exists_discMap_of_pow_dvd | exact GlobalTheory.BSP.exists_discMap_of_pow_dvd | (intros; apply GlobalTheory.BSP.exists_discMap_of_pow_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRings
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRings
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_σF_self {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Per.Fl l) : x ∣ Per.σF g x := by
  apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
  rw [GlobalTheory.RingBasics.untilt_σF]
  generalize x.untilt = y
  by_cases hy : (y : ℂ_[l]) = 0
  · obtain rfl : y = 0 := Subtype.ext hy
    simp
  · refine ⟨⟨Per.σC g y / y, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, GlobalTheory.RingBasics.norm_σC, div_self (norm_ne_zero_iff.2 hy)]
    · rw [GlobalTheory.RingIface.sigO_coe]
      change Per.σC g y = (y : ℂ_[l]) * (Per.σC g y / y)
      field_simp

theorem galois_discMap : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    (∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X)) ∧ ∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l,
      ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G := by
  intro l _ K bk
  have h : ∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X) := fun g => by
    rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich]
    exact map_dvd (WittVector.teichmuller l) (dvd_σF_self g bk.flat)
  refine ⟨h, fun ρ hρ g => ⟨_, isDiscMap_map (Per.σA g) ?_⟩⟩
  obtain ⟨c, hc⟩ := h g
  have h1 := norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ
  rw [pow_one, pow_one] at h1
  rw [hc, map_mul]
  exact (norm_mul_le _ _).trans ((mul_le_mul h1 (norm_toDisc_le c) (norm_nonneg _) ρ.2).trans (mul_one _).le)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRingsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_extends_to_ainf_disc_rings : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X)) ∧ ∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l, ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G := by
  first | exact @GlobalTheory.BSP.galois_discMap | exact GlobalTheory.BSP.galois_discMap | (intros; apply GlobalTheory.BSP.galois_discMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpRangePositiveSignPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpRangePositiveSignPlace
noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem stepJumpDirect_holds : StepJumpDirect := by
  intro D i r eta s S sg U hs hJ Xs w hw hsg
  obtain ⟨hc, hj, hU⟩ := hJ w hw
  refine ⟨insert 0 (U w), ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · constructor <;> push_cast <;> omega
    · obtain ⟨h, -, -⟩ := hU u hu
      have hs' : ((eta : ℚ) + D.R.t + 1) < s := by exact_mod_cast hs
      have hS : (0 : ℚ) ≤ S := by positivity
      have ht : (0 : ℚ) ≤ D.R.t := by positivity
      have he : (0 : ℚ) ≤ eta := by positivity
      have key : -((eta : ℚ) + D.R.t + 1) - 1 < u ∧ (u : ℚ) ≤ s + S := by
        rcases h with ⟨h1, h2⟩ | h | h
        · have h1' : (0 : ℚ) ≤ u := by exact_mod_cast h1
          have h2' : (u : ℚ) < D.R.t := by exact_mod_cast h2
          constructor <;> linarith
        · rw [abs_le] at h; unfold cen at h
          constructor <;> linarith [h.1, h.2]
        · unfold cloud cen at h; rw [hsg] at h; simp only [if_true] at h; push_cast at h
          constructor <;> linarith [h.1, h.2]
      have k1 : -((eta : ℤ) + D.R.t + 1) - 1 < u := by exact_mod_cast key.1
      have k2 : u ≤ (s : ℤ) + S := by exact_mod_cast key.2
      constructor <;> push_cast <;> omega
  · exact (Finset.card_insert_le _ _).trans (by omega)
  · intro x τ a ha
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (hj x τ a ha))

end GlobalTheory.Pass

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpRangePositiveSignPlaceStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jump_range_positive_sign_place : StepJumpDirect := by
  first | exact @GlobalTheory.Pass.stepJumpDirect_holds | exact GlobalTheory.Pass.stepJumpDirect_holds | (intros; apply GlobalTheory.Pass.stepJumpDirect_holds <;> assumption)
end
end
