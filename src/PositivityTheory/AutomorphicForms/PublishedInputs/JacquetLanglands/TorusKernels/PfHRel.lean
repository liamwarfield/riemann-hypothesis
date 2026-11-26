module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.ExLLeOfCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Qminor

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHRel
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.HeckeRelationLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def asm (g : InfinitePlace F → GL (Fin 2) ℝ) : GL (Fin 2) (TR.Rinf F) where
  val := Matrix.of fun i j v => (g v).val i j
  inv := Matrix.of fun i j v => (g v)⁻¹.val i j
  val_inv := by
    refine Matrix.ext fun i j => funext fun v => ?_
    have h := congrFun (congrFun (g v).mul_inv i) j
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (g v).val i 0 * (g v)⁻¹.val 0 j + (g v).val i 1 * (g v)⁻¹.val 1 j = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v
    rw [h]
    fin_cases i <;> fin_cases j <;> rfl
  inv_val := by
    refine Matrix.ext fun i j => funext fun v => ?_
    have h := congrFun (congrFun (g v).inv_mul i) j
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (g v)⁻¹.val i 0 * (g v).val 0 j + (g v)⁻¹.val i 1 * (g v).val 1 j = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v
    rw [h]
    fin_cases i <;> fin_cases j <;> rfl

omit [NumberField F] [IsTotallyReal F] in
theorem gv_asm (g : InfinitePlace F → GL (Fin 2) ℝ) (v : InfinitePlace F) : gv v (asm g) = g v :=
  Units.ext (Matrix.ext fun _ _ => rfl)

omit [NumberField F] [IsTotallyReal F] in
theorem exists_g (hc : B1c) (z : X (InfinitePlace F)) : ∃ g : GL (Fin 2) (TR.Rinf F), (fun v => gv v g • iP) = z := by
  choose h _ _ hh using fun v => hc.2.2.2.2.2 (z v)
  exact ⟨asm h, funext fun v => by rw [gv_asm, hh]⟩

theorem inf_of (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    Matrix.GeneralLinearGroup.map (TR.pInf F) (TR.infGL F 2 g * finGL F 2 x) = g := by
  rw [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one]

theorem fin_of (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    Matrix.GeneralLinearGroup.map (pFin F) (TR.infGL F 2 g * finGL F 2 x) = x := by
  rw [map_mul, TR.pFin_infGL, pFin_finGL, one_mul]

end UpperTheory.Esk.HeckeRelationLemmas

open UpperTheory.Esk in
theorem UpperTheory.Esk.pf_HRel : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.HRel := by
  intro hb hc F _ _ _ k
  have hne : ∀ g : GL (Fin 2) (TR.Rinf F), ∏ v, j1 (k v) (gv v g) iP ≠ 0 :=
    fun g => Finset.prod_ne_zero_iff.2 fun v _ => hb.2.1 _ _ _
  refine ⟨fun f => ⟨fun a => f (fun v => gv v (Matrix.GeneralLinearGroup.map (TR.pInf F) a) • iP,
      Matrix.GeneralLinearGroup.map (pFin F) a) / ∏ v, j1 (k v) (gv v (Matrix.GeneralLinearGroup.map (TR.pInf F) a)) iP,
      fun g x => ?_⟩, fun f φ φ' h h' => ?_, fun f f' φ h h' => ?_, fun f f' φ φ' s h h' => ?_, fun g x => ?_,
      fun n a f φ h => ?_⟩
  · simp only [HeckeRelationLemmas.inf_of, HeckeRelationLemmas.fin_of]
    exact div_mul_cancel₀ _ (hne g)
  · funext a
    rw [← TR.infGL_mul_finGL a]
    exact mul_right_cancel₀ (hne _) ((h _ _).trans (h' _ _).symm)
  · funext p
    obtain ⟨z, x⟩ := p
    obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    rw [← h g x, ← h' g x]
  · intro g x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc, h g x, h' g x]
  · simp
  · intro g x
    simp only [Dat.Op, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change φ.1 (TR.infGL F 2 g * finGL F 2 x * finGL F 2 (a i)) * _ = _
    rw [mul_assoc, ← map_mul, h g (x * a i)]
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfPropMV
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

namespace UpperTheory.Esk.PropMVAux

variable {l : ℕ} [Fact l.Prime]

theorem add_lt {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem norm_one_of {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have h1 : ‖x - 1‖ ≠ ‖(1 : Qbar l)‖ := by rw [norm_one]; exact h.ne
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
  rwa [sub_add_cancel, norm_one, max_eq_right h.le] at h2

def oneU (l : ℕ) [Fact l.Prime] : Subgroup (Qbar l)ˣ where
  carrier := {x | ‖(x : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have e : ((a * b : (Qbar l)ˣ) : Qbar l) - 1 = a * (b - 1) + (a - 1) := by rw [Units.val_mul]; ring
    show ‖_‖ < 1
    rw [e]
    refine add_lt ?_ ha
    rw [norm_mul, norm_one_of ha, one_mul]
    exact hb
  inv_mem' {a} ha := by
    have e : (a : Qbar l) * (((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(a - 1) := by
      rw [mul_sub, Units.mul_inv]; ring
    have h := congrArg norm e
    rw [norm_mul, norm_one_of ha, one_mul, norm_neg] at h
    show ‖_‖ < 1
    rw [h]
    exact ha

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
theorem cyc_mem (s : G F Ω) : cycBar F Ω l s ^ (l - 1) ∈ oneU l := by
  have e : ((cycBar F Ω l s ^ (l - 1) : (Qbar l)ˣ) : Qbar l) - 1 =
      algebraMap ℚ_[l] (Qbar l) ((((cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1 : ℤ_[l])) : ℚ_[l]) := by
    rw [Units.val_pow_eq_pow_val]
    change (algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l])) ^ _ - 1 = _
    simp
  show ‖_‖ < 1
  rw [e, norm_algebraMap']
  change ‖(cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1‖ < 1
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, ZMod.pow_card_sub_one_eq_one, sub_self]
  exact ((cycZ F Ω l s).isUnit.map _).ne_zero

theorem cont_cyc : Continuous (cycBar F Ω l) :=
  have h : Continuous fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l]) :=
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom h).comp (continuous_cycZ F Ω l)

theorem cyc_frob [IsAlgClosure F Ω] {A : ValuationSubring Ω} {v : Pl F} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (h : IsPlaceOver A v) {σ : G F Ω} (hσ : IsFrob A (normV v) σ) :
    ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
  change algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l σ : ℤ_[l]) : ℚ_[l]) = _
  rw [cycZ_of_isFrob hl h hσ]
  simp

theorem fin_l : {w : Pl F | ((l : ℕ) : 𝓞 F) ∈ w.asIdeal}.Finite := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

theorem cond_ex (ω : HChar F) {m : ℕ} (hm : 0 < m) (h : ω.OrderDvd m) :
    ∃ c : Pl F → ℕ, (∀ w, IsCondAt w ω (c w)) ∧ (∀ w, c w = 0 ↔ ω.UnrAt w) ∧ {w | c w ≠ 0}.Finite := by
  classical
  have ho := isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) h
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  have hex : ∀ w, ∃ n, ω.LevelLe w n := fun w => ⟨M, fun x hu hx => key w x hu fun _ => hx⟩
  have h0 : ∀ w, Nat.find (hex w) = 0 ↔ ω.UnrAt w := fun w => by rw [Nat.find_eq_zero, HChar.unrAt_iff]
  refine ⟨fun w => Nat.find (hex w), fun w => ⟨Nat.find_spec (hex w), fun n hn => Nat.find_min' (hex w) hn⟩, h0,
    hS.subset fun w hw => ?_⟩
  by_contra hS
  exact hw ((h0 w).2 fun x hx => key w x hx fun h => absurd h hS)

theorem loc_zpow {ω : HChar F} {w : Pl F} (hu : ω.UnrAt w) (x : (w.adicCompletion F)ˣ) :
    ∃ n : ℤ, ω.loc w x = ω.val w ^ n := by
  have hx0 : Valued.v (x : w.adicCompletion F) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (x : w.adicCompletion F) = WithZero.exp n := ⟨_, (WithZero.exp_log hx0).symm⟩
  have hun : IsUnitAt w (x * atFin w (unif w) ^ n) := by
    have h2 := unif_spec w
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h2, ← WithZero.exp_zsmul, hn, ← WithZero.exp_add]
    simp
  have h3 := hu _ hun
  rw [map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h3
  exact ⟨_, h3⟩

theorem closed_oneU : IsClosed (oneU l : Set (Qbar l)ˣ) := by
  have : IsClosed {x : Qbar l | ‖x - 1‖ < 1} := by
    simpa only [Metric.ball, dist_eq_norm] using IsUltrametricDist.isClosed_ball (1 : Qbar l) 1
  exact this.preimage Units.continuous_val

theorem dec_cong {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) {ι : Qbar l ≃+* ℂ} {ω : HChar F}
    {ξ : G F Ω →* (Qbar l)ˣ} (hc : Continuous ξ) (hL : IsLAdicOf art ι ω 0 ξ) {w : Pl F} (hu : ω.UnrAt w)
    (hv : ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1) {A : ValuationSubring Ω} (hA : IsPlaceOver A w) {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) : Cong (ξ σ) 1 := by
  have hm : toAb F Ω σ ∈ (art.comp (localIdele F w)).range.topologicalClosure := by
    rw [ha.dec w A hA]
    exact ⟨σ, hσ, rfl⟩
  have hle : (art.comp (localIdele F w)).range ≤ (oneU l).comap (liftAb ξ hc) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨τ, hτ⟩ := toAb_surjective (art (localIdele F w x))
    obtain ⟨n, hn⟩ := loc_zpow hu x
    have hv' : Units.map ι.symm.toRingHom.toMonoidHom (ω.val w) ∈ oneU l := hv
    have e : ξ τ = Units.map ι.symm.toRingHom.toMonoidHom (ω.val w) ^ n := by
      rw [← map_zpow, ← hn]
      exact Units.ext (hL.loc_away (Or.inr rfl) x τ hτ.symm)
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, ← hτ, liftAb_toAb, e]
    exact zpow_mem hv' _
  have h := Subgroup.topologicalClosure_minimal _ hle (closed_oneU.preimage (continuous_liftAb ξ hc)) hm
  rw [Subgroup.mem_comap, liftAb_toAb] at h
  exact h

theorem tr_det (ι : Qbar l ≃+* ℂ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (a b : ℂ)
    (h : M.charpoly.map ι.toRingHom = Polynomial.X ^ 2 - C a * Polynomial.X + C b) : M.trace = ι.symm a ∧ M.det = ι.symm b := by
  rw [Matrix.charpoly_fin_two] at h
  have h2 := congrArg (AddMonoidAlgebra.coeff · 1) h
  have h3 := congrArg (AddMonoidAlgebra.coeff · 0) h
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_C] at h2 h3
  rw [← h2, ← h3]
  simp

theorem det_res [IsAlgClosure F Ω] (ξ : G F Ω →* (Qbar l)ˣ) (hξ : Continuous ξ) (r : G F Ω →* GL (Fin 2) (Qbar l))
    (hr : Continuous r) (k : ℕ) (hk : l - 1 ∣ k) (hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1) {S : Set (Pl F)} (hS : S.Finite)
    (h : ∀ w, w ∉ S → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
      ‖(r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ σ⁻¹)‖ < 1 ∧
      (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ξ σ⁻¹ * (cycBar F Ω l σ : Qbar l) ^ k) :
    Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ (-(k : ℤ)) * ξ ∧ ResSum r ![1, ξ] := by
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have c1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp (hr.comp continuous_inv)
  have c2 : Continuous fun g : G F Ω => (ξ g⁻¹ : Qbar l) := Units.continuous_val.comp (hξ.comp continuous_inv)
  have c3 : Continuous fun g : G F Ω => (cycBar F Ω l g : Qbar l) := Units.continuous_val.comp cont_cyc
  have hdet : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ξ g⁻¹ * (cycBar F Ω l g : Qbar l) ^ k := fun g => by
    refine congrFun (Continuous.ext_on hD c1.matrix_det (c2.mul (c3.pow k)) ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    exact (h v hv A hA σ hσ).2
  have htr : ∀ g : G F Ω, ‖(r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ g⁻¹)‖ < 1 := fun g => by
    have h0 : IsClosed {x : Qbar l | ‖x‖ < 1} := by
      simpa only [Metric.ball, dist_zero_right] using IsUltrametricDist.isClosed_ball (0 : Qbar l) 1
    have h1 := h0.preimage (c1.matrix_trace.sub (continuous_const.add c2 : Continuous fun g : G F Ω => 1 + (ξ g⁻¹ : Qbar l)))
    refine h1.closure_subset_iff.2 ?_ (hD g)
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    exact (h v hv A hA σ hσ).1
  refine ⟨MonoidHom.ext fun g => Units.ext ?_, fun g i => ?_⟩
  · have h1 := hdet g⁻¹
    rw [inv_inv] at h1
    change (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ((cycBar F Ω l g ^ (-(k : ℤ)) * ξ g : (Qbar l)ˣ) : Qbar l)
    rw [h1]
    simp [mul_comm]
  · have h1 := hdet g⁻¹
    have h2 := htr g⁻¹
    rw [inv_inv] at h1 h2
    have h3 : ‖(r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det - ξ g‖ < 1 := by
      obtain ⟨t, rfl⟩ := hk
      have h4 : ‖((cycBar F Ω l g⁻¹ ^ ((l - 1) * t) : (Qbar l)ˣ) : Qbar l) - 1‖ < 1 := by
        rw [pow_mul]; exact pow_mem (cyc_mem g⁻¹) t
      rw [h1, ← mul_sub_one, norm_mul, hn, one_mul, ← Units.val_pow_eq_pow_val]
      exact h4
    have e : (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly - ∏ j, (Polynomial.X - C ((![1, ξ] j g : (Qbar l)ˣ) : Qbar l)) =
        C (-((r g : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ g))) * Polynomial.X + C ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det - ξ g) := by
      rw [Matrix.charpoly_fin_two, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_neg, map_sub, map_add (f := _), map_one]
      ring
    rw [← coeff_sub, e]
    rcases i with _ | _ | i
    · rwa [coeff_add, mul_coeff_zero, coeff_X_zero, mul_zero, zero_add, coeff_C_zero]
    · rwa [coeff_add, coeff_mul_X, coeff_C_zero, coeff_C_succ, add_zero, norm_neg]
    · rw [coeff_add, coeff_mul_X, coeff_C_succ, coeff_C_succ, add_zero, norm_zero]
      exact zero_lt_one

theorem norm_eq_one {x y : Qbar l} (hy : ‖y‖ = 1) (h : ‖x - y‖ < 1) : ‖x‖ = 1 := by
  have h1 : ‖x - y‖ ≠ ‖y‖ := by rw [hy]; exact h.ne
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
  rwa [sub_add_cancel, hy, max_eq_right h.le] at h2

theorem nu_lt {ι : Qbar l ≃+* ℂ} {x : ℂ} : Wc.nu ι x < 1 ↔ ‖ι.symm x‖ < 1 := by
  rw [Wc.nu_apply, ← NNReal.coe_lt_one, coe_nnnorm]

theorem nu_eq {ι : Qbar l ≃+* ℂ} {x : ℂ} : Wc.nu ι x = 1 ↔ ‖ι.symm x‖ = 1 := by
  rw [Wc.nu_apply, ← NNReal.coe_eq_one, coe_nnnorm]

open Classical in
theorem prod_away {ι : Qbar l ≃+* ℂ} (D : Wc.LDat F ι) (S : Set (InfinitePlace F)) (t : ℕ) (w : Pl F)
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) : (∏ v, if D.pl v = w ∧ v ∈ S then (l : ℂ) ^ t else 1) = 1 :=
  Finset.prod_eq_one fun v _ => by
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hw (h ▸ D.mem v)

open Classical in
theorem prod_at {ι : Qbar l ≃+* ℂ} (D : Wc.LDat F ι) (S : Set (InfinitePlace F)) (t : ℕ) (w : Pl F) (v₀ : InfinitePlace F)
    (hv : D.pl v₀ = w) : (∏ v, if D.pl v = w ∧ v ∈ S then (l : ℂ) ^ t else 1) = if v₀ ∈ S then (l : ℂ) ^ t else 1 := by
  rw [Finset.prod_eq_single v₀ (fun v _ hne => if_neg fun h => hne (D.inj (h.1.trans hv.symm)))
    (fun h => absurd (Finset.mem_univ _) h)]
  by_cases h : v₀ ∈ S <;> simp [hv, h]

end UpperTheory.Esk.PropMVAux
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHFin
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.FiniteLevelGroupLemmas

def Gm (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) :
    (X (InfinitePlace F) × GF F → ℂ) →ₗ[ℂ] (GA F 2 → ℂ) where
  toFun f := Classical.choose ((h F k).1 f)
  map_add' f f' := by
    have e := (h F k).2.2.2.1 f f' _ _ 1 (Classical.choose_spec ((h F k).1 f)) (Classical.choose_spec ((h F k).1 f'))
    simp only [one_smul] at e
    exact (h F k).2.1 _ _ _ (Classical.choose_spec ((h F k).1 (f + f'))) e
  map_smul' s f := by
    have e := (h F k).2.2.2.1 0 f 0 _ s (h F k).2.2.2.2.1 (Classical.choose_spec ((h F k).1 f))
    simp only [zero_add] at e
    exact (h F k).2.1 _ _ _ (Classical.choose_spec ((h F k).1 (s • f))) e

theorem rel (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ)
    (f : X (InfinitePlace F) × GF F → ℂ) : Rel k f (Gm h F k f) :=
  Classical.choose_spec ((h F k).1 f)

theorem inj (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) :
    Function.Injective (Gm h F k) := by
  intro f f' e
  have h2 := rel h F k f'
  rw [← e] at h2
  exact (h F k).2.2.1 f f' _ (rel h F k f) h2

end UpperTheory.Esk.FiniteLevelGroupLemmas

theorem UpperTheory.Esk.pf_HFin : UpperTheory.Esk.HRel → UpperTheory.Esk.H2a → UpperTheory.Esk.H2d → UpperTheory.Esk.H2e → UpperTheory.Esk.HFinC → UpperTheory.Esk.HFin := by
  intro hR h2a h2d h2e hC F _ _ _ k c hc ω χ hω hχ hS hk
  classical
  let S : Set (TR.Sm F 2) := {φ | IsHolV k c ω φ ∧ TR.IsCuspForm φ}
  have : FiniteDimensional ℂ (Submodule.span ℂ S) := hC F k c hc ω hω
  let W : Submodule ℂ (GA F 2 → ℂ) := (Submodule.span ℂ S).map (TR.Sm F 2).subtype
  have : FiniteDimensional ℂ W := inferInstance
  let p := Submodule.span ℂ {f | (mkDat c χ).IsForm k f}
  have hle : p.map (FiniteLevelGroupLemmas.Gm hR F k) ≤ W := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hrel := FiniteLevelGroupLemmas.rel hR F k f
    obtain ⟨hs, hhol⟩ := h2d F k c hc ω χ hω hχ hS hk f _ hf hrel
    have hb := (h2a F k c hc ω χ hω hχ hS hk f _ hf hrel).2.2.2
    have hcusp := h2e F k c ω ⟨_, hs⟩ hω hk hhol hb
    exact ⟨⟨_, hs⟩, Submodule.subset_span ⟨hhol, hcusp⟩, rfl⟩
  have : FiniteDimensional ℂ (p.map (FiniteLevelGroupLemmas.Gm hR F k)) := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (FiniteLevelGroupLemmas.inj hR F k) p).symm
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHCap
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

namespace UpperTheory.Esk.CasimirEigenvalueLemmas

theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {k c} {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : UpperTheory.Esk.IsHolV k c ω φ) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ.cent, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  _root_.UpperTheory.Reformulated.B.Qf10.casimir E hE k φ h0 h1 h2 u

end UpperTheory.Esk.CasimirEigenvalueLemmas

open UpperTheory.Esk.CasimirEigenvalueLemmas in
theorem UpperTheory.Esk.pf_HCap : UpperTheory.Esk.HCap := by
  intro F _ _ _ k c ω hω φ hφ
  refine ⟨by simpa using lie_scalar hω hφ 1, fun v u => ?_⟩
  have h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
    classical
    rw [← lie_scalar hω hφ (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have := casimir _ (TR.glRel_Eop v) (k v) φ h0 (hφ.wt v) (hφ.low v) u
  rw [← this, TR.cap]
  norm_num
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfGMod
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped NNReal

namespace UpperTheory.Esk.ModulusCharacterLemmas

variable {F : Type} [Field F] [NumberField F]

theorem tnn {e : ℝ≥0} (he : e ≠ 0) (m : ℤ) : WithZeroMulInt.toNNReal he (WithZero.exp m) = e ^ m := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]; rfl

theorem exp_mul_pow (m : ℤ) :
    WithZero.exp m * (WithZero.exp (-1 : ℤ)) ^ m = (1 : WithZero (Multiplicative ℤ)) := by
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_zpow, ← WithZero.coe_mul,
    ← ofAdd_zsmul, ← ofAdd_add]
  simp

theorem val_exp {w : Pl F} {x : w.adicCompletion F} (hx : x ≠ 0) : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
  ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm⟩

theorem norm_eq (w : Pl F) {x : w.adicCompletion F} {m : ℤ} (hm : Valued.v x = WithZero.exp m) :
    ‖x‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ m := by
  rw [FinitePlace.norm_def (x := x), hm, tnn, NNReal.coe_zpow, NNReal.coe_natCast]

theorem normV_eq (w : Pl F) : normV w = Ideal.absNorm w.asIdeal := by
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem nu_nat {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (h : ¬ l ∣ n) : nu ι (n : ℂ) = 1 := by
  have e : ι.symm (n : ℂ) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l]) := by rw [map_natCast, map_natCast]
  apply NNReal.coe_injective
  rw [nu_apply, coe_nnnorm, e, norm_algebraMap',
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h), NNReal.coe_one]

theorem not_dvd (w : Pl F) {l : ℕ} [hl : Fact l.Prime] (h : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) : ¬ l ∣ normV w := by
  intro hd
  haveI := w.isPrime
  have hne : normV w ≠ 0 := by
    rw [normV_eq]; have := HeightOneSpectrum.one_lt_absNorm w; omega
  haveI : Finite (𝓞 F ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  have hd' : l ∣ Fintype.card (𝓞 F ⧸ w.asIdeal) := by rw [Fintype.card_eq_nat_card]; exact hd
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card l hd'
  have h1 : (l : 𝓞 F ⧸ w.asIdeal) * a = 0 := by rw [← nsmul_eq_mul, ← ha, addOrderOf_nsmul_eq_zero]
  have h2 : (l : 𝓞 F ⧸ w.asIdeal) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ne, Ideal.Quotient.eq_zero_iff_mem]; exact h
  have h3 : a = 0 := (mul_eq_zero.1 h1).resolve_left h2
  rw [h3, addOrderOf_zero] at ha
  exact hl.out.one_lt.ne ha

theorem away {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Pl F) (h : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    {x : w.adicCompletion F} (hx : x ≠ 0) : nu ι (‖x‖ : ℂ) = 1 := by
  obtain ⟨m, hm⟩ := val_exp hx
  rw [norm_eq w hm, Complex.ofReal_zpow, Complex.ofReal_natCast, map_zpow₀, ← normV_eq, nu_nat ι (not_dvd w h),
    one_zpow]

theorem atL {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι) (v : InfinitePlace F)
    {x : (D.pl v).adicCompletion F} (hx : x ≠ 0) : nu ι ((‖x‖ : ℂ) * D.em v x) = 1 := by
  obtain ⟨m, hm⟩ := val_exp hx
  set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL
  have hLv : Valued.v L = WithZero.exp (-1 : ℤ) := D.unif v
  have hL0 : L ≠ 0 := fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm
  have hemL : D.em v L = (l : ℂ) := map_natCast _ l
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hy : Valued.v (x * L ^ m) = 1 := by rw [map_mul, map_zpow₀, hLv, hm, exp_mul_pow]
  have hnu : nu ι (D.em v (x * L ^ m)) = 1 :=
    le_antisymm ((D.le v _).2 hy.le) (not_lt.1 fun h => ((D.lt v _).1 h).ne hy)
  have hn : ‖x‖ = (l : ℝ) ^ m := by rw [norm_eq _ hm, ← normV_eq, D.norm v]
  have e : (‖x‖ : ℂ) * D.em v x = D.em v (x * L ^ m) := by
    rw [hn, map_mul, map_zpow₀, hemL, Complex.ofReal_zpow, Complex.ofReal_natCast]
    ring
  rw [e, hnu]

theorem nrm_unit {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem fin_supp (y : (Af F)ˣ) : (Function.mulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖).Finite := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (nrm_unit (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

end UpperTheory.Esk.ModulusCharacterLemmas

open UpperTheory.Esk.ModulusCharacterLemmas in
theorem UpperTheory.Esk.pf_GMod : UpperTheory.Esk.GMod := by
  intro F _ _ l _ ι D z
  have hz : ∀ w, pLoc F w (z : Af F) ≠ 0 := fun w => (z.isUnit.map (pLoc F w)).ne_zero
  have habs : absF z = ∏ᶠ w : Pl F, ‖pLoc F w (z : Af F)‖ := rfl
  refine ⟨?_, ?_⟩
  · rw [habs]
    exact finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w => norm_pos_iff.2 (hz w)
  classical
  have hfin := fin_supp z
  set s : Finset (Pl F) := hfin.toFinset ∪ Finset.univ.image D.pl with hs_def
  have hs : absF z = ∏ w ∈ s, ‖pLoc F w (z : Af F)‖ := by
    rw [habs]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    rw [hs_def, Finset.coe_union]
    exact Or.inl (hfin.mem_toFinset.2 hw)
  have hprod : ∏ v, D.ea v (z : Af F) = ∏ w ∈ s, ∏ v ∈ Finset.univ.filter (fun v => D.pl v = w), D.ea v (z : Af F) :=
    (Finset.prod_fiberwise_of_maps_to (fun v _ => by simp [hs_def]) _).symm
  rw [hs, hprod, Complex.ofReal_prod, ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  by_cases hw : ∃ v, D.pl v = w
  · obtain ⟨v, rfl⟩ := hw
    have e : Finset.univ.filter (fun u => D.pl u = D.pl v) = {v} := by
      ext u; simp [D.inj.eq_iff]
    rw [e, Finset.prod_singleton]
    exact atL D v (hz _)
  · have e : Finset.univ.filter (fun u => D.pl u = w) = ∅ := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hw ⟨u, h⟩
    rw [e, Finset.prod_empty, mul_one]
    exact away ι w (fun h => hw (D.surj w h)) (hz w)
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicOrbitIntegralProof
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc Matrix

namespace UpperTheory.Esk.HyperbolicSetupLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

omit [IsTotallyReal F] in
theorem pow_char {ω : HChar F} (h : IsOfFinOrder ω) : ∃ n, 0 < n ∧ ∀ x, ω.1 x ^ n = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact ⟨n, hn, fun x => by rw [← MonoidHom.pow_apply, e2, MonoidHom.one_apply]⟩

theorem exp_triv {ω : HChar F} (h : IsOfFinOrder ω) (z : TR.Rinf F) : ω.1 (TR.infId F (TR.expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : TR.expU z = TR.expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, TR.expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

def pU : (TR.Rinf F)ˣ ≃* (InfinitePlace F → ℝˣ) := MulEquiv.piUnits

omit [NumberField F] [IsTotallyReal F] in
theorem pU_symm_val (f : InfinitePlace F → ℝˣ) (w : InfinitePlace F) :
    (((pU.symm f : (TR.Rinf F)ˣ) : TR.Rinf F) w) = (f w : ℝ) := rfl

omit [NumberField F] [IsTotallyReal F] in
theorem pU_val (s : (TR.Rinf F)ˣ) (w : InfinitePlace F) : ((pU s w : ℝˣ) : ℝ) = (s : TR.Rinf F) w := rfl


open Classical in
def atV (v : InfinitePlace F) (x : ℝˣ) : (TR.Rinf F)ˣ := pU.symm (Pi.mulSingle v x : InfinitePlace F → ℝˣ)

open Classical in
omit [NumberField F] [IsTotallyReal F] in
theorem atV_val (v w : InfinitePlace F) (x : ℝˣ) :
    ((atV v x : (TR.Rinf F)ˣ) : TR.Rinf F) w = (((Pi.mulSingle v x : InfinitePlace F → ℝˣ) w : ℝˣ) : ℝ) := pU_symm_val _ w

theorem atV_neg (v : InfinitePlace F) :
    TR.infId F (atV v (-1)) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1) := by
  classical
  refine Units.ext (Prod.ext (funext fun w => ?_) ?_)
  · change (1 - TR.infEq F 1 + TR.infEq F ((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F)) w =
      Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w
    rw [map_one, sub_self, zero_add]
    change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      (((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w) = _
    by_cases h : w = v
    · subst h
      have : ((atV w (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w = -1 := by rw [atV_val]; simp
      rw [this]
      simp
    · have : ((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w = 1 := by rw [atV_val, Pi.mulSingle_eq_of_ne h]; simp
      rw [this]
      simp [h]
  · change (1 : Af F) - 0 + 0 = 1
    simp

open Classical in
omit [IsTotallyReal F] in
theorem prod_atV (s : (TR.Rinf F)ˣ) : s = ∏ v, atV v (pU s v) := by
  simp only [atV]
  rw [← map_prod, Finset.univ_prod_mulSingle, MulEquiv.symm_apply_apply]

theorem inf_sign {k : InfinitePlace F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) (hs : Sgn k ω) (u : (TR.Rinf F)ˣ) :
    ((ω.1 (TR.infId F u) : ℂˣ) : ℂ) = ∏ v, ((SignType.sign (u.val v) : ℝ) : ℂ) ^ k v := by
  obtain ⟨s, hss, e⟩ := TR.exists_sign_mul_expU u
  have hsv : ∀ v, (s : TR.Rinf F) v = 1 ∨ (s : TR.Rinf F) v = -1 := fun v => by
    have := congrArg (fun x : (TR.Rinf F)ˣ => (x : TR.Rinf F) v) hss
    simp only [Units.val_mul, Pi.mul_apply, Units.val_one, Pi.one_apply] at this
    exact mul_self_eq_one_iff.1 this
  have hsign : ∀ v, ((SignType.sign (u.val v) : ℝ)) = (s : TR.Rinf F) v := fun v => by
    have hu : u.val v = (s : TR.Rinf F) v * Real.exp (Real.log |u.val v|) := by
      conv_lhs => rw [e]
      simp [TR.expU_val]
    rw [hu, sign_mul, sign_pos (Real.exp_pos _), mul_one]
    rcases hsv v with h | h <;> rw [h] <;> simp
  have hL : ((ω.1 (TR.infId F u) : ℂˣ) : ℂ) = ∏ v, ((ω.1 (TR.infId F (atV v (pU s v))) : ℂˣ) : ℂ) := by
    have h1 : ω.1 (TR.infId F u) = ω.1 (TR.infId F s) := by
      rw [e, map_mul, map_mul, exp_triv hω, mul_one]
    rw [h1]
    conv_lhs => rw [prod_atV s]
    rw [map_prod, map_prod, Units.coe_prod]
  rw [hL]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hsign v]
  have hpv : ((pU s v : ℝˣ) : ℝ) = (s : TR.Rinf F) v := pU_val s v
  rcases hsv v with h | h
  · have : pU s v = 1 := Units.ext (hpv.trans h)
    rw [this, h]
    simp [atV]
  · have : pU s v = -1 := Units.ext (by rw [hpv, h]; simp)
    rw [this, h, atV_neg]
    have := hs v
    rw [HChar.locInf] at this
    simpa using this

theorem pInf_alg (x : F) (v : InfinitePlace F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap F (InfiniteAdeleRing F) x v) = _
  simp

theorem fin_rat {k : InfinitePlace F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) (hs : Sgn k ω) (a : Fˣ) :
    ((ω.1 (finId F (ratU F a)) : ℂˣ) : ℂ) =
      ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v := by
  let φ : F →+* TR.Rinf F := (TR.pInf F).comp (algebraMap F (AdeleRing (𝓞 F) F))
  have e : TR.infId F (Units.map φ.toMonoidHom a) * finId F (ratU F a) =
      Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a := by
    refine Units.ext (TR.ad_ext ?_ ?_)
    · rw [Units.val_mul, map_mul]
      change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F (φ a)) *
        TR.pInf F (1 - GlobalTheory.CuspRep.sFin F 1 + GlobalTheory.CuspRep.sFin F _) = φ a
      have h1 : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
      have h2 : ∀ x, TR.pInf F (GlobalTheory.CuspRep.sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
      simp only [map_add (f := _), map_sub, map_one, h1, h2, sub_self, zero_add, sub_zero, add_zero, mul_one]
    · rw [Units.val_mul, map_mul]
      change ((1 : Af F) - 0 + 0) * ((1 : Af F) - 1 + algebraMap F (Af F) a) = algebraMap F (Af F) a
      simp only [sub_self, zero_add, sub_zero, add_zero, one_mul]
  have h1 : ω.1 (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 := ω.2.2 a
  rw [← e, map_mul] at h1
  have h2 := congrArg Units.val h1
  rw [Units.val_mul, Units.val_one, inf_sign hω hs] at h2
  have h3 : ∀ v, ((Units.map φ.toMonoidHom a : (TR.Rinf F)ˣ) : TR.Rinf F) v =
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F) := fun v => pInf_alg (a : F) v
  simp only [h3] at h2
  have hP : (∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
      ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [← mul_pow]
    have : ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) *
        ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) = 1 := by
      have ha : InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F) ≠ 0 :=
        (map_ne_zero _).2 a.ne_zero
      rcases lt_or_gt_of_ne ha with h | h
      · rw [sign_neg h]; simp
      · rw [sign_pos h]; simp
    rw [this, one_pow]
  calc _ = (∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
        ((∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
          ((ω.1 (finId F (ratU F a)) : ℂˣ) : ℂ)) := by rw [← mul_assoc, hP, one_mul]
    _ = _ := by rw [h2, mul_one]

end UpperTheory.Esk.HyperbolicSetupLemmas

open UpperTheory.Esk.HyperbolicSetupLemmas in
theorem UpperTheory.Esk.hyperbolic_orbit_integral_proof : UpperTheory.Esk.H0b := by
  intro F _ _ _ k c ω χ hω hχ
  refine ⟨?_, fun hs => ⟨?_, inf_sign hω hs⟩⟩
  · obtain ⟨n, hn, hp⟩ := pow_char hω
    refine ⟨n, hn, fun h => ?_⟩
    obtain ⟨⟨k', hk', z, hz⟩, h2⟩ := hχ h
    rw [h2 k' hk' z hz]
    exact hp _
  · intro γ h
    obtain ⟨h1, h2, h3⟩ := center_entries h
    have h0 : γ 0 0 ≠ 0 := fun e => γ.det_ne_zero (by rw [Matrix.det_fin_two, e, h1]; simp)
    set a : Fˣ := Units.mk0 _ h0 with ha
    have hz : jF F γ = zc F (ratU F a) := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      change algebraMap F (Af F) (γ i j) = Matrix.scalar (Fin 2) (algebraMap F (Af F) (γ 0 0)) i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2, ← h3]
    obtain ⟨-, hχ2⟩ := hχ ⟨jF F γ, (mkDat c χ).cenH γ h⟩
    have e := hχ2 1 (one_mem _) (ratU F a) (by rw [one_mul]; exact hz)
    change ((χ ⟨jF F γ, _⟩ : ℂˣ) : ℂ) = ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (γ 0 0)) : ℝ) : ℂ) ^ k v
    rw [e, fin_rat hω hs a]
    rfl
end
end
