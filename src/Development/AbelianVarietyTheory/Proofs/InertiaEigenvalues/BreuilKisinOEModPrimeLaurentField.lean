module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentField
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.OEmod

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

def ψ : bk.S →+* Cb l := (WittVector.constantCoeff (p := l) (R := Cb l)).comp bk.evW

theorem ψ_apply (s : bk.S) : ψ bk s = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by
  simp [ψ, BK.evW, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem ψ_X : ψ bk X = algebraMap (OCb l) (Cb l) bk.flat := by
  rw [ψ_apply, bk.ev_X, WittVector.teichmuller_coeff_zero]

theorem cc_evW_X : WittVector.constantCoeff (bk.evW X) = algebraMap (OCb l) (Cb l) bk.flat := ψ_X bk

theorem cc_l_mul (y : WCb l) : WittVector.constantCoeff ((l : WCb l) * y) = 0 := by
  rw [WittVector.constantCoeff_apply, mul_comm]
  exact WittVector.mul_charP_coeff_zero y

theorem evW_X_eq : bk.evW X = WittVector.teichmuller l (algebraMap (OCb l) (Cb l) bk.flat) := by
  simp [BK.evW, bk.ev_X, inclW, WittVector.map_teichmuller]

theorem l_dvd_of_not_isUnit (a : ℕ) [NeZero a] (x : Wq l a) (h : ¬ IsUnit x) : (l : Wq l a) ∣ x := by
  by_cases h0 : x = 0
  · exact h0 ▸ dvd_zero _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x h0
  cases m with
  | zero => exact absurd (by simpa using WittVector.isUnit_of_coeff_zero_ne_zero b hb) h
  | succ m => exact Dvd.intro _ (by rw [pow_succ', mul_assoc])

theorem exists_unit (s : bk.S) (hs : ψ bk s ≠ 0) :
    ∃ (k : ℕ) (s₁ : bk.S), IsUnit s₁ ∧ ψ bk s = ψ bk X ^ k * ψ bk s₁ := by
  have hex : ∃ i, IsUnit (coeff i s) := by
    by_contra hno
    push_neg at hno
    have hd : ∀ i, (l : Wq l bk.a) ∣ coeff i s := fun i => l_dvd_of_not_isUnit bk.a _ (hno i)
    choose c hc using hd
    have : s = (l : bk.S) * PowerSeries.mk c := by
      ext i
      rw [← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, hc i]
    apply hs
    rw [this, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  classical
  let k := Nat.find hex
  have hk : IsUnit (coeff k s) := Nat.find_spec hex
  have hlt : ∀ i < k, (l : Wq l bk.a) ∣ coeff i s := fun i hi =>
    l_dvd_of_not_isUnit bk.a _ (Nat.find_min hex hi)
  choose! c hc using hlt
  let s₁ : bk.S := PowerSeries.mk fun i => coeff (i + k) s
  let s₂ : bk.S := PowerSeries.mk fun i => if i < k then c i else 0
  have hs₁ : IsUnit s₁ := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]
    exact hk
  have hsplit : s = X ^ k * s₁ + (l : bk.S) * s₂ := by
    ext i
    rw [map_add (f := _), coeff_X_pow_mul', ← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, coeff_mk]
    by_cases hi : i < k
    · rw [if_neg (by omega), if_pos hi, zero_add, hc i hi]
    · rw [if_pos (by omega), if_neg hi, mul_zero, add_zero, Nat.sub_add_cancel (by omega)]
  refine ⟨k, s₁, hs₁, ?_⟩
  conv_lhs => rw [hsplit]
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]

end GlobalTheory.BSP.OEmod

open GlobalTheory.BSP.OEmod in
theorem GlobalTheory.BSP.oe_mod_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S), algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0)) ∧ (∀ s : bk.S, bk.evW s ∈ bk.OE) ∧ IsUnit (bk.evW X) ∧ (∀ w : WCb l, bk.evW X * w ∈ bk.OE → w ∈ bk.OE) ∧ ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), y⁻¹ ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  intro l _ K bk
  have hflat : bk.flat ≠ 0 := (GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk).2.2.2.1
  have hf : algebraMap (OCb l) (Cb l) bk.flat ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hflat
  have hunit : IsUnit (bk.evW X) := by
    rw [evW_X_eq]
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [WittVector.teichmuller_coeff_zero]
    exact hf
  have h1 : ∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S),
      algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by
    intro y
    rw [Subring.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨m, s, z, h⟩ := hw 1
      refine ⟨m, s, ?_⟩
      have := congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) h
      rw [map_mul, map_pow, map_add (f := _), pow_one, cc_l_mul, add_zero, cc_evW_X] at this
      rw [this, ← ψ_apply]
      rfl
    · rintro ⟨m, s, h⟩
      obtain ⟨u, hu⟩ := hunit
      refine ⟨(↑(u⁻¹) : WCb l) ^ m * bk.evW s, fun n => ⟨m, s, 0, ?_⟩, ?_⟩
      · rw [mul_zero, add_zero, ← mul_assoc, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_mul]
      · have hc : WittVector.constantCoeff (bk.evW X) * WittVector.constantCoeff ((↑(u⁻¹) : WCb l)) = 1 := by
          rw [← map_mul, ← hu, Units.mul_inv, map_one]
        rw [cc_evW_X] at hc
        rw [map_mul, map_pow]
        have hs : WittVector.constantCoeff (bk.evW s) = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := ψ_apply bk s
        rw [hs, ← h, ← mul_assoc, ← mul_pow, mul_comm _ (algebraMap (OCb l) (Cb l) bk.flat), hc, one_pow, one_mul]
  refine ⟨h1, fun s n => ⟨0, s, 0, by simp⟩, hunit, fun w hw n => ?_, fun y hy => ?_⟩
  · obtain ⟨m, s, z, h⟩ := hw n
    exact ⟨m + 1, s, z, by rw [pow_succ, mul_assoc, h]⟩
  · by_cases hy0 : y = 0
    · rw [hy0, inv_zero]; exact Subring.zero_mem _
    obtain ⟨m, s, h⟩ := (h1 y).1 hy
    rw [← ψ_apply] at h
    have hs : ψ bk s ≠ 0 := by rw [← h]; exact mul_ne_zero (pow_ne_zero _ hf) hy0
    obtain ⟨k, s₁, ⟨t, rfl⟩, hk⟩ := exists_unit bk s hs
    rw [h1]
    refine ⟨k, ((X : bk.S) ^ m * ↑(t⁻¹) : bk.S), ?_⟩
    rw [← ψ_apply, map_mul, map_pow, ψ_X]
    rw [hk, ψ_X] at h
    have ht : ψ bk ↑t * ψ bk ↑(t⁻¹) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have ht0 : ψ bk ↑t ≠ 0 := left_ne_zero_of_mul_eq_one ht
    have hinv : ψ bk ↑(t⁻¹) = (ψ bk ↑t)⁻¹ := eq_inv_of_mul_eq_one_right ht
    rw [hinv]
    field_simp
    linear_combination -h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentFieldStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S), algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0)) ∧ (∀ s : bk.S, bk.evW s ∈ bk.OE) ∧ IsUnit (bk.evW X) ∧ (∀ w : WCb l, bk.evW X * w ∈ bk.OE → w ∈ bk.OE) ∧ ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), y⁻¹ ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  first | exact @GlobalTheory.BSP.oe_mod_l | exact GlobalTheory.BSP.oe_mod_l | (intros; apply GlobalTheory.BSP.oe_mod_l <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorThreeLayerPropertiesEveryPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachEtaleMapFrobeniusGaloisEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachEtaleMapFrobeniusGaloisEquivariant
noncomputable section

namespace GlobalTheory.NL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem tmul_basis_inj {O R M : Type} [CommRing O] [AddCommGroup R] [Module O R] [AddCommGroup M]
    [Module O M] (e₀ : M) (hs : Submodule.span O {e₀} = ⊤) (hi : ∀ c : O, c • e₀ = 0 → c = 0)
    {r r' : R} (h : r ⊗ₜ[O] e₀ = r' ⊗ₜ[O] e₀) : r = r' := by
  have hb : Function.Bijective (LinearMap.toSpanSingleton O M e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => hi c (by simpa using hc), fun x => ?_⟩
    have hx : x ∈ Submodule.span O {e₀} := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨c, by simpa using hc⟩
  let f := LinearEquiv.ofBijective _ hb
  have h1 : f.symm e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [f]
  have := congrArg (fun z => TensorProduct.rid O R (LinearMap.lTensor R f.symm.toLinearMap z)) h
  simpa [h1] using this

theorem ioLaws_of_injective (E : EtTie W RA RW inclR φR gR πA)
    (hO : Function.Injective (algebraMap O LL)) : IoLaws E := by
  obtain ⟨e, e₀, hs, hj, -⟩ := E.one_e
  have h0 : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hT⟩ := W.one_line
    have hm : u ∈ W.one.L.T := hT ▸ Submodule.mem_span_singleton_self u
    have hx : (⟨u, hm⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀} := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
    have := congrArg Subtype.val hc
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact hu this.symm
  have hi : ∀ c : O, c • e₀ = 0 → c = 0 := by
    intro c hc
    have h1 : algebraMap O LL c • (e₀ : W.one.V) = 0 := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val hc
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact hO (by rw [h2, map_zero])
    · exact absurd h2 h0
  have hx : ∀ x : W.EE, E.jD W.one (x • e) = E.ioE x ⊗ₜ[O] e₀ := by
    intro x
    rw [E.jD_smul, hj, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hact : ∀ g : G, W.one.actT g e₀ = e₀ := fun g => Subtype.ext (W.one_triv g _)
  have hφ : W.φD W.one e = e := by
    apply E.jD_inj
    rw [E.jD_φ, hj]
    simp [TWmap]
  have hγ : ∀ g : G, W.γD W.one (W.resΓ g) e = e := by
    intro g
    apply E.jD_inj
    rw [E.jD_act, hj]
    simp [TWact, hact]
  refine ⟨fun x => ?_, fun g x => ?_⟩
  · apply tmul_basis_inj e₀ hs hi
    have := E.jD_φ W.one (x • e)
    rw [W.φD_smul, hφ, hx, hx] at this
    simpa [TWmap] using this
  · apply tmul_basis_inj e₀ hs hi
    have := E.jD_act W.one g (x • e)
    rw [W.γD_smul, hγ, hx, hx] at this
    simpa [TWact, hact] using this

end Generic

theorem ioLaws : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; IoLaws E := by
  intro D HW F l _ K s LL h
  exact ioLaws_of_injective _ Subtype.val_injective

end GlobalTheory.NL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachEtaleMapFrobeniusGaloisEquivariantStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_etale_map_frobenius_galois_equivariant : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; IoLaws E := by
  first | exact @GlobalTheory.NL.ioLaws | exact GlobalTheory.NL.ioLaws | (intros; apply GlobalTheory.NL.ioLaws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorThreeLayerPropertiesEveryPlace
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.AllLaws

theorem laws : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; Laws (HW l) (F l) h := by
  intro D HW F l _ K s LL h W E
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact ⟨GlobalTheory.T.wachLevelExpansionLaws_of_rootsOfUnity D HW l K s LL h, GlobalTheory.T.wach_etale_map_frobenius_galois_equivariant D HW F l K s LL h,
    GlobalTheory.TrivCrys.isCrys_lat_of_trivial W.one W.one_triv⟩

end GlobalTheory.NL.AllLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorThreeLayerPropertiesEveryPlaceStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_functor_three_layer_properties_every_place : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; Laws (HW l) (F l) h := by
  first | exact @GlobalTheory.NL.AllLaws.laws | exact GlobalTheory.NL.AllLaws.laws | (intros; apply GlobalTheory.NL.AllLaws.laws <;> assumption)
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.SandArb

theorem map_mulLeft {O R M : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M] [Module O M]
    (a : R) (z : R ⊗[O] M) :
    TensorProduct.map (LinearMap.mulLeft O a) LinearMap.id z = a • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add (f := _), smul_add, hx, hy]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) {s : ℕ} (hs : W.s = s)
    (hp : PD.p.Prime) (hL : LevLaws W) (hI : IoLaws E)

set_option maxHeartbeats 1000000 in
theorem of_layers {Zl : Type} [CommRing Zl] (zl : PowerSeries Zl →+* LetA O n) (h1 : IsCrys PD W.one.ρ)
    (hP : ∀ T, @Module.Projective (PowerSeries Zl) _ ↥(W.N T) _ (Module.compHom _ zl))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (w : RA) (c : RW) (hc : c = inclR w)
    (hS : GlobalTheory.HWL.Sand (latOf E hs hp hL hI zl h1 hP) T w) :
    (∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
        TensorProduct.map (LinearMap.mulLeft O c) LinearMap.id (E.jD T x)) ∧
      ∀ t : ↥T.L.T, (c ⊗ₜ[O] t : TW RW T) ∈ Submodule.span O {z : TW RW T | ∃ a : RA, ∃ y ∈ W.N T,
        z = TensorProduct.map (LinearMap.mulLeft O (inclR a)) LinearMap.id (E.jD T y)} := by
  subst hc
  have hN : nOf W T = W.N T := nOf_crys W hT
  have h1' : ∀ x ∈ nOf W T, ∃ y : TW RA T, TWincl inclR T y = inclR w • E.jD T x := hS.1
  have h2' : ∀ t : ↥T.L.T, inclR w • ((1 : RW) ⊗ₜ[O] t : TW RW T) ∈
      Submodule.span O {z : TW RW T | ∃ (a : RA), ∃ y ∈ nOf W T, z = inclR a • E.jD T y} := hS.2
  rw [hN] at h1' h2'
  refine ⟨fun x hx => ?_, fun t => ?_⟩
  · rw [map_mulLeft]; exact h1' x hx
  · have := h2' t
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this
    simp only [map_mulLeft]
    exact this

end Generic

section
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (hL : Laws H F h)

set_option maxHeartbeats 400000 in
theorem sand_layers (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    ∃ m : ℕ, GlobalTheory.HWL.Sand (LatL H F h hL) T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) :=
  apply_layers H F h hL
    (fun _ _ _ _ Mo => ∃ m : ℕ, GlobalTheory.HWL.Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL))
    (fun Γ R I hI E Mo => GlobalTheory.HWL.SandProof.sandwich l P AI K s LL h Γ R I hI E Mo T hT)

theorem incl_pow (a : RA LL) (w : Ainf l) (ha : a = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) (m : ℕ) :
    inclR LL a ^ m = inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (w ^ m)) := by
  rw [ha, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]

end

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem sandwich : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∃ m : ℕ, (∀ x ∈ W.N T, ∃ y : TW (RA LL) T, TWincl (inclR LL) T y = TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL (E.io W.X) ^ m)) LinearMap.id (E.jD T x)) ∧ ∀ t : ↥T.L.T, ((inclR LL (E.io W.X) ^ m) ⊗ₜ[↥(OL LL)] t : TW (RW LL) T) ∈ Submodule.span ↥(OL LL) {z : TW (RW LL) T | ∃ a : RA LL, ∃ y ∈ W.N T, z = TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL a)) LinearMap.id (E.jD T y)} := by
  intro D HW F l _ K s LL h
  have hL : Laws (HW l) (F l) h := GlobalTheory.T.wach_functor_three_layer_properties_every_place D HW F l K s LL h
  have hX := (GlobalTheory.T.wachInclusion_X_Q_frobenius D HW F l K s LL h).1
  refine fun T hT => (sand_layers (HW l) (F l) h hL T hT).imp fun m hm => ?_
  exact of_layers ((F l).E K s LL h).tie ((HW l).W_s K s LL h) (p_prime (D.loc l) K) hL.lev hL.io _ hL.one
    ((HW l).W_proj K s LL h) T hT _ _ (incl_pow _ _ hX m) hm

end GlobalTheory.NL.SandArb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.Prism

theorem semiBC_basis (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M]
    [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (h : SemiBC u)
    (ι : Type) (e : Module.Basis ι A M) : ∃ b : Module.Basis ι B N, ∀ i, b i = u (e i) := by
  classical
  let g : (ι →₀ B) →ₗ[B] N := Finsupp.linearCombination B (fun i => u (e i))
  let v : M →ₛₗ[f] (ι →₀ B) :=
    { toFun := fun x => Finsupp.mapRange f f.map_zero (e.repr x)
      map_add' := fun x y => by
        ext i; simp
      map_smul' := fun a x => by
        ext i; simp }
  obtain ⟨w, hw, -⟩ := h (ι →₀ B) v
  have key : ∀ x : M, g (v x) = u x := by
    intro x
    conv_rhs => rw [← e.linearCombination_repr x]
    simp only [g, v, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun i => by simp), map_finsuppSum]
    refine Finsupp.sum_congr (fun i _ => ?_)
    simp
  have h1 : w.comp g = LinearMap.id := by
    ext i
    simp [g, hw, v]
  have h2 : g.comp w = LinearMap.id := by
    obtain ⟨w0, -, huniq⟩ := h N u
    have a1 := huniq (g.comp w) (fun x => by simp [hw, key])
    have a2 := huniq LinearMap.id (fun x => rfl)
    rw [a1, a2]
  let E : N ≃ₗ[B] (ι →₀ B) := LinearEquiv.ofLinear w g h1 h2
  refine ⟨Module.Basis.ofRepr E, fun i => ?_⟩
  simp [Module.Basis.ofRepr, E, g]

end GlobalTheory.Prism
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N), SemiBC u → ∀ (ι : Type) (e : Module.Basis ι A M), ∃ b : Module.Basis ι B N, ∀ i, b i = u (e i) := by
  first | exact @GlobalTheory.Prism.semiBC_basis | exact GlobalTheory.Prism.semiBC_basis | (intros; apply GlobalTheory.Prism.semiBC_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeIffIsBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeIffIsBaseChange
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem _root_.GlobalTheory.BSP.semiBC_iff_isBaseChange (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type)
    [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] (u : M →ₛₗ[algebraMap A B] N) (u' : M →ₗ[A] N)
    (h : ∀ x, u' x = u x) : _root_.GlobalTheory.Prism.SemiBC u ↔ IsBaseChange B u' := by
  constructor
  · intro hu
    refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g => ?_
    letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup B
    let v : M →ₛₗ[algebraMap A B] Q :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun a x => by simp [algebraMap_smul] }
    obtain ⟨w, hw, hw'⟩ := hu Q v
    refine ⟨w, ?_, fun w₂ hw₂ => hw' w₂ fun x => ?_⟩
    · ext x
      simp [h, hw x, v]
    · rw [← h]
      exact LinearMap.congr_fun hw₂ x
  · intro hb Q _ _ v
    letI : Module A Q := Module.compHom Q (algebraMap A B)
    haveI : IsScalarTower A B Q :=
      ⟨fun a b q => by
        show (a • b) • q = algebraMap A B a • b • q
        rw [Algebra.smul_def, mul_smul]⟩
    let g : M →ₗ[A] Q :=
      { toFun := v
        map_add' := v.map_add
        map_smul' := fun a x => by
          rw [v.map_smulₛₗ]
          rfl }
    refine ⟨hb.lift g, fun x => ?_, fun w hw => hb.algHom_ext _ _ fun x => ?_⟩
    · rw [← h, hb.lift_eq]
      rfl
    · rw [hb.lift_eq, h, hw]
      rfl

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeIffIsBaseChangeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] (u : M →ₛₗ[algebraMap A B] N) (u' : M →ₗ[A] N), (∀ x, u' x = u x) → (SemiBC u ↔ IsBaseChange B u') := by
  first | exact @GlobalTheory.BSP.semiBC_iff_isBaseChange | exact GlobalTheory.BSP.semiBC_iff_isBaseChange | (intros; apply GlobalTheory.BSP.semiBC_iff_isBaseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSection
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSection
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PendOf.PrTypeProof

theorem typeSum_indep (D : D7) (i : D.nd.Loc) : iSupIndep (typeSum D i) := by
  intro o
  have hd : Disjoint {P | D.naut.ptV i P = o} {P | D.naut.ptV i P ≠ o} :=
    Set.disjoint_left.2 fun P h h' => h' h
  refine ((D.naut.typeV_indep i).disjoint_biSup_biSup hd).mono_right ?_
  refine iSup₂_le fun o' ho' => iSup₂_le fun P hP => ?_
  exact le_biSup (D.naut.typeV i) (show P ∈ {P | D.naut.ptV i P ≠ o} from fun e => ho' (hP.symm.trans e))

theorem typeV_le_typeSum (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) :
    D.naut.typeV i P ≤ typeSum D i (D.naut.ptV i P) :=
  le_biSup (D.naut.typeV i) (show P ∈ {Q | D.naut.ptV i Q = D.naut.ptV i P} from rfl)

theorem main : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → PrType D := by
  intro D hS i PI x hx
  classical
  let s := (hS i).some
  set v := D.nd.prMt i x with hvdef
  have hvtop : v ∈ ⨆ y, heckeEig (D.nd.T i) (D.nd.act i) y := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ v).1 hvtop
  have hΦv : s.Φ v = ∑ y ∈ f.support, s.Φ (f y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, Finsupp.sum, map_sum]
  have hn := s.split x
  have hind := typeSum_indep D i
  have hjx : D.what₂.jMt _ _ x ∈ typeSum D i (D.naut.ptV i PI) := typeV_le_typeSum D i PI hx
  have key : ∀ y, some y ≠ D.naut.ptV i PI → f y = 0 := by
    intro y hy
    by_cases hs : y ∈ f.support
    · have e : s.Φ (f y) = (D.what₂.jMt _ _ x - (D.what₂.jMt _ _ x - s.Φ v)) -
          ∑ y' ∈ f.support.erase y, s.Φ (f y') := by
        rw [sub_sub_cancel, hΦv, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : s.Φ (f y) ∈ ⨆ (o) (_ : o ≠ some y), typeSum D i o := by
        rw [e]
        refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) (Submodule.sum_mem _ fun y' hy' => ?_)
        · exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (Ne.symm hy) hjx)
        · exact Submodule.mem_iSup_of_mem none (Submodule.mem_iSup_of_mem (by simp) hn)
        · refine Submodule.mem_iSup_of_mem (some y') (Submodule.mem_iSup_of_mem ?_ (s.eig y' _ (hf y')))
          exact fun e' => Finset.ne_of_mem_erase hy' (Option.some_injective _ e')
      have h0 : s.Φ (f y) = 0 := (Submodule.disjoint_def.1 (hind (some y))) _ (s.eig y _ (hf y)) m2
      exact s.inj (h0.trans (map_zero s.Φ).symm)
    · exact Finsupp.notMem_support_iff.1 hs
  refine ⟨fun p hp => ?_, fun hp => ?_⟩
  · rw [← hsum, Finsupp.sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hyp : y = p
    · subst hyp; exact hf y
    · rw [key y (by rw [hp]; exact fun e => hyp (Option.some_injective _ e))]
      exact Submodule.zero_mem _
  · rw [← hsum, Finsupp.sum]
    exact Finset.sum_eq_zero fun y _ => key y (by rw [hp]; simp)

end GlobalTheory.PendOf.PrTypeProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSectionStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeSpaceProjectionEigen_of_localisedFormsSection : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → PrType D := by
  first | exact @GlobalTheory.PendOf.PrTypeProof.main | exact GlobalTheory.PendOf.PrTypeProof.main | (intros; apply GlobalTheory.PendOf.PrTypeProof.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameCocyclesLinked
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameCocyclesLinked
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.LinkCocycle

theorem dvd_of_inclW {l : ℕ} [Fact l.Prime] (n : ℕ) : ∀ (a : Ainf l) (w : WCb l),
    inclW l a = (l : WCb l) ^ n * w → (l : Ainf l) ^ n ∣ a := by
  induction n with
  | zero => intro a w _; exact ⟨a, by simp⟩
  | succ n ih =>
    intro a w h
    obtain ⟨a₁, ha₁⟩ := GlobalTheory.HWL.TensorWitt.ainf_saturated_in_tiltWitt_prime a ((l : WCb l) ^ n * w) (by rw [h]; ring)
    obtain ⟨c, hc⟩ := ih a₁ w ha₁
    have h1 : a = (l : Ainf l) * a₁ := GlobalTheory.HWL.TensorWitt.inclW_injective (by
      rw [map_mul, map_natCast, ha₁, h]; ring)
    exact ⟨c, by rw [h1, hc]; ring⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N d ρ) (F' : Frame bk N' d' ρ') (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ (g : ↥(GK K)) i j, (l : Ainf l) ^ n ∣ (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g) i j := by
  intro l _ K bk N N' d d' n ρ ρ' F F' Pi R hPi hR g i j
  classical
  choose M hM using hPi g
  choose D hD using hR
  set c : WCb l := (l : WCb l) ^ n with hc
  set σ : WCb l →+* WCb l := ((galW l (g : GQ l) : WCb l ≃ₐ[ℤ_[l]] WCb l) : WCb l →+* WCb l) with hσ
  set T := F.T
  set T' := F'.T
  set P := zW Pi
  set A := zW (ρ g)
  set A' := zW (ρ' g)
  set Rw := (R.map bk.ev).map (inclW l)
  set Rgw := ((R.map bk.ev).map (Per.σA (g : GQ l))).map (inclW l)
  set E := (F.ε g).map (inclW l)
  set E' := (F'.ε g).map (inclW l)
  set Ds : Matrix (Fin d) (Fin d') (WCb l) := Matrix.of D
  set Mw : Matrix (Fin d) (Fin d') (WCb l) := zW (Matrix.of M)
  have e1 : A * T.map σ = T * E := F.gal g
  have e2 : A' * T'.map σ = T' * E' := F'.gal g
  have e3 : P * T' - T * Rw = c • Ds := Matrix.ext fun i j => by
    simpa [Ds, Rw, BK.evW, Matrix.map_map] using hD i j
  have e4 : P * T'.map σ - T.map σ * Rgw = c • Ds.map σ := by
    have hP : P.map σ = P := Matrix.ext fun i j => by simp [P, zW, σ]
    have hRg : Rw.map σ = Rgw := Matrix.ext fun i j => by simp [Rw, Rgw, σ, galW_inclW]
    have : (P * T' - T * Rw).map σ = (c • Ds).map σ := by rw [e3]
    rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul] at this
    rw [hP, hRg] at this
    rw [this]; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hc, map_pow, map_natCast]
  have e5 : P * A' - A * P = c • Mw := by
    have hM' : Pi * ρ' g - ρ g * Pi = ((l : ℤ_[l]) ^ n) • Matrix.of M := Matrix.ext fun i j => by simpa using hM i j
    have : (Pi * ρ' g - ρ g * Pi).map (algebraMap ℤ_[l] (WCb l)) = (((l : ℤ_[l]) ^ n) • Matrix.of M).map (algebraMap ℤ_[l] (WCb l)) := by rw [hM']
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul] at this
    rw [this]; ext i j; simp [Mw, zW, c]
  have key : T * (E * Rgw - Rw * E') = (c • Ds) * E' - (c • Mw) * T'.map σ - A * (c • Ds.map σ) := by
    rw [← e3, ← e4, ← e5]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T E, ← e1, ← e2]
    simp only [Matrix.mul_assoc]
    abel
  have key2 : T * (E * Rgw - Rw * E') = c • (Ds * E' - Mw * T'.map σ - A * Ds.map σ) := by
    rw [key, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_sub]
  have hT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp F.unit)
  have hX : E * Rgw - Rw * E' = c • (T⁻¹ * (Ds * E' - Mw * T'.map σ - A * Ds.map σ)) := by
    rw [← Matrix.mul_smul, ← key2, ← Matrix.mul_assoc, hT, Matrix.one_mul]
  have hY : (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g).map (inclW l) =
      E * Rgw - Rw * E' := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]
  refine dvd_of_inclW n _ ((T⁻¹ * (Ds * E' - Mw * T'.map σ - A * Ds.map σ)) i j) ?_
  have := congrFun (congrFun (hY.trans hX) i) j
  simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hc] using this
end GlobalTheory.BKLim.LinkCocycle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameCocyclesLinkedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N d ρ) (F' : Frame bk N' d' ρ') (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ (g : ↥(GK K)) i j, (l : Ainf l) ^ n ∣ (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g) i j := by
  first | exact @GlobalTheory.BKLim.LinkCocycle.main | exact GlobalTheory.BKLim.LinkCocycle.main | (intros; apply GlobalTheory.BKLim.LinkCocycle.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsApproxRootEisensteinAwayPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsApproxRootEisensteinAwayPrime
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem eval_derivative_scaleRoots_mul {R : Type*} [CommRing R] (P : Polynomial R) (s x : R) :
    (Polynomial.derivative (P.scaleRoots s)).eval (s * x) =
      s ^ (P.natDegree - 1) * (Polynomial.derivative P).eval x := by
  have h1 : (Polynomial.derivative (P.scaleRoots s)).natDegree < P.natDegree - 1 + 1 := by
    have := Polynomial.natDegree_derivative_le (P.scaleRoots s)
    rw [Polynomial.natDegree_scaleRoots] at this
    omega
  have h2 : (Polynomial.derivative P).natDegree < P.natDegree - 1 + 1 := by
    have := Polynomial.natDegree_derivative_le P
    omega
  rw [Polynomial.eval_eq_sum_range' h1, Polynomial.eval_eq_sum_range' h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ P.natDegree - 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative, Polynomial.coeff_scaleRoots]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi'
  have h3 : P.natDegree - (i + 1) = k := by omega
  rw [h3, hk]
  ring

theorem exists_approx_root_scaleRoots {R : Type*} [CommRing R] (P : Polynomial R) (hP : 0 < P.natDegree)
    (t x b : R) (c : ℕ) (hb : P.eval x ∣ b * (Polynomial.derivative P).eval x - t ^ c) (n : ℕ) :
    ∃ (m : ℕ) (q : R), P.eval x ∣ q - t ^ m * x ∧ P.eval x ^ (n + 1) ∣ (P.scaleRoots (t ^ m)).eval q := by
  induction n with
  | zero => exact ⟨0, x, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨m, q, ⟨z, hz⟩, ⟨w, hw⟩⟩ := ih
    obtain ⟨e, he⟩ : ∃ e, P.natDegree = e + 1 := ⟨P.natDegree - 1, by omega⟩
    obtain ⟨v, hv⟩ := hb
    set E := P.eval x with hE
    set s := t ^ m with hs
    set r := t ^ c * s ^ e with hr
    have hsr : t ^ (m + (c + m * e)) = s * r := by rw [hr, hs]; ring
    set h := -(b * (P.scaleRoots s).eval q) with hh
    refine ⟨m + (c + m * e), r * q + h, ?_, ?_⟩
    · rw [hsr]
      refine ⟨r * z - b * E ^ n * w, ?_⟩
      rw [hh, hw]
      linear_combination r * hz
    · rw [hsr]
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion (P.scaleRoots (s * r)) (r * q) h
      have h0 : (P.scaleRoots (s * r)).eval (r * q) = r ^ (e + 1) * (P.scaleRoots s).eval q := by
        rw [Polynomial.scaleRoots_mul, Polynomial.scaleRoots_eval_mul, Polynomial.natDegree_scaleRoots, he]
      have h1 := eval_derivative_scaleRoots_mul P (s * r) x
      rw [he, Nat.add_sub_cancel] at h1
      obtain ⟨y, hy⟩ := Polynomial.sub_dvd_eval_sub (r * q) (s * r * x)
        (Polynomial.derivative (P.scaleRoots (s * r)))
      have h2 : (Polynomial.derivative (P.scaleRoots (s * r))).eval (r * q) =
          (s * r) ^ e * (Polynomial.derivative P).eval x + E * (r * z * y) := by
        rw [← h1]
        linear_combination hy + r * y * hz
      rw [hk, h0, h2, hh, hw]
      refine ⟨-((s * r) ^ e * v * w) - b * w * (r * z * y) + k * b ^ 2 * w ^ 2 * E ^ n, ?_⟩
      have h3 : r ^ (e + 1) = (s * r) ^ e * t ^ c := by
        rw [pow_succ, mul_pow]; nth_rewrite 2 [hr]; ring
      rw [h3]
      linear_combination (-((s * r) ^ e * E ^ (n + 1) * w)) * hv

theorem BK.exists_approx_root : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n : ℕ),
    ∃ (m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X ∧
      bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) := by
  intro l _ K bk n
  obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
  have hcoe : ∀ p : Polynomial (Wq l bk.a),
      (p.map (PowerSeries.C : Wq l bk.a →+* bk.S)).eval (X : bk.S) = (p : bk.S) := fun p => by
    rw [Polynomial.eval_map, Polynomial.eval₂_C_X_eq_coe]
  have hdeg : (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S)).natDegree = bk.Ep.natDegree :=
    bk.monic.natDegree_map _
  have hb : (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S)).eval (X : bk.S) ∣
      (b : bk.S) * (Polynomial.derivative (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S))).eval X -
        (l : bk.S) ^ c := by
    rw [Polynomial.derivative_map, hcoe, hcoe]
    have h := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hab
    beta_reduce at h
    rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, map_pow, map_natCast] at h
    exact ⟨-(a : bk.S), by linear_combination h⟩
  obtain ⟨m, q, h1, h2⟩ := exists_approx_root_scaleRoots _ (hdeg ▸ bk.deg_pos) (l : bk.S) X b c hb n
  rw [hcoe] at h1 h2
  refine ⟨m, q, h1, (pow_dvd_pow _ n.le_succ).trans ?_⟩
  rw [← Polynomial.eval_map, Polynomial.map_scaleRoots _ _ _ (by rw [bk.monic.leadingCoeff, map_one]; exact one_ne_zero),
    map_pow, map_natCast]
  exact h2

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsApproxRootEisensteinAwayPrimeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_root_eisenstein_away_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n : ℕ), ∃ (m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X ∧ bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) := by
  first | exact @GlobalTheory.BSP.BK.exists_approx_root | exact GlobalTheory.BSP.BK.exists_approx_root | (intros; apply GlobalTheory.BSP.BK.exists_approx_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosed
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfSat

section Coeff

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

theorem coeff_pow_mul_add (r : ℕ) (w : WittVector p R) (i : ℕ) :
    (((p : WittVector p R) ^ r * w).coeff (i + r)) = (w.coeff i) ^ (p ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : (p : WittVector p R) ^ (r + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ r * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h, show i + (r + 1) = (i + r).succ by omega, WittVector.verschiebung_coeff_succ,
      WittVector.coeff_frobenius_charP, ih, ← pow_mul, pow_succ]

theorem coeff_pow_mul_lt (n : ℕ) (w : WittVector p R) :
    ∀ j, j < n → ((p : WittVector p R) ^ n * w).coeff j = 0 := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    have h : (p : WittVector p R) ^ (n + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ n * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ j =>
      rw [WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP, ih j (by omega),
        zero_pow hp.out.ne_zero]

theorem coeff_eq_of_dvd {n : ℕ} {u v : WittVector p R} (h : (p : WittVector p R) ^ n ∣ u - v)
    (j : ℕ) (hj : j < n) : u.coeff j = v.coeff j := by
  obtain ⟨w, hw⟩ := h
  have hz : WittVector.truncate n (u - v) = 0 := by
    ext k
    rw [WittVector.coeff_truncate, hw, coeff_pow_mul_lt n w k k.2]
    simp
  have ht : WittVector.truncate n u = WittVector.truncate n v := by
    rw [map_sub, sub_eq_zero] at hz; exact hz
  have := congrArg (TruncatedWittVector.coeff (⟨j, hj⟩ : Fin n)) ht
  simpa [WittVector.coeff_truncate] using this

end Coeff

variable (l : ℕ) [Fact l.Prime]

theorem exists_of_pow_eq (r : ℕ) (d : Cb l) (b : OCb l)
    (h : d ^ (l ^ r) = algebraMap (OCb l) (Cb l) b) : ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = d := by
  refine ⟨(iterateFrobeniusEquiv (OCb l) l r).symm b, ?_⟩
  apply iterateFrobenius_inj (Cb l) l r
  rw [iterateFrobenius_def, iterateFrobenius_def, h, ← map_pow]
  congr 1
  have := (iterateFrobeniusEquiv (OCb l) l r).apply_symm_apply b
  rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at this

theorem mem_range_of_pow_mul (r : ℕ) (y : WCb l)
    (hy : ∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * y - inclW l a) :
    ∃ a : Ainf l, y = inclW l a := by
  have hc : ∀ i, ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = y.coeff i := by
    intro i
    obtain ⟨a, ha⟩ := hy (i + r + 1)
    have he := coeff_eq_of_dvd ha (i + r) (by omega)
    rw [coeff_pow_mul_add] at he
    exact exists_of_pow_eq l r _ _ (by rw [he]; exact WittVector.map_coeff _ _ _)
  choose c hc using hc
  refine ⟨WittVector.mk l c, ?_⟩
  ext i
  rw [show inclW l (WittVector.mk l c) = WittVector.map (algebraMap (OCb l) (Cb l)) (WittVector.mk l c)
    from rfl, WittVector.map_coeff]
  exact (hc i).symm

theorem mem_ideal_of_saturated : ∀ (l : ℕ) [Fact l.Prime] (ι : Ainf l), IsUnit (inclW l ι) →
    ∀ (r : ℕ) (x : WCb l), (∀ n : ℕ, ∃ a : Ainf l,
      (l : WCb l) ^ n ∣ (l : WCb l) ^ r * x - inclW l (ι * a)) →
    ∃ a : Ainf l, x = inclW l (ι * a) := by
  intro l _ ι hu r x hx
  obtain ⟨u, hu⟩ := hu
  obtain ⟨a, ha⟩ := mem_range_of_pow_mul l r (↑u⁻¹ * x) (by
    intro n
    obtain ⟨a, w, hw⟩ := hx n
    refine ⟨a, ↑u⁻¹ * w, ?_⟩
    have : (l : WCb l) ^ r * (↑u⁻¹ * x) - inclW l a
        = ↑u⁻¹ * ((l : WCb l) ^ r * x - inclW l (ι * a)) := by
      rw [map_mul, ← hu, mul_sub]
      rw [← mul_assoc (↑u⁻¹ : WCb l) (↑u) _, Units.inv_mul, one_mul]
      ring
    rw [this, hw]; ring)
  refine ⟨a, ?_⟩
  rw [map_mul, ← ha, ← hu, ← mul_assoc, Units.mul_inv, one_mul]

end GlobalTheory.AinfSat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_principal_ideal_saturated_closed : ∀ (l : ℕ) [Fact l.Prime] (ι : Ainf l), IsUnit (inclW l ι) → ∀ (r : ℕ) (x : WCb l), (∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * x - inclW l (ι * a)) → ∃ a : Ainf l, x = inclW l (ι * a) := by
  first | exact @GlobalTheory.AinfSat.mem_ideal_of_saturated | exact GlobalTheory.AinfSat.mem_ideal_of_saturated | (intros; apply GlobalTheory.AinfSat.mem_ideal_of_saturated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLattices
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.LatExact

theorem W_exact : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) (O := ↥(OL LL)) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧ ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π hses
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses
  exact ⟨h1, h3, fun x => h2 x⟩

end GlobalTheory.LatExact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLatticesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFunctor_exact_on_lattices : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) (O := ↥(OL LL)) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧ ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x := by
  first | exact @GlobalTheory.LatExact.W_exact | exact GlobalTheory.LatExact.W_exact | (intros; apply GlobalTheory.LatExact.W_exact <;> assumption)
end
end
