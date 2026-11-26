module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNOfMapMemSaturated

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LayersOfExists
noncomputable section

namespace GlobalTheory.HWL.Back

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
open scoped Classical

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {W : LocWach PD LL O v n} {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA}
    {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}


theorem tmul_cancel (hO : Function.Injective (algebraMap O LL)) (W : LocWach PD LL O v n)
    (e₀ : ↥W.one.L.T) (h₀ : Submodule.span O {e₀} = ⊤) {r r' : RW}
    (h : (r ⊗ₜ[O] e₀ : TW RW W.one) = r' ⊗ₜ[O] e₀) : r = r' := by
  obtain ⟨e, he, hT⟩ := W.one_line
  have hne : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    have heT : e ∈ W.one.L.T := hT ▸ Submodule.mem_span_singleton_self e
    have : (⟨e, heT⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀} := h₀ ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
    apply he
    have := congrArg Subtype.val ha
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  have hbij : Function.Bijective (LinearMap.toSpanSingleton O ↥W.one.L.T e₀) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      have := congrArg Subtype.val ha
      simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, Submodule.coe_zero] at this
      rw [← algebraMap_smul LL a, smul_eq_zero] at this
      exact hO (by rw [this.resolve_right hne, map_zero])
    · rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, h₀]
  let ψ := (LinearEquiv.ofBijective _ hbij).symm
  have hψ : ψ e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp
  have := congrArg (fun x => TensorProduct.rid O RW (LinearMap.lTensor RW ψ.toLinearMap x)) h
  simpa [hψ] using this

theorem ioE_φ (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (a : W.EE) : E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h₀, he, -⟩ := E.one_e
  have h1 := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, he] at h1
  simp only [TWmap, smul_tmul', smul_eq_mul, mul_one, map_tmul, AlgHom.toLinearMap_apply, map_one,
    LinearMap.id_apply] at h1
  exact tmul_cancel hO W e₀ h₀ h1

theorem ioE_γ (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h₀, he, -⟩ := E.one_e
  have h1 := E.jD_act W.one g (a • e)
  have h2 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, he] at h1
  simp only [TWact, smul_tmul', smul_eq_mul, mul_one, map_tmul, AlgHom.toLinearMap_apply, map_one,
    h2] at h1
  exact tmul_cancel hO W e₀ h₀ h1





end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime]


end Concrete

end GlobalTheory.HWL.Back
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevLawsOfEvLaw
noncomputable section

namespace GlobalTheory.NL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

section Generic

variable {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
    [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] {v : AddValuation L (WithTop ℚ)}
    {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR}
    [Algebra Qp L] [TopologicalSpace L] {n : ℕ}

def levOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
  (W.lev i ζ).comp (Pi.constAlgHom O (ZMod n) O⟦X⟧)


omit [CharZero L] [Algebra ℚ L] in
theorem lev_eq_levOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) (f : LetA O n) :
    W.lev i ζ f = levOne W i ζ (f i) := by
  have h := W.lev_letter i ζ (f - Pi.constAlgHom O (ZMod n) O⟦X⟧ (f i)) (sub_self (f i))
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem levOne_X (W : LocWach PD L O v n) (i : ZMod n) {ζ : L} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    levOne W i ζ X = C ζ * exp L - 1 := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i ζ h
  have hE : E = exp L := PowerSeries.exp_unique_of_derivative_eq_self h1 h0
  rw [← hE, ← h2, add_sub_cancel_left]
  rfl

theorem levLaws_of_evLaw [IsDomain O] (hl0 : (l : O) ≠ 0) (hlu : ¬ IsUnit (l : O)) (W : LocWach PD L O v n)
    (hp : PD.p = l) (c : W.Gam → ℤ_[l]) (hc : ∀ g, algebraMap ℤ_[l] O (c g) = (W.χΓ g : O))
    (hv : ∀ (c : ℤ_[l]) (j a : ℕ), (j : WithTop ℚ) ≤ v (algebraMap ℤ_[l] L c - (a : L)) →
      (l : ℤ_[l]) ^ j ∣ c - a) (H : Ser.EvLaw l (O := O) v inferInstance) : LevLaws W := by
  have hc' : ∀ g, algebraMap O L (W.χΓ g : O) = algebraMap ℤ_[l] L (c g) :=
    fun g => by rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hpr : PD.p.Prime := hp ▸ (Fact.out : l.Prime)
  have hφX : W.φ₀ X = (1 + X) ^ l - 1 := by rw [W.φ₀_X, W.q₀_def, hp]
  have hφ : W.φ₀ = GlobalTheory.Fon.phi0 l O :=
    GlobalTheory.Cyc.algHom_ext_of_constantCoeff_zero _ _ (by rw [hφX, GlobalTheory.Fon.cyclotomicFrobeniusPowerSeries_X]) (by rw [hφX]; simp)
  have hγ : ∀ g, W.γ₀ g = GlobalTheory.Fon.gam O (c g) := fun g =>
    GlobalTheory.Cyc.algHom_ext_of_constantCoeff_zero _ _
      (GlobalTheory.Cyc.eq_of_commute_pow l hl0 hlu W.φ₀ _ _ hφX (W.γ₀_comm g _) (by rw [hφ]; exact GlobalTheory.Fon.cyclotomicFrobenius_comm_gammaAction _ _ _)
        (W.γ₀_X g).1 (GlobalTheory.Fon.constantCoeff_gam_X _ _)
        (by rw [(W.γ₀_X g).2, GlobalTheory.Fon.coeff_one_gam_X, hc])) (W.γ₀_X g).1
  constructor
  · rintro g i ζ _ j a h hj rfl f
    rw [hc'] at hj ⊢
    rw [lev_eq_levOne, lev_eq_levOne]
    change levOne W i ζ (W.γ₀ g (f i)) = _
    rw [hγ]
    exact Ser.ev_gam H (hp ▸ h.pow_eq_one) _ (hv _ j a hj) (levOne_X W i ⟨j, h⟩)
      (levOne_X W i (root_pow hpr ⟨j, h⟩ a)) (f i)
  · rintro i ζ ⟨j, h⟩ f
    rw [lev_eq_levOne, lev_eq_levOne]
    change levOne W i ζ (W.φ₀ (f (i - 1))) = _
    have := Ser.ev_gam H (hp ▸ h.pow_eq_one) (l : ℤ_[l]) (a := l) (by simp) (levOne_X W i ⟨j, h⟩)
      (levOne_X W (i - 1) (root_pow hpr ⟨j, h⟩ l)) (f (i - 1))
    rw [GlobalTheory.Fon.gam_l, map_natCast] at this
    rw [hφ, hp]
    exact this

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem levLaws : LevLaws (H.W K s LL h) := by
  obtain ⟨_, -, h0, hu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨c, hc⟩ := Ser.exists_padic_char (GamL H h)
  refine levLaws_of_evLaw h0 hu _ (P.PD_p K) (fun g => (c g : ℤ_[l])) hc (Ser.dvd_of_le_v P) ?_
  convert Ser.evLaw_integers P LL using 1
  exact Algebra.algebra_ext _ _ fun r => PowerSeries.algebraMap_apply

theorem ioLaws_tie : IoLaws (F.E K s LL h).tie := by
  set_option synthInstance.maxHeartbeats 100000 in
    exact ⟨GlobalTheory.HWL.Back.ioE_φ (O := ↥(OL LL)) Subtype.val_injective _,
    GlobalTheory.HWL.Back.ioE_γ (O := ↥(OL LL)) Subtype.val_injective _⟩

theorem one_crys : IsCrys (P.PD K) (H.W K s LL h).one.ρ :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  GlobalTheory.TrivCrys.isCrys_lat_of_trivial _ (H.W K s LL h).one_triv

end Concrete

theorem laws : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL), Laws H F h :=
  fun H F _ _ _ h => ⟨levLaws H h, ioLaws_tie H F h, one_crys H h⟩

end GlobalTheory.NL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlaces
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.NygaardFrobeniusPower

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem map_smulA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem isUnit_φA_pow (k : ℕ) (a : LetA O n) (ha : IsUnit (algebraMap (LetA O n) W.EE a)) :
    IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) a)) := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply]
    have : algebraMap (LetA O n) W.EE (W.φA ((W.φA ^ k) a)) =
        W.φE (algebraMap (LetA O n) W.EE ((W.φA ^ k) a)) := (W.φE_ext _).symm
    rw [this]
    exact ih.map W.φE

theorem isUnit_X : IsUnit (algebraMap (LetA O n) W.EE W.X) :=
  isUnit_φA_pow W (W.s - 1) letπ W.EE_π

theorem Q_pow_φ_mem [NeZero n] (T : LocLat G Qp LL O) (M : ZMod n → ℕ)
    (hM : ∀ i, ∀ x ∈ W.Nl T (i - 1), W.Q ^ (M i) • W.φD T x ∈ W.N T)
    (x : W.DD T) (hx : x ∈ W.N T) : W.Q ^ (mx M) • W.φD T x ∈ W.N T := by
  have hx' : x = ∑ i : ZMod n, (letE i : LetA O n) • x := by
    rw [← Finset.sum_smul, sum_letE, one_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hle : M (i + 1) ≤ mx M := le_ciSup (Set.finite_range M).bddAbove (i + 1)
  have hmem : (letE i : LetA O n) • x ∈ W.Nl T (i + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨x, hx, by simp⟩
  have h1 := hM (i + 1) _ hmem
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ h1

theorem core [NeZero n] (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (M : ZMod n → ℕ)
    (hex : ∀ y, W.map π y = 0 → ∃ z, W.map ι z = y)
    (hsat : ∀ z : W.DD T, W.map ι z ∈ W.N Tp → z ∈ W.N T)
    (hφ : ∀ i, ∀ x ∈ W.Nl Tp (i - 1), W.Q ^ (M i) • W.φD Tp x ∈ W.N Tp)
    (hγ : ∀ x ∈ W.N Tp, W.γ Tp x - x ∈ (aN W) Tp W.X)
    (e : W.DD W.one) (he : W.φD W.one e = e) (hge : ∀ g, W.γD W.one g e = e)
    (x : W.DD Tp) (hx : x ∈ W.N Tp) (c : O) (hc : W.map π x = c • e) :
    (∃ y ∈ (invN W) T (W.Q ^ mx M), W.map ι y = W.φD Tp x - x) ∧
      (∃ z ∈ (aN W) T W.X, W.map ι z = W.γ Tp x - x) := by
  constructor
  · have h0 : W.map π (W.φD Tp x - x) = 0 := by
      rw [map_sub, W.map_φ, hc, (W.φD W.one).map_smul, he, sub_self]
    obtain ⟨y, hy⟩ := hex _ h0
    refine ⟨y, hsat _ ?_, hy⟩
    change W.map ι (W.Q ^ mx M • y) ∈ W.N Tp
    rw [map_smulA, hy, smul_sub]
    exact Submodule.sub_mem _ (Q_pow_φ_mem W Tp M hφ x hx) (Submodule.smul_mem _ _ hx)
  · obtain ⟨w, hw, hw'⟩ := hγ x hx
    change W.X • w = W.γ Tp x - x at hw'
    have hX0 : W.X • W.map π w = 0 := by
      rw [← map_smulA, hw', map_sub, LocWach.γ, W.map_γ, hc, (W.γD W.one W.gam).map_smul, hge,
        sub_self]
    have h0 : W.map π w = 0 := by
      obtain ⟨u, hu⟩ := isUnit_X W
      rw [← algebraMap_smul W.EE W.X, ← hu] at hX0
      have := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) hX0
      simpa [smul_smul] using this
    obtain ⟨z, hz⟩ := hex _ h0
    have hzN : z ∈ W.N T := hsat z (hz ▸ hw)
    refine ⟨W.X • z, ⟨z, hzN, rfl⟩, ?_⟩
    rw [map_smulA, hz]
    exact hw'

end Generic


set_option maxHeartbeats 1000000 in
theorem crystalline_extension_integral_cocycle_all_places : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P8 D HW F := by
  intro D HW F Cm l _ K s LL h T M hh hT hjT Tp ι π hses hTp e heN hφe hγe x hx c hc
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hexact : Function.Exact (((HW l).W K s LL h).map ι) (((HW l).W K s LL h).map π) := by
    let E := ((F l).E K s LL h).tie
    haveI := GlobalTheory.EtaleExact.finite_OL LL
    haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
    have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
    exact (GlobalTheory.EtaleExact.exact_of_tie E
      (GlobalTheory.EtaleExact.map_ne_top_of_tie E (by
        rw [hp]
        exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL) (by
        rw [hp]
        exact GlobalTheory.EtaleExact.sep_RW LL)) T Tp ((HW l).W K s LL h).one ι π hses).2.1
  have hsat := GlobalTheory.T.mem_wachN_of_map_mem_saturated D HW F l K s LL h T Tp ((HW l).W K s LL h).one ι π hT hTp
    (GlobalTheory.NL.one_crys (HW l) h) hses
  have hjs := GlobalTheory.NL.JumpsSES.jumps_ses_and_one D HW l K s LL h T Tp ((HW l).W K s LL h).one ι π hTp hses
  have hjTp : JumpsLet ((HW l).W K s LL h) Tp M hh := by
    intro τ i hτ a ha
    rcases (hjs.1 τ a).1 ha with h1 | h1
    · exact hjT τ i hτ a h1
    · rw [hjs.2 τ a h1]
      exact ⟨by simp, by simp⟩
  have h5 := (GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm l K s LL h Tp M hh hTp hjTp).1
  have h2 := (GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm l K s LL h Tp hTp).2.2
  exact core _ T Tp ι π M (fun y hy => (hexact y).1 hy) hsat h5 h2 e hφe hγe x hx c hc

end GlobalTheory.NL.NygaardFrobeniusPower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlacesStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p8_of_cmpOf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P8 D HW F := by
  first | exact @GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places | exact GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places | (intros; apply GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places <;> assumption)
end
