module

public import Formalism.SharpRestriction.LevelLetterCocycles.RingStepsOf
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvFil
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfJumpsLet
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMem
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.LvDataLocalizesConstOfCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfCoeff
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfHOnil

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfHuZ
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem Pf_HuZ_v_dvd (W : LocWach PD LL O v n) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (k : ℕ) (z : ℤ_[PD.p]) (hz : (PD.p : ℤ_[PD.p]) ^ k ∣ z) :
    (k : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)) := by
  obtain ⟨y, rfl⟩ := hz
  rw [map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast, AddValuation.map_mul,
    AddValuation.map_pow, W.v_l, nsmul_one]
  exact le_add_of_nonneg_right (hv_int _)

theorem hv_holds (W : LocWach PD LL O v n) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) :
    ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)) :=
  fun s z hz => Pf_HuZ_v_dvd W hv_int (s + 1) z hz

theorem huZ_holds (hu : ιZ uZ = (W.χΓ W.gam : O)) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) :
    ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)) := by
  intro k
  have : NeZero (PD.p ^ k) := ⟨pow_ne_zero _ (Fact.out : PD.p.Prime).ne_zero⟩
  have hdvd : (PD.p : ℤ_[PD.p]) ^ k ∣
      (uZ : ℤ_[PD.p]) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : ℤ_[PD.p]) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_zmod_val, sub_self]
  have h := Pf_HuZ_v_dvd (ιZ := ιZ) W hv_int k _ hdvd
  rwa [map_sub, map_natCast, hu, map_sub, map_natCast] at h

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvDelta
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section Graded

variable {LL Ks : Type} [Field LL] [CommRing Ks] [Algebra LL Ks]

theorem grdB_zero' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : grdB τ a 0 = 0 := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((0 : HahnSeries ℤ Ks).coeff n) = (0 : HahnSeries ℤ Ks).coeff n
  simp

theorem grdB_one' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : grdB τ a 1 = 1 := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((1 : HahnSeries ℤ Ks).coeff n) = (1 : HahnSeries ℤ Ks).coeff n
  by_cases h : n = 0
  · subst h
    simp
  · simp [HahnSeries.coeff_one, h]

theorem grdB_mul' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (x y : HahnSeries ℤ Ks) :
    grdB τ a (x * y) = grdB τ a x * grdB τ a y := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((x * y).coeff n) = (grdB τ a x * grdB τ a y).coeff n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [HahnSeries.coeff_mul, HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
  symm
  have hsub : ∀ ij : ℤ × ℤ, ij ∈ Finset.antidiagonal (grdB τ a x).isPWO_support
      (grdB τ a y).isPWO_support n → ij ∈ Finset.antidiagonal x.isPWO_support y.isPWO_support n := by
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    refine ⟨fun h0 => hij.1 ?_, fun h0 => hij.2.1 ?_, hij.2.2⟩
    · change algebraMap LL Ks ((a ^ ij.1 : LLˣ) : LL) * τ (x.coeff ij.1) = 0
      rw [h0, map_zero, mul_zero]
    · change algebraMap LL Ks ((a ^ ij.2 : LLˣ) : LL) * τ (y.coeff ij.2) = 0
      rw [h0, map_zero, mul_zero]
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    have hn : ij.1 + ij.2 = n := hij.2.2
    change (algebraMap LL Ks ((a ^ ij.1 : LLˣ) : LL) * τ (x.coeff ij.1)) *
      (algebraMap LL Ks ((a ^ ij.2 : LLˣ) : LL) * τ (y.coeff ij.2)) = _
    rw [← hn, zpow_add, Units.val_mul, map_mul, map_mul]
    ring
  · intro ij hmem hnot
    rw [Finset.mem_antidiagonal] at hmem hnot
    by_cases h1 : (grdB τ a x).coeff ij.1 = 0
    · rw [h1, zero_mul]
    · by_cases h2 : (grdB τ a y).coeff ij.2 = 0
      · rw [h2, mul_zero]
      · exact absurd ⟨h1, h2, hmem.2.2⟩ hnot

theorem grdB_ringInverse (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) {X : HahnSeries ℤ Ks} (hX : grdB τ a X = X) :
    grdB τ a (Ring.inverse X) = Ring.inverse X := by
  by_cases hu : IsUnit X
  · obtain ⟨u, rfl⟩ := hu
    rw [Ring.inverse_unit]
    have h1 : grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * ↑u = 1 := by
      conv_lhs => rw [← hX]
      rw [← grdB_mul', Units.inv_mul, grdB_one']
    calc grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks)
        = grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
      _ = (grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * ↑u) * ↑u⁻¹ := by ring
      _ = ↑u⁻¹ := by rw [h1, one_mul]
  · rw [Ring.inverse_non_unit _ hu, grdB_zero']

theorem ofPS_coeff_neg {R : Type} [CommRing R] (x : PowerSeries R) {i : ℤ} (hi : i < 0) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff i = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_of_notMem_range (by
    rintro ⟨m, hm⟩
    simp at hm
    omega)

end Graded

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem val_sub_toZModPow (W : LocWach PD LL O v n) (valRing : ValRing O v) (ιZ : ℤ_[PD.p] →+* O)
    (ω : ℤ_[PD.p]) (N : ℕ) :
    ((N : ℕ) : WithTop ℚ) ≤
      v (algebraMap O LL (ιZ ω) - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : LL)) := by
  have : NeZero (PD.p ^ N) := ⟨pow_ne_zero _ PD.hp.ne_zero⟩
  have hk : ω - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : ℤ_[PD.p]) ∈
      RingHom.ker (PadicInt.toZModPow (p := PD.p) N) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  obtain ⟨y, hy⟩ := hk
  have e : algebraMap O LL (ιZ ω) - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : LL) =
      ((PD.p : ℕ) : LL) ^ N * algebraMap O LL (ιZ y) := by
    rw [← map_natCast (algebraMap O LL), ← map_natCast ιZ, ← map_sub, ← map_sub, hy, map_mul, map_mul,
      map_pow, map_pow, map_natCast, map_natCast]
  rw [e, AddValuation.map_mul, AddValuation.map_pow, W.v_l, nsmul_one]
  exact le_add_of_nonneg_right (valRing.2.2 _)

variable {W : LocWach PD LL O v n}

theorem delta_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (c : ZMod n)
    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF, algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ω.1))
    (valRing : ValRing O v) :
    DeltaRho hR uZ ιZ c := by
  intro s j a
  obtain ⟨g, hg, hχ⟩ := hω j
  apply HahnSeries.ext
  funext i
  by_cases hi : i < 0
  · show algebraMap LL (KsW W s) ((((levW W uZ ιZ s).a j) ^ i : LLˣ) : LL) *
        ((levW W uZ ιZ s).τ j) ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i) =
      (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i
    rw [ofPS_coeff_neg _ hi, map_zero, mul_zero]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hi)
    show algebraMap LL (KsW W s) ((((levW W uZ ιZ s).a j) ^ (k : ℤ) : LLˣ) : LL) *
        ((levW W uZ ιZ s).τ j) ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff (k : ℤ)) =
      (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff (k : ℤ)
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    have hc : ∀ ζ' : Rs LL PD.p s, (PowerSeries.coeff k (rhoL hR c s a)) ζ' =
        PowerSeries.coeff k (W.lev c (ζ' : LL) ((baseIdOf hR).d a)) := fun ζ' => by
      show Pi.evalRingHom (fun _ => LL) ζ' (PowerSeries.coeff k (rhoL hR c s a)) = _
      rw [← PowerSeries.coeff_map, map_eval_rhoL]
      rfl
    funext ζ
    change ((((levW W uZ ιZ s).a j) ^ (k : ℤ) : LLˣ) : LL) *
      (PowerSeries.coeff k (rhoL hR c s a)) (powR LL PD.p s (redU PD.p s j.1) ζ) =
      (PowerSeries.coeff k (rhoL hR c s a)) ζ
    rw [hc, hc]
    have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) := (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
    have hv := val_sub_toZModPow W valRing ιZ (j.1 : ℤ_[PD.p]) (s + 1)
    rw [← hχ] at hv
    have hL := lev_Γ g c ζ _ (s + 1) _ hprim hv rfl ((baseIdOf hR).d a)
    rw [BaseId.γA_Δ _ g hg] at hL
    rw [hL, PowerSeries.coeff_rescale, hχ]
    congr 1

theorem loclInv_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (T : LocLat G Qp LL O)
    (c : ZMod n) {r : ℕ} (Λ : PowerSeries O) (lam : Fin r → Dc W T c) (hΔ : DeltaRho hR uZ ιZ c) :
    LocLInv hR uZ ιZ T c Λ lam := by
  intro s y j
  rw [Level.δ]
  unfold locLF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [graded_semilinear_holds, grdB_ringInverse _ _ (hΔ s j Λ), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [graded_semilinear_holds, hΔ s j (y k), SlopeTestRemainingChoices.grd_cst]

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapHyp
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section General

variable {LL Ks D₁ D₂ : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D₁]
  [Module LL D₁] [AddCommGroup D₂] [Module LL D₂]

theorem Pf_MapHyp_ambMap_coeff (g : Ks ⊗[LL] D₁ →ₗ[Ks] Ks ⊗[LL] D₂) (f : Amb LL Ks D₁) (k : ℤ) :
    ((HahnModule.of Ks).symm (ambMap g f)).coeff k = g (((HahnModule.of Ks).symm f).coeff k) :=
  rfl

theorem Pf_MapHyp_ambMap_smul (g : Ks ⊗[LL] D₁ →ₗ[Ks] Ks ⊗[LL] D₂) (x : HahnSeries ℤ Ks)
    (f : Amb LL Ks D₁) : ambMap g (x • f) = x • ambMap g f := by
  have hsupp : ((HahnModule.of Ks).symm (ambMap g f)).support ⊆
      ((HahnModule.of Ks).symm f).support := by
    intro k hk
    rw [HahnSeries.mem_support] at hk ⊢
    intro h0
    apply hk
    rw [Pf_MapHyp_ambMap_coeff, h0, map_zero]
  apply HahnModule.ext
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [HahnModule.coeff_smul_right (y := ambMap g f) ((HahnModule.of Ks).symm f).isPWO_support hsupp,
    Pf_MapHyp_ambMap_coeff, HahnModule.coeff_smul, map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [map_smul, Pf_MapHyp_ambMap_coeff]

theorem Pf_MapHyp_baseChange_tD (h : D₁ →ₗ[LL] D₂) (τ : Ks ≃ₐ[LL] Ks) (a : LL) (y : Ks ⊗[LL] D₁) :
    h.baseChange Ks (a • tD D₁ τ y) = a • tD D₂ τ (h.baseChange Ks y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x d => simp [tD, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
  | add y y' hy hy' => simp only [map_add (f := _), smul_add, hy, hy']

theorem Pf_MapHyp_grd_ambMap (h : D₁ →ₗ[LL] D₂) (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (f : Amb LL Ks D₁) :
    grd (D := D₂) τ a (ambMap (h.baseChange Ks) f) = ambMap (h.baseChange Ks) (grd (D := D₁) τ a f) := by
  apply HahnModule.ext
  funext i
  change ((a ^ i : LLˣ) : LL) • tD D₂ τ (h.baseChange Ks (cf f i)) =
    h.baseChange Ks (((a ^ i : LLˣ) : LL) • tD D₁ τ (cf f i))
  rw [Pf_MapHyp_baseChange_tD]

end General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

variable {W : LocWach PD LL O v n} {T₁ T₂ : LocLat G Qp LL O}
variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {c : ZMod n}

theorem memD_holds (W : LocWach PD LL O v n) (F : LatHom T₁.L T₂.L) (c : ZMod n) : MemD W F c := by
  intro x hx
  have hA : ∀ (g : G) (y : T₁.V ⊗[Qp] B),
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (actVB PD T₁.ρ g y) =
        actVB PD T₂.ρ g (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w b => simp [actVB, AlgebraTensorModule.map_tmul, F.equiv]
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
  have hB : ∀ (c' : K₀) (y : T₁.V ⊗[Qp] B),
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B)
          (mulVB (K₀ := K₀) (B := B) (V := T₁.V) (LL := LL) c' y) =
        mulVB (K₀ := K₀) (B := B) (V := T₂.V) (LL := LL) c'
          (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) := by
    intro c' y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w b => simp [mulVB, AlgebraTensorModule.map_tmul]
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
  simp only [DcrisL, Dcris, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢
  exact ⟨fun g => by rw [← hA, hx.1 g], fun c' => by rw [← hB, hx.2 c', map_smul]⟩

theorem smul_holds {F : LatHom T₁.L T₂.L} (memD : MemD W F c) :
    ∀ (s : ℕ) (x : HahnSeries ℤ (KsW W s)) (f : Amb LL (KsW W s) (Dc W T₁ c)),
      ambF memD s (x • f) = x • ambF memD s f :=
  fun s x f => Pf_MapHyp_ambMap_smul ((dmapOf memD).baseChange (KsW W s)) x f

theorem inv_holds {F : LatHom T₁.L T₂.L} (memD : MemD W F c) :
    ∀ (s : ℕ) (f : Amb LL (KsW W s) (Dc W T₁ c)), (levW W uZ ιZ s).Inv f →
      (levW W uZ ιZ s).Inv (ambF memD s f) := by
  intro s f hf j
  have hj : (levW W uZ ιZ s).δ j f = f := hf j
  show (levW W uZ ιZ s).δ j (ambF memD s f) = ambF memD s f
  rw [Level.δ] at hj ⊢
  unfold ambF
  rw [Pf_MapHyp_grd_ambMap, hj]

theorem mapHyp_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (F : LatHom T₁.L T₂.L)
    (c : ZMod n) : MapHyp hR uZ ιZ F c :=
  ⟨memD_holds W F c, smul_holds (memD_holds W F c), inv_holds (memD_holds W F c)⟩

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfHOmega
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {W : LocWach PD LL O v n}

theorem Pf_HOmega_pow_card (δ : W.Gam) (hδ : δ ∈ W.DelF) : δ ^ W.DelF.card = 1 := by
  have hH : ∀ g : W.Gam, g ∈ CommGroup.torsion W.Gam ↔ g ∈ W.DelF := by
    intro g
    rw [W.DelF_def, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  have hset : ((CommGroup.torsion W.Gam : Subgroup W.Gam) : Set W.Gam) = (W.DelF : Set W.Gam) := by
    ext g
    simp only [SetLike.mem_coe]
    exact hH g
  have hcardH : Nat.card (CommGroup.torsion W.Gam) = W.DelF.card := by
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hd := orderOf_dvd_natCard (⟨δ, (hH δ).2 hδ⟩ : CommGroup.torsion W.Gam)
  rw [Subgroup.orderOf_mk, hcardH] at hd
  exact orderOf_dvd_iff_pow_eq_one.1 hd

theorem hω_holds (hcard : W.DelF.card = PD.p - 1) (hinj : Function.Injective (algebraMap O LL))
    (ιZ : ℤ_[PD.p] →+* O) :
    ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF, algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ω.1) := by
  classical
  intro ω
  have hpos : 0 < PD.p - 1 := by have := PD.hp.two_le; omega
  set f : W.Gam → LL := fun g => algebraMap O LL (W.χΓ g : O) with hf
  have hAcard : (W.DelF.image f).card = PD.p - 1 := by
    rw [Finset.card_image_of_injOn, hcard]
    intro x _ y _ hxy
    apply W.χΓ_inj
    apply Units.ext
    exact hinj hxy
  have hARt : W.DelF.image f ⊆ Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    rw [Polynomial.mem_nthRootsFinset hpos]
    have h1 : g ^ (PD.p - 1) = 1 := hcard ▸ Pf_HOmega_pow_card g hg
    simp only [hf]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one, map_one]
  have hRt : (Polynomial.nthRootsFinset (PD.p - 1) (1 : LL)).card ≤ PD.p - 1 := by
    unfold Polynomial.nthRootsFinset
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  have hEq : W.DelF.image f = Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) :=
    Finset.eq_of_subset_of_card_le hARt (by omega)
  have hωR : algebraMap O LL (ιZ ω.1) ∈ Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) := by
    rw [Polynomial.mem_nthRootsFinset hpos, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ω.2,
      Units.val_one, map_one, map_one]
  rw [← hEq] at hωR
  obtain ⟨g, hg, hgω⟩ := Finset.mem_image.1 hωR
  exact ⟨g, hg, hgω⟩

end Formalism.MainNotions.N.Ln03.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

namespace Assemble

theorem frac_of [IsDomain O] [IsFractionRing O LL] (a : LL) :
    ∃ y o : O, algebraMap O LL y ≠ 0 ∧ algebraMap O LL y * a = algebraMap O LL o := by
  obtain ⟨⟨o, y⟩, h⟩ := IsLocalization.surj (nonZeroDivisors O) a
  exact ⟨y, o, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2, by rw [mul_comm]; exact h⟩

theorem firstGeometricCondition_of_properties (hR : Ring9 W) :
    ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι PowerSeries.X = (w : PowerSeries O) * PowerSeries.X ^ (PD.p - 1) := by
  obtain ⟨w, hw, h⟩ := π₀₁_eq hR
  exact ⟨hw.unit, by rw [(baseIdOf hR).ι_X, IsUnit.unit_spec]; exact h⟩

end Assemble

theorem lvHyp_holds (Lb : LevB W) (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) {T : LocLat G Qp LL O}
    (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) (Λ κ : PowerSeries O) {r : ℕ} (e : Fin r → C.V)

    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hgamK : W.gamK = W.gam)

    (hs1 : W.s = 1) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hT : IsCrys PD T.ρ) {Mj hj : ZMod n → ℕ}
    (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj hj)

    (valRing : ValRing O v) (hv : ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)))

    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF,
      algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ((ω.1 : ℤ_[PD.p]ˣ) : ℤ_[PD.p])))
    (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)))
    (m : ℕ) (hm : ∀ i, Mj i ≤ m) (hκ : κ = Λ * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) :
    LvHyp Lb hR uZ ιZ C c ell Λ κ (lamOf C c ell e) := by
  have hΔ := delta_holds hR uZ ιZ c lev_Γ hω valRing
  exact
    { delta := hΔ
      gamInv := gamInv_holds uZ ιZ T c
      gamRho := gamRho_holds hR uZ ιZ c lev_Γ hgamK huZ
      kap := kap_holds C ell Λ κ hP5 hT hJl hs1 hR m hm hκ
      expSemi := expSemi_holds Lb hR T c levN_eq
      locInv := locInv_holds Lb C κ hΔ hT levB_Γ hω hv
      loclInv := loclInv_holds hR uZ ιZ T c Λ _ hΔ
      filAnti := filAnti_holds
      rhoC := rhoC_holds hR c }

theorem levSteps_of_jumps [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ}
    {κ : PowerSeries O} {r : ℕ} {e : Fin r → C.V}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ (lamOf C c ell e))
    (ϖ : O) (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)

    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) {π' : LetA O n} (hP9 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hT : IsCrys PD T.ρ) {Mj hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj hj)
    (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n0))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p) (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)))
    (m : ℕ) (hm : ∀ i, Mj i ≤ m)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k)

    (hmem : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Mem)
    (hpa1b : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocalizesConst M e)
    (hjumps : ∀ s < ell, Formalism.ExponentWindows.G.Jumps (kind s) G₀ Sz η (b s) (FilD W T c s)) :
    LevSteps Hy ϖ j M g G₀ Sz η kind b e := by
  have R := ringSteps_of Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η ϖ hϖ (by omega) hℓm n0 hn0 hroot (Assemble.firstGeometricCondition_of_properties hR) G2 hφ hρζ
    huZv hutie hom'
  have hp0 : (PD.p : LL) ≠ 0 := Nat.cast_ne_zero.2 PD.hp.ne_zero
  have hP5' : ∀ i, (latOf C).P5M i m := fun i => LvLoc.latOf_P5M_of_p5_of_le C (hP5 T Mj hj hT hJl) hs1 hR m hm i
  exact
    { k1b := R.1
      k1c := fun s hs => (R.2.2.1 s hs).1
      k1d := fun s hs => (R.2.2.1 s hs).2
      unitsAt := R.2.2.2.1
      compl := R.2.2.2.2
      filt := filt_holds ell hfin
      jumps := hjumps
      mem := hmem
      locReg := locReg_holds Hy j M g η kind b m hκ R.1 R.2.2.2.1 hP5' levN_eq levB_φ lev_φ hp0 hs1 hP4
      pa1b := hpa1b
      equiv := equiv_holds Hy j M g η kind b hT levB_Γ hs1 hl huZ
      span := span_holds hBasis hBasis_e
      ind := ind_holds hBasis hBasis_e
      locLIs := locLIs_holds Hy j M g η kind b H rfl R.1 R.2.2.2.1
      lamInd := lamInd_holds hP3 hP9 Assemble.frac_of hBasis hBasis_e rfl
      lamSpan := lamSpan_holds hP3 hP9 hBasis hBasis_e rfl }

theorem mapSteps_holds {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
    {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
    (hC : CoordHom C₁ C₂ F) (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ (lamOf C₁ c ell e₁))
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ (lamOf C₂ c ell e₂))
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))

    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))

    (hk1b₁ : (lvModel Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b) (hUnits₁ : (lvModel Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt)
    (hk1b₂ : (lvModel Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b) (hUnits₂ : (lvModel Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt)

    (m₁ m₂ : ℕ)
    (hκ₁ : κ₁ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m₁)
    (hκ₂ : κ₂ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m₂)
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) :
    MapSteps hC Hy₁ Hy₂ Mh j M g η kind b e₁ e₂ P := by
  have hprL := prLIs_holds hC e₁ e₂ P he₂ hP
  exact
    { locComm := locComm_holds hC Hy₁ Hy₂ Mh j M g η kind b levN_eq
        (kapUnit_holds Hy₁ j M g η kind b m₁ hκ₁ hk1b₁ hUnits₁)
        (kapUnit_holds Hy₂ j M g η kind b m₂ hκ₂ hk1b₂ hUnits₂)
      loclComm := loclComm_holds hC Hy₁ Hy₂ Mh j M g η kind b e₁ e₂ P rfl rfl he₁ he₂ hP
      mapFl := mapFl_holds Hy₁ Hy₂ Mh j M g η kind b
      cMap := cMap_holds Mh.memD kind b η P
        (lambda_of_matrixCongruences hC Mh.memD e₁ e₂ P he₁ he₂ hprL)
      prLIs := hprL }

theorem mapHyp_of (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (c : ZMod n) : MapHyp hR uZ ιZ F c :=
  mapHyp_holds hR uZ ιZ F c

namespace Assemble

theorem finrank_one (hKb : Function.Bijective (algebraMap K₀ K)) : Module.finrank K₀ K = 1 :=
  (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hKb).toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self K₀)

theorem pow_unif [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) :
    ∃ (N : ℕ) (u : O), ((PD.p : ℕ) : O) ^ N = ϖ * u := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hℓm
  obtain ⟨u, hu⟩ := hℓm
  exact ⟨1, u, by rw [pow_one, hu]⟩

theorem p_ne_zero [CharZero LL] : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  have h2 : ((PD.p : ℕ) : LL) = 0 := by rw [← map_natCast (algebraMap O LL), h, map_zero]
  exact PD.hp.ne_zero (Nat.cast_eq_zero.1 h2)

theorem jumps_bound [Fintype (K →ₐ[Qp] LL)] (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hKb : Function.Bijective (algebraMap K₀ K)) {T : LocLat G Qp LL O} (hc : CrysLat PD T) :
    ∃ (Mj hj : ZMod n → ℕ) (m : ℕ), Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj hj ∧ ∀ i, Mj i ≤ m := by
  obtain ⟨Mj, hj, h⟩ := jumps_bounded_crystalline (W := W) hDR hKb T hc
  exact ⟨Mj, hj, Finset.univ.sup Mj, h, fun i => Finset.le_sup (Finset.mem_univ i)⟩

end Assemble

theorem lvHyp_holds' (Lb : LevB W) (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) {T : LocLat G Qp LL O}
    (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) (Λ κ : PowerSeries O) {r : ℕ} (e : Fin r → C.V)

    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))

    (hs1 : W.s = 1) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T) (hT : IsCrys PD T.ρ)
    {Mj hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj hj)

    (valRing : ValRing O v) (hKb : Function.Bijective (algebraMap K₀ K))

    (hl : 5 ≤ PD.p) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (m : ℕ) (hm : ∀ i, Mj i ≤ m) (hκ : κ = Λ * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) :
    LvHyp Lb hR uZ ιZ C c ell Λ κ (lamOf C c ell e) :=
  lvHyp_holds Lb hR uZ ιZ C c ell Λ κ e lev_Γ levB_Γ levN_eq (W.gamK_eq_one hs1 (by omega)) hs1 hP5 hT hJl
    valRing (hv_holds W valRing.2.2)
    (hω_holds (card_DelF hs1 (by omega) (Assemble.finrank_one hKb) h9) valRing.1 ιZ)
    (huZ_holds hutie valRing.2.2) m hm hκ

theorem levSteps_of_jumps' [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ}
    {κ : PowerSeries O} {r : ℕ} {e : Fin r → C.V}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ (lamOf C c ell e))
    (ϖ : O) (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)

    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (cmp_eq : ∀ (i : ZMod n) (x : ↥(W.N T)), W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hP4L : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hc : CrysLat PD T) {Mj Hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj Hj)

    (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hKb : Function.Bijective (algebraMap K₀ K))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hn : ell ≤ n) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p) (m : ℕ) (hm : ∀ i, Mj i ≤ m)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (hj : j ≤ ell) (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M)
    (hjumps : ∀ s < ell, Formalism.ExponentWindows.G.Jumps (kind s) G₀ Sz η (b s) (FilD W T c s)) :
    LevSteps Hy ϖ j M g G₀ Sz η kind b e := by
  have hℓ2 : PD.p ≠ 2 := by omega
  have hK1 := Assemble.finrank_one hKb
  have hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀ := ((h9 hs1 hℓ2).2.2 hK1).2
  have R := ringSteps_of Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η ϖ hϖ hℓ2 hℓm n hn hroot (Assemble.firstGeometricCondition_of_properties hR) G2 hφ hρζ
    huZv hutie hom'
  have hfin : FiniteDimensional LL ↥(Dcris PD T.ρ) := by
    have := hc.1
    exact lvFil_fin_of_isCrys PD T.ρ hc.2.2.2
  have hP5' : ∀ i, (latOf C).P5M i m := fun i => LvLoc.latOf_P5M_of_p5_of_le C (hP5 T Mj Hj hc.2.2.2 hJl) hs1 hR m hm i
  have he : ∀ k, e k ∈ (latOf C).N (c - (ell : ZMod n)) := fun k => by
    rw [← hBasis_e k]
    exact (hBasis k).2
  have hmem := mem_holds hP4L hSat hc.2.2.2 (levN_eq T) hmod hP3
    (free_of (baseIdOf_inj hR) (baseIdOf_full hR) hmod C c) hroot hn m hκ R.1 R.2.2.2.1
    (filt_holds ell hfin) ϖ R.2.2.2.2 (Assemble.pow_unif hϖ hℓm) Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η
  have hpa1b := lvData_localizesConst_of_crystalline Hy j M g η kind b m e hκ he rfl R.1 R.2.2.2.1 hP5' levN_eq levB_φ lev_φ levB_Γ
    cmp_eq hc.2.2.2 hs1 hℓ2 hP4 hR hj h3g
  exact levSteps_of_jumps Hy ϖ j M g G₀ Sz η kind b levN_eq levB_φ lev_φ levB_Γ hs1 hP4 hP3 hmod hP5
    hc.2.2.2 hJl hfin hϖ hℓm n hn hroot G2 hφ hρζ huZv hutie hom' hl (huZ_holds hutie hv_int) m hm hκ
    hBasis hBasis_e hmem hpa1b hjumps

theorem levSteps_holds' [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ}
    {κ : PowerSeries O} {r : ℕ} {e : Fin r → C.V}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ (lamOf C c ell e))
    (ϖ : O) (j M g G₀ Sz η : ℕ) (ty : ZMod n → LT)

    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (cmp_eq : ∀ (i : ZMod n) (x : ↥(W.N T)), W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hP4L : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hc : CrysLat PD T) {Mj Hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj Hj)

    (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hKb : Function.Bijective (algebraMap K₀ K))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hn : ell ≤ n) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p) (m : ℕ) (hm : ∀ i, Mj i ≤ m)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (hj : j ≤ ell) (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M)
    (hJ : KindJumps PD T W.emb G₀ Sz η ty) :
    LevSteps Hy ϖ j M g G₀ Sz η (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e :=
  levSteps_of_jumps' Hy ϖ j M g G₀ Sz η _ _ levN_eq levB_φ lev_φ levB_Γ cmp_eq hs1 hP4 hP4L hSat hP3 h9 hP5 hc hJl hv_int hKb hϖ hℓm hn hroot G2 hφ hρζ huZv hutie hom' hl m hm hκ hBasis hBasis_e hj h3g (jumps_holds hKb.2 c ell G₀ Sz η ty hJ)

theorem levSteps_holds_quot' [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ}
    {κ : PowerSeries O} {r : ℕ} {e : Fin r → C.V}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ (lamOf C c ell e))
    (ϖ : O) (j M g G₀ Sz η : ℕ) (ty : ZMod n → LT)

    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (cmp_eq : ∀ (i : ZMod n) (x : ↥(W.N T)), W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hP4L : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hc : CrysLat PD T) {Mj Hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj Hj)

    (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hKb : Function.Bijective (algebraMap K₀ K))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hn : ell ≤ n) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p) (m : ℕ) (hm : ∀ i, Mj i ≤ m)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (hj : j ≤ ell) (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M)
    (hQuot : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    {T₀ : LocLat G Qp LL O} (F : LatHom T₀.L T.L) (hc₀ : CrysLat PD T₀) (hon : F.Onto)
    (hJ : KindJumps PD T₀ W.emb G₀ Sz η ty) :
    LevSteps Hy ϖ j M g G₀ Sz η (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e :=
  levSteps_of_jumps' Hy ϖ j M g G₀ Sz η _ _ levN_eq levB_φ lev_φ levB_Γ cmp_eq hs1 hP4 hP4L hSat hP3 h9 hP5 hc hJl hv_int hKb hϖ hℓm hn hroot G2 hφ hρζ huZv hutie hom' hl m hm hκ hBasis hBasis_e hj h3g
    (jumps_holds_quot hKb.2 hQuot F hc₀ hc hon c ell G₀ Sz η ty hJ)

theorem finalArc_holds [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL] [Fintype (K →ₐ[Qp] LL)]
    (Lb : LevB W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O)
    {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
    {F : LatHom T₁.L T₂.L} (hC : CoordHom C₁ C₂ F) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (ϖ : O)
    (j M g G₀ Sz η : ℕ) (ty : ZMod n → LT) {r₁ r₂ : ℕ} (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V)
    (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))

    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (cmp_eq : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(W.N T)),
      W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)
    (levB_φ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL),
      (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hP4L : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hQuot : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)

    (hc₁ : CrysLat PD T₁) (hc₂ : CrysLat PD T₂) (hon : F.Onto) (hJ : KindJumps PD T₁ W.emb G₀ Sz η ty)

    (valRing : ValRing O v) (hKb : Function.Bijective (algebraMap K₀ K))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hn : ell ≤ n) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p)
    (hBasis₁ : Module.Basis (Fin r₁) (PowerSeries O) ↥((latOf C₁).N (c - (ell : ZMod n))))
    (hBasis_e₁ : ∀ k, (hBasis₁ k : C₁.V) = e₁ k)
    (hBasis₂ : Module.Basis (Fin r₂) (PowerSeries O) ↥((latOf C₂).N (c - (ell : ZMod n))))
    (hBasis_e₂ : ∀ k, (hBasis₂ k : C₂.V) = e₂ k)
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l))
    (hj : j ≤ ell) (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M) :
    E.FinalArc (latHomOf hC) c ell H LL (KsW W) (DeltaT PD.p) ϖ (W.χΓ W.gam) j M g G₀ Sz η
      (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) := by
  obtain ⟨Mj₁, hj₁, m₁, hJl₁, hm₁⟩ := Assemble.jumps_bound (W := W) hDR hKb hc₁
  obtain ⟨Mj₂, hj₂, m₂, hJl₂, hm₂⟩ := Assemble.jumps_bound (W := W) hDR hKb hc₂
  have hT₁ := hc₁.2.2.2
  have hT₂ := hc₂.2.2.2
  have Hy₁ := lvHyp_holds' Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m₁) e₁
    lev_Γ levB_Γ levN_eq hs1 hP5 (hP9 T₁ hT₁) hT₁ hJl₁ valRing hKb hl hutie m₁ hm₁ rfl
  have Hy₂ := lvHyp_holds' Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m₂) e₂
    lev_Γ levB_Γ levN_eq hs1 hP5 (hP9 T₂ hT₂) hT₂ hJl₂ valRing hKb hl hutie m₂ hm₂ rfl
  have ls₁ := levSteps_holds' Hy₁ ϖ j M g G₀ Sz η ty levN_eq (levB_φ T₁ hT₁) lev_φ levB_Γ (cmp_eq T₁ hT₁) hs1
    (hP4 T₁ hT₁) hP4L hSat (hP3 T₁ hT₁) (hP9 T₁ hT₁) hP5 hc₁ hJl₁ valRing.2.2 hKb hϖ hℓm hn hroot G2 hφ hρζ
    huZv hutie hom' hl m₁ hm₁ rfl hBasis₁ hBasis_e₁ hj h3g hJ
  have ls₂ := levSteps_holds_quot' Hy₂ ϖ j M g G₀ Sz η ty levN_eq (levB_φ T₂ hT₂) lev_φ levB_Γ (cmp_eq T₂ hT₂)
    hs1 (hP4 T₂ hT₂) hP4L hSat (hP3 T₂ hT₂) (hP9 T₂ hT₂) hP5 hc₂ hJl₂ valRing.2.2 hKb hϖ hℓm hn hroot G2 hφ
    hρζ huZv hutie hom' hl m₂ hm₂ rfl hBasis₂ hBasis_e₂ hj h3g hQuot F hc₁ hon hJ
  have he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)) := fun k => by
    rw [← hBasis_e₁ k]
    exact (hBasis₁ k).2
  have he₂ : ∀ k, e₂ k ∈ (latOf C₂).N (c - (ell : ZMod n)) := fun k => by
    rw [← hBasis_e₂ k]
    exact (hBasis₂ k).2
  have ms := mapSteps_holds hC e₁ e₂ Hy₁ Hy₂ (mapHyp_of hR uZ ιZ F c) j M g η _ _ P levN_eq
    ls₁.k1b ls₁.unitsAt ls₂.k1b ls₂.unitsAt m₁ m₂ rfl rfl he₁ he₂ hP
  exact arc_of_steps hC Hy₁ Hy₂ (mapHyp_of hR uZ ιZ F c) ϖ j M g G₀ Sz η _ _ e₁ e₂ P ls₁ ls₂ ms

theorem coordSteps_holds [IsDomain O] [IsDiscreteValuationRing O] [CharZero LL]
    [Fintype (K →ₐ[Qp] LL)] (hR : Ring9 W) {e : W.DD W.one}

    (hs1 : W.s = 1) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W) (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hUnitGen : UnitGen W e) (hCrysOne : IsCrys PD W.one.ρ)

    (hKb : Function.Bijective (algebraMap K₀ K))

    (hl : 5 ≤ PD.p) :
    CoordSteps hR e :=
  coordSteps_of hR e (coeffStep_holds hR)
    (splitStep_holds inferInstance (hOnil_of (Assemble.p_ne_zero (LL := LL))) hs1
      (by omega) hP9 hLem3 (jumps_bounded_crystalline hDR hKb))
    (unitStep_holds hUnitGen hCrysOne)

end Formalism.MainNotions.N.Ln03.Pf
