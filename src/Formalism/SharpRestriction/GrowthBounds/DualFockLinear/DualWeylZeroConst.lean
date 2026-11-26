module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideExplicitIdentification
public import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneMemH0WeightZero
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FilterOfSupported
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.CloudBStepOfRho
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.CloudBAtOfRho
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

theorem OpCl_mono {R : Type} [CommRing R] {n' k : ℕ} (TT : Finset (Fin n')) (c : ℕ)
    {M N : Submodule R (MvPolynomial (Fin n' × Fin k) R)} (h : M ≤ N) : OpCl TT c M ≤ OpCl TT c N := by
  unfold OpCl
  apply Submodule.span_mono
  rintro y ⟨f, hf, l, h1, h2, rfl⟩
  exact ⟨f, h hf, l, h1, h2, rfl⟩

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n'))
  (lam0 : Fin n' → Fin (m + 1) → ℤ)

def RhoAt (c0 loss : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ (κ : ℕ) (Ix : Type) (ρ : Ix → (Vsp Kf lam0 →ₗ[Kf] Vsp Kf (flW (m := m) (dT TT lam0)))), (κ : ℝ) ≤ bK ∧
    (∀ β, ∀ u ∈ Re p ι σ w r lam0 e, ρ β u ∈ Re p ι σ w r (flW (dT TT lam0)) e) ∧
    (∀ β, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ u ∈ Re p ι σ w r lam0 e',
      ρ β u ∈ scale (algebraMap O Kf w ^ (-(loss : ℤ))) (Re p ι σ w r (flW (dT TT lam0)) e')) ∧
    (∀ β, ∀ u ∈ HL (O := O) ι σ lam0 e.tgt,
      ρ β u ∈ scale ((p : Kf) ^ Ar r (restW TT lam0) * algebraMap O Kf w ^ (-(loss : ℤ)))
        (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)) ∧
    (∀ β (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) (s : Vsp Kf (restW TT lam0)) (u : Vsp Kf lam0),
      ((u : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ((Θ F : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * ((s : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
      ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈
          OpCl TT c0 (Submodule.span (KK O) {(F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))}) ∧ ρ β u = Θ F') ∧
    (∀ u ∈ Re p ι σ w r lam0 e,
      (∀ β, ρ β u ∈ scale (algebraMap O Kf w ^ ((2 * κ + 1 : ℕ) : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e)) →
      u ∈ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r lam0 e))

end At

private theorem mem_scale_iff_exists_smul {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X]
    [Module Kf X] [Module O X] [IsScalarTower O Kf X] {c : Kf} {M : Submodule O X} {x : X} :
    x ∈ scale c M ↔ ∃ y ∈ M, c • y = x := by
  simp [scale]

private theorem smul_mem_scale_mul_of_mem_scale {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X]
    [Module Kf X] [Module O X] [IsScalarTower O Kf X] {a : Kf} {M : Submodule O X} {x : X} (b : Kf)
    (hx : x ∈ scale a M) : b • x ∈ scale (b * a) M := by
  obtain ⟨y, hy, rfl⟩ := mem_scale_iff_exists_smul.mp hx
  exact mem_scale_iff_exists_smul.mpr ⟨y, hy, by rw [mul_smul]⟩

private theorem scale_scale_eq_scale_mul {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X]
    [Module Kf X] [Module O X] [IsScalarTower O Kf X] (a b : Kf) (M : Submodule O X) :
    scale a (scale b M) = scale (a * b) M := by
  ext x
  simp only [mem_scale_iff_exists_smul]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by rw [mul_smul]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨b • z, ⟨z, hz, rfl⟩, by rw [mul_smul]⟩

private theorem dualMap_mem_scale_dualLat_of_maps_to_scale {O Kf V0 V1 : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V0]
    [Module Kf V0] [Module O V0] [IsScalarTower O Kf V0] [AddCommGroup V1] [Module Kf V1] [Module O V1]
    [IsScalarTower O Kf V1] (f : V0 →ₗ[Kf] V1) (M0 : Submodule O V0) (M1 : Submodule O V1) (d t : Kf)
    (hd : d ≠ 0) (ht : t ≠ 0) (hf : ∀ u ∈ M0, f u ∈ scale d M1) (T : Module.Dual Kf V1)
    (hT : T ∈ scale t (dualLat O Kf M1)) : f.dualMap T ∈ scale (t * d) (dualLat O Kf M0) := by
  obtain ⟨T0, hT0, rfl⟩ := mem_scale_iff_exists_smul.mp hT
  have hT0' : ∀ v ∈ M1, T0 v ∈ Set.range (algebraMap O Kf) := hT0
  refine mem_scale_iff_exists_smul.mpr ⟨(t * d)⁻¹ • f.dualMap (t • T0), ?_, ?_⟩
  · show ∀ u ∈ M0, _ ∈ Set.range (algebraMap O Kf)
    intro u hu
    obtain ⟨z, hz, hzu⟩ := mem_scale_iff_exists_smul.mp (hf u hu)
    obtain ⟨o, ho⟩ := hT0' z hz
    refine ⟨o, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.dualMap_apply, ← hzu, LinearMap.smul_apply, map_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, ho]
    field_simp
  · rw [smul_smul, mul_inv_cancel₀ (mul_ne_zero ht hd), one_smul]


set_option maxHeartbeats 1000000 in
theorem cloudBAt_of_rho {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hBP : BePerfect)
    {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0)
    (c0 loss : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) (dT TT lam0))))
    (hv : ∀ (b : Fin nb) (s : Vsp Kf (restW TT lam0)) (u : Vsp Kf lam0), s ∈ Re p ι σ w r (restW TT lam0) e →
      ((u : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * ((s : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
      u ∈ Re p ι σ w r lam0 e)
    (hρ : RhoAt p n' ι σ w r TT lam0 c0 loss bK e Θ) : CloudBAt p n' ι σ w r TT lam0 c0 loss bK e FsB Θ := by
  obtain ⟨κ, Ix, ρ, hκ, h1, h2, h3, h4, h5⟩ := hρ
  haveI := hS.frac_alt
  have hpne : (p : Kf) ≠ 0 := by
    have hW : (p : W) ≠ 0 := hS.p_unif.ne_zero
    have hQ : (p : Qq) ≠ 0 := by
      intro h
      apply hW
      apply IsFractionRing.injective W Qq
      rw [map_natCast, h, map_zero]
    intro h
    apply hQ
    apply ι.injective
    rw [map_natCast, h, map_zero]
  have hp2 : (algebraMap O Kf w) ^ 2 = (p : Kf) := by
    rw [← map_pow, hS.w_sq, map_natCast]
  have hω : (algebraMap O Kf w) ≠ 0 := by
    intro h
    apply hpne
    rw [← hp2, h, zero_pow two_ne_zero]
  have hw0 : w ≠ 0 := by
    intro h
    apply hω
    rw [h, map_zero]
  have hpz : ∀ k : ℤ, (p : Kf) ^ k = (algebraMap O Kf w) ^ (2 * k) := by
    intro k
    rw [← hp2, ← zpow_natCast, ← zpow_mul]
    norm_num
  have hadd : (Ar r lam0) = (Ar r (flW (m := m) (dT TT lam0))) + Ar r (restW TT lam0) := by
    unfold Ar
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [lamAt, restW]
    split_ifs <;> simp only [Pi.sub_apply] <;> ring
  have hre1 : ∀ (e' : Edge W Qq (m + 1)) (u : ↥(Vsp Kf lam0)), u ∈ HLe p ι σ w lam0 e' →
      (algebraMap O Kf w) ^ (-(Ar r lam0)) • u ∈ Re p ι σ w r lam0 e' := by
    intro e' u hu
    unfold Re
    exact mem_scale_iff_exists_smul.mpr ⟨u, hu, rfl⟩
  unfold CloudBAt
  refine ⟨κ, hκ, ?_⟩
  intro n2 sh hsh S hSd c hc
  have hSre : ∀ x, S x ∈ Re p ι σ w r lam0 e := fun x => hv x.1 (sh x.2) (S x) (hsh x.2) (hSd x.1 x.2)
  set xx := ∑ x, c x • S x with hxx
  have hxre : xx ∈ Re p ι σ w r lam0 e := Submodule.sum_mem _ (fun x _ => Submodule.smul_mem _ _ (hSre x))
  obtain ⟨β, hβ⟩ : ∃ β, ρ β xx ∉ scale ((algebraMap O Kf w) ^ ((2 * κ + 1 : ℕ) : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e) := by
    by_contra hne
    push_neg at hne
    exact hc (by simpa using h5 xx hxre hne)
  have desc : ∀ N : ℕ, ∀ v, v ∈ Re p ι σ w r (flW (m := m) (dT TT lam0)) e →
      v ∉ scale ((algebraMap O Kf w) ^ (N : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e) →
      ∃ a < N, ∃ y ∈ Re p ι σ w r (flW (m := m) (dT TT lam0)) e,
        y ∉ scale ((algebraMap O Kf w) ^ (1 : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e) ∧ (algebraMap O Kf w) ^ a • y = v := by
    intro N
    induction N with
    | zero =>
      intro v hv0 hn
      exact absurd (mem_scale_iff_exists_smul.mpr ⟨v, hv0, by simp⟩) hn
    | succ N ih =>
      intro v hv0 hn
      by_cases h : v ∈ scale ((algebraMap O Kf w) ^ (1 : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e)
      · obtain ⟨v1, hv1, rfl⟩ := mem_scale_iff_exists_smul.mp h
        have hn1 : v1 ∉ scale ((algebraMap O Kf w) ^ (N : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e) := by
          intro h'
          apply hn
          have h'' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (1 : ℤ)) h'
          have e1 : (algebraMap O Kf w) ^ (1 : ℤ) * (algebraMap O Kf w) ^ (N : ℤ) = (algebraMap O Kf w) ^ ((N + 1 : ℕ) : ℤ) := by
            rw [← zpow_add₀ hω]
            push_cast
            ring_nf
          rwa [e1] at h''
        obtain ⟨a, ha, y, hy, hy1, hya⟩ := ih v1 hv1 hn1
        refine ⟨a + 1, by omega, y, hy, hy1, ?_⟩
        rw [← hya, smul_smul, zpow_one, ← pow_succ']
      · exact ⟨0, by omega, v, hv0, h, by simp⟩
  obtain ⟨a, ha, y, hy, hy1, hya⟩ := desc (2 * κ + 1) (ρ β xx) (h1 β xx hxre) hβ
  have hak : a ≤ 2 * κ := by omega
  choose F' hF'1 hF'2 using fun x : Fin nb × Fin n2 => h4 β (FsB x.1) (sh x.2) (S x) (hSd x.1 x.2)
  have hG : Θ (∑ x, c x • F' x) = ρ β xx := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxx, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [map_smul, LinearMap.map_smul_of_tower, hF'2]
  have hGmem : (↑(∑ x, c x • F' x) : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB := by
    rw [Submodule.coe_sum]
    apply Submodule.sum_mem
    intro x _
    rw [Submodule.coe_smul]
    apply Submodule.smul_of_tower_mem
    unfold SgOp
    exact OpCl_mono TT c0 (Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self (f := fun b => (↑(FsB b) : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))) x.1))) (hF'1 x)
  have hF1 : (w ^ a) • Θ.symm y = ∑ x, c x • F' x := by
    apply Θ.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, hG, ← hya, ← algebraMap_smul Kf (w ^ a) y, map_pow]
  have hF1mem : (↑(Θ.symm y) : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB := by
    have hu : (algebraMap O (KK O) w) ^ a ≠ 0 :=
      pow_ne_zero _ (by rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hw0)
    have h' := Submodule.smul_mem (SgOp n' TT lam0 c0 FsB) ((algebraMap O (KK O) w) ^ a)⁻¹ hGmem
    rw [← hF1, Submodule.coe_smul, ← algebraMap_smul (KK O) (w ^ a), map_pow, smul_smul, inv_mul_cancel₀ hu,
      one_smul] at h'
    exact h'
  refine ⟨Θ.symm y, hF1mem, ?_, ?_, ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) • (ρ β).dualMap, w ^ (2 * κ - a), ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.apply_symm_apply]
    exact hy
  · rw [LinearEquiv.apply_symm_apply]
    simpa using hy1
  · intro T
    rw [map_pow]
    simp only [be, LinearMap.smul_apply, LinearMap.dualMap_apply, LinearEquiv.apply_symm_apply, map_smul,
      smul_eq_mul, ← hya, hpz]
    rw [← hp2, ← pow_mul]
    have e4 : (algebraMap O Kf w) ^ (2 * κ - a) * (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0)) * (algebraMap O Kf w) ^ (2 * (Ar r lam0)) * (algebraMap O Kf w) ^ a =
        (algebraMap O Kf w) ^ (2 * κ) * (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0)))) := by
      simp only [← zpow_natCast]
      simp only [← zpow_add₀ hω]
      congr 1
      push_cast [Nat.cast_sub hak]
      ring
    linear_combination (T y) * e4
  · intro T hT
    have hf : ∀ u ∈ HLe p ι σ w lam0 e,
        ρ β u ∈ scale ((algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))))) (HLe p ι σ w (flW (m := m) (dT TT lam0)) e) := by
      intro u hu
      have h' := h1 β _ (hre1 e u hu)
      unfold Re at h'
      rw [map_smul] at h'
      have h'' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (Ar r lam0)) h'
      rw [smul_smul, ← zpow_add₀ hω (Ar r lam0) (-(Ar r lam0)), add_neg_cancel, zpow_zero, one_smul,
        ← zpow_add₀ hω (Ar r lam0) (-(Ar r (flW (m := m) (dT TT lam0)))), ← sub_eq_add_neg] at h''
      exact h''
    unfold Re' at hT ⊢
    have hd := dualMap_mem_scale_dualLat_of_maps_to_scale (ρ β) _ _ _ _ (zpow_ne_zero _ hω) (zpow_ne_zero _ hω) hf T hT
    have h' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) hd
    have e3 : (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0)) * ((algebraMap O Kf w) ^ (-(Ar r (flW (m := m) (dT TT lam0)))) * (algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))))) = (algebraMap O Kf w) ^ (-(Ar r lam0)) := by
      rw [← zpow_add₀ hω, ← zpow_add₀ hω]
      congr 1
      ring
    rw [e3] at h'
    have hΛ : (((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) • (ρ β).dualMap) T ∈
        scale ((algebraMap O Kf w) ^ (-(Ar r lam0))) (dualLat O Kf (HLe p ι σ w lam0 e)) := by
      rw [LinearMap.smul_apply]
      exact h'
    refine ⟨hΛ, ?_⟩
    obtain ⟨Y, hY, hYe⟩ := mem_scale_iff_exists_smul.mp hΛ
    have hY' : ∀ v ∈ HLe p ι σ w lam0 e, Y v ∈ Set.range (algebraMap O Kf) := hY
    have hxre' := hxre
    unfold Re at hxre'
    obtain ⟨u0, hu0, hu0e⟩ := mem_scale_iff_exists_smul.mp hxre'
    obtain ⟨o, ho⟩ := hY' u0 hu0
    refine ⟨o, ?_⟩
    rw [be, ← hYe, ← hu0e, LinearMap.smul_apply, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hpz]
    have e5 : (algebraMap O Kf w) ^ (-(Ar r lam0)) * (algebraMap O Kf w) ^ (2 * (Ar r lam0)) * (algebraMap O Kf w) ^ (-(Ar r lam0)) = 1 := by
      rw [← zpow_add₀ hω, ← zpow_add₀ hω, ← zpow_zero (algebraMap O Kf w)]
      congr 1
      ring
    linear_combination ho - (Y u0) * e5
  · intro e' he' htgt i T hT
    have hf : ∀ u ∈ HLe p ι σ w lam0 e',
        ρ β u ∈ scale ((algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))) - loss)) (HLe p ι σ w (flW (m := m) (dT TT lam0)) e') := by
      intro u hu
      have h' := h2 β e' he' htgt _ (hre1 e' u hu)
      unfold Re at h'
      rw [scale_scale_eq_scale_mul, map_smul] at h'
      have h'' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (Ar r lam0)) h'
      rw [smul_smul, ← zpow_add₀ hω (Ar r lam0) (-(Ar r lam0)), add_neg_cancel, zpow_zero, one_smul] at h''
      have e3 : (algebraMap O Kf w) ^ (Ar r lam0) * ((algebraMap O Kf w) ^ (-(loss : ℤ)) * (algebraMap O Kf w) ^ (-(Ar r (flW (m := m) (dT TT lam0))))) = (algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))) - loss) := by
        rw [← zpow_add₀ hω, ← zpow_add₀ hω]
        congr 1
        ring
      rwa [e3] at h''
    unfold Re' at hT ⊢
    rw [scale_scale_eq_scale_mul] at hT ⊢
    have hd := dualMap_mem_scale_dualLat_of_maps_to_scale (ρ β) _ _ _ _ (zpow_ne_zero _ hω)
      (mul_ne_zero (zpow_ne_zero _ hω) (zpow_ne_zero _ hω)) hf T hT
    have h' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) hd
    have e3 : (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0)) * ((algebraMap O Kf w) ^ i * (algebraMap O Kf w) ^ (-(Ar r (flW (m := m) (dT TT lam0)))) * (algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))) - loss)) =
        (algebraMap O Kf w) ^ (i - loss) * (algebraMap O Kf w) ^ (-(Ar r lam0)) := by
      simp only [← zpow_add₀ hω]
      congr 1
      ring
    rw [e3] at h'
    rw [LinearMap.smul_apply]
    exact h'
  · intro i T hT
    have hd := dualMap_mem_scale_dualLat_of_maps_to_scale (ρ β) _ _ _ _ (mul_ne_zero (zpow_ne_zero _ hpne) (zpow_ne_zero _ hω))
      (zpow_ne_zero _ hω) (h3 β) T hT
    have h' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) hd
    have e3 : (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0)) * ((algebraMap O Kf w) ^ i * ((p : Kf) ^ Ar r (restW TT lam0) * (algebraMap O Kf w) ^ (-(loss : ℤ)))) =
        (algebraMap O Kf w) ^ (i - loss) := by
      rw [hpz]
      simp only [← zpow_add₀ hω]
      congr 1
      rw [hadd]
      ring
    rw [e3] at h'
    rw [LinearMap.smul_apply]
    exact h'

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

def RhoStep (C CK : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        RhoAt p n' ι σ w r TT lam0 c0 (r * TT.card * c0 + 2 * r * n' * cpp)
          (CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e Θ

def RestRho (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → RhoStep C CK

theorem cloudBStep_of_rho (D : Formalism.BasicNotions.D7) (C CK CLa : ℝ) (hR : RhoStep C CK) : CloudBStep C CK CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hw : algebraMap O Kf w ≠ 0 := w_ne_zero hSet.1
  obtain ⟨Θ', hΘ1, hΘ2⟩ := theta_exists p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (vecE n') (dT TT lam0) (flW (dT TT lam0))
    (by omega) (by omega) (isFlat_flW _) hm hhm
  have hΘeq : Θ = Θ' := LinearEquiv.ext fun G => Subtype.ext (by rw [hΘ G, hΘ2 G])
  have hFs : ∀ b, Θ (FsB b) ∈ Re p ι σ w r (flW (dT TT lam0)) e := by
    intro b
    have h1 : InWjRg p n' O w r (flatLetters (vecE n')) g (FsB b : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) 0 := by
      show InWj w (subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O))) 0
      rw [hFsB b]
      unfold symB toK
      rw [subst_SPtrue w F hF.2.1 hSet.1.even (by omega) hrk hg, ← map_mul]
      intro mm
      exact ⟨AddMonoidAlgebra.coeff _ mm, by rw [coeff_map, pow_zero, one_mul]⟩
    have h2 := (hΘ1.2 g hg e hbasis (FsB b) 0).1 h1
    rw [hΘeq]
    obtain ⟨z, hz, hze⟩ := mem_scale.1 h2
    rw [← hze]
    simpa using hz
  refine cloudBAt_of_rho hSet.1 Formalism.L2.G.Model.bePerfect r TT lam0 hdom c0 _ _ e he FsB Θ ?_
    (hR p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ e he htgt hm g hhm hg hbasis
      Θ hΘ)
  intro b s u hs hu
  exact edge_lattice_mul_of_weight_sum D (Formalism.L2.G.Model.products_sections_integral D) p ι σ w hw r (lambda_zero_eq_product TT lam0) (flW_dom _)
    (restW_dom (by omega) TT lam0 hdom) e hu (hFs b) hs

theorem restCloudB_of_rho (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestRho D CLa Ck Crk Cdeg) :
    RestCloudB D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨CK, C₁, h1, h2, h3⟩ := h hA
  exact ⟨CK, C₁, h1, h2, fun C hC => cloudBStep_of_rho D C CK CLa (h3 C hC)⟩

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section Slice

variable {K : Type} [Field K] {S τ : Type} [DecidableEq S] (A : Finset S)

def slice (γ : MvPolynomial (S × τ) K →ₗ[K] K) : MvPolynomial (S × τ) K →ₗ[K] MvPolynomial (S × τ) K :=
  (MvPolynomial.basisMonomials (S × τ) K).constr K
    (fun e => γ (monomial (e.filter fun v : S × τ => v.1 ∉ A) 1) • monomial (e.filter fun v : S × τ => v.1 ∈ A) 1)

theorem slice_monomial (γ : MvPolynomial (S × τ) K →ₗ[K] K) (e : S × τ →₀ ℕ) (a : K) :
    slice A γ (monomial e a) =
      (a * γ (monomial (e.filter fun v : S × τ => v.1 ∉ A) 1)) • monomial (e.filter fun v : S × τ => v.1 ∈ A) 1 := by
  have h : (monomial e a : MvPolynomial (S × τ) K) = a • MvPolynomial.basisMonomials (S × τ) K e := by
    simp only [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul]
  simp only [slice, Module.Basis.constr_basis, smul_smul]

theorem filter_of_supported {P : MvPolynomial (S × τ) K} {q : S × τ → Prop} [DecidablePred q]
    (hP : P ∈ supported K {v | q v}) {e : S × τ →₀ ℕ} (he : e ∈ P.support) :
    e.filter q = e ∧ e.filter (fun v => ¬ q v) = 0 := by
  rw [mem_supported] at hP
  have key : ∀ v, e v ≠ 0 → q v := fun v hv =>
    hP (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨e, he, Finsupp.mem_support_iff.2 hv⟩))
  refine ⟨(Finsupp.filter_eq_self_iff _ _).2 key, (Finsupp.filter_eq_zero_iff _ _).2 fun v hv => ?_⟩
  by_contra h
  exact hv (key v h)

theorem slice_mul_left (γ : MvPolynomial (S × τ) K →ₗ[K] K) (P R : MvPolynomial (S × τ) K)
    (hP : P ∈ supported K {v : S × τ | v.1 ∈ A}) : slice A γ (P * R) = P * slice A γ R := by
  induction R using MvPolynomial.induction_on' with
  | monomial f b =>
    conv_lhs => rw [P.as_sum]
    conv_rhs => rw [P.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have h := filter_of_supported (q := fun v : S × τ => v.1 ∈ A) hP he
    beta_reduce at h
    rw [monomial_mul_monomial, slice_monomial, slice_monomial, Finsupp.filter_add, Finsupp.filter_add, h.1, h.2,
      zero_add, mul_smul_comm, monomial_mul_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul]
    congr 1
    ring
  | add p q hp hq => rw [mul_add, map_add (f := _), hp, hq, map_add (f := _), mul_add]

theorem slice_spec (γ : MvPolynomial (S × τ) K →ₗ[K] K) (Q : MvPolynomial (S × τ) K)
    (hQ : Q ∈ supported K {v : S × τ | v.1 ∉ A}) : slice A γ Q = γ Q • 1 := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun e he => ?_
  have h := filter_of_supported (q := fun v : S × τ => v.1 ∉ A) hQ he
  beta_reduce at h
  have h2 : e.filter (fun v : S × τ => v.1 ∈ A) = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro v hv
    exact (Finsupp.filter_eq_zero_iff _ _).1 h.2 v (not_not.2 hv)
  have h3 : (monomial e (AddMonoidAlgebra.coeff Q e) : MvPolynomial (S × τ) K) = AddMonoidAlgebra.coeff Q e • monomial e 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [slice_monomial, h.1, h2, ← C_apply, C_1, h3, map_smul, smul_eq_mul]

theorem slice_mul (γ : MvPolynomial (S × τ) K →ₗ[K] K) (P Q : MvPolynomial (S × τ) K)
    (hP : P ∈ supported K {v : S × τ | v.1 ∈ A}) (hQ : Q ∈ supported K {v : S × τ | v.1 ∉ A}) :
    slice A γ (P * Q) = γ Q • P := by
  rw [slice_mul_left A γ P Q hP, slice_spec A γ Q hQ, mul_smul_comm, mul_one]

end Slice

section Tensor

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}

theorem blockEmb_supported (s : S) (F : MvPolynomial (Fin k × Fin n) K) (q : S → Prop) (hs : q s) :
    blockEmb K s F ∈ supported K {v : S × (Fin k × Fin n) | q v.1} := by
  rw [mem_supported]
  intro v hv
  have hv' := vars_rename (fun w : Fin k × Fin n => (s, w)) F (Finset.mem_coe.1 hv)
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv'
  exact hs

theorem prod_split (A : Finset S) (F : S → MvPolynomial (Fin k × Fin n) K) :
    ∏ s, blockEmb K s (F s) =
      (∏ s, blockEmb K s (if s ∈ A then F s else 1)) * ∏ s, blockEmb K s (if s ∈ A then 1 else F s) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  split_ifs <;> simp

theorem slice_tensor (A : Finset S) (M MT Msp : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h1 : ∀ s ∈ A, M s ≤ MT s ∧ (1 : MvPolynomial (Fin k × Fin n) K) ∈ Msp s)
    (h2 : ∀ s, s ∉ A → (1 : MvPolynomial (Fin k × Fin n) K) ∈ MT s ∧ M s ≤ Msp s)
    (γ : MvPolynomial (S × (Fin k × Fin n)) K →ₗ[K] K) (c : K)
    (hγ : ∀ Q ∈ tensorLat R K Msp, ∃ a : R, γ Q = c * algebraMap R K a) :
    ∀ u ∈ tensorLat R K M, ∃ y ∈ tensorLat R K MT, slice A γ u = c • y := by
  intro u hu
  unfold tensorLat at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have hXs : (∏ s, blockEmb K s (if s ∈ A then F s else 1)) ∈
        supported K {v : S × (Fin k × Fin n) | v.1 ∈ A} := by
      refine Subalgebra.prod_mem _ fun s _ => ?_
      split_ifs with h
      · exact blockEmb_supported s _ (· ∈ A) h
      · rw [map_one]; exact one_mem _
    have hYs : (∏ s, blockEmb K s (if s ∈ A then 1 else F s)) ∈
        supported K {v : S × (Fin k × Fin n) | v.1 ∉ A} := by
      refine Subalgebra.prod_mem _ fun s _ => ?_
      split_ifs with h
      · rw [map_one]; exact one_mem _
      · exact blockEmb_supported s _ (· ∉ A) h
    have hYm : (∏ s, blockEmb K s (if s ∈ A then 1 else F s)) ∈ tensorLat R K Msp := by
      unfold tensorLat
      refine Submodule.subset_span ⟨_, fun s => ?_, rfl⟩
      split_ifs with h
      · exact (h1 s h).2
      · exact (h2 s h).2 (hF s)
    obtain ⟨a, ha⟩ := hγ _ hYm
    refine ⟨a • ∏ s, blockEmb K s (if s ∈ A then F s else 1), Submodule.smul_mem _ a ?_, ?_⟩
    · unfold tensorLat
      refine Submodule.subset_span ⟨_, fun s => ?_, rfl⟩
      split_ifs with h
      · exact (h1 s h).1 (hF s)
      · exact (h2 s h).1
    · rw [prod_split A F, slice_mul A γ _ _ hXs hYs, ha, mul_smul, algebraMap_smul]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ea⟩ := hx
    obtain ⟨b, hb, eb⟩ := hy
    exact ⟨a + b, add_mem ha hb, by rw [map_add (f := _), ea, eb, smul_add]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha, ea⟩ := hx
    exact ⟨r • a, Submodule.smul_mem _ r ha, by rw [LinearMap.map_smul_of_tower, ea, smul_comm]⟩

end Tensor

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (kp_lamAt_antitone H0_le_twisted_nabla)

structure Peel {n' m : ℕ} (A : Finset (Fin n')) (X XT sp : Fin n' → Fin (m + 1) → ℤ) : Prop where
  top : ∀ s ∈ A, XT s = X s ∧ sp s = 0
  off : ∀ s, s ∉ A → XT s = 0 ∧ sp s = X s

theorem lamAt_congr {n' m : ℕ} {X Y : Fin n' → Fin (m + 1) → ℤ} {s : Fin n'} (h : X s = Y s) : lamAt X s = lamAt Y s := by
  unfold lamAt
  rw [h]

theorem lamAt_zero {n' m : ℕ} {X : Fin n' → Fin (m + 1) → ℤ} {s : Fin n'} (h : X s = 0) : lamAt X s = 0 := by
  unfold lamAt
  rw [h]
  split_ifs
  · rfl
  · funext i
    simp

theorem nuOf_zero (m : ℕ) : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by
  funext t
  simp [nuOf]

theorem anti_zero (m : ℕ) : Antitone (0 : Fin (m + 1) → ℤ) := fun _ _ _ => le_rfl

theorem one_mem_H0_weight_zero (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (Λ : Submodule O (Fin (m + 1) → Kf)) :
    (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ H0 O m 0 Λ := by
  unfold H0
  rw [if_pos (anti_zero m)]
  simp only [Submodule.mem_iInf]
  rintro g ⟨hg, -⟩
  rw [nablaLTwMem O Kf m 0 g hg]
  refine ⟨1, ?_, ?_⟩
  · have : (fun t : Fin (m + 1) => (((0 : Fin (m + 1) → ℤ) t) - (0 : Fin (m + 1) → ℤ) (Fin.last m)).toNat) = 0 := by
      funext t
      simp
    rw [this]
    exact one_mem_dualWeyl
  · simp

section

variable {Kf : Type} [Field Kf] {n' m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

theorem slice_V (hP : Peel A X XT sp)
    (γ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf) :
    ∀ u ∈ Vsp Kf X, slice A γ u ∈ Vsp Kf XT := by
  intro u hu
  obtain ⟨y, hy, he⟩ := slice_tensor (R := Kf) A
    (fun s => if Antitone (lamAt X s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) else ⊥)
    (fun s => if Antitone (lamAt XT s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt XT s)) else ⊥)
    (fun s => if Antitone (lamAt sp s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt sp s)) else ⊥)
    (fun s hs => ⟨by rw [lamAt_congr (hP.top s hs).1], by
      rw [lamAt_zero (hP.top s hs).2, if_pos (anti_zero m), nuOf_zero]; exact one_mem_dualWeyl⟩)
    (fun s hs => ⟨by rw [lamAt_zero (hP.off s hs).1, if_pos (anti_zero m), nuOf_zero]; exact one_mem_dualWeyl, by
      rw [lamAt_congr (hP.off s hs).2]⟩)
    γ 1 (fun Q _ => ⟨γ Q, by simp⟩) u hu
  rw [he, one_smul]
  exact hy

variable {O : Type} [CommRing O] [Algebra O Kf]

theorem slice_Hten (hP : Peel A X XT sp) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (γ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf) (c : Kf)
    (hγ : ∀ Q ∈ Hten O sp Λ, ∃ a : O, γ Q = c * algebraMap O Kf a) :
    ∀ u ∈ Hten O X Λ, ∃ y ∈ Hten O XT Λ, slice A γ u = c • y :=
  slice_tensor (R := O) A _ _ _
    (fun s hs => ⟨by rw [lamAt_congr (hP.top s hs).1], by
      rw [lamAt_zero (hP.top s hs).2]; exact one_mem_H0_weight_zero O Kf m _⟩)
    (fun s hs => ⟨by rw [lamAt_zero (hP.off s hs).1]; exact one_mem_H0_weight_zero O Kf m _, by
      rw [lamAt_congr (hP.off s hs).2]⟩)
    γ c hγ

theorem Hten_le_V (hd : IsDominant X) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (hΛ : ∀ s, ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ Λ s = colSpan O g) :
    ∀ Q ∈ Hten O X Λ, Q ∈ Vsp Kf X := by
  intro Q hQ
  choose g hg hΛg using hΛ
  have h1 : Q ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt X s) (g s)) := by
    refine Submodule.span_mono ?_ hQ
    rintro _ ⟨F, hF, rfl⟩
    refine ⟨F, fun s => ?_, rfl⟩
    have h0 : F s ∈ H0 O m (lamAt X s) (Λ s) := hF s
    rw [hΛg s] at h0
    exact H0_le_twisted_nabla m _ (kp_lamAt_antitone X hd s) (g s) (hg s) h0
  have h2 := tr_tens_le O Kf m (fun s => lamAt X s) g hg Q h1
  unfold Vsp
  have : (fun s => if Antitone (lamAt X s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) else ⊥) =
      fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) := by
    funext s
    rw [if_pos (kp_lamAt_antitone X hd s)]
  rw [this]
  exact h2

end

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (lb_D lb_D_det)

section Ext

variable {Kf : Type} [Field Kf] {n' m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

theorem exists_ext (G : Module.Dual Kf (Vsp Kf X)) :
    ∃ γ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf, ∀ Q : Vsp Kf X, γ (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = G Q := by
  obtain ⟨γ, hγ⟩ := LinearMap.exists_extend G
  exact ⟨γ, fun Q => by rw [← hγ]; rfl⟩

def extD (G : Module.Dual Kf (Vsp Kf X)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf := (exists_ext G).choose

theorem extD_spec (G : Module.Dual Kf (Vsp Kf X)) (Q : Vsp Kf X) : extD G (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = G Q :=
  (exists_ext G).choose_spec Q

def peelMap (hP : Peel A X XT sp) (c : Kf) (G : Module.Dual Kf (Vsp Kf sp)) : Vsp Kf X →ₗ[Kf] Vsp Kf XT :=
  (c • slice A (extD G)).restrict (fun u hu => Submodule.smul_mem _ _ (slice_V hP _ u hu))

theorem peelMap_coe (hP : Peel A X XT sp) (c : Kf) (G : Module.Dual Kf (Vsp Kf sp)) (u : Vsp Kf X) :
    ((peelMap hP c G u : Vsp Kf XT) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = c • slice A (extD G) (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := rfl

variable {O : Type} [CommRing O] [Algebra O Kf]

theorem peel_Hten (hP : Peel A X XT sp) (hdT : IsDominant XT) (hdsp : IsDominant sp)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (hΛ : ∀ s, ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ Λ s = colSpan O g)
    (c0 c : Kf) (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Qv : Vsp Kf sp, (Qv : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O sp Λ → ∃ a : O, G Qv = c * algebraMap O Kf a)
    (u : Vsp Kf X) (hu : (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O X Λ) :
    ∃ yv : Vsp Kf XT, (yv : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O XT Λ ∧ peelMap hP c0 G u = (c0 * c) • yv := by
  obtain ⟨y, hy, he⟩ := slice_Hten hP Λ (extD G) c (fun Q hQ => by
      obtain ⟨a, ha⟩ := hG ⟨Q, Hten_le_V hdsp Λ hΛ Q hQ⟩ hQ
      exact ⟨a, by rw [← ha]; exact extD_spec G ⟨Q, _⟩⟩) u hu
  refine ⟨⟨y, Hten_le_V hdT Λ hΛ y hy⟩, hy, Subtype.ext ?_⟩
  rw [peelMap_coe, he, smul_smul]
  rfl

end Ext

section Lat

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem Re'_le_scale (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (X : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant X) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) (M : ℕ) (hM : ordMax r X ≤ M) :
    Re' p ι σ w r X e ≤ scale (algebraMap O Kf w ^ (-(M : ℤ))) (dualLat O Kf (HL (O := O) ι σ X e.tgt)) := by
  obtain ⟨I, hI, x, π, _, c2, _, c4, c4', _, c7⟩ := edge_lattice_adapted_basis h m r X hd e he
  have hw := w_ne_zero h
  have hp0 : (p : Kf) ≠ 0 := by rw [Formalism.L2.G.Model.p_eq h]; exact pow_ne_zero _ hw
  rw [← c7, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine mem_scale.2 ⟨w ^ ((M : ℤ) - order r X (π i)).toNat • (((p : Kf) ^ π i)⁻¹ • x.coord i), ?_, ?_⟩
  · rw [← c2, Formalism.L2.G.Model.dualLat_span x (fun i => (p : Kf) ^ π i) (fun i => zpow_ne_zero _ hp0)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have h1 := c4' i
    rw [← algebraMap_smul Kf (w ^ ((M : ℤ) - order r X (π i)).toNat), smul_smul, smul_smul, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega), ← zpow_add₀ hw]
    show _ = ((algebraMap O Kf) w ^ (-order r X (π i)) * (p : Kf) ^ (-π i)) • x.coord i
    rw [zpow_neg (p : Kf)]
    congr 3
    ring

variable {m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

theorem p_zpow (h : HidaSetting p n' W Qq O Kf ι σ j w) (z : ℤ) : (p : Kf) ^ z = algebraMap O Kf w ^ (2 * z) := by
  rw [Formalism.L2.G.Model.p_eq h, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem peel_Re (h : HidaSetting p n' W Qq O Kf ι σ j w) (hP : Peel A X XT sp) (hX : X = XT + sp) (hdT : IsDominant XT)
    (hdsp : IsDominant sp) (r : ℕ) (e' : Edge W Qq (m + 1)) (he' : IsEdge p n' r e') (N : ℤ)
    (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Q ∈ Re p ι σ w r sp e', ∃ a : O, be p r sp Q G = algebraMap O Kf w ^ N * algebraMap O Kf a) :
    ∀ u ∈ Re p ι σ w r X e',
      peelMap hP ((p : Kf) ^ Ar r sp) G u ∈ scale (algebraMap O Kf w ^ N) (Re p ι σ w r XT e') := by
  intro u hu
  have hw := w_ne_zero h
  have hAr : Ar r X = Ar r XT + Ar r sp := by rw [hX]; exact Ar_add r _ _
  obtain ⟨gs, hgs, _, h2, _⟩ := Formalism.L2.G.Model.edgeLat h m r e' he'
  have hΛ : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧
      LeAt p ι σ w s.val e' = colSpan O g := fun s =>
    ⟨_, by rw [Matrix.det_mul]; exact (hgs _).mul (lb_D_det _ _ _ hw), h2 s.val⟩
  obtain ⟨u0, hu0, rfl⟩ := mem_scale.1 hu
  have hu0' : ((u0 : Vsp Kf X) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O X (fun s => LeAt p ι σ w s.val e') := hu0
  obtain ⟨yv, hy, he⟩ := peel_Hten hP hdT hdsp (fun s => LeAt p ι σ w s.val e') hΛ ((p : Kf) ^ Ar r sp)
    (algebraMap O Kf w ^ (N - Ar r sp)) G (by
      intro Qv hQv
      obtain ⟨a, ha⟩ := hG (algebraMap O Kf w ^ (-Ar r sp) • Qv) (mem_scale.2 ⟨Qv, hQv, rfl⟩)
      refine ⟨a, ?_⟩
      rw [be_smulK_left] at ha
      unfold be at ha
      rw [map_smul, smul_eq_mul, p_zpow h, ← mul_assoc, ← zpow_add₀ hw] at ha
      have e1 : -Ar r sp + 2 * Ar r sp = Ar r sp := by ring
      rw [e1] at ha
      rw [zpow_sub₀ hw, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hw), mul_comm]
      exact ha) u0 hu0'
  rw [map_smul, he]
  refine mem_scale.2 ⟨algebraMap O Kf w ^ (-Ar r XT) • yv, mem_scale.2 ⟨yv, hy, rfl⟩, ?_⟩
  rw [smul_smul, smul_smul, p_zpow h, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, hAr]
  congr 2
  ring

theorem peel_HL (hP : Peel A X XT sp) (hdT : IsDominant XT) (hdsp : IsDominant sp)
    (L : Submodule W (Fin (m + 1) → Qq))
    (hL : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ extO O ι σ s.val L = colSpan O g)
    (c0 c : Kf) (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Q ∈ HL (O := O) ι σ sp L, ∃ a : O, G Q = c * algebraMap O Kf a) :
    ∀ u ∈ HL (O := O) ι σ X L, peelMap hP c0 G u ∈ scale (c0 * c) (HL (O := O) ι σ XT L) := by
  intro u hu
  obtain ⟨yv, hy, he⟩ := peel_Hten hP hdT hdsp (fun s => extO O ι σ s.val L) hL c0 c G (fun Qv hQv => hG Qv hQv) u hu
  exact mem_scale.2 ⟨yv, hy, he.symm⟩

end Lat

theorem dualWeyl_zero_const {R : Type} [CommRing R] {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) R)
    (hF : F ∈ dualWeyl R r n 0) : F = C (AddMonoidAlgebra.coeff F 0) := by
  classical
  have h1 : IsWeightedHomogeneous (colW r n) F 0 := (mem_dualWeyl_iff.1 hF).1
  ext e
  rw [coeff_C]
  split_ifs with he
  · rw [he]
  · apply h1.coeff_eq_zero
    intro hwt
    apply he
    symm
    ext v
    have h2 := congrFun hwt v.2
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h2
    by_contra hv
    have h3 := (Finset.sum_eq_zero_iff.1 h2) v (Finsupp.mem_support_iff.2 (by simpa using hv))
    simp [colW] at h3
    exact hv (by simpa using h3)

end Formalism.MainNotions.TestSideCounting
