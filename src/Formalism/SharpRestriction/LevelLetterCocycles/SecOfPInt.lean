module

public import Formalism.SharpRestriction.LevelLetterCocycles.MembershipCriterionOfLevelZero
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.JumpsLetExists

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LinearIdentityHeadDifference
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FilCrisTriv
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

section Funct

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} (f : V →ₗ[LL] V')

theorem crisMap_φVB (z : V ⊗[Qp] B) :
    crisMap B f (φVB PD (LL := LL) (V := V) z) = φVB PD (LL := LL) (V := V') (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [crisMap, φVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem crisMap_φVB_pow (s : ℕ) (z : V ⊗[Qp] B) :
    crisMap B f (((φVB PD (LL := LL) (V := V)) ^ s) z) =
      ((φVB PD (LL := LL) (V := V')) ^ s) (crisMap B f z) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', pow_succ']
    exact (crisMap_φVB PD f _).trans (congrArg (φVB PD (LL := LL) (V := V')) ih)

theorem act_φVB (g : G) (z : V ⊗[Qp] B) :
    actVB PD ρ g (φVB PD (LL := LL) (V := V) z) = φVB PD (LL := LL) (V := V) (actVB PD ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [actVB, φVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem φVB_Dcris {z : V ⊗[Qp] B} (hz : z ∈ Dcris PD ρ) : φVB PD (LL := LL) (V := V) z ∈ Dcris PD ρ := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz ⊢
  intro g
  rw [act_φVB, hz g]

theorem φVB_pow_Dcris (s : ℕ) {z : V ⊗[Qp] B} (hz : z ∈ Dcris PD ρ) :
    ((φVB PD (LL := LL) (V := V)) ^ s) z ∈ Dcris PD ρ := by
  induction s with
  | zero => simpa using hz
  | succ s ih =>
    rw [pow_succ']
    exact φVB_Dcris PD ih

theorem act_mulVB (g : G) (c : K₀) (z : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (LL := LL) (V := V) (B := B) c z) = mulVB (LL := LL) (V := V) (B := B) c (actVB PD ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp [actVB, mulVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mulVB_Dcris (c : K₀) {z : V ⊗[Qp] B} (hz : z ∈ Dcris PD ρ) :
    mulVB (LL := LL) (V := V) (B := B) c z ∈ Dcris PD ρ := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz ⊢
  intro g
  rw [act_mulVB, hz g]

theorem coord_ιV {ι₀ : Type} (b : Module.Basis ι₀ Qp V) (i : ι₀) (z : V ⊗[Qp] B) :
    Formalism.MainNotions.LiftingTheory.lone_coord b i BdR (ιV PD (LL := LL) (V := V) z) = PD.ι (Formalism.MainNotions.LiftingTheory.lone_coord b i B z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    simp [Formalism.MainNotions.LiftingTheory.lone_coord, ιV, Algebra.smul_def, IsScalarTower.algebraMap_apply Qp K₀ B,
      IsScalarTower.algebraMap_apply Qp K₀ BdR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem tensor_eq_sum_lemma {n : ℕ} (b : Module.Basis (Fin n) Qp V) (C : Type) [AddCommGroup C]
    [Module Qp C] (z : V ⊗[Qp] C) :
    z = ∑ i, b i ⊗ₜ[Qp] Formalism.MainNotions.LiftingTheory.lone_coord b i C z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    have e : (∑ i, b i ⊗ₜ[Qp] Formalism.MainNotions.LiftingTheory.lone_coord b i C (v ⊗ₜ[Qp] c)) =
        (∑ i, b.repr v i • b i) ⊗ₜ[Qp] c := by
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul]
      simp [Formalism.MainNotions.LiftingTheory.lone_coord]
    rw [e, Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) hx hy

private theorem coord_act_lemma_2 (hρ : ∀ g x, ρ g x = x) {n : ℕ} (b : Module.Basis (Fin n) Qp V) (i : Fin n)
    (g : G) (z : V ⊗[Qp] B) :
    Formalism.MainNotions.LiftingTheory.lone_coord b i B (actVB PD ρ g z) = PD.actB g (Formalism.MainNotions.LiftingTheory.lone_coord b i B z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    simp [Formalism.MainNotions.LiftingTheory.lone_coord, actVB, hρ, Algebra.smul_def, IsScalarTower.algebraMap_apply Qp K₀ B]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem coord_map_lemma_3 {n : ℕ} (b : Module.Basis (Fin n) Qp V) (i : Fin n) {C D : Type}
    [AddCommGroup C] [Module Qp C] [AddCommGroup D] [Module Qp D] (g : C →ₗ[Qp] D) (w : V ⊗[Qp] C) :
    Formalism.MainNotions.LiftingTheory.lone_coord b i D (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) g w) =
      g (Formalism.MainNotions.LiftingTheory.lone_coord b i C w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [Formalism.MainNotions.LiftingTheory.lone_coord]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem fil_le_lemma_4 (a : ℤ) (k : ℕ) : PD.Fil (a + (k : ℤ)) ≤ PD.Fil a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a + ((k + 1 : ℕ) : ℤ) = (a + k) + 1 := by push_cast; ring
    rw [e]
    exact le_trans (PD.Fil_anti (a + k)) ih

private theorem fil_one_lemma_5 (h1 : (1 : BdR) ∈ PD.Fil 1) (a : ℤ) : (1 : BdR) ∈ PD.Fil a := by
  have hn : ∀ m : ℕ, (1 : BdR) ∈ PD.Fil (m : ℤ) := by
    intro m
    induction m with
    | zero => simpa using PD.one_mem
    | succ m ih =>
      have h := PD.Fil_mul 1 (m : ℤ) 1 1 h1 ih
      rw [mul_one, show (1 : ℤ) + (m : ℤ) = ((m + 1 : ℕ) : ℤ) by push_cast; ring] at h
      exact h
  rcases le_or_gt a 0 with ha | ha
  · have hle := fil_le_lemma_4 PD a (Int.toNat (-a))
    have e : a + ((Int.toNat (-a) : ℕ) : ℤ) = 0 := by
      rw [Int.toNat_of_nonneg (by omega)]; omega
    rw [e] at hle
    exact hle PD.one_mem
  · rw [← Int.toNat_of_nonneg ha.le]
    exact hn _

private theorem fil_const_lemma_6 (u : ℤ) (hu : 1 ≤ u) (k : K) (hk : algebraMap K BdR k ∈ PD.Fil u) :
    algebraMap K BdR k = 0 := by
  by_cases h0 : k = 0
  · simp [h0]
  · have h1u : (1 : BdR) ∈ PD.Fil u := by
      have h := (PD.Fil u).smul_mem k⁻¹ hk
      rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h0, map_one] at h
    have hle := fil_le_lemma_4 PD 1 (Int.toNat (u - 1))
    have e : (1 : ℤ) + ((Int.toNat (u - 1) : ℕ) : ℤ) = u := by
      rw [Int.toNat_of_nonneg (by omega)]; omega
    rw [e] at hle
    have h10 : (1 : BdR) = 0 := PD.Fil_sep 1 (fun a => fil_one_lemma_5 PD (hle h1u) a)
    rw [← mul_one (algebraMap K BdR k), h10, mul_zero]

theorem filCris_triv [FiniteDimensional Qp V] (hρ : ∀ g x, ρ g x = x) (u : ℤ) (hu : 1 ≤ u) {z : V ⊗[Qp] B}
    (hz : z ∈ FilCris PD ρ u) : z = 0 := by
  rw [FilCris, Submodule.mem_inf] at hz
  obtain ⟨hD, hF⟩ := hz
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hD
  rw [Submodule.mem_comap, FilV, LinearMap.mem_range] at hF
  obtain ⟨w, hw⟩ := hF
  have b : Module.Basis (Fin (Module.finrank Qp V)) Qp V := Module.finBasis Qp V
  have key : ∀ i, Formalism.MainNotions.LiftingTheory.lone_coord b i B z = 0 := by
    intro i
    have hinv : ∀ g, PD.actB g (Formalism.MainNotions.LiftingTheory.lone_coord b i B z) = Formalism.MainNotions.LiftingTheory.lone_coord b i B z := by
      intro g
      rw [← coord_act_lemma_2 PD hρ b i g z, hD g]
    obtain ⟨k, hk⟩ := PD.invB _ hinv
    have hι : PD.ι (Formalism.MainNotions.LiftingTheory.lone_coord b i B z) ∈ PD.Fil u := by
      rw [← coord_ιV PD (LL := LL) b i z, ← hw, coord_map_lemma_3 (LL := LL) b i]
      exact (Formalism.MainNotions.LiftingTheory.lone_coord b i _ w).2
    rw [← hk] at hι ⊢
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR] at hι
    have h0 := fil_const_lemma_6 PD u hu _ hι
    rw [← IsScalarTower.algebraMap_apply K₀ K BdR, ← PD.ι.commutes] at h0
    apply PD.ι_inj
    rw [h0, map_zero]
  rw [tensor_eq_sum_lemma b B z]
  simp [key]

end Funct

section SES

theorem ses_exact (hK : Function.Bijective (algebraMap K₀ K)) (h9 : DcrisExactStrict PD LL)
    (T₂ Y T₀ : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L T₀.L) (hses : IsSESLat (Qp := Qp) ι π)
    (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (h0 : IsCrys PD T₀.ρ) :
    (∀ y ∈ Dcris PD T₂.ρ, crisMap B ι.f y = 0 → y = 0) ∧
      (∀ x ∈ Dcris PD Y.ρ, crisMap B π.f x = 0 → ∃ y ∈ Dcris PD T₂.ρ, crisMap B ι.f y = x) := by
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (hses.2.2.2.1 x).symm
  obtain ⟨e1, e2, -⟩ := h9 hK T₂.V Y.V T₀.V T₂.ρ Y.ρ T₀.ρ ι.f π.f T₂.cont Y.cont T₀.cont ι.equiv π.equiv
    hses.1 hses.2.1 hrk h2 hY h0
  exact ⟨e1, e2⟩

variable {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private theorem crisMap_rT_lemma_9 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (C : Type) [CommRing C] [Algebra Qp C]
    (f : V →ₗ[LL] V') (x : V ⊗[Qp] C) :
    crisMap C f x = LinearMap.rTensor C (f.restrictScalars Qp) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [crisMap]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem crisMap_inj_lemma_10 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (C : Type) [CommRing C] [Algebra Qp C]
    (f : V →ₗ[LL] V') (hf : Function.Injective f) : Function.Injective (crisMap (Qp := Qp) C f) := by
  intro x y h
  rw [crisMap_rT_lemma_9 C f x, crisMap_rT_lemma_9 C f y] at h
  have hi : Function.Injective (LinearMap.rTensor C (f.restrictScalars Qp)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hf
  exact hi h

private theorem crisMap_exact_lemma_11 {V₀ V V' : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀] [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (C : Type) [CommRing C] [Algebra Qp C]
    (f : V₀ →ₗ[LL] V) (g : V →ₗ[LL] V') (hfg : ∀ x, g x = 0 ↔ ∃ y, f y = x) (hg : Function.Surjective g)
    (x : V ⊗[Qp] C) (hx : crisMap C g x = 0) : ∃ y, crisMap C f y = x := by
  rw [crisMap_rT_lemma_9] at hx
  have hex : Function.Exact (f.restrictScalars Qp) (g.restrictScalars Qp) := by
    intro x
    rw [Set.mem_range]
    exact hfg x
  obtain ⟨y, hy⟩ := (rTensor_exact C hex hg x).1 hx
  exact ⟨y, by rw [crisMap_rT_lemma_9]; exact hy⟩

private theorem crisMap_act_lemma_12 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] {ρ : Representation LL G V}
    {ρ' : Representation LL G V'} (f : V →ₗ[LL] V') (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (z : V ⊗[Qp] B) :
    crisMap B f (actVB PD ρ g z) = actVB PD ρ' g (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [crisMap, actVB, hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem algmap_lT_lemma_15 {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U] {C D : Type} [AddCommGroup C] [Module Qp C]
    [AddCommGroup D] [Module Qp D] (g : C →ₗ[Qp] D) (w : U ⊗[Qp] C) :
    AlgebraTensorModule.map (LinearMap.id : U →ₗ[LL] U) g w = LinearMap.lTensor U g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem filV_iff_lemma_13 {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U] (a : ℤ) (y : U ⊗[Qp] BdR) :
    y ∈ FilV PD (LL := LL) (V := U) a ↔ LinearMap.lTensor U ((PD.Fil a).restrictScalars Qp).mkQ y = 0 := by
  have hex := lTensor_exact U (LinearMap.exact_subtype_mkQ ((PD.Fil a).restrictScalars Qp))
    (Submodule.mkQ_surjective ((PD.Fil a).restrictScalars Qp))
  rw [hex y, FilV, LinearMap.mem_range, Set.mem_range]
  simp only [algmap_lT_lemma_15]

private theorem comm_q_lemma_21 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR) :
    LinearMap.lTensor V' ((PD.Fil a).restrictScalars Qp).mkQ (LinearMap.rTensor BdR (f.restrictScalars Qp) x) =
      LinearMap.rTensor (BdR ⧸ (PD.Fil a).restrictScalars Qp) (f.restrictScalars Qp)
        (LinearMap.lTensor V ((PD.Fil a).restrictScalars Qp).mkQ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem filV_strict_lemma_16 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (hf : Function.Injective f)
    (a : ℤ) (x : V ⊗[Qp] BdR) (hx : crisMap BdR f x ∈ FilV PD (LL := LL) (V := V') a) :
    x ∈ FilV PD (LL := LL) (V := V) a := by
  rw [filV_iff_lemma_13 PD] at hx
  rw [filV_iff_lemma_13 PD]
  rw [crisMap_rT_lemma_9] at hx
  have hc := comm_q_lemma_21 PD f a x
  rw [hc] at hx
  have hi : Function.Injective (LinearMap.rTensor (BdR ⧸ (PD.Fil a).restrictScalars Qp) (f.restrictScalars Qp)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hf
  exact hi (hx.trans (map_zero _).symm)

private theorem filV_fwd_lemma_20 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) : crisMap BdR f x ∈ FilV PD (LL := LL) (V := V') a := by
  rw [filV_iff_lemma_13 PD] at hx
  rw [filV_iff_lemma_13 PD, crisMap_rT_lemma_9]
  have hc := comm_q_lemma_21 PD f a x
  rw [hc, hx, map_zero]

private theorem crisMap_iV_lemma_17 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (z : V ⊗[Qp] B) :
    crisMap BdR f (ιV PD (LL := LL) (V := V) z) = ιV PD (LL := LL) (V := V') (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [crisMap, ιV]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem crisMap_mulVB_lemma_19 {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (c : K₀) (z : V ⊗[Qp] B) :
    crisMap B f (mulVB (LL := LL) (V := V) (B := B) c z) = mulVB (LL := LL) (V := V') (B := B) c (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp [crisMap, mulVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fil_pull [FiniteDimensional Qp LL] (W : LocWach PD LL O v n)
    (hK : Function.Bijective (algebraMap K₀ K)) (h9 : DcrisExactStrict PD LL)
    (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (hses : IsSESLat (Qp := Qp) ι π)
    (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (u : ℤ) (hu : 1 ≤ u) (τ₀ : K₀ →ₐ[Qp] LL)
    {ν : Y.V ⊗[Qp] B} (hν : ν ∈ FilCris PD Y.ρ u ⊓ DcrisL PD Y.ρ τ₀) :
    ∃ μ ∈ FilCris PD T₂.ρ u ⊓ DcrisL PD T₂.ρ τ₀, crisMap B ι.f μ = ν := by
  haveI : FiniteDimensional Qp W.one.V := Module.Finite.trans LL W.one.V
  obtain ⟨hνF, hνL⟩ := Submodule.mem_inf.1 hν
  rw [FilCris, Submodule.mem_inf] at hνF
  obtain ⟨hνD, hνV⟩ := hνF
  have hπD : crisMap B π.f ν ∈ Dcris PD W.one.ρ := by
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hνD ⊢
    intro g
    rw [← crisMap_act_lemma_12 PD π.f π.equiv, hνD g]
  have hπV : crisMap B π.f ν ∈
      (FilV PD (LL := LL) (V := W.one.V) u).comap (ιV PD (LL := LL) (V := W.one.V)) := by
    rw [Submodule.mem_comap, ← crisMap_iV_lemma_17 PD π.f]
    rw [Submodule.mem_comap] at hνV
    exact filV_fwd_lemma_20 PD π.f u _ hνV
  have hπ0 : crisMap B π.f ν = 0 :=
    filCris_triv PD W.94 u hu (by rw [FilCris, Submodule.mem_inf]; exact ⟨hπD, hπV⟩)
  obtain ⟨μ, hμ⟩ := crisMap_exact_lemma_11 B ι.f π.f hses.2.2.2.1 hses.2.1 ν hπ0
  have hinj := crisMap_inj_lemma_10 (Qp := Qp) B ι.f hses.1
  have hμD : μ ∈ Dcris PD T₂.ρ := by
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hνD ⊢
    intro g
    apply hinj
    rw [crisMap_act_lemma_12 PD ι.f ι.equiv, hμ, hνD g]
  have hμF : μ ∈ FilCris PD T₂.ρ u := by
    rw [FilCris, Submodule.mem_inf, Submodule.mem_comap]
    refine ⟨hμD, filV_strict_lemma_16 PD ι.f hses.1 u _ ?_⟩
    rw [crisMap_iV_lemma_17 PD ι.f, hμ]
    rw [Submodule.mem_comap] at hνV
    exact hνV
  have hμL : μ ∈ DcrisL PD T₂.ρ τ₀ := by
    rw [DcrisL, Submodule.mem_inf] at hνL ⊢
    refine ⟨hμD, ?_⟩
    have hνL2 := hνL.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hνL2 ⊢
    intro c
    apply hinj
    rw [crisMap_mulVB_lemma_19 ι.f, map_smul, hμ, hνL2 c]
  exact ⟨μ, Submodule.mem_inf.2 ⟨hμF, hμL⟩, hμ⟩

end SES

end Formalism.MainNotions.UnusedSlot80.SplitP
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup

theorem lin_map {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {d dY : ℕ} (l Λ : R) (κ κY κ' K : ℕ)
    (u : M) (X : Fin d → M) (Z : Fin dY → M) (a : Fin d → R) (o : Fin d → Fin dY → R) :
    l ^ (κ' + K) • (l ^ (κ + κY) • Λ • u - ∑ j, (∑ k, a k * o k j) • (l ^ κ • Z j)) =
      l ^ K • l ^ κY • (l ^ κ' • (l ^ κ • Λ • u - ∑ k, a k • X k)) +
        l ^ κ' • ∑ k, a k • (l ^ K • (l ^ κY • X k - l ^ κ • ∑ j, o k j • Z j)) := by
  have e1 : ∑ j, (∑ k, a k * o k j) • (l ^ κ • Z j) = ∑ k, a k • (l ^ κ • ∑ j, o k j • Z j) := by
    simp only [Finset.sum_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by module
  set Yv : Fin d → M := fun k => ∑ j, o k j • Z j with hYv
  have e2 : ∑ k, a k • (l ^ K • (l ^ κY • X k - l ^ κ • Yv k)) =
      l ^ K • l ^ κY • ∑ k, a k • X k - l ^ K • ∑ k, a k • (l ^ κ • Yv k) := by
    rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by module
  rw [e1, e2]
  module

theorem linear_identity_head_difference {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (l π : R) (κ κY : ℕ)
    (S E U SY : M) :
    l ^ κY • (l ^ κ • (S + π • E) + π • U) - l ^ κ • (l ^ κY • S + π • SY) =
      π • (l ^ (κY + κ) • E + l ^ κY • U - l ^ κ • SY) := by
  module

theorem linear_identity_tail_difference {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (l π : R) (κ κY M' : ℕ)
    (U X S Z : M) :
    (l ^ κY • (U + π ^ M' • X) - l ^ κ • (S + π ^ M' • Z)) - (l ^ κY • U - l ^ κ • S) =
      π ^ M' • (l ^ κY • X - l ^ κ • Z) := by
  module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem horTr_split (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (c : ZMod n)
    {d : ℕ} (b : Fin d → W.DD T) (hb : ∀ m, Formalism.MainNotions.LiftingTheory.InNΔi W T c (b m)) (hπ : W.π₀ ∈ W.AΔ)
    (sol : Fin d → ℕ → Fin d → LL) (hsol0 : ∀ k, sol k 0 = Pi.single k 1) (M κ : ℕ) (hM : 1 ≤ M) (k : Fin d)
    {H : W.DD T} (h : IsHorTr W T b sol M κ k H) :
    ∃ S, Formalism.MainNotions.LiftingTheory.InNΔi W T c S ∧ H = lA W ^ κ • b k + W.π₀ • S := by
  obtain ⟨y, hy, rfl⟩ := h
  have hy0 : ∀ m, y 0 m = if m = k then ((PD.p : ℕ) : O) ^ κ else 0 := by
    intro m
    apply hinj
    rw [hy 0 hM m, hsol0 k]
    by_cases hm : m = k
    · subst hm; simp
    · simp [hm, Pi.single_apply]
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  refine ⟨∑ r ∈ Finset.range M', W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y (r + 1)),
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W T c _ _ fun r _ =>
      Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (W.AΔ.pow_mem hπ r)
        (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W T c _ _ fun m _ => Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_osmul W T c _ (hb m)), ?_⟩
  rw [Finset.sum_range_succ', pow_zero, one_smul, add_comm, Finset.smul_sum]
  congr 1
  · rw [LevC.lA_smul_eq]
    unfold Formalism.MainNotions.LiftingTheory.vecB
    simp only [hy0, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_smul, ← pow_succ']

theorem horTr_γ (T : LocLat G Qp LL O) (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c b sol) (M κ : ℕ) (k : Fin d) {H : W.DD T}
    (h : IsHorTr W T b sol M κ k H) :
    ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧ W.γ T H - H = W.π₀ ^ M • x := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨x, hx, hxe⟩ := (hb.2 k).1 M κ y hy
  refine ⟨x, hx, ?_⟩
  rw [← hxe, smul_zero, sub_zero]

variable [IsDomain O]

theorem γ_lA (T : LocLat G Qp LL O) (t : ℕ) (z : W.DD T) : W.γ T (lA W ^ t • z) = lA W ^ t • W.γ T z := by
  rw [LevC.lA_smul_eq, map_smul, ← LevC.lA_smul_eq]

variable [NeZero n]

theorem frame_const (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {T₂ Y : LocLat G Qp LL O} (ι : LatHom T₂.L Y.L)
    (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (c' : ZMod n) {d dY : ℕ} (b : Fin d → W.DD T₂)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T₂ c' b) (bY : Fin dY → W.DD Y) (hbY : Formalism.MainNotions.LiftingTheory.IsFrameΔ W Y c' bY)
    (k : Fin d) :
    ∃ (m : Fin dY → LetA O n), (∀ j, m j ∈ W.AΔ ∧ letE c' * m j = m j) ∧
      W.map ι (b k) = ∑ j, m j • bY j ∧
      ∃ E, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' E ∧
        W.map ι (b k) - ∑ j, PowerSeries.constantCoeff (m j c') • bY j = W.π₀ • E := by
  have hx := Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W ι h2 hY c' (hb.1 k)
  obtain ⟨m, ⟨hm, hmx⟩, -⟩ := hbY.2 _ hx
  refine ⟨m, hm, hmx, ?_⟩
  set o : Fin dY → O := fun j => PowerSeries.constantCoeff (m j c') with ho
  have hdv : ∀ j, ∃ g ∈ W.AΔ, m j - letE c' * algebraMap O (LetA O n) (o j) = W.π₀ * g := by
    intro j
    refine Formalism.MainNotions.N.Pv.LocalLengthBound.frobenius_uniformizer_pow_dvd (c := c') hR (W.AΔ.sub_mem (hm j).1
      (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W c') (W.AΔ.algebraMap_mem _))) ?_ ?_
    · rw [mul_sub, (hm j).2, ← mul_assoc, Formalism.MainNotions.N.Pv.LocalLengthBound.letE_sq]
    · have := Formalism.MainNotions.UnusedSlot80.ArcF.ev_apply c' (m j - letE c' * algebraMap O (LetA O n) (o j))
      rw [← this, map_sub, map_mul, Formalism.MainNotions.UnusedSlot80.ArcF.ev_letE, Formalism.MainNotions.UnusedSlot80.ArcF.ev_alg, one_mul,
        Formalism.MainNotions.UnusedSlot80.ArcF.ev_apply, sub_self]
  choose g hg hge using hdv
  have hbl : ∀ j, (letE c' : LetA O n) • bY j = bY j := fun j =>
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_letter W Y c' (hbY.1 j)
  refine ⟨∑ j, g j • bY j, Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W Y c' _ _ fun j _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W Y c' (hg j) (hbY.1 j), ?_⟩
  rw [hmx, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : o j • bY j = (letE c' * algebraMap O (LetA O n) (o j)) • bY j := by
    rw [mul_comm, mul_smul, hbl j, algebraMap_smul]
  rw [e1, ← sub_smul, hge j, mul_smul]

theorem hor_diff (C : LevC.Ctx W) {T₂ Y : LocLat G Qp LL O} (ι : LatHom T₂.L Y.L)
    (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (A : ArcP n) (hA : A.OK) (a : ZMod n) (c' : ZMod n) (e : ℕ)
    {d dY : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T₂ c' b sol)
    (bY : Fin dY → W.DD Y) (solY : Fin dY → ℕ → Fin dY → LL) (hbY : IsHor W Y c' bY solY)
    (κ κY : ℕ) (Hh : Fin d → W.DD T₂) (HhY : Fin dY → W.DD Y)
    (hHh : ∀ k, IsHorTr W T₂ b sol (A.M PD.p) κ k (Hh k)) (hHhY : ∀ j, IsHorTr W Y bY solY (A.M PD.p) κY j (HhY j))
    (o : Fin d → Fin dY → O)
    (ho : ∀ k, ∃ E, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' E ∧ W.map ι (b k) - ∑ j, o k j • bY j = W.π₀ • E) (k : Fin d) :
    ∃ K : ℕ, InFP W Y c' e (W.π₀ * abelian₂ W A a e ^ 2)
      (lA W ^ K • ((W.φD Y) ^ e) (lA W ^ κY • W.map ι (Hh k) - lA W ^ κ • ∑ j, o k j • HhY j)) := by
  have hM : 1 ≤ A.M PD.p := by unfold ArcP.M; exact Nat.le_add_left 1 _
  have hπ := C.hR.1
  obtain ⟨S, hS, hSe⟩ := horTr_split W C.hinj T₂ c' b (fun m => hb.1.1 m) hπ sol (fun k => (hb.2 k).2) _ κ hM k (hHh k)
  have hSY : ∀ j, ∃ S, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' S ∧ HhY j = lA W ^ κY • bY j + W.π₀ • S := fun j =>
    horTr_split W C.hinj Y c' bY (fun m => hbY.1.1 m) hπ solY (fun k => (hbY.2 k).2) _ κY hM j (hHhY j)
  choose SY hSY hSYe using hSY
  obtain ⟨E, hE, hEe⟩ := ho k
  obtain ⟨x, hx, hxe⟩ := horTr_γ W T₂ c' b sol hb _ κ k (hHh k)
  have hxY : ∀ j, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' x ∧ W.γ Y (HhY j) - HhY j = W.π₀ ^ (A.M PD.p) • x := fun j =>
    horTr_γ W Y c' bY solY hbY _ κY j (hHhY j)
  choose xY hxY hxYe using hxY
  set D : W.DD Y := lA W ^ κY • W.map ι (Hh k) - lA W ^ κ • ∑ j, o k j • HhY j with hD
  have hmapS := Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W ι h2 hY c' hS
  have hmapx := Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W ι h2 hY c' hx

  have hD1 : ∃ E', Formalism.MainNotions.LiftingTheory.InNΔi W Y c' E' ∧ D = W.π₀ • E' := by
    refine ⟨lA W ^ (κY + κ) • E + lA W ^ κY • W.map ι S - lA W ^ κ • ∑ j, o k j • SY j,
      Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W Y c'
        (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_add W Y c' (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ hE)
          (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ hmapS))
        (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W Y c' _ _ fun j _ =>
          Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_osmul W Y c' _ (hSY j))), ?_⟩
    have hmk : W.map ι (b k) = ∑ j, o k j • bY j + W.π₀ • E := by rw [← hEe]; abel
    have s1 : ∑ j, o k j • (lA W ^ κY • bY j) = lA W ^ κY • ∑ j, o k j • bY j := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    have s2 : ∑ j, o k j • (W.π₀ • SY j) = W.π₀ • ∑ j, o k j • SY j := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    have s12 : ∑ j, o k j • HhY j = lA W ^ κY • ∑ j, o k j • bY j + W.π₀ • ∑ j, o k j • SY j := by
      simp only [hSYe, smul_add, Finset.sum_add_distrib]
      rw [s1, s2]
    rw [hD, hSe, map_add (f := _), Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul, Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul, hmk, s12]
    exact linear_identity_head_difference _ _ _ _ _ _ _ _
  have hγT := sub_eq_iff_eq_add'.1 hxe
  have hγι : W.γ Y (W.map ι (Hh k)) = W.map ι (Hh k) + W.π₀ ^ (A.M PD.p) • W.map ι x := by
    rw [show W.γ Y (W.map ι (Hh k)) = W.map ι (W.γ T₂ (Hh k)) from (W.map_γ ι W.gam (Hh k)).symm, hγT,
      map_add, Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul]
  have hγY : ∀ j, W.γ Y (HhY j) = HhY j + W.π₀ ^ (A.M PD.p) • xY j := fun j => sub_eq_iff_eq_add'.1 (hxYe j)
  have hD2 : ∃ z, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' z ∧ W.γ Y D - D = W.π₀ ^ (A.M PD.p) • z := by
    refine ⟨lA W ^ κY • W.map ι x - lA W ^ κ • ∑ j, o k j • xY j,
      Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W Y c' (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ hmapx)
        (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W Y c' _ _ fun j _ =>
          Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_osmul W Y c' _ (hxY j))), ?_⟩
    have s3 : ∑ j, o k j • (W.π₀ ^ (A.M PD.p) • xY j) = W.π₀ ^ (A.M PD.p) • ∑ j, o k j • xY j := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    have s4 : W.γ Y (∑ j, o k j • HhY j) = ∑ j, o k j • HhY j + W.π₀ ^ (A.M PD.p) • ∑ j, o k j • xY j := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hγY, smul_add, Finset.sum_add_distrib]
      rw [s3]
    rw [hD, map_sub, γ_lA, γ_lA, hγι, s4]
    exact linear_identity_tail_difference _ _ _ _ _ _ _ _ _
  obtain ⟨K, x', hx', hK⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.formal_unique W Y c' C.hinj C.hO2 hπ C.hR.2.2.1
    (C.hH C.hCA Y hY c').1 (C.hH C.hCA Y hY c').2.1 (A.M PD.p) D hD1 hD2
  obtain ⟨ν, hν, hνe⟩ := LevC.yM_gen W C.hTr C.hCA hπ C.h5p A hA a e
  refine ⟨K, ν • ((W.φD Y) ^ e) x', Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W Y c' e hν hx', ?_⟩
  rw [← Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul, hK, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, map_pow, hνe, mul_smul]

theorem inFP_sum (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) {ι₀ : Type} (s : Finset ι₀)
    (z : ι₀ → W.DD T) (h : ∀ i ∈ s, InFP W T c e f (z i)) : InFP W T c e f (∑ i ∈ s, z i) := by
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c e f
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c e f (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem repVV_map (C : LevC.Ctx W) {T₂ Y : LocLat G Qp LL O} (ι : LatHom T₂.L Y.L)
    (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (A : ArcP n) (hA : A.OK) (a : ZMod n) (c' : ZMod n) (e : ℕ)
    {d dY : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T₂ c' b sol)
    (bY : Fin dY → W.DD Y) (solY : Fin dY → ℕ → Fin dY → LL) (hbY : IsHor W Y c' bY solY)
    (o : Fin d → Fin dY → O)
    (ho : ∀ k, ∃ E, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' E ∧ W.map ι (b k) - ∑ j, o k j • bY j = W.π₀ • E)
    {x : W.DD T₂} {F : Fin d → W.EE} (hF : RepVV W T₂ c' e (A.M PD.p) (abelian₂ W A a e) b sol x F) :
    RepVV W Y c' e (A.M PD.p) (abelian₂ W A a e) bY solY (W.map ι x)
      (fun j => ∑ k, F k * algebraMap O W.EE (o k j)) := by
  obtain ⟨κ, κ', Hh, aa, hHh, haa, hP⟩ := hF
  obtain ⟨κY, HhY, hHhY⟩ := LevC.horTr_exists W C.hO2 C.hH C.hCA Y hY c' bY solY hbY (A.M PD.p)
  choose K hK using fun k => hor_diff W C ι h2 hY A hA a c' e b sol hb bY solY hbY κ κY Hh HhY hHh hHhY o ho k
  set Kt : ℕ := ∑ k, K k with hKt
  set Λ : LetA O n := abelian₂ W A a e with hΛ
  refine ⟨κ + κY, κ' + Kt, fun j => lA W ^ κ • HhY j,
    fun j => ∑ k, aa k * algebraMap O (LetA O n) (o k j),
    fun j => by rw [add_comm κ κY]; exact LevC.horTr_scale W Y bY solY _ κY κ j (hHhY j),
    fun j => ⟨W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (haa k).1 (W.AΔ.algebraMap_mem _), ?_⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, (haa k).2, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  · simp only [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul]
    rw [lin_map (lA W) Λ κ κY κ' Kt (W.map ι x) (fun k => ((W.φD Y) ^ e) (W.map ι (Hh k)))
      (fun j => ((W.φD Y) ^ e) (HhY j)) aa (fun k j => algebraMap O (LetA O n) (o k j))]
    refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W Y c' e _ ?_ ?_
    · refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W _)
        (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W _) ?_)
      have := Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_map W ι h2 hY c' e _ hP
      convert this using 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul, map_sub, map_sum, Formalism.MainNotions.UnusedSlot80.Relay2.map_φpow]
    · refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W _)
        (inFP_sum W Y c' e _ _ _ fun k _ => Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (haa k).1 ?_)
      have hle : K k ≤ Kt := Finset.single_le_sum (fun i _ => Nat.zero_le (K i)) (Finset.mem_univ k)
      have := Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W (Kt - K k)) (hK k)
      convert this using 1
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hle]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul, map_sum, map_smul, algebraMap_smul]

theorem dv_map {T₂ Y : LocLat G Qp LL O} (ι : LatHom T₂.L Y.L) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ)
    (c' : ZMod n) (e : ℕ) {d dY : ℕ} (b : Fin d → W.DD T₂) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T₂ c' b)
    (bY : Fin dY → W.DD Y) (hbY : Formalism.MainNotions.LiftingTheory.IsFrameΔ W Y c' bY) (k : Fin d) (m : Fin dY → LetA O n)
    (hmx : W.map ι (b k) = ∑ j, m j • bY j) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (PowerSeries.constantCoeff (m j c')) • dv W Y e bY (Pi.single j 1) := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.dv_single, crisMap_φVB_pow PD]
  have hbN := (hb.1 k).1.1
  have hmN := W.map_N ι h2 hY _ hbN
  have e1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B ι.f (cmpD W T₂ (b k)) = cmpD W Y (W.map ι (b k)) := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T₂ hbN, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W Y hmN]
    exact (W.cmp_map ι h2 hY ⟨b k, hbN⟩ hmN).symm
  have hsum : ∑ j, m j • bY j ∈ W.N Y := hmx ▸ hmN
  have e2 : cmpD W Y (W.map ι (b k)) = W.cmp Y ⟨∑ j, m j • bY j, hsum⟩ := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W Y hmN]
    congr 1
    exact Subtype.ext hmx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, e2, Formalism.MainNotions.UnusedSlot80.ArcF.cmp_sum_letter W Y c' bY (fun j => (hbY.1 j).1.1)
    (fun j => Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_letter W Y c' (hbY.1 j)) m hsum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Formalism.MainNotions.UnusedSlot80.ArcF.dv_single, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W Y (hbY.1 j).1.1]

end Formalism.MainNotions.UnusedSlot80.SplitP
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers Formalism.MainNotions.UnusedSlot80.LevC

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

variable [IsDomain O]

def IntA (a : ZMod n) (g : W.EE) : Prop := ∃ u ∈ W.AΔ, g = algebraMap (LetA O n) W.EE (letE a * u)

theorem secOfP_int (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK)
    (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (x : W.DD T)
    (hx : InFP W T c' e 1 x) :
    ∃ (κ : ℕ) (f : Fin d → W.EE), RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol
      (lA W ^ κ • x) f ∧ ∀ k, IntA W (c' + (e : ZMod n)) (f k) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨yP, hyP, hyx⟩ := hx
  rw [one_smul] at hyx
  obtain ⟨β₀, hβ₀, hyβ⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 yP hyP
  have hbl : ∀ m, (letE c' : LetA O n) • b m = b m := fun m =>
    Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1.1 m).2
  have hφl : ∀ m, (letE (c' + (e : ZMod n)) : LetA O n) • ((W.φD T) ^ e) (b m) = ((W.φD T) ^ e) (b m) :=
    fun m => φD_pow_letter W T c' (b m) (hbl m) e
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  let β : Fin d → LetA O n := fun m => letE (c' + (e : ZMod n)) * β₀ m
  have hβ : ∀ m, β m ∈ W.AΔ := fun m => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) (hβ₀ m)
  have hΛx : x = ∑ m, β m • ((W.φD T) ^ e) (b m) := by
    rw [hyx, hyβ]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [β, mul_smul]
    rw [smul_comm, hφl]
  have hHc := hH hCA T hTc c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.1 k r m)
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  set M : ℕ := A.M PD.p with hMdef
  let κ : ℕ := Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M
  let yy : Fin d → ℕ → Fin d → O := fun k r m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m := by
    intro k r hr m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [yy, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := φA_pow_mem_AΔ W hR.1 e
  set D : LetA O n := W.π₀ * Λ ^ 2 with hDdef
  obtain ⟨ν, hν, hYM⟩ := yM_gen W hTr hCA hR.1 h5p A hA (c' + (e : ZMod n)) e
  have hYM' : Y ^ M = D * ν := by rw [hYdef, hMdef, hYM]
  choose ρ hρ using fun m m' =>
    Formalism.MainNotions.UnusedSlot80.ArcF.frame_inv_poly hinj sol (fun k => (hb.2 k).2) M κ yy hyy zz hzz Y m m'
  let HY : Fin d → Fin d → LetA O n := fun m k =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (yy k r m) * Y ^ r
  let GY : Fin d → Fin d → LetA O n := fun k m' =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (zz r k m') * Y ^ r
  have hGY : ∀ k m', GY k m' ∈ W.AΔ := fun k m' => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  let aa : Fin d → LetA O n := fun k => ∑ m', GY k m' * β m'
  have haa : ∀ k, aa k ∈ W.AΔ := fun k => W.AΔ.sum_mem fun m' _ => W.AΔ.mul_mem (hGY k m') (hβ m')
  have haal : ∀ k, letE (c' + (e : ZMod n)) * 1 * aa k = aa k := by
    intro k
    simp only [aa, mul_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    simp only [β]
    linear_combination (GY k m' * β₀ m') * (letE_mul_self (O := O) (c' + (e : ZMod n)))
  let w : Fin d → LetA O n := fun m => -(ν * ∑ m', Polynomial.aeval Y (ρ m m') * β m')
  have hw : ∀ m, w m ∈ W.AΔ := fun m => W.AΔ.neg_mem (W.AΔ.mul_mem hν (W.AΔ.sum_mem fun m' _ =>
      W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _) (hβ m')))
  have hkey : ∀ m, lA W ^ κ * lA W ^ κ * β m - ∑ k, aa k * HY m k = D * w m := by
    intro m
    have A2 : ∑ k, aa k * HY m k = ∑ m', (∑ k, HY m k * GY k m') * β m' := by
      simp only [aa, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun k _ => by ring
    have h1 : ∀ m', (∑ k, HY m k * GY k m') * β m' =
        lA W ^ κ * lA W ^ κ * ((if m = m' then 1 else 0) * β m') +
          Y ^ M * (Polynomial.aeval Y (ρ m m') * β m') := by
      intro m'
      have := hρ m m'
      simp only [HY, GY] at this ⊢
      rw [this, map_mul, map_pow, map_natCast, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]
      unfold lA
      split_ifs <;> ring
    rw [A2, Finset.sum_congr rfl fun m' _ => h1 m', Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, w]
    rw [hYM']
    ring
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1 s) _
  refine ⟨κ, fun k => algebraMap (LetA O n) W.EE (aa k),
    ⟨κ, 0, fun k => ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r), fun k => Λ * aa k,
      fun k => ⟨yy k, hyy k, rfl⟩, fun k => ⟨W.AΔ.mul_mem hΛm (haa k), by rw [map_mul]⟩, ?_⟩,
    fun k => ⟨aa k, haa k, by
      show algebraMap (LetA O n) W.EE (aa k) = _
      congr 1
      conv_rhs => rw [← mul_one (letE (c' + (e : ZMod n)) : LetA O n), haal k]⟩⟩
  have hsum : ∑ k, aa k • ((W.φD T) ^ e)
      (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
      ∑ m, (∑ k, aa k * HY m k) • ((W.φD T) ^ e) (b m) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [HY, ← hYdef]
    congr 1
    refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hfin0 : lA W ^ κ • lA W ^ κ • x - ∑ k, aa k • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
      D • ∑ m, w m • ((W.φD T) ^ e) (b m) := by
    rw [hsum, hΛx]
    simp only [Finset.smul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [smul_smul]
    rw [← sub_smul, ← hkey m]
    congr 1
    ring
  have hfin : lA W ^ 0 • (lA W ^ κ • Λ • (lA W ^ κ • x) - ∑ k, (Λ * aa k) • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) =
      D • ∑ m, (Λ * w m) • ((W.φD T) ^ e) (b m) := by
    have e2 : lA W ^ κ • Λ • (lA W ^ κ • x) - ∑ k, (Λ * aa k) • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
        Λ • (lA W ^ κ • lA W ^ κ • x - ∑ k, aa k • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) := by
      rw [smul_sub, Finset.smul_sum]
      simp only [mul_smul]
      rw [smul_comm Λ (lA W ^ κ) (lA W ^ κ • x)]
    rw [pow_zero, one_smul, e2, hfin0, smul_comm Λ D, Finset.smul_sum]
    simp only [mul_smul]
  rw [hfin]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (AddSubgroup.sum_mem _ fun m _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (W.AΔ.mul_mem hΛm (hw m)) (hb.1.1 m))

end Formalism.MainNotions.UnusedSlot80.SplitP
