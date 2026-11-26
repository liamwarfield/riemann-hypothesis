module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {S : Scheme.{0}}

def transl {A : Over S} [GrpObj A] (h : 𝟙_ (Over S) ⟶ A) : A ⟶ A := 𝟙 A * (toUnit A ≫ h)

def lbPow {X : Scheme.{0}} (L : LB X) (m : ℕ) : LB X :=
  LB.LinComb L (K := Fin m) (fun _ => 𝟙 X) (fun _ => 1)

def sq2 {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    (G2 A).left ⟶ (G2 A').left :=
  (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem eta_zero {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

theorem eta_neg {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (x : D.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, eta_zero]

def heckeSub {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (g : D.La →ₗ[D.O] D.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • g x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add (f := _), smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

theorem mem_heckeSub {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (g : D.La →ₗ[D.O] D.La) (N : ℕ)
    (x : D.La) : o.eta (N • g x) ∈ heckeSub o g N := ⟨x, rfl⟩

theorem one_comp_transl {A : Over S} [GrpObj A] (h : 𝟙_ (Over S) ⟶ A) : (1 : 𝟙_ (Over S) ⟶ A) ≫ transl h = h := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (1 ≫ toUnit A) (𝟙 _),
    Category.id_comp, _root_.one_mul]

theorem comp_eq_one_of_transl {A A' : Over S} [GrpObj A] [GrpObj A'] (ψ : A ⟶ A') [IsMonHom ψ]
    (h : 𝟙_ (Over S) ⟶ A) (hh : (transl h).left ≫ ψ.left = ψ.left) : h ≫ ψ = 1 := by
  have e : transl h ≫ ψ = ψ := Over.OverMorphism.ext hh
  rw [← one_comp_transl h, Category.assoc, e, one_comp]

end GlobalTheory.UPel.HT.Hecke
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL.Bruhat

variable {F : Type} [Field F] {n : ℕ}

theorem perm_eq_of_le (τ : Equiv.Perm (Fin n)) (h : ∀ b, τ b ≤ b) (b : Fin n) : τ b = b := by
  have hs : ∑ i : Fin n, (τ i : ℕ) = ∑ i : Fin n, (i : ℕ) := Equiv.sum_comp τ (fun i => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin n => (τ i : ℕ))
    (g := fun i : Fin n => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)
  exact Fin.ext this

def mono (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun a c => if a = m.1 c then (m.2 c : F) else 0

theorem mul_mono (A : Matrix (Fin n) (Fin n) F) (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) (a c : Fin n) :
    (A * mono m) a c = A a (m.1 c) * m.2 c := by
  simp [mono, Matrix.mul_apply]

theorem mono_mul (A : Matrix (Fin n) (Fin n) F) (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) (a c : Fin n) :
    (mono m * A) a c = m.2 (m.1.symm a) * A (m.1.symm a) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (m.1.symm a)]
  · simp [mono]
  · intro k _ hk
    have : a ≠ m.1 k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [mono, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mono_unique {m m' : Equiv.Perm (Fin n) × (Fin n → Fˣ)} {u u' : GL (Fin n) F} (hu : u ∈ unip F n)
    (hu' : u' ∈ unip F n)
    (h : (u : Matrix (Fin n) (Fin n) F) * mono m = mono m' * (u' : Matrix (Fin n) (Fin n) F)) : m = m' := by
  have key : ∀ b, (m.2 b : F) = m'.2 (m'.1.symm (m.1 b)) *
      (u' : Matrix (Fin n) (Fin n) F) (m'.1.symm (m.1 b)) b := by
    intro b
    have h1 := congrFun (congrFun h (m.1 b)) b
    rwa [mul_mono, mono_mul, unip_diag hu, one_mul] at h1
  have hle : ∀ b, (m.1.trans m'.1.symm) b ≤ b := by
    intro b
    by_contra hlt
    have hlt' : b < m'.1.symm (m.1 b) := not_le.1 hlt
    apply (m.2 b).ne_zero
    rw [key b, unip_lower hu' hlt', mul_zero]
  have hfix : ∀ b, m'.1.symm (m.1 b) = b := fun b => perm_eq_of_le _ hle b
  refine Prod.ext (Equiv.ext fun b => ?_) (funext fun b => Units.ext ?_)
  · have := congrArg m'.1 (hfix b)
    rwa [Equiv.apply_symm_apply] at this
  · rw [key b, hfix b, unip_diag hu', mul_one]

theorem mem_unip_of {A : Matrix (Fin n) (Fin n) F} (hl : ∀ i j, j < i → A i j = 0) (hd : ∀ i, A i i = 1) :
    ∃ u ∈ unip F n, (u : Matrix (Fin n) (Fin n) F) = A := by
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hl i j hij)]
    simp [hd]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, ⟨fun i j hij => hl i j hij, hd⟩, rfl⟩

theorem exists_col_reduced (g : GL (Fin n) F) :
    ∃ u ∈ unip F n, ∃ σ : Equiv.Perm (Fin n),
      (∀ c, ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (σ c) c ≠ 0) ∧
      ∀ a c, σ c < a → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0 := by
  classical
  let P : ℕ → Prop := fun N => ∃ u ∈ unip F n, ∃ f : Fin n → ℕ, ∑ c, f c = N ∧
    ∀ a c : Fin n, f c ≤ a.val → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0
  have hex : ∃ N, P N := ⟨_, 1, Subgroup.one_mem _, fun _ => n, rfl,
    fun a c h => absurd a.2 (not_lt.2 h)⟩
  obtain ⟨u, hu, f, hf, hz⟩ := Nat.find_spec hex
  have hpos : ∀ c, 0 < f c := by
    intro c
    by_contra h0
    have h1 : (((g * u)⁻¹ * (g * u) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c c = 1 := by
      rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      rw [hz k c (by omega), mul_zero]
  have hmin : ∀ v ∈ unip F n,
      (∀ a c : Fin n, f c ≤ a.val → ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0) →
      ∀ c, ∃ a : Fin n, a.val + 1 = f c ∧ ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c ≠ 0 := by
    intro v hv hzv c
    by_contra hcon
    push_neg at hcon
    have hlt : ∑ k, Function.update f c (f c - 1) k < Nat.find hex := by
      rw [← hf]
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
      · by_cases hk : k = c
        · subst hk; simp
        · rw [Function.update_of_ne hk]
      · have := hpos c
        rw [Function.update_self]; omega
    refine Nat.find_min hex hlt ⟨v, hv, _, rfl, fun a k hk => ?_⟩
    by_cases hkc : k = c
    · subst hkc
      rw [Function.update_self] at hk
      by_cases h2 : f k ≤ a.val
      · exact hzv a k h2
      · exact hcon a (by omega)
    · rw [Function.update_of_ne hkc] at hk
      exact hzv a k hk
  choose s hs hsne using hmin u hu hz
  have hinj : ∀ k c, k < c → s k ≠ s c := by
    intro k c hkc he
    have hfe : f k = f c := by rw [← hs k, ← hs c, he]
    set H := ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH
    obtain ⟨t, ht, htv⟩ := mem_unip_of (A := Matrix.transvection k c (-(H (s c) c / H (s c) k)))
      (fun i j hij => by
        have h1 : ¬ (k = i ∧ c = j) := by
          rintro ⟨rfl, rfl⟩; exact absurd hkc (not_lt.2 hij.le)
        simp [Matrix.transvection, Matrix.one_apply_ne (ne_of_gt hij), Matrix.single_apply, h1])
      (fun i => by
        have h1 : ¬ (k = i ∧ c = i) := by
          rintro ⟨rfl, h⟩; exact absurd h (ne_of_gt hkc)
        simp [Matrix.transvection, Matrix.single_apply, h1])
    have hval : ((g * (u * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        H * Matrix.transvection k c (-(H (s c) c / H (s c) k)) := by
      rw [← mul_assoc, Units.val_mul, htv]
    obtain ⟨a, ha, hane⟩ := hmin (u * t) (Subgroup.mul_mem _ hu ht) (fun a j hj => by
      rw [hval]
      by_cases hjc : j = c
      · subst hjc
        rw [Matrix.mul_transvection_apply_same, hz a j hj, hz a k (hfe ▸ hj)]
        simp
      · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hjc]
        exact hz a j hj) c
    have hac : a = s c := Fin.ext (by have := hs c; omega)
    apply hane
    have hk0 : H (s c) k ≠ 0 := he ▸ hsne k
    rw [hval, Matrix.mul_transvection_apply_same, hac]
    field_simp
    ring
  have hinj' : Function.Injective s := by
    intro k c he
    rcases lt_trichotomy k c with h | h | h
    · exact absurd he (hinj k c h)
    · exact h
    · exact absurd he.symm (hinj c k h)
  refine ⟨u, hu, Equiv.ofBijective s (Finite.injective_iff_bijective.1 hinj'), hsne, fun a c h => hz a c ?_⟩
  have h1 : (s c).val < a.val := h
  have := hs c
  omega

theorem exists_decomp (g : GL (Fin n) F) : ∃ m : Equiv.Perm (Fin n) × (Fin n → Fˣ), ∃ u ∈ unip F n, ∃ u' ∈ unip F n,
    (g : Matrix (Fin n) (Fin n) F) = (u : Matrix (Fin n) (Fin n) F) * mono m * (u' : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨v, hv, σ, hne, hz⟩ := exists_col_reduced g
  set H := ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH
  obtain ⟨u, hu, huv⟩ := mem_unip_of (A := Matrix.of fun a b => H a (σ.symm b) / H b (σ.symm b))
    (fun i j hij => by
      rw [Matrix.of_apply, hz i _ (by simpa using hij), zero_div])
    (fun i => by
      have := hne (σ.symm i)
      rw [Equiv.apply_symm_apply] at this
      rw [Matrix.of_apply, div_self this])
  refine ⟨(σ, fun c => Units.mk0 _ (hne c)), u, hu, v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
  have h1 : (u : Matrix (Fin n) (Fin n) F) * mono (σ, fun c => Units.mk0 _ (hne c)) = H := by
    ext a c
    rw [mul_mono, huv]
    simp [div_mul_cancel₀ _ (hne c)]
  rw [h1, hH, ← Units.val_mul, mul_inv_cancel_right]

theorem bruhat : ∀ (F : Type) [Field F] (n : ℕ) (g : GL (Fin n) F), ∃! m : Equiv.Perm (Fin n) × (Fin n → Fˣ), ∃ u ∈ unip F n, ∃ u' ∈ unip F n, (g : Matrix (Fin n) (Fin n) F) = (u : Matrix (Fin n) (Fin n) F) * (Matrix.of fun a c => if a = m.1 c then (m.2 c : F) else 0) * (u' : Matrix (Fin n) (Fin n) F) := by
  intro F _ n g
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  refine ⟨m, ⟨u, hu, u', hu', h⟩, ?_⟩
  rintro m' ⟨v, hv, v', hv', h'⟩
  have h2 : (v : Matrix (Fin n) (Fin n) F) * mono m' * v' = u * mono m * u' := h'.symm.trans h
  refine mono_unique (u := u⁻¹ * v) (u' := u' * v'⁻¹) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hv)
    (Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hv')) ?_
  have h3 := congrArg (fun X => ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X *
    ((v'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h2
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.inv_mul_cancel_left] at h3
  simp only [Units.val_mul, Matrix.mul_assoc]
  exact h3

end GlobalTheory.FinGL.Bruhat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg.HarmStable

section General

variable {σ : Type}

def DegZero (K : Module.End ℂ (MvPolynomial σ ℂ)) : Prop :=
  ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → K P ∈ homog σ d

theorem hc_hc (d e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent d (homogeneousComponent e P) =
      if d = e then homogeneousComponent e P else 0 :=
  homogeneousComponent_of_mem (homogeneousComponent_mem e P)

theorem DegZero.comm {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K) (d : ℕ)
    (P : MvPolynomial σ ℂ) : homogeneousComponent d (K P) = K (homogeneousComponent d P) := by
  rw [← sum_homogeneousComponent P]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [homogeneousComponent_of_mem (hK e _ (homogeneousComponent_mem e P)), hc_hc]
  split_ifs <;> simp

theorem minusPart_eq_zero_iff (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart A P = 0 ↔
      ∀ d, homogeneousComponent d (A (homogeneousComponent (d + 2) P)) = 0 := by
  constructor
  · intro h d
    have hfin : (Function.support fun e : ℕ =>
        homogeneousComponent e (A (homogeneousComponent (e + 2) P))) ⊆
        ((Finset.range (P.totalDegree + 1) ∪ {d} : Finset ℕ) : Set ℕ) := by
      intro e he
      by_contra hne
      apply he
      have : P.totalDegree < e + 2 := by
        simp only [Finset.coe_union, Finset.coe_range, Set.mem_union, Set.mem_Iio, not_or] at hne
        omega
      simp [homogeneousComponent_eq_zero _ _ this]
    rw [minusPart, finsum_eq_sum_of_support_subset _ hfin] at h
    have h2 := congrArg (homogeneousComponent d) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h2
    simp only [hc_hc] at h2
    rw [Finset.sum_ite_eq] at h2
    simpa using h2
  · intro h
    rw [minusPart]
    simp [h]

def lowKer {ι : Type} (A : ι → Module.End ℂ (MvPolynomial σ ℂ)) (c : ι → Prop) :
    Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨅ Z, ⨅ (_ : c Z), ⨅ d : ℕ,
    LinearMap.ker (homogeneousComponent d ∘ₗ A Z ∘ₗ homogeneousComponent (d + 2))

theorem mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {P : MvPolynomial σ ℂ} : P ∈ lowKer A c ↔
      ∀ Z, c Z → ∀ d, homogeneousComponent d (A Z (homogeneousComponent (d + 2) P)) = 0 := by
  simp [lowKer, Submodule.mem_iInf]

theorem coe_lowKer {ι : Type} (A : ι → Module.End ℂ (MvPolynomial σ ℂ)) (c : ι → Prop) :
    (lowKer A c : Set (MvPolynomial σ ℂ)) = {P | ∀ Z, c Z → minusPart (A Z) P = 0} := by
  ext P
  simp only [SetLike.mem_coe, mem_lowKer, Set.mem_setOf_eq, minusPart_eq_zero_iff]

theorem hc_mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowKer A c) (e : ℕ) :
    homogeneousComponent e P ∈ lowKer A c := by
  rw [mem_lowKer] at hP ⊢
  intro Z hZ d
  rw [hc_hc]
  split_ifs with h
  · rw [← h]; exact hP Z hZ d
  · simp

theorem map_mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K)
    (hc : ∀ Z, c Z → A Z * K = K * A Z ∨ ∃ Z', c Z' ∧ A Z' = A Z * K - K * A Z)
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowKer A c) : K P ∈ lowKer A c := by
  rw [mem_lowKer] at hP ⊢
  intro Z hZ d
  rw [hK.comm, ← Module.End.mul_apply (A Z) K]
  rcases hc Z hZ with h | ⟨Z', hZ', h⟩
  · rw [h, Module.End.mul_apply, hK.comm, hP Z hZ d, map_zero]
  · rw [← sub_add_cancel (A Z * K) (K * A Z), ← h, LinearMap.add_apply, map_add (f := _), hP Z' hZ' d,
      Module.End.mul_apply, hK.comm, hP Z hZ d, map_zero, add_zero]

theorem X_mul_pderiv_mem (u v : σ) {d : ℕ} {P : MvPolynomial σ ℂ} (hP : P ∈ homog σ d) :
    X u * pderiv v P ∈ homog σ d := by
  rcases d with _ | d
  · rw [totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hP), pderiv_C,
      mul_zero]
    exact Submodule.zero_mem _
  · have := (isHomogeneous_X ℂ u).mul (IsHomogeneous.pderiv (i := v) hP)
    rwa [Nat.add_sub_cancel, add_comm] at this

theorem pderiv_X_mul_mem (u v : σ) {d : ℕ} {P : MvPolynomial σ ℂ} (hP : P ∈ homog σ d) :
    pderiv v (X u * P) ∈ homog σ d := by
  have := IsHomogeneous.pderiv (i := v) ((isHomogeneous_X ℂ u).mul hP)
  rwa [Nat.add_sub_cancel_left] at this

end General

variable {p q r s : ℕ}

theorem degZero_omE {l l' : Ln p q r s} (h : linePos l = linePos l') : DegZero (omE l l') := by
  intro d P hP
  rw [omE, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [raiB, lowB, ← h]
    split_ifs
    · exact X_mul_pderiv_mem l l' hP
    · exact Submodule.neg_mem _ (pderiv_X_mul_mem l' l hP)
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

theorem degZero_omAct {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (h : ∀ l l', linePos l ≠ linePos l' → M l l' = 0) : DegZero (omAct p q r s M) := by
  intro d P hP
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  by_cases hl : linePos l = linePos l'
  · exact Submodule.smul_mem _ _ (degZero_omE hl d P hP)
  · rw [h l l' hl, zero_smul]; exact Submodule.zero_mem _

theorem degZero_fockAct1 {Y : Mat p q} (hY : IsKC Y) : DegZero (fockAct1 p q r s Y) := by
  refine degZero_omAct ?_
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  show Y a b * (1 : Mat r s) c e = 0
  by_cases hce : c = e
  · subst hce
    rw [hY a b, zero_mul]
    revert h
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hce, mul_zero]

theorem degZero_fockAct2 {Y : Mat r s} (hY : IsKC Y) : DegZero (fockAct2 p q r s Y) := by
  refine degZero_omAct ?_
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  show (1 : Mat p q) a b * Y c e = 0
  by_cases hab : a = b
  · subst hab
    rw [hY c e, mul_zero]
    revert h
    rcases a with a | a <;> rcases e with e | e <;> rcases c with c | c <;>
      simp [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hab, zero_mul]

theorem isPC_bracket {Y Z : Mat p q} (hY : IsKC Y) (hZ : IsPC Z) : IsPC (Z * Y - Y * Z) := by
  intro a b hab
  have h1 : (Z * Y) a b = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : sameBlock a c
    · rw [hZ a c hc, zero_mul]
    · rw [hY c b, mul_zero]
      revert hab hc
      rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp [sameBlock]
  have h2 : (Y * Z) a b = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : sameBlock a c
    · rw [hZ c b, mul_zero]
      revert hab hc
      rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp [sameBlock]
    · rw [hY a c hc, zero_mul]
  rw [Matrix.sub_apply, h1, h2, sub_zero]

def sub1 (p q r s : ℕ) : Submodule ℂ (Pol p q r s) :=
  lowKer (fun Z : Mat r s => fockAct2 p q r s Z) IsPC

def sub2 (p q r s : ℕ) : Submodule ℂ (Pol p q r s) :=
  lowKer (fun Z : Mat p q => fockAct1 p q r s Z) IsPC

theorem coe_fockHarmonicsFirstMemberSubspace : (sub1 p q r s : Set (Pol p q r s)) = harm1 p q r s := coe_lowKer _ _

theorem coe_fockHarmonicsSecondMemberSubmodule : (sub2 p q r s : Set (Pol p q r s)) = harm2 p q r s := coe_lowKer _ _

theorem fockHarmonicsFirstMember_kStable : KStable (fockAct1 p q r s) (sub1 p q r s) ∧
    KStable (fockAct2 p q r s) (sub1 p q r s) := by
  obtain ⟨-, -, h2, h3⟩ := GlobalTheory.T.fockOperators_lie_representation_commute p q r s
  exact ⟨fun Y hY _ hw => map_mem_lowKer (degZero_fockAct1 hY)
      (fun Z _ => Or.inl (h3 Y Z).symm) hw,
    fun Y hY _ hw => map_mem_lowKer (degZero_fockAct2 hY)
      (fun Z hZ => Or.inr ⟨_, isPC_bracket hY hZ, h2 Z Y⟩) hw⟩

theorem fockHarmonicsSecondMember_kStable : KStable (fockAct1 p q r s) (sub2 p q r s) ∧
    KStable (fockAct2 p q r s) (sub2 p q r s) := by
  obtain ⟨-, h1, -, h3⟩ := GlobalTheory.T.fockOperators_lie_representation_commute p q r s
  exact ⟨fun Y hY _ hw => map_mem_lowKer (degZero_fockAct1 hY)
      (fun Z hZ => Or.inr ⟨_, isPC_bracket hY hZ, h1 Z Y⟩) hw,
    fun Y hY _ hw => map_mem_lowKer (degZero_fockAct2 hY)
      (fun Z _ => Or.inl (h3 Z Y)) hw⟩

end GlobalTheory.FockAlg.HarmStable

namespace GlobalTheory.FockAlg

open HarmStable

theorem harm_graded_stable : ∀ (p q r s : ℕ) (S : Set (Pol p q r s)),
    (S = harm1 p q r s ∨ S = harm2 p q r s ∨ S = jointHarm p q r s) →
    (Submodule.span ℂ S : Set (Pol p q r s)) = S ∧
      KStable (fockAct1 p q r s) (Submodule.span ℂ S) ∧
      KStable (fockAct2 p q r s) (Submodule.span ℂ S) ∧
      ∀ P ∈ S, ∀ d : ℕ, homogeneousComponent d P ∈ S := by
  intro p q r s S hS
  rcases hS with rfl | rfl | rfl
  · rw [← coe_fockHarmonicsFirstMemberSubspace, Submodule.span_eq]
    exact ⟨rfl, fockHarmonicsFirstMember_kStable.1, fockHarmonicsFirstMember_kStable.2, fun P hP d => hc_mem_lowKer hP d⟩
  · rw [← coe_fockHarmonicsSecondMemberSubmodule, Submodule.span_eq]
    exact ⟨rfl, fockHarmonicsSecondMember_kStable.1, fockHarmonicsSecondMember_kStable.2, fun P hP d => hc_mem_lowKer hP d⟩
  · rw [jointHarm, ← coe_fockHarmonicsFirstMemberSubspace, ← coe_fockHarmonicsSecondMemberSubmodule, ← Submodule.coe_inf, Submodule.span_eq]
    exact ⟨rfl,
      fun Y hY w hw => ⟨fockHarmonicsSecondMember_kStable.1 Y hY w hw.1, fockHarmonicsFirstMember_kStable.1 Y hY w hw.2⟩,
      fun Y hY w hw => ⟨fockHarmonicsSecondMember_kStable.2 Y hY w hw.1, fockHarmonicsFirstMember_kStable.2 Y hY w hw.2⟩,
      fun P hP d => ⟨hc_mem_lowKer hP.1 d, hc_mem_lowKer hP.2 d⟩⟩

end GlobalTheory.FockAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStableStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonics_graded_compactStable : ∀ (p q r s : ℕ) (S : Set (Pol p q r s)), (S = harm1 p q r s ∨ S = harm2 p q r s ∨ S = jointHarm p q r s) → (Submodule.span ℂ S : Set (Pol p q r s)) = S ∧ KStable (fockAct1 p q r s) (Submodule.span ℂ S) ∧ KStable (fockAct2 p q r s) (Submodule.span ℂ S) ∧ ∀ P ∈ S, ∀ d : ℕ, homogeneousComponent d P ∈ S := by
  first | exact @GlobalTheory.FockAlg.harm_graded_stable | exact GlobalTheory.FockAlg.harm_graded_stable | (intros; apply GlobalTheory.FockAlg.harm_graded_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRules
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRules
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.RedRules

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (σ : Type)

theorem inj : Function.Injective (algebraMap (WittVector p k) (Fr p k)) :=
  IsFractionRing.injective _ _

theorem coeff_smul' (r : WittVector p k) (f : MvPowerSeries σ (Fr p k)) (α : σ →₀ ℕ) :
    coeff α (r • f) = algebraMap _ (Fr p k) r * coeff α f := by
  change r • coeff α f = _
  rw [Algebra.smul_def]

theorem intBy_one_iff (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g := by
  constructor
  · intro hf
    choose w hw using hf
    refine ⟨fun α => WittVector.constantCoeff (w α), fun α => ⟨w α, ?_, rfl⟩⟩
    rw [hw α, one_mul]
  · rintro ⟨g, hg⟩ α
    obtain ⟨w, hw, -⟩ := hg α
    exact ⟨w, by rw [one_mul, hw]⟩

theorem red_unique (f : MvPowerSeries σ (Fr p k)) (g g' : MvPowerSeries σ k)
    (h : Red p f g) (h' : Red p f g') : g = g' := by
  ext α
  obtain ⟨w, hw, hg⟩ := h α
  obtain ⟨w', hw', hg'⟩ := h' α
  have : w = w' := inj p k (hw.symm.trans hw')
  rw [← hg, ← hg', this]

theorem red_lift (g : MvPowerSeries σ k) : Red p (Katz.lift p g) g := fun α =>
  ⟨WittVector.teichmuller p (coeff α g), coeff_lift p g α, by
    rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

theorem red_add_sub (f f' : MvPowerSeries σ (Fr p k)) (g g' : MvPowerSeries σ k)
    (h : Red p f g) (h' : Red p f' g') : Red p (f + f') (g + g') ∧ Red p (f - f') (g - g') := by
  constructor
  · intro α
    obtain ⟨w, hw, hg⟩ := h α
    obtain ⟨w', hw', hg'⟩ := h' α
    exact ⟨w + w', by rw [map_add (f := _), map_add (f := _), hw, hw'], by rw [map_add (f := _), map_add (f := _), hg, hg']⟩
  · intro α
    obtain ⟨w, hw, hg⟩ := h α
    obtain ⟨w', hw', hg'⟩ := h' α
    exact ⟨w - w', by rw [map_sub, map_sub, hw, hw'], by rw [map_sub, map_sub, hg, hg']⟩

theorem red_smul (r : WittVector p k) (f : MvPowerSeries σ (Fr p k)) (g : MvPowerSeries σ k)
    (h : Red p f g) : Red p (r • f) (WittVector.constantCoeff r • g) := by
  intro α
  obtain ⟨w, hw, hg⟩ := h α
  refine ⟨r * w, ?_, ?_⟩
  · rw [coeff_smul', hw, map_mul]
  · rw [map_mul, hg, MvPowerSeries.coeff_smul]

theorem constantCoeff_p_mul (v : WittVector p k) :
    WittVector.constantCoeff ((p : WittVector p k) * v) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem exists_p_mul [PerfectRing k p] (w : WittVector p k) (hw : WittVector.constantCoeff w = 0) :
    ∃ v, w = (p : WittVector p k) * v := by
  by_cases h0 : w = 0
  · exact ⟨0, by rw [h0, mul_zero]⟩
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  cases m with
  | zero =>
    rw [pow_zero, one_mul, WittVector.constantCoeff_apply] at hw
    exact absurd hw hb
  | succ m => exact ⟨(p : WittVector p k) ^ m * b, by rw [pow_succ, mul_comm _ (p : WittVector p k), mul_assoc]⟩

theorem intBy_p_iff [PerfectRing k p] (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ p ↔ Red p f 0 := by
  constructor
  · intro hf α
    obtain ⟨v, hv⟩ := hf α
    exact ⟨_, hv, by rw [constantCoeff_p_mul, map_zero]⟩
  · intro hf α
    obtain ⟨w, hw, h0⟩ := hf α
    rw [map_zero] at h0
    obtain ⟨v, rfl⟩ := exists_p_mul p k w h0
    exact ⟨v, hw⟩

theorem intBy_iff (c : WittVector p k) (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g := by
  constructor
  · intro hf
    choose w hw using hf
    refine ⟨(fun α => algebraMap _ (Fr p k) (w α) : MvPowerSeries σ (Fr p k)), fun α => ⟨w α, by rw [one_mul]; rfl⟩, ?_⟩
    ext α
    rw [hw α, map_mul]
    exact (coeff_smul' p k σ c (fun α => algebraMap _ (Fr p k) (w α)) α).symm
  · rintro ⟨g, hg, rfl⟩ α
    obtain ⟨w, hw⟩ := hg α
    exact ⟨w, by rw [coeff_smul', hw, one_mul, map_mul]⟩

end GlobalTheory.Katz.RedRules

open GlobalTheory.Katz.RedRules in
theorem GlobalTheory.Katz.red_rules : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ : Type), (∀ (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g) ∧ (∀ (f : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f g' → g = g') ∧ (∀ g : MvPowerSeries σ k, Red p (Katz.lift p g) g) ∧ (∀ (f f' : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f' g' → Red p (f + f') (g + g') ∧ Red p (f - f') (g - g')) ∧ (∀ (r : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)) g, Red p f g → Red p (r • f) (WittVector.constantCoeff r • g)) ∧ (∀ f : MvPowerSeries (σ) (Fr p k), f ∈ intBy p k σ p ↔ Red p f 0) ∧ (∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g) := by
  intro p _ k _ _ _ σ
  exact ⟨intBy_one_iff p k σ, red_unique p k σ, red_lift p k σ, red_add_sub p k σ, red_smul p k σ,
    intBy_p_iff p k σ, intBy_iff p k σ⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ : Type), (∀ (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g) ∧ (∀ (f : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f g' → g = g') ∧ (∀ g : MvPowerSeries σ k, Red p (Katz.lift p g) g) ∧ (∀ (f f' : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f' g' → Red p (f + f') (g + g') ∧ Red p (f - f') (g - g')) ∧ (∀ (r : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)) g, Red p f g → Red p (r • f) (WittVector.constantCoeff r • g)) ∧ (∀ f : MvPowerSeries (σ) (Fr p k), f ∈ intBy p k σ p ↔ Red p f 0) ∧ (∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g) := by
  first | exact @GlobalTheory.Katz.red_rules | exact GlobalTheory.Katz.red_rules | (intros; apply GlobalTheory.Katz.red_rules <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

namespace CobCob

variable {R : Type} [CommRing R] {d : ℕ} {τ : Type}

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.elim_has {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [hu, hv])

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.op_const
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.op μ u v i) = 0 := by
  unfold _root_.GlobalTheory.Katz.op _root_.GlobalTheory.Katz.at2
  exact constantCoeff_subst_eq_zero (_root_.GlobalTheory.Katz.CobCob.elim_has hu hv)
    (by rintro (j | j) <;> simp [hu, hv]) (h i)

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsFirstVariables (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.x1 (R := R) i) = 0 := by
  unfold _root_.GlobalTheory.Katz.x1
  exact constantCoeff_X _

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsSecondVariables (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.x2 (R := R) i) = 0 := by
  unfold _root_.GlobalTheory.Katz.x2
  exact constantCoeff_X _

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsThirdVariables (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.x3 (R := R) i) = 0 := by
  unfold _root_.GlobalTheory.Katz.x3
  exact constantCoeff_X _

end CobCob

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_sub_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (c - c') u v =
      _root_.GlobalTheory.Katz.at2 c u v - _root_.GlobalTheory.Katz.at2 c' u v := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_sub h c c'

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_subst_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) {a : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries (Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (subst a f) u v =
      subst (fun i => _root_.GlobalTheory.Katz.at2 (a i) u v) f := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) h f

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_X_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (s : Fin d ⊕ Fin d) :
    _root_.GlobalTheory.Katz.at2 (X s) u v = Sum.elim u v s := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_X h s

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_cob1_eq_subst_op_sub {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (_root_.GlobalTheory.Katz.cob1 μ f) u v =
      subst (_root_.GlobalTheory.Katz.op μ u v) f - subst u f - subst v f := by
  unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
  rw [at2_sub_of_hasSubst h, at2_sub_of_hasSubst h,
    at2_subst_of_hasSubst h hμ,
    at2_subst_of_hasSubst h (fun i => constantCoeff_X _),
    at2_subst_of_hasSubst h (fun i => constantCoeff_X _)]
  simp only [at2_X_of_hasSubst h, Sum.elim_inl, Sum.elim_inr]
  rfl

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_add_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (c + c') u v =
      _root_.GlobalTheory.Katz.at2 c u v + _root_.GlobalTheory.Katz.at2 c' u v := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_add h c c'

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_smul_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (r : R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (r • c) u v = r • _root_.GlobalTheory.Katz.at2 c u v := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_smul h r c

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem op_addLaw_eq_add_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) :
    _root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) u v = fun i => u i + v i := by
  funext i
  unfold _root_.GlobalTheory.Katz.op _root_.GlobalTheory.Katz.addLaw
  rw [at2_add_of_hasSubst h, at2_X_of_hasSubst h,
    at2_X_of_hasSubst h]
  rfl


set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt : ∀ (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) →
    ∀ f : MvPowerSeries (Fin d) R,
    _root_.GlobalTheory.Katz.cob2 μ (_root_.GlobalTheory.Katz.cob1 μ f) =
      subst (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) f -
      subst (_root_.GlobalTheory.Katz.op μ
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
        _root_.GlobalTheory.Katz.x3) f ∧
    _root_.GlobalTheory.Katz.swap (_root_.GlobalTheory.Katz.cob1 μ f) -
      _root_.GlobalTheory.Katz.cob1 μ f =
      subst (fun i => _root_.GlobalTheory.Katz.swap (μ i)) f - subst μ f ∧
    (∀ c c', _root_.GlobalTheory.Katz.cob2 μ (c + c') =
      _root_.GlobalTheory.Katz.cob2 μ c + _root_.GlobalTheory.Katz.cob2 μ c' ∧
      _root_.GlobalTheory.Katz.cob2 μ (c - c') =
      _root_.GlobalTheory.Katz.cob2 μ c - _root_.GlobalTheory.Katz.cob2 μ c' ∧
      _root_.GlobalTheory.Katz.swap (c - c') =
      _root_.GlobalTheory.Katz.swap c - _root_.GlobalTheory.Katz.swap c') ∧
    (∀ (r : R) c, _root_.GlobalTheory.Katz.cob2 μ (r • c) = r • _root_.GlobalTheory.Katz.cob2 μ c ∧
      _root_.GlobalTheory.Katz.swap (r • c) = r • _root_.GlobalTheory.Katz.swap c) ∧
    _root_.GlobalTheory.Katz.IsLaw (_root_.GlobalTheory.Katz.addLaw R d) ∧
    (_root_.GlobalTheory.Katz.IsLaw μ →
      _root_.GlobalTheory.Katz.IsCoc μ (_root_.GlobalTheory.Katz.cob1 μ f)) := by
  intro R _ d μ hμ f
  have h1 := _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)
  have h2 := _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)
  have h3 := _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsThirdVariables (R := R) (d := d)
  have h23 := _root_.GlobalTheory.Katz.CobCob.elim_has h2 h3
  have h12 := _root_.GlobalTheory.Katz.CobCob.elim_has h1 h2
  have h12_3 := _root_.GlobalTheory.Katz.CobCob.elim_has (_root_.GlobalTheory.Katz.CobCob.op_const hμ h1 h2) h3
  have h1_23 := _root_.GlobalTheory.Katz.CobCob.elim_has h1 (_root_.GlobalTheory.Katz.CobCob.op_const hμ h2 h3)
  have hs : HasSubst (Sum.elim (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
    _root_.GlobalTheory.Katz.CobCob.elim_has (fun i => constantCoeff_X _) (fun i => constantCoeff_X _)
  have part1 : _root_.GlobalTheory.Katz.cob2 μ (_root_.GlobalTheory.Katz.cob1 μ f) =
      subst (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) f -
      subst (_root_.GlobalTheory.Katz.op μ
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
        _root_.GlobalTheory.Katz.x3) f := by
    unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_cob1_eq_subst_op_sub h23 hμ, at2_cob1_eq_subst_op_sub h12_3 hμ,
      at2_cob1_eq_subst_op_sub h1_23 hμ, at2_cob1_eq_subst_op_sub h12 hμ]
    abel
  have part2 : _root_.GlobalTheory.Katz.swap (_root_.GlobalTheory.Katz.cob1 μ f) -
      _root_.GlobalTheory.Katz.cob1 μ f =
      subst (fun i => _root_.GlobalTheory.Katz.swap (μ i)) f - subst μ f := by
    have e : _root_.GlobalTheory.Katz.swap (_root_.GlobalTheory.Katz.cob1 μ f) =
        subst (fun i => _root_.GlobalTheory.Katz.swap (μ i)) f -
          _root_.GlobalTheory.Katz.inR f - _root_.GlobalTheory.Katz.inL f :=
      at2_cob1_eq_subst_op_sub hs hμ f
    rw [e]
    unfold _root_.GlobalTheory.Katz.cob1
    abel
  refine ⟨part1, part2, fun c c' => ⟨?_, ?_, ?_⟩, fun r c => ⟨?_, ?_⟩, ?_, fun hl => ?_⟩
  · unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_add_of_hasSubst h23, at2_add_of_hasSubst h12_3,
      at2_add_of_hasSubst h1_23, at2_add_of_hasSubst h12]
    abel
  · unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_sub_of_hasSubst h23, at2_sub_of_hasSubst h12_3,
      at2_sub_of_hasSubst h1_23, at2_sub_of_hasSubst h12]
    abel
  · unfold _root_.GlobalTheory.Katz.swap
    exact at2_sub_of_hasSubst hs c c'
  · unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_smul_of_hasSubst h23, at2_smul_of_hasSubst h12_3,
      at2_smul_of_hasSubst h1_23, at2_smul_of_hasSubst h12]
    simp only [smul_sub, smul_add]
  · unfold _root_.GlobalTheory.Katz.swap
    exact at2_smul_of_hasSubst hs r c
  · have hc : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.addLaw R d i) = 0 := by
      intro i
      simp [_root_.GlobalTheory.Katz.addLaw]
    refine ⟨hc, ?_, ?_, ?_⟩
    · rw [op_addLaw_eq_add_of_hasSubst
        (_root_.GlobalTheory.Katz.CobCob.elim_has (fun i => constantCoeff_X i) (fun _ => by simp))]
      funext i
      simp
    · intro i
      unfold _root_.GlobalTheory.Katz.swap _root_.GlobalTheory.Katz.addLaw
      rw [at2_add_of_hasSubst hs, at2_X_of_hasSubst hs,
        at2_X_of_hasSubst hs]
      simp [add_comm]
    · rw [op_addLaw_eq_add_of_hasSubst
          (_root_.GlobalTheory.Katz.CobCob.elim_has (_root_.GlobalTheory.Katz.CobCob.op_const hc h1 h2) h3),
        op_addLaw_eq_add_of_hasSubst h12,
        op_addLaw_eq_add_of_hasSubst
          (_root_.GlobalTheory.Katz.CobCob.elim_has h1 (_root_.GlobalTheory.Katz.CobCob.op_const hc h2 h3)),
        op_addLaw_eq_add_of_hasSubst h23]
      funext i
      exact add_assoc _ _ _
  · unfold _root_.GlobalTheory.Katz.IsCoc
    constructor
    · rw [part1, hl.assoc, sub_self]
    · rw [← sub_eq_zero, part2]
      simp [hl.comm]

end Katz

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ f : MvPowerSeries (Fin d) R, cob2 μ (cob1 μ f) = subst (op μ x1 (op μ x2 x3)) f - subst (op μ (op μ x1 x2) x3) f ∧ swap (cob1 μ f) - cob1 μ f = subst (fun i => swap (μ i)) f - subst μ f ∧ (∀ c c', cob2 μ (c + c') = cob2 μ c + cob2 μ c' ∧ cob2 μ (c - c') = cob2 μ c - cob2 μ c' ∧ swap (c - c') = swap c - swap c') ∧ (∀ (r : R) c, cob2 μ (r • c) = r • cob2 μ c ∧ swap (r • c) = r • swap c) ∧ IsLaw (addLaw R d) ∧ (IsLaw μ → IsCoc μ (cob1 μ f)) := by
  first | exact @GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt | exact GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt | (intros; apply GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt <;> assumption)
end
end
