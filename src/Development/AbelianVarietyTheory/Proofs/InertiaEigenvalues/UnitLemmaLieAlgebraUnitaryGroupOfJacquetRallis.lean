module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaUnitaryGroupOddResidueOfLie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualStableLatticeUnitOrbitsFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusModIntegralUnitsStructureAndIntegralityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearLatticeCountDescentProof
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatch

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendsto
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusOrbitLatticeCountBoundedByRho
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusOrbitLatticeCountBoundedByRho
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.TorusOrbitLat

section General

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem mem_stabLat_iff (t : Aˣ) (L : Submodule O A) :
    t ∈ stabLat O L ↔ ∀ y, y ∈ L ↔ (t : A) * y ∈ L := Iff.rfl

theorem mem_intUnits_iff (t : Aˣ) :
    t ∈ intUnits O A ↔ IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A) := Iff.rfl

theorem mem_mulLat_unit (u : Aˣ) (L : Submodule O A) (w : A) :
    w ∈ mulLat O (u : A) L ↔ ((u⁻¹ : Aˣ) : A) * w ∈ L := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem mulLat_eq_iff (u v : Aˣ) (L : Submodule O A) :
    mulLat O (u : A) L = mulLat O (v : A) L ↔ u⁻¹ * v ∈ stabLat O L := by
  rw [mem_stabLat_iff]
  constructor
  · intro h y
    calc y ∈ L ↔ (v : A) * y ∈ mulLat O (v : A) L := by rw [mem_mulLat_unit]; simp
      _ ↔ (v : A) * y ∈ mulLat O (u : A) L := by rw [h]
      _ ↔ ((u⁻¹ * v : Aˣ) : A) * y ∈ L := by rw [mem_mulLat_unit, Units.val_mul, mul_assoc]
  · intro h
    ext w
    rw [mem_mulLat_unit, mem_mulLat_unit, h (((v⁻¹ : Aˣ) : A) * w)]
    simp [mul_assoc]

theorem isIntegral_inv_mul_iff (t u : Aˣ) (hu : u ∈ intUnits O A) (w : A) :
    IsIntegral O ((((t * u)⁻¹ : Aˣ) : A) * w) ↔ IsIntegral O (((t⁻¹ : Aˣ) : A) * w) := by
  rw [mem_intUnits_iff] at hu
  rw [mul_inv_rev, Units.val_mul, mul_assoc]
  constructor
  · intro h
    have := hu.1.mul h
    simpa using this
  · intro h
    exact hu.2.mul h

end General

section Main

variable {K : UQ} (B : InvAlg K)

theorem rho_cond_mk (t : B.T) (w : B.A) :
    IsIntegral K.O (((((Quotient.out (QuotientGroup.mk t : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T) : B.T) :
      B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) ↔ IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) t
  rw [hh, Subgroup.coe_mul]
  exact isIntegral_inv_mul_iff _ _ (Subgroup.mem_subgroupOf.mp h.2) w

theorem orbit_count : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 → ∀ a : K.O, (∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j)) → ∀ m k : ℕ, m ≤ k → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ m * y ∈ L) → (∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ m * y)) → Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k - m)) ≤ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ≤ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k + m)) := by
  intro K B L hSle hidx a hrho m k hmk hin hout
  set w : B.A := algebraMap K.O B.A a with hw
  set H : Subgroup B.T := (stabLat K.O L).subgroupOf B.T with hH
  set Kc : Subgroup B.T := (intUnits K.O B.A).subgroupOf B.T with hKc
  have hHK : H ≤ Kc := by
    intro x hx
    rw [hH, Subgroup.mem_subgroupOf] at hx
    rw [hKc, Subgroup.mem_subgroupOf]
    exact hSle ⟨hx, x.2⟩
  have hidx_eq : (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) = (H.subgroupOf Kc).index := by
    rw [← Subgroup.relIndex_subgroupOf (inf_le_right : intUnits K.O B.A ⊓ B.T ≤ B.T),
      Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_right]
    rfl
  have hQfin : Finite (Kc ⧸ H.subgroupOf Kc) := by
    rw [← Subgroup.index_ne_zero_iff_finite, ← hidx_eq]; exact hidx
  have hRfin : ∀ j, Finite {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => (Nat.card_pos_iff.mp (hrho j)).2
  have hrho_eq : ∀ j, B.rho (w ^ j) = Nat.card {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => rfl
  let e := Subgroup.quotientEquivProdOfLE hHK
  have he1 : ∀ g : B.T, (e (QuotientGroup.mk g)).1 = QuotientGroup.mk g := fun g => rfl

  let Y := {c : B.T ⧸ H // w ^ k ∈ mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L}
  let fY : Y → {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ w ^ k ∈ M} :=
    fun c => ⟨mulLat K.O (((Quotient.out c.1 : B.T) : B.Aˣ) : B.A) L, ⟨_, (Quotient.out c.1).2, rfl⟩, c.2⟩
  have hfY : Function.Bijective fY := by
    constructor
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
      have h' : mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L = mulLat K.O (((Quotient.out c' : B.T) : B.Aˣ) : B.A) L :=
        congrArg Subtype.val h
      rw [mulLat_eq_iff] at h'
      apply Subtype.ext
      change c = c'
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using h')
    · rintro ⟨M, ⟨t, ht, rfl⟩, hM⟩
      have hc := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H))
      rw [hH, Subgroup.mem_subgroupOf] at hc
      have key : mulLat K.O (((Quotient.out (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H) : B.T) : B.Aˣ) : B.A) L =
          mulLat K.O (t : B.A) L := by
        rw [mulLat_eq_iff]; simpa using hc
      exact ⟨⟨_, key ▸ hM⟩, Subtype.ext key⟩
  have hcardXY := Nat.card_congr (Equiv.ofBijective fY hfY)

  have key1 : ∀ g : B.T, ((((g : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w ^ k ∈ L) →
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A) := by
    intro g hg
    rw [he1 g, rho_cond_mk]
    have := hout _ hg
    convert this using 1
    rw [pow_add]; ring
  let U : Y → {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) := fun c =>
    (⟨(e c.1).1, by
      have := key1 (Quotient.out c.1) (by rw [← mem_mulLat_unit]; exact c.2)
      rwa [QuotientGroup.out_eq'] at this⟩, (e c.1).2)
  have hU : Function.Injective U := by
    intro c c' h
    apply Subtype.ext
    apply e.injective
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 h2
  have hYfin : Finite Y := by
    haveI := hRfin (k + m)
    exact Finite.of_injective U hU

  have key2 : ∀ g : B.T,
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A) →
      w ^ k ∈ mulLat K.O ((g : B.Aˣ) : B.A) L := by
    intro g hg
    rw [he1 g, rho_cond_mk] at hg
    rw [mem_mulLat_unit]
    have := hin _ hg
    convert this using 1
    rw [← Nat.add_sub_cancel' hmk, pow_add, Nat.add_sub_cancel_left]; ring
  let D : {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) → Y := fun p =>
    ⟨e.symm (p.1.1, p.2), by
      have hc : e (e.symm (p.1.1, p.2)) = (p.1.1, p.2) := e.apply_symm_apply _
      apply key2
      rw [QuotientGroup.out_eq', hc]
      exact p.1.2⟩
  have hD : Function.Injective D := by
    intro p p' h
    have h' := e.symm.injective (congrArg Subtype.val h)
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext (Subtype.ext h1) h2
  refine ⟨?_, ?_, ?_⟩
  · exact Finite.of_equiv Y (Equiv.ofBijective fY hfY)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    exact (Nat.card_prod _ _).symm.trans_le (Nat.card_le_card_of_injective D hD)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    haveI := hRfin (k + m)
    exact (Nat.card_le_card_of_injective U hU).trans_eq (Nat.card_prod _ _)

end Main

end GlobalTheory.TorusOrbitLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusOrbitLatticeCountBoundedByRhoStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_orbit_lattice_count_bounded_by_rho : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 → ∀ a : K.O, (∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j)) → ∀ m k : ℕ, m ≤ k → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ m * y ∈ L) → (∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ m * y)) → Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k - m)) ≤ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ≤ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k + m)) := by
  first | exact @GlobalTheory.TorusOrbitLat.orbit_count | exact GlobalTheory.TorusOrbitLat.orbit_count | (intros; apply GlobalTheory.TorusOrbitLat.orbit_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAlgebraInvolutionRhoPowEqCardBox
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAlgebraInvolutionRhoPowEqCardBox
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem rho_pow_eq_card_box : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  intro K B a r φ c hφ hker hint k
  have hK : (intUnits K.O B.A).subgroupOf B.T = φ.ker := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  unfold InvAlg.rho
  rw [hK]
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have he : ∀ q : B.T ⧸ φ.ker, e q = φ (Quotient.out q) := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h1 : Nat.card {q : B.T ⧸ φ.ker //
      IsIntegral K.O ((((Quotient.out q : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} =
      Nat.card {v : Fin r → ℤ // ∀ i, v i ∈ Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)} := by
    apply Nat.card_congr
    refine (e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv ?_
    intro q
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.trans_apply, MulEquiv.coe_toEquiv, he, Set.mem_Icc, ← abs_le]
    exact hint _ k
  rw [h1, Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : Nat.card (Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)) = 2 * k * c i + 1 := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_Icc, Int.card_Icc, show 2 * k * c i = 2 * (k * c i) by ring]
    omega
  exact h2

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAlgebraInvolutionRhoPowEqCardBoxStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebraInvolution_rho_pow_eq_card_box : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  first | exact @GlobalTheory.UnitLemma.rho_pow_eq_card_box | exact GlobalTheory.UnitLemma.rho_pow_eq_card_box | (intros; apply GlobalTheory.UnitLemma.rho_pow_eq_card_box <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UUEqSumOverTorusOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UUEqSumOverTorusOrbits
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

theorem torusOrb_mem_mulLat_unit (u : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (u : B.A) L ↔ ((u⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  unfold mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [LinearMap.mulLeft_apply, ← mul_assoc] using hz
  · intro h
    exact ⟨_, h, by simp [LinearMap.mulLeft_apply, ← mul_assoc]⟩

theorem torusOrb_mulLat_one (L : Submodule K.O B.A) : mulLat K.O (1 : B.A) L = L := by
  ext y; simpa using torusOrb_mem_mulLat_unit B 1 L y

theorem torusOrb_mulLat_mul (s t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((s : B.A)) (mulLat K.O (t : B.A) L) = mulLat K.O ((s * t : B.Aˣ) : B.A) L := by
  ext y
  rw [torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, mul_inv_rev, Units.val_mul, mul_assoc]

theorem torusOrb_mulLat_inv (t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((t⁻¹ : B.Aˣ) : B.A) (mulLat K.O (t : B.A) L) = L := by
  rw [torusOrb_mulLat_mul, inv_mul_cancel, Units.val_one, torusOrb_mulLat_one]

theorem herm_torus_mul_right_eq_inv_mul_middle (x y : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (z : B.A) :
    B.herm x y ((t : B.A) * z) = B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) z := by
  have h1 : ((t⁻¹ : B.Aˣ) : B.A) = B.σ (t : B.A) := Units.inv_eq_of_mul_eq_one_right ht
  unfold herm
  rw [show B.σ ((t : B.A) * z) = B.σ (t : B.A) * B.σ z from map_mul B.σ _ _, ← h1]
  congr 1
  ring

theorem torusOrb_mulLat_mem_X (x : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (L : Submodule K.O B.A) (hL : L ∈ B.X x) :
    mulLat K.O (t : B.A) L ∈ B.X x := by
  obtain ⟨⟨hfg, hsp⟩, hg, hsd⟩ := hL
  refine ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩
  · rw [eq_top_iff]
    intro a _
    have hmem : ((t⁻¹ : B.Aˣ) : B.A) * a ∈ Submodule.span K.E (L : Set B.A) := by rw [hsp]; trivial
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.mulLeft K.E (t : B.A)) hmem
    rw [Submodule.map_span] at h2
    have h3 : (LinearMap.mulLeft K.E (t : B.A)) ((((t⁻¹ : B.Aˣ) : B.A) * a)) = a := by
      simp [LinearMap.mulLeft_apply, ← mul_assoc]
    rw [h3] at h2
    have e : ((mulLat K.O (t : B.A) L : Submodule K.O B.A) : Set B.A) =
        (LinearMap.mulLeft K.E (t : B.A)) '' (L : Set B.A) := by
      show ((L.map (LinearMap.mulLeft K.O (t : B.A)) : Submodule K.O B.A) : Set B.A) = _
      rw [Submodule.map_coe]
      rfl
    rw [e]
    exact h2
  · intro y hy
    rw [torusOrb_mem_mulLat_unit] at hy ⊢
    rw [mul_left_comm]
    exact hg _ hy
  · intro y
    rw [torusOrb_mem_mulLat_unit, hsd]
    constructor
    · intro h z hz
      rw [torusOrb_mem_mulLat_unit] at hz
      have := h _ hz
      rw [← herm_torus_mul_right_eq_inv_mul_middle B x y t ht] at this
      simpa [← mul_assoc] using this
    · intro h z hz
      rw [← herm_torus_mul_right_eq_inv_mul_middle B x y t ht]
      apply h
      rw [torusOrb_mem_mulLat_unit]
      simpa [← mul_assoc] using hz

def torusOrbRel (x : B.A) (L M : B.X x) : Prop :=
  ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) (L : Submodule K.O B.A)

theorem torusOrb_orbRel_equivalence (x : B.A) : Equivalence (B.torusOrbRel x) := by
  refine { refl := ?_, symm := ?_, trans := ?_ }
  · intro L
    exact ⟨1, B.T.one_mem, by rw [Units.val_one, torusOrb_mulLat_one]⟩
  · rintro L M ⟨t, ht, h⟩
    refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
    rw [h, torusOrb_mulLat_inv]
  · rintro L M N ⟨s, hs, h1⟩ ⟨t, ht, h2⟩
    refine ⟨t * s, B.T.mul_mem ht hs, ?_⟩
    rw [h2, h1, torusOrb_mulLat_mul]

theorem torusOrb_orb_mk_eq (x : B.A) {L M : B.X x}
    (h : (Quot.mk (B.torusOrbRel x) L : Orb K.O B.T (B.X x)) = Quot.mk (B.torusOrbRel x) M) : B.torusOrbRel x L M :=
  (Equivalence.eqvGen_iff (B.torusOrb_orbRel_equivalence x)).1 (Quot.eqvGen_exact h)

def torusOrb_orbSplit (x w : B.A) : {L : B.X x // w ∈ (L : Submodule K.O B.A)} ≃
    Σ o : Orb K.O B.T (B.X x), {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} where
  toFun L := ⟨(Quot.mk (B.torusOrbRel x) L.1 : Orb K.O B.T (B.X x)), L.1.1,
    B.torusOrb_orb_mk_eq x (Quot.out_eq (Quot.mk (B.torusOrbRel x) L.1 : Orb K.O B.T (B.X x))), L.2⟩
  invFun p := ⟨⟨p.2.1, by
      obtain ⟨t, ht, h⟩ := p.2.2.1
      rw [h]
      exact B.torusOrb_mulLat_mem_X x t ht _ (Quot.out p.1).2⟩, p.2.2.2⟩
  left_inv L := rfl
  right_inv p := by
    obtain ⟨o, M, h⟩ := p
    refine Sigma.subtype_ext ?_ rfl
    dsimp only
    conv_rhs => rw [← Quot.out_eq o]
    symm
    apply Quot.sound
    exact h.1

theorem torusOrb_UU_eq_finsum (x w : B.A) (hfin : Finite (Orb K.O B.T (B.X x)))
    (hfib : ∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) :
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} := by
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  unfold UU
  rw [Nat.card_congr (B.torusOrb_orbSplit x w), Nat.card_sigma, finsum_eq_sum_of_fintype]

end InvAlg

theorem UU_eq_sum_orbits : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), Finite (Orb K.O B.T (B.X x)) →
    (∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) →
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} :=
  fun _ B x w h1 h2 => B.torusOrb_UU_eq_finsum x w h1 h2

end GlobalTheory.UnitLemma
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UUEqSumOverTorusOrbitsStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.UU_eq_sum_over_torus_orbits : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), Finite (Orb K.O B.T (B.X x)) → (∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) → B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} := by
  first | exact @GlobalTheory.UnitLemma.UU_eq_sum_orbits | exact GlobalTheory.UnitLemma.UU_eq_sum_orbits | (intros; apply GlobalTheory.UnitLemma.UU_eq_sum_orbits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoRatioBoxCountsProdOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoRatioBoxCountsProdOne
open Filter

namespace GlobalTheory

theorem ratio_box_counts_tendsto_one (r : ℕ) (c : Fin r → ℕ) (m : ℕ) :
    Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) /
      ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  have key : ∀ i, Tendsto (fun k : ℕ => ((2 * (k + m) * c i + 1 : ℕ) : ℝ) /
      ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    intro i
    rcases Nat.eq_zero_or_pos (c i) with h | h
    · simp [h]
    · have hc : (0:ℝ) < c i := by exact_mod_cast h
      have hden : Tendsto (fun k : ℕ => ((2 * k * c i + 1 : ℕ) : ℝ)) atTop atTop := by
        push_cast
        apply tendsto_atTop_add_const_right
        exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2)).atTop_mul_const hc
      have h0 : Tendsto (fun k : ℕ => (2 * m * c i : ℝ) / ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hden
      have h1 := (tendsto_const_nhds (x := (1:ℝ))).add h0
      rw [add_zero] at h1
      refine h1.congr (fun k => ?_)
      have hpos : ((2 * k * c i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
  have h := tendsto_finsetProd (Finset.univ : Finset (Fin r)) (fun i _ => key i)
  simp only [Finset.prod_const_one] at h
  refine h.congr (fun k => ?_)
  rw [Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoRatioBoxCountsProdOneStatement
open Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_ratio_box_counts_prod_one : ∀ (r : ℕ) (c : Fin r → ℕ) (m : ℕ), Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) / ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  first | exact @GlobalTheory.ratio_box_counts_tendsto_one | exact GlobalTheory.ratio_box_counts_tendsto_one | (intros; apply GlobalTheory.ratio_box_counts_tendsto_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendsto
open GlobalTheory.UnitLemma Polynomial Filter Topology

namespace GlobalTheory.UnitLemma

theorem unitaryLimit : UnitaryLimit := by
  have L0 := GlobalTheory.T.selfDual_stable_lattice_unit_orbits_finite
  have S1 := GlobalTheory.T.fullLattice_sandwich_between_integral_elements
  have S2 := GlobalTheory.T.torus_orbit_lattice_count_bounded_by_rho
  have S3 := GlobalTheory.T.UU_eq_sum_over_torus_orbits
  have S4 := GlobalTheory.T.torus_mod_integralUnits_structure_and_integrality
  have S5 := GlobalTheory.T.finiteAlgebraInvolution_rho_pow_eq_card_box
  have S6 := GlobalTheory.T.tendsto_ratio_box_counts_prod_one

  intro K B hB a ha x hx
  classical
  obtain ⟨r, φ, c, hsurj, hker, hc, hint⟩ := S4 K B hB a ha
  have hrho : ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) :=
    S5 K B a r φ c hsurj hker hint
  have hpos : ∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j) := fun j => by
    rw [hrho]; exact Finset.prod_pos fun i _ => by omega
  obtain ⟨hfin, hstab⟩ := L0 K B hB.2 x hx.1 hx.2
  choose m hm using fun o : Orb K.O B.T (B.X x) => S1 K B hB a ha _ (Quot.out o).2.1
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  set M := Finset.univ.sup m with hMdef
  have hmM : ∀ o, m o ≤ M := fun o => Finset.le_sup (Finset.mem_univ o)
  have key := fun (k : ℕ) (hk : M ≤ k) (o : Orb K.O B.T (B.X x)) =>
    S2 K B _ (hstab _ (Quot.out o).2).1 (hstab _ (Quot.out o).2).2 a hpos M k hk
      (hm o M (hmM o)).1 (hm o M (hmM o)).2
  have hUU : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) =
      ∑ o : Orb K.O B.T (B.X x), (Nat.card {L' : Submodule K.O B.A // (∃ t ∈ B.T, L' = mulLat K.O (t : B.A) (Quot.out o).1) ∧
        algebraMap K.O B.A a ^ k ∈ L'} : ℝ) := by
    intro k hk
    rw [S3 K B x _ hfin (fun o => (key k hk o).1), finsum_eq_sum_of_fintype]
    push_cast; rfl
  have hN : (B.N x : ℝ) = ∑ o : Orb K.O B.T (B.X x),
      (((stabLat K.O (Quot.out o).1 ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℝ) := by
    unfold InvAlg.N orbSum
    rw [finsum_eq_sum_of_fintype]
    push_cast
    simp
  have hlo : ∀ k, M ≤ k → (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) ≤ B.UU x (algebraMap K.O B.A a ^ k) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.1
  have hhi : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) ≤ (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.2
  have hposR : ∀ j, (0 : ℝ) < B.rho (algebraMap K.O B.A a ^ j) := fun j => by exact_mod_cast hpos j
  have hup : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have := (S6 r c M).const_mul (B.N x : ℝ)
    rw [mul_one] at this
    refine this.congr fun k => ?_
    rw [hrho, hrho, mul_div_assoc]
  have hdown : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have h1 := ((S6 r c M).inv₀ one_ne_zero).comp (tendsto_sub_atTop_nat M)
    have h2 := h1.const_mul (B.N x : ℝ)
    rw [inv_one, mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop M] with k hk
    simp only [Function.comp_apply, inv_div]
    rw [Nat.sub_add_cancel hk, hrho, hrho, mul_div_assoc]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hdown hup ?_ ?_
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hlo k hk) (hposR k).le
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hhi k hk) (hposR k).le

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendstoStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lattice_count_ratio_tendsto : UnitaryLimit := by
  first | exact @GlobalTheory.UnitLemma.unitaryLimit | exact GlobalTheory.UnitLemma.unitaryLimit | (intros; apply GlobalTheory.UnitLemma.unitaryLimit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaLieAlgebraUnitaryGroupOfJacquetRallis
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem unitLemma_lie_and_group (hM : ∀ r : ℕ, GlobalTheory.JR.UnitMatch r) :
    UnitLemmaLie ∧ UnitLemmaGroup :=
  have hL : UnitLemmaLie := GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent (GlobalTheory.T.relativeFundamentalLemmaCountIdentity_of_unitMatch hM) GlobalTheory.T.unitary_lattice_count_ratio_tendsto GlobalTheory.T.linearLatticeCountDescent_proof
  ⟨hL, GlobalTheory.T.unitLemma_unitary_group_odd_residue_of_lie hL⟩

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaLieAlgebraUnitaryGroupOfJacquetRallisStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → UnitLemmaLie ∧ UnitLemmaGroup := by
  first | exact @GlobalTheory.UnitLemma.unitLemma_lie_and_group | exact GlobalTheory.UnitLemma.unitLemma_lie_and_group | (intros; apply GlobalTheory.UnitLemma.unitLemma_lie_and_group <;> assumption)
end
