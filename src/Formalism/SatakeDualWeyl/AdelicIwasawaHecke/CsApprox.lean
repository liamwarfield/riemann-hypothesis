module

public import Formalism.SatakeDualWeyl.DefsCS
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaE

@[expose] public section

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
noncomputable section
namespace Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

section CsApprox

variable {F : Type} [Field F] [NumberField F]

theorem csApprox_val_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  first
  | (rw [valuedAdicCompletion_eq_valuation' v]; exact valuation_of_algebraMap v r)
  | simp [valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  | (erw [valuedAdicCompletion_eq_valuation']; exact valuation_of_algebraMap v r)

theorem csApprox_local (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ s : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) s) < v.intValuation D := by
  set c := algebraMap (𝓞 F) (v.adicCompletion F) D with hcdef
  have hc : c ≠ 0 := levelaf_algebraMap_ne_zero v D hD
  have hrc : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).restrict c ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hc
  have hs : {y : v.adicCompletion F | Valued.v (y - x) < Valued.v c} ∈ nhds x := by
    refine Valued.mem_nhds.2 ⟨Units.mk0 _ hrc, fun y hy => ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0] at hy ⊢
    exact lt_of_not_ge fun h => (not_le.2 hy) ((Valuation.restrict_le_iff _).2 h)
  obtain ⟨b, hb⟩ := (denseRange_algebraMap (K := F) v).mem_nhds hs
  simp only [Set.mem_ofPred_eq] at hb
  have hcv : Valued.v c = v.intValuation D := csApprox_val_int v D
  rw [hcv] at hb
  have hb1 : v.valuation F b ≤ 1 := by
    rw [← levelaf_valued_algebraMap]
    have e : algebraMap F (v.adicCompletion F) b = (algebraMap F (v.adicCompletion F) b - x) + x := by
      ring
    rw [e]
    exact Valuation.map_add_le _ (hb.le.trans (v.intValuation_le_one D)) hx
  obtain ⟨s, hs⟩ := exists_valuation_sub_lt_of_integer v hb1
    (Units.mk0 (v.intValuation D) (v.intValuation_ne_zero D hD))
  simp only [Units.val_mk0] at hs
  refine ⟨s, ?_⟩
  have hs' : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) s - algebraMap F (v.adicCompletion F) b)
      < v.intValuation D := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub,
      levelaf_valued_algebraMap]
    exact hs
  have e2 : x - algebraMap (𝓞 F) (v.adicCompletion F) s =
      -(algebraMap F (v.adicCompletion F) b - x) +
        -(algebraMap (𝓞 F) (v.adicCompletion F) s - algebraMap F (v.adicCompletion F) b) := by
    ring
  rw [e2]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [Valuation.map_neg]; exact hb
  · rw [Valuation.map_neg]; exact hs'

theorem csApprox_global (D : 𝓞 F) (hD : D ≠ 0) (a : FiniteAdeleRing (𝓞 F) F) (ha : a ∈ intAd F) :
    ∃ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
  classical
  have hP := levelaf_finite_places D hD
  choose s hs using fun v : HeightOneSpectrum (𝓞 F) => csApprox_local v D hD (a v) (ha v)
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hP.toFinset)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {D})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => s v)
  refine ⟨r, fun v => ?_⟩
  by_cases hv : v ∈ hP.toFinset
  · have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
    rw [← v.intValuation_eq_exp_neg_multiplicity hD] at h1
    have e1 : a v - algebraMap (𝓞 F) (v.adicCompletion F) r =
        (a v - algebraMap (𝓞 F) (v.adicCompletion F) (s v)) +
          -(algebraMap (𝓞 F) (v.adicCompletion F) (r - s v)) := by
      rw [map_sub]; ring
    rw [e1, csApprox_val_int]
    refine Valuation.map_add_le _ (hs v).le ?_
    rw [Valuation.map_neg, csApprox_val_int]
    exact h1
  · have hv' : ¬ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := by simpa using hv
    have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) = 1 :=
      le_antisymm ((mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v v D)) (not_lt.1 hv')
    rw [h1]
    exact (mem_adicCompletionIntegers _ _ _).1 (sub_mem (ha v) (levelaf_int_mem_v v r))

end CsApprox

theorem integral_adele_approximation_holds : Formalism.UG.CS.IntAdApprox := by
  intro F _ _ D hD a ha
  obtain ⟨r, hle⟩ := csApprox_global D hD a ha
  set y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F D)⁻¹ *
    (a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) with hy
  refine ⟨r, y, fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ *
        (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ∈ _
    have hne : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (levelaf_algebraMap_ne_zero v D hD)
    rw [mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀,
      ← IsScalarTower.algebraMap_apply]
    calc _ ≤ (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D))⁻¹ *
          Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := mul_le_mul_right (hle v) _
      _ = 1 := inv_mul_cancel₀ hne
  · have hD' : algebraMap (𝓞 F) F D ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD
    rw [hy, IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) D, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ hD', map_one, one_mul]
    ring

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEquiv
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem csEquiv_bc_mulVec (γ : GL n E) (x : n → E) :
    (((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i))) =
      fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((γ : Matrix n n E) *ᵥ x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem csEquiv_mem (Λ : Submodule (𝓞 E) (n → E)) (γ : GL n E)
    (g k : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)) (x : n → E) :
    x ∈ globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k) Λ ↔
      ((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x ∈ globLat g Λ := by
  have hki := (stabGL _).inv_mem hk
  show (((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k)⁻¹ :
      GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
    ((g⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x) i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← map_inv, csEquiv_bc_mulVec]
  exact (hki _).symm

theorem csEquiv_main (Λ : Submodule (𝓞 E) (n → E)) (γ : GL n E)
    (g k : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)) :
    globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k) Λ =
      Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat g Λ) := by
  ext x
  rw [csEquiv_mem Λ γ g k hk x]
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [glEquiv_apply', Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [glEquiv_apply', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact hy

end

theorem global_lattice_equiv_holds : Formalism.UG.CS.GlobLatEquiv := by
  intro F E _ _ _ _ _ n _ _ Λ γ g k hk
  exact csEquiv_main Λ γ g k hk

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEasy
noncomputable section

open Matrix NumberField

namespace Formalism.UG.P

theorem sigma_involution_holds : Formalism.UG.CS.SigmaInvol := by
  intro F E _ _ _ _ _ σ hσ e
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have h : ∀ x, τ (σ x) = starRingEnd ℂ (τ x) := fun x => by
    simpa using RingHom.congr_fun (hσ τ) x
  apply τ.injective
  rw [h, h, Complex.conj_conj]

theorem csEasy_stdLat_eq_range (E : Type) [Field E] [NumberField E] (n : Type) [Fintype n]
    [DecidableEq n] :
    Formalism.UG.stdLat (n := n) (A := E) (𝓞 E) =
      LinearMap.range (LinearMap.pi (fun i : n =>
        (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i))) := by
  ext x
  simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i => by simpa using hy i⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, by simp⟩

theorem standard_lattice_full_holds : Formalism.UG.CS.StdLatFull := by
  intro E _ _ n _ _
  refine ⟨?_, ?_⟩
  · rw [csEasy_stdLat_eq_range]
    infer_instance
  · rw [eq_top_iff, ← (Pi.basisFun E n).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    show Pi.basisFun E n i ∈ Formalism.UG.stdLat (n := n) (A := E) (𝓞 E)
    simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range,
      Pi.basisFun_apply]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩

theorem csEasy_formJ_apply {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ e, σ (σ e) = e)
    {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (c : E) (x y : n → E) :
    Formalism.UG.CS.formJ σ hσ J c x y = c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.CS.formJ Formalism.UG.hform
  rw [Matrix.toLinearMapₛₗ₂'_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show σ (x i) * (y j * (c * J i j)) = c * (σ (x i) * J i j * y j)
  ring

theorem hermitian_form_symmetry_holds : Formalism.UG.CS.FormSymm := by
  intro E _ σ hσ n _ _ J c hc hJ
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using this
  refine ⟨?_, fun x y => csEasy_formJ_apply σ hσ J c x y⟩
  constructor
  intro x y
  rw [csEasy_formJ_apply, csEasy_formJ_apply]
  show σ (c * Formalism.UG.hform σ J x y) = c * Formalism.UG.hform σ J y x
  rw [map_mul, hc]
  congr 1
  unfold Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hσ, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma hform_mulVec_mulVec_of_cT_mul_mul_eq {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    [DecidableEq n] (J M : Matrix n n E) (x y : n → E) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have e : ∀ (A : Matrix n n E) (u v : n → E),
      Formalism.UG.hform σ A u v = (fun i => σ (u i)) ⬝ᵥ (A *ᵥ v) := by
    intro A u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hs : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, map_sum]
  rw [e, e, hs, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Formalism.UG.cT]
  simp only [Matrix.mul_assoc]

private lemma hform_single_single_stabilizer_orbit_volume {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    [DecidableEq n] (A : Matrix n n E) (i j : n) :
    Formalism.UG.hform σ A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [Formalism.UG.hform, Pi.single_apply]

theorem unitary_isometry_lattice_holds : Formalism.UG.CS.IsomUJ := by
  intro E _ σ hσ n _ _ J c hc hcσ g
  have hg : ∀ x, Formalism.UG.glEquiv g x = (g : Matrix n n E) *ᵥ x := fun x => rfl
  show Formalism.UG.cT σ (g : Matrix n n E) * J * (g : Matrix n n E) = J ↔ _
  show _ ↔ ∀ x y, _ = _
  simp only [hg, csEasy_formJ_apply, hform_mulVec_mulVec_of_cT_mul_mul_eq, mul_right_inj' hc]
  constructor
  · intro h x y
    rw [h]
  · intro h
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rwa [hform_single_single_stabilizer_orbit_volume, hform_single_single_stabilizer_orbit_volume] at this

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section

variable {F : Type} [Field F] [NumberField F]

theorem csGlobApprox_vD (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by
  first
  | exact (v.valuedAdicCompletion_eq_valuation r).trans (v.valuation_of_algebraMap r)
  | exact (v.valuedAdicCompletion_eq_valuation r).trans (v.valuation_of_algebraMap (K := F) r)
  | (rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
     exact (v.valuedAdicCompletion_eq_valuation' _).trans (v.valuation_of_algebraMap (K := F) r))

theorem csGlobApprox_local (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
  set Dv := algebraMap (𝓞 F) (v.adicCompletion F) D with hDvdef
  have hDv : Dv ≠ 0 := levelaf_algebraMap_ne_zero v D hD
  have hDv0 : Valued.v Dv ≠ 0 := (Valuation.ne_zero_iff _).2 hDv
  have hDv1 : Valued.v Dv ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 (levelaf_int_mem_v v D)
  have hx1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 hx
  have ho : IsOpen ((fun y => (y - x) * Dv⁻¹) ⁻¹'
      ((Valued.v : Valuation (v.adicCompletion F) _).integer : Set (v.adicCompletion F))) :=
    (Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)
  obtain ⟨f, hf⟩ := (HeightOneSpectrum.denseRange_algebraMap F v).exists_mem_open ho
    ⟨x, by simp⟩
  have hf' : Valued.v (algebraMap F (v.adicCompletion F) f - x) ≤ Valued.v Dv := by
    change (algebraMap F (v.adicCompletion F) f - x) * Dv⁻¹ ∈
      (Valued.v : Valuation (v.adicCompletion F) _).integer at hf
    have h := (Valuation.mem_integer_iff _ _).1 hf
    simp only [map_mul, map_inv₀] at h
    calc Valued.v (algebraMap F (v.adicCompletion F) f - x)
        = Valued.v (algebraMap F (v.adicCompletion F) f - x) * (Valued.v Dv)⁻¹ * Valued.v Dv := by
          rw [inv_mul_cancel_right₀ hDv0]
      _ ≤ 1 * Valued.v Dv := mul_le_mul_left h _
      _ = Valued.v Dv := one_mul _
  have hfv : v.valuation F f ≤ 1 := by
    rw [← levelaf_valued_algebraMap]
    rw [show algebraMap F (v.adicCompletion F) f = (algebraMap F (v.adicCompletion F) f - x) + x by
      ring]
    exact Valuation.map_add_le _ (hf'.trans hDv1) hx1
  have hD' : v.intValuation D ≠ 0 := by rw [← csGlobApprox_vD]; exact hDv0
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hfv (Units.mk0 _ hD')
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) f)
      ≤ Valued.v Dv := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub,
      levelaf_valued_algebraMap, hDvdef, csGlobApprox_vD]
    exact ha.le
  rw [show x - algebraMap (𝓞 F) (v.adicCompletion F) a =
      -(algebraMap F (v.adicCompletion F) f - x) +
        -(algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) f) by ring]
  exact Valuation.map_add_le _ (by rw [Valuation.map_neg]; exact hf')
    (by rw [Valuation.map_neg]; exact h2)

end

private theorem exists_not_mem_asIdeal_pow_of_ne_zero {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (z : 𝓞 F) (hz : z ≠ 0) :
    ∃ n : ℕ, z ∉ w.asIdeal ^ n := by
  by_contra h
  push_neg at h
  have hmem : z ∈ ⨅ i : ℕ, w.asIdeal ^ i := Submodule.mem_iInf _ |>.2 h
  rw [Ideal.iInf_pow_eq_bot_of_isDomain] at hmem
  · exact hz ((Submodule.mem_bot _).1 hmem)
  · exact w.isPrime.ne_top

private theorem intValuation_lt_of_mem_pow_of_not_mem_pow {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {z D : 𝓞 F} {n : ℕ}
    (hDn : D ∉ w.asIdeal ^ n) (hz : z ∈ w.asIdeal ^ n) : w.intValuation z < w.intValuation D :=
  lt_of_le_of_lt ((w.intValuation_le_pow_iff_mem z n).2 hz)
    (not_le.1 fun h => hDn ((w.intValuation_le_pow_iff_mem D n).1 h))

private theorem valued_v_algebraMap_adicCompletion {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (w.adicCompletion F) k) = w.valuation F k := by
  first
  | exact w.valuedAdicCompletion_eq_valuation' k
  | rfl
  | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem csGlob_intAdApprox : Formalism.UG.CS.IntAdApprox := by
  intro F _ _ D hD a ha
  classical
  have ha' : ∀ w : HeightOneSpectrum (𝓞 F), a w ∈ w.adicCompletionIntegers F := ha
  have hfin : {w : HeightOneSpectrum (𝓞 F) | D ∈ w.asIdeal}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {D})
      (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hD)
    simpa only [Ideal.dvd_span_singleton] using h
  choose r hr using fun w : HeightOneSpectrum (𝓞 F) => csGlobApprox_local w D hD (a w) (ha' w)
  choose e he using fun w : HeightOneSpectrum (𝓞 F) => exists_not_mem_asIdeal_pow_of_ne_zero w D hD
  obtain ⟨r0, hr0⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
    (fun w => w.asIdeal) e (fun w _ => w.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun w => r w.1)
  have hγ : ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation D ≠ 0 := fun w =>
    (lt_of_le_of_lt zero_le' (intValuation_lt_of_mem_pow_of_not_mem_pow w (he w) (Submodule.zero_mem _))).ne'
  have hbound : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) ≤ w.intValuation D := by
    intro w
    by_cases hw : D ∈ w.asIdeal
    · have hmem := hr0 w (hfin.mem_toFinset.2 hw)
      have h1 := hr w
      rw [csGlobApprox_vD] at h1
      have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) (r w) -
          algebraMap (𝓞 F) (w.adicCompletion F) r0) ≤ w.intValuation D := by
        rw [Valuation.map_sub_swap, ← map_sub, csGlobApprox_vD]
        exact (intValuation_lt_of_mem_pow_of_not_mem_pow w (he w) hmem).le
      rw [← sub_add_sub_cancel (a w) (algebraMap (𝓞 F) (w.adicCompletion F) (r w))]
      exact Valuation.map_add_le _ h1 h2
    · have h1 : w.intValuation D = 1 := by
        refine le_antisymm (w.intValuation_le_one D) ?_
        by_contra hlt
        push_neg at hlt
        first
        | exact hw ((w.intValuation_lt_one_iff_mem D).1 hlt)
        | exact hw (Ideal.dvd_span_singleton.1 ((w.intValuation_lt_one_iff_dvd D).1 hlt))
      rw [h1]
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
      · exact ha' w
      · rw [csGlobApprox_vD]
        exact w.intValuation_le_one r0
  have hd : algebraMap (𝓞 F) F D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD
  have hsc : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) D =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D) := by
    first
    | exact IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) D
    | rfl
  have hunit : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) D *
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D)⁻¹ = 1 := by
    rw [hsc, ← map_mul, mul_inv_cancel₀ hd, map_one]
  obtain ⟨Y, hY⟩ : ∃ Y : FiniteAdeleRing (𝓞 F) F, Y =
      (a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r0) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D)⁻¹ := ⟨_, rfl⟩
  refine ⟨r0, Y, (fun w => ?_ : ∀ w : HeightOneSpectrum (𝓞 F), Y w ∈ w.adicCompletionIntegers F), ?_⟩
  · have hcoord : Y w = (a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) *
        algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ := by
      rw [hY]
      first
      | rfl
      | simp
    rw [hcoord]
    have hle : Valued.v ((a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) *
        algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹) ≤ 1 := by
      rw [map_mul, valued_v_algebraMap_adicCompletion, map_inv₀, w.valuation_of_algebraMap]
      calc _ ≤ w.intValuation D * (w.intValuation D)⁻¹ := by
            first
            | exact mul_le_mul_right (hbound w) _
            | exact mul_le_mul_of_nonneg_right (hbound w) zero_le'
            | (gcongr; exact hbound w)
        _ = 1 := mul_inv_cancel₀ (hγ w)
    exact hle
  · rw [hY]
    linear_combination (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r0 - a) * hunit

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaFinal

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem fIwasawa_ordL_mul (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have hxy' : Valued.v (x * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hx' hy'
  unfold Formalism.UG.ordL
  rw [dite_eq_right hxy', dite_eq_right hx', dite_eq_right hy']
  have key : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_mul, WithZero.coe_unzero, map_mul]
  rw [key, toAdd_mul]
  ring

theorem fIwasawa_ordL_unit (x y : L) (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1)
    (hxy : y * x = 1) : ordL x = 0 := by
  have h1 : Valued.v y * Valued.v x = 1 := by
    have := congrArg Valued.v hxy
    rwa [map_mul, map_one] at this
  have hge : 1 ≤ Valued.v x :=
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v y * Valued.v x := h1.symm
      _ ≤ 1 * Valued.v x := by gcongr
      _ = Valued.v x := one_mul _
  have hv : Valued.v x = 1 := le_antisymm hx hge
  have hne : Valued.v x ≠ 0 := by rw [hv]; exact one_ne_zero
  unfold Formalism.UG.ordL
  rw [dite_eq_right hne]
  have key : WithZero.unzero hne = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, hv, WithZero.coe_one]
  rw [key, toAdd_one, neg_zero]

variable (σ : L →+* L) {n m : ℕ} (q : ℕ) (α : Fin m → ℂ)

private lemma blockTriangular_mul_diag (B C : Matrix (Fin n) (Fin n) L)
    (hB : B.BlockTriangular id) (hC : C.BlockTriangular id) (i : Fin n) :
    (B * C) i i = B i i * C i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hB (show id k < id i from h), zero_mul]
    · rw [hC (show id i < id k from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

private lemma GL_blockTriangular_diag_ne_zero (g : GL (Fin n) L)
    (hg : (g : Matrix (Fin n) (Fin n) L).BlockTriangular id) (i : Fin n) :
    (g : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  have hdet : (g : Matrix (Fin n) (Fin n) L).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (Units.mul_inv g)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  rw [Matrix.det_of_upperTriangular hg] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)

theorem fIwasawa_chi_mul (hα : ∀ i, α i ≠ 0) (hq : (q : ℂ) ≠ 0) (b c : GU σ n)
    (hb : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hc : ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    chiDeltaU q α (b * c) = chiDeltaU q α b * chiDeltaU q α c := by
  have hdb := GL_blockTriangular_diag_ne_zero (b : GL (Fin n) L) hb
  have hdc := GL_blockTriangular_diag_ne_zero (c : GL (Fin n) L) hc
  have hbc : ∀ i : Fin n, (((b * c : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i :=
    fun i => blockTriangular_mul_diag _ _ hb hc i
  unfold Formalism.UG.chiDeltaU
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  split_ifs with h
  · rw [hbc ⟨i.val, h⟩, fIwasawa_ordL_mul _ _ (hdb ⟨i.val, h⟩) (hdc ⟨i.val, h⟩)]
    rw [zpow_add₀ (hα i), neg_add, add_mul, zpow_add₀ hq]
    ring
  · rw [mul_one]

private lemma GL_inv_blockTriangular (g : GL (Fin n) L)
    (hg : (g : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hg

private lemma KU_entries_valuation_le_one (g : GU σ n) (hg : g ∈ KU σ n) (i j : Fin n) :
    Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 ∧
    Valued.v ((((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 := by
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf] at hg
  obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp hg.2
  rw [← hg', ← map_inv]
  refine ⟨?_, ?_⟩
  · exact (Valuation.mem_integer_iff _ _).mp ((g' : Matrix (Fin n) (Fin n) (intL L)) i j).2
  · exact (Valuation.mem_integer_iff _ _).mp
      (((g'⁻¹ : GL (Fin n) (intL L)) : Matrix (Fin n) (Fin n) (intL L)) i j).2

theorem fIwasawa_chi_int (b : GU σ n)
    (hb : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id) (hk : b ∈ KU σ n) :
    chiDeltaU q α b = 1 := by
  have hbinv := GL_inv_blockTriangular (b : GL (Fin n) L) hb
  unfold Formalism.UG.chiDeltaU
  apply Finset.prod_eq_one
  intro i _
  split_ifs with h
  · have h0 : ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩) = 0 := by
      apply fIwasawa_ordL_unit _ ((((b : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)
        (KU_entries_valuation_le_one σ b hk _ _).1 (KU_entries_valuation_le_one σ b hk _ _).2
      rw [← blockTriangular_mul_diag _ _ hbinv hb, Units.inv_mul]
      exact Matrix.one_apply_eq _
    rw [h0]
    simp
  · rfl

theorem fIwasawa_iwasawa (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (g : GU σ n) : ∃ b k : GU σ n, IsBorelU b ∧ k ∈ KU σ n ∧ g = b * k := by
  obtain ⟨k, hk, hup⟩ := fIwasawa_upper σ hσ hσv _ (fIwasawa_mem_un σ g⁻¹)
  have hkG : fIwasawaMk σ k hk.1 ∈ KU σ n := fIwasawa_mk_mem_K σ hσv k hk.1 hk.2
  refine ⟨(fIwasawaMk σ k hk.1 * g⁻¹)⁻¹, fIwasawaMk σ k hk.1, ?_, hkG, by group⟩
  have h1 : (((fIwasawaMk σ k hk.1 * g⁻¹ : GU σ n) : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L).BlockTriangular id := by
    rw [Subgroup.coe_mul, Units.val_mul, fIwasawa_mk_val]; exact hup
  have h2 := spherical_upper_inv _ h1
  rw [← Subgroup.coe_inv] at h2
  exact (spherical_upper_iff _).2 h2

theorem fIwasawa_wd (hα : ∀ i, α i ≠ 0) (hq : (q : ℂ) ≠ 0) (b b' k k' : GU σ n)
    (hb : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hb' : ((b' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hk : k ∈ KU σ n) (hk' : k' ∈ KU σ n) (h : b * k = b' * k') :
    chiDeltaU q α b = chiDeltaU q α b' := by
  have hc_eq : b = b' * (k' * k⁻¹) := by
    calc b = b * k * k⁻¹ := by group
      _ = b' * k' * k⁻¹ := by rw [h]
      _ = b' * (k' * k⁻¹) := by group
  have hkk : k' * k⁻¹ ∈ KU σ n := (KU σ n).mul_mem hk' ((KU σ n).inv_mem hk)
  have hc_eq2 : k' * k⁻¹ = b'⁻¹ * b := by rw [hc_eq]; group
  have htri : (((k' * k⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
    rw [hc_eq2]
    exact Matrix.BlockTriangular.mul (GL_inv_blockTriangular (b' : GL (Fin n) L) hb') hb
  rw [hc_eq, fIwasawa_chi_mul σ q α hα hq b' (k' * k⁻¹) hb' htri,
    fIwasawa_chi_int σ q α (k' * k⁻¹) htri hkk, mul_one]

end FIwasawaFinal

theorem exists_spherical_function_unitary : Formalism.UG.SphericalExistsU := by
  intro L _ _ _ ϖ σ q n m hU hmn hnm α hα
  obtain ⟨hσ, hσv, -, -, -, hq2, -⟩ := hU
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  choose B K hB hK hBK using fIwasawa_iwasawa (n := n) σ hσ hσv
  have htri : ∀ g : GU σ n, IsBorelU g →
      (((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
    intro g hg i j hij
    exact hg i j hij
  have h1tri : (((1 : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
    Matrix.blockTriangular_one
  refine ⟨fun g => chiDeltaU q α (B g), ?_, ?_, ?_⟩
  · intro b g k hb hk
    have e : b * g * k = (b * B g) * (K g * k) := by
      conv_lhs => rw [hBK g]
      simp only [mul_assoc]
    have hbB : (((b * B g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
      Matrix.BlockTriangular.mul (htri b hb) (htri _ (hB g))
    have hKk : K g * k ∈ KU σ n := (KU σ n).mul_mem (hK g) hk
    show chiDeltaU q α (B (b * g * k)) = chiDeltaU q α b * chiDeltaU q α (B g)
    rw [fIwasawa_wd σ q α hα hq (B (b * g * k)) (b * B g) (K (b * g * k)) (K g * k)
      (htri _ (hB _)) hbB (hK _) hKk (by rw [← hBK, e])]
    exact fIwasawa_chi_mul σ q α hα hq b (B g) (htri b hb) (htri _ (hB g))
  · show chiDeltaU q α (B 1) = 1
    rw [fIwasawa_wd σ q α hα hq (B 1) 1 (K 1) 1 (htri _ (hB 1)) h1tri (hK 1) (KU σ n).one_mem
      (by rw [← hBK, mul_one])]
    exact fIwasawa_chi_int σ q α 1 h1tri (KU σ n).one_mem
  · intro ψ hψ
    funext g
    have hg := hψ (B g) 1 (K g) (hB g) (hK g)
    rw [mul_one, ← hBK] at hg
    rw [hg]
    exact mul_comm _ _

end Formalism.UG.P
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsAsmHformSmulRight
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

theorem csAsm_hform_smul_right {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    (J : Matrix n n E) (c : E) (y x : n → E) :
    hform σ J y (c • x) = c * hform σ J y x := by
  unfold Formalism.UG.hform
  simp [Matrix.mulVec_smul, dotProduct_smul, Finset.mul_sum, smul_eq_mul, mul_left_comm]

theorem csAsm_gmap_mul {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (a b : V ≃ₗ[K] V)
    (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  first
  | rfl
  | (congr 1; ext x; simp [LinearEquiv.mul_apply])

theorem csAsm_gmap_one {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  simp

theorem csAsm_gmap_inv {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (a : V ≃ₗ[K] V)
    (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a L) = L := by
  rw [← csAsm_gmap_mul, inv_mul_cancel, csAsm_gmap_one]

theorem classSetFiniteL_of (hSigmaInvol : Formalism.UG.CS.SigmaInvol) (hTracePos : Formalism.UG.CS.TracePos)
    (hFormSymm : Formalism.UG.CS.FormSymm) (hIsomUJ : Formalism.UG.CS.IsomUJ)
    (hGlobLatLattice : Formalism.UG.CS.GlobLatLattice) (hClassInj : Formalism.UG.CS.ClassInj)
    (hScaleBound : Formalism.UG.CS.ScaleBound) (hDualBound : Formalism.UG.CS.DualBound)
    (hClassSetFiniteBdd : Formalism.UG.CS.ClassSetFiniteBdd) (hStdLatFull : Formalism.UG.CS.StdLatFull) :
    Formalism.UG.ClassSetFiniteL := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hJ hdet hdef Λ hfin hspan
  have hinv : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e := fun e => hSigmaInvol F E σ hσ e
  obtain ⟨c, hc0, hcpos⟩ := hTracePos F E n σ J hdef
  set cE : E := algebraMap F E (c : F) with hcE
  have hσc : (σ : E →+* E) cE = cE := by
    rw [hcE]
    exact σ.commutes _
  have hcF : ((c : 𝓞 F) : F) ≠ 0 := by
    intro h
    apply hc0
    first
    | exact_mod_cast h
    | exact RingOfIntegers.ext h
  have hcE0 : cE ≠ 0 := by
    rw [hcE]
    exact (map_ne_zero _).mpr hcF
  set cO : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) c with hcO
  have hcOE : algebraMap (𝓞 E) E cO = cE := by
    rw [hcO, hcE, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
  have hcO0 : cO ≠ 0 := by
    intro h
    apply hcE0
    rw [← hcOE, h, map_zero]
  letI : StarRing E := starOfInv (σ : E →+* E) hinv
  obtain ⟨hsymm, hfe⟩ := hFormSymm E (σ : E →+* E) hinv n J cE hσc hJ
  obtain ⟨d, hd0, hd⟩ := hScaleBound F E n σ J Λ hfin hspan
  obtain ⟨e, he0, he⟩ := hDualBound F E n σ J Λ hdet hfin hspan
  have hpos : ∀ x : n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (formJ (σ : E →+* E) hinv J cE x x) := by
    intro x hx
    rw [hfe]
    exact hcpos x hx
  obtain ⟨s, hs⟩ := hClassSetFiniteBdd E (n → E) (formJ (σ : E →+* E) hinv J cE) hsymm hpos d (e * cO) hd0
    (mul_ne_zero he0 hcO0)
  have key : ∀ g : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ N ∈ s, ∃ φ ∈ Formalism.HermitianLatticesTheory.isom (formJ (σ : E →+* E) hinv J cE),
      Formalism.HermitianLatticesTheory.gmap φ N = globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ := by
    intro g
    apply hs
    · exact hGlobLatLattice F E n Λ hfin hspan g
    · intro x hx y hy
      rw [hfe, Submodule.mem_one]
      obtain ⟨o, ho⟩ := hd g g.2 x hx y hy
      refine ⟨o * cO, ?_⟩
      rw [map_mul, ho, hcOE]
      show algebraMap (𝓞 E) E d * hform (σ : E →+* E) J x y * cE = algebraMap (𝓞 E) E d * (cE * hform (σ : E →+* E) J x y)
      ring
    · intro x hx
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, Submodule.mem_one] at hx
      have hx' : ∀ y ∈ globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ,
          hform (σ : E →+* E) J y (cE • x) ∈ (algebraMap (𝓞 E) E).range := by
        intro y hy
        obtain ⟨o, ho⟩ := hx y hy
        rw [hfe] at ho
        refine ⟨o, ?_⟩
        rw [csAsm_hform_smul_right]
        exact ho
      have h2 := he g g.2 (cE • x) hx'
      convert h2 using 1
      show algebraMap (𝓞 E) E (e * cO) • x = algebraMap (𝓞 E) E e • cE • x
      rw [map_mul, hcOE, smul_smul]
  classical
  choose N hN φ hφ hφN using key
  let f : ClassSet ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) → s :=
    fun q => ⟨N (Quotient.out q), hN (Quotient.out q)⟩
  have hf : Function.Injective f := by
    intro q1 q2 h12
    have hNN : N (Quotient.out q1) = N (Quotient.out q2) := congrArg Subtype.val h12
    obtain ⟨γ, hγ⟩ : ∃ γ : GL n E, glEquiv γ = φ (Quotient.out q1) * (φ (Quotient.out q2))⁻¹ :=
      ⟨Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (n → E)).symm
        (φ (Quotient.out q1) * (φ (Quotient.out q2))⁻¹)), by simp [glEquiv]⟩
    have hUJ : γ ∈ UJ (σ : E →+* E) J :=
      (hIsomUJ E (σ : E →+* E) hinv n J cE hcE0 hσc γ).mpr (by
        rw [hγ]
        exact mul_mem (hφ _) (inv_mem (hφ _)))
    have hlat : globLat ((Quotient.out q1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ =
        Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat ((Quotient.out q2 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
          GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) := by
      rw [hγ, csAsm_gmap_mul, ← hφN (Quotient.out q2), csAsm_gmap_inv, ← hNN, hφN]
    have h3 := hClassInj F E n σ J Λ hfin hspan (Quotient.out q1) (Quotient.out q2) γ hUJ hlat
    rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at h3
  exact Finite.of_injective f hf

theorem classSetFinite_of (hSigmaInvol : Formalism.UG.CS.SigmaInvol) (hTracePos : Formalism.UG.CS.TracePos)
    (hFormSymm : Formalism.UG.CS.FormSymm) (hIsomUJ : Formalism.UG.CS.IsomUJ)
    (hGlobLatLattice : Formalism.UG.CS.GlobLatLattice) (hClassInj : Formalism.UG.CS.ClassInj)
    (hScaleBound : Formalism.UG.CS.ScaleBound) (hDualBound : Formalism.UG.CS.DualBound)
    (hClassSetFiniteBdd : Formalism.UG.CS.ClassSetFiniteBdd) (hStdLatFull : Formalism.UG.CS.StdLatFull) :
    Formalism.UG.ClassSetFinite := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hJ hdet hdef
  have h := classSetFiniteL_of hSigmaInvol hTracePos hFormSymm hIsomUJ hGlobLatLattice hClassInj hScaleBound
    hDualBound hClassSetFiniteBdd hStdLatFull F E n σ J hσ hJ hdet hdef (stdLat (n := n) (A := E) (𝓞 E))
    (hStdLatFull E n).1 (hStdLatFull E n).2
  have heq : levelAfL σ J (stdLat (n := n) (A := E) (𝓞 E)) = levelAf σ J := by
    unfold Formalism.UG.levelAfL Formalism.UG.levelAf
    congr 1
    apply le_antisymm
    · unfold Formalism.UG.latS
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range] at hx ⊢
      intro i
      obtain ⟨a, ha⟩ := hx i
      exact ⟨⟨inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i),
        Subring.subset_closure (Or.inl ⟨⟨x i, a, ha⟩, rfl⟩)⟩, rfl⟩
    · intro v hv
      simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range] at hv
      unfold Formalism.UG.latS
      rw [pi_eq_sum_univ v]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      obtain ⟨y, hy⟩ := hv i
      have hy' : (y : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = v i := hy
      have hsm : (v i • fun j => if i = j then (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) else 0) =
          y • (fun j => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (if i = j then (1 : E) else 0)) := by
        ext j
        simp only [Pi.smul_apply, smul_eq_mul, Subring.smul_def]
        rw [← hy']
        split_ifs <;> simp
      rw [hsm]
      refine Submodule.smul_mem _ y (Submodule.subset_span ⟨fun j => if i = j then (1 : E) else 0, ?_, rfl⟩)
      simp only [SetLike.mem_coe, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range]
      intro j
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
  rw [heq] at h
  exact h

end Formalism.UG.P
end
end
