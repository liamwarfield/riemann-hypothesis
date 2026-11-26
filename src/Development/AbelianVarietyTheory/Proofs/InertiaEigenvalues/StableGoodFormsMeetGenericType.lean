module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UupEqOneOfLeOne
noncomputable section

namespace GlobalTheory.MeetsGen

def pU {K G : Type} [Field K] [Group G] (U : Subgroup G) [Fintype U] (f : U → K) : MonoidAlgebra K G :=
  ∑ u : U, MonoidAlgebra.single (u : G) ((Fintype.card U : K)⁻¹ * f u)

def cU {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K) : MonoidAlgebra K G :=
  ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U f * MonoidAlgebra.single g⁻¹ (1 : K)

def uElt {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K) (e : MonoidAlgebra K G) :
    MonoidAlgebra K G :=
  cU U f * e + (1 - e)

theorem uup_eq_one_of_le_one {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ) (hr : r ≤ 1) (u : Formalism.L2.NX.GProd p r)
    (hu : u ∈ Formalism.L2.NX.Uup p r) : u = 1 := by
  funext x
  apply Units.ext
  ext a c
  have ha : a = c := Fin.ext (by have := a.2; have := c.2; omega)
  subst ha
  simp only [Pi.one_apply, Units.val_one, Matrix.one_apply_eq]
  exact ((Formalism.L2.NX.mem_Uup).1 hu x).2 a

theorem map_uElt {E L G : Type} [Field E] [Field L] [Group G] [Fintype G] (j : E →+* L) (U : Subgroup G) [Fintype U]
    (f : U → E) (e : MonoidAlgebra E G) :
    MonoidAlgebra.mapRingHom G j (uElt U f e) = uElt U (fun u => j (f u)) (MonoidAlgebra.mapRingHom G j e) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [uElt, cU, pU, map_add (f := _), map_mul, map_sub, map_one, map_sum, MonoidAlgebra.mapRingHom_single, map_inv₀,
    map_natCast]

theorem eq_sum_of_uElt_mul {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K)
    (e v : MonoidAlgebra K G) (hI : e * e = e) (hC : ∀ a, e * a = a * e) (hv : uElt U f e * v = 1) :
    e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U f * (MonoidAlgebra.single g⁻¹ (1 : K) * e * v) := by
  have h1 : e * uElt U f e = cU U f * e := by
    simp only [uElt]
    rw [mul_add, mul_sub, mul_one, hI, sub_self, add_zero, ← mul_assoc, hC (cU U f), mul_assoc, hI]
  calc e = e * (uElt U f e * v) := by rw [hv, mul_one]
    _ = cU U f * e * v := by rw [← mul_assoc, h1]
    _ = _ := by
      simp only [cU, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [mul_assoc]

end GlobalTheory.MeetsGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRightInverseCentralProjectorUnitElement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRightInverseCentralProjectorUnitElement
open GlobalTheory.MeetsGen CategoryTheory

noncomputable section

namespace GlobalTheory.MeetsUnit

variable {G : Type} [Group G] [Fintype G]

theorem single_mul_cU (U : Subgroup G) [Fintype U] (f : U → ℂ) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * cU U f = cU U f * MonoidAlgebra.single h 1 := by
  unfold cU
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
  have e1 : MonoidAlgebra.single (h * g) (1 : ℂ) = MonoidAlgebra.single h 1 * MonoidAlgebra.single g 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul]
  have e2 : MonoidAlgebra.single (h * g)⁻¹ (1 : ℂ) * MonoidAlgebra.single h 1 = MonoidAlgebra.single g⁻¹ 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul, mul_inv_rev, inv_mul_cancel_right]
  simp only [Equiv.coe_mulLeft]
  rw [mul_assoc _ (MonoidAlgebra.single (h * g)⁻¹ (1 : ℂ)), e2, e1]
  simp only [mul_assoc]

theorem single_mul_uElt (U : Subgroup G) [Fintype U] (f : U → ℂ) (e : MonoidAlgebra ℂ G)
    (hC : ∀ a, e * a = a * e) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * uElt U f e = uElt U f e * MonoidAlgebra.single h 1 := by
  have hc := single_mul_cU U f h
  have he := hC (MonoidAlgebra.single h 1)
  simp only [uElt, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul]
  rw [he, mul_assoc (cU U f) e, he, ← mul_assoc, ← mul_assoc, hc]

theorem trace_cU (V : FDRep ℂ G) (U : Subgroup G) [Fintype U] (f : U → ℂ) :
    LinearMap.trace ℂ V (Representation.asAlgebraHom V.ρ (cU U f)) =
      (Fintype.card G : ℂ) * ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) * V.character u := by
  have hp : Representation.asAlgebraHom V.ρ (pU U f) = ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) • V.ρ u := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pU, map_sum, Representation.asAlgebraHom_single]
  unfold cU
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  rw [Finset.sum_congr rfl (fun g _ => by
    rw [map_mul (Representation.asAlgebraHom V.ρ), map_mul (Representation.asAlgebraHom V.ρ), Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, one_smul,
      one_smul, LinearMap.trace_mul_comm ℂ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul])]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hp, map_sum]
  simp only [map_smul, smul_eq_mul, FDRep.character]

def lreg : Representation ℂ G (MonoidAlgebra ℂ G) :=
  (Algebra.lmul ℂ (MonoidAlgebra ℂ G)).toRingHom.toMonoidHom.comp (MonoidAlgebra.of ℂ G)

theorem lreg_apply (g : G) (x : MonoidAlgebra ℂ G) : lreg g x = MonoidAlgebra.single g 1 * x := rfl

theorem exists_rightInv_uElt : ∀ {G : Type} [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (ψ : U →* ℂˣ)
    (e : MonoidAlgebra ℂ G), e * e = e → (∀ a, e * a = a * e) →
    (∀ χ : G → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, e.coeff g * χ g = χ 1 →
      ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0) →
    ∃ v : MonoidAlgebra ℂ G, uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) e * v = 1 := by
  intro G _ _ U _ ψ e hI hC hχ
  classical
  set f : U → ℂ := fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ) with hf
  set w := uElt U f e with hw
  have hinj : Function.Injective (LinearMap.mulLeft ℂ w) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    by_contra hy0
    let K : Submodule ℂ (MonoidAlgebra ℂ G) := LinearMap.ker (LinearMap.mulLeft ℂ w)
    have hK : ∀ x, x ∈ K ↔ w * x = 0 := fun x => LinearMap.mem_ker
    let A : Subrepresentation (lreg (G := G)) := ⟨K, fun g x hx => by
      rw [hK] at hx ⊢
      rw [lreg_apply, ← mul_assoc, ← single_mul_uElt U f e hC g, mul_assoc, hx, mul_zero]⟩
    haveI : Nontrivial A.toSubmodule :=
      Submodule.nontrivial_iff_ne_bot.2 (fun hb => hy0 ((Submodule.eq_bot_iff _).1 hb y hy))
    obtain ⟨τ, hτs, φ, hφ, hφ0⟩ := PI.GreenLabelSurjWork.exists_simple_constituent A.toRepresentation
    haveI := hτs
    haveI := PI.CharIdemW.nontrivial_of_simple τ
    have hcomm : ∀ a : MonoidAlgebra ℂ G, (∀ k : G, MonoidAlgebra.single k (1 : ℂ) * a = a * MonoidAlgebra.single k 1) →
        ∀ k : G, τ.ρ k * Representation.asAlgebraHom τ.ρ a = Representation.asAlgebraHom τ.ρ a * τ.ρ k := by
      intro a ha k
      rw [← Representation.asAlgebraHom_single_one, ← map_mul, ← map_mul, ha k]
    obtain ⟨μ, hμ⟩ := PI.CharIdemW.schur_scalar τ _ (hcomm w (single_mul_uElt U f e hC))
    obtain ⟨ν, hν⟩ := PI.CharIdemW.schur_scalar τ _ (hcomm e (fun k => hC _ |>.symm))
    have hφw : ∀ x, φ (Representation.asAlgebraHom τ.ρ w x) = 0 := by
      intro x
      set_option synthInstance.maxHeartbeats 100000 in
        rw [GlobalTheory.GoodFactor.asAlg_eq τ.ρ w, LinearMap.sum_apply, map_sum]
      simp only [LinearMap.smul_apply, map_smul]
      have h1 : ∀ g, φ (τ.ρ g x) = A.toRepresentation g (φ x) := fun g => LinearMap.congr_fun (hφ g) x
      simp only [h1]
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      show ∑ g, w.coeff g • (MonoidAlgebra.single g (1 : ℂ) * (φ x : MonoidAlgebra ℂ G)) = 0
      have h2 : ∀ g, w.coeff g • (MonoidAlgebra.single g (1 : ℂ) * (φ x : MonoidAlgebra ℂ G)) =
          MonoidAlgebra.single g (w.coeff g) * (φ x : MonoidAlgebra ℂ G) := fun g => by
        rw [← smul_mul_assoc, MonoidAlgebra.smul_single', mul_one]
      simp only [h2]
      rw [← Finset.sum_mul, GlobalTheory.GoodFactor.sum_single]
      exact (hK _).1 (φ x).2
    have hμ0 : μ = 0 := by
      by_contra h
      apply hφ0
      refine LinearMap.ext fun x => ?_
      have h3 : x = μ⁻¹ • Representation.asAlgebraHom τ.ρ w x := by
        rw [hμ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, inv_mul_cancel₀ h, one_smul]
      rw [h3, map_smul, hφw, smul_zero, LinearMap.zero_apply]
    have h10 : (1 : Module.End ℂ τ) ≠ 0 := one_ne_zero
    have hνν : ν * ν = ν := by
      have h4 : Representation.asAlgebraHom τ.ρ (e * e) = Representation.asAlgebraHom τ.ρ e := by rw [hI]
      rw [map_mul, hν, smul_mul_smul_comm, one_mul] at h4
      exact smul_left_injective ℂ h10 h4
    have hTw : Representation.asAlgebraHom τ.ρ w =
        Representation.asAlgebraHom τ.ρ (cU U f) * Representation.asAlgebraHom τ.ρ e + 1 -
          Representation.asAlgebraHom τ.ρ e := by
      rw [hw, uElt, map_add (f := _), map_mul, map_sub, map_one, add_sub_assoc]
    rw [hμ, hμ0, zero_smul, hν] at hTw
    have hν01 : ν * (ν - 1) = 0 := by linear_combination hνν
    rcases mul_eq_zero.mp hν01 with h0 | h0
    · rw [h0, zero_smul, mul_zero, zero_add, sub_zero] at hTw
      exact h10 hTw.symm
    · have hν1 : ν = 1 := sub_eq_zero.mp h0
      rw [hν1, one_smul, mul_one, add_sub_cancel_right] at hTw
      have htr := trace_cU τ U f
      rw [← hTw, map_zero] at htr
      have hirr := GlobalTheory.GoodFactor.isIrrChar_character τ hτs
      have hfix : ∑ g, e.coeff g * τ.character g = τ.character 1 := by
        have h5 : LinearMap.trace ℂ τ (Representation.asAlgebraHom τ.ρ e) = ∑ g, e.coeff g * τ.character g := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [GlobalTheory.GoodFactor.asAlg_eq τ.ρ e, map_sum]
          simp only [map_smul, smul_eq_mul, FDRep.character]
        rw [← h5, hν, hν1, one_smul, FDRep.character, map_one τ.ρ]
      have hne := hχ _ hirr hfix
      have h6 : ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) * τ.character u =
          (Fintype.card U : ℂ)⁻¹ * ∑ u : U, τ.character u * f u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [h6] at htr
      have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hU : (Fintype.card U : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      exact mul_ne_zero hG (mul_ne_zero hU hne) htr.symm
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hinj 1
  exact ⟨v, hv⟩

end GlobalTheory.MeetsUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRightInverseCentralProjectorUnitElementStatement
open GlobalTheory.MeetsGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_right_inverse_centralProjectorUnitElement : ∀ {G : Type} [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (ψ : U →* ℂˣ) (e : MonoidAlgebra ℂ G), e * e = e → (∀ a, e * a = a * e) → (∀ χ : G → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, e.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0) → ∃ v : MonoidAlgebra ℂ G, uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) e * v = 1 := by
  first | exact @GlobalTheory.MeetsUnit.exists_rightInv_uElt | exact GlobalTheory.MeetsUnit.exists_rightInv_uElt | (intros; apply GlobalTheory.MeetsUnit.exists_rightInv_uElt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodIdempotentIrreducibleCharacterGenericSumNeZe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodIdempotentIrreducibleCharacterGenericSumNeZe
open Formalism.BasicNotions GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.WhittakerMeets

open Formalism.L2.DIV GlobalTheory.FinGL

def addOf {p : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) : AddChar (ZMod p) ℂ where
  toFun a := (θ (Multiplicative.ofAdd a) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [ofAdd_add]

theorem addOf_ne_one {p : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) (h : θ ≠ 1) : addOf θ ≠ 1 := by
  intro h1
  apply h
  refine MonoidHom.ext fun z => Units.ext ?_
  have h2 : addOf θ (Multiplicative.toAdd z) = 1 := by rw [h1]; rfl
  exact h2

theorem addCharHom_addOf {p r : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) (h : unip (ZMod p) r) :
    ((addCharHom (addOf θ) (supHom (ZMod p) r) h : ℂˣ) : ℂ) =
      (θ (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))) : ℂ) :=
  rfl

theorem local_sum_ne_zero {p : ℕ} [hp : Fact p.Prime] {r : ℕ} [Fintype (unip (ZMod p) r)] (θ : GL (Fin r) (ZMod p) → ℂ)
    (hθ : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar θ) (θ' : Multiplicative (ZMod p) →* ℂˣ) (h' : θ' ≠ 1) :
    ∑ h : unip (ZMod p) r, θ h *
      (((θ' (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))))⁻¹ : ℂˣ) : ℂ)
      ≠ 0 := by
  obtain ⟨d, b, σ, hσ, hθe⟩ := hθ
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.finite_parInd (F := ZMod p) b σ
  have h1 := GlobalTheory.GenericProduct.sum_unip_eq (addOf θ') (parInd b σ)
  rw [GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one (ZMod p) (addOf θ') (addOf_ne_one θ' h') r _ b σ hσ, Nat.cast_one, mul_one] at h1
  have e : ∀ h : unip (ZMod p) r, θ h *
      (((θ' (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))))⁻¹ : ℂˣ) : ℂ) =
      LinearMap.trace ℂ _ (parInd b σ h) * (((addCharHom (addOf θ') (supHom (ZMod p) r) h)⁻¹ : ℂˣ) : ℂ) := by
    intro h
    rw [hθe, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, addCharHom_addOf]
    rfl
  rw [Finset.sum_congr rfl fun h _ => e h, h1]
  exact Nat.cast_ne_zero.2 Nat.card_pos.ne'

end GlobalTheory.WhittakerMeets

namespace GlobalTheory.WhittakerMeets

open Formalism.L2.DIV GlobalTheory.FinGL

theorem sum_ne_zero : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)] (U : Subgroup (G0g D.nd)) [Fintype U], U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r → ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ → 2 ≤ D.R.r → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0 := by
  intro D S _ U _ hU ψ hψ hr χ hχ he
  classical
  subst hU
  haveI hF : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fact (D.host.g kv.1).Prime := fun kv => ⟨D.host.g_prime kv.1⟩
  haveI hN : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), NeZero (D.host.g kv.1) := fun kv => ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨θ, hθ, hχe⟩ := GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product D (fun k => ⟨_, S.O k, S.eSer_def k⟩) χ hχ he
  obtain ⟨θ', hθ'1, hψe⟩ := hψ
  have hθ' := hθ'1 hr
  letI : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fintype (unip (ZMod (D.host.g kv.1)) D.R.r) := fun kv => Fintype.ofFinite _
  let f : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), unip (ZMod (D.host.g kv.1)) D.R.r → ℂ := fun kv h =>
    θ kv h * (((θ' kv (Multiplicative.ofAdd (Formalism.L2.NX.supSum D.R.r
      ((h : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))))⁻¹ : ℂˣ) : ℂ)
  let e : Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ≃
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), unip (ZMod (D.host.g kv.1)) D.R.r :=
    { toFun := fun u kv => ⟨u.1 kv, (u.2 kv).1, (u.2 kv).2⟩
      invFun := fun y => ⟨fun kv => (y kv).1, fun kv => ⟨(y kv).2.1, (y kv).2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hterm : ∀ u : Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r,
      χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) = ∏ kv, f kv (e u kv) := by
    intro u
    rw [hχe, hψe, Formalism.L2.NX.stdVal, ← Finset.prod_inv_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]
    rfl
  rw [Finset.sum_congr rfl fun u _ => hterm u, Fintype.sum_equiv e _ (fun y => ∏ kv, f kv (y kv)) fun _ => rfl,
    ← Fintype.prod_sum]
  exact Finset.prod_ne_zero_iff.2 fun kv _ => local_sum_ne_zero (θ kv) (hθ kv) (θ' kv) (hθ' kv)

end GlobalTheory.WhittakerMeets
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodIdempotentIrreducibleCharacterGenericSumNeZeStatement
open Formalism.BasicNotions GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_idempotent_irreducible_character_generic_sum_ne_zero : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)] (U : Subgroup (G0g D.nd)) [Fintype U], U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r → ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ → 2 ≤ D.R.r → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0 := by
  first | exact @GlobalTheory.WhittakerMeets.sum_ne_zero | exact GlobalTheory.WhittakerMeets.sum_ne_zero | (intros; apply GlobalTheory.WhittakerMeets.sum_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableSubmoduleMeetsCharacterTypeVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableSubmoduleMeetsCharacterTypeVectors
open GlobalTheory.MeetsGen

noncomputable section
namespace GlobalTheory.MeetsTypeVec

theorem lift_apply_mem {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (φ : G →* Module.End K V) (W : Submodule K V) (hW : ∀ g x, x ∈ W → φ g x ∈ W)
    (a : MonoidAlgebra K G) {x : V} (hx : x ∈ W) :
    MonoidAlgebra.lift K (Module.End K V) G φ a x ∈ W := by
  rw [MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun g _ => by
    rw [LinearMap.smul_apply]; exact W.smul_mem _ (hW g x hx)

theorem proj_eigen {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (φ : G →* Module.End K V) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (y : V) (u' : U) :
    φ u' (MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K))) y)
      = ((ψ u' : Kˣ) : K) • MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K))) y := by
  have hφ : ∀ u : U, φ u' (φ u y) = φ ((u' * u : U) : G) y := by
    intro u; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pU, map_sum, MonoidAlgebra.lift_single, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    Finset.smul_sum, hφ]
  refine Fintype.sum_equiv (Equiv.mulLeft u') _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, smul_smul]
  congr 1
  simp only [map_mul, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  have h1 : ((ψ u' : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp

theorem meets : ∀ {K G V : Type} [Field K] [Group G] [Fintype G] [AddCommGroup V] [Module K V] (ρ : G →* (V ≃ₗ[K] V)) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (e : MonoidAlgebra K G) (b : G → MonoidAlgebra K G), e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)) * b g → ∀ (W : Submodule K V), W ≠ ⊥ → (∀ g x, x ∈ W → ρ g x ∈ W) → (∀ x ∈ W, MonoidAlgebra.lift K (Module.End K V) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) e x = x) → W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) ≠ ⊥ := by
  intro K G V _ _ _ _ _ ρ U _ ψ e b he W hW0 hWs hWe
  set φ : G →* Module.End K V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ with hφdef
  have hφ : ∀ g x, φ g x = ρ g x := fun _ _ => rfl
  have hWs' : ∀ g x, x ∈ W → φ g x ∈ W := fun g x hx => by rw [hφ]; exact hWs g x hx
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hsum : x = ∑ g : G, φ g (MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)))
      (MonoidAlgebra.lift K (Module.End K V) G φ (b g) x)) := by
    conv_lhs => rw [← hWe x hxW, he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MonoidAlgebra.lift_single, one_smul, LinearMap.sum_apply, Module.End.mul_apply]
  intro hbot
  apply hx0
  rw [hsum]
  refine Finset.sum_eq_zero fun g _ => ?_
  have hmem : MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)))
      (MonoidAlgebra.lift K (Module.End K V) G φ (b g) x) ∈
      W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) := by
    refine ⟨lift_apply_mem φ W hWs' _ (lift_apply_mem φ W hWs' _ hxW), ?_⟩
    refine Submodule.mem_iInf _ |>.2 fun u => LinearMap.mem_ker.2 ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ← hφ, proj_eigen,
      sub_self]
  rw [hbot] at hmem
  rw [(Submodule.mem_bot K).1 hmem, map_zero]

end GlobalTheory.MeetsTypeVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableSubmoduleMeetsCharacterTypeVectorsStatement
open GlobalTheory.MeetsGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_submodule_meets_character_type_vectors : ∀ {K G V : Type} [Field K] [Group G] [Fintype G] [AddCommGroup V] [Module K V] (ρ : G →* (V ≃ₗ[K] V)) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (e : MonoidAlgebra K G) (b : G → MonoidAlgebra K G), e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)) * b g → ∀ (W : Submodule K V), W ≠ ⊥ → (∀ g x, x ∈ W → ρ g x ∈ W) → (∀ x ∈ W, MonoidAlgebra.lift K (Module.End K V) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) e x = x) → W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) ≠ ⊥ := by
  first | exact @GlobalTheory.MeetsTypeVec.meets | exact GlobalTheory.MeetsTypeVec.meets | (intros; apply GlobalTheory.MeetsTypeVec.meets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonoidAlgebraExistsRightInvOfMapField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonoidAlgebraExistsRightInvOfMapField
namespace GlobalTheory

open MonoidAlgebra

theorem groupAlgebra_coeff_mul_fintype {R G : Type} [CommRing R] [Group G] [Fintype G]
    (x y : MonoidAlgebra R G) (a : G) :
    (x * y).coeff a = ∑ c : G, x.coeff (a * c⁻¹) * y.coeff c := by
  classical
  have hs : ∀ (f : G →₀ R) (g : G → R → R), (∀ i, g i 0 = 0) → f.sum g = ∑ i, g i (f i) :=
    fun f g h => Finsupp.sum_fintype f g h
  rw [MonoidAlgebra.coeff_mul, hs _ _ (fun i => by simp)]
  rw [Finset.sum_congr rfl fun b _ => hs _ _ (fun i => by simp)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ∀ m : G, (m * c = a) ↔ (m = a * c⁻¹) := fun m => eq_mul_inv_iff_mul_eq.symm
  simp_rw [this]
  simp

theorem groupAlgebra_exists_right_inv_of_map {E L G : Type} [Field E] [Field L] [Group G]
    [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G) :
    (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) →
      ∃ v : MonoidAlgebra E G, x * v = 1 := by
  classical
  rintro ⟨vL, hvL⟩
  let M : Matrix G G E := fun a c => x.coeff (a * c⁻¹)

  have hsurj : Function.Surjective (M.map j).mulVec := by
    intro w
    let y : MonoidAlgebra L G := ofCoeff (Finsupp.equivFunOnFinite.symm w)
    refine ⟨fun c => (vL * y).coeff c, ?_⟩
    funext a
    have h1 : (MonoidAlgebra.mapRingHom G j x * (vL * y)).coeff a = w a := by
      rw [← mul_assoc, hvL, one_mul]
      rfl
    rw [groupAlgebra_coeff_mul_fintype] at h1
    simp only [MonoidAlgebra.coeff_mapRingHom] at h1
    exact h1
  have hU : IsUnit (M.map j) := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hdetL : IsUnit (j M.det) := by
    rw [RingHom.map_det]
    exact (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdet : M.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdetL
    exact not_isUnit_zero hdetL
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM
    (fun a => (1 : MonoidAlgebra E G).coeff a)
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm u), ?_⟩
  apply MonoidAlgebra.ext
  ext a
  rw [groupAlgebra_coeff_mul_fintype]
  have := congrFun hu a
  simpa [Matrix.mulVec, dotProduct, M] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonoidAlgebraExistsRightInvOfMapFieldStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monoidAlgebra_exists_right_inv_of_map_field : ∀ {E L G : Type} [Field E] [Field L] [Group G] [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G), (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) → ∃ v : MonoidAlgebra E G, x * v = 1 := by
  first | exact @GlobalTheory.groupAlgebra_exists_right_inv_of_map | exact GlobalTheory.groupAlgebra_exists_right_inv_of_map | (intros; apply GlobalTheory.groupAlgebra_exists_right_inv_of_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubfieldAdjoinRootsOfUnityEmbeddingComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubfieldAdjoinRootsOfUnityEmbeddingComplex
namespace GlobalTheory

theorem adjoin_roots_of_unity_embeds_complex {L0 K : Type} [Field L0] [Field K] (s : L0 →+* K)
    (t : L0 →+* ℂ) (Z : Set K) (hZ : ∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1) :
    ∃ (E : Subfield K) (j : E →+* ℂ), (∀ x, s x ∈ E) ∧ Z ⊆ E ∧
      ∀ x (hx : s x ∈ E), j ⟨s x, hx⟩ = t x := by
  letI : Algebra L0 K := s.toAlgebra
  letI : Algebra L0 ℂ := t.toAlgebra
  have hint : ∀ z ∈ Z, IsIntegral L0 z := by
    intro z hz
    obtain ⟨n, hn, hzn⟩ := hZ z hz
    exact ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hzn]⟩
  haveI : Algebra.IsAlgebraic L0 (IntermediateField.adjoin L0 Z) :=
    IntermediateField.isAlgebraic_adjoin hint
  let φ : IntermediateField.adjoin L0 Z →ₐ[L0] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(IntermediateField.adjoin L0 Z).toSubfield, φ.toRingHom,
    fun x => (IntermediateField.adjoin L0 Z).algebraMap_mem x,
    fun z hz => IntermediateField.subset_adjoin L0 Z hz, ?_⟩
  intro x hx
  have h : (⟨s x, hx⟩ : IntermediateField.adjoin L0 Z) = algebraMap L0 _ x := rfl
  change φ ⟨s x, hx⟩ = t x
  rw [h, φ.commutes]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubfieldAdjoinRootsOfUnityEmbeddingComplexStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subfield_adjoin_rootsOfUnity_embedding_complex : ∀ {L0 K : Type} [Field L0] [Field K] (s : L0 →+* K) (t : L0 →+* ℂ) (Z : Set K), (∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1) → ∃ (E : Subfield K) (j : E →+* ℂ), (∀ x, s x ∈ E) ∧ Z ⊆ E ∧ ∀ x (hx : s x ∈ E), j ⟨s x, hx⟩ = t x := by
  first | exact @GlobalTheory.adjoin_roots_of_unity_embeds_complex | exact GlobalTheory.adjoin_roots_of_unity_embeds_complex | (intros; apply GlobalTheory.adjoin_roots_of_unity_embeds_complex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableGoodFormsMeetGenericType
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.MeetsGen.exists_right_inv_generic_central_projector : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)]
    (U : Subgroup (G0g D.nd)) [Fintype U],
    U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r →
    ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ →
    2 ≤ D.R.r → ∃ v : MonoidAlgebra ℂ (G0g D.nd),
      GlobalTheory.MeetsGen.uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) D.ntypes.e0 * v = 1 := by
  intro D S _ U _ hU ψ hψ hr
  obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D
  exact GlobalTheory.T.exists_right_inverse_centralProjectorUnitElement U ψ D.ntypes.e0 hi (fun a => ((Subalgebra.mem_center_iff.mp hc) a).symm)
    (GlobalTheory.T.good_idempotent_irreducible_character_generic_sum_ne_zero D S U hU ψ hψ hr)


open GlobalTheory.MeetsGen in
theorem GlobalTheory.TwInputs.meetsAll_of_ties : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7), NExpTied D → GrpSide D → MeetsAll D := by
  intro hG D T S i j b W hW hst hfix
  classical
  by_cases hr : D.R.r ≤ 1
  · have hFm0 : Fm0 D.nexp i j b = ⊤ := by
      rw [eq_top_iff]
      intro x _
      simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
      intro u
      have hu1 : u = 1 := Subtype.ext (GlobalTheory.MeetsGen.uup_eq_one_of_le_one _ _ hr _ (T.U_eq ▸ u.2))
      subst hu1
      simp
    rw [hFm0, inf_top_eq]
    exact hW
  have hr : 2 ≤ D.R.r := by omega
  haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fintype (G0g D.nd) := Fintype.ofFinite _
  haveI : Fintype D.nexp.U := Fintype.ofFinite _
  obtain ⟨θ, hθ, hψ⟩ := T.psiU_gen i b
  let s : ↥D.LL0 →+* FractionRing (D.ntw.O i) :=
    (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)).comp (if b then D.ntw.emb0 i else D.ntw.emb0b i)
  let t : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp D.LL0.val.toRingHom
  let Z : Set (FractionRing (D.ntw.O i)) :=
    {z | ∃ (x : Σ k : Fin 2, D.nd.PlG k) (a : Multiplicative (ZMod (D.host.g x.1))), z = ((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i))}
  have hZ : ∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
    rintro z ⟨x, a, rfl⟩
    haveI : NeZero (D.host.g x.1) := ⟨(D.host.g_prime x.1).ne_zero⟩
    refine ⟨Fintype.card (Multiplicative (ZMod (D.host.g x.1))), Fintype.card_pos, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  obtain ⟨E, jE, hsE, hZE, hj⟩ := GlobalTheory.T.exists_subfield_adjoin_rootsOfUnity_embedding_complex s t Z hZ

  let θE : ∀ x : (Σ k : Fin 2, D.nd.PlG k), Multiplicative (ZMod (D.host.g x.1)) →* Eˣ := fun x =>
    { toFun := fun a => ⟨⟨((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hZE ⟨x, a, rfl⟩⟩,
        ⟨(((θ x a)⁻¹ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hZE ⟨x, a⁻¹, by simp⟩⟩,
        Subtype.ext (by simp), Subtype.ext (by simp)⟩
      map_one' := by ext; simp
      map_mul' := fun a a' => by ext; simp }
  have hθE : ∀ x a, (((θE x a : Eˣ) : E) : FractionRing (D.ntw.O i)) = ((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) :=
    fun _ _ => rfl
  let θ' : ∀ x : (Σ k : Fin 2, D.nd.PlG k), Multiplicative (ZMod (D.host.g x.1)) →* ℂˣ :=
    fun x => (Units.map jE.toMonoidHom).comp (θE x)
  have hθ' : 2 ≤ D.R.r → ∀ x, θ' x ≠ 1 := by
    intro h x h1
    apply hθ h x
    refine MonoidHom.ext fun a => Units.ext ?_
    have h2 := congrArg (fun φ : Multiplicative (ZMod (D.host.g x.1)) →* ℂˣ => ((φ a : ℂˣ) : ℂ)) h1
    simp only [θ', MonoidHom.comp_apply, Units.coe_map, MonoidHom.one_apply, Units.val_one] at h2
    have h3 : ((θE x a : Eˣ) : E) = 1 := jE.injective (by rw [map_one]; exact h2)
    have h4 : (((θE x a : Eˣ) : E) : FractionRing (D.ntw.O i)) = 1 := by rw [h3]; rfl
    rw [MonoidHom.one_apply, Units.val_one]
    exact (hθE x a).symm.trans h4
  let ψ' : D.nexp.U →* ℂˣ := (Formalism.L2.NX.psiStd _ _ θ').comp (Subgroup.inclusion T.U_eq.le)
  have hψ' : Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ' :=
    ⟨θ', hθ', fun u => rfl⟩
  obtain ⟨vC, hvC⟩ := GlobalTheory.MeetsGen.exists_right_inv_generic_central_projector D S D.nexp.U T.U_eq ψ' hψ' hr

  have hψE : ∀ u : D.nexp.U, ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) ∈ E := by
    intro u
    rw [hψ u]
    simp only [Formalism.L2.NX.stdVal, Units.coe_prod]
    exact E.prod_mem fun x _ => hZE ⟨x, _, rfl⟩
  let fE : D.nexp.U → E := fun u => ⟨(((D.nexp.psiU i b u)⁻¹ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)),
    by rw [Units.val_inv_eq_inv_val]; exact E.inv_mem (hψE u)⟩
  let eE : MonoidAlgebra E (G0g D.nd) :=
    MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => (⟨s (D.nexp.eLL0 g), hsE _⟩ : E))
  have hψval : ∀ u : D.nexp.U, jE ⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ =
      ((ψ' u : ℂˣ) : ℂ) := by
    intro u
    have e1 : (⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ : E) =
        ∏ x, ((θE x (Multiplicative.ofAdd (Formalism.L2.NX.supSum D.R.r
          (((u : G0g D.nd) x : GL (Fin D.R.r) (ZMod (D.host.g x.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g x.1))))) : Eˣ) : E) := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_finsetProd, hθE]
      rw [hψ u]
      simp [Formalism.L2.NX.stdVal, Units.coe_prod]
    rw [e1, map_prod]
    simp [ψ', Formalism.L2.NX.psiStd, Formalism.L2.NX.stdVal, θ', Units.coe_prod]
  have hC1 : MonoidAlgebra.mapRingHom (G0g D.nd) jE (uElt D.nexp.U fE eE) =
      uElt D.nexp.U (fun u => (((ψ' u)⁻¹ : ℂˣ) : ℂ)) D.ntypes.e0 := by
    rw [GlobalTheory.MeetsGen.map_uElt]
    congr 1
    · funext u
      have e2 : fE u = (⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ : E)⁻¹ :=
        Subtype.ext (by simp [fE])
      rw [e2, map_inv₀, hψval, Units.val_inv_eq_inv_val]
    · refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
      rw [MonoidAlgebra.coeff_mapRingHom]
      simp only [eE, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
      rw [hj, ← D.nStage_trivialCharacter_coeff_eq]
      rfl
  have hK1 : MonoidAlgebra.mapRingHom (G0g D.nd) E.subtype eE = D.nexp.eAlg i b := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    rw [MonoidAlgebra.coeff_mapRingHom, D.nexp.eAlg_def]
    simp only [eE, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
    rfl
  obtain ⟨vE, hvE⟩ := GlobalTheory.T.monoidAlgebra_exists_right_inv_of_map_field jE (uElt D.nexp.U fE eE) ⟨vC, by rw [hC1]; exact hvC⟩
  have hvK := congrArg (MonoidAlgebra.mapRingHom (G0g D.nd) E.subtype) hvE
  rw [map_mul, map_one, GlobalTheory.MeetsGen.map_uElt, hK1] at hvK
  have heq := GlobalTheory.MeetsGen.eq_sum_of_uElt_mul D.nexp.U _ (D.nexp.eAlg i b) _ (D.nexp.eAlg_idem i b) (D.nexp.eAlg_central i b) hvK
  exact GlobalTheory.T.stable_submodule_meets_character_type_vectors (D.nexp.actG i j b) D.nexp.U (D.nexp.psiU i b) (D.nexp.eAlg i b) _ heq W hW
    (fun g x hx => hst g x hx) (fun x hx => hfix x hx)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableGoodFormsMeetGenericTypeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableGoodForms_meet_generic_type : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7), NExpTied D → GrpSide D → MeetsAll D := by
  first | exact @GlobalTheory.TwInputs.meetsAll_of_ties | exact GlobalTheory.TwInputs.meetsAll_of_ties | (intros; apply GlobalTheory.TwInputs.meetsAll_of_ties <;> assumption)
end
