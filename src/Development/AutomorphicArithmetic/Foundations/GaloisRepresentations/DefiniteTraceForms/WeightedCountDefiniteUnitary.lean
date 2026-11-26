module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMoveDefiniteSimilitudePairMarked
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelBaseChangeMap
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplexCountRegularMarkedPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzTermEqDefinitePairOfLocalIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzTermEqDefinitePairOfLocalIsometry
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDefTerm

theorem pointSum_equiv {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ ≃* Γ')
    (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (ι₁' : Γ' →* G₁) (ι₂' : Γ' →* G₂) (h₁ : ∀ y, ι₁' (e y) = ι₁ y)
    (h₂ : ∀ y, ι₂' (e y) = ι₂ y) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f : G₁ → ℂ) (φ : G₂ → ℂ) :
    pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ = pointSum ι₁' ι₂' θ K₁ K₂ γ δ f φ := by
  have e₁ : ι₁ = ι₁'.comp e.toMonoidHom := MonoidHom.ext fun y => (h₁ y).symm
  have e₂ : ι₂ = ι₂'.comp e.toMonoidHom := MonoidHom.ext fun y => (h₂ y).symm
  subst e₁ e₂
  have hr : ((ι₁'.comp e.toMonoidHom).prod (ι₂'.comp e.toMonoidHom)).range = (ι₁'.prod ι₂').range := by
    ext g
    simp only [MonoidHom.mem_range, MonoidHom.prod_apply, MonoidHom.comp_apply]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨e y, hy⟩
    · rintro ⟨y, hy⟩; exact ⟨e.symm y, by simpa using hy⟩
  have hc : ∀ x : G₁ × G₂, Nat.card (stab (ι₁'.comp e.toMonoidHom) (ι₂'.comp e.toMonoidHom) K₁ K₂ x) =
      Nat.card (stab ι₁' ι₂' K₁ K₂ x) := by
    intro x
    have : stab (ι₁'.comp e.toMonoidHom) (ι₂'.comp e.toMonoidHom) K₁ K₂ x =
        (stab ι₁' ι₂' K₁ K₂ x).comap e.toMonoidHom := by
      simp only [stab, Subgroup.comap_inf, Subgroup.comap_comap]
    rw [this]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv fun a => Iff.rfl)
  unfold pointSum
  simp only [hc]
  rw [hr]

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem quot_commute (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) :
    ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * (P.γ : G.C) = (P.γ : G.C) * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) := by
  have hP := P.sim
  have hQ := Q.sim
  rw [hγ, hc] at hP
  rw [hγ]
  set γ := Q.γ
  set c := Q.c
  set b₁ := P.β
  set b₂ := Q.β
  set C := algebraMap ℚ G.C (c : ℚ)
  have hs : sh G (γ : G.C) = ((b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (C * b₂) := by
    rw [← hQ]; simp only [← mul_assoc, Units.inv_mul_cancel_left]
    rw [mul_assoc ((b₂⁻¹ : G.Cˣ) : G.C), Units.inv_mul, mul_one, Units.inv_mul, one_mul]
  have hCu : IsUnit C := c.isUnit.map (algebraMap ℚ G.C)
  have h := congrArg (· * ((b₂⁻¹ : G.Cˣ) : G.C)) hP
  rw [hs] at h
  have key : C * ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) =
      C * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) := by
    calc C * ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C))
        = ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * C := Algebra.commutes _ _
      _ = (γ : G.C) * b₁ * (((b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (C * b₂)) *
            ((b₂⁻¹ : G.Cˣ) : G.C) := by
          simp only [Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = C * b₁ * ((b₂⁻¹ : G.Cˣ) : G.C) := h
      _ = _ := by simp only [Units.val_mul, mul_assoc]
  have k2 := hCu.mul_left_cancel key
  calc ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * (γ : G.C)
      = ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * γ := by rw [k2]
    _ = _ := by simp only [mul_assoc, Units.inv_mul, mul_one]

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem commute_quot (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) (y : G.C)
    (hy : y * (P.γ : G.C) = (P.γ : G.C) * y) :
    y * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) = ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * y := by
  obtain ⟨w, hw⟩ := (GlobalTheory.LKCentAf.cent_iff_mem P _).1 (quot_commute P Q hγ hc)
  have hb : ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) ∈ Algebra.adjoin G.F ({(P.γ : G.C)} : Set G.C) := by
    rw [← hw]; exact w.2
  exact Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun z hz => by
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hy

theorem cent_eq (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) : P.cent = Q.cent := by
  ext ⟨y, s⟩
  change (y * P.γ = P.γ * y ∧ (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β) ↔
    (y * Q.γ = Q.γ * y ∧ (y : G.C) * Q.β * sh G y = algebraMap ℚ G.C s * Q.β)
  rw [← hγ]
  refine and_congr_right fun h1 => ?_
  have hy : (y : G.C) * (P.γ : G.C) = (P.γ : G.C) * y := by rw [← Units.val_mul, h1, Units.val_mul]
  have hcomm := commute_quot P Q hγ hc y hy
  set b : G.Cˣ := P.β * Q.β⁻¹
  have hβ : (P.β : G.C) = (b : G.C) * Q.β := by simp [b, mul_assoc]
  rw [hβ]
  have e1 : (y : G.C) * (b * Q.β) * sh G y = b * ((y : G.C) * Q.β * sh G y) := by
    rw [← mul_assoc (y : G.C), hcomm]; simp only [mul_assoc]
  have e2 : algebraMap ℚ G.C s * ((b : G.C) * Q.β) = b * (algebraMap ℚ G.C s * Q.β) := by
    rw [← mul_assoc, Algebra.commutes, mul_assoc]
  rw [e1, e2]
  constructor
  · intro h
    have := congrArg (((b⁻¹ : G.Cˣ) : G.C) * ·) h
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using this
  · intro h; rw [h]

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem triv_mul_inv (bP bQ : G.C) (x u : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) bQ x t)
    (hu : (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) bQ * (starT G.star (AfP p) u).unop = inC G (AfP p) bP) :
    Triv G (AfP p) bP (x * u⁻¹) t := by
  unfold Triv at *
  have hs : (starT G.star (AfP p) (((x * u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop =
      (starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop *
        (starT G.star (AfP p) (x : AfP p ⊗[ℚ] G.C)).unop := by
    rw [Units.val_mul, map_mul, MulOpposite.unop_mul]
  have h1 : (starT G.star (AfP p) (u : AfP p ⊗[ℚ] G.C)).unop *
      (starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  rw [hs, ← hu, ← hx]
  calc ((x * u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        ((u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) bQ * (starT G.star (AfP p) u).unop) *
        ((starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop *
          (starT G.star (AfP p) (x : AfP p ⊗[ℚ] G.C)).unop)
      = (x : AfP p ⊗[ℚ] G.C) * (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * u) * inC G (AfP p) bQ *
          ((starT G.star (AfP p) (u : AfP p ⊗[ℚ] G.C)).unop *
            (starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop) *
          (starT G.star (AfP p) (x : AfP p ⊗[ℚ] G.C)).unop := by
        simp only [Units.val_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h1, mul_one, mul_one]

theorem termAt_eq (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) (x u : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) Q.β x t) (hx' : Triv G (AfP p) P.β (x * u⁻¹) t)
    (hu : (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u)
    (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (δ z : Gr G r) :
    P.termAt Kf f r K φ (x * u⁻¹) t hx' δ z = Q.termAt Kf f r K φ x t hx δ z := by
  set e : P.cent ≃* Q.cent := MulEquiv.subgroupCongr (cent_eq P Q hγ hc)
  have h₁ : ∀ y, Q.toAf x t hx (e y) = P.toAf (x * u⁻¹) t hx' y := by
    intro y
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    apply Units.ext
    have hyc : ((y : G.Cˣ × ℚˣ).1 : G.C) * (P.γ : G.C) = (P.γ : G.C) * (y : G.Cˣ × ℚˣ).1 := by
      rw [← Units.val_mul, y.2.1, Units.val_mul]
    have hc1 : ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, hyc]
    have hc2 : (u : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) * u := by rw [hγ]; exact hu
    have hcomm := GlobalTheory.LKCentAf.commute_of_centralizer ℚ (AfP p) G.C _ (P.γ : G.C) _
      (GlobalTheory.LKCentAf.cent_iff_mem P) _ _ hc2 hc1
    show (x : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) =
      ((x * u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) *
        (((x * u⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)
    have hY : ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        (((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * u) = (1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C) := by
      rw [← hcomm, ← mul_assoc, Units.inv_mul, one_mul]
    calc (x : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) *
          ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)
        = (x : AfP p ⊗[ℚ] G.C) * (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
            (((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * u)) *
            ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by rw [hY]
      _ = _ := by simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, mul_assoc]
  have hself : e P.self = Q.self := Subtype.ext (by
    show ((P.γ, P.c) : G.Cˣ × ℚˣ) = (Q.γ, Q.c)
    rw [hγ, hc])
  have hs : P.toAf (x * u⁻¹) t hx' P.self = Q.toAf x t hx Q.self := by rw [← h₁, hself]
  unfold Pair.termAt DPair.termAt
  rw [hs]
  exact pointSum_equiv e _ _ _ _ h₁ (fun y => rfl) _ _ _ _ _ _ _

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

theorem term_eq_of_local_isom : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Q : DPair G), P.γ = Q.γ → P.c = Q.c → (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C)) → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → P.term Kf f r K φ = Q.term Kf f r K φ := by
  intro p _ G P Q hγ hc hu Kf f r K φ hr hf hφ
  obtain ⟨u, huγ, huβ⟩ := hu
  have hat : P.atP = Q.atP := by
    unfold Pair.atP DPair.atP
    rw [hγ, hc]
  unfold DPair.term
  split_ifs with h
  · have hQ := Q.trivAf.choose_spec.choose_spec
    have hx' := triv_mul_inv (P.β : G.C) (Q.β : G.C) _ u _ hQ huβ
    rw [GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G P Kf f r K φ hr hf hφ _ _ hx' h.choose.1 h.choose.2 (by rw [hat]; exact h.choose_spec)]
    exact termAt_eq P Q hγ hc _ u _ hQ hx' huγ Kf f r K φ _ _
  · unfold Pair.term
    rw [dite_eq_right]
    rwa [hat]

end GlobalTheory.LKDefTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzTermEqDefinitePairOfLocalIsometryStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzTerm_eq_definitePair_of_local_isometry : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Q : DPair G), P.γ = Q.γ → P.c = Q.c → (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C)) → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → P.term Kf f r K φ = Q.term Kf f r K φ := by
  first | exact @GlobalTheory.LKDefTerm.term_eq_of_local_isom | exact GlobalTheory.LKDefTerm.term_eq_of_local_isom | (intros; apply GlobalTheory.LKDefTerm.term_eq_of_local_isom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOdd
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.Move

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem aeval_conj (y : G.Cˣ) (x : G.C) (A : Polynomial G.F) :
    Polynomial.aeval ((y : G.C) * x * ((y⁻¹ : G.Cˣ) : G.C)) A =
      (y : G.C) * Polynomial.aeval x A * ((y⁻¹ : G.Cˣ) : G.C) := by
  have hp : ∀ k : ℕ, ((y : G.C) * x * ((y⁻¹ : G.Cˣ) : G.C)) ^ k =
      (y : G.C) * x ^ k * ((y⁻¹ : G.Cˣ) : G.C) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
  induction A using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add (f := _), map_add (f := _), hf, hg, mul_add, add_mul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, hp n, ← mul_assoc, ← mul_assoc,
      Algebra.commutes a (y : G.C)]
    simp only [mul_assoc]

theorem move (y : G.Cˣ) (s : ℚ) (g b b' : G.C) (A : Polynomial G.F)
    (hb : b' = algebraMap ℚ G.C s * (y * b * sh G y)) :
    Polynomial.aeval ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) A * b' =
      algebraMap ℚ G.C s * (y * (Polynomial.aeval g A * b) * sh G y) := by
  rw [aeval_conj, hb, ← mul_assoc, ← Algebra.commutes s]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem cancel {R : Type*} [Ring R] (X w : R) (b u : Rˣ) (hu : X * b = u) (h : X * b = X * w) :
    (b : R) = w := by
  have hX : X = (u : R) * ((b⁻¹ : Rˣ) : R) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  have hl : (b : R) * ((u⁻¹ : Rˣ) : R) * X = 1 := by
    rw [hX, mul_assoc, ← mul_assoc ((u⁻¹ : Rˣ) : R), Units.inv_mul, one_mul, Units.mul_inv]
  calc (b : R) = ((b : R) * ((u⁻¹ : Rˣ) : R) * X) * b := by rw [hl, one_mul]
    _ = ((b : R) * ((u⁻¹ : Rˣ) : R) * X) * w := by rw [mul_assoc _ X, h, ← mul_assoc]
    _ = w := by rw [hl, one_mul]

private theorem minpoly_monic_of_irreducible (x : G.C)
    (hi : Irreducible (minpoly G.F x)) : (minpoly G.F x).Monic := by
  have hint : IsIntegral G.F x := by
    by_contra h
    exact hi.ne_zero (minpoly.eq_zero h)
  exact minpoly.monic hint

private theorem aeval_eq_zero_of_aeval_conj_eq_zero (y : G.Cˣ) (g : G.C)
    (q : Polynomial G.F) (h : Polynomial.aeval ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) q = 0) :
    Polynomial.aeval g q = 0 := by
  rw [aeval_conj] at h
  calc Polynomial.aeval g q
      = ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * Polynomial.aeval g q * ((y⁻¹ : G.Cˣ) : G.C)) * (y : G.C) := by
        simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
    _ = 0 := by rw [h, mul_zero, zero_mul]

private theorem minpoly_conj_eq_of_irreducible (y : G.Cˣ) (g : G.C)
    (hi : Irreducible (minpoly G.F ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)))) :
    minpoly G.F ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) = minpoly G.F g :=
  minpoly.eq_of_irreducible_of_monic hi (aeval_eq_zero_of_aeval_conj_eq_zero y g _ (minpoly.aeval _ _))
    (minpoly_monic_of_irreducible _ hi)

end GlobalTheory.LKDef.Move

namespace GlobalTheory.LKDef

open GlobalTheory.LKDef.Move

theorem cls_equiv_dcls_irr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (sel : Polynomial G.F → ℂ), IsSel G sel → ∃ e : {q : Cls G // Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol)} ≃ {q : DCls G // Irreducible (Quot.out q).pol}, ∀ q, (Quot.out (e q).1).pol = (Quot.out q.1).pol ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → (Quot.out (e q).1).term Kf f r K φ = (Quot.out q.1).term Kf f r K φ := by
  intro p hp G ha hn sel hsel
  obtain ⟨v0, hv0⟩ : ∃ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 := by
    have h1 : 0 < G.a := by rw [ha]; exact Nat.one_pos
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp h1
    exact ⟨x.1, x.2⟩
  have key := fun (P0 : Polynomial G.F) (hi : Irreducible P0) (hm : P0.Monic)
      (hd : P0.natDegree = G.n) =>
    GlobalTheory.T.exists_polynomial_move_definiteSimilitudePair_marked p G ha hn P0 (sel P0) v0 hv0 hi (hsel v0 hv0 P0 hm hd)
  choose! A hA1 hA2 using key
  have hF := fun (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)) =>
    hA2 P.pol hi (minpoly_monic_of_irreducible (P.γ : G.C) hi) P.reg.1 P rfl hm
  choose FQ hFγ hFc hFβ hFu using hF
  have hB := fun (Q : DPair G) (hi : Irreducible Q.pol) =>
    hA1 Q.pol hi (minpoly_monic_of_irreducible (Q.γ : G.C) hi) Q.reg.1 Q rfl
  choose BP hBγ hBc hBβ hBm hBu using hB

  have hpolP : ∀ P P' : Pair G, P'.Rel P → Irreducible P.pol → P'.pol = P.pol := by
    intro P P' hr hi
    obtain ⟨y, s, -, -, hγ⟩ := hr
    have e : (P.γ : G.C) = (y : G.C) * P'.γ * ((y⁻¹ : G.Cˣ) : G.C) := by
      rw [hγ, Units.val_mul, Units.val_mul]
    have hi' : Irreducible (minpoly G.F ((y : G.C) * P'.γ * ((y⁻¹ : G.Cˣ) : G.C))) := by
      rw [← e]; exact hi
    show minpoly G.F (P'.γ : G.C) = minpoly G.F (P.γ : G.C)
    rw [e]
    exact (minpoly_conj_eq_of_irreducible y _ hi').symm
  have hFirr : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      Irreducible (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol := by
    intro P hi hm
    rw [DPair.pol_eq_of_rel (DPair.rel_out (FQ P hi hm))]
    show Irreducible (minpoly G.F ((FQ P hi hm).γ : G.C))
    rw [hFγ P hi hm]
    exact hi
  have hBok : ∀ (Q : DPair G) (hi : Irreducible Q.pol),
      Irreducible (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol ∧
      (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).Mark
        (sel (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol) := by
    intro Q hi
    have hr := (Pair.mk_eq_iff_rel_and_out_rel p G (BP Q hi) (BP Q hi)).2
    have hPpol : (BP Q hi).pol = Q.pol := by
      show minpoly G.F ((BP Q hi).γ : G.C) = minpoly G.F (Q.γ : G.C)
      rw [hBγ Q hi]
    have hPi : Irreducible (BP Q hi).pol := by rw [hPpol]; exact hi
    rw [hpolP _ _ hr hPi, Pair.mark_iff_of_rel p G _ _ _ hr, hPpol]
    exact ⟨hi, hBm Q hi⟩

  have hleft : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      P.Rel (BP _ (hFirr P hi hm)) := by
    intro P hi hm
    obtain ⟨y, s, hs, hβ, hγ⟩ := DPair.rel_out (FQ P hi hm)
    have hpol : (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol = P.pol := by
      rw [DPair.pol_eq_of_rel (DPair.rel_out (FQ P hi hm))]
      show minpoly G.F ((FQ P hi hm).γ : G.C) = minpoly G.F (P.γ : G.C)
      rw [hFγ P hi hm]
    refine ⟨y, s, hs, ?_, ?_⟩
    · rw [hBβ _ (hFirr P hi hm), hpol, hγ, Units.val_mul, Units.val_mul,
        GlobalTheory.LKDef.Move.move y s ((FQ P hi hm).γ : G.C) _ _ (A P.pol) hβ, hFγ P hi hm, ← hFβ P hi hm]
    · rw [hBγ _ (hFirr P hi hm), hγ, hFγ P hi hm]

  have hright : ∀ (Q : DPair G) (hi : Irreducible Q.pol),
      (FQ _ (hBok Q hi).1 (hBok Q hi).2).Rel Q := by
    intro Q hi
    have hr := (Pair.mk_eq_iff_rel_and_out_rel p G (BP Q hi) (BP Q hi)).2
    have hPpol : (BP Q hi).pol = Q.pol := by
      show minpoly G.F ((BP Q hi).γ : G.C) = minpoly G.F (Q.γ : G.C)
      rw [hBγ Q hi]
    have hPi : Irreducible (BP Q hi).pol := by rw [hPpol]; exact hi
    have hP'pol : (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol = Q.pol := by
      rw [hpolP _ _ hr hPi, hPpol]
    have hA' : A (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol = A Q.pol := by
      rw [hP'pol]
    obtain ⟨y, s, hs, hβ, hγ⟩ := id hr
    have hc : (y : G.C) * (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).γ *
        ((y⁻¹ : G.Cˣ) : G.C) = Q.γ := by
      rw [← hBγ Q hi, hγ, Units.val_mul, Units.val_mul]
    refine ⟨y, s, hs, ?_, ?_⟩
    · refine GlobalTheory.LKDef.Move.cancel (Polynomial.aeval (Q.γ : G.C) (A Q.pol)) _ Q.β (BP Q hi).β
        (hBβ Q hi).symm ?_
      rw [← hBβ Q hi, hβ, hFβ _ (hBok Q hi).1 (hBok Q hi).2,
        ← GlobalTheory.LKDef.Move.move y s _ _ _ _ rfl, hc, hA']
    · rw [hFγ _ (hBok Q hi).1 (hBok Q hi).2, ← hBγ Q hi, hγ]

  have hterm : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol = P.pol ∧
      ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r →
        (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
        (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).term Kf f r K φ =
          P.term Kf f r K φ := by
    intro P hi hm
    have h9 := GlobalTheory.T.related_pairs_orbital_term_eq p G (FQ P hi hm) _ (DPair.rel_out (FQ P hi hm))
    refine ⟨?_, fun Kf f r K φ hr hf hφ => ?_⟩
    · rw [← h9.1]
      show minpoly G.F ((FQ P hi hm).γ : G.C) = minpoly G.F (P.γ : G.C)
      rw [hFγ P hi hm]
    · rw [← h9.2.2 Kf f r K φ hr hf hφ]
      exact (GlobalTheory.T.kottwitzTerm_eq_definitePair_of_local_isometry p G P (FQ P hi hm) (hFγ P hi hm).symm (hFc P hi hm).symm (hFu P hi hm)
        Kf f r K φ hr hf hφ).symm
  refine ⟨⟨fun q => ⟨(Quot.mk (DPair.Rel (G := G)) (FQ _ q.2.1 q.2.2) : DCls G), hFirr _ q.2.1 q.2.2⟩,
    fun q => ⟨(Quot.mk (Pair.Rel (G := G)) (BP _ q.2) : Cls G), hBok _ q.2⟩, fun q => ?_, fun q => ?_⟩,
    fun q => hterm _ q.2.1 q.2.2⟩
  · apply Subtype.ext
    exact ((Pair.mk_eq_iff_rel_and_out_rel p G _ _).1.mpr (hleft _ q.2.1 q.2.2)).symm.trans
      (Quot.out_eq q.1)
  · apply Subtype.ext
    exact ((DPair.mk_eq_iff _ _).mpr (hright _ q.2)).trans (Quot.out_eq q.1)
end GlobalTheory.LKDef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOddStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (sel : Polynomial G.F → ℂ), IsSel G sel → ∃ e : {q : Cls G // Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol)} ≃ {q : DCls G // Irreducible (Quot.out q).pol}, ∀ q, (Quot.out (e q).1).pol = (Quot.out q.1).pol ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → (Quot.out (e q).1).term Kf f r K φ = (Quot.out q.1).term Kf f r K φ := by
  first | (exact @GlobalTheory.LKDef.cls_equiv_dcls_irr) | (exact GlobalTheory.LKDef.cls_equiv_dcls_irr) | (intros; apply GlobalTheory.LKDef.cls_equiv_dcls_irr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DPairOneIrr
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

def MoveDefInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel →
    ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ),
      0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
      markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ

namespace MoveEx

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example

end MoveEx

end GlobalTheory.LKDef
end
end

section -- merged from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FinitelyManyMarkedClassesTermDegreeOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights

def FinitelyManyMarkedClassesTermDegreeOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1))
    (f' : Gr G 1 → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
    {q : Cls G | (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite

end GlobalTheory.RootSumWeights
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkWeightedFixedPointDefinitePairOddOfCounts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotConjTransposeMulMul
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem dot_conjTranspose_mul_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (y z : Fin n → ℂ) :
    star y ⬝ᵥ (Mᴴ * N * M) *ᵥ z = star (M *ᵥ y) ⬝ᵥ N *ᵥ (M *ᵥ z) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem mark_unique : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ μ' : ℂ), G.a = 1 →
    P.Mark μ → P.Mark μ' → μ = μ' := by
  intro p _ G P μ μ' ha hm hm'
  obtain ⟨v, hv, x, hx, hxp⟩ := hm
  obtain ⟨v', hv', x', hx', hxp'⟩ := hm'
  have hvv : v = v' := by
    have hc : Fintype.card {w : InfinitePlace G.F // sigPosH (G.gram_herm w) = 1} = 1 := ha
    rw [Fintype.card_eq_one_iff] at hc
    obtain ⟨w, hw⟩ := hc
    exact congrArg Subtype.val ((hw ⟨v, hv⟩).trans (hw ⟨v', hv'⟩).symm)
  subst hvv
  by_contra hne
  have hn := GlobalTheory.T.mark_norm_sq_eq_similitudeFactor p G P μ ⟨v, hv, x, hx, hxp⟩
  obtain ⟨-, -, hlaw⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P v

  have e := dot_conjTranspose_mul_mul (G.psi v P.γ) (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) x x'
  rw [hlaw, hx, hx', Matrix.mulVec_smul, Matrix.smul_mulVec, star_smul, smul_dotProduct,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at e
  have hc0 : ((P.c : ℚ) : ℝ) ≠ 0 := by exact_mod_cast P.c.ne_zero
  have hμ : star μ * μ = (((P.c : ℚ) : ℂ)) := by
    rw [show star μ = (starRingEnd ℂ) μ from rfl, Complex.conj_mul', ← Complex.ofReal_pow, hn, Complex.ofReal_ratCast]
  have hμ0 : star μ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hμ
    exact hc0 (by exact_mod_cast hμ.symm)
  have horth : star x ⬝ᵥ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *ᵥ x' = 0 := by
    by_contra hne0
    have h1 : (((P.c : ℚ) : ℂ)) = star μ * μ' := by
      rw [← mul_assoc] at e; exact mul_right_cancel₀ hne0 e
    exact hne (mul_left_cancel₀ hμ0 (hμ.trans h1))

  obtain ⟨Z, hZ⟩ := GlobalTheory.T.similitudePair_gram_inv_congruent p G P v
  rw [hZ, dot_conjTranspose_mul_mul] at horth hxp hxp'
  have hx'0 : x' ≠ 0 := by
    rintro rfl; simp at hxp'
  have hY : (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x' ≠ 0 := by
    intro h0
    apply hx'0
    have := congrArg (fun w => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec] using this
  have hneg := GlobalTheory.T.hermitianForm_neg_on_orthogonal_of_positiveIndex_one (G.gram v) (G.gram_herm v) (G.gram_det v) hv _ _ hxp horth hY
  exact absurd hxp' (not_lt.mpr hneg.le)

end GlobalTheory.LKMid.Pair
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights

theorem exists_root_enum {F : Type} [Field F] (τ : F →+* ℂ) (n : ℕ) :
    ∃ sel : Fin n → Polynomial F → ℂ, ∀ P : Polynomial F, P.Monic → P.natDegree = n →
      (P.map τ).roots = Finset.univ.val.map fun i => sel i P := by
  have key : ∀ P : Polynomial F, ∃ g : Fin n → ℂ, P.Monic → P.natDegree = n →
      (P.map τ).roots = Finset.univ.val.map g := by
    intro P
    by_cases h : P.Monic ∧ P.natDegree = n
    · have hc : (P.map τ).roots.toList.length = n := by
        rw [Multiset.length_toList, ← (IsAlgClosed.splits (P.map τ)).natDegree_eq_card_roots,
          h.1.natDegree_map, h.2]
      obtain ⟨l, hl, hl'⟩ : ∃ l : List ℂ, l.length = n ∧ (P.map τ).roots = (l : Multiset ℂ) :=
        ⟨_, hc, (Multiset.coe_toList _).symm⟩
      subst hl
      exact ⟨l.get, fun _ _ => by rw [Fin.univ_val_map, List.ofFn_get, hl']⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using key
  exact ⟨fun i P => g P i, hg⟩

theorem markWeightedFixedPoint_definitePair_odd_of_counts : GlobalTheory.LKDef.MoveDefInv → GlobalTheory.RootSumWeights.CxCountRegMark → GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne → GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd := by
  intro hmove hcount hfin p _ G ha hn v hv c L f hf hreg K' f' hf' h0
  rw [hcount p G ha v hv c L f hf hreg K' f' hf']
  obtain ⟨sel, hsel⟩ := exists_root_enum v.embedding G.n
  have hmon : ∀ x : G.C, (minpoly G.F x).Monic := fun x => minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hmem : ∀ P : Polynomial G.F, P.Monic → P.natDegree = G.n → ∀ μ : ℂ,
      P.eval₂ v.embedding μ = 0 ↔ ∃ i, sel i P = μ := by
    intro P hm hd μ
    rw [← Polynomial.eval_map, ← Polynomial.IsRoot.def, ← Polynomial.mem_roots (hm.map _).ne_zero, hsel P hm hd]
    simp
  have hIs : ∀ i, IsSel G (sel i) := by
    intro i w hw P hm hd
    have hc : Fintype.card {w : InfinitePlace G.F // sigPosH (G.gram_herm w) = 1} = 1 := ha
    obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.1 hc
    have hwv : w = v := congrArg Subtype.val ((hu ⟨w, hw⟩).trans (hu ⟨v, hv⟩).symm)
    subst hwv
    exact (hmem P hm hd _).2 ⟨i, rfl⟩
  have hF := hfin p G ha L f K' f' hf hf'

  have hL : markSumC G c L.K.toSubgroup f K' f' =
      ∑ i, markedSumIrr G (fun P => c P (sel i P)) (sel i) L.K.toSubgroup f 1 K' f' := by
    unfold markSumC markedSumIrr
    rw [← finsum_sum_comm]
    · refine finsum_congr fun q => ?_
      set P : Pair G := Quot.out q
      by_cases hm : ∃ μ, P.Mark μ
      · rw [dite_eq_left hm]
        by_cases hi : Irreducible P.pol
        · have hμ := hm.choose_spec
          obtain ⟨j, hj⟩ := (hmem P.pol (hmon _) P.reg.1 _).1 (mark_isRoot_pol p G P _ ha hμ v hv)
          have hnd : (Finset.univ.val.map fun i => sel i P.pol).Nodup := by
            rw [← hsel P.pol (hmon _) P.reg.1]
            exact Polynomial.nodup_roots (P.reg.2.map)
          have hinj := Multiset.inj_on_of_nodup_map hnd
          rw [Finset.sum_eq_single j]
          · rw [if_pos ⟨hi, hj ▸ hμ⟩]
            beta_reduce
            rw [hj]
          · intro i _ hij
            rw [if_neg]
            rintro ⟨-, hi'⟩
            exact hij (hinj i (Finset.mem_univ_val i) j (Finset.mem_univ_val j)
              ((Pair.mark_unique p G P _ _ ha hi' hμ).trans hj.symm))
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [h0 P hm hi, mul_zero]
          exact (Finset.sum_eq_zero fun i _ => if_neg fun h => hi h.1).symm
      · rw [dite_eq_right hm]
        exact (Finset.sum_eq_zero fun i _ => if_neg fun h => hm ⟨_, h.2⟩).symm
    · intro i _
      refine hF.subset fun q hq => ?_
      rw [Function.mem_support] at hq
      split_ifs at hq with h
      · exact ⟨⟨_, h.2⟩, right_ne_zero_of_mul hq⟩
      · exact absurd rfl hq

  have hD : {q : DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
    obtain ⟨e, he⟩ := cls_equiv_dcls_irr p G ha hn _ (hIs ⟨0, G.n_pos⟩)
    have h1 := (hF.preimage (f := fun q : {q : Cls G // Irreducible (Quot.out q).pol ∧
      (Quot.out q).Mark (sel ⟨0, G.n_pos⟩ (Quot.out q).pol)} => q.1) Subtype.val_injective.injOn).image
      fun q => (e q).1
    refine h1.subset fun d hd => ⟨e.symm ⟨d, hd.1⟩, ⟨⟨_, (e.symm ⟨d, hd.1⟩).2.2⟩, ?_⟩, by simp⟩
    rw [← (he _).2 L.K.toSubgroup f 1 K' f' one_pos hf.2.2.1 hf'.2.2.1, Equiv.apply_symm_apply]
    exact hd.2
  rw [hL, Finset.sum_congr rfl fun i _ =>
    hmove p G ha hn _ _ (hIs i) L.K.toSubgroup f 1 K' f' one_pos hf.2.2.1 hf'.2.2.1]
  unfold dSumIrr
  rw [← finsum_sum_comm]
  · refine finsum_congr fun q => ?_
    set Q : DPair G := Quot.out q
    by_cases hi : Irreducible Q.pol
    · simp only [if_pos hi]
      rw [← Finset.sum_mul, rootSum, hsel Q.pol (hmon _) Q.reg.1, Multiset.map_map]
      rfl
    · simp only [if_neg hi, Finset.sum_const_zero]
  · intro i _
    refine hD.subset fun q hq => ?_
    rw [Function.mem_support] at hq
    split_ifs at hq with h
    · exact ⟨h, right_ne_zero_of_mul hq⟩
    · exact absurd rfl hq

end GlobalTheory.RootSumWeights
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsSumEqDefinitePairsSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumReindexEquivalentSubtypes
open scoped Classical

namespace GlobalTheory

theorem finsum_ite_eq_of_equiv {A B : Type} (PA : A → Prop) (PB : B → Prop)
    (e : {a // PA a} ≃ {b // PB b}) (g : A → ℂ) (h : B → ℂ)
    (hgh : ∀ a, h (e a).1 = g a.1) :
    (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ b, if PB b then h b else 0 := by
  have hA : (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ a : {a // PA a}, g a.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun a => (finsum_eq_if).symm
  have hB : (∑ᶠ b, if PB b then h b else 0) = ∑ᶠ b : {b // PB b}, h b.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun b => (finsum_eq_if).symm
  rw [hA, hB, ← finsum_comp_equiv e]
  exact finsum_congr fun a => (hgh a).symm

end GlobalTheory
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem marked_field_pairs_sum_eq_definite_pairs_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ := by
  intro p _ G ha hn wt sel hsel Kf f r K φ hr hf hφ
  obtain ⟨e, he⟩ := GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd p G ha hn sel hsel
  unfold markedSumIrr dSumIrr
  convert GlobalTheory.finsum_ite_eq_of_equiv _ _ e (fun a : Cls G => wt (Quot.out a).pol * (Quot.out a).term Kf f r K φ)
    (fun b : DCls G => wt (Quot.out b).pol * (Quot.out b).term Kf f r K φ) fun q => by
    obtain ⟨hpol, hterm⟩ := he q
    show wt (Quot.out (e q).1).pol * (Quot.out (e q).1).term Kf f r K φ = wt (Quot.out q.1).pol * (Quot.out q.1).term Kf f r K φ
    rw [hpol, hterm Kf f r K φ hr hf hφ]

end GlobalTheory.LKDef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitelyManyMarkedClassesTermDegreeOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem commComm_conj {S : Type} [Ring S] (u : S) (v : Sˣ)
    (h : ∀ a b : S, Commute a u → Commute b u → Commute a b) :
    ∀ a b : S, Commute a (v * u * v⁻¹) → Commute b (v * u * v⁻¹) → Commute a b := by
  intro a b ha hb
  have key : ∀ c : S, Commute c (v * u * v⁻¹) → Commute (((v⁻¹ : Sˣ) : S) * c * v) u := by
    intro c hc
    unfold Commute SemiconjBy at hc ⊢
    calc (((v⁻¹ : Sˣ) : S) * c * v) * u = ((v⁻¹ : Sˣ) : S) * (c * (v * u * ((v⁻¹ : Sˣ) : S))) * v := by
          simp [mul_assoc]
      _ = ((v⁻¹ : Sˣ) : S) * ((v * u * ((v⁻¹ : Sˣ) : S)) * c) * v := by rw [hc]
      _ = u * (((v⁻¹ : Sˣ) : S) * c * v) := by simp [mul_assoc]
  have h' := h _ _ (key a ha) (key b hb)
  unfold Commute SemiconjBy at h' ⊢
  have := congrArg (fun z => (v : S) * z * ((v⁻¹ : Sˣ) : S)) h'
  simpa [mul_assoc] using this

variable {p : ℕ} [Fact p.Prime]

theorem regAf_conj (G : HTGroup p) (g h : G.GAf) (hg : RegAf G g) : RegAf G (h⁻¹ * g * h) := by
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  have e : ((ubcMap (AfP.eval w) (h⁻¹ * g * h)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      (((ubcMap (AfP.eval w) h).1.1⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((ubcMap (AfP.eval w) g).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((((ubcMap (AfP.eval w) h).1.1⁻¹)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    simp [map_mul, map_inv]
  rw [e]
  exact commComm_conj _ _ hw

theorem commComm_tmul (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] (γ : G.C)
    (hsep : (minpoly G.F γ).Separable) (hdeg : (minpoly G.F γ).natDegree = G.n) :
    ∀ a b : K ⊗[ℚ] G.C, Commute a ((1 : K) ⊗ₜ γ) → Commute b ((1 : K) ⊗ₜ γ) → Commute a b := by
  set Z := Subalgebra.centralizer ℚ ({γ} : Set G.C) with hZdef
  have hZ : ∀ x y : Z, x * y = y * x := by
    intro x y
    apply Subtype.ext
    have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC γ hsep hdeg
    have hx : ∀ g ∈ ({γ} : Set G.C), g * (x : G.C) = x * g := (Subalgebra.mem_centralizer_iff _).1 x.2
    have hy : ∀ g ∈ ({γ} : Set G.C), g * (y : G.C) = y * g := (Subalgebra.mem_centralizer_iff _).1 y.2
    show (x : G.C) * y = y * x
    have hy' : (y : G.C) ∈ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
      rw [Subalgebra.mem_centralizer_iff]; exact hy
    rw [hc] at hy'
    have h2 := Algebra.adjoin_le_centralizer_centralizer G.F ({γ} : Set G.C) hy'
    rw [Subalgebra.mem_centralizer_iff] at h2
    have hx' : (x : G.C) ∈ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
      rw [Subalgebra.mem_centralizer_iff]; exact hx
    exact h2 x hx'
  have hcomm : ∀ a b : K ⊗[ℚ] Z, a * b = b * a := by
    intro a b
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]
    | tmul r x =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [add_mul, mul_add, hx, hy]
      | tmul s y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm r s, hZ x y]
  have hcen := Subalgebra.centralizer_coe_image_includeRight_eq_center_tensorProduct ℚ K G.C ({γ} : Set G.C)
  have mem : ∀ c : K ⊗[ℚ] G.C, Commute c ((1 : K) ⊗ₜ γ) →
      c ∈ (Algebra.TensorProduct.map (AlgHom.id ℚ K) Z.val).range := by
    intro c hc
    rw [← hcen, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hc.eq.symm
  intro a b ha hb
  obtain ⟨a', rfl⟩ := mem a ha
  obtain ⟨b', rfl⟩ := mem b hb
  unfold Commute SemiconjBy
  rw [← map_mul, ← map_mul, hcomm]

theorem regAf_pair (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (h : G.GAf) : RegAf G (h⁻¹ * P.toAf x t hx P.self * h) := by
  apply regAf_conj
  obtain ⟨w⟩ := finitePlacesAway_nonempty p
  refine ⟨w, ?_⟩
  let φ := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  have e : ((ubcMap (AfP.eval w) (P.toAf x t hx P.self)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      ((Units.map φ.toRingHom.toMonoidHom x : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((1 : w.1.adicCompletion ℚ) ⊗ₜ (P.γ : G.C)) *
        (((Units.map φ.toRingHom.toMonoidHom x)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (P.γ : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) = _
    rw [map_mul, map_mul]
    simp [φ, inC, Units.coe_map_inv]
  rw [e]
  exact commComm_conj _ _ (commComm_tmul G _ _ P.reg.2 P.reg.1)

end GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

namespace GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem finitely_many_marked_classes_degree_one_of_regular (hI : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
    Set.Finite {Q : Cls G | (∃ μ, (Quot.out Q).Mark μ) ∧ (Quot.out Q).term L.K.toSubgroup f 1 K' f' ≠ 0}) :
    GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne := by
  intro p _ G ha L f K' f' hf hf'
  let f₀ : G.GAf → ℂ := fun g => if RegAf G g then f g else 0
  have hiff : ∀ (k g : G.GAf), RegAf G (k⁻¹ * g * k) ↔ RegAf G g := by
    intro k g
    refine ⟨fun h => ?_, fun h => regAf_conj G g k h⟩
    have := regAf_conj G _ k⁻¹ h
    simpa [mul_assoc] using this
  have hf₀ : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f₀ := by
    obtain ⟨h1, h2, h3, S, hS⟩ := hf
    refine ⟨h1, h2, fun k hk g => ?_, S, fun g hg => hS g ?_⟩
    · have e := h3 k hk g
      simp only [MonoidHom.id_apply] at e ⊢
      simp only [f₀, e, hiff]
    · intro h; apply hg; simp [f₀, h]
  have hreg : ∀ g, f₀ g ≠ 0 → RegAf G g := fun g hg => by
    by_contra h; exact hg (by simp [f₀, h])
  have hterm : ∀ P : Pair G, P.term L.K.toSubgroup f 1 K' f' = P.term L.K.toSubgroup f₀ 1 K' f' := by
    intro P
    have key : ∀ x t hx δ z, P.termAt L.K.toSubgroup f 1 K' f' x t hx δ z =
        P.termAt L.K.toSubgroup f₀ 1 K' f' x t hx δ z := by
      intro x t hx δ z
      unfold Pair.termAt pointSum
      refine finsum_congr fun q => ?_
      have : f ((Quotient.out q).1⁻¹ * P.toAf x t hx P.self * (Quotient.out q).1) =
          f₀ ((Quotient.out q).1⁻¹ * P.toAf x t hx P.self * (Quotient.out q).1) := by
        simp only [f₀, if_pos (regAf_pair G P x t hx _)]
      rw [this]
    unfold Pair.term
    split_ifs <;> simp only [key]
  have hfin := hI p G ha L f₀ hf₀ hreg K' f' hf'
  simpa only [hterm] using hfin

end GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem GlobalTheory.RootSumWeights.finitely_many_marked_classes_term_degree_one : GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne := GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas.finitely_many_marked_classes_degree_one_of_regular GlobalTheory.T.finite_markedPairClasses_degreeOne_term_ne_zero
end

namespace UpperTheory.Gal.Cnt

theorem weighted_count_definite_unitary : GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd :=
  GlobalTheory.RootSumWeights.markWeightedFixedPoint_definitePair_odd_of_counts GlobalTheory.LKDef.marked_field_pairs_sum_eq_definite_pairs_sum UpperTheory.Cb.complex_count_regular_marked_points GlobalTheory.RootSumWeights.finitely_many_marked_classes_term_degree_one

theorem trace_definite_forms_identity : GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace := GlobalTheory.LKDef.trace_definite_forms_identity

end UpperTheory.Gal.Cnt
