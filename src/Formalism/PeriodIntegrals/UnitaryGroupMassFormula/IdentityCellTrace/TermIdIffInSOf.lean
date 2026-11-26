module

public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Lemmata.GeneralBFactThirdTail.Imports
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelevantCarrierNonempty.InSCarrierNonempty
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.AlgIdentity
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.ExistsSmulMem
noncomputable section

open NumberField

namespace PI.UnitaryGroupMassFormula.IdCellInSW

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_smul_mem (Λ : Submodule (𝓞 E) V) (hsp : Submodule.span E (Λ : Set V) = ⊤) (x : V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ Λ := by
  first | exact Bl.general_b_fact_third''''''.goal1 .. | (apply Bl.general_b_fact_third''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third''''''.goal1 <;> assumption)

variable [StarRing E]

theorem riesz [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (Λ : Submodule (𝓞 E) V) (hΛ : Λ.FG) (hsp : Submodule.span E (Λ : Set V) = ⊤)
    (f : Λ →ₗ[𝓞 E] E) : ∃ w : V, ∀ y (hy : y ∈ Λ), h w y = f ⟨y, hy⟩ := _root_.PI.UnitaryGroupMassFormula.BetaModX.Iota.riesz h hs hnd Λ hΛ hsp f


omit [StarRing E] in
theorem exists_retract (Λ : Submodule (𝓞 E) V) (hΛ : Λ.FG) (X : Submodule E V) :
    ∃ ρ : Λ →ₗ[𝓞 E] Λ, (∀ y, ((ρ y : Λ) : V) ∈ X) ∧ ∀ y : Λ, (y : V) ∈ X → ρ y = y := by
  classical
  let N : Submodule (𝓞 E) Λ := (X.restrictScalars (𝓞 E)).comap Λ.subtype
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ
  have htf : Module.IsTorsionFree (𝓞 E) (Λ ⧸ N) := by
    refine ⟨fun r hr q₁ q₂ hq => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    obtain ⟨y₁, rfl⟩ := N.mkQ_surjective q₁
    obtain ⟨y₂, rfl⟩ := N.mkQ_surjective q₂
    have hq' : N.mkQ (r • (y₁ - y₂)) = 0 := by
      rw [map_smul, map_sub, smul_sub, sub_eq_zero]
      exact hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hmem : ((r • (y₁ - y₂) : Λ) : V) ∈ X := hq'
    have hrE : algebraMap (𝓞 E) E r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hr0
    have e : ((y₁ - y₂ : Λ) : V) = (algebraMap (𝓞 E) E r)⁻¹ • ((r • (y₁ - y₂) : Λ) : V) := by
      rw [Submodule.coe_smul, ← algebraMap_smul E r, smul_smul, inv_mul_cancel₀ hrE, one_smul]
    show ((y₁ - y₂ : Λ) : V) ∈ X
    rw [e]
    exact X.smul_mem _ hmem
  have : Module.FinitePresentation (𝓞 E) (Λ ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) (Λ ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let ρ : Λ →ₗ[𝓞 E] Λ := LinearMap.id - s ∘ₗ N.mkQ
  refine ⟨ρ, fun y => ?_, fun y hy => ?_⟩
  · have h0 : N.mkQ (ρ y) = 0 := by
      have := congrArg (fun φ => φ (N.mkQ y)) hs
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      simp only [ρ, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.coe_comp,
        Function.comp_apply, map_sub, this, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · have h0 : N.mkQ y = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hy
    simp [ρ, h0]

end PI.UnitaryGroupMassFormula.IdCellInSW
end
end

noncomputable section

open NumberField

namespace PI.UnitaryGroupMassFormula.IdCellInSW

section Alg

variable {E : Type} [Field E] [StarRing E] {r : ℕ}

theorem alg_identity (α α' β β' : Fin r → E) (G s : Fin r → Fin r → E)
    (hs : ∀ a b, G a b + s a b + star (s b a) = 0) :
    (∑ a, α' a * star (β a)) + (∑ a, star (α a) * β' a) +
      (∑ a, ∑ b, star (α a) * (α' b * G a b)) +
      (∑ a, (-β' a + ∑ b, s a b * α' b) * star (α a)) +
      (∑ a, star (-β a + ∑ b, s a b * α b) * α' a) = 0 := by
  have key : ∀ a b, star (α a) * (α' b * G a b) + s a b * α' b * star (α a) +
      star (s b a) * star (α a) * α' b = 0 := by
    intro a b
    have := hs a b
    linear_combination (star (α a) * α' b) * this
  have h1 : (∑ a, (-β' a + ∑ b, s a b * α' b) * star (α a)) =
      -(∑ a, star (α a) * β' a) + ∑ a, ∑ b, s a b * α' b * star (α a) := by
    simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_mul]
    congr 1
    exact congrArg Neg.neg (Finset.sum_congr rfl fun a _ => mul_comm _ _)
  have h2 : (∑ a, star (-β a + ∑ b, s a b * α b) * α' a) =
      -(∑ a, α' a * star (β a)) + ∑ a, ∑ b, star (s b a) * star (α a) * α' b := by
    simp only [star_add, star_neg, star_sum, star_mul', add_mul, neg_mul, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, Finset.sum_mul]
    congr 1
    · exact congrArg Neg.neg (Finset.sum_congr rfl fun a _ => mul_comm _ _)
    · rw [Finset.sum_comm]
  rw [h1, h2]
  have h3 : (∑ a, ∑ b, star (α a) * (α' b * G a b)) + (∑ a, ∑ b, s a b * α' b * star (α a)) +
      (∑ a, ∑ b, star (s b a) * star (α a) * α' b) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun b _ => key a b
  linear_combination h3

end Alg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]

theorem one_mul_mem {a b : E} (ha : a ∈ (1 : Submodule (𝓞 E) E)) (hb : b ∈ (1 : Submodule (𝓞 E) E)) :
    a * b ∈ (1 : Submodule (𝓞 E) E) := by
  simpa using Submodule.mul_mem_mul ha hb

theorem core (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (Λ : Submodule (𝓞 E) V) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set V) = ⊤)
    (hU : Formalism.HermitianLatticesTheory.dual h Λ = Λ)
    (X : Submodule E V) (hiso : ∀ x ∈ X, ∀ y ∈ X, h x y = 0) {r : ℕ}
    (e e' : Fin r → V) (he : ∀ a, e a ∈ X) (he' : ∀ a, e' a ∈ X)
    (c c' : Fin r → V → E)
    (hc : ∀ x ∈ X, x = ∑ a, c a x • e a) (hc' : ∀ x ∈ X, x = ∑ a, c' a x • e' a)
    (hcadd : ∀ a, ∀ x ∈ X, ∀ y ∈ X, c a (x + y) = c a x + c a y)
    (hcadd' : ∀ a, ∀ x ∈ X, ∀ y ∈ X, c' a (x + y) = c' a x + c' a y)
    (hcsmul : ∀ a (t : E), ∀ x ∈ X, c a (t • x) = t * c a x)
    (hcsmul' : ∀ a (t : E), ∀ x ∈ X, c' a (t • x) = t * c' a x)
    (hδ : ∀ a b, c a (e b) = if a = b then 1 else 0) (hδ' : ∀ a b, c' a (e' b) = if a = b then 1 else 0)
    (J : Fin r → Submodule (𝓞 E) E)
    (hJ1 : ∀ a, ∀ t ∈ J a, t • e a ∈ Λ ∧ t • e' a ∈ Λ)
    (hJ2 : ∀ x ∈ Λ, x ∈ X → ∀ a, c a x ∈ J a ∧ c' a x ∈ J a)
    (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) :
    ∃ n : V ≃ₗ[E] V, n ∈ Formalism.HermitianLatticesTheory.isom h ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ ∧ (∀ a, n (e a) = e' a) ∧
      ∀ v, (∀ x ∈ X, h x v = 0) → n v - v ∈ X := by
  classical

  have hl : ∀ (t : E) x y, h (t • x) y = star t * h x y := fun t x y => by
    rw [LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]
  have hr : ∀ (t : E) x y, h x (t • y) = t * h x y := fun t x y => by
    rw [map_smul, smul_eq_mul]
  have hsy : ∀ x y, h y x = star (h x y) := fun x y => by
    rw [← hs.eq x y, starRingEnd_apply]
  have memΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, h y x ∈ (1 : Submodule (𝓞 E) E) := fun x => by
    conv_lhs => rw [← hU]
    exact Formalism.HermitianLatticesTheory.dualBasic_mem_dual h Λ x
  have intΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, h x y ∈ (1 : Submodule (𝓞 E) E) := fun x hx y hy =>
    (memΛ y).1 hy x hx

  obtain ⟨ρ, hρX, hρid⟩ := exists_retract Λ hfg X
  let φ : Fin r → V → E := fun a x => c' a x - c a x
  have hφadd : ∀ a, ∀ x ∈ X, ∀ y ∈ X, φ a (x + y) = φ a x + φ a y := fun a x hx y hy => by
    simp only [φ, hcadd a x hx y hy, hcadd' a x hx y hy]; ring
  have hφsmul : ∀ a (t : E), ∀ x ∈ X, φ a (t • x) = t * φ a x := fun a t x hx => by
    simp only [φ, hcsmul a t x hx, hcsmul' a t x hx]; ring
  let ψ : Fin r → (Λ →ₗ[𝓞 E] E) := fun a =>
    { toFun := fun y => φ a (ρ y : V)
      map_add' := fun y₁ y₂ => by
        rw [map_add (f := _), Submodule.coe_add, hφadd a _ (hρX y₁) _ (hρX y₂)]
      map_smul' := fun o y => by
        rw [map_smul, Submodule.coe_smul, ← algebraMap_smul E o, hφsmul a _ _ (hρX y),
          RingHom.id_apply, Algebra.smul_def] }
  choose w hw using fun a => riesz h hs hnd Λ hfg hsp (ψ a)
  have hwX : ∀ a, ∀ x ∈ X, h (w a) x = φ a x := by
    intro a x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem Λ hsp x
    have hdX : d • x ∈ X := by rw [← algebraMap_smul E d x]; exact X.smul_mem _ hx
    have h1 := hw a (d • x) hdx
    have h2 : ρ ⟨d • x, hdx⟩ = ⟨d • x, hdx⟩ := hρid _ hdX
    have h3 : ψ a ⟨d • x, hdx⟩ = φ a (d • x) := by
      show φ a (ρ ⟨d • x, hdx⟩ : V) = _
      rw [h2]
    rw [h3, ← algebraMap_smul E d x, hr, hφsmul a _ x hx] at h1
    exact mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd) h1
  have hwJ : ∀ a, ∀ y ∈ Λ, h (w a) y ∈ J a := by
    intro a y hy
    rw [hw a y hy]
    show φ a (ρ ⟨y, hy⟩ : V) ∈ J a
    have hm := hJ2 _ (ρ ⟨y, hy⟩).2 (hρX _) a
    exact (J a).sub_mem hm.2 hm.1

  have key : ∀ b, ∑ a, h (w a) (e' b) • e a = e b - e' b := by
    intro b
    have h1 : ∀ a, h (w a) (e' b) = (if a = b then 1 else 0) - c a (e' b) := fun a => by
      rw [hwX a _ (he' b)]
      simp only [φ, hδ' a b]
    simp only [h1, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hc _ (he' b)]

  let G : Fin r → Fin r → E := fun a b => h (w a) (w b)
  let k : Fin r → Fin r → E := fun a b => if a < b then -1 else if a = b then -(θ : E) else 0
  let s : Fin r → Fin r → E := fun a b => k a b * G a b
  have hkint : ∀ a b, k a b ∈ (1 : Submodule (𝓞 E) E) := by
    intro a b
    simp only [k]
    split_ifs
    · exact Submodule.mem_one.2 ⟨-1, by simp⟩
    · exact Submodule.mem_one.2 ⟨-θ, by simp⟩
    · exact Submodule.zero_mem _
  have hsG : ∀ a b, G a b + s a b + star (s b a) = 0 := by
    intro a b
    have hG : star (G b a) = G a b := (hsy (w b) (w a)).symm
    rcases lt_trichotomy a b with hab | rfl | hab
    · have h1 : ¬ b < a := not_lt.2 hab.le
      have h2 : b ≠ a := hab.ne'
      simp only [s, k, if_pos hab, if_neg h1, if_neg h2, zero_mul, star_zero]
      ring
    · have hGs : star (G a a) = G a a := hG
      simp only [s, k, lt_irrefl, if_false, if_true, star_mul', star_neg, hGs]
      linear_combination (-(G a a)) * hθ
    · have h1 : ¬ a < b := not_lt.2 hab.le
      have h2 : a ≠ b := hab.ne'
      simp only [s, k, if_pos hab, if_neg h1, if_neg h2, zero_mul, star_mul', star_neg, star_one, hG]
      ring

  let cc : Fin r → (V →ₗ[E] E) := fun a => -(h (w a)) + ∑ b, s a b • h (e b)
  have hcc : ∀ a v, cc a v = -h (w a) v + ∑ b, s a b * h (e b) v := fun a v => by
    simp [cc]
  let nL : V →ₗ[E] V :=
    LinearMap.id + ∑ a, (h (e a)).smulRight (w a) + ∑ a, (cc a).smulRight (e' a)
  have hn : ∀ v, nL v = v + ∑ a, h (e a) v • w a + ∑ a, cc a v • e' a := fun v => by
    simp [nL]
  have hBX : ∀ v, ∑ a, cc a v • e' a ∈ X := fun v =>
    X.sum_mem fun a _ => X.smul_mem _ (he' a)

  have K1 : ∀ v a, h (v + ∑ b, h (e b) v • w b) (e' a) = star (h (e a) v) := by
    intro v a
    have hk := congrArg (h v) (key a)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sub] at hk
    simp only [hr] at hk
    rw [map_add (f := _), LinearMap.add_apply, LinearMap.map_sum₂]
    simp only [hl]
    have e1 : h v (e' a) = h v (e a) - ∑ b, h (w b) (e' a) * h v (e b) := by rw [hk]; ring
    rw [e1, ← hsy]
    have e2 : ∑ b, star (h (e b) v) * h (w b) (e' a) = ∑ b, h (w b) (e' a) * h v (e b) :=
      Finset.sum_congr rfl fun b _ => by rw [hsy (e b) v, mul_comm]
    rw [e2]
    ring

  have hiso_n : ∀ v v', h (nL v) (nL v') = h v v' := by
    intro v v'
    rw [hn, hn]
    set P := v + ∑ b, h (e b) v • w b with hP
    set P' := v' + ∑ b, h (e b) v' • w b with hP'
    have hBB : h (∑ a, cc a v • e' a) (∑ a, cc a v' • e' a) = 0 := hiso _ (hBX v) _ (hBX v')
    have hPB : h P (∑ a, cc a v' • e' a) = ∑ a, cc a v' * star (h (e a) v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [hr, K1]
    have hBP : h (∑ a, cc a v • e' a) P' = ∑ a, star (cc a v) * h (e a) v' := by
      rw [LinearMap.map_sum₂]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hl, hsy P' (e' a), K1, star_star]
    have hPP : h P P' = h v v' + ((∑ a, h (e a) v' * star (h (w a) v)) +
        (∑ a, star (h (e a) v) * h (w a) v') +
        (∑ a, ∑ b, star (h (e a) v) * (h (e b) v' * G a b))) := by
      have e1 : ∀ a, h v (w a) = star (h (w a) v) := fun a => hsy _ _
      have hdbl : (∑ b, h (e b) v' * ∑ a, star (h (e a) v) * h (w a) (w b)) =
          ∑ a, ∑ b, star (h (e a) v) * (h (e b) v' * G a b) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by simp only [G]; ring
      rw [hP, hP']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, e1, RingHom.id_apply, mul_add]
      rw [Finset.sum_add_distrib, hdbl]
      ring
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [hBB, hPB, hBP, hPP]
    have := alg_identity (fun a => h (e a) v) (fun a => h (e a) v') (fun a => h (w a) v)
      (fun a => h (w a) v') G s hsG
    simp only [hcc]
    linear_combination this
  have hinj : Function.Injective nL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine hnd.1 v fun y => ?_
    rw [← hiso_n v y, hv, LinearMap.map_zero₂]

  have P1 : ∀ a, ∀ v ∈ Λ, h (e a) v • w a ∈ Λ := by
    intro a v hv
    rw [memΛ]
    intro y hy
    rw [hr, hsy (w a) y]
    have ht := (hJ1 a _ (hwJ a y hy)).1
    have := intΛ _ ht v hv
    rw [hl] at this
    rwa [mul_comm]
  have P1' : ∀ a, ∀ v ∈ Λ, h (e' a) v • w a ∈ Λ := by
    intro a v hv
    rw [memΛ]
    intro y hy
    rw [hr, hsy (w a) y]
    have ht := (hJ1 a _ (hwJ a y hy)).2
    have := intΛ _ ht v hv
    rw [hl] at this
    rwa [mul_comm]
  have P2 : ∀ a, ∀ v ∈ Λ, cc a v • e' a ∈ Λ := by
    intro a v hv
    rw [memΛ]
    intro y hy
    rw [hr, hcc, hsy (e' a) y]
    have t1 : h (w a) v * star (h (e' a) y) ∈ (1 : Submodule (𝓞 E) E) := by
      have := intΛ _ (P1' a y hy) v hv
      rwa [hl, mul_comm] at this
    have t2 : ∀ b, s a b * h (e b) v * star (h (e' a) y) ∈ (1 : Submodule (𝓞 E) E) := by
      intro b
      have := intΛ _ (P1' a y hy) _ (P1 b v hv)
      rw [hl, hr] at this
      have e1 : s a b * h (e b) v * star (h (e' a) y) =
          k a b * (star (h (e' a) y) * (h (e b) v * h (w a) (w b))) := by simp only [s, G]; ring
      rw [e1]
      exact one_mul_mem (hkint a b) this
    rw [add_mul, Finset.sum_mul, neg_mul]
    exact Submodule.add_mem _ (Submodule.neg_mem _ t1) (Submodule.sum_mem _ fun b _ => t2 b)
  have hint : ∀ v ∈ Λ, nL v ∈ Λ := by
    intro v hv
    rw [hn]
    exact Λ.add_mem (Λ.add_mem hv (Λ.sum_mem fun a _ => P1 a v hv)) (Λ.sum_mem fun a _ => P2 a v hv)

  let n : V ≃ₗ[E] V := LinearEquiv.ofInjectiveEndo nL hinj
  have hnapp : ∀ v, n v = nL v := fun v => rfl
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · show ∀ x y, h (n x) (n y) = h x y
    intro x y
    rw [hnapp, hnapp, hiso_n]
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact hint v hv
    · intro y hy
      refine ⟨n.symm y, ?_, by simp⟩
      rw [SetLike.mem_coe, memΛ]
      intro x hx
      have e : h x (n.symm y) = h (nL x) y := by
        rw [← hiso_n x (n.symm y), ← hnapp (n.symm y), LinearEquiv.apply_symm_apply]
      rw [e]
      exact intΛ _ (hint x hx) y hy
  · intro a
    rw [hnapp, hn]
    have h0 : ∀ b, h (e b) (e a) = 0 := fun b => hiso _ (he b) _ (he a)
    have h1 : ∀ b, cc b (e a) = (if b = a then 1 else 0) - c' b (e a) := by
      intro b
      rw [hcc, hwX b _ (he a)]
      simp only [h0, mul_zero, Finset.sum_const_zero, add_zero, φ, hδ b a]
      ring
    simp only [h0, zero_smul, Finset.sum_const_zero, add_zero, h1, sub_smul, ite_smul, one_smul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hc' _ (he a)]
    abel
  · intro v hv
    rw [hnapp, hn]
    have h0 : ∀ a, h (e a) v = 0 := fun a => hv _ (he a)
    simp only [h0, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
    exact hBX v

end PI.UnitaryGroupMassFormula.IdCellInSW
end
end

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.FourParts

namespace PI.UnitaryGroupMassFormula.IdCellInSW

section Flag

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem coef_expand (G : FlagG S r T) (x : S.V) (hx : x ∈ G.X) : x = ∑ a, G.coefX x a • G.e a := by
  have hx' : x ∈ Submodule.span E (Set.range G.e) := hx
  simp only [FlagG.coefX, dif_pos hx']
  have := G.e_indep.linearCombination_repr ⟨x, hx'⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at this
  exact this.symm

theorem coef_add (G : FlagG S r T) (a : Fin r) (x : S.V) (hx : x ∈ G.X) (y : S.V) (hy : y ∈ G.X) :
    G.coefX (x + y) a = G.coefX x a + G.coefX y a := by
  have hx' : x ∈ Submodule.span E (Set.range G.e) := hx
  have hy' : y ∈ Submodule.span E (Set.range G.e) := hy
  have hxy : x + y ∈ Submodule.span E (Set.range G.e) := Submodule.add_mem _ hx' hy'
  simp only [FlagG.coefX, dif_pos hx', dif_pos hy', dif_pos hxy]
  have e : (⟨x + y, hxy⟩ : Submodule.span E (Set.range G.e)) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
  rw [e, map_add (f := _), Finsupp.add_apply]

theorem coef_smul (G : FlagG S r T) (a : Fin r) (t : E) (x : S.V) (hx : x ∈ G.X) :
    G.coefX (t • x) a = t * G.coefX x a := by
  have hx' : x ∈ Submodule.span E (Set.range G.e) := hx
  have htx : t • x ∈ Submodule.span E (Set.range G.e) := Submodule.smul_mem _ t hx'
  simp only [FlagG.coefX, dif_pos hx', dif_pos htx]
  have e : (⟨t • x, htx⟩ : Submodule.span E (Set.range G.e)) = t • ⟨x, hx'⟩ := rfl
  rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem coef_e (G : FlagG S r T) (a b : Fin r) : G.coefX (G.e b) a = if a = b then 1 else 0 := by
  have hb : G.e b ∈ Submodule.span E (Set.range G.e) := Submodule.subset_span ⟨b, rfl⟩
  simp only [FlagG.coefX, dif_pos hb]
  rw [G.e_indep.repr_eq_single b ⟨G.e b, hb⟩ rfl, Finsupp.single_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem e_mem_X (G : FlagG S r T) (a : Fin r) : G.e a ∈ G.X := Submodule.subset_span ⟨a, rfl⟩

theorem X_iso (G : FlagG S r T) : ∀ x ∈ G.X, ∀ y ∈ G.X, S.hT x y = 0 := by
  have h1 : ∀ a, ∀ x ∈ G.X, S.hT x (G.e a) = 0 := by
    intro a x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact G.e_iso b a
    | zero => simp
    | add y w _ _ hy hw => simp [hy, hw]
    | smul t y _ hy => simp [hy]
  intro x hx y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, rfl⟩ := hz
    exact h1 b x hx
  | zero => simp
  | add y w _ _ hy hw => simp [hy, hw]
  | smul t y _ hy => simp [hy]

end Flag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TraceOne (D : D7) : Prop := ∃ θ : 𝓞 D.host.E, (θ : D.host.E) + star (θ : D.host.E) = 1

def Jd (D : D7) (a : Fin D.R.rS) : Submodule (𝓞 D.host.E) D.host.E :=
  ((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    Submodule (𝓞 D.host.E) D.host.E)

theorem XS_coef {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) (y : (VS D).V) (hy : y ∈ XS D G) :
    y ∈ G.X ∧ ∀ a, G.coefX y a ∈ Jd D a := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, t, ht, rfl⟩ := hz
    refine ⟨G.X.smul_mem _ (e_mem_X G b), fun a => ?_⟩
    rw [coef_smul G a t _ (e_mem_X G b), coef_e]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, mul_one]
      exact (FractionalIdeal.mem_coe).2 ht
    · simp only [hab, if_false, mul_zero]
      exact Submodule.zero_mem _
  | zero =>
    refine ⟨G.X.zero_mem, fun a => ?_⟩
    have := coef_smul G a 0 0 G.X.zero_mem
    rw [zero_smul, zero_mul] at this
    rw [this]
    exact Submodule.zero_mem _
  | add y w _ _ hy hw =>
    exact ⟨G.X.add_mem hy.1 hw.1, fun a => by
      rw [coef_add G a y hy.1 w hw.1]
      exact Submodule.add_mem _ (hy.2 a) (hw.2 a)⟩
  | smul o y _ hy =>
    refine ⟨by rw [← algebraMap_smul D.host.E o y]; exact G.X.smul_mem _ hy.1, fun a => ?_⟩
    rw [← algebraMap_smul D.host.E o y, coef_smul G a _ y hy.1, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o (hy.2 a)

theorem smul_e_mem_XS {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) (t : D.host.E)
    (ht : t ∈ Jd D a) : t • G.e a ∈ XS D G :=
  Submodule.subset_span ⟨a, t, (FractionalIdeal.mem_coe).1 ht, rfl⟩

theorem isIdF_of (D : D7) (hθ : TraceOne D) {u u' : D.what₂.Word}
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : IsRowLat D F0 Λ) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hP : PD D Λ (lf D F0) u' F') (hin : InSF (lf D F0) F') : IsIdF Λ (lf D F0) F' := by
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨_, ⟨hlat, hU, _, _⟩, hXS⟩ := hΛ
  obtain ⟨_, _, _, hXS'⟩ := hP

  have hle : ∀ k, F0.Xa k ≤ F'.fl.Xa k := PI.UnitaryGroupMassFormula.InSRelevantW.xa_le_of hin.1
  have hin' : ∀ a : Fin D.R.rS, F0.e a - F'.fl.e a ∈ F'.fl.Xa a.val := fun a => by
    rw [← neg_sub]
    exact Submodule.neg_mem _ (hle _ (hin.1 a))
  have hle' : ∀ k, F'.fl.Xa k ≤ F0.Xa k := PI.UnitaryGroupMassFormula.InSRelevantW.xa_le_of hin'
  have hXX : F'.fl.X = F0.X := by
    rw [← PI.UnitaryGroupMassFormula.InSRelevantW.xa_r F'.fl, ← PI.UnitaryGroupMassFormula.InSRelevantW.xa_r F0]
    exact le_antisymm (hle' _) (hle _)
  have hXΛ : ∀ y ∈ Λ, y ∈ F0.X → y ∈ XS D F0 := fun y hy hyX => by
    rw [← hXS]
    exact ⟨hy, hyX⟩
  have hXΛ' : ∀ y ∈ Λ, y ∈ F0.X → y ∈ XS D F'.fl := fun y hy hyX => by
    have hy' : y ∈ XLam Λ F' := ⟨hy, by
      show y ∈ F'.fl.X
      rw [hXX]
      exact hyX⟩
    exact hXS' ▸ hy'
  have hXSΛ : ∀ y ∈ XS D F0, y ∈ Λ := fun y hy => by
    rw [← hXS] at hy
    exact hy.1
  have hXSΛ' : ∀ y ∈ XS D F'.fl, y ∈ Λ := fun y hy => by
    have hy' : y ∈ XLam Λ F' := hXS'.symm ▸ hy
    exact hy'.1
  have he' : ∀ a, F'.fl.e a ∈ F0.X := fun a => hXX ▸ e_mem_X F'.fl a
  have hriesz (φ : (VS D).V →ₗ[D.host.E] D.host.E) : ∃ μ : (VS D).V, ∀ v, (VS D).hT μ v = φ v := by
    classical
    obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis (VS D).hT (VS D).nondeg (VS D).frame
    refine ⟨∑ j, star (φ ((VS D).frame j)) • bs j, fun v => ?_⟩
    have key : (VS D).hT (∑ j, star (φ ((VS D).frame j)) • bs j) = φ := by
      apply (VS D).frame.ext
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      have hs : ∀ j, (VS D).hT (star (φ ((VS D).frame j)) • bs j) ((VS D).frame i) =
          φ ((VS D).frame j) * (if i = j then 1 else 0) := by
        intro j
        rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
        congr 1
        rw [← (VS D).herm.eq ((VS D).frame i) (bs j), hbs]
        split_ifs <;> simp
      simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [key]
  have hspan : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
    by_contra hspan
    obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
    obtain ⟨μ, hμ⟩ := hriesz φ
    have hμ₀ : μ ≠ 0 := by
      intro h
      apply hφ₀
      ext y
      simpa [h] using (hμ y).symm
    have hline (a : D.host.E) : a • μ ∈ Λ := by
      rw [← hU]
      change a • μ ∈ Formalism.E.hdual (VS D).hT Λ
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro y hy
      have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
      simp [← (VS D).herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
    obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
      (show μ ∉ (⊥ : Submodule D.host.E (VS D).V) by simpa using hμ₀)
    let f := ψ.restrictScalars (𝓞 D.host.E)
    have hmap (x : D.host.E) : x ∈ Λ.map f := by
      refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
      change ψ ((x / ψ μ) • μ) = x
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
    obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
      (S := nonZeroDivisors (𝓞 D.host.E)) (hlat.fg.map f)
    have hinj := IsFractionRing.injective (𝓞 D.host.E) D.host.E
    have hne {a : 𝓞 D.host.E} (ha : a ≠ 0) : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 :=
      fun h => ha (hinj (h.trans (map_zero _).symm))
    have hinteger (x : D.host.E) : IsLocalization.IsInteger (𝓞 D.host.E) x := by
      have hx := hd _ (hmap ((algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ * x))
      rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
        one_mul] at hx
    apply RingOfIntegers.not_isField D.host.E
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro a ha
    obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 D.host.E) D.host.E a)⁻¹)
    refine ⟨b, hinj ?_⟩
    rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]
  obtain ⟨n, hnisom, hngmap, hne, hnperp⟩ :=
    core (VS D).hT (VS D).herm (VS D).nondeg Λ hlat.fg hspan hU F0.X (X_iso F0)
      F0.e F'.fl.e (e_mem_X F0) he'
      (fun a x => F0.coefX x a) (fun a x => F'.fl.coefX x a)
      (fun x hx => coef_expand F0 x hx) (fun x hx => coef_expand F'.fl x (hXX ▸ hx))
      (fun a x hx y hy => coef_add F0 a x hx y hy)
      (fun a x hx y hy => coef_add F'.fl a x (hXX ▸ hx) y (hXX ▸ hy))
      (fun a t x hx => coef_smul F0 a t x hx) (fun a t x hx => coef_smul F'.fl a t x (hXX ▸ hx))
      (fun a b => coef_e F0 a b) (fun a b => coef_e F'.fl a b)
      (Jd D)
      (fun a t ht => ⟨hXSΛ _ (smul_e_mem_XS F0 a t ht), hXSΛ' _ (smul_e_mem_XS F'.fl a t ht)⟩)
      (fun x hx hxX a => ⟨(XS_coef F0 x (hXΛ x hx hxX)).2 a, (XS_coef F'.fl x (hXΛ' x hx hxX)).2 a⟩)
      θ hθ
  have hperp : ∀ x ∈ orth (VS D) (Xsp (lf D F0)), n x - x ∈ Xsp (lf D F0) := by
    intro x hx
    refine hnperp x fun y hy => ?_
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx y hy
  refine ⟨n, ⟨⟨hnisom, hngmap⟩, ?_, hperp⟩, hne, ?_⟩
  · intro j x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      have hi' : i.val < j + 1 := hi
      show n (F0.e i) - F0.e i ∈ F0.Xa j
      rw [hne i]
      exact PI.UnitaryGroupMassFormula.InSRelevantW.xa_mono F0 (Nat.lt_succ_iff.1 hi') (hin.1 i)
    | zero => simp
    | add y w _ _ hy hw =>
      have e : n (y + w) - (y + w) = (n y - y) + (n w - w) := by rw [map_add (f := _)]; abel
      rw [e]
      exact Submodule.add_mem _ hy hw
    | smul t y _ hy =>
      have e : n (t • y) - t • y = t • (n y - y) := by rw [map_smul, smul_sub]
      rw [e]
      exact Submodule.smul_mem _ t hy
  · have h1 := hperp _ (z_mem_orth (lf D F0))
    have e : n (lf D F0).fl.z - F'.fl.z = (n (lf D F0).fl.z - (lf D F0).fl.z) - (F'.fl.z - (lf D F0).fl.z) := by
      abel
    rw [e]
    exact Submodule.sub_mem _ h1 hin.2

theorem termIdIffInS_of (D : D7) (hθ : TraceOne D) (u u' : D.what₂.Word) : TermIdIffInS D u u' := by
  intro F0 Λ hΛ x _ hin
  exact isIdF_of D hθ F0 Λ hΛ x.1 x.2 hin

end PI.UnitaryGroupMassFormula.IdCellInSW
