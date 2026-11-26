module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.Reindex

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnMinorLeft
private theorem eabH_comp_mul_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.EabH H a b (fun x => f (h * x)) = fun x => Formalism.QuantumDeterminants.EabH H a b f (h * x) := by
  funext g
  simp only [Formalism.QuantumDeterminants.EabH, Formalism.REAL.RdV, mul_assoc]

private theorem qdTop_eabH_comp_mul_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H h : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) u a b (fun x => f (h * x)) =
      fun x => Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) u a b f (h * x) := by
  funext g
  simp only [Formalism.QuantumDeterminants.Top, eabH_comp_mul_left]

private theorem foldr_apply_comp_mul_left_of_forall_mem {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : Matrix (Fin n) (Fin n) ℂ) (L : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)))
    (hL : ∀ T ∈ L, ∀ f : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f (h * x)) = fun x => T f (h * x))
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    L.foldr (fun T g => T g) (fun x => f (h * x)) = fun x => L.foldr (fun T g => T g) f (h * x) := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hL T' (by simp [hT']))]
    exact hL T (by simp) _

theorem qnMinorLeft : Formalism.FourierDecayAlt.Q.QMinorLeftH := by
  intro E _ _ n t H f a b u h
  funext x
  simp only [Formalism.QuantumDeterminants.qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hL : ∀ T ∈ List.ofFn (fun k : Fin t =>
      Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)),
      ∀ f' : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f' (h * x)) = fun x => T f' (h * x) := by
    intro T hT f'
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hT
    exact qdTop_eabH_comp_mul_left H h _ _ _ f'
  rw [foldr_apply_comp_mul_left_of_forall_mem h _ hL f]

theorem quantum_minor_left : Formalism.FourierDecayAlt.Q.QMinorLeftH := qnMinorLeft
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGConvScalar
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.AveragingOperatorIdempotent
open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem psiNat_mul_uni (ψ₀ : AddChar F ℂ) (z : GL (Fin k) F) {u : GL (Fin k) F} (hu : IsUni k u) :
    psiNat ψ₀ (z * u) = psiNat ψ₀ z * psiU ψ₀ u := by
  unfold psiNat
  by_cases hz : IsUni k z
  · rw [if_pos (isUni_mul hz hu), if_pos hz, psiU_mul ψ₀ hz hu]
  · have : ¬ IsUni k (z * u) := fun h => hz (by simpa using isUni_mul h (isUni_inv hu))
    rw [if_neg this, if_neg hz, zero_mul]

theorem sumPsi_mul_pi (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) {u : GL (Fin k) F}
    (hu : IsUni k u) :
    (∑ x : GL (Fin k) F, psiNat ψ₀ x • π x) * π u = (psiU ψ₀ u)⁻¹ • ∑ x : GL (Fin k) F, psiNat ψ₀ x • π x := by
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight u) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulRight]
  rw [smul_mul_assoc, ← map_mul, psiNat_mul_uni ψ₀ x hu, smul_smul]
  congr 1
  field_simp [psiU_ne_zero ψ₀ u]

theorem projQ_comp_pi (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) {u : GL (Fin k) F}
    (hu : IsUni k u) : projQ ψ₀ π ∘ₗ π u = (psiU ψ₀ u)⁻¹ • projQ ψ₀ π := by
  rw [← Module.End.mul_eq_comp]
  unfold projQ
  rw [smul_mul_assoc, sumPsi_mul_pi ψ₀ π hu, smul_comm]

theorem sum_boole_uni : (∑ x : GL (Fin k) F, if IsUni k x then (1 : ℂ) else 0) = (cardU F k : ℂ) := by
  rw [Finset.sum_boole]
  unfold cardU
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem averaging_operator_idempotent : QIdem := by
  intro F _ _ k ψ₀ V _ _ π
  have hterm : ∀ x : GL (Fin k) F, projQ ψ₀ π * (psiNat ψ₀ x • π x) =
      (if IsUni k x then (1 : ℂ) else 0) • projQ ψ₀ π := by
    intro x
    by_cases hx : IsUni k x
    · rw [mul_smul_comm, Module.End.mul_eq_comp, projQ_comp_pi ψ₀ π hx, smul_smul, if_pos hx]
      congr 1
      unfold psiNat; rw [if_pos hx]; field_simp [psiU_ne_zero ψ₀ x]
    · unfold psiNat; rw [if_neg hx, if_neg hx, zero_smul, zero_smul, mul_zero]
  rw [← Module.End.mul_eq_comp]
  conv_lhs => rw [show projQ ψ₀ π * projQ ψ₀ π =
    projQ ψ₀ π * (((cardU F k : ℂ))⁻¹ • ∑ x : GL (Fin k) F, psiNat ψ₀ x • π x) from rfl]
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [hterm]
  rw [← Finset.sum_smul, smul_smul, sum_boole_uni, inv_mul_cancel₀ (cardU_ne_zero F k), one_smul]

theorem idempotent_trace_formula : IdemTrace := by
  intro V _ _ _ e he
  have h : IsIdempotentElem e := he
  exact ((LinearMap.isProj_range_iff_isIdempotentElem e).2 h).trace

end PI.GGConvScalarW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.IntertwinerRankLeOne
open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pi_sgn_mul (π : Representation ℂ (GL (Fin k) F) V) (x : GL (Fin k) F) (v : V) :
    π (sgn k) (π x v) = π (sgn k * x * sgn k) (π (sgn k) v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc (sgn k * x),
    sgn_mul_self, mul_one]

theorem pi_sgn_sgn (π : Representation ℂ (GL (Fin k) F) V) (v : V) : π (sgn k) (π (sgn k) v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, sgn_mul_self, map_one, Module.End.one_apply]

theorem whit_sgn_projQ (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) (ℓ : Module.Dual ℂ V)
    (hℓ : IsWhit ψ₀ π ℓ) (v : V) : ℓ (π (sgn k) (projQ ψ₀ π v)) = ℓ (π (sgn k) v) := by
  have hterm : ∀ x : GL (Fin k) F, psiNat ψ₀ x * ℓ (π (sgn k) (π x v)) =
      (if IsUni k x then (1 : ℂ) else 0) * ℓ (π (sgn k) v) := by
    intro x
    rw [pi_sgn_mul]
    by_cases hx : IsUni k x
    · rw [hℓ _ (isUni_sgn_conj hx), ← mul_assoc, if_pos hx]
      unfold psiNat
      rw [if_pos hx, mul_comm (psiU ψ₀ x), psiU_sgn_conj]
    · unfold psiNat; rw [if_neg hx, if_neg hx, zero_mul, zero_mul]
  unfold projQ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul]
  simp_rw [hterm]
  rw [← Finset.sum_mul, sum_boole_uni, ← mul_assoc, inv_mul_cancel₀ (cardU_ne_zero F k), one_mul]

theorem isWhit_of_dual (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) (f : Module.Dual ℂ V) :
    IsWhit ψ₀ π (f ∘ₗ (projQ ψ₀ π ∘ₗ π (sgn k))) := by
  intro u hu v
  have hq := LinearMap.congr_fun (projQ_comp_pi ψ₀ π (isUni_sgn_conj hu)) (π (sgn k) v)
  simp only [LinearMap.comp_apply] at hq ⊢
  rw [pi_sgn_mul, hq, LinearMap.smul_apply, map_smul, smul_eq_mul,
    inv_eq_of_mul_eq_one_right (psiU_sgn_conj ψ₀ u)]

theorem generic_iff_criterion : GenericIff := by
  intro F _ _ k ψ₀ V _ _ π
  constructor
  · rintro ⟨ℓ, hne, hw⟩ hQ
    apply hne
    ext v
    have := whit_sgn_projQ ψ₀ π ℓ hw (π (sgn k) v)
    rw [hQ, LinearMap.zero_apply, map_zero, map_zero, pi_sgn_sgn] at this
    rw [← this, LinearMap.zero_apply]
  · intro hQ
    obtain ⟨v, hv⟩ : ∃ v, projQ ψ₀ π v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hQ (LinearMap.ext h)
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f (projQ ψ₀ π v) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
    refine ⟨f ∘ₗ (projQ ψ₀ π ∘ₗ π (sgn k)), ?_, isWhit_of_dual ψ₀ π f⟩
    intro h0
    apply hf
    have := LinearMap.congr_fun h0 (π (sgn k) v)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, pi_sgn_sgn] at this
    exact this

theorem intertwiner_rank_le_one : RankLeOne := by
  intro hm F _ _ k ψ₀ hψ V _ _ _ π hirr
  set T : V →ₗ[ℂ] V := projQ ψ₀ π ∘ₗ π (sgn k) with hTdef
  have hsurj : LinearMap.range (π (sgn k)) = ⊤ :=
    LinearMap.range_eq_top.2 fun v => ⟨π (sgn k) v, pi_sgn_sgn π v⟩
  have hrT : LinearMap.range T = LinearMap.range (projQ ψ₀ π) :=
    LinearMap.range_comp_of_range_eq_top _ hsurj
  rw [← hrT, ← LinearMap.finrank_range_dualMap_eq_finrank_range T]
  by_cases h : ∃ ℓ₁ ∈ LinearMap.range T.dualMap, ℓ₁ ≠ 0
  · obtain ⟨ℓ₁, ⟨f₁, rfl⟩, hne⟩ := h
    have hle : LinearMap.range T.dualMap ≤ Submodule.span ℂ {T.dualMap f₁} := by
      rintro _ ⟨f₂, rfl⟩
      obtain ⟨c, hc⟩ := hm F k ψ₀ hψ V π hirr _ _ (isWhit_of_dual ψ₀ π f₁) (isWhit_of_dual ψ₀ π f₂) hne
      rw [Submodule.mem_span_singleton]
      exact ⟨c, hc.symm⟩
    exact (Submodule.finrank_mono hle).trans (finrank_span_singleton hne).le
  · push_neg at h
    rw [(Submodule.eq_bot_iff _).2 h, finrank_bot]
    omega

end PI.GGConvScalarW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.ConvScalarOfLitOf
open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

theorem convScalar_of (h1 : RepGamConj) (h2 : RepGamComm) (h3 : QIdem) (h4 : GenericIff) (h5 : RankLeOne)
    (h6 : SchurC) (h7 : TraceRepGam) (h8 : IdemTrace) (h9 : DimPos) (hm : GelfandGraevMultOne) :
    ConvScalar := by
  intro F _ _ k ψ₀ hψ V _ _ _ π hπ
  have hu : IsUni k (1 : GL (Fin k) F) :=
    ⟨fun i => by simp, fun i j hij => by simp [Matrix.one_apply_ne (ne_of_gt hij)]⟩
  have hpsi1 : psiNat ψ₀ (1 : GL (Fin k) F) = 1 := by
    simp only [psiNat, if_pos hu, psiU]
    have hs : superdiag k ((1 : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = 0 := by
      unfold superdiag
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · have hij : i ≠ j := by
          intro e
          rw [e] at h
          omega
        simp [Matrix.one_apply_ne hij]
      · rfl
    rw [hs, AddChar.map_zero_eq_one]
  have hgam : gam ψ₀ (1 : GL (Fin k) F) =
      (cardU F k : ℂ)⁻¹ * (Fintype.card (GL (Fin k) F) : ℂ) := by
    unfold gam
    simp [hpsi1]
  have hG0 : (Fintype.card (GL (Fin k) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hU0 : (cardU F k : ℂ) ≠ 0 := by
    haveI : Nonempty {x : GL (Fin k) F // IsUni k x} := ⟨⟨1, hu⟩⟩
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hdim := h9 F k V π hπ
  have hd0 : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdim.ne'
  obtain ⟨c, hc⟩ := h6 F k V π hπ (repGam ψ₀ π) fun g => h2 F k ψ₀ V π g
  have htr := h7 F k ψ₀ V π
  rw [hc, h8 V (projQ ψ₀ π) (h3 F k ψ₀ V π), map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hc, hgam]
  split_ifs with hgen
  · have hne := (h4 F k ψ₀ V π).mp hgen
    have hr1 : Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) = 1 := by
      have hle := h5 hm F k ψ₀ hψ V π hπ
      have hpos : Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) ≠ 0 := fun h0 =>
        hne (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))
      omega
    rw [hr1, Nat.cast_one, mul_one] at htr
    have hcv : c = (Fintype.card (GL (Fin k) F) : ℂ) / (Module.finrank ℂ V : ℂ) := by
      rw [eq_div_iff hd0]
      exact htr
    rw [smul_smul, hcv]
    congr 1
    field_simp
  · have hz : projQ ψ₀ π = 0 := by
      by_contra h
      exact hgen ((h4 F k ψ₀ V π).mpr h)
    rw [hz, LinearMap.range_zero, finrank_bot, Nat.cast_zero, mul_zero] at htr
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp htr with h | h
      · exact h
      · exact absurd h hd0
    rw [hc0, zero_smul, smul_zero]

theorem convScalarOfLit_of (h1 : RepGamConj) (h2 : RepGamComm) (h3 : QIdem) (h4 : GenericIff)
    (h5 : RankLeOne) (h6 : SchurC) (h7 : TraceRepGam) (h8 : IdemTrace) (h9 : DimPos) :
    ConvScalarOfLit := by
  exact fun hm => convScalar_of h1 h2 h3 h4 h5 h6 h7 h8 h9 hm

end PI.GGConvScalarW
end
end

theorem convolution_scalar : Formalism.L2.SG.GGMirabolic.ConvScalarOfLit :=
  PI.GGConvScalarW.convScalarOfLit_of PI.GGConvScalarW.representation_conjugate_gamma PI.GGConvScalarW.representation_commutes_gamma
    PI.GGConvScalarW.averaging_operator_idempotent PI.GGConvScalarW.generic_iff_criterion PI.GGConvScalarW.intertwiner_rank_le_one
    PI.GGConvScalarW.schur_lemma_complex PI.GGConvScalarW.trace_representation_gamma PI.GGConvScalarW.idempotent_trace_formula
    PI.GGConvScalarW.representation_dimension_pos
end
