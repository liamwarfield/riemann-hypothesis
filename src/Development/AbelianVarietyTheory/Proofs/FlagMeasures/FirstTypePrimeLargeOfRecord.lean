module

public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGSmall
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TrDualLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.PsiTower
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.AddCharKernel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem first_type_prime_large_of_record (D : D7) : StandardLattice.GBig D := by
  refine ⟨0, ?_⟩
  have hc := D.ntypes.g_cond 0
  have hg := (D.host.g_prime 0).two_le
  have h3 : D.host.QS * D.host.q * D.host.d ≤ D.host.g 0 := by
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega)] at hc
    omega
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hf : D.R.f ≤ D.R.k := D.R.f_le_k
  have hm := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have h4 : D.R.f * D.R.k ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr
  have hQ : 1 ≤ D.host.QS := D.host.QS_pos
  have h5 : D.host.q ≤ D.host.QS * D.host.q * D.host.d :=
    calc D.host.q = 1 * D.host.q * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hQ) (by omega)
  rw [mul_assoc] at hq ⊢
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.SnMass.SkewVol

section Fixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem differentIdeal_eq_map_of_unramified (hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)) :
    differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hu, Ideal.top_mul]

theorem dInv_eq_inv_coe (K : Type) [Field K] [NumberField K] (j : ℕ) :
    dInv K j = ((↑(differentIdeal ℤ (𝓞 K) ^ j) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [SgGlob.dInv, FractionalIdeal.coeIdeal_pow, inv_pow]

theorem algebraMap_mem_inv_map_iff (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (y : F) :
    algebraMap F E y ∈ ((↑(I.map (algebraMap (𝓞 F) (𝓞 E))) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ ↔
      y ∈ ((↑I : FractionalIdeal (𝓞 F)⁰ F))⁻¹ := by
  have hIE : I.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hIE),
    FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI)]
  have key : ∀ a : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) =
      algebraMap F E (algebraMap (𝓞 F) F a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  constructor
  · intro h z hz
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have h1 := h (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a))
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mem_map_of_mem _ ha, rfl⟩)
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [key, ← map_mul] at hc
    have hint : IsIntegral ℤ (y * algebraMap (𝓞 F) F a) := by
      rw [← isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom) (algebraMap F E).injective]
      show IsIntegral ℤ (algebraMap F E (y * algebraMap (𝓞 F) F a))
      rw [← hc]
      exact c.2
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, hint⟩, rfl⟩
  · intro h z hz
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    let T : Ideal (𝓞 E) := Submodule.comap
      ((LinearMap.mulLeft (𝓞 E) (algebraMap F E y)) ∘ₗ Algebra.linearMap (𝓞 E) E)
      ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
    have hle : I.map (algebraMap (𝓞 F) (𝓞 E)) ≤ T := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
        (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩))
      show algebraMap F E y * algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) ∈
        (1 : FractionalIdeal (𝓞 E)⁰ E)
      rw [key, ← map_mul, ← hc]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨algebraMap (𝓞 F) (𝓞 E) c, key c⟩
    exact hle hb

theorem cm_sigma_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

theorem mem_range_of_cm_fixed {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hne := cm_sigma_ne_id h
  have hxS : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
  have hle : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) ≤ 2 := by
    rw [← Subalgebra.finrank_toSubmodule, ← h.2.2.1]
    exact Submodule.finrank_le _
  have hpos : 0 < Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) := Module.finrank_pos
  have hS : AlgHom.equalizer σ (AlgHom.id F E) = ⊥ := by
    rcases (by omega : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 1 ∨
        Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 2) with h1 | h2
    · exact Subalgebra.finrank_eq_one_iff.1 h1
    · exfalso
      apply hne
      have htop : Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [Subalgebra.finrank_toSubmodule, h2, h.2.2.1])
      ext z
      have hz : z ∈ Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) :=
        htop ▸ Submodule.mem_top
      exact hz
  rw [hS] at hxS
  exact Algebra.mem_bot.1 hxS

theorem imV_eq_zero_iff {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : imV x = 0 ↔ σ x = x := by
  constructor
  · intro hx
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    let w : InfinitePlace E := InfinitePlace.mk τ
    have him : (w.embedding x).im = 0 := congrFun hx w
    apply w.embedding.injective
    rw [h.2.2.2]
    exact Complex.conj_eq_iff_im.2 him
  · intro hx
    funext w
    show (w.embedding x).im = 0
    have := h.2.2.2 w.embedding x
    rw [hx] at this
    exact Complex.conj_eq_iff_im.1 this.symm

end Fixed

theorem mem_dInv_imV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) →
    ∀ (j : ℕ) (x : E), (x ∈ dInv E j ∧ imV x = 0) ↔ ∃ y ∈ dInv F j, algebraMap F E y = x := by
  intro F E _ _ _ _ _ σ h hu j x
  have hIne : differentIdeal ℤ (𝓞 F) ^ j ≠ ⊥ := pow_ne_zero _ differentIdeal_ne_bot
  have hE : dInv E j = ((↑((differentIdeal ℤ (𝓞 F) ^ j).map (algebraMap (𝓞 F) (𝓞 E))) :
      FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
    rw [dInv_eq_inv_coe, differentIdeal_eq_map_of_unramified hu, Ideal.map_pow]
  constructor
  · rintro ⟨hx, him⟩
    obtain ⟨y, rfl⟩ := mem_range_of_cm_fixed h ((imV_eq_zero_iff h x).1 him)
    refine ⟨y, ?_, rfl⟩
    rw [dInv_eq_inv_coe]
    rw [hE] at hx
    exact (algebraMap_mem_inv_map_iff _ hIne y).1 hx
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, (imV_eq_zero_iff h _).2 (σ.commutes y)⟩
    rw [hE]
    rw [dInv_eq_inv_coe] at hy
    exact (algebraMap_mem_inv_map_iff _ hIne y).2 hy

end GlobalTheory.SnMass.SkewVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCmStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (j : ℕ) (x : E), (x ∈ dInv E j ∧ imV x = 0) ↔ ∃ y ∈ dInv F j, algebraMap F E y = x := by
  first | exact @GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff | exact GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff | (intros; apply GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraSeriesCentralIdempotentNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraSeriesCentralIdempotentNeZero
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem ip_symm_of_inv {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ip α β = ip β α := by
  unfold ip
  congr 1
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun x => ?_
  simp [mul_comm]

theorem exists_cusp_list (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hG : Green) :
    ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 →
      ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2) ∧ degL (Q.map Prod.snd) = n ∧
        f = (Q.map Prod.fst).prod := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hn h0
    by_cases hu : IsUnit f
    · have h1 : f = 1 := hf.isUnit_iff.mp hu
      refine ⟨[], by simp, ?_, by simpa using h1⟩
      rw [← hn, h1]; simp [degL]
    · obtain ⟨P, hPm, hPi, q, hq⟩ := Polynomial.exists_monic_irreducible_factor f hu
      have hqm : q.Monic := hPm.of_mul_monic_left (hq ▸ hf)
      have hdeg : n = P.natDegree + q.natDegree := by
        rw [← hn, hq, hPm.natDegree_mul hqm]
      have hpos : 0 < P.natDegree := hPi.natDegree_pos
      have hc : P.coeff 0 * q.coeff 0 ≠ 0 := by
        rwa [hq, Polynomial.mul_coeff_zero] at h0
      obtain ⟨Q, hQ1, hQ2, hQ3⟩ := ih q.natDegree (by omega) q hqm rfl (right_ne_zero_of_mul hc)
      obtain ⟨τ, hτ, -⟩ := hG g L P.natDegree hpos
      have hP : IsPrimeLab P.natDegree P := ⟨hPm, hPi, left_ne_zero_of_mul hc, rfl⟩
      refine ⟨(P, ⟨P.natDegree, τ P⟩) :: Q, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact (hτ P hP).1
        · exact hQ1 p hp
      · rw [hdeg, ← hQ2]; simp [degL]
      · rw [List.map_cons, List.prod_cons, ← hQ3]; exact hq

theorem exists_irr_hasLabel (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hG : Green) (n : ℕ) (f : (ZMod g)[X])
    (hf : f.Monic) (hn : f.natDegree = n) (h0 : f.coeff 0 ≠ 0) :
    ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ HasLabel L ρ f := by
  obtain ⟨Q, hQ1, hQ2, hQ3⟩ := exists_cusp_list g L hG n f hf hn h0
  have hirr : ∀ p ∈ Q.map Prod.snd, IsIrr p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (hQ1 q hq).2.1.2.1
  have hch : IsChar (hcL (Q.map Prod.snd) n) :=
    (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g _ (Q.map Prod.snd) n hQ2.symm fun p hp => by
      obtain ⟨V, -, hV⟩ := hirr p hp
      exact ⟨V, hV⟩).1
  have hne : hcL (Q.map Prod.snd) n 1 ≠ 0 := by
    intro h
    have hd := GlobalTheory.T.harishChandraProductList_degree g (Q.map Prod.snd) n hQ2.symm
    rw [h, zero_mul] at hd
    refine mul_ne_zero ?_ ?_ hd.symm
    · refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
      have hi1 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
      have h1 : 1 < g ^ i := Nat.one_lt_pow hi1 (Fact.out : g.Prime).one_lt
      rw [sub_ne_zero]
      exact_mod_cast h1.ne'
    · refine List.prod_ne_zero fun hz => ?_
      obtain ⟨p, hp, hp0⟩ := List.mem_map.mp hz
      obtain ⟨d, hd0, hd1⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g p.1) 1 p.2).2.1 (hirr p hp)
      rw [hp0] at hd1
      have : d = 0 := by exact_mod_cast hd1.symm
      omega
  have hdec := GlobalTheory.T.character_decomposition_and_classFunction_expansion (Gn g n) (hcL (Q.map Prod.snd) n)
  have hsum := hdec.2.1 (hdec.2.2.1 hch)
  by_contra hcon
  push Not at hcon
  apply hne
  rw [hsum, finsum_mem_of_eqOn_zero]
  · rfl
  · intro ρ hρ
    have : ip (hcL (Q.map Prod.snd) n) ρ = 0 := by
      by_contra hip
      exact hcon ρ hρ ⟨Q, hQ1, hQ2, hQ3, by rwa [ip_symm_of_inv]⟩
    simp [this]

theorem zOf_ne_zero_of_isIrr {G : Type} [Group G] [Fintype G] {ρ : G → ℂ} (hρ : IsIrr ρ) : zOf ρ ≠ 0 := by
  intro h
  obtain ⟨-, h1, h2⟩ := GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree G 1 ρ
  obtain ⟨d, hd0, hd1⟩ := h1 hρ
  have htr : tr (1 : MonoidAlgebra ℂ G) ρ = ρ 1 := by
    unfold tr
    rw [Finset.sum_eq_single 1]
    · simp [MonoidAlgebra.one_def]
    · intro b _ hb
      simp [MonoidAlgebra.one_def, Finsupp.single_apply, hb, hb.symm]
    · simp
  have hd : ρ 1 ≠ 0 := by rw [hd1]; exact_mod_cast hd0.ne'
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h, mul_zero, htr] at h2
  exact mul_ne_zero (div_ne_zero hd hc) hd (h2.symm.trans (by simp))

theorem eSerC_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), Green → ∀ (n : ℕ) (f : (ZMod g)[X]),
    f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → eSerC L n f ≠ 0 := by
  intro g _ L hG n f hf hn h0 he
  obtain ⟨ρ, hρ, hl⟩ := exists_irr_hasLabel g L hG n f hf hn h0
  have hfin : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite :=
    (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)).1.subset fun χ hχ => hχ.1
  apply zOf_ne_zero_of_isIrr hρ
  have h : zOf ρ * eSerC L n f = zOf ρ := by
    unfold eSerC
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, Finset.sum_eq_single ρ]
    · rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ ρ hρ hρ).1, if_pos rfl]
    · intro b hb hne
      rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ b hρ (hfin.mem_toFinset.mp hb).1).1, if_neg hne.symm]
    · intro hb
      exact absurd (hfin.mem_toFinset.mpr ⟨hρ, hl⟩) hb
  rw [← h, he, mul_zero]

end GlobalTheory.GLm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraSeriesCentralIdempotentNeZeroStatement
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesCentralIdempotent_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), Green → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → eSerC L n f ≠ 0 := by
  exact @GlobalTheory.GLm.eSerC_ne_zero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanDifferentEqLocalGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanDifferentEqLocalGenerator
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

namespace GlobalTheory.LocDiffGen

variable {D : D7}

theorem iF_int (p : PlF D) (a : 𝓞 D.host.F) :
    (D.s.atP p).ιF (a : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := by
  have h1 : (D.s.atP p).ιF (a : D.host.F) ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [(D.s.atP p).val, map_one]
    exact p.valuation_le_one (K := D.host.F) a
  rw [map_one, Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp), map_one] at h1
  exact (Valuation.mem_integer_iff _ _).2 h1

theorem dual_sub (Z : LocDat D) (p : PlF D) (z : (D.s.atP p).Fp)
    (hz : haveI := (D.s.atP p).ellPrime; ∀ c ∈ 𝒪[(D.s.atP p).Fp],
      ‖Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp (c * z)‖ ≤ 1) :
    Z.δ p * z ∈ 𝒪[(D.s.atP p).Fp] := by
  haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  obtain ⟨-, hδ, -, hO, hpsi, -⟩ := Z.agree p
  have hx : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * z) ∈ (Z.M p).L.O := by
    rw [← (Z.M p).L.additive_character_dual_ring]
    intro y hy
    rw [hO] at hy
    rw [hpsi]
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * z) * y *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ = y * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z := by
      have e2 : Z.δ p * z * (Z.δ p)⁻¹ = z := by field_simp
      rw [← e2, map_mul (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) (Z.δ p * z) (Z.δ p)⁻¹, e2]
      ring
    rw [e]
    refine (PI.LocDualGen.Top.psi_tower PI.LocDualGen.Psi.addCharKernel (D.s.atP p) _).2 ?_
    rw [map_neg, PI.LocDualGen.Top.tr_smul, map_neg, norm_neg]
    exact hz _ (PI.UnitaryGroupMassFormula.CntFormula.DeltaC.trace_mem (D.s.atP p) hy)
  rw [hO, (D.s.atP p).O_def] at hx
  have hi : IsIntegral 𝒪[(D.s.atP p).Fp] (Z.δ p * z) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective).1 hx
  exact PI.UnitaryGroupMassFormula.CntFormula.DeltaC.mem_of_isIntegral_fp (D.s.atP p) hi

theorem diff_sub (Z : LocDat D) (p : PlF D) (x : 𝓞 D.host.F) (hx : x ∈ differentIdeal ℤ (𝓞 D.host.F)) :
    (Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := by
  obtain ⟨t, ht, hne, -, hinv⟩ := PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice
    (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective)
    PI.CntNotIntW.small_powers_bound D Z.δ Z.M Z.agree p
  have hB := PI.CntNotIntW.dual_mul_different_integral D t ht x hx
  let w : 𝓞 D.host.F := ⟨_, (mem_integralClosure_iff ℤ D.host.F).2 hB⟩
  have hw : (D.s.atP p).ιF (w : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := iF_int p w
  have hw' : (D.s.atP p).ιF (w : D.host.F) = (D.s.atP p).ιF t * (D.s.atP p).ιF (x : D.host.F) := by
    rw [← map_mul]; rfl
  have ht0 : (D.s.atP p).ιF t ≠ 0 := right_ne_zero_of_mul hne
  have hδ0 : Z.δ p ≠ 0 := left_ne_zero_of_mul hne
  have e : (Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F) =
      (D.s.atP p).ιF (w : D.host.F) * (Z.δ p * (D.s.atP p).ιF t)⁻¹ := by
    rw [hw']; field_simp
  rw [e]
  exact mul_mem hw hinv

theorem dual_glob (Z : LocDat D) (p : PlF D) (t : D.host.F)
    (ht : ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) :
    Z.δ p * (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp] := by
  haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  haveI := (D.s.atP p).lf
  exact dual_sub Z p _ (fun c hc => trace_dual_local D.host.F p (D.s.atP p).Fp (D.s.atP p).qlCont
    (D.s.atP p).qlFin (D.s.atP p).ιF (D.s.atP p).dense (D.s.atP p).val t ht c hc)

theorem span_different_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D), Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) = Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)} := by
  intro D Z p
  obtain ⟨-, hδ, -, hO, -, -⟩ := Z.agree p
  have hmem : ∀ c ∈ 𝒪[(D.s.atP p).Fp], algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (Z.M p).L.O := by
    intro c hc; rw [hO]; exact PI.CntNotIntW.algMap_mem_O D p c hc
  have hf : ∀ x : 𝓞 D.host.F, (D.s.atP p).ιE (algebraMap D.host.F D.host.E x) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (x : D.host.F)) :=
    fun x => (D.s.atP p).compat _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨_, hmem _ (diff_sub Z p x hx)⟩, ?_⟩
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F)) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) = _
    rw [← map_mul]
    show _ = (D.s.atP p).ιE (algebraMap D.host.F D.host.E (x : D.host.F))
    rw [hf]
    congr 1
    field_simp
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set N := Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) with hN
    have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0 := one_ne_zero
    have hIJ : ((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) = 1 := by
      rw [coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := D.host.F) (B := 𝓞 D.host.F)]
      exact inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10)
    have key : ∀ y : D.host.F, y ∈ (((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)) →
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF y) ∈ N := by
      intro y hy
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro m hm n hn
        obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
        have hn' := (FractionalIdeal.mem_dual h10).1 hn
        have ht : ∀ a : 𝓞 D.host.F, ∃ k : ℤ, Algebra.trace ℚ D.host.F (n * a) = k := by
          intro a
          obtain ⟨k, hk⟩ := hn' _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
          exact ⟨k, by rw [← Algebra.traceForm_apply, ← hk]; simp⟩
        have hc := dual_glob Z p n ht
        have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F x * n)) =
            (⟨_, hmem _ hc⟩ : (Z.M p).L.O) • (D.s.atP p).ιE (algebraMap D.host.F D.host.E (x : D.host.F)) := by
          rw [hf, Subring.smul_def]
          show _ = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF n) * _
          rw [← map_mul, map_mul (D.s.atP p).ιF]
          congr 1
          show _ = _ * (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F x)
          ring
        rw [e]
        exact N.smul_mem _ (Submodule.subset_span ⟨x, hx, rfl⟩)
      · intro a b ha hb
        rw [map_add (f := _), mul_add, map_add (f := _)]
        exact N.add_mem ha hb
    have h1 := key 1 (by rw [hIJ]; exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)
    have e1 : Z.δ p * (D.s.atP p).ιF 1 = Z.δ p := by rw [map_one, mul_one]
    rw [e1] at h1
    exact h1

end GlobalTheory.LocDiffGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanDifferentEqLocalGeneratorStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_different_eq_localGenerator : ∀ (D : D7) (Z : LocDat D) (p : PlF D), Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) = Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)} := by
  first | exact @GlobalTheory.LocDiffGen.span_different_eq | exact GlobalTheory.LocDiffGen.span_different_eq | (intros; apply GlobalTheory.LocDiffGen.span_different_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassLowTypesFirst
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowTypeMass

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}

open scoped Classical in
theorem lintegral_rmul_of_measurable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hS : SideG k r z π u μW μN μG νq) (F : Mx k r → ℝ≥0∞)
    (hF : Measurable ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}.piecewise
      (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)))
    (hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x)
    {g : Mx k r} (hg : g ∈ GG k r) :
    ∫⁻ x, F (Matrix.of x * g) ∂νq = ∫⁻ x, F (Matrix.of x) ∂νq := by
  classical
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ hF (fun s hs x hx => by
    rw [hval x hx]
    exact (hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx)) g hg
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => hval x hx)))
  exact (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm

theorem norm_sq_sqrt_scaled {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {t d : ℝ} (ht : 0 ≤ t)
    (hd : 0 ≤ d) (v : Wp) : ‖((Real.sqrt t * Real.sqrt d : ℝ) : ℂ) • v‖ ^ 2 = t * (d * ‖v‖ ^ 2) := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hd]
  ring

open scoped Classical in
theorem measurable_piecewise_mass {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (φ : (Fin (r + 1) → ℝ) → ℝ) (hφm : Measurable φ) (d : ℝ) (B : Mx k r → Wp) (hB : ContinuousOn B (GG k r)) :
    Measurable ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}.piecewise
      (fun x : Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
        ENNReal.ofReal (d * ‖B (Matrix.of x)‖ ^ 2)) (fun _ => 0)) := by
  classical
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hL : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) A :=
    continuousOn_pi.2 fun a => GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a
  have hLm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a)
      (fun _ => (0 : Fin (r + 1) → ℝ))) :=
    hL.measurable_piecewise continuousOn_const hAm
  have hBc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) A :=
    continuousOn_const.mul (hB.norm.pow 2)
  have hBm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) (fun _ => (0 : ℝ))) :=
    hBc.measurable_piecewise continuousOn_const hAm
  have heq : A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
        ENNReal.ofReal (d * ‖B (Matrix.of x)‖ ^ 2)) (fun _ => 0) =
      A.indicator (fun x => ENNReal.ofReal (φ (A.piecewise
        (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) (fun _ => (0 : Fin (r + 1) → ℝ)) x)) *
        ENNReal.ofReal (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) (fun _ => (0 : ℝ)) x)) := by
    funext x
    by_cases hx : x ∈ A
    · simp [Set.piecewise, Set.indicator, hx]
    · simp [Set.piecewise, Set.indicator, hx]
  rw [heq]
  exact ((ENNReal.measurable_ofReal.comp (hφm.comp hLm)).mul (ENNReal.measurable_ofReal.comp hBm)).indicator hAm

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

end main

end GlobalTheory.LowTypeMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftAntidiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftAntidiagonal
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem exists_lift_antidiag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → ℝ), l ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inr a))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inr a))) → degB r β ≤ degB r (.inr (.inr (.inr a))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV a l hl
  obtain ⟨c, hc, hσ, hlw⟩ := hl
  have hσ' : σ c = -c := hσ
  refine ⟨rowE (σ : E →+* E) J (fun i => P i a.castSucc) 0 c, ?_, ?_⟩
  · refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV a 0 c ?_ ?_ ?_ hc
    · intro b _
      simp [form]
    · simp [form, hσ']
    · intro b _
      simp
  have hE : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) 0 c) w i j =
      (if i = j then 1 else 0) +
        (if j = esI k r a then (if i = eI k r a then (s a : ℂ) * ((s a : ℂ) * w.embedding c) else 0) else 0) := by
    intro w i j
    have h0 : (A w *ᵥ fun l => w.embedding ((0 : Fin (2 * r + k + 1) → E) l)) = 0 := by
      have h1 : (fun l => w.embedding ((0 : Fin (2 * r + k + 1) → E) l)) = 0 := by
        funext l
        simp
      rw [h1, mulVec_zero]
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV a 0 c w i j, h0]
    simp [herm]
  have hne : ∀ b b' : Fin r, eI k r b ≠ esI k r b' := by
    intro b b' h
    have := congrArg Fin.val h
    simp only [eI, esI] at this
    omega
  have hnw : ∀ (j : Fin (k + 1)) (b : Fin r), wI k r j ≠ esI k r b := by
    intro j b h
    have := congrArg Fin.val h
    simp only [wI, esI] at this
    omega
  have hnw' : ∀ (j : Fin (k + 1)) (b : Fin r), eI k r b ≠ wI k r j := by
    intro j b h
    have := congrArg Fin.val h
    simp only [wI, eI] at this
    omega
  have hee : ∀ b b' : Fin r, b ≠ b' → eI k r b ≠ eI k r b' := by
    intro b b' hb h
    apply hb
    have := congrArg Fin.val h
    simp only [eI] at this
    exact Fin.ext this
  have hss : ∀ b b' : Fin r, esI k r b = esI k r b' → b = b' := by
    intro b b' h
    have := congrArg Fin.val h
    simp only [esI] at this
    exact Fin.ext (by omega)
  constructor
  · intro w
    show ((gM A _ w) (eI k r a) (esI k r a)).im = l w
    rw [hE, hlw w]
    simp [hne a a, pow_two, mul_assoc, Complex.mul_im]
  · rintro (p | b | p | b) hβ _ w
    · show (gM A _ w) (eI k r p.1.1) (eI k r p.1.2) = 0
      rw [hE]
      have h1 : eI k r p.1.1 ≠ eI k r p.1.2 := hee _ _ (ne_of_lt p.2)
      simp [h1, (hne p.1.2 a)]
    · funext j
      show (gM A _ w) (eI k r b) (wI k r j) = 0
      rw [hE]
      simp [hnw' j b, hnw j a]
    · show (gM A _ w) (eI k r p.1.1) (esI k r p.1.2) = 0
      rw [hE]
      have h1 : p.1.1 ≠ p.1.2 := ne_of_lt p.2
      by_cases h2 : p.1.2 = a
      · have h3 : eI k r p.1.1 ≠ eI k r a := hee _ _ (h2 ▸ h1)
        simp [hne p.1.1 p.1.2, h3]
      · have h3 : esI k r p.1.2 ≠ esI k r a := fun h => h2 (hss _ _ h)
        simp [hne p.1.1 p.1.2, h3]
    · show ((gM A _ w) (eI k r b) (esI k r b)).im = 0
      rw [hE]
      have hb : b ≠ a := fun h => hβ (by rw [h])
      have h3 : esI k r b ≠ esI k r a := fun h => hb (hss _ _ h)
      simp [hne b b, h3]

end GlobalTheory.SnMass.VolN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftAntidiagonalStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_antidiagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → ℝ), l ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inr a))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inr a))) → degB r β ≤ degB r (.inr (.inr (.inr a))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.exists_lift_antidiag | exact GlobalTheory.SnMass.VolN.exists_lift_antidiag | (intros; apply GlobalTheory.SnMass.VolN.exists_lift_antidiag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LastMajorantLengthSqGeAndPos
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LastMajorantLengthSqGeAndPos
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.LastLen

private lemma herm_splitForm_inv_mulVec_eq_of_mem {k r : ℕ} {g : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r}
    (hg : g ∈ _root_.BranchingSupport.GG k r) (w : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ w) (g⁻¹ *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w w := by
  have hgH : gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r := hg
  have hdet : IsUnit g.det := _root_.GlobalTheory.TensLen.isUnit_det_of_unitary (_root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq k r) hgH
  have h := _root_.Formalism.FourierDecayAlt.P.SettingConstruction.form_of_unitary (_root_.Formalism.QuantumDeterminants.Hpk k r) hgH (g⁻¹ *ᵥ w) (g⁻¹ *ᵥ w)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  exact h.symm

private lemma splitForm_mulVec_apply_eq_sgn_mul_sig (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) :
    (_root_.Formalism.QuantumDeterminants.Hpk k r *ᵥ u) i = _root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) := by
  simp only [Matrix.mulVec, dotProduct, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

private lemma herm_splitForm_eq_sum_star_mul_sgn_mul_sig (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) u u = ∑ i, star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)) := by
  unfold _root_.Formalism.QuantumDeterminants.herm
  simp only [dotProduct, Pi.star_apply, splitForm_mulVec_apply_eq_sgn_mul_sig]

private lemma herm_splitForm_sub_eq_of_isotropic {k r : ℕ} (z y : Fin (2 * r + k + 1) → ℂ)
    (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hy : ∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (z - y) (z - y) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) z z := by
  have hz' : ∀ i : Fin (2 * r + k + 1), (i : ℕ) < r ∨ r + k < (i : ℕ) → z i = 0 := hz
  rw [herm_splitForm_eq_sum_star_mul_sgn_mul_sig, herm_splitForm_eq_sum_star_mul_sgn_mul_sig]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  by_cases h1 : (i : ℕ) < r
  · have hσ := _root_.Formalism.QuantumDeterminants.GBasic.sig_lo k r i h1
    rw [hz' i (Or.inl h1), hz' (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) (Or.inr (by omega)),
      hy (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) (by omega)]
    simp
  · by_cases h2 : r + k < (i : ℕ)
    · rw [hz' i (Or.inr h2), hy i (by omega)]
      simp
    · rw [_root_.Formalism.QuantumDeterminants.GBasic.sig_mid k r i (by omega) (by omega), hy i (by omega), sub_zero]

private lemma neg_re_herm_splitForm_le_sum_normSq (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) :
    -(_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) u u).re ≤ ∑ i, Complex.normSq (u i) := by
  have hs : ∀ i, ‖_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i‖ = 1 := by
    intro i
    unfold _root_.Formalism.QuantumDeterminants.GBasic.sgn
    split_ifs <;> simp
  have hperm : ∑ i, Complex.normSq (u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)) = ∑ i, Complex.normSq (u i) :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (_root_.Formalism.QuantumDeterminants.GBasic.sig_sig k r)) (fun i => Complex.normSq (u i))
  rw [herm_splitForm_eq_sum_star_mul_sgn_mul_sig, Complex.re_sum, ← Finset.sum_neg_distrib]
  calc ∑ i, -(star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))).re
      ≤ ∑ i, (Complex.normSq (u i) + Complex.normSq (u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))) / 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := Complex.abs_re_le_norm (star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)))
        rw [norm_mul, norm_mul, norm_star, hs, one_mul] at h1
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
        nlinarith [neg_le_abs (star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))).re,
          sq_nonneg (‖u i‖ - ‖u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)‖)]
    _ = ∑ i, Complex.normSq (u i) := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hperm]
        ring

theorem _root_.GlobalTheory.LastLen.last_len : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), _root_.Formalism.QuantumDeterminants.inWb k r z → 0 < _root_.Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ _root_.BranchingSupport.GG k r, _root_.Formalism.QuantumDeterminants.Tz k r z ≤ _root_.BranchingSupport.lenA k r z g (Fin.last r) ^ 2 ∧ ∀ a, 0 < _root_.BranchingSupport.lenA k r z g a ∧ _root_.BranchingSupport.lenA k r z g a = _root_.Formalism.MainNotions.S.lA k r z g a := by
  intro k r z hz hT g hg
  have hpos := (_root_.GlobalTheory.TensLen.lengths k r z hz hT g hg).2.2.1
  refine ⟨?_, fun a => ⟨hpos a, _root_.BranchingSupport.TensInh.lenA_eq_lA z g a⟩⟩
  have hbound : √(_root_.Formalism.QuantumDeterminants.Tz k r z) ≤ _root_.BranchingSupport.lenA k r z g (Fin.last r) := by
    rw [_root_.BranchingSupport.TensInh.lenA_eq_lA]
    unfold _root_.Formalism.MainNotions.S.lA _root_.Formalism.MainNotions.S.eucl
    refine le_csInf ⟨_, 0, Submodule.zero_mem _, rfl⟩ ?_
    rintro t ⟨y, hy, rfl⟩
    apply Real.sqrt_le_sqrt
    have hy0 : ∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0 := by
      intro i hi
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        unfold _root_.Formalism.QuantumDeterminants.bvec _root_.Formalism.QuantumDeterminants.eI
        refine Pi.single_eq_of_ne ?_ _
        intro h
        have h' := congrArg Fin.val h
        have := b.1.isLt
        simp only at h'
        omega
      | zero => rfl
      | add x x' _ _ hx hx' => simp [hx, hx']
      | smul c x _ hx => simp [hx]
    have hf : _root_.Formalism.QuantumDeterminants.fvec k r z (Fin.last r) = z := by
      unfold _root_.Formalism.QuantumDeterminants.fvec
      simp
    rw [hf]
    calc _root_.Formalism.QuantumDeterminants.Tz k r z = -(_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ (z - y)) (g⁻¹ *ᵥ (z - y))).re := by
          rw [herm_splitForm_inv_mulVec_eq_of_mem hg, herm_splitForm_sub_eq_of_isotropic z y hz hy0,
            _root_.Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq]
          simp
      _ ≤ _ := neg_re_herm_splitForm_le_sum_normSq k r _
  calc _root_.Formalism.QuantumDeterminants.Tz k r z = √(_root_.Formalism.QuantumDeterminants.Tz k r z) ^ 2 := (Real.sq_sqrt hT.le).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2

end GlobalTheory.LastLen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LastMajorantLengthSqGeAndPosStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_majorant_length_sq_ge_and_pos : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ g ∈ GG k r, Tz k r z ≤ lenA k r z g (Fin.last r) ^ 2 ∧ ∀ a, 0 < lenA k r z g a ∧ lenA k r z g a = lA k r z g a := by
  first | exact @GlobalTheory.LastLen.last_len | exact GlobalTheory.LastLen.last_len | (intros; apply GlobalTheory.LastLen.last_len <;> assumption)
end
end
