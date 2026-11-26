module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltStepSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PConormalGenerationGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.ModelSt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

universe u w

theorem SubvarDrop.proof : SubvarDrop.Statement.{u, w} := by
  intro k _ Ω _ _ N x d pp hx hpp hhom hle hrel hf
  have := hpp
  obtain ⟨f, hfp, hfq⟩ := hf
  obtain ⟨j, hj⟩ := hrel

  have hup : ringKrullDim (Poly k N ⧸ pp) + 1 ≤ ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hx.dim]
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_
    · apply mem_nonZeroDivisors_of_ne_zero
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hfp

  have hnf : ¬ IsField (Poly k N ⧸ pp) := by
    intro hF
    obtain ⟨v, hv⟩ := hF.mul_inv_cancel (a := Ideal.Quotient.mk pp (X j))
      (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← map_one (Ideal.Quotient.mk pp), Ideal.Quotient.eq] at hv
    have h0 := hhom _ hv 0
    rw [homogeneousComponent_zero] at h0
    have h1 : (1 : Poly k N) ∈ pp := by
      have hc : AddMonoidAlgebra.coeff (X j * g - 1 : Poly k N) 0 = -1 := by
        change constantCoeff (X j * g - 1 : Poly k N) = -1; simp
      rw [hc, map_neg, map_one] at h0
      simpa using pp.neg_mem h0
    exact hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hne0 : ringKrullDim (Poly k N ⧸ pp) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (Poly k N ⧸ pp) := (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr h0
    exact hnf Ring.KrullDimLE.isField_of_isDomain
  have hnn : 0 ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_nonneg_of_nontrivial

  rw [← WithBot.coe_one, ← WithBot.coe_natCast] at hup
  generalize hD : ringKrullDim (Poly k N ⧸ pp) = D at hup hne0 hnn
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe, top_add] at hup
      exact absurd hup (by simp)
    | coe n =>
      obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by
        have : n ≠ 0 := by rintro rfl; exact hne0 rfl
        omega⟩
      refine ⟨e, ?_, ⟨hpp, hhom, hle, ⟨j, hj⟩, hD⟩⟩
      rw [← WithBot.coe_add, WithBot.coe_le_coe] at hup
      have : ((e + 1 + 1 : ℕ) : ℕ∞) ≤ ((d + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast hup
      have := Nat.cast_le.mp this
      omega

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section InterNumPointLemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem interNumPoint_restrLen_eq_finrank (y : Fin (N + 1) → Ω) {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (F : SubSystem k y Ω) : restrLen (primeOf (S := k) y) F = Module.finrank k F.secs := by
  have hid : ∀ I : Chart y, idealMod (x := y) (primeOf (S := k) y) I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
    rw [(mem_primeOf_of_isHomogeneous y hfe).mp hf, zero_div]
  have hbot : ∀ I : Chart y, (F.twist (idealSys y (primeOf (S := k) y))).sub I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨q, hq, z, _, rfl⟩
    have hq' : q ∈ idealMod (x := y) (primeOf (S := k) y) I := hq
    rw [hid I, Submodule.mem_bot] at hq'
    rw [hq', zero_smul]
  have hsecs : (F.twist (idealSys y (primeOf (S := k) y))).secs = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have h1 := (Submodule.mem_iInf _).mp hz (singleChart hyj)
    rw [Submodule.restrictScalars_mem, hbot] at h1
    exact h1
  unfold restrLen
  rw [hsecs, Submodule.comap_bot, Submodule.ker_subtype,
    (Submodule.quotEquivOfEqBot (⊥ : Submodule k F.secs) rfl).length_eq, Module.length_eq_rank]
  rfl

theorem interNumPoint_interSum_eq (y : Fin (N + 1) → Ω) {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (L : Fin 0 → SubSystem k y Ω) (c : ℕ) :
    interSum (primeOf (S := k) y) L c = Module.finrank k (twistSys k y (c : ℤ)).secs := by
  have huniv : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by decide
  have h0 : tensorSub L ∅ = twistSys k y 0 := rfl
  rw [interSum, huniv, Finset.sum_singleton, h0, twistSys_zero_twist,
    interNumPoint_restrLen_eq_finrank y hyj]
  simp

end InterNumPointLemmas

theorem InterNumPoint.proof (hHP : HilbertPoint.Statement.{u, w}) : InterNumPoint.Statement.{u, w} := by
  intro k _ Ω _ _ N y hsub L
  obtain ⟨_, hdim, hsecs⟩ := hHP k Ω N y hsub
  obtain ⟨j, hj⟩ := hsub.relevant
  have hyj : y j ≠ 0 := by
    intro h
    apply hj
    rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j), aeval_X]
    exact h
  have hev : (fun _ : ℕ => (Module.finrank k (funField (k := k) y) : ℤ)) =ᶠ[atTop]
      interSum (primeOf (S := k) y) L := by
    filter_upwards [hdim, hsecs] with n hn hs
    rw [interNumPoint_interSum_eq y hyj, hs, hn]
  exact (tendsto_const_nhds.congr' hev).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ClaimLemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem coordGraded_tilde_mem_chartRing {I : Chart x} {y : Ω}
    (hy : y ∈ (coordGraded k x).tilde 0 I) : y ∈ chartRing k x I := by
  refine Submodule.span_induction (p := fun y _ => y ∈ chartRing k x I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hm' : m ∈ Submodule.span k {z | ∃ (f : Poly k N) (e' : ℕ), f.IsHomogeneous e' ∧
        (e' : ℤ) = a ∧ z = aeval x f} := hm
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ chartRing k x I)
      ?_ ?_ ?_ ?_ hm'
    · rintro _ ⟨f, e', hf, he', rfl⟩
      have hee : e' = e := by omega
      subst hee
      exact ⟨f, s, e', hs, hf, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact (chartRing k x I).zero_mem
    · intro a b _ _ ha hb; rw [smul_add]; exact (chartRing k x I).add_mem ha hb
    · intro r a _ ha; rw [smul_comm]; exact (chartRing k x I).smul_mem ha r
  · exact (chartRing k x I).zero_mem
  · intro a b _ _ ha hb; exact (chartRing k x I).add_mem ha hb
  · intro a y _ hy; rw [chartRing_smul_def]; exact (chartRing k x I).mul_mem a.2 hy

theorem coordGraded_tildeSys_twist (X : SubSystem k x Ω) :
    ((coordGraded k x).tildeSys 0).twist X = X := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    have hyA := coordGraded_tilde_mem_chartRing hy
    have hqy : q • y = (⟨y, hyA⟩ : chartRing k x I) • q := by
      rw [smul_eq_mul, chartRing_smul_def, mul_comm]
    rw [SetLike.mem_coe, hqy]
    exact (X.sub I).smul_mem _ hq
  · intro q hq
    refine Submodule.subset_span ⟨q, hq, 1, ?_, by rw [smul_eq_mul, mul_one]⟩
    exact Submodule.subset_span ⟨1, 1, 0, 0, one_mem _, isHomogeneous_one _ _,
      Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _, by simp, by simp⟩, by simp, by simp⟩

theorem twist_tildeSys_mono {M₁ M₂ : FinGradedSub (S := k) (x := x) Ω}
    (h : ∀ c, M₂.piece c ≤ M₁.piece c) (X : SubSystem k x Ω) (I : Chart x) :
    ∀ y ∈ ((M₂.tildeSys 0).twist X).sub I, y ∈ ((M₁.tildeSys 0).twist X).sub I := by
  intro y hy
  refine Submodule.span_mono ?_ hy
  rintro _ ⟨q, hq, z, hz, rfl⟩
  refine ⟨q, hq, z, Submodule.span_mono ?_ hz, rfl⟩
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  exact ⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩

variable (T : StepData k x) (Jg : FinGradedSub (S := k) (x := x) Ω)
  (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
    f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f})


include hJg in
theorem claim_le : ∀ c, Jg.piece c ≤ (coordGraded k x).piece c := by
  intro c
  rw [hJg]
  refine Submodule.span_mono ?_
  rintro _ ⟨f, e, -, hf, he, rfl⟩
  exact ⟨f, e, hf, he, rfl⟩


include hJg in
theorem claim_kill : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → ∀ (a : ℤ),
    ∀ z ∈ (coordGraded k x).piece a, aeval x f • z ∈ Jg.piece (a + e) := by
  intro f e hf hfe a z hz
  have hz' : z ∈ Submodule.span k {z | ∃ (g : Poly k N) (e' : ℕ), g.IsHomogeneous e' ∧
      (e' : ℤ) = a ∧ z = aeval x g} := hz
  refine Submodule.span_induction (p := fun z _ => aeval x f • z ∈ Jg.piece (a + e)) ?_ ?_ ?_ ?_ hz'
  · rintro _ ⟨g, e', hg, he', rfl⟩
    rw [hJg]
    exact Submodule.subset_span ⟨f * g, e + e', T.J.mul_mem_right g hf, hfe.mul hg,
      by push_cast; omega, by rw [map_mul, smul_eq_mul]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha

end ClaimLemmas

theorem ClaimVanish.proof (h₁ : StepTwo.Statement.{u, w, w}) (h₂ : TwistVanish.Statement.{u, w})
    (h₃ : ClaimSeq.Statement.{u, w}) : ClaimVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK
  obtain ⟨Jg, hJg, hseq⟩ := h₃ k Ω N x T
  obtain ⟨cS, hS⟩ := h₁ k Ω N x T hK Ω (coordGraded k x) Jg (claim_le T Jg hJg)
    (claim_kill T Jg hJg)
  obtain ⟨cB, hB⟩ := h₂ k Ω N x (twistBundle k x 0) (twistBundle k x 1) N x (twist_hyps k N x).1
    (twist_hyps k N x).2
  refine ⟨max cS cB, fun b => ?_⟩
  induction b with
  | zero =>
    intro c hc
    have h0 := hB 0 c (le_trans (le_max_right _ _) hc)
    have e : ((twistBundle k x 0).twist ((twistBundle k x 1).pow 0)).twist (twistSys k x c) =
        (T.L.pow 0).twist (twistSys k x c) := by
      show ((twistSys k x 0).twist (twistSys k x 0)).twist (twistSys k x c) =
        (twistSys k x 0).twist (twistSys k x c)
      rw [twistSys_zero_twist]
    rw [e] at h0
    exact h0
  | succ b ih =>
    intro c hc
    have hq := hS (b + 1) c (le_trans (le_max_left _ _) hc)
    rw [coordGraded_tildeSys_twist] at hq
    refine SubSystem.subsingleton_H_one_of_quot _
      ((Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))) ?_ ?_ hq
    · intro I y hy
      have hy' := twist_tildeSys_mono (claim_le T Jg hJg) _ I y hy
      rwa [coordGraded_tildeSys_twist] at hy'
    · exact SubSystem.subsingleton_H_one_of_smul _ _ T.si T.si_ne (hseq b c)
        (ih (c + T.c₁) (le_trans hc (by linarith [T.c₁_pos])))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsMemSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace CechZerothCohomologySections

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

def pt {i : Fin (N + 1)} (hi : i ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{i}, Finset.singleton_nonempty i, Finset.singleton_subset_iff.mpr hi⟩, Finset.card_singleton i⟩

theorem idx_ext {U : Finset (Fin (N + 1))} {i : ℕ} {K K' : Cech.Idx U i} (h : K.1.1 = K'.1.1) :
    K = K' :=
  Subtype.ext (Subtype.ext h)

theorem mem_sub_of_mem_secs (F : SubSystem S x E) {z : E} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I :=
  (Submodule.mem_iInf _).mp hz I

theorem cocycle_coe_eq (F : SubSystem S x E) {s : Cech.Cochain (fun I => F.sub I) 0}
    (hs : Cech.d (fun I => F.sub I) F.res 0 s = 0) (K K' : Cech.Idx (support x) 0) :
    (s K : E) = (s K' : E) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp K.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K'.2
  by_cases hab : a = b
  · subst hab; rw [idx_ext (ha.trans hb.symm)]
  have hsub : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact K.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self _)
    · rw [Finset.mem_singleton.mp hz]
      exact K'.1.2.2 (by rw [hb]; exact Finset.mem_singleton_self _)
  let J : Cech.Idx (support x) 1 :=
    ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsub⟩, Finset.card_pair hab⟩
  have ha' : a ∈ J.1.1 := Finset.mem_insert_self _ _
  have hb' : b ∈ J.1.1 := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have fa : Cech.face J ⟨a, ha'⟩ = K' := idx_ext (by
    change ({a, b} : Finset _).erase a = _
    rw [hb]; ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · rintro rfl; exact ⟨Ne.symm hab, Or.inr rfl⟩)
  have fb : Cech.face J ⟨b, hb'⟩ = K := idx_ext (by
    change ({a, b} : Finset _).erase b = _
    rw [ha]; ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · rintro rfl; exact ⟨hab, Or.inl rfl⟩)
  have hval : ∀ L L' : Cech.Idx (support x) 0, L = L' → (s L : E) = (s L' : E) := by
    rintro L L' rfl; rfl
  have h0 := congrArg (F.sub J.1).subtype (congrFun hs J)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cech.d_apply, map_sum, Pi.zero_apply, map_zero] at h0
  have huniv : (Finset.univ : Finset J.1.1) = {⟨a, ha'⟩, ⟨b, hb'⟩} := by
    ext ⟨z, hz⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    exact (Finset.mem_insert.mp hz).imp id Finset.mem_singleton.mp
  have hne : (⟨a, ha'⟩ : J.1.1) ≠ ⟨b, hb'⟩ := fun h => hab (congrArg Subtype.val h)
  rw [huniv, Finset.sum_pair hne, map_zsmul, map_zsmul] at h0
  have h1 : Cech.sgn ({a, b} : Finset (Fin (N + 1))) a • (s K' : E) +
      Cech.sgn ({a, b} : Finset (Fin (N + 1))) b • (s K : E) = 0 := by
    rw [← hval _ _ fa, ← hval _ _ fb]; exact h0
  have hsum := Cech.sum_sgn_of_card_two (Finset.card_pair hab)
  rw [Finset.sum_pair hab] at hsum
  have hb2 : Cech.sgn ({a, b} : Finset (Fin (N + 1))) b =
      - Cech.sgn ({a, b} : Finset (Fin (N + 1))) a := by linarith
  rw [hb2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h1
  have hsq : Cech.sgn ({a, b} : Finset (Fin (N + 1))) a *
      Cech.sgn ({a, b} : Finset (Fin (N + 1))) a = 1 := by
    unfold Cech.sgn; rw [← mul_pow]; norm_num
  have h2 : (s K' : E) - (s K : E) = 0 := by
    rw [← one_smul ℤ ((s K' : E) - (s K : E)), ← hsq, mul_smul, h1, smul_zero]
  exact (sub_eq_zero.mp h2).symm

def constC (F : SubSystem S x E) : F.secs →ₗ[S] Cech.Cochain (fun I => F.sub I) 0 where
  toFun z K := ⟨z, mem_sub_of_mem_secs F z.2 K.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem constC_cocycle (F : SubSystem S x E) (z : F.secs) :
    Cech.d (fun I => F.sub I) F.res 0 (constC F z) = 0 :=
  Cech.d_zero_of_compat (v := fun I => (⟨z, mem_sub_of_mem_secs F z.2 I⟩ : F.sub I))
    (fun _ _ _ => rfl)

def toKer (F : SubSystem S x E) :
    F.secs →ₗ[S] LinearMap.ker (Cech.d (fun I => F.sub I) F.res 0) :=
  (constC F).codRestrict _ fun z => LinearMap.mem_ker.mpr (constC_cocycle F z)

theorem exists_mem_support (hx : x ≠ 0) : ∃ i, i ∈ support x := by
  by_contra h
  simp only [not_exists] at h
  exact hx (funext fun i => by_contra fun hi => h i ((mem_support x).mpr hi))

theorem toKer_bijective (F : SubSystem S x E) (hx : x ≠ 0) : Function.Bijective (toKer F) := by
  obtain ⟨i₀, hi₀⟩ := exists_mem_support hx
  refine ⟨fun z₁ z₂ h => ?_, fun s => ?_⟩
  · have := congrArg (fun t => ((t.1 (pt hi₀) : F.sub (pt hi₀).1) : E)) h
    exact Subtype.ext this
  · have hs := LinearMap.mem_ker.mp s.2
    have hz : (s.1 (pt hi₀) : E) ∈ F.secs := by
      refine Submodule.mem_iInf _ |>.mpr fun I => ?_
      obtain ⟨i, hi⟩ := I.2.1
      have hsup : i ∈ support x := I.2.2 hi
      rw [Submodule.restrictScalars_mem, cocycle_coe_eq F hs (pt hi₀) (pt hsup)]
      exact F.mono _ I (Finset.singleton_subset_iff.mpr hi) _ (s.1 (pt hsup)).2
    refine ⟨⟨_, hz⟩, Subtype.ext (funext fun K => Subtype.ext ?_)⟩
    exact cocycle_coe_eq F hs (pt hi₀) K

theorem proof : CechZerothCohomologySections.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F hx
  have hp : (Cech.bdry (fun I => F.sub I) F.res 0).comap
      (LinearMap.ker (Cech.d (fun I => F.sub I) F.res 0)).subtype = ⊥ := by
    rw [show Cech.bdry (fun I => F.sub I) F.res 0 = ⊥ from rfl, Submodule.comap_bot,
      Submodule.ker_subtype]
  set_option synthInstance.maxHeartbeats 200000 in
    exact ⟨(Submodule.quotEquivOfEqBot _ hp).trans
    (LinearEquiv.ofBijective (toKer F) (toKer_bijective F hx)).symm⟩

end CechZerothCohomologySections

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AmpleAffineGen

noncomputable section

universe u w

namespace VeryAmpleDim

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem mem_sub_of_mem_secs {H : SubSystem k x Ω} {s : Ω} (hs : s ∈ H.secs) (I : Chart x) :
    s ∈ H.sub I :=
  (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs I)

theorem ampleBase_le_funField {r : ℕ} (h : Fin (r + 1) → Ω) {j : Fin (r + 1)} (hj : h j ≠ 0) {a : Ω}
    (ha : a ∈ ampleBase (S := k) h j) : a ∈ funField (k := k) h := by
  have hle : ampleBase (S := k) h j ≤ (funField (k := k) h).toSubalgebra :=
    Algebra.adjoin_le (by
      rintro _ ⟨l, rfl⟩
      exact IntermediateField.subset_adjoin k _ ⟨j, l, hj, rfl⟩)
  exact hle ha

theorem mem_funField_of_mem_chartRing {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ chartRing k x (singleChart hi)) : a ∈ funField (k := k) x :=
  ampleBase_le_funField x hi (mem_ampleBase_of_mem_chartRing hi ha)

theorem funField_le (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {i : Fin (N + 1)} (hi : x i ≠ 0) :
    funField (k := k) h ≤ funField (k := k) x := by
  show IntermediateField.adjoin k _ ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, l, hj, rfl⟩
  obtain ⟨Q', hQ'⟩ := Nb.invertible (singleChart hi)
  have hone : (1 : Ω) ∈ Nb.sub (singleChart hi) * Q' := by
    rw [hQ']; exact Submodule.one_le.mp le_rfl
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ Q', q ≠ 0 := by
    by_contra hc
    push Not at hc
    have hbot : Q' = ⊥ := (Submodule.eq_bot_iff _).mpr hc
    rw [hbot, Submodule.mul_bot] at hone
    exact one_ne_zero ((Submodule.mem_bot _).mp hone)
  have hmem : ∀ l, h l * q ∈ chartRing k x (singleChart hi) := by
    intro l
    have hl := Submodule.mul_mem_mul (mem_sub_of_mem_secs (hv.mem_secs l) (singleChart hi)) hq
    rw [hQ'] at hl
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hl
    rw [← ha]
    exact a.2
  have e : h l / h j = (h l * q) / (h j * q) := (mul_div_mul_right _ _ hq0).symm
  rw [e]
  exact div_mem (mem_funField_of_mem_chartRing hi (hmem l)) (mem_funField_of_mem_chartRing hi (hmem j))

theorem le_funField (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {j₀ : Fin (r + 1)} (hj₀ : h j₀ ≠ 0) :
    funField (k := k) x ≤ funField (k := k) h := by
  classical
  obtain ⟨n, a, b, J, -, hb, hsum, hloc⟩ := hv.affine j₀ hj₀
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at hsum
  have hh : ∀ I : Chart x, h j₀ ∈ (Nb.toSubSystem.pow 1).sub I := fun I =>
    Submodule.subset_span ⟨h j₀, mem_sub_of_mem_secs (hv.mem_secs j₀) I, 1,
      one_mem_twistMod_zero (S := k) I, by rw [smul_eq_mul, mul_one]⟩
  have hF : ∀ z ∈ ampleRing Nb.toSubSystem 1 (h j₀), z ∈ funField (k := k) h := fun z hz =>
    ampleBase_le_funField h hj₀ (hv.closed j₀ hj₀ hz)
  obtain ⟨c, hc⟩ := (J t).2.1
  have hxc : x c ≠ 0 := (mem_support x).mp ((J t).2.2 hc)
  have key : ∀ l, x l / x c ∈ funField (k := k) h := by
    intro l
    have hA : x l / x c ∈ chartRing k x (J t) :=
      ⟨X l, X c, 1, X_mem_monos hc, isHomogeneous_X k l, isHomogeneous_X k c, by simp⟩
    have hE : ∀ I : Chart x, ∃ E : ℕ,
        b t ^ E * (x l / x c) ∈ ampleChart Nb.toSubSystem 1 (h j₀) I := by
      intro I
      obtain ⟨e, he⟩ := hloc t I
      obtain ⟨D, hD⟩ := exists_pow_mul_mem I (J t)
        (chartRing_mono (subset_unionChart_right I (J t)) hA)
      refine ⟨e * D, ?_⟩
      rw [← pow_mul_cancel (u := b t) (y := x l / x c) (chartRatio_mul_chartRatio I (J t)) e D]
      exact (ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem
        (pow_mem (show _ ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from he) D)
        (mem_ampleSubalg_of_mem_chartRing (hh I) hD)
    choose E hE using hE
    have hmem : b t ^ (∑ I, E I) * (x l / x c) ∈ ampleRing Nb.toSubSystem 1 (h j₀) := by
      refine Set.mem_iInter.mpr fun I => ?_
      have hle : E I ≤ ∑ I, E I := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I)
      have e : b t ^ (∑ I, E I) * (x l / x c) = b t ^ ((∑ I, E I) - E I) * (b t ^ E I * (x l / x c)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e]
      exact (ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem
        (pow_mem (show b t ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from Set.mem_iInter.mp (hb t) I) _)
        (hE I)
    rw [← mul_div_cancel_left₀ (x l / x c) (pow_ne_zero (∑ I, E I) ht)]
    exact div_mem (hF _ hmem) (pow_mem (hF _ (hb t)) _)
  show IntermediateField.adjoin k _ ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, l, hi, rfl⟩
  have e : x l / x i = (x l / x c) / (x i / x c) := by field_simp
  rw [e]
  exact div_mem (key l) (key i)

end VeryAmpleDim

theorem VeryAmpleDim.proof : VeryAmpleDim.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hx hv
  obtain ⟨i, hi⟩ := hx.relevant
  have hxi : x i ≠ 0 := by
    intro h0
    apply hi
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X, h0]
  obtain ⟨j, hj⟩ : ∃ j, h j ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨Q', hQ'⟩ := Nb.invertible (singleChart hxi)
    have hbot : Nb.sub (singleChart hxi) = ⊥ := by
      rw [← hv.generates (singleChart hxi), Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      exact hc l
    rw [hbot, Submodule.bot_mul] at hQ'
    have h1 : (1 : Ω) ∈ (⊥ : Submodule (chartRing k x (singleChart hxi)) Ω) := by
      rw [hQ']; exact Submodule.one_le.mp le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).mp h1)
  have hfield : funField (k := k) x = funField (k := k) h :=
    le_antisymm (VeryAmpleDim.le_funField Nb hv hj) (VeryAmpleDim.funField_le Nb hv hxi)
  have hdx : dimCl k x = e := (DimTie.proof k Ω N x (Function.ne_iff.mpr ⟨i, hxi⟩) e).mp hx
  refine (DimTie.proof k Ω r h (Function.ne_iff.mpr ⟨j, hj⟩) e).mpr ?_
  rw [← hdx]
  unfold dimCl
  rw [hfield]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosedLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace GraphClosedAlt

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem chartRing_subset_ampleChart (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 h I := by
  refine ⟨0, ?_⟩
  rw [pow_zero, mul_one, mul_zero]
  change a ∈ twistMod S x 0 I
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero]
  have : a = (⟨a, ha⟩ : chartRing S x I) • (1 : Ω) := by rw [chartRing_smul_def, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem ampleChart_mul (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a b : Ω}
    (ha : a ∈ ampleChart H 1 h I) (hb : b ∈ ampleChart H 1 h I) : a * b ∈ ampleChart H 1 h I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  rw [one_mul] at hn hm ⊢
  rw [SubSystem.pow_sub] at hn hm ⊢
  rw [pow_add, pow_add]
  have : a * b * (h ^ n * h ^ m) = (a * h ^ n) * (b * h ^ m) := by ring
  rw [this]
  exact Submodule.mul_mem_mul hn hm

theorem ampleChart_pow (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ ampleChart H 1 h I) (e : ℕ) : a ^ e ∈ ampleChart H 1 h I := by
  induction e with
  | zero => rw [pow_zero]; exact chartRing_subset_ampleChart H h I (one_mem _)
  | succ e ih => rw [pow_succ]; exact ampleChart_mul H h I ih ha

def chartUnion (I J : Chart x) : Chart x :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

theorem xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

theorem div_mem_chartRing (I : Chart x) (j : Fin (N + 1)) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    x j / x i ∈ chartRing S x I :=
  ⟨X j, X i, 1, X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩

theorem exists_pow_mul_ratio_mem (I J : Chart x) {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I.1)
    {i : Fin (N + 1)} (hi : i ∈ I.1 ∪ J.1) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * (x i₀ / x i) ∈ chartRing S x I := by
  by_cases hiI : i ∈ I.1
  · exact ⟨0, by rw [pow_zero, one_mul]; exact div_mem_chartRing I i₀ hiI⟩
  have hiJ : i ∈ J.1 := (Finset.mem_union.mp hi).resolve_left hiI
  refine ⟨1, ?_⟩
  have hw : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
  have hQ : xProd I ≠ 0 := xProd_ne_zero I
  obtain ⟨m, hm⟩ : ∃ m, I.1.card = m + 1 := ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  obtain ⟨c, hc⟩ : ∃ c, J.1.card = c + 1 := ⟨J.1.card - 1, (Nat.succ_pred_eq_of_pos J.2.1.card_pos).symm⟩
  have hce : (J.1.erase i).card = c := by rw [Finset.card_erase_of_mem hiJ, hc]; rfl
  set P := ∏ j ∈ J.1.erase i, x j with hP
  have hJP : xProd J = x i * P := (Finset.mul_prod_erase J.1 x hiJ).symm
  have hprodI : ∏ i' ∈ I.1, (x i₀ / x i') = x i₀ ^ (m + 1) / xProd I := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hm]; rfl
  have hprodJ : ∏ j ∈ J.1.erase i, (x j / x i₀) = P / x i₀ ^ c := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hce]
  have key : (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ 1 * (x i₀ / x i) =
      (x i / x i₀) ^ m * (∏ j ∈ J.1.erase i, (x j / x i₀)) ^ (m + 1) *
        (∏ i' ∈ I.1, (x i₀ / x i')) ^ (c + 1) := by
    rw [hprodI, hprodJ, hJP, hm, hc, pow_one]
    simp only [div_pow, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [key]
  refine mul_mem (mul_mem (pow_mem (div_mem_chartRing I i hi₀) m)
    (pow_mem (prod_mem fun j _ => div_mem_chartRing I j hi₀) _))
    (pow_mem (prod_mem fun i' hi' => div_mem_chartRing I i₀ hi') _)

theorem exists_pow_mul_mem_chartRing (I J : Chart x) {z : Ω}
    (hz : z ∈ chartRing S x (chartUnion I J)) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * z ∈ chartRing S x I := by
  set σ := xProd J ^ I.1.card / xProd I ^ J.1.card
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hw : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  have hmon : ∀ s ∈ monos (S := S) (I.1 ∪ J.1), ∃ (e d : ℕ), s.IsHomogeneous d ∧
      σ ^ e * (x i₀ ^ d / aeval x s) ∈ chartRing S x I := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem a ha =>
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨e, he⟩ := exists_pow_mul_ratio_mem (S := S) I J hi₀ (i := i) (by exact_mod_cast hi)
      exact ⟨e, 1, isHomogeneous_X S i, by rw [pow_one, aeval_X]; exact he⟩
    | one => exact ⟨0, 0, isHomogeneous_one _ _, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨e₁, d₁, had, hae⟩ := ha
      obtain ⟨e₂, d₂, hbd, hbe⟩ := hb
      refine ⟨e₁ + e₂, d₁ + d₂, had.mul hbd, ?_⟩
      have : σ ^ (e₁ + e₂) * (x i₀ ^ (d₁ + d₂) / aeval x (a * b)) =
          (σ ^ e₁ * (x i₀ ^ d₁ / aeval x a)) * (σ ^ e₂ * (x i₀ ^ d₂ / aeval x b)) := by
        rw [map_mul, pow_add, pow_add]; ring
      rw [this]
      exact mul_mem hae hbe
  obtain ⟨f, s, d, hs, hf, hsd, rfl⟩ := hz
  obtain ⟨e, d', hsd', hmem⟩ := hmon s hs
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (chartUnion I J) hs
  have hsne : s ≠ 0 := fun h => hs0 (by rw [h, map_zero])
  have hdd : d' = d := hsd'.inj_right hsd hsne
  subst hdd
  have hf' : aeval x f / x i₀ ^ d' ∈ chartRing S x I :=
    ⟨f, X i₀ ^ d', d', pow_mem (X_mem_monos hi₀) d', hf, isHomogeneous_X_pow i₀ d', by simp⟩
  refine ⟨e, ?_⟩
  have : σ ^ e * (aeval x f / aeval x s) = (aeval x f / x i₀ ^ d') * (σ ^ e * (x i₀ ^ d' / aeval x s)) := by
    field_simp
  rw [this]
  exact mul_mem hf' hmem

theorem exists_pow_mul_mem_ampleRing (H : SubSystem S x Ω) (h b : Ω) (J : Chart x)
    (hb : b ∈ ampleRing H 1 h)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H 1 h I)
    {c : Ω} (hc : c ∈ chartRing S x J) : ∃ e : ℕ, b ^ e * c ∈ ampleRing H 1 h := by
  classical
  have hloc : ∀ I : Chart x, ∃ e : ℕ, b ^ e * c ∈ ampleChart H 1 h I := by
    intro I
    obtain ⟨e₀, he₀⟩ := hbJ I
    have hcU : c ∈ chartRing S x (chartUnion I J) := chartRing_mono Finset.subset_union_right hc
    obtain ⟨e₁, he₁⟩ := exists_pow_mul_mem_chartRing I J hcU
    refine ⟨e₀ * e₁, ?_⟩
    have hρσ : (xProd I ^ J.1.card / xProd J ^ I.1.card) *
        (xProd J ^ I.1.card / xProd I ^ J.1.card) = 1 := by
      have := xProd_ne_zero I
      have := xProd_ne_zero J
      field_simp
    have : b ^ (e₀ * e₁) * c = (b ^ e₀ * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ e₁ *
        ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e₁ * c) := by
      calc b ^ (e₀ * e₁) * c = (b ^ e₀) ^ e₁ * ((xProd I ^ J.1.card / xProd J ^ I.1.card) *
          (xProd J ^ I.1.card / xProd I ^ J.1.card)) ^ e₁ * c := by
            rw [hρσ, one_pow, mul_one, pow_mul]
        _ = _ := by ring
    rw [this]
    exact ampleChart_mul H h I (ampleChart_pow H h I he₀ e₁)
      (chartRing_subset_ampleChart H h I he₁)
  choose f hf using hloc
  refine ⟨∑ I, f I, Set.mem_iInter.mpr fun I => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (fun I _ => Nat.zero_le (f I)) (Finset.mem_univ I))
  have : b ^ (f I + k) * c = (b ^ f I * c) * b ^ k := by ring
  rw [hk, this]
  exact ampleChart_mul H h I (hf I) (ampleChart_pow H h I (Set.mem_iInter.mp hb I) k)

end GraphClosedAlt

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def CellLocEval.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ),
    Nonempty (cellH S y γ n ≃ₗ[S] cechHc ι (quotPart S (mIdealOver S y)) γ n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperDiffPolySt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperDiffPoly.Statement : Prop :=
  ∀ (t D : ℕ) (f : (Fin t → ℕ) → ℤ → ℚ) (μ : Fin t → ℤ),
    IsNumPolyLT t D (fun n c => f n (c + 1) - f n c) →
    (∀ j, IsNumPolyLT t D (fun n c => f (Function.update n j (n j + 1)) (c + μ j) - f n c)) →
    IsNumPolyLT t (D + 1) f

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionNonvanishSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SectionNonvanish.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → (∃ i, (X i : Poly k N) ∉ pp) →
    ∀ D : LineBundle k x, D.toSubSystem.Generated →
    ∃ s ∈ D.toSubSystem.secs, ∃ I, s ∉ (D.toSubSystem.twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSubquotFiniteSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperSubquotFinite.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F F₁ F₂ : SubFamily k x E), (∀ I, (F.sub I).FG) → (∀ I, F₁.sub I ≤ F.sub I) →
    (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ i : ℕ, FiniteDimensional k (SubSystem.quotH F₁.toSubSystem F₂.toSubSystem i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def StepThree.OnW.Lift.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∀ pp ∈ T.J.minimalPrimes, ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), 1 ≤ b → c₀ ≤ c → ∀ s : Chart x → Ω,
      (∀ I, s I ∈ ((T.L.pow b).twist (twistSys k x c)).sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I₂) →
      ∃ t ∈ ((T.L.pow b).twist (twistSys k x c)).secs, ∀ I, t - s I ∈ (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MulQuotEqSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def MulQuotEq.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (F₁ F₂ G₁ G₂ : SubSystem k x Ω) (s : Ω),
    (∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I) →
    (∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I) →
    (∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) →
    eulerCharQuot k G₁ G₂ = eulerCharQuot k F₁ F₂

end

end GroundTheory.Heights₂.Heights.Kleiman
end
