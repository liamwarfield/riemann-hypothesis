module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZFamily

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointDegreePos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section

variable {k : Type u} [Field k] {N : ℕ}

theorem oneBlock_homogeneousComponent (f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    oneBlock (S := k) (N := N) (homogeneousComponent n f) =
      homogeneousComponent n (oneBlock (S := k) (N := N) f) := by
  classical
  have ho : ∀ g, oneBlock (S := k) (N := N) g = rename (HilbertPositive.blockEquiv N) g := fun _ => rfl
  ext d
  set d' := Finsupp.mapDomain (HilbertPositive.blockEquiv N).symm d with hd'
  have hd : d = Finsupp.mapDomain (HilbertPositive.blockEquiv N) d' := by
    rw [hd', ← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hdeg : d.degree = d'.degree := by
    rw [hd, Finsupp.degree_mapDomain]
  rw [ho, ho, coeff_homogeneousComponent, hd,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective, coeff_homogeneousComponent, ← hd, hdeg]

theorem isMultiProjPrime_comap_oneBlock {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {pp : Ideal (Poly k N)} (h : IsSubvar x pp 0) :
    NumbersDVR.IsMultiProjPrime (pp.comap (oneBlock (S := k) (N := N)).toRingHom) ∧
      FieldNumbers.relDim (pp.comap (oneBlock (S := k) (N := N)).toRingHom) =
        ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  have := h.isPrime
  let e : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (HilbertPositive.blockEquiv N)).toRingEquiv
  have hc : pp.comap (oneBlock (S := k) (N := N)).toRingHom = pp.comap e.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  refine ⟨⟨Ideal.comap_isPrime _ _, ?_, ?_⟩, ?_⟩
  · intro f hf b
    have heq : weightedHomogeneousComponent (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) b f =
        homogeneousComponent (b ()) f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent,
        HilbertPositive.weight_blockWeight_one d]
      congr 1
      apply propext
      constructor
      · intro h; rw [← h]
      · intro h; funext u; exact h
    rw [heq]
    change oneBlock (S := k) (N := N) _ ∈ pp
    change oneBlock (S := k) (N := N) f ∈ pp at hf
    rw [oneBlock_homogeneousComponent]
    exact h.homog _ hf _
  · intro u
    obtain ⟨i, hi⟩ := h.relevant
    refine ⟨i, ?_⟩
    change oneBlock (S := k) (N := N) (X _) ∉ pp
    rw [oneBlock, rename_X]
    exact hi
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit, hc]
    have hm : pp = (pp.comap e.toRingHom).map e.toRingHom := by
      rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective]
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e hm), h.dim]

end

theorem PointDegreePos.proof : PointDegreePos.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp h
  obtain ⟨hP, hrel⟩ := isMultiProjPrime_comap_oneBlock h
  have := hP.isPrime
  obtain ⟨hfd, -⟩ := FieldNumbers.IntNumBase.full k Unit (fun _ => Fin (N + 1)) _ hP hrel
  unfold FieldNumbers.resDeg
  rw [dite_eq_left hP.isPrime]
  exact Module.finrank_pos

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutNonempty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Chart

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem coe_aeval_ratio_mem_idealMod {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) {j : Fin (N + 1)} (hj : x j ≠ 0)
    {p : Poly k N} (hp : p ∈ pp) :
    ((aeval (ratio (S := k) hj) p : chartRing k x (singleChart hj)) : Ω) ∈
      idealMod (x := x) pp (singleChart hj) := by
  rw [← sum_homogeneousComponent p]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.sum_mem _ fun d _ => Submodule.subset_span ?_
  exact ⟨homogeneousComponent d p, X j ^ d, d, hh p hp d,
    pow_mem (X_mem_monos (Finset.mem_singleton_self j)) d, homogeneousComponent_isHomogeneous d p,
    isHomogeneous_X_pow j d, coe_aeval_ratio' hj (homogeneousComponent_isHomogeneous d p)⟩

theorem coe_aeval_ratio_mul_mem_span {L : SubSystem k x Ω} {s : Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    {z : Poly k N} (hz : z ∈ zeroIdeal L s) {δ : Ω} (hδ : δ ∈ L.sub (singleChart hj)) :
    ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * δ ∈
      Submodule.span (chartRing k x (singleChart hj)) {s} := by
  induction hz using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hfc, hf⟩ := hf
    obtain ⟨o, ho, he⟩ := hf (singleChart hj) δ hδ
    rw [twistMod_eq_span _ _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton] at ho
    obtain ⟨b, rfl⟩ := ho
    rw [Submodule.mem_span_singleton]
    refine ⟨b, ?_⟩
    rw [coe_aeval_ratio hj hfc, chartRing_smul_def, div_mul_eq_mul_div, he, chartRing_smul_def,
      zpow_natCast]
    field_simp
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add (f := _), Subalgebra.coe_add, add_mul]
    exact Submodule.add_mem _ ha hb
  | smul g z _ hz =>
    rw [smul_eq_mul, map_mul, Subalgebra.coe_mul, mul_assoc]
    exact Submodule.smul_mem _ (aeval (ratio (S := k) hj) g) hz

theorem sub_le_twist_sup_span {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) (L : LineBundle k x) (s : Ω)
    (hmin : ∀ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, ∀ i, (X i : Poly k N) ∈ qq)
    (j : Fin (N + 1)) (hj : x j ≠ 0) :
    L.sub (singleChart hj) ≤ (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
      Submodule.span (chartRing k x (singleChart hj)) {s} := by
  have hrad : (X j : Poly k N) ∈ (pp ⊔ zeroIdeal L.toSubSystem s).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.mpr fun qq hq => hmin qq hq j
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hm
  intro ℓ hℓ
  have h1 : ((aeval (ratio (S := k) hj) ((X j : Poly k N) ^ m) : chartRing k x (singleChart hj)) : Ω) = 1 := by
    rw [map_pow, aeval_X, SubmonoidClass.coe_pow]
    change (x j / x j) ^ m = 1
    rw [div_self hj, one_pow]
  have hsplit : ℓ = ((aeval (ratio (S := k) hj) p : chartRing k x (singleChart hj)) : Ω) * ℓ +
      ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * ℓ := by
    rw [← add_mul, ← Subalgebra.coe_add, ← map_add (f := _), hpz, h1, one_mul]
  rw [hsplit]
  refine Submodule.add_mem_sup (Submodule.subset_span ?_) (coe_aeval_ratio_mul_mem_span hj hz hℓ)
  exact ⟨_, coe_aeval_ratio_mem_idealMod hh hj hp, ℓ, hℓ, rfl⟩

end Chart

theorem CutNonempty.proof (hO : CutOneGenerator.Statement.{u, w}) : CutNonempty.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs _
  by_contra hne
  push Not at hne
  exact hO k Ω N x n pp L s hW hL hs (sub_le_twist_sup_span hW.homog L s hne)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionMulInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionMulInj

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_of_mem_idealMod (J : Ideal (Poly S N)) (I : Chart x) {z : Ω} (hz : z ∈ idealMod (x := x) J I) :
    ∃ (G m : Poly S N) (e : ℕ), G ∈ J ∧ m ∈ monos I.1 ∧ G.IsHomogeneous e ∧ m.IsHomogeneous e ∧
      z = aeval x G / aeval x m := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero => exact ⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨G, m, e, hG, hm, hGe, hme, rfl⟩ := ha
    obtain ⟨G', m', e', hG', hm', hGe', hme', rfl⟩ := hb
    refine ⟨G * m' + m * G', m * m', e + e', J.add_mem (J.mul_mem_right _ hG) (J.mul_mem_left _ hG'),
      mul_mem hm hm', (hGe.mul hme').add (hme.mul hGe'), hme.mul hme', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hm) (eval_ne_zero_of_mem_monos I hm')]
    simp only [map_add (f := _), map_mul]
  | smul r a _ ha =>
    obtain ⟨F, m₀, e₀, hm₀, hF, hm₀e, hr⟩ := r.2
    obtain ⟨G, m, e, hG, hm, hGe, hme, rfl⟩ := ha
    refine ⟨F * G, m₀ * m, e₀ + e, J.mul_mem_left _ hG, mul_mem hm₀ hm, hF.mul hGe, hm₀e.mul hme, ?_⟩
    rw [chartRing_smul_def, hr, map_mul, map_mul, div_mul_div_comm]


omit [Algebra S Ω] in
theorem not_mem_of_mem_monos {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) {I : Chart x}
    (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {m : Poly S N} (hm : m ∈ monos I.1) : m ∉ pp := by
  induction hm using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    exact hX j (by exact_mod_cast hj)
  | one => exact fun h => hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  | mul a b _ _ ha hb => exact fun h => (hpp.mem_or_mem h).elim ha hb

theorem mem_of_div_mem_idealMod {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {F m : Poly S N} {e : ℕ} (hm : m ∈ monos I.1)
    (hF : F.IsHomogeneous e) (hme : m.IsHomogeneous e) (h : aeval x F / aeval x m ∈ idealMod (x := x) pp I) :
    F ∈ pp := by
  obtain ⟨G, m', e', hG, hm', hGe, hme', heq⟩ := exists_of_mem_idealMod pp I h
  have h0 := eval_ne_zero_of_mem_monos I hm
  have h0' := eval_ne_zero_of_mem_monos I hm'
  have hdiff : F * m' - m * G ∈ primeOf (S := S) x := by
    have hhom : (F * m' - m * G).IsHomogeneous (e + e') := (hF.mul hme').sub (hme.mul hGe)
    rw [mem_primeOf_of_isHomogeneous x hhom, map_sub, map_mul, map_mul, sub_eq_zero]
    rw [div_eq_div_iff h0 h0'] at heq
    rw [heq, mul_comm]
  have hFm : F * m' ∈ pp := by
    have := pp.add_mem (hZ hdiff) (pp.mul_mem_left m hG)
    rwa [sub_add_cancel] at this
  exact (hpp.mem_or_mem hFm).resolve_right (not_mem_of_mem_monos hpp hX hm')

theorem mem_or_mem {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) (a b : chartRing S x I)
    (h : (a : Ω) * b ∈ idealMod (x := x) pp I) :
    (a : Ω) ∈ idealMod (x := x) pp I ∨ (b : Ω) ∈ idealMod (x := x) pp I := by
  obtain ⟨F, m, e, hm, hF, hme, ha⟩ := a.2
  obtain ⟨F', m', e', hm', hF', hme', hb⟩ := b.2
  rw [ha, hb, div_mul_div_comm, ← map_mul, ← map_mul] at h
  have := mem_of_div_mem_idealMod hpp hZ hX (mul_mem hm hm') (hF.mul hF') (hme.mul hme') h
  refine (hpp.mem_or_mem this).imp (fun hF0 => ?_) (fun hF0 => ?_)
  · rw [ha]; exact Submodule.subset_span ⟨F, m, e, hF0, hm, hF, hme, rfl⟩
  · rw [hb]; exact Submodule.subset_span ⟨F', m', e', hF0, hm', hF', hme', rfl⟩

end SectionMulInj


open SectionMulInj in
theorem SectionMulInj.proof : SectionMulInj.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hpp hhom hZ D M s ⟨f, hf, hfp⟩ I y hy hsy
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change y ∈ idealMod (x := x) pp I * M.sub I
  by_cases hX : ∃ j ∈ I.1, (X j : Poly k N) ∈ pp
  · obtain ⟨j, hj, hXj⟩ := hX
    have := StepThree.OnW.Gen.sub_le_twist_idealSys_of_mem M.toSubSystem I hj hXj hy
    rwa [SubSystem.twist_sub_eq_mul_of_line] at this
  push Not at hX
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)

  obtain ⟨e, he⟩ : ∃ e, homogeneousComponent e f ∉ pp := by
    by_contra hall
    push Not at hall
    exact hfp (by rw [← sum_homogeneousComponent f]; exact pp.sum_mem fun d _ => hall d)
  set g : chartRing k x I := ⟨_, StepThree.Away.div_pow_mem_chartRing I hi
    (homogeneousComponent_isHomogeneous e f)⟩ with hg
  have hgI : (g : Ω) ∉ idealMod (x := x) pp I := fun h => he <| by
    refine mem_of_div_mem_idealMod hpp hZ hX (pow_mem (X_mem_monos hi) e)
      (homogeneousComponent_isHomogeneous e f) (isHomogeneous_X_pow i e) ?_
    rw [map_pow, aeval_X]; exact h

  have hgD : Submodule.span (chartRing k x I) {(g : Ω)} * D.sub I ≤ Submodule.span _ {s} := by
    rw [Submodule.mul_le]
    intro a ha δ hδ
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
      (StepThree.Away.homogeneousComponent_mul_mem D.toSubSystem s I hi hf e δ hδ)
    rw [Submodule.mem_span_singleton]
    refine ⟨r * t, ?_⟩
    have hpow : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    rw [chartRing_smul_def] at ht
    change ((r * t : chartRing k x I) : Ω) * s = ((r : Ω) * (g : Ω)) * δ
    rw [Subalgebra.coe_mul, hg]
    change (r : Ω) * t * s = (r : Ω) * (aeval x (homogeneousComponent e f) / x i ^ e) * δ
    rw [mul_assoc (r : Ω), mul_assoc (r : Ω)]
    congr 1
    rw [div_mul_eq_mul_div, eq_div_iff hpow, ← ht]
    ring
  obtain ⟨D', hD'⟩ := D.invertible I
  obtain ⟨M', hM'⟩ := M.invertible I
  have h1D : (1 : Ω) ∈ D.sub I * D' := by rw [hD']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩

  have hgs : (g : Ω) ∈ Submodule.span (chartRing k x I) {s} * D' := by
    have := Submodule.mul_mem_mul (Submodule.mem_span_singleton_self (g : Ω)) h1D
    rw [mul_one, ← mul_assoc] at this
    exact mul_le_mul' hgD le_rfl this
  have hsy' : s * y ∈ idealMod (x := x) pp I * (D.sub I * M.sub I) := by
    rw [SubSystem.twist_sub_eq_mul_of_line, SubSystem.twist_sub_eq_mul_of_line] at hsy
    exact hsy
  have hgy : Submodule.span (chartRing k x I) {(g : Ω) * y} ≤ idealMod (x := x) pp I * M.sub I := by
    calc Submodule.span (chartRing k x I) {(g : Ω) * y}
        ≤ Submodule.span (chartRing k x I) {s} * D' * Submodule.span _ {y} := by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          exact Submodule.mul_mem_mul hgs (Submodule.mem_span_singleton_self y)
      _ = D' * Submodule.span _ {s * y} := by
          rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span]; ring
      _ ≤ D' * (idealMod (x := x) pp I * (D.sub I * M.sub I)) := by
          gcongr
          rw [Submodule.span_le, Set.singleton_subset_iff]; exact hsy'
      _ = idealMod (x := x) pp I * M.sub I * (D.sub I * D') := by ring
      _ = idealMod (x := x) pp I * M.sub I := by rw [hD', mul_one]

  have hyM : Submodule.span (chartRing k x I) {y} * M' ≤ idealMod (x := x) pp I := by
    intro z hz
    have hz1 : z ∈ (1 : Submodule (chartRing k x I) Ω) := by
      rw [← hM']
      refine (mul_le_mul' ?_ le_rfl : _ ≤ M.sub I * M') hz
      rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hz1
    have hgz : (g : Ω) * algebraMap (chartRing k x I) Ω r ∈ idealMod (x := x) pp I := by
      have hle : Submodule.span (chartRing k x I) {(g : Ω)} * (Submodule.span _ {y} * M') ≤
          idealMod (x := x) pp I := by
        calc Submodule.span (chartRing k x I) {(g : Ω)} * (Submodule.span _ {y} * M')
            = Submodule.span _ {(g : Ω) * y} * M' := by
              rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span]; ring
          _ ≤ idealMod (x := x) pp I * M.sub I * M' := by gcongr
          _ = idealMod (x := x) pp I := by rw [mul_assoc, hM', mul_one]
      exact hle (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) hz)
    exact ((mem_or_mem hpp hZ hX g r hgz).resolve_left hgI)
  have hle : Submodule.span (chartRing k x I) {y} ≤ idealMod (x := x) pp I * M.sub I :=
    calc Submodule.span (chartRing k x I) {y}
        = Submodule.span (chartRing k x I) {y} * M' * M.sub I := by
          rw [mul_assoc, mul_comm M', hM', mul_one]
      _ ≤ idealMod (x := x) pp I * M.sub I := by gcongr
  exact hle (Submodule.mem_span_singleton_self y)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutOneGenerator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace CutOneGenerator

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem mem_sub_of_mem_secs {S : Type u} [CommRing S] {E : Type w} [Field E] [Algebra S E] {M : ℕ}
    {z : Fin (M + 1) → E} {H : SubSystem S z E} {t : E} (ht : t ∈ H.secs) (I : Chart z) :
    t ∈ H.sub I :=
  (Submodule.restrictScalars_mem S _ _).mp ((Submodule.mem_iInf _).mp ht I)

theorem mem_chartRing_of_mem_idealMod {pp : Ideal (Poly k N)} {I : Chart x} {a : Ω}
    (ha : a ∈ idealMod (x := x) pp I) : a ∈ chartRing k x I := by
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨f, s, e, -, hs, hf, hse, rfl⟩ := ha; exact ⟨f, s, e, hs, hf, hse, rfl⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact mul_mem c.2 ha

variable {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {Q : SubSystem k x Ω} {Q' : SubSystem k y K'} {ρ : Ω → K'}

theorem restrict_zero (hR : RestrictData Q hxy Q' ρ) (J : Chart y) : ρ 0 = 0 := by
  have := hR.add J 0 (Q.sub _).zero_mem 0 (Q.sub _).zero_mem
  rw [add_zero] at this
  simpa using this

theorem exists_restrict_mul (hR : RestrictData Q hxy Q' ρ) (J : Chart y) {c q : Ω}
    (hc : c ∈ chartRing k x (liftChart hxy J)) (hq : q ∈ Q.sub (liftChart hxy J)) :
    ∃ b ∈ chartRing k y J, ρ (c * q) = b * ρ q := by
  obtain ⟨f, t, e, ht, hf, hte, rfl⟩ := hc
  exact ⟨_, ⟨f, t, e, ht, hf, hte, rfl⟩, hR.smul J q hq f t e ht hf hte⟩

theorem restrict_twist_eq_zero (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {z : Ω}
    (hz : z ∈ (Q.twist (idealSys x pp)).sub (liftChart hxy J)) :
    z ∈ Q.sub (liftChart hxy J) ∧ ρ z = 0 := by
  have hgen : ∀ w ∈ Q.sub (liftChart hxy J), ∀ q ∈ idealMod (x := x) pp (liftChart hxy J),
      q * w ∈ Q.sub (liftChart hxy J) ∧ ρ (q * w) = 0 := by
    intro w hw q hq
    have hmw : ∀ a ∈ idealMod (x := x) pp (liftChart hxy J), a * w ∈ Q.sub (liftChart hxy J) :=
      fun a ha => (Q.sub _).smul_mem
        ⟨a, mem_chartRing_of_mem_idealMod (pp := pp) (I := liftChart hxy J) ha⟩ hw
    refine ⟨hmw q hq, ?_⟩
    induction hq using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨f, t, e, hfp, ht, hf, hte, rfl⟩ := ha
      rw [hR.smul J w hw f t e ht hf hte,
        (mem_primeOf_of_isHomogeneous y hf).mp (hpp ▸ hfp), zero_div, zero_mul]
    | zero => rw [zero_mul]; exact restrict_zero hR J
    | add a b ha hb iha ihb =>
      rw [add_mul, hR.add J _ (hmw a ha) _ (hmw b hb), iha, ihb, add_zero]
    | smul c a ha iha =>
      obtain ⟨b, -, hb⟩ := exists_restrict_mul hR J c.2 (hmw a ha)
      rw [chartRing_smul_def, mul_assoc, hb, iha, mul_zero]
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨q, hq, w, hw, rfl⟩ := hz; exact hgen w hw q hq
  | zero => exact ⟨zero_mem _, restrict_zero hR J⟩
  | add a b _ _ ha hb => exact ⟨add_mem ha.1 hb.1, by rw [hR.add J a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
  | smul c a _ ha =>
    refine ⟨(Q.sub _).smul_mem c ha.1, ?_⟩
    obtain ⟨b, -, hb⟩ := exists_restrict_mul hR J c.2 ha.1
    rw [chartRing_smul_def]
    erw [hb]
    rw [ha.2, mul_zero]

theorem exists_eq_mul_of_le (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {s : Ω} (hs : s ∈ Q.sub (liftChart hxy J))
    (hle : Q.sub (liftChart hxy J) ≤ (Q.twist (idealSys x pp)).sub (liftChart hxy J) ⊔
      Submodule.span (chartRing k x (liftChart hxy J)) {s}) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ b ∈ chartRing k y J, t = b * ρ s := by
  rw [← hR.span J] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨q, hq, rfl⟩ := ht
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (hle hq)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨hu', hu0⟩ := restrict_twist_eq_zero hR hpp J hu
    obtain ⟨b, hb, he⟩ := exists_restrict_mul hR J a.2 hs
    refine ⟨b, hb, ?_⟩
    rw [hR.add J u hu' _ ((Q.sub _).smul_mem a hs), hu0, zero_add, chartRing_smul_def, he]
  | zero => exact ⟨0, zero_mem _, (zero_mul _).symm⟩
  | add t t' _ _ ht ht' =>
    obtain ⟨b, hb, rfl⟩ := ht
    obtain ⟨b', hb', rfl⟩ := ht'
    exact ⟨b + b', add_mem hb hb', (add_mul _ _ _).symm⟩
  | smul c t _ ht =>
    obtain ⟨b, hb, rfl⟩ := ht
    exact ⟨c * b, mul_mem c.2 hb, by rw [chartRing_smul_def, mul_assoc]⟩

theorem exists_algHom_ker_eq {R : Type w} [CommRing R] [Algebra k R] (P : Ideal R) [P.IsPrime] :
    ∃ (F : Type w) (_ : Field F) (_ : Algebra k F) (ψ : R →ₐ[k] F), RingHom.ker ψ = P := by
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (IsScalarTower.toAlgHom k (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  ext a
  rw [RingHom.mem_ker]
  change algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P a) = 0 ↔ _
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end CutOneGenerator


open CutOneGenerator in
theorem CutOneGenerator.proof (hG : GlobalFunctionsIntegral.Statement.{u, w}) :
    CutOneGenerator.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs hgen
  obtain ⟨r, h, hV⟩ := hL
  obtain ⟨j, hXj⟩ := hW.relevant
  have hxj : x j ≠ 0 := by
    intro h0
    apply hXj
    apply hW.le
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j), aeval_X, h0]
  obtain ⟨hprime, hpt⟩ :=
    PrimeFiltration.Point.proof k Ω N x pp hW.isPrime hW.homog hW.le j hxj hXj
  obtain ⟨K', _, _, ψ, hker⟩ := @exists_algHom_ker_eq k _ _ _ _ (chartPrime pp hxj) hprime
  set y : Fin (N + 1) → K' := fun i => ψ (ratio hxj i) with hy
  have hpy : primeOf (S := k) y = pp := hpt K' ψ hker
  have hy0 : y j ≠ 0 := by
    have e : ratio (S := k) hxj j = 1 := Subtype.ext (div_self hxj)
    show ψ (ratio hxj j) ≠ 0
    rw [e, map_one]
    exact one_ne_zero
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i hyi hxi
    apply hyi
    have e : ratio (S := k) hxj i = 0 := Subtype.ext (by show x i / x j = 0; rw [hxi, zero_div])
    show ψ (ratio hxj i) = 0
    rw [e, map_zero]
  have hne : y ≠ 0 := Function.ne_iff.mpr ⟨j, hy0⟩
  obtain ⟨Q', ρ, hR, hV', hdim⟩ :=
    exists_restrictData_isVeryAmpleBy (by rw [hpy]; exact hW.le) hxy (singleChart hy0) L h hV
  have hWy : IsSubvar y (primeOf (S := k) y) (n + 1) := by
    rw [hpy]; exact ⟨hW.isPrime, hW.homog, hpy.le, hW.relevant, hW.dim⟩
  have hdy : dimCl k y = ((n + 1 : ℕ) : Cardinal) := (DimTie.proof k K' N y hne (n + 1)).mp hWy
  have hmul : ∀ t ∈ Q'.secs, ∀ i (hi : y i ≠ 0), ∃ b ∈ chartRing k y (singleChart hi), t = b * ρ s :=
    fun t ht i hi => exists_eq_mul_of_le hR hpy (singleChart hi) (mem_sub_of_mem_secs hs _)
      (hgen i (hxy i hi)) (mem_sub_of_mem_secs ht _)
  have hρs : ρ s ≠ 0 := by
    intro h0
    obtain ⟨Q'', hQ''⟩ := Q'.invertible (singleChart hy0)
    have hbot : Q'.sub (singleChart hy0) = ⊥ := (Submodule.eq_bot_iff _).mpr fun t ht => by
      obtain ⟨b, -, rfl⟩ := exists_eq_mul_of_le hR hpy (singleChart hy0) (mem_sub_of_mem_secs hs _)
        (hgen j (hxy j hy0)) ht
      rw [h0, mul_zero]
    rw [hbot, Submodule.bot_mul] at hQ''
    have h1 : (1 : K') ∈ (⊥ : Submodule (chartRing k y (singleChart hy0)) K') := by
      rw [hQ'']; exact Submodule.one_le.mp le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).mp h1)
  have hint : ∀ l, IsIntegral k (ρ (h l) / ρ s) := fun l => hG k K' N y _ hne fun i hi => by
    obtain ⟨b, hb, he⟩ := hmul (ρ (h l)) (hV'.mem_secs l) i hi
    rw [he, mul_div_cancel_right₀ _ hρs]
    exact hb
  have halg : Algebra.IsAlgebraic k (funField (k := k) (ρ ∘ h)) := by
    apply IntermediateField.isAlgebraic_adjoin
    rintro _ ⟨i, l, -, rfl⟩
    have e : (ρ ∘ h) l / (ρ ∘ h) i = ρ (h l) / ρ s * (ρ (h i) / ρ s)⁻¹ := by
      rw [inv_div, div_mul_div_cancel₀ hρs]; rfl
    rw [e]
    exact (hint l).mul (hint i).inv
  have h0 : dimCl k (ρ ∘ h) = 0 := trdeg_eq_zero
  rw [← hdim, hdy] at h0
  exact Nat.succ_ne_zero n (Nat.cast_eq_zero.mp h0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MConeMapOverOfIsMultiHomog
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (isMultiHomog_mul isMultiHomog_add isMultiHomog_X isMultiHomog_one)

namespace ResidueMap

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem isMultiHomog_sub {f g : MRingOver F ι} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  exacts [hf m h k, hg m h k]


omit [Fintype K] in
theorem isMultiHomog_C (r : F) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C r : MRingOver F ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
  subst hm0
  simp


omit [Fintype K] in
theorem isMultiHomog_rename [DecidableEq K] (k : K) {f : MvPolynomial (ι k) F} {m : ℕ} (hf : f.IsHomogeneous m) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (fun i : ι k => (⟨k, i⟩ : Σ k, ι k)) f) (Pi.single k m) := by
  classical
  intro e he k'
  rw [support_rename_of_injective sigma_mk_injective] at he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  have hdeg : ∑ i, d i = m := by
    have h1 := hf (mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    simpa using h1
  by_cases hk : k' = k
  · subst hk
    rw [Pi.single_eq_same, ← hdeg]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply_of_injective sigma_mk_injective d i
  · rw [Pi.single_eq_of_ne hk]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact Finsupp.mapDomain_of_notMem_range _ _
      (by rintro ⟨j, hj⟩; exact hk (congrArg Sigma.fst hj).symm)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_rename_block {A : Type} [CommRing A] [Algebra F A] (z : (Σ k, ι k) → A) (k : K)
    (p : MvPolynomial (ι k) F) :
    aeval z (rename (fun i : ι k => (⟨k, i⟩ : Σ k, ι k)) p) = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec z k) p := by
  rw [aeval_rename]; rfl

variable {Ω : Type} [Field Ω] [Algebra F Ω]

theorem mConeMapOver_of_isMultiHomog (y : (Σ k, ι k) → Ω) {g : MRingOver F ι} {d : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) :
    mConeMapOver F y g = MvPolynomial.C (aeval y g) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p = ∏ k, MvPolynomial.X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  simp only [mConeMapOver, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mem_mIdealOver_iff (y : (Σ k, ι k) → Ω) {g : MRingOver F ι} {d : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) :
    g ∈ mIdealOver F y ↔ aeval y g = 0 := by
  rw [mIdealOver, RingHom.mem_ker, mConeMapOver_of_isMultiHomog y hg]
  have hP : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)
  rw [mul_eq_zero, or_iff_left hP, MvPolynomial.C_eq_zero]

variable {K' : Type} [Field K'] [Algebra F K']

theorem vanish {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {g : MRingOver F ι} {d : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d)
    (h : aeval y g = 0) : aeval y' g = 0 :=
  (mem_mIdealOver_iff y' hg).mp (hle ((mem_mIdealOver_iff y hg).mpr h))

theorem ne_zero_of {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {g : MRingOver F ι} {d : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d)
    (hg' : aeval y' g ≠ 0) : aeval y g ≠ 0 :=
  fun h => hg' (vanish hle hg h)

theorem wd {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {f g f₂ g₂ : MRingOver F ι} {n n₂ : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g n)
    (hf₂ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f₂ n₂)
    (hg₂ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g₂ n₂)
    (hg' : aeval y' g ≠ 0) (hg₂' : aeval y' g₂ ≠ 0)
    (h : aeval y f / aeval y g = aeval y f₂ / aeval y g₂) :
    aeval y' f / aeval y' g = aeval y' f₂ / aeval y' g₂ := by
  rw [div_eq_div_iff (ne_zero_of hle hg hg') (ne_zero_of hle hg₂ hg₂')] at h
  rw [div_eq_div_iff hg' hg₂']
  have h2 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f₂ * g) (n + n₂) := by
    rw [add_comm]; exact isMultiHomog_mul hf₂ hg
  have hp := isMultiHomog_sub (isMultiHomog_mul hf hg₂) h2
  have h0 := vanish hle hp (by rw [map_sub, map_mul, map_mul, h, sub_self])
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h0
  exact h0


variable (F) in
def fracSet (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι k) → K') : Set Ω :=
  {x | ∃ (f g : MRingOver F ι) (n : K → ℕ),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n ∧
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g n ∧ aeval y' g ≠ 0 ∧
    x = aeval y f / aeval y g}

def locR {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y') :
    Subalgebra F Ω where
  carrier := fracSet F y y'
  mul_mem' := by
    rintro _ _ ⟨f, g, n, hf, hg, hg', rfl⟩ ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', rfl⟩
    exact ⟨f * f₂, g * g₂, n + n₂, isMultiHomog_mul hf hf₂, isMultiHomog_mul hg hg₂,
      by rw [map_mul]; exact mul_ne_zero hg' hg₂', by rw [map_mul, map_mul, div_mul_div_comm]⟩
  add_mem' := by
    rintro _ _ ⟨f, g, n, hf, hg, hg', rfl⟩ ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', rfl⟩
    have h2 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f₂ * g) (n + n₂) := by
      rw [add_comm]; exact isMultiHomog_mul hf₂ hg
    refine ⟨f * g₂ + f₂ * g, g * g₂, n + n₂, isMultiHomog_add (isMultiHomog_mul hf hg₂) h2,
      isMultiHomog_mul hg hg₂, by rw [map_mul]; exact mul_ne_zero hg' hg₂', ?_⟩
    rw [div_add_div _ _ (ne_zero_of hle hg hg') (ne_zero_of hle hg₂ hg₂'), map_add (f := _), map_mul, map_mul, map_mul]
    ring
  algebraMap_mem' r := ⟨C r, 1, 0, isMultiHomog_C r, isMultiHomog_one, by simp, by simp⟩

theorem exists_of_mem {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} {hle : mIdealOver F y ≤ mIdealOver F y'}
    {x : Ω} (hx : x ∈ locR hle) :
    ∃ (f g : MRingOver F ι) (n : K → ℕ),
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n ∧
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g n ∧ aeval y' g ≠ 0 ∧
      x = aeval y f / aeval y g := hx

def sigmaFun {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    (x : locR hle) : K' :=
  aeval y' (exists_of_mem x.2).choose / aeval y' (exists_of_mem x.2).choose_spec.choose

theorem sigmaFun_eq {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    (x : locR hle) {f g : MRingOver F ι} {n : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g n)
    (hg' : aeval y' g ≠ 0) (hx : (x : Ω) = aeval y f / aeval y g) :
    sigmaFun hle x = aeval y' f / aeval y' g := by
  obtain ⟨hf0, hg0, hg0', hx0⟩ := (exists_of_mem x.2).choose_spec.choose_spec.choose_spec
  exact wd hle hf0 hg0 hf hg hg0' hg' (hx0.symm.trans hx)

def sigma {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y') :
    locR hle →ₐ[F] K' where
  toFun := sigmaFun hle
  map_one' := by
    rw [sigmaFun_eq hle 1 isMultiHomog_one isMultiHomog_one (by simp) (by simp)]; simp
  map_zero' := by
    rw [sigmaFun_eq hle 0 (isMultiHomog_C (0 : F)) isMultiHomog_one (by simp) (by simp)]; simp
  map_mul' x x' := by
    obtain ⟨f, g, n, hf, hg, hg', hx⟩ := exists_of_mem x.2
    obtain ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', hx₂⟩ := exists_of_mem x'.2
    rw [sigmaFun_eq hle x hf hg hg' hx, sigmaFun_eq hle x' hf₂ hg₂ hg₂' hx₂,
      sigmaFun_eq hle (x * x') (isMultiHomog_mul hf hf₂) (isMultiHomog_mul hg hg₂)
        (by rw [map_mul]; exact mul_ne_zero hg' hg₂')
        (by rw [Subalgebra.coe_mul, hx, hx₂, map_mul, map_mul, div_mul_div_comm]),
      map_mul, map_mul, div_mul_div_comm]
  map_add' x x' := by
    obtain ⟨f, g, n, hf, hg, hg', hx⟩ := exists_of_mem x.2
    obtain ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', hx₂⟩ := exists_of_mem x'.2
    have h2 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f₂ * g) (n + n₂) := by
      rw [add_comm]; exact isMultiHomog_mul hf₂ hg
    rw [sigmaFun_eq hle x hf hg hg' hx, sigmaFun_eq hle x' hf₂ hg₂ hg₂' hx₂,
      sigmaFun_eq hle (x + x') (isMultiHomog_add (isMultiHomog_mul hf hg₂) h2) (isMultiHomog_mul hg hg₂)
        (by rw [map_mul]; exact mul_ne_zero hg' hg₂')
        (by rw [Subalgebra.coe_add, hx, hx₂, div_add_div _ _ (ne_zero_of hle hg hg') (ne_zero_of hle hg₂ hg₂'),
              map_add, map_mul, map_mul, map_mul]; ring),
      div_add_div _ _ hg' hg₂', map_add, map_mul, map_mul, map_mul]
    ring
  commutes' r := by
    show sigmaFun hle (algebraMap F (locR hle) r) = _
    rw [sigmaFun_eq hle _ (isMultiHomog_C r) isMultiHomog_one (by simp) (by simp)]; simp

theorem sigma_apply {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    (x : locR hle) : sigma hle x = sigmaFun hle x := rfl

theorem frac_spec {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {f g : MRingOver F ι} {n : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g n)
    (hg' : aeval y' g ≠ 0) (x : Ω) (hx : x = aeval y f / aeval y g) :
    ∃ h : x ∈ locR hle, sigma hle ⟨x, h⟩ = aeval y' f / aeval y' g :=
  ⟨⟨f, g, n, hf, hg, hg', hx⟩, (sigma_apply hle _).trans (sigmaFun_eq hle _ hf hg hg' hx)⟩

end ResidueMap


open ResidueMap in
theorem ResidueMap.proof : ResidueMap.Statement := by
  intro F _ K _ ι _ Ω _ _ y K' _ _ y' hle
  classical
  refine ⟨locR hle, sigma hle, ?_, ?_, ?_⟩
  · intro f g n hf hg hg'
    exact frac_spec hle hf hg hg' _ rfl
  · intro k f g m hf hg hg'
    have hg'' : aeval y' (rename (fun i : ι k => (⟨k, i⟩ : Σ k, ι k)) g) ≠ 0 := by
      rwa [aeval_rename_block]
    obtain ⟨h, hσ⟩ := frac_spec hle (isMultiHomog_rename k hf) (isMultiHomog_rename k hg) hg''
      (aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) g)
      (by rw [aeval_rename_block, aeval_rename_block])
    refine ⟨h, ?_⟩
    rw [hσ, aeval_rename_block, aeval_rename_block]
  · intro d hd z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨k, i⟩, rfl⟩ := hx
      obtain ⟨h, hσ⟩ := frac_spec hle (isMultiHomog_X (F := F) k i) (isMultiHomog_X (F := F) k (d k))
        (by rw [aeval_X]; exact hd k) _ (by rw [aeval_X, aeval_X])
      refine ⟨h, ?_⟩
      rw [hσ, aeval_X, aeval_X]
      exact Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩
    | algebraMap r =>
      refine ⟨Subalgebra.algebraMap_mem _ r, ?_⟩
      show sigma hle (algebraMap F (locR hle) r) ∈ _
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | add x x' _ _ ih ih' =>
      obtain ⟨h, hσ⟩ := ih
      obtain ⟨h', hσ'⟩ := ih'
      refine ⟨add_mem h h', ?_⟩
      rw [show (⟨x + x', add_mem h h'⟩ : locR hle) = ⟨x, h⟩ + ⟨x', h'⟩ from rfl, map_add (f := _)]
      exact add_mem hσ hσ'
    | mul x x' _ _ ih ih' =>
      obtain ⟨h, hσ⟩ := ih
      obtain ⟨h', hσ'⟩ := ih'
      refine ⟨mul_mem h h', ?_⟩
      rw [show (⟨x * x', mul_mem h h'⟩ : locR hle) = ⟨x, h⟩ * ⟨x', h'⟩ from rfl, map_mul]
      exact mul_mem hσ hσ'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end
