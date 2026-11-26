module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsVeryAmpleZFinite
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace VeryAmpleZFamily

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ} {h : Fin (r + 1) → Ω}

theorem aeval_mem_pow {I : Chart x} {Q : Submodule (chartRing S x I) Ω} (hQ : ∀ l, h l ∈ Q)
    {f : MvPolynomial (Fin (r + 1)) S} {e : ℕ} (hf : f.IsHomogeneous e) : aeval h f ∈ Q ^ e := by
  have hmon : ∀ (d : Fin (r + 1) →₀ ℕ) (t : Finset (Fin (r + 1))),
      ∏ j ∈ t, h j ^ d j ∈ Q ^ (∑ j ∈ t, d j) := by
    intro d t
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, pow_add]
      exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hQ j) _) ih
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [aeval_monomial]
  have hdeg : ∑ j ∈ d.support, d j = e := by
    have := hf (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have hm := hmon d d.support
  rw [hdeg] at hm
  have := Submodule.smul_mem (Q ^ e)
    (⟨algebraMap S Ω (AddMonoidAlgebra.coeff f d), Subalgebra.algebraMap_mem _ _⟩ : chartRing S x I) hm
  rw [chartRing_smul_def] at this
  exact this


omit [Module S E] [IsScalarTower S Ω E] in
theorem smul_mem_twist_pow (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z : E}
    {q : Ω} (hz : z ∈ (F.twist (H.pow c)).sub I) (hq : q ∈ (H.pow d).sub I) :
    q • z ∈ (F.twist (H.pow (c + d))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => q • z ∈ (F.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨p, hp, y, hy, rfl⟩
    exact Submodule.subset_span ⟨p * q, AmpleTwistLocal.mul_mem_pow H I hp d hq, y, hy, by
      rw [smul_smul, mul_comm]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    rw [Subalgebra.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ a hz

theorem mem_sub_of_mem_secs {H : SubSystem S x Ω} {z : Ω} (hz : z ∈ H.secs) (I : Chart x) : z ∈ H.sub I :=
  (Submodule.restrictScalars_mem S _ _).mp ((Submodule.mem_iInf _).mp hz I)

theorem prod_pow_mem (H : SubSystem S x Ω) (I : Chart x) (hh : ∀ l, h l ∈ H.sub I)
    (T : Finset (Fin (r + 1))) (n : ℕ) : (∏ l ∈ T, h l) ^ n ∈ (H.pow (T.card * n)).sub I := by
  refine AmpleTwistLocal.pow_mem_pow H I ?_ n
  rw [SubSystem.pow_sub, ← AmpleAffineGen.aeval_monoProd (S := S)]
  exact aeval_mem_pow hh (AmpleAffineGen.monoProd_isHomogeneous T)

theorem mem_secsOnZChart (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x)
    (hh : ∀ l, h l ∈ H.sub I) (J : Chart h) (e : E) :
    e ∈ secsOnZChart F H h I J ↔
      ∃ n : ℕ, xProd J ^ n • e ∈ (F.twist (H.pow (J.1.card * n))).sub I := by
  refine ⟨fun he => ?_, fun he => Submodule.subset_span he⟩
  refine Submodule.span_induction (p := fun e _ =>
    ∃ n : ℕ, xProd J ^ n • e ∈ (F.twist (H.pow (J.1.card * n))).sub I) (fun _ h => h) ?_ ?_ ?_ he
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro a b _ _ ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have e1 : xProd J ^ (n + m) • (a + b) =
        xProd J ^ m • (xProd J ^ n • a) + xProd J ^ n • (xProd J ^ m • b) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm m n]
    rw [e1]
    refine Submodule.add_mem _ ?_ ?_
    · have := smul_mem_twist_pow F H I hn (prod_pow_mem H I hh J.1 m)
      rwa [← Nat.mul_add] at this
    · have := smul_mem_twist_pow F H I hm (prod_pow_mem H I hh J.1 n)
      rwa [← Nat.mul_add, Nat.add_comm m n] at this
  · rintro c a _ ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have e1 : xProd J ^ n • c • a =
        (⟨algebraMap S Ω c, Subalgebra.algebraMap_mem _ _⟩ : chartRing S x I) • (xProd J ^ n • a) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul Ω c a, smul_smul, smul_smul, mul_comm]
    rw [e1]
    exact Submodule.smul_mem _ _ hn

theorem exists_mul_eq_monoProd_pow {T : Finset (Fin (r + 1))} {s : Poly S r} (hs : s ∈ monos T) :
    ∃ (k : ℕ) (t : Poly S r), t ∈ monos T ∧ s * t = AmpleAffineGen.monoProd T ^ k := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨1, AmpleAffineGen.monoProd (T.erase i),
      AmpleAffineGen.monoProd_mem_monos (Finset.erase_subset _ _), by
        rw [pow_one, AmpleAffineGen.monoProd, AmpleAffineGen.monoProd,
          Finset.mul_prod_erase _ _ (by exact_mod_cast hi)]⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, t, ht, e⟩ := ha
    obtain ⟨k', t', ht', e'⟩ := hb
    exact ⟨k + k', t * t', mul_mem ht ht', by
      rw [pow_add, ← e, ← e']; ring⟩

theorem exists_mul_xProd_pow_mem (H : SubSystem S x Ω) (I : Chart x) (hh : ∀ l, h l ∈ H.sub I)
    (J : Chart h) {a : Ω} (ha : a ∈ chartRing S h J) :
    ∃ k : ℕ, a * xProd J ^ k ∈ (H.pow (J.1.card * k)).sub I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  obtain ⟨k, t, ht, hst⟩ := exists_mul_eq_monoProd_pow hs
  obtain ⟨d, htd⟩ := monos_isHomogeneous ht
  have hval : aeval h s * aeval h t = xProd J ^ k := by
    rw [← map_mul, hst, map_pow, AmpleAffineGen.aeval_monoProd]; rfl
  have hne : AmpleAffineGen.monoProd (S := S) J.1 ^ k ≠ 0 := by
    intro h0
    have := congrArg (aeval h) h0
    rw [map_pow, AmpleAffineGen.aeval_monoProd, map_zero] at this
    exact pow_ne_zero _ (AmpleAffineGen.xProd_ne_zero J) this
  have hdeg : e + d = J.1.card * k := by
    have h1 := hse.mul htd
    rw [hst] at h1
    exact h1.inj_right ((AmpleAffineGen.monoProd_isHomogeneous J.1).pow k) hne
  refine ⟨k, ?_⟩
  have hs0 : aeval h s ≠ 0 := eval_ne_zero_of_mem_monos J hs
  have e1 : aeval h f / aeval h s * xProd J ^ k = aeval h (f * t) := by
    rw [← hval, map_mul]; field_simp
  rw [e1, SubSystem.pow_sub, ← hdeg]
  exact aeval_mem_pow hh (hf.mul htd)

theorem secsOnZChart_mono (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x)
    (hh : ∀ l, h l ∈ H.sub I) {J J' : Chart h} (hJ : J.1 ⊆ J'.1) {e : E}
    (he : e ∈ secsOnZChart F H h I J) : e ∈ secsOnZChart F H h I J' := by
  classical
  rw [mem_secsOnZChart F H I hh] at he ⊢
  obtain ⟨n, hn⟩ := he
  refine ⟨n, ?_⟩
  have e1 : xProd J' ^ n • e = (∏ l ∈ J'.1 \ J.1, h l) ^ n • (xProd J ^ n • e) := by
    rw [smul_smul, ← mul_pow]
    unfold xProd
    rw [Finset.prod_sdiff hJ]
  rw [e1]
  have := smul_mem_twist_pow F H I hn (prod_pow_mem H I hh (J'.1 \ J.1) n)
  rwa [← Nat.add_mul, Nat.add_comm, Finset.card_sdiff_add_card_eq_card hJ] at this

theorem proof : VeryAmpleZFamily.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hv
  have hh : ∀ I l, h l ∈ H.toSubSystem.sub I := fun I l => mem_sub_of_mem_secs (hv.mem_secs l) I
  have mem : ∀ (J : Chart h) (e : E), e ∈ secsOnZ F.toSubSystem H.toSubSystem h J ↔
      ∀ I, ∃ n : ℕ, xProd J ^ n • e ∈
        (F.toSubSystem.twist (H.toSubSystem.pow (J.1.card * n))).sub I := by
    intro J e
    rw [secsOnZ, Submodule.mem_iInf]
    exact forall_congr' fun I => mem_secsOnZChart F.toSubSystem H.toSubSystem I (hh I) J e
  have smul : ∀ (J : Chart h) (a : chartRing S h J) (e : E),
      e ∈ secsOnZ F.toSubSystem H.toSubSystem h J → (a : Ω) • e ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
    intro J a e he
    rw [mem] at he ⊢
    intro I
    obtain ⟨n, hn⟩ := he I
    obtain ⟨k, hk⟩ := exists_mul_xProd_pow_mem H.toSubSystem I (hh I) J a.2
    refine ⟨n + k, ?_⟩
    have e1 : xProd J ^ (n + k) • (a : Ω) • e = ((a : Ω) * xProd J ^ k) • (xProd J ^ n • e) := by
      rw [smul_smul, smul_smul]; ring_nf
    rw [e1, Nat.mul_add]
    exact smul_mem_twist_pow F.toSubSystem H.toSubSystem I hn hk
  have mono : ∀ J J' : Chart h, J.1 ⊆ J'.1 → ∀ e, e ∈ secsOnZ F.toSubSystem H.toSubSystem h J →
      e ∈ secsOnZ F.toSubSystem H.toSubSystem h J' := by
    intro J J' hJ e he
    rw [secsOnZ, Submodule.mem_iInf] at he ⊢
    exact fun I => secsOnZChart_mono F.toSubSystem H.toSubSystem I (hh I) hJ (he I)
  let sub : ∀ J : Chart h, Submodule (chartRing S h J) E := fun J =>
    { carrier := secsOnZ F.toSubSystem H.toSubSystem h J
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun a e he => smul J a e he }
  refine ⟨{ sub := sub, mono := fun J J' hJ e he => mono J J' hJ e he, mem_iff := ?_ }, fun J => ?_⟩
  · intro J J' hJ y
    constructor
    · intro hy
      change y ∈ secsOnZ F.toSubSystem H.toSubSystem h J' at hy
      rw [mem] at hy
      choose n hn using hy
      obtain ⟨M, hM⟩ := Finite.bddAbove_range n
      have hM' : ∀ I, n I ≤ M := fun I => hM ⟨I, rfl⟩
      refine ⟨⟨AmpleAffineGen.chartRatio J J' ^ M, pow_mem (AmpleAffineGen.chartRatio_mem J J') M⟩, ?_, ?_⟩
      · refine IsUnit.of_mul_eq_one
          ⟨AmpleAffineGen.chartRatio J' J ^ M, pow_mem (AmpleAffineGen.chartRatio_mem J' J) M⟩
          (Subtype.ext ?_)
        change AmpleAffineGen.chartRatio J J' ^ M * AmpleAffineGen.chartRatio J' J ^ M = 1
        rw [← mul_pow, AmpleAffineGen.chartRatio_mul_chartRatio, one_pow]
      · change AmpleAffineGen.chartRatio J J' ^ M • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J
        rw [mem]
        intro I
        refine ⟨J'.1.card * M, ?_⟩
        have hJpos : 0 < J.1.card := Finset.card_pos.mpr J.2.1
        have hnK : n I ≤ J.1.card * M := (hM' I).trans (Nat.le_mul_of_pos_left M hJpos)
        have e1 : xProd J ^ (J'.1.card * M) • (AmpleAffineGen.chartRatio J J' ^ M • y) =
            xProd J' ^ (J.1.card * M - n I) • (xProd J' ^ n I • y) := by
          rw [smul_smul, smul_smul, ← pow_add, Nat.sub_add_cancel hnK, AmpleAffineGen.chartRatio, div_pow,
            ← pow_mul, ← pow_mul, ← mul_div_assoc,
            mul_div_cancel_left₀ _ (pow_ne_zero _ (AmpleAffineGen.xProd_ne_zero J))]
        rw [e1]
        have := smul_mem_twist_pow F.toSubSystem H.toSubSystem I (hn I)
          (prod_pow_mem H.toSubSystem I (hh I) J'.1 (J.1.card * M - n I))
        have e2 : J'.1.card * n I + J'.1.card * (J.1.card * M - n I) = J.1.card * (J'.1.card * M) := by
          rw [← Nat.mul_add, Nat.add_sub_cancel' hnK]; ring
        rw [e2] at this
        exact this
    · rintro ⟨a, ha, hay⟩
      change y ∈ secsOnZ F.toSubSystem H.toSubSystem h J'
      have h1 : (a : Ω) • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J' := mono J J' hJ _ hay
      obtain ⟨u, hu⟩ := ha
      have h2 := smul J' (↑u⁻¹) _ h1
      have hinv : ((↑u⁻¹ : chartRing S h J') : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val u.inv_mul
        rw [hu] at this
        exact this
      rwa [smul_smul, hinv, one_smul] at h2
  · ext e
    exact Iff.rfl

end VeryAmpleZFamily

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace VeryAmpleZTwist

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E]

theorem chart_smul_eq {I : Chart x} (c : chartRing S x I) (z : E) : c • z = (c : Ω) • z := rfl

theorem smul_mem_twist_twist (G : SubSystem S x E) (P Q : SubSystem S x Ω) (I : Chart x) {q : Ω}
    (hq : q ∈ P.sub I) {z : E} (hz : z ∈ (G.twist Q).sub I) : q • z ∈ ((G.twist P).twist Q).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => q • z ∈ ((G.twist P).twist Q).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q', hq', y, hy, rfl⟩
    refine Submodule.subset_span ⟨q', hq', q • y, Submodule.subset_span ⟨q, hq, y, hy, rfl⟩, ?_⟩
    rw [smul_smul, smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b c _ _ hb hc; rw [smul_add]; exact Submodule.add_mem _ hb hc
  · intro c z _ hz
    rw [chart_smul_eq, smul_smul, mul_comm, ← smul_smul, ← chart_smul_eq]
    exact Submodule.smul_mem _ c hz

theorem smul_mem_twist_pow (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {w : Ω}
    (hw : w ∈ (H.pow c).sub I) {z : E} (hz : z ∈ (G.twist (H.pow d)).sub I) :
    w • z ∈ (G.twist (H.pow (d + c))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => w • z ∈ (G.twist (H.pow (d + c))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq c hw, y, hy, ?_⟩
    rw [smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
  · intro c' z _ hz
    rw [chart_smul_eq, smul_smul, mul_comm, ← smul_smul, ← chart_smul_eq]
    exact Submodule.smul_mem _ c' hz

theorem mem_twist_pow_add (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    (hz : z ∈ ((G.twist (H.pow a)).twist (H.pow b)).sub I) : z ∈ (G.twist (H.pow (a + b))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => z ∈ (G.twist (H.pow (a + b))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    exact smul_mem_twist_pow G H I hq hy
  · exact Submodule.zero_mem _
  · intro b e _ _ hb he; exact Submodule.add_mem _ hb he
  · intro c z _ hz; exact Submodule.smul_mem _ c hz

theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.sub I) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => exact one_mem_twistMod_zero I
  | insert l T hl ih =>
    rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    exact Submodule.subset_span ⟨h l, hh l, _, ih, rfl⟩

theorem proof (hFam : VeryAmpleZFamily.Statement.{u, v, w}) : VeryAmpleZTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hH a J
  obtain ⟨F', hF'⟩ := hFam S Ω N x E F H r h hH
  obtain ⟨j, hj⟩ := J.2.1
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hj)
  have hmem : ∀ l I, h l ∈ H.sub I := fun l I => (Submodule.mem_iInf _).mp (hH.mem_secs l) I
  have hpow : ∀ I, h j ^ a ∈ (H.pow a).sub I := fun I => by
    have h1 : h j ∈ (H.pow 1).sub I := by rw [SubSystem.pow_sub, pow_one]; exact hmem j I
    simpa using AmpleTwistLocal.pow_mem_pow H.toSubSystem I h1 a

  have fwd : ∀ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J,
      h j ^ a • y ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J := by
    intro y hy
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    have hyI : y ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J := (Submodule.mem_iInf _).mp hy I
    refine Submodule.span_induction (p := fun y _ =>
      h j ^ a • y ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J) ?_ ?_ ?_ ?_ hyI
    · rintro y ⟨n, hn⟩
      refine Submodule.subset_span ⟨n, ?_⟩
      rw [smul_smul, mul_comm (xProd J ^ n), ← smul_smul]
      exact smul_mem_twist_twist _ _ _ I (hpow I) hn
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
    · intro s e _ he; rw [smul_comm]; exact Submodule.smul_mem _ s he

  have bwd : ∀ e ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J,
      (h j ^ a)⁻¹ • e ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
    classical
    intro e he
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    have heI : e ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J := (Submodule.mem_iInf _).mp he I
    set u := ∏ l ∈ J.1.erase j, h l with hu
    have hxu : xProd J = h j * u := (Finset.mul_prod_erase J.1 h hj).symm
    have hk : J.1.card = (J.1.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    have hua : u ^ a ∈ (H.pow ((J.1.erase j).card * a)).sub I :=
      AmpleTwistLocal.pow_mem_pow H.toSubSystem I (prod_mem_pow H.toSubSystem I (fun l => hmem l I) _) a
    refine Submodule.span_induction (p := fun e _ =>
      (h j ^ a)⁻¹ • e ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J) ?_ ?_ ?_ ?_ heI
    · rintro e ⟨n, hn⟩
      refine Submodule.subset_span ⟨n + a, ?_⟩
      have heq : xProd J ^ (n + a) • (h j ^ a)⁻¹ • e = u ^ a • (xProd J ^ n • e) := by
        rw [smul_smul, smul_smul, hxu]
        congr 1
        field_simp
        ring
      have hdeg : a + J.1.card * n + (J.1.erase j).card * a = J.1.card * (n + a) := by
        rw [hk]; ring
      rw [heq, ← hdeg]
      exact smul_mem_twist_pow _ _ I hua (mem_twist_pow_add _ _ I hn)
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
    · intro s e _ he; rw [smul_comm]; exact Submodule.smul_mem _ s he
  have hq : h j ^ a ∈ twistMod S h (a : ℤ) J := by
    rw [twistMod_eq_span (a : ℤ) J hj, zpow_natCast]
    exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    suffices H1 : ∀ c : chartRing S h J, c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J by
      simpa using H1 1
    refine Submodule.span_induction (p := fun z _ => ∀ c : chartRing S h J,
      c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, y, hy, rfl⟩ c
      rw [twistMod_eq_span (a : ℤ) J hj, Submodule.mem_span_singleton] at hq
      obtain ⟨d, rfl⟩ := hq
      have hy' : y ∈ F'.sub J := by
        have : y ∈ (F'.sub J).restrictScalars S := by rw [hF' J]; exact hy
        exact this
      have hcd : (c * d) • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
        rw [← hF' J]; exact Submodule.smul_mem _ (c * d) hy'
      have heq : c • ((d • h j ^ (a : ℤ)) • y) = h j ^ a • ((c * d) • y) := by
        rw [chart_smul_eq, chart_smul_eq, smul_eq_mul, zpow_natCast, smul_smul, chart_smul_eq (c * d),
          smul_smul]
        congr 1
        push_cast
        ring
      rw [heq]
      exact fwd _ hcd
    · intro c; rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he c; rw [smul_add]; exact Submodule.add_mem _ (hb c) (he c)
    · intro c' e _ he c; rw [smul_smul]; exact he (c * c')
  · intro e he
    have heq : e = h j ^ a • ((h j ^ a)⁻¹ • e) := by
      rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hj0), one_smul]
    rw [Submodule.restrictScalars_mem, heq]
    exact Submodule.subset_span ⟨h j ^ a, by exact_mod_cast hq, _, bwd e he, rfl⟩

end VeryAmpleZTwist

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeFiniteE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section ReadOnCharts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

def chartVal {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n) (I : Cech.Idx (support x) n) : E :=
  coeffE S x E c (locConeE M I.1.1 I.1.2.2 (y ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩))

theorem chartVal_zero {n : ℕ} (I : Cech.Idx (support x) n) :
    chartVal M c (0 : Cech.Cochain (locSys S N M.coneSubE) n) I = 0 := by
  unfold chartVal
  rw [Pi.zero_apply, map_zero, map_zero]

theorem chartVal_add {n : ℕ} (y y' : Cech.Cochain (locSys S N M.coneSubE) n) (I : Cech.Idx (support x) n) :
    chartVal M c (y + y') I = chartVal M c y I + chartVal M c y' I := by
  unfold chartVal
  rw [Pi.add_apply, map_add (f := _), map_add (f := _)]

theorem chartVal_smul {n : ℕ} (a : S) (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (I : Cech.Idx (support x) n) : chartVal M c (a • y) I = a • chartVal M c y I := by
  unfold chartVal
  rw [Pi.smul_apply, LinearMap.map_smul_of_tower, map_smul]

theorem chartVal_mem {n : ℕ} {y : Cech.Cochain (locSys S N M.coneSubE) n}
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) (I : Cech.Idx (support x) n) :
    chartVal M c y I ∈ (M.tildeSys c).sub I.1 := by
  obtain ⟨v, hv, hyv⟩ := locConeE_degLoc M c _ I.1.2.2
    (hy ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ (Set.mem_univ _))
  unfold chartVal
  rw [hyv, coeffE_singleE_same]
  exact hv

theorem chartVal_d {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n) (J : Cech.Idx (support x) (n + 1)) :
    chartVal M c (Cech.d (locSys S N M.coneSubE) locResS n y) J =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • chartVal M c y (Cech.face J j) := by
  refine (congrArg (coeffE S x E c)
    (locConeE_d M y ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩ J.1.2.2)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  rfl

def toTildeC {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) :
    Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n :=
  fun I => ⟨chartVal M c y I, chartVal_mem M c hy I⟩

theorem coe_d_toTildeC {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) (J : Cech.Idx (support x) (n + 1)) :
    ((Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n (toTildeC M c y hy) J : _) : E) =
      chartVal M c (Cech.d (locSys S N M.coneSubE) locResS n y) J := by
  rw [coe_d_sub, chartVal_d]
  rfl

def toTildeCocy (n : ℕ) :
    Cech.cocyDeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) locResS n →ₗ[S]
      LinearMap.ker (Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n) where
  toFun y := ⟨toTildeC M c y.1 y.2.2, LinearMap.mem_ker.mpr (funext fun J => Subtype.ext (by
    rw [coe_d_toTildeC, LinearMap.mem_ker.mp y.2.1, chartVal_zero]
    rfl))⟩
  map_add' y y' := Subtype.ext (funext fun I => Subtype.ext (chartVal_add M c y.1 y'.1 I))
  map_smul' a y := Subtype.ext (funext fun I => Subtype.ext (chartVal_smul M c a y.1 I))

set_option synthInstance.maxHeartbeats 200000 in
def toTildeH (n : ℕ) : cohom M.coneGradedE n c →ₗ[S] (M.tildeSys c).H n :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp (toTildeCocy M c n)) (by
    intro y hy
    rw [Submodule.mem_comap] at hy
    refine LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr ?_)
    cases n with
    | zero =>
      change (y : Cech.Cochain (locSys S N M.coneSubE) 0) ∈ (⊥ : Submodule S _) at hy
      rw [Submodule.mem_bot] at hy
      change toTildeC M c y.1 y.2.2 ∈ (⊥ : Submodule S _)
      rw [Submodule.mem_bot]
      funext I
      apply Subtype.ext
      change chartVal M c (y : Cech.Cochain (locSys S N M.coneSubE) 0) I = 0
      rw [hy, chartVal_zero]
    | succ k =>
      change (y : Cech.Cochain (locSys S N M.coneSubE) (k + 1)) ∈
        (Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) k).map
          (Cech.d (locSys S N M.coneSubE) locResS k) at hy
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
      change toTildeC M c y.1 y.2.2 ∈
        LinearMap.range (Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res k)
      refine ⟨toTildeC M c z hz, funext fun J => Subtype.ext ?_⟩
      rw [coe_d_toTildeC]
      change _ = chartVal M c (y : Cech.Cochain (locSys S N M.coneSubE) (k + 1)) J
      rw [← hzy])

theorem d_liftCochain_any {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (ht : Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n t = 0) :
    Cech.d (locSys S N M.coneSubE) locResS n (liftCochain M c t) = 0 := by
  funext K
  change _ = 0
  by_cases hK : K.1.1 ⊆ support x
  · apply locConeE_injective M K.1.1 hK
    rw [locConeE_d M (liftCochain M c t) K hK, map_zero]
    have h0 := coe_d_sub (M.tildeSys c) t ⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩
    rw [ht] at h0
    calc ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
          ((Cech.face_subset K j).trans hK) (liftCochain M c t (Cech.face K j))
        = ∑ j : K.1.1, Cech.sgn K.1.1 j • singleE S x E c
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (n + 1)) j) : E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [liftCochain_of M c t _ ((Cech.face_subset K j).trans hK)]
          congr 1
          exact locConeE_liftTilde M c _ _ _
      _ = singleE S x E c (∑ j : K.1.1, Cech.sgn K.1.1 j •
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (n + 1)) j) : E)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_zsmul]
      _ = 0 := by
          rw [← h0]
          exact map_zero _
  · have := locModE_subsingleton (S := S) M (Finset.not_subset.mp hK).choose_spec.1
      (by simpa [mem_support] using (Finset.not_subset.mp hK).choose_spec.2)
    exact Subsingleton.elim _ _

theorem chartVal_liftCochain {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (I : Cech.Idx (support x) n) : chartVal M c (liftCochain M c t) I = (t I : E) := by
  have e1 := liftCochain_of M c t ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ I.1.2.2
  have e2 := locConeE_liftTilde M c ⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩ I.1.2.2 (t I)
  unfold chartVal
  rw [e1]
  exact (congrArg (coeffE S x E c) e2).trans (coeffE_singleE_same _ _)

set_option synthInstance.maxHeartbeats 200000 in
theorem toTildeH_surjective (n : ℕ) : Function.Surjective (toTildeH M c n) := by
  intro q
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨Submodule.Quotient.mk ⟨liftCochain M c t.1,
    d_liftCochain_any M c t.1 (LinearMap.mem_ker.mp t.2), liftCochain_mem M c t.1⟩, ?_⟩
  change Submodule.Quotient.mk (toTildeCocy M c n _) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (funext fun I => Subtype.ext (chartVal_liftCochain M c t.1 I))

end ReadOnCharts

theorem TildeFiniteE.proof (h : SerreFinite.Statement.{u, v}) : TildeFiniteE.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M i c
  have : Module.Finite S (cohom M.coneGradedE i c) :=
    h S N M.coneSubE M.coneGradedE M.coneSubE_finite i c
  exact Module.Finite.of_surjective (toTildeH M c i) (toTildeH_surjective M c i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace StepThree.OnW.Gen

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem sub_le_twist_idealSys_of_mem (F : SubSystem S x Ω) {pp : Ideal (Poly S N)} (I : Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) (hX : (X i : Poly S N) ∈ pp) :
    F.sub I ≤ (F.twist (idealSys x pp)).sub I := by
  intro z hz
  have hx : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have h1 : (1 : Ω) ∈ idealMod (x := x) pp I :=
    Submodule.subset_span ⟨X i, X i, 1, hX, X_mem_monos hi, isHomogeneous_X S i, isHomogeneous_X S i, by
      rw [aeval_X, div_self hx]⟩
  exact Submodule.subset_span ⟨1, h1, z, hz, (one_smul Ω z).symm⟩

theorem primeOf_le_zeroIdeal (D : SubSystem S x Ω) (s : Ω) : primeOf (S := S) x ≤ zeroIdeal D s := by
  intro f hf
  rw [← sum_homogeneousComponent f]
  refine Ideal.sum_mem _ fun d _ => Ideal.subset_span ⟨d, homogeneousComponent_isHomogeneous d f, ?_⟩
  intro I δ _
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [(mem_primeOf_of_isHomogeneous x (homogeneousComponent_isHomogeneous d f)).mp
    (homogeneousComponent_mem_primeOf x hf d), zero_mul, mul_zero]


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem homog_of_mem_minimalPrimes (D : SubSystem S x Ω) (s : Ω) {pp : Ideal (Poly S N)}
    (hpp : pp ∈ (zeroIdeal D s).minimalPrimes) :
    ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp := by
  have hJ : (zeroIdeal D s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) S) :=
    Ideal.homogeneous_span _ _ fun f ⟨c, hf, _⟩ => ⟨c, (mem_homogeneousSubmodule c f).mpr hf⟩
  have hcore : (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal.IsPrime :=
    hpp.1.1.homogeneousCore
  have hle : zeroIdeal D s ≤ (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal :=
    hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hpp.1.2)
  have heq : (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal = pp :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
      (hpp.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _))
  have hW : pp.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) S) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  intro p hp d
  have h := hW d hp
  have hc : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) S) p d : Poly S N) =
      homogeneousComponent d p := decomposition.decompose'_apply p d
  rwa [hc] at h

variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}

theorem exists_restrict_powBundle (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (n : ℕ) :
    ∃ r' : Ω → K', RestrictData (M.powBundle n).toSubSystem hxy (M'.powBundle n).toSubSystem r' := by
  induction n with
  | zero => exact RestrictTwist.proof.1 S Ω N x K' y hxy hle 0
  | succ n ih =>
    obtain ⟨r', hr'⟩ := ih
    exact RestrictTwist.proof.2 S Ω N x K' y hxy _ M _ M' r' r hr' h

def twistMulBundle (M : LineBundle S x) (p : ℕ) (m : ℤ) : LineBundle S x :=
  (M.powBundle p).tensorProd (twistBundle S x m)

theorem twistMulBundle_toSubSystem (M : LineBundle S x) (p : ℕ) (m : ℤ) :
    (twistMulBundle M p m).toSubSystem = twistMul M.toSubSystem p m := by
  change (M.powBundle p).toSubSystem.twist (twistSys S x m) = _
  rw [LineBundle.powBundle_toSubSystem]
  rfl

theorem exists_restrict_twistMulBundle (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (p : ℕ) (m : ℤ) :
    ∃ r' : Ω → K', RestrictData (twistMulBundle M p m).toSubSystem hxy
      (twistMulBundle M' p m).toSubSystem r' := by
  obtain ⟨rP, hrP⟩ := exists_restrict_powBundle hxy hle M M' r h p
  obtain ⟨rc, hrc⟩ := RestrictTwist.proof.1 S Ω N x K' y hxy hle m
  exact RestrictTwist.proof.2 S Ω N x K' y hxy _ (twistBundle S x m) _ (twistBundle S y m) rP rc hrP hrc

end Helpers

end StepThree.OnW.Gen


open StepThree.OnW.Gen in
theorem StepThree.OnW.Gen.proof (hRL : RestrLenRestrict.Statement.{u, w})
    (hRG : RestrictGenerated.Statement.{u, w}) : StepThree.OnW.Gen.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  have hpr : pp.IsPrime := hpp.1.1
  have hhom := homog_of_mem_minimalPrimes T.D T.si hpp
  have hle : primeOf (S := k) x ≤ pp := (primeOf_le_zeroIdeal T.D T.si).trans hpp.1.2
  by_cases hrel : ∃ j, (X j : Poly k N) ∉ pp
  swap
  · push Not at hrel
    refine ⟨0, fun b c _ _ I => ?_⟩
    obtain ⟨i, hi⟩ := I.2.1
    exact le_sup_of_le_right (sub_le_twist_idealSys_of_mem _ I hi (hrel i))
  obtain ⟨j, hjp⟩ := hrel
  have hj : x j ≠ 0 := fun h0 => hjp (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := PrimeFiltration.Point.proof k Ω N x pp hpr hhom hle j hj hjp

  have := hcp
  let A := chartRing k x (singleChart hj)
  let Ip : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] Ip.ResidueField := IsScalarTower.toAlgHom k A Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    rw [h0, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := hpy ▸ hle

  obtain ⟨f, e₀, hfJ, hfh, hfq⟩ := StepData.JProper.proof k Ω N x T
  obtain ⟨e, he, hsub⟩ :=
    SubvarDrop.proof k Ω N x T.d pp T.dim hpr hhom hle ⟨j, hjp⟩ ⟨f, hpp.1.2 hfJ, hfq⟩
  have hsubW : IsSubvar (fun i => ψ (ratio hj i)) (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]
    exact ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩

  obtain ⟨M', rM, hM'⟩ := PrimeFiltration.Restrict.proof k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy T.M
  have hRM : RestrictData T.M.toSubSystem hxy M'.toSubSystem rM :=
    ⟨fun I => (hM' I).1, fun I => (hM' I).2.1, fun I => (hM' I).2.2.1, fun I => (hM' I).2.2.2⟩
  have hnef : Nef M'.toSubSystem :=
    NefRestrict.proof RestrictTwist.proof hRL k Ω N x _ _ hxy hxy' T.M M' rM hRM T.nef

  have hts : 0 < T.t - T.s' := by
    have hd : (1 : ℚ) ≤ (T.d : ℚ) + 1 := by
      have := (Nat.cast_nonneg T.d : (0 : ℚ) ≤ T.d); linarith
    have ht : 0 < T.t := by
      by_contra hneg'
      have hneg : T.t ≤ 0 := not_lt.mp hneg'
      have : T.t / ((T.d : ℚ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith [T.s'_pos, T.s'_lt]
    have : T.t / ((T.d : ℚ) + 1) ≤ T.t := div_le_self ht.le hd
    linarith [T.s'_lt]
  obtain ⟨q, m', hq, hm', hva⟩ := hK e he _ N _ M' hsubW hnef (T.t - T.s') hts
  obtain ⟨rr, h, hvb⟩ := hva
  have hqm : (q : ℤ) * T.m = T.p * m' := by
    have : (((q : ℤ) * T.m : ℤ) : ℚ) = ((T.p * m' : ℤ) : ℚ) := by
      push_cast; rw [T.m_eq, hm']; ring
    exact_mod_cast this

  have hBgen : (twistMul M'.toSubSystem q m').Generated := fun I => le_antisymm
    (Submodule.span_le.mpr fun z hz => KThm.mem_sub_of_mem_secs hz I)
    (by rw [← hvb.generates I]; exact Submodule.span_mono (Set.range_subset_iff.mpr hvb.mem_secs))

  have hv : ∀ b₂ : ℕ, ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c →
      (((twistMul M'.toSubSystem T.p T.m).pow b₂).twist
        (twistSys k (fun i => ψ (ratio hj i)) c)).Generated := by
    intro b₂
    obtain ⟨c₀, hc₀⟩ := Generated.proof Extension.proof k _ N _ ((twistMulBundle M' T.p T.m).powBundle b₂)
    refine ⟨c₀, fun c hc => ?_⟩
    have hs := hc₀ c hc
    rwa [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem] at hs
  choose cv hcv using hv
  refine ⟨∑ b₂ ∈ Finset.range q, |cv b₂|, fun b c _ hc I => ?_⟩

  obtain ⟨rL, hrL⟩ := exists_restrict_twistMulBundle hxy hxy' T.M M' rM hRM T.p T.m
  obtain ⟨rb, hrb⟩ := exists_restrict_powBundle hxy hxy' _ _ rL hrL b
  obtain ⟨rc, hrc⟩ := RestrictTwist.proof.1 k Ω N x _ _ hxy hxy' c
  obtain ⟨r'', hr''⟩ := RestrictTwist.proof.2 k Ω N x _ _ hxy _ (twistBundle k x c) _
    (twistBundle k (fun i => ψ (ratio hj i)) c) rb rc hrb hrc
  have hQ : ((twistMulBundle T.M T.p T.m).powBundle b).toSubSystem.twist (twistSys k x c) =
      (T.L.pow b).twist (twistSys k x c) := by
    rw [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem]
    rfl
  have hlt : b % q < q := Nat.mod_lt b (by omega)
  have hcb : cv (b % q) ≤ c :=
    le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (f := fun b₂ => |cv b₂|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)) hc)
  have hW : (twistMul M'.toSubSystem T.p T.m).pow b = ((twistMul M'.toSubSystem T.p T.m).pow (b % q)).twist
      ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))) := by
    rw [← TwistAlg.proof k _ N _ M'.toSubSystem T.p q T.m m' (b / q) (b % q) hqm, Nat.div_add_mod b q]
  have hgen : (((twistMulBundle M' T.p T.m).powBundle b).tensorProd
      (twistBundle k (fun i => ψ (ratio hj i)) c)).toSubSystem.Generated := by
    change (((twistMulBundle M' T.p T.m).powBundle b).toSubSystem.twist
      (twistSys k (fun i => ψ (ratio hj i)) c)).Generated
    rw [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem, hW, SubSystem.twist_assoc,
      SubSystem.twist_comm ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))), ← SubSystem.twist_assoc]
    exact KThm.generated_twist (hcv _ c hcb) (KThm.generated_pow hBgen _)
  have key := hRG k Ω N x _ _ hxy pp hle hpy (((twistMulBundle T.M T.p T.m).powBundle b).tensorProd
    (twistBundle k x c))
    (((twistMulBundle M' T.p T.m).powBundle b).tensorProd (twistBundle k (fun i => ψ (ratio hj i)) c)) r'' hr''
    hgen I
  have hQ' : (((twistMulBundle T.M T.p T.m).powBundle b).tensorProd (twistBundle k x c)).toSubSystem =
      (T.L.pow b).twist (twistSys k x c) := hQ
  rw [hQ'] at key
  exact key

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

def ResidueMap.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
    mIdealOver F y ≤ mIdealOver F y' →
    ∃ (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
      (∀ (f g : MRingOver F ι) (n : K → ℕ),
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n →
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g n → aeval y' g ≠ 0 →
        ∃ h : aeval y f / aeval y g ∈ R, σ ⟨_, h⟩ = aeval y' f / aeval y' g) ∧
      (∀ (k : K) (f g : MvPolynomial (ι k) F) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m →
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) g ≠ 0 →
        ∃ h : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) g ∈ R,
          σ ⟨_, h⟩ = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) g) ∧
      (∀ d : ∀ k, ι k, (∀ k, y' ⟨k, d k⟩ ≠ 0) → ∀ z ∈ chartRingOver F y d,
        ∃ h : z ∈ R, σ ⟨z, h⟩ ∈ chartRingOver F y' d)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

def ResidueGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
    mIdealOver F y ≤ mIdealOver F y' →
    ∀ (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
      (∀ (f g : MRingOver F ι) (n : K → ℕ),
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n →
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g n → aeval y' g ≠ 0 →
        ∃ h : aeval y f / aeval y g ∈ R, σ ⟨_, h⟩ = aeval y' f / aeval y' g) →
      (∀ d : ∀ k, ι k, (∀ k, y' ⟨k, d k⟩ ≠ 0) → ∀ z ∈ chartRingOver F y d,
        ∃ h : z ∈ R, σ ⟨z, h⟩ ∈ chartRingOver F y' d) →
    ∀ β : K → ℤ, IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y β → ∀ d₀ : ∀ k, ι k, (∀ k, y' ⟨k, d₀ k⟩ ≠ 0) →
      ∃ ρ : Ω → K',
        (∀ h ∈ secOver F y β, ∃ hh : h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k) ∈ R,
          σ ⟨_, hh⟩ = ρ h * ∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) ∧
        ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
          Submodule.span (chartRingOver F y' c) (ρ '' (secOver F y β : Set Ω)) =
            Submodule.span (chartRingOver F y' c) {(∏ k, y' ⟨k, c k⟩ ^ (-β k))⁻¹}

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
