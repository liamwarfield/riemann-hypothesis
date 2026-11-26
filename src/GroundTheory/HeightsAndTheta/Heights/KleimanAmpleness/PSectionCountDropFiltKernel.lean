module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltKernel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionCount.Drop.Filt.Kernel

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_secs_iff' {F : SubSystem S x Ω} {y : Ω} : y ∈ F.secs ↔ ∀ I, y ∈ F.sub I := by
  simp [SubSystem.secs, Submodule.mem_iInf]

def ratioPow (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (j : Fin (N + 1)) (b : ℕ) :
    chartRing S x I :=
  ⟨x j ^ b / x i ^ b, X j ^ b, X i ^ b, b, pow_mem (X_mem_monos hi) b, isHomogeneous_X_pow _ _,
    isHomogeneous_X_pow _ _, by simp⟩

theorem aeval_div_mem_chartRing (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (f : Poly S N) :
    aeval (fun l => x l / x i) f ∈ chartRing S x I := by
  have h : (aeval (fun l => x l / x i) : Poly S N →ₐ[S] Ω).range ≤ chartRing S x I := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X _ _, isHomogeneous_X _ _, by simp⟩
  exact h ⟨f, rfl⟩

theorem idealMod_le (j : Fin (N + 1)) (b : ℕ) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    idealMod (primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b)) I ≤
      Submodule.span (chartRing S x I) {x j ^ b / x i ^ b} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set M := Submodule.span (chartRing S x I) {x j ^ b / x i ^ b}
  let K : Ideal (Poly S N) :=
    { carrier := {f | aeval (fun l => x l / x i) f ∈ M}
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at *; exact M.add_mem hf hg
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact M.zero_mem
      smul_mem' := fun r f hf => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        exact M.smul_mem ⟨_, aeval_div_mem_chartRing I hi r⟩ hf }
  have hK : primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b) ≤ K := by
    refine sup_le (fun f hf => ?_) (Ideal.span_le.mpr ?_)
    · change aeval (fun l => x l / x i) f ∈ M
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_homogeneousComponent f, map_sum]
      convert M.zero_mem
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [aeval_div_of_isHomogeneous (homogeneousComponent_isHomogeneous d f) i,
        (mem_primeOf_of_isHomogeneous x (homogeneousComponent_isHomogeneous d f)).mp
          (homogeneousComponent_mem_primeOf x hf d), zero_div]
    · rintro g ⟨c, hg, hz⟩
      have hδ : x i ^ b ∈ (twistSys S x (b : ℤ)).sub I := by
        change x i ^ b ∈ twistMod S x (b : ℤ) I
        rw [twistMod_eq_span _ I hi, zpow_natCast]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨o, ho, he⟩ := hz I _ hδ
      rw [twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton] at ho
      obtain ⟨a, rfl⟩ := ho
      change aeval (fun l => x l / x i) g ∈ M
      rw [aeval_div_of_isHomogeneous hg i, Submodule.mem_span_singleton]
      refine ⟨a, ?_⟩
      rw [chartRing_smul_def] at he ⊢
      field_simp
      linear_combination -he
  rw [idealMod, Submodule.span_le]
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hm : aeval (fun l => x l / x i) f ∈ M := hK hf
  rw [aeval_div_of_isHomogeneous hfe i] at hm
  have h := M.smul_mem (⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow _ _, hse,
    by simp⟩ : chartRing S x I) hm
  rw [chartRing_smul_def] at h
  rw [SetLike.mem_coe]
  convert h using 1
  change _ = x i ^ e / aeval x s * (aeval x f / x i ^ e)
  have : x i ^ e ≠ 0 := pow_ne_zero _ hxi
  field_simp

theorem proof : SectionCount.Drop.Filt.Kernel.Statement.{u, w} := by
  intro S _ Ω _ _ N x j b F hj
  have hjb : x j ^ b ≠ 0 := pow_ne_zero _ hj
  constructor
  · intro t ht
    refine mem_secs_iff'.mpr fun I => ?_
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hI := mem_secs_iff'.mp ht I
    rw [SubSystem.twist_sub_eq_mul_of_line] at hI
    refine Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)
    · change q ∈ twistMod S x (-(b : ℤ)) I at hq
      rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨a, rfl⟩ := hq
      have h := (F.sub I).smul_mem (a * ratioPow I hi j b) hy
      rw [chartRing_smul_def] at h ⊢
      convert h using 1
      simp only [ratioPow, Subalgebra.coe_mul, zpow_neg, zpow_natCast]
      field_simp
    · rw [mul_add]; exact (F.sub I).add_mem hu hv
  · intro s hs
    refine ⟨(x j ^ b)⁻¹ * s, mem_secs_iff'.mpr fun I => ?_, by field_simp⟩
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hI := mem_secs_iff'.mp hs I
    rw [SubSystem.twist_sub_eq_mul_of_line] at hI
    rw [SubSystem.twist_sub_eq_mul_of_line]
    refine Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (idealMod_le j b I hi hq)
      have hq' : (a : Ω) * x i ^ (-(b : ℤ)) ∈ (twistSys S x (-(b : ℤ))).sub I := by
        change _ ∈ twistMod S x (-(b : ℤ)) I
        rw [twistMod_eq_span _ I hi]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
      convert Submodule.mul_mem_mul hq' hy using 1
      rw [chartRing_smul_def]
      simp only [zpow_neg, zpow_natCast]
      field_simp
    · rw [mul_add]; exact add_mem hu hv

end SectionCount.Drop.Filt.Kernel

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial
open scoped Pointwise

noncomputable section

universe u w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

theorem exists_mul_eq_prod_pow {J : Finset (Fin (N + 1))} {s : Poly k N} (hs : s ∈ monos J) :
    ∃ (t : Poly k N) (m d : ℕ), t.IsHomogeneous d ∧ s * t = (∏ i ∈ J, X i) ^ m := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨∏ i' ∈ J.erase i, X i', 1, ∑ _i' ∈ J.erase i, 1,
      IsHomogeneous.prod _ _ _ fun i' _ => isHomogeneous_X k i', ?_⟩
    rw [pow_one, Finset.mul_prod_erase J (fun i' => (X i' : Poly k N)) (Finset.mem_coe.mp hi)]
  | one => exact ⟨1, 0, 0, isHomogeneous_one _ _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨t₁, m₁, d₁, ht₁, h₁⟩ := ha
    obtain ⟨t₂, m₂, d₂, ht₂, h₂⟩ := hb
    exact ⟨t₁ * t₂, m₁ + m₂, d₁ + d₂, ht₁.mul ht₂, by rw [pow_add, ← h₁, ← h₂]; ring⟩

theorem exists_mem_chartRing_mul_pow (I J : Chart x) {c : Ω} (hc : c ∈ chartRing k x J) :
    ∃ (c' : Ω) (m : ℕ), c' ∈ chartRing k x I ∧
      c = c' * (xProd I ^ J.1.card / xProd J ^ I.1.card) ^ m := by
  classical
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  obtain ⟨t, m, d, ht, hst⟩ := exists_mul_eq_prod_pow (k := k) hs
  have hs0 := eval_ne_zero_of_mem_monos J hs
  have hJ0 : xProd J ≠ 0 := xProd_ne_zero J
  have hI0 : xProd I ≠ 0 := xProd_ne_zero I
  have hevJ : aeval x (∏ i ∈ J.1, (X i : Poly k N)) = xProd J := by simp [xProd, map_prod]
  have hevI : aeval x (∏ i ∈ I.1, (X i : Poly k N)) = xProd I := by simp [xProd, map_prod]
  have hst' : aeval x s * aeval x t = xProd J ^ m := by rw [← map_mul, hst, map_pow, hevJ]
  have ht0 : aeval x t ≠ 0 := right_ne_zero_of_mul (hst' ▸ pow_ne_zero m hJ0)
  have hpJ : (∏ i ∈ J.1, (X i : Poly k N)).IsHomogeneous J.1.card := by
    simpa using IsHomogeneous.prod J.1 (fun i => (X i : Poly k N)) (fun _ => 1)
      fun i _ => isHomogeneous_X k i
  have hpI : (∏ i ∈ I.1, (X i : Poly k N)).IsHomogeneous I.1.card := by
    simpa using IsHomogeneous.prod I.1 (fun i => (X i : Poly k N)) (fun _ => 1)
      fun i _ => isHomogeneous_X k i
  have hdeg : e + d = J.1.card * m := by
    have h2 : (s * t).IsHomogeneous (J.1.card * m) := by rw [hst]; exact hpJ.pow m
    have hne : s * t ≠ 0 := by
      rw [hst]
      exact pow_ne_zero _ fun h0 => hJ0 (by rw [← hevJ, h0, map_zero])
    exact (hse.mul ht).inj_right h2 hne
  obtain ⟨i', hi'⟩ : ∃ i', I.1.card = i' + 1 :=
    ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  refine ⟨aeval x (f * t * (∏ i ∈ J.1, X i) ^ (m * i')) /
      aeval x ((∏ i ∈ I.1, X i) ^ (m * J.1.card)), m,
    ⟨f * t * (∏ i ∈ J.1, X i) ^ (m * i'), (∏ i ∈ I.1, X i) ^ (m * J.1.card),
      I.1.card * (m * J.1.card),
      pow_mem (Submonoid.prod_mem _ fun i hi => X_mem_monos hi) _, ?_, hpI.pow _, rfl⟩, ?_⟩
  · have h3 := (hf.mul ht).mul (hpJ.pow (m * i'))
    convert h3 using 1
    rw [hdeg, hi']
    ring
  · have key : aeval x f / aeval x s = aeval x f * aeval x t / xProd J ^ m := by
      rw [← hst', mul_div_mul_right _ _ ht0]
    rw [key]
    simp only [map_mul, map_pow, hevJ, hevI]
    rw [hi', div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm,
      div_eq_div_iff (pow_ne_zero _ hJ0) (mul_ne_zero (pow_ne_zero _ hI0) (pow_ne_zero _ hJ0))]
    ring

theorem ampleChart_mul {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z₁ z₂ : Ω}
    (h₁ : z₁ ∈ ampleChart H m hh I) (h₂ : z₂ ∈ ampleChart H m hh I) :
    z₁ * z₂ ∈ ampleChart H m hh I := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  refine ⟨n₁ + n₂, ?_⟩
  rw [SubSystem.pow_sub_eq_pow] at hn₁ hn₂ ⊢
  rw [mul_add, pow_add]
  have h3 := Submodule.mul_mem_mul hn₁ hn₂
  convert h3 using 1
  ring

theorem mem_ampleChart_of_mem_chartRing {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x}
    {c : Ω} (hc : c ∈ chartRing k x I) : c ∈ ampleChart H m hh I :=
  ⟨0, by
    rw [pow_zero, mul_one, mul_zero, SubSystem.pow_sub_eq_pow, pow_zero]
    exact Submodule.mem_one.mpr ⟨⟨c, hc⟩, rfl⟩⟩

theorem ampleChart_pow {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z : Ω}
    (hz : z ∈ ampleChart H m hh I) (n : ℕ) : z ^ n ∈ ampleChart H m hh I := by
  induction n with
  | zero => rw [pow_zero]; exact mem_ampleChart_of_mem_chartRing (one_mem _)
  | succ n ih => rw [pow_succ]; exact ampleChart_mul ih hz

theorem exists_pow_mul_mem_ampleRing {L : SubSystem k x Ω} {hl b c : Ω} {J : Chart x}
    (hb : b ∈ ampleRing L 1 hl)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart L 1 hl I)
    (hc : c ∈ chartRing k x J) : ∃ E : ℕ, b ^ E * c ∈ ampleRing L 1 hl := by
  classical
  have hI : ∀ I : Chart x, ∃ E₀ : ℕ, ∀ E, E₀ ≤ E → b ^ E * c ∈ ampleChart L 1 hl I := by
    intro I
    obtain ⟨e, he⟩ := hbJ I
    obtain ⟨c', m, hc', hcc⟩ := exists_mem_chartRing_mul_pow I J hc
    have hbI : b ∈ ampleChart L 1 hl I := Set.mem_iInter.mp hb I
    refine ⟨e * m, fun E hE => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hE
    have h4 : b ^ (e * m + d) * c =
        b ^ d * (c' * (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ m) := by
      rw [hcc]; ring
    rw [h4]
    exact ampleChart_mul (ampleChart_pow hbI d)
      (ampleChart_mul (mem_ampleChart_of_mem_chartRing hc') (ampleChart_pow he m))
  choose E₀ hE₀ using hI
  exact ⟨∑ I, E₀ I, Set.mem_iInter.mpr fun I =>
    hE₀ I _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I))⟩

variable {L G : SubSystem k x Ω} {r₁ s₁ : ℕ} {h : Fin (r₁ + 1) → Ω} {g : Fin (s₁ + 1) → Ω}

end Lemmas

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ChartIdeal

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

abbrev idealChart (J : Ideal (Poly k N)) (I : Chart x) : Ideal (chartRing k x I) :=
  (idealMod (x := x) J I).comap (Algebra.linearMap (chartRing k x I) Ω)

theorem idealMod_le_range (J : Ideal (Poly k N)) (I : Chart x) :
    idealMod (x := x) J I ≤ LinearMap.range (Algebra.linearMap (chartRing k x I) Ω) := by
  rw [idealMod, Submodule.span_le]
  rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
  exact ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩

theorem idealMod_mono {J J' : Ideal (Poly k N)} (h : J ≤ J') (I : Chart x) :
    idealMod (x := x) J I ≤ idealMod (x := x) J' I := by
  refine Submodule.span_mono ?_
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  exact ⟨f, s, e, h hf, hs, hfe, hse, rfl⟩

theorem idealMod_mul_le (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealMod (x := x) J I * idealMod (x := x) J' I ≤ idealMod (x := x) (J * J') I := by
  rw [idealMod, idealMod, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨f, s, e, hf, hs, hfe, hse, rfl⟩, _, ⟨f', s', e', hf', hs', hfe', hse', rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨f * f', s * s', e + e', Ideal.mul_mem_mul hf hf', mul_mem hs hs',
    hfe.mul hfe', hse.mul hse', ?_⟩
  simp only [map_mul, div_mul_div_comm]

theorem idealChart_mul_le (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealChart J I * idealChart J' I ≤ idealChart (x := x) (J * J') I :=
  Ideal.mul_le.mpr fun a ha b hb => by
    have := idealMod_mul_le (x := x) J J' I (Submodule.mul_mem_mul ha hb)
    simpa using this

theorem idealChart_top (I : Chart x) : idealChart (x := x) (⊤ : Ideal (Poly k N)) I = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  refine Submodule.subset_span ⟨1, 1, 0, Submodule.mem_top, one_mem _, isHomogeneous_one _ _,
    isHomogeneous_one _ _, ?_⟩
  simp

theorem idealChart_prod_le {ι : Type*} (s : Finset ι) (P : ι → Ideal (Poly k N)) (I : Chart x) :
    ∏ i ∈ s, idealChart (P i) I ≤ idealChart (x := x) (∏ i ∈ s, P i) I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Ideal.one_eq_top, idealChart_top, le_refl]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (Ideal.mul_mono_right ih).trans (idealChart_mul_le _ _ I)

theorem idealChart_pow_le (P : Ideal (Poly k N)) (I : Chart x) (n : ℕ) :
    idealChart P I ^ n ≤ idealChart (x := x) (P ^ n) I := by
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top, idealChart_top, le_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono_left ih).trans (idealChart_mul_le _ _ I)

theorem twist_idealSys_le (F : SubSystem k x Ω) (pp : Ideal (Poly k N)) (I : Chart x) :
    (F.twist (idealSys x pp)).sub I ≤ idealChart pp I • F.sub I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨q, hq, y, hy, rfl⟩
  obtain ⟨a, rfl⟩ := idealMod_le_range pp I hq
  exact Submodule.smul_mem_smul (show a ∈ idealChart pp I from hq) hy

end ChartIdeal

section Algebra

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

theorem le_sup_mul_smul {G F : Submodule A M} {P Q : Ideal A} (hP : F ≤ G ⊔ P • F)
    (hQ : F ≤ G ⊔ Q • F) : F ≤ G ⊔ (P * Q) • F := by
  calc F ≤ G ⊔ P • F := hP
    _ ≤ G ⊔ P • (G ⊔ Q • F) := sup_le_sup_left (Submodule.smul_mono le_rfl hQ) _
    _ ≤ G ⊔ (P * Q) • F := by
      rw [Submodule.smul_sup, Submodule.mul_smul, ← sup_assoc]
      exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _

theorem le_sup_prod_smul {ι : Type*} {G F : Submodule A M} (s : Finset ι) (P : ι → Ideal A)
    (h : ∀ i ∈ s, F ≤ G ⊔ P i • F) : F ≤ G ⊔ (∏ i ∈ s, P i) • F := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact le_sup_mul_smul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem le_sup_pow_smul {G F : Submodule A M} {P : Ideal A} (h : F ≤ G ⊔ P • F) (n : ℕ) :
    F ≤ G ⊔ (P ^ n) • F := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
  | succ n ih => rw [pow_succ]; exact le_sup_mul_smul ih h

end Algebra

theorem StepThree.proof (hAway : StepThree.Away.Statement.{u, w})
    (hOnW : StepThree.OnW.Statement.{u, w}) : StepThree.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK
  classical
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly k N) T.J
  choose! c₀ hc₀ using hOnW k Ω N x T hK
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg T.J (IsNoetherian.noetherian _)
  set s := hfin.toFinset
  refine ⟨∑ p ∈ s, |c₀ p|, fun b hb I => ?_⟩
  have hc : 0 ≤ ∑ p ∈ s, |c₀ p| := Finset.sum_nonneg fun p _ => abs_nonneg _
  set F := (T.L.pow b).twist (twistSys k x (∑ p ∈ s, |c₀ p|))
  set G := Submodule.span (chartRing k x I) (F.secs : Set Ω)
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) ?_
  · exact (Submodule.mem_iInf _).mp hz I
  have h1 : ∀ p ∈ s, F.sub I ≤ G ⊔ idealChart p I • F.sub I := fun p hp => by
    have hp' := hfin.mem_toFinset.mp hp
    refine (hc₀ p hp' b _ hb ?_ I).trans (sup_le_sup_left (twist_idealSys_le F p I) _)
    exact (le_abs_self _).trans (Finset.single_le_sum (fun q _ => abs_nonneg (c₀ q)) hp)
  have h2 := le_sup_pow_smul (le_sup_prod_smul s _ h1) (n * b)
  have hrad : ∏ p ∈ s, p ≤ T.J.radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact le_sInf fun q hq => Ideal.prod_le_inf.trans (Finset.inf_le (hfin.mem_toFinset.mpr hq))
  have h3 : (∏ p ∈ s, idealChart p I) ^ (n * b) ≤ idealChart T.J I ^ b := by
    rw [pow_mul]
    refine Ideal.pow_right_mono ?_ b
    refine (Ideal.pow_right_mono (idealChart_prod_le s (fun p => p) I) n).trans
      ((idealChart_pow_le _ I n).trans ?_)
    exact Submodule.comap_mono (idealMod_mono ((Ideal.pow_right_mono hrad n).trans hn) I)
  have h4 := hAway k Ω N x T b _ hc I
  exact h2.trans (sup_le le_rfl ((Submodule.smul_mono_left h3).trans h4))

end

end GroundTheory.Heights₂.Heights.Kleiman
end
