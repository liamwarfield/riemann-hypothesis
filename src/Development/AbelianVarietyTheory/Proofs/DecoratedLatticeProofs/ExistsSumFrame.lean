module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealHermitianSelfDualOfLocalGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealHermitianSelfDualOfLocalGenerator
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FinPl.SelfDualIdeal

variable {D : D7}
open GlobalTheory.FinPlLoc

theorem alg₁ {R : Type} [CommRing R] {u u' w w' e : R} (hU : u' * u = 1) (hC : w' * w = 1) (he : e * e = e)
    (c d h : R) : e * (c * d * h) = u * w * h * (u' * (e * d) * (w' * (e * c))) := by
  calc _ = (u' * u) * (w' * w) * (e * e) * (c * d * h) := by rw [hU, hC, he, one_mul, one_mul]
    _ = _ := by ring

theorem alg₂ {R : Type} [CommRing R] {u u' : R} (hU : u' * u = 1) (w e d h : R) :
    u * w * h * (u' * (e * d)) = d * h * (w * e) := by
  calc _ = (u' * u) * (d * h * (w * e)) := by ring
    _ = _ := by rw [hU, one_mul]

theorem alg₃ {R : Type} [CommRing R] {u u' e : R} (hU : u' * u = 1) (he : e * e = e) (d y : R) :
    e * (d * y) = u' * (e * d) * (y * (u * e)) := by
  calc _ = (u' * u) * (e * e) * (d * y) := by rw [hU, he, one_mul]
    _ = _ := by ring

theorem intAt_mul {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by
    rw [RingHom.map_mul (finPart D) a b]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem cA_mem_intAt {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) := by
  refine ⟨?_, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩
  have h := congrArg (cA D) ((mem_idAt_iff _ a).1 ha.1)
  rw [RingHom.map_mul (cA D), cA_idem] at h
  exact (mem_idAt_iff _ _).2 h

theorem idem_mul_incA (P : Pl D → Prop) (y : D.host.E) :
    idem D P * incA D y = pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] y := by
  rw [mul_comm, idem, GlobalTheory.IdVGen.incA_mul_tmul, mul_one]

theorem idem_mul_incA_mem {𝔞 : FI D} {c : D.host.E} (hc : c ∈ 𝔞) (v : Pl D) : idem D (· = v) * incA D c ∈ idV 𝔞 v :=
  AddSubgroup.subset_closure ⟨ePl D (· = v), ePl_int _, fun w hw => by rw [evalV_ePl, if_neg hw], c, hc,
    idem_mul_incA _ c⟩

theorem mul_incA_mem {v : Pl D} {𝔞 : FI D} {y : D.host.E}
    (hy : ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y * c) {s : AE D} (hs : s ∈ idV 𝔞 v) :
    incA D y * s ∈ intAt D (· = v) := by
  induction hs using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hy c hc
    rw [GlobalTheory.IdVGen.incA_mul_tmul, ← hb]
    exact GlobalTheory.IdVGen.gen_mem_intAt hα h0 b
  | zero => rw [mul_zero]; exact GlobalTheory.IdVGen.intAt_zero' v
  | add a b _ _ ha hb => rw [mul_add]; exact GlobalTheory.IdVGen.intAt_add' ha hb
  | neg a _ ha => rw [mul_neg]; exact GlobalTheory.IdVGen.intAt_neg' ha

theorem mul_cA_mem {v : Pl D} {𝔞 : FI D} {y : D.host.E}
    (hy : ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y * star c) {s : AE D} (hs : s ∈ idV 𝔞 v) :
    incA D y * cA D s ∈ intAt D (· = v) := by
  induction hs using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hy c hc
    have e : cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star c := rfl
    rw [e, GlobalTheory.IdVGen.incA_mul_tmul, ← hb]
    exact GlobalTheory.IdVGen.gen_mem_intAt hα h0 b
  | zero => rw [RingHom.map_zero, mul_zero]; exact GlobalTheory.IdVGen.intAt_zero' v
  | add a b _ _ ha hb => rw [RingHom.map_add (f := _), mul_add]; exact GlobalTheory.IdVGen.intAt_add' ha hb
  | neg a _ ha => rw [RingHom.map_neg, mul_neg]; exact GlobalTheory.IdVGen.intAt_neg' ha

theorem exists_int_mul (y : D.host.E) : ∃ t : 𝓞 D.host.F, t ≠ 0 ∧ ∃ b : 𝓞 D.host.E,
    (b : D.host.E) = algebraMap D.host.F D.host.E (t : D.host.F) * y := by
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) (Rₘ := ℚ) y
    (Algebra.IsIntegral.isIntegral y)
  refine ⟨((m : ℤ) : 𝓞 D.host.F), Int.cast_ne_zero.2 (nonZeroDivisors.coe_ne_zero m), ⟨m • y, hm⟩, ?_⟩
  change (m : ℤ) • y = _
  simp [zsmul_eq_mul]

theorem one_eq_sum (T : Finset (Pl D)) :
    (1 : Af D.host.F) = ∑ v ∈ T, ePl D (· = v) + ePl D (· ∉ T) := by
  classical
  have key : ∀ w, evalV D.host.F w (1 : Af D.host.F) =
      evalV D.host.F w (∑ v ∈ T, ePl D (· = v) + ePl D (· ∉ T)) := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_one, map_add (f := _), map_sum]
    simp only [evalV_ePl]
    by_cases hw : w ∈ T <;> simp [hw]
  exact RestrictedProduct.ext _ _ fun w => key w

theorem exists_integer_of_forall (y : D.host.E) (h : ∀ v : Pl D, idem D (· = v) * incA D y ∈ intAt D (· = v)) :
    ∃ b : 𝓞 D.host.E, (b : D.host.E) = y := by
  classical
  obtain ⟨t, ht0, b, hb⟩ := exists_int_mul y
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hfin := Ideal.finite_factors (I := Ideal.span {t}) (by simpa using ht0)
  have h1 : (1 : Af D.host.F) ⊗ₜ[D.host.F] y ∈ intAE D := by
    rw [one_eq_sum hfin.toFinset, TensorProduct.add_tmul, TensorProduct.sum_tmul]
    refine add_mem (sum_mem fun v _ => ?_) ?_
    · have := (h v).2
      rwa [idem_mul_incA, finPart_pair] at this
    · refine AddSubgroup.subset_closure ⟨(t : D.host.F)⁻¹ • ePl D (· ∉ hfin.toFinset), fun w => ?_, b, ?_⟩
      · rw [map_smul, evalV_ePl]
        by_cases hw : w ∈ hfin.toFinset
        · rw [if_neg (not_not.2 hw), smul_zero]; exact zero_mem _
        · rw [if_pos hw, Algebra.smul_def, mul_one]
          refine GlobalTheory.IdVGen.inv_mem_integers fun hm => hw ?_
          rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
          exact hm
      · rw [hb, TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hF, one_smul]
  have h2 : intAE D ≤ GlobalTheory.AdLat.hat1 D.host.F ((1 : FI D) : Set D.host.E) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, y, rfl⟩
    exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral D.host.F ha ((FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩)
  exact (FractionalIdeal.mem_one_iff _).1 ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff D.host.F 1 y).1 (h2 h1))

theorem idem_ne_zero (v : Pl D) : idem D (· = v) ≠ 0 := by
  intro h
  have := compAt_idem (· = v) v
  rw [h, if_pos rfl, RingHom.map_zero] at this
  exact zero_ne_one this

theorem selfDual_of_local : ∀ (D : D7) (h : D.host.E) (𝔞 : FI D) (u : (AE D)ˣ), (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ idV 𝔞 x ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) → (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (u : AE D) * cA D (u : AE D) * incA D h * a ∈ intAt D (· = x)) → ∀ d : D.host.E, d ∈ 𝔞 ↔ ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * h := by
  intro D h 𝔞 u H1 H2 d
  have hU : ((u⁻¹ : (AE D)ˣ) : AE D) * (u : AE D) = 1 := u.inv_mul
  have hC : cA D ((u⁻¹ : (AE D)ˣ) : AE D) * cA D (u : AE D) = 1 := by
    rw [← RingHom.map_mul (cA D), hU, RingHom.map_one]
  generalize ((u⁻¹ : (AE D)ˣ) : AE D) = u' at H1 hU hC
  generalize (u : AE D) = u at H2 hU hC
  have hue : ∀ v, u * idem D (· = v) ∈ idV 𝔞 v := fun v =>
    (H1 v _ (Ideal.mul_mem_left _ _ (idem_mem_idAt _))).2 (by rw [← mul_assoc, hU, one_mul]; exact idem_mem_intAt _)
  have loc : ∀ v, ∀ x ∈ 𝔞, u' * (idem D (· = v) * incA D x) ∈ intAt D (· = v) := fun v x hx =>
    (H1 v _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _))).1 (idem_mul_incA_mem hx v)
  constructor
  · intro hd c hc
    refine exists_integer_of_forall _ fun v => ?_
    have h3 := intAt_mul (loc v d hd) (cA_mem_intAt (loc v c hc))
    have h4 := (H2 v _ h3.1).1 h3
    have he := idem_mul_self (D := D) (· = v)
    rw [RingHom.map_mul (cA D), RingHom.map_mul (cA D), cA_idem, GlobalTheory.FinPl.FrameLat.cA_incA] at h4
    rw [RingHom.map_mul (incA D), RingHom.map_mul (incA D), alg₁ hU hC he]
    exact h4
  · intro hd
    have h𝔞 : 𝔞 ≠ 0 := by
      rintro rfl
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let v : Pl D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩
      have h0 := hue v
      rw [idV_zero, AddSubgroup.mem_bot] at h0
      apply idem_ne_zero v
      rw [← one_mul (idem D (· = v)), ← hU, mul_assoc, h0, mul_zero]
    have s1 : ∀ v, u' * (idem D (· = v) * incA D d) ∈ intAt D (· = v) := by
      intro v
      have hc := mul_cA_mem (y := d * h) (fun c hc => by
        obtain ⟨b, hb⟩ := hd c hc
        exact ⟨b, by rw [hb]; ring⟩) (hue v)
      refine (H2 v _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _)))).2 ?_
      rw [RingHom.map_mul (cA D), cA_idem, RingHom.map_mul (incA D)] at hc
      rw [alg₂ hU]; exact hc
    rw [← inv_inv 𝔞, FractionalIdeal.mem_inv_iff (inv_ne_zero h𝔞)]
    intro y hy
    refine (FractionalIdeal.mem_one_iff _).2 (exists_integer_of_forall _ fun v => ?_)
    have t := mul_incA_mem (y := y) (fun c hc =>
      (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff h𝔞).1 hy c hc)) (hue v)
    have h5 := intAt_mul (s1 v) t
    have he := idem_mul_self (D := D) (· = v)
    rw [RingHom.map_mul (incA D), alg₃ hU he]
    exact h5

end GlobalTheory.FinPl.SelfDualIdeal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealHermitianSelfDualOfLocalGeneratorStatement
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdeal_hermitianSelfDual_of_local_generators : ∀ (D : D7) (h : D.host.E) (𝔞 : FI D) (u : (AE D)ˣ), (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ idV 𝔞 x ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) → (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (u : AE D) * cA D (u : AE D) * incA D h * a ∈ intAt D (· = x)) → ∀ d : D.host.E, d ∈ 𝔞 ↔ ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * h := by
  first | exact @GlobalTheory.FinPl.SelfDualIdeal.selfDual_of_local | exact GlobalTheory.FinPl.SelfDualIdeal.selfDual_of_local | (intros; apply GlobalTheory.FinPl.SelfDualIdeal.selfDual_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleChangeFinitelyManySplitPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleChangeFinitelyManySplitPlaces
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.IdeleChange

open GlobalTheory.FinPl.FrameLat

variable {D : D7}

theorem idAt_le_idOff {x y : Pl D} (hxy : x ≠ y) : idAt D (· = x) ≤ idOff D (· = y) := by
  intro a ha
  unfold idOff
  rw [Submodule.mem_iInf]
  rintro ⟨w, rfl⟩
  exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 ha).2 ⟨w, fun e => hxy e.symm⟩

theorem mul_eq_zero_of_ne {x y : Pl D} (hxy : x ≠ y) {a b : AE D} (ha : a ∈ idAt D (· = x))
    (hb : b ∈ idAt D (· = y)) : a * b = 0 := by
  obtain ⟨⟨ε, -, -, -, h1, h2⟩, -⟩ := GlobalTheory.FinPl.localComponents D (· = y)
  have hb' := (h1 b).1 hb
  have ha' := (h2 a).1 (idAt_le_idOff hxy ha)
  calc a * b = a * (ε * b) := by rw [hb']
    _ = (ε * a) * b := by ring
    _ = 0 := by rw [ha', zero_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 2000000 in
theorem exists_change_one (q : SplitPt D k) (h : D.host.E) (hh : h ≠ 0) (hs : star h = h) (m : (AE D)ˣ) :
    ∃ m' : (AE D)ˣ, (∀ x, x ≠ q.v → ∀ a ∈ idAt D (· = x),
        (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧
      ∀ a ∈ idAt D (· = q.v), (m' : AE D) * cA D (m' : AE D) * incA D h * a = a := by
  have ht0 : q.pr (incA D h) ≠ 0 := by
    intro e
    exact hh ((map_eq_zero_iff (q.pr.comp (incA D)) (q.pr.comp (incA D)).injective).1 e)
  obtain ⟨t, ht⟩ : ∃ t : k, t = q.pr (incA D h) := ⟨_, rfl⟩
  rw [← ht] at ht0
  obtain ⟨s, hsdef⟩ : ∃ s : k, s = t⁻¹ := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : AE D, f = q.e + cA D q.e := ⟨_, rfl⟩
  have hf : ∀ b ∈ idAt D (· = q.v), f * b = b := fun b hb => by rw [hfdef]; exact (idem_iff q b).1 hb
  have hfm : f ∈ idAt D (· = q.v) := by rw [hfdef]; exact sum_mem_idAt q
  have hff : f * f = f := hf _ hfm
  have hcf : cA D f = f := by rw [hfdef, map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hce : cA D q.e * q.e = 0 := cAe_mul_e q
  have hcee : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, q.split.1]
  have hsc : ∀ c, q.sec c * cA D q.e = 0 := fun c => by
    linear_combination (-(cA D q.e)) * e_mul_sec q c + q.sec c * hec
  have hcem : cA D q.e ∈ idAt D (· = q.v) := by rw [← sec_one]; exact csec_mem_idAt (p := q) 1
  obtain ⟨u, hudef⟩ : ∃ u : AE D, u = q.sec s + cA D q.e := ⟨_, rfl⟩
  obtain ⟨u', hu'def⟩ : ∃ u' : AE D, u' = q.sec t + cA D q.e := ⟨_, rfl⟩
  have hu : u ∈ idAt D (· = q.v) := by rw [hudef]; exact add_mem (sec_mem_idAt q _) hcem
  have hu' : u' ∈ idAt D (· = q.v) := by rw [hu'def]; exact add_mem (sec_mem_idAt q _) hcem
  have hcu : cA D u ∈ idAt D (· = q.v) := by
    rw [hudef, map_add (f := _), Formalism.L2.Theta.cA_cA]; exact add_mem (csec_mem_idAt (p := q) _) (e_mem_idAt q)
  have hst : q.sec s * q.sec t = q.e := by rw [← sec_mul, hsdef, inv_mul_cancel₀ ht0, sec_one]
  have huu : u * u' = f := by
    have h1 := hsc s
    have h2 : cA D q.e * q.sec t = 0 := by rw [mul_comm]; exact hsc t
    rw [hudef, hu'def, hfdef]
    linear_combination hst + h1 + h2 + hcee
  have hmm : (m : AE D) * ((m⁻¹ : (AE D)ˣ) : AE D) = 1 := m.mul_inv
  obtain ⟨mi, hmi⟩ : ∃ mi : AE D, mi = ((m⁻¹ : (AE D)ˣ) : AE D) := ⟨_, rfl⟩
  rw [← hmi] at hmm
  obtain ⟨w, hw⟩ : ∃ w : AE D, w = (m : AE D) * (1 - f) + u := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : AE D, w' = mi * (1 - f) + u' := ⟨_, rfl⟩
  have hww : w * w' = 1 := by
    rw [hw, hw']
    linear_combination (1 - f) ^ 2 * hmm + hff - (m : AE D) * hf _ hu' - mi * hf _ hu + huu
  have hcw : cA D w = cA D (m : AE D) * (1 - f) + cA D u := by
    rw [hw, map_add (f := _), map_mul, map_sub, map_one, hcf]
  refine ⟨Units.mkOfMulEqOne w w' hww, fun x hx a ha => ?_, fun a ha => ?_⟩
  · have hfa : f * a = 0 := mul_eq_zero_of_ne (Ne.symm hx) hfm ha
    have hua : u * a = 0 := mul_eq_zero_of_ne (Ne.symm hx) hu ha
    have hcua : cA D u * a = 0 := mul_eq_zero_of_ne (Ne.symm hx) hcu ha
    rw [Units.val_mkOfMulEqOne, hcw, hw]
    constructor
    · linear_combination (-(m : AE D)) * hfa + hua
    · linear_combination (-(cA D (m : AE D))) * hfa + hcua
  · rw [Units.val_mkOfMulEqOne]
    have hb : incA D h * a ∈ idAt D (· = q.v) := Ideal.mul_mem_left _ _ ha
    have hwa : ∀ b ∈ idAt D (· = q.v), w * b = u * b := fun b hb => by
      rw [hw]
      linear_combination (-(m : AE D)) * hf b hb
    have hcwa : ∀ b ∈ idAt D (· = q.v), cA D w * b = cA D u * b := fun b hb => by
      rw [hcw]
      linear_combination (-(cA D (m : AE D))) * hf b hb
    have hc2 : cA D u * (incA D h * a) ∈ idAt D (· = q.v) := Ideal.mul_mem_left _ _ hb
    have hA : q.sec s * incA D h = q.e := by
      rw [sec_mul_right, ← ht, hsdef, inv_mul_cancel₀ ht0, sec_one]
    have hB : cA D (q.sec s) * incA D h = cA D q.e := by
      have e0 : incA D h = cA D (incA D h) := by rw [cA_incA, hs]
      rw [e0, ← map_mul, hA]
    have hC1 : cA D q.e * cA D (q.sec s) = cA D (q.sec s) := by rw [← map_mul, e_mul_sec]
    have hD : q.sec s * q.e = q.sec s := by rw [mul_comm, e_mul_sec]
    have hkey : u * cA D u * incA D h = f := by
      rw [hudef, hfdef, map_add (f := _), Formalism.L2.Theta.cA_cA]
      linear_combination (incA D h) * ((-(q.sec s)) * hC1 + (cA D (q.sec s)) * hsc s + hD + hce + hC1) + hA + hB
    calc w * cA D w * incA D h * a = w * (cA D w * (incA D h * a)) := by ring
      _ = u * (cA D u * (incA D h * a)) := by rw [hcwa _ hb, hwa _ hc2]
      _ = (u * cA D u * incA D h) * a := by ring
      _ = a := by rw [hkey, hf a ha]

theorem exists_change_list {ι : Type} (p : ι → SplitPt D k) (hp : Function.Injective fun i => (p i).v) (h : D.host.E)
    (hh : h ≠ 0) (hs : star h = h) (m : (AE D)ˣ) (l : List ι) :
    ∃ m' : (AE D)ˣ, (∀ x, (∀ i ∈ l, x ≠ (p i).v) → ∀ a ∈ idAt D (· = x),
        (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧
      ∀ i ∈ l, ∀ a ∈ idAt D (· = (p i).v), (m' : AE D) * cA D (m' : AE D) * incA D h * a = a := by
  induction l with
  | nil => exact ⟨m, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ hi => absurd hi List.not_mem_nil⟩
  | cons i l ih =>
    obtain ⟨m₁, hA₁, hB₁⟩ := ih
    obtain ⟨m₂, hA₂, hB₂⟩ := exists_change_one (p i) h hh hs m₁
    refine ⟨m₂, fun x hx a ha => ?_, fun j hj a ha => ?_⟩
    · have e2 := hA₂ x (hx i List.mem_cons_self) a ha
      have e1 := hA₁ x (fun j hj => hx j (List.mem_cons_of_mem _ hj)) a ha
      exact ⟨e2.1.trans e1.1, e2.2.trans e1.2⟩
    · by_cases e : j = i
      · subst e; exact hB₂ a ha
      · have hj' : j ∈ l := (List.mem_cons.1 hj).resolve_left e
        have hne : (p j).v ≠ (p i).v := fun e' => e (hp e')
        have hb : incA D h * a ∈ idAt D (· = (p j).v) := Ideal.mul_mem_left _ _ ha
        have e1 := (hA₂ _ hne _ hb).2
        have hc : cA D (m₁ : AE D) * (incA D h * a) ∈ idAt D (· = (p j).v) := Ideal.mul_mem_left _ _ hb
        have e2 := (hA₂ _ hne _ hc).1
        calc (m₂ : AE D) * cA D (m₂ : AE D) * incA D h * a = (m₂ : AE D) * (cA D (m₂ : AE D) * (incA D h * a)) := by ring
          _ = (m₁ : AE D) * (cA D (m₁ : AE D) * (incA D h * a)) := by rw [e1, e2]
          _ = (m₁ : AE D) * cA D (m₁ : AE D) * incA D h * a := by ring
          _ = a := hB₁ j hj' a ha

end GlobalTheory.FinPl.IdeleChange


open GlobalTheory.FinPl.IdeleChange in
theorem GlobalTheory.FinPl.exists_idele_change_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ h : D.host.E, h ≠ 0 → star h = h → ∀ m : (AE D)ˣ, ∃ m' : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧ ∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP h hh hs m
  obtain ⟨m', hA, hB⟩ := exists_change_list p hP.inj h hh hs m I
  refine ⟨m', fun x hx a ha => hA x (fun i _ e => hx ((hP.mem x).2 ⟨i, e⟩)) a ha, fun x hx a ha => ?_⟩
  obtain ⟨i, rfl⟩ := (hP.mem x).1 hx
  rw [hB i (hP.all i) a ha]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleChangeFinitelyManySplitPlacesStatement
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idele_change_finitely_many_split_places : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ h : D.host.E, h ≠ 0 → star h = h → ∀ m : (AE D)ˣ, ∃ m' : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧ ∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
  first | exact @GlobalTheory.FinPl.exists_idele_change_split | exact GlobalTheory.FinPl.exists_idele_change_split | (intros; apply GlobalTheory.FinPl.exists_idele_change_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFractionalIdealOfHermIdele
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFractionalIdealOfHermIdele
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct nonZeroDivisors

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SeeSaw.IdeleIdeal

variable {D : D7}

theorem one_tmul_mem (o : 𝓞 D.host.E) : (1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAE D :=
  GlobalTheory.FinPl.Conductor.tmul_mem (fun v => by rw [map_one]; exact one_mem _) o

theorem one_tmul_mem_iff (e : D.host.E) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] e ∈ intAE D ↔ e ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have h : finPart D (incA D e) = (1 : Af D.host.F) ⊗ₜ[D.host.F] e := by
    change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [← h]
  exact (GlobalTheory.SplitDec.int_iff (incA D e)).trans (GlobalTheory.SplitDec.rat_int_iff e)

theorem exists_int_mul (y : Af D.host.F ⊗[D.host.F] D.host.E) : ∃ N : 𝓞 D.host.E, N ≠ 0 ∧
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * y ∈ intAE D := by
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.FinPl.Conductor.approx y
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  have hb0 : (b : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  refine add_mem ?_ (GlobalTheory.FinPl.Conductor.mul_mem_int (one_tmul_mem b) hu)
  have e : (b : D.host.E) * x = (a : D.host.E) := by
    rw [← hab]; field_simp
  rw [e]
  exact one_tmul_mem a

theorem approx_mul (z : Af D.host.F ⊗[D.host.F] D.host.E) {N : 𝓞 D.host.E} (hN : N ≠ 0) :
    ∃ x : D.host.E, ∃ u ∈ intAE D,
    z = (1 : Af D.host.F) ⊗ₜ[D.host.F] x + ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * u := by
  have hN' : (N : D.host.E) ≠ 0 := by exact_mod_cast hN
  obtain ⟨x, u, hu, e⟩ := GlobalTheory.FinPl.Conductor.approx
    (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) * z)
  refine ⟨N * x, u, hu, ?_⟩
  have h1 : ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hN']; rfl
  calc z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) *
        (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) * z) := by rw [← mul_assoc, h1, one_mul]
    _ = _ := by rw [e, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end GlobalTheory.SeeSaw.IdeleIdeal

namespace GlobalTheory.SeeSaw.IdeleIdeal

variable {D : D7}

def subOf (y : Af D.host.F ⊗[D.host.F] D.host.E) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {d | y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D}
  add_mem' {a b} ha hb := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a + b)) ∈ intAE D
    rw [TensorProduct.tmul_add, mul_add]; exact add_mem ha hb
  zero_mem' := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (0 : D.host.E)) ∈ intAE D
    rw [TensorProduct.tmul_zero, mul_zero]; exact zero_mem _
  smul_mem' c d hd := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c • d)) ∈ intAE D
    have e : y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c • d)) =
        ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) * (y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
      rw [Algebra.smul_def, ← mul_assoc, mul_comm _ y, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e]
    exact GlobalTheory.FinPl.Conductor.mul_mem_int (one_tmul_mem c) hd

theorem mem_subOf {y : Af D.host.F ⊗[D.host.F] D.host.E} {d : D.host.E} :
    d ∈ subOf y ↔ y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := Iff.rfl

theorem isFractional_subOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) :
    IsFractional (𝓞 D.host.E)⁰ (subOf y) := by
  obtain ⟨N, hN, hNy⟩ := exists_int_mul y'
  refine ⟨N, mem_nonZeroDivisors_of_ne_zero hN, fun d hd => ?_⟩
  have e : (1 : Af D.host.F) ⊗ₜ[D.host.F] (N • d) =
      (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * y') * (y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
    rw [mul_assoc, ← mul_assoc y', h, one_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
  have := GlobalTheory.FinPl.Conductor.mul_mem_int hNy (mem_subOf.1 hd)
  rw [← e, one_tmul_mem_iff, Submodule.mem_one] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨r, hr⟩

def idealOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) : FI D := ⟨subOf y, isFractional_subOf h⟩

theorem mem_idealOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) {d : D.host.E} :
    d ∈ idealOf h ↔ y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := Iff.rfl

end GlobalTheory.SeeSaw.IdeleIdeal


open GlobalTheory.SeeSaw.IdeleIdeal GlobalTheory.FinPlLoc in
theorem GlobalTheory.SeeSaw.exists_idealOfIdele : ∀ (D : D7) (m : (AE D)ˣ), ∃ 𝔞 : FI D, ∀ x : Pl D, ∀ a ∈ idAt D (· = x),
    a ∈ idV 𝔞 x ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D m
  set mi := finPart D ((m⁻¹ : (AE D)ˣ) : AE D) with hmi
  set mf := finPart D (m : AE D) with hmf
  have hmm : mf * mi = 1 := by
    rw [hmf, hmi, ← map_mul, Units.mul_inv, map_one]
  refine ⟨idealOf hmm, fun x a ha => ?_⟩
  have hmemA : ∀ d : D.host.E, d ∈ (idealOf hmm) ↔
      mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := fun d => mem_idealOf hmm
  constructor
  · intro hv
    refine ⟨Ideal.mul_mem_left _ _ ha, ?_⟩
    rw [map_mul, ← hmi]
    clear ha
    induction hv using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, -, d, hd, rfl⟩ := hy
      rw [finPart_pair]
      have e : mi * (α ⊗ₜ[D.host.F] d) = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * (mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
        rw [mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      have h1 : α ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D := by
        simpa using GlobalTheory.FinPl.Conductor.tmul_mem hα (1 : 𝓞 D.host.E)
      exact GlobalTheory.FinPl.Conductor.mul_mem_int h1 ((hmemA d).1 hd)
    | zero => rw [map_zero, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _), mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg, mul_neg]; exact neg_mem hy
  · intro hi
    have hz : mi * finPart D a ∈ intAE D := by
      have := hi.2
      rwa [map_mul, ← hmi] at this
    obtain ⟨N, hN, hNm⟩ := exists_int_mul mi
    obtain ⟨d, u, hu, e⟩ := approx_mul (finPart D a) hN
    have hd : d ∈ (idealOf hmm) := by
      rw [hmemA]
      have e2 : mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) =
          mi * finPart D a - (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * mi) * u := by
        rw [e]; ring
      rw [e2]
      exact sub_mem hz (GlobalTheory.FinPl.Conductor.mul_mem_int hNm hu)
    have hidem : (singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a :=
      GlobalTheory.FinPl.Conductor.idem_mul x _ fun w hw => (Submodule.mem_iInf _).1 (Ideal.mem_inf.1 ha).2 ⟨w, hw⟩
    have hε : singleV D.host.F x 1 ∈ intAf D.host.F := by
      have := GlobalTheory.FinPl.Conductor.idem_mul_mem (v := x) (α := 1) (by rw [map_one]; exact one_mem _)
      rwa [mul_one] at this
    have hsupp : ∀ (β : Af D.host.F) w, w ≠ x → evalV D.host.F w (singleV D.host.F x 1 * β) = 0 := fun β w hw => by
      rw [map_mul, GlobalTheory.FinPl.Conductor.ev_ne hw, zero_mul]

    have hrest : ∀ u ∈ intAE D, finIn D ((singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) *
        (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * u)) ∈ idV (idealOf hmm) x := by
      intro u hu
      induction hu using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨β, hβ, o, rfl⟩ := hy
        have e3 : (singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) *
            (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * (β ⊗ₜ[D.host.F] (o : D.host.E))) =
            (singleV D.host.F x 1 * β) ⊗ₜ[D.host.F] ((N : D.host.E) * o) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
        rw [e3, finIn_tmul]
        refine AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPl.Conductor.idem_mul_mem (hβ x), hsupp β, _, ?_, rfl⟩
        rw [hmemA]
        have e4 : mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * o)) =
            (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * mi) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) := by
          rw [mul_comm _ mi, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [e4]
        exact GlobalTheory.FinPl.Conductor.mul_mem_int hNm (one_tmul_mem o)
      | zero => rw [mul_zero, mul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add, mul_add, map_add (f := _)]; exact add_mem hy hz
      | neg y _ hy => rw [mul_neg, mul_neg, map_neg]; exact neg_mem hy
    rw [eq_finIn (infPart_of_idAt ha), ← hidem, e, mul_add, map_add (f := _)]
    refine add_mem ?_ (hrest u hu)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, finIn_tmul]
    exact AddSubgroup.subset_closure ⟨_, hε, fun w hw => GlobalTheory.FinPl.Conductor.ev_ne hw, d, hd, rfl⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFractionalIdealOfHermIdeleStatement
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fractionalIdeal_of_hermIdele : ∀ (D : D7) (m : (AE D)ˣ), ∃ 𝔞 : FI D, ∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ idV 𝔞 x ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  first | exact @GlobalTheory.SeeSaw.exists_idealOfIdele | exact GlobalTheory.SeeSaw.exists_idealOfIdele | (intros; apply GlobalTheory.SeeSaw.exists_idealOfIdele <;> assumption)
end
end

open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.CoreIdele

variable {D : D7}

theorem card_eq_of_inv {k : Type} [Field k] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (b : Matrix m n k) (b' : Matrix n m k) (h : b * b' = 1) (h' : b' * b = 1) : Fintype.card n = Fintype.card m := by
  have h1 : Fintype.card m ≤ Fintype.card n := by
    have := Matrix.rank_mul_le_left b b'
    rw [h, Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width b)
  have h2 : Fintype.card n ≤ Fintype.card m := by
    have := Matrix.rank_mul_le_left b' b
    rw [h', Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width b')
  omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_sumFrame' (p : SplitPt D k) {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E}
    (hζ : IsLineVec L ζ) {n : Type} [Fintype n] [DecidableEq n] (β : Frame p A n) :
    ∃ β₀ : Frame p S (n ⊕ Fin 1), IsSumFrame o ζ β β₀ := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let r : Fin L.rank → D.host.E := (star ζ ⬝ᵥ L.gram *ᵥ ζ)⁻¹ • (star ζ ᵥ* L.gram)
  have hr : r ⬝ᵥ ζ = 1 := by
    simp only [r]
    rw [smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hζ.2]
  let bE : Matrix (Fin S.rank) (Fin A.rank ⊕ Fin 1) D.host.E := fromCols o.iA (replicateCol (Fin 1) (o.iB *ᵥ ζ))
  let bE' : Matrix (Fin A.rank ⊕ Fin 1) (Fin S.rank) D.host.E := fromRows o.qA (replicateRow (Fin 1) (r ᵥ* o.qB))
  have h1 : bE' * bE = 1 := by
    simp only [bE, bE']
    rw [fromRows_mul_fromCols, ← Matrix.fromBlocks_one]
    congr 1
    · exact o.qA_iA
    · rw [← replicateCol_mulVec, Matrix.mulVec_mulVec, o.qA_iB, Matrix.zero_mulVec]; rfl
    · rw [← replicateRow_vecMul, Matrix.vecMul_vecMul, show o.qB * o.iA = 0 from o.symm.qA_iB, Matrix.vecMul_zero]; rfl
    · ext i j
      rw [replicateRow_mul_replicateCol_apply, dotProduct_mulVec, Matrix.vecMul_vecMul,
        show o.qB * o.iB = 1 from o.symm.qA_iA, Matrix.vecMul_one, hr, Subsingleton.elim i j, Matrix.one_apply_eq]
  have hn : Fintype.card n = A.rank := by simpa using card_eq_of_inv β.b β.b' β.bb' β.b'b
  let X : Matrix (Fin A.rank ⊕ Fin 1) (n ⊕ Fin 1) k := fromBlocks β.b 0 0 1
  let X' : Matrix (n ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b' 0 0 1
  have hX : X' * X = 1 := by
    simp only [X, X', fromBlocks_multiply, β.b'b]; simp
  have g1 : (X' * bE'.map f) * (bE.map f * X) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bE'.map f), ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.one_mul, hX]
  have hc : Fintype.card (Fin S.rank) = Fintype.card (n ⊕ Fin 1) := by
    have := o.rank_add; have := hζ.1
    simp only [Fintype.card_fin, Fintype.card_sum, hn]; omega
  have g2 : (bE.map f * X) * (X' * bE'.map f) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).2 g1
  obtain ⟨β₀, h₀⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character D).2 k p).1 S (n ⊕ Fin 1) _ _ g2 g1
  refine ⟨β₀, ?_⟩
  rw [IsSumFrame, h₀]
  simp only [bE, X, fromCols_map, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  ext i (j | j) <;> rfl

theorem line_of_orth {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (v : Pl D) (ho : OrthAt o M LA LL v) (a : AE D) :
    a • ratV (vecB o ζ) ∈ latV S M (· = v) ↔ a • ratV ζ ∈ latV L LL (· = v) := by
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.FinPl.CoreIdele

theorem GlobalTheory.FinPl.CoreIdele.lineLat_idele : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ m : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * cA D (m : AE D) * incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) * a ∈ intAt D (· = x)) → ∃ LL : Lat L, IsSelfDualC L LL ∧ ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP L ζ hζ m hm
  set h := star ζ ⬝ᵥ L.gram *ᵥ ζ with hhdef
  have hh : star h = h := by
    have hG : ∀ i j, star (L.gram i j) = L.gram j i := fun i j => by
      have := congrFun (congrFun (gram_conjTranspose L) j) i
      simpa [Matrix.conjTranspose_apply] using this
    have e : star (star ζ ⬝ᵥ L.gram *ᵥ ζ) = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
      simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum, hG]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    exact e
  obtain ⟨m', hoff, hon⟩ := GlobalTheory.T.exists_idele_change_finitely_many_split_places D k ι p I P hP h hζ.2 hh m
  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.T.exists_fractionalIdeal_of_hermIdele D m'
  have key : ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), ((m'⁻¹ : (AE D)ˣ) : AE D) * a = ((m⁻¹ : (AE D)ˣ) : AE D) * a := by
    intro x hx a ha
    have h1 : ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
    have h2 := (hoff x hx _ h1).1
    rw [← mul_assoc (m : AE D), Units.mul_inv, one_mul] at h2
    calc ((m'⁻¹ : (AE D)ˣ) : AE D) * a = ((m'⁻¹ : (AE D)ˣ) : AE D) * ((m' : AE D) * (((m⁻¹ : (AE D)ˣ) : AE D) * a)) := by
          rw [h2]
      _ = ((m⁻¹ : (AE D)ˣ) : AE D) * a := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have hloc : ∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔
      (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
    intro x a ha
    by_cases hx : P x
    · exact hon x hx a ha
    · have h1 : incA D h * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
      have h2 : cA D (m : AE D) * (incA D h * a) ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ h1
      have e : (m' : AE D) * cA D (m' : AE D) * incA D h * a = (m : AE D) * cA D (m : AE D) * incA D h * a := by
        rw [mul_assoc, mul_assoc, (hoff x hx _ h1).2, (hoff x hx _ h2).1, ← mul_assoc, ← mul_assoc]
      rw [e]
      exact hm x hx a ha
  have hsd := GlobalTheory.T.fractionalIdeal_hermitianSelfDual_of_local_generators D h 𝔞 m' h𝔞 hloc
  have hζ0 : ζ ≠ 0 := fun e => hζ.2 (by rw [e]; simp)
  refine ⟨GlobalTheory.SeeSaw.LiftModel.lineLat L ζ 𝔞, GlobalTheory.SeeSaw.LiftModel.isSelfDualC_lineLat D L ζ hζ 𝔞 hsd, fun x hx a ha => ?_⟩
  rw [GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ0 𝔞 x a ha, h𝔞 x a ha, key x hx a ha]


open GlobalTheory.FinPl.CoreIdele GlobalTheory.SeeSaw.CoreGlue in
theorem GlobalTheory.FinPl.CoreIdele.exists_core : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (q : Unif k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (β : ∀ i, Frame (p i) B.A n) (Q : ι → Pair k n) (LA : Lat B.A), IsSelfDualC B.A LA → (∀ i, (β i).IsLat LA (Q i).lat) → (∀ i, valuation k ((p i).pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = valuation k ((q.1 : 𝒪[k]) : k)) → ∀ m : (AE D)ˣ, (∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * a ∈ intAt D (· = x)) → (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * cA D (m : AE D) * incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a ∈ intAt D (· = x)) → ∃ (M : Lat B.V₀) (β₀ : ∀ i, Frame (p i) B.V₀ (n ⊕ Fin 1)), IsSelfDualC B.V₀ M ∧ (∀ i, GluedCore B M q (β i) (β₀ i) (Q i)) ∧ (∀ x, ¬ P x → ∃ LL : Lat B.L, IsSelfDualC B.L LL ∧ OrthAt B.o M LA LL x ∧ ∀ a ∈ idAt D (· = x), a • ratV B.ζ ∈ latV B.L LL (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧ ∀ x, ∀ a ∈ idAt D (· = x), a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP q n _ _ ρ B β Q LA hLA _ hnorm m hmP hmoff
  obtain ⟨LL, hLL, hline⟩ := lineLat_idele D k ι p I P hP B.L B.ζ B.line m hmoff
  obtain ⟨M₁, hM₁, horth⟩ := exists_orthSum B.o hLA hLL
  have frames : ∀ i, ∃ β₀ : Frame (p i) B.V₀ (n ⊕ Fin 1), IsSumFrame B.o B.ζ (β i) β₀ :=
    fun i => exists_sumFrame' (p i) B.o B.line (β i)
  choose β₀ hβ₀ using frames
  obtain ⟨M, hM, hlat, hoff⟩ := exists_modify hP.inj β₀ (fun i => gluedS q 1 (Q i).ker (Q i).vec)
    (fun i => by haveI := (Q i).ker_isLat; infer_instance) hM₁ I
  have glued : ∀ i, GluedCore B M q (β i) (β₀ i) (Q i) := fun i =>
    ⟨hP.unit i, hβ₀ i, hnorm i, hlat i (hP.all i)⟩
  have offP : ∀ x, ¬ P x → ∀ i, x ≠ (p i).v := fun x hx i e => hx ((hP.mem x).2 ⟨i, e⟩)
  have horthM : ∀ x, ¬ P x → OrthAt B.o M LA LL x := fun x hx y => by
    rw [hoff x (offP x hx)]
    exact horth x y
  refine ⟨M, β₀, hM, glued, fun x hx => ⟨LL, hLL, horthM x hx, hline x hx⟩, fun x a ha => ?_⟩
  by_cases hx : P x
  · obtain ⟨i, rfl⟩ := (hP.mem x).1 hx
    rw [line_of_glued hM (glued i) ha]
    have hma : ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_left _ _ ha
    have := hmP _ hx _ hma
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this.symm
  · rw [line_of_orth B.o B.ζ M LA LL x (horthM x hx) a]
    exact hline x hx a ha
