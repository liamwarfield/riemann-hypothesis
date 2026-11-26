module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndLatticeTraceIntegral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralTraceOneUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralTraceOneUnramified
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc

theorem exists_integral_add_cc_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    Unr E → ∃ t : E, IsIntegral ℤ t ∧ t + cc t = 1 := by
  intro E _ _ _ hE
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hE
  let σ := IsCMField.ringOfIntegersComplexConj E
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | ∃ t : 𝓞 E, algebraMap _ (𝓞 E) a = t + σ t}
      add_mem' := by
        rintro a b ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨s + t, by rw [map_add (f := _), hs, ht, map_add (f := _)]; ring⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨t, ht⟩
        refine ⟨algebraMap _ (𝓞 E) c * t, ?_⟩
        rw [smul_eq_mul, map_mul, ht, map_mul, AlgEquiv.commutes]
        ring }
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) m
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1
        (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))]; exact bot_le)
    have htr : ∀ t : 𝓞 E, t + σ t ∈ P := by
      intro t
      have hco : ((t + σ t : 𝓞 E) : E) = (t : E) + IsCMField.complexConj E t := by
        rw [← IsCMField.coe_ringOfIntegersComplexConj]
        rfl
      have hfix := (IsCMField.complexConj_eq_self_iff E ((t : E) + IsCMField.complexConj E t)).1 (by
        rw [map_add (f := _), IsCMField.complexConj_apply_apply, add_comm])
      have hi : IsIntegral ℤ (⟨_, hfix⟩ : maximalRealSubfield E) := by
        have h0 : IsIntegral ℤ ((t + σ t : 𝓞 E) : E) := (t + σ t).isIntegral_coe
        rw [hco] at h0
        exact (isIntegral_algebraMap_iff ).1 h0
      let a : 𝓞 (maximalRealSubfield E) := ⟨_, hi⟩
      have hA : algebraMap _ (𝓞 E) a = t + σ t := by
        apply RingOfIntegers.ext
        rw [hco]
        rfl
      have h1 : a ∈ Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P := by
        change a ∈ Ideal.under (𝓞 (maximalRealSubfield E)) P
        rw [hPm]
        exact hIm ⟨t, hA⟩
      exact hA ▸ Ideal.mem_comap.1 h1
    have hσ : ∃ s, σ.toAlgHom s ≠ s := by
      by_contra hc
      push Not at hc
      apply IsCMField.complexConj_ne_one E
      ext x
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
      have hc' : ∀ s : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E s :=
        fun s => congrArg (fun z : 𝓞 E => (z : E)) (hc s)
      simp [hc']
    obtain ⟨t, ht⟩ := GlobalTheory.UCls.Det.exists_sub_notMem σ.toAlgHom hσ P hP.ne_top
    apply ht
    have h2 := P.sub_mem (htr t) (P.mul_mem_right (σ t) (htr 1))
    convert h2 using 1
    change t - σ t = t + σ t - (1 + σ 1) * σ t
    rw [map_one]
    ring
  obtain ⟨t, ht⟩ : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := hI ▸ Submodule.mem_top
  refine ⟨(t : E), t.isIntegral_coe, ?_⟩
  have h := congrArg (fun z : 𝓞 E => (z : E)) ht
  rw [map_one] at h
  change (1 : E) = (t : E) + ((σ t : 𝓞 E) : E) at h
  rw [IsCMField.coe_ringOfIntegersComplexConj] at h
  rw [cc]
  exact h.symm

end GlobalTheory.LieDisc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralTraceOneUnramifiedStatement
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_trace_one_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∃ t : E, IsIntegral ℤ t ∧ t + cc t = 1 := by
  first | exact @GlobalTheory.LieDisc.exists_integral_add_cc_eq_one | exact GlobalTheory.LieDisc.exists_integral_add_cc_eq_one | (intros; apply GlobalTheory.LieDisc.exists_integral_add_cc_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImaginaryLatticeScalingIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImaginaryLatticeScalingIndex
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc.ImIndex

open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def imSp (E : Type) [Field E] [NumberField E] [IsCMField E] : Submodule ℚ E where
  carrier := {a | cc a = -a}
  zero_mem' := by simp [cc]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, cc, map_add (f := _)] at ha hb ⊢; rw [ha, hb, neg_add]
  smul_mem' q a ha := by
    simp only [Set.mem_ofPred_eq, cc] at ha ⊢
    rw [map_rat_smul, ha, smul_neg]

theorem mem_imSp {a : E} : a ∈ imSp E ↔ cc a = -a := Iff.rfl

def dm (E : Type) [Field E] [NumberField E] [IsCMField E] : E →ₗ[ℚ] E where
  toFun x := x - cc x
  map_add' x y := by simp only [cc, map_add (f := _)]; ring
  map_smul' q x := by simp only [cc, map_rat_smul, RingHom.id_apply, smul_sub]

theorem range_dm : LinearMap.range (dm E) = imSp E := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change cc (x - cc x) = -(x - cc x)
    rw [show cc (x - cc x) = cc x - cc (cc x) by simp [cc], cc_cc]; ring
  · intro hy
    refine ⟨(1 / 2 : ℚ) • y, ?_⟩
    change (1 / 2 : ℚ) • y - cc ((1 / 2 : ℚ) • y) = y
    rw [show cc ((1 / 2 : ℚ) • y) = (1 / 2 : ℚ) • cc y from map_rat_smul _ _ _, (mem_imSp).1 hy,
      smul_neg, sub_neg_eq_add, ← add_smul]
    norm_num

theorem mem_ker_dm {x : E} : x ∈ LinearMap.ker (dm E) ↔ x ∈ maximalRealSubfield E := by
  rw [LinearMap.mem_ker, ← IsCMField.complexConj_eq_self_iff]
  change x - cc x = 0 ↔ _
  rw [sub_eq_zero, eq_comm]; rfl

def kerEquiv (E : Type) [Field E] [NumberField E] [IsCMField E] :
    LinearMap.ker (dm E) ≃ₗ[ℚ] maximalRealSubfield E where
  toFun x := ⟨x.1, mem_ker_dm.1 x.2⟩
  invFun y := ⟨y.1, mem_ker_dm.2 y.2⟩
  map_add' x y := rfl
  map_smul' q x := by ext; simp [Rat.smul_def]
  left_inv x := rfl
  right_inv y := rfl

theorem finrank_imSp : Module.finrank ℚ (imSp E) = fdeg E := by
  have h := LinearMap.finrank_range_add_finrank_ker (dm E)
  rw [range_dm, (kerEquiv E).finrank_eq] at h
  have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  unfold fdeg
  rw [← h1, h2] at h ⊢
  omega

instance : Module.Finite ℤ (imLat E) := by
  let f : imLat E →+ 𝓞 E :=
    { toFun := fun x => ⟨x.1, x.2.1⟩
      map_zero' := rfl
      map_add' := fun x y => rfl }
  exact Module.Finite.of_injective f.toIntLinearMap (fun x y h => Subtype.ext (congrArg Subtype.val h :))

instance : Module.Free ℤ (imLat E) := Module.free_of_finite_type_torsion_free'

theorem finrank_imLat : Module.finrank ℤ (imLat E) = fdeg E := by
  rw [← finrank_imSp]
  let b := Module.Free.chooseBasis ℤ (imLat E)
  let v : Module.Free.ChooseBasisIndex ℤ (imLat E) → E := fun i => (b i : E)
  have hz : LinearIndependent ℤ v :=
    b.linearIndependent.map' (imLat E).subtype.toIntLinearMap
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hq : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hz
  have hspan : Submodule.span ℚ (Set.range v) = imSp E := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (b i).2.2
    · intro x hx
      have halg : IsAlgebraic ℤ x :=
        (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
      obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
      have hy : n • x ∈ imLat E := by
        refine ⟨hint, ?_⟩
        rw [mem_imSp] at hx
        simp only [cc, map_zsmul] at hx ⊢
        rw [hx, smul_neg]
      have hsum := b.sum_repr ⟨n • x, hy⟩
      have hmem : n • x ∈ Submodule.span ℚ (Set.range v) := by
        rw [show n • x = ((⟨n • x, hy⟩ : imLat E) : E) from rfl, ← hsum]
        change (imLat E).subtype (∑ i, (b.repr ⟨n • x, hy⟩) i • b i) ∈ _
        rw [map_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        change (((b.repr ⟨n • x, hy⟩) i • b i : imLat E) : E) ∈ _
        rw [AddSubgroup.coe_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hx' : x = ((n : ℚ)⁻¹) • (n • x) := by
        rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
      rw [hx']
      exact Submodule.smul_mem _ _ hmem
  rw [← hspan, finrank_span_eq_card hq, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory.LieDisc.ImIndex


open GlobalTheory.LieDisc.ImIndex in
theorem GlobalTheory.LieDisc.relIndex_mulLeft_imLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ),
    Unr E → 1 ≤ r →
      (AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E)).relIndex (imLat E) = r ^ fdeg E := by
  intro E _ _ _ r _ _
  rw [AddSubgroup.relIndex, ← finrank_imLat, ← AddSubgroup.index_range_nsmul (imLat E) r]
  congr 1
  ext ⟨x, hx⟩
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft,
    AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simp [← hyx, nsmul_eq_mul])⟩
  · rintro ⟨⟨y, hy⟩, hyx⟩
    refine ⟨y, hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [nsmul_eq_mul] using this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImaginaryLatticeScalingIndexStatement
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imaginary_lattice_scaling_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), Unr E → 1 ≤ r → (AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E)).relIndex (imLat E) = r ^ fdeg E := by
  first | exact @GlobalTheory.LieDisc.relIndex_mulLeft_imLat | exact GlobalTheory.LieDisc.relIndex_mulLeft_imLat | (intros; apply GlobalTheory.LieDisc.relIndex_mulLeft_imLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEndLatticeOfTraceDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEndLatticeOfTraceDual
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def rankOneHerm (G : Matrix (Fin r) (Fin r) E) (l y : Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => l a * ∑ k, G b k * cc (y k)

theorem rankOneHerm_mulVec (G : Matrix (Fin r) (Fin r) E) (l y x : Fin r → E) :
    rankOneHerm G l y *ᵥ x = herm G x y • l := by
  ext a
  simp only [rankOneHerm, mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul, herm]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem trace_mul_rankOneHerm (G Y : Matrix (Fin r) (Fin r) E) (l y : Fin r → E) :
    (Y * rankOneHerm G l y).trace = herm G (Y *ᵥ l) y := by
  simp only [trace, diag, Matrix.mul_apply, rankOneHerm, of_apply, herm, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem rankOneHerm_mem_endLat {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hΛ : SelfDualLat G Λ) {l y : Fin r → E} (hl : l ∈ Λ) (hy : y ∈ Λ) :
    rankOneHerm G l y ∈ endLat Λ := fun x hx => by
  rw [rankOneHerm_mulVec]
  exact smul_mem_of_isIntegral (((hΛ.2.2.2.2 x).mpr hx) y hy) hl

theorem mem_endLat_of_trace_integral (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E)
    (hΛ : SelfDualLat G Λ) (hY : ∀ Z ∈ endLat Λ, IsIntegral ℤ (Y * Z).trace) : Y ∈ endLat Λ := by
  intro l hl
  refine (hΛ.2.2.2.2 _).mp fun y hy => ?_
  rw [← trace_mul_rankOneHerm]
  exact hY _ (rankOneHerm_mem_endLat hΛ hl hy)

end GlobalTheory.LieDisc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEndLatticeOfTraceDualStatement
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_end_lattice_of_trace_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → (∀ Z ∈ endLat Λ, IsIntegral ℤ (Y * Z).trace) → Y ∈ endLat Λ := by
  first | exact @GlobalTheory.LieDisc.mem_endLat_of_trace_integral | exact GlobalTheory.LieDisc.mem_endLat_of_trace_integral | (intros; apply GlobalTheory.LieDisc.mem_endLat_of_trace_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfTraceIntegralUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfTraceIntegralUnramified
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
open scoped nonZeroDivisors

namespace GlobalTheory.LieDisc

theorem isIntegral_of_trace_integral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : E,
      (∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (w * a + cc (w * a))) → IsIntegral ℤ w := by
  intro E _ _ _ hu w hw
  set F := maximalRealSubfield E
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by
    haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hu
    infer_instance
  have hd : differentIdeal (𝓞 F) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have h := coeIdeal_differentIdeal (𝓞 F) F (L := E) (B := 𝓞 E)
    rw [hd, FractionalIdeal.coeIdeal_top] at h
    exact (inv_eq_one.1 h.symm)
  have hmem : w ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have ht := Formalism.FourierDecayAlt.P.S6x3.trace_eq E (w * algebraMap (𝓞 E) E b)
    have hi : IsIntegral ℤ (Algebra.trace F E (w * algebraMap (𝓞 E) E b)) := by
      rw [← isIntegral_algebraMap_iff (B := E), ht]
      exact hw _ (RingOfIntegers.isIntegral_coe b)
    exact ⟨⟨_, hi⟩, rfl⟩
  rw [hdual] at hmem
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

end GlobalTheory.LieDisc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfTraceIntegralUnramifiedStatement
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_trace_integral_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : E, (∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (w * a + cc (w * a))) → IsIntegral ℤ w := by
  first | exact @GlobalTheory.LieDisc.isIntegral_of_trace_integral | exact GlobalTheory.LieDisc.isIntegral_of_trace_integral | (intros; apply GlobalTheory.LieDisc.isIntegral_of_trace_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndLatticeTraceOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndLatticeTraceOne
noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => x a * ∑ k, G b k * cc (y k)

theorem rankOne_mulVec (G : Matrix (Fin r) (Fin r) E) (x y v : Fin r → E) :
    rankOne G x y *ᵥ v = herm G v y • x := by
  ext a
  simp only [rankOne, mulVec, dotProduct, of_apply, herm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem trace_rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    (rankOne G x y).trace = herm G x y := by
  simp only [Matrix.trace, diag, rankOne, of_apply, herm, Finset.mul_sum, mul_assoc]

def traceIdeal (Λ : Submodule (𝓞 E) (Fin r → E)) : Ideal (𝓞 E) where
  carrier := {s | ∃ Z ∈ endLat Λ, Z.trace = (s : E)}
  zero_mem' := ⟨0, (endLat Λ).zero_mem, by simp⟩
  add_mem' {s t} hs ht := by
    obtain ⟨Z, hZ, e⟩ := hs
    obtain ⟨Z', hZ', e'⟩ := ht
    exact ⟨Z + Z', (endLat Λ).add_mem hZ hZ', by rw [trace_add, e, e']; push_cast; rfl⟩
  smul_mem' c {s} hs := by
    obtain ⟨Z, hZ, e⟩ := hs
    refine ⟨(c : E) • Z, smul_mem_endLat c.isIntegral_coe hZ, ?_⟩
    rw [trace_smul, e, smul_eq_mul, smul_eq_mul]
    push_cast; rfl

theorem exists_endLat_trace_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hr : 1 ≤ r)
    (h : SelfDualLat G Λ) : ∃ Z ∈ endLat Λ, Z.trace = 1 := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm G x y) := fun x hx => (h.2.2.2.2 x).2 hx
  have htop : traceIdeal Λ = ⊤ := by
    by_contra hT
    refine GlobalTheory.UCls.Det.exists_herm_notMem hr h (traceIdeal Λ) hT fun x hx y hy =>
      ⟨⟨herm G x y, hint x hx y hy⟩, ⟨rankOne G x y, fun v hv => ?_, trace_rankOne G x y⟩, rfl⟩
    rw [rankOne_mulVec]
    exact smul_mem_of_isIntegral (hint v hv y hy) hx
  have h1 : (1 : 𝓞 E) ∈ traceIdeal Λ := htop ▸ Submodule.mem_top
  obtain ⟨Z, hZ, e⟩ := h1
  exact ⟨Z, hZ, by rw [e]; simp⟩

end GlobalTheory.LieDisc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndLatticeTraceOneStatement
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_end_lattice_trace_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → SelfDualLat G Λ → ∃ Z ∈ endLat Λ, Z.trace = 1 := by
  first | exact @GlobalTheory.LieDisc.exists_endLat_trace_eq_one | exact GlobalTheory.LieDisc.exists_endLat_trace_eq_one | (intros; apply GlobalTheory.LieDisc.exists_endLat_trace_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointProperties
noncomputable section

namespace GlobalTheory.LieDisc.HAdjAlg

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem map_mul_cc (A B : Matrix (Fin r) (Fin r) E) : (A * B).map cc = A.map cc * B.map cc :=
  Matrix.map_mul (f := (IsCMField.complexConj E : E →+* E))

theorem map_map_cc (A : Matrix (Fin r) (Fin r) E) : (A.map cc).map cc = A := by
  ext i j; simp [cc_cc]

theorem herm_eq_dot (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cc_mulVec (A : Matrix (Fin r) (Fin r) E) (y : Fin r → E) :
    (fun b => cc ((A *ᵥ y) b)) = A.map cc *ᵥ fun b => cc (y b) := by
  ext i; simp [mulVec, dotProduct, cc, map_sum, map_mul]

theorem map_one_cc : (1 : Matrix (Fin r) (Fin r) E).map cc = 1 := by
  exact Matrix.map_one cc (by simp [cc]) (by simp [cc])

theorem map_smul_cc (c : E) (A : Matrix (Fin r) (Fin r) E) : (c • A).map cc = cc c • A.map cc := by
  ext i j; simp [cc, map_mul]

theorem trace_map_cc (A : Matrix (Fin r) (Fin r) E) : (A.map cc).trace = cc A.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, cc, map_sum]

end GlobalTheory.LieDisc.HAdjAlg

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc GlobalTheory.LieDisc.HAdjAlg

theorem GlobalTheory.LieDisc.hAdj_algebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ (Y : Matrix (Fin r) (Fin r) E) (x y : Fin r → E), herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y)) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y * Z) = hAdj G Z * hAdj G Y) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y + Z) = hAdj G Y + hAdj G Z) ∧ (∀ (c : E) (Y : Matrix (Fin r) (Fin r) E), hAdj G (c • Y) = cc c • hAdj G Y) ∧ hAdj G 1 = 1 ∧ (∀ Y : Matrix (Fin r) (Fin r) E, hAdj G (hAdj G Y) = Y) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, (hAdj G Y).trace = cc Y.trace) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, IsSkew G Y ↔ hAdj G Y = -Y) := by
  intro E _ _ _ r G hG hdet
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  have hGi : G * G⁻¹ = 1 := mul_nonsing_inv G hu
  have hiG : G⁻¹ * G = 1 := nonsing_inv_mul G hu
  have hGt : G.map cc = Gᵀ := by ext a b; simp [hG]
  have adj1 : ∀ (Y : Matrix (Fin r) (Fin r) E) (x y : Fin r → E),
      herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y) := by
    intro Y x y
    rw [herm_eq_dot, herm_eq_dot, cc_mulVec, hAdj, map_map_cc, mulVec_mulVec,
      show G * (G⁻¹ * Yᵀ * G) = Yᵀ * G by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGi, Matrix.one_mul],
      ← mulVec_mulVec, dotProduct_mulVec x Yᵀ, vecMul_transpose]
  refine ⟨adj1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y Z
    rw [hAdj, hAdj, hAdj, ← map_mul_cc, transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]
  · intro Y Z
    simp only [hAdj, transpose_add, Matrix.mul_add, Matrix.add_mul]
    ext i j; simp [cc]
  · intro c Y
    rw [hAdj, hAdj, ← map_smul_cc, transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hAdj, transpose_one, Matrix.mul_one, hiG, map_one_cc]
  · intro Y
    have h1 : (G⁻¹).map cc * Gᵀ = 1 := by rw [← hGt, ← map_mul_cc, hiG, map_one_cc]
    have h2 : (G⁻¹)ᵀ * Gᵀ = 1 := by rw [← transpose_mul, hGi, transpose_one]
    rw [hAdj, hAdj, map_mul_cc, map_mul_cc, hGt, ← transpose_map, map_map_cc, transpose_mul, transpose_mul,
      transpose_transpose]
    calc _ = ((G⁻¹).map cc * Gᵀ) * Y * (G⁻¹ᵀ * Gᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = Y := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  · intro Y
    rw [hAdj, trace_map_cc, trace_mul_comm, ← Matrix.mul_assoc, hGi, Matrix.one_mul, trace_transpose]
  · intro Y
    have hadd : ∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = herm G u ((hAdj G Y + Y) *ᵥ w) := by
      intro u w
      rw [adj1, herm_eq_dot, herm_eq_dot, herm_eq_dot, ← dotProduct_add, ← mulVec_add]
      congr 2
      ext b; simp [add_mulVec, cc, map_add (f := _)]
    constructor
    · intro hs
      have hv : ∀ w, (hAdj G Y + Y) *ᵥ w = 0 := by
        intro w
        set v := (hAdj G Y + Y) *ᵥ w
        have h0 : ∀ u, herm G u v = 0 := fun u => by rw [← hadd]; exact hs u w
        have hGv : G *ᵥ (fun b => cc (v b)) = 0 := by
          ext i
          have := h0 (Pi.single i 1)
          rw [herm_eq_dot, single_dotProduct, one_mul] at this
          simpa using this
        have hcv : (fun b => cc (v b)) = 0 := by
          rw [← one_mulVec (fun b => cc (v b)), ← hiG, ← mulVec_mulVec, hGv, mulVec_zero]
        ext b
        have := congrFun hcv b
        simp only [Pi.zero_apply] at this
        rw [← cc_cc (v b), this]; simp [cc]
      have hA : hAdj G Y + Y = 0 := by
        ext i j
        have := congrFun (hv (Pi.single j 1)) i
        simpa [mulVec_single] using this
      exact eq_neg_of_add_eq_zero_left hA
    · intro h u w
      rw [hadd, h, neg_add_cancel, zero_mulVec]
      simp [herm, cc]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointPropertiesStatement
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_adjoint_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ (Y : Matrix (Fin r) (Fin r) E) (x y : Fin r → E), herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y)) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y * Z) = hAdj G Z * hAdj G Y) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y + Z) = hAdj G Y + hAdj G Z) ∧ (∀ (c : E) (Y : Matrix (Fin r) (Fin r) E), hAdj G (c • Y) = cc c • hAdj G Y) ∧ hAdj G 1 = 1 ∧ (∀ Y : Matrix (Fin r) (Fin r) E, hAdj G (hAdj G Y) = Y) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, (hAdj G Y).trace = cc Y.trace) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, IsSkew G Y ↔ hAdj G Y = -Y) := by
  first | exact @GlobalTheory.LieDisc.hAdj_algebra | exact GlobalTheory.LieDisc.hAdj_algebra | (intros; apply GlobalTheory.LieDisc.hAdj_algebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointMemEndLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointMemEndLattice
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp only [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cc_map_mulVec (M : Matrix (Fin r) (Fin r) E) (y : Fin r → E) :
    (fun b => cc ((M.map cc *ᵥ y) b)) = M *ᵥ fun b => cc (y b) := by
  funext b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_apply, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply]

theorem herm_mulVec_left_eq (G Y : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (x y : Fin r → E) :
    herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y) := by
  rw [herm_eq_dotProduct, herm_eq_dotProduct, hAdj, cc_map_mulVec, mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hG), Matrix.one_mul,
    ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_transpose]
  exact (dotProduct_mulVec _ _ _).symm

theorem hAdj_mem_endLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (Y : Matrix (Fin r) (Fin r) E) (h : SelfDualLat G Λ) (hY : Y ∈ endLat Λ) : hAdj G Y ∈ endLat Λ := by
  obtain ⟨hGh, hdet, -, -, hsd⟩ := h
  intro y hy
  refine (hsd _).1 fun x hx => ?_
  have h1 : IsIntegral ℤ (herm G x (hAdj G Y *ᵥ y)) := by
    rw [← herm_mulVec_left_eq G Y hdet]
    exact (hsd (Y *ᵥ x)).2 (hY x hx) y hy
  rw [← GlobalTheory.UCls.Det.herm_symm G hGh]
  exact h1.map (IsCMField.complexConj E)

end GlobalTheory.LieDisc

theorem GlobalTheory.LieDisc.hAdj_mem_endLat_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → hAdj G Y ∈ endLat Λ :=
  fun _ _ _ _ r G Λ Y h hY => GlobalTheory.LieDisc.hAdj_mem_endLat G Λ Y h hY
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointMemEndLatticeStatement
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_adjoint_mem_end_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → hAdj G Y ∈ endLat Λ := by
  first | exact @GlobalTheory.LieDisc.hAdj_mem_endLat_main | exact GlobalTheory.LieDisc.hAdj_mem_endLat_main | (intros; apply GlobalTheory.LieDisc.hAdj_mem_endLat_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndex
noncomputable section

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem trace_trProj (hr : r ≠ 0) (Y : Matrix (Fin r) (Fin r) E) : (trProj Y).trace = 0 := by
  have : (r : E) ≠ 0 := by exact_mod_cast hr
  simp only [trProj, trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  field_simp; ring

theorem cc_trace_of_isSkew {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Z : Matrix (Fin r) (Fin r) E} (hZ : IsSkew G Z) : cc Z.trace = -Z.trace := by
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [← h7, (h8 Z).1 hZ, trace_neg]

theorem isSkew_sub_smul {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Z : Matrix (Fin r) (Fin r) E} (hZ : IsSkew G Z) {c : E} (hc : cc c = -c) : IsSkew G (Z - c • 1) := by
  obtain ⟨-, -, h3, h4, h5, -, -, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [h8, sub_eq_add_neg, h3, ← neg_smul, h4, h5, (h8 Z).1 hZ]
  have e : cc (-c) = c := by simp only [cc, map_neg] at hc ⊢; rw [hc, neg_neg]
  rw [e, neg_add, neg_smul, neg_neg]

theorem cc_trace_div {Z : Matrix (Fin r) (Fin r) E} (h : cc Z.trace = -Z.trace) :
    cc (Z.trace / r) = -(Z.trace / r) := by
  simp only [cc, map_div₀, map_natCast] at h ⊢
  rw [h, neg_div]

theorem trProj_mem_dualLie (hr : r ≠ 0) {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hS : SelfDualLat G Λ) {Z : Matrix (Fin r) (Fin r) E} (hZ : Z ∈ skewLat G Λ) : trProj Z ∈ dualLie G Λ := by
  refine ⟨trace_trProj hr Z, isSkew_sub_smul hS.1 hS.2.1 hZ.1 (cc_trace_div
    (cc_trace_of_isSkew hS.1 hS.2.1 hZ.1)), fun X hX => ?_⟩
  have h1 : (X * trProj Z).trace = (X * Z).trace := by
    simp only [trProj, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul, hX.1,
      smul_zero, sub_zero]
  rw [h1]
  exact GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS (mul_mem_endLat hX.2.2 hZ.2)

end GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hAdj_sub {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (Y Z : Matrix (Fin r) (Fin r) E) : hAdj G (Y - Z) = hAdj G Y - hAdj G Z := by
  obtain ⟨-, -, h3, h4, -, -, -, -⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [sub_eq_add_neg, h3, ← neg_one_smul E Z, h4, sub_eq_add_neg, ← neg_one_smul E (hAdj G Z)]
  congr 2
  simp [cc]

theorem trace_mul_hAdj {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Y : Matrix (Fin r) (Fin r) E} (hY : IsSkew G Y) (W : Matrix (Fin r) (Fin r) E) :
    (Y * hAdj G W).trace = -cc (Y * W).trace := by
  obtain ⟨-, h2, -, -, -, -, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  have hY' : Y = -hAdj G Y := by rw [(h8 Y).1 hY, neg_neg]
  conv_lhs => rw [hY']
  rw [Matrix.neg_mul, ← h2, trace_neg, h7, trace_mul_comm W Y]

theorem isIntegral_trace_mul_of_trace_eq_zero (hU : Unr E) {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hS : SelfDualLat G Λ) {Y : Matrix (Fin r) (Fin r) E}
    (hY : Y ∈ dualLie G Λ) {Z : Matrix (Fin r) (Fin r) E} (hZ : Z ∈ endLat Λ) (hZ0 : Z.trace = 0) :
    IsIntegral ℤ (Y * Z).trace := by
  obtain ⟨-, -, -, h4, -, h6, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1
  refine GlobalTheory.T.integral_of_trace_integral_unramified E hU _ fun a ha => ?_
  set X := a • Z - hAdj G (a • Z) with hXdef
  have hX : X ∈ lieLat G Λ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [trace_sub, h7, trace_smul, hZ0, smul_zero, sub_eq_zero]; simp [cc]
    · show IsSkew G X
      rw [h8, hXdef, hAdj_sub hS.1 hS.2.1, h6, neg_sub]
    · exact (endLat Λ).sub_mem (smul_mem_endLat ha hZ) (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ _ hS (smul_mem_endLat ha hZ))
  have h := hY.2.2 X hX
  rw [trace_mul_comm, hXdef, Matrix.mul_sub, trace_sub, trace_mul_hAdj hS.1 hS.2.1 hY.2.1,
    Matrix.mul_smul, trace_smul, smul_eq_mul, sub_neg_eq_add] at h
  convert h using 2 <;> ring_nf

end GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem trace_hAdj_one {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Z : Matrix (Fin r) (Fin r) E} (hZ : Z.trace = 1) : (hAdj G Z).trace = 1 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [h7, hZ]; simp [cc]

theorem exists_skewLat_trProj_eq (hr : r ≠ 0) (hU : Unr E) {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hS : SelfDualLat G Λ) {Y : Matrix (Fin r) (Fin r) E}
    (hY : Y ∈ dualLie G Λ) : ∃ Z ∈ skewLat G Λ, trProj Z = Y := by
  obtain ⟨-, -, h3, h4, h5, -, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1
  obtain ⟨Z₁, hZ₁, hZ₁1⟩ := GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS
  set c₀ := -(Y * Z₁).trace with hc₀

  have hb : ∀ Z ∈ endLat Λ, IsIntegral ℤ ((Y * Z).trace + c₀ * Z.trace) := by
    intro Z hZ
    have hZt := GlobalTheory.T.end_lattice_trace_integral E r G Λ Z hS hZ
    have hm : Z - Z.trace • Z₁ ∈ endLat Λ := (endLat Λ).sub_mem hZ (smul_mem_endLat hZt hZ₁)
    have h0 : (Z - Z.trace • Z₁).trace = 0 := by
      rw [trace_sub, trace_smul, hZ₁1, smul_eq_mul, mul_one, sub_self]
    have := isIntegral_trace_mul_of_trace_eq_zero hU hS hY hm h0
    rw [Matrix.mul_sub, Matrix.mul_smul, trace_sub, trace_smul, smul_eq_mul] at this
    convert this using 1; rw [hc₀]; ring

  have hs : IsIntegral ℤ (c₀ + cc c₀) := by
    have := hb _ (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ Z₁ hS hZ₁)
    rw [trace_mul_hAdj hS.1 hS.2.1 hY.2.1, trace_hAdj_one hS.1 hS.2.1 hZ₁1, mul_one] at this
    convert this using 1
    rw [hc₀]; simp only [cc, map_neg]; ring
  obtain ⟨t, ht, ht1⟩ := GlobalTheory.T.exists_integral_trace_one_unramified E hU
  set s := c₀ + cc c₀ with hsdef
  set c := c₀ - s * t with hcdef
  have hccs : cc s = s := by rw [hsdef]; simp only [cc, map_add (f := _), IsCMField.complexConj_apply_apply]; ring
  have hcc : cc c = -c := by
    have e1 : cc c = cc c₀ - s * cc t := by
      rw [hcdef]; simp only [cc, map_sub, map_mul] at hccs ⊢; rw [hccs]
    rw [e1, hcdef]
    have e2 : cc t = 1 - t := by rw [← ht1]; ring
    rw [e2, hsdef]; ring
  refine ⟨Y + c • 1, ⟨?_, ?_⟩, ?_⟩
  · rw [h8, h3, h4, h5, (h8 Y).1 hY.2.1, hcc, neg_add, neg_smul]
  · refine GlobalTheory.T.mem_end_lattice_of_trace_dual E r G Λ _ hS fun Z hZ => ?_
    have e : ((Y + c • 1) * Z).trace = ((Y * Z).trace + c₀ * Z.trace) - s * t * Z.trace := by
      rw [Matrix.add_mul, trace_add, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul, hcdef]; ring
    rw [e]
    exact (hb Z hZ).sub ((hs.mul ht).mul (GlobalTheory.T.end_lattice_trace_integral E r G Λ Z hS hZ))
  · have hrE : (r : E) ≠ 0 := by exact_mod_cast hr
    simp only [trProj, trace_add, hY.1, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, zero_add]
    rw [mul_div_assoc, div_self hrE, mul_one, add_sub_cancel_right]

end GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def trProjHom (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    skewLat G Λ →+ Matrix (Fin r) (Fin r) E where
  toFun Z := trProj (Z : Matrix (Fin r) (Fin r) E)
  map_zero' := by simp [trProj]
  map_add' Y Z := by
    simp only [trProj, AddSubgroup.coe_add, trace_add, add_div, add_smul]; abel

def traceHom (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) : skewLat G Λ →+ E where
  toFun Z := (Z : Matrix (Fin r) (Fin r) E).trace
  map_zero' := by simp
  map_add' Y Z := by simp [trace_add]

theorem trProj_mem_lieLat_iff (hr : r ≠ 0) {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hS : SelfDualLat G Λ) {Z : Matrix (Fin r) (Fin r) E} (hZ : Z ∈ skewLat G Λ) :
    trProj Z ∈ lieLat G Λ ↔ Z.trace ∈ AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E) := by
  have hrE : (r : E) ≠ 0 := by exact_mod_cast hr
  have hD := trProj_mem_dualLie hr hS hZ
  constructor
  · intro h
    have hm : (Z.trace / r) • (1 : Matrix (Fin r) (Fin r) E) ∈ endLat Λ := by
      have := (endLat Λ).sub_mem hZ.2 h.2.2
      simpa [trProj] using this
    obtain ⟨Z₁, hZ₁, hZ₁1⟩ := GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS
    have hi : IsIntegral ℤ (Z.trace / r) := by
      have := GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS (mul_mem_endLat hm hZ₁)
      rwa [Matrix.smul_mul, Matrix.one_mul, trace_smul, hZ₁1, smul_eq_mul, mul_one] at this
    refine ⟨Z.trace / r, ⟨hi, cc_trace_div (cc_trace_of_isSkew hS.1 hS.2.1 hZ.1)⟩, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft]
    field_simp
  · rintro ⟨b, hb, hbe⟩
    simp only [AddMonoidHom.coe_mulLeft] at hbe
    have e : trProj Z = Z - b • (1 : Matrix (Fin r) (Fin r) E) := by
      rw [trProj, ← hbe, mul_div_cancel_left₀ _ hrE]
    refine ⟨hD.1, hD.2.1, ?_⟩
    rw [e]
    exact (endLat Λ).sub_mem hZ.2 (smul_mem_endLat hb.1 one_mem_endLat)

theorem traceHom_surj (hr : r ≠ 0) (hU : Unr E) {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hS : SelfDualLat G Λ) {b : E} (hb : b ∈ imLat E) : ∃ Z ∈ skewLat G Λ, Z.trace = b := by
  obtain ⟨-, -, -, -, -, h6, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1
  obtain ⟨Z₁, hZ₁, hZ₁1⟩ := GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS
  obtain ⟨t, ht, ht1⟩ := GlobalTheory.T.exists_integral_trace_one_unramified E hU
  have hbt : IsIntegral ℤ (b * t) := hb.1.mul ht
  refine ⟨(b * t) • Z₁ - hAdj G ((b * t) • Z₁), ⟨?_, ?_⟩, ?_⟩
  · rw [h8, hAdj_sub hS.1 hS.2.1, h6, neg_sub]
  · exact (endLat Λ).sub_mem (smul_mem_endLat hbt hZ₁) (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ _ hS (smul_mem_endLat hbt hZ₁))
  · rw [trace_sub, h7, trace_smul, hZ₁1, smul_eq_mul, mul_one]
    have hb2 := hb.2
    simp only [cc, map_mul] at hb2 ⊢
    rw [hb2]
    have e2 : IsCMField.complexConj E t = 1 - t := by
      have := ht1; simp only [cc] at this; rw [← this]; ring
    rw [e2]; ring

theorem relIndex_lieLat_dualLie (hr : r ≠ 0) (hU : Unr E) {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hS : SelfDualLat G Λ) :
    (lieLat G Λ).relIndex (dualLie G Λ) =
      (AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E)).relIndex (imLat E) := by
  let f : skewLat G Λ →+ dualLie G Λ :=
    (trProjHom G Λ).codRestrict (dualLie G Λ) fun Z => trProj_mem_dualLie hr hS Z.2
  let g : skewLat G Λ →+ imLat E :=
    (traceHom G Λ).codRestrict (imLat E) fun Z =>
      ⟨GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS Z.2.2, cc_trace_of_isSkew hS.1 hS.2.1 Z.2.1⟩
  have hf : Function.Surjective f := by
    rintro ⟨Y, hY⟩
    obtain ⟨Z, hZ, e⟩ := exists_skewLat_trProj_eq hr hU hS hY
    exact ⟨⟨Z, hZ⟩, Subtype.ext e⟩
  have hg : Function.Surjective g := by
    rintro ⟨b, hb⟩
    obtain ⟨Z, hZ, e⟩ := traceHom_surj hr hU hS hb
    exact ⟨⟨Z, hZ⟩, Subtype.ext e⟩
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_comap_of_surjective _ hf, ← AddSubgroup.index_comap_of_surjective _ hg]
  congr 1
  ext Z
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
  exact trProj_mem_lieLat_iff hr hS Z.2

end GlobalTheory.LieDisc

namespace GlobalTheory

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem lieLat_relIndex_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ →
    (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧
      (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧
      ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) = r ^ fdeg E := by
  intro E _ _ _ r G Λ hr hU hS
  have hr0 : r ≠ 0 := by omega
  rw [LieDisc.closure_dualLie, LieDisc.relIndex_lieLat_dualLie hr0 hU hS]
  exact GlobalTheory.T.imaginary_lattice_scaling_index E r hU (by omega)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndexStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_dual_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) = r ^ fdeg E := by
  first | exact @GlobalTheory.lieLat_relIndex_dual | exact GlobalTheory.lieLat_relIndex_dual | (intros; apply GlobalTheory.lieLat_relIndex_dual <;> assumption)
end
