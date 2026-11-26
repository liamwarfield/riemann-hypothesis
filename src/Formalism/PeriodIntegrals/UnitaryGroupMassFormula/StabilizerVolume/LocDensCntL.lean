module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoGram

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCntRes
noncomputable section

namespace PI.VolStabS

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Res

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

abbrev iO (a : 𝓞 F) : Fv F v := algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)

theorem vcoe (x : F) : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem lt_one_iff_le_expm1 (g : WithZero (Multiplicative ℤ)) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rw [← WithZero.exp_log hg, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem v_iO_le (a : 𝓞 F) : Valued.v (iO v a) ≤ 1 := by
  rw [vcoe]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v a

theorem v_iO_lt_iff (a : 𝓞 F) : Valued.v (iO v a) < 1 ↔ a ∈ v.asIdeal := by
  rw [vcoe]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v a

theorem exists_appr {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 := by
  have hx1 : Valued.v x ≤ 1 := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hx
  have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) F v
  have hnhds : {y : Fv F v | Valued.v (y - x) < 1} ∈ 𝓝 x :=
    Valued.mem_nhds.mpr ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, k, rfl⟩ := mem_closure_iff_nhds.mp (hd x) _ hnhds
  simp only [Set.mem_setOf_eq] at hy
  have hk' : Valued.v (algebraMap F (Fv F v) k) ≤ 1 := by
    have e : algebraMap F (Fv F v) k = (algebraMap F (Fv F v) k - x) + x := by ring
    rw [e]
    exact le_trans (Valuation.map_add _ _ _) (max_le hy.le hx1)
  have hk : v.valuation F k ≤ 1 := by rw [← vcoe]; exact hk'
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hk 1
  refine ⟨a, ?_⟩
  have e : x - iO v a = (x - algebraMap F (Fv F v) k) + -(iO v a - algebraMap F (Fv F v) k) := by ring
  have e2 : iO v a - algebraMap F (Fv F v) k = algebraMap F (Fv F v) (algebraMap (𝓞 F) F a - k) := by
    simp [iO, map_sub]
  rw [e]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
  · rw [Valuation.map_sub_swap]
    exact hy
  · rw [Valuation.map_neg, e2, vcoe]
    simpa using ha


open Classical in
def appr (x : Fv F v) : 𝓞 F :=
  if h : ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 then h.choose else 0

theorem appr_spec {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v (x - iO v (appr v x)) < 1 := by
  have h := exists_appr v hx
  unfold appr
  rw [dite_eq_left h]
  exact h.choose_spec

def red (x : Fv F v) : 𝓞 F ⧸ v.asIdeal := Ideal.Quotient.mk _ (appr v x)

theorem red_eq_mk_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (a : 𝓞 F) :
    red v x = Ideal.Quotient.mk _ a ↔ Valued.v (x - iO v a) < 1 := by
  have hs := appr_spec v hx
  unfold red
  rw [Ideal.Quotient.eq, ← v_iO_lt_iff]
  have e : iO v (appr v x - a) = (x - iO v a) - (x - iO v (appr v x)) := by
    simp only [iO, map_sub]
    ring
  rw [e]
  constructor
  · intro h
    have e2 : x - iO v a = (x - iO v (appr v x)) + ((x - iO v a) - (x - iO v (appr v x))) := by ring
    rw [e2]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hs h)
  · intro h
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h hs)

theorem mem_O_iO (a : 𝓞 F) : iO v a ∈ v.adicCompletionIntegers F := by
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr (v_iO_le v a)

theorem red_iO (a : 𝓞 F) : red v (iO v a) = Ideal.Quotient.mk _ a := by
  refine (red_eq_mk_iff v (mem_O_iO v a) a).mpr ?_
  rw [sub_self, map_zero]
  exact zero_lt_one

theorem red_add {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x + y) = red v x + red v y := by
  have hxy : x + y ∈ v.adicCompletionIntegers F := add_mem hx hy
  have e1 : red v x + red v y = Ideal.Quotient.mk _ (appr v x + appr v y) := by
    simp only [red, map_add (f := _)]
  rw [e1, red_eq_mk_iff v hxy]
  have e : x + y - iO v (appr v x + appr v y) = (x - iO v (appr v x)) + (y - iO v (appr v y)) := by
    simp only [iO, map_add (f := _)]
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (appr_spec v hx) (appr_spec v hy))

theorem red_mul {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x * y) = red v x * red v y := by
  have hxy : x * y ∈ v.adicCompletionIntegers F := mul_mem hx hy
  have e1 : red v x * red v y = Ideal.Quotient.mk _ (appr v x * appr v y) := by
    simp only [red, map_mul]
  rw [e1, red_eq_mk_iff v hxy]
  have e : x * y - iO v (appr v x * appr v y) =
      (x - iO v (appr v x)) * y + iO v (appr v x) * (y - iO v (appr v y)) := by
    simp only [iO, map_mul]
    ring
  rw [e]
  have hy1 : Valued.v y ≤ 1 := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hy
  have ha1 : Valued.v (iO v (appr v x)) ≤ 1 := v_iO_le v _
  apply lt_of_le_of_lt (Valuation.map_add _ _ _)
  apply max_lt
  · rw [map_mul]
    calc Valued.v (x - iO v (appr v x)) * Valued.v y ≤ Valued.v (x - iO v (appr v x)) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact appr_spec v hx
  · rw [map_mul]
    calc Valued.v (iO v (appr v x)) * Valued.v (y - iO v (appr v y)) ≤ 1 * Valued.v (y - iO v (appr v y)) := by
          gcongr
      _ < 1 := by rw [one_mul]; exact appr_spec v hy

theorem red_one : red v 1 = 1 := by
  have h := (red_eq_mk_iff v (one_mem _) 1).mpr (by simp [iO])
  rw [h, map_one]

theorem red_eq_zero_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    red v x = 0 ↔ Valued.v x < 1 := by
  rw [← map_zero (Ideal.Quotient.mk v.asIdeal), red_eq_mk_iff v hx]
  simp [iO]

theorem red_zero : red v 0 = 0 := by
  have h := (red_eq_mk_iff v (zero_mem _) 0).mpr (by simp [iO])
  rw [h, map_zero]

theorem red_neg {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : red v (-x) = -red v x := by
  have hn : -x ∈ v.adicCompletionIntegers F := neg_mem hx
  have e1 : -red v x = Ideal.Quotient.mk _ (-appr v x) := by
    simp only [red, map_neg]
  rw [e1, red_eq_mk_iff v hn]
  have e : -x - iO v (-appr v x) = -(x - iO v (appr v x)) := by
    simp only [iO, map_neg]
    ring
  rw [e, Valuation.map_neg]
  exact appr_spec v hx

theorem red_surj (t : 𝓞 F ⧸ v.asIdeal) : ∃ x ∈ v.adicCompletionIntegers F, red v x = t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  exact ⟨iO v a, mem_O_iO v a, red_iO v a⟩

theorem lt_one_iff_unif (x : Fv F v) :
    Valued.v x < 1 ↔ Valued.v ((unifV v)⁻¹ * x) ≤ 1 := by
  have hne : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [map_mul, map_inv₀, unifV_val, lt_one_iff_le_expm1]
  constructor
  · intro h
    calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v x ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) :=
          by gcongr
      _ = 1 := inv_mul_cancel₀ hne
  · intro h
    have h2 : WithZero.exp (-1 : ℤ) * ((WithZero.exp (-1 : ℤ))⁻¹ * Valued.v x) ≤ WithZero.exp (-1 : ℤ) * 1 := by
      gcongr
    rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_one] at h2

theorem ev_int (x : F) : ∀ᶠ v in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have hfin := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x
  refine Filter.eventually_cofinite.mpr (hfin.subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F w, vcoe, not_le] at hw
  exact hw

theorem ev_unit {x : F} (hx : x ≠ 0) : ∀ᶠ v in cofinite,
    Valued.v (algebraMap F (Fv F v) x) = 1 := by
  have h1 := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x
  have h2 := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x⁻¹
  refine Filter.eventually_cofinite.mpr ((h1.union h2).subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  rw [vcoe] at hw
  rcases lt_or_gt_of_ne hw with h | h
  · right
    show 1 < w.valuation F x⁻¹
    rw [map_inv₀]
    exact one_lt_inv_iff₀.mpr ⟨by
      rw [zero_lt_iff]
      exact (Valuation.ne_zero_iff _).mpr hx, h⟩
  · left
    exact h

end Res

section Count

theorem measure_count {G V : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup V] [Finite V] (μ : Measure G) [μ.IsAddLeftInvariant] (L N : AddSubgroup G)
    (hNL : N ≤ L) (hN : MeasurableSet (N : Set G)) (φ : G → V)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, φ (x + y) = φ x + φ y) (hker : ∀ x ∈ L, φ x = 0 ↔ x ∈ N)
    (hsurj : ∀ w, ∃ x ∈ L, φ x = w) (S : Set V) :
    μ {x | x ∈ L ∧ φ x ∈ S} = (Nat.card S : ENNReal) * μ N := by
  classical
  choose xw hxwL hxw using hsurj
  have hS : S.Finite := Set.toFinite S
  have key : ∀ w x, -xw w + x ∈ (N : Set G) → x ∈ L ∧ φ x = w := by
    intro w x hn
    have hnL : -xw w + x ∈ L := hNL hn
    have e : xw w + (-xw w + x) = x := by abel
    have hxL : x ∈ L := by
      have h2 := add_mem (hxwL w) hnL
      rwa [e] at h2
    refine ⟨hxL, ?_⟩
    have h1 := hadd (xw w) (hxwL w) (-xw w + x) hnL
    rw [e, hxw, (hker _ hnL).mpr hn, add_zero] at h1
    exact h1
  have hset : {x | x ∈ L ∧ φ x ∈ S} = ⋃ w ∈ hS.toFinset, (fun n => -xw w + n) ⁻¹' (N : Set G) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨hxL, hxS⟩
      refine ⟨φ x, hxS, ?_⟩
      have hneg : -xw (φ x) ∈ L := neg_mem (hxwL _)
      have hm : -xw (φ x) + x ∈ L := add_mem hneg hxL
      rw [SetLike.mem_coe, ← hker _ hm]
      have h1 := hadd (-xw (φ x) + x) hm (xw (φ x)) (hxwL _)
      have e : -xw (φ x) + x + xw (φ x) = x := by abel
      rw [e, hxw] at h1
      exact (add_eq_right.mp h1.symm)
    · rintro ⟨w, hwS, hn⟩
      obtain ⟨hxL, hφ⟩ := key w x hn
      exact ⟨hxL, hφ ▸ hwS⟩
  have hd : (↑hS.toFinset : Set V).PairwiseDisjoint (fun w => (fun n => -xw w + n) ⁻¹' (N : Set G)) := by
    intro w _ w' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    exact hne ((key w x hx).2.symm.trans (key w' x hx').2)
  have hm : ∀ w ∈ hS.toFinset, MeasurableSet ((fun n => -xw w + n) ⁻¹' (N : Set G)) :=
    fun w _ => measurable_const_add _ hN
  rw [hset, measure_biUnion_finset hd hm]
  simp only [measure_preimage_add]
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_finite_toFinset hS]

end Count

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

structure AntiB (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) where
  δ : E
  D0 : F
  c : Module.Basis (Fin 2) F E
  hc0 : c 0 = 1
  hc1 : c 1 = δ
  hδ : δ * δ = algebraMap F E D0
  hσδ : σ δ = -δ
  hD0 : D0 ≠ 0

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem repr_change {ι ι' : Type} [Fintype ι'] (b : Module.Basis ι F E)
    (c : Module.Basis ι' F E) (z : Fv F v ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr z k =
      ∑ j, (Algebra.TensorProduct.basis (Fv F v) c).repr z j *
        algebraMap F (Fv F v) (b.repr (c j) k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) c).sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_repr_tmul, mul_comm]

theorem int_iff {ι ι' : Type} [Fintype ι] [Fintype ι'] (b : Module.Basis ι F E)
    (c : Module.Basis ι' F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (z : Fv F v ⊗[F] E) :
    (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k ∈ v.adicCompletionIntegers F) ↔
      (∀ j, (Algebra.TensorProduct.basis (Fv F v) c).repr z j ∈ v.adicCompletionIntegers F) := by
  constructor
  · intro h j
    rw [repr_change v c b z j]
    exact sum_mem (fun k _ => mul_mem (h k) (hcb k j))
  · intro h k
    rw [repr_change v b c z k]
    exact sum_mem (fun j _ => mul_mem (h j) (hbc j k))

variable {σ : E →ₐ[F] E} (A : AntiB F E σ)

abbrev Pt (x y : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ (1 : E) + y ⊗ₜ A.δ

abbrev Xc (z : Fv F v ⊗[F] E) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) A.c).repr z 0

abbrev Yc (z : Fv F v ⊗[F] E) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) A.c).repr z 1

theorem repr_Pt (x y : Fv F v) :
    (Algebra.TensorProduct.basis (Fv F v) A.c).repr (Pt v A x y) = Finsupp.single 0 x + Finsupp.single 1 y := by
  have h1 : A.c.repr 1 = Finsupp.single 0 1 := by rw [← A.hc0, Module.Basis.repr_self]
  have h2 : A.c.repr A.δ = Finsupp.single 1 1 := by rw [← A.hc1, Module.Basis.repr_self]
  rw [Pt, map_add (f := _), Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul, h1, h2]
  simp

theorem Xc_Pt (x y : Fv F v) : Xc v A (Pt v A x y) = x := by
  simp only [Xc, repr_Pt]
  simp

theorem Yc_Pt (x y : Fv F v) : Yc v A (Pt v A x y) = y := by
  simp only [Yc, repr_Pt]
  simp

theorem decomp (z : Fv F v ⊗[F] E) : z = Pt v A (Xc v A z) (Yc v A z) := by
  apply (Algebra.TensorProduct.basis (Fv F v) A.c).repr.injective
  rw [repr_Pt]
  ext i
  fin_cases i <;> simp

theorem Pt_mul (x y x' y' : Fv F v) :
    Pt v A x y * Pt v A x' y' =
      Pt v A (x * x' + y * y' * algebraMap F (Fv F v) A.D0) (x * y' + y * x') := by
  simp only [Pt, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, A.hδ, TensorProduct.add_tmul]
  rw [Algebra.algebraMap_eq_smul_one A.D0, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
    mul_comm (algebraMap F (Fv F v) A.D0)]
  abel

theorem one_eq_Pt : (1 : Fv F v ⊗[F] E) = Pt v A 1 0 := by
  simp [Pt, Algebra.TensorProduct.one_def]

theorem sig_Pt (x y : Fv F v) : sigR (Fv F v) σ (Pt v A x y) = Pt v A x (-y) := by
  simp [Pt, sigR, Algebra.TensorProduct.map_tmul, A.hσδ, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

theorem Xc_mul (z w : Fv F v ⊗[F] E) :
    Xc v A (z * w) = Xc v A z * Xc v A w + Yc v A z * Yc v A w * algebraMap F (Fv F v) A.D0 := by
  conv_lhs => rw [decomp v A z, decomp v A w]
  rw [Pt_mul, Xc_Pt]

theorem Yc_mul (z w : Fv F v ⊗[F] E) :
    Yc v A (z * w) = Xc v A z * Yc v A w + Yc v A z * Xc v A w := by
  conv_lhs => rw [decomp v A z, decomp v A w]
  rw [Pt_mul, Yc_Pt]

theorem Xc_sig (z : Fv F v ⊗[F] E) : Xc v A (sigR (Fv F v) σ z) = Xc v A z := by
  conv_lhs => rw [decomp v A z]
  rw [sig_Pt, Xc_Pt]

theorem Yc_sig (z : Fv F v ⊗[F] E) : Yc v A (sigR (Fv F v) σ z) = -Yc v A z := by
  conv_lhs => rw [decomp v A z]
  rw [sig_Pt, Yc_Pt]

theorem Xc_one : Xc v A 1 = 1 := by
  rw [one_eq_Pt v A, Xc_Pt]

theorem Yc_one : Yc v A 1 = 0 := by
  rw [one_eq_Pt v A, Yc_Pt]

theorem repr_incl (e : E) (j : Fin 2) :
    (Algebra.TensorProduct.basis (Fv F v) A.c).repr (inclR (Fv F v) e) j =
      algebraMap F (Fv F v) (A.c.repr e j) := by
  simp [inclR, Algebra.TensorProduct.basis_repr_tmul]

theorem Xc_add (z w : Fv F v ⊗[F] E) : Xc v A (z + w) = Xc v A z + Xc v A w := by
  simp only [Xc, map_add (f := _), Finsupp.add_apply]

theorem Yc_add (z w : Fv F v ⊗[F] E) : Yc v A (z + w) = Yc v A z + Yc v A w := by
  simp only [Yc, map_add (f := _), Finsupp.add_apply]

theorem Xc_neg (z : Fv F v ⊗[F] E) : Xc v A (-z) = -Xc v A z := by
  simp only [Xc, map_neg, Finsupp.neg_apply]

theorem Yc_neg (z : Fv F v ⊗[F] E) : Yc v A (-z) = -Yc v A z := by
  simp only [Yc, map_neg, Finsupp.neg_apply]

theorem Xc_zero : Xc v A 0 = 0 := by
  simp only [Xc, map_zero, Finsupp.zero_apply]

theorem Yc_zero : Yc v A 0 = 0 := by
  simp only [Yc, map_zero, Finsupp.zero_apply]

def InC (z : Fv F v ⊗[F] E) : Prop :=
  Xc v A z ∈ v.adicCompletionIntegers F ∧ Yc v A z ∈ v.adicCompletionIntegers F

variable (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)

def lamC : Subring (Fv F v ⊗[F] E) where
  carrier := {z | InC v A z}
  mul_mem' {z w} hz hw := by
    change InC v A z at hz
    change InC v A w at hw
    change InC v A (z * w)
    refine ⟨?_, ?_⟩
    · rw [Xc_mul]
      exact add_mem (mul_mem hz.1 hw.1) (mul_mem (mul_mem hz.2 hw.2) hD)
    · rw [Yc_mul]
      exact add_mem (mul_mem hz.1 hw.2) (mul_mem hz.2 hw.1)
  one_mem' := by
    change InC v A 1
    refine ⟨?_, ?_⟩
    · rw [Xc_one]; exact one_mem _
    · rw [Yc_one]; exact zero_mem _
  add_mem' {z w} hz hw := by
    change InC v A z at hz
    change InC v A w at hw
    change InC v A (z + w)
    exact ⟨by rw [Xc_add]; exact add_mem hz.1 hw.1, by rw [Yc_add]; exact add_mem hz.2 hw.2⟩
  zero_mem' := by
    change InC v A 0
    exact ⟨by rw [Xc_zero]; exact zero_mem _, by rw [Yc_zero]; exact zero_mem _⟩
  neg_mem' {z} hz := by
    change InC v A z at hz
    change InC v A (-z)
    exact ⟨by rw [Xc_neg]; exact neg_mem hz.1, by rw [Yc_neg]; exact neg_mem hz.2⟩

theorem mem_lamC (z : Fv F v ⊗[F] E) : z ∈ lamC v A hD ↔
    Xc v A z ∈ v.adicCompletionIntegers F ∧ Yc v A z ∈ v.adicCompletionIntegers F :=
  Iff.rfl

theorem incl_mem (e : E) (he : ∀ j, algebraMap F (Fv F v) (A.c.repr e j) ∈ v.adicCompletionIntegers F) :
    inclR (Fv F v) e ∈ lamC v A hD := by
  rw [mem_lamC]
  exact ⟨by rw [Xc, repr_incl]; exact he 0, by rw [Yc, repr_incl]; exact he 1⟩

theorem sig_mem {z : Fv F v ⊗[F] E} (hz : z ∈ lamC v A hD) : sigR (Fv F v) σ z ∈ lamC v A hD := by
  rw [mem_lamC] at hz ⊢
  rw [Xc_sig, Yc_sig]
  exact ⟨hz.1, neg_mem hz.2⟩

def sigC : lamC v A hD →+* lamC v A hD where
  toFun z := ⟨sigR (Fv F v) σ z, sig_mem v A hD z.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem coe_sigC (z : lamC v A hD) : (sigC v A hD z : Fv F v ⊗[F] E) = sigR (Fv F v) σ z := rfl

variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))


include hr in
def rho : lamC v A hD →+* K where
  toFun z := algebraMap _ K (red v (Xc v A z)) + algebraMap _ K (red v (Yc v A z)) * r
  map_one' := by
    simp only [Subring.coe_one, Xc_one, Yc_one, red_one, red_zero, map_one, map_zero, zero_mul,
      add_zero]
  map_mul' z w := by
    have hz := z.2
    have hw := w.2
    rw [mem_lamC] at hz hw
    simp only [Subring.coe_mul, Xc_mul, Yc_mul]
    rw [red_add v (mul_mem hz.1 hw.1) (mul_mem (mul_mem hz.2 hw.2) hD),
      red_add v (mul_mem hz.1 hw.2) (mul_mem hz.2 hw.1), red_mul v hz.1 hw.1,
      red_mul v (mul_mem hz.2 hw.2) hD, red_mul v hz.2 hw.2, red_mul v hz.1 hw.2,
      red_mul v hz.2 hw.1]
    simp only [map_add (f := _), map_mul]
    linear_combination (-(algebraMap _ K (red v (Yc v A z)) * algebraMap _ K (red v (Yc v A w)))) * hr
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, Xc_zero, Yc_zero, red_zero, map_zero, zero_mul, add_zero]
  map_add' z w := by
    have hz := z.2
    have hw := w.2
    rw [mem_lamC] at hz hw
    simp only [AddMemClass.coe_add, Xc_add, Yc_add]
    rw [red_add v hz.1 hw.1, red_add v hz.2 hw.2]
    simp only [map_add (f := _)]
    ring

theorem rho_apply (z : lamC v A hD) : rho v A hD r hr z =
    algebraMap _ K (red v (Xc v A z)) + algebraMap _ K (red v (Yc v A z)) * r := rfl

theorem rho_sig (σ' : K ≃ₐ[𝓞 F ⧸ v.asIdeal] K) (hσr : σ' r = -r)
    (z : lamC v A hD) : rho v A hD r hr (sigC v A hD z) = σ' (rho v A hD r hr z) := by
  have hz := (mem_lamC v A hD _).1 z.2
  rw [rho_apply, rho_apply, coe_sigC, Xc_sig, Yc_sig, red_neg v hz.2, map_add (f := _), map_mul, AlgEquiv.commutes,
    AlgEquiv.commutes, hσr, map_neg]
  ring

variable (hbij : Function.Bijective
  (fun p : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) => algebraMap _ K p.1 + algebraMap _ K p.2 * r))

include hbij in
theorem rho_eq_zero (z : lamC v A hD) : rho v A hD r hr z = 0 ↔
    Valued.v (Xc v A z) < 1 ∧ Valued.v (Yc v A z) < 1 := by
  have hz := (mem_lamC v A hD _).1 z.2
  rw [rho_apply, ← red_eq_zero_iff v hz.1, ← red_eq_zero_iff v hz.2]
  constructor
  · intro h
    have h' := @hbij.1 (red v (Xc v A z), red v (Yc v A z)) (0, 0) (by simp only [map_zero, zero_mul, add_zero]; exact h)
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    simp

include hbij in
theorem rho_surj (w : K) : ∃ z : lamC v A hD, rho v A hD r hr z = w := by
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 w
  obtain ⟨x, hx, rfl⟩ := red_surj v a
  obtain ⟨y, hy, rfl⟩ := red_surj v b
  refine ⟨⟨Pt v A x y, (mem_lamC v A hD _).2 ⟨by rw [Xc_Pt]; exact hx, by rw [Yc_Pt]; exact hy⟩⟩, ?_⟩
  rw [rho_apply]
  show algebraMap _ K (red v (Xc v A (Pt v A x y))) + algebraMap _ K (red v (Yc v A (Pt v A x y))) * r = w
  rw [Xc_Pt, Yc_Pt]
  exact hab

theorem smul_char (z : Fv F v ⊗[F] E) :
    (∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = z) ↔
      (z ∈ lamC v A hD ∧ Valued.v (Xc v A z) < 1 ∧ Valued.v (Yc v A z) < 1) := by
  have hXs : ∀ (c : Fv F v) (z : Fv F v ⊗[F] E), Xc v A (c • z) = c * Xc v A z := fun c z => by
    simp only [Xc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hYs : ∀ (c : Fv F v) (z : Fv F v ⊗[F] E), Yc v A (c • z) = c * Yc v A z := fun c z => by
    simp only [Yc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  obtain ⟨hπ0, -, hπI⟩ := unifV_spec v
  have hπv : Valued.v (unifV v) < 1 := (lt_one_iff_unif v _).2 (by rw [inv_mul_cancel₀ hπ0, map_one])
  have hI : ∀ x : Fv F v, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 :=
    fun x => HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v
  constructor
  · rintro ⟨z', hz', rfl⟩
    rw [mem_lamC] at hz'
    rw [mem_lamC, hXs, hYs]
    refine ⟨⟨mul_mem hπI hz'.1, mul_mem hπI hz'.2⟩, ?_, ?_⟩
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hπv ((hI _).1 hz'.1)
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hπv ((hI _).1 hz'.2)
  · rintro ⟨hz, h1, h2⟩
    refine ⟨(unifV v)⁻¹ • z, ?_, ?_⟩
    · rw [mem_lamC, hXs, hYs, hI, hI]
      exact ⟨(lt_one_iff_unif v _).1 h1, (lt_one_iff_unif v _).1 h2⟩
    · rw [smul_smul, mul_inv_cancel₀ hπ0, one_smul]

end Lat

end PI.VolStabS
