module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.PsiTower
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.AddCharKernel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.EpSelfDual
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemOfClosed

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.LocDualGenOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDual
noncomputable section

open ValuativeRel

namespace PI.LocDualGen.FpD

open PI.LocDualGen.W

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]

def P (x : K) : Prop := ∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * (b : K))‖ ≤ 1

theorem tr_alg_mul (q : ℚ_[l]) (z : K) :
    Algebra.trace ℚ_[l] K (algebraMap ℚ_[l] K q * z) = q * Algebra.trace ℚ_[l] K z := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

private theorem t2_lemma : T2Space K := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep ?_
  intro x hx
  have hv : ValuativeRel.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨{z | ValuativeRel.valuation K z < ValuativeRel.valuation K x}, ?_, fun h => lt_irrefl (ValuativeRel.valuation K x) h⟩
  exact (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hv, fun z hz => hz⟩

private theorem isOpen_lemma_2 : IsOpen (𝒪[K] : Set K) := by
  have h0 : ((𝒪[K]).toAddSubgroup : Set K) ∈ nhds (0 : K) := by
    refine (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun z hz => ?_⟩
    have hz' : ValuativeRel.valuation K z < 1 := by simpa using hz
    exact (Valuation.mem_integer_iff _ _).2 hz'.le
  exact AddSubgroup.isOpen_of_mem_nhds _ h0

private theorem trace_cont_lemma_3 (hcont : Continuous (algebraMap ℚ_[l] K)) :
    Continuous (Algebra.trace ℚ_[l] K) := by
  haveI := t2_lemma (K := K)
  haveI : ContinuousSMul ℚ_[l] K := ⟨by
    simp only [Algebra.smul_def]
    exact (hcont.comp continuous_fst).mul continuous_snd⟩
  exact LinearMap.continuous_of_finiteDimensional _

private theorem int_lemma_4 (hcont : Continuous (algebraMap ℚ_[l] K)) (z : ℚ_[l]) (hz : ‖z‖ ≤ 1) :
    algebraMap ℚ_[l] K z ∈ 𝒪[K] := by
  have hcl : IsClosed (𝒪[K] : Set K) :=
    AddSubgroup.isClosed_of_isOpen ((𝒪[K]).toAddSubgroup) (isOpen_lemma_2 (K := K))
  let w : ℤ_[l] := ⟨z, hz⟩
  have key : algebraMap ℚ_[l] K (w : ℚ_[l]) ∈ 𝒪[K] := by
    refine PadicInt.denseRange_natCast.induction_on w ?_ ?_
    · exact hcl.preimage (hcont.comp continuous_subtype_val)
    · intro n
      rw [PadicInt.coe_natCast, map_natCast]
      exact natCast_mem _ n

  exact key

private theorem small_lemma_5 (hcont : Continuous (algebraMap ℚ_[l] K)) (y : K) :
    ∃ N : ℕ, ∀ k ≥ N, algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y ∈ 𝒪[K] := by
  have h1 : Filter.Tendsto (fun k : ℕ => (l : ℚ_[l]) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by first
      | exact Padic.norm_p_lt_one
      | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))
  have h2 : Filter.Tendsto (fun k : ℕ => algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y)
      Filter.atTop (nhds 0) := by
    have := ((hcont.tendsto 0).comp h1).mul_const y
    rw [map_zero, zero_mul] at this
    exact this
  have h3 : (𝒪[K] : Set K) ∈ nhds (0 : K) := (isOpen_lemma_2 (K := K)).mem_nhds (zero_mem _)
  exact Filter.eventually_atTop.1 (h2.eventually_mem h3)

private theorem P_add_mem {x y : K} (hx : P l x) (hy : P l y) : P l (x + y) := fun b => by
  rw [add_mul, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx b) (hy b))

private theorem mul_mem_dual₂ {x : K} (hx : P l x) (c : 𝒪[K]) : P l (x * c) := fun b => by
  rw [mul_assoc]
  exact hx (c * b)

private theorem bound_lemma_8 (hcont : Continuous (algebraMap ℚ_[l] K)) :
    ∃ m : ℕ, ∀ x : K, P l x → algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ∈ 𝒪[K] := by
  classical
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hnd := traceForm_nondegenerate ℚ_[l] K
  let B := Module.finBasis ℚ_[l] K
  choose N hN using fun i => small_lemma_5 l hcont (B i)
  let b := B.isUnitSMul (w := fun i => (l : ℚ_[l]) ^ N i)
    (fun i => (isUnit_iff_ne_zero.2 hl0).pow _)
  have hb : ∀ i, b i ∈ 𝒪[K] := fun i => by
    simp only [b, Module.Basis.isUnitSMul_apply, Algebra.smul_def]
    exact hN i (N i) le_rfl
  let D := (Algebra.traceForm ℚ_[l] K).dualBasis hnd b
  choose N' hN' using fun i => small_lemma_5 l hcont (D i)
  refine ⟨Finset.univ.sup N', fun x hx => ?_⟩
  have hc : ∀ i, algebraMap ℚ_[l] K (D.repr x i) ∈ 𝒪[K] := fun i => by
    apply int_lemma_4 l hcont
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    exact hx ⟨b i, hb i⟩
  rw [← D.sum_repr x, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, mul_left_comm]
  exact mul_mem (hc i) (hN' i _ (Finset.le_sup (Finset.mem_univ i)))

theorem exists_ne_zero (hcont : Continuous (algebraMap ℚ_[l] K)) : ∃ x : K, x ≠ 0 ∧ P l x := by
  have hT := trace_cont_lemma_3 l hcont
  have hcpt : IsCompact (𝒪[K] : Set K) := by
    have h : CompactSpace 𝒪[K] := inferInstance
    exact isCompact_iff_compactSpace.2 h
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hT.continuousOn
  have hl1 : ‖(l : ℚ_[l])‖ < 1 := (by first
      | exact Padic.norm_p_lt_one
      | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))
  have hpos : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hl1
  refine ⟨algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ n), ?_, fun b => ?_⟩
  · rw [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · rw [tr_alg_mul, norm_mul, norm_pow]
    have h1 : ‖Algebra.trace ℚ_[l] K (b : K)‖ ≤ max C 1 := (hC b b.2).trans (le_max_left _ _)
    calc ‖(l : ℚ_[l])‖ ^ n * ‖Algebra.trace ℚ_[l] K (b : K)‖
        ≤ ‖(l : ℚ_[l])‖ ^ n * max C 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (max C 1)⁻¹ * max C 1 := mul_le_mul_of_nonneg_right hn.le hpos.le
      _ = 1 := inv_mul_cancel₀ hpos.ne'

end

private theorem main_lemma_9 {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (hcont : Continuous (algebraMap ℚ_[l] K)) :
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[K] := by
  classical
  obtain ⟨m, hm⟩ := bound_lemma_8 l hcont
  obtain ⟨x0, hx0, hPx0⟩ := exists_ne_zero l hcont
  set t : K := algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) with ht
  have ht0 : t ≠ 0 := by
    rw [ht, Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let I : Ideal 𝒪[K] :=
    { carrier := {c | P l ((c : K) * t⁻¹)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        push_cast
        rw [add_mul]
        exact P_add_mem l ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro b
        simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        have h := mul_mem_dual₂ l ha c
        have e : ((c * a : 𝒪[K]) : K) * t⁻¹ = (a : K) * t⁻¹ * (c : K) := by
          push_cast
          ring
        rw [e]
        exact h }
  obtain ⟨g0, hg0⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ c : 𝒪[K], c ∈ I ↔ P l ((c : K) * t⁻¹) := fun c => Iff.rfl
  have hspan : ∀ c : 𝒪[K], c ∈ I ↔ ∃ r : 𝒪[K], r * g0 = c := fun c => by
    rw [hg0, Submodule.mem_span_singleton]
    rfl
  have hc0 : (⟨t * x0, hm x0 hPx0⟩ : 𝒪[K]) ∈ I := by
    rw [hmem]
    have e : t * x0 * t⁻¹ = x0 := by field_simp
    simpa only [e] using hPx0
  have hg0I : g0 ∈ I := (hspan g0).2 ⟨1, one_mul _⟩
  have hg0ne : (g0 : K) ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := (hspan _).1 hc0
    have := congrArg (fun u : 𝒪[K] => (u : K)) hr
    simp only [Subring.coe_mul, h, mul_zero] at this
    exact mul_ne_zero ht0 hx0 this.symm
  set g : K := (g0 : K) * t⁻¹ with hg
  have hPg : P l g := (hmem g0).1 hg0I
  have hgne : g ≠ 0 := mul_ne_zero hg0ne (inv_ne_zero ht0)
  refine ⟨g⁻¹, inv_ne_zero hgne, fun a => ?_⟩
  simp only [inv_inv]
  constructor
  · intro h
    have hPa : P l (a * g) := fun b => by
      have e : a * g * (b : K) = a * (b : K) * g := by ring
      rw [e]
      exact h b
    have hc : (⟨t * (a * g), hm _ hPa⟩ : 𝒪[K]) ∈ I := by
      rw [hmem]
      have e : t * (a * g) * t⁻¹ = a * g := by field_simp
      simpa only [e] using hPa
    obtain ⟨r, hr⟩ := (hspan _).1 hc
    have h2 := congrArg (fun u : 𝒪[K] => (u : K)) hr
    simp only [Subring.coe_mul] at h2
    have h3 : (r : K) = a := by
      have e : t * (a * g) = a * (g0 : K) := by
        rw [hg]
        field_simp
      rw [e] at h2
      exact mul_right_cancel₀ hg0ne h2
    rw [← h3]
    exact r.2
  · intro ha b
    have h := mul_mem_dual₂ l hPg ⟨a, ha⟩ b
    have e : a * (b : K) * g = g * a * (b : K) := by ring
    rw [e]
    exact h

theorem existsDifferentGenerator : FpDual := by
  intro K _ _ _ l _ _ hK _ hcont hfin
  haveI := hK
  haveI := hfin
  exact main_lemma_9 l hcont

end PI.LocDualGen.FpD
end
end

namespace PI.LocDualGen.Of

theorem locDualGen_of (h : PI.LocDualGen.W.FpDualUnram) : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Top.stmt_of PI.LocDualGen.Psi.addCharKernel PI.LocDualGen.FpD.existsDifferentGenerator h
    PI.LocDualGen.EpG.quadraticSelfDual

end PI.LocDualGen.Of
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.UnramifiedDualGenerator
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.IsClosedO
noncomputable section

open ValuativeRel IsLocalRing

namespace PI.LocDualGen.FpU

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]

theorem t2 : T2Space K := by
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed, ← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hv : valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨Units.mk0 _ hv, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ h0
  have hz' : valuation K z < valuation K x := hz
  have h0' : x + z = 0 := h0
  have : z = -x := by linear_combination h0'
  rw [this, Valuation.map_neg] at hz'
  exact lt_irrefl _ hz'

theorem isClosed_O : IsClosed ((𝒪[K] : Set K)) := by
  haveI : T2Space K := t2 (K := K)
  exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).isClosed

theorem iota_mem (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    algebraMap ℚ_[l] K (a : ℚ_[l]) ∈ 𝒪[K] := by
  have hcl : IsClosed {a : ℤ_[l] | algebraMap ℚ_[l] K (a : ℚ_[l]) ∈ 𝒪[K]} :=
    (isClosed_O (K := K)).preimage (hcont.comp continuous_subtype_val)
  refine PadicInt.denseRange_intCast.induction_on a hcl ?_
  intro n
  simp only [Set.mem_setOf_eq, PadicInt.coe_intCast, map_intCast]
  exact intCast_mem _ n

def iotaR (hcont : Continuous (algebraMap ℚ_[l] K)) : ℤ_[l] →+* 𝒪[K] :=
  ((algebraMap ℚ_[l] K).comp (PadicInt.Coe.ringHom (p := l))).codRestrict 𝒪[K]
    (fun a => iota_mem K l hcont a)

theorem iotaR_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    ((iotaR K l hcont a : 𝒪[K]) : K) = algebraMap ℚ_[l] K (a : ℚ_[l]) := rfl

theorem charP_res (huni : Irreducible ((l : ℕ) : 𝒪[K])) : CharP 𝓀[K] l := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (residue 𝒪[K]) l,
    IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 huni.not_isUnit)

theorem repr_sum {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (c : ι → R) (i : ι) : b.repr (∑ j, c j • b j) i = c i := by
  exact congrFun (b.repr_sum_self c) i

section Res

variable [CharP 𝓀[K] l]

abbrev algRes : Algebra (ZMod l) 𝓀[K] := ZMod.algebra _ l

attribute [local instance] algRes

theorem res_iotaR (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    residue 𝒪[K] (iotaR K l hcont a) = algebraMap (ZMod l) 𝓀[K] (PadicInt.toZMod a) := by
  obtain ⟨-, h⟩ := PadicInt.zmodRepr_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  have ha : a = ((a.zmodRepr : ℕ) : ℤ_[l]) + b * (l : ℤ_[l]) := by rw [hb]; ring
  rw [ha]
  simp [map_natCast, CharP.cast_eq_zero]

abbrev fdim : ℕ := Module.finrank (ZMod l) 𝓀[K]

def bb : Module.Basis (Fin (fdim K l)) (ZMod l) 𝓀[K] := Module.finBasis (ZMod l) 𝓀[K]

def blift (i : Fin (fdim K l)) : 𝒪[K] := (residue_surjective (bb K l i)).choose

theorem res_blift (i : Fin (fdim K l)) : residue 𝒪[K] (blift K l i) = bb K l i := by
  exact (residue_surjective (bb K l i)).choose_spec

def Phi (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) : 𝒪[K] :=
  ∑ i, iotaR K l hcont (c i) * blift K l i

theorem Phi_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) :
    ((Phi K l hcont c : 𝒪[K]) : K) = ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by
  unfold Phi
  push_cast
  simp only [iotaR_coe]

theorem Phi_add (hcont : Continuous (algebraMap ℚ_[l] K)) (c c' : Fin (fdim K l) → ℤ_[l]) (s : ℤ_[l]) :
    Phi K l hcont (c + s • c') = Phi K l hcont c + iotaR K l hcont s * Phi K l hcont c' := by
  simp only [Phi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem res_Phi (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) :
    residue 𝒪[K] (Phi K l hcont c) = ∑ i, PadicInt.toZMod (c i) • bb K l i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Phi, map_sum, map_mul, res_iotaR, res_blift, Algebra.smul_def]

theorem one_step (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ∃ c, ∃ y : 𝒪[K], x = Phi K l hcont c + (l : 𝒪[K]) * y := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  set r := (bb K l).repr (residue 𝒪[K] x) with hr
  refine ?_
  have hc : residue 𝒪[K] (Phi K l hcont (fun i => ((r i).val : ℤ_[l]))) = residue 𝒪[K] x := by
    rw [res_Phi]
    have h1 : ∀ i, PadicInt.toZMod (((r i).val : ℕ) : ℤ_[l]) = r i := fun i => by
      rw [map_natCast, ZMod.natCast_zmod_val]
    simp_rw [h1]
    exact (bb K l).sum_repr (residue 𝒪[K] x)
  have hm : x - Phi K l hcont (fun i => ((r i).val : ℤ_[l])) ∈ maximalIdeal 𝒪[K] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hc, sub_self]
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 huni,
    Ideal.mem_span_singleton'] at hm
  obtain ⟨y, hy⟩ := hm
  exact ⟨_, y, by rw [mul_comm, hy]; ring⟩

theorem n_step (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (j : ℕ) (x : 𝒪[K]) : ∃ c, ∃ y : 𝒪[K], x = Phi K l hcont c + (l : 𝒪[K]) ^ j * y := by
  induction j with
  | zero => exact ⟨0, x, by simp [Phi]⟩
  | succ j ih =>
    obtain ⟨c, y, hxy⟩ := ih
    obtain ⟨c', y', hy⟩ := one_step K l hcont huni y
    refine ⟨c + ((l : ℤ_[l]) ^ j) • c', y', ?_⟩
    rw [Phi_add, hxy, hy]
    simp only [map_pow, map_natCast]
    ring

theorem span (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ∃ c, x = Phi K l hcont c := by
  haveI : T2Space K := t2 (K := K)
  choose c y hxy using fun j => n_step K l hcont huni j x
  let F : (Fin (fdim K l) → ℤ_[l]) → K := fun c => ((Phi K l hcont c : 𝒪[K]) : K)
  have hF : Continuous F := by
    have : F = fun c => ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by
      funext c
      exact Phi_coe K l hcont c
    rw [this]
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (hcont.comp (continuous_subtype_val.comp (continuous_apply i))).mul continuous_const
  have hcl : IsClosed (Set.range F) := (isCompact_range hF).isClosed
  have h0 : Filter.Tendsto (fun j => (l : K) ^ j * (y j : K)) Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun j => (l : ℚ_[l]) ^ j) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    have hp' : Filter.Tendsto (fun j => (l : K) ^ j) Filter.atTop (nhds 0) := by
      have := (hcont.tendsto 0).comp hp
      simpa [Function.comp_def, map_pow, map_natCast] using this
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff] at hp' ⊢
    intro γ _
    filter_upwards [hp' γ trivial] with j hj
    have hj' : valuation K ((l : K) ^ j) < γ := hj
    show valuation K ((l : K) ^ j * (y j : K)) < γ
    rw [map_mul]
    have hy1 : valuation K (y j : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (y j).2
    calc valuation K ((l : K) ^ j) * valuation K (y j : K) ≤ valuation K ((l : K) ^ j) * 1 :=
          by gcongr
      _ = valuation K ((l : K) ^ j) := mul_one _
      _ < _ := hj'
  have heq : (fun j => F (c j)) = fun j => (x : K) - (l : K) ^ j * (y j : K) := by
    funext j
    have := congrArg (fun z : 𝒪[K] => (z : K)) (hxy j)
    push_cast at this
    simp only [F]
    rw [this]
    ring
  have hlim : Filter.Tendsto (fun j => F (c j)) Filter.atTop (nhds (x : K)) := by
    rw [heq]
    simpa using (tendsto_const_nhds (x := (x : K))).sub h0
  obtain ⟨c0, hc0⟩ := hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun j => ⟨c j, rfl⟩)
  exact ⟨c0, Subtype.ext hc0.symm⟩

end Res

end PI.LocDualGen.FpU
end
end

noncomputable section

open ValuativeRel IsLocalRing

namespace PI.LocDualGen.FpU

theorem exists_trace_ne_zero (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [Algebra (ZMod p) F] : ∃ z : F, Algebra.trace (ZMod p) F z ≠ 0 := by
  have h : ringChar F = p := ringChar.eq F p
  subst h
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate F (one_ne_zero : (1 : F) ≠ 0)
  exact ⟨b, by simpa using hb⟩

section Main

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]

variable [CharP 𝓀[K] l]

attribute [local instance] algRes

theorem linIndep (hcont : Continuous (algebraMap ℚ_[l] K)) :
    LinearIndependent ℚ_[l] (fun i => (blift K l i : K)) :=
  by apply _root_.UpperTheory.Reformulated.B.Qi13.linIndep <;> assumption

theorem exists_pow_mul_mem (huni : Irreducible ((l : ℕ) : 𝒪[K])) (x : K) :
    ∃ n : ℕ, (l : K) ^ n * x ∈ 𝒪[K] := by
  by_cases hx : x ∈ 𝒪[K]
  · exact ⟨0, by simpa using hx⟩
  have hx1 : 1 < valuation K x := by
    rw [Valuation.mem_integer_iff, not_le] at hx
    exact hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx1
    exact absurd hx1 (not_lt.mpr zero_le)
  have hinv : x⁻¹ ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hx1.le
  have hr0 : (⟨x⁻¹, hinv⟩ : 𝒪[K]) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    exact inv_ne_zero hx0 this
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 huni
  refine ⟨n, ?_⟩
  have hu' : x⁻¹ = ((u : 𝒪[K]) : K) * (l : K) ^ n := by
    have := congrArg Subtype.val hu
    simpa using this
  have huu : ((u : 𝒪[K]) : K) * (((u⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) : K) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]
    rfl
  have hxe : x = (((u : 𝒪[K]) : K) * (l : K) ^ n)⁻¹ := by rw [← hu', inv_inv]
  have hl0 : ((l : K)) ^ n ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu'
    exact inv_ne_zero hx0 hu'
  have hv : (l : K) ^ n * x = (((u⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) : K) := by
    rw [hxe, mul_inv, ← mul_assoc, mul_comm ((l : K) ^ n), mul_assoc, mul_inv_cancel₀ hl0, mul_one]
    exact inv_eq_of_mul_eq_one_right huu
  rw [hv]
  exact (u⁻¹ : (𝒪[K])ˣ).1.2

theorem spanTop (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K])) :
    ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (blift K l i : K)) := by
  intro x _
  obtain ⟨n, hn⟩ := exists_pow_mul_mem K l huni x
  obtain ⟨c, hc⟩ := span K l hcont huni ⟨_, hn⟩
  have hc' := congrArg Subtype.val hc
  rw [Phi_coe] at hc'
  change (l : K) ^ n * x = _ at hc'
  have hl0 : (l : K) ^ n ≠ 0 := pow_ne_zero _ (by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  have hx : x = ∑ i, (((l : ℚ_[l]) ^ n)⁻¹ * (c i : ℚ_[l])) • (blift K l i : K) := by
    have e : x = ((l : K) ^ n)⁻¹ * ((l : K) ^ n * x) := by field_simp
    rw [e, hc', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def, map_mul, map_inv₀, map_pow, map_natCast]
    ring
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

def B (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K])) :
    Module.Basis (Fin (fdim K l)) ℚ_[l] K :=
  Module.Basis.mk (linIndep K l hcont) (spanTop K l hcont huni)

theorem B_apply (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (i : Fin (fdim K l)) : B K l hcont huni i = (blift K l i : K) := by
  simp [B]

def coef (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (y : 𝒪[K]) : Fin (fdim K l) → ℤ_[l] :=
  (span K l hcont huni y).choose

theorem repr_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (y : 𝒪[K]) (j : Fin (fdim K l)) :
    (B K l hcont huni).repr (y : K) j = (coef K l hcont huni y j : ℚ_[l]) := by
  have h' : (y : K) = ((Phi K l hcont (coef K l hcont huni y) : 𝒪[K]) : K) :=
    congrArg Subtype.val (span K l hcont huni y).choose_spec
  rw [h', Phi_coe]
  have e : ∑ i, algebraMap ℚ_[l] K ((coef K l hcont huni y i : ℤ_[l]) : ℚ_[l]) * (blift K l i : K) =
      ∑ i, ((coef K l hcont huni y i : ℤ_[l]) : ℚ_[l]) • B K l hcont huni i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [B_apply, Algebra.smul_def]
  rw [e, repr_sum]

theorem res_coef (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (y : 𝒪[K]) (j : Fin (fdim K l)) :
    (bb K l).repr (residue 𝒪[K] y) j = PadicInt.toZMod (coef K l hcont huni y j) := by
  conv_lhs => rw [(span K l hcont huni y).choose_spec]
  rw [res_Phi, repr_sum]
  rfl

theorem trace_eq (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : Algebra.trace ℚ_[l] K (x : K) =
      ((∑ i, coef K l hcont huni (x * blift K l i) i : ℤ_[l]) : ℚ_[l]) := by
  rw [Algebra.trace_eq_matrix_trace (B K l hcont huni), Matrix.trace]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show ((∑ i, coef K l hcont huni (x * blift K l i) i : ℤ_[l]) : ℚ_[l]) =
      ∑ i, ((coef K l hcont huni (x * blift K l i) i : ℤ_[l]) : ℚ_[l]) from
    map_sum PadicInt.Coe.ringHom _ _]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, B_apply]
  have e : (x : K) * (blift K l i : K) = ((x * blift K l i : 𝒪[K]) : K) := rfl
  rw [e, repr_coe]

theorem toZMod_trace (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : PadicInt.toZMod (∑ i, coef K l hcont huni (x * blift K l i) i) =
      Algebra.trace (ZMod l) 𝓀[K] (residue 𝒪[K] x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace (bb K l), Matrix.trace, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, ← res_blift K l i, ← map_mul, res_coef]

theorem trace_int (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ‖Algebra.trace ℚ_[l] K (x : K)‖ ≤ 1 := by
  rw [trace_eq K l hcont huni]
  exact (∑ i, coef K l hcont huni (x * blift K l i) i).2

theorem exists_trace_unit (hcont : Continuous (algebraMap ℚ_[l] K))
    (huni : Irreducible ((l : ℕ) : 𝒪[K])) : ∃ x : 𝒪[K], ¬ ‖Algebra.trace ℚ_[l] K (x : K)‖ < 1 := by
  obtain ⟨z, hz⟩ := exists_trace_ne_zero 𝓀[K] l
  obtain ⟨x, rfl⟩ := residue_surjective z
  refine ⟨x, fun hlt => hz ?_⟩
  rw [← toZMod_trace K l hcont huni]
  rw [trace_eq K l hcont huni] at hlt
  have hnu : (∑ i, coef K l hcont huni (x * blift K l i) i) ∈ maximalIdeal ℤ_[l] :=
    (mem_maximalIdeal _).mpr (PadicInt.mem_nonunits.mpr hlt)
  rw [← PadicInt.ker_toZMod] at hnu
  exact hnu

end Main

theorem unramified_dual_generator : PI.LocDualGen.W.FpDualUnram := by
  intro K _ _ _ l _ _ hlf _ hcont _ huni a
  haveI := hlf
  haveI := charP_res K l huni
  letI := algRes K l
  obtain ⟨z, hz⟩ := exists_trace_unit K l hcont huni
  constructor
  · intro H
    by_contra ha
    have ha1 : 1 < valuation K a := by
      rw [Valuation.mem_integer_iff, not_le] at ha
      exact ha
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha1
      exact absurd ha1 (not_lt.mpr zero_le)
    have hinv : a⁻¹ ∈ 𝒪[K] := by
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ ha1.le
    have hnu : (⟨a⁻¹, hinv⟩ : 𝒪[K]) ∈ maximalIdeal 𝒪[K] := by
      rw [mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
      intro h1
      change valuation K a⁻¹ = 1 at h1
      rw [map_inv₀, inv_eq_one] at h1
      rw [h1] at ha1
      exact lt_irrefl _ ha1
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp huni,
      Ideal.mem_span_singleton'] at hnu
    obtain ⟨t, ht⟩ := hnu
    have ht' : (t : K) * (l : K) = a⁻¹ := congrArg Subtype.val ht
    have hl0 : (l : K) ≠ 0 := by
      rw [← map_natCast (algebraMap ℚ_[l] K)]
      exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have hat : a * (t : K) = algebraMap ℚ_[l] K ((l : ℚ_[l])⁻¹) := by
      rw [map_inv₀, map_natCast]
      field_simp
      have := congrArg (fun w => a * w) ht'
      simp only [mul_inv_cancel₀ ha0] at this
      rw [← this]
      ring
    have h1 := H (t * z)
    change ‖Algebra.trace ℚ_[l] K (a * ((t : K) * (z : K)))‖ ≤ 1 at h1
    rw [← mul_assoc, hat, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, norm_mul, norm_inv] at h1
    have hlpos : 0 < ‖(l : ℚ_[l])‖ := norm_pos_iff.mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    rw [inv_mul_le_iff₀ hlpos, mul_one] at h1
    exact hz (lt_of_le_of_lt h1 Padic.norm_p_lt_one)
  · intro ha b
    exact trace_int K l hcont huni ⟨a * b, mul_mem ha b.2⟩

end PI.LocDualGen.FpU
end
end

theorem local_dual_generation : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Of.locDualGen_of PI.LocDualGen.FpU.unramified_dual_generator
