module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusOfBasic
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BasisFormSumOfGain
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirRealOfCentral
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CommutatorAdjointHolds

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CompactGroupFacts
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS Filter Topology Set

namespace PositivityTheory.CW

theorem second_derivative_holds : B3 := by
  intro ψ ψ' d hmax hψ hd
  by_contra hneg
  have hdpos : 0 < d := lt_of_not_ge hneg
  have h0 : ψ' 0 = 0 := hmax.hasDerivAt_eq_zero (hψ 0)
  have hslope := hd.tendsto_slope_zero_right
  have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ψ t ≤ ψ 0 := nhdsWithin_le_nhds hmax
  have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (ψ' (0 + t) - ψ' 0) := hslope (lt_mem_nhds hdpos)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (e1.and e2)
  have hu0 : (0 : ℝ) < u := hu
  have hb : u / 2 ∈ Set.Ioo (0 : ℝ) u := ⟨by linarith, by linarith⟩
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' (half_pos hu0)
    (fun t _ => (hψ t).continuousAt.continuousWithinAt) (fun t _ => hψ t)
  have hcu : c ∈ Set.Ioo (0 : ℝ) u := ⟨hc.1, hc.2.trans (by linarith)⟩
  obtain ⟨-, hc'⟩ := hsub hcu
  obtain ⟨hbmax, -⟩ := hsub hb
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at hc'
  have hψc : 0 < ψ' c := (pos_iff_pos_of_mul_pos hc').mp (inv_pos.mpr hc.1)
  rw [hcslope, sub_zero] at hψc
  have hdiff : 0 < ψ (u / 2) - ψ 0 := by
    have := mul_pos hψc (half_pos hu0)
    rwa [div_mul_cancel₀ _ (half_pos hu0).ne'] at this
  linarith

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.IdentityFiltrationBound
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CommutatorAdjointLower

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem comm_eq (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    (Mm E * Md ε E - Md ε E * Mm E) a b = ∑ c, (adjSign ε c b - adjSign ε a c) • (E a c * E c b) := by
  simp only [Mm, Md, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, mul_smul_comm, smul_mul_assoc,
    sub_smul, Finset.sum_sub_distrib]

theorem Z_eq (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ V} (hE : IsGlRep E) (a b : Fin n) :
    Z ε E a b = ∑ c, ((if ε c = ε a then E a c * E c b + E c b * E a c else 0) -
      (if ε c = ε b then E a c * E c b + E c b * E a c else 0)) := by
  unfold IsGlRep at hE
  rw [← sub_eq_zero]
  unfold Z casimirK
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ite_mul_sub_mul_ite, mul_mul_sub_mul_mul_eq_add, hE]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [ite_sub_add_sub_eq, ← ite_and, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [and_comm (b := _ = a), and_comm (b := b = _), Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [@eq_comm _ (ε a), @eq_comm _ (ε b), ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x _
  split_ifs <;> abel

end CommutatorAdjointLower

theorem commutator_adjoint_holds : A1 → CommutatorAdjointModLower := by
  intro hA n ε V _ _ E h a b
  obtain ⟨-, -, hE1, -, hcomm, -, -⟩ := hA n ε V E h
  rw [CommutatorAdjointLower.comm_eq, CommutatorAdjointLower.Z_eq ε h.gl, ← Finset.sum_add_distrib]
  have key : ∀ c, (adjSign ε c b - adjSign ε a c) • (E a c * E c b) +
      ((if ε c = ε a then E a c * E c b + E c b * E a c else 0) -
        (if ε c = ε b then E a c * E c b + E c b * E a c else 0)) =
      ((if ε c = ε a then (1 : ℂ) else 0) - (if ε c = ε b then 1 else 0)) • (E c b * E a c - E a c * E c b) := by
    intro c
    simp only [adjSign, @eq_comm _ (ε a) (ε c)]
    split_ifs <;> module
  rw [Finset.sum_congr rfl fun c _ => key c]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hcomm 1 1 _ (hE1 c b) _ (hE1 a c))

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenspacesOrthogonalOfCalculus
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenspaceOrthogonality

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {A : Module.End ℂ V}

lemma nc_sum (f : Fin n × Fin n → ℂ) :
    ∑ p ∈ nc ε, f p = ∑ a, ∑ b, if ε a ≠ ε b then f (a, b) else 0 := by
  unfold nc
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

lemma s1 (g : Fin n → Fin n → ℂ) (c : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if c = a then g a b else 0) else 0) =
      ∑ b, if ε c ≠ ε b then g c b else 0 := by
  rw [Finset.sum_eq_single c]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp
  · intro a _ hac
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm hac]
  · simp

lemma s2 (g : Fin n → Fin n → ℂ) (d : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if b = d then g a b else 0) else 0) =
      ∑ a, if ε a ≠ ε d then g a d else 0 := by
  rw [Finset.sum_comm, Finset.sum_eq_single d]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp
  · intro b _ hbd
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [hbd]
  · simp

lemma comm_apply (hgl : IsGlRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) +
      ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h := congrArg (fun T : Module.End ℂ V => T x) (hgl a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [← sub_eq_iff_eq_add', h]
  split_ifs <;> simp

lemma pt (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (a b : Fin n) (x y : V) :
    inner ℂ (E a b (E c d x)) (A (E a b y)) =
      inner ℂ (E a b x) (A (E a b (E d c y)))
      + (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0)
      - (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0)
      + (if b = c then inner ℂ (E a d x) (A (E a b y)) else 0)
      - (if d = a then inner ℂ (E c b x) (A (E a b y)) else 0) := by
  have hsgn : adjSign ε c d = 1 := by simp [adjSign, hcd]
  have h1 : inner ℂ (E c d (E a b x)) (A (E a b y)) = inner ℂ (E a b x) (A (E a b (E d c y)))
      + (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0)
      - (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0) := by
    rw [huni c d, hsgn, one_mul, ← hA d c hcd.symm, comm_apply hgl d c a b y]
    rw [map_add (f := _), map_sub, inner_add_right, inner_sub_right]
    split_ifs <;> (try simp) <;> ring
  rw [comm_apply hgl a b c d x, inner_add_left, h1, inner_sub_left]
  split_ifs <;> (try simp) <;> ring

lemma key (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (x y : V) :
    beta ε E A (E c d x) y = beta ε E A x (E d c y) := by
  have e : ∀ a b, (if ε a ≠ ε b then inner ℂ (E a b (E c d x)) (A (E a b y)) else 0) =
      (if ε a ≠ ε b then inner ℂ (E a b x) (A (E a b (E d c y))) else 0)
      + (if ε a ≠ ε b then (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0) else 0)
      - (if ε a ≠ ε b then (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0) else 0)
      + (if ε a ≠ ε b then (if b = c then inner ℂ (E a d x) (A (E a b y)) else 0) else 0)
      - (if ε a ≠ ε b then (if d = a then inner ℂ (E c b x) (A (E a b y)) else 0) else 0) := by
    intro a b
    by_cases hab : ε a ≠ ε b
    · simp only [if_pos hab]
      exact pt hgl huni hA hcd a b x y
    · simp only [if_neg hab]
      simp
  have h1 := s1 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E d b y))) c
  have h4 := s1 (ε := ε) (fun a b => inner ℂ (E c b x) (A (E a b y))) d
  have h2 := s2 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E a c y))) d
  have h3 := s2 (ε := ε) (fun a b => inner ℂ (E a d x) (A (E a b y))) c
  simp only [beta, nc_sum]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4, hcd]
  ring

lemma beta_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    beta ε E A (∑ i ∈ s, f i) w = ∑ i ∈ s, beta ε E A (f i) w := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [beta, map_sum, sum_inner]
  exact Finset.sum_comm

lemma beta_sum_right {ι : Type*} (s : Finset ι) (f : ι → V) (v : V) :
    beta ε E A v (∑ i ∈ s, f i) = ∑ i ∈ s, beta ε E A v (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [beta, map_sum, inner_sum]
  exact Finset.sum_comm

lemma Lsym (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z)) (v w : V) :
    beta ε E A (casimirK ε E v) w = beta ε E A v (casimirK ε E w) := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, beta_sum_left, beta_sum_right]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.mp hb).2
  rw [key hgl huni hA hab.symm, key hgl huni hA hab]

lemma beta_smul_left (r : ℝ) (v w : V) :
    beta ε E A ((r : ℂ) • v) w = (r : ℂ) * beta ε E A v w := by
  unfold beta
  simp [Finset.mul_sum]

lemma beta_smul_right (r : ℂ) (v w : V) :
    beta ε E A v (r • w) = r * beta ε E A v w := by
  unfold beta
  simp [Finset.mul_sum]

end EigenspaceOrthogonality

theorem eigenspaces_orthogonal_of_calculus : A0 → FunctionalCalculusLaws → EigenspacesOrthogonalAlt := by
  intro hA0 hA11b n ε V _ _ E h ι b μ hB φ ν ν' v w hne hv hw
  obtain ⟨-, -, hZ, -⟩ := hA0 n ε V E h
  obtain ⟨hfc, -⟩ := hA11b n ε V E h ι b μ hB
  have hcomm : ∀ c d, ε c = ε d → ∀ z, fc b μ φ (E c d z) = E c d (fc b μ φ z) := by
    intro c d hcd z
    have heig : ∀ i, Eig ε E (μ i) (E c d (b i)) := by
      intro i
      have hz := congrArg (fun T : Module.End ℂ V => T (b i)) (hZ c d hcd)
      simp only [Z, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at hz
      show casimirK ε E (E c d (b i)) = ((μ i : ℝ) : ℂ) • E c d (b i)
      rw [sub_eq_zero.mp hz, show casimirK ε E (b i) = ((μ i : ℝ) : ℂ) • b i from hB.eig i, map_smul]
    have hT : (fc b μ φ).comp (E c d) = (E c d).comp (fc b μ φ) := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply]
      rw [hfc φ (μ i) _ (heig i), hfc φ (μ i) _ (hB.eig i), map_smul]
    exact LinearMap.congr_fun hT z
  have hL := EigenspaceOrthogonality.Lsym (A := fc b μ φ) h.gl h.uni hcomm v w
  rw [show casimirK ε E v = ((ν : ℝ) : ℂ) • v from hv,
    show casimirK ε E w = ((ν' : ℝ) : ℂ) • w from hw,
    EigenspaceOrthogonality.beta_smul_left, EigenspaceOrthogonality.beta_smul_right] at hL
  have hm : (((ν : ℝ) : ℂ) - ((ν' : ℝ) : ℂ)) * beta ε E (fc b μ φ) v w = 0 := by
    rw [sub_mul, hL, sub_self]
  rcases mul_eq_zero.mp hm with h0 | h0
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h0)) hne
  · exact h0

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenWeightedSumBound
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace SumSquaresShift

theorem shift {n : ℕ} {ε : Fin n → Bool} (hB3g : UnitaryGroupFacts) (F0 : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) (D : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F0 (g * NormedSpace.exp (t • X))) (D g) 0)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset ε) (t : ℝ) :
    HasDerivAt (fun t : ℝ => F0 (g * NormedSpace.exp (t • X))) (D (g * NormedSpace.exp (t • X))) t := by
  obtain ⟨-, -, hmem, hadd, -⟩ := hB3g n ε
  have hg' := hmem g hg X hX t
  have h1 := h _ hg'
  have h0 : HasDerivAt (fun s : ℝ => F0 (g * NormedSpace.exp (t • X) * NormedSpace.exp (s • X)))
      (D (g * NormedSpace.exp (t • X))) (t - t) := by
    rw [sub_self]; exact h1
  have h4 := h0.comp_sub_const t t
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  have hu : t + (u - t) = u := by ring
  show F0 (g * NormedSpace.exp (u • X)) = F0 (g * NormedSpace.exp (t • X) * NormedSpace.exp ((u - t) • X))
  rw [mul_assoc, ← hadd X t (u - t), hu]

end SumSquaresShift

open SumSquaresShift in
theorem second_derivatives_of_growth : B1 → UnitaryGroupFacts → SumSquaresSecondDerivative := by
  intro hB1 hB3g n ε V _ _ E hMod ι b μ hEig κ hκ F hF S a g hg
  obtain ⟨hXp, hcas, hnorm⟩ := hB1 n ε V E hMod
  have hd : ∀ p ∈ nc ε, ∀ (v : V) (t : ℝ),
      HasDerivAt (fun s : ℝ => F v (g * NormedSpace.exp (s • Xp p.1 p.2)))
        (F (actM E (Xp p.1 p.2) v) (g * NormedSpace.exp (t • Xp p.1 p.2))) t := by
    intro p hp v t
    exact shift hB3g (F v) (Xp p.1 p.2) (hXp p hp) (fun k => F (actM E (Xp p.1 p.2) v) k)
      (fun k hk => hF _ (hXp p hp) v k hk) g hg t
  have hexp0 : ∀ X : Matrix (Fin n) (Fin n) ℂ, g * NormedSpace.exp ((0:ℝ) • X) = g := by
    intro X
    simp [NormedSpace.exp_zero]
  refine ⟨fun p => ∑ i ∈ S, a i * (2 * (inner ℝ (F (b i) g)
      (F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g) + ‖F (actM E (Xp p.1 p.2) (b i)) g‖ ^ 2)), ?_, ?_⟩
  · intro p hp
    refine ⟨fun t => ∑ i ∈ S, a i * (2 * inner ℝ (F (b i) (g * NormedSpace.exp (t • Xp p.1 p.2)))
      (F (actM E (Xp p.1 p.2) (b i)) (g * NormedSpace.exp (t • Xp p.1 p.2)))), ?_, ?_⟩
    · intro t
      beta_reduce
      apply HasDerivAt.fun_sum
      intro i _
      exact ((hd p hp (b i) t).norm_sq).const_mul (a i)
    · beta_reduce
      apply HasDerivAt.fun_sum
      intro i _
      have h1 := hd p hp (b i) 0
      have h2 := hd p hp (actM E (Xp p.1 p.2) (b i)) 0
      have h3 := ((HasDerivAt.inner ℝ h1 h2).const_mul 2).const_mul (a i)
      rw [hexp0] at h3
      refine h3.congr_deriv ?_
      rw [real_inner_self_eq_norm_sq]
  · dsimp only
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hN : ∑ p ∈ nc ε, ‖F (actM E (Xp p.1 p.2) (b i)) g‖ ^ 2
        = ∑ p ∈ nc ε, ‖F (E p.1 p.2 (b i)) g‖ ^ 2 :=
      hnorm ((LinearMap.proj g).comp F) (b i)
    have hs : ∑ p ∈ nc ε, F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g
        = ((κ - μ i : ℝ) : ℂ) * F (b i) g := by
      have h0 := congrArg (fun v => F v g) (hcas κ hκ (b i))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.sum_apply] at h0
      rw [h0, (hEig.eig i : casimirK ε E (b i) = _)]
      simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have hI : ∑ p ∈ nc ε, inner ℝ (F (b i) g) (F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g)
        = (κ - μ i) * ‖F (b i) g‖ ^ 2 := by
      rw [← inner_sum, hs, ← Complex.real_smul, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, hI, hN]
    ring

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BasisSumOfOrthogonality
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace FormEigenMonotone

lemma phi_nonneg (s : ℕ) (R x : ℝ) : 0 ≤ phiR s R x := le_max_right _ _

lemma phi_zero {s : ℕ} {R x : ℝ} (hR : 0 < R) (hx : R ≤ x) : phiR s R x = 0 := by
  unfold phiR
  apply max_eq_right
  have h1 : (0:ℝ) < (1+R)^s := by positivity
  have h2 : (1+R)^s ≤ (1+x)^s := pow_le_pow_left₀ (by linarith) (by linarith) s
  have := inv_anti₀ h1 h2
  linarith

lemma phi_le_one {s : ℕ} {R x : ℝ} (hR : 0 < R) (hx : 0 ≤ x) : phiR s R x ≤ 1 := by
  unfold phiR
  apply max_le _ zero_le_one
  have h1 : (1:ℝ) ≤ (1+x)^s := one_le_pow₀ (by linarith)
  have h2 : ((1+x)^s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have h3 : 0 ≤ ((1+R)^s)⁻¹ := by positivity
  linarith

lemma phi_eq {s : ℕ} {R x : ℝ} (hx : 0 ≤ x) (hxR : x < R) :
    phiR s R x = ((1+x)^s)⁻¹ - ((1+R)^s)⁻¹ := by
  unfold phiR
  apply max_eq_left
  have h1 : (0:ℝ) < (1+x)^s := by positivity
  have h2 : (1+x)^s ≤ (1+R)^s := pow_le_pow_left₀ (by linarith) (by linarith) s
  have := inv_anti₀ h1 h2
  linarith

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}

lemma beta_add (A B : Module.End ℂ V) (v w : V) :
    beta ε E (A + B) v w = beta ε E A v w + beta ε E B v w := by
  simp only [beta, LinearMap.add_apply, inner_add_right, Finset.sum_add_distrib]

lemma re_inner_smul_self (r : ℝ) (v : V) : (inner ℂ v ((r : ℂ) • v)).re = r * ‖v‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) v

lemma beta_const_re (r : ℝ) (v : V) :
    (beta ε E ((r : ℂ) • 1) v v).re = r * ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 := by
  simp only [beta, LinearMap.smul_apply, Module.End.one_apply, Complex.re_sum, re_inner_smul_self,
    Finset.mul_sum]

lemma beta_mono
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (φ ψ : ℝ → ℝ) (h : ∀ x, 0 ≤ x → φ x ≤ ψ x) (v : V) :
    (beta ε E (fc b μ φ) v v).re ≤ (beta ε E (fc b μ ψ) v v).re := by
  simp only [beta, Complex.re_sum]
  exact Finset.sum_le_sum fun p _ => hmono φ ψ h _

lemma norm_fib (hb : Orthonormal ℂ b) (f : V →ₗ[ℂ] ℂ) (F : Finset ι) :
    ‖∑ j ∈ F, starRingEnd ℂ (f (b j)) • b j‖ ^ 2 = ∑ j ∈ F, ‖f (b j)‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, hb.inner_sum, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_conj, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma eig_fib (hb : ∀ i, Eig ε E (μ i) (b i)) (ν : ℝ) (F : Finset ι) (hF : ∀ j ∈ F, μ j = ν)
    (a : ι → ℂ) : Eig ε E ν (∑ j ∈ F, a j • b j) := by
  unfold Eig
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_smul, hb j, hF j hj, smul_comm]

lemma key {κ c x₀ R : ℝ} {s : ℕ}
    (hA0 : ∀ w, ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 = (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2)
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1)
    (hA12 : ∀ ν v, x₀ ≤ ν → Eig ε E ν v →
      ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re)
    (hc : 0 ≤ c) (hR : 0 < R) (ν : ℝ) (hν : 0 ≤ ν) (h : V) (hh : Eig ε E ν h) :
    phiR s R ν * (ν - κ + c) * ‖h‖ ^ 2 - (if ν < x₀ then x₀ + |κ| + c else 0) * ‖h‖ ^ 2 ≤
      (beta ε E (fc b μ (phiR s R)) h h).re := by
  have hN : ∀ w, 0 ≤ (beta ε E (fc b μ (phiR s R)) w w).re := by
    intro w
    have h0 := beta_mono (ε := ε) (E := E) hmono (fun _ => (0:ℝ)) (phiR s R)
      (fun x _ => phi_nonneg s R x) w
    rw [hconst 0, beta_const_re] at h0
    simpa using h0
  have hd0 : (0:ℝ) ≤ ((1 + R) ^ s)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) _)
  have hS : ∑ p ∈ nc ε, ‖E p.1 p.2 h‖ ^ 2 = (ν - κ) * ‖h‖ ^ 2 := by
    rw [hA0 h, show casimirK ε E h = (ν : ℂ) • h from hh, re_inner_smul_self]
    ring
  have hlow : (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) h h).re - ((1 + R) ^ s)⁻¹ * ((ν - κ) * ‖h‖ ^ 2)
      ≤ (beta ε E (fc b μ (phiR s R)) h h).re := by
    have e : fc b μ (fun x => ((1 + x) ^ s)⁻¹ + -((1 + R) ^ s)⁻¹)
        = fc b μ (fun x => ((1 + x) ^ s)⁻¹) + fc b μ (fun _ => -((1 + R) ^ s)⁻¹) := hadd _ _
    have h1 := beta_mono (ε := ε) (E := E) hmono (fun x => ((1 + x) ^ s)⁻¹ + -((1 + R) ^ s)⁻¹)
      (phiR s R) (fun x _ => by
        simp only [phiR]
        linarith [le_max_left (((1 + x) ^ s)⁻¹ - ((1 + R) ^ s)⁻¹) 0]) h
    rw [e, beta_add, hconst (-((1 + R) ^ s)⁻¹), Complex.add_re, beta_const_re, hS] at h1
    linarith
  have hn : 0 ≤ ‖h‖ ^ 2 := by positivity
  by_cases hx : ν < x₀
  · rw [if_pos hx]
    have hp0 := phi_nonneg s R ν
    have hp1 := phi_le_one (s := s) hR hν
    have hbd : phiR s R ν * (ν - κ + c) ≤ x₀ + |κ| + c := by
      rcases le_total 0 (ν - κ + c) with h0 | h0
      · nlinarith [neg_le_abs κ, mul_le_mul_of_nonneg_right hp1 h0]
      · nlinarith [abs_nonneg κ, mul_nonpos_of_nonneg_of_nonpos hp0 h0]
    have := mul_le_mul_of_nonneg_right hbd hn
    linarith [hN h]
  · rw [if_neg hx]
    have hA := hA12 ν h (not_lt.mp hx) hh
    by_cases hνR : ν < R
    · rw [phi_eq hν hνR]
      nlinarith [hlow, mul_nonneg (mul_nonneg hd0 hc) hn]
    · rw [phi_zero hR (not_lt.mp hνR)]
      simpa using hN h

end FormEigenMonotone

theorem basis_form_sum_of_gain : A0 → FunctionalCalculusLaws → A12 → BasisSumAsFormValues → A13 := by
  intro hA0 hA11 hA12 hA13a
  unfold A0 FunctionalCalculusLaws A12 BasisSumAsFormValues A13 ForBas ForMod at *
  intro n ε V i1 i2 E hM ι b μ hEB κ hκ c hc
  obtain ⟨-, -, hmono, hadd, -, hconst, -⟩ := hA11 n ε V E hM ι b μ hEB
  obtain ⟨s, x₀, hs, hx₀, hb12⟩ := hA12 n ε V E hM ι b μ hEB κ hκ c hc
  have hA0' := fun w => ((hA0 n ε V E hM).2.2.2 κ hκ w).2.1
  have hK : 0 ≤ x₀ + |κ| + c := by linarith [abs_nonneg κ]
  refine ⟨s, x₀, x₀ + |κ| + c, hs, hK, ?_⟩
  intro R f S T hS hT
  have hTb : 0 ≤ (x₀ + |κ| + c) * ∑ i ∈ T, ‖f (b i)‖ ^ 2 :=
    mul_nonneg hK (Finset.sum_nonneg fun i _ => by positivity)
  rcases le_or_gt R 0 with hR | hR
  · have hSe : ∀ i ∈ S, False := fun i hi => by
      have := (hS i).1 hi
      linarith [hEB.nonneg i]
    rw [Finset.sum_eq_zero (s := S) (f := fun i => phiR s R (μ i) * ‖f (b i)‖ ^ 2)
        (fun i hi => (hSe i hi).elim),
      Finset.sum_eq_zero (s := S) (f := fun i => phiR s R (μ i) *
        (∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2 - (μ i - κ) * ‖f (b i)‖ ^ 2))
        (fun i hi => (hSe i hi).elim)]
    linarith
  · have hφS : ∀ i ∉ S, phiR s R (μ i) = 0 := fun i hi =>
      FormEigenMonotone.phi_zero hR (not_lt.mp fun h => hi ((hS i).2 h))
    obtain ⟨T', hST', hT'⟩ := hA13a n ε V E hM ι b μ hEB (phiR s R) S hφS
    have key1 := hT' f
    have hstep : ∀ ν ∈ Finset.image μ T',
        (phiR s R ν * (ν - κ + c) - (if ν < x₀ then x₀ + |κ| + c else 0)) *
          ∑ j ∈ T' with μ j = ν, ‖f (b j)‖ ^ 2 ≤
        (beta ε E (fc b μ (phiR s R)) (∑ j ∈ T' with μ j = ν, (starRingEnd ℂ) (f (b j)) • b j)
            (∑ j ∈ T' with μ j = ν, (starRingEnd ℂ) (f (b j)) • b j)).re := by
      intro ν hν
      obtain ⟨j0, -, rfl⟩ := Finset.mem_image.1 hν
      have hEig := FormEigenMonotone.eig_fib hEB.eig (μ j0) (T'.filter fun j => μ j = μ j0)
        (fun j hj => (Finset.mem_filter.1 hj).2) (fun j => (starRingEnd ℂ) (f (b j)))
      beta_reduce at hEig
      have hk := FormEigenMonotone.key (b := b) (μ := μ) hA0' hmono hadd hconst hb12 hc hR (μ j0)
        (hEB.nonneg j0) _ hEig
      rw [FormEigenMonotone.norm_fib hEB.on f] at hk
      linarith
    have hsum1 : ∑ ν ∈ Finset.image μ T', (phiR s R ν * (ν - κ + c) - (if ν < x₀ then x₀ + |κ| + c else 0)) *
          ∑ j ∈ T' with μ j = ν, ‖f (b j)‖ ^ 2
        = ∑ j ∈ T', (phiR s R (μ j) * (μ j - κ + c) - (if μ j < x₀ then x₀ + |κ| + c else 0)) *
          ‖f (b j)‖ ^ 2 := by
      apply Finset.sum_image'
      intro i _
      beta_reduce
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(Finset.mem_filter.1 hj).2]
    have e := Finset.sum_subset hST' (f := fun j => phiR s R (μ j) * (μ j - κ + c) * ‖f (b j)‖ ^ 2)
      (fun j _ hj => by simp only [hφS j hj, zero_mul])
    have hsplit : ∑ j ∈ T', (phiR s R (μ j) * (μ j - κ + c) - (if μ j < x₀ then x₀ + |κ| + c else 0)) *
          ‖f (b j)‖ ^ 2
        = ∑ j ∈ S, phiR s R (μ j) * (μ j - κ) * ‖f (b j)‖ ^ 2 +
            c * ∑ j ∈ S, phiR s R (μ j) * ‖f (b j)‖ ^ 2
          - ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      congr 1
      rw [← e, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hTb2 : ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2
        ≤ (x₀ + |κ| + c) * ∑ i ∈ T, ‖f (b i)‖ ^ 2 := by
      rw [Finset.mul_sum]
      calc ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2
          = ∑ j ∈ T' with μ j < x₀, (x₀ + |κ| + c) * ‖f (b j)‖ ^ 2 := by
            rw [Finset.sum_filter]
            exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
        _ ≤ ∑ i ∈ T, (x₀ + |κ| + c) * ‖f (b i)‖ ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              exact (hT j).2 (Finset.mem_filter.1 hj).2
            · intro j _ _
              exact mul_nonneg hK (by positivity)
    have hle := Finset.sum_le_sum hstep
    rw [hsum1, hsplit, ← key1] at hle
    have hR2 : ∑ i ∈ S, phiR s R (μ i) *
          (∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2 - (μ i - κ) * ‖f (b i)‖ ^ 2)
        = ∑ i ∈ S, phiR s R (μ i) * ∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2
          - ∑ i ∈ S, phiR s R (μ i) * (μ i - κ) * ‖f (b i)‖ ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hR2]
    linarith

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.InversePowerBoundHolds
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace InversePowerBound

lemma sq_le_inv_pow (s : ℕ) (y : ℝ) (hy : -1 < y) (h0 : 0 ≤ 1 - (s : ℝ) * y / 2) :
    (1 - (s : ℝ) * y / 2) ^ 2 ≤ ((1 + y) ^ s)⁻¹ := by
  have h1 : 0 < 1 + y := by linarith
  have hpos : 0 < (1 + y) ^ s := pow_pos h1 s

  have hA : 1 - (s : ℝ) * y / 2 ≤ Real.exp (-((s : ℝ) * y / 2)) := by
    linarith [Real.add_one_le_exp (-((s : ℝ) * y / 2))]
  have hB : (1 + y) ^ s ≤ Real.exp ((s : ℝ) * y) := by
    calc (1 + y) ^ s ≤ (Real.exp y) ^ s :=
          pow_le_pow_left₀ h1.le (by linarith [Real.add_one_le_exp y]) s
      _ = Real.exp ((s : ℝ) * y) := by rw [← Real.exp_nat_mul]
  have hC : (1 - (s : ℝ) * y / 2) ^ 2 ≤ Real.exp (-((s : ℝ) * y)) := by
    calc (1 - (s : ℝ) * y / 2) ^ 2 ≤ (Real.exp (-((s : ℝ) * y / 2))) ^ 2 :=
          pow_le_pow_left₀ h0 hA 2
      _ = Real.exp (-((s : ℝ) * y)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (1 - (s : ℝ) * y / 2) ^ 2 ≤ Real.exp (-((s : ℝ) * y)) := hC
    _ = (Real.exp ((s : ℝ) * y))⁻¹ := by rw [Real.exp_neg]
    _ ≤ ((1 + y) ^ s)⁻¹ := inv_anti₀ hpos hB

end InversePowerBound

theorem inverse_power_bound_holds : A10 := by
  intro s _hs
  refine ⟨(s : ℝ) ^ 4 / 16, by positivity, fun y hy => ?_⟩
  have hpos : 0 < ((1 + y) ^ s)⁻¹ := inv_pos.mpr (pow_pos (by linarith) s)

  have hsq : 1 - (s : ℝ) * y + (s : ℝ) ^ 2 / 4 * y ^ 2 = (1 - (s : ℝ) * y / 2) ^ 2 := by ring
  have e : (s : ℝ) ^ 4 / 16 * y ^ 4 = ((s : ℝ) * y / 2) ^ 4 := by ring
  by_cases h0 : 0 ≤ 1 - (s : ℝ) * y / 2
  · have h := InversePowerBound.sq_le_inv_pow s y hy h0
    have : 0 ≤ (s : ℝ) ^ 4 / 16 * y ^ 4 := by positivity
    linarith
  ·
    rw [not_le] at h0
    have hu : 1 < (s : ℝ) * y / 2 := by linarith
    have k1 : (1 - (s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 2 := by nlinarith
    have k2 : ((s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 4 := by
      have : 1 ≤ ((s : ℝ) * y / 2) ^ 2 := by nlinarith
      nlinarith
    linarith

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GelfandCentralHolds
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CasimirPowerCommute

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem comm_pow (E : Fin n → Fin n → Module.End ℂ V) (hE : IsGlRep E) (c d : Fin n) :
    ∀ (k : ℕ) (a b : Fin n), E c d * (Mm E ^ k) a b - (Mm E ^ k) a b * E c d =
      (if d = a then (Mm E ^ k) c b else 0) - (if b = c then (Mm E ^ k) a d else 0) := by
  have hM : ∀ i j, Mm E i j = E i j := fun _ _ => rfl
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [pow_zero, Matrix.one_apply]
    have h0 : (if d = a then (if c = b then (1 : Module.End ℂ V) else 0) else 0) =
        (if b = c then (if a = d then 1 else 0) else 0) := by
      by_cases h2 : d = a
      · subst h2
        by_cases h3 : b = c
        · subst h3; simp
        · simp [h3, Ne.symm h3]
      · simp [h2, Ne.symm h2]
    rw [h0, sub_self]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    have key : ∀ j, E c d * ((Mm E ^ k) a j * E j b) - ((Mm E ^ k) a j * E j b) * E c d
        = (E c d * (Mm E ^ k) a j - (Mm E ^ k) a j * E c d) * E j b
          + (Mm E ^ k) a j * (E c d * E j b - E j b * E c d) := by
      intro j; noncomm_ring
    simp only [pow_succ, Matrix.mul_apply, hM]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [key, ih, hE c d]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h1 : d = a <;> by_cases h2 : b = c <;> simp [h1, h2] <;> abel

end CasimirPowerCommute

theorem gelfand_central_holds : A2 := by
  intro n ε V _ _ E h k c d
  have hc := CasimirPowerCommute.comm_pow E h.gl c d k
  rw [← sub_eq_zero, Matrix.trace, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [Matrix.diag_apply, hc, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GrowthPolynomialOperator
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace NoncommutativeSwapSum

lemma nc_swap {n : ℕ} {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f : Fin n × Fin n → M) :
    ∑ p ∈ nc ε, f p.swap = ∑ p ∈ nc ε, f p := by
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_ <;> simp [nc, ne_comm]

lemma sumS {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (κ : ℂ)
    (hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = κ • w - casimirK ε E w) :
    ∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1 = κ • (1 : Module.End ℂ V) - casimirK ε E := by
  ext w
  rw [LinearMap.sum_apply]
  simpa using hS w

lemma key {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (κ : ℂ)
    (hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = κ • w - casimirK ε E w) :
    ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 = -∑ p ∈ nc ε, Z ε E p.1 p.2 * E p.2 p.1 := by
  have h1 := sumS ε E κ hS
  have hc : casimirK ε E * (∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1)
      - (∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1) * casimirK ε E = 0 := by
    rw [h1, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    abel
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib] at hc
  have h2 : ∀ p ∈ nc ε, casimirK ε E * (E p.1 p.2 * E p.2 p.1) - E p.1 p.2 * E p.2 p.1 * casimirK ε E
      = Z ε E p.1 p.2 * E p.2 p.1 + E p.1 p.2 * Z ε E p.2 p.1 := by
    intro p _
    simp only [Z]
    noncomm_ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib] at hc
  have h3 : ∑ p ∈ nc ε, E p.1 p.2 * Z ε E p.2 p.1 = ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 :=
    nc_swap ε (fun p => E p.2 p.1 * Z ε E p.1 p.2)
  rw [h3] at hc
  exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hc)

end NoncommutativeSwapSum

theorem a9_of_a0_a1_eigenbasis_a6 : A0 → A1 → CasimirIsRealScalar → A6 → A9 := by
  intro h0 h1 h3 h6 n ε V _ _ E hM
  obtain ⟨_, _, _, h0c⟩ := h0 n ε V E hM
  obtain ⟨_, _, hE1, _, hcomm, hL2, hZ2⟩ := h1 n ε V E hM
  obtain ⟨κ, hκ⟩ := h3 n ε V E hM
  have hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = (κ : ℂ) • w - casimirK ε E w :=
    fun w => (h0c κ hκ w).2.2
  have hWU : (∑ p ∈ nc ε, (E p.2 p.1 * Z ε E p.1 p.2 - Z ε E p.1 p.2 * E p.2 p.1)) ∈ U E 2 :=
    Submodule.sum_mem _ fun p _ => hcomm 1 2 _ (hE1 _ _) _ (hZ2 _ _)
  obtain ⟨C1, hC1, hW1⟩ := h6 n ε V E hM 2 _ hWU
  have hZZ : ∀ p : Fin n × Fin n,
      casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E ∈ U E 3 :=
    fun p => hcomm 2 2 _ hL2 _ (hZ2 _ _)
  choose Cp hCp0 hCp using fun p => h6 n ε V E hM 3 _ (hZZ p)
  have hCs : 0 ≤ ∑ p ∈ nc ε, Cp p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  refine ⟨C1 + ∑ p ∈ nc ε, Cp p ^ 2, by positivity, fun μ v hμ hv => ⟨?_, ?_⟩⟩
  · have hT : (∑ p ∈ nc ε, (E p.2 p.1 * Z ε E p.1 p.2 - Z ε E p.1 p.2 * E p.2 p.1))
        = (2 : ℂ) • ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 := by
      rw [Finset.sum_sub_distrib, NoncommutativeSwapSum.key ε E (κ : ℂ) hS, two_smul]
      abel
    have hWv := hW1 μ v hμ hv
    rw [Real.sq_sqrt (by linarith), hT, LinearMap.smul_apply, norm_smul] at hWv
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at hWv
    have hTsum : ∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)
        = -inner ℂ v ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v) := by
      rw [LinearMap.sum_apply, inner_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hne : ε p.1 ≠ ε p.2 := (Finset.mem_filter.mp hp).2
      rw [hM.uni, adjSign, if_neg hne]
      simp
    have hv0 := norm_nonneg v
    have hTv0 := norm_nonneg ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v)
    rw [hTsum, norm_neg]
    calc ‖inner ℂ v ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v)‖
        ≤ ‖v‖ * ‖(∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (C1 * (1 + μ) * ‖v‖) := by
          apply mul_le_mul_of_nonneg_left _ hv0
          have : 0 ≤ C1 * (1 + μ) * ‖v‖ := by
            apply mul_nonneg (mul_nonneg hC1 (by linarith)) hv0
          linarith
      _ = C1 * (1 + μ) * ‖v‖ ^ 2 := by ring
      _ ≤ (C1 + ∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) * ‖v‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          linarith
  · have hs : Real.sqrt (1 + μ) ^ 2 = 1 + μ := Real.sq_sqrt (by linarith)
    have hp : ∀ p ∈ nc ε,
        ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
          ≤ Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
      intro p _
      have h := hCp p μ v hμ hv
      have hm := mul_self_le_mul_self (norm_nonneg _) h
      calc ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
          = ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖
            * ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ := sq _
        _ ≤ (Cp p * Real.sqrt (1 + μ) ^ 3 * ‖v‖) * (Cp p * Real.sqrt (1 + μ) ^ 3 * ‖v‖) := hm
        _ = Cp p ^ 2 * (Real.sqrt (1 + μ) ^ 2) ^ 3 * ‖v‖ ^ 2 := by ring
        _ = Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by rw [hs]
    calc ∑ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
        ≤ ∑ p ∈ nc ε, Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := Finset.sum_le_sum hp
      _ = (∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ (C1 + ∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
          linarith

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SymmetricPowerHolds
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace identity_filtration_of_scalar

theorem symm_pow {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (P : Module.End ℂ W)
    (hP : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) :
    ∀ k : ℕ, ∀ x y, inner ℂ ((P ^ k) x) y = inner ℂ x ((P ^ k) y) := by
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hP]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.self_pow P k).eq]

end identity_filtration_of_scalar

theorem symmetric_power_holds : A7 := by
  intro W _ _ P hP x hx h0 j
  induction j with
  | zero => simp
  | succ j ih =>
    have hsym := identity_filtration_of_scalar.symm_pow P hP (2 ^ j)

    have key : (inner ℂ x ((P ^ (2 ^ (j + 1))) x)).re = ‖(P ^ (2 ^ j)) x‖ ^ 2 := by
      rw [pow_succ, pow_mul, sq, Module.End.mul_apply, ← hsym]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) ((P ^ (2 ^ j)) x)

    have cs : |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ≤ ‖(P ^ (2 ^ j)) x‖ := by
      calc _ ≤ ‖inner ℂ x ((P ^ (2 ^ j)) x)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖(P ^ (2 ^ j)) x‖ := norm_inner_le_norm _ _
        _ = _ := by rw [hx, one_mul]
    have hpos : 0 ≤ (inner ℂ x (P x)).re ^ (2 ^ j) := pow_nonneg h0 _
    calc (inner ℂ x (P x)).re ^ (2 ^ (j + 1)) = ((inner ℂ x (P x)).re ^ (2 ^ j)) ^ 2 := by
          rw [pow_succ, pow_mul]
      _ ≤ ((inner ℂ x ((P ^ (2 ^ j)) x)).re) ^ 2 := pow_le_pow_left₀ hpos ih 2
      _ = |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖(P ^ (2 ^ j)) x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) cs 2
      _ = _ := key.symm

end PositivityTheory.CW

end
end

namespace PositivityTheory.CWB

open PositivityTheory.CW

theorem word_filtration_basic : A0 := orthonormal_eigenbasis_of_basic

theorem aux_statement_7 : A1 := word_filtration_of_length

theorem filtration_adjoint_stable : FiltrationAdjointStable := adjoint_stable_filtration

theorem gelfand_invariants_central : A2 := gelfand_central_holds

theorem casimir_eigenvector_exists : A3 := casimir_eigen_exists

theorem casimir_real_scalar : CasimirIsRealScalar := casimir_real_of_central gelfand_invariants_central casimir_eigenvector_exists

theorem power_traces_nilpotent : A4 := nilpotent_of_power_traces

theorem commutator_adjoint_lower_order : CommutatorAdjointModLower := commutator_adjoint_holds aux_statement_7

theorem aux_statement_6 : A5 := normal_nilpotent_of_commutator aux_statement_7 gelfand_invariants_central casimir_eigenvector_exists power_traces_nilpotent commutator_adjoint_lower_order

theorem identity_operator_filtration : A6 := SymmetricPowerMatrix word_filtration_basic aux_statement_7 casimir_real_scalar

theorem matrix_symmetric_power : A7 := symmetric_power_holds

theorem column_moments_bound : ColumnOperatorMoments := column_moments_of_symmetric matrix_symmetric_power

theorem second_moment_bound : A8 := second_moment_of_columns word_filtration_basic aux_statement_7 filtration_adjoint_stable casimir_real_scalar aux_statement_6 identity_operator_filtration column_moments_bound

theorem etale_cohomology_vanishing_negative_degree_zero : A9 := a9_of_a0_a1_eigenbasis_a6 word_filtration_basic aux_statement_7 casimir_real_scalar identity_operator_filtration

theorem inverse_power_square_bound : A10 := inverse_power_bound_holds

theorem orthonormal_eigenbasis_exists : EigenbasisExists := eigenbasis_of_basic word_filtration_basic

theorem functional_calculus : FunctionalCalculusLaws := functional_calculus_of_basic word_filtration_basic

theorem normal_nilpotent_graded_zero : EigenspacesOrthogonalAlt := eigenspaces_orthogonal_of_calculus word_filtration_basic functional_calculus

theorem eigen_gain_high : A12 := eigen_gain_of_moments word_filtration_basic second_moment_bound etale_cohomology_vanishing_negative_degree_zero inverse_power_square_bound functional_calculus

theorem basis_sum_form_values : BasisSumAsFormValues := basis_sum_of_orthogonality word_filtration_basic functional_calculus normal_nilpotent_graded_zero

theorem eigenspace_form_sum : A13 := basis_form_sum_of_gain word_filtration_basic functional_calculus eigen_gain_high basis_sum_form_values

theorem word_length_filtration : B1 := growth_of_basic word_filtration_basic

theorem hilbert_schmidt_growth : B2 := heightFunctionalStatement_of_pairingProperties

theorem tateTwist_local_to_global_strictlyHenselian : B3 := second_derivative_holds

theorem group_facts : UnitaryGroupFacts := group_facts_holds

theorem maximum_principle_one_function : MaximumPrincipleVar := maximum_principle_of_facts hilbert_schmidt_growth tateTwist_local_to_global_strictlyHenselian group_facts

theorem second_derivative_sum_squares : SumSquaresSecondDerivative := second_derivatives_of_growth word_length_filtration group_facts

theorem lieExponentialMajorant_holds : B5 := eigen_weighted_sum_bound word_filtration_basic functional_calculus

theorem maxPr : MaxPr := maxPr_of casimir_real_scalar orthonormal_eigenbasis_exists eigenspace_form_sum group_facts maximum_principle_one_function second_derivative_sum_squares lieExponentialMajorant_holds

end PositivityTheory.CWB
