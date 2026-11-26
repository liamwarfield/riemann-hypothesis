module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ActDiagMemOfWK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.GeneratedSubStable

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ProdModeCharExp
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.CompactLoweringSpanDiagStable
noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section Straight

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

theorem lowerWord_weight (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M}
    (hy : ∀ a, E a a y = (μ a : ℂ) • y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ (a : Fin n),
      E a a (lowWord E y l) = (lowWt μ l a : ℂ) • lowWord E y l
  | [], _, a => by simpa [lowWord, lowWt] using hy a
  | (c, d) :: l, hl, a => by
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have h := congrArg (fun X : Module.End ℂ M => X (lowWord E y l)) (hE a a c d rfl hcd.2)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [lowerWord_weight hE hy l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) a, map_smul,
      sub_eq_iff_eq_add] at h
    simp only [lowWord, lowWt]
    rw [h]
    simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases hac : a = c <;> by_cases had : a = d
    · subst hac; subst had; simp
    · subst hac
      simp only [if_neg had, if_neg (Ne.symm had), LinearMap.zero_apply, sub_zero]
      push_cast
      module
    · subst had
      simp only [if_neg hac, LinearMap.zero_apply, zero_sub]
      push_cast
      module
    · simp [hac, had, Ne.symm had]

theorem compactLoweringSpan_diag_stable (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M}
    (hy : ∀ a, E a a y = (μ a : ℂ) • y) (a : Fin n) :
    ∀ x ∈ kLowSpan ε E y, E a a x ∈ kLowSpan ε E y := by
  have : kLowSpan ε E y ≤ (kLowSpan ε E y).comap (E a a) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨l, hl, rfl⟩
    show E a a (lowWord E y l) ∈ kLowSpan ε E y
    rw [lowerWord_weight hE hy l hl a]
    exact Submodule.smul_mem _ _ (lowWord_mem hl)
  exact fun x hx => this hx

theorem lowerWord_mem_span_of_ge (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M}
    (hy : ∀ a, E a a y = (μ a : ℂ) • y)
    {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) {a b : Fin n} (hab : b ≤ a)
    (hε : ε a = ε b) : E a b (lowWord E y l) ∈ kLowSpan ε E y := by
  rcases hab.lt_or_eq with h | rfl
  · exact kLowSpan_low_stable (c := a) (d := b) ⟨h, hε⟩ _ (lowWord_mem hl)
  · exact compactLoweringSpan_diag_stable hE hy b _ (lowWord_mem hl)

theorem lowerWord_raise_mem_span (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ a b : Fin n, a < b → ε a = ε b →
      E a b (lowWord E y l) ∈ kLowSpan ε E y
  | [], _, a, b, hab, hε => by
    simp only [lowWord]
    rw [hy.2 a b hab hε]
    exact Submodule.zero_mem _
  | (c, d) :: l, hl, a, b, hab, hε => by
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have hl' : ∀ p ∈ l, IsKLow ε p := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have ih := lowerWord_raise_mem_span hE hy l hl'
    have key : ∀ a' b' : Fin n, ε a' = ε b' → E a' b' (lowWord E y l) ∈ kLowSpan ε E y := by
      intro a' b' h'
      rcases lt_or_ge a' b' with h | h
      · exact ih a' b' h h'
      · exact lowerWord_mem_span_of_ge hE hy.1 hl' h h'
    have h := congrArg (fun X : Module.End ℂ M => X (lowWord E y l)) (hE a b c d hε hcd.2)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [sub_eq_iff_eq_add] at h
    simp only [lowWord]
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (kLowSpan_low_stable hcd _ (ih a b hab hε))
    · split_ifs with hbc
      · subst hbc; exact key a d (hε.trans hcd.2)
      · simp
    · split_ifs with hda
      · subst hda; exact key c b (hcd.2.trans hε)
      · simp

theorem compactLoweringSpan_kStable (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    IsKStableSub ε E (kLowSpan ε E y) := by
  intro a b hab
  rcases lt_or_ge a b with h | h
  · have : kLowSpan ε E y ≤ (kLowSpan ε E y).comap (E a b) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨l, hl, rfl⟩
      exact lowerWord_raise_mem_span hE hy l hl a b h hab
    exact fun x hx => this hx
  · rcases h.lt_or_eq with h | rfl
    · exact kLowSpan_low_stable ⟨h, hab⟩
    · exact compactLoweringSpan_diag_stable hE hy.1 b

end Straight

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section T

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem tco_diagE (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a b y) =
      E a b (tcoef ((fockBasis n).coord s) y) +
        tcoef ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a b) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    simp only [diagE, sgE_cpT, eT, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
      LinearMap.id_apply, map_add, tcoef_tmul, LinearMap.coe_comp, Function.comp_apply, map_smul]
  | add y y' hy hy' =>
    rw [map_add (f := _), map_add (f := _), hy, hy', map_add (f := _), map_add (f := _), map_add (f := _)]
    abel

theorem tco_diagE_wt (E : Fin n → Fin n → Module.End ℂ N) (a : Fin n)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a a y) =
      E a a (tcoef ((fockBasis n).coord s) y) + ((fockWt ε s a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) y := by
  rw [tco_diagE, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a a) y]
  congr 1
  rw [Finset.sum_eq_single s]
  · simp [fockBasis_wt]
  · intro b _ hb
    simp [fockBasis_wt, Finsupp.single_apply, hb]
  · simp

end T

theorem modeChar_exp (θ : Fin n → ℝ) (x : Fin n × Fin n) :
    modeChar ε (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) x =
      Complex.exp (((∑ a, modeWt ε x a * θ a : ℝ) : ℂ) * Complex.I) := by
  unfold modeChar modeWt
  by_cases h : IsPhys ε x
  · rw [if_pos h, if_pos (show ε x.1 = true ∧ ε x.2 = false from h), Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [root, Pi.sub_apply, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  · rw [if_neg h, if_neg (show ¬(ε x.1 = true ∧ ε x.2 = false) from h)]
    simp

theorem prod_modeChar_exp (θ : Fin n → ℝ) (s : Finset (Fin (n * n))) :
    ∏ m ∈ s, modeChar ε (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) (finProdFinEquiv.symm m) =
      Complex.exp (((∑ a, fockWt ε s a * θ a : ℝ) : ℂ) * Complex.I) := by
  simp only [modeChar_exp]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 2
  simp only [fockWt, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem diag_mem_Kset' (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε :=
  bwt_diag_mem_Kset ε θ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem wK_diag_wt (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {μ : Fin n → ℝ}
    {y : TensorProduct ℂ D (Fock n)} (hy : ∀ a, diagE ε (eT E) cpT cmT a a y = ((μ a : ℝ) : ℂ) • y)
    (θ : Fin n → ℝ) :
    wK hD (diag_mem_Kset' ε θ) y = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y := by
  apply coordH_injective
  funext s
  rw [map_smul, Pi.smul_apply, coordH_apply, coordH_apply, tco_wK]
  rw [Finset.sum_eq_single s]
  · rw [ff_diag, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, prod_modeChar_exp]
    have hts : ∀ a, E a a (tcoef ((fockBasis n).coord s) y) =
        (((μ - fockWt ε s) a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) y := by
      intro a
      have h := congrArg (tcoef ((fockBasis n).coord s)) (hy a)
      rw [tco_diagE_wt, map_smul] at h
      rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h]
      abel
    have hw := (isWtOn_iff hσ hD (tcoef ((fockBasis n).coord s) y) (μ - fockWt ε s)).2 hts θ
      (bwt_diag_mem_Kset ε θ)
    rw [Submodule.coe_smul]
    change _ • σ _ _ = _
    rw [hw, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    simp only [Pi.sub_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  · intro b _ hb
    rw [ff_diag, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      if_neg hb, smul_zero, zero_smul]
  · simp

theorem bwtDiag_inK (ε : Fin n → Bool) (θ : Fin n → ℝ) : inK ε (bwtDiag θ) := by
  refine ⟨bwtDiag_inG ε θ, ?_⟩
  unfold bwtDiag Jm
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  ring

theorem wK_congr (hD : IsDerivedOn ε σ D E) {k k' : Matrix (Fin n) (Fin n) ℂ} (h : k = k')
    (hk : k ∈ Kset ε) (hk' : k' ∈ Kset ε) (y : TensorProduct ℂ D (Fock n)) :
    wK hD hk y = wK hD hk' y := by
  subst h
  rfl

theorem diagE_wt_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {μ : Fin n → ℝ}
    {y : TensorProduct ℂ D (Fock n)}
    (hy : ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) y = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y)
    (a : Fin n) : diagE ε (eT E) cpT cmT a a y = ((μ a : ℝ) : ℂ) • y := by
  set θ : Fin n → ℝ := Pi.single a 1 with hθ
  have hX := bwtDiag_inK ε θ
  have hcurve : ∀ t : ℝ, coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) =
      Complex.exp (((t * μ a : ℝ) : ℂ) * Complex.I) • coordH y := by
    intro t
    rw [wK_congr hD (bwt_exp θ t) _ (diag_mem_Kset' ε (fun b => t * θ b)), hy, map_smul]
    congr 4
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [hθ, Pi.single_apply, hb]) (by simp)]
    simp [hθ]
    ring
  have hder1 : HasDerivAt (fun t : ℝ => coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y))
      (coordH (actM (diagE ε (eT E) cpT cmT) (bwtDiag θ) y)) 0 :=
    hasDerivAt_pi.2 fun s => tco_wK_hasDeriv hσ hD hX y s
  have he : HasDerivAt (fun t : ℝ => Complex.exp (((t * μ a : ℝ) : ℂ) * Complex.I))
      (((μ a : ℝ) : ℂ) * Complex.I) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ((t * μ a : ℝ) : ℂ)) ((1 * μ a : ℝ) : ℂ) 0 :=
      ((hasDerivAt_id (0 : ℝ)).mul_const (μ a)).ofReal_comp
    have h2 := (h1.mul_const Complex.I).cexp
    convert h2 using 1
    simp
  have hder2 := he.smul_const (coordH y)
  rw [funext hcurve] at hder1
  have heq := hder1.unique hder2
  have h2 : actM (diagE ε (eT E) cpT cmT) (bwtDiag θ) y = (((μ a : ℝ) : ℂ) * Complex.I) • y :=
    coordH_injective (by rw [heq, map_smul])
  rw [bwtDiag, bwt_actM_diag, LinearMap.sum_apply,
    Finset.sum_eq_single a (fun b _ hb => by simp [hθ, Pi.single_apply, hb]) (by simp)] at h2
  simp only [hθ, Pi.single_eq_same, Complex.ofReal_one, one_mul, LinearMap.smul_apply] at h2
  have h3 := congrArg (fun v => (-Complex.I) • v) h2
  simp only [smul_smul] at h3
  have hI : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have hI' : -Complex.I * (((μ a : ℝ) : ℂ) * Complex.I) = ((μ a : ℝ) : ℂ) := by
    linear_combination (-((μ a : ℝ) : ℂ)) * Complex.I_mul_I
  rw [hI, one_smul, hI'] at h3
  exact h3

section Orth

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem kLow_wt_eq_lowWt {A : Fin n → Fin n → Module.End ℂ (TensorProduct ℂ M (Fock n))}
    (hK : Formalism.REAL.KRel ε A)
    (hA : ∀ (a : Fin n) (y y' : TensorProduct ℂ M (Fock n)), tform (A a a y) y' = tform y (A a a y'))
    {γ : Fin n → ℝ} {z : TensorProduct ℂ M (Fock n)} (hz : IsKHWVec ε A γ z)
    {y : TensorProduct ℂ M (Fock n)} (hy : y ∈ kLowSpan ε A z) (hy0 : y ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ a, A a a y = ((μ a : ℝ) : ℂ) • y) :
    ∃ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) ∧ μ = lowWt γ l := by
  by_contra hne
  push Not at hne
  have horth : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → tform y (lowWord A z l) = 0 := by
    intro l hl
    obtain ⟨a, ha⟩ : ∃ a, μ a ≠ lowWt γ l a := by
      by_contra h
      push Not at h
      exact hne l hl (funext h)
    have h1 := hA a y (lowWord A z l)
    rw [hμ a, lowerWord_weight hK hz.1 l hl a, tensorForm_smul_left, tform_smul_right, Complex.star_def,
      Complex.conj_ofReal] at h1
    have h2 : (((μ a : ℝ) : ℂ) - ((lowWt γ l a : ℝ) : ℂ)) * tform y (lowWord A z l) = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (by exact_mod_cast sub_eq_zero.1 h) ha
    · exact h
  have hall : ∀ w ∈ kLowSpan ε A z, tform y w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact horth l hl
    | zero => simp [tform]
    | add x x' _ _ hx hx' => rw [tform_add_right, hx, hx', add_zero]
    | smul c x _ hx => rw [tform_smul_right, hx, mul_zero]
  have := tform_self_re_pos hy0
  rw [hall y hy] at this
  simp at this

end Orth

theorem cdom_lowWt (γ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → Formalism.MainNotions.S.CDom ε (lowWt γ l) γ := by
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [lowWt]⟩
  | cons p l ih =>
    intro hl
    obtain ⟨c, hc, heq⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨c0, d0⟩ := p
    have hp : IsKLow ε (c0, d0) := hl _ (List.mem_cons_self ..)
    refine ⟨fun a b => c a b + if a = d0 ∧ b = c0 then 1 else 0, ?_, ?_⟩
    · intro a b h
      by_cases h' : a = d0 ∧ b = c0
      · obtain ⟨rfl, rfl⟩ := h'
        exact ⟨hp.1, hp.2.symm⟩
      · dsimp only at h
        rw [if_neg h', add_zero] at h
        exact hc a b h
    · have hs : (∑ a, ∑ b, (((if a = d0 ∧ b = c0 then 1 else 0 : ℕ)) : ℝ) • Formalism.REAL.root a b) =
          Formalism.REAL.root d0 c0 := by
        rw [Finset.sum_eq_single d0 (fun a _ ha => Finset.sum_eq_zero fun b _ => by simp [ha]) (by simp),
          Finset.sum_eq_single c0 (fun b _ hb => by simp [hb]) (by simp)]
        simp
      simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, hs, ← heq, lowWt]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, root, Formalism.REAL.root]
      ring

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem kset_mem_UJset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  show kᴴ * Jm ε * k = Jm ε
  rw [mul_assoc, ← hk.2, ← mul_assoc, ← Matrix.star_eq_conjTranspose,
    (Matrix.mem_unitaryGroup_iff').1 hk.1, one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem inner_sigD (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (u v : D) : inner ℂ (sigD hD hk u) (sigD hD hk v) = inner ℂ u v := by
  let Lk : H →ₗᵢ[ℂ] H := { toLinearMap := (σ k : H →ₗ[ℂ] H), norm_map' := hσ.2.1 k (kset_mem_UJset hk) }
  rw [Submodule.coe_inner, Submodule.coe_inner]
  exact Lk.inner_map_map u v

theorem coord_ff_basis (k : Matrix (Fin n) (Fin n) ℂ) (s s' : Finset (Fin (n * n))) :
    (fockBasis n).coord s (ff ε k (fockBasis n s')) = ffMat ε k s s' := by
  rw [ffMat, LinearMap.toMatrix_apply, Module.Basis.coord_apply, AlgHom.toLinearMap_apply]

theorem tform_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (y y' : TensorProduct ℂ D (Fock n)) :
    tform (wK hD hk y) (wK hD hk y') = tform y y' := by
  have hU := (Matrix.mem_unitaryGroup_iff').1 (ffMat_unitary (ε := ε) hk)
  unfold tform
  simp only [tco_wK, coord_ff_basis, sum_inner, inner_sum, inner_smul_left, inner_smul_right, inner_sigD hσ hD hk,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Finset.sum_comm]
  have h1 : ∀ s'' : Finset (Fin (n * n)), ∑ x, ffMat ε k x s' * ((starRingEnd ℂ) (ffMat ε k x s'') *
      inner ℂ (tcoef ((fockBasis n).coord s'') y) (tcoef ((fockBasis n).coord s') y')) =
      (1 : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ) s'' s' *
        inner ℂ (tcoef ((fockBasis n).coord s'') y) (tcoef ((fockBasis n).coord s') y') := by
    intro s''
    rw [← hU, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.star_apply, Complex.star_def]
    ring
  rw [Finset.sum_congr rfl fun s'' _ => h1 s'']
  simp [Matrix.one_apply]

theorem sigD_one (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    sigD hD h1 = LinearMap.id := by
  ext v
  simp [sigD, hσ.1.1]

theorem wK_one (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    wK hD h1 = LinearMap.id := by
  rw [wK, sigD_one hσ hD h1, ff_one]
  exact TensorProduct.map_id

theorem wK_mul (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ Kset ε) (hb : b ∈ Kset ε) (hab : a * b ∈ Kset ε) :
    wK hD hab = wK hD ha ∘ₗ wK hD hb := by
  have hs : sigD hD hab = sigD hD ha ∘ₗ sigD hD hb := by
    ext v
    simp [sigD, hσ.1.2 a (kset_mem_UJset ha) b (kset_mem_UJset hb)]
  rw [wK, wK, wK, hs, ff_mul ha hb, ← TensorProduct.map_comp]
  rfl

theorem one_mem_Kset' : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨one_mem _, by rw [one_mul, mul_one]⟩

theorem mul_mem_Kset' {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Kset ε) (hb : b ∈ Kset ε) : a * b ∈ Kset ε :=
  ⟨mul_mem ha.1 hb.1, by rw [mul_assoc, hb.2, ← mul_assoc, ha.2, mul_assoc]⟩

section TSubSec

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def TSub (S : Submodule ℂ (TensorProduct ℂ M (Fock n))) : Type _ := S

variable {S : Submodule ℂ (TensorProduct ℂ M (Fock n))}

instance : AddCommGroup (TSub S) := inferInstanceAs (AddCommGroup S)

instance : Module ℂ (TSub S) := inferInstanceAs (Module ℂ S)

def tsubVal (S : Submodule ℂ (TensorProduct ℂ M (Fock n))) : TSub S →ₗ[ℂ] TensorProduct ℂ M (Fock n) :=
  S.subtype

theorem tsubVal_injective : Function.Injective (tsubVal S) := Subtype.val_injective

theorem tsubVal_mem (x : TSub S) : tsubVal S x ∈ S := (x : S).2

instance tsubCore : InnerProductSpace.Core ℂ (TSub S) where
  inner x y := tform (tsubVal S x) (tsubVal S y)
  conj_inner_symm x y := tform_conj _ _
  re_inner_nonneg x := by
    by_cases h : tsubVal S x = 0
    · rw [h]
      simp [tform]
    · exact (tform_self_re_pos h).le
  add_left x y z := by
    simp only [map_add (f := _)]
    exact tform_add_left _ _ _
  smul_left x y r := by
    simp only [map_smul]
    exact tensorForm_smul_left r _ _
  definite x h := by
    by_contra hx
    have hx' : tsubVal S x ≠ 0 := fun h0 => hx (tsubVal_injective (h0.trans (map_zero _).symm))
    have h' : tform (tsubVal S x) (tsubVal S x) = 0 := h
    have := tform_self_re_pos hx'
    rw [h'] at this
    simp at this

instance : NormedAddCommGroup (TSub S) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (TSub S) := InnerProductSpace.ofCore _

theorem tsub_inner (x y : TSub S) : inner ℂ x y = tform (tsubVal S x) (tsubVal S y) := rfl

instance [h : FiniteDimensional ℂ S] : FiniteDimensional ℂ (TSub S) := h

end TSubSec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

def tOp (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ S]
    (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S, wK hD hk y ∈ S)
    (k : Matrix (Fin n) (Fin n) ℂ) : TSub S →L[ℂ] TSub S :=
  @dite _ (k ∈ Kset ε) (Classical.propDecidable _)
    (fun hk => LinearMap.toContinuousLinearMap
      (((wK hD hk).restrict (hSK k hk) : S →ₗ[ℂ] S) : TSub S →ₗ[ℂ] TSub S)) (fun _ => 0)

section Op

variable (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ S]
  (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S, wK hD hk y ∈ S)

theorem tOp_apply {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : TSub S) :
    tsubVal S (tOp hD hSK k x) = wK hD hk (tsubVal S x) := by
  simp only [tOp, dif_pos hk]
  rfl

theorem tOp_isURepOn (hσ : IsURepOn (UJset ε) σ) :
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) (tOp hD hSK) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext x
    apply tsubVal_injective
    rw [tOp_apply hD hSK one_mem_Kset', wK_one hσ hD]
    rfl
  · intro a ha b hb
    ext x
    apply tsubVal_injective
    rw [tOp_apply hD hSK (mul_mem_Kset' ha hb), ContinuousLinearMap.comp_apply, tOp_apply hD hSK ha,
      tOp_apply hD hSK hb, wK_mul hσ hD ha hb]
    rfl
  · intro g hg v
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), tsub_inner, tsub_inner,
      tOp_apply hD hSK hg, tform_wK hσ hD hg]
  · intro v
    have hΨ : Set.EqOn (fun g => coordH (tsubVal S (tOp hD hSK g v)))
        (fun g => fun s => ∑ s', ffMat ε g s s' • σ g ((tcoef ((fockBasis n).coord s') (tsubVal S v) : D) : H))
        (Formalism.REAL.Kset ε) := by
      intro g hg
      have hg' : g ∈ Kset ε := hg
      funext s
      simp only
      rw [tOp_apply hD hSK hg', coordH_apply, tco_wK, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [coord_ff_basis]
      rfl
    have hc : ContinuousOn (fun g => coordH (tsubVal S (tOp hD hSK g v))) (Formalism.REAL.Kset ε) := by
      refine ContinuousOn.congr ?_ hΨ
      refine continuousOn_pi.2 fun s => continuousOn_finsetSum _ fun s' _ => ?_
      exact (ffMat_continuous s s').continuousOn.smul
        ((hσ.2.2 _).mono fun g hg => kset_mem_UJset hg)
    have hinj : Function.Injective (coordH ∘ₗ tsubVal S) := coordH_injective.comp tsubVal_injective
    let e := LinearEquiv.ofInjective _ hinj
    have hcont : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
    have hfe : (fun g => tOp hD hSK g v) =
        fun g => e.symm ⟨(coordH ∘ₗ tsubVal S) (tOp hD hSK g v), LinearMap.mem_range_self _ _⟩ := by
      funext g
      refine (e.symm_apply_apply (tOp hD hSK g v)).symm.trans ?_
      congr 1
    rw [hfe, continuousOn_iff_continuous_restrict]
    exact hcont.comp ((continuousOn_iff_continuous_restrict.1 hc).subtype_mk _)

end Op

section KType

variable (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ S]
  (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S, wK hD hk y ∈ S)

theorem tOp_trace {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    LinearMap.trace ℂ (TSub S) (tOp hD hSK k : TSub S →ₗ[ℂ] TSub S) =
      LinearMap.trace ℂ S ((wK hD hk).restrict (hSK k hk)) := by
  simp only [tOp, dif_pos hk]
  rfl

theorem tOp_isKTypeOf (hσ : IsURepOn (UJset ε) σ) {γ : Fin n → ℝ}
    (hS : IsKIrrHW ε (diagE ε (eT E) cpT cmT) γ S) :
    Formalism.MainNotions.S.IsKTypeOf ε (tOp hD hSK) γ ⊤ := by
  classical
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hKA : Formalism.REAL.KRel ε (diagE ε (eT E) cpT cmT) :=
    fun a b c d hab hcd => diagAction_commutator (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b c d hab hcd
  obtain ⟨_, hSs, hirr, w, hwS, hw0, hwK⟩ := hS
  have hSeq : kLowSpan ε (diagE ε (eT E) cpT cmT) w = S := by
    have hle := kLowSpan_le hSs hwS
    rcases hirr _ hle (compactLoweringSpan_kStable hKA hwK) with h | h
    · exfalso
      apply hw0
      have := self_mem_kLowSpan (ε := ε) (E := diagE ε (eT E) cpT cmT) w
      rw [h, Submodule.mem_bot] at this
      exact this
    · exact h
  refine ⟨inferInstance, fun g _ v _ => Submodule.mem_top, ?_, ?_, ?_⟩
  · intro S'' _ hK''
    let P : Submodule ℂ (TensorProduct ℂ D (Fock n)) := S''.map (tsubVal S)
    have hPS : P ≤ S := by
      rintro _ ⟨x, _, rfl⟩
      exact tsubVal_mem x
    have hPfd : FiniteDimensional ℂ P := Module.Finite.map S'' (tsubVal S)
    have hPK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ P, wK hD hk y ∈ P := by
      rintro k hk _ ⟨x, hx, rfl⟩
      exact ⟨tOp hD hSK k x, hK'' k hk x hx, tOp_apply hD hSK hk x⟩
    have hPs : IsKStableSub ε (diagE ε (eT E) cpT cmT) P := fun a b hab y hy =>
      diagE_mem_of_wK hσ hD P hPfd hPK hab hy
    rcases hirr P hPS hPs with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have : tsubVal S x ∈ P := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact tsubVal_injective (this.trans (map_zero _).symm)
    · right
      rw [eq_top_iff]
      intro x _
      have hxP : tsubVal S x ∈ P := by
        rw [h]
        exact tsubVal_mem x
      obtain ⟨x', hx', hxx⟩ := hxP
      exact (tsubVal_injective hxx) ▸ hx'
  · refine ⟨(show TSub S from ⟨w, hwS⟩), Submodule.mem_top, ?_, ?_⟩
    · intro h
      apply hw0
      have := congrArg (tsubVal S) h
      rwa [map_zero] at this
    · intro θ _
      apply tsubVal_injective
      rw [tOp_apply hD hSK (diag_mem_Kset' ε θ), map_smul]
      exact wK_diag_wt hσ hD hwK.1 θ
  · intro μ v _ hv0 hwt
    have hy : ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (tsubVal S v) =
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • tsubVal S v := by
      intro θ
      rw [← tOp_apply hD hSK (diag_mem_Kset' ε θ), hwt θ (bwt_diag_mem_Kset ε θ), map_smul]
    have hμ := diagE_wt_of_wK hσ hD hy
    have hvS : tsubVal S v ∈ kLowSpan ε (diagE ε (eT E) cpT cmT) w := hSeq ▸ tsubVal_mem v
    have hv0' : tsubVal S v ≠ 0 := fun h => hv0 (tsubVal_injective (h.trans (map_zero _).symm))
    obtain ⟨l, hl, rfl⟩ := kLow_wt_eq_lowWt hKA (fun a y y' => tensorForm_diagAction_adjoint hU rfl y y') hwK hvS hv0' hμ
    exact cdom_lowWt γ l hl

theorem tSub_nontrivial {γ : Fin n → ℝ} (hS : IsKIrrHW ε (diagE ε (eT E) cpT cmT) γ S) : Nontrivial (TSub S) := by
  obtain ⟨_, _, _, w, hwS, hw0, _⟩ := hS
  refine ⟨⟨(show TSub S from ⟨w, hwS⟩), 0, fun h => hw0 ?_⟩⟩
  have := congrArg (tsubVal S) h
  rwa [map_zero] at this

end KType

end ReciprocityTheory.ChartRestriction.DS.TRGap
