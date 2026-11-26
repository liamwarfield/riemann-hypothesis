module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTauComponentFrameOfLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleTwistCoboundaryOnBall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsVanishAtPrimeOfAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulMemOfTwistedInvariantModLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulMemOfTwistedInvariantModLattice
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.FrameInv

variable {l : ℕ} [Fact l.Prime] {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
  {χ : GQ l →* ℚ_[l]ˣ}

variable {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)}

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
private theorem continuous_algebraMap_padicComplex_lemma_7 :
    Continuous (algebraMap ℚ_[l] ℂ_[l]) :=
  continuous_algebraMap ℚ_[l] ℂ_[l]

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
private theorem exists_primitiveRoot_primePow_padicAlgCl_lemma_9 (n : ℕ) :
    ∃ ζ : _root_.Formalism.BasicNotions.Loc.Om l, IsPrimitiveRoot ζ (l ^ n) := by
  have hl : (l : PadicAlgCl l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  haveI : NeZero ((l ^ n : ℕ) : PadicAlgCl l) := ⟨by push_cast; exact pow_ne_zero n hl⟩
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ n) (PadicAlgCl l))
    (Polynomial.degree_cyclotomic_pos _ _ hpos).ne'
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).1 hζ⟩

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
private theorem continuous_cyclotomicCharacter_lemma_8 {χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ}
    (hχ : _root_.GlobalTheory.Cyc.IsCyc χ) : Continuous fun g => (χ g : ℚ_[l]) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hε three_pos) (inv_lt_one_of_one_lt₀ hl1)
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_primePow_padicAlgCl_lemma_9 (l := l) m
  filter_upwards [_root_.GlobalTheory.Cyc.eventually_apply_eq ζ g₀] with g hg
  obtain ⟨a, ha, hga⟩ := hχ g m ζ hζ.pow_eq_one
  obtain ⟨a₀, ha₀, hga₀⟩ := hχ g₀ m ζ hζ.pow_eq_one
  have hpow : (l : ℝ) ^ (-(m : ℤ)) = (l : ℝ)⁻¹ ^ m := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero m (Fact.out : l.Prime).ne_zero)
  have heq : ζ ^ a = ζ ^ a₀ := by rw [← hga, ← hga₀, hg]
  have hdvd : ((l ^ m : ℕ) : ℤ) ∣ (a₀ : ℤ) - a := by
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ hζ0, zpow_natCast, zpow_natCast, heq, div_self]
    exact pow_ne_zero _ hζ0
  have hint : ‖(((a₀ : ℤ) - a : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    rw [Padic.norm_int_le_pow_iff_dvd]
    exact_mod_cast hdvd
  rw [dist_eq_norm]
  have hsplit : (χ g : ℚ_[l]) - χ g₀ =
      ((χ g : ℚ_[l]) - a) - ((χ g₀ : ℚ_[l]) - a₀) - ((((a₀ : ℤ) - a : ℤ) : ℚ_[l])) := by
    push_cast
    ring
  rw [hsplit]
  calc ‖((χ g : ℚ_[l]) - a) - ((χ g₀ : ℚ_[l]) - a₀) - ((((a₀ : ℤ) - a : ℤ) : ℚ_[l]))‖
      ≤ ‖(χ g : ℚ_[l]) - a‖ + ‖(χ g₀ : ℚ_[l]) - a₀‖ + ‖(((a₀ : ℤ) - a : ℤ) : ℚ_[l])‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ (l : ℝ) ^ (-(m : ℤ)) + (l : ℝ) ^ (-(m : ℤ)) + (l : ℝ) ^ (-(m : ℤ)) := by
        gcongr
    _ < ε := by
        rw [hpow]
        linarith

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
private theorem continuous_cyclotomicCharPow_lemma_6 {χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ}
    (hχ : _root_.GlobalTheory.Cyc.IsCyc χ) (i : ℤ) :
    Continuous (_root_.GlobalTheory.Cyc.chiC χ i) := by
  have h : _root_.GlobalTheory.Cyc.chiC χ i =
      fun g => algebraMap ℚ_[l] ℂ_[l] ((χ g : ℚ_[l]) ^ i) := by
    funext g
    unfold _root_.GlobalTheory.Cyc.chiC
    rw [Units.val_zpow_eq_zpow_val]
  rw [h]
  exact continuous_algebraMap_padicComplex_lemma_7.comp
    ((continuous_cyclotomicCharacter_lemma_8 hχ).zpow₀ i fun g => Or.inl (Units.ne_zero _))

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
variable (act : _root_.Formalism.BasicNotions.Loc.GQ l →* ℂ_[l] ≃+* ℂ_[l]) (χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
  (U : _root_.Formalism.BasicNotions.Loc.GQ l → Matrix (Fin r) (Fin r) ℂ_[l]) in
private theorem continuousOn_twistedAction_lemma (hact : _root_.GlobalTheory.Cyc.IsActC act)
    (hχ : _root_.GlobalTheory.Cyc.IsCyc χ) {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {m : ℕ} {g : _root_.Formalism.BasicNotions.Loc.GQ l}
    (hF : _root_.GlobalTheory.Cyc.Frame χ K m U g) (y : Fin r → ℂ_[l]) :
    ContinuousOn (fun σ => _root_.GlobalTheory.Cyc.twAct act χ i U σ y)
      (_root_.GlobalTheory.Cyc.Gj K m) := by
  unfold _root_.GlobalTheory.Cyc.twAct
  refine continuousOn_pi.2 fun a => ?_
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
  refine (continuous_cyclotomicCharPow_lemma_6 hχ i).continuousOn.mul ?_
  refine continuousOn_finsetSum _ fun b _ => ?_
  exact (hF.2.1 a b).mul
    (_root_.GlobalTheory.Cyc.IsActC.continuous_orbit l act hact (y b)).continuousOn

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
private theorem act_algebraMap_padic_lemma_10 {act : _root_.Formalism.BasicNotions.Loc.GQ l →* ℂ_[l] ≃+* ℂ_[l]}
    (hact : _root_.GlobalTheory.Cyc.IsActC act) (σ : _root_.Formalism.BasicNotions.Loc.GQ l) (x : ℚ_[l]) :
    act σ (algebraMap ℚ_[l] ℂ_[l] x) = algebraMap ℚ_[l] ℂ_[l] x := by
  have h := hact.1 σ (algebraMap ℚ_[l] (PadicAlgCl l) x)
  rw [AlgEquiv.commutes] at h
  exact h

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
private theorem cyclotomicCharPow_mul_lemma_11 (χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ) (i : ℤ) (σ τ : _root_.Formalism.BasicNotions.Loc.GQ l) :
    _root_.GlobalTheory.Cyc.chiC χ i (σ * τ) =
      _root_.GlobalTheory.Cyc.chiC χ i σ * _root_.GlobalTheory.Cyc.chiC χ i τ := by
  unfold _root_.GlobalTheory.Cyc.chiC
  rw [map_mul, mul_zpow, Units.val_mul, map_mul]

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
variable (act : _root_.Formalism.BasicNotions.Loc.GQ l →* ℂ_[l] ≃+* ℂ_[l]) (χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
  (U : _root_.Formalism.BasicNotions.Loc.GQ l → Matrix (Fin r) (Fin r) ℂ_[l]) in
private theorem twistedAction_mul_lemma_2 (hact : _root_.GlobalTheory.Cyc.IsActC act) {K : _root_.Formalism.BasicNotions.Loc.FinExt l}
    {m : ℕ} {g : _root_.Formalism.BasicNotions.Loc.GQ l} (hF : _root_.GlobalTheory.Cyc.Frame χ K m U g) {σ τ : _root_.Formalism.BasicNotions.Loc.GQ l}
    (hσ : σ ∈ _root_.GlobalTheory.Cyc.Gj K m) (hτ : τ ∈ _root_.GlobalTheory.Cyc.Gj K m)
    (v : Fin r → ℂ_[l]) :
    _root_.GlobalTheory.Cyc.twAct act χ i U (σ * τ) v =
      _root_.GlobalTheory.Cyc.twAct act χ i U σ (_root_.GlobalTheory.Cyc.twAct act χ i U τ v) := by
  have hfix : ∀ a b, act σ (U τ a b) = U τ a b := fun a b =>
    _root_.GlobalTheory.Cyc.TateS.act_fix hact K hσ (hF.2.2.1 τ hτ a b).1
  have hc : act σ (_root_.GlobalTheory.Cyc.chiC χ i τ) = _root_.GlobalTheory.Cyc.chiC χ i τ := by
    unfold _root_.GlobalTheory.Cyc.chiC
    exact act_algebraMap_padic_lemma_10 hact σ _
  unfold _root_.GlobalTheory.Cyc.twAct
  rw [hF.2.2.2.1 σ hσ τ hτ, cyclotomicCharPow_mul_lemma_11, ← Matrix.mulVec_mulVec, mul_smul,
    ← Matrix.mulVec_smul]
  congr 2
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, hfix, hc, Finset.mul_sum]

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
variable (act : _root_.Formalism.BasicNotions.Loc.GQ l →* ℂ_[l] ≃+* ℂ_[l]) (χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
  (U : _root_.Formalism.BasicNotions.Loc.GQ l → Matrix (Fin r) (Fin r) ℂ_[l]) in
private theorem twistedAction_smul_lemma_3 (σ : _root_.Formalism.BasicNotions.Loc.GQ l) (c : ℂ_[l]) (v : Fin r → ℂ_[l]) :
    _root_.GlobalTheory.Cyc.twAct act χ i U σ (c • v) =
      act σ c • _root_.GlobalTheory.Cyc.twAct act χ i U σ v := by
  unfold _root_.GlobalTheory.Cyc.twAct
  have h : (fun a => act σ ((c • v) a)) = act σ c • fun a => act σ (v a) := by
    funext a
    simp
  rw [h, Matrix.mulVec_smul, smul_comm]

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
variable (act : _root_.Formalism.BasicNotions.Loc.GQ l →* ℂ_[l] ≃+* ℂ_[l]) (χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
  (U : _root_.Formalism.BasicNotions.Loc.GQ l → Matrix (Fin r) (Fin r) ℂ_[l]) in
private theorem twistedAction_sub_lemma_4 (σ : _root_.Formalism.BasicNotions.Loc.GQ l) (v w : Fin r → ℂ_[l]) :
    _root_.GlobalTheory.Cyc.twAct act χ i U σ (v - w) =
      _root_.GlobalTheory.Cyc.twAct act χ i U σ v - _root_.GlobalTheory.Cyc.twAct act χ i U σ w := by
  unfold _root_.GlobalTheory.Cyc.twAct
  have h : (fun a => act σ ((v - w) a)) = (fun a => act σ (v a)) - fun a => act σ (w a) := by
    funext a
    simp
  rw [h, Matrix.mulVec_sub, smul_sub]

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
variable (act : _root_.Formalism.BasicNotions.Loc.GQ l →* ℂ_[l] ≃+* ℂ_[l]) (χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
  (U : _root_.Formalism.BasicNotions.Loc.GQ l → Matrix (Fin r) (Fin r) ℂ_[l]) in
private theorem twistedAction_add_lemma_12 (σ : _root_.Formalism.BasicNotions.Loc.GQ l) (v w : Fin r → ℂ_[l]) :
    _root_.GlobalTheory.Cyc.twAct act χ i U σ (v + w) =
      _root_.GlobalTheory.Cyc.twAct act χ i U σ v + _root_.GlobalTheory.Cyc.twAct act χ i U σ w := by
  unfold _root_.GlobalTheory.Cyc.twAct
  have h : (fun a => act σ ((v + w) a)) = (fun a => act σ (v a)) + fun a => act σ (w a) := by
    funext a
    simp
  rw [h, Matrix.mulVec_add, smul_add]

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
private theorem cyclotomicCharPow_add_lemma_14 (χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ) (a b : ℤ) (σ : _root_.Formalism.BasicNotions.Loc.GQ l) :
    _root_.GlobalTheory.Cyc.chiC χ (a + b) σ =
      _root_.GlobalTheory.Cyc.chiC χ a σ * _root_.GlobalTheory.Cyc.chiC χ b σ := by
  unfold _root_.GlobalTheory.Cyc.chiC
  rw [zpow_add, Units.val_mul, map_mul]

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
variable (act : _root_.Formalism.BasicNotions.Loc.GQ l →* ℂ_[l] ≃+* ℂ_[l]) (χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
  (U : _root_.Formalism.BasicNotions.Loc.GQ l → Matrix (Fin r) (Fin r) ℂ_[l]) in
private theorem twistedAction_eq_charPow_smul_lemma_13 (j : ℤ) (σ : _root_.Formalism.BasicNotions.Loc.GQ l) (v : Fin r → ℂ_[l]) :
    _root_.GlobalTheory.Cyc.twAct act χ i U σ v =
      _root_.GlobalTheory.Cyc.chiC χ (i - j) σ • _root_.GlobalTheory.Cyc.twAct act χ j U σ v := by
  unfold _root_.GlobalTheory.Cyc.twAct
  rw [smul_smul, ← cyclotomicCharPow_add_lemma_14, sub_add_cancel]

open scoped Matrix in
variable {l : ℕ} [Fact l.Prime] in
variable (act : _root_.Formalism.BasicNotions.Loc.GQ l →* ℂ_[l] ≃+* ℂ_[l]) (χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
  (U : _root_.Formalism.BasicNotions.Loc.GQ l → Matrix (Fin r) (Fin r) ℂ_[l]) in
private theorem eq_zero_of_twistedInvariant_offJumps_lemma_5 (hact : _root_.GlobalTheory.Cyc.IsActC act)
    (hχ : _root_.GlobalTheory.Cyc.IsCyc χ) {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {m : ℕ} (hm : _root_.GlobalTheory.Cyc.Lev l m)
    {J : Set ℤ} (hJ : _root_.GlobalTheory.Cyc.HTBasis act χ (_root_.GlobalTheory.Cyc.Gj K m) U J)
    (hi : i ∉ J) {w : Fin r → ℂ_[l]}
    (hw : ∀ σ ∈ _root_.GlobalTheory.Cyc.Gj K m, _root_.GlobalTheory.Cyc.twAct act χ i U σ w = w) :
    w = 0 := by
  obtain ⟨e, u, hli, huJ, he⟩ := hJ
  have hspan : Submodule.span ℂ_[l] (Set.range e) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  let B := Module.Basis.mk hli hspan.ge
  have hB : ∀ k, B k = e k := fun k => Module.Basis.mk_apply hli hspan.ge k
  have hw' := B.sum_repr w
  have hsum : ∀ σ ∈ _root_.GlobalTheory.Cyc.Gj K m, ∀ c : Fin r → ℂ_[l],
      _root_.GlobalTheory.Cyc.twAct act χ i U σ (∑ k, c k • B k) =
        ∑ k, (_root_.GlobalTheory.Cyc.chiC χ (i - u k) σ * act σ (c k)) • B k := by
    intro σ hσ c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show _root_.GlobalTheory.Cyc.twAct act χ i U σ (∑ k, c k • B k) =
        (AddMonoidHom.mk' (_root_.GlobalTheory.Cyc.twAct act χ i U σ)
          (twistedAction_add_lemma_12 act χ i U σ)) (∑ k, c k • B k) from rfl, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [AddMonoidHom.mk'_apply, twistedAction_smul_lemma_3, hB,
      twistedAction_eq_charPow_smul_lemma_13 act χ i U (u k), he σ hσ k, smul_smul, mul_comm]
  have hcoef : ∀ k, B.repr w k = 0 := by
    intro k
    have hk : ∀ σ ∈ _root_.GlobalTheory.Cyc.Gj K m,
        _root_.GlobalTheory.Cyc.chiC χ (i - u k) σ * act σ (B.repr w k) = B.repr w k := by
      intro σ hσ
      have h1 := hsum σ hσ (B.repr w)
      rw [hw', hw σ hσ] at h1
      have h2 := congrArg (fun v => B.repr v k) h1
      simp only [Module.Basis.repr_sum_self] at h2
      exact h2.symm
    exact (_root_.GlobalTheory.CyclotomicTowerSubgroupInclusions.invariants_twist l act χ hact hχ K m hm (i - u k) _ hk).1
      (sub_ne_zero.2 fun h => hi (h ▸ huJ k))
  rw [← hw']
  simp [hcoef]

open scoped Matrix in
theorem _root_.GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod : ∀ (l : ℕ) [Fact l.Prime]
    (act : _root_.Formalism.BasicNotions.Loc.GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ),
    _root_.GlobalTheory.Cyc.IsActC act → _root_.GlobalTheory.Cyc.IsCyc χ →
    ∀ (K : _root_.Formalism.BasicNotions.Loc.FinExt l), ∀ (m r : ℕ), _root_.GlobalTheory.Cyc.Lev l m →
    ∀ (U : _root_.Formalism.BasicNotions.Loc.GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : _root_.Formalism.BasicNotions.Loc.GQ l),
    _root_.GlobalTheory.Cyc.Frame χ K m U g → ∀ J : Finset ℤ,
    _root_.GlobalTheory.Cyc.HTBasis act χ (_root_.GlobalTheory.Cyc.Gj K m) U (J : Set ℤ) →
    ∀ (i : ℤ), i ∉ J → ∀ M : AddSubgroup (Fin r → PadicComplex l),
    _root_.GlobalTheory.Cyc.ball l r ⊆ (M : Set _) →
    (∀ x ∈ M, (l : PadicComplex l) • x ∈ _root_.GlobalTheory.Cyc.ball l r) →
    ∀ y : Fin r → PadicComplex l,
    (∀ σ ∈ _root_.GlobalTheory.Cyc.Gj K m,
      _root_.GlobalTheory.Cyc.twAct act χ i U σ y - y ∈ M) →
    (l : PadicComplex l) ^ (2 + max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • y ∈ M := by
  intro l _ act χ hact hχ K m r hm U g hF J hJ i hi M hball hlM y hy
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hactl : ∀ σ (n : ℕ), act σ ((l : ℂ_[l]) ^ n) = (l : ℂ_[l]) ^ n := by
    intro σ n
    rw [map_pow, map_natCast]
  have hcoc : _root_.GlobalTheory.Cyc.CocOn (_root_.GlobalTheory.Cyc.Gj K m)
      (_root_.GlobalTheory.Cyc.twAct act χ i U) (_root_.GlobalTheory.Cyc.ball l r)
      (fun σ => (l : ℂ_[l]) • (_root_.GlobalTheory.Cyc.twAct act χ i U σ y - y)) := by
    unfold _root_.GlobalTheory.Cyc.CocOn
    refine ⟨?_, fun σ hσ => hlM _ (hy σ hσ), fun σ hσ τ hτ => ?_⟩
    · exact ((continuousOn_twistedAction_lemma act χ i U hact hχ hF y).sub continuousOn_const).const_smul (l : ℂ_[l])
    · simp only
      rw [twistedAction_mul_lemma_2 act χ i U hact hF hσ hτ, twistedAction_smul_lemma_3, twistedAction_sub_lemma_4,
        map_natCast, ← smul_add]
      congr 1
      abel
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∑ a, ‖y a‖ < (l : ℝ) ^ n := pow_unbounded_of_one_lt _ hl1
  have hyball : (l : ℂ_[l]) ^ (n + 1) • y ∈ _root_.GlobalTheory.Cyc.ball l r := by
    show ∀ a, ‖((l : ℂ_[l]) ^ (n + 1) • y) a‖ ≤ 1
    intro a
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow, _root_.GlobalTheory.Cyc.norm_natCast_prime_padicComplex, inv_pow,
      inv_mul_le_iff₀ (pow_pos (by positivity) _), mul_one]
    have h1 : ‖y a‖ ≤ ∑ b, ‖y b‖ :=
      Finset.single_le_sum (fun b _ => norm_nonneg (y b)) (Finset.mem_univ a)
    have h2 : (l : ℝ) ^ n ≤ (l : ℝ) ^ (n + 1) := pow_le_pow_right₀ hl1.le (Nat.le_succ n)
    linarith
  have hcob : _root_.GlobalTheory.Cyc.CobOn (_root_.GlobalTheory.Cyc.Gj K m)
      (_root_.GlobalTheory.Cyc.twAct act χ i U) (_root_.GlobalTheory.Cyc.ball l r)
      (fun σ => (l : ℂ_[l]) ^ n • (l : ℂ_[l]) • (_root_.GlobalTheory.Cyc.twAct act χ i U σ y - y)) := by
    unfold _root_.GlobalTheory.Cyc.CobOn
    refine ⟨(l : ℂ_[l]) ^ (n + 1) • y, hyball, fun σ hσ => ?_⟩
    simp only
    rw [twistedAction_smul_lemma_3, hactl, smul_smul, ← pow_succ, smul_sub]
  obtain ⟨z, hz, hzc⟩ := _root_.GlobalTheory.Cyc.FrameTorsion.torsion_killed l act χ hact hχ K m r hm U g
    hF J hJ i _ n hcoc hcob
  generalize max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i))) = N at hzc ⊢
  have hinv : ∀ σ ∈ _root_.GlobalTheory.Cyc.Gj K m,
      _root_.GlobalTheory.Cyc.twAct act χ i U σ ((l : ℂ_[l]) ^ (2 + N) • y - z) =
        (l : ℂ_[l]) ^ (2 + N) • y - z := by
    intro σ hσ
    have h := hzc σ hσ
    have h' : (l : ℂ_[l]) ^ (2 + N) • (_root_.GlobalTheory.Cyc.twAct act χ i U σ y - y) =
        _root_.GlobalTheory.Cyc.twAct act χ i U σ z - z := by
      rw [show 2 + N = 1 + N + 1 by omega, pow_succ, mul_smul]
      exact h
    rw [smul_sub] at h'
    rw [twistedAction_sub_lemma_4, twistedAction_smul_lemma_3, hactl, sub_eq_sub_iff_sub_eq_sub]
    exact h'
  have hw0 := eq_zero_of_twistedInvariant_offJumps_lemma_5 act χ i U hact hχ hm hJ
    (fun h => hi (Finset.mem_coe.1 h)) hinv
  rw [sub_eq_zero] at hw0
  rw [hw0]
  exact hball hz

end GlobalTheory.FrameInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulMemOfTwistedInvariantModLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_smul_mem_of_twistedInvariant_mod_lattice : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ), i ∉ J → ∀ M : AddSubgroup (Fin r → PadicComplex l), ball l r ⊆ (M : Set _) → (∀ x ∈ M, (l : PadicComplex l) • x ∈ ball l r) → ∀ y : Fin r → PadicComplex l, (∀ σ ∈ Gj K m, twAct act χ i U σ y - y ∈ M) → (l : PadicComplex l) ^ (2 + max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • y ∈ M := by
  first | exact @GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod | exact GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod | (intros; apply GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMemOL
namespace GlobalTheory.IntegerRingPowers

open Formalism.BasicNotions

theorem exists_pow_smul_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (a : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * a ∈ Loc.OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hint : IsIntegral ℚ_[l] a := IsIntegral.of_finite ℚ_[l] a
  obtain ⟨⟨m, hm⟩, hmi⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ_[l]) a hint
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.valuation, ?_⟩
  rw [Loc.OL, mem_integralClosure_iff]
  have hmi' : IsIntegral ℤ_[l] (m • a) := hmi
  have e := PadicInt.unitCoeff_spec hm0
  set u := PadicInt.unitCoeff hm0
  have key : (l : ↥LL.1) ^ m.valuation * a = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (m • a) := by
    conv_rhs => rw [e]
    rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast]
  rw [key]
  exact IsIntegral.smul _ hmi'

theorem smul_mem_of_mem_OL {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) {c : ↥LL.1} (hc : c ∈ Loc.OL LL)
    {w : T.V} (hw : w ∈ T.L.T) : c • w ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(Loc.OL LL)) hw
  have e := T.towO.smul_assoc (⟨c, hc⟩ : ↥(Loc.OL LL)) (1 : ↥LL.1) w
  have e2 : ((⟨c, hc⟩ : ↥(Loc.OL LL)) • (1 : ↥LL.1)) = c := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e2, one_smul] at e
  rw [e]; exact h

theorem natCast_pow_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (k : ℕ) :
    (l : ↥LL.1) ^ k ∈ Loc.OL LL :=
  (Loc.OL LL).pow_mem ((Loc.OL LL).natCast_mem l) k

theorem pow_smul_smul_eq {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) (a : ↥LL.1) (x : T.V) (k n : ℕ) :
    (l : ↥LL.1) ^ (k + n) • a • x = ((l : ↥LL.1) ^ k * a) • ((l : ↥LL.1) ^ n • x) := by
  rw [pow_add, mul_smul, mul_smul]
  congr 1
  rw [← mul_smul, ← mul_smul, mul_comm]

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (K LL : Formalism.BasicNotions.Loc.FinExt l)
    (T : Formalism.BasicNotions.LocLat ↥(Formalism.BasicNotions.Loc.GK K) ℚ_[l]
      ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↥(Formalism.BasicNotions.Loc.OL LL))
    (v : Formalism.BasicNotions.LocLat.V T),
    ∃ (n : ℕ), (↑l : ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l))) ^ n • v ∈
      Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T) := by
  intro l _ K LL T v
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := hy
    refine ⟨n + k, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL k) hn
    · rw [pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL n) hk
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_smul_mem_OL LL a
    refine ⟨k + n, ?_⟩
    rw [pow_smul_smul_eq T a x k n]
    exact smul_mem_of_mem_OL T hk hn

end GlobalTheory.IntegerRingPowers
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsVanishAtPrimeOfAdmissible
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.InvKilled

variable {l : ℕ} [Fact l.Prime]

theorem exists_pow_smul_mem (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegerRingPowers.main
  | exact _root_.GlobalTheory.IntegerRingPowers.main
  | (apply _root_.GlobalTheory.IntegerRingPowers.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerRingPowers.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerRingPowers.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerRingPowers.main ..)

theorem killed_of_coordinates {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [CharZero LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) [Module ℤ_[l] ↥T.L.T]
    (hsm : ∀ (k : ℕ) (t : ↥T.L.T),
      ((((l : ℤ_[l]) ^ k) • t : ↥T.L.T) : T.V) = (l : LL) ^ k • (t : T.V))
    (ac : G → (↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T)) (hac : ∀ g t, ((ac g t : ↥T.L.T) : T.V) = T.ρ g t)
    {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] ↥T.L.T)
    (M : G → Matrix (Fin d) (Fin d) (PadicComplex l))
    (hb : ∀ g i j, M g i j = zC (b.repr (ac g (b j)) i)) (c : ℕ)
    (H : ∀ y : Fin d → ℚ_[l], (∀ σ,
      (M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ ball l d) →
      ∀ a, ‖(l : ℚ_[l]) ^ c * y a‖ ≤ 1)
    (v : T.V) (hw : ∀ g, T.ρ g v - v ∈ T.L.T) (n : ℕ) (hn : (l : LL) ^ n • v ∈ T.L.T) :
    (l : LL) ^ c • v ∈ T.L.T := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlL : (l : LL) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set t : ↥T.L.T := ⟨_, hn⟩ with ht
  have hy := H (fun a => ((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])) (by
    intro σ a
    have e1 : ac σ t - t = (l : ℤ_[l]) ^ n • (⟨_, hw σ⟩ : ↥T.L.T) := by
      apply Subtype.ext
      rw [hsm, Submodule.coe_sub, hac]
      change T.ρ σ ((l : LL) ^ n • v) - (l : LL) ^ n • v = _
      rw [map_smul, smul_sub]
    have e2 : b.repr (ac σ t) a =
        ∑ j, b.repr (ac σ (b j)) a * b.repr t j := by
      conv_lhs => rw [← b.sum_repr t]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
        smul_eq_mul, mul_comm]
    have e3 := congrArg (fun z => ((b.repr z a : ℤ_[l]) : ℚ_[l])) e1
    simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, e2] at e3
    push_cast at e3
    have e4 : ((M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l)
          (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l]))) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])))) a =
        algebraMap ℚ_[l] (PadicComplex l) ((b.repr (⟨_, hw σ⟩ : ↥T.L.T) a : ℤ_[l]) : ℚ_[l]) := by
      have hb' : ∀ i j, M σ i j = zC (b.repr (ac σ (b j)) i) := hb σ
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, hb', zC, ← map_mul, ← map_sum, ← map_sub]
      congr 1
      have hp : (l : ℚ_[l]) ^ n ≠ 0 := pow_ne_zero _ hl
      rw [← inv_mul_cancel_left₀ hp (((b.repr (⟨_, hw σ⟩ : ↥T.L.T) a : ℤ_[l]) : ℚ_[l])), ← e3,
        mul_sub, PadicInt.coe_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [PadicInt.coe_mul]; ring
    rw [e4, norm_algebraMap']
    exact PadicInt.norm_le_one _)
  let z : Fin d → ℤ_[l] := fun a => ⟨_, hy a⟩
  let t' : ↥T.L.T := ∑ a, z a • b a
  have e5 : (l : ℤ_[l]) ^ c • t = (l : ℤ_[l]) ^ n • t' := by
    apply b.repr.injective
    ext a
    have : b.repr t' a = z a := congrFun (b.repr_sum_self z) a
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, this]
    have hz : ((z a : ℤ_[l]) : ℚ_[l]) = (l : ℚ_[l]) ^ c * (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])) := rfl
    rw [PadicInt.coe_mul, PadicInt.coe_mul, hz]
    push_cast
    field_simp
  have e6 := congrArg Subtype.val e5
  rw [hsm, hsm] at e6
  change (l : LL) ^ c • (l : LL) ^ n • v = _ at e6
  rw [smul_comm] at e6
  have e7 := smul_right_injective _ (pow_ne_zero n hlL) e6
  rw [e7]
  exact t'.2

theorem pow_smul_compHom {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) (φ : ℤ_[l] →+* O) :
    letI : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T φ
    ∀ (k : ℕ) (t : ↥T.L.T),
      ((((l : ℤ_[l]) ^ k) • t : ↥T.L.T) : T.V) = (l : LL) ^ k • (t : T.V) := by
  intro k t
  change (φ ((l : ℤ_[l]) ^ k)) • (t : T.V) = _
  rw [← algebraMap_smul LL, map_pow, map_natCast, map_pow, map_natCast]

theorem killed_of_coord (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T M A) (c : ℕ)
    (H : ∀ y : Fin d → ℚ_[l], (∀ σ ∈ GK K,
      (M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ ball l d) →
      ∀ a, ‖(l : ℚ_[l]) ^ c * y a‖ ≤ 1)
    (v : T.V) (hw : ∀ g : ↥(GK K), T.ρ g v - v ∈ T.L.T) : (l : ↥LL.1) ^ c • v ∈ T.L.T := by
  obtain ⟨b, hb, -⟩ := hM
  obtain ⟨n, hn⟩ := exists_pow_smul_mem K LL T v
  refine @killed_of_coordinates l _ _ _ _ _ _ _ _ _ _ _ _ _ _ T (zlMod LL T) ?_
    (fun g => actTZ LL T g) (fun _ _ => rfl) d b (fun g => M g) hb c
    (fun y hy => H y fun σ hσ => hy ⟨σ, hσ⟩) v hw n hn
  exact pow_smul_compHom T (algebraMap ℤ_[l] ↥(OL LL))

theorem killed_quot {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O)
    (p c : ℕ) (H : ∀ v : T.V, (∀ g, T.ρ g v - v ∈ T.L.T) → (p : LL) ^ c • v ∈ T.L.T)
    (x : T.V ⧸ T.L.T) (hx : ∀ g, actD T.L g x = x) : ((p : O) ^ c) • x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL, map_pow,
    map_natCast]
  exact H v fun g => (Submodule.Quotient.eq _).1 (hx g)

def imBall {r d : ℕ} (P : Matrix (Fin r) (Fin d) (PadicComplex l)) :
    AddSubgroup (Fin r → PadicComplex l) where
  carrier := P.mulVec '' ball l d
  zero_mem' := ⟨0, fun a => by simp, Matrix.mulVec_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, fun a => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx a) (hy a)),
      Matrix.mulVec_add _ _ _⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, fun a => by simpa using hx a, Matrix.mulVec_neg _ _⟩

theorem Ks_mono' (K : FinExt l) {i j : ℕ} (h : i ≤ j) : Ks K i ≤ Ks K j := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  intro x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [pow_add, pow_mul, hx, one_pow]

theorem act_algebraMap' {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (x : ℚ_[l]) :
    act g (algebraMap ℚ_[l] (PadicComplex l) x) = algebraMap ℚ_[l] (PadicComplex l) x := by
  have := ha.1 g (algebraMap ℚ_[l] (Om l) x)
  rw [AlgEquiv.commutes] at this
  exact this

theorem invariants_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; H0at S E := by
  intro D HW F h7 l _ K s LL h S E M0 h0 T τ hW hj x hx
  have hell : ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  obtain ⟨d, M, A, hM⟩ := (GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral l K LL T).1
  obtain ⟨r, P, U, g, J, hJ, hfin, hFr, hHT, hPM, hb1, hb2, hint⟩ :=
    GlobalTheory.T.exists_tau_component_frame_of_lattice D HW F h7 l K s LL h T M0 h0 τ hW d M A hM
  have hact : IsActC (D.locA l).actC := ⟨(D.locA l).actC_ext, (D.locA l).actC_norm⟩
  have hχ : IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  set m := mN l s (M0 + h0) with hm
  have hsm : s + 1 ≤ m := by rw [hm, mN]; omega
  have hs1 := h.1
  have hLev : Lev l m := ⟨by omega, fun _ => by omega⟩
  have hG : Gj K m ≤ GK K :=
    IntermediateField.fixingSubgroup_le (h.2.2.1.trans (Ks_mono' K (by omega)))
  have h0J : (0 : ℤ) ∉ J := fun hh => hj (hJ 0 hh)
  have hc0 : c0 S T τ M0 h0 = 2 + ∑ u ∈ hfin.toFinset, (m + padicValInt l u) := by
    rw [c0, hell, hs]
    congr 1
    exact finsum_mem_eq_finite_toFinset_sum (fun u => m + vZ l u) hfin
  rw [hell]
  refine killed_quot T l _ (killed_of_coord K LL T M A hM _ ?_) x hx
  intro y hy
  have hl1 : ‖(l : ℚ_[l])‖ ≤ 1 := (Padic.norm_p_lt_one).le
  rcases J.eq_empty_or_nonempty with rfl | ⟨u0, hu0⟩
  · obtain ⟨e, u, -, hu, -⟩ := hHT
    have : IsEmpty (Fin r) := ⟨fun k => by simpa using hu k⟩
    intro a
    have := hint y ⟨0, fun a => by simp, Subsingleton.elim _ _⟩ a
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1) (norm_nonneg _) this
  · have key := GlobalTheory.T.prime_pow_smul_mem_of_twistedInvariant_mod_lattice l _ _ hact hχ K m r hLev U g hFr J hHT 0 h0J (imBall P) hb1
      (by rintro _ ⟨z, hz, rfl⟩; exact hb2 z hz)
      (P.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a))) (by
        intro σ hσ
        refine ⟨_, hy σ (hG hσ), ?_⟩
        have e1 : (fun a => (D.locA l).actC σ
            (P.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) a)) =
            (P.map ((D.locA l).actC σ)).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) := by
          funext a
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
            act_algebraMap' hact]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPM σ hσ, twAct, e1, Matrix.mulVec_mulVec]
        simp [chiC])
    rw [Finset.erase_eq_of_notMem h0J] at key
    simp only [sub_zero] at key
    have hle1 : 1 ≤ ∑ u ∈ J, (m + padicValInt l u) :=
      le_trans (by omega) (Finset.single_le_sum (f := fun u => m + padicValInt l u)
        (fun _ _ => Nat.zero_le _) hu0)
    have hle2 : ∑ u ∈ J, (m + padicValInt l u) ≤ ∑ u ∈ hfin.toFinset, (m + padicValInt l u) :=
      Finset.sum_le_sum_of_subset fun u hu => hfin.mem_toFinset.2 (hJ u hu)
    rw [max_eq_right hle1] at key
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle2
    have hi := hint (fun a => (l : ℚ_[l]) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) * y a) (by
      have e : (fun a => algebraMap ℚ_[l] (PadicComplex l)
          ((l : ℚ_[l]) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) * y a)) =
          (l : PadicComplex l) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) •
            (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) := by
        funext a
        simp only [map_mul, map_pow, map_natCast, Pi.smul_apply, smul_eq_mul]
      rw [e, Matrix.mulVec_smul]
      exact key)
    intro a
    rw [hc0, hk, ← add_assoc, add_comm _ k, pow_add, mul_assoc, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1) (norm_nonneg _) (hi a)

end GlobalTheory.Cyc.InvKilled
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsVanishAtPrimeOfAdmissibleStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariants_vanish_at_prime_of_admissible : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; H0at S E := by
  first | exact @GlobalTheory.Cyc.InvKilled.invariants_killed | exact GlobalTheory.Cyc.InvKilled.invariants_killed | (intros; apply GlobalTheory.Cyc.InvKilled.invariants_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZero
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.HubX.InvariantsNoJump

theorem mem_Jset_of_isJumpV (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (a : ℤ)
    (ha : IsJumpV S.PD Y.ρ τ a) : a ∈ LocalSituation.Jset S Y := by
  intro heq
  apply ha
  unfold FildR DdRE
  rw [inf_right_comm, heq, inf_right_comm]

theorem two_add_sum_jumps_le_intervalExponent (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (l m vd : ℕ)
    (hfin : (LocalSituation.Jset S Y).Finite) (h0 : ¬ IsJumpV S.PD Y.ρ τ 0) :
    2 + ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD Y.ρ τ u), (m + LocalSituation.vZ l u) ≤ LocalSituation.cLL l m vd (LocalSituation.Jset S Y) 0 1 := by
  classical
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by decide
  unfold LocalSituation.cLL LocalSituation.rI
  rw [hI, Finset.sum_singleton]
  simp only [sub_zero]
  have hle : ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD Y.ρ τ u), (m + LocalSituation.vZ l u) ≤
      ∑ᶠ (u : ℤ) (_ : u ∈ LocalSituation.Jset S Y) (_ : u ≠ 0), (m + LocalSituation.vZ l u) := by
    simp only [finsum_eq_if]
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_,
      finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
    rotate_left
    all_goals try
      intro u hu
      rw [Set.Finite.coe_toFinset]
      by_contra hn
      have hn' : ¬ IsJumpV S.PD Y.ρ τ u := fun hj => hn (mem_Jset_of_isJumpV S Y τ u hj)
      apply hu
      simp [hn, hn']
    apply Finset.sum_le_sum
    · intro u _
      by_cases hj : IsJumpV S.PD Y.ρ τ u
      · have hu0 : u ≠ 0 := by rintro rfl; exact h0 hj
        simp only [if_pos hj, if_pos (mem_Jset_of_isJumpV S Y τ u hj), if_pos hu0, le_refl]
      · simp only [if_neg hj]
        exact Nat.zero_le _
  omega

end GlobalTheory.HubX.InvariantsNoJump

namespace GlobalTheory.HubX.InvariantsNoJump

theorem torsion_exponent_kills_invariants_no_jump_zero : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := LocalSituation.sit D.loc HW l (D.locA l) K s LL h; ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O), LocalSituation.HypW S ((F l).E K s LL h).tie T M0 h0 → (∀ τ, ¬ IsJumpV S.PD T.ρ τ 0) → ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T) • x = 0 := by
  intro _ _ _ D HW F _ l _ K s LL h S M0 h0 T hW hJ x hx
  have hat := GlobalTheory.T.invariants_vanish_at_prime_of_admissible D HW F (GlobalTheory.Per.FontaineAll.fontaine_bounds D) l K s LL h
  have hp : LocalSituation.ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  have hcard := Formalism.MainNotions.N.JsetEmb.card_emb_good h
  have hpos : 0 < Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    rw [hcard]; exact Module.finrank_pos
  obtain ⟨τ⟩ := (Nat.card_pos_iff.1 hpos).1
  have key := hat M0 h0 T τ hW (hJ τ) x hx
  have hfin : (LocalSituation.Jset S T).Finite :=
    (Set.finite_Icc (-(M0 : ℤ)) h0).subset fun a ha => hW.2.1 a ha
  have hle : LocalSituation.c0 S T τ M0 h0 ≤ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T := by
    unfold LocalSituation.c0
    rw [hp, hs]
    exact two_add_sum_jumps_le_intervalExponent S T τ l _ _ hfin (hJ τ)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, pow_add, mul_comm, mul_smul, key, smul_zero]

end GlobalTheory.HubX.InvariantsNoJump
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZeroStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_exponent_kills_invariants_of_good : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := LocalSituation.sit D.loc HW l (D.locA l) K s LL h; ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O), LocalSituation.HypW S ((F l).E K s LL h).tie T M0 h0 → (∀ τ, ¬ IsJumpV S.PD T.ρ τ 0) → ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T) • x = 0 := by
  first | exact @GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero | exact GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero | (intros; apply GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero <;> assumption)
end
