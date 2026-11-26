module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc

noncomputable section

namespace UpperTheory.ConvolutionTheory.Loc

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} [TopologicalSpace k] [TopologicalSpace E]
  [MeasurableSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)]

def Match (σ : E ≃ₐ[k] E) (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) (φ : GL (Fin n) E → ℂ) (f : GL (Fin n) k → ℂ) : Prop :=
  (∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
      (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
      IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ → μδ.IsHaarMeasure → μγ.IsHaarMeasure →
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
        Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
      twOrbIntegralC (sigmaGL σ) μE δ μδ φ = orbIntegralC μk γ μγ f) ∧
  ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
    IsRegSemisimple γ → (¬ ∃ δ : GL (Fin n) E, IsNormOf σ δ γ) → μγ.IsHaarMeasure → orbIntegralC μk γ μγ f = 0

end UpperTheory.ConvolutionTheory.Loc

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
open ValuativeRel UpperTheory.ConvolutionTheory.Loc

section

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private theorem bd_mul {a b : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E} (h : ∀ i j, valuation E (M i j) ≤ a)
    (h' : ∀ i j, valuation E (N i j) ≤ b) (i j : Fin n) : valuation E ((M * N) i j) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem bd_one (i j : Fin n) : valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

private theorem bd_inv {r : ValueGroupWithZero E} (hr : r < 1) {A H : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, valuation E (A i j) ≤ r)
    (hH : H = 1 - H * A) (i j : Fin n) : valuation E (H i j) ≤ 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun p : Fin n × Fin n => valuation E (H p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩
  refine (hp (i, j) (Finset.mem_univ _)).trans ?_
  by_contra hc
  push Not at hc
  have h1 := bd_mul (fun a b => hp (a, b) (Finset.mem_univ _)) hA p.1 p.2
  have h2 : valuation E ((H * A) p.1 p.2) < valuation E (H p.1 p.2) :=
    h1.trans_lt (mul_lt_of_lt_one_right (zero_lt_one.trans hc) hr)
  have h3 : valuation E ((1 - H * A) p.1 p.2) < valuation E (H p.1 p.2) :=
    Valuation.map_sub_lt _ ((bd_one _ _).trans_lt hc) h2
  rw [← hH] at h3
  exact lt_irrefl _ h3

end

theorem UpperTheory.ConvolutionTheory.Loc.ballSub :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (r : ValueGroupWithZero E), 0 < r → r < 1 →
      ∃ K : Subgroup (GL (Fin n) E), (K : Set (GL (Fin n) E)) = ball n r ∧ IsOpen (K : Set (GL (Fin n) E)) ∧ IsCompact (K : Set (GL (Fin n) E)) := by
  intro E _ _ _ _ n r h0 h1
  have mb : ∀ {g : GL (Fin n) E}, g ∈ ball n r → ∀ i j, valuation E (((g : Matrix (Fin n) (Fin n) E) - 1) i j) ≤ r := fun hg i j => hg i j
  have hinv : ∀ g ∈ ball (E := E) n r, g⁻¹ ∈ ball n r := by
    intro g hg i j
    have e : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 - (g⁻¹ : GL (Fin n) E) * ((g : Matrix (Fin n) (Fin n) E) - 1) := by
      rw [mul_sub, Units.inv_mul]; simp
    have h := bd_mul (bd_inv h1 (mb hg) e) (mb hg) i j
    rw [one_mul] at h
    rw [e, Matrix.sub_apply, sub_sub_cancel_left, Valuation.map_neg]
    exact h
  let K : Subgroup (GL (Fin n) E) :=
    { carrier := ball n r
      one_mem' := fun i j => by simp
      inv_mem' := fun {g} hg => hinv g hg
      mul_mem' := fun {a b} ha hb i j => by
        have e : ((a * b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
            ((a : Matrix (Fin n) (Fin n) E) - 1) * ((b : Matrix (Fin n) (Fin n) E) - 1) + ((a : Matrix (Fin n) (Fin n) E) - 1) +
              ((b : Matrix (Fin n) (Fin n) E) - 1) := by
          rw [Units.val_mul]; noncomm_ring
        rw [← Matrix.sub_apply, e]
        refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (ha i j)) (hb i j)
        exact (bd_mul (mb ha) (mb hb) i j).trans
          (mul_le_of_le_one_right' h1.le) }
  have hent : ∀ i j, Continuous fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j :=
    fun i j => (Units.continuous_val.matrix_elem i j).sub continuous_const
  refine ⟨K, rfl, K.isOpen_of_mem_nhds (g := 1) ?_, ?_⟩
  · have hb : {x : E | valuation E x < r} ∈ nhds (0 : E) :=
      (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 r h0.ne', subset_rfl⟩
    have : ∀ᶠ g : GL (Fin n) E in nhds 1, ∀ i j,
        valuation E ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) < r := by
      refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact (hent i j).continuousAt.preimage_mem_nhds (t := {x : E | valuation E x < r}) (by simpa using hb)
    exact this.mono fun g hg i j => (hg i j).le
  · have hc : IsCompact {M : Matrix (Fin n) (Fin n) E | ∀ i j, valuation E (M i j) ≤ r} :=
      isCompact_pi_infinite (s := fun _ : Fin n => {x : Fin n → E | ∀ j, x j ∈ {y | valuation E y ≤ r}})
        fun _ => isCompact_pi_infinite fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E r
    have hc' := hc.image (f := fun M => M + 1) (by fun_prop)
    have h := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.2.2 _ _ hc' hc'
    convert h using 1
    ext g
    constructor
    · intro hg
      exact ⟨⟨_, mb hg, sub_add_cancel _ _⟩, ⟨_, mb (hinv g hg), sub_add_cancel _ _⟩⟩
    · rintro ⟨⟨M, hM, e⟩, -⟩ i j
      rw [← e]
      simpa using hM i j
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.StrictNormal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.strictNormal :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ t t' : Fin n → Eˣ, Strict t → Strict t' → ∀ x : GL (Fin n) E,
      x⁻¹ * diagT E (Fin n) t * sg σ x = diagT E (Fin n) t' → ∃ s : Fin n → Eˣ, x = diagT E (Fin n) s := by
  intro E _ _ _ _ n σ q hσ t t' ht ht' x hx
  have hd : ∀ s : Fin n → Eˣ, (diagT E (Fin n) s : Matrix (Fin n) (Fin n) E) = diagonal (fun a => (s a : E)) :=
    fun _ => val_diagT ..
  have h1 : diagT E (Fin n) t * sg σ x = x * diagT E (Fin n) t' := by
    rw [← hx]; group

  have key : ∀ i j, (x : Matrix (Fin n) (Fin n) E) i j ≠ 0 →
      valuation E (t i : E) = valuation E (t' j : E) := by
    intro i j hij
    have h2 := congrArg (fun g : GL (Fin n) E => valuation E ((g : Matrix (Fin n) (Fin n) E) i j)) h1
    simp only [Units.val_mul, hd, diagonal_mul, mul_diagonal, map_mul] at h2
    have h3 : (sg σ x : Matrix (Fin n) (Fin n) E) i j = σ ((x : Matrix (Fin n) (Fin n) E) i j) := rfl
    rw [h3, hσ.isom, mul_comm] at h2
    exact mul_left_cancel₀ ((Valuation.ne_zero_iff _).2 hij) h2
  have hm : StrictMono fun i => valuation E (t i : E) := fun i j h => ht i j h
  have hm' : StrictMono fun i => valuation E (t' i : E) := fun i j h => ht' i j h
  have hdet : (x : Matrix (Fin n) (Fin n) E).det ≠ 0 := GeneralLinearGroup.det_ne_zero x
  obtain ⟨w, hw⟩ : ∃ w : Equiv.Perm (Fin n), ∀ j, (x : Matrix (Fin n) (Fin n) E) (w j) j ≠ 0 := by
    by_contra hcon
    apply hdet
    rw [det_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    have : ∃ j, (x : Matrix (Fin n) (Fin n) E) (w j) j = 0 := by
      by_contra h
      exact hcon ⟨w, fun j hj => h ⟨j, hj⟩⟩
    obtain ⟨j, hj⟩ := this
    rw [Finset.prod_eq_zero (f := fun i => (x : Matrix (Fin n) (Fin n) E) (w i) i) (Finset.mem_univ j) hj, smul_zero]
  have hwm : StrictMono w := by
    intro a b hab
    apply hm.lt_iff_lt.1
    simp only [key _ _ (hw a), key _ _ (hw b)]
    exact hm' hab
  have hwid : ∀ j, w j = j := by
    intro j
    have := Subsingleton.elim (hwm.orderIsoOfSurjective w w.surjective) (OrderIso.refl _)
    exact congrArg (fun e : Fin n ≃o Fin n => e j) this
  have hdiag : ∀ j, (x : Matrix (Fin n) (Fin n) E) j j ≠ 0 := fun j => by
    have := hw j
    rwa [hwid] at this
  refine ⟨fun j => Units.mk0 _ (hdiag j), Units.ext ?_⟩
  rw [hd]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij]
    by_contra hne
    exact hij (hm.injective ((key i j hne).trans (key j j (hdiag j)).symm))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootEx
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.RootExistence

section Bound

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private def Bd (c : ValueGroupWithZero E) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, valuation E (M i j) ≤ c

variable {a b c : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E}

private theorem Bd.mono (h : Bd a M) (hab : a ≤ b) : Bd b M := fun i j => (h i j).trans hab

private theorem Bd.zero : Bd a (0 : Matrix (Fin n) (Fin n) E) := fun i j => by simp

private theorem Bd.add (h : Bd a M) (h' : Bd a N) : Bd a (M + N) := fun i j =>
  Valuation.map_add_le _ (h i j) (h' i j)

private theorem Bd.sub (h : Bd a M) (h' : Bd a N) : Bd a (M - N) := fun i j =>
  Valuation.map_sub_le _ (h i j) (h' i j)

private theorem Bd.mul (h : Bd a M) (h' : Bd b N) : Bd (a * b) (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem Bd.smul (h : Bd a M) (x : E) : Bd (valuation E x * a) (x • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_mul' le_rfl (h i j)

private theorem Bd.nsmul (h : Bd a M) (m : ℕ) : Bd a (m • M) := by
  induction m with
  | zero => simpa using Bd.zero
  | succ m ih => rw [succ_nsmul]; exact ih.add h

private theorem Bd.one : Bd 1 (1 : Matrix (Fin n) (Fin n) E) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs <;> simp

private theorem Bd.of_sub_one (h : Bd a (M - 1)) (ha : a ≤ 1) : Bd 1 M := by
  simpa using (h.mono ha).add Bd.one

private theorem Bd.pow_sub_one (h : Bd a (M - 1)) (ha : a ≤ 1) (m : ℕ) : Bd a (M ^ m - 1) := by
  induction m with
  | zero => simpa using Bd.zero
  | succ m ih =>
    have e : M ^ (m + 1) - 1 = (M ^ m - 1) * M + (M - 1) := by
      rw [pow_succ]; noncomm_ring
    rw [e]
    exact Bd.add (by simpa using ih.mul (h.of_sub_one ha)) h

private theorem Bd.pow_sub_pow (hM : Bd a (M - 1)) (hN : Bd a (N - 1)) (ha : a ≤ 1) (hd : Bd b (M - N)) (m : ℕ) :
    Bd (a * b) (M ^ m - N ^ m - m • (M - N)) := by
  induction m with
  | zero => simpa using Bd.zero
  | succ m ih =>
    have e : M ^ (m + 1) - N ^ (m + 1) - (m + 1) • (M - N) =
        M * (M ^ m - N ^ m - m • (M - N)) + (M - 1) * (m • (M - N)) + (M - N) * (N ^ m - 1) := by
      rw [pow_succ', pow_succ', succ_nsmul]
      generalize m • (M - N) = D
      noncomm_ring
    rw [e]
    refine Bd.add (Bd.add ?_ (hM.mul (hd.nsmul m))) ?_
    · simpa using (hM.of_sub_one ha).mul ih
    · rw [mul_comm a b]
      exact hd.mul (hN.pow_sub_one ha m)

private theorem val_nat_le_one (q : ℕ) : valuation E (q : E) ≤ 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by simp)

end Bound

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem eq_zero_of_bd {ρ c : ValueGroupWithZero E} (hρ : ρ < 1) {M : Matrix (Fin n) (Fin n) E}
    (h : ∀ k : ℕ, Bd (ρ ^ k * c) M) : M = 0 := by
  ext i j
  by_contra hne
  have hv : valuation E (M i j) ≠ 0 := by simpa using hne
  have hc : c ≠ 0 := by
    rintro rfl
    exact hv (by simpa using h 0 i j)
  haveI : MulArchimedean (ValueGroupWithZero E) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hρ (Units.mk0 (valuation E (M i j) / c) (div_ne_zero hv hc))
  rw [Units.val_mk0, lt_div_iff₀ (zero_lt_iff.mpr hc)] at hk
  exact absurd (h k i j) (not_le.mpr hk)

private theorem isCompact_bd (c : ValueGroupWithZero E) : IsCompact {M : Matrix (Fin n) (Fin n) E | Bd c M} := by
  have h := isCompact_pi_infinite (s := fun _ : Fin n => {x : Fin n → E | ∀ j, x j ∈ {y | valuation E y ≤ c}})
    fun _ => isCompact_pi_infinite fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E c
  exact h

private theorem exists_root (q : ℕ) (r : ValueGroupWithZero E) (hr : r < valuation E (q : E))
    (g : Matrix (Fin n) (Fin n) E) (hg : Bd (r * valuation E (q : E)) (g - 1)) :
    ∃ u : Matrix (Fin n) (Fin n) E, Bd r (u - 1) ∧ u ^ q = g := by
  have hq0 : 0 < valuation E (q : E) := lt_of_le_of_lt zero_le hr
  have hq : (q : E) ≠ 0 := by
    intro h
    simp [h] at hq0
  have hr1 : r ≤ 1 := hr.le.trans (val_nat_le_one q)
  haveI : T2Space E := by
    letI := IsTopologicalAddGroup.rightUniformSpace E
    haveI := isUniformAddGroup_of_addCommGroup (G := E)
    infer_instance
  set ρ := r / valuation E (q : E) with hρ
  have hρ1 : ρ < 1 := (div_lt_one₀ hq0).mpr hr
  let S : ℕ → Set (Matrix (Fin n) (Fin n) E) := fun k =>
    {X | Bd r X} ∩ {X | Bd (ρ ^ k * (r * valuation E (q : E))) ((X + 1) ^ q - g)}
  have hcl : ∀ k, IsClosed (S k) := fun k =>
    (isCompact_bd r).isClosed.inter
      ((isCompact_bd (ρ ^ k * (r * valuation E (q : E)))).isClosed.preimage
        (f := fun X : Matrix (Fin n) (Fin n) E => (X + 1) ^ q - g) (by fun_prop))
  have hanti : ∀ k, S (k + 1) ⊆ S k := fun k X hX =>
    ⟨hX.1, Bd.mono hX.2 (mul_le_mul' (pow_le_pow_right_of_le_one' hρ1.le k.le_succ) le_rfl)⟩
  have hne : ∀ k, (S k).Nonempty := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, Bd.zero, ?_⟩
      have := (Bd.zero (n := n)).sub hg
      simpa using this
    | succ k ih =>
      obtain ⟨X, hX, hX'⟩ := ih
      have hD : Bd (ρ ^ k * r) ((q : E)⁻¹ • ((X + 1) ^ q - g)) := by
        have h := Bd.smul hX' (q : E)⁻¹
        rwa [map_inv₀, ← mul_assoc (ρ ^ k), mul_comm (ρ ^ k * r), inv_mul_cancel_left₀ hq0.ne'] at h
      set D := (q : E)⁻¹ • ((X + 1) ^ q - g) with hDdef
      have hqD : q • D = (X + 1) ^ q - g := by
        rw [hDdef, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hq]
      have hXD : Bd r (X - D) :=
        Bd.sub hX (hD.mono (by simpa using mul_le_mul' (pow_le_one' hρ1.le k) (le_refl r)))
      refine ⟨X - D, hXD, ?_⟩
      have h := Bd.pow_sub_pow (M := X + 1) (N := X - D + 1) (a := r) (b := ρ ^ k * r)
        (by simpa using hX) (by simpa using hXD) hr1 (by simpa using hD) q
      have e1 : X + 1 - (X - D + 1) = D := by abel
      rw [e1, hqD] at h
      have h' := (Bd.zero (n := n)).sub h
      have e2 : 0 - ((X + 1) ^ q - (X - D + 1) ^ q - ((X + 1) ^ q - g)) = (X - D + 1) ^ q - g := by abel
      have e3 : r * (ρ ^ k * r) = ρ ^ (k + 1) * (r * valuation E (q : E)) := by
        have : ρ * valuation E (q : E) = r := div_mul_cancel₀ _ hq0.ne'
        calc r * (ρ ^ k * r) = ρ * valuation E (q : E) * (ρ ^ k * r) := by rw [this]
          _ = _ := by rw [pow_succ]; ac_rfl
      rw [e2, e3] at h'
      exact h'
  obtain ⟨X, hX⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne
    ((isCompact_bd r).of_isClosed_subset (hcl 0) Set.inter_subset_left) hcl
  rw [Set.mem_iInter] at hX
  exact ⟨X + 1, by simpa using (hX 0).1, sub_eq_zero.mp (eq_zero_of_bd hρ1 fun k => (hX k).2)⟩

private theorem root_unique (q : ℕ) (r : ValueGroupWithZero E) (hr : r < valuation E (q : E))
    {A C : Matrix (Fin n) (Fin n) E} (hA : Bd r (A - 1)) (hC : Bd r (C - 1)) (h : A ^ q = C ^ q) : A = C := by
  have hq0 : 0 < valuation E (q : E) := lt_of_le_of_lt zero_le hr
  have hq : (q : E) ≠ 0 := by
    intro h
    simp [h] at hq0
  have hr1 : r ≤ 1 := hr.le.trans (val_nat_le_one q)
  have hρ1 : r / valuation E (q : E) < 1 := (div_lt_one₀ hq0).mpr hr
  refine sub_eq_zero.mp (eq_zero_of_bd (c := r) hρ1 fun k => ?_)
  induction k with
  | zero => simpa using hA.sub hC
  | succ k ih =>
    have h1 := Bd.pow_sub_pow hA hC hr1 ih q
    rw [h, sub_self] at h1
    have h2 := ((Bd.zero (n := n)).sub h1).smul (q : E)⁻¹
    rw [zero_sub, zero_sub, neg_neg, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hq, map_inv₀] at h2
    refine h2.mono (le_of_eq ?_)
    rw [pow_succ, div_eq_mul_inv]
    ac_rfl

end UpperTheory.ConvolutionTheory.Loc.RootExistence

open UpperTheory.ConvolutionTheory.Loc.RootExistence in
theorem UpperTheory.ConvolutionTheory.Loc.rootEx :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (q : ℕ) (r : ValueGroupWithZero E), r < valuation E (q : E) →
      ∀ g ∈ ball n (r * valuation E (q : E)), ∃! u, u ∈ ball n r ∧ u ^ q = g := by
  intro E _ _ _ _ n q r hr g hg
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hr
  obtain ⟨u, hu, huq⟩ := exists_root q r hr (g : Matrix (Fin n) (Fin n) E) hg
  have hunit : IsUnit u := (isUnit_pow_iff hq).mp (huq ▸ g.isUnit)
  obtain ⟨w, rfl⟩ := hunit
  refine ⟨w, ⟨hu, Units.ext (by simpa using huq)⟩, fun w' hw' => Units.ext ?_⟩
  refine root_unique q r hr hw'.1 hu ?_
  rw [huq, ← hw'.2, Units.val_pow_eq_pow_val]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SgIterateEqSelf
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc

variable {E : Type} [Field E] {n : ℕ}

theorem nrm_succ (σ : E ≃+* E) (q : ℕ) (δ : GL (Fin n) E) :
    nrm σ (q + 1) δ = nrm σ q δ * (sg σ)^[q] δ := by
  simp [nrm, List.range_succ]

theorem sg_iterate_apply (σ : E ≃+* E) (q : ℕ) (x : GL (Fin n) E) (i j : Fin n) :
    (((sg σ)^[q] x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = σ^[q] ((x : Matrix (Fin n) (Fin n) E) i j) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem sg_iterate_eq_self {σ : E ≃+* E} {q : ℕ} (h : ∀ a, σ^[q] a = a) (x : GL (Fin n) E) : (sg σ)^[q] x = x := by
  apply Units.ext
  ext i j
  rw [sg_iterate_apply, h]

theorem nrm_conj_iterate (σ : E ≃+* E) (q : ℕ) (δ x : GL (Fin n) E) :
    nrm σ q (x⁻¹ * δ * sg σ x) = x⁻¹ * nrm σ q δ * (sg σ)^[q] x := by
  induction q with
  | zero => simp [nrm]
  | succ q ih =>
    rw [nrm_succ, nrm_succ, ih, iterate_map_mul, iterate_map_mul, iterate_map_inv, Function.iterate_succ_apply]
    group

theorem nrm_conj {σ : E ≃+* E} {q : ℕ} (h : ∀ a, σ^[q] a = a) (δ x : GL (Fin n) E) :
    nrm σ q (x⁻¹ * δ * sg σ x) = x⁻¹ * nrm σ q δ * x := by
  rw [nrm_conj_iterate, sg_iterate_eq_self h]

end UpperTheory.ConvolutionTheory.Loc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootConj
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

section SlopeTestRemainingChoices

variable {E : Type} [Field E] {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {n : ℕ}

private def Bd (v : Valuation E Γ) (X : Matrix (Fin n) (Fin n) E) (c : Γ) : Prop := ∀ i j, v (X i j) ≤ c

private lemma Bd.add {v : Valuation E Γ} {X Y : Matrix (Fin n) (Fin n) E} {c : Γ} (hX : Bd v X c) (hY : Bd v Y c) :
    Bd v (X + Y) c := fun i j => by
  rw [Matrix.add_apply]; exact v.map_add_le (hX i j) (hY i j)

private lemma Bd.mul {v : Valuation E Γ} {X Y : Matrix (Fin n) (Fin n) E} {c d : Γ} (hX : Bd v X c) (hY : Bd v Y d) :
    Bd v (X * Y) (c * d) := fun i j => by
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun k _ => ?_
  rw [v.map_mul]
  exact mul_le_mul' (hX i k) (hY k j)

private lemma Bd.mono {v : Valuation E Γ} {X : Matrix (Fin n) (Fin n) E} {c d : Γ} (hX : Bd v X c) (h : c ≤ d) :
    Bd v X d := fun i j => (hX i j).trans h

private lemma Bd.one (v : Valuation E Γ) : Bd v (1 : Matrix (Fin n) (Fin n) E) 1 := fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

private lemma val_nat_le (v : Valuation E Γ) (m : ℕ) : v (m : E) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.cast_succ]; exact v.map_add_le ih (by simp)

private lemma Bd.nsmul {v : Valuation E Γ} {X : Matrix (Fin n) (Fin n) E} {c : Γ} (hX : Bd v X c) (m : ℕ) :
    Bd v ((m : E) • X) c := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, v.map_mul]
  simpa using mul_le_mul' (val_nat_le v m) (hX i j)

private lemma Bd.pow_sub {v : Valuation E Γ} {B : Matrix (Fin n) (Fin n) E} {r : Γ} (hr : r ≤ 1)
    (hB : Bd v (B - 1) r) (m : ℕ) : Bd v (B ^ m - 1) r := by
  induction m with
  | zero => intro i j; simp
  | succ m ih =>
    have h1 : Bd v (B ^ m - 1 + 1) 1 := (ih.mono hr).add (Bd.one v)
    have h2 := (hB.mul h1).mono (mul_one r).le
    have e : B ^ (m + 1) - 1 = (B - 1) * (B ^ m - 1 + 1) + (B ^ m - 1) := by
      rw [pow_succ']; noncomm_ring
    rw [e]; exact h2.add ih

private lemma Bd.tele {v : Valuation E Γ} {A B g : Matrix (Fin n) (Fin n) E} {r c : Γ} (hr : r ≤ 1)
    (hA : Bd v (A - 1) r) (hB : Bd v (B - 1) r) (hh : Bd v (A * g - g * B) c) (m : ℕ) :
    Bd v (A ^ m * g - g * B ^ m - (m : E) • (A * g - g * B)) (r * c) := by
  induction m with
  | zero => intro i j; simp
  | succ m ih =>
    have hrc : r * c ≤ c := by simpa using mul_le_mul' hr (le_refl c)
    have h1 := hA.mul ((ih.mono hrc).add (hh.nsmul m))
    have h2 := (hh.mul (hB.pow_sub hr m)).mono (mul_comm c r).le
    have e : A ^ (m + 1) * g - g * B ^ (m + 1) - ((m + 1 : ℕ) : E) • (A * g - g * B) =
        (A - 1) * (A ^ m * g - g * B ^ m - (m : E) • (A * g - g * B) + (m : E) • (A * g - g * B)) +
          (A * g - g * B) * (B ^ m - 1) + (A ^ m * g - g * B ^ m - (m : E) • (A * g - g * B)) := by
      rw [Nat.cast_succ, add_smul, one_smul, pow_succ', pow_succ']
      generalize (m : E) • (A * g - g * B) = Z
      noncomm_ring
    rw [e]; exact (h1.add h2).add ih

private lemma intertwine (v : Valuation E Γ) {A B g : Matrix (Fin n) (Fin n) E} {r : Γ} {q : ℕ} (hq : r < v (q : E))
    (hA : Bd v (A - 1) r) (hB : Bd v (B - 1) r) (h : A ^ q * g = g * B ^ q) : A * g = g * B := by
  rw [← sub_eq_zero]
  ext i0 j0
  obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v ((A * g - g * B) p.1 p.2)) ⟨(i0, j0), Finset.mem_univ _⟩
  have hh : Bd v (A * g - g * B) (v ((A * g - g * B) i j)) := fun a b => hmax (a, b) (Finset.mem_univ _)
  have ht := Bd.tele (hq.le.trans (val_nat_le v q)) hA hB hh q i j
  rw [h, sub_self, zero_sub, Matrix.neg_apply, v.map_neg, Matrix.smul_apply, smul_eq_mul, v.map_mul] at ht
  have h0 : v ((A * g - g * B) i j) = 0 := by
    by_contra hne
    exact absurd ht (not_le.2 (mul_lt_mul_of_pos_right hq (zero_lt_iff.2 hne)))
  have := hh i0 j0
  rw [h0, le_zero_iff, v.zero_iff] at this
  simpa using this

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Loc.rootConj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (q : ℕ) (r : ValueGroupWithZero E), r < valuation E (q : E) →
      ∀ u ∈ ball n r, ∀ u' ∈ ball n r, ∀ g : GL (Fin n) E, g⁻¹ * u ^ q * g = u' ^ q → g⁻¹ * u * g = u' := by
  intro E _ _ _ _ n q r hq u hu u' hu' g h
  have h1 : u ^ q * g = g * u' ^ q := by rw [← h]; group
  have h2 : (u : Matrix (Fin n) (Fin n) E) * g = g * u' :=
    intertwine (valuation E) hq (fun i j => hu i j) (fun i j => hu' i j)
      (by simpa using congrArg Units.val h1)
  have h3 : u * g = g * u' := Units.ext (by simpa using h2)
  rw [mul_assoc, h3]; group
end
