module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.SeparableOfMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

private theorem iter_eq {k E : Type} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E) (j : ℕ) (x : E) :
    (σ : E ≃+* E)^[j] x = (σ ^ j) x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, pow_succ']; rfl

private theorem mem_range_incl {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} (g : GL (Fin n) E) :
    (∃ y : GL (Fin n) k, incl y = g) ↔
      ∀ i j, (g : Matrix (Fin n) (Fin n) E) i j ∈ Set.range (algebraMap k E) := by
  constructor
  · rintro ⟨y, rfl⟩ i j
    exact ⟨(y : Matrix (Fin n) (Fin n) k) i j, rfl⟩
  · intro h
    choose M hM using h
    have e : (algebraMap k E).mapMatrix (Matrix.of M) = (g : Matrix (Fin n) (Fin n) E) := by
      ext i j
      exact hM i j
    have hd : (Matrix.of M).det ≠ 0 := by
      intro h0
      have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
      rw [h0, map_zero, e] at h1
      exact (Matrix.GeneralLinearGroup.det g).ne_zero h1.symm
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩
    ext i j
    exact hM i j

section

variable (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]

private theorem closedEmb_alg : Topology.IsClosedEmbedding (algebraMap k E) := by
  let _ := GroundTheory.LocalField.nontriviallyNormedField k
  have := GroundTheory.LocalField.completeSpace_nontriviallyNormedField k
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  exact LinearMap.isClosedEmbedding_of_injective (f := Algebra.linearMap k E)
    (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)

private theorem closedEmb_incl (n : ℕ) :
    Topology.IsClosedEmbedding (incl : GL (Fin n) k → GL (Fin n) E) := by
  have h := closedEmb_alg k E
  have hM : Topology.IsEmbedding
      ((algebraMap k E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) k →* Matrix (Fin n) (Fin n) E) :=
    Topology.IsEmbedding.piMap (f := fun _ : Fin n => Pi.map fun _ : Fin n => algebraMap k E)
      fun _ => Topology.IsEmbedding.piMap fun _ => h.isEmbedding
  refine ⟨hM.units_map, ?_⟩
  have e : Set.range (incl : GL (Fin n) k → GL (Fin n) E) =
      ⋂ i, ⋂ j, (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) ⁻¹' Set.range (algebraMap k E) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact mem_range_incl g
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => h.isClosed_range.preimage ?_
  exact Units.continuous_val.matrix_elem i j

private theorem ram_one (h : IsUnramifiedLoc k E) : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation k))) = 1 := by
  obtain ⟨π, hπ, hmax⟩ := h
  have key : ∀ x : 𝒪[E], x ∈ IsLocalRing.maximalIdeal 𝒪[E] ↔ valuation E (x : E) < 1 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  have hπk : π ∈ 𝒪[k] := (GroundTheory.LocalField.algebraMap_mem_integer_iff k E π).1 hπ.le
  have hm : (⟨π, hπk⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro hu
    exact (key _).2 hπ (hu.map (algebraMap 𝒪[k] 𝒪[E]))
  rw [← GroundTheory.LocalField.isUnramified_iff, ← GroundTheory.LocalField.map_maximalIdeal_eq_iff]
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy hu
    exact hy (isUnit_of_map_unit _ _ hu)
  · have hd : algebraMap 𝒪[k] 𝒪[E] ⟨π, hπk⟩ ∣ x :=
      (Valuation.integer.integers (valuation E)).dvd_of_le (hmax _ ((key x).1 hx))
    exact Ideal.mem_of_dvd _ hd (Ideal.mem_map_of_mem _ hm)

private theorem res_move (h : IsUnramifiedLoc k E) (τ : E ≃ₐ[k] E) (hτ : τ ≠ 1) :
    ∃ x, valuation E x ≤ 1 ∧ valuation E (τ x - x) = 1 := by
  by_contra hc
  push Not at hc
  apply hτ
  apply GroundTheory.LocalField.residueAlgEquiv_injective_of_unramified k E (ram_one k E h)
  rw [map_one]
  ext z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  rw [GroundTheory.LocalField.residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one]
  exact hc x x.2

end

theorem UpperTheory.ConvolutionTheory.Loc.bridge :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), Cyc (σ : E ≃+* E) (Module.finrank k E) ∧
      (IsUnramifiedLoc k E → (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → Unram (σ : E ≃+* E) (Module.finrank k E)) ∧
      ∀ n : ℕ, (∀ g : GL (Fin n) E, sg (σ : E ≃+* E) g = sigmaGL σ g) ∧ (∀ g : GL (Fin n) E, nrm (σ : E ≃+* E) (Module.finrank k E) g = normGL σ g) ∧
        ((∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ g : GL (Fin n) E, sigmaGL σ g = g ↔ ∃ y : GL (Fin n) k, incl y = g) ∧
        Topology.IsClosedEmbedding (incl : GL (Fin n) k → GL (Fin n) E) ∧
        iwahori (m := n) E = (GlobalTheory.SmGL.iwahori E (Fin n) : Set (GL (Fin n) E)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ
  have hc : Cyc (σ : E ≃+* E) (Module.finrank k E) := by
    refine ⟨fun x => GroundTheory.LocalField.valuation_algEquiv_apply k E σ x, Module.finrank_pos, fun x => ?_⟩
    rw [iter_eq, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one']
    rfl
  refine ⟨hc, fun hu hgen => ⟨hc, fun j hj hj' => ?_⟩, fun n => ⟨fun g => rfl, fun g => ?_, fun hgen g => ?_,
    closedEmb_incl k E n, ?_⟩⟩
  · simp only [iter_eq]
    refine res_move k E hu _ (pow_ne_one_of_lt_orderOf hj.ne' ?_)
    rwa [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  · unfold nrm normGL twNorm
    congr 2
  · rw [mem_range_incl]
    constructor
    · intro h i j
      have hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) ((g : Matrix (Fin n) (Fin n) E) i j) :=
        congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E) i j) h
      have := (IsGalois.mem_bot_iff_fixed ((g : Matrix (Fin n) (Fin n) E) i j)).mpr fun τ =>
        (Subgroup.zpowers_le.mpr hσ) (hgen τ)
      rwa [IntermediateField.mem_bot] at this
    · intro h
      ext i j
      obtain ⟨y, hy⟩ := h i j
      show σ ((g : Matrix (Fin n) (Fin n) E) i j) = _
      rw [← hy, AlgEquiv.commutes]
  · ext g
    rw [SetLike.mem_coe, GlobalTheory.SmGL.mem_iwahori]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NormInj
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

private theorem inj {k E : Type} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hσ : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ} (δ δ' : GL (Fin n) E) (h : IsTwRegSemisimple σ δ)
    (e : (normGL σ δ' : Matrix (Fin n) (Fin n) E).charpoly = (normGL σ δ : Matrix (Fin n) (Fin n) E).charpoly) :
    TwConjugate (sigmaGL σ) δ δ' := by
  have hn : ∀ x : GL (Fin n) E, UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) x = normGL σ x := fun x => by
    unfold UpperTheory.ConvolutionTheory.D.nm normGL twNorm
    congr 2
    funext i
    rw [← sigmaGL_pow]
    rfl
  obtain ⟨x, hx⟩ := UpperTheory.ConvolutionTheory.D.nmInj k E σ _ (UpperTheory.ConvolutionTheory.D.galField k E σ hσ) n δ δ' (by rw [hn]; exact h) (by rw [hn, hn]; exact e)
  exact ⟨x, hx⟩

theorem UpperTheory.ConvolutionTheory.Loc.normInj :
    ∀ (k E : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E),
      (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (γ : GL (Fin n) k), IsRegSemisimple γ → ∀ δ δ' : GL (Fin n) E,
        IsNormOf σ δ γ → IsNormOf σ δ' γ → TwConjugate (sigmaGL σ) δ δ' := by
  intro k E _ _ _ _ _ _ σ hσ n γ hγ δ δ' h h'
  have key : ∀ x : GL (Fin n) E, IsNormOf σ x γ → (normGL σ x : Matrix (Fin n) (Fin n) E).charpoly =
      (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := fun x ⟨g, hg⟩ => by
    rw [hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]
    rfl
  refine inj σ hσ δ δ' ?_ ((key _ h').trans (key _ h).symm)
  unfold IsTwRegSemisimple
  rw [key _ h]
  exact Polynomial.Separable.map hγ
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ConjDesc
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.conjDesc :
    ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n : ℕ) (γ γ' : GL (Fin n) k), IsRegSemisimple γ →
      (∃ h : GL (Fin n) E, incl γ' = h * incl γ * h⁻¹) → ∃ y : GL (Fin n) k, γ' = y * γ * y⁻¹ := by
  intro k E _ _ _ n γ γ' hγ ⟨h, hh⟩
  have hc : (γ' : Matrix (Fin n) (Fin n) k).charpoly = (γ : Matrix (Fin n) (Fin n) k).charpoly := by
    apply Polynomial.map_injective (algebraMap k E) (algebraMap k E).injective
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
    have e := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E).charpoly) hh
    simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at e
    exact e
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep k k n _ hγ).1 _ hc
  refine ⟨x⁻¹, ?_⟩
  have : γ * x = x * γ' := Units.ext hx
  rw [inv_inv, mul_assoc, this, inv_mul_cancel_left]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ValuationNatCastLeOne
open ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.BallG

section Bound

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private def Bd (c : ValueGroupWithZero E) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, valuation E (M i j) ≤ c

variable {a b c : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E}

private theorem Bd.mono (h : Bd a M) (hab : a ≤ b) : Bd b M := fun i j => (h i j).trans hab

private theorem Bd.add (h : Bd a M) (h' : Bd a N) : Bd a (M + N) := fun i j =>
  Valuation.map_add_le _ (h i j) (h' i j)

private theorem Bd.neg (h : Bd a M) : Bd a (-M) := fun i j => by
  rw [Matrix.neg_apply, Valuation.map_neg]
  exact h i j

private theorem Bd.mul (h : Bd a M) (h' : Bd b N) : Bd (a * b) (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem Bd.nsmul (h : Bd a M) (m : ℕ) : Bd a (m • M) := by
  induction m with
  | zero => intro i j; simp
  | succ m ih => rw [succ_nsmul]; exact ih.add h

private theorem Bd.pow (h : Bd a M) (ha : a ≤ 1) (m : ℕ) : Bd (a * a) ((1 + M) ^ m - 1 - m • M) := by
  induction m with
  | zero => intro i j; simp
  | succ m ih =>
    have e : (1 + M) ^ (m + 1) - 1 - (m + 1) • M =
        ((1 + M) ^ m - 1 - m • M) + ((1 + M) ^ m - 1 - m • M) * M + (m • M) * M := by
      rw [pow_succ, succ_nsmul]
      generalize m • M = D
      noncomm_ring
    rw [e]
    exact (ih.add ((ih.mul h).mono (mul_le_of_le_one_right' ha))).add ((h.nsmul m).mul h)

private theorem Bd.inv (h : Bd a M) (ha : a < 1) (e : N = -M + -(M * N)) : Bd a N := by
  intro i j
  haveI : Nonempty (Fin n × Fin n) := ⟨(i, j)⟩
  obtain ⟨p, hp⟩ := Finite.exists_max fun p : Fin n × Fin n => valuation E (N p.1 p.2)
  have hN : Bd (valuation E (N p.1 p.2)) N := fun i j => hp (i, j)
  refine (hp (i, j)).trans ?_
  have h1 : Bd (max a (a * valuation E (N p.1 p.2))) (-M + -(M * N)) :=
    (h.neg.mono (le_max_left _ _)).add ((h.mul hN).neg.mono (le_max_right _ _))
  have h2 := h1 p.1 p.2
  rw [← e] at h2
  rcases le_max_iff.mp h2 with h3 | h3
  · exact h3
  · by_contra h4
    have h0 : 0 < valuation E (N p.1 p.2) := lt_of_le_of_lt zero_le (not_le.mp h4)
    exact absurd h3 (not_le.mpr (mul_lt_of_lt_one_left h0 ha))

theorem valuation_natCast_le_one (q : ℕ) : valuation E (q : E) ≤ 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by simp)

end Bound

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

theorem ball_mono {r s : ValueGroupWithZero E} (h : r ≤ s) : ball n r ⊆ ball n s := fun _ hg i j => (hg i j).trans h

def ballSub (n : ℕ) (r : ValueGroupWithZero E) (hr : r < 1) : Subgroup (GL (Fin n) E) where
  carrier := ball n r
  one_mem' := fun i j => by simp
  mul_mem' := by
    intro x y hx hy
    have hx' : Bd r ((x : Matrix (Fin n) (Fin n) E) - 1) := hx
    have hy' : Bd r ((y : Matrix (Fin n) (Fin n) E) - 1) := hy
    have e : ((x * y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
        (x - 1) + (y - 1) + ((x : Matrix (Fin n) (Fin n) E) - 1) * (y - 1) := by
      rw [Units.val_mul]; noncomm_ring
    have := (hx'.add hy').add ((hx'.mul hy').mono (mul_le_of_le_one_right' hr.le))
    rw [← e] at this
    exact this
  inv_mem' := by
    intro x hx
    have hx' : Bd r ((x : Matrix (Fin n) (Fin n) E) - 1) := hx
    refine (hx'.inv hr (N := ((x⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) ?_ :)
    rw [mul_sub, sub_mul, Units.mul_inv]
    noncomm_ring

theorem isOpen_ball {r : ValueGroupWithZero E} (hr : r ≠ 0) : IsOpen (ball n r) := by
  have hO : IsOpen {x : E | valuation E x ≤ r} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨Units.mk0 r hr, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact Valuation.map_add_le _ hx (le_of_lt (show valuation E z < r from hz))
  have e : ball n r = ⋂ i, ⋂ j, (fun g : GL (Fin n) E =>
      (g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) ⁻¹' {x : E | valuation E x ≤ r} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hO.preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem isCompact_ball {r : ValueGroupWithZero E} (hr : r < 1) : IsCompact (ball n r) := by
  have h0 : IsCompact {M : Matrix (Fin n) (Fin n) E | Bd r M} :=
    isCompact_pi_infinite (s := fun _ : Fin n => {x : Fin n → E | ∀ j, x j ∈ {y | valuation E y ≤ r}})
      fun _ => isCompact_pi_infinite fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E r
  have h1 : IsCompact {M : Matrix (Fin n) (Fin n) E | Bd r (M - 1)} :=
    (Homeomorph.subRight (1 : Matrix (Fin n) (Fin n) E)).isCompact_preimage.mpr h0
  have h2 := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.2.2 _ _ h1 h1
  convert h2 using 1
  ext g
  exact ⟨fun hg => ⟨hg, (ballSub n r hr).inv_mem hg⟩, fun hg => hg.1⟩

theorem pow_mem_ball {q : ℕ} {r : ValueGroupWithZero E} (hr : r < valuation E (q : E)) {u : GL (Fin n) E}
    (hu : u ∈ ball n r) : u ^ q ∈ ball n (r * valuation E (q : E)) := by
  have hu' : Bd r ((u : Matrix (Fin n) (Fin n) E) - 1) := hu
  have h1 := (hu'.pow (hr.le.trans (valuation_natCast_le_one q)) q).mono (mul_le_mul' le_rfl hr.le)
  have h2 : Bd (r * valuation E (q : E)) (q • ((u : Matrix (Fin n) (Fin n) E) - 1)) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, map_mul, mul_comm]
    exact mul_le_mul' (hu' i j) le_rfl
  have h3 := h1.add h2
  rw [sub_add_cancel, add_sub_cancel, ← Units.val_pow_eq_pow_val] at h3
  exact h3

theorem sg_mem_ball_iff {σ : E ≃+* E} (hσ : Isom σ) {r : ValueGroupWithZero E} {u : GL (Fin n) E} :
    sg σ u ∈ ball n r ↔ u ∈ ball n r := by
  refine forall₂_congr fun i j => ?_
  have e : ((sg σ u : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
      σ ((u : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
    rw [map_sub]
    congr 1
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [e, hσ]

theorem exists_fixed_root {σ : E ≃+* E} (hσ : Isom σ) {q : ℕ} {r : ValueGroupWithZero E} (hr : r < valuation E (q : E))
    {g : GL (Fin n) E} (hg : g ∈ ball n (r * valuation E (q : E))) (hf : sg σ g = g) :
    ∃ u ∈ ball n r, sg σ u = u ∧ u ^ q = g := by
  obtain ⟨u, ⟨hu, huq⟩, huu⟩ := rootEx E n q r hr g hg
  exact ⟨u, hu, huu _ ⟨(sg_mem_ball_iff hσ).mpr hu, by rw [← map_pow, huq, hf]⟩, huq⟩

theorem exists_radius {w : ValueGroupWithZero E} (hw : w ≠ 0) : ∃ r : ValueGroupWithZero E, 0 < r ∧ r < w := by
  obtain ⟨c, hc0, hc1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := E)
  exact ⟨c * w, mul_pos hc0 (zero_lt_iff.mpr hw), mul_lt_of_lt_one_left (zero_lt_iff.mpr hw) hc1⟩

end UpperTheory.ConvolutionTheory.Loc.BallG
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RigidNear
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

private theorem UpperTheory.ConvolutionTheory.Loc.nrm_fixed_eq_pow {E : Type} [Field E] {n : ℕ} (σ : E ≃+* E) (q : ℕ) (u : GL (Fin n) E)
    (hu : sg σ u = u) : nrm σ q u = u ^ q := by
  induction q with
  | zero => simp [nrm]
  | succ q ih => rw [nrm_succ, ih, Function.iterate_fixed hu, pow_succ]

theorem UpperTheory.ConvolutionTheory.Loc.rigidNear :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ r : ValueGroupWithZero E, r < valuation E (q : E) →
      ∀ u ∈ ball n r, ∀ u' ∈ ball n r, sg σ u = u → sg σ u' = u' → ∀ g : GL (Fin n) E, g⁻¹ * u * sg σ g = u' → sg σ g = g := by
  intro E _ _ _ _ n σ q hc r hr u hu u' hu' h h' g hg
  have h1 : g⁻¹ * u ^ q * g = u' ^ q := by
    rw [← UpperTheory.ConvolutionTheory.Loc.nrm_fixed_eq_pow σ q u h, ← UpperTheory.ConvolutionTheory.Loc.nrm_fixed_eq_pow σ q u' h', ← hg, nrm_conj hc.ord]
  have h2 := UpperTheory.ConvolutionTheory.Loc.rootConj E n q r hr u hu u' hu' g h1
  exact mul_left_cancel (hg.trans h2.symm)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.TwOrbConj
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.twOrbConj :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] (μE : Measure (GL (Fin n) E)), μE.IsHaarMeasure →
      ∀ (δ g : GL (Fin n) E) (μ : Measure (twCent (sigmaGL σ) δ)) (μ' : Measure (twCent (sigmaGL σ) (twConj (sigmaGL σ) g δ))),
        IsTwRegSemisimple σ δ → μ.IsHaarMeasure → μ'.IsHaarMeasure →
        Measure.map (fun x : twCent (sigmaGL σ) δ => g⁻¹ * (x : GL (Fin n) E) * g) μ =
          Measure.map (fun x : twCent (sigmaGL σ) (twConj (sigmaGL σ) g δ) => (x : GL (Fin n) E)) μ' →
        ∀ φ ∈ SB (GL (Fin n) E), twOrbIntegralC (sigmaGL σ) μE (twConj (sigmaGL σ) g δ) μ' φ = twOrbIntegralC (sigmaGL σ) μE δ μ φ := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ n _ _ μE hμE δ g μ μ' hδ hμ hμ' hmap φ hφ
  obtain ⟨h1, h2, h3, -, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop E n
  have hc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) :=
    ((UpperTheory.V.Z.Tf.Orb.extCont k E).2.2 n).2 σ
  have htw : Continuous fun x : GL (Fin n) E => twConj (sigmaGL σ) x δ :=
    (continuous_inv.mul continuous_const).mul hc
  have hclosed : IsClosed (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) := isClosed_eq htw continuous_const
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have hcomm : ∀ a ∈ twCent (sigmaGL σ) δ, ∀ b ∈ twCent (sigmaGL σ) δ, Commute a b := by
    intro a ha b hb
    have key : ∀ c ∈ twCent (sigmaGL σ) δ, Commute (c : Matrix (Fin n) (Fin n) E) (normGL σ δ : GL (Fin n) E) := by
      intro c hc
      have := congrArg Units.val (twCent_commute_twNorm (sigmaGL σ) hθ δ hc)
      exact this
    exact Units.ext (UpperTheory.V.Z.Tf.Orb.centComm E n _ _ _ hδ (key a ha) (key b hb))
  have hmem : ∀ x, x ∈ twCent (sigmaGL σ) δ ↔ g⁻¹ * x * g ∈ twCent (sigmaGL σ) (twConj (sigmaGL σ) g δ) := by
    intro x
    rw [mem_twCent, mem_twCent, twConj, map_mul, map_mul, map_inv]
    have e : (g⁻¹ * x * g)⁻¹ * (g⁻¹ * δ * sigmaGL σ g) * ((sigmaGL σ g)⁻¹ * sigmaGL σ x * sigmaGL σ g) =
        g⁻¹ * (x⁻¹ * δ * sigmaGL σ x) * sigmaGL σ g := by group
    rw [e, mul_left_inj, mul_right_inj]
  have hφc : Continuous φ := IsLocallyConstant.continuous hφ.1
  have main := UpperTheory.V.Z.Tf.Orb.quotConj UpperTheory.V.Z.Tf.Orb.haarComm UpperTheory.V.Z.Tf.Orb.quotIndep (GL (Fin n) E) μE hμE
    _ _ g hclosed hcomm hmem μ μ' hμ hμ' hmap (fun x => φ (twConj (sigmaGL σ) x δ)) (hφc.comp htw).measurable
    (fun h hh x => by rw [twConj_mul_left _ _ hh])
  unfold twOrbIntegralC
  rw [← main]
  congr 1
  funext x
  congr 1
  simp only [twConj, map_mul]
  group
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.QuotDesc
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open scoped ENNReal NNReal Pointwise

namespace UpperTheory.ConvolutionTheory.Loc

section Meas

variable {G T : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [Group T] [MeasurableSpace T] [MeasurableInv T] {i : T →* G}
  {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG] {μT : Measure T} [SFinite μT] [μT.IsInvInvariant]

private theorem swap_fibre (hi : Measurable i) {F a b : G → ℝ≥0∞} (hF : Measurable F) (ha : Measurable a) (hb : Measurable b)
    (hFT : ∀ t g, F (i t * g) = F g) :
    ∫⁻ g, F g * a g * ∫⁻ t, b (i t * g) ∂μT ∂μG = ∫⁻ g, F g * b g * ∫⁻ t, a (i t * g) ∂μT ∂μG := by
  have e1 : ∫⁻ g, F g * a g * ∫⁻ t, b (i t * g) ∂μT ∂μG = ∫⁻ t, ∫⁻ g, F g * a g * b (i t * g) ∂μG ∂μT := by
    rw [lintegral_lintegral_swap (by fun_prop)]
    refine lintegral_congr fun g => ?_
    rw [lintegral_const_mul _ (by fun_prop)]
  have e2 : ∀ t : T, ∫⁻ g, F g * a g * b (i t * g) ∂μG = ∫⁻ g, F g * b g * a (i t⁻¹ * g) ∂μG := by
    intro t
    rw [← lintegral_mul_left_eq_self _ (i t⁻¹)]
    refine lintegral_congr fun g => ?_
    rw [hFT, map_inv, mul_inv_cancel_left]
    ring
  rw [e1, lintegral_congr e2, lintegral_lintegral_swap (by fun_prop)]
  refine lintegral_congr fun g => ?_
  rw [lintegral_const_mul _ (by fun_prop), lintegral_inv_eq_self (fun t : T => a (i t * g))]


omit [MeasurableInv G] [MeasurableInv T] [SFinite μT] [μT.IsInvInvariant] in
private theorem norm_toNNReal (hi : Measurable i) {ρ : G → ℝ≥0∞} (hρ : Measurable ρ) (h1 : ∀ g, ∫⁻ t, ρ (i t * g) ∂μT = 1) (g : G) :
    ∫⁻ t, ((ρ (i t * g)).toNNReal : ℝ≥0∞) ∂μT = 1 := by
  rw [← h1 g]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_lt_top (f := fun t => ρ (i t * g)) (μ := μT) (by fun_prop) (by rw [h1]; exact ENNReal.one_ne_top)] with t ht
  exact ENNReal.coe_toNNReal ht.ne

variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H] {μH : Measure H} [μH.IsMulLeftInvariant] [SFinite μH]

private theorem lintegral_desc {j : H →* G} (hj : Measurable j) {ι : T →* H} (hι : Measurable ι) {K : Subgroup G}
    (hK : MeasurableSet (K : Set G)) {ρ : G → ℝ≥0∞} (hρ : Measurable ρ) (h1 : ∀ g, ∫⁻ t, ρ (j (ι t) * g) ∂μT = 1)
    {ρ' : H → ℝ≥0∞} (hρ' : Measurable ρ') (h1' : ∀ h, ∫⁻ t, ρ' (ι t * h) ∂μT = 1)
    {F : G → ℝ≥0∞} (hF : Measurable F) (hFT : ∀ t g, F (j (ι t) * g) = F g) (hs : ∀ g, F g ≠ 0 → ∃ h, ∃ κ ∈ K, g = j h * κ) :
    μH (K.comap j) * ∫⁻ g, ρ g * F g ∂μG = ∫⁻ h, ρ' h * ∫⁻ κ in (K : Set G), F (j h * κ) ∂μG ∂μH := by
  set e : G → ℝ≥0∞ := (K : Set G).indicator 1 with he
  have hem : Measurable e := measurable_one.indicator hK
  set b : G → ℝ≥0∞ := fun g => ∫⁻ h, ρ' h * e ((j h)⁻¹ * g) ∂μH with hb
  have hbm : Measurable b := Measurable.lintegral_prod_left (by fun_prop)
  have e1 : ∫⁻ h, ρ' h * ∫⁻ κ in (K : Set G), F (j h * κ) ∂μG ∂μH = ∫⁻ g, F g * b g ∂μG := by
    have : ∀ h, ρ' h * ∫⁻ κ in (K : Set G), F (j h * κ) ∂μG = ∫⁻ g, F g * (ρ' h * e ((j h)⁻¹ * g)) ∂μG := by
      intro h
      rw [← lintegral_mul_left_eq_self (μ := μG) _ (j h), ← lintegral_indicator hK, ← lintegral_const_mul _ (Measurable.indicator (by fun_prop) hK)]
      refine lintegral_congr fun g => ?_
      by_cases hg : g ∈ (K : Set G) <;> simp [he, hg, mul_comm]
    rw [lintegral_congr this, lintegral_lintegral_swap (by fun_prop)]
    refine lintegral_congr fun g => ?_
    rw [lintegral_const_mul _ (by fun_prop)]
  have e2 : ∀ h, ∀ κ ∈ K, ∫⁻ t, b (j (ι t) * (j h * κ)) ∂μT = μH (K.comap j) := by
    intro h0 κ hκ
    have : ∀ t, b (j (ι t) * (j h0 * κ)) = ∫⁻ h, ρ' (ι t * (h0 * h)) * e ((j h)⁻¹ * κ) ∂μH := by
      intro t
      simp only [hb]
      rw [← lintegral_mul_left_eq_self _ (ι t * h0)]
      refine lintegral_congr fun h => ?_
      congr 2
      · group
      · simp only [map_mul]; group
    rw [lintegral_congr this, lintegral_lintegral_swap (by fun_prop),
      ← lintegral_indicator_one (show MeasurableSet (K.comap j : Set H) from hj hK)]
    refine lintegral_congr fun h => ?_
    rw [lintegral_mul_const _ (by fun_prop), h1', one_mul]
    have : (j h)⁻¹ * κ ∈ K ↔ j h ∈ K := by rw [K.mul_mem_cancel_right hκ, K.inv_mem_iff]
    by_cases hh : j h ∈ K <;> simp [he, Set.indicator, this, hh]
  have e3 := swap_fibre (μG := μG) (μT := μT) (i := j.comp ι) (hj.comp hι) hF hρ hbm hFT
  simp only [MonoidHom.comp_apply, h1, mul_one] at e3
  rw [e1, ← e3, ← lintegral_const_mul _ (by fun_prop)]
  refine lintegral_congr fun g => ?_
  by_cases hg : F g = 0
  · simp [hg]
  · obtain ⟨h, κ, hκ, rfl⟩ := hs g hg
    rw [e2 h κ hκ]; ring

private theorem integral_desc {j : H →* G} (hj : Measurable j) {ι : T →* H} (hι : Measurable ι) {K : Subgroup G}
    (hK : MeasurableSet (K : Set G)) (hc : μH (K.comap j) ≠ ∞) {ρ : G → ℝ≥0∞} (hρ : Measurable ρ) (h1 : ∀ g, ∫⁻ t, ρ (j (ι t) * g) ∂μT = 1)
    {ρ' : H → ℝ≥0∞} (hρ' : Measurable ρ') (h1' : ∀ h, ∫⁻ t, ρ' (ι t * h) ∂μT = 1)
    {Φ : G → ℂ} (hΦ : Measurable Φ) (hΦT : ∀ t g, Φ (j (ι t) * g) = Φ g) (hs : ∀ g, Φ g ≠ 0 → ∃ h, ∃ κ ∈ K, g = j h * κ)
    (hfin : ∫⁻ g, ((ρ g).toNNReal : ℝ≥0∞) * ‖Φ g‖ₑ ∂μG ≠ ∞) :
    ((μH (K.comap j)).toReal : ℂ) * ∫ g, Φ g * ((ρ g).toReal : ℂ) ∂μG =
      ∫ h, (∫ κ in (K : Set G), Φ (j h * κ) ∂μG) * ((ρ' h).toReal : ℂ) ∂μH := by
  set r : G → ℝ≥0 := fun g => (ρ g).toNNReal
  set r' : H → ℝ≥0 := fun g => (ρ' g).toNNReal
  have hr : Measurable r := hρ.ennreal_toNNReal
  have hr' : Measurable r' := hρ'.ennreal_toNNReal
  set A := μG.withDensity fun g => r g with hA
  set B := (μH.withDensity fun h => r' h).prod (μG.restrict K) with hB
  have key : ∀ F : G → ℝ≥0∞, Measurable F → (∀ t g, F (j (ι t) * g) = F g) → (∀ g, F g ≠ 0 → Φ g ≠ 0) →
      μH (K.comap j) * ∫⁻ g, F g ∂A = ∫⁻ p, F (j p.1 * p.2) ∂B := by
    intro F hF hFT hF0
    rw [hA, hB, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hF, lintegral_prod _ (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (Measurable.lintegral_prod_right (by fun_prop))]
    exact lintegral_desc (ρ := fun g => r g) (ρ' := fun g => r' g) hj hι hK (by fun_prop)
      (norm_toNNReal (i := j.comp ι) (hj.comp hι) hρ h1) (by fun_prop) (norm_toNNReal hι hρ' h1') hF hFT
      fun g hg => hs g (hF0 g hg)
  have hπ : Measurable fun p : H × G => Φ (j p.1 * p.2) := by fun_prop
  have hint : Integrable (fun p : H × G => Φ (j p.1 * p.2)) B := by
    refine ⟨hπ.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, ← key (fun g => ‖Φ g‖ₑ) hΦ.enorm (fun t g => by rw [hΦT]) (fun g hg h => hg (by simp [h])), hA,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hΦ.enorm]
    exact ENNReal.mul_lt_top hc.lt_top hfin.lt_top
  have h0 : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  have hm : ((μH (K.comap j) • A).map Φ).restrict {0}ᶜ = (B.map fun p : H × G => Φ (j p.1 * p.2)).restrict {0}ᶜ := by
    refine Measure.ext_of_lintegral _ fun φ hφ => ?_
    rw [← lintegral_indicator h0, ← lintegral_indicator h0, lintegral_map (hφ.indicator h0) hΦ,
      lintegral_map (hφ.indicator h0) hπ, lintegral_smul_measure]
    exact key (fun g => ({0}ᶜ : Set ℂ).indicator φ (Φ g)) ((hφ.indicator h0).comp hΦ) (fun t g => by rw [hΦT])
      fun g hg h => hg (by simp [h])
  have h2 := congrArg (fun ν : Measure ℂ => ∫ z, z ∂ν) hm
  simp only [setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun z : ℂ => z) (s := {0}ᶜ) (by simp)] at h2
  rw [integral_map hΦ.aemeasurable measurable_id'.aestronglyMeasurable,
    integral_map hπ.aemeasurable measurable_id'.aestronglyMeasurable, integral_smul_measure, hB, integral_prod _ hint, hA,
    integral_withDensity_eq_integral_smul hr, integral_withDensity_eq_integral_smul hr'] at h2
  simp only [NNReal.smul_def, Complex.real_smul] at h2
  simp only [mul_comm (Φ _), mul_comm (∫ κ in (K : Set G), Φ (j _ * κ) ∂μG)]
  exact h2

end Meas

private theorem mass_ne_top {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] {i : T →* G} (hi : Continuous i)
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG] [IsFiniteMeasureOnCompacts μG] {μT : Measure T} [μT.IsHaarMeasure] [μT.IsInvInvariant]
    {ρ : G → ℝ≥0∞} (hρ : Measurable ρ) (h1 : ∀ g, ∫⁻ t, ρ (i t * g) ∂μT = 1) {Φ : G → ℂ} (hΦ : Continuous Φ)
    (hΦT : ∀ t g, Φ (i t * g) = Φ g) {D : Set G} (hD : IsCompact D) (hs : ∀ g, Φ g ≠ 0 → ∃ s, ∃ d ∈ D, g = i s * d) :
    ∫⁻ g, ρ g * ‖Φ g‖ₑ ∂μG ≠ ∞ := by
  haveI : μT.IsMulRightInvariant := by rw [← Measure.inv_eq_self μT]; infer_instance
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : T)
  have hC : IsCompact (i '' V * D) := (hV.image hi).mul hD
  have h := swap_fibre (μG := μG) (μT := μT) hi.measurable (F := fun g => ‖Φ g‖ₑ) hΦ.measurable.enorm hρ
    (measurable_one.indicator hC.measurableSet) (fun t g => by rw [hΦT])
  simp only [h1, mul_one] at h
  have h2 : ∫⁻ g, ‖Φ g‖ₑ * (i '' V * D).indicator 1 g ∂μG < ∞ := by
    refine lt_of_eq_of_lt ?_ (hΦ.continuousOn.integrableOn_compact (μ := μG) hC).2
    rw [← lintegral_indicator hC.measurableSet]
    refine lintegral_congr fun g => ?_
    by_cases hg : g ∈ i '' V * D <;> simp [hg]
  refine (ENNReal.lt_top_of_mul_ne_top_left (b := μT V) (ne_top_of_le_ne_top (h.trans_lt h2).ne ?_)
    (Measure.measure_pos_of_mem_nhds μT hV1).ne').ne
  rw [← lintegral_mul_const (f := fun g => ρ g * ‖Φ g‖ₑ) _ (hρ.mul hΦ.measurable.enorm)]
  refine lintegral_mono fun g => ?_
  by_cases hg : Φ g = 0
  · simp [hg]
  · obtain ⟨s, d, hd, rfl⟩ := hs g hg
    rw [mul_comm (ρ _)]
    refine mul_le_mul_right ?_ _
    rw [← lintegral_indicator_one hV.measurableSet, ← lintegral_mul_right_eq_self _ s]
    refine lintegral_mono fun t => ?_
    by_cases ht : t * s ∈ V
    · rw [Set.indicator_of_mem ht, ← mul_assoc, ← map_mul, Set.indicator_of_mem (Set.mul_mem_mul (Set.mem_image_of_mem _ ht) hd)]
      exact le_rfl
    · simp [ht]

end UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.quotDesc :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
        [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
        [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (j : H →* G), Topology.IsClosedEmbedding j →
      ∀ (μG : Measure G) (μH : Measure H), μG.IsHaarMeasure → μG.IsMulRightInvariant → μH.IsHaarMeasure → μH.IsMulRightInvariant →
      ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
      ∀ (S : Subgroup G) (T : Subgroup H) (μS : Measure S) (μT : Measure T), IsClosed (T : Set H) → S = T.map j →
        μT.IsHaarMeasure → μT.IsInvInvariant → Measure.map (fun s : S => (s : G)) μS = Measure.map (fun t : T => j t) μT →
      ∀ Φ : G → ℂ, Continuous Φ → (∀ s ∈ S, ∀ g, Φ (s * g) = Φ g) → (∀ g, Φ g ≠ 0 → ∃ h, ∃ κ ∈ K, g = j h * κ) →
        (∃ D : Set G, IsCompact D ∧ ∀ g, Φ g ≠ 0 → ∃ s ∈ S, ∃ d ∈ D, g = s * d) →
        quotIntegral μG S μS Φ = (((μH (K.comap j)).toReal⁻¹ : ℝ) : ℂ) * quotIntegral μH T μT fun h => ∫ κ in (K : Set G), Φ (j h * κ) ∂μG := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj μG μH _ _ _ _ K hKo hKc S T μS μT hT hS _ _ hmap Φ hΦ hΦS hs ⟨D, hD, hDs⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set H)
  have hjm : Measurable j := hj.continuous.measurable
  have hi : Topology.IsClosedEmbedding (j.comp T.subtype) := hj.comp hT.isClosedEmbedding_subtypeVal
  have hN : ∀ ρ : G → ℝ≥0∞, Measurable ρ → ∀ g, ∫⁻ s : S, ρ (s * g) ∂μS = ∫⁻ t : T, ρ (j t * g) ∂μT := by
    intro ρ hρ g
    rw [← lintegral_map (f := fun x => ρ (x * g)) (by fun_prop) measurable_subtype_coe, hmap,
      lintegral_map (f := fun x => ρ (x * g)) (by fun_prop) (by fun_prop)]
  have exG : ∃ ρ, IsQuotNormaliser S μS ρ := by
    obtain ⟨b, hb, h1⟩ := GlobalTheory.exists_bruhat_function_closedEmbedding G T (j.comp T.subtype) hi μT
    exact ⟨b, hb, fun g => (hN b hb g).trans (h1 g)⟩
  have exH : ∃ ρ, IsQuotNormaliser T μT ρ :=
    GlobalTheory.exists_bruhat_function_closedEmbedding H T T.subtype hT.isClosedEmbedding_subtypeVal μT
  rw [quotIntegral, quotIntegral, dite_eq_left exG, dite_eq_left exH]
  obtain ⟨hρ, h1⟩ := exG.choose_spec
  obtain ⟨hρ', h1'⟩ := exH.choose_spec
  have h1T : ∀ g, ∫⁻ t : T, exG.choose (j t * g) ∂μT = 1 := fun g => (hN _ hρ g).symm.trans (h1 g)
  have hΦT : ∀ (t : T) g, Φ (j t * g) = Φ g := fun t g => hΦS _ (hS ▸ Subgroup.mem_map_of_mem j t.2) g
  have hc : μH (K.comap j) ≠ ∞ := (hj.isCompact_preimage hKc).measure_lt_top.ne
  have hc0 : μH (K.comap j) ≠ 0 := ((hKo.preimage hj.continuous).measure_pos μH ⟨1, (K.comap j).one_mem⟩).ne'
  have hfin := mass_ne_top (μG := μG) (i := j.comp T.subtype) hi.continuous hρ h1T hΦ hΦT hD fun g hg => by
    obtain ⟨s, hsS, d, hd, rfl⟩ := hDs g hg
    obtain ⟨t, ht, rfl⟩ := (hS ▸ hsS : s ∈ T.map j)
    exact ⟨⟨t, ht⟩, d, hd, rfl⟩
  have := integral_desc (μG := μG) (μH := μH) (μT := μT) (ι := T.subtype) hjm measurable_subtype_coe hKo.measurableSet hc hρ h1T hρ' h1'
    hΦ.measurable hΦT hs (ne_top_of_le_ne_top hfin (lintegral_mono fun g => mul_le_mul_left ENNReal.coe_toNNReal_le_self _))
  have hc' : ((μH (K.comap j)).toReal : ℂ) ≠ 0 := by exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨hc0, hc⟩
  rw [← this, Complex.ofReal_inv, inv_mul_cancel_left₀ hc']
end
