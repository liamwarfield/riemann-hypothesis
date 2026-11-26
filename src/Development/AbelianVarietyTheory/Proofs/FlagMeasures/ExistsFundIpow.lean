module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundIpow
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.IdealFund

open GlobalTheory.HomCovolume

theorem exists_lat (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K) (ι : Type) [Fintype ι]
    (σ : ι → (K →+* ℂ)) (hσ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w)
    (a : FractionalIdeal (𝓞 K)⁰ K) (ha : a ≠ 0) :
    ∃ L : Submodule ℤ (ι → ℂ), (∀ z, z ∈ L ↔ ∃ y ∈ a, ∀ v, z v = σ v y) ∧
      HasCov volume L ((FractionalIdeal.absNorm a : ℝ) * Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) := by
  obtain ⟨L, hL, hcov⟩ := exists_idealLat K hK a ha
  let g : ι ≃ InfinitePlace K := Equiv.ofBijective (fun v => InfinitePlace.mk (σ v))
    ((Function.bijective_iff_existsUnique _).2 hσ)
  have hg : ∀ w, InfinitePlace.mk (σ (g.symm w)) = w := fun w => g.apply_symm_apply w
  have hκ : ∀ w : InfinitePlace K, ∃ κ : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ t, κ (σ (g.symm w) t) = w.embedding t := by
    intro w
    have h1 : InfinitePlace.mk (σ (g.symm w)) = InfinitePlace.mk w.embedding := by
      rw [hg, InfinitePlace.mk_embedding]
    rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
    · exact ⟨LinearIsometryEquiv.refl _ _, fun t => by rw [← h]; rfl⟩
    · exact ⟨Complex.conjLIE, fun t => by rw [← h]; rfl⟩
  choose κ hκ using hκ
  let e₀ : (ι → ℂ) ≃ₗ[ℝ] (InfinitePlace K → ℂ) :=
    { toFun := fun z w => κ w (z (g.symm w)), invFun := fun x v => (κ (g v)).symm (x (g v))
      map_add' := fun _ _ => funext fun w => by simp
      map_smul' := fun _ _ => funext fun w => by simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
      left_inv := fun _ => funext fun v => by simp
      right_inv := fun _ => funext fun w => by simp }
  have hcard : Fintype.card ι = Fintype.card (InfinitePlace K) := Fintype.card_congr g
  have hmp : MeasurePreserving e₀.toContinuousLinearEquiv volume volume := by
    refine measurePreserving_of_ball _ _ _ (fun x => ?_) ?_
    · change ‖fun w => κ w (x (g.symm w))‖ ≤ 1 ↔ _
      simp only [pi_norm_le_iff_of_nonneg zero_le_one, LinearIsometryEquiv.norm_map]
      exact ⟨fun h v => by simpa using h (g v), fun h w => h _⟩
    · simp [volume_pi_closedBall _ zero_le_one, hcard]
  refine ⟨ZLattice.comap ℝ L e₀.toContinuousLinearEquiv.toLinearMap, fun z => ?_, ?_⟩
  · change e₀ z ∈ L ↔ _
    rw [hL]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h v => ?_, fun h w => ?_⟩
    · have h1 : κ (g v) (z (g.symm (g v))) = (g v).embedding y := h (g v)
      rw [← hκ] at h1
      simpa using h1
    · change κ w (z (g.symm w)) = _
      rw [h, hκ]
  · rw [hcard]
    exact HasCov.of_measurePreserving _ hmp (fun _ => Iff.rfl) hcov

theorem exists_fund_ipow : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)), IsPlaces σ → ∀ (𝔡 : Ideal (𝓞 K)) (n : ℤ) (c : ι → ℂ), 𝔡 ≠ ⊥ → (∀ v, c v ≠ 0) → ∃ F : Set (ι → ℂ), MeasurableSet F ∧ (∀ a : ι → ℂ, ∃! t : K, t ∈ ipow 𝔡 n ∧ ((fun v => c v * σ v t) + a) ∈ F) ∧ volume F = ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ∏ v, ‖c v‖ ^ 2) := by
  intro K _ _ _ hK ι _ σ hσ 𝔡 n c h𝔡 hc
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔡
  obtain ⟨L₀, hL₀, hcov⟩ := exists_lat K hK.1 ι σ hσ.2 _ (zpow_ne_zero n h0)
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) :=
    LinearMap.pi fun v => (Algebra.lmul ℝ ℂ (c v)⁻¹).comp (LinearMap.proj v)
  have hf : ∀ z v, f z v = (c v)⁻¹ * z v := fun _ _ => rfl
  have hdet : LinearMap.det f = (∏ v, ‖c v‖ ^ 2)⁻¹ := by
    rw [LinearMap.det_pi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
  have hpos : 0 < ∏ v, ‖c v‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hc v)) _
  let L : Submodule ℤ (ι → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ ∃ t ∈ ipow 𝔡 n, z = fun v => c v * σ v t := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => funext fun v => ?_, fun h v => ?_⟩
    · rw [← h, hf, mul_inv_cancel_left₀ (hc v)]
    · rw [hf, h, inv_mul_cancel_left₀ (hc v)]
  obtain ⟨v₀, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
  refine ⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := existsUnique_add_mem_latticeDomain L a
    obtain ⟨t, ht, hzt⟩ := (hL z).1 z.2
    refine ⟨t, ⟨ht, by rw [← hzt, add_comm]; exact hz⟩, ?_⟩
    rintro t' ⟨ht', h'⟩
    have h1 := hu ⟨_, (hL _).2 ⟨t', ht', rfl⟩⟩ (by rw [add_comm] at h'; exact h')
    have h2 := congrFun ((congrArg Subtype.val h1).trans hzt) v₀
    exact (σ v₀).injective (mul_left_cancel₀ (hc v₀) h2)
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos),
      div_inv_eq_mul, map_zpow₀, FractionalIdeal.coeIdeal_absNorm] at h
    have hfin : volume (latticeDomain L) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]
    congr 1
    push_cast
    ring

end GlobalTheory.IdealFund
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocSizeBlocks
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviIso.Size

theorem detOn_of_frame {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (g : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) m ℂ) (X : Matrix m m ℂ) (W : Submodule ℂ (Fin n → ℂ)) (hC : Cᴴ * C = 1)
    (hW : ∀ y, y ∈ W ↔ ∃ u, y = C *ᵥ u) (hg : g * C = C * X) : detOn g W = ‖X.det‖ := by
  have hst : ∀ y ∈ W, Matrix.toLin' g y ∈ W := by
    intro y hy
    obtain ⟨u, rfl⟩ := (hW y).1 hy
    exact (hW _).2 ⟨X *ᵥ u, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hg, Matrix.mulVec_mulVec]⟩
  let f : (m → ℂ) →ₗ[ℂ] W := (Matrix.toLin' C).codRestrict W fun u => (hW _).2 ⟨u, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u v h => ?_, fun y => ?_⟩
    · have h1 : C *ᵥ u = C *ᵥ v := congrArg Subtype.val h
      have h2 := congrArg (fun y => Cᴴ *ᵥ y) h1
      simpa only [Matrix.mulVec_mulVec, hC, Matrix.one_mulVec] using h2
    · obtain ⟨u, hu⟩ := (hW y).1 y.2
      exact ⟨u, Subtype.ext hu.symm⟩
  let e := LinearEquiv.ofBijective f hf
  have he : (Matrix.toLin' g).restrict hst =
      (e : (m → ℂ) →ₗ[ℂ] W) ∘ₗ Matrix.toLin' X ∘ₗ (e.symm : W →ₗ[ℂ] (m → ℂ)) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨u, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    change g *ᵥ (C *ᵥ u) = C *ᵥ (X *ᵥ u)
    rw [Matrix.mulVec_mulVec, hg, Matrix.mulVec_mulVec]
  unfold detOn
  rw [dite_eq_left hst, he, LinearMap.det_conj, LinearMap.det_toLin']

theorem detOn_blocks {n a : ℕ} {j : Fin a → ℕ} (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p : Fin a → Prop) [DecidablePred p] (W : Submodule ℂ (Fin n → ℂ))
    (h1 : ∀ i, (B i)ᴴ * B i = 1) (h2 : ∀ i k, i ≠ k → (B i)ᴴ * B k = 0)
    (hW : ∀ y, y ∈ W ↔ ∃ u : ∀ i, Fin (j i) → ℂ, (∀ i, ¬ p i → u i = 0) ∧ y = ∑ i, B i *ᵥ u i)
    (g : Matrix (Fin n) (Fin n) ℂ) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ)
    (hg : ∀ i, g * B i = B i * x i) :
    detOn g W = ∏ i ∈ Finset.univ.filter p, ‖(x i).det‖ := by
  let C : Matrix (Fin n) (Σ i : {i // p i}, Fin (j i)) ℂ := Matrix.of fun r s => B s.1 r s.2
  have hCv : ∀ u, C *ᵥ u = ∑ i : {i // p i}, B i *ᵥ fun s => u ⟨i, s⟩ := by
    intro u
    funext r
    simp [C, Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [detOn_of_frame g C (Matrix.blockDiagonal' fun i : {i // p i} => x i) W ?_ ?_ ?_]
  · rw [ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal', norm_prod,
      Finset.prod_subtype (Finset.univ.filter p) (p := p) (by simp)]
  · ext ⟨i, s⟩ ⟨k, t⟩
    change ((B i)ᴴ * B k) s t = _
    by_cases h : i = k
    · subst h
      rw [h1]
      simp [Matrix.one_apply]
    · rw [h2 i k (fun e => h (Subtype.ext e)), Matrix.one_apply_ne (fun e => h (congrArg Sigma.fst e))]
      rfl
  · intro y
    rw [hW]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun s => u s.1 s.2, ?_⟩
      rw [hCv, ← Finset.sum_subtype (Finset.univ.filter p) (by simp) (fun i => B i *ᵥ u i),
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rfl
      · rw [hu i h, Matrix.mulVec_zero]
    · rintro ⟨u, rfl⟩
      refine ⟨fun i => if h : p i then fun s => u ⟨⟨i, h⟩, s⟩ else 0, fun i h => dif_neg h, ?_⟩
      rw [hCv, ← Finset.sum_subset (Finset.filter_subset p Finset.univ) ?_,
        Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]
      · refine Finset.sum_congr rfl fun i _ => ?_
        beta_reduce
        rw [dite_eq_left i.2]
      · intro i _ hi
        beta_reduce
        rw [dif_neg (by simpa using hi), Matrix.mulVec_zero]
  · ext r ⟨k, t⟩
    change (g * B k) r t = _
    rw [hg, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [C]
    · intro i _ hi
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hi]
    · simp

theorem locSize_blocks : ∀ (n a : ℕ) (j : Fin a → ℕ) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, (B i)ᴴ * B i = 1) → (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) → SpansFlag B W → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ), (∀ i, (x i).det ≠ 0) → (∀ i, g * B i = B i * x i) → ∀ i, locSize j W g i = ‖(x i).det‖ ^ (-(1 : ℝ) / j i) := by
  intro n a j B W h1 h2 hW g x hx hg i
  unfold locSize
  rw [detOn_blocks B _ _ h1 h2 (hW i.succ) g x hg, detOn_blocks B _ _ h1 h2 (hW i.castSucc) g x hg]
  have e : (Finset.univ.filter fun k : Fin a => k.castSucc < i.succ) =
      insert i (Finset.univ.filter fun k : Fin a => k.castSucc < i.castSucc) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega
  rw [e, Finset.prod_insert (by simp), mul_div_cancel_right₀]
  exact Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (hx k)

end GlobalTheory.LeviIso.Size
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZero
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.Schmid

theorem rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a = ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  have h1 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      = n - 1 - a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h2 : (univ.filter fun b => b < a ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have ha := a.2
  have h3 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      + a + 1 = n := by omega
  have h3' := congrArg (Nat.cast : ℕ → ℝ) h3
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  push_cast at h3' h2'
  unfold Formalism.REAL.rhoN Formalism.REAL.rhoC
  linarith

theorem nsq_sub_root {n : ℕ} (u : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    Formalism.REAL.nsq (u - Formalism.REAL.root a b) = Formalism.REAL.nsq u - 2 * (u a - u b) + 2 := by
  have : ∀ i, (u - Formalism.REAL.root a b) i * (u - Formalism.REAL.root a b) i =
      u i * u i - 2 * ((if i = a then u i else 0) - (if i = b then u i else 0)) +
        ((if i = a then 1 else 0) + (if i = b then 1 else 0)) := by
    intro i
    simp only [Formalism.REAL.root, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h1.symm.trans h2) hab
    all_goals simp [h1, h2, hab, hab.symm]
    all_goals ring
  simp only [Formalism.REAL.nsq, Formalism.REAL.dot, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
  norm_num

theorem vNormSq_sub_root_lt {n : ℕ} (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : StrictAnti μ)
    {a b : Fin n} (hab : a < b) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b) < Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ) := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [show Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b + (2 : ℝ) • Formalism.REAL.rhoC ε
      = (Formalism.QuantumDeterminants.lowK ε μ + (2 : ℝ) • Formalism.REAL.rhoC ε) - Formalism.REAL.root a b by abel,
    nsq_sub_root _ hab.ne]
  have h1 := hμ hab
  have h2 := rhoN_add_rhoC ε a
  have h3 := rhoN_add_rhoC ε b
  have h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

theorem thetaA_one {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (G : Arr V n 1) :
    thetaA E 1 G = ∑ a, ∑ b, E a b (at1 G a b) := by
  rw [theta_map_word_sum_apply, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun α => ?_
  have h : α = fun _ => (α 0) := fin_one_fun_eq_const_apply_zero α
  have e : at1 G (α 0).1 (α 0).2 = G α := by
    conv_rhs => rw [h]
    rfl
  simp only [Equiv.funUnique_apply]
  change _ = E (α 0).1 (α 0).2 (at1 G (α 0).1 (α 0).2)
  rw [e]
  simp [ew]

theorem mul_vminus_eq_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsHCParam lam → IsDS ε lam σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E a b (at1 G a b) = 0 := by
  intro n ε H _ _ _ σ V E lam u hl hσ hD hu hfd F hF
  have hg := hD.1
  obtain ⟨-, hθ⟩ := (arr_module_facts V n ε E 1).1 hg
  obtain ⟨-, -, hst, -, -, -, hpf⟩ := pfil_facts_hold V n ε E u hg
  have hker : Vminus ε E (LamOf ε lam) u ≤ LinearMap.ker (thetaA E 1) := by
    apply isotypic_part_le_of_forall
    intro y hy μ hμ hyh
    apply compact_span_le_of_stable
    · intro c d _ x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hθ, hx, map_zero]
    · rw [LinearMap.mem_ker]
      obtain ⟨a, b, hba, hne, rfl⟩ := hμ
      by_contra hw0
      have hμeq : LamOf ε lam + Formalism.REAL.root a b = lowK ε lam - Formalism.REAL.root b a := by
        rw [root_swap' a b, sub_eq_add_neg]; rfl
      have hwh : KHighest ε E (lowK ε lam - Formalism.REAL.root b a) (thetaA E 1 y) := by
        refine ⟨fun c => ?_, fun c d hcd hcomp => ?_⟩
        · rw [← hθ, hyh.1 c, map_smul, hμeq]
        · rw [← hθ, hyh.2 c d hcd hcomp, map_zero]
      have hmem : thetaA E 1 y ∈ pfil ε E u 1 := (theta_filtration_holds V n ε E u hg).1 1 y hy
      have := hpf hfd 1
      have hf : FiniteDimensional ℂ (kSpan ε E (thetaA E 1 y)) :=
        Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst 1) hmem)
      have hK := (GlobalTheory.Jet.KType.kType_iff n ε H σ V E hσ.2.2.1 hD).1 _ _ hw0 hwh hf
      exact absurd (hσ.2.2.2.2.2.2 _ _ hK) (not_le.mpr (vNormSq_sub_root_lt ε hl.1 hba))
  rw [← thetaA_one]
  exact hker hF

end GlobalTheory.Jet.Schmid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZeroStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_derivative_sum_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsHCParam lam → IsDS ε lam σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E a b (at1 G a b) = 0 := by
  first | exact @GlobalTheory.Jet.Schmid.mul_vminus_eq_zero | exact GlobalTheory.Jet.Schmid.mul_vminus_eq_zero | (intros; apply GlobalTheory.Jet.Schmid.mul_vminus_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryOrthogonalEmbeddingStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryOrthogonalEmbeddingStabilizer
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabRing

open Formalism.UG

theorem cT_add_rect {R : Type} [CommRing R] (σ : R →+* R) {a b : Type} (M N : Matrix a b R) :
    cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem exists_emb_block {R : Type} [CommRing R] (σ : R →+* R) {n m k : Type}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (J : Matrix n n R) (J' : Matrix m m R) (X : Matrix n k R) (U : Matrix k n R)
    (A : Matrix n m R) (A' : Matrix m n R)
    (hB : IsUnit (cT σ X * J * X)) (hXA : cT σ X * J * A = 0) (hAX : cT σ A * J * X = 0)
    (hJ : cT σ A * J * A = J') (h1 : A' * A = 1) (h2 : A' * X = 0) (h3 : U * A = 0) (h4 : U * X = 1)
    (h5 : X * U + A * A' = 1) :
    ∃ j : UJ σ J' →* UJ σ J,
      (∀ g, ((j g : GL n R) : Matrix n n R) = X * U + A * ((g : GL m R) : Matrix m m R) * A') ∧
      ∀ h : UJ σ J, ((h : GL n R) : Matrix n n R) * X = X → h ∈ j.range := by
  have hmul : ∀ g g' : Matrix m m R,
      (X * U + A * g * A') * (X * U + A * g' * A') = X * U + A * (g * g') * A' := by
    intro g g'
    calc (X * U + A * g * A') * (X * U + A * g' * A')
        = X * (U * X) * U + X * (U * A) * g' * A' + (A * g * (A' * X) * U + A * g * (A' * A) * g' * A') := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
      _ = _ := by rw [h1, h2, h3, h4]; simp [Matrix.mul_assoc]
  have hone : X * U + A * (1 : Matrix m m R) * A' = 1 := by rw [Matrix.mul_one, h5]
  have hform : ∀ g : Matrix m m R, cT σ (X * U + A * g * A') * J * (X * U + A * g * A')
      = cT σ U * (cT σ X * J * X) * U + cT σ A' * (cT σ g * J' * g) * A' := by
    intro g
    calc cT σ (X * U + A * g * A') * J * (X * U + A * g * A')
        = cT σ U * (cT σ X * J * X) * U + cT σ U * (cT σ X * J * A) * g * A'
          + (cT σ A' * cT σ g * (cT σ A * J * X) * U
            + cT σ A' * (cT σ g * (cT σ A * J * A) * g) * A') := by
          simp only [cT_add_rect, cT_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
      _ = _ := by rw [hXA, hAX, hJ]; simp
  have hJJ : cT σ U * (cT σ X * J * X) * U + cT σ A' * J' * A' = J := by
    have := hform 1
    rw [hone] at this
    simpa [cT_one] using this.symm
  let j0 : GL m R → GL n R := fun g =>
    ⟨X * U + A * (g : Matrix m m R) * A', X * U + A * ((g⁻¹ : GL m R) : Matrix m m R) * A',
      by rw [hmul, Units.mul_inv, hone], by rw [hmul, Units.inv_mul, hone]⟩
  have hmem : ∀ g : UJ σ J', j0 g ∈ UJ σ J := by
    intro g
    have hg : cT σ ((g : GL m R) : Matrix m m R) * J' * ((g : GL m R) : Matrix m m R) = J' := g.2
    change cT σ (X * U + A * ((g : GL m R) : Matrix m m R) * A') * J
      * (X * U + A * ((g : GL m R) : Matrix m m R) * A') = J
    rw [hform, hg, hJJ]
  let j : UJ σ J' →* UJ σ J :=
    { toFun := fun g => ⟨j0 g, hmem g⟩
      map_one' := by
        apply Subtype.ext; apply Units.ext
        exact hone
      map_mul' := by
        intro g g'
        apply Subtype.ext; apply Units.ext
        exact (hmul _ _).symm }
  refine ⟨j, fun g => rfl, ?_⟩
  have hXJ : cT σ X * J = cT σ X * J * X * U := by
    calc cT σ X * J = cT σ X * J * (X * U + A * A') := by rw [h5, Matrix.mul_one]
      _ = cT σ X * J * X * U + cT σ X * J * A * A' := by
        simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = _ := by rw [hXA]; simp
  have key : ∀ h : Matrix n n R, cT σ h * J * h = J → h * X = X → A * (A' * h * A) = h * A := by
    intro h hh hX
    have e1 : cT σ X * J * X * (U * h * A) = 0 := by
      calc cT σ X * J * X * (U * h * A) = (cT σ X * J * X * U) * h * A := by
            simp only [Matrix.mul_assoc]
        _ = cT σ (h * X) * J * h * A := by rw [← hXJ, hX]
        _ = cT σ X * (cT σ h * J * h) * A := by simp only [cT_mul, Matrix.mul_assoc]
        _ = 0 := by rw [hh, hXA]
    have e2 : U * h * A = 0 := by
      obtain ⟨b, hb⟩ := hB
      rw [← hb] at e1
      calc U * h * A = ((b⁻¹ : GL k R) : Matrix k k R) * (b : Matrix k k R) * (U * h * A) := by
            rw [Units.inv_mul, Matrix.one_mul]
        _ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]
    calc A * (A' * h * A) = X * (U * h * A) + A * (A' * h * A) := by rw [e2]; simp
      _ = (X * U + A * A') * h * A := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = h * A := by rw [h5, Matrix.one_mul]
  intro h hX
  have hh : cT σ ((h : GL n R) : Matrix n n R) * J * ((h : GL n R) : Matrix n n R) = J := h.2
  have hh' : cT σ (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * J
      * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) = J := (h⁻¹).2
  have hX' : (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * X = X := by
    conv_lhs => rw [← hX]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have k1 := key _ hh hX
  have k2 := key _ hh' hX'
  let g : GL m R := ⟨A' * ((h : GL n R) : Matrix n n R) * A,
    A' * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * A,
    by rw [Matrix.mul_assoc _ A, k2, Matrix.mul_assoc A', ← Matrix.mul_assoc _ _ A, Units.mul_inv,
      Matrix.one_mul, h1],
    by rw [Matrix.mul_assoc _ A, k1, Matrix.mul_assoc A', ← Matrix.mul_assoc _ _ A, Units.inv_mul,
      Matrix.one_mul, h1]⟩
  have hg : g ∈ UJ σ J' := by
    change cT σ (A' * ((h : GL n R) : Matrix n n R) * A) * J'
      * (A' * ((h : GL n R) : Matrix n n R) * A) = J'
    calc cT σ (A' * ((h : GL n R) : Matrix n n R) * A) * J' * (A' * ((h : GL n R) : Matrix n n R) * A)
        = cT σ (A * (A' * ((h : GL n R) : Matrix n n R) * A)) * J
          * (A * (A' * ((h : GL n R) : Matrix n n R) * A)) := by
          rw [cT_mul σ A, ← hJ]; simp only [Matrix.mul_assoc]
      _ = cT σ A * (cT σ ((h : GL n R) : Matrix n n R) * J * ((h : GL n R) : Matrix n n R)) * A := by
          rw [k1]; simp only [cT_mul, Matrix.mul_assoc]
      _ = J' := by rw [hh, hJ]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  change X * U + A * (A' * ((h : GL n R) : Matrix n n R) * A) * A' = ((h : GL n R) : Matrix n n R)
  rw [k1]
  calc X * U + ((h : GL n R) : Matrix n n R) * A * A'
      = ((h : GL n R) : Matrix n n R) * X * U + ((h : GL n R) : Matrix n n R) * A * A' := by rw [hX]
    _ = ((h : GL n R) : Matrix n n R) * (X * U + A * A') := by
      simp only [Matrix.mul_add, Matrix.mul_assoc]
    _ = _ := by rw [h5, Matrix.mul_one]

theorem exists_emb : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n m : ℕ) (J : Matrix (Fin n) (Fin n) R) (J' : Matrix (Fin m) (Fin m) R) (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R), IsUnit ((fun i => σ (x i)) ⬝ᵥ (J *ᵥ x)) → (fun i => σ (x i)) ᵥ* (J * A) = 0 → Formalism.UG.cT σ A *ᵥ (J *ᵥ x) = 0 → Formalism.UG.cT σ A * J * A = J' → A' * A = 1 → A' *ᵥ x = 0 → u ᵥ* A = 0 → u ⬝ᵥ x = 1 → vecMulVec x u + A * A' = 1 → ∃ j : Formalism.UG.UJ σ J' →* Formalism.UG.UJ σ J, (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = vecMulVec x u + A * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * A') ∧ ∀ h : Formalism.UG.UJ σ J, ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x = x → h ∈ j.range := by
  intro R _ σ n m J J' x u A A' hB hXA hAX hJ h1 h2 h3 h4 h5
  have hc : cT σ (replicateCol Unit x) = replicateRow Unit (fun i => σ (x i)) := by
    ext i j; simp [cT]
  rw [vecMulVec_eq Unit] at h5 ⊢
  obtain ⟨j, hj1, hj2⟩ := exists_emb_block σ J J' (replicateCol Unit x) (replicateRow Unit u) A A'
    (by
      rw [hc, Matrix.mul_assoc, ← replicateCol_mulVec, replicateRow_mul_replicateCol,
        Matrix.isUnit_iff_isUnit_det]
      simpa using hB)
    (by rw [hc, Matrix.mul_assoc, ← replicateRow_vecMul, hXA]; simp)
    (by rw [Matrix.mul_assoc, ← replicateCol_mulVec, ← replicateCol_mulVec, hAX]; simp)
    hJ h1
    (by rw [← replicateCol_mulVec, h2]; simp)
    (by rw [← replicateRow_vecMul, h3]; simp)
    (by rw [replicateRow_mul_replicateCol, h4]; ext i j; simp)
    h5
  exact ⟨j, hj1, fun h hx => hj2 h (by rw [← replicateCol_mulVec, hx])⟩

end GlobalTheory.StabRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryOrthogonalEmbeddingStabilizerStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n m : ℕ) (J : Matrix (Fin n) (Fin n) R) (J' : Matrix (Fin m) (Fin m) R) (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R), IsUnit ((fun i => σ (x i)) ⬝ᵥ (J *ᵥ x)) → (fun i => σ (x i)) ᵥ* (J * A) = 0 → Formalism.UG.cT σ A *ᵥ (J *ᵥ x) = 0 → Formalism.UG.cT σ A * J * A = J' → A' * A = 1 → A' *ᵥ x = 0 → u ᵥ* A = 0 → u ⬝ᵥ x = 1 → vecMulVec x u + A * A' = 1 → ∃ j : Formalism.UG.UJ σ J' →* Formalism.UG.UJ σ J, (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = vecMulVec x u + A * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * A') ∧ ∀ h : Formalism.UG.UJ σ J, ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x = x → h ∈ j.range := by
  first | exact @GlobalTheory.StabRing.exists_emb | exact GlobalTheory.StabRing.exists_emb | (intros; apply GlobalTheory.StabRing.exists_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizePos
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.RationalCount

abbrev op {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)

theorem norm_op_conj_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ‖op (g.map (starRingEnd ℂ))‖ ≤ ‖op g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  let u' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 fun i => starRingEnd ℂ (u i)
  have h1 : ‖u'‖ = ‖u‖ := by simp [u', EuclideanSpace.norm_eq]
  have h2 : ‖op (g.map (starRingEnd ℂ)) u‖ = ‖op g u'‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : op (g.map (starRingEnd ℂ)) u i = starRingEnd ℂ (op g u' i) := by
      simp [op, u', Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    rw [this, RCLike.norm_conj]
  rw [h2, ← h1]
  exact (op g).le_opNorm u'

theorem norm_op_conj {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ‖op (g.map (starRingEnd ℂ))‖ = ‖op g‖ := by
  refine le_antisymm (norm_op_conj_le g) ?_
  have h := norm_op_conj_le (g.map (starRingEnd ℂ))
  have e : (g.map (starRingEnd ℂ)).map (starRingEnd ℂ) = g := by ext i j; simp
  rwa [e] at h

theorem finrank_op (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = 2 * n ^ 2 := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    ← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n))
      (F' := EuclideanSpace ℂ (Fin n))).finrank_eq, Module.finrank_linearMap]
  simp [sq]

variable (I : AutInst)

theorem comap_bijective :
    Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
  have key : ∀ w : InfinitePlace I.E, w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
    intro w
    rcases GlobalTheory.Count.Test.embedding_cases I w with h | h
    · rw [← h, InfinitePlace.mk_embedding]
    · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
  refine ⟨fun w w' h => ?_, InfinitePlace.comap_surjective⟩
  rw [key w, key w']
  exact congrArg (fun v => InfinitePlace.mk (I.φ v)) h

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  have hR := I.cm.totReal
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, AutInst.f, IsTotallyReal.finrank,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

theorem opNormAt_eq (x y : I.GA) (δ : Matrix (Fin I.n) (Fin I.n) I.E) (w : InfinitePlace I.E) :
    opNormAt (bas I) (frm I y) (bas I) (frm I x) w (Matrix.toLin' δ) =
      ‖op ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
        δ.map (I.φ (w.comap (algebraMap I.F I.E))) *
        (I.P (w.comap (algebraMap I.F I.E)) * uMat (y.1 (w.comap (algebraMap I.F I.E)))))‖ := by
  have e : LinearMap.toMatrix (bas I) (bas I) (Matrix.toLin' δ) = δ := by simp [bas]
  unfold opNormAt frm
  rw [e]
  split_ifs with h
  · rw [h]
  · have h' := (GlobalTheory.Count.Test.embedding_cases I w).resolve_left h
    set v := w.comap (algebraMap I.F I.E)
    have hu : IsUnit (I.P v * uMat (x.1 v)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 ((I.P_unit v).mul (Units.isUnit _))
    have hJ : δ.map w.embedding = (δ.map (I.φ v)).map (starRingEnd ℂ) := by
      rw [h']; rfl
    have hi : ((I.P v * uMat (x.1 v)).map (starRingEnd ℂ))⁻¹ = (I.P v * uMat (x.1 v))⁻¹.map (starRingEnd ℂ) := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]
      simp [Matrix.map_one]
    rw [hJ, hi, ← Matrix.map_mul, ← Matrix.map_mul]
    exact norm_op_conj _

theorem uMat_eq (x y a : I.GA) (γ : Matrix (Fin I.n) (Fin I.n) I.E) (v : InfinitePlace I.F)
    (h : uMat (a.1 v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v) :
    uMat ((x⁻¹ * a * y).1 v) = (I.P v * uMat (x.1 v))⁻¹ * γ.map (I.φ v) * (I.P v * uMat (y.1 v)) := by
  have e : uMat ((x⁻¹ * a * y).1 v) = (uMat (x.1 v))⁻¹ * uMat (a.1 v) * uMat (y.1 v) := by
    simp [uMat]
  rw [e, h, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

theorem mulVec_mem (x y a : I.GA) (γ : GL (Fin I.n) I.E)
    (h : I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (hK : (x⁻¹ * a * y).2 ∈ I.Kset) (z : Fin I.n → I.E) (hz : z ∈ lamX I y) :
    (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I x := by
  have h1 := (GlobalTheory.Count.Test.lamX_equivariant I a y γ h z).2 hz
  rw [GlobalTheory.Count.Test.mem_lamX] at h1 ⊢
  have h2 := (hK _).1 h1
  have h3 : I.fmat (x⁻¹ * a * y).2 * I.fmat (a * y).2⁻¹ = I.fmat x.2⁻¹ := by
    have : (x⁻¹ * a * y).2 * (a * y).2⁻¹ = x.2⁻¹ := by simp [mul_assoc]
    rw [← this]; rfl
  rw [Matrix.mulVec_mulVec] at h2
  rw [← h3]
  exact h2

theorem lamX_ne_bot (hn : 1 ≤ I.n) (x : I.GA) : lamX I x ≠ ⊥ := by
  intro h0
  have h1 := (GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x).2.2.1
  rw [h0] at h1
  have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  simp at h1

theorem truncatedLeastLatticeSize_pos (hn : 1 ≤ I.n) (x : I.GA) : 0 < tau1 I x :=
  lt_min (by norm_num) (GlobalTheory.StepDualityCompare.least_pos I x
    (GlobalTheory.NearLowerCompare.lamX_isLattice I x).fg (lamX_ne_bot I hn x))

theorem separated (hn : 1 ≤ I.n) (x y a b : I.GA) (ha : a ∈ I.GFset) (hb : b ∈ I.GFset)
    (haK : (x⁻¹ * a * y).2 ∈ I.Kset) (hbK : (x⁻¹ * b * y).2 ∈ I.Kset) (hab : a ≠ b) :
    tau1 I x * tau1 I y ≤ (∏ v, ‖op (uMat ((x⁻¹ * a * y).1 v)) - op (uMat ((x⁻¹ * b * y).1 v))‖) ^
      ((1 : ℝ) / Fintype.card (InfinitePlace I.F)) := by
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  obtain ⟨γ, -, hγ1, hγ2⟩ := ha
  obtain ⟨η, -, hη1, hη2⟩ := hb
  have hne : (γ : Matrix (Fin I.n) (Fin I.n) I.E) - η ≠ 0 := by
    intro h
    have h' : (γ : Matrix (Fin I.n) (Fin I.n) I.E) = η := sub_eq_zero.1 h
    refine hab (Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_)))
    · exact (hγ1 v).trans (h' ▸ (hη1 v).symm)
    · exact hγ2.trans (h' ▸ hη2.symm)
  have hx := GlobalTheory.NearLowerCompare.lamX_isLattice I x
  have hy := GlobalTheory.NearLowerCompare.lamX_isLattice I y
  have h := sizeIneq I.E _ _ _ _ (bas I) (frm I y) (bas I) (frm I x)
    (GlobalTheory.NearLowerCompare.frm_isUnit I y) (GlobalTheory.NearLowerCompare.frm_isUnit I x)
    (Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - η)) (lamX I y) (lamX I x) hy.fg hx.fg
    (by
      rintro _ ⟨z, hz, rfl⟩
      have := sub_mem (mulVec_mem I x y a γ hγ2 haK z hz) (mulVec_mem I x y b η hη2 hbK z hz)
      simpa [Matrix.sub_mulVec] using this)
    (by
      intro h0
      apply hne
      apply Matrix.toLin'.injective
      rw [map_zero]
      refine LinearMap.ext_on (GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I y).2.2.1 fun z hz => ?_
      exact (Submodule.eq_bot_iff _).1 h0 _ ⟨z, hz, rfl⟩)
  rw [(GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I y).2.1 hn, div_inv_eq_mul] at h
  have e1 : (nPl I.E : ℝ) = Fintype.card (InfinitePlace I.F) := by
    rw [nPl, Fintype.card_of_bijective (comap_bijective I)]
  have e2 : ∏ w, opNormAt (bas I) (frm I y) (bas I) (frm I x) w
      (Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - η)) =
      ∏ v, ‖op (uMat ((x⁻¹ * a * y).1 v)) - op (uMat ((x⁻¹ * b * y).1 v))‖ := by
    refine Fintype.prod_bijective _ (comap_bijective I) _ _ fun w => ?_
    rw [opNormAt_eq, uMat_eq I x y a γ _ (hγ1 _), uMat_eq I x y b η _ (hη1 _), op, op, op, ← map_sub, ← map_sub,
      Matrix.map_sub _ (map_sub _), Matrix.mul_sub, Matrix.sub_mul]
  rw [e1, e2] at h
  refine le_trans ?_ h
  exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (truncatedLeastLatticeSize_pos I hn y).le
    ((truncatedLeastLatticeSize_pos I hn x).le.trans (min_le_right _ _))

theorem count_le (I : AutInst) (x y : I.GA) (r : InfinitePlace I.F → ℝ) (hn : 1 ≤ I.n) (_hr : ∀ v, 0 ≤ r v) :
    {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * y).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * y).1 v)) ≤ r v}.Finite ∧
    (({a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * y).2 ∈ I.Kset ∧
        ∀ v, dOp (uMat ((x⁻¹ * a * y).1 v)) ≤ r v}.ncard : ℕ) : ℝ) ≤
      (1 + 2 * Real.sqrt I.n * Real.exp ((∑ v, r v) / I.f) / (tau1 I x * tau1 I y)) ^ (2 * (I.n ^ 2 * I.f)) := by
  set A := {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * y).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * y).1 v)) ≤ r v}
  let s : I.GA → InfinitePlace I.F → (EuclideanSpace ℂ (Fin I.n) →L[ℂ] EuclideanSpace ℂ (Fin I.n)) :=
    fun a v => op (uMat ((x⁻¹ * a * y).1 v))
  have hla : 0 < tau1 I x * tau1 I y := mul_pos (truncatedLeastLatticeSize_pos I hn x) (truncatedLeastLatticeSize_pos I hn y)
  have hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → tau1 I x * tau1 I y ≤
      (∏ v, ‖s a v - s b v‖) ^ ((1 : ℝ) / Fintype.card (InfinitePlace I.F)) :=
    fun a ha b hb hab => separated I hn x y a b ha.1 hb.1 ha.2.1 hb.2.1 hab
  have hcard : (0 : ℝ) < Fintype.card (InfinitePlace I.F) := by exact_mod_cast Fintype.card_pos
  have hinj : Set.InjOn s A := by
    intro a ha b hb h
    by_contra hab
    have := hsep a ha b hb hab
    rw [h] at this
    simp only [sub_self, norm_zero, Finset.prod_const, Finset.card_univ] at this
    rw [zero_pow Fintype.card_ne_zero, Real.zero_rpow (one_div_pos.2 hcard).ne'] at this
    exact absurd this (not_le.2 hla)
  have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin I.n) →L[ℂ] EuclideanSpace ℂ (Fin I.n)) :=
    Module.Finite.trans ℂ _
  obtain ⟨hfin, hle⟩ := GlobalTheory.packing_geometric_mean_separated (InfinitePlace I.F)
    (fun _ => EuclideanSpace ℂ (Fin I.n) →L[ℂ] EuclideanSpace ℂ (Fin I.n)) (2 * I.n ^ 2)
    (by nlinarith) (fun _ => finrank_op I.n) (tau1 I x * tau1 I y) (s '' A) (fun v => Real.exp (r v)) hla
    (fun v => Real.exp_pos _) (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      exact hsep a ha b hb fun h => hab (by rw [h]))
  have hA : {t ∈ s '' A | ∀ v, ‖t v‖ ≤ Real.exp (r v)} = s '' A := by
    refine Set.sep_eq_self_iff_mem_true.2 ?_
    rintro _ ⟨a, ha, rfl⟩ v
    exact (Real.le_exp_log _).trans (Real.exp_le_exp.2 (ha.2.2 v))
  rw [hA] at hfin hle
  refine ⟨hfin.of_finite_image hinj, ?_⟩
  rw [hinj.ncard_image, ← Real.exp_sum, ← Real.exp_mul, card_places, mul_one_div, mul_assoc 2 (I.n ^ 2)] at hle
  refine hle.trans (pow_le_pow_left₀ (by positivity) ?_ _)
  have h1 : (1 : ℝ) ≤ Real.sqrt I.n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have h2 := Real.exp_pos ((∑ v, r v) / I.f)
  gcongr
  linarith

end GlobalTheory.RationalCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KfinCoefMulSplit
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KFinCoefSplit

variable {k r : ℕ}

theorem kfin_smul {R : Rep k r} (a : ℂ) {v : R.H} (hv : R.KFin v) : R.KFin (a • v) := by
  obtain ⟨S, hfd, hv, hst⟩ := hv
  exact ⟨S, hfd, S.smul_mem a hv, hst⟩

theorem kfin_sum {R : Rep k r} {ι : Type} [Fintype ι] (x : ι → R.H) (hx : ∀ c, R.KFin (x c)) :
    R.KFin (∑ c, x c) := by
  choose S hfd hS hst using hx
  refine ⟨⨆ c, S c, inferInstance, Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c (hS c),
    fun g hg y hy => ?_⟩
  have hle : (⨆ c, S c) ≤ (⨆ c, S c).comap (R.σ g : R.H →ₗ[ℂ] R.H) :=
    iSup_le fun c z hz => Submodule.mem_iSup_of_mem c (hst c g hg z hz)
  exact hle hy

theorem kfin_coef_mul_split : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (om om' : ι → ℂ) (v v' : R.H), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → R.KFin v → R.KFin v' → (∀ I, (RI I).KFin (∑ c, pr I c (tm R om v c)) ∧ (RI I).KFin (∑ c, pr I c (tm R om' v' c))) ∧ ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R om v c), (RI I).σ g (∑ c, pr I c (tm R om' v' c))⟫_ℂ := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI om om' v v' hR hRI hF hT hv hv'
  obtain ⟨-, -, -, -, hRT, -, hRK, -, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have hadj := (GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT).2.2.2.2
  have hkf := (GlobalTheory.tensor_decomposition_kfinite hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw).2.1
  have hp : ∀ I (a : ι → ℂ) (w : R.H), R.KFin w → (RI I).KFin (∑ c, pr I c (tm R a w c)) := fun I a w hw =>
    kfin_sum _ fun c => hkf I c _ (kfin_smul (a c) hw)
  exact ⟨fun I => ⟨hp I om v hv, hp I om' v' hv'⟩,
    fun g hg => hadj om om' v (hRT v (hRK v hv)) v' (hRT v' (hRK v' hv')) g hg⟩

end GlobalTheory.KFinCoefSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsOrthComplementOfUnitVectorAtRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsOrthComplementOfUnitVectorAtRealPlace
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StabUnfold

theorem ofReal_qEps_eq {n : ℕ} (ε : Fin n → Bool) (y : Fin n → ℂ) :
    ((qEps ε y : ℝ) : ℂ) = star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  unfold qEps Formalism.REAL.Jm
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (y i) * y i = ((‖y i‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.conj_mul']
  split_ifs <;> simp [← h]

theorem frame_inv_form (I : AutInst) (v : InfinitePlace I.F) :
    ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = I.J.map (I.φ v) := by
  have hd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h1 : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  rw [← I.P_spec v]
  calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹
      = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem isPerp_at_place (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (h : IsPerp D s x A xf) (v : InfinitePlace I.F) :
    qEps (I.ε v) (infVec I v x) = sgn ℝ s ∧
      star (infVec I v x) ᵥ* (Formalism.REAL.Jm (I.ε v) * infMat D v A) = 0 ∧
      (infMat D v A)ᴴ * Formalism.REAL.Jm (I.ε v) * infMat D v A = Formalism.REAL.Jm (D.ε v) := by
  obtain ⟨-, h1, h2, h3, -⟩ := h
  have hφ : ∀ a : I.E, I.φ v (star a) = star (I.φ v a) := fun a => I.cm.cmUnram.2.1 _ a
  have hF := frame_inv_form I v
  have hs : star (fun i => I.φ v (x i)) = fun i => I.φ v (star x i) := by
    funext i; simp [hφ]
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ofReal_injective
    rw [ofReal_qEps_eq, infVec, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hF, hs]
    have := congrArg (I.φ v) h1
    have e : ((sgn ℝ s : ℝ) : ℂ) = I.φ v (sgn I.E s) := by
      unfold sgn; split_ifs <;> simp
    rw [e, ← this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, mulVec, map_sum]
  · rw [infVec, infMat, star_mulVec, vecMul_vecMul]
    have e : ((I.P v)⁻¹)ᴴ * (Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * A.map (I.φ v) * D.P v))
        = (I.J * A).map (I.φ v) * D.P v := by
      rw [Matrix.map_mul, ← hF]; simp only [Matrix.mul_assoc]
    rw [e, ← vecMul_vecMul, hs]
    have e2 : (fun i => I.φ v (star x i)) ᵥ* (I.J * A).map (I.φ v) = 0 := by
      funext j
      have := congrArg (I.φ v) (congrFun h2 j)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [vecMul, dotProduct, map_sum] using this
    rw [e2, zero_vecMul]
  · rw [← D.P_spec v, ← h3, Matrix.map_mul, Matrix.map_mul, ← hF, infMat,
      Matrix.conjTranspose_map (I.φ v) hφ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.StabUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsOrthComplementOfUnitVectorAtRealPlaceStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrthComplementOfUnitVector_at_real_place : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ v, qEps (I.ε v) (infVec I v x) = sgn ℝ s ∧ star (infVec I v x) ᵥ* (Formalism.REAL.Jm (I.ε v) * infMat D v A) = 0 ∧ (infMat D v A)ᴴ * Formalism.REAL.Jm (I.ε v) * infMat D v A = Formalism.REAL.Jm (D.ε v) := by
  first | exact @GlobalTheory.StabUnfold.isPerp_at_place | exact GlobalTheory.StabUnfold.isPerp_at_place | (intros; apply GlobalTheory.StabUnfold.isPerp_at_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddingsMatchInfinitePlacesAutInstance
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddingsMatchInfinitePlacesAutInstance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.Place

theorem comap_mk_phi (I : AutInst) (v : InfinitePlace I.F) :
    (InfinitePlace.mk (I.φ v)).comap (algebraMap I.F I.E) = v := by
  have h2 : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
  rw [InfinitePlace.comap_mk, h2, InfinitePlace.mk_embedding]

theorem placeMatch : ∀ (I : AutInst) (xf : I.Gf), PlaceMatch I.φ I.P (frm I (1, xf)) := by
  intro I xf
  have hb := GlobalTheory.Count.FrameMajorant.comap_bijective I
  refine ⟨⟨fun v v' h => ?_, fun w => ⟨w.comap (algebraMap I.F I.E), hb.1 (comap_mk_phi I _)⟩⟩, fun v => ?_⟩
  · have h' : InfinitePlace.mk (I.φ v) = InfinitePlace.mk (I.φ v') := h
    rw [← comap_mk_phi I v, h', comap_mk_phi]
  · have he := GlobalTheory.PointEquivariance.embedding_eq I (InfinitePlace.mk (I.φ v))
    have hu : ∀ u, uMat ((((1, xf) : I.GA)).1 u) = 1 := fun u => rfl
    rw [comap_mk_phi] at he
    unfold frm
    rw [comap_mk_phi, hu, Matrix.mul_one]
    by_cases h : (InfinitePlace.mk (I.φ v)).embedding = I.φ v
    · exact Or.inl ⟨h, if_pos h⟩
    · exact Or.inr ⟨he.resolve_left h, if_neg h⟩

end GlobalTheory.RadCov.Place
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddingsMatchInfinitePlacesAutInstanceStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingsMatchInfinitePlaces_autInstance : ∀ (I : AutInst) (xf : I.Gf), PlaceMatch I.φ I.P (frm I (1, xf)) := by
  first | exact @GlobalTheory.RadCov.Place.placeMatch | exact GlobalTheory.RadCov.Place.placeMatch | (intros; apply GlobalTheory.RadCov.Place.placeMatch <;> assumption)
end
end
