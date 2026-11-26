module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ContinuousAeval
open MvPolynomial Filter Topology NumberField

namespace ChowFormHeightComparison₂.GenericDenseBound

theorem ratPrimeDense : GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof)
    GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.proof

theorem continuous_aeval {n : ℕ} (f : MvPolynomial (Fin n) ℚ) : Continuous fun z : Fin n → ℂ => aeval z f := by
  have : (fun z : Fin n → ℂ => aeval z f) = fun z => eval z (map (algebraMap ℚ ℂ) f) := by
    funext z
    rw [eval_map, aeval_def]
  rw [this]
  exact MvPolynomial.continuous_eval _

theorem generic_dense {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℚ)) (hP : P.IsPrime) {z₀ : Fin n → ℂ}
    (hz₀ : ∀ g ∈ P, aeval z₀ g = 0) :
    ∃ z : ℕ → Fin n → ℂ, (∀ m g, aeval (z m) g = 0 ↔ g ∈ P) ∧ Tendsto z atTop (𝓝 z₀) := by
  let V : Set (Fin n → ℂ) := {z | ∀ g ∈ P, aeval z g = 0}
  have hV : IsClosed V := by
    have : V = ⋂ g ∈ P, {z | aeval z g = 0} := by ext z; simp [V]
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (continuous_aeval g) continuous_const
  haveI : CompleteSpace V := hV.completeSpace_coe
  haveI : Countable (MvPolynomial (Fin n) ℚ) := (basisMonomials (Fin n) ℚ).repr.injective.countable
  let O : {f : MvPolynomial (Fin n) ℚ // f ∉ P} → Set V := fun f => {z | aeval z.1 f.1 ≠ 0}
  have hO : ∀ f, IsOpen (O f) := fun f =>
    isOpen_ne_fun ((continuous_aeval f.1).comp continuous_subtype_val) continuous_const
  have hD : ∀ f, Dense (O f) := fun f => by
    rw [Subtype.dense_iff]
    refine (ratPrimeDense (Fin n) P f.1 hP f.2).trans (closure_mono ?_)
    rintro z ⟨h1, h2⟩
    exact ⟨⟨z, h1⟩, h2, rfl⟩
  obtain ⟨u, hu, hl⟩ := mem_closure_iff_seq_limit.1 (dense_iInter_of_isOpen hO hD ⟨z₀, hz₀⟩)
  refine ⟨fun m => (u m).1, fun m g => ⟨fun h => ?_, fun h => (u m).2 g h⟩,
    (continuous_subtype_val.tendsto _).comp hl⟩
  by_contra hg
  exact Set.mem_iInter.1 (hu m) ⟨g, hg⟩ h

theorem exists_int_mul {n : ℕ} (g : MvPolynomial (Fin n) ℚ) :
    ∃ (N : ℕ) (g' : MvPolynomial (Fin n) ℤ), N ≠ 0 ∧ map (Int.castRingHom ℚ) g' = (N : MvPolynomial (Fin n) ℚ) * g := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, C a.num, a.den_ne_zero, ?_⟩
    rw [map_C, ← map_natCast (C : ℚ →+* MvPolynomial (Fin n) ℚ), ← map_mul]
    congr 1
    simp [Rat.den_mul_eq_num]
  | add p q hp hq =>
    obtain ⟨N, p', hN, hp⟩ := hp
    obtain ⟨M, q', hM, hq⟩ := hq
    refine ⟨N * M, M * p' + N * q', mul_ne_zero hN hM, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, hp, hq, map_natCast, map_natCast]
    push_cast
    ring
  | mul_X p i hp =>
    obtain ⟨N, p', hN, hp⟩ := hp
    refine ⟨N, p' * X i, hN, ?_⟩
    rw [map_mul, hp, map_X, mul_assoc]

theorem aeval_map_int {n : ℕ} {A : Type} [CommRing A] [Algebra ℚ A] (z : Fin n → A) (g : MvPolynomial (Fin n) ℤ) :
    aeval z (map (Int.castRingHom ℚ) g) = aeval z g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, map_X, aeval_X]

theorem hom_aeval {n : ℕ} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : Fin n → A)
    (g : MvPolynomial (Fin n) ℤ) : φ (aeval z g) = aeval (fun i => φ (z i)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, aeval_X]

theorem exists_seq_emb {B Ω : Type} [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B] [Field Ω] [CharZero Ω]
    [Algebra B Ω] [IsFractionRing B Ω] (x : B →+* ℂ) :
    ∃ ρ : ℕ → Ω →+* ℂ, ∀ b : B, Tendsto (fun m => ρ m (algebraMap B Ω b)) atTop (𝓝 (x b)) := by
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType ℤ B)
  let a : Fin n → B := fun i => π (X i)
  have hπa : ∀ g, π g = aeval a g := fun g => by
    have : π = aeval a := MvPolynomial.algHom_ext fun i => by simp [a]
    rw [this]
  let φ : MvPolynomial (Fin n) ℚ →ₐ[ℚ] Ω := aeval fun i => algebraMap B Ω (a i)
  let P : Ideal (MvPolynomial (Fin n) ℚ) := RingHom.ker φ
  have hP : P.IsPrime := RingHom.ker_isPrime φ
  have hmem : ∀ g : MvPolynomial (Fin n) ℤ, map (Int.castRingHom ℚ) g ∈ P ↔ π g = 0 := fun g => by
    rw [RingHom.mem_ker]
    show aeval _ _ = 0 ↔ _
    rw [aeval_map_int, ← hom_aeval (algebraMap B Ω) a g, ← hπa]
    exact map_eq_zero_iff _ (IsFractionRing.injective B Ω)
  have hz₀ : ∀ g ∈ P, aeval (fun i => x (a i)) g = 0 := fun g hg => by
    obtain ⟨N, g', hN, e⟩ := exists_int_mul g
    have h1 : π g' = 0 := (hmem g').1 (e ▸ P.mul_mem_left _ hg)
    have h2 : aeval (fun i => x (a i)) (map (Int.castRingHom ℚ) g') = 0 := by
      rw [aeval_map_int, ← hom_aeval x a g', ← hπa, h1, map_zero]
    rw [e, map_mul, map_natCast] at h2
    exact (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 hN)
  obtain ⟨z, hz, hl⟩ := generic_dense P hP hz₀
  have hker : ∀ m g, aeval (z m) g = 0 ↔ π g = 0 := fun m g => by
    rw [← hmem, ← hz m, aeval_map_int]
  have hex : ∀ m, ∃ r : B →+* ℂ, ∀ g, r (π g) = aeval (z m) g := fun m =>
    ⟨RingHom.liftOfSurjective (π : MvPolynomial (Fin n) ℤ →+* B) hπ
      ⟨(aeval (z m) : MvPolynomial (Fin n) ℤ →ₐ[ℤ] ℂ), fun g hg => (hker m g).2 hg⟩,
      fun g => RingHom.liftOfSurjective_comp_apply _ _ _ g⟩
  choose r hr using hex
  have hinj : ∀ m, Function.Injective (r m) := fun m => by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨g, rfl⟩ := hπ b
    exact (hker m g).1 ((hr m g).symm.trans hb)
  refine ⟨fun m => IsFractionRing.lift (hinj m), fun b => ?_⟩
  obtain ⟨g, rfl⟩ := hπ b
  have h1 := ((continuous_aeval (map (Int.castRingHom ℚ) g)).tendsto _).comp hl
  simp only [IsFractionRing.lift_algebraMap, hr]
  rw [hπa, hom_aeval x a g, ← aeval_map_int]
  refine h1.congr fun m => ?_
  exact aeval_map_int _ _

theorem bound_of_emb {K B Ω : Type} [Field K] [NumberField K] [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B]
    [Field Ω] [Algebra B Ω] [IsFractionRing B Ω] (ι : K →+* Ω) (a₀ : 𝓞 K →+* B)
    (ha : ∀ c : 𝓞 K, algebraMap B Ω (a₀ c) = ι (c : K)) (x : B →+* ℂ) {J : Type} (r : J → B)
    (F G : (K →+* ℂ) → (J → ℂ) → ℝ) (hF : ∀ σ, Continuous (F σ)) (hG : ∀ σ, Continuous (G σ))
    (h : ∀ ρ : Ω →+* ℂ, F (ρ.comp ι) (fun j => ρ (algebraMap B Ω (r j))) ≤ G (ρ.comp ι) (fun j => ρ (algebraMap B Ω (r j)))) :
    ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = x.comp a₀ ∧ F σ (fun j => x (r j)) ≤ G σ (fun j => x (r j)) := by
  have : CharZero Ω := charZero_of_injective_ringHom ι.injective
  obtain ⟨ρ, hρ⟩ := exists_seq_emb (Ω := Ω) x
  obtain ⟨σ, hσ⟩ : ∃ σ : K →+* ℂ, ∃ᶠ m in atTop, (ρ m).comp ι = σ :=
    frequently_exists.1 (Frequently.of_forall fun m => ⟨_, rfl⟩)
  have ht : Tendsto (fun m j => ρ m (algebraMap B Ω (r j))) atTop (𝓝 fun j => x (r j)) :=
    tendsto_pi_nhds.2 fun j => hρ _
  refine ⟨σ, RingHom.ext fun c => ?_, ?_⟩
  · refine tendsto_nhds_unique_of_frequently_eq (tendsto_const_nhds (x := σ (c : K))) (hρ (a₀ c))
      (hσ.mono fun m hm => ?_)
    rw [ha, ← hm]
    rfl
  · refine le_of_tendsto_of_tendsto_of_frequently (((hF σ).tendsto _).comp ht) (((hG σ).tendsto _).comp ht)
      (hσ.mono fun m hm => ?_)
    have := h (ρ m)
    rwa [hm] at this

end ChowFormHeightComparison₂.GenericDenseBound
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace ChowFormHeightComparison₂.GenericDenseBound

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem finiteType_sections {K : Type} [Field K] [NumberField K] {X : Scheme.{0}} {p : X ⟶ Sp (𝓞 K)}
    (hp : IsProjOver p) {W : X.Opens} (hW : IsAffineOpen W) : Algebra.FiniteType ℤ Γ(X, W) := by
  have : IsProper p := by
    obtain ⟨N, j, _, e⟩ := hp
    have := isProper_str (𝓞 K) N
    rw [← e]
    infer_instance
  have hft : (algX p W).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩
      (show W ≤ p ⁻¹ᵁ ⊤ from le_top)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of (𝓞 K))).symm.commRingCatIsoToRingEquiv.surjective)
  have h0 : (algebraMap ℤ (𝓞 K)).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h1 := hft.comp h0
  rw [Subsingleton.elim ((algX p W).comp (algebraMap ℤ (𝓞 K))) (algebraMap ℤ Γ(X, W))] at h1
  exact RingHom.finiteType_algebraMap.1 h1

theorem final_ineq {a Q t : ℝ} {τ : ℕ} (hQ : 0 ≤ Q) (h : a ≤ Real.exp (2 * (τ : ℝ) * t) * Q ^ τ) :
    a * Real.exp (-((τ : ℝ) * Real.log Q)) ≤ Real.exp (2 * (τ : ℝ) * t) := by
  rcases hQ.eq_or_lt with h0 | h0
  · subst h0
    rw [Real.log_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact h.trans (mul_le_of_le_one_right (Real.exp_pos _).le (pow_le_one₀ le_rfl zero_le_one))
  · rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log h0, mul_inv_le_iff₀ (pow_pos h0 τ)]
    exact h

theorem norm_le_of_emb {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : GlobalTheory.HermLB p}
    {ψ : Ω →+* X.functionField} {s : W → L.B.Sec} (hM : GlobalTheory.ImageModel.IsModelOf Nm W ev d p L ψ s) (β : Ω) (τ : ℕ)
    (t : ℝ)
    (hb : ∀ (N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame Nm W b g A → ∀ (σ : K →+* ℂ) (ρ : Ω →+* ℂ),
      ρ.comp (algebraMap K Ω) = σ → ‖ρ β‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (ev (b i))) ^ τ)
    (w : W) (hw : ev w ≠ 0) (σ : 𝓞 K →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ ptsIn p σ (L.B.U k))
    (hr : RegAt (under y) (ψ β * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) ^ τ)) :
    ‖ratVal (ψ β * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) ^ τ) y‖ ^ 2 *
      Real.exp (-((τ : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * (τ : ℝ) * t) := by
  obtain ⟨N, n, b, g, A, c, gw, hF, -, hbc, hφ⟩ := hM.fs
  obtain ⟨U', hU', a, ha⟩ := hr.exists_fnOf
  have hyk : under y ∈ L.B.U k := mem_ptsIn.1 hy
  obtain ⟨O, hO, hyO, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (memInf hU' hyk)
  have hO' : IsAffineOpen O := hO
  have hle1 : O ≤ U' := hle.trans inf_le_left
  have hle2 : O ≤ L.B.U k := hle.trans inf_le_right
  have hyO' : y ∈ ptsIn p σ O := mem_ptsIn.2 hyO
  have hg : genericPoint X ∈ O := gen_mem hyO
  have : Nonempty O := ⟨⟨_, hyO⟩⟩
  have := finiteType_sections hM.arith.isProjOver hO'
  have := functionField_isFractionRing_of_isAffineOpen X O hO'
  have halg : ∀ z : Γ(X, O), algebraMap Γ(X, O) X.functionField z = fnOf O hg z := fun _ => rfl
  let r : Option (Fin n) → Γ(X, O) := fun j => j.elim (resG X hle1 a) fun j => resG X hle2 ((s (gw j)).f k)
  have hψw : ψ (ev w) ≠ 0 := (map_ne_zero ψ).2 hw
  set u := fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) with hu
  obtain ⟨σ', hσ', hineq⟩ := bound_of_emb (Ω := X.functionField) (ψ.comp (algebraMap K Ω)) (algX p O)
    (fun z => by
      rw [halg, RingHom.comp_apply, hM.base]
      exact (RingHom.congr_fun (fnOf_comp_algX p O hg) z).trans rfl)
    (evHom hyO') r (fun _ v => ‖v none‖ ^ 2)
    (fun σ' v => Real.exp (2 * (τ : ℝ) * t) * (∑ a, ‖∑ j, (∑ m, σ' (c j m) * A σ' m a) * v (some j)‖ ^ 2) ^ τ)
    (fun _ => by fun_prop) (fun _ => by fun_prop)
    (fun ρ => by
      have h1 := hb N n b g A hF _ (ρ.comp ψ) rfl
      have e0 : (ρ.comp ψ).comp (algebraMap K Ω) = ρ.comp (ψ.comp (algebraMap K Ω)) := rfl
      rw [e0] at h1
      generalize hσ' : ρ.comp (ψ.comp (algebraMap K Ω)) = σ' at h1 ⊢
      have hσa : ∀ z, σ' z = ρ (ψ (algebraMap K Ω z)) := fun z => by rw [← hσ']; rfl
      set lam := ρ ((ψ (ev w))⁻¹ * u) with hlam
      have e1 : ρ (algebraMap Γ(X, O) X.functionField (r none)) = ρ (ψ β) * lam ^ τ := by
        rw [halg]
        show ρ (fnOf O hg (resG X hle1 a)) = _
        rw [fnOf_resG, ha, hlam, ← map_pow ρ, ← map_mul ρ, mul_pow, mul_assoc]
      have e2 : ∀ j, ρ (algebraMap Γ(X, O) X.functionField (r (some j))) = ρ (ψ (ev (gw j))) * lam := fun j => by
        rw [halg]
        show ρ (fnOf O hg (resG X hle2 ((s (gw j)).f k))) = _
        rw [fnOf_resG, hlam, ← map_mul ρ]
        congr 1
        have := hM.ratio w (gw j) k (hle2 hg)
        rw [← mul_assoc, mul_comm (ψ (ev (gw j))), mul_assoc, eq_inv_mul_iff_mul_eq₀ hψw]
        exact this
      have e3 : ∀ m, ρ (ψ (ev (b m))) = ∑ j, σ' (c j m) * ρ (ψ (ev (gw j))) := fun m => by
        rw [hbc m]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, Algebra.smul_def, map_mul, hσa]
      have e4 : ∀ a, ∑ j, (∑ m, σ' (c j m) * A σ' m a) * (ρ (ψ (ev (gw j))) * lam) =
          lam * ∑ m, A σ' m a * ρ (ψ (ev (b m))) := fun a => by
        simp only [e3, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      simp only [e1, e2, e4, norm_mul, mul_pow, norm_pow, ← Finset.mul_sum]
      have hS : 0 ≤ ∑ a, ‖∑ m, A σ' m a * ρ (ψ (ev (b m)))‖ ^ 2 := by positivity
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have e5 : (Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ') (fun i => (ρ.comp ψ) (ev (b i))) ^ τ) ^ 2 =
          Real.exp (2 * (τ : ℝ) * t) * (∑ a, ‖∑ m, A σ' m a * ρ (ψ (ev (b m)))‖ ^ 2) ^ τ := by
        rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul, mul_comm τ 2, pow_mul]
        unfold GlobalTheory.Adelic.archSize
        simp only [RingHom.comp_apply]
        rw [Real.sq_sqrt hS]
        congr 2
        push_cast
        ring
      rw [e5] at h2
      have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ (‖lam‖ ^ τ) ^ 2 by positivity)
      refine h3.trans_eq ?_
      ring)
  have hσ : σ'.comp (algebraMap (𝓞 K) K) = σ := hσ'.trans (RingHom.ext fun z =>
    (ev_eq hyO' _).symm.trans (ev_algX hyO' z))
  subst hσ
  rw [hφ σ' k y, ← ha, ratVal_fnOf (mem_ptsIn.2 hU')]
  refine final_ineq (by positivity) ?_
  have f1 : evHom hyO' (r none) = GlobalTheory.CxPts.ev p _ U' a y := (ev_eq hyO' _).symm.trans (ev_res hle1 hyO' a)
  have f2 : ∀ j, evHom hyO' (r (some j)) = valR y.1 (L.B.U k) ((s (gw j)).f k) := fun j =>
    (ev_eq hyO' _).symm.trans (ev_res hle2 hyO' _)
  simp only [f1, f2] at hineq
  exact hineq

end ChowFormHeightComparison₂.GenericDenseBound
