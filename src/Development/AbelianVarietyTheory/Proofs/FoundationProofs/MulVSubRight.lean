module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Matrix

noncomputable section

namespace GlobalTheory.RatEqui

variable (D : D7) {N N' : ℕ}

theorem embT_conj (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = (starRingEnd ℂ) (embT D τ x) :=
  Formalism.HC.HostAx.conjE_apply D.host.toHostAx _ _

def adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E :=
  (M.map D.host.conj).transpose

theorem adj_map {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (adj D M).map (embT D τ) = (M.map (embT D τ))ᴴ := by
  ext i j
  simp [adj, embT_conj]

def mulV (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E) :
    VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ => (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) : Matrix _ _ ℂ)
  map_add' z w := by
    funext τ
    change M'.map (embT D τ) * (Matrix.of (z τ) + Matrix.of (w τ)) * M.map (embT D τ) = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c z := by
    funext τ
    change M'.map (embT D τ) * (c • Matrix.of (z τ)) * M.map (embT D τ) = _
    rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem mulV_apply (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') (τ : D.what₂.Tau) :
    mulV D M' M z τ = (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) : Matrix _ _ ℂ) := rfl

theorem mulV_mulV (M₁' M₂' : Matrix (Fin N') (Fin N') D.host.E) (M₁ M₂ : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D M₁' M₁ (mulV D M₂' M₂ z) = mulV D (M₁' * M₂') (M₂ * M₁) z := by
  funext τ
  change M₁'.map (embT D τ) * (M₂'.map (embT D τ) * Matrix.of (z τ) * M₂.map (embT D τ)) * M₁.map (embT D τ) =
    (M₁' * M₂').map (embT D τ) * Matrix.of (z τ) * (M₂ * M₁).map (embT D τ)
  simp only [Matrix.map_mul, Matrix.mul_assoc]

theorem mulV_one (z : VC D N N') : mulV D 1 1 z = z := by
  funext τ
  rw [mulV_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.one_mul, Matrix.mul_one]
  rfl

theorem mulV_sub_left (M₁' M₂' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D (M₁' - M₂') M z = mulV D M₁' M z - mulV D M₂' M z := by
  funext τ
  change (M₁' - M₂').map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) =
    M₁'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) - M₂'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, Matrix.sub_mul]

theorem mulV_sub_right (M' : Matrix (Fin N') (Fin N') D.host.E) (M₁ M₂ : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D M' (M₁ - M₂) z = mulV D M' M₁ z - mulV D M' M₂ z := by
  funext τ
  change M'.map (embT D τ) * Matrix.of (z τ) * (M₁ - M₂).map (embT D τ) =
    M'.map (embT D τ) * Matrix.of (z τ) * M₁.map (embT D τ) - M'.map (embT D τ) * Matrix.of (z τ) * M₂.map (embT D τ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.mul_sub]

theorem Hf_eq_trace (T : Tor D) (z w : VC D N N') :
    Hf D T z w = (∑ τ, Matrix.trace (Matrix.of (z τ) * (Matrix.of (w τ))ᴴ)) / (area T.abelian₂ : ℂ) := by
  simp [Hf, Matrix.trace, Matrix.mul_apply]

theorem Hf_mulV (T : Tor D) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z w : VC D N N') : Hf D T (mulV D M' M z) w = Hf D T z (mulV D (adj D M') (adj D M) w) := by
  rw [Hf_eq_trace, Hf_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  change Matrix.trace (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) * (Matrix.of (w τ))ᴴ) =
    Matrix.trace (Matrix.of (z τ) * ((adj D M').map (embT D τ) * Matrix.of (w τ) * (adj D M).map (embT D τ))ᴴ)
  rw [adj_map, adj_map, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem pull_eq (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (G : VC D N N' → ℂ) :
    pull D (tor0 D cc δ) γ γ' G = fun z => G (mulV D (adj D γ') γ z) := by
  funext z
  unfold pull
  congr 1
  funext τ
  rw [mulV_apply, adj_map]
  rfl

theorem mulV_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M' : Matrix (Fin N') (Fin N') D.host.E)
    (M : Matrix (Fin N) (Fin N) D.host.E) (z : Matrix (Fin N') (Fin N) D.host.E) :
    mulV D M' M (pt D (tor0 D cc δ) δ z) = pt D (tor0 D cc δ) δ (M' * z * M) := by
  unfold pt
  rw [map_smul]
  congr 1
  funext τ
  change M'.map (embT D τ) * z.map (embT D τ) * M.map (embT D τ) = (M' * z * M).map (embT D τ)
  simp only [Matrix.map_mul]

theorem adj_mul {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) D.host.E) : adj D (M₁ * M₂) = adj D M₂ * adj D M₁ := by
  unfold adj
  rw [← Matrix.transpose_mul]
  congr 1
  exact Matrix.map_mul (f := (D.host.conj : D.host.E →+* D.host.E))

theorem adj_one {n : ℕ} : adj D (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  unfold adj
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end GlobalTheory.RatEqui
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerate
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.TraceSemisimple

def spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) :
    Subalgebra K (Matrix (Fin a) (Fin a) K) :=
  (Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))).toSubalgebra
    (Submodule.subset_span ⟨1, by simp⟩)
    (by
      intro x y hx hy
      have h := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp⟩)

theorem mem_spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K)
    (x : Matrix (Fin a) (Fin a) K) :
    x ∈ spanAlg ρ ↔ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) := Iff.rfl

theorem isSemisimpleRing_spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ}
    (ρ : Γ →* GL (Fin a) K)
    (h : ∀ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) :
    IsSemisimpleRing (spanAlg ρ) := by
  have : IsArtinianRing (spanAlg ρ) := IsArtinianRing.of_finite K _
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  apply Subtype.ext
  refine h x.1 x.2 fun g => ?_
  let y : spanAlg ρ := ⟨(ρ g : GL (Fin a) K), Submodule.subset_span ⟨g, rfl⟩⟩
  have hxy : x * y ∈ Ring.jacobson (spanAlg ρ) := Ideal.mul_mem_right _ _ hx
  obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson (spanAlg ρ)) := IsSemiprimaryRing.isNilpotent
  have h1 : (x * y) ^ n = 0 := by
    have := Ideal.pow_mem_pow hxy n
    rw [hn] at this
    simpa using this
  have h2 : IsNilpotent ((x * y : spanAlg ρ) : Matrix (Fin a) (Fin a) K) :=
    ⟨n, by simpa using congrArg Subtype.val h1⟩
  exact (Matrix.isNilpotent_trace_of_isNilpotent h2).eq_zero

theorem isSSRep_of_trace_nondegenerate :
    ∀ (Γ K : Type) [Group Γ] [Field K] (a : ℕ) (ρ : Γ →* GL (Fin a) K),
    (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) →
    IsSSRep ρ := by
  intro Γ K _ _ a ρ h W hW
  have := isSemisimpleRing_spanAlg ρ h
  let f : spanAlg ρ →+* Module.End K (Fin a → K) :=
    ((Matrix.toLinAlgEquiv' (R := K) (n := Fin a)).toAlgHom.comp (spanAlg ρ).val).toRingHom
  let : Module (spanAlg ρ) (Fin a → K) := Module.compHom _ f
  have hW' : ∀ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      ∀ v ∈ W, x.mulVec v ∈ W := by
    intro x hx v hv
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hW g v hv
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_mulVec]; exact W.smul_mem c hx
  let U : Submodule (spanAlg ρ) (Fin a → K) :=
    { toAddSubmonoid := W.toAddSubmonoid
      smul_mem' := fun x v hv => hW' x.1 x.2 v hv }
  obtain ⟨U', hU⟩ := exists_isCompl U
  let W' : Submodule K (Fin a → K) :=
    { toAddSubmonoid := U'.toAddSubmonoid
      smul_mem' := fun c v hv => by
        have : (c • (1 : Matrix (Fin a) (Fin a) K)).mulVec v ∈ U' :=
          U'.smul_mem ⟨c • 1, (spanAlg ρ).smul_mem (spanAlg ρ).one_mem c⟩ hv
        rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at this }
  refine ⟨W', fun g v hv => ?_, ?_, ?_⟩
  · exact U'.smul_mem ⟨(ρ g : GL (Fin a) K), Submodule.subset_span ⟨g, rfl⟩⟩ hv
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    exact (Submodule.disjoint_def.1 hU.disjoint) v hv hv'
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have : v ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 this
    exact Submodule.add_mem_sup hx hy

end GlobalTheory.TraceSemisimple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GenusOneDatum


open PowerSeries in
theorem exists_fixed_of_contract {R : Type*} [CommRing R] (T : PowerSeries R → PowerSeries R)
    (hT : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ x - y → X ^ (n + 1) ∣ T x - T y) :
    ∃ x, T x = x := by
  have hit : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ T^[n] x - T^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hT n _ _ (ih x y)
  let L : PowerSeries R := PowerSeries.mk fun n => coeff n (T^[n + 1] 0)
  have hL : ∀ n, X ^ n ∣ L - T^[n] 0 := by
    intro n
    rw [X_pow_dvd_iff]
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, n = (m + 1) + k := ⟨n - (m + 1), by omega⟩
    have := X_pow_dvd_iff.1 (hit (m + 1) 0 (T^[k] 0)) m (by omega)
    rw [← Function.iterate_add_apply] at this
    simpa [L] using this
  refine ⟨L, ?_⟩
  ext n
  have h1 := hT n _ _ (hL n)
  have h2 := hL (n + 1)
  rw [Function.iterate_succ_apply'] at h2
  have h3 := dvd_sub h1 h2
  have h4 := X_pow_dvd_iff.1 h3 n (by omega)
  rw [sub_sub_sub_cancel_right, map_sub, sub_eq_zero] at h4
  exact h4

theorem exists_isWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) : ∃ wq, IsWq W wq := by
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  obtain ⟨w, hw⟩ := exists_fixed_of_contract (fun wq : PowerSeries ℂ_[p] =>
    1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3) (by
      rintro n x y ⟨z, hz⟩
      refine ⟨z * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2)), ?_⟩
      have hz' : x - y = X ^ n * z := hz
      change _ = X ^ (n + 1) * _
      linear_combination (X * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2))) * hz')
  exact ⟨w, hw.symm⟩

theorem constantCoeff_of_isWq {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.constantCoeff wq = 1 := by
  have h' := congrArg PowerSeries.constantCoeff h
  simpa using h'

theorem coeff_one_flog {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.coeff 1 (flog W wq) = 1 := by
  have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  simp [flog, omegaW, PowerSeries.constantCoeff_inv, constantCoeff_of_isWq h, h2]

theorem constantCoeff_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : PowerSeries.constantCoeff (flog W wq) = 0 := by
  simp [flog]

theorem exists_subst_eq_X {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    ∃ ex : PowerSeries R, PowerSeries.constantCoeff ex = 0 ∧
      PowerSeries.subst ex l = PowerSeries.X := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, -⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h ()⟩

theorem exists_genusOne_datum : ∀ (D : D7), GL3Theta.modelEx D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∃ g : GL3Theta.G1 p, GL3Theta.At D cc δ g ∧ g.lam = lam ∧ ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
  intro D hm p _ lam cc δ hc hcop
  obtain ⟨⟨C, hC⟩, -, hu⟩ := hm p lam cc δ hc.1 hcop hc.2
  obtain ⟨wq, hwq⟩ := exists_isWq (C • wModel lam (lamOf D cc δ))
  obtain ⟨ex, he0, he⟩ := exists_subst_eq_X _ (constantCoeff_flog _ wq) (coeff_one_flog hwq)
  exact ⟨⟨lam, lamOf D cc δ, C, wq, ex⟩, ⟨hc.1, hcop, hc.2, rfl, hC, hwq, he0, he⟩, rfl, hu C hC⟩

end GlobalTheory.GenusOneDatum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.UnramHecke

def phase : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [div_mul_div_comm]

theorem phase_val (z : ℂˣ) : ((phase z : ℂˣ) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl

theorem norm_phase (z : ℂˣ) : ‖((phase z : ℂˣ) : ℂ)‖ = 1 := by
  rw [phase_val, norm_div, Complex.norm_real, norm_norm, div_self (by simp)]

theorem phase_of_norm (z : ℂˣ) (h : ‖(z : ℂ)‖ = 1) : phase z = z := by
  ext; rw [phase_val, h]; simp

theorem exists_unitary_extension {A M : Type} [CommGroup A] [CommGroup M] (Φ : A →* M) (χ : A →* ℂˣ)
    (hk : ∀ a, Φ a = 1 → χ a = 1) (hu : ∀ a, ‖((χ a : ℂˣ) : ℂ)‖ = 1) :
    ∃ κ : M →* ℂˣ, (∀ x, κ (Φ x) = χ x) ∧ ∀ y, ‖((κ y : ℂˣ) : ℂ)‖ = 1 := by
  let _ : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact Units.ne_zero _ hz.symm
    exact ⟨Additive.ofMul (Units.mk0 z hz0), Units.ext hz⟩
  let _ : DivisibleBy (Additive ℂˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift Φ)) (QuotientGroup.kerLift_injective Φ)
    (MonoidHom.toAdditive (QuotientGroup.lift Φ.ker χ fun a ha => hk a ha))
  refine ⟨phase.comp (MonoidHom.toAdditive.symm ρ), fun x => ?_, fun y => norm_phase _⟩
  have h : (MonoidHom.toAdditive.symm ρ) (Φ x) = χ x :=
    DFunLike.congr_fun hρ (Additive.ofMul (QuotientGroup.mk x))
  rw [MonoidHom.comp_apply, h, phase_of_norm _ (hu x)]

variable (D : D7)

theorem emb_conj (σ : D.host.E →+* ℂ) (z : D.host.E) : σ (D.host.conj z) = starRingEnd ℂ (σ z) :=
  D.host.conjE_apply σ z

theorem conj_conj (z : D.host.E) : D.host.conj (D.host.conj z) = z := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

theorem sgA_sgA (x : AE D) : sgA D (sgA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]

theorem sgU_sgU (x : (AE D)ˣ) : sgU D (sgU D x) = x := Units.ext (sgA_sgA D x)

theorem sgA_mem {x : AE D} (hx : x ∈ OhE D) : sgA D x ∈ OhE D :=
  Formalism.UG.P.csDual_sig_mem _ hx

def intUnits : Subgroup (AE D)ˣ where
  carrier := {u | IntU D u}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [Units.val_mul]; exact mul_mem ha.1 hb.1,
    by rw [mul_inv, Units.val_mul]; exact mul_mem ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem sgU_mem {u : (AE D)ˣ} (hu : u ∈ intUnits D) : sgU D u ∈ intUnits D :=
  ⟨sgA_mem D hu.1, by rw [← map_inv]; exact sgA_mem D hu.2⟩

def ratio : (AE D)ˣ →* (AE D)ˣ := MonoidHom.id _ / sgU D

theorem ratio_apply (x : (AE D)ˣ) : ratio D x = x / sgU D x := rfl

abbrev incU : D.host.Eˣ →* (AE D)ˣ := Units.map (inc D).toMonoidHom

def infChar (c : ℤ) : D.host.Eˣ →* ℂˣ :=
  ∏ τ : D.what₂.Tau, (zpowGroupHom (2 * c)).comp (phase.comp (Units.map (embT D τ).toMonoidHom))

theorem infChar_val (c : ℤ) (a : D.host.Eˣ) : ((infChar D c a : ℂˣ) : ℂ) =
    ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (2 * c) := by
  simp [infChar, phase_val]

theorem norm_infChar (c : ℤ) (a : D.host.Eˣ) : ‖((infChar D c a : ℂˣ) : ℂ)‖ = 1 := by
  rw [infChar_val, norm_prod]
  refine Finset.prod_eq_one fun τ _ => ?_
  have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (by simpa using h), one_zpow]

theorem ratio_eq_pm (a : D.host.Eˣ) (h : ratio D (incU D a) ∈ intUnits D) :
    ∃ m : ℕ, 0 < m ∧ ((a : D.host.E) / D.host.conj a) ^ m = 1 := by
  have hc : D.host.conj (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  have hval : ((ratio D (incU D a) : (AE D)ˣ) : AE D) = inc D ((a : D.host.E) / D.host.conj a) := by
    have h1 : ((sgU D (incU D a) : (AE D)ˣ) : AE D) = inc D (D.host.conj a) :=
      Formalism.UG.P.csDual_sig_incl _ _
    rw [ratio_apply, div_eq_mul_inv, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, h1, ← map_mul,
      div_mul_cancel₀ _ hc]
    rfl
  have hint : IsIntegral ℤ ((a : D.host.E) / D.host.conj a) :=
    Formalism.UG.P.csGlob_int (F := ℚ) _ (by have := h.1; rw [hval] at this; exact this)
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one D.host.E ℂ hint (fun φ => by
    rw [map_div₀, emb_conj, norm_div, Complex.norm_conj, div_self]
    simpa using a.ne_zero)
  exact ⟨n, hn, hpow⟩

theorem infChar_eq_one (c : ℤ) (a : D.host.Eˣ) (h : ratio D (incU D a) ∈ intUnits D) : infChar D c a = 1 := by
  apply Units.ext
  rw [infChar_val, Units.val_one]
  have key : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (2 * c) =
      embT D τ ((a : D.host.E) / D.host.conj a) ^ c := by
    intro τ
    have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
    rw [zpow_mul, map_div₀, emb_conj, zpow_two, div_mul_div_comm, ← sq (‖_‖ : ℂ), ← Complex.mul_conj',
      mul_div_mul_left _ _ h]
  simp only [key]
  exact UpperTheory.Mu.prod_emb_zpow D.host D.eTau (ratio_eq_pm D a h) c

end GlobalTheory.NormSum.UnramHecke
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasis
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OnCoord
variable {D : D7}

theorem embT_conj (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = starRingEnd ℂ (embT D τ x) :=
  D.host.conjE_apply (embT D τ) x

theorem coord_emb (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (y : Matrix (Fin N') (Fin N) D.host.E) :
    coordB D (tor0 D cc δ) b k (embV D (tor0 D cc δ) y) =
      D.host.φ₀ ((hYY D y (b k) : D.host.K) : D.host.E) := by
  unfold hYY
  rw [← h.2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordB, embV, tor0, map_sum, map_mul, embT_conj]

theorem coord_add (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (z w : VC D N N') :
    coordB D T b k (z + w) = coordB D T b k z + coordB D T b k w := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coord_smul (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (c : ℂ) (z : VC D N N') :
    coordB D T b k (c • z) = c * coordB D T b k z := by
  simp only [coordB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

noncomputable def coordL (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b k
  map_add' := coord_add T b k
  map_smul' := coord_smul T b k

theorem coord_sum (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) {ι : Type} (s : Finset ι) (z : ι → VC D N N') :
    coordB D T b k (∑ i ∈ s, z i) = ∑ i ∈ s, coordB D T b k (z i) :=
  map_sum (coordL T b k) z s

theorem embT_injective : Function.Injective (embT D) := by
  intro τ τ' h
  apply D.eTau.injective
  apply Subtype.ext
  have h1 : D.host.sigmaOf (D.eTau τ : D.R.GG) = D.host.sigmaOf (D.eTau τ' : D.R.GG) := by
    ext x
    have := DFunLike.congr_fun h x
    exact D.host.φ₀.injective this
  exact (D.host.gal).symm.injective h1

theorem indep (c : D.what₂.Tau → ℂ) (h : ∀ x, ∑ τ, embT D τ x * c τ = 0) (τ : D.what₂.Tau) : c τ = 0 := by
  have h1 := (linearIndependent_monoidHom D.host.E ℂ).comp (fun τ => (embT D τ : D.host.E →* ℂ))
    (fun τ τ' h => embT_injective (RingHom.coe_monoidHom_injective h))
  refine Fintype.linearIndependent_iff.1 h1 c ?_ τ
  funext x
  simpa [Finset.sum_apply, mul_comm] using h x

theorem lin_eq_zero (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (f : VC D N N' →ₗ[ℂ] ℂ)
    (h : ∀ y, f (embV D (tor0 D cc δ) y) = 0) (z : VC D N N') : f z = 0 := by
  have h1 : ∀ τ i j, f (coordV D (τ, i, j)) = 0 := by
    intro τ i j
    refine indep (fun τ => f (coordV D (τ, i, j))) (fun x => ?_) τ
    rw [← h (Matrix.single i j x)]
    have : embV D (tor0 D cc δ) (Matrix.single i j x) = ∑ τ, embT D τ x • coordV D (τ, i, j) := by
      funext τ' i' j'
      simp only [embV, tor0, coordV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.single_apply]
      by_cases hi : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := hi
        simp
      · have : ¬ (i' = i ∧ j' = j) := fun h => hi ⟨h.1.symm, h.2.symm⟩
        simp [hi, this]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp
  have h2 : z = ∑ τ, ∑ i, ∑ j, z τ i j • coordV D (τ, i, j) := by
    funext τ' i' j'
    simp [coordV, Finset.sum_apply, ite_and]
  rw [h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, h1]

theorem embV_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (x + y) = embV D (tor0 D cc δ) x + embV D (tor0 D cc δ) y := by
  funext τ i j
  simp [embV, tor0]

theorem embV_smul (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (a : D.host.K)
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (a • y) = D.host.φ₀ (a : D.host.E) • embV D (tor0 D cc δ) y := by
  funext τ i j
  have : (a • y) i j = (a : D.host.E) * y i j := rfl
  simp only [embV, tor0, this, map_mul, h.1 τ a, Pi.smul_apply, smul_eq_mul]

theorem coords_of_orthonormal_basis : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k)) ∧ (∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0) ∧ (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D (tor0 D cc δ) b k z * (starRingEnd ℂ) (coordB D (tor0 D cc δ) b k w)) ∧ (∀ x : VC D N N', x ∈ LaB D (tor0 D cc δ) b ↔ ∀ k, coordB D (tor0 D cc δ) b k x ∈ (lamOf D cc δ)) ∧ Function.Bijective (fun (z : VC D N N') (k : Fin r) => coordB D (tor0 D cc δ) b k z) := by
  intro D h cc δ N N' r b hb
  have h2 : ∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0 := by
    intro j k
    rw [coord_emb h, hb.1 k j]
    split_ifs <;> simp
  have hc : ∀ (c : Fin r → ℂ) j,
      coordB D (tor0 D cc δ) b j (∑ k, c k • embV D (tor0 D cc δ) (b k)) = c j := by
    intro c j
    simp [coord_sum, coord_smul, h2]
  let P : VC D N N' →ₗ[ℂ] VC D N N' :=
    ∑ k, (coordL (tor0 D cc δ) b k).smulRight (embV D (tor0 D cc δ) (b k))
  have hP : ∀ z, P z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k) := by
    intro z
    simp only [P, LinearMap.sum_apply, LinearMap.smulRight_apply]
    rfl
  have hE : ∀ y, P (embV D (tor0 D cc δ) y) = embV D (tor0 D cc δ) y := by
    intro y
    have hy : y ∈ Submodule.span D.host.K (Set.range b) := hb.2 ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [hP]
      simp [h2]
    | zero =>
      have : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
        funext τ i j
        simp [embV, tor0]
      rw [this, map_zero]
    | add x y _ _ hx hy => rw [embV_add, map_add (f := _), hx, hy]
    | smul a x _ hx => rw [embV_smul h, map_smul, hx]
  have h1 : ∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k) := by
    intro z
    rw [← hP]
    funext τ i j
    let e : VC D N N' →ₗ[ℂ] ℂ :=
      { toFun := fun z => z τ i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have := lin_eq_zero cc δ (e ∘ₗ (LinearMap.id - P)) (fun y => by
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, hE, LinearMap.id_apply, sub_self, map_zero]) z
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub] at this
    exact sub_eq_zero.1 this
  refine ⟨h1, h2, fun z w => ?_, fun x => ⟨fun hx k => ?_, fun hx => ?_⟩, fun z w hzw => ?_, fun c => ?_⟩
  · have hw : ∀ τ i j, w τ i j = ∑ k, coordB D (tor0 D cc δ) b k w * (tor0 D cc δ).emb τ (b k i j) := by
      intro τ i j
      have := congrFun (congrFun (congrFun (h1 w) τ) i) j
      simpa [Finset.sum_apply, embV] using this
    obtain ⟨c, hcw⟩ : ∃ c : Fin r → ℂ, ∀ k, coordB D (tor0 D cc δ) b k w = c k := ⟨_, fun _ => rfl⟩
    simp only [hcw] at hw ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, map_sum, map_mul, Finset.mul_sum, coordB, Finset.sum_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  · induction hx using AddSubgroup.closure_induction generalizing k with
    | mem x hx =>
      obtain ⟨w, hw, j, rfl⟩ := hx
      rw [coord_smul, h2]
      split_ifs
      · rw [mul_one]; exact hw
      · rw [mul_zero]; exact zero_mem _
    | zero =>
      have : coordB D (tor0 D cc δ) b k 0 = 0 := map_zero (coordL (tor0 D cc δ) b k)
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy => rw [coord_add]; exact add_mem (hx k) (hy k)
    | neg x _ hx =>
      have : coordB D (tor0 D cc δ) b k (-x) = - coordB D (tor0 D cc δ) b k x :=
        map_neg (coordL (tor0 D cc δ) b k) x
      rw [this]; exact neg_mem (hx k)
  · rw [h1 x]
    exact sum_mem fun k _ => AddSubgroup.subset_closure ⟨_, hx k, k, rfl⟩
  · rw [h1 z, h1 w]
    exact Finset.sum_congr rfl fun k _ => by rw [show coordB D (tor0 D cc δ) b k z = coordB D (tor0 D cc δ) b k w from congrFun hzw k]
  · exact ⟨_, funext (hc c)⟩

end GlobalTheory.OnCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasisStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_along_orthonormal_realSubfield_basis : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k)) ∧ (∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0) ∧ (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D (tor0 D cc δ) b k z * (starRingEnd ℂ) (coordB D (tor0 D cc δ) b k w)) ∧ (∀ x : VC D N N', x ∈ LaB D (tor0 D cc δ) b ↔ ∀ k, coordB D (tor0 D cc δ) b k x ∈ (lamOf D cc δ)) ∧ Function.Bijective (fun (z : VC D N N') (k : Fin r) => coordB D (tor0 D cc δ) b k z) := by
  first | exact @GlobalTheory.OnCoord.coords_of_orthonormal_basis | exact GlobalTheory.OnCoord.coords_of_orthonormal_basis | (intros; apply GlobalTheory.OnCoord.coords_of_orthonormal_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.TraceInt

theorem pair_integral {E : Type} [Field E] [NumberField E] [StarRing E] {N N' : ℕ}
    {L : Submodule (𝓞 E) (Fin N → E)} {L' : Submodule (𝓞 E) (Fin N' → E)}
    (hL : IsSDLat E N L) (hL' : IsSDLat E N' L') {A B : Matrix (Fin N') (Fin N) E}
    (hA : ∀ x ∈ L, A.mulVec x ∈ L') (hB : ∀ x ∈ L, B.mulVec x ∈ L') :
    IsIntegral ℤ (∑ i, ∑ j, A i j * star (B i j)) := by
  obtain ⟨hLfg, hLspan, hLdual⟩ := hL
  obtain ⟨-, -, hL'dual⟩ := hL'
  obtain ⟨m, x, φ, hx, hφ, hxφ⟩ := GlobalTheory.TauLat.exists_dual_family L
    { toIsLattice := Submodule.IsLattice.of_fg E hLfg, span_eq_top := hLspan }

  set ψ : Fin m → Fin N → E := fun k b => star (φ k b) with hψdef
  have hψ : ∀ k, ψ k ∈ L := by
    intro k
    rw [hLdual]
    intro y hy
    rw [GlobalTheory.TauLat.mem_range_iff]
    have h1 : ∑ i, star (y i) * ψ k i = starRingEnd E (φ k ⬝ᵥ y) := by
      rw [starRingEnd_apply, dotProduct, star_sum]
      simp [hψdef, star_mul', mul_comm]
    unfold stdH
    rw [h1]
    exact GlobalTheory.TauLat.integral_map _ (hφ k y hy)

  have key : ∀ i, ∑ j, A i j * star (B i j) = ∑ k, (A.mulVec (x k)) i * star ((B.mulVec (ψ k)) i) := by
    intro i
    have e1 : ∑ j, A i j * star (B i j) =
        ∑ a, ∑ b, A i a * star (B i b) * ∑ k, x k a * φ k b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [hxφ, mul_ite]
    rw [e1]
    simp only [Matrix.mulVec, dotProduct, hψdef, star_sum, star_mul', star_star, Finset.mul_sum,
      Finset.sum_mul]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_comm]
  refine IsIntegral.sum _ fun k _ => ?_

  have hint : IsIntegral ℤ (∑ i, star ((A.mulVec (x k)) i) * (B.mulVec (ψ k)) i) := by
    rw [← GlobalTheory.TauLat.mem_range_iff]
    exact (hL'dual _).1 (hB _ (hψ k)) _ (hA _ (hx k))
  have h2 : ∑ i, (A.mulVec (x k)) i * star ((B.mulVec (ψ k)) i) =
      starRingEnd E (∑ i, star ((A.mulVec (x k)) i) * (B.mulVec (ψ k)) i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, starRingEnd_apply, starRingEnd_apply, star_star, mul_comm]
  rw [h2]
  exact GlobalTheory.TauLat.integral_map _ hint

theorem mulVec_mem_of_homL (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') : ∀ x ∈ L, A.mulVec x ∈ L' := by
  unfold homL at hA
  induction hA using Submodule.span_induction with
  | mem B hB => exact hB
  | zero => intro x _; simp
  | add B C _ _ hB hC =>
    intro x hx
    rw [Matrix.add_mulVec]
    exact L'.add_mem (hB x hx) (hC x hx)
  | smul c B _ hB =>
    intro x hx
    rw [Matrix.smul_mulVec]
    exact L'.smul_mem c (hB x hx)

theorem hYY_add_left (D : D7) {N N' : ℕ} (x x' y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (x + x') y = hYY D x y + hYY D x' y := by
  unfold hYY
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem hYY_add_right (D : D7) {N N' : ℕ} (x y y' : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D x (y + y') = hYY D x y + hYY D x y' := by
  unfold hYY
  simp only [Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hYY_gen (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) (hL' : SD D L')
    {a a' : D.host.E} (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (ha' : a' ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    {A B : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L') (hB : B ∈ homL D L L') :
    hYY D (a • A) (a' • B) ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  have hs : IsIntegral ℤ (∑ i, ∑ j, A i j * D.host.conj (B i j)) := by
    let _ := D.host.cmStar
    have h := pair_integral (E := D.host.E) hL hL' (mulVec_mem_of_homL D hA) (mulVec_mem_of_homL D hB)
    simpa only [bridge_star_holds _ D.host] using h
  have hsum : ∑ i, ∑ j, (a • A) i j * D.host.conj ((a' • B) i j) =
      a * (∑ i, ∑ j, A i j * D.host.conj (B i j)) * D.host.conj a' := by
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have has : a * (∑ i, ∑ j, A i j * D.host.conj (B i j)) ∈ D.host.AA0 := by
    have h1 : ∀ c : 𝓞 D.host.E, (c : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro c
      have h := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
      rwa [Algebra.smul_def] at h
    rw [mul_comm]
    exact h1 ⟨_, hs⟩
  unfold hYY
  rw [hsum]
  exact (factMMUnimodular _ D.host _).1 has a' ha'

private theorem exists_ringOfIntegers_eq_conj (D : D7) (c : 𝓞 D.host.E) :
    ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.host.conj (c : D.host.E) :=
  ⟨⟨D.host.conj (c : D.host.E),
    GlobalTheory.TauLat.integral_map (D.host.conj : D.host.E →+* D.host.E) c.isIntegral_coe⟩, rfl⟩

private theorem conjO_conjO_unimodular_class_representatives (D : D7) (z : D.host.E) : D.host.conj (D.host.conj z) = z := by
  let _ := D.host.cmStar
  rw [← bridge_star_holds _ D.host z, ← bridge_star_holds _ D.host (star z), star_star]

private theorem hYY_smul_left_eq_conj_smul_right (D : D7) {N N' : ℕ} (c c' : 𝓞 D.host.E)
    (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (c • x) y = hYY D x (c' • y) := by
  unfold hYY
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
  change (c : D.host.E) * x i j * D.host.conj (y i j) =
    x i j * (D.host.conj (c' : D.host.E) * D.host.conj (y i j))
  rw [hc, conjO_conjO_unimodular_class_representatives]
  ring

private theorem hYY_smul_right_eq_conj_smul_left (D : D7) {N N' : ℕ} (c c' : 𝓞 D.host.E)
    (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D x (c • y) = hYY D (c' • x) y := by
  have hc' : (c : D.host.E) = D.host.conj (c' : D.host.E) := by rw [hc, conjO_conjO_unimodular_class_representatives]
  exact (hYY_smul_left_eq_conj_smul_right D c' c hc' x y).symm

theorem hYY_integral : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    ∀ x ∈ YYl D L L', ∀ y ∈ YYl D L L', hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  intro D N N' L L' hL hL' x hx y hy
  have hsub : ∀ (c : 𝓞 D.host.E) (a : D.host.E),
      a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) →
      (c : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro c a ha
    have h := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
    rwa [Algebra.smul_def] at h

  have hgen : ∀ y ∈ YYl D L L', ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      ∀ A ∈ homL D L L', hYY D (a • A) y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
    intro y hy
    unfold YYl at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a', ha', B, hB, rfl⟩ := hz
      intro a ha A hA
      exact hYY_gen D hL hL' ha ha' hA hB
    | zero =>
      intro a _ A _
      unfold hYY
      simp
    | add z w _ _ hz hw =>
      intro a ha A hA
      rw [hYY_add_right]
      exact Subring.add_mem _ (hz a ha A hA) (hw a ha A hA)
    | smul c z _ hz =>
      intro a ha A hA
      obtain ⟨c', hc'⟩ := exists_ringOfIntegers_eq_conj D c
      rw [hYY_smul_right_eq_conj_smul_left D c c' hc', ← smul_assoc, Algebra.smul_def]
      exact hz _ (hsub c' a ha) A hA
  unfold YYl at hx
  induction hx using Submodule.span_induction generalizing y with
  | mem z hz =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hz
    exact hgen y hy a ha A hA
  | zero =>
    unfold hYY
    simp
  | add z w _ _ hz hw =>
    rw [hYY_add_left]
    exact Subring.add_mem _ (hz y hy) (hw y hy)
  | smul c z _ hz =>
    obtain ⟨c', hc'⟩ := exists_ringOfIntegers_eq_conj D c
    rw [hYY_smul_left_eq_conj_smul_right D c c' hc']
    exact hz _ ((YYl D L L').smul_mem c' hy)

end GlobalTheory.NormSum.TraceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValuesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_pairing_integral_values : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∀ x ∈ YYl D L L', ∀ y ∈ YYl D L L', hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  first | exact @GlobalTheory.NormSum.TraceInt.hYY_integral | exact GlobalTheory.NormSum.TraceInt.hYY_integral | (intros; apply GlobalTheory.NormSum.TraceInt.hYY_integral <;> assumption)
end
end
