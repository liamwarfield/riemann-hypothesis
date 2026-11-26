module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChKerCCongr
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPeriodMatrixIntVecContinuousBoundary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPeriodMatrixIntVecContinuousBoundary
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PeriodFrame

theorem combMat_mulVec_eq_sum {g r : ℕ} (l : Fin r → Fin g → ℂ) (φ : Matrix (Fin g) (Fin r) ℚ) (v : Fin g → ℂ) :
    combMat l φ *ᵥ v = ∑ m, (∑ i, (φ i m : ℂ) * v i) • l m := by
  ext k
  simp only [combMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem exists_nat_mul_int {r : ℕ} (u : Fin r → ℚ) : ∃ N : ℕ, 0 < N ∧ ∀ m, ∃ k : ℤ, (N : ℚ) * u m = k := by
  refine ⟨∏ m, (u m).den, Finset.prod_pos fun m _ => (u m).den_pos, fun m => ?_⟩
  refine ⟨(∏ j ∈ Finset.univ.erase m, (u j).den : ℕ) * (u m).num, ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ m)]
  push_cast
  rw [_root_.mul_assoc, _root_.mul_comm ((u m).den : ℚ), Rat.mul_den_eq_num]

end GlobalTheory.PeriodFrame

theorem GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous : ∀ (n a g r₀ r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (rk D : ℕ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → Mᵀ = -M → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) → 0 < D → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → ∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 1) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).mulVec (fun j => (v j : ℂ)) = F (logExp a s) := by
  intro n a g r₀ r K ζ lam M c α φ rk D hK hζa hζK hζ0 hlam hζc hM hφ hrk hD hdet v hv hsupp F hF heq
  set u : Fin r → ℚ := fun m => ∑ i, φ i m * (v i : ℚ) with hu
  obtain ⟨N, hN0, hNint⟩ := GlobalTheory.PeriodFrame.exists_nat_mul_int u
  choose kk hkk using hNint
  set W : (Fin n → ℂ) → Fin g → ℂ := fun z => ((N : ℂ) / D) • (GlobalTheory.PeriodFrame.combMat (ζ z) α *ᵥ F z) with hW
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hζc0 : ContinuousAt ζ 0 := (hζa 0 h0).continuousAt
  have hFc0 : ContinuousAt F 0 := hF.continuousAt (Metric.isOpen_ball.mem_nhds h0)
  have hWc : ContinuousAt W 0 := by
    have h1 : ∀ m k, ContinuousAt (fun z => ζ z m k) 0 := fun m k =>
      (continuous_apply k).continuousAt.comp ((continuous_apply m).continuousAt.comp hζc0)
    have h2 : ∀ i, ContinuousAt (fun z => F z i) 0 := fun i => (continuous_apply i).continuousAt.comp hFc0
    refine continuousAt_pi.2 fun k => ?_
    simp only [hW, GlobalTheory.PeriodFrame.combMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hlK : ∀ᶠ b in 𝓝 (0 : Fin n → ℂ), ∀ j, ζ b j ∈ K b := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with b hb using hζK b hb
  have hev := IsLatFam.eventually_intComb hK h0 hζc0 hlK hζ0 (W 0)
  have ht : Filter.Tendsto (fun z => (z, W z)) (𝓝 (0 : Fin n → ℂ)) (𝓝 ((0 : Fin n → ℂ), W 0)) :=
    (continuousAt_id.prodMk hWc).tendsto
  have hev2 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧
      (W z ∈ K z → ∃ m : Fin r₀ → ℤ, W z = ∑ j, m j • ζ z j) :=
    Filter.Eventually.and (Metric.isOpen_ball.mem_nhds h0 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1)
      (ht.eventually hev)
  set s : ℝ → Fin n → ℂ := fun R k => if (k : ℕ) < a then -(R : ℂ) else 0 with hs
  have hsdom : ∀ R : ℝ, 0 < R → s R ∈ logDom n a := by
    intro R hR k
    by_cases hk : (k : ℕ) < a
    · simp [hs, hk, hR]
    · simp [hs, hk]
  have hslim : Filter.Tendsto (fun R => logExp a (s R)) Filter.atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun k => ?_
    by_cases hk : (k : ℕ) < a
    · simp only [logExp, hs, hk, if_true, Pi.zero_apply]
      have h3 : Filter.Tendsto (fun R : ℝ => ((Real.exp (-R) : ℝ) : ℂ)) Filter.atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
      simpa [Complex.ofReal_exp] using h3
    · simp [logExp, hs, hk]
  obtain ⟨R, ⟨hzb, hzK⟩, hR0⟩ := ((hslim.eventually hev2).and (Filter.eventually_gt_atTop 0)).exists
  have hs0 := hsdom R hR0
  have he := heq (s R) hs0 hzb
  have hWz : W (logExp a (s R)) = ∑ m, ((kk m : ℤ) : ℂ) • lam (s R) m := by
    have hP := hdet (s R) hs0
    have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hsm : ∀ (c : ℂ) (A : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ), (c • A) *ᵥ x = c • (A *ᵥ x) := by
      intro c A x; ext p; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]
    simp only [hW]
    rw [← he, GlobalTheory.PeriodFrame.perTau, Matrix.mulVec_mulVec, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hP, Matrix.one_mul, hsm, smul_smul,
      GlobalTheory.PeriodFrame.combMat_mulVec_eq_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
    congr 1
    have h4 := congrArg (Rat.cast : ℚ → ℂ) (hkk m)
    push_cast [hu] at h4
    rw [← h4]
    field_simp

  have hWK : W (logExp a (s R)) ∈ K (logExp a (s R)) :=
    ((hlam (s R) hs0).2 _).2 ⟨kk, by rw [hWz]; exact Finset.sum_congr rfl fun m _ => Int.cast_smul_eq_zsmul ℂ _ _⟩
  obtain ⟨mm, hmm⟩ := hzK hWK
  have hcomb : ∑ j, kk j • lam (s R) j = ∑ j, (∑ i, mm i * c i j) • lam (s R) j := by
    have e1 : ∑ j, kk j • lam (s R) j = W (logExp a (s R)) := by
      rw [hWz]; exact Finset.sum_congr rfl fun m _ => (Int.cast_smul_eq_zsmul ℂ _ _).symm
    rw [e1, hmm]
    simp only [hζc (s R) hs0, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hkc : ∀ j, kk j = ∑ i, mm i * c i j := by
    have hli := (hlam (s R) hs0).1
    have h5 := Fintype.linearIndependent_iff.1 hli (fun j => ((kk j - ∑ i, mm i * c i j : ℤ) : ℝ)) (by
      simp only [Int.cast_smul_eq_zsmul, sub_smul, Finset.sum_sub_distrib, hcomb, sub_self])
    intro j
    have h6 := h5 j
    have h7 : kk j - ∑ i, mm i * c i j = 0 := by exact_mod_cast h6
    exact sub_eq_zero.1 h7
  set cq := c.map (Int.cast : ℤ → ℚ) with hcq
  set Mq := M.map (Int.cast : ℤ → ℚ) with hMq
  set vq : Fin g → ℚ := fun i => (v i : ℚ) with hvq
  set mq : Fin r₀ → ℚ := fun i => (mm i : ℚ) with hmq
  have hvec : Matrix.vecMul ((N : ℚ) • vq) φ = Matrix.vecMul mq cq := by
    ext j
    have h6 := hkk j
    rw [hkc j] at h6
    push_cast at h6
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, hcq, hvq, hmq, Matrix.map_apply]
    rw [← h6, hu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hskew : cq * (Mq * (α * cq)ᵀ) = -((α * cq) * Mq * cqᵀ)ᵀ := by
    have hMt : Mqᵀ = -Mq := by
      ext i j
      have h := congrFun (congrFun hM i) j
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
      simp [hMq, Matrix.transpose_apply, h]
    rw [Matrix.transpose_mul (α * cq * Mq), Matrix.transpose_transpose, Matrix.transpose_mul (α * cq) Mq, hMt]
    simp [Matrix.neg_mul, Matrix.mul_neg]
  have hfin := congrArg (fun x => Matrix.vecMul x (Mq * (α * cq)ᵀ)) hvec
  simp only [Matrix.vecMul_vecMul] at hfin
  rw [show φ * (Mq * (α * cq)ᵀ) = 1 by rw [← Matrix.mul_assoc, hφ], Matrix.vecMul_one, hskew] at hfin
  apply hv
  funext i
  by_cases hi : i.val < rk
  · have h7 := congrFun hfin i
    have h8 : Matrix.vecMul mq (-((α * cq) * Mq * cqᵀ)ᵀ) i = 0 := by
      simp only [Matrix.vecMul, dotProduct, Matrix.neg_apply, Matrix.transpose_apply, hrk i hi, neg_zero, mul_zero,
        Finset.sum_const_zero]
    rw [h8] at h7
    simp only [Pi.smul_apply, smul_eq_mul, hvq] at h7
    have hN : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
    have h9 := (mul_eq_zero.1 h7).resolve_left hN
    simpa using h9
  · exact hsupp i (not_lt.1 hi)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPeriodMatrixIntVecContinuousBoundaryStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_periodMatrix_intVec_continuous_boundary : ∀ (n a g r₀ r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (rk D : ℕ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → Mᵀ = -M → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) → 0 < D → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → ∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 1) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).mulVec (fun j => (v j : ℂ)) = F (logExp a s) := by
  first | exact @GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous | exact GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous | (intros; apply GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

theorem exists_moved {K T : Type} [Field K] {σ : K →+* ℂ} {n : ℕ} {A : T → Type} [∀ t, AddCommGroup (A t)] [∀ t, Module ℂ (A t)]
    {V : Type} [AddCommGroup V] [Module ℂ V] {a b : T} (h : a = b) (E : V ≃ₗ[ℂ] A b) (j : (Fin n → K) →ₛₗ[σ] A a)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ j' : (Fin n → K) →ₛₗ[σ] V, (∀ y, j' y = E.symm (h ▸ j y)) ∧ (LinearIndependent ℂ fun i => j' (Pi.single i 1)) ∧
      Submodule.span ℂ (Set.range fun i => j' (Pi.single i 1)) = ⊤ := by
  subst h
  refine ⟨E.symm.toLinearMap.comp j, fun _ => rfl, li.map' E.symm.toLinearMap E.symm.ker, ?_⟩
  have := congrArg (Submodule.map E.symm.toLinearMap) sp
  rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at this

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem exists_read_fam {s : ℕ} (hOk : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.Ok s)
    (σ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok) {T : Type} {A : T → Type} [∀ t, AddCommGroup (A t)] [∀ t, Module ℂ (A t)]
    {V : Type} [AddCommGroup V] [Module ℂ V] {b : T} (E : V ≃ₗ[ℂ] A b) (tup : TupF TU → T) (h0 : tup (mu0F TU) = b)
    (inj : Function.Injective tup)
    (j : ∀ t : TupF TU, (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlDim
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r P.grp P.chr) → X.K) →ₛₗ[σ] A (tup t))
    (li : ∀ t, LinearIndependent ℂ fun i => j t (Pi.single i 1))
    (sp : ∀ t, Submodule.span ℂ (Set.range fun i => j t (Pi.single i 1)) = ⊤)
    (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3) :
    ∃ ι : V ≃ₗ[ℂ] (Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ),
      (∀ (t : TupF TU) (ht : tup t = b) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅) y,
        ∃ (F' : (mtildeKGSD W Ch sel t.1).EqFun) (hm : F'.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun),
          HEq ((mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F')
            (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm
              ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
                (lvlIdem P.grp P.chr)).mulVec y)) ∧
          ι (E.symm (ht ▸ j t y)) = zOfRow W Ch sel t.1 hQ P σ hM ⟨F'.1, hm⟩) ∧
      ∀ (t : TupF TU) (ht : tup t = b) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅)
        (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K),
        ∃ hm : (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs t F).1.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun,
          ι (E.symm (ht ▸ j t ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r P.grp P.chr *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F))) =
            zOfRow W Ch sel t.1 hQ P σ hM ⟨_, hm⟩ := by
  have hQ0 := Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := X) (S := S) sel
  obtain ⟨j', hj, li', sp'⟩ := exists_moved (A := A) h0 E (j (mu0F TU)) (li _) (sp _)
  obtain ⟨ι, hι⟩ := exists_read W Ch sel (mu0F TU).1 hX P hQ0 σ hM j' li' sp'
  refine ⟨ι, fun t e hQ y => ?_, fun t e hQ F => ?_⟩
  · obtain rfl : t = mu0F TU := inj (e.trans h0.symm)
    obtain ⟨F', hm, e1, e2⟩ := hι y
    exact ⟨F', hm, heq_of_eq e1, (congrArg ι (hj y)).symm.trans e2⟩
  · obtain rfl : t = mu0F TU := inj (e.trans h0.symm)
    obtain ⟨F', hm, e1, e2⟩ := hι ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).S.lvlPr
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).r P.grp P.chr *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F)
    have e3 : F' = (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs (mu0F TU) F).1 :=
      ((mtildeKGSD W Ch sel (mu0F TU).1).res (mtildeKOk W Ch sel (mu0F TU).1 hX)).injective
        (e1.trans (evC_res_lvl W Ch sel hX v0 TU Xg S0 xiVal trIv P hOk Zs (mu0F TU) F).symm)
    subst e3
    exact ⟨hm, (congrArg ι (hj _)).symm.trans e2⟩

end Gen

section Main

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem tup_heq (ht : I.IsTw) (U : Set I.ι) (X' : Fields) (hx : X' = B.fields) (Pr : Primes X')
    (sel : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S : Set ℕ) (tup : I.ι → Tup X'.F X'.E X'.K S)
    (cst : ∀ a, LocCst X' (rowSG Pr sel (tup a))) (idx : ∀ a, ChIdx X' Pr B.R (QE sel (tup a : Chr X'.F X'.E X'.K)))
    (h1 : HEq Pr (B.primes X)) (h2 : HEq sel I.sel) (h3 : S = I.S) (h4 : HEq tup I.tup) (h5 : HEq cst I.cst) (h6 : HEq idx I.idx) :
    HEq (fun t : TupU I U => t.1) (fun t => tup (ixOf I U t)) ∧ HEq (fun t : TupU I U => cstT I t.1) (fun t => cst (ixOf I U t)) ∧
      HEq (fun t : TupU I U => idxT I t.1) (fun t => idx (ixOf I U t)) := by
  subst hx h3
  cases h1
  cases h2
  cases h4
  cases h5
  cases h6
  refine ⟨heq_of_eq (funext fun t => (tup_ixOf I t).symm), Function.hfunext rfl fun t t' e => ?_, Function.hfunext rfl fun t t' e => ?_⟩
  · cases e
    rw [← cstT_tup ht, tup_ixOf]
  · cases e
    rw [← idxT_tup ht, tup_ixOf]

variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
  {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
  {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX}

theorem iT_heq {t : KerEntTied ex} (hS : I.StdKer l Z t) (τ : (I.rec7 l Z).what₂.Tau) : HEq (t.seam.iT.symm τ) τ := by
  have key : ∀ (X' : Fields) (_ : X' = B.fields) (s : Seam (I.rec7 l Z) X'),
      HEq s (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) → HEq (s.iT.symm τ) τ := by
    intro X' hx s hs
    subst hx
    cases hs
    rfl
  exact key _ hS.X_eq _ hS.seam

abbrev colRecK (t : KerEntTied ex) : ColRec3 B.fields (famC I hX U Xg tr) (lev1 I) (chr1 I) :=
  colRecC h hp l Z ht hJ t.χ (ker_chi_eq I l Z t) hX U Xg tr

section Pins

variable {h hp l Z ht hJ hX U Xg tr} {hOk : (famC I hX U Xg tr).fam3.Ok3 1} {T : Formalism.L2.TiedDataSK ex} {hS : I.StdKer l Z T.ker}
  {Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)}
  {R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp}
  {htup : R.I.tup = ixOf I U} {hw : ∀ u, R.I.wU u = u}

end Pins

end Main


end GlobalTheory.Mem.R3.SelC

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.SelC

theorem pack_heq {D : D7} (p q : Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
      (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D) (_ : Algebra C.Q.c.F D.what₂.LL)
      (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3), G0 R.Pg D.R.r ≃* G0g D.nd) (e : p = q) :
    letI := p.2.1; letI := p.2.2.1; letI := p.2.2.2.2.2.2.2.2.1; letI := q.2.1; letI := q.2.2.1; letI := q.2.2.2.2.2.2.2.2.1
    (p.1 = q.1 ∧ HEq p.2.1 q.2.1 ∧ p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2.1 = q.2.2.2.2.1 ∧ p.2.2.2.2.2.1 = q.2.2.2.2.2.1 ∧
      HEq p.2.2.2.2.2.2.1 q.2.2.2.2.2.2.1) ∧
    (HEq p.2.2.2.2.2.2.2.2.2.2.1.P0 q.2.2.2.2.2.2.2.2.2.2.1.P0 ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.ψ0 q.2.2.2.2.2.2.2.2.2.2.1.ψ0 ∧
      HEq p.2.2.2.2.2.2.2.2.2.2.1.P1 q.2.2.2.2.2.2.2.2.2.2.1.P1 ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.ψ1 q.2.2.2.2.2.2.2.2.2.2.1.ψ1 ∧
      HEq p.2.2.2.2.2.2.2.2.2.2.1.Dc q.2.2.2.2.2.2.2.2.2.2.1.Dc ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.Sp q.2.2.2.2.2.2.2.2.2.2.1.Sp) ∧
    HEq (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1) (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1) ∧
    HEq (p.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1))
      (q.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)) ∧
    HEq (p.2.2.2.2.2.2.2.2.2.2.1.Sp (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1))
      (q.2.2.2.2.2.2.2.2.2.2.1.Sp (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)) ∧
    (p.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1)).Mem =
      (q.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)).Mem := by
  subst e
  exact ⟨⟨rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl⟩, ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩, HEq.rfl, HEq.rfl, HEq.rfl, rfl⟩

theorem heq_app {A M M' : Type} (e : M = M') {f : A → M} {g : A → M'} (h : HEq f g) (u : A) : HEq (f u) (g u) := by
  subst e
  cases h
  rfl

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}


variable {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}




attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.Mem.R3.SelC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsRationalCombinationFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsRationalCombinationFrame
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeriodFrame

theorem frame_hermForm_sum_left {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : Fin n → ℂ)
    (E : Fin n → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
  unfold hermForm
  rw [sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul]

theorem frame_hermForm_sum_right {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : Fin n → ℂ)
    (E : Fin n → Fin g → ℂ) (z : Fin g → ℂ) :
    hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
  have hs : star (∑ i, c i • E i) = ∑ i, star (c i) • star (E i) := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext k
    simp [mul_comm]
  simp only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem frame_col {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) (i : Fin g) :
    (fun k => combMat l ε k i) = ∑ m, (ε i m : ℂ) • l m := by
  funext k
  simp [combMat, Finset.sum_apply]

theorem frame_im_hermForm {g r : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ)
    (l : Fin r → Fin g → ℂ) (hM : ∀ i j, (hermForm Hm (l i) (l j)).im = M i j)
    (A B : Matrix (Fin g) (Fin r) ℚ) (i k : Fin g) :
    (hermForm Hm (fun x => combMat l A x i) (fun x => combMat l B x k)).im
      = (((A * M.map (Int.cast : ℤ → ℚ) * Bᵀ) i k : ℚ) : ℝ) := by
  rw [frame_col, frame_col, frame_hermForm_sum_left]
  simp only [frame_hermForm_sum_right, Finset.mul_sum, Complex.im_sum]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  push_cast
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  simp [Complex.mul_im, hM]
  ring

theorem riemann_relations_frame : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), 0 < D → Hm.IsHermitian → (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ l → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ε * M.map (Int.cast : ℤ → ℚ) * εᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * εᵀ = 1 → IsUnit (GlobalTheory.PeriodFrame.combMat l ε).det ∧ ((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).IsSymm ∧ (((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).PosDef ∧ (GlobalTheory.PeriodFrame.combMat l ε)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat l ε)ᵀᴴ = ((D : ℝ) : ℂ) • ((((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).map Complex.ofReal)⁻¹ := by
  intro g r Hm M l ε φ D hD hH hpos _hl hM hεε hφφ hφε
  set P := combMat l ε with hP
  set Q := combMat l φ with hQ
  set E : Fin g → Fin g → ℂ := fun i k => P k i with hE
  set F : Fin g → Fin g → ℂ := fun j k => Q k j with hF
  have hEE : ∀ i j, (hermForm Hm (E i) (E j)).im = 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM ε ε i j
    rw [hεε] at h
    simpa using h
  have hFF : ∀ i j, (hermForm Hm (F i) (F j)).im = 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM φ φ i j
    rw [hφφ] at h
    simpa using h
  have hFE : ∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM φ ε i j
    rw [hφε] at h
    change (hermForm Hm (F i) (E j)).im = _ at h
    rw [h]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hind : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have h1 : hermForm Hm (F j) (∑ i, ((a i : ℝ) : ℂ) • E i) = 0 := by
      have hs : (∑ i, ((a i : ℝ) : ℂ) • E i) = ∑ i, a i • E i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ext k
        simp
      rw [hs, ha]
      simp [hermForm]
    rw [frame_hermForm_sum_right] at h1
    have h2 := congrArg Complex.im h1
    simpa [Complex.im_sum, Complex.mul_im, hFE] using h2
  have hdet : P.det ≠ 0 := by
    have h := GlobalTheory.det_ne_zero_of_real_indep_isotropic g Hm E hpos hind hEE
    exact h
  have hU : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  set τ := P⁻¹ * Q with hτ
  have hPτ : P * τ = Q := by
    rw [hτ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have hFτ : ∀ j, F j = ∑ i, τ i j • E i := by
    intro j
    funext k
    have h := congrFun (congrFun hPτ k) j
    simp only [Matrix.mul_apply] at h
    simp only [hF, hE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨hposτ, hsymτ⟩ := GlobalTheory.riemann_relations_period_matrix g g Hm E F τ hH hpos hFτ hEE hFE
  have hτs : ∀ i j, τ i j = τ j i := fun i j => by
    have h := hsymτ i j
    rw [hFF] at h
    simpa [sub_eq_zero] using h
  set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hY
  set a : Matrix (Fin g) (Fin g) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hEE])
  have hYA : Y * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hFτ j, frame_hermForm_sum_left] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero, zero_add] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hY, Matrix.map_apply]
    rw [hτs j i]
  have hTim : ((D : ℂ) • τ).map Complex.im = (D : ℝ) • Y := by
    ext i j
    simp [hY]
  have hTre : (((D : ℂ) • τ).map Complex.im).map Complex.ofReal = (D : ℂ) • Y.map Complex.ofReal := by
    rw [hTim]
    ext i j
    simp
  have hYAc : Y.map Complex.ofReal * a.map Complex.ofReal = 1 := by
    ext i k
    have h := congrFun (congrFun hYA i) k
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hinv : ((((D : ℂ) • τ).map Complex.im).map Complex.ofReal)⁻¹ = (D : ℂ)⁻¹ • a.map Complex.ofReal := by
    apply Matrix.inv_eq_right_inv
    rw [hTre, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hDne, one_smul, hYAc]
  refine ⟨hU, ?_, ?_, ?_⟩
  · show ((D : ℂ) • τ)ᵀ = (D : ℂ) • τ
    ext i j
    simp only [Matrix.transpose_apply, Matrix.smul_apply]
    rw [hτs j i]
  · rw [Matrix.posDef_iff_dotProduct_mulVec, hTim]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, star_trivial, hY, Matrix.map_apply]
      rw [hτs j i]
    · have e : star x ⬝ᵥ (((D : ℝ) • Y) *ᵥ x) = (D : ℝ) * (∑ i, ∑ j, (x i : ℂ) * τ i j * (x j : ℂ)).im := by
        simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Complex.im_sum,
          Finset.mul_sum, hY, Matrix.map_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [Complex.mul_im]
        ring
      rw [e]
      exact mul_pos (by exact_mod_cast hD) (hposτ x hx)
  · rw [hinv, smul_smul, Complex.ofReal_natCast, mul_inv_cancel₀ hDne, one_smul]
    ext i j
    rw [Matrix.map_apply, ← hAr i j]
    simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.conjTranspose_apply, Pi.star_apply, Matrix.map_apply, hE, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    ring

end GlobalTheory.PeriodFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsRationalCombinationFrameStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannRelations_rationalCombinationFrame : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), 0 < D → Hm.IsHermitian → (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ l → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ε * M.map (Int.cast : ℤ → ℚ) * εᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * εᵀ = 1 → IsUnit (GlobalTheory.PeriodFrame.combMat l ε).det ∧ ((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).IsSymm ∧ (((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).PosDef ∧ (GlobalTheory.PeriodFrame.combMat l ε)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat l ε)ᵀᴴ = ((D : ℝ) : ℂ) • ((((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).map Complex.ofReal)⁻¹ := by
  first | exact @GlobalTheory.PeriodFrame.riemann_relations_frame | exact GlobalTheory.PeriodFrame.riemann_relations_frame | (intros; apply GlobalTheory.PeriodFrame.riemann_relations_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartLevelCharactersRational
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartLevelCharactersRational
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

noncomputable section

namespace GlobalTheory.ChiRatStd

open GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT


set_option maxHeartbeats 1600000 in
theorem chiRatAll_of_reads {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
    {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (L : (I.stp u a i).Cl → Submodule (𝓞 B.host.E) (B.sp.X i).V) (hL : L = I.latAt u a i)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (L c.1)))
    (k : Ch → TC.GA B (B.R.N i))
    (hR : I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (hfin : ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) (β : Ch) :
    Formalism.L2.G.Cmp.ChiRatAll (K β).lev B.embLL := by
  subst hL
  obtain ⟨c, rfl⟩ := hR.onto β
  intro κ
  have hF : ChiFin I l Z (K (chOf c)).lev := by
    obtain ⟨n, hn, h⟩ := hfin (chOf c)
    exact ⟨n, hn, fun κ _ => h κ⟩
  obtain ⟨x, hx, ⟨q, hq⟩, -⟩ := GlobalTheory.T.exists_levelElement_same_character_near_bad I hOk hP l Z u a i hi bad Ch chOf K k hR c hF κ
  obtain ⟨κ', hg, hq', -⟩ := (hR.lev c x.1 q hq).1 x.2
  have hc := hR.chr c x κ' hg (by rw [hq']; exact hq)
  exact ⟨_, by rw [← hx]; exact hc.symm⟩


set_option maxHeartbeats 1600000 in
theorem chiRatAll_twChart : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch),
    V4.MuIsW (w.st Z) f T Wt w.I.xi →
    ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
    ∀ (u : (w.D Z).what₂.Word) (μ : (w.D Z).what₂.Tup) (hμ : μ ≠ (w.D Z).what₂.mu0) (j : ℕ) (hj : j + 1 ≤ (w.D Z).R.m)
      (β : tt.ch.Ch u μ (j + 1)),
      Formalism.L2.G.Cmp.ChiRatAll (tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (w.D Z).what₂.embLL := by
  intro K B f T w _ _ _ Z t Wt nch n _ tt hstd u μ hμ j hj β
  obtain ⟨k, hR⟩ := hstd.1.reads u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  exact chiRatAll_of_reads w.I w.ok w.pins w.l Z u μ (j + 1) hj _ _ _ (hstd.1.lat u μ (j + 1))
    (fun β => tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β) k hR
    (fun β => tt.forms.chi_fin u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β) β

end GlobalTheory.ChiRatStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartLevelCharactersRationalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chain_chart_level_characters_rational : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch),
    V4.MuIsW (w.st Z) f T Wt w.I.xi →
    ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
    ∀ (u : (w.D Z).what₂.Word) (μ : (w.D Z).what₂.Tup) (hμ : μ ≠ (w.D Z).what₂.mu0) (j : ℕ) (hj : j + 1 ≤ (w.D Z).R.m)
      (β : tt.ch.Ch u μ (j + 1)),
      Formalism.L2.G.Cmp.ChiRatAll (tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (w.D Z).what₂.embLL := by
  first | exact @GlobalTheory.ChiRatStd.chiRatAll_twChart | exact GlobalTheory.ChiRatStd.chiRatAll_twChart | (intros; apply GlobalTheory.ChiRatStd.chiRatAll_twChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationImageBoundedDomainEqOpenPart
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationImageBoundedDomainEqOpenPart
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

theorem GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) = ptsIn X.str (σ.comp e.toRingHom) (openPart j) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  obtain ⟨hjo, hfj, -⟩ := hL
  have hm : Mono j := inferInstance
  have hinj : Function.Injective (cxOf e σ hj) := fun a b h =>
    Subtype.ext ((cancel_mono j).1 (congrArg Subtype.val h))
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  have hmem : ∀ y : CxPts X.str (σ.comp e.toRingHom),
      y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
    intro y
    constructor
    · intro h hb
      have h1 := h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
      exact h1 hb
    · intro h pt _
      obtain rfl : pt = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      exact h
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨x, hx, hxv⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) (Nat.le_add_right _ _)
      (U.X k).Ψ (Equiv.refl _) hp0 (unflat v) hv
    have hv' : v = flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x) := by
      rw [hxv]; rfl
    rw [hmem, hv', hψ ⟨x, hx⟩]
    exact not_liesIn_cxPt (Z := T.Z) _
  · intro hy
    rw [hmem] at hy
    obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β T.Z ℂ σ (cxOf e σ hj y).1 (cxOf e σ hj y).2
    obtain ⟨q, hq, -⟩ := exists_frPt_cxPt_of_eigFrame E H Dw l Xo c O β T.Z σ (cxOf e σ hj y) hy g
    obtain ⟨k', x', t, hB⟩ := hU.2.2.1 q
    have hq' : cxPt T.Z (U.un k' x') = cxOf e σ hj y := (cxPt_congr hB.1.symm).trans hq
    have hyχ : y.1 ≫ j ≫ genStr T.Z = spMap σ := by
      have h2 := (cxOf e σ hj y).2
      simpa [cxOf, Category.assoc] using h2
    obtain ⟨p, hp⟩ := GlobalTheory.FlagCptBase.exists_pt_over_base E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ k X j hjo hj f hfj
      (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ)
      (fun i K _ χ p h => GlobalTheory.CarryAll.carry_some E H Dw l Xo c O β T.Z F e (Φ.C i) K χ p h) ℂ σ y.1 hyχ
    let s : Sp (CAt σ) := IsLocalRing.closedPoint ℂ
    obtain ⟨w', hw'⟩ := Φ.label k' x' s
    have hkk : k = k' := by
      refine GlobalTheory.FlagCptBase.eq_of_apply_eq Φ (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ)
        (fun i K _ χ p h => GlobalTheory.CarryAll.carry_some E H Dw l Xo c O β T.Z F e (Φ.C i) K χ p h) (p s) w' ?_
      rw [hw']
      have h3 : (GlobalTheory.AllWt.ptF (U.un k' x') ≫ T.Z.jQ) = (cxOf e σ hj y).1 := congrArg Subtype.val hq'
      rw [h3]
      show (Φ.C k).π (p s) = (y.1 ≫ j) s
      rw [← hp, ← hfj]
      rfl
    subst hkk
    refine ⟨flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x'.1), ?_, hinj ?_⟩
    · exact GlobalTheory.TrueCx.domPt_mem (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) hp0 x'.2
    · rw [hψ x', hq']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationImageBoundedDomainEqOpenPartStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_image_boundedDomain_eq_openPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) = ptsIn X.str (σ.comp e.toRingHom) (openPart j) := by
  first | exact @GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart | exact GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart | (intros; apply GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLineIffEigenSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanTie

section Core

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem mem_goodL_iff_iotaR (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hU : R.toRealDat.LUnif) (hW : R.toRealDat.models_HW)
    (hidem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g))
    (hψ : LvlPsi R F cG θ) (j : ℕ) (v : (ratDatR R cG kKs hk).WL j) :
    v ∈ goodL D (ratDatR R cG kKs hk) θ j ↔
      GlobalTheory.EigSpanDesc.iotaR R (idxOf D j) v ∈ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j) := by
  have hinj : Function.Injective fun x : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x) := by
    refine (hW _ _).1.comp ((injective_iff_map_eq_zero ((R.FW (idxOf D j)).j (sg0 D A3.A))).2 fun x hx => ?_)
    by_contra hne
    exact ((hU _ _).1 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)).ne_zero 0 hx
  have hact : ∀ (g : G) (x : Fin (R.nW (idxOf D j)) → D.what₂.LL),
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A)
        ((((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g x)) =
      postOn _ (Links.actL (Wc D (idxOf D j)) (R.βW (idxOf D j)) (R.datWp (idxOf D j) R.triv) (R.eG g))
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x)) := fun g x => by
    rw [map_smulₛₗ, map_smul, (hU _ _).2.2, smul_smul, ← map_mul, inv_mul_cancel₀ (Units.ne_zero _), map_one, one_smul]
  have hactL : ∀ (g : G) (x : (ratDatR R cG kKs hk).WL j),
      GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j ((R.eG.trans cG) g) x =
        (((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g x := fun g x => by
    show ((((R.FW (idxOf D j)).chi ((R.eG.trans cG).symm ((R.eG.trans cG) g)) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (R.FW (idxOf D j)).ρ ((R.eG.trans cG).symm ((R.eG.trans cG) g)) x = _
    rw [MulEquiv.symm_apply_apply]
  have hsum : ∀ x : (ratDatR R cG kKs hk).WL j,
      (∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j g) x =
        ∑ g : G, (idemOf A3.A.X).coeff g •
          ((((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g x) := fun x => by
    rw [← finsum_comp_equiv (R.eG.trans cG).toEquiv, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hc : ((D.nexp.eLL0 ((R.eG.trans cG) g) : ↥D.LL0) : D.what₂.LL) = (idemOf A3.A.X).coeff g :=
      D.what₂.embLL.injective ((D.nStage_trivialCharacter_coeff_eq _).trans (hidem g).symm)
    rw [LinearMap.smul_apply, ← hactL g x, ← hc]
    rfl
  have hsmul : ∀ (c : D.what₂.LL) (x : Fin (R.nW (idxOf D j)) → D.what₂.LL),
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (c • x)) =
        sg0 D A3.A c • (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x) := fun c x => by
    rw [map_smulₛₗ, map_smul]
  have hact2 : ∀ (g : G) (x : (ratDatR R cG kKs hk).WL j),
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A)
        (GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j ((R.eG.trans cG) g) x)) =
      postOn _ (Links.actL (Wc D (idxOf D j)) (R.βW (idxOf D j)) (R.datWp (idxOf D j) R.triv) (R.eG g))
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x)) := fun g x =>
    (congrArg (fun y : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) y)) (hactL g x)).trans (hact g x)
  have hchain : (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A)
      (∑ g : G, (idemOf A3.A.X).coeff g •
        ((((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g v))) =
      ∑ g : G, sg0 D A3.A ((idemOf A3.A.X).coeff g) •
        postOn _ (Links.actL (Wc D (idxOf D j)) (R.βW (idxOf D j)) (R.datWp (idxOf D j) R.triv) (R.eG g))
          ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) v)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smulₛₗ, map_smul]
    exact congrArg _ (hact g v)
  rw [goodL, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, one_smul]
  change _ ↔ (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) v) ∈
    R.toRealDat.Wat (idxOf D j) (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))
  rw [GlobalTheory.LevelForms.mem_wat_iff R.toRealDat F.lv2 hU hW false]
  refine and_comm.trans (and_congr ?_ ?_)
  · constructor
    · intro h p
      have hu : (R.eG.trans cG) (p : G) ∈ Formalism.IndefR.NX.U D.nd := (hψ.1 p).1 p.2
      have h1 : GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j ((R.eG.trans cG) (p : G)) v =
          (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) • v :=
        Module.End.mem_eigenspace_iff.1 (h ⟨_, hu⟩)
      rw [hψ.2 ⟨p.1, p.2⟩ hu] at h1
      exact (hact2 p v).symm.trans ((congrArg (fun y : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
        (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) y)) h1).trans (hsmul _ v))
    · intro h u
      obtain ⟨u, hu⟩ := u
      obtain ⟨g, rfl⟩ := (R.eG.trans cG).surjective u
      have hg : g ∈ F.P0 := (hψ.1 g).2 hu
      have hp := hψ.2 ⟨g, hg⟩ hu
      refine Module.End.mem_eigenspace_iff.2 (hinj ?_)
      refine (hact2 g v).trans ((h ⟨g, hg⟩).trans ?_)
      rw [hp]
      exact (hsmul _ v).symm
  · rw [hsum]
    exact ⟨fun h => hchain.symm.trans (congrArg (fun y : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
        (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) y)) h),
      fun h => hinj (hchain.trans h)⟩

end Core


end GlobalTheory.EigSpanTie

end
end
