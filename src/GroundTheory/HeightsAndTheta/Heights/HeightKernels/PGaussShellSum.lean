module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
public import GroundTheory.GlobalFields.TateThesis.LatticePoisson
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShellSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

noncomputable section

namespace PGaussShellSum

theorem inv_one_sub_exp_neg_one_le_two : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have he : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hlt : 0 < 1 - Real.exp (-1) := by linarith
  rw [inv_le_comm₀ hlt (by norm_num)]
  linarith

theorem exp_neg_nat (m : ℕ) : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end PGaussShellSum


open PGaussShellSum in
theorem GaussShellSum.proof (hS : GaussShell.Statement) : GaussShellSum.Statement := by
  intro n hn Λ δ hδ hmin
  set K : ℝ := gaussShellConst n * (1 + 1 / δ) ^ n with hK
  let f : Λ → ℝ := fun μ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  have hf : 0 ≤ f := fun μ => (Real.exp_pos _).le
  have hK0 : 0 ≤ K := by
    have hc : 0 ≤ gaussShellConst n := by unfold gaussShellConst; positivity
    have : 0 ≤ 1 + 1 / δ := by positivity
    positivity
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1) < 1 := by
    exact Real.exp_lt_one_iff.2 (by norm_num)
  have hgeo : Summable fun j : ℕ => K * Real.exp (-1) ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left K
  have hbound : ∀ u : Finset Λ, ∑ μ ∈ u, f μ ≤ 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by
    intro u
    let fl : Λ → ℕ := fun μ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to (g := fl) (t := u.image fl)
      (fun μ hμ => Finset.mem_image_of_mem fl hμ) f]
    calc ∑ j ∈ u.image fl, ∑ μ ∈ u with fl μ = j, f μ
        ≤ ∑ j ∈ u.image fl, K * Real.exp (-1) ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← exp_neg_nat]
          exact hS n hn Λ δ hδ hmin u j
      _ ≤ ∑' j : ℕ, K * Real.exp (-1) ^ j :=
          hgeo.sum_le_tsum _ (fun j _ => by positivity)
      _ = K * (1 - Real.exp (-1))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      _ ≤ K * 2 := mul_le_mul_of_nonneg_left inv_one_sub_exp_neg_one_le_two hK0
      _ = 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by rw [hK]; ring
  exact ⟨summable_of_sum_le hf hbound, Real.tsum_le_of_sum_le hf hbound⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric

namespace PGaussPacking

theorem pairwiseDisjoint_balls {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ : ℝ}
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) :
    (s : Set (EuclideanSpace ℝ (Fin n))).PairwiseDisjoint (fun x => ball x (δ / 2)) := by
  intro x hx y hy hxy
  apply ball_disjoint_ball
  rw [dist_eq_norm]
  linarith [hsep x hx y hy hxy]

theorem biUnion_balls_subset {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ r : ℝ}
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) :
    (⋃ x ∈ s, ball x (δ / 2)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2) := by
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨x, hx, hz⟩ := hz
  rw [mem_ball, dist_eq_norm] at hz ⊢
  rw [sub_zero]
  calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
    _ < δ / 2 + r := by linarith [hs x hx]
    _ = r + δ / 2 := by ring

end PGaussPacking


open PGaussPacking in
theorem GaussPacking.proof : GaussPacking.Statement := by
  intro n s δ r hδ hr hsep hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : s.card ≤ 1 := Finset.card_le_one.2 (fun a _ b _ => Subsingleton.elim a b)
    have h1' : (s.card : ℝ) ≤ 1 := by exact_mod_cast h1
    simpa using h1'
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  have hδ2 : 0 < δ / 2 := by positivity
  have hR : 0 ≤ r + δ / 2 := by positivity
  have hmeas : ∑ x ∈ s, (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x (δ / 2)) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2)) := by
    rw [← measure_biUnion_finset (pairwiseDisjoint_balls s hsep) (fun x _ => measurableSet_ball)]
    exact measure_mono (biUnion_balls_subset s hs)
  simp only [Measure.addHaar_ball _ _ hδ2.le, Measure.addHaar_ball _ _ hR,
    finrank_euclideanSpace_fin, Finset.sum_const, nsmul_eq_mul] at hmeas
  have hc0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ 0 :=
    (measure_ball_pos _ _ one_pos).ne'
  have hct : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  rw [← mul_assoc] at hmeas
  have h2 := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hmeas
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have hp : 0 < (δ / 2) ^ n := pow_pos hδ2 n
  have key : (1 + 2 * r / δ) ^ n = (r + δ / 2) ^ n / (δ / 2) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [key, le_div_iff₀ hp]
  exact h2

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeCovolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MeasureTheory Module

noncomputable section

namespace PGaussLatticeCovolume

def cols {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) : Fin g → EuclideanSpace ℝ (Fin g) :=
  fun i => WithLp.toLp 2 (B *ᵥ Pi.single i 1)

theorem cols_linearIndependent {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    LinearIndependent ℝ (cols B) := by
  have h := Matrix.linearIndependent_cols_of_det_ne_zero hB
  have e : cols B = (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm ∘ B.col := by
    funext i
    simp [cols]
  rw [e]
  exact h.map' _ (LinearEquiv.ker _)

def colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Basis (Fin g) ℝ (EuclideanSpace ℝ (Fin g)) :=
  basisOfLinearIndependentOfCardEqFinrank' (cols B) (cols_linearIndependent hB) (by simp)

theorem coe_colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    ⇑(colBasis hB) = cols B := by
  simp [colBasis]

theorem span_colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Submodule.span ℤ (Set.range (colBasis hB)) = gaussLattice B := by
  rw [coe_colBasis]
  rfl

def intBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Basis (Fin g) ℤ (gaussLattice B) :=
  ((colBasis hB).restrictScalars ℤ).map (LinearEquiv.ofEq _ _ (span_colBasis hB))

theorem coe_intBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    ((↑) : gaussLattice B → EuclideanSpace ℝ (Fin g)) ∘ intBasis hB = cols B := by
  funext i
  simp [intBasis, Basis.restrictScalars_apply, coe_colBasis]

theorem det_cols {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    (EuclideanSpace.basisFun (Fin g) ℝ).toBasis.det (cols B) = B.det := by
  rw [Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, cols]

theorem volume_fundamentalDomain_basisFun (g : ℕ) :
    volume.real (ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin g) ℝ).toBasis) = 1 := by
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume),
    OrthonormalBasis.coe_toBasis, measureReal_def,
    (EuclideanSpace.basisFun (Fin g) ℝ).volume_parallelepiped, ENNReal.toReal_one]

end PGaussLatticeCovolume


open PGaussLatticeCovolume in
theorem GaussLatticeCovolume.proof (hL : GaussLatticeIsLattice.Statement) :
    GaussLatticeCovolume.Statement := by
  intro g B hB
  have : DiscreteTopology (gaussLattice B) := (hL g B hB).1
  have : IsZLattice ℝ (gaussLattice B) := (hL g B hB).2
  rw [ZLattice.covolume_eq_det_mul_measureReal (gaussLattice B) volume (intBasis hB)
      (EuclideanSpace.basisFun (Fin g) ℝ).toBasis,
    coe_intBasis, det_cols, volume_fundamentalDomain_basisFun, mul_one]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShell
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

noncomputable section

namespace PGaussShell

theorem base_le (m δ : ℝ) (hm : 0 ≤ m) (hδ : 0 < δ) :
    1 + 2 * (m + 1) / δ ≤ 3 * (m + 1) * (1 + 1 / δ) := by
  have h2 : 3 * (m + 1) * (1 + 1 / δ) = 3 * (m + 1) + 3 * (m + 1) / δ := by ring
  have h1 : 2 * (m + 1) / δ ≤ 3 * (m + 1) / δ :=
    div_le_div_of_nonneg_right (by linarith) hδ.le
  linarith

end PGaussShell

theorem GaussShell.proof (hP : GaussPacking.Statement) (hT : GaussTermBound.Statement) :
    GaussShell.Statement := by
  intro n hn Λ δ hδ hmin F m
  set T := F.filter (fun μ : Λ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊ = m) with hTdef
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hlow : ∀ μ ∈ T, (m : ℝ) ≤ ‖(μ : EuclideanSpace ℝ (Fin n))‖ := by
    intro μ hμ
    rw [← (Finset.mem_filter.1 hμ).2]
    exact Nat.floor_le (norm_nonneg _)
  have hup : ∀ μ ∈ T, ‖(μ : EuclideanSpace ℝ (Fin n))‖ ≤ (m : ℝ) + 1 := by
    intro μ hμ
    have h := Nat.lt_floor_add_one ‖(μ : EuclideanSpace ℝ (Fin n))‖
    rw [(Finset.mem_filter.1 hμ).2] at h
    exact h.le
  have hterm : ∀ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
      Real.exp (-π * (m : ℝ) ^ 2) := by
    intro μ hμ
    apply Real.exp_le_exp.2
    have : (m : ℝ) ^ 2 ≤ ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      pow_le_pow_left₀ hm0 (hlow μ hμ) 2
    nlinarith [Real.pi_pos]
  have hsum : ∑ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
      (T.card : ℝ) * Real.exp (-π * (m : ℝ) ^ 2) := by
    have h := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hcard : (T.card : ℝ) ≤ (1 + 2 * ((m : ℝ) + 1) / δ) ^ n := by
    have h := hP n (T.map (Function.Embedding.subtype _)) δ ((m : ℝ) + 1) hδ (by linarith) ?_ ?_
    · rwa [Finset.card_map] at h
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hy
      simp only [Function.Embedding.coe_subtype] at hxy ⊢
      exact hmin _ (Λ.sub_mem a.2 b.2) (sub_ne_zero.2 hxy)
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      exact hup a ha
  have hδ' : (0 : ℝ) ≤ 1 + 1 / δ := by
    have : 0 ≤ 1 / δ := le_of_lt (one_div_pos.2 hδ)
    linarith
  have hb0 : (0 : ℝ) ≤ 1 + 2 * ((m : ℝ) + 1) / δ := by
    have : 0 ≤ 2 * ((m : ℝ) + 1) / δ := div_nonneg (by linarith) hδ.le
    linarith
  have hpow : (1 + 2 * ((m : ℝ) + 1) / δ) ^ n ≤
      3 ^ n * ((m : ℝ) + 1) ^ n * (1 + 1 / δ) ^ n := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ hb0 (PGaussShell.base_le _ _ hm0 hδ) n
  calc ∑ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      ≤ (T.card : ℝ) * Real.exp (-π * (m : ℝ) ^ 2) := hsum
    _ ≤ 3 ^ n * ((m : ℝ) + 1) ^ n * (1 + 1 / δ) ^ n * Real.exp (-π * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (hcard.trans hpow) (Real.exp_pos _).le
    _ = 3 ^ n * (1 + 1 / δ) ^ n * (((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2)) := by ring
    _ ≤ 3 ^ n * (1 + 1 / δ) ^ n * (√(n : ℝ) ^ n * Real.exp √(n : ℝ) *
          Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ))) :=
        mul_le_mul_of_nonneg_left (hT n hn m) (by positivity)
    _ = gaussShellConst n * (1 + 1 / δ) ^ n * Real.exp (-(m : ℝ)) := by
        unfold gaussShellConst; ring

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPoissonBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace PGaussPoissonBound

theorem norm_toLp_sq {g : ℕ} (v : Fin g → ℝ) : ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

end PGaussPoissonBound


open PGaussPoissonBound in
theorem GaussPoissonBound.proof (hL : GaussLatticeIsLattice.Statement)
    (hV : GaussLatticeCovolume.Statement) (hK : GaussLatticeCoords.Statement)
    (hF : GaussFourierSelf.Statement) : GaussPoissonBound.Statement := by
  intro g B hB a
  obtain ⟨hdisc, hlat⟩ := hL g B hB
  have : DiscreteTopology (gaussLattice B) := hdisc
  have : IsZLattice ℝ (gaussLattice B) := hlat
  obtain ⟨hmem, hsurj, hinj⟩ := hK g B hB
  let E := EuclideanSpace ℝ (Fin g)
  let L := gaussLattice B
  let φ : (Fin g → ℤ) ≃ L := Equiv.ofBijective
    (fun k => ⟨WithLp.toLp 2 (B *ᵥ intVec k), hmem k⟩)
    ⟨fun k k' h => hinj (by
        have := congrArg (fun x : L => WithLp.ofLp (x : E)) h
        simpa using this),
      fun x => by
        obtain ⟨k, hk⟩ := hsurj x x.2
        exact ⟨k, Subtype.ext hk.symm⟩⟩
  let G := GroundTheory.Global.gaussianSchwartz E
  let a' : E := WithLp.toLp 2 (B *ᵥ a)
  let f : (Fin g → ℤ) → ℝ := fun k =>
    Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))
  have hG : ∀ k, G ((φ k : E) + a') = ((f k : ℝ) : ℂ) := fun k => by
    have h1 : ((φ k : E) + a') = WithLp.toLp 2 (B *ᵥ (intVec k + a)) := by
      rw [Matrix.mulVec_add]; rfl
    rw [h1, GroundTheory.Global.gaussianSchwartz_apply, norm_toLp_sq]
  have hnG : ∀ k, ‖G ((φ k : E) + a')‖ = f k := fun k => by
    rw [hG, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hGfun : (G : E → ℂ) = fun x => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) :=
    funext fun x => GroundTheory.Global.gaussianSchwartz_apply x
  have hFG : ∀ μ : E, 𝓕 (G : E → ℂ) μ = ((Real.exp (-π * ‖μ‖ ^ 2) : ℝ) : ℂ) := fun μ => by
    rw [hGfun]; exact hF g μ
  have hnD : ∀ μ : GroundTheory.Global.dualLattice L,
      ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ = Real.exp (-π * ‖(μ : E)‖ ^ 2) := fun μ => by
    rw [norm_mul, Circle.norm_coe, mul_one, hFG, Complex.norm_of_nonneg (Real.exp_pos _).le]

  have hsumf : Summable f := by
    have h := (φ.summable_iff (f := fun ℓ : L => ‖G (ℓ + a')‖)).2
      (GroundTheory.Global.lattice_summable_norm L G a')
    exact h.congr fun k => hnG k

  have hsumD := GroundTheory.Global.dualLattice_summable_norm L G a'
  have hsumE : Summable fun μ : GroundTheory.Global.dualLattice L => Real.exp (-π * ‖(μ : E)‖ ^ 2) :=
    hsumD.congr hnD
  refine ⟨hsumf, hsumE, ?_⟩

  have hP := GroundTheory.Global.lattice_poisson_summation L G a'
  have hlhs : ∑' ℓ : L, G (ℓ + a') = ((∑' k, f k : ℝ) : ℂ) := by
    rw [← φ.tsum_eq (fun ℓ : L => G (ℓ + a')), Complex.ofReal_tsum]
    exact tsum_congr fun k => hG k
  rw [hlhs] at hP
  have hcov : ZLattice.covolume L = |B.det| := hV g B hB
  have hcpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  calc ∑' k, f k = ‖((∑' k, f k : ℝ) : ℂ)‖ :=
        (Complex.norm_of_nonneg (tsum_nonneg fun k => (Real.exp_pos _).le)).symm
    _ = (ZLattice.covolume L)⁻¹ *
          ‖∑' μ : GroundTheory.Global.dualLattice L, 𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ := by
        rw [hP, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    _ ≤ (ZLattice.covolume L)⁻¹ *
          ∑' μ : GroundTheory.Global.dualLattice L, ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsumD) (inv_pos.2 hcpos).le
    _ = |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B),
          Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := by
        rw [hcov]; exact congrArg _ (tsum_congr hnD)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCubeParseval
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Real ComplexConjugate

noncomputable section

namespace KThetaCubeParseval

lemma torusChar_eq {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = Complex.exp (((2 * π * ∑ i, (m i : ℝ) * u i : ℝ) : ℂ) * Complex.I) := by
  unfold torusChar
  congr 1
  push_cast
  ring

lemma norm_torusChar {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ‖torusChar m u‖ = 1 := by
  rw [torusChar_eq, Complex.norm_exp_ofReal_mul_I]

lemma torusChar_mul_conj {g : ℕ} (k l : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar k u * conj (torusChar l u) = torusChar (k - l) u := by
  rw [torusChar_eq, torusChar_eq, torusChar_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

lemma continuous_torusChar {g : ℕ} (m : Fin g → ℤ) : Continuous (torusChar m) := by
  unfold torusChar
  fun_prop

lemma measureReal_cube (g : ℕ) :
    (volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)).real Set.univ = 1 := by
  simp [Measure.real, Real.volume_Icc_pi]

end KThetaCubeParseval


open KThetaCubeParseval in
theorem ThetaCubeParseval.proof (h : ThetaCharIntegral.Statement) : ThetaCubeParseval.Statement := by
  intro g c hc
  set μ := volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)

  set F : (Fin g → ℤ) × (Fin g → ℤ) → (Fin g → ℝ) → ℂ :=
    fun p u => c p.1 * conj (c p.2) * torusChar (p.1 - p.2) u with hF
  have hnorm1 : ∀ u, Summable fun k => ‖c k * torusChar k u‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hnorm2 : ∀ u, Summable fun l => ‖conj (c l) * conj (torusChar l u)‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hpt : ∀ u, ((‖∑' k, c k * torusChar k u‖ ^ 2 : ℝ) : ℂ) = ∑' p, F p u := by
    intro u
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, Complex.conj_tsum]
    simp only [map_mul]
    rw [tsum_mul_tsum_of_summable_norm (hnorm1 u) (hnorm2 u)]
    congr 1
    ext p
    rw [hF]
    dsimp only
    rw [← torusChar_mul_conj]
    ring
  have hnormF : ∀ p u, ‖F p u‖ = ‖c p.1‖ * ‖c p.2‖ := by
    intro p u
    simp [hF, norm_torusChar]
  have hint : ∀ p, Integrable (F p) μ := fun p =>
    ((continuous_torusChar (p.1 - p.2)).const_smul (c p.1 * conj (c p.2))).integrableOn_Icc
  have hμ : μ.real Set.univ = 1 := measureReal_cube g
  have hsum : Summable fun p => ∫ u, ‖F p u‖ ∂μ := by
    simp only [hnormF, integral_const, hμ, one_smul]
    exact Summable.mul_of_nonneg hc hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hterm : ∀ p, ∫ u, F p u ∂μ = if p.1 - p.2 = 0 then c p.1 * conj (c p.2) else 0 := by
    intro p
    rw [hF]
    dsimp only
    rw [integral_const_mul, h g (p.1 - p.2)]
    split_ifs <;> simp
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_tsum]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hterm]
  have hinj : Function.Injective fun k : Fin g → ℤ => (k, k) := fun a b hab => (Prod.mk.inj hab).1
  rw [← hinj.tsum_eq]
  · congr 1
    ext k
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · intro p hp
    have : p.1 - p.2 = 0 := by
      by_contra hne
      exact hp (by simp [hne])
    exact ⟨p.1, Prod.ext rfl (sub_eq_zero.mp this)⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartHessHolo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix Filter Topology

noncomputable section

namespace ChartEnergySwapHessian

open ChartMongeAmpereAffineInvariance

variable {D : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E']

theorem eventually_fderiv_I_smul {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y) :
    ∀ᶠ y' in 𝓝 y, ∀ v, fderiv ℝ F y' (Complex.I • v) = Complex.I • fderiv ℝ F y' v := by
  filter_upwards [hF.eventually (by simp)] with y' hy' v
  rw [(hy'.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
  simp

theorem fderiv_fderiv_I_right {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y u (Complex.I • v) = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by
  have hR : ContDiffAt ℝ 2 F y := hF.restrict_scalars ℝ
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun y' => fderiv ℝ F y' (Complex.I • v))
      ((fderiv ℝ (fderiv ℝ F) y).flip (Complex.I • v)) y := by
    simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • v) y)
  have h2 : HasFDerivAt (fun y' => Complex.I • fderiv ℝ F y' v)
      (Complex.I • (fderiv ℝ (fderiv ℝ F) y).flip v) y := by
    have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).const_smul Complex.I
    simpa [Pi.smul_def] using this
  have h3 := h2.congr_of_eventuallyEq ((eventually_fderiv_I_smul hF).mono fun y' hy' => hy' v)
  have := congrArg (fun L => L u) (h1.unique h3)
  simpa using this


omit [NormedSpace ℂ E'] [IsScalarTower ℝ ℂ E'] in
theorem fderiv_fderiv_symm {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℝ 2 F y)
    (u v : Fin D → ℂ) : fderiv ℝ (fderiv ℝ F) y u v = fderiv ℝ (fderiv ℝ F) y v u :=
  hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) u v

theorem fderiv_fderiv_I_left {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y (Complex.I • u) v = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by
  rw [fderiv_fderiv_symm (hF.restrict_scalars ℝ), fderiv_fderiv_I_right hF,
    fderiv_fderiv_symm (hF.restrict_scalars ℝ)]

theorem fderiv_fderiv_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : G → ℝ}
    {F : (Fin D → ℂ) → G} {y : Fin D → ℂ} (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℝ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ fun y' => g (F y')) y u v =
      fderiv ℝ (fderiv ℝ g) (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) +
        fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) := by
  have hgev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ g (F y') :=
    hF.continuousAt.tendsto.eventually
      ((hg.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))
  have hFev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ F y' :=
    (hF.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y' => g (F y')) =ᶠ[𝓝 y]
      fun y' => (fderiv ℝ g (F y')).comp (fderiv ℝ F y') := by
    filter_upwards [hgev, hFev] with y' h1 h2
    exact fderiv_comp y' h1 h2
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) (F y) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y' => fderiv ℝ g (F y'))
      ((fderiv ℝ (fderiv ℝ g) (F y)).comp (fderiv ℝ F y)) y :=
    hgd.hasFDerivAt.comp y (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hall := (hc.clm_comp hFd.hasFDerivAt).congr_of_eventuallyEq heq
  rw [hall.fderiv]
  simp [add_comm]

theorem fderiv_fderiv_add {f₁ f₂ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h₁ : ContDiffAt ℝ 2 f₁ y)
    (h₂ : ContDiffAt ℝ 2 f₂ y) :
    fderiv ℝ (fderiv ℝ fun y' => f₁ y' + f₂ y') y = fderiv ℝ (fderiv ℝ f₁) y + fderiv ℝ (fderiv ℝ f₂) y := by
  have heq : fderiv ℝ (fun y' => f₁ y' + f₂ y') =ᶠ[𝓝 y] fun y' => fderiv ℝ f₁ y' + fderiv ℝ f₂ y' := by
    filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with y' a b
    exact fderiv_add (a.differentiableAt (by norm_num)) (b.differentiableAt (by norm_num))
  have hd₁ : DifferentiableAt ℝ (fderiv ℝ f₁) y :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd₂ : DifferentiableAt ℝ (fderiv ℝ f₂) y :=
    (h₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ((hd₁.hasFDerivAt.add hd₂.hasFDerivAt).congr_of_eventuallyEq heq).fderiv

theorem sesq_eq_of_form (H H₀ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, H u v = H₀ (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) (a b : Fin D → ℂ) :
    sesq H a b = sesq H₀ (L a) (L b) := by
  simp only [sesq, hH, map_smul]
  rw [hR₁, hR₂]
  push_cast
  ring

theorem cxHessian_of_form (f g : (Fin D → ℂ) → ℝ) (y w : Fin D → ℂ) (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ))
    (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, fderiv ℝ (fderiv ℝ f) y u v = fderiv ℝ (fderiv ℝ g) w (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) :
    cxHessian f y = (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ * cxHessian g w *
      (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map (starRingEnd ℂ) := by
  ext i j
  rw [cxHessian_eq_sesq, sesq_eq_of_form _ _ L R hH hR₁ hR₂, sesq_expand]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hc : cxHessian g w l k = sesq (fderiv ℝ (fderiv ℝ g) w) (Pi.single l 1) (Pi.single k 1) := rfl
  simp only [hc, starRingEnd_apply]
  ring

theorem cxHessian_comp_holo (f g : (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ)) (h : (Fin D → ℂ) → ℂ)
    (y : Fin D → ℂ) (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℂ 2 F y) (hh : ContDiffAt ℂ 2 h y)
    (hf : f =ᶠ[𝓝 y] fun y' => g (F y') + (h y').re) :
    cxHessian f y = (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ *
      cxHessian g (F y) * (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map
        (starRingEnd ℂ) := by
  have hFR : ContDiffAt ℝ 2 F y := hF.restrict_scalars ℝ
  have hhR : ContDiffAt ℝ 2 h y := hh.restrict_scalars ℝ
  have hHess : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ fun y' => g (F y') + (h y').re) y := by
    have : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (fun y' => g (F y') + (h y').re) :=
      hf.eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq
    exact this.fderiv_eq
  have hre2 : ContDiffAt ℝ 2 (fun y' => (h y').re) y := Complex.reCLM.contDiff.contDiffAt.comp y hhR
  have hsum := fderiv_fderiv_add (f₁ := fun y' => g (F y')) (f₂ := fun y' => (h y').re) (hg.comp y hFR) hre2
  have hre : ∀ u v, fderiv ℝ (fderiv ℝ fun y' => (h y').re) y u v =
      Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v) := by
    intro u v
    have := fderiv_fderiv_comp (g := ⇑Complex.reCLM) (F := h) Complex.reCLM.contDiff.contDiffAt hhR u v
    have h0 : fderiv ℝ (fderiv ℝ (⇑Complex.reCLM)) (h y) = 0 := by
      have : fderiv ℝ (⇑Complex.reCLM) = fun _ => Complex.reCLM := funext fun _ => Complex.reCLM.fderiv
      rw [this]
      exact fderiv_const_apply _
    rw [h0, Complex.reCLM.fderiv] at this
    simpa using this
  have hLF : ∀ u, fderiv ℝ F y u = fderiv ℂ F y u := fun u => by
    rw [(hF.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
    rfl
  refine cxHessian_of_form f g y (F y) (fderiv ℂ F y)
    (fun u v => fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) + Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v))
    ?_ ?_ ?_
  · intro u v
    rw [hHess, hsum, _root_.add_apply, _root_.add_apply, fderiv_fderiv_comp hg hFR,
      hre, hLF, hLF]
    ring
  · intro u v
    simp only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh,
      fderiv_fderiv_I_right hh, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
    ring
  · intro u v
    simp only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh,
      fderiv_fderiv_I_right hh]

theorem maDensity_comp_holo (Φ' Φ : Fin D → (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ))
    (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ) (hΦ : ∀ j, ContDiffAt ℝ 2 (Φ j) (F y)) (hF : ContDiffAt ℂ 2 F y)
    (hh : ContDiffAt ℂ 2 h y) (hΦ' : ∀ j, Φ' j =ᶠ[𝓝 y] fun y' => Φ j (F y') + (h y').re) :
    maDensity Φ' y = Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det *
      maDensity Φ (F y) := by
  set J := LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) with hJ
  have hQ : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det (starRingEnd ℂ) J).symm
  have hH : ∀ j, cxHessian (Φ' j) y = Jᵀ * cxHessian (Φ j) (F y) * J.map (starRingEnd ℂ) := fun j =>
    cxHessian_comp_holo (Φ' j) (Φ j) F h y (hΦ j) hF hh (hΦ' j)
  simp only [maDensity, hH]
  rw [mixedDisc_mul_mul (Jᵀ) (J.map (starRingEnd ℂ)) (fun j => cxHessian (Φ j) (F y)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring

theorem det_fderiv_real {F : (Fin D → ℂ) → (Fin D → ℂ)} {y : Fin D → ℂ} (hF : DifferentiableAt ℂ F y) :
    (fderiv ℝ F y).det =
      Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det := by
  rw [hF.fderiv_restrictScalars ℝ, LinearMap.det_toMatrix']
  have : ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F y) : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) :
      (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      ((fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).restrictScalars ℝ := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

end ChartEnergySwapHessian

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplFirstRow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplFirstRow

theorem intVec_ne_zero {ι : Type*} {v : ι → ℤ} (hv : v ≠ 0) : intVec v ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h i
  simpa [intVec] using this

end PSymplFirstRow

theorem SymplFirstRow.proof (h1 : SymplMinExists.Statement) (h2 : SymplMinBound.Statement)
    (h3 : SymplOrbit.Statement) (h4 : SymplShortPrim.Statement) (h5 : SymplGramMem.Statement) :
    SymplFirstRow.Statement := by
  intro n G hG hpd
  obtain ⟨ρsq, hleast⟩ := h1 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd
  have hdet : G.det = 1 := SymplecticGroup.det_eq_one hG
  have hbound := h2 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd hdet ρsq hleast
  obtain ⟨v, hv0, hvρ⟩ := hleast.1
  refine ⟨ρsq, hleast, ?_, ?_, ?_⟩
  · rw [hvρ]
    have := hpd.dotProduct_mulVec_pos (PSymplFirstRow.intVec_ne_zero hv0)
    simpa [qf] using this
  · simp only [Fintype.card_sum, Fintype.card_fin] at hbound
    push_cast at hbound
    linarith
  · have hmin : ∀ u : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, u ≠ 0 →
        qf G (intVec v) ≤ qf G (intVec u) := by
      intro u hu
      rw [← hvρ]
      exact hleast.2 ⟨u, hu, rfl⟩
    obtain ⟨P, hP, m, hm⟩ := h3 n v
    have hrow : ∃ P' ∈ symplecticGroup (Fin (n + 1)) ℤ, P' (Sum.inl 0) = v := by
      rcases h4 _ G hpd v (P (Sum.inl 0)) m hm hv0 hmin with h | h
      · exact ⟨P, hP, by rw [hm, h, one_smul]⟩
      · refine ⟨-P, SymplecticGroup.neg_mem hP, ?_⟩
        rw [hm, h, neg_one_smul]
        rfl
    obtain ⟨P', hP', hP'v⟩ := hrow
    refine ⟨P', hP', ?_⟩
    rw [(h5 (n + 1) P' G hP' hG hpd).2.2.2 (Sum.inl 0), hP'v, hvρ]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplShortPrim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplShortPrim

lemma intVec_smul {ι : Type} (m : ℤ) (w : ι → ℤ) : intVec (m • w) = (m : ℝ) • intVec w := by
  funext i
  simp [intVec]

lemma qf_smul {ι : Type} [Fintype ι] (Y : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    qf Y (c • x) = c ^ 2 * qf Y x := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

end PSymplShortPrim


open PSymplShortPrim in
theorem SymplShortPrim.proof : SymplShortPrim.Statement := by
  intro ι _ _ G hG v w m hvw hv hmin
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hw : w ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hwR : intVec w ≠ 0 := by
    intro h
    apply hw
    funext i
    have := congrFun h i
    simpa [intVec] using this
  have hq : 0 < qf G (intVec w) := by
    have := hG.dotProduct_mulVec_pos hwR
    simpa [qf] using this
  have hle := hmin w hw
  rw [hvw, intVec_smul, qf_smul] at hle
  have hm2 : ((m : ℝ)) ^ 2 ≤ 1 := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hm2' : m ^ 2 ≤ 1 := by exact_mod_cast hm2
  have habs : |m| ≤ 1 := (sq_le_one_iff_abs_le_one m).mp hm2'
  rw [abs_le] at habs
  omega

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplDetSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplDetSchur

noncomputable def clearCol {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => if i = j then 1 else if j = 0 then -A i 0 / A 0 0 else 0

theorem det_clearCol {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (clearCol A).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ ?_]
  · simp [clearCol]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hne : i ≠ j := ne_of_lt hij'
    have hj : j ≠ 0 := by
      rintro rfl
      simp at hij'
    simp [clearCol, hne, hj]

theorem clearCol_mul_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin (n + 1)) :
    (clearCol A * A) 0 j = A 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [clearCol, (Fin.succ_ne_zero _).symm, Fin.succ_ne_zero]

theorem clearCol_mul_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n)
    (j : Fin (n + 1)) :
    (clearCol A * A) i.succ j = A i.succ j - A i.succ 0 / A 0 0 * A 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [clearCol, Fin.succ_ne_zero, Fin.succ_inj]
  ring

end PSymplDetSchur


open PSymplDetSchur in
theorem SymplDetSchur.proof : SymplDetSchur.Statement := by
  intro n A ha
  have hdet : A.det = (clearCol A * A).det := by
    rw [Matrix.det_mul, det_clearCol, one_mul]
  rw [hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hcol : ∀ i : Fin n, (clearCol A * A) i.succ 0 = 0 := by
    intro i
    rw [clearCol_mul_succ]
    field_simp
    ring
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero, clearCol_mul_zero]
  congr 1
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, clearCol_mul_succ]
  ring

end GroundTheory.Heights₂.Heights
end
