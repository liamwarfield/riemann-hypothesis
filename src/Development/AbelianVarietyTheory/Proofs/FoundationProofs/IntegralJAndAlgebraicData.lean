module

public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEntireOfLocallyDvd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators IntermediateField

noncomputable section

namespace GlobalTheory.CurveAlgebraic

theorem exists_algHom_apply_eq {k : Type} [Field k] [Algebra k ℂ] {x x' : ℂ}
    (hx : Transcendental k x) (hx' : Transcendental k x')
    (hm : x ∈ (algebraicClosure k⟮x⟯ ℂ)) :
    ∃ σ : (algebraicClosure k⟮x⟯ ℂ) →ₐ[k] ℂ, σ ⟨x, hm⟩ = x' := by
  let τ : k⟮x⟯ →ₐ[k] ℂ := (k⟮x'⟯.val).comp
    ((RatFunc.algEquivOfTranscendental x' hx').toAlgHom.comp
      (RatFunc.algEquivOfTranscendental x hx).symm.toAlgHom)
  have hτ : τ (IntermediateField.AdjoinSimple.gen k x) = x' := by
    change ((RatFunc.algEquivOfTranscendental x' hx')
      ((RatFunc.algEquivOfTranscendental x hx).symm
        (IntermediateField.AdjoinSimple.gen k x)) : ℂ) = x'
    rw [RatFunc.algEquivOfTranscendental_symm_gen, RatFunc.algEquivOfTranscendental_X]
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := k) (L := k⟮x⟯)
    (M := ℂ) (E := algebraicClosure k⟮x⟯ ℂ) τ
  refine ⟨σ, ?_⟩
  rw [← hτ, ← hσ]
  rfl

theorem isAlgebraic_of_torsion {k : Type} [Field k] [CharZero k] [Algebra k ℂ]
    (W : WeierstrassCurve.Affine k) (V : WeierstrassCurve.Affine ℂ) (hV : W.baseChange ℂ = V)
    (m : ℕ) (S : Set ℂ) (hS : S.Finite)
    (hmem : ∀ x y (h : V.Nonsingular x y),
      m • (WeierstrassCurve.Affine.Point.some x y h) = 0 → x ∈ S)
    {x y : ℂ} (h : V.Nonsingular x y) (h0 : m • (WeierstrassCurve.Affine.Point.some x y h) = 0)
    (hy : IsAlgebraic k⟮x⟯ y) : IsAlgebraic k x := by
  subst hV
  by_contra hx
  let F := algebraicClosure k⟮x⟯ ℂ
  have hxF : x ∈ F := F.algebraMap_mem (IntermediateField.AdjoinSimple.gen k x)
  have hyF : y ∈ F := mem_algebraicClosure_iff.mpr hy
  let ι : F →ₐ[k] ℂ := F.val.restrictScalars k
  have hι : Function.Injective ι := ι.toRingHom.injective
  have hF : (W.baseChange F).Nonsingular ⟨x, hxF⟩ ⟨y, hyF⟩ :=
    (W.baseChange_nonsingular hι _ _).mp h
  have h1 : m • (WeierstrassCurve.Affine.Point.some _ _ hF) = 0 := by
    apply WeierstrassCurve.Affine.Point.map_injective (W' := W) ι
    rw [map_nsmul, map_zero, WeierstrassCurve.Affine.Point.map_some]
    exact h0
  have h2 : ∀ n : ℕ, x + n ∈ S := fun n => by
    have hn : Transcendental k (x + n) := fun ha => hx (by
      have := ha.sub (isAlgebraic_natCast (R := k) (A := ℂ) n)
      simpa using this)
    obtain ⟨σ, hσ⟩ := exists_algHom_apply_eq hx hn hxF
    have h3 := congrArg (WeierstrassCurve.Affine.Point.map (W' := W) σ) h1
    rw [map_nsmul, map_zero, WeierstrassCurve.Affine.Point.map_some] at h3
    exact hσ ▸ hmem _ _ _ h3
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => x + n) ?_ h2 hS
  intro a b hab
  simpa using hab

theorem weierstrassP_mem (L : PeriodPair) (h2 : L.g₂ ∈ Qbar) (h3 : L.g₃ ∈ Qbar) {m : ℕ}
    (hm : 0 < m) {t : ℂ} (ht : t ∉ L.lattice) (hmt : (m : ℂ) * t ∈ L.lattice) :
    L.weierstrassP t ∈ Qbar ∧ L.derivWeierstrassP t ∈ Qbar := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmul : ∀ z : ℂ, m • latticePoint L z = latticePoint L ((m : ℂ) * z) := fun z => by
    rw [← latticePointHom_apply, ← latticePointHom_apply, ← map_nsmul, nsmul_eq_mul]
  obtain ⟨A, D, -, -, hD, -, -, -, -, hroot, -⟩ := exists_weierstrassP_mul_eq_div (L := L) (L' := L)
    hm0 (fun l hl => by rw [← nsmul_eq_mul]; exact nsmul_mem hl m) ⊤ trivial trivial trivial
    (fun _ _ _ => trivial)
  have hsq := L.derivWeierstrassP_sq t ht
  have hx : IsAlgebraic Qbar (L.weierstrassP t) := by
    refine isAlgebraic_of_torsion
      (⟨0, 0, 0, -⟨L.g₂, h2⟩ / 4, -⟨L.g₃, h3⟩ / 4⟩ : WeierstrassCurve Qbar) (latticeCurve L).toAffine ?_ m
      (D.rootSet ℂ) (D.rootSet_finite ℂ) ?_ (latticeCurve_nonsingular L ht) ?_ ?_
    · ext <;> simp [latticeCurve, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange] <;> rfl
    · intro x y h h0
      obtain ⟨z, hz⟩ := latticePoint_surjective L (.some x y h)
      have hz' : z ∉ L.lattice := fun hc => by
        rw [latticePoint_of_mem L hc] at hz
        exact WeierstrassCurve.Affine.Point.some_ne_zero _ hz.symm
      rw [← hz, hmul, latticePoint_eq_zero_iff] at h0
      rw [latticePoint_of_notMem L hz'] at hz
      obtain ⟨rfl, -⟩ := WeierstrassCurve.Affine.Point.some.inj hz
      rw [Polynomial.mem_rootSet]
      exact ⟨hD.ne_zero, (hroot z hz').mpr h0⟩
    · rw [← latticePoint_of_notMem L ht, hmul, latticePoint_eq_zero_iff]
      exact hmt
    · set F := (↥Qbar)⟮L.weierstrassP t⟯
      have e1 : L.weierstrassP t ∈ F := IntermediateField.mem_adjoin_simple_self _ _
      have e2 : L.g₂ ∈ F := F.algebraMap_mem ⟨L.g₂, h2⟩
      have e3 : L.g₃ ∈ F := F.algebraMap_mem ⟨L.g₃, h3⟩
      have e4 : (L.derivWeierstrassP t / 2) ^ 2 ∈ F := by
        rw [div_pow, hsq]
        refine div_mem (sub_mem (sub_mem (mul_mem (ofNat_mem F 4) (pow_mem e1 3)) (mul_mem e2 e1)) e3)
          (pow_mem (ofNat_mem F 2) 2)
      exact IsAlgebraic.of_pow two_pos (isAlgebraic_algebraMap (⟨_, e4⟩ : F))
  have hx' : L.weierstrassP t ∈ Qbar :=
    haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
    mem_algebraicClosure_iff.mpr (hx.restrictScalars ℚ)
  refine ⟨hx', mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)⟩
  rw [hsq, ← mem_algebraicClosure_iff]
  exact sub_mem (sub_mem (mul_mem (ofNat_mem _ 4) (pow_mem hx' 3)) (mul_mem h2 hx')) h3

theorem exists_periodPair (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (h : Crv D cc δ) : ∃ L : PeriodPair, (∀ z, z ∈ lamOf D cc δ ↔ z ∈ L.lattice) ∧
      L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 ∧ IsIntegral ℤ (1728 * L.g₂ ^ 3) := by
  obtain ⟨⟨w₁, w₂, hw, he⟩, -, hΔ, -, hcm⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ h
  let L : PeriodPair := ⟨w₁, w₂, hw⟩
  have hL : ∀ z, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := fun z => by
    rw [he, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨e2, e3, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  have hΔ' : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by rw [← e2, ← e3]; exact hΔ
  refine ⟨L, hL, hΔ', ?_⟩
  have := CMCurves.isIntegral_latticeJ (Formalism.L2.Pj.LPb.finrank_K D)
    (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) L
    (fun a z hz => (hL _).mp (hcm a z ((hL _).mpr hz)))
  rwa [CMCurves.latticeJ, hΔ', div_one] at this

theorem integral_j_and_algebraic_data : ∀ (D : D7), admG1 D → GL3Theta.admJ D ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → DataIn D (tor0 D cc δ) Qbar ∧ ∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ Qbar ∧ wpD (lamOf D cc δ) t ∈ Qbar := by
  intro D hD
  refine ⟨fun cc δ h1 h2 => ?_, fun cc δ h => ?_⟩
  · obtain ⟨L, hL, -, hj⟩ := exists_periodPair D hD cc δ ⟨h1, h2⟩
    rwa [(GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL).1]
  obtain ⟨L, hL, hΔ, hj⟩ := exists_periodPair D hD cc δ h
  obtain ⟨e2, e3, -, -, hp, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  have hj' : 1728 * L.g₂ ^ 3 ∈ Qbar :=
    mem_algebraicClosure_iff.mpr (hj.tower_top (A := ℚ)).isAlgebraic
  have hc : L.g₂ ^ 3 ∈ Qbar := by
    have := div_mem hj' (ofNat_mem Qbar 1728)
    rwa [mul_div_cancel_left₀ _ (by norm_num)] at this
  have h2 : L.g₂ ∈ Qbar :=
    mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow three_pos (mem_algebraicClosure_iff.mp hc))
  have h3 : L.g₃ ∈ Qbar := by
    refine mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)
    rw [← mem_algebraicClosure_iff,
      show L.g₃ ^ 2 = (L.g₂ ^ 3 - 1) / 27 by linear_combination (-1 / 27 : ℂ) * hΔ]
    exact div_mem (sub_mem hc (one_mem _)) (ofNat_mem _ 27)
  refine ⟨⟨fun τ x => ?_, e2 ▸ h2, e3 ▸ h3⟩, ?_⟩
  · exact mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)
  · rintro t ⟨m, hm, hmt⟩ ht
    rw [(hp t ht).1, (hp t ht).2]
    exact weierstrassP_mem L h2 h3 hm (fun hc => ht ((hL _).mpr hc)) ((hL _).mp hmt)

end GlobalTheory.CurveAlgebraic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicDataStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admJ_and_torsion_data_algebraic : ∀ (D : D7), admG1 D → GL3Theta.admJ D ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → DataIn D (tor0 D cc δ) Qbar ∧ ∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ Qbar ∧ wpD (lamOf D cc δ) t ∈ Qbar := by
  first | exact @GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data | exact GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data | (intros; apply GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.DatumBasic

variable {p : ℕ} [Fact p.Prime]

theorem wModel_Δ (lam : Qbar →+* ℂ_[p]) {Λ : AddSubgroup ℂ} (h2 : g2 Λ ∈ Qbar) (h3 : g3 Λ ∈ Qbar)
    (hd : TaylorLogMetric.discr Λ = 1) : (wModel lam Λ).Δ = 1 := by
  set a : Qbar := ⟨g2 Λ, h2⟩ with ha
  set b : Qbar := ⟨g3 Λ, h3⟩ with hb
  have hc : ∀ x : Qbar, lamC lam (-(x : ℂ) / 4) = -(lam x) / 4 := by
    intro x
    have e : -(x : ℂ) / 4 = ((-x / 4 : Qbar) : ℂ) := by
      push_cast
      rfl
    rw [e, lamC, dite_eq_left (-x / 4).2]
    change lam (-x / 4) = _
    rw [map_div₀, map_neg, map_ofNat]
  have e : a ^ 3 - 27 * b ^ 2 = 1 := by
    apply Subtype.ext
    push_cast
    exact hd
  have e2 := congrArg lam e
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one] at e2
  have ea := hc a
  have eb := hc b
  simp only [ha, hb] at ea eb
  simp only [wModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, ea, eb]
  linear_combination e2

theorem intSer_of_isWq {W : WeierstrassCurve ℂ_[p]} (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) {w : PowerSeries ℂ_[p]}
    (h : IsWq W w) : IntSer w := by
  obtain ⟨hr, -, hC, hX, -⟩ := SerRing.series_ring_laws p
  have hadd : ∀ {f g : PowerSeries ℂ_[p]}, IntSer f → IntSer g → IntSer (f + g) :=
    fun hf hg => (hr _ _ hf hg).1
  have hterm : ∀ (c : ℂ_[p]) (i j : ℕ) (t : PowerSeries ℂ_[p]), ‖c‖ ≤ 1 → IntSer t →
      IntSer (PowerSeries.C c * PowerSeries.X ^ i * t ^ j) := fun c i j t hc ht =>
    SerRing.intSer_mul (SerRing.intSer_mul ((hC c).2 hc) (SerRing.intSer_pow hX i))
      (SerRing.intSer_pow ht j)
  have hone : IntSer (1 : PowerSeries ℂ_[p]) := by simpa using SerRing.intSer_pow hX 0
  have key : ∀ n : ℕ, ∃ t : PowerSeries ℂ_[p], IntSer t ∧ PowerSeries.X ^ n ∣ w - t := by
    intro n
    induction n with
    | zero => exact ⟨1, hone, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht, z, hz⟩ := ih
      refine ⟨_, hadd (hadd (hadd (hadd (hadd hone (hterm _ 1 1 t h1 ht)) (hterm _ 2 1 t h2 ht))
        (hterm _ 3 2 t h3 ht)) (hterm _ 4 2 t h4 ht)) (hterm _ 6 3 t h6 ht),
        z * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2)), ?_⟩
      have h' : w = 1 + PowerSeries.C W.a₁ * PowerSeries.X * w +
          PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C W.a₃ * PowerSeries.X ^ 3 * w ^ 2 +
          PowerSeries.C W.a₄ * PowerSeries.X ^ 4 * w ^ 2 +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 6 * w ^ 3 := h
      linear_combination h' + (PowerSeries.X * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2))) * hz
  intro n
  obtain ⟨t, ht, hd⟩ := key (n + 1)
  have e := PowerSeries.X_pow_dvd_iff.1 hd n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at e
  rw [e]
  exact ht n

theorem datum_basic : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → ‖((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ IntSer g.wq⁻¹ ∧ PowerSeries.constantCoeff g.wq⁻¹ = 1 ∧ PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  intro p _ g ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hw, _⟩ hL a2 a3 hd
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have := congrArg PowerSeries.constantCoeff hw
    simpa using this
  refine ⟨?_, SerRing.intSer_inv (intSer_of_isWq h1 h2 h3 h4 h6 hw) (by rw [hw0, norm_one]),
    by rw [PowerSeries.constantCoeff_inv, hw0, inv_one],
    GlobalTheory.ThetaParam.constantCoeff_ePhi1 g hw (GlobalTheory.OddTheta.sgStar_laws _ hL).1.2.1,
    GlobalTheory.ThetaParam.atU_sg g ((hL.sg_eq_zero 0).2 (zero_mem _))⟩
  rw [WeierstrassCurve.variableChange_Δ, wModel_Δ g.lam a2 a3 hd, mul_one, norm_pow] at hΔ
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hΔ

end GlobalTheory.EvenTheta.DatumBasic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.RatTransl

variable {D : D7} {T : Tor D} {N N' : ℕ}

theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem hf_nsmul (n : ℕ) (x z : VC D N N') : Hf D T (n • x) z = Hf D T x (n • z) := by
  simp only [Hf, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hf_conj (x z : VC D N N') : Hf D T z x = (starRingEnd ℂ) (Hf D T x z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem differentiable_hf (x : VC D N N') : Differentiable ℂ (fun z => Hf D T z x) := by
  unfold Hf
  fun_prop

theorem differentiable_wd (x : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (Wd D T x G) := by
  have h := differentiable_hf (T := T) x
  unfold Wd U
  fun_prop

theorem wd_wd_of_int {x z : VC D N N'} {G : VC D N N' → ℂ} (hx : Wd D T x G = G) (m : ℤ)
    (hm : (Hf D T x z).im = m) (w : VC D N N') : Wd D T x (Wd D T z G) w = Wd D T z G w := by
  have h1 := congrFun hx (w + z)
  have h2 : Hf D T x z = Hf D T z x + 2 * Complex.I * m := by
    rw [hf_conj x z]
    apply Complex.ext <;> simp [hm]
    ring
  have h3 : Complex.exp (-(Real.pi : ℂ) * Hf D T (w + x) z - (Real.pi : ℂ) * Hf D T z z / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T w x - (Real.pi : ℂ) * Hf D T x x / 2) =
      Complex.exp (-(Real.pi : ℂ) * Hf D T (w + z) x - (Real.pi : ℂ) * Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T w z - (Real.pi : ℂ) * Hf D T z z / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-m, ?_⟩
    rw [hf_add_left, hf_add_left, h2]
    push_cast
    ring
  simp only [Wd, U] at h1 ⊢
  rw [← h1, add_right_comm w x z]
  linear_combination (wdPh D T x * wdPh D T z * G (w + z + x)) * h3

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  exact h2 ▸ (h1 1).2

theorem pt_nsmul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (n : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (n • z) = n • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
  ring

theorem map_inc_nsmul (n : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    (n • z).map (inc D) = n • z.map (inc D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]

theorem wd_mem_TT : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N' := by
  rintro D hg cc δ hc N N' z F ⟨hd, m, hm, hF⟩
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hg cc δ hc N N'
  obtain ⟨-, -, hI, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N')
    (Or.inr ⟨_, _, sd_std D _, sd_std D _, rfl⟩)
  obtain ⟨n, hn, hz⟩ := h4 (z.map (inc D))
  rw [← map_inc_nsmul, h1, pt_nsmul] at hz
  refine ⟨differentiable_wd _ hd, n * m, Nat.mul_pos hn hm, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hI _ (AddSubgroup.nsmul_mem _ hx m) _ hz
  have h0 : Wd D (tor0 D cc δ) ((n * m) • x) F = F := by
    rw [mul_comm, mul_smul]
    exact hF _ (AddSubgroup.nsmul_mem _ hx n)
  funext w
  exact wd_wd_of_int h0 k (by rw [mul_smul, hf_nsmul, hk]) w

end GlobalTheory.FinWeil.RatTransl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctionsStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_rationalTranslate_mem_thetaFunctions : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N' := by
  first | exact @GlobalTheory.FinWeil.RatTransl.wd_mem_TT | exact GlobalTheory.FinWeil.RatTransl.wd_mem_TT | (intros; apply GlobalTheory.FinWeil.RatTransl.wd_mem_TT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.QuadSubfield

variable (D : D7)

theorem emb_conj (f : D.host.E →+* ℂ) (y : D.host.E) :
    f (D.host.conj y) = starRingEnd ℂ (f y) := D.host.conjE_apply f y

theorem conj_conj (y : D.host.E) : D.host.conj (D.host.conj y) = y := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

theorem exists_coords {x : D.host.E} (hx : x ∈ D.host.K) :
    ∃ a b : ℚ, x = (a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD := by
  have halg : IsAlgebraic ℚ D.host.sqrtMinusD := Algebra.IsAlgebraic.isAlgebraic _
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqrtMinusD} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hx
  clear hx
  have hs := D.host.sqrtMinusD_sq
  induction hx' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    refine ⟨a * a' - D.host.d * b * b', a * b' + a' * b, ?_⟩
    push_cast
    linear_combination (b : D.host.E) * (b' : D.host.E) * hs

theorem conj_coords (a b : ℚ) :
    D.host.conj ((a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD) =
      (a : D.host.E) - (b : D.host.E) * D.host.sqrtMinusD := by
  rw [map_add (f := _), map_mul, map_ratCast, map_ratCast, D.host.conj_sqrtMinusD]
  ring

theorem conj_mem {x : D.host.E} (hx : x ∈ D.host.K) : D.host.conj x ∈ D.host.K := by
  obtain ⟨a, b, rfl⟩ := exists_coords D hx
  rw [conj_coords]
  exact sub_mem (SubfieldClass.ratCast_mem _ a)
    (mul_mem (SubfieldClass.ratCast_mem _ b) (Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D))

def conjK : D.host.K →+* D.host.K :=
  RingHom.codRestrict ((D.host.conj : D.host.E →+* D.host.E).comp D.host.K.val.toRingHom)
    D.host.K (fun x => conj_mem D x.2)

theorem coe_conjK (x : D.host.K) : ((conjK D x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := rfl

theorem isGalois_over : IsGalois D.host.K D.host.E := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  exact IsGalois.tower_top_of_isGalois ℚ _ _

theorem coe_trace (y : D.host.E) :
    ((Algebra.trace D.host.K D.host.E y : D.host.K) : D.host.E) =
      ∑ τ : D.host.E ≃ₐ[D.host.K] D.host.E, τ y := by
  have := isGalois_over D
  exact trace_eq_sum_automorphisms (K := D.host.K) y

theorem conj_comm (τ : D.host.E ≃ₐ[D.host.K] D.host.E) (y : D.host.E) :
    D.host.conj (τ y) = τ (D.host.conj y) := by
  have h : D.host.conj * τ.restrictScalars ℚ = τ.restrictScalars ℚ * D.host.conj :=
    D.host.gal.injective (by rw [map_mul, map_mul, mul_comm])
  exact AlgEquiv.congr_fun h y

theorem trace_conj (y : D.host.E) :
    Algebra.trace D.host.K D.host.E (D.host.conj y) =
      conjK D (Algebra.trace D.host.K D.host.E y) := by
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_conjK, coe_trace, coe_trace, map_sum]
  exact Finset.sum_congr rfl fun τ _ => (conj_comm D τ y).symm

theorem trace_pos (y : D.host.E) (hy : y ≠ 0) :
    ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  obtain ⟨a, b, hab⟩ := exists_coords D (Algebra.trace D.host.K D.host.E (y * D.host.conj y)).2
  have hfix : D.host.conj ((Algebra.trace D.host.K D.host.E (y * D.host.conj y) : D.host.K) : D.host.E)
      = ((Algebra.trace D.host.K D.host.E (y * D.host.conj y) : D.host.K) : D.host.E) := by
    rw [← coe_conjK, ← trace_conj, map_mul, conj_conj, mul_comm]
  rw [hab, conj_coords] at hfix
  have hb : (b : D.host.E) * D.host.sqrtMinusD = 0 := by linear_combination (-1 / 2 : D.host.E) * hfix
  rw [hb, add_zero] at hab
  refine ⟨a, ?_, Subtype.ext (by rw [hab]; simp)⟩
  have h1 := congrArg D.host.φ₀ hab
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_trace, map_sum, map_ratCast] at h1
  have h2 : ∀ τ : D.host.E ≃ₐ[D.host.K] D.host.E,
      D.host.φ₀ (τ (y * D.host.conj y)) = ((Complex.normSq (D.host.φ₀ (τ y)) : ℝ) : ℂ) := by
    intro τ
    rw [map_mul, ← conj_comm, map_mul, emb_conj, Complex.mul_conj]
  simp only [h2] at h1
  have h3 : ∑ τ : D.host.E ≃ₐ[D.host.K] D.host.E, Complex.normSq (D.host.φ₀ (τ y)) = (a : ℝ) := by
    exact_mod_cast h1
  have h4 : (0 : ℝ) < a := by
    rw [← h3]
    refine Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ?_) Finset.univ_nonempty
    simpa using hy
  exact_mod_cast h4

theorem finrank_over : Module.finrank D.host.K D.host.E = fF D := by
  have h := Module.finrank_mul_finrank ℚ D.host.K D.host.E
  rw [Formalism.L2.Pj.LPb.finrank_K, D.host.finrank_cmField] at h
  show _ = 2 * D.R.ord
  omega

theorem quadratic_subfield : ∀ D : D7, Module.finrank D.host.K D.host.E = fF D ∧ ∃ (σ : D.host.K →+* D.host.K) (θ : D.host.K), (∀ x : D.host.K, ((σ x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E)) ∧ θ ^ 2 = -(D.host.d : D.host.K) ∧ σ θ = -θ ∧ (∀ x : D.host.K, ∃ a b : ℚ, x = (a : D.host.K) + (b : D.host.K) * θ) ∧ IsIntegral ℤ ((1 + θ) / 2) ∧ (∀ y : D.host.E, D.host.conj (D.host.conj y) = y) ∧ (∀ y : D.host.E, Algebra.trace D.host.K D.host.E (D.host.conj y) = σ (Algebra.trace D.host.K D.host.E y)) ∧ ∀ y : D.host.E, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  intro D
  refine ⟨finrank_over D, conjK D, ⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩,
    coe_conjK D, ?_, ?_, ?_, ?_, conj_conj D, trace_conj D, trace_pos D⟩
  · apply Subtype.ext
    simpa using D.host.sqrtMinusD_sq
  · apply Subtype.ext
    rw [coe_conjK]
    exact D.host.conj_sqrtMinusD
  · intro x
    obtain ⟨a, b, h⟩ := exists_coords D x.2
    exact ⟨a, b, Subtype.ext (by simpa using h)⟩
  · have h := (Formalism.L2.Pj.LPb.w0K D).2
    convert h using 1
    first | rfl | (apply Subtype.ext; simp [Formalism.L2.Pj.LPb.w0K])

end GlobalTheory.QuadSubfield
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOneStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imaginary_quadratic_field_structure : ∀ D : D7, Module.finrank D.host.K D.host.E = fF D ∧ ∃ (σ : D.host.K →+* D.host.K) (θ : D.host.K), (∀ x : D.host.K, ((σ x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E)) ∧ θ ^ 2 = -(D.host.d : D.host.K) ∧ σ θ = -θ ∧ (∀ x : D.host.K, ∃ a b : ℚ, x = (a : D.host.K) + (b : D.host.K) * θ) ∧ IsIntegral ℤ ((1 + θ) / 2) ∧ (∀ y : D.host.E, D.host.conj (D.host.conj y) = y) ∧ (∀ y : D.host.E, Algebra.trace D.host.K D.host.E (D.host.conj y) = σ (Algebra.trace D.host.K D.host.E y)) ∧ ∀ y : D.host.E, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  first | exact @GlobalTheory.QuadSubfield.quadratic_subfield | exact GlobalTheory.QuadSubfield.quadratic_subfield | (intros; apply GlobalTheory.QuadSubfield.quadratic_subfield <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIdxOfParallelSig
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WittIndexParallel
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParallelSig {D : D7} (V : HSp D) (p q : ℕ) : Prop :=
  ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (V.gram.map τ) p q

theorem parallelSig_of_sigOK {D : D7} {V : HSp D} {p q : ℕ} (h : V.SigOK) (hs : ∀ τ, V.sig τ = (p, q)) :
    ParallelSig V p q := fun τ => by
  have := h τ
  rwa [hs τ] at this

end GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

end
end

noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH

namespace GlobalTheory.ParallelWitt

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem embedding_star (τ : E →+* ℂ) (a : E) : τ (star a) = star (τ a) :=
  IsCMField.complexEmbedding_complexConj E τ a

theorem form_eq {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (x y : Fin S.rank → E) :
    S.hT (S.frame.equivFun.symm x) (S.frame.equivFun.symm y) = star x ⬝ᵥ (S.gram *ᵥ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, starRingEnd_apply, dotProduct, mulVec, HSpace.gram, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem finrank_le (S : HSpace E) {p q : ℕ} (τ : E →+* ℂ) (hs : Formalism.UG.HasSignature (S.gram.map τ) p q)
    (U : Submodule E S.V) (hU : ∀ x ∈ U, ∀ y ∈ U, S.hT x y = 0) : Module.finrank E U ≤ q := by
  let b := Module.finBasis E U
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  let M := LinearMap.toMatrix b S.frame U.subtype
  let L := LinearMap.toMatrix S.frame b g
  have hL : L * M = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  have hb : ∀ i, (b i : S.V) = ∑ a, M a i • S.frame a := by
    intro i
    simp only [M, LinearMap.toMatrix_apply, Submodule.subtype_apply]
    exact (S.frame.sum_repr _).symm
  have h : Mᴴ * S.gram * M = 0 := by
    ext i j
    have h0 := hU _ (b i).2 _ (b j).2
    rw [hb i, hb j] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      starRingEnd_apply] at h0
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, HSpace.gram, Matrix.zero_apply]
    rw [← h0]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine (GlobalTheory.WittSignature.le_of_isotropic_signature _ hs (M.map τ) (L.map τ) ?_ ?_).2
  · rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero τ) (map_one τ)]
  · have : (M.map τ)ᴴ = (Mᴴ).map τ := by
      ext i j
      simp [Matrix.conjTranspose_apply, embedding_star]
    rw [this, ← Matrix.map_mul, ← Matrix.map_mul, h, Matrix.map_zero _ (map_zero τ)]

end CM

open GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.ParallelWitt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpBallUMemNhds
open Formalism.BasicNotions MeasureTheory Filter Topology

namespace GlobalTheory.ExpBallNhds

theorem exp_local_algebra (A : Type) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    (∃ S ∈ 𝓝 (0 : A), Set.InjOn (NormedSpace.exp : A → A) S) ∧
      Filter.map (NormedSpace.exp : A → A) (𝓝 0) = 𝓝 1 := by
  have h : HasStrictFDerivAt (NormedSpace.exp : A → A)
      ((ContinuousLinearEquiv.refl ℂ A : A ≃L[ℂ] A) : A →L[ℂ] A) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := A)
  refine ⟨⟨(h.toOpenPartialHomeomorph _).source, ?_, ?_⟩, ?_⟩
  · exact (h.toOpenPartialHomeomorph _).open_source.mem_nhds h.mem_toOpenPartialHomeomorph_source
  · have := (h.toOpenPartialHomeomorph _).injOn
    simpa using this
  · have := h.map_nhds_eq_of_equiv
    rwa [NormedSpace.exp_zero] at this

theorem exp_local_matrix (n : Type) [Fintype n] [DecidableEq n] :
    (∃ S ∈ 𝓝 (0 : Matrix n n ℂ), Set.InjOn (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) S) ∧
      Filter.map (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) (𝓝 0) = 𝓝 1 := by
  let : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  exact exp_local_algebra (Matrix n n ℂ)

private theorem exists_local_homeomorph_matrix_exp_source_zero {n : Type} [Fintype n] [DecidableEq n] :
    ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
      (0 : Matrix n n ℂ) ∈ e.source ∧ ⇑e = NormedSpace.exp := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)) 0 :=
    hasStrictFDerivAt_exp_zero
  exact ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source,
    hf.toOpenPartialHomeomorph_coe⟩

open Matrix in
theorem _root_.GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds : ∀ (P Q : ℕ) (r : ℝ), 0 < r →
    {g : _root_.Formalism.BasicNotions.UpqT P Q | ∃ X ∈ _root_.Formalism.BasicNotions.ballU P Q r,
      _root_.Formalism.BasicNotions.UpqT.mat g = NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} ∈
      𝓝 (1 : _root_.Formalism.BasicNotions.UpqT P Q) := by
  intro P Q r hr
  obtain ⟨e, h0, he⟩ := exists_local_homeomorph_matrix_exp_source_zero (n := Fin P ⊕ Fin Q)
  set J := _root_.Formalism.UG.Jpq P Q with hJ
  have hJJ : J * J = 1 := by
    rw [hJ]; unfold _root_.Formalism.UG.Jpq; simp [fromBlocks_multiply]
  have hJinv : J⁻¹ = J := Matrix.inv_eq_right_inv hJJ
  have hJunit : IsUnit J := ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
  set σ : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
    fun X => -(J * Xᴴ * J) with hσ
  have hσc : Continuous σ := by
    rw [hσ]
    exact ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
      continuous_const).neg
  have hσ0 : σ 0 = 0 := by simp [hσ]
  set N : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := {X | ∑ i, ∑ j, ‖X i j‖ < r} with hN
  have hNo : IsOpen N := isOpen_lt (by fun_prop) continuous_const
  have hU : e.source ∩ σ ⁻¹' e.source ∩ N ∈ 𝓝 (0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
    refine ((e.open_source.inter (e.open_source.preimage hσc)).inter hNo).mem_nhds ⟨⟨h0, ?_⟩, ?_⟩
    · show σ 0 ∈ e.source
      rw [hσ0]; exact h0
    · show ∑ i, ∑ j, ‖(0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j‖ < r
      simpa using hr
  have himg := e.image_mem_nhds h0 hU
  rw [he, NormedSpace.exp_zero] at himg
  have hmat : Continuous (fun g : _root_.Formalism.BasicNotions.UpqT P Q => _root_.Formalism.BasicNotions.UpqT.mat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hpre : (fun g : _root_.Formalism.BasicNotions.UpqT P Q => _root_.Formalism.BasicNotions.UpqT.mat g) ⁻¹'
      (NormedSpace.exp '' (e.source ∩ σ ⁻¹' e.source ∩ N)) ∈ 𝓝 (1 : _root_.Formalism.BasicNotions.UpqT P Q) :=
    hmat.continuousAt.preimage_mem_nhds himg
  filter_upwards [hpre] with g hg
  obtain ⟨X, ⟨⟨hXs, hσXs⟩, hXN⟩, hgX⟩ := hg
  beta_reduce at hgX
  have hgU : (_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g = J := g.2
  have hexpσ : NormedSpace.exp (σ X) = NormedSpace.exp X := by
    have hleft : J * (_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g = 1 := by
      rw [show J * (_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g = J * ((_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g)
        by simp only [mul_assoc], hgU, hJJ]
    rw [hσ]
    show NormedSpace.exp (-(J * Xᴴ * J)) = _
    have hc := Matrix.exp_conj J Xᴴ hJunit
    rw [hJinv] at hc
    rw [Matrix.exp_neg, hc, Matrix.exp_conjTranspose, hgX, Matrix.inv_eq_right_inv hleft]
  have hσX : σ X = X := e.injOn hσXs hXs (by rw [he]; exact hexpσ)
  have hJX : J * X = -(Xᴴ * J) := by
    conv_lhs => rw [← hσX]
    rw [hσ]
    show J * -(J * Xᴴ * J) = _
    rw [mul_neg, ← mul_assoc, ← mul_assoc, hJJ, one_mul]
  have hlie : X ∈ _root_.Formalism.BasicNotions.lieU P Q := by
    show Xᴴ * _root_.Formalism.UG.Jpq P Q + _root_.Formalism.UG.Jpq P Q * X = 0
    rw [← hJ, hJX, add_neg_cancel]
  exact ⟨⟨X, hlie⟩, hXN, hgX.symm⟩

end GlobalTheory.ExpBallNhds
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaEqProdSigmaStarSquareQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWpFEq
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem exists_wpF_eq : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ r : ℂ, ∃ Q, Q ∉ Λ ∧ wpF Λ Q = r := by
  intro Λ h r
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨z, hz, e⟩ := GlobalTheory.exists_weierstrassP_eq L r
  exact ⟨z, (hL z).not.2 hz, (GlobalTheory.OddTheta.wpF_eq L Λ hL z).trans e⟩

end GlobalTheory.EvenTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaEqProdSigmaStarSquareQuotient
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

open Polynomial

variable {Λ : AddSubgroup ℂ}

theorem IsLat.wpF_add_of_mem (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    wpF Λ (z + ω) = wpF Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.wpF_eq L Λ hL, GlobalTheory.OddTheta.wpF_eq L Λ hL]
  exact L.weierstrassP_add_coe z ⟨ω, (hL ω).1 hω⟩

theorem IsLat.entire_eq_of_periodic (h : IsLat Λ) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hper : ∀ ω ∈ Λ, ∀ z, F (z + ω) = F z) (z : ℂ) : F z = F 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  exact hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hF.continuous
      fun z w hw => hper w ((hL w).2 hw) z).isBounded z 0

theorem IsLat.sqTh_law (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    sqTh Λ v (z + ω) * sgStar Λ z ^ 2 = sqTh Λ v z * sgStar Λ (z + ω) ^ 2 := by
  by_cases hz : z ∈ Λ
  · rw [(h.sg_eq_zero z).2 hz, (h.sg_eq_zero _).2 (add_mem hz hω)]
    simp
  · have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using sub_mem h' hω)
    rw [h.sqTh_eq hv hz, h.sqTh_eq hv hz', h.wpF_add_of_mem hω]
    ring

theorem IsLat.exists_poly_wp (h : IsLat Λ) (k : ℕ) : ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ z, F (-z) = F z) →
    (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) →
    ∃ P : ℂ[X], P.natDegree ≤ k ∧ P.coeff k = F 0 ∧
      ∀ z ∉ Λ, F z = sgStar Λ z ^ (2 * k) * P.eval (wpF Λ z) := by
  induction k with
  | zero =>
    intro F hF _ hlaw
    refine ⟨C (F 0), by simp, by simp, fun z _ => ?_⟩
    simpa using h.entire_eq_of_periodic hF (fun ω hω z => by simpa using hlaw ω hω z) z
  | succ k ih =>
    intro F hF he hlaw
    obtain ⟨v, hv⟩ := h.dense_compl.nonempty
    have hv : v ∉ Λ := hv
    have hd := h.differentiable_sqTh v
    obtain ⟨G, hG, hGe, hFG, hGl⟩ := GlobalTheory.EvenTheta.exists_eq_sg_sq_mul Λ h k
      (fun z => F z - F 0 * sqTh Λ v z ^ (k + 1)) (by fun_prop)
      (fun z => by simp only [he, sqTh_neg]) (by simp [h.sqTh_zero hv])
      (fun ω hω z => by
        have h1 := congrArg (· ^ (k + 1)) (h.sqTh_law hv hω z)
        simp only [mul_pow, ← pow_mul] at h1
        linear_combination hlaw ω hω z - F 0 * h1)
    obtain ⟨P, hP, -, hPG⟩ := ih G hG hGe hGl
    have hm : ((X - C (wpF Λ v)) ^ (k + 1) : ℂ[X]).Monic := (monic_X_sub_C _).pow _
    have hdeg : ((X - C (wpF Λ v)) ^ (k + 1) : ℂ[X]).natDegree = k + 1 := by
      rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    refine ⟨C (F 0) * (X - C (wpF Λ v)) ^ (k + 1) + P, ?_, ?_, fun z hz => ?_⟩
    · refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans hdeg.le) (by omega)
    · have h1 := hm.coeff_natDegree
      rw [hdeg] at h1
      rw [coeff_add, coeff_C_mul, h1, coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k + 1)]
      simp
    · have h1 := hFG z
      simp only [hPG z hz, h.sqTh_eq hv hz, mul_pow, ← pow_mul] at h1
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
      linear_combination h1

theorem exists_eval_eq_prod_fin {k : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ k) (h1 : P.coeff k = 1) :
    ∃ r : Fin k → ℂ, ∀ x, P.eval x = ∏ i, (x - r i) := by
  have hdeg : P.natDegree = k := natDegree_eq_of_le_of_coeff_ne_zero hP (by rw [h1]; exact one_ne_zero)
  have hm : P.Monic := by rw [Monic, leadingCoeff, hdeg, h1]
  have hs : P.Splits := IsAlgClosed.splits P
  have he := hs.eq_prod_roots_of_monic hm
  have hc := hs.natDegree_eq_card_roots
  obtain ⟨l, hl⟩ := Quotient.exists_rep P.roots
  have hl : (l : Multiset ℂ) = P.roots := hl
  rw [← hl] at he hc
  rw [hdeg, Multiset.coe_card] at hc
  subst hc
  refine ⟨fun i => l[i.1]'i.2, fun x => ?_⟩
  rw [he, eval_multiset_prod, Multiset.map_map, Multiset.map_coe, Multiset.prod_coe]
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  exact (Fin.prod_univ_fun_getElem l fun a => x - a).symm

theorem exists_eq_prod_sqTh : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 1 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ) ∧ ∀ z, F z = ∏ i, sqTh Λ (Q i) z := by
  intro Λ h k F hF he h0 hlaw
  obtain ⟨P, hP, hc, hPF⟩ := h.exists_poly_wp k F hF he hlaw
  obtain ⟨r, hr⟩ := exists_eval_eq_prod_fin hP (hc.trans h0)
  choose Q hQ hQr using fun i => GlobalTheory.EvenTheta.exists_wpF_eq Λ h (r i)
  refine ⟨Q, hQ, fun z => ?_⟩
  refine congrFun (Continuous.ext_on h.dense_compl hF.continuous
    (g := fun z => ∏ i, sqTh Λ (Q i) z)
    (continuous_finsetProd _ fun i _ => (h.differentiable_sqTh (Q i)).continuous) fun z hz => ?_) z
  have hz : z ∉ Λ := hz
  beta_reduce
  simp only [h.sqTh_eq (hQ _) hz, hQr, hPF z hz, hr, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]

end GlobalTheory.EvenTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaEqProdSigmaStarSquareQuotientStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenTheta_eq_prod_sigmaStarSquareQuotient : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 1 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ) ∧ ∀ z, F z = ∏ i, sqTh Λ (Q i) z := by
  first | exact @GlobalTheory.EvenTheta.exists_eq_prod_sqTh | exact GlobalTheory.EvenTheta.exists_eq_prod_sqTh | (intros; apply GlobalTheory.EvenTheta.exists_eq_prod_sqTh <;> assumption)
end
end
