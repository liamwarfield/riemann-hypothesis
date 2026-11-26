module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthCommonDenominatorRankLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionEstimateOffCentreCell
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTruthOfLabelTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanMarkedFormUniqueInCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExistsMarkedFormInCell

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionFunctionIntegralStrictlyCon
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionFunctionIntegralStrictlyCon
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey

theorem exists_starFun_strict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ K D : ℕ, 0 < K ∧ 0 < D ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (starFun H.bar ψ w K D).evalZ β = n) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsStrict H.bar (starFun H.bar ψ w K D) γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsStrict H.bar (starFun H.bar ψ w K D) (Fin.cons β₀ fun j => γ (s j))) := by
  intro E _ _ _ H q ψ w hdom hψ hcs
  obtain ⟨D₀, hD₀, hint⟩ := GlobalTheory.T.starDepth_common_denominator_rank_le E H q ψ w hψ hcs
  obtain ⟨N₀, C₀, hdata⟩ := GlobalTheory.T.exists_uniform_strictness_and_face_cut_bounds E H q ψ hdom hψ
  obtain ⟨b, hgens⟩ := GlobalTheory.T.exists_bounded_generators_star_subdivision_cone E H q ψ w hψ hcs
  have hD₀r : (0 : ℝ) < D₀ := by exact_mod_cast hD₀
  refine ⟨N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1, D₀, by omega, hD₀, ?_, ?_, ?_⟩
  · intro X _ _ _ _ hX β hβ hp
    obtain ⟨n₁, hn₁⟩ := (hψ X hX).integral β hβ hp
    obtain ⟨n₂, hn₂⟩ := hint X hX β hβ hp
    refine ⟨D₀ * (N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1) * n₁ + n₂, ?_⟩
    rw [starFun_evalZ, hn₁]
    push_cast
    linear_combination hn₂
  · intro X _ _ _ _ hX m γ hγ hnoc
    obtain ⟨N, ℓ, hN, hNN, hsw, -⟩ := hdata X hX m γ hγ
    have hgap := GlobalTheory.T.starDepth_le_strictnessGap_off_centres E H q ψ w hψ hcs X hX m γ N ℓ hγ hnoc hN hsw
    have hnn : ∀ β : LinearMap.BilinForm ℤ X, 0 ≤ (starDepth H.bar ψ w).evalZ β := fun β =>
      starDepth_eval_nonneg (fun a b => (β a b : ℝ))
    set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef
    have hKN : (N : ℝ) + 1 ≤ K := by
      have : N + 1 ≤ K := by rw [hKdef]; omega
      exact_mod_cast this
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    refine ⟨N, ((D₀ * K : ℕ) : ℤ) • ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · have h0 := hsw.1 i
      have hps : (starDepth H.bar ψ w).evalZ (γ i) = 0 :=
        le_antisymm (by have := hgap (γ i) (hγ.mem i) (hγ.nonneg i); linarith) (hnn _)
      rw [starFun_evalZ, hps]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      push_cast
      rw [h0]; ring
    · have hg := hgap β hβ hp
      have hf := hsw.2.1 β hβ hp
      have hps := hnn β
      rw [starFun_evalZ]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      push_cast
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      set L : ℝ := (ℓ β : ℝ)
      have k1 : (N : ℝ) * P ≤ K * (L - N * Ψ) := by nlinarith [mul_le_mul_of_nonneg_left hg hN0]
      nlinarith [mul_le_mul_of_nonneg_left k1 hD₀r.le]
    · have hg := hgap β hβ hp
      have hf := hsw.2.1 β hβ hp
      have hps := hnn β
      rw [starFun_evalZ] at he
      simp only [LinearMap.smul_apply, smul_eq_mul] at he
      push_cast at he
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      set L : ℝ := (ℓ β : ℝ)
      have e1 : (N : ℝ) * P = K * (L - N * Ψ) := by
        have := mul_left_cancel₀ hD₀r.ne' (show (D₀ : ℝ) * (N * P) = D₀ * (K * (L - N * Ψ)) by linear_combination he)
        exact this
      have e2 : L - N * Ψ = 0 := by nlinarith [mul_le_mul_of_nonneg_left hg hN0]
      exact hsw.2.2 β hβ hp (by linarith)
  · intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hpos
    obtain ⟨N, ℓ, hN, hNN, hsw, hcuts⟩ := hdata X hX m γ hγ
    obtain ⟨h', hcut', hpos', hdom'⟩ := hcuts m' s h hcut
    have hp' : 0 < h' β₀ := hpos' β₀ hin₀ hpos
    obtain ⟨hin, hone, hzero, heq⟩ :=
      GlobalTheory.T.starDepth_le_on_centre_cell E H q ψ w hψ hcs X hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h' hcut' hp'
    set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef
    have hKb : N + N * C₀ + N ^ 2 * C₀ * b + 1 ≤ K := by
      rw [hKdef]
      have h1 : N * C₀ ≤ N₀ * C₀ := Nat.mul_le_mul_right _ hNN
      have h2 : N ^ 2 * C₀ * b ≤ N₀ ^ 2 * C₀ * b :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hNN 2))
      omega
    have hoff := GlobalTheory.T.star_subdivision_estimate_off_centre_cell E H q ψ w b hψ hcs X hX (hgens X hX) m γ N ℓ hγ hN hsw β₀ hβ₀ hp₀ hw₀ hin₀ m' s h'
      hcut' hp' C₀ hdom' K hKb
    have hlinγ : ∀ β, InRCone γ β → (ℓ β : ℝ) = N * ψ.evalZ β := fun β hβ => StarKey.ell_eq_of_inRCone hγ.linear hsw hβ
    have hcast : (((h' β₀).toNat : ℕ) : ℝ) = (h' β₀ : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hp'.le]
    have hH0 : (0 : ℝ) < h' β₀ := by exact_mod_cast hp'
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    refine ⟨N * (h' β₀).toNat, (D₀ : ℤ) • (((K : ℤ) * h' β₀) • ℓ + (N : ℤ) • h'), by
      have : 0 < (h' β₀).toNat := by omega
      positivity, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        rw [starFun_evalZ, hone]
        have hl := hlinγ β₀ hin₀
        simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
        push_cast
        rw [hcast, hl]; ring
      · simp only [Fin.cons_succ]
        have hh : h' (γ (s j)) = 0 := (hcut'.2 (s j)).2 ⟨j, rfl⟩
        rw [starFun_evalZ, hzero j]
        simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, hh]
        push_cast
        rw [hcast, hsw.1 (s j)]; ring
    · rw [starFun_evalZ]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
      push_cast
      rw [hcast]
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      by_cases hc : InRCone γ β
      · have hl := hlinγ β hc
        have hi := hin β hβ hp hc
        rw [hl]
        nlinarith [mul_le_mul_of_nonneg_left hi (mul_nonneg hD₀r.le hN0.le)]
      · have ho := hoff β hβ hp hc
        nlinarith [mul_lt_mul_of_pos_left ho hD₀r]
    · rw [starFun_evalZ] at he
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at he
      push_cast at he
      rw [hcast] at he
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      by_cases hc : InRCone γ β
      · have hl := hlinγ β hc
        rw [hl] at he
        refine heq β hβ hp hc ?_
        have : ((D₀ : ℝ) * N) * ((h' β₀ : ℝ) * P) = ((D₀ : ℝ) * N) * (h' β : ℝ) := by linear_combination he
        exact mul_left_cancel₀ (mul_pos hD₀r hN0).ne' this
      · have ho := hoff β hβ hp hc
        nlinarith [mul_lt_mul_of_pos_left ho hD₀r]

end GlobalTheory.PolFan.StarKey
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionFunctionIntegralStrictlyConStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_starSubdivision_function_integral_strictly_concave : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ K D : ℕ, 0 < K ∧ 0 < D ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (starFun H.bar ψ w K D).evalZ β = n) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsStrict H.bar (starFun H.bar ψ w K D) γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsStrict H.bar (starFun H.bar ψ w K D) (Fin.cons β₀ fun j => γ (s j))) := by
  first | exact @GlobalTheory.PolFan.StarKey.exists_starFun_strict | exact GlobalTheory.PolFan.StarKey.exists_starFun_strict | (intros; apply GlobalTheory.PolFan.StarKey.exists_starFun_strict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralCharacterIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralGroupAlgebraOpPreservesIntegralLevelForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralGroupAlgebraOpPreservesIntegralLevelForms
set_option autoImplicit false

noncomputable section

open NumberField
open scoped Matrix ComplexOrder

namespace GlobalTheory.CentralLevelOp

open Formalism.DivisionValues _root_.Formalism.L2.DIV

theorem lvlOp_mem_lvlNab : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : NumberField.InfinitePlace K), Formalism.DivisionValues.IsConjAt v0 →
    ∀ (S : Formalism.L2.DIV.CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ) (a : MonoidAlgebra K G), (∀ b, a * b = b * a) → (∀ t : G, ∃ n : ℤ, a.coeff t = n) →
    ∀ x ∈ S.lvlNab r P ψ, (S.lvlOp r P ψ a).mulVec x ∈ S.lvlNab r P ψ := by
  intro K _ _ _ v0 h0 S hH G _ _ r hr P ψ a hc hz x hx
  have hE := (level_operator_spec K v0 h0 S hH G r hr P ψ a (hc _)).1
  change (S.lvlE r P ψ).mulVec x ∈ S.nabLat at hx
  change (S.lvlE r P ψ).mulVec ((S.lvlOp r P ψ a).mulVec x) ∈ S.nabLat
  rw [Matrix.mulVec_mulVec, hE, ← Matrix.mulVec_mulVec, CSD.gaMat, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun t _ => ?_
  obtain ⟨n, hn⟩ := hz t
  rw [Matrix.smul_mulVec, hn, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_of_tower_mem _ n ((action_preserves_lattice K S G r hr t).1 _ hx)

end GlobalTheory.CentralLevelOp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralGroupAlgebraOpPreservesIntegralLevelFormsStatement
open NumberField
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralGroupAlgebraOp_preserves_integralLevelForms : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : NumberField.InfinitePlace K), Formalism.DivisionValues.IsConjAt v0 →
    ∀ (S : Formalism.L2.DIV.CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ) (a : MonoidAlgebra K G), (∀ b, a * b = b * a) → (∀ t : G, ∃ n : ℤ, a.coeff t = n) →
    ∀ x ∈ S.lvlNab r P ψ, (S.lvlOp r P ψ a).mulVec x ∈ S.lvlNab r P ψ := by
  first | exact @GlobalTheory.CentralLevelOp.lvlOp_mem_lvlNab | exact GlobalTheory.CentralLevelOp.lvlOp_mem_lvlNab | (intros; apply GlobalTheory.CentralLevelOp.lvlOp_mem_lvlNab <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open scoped Matrix ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.CenIntAtLoc

open _root_.Formalism.L2.DIV

theorem mapCoef_mem_center {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) (z : MonoidAlgebra R G)
    (hz : ∀ a, z * a = a * z) :
    Formalism.MainNotions.PairedCharacterCondition.mapCoef f z ∈ Subalgebra.center S (MonoidAlgebra S G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    have e : MonoidAlgebra.of S G m = MonoidAlgebra.mapRingHom G f (MonoidAlgebra.of R G m) := by
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]
    rw [e]
    show MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _ =
      MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _
    rw [← map_mul, ← map_mul, hz]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem coeff_mapCoef {R S M : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : MonoidAlgebra R M) (m : M) :
    (Formalism.MainNotions.PairedCharacterCondition.mapCoef f z).coeff m = f (z.coeff m) := by
  simp [Formalism.MainNotions.PairedCharacterCondition.mapCoef]

theorem cenInt_of_allT {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G}
    {ψ1 : P1 →* D.what₂.LLˣ} {X0 : BaseLevelRowSide D} {tp : D.what₂.Tup → T} {eG : G ≃* G0g D.nd}
    (h : AllT D A P0 ψ0 P1 ψ1 X0 tp eG) (v : InfinitePlace D.what₂.LL) (hv : Formalism.DivisionValues.IsConjAt v)
    (hpos : ∀ k τ, ((A.fam.L k τ).S.H.map v.embedding).PosDef)
    (hact : ∀ k τ, (A.fam.L k τ).S.ActGood (A.fam.L k τ).r) : GlobalTheory.PendOf.CenInt D := by
  intro i z hz x hx
  have hc := mapCoef_mem_center (Int.castRingHom ℂ) z hz
  have key : ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ x ∈ GlobalTheory.EtaJoin.genSet D μ j,
      ∃ y ∈ GlobalTheory.EtaJoin.lat D μ j, D.what₂.jMt μ j y = D.ntypes.cenMt μ j ⟨_, hc⟩ (D.what₂.jMt μ j x) := by
    intro μ j h1 h2 x hx
    obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
    let a : MonoidAlgebra D.what₂.LL G :=
      MonoidAlgebra.mapDomainRingEquiv D.what₂.LL eG.symm (Formalism.MainNotions.PairedCharacterCondition.mapCoef (Int.castRingHom D.what₂.LL) z)
    have hcoef : ∀ g : G, a.coeff g = ((z.coeff (eG g) : ℤ) : D.what₂.LL) := by
      intro g
      simp [a, coeff_mapCoef]
    have ha : ∀ g : G, D.what₂.embLL (a.coeff g) =
        ((⟨_, hc⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g) := by
      intro g
      rw [hcoef g]
      simp [coeff_mapCoef]
    have hcL := mapCoef_mem_center (Int.castRingHom D.what₂.LL) z hz
    have hac : ∀ b, a * b = b * a := by
      intro b
      obtain ⟨b', rfl⟩ := (MonoidAlgebra.mapDomainRingEquiv D.what₂.LL eG.symm).surjective b
      simp only [a, ← map_mul]
      rw [Subalgebra.mem_center_iff.mp hcL b']
    have hint : ∀ t : G, ∃ n : ℤ, a.coeff t = n := fun t => ⟨_, hcoef t⟩
    obtain ⟨-, -, h3⟩ := h.cen μ ⟨_, hc⟩ a ha
    classical
    have h3' := h3 k ((h.eMt k μ).symm x)
    rw [LinearEquiv.apply_symm_apply] at h3'
    obtain ⟨hgen, hlat⟩ := h.latL k μ
    have hx' : (h.eMt k μ).symm x ∈ lNab D A P0 ψ0 k (tp μ) := by
      rw [hlat]
      refine ⟨fun v => if v = D.what₂.jMt μ ((k : ℕ) + 1) x then 1 else 0, ?_⟩
      have hxg : D.what₂.jMt μ ((k : ℕ) + 1) x ∈ (D.what₂.MtLat μ ((k : ℕ) + 1)).gen := hx
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply]
      rw [Finset.sum_eq_single_of_mem _ hxg]
      · simp
      · intro b _ hb
        simp [hb]
    have hy' := GlobalTheory.T.centralGroupAlgebraOp_preserves_integralLevelForms D.what₂.LL v hv (A.fam.L k (tp μ)).S (hpos k (tp μ)) G (A.fam.L k (tp μ)).r (hact k (tp μ))
      (A.fam.lvlA P0 ψ0).P (A.fam.lvlA P0 ψ0).ψ a hac hint _ hx'
    obtain ⟨c, hc'⟩ := (hlat _).mp hy'
    have hsrc : ∀ u : (D.what₂.MtLat μ ((k : ℕ) + 1)).gen, ∃ w, D.what₂.jMt μ ((k : ℕ) + 1) (h.eMt k μ w) = u.1 := by
      intro u
      obtain ⟨w, hw⟩ := hgen u.1 u.2
      exact ⟨w, hw⟩
    choose ws hws using hsrc
    refine ⟨∑ u ∈ (D.what₂.MtLat μ ((k : ℕ) + 1)).gen.attach, c u.1 • h.eMt k μ (ws u), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      show D.what₂.jMt μ ((k : ℕ) + 1) (h.eMt k μ (ws u)) ∈ (D.what₂.MtLat μ ((k : ℕ) + 1)).gen
      rw [hws u]
      exact u.2
    · rw [h3']
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at hc'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hc', map_sum, ← Finset.sum_attach (D.what₂.MtLat μ ((k : ℕ) + 1)).gen]
      refine Finset.sum_congr rfl fun u _ => ?_
      have e1 : c u.1 • h.eMt k μ (ws u) = ((c u.1 : 𝓞 D.what₂.LL) : D.what₂.LL) • h.eMt k μ (ws u) := rfl
      rw [e1, LinearMap.map_smulₛₗ, hws u]
  obtain ⟨y, hy, hyx⟩ := key (D.nd.mu i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 x hx
  refine ⟨y, hy, ?_⟩
  rw [hyx]
  unfold NTypes.onMt
  rw [dite_eq_left hc]

end GlobalTheory.CenIntAtLoc

namespace GlobalTheory.CenIntAtLoc

end GlobalTheory.CenIntAtLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowDepthOfPrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemIsot
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowFix

open _root_.Formalism.L2.NG Formalism.IndefR.principalLevelFrame

theorem exists_fixed_of_mem_isot {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A)
    (π : FinTyp L n) (Q : (π.S →ₗ[ℂ] A) → Prop) (Kp : Formalism.AUTREP.GAf L n → Prop) {y : A}
    (hy : y ∈ ⨆ (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ ∧ Q Φ), LinearMap.range Φ) (hy0 : y ≠ 0)
    (hfix : ∀ κ, Kp κ → ρ κ y = y) :
    ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f := by
  classical
  let ι := {Φ : π.S →ₗ[ℂ] A // IsEqvA ρ π Φ ∧ Q Φ}
  have hy' : y ∈ ⨆ j : ι, LinearMap.range j.1 := by
    rwa [iSup_subtype'] at hy
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hy'
  let Y : Finset ι → Submodule ℂ A := fun t => ⨆ j ∈ t, LinearMap.range j.1
  have hYst : ∀ (t : Finset ι) (g : Formalism.AUTREP.GAf L n) (x : A), x ∈ Y t → ρ g x ∈ Y t := by
    intro t g x hx
    have hle : Y t ≤ (Y t).comap (ρ g) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap, ← j.2.1 g v]
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => LinearMap.range j.1) j hj) (LinearMap.mem_range_self _ _)
    exact hle hx
  have key : ∀ (t : Finset ι) (x : A), x ∈ Y t → x ≠ 0 → (∀ κ, Kp κ → ρ κ x = x) →
      ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx hx0 _
      exact absurd (by simpa [Y] using hx) hx0
    | insert j t hjt ih =>
      intro x hx hx0 hxfix
      have hx' : x ∈ LinearMap.range j.1 ⊔ Y t := by
        simpa [Y, Finset.iSup_insert] using hx
      obtain ⟨_, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      let U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := ((Y t).comap j.1).map π.S.subtype
      have hUst : ∀ h, ∀ f ∈ U, rt L n h f ∈ U := by
        rintro h _ ⟨a, ha, rfl⟩
        refine ⟨⟨rt L n h a, π.stable h a a.2⟩, ?_, rfl⟩
        have ha' : j.1 a ∈ Y t := ha
        show j.1 _ ∈ Y t
        rw [j.2.1 h a]
        exact hYst t h _ ha'
      rcases π.irr U (Submodule.map_subtype_le _ _) hUst with hU | hU
      ·
        have hvfix : ∀ κ, Kp κ → rt L n κ (v : Formalism.AUTREP.GAf L n → ℂ) = v := by
          intro κ hκ
          let v' : π.S := ⟨rt L n κ v, π.stable κ v v.2⟩
          have hmem : v' - v ∈ (Y t).comap j.1 := by
            rw [Submodule.mem_comap, map_sub, j.2.1 κ v]
            have h1 := hxfix κ hκ
            rw [map_add (f := _)] at h1
            have h3 : ρ κ (j.1 v) - j.1 v = z - ρ κ z := by
              rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
            rw [h3]
            exact sub_mem hz (hYst t κ z hz)
          have hU' : ((v' - v : π.S) : Formalism.AUTREP.GAf L n → ℂ) ∈ U := ⟨_, hmem, rfl⟩
          rw [hU, Submodule.mem_bot] at hU'
          exact sub_eq_zero.1 hU'
        by_cases hv : (v : Formalism.AUTREP.GAf L n → ℂ) = 0
        · have hv' : v = 0 := Subtype.ext hv
          subst hv'
          simp only [map_zero, zero_add] at hx0 hxfix
          exact ih z hz hx0 hxfix
        · exact ⟨v, v.2, hv, hvfix⟩
      · have hvU : (v : Formalism.AUTREP.GAf L n → ℂ) ∈ U := by rw [hU]; exact v.2
        obtain ⟨a, ha, hav⟩ := hvU
        have : a = v := Subtype.ext hav
        subst this
        exact ih _ (add_mem ha hz) hx0 hxfix
  exact key s y (by simpa [Y] using hs) hy0 hfix

theorem exists_fixed_rowRep : ∀ (D : D7) (V : HSp D) (n : ℕ) (Sp : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : principalLevelFrame.RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ) (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (σ : principalLevelFrame.FTR θ P M J χ e) (Kp : Formalism.AUTREP.GAf D.host.E n → Prop), (∀ b κ, Kp κ → P.ψ κ ∈ J b ∧ χ b (P.ψ κ) = 1) → ∃ f ∈ (principalLevelFrame.rowRepR θ σ).S, f ≠ 0 ∧ ∀ κ, Kp κ → NG.rt D.host.E n κ f = f := by
  intro D V n Sp θ P M J χ e σ Kp hK
  obtain ⟨b, hb⟩ := rowRepR_occ θ σ
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hy' : y ∈ Formalism.IndefR.Mult.goodPart θ M (J b) (χ b) (e b) ⊓
      isotIn (actM P M) (Minf θ P M) (FinTyp.conjT (rowRepR θ σ)) := hy
  rw [Submodule.mem_inf] at hy'
  have hM : y ∈ Formalism.IndefR.Mult.Mult θ M (J b) (χ b) := (Submodule.mem_inf.1 hy'.1).1
  have hfixY : ∀ κ, Kp κ → actM P M κ y = y := by
    intro κ hκ
    have hle : Formalism.IndefR.Mult.Mult θ M (J b) (χ b) ≤ LinearMap.ker (actM P M κ - LinearMap.id) := by
      refine Submodule.span_le.2 ?_
      intro T hT
      have hT' : Formalism.IndefR.Mult.IsMultMap θ M (J b) (χ b) T := hT
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      apply MultilinearMap.ext
      intro v
      funext g
      rw [actM_apply, hT'.lev v _ (hK b κ hκ).1 g, (hK b κ hκ).2, one_mul]
    have h := hle hM
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
    exact h
  obtain ⟨f, hf, hf0, hffix⟩ := exists_fixed_of_mem_isot (actM P M) (FinTyp.conjT (rowRepR θ σ))
    (fun Φ => LinearMap.range Φ ≤ Minf θ P M) Kp hy'.2 hy0 hfixY
  refine ⟨fun g => star (f g), (mem_conjSub).1 hf, ?_, fun κ hκ => ?_⟩
  · intro h0
    apply hf0
    funext g
    have := congrFun h0 g
    simpa using this
  · rw [← conj_rt, hffix κ hκ]

end GlobalTheory.RowFix
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowDepthTrue


set_option maxHeartbeats 1000000 in
theorem rowDepth_rowRepR : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → D.host.F = maximalRealSubfield D.host.E →
    GlobalTheory.HeightCounting.RowDepth D (fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) := by
  intro hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHo hF σ k v
  obtain ⟨s, hs⟩ := GlobalTheory.FixedPlaceOverType.exists_splitPlace_w_plGw D k v
  obtain ⟨τ, hτ⟩ := GlobalTheory.RowLocalRows2.finTyp_rows_exists_isLocS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHo hF σ s
  have hβ := hP.char.base.lev.βY 0 Y.hm
  obtain ⟨h, hA⟩ := GlobalTheory.RowLevelSplit.lemA_pf
    (GlobalTheory.RowLevelSplit.stdFrame_splitPlace_entries_off_place GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one GlobalTheory.ConjLt.frame_mat_sub_one_lt GlobalTheory.SplitFrameW.main
      GlobalTheory.PlaceOverSplit.eq_or_eq_cP) D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) _ _ Y.stdPsi.1 hβ s
  have hh : ∀ (b : Bool) (κ : Formalism.AUTREP.GAf D.host.E D.R.r), TrivOutside {s.v} κ →
      h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) →
      Y.PY.ψ κ ∈ levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) ∧
        levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) (Y.PY.ψ κ) = 1 := by
    intro b κ hκ hk
    classical
    exact GlobalTheory.RowLevelSplit.lemB_pf D (Yc D 0) (R.βY 0) _ (_ ∪ _) (Y.PY.ψ κ) Finset.subset_union_left
      Finset.subset_union_right (Y.PY.into κ) (hA κ hκ hk _)
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.RowFix.exists_fixed_rowRep D (Yc D 0) D.R.r _ R.θ Y.PY (R.MY 0) _ _ _ (Y.eFT σ)
    (fun κ => TrivOutside {s.v} κ ∧
      h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r))
    (fun b κ hκ => hh b κ hκ.1 hκ.2)
  exact ⟨s, τ, hs, hτ, GlobalTheory.RowLevelSplitData.fixed_ne_bot_of_fixed_vector_conj D.host.E D.R.r _ s τ h hτ f hfS hf0
    (fun κ h1 h2 => hfix κ ⟨h1, h2⟩)⟩


open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up in
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl in
theorem stepW_of_ev {Q : Ctx → Prop} (h : Ev Q) (p : WP) : StepW p fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)



end GlobalTheory.RowDepthTrue

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorZeroOneBarycentresPolyFan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMarkedBalancedIntFormPullbackIffSplitSurjectio
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMarkedBalancedIntFormPullbackIffSplitSurjectio
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark.SplitPull

theorem apply_eq_zero_of_isotropic {X : Type} [AddCommGroup X] {x : LinearMap.BilinForm ℤ X}
    (hs : ∀ y z, x y z = x z y) (hp : ∀ y, 0 ≤ x y y) {d : X} (hd : x d d = 0) (z : X) : x d z = 0 := by
  by_contra h
  have h1 := hp ((-(x d z * (x z z + 1))) • d + z)
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hd, hs z d] at h1
  have h2 : 1 ≤ x d z * x d z := mul_self_pos.2 h
  have h3 := hp z
  nlinarith [mul_le_mul_of_nonneg_right h2 (show 0 ≤ x z z + 1 by omega)]

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O}
  {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
  {r : X →ₗ[O] X₁} {s : X₁ →ₗ[O] X}

def pullHom (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_pull (h : ∀ a, r (s a) = a) (β : LinearMap.BilinForm ℤ X₁) : pull s (pull r β) = β :=
  LinearMap.ext₂ fun a b => by simp [h]

theorem pull_injective (h : ∀ a, r (s a) = a) : Function.Injective (pull r) :=
  Function.LeftInverse.injective (pull_pull h)

theorem eq_pull (h : ∀ a, r (s a) = a) {β : LinearMap.BilinForm ℤ X₁} {x : LinearMap.BilinForm ℤ X}
    (hs : ∀ y z, x y z = x z y) (hp : ∀ y, 0 ≤ x y y) (hv : ∀ y, pull r β y y = 0 → x y y = 0) :
    pull r (pull s x) = x := by
  have key : ∀ a z, x (s (r a)) z = x a z := fun a z => by
    have := apply_eq_zero_of_isotropic hs hp (hv (a - s (r a)) (by simp [h])) z
    rw [map_sub, LinearMap.sub_apply] at this
    omega
  refine LinearMap.ext₂ fun a b => ?_
  rw [pull_apply, pull_apply, key, hs, key, hs]

variable [Module.Finite O X] [Module.Finite O X₁]

theorem inFace_pull_iff (h : ∀ a, r (s a) = a) {β x : LinearMap.BilinForm ℤ X₁} :
    InFace bar ψ lab (pull r β) (pull r x) ↔ InFace bar ψ lab β x := by
  have hr : Function.Surjective r := fun a => ⟨s a, h a⟩
  have e : pull r β + pull r x = pull r (β + x) := rfl
  unfold InFace
  rw [e]
  simp only [evalZ_pull _ hr, pull_apply]
  refine and_congr ⟨fun hx => ?_, pull_mem r⟩ (and_congr (hr.forall (p := fun y => 0 ≤ x y y)).symm
    (and_congr (hr.forall (p := fun y => β y y = 0 → x y y = 0)).symm Iff.rfl))
  rw [← pull_pull h x]
  exact pull_mem s hx

theorem InFace_eq_pull (h : ∀ a, r (s a) = a) {β : LinearMap.BilinForm ℤ X₁} {x : LinearMap.BilinForm ℤ X}
    (hx : InFace bar ψ lab (pull r β) x) : ∃ x₁, pull r x₁ = x :=
  ⟨_, eq_pull h hx.1.1 hx.2.1 hx.2.2.1⟩

theorem isIndec_pull_iff (h : ∀ a, r (s a) = a) {β x : LinearMap.BilinForm ℤ X₁} :
    IsIndec bar ψ lab (pull r β) (pull r x) ↔ IsIndec bar ψ lab β x := by
  have hne : ∀ y : LinearMap.BilinForm ℤ X₁, pull r y ≠ 0 ↔ y ≠ 0 := fun y =>
    (pull_injective h).ne_iff' (rfl : pull r 0 = 0)
  refine and_congr (inFace_pull_iff h) (and_congr (hne x) ⟨fun H y z hy hz y0 z0 e => ?_, fun H y z hy hz y0 z0 e => ?_⟩)
  · exact H _ _ ((inFace_pull_iff h).2 hy) ((inFace_pull_iff h).2 hz) ((hne y).2 y0) ((hne z).2 z0) (by rw [← e]; rfl)
  · obtain ⟨y, rfl⟩ := InFace_eq_pull h hy
    obtain ⟨z, rfl⟩ := InFace_eq_pull h hz
    exact H y z ((inFace_pull_iff h).1 hy) ((inFace_pull_iff h).1 hz) ((hne y).1 y0) ((hne z).1 z0)
      (pull_injective h e)

theorem isMarked_pull_iff' (h : ∀ a, r (s a) = a) (i : ℕ) (β : LinearMap.BilinForm ℤ X₁) :
    IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β := by
  classical
  have hr : Function.Surjective r := fun a => ⟨s a, h a⟩
  have hsum : ∀ S : Finset (LinearMap.BilinForm ℤ X₁), ∑ x ∈ S.map ⟨pull r, pull_injective h⟩, x = pull r (∑ x ∈ S, x) :=
    fun S => by
      rw [Finset.sum_map]
      exact (map_sum (pullHom r) (fun x => x) S).symm
  unfold IsMarked
  rw [evalZ_pull _ hr]
  refine and_congr ⟨fun hx => ?_, pull_mem r⟩ (and_congr (hr.forall (p := fun y => 0 ≤ β y y)).symm
    (and_congr ⟨fun H k β' e => H k (pull r β') (by rw [← e]; rfl), fun H k β' e => H k (pull s β') ?_⟩
      (and_congr Iff.rfl ⟨?_, ?_⟩)))
  · rw [← pull_pull h β]
    exact pull_mem s hx
  · rw [← pull_pull h β, ← e]; rfl
  · rintro ⟨S, hS, k, hk, e⟩
    have hS' : (S.preimage (pull r) (pull_injective h).injOn).map ⟨pull r, pull_injective h⟩ = S := by
      ext x
      simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
      refine ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ?_⟩
      obtain ⟨y, rfl⟩ := InFace_eq_pull h ((hS x).1 hx).1
      exact ⟨y, hx, rfl⟩
    refine ⟨S.preimage (pull r) (pull_injective h).injOn, fun x => ?_, k, hk, pull_injective h ?_⟩
    · rw [Finset.mem_preimage, hS, isIndec_pull_iff h]
    · rw [← hsum, hS', ← e]; rfl
  · rintro ⟨S, hS, k, hk, e⟩
    refine ⟨S.map ⟨pull r, pull_injective h⟩, fun x => ?_, k, hk, ?_⟩
    · simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (isIndec_pull_iff h).2 ((hS y).1 hy)
      · intro hx
        obtain ⟨y, rfl⟩ := InFace_eq_pull h hx.1
        exact ⟨y, (hS y).2 ((isIndec_pull_iff h).1 hx), rfl⟩
    · rw [hsum, ← e]; rfl

theorem isMarked_pull_iff : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) (X X₁ : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    (r : X →ₗ[O] X₁) (s : X₁ →ₗ[O] X), (∀ a, r (s a) = a) → ∀ β : LinearMap.BilinForm ℤ X₁,
    IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β :=
  fun _ _ _ _ _ i _ _ _ _ _ _ _ _ _ _ h β => isMarked_pull_iff' h i β

end GlobalTheory.PolFan.Mark.SplitPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMarkedBalancedIntFormPullbackIffSplitSurjectioStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) (X X₁ : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (s : X₁ →ₗ[O] X), (∀ a, r (s a) = a) → ∀ β : LinearMap.BilinForm ℤ X₁, IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β := by
  first | exact @GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff | exact GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff | (intros; apply GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorZeroOneBarycentresPolyFan
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem exists_markFun {O : Type} [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) :
    ∃ w : InvFun O, ∀ n B, w.toFun n B = markVal bar ψ lab i n B := by
  classical
  refine ⟨{ toFun := markVal bar ψ lab i, inv := ?_, zero := ?_ }, fun _ _ => rfl⟩
  · intro n m r hr B
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hrs : ∀ a, r (s a) = a := fun a => LinearMap.congr_fun hs a
    unfold markVal
    by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin m → O), ∀ a b, B a b = β a b
    · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (r a) (r b) = β a b :=
        ⟨pull r h.choose, fun a b => h.choose_spec _ _⟩
      rw [dite_eq_left h, dite_eq_left h']
      have e : h'.choose = pull r h.choose := LinearMap.ext₂ fun a b => by
        have h1 := h'.choose_spec a b
        have h2 := h.choose_spec (r a) (r b)
        rw [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [e, GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection O bar ψ lab i _ _ r s hrs]
    · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (r a) (r b) = β a b := by
        rintro ⟨β, h3⟩
        exact h ⟨pull s β, fun a b => by rw [pull_apply, ← h3, hrs, hrs]⟩
      rw [dite_eq_right h, dite_eq_right h']
  · intro B
    unfold markVal
    split_ifs with h h2
    · exfalso
      have := h2.2.2.2.1
      rw [InvFun.evalZ, lab.eval_of_subsingleton] at this
      exact absurd this (by positivity)
    · rfl
    · rfl


open Classical in
theorem evalZ_markFun {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ} {w : InvFun O}
    (hw : ∀ n B, w.toFun n B = markVal bar ψ lab i n B) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (β : LinearMap.BilinForm ℤ X) :
    w.evalZ β = if IsMarked bar ψ lab i X β then 1 else 0 := by
  classical
  obtain ⟨n, t, ht⟩ := Module.Finite.exists_fin' O X
  obtain ⟨u, hu⟩ := Module.projective_lifting_property t LinearMap.id ht
  have htu : ∀ a, t (u a) = a := fun a => LinearMap.congr_fun hu a
  rw [InvFun.evalZ, w.eval_eq ht, hw]
  have e := markVal_int (bar := bar) (ψ := ψ) (lab := lab) (i := i) n (pull t β)
  simp only [pull_apply] at e
  rw [e, GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection O bar ψ lab i _ _ t u htu]

theorem exists_markFun_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms H.bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  intro E _ _ _ H q ψ lab i hD hψ htψ htlab hlab
  classical
  obtain ⟨w, hw⟩ := exists_markFun H.bar ψ lab i
  have ev := fun {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (β : LinearMap.BilinForm ℤ X) => evalZ_markFun hw (X := X) β
  have mk : ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
      (β : LinearMap.BilinForm ℤ X), w.evalZ β = 1 → IsMarked H.bar ψ lab i X β := fun β h => by
    rw [ev] at h
    split_ifs at h with h'
    · exact h'
    · norm_num at h
  refine ⟨w, fun σ hσ n B => by rw [hw, hw]; exact GlobalTheory.T.markedFormIndicatorValue_invariant_hostFixingAut E H ψ lab i htψ htlab σ hσ n B, ?_⟩
  intro X _ _ _ _ hX
  refine ⟨fun β _ _ => ?_, fun β _ _ h1 => (mk β h1).2.2.1, fun β _ _ h1 => (mk β h1).2.2.2.1,
    fun m v hv hle β _ _ β' _ _ h1 h1' hc hc' =>
      GlobalTheory.T.polFan_marked_form_unique_in_cell E H q ψ lab i hD hψ hlab X hX m v hv hle β β' (mk β h1) (mk β' h1') hc hc',
    fun m v hv β hβ hp hc hl => ?_⟩
  · rw [ev]
    split_ifs <;> simp
  · obtain ⟨β₀, h0, hc0⟩ := GlobalTheory.T.polFan_exists_marked_form_in_cell E H q ψ lab i hD hψ hlab X hX m v hv β hβ hp hc hl
    exact ⟨β₀, h0.1, h0.2.1, by rw [ev, if_pos h0], hc0⟩

end GlobalTheory.PolFan.Mark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorZeroOneBarycentresPolyFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedFormIndicator_zeroOne_barycentres_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms H.bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  first | exact @GlobalTheory.PolFan.Mark.exists_markFun_props | exact GlobalTheory.PolFan.Mark.exists_markFun_props | (intros; apply GlobalTheory.PolFan.Mark.exists_markFun_props <;> assumption)
end
end
