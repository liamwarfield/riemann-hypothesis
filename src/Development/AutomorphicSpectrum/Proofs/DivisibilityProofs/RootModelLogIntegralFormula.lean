module

public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinear
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormula
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.RootModelPointsIntegral
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.GeoComb

theorem exists_perm_of_map_eq {J : Type} {d : ℕ} (f g : Fin d → J)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : ∃ σ : Equiv.Perm (Fin d), ∀ k, f k = g (σ k) := by
  classical
  have hc : ∀ j, Fintype.card {a // f a = j} = Fintype.card {a // g a = j} := by
    intro j
    have := congrArg (Multiset.count j) h
    simp only [Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert this using 1 <;> simp [Finset.card_def, Finset.filter_val, eq_comm]
  let e : ∀ j, {a // f a = j} ≃ {a // g a = j} := fun j => Fintype.equivOfCardEq (hc j)
  let σ : Equiv.Perm (Fin d) :=
    ((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e)).trans (Equiv.sigmaFiberEquiv g)
  refine ⟨σ, fun a => ?_⟩
  exact ((e (f a) ⟨a, rfl⟩).2).symm

theorem toMultiset_word {J : Type} {d : ℕ} (w : Fin d → J) :
    Finsupp.toMultiset (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ) = Finset.univ.val.map w := by
  rw [Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  rw [← Multiset.sum_map_singleton (Finset.univ.val.map w), Multiset.map_map]
  rfl

theorem degree_word {J : Type} {d : ℕ} (w : Fin d → J) :
    (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ).degree = d := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp

theorem monoLines_word {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (ℓ : J → HermLine ι)
    {d : ℕ} (w : Fin d → J) :
    ∃ σ : Equiv.Perm (Fin d), ∀ k, monoLines ℓ (∑ k, Finsupp.single (w k) 1) d k = ℓ (w (σ k)) := by
  set m : J →₀ ℕ := ∑ k, Finsupp.single (w k) 1 with hm
  set L : List J := (Finsupp.toMultiset m).toList with hL
  have hML : (L : Multiset J) = Finset.univ.val.map w := by
    rw [hL, Multiset.coe_toList, hm, toMultiset_word]
  have hlen : L.length = d := by
    have := congrArg Multiset.card hML
    simpa using this
  let f : Fin d → J := fun k => L.get (Fin.cast hlen.symm k)
  have hf : List.ofFn f = L :=
    List.ext_get (by simp [hlen]) (fun i h1 h2 => by simp [f])
  have hmap : Finset.univ.val.map f = Finset.univ.val.map w := by
    rw [Fin.univ_val_map, hf, hML]
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq f w hmap
  refine ⟨σ, fun k => ?_⟩
  have hk : (k : ℕ) < L.length := by
    rw [hlen]
    exact k.2
  rw [← hσ k]
  simp only [monoLines]
  rw [dite_eq_left hk]
  rfl

theorem map_prod_lin {J : Type} [Fintype J] [DecidableEq J] {d : ℕ} (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ)
    (c : Fin d → J → ℝ) :
    Φ (∏ k, ∑ j, C (c k j) * X j) =
      ∑ w : Fin d → J, (∏ k, c k (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.prod_univ_sum, map_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.C_mul', map_smul, smul_eq_mul,
    MvPolynomial.monomial_sum_one]
  rfl

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def cf (lam : Wt Ψ N) (s : ℝ) : Option (Ψ × Fin N) → ℝ
  | some r => -lam r.1 r.2
  | none => s

theorem linA_eq (lam : Wt Ψ N) (s : ℝ) : linA lam s = ∑ j, C (cf lam s j) * X j := by
  rw [Fintype.sum_option]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linA, toA, linRoot, cf, map_neg, map_sum, map_mul, rename_C, rename_X, neg_mul,
    Finset.sum_neg_distrib]
  ring

theorem coef_mul (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ) (j : Option (Ψ × Fin N)) :
    M.coef lam s j * (M.kA : ℝ) ^ ((Finsupp.single j 1 : Option (Ψ × Fin N) →₀ ℕ) none) = cf lam s j := by
  cases j with
  | none =>
    have hk : (M.kA : ℝ) ≠ 0 := by exact_mod_cast M.kA_pos.ne'
    simp [RootModel.coef, cf]
    field_simp
  | some r =>
    simp [RootModel.coef, cf]

theorem line_smooth (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem line_deg (M : RootModel Ψ N) (t t' : ℝ) (j : Option (Ψ × Fin N)) : (M.line t j).a = (M.line t' j).a := by
  cases j with
  | none => rfl
  | some r => simp [RootModel.line, M.x_deg]

theorem geoFun_monomial (M : RootModel Ψ N) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.geoFun (monomial m 1) = M.geoMono m := by
  have hb : (monomial m 1 : RPA Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ m := by
    simp [MvPolynomial.coe_basisMonomials]
  rw [hb]
  exact Module.Basis.constr_basis _ _ _ _

end RootFieldNumerics.GeoComb

namespace RootFieldNumerics

open GeoComb

theorem root_model_points_integral : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Fin (dimFl Ψ N) → Wt Ψ N) (s : Fin (dimFl Ψ N) → ℝ) (q : ℕ) (n : Fin (dimFl Ψ N) → Option (Ψ × Fin N) → ℤ), (∀ k j, (n k j : ℝ) = q * M.coef (lam k) (s k) j) → ptsIntegral M.P (fun k z => Real.log ((combLine (M.line t) (n k)).h z)) (fun _ => 1) = M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (∏ k, linA (lam k) (s k)) := by
  intro II hII Ψ _ N M t lam s q n hn
  classical
  have hP : IsArithVar M.P (dimFl Ψ N + 1) := M.arith
  have hsm : ∀ j, IsSmoothHerm (M.line t j) := line_smooth M t
  obtain ⟨hexp, hperm⟩ :=
    GlobalTheory.T.log_integral_multilinear II hII M.K M.ι M.P (dimFl Ψ N) (Option (Ψ × Fin N)) (M.line t) n hP hsm
  have hterm : ∀ w : Fin (dimFl Ψ N) → Option (Ψ × Fin N),
      ptsIntegral M.P (fun k z => Real.log ((M.line t (w k)).h z)) (fun _ => 1) =
        M.δ * (M.kA : ℝ) ^ ((∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none) *
          M.geoMono (∑ k, Finsupp.single (w k) 1) := by
    intro w
    obtain ⟨σ, hσ⟩ := monoLines_word (M.line 1) w
    have hmono_sm : ∀ k, IsSmoothHerm (monoLines (M.line 1) (∑ k, Finsupp.single (w k) 1) (dimFl Ψ N) k) := by
      intro k
      rw [hσ k]
      exact line_smooth M 1 _
    rw [hperm (monoLines (M.line 1) (∑ k, Finsupp.single (w k) 1) (dimFl Ψ N)) (fun k => M.line t (w k))
      σ⁻¹ hmono_sm (fun k => hsm _)
      (fun k => by
        rw [hσ, show σ (σ⁻¹ k) = k by simp]
        exact line_deg M t 1 _)]
    have hδ : (M.δ : ℝ) ≠ 0 := by exact_mod_cast M.δ_pos.ne'
    have hk : (M.kA : ℝ) ≠ 0 := by exact_mod_cast M.kA_pos.ne'
    rw [RootModel.geoMono, if_pos (degree_word w)]
    field_simp
  rw [hexp]
  simp_rw [linA_eq]
  rw [map_prod_lin, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [hterm w, geoFun_monomial]
  have hc : (∏ k, (n k (w k) : ℝ)) *
      (M.kA : ℝ) ^ ((∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none) =
        (q : ℝ) ^ dimFl Ψ N * ∏ k, cf (lam k) (s k) (w k) := by
    rw [Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    simp_rw [hn, mul_assoc, coef_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  linear_combination ((M.δ : ℝ) * M.geoMono (∑ k, Finsupp.single (w k) 1)) * hc

end RootFieldNumerics
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormula
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem geoFun_comb_mixed : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Fin (dimFl Ψ N) → Wt Ψ N) (s : Fin (dimFl Ψ N) → ℝ) (q : ℕ) (n : Fin (dimFl Ψ N) → Option (Ψ × Fin N) → ℤ), (∀ k j, (n k j : ℝ) = q * M.coef (lam k) (s k) j) → ptsIntegral M.P (fun k z => Real.log ((combLine (M.line t) (n k)).h z)) (fun _ => 1) = M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (∏ k, linA (lam k) (s k)) := by
  exact RootFieldNumerics.root_model_points_integral

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormulaStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_log_integral_formula : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Fin (dimFl Ψ N) → Wt Ψ N) (s : Fin (dimFl Ψ N) → ℝ) (q : ℕ) (n : Fin (dimFl Ψ N) → Option (Ψ × Fin N) → ℤ), (∀ k j, (n k j : ℝ) = q * M.coef (lam k) (s k) j) → ptsIntegral M.P (fun k z => Real.log ((combLine (M.line t) (n k)).h z)) (fun _ => 1) = M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (∏ k, linA (lam k) (s k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.geoFun_comb_mixed | exact GlobalTheory.CompanionTheory.Ar.Top.geoFun_comb_mixed | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.geoFun_comb_mixed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainUnitLogIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainUnitLogIntegral
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

section Proj

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blockEquiv (k₀ : K) (hk : ∀ a : K, a = k₀) : Unit ≃ K :=
  Equiv.ofBijective (fun _ => k₀) ⟨fun _ _ _ => rfl, fun a => ⟨(), (hk a).symm⟩⟩

def coordEquiv (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    (Σ _ : Unit, Fin (n + 1)) ≃ (Σ k, ι k) :=
  Equiv.ofBijective (fun p => ⟨k₀, σ.symm p.2⟩) (by
    constructor
    · rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
      have h2 : σ.symm a = σ.symm b := by simpa using h
      rw [σ.symm.injective h2]
    · rintro ⟨k, i⟩
      obtain rfl := hk k
      exact ⟨⟨(), σ i⟩, by simp⟩)

variable (ι) in
theorem card_coords (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    Nat.card (Σ k, ι k) = n + 1 := by
  rw [← Nat.card_congr (coordEquiv k₀ hk σ)]
  simp

theorem card_blocks (k₀ : K) (hk : ∀ a : K, a = k₀) : Fintype.card K = 1 :=
  Fintype.card_eq_one_iff.2 ⟨k₀, hk⟩

variable (p : ℕ) [Fact p.Prime]

theorem span_eq_ker : (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)) = RingHom.ker (Bridge.GeoNum.red (ι := ι) p) :=
  (Bridge.GeoNum.ker_red p).symm

theorem isPrime_span : (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)).IsPrime := by
  rw [span_eq_ker]
  exact RingHom.ker_isPrime _

theorem isRelevant_span (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    IsRelevant (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)) := by
  intro k
  obtain rfl := hk k
  refine ⟨σ.symm 0, ?_⟩
  rw [span_eq_ker, RingHom.mem_ker, Bridge.GeoNum.red, map_X]
  exact X_ne_zero _

theorem divSupp_bot (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    divSupp (⊥ : Ideal (MRing ι)) (C (p : ℤ)) = {Ideal.span {C (p : ℤ)}} := by
  have := isPrime_span (ι := ι) p
  ext W
  simp only [divSupp, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, isRelevant_span p k₀ hk σ⟩

theorem ringKrullDim_span (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    ringKrullDim (MRing ι ⧸ (Ideal.span {C (p : ℤ)} : Ideal (MRing ι))) =
      ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  rw [span_eq_ker, ringKrullDim_eq_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective (Bridge.GeoNum.red_surjective p)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ENat.card_eq_coe_natCard, card_coords ι k₀ hk σ, card_blocks k₀ hk]
  simp

theorem intNum_bot (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) (a : K → ℤ) (ha : a k₀ = 1) :
    NumbersDVR.intNum (ZMod p) (⊥ : Ideal (NumbersDVR.MRing ι (ZMod p))) (fun _ : Fin n => a) = 1 := by
  have h := FieldNumbers.Relabel.intNum_map_rename (F := ZMod p) (blockEquiv k₀ hk)
    (coordEquiv k₀ hk σ) (fun _ => rfl)
    (⊥ : Ideal (NumbersDVR.MRing (FieldNumbers.ProjIdx n) (ZMod p))) (fun _ : Fin n => a)
  rw [Ideal.map_bot] at h
  rw [h]
  have hb : (fun _ : Fin n => a ∘ blockEquiv k₀ hk) = fun _ : Fin n => (1 : Unit → ℤ) := by
    funext _ u
    exact ha
  rw [hb]
  exact FieldNumbers.intNum_projectiveSpace (ZMod p) n

theorem geoNum_span (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) (a : K → ℤ) (ha : a k₀ = 1) :
    geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)) (fun _ : Fin n => a) = 1 := by
  have hV : IsMultiProjPrime (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)) :=
    ⟨isPrime_span p, ⟨{C (p : ℤ)}, fun f hf => ⟨0, by
      rw [Set.mem_singleton_iff.mp hf]
      exact Inter.Conservation.isMultiHomog_C _⟩, rfl⟩, isRelevant_span p k₀ hk σ⟩
  rw [← Bridge.intNum_map_eq_geoNum p n _ hV (Ideal.mem_span_singleton_self _) (ringKrullDim_span p k₀ hk σ)]
  have hb : (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)).map
      (MvPolynomial.map (Int.castRingHom (ZMod p))) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (span_eq_ker p).le
  rw [hb]
  exact intNum_bot p k₀ hk σ a ha

omit p in
theorem arithVar_bot (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    IsArithVar (⊥ : Ideal (MRing ι)) (n + 1) := by
  refine ⟨⟨k₀⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun k => ?_⟩, ?_, ?_⟩
  · obtain rfl := hk k
    refine ⟨σ.symm 0, ?_⟩
    rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
      ENat.card_eq_coe_natCard, card_coords ι k₀ hk σ, card_blocks k₀ hk]
    push_cast
    exact add_comm _ _


omit p in
theorem ptsIntegral_bot (II : IntersectionSystem) (hII : IsIntersectionSystem II) (k₀ : K) (hk : ∀ a : K, a = k₀)
    {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) (L : HermLine ι) (hL : IsSmoothHerm L) (ha : L.a k₀ = 1) :
    ptsIntegral (⊥ : Ideal (MRing ι)) (pot fun _ : Fin n => L) (fun _ => 1) = 1 := by
  have hP := arithVar_bot k₀ hk σ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := (Inter.Conservation.proof : ConservationStatement) K ι (II K ι) (hII _ _) ⊥ n
    (fun _ => L) 2 hP (fun _ => hL) Nat.prime_two
  have hW : (Ideal.span {C ((2 : ℕ) : ℤ)} : Ideal (MRing ι)) ∈ divSupp (⊥ : Ideal (MRing ι)) (C ((2 : ℕ) : ℤ)) := by
    rw [divSupp_bot 2 k₀ hk σ]
    rfl
  have := isPrime_span (ι := ι) 2
  have hv : vertR (⊥ : Ideal (MRing ι)) (fun _ : Fin n => L) (C ((2 : ℕ) : ℤ)) = Real.log ((2 : ℕ) : ℝ) := by
    have hg : geoNum n (Ideal.span {C ((2 : ℕ) : ℤ)} : Ideal (MRing ι)) (fun j => ((fun _ : Fin n => L) j).a) = 1 :=
      geoNum_span 2 k₀ hk σ L.a ha
    unfold vertR
    rw [divSupp_bot 2 k₀ hk σ, finsum_mem_singleton, if_neg (Inter.Conservation.not_horizontal Nat.prime_two hW),
      Inter.Conservation.charOf_eq Nat.prime_two hW, bot_sup_eq, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self, hg]
    simp
  rw [h1, hv] at h2
  have hlog : Real.log ((2 : ℕ) : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h3 : Real.log ((2 : ℕ) : ℝ) * 1 =
      Real.log ((2 : ℕ) : ℝ) * ptsIntegral (⊥ : Ideal (MRing ι)) (pot fun _ : Fin n => L) (fun _ => 1) := by
    rw [mul_one]
    exact h2
  exact (mul_left_cancel₀ hlog h3).symm

end Proj

section First

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type} [Fintype K] [DecidableEq K]

theorem pPart_eq_bot (τ : Ψ) (h : 0 < N - 1) (k₀ : K) (hk : ∀ a : K, a = k₀) :
    PPart (fun _ : K => ((τ, ⟨0, h⟩) : FlBlock Ψ N)) = ⊥ := by
  set j : K → FlBlock Ψ N := fun _ => (τ, ⟨0, h⟩) with hj
  have hN : 0 < N := by omega
  let emb : (Σ k, PIdx j k) → Ψ × Fin N × Fin N := fun p => (τ, ⟨0, hN⟩, p.2.1 ⟨0, Nat.succ_pos _⟩)
  have hemb : Function.Injective emb := by
    rintro ⟨a, A⟩ ⟨b, B⟩ hab
    obtain rfl : a = b := (hk a).trans (hk b).symm
    have h3 : A.1 ⟨0, Nat.succ_pos _⟩ = B.1 ⟨0, Nat.succ_pos _⟩ := (Prod.ext_iff.1 (Prod.ext_iff.1 hab).2).2
    have hAB : A = B := by
      refine Subtype.ext (funext fun x => ?_)
      have hx : x = ⟨0, Nat.succ_pos _⟩ := Fin.ext (by have := x.2; simp [j] at this ⊢)
      rw [hx]
      exact h3
    rw [hAB]
  have hy : ∀ p, yPart j p = algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) (X (emb p)) := by
    intro p
    unfold yPart yFl
    congr 1
    change Matrix.det (n := Fin 1) _ = _
    rw [Matrix.det_fin_one]
    rfl
  have hval : ∀ x : MRing (PIdx j), aeval (yPart j) x = algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N)
      (rename emb (map (Int.castRingHom ℚ) x)) := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f p hf => simp only [map_mul, hf, aeval_X, map_X, rename_X, hy]
  have hcomp : ∀ x : MRing (PIdx j), aeval (fun _ : K => (1 : ΩFl Ψ N)) (mConeMap (yPart j) x) = aeval (yPart j) x := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f p hf => simp only [map_mul, hf]; simp [mConeMap]
  unfold PPart mCoordIdeal
  rw [← RingHom.injective_iff_ker_eq_bot]
  intro x y hxy
  have h1 := congrArg (aeval (fun _ : K => (1 : ΩFl Ψ N))) hxy
  rw [hcomp, hcomp, hval, hval] at h1
  have h2 := IsFractionRing.injective (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) h1
  exact map_injective _ (RingHom.injective_int _) (rename_injective _ hemb h2)

def incrOne (N : ℕ) : PlueckerData.Incr 1 N ≃ Fin N where
  toFun A := A.1 0
  invFun i := ⟨fun _ => i, Subsingleton.strictMono _⟩
  left_inv A := Subtype.ext (funext fun x => by rw [Subsingleton.elim x 0])
  right_inv _ := rfl

end First

theorem ptsIntegral_first : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K]
    (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ k₀ : K, (∀ a : K, a = k₀) →
    ∀ j : K → FlBlock Ψ N, IsChain j →
      ptsIntegral (PPart j) (pot fun _ : Fin (N - 1) => unitLine j k₀) (fun _ => 1) = 1 := by
  intro Ψ _ _ N K _ _ II hII k₀ hk j hj
  obtain ⟨τ, h, rfl⟩ : ∃ (τ : Ψ) (h : 0 < N - 1), j = fun _ => ((τ, ⟨0, h⟩) : FlBlock Ψ N) := by
    have h : 0 < N - 1 := Nat.lt_of_le_of_lt (Nat.zero_le _) (j k₀).2.2
    refine ⟨(j k₀).1, h, ?_⟩
    obtain ⟨k, hk'⟩ := hj.down k₀ ((j k₀).1, ⟨0, h⟩) rfl (Nat.zero_le _)
    funext a
    rw [hk k] at hk'
    rw [hk a]
    exact hk'
  have hN : N - 1 + 1 = N := by omega
  rw [pPart_eq_bot τ h k₀ hk]
  refine ptsIntegral_bot II hII.1 k₀ hk (n := N - 1)
    ((incrOne N).trans (finCongr hN.symm)) _ (FlagHeightMultilinear.isSmoothHerm_fsHerm _) ?_
  simp [unitLine, fsHerm]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainUnitLogIntegralStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_chain_unit_log_integral : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K] (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ k₀ : K, (∀ a : K, a = k₀) → ∀ j : K → FlBlock Ψ N, IsChain j → ptsIntegral (PPart j) (pot fun _ : Fin (N - 1) => unitLine j k₀) (fun _ => 1) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first <;> assumption)
end
end
