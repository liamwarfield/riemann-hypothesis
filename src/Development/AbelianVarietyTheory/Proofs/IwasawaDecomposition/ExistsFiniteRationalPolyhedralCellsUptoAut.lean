module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedPsdRationalRadicalConeSubsetIntCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedPsdRationalRadicalConeSubsetIntCone
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem psdCone_subset_psdCone_int (O : Type) [CommRing O] [Module.Finite ℤ O] [Module.Free ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] : psdCone (bar := bar) (X := X) ⊆ psdCone (bar := (id : ℤ → ℤ)) (X := X) := by
  rintro B ⟨X₁, _, _, hP, r, B₁, hr, h1, h2, h3⟩
  haveI : Module.Projective ℤ X₁ := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 hP
    exact Module.Projective.of_split (s.restrictScalars ℤ) ((Finsupp.linearCombination O id).restrictScalars ℤ)
      (by ext x; exact congrArg (· x) hs)
  refine ⟨X₁, inferInstance, inferInstance, inferInstance, r.toAddMonoidHom.toIntLinearMap, B₁, hr,
    ⟨h1.1, fun a y z => ?_⟩, h2, h3⟩
  show B₁ (a • y) z = B₁ y (a • z)
  rw [map_zsmul, map_zsmul, LinearMap.smul_apply]

end GlobalTheory.PolFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedPsdRationalRadicalConeSubsetIntConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] [Module.Free ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X], psdCone (bar := bar) (X := X) ⊆ psdCone (bar := (id : ℤ → ℤ)) (X := X) := by
  first | exact @GlobalTheory.PolFan.psdCone_subset_psdCone_int | exact GlobalTheory.PolFan.psdCone_subset_psdCone_int | (intros; apply GlobalTheory.PolFan.psdCone_subset_psdCone_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrictlyConcavePolFanConeRealForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrictlyConcavePolFanConeRealForms
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

theorem strictWith_real : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N m : ℕ)
    (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → IsCone (id : ℤ → ℤ) φ u →
    StrictWith (id : ℤ → ℤ) φ N (linW w) u → (∀ B ∈ rcone u, (N : ℝ) * evalR φ B = evalW w B) ∧
      ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), (N : ℝ) * evalR φ B ≤ evalW w B ∧ ((N : ℝ) * evalR φ B = evalW w B → B ∈ rcone u) := by
  intro X _ _ φ N m u w hF hu hS
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨?_, ?_⟩
  · rintro B ⟨t, ht, rfl⟩
    rw [(linearOn_iff φ u).1 hu.linear t ht, evalW_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i]; ring
  · intro B hB
    obtain ⟨m', γ, c, hγ, hc, rfl⟩ := hF.cover B hB
    have hle : ∀ i, (N : ℝ) * φ.evalZ (γ i) ≤ linW w (γ i) := fun i => h2 _ (hγ.mem i) (hγ.nonneg i)
    rw [(linearOn_iff φ γ).1 hγ.linear c hc, evalW_sum, Finset.mul_sum]
    have hterm : ∀ i, (N : ℝ) * (c i * φ.evalZ (γ i)) ≤ c i * linW w (γ i) := fun i => by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hle i) (hc i)
    refine ⟨Finset.sum_le_sum fun i _ => hterm i, fun he => ?_⟩
    have heq : ∀ i, (N : ℝ) * (c i * φ.evalZ (γ i)) = c i * linW w (γ i) :=
      fun i => (Finset.sum_eq_sum_iff_of_le fun i _ => hterm i).1 he i (Finset.mem_univ i)
    have hd : ∀ i, ∃ d : Fin m → ℝ, (∀ j, 0 ≤ d j) ∧ c i • toReal (γ i) = ∑ j, d j • toReal (u j) := by
      intro i
      rcases (hc i).eq_or_lt with h0 | h0
      · exact ⟨0, fun _ => le_rfl, by simp [← h0]⟩
      · have hi : (N : ℝ) * φ.evalZ (γ i) = linW w (γ i) := by
          have := heq i
          rw [mul_left_comm] at this
          exact mul_left_cancel₀ h0.ne' this
        obtain ⟨k, e, hk, hke⟩ := h3 _ (hγ.mem i) (hγ.nonneg i) hi
        refine ⟨fun j => c i * e j / k, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
        have := LinearMap.congr_fun₂ hke a b
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul, smul_eq_mul] at this
        have hk' : (k : ℝ) ≠ 0 := by positivity
        have this' : (k : ℝ) * (γ i a b : ℝ) = ∑ j, (e j : ℝ) * (u j a b : ℝ) := by exact_mod_cast this
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul]
        calc c i * (γ i a b : ℝ) = c i / k * (k * γ i a b) := by field_simp
          _ = ∑ j, c i * e j / k * u j a b := by
            rw [this', Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    choose d hd0 hd1 using hd
    refine ⟨fun j => ∑ i, d i j, fun j => Finset.sum_nonneg fun i _ => hd0 i j, ?_⟩
    simp only [hd1, Finset.sum_smul]
    exact Finset.sum_comm

end GlobalTheory.PolCell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrictlyConcavePolFanConeRealFormsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictlyConcave_polFan_cone_real_forms : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → IsCone (id : ℤ → ℤ) φ u → StrictWith (id : ℤ → ℤ) φ N (linW w) u → (∀ B ∈ rcone u, (N : ℝ) * evalR φ B = evalW w B) ∧ ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), (N : ℝ) * evalR φ B ≤ evalW w B ∧ ((N : ℝ) * evalR φ B = evalW w B → B ∈ rcone u) := by
  first | exact @GlobalTheory.PolCell.strictWith_real | exact GlobalTheory.PolCell.strictWith_real | (intros; apply GlobalTheory.PolCell.strictWith_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellOfContactSetIntInequalities
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellOfContactSetIntInequalities
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

section Contact

variable {X : Type} [AddCommGroup X] {m : ℕ}

theorem sum_smul_toReal_apply' (t : Fin m → ℝ) (u : Fin m → LinearMap.BilinForm ℤ X) (y z : X) :
    (∑ i, t i • toReal (u i)) y z = ∑ i, t i * (u i y z : ℝ) := by
  simp [LinearMap.sum_apply]

theorem toReal_sum_nsmul (n : Fin m → ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) :
    toReal (∑ i, n i • u i) = ∑ i, (n i : ℝ) • toReal (u i) := by
  ext y z
  rw [sum_smul_toReal_apply']
  simp [LinearMap.sum_apply]

theorem sum_smul_toReal_comb {r : ℕ} (v : Fin r → Fin m → ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (c : Fin r → ℝ) :
    ∑ k, c k • toReal (∑ i, v k i • u i) = ∑ i, (∑ k, c k • fun i => (v k i : ℝ)) i • toReal (u i) := by
  ext y z
  rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    toReal_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

variable {O : Type} [CommRing O] [Module O X]

theorem sum_mem_realForms_iff (bar : O → O) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i y z, u i y z = u i z y)
    (t : Fin m → ℝ) : ∑ i, t i • toReal (u i) ∈ realForms bar X ↔
      ∀ b ∈ {b : Fin m → ℤ | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)},
        ∑ i, (b i : ℝ) * t i = 0 := by
  rw [mem_realForms]
  constructor
  · rintro ⟨-, h⟩ b ⟨a, y, z, rfl⟩
    have := h a y z
    rw [sum_smul_toReal_apply', sum_smul_toReal_apply'] at this
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    simpa only [mul_comm] using this
  · intro h
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
      exact Finset.sum_congr rfl fun i _ => by rw [hu i y z]
    · have := h _ ⟨a, y, z, rfl⟩
      rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
      simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at this
      simpa only [mul_comm] using this

end Contact

theorem exists_isCell_of_contact (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ψ : InvFun O) (K : ℕ) (Λ : (X × X) →₀ ℤ) (m : ℕ)
    (u : Fin m → LinearMap.BilinForm ℤ X) (A : Set (Fin m → ℤ)) (hA : A.Finite) (hK : 0 < K)
    (hsym : ∀ i y z, u i y z = u i z y) (hnn : ∀ i y, 0 ≤ u i y y)
    (hint : ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z)
    (hle : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (K : ℝ) * ψ.evalZ β ≤ evalW Λ (toReal β))
    (hcon : ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧
      (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i))
    (hlin : ∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) →
      ∑ i, t i • toReal (u i) ∈ realForms bar X →
      (K : ℝ) * evalR ψ (∑ i, t i • toReal (u i)) = evalW Λ (∑ i, t i • toReal (u i))) :
    ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → B ∈ rcone γ := by
  obtain ⟨r, v, hiff, hZ⟩ := GlobalTheory.T.minkowskiWeyl_orthant_cone_integral_constraints m A
    {b | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)} hA
  have hbal := sum_mem_realForms_iff bar u hsym
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hvk : ∀ k, (∀ i, (0 : ℝ) ≤ (v k i : ℝ)) ∧ (∀ a ∈ A, ∑ i, (a i : ℝ) * (v k i : ℝ) ≤ 0) ∧
      (∀ b ∈ {b : Fin m → ℤ | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)},
        ∑ i, (b i : ℝ) * (v k i : ℝ) = 0) := by
    intro k
    refine (hiff _).2 ⟨Pi.single k 1, fun j => ?_, ?_⟩
    · by_cases h : j = k
      · subst h; simp
      · simp [h]
    · funext i
      rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp
  have hγR : ∀ k, toReal (∑ i, v k i • u i) = ∑ i, (v k i : ℝ) • toReal (u i) := fun k => toReal_sum_nsmul _ _
  have hγbal : ∀ k, (∑ i, v k i • u i) ∈ balForms bar X := by
    intro k
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hsym i y z]
    · have h := ((hbal _).2 (hvk k).2.2).2 a y z
      rw [← hγR] at h
      simp only [toReal_apply] at h
      exact_mod_cast h
  have hγval : ∀ k, ((linW Λ (∑ i, v k i • u i) : ℤ) : ℝ) = K * ψ.evalZ (∑ i, v k i • u i) := by
    intro k
    have h := hlin _ (hvk k).1 (hvk k).2.1 ((hbal _).2 (hvk k).2.2)
    rw [← hγR, evalR_toReal, evalW_toReal] at h
    exact h.symm
  have hcomb := sum_smul_toReal_comb v u
  refine ⟨r, fun k => ∑ i, v k i • u i, ⟨hγbal, fun k y => ?_, ?_, ?_⟩, ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_nonneg fun i _ => nsmul_nonneg (hnn i y) _
  · rw [linearOn_iff]
    intro c hc
    obtain ⟨hnt, hAt, hVt⟩ := (hiff _).2 ⟨c, hc, rfl⟩
    have h := hlin _ hnt hAt ((hbal _).2 hVt)
    rw [← hcomb, evalW_sum] at h
    have : (K : ℝ) * evalR ψ (∑ k, c k • toReal (∑ i, v k i • u i)) = K * ∑ k, c k * ψ.evalZ (∑ i, v k i • u i) := by
      rw [h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hγval]; ring
    exact mul_left_cancel₀ hKr.ne' this
  · refine ⟨K, linW Λ, hK, hγval, fun β hβ hp => ?_, fun β hβ hp heq => ?_⟩
    · rw [← evalW_toReal]; exact hle β hβ hp
    · have hpsd : toReal β ∈ psdCone (bar := bar) (X := X) := by
        have := GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
          (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
        simpa using this
      obtain ⟨t, ht0, htA, htB⟩ := hcon _ hpsd (by rw [evalR_toReal, evalW_toReal]; exact heq)
      have hVt := (hbal t).1 (htB ▸ toReal_mem hβ)
      choose z hz using hint β t htB
      have hz0 : ∀ i, 0 ≤ z i := fun i => by
        have := ht0 i; rw [hz i] at this; exact_mod_cast this
      have htn : ∀ i, (((z i).toNat : ℤ) : ℝ) = t i := fun i => by
        rw [Int.toNat_of_nonneg (hz0 i), hz i]
      obtain ⟨k, c, hk, hkc⟩ := hZ (fun i => (z i).toNat)
        (fun a ha => by
          have := htA a ha
          simp only [← htn] at this
          exact_mod_cast this)
        (fun b hb => by
          have := hVt b hb
          simp only [← htn] at this
          exact_mod_cast this)
      refine ⟨k, c, hk, LinearMap.ext₂ fun y w => ?_⟩
      have hβz : β y w = ∑ i, ((z i).toNat : ℤ) * u i y w := by
        have h1 : (β y w : ℝ) = ∑ i, t i * (u i y w : ℝ) := by
          rw [← toReal_apply, htB, sum_smul_toReal_apply']
        have h2 : (β y w : ℝ) = ((∑ i, ((z i).toNat : ℤ) * u i y w : ℤ) : ℝ) := by
          rw [h1]; push_cast
          exact Finset.sum_congr rfl fun i _ => by rw [← htn i]; push_cast; ring
        exact_mod_cast h2
      have hcoord : ∀ i, (k : ℤ) * ((z i).toNat : ℤ) = ∑ j, (c j : ℤ) * (v j i : ℤ) := fun i => by
        have := congrFun hkc i
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
        exact_mod_cast this
      calc (k • β) y w = (k : ℤ) * β y w := by simp
        _ = ∑ i, ((k : ℤ) * ((z i).toNat : ℤ)) * u i y w := by
          rw [hβz, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i, ∑ j, (c j : ℤ) * ((v j i : ℤ) * u i y w) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoord, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, (c j : ℤ) * ∑ i, (v j i : ℤ) * u i y w := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
        _ = (∑ j, c j • ∑ i, v j i • u i) y w := by
          simp [LinearMap.sum_apply, nsmul_eq_mul]
  · intro B hB hBe
    obtain ⟨t, ht0, htA, rfl⟩ := hcon B hB hBe
    obtain ⟨c, hc, rfl⟩ := (hiff _).1 ⟨ht0, htA, (hbal _).1 (mem_realForms_of_mem_psdCone hB)⟩
    exact ⟨c, hc, (hcomb c).symm⟩

end GlobalTheory.PolCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellOfContactSetIntInequalitiesStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cell_of_contactSet_intInequalities : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ψ : InvFun O) (K : ℕ) (Λ : (X × X) →₀ ℤ) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (A : Set (Fin m → ℤ)), A.Finite → 0 < K → (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) → (∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (K : ℝ) * ψ.evalZ β ≤ evalW Λ (toReal β)) → (∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) → (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → ∑ i, t i • toReal (u i) ∈ realForms bar X → (K : ℝ) * evalR ψ (∑ i, t i • toReal (u i)) = evalW Λ (∑ i, t i • toReal (u i))) → ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → B ∈ rcone γ := by
  first | exact @GlobalTheory.PolCell.exists_isCell_of_contact | exact GlobalTheory.PolCell.exists_isCell_of_contact | (intros; apply GlobalTheory.PolCell.exists_isCell_of_contact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinitePolFanConesCoverRealCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinitePolFanConesCoverRealCone
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

open GlobalTheory.PolFan

theorem exists_finite_cover_rcone : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N p : ℕ) (P : Fin p → LinearMap.BilinForm ℤ X), IsPolFanOn (id : ℤ → ℤ) φ X → (∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u) → (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) → ∃ (s : ℕ) (m : Fin s → ℕ) (u : ∀ k, Fin (m k) → LinearMap.BilinForm ℤ X) (w : Fin s → (X × X) →₀ ℤ), (∀ k, IsCone (id : ℤ → ℤ) φ (u k) ∧ StrictWith (id : ℤ → ℤ) φ N (linW (w k)) (u k)) ∧ ∀ B ∈ rcone P, B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) → ∃ k, B ∈ rcone (u k) := by
  intro X _ _ φ N p P hφ hcov hsym hpos
  let ι : Type := {x : Σ m : ℕ, (Fin m → LinearMap.BilinForm ℤ X) × ((X × X) →₀ ℤ) //
    IsCone (id : ℤ → ℤ) φ x.2.1 ∧ StrictWith (id : ℤ → ℤ) φ N (linW x.2.2) x.2.1}
  have hnn : ∀ (x : ι) i, 0 ≤ linW x.1.2.2 (P i) := by
    intro x i
    have h1 := x.2.2.2.1 (P i) (mem_balForms_int.2 (hsym i)) (hpos i)
    have h2 := hφ.evalZ_nonneg (mem_balForms_int.2 (hsym i)) (hpos i)
    have : (0 : ℝ) ≤ (linW x.1.2.2 (P i) : ℝ) := le_trans (mul_nonneg (Nat.cast_nonneg _) h2) h1
    exact_mod_cast this
  let f : ι → Fin p → ℕ := fun x i => (linW x.1.2.2 (P i)).toNat
  obtain ⟨F, hF⟩ := GlobalTheory.T.dickson_exists_finite_subfamily_below p f
  let e := F.equivFin
  let g : Fin F.card → ι := fun k => (e.symm k : ι)
  refine ⟨F.card, fun k => (g k).1.1, fun k => (g k).1.2.1, fun k => (g k).1.2.2, fun k => (g k).2, ?_⟩
  intro B hB hBp
  obtain ⟨m, u, w, hc, hs, hBu⟩ := hcov B hBp
  let i₀ : ι := ⟨⟨m, u, w⟩, hc, hs⟩
  obtain ⟨j, hjF, hj⟩ := hF i₀
  refine ⟨e ⟨j, hjF⟩, ?_⟩
  have hg : g (e ⟨j, hjF⟩) = j := by simp [g]
  show B ∈ rcone (g (e ⟨j, hjF⟩)).1.2.1
  rw [hg]
  obtain ⟨t, ht, rfl⟩ := hB
  have A := (GlobalTheory.T.strictlyConcave_polFan_cone_real_forms X φ N m u w hφ hc hs).1 _ hBu
  have C := (GlobalTheory.T.strictlyConcave_polFan_cone_real_forms X φ N j.1.1 j.1.2.1 j.1.2.2 hφ j.2.1 j.2.2).2 _ hBp
  apply C.2
  have hle : evalW j.1.2.2 (∑ i, t i • toReal (P i)) ≤ evalW w (∑ i, t i • toReal (P i)) := by
    rw [evalW_sum, evalW_sum]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
    have h1 := hj i
    have h2 := hnn j i
    have h3 := hnn i₀ i
    simp only [f] at h1
    have : linW j.1.2.2 (P i) ≤ linW w (P i) := by
      have h3' : 0 ≤ linW w (P i) := h3
      have h1' : (linW j.1.2.2 (P i)).toNat ≤ (linW w (P i)).toNat := h1
      omega
    exact_mod_cast this
  linarith [C.1]

end GlobalTheory.PolCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinitePolFanConesCoverRealConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_polFanCones_cover_realCone : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N p : ℕ) (P : Fin p → LinearMap.BilinForm ℤ X), IsPolFanOn (id : ℤ → ℤ) φ X → (∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u) → (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) → ∃ (s : ℕ) (m : Fin s → ℕ) (u : ∀ k, Fin (m k) → LinearMap.BilinForm ℤ X) (w : Fin s → (X × X) →₀ ℤ), (∀ k, IsCone (id : ℤ → ℤ) φ (u k) ∧ StrictWith (id : ℤ → ℤ) φ N (linW (w k)) (u k)) ∧ ∀ B ∈ rcone P, B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) → ∃ k, B ∈ rcone (u k) := by
  first | exact @GlobalTheory.PolCell.exists_finite_cover_rcone | exact GlobalTheory.PolCell.exists_finite_cover_rcone | (intros; apply GlobalTheory.PolCell.exists_finite_cover_rcone <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntFormDominatingPolFanBaseClassMinMeans
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntFormDominatingPolFanBaseClassMinMeans
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

section Formulas

variable {X : Type} [AddCommGroup X]

theorem evalW_add_left (w w' : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (w + w') B = evalW w B + evalW w' B := by
  unfold evalW
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

theorem evalW_zero_left (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW (0 : (X × X) →₀ ℤ) B = 0 := by
  simp [evalW]

theorem evalW_zsmul_left (k : ℤ) (w : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (k • w) B = k * evalW w B := by
  unfold evalW
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun p _ => ?_
  simp only [smul_eq_mul, Int.cast_mul]
  ring

theorem evalW_single_left (p : X × X) (k : ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (Finsupp.single p k) B = k * B p.1 p.2 := by
  unfold evalW
  exact Finsupp.sum_single_index (by simp)

theorem evalW_finset_sum_left {ι : Type} (s : Finset ι) (f : ι → (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (∑ i ∈ s, f i) B = ∑ i ∈ s, evalW (f i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalW_zero_left]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evalW_add_left, ih]

theorem evalW_lamW (D N n : ℕ) (𝓜 : Finset ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (w : (X × X) →₀ ℤ)
    (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (lamW D N n 𝓜 r w a) B = D * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * evalW w B +
      ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, B (r (a M y)) (r (a M y))) := by
  simp only [lamW, evalW_zsmul_left, evalW_add_left, evalW_finset_sum_left, evalW_single_left]
  push_cast
  simp

theorem kDen_mul_evalR_baseFun {O : Type} [CommRing O] [Module.Finite ℤ O] [Module O X] [Module.Finite O X]
    [Module.Finite ℤ X] (D : ℕ) (φ : InvFun ℤ) (N n : ℕ) (𝓜 : Finset ℕ) {r : (Fin n → ℤ) →ₗ[ℤ] X}
    (hr : Function.Surjective r) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    (kDen N n 𝓜 : ℝ) * evalR (baseFun O D φ 𝓜) B = D * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φ B) +
      ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, classMin M (fun x z => B (r x) (r z)) y) := by
  have hE : ∀ M, (fineMean M).eval X (fun x z => B x z) =
      (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
    intro M
    rw [(fineMean M).eval_eq hr]
    simp [fineMean]
  have key : ∀ M ∈ 𝓜, (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (((M : ℝ) + 1) ^ n)⁻¹ =
      ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n := by
    intro M hM
    rw [← Finset.mul_prod_erase 𝓜 (fun M : ℕ => ((M : ℝ) + 1) ^ n) hM]
    have : ((M : ℝ) + 1) ^ n ≠ 0 := by positivity
    field_simp
  have hs : (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) *
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y =
      ∑ M ∈ 𝓜, (∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun M hM => by rw [← mul_assoc, key M hM]
  have h1 : evalR (baseFun O D φ 𝓜) B = D * (evalR φ B + ∑ M ∈ 𝓜, (fineMean M).eval X (fun x z => B x z)) :=
    eval_baseFun D φ 𝓜 _
  rw [h1]
  simp only [hE, kDen]
  push_cast
  calc _ = (D : ℝ) * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φ B) + N * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) *
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y)) := by ring
    _ = _ := by
      rw [hs, Finset.mul_sum]
      simp only [mul_assoc]

theorem classMin_le_of_nonneg (M : ℕ) {n : ℕ} {B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ} (hB : ∀ x, 0 ≤ B x x)
    {y : Fin n → ZMod (M + 1)} {x : Fin n → ℤ} (hx : redV M x = y) : classMin M B y ≤ B x x :=
  csInf_le ⟨0, by rintro _ ⟨b, -, rfl⟩; exact hB b⟩ ⟨x, hx, rfl⟩

end Formulas

theorem exists_contact_baseFun_lamW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Finite ℤ X] (N m n : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), 0 < D → IsPolFanOn (id : ℤ → ℤ) φs X → 0 < N → IsCone (id : ℤ → ℤ) φs u → StrictWith (id : ℤ → ℤ) φs N (linW w) u → Function.Surjective r → (∀ M y, redV M (a M y) = y) → ∃ A : Set (Fin m → ℤ), A.Finite ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (kDen N n 𝓜 : ℝ) * (baseFun (𝓞 E) D φs 𝓜).evalZ β ≤ evalW (lamW D N n 𝓜 r w a) (toReal β)) ∧ (∀ B ∈ psdCone (bar := H.bar) (X := X), (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) ∧ (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) (∑ i, t i • toReal (u i)) = evalW (lamW D N n 𝓜 r w a) (∑ i, t i • toReal (u i))) ∧ ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
  intro E _ _ _ H D φs 𝓜 X _ _ _ _ N m n u w r a hD hφ hN hu hS hr ha
  classical
  choose F hF using fun (M : ℕ) (y : Fin n → ZMod (M + 1)) =>
    GlobalTheory.T.dickson_exists_finite_subfamily_below m (fun a' : {a' : Fin n → ℤ // redV M a' = y} => fun j => (u j (r a'.1) (r a'.1)).toNat)
  let vec : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → (Fin n → ℤ) → Fin m → ℤ :=
    fun M y a' i => u i (r (a M y)) (r (a M y)) - u i (r a') (r a')
  have hI := GlobalTheory.T.strictlyConcave_polFan_cone_real_forms X φs N m u w hφ hu hS
  have hsum : ∀ (t : Fin m → ℝ) (x z : X), (∑ i, t i • toReal (u i)) x z = ∑ i, t i * (u i x z : ℝ) := by
    intro t x z
    simp [LinearMap.sum_apply]
  have hP : 0 < ∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n := Finset.prod_pos fun _ _ => by positivity
  have hc : ∀ M ∈ 𝓜, 0 < (N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n := fun M _ =>
    mul_pos (by exact_mod_cast hN) (Finset.prod_pos fun _ _ => by positivity)
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD

  have hle_gen : ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X),
      (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B ≤ evalW (lamW D N n 𝓜 r w a) B := by
    intro B hB
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW]
    have h1 := ((hI.2 B hB).1)
    have h2 : ∀ M ∈ 𝓜, ∑ y, classMin M (fun x z => B (r x) (r z)) y ≤ ∑ y, B (r (a M y)) (r (a M y)) :=
      fun M _ => Finset.sum_le_sum fun y _ =>
        classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB (r x)) (ha M y)
    have h3 := Finset.sum_le_sum fun M hM => mul_le_mul_of_nonneg_left (h2 M hM) (hc M hM).le
    have h4 := mul_le_mul_of_nonneg_left h1 hP.le
    exact mul_le_mul_of_nonneg_left (add_le_add h4 h3) hD'.le

  have hback : ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) →
      (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
    intro B hB hcl
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW, hI.1 B hB]
    congr 2
    exact Finset.sum_congr rfl fun M hM => by rw [Finset.sum_congr rfl fun y _ => hcl M hM y]
  refine ⟨⋃ M ∈ (𝓜 : Set ℕ), ⋃ y : Fin n → ZMod (M + 1),
      (fun a' : {a' : Fin n → ℤ // redV M a' = y} => vec M y a'.1) '' (F M y : Set _), ?_, ?_, ?_, ?_, hback⟩
  · exact Set.Finite.biUnion (Finset.finite_toSet 𝓜) fun M _ =>
      Set.finite_iUnion fun y => (Finset.finite_toSet _).image _
  · intro β hβ hβ0
    have hB : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
      have := GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; simpa using hβ)
        (fun i y => by fin_cases i; simpa using hβ0 y) (fun i => by fin_cases i; simp)
      simpa using this
    rw [← evalR_toReal]
    exact hle_gen _ (GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone (𝓞 E) H.bar X hB)
  · intro B hB heq
    have hB' := GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone (𝓞 E) H.bar X hB
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW] at heq
    have heq' := mul_left_cancel₀ hD'.ne' heq
    have h1 := (hI.2 B hB').1
    have hy : ∀ M, ∀ y, 0 ≤ B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y := fun M y =>
      sub_nonneg.2 (classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB' (r x)) (ha M y))
    have hT : 0 ≤ ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) :=
      Finset.sum_nonneg fun M hM => mul_nonneg (hc M hM).le (Finset.sum_nonneg fun y _ => hy M y)
    have hT' : ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) =
        ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, B (r (a M y)) (r (a M y)) -
        ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
          ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun M _ => by rw [Finset.sum_sub_distrib, mul_sub]
    have h4 := mul_le_mul_of_nonneg_left h1 hP.le
    have hT0 : ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) = 0 := by
      linarith
    have hW : (N : ℝ) * evalR φs B = evalW w B := by
      have : (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φs B) = (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * evalW w B := by
        linarith
      exact mul_left_cancel₀ hP.ne' this
    have hcl : ∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y)) := by
      intro M hM y
      have e1 := (Finset.sum_eq_zero_iff_of_nonneg fun M hM =>
        mul_nonneg (hc M hM).le (Finset.sum_nonneg fun y _ => hy M y)).1 hT0 M hM
      have e2 := (mul_eq_zero.1 e1).resolve_left (hc M hM).ne'
      have e3 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hy M y).1 e2 y (Finset.mem_univ _)
      linarith
    have hcm : ∀ M y (x : Fin n → ℤ), redV M x = y → classMin M (fun x z => B (r x) (r z)) y ≤ B (r x) (r x) :=
      fun M y x hx => classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB' (r x)) hx
    obtain ⟨t, ht0, rfl⟩ := (hI.2 B hB').2 hW
    refine ⟨t, ht0, ?_, rfl⟩
    intro v hv
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe] at hv
    obtain ⟨M, hM, y, a', ha'F, rfl⟩ := hv
    have e := hcl M hM y
    have e' := hcm M y a'.1 a'.2
    rw [e, hsum, hsum] at e'
    rw [hsum] at e
    have : ∑ i, ((vec M y a'.1 i : ℤ) : ℝ) * t i =
        ∑ i, t i * (u i (r (a M y)) (r (a M y)) : ℝ) - ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [vec]
      push_cast
      ring
    rw [this]
    linarith
  · intro t ht hA
    refine hback _ ⟨t, ht, rfl⟩ fun M hM y => ?_
    refine IsLeast.csInf_eq ⟨⟨a M y, ha M y, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a', ha'F, hle⟩ := hF M y ⟨x, hx⟩
    have hmem : vec M y a'.1 ∈ ⋃ M ∈ (𝓜 : Set ℕ), ⋃ y : Fin n → ZMod (M + 1),
        (fun a' : {a' : Fin n → ℤ // redV M a' = y} => vec M y a'.1) '' (F M y : Set _) := by
      simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
      exact ⟨M, hM, y, a', ha'F, rfl⟩
    have h1 := hA _ hmem
    have h2 : ∑ i, ((vec M y a'.1 i : ℤ) : ℝ) * t i =
        ∑ i, t i * (u i (r (a M y)) (r (a M y)) : ℝ) - ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [vec]
      push_cast
      ring
    have h3 : ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) ≤ ∑ i, t i * (u i (r x) (r x) : ℝ) := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
      have p1 := hu.nonneg i (r a'.1)
      have p2 := hu.nonneg i (r x)
      have p3 : (u i (r a'.1) (r a'.1)).toNat ≤ (u i (r x) (r x)).toNat := hle i
      exact_mod_cast (show u i (r a'.1) (r a'.1) ≤ u i (r x) (r x) by omega)
    show (∑ i, t i • toReal (u i)) (r (a M y)) (r (a M y)) ≤ (∑ i, t i • toReal (u i)) (r x) (r x)
    rw [hsum, hsum]
    linarith

end GlobalTheory.PolCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntFormDominatingPolFanBaseClassMinMeansStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intForm_dominating_polFanBase_classMinMeans : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Finite ℤ X] (N m n : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), 0 < D → IsPolFanOn (id : ℤ → ℤ) φs X → 0 < N → IsCone (id : ℤ → ℤ) φs u → StrictWith (id : ℤ → ℤ) φs N (linW w) u → Function.Surjective r → (∀ M y, redV M (a M y) = y) → ∃ A : Set (Fin m → ℤ), A.Finite ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (kDen N n 𝓜 : ℝ) * (baseFun (𝓞 E) D φs 𝓜).evalZ β ≤ evalW (lamW D N n 𝓜 r w a) (toReal β)) ∧ (∀ B ∈ psdCone (bar := H.bar) (X := X), (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) ∧ (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) (∑ i, t i • toReal (u i)) = evalW (lamW D N n 𝓜 r w a) (∑ i, t i • toReal (u i))) ∧ ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
  first | exact @GlobalTheory.PolCell.exists_contact_baseFun_lamW | exact GlobalTheory.PolCell.exists_contact_baseFun_lamW | (intros; apply GlobalTheory.PolCell.exists_contact_baseFun_lamW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoordsIntegralOfPartOfIntBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoordsIntegralOfPartOfIntBasis
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem GlobalTheory.cone_coords_int_of_isPartOfBasis : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i, u i ∈ balForms (id : ℤ → ℤ) X), IsPartOfBasis (fun i => (⟨u i, hu i⟩ : balForms (id : ℤ → ℤ) X)) → ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z := by
  intro X _ m u hu hpb β t h
  obtain ⟨n, b, hb⟩ := hpb
  have hpt : ∀ a y, (β a y : ℝ) = ∑ i, t i * (u i a y : ℝ) := fun a y => by
    have := LinearMap.congr_fun₂ h a y
    simpa [LinearMap.sum_apply, toReal_apply] using this
  have hsym : ∀ a y, β a y = β y a := fun a y => by
    have h1 := hpt a y
    have h2 := hpt y a
    have : (β a y : ℝ) = β y a := by
      rw [h1, h2]
      exact Finset.sum_congr rfl fun i _ => by rw [((mem_balForms_int).1 (hu i)) a y]
    exact_mod_cast this
  let β' : balForms (id : ℤ → ℤ) X := ⟨β, (mem_balForms_int).2 hsym⟩
  set s := b.repr β' with hs
  have hexp : ∀ a y, β a y = ∑ j, s j * ((b j : LinearMap.BilinForm ℤ X) a y) := fun a y => by
    have h0 := congrArg (fun γ : balForms (id : ℤ → ℤ) X => (γ : LinearMap.BilinForm ℤ X) a y) (b.sum_repr β')
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h0
    exact h0.symm
  let e : Fin m ⊕ Fin n → ℝ := Sum.elim t 0
  let c : Fin m ⊕ Fin n → ℝ := fun j => (s j : ℝ) - e j
  have hc : ∑ j, c j • toReal ((balForms (id : ℤ → ℤ) X).subtype (b j)) = 0 := by
    refine LinearMap.ext₂ fun a y => ?_
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, Submodule.subtype_apply, smul_eq_mul,
      LinearMap.zero_apply, c, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have e1 : (∑ j, (s j : ℝ) * ((b j : LinearMap.BilinForm ℤ X) a y : ℝ)) = β a y := by
      rw [hexp a y]; push_cast; rfl
    rw [e1, hpt a y, Fintype.sum_sum_type]
    simp [e, hb]
  intro i
  refine ⟨s (Sum.inl i), ?_⟩
  have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := (balForms (id : ℤ → ℤ) X).subtype) Subtype.val_injective
    (b.coord (Sum.inl i)) hc
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at this
  rw [Finset.sum_eq_single (Sum.inl i)] at this
  · simp [c, e] at this
    linarith
  · intro j _ hj; simp [hj]
  · simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoordsIntegralOfPartOfIntBasisStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realConeCoords_integral_of_partOfIntBasis : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i, u i ∈ balForms (id : ℤ → ℤ) X), IsPartOfBasis (fun i => (⟨u i, hu i⟩ : balForms (id : ℤ → ℤ) X)) → ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z := by
  first | exact @GlobalTheory.cone_coords_int_of_isPartOfBasis | exact GlobalTheory.cone_coords_int_of_isPartOfBasis | (intros; apply GlobalTheory.cone_coords_int_of_isPartOfBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRationalPolyhedralCellsUptoAut
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

theorem exists_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → HasRedCover H.bar X → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro E _ _ _ H g q φs 𝓜 X _ _ _ _ hφ hg hq hcov
  have LG : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.Finite ℤ X ∧ Module.Projective ℤ X ∧ Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := GlobalTheory.T.ringOfIntegers_projective_module_int_finrank
  have LN : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → ∃ N : ℕ, 0 < N ∧ ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u := GlobalTheory.T.exists_common_denominator_strictness_smooth_fan
  have LCov : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N p : ℕ) (P : Fin p → LinearMap.BilinForm ℤ X), IsPolFanOn (id : ℤ → ℤ) φ X → (∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u) → (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) → ∃ (s : ℕ) (m : Fin s → ℕ) (u : ∀ k, Fin (m k) → LinearMap.BilinForm ℤ X) (w : Fin s → (X × X) →₀ ℤ), (∀ k, IsCone (id : ℤ → ℤ) φ (u k) ∧ StrictWith (id : ℤ → ℤ) φ N (linW (w k)) (u k)) ∧ ∀ B ∈ rcone P, B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) → ∃ k, B ∈ rcone (u k) := GlobalTheory.T.exists_finite_polFanCones_cover_realCone
  have LDick : ∀ {ι : Type} (n : ℕ) (f : ι → Fin n → ℕ), ∃ F : Finset ι, ∀ i, ∃ j ∈ F, f j ≤ f i := GlobalTheory.T.dickson_exists_finite_subfamily_below
  have LPsi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Finite ℤ X] (N m n : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), 0 < D → IsPolFanOn (id : ℤ → ℤ) φs X → 0 < N → IsCone (id : ℤ → ℤ) φs u → StrictWith (id : ℤ → ℤ) φs N (linW w) u → Function.Surjective r → (∀ M y, redV M (a M y) = y) → ∃ A : Set (Fin m → ℤ), A.Finite ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (kDen N n 𝓜 : ℝ) * (baseFun (𝓞 E) D φs 𝓜).evalZ β ≤ evalW (lamW D N n 𝓜 r w a) (toReal β)) ∧ (∀ B ∈ psdCone (bar := H.bar) (X := X), (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) ∧ (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) (∑ i, t i • toReal (u i)) = evalW (lamW D N n 𝓜 r w a) (∑ i, t i • toReal (u i))) ∧ ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := GlobalTheory.T.exists_intForm_dominating_polFanBase_classMinMeans
  have LACL : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ψ : InvFun O) (K : ℕ) (Λ : (X × X) →₀ ℤ) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (A : Set (Fin m → ℤ)), A.Finite → 0 < K → (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) → (∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (K : ℝ) * ψ.evalZ β ≤ evalW Λ (toReal β)) → (∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) → (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → ∑ i, t i • toReal (u i) ∈ realForms bar X → (K : ℝ) * evalR ψ (∑ i, t i • toReal (u i)) = evalW Λ (∑ i, t i • toReal (u i))) → ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → B ∈ rcone γ := GlobalTheory.T.exists_cell_of_contactSet_intInequalities
  have LInt : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i, u i ∈ balForms (id : ℤ → ℤ) X), IsPartOfBasis (fun i => (⟨u i, hu i⟩ : balForms (id : ℤ → ℤ) X)) → ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z := GlobalTheory.T.realConeCoords_integral_of_partOfIntBasis
  have LPsd : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] [Module.Free ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X], psdCone (bar := bar) (X := X) ⊆ psdCone (bar := (id : ℤ → ℤ)) (X := X) := GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone

  obtain ⟨hfin, hproj, hrk⟩ := LG E X
  haveI := hfin
  haveI := hproj
  have hφX : IsPolFanOn (id : ℤ → ℤ) φs X := hφ X (by rw [hrk]; exact (Nat.mul_le_mul_left _ hq).trans hg)
  obtain ⟨N, hN, hD⟩ := LN X φs hφX
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' ℤ X
  obtain ⟨k, nP, P, hPs, hPp, hPc⟩ := hcov
  choose s mm u w huw hcj using fun j => LCov X φs N (nP j) (P j) hφX hD (hPs j) (hPp j)
  have hcls : ∀ (j : Fin k) (M : ℕ) (y : Fin n → ZMod (M + 1)), ∃ F : Finset (Fin n → ℤ), (∀ a ∈ F, redV M a = y) ∧
      ∀ B ∈ rcone (P j), ∃ a ∈ F, classMin M (fun x z => B (r x) (r z)) y = B (r a) (r a) := by
    intro j M y
    obtain ⟨F, hF⟩ := LDick (ι := {a : Fin n → ℤ // redV M a = y}) (nP j) fun a i => (P j i (r a.1) (r a.1)).toNat
    refine ⟨F.map (Function.Embedding.subtype _), fun a ha => ?_, ?_⟩
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 ha
      exact a.2
    · rintro B ⟨t, ht, rfl⟩
      have hval : ∀ a : Fin n → ℤ, (∑ i, t i • toReal (P j i)) (r a) (r a) = ∑ i, t i * (P j i (r a) (r a) : ℝ) := fun a => by
        simp [LinearMap.sum_apply]
      obtain ⟨a0, ha0, -⟩ := hF ⟨_, (redV_surjective M n y).choose_spec⟩
      obtain ⟨a1, ha1, hmin⟩ := Finset.exists_min_image (F.map (Function.Embedding.subtype _))
        (fun a => (∑ i, t i • toReal (P j i)) (r a) (r a)) ⟨_, Finset.mem_map_of_mem _ ha0⟩
      refine ⟨a1, ha1, IsLeast.csInf_eq ⟨⟨a1, ?_, rfl⟩, ?_⟩⟩
      · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 ha1
        exact a.2
      · rintro x ⟨a, ha, rfl⟩
        obtain ⟨a', ha', hle⟩ := hF ⟨a, ha⟩
        refine (hmin _ (Finset.mem_map_of_mem _ ha')).trans ?_
        simp only [Function.Embedding.subtype_apply, hval]
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
        have h1 := hle i
        have h2 := hPp j i (r a'.1)
        have h3 := hPp j i (r a)
        simp only at h1
        exact_mod_cast (by omega : P j i (r a'.1) (r a'.1) ≤ P j i (r a) (r a))
  choose F hFred hFmin using hcls
  let toA : ∀ j, (∀ M : 𝓜, ∀ y : Fin n → ZMod (M.1 + 1), ↥(F j M.1 y)) → ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ :=
    fun j c M y => if h : M ∈ 𝓜 then (c ⟨M, h⟩ y).1 else (redV_surjective M n y).choose
  have toA_red : ∀ j c M y, redV M (toA j c M y) = y := fun j c M y => by
    simp only [toA]
    split_ifs with h
    · exact hFred j M y _ (c ⟨M, h⟩ y).2
    · exact (redV_surjective M n y).choose_spec
  have hK : 0 < kDen N n 𝓜 := Nat.mul_pos hN (Finset.prod_pos fun _ _ => by positivity)
  have cell : ∀ (mu : ℕ) (uu : Fin mu → LinearMap.BilinForm ℤ X) (ww : (X × X) →₀ ℤ)
      (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), IsCone (id : ℤ → ℤ) φs uu →
      StrictWith (id : ℤ → ℤ) φs N (linW ww) uu → (∀ M y, redV M (a M y) = y) →
      ∃ (sγ : ℕ) (γ : Fin sγ → LinearMap.BilinForm ℤ X), IsCell H.bar (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) γ ∧
        ∀ B ∈ psdCone (bar := H.bar) (X := X), B ∈ rcone uu →
          (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → B ∈ rcone γ := by
    intro mu uu ww a hc hs ha
    obtain ⟨A, hA, hle, hcon, hback, hgen⟩ :=
      LPsi E H (fineDen g 𝓜) φs 𝓜 X N mu n uu ww r a (fineDen_pos g 𝓜) hφX hN hc hs hr ha
    obtain ⟨sγ, γ, hγ, hγc⟩ := LACL (𝓞 E) H.bar X (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (kDen N n 𝓜)
      (lamW (fineDen g 𝓜) N n 𝓜 r ww a) mu uu A hA hK (fun i => (hc.mem i).1) hc.nonneg
      (LInt X mu uu hc.mem hc.basis) hle hcon (fun t ht hA' _ => hback t ht hA')
    exact ⟨sγ, γ, hγ, fun B hB hBu hBc => hγc B hB (hgen B hBu hBc)⟩
  choose sγ γ hγ hγc using fun (j : Fin k) (d : Fin (s j) × (∀ M : 𝓜, ∀ y : Fin n → ZMod (M.1 + 1), ↥(F j M.1 y))) =>
    cell (mm j d.1) (u j d.1) (w j d.1) (toA j d.2) (huw j d.1).1 (huw j d.1).2 (toA_red j d.2)
  refine ⟨⋃ j, ⋃ d, Set.range (γ j d), Set.finite_iUnion fun j => Set.finite_iUnion fun d => Set.finite_range _,
    fun B hB => ?_⟩
  obtain ⟨e, j, c, hc0, hce⟩ := hPc B hB
  have hB' : pullR e.toLinearMap B ∈ psdCone (bar := H.bar) (X := X) := pullR_mem_psdCone e.surjective hB
  have hBP : pullR e.toLinearMap B ∈ rcone (P j) := ⟨c, hc0, hce⟩
  obtain ⟨kk, hkk⟩ := hcj j _ hBP (LPsd (𝓞 E) H.bar X hB')
  choose a0 ha0F ha0 using fun (M : 𝓜) y => hFmin j M.1 y _ hBP
  let d : Fin (s j) × (∀ M : 𝓜, ∀ y : Fin n → ZMod (M.1 + 1), ↥(F j M.1 y)) := (kk, fun M y => ⟨a0 M y, ha0F M y⟩)
  obtain ⟨c', hc', hBc⟩ := hγc j d _ hB' hkk fun M hM y => by
    simp only [toA, d, dif_pos hM]
    exact ha0 ⟨M, hM⟩ y
  exact ⟨e, _, γ j d, c', hγ j d, fun i => Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨d, i, rfl⟩⟩, hc', hBc⟩

end GlobalTheory.PolCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRationalPolyhedralCellsUptoAutStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_rational_polyhedral_cells_upto_aut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → HasRedCover H.bar X → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  first | exact @GlobalTheory.PolCell.exists_cells | exact GlobalTheory.PolCell.exists_cells | (intros; apply GlobalTheory.PolCell.exists_cells <;> assumption)
end
