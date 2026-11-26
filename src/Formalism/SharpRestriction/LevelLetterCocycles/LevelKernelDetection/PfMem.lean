module

public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.XPowDvdOfComponents

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.CombineProd
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

section Alg

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem combine_two (a b l u w : R) (k : ℕ) (hl : u * a + w * b = l ^ k) (y y₁ y₂ : V)
    (ha : y = a • y₁) (hb : y = b • y₂) :
    l ^ k • y = (a * b) • (u • y₂ + w • y₁) := by
  have e1 : (u * a) • y = (a * b * u) • y₂ := by
    rw [hb, smul_smul]
    congr 1
    ring
  have e2 : (w * b) • y = (a * b * w) • y₁ := by
    rw [ha, smul_smul]
    congr 1
    ring
  rw [← hl, add_smul, e1, e2, smul_add, smul_smul, smul_smul]

theorem combine_pow (l x y : R) (hl : l ∈ Ideal.span ({x, y} : Set R)) (a b : ℕ) :
    l ^ (a + b) ∈ Ideal.span ({x ^ a, y ^ b} : Set R) := by
  obtain ⟨u, w, huw⟩ := Ideal.mem_span_pair.1 hl
  rw [← huw]
  refine Ideal.add_pow_mem_of_pow_mem_of_le (m := a) (n := b) (k := a + b) _ ?_ ?_ (by omega)
  · rw [mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem combine_prod (l q : R) (a : ℕ → R) (m : ℕ)
    (h : ∀ s < m, ∃ j : ℕ, l ^ j ∈ Ideal.span ({a s, q} : Set R)) :
    ∃ j : ℕ, l ^ j ∈ Ideal.span ({∏ s ∈ Finset.range m, a s, q} : Set R) := by
  induction m with
  | zero =>
    refine ⟨0, Ideal.subset_span ?_⟩
    simp
  | succ m ih =>
    obtain ⟨j₁, h₁⟩ := ih (fun s hs => h s (by omega))
    obtain ⟨j₂, h₂⟩ := h m (by omega)
    obtain ⟨u₁, w₁, e₁⟩ := Ideal.mem_span_pair.1 h₁
    obtain ⟨u₂, w₂, e₂⟩ := Ideal.mem_span_pair.1 h₂
    refine ⟨j₁ + j₂, Ideal.mem_span_pair.2 ⟨u₁ * u₂,
      u₁ * (∏ s ∈ Finset.range m, a s) * w₂ + w₁ * u₂ * a m + w₁ * w₂ * q, ?_⟩⟩
    rw [Finset.prod_range_succ, pow_add, ← e₁, ← e₂]
    ring

theorem combine_mod (N : Submodule R V) (l : R) (p : ℕ → R)
    (hcop : ∀ s s' : ℕ, s ≠ s' → l ∈ Ideal.span ({p s, p s'} : Set R)) (E : ℕ → ℕ) (y : V)
    (hy : y ∈ N) (ell : ℕ) (h : ∀ s < ell, ∃ y' ∈ N, y = p s ^ E s • y') :
    ∃ K : ℕ, ∃ z ∈ N, l ^ K • y = (∏ s ∈ Finset.range ell, p s ^ E s) • z := by
  induction ell with
  | zero => exact ⟨0, y, hy, by simp⟩
  | succ m ih =>
    obtain ⟨K, z, hz, hK⟩ := ih (fun s hs => h s (by omega))
    obtain ⟨y₂, hy₂, e₂⟩ := h m (by omega)
    obtain ⟨j, hj⟩ := combine_prod l (p m ^ E m) (fun s => p s ^ E s) m
      (fun s hs => ⟨E s + E m, combine_pow l (p s) (p m) (hcop s m (by omega)) (E s) (E m)⟩)
    obtain ⟨u, w, huw⟩ := Ideal.mem_span_pair.1 hj
    have e := combine_two (∏ s ∈ Finset.range m, p s ^ E s) (p m ^ E m) l u w j huw
      (l ^ K • y) z (l ^ K • y₂) hK (by rw [e₂, smul_comm])
    refine ⟨j + K, u • l ^ K • y₂ + w • z,
      N.add_mem (N.smul_mem _ (N.smul_mem _ hy₂)) (N.smul_mem _ hz), ?_⟩
    rw [Finset.prod_range_succ, pow_add, mul_smul, e]

end Alg

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem combine_cop [IsDomain O] (hR : Ring9 W) (s s' : ℕ) (hss : s ≠ s') :
    PowerSeries.C (((PD.p : ℕ) : O)) ∈
      Ideal.span ({(baseIdOf hR).Bs.p s, (baseIdOf hR).Bs.p s'} : Set (PowerSeries O)) := by
  obtain ⟨u, hu⟩ := frobenius_uniformizer_identity hR
  have h2 := PD.hp.two_le
  have hℓ : (baseIdOf hR).Bs.ℓ = PD.p := rfl
  have hdvd : (PowerSeries.X * (PowerSeries.X + PowerSeries.C (((baseIdOf hR).Bs.ℓ : ℕ) : O)) :
      PowerSeries O) ∣ (baseIdOf hR).Bs.φ PowerSeries.X := by
    refine ⟨(u : PowerSeries O) * (baseIdOf hR).Bs.q ^ ((baseIdOf hR).Bs.ℓ - 2), ?_⟩
    rw [hu]
    have e : (baseIdOf hR).Bs.ℓ - 1 = ((baseIdOf hR).Bs.ℓ - 2) + 1 := by rw [hℓ]; omega
    rw [e, pow_succ]
    change _ = PowerSeries.X * (baseIdOf hR).Bs.q * _
    ring
  exact (LevelStatements.Lv.psCoprime O (baseIdOf hR).Bs.ℓ (baseIdOf hR).Bs.φ hdvd).2 s s' hss

theorem combine [IsDomain O] (hSat : Sat W) (hcrys : IsCrys PD T.ρ) (ell : ℕ) (E : ℕ → ℕ) (y : C.V)
    (hy : y ∈ (latOf C).N c)
    (h : ∀ s < ell, ∃ y' ∈ (latOf C).N c, y = (baseIdOf hR).Bs.p s ^ E s • y') :
    ∃ y' ∈ (latOf C).N c, y = (∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ E s) • y' := by
  set κ : PowerSeries O := ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ E s with hκ
  obtain ⟨K, z, hz, hK⟩ := combine_mod ((latOf C).N c) (PowerSeries.C (((PD.p : ℕ) : O)))
    (fun s => (baseIdOf hR).Bs.p s) (combine_cop hR) E y hy ell h
  have hd : (baseIdOf hR).d κ = ∏ s ∈ Finset.range ell, pS W s ^ E s := by
    rw [hκ, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, BaseId.d_p]
  have hdl : (baseIdOf hR).d (PowerSeries.C (((PD.p : ℕ) : O)) ^ K) =
      ((PD.p : ℕ) : LetA O n) ^ K := by
    rw [map_pow, BaseId.d_C, map_natCast]
  have hNΔ : ∀ x : W.DD T, x ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ x = x) → x ∈ W.NΔ T :=
    fun x h1 h2 => ⟨h1, h2⟩
  have hx : C.t c y ∈ mulSet W T ((baseIdOf hR).d κ) (W.NΔ T) := by
    refine hSat T ((baseIdOf hR).d κ) 1 hcrys ⟨0, (baseIdOf hR).d κ, ⟨E, ell, hd⟩, by simp⟩
      ⟨0, 1, ⟨fun _ => 0, 0, by simp⟩, by simp⟩ (C.t c y) (fun δ hδ => C.t_Δ c y δ hδ) ?_ ?_
    · rw [one_smul]
      exact hNΔ _ hy (fun δ hδ => C.t_Δ c y δ hδ)
    · refine ⟨K, C.t c z, hNΔ _ hz (fun δ hδ => C.t_Δ c z δ hδ), ?_⟩
      rw [← hdl, ← Coord.t_smul, hK, Coord.t_smul]
  obtain ⟨z', hz', hxz⟩ := hx
  have hlet : (letE c : LetA O n) • ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    rw [smul_smul, letE_mul_self]
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    intro δ hδ
    rw [WachCoordinates.γD_smulA, γA_letE, hz'.2 δ hδ]
  obtain ⟨y'', hy''⟩ := C.t_surj c _ hlet hΔ
  refine ⟨y'', ?_, ?_⟩
  · show C.t c y'' ∈ W.N T
    rw [hy'']
    exact (W.N T).smul_mem _ hz'.1
  · apply C.t_inj c
    rw [Coord.t_smul, hy'', smul_smul, mul_comm, ← smul_smul, ← hxz, C.t_letter]

end Formalism.MainNotions.N.Ln03.K8

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PowerSeriesCancelBounded
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Content

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem C_dvd_iff_dvd_coeffs (ϖ : O) (f : PowerSeries O) :
    PowerSeries.C ϖ ∣ f ↔ ∀ k, ϖ ∣ PowerSeries.coeff k f := by
  constructor
  · rintro ⟨g, rfl⟩ k
    rw [PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose g hg using h
    refine ⟨PowerSeries.mk g, ?_⟩
    ext k
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hg]

theorem prime_C_uniformizer {ϖ : O} (hϖ : Irreducible ϖ) : Prime (PowerSeries.C ϖ : PowerSeries O) := by
  have : (Ideal.span {ϖ} : Ideal O).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).2 hϖ.prime
  have key : ∀ f : PowerSeries O, PowerSeries.C ϖ ∣ f ↔
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f = 0 := by
    intro f
    rw [C_dvd_iff_dvd_coeffs]
    constructor
    · intro h
      ext k
      rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact h k
    · intro h k
      have h1 := congrArg (PowerSeries.coeff k) h
      rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
      exact h1
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hϖ.ne_zero
    simpa using congrArg PowerSeries.constantCoeff h
  · intro hu
    apply hϖ.not_isUnit
    simpa using hu.map PowerSeries.constantCoeff
  · intro f g hfg
    rw [key, map_mul] at hfg
    rcases mul_eq_zero.1 hfg with h | h
    · exact Or.inl ((key f).2 h)
    · exact Or.inr ((key g).2 h)

theorem power_series_cancel_bounded (q : O) {f : PowerSeries O} (hf : f ≠ 0) :
    ∃ c₀ : ℕ, ∀ (k : ℕ) (g : PowerSeries O),
      (PowerSeries.C q) ^ (k + c₀) ∣ f * g → (PowerSeries.C q) ^ k ∣ g := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hP := prime_C_uniformizer hϖ
  set P : PowerSeries O := PowerSeries.C ϖ with hPdef
  have hex : ∃ v : ℕ, ¬ P ^ (v + 1) ∣ f := by
    obtain ⟨k, hk⟩ : ∃ k, PowerSeries.coeff k f ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hf (PowerSeries.ext fun k => by simpa using hall k)
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hk hϖ
    refine ⟨e, fun hd => ?_⟩
    rw [hPdef, ← map_pow, C_dvd_iff_dvd_coeffs] at hd
    have h1 : ϖ ^ (e + 1) ∣ ϖ ^ e := he.dvd_iff_dvd_right.1 (hd k)
    have h2 := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h1
    omega
  classical
  set v := Nat.find hex with hv
  have hnot : ¬ P ^ (v + 1) ∣ f := Nat.find_spec hex
  have hdv : P ^ v ∣ f := by
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · rw [h0, pow_zero]
      exact one_dvd _
    · have h1 := not_not.1 (Nat.find_min hex (show v - 1 < v by omega))
      rwa [show v - 1 + 1 = v by omega] at h1
  obtain ⟨f', hf'⟩ := hdv
  have hf'P : ¬ P ∣ f' := by
    rintro ⟨u, hu⟩
    apply hnot
    exact ⟨u, by rw [hf', hu, pow_succ, mul_assoc]⟩
  have iter : ∀ (M : ℕ) (g : PowerSeries O), P ^ M ∣ f' * g → P ^ M ∣ g := by
    intro M
    induction M with
    | zero => intro g _; rw [pow_zero]; exact one_dvd _
    | succ M ih =>
      intro g hg
      have h1 : P ∣ f' * g := dvd_trans (dvd_pow_self P (Nat.succ_ne_zero M)) hg
      obtain ⟨g', rfl⟩ := (hP.dvd_or_dvd h1).resolve_left hf'P
      have h2 : P ^ M ∣ f' * g' := by
        rw [pow_succ', show f' * (P * g') = P * (f' * g') by ring] at hg
        exact (mul_dvd_mul_iff_left hP.ne_zero).1 hg
      rw [pow_succ']
      exact mul_dvd_mul_left P (ih g' h2)
  refine ⟨v, fun k g hg => ?_⟩
  by_cases hq : q = 0
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, pow_zero]
      exact one_dvd _
    · rw [hq, map_zero, zero_pow (by omega), zero_dvd_iff] at hg
      rcases mul_eq_zero.1 hg with h | h
      · exact absurd h hf
      · rw [h]
        exact dvd_zero _
  · obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hq hϖ
    have hA : ∀ j : ℕ, Associated ((PowerSeries.C q) ^ j) (P ^ (e * j)) := fun j => by
      have h0 := (he.map PowerSeries.C).pow_pow (n := j)
      rw [map_pow, ← pow_mul] at h0
      exact h0
    rcases Nat.eq_zero_or_pos e with he0 | he0
    · rw [(hA k).dvd_iff_dvd_left, he0, zero_mul, pow_zero]
      exact one_dvd _
    · rw [(hA (k + v)).dvd_iff_dvd_left, hf'] at hg
      have h1 : P ^ v * P ^ (e * k) ∣ P ^ v * (f' * g) := by
        rw [← pow_add, ← mul_assoc]
        exact dvd_trans (pow_dvd_pow P (by nlinarith)) hg
      have h2 := (mul_dvd_mul_iff_left (pow_ne_zero v hP.ne_zero)).1 h1
      rw [(hA k).dvd_iff_dvd_left]
      exact iter _ g h2

end Content

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem isRegular_image_in_EE [IsDomain O] [IsDiscreteValuationRing O] (hR : Ring9 W)
    {κ : PowerSeries O} (hκ : κ ≠ 0) (x : W.EE)
    (hx : algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ) * x = 0) : x = 0 := by
  have := W.EE_complete
  have hf : (baseIdOf hR).ι κ ≠ 0 := fun h => hκ (baseIdOf_inj hR (by rw [h, map_zero]))
  obtain ⟨c₀, hc₀⟩ := power_series_cancel_bounded ((PD.p : ℕ) : O) hf
  have key : ∀ k : ℕ, x ∈ Ideal.span {((PD.p : ℕ) : W.EE) ^ k} := by
    intro k
    obtain ⟨a, m, ham⟩ := W.EE_dense x (k + c₀)
    have h1 : algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ * a) ∈
        Ideal.span {((PD.p : ℕ) : W.EE) ^ (k + c₀)} := by
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ham
      rw [Ideal.mem_span_singleton']
      refine ⟨-(algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ) * y), ?_⟩
      have e : algebraMap (LetA O n) W.EE a =
          x * algebraMap (LetA O n) W.EE (letπ ^ m) - y * ((PD.p : ℕ) : W.EE) ^ (k + c₀) := by
        rw [hy]; ring
      rw [map_mul, e, mul_sub, ← mul_assoc, hx, zero_mul]
      ring
    obtain ⟨b, hb⟩ := W.EE_sat _ _ h1
    have h2 : ∀ i, (PowerSeries.C ((PD.p : ℕ) : O)) ^ k ∣ a i := by
      intro i
      apply hc₀ k (a i)
      have h3 := congrFun hb i
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, BaseId.d_apply] at h3
      rw [map_natCast, h3]
      exact dvd_mul_right _ _
    choose d hd using h2
    have h4 : algebraMap (LetA O n) W.EE a ∈ Ideal.span {((PD.p : ℕ) : W.EE) ^ k} := by
      have h5 : a = ((PD.p : ℕ) : LetA O n) ^ k * d := by
        funext i
        simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply]
        rw [hd i, map_natCast]
      rw [h5, map_mul, map_pow, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have ham' : x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a ∈
        Ideal.span {((PD.p : ℕ) : W.EE) ^ k} :=
      Ideal.mem_span_singleton.2 (dvd_trans (pow_dvd_pow _ (Nat.le_add_right k c₀))
        (Ideal.mem_span_singleton.1 ham))
    have h6 := Ideal.add_mem _ ham' h4
    rw [sub_add_cancel, map_pow] at h6
    exact (Ideal.mul_unit_mem_iff_mem _ (W.EE_π.pow m)).1 h6
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {((PD.p : ℕ) : W.EE)}) W.EE) x
    fun k => ?_
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact key k

theorem smul_cancel [IsDomain O] [IsDiscreteValuationRing O] (κ : PowerSeries O) (hκ : κ ≠ 0)
    (x y : C.V) (h : κ • x = κ • y) : x = y := by
  have hz : (baseIdOf hR).d κ • C.t 0 (x - y) = 0 := by
    rw [← C.t_smul, smul_sub, h, sub_self, C.t_zero]
  have hz' : algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ) • C.t 0 (x - y) = 0 := by
    rw [algebraMap_smul]
    exact hz
  have := (W.DD_free T).1
  have h0 : C.t 0 (x - y) = 0 := by
    apply (Module.Free.chooseBasis W.EE (W.DD T)).repr.injective
    ext k
    have h2 := congrArg (fun z => (Module.Free.chooseBasis W.EE (W.DD T)).repr z k) hz'
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at h2
    rw [map_zero, Finsupp.zero_apply]
    exact isRegular_image_in_EE hR hκ _ h2
  exact sub_eq_zero.1 (C.t_inj 0 (by rw [h0, C.t_zero]))

end Formalism.MainNotions.N.Ln03.K8
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03.K8

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem mem_holds [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (hP4 : LevelMapHodgeFiltration W)
    (hSat : Sat W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hfree : (latOf C).Free c)
    (hζ : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    {ell : ℕ} (hell : ell ≤ n) {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c} (m : ℕ)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (hfilt : ∀ s < ell, IsFilt (FilD W T c s)) (ϖ : O)
    (hcompl : ∀ s < ell, ∀ (k : ℕ) (a : PowerSeries O), PowerSeries.X ^ k ∣ rhoL hR c s a →
      ∃ (N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * a = (baseIdOf hR).Bs.p s ^ k * z)
    (hϖ : ∃ (N : ℕ) (u : O), ((PD.p : ℕ) : O) ^ N = ϖ * u)
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam)
    (f' : PowerSeries O) (kind : ℕ → Kind) (b : ℕ → ℕ) (η : ℕ) :
    (lvData Hy f' kind b η).Mem := by
  intro x
  have hκE : κ = ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ (H s + m) := by
    rw [hκ, Formalism.ExponentWindows.abelian₂, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => (pow_add _ _ _).symm
  have hloc : ∀ s (hs : s < ell), (lvData Hy f' kind b η).loc s x ∈ (lvData Hy f' kind b η).Nl s ↔
      Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) •
        expN Lb s T c ⟨C.t c (κ • (x : C.V)), Hy.kap x x.2⟩ ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) := by
    intro s hs
    change prL s (locM Lb C Hy.delta ell _ κ Hy.kap Hy.expSemi Hy.locInv x) ∈ Xi _ _ ↔ _
    rw [prL_of_lt s hs]
    rfl
  constructor
  · intro hx s hs
    rw [hloc s hs]
    have hm : (baseIdOf hR).d κ • ((⟨C.t c x, hx⟩ : ↥(W.N T)) : W.DD T) ∈ W.N T := by
      have h0 := Hy.kap x x.2
      change C.t c (κ • (x : C.V)) ∈ W.N T at h0
      rwa [C.t_smul] at h0
    have e1 : (⟨C.t c (κ • (x : C.V)), Hy.kap x x.2⟩ : ↥(W.N T)) = ⟨(baseIdOf hR).d κ • C.t c x, hm⟩ :=
      Subtype.ext (C.t_smul c κ x)
    rw [e1, Hy.expSemi s κ ⟨C.t c x, hx⟩ hm, smul_smul]
    by_cases hu : IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ))
    · rw [Ring.inverse_mul_cancel _ hu, one_smul]
      exact expN_mem_xi hP4 hcrys hLb s _
    · rw [Ring.inverse_non_unit _ hu, zero_mul, zero_smul]
      exact zero_mem _
  · intro h
    have hy : κ • (x : C.V) ∈ (latOf C).N c := Hy.kap x x.2
    have hdet : ∀ s < ell, ∃ y' ∈ (latOf C).N c,
        κ • (x : C.V) = (baseIdOf hR).Bs.p s ^ (H s + m) • y' := by
      intro s hs
      have h1 : Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s)
          (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ (H s' + m)))) •
          expN Lb s T c ⟨C.t c (κ • (x : C.V)), hy⟩ ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) := by
        rw [← hκE]
        exact (hloc s hs).1 (h s hs)
      exact detect hP4 hSat hcrys hLb hmod hP3 hfree ϖ ell hcompl hϖ s hs (hfilt s hs) (H s + m) _ hy
        ((levelCond_iff ell hk1b hunits (fun s' => H s' + m) s hs _ hy Hy.filAnti).1 h1)
    obtain ⟨y', hy', hyy⟩ := combine hSat hcrys ell (fun s' => H s' + m) _ hy hdet
    have hp0 : ∀ s < ell, (baseIdOf hR).Bs.p s ≠ 0 := by
      intro s hs h0
      obtain ⟨ζ, hζ⟩ := hζ
      have hdvd : PD.p ^ (s + 1) ∣ PD.p ^ n := pow_dvd_pow _ (by omega)
      have hprim : IsPrimitiveRoot (ζ ^ (PD.p ^ n / PD.p ^ (s + 1))) (PD.p ^ (s + 1)) := by
        have := hζ.pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (pow_pos PD.hp.pos _) hdvd)
          (pow_pos PD.hp.pos _)).ne' (Nat.div_dvd_of_dvd hdvd)
        rwa [Nat.div_div_self hdvd (pow_pos PD.hp.pos _).ne'] at this
      have : Nonempty (Rs LL PD.p s) :=
        ⟨⟨_, (mem_primitiveRoots (pow_pos PD.hp.pos _)).2 hprim⟩⟩
      obtain ⟨ε, hε⟩ := hk1b s hs
      rw [h0, map_zero] at hε
      exact PowerSeries.X_ne_zero ((Units.mul_right_eq_zero ε).1 hε.symm)
    have hκ0 : κ ≠ 0 := by
      rw [hκE]
      exact Finset.prod_ne_zero_iff.2 fun s hs => pow_ne_zero _ (hp0 s (Finset.mem_range.1 hs))
    have hxy : (x : C.V) = y' := by
      apply smul_cancel κ hκ0
      rw [hyy, ← hκE]
    rw [hxy]
    exact hy'

end Formalism.MainNotions.N.Ln03.Pf

end
