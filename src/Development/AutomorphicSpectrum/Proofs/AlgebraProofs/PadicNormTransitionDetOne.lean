module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DTrans
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleIntersectionSymmetry

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicNormTransitionDetOne
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.DTransUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem transition_matrix_unique {I : Type} [Fintype I] [DecidableEq I] (e : I → D.La) (he : LinearIndependent (𝓞 E) e)
    (C : Matrix I I E) (hC : ∀ m y, ∑ n, C m n * sesq D (e n) y = 0) : C = 0 := by
  classical
  ext m k
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (Finset.univ.image (C m))
  choose u hu using fun n => hc (C m n) (Finset.mem_image_of_mem (C m) (Finset.mem_univ n))
  have hc0 : ((c : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero c
  have huv : ∀ n, (u n : E) = (c : 𝓞 E) * C m n := fun n => by
    rw [show ((u n : 𝓞 E) : E) = algebraMap (𝓞 E) E (u n) from rfl, hu n, Algebra.smul_def]
  set z : D.La := ∑ n, u n • e n with hz
  have hz0 : ∀ y, sesq D y z = 0 := by
    intro y
    have h1 : sesq D z y = 0 := by
      rw [hz, sesq_sum_smul_left]
      simp_rw [huv]
      calc ∑ n, (c : 𝓞 E) * C m n * sesq D (e n) y = (c : 𝓞 E) * ∑ n, C m n * sesq D (e n) y := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
        _ = 0 := by rw [hC m y, mul_zero]
    rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 z y, h1, map_zero, neg_zero]
  have hzz : z = 0 := (GlobalTheory.T.sesq_unimodular_dual E H D).1 z hz0
  have hu0 := (Fintype.linearIndependent_iff.1 he) u (by rw [← hz]; exact hzz)
  have : (c : 𝓞 E) * C m k = 0 := by rw [← huv, hu0 k]; simp
  simpa [hc0] using this

theorem isTransition_of_coefficients {I : Type} [Fintype I] (x e : I → D.La) (m : ℕ) (hm : 0 < m) (S : Matrix I I (𝓞 E))
    (hS : ∀ a, m • x a = ∑ b, S a b • e b) :
    IsTransition D x e (Matrix.of fun a b => (S a b : E) / m) := by
  intro a y
  have hm0 : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
  have h := congrArg (fun z => sesq D z y) (hS a)
  rw [sesq_sum_smul_left, ← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1] at h
  apply mul_left_cancel₀ hm0
  have h' : (m : E) * sesq D (x a) y = ∑ b, (S a b : E) * sesq D (e b) y := by simpa using h
  rw [h', Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.of_apply]
  field_simp

end

theorem padic_norm_transition_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La) (T : Matrix I I E) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → IsLocBasis (𝓞 E) ℓ e → IsTransition D x e T → ∀ j : E →+* ℂ_[ℓ], ‖j T.det‖ = 1 := by
  intro E _ _ _ H D I _ _ x e T ℓ hx he hT j
  classical
  have : Fact (Nat.Prime ℓ) := ⟨ℓ.2⟩
  obtain ⟨hxi, n0, hn0, hspx⟩ := hx
  obtain ⟨hei, m0, hm0, hspe⟩ := he
  have hm0p : 0 < m0 := Nat.pos_of_ne_zero fun h => hm0 (h ▸ dvd_zero _)
  have hn0p : 0 < n0 := Nat.pos_of_ne_zero fun h => hn0 (h ▸ dvd_zero _)
  choose S hS using fun a => (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hspe (x a))
  choose R hR using fun b => (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hspx (e b))
  have hT1 := isTransition_of_coefficients D x e m0 hm0p (Matrix.of S) fun a => (hS a).symm
  have hT2 := isTransition_of_coefficients D e x n0 hn0p (Matrix.of R) fun b => (hR b).symm
  set T1 : Matrix I I E := Matrix.of fun a b => ((Matrix.of S) a b : E) / m0
  set T2 : Matrix I I E := Matrix.of fun a b => ((Matrix.of R) a b : E) / n0

  have hTT1 : T = T1 := by
    have := transition_matrix_unique D e hei (T - T1) fun m y => by
      calc ∑ n, (T - T1) m n * sesq D (e n) y = ∑ n, T m n * sesq D (e n) y - ∑ n, T1 m n * sesq D (e n) y := by
            rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun n _ => by rw [Matrix.sub_apply, sub_mul]
        _ = 0 := by rw [← hT m y, ← hT1 m y, sub_self]
    exact sub_eq_zero.1 this

  have hTT2 : T2 * T = 1 := by
    have := transition_matrix_unique D e hei (T2 * T - 1) fun b y => by
      have hsum : ∑ n, (T2 * T) b n * sesq D (e n) y = sesq D (e b) y := by
        rw [hT2 b y]
        calc ∑ n, (T2 * T) b n * sesq D (e n) y = ∑ n, ∑ c, T2 b c * T c n * sesq D (e n) y := by
              refine Finset.sum_congr rfl fun n _ => ?_; rw [Matrix.mul_apply, Finset.sum_mul]
          _ = ∑ c, T2 b c * ∑ n, T c n * sesq D (e n) y := by
              rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
          _ = ∑ c, T2 b c * sesq D (x c) y := Finset.sum_congr rfl fun c _ => by rw [hT c y]
      have hone : ∑ n, (1 : Matrix I I E) b n * sesq D (e n) y = sesq D (e b) y := by
        rw [Finset.sum_eq_single b]
        · rw [Matrix.one_apply_eq, _root_.one_mul]
        · intro n _ hn; rw [Matrix.one_apply_ne (Ne.symm hn), MulZeroClass.zero_mul]
        · simp
      calc ∑ n, (T2 * T - 1) b n * sesq D (e n) y
            = ∑ n, (T2 * T) b n * sesq D (e n) y - ∑ n, (1 : Matrix I I E) b n * sesq D (e n) y := by
              rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun n _ => by rw [Matrix.sub_apply, sub_mul]
        _ = 0 := by rw [hsum, hone, sub_self]
    exact sub_eq_zero.1 this

  have hnat : ∀ k : ℕ, ¬ (ℓ : ℕ) ∣ k → ‖((k : ℕ) : ℂ_[ℓ])‖ = 1 := by
    intro k hk
    have hcop : Nat.Coprime k ℓ := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd ℓ.2).2 hk))
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * k + b * ℓ = 1 := by
      refine ⟨Nat.gcdA k ℓ, Nat.gcdB k ℓ, ?_⟩
      have := Nat.gcd_eq_gcd_ab k ℓ
      rw [hcop] at this
      push_cast at this
      linarith
    have h1 : ((a : ℂ_[ℓ]) * k + (b : ℂ_[ℓ]) * ℓ) = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : ℂ_[ℓ])) hab
    have hle : ‖((k : ℕ) : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    have ha : ‖(a : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
    have hb : ‖(b : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
    have hl := GlobalTheory.FlatCM.PlaceShiftModel.norm_ell (ℓ := (ℓ : ℕ))
    have hmax := IsUltrametricDist.norm_add_le_max ((a : ℂ_[ℓ]) * k) ((b : ℂ_[ℓ]) * ℓ)
    rw [h1, norm_one, norm_mul, norm_mul] at hmax
    have hbl : ‖(b : ℂ_[ℓ])‖ * ‖((ℓ : ℕ) : ℂ_[ℓ])‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hb) hl
    rcases le_max_iff.1 hmax with h | h
    · have : 1 ≤ ‖((k : ℕ) : ℂ_[ℓ])‖ := le_trans h (mul_le_of_le_one_left (norm_nonneg _) ha)
      exact le_antisymm hle this
    · exact absurd h (not_le.2 hbl)
  have hentry : ∀ (A : Matrix I I (𝓞 E)) (k : ℕ), ¬ (ℓ : ℕ) ∣ k → ∀ a b,
      ‖j (((Matrix.of fun a b => ((A a b : 𝓞 E) : E) / k) : Matrix I I E) a b)‖ ≤ 1 := by
    intro A k hk a b
    simp only [Matrix.of_apply, map_div₀, map_natCast, norm_div, hnat k hk, div_one]
    exact GlobalTheory.FlatCM.PlaceShiftModel.norm_le_one j (A a b)
  have hdet : ∀ M : Matrix I I E, (∀ a b, ‖j (M a b)‖ ≤ 1) → ‖j M.det‖ ≤ 1 := by
    intro M hM
    rw [RingHom.map_det]
    have := GlobalTheory.T.ultrametric_det_norm_le ℂ_[ℓ] I (M.map j) 1 zero_le_one (fun a b => hM a b)
    simpa using this
  have h1 : ‖j T.det‖ ≤ 1 := by rw [hTT1]; exact hdet _ (hentry (Matrix.of S) m0 hm0)
  have h2 : ‖j T2.det‖ ≤ 1 := hdet _ (hentry (Matrix.of R) n0 hn0)
  have hprod : ‖j T2.det‖ * ‖j T.det‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← Matrix.det_mul, hTT2, Matrix.det_one, map_one, norm_one]
  nlinarith [norm_nonneg (j T.det), norm_nonneg (j T2.det)]

end PositivityTheory.Xgf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicNormTransitionDetOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La) (T : Matrix I I E) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → IsLocBasis (𝓞 E) ℓ e → IsTransition D x e T → ∀ j : E →+* ℂ_[ℓ], ‖j T.det‖ = 1 := by
  first | exact @PositivityTheory.Xgf.padic_norm_transition_det_one | exact PositivityTheory.Xgf.padic_norm_transition_det_one
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicNormTransitionDetOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_norm_transition_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La) (T : Matrix I I E) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → IsLocBasis (𝓞 E) ℓ e → IsTransition D x e T → ∀ j : E →+* ℂ_[ℓ], ‖j T.det‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one | exact GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one | (intros; apply GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLieBundleIntersection
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionIntersection
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionComparison
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : (∀ k, ι k) → AddSubgroup V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), QuotExact O x A A' E.lat E'.lat C.lat C'.lat → ∃ E'' : ChartBundle O (mseg x) N V, LatLE O x E' E'' ∧ LatLE O x E'' E ∧ QuotEquiv O x A A' E''.lat E'.lat ∧ QuotEquiv O x E.lat E''.lat C.lat C'.lat := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hQ
  obtain ⟨Γ, Δ, hΓ, hΔ, hX⟩ := hQ
  have bundleOfFamily : ∀ (N : ℕ) (W : Type) [AddCommGroup W] [Module Ω W],
      (∀ Γ : (∀ k, ι k) → AddSubgroup W, IsLatFamily O x Γ →
        (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) →
        ∃ E : ChartBundle O (mseg x) N W, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧
      ∀ E : ChartBundle O (mseg x) N W, IsLatFamily O x E.lat ∧
        ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) := by
    classical
    intro N W _ _
    refine ⟨fun Γ hfam hloc => ?_, fun E => ⟨⟨fun s _ => E.stable s, fun s t hs ht => E.overlap s t hs ht⟩, fun s hs => ⟨E.stable s, E.frame s hs⟩⟩⟩
    refine ⟨{ lat := fun s => if mseg x s = 0 then ⊥ else Γ s
              stable := ?_
              frame := ?_
              overlap := ?_ }, ?_⟩
    · intro s a ha e he
      by_cases h : mseg x s = 0
      · simp only [h, if_true, AddSubgroup.mem_bot] at he ⊢
        rw [he, smul_zero]
      · simp only [h, if_false] at he ⊢
        exact hfam.1 s h a ha e he
    · intro s hs
      simp only [hs, if_false]
      exact (hloc s hs).2
    · intro s t hs ht e he
      simp only [hs, ht, if_false] at he ⊢
      exact hfam.2 s t hs ht e he
    · intro s hs
      simp only [hs, if_false]
  obtain ⟨F, hF⟩ : ∃ F : (∀ k, ι k) → AddSubgroup V,
      F = fun s => (Δ s).comap (AddMonoidHom.inl V V₂) := ⟨_, rfl⟩
  have memF : ∀ s b, b ∈ F s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s b
    subst hF
    exact Iff.rfl
  have hFlat : IsLatFamily O x F := by
    refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
    · have h := hΔ.1.1 s hs a ha (v, 0) ((memF s v).1 hv)
      rw [memF]
      simpa using h
    · obtain ⟨m, hm⟩ := hΔ.1.2 s t hs ht (v, 0) ((memF s v).1 hv)
      refine ⟨m, ?_⟩
      rw [memF]
      simpa using hm
  have hFfree : ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (F s) := by
    intro s hs
    have hE := ((bundleOfFamily N V).2 E).2 s hs
    have hC := ((bundleOfFamily N₂ V₂).2 C).2 s hs
    have hC' := ((bundleOfFamily N₂ V₂).2 C').2 s hs
    have h := (GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main (chartRing O (mseg x) s) N N₂ (E.lat s) (C.lat s)
      (C'.lat s) (Δ s) hE hC hC' (fun a ha v hv => hΔ.1.1 s hs a ha v hv)
      (fun v w h => (hΔ.2 s hs).1 v w h) (fun v hv => (hΔ.2 s hs).2.1 v hv)
      (fun w => (hΔ.2 s hs).2.2.1 w) (fun w hw => (hX s hs).2.1 w hw)).2
    rw [hF]
    exact h
  obtain ⟨E'', hE''⟩ := (bundleOfFamily N V).1 F hFlat hFfree
  have memE'' : ∀ s, mseg x s ≠ 0 → ∀ b, b ∈ E''.lat s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s hs b
    rw [hE'' s hs, memF]
  refine ⟨E'', fun s hs b hb => ?_, fun s hs b hb => ?_,
    ⟨Γ, ⟨hΓ.1, fun s hs => ⟨fun v w h => ⟨((hΓ.2 s hs).1 v w h).1,
        (memE'' s hs w).2 (((hX s hs).2.2 w).2 ⟨v, h⟩)⟩,
      (hΓ.2 s hs).2.1, (hΓ.2 s hs).2.2.1, (hΓ.2 s hs).2.2.2⟩⟩,
      fun s hs => ⟨(hX s hs).1, fun w hw => ((hX s hs).2.2 w).1 ((memE'' s hs w).1 hw)⟩⟩,
    ⟨Δ, ⟨hΔ.1, fun s hs => ⟨(hΔ.2 s hs).1, (hΔ.2 s hs).2.1, (hΔ.2 s hs).2.2.1,
        fun v hv => (memE'' s hs v).1 hv⟩⟩,
      fun s hs => ⟨fun v hv => (memE'' s hs v).2 hv, (hX s hs).2.1⟩⟩⟩
  · exact (memE'' s hs b).2 ((hΔ.2 s hs).2.2.2 b hb)
  · exact ((hΔ.2 s hs).1 b 0 ((memE'' s hs b).1 hb)).1

end GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionComparisonStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_extension_comparison : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : (∀ k, ι k) → AddSubgroup V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), QuotExact O x A A' E.lat E'.lat C.lat C'.lat → ∃ E'' : ChartBundle O (mseg x) N V, LatLE O x E' E'' ∧ LatLE O x E'' E ∧ QuotEquiv O x A A' E''.lat E'.lat ∧ QuotEquiv O x E.lat E''.lat C.lat C'.lat := by
  exact @GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle.main
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionIntersection
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotAdd

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : ChartBundle O (mseg x) N₀ V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x A A' → SameGeneric O x E E' → SameGeneric O x C C' → QuotExact O x A.lat A'.lat E.lat E'.lat C.lat C'.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ck O x d N₀ A A' k L Q + ck O x d N₂ C C' k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hM hA hE hC hX k hk1 hk2 q L Q hQ
  obtain ⟨E'', h1, h2, h3, h4⟩ :=
    GlobalTheory.T.chart_bundle_extension_comparison O Ω K ι x N₀ N N₂ V₀ V V₂ A.lat A'.lat E E' C C' hX
  have hEE'' : SameGeneric O x E E'' := fun s hs =>
    ⟨fun v hv => by
        obtain ⟨c, hc, hcv⟩ := (hE s hs).1 v hv
        exact ⟨c, hc, h1 s hs hcv⟩,
      fun v hv => ⟨1, one_ne_zero, by simpa using h2 s hs hv⟩⟩
  have hE''E' : SameGeneric O x E'' E' := fun s hs =>
    ⟨fun v hv => (hE s hs).1 v (h2 s hs hv),
      fun v hv => ⟨1, one_ne_zero, by simpa using h1 s hs hv⟩⟩
  have hcoc := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d N V E E'' E' hM hEE'' hE''E' k hk1 hk2 q L Q hQ).1
  have hAe := GlobalTheory.T.chart_bundle_intersection_symmetry O Ω K ι x d N₀ N V₀ V A A' E'' E' hM hA hE''E' h3 k hk1 hk2 q L Q hQ
  have hCe := GlobalTheory.T.chart_bundle_intersection_symmetry O Ω K ι x d N N₂ V V₂ E E'' C C' hM hEE'' hC h4 k hk1 hk2 q L Q hQ
  rw [hcoc, hAe, hCe, add_comm]

end GlobalTheory.CompanionTheory.Ar.Num.QuotAdd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionIntersectionStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_extension_intersection : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : ChartBundle O (mseg x) N₀ V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x A A' → SameGeneric O x E E' → SameGeneric O x C C' → QuotExact O x A.lat A'.lat E.lat E'.lat C.lat C'.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ck O x d N₀ A A' k L Q + ck O x d N₂ C C' k L Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.QuotAdd.main | exact GlobalTheory.CompanionTheory.Ar.Num.QuotAdd.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.QuotAdd.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLieBundleIntersection
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeTate

theorem algebraMap_ne_zero_of_model {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {x : (Σ k, ι k) → Ω} {d : ℕ}
    (hm : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d)
    {w : O} (hw : w ≠ 0) : algebraMap O Ω w ≠ 0 := by
  intro h0
  apply hw
  have hmem : w ∈ (mcIdeal O x).comap (C : O →+* MvPolynomial (Σ k, ι k) O) := by
    rw [Ideal.mem_comap]
    show _ = _
    have : (C w : MvPolynomial (Σ k, ι k) O) = algebraMap O _ w := rfl
    rw [this, AlgHom.commutes]
    simp [MvPolynomial.algebraMap_eq, h0]
  rw [hm.2.2.1] at hmem
  simpa using hmem

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d r s n : ℕ) (VL : Type) [AddCommGroup VL] [Module Ω VL] (VO : Type) [AddCommGroup VO] [Module Ω VO] (VH : Type) [AddCommGroup VH] [Module Ω VH] (Lie W La : ChartBundle O (mseg x) r VL) (om omHT : ChartBundle O (mseg x) s VO) (T H : ChartBundle O (mseg x) n VH) (w : O), w ≠ 0 → GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → LatLE O x Lie W → LatLE O x W La → IsScaled x (algebraMap O Ω w) La.lat Lie.lat → SameGeneric O x om omHT → SameGeneric O x H T → QuotExact O x La.lat W.lat H.lat T.lat om.lat omHT.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d r Lie W k L Q + ck O x d s om omHT k L Q = ck O x d n H T k L Q - (k : ℤ) * rootNum O x d r Lie (psum (Fin r) ℤ (k - 1)) L Q w := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d r s n VL _ _ VO _ _ VH _ _ Lie W La om omHT T H w hw hm hLW hWL hsc
    hom hHT hex k hk1 hk2 q L Q hQ
  have hw' : algebraMap O Ω w ≠ 0 := algebraMap_ne_zero_of_model hm hw
  have hscale : ∀ s, mseg x s ≠ 0 → ∀ v ∈ La.lat s, algebraMap O Ω w • v ∈ Lie.lat s :=
    fun s hs v hv => (hsc s hs _).2 ⟨v, hv, rfl⟩
  have sWLa : SameGeneric O x W La := fun s hs =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hWL s hs hv⟩,
      fun v hv => ⟨w, hw, hLW s hs (hscale s hs v hv)⟩⟩
  have sLaW : SameGeneric O x La W := fun s hs => ⟨(sWLa s hs).2, (sWLa s hs).1⟩
  have sLieW : SameGeneric O x Lie W := fun s hs =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hLW s hs hv⟩,
      fun v hv => ⟨w, hw, hscale s hs v (hWL s hs hv)⟩⟩
  have sWLie : SameGeneric O x W Lie := fun s hs => ⟨(sLieW s hs).2, (sLieW s hs).1⟩
  have sLaLa : SameGeneric O x La La := fun s hs =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  have h1 := GlobalTheory.T.chart_bundle_extension_intersection O Ω K ι x d r n s VL VH VO La W H T om omHT hm sLaW hHT hom hex k hk1 hk2
    q L Q hQ
  have h2 := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d r VL La W Lie hm sLaW sWLie k hk1 hk2 q L Q hQ).1
  have h3 := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d r VL Lie W Lie hm sLieW sWLie k hk1 hk2 q L Q hQ).2
  have h4 := (GlobalTheory.T.dvr_bundle_statement_d O Ω K ι x d r VL La Lie w hw hm hsc k hk1 hk2 q L Q hQ).1
  have hcarry : ∀ s, mseg x s ≠ 0 → ∀ v,
      ((LinearEquiv.smulOfNeZero Ω VL _ hw') v ∈ Lie.lat s ↔ v ∈ La.lat s) ∧
        ((LinearEquiv.smulOfNeZero Ω VL _ hw') v ∈ Lie.lat s ↔ v ∈ La.lat s) := by
    intro s hs v
    have : (LinearEquiv.smulOfNeZero Ω VL _ hw') v ∈ Lie.lat s ↔ v ∈ La.lat s := by
      rw [LinearEquiv.smulOfNeZero_apply, hsc s hs]
      constructor
      · rintro ⟨e, he, hve⟩
        rwa [smul_right_injective VL hw' hve]
      · exact fun hv => ⟨v, hv, rfl⟩
    exact ⟨this, this⟩
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have : d - (k - 1) = d + 1 - k := by omega
    rwa [this]
  have h5 := (GlobalTheory.T.same_generic_linear_equiv O Ω K ι x d hm r VL VL (LinearEquiv.smulOfNeZero Ω VL _ hw') La La Lie Lie
    sLaLa hcarry).2 (k - 1) (psum (Fin r) ℤ (k - 1)) (psum_isSymmetric _ _ _)
    (isHomogeneous_psum r (k - 1)) (by omega) q L Q hQ' w hw
  rw [h5]
  linarith

end GlobalTheory.CompanionTheory.Ar.Num.HodgeTate
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLieBundleIntersectionStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lie_bundle_intersection : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d r s n : ℕ) (VL : Type) [AddCommGroup VL] [Module Ω VL] (VO : Type) [AddCommGroup VO] [Module Ω VO] (VH : Type) [AddCommGroup VH] [Module Ω VH] (Lie W La : ChartBundle O (mseg x) r VL) (om omHT : ChartBundle O (mseg x) s VO) (T H : ChartBundle O (mseg x) n VH) (w : O), w ≠ 0 → GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → LatLE O x Lie W → LatLE O x W La → IsScaled x (algebraMap O Ω w) La.lat Lie.lat → SameGeneric O x om omHT → SameGeneric O x H T → QuotExact O x La.lat W.lat H.lat T.lat om.lat omHT.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d r Lie W k L Q + ck O x d s om omHT k L Q = ck O x d n H T k L Q - (k : ℤ) * rootNum O x d r Lie (psum (Fin r) ℤ (k - 1)) L Q w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeTate.main | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeTate.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeTate.main <;> assumption)
end
end
