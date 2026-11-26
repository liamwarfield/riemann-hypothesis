module

public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerCommensurableInvVolumeSmulComplement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

private lemma exists_integer_eq_star {K : Type} [Field K] [NumberField K] [StarRing K]
    (a : 𝓞 K) : ∃ b : 𝓞 K, (b : K) = star (a : K) := by
  have hint : IsIntegral ℤ (starRingEnd K (a : K)) :=
    map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe a)
  rw [starRingEnd_apply] at hint
  exact ⟨⟨star (a : K), (mem_integralClosure_iff ℤ K).2 hint⟩, rfl⟩

theorem _root_.GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K →
      ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by
  intro K _ _ _ h
  unfold _root_.Formalism.HermitianLatticesTheory.IsCMUnram at h
  obtain ⟨-, -, hP⟩ := h
  let S : Set (𝓞 K) := {x | ∃ θ τ : 𝓞 K,
    algebraMap (𝓞 K) K τ = star (algebraMap (𝓞 K) K θ) ∧ x = θ - τ}
  let I : Ideal (𝓞 K) := Ideal.span S
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨θ, τ, hτ, hnot⟩ := hP P hPm
    exact hnot (hle (Ideal.subset_span ⟨θ, τ, hτ, rfl⟩))
  have key : ∀ x ∈ I, ∃ t : 𝓞 K, (x : K) * star (x : K) = (t : K) + star (t : K) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨θ, τ, hτ, rfl⟩ := hx
      change (τ : K) = star (θ : K) at hτ
      have h2 : star (τ : K) = θ := by rw [hτ, star_star]
      refine ⟨θ * (τ - θ), ?_⟩
      push_cast
      rw [star_sub, star_mul', star_sub, h2, ← hτ]
      ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨u, hu⟩ := hy
      obtain ⟨y', hy'⟩ := exists_integer_eq_star y
      refine ⟨s + u + x * y', ?_⟩
      push_cast
      simp only [star_add, star_mul', hy', star_star]
      linear_combination hs + hu
    | smul c x _ hx =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨c', hc'⟩ := exists_integer_eq_star c
      refine ⟨c * c' * s, ?_⟩
      rw [smul_eq_mul]
      push_cast
      simp only [star_mul', hc', star_star]
      linear_combination ((c : K) * star (c : K)) * hs
  obtain ⟨t, ht⟩ := key 1 (hI ▸ Submodule.mem_top)
  exact ⟨t, by simpa using ht.symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.FrameGram

theorem std_frame_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0 ∧ (∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) ∧ (∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) ∧ (∀ i j, gramE σ J (F0 P) i j = if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧ ∀ v : HeightOneSpectrum (𝓞 F), LinearIndependent (Fv F v ⊗[F] E) (ratTup (F := F) (Fv F v) (F0 P)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ r P T hP
  obtain ⟨he, _, hf, hez, _, hz, hT⟩ := hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := frame_gram_snoc hσ hJ P.e P.f P.z T hT he hez hz hf
    (F0 P) rfl (tupH P) rfl
  exact ⟨h1, h2, h3, h4, fun v => h5 _⟩

end GlobalTheory.FrameGram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZeroStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrame_gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0 ∧ (∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) ∧ (∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) ∧ (∀ i j, gramE σ J (F0 P) i j = if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧ ∀ v : HeightOneSpectrum (𝓞 F), LinearIndependent (Fv F v ⊗[F] E) (ratTup (F := F) (Fv F v) (F0 P)) := by
  first | exact @GlobalTheory.FrameGram.std_frame_gram | exact GlobalTheory.FrameGram.std_frame_gram | (intros; apply GlobalTheory.FrameGram.std_frame_gram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceEqSumLocalTracesAbovePrime
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocalTraceSum

open Filter Topology TensorProduct

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isOpen_lt (γ : ValueGroupWithZero K) : IsOpen {x : K | valuation K x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hγ : γ ≠ 0 := (lt_of_le_of_lt zero_le hx).ne'
  refine (IsValuativeTopology.hasBasis_nhds' x).mem_iff.2 ⟨γ, hγ, fun y hy => ?_⟩
  have := (valuation K).map_add_lt (x := y - x) (y := x) hy hx
  simpa using this

theorem tendsto_pow {x : K} (h : valuation K x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

variable {l : ℕ} [Fact l.Prime] [Algebra ℚ_[l] K]

variable {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

end Local

section Place

variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]

end Place

section Ext

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[l] K] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

end Ext

end GlobalTheory.LocalTraceSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMoveProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMoveProperties
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveFacts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem conj_form {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) : hf L Hm y x = L.cj (hf L Hm x y) := by
  have h' : cT L Hm = Hm := h
  have hH : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h' j) i
  unfold hf
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [map_sum, map_mul, L.cj_cj, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hf_add_left_flag_measures' (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → E) : hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hf_smul_left_flag_measures' (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (x y : Fin n → E) : hf L Hm (c • x) y = c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hf_zero_left_flag_measures (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (y : Fin n → E) : hf L Hm 0 y = 0 := by
  simp [hf]

theorem form_zero_of_span {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (A : Set (Fin n → E)) (hA : ∀ a ∈ A, ∀ b ∈ A, hf L Hm a b = 0) :
    ∀ x ∈ Submodule.span E A, ∀ y ∈ Submodule.span E A, hf L Hm x y = 0 := by
  intro x hx y hy
  have h1 : ∀ a ∈ A, ∀ z ∈ Submodule.span E A, hf L Hm z a = 0 := by
    intro a ha z hz
    induction hz using Submodule.span_induction with
    | mem w hw => exact hA w hw a ha
    | zero => exact hf_zero_left_flag_measures L Hm a
    | add u v _ _ hu hv => rw [hf_add_left_flag_measures', hu, hv, add_zero]
    | smul c u _ hu => rw [hf_smul_left_flag_measures', hu, mul_zero]
  induction hx using Submodule.span_induction with
  | mem w hw => rw [conj_form h y w, h1 w hw y hy, map_zero]
  | zero => exact hf_zero_left_flag_measures L Hm y
  | add u v _ _ hu hv => rw [hf_add_left_flag_measures', hu, hv, add_zero]
  | smul c u _ hu => rw [hf_smul_left_flag_measures', hu, mul_zero]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j := by
  unfold Frames.spanTo
  exact Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem iso_spanTo (g : Fin (r + 1) → S.V) (c : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then c else 0)
    (x : S.V) (hx : x ∈ S.spanTo g r) : S.h x x = 0 := by
  have hH : IsHerm L S.Hm := S.herm.1
  show hf L S.Hm x x = 0
  refine form_zero_of_span hH (g '' {i | (i : ℕ) < r}) ?_ x hx x hx
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have ha' : (a : ℕ) < r := ha
  have hne : a ≠ Fin.last r := fun e => by subst e; simp at ha'
  rw [hg, if_neg (fun hc => hne hc.1)]

theorem mem_span_frame (g : Fin (r + 1) → S.V) (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r)
    (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    x ∈ Submodule.span E (Set.range fun b => n (g b)) := by
  have key : ∀ m : ℕ, m ≤ r → S.spanTo g m ≤ Submodule.span E (Set.range fun b => n (g b)) := by
    intro m
    induction m with
    | zero =>
      intro _
      unfold Frames.spanTo
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact absurd (show (i : ℕ) < 0 from hi) (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm
      have hm' : m < r := by omega
      have h0 : n ∈ S.Nof g := hn
      unfold Frames.Nof at h0
      have hI := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h0).1).2
      have hU : n ∈ unipOn (S.spanTo g (m + 1)) (S.spanTo g m) := Subgroup.mem_iInf.mp hI ⟨m, hm'⟩
      have hU' : (∀ v, n v ∈ S.spanTo g (m + 1) ↔ v ∈ S.spanTo g (m + 1)) ∧
          ∀ v ∈ S.spanTo g (m + 1), n v - v ∈ S.spanTo g m := hU
      have hsub : S.spanTo g (m + 1) ≤ Submodule.span E (Set.range fun b => n (g b)) := by
        unfold Frames.spanTo
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        have hgi : g i ∈ S.spanTo g (m + 1) := Submodule.subset_span ⟨i, hi, rfl⟩
        have h2 := ih hm'.le (hU'.2 (g i) hgi)
        have h3 : n (g i) ∈ Submodule.span E (Set.range fun b => n (g b)) :=
          Submodule.subset_span ⟨i, rfl⟩
        have h4 := Submodule.sub_mem _ h3 h2
        rwa [sub_sub_cancel] at h4
      exact hsub
  exact key (j + 1) (Nat.succ_le_of_lt j.2) hx

theorem parts_of_mem_Mof (hth : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O)
    (g g' : Fin (r + 1) → S.V) (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ ξ ∈ Submodule.span L.O (Set.range g), ∃ ξ' ∈ Submodule.span L.O (Set.range g'),
      algebraMap F E S.th • m = ξ + ξ' := by
  have hinv : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hth, map_one]
  unfold Frames.Mof at hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · refine ⟨algebraMap F E S.th • g b, ?_, 0, zero_mem _, by rw [add_zero]⟩
      exact Submodule.smul_mem _ (⟨algebraMap F E S.th, hO⟩ : L.O) (Submodule.subset_span ⟨b, rfl⟩)
    · refine ⟨-g b, neg_mem (Submodule.subset_span ⟨b, rfl⟩), g' b, Submodule.subset_span ⟨b, rfl⟩, ?_⟩
      show algebraMap F E S.th • algebraMap F E S.th⁻¹ • (g' b - g b) = -g b + g' b
      rw [smul_smul, hinv, one_smul, sub_eq_neg_add]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, a', ha', e⟩ := hu
    obtain ⟨b, hb, b', hb', e'⟩ := hv
    exact ⟨a + b, add_mem ha hb, a' + b', add_mem ha' hb', by rw [smul_add, e, e']; abel⟩
  | smul c u _ hu =>
    obtain ⟨a, ha, a', ha', e⟩ := hu
    refine ⟨c • a, Submodule.smul_mem _ c ha, c • a', Submodule.smul_mem _ c ha', ?_⟩
    show algebraMap F E S.th • ((c : E) • u) = (c : E) • a + (c : E) • a'
    rw [smul_smul, mul_comm (algebraMap F E S.th) (c : E), ← smul_smul, e, smul_add]

theorem move_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → s • x ∈ Λ ∧ L.cj s • x ∈ Λ ∧ s • x' ∈ Λ ∧ L.cj s • x' ∈ Λ ∧ (∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) ∧ S.h x x = 0 ∧ S.h x' x' = 0 ∧ S.h u x = 0 ∧ S.h u x' = 0 ∧ x ∈ S.X ∧ x' ∈ S.X' := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hM
  obtain ⟨hx, hx', hin, -, -, huperp, ⟨c, hcO, hs⟩, -⟩ := hM
  obtain ⟨y, hyΛ, hxy⟩ := id hin
  obtain ⟨⟨-, -, hint⟩, -⟩ := hF
  have hj : (j : ℕ) + 1 ≤ r := Nat.succ_le_of_lt j.2
  have hxX : x ∈ S.X := spanTo_mono S S.f hj hx
  have hx'X : x' ∈ S.X' := spanTo_mono S S.f' hj hx'
  have hH : IsHerm L S.Hm := S.herm.1
  have hxx : S.h x x = 0 := iso_spanTo S S.f _ S.gram x hxX
  have hx'x' : S.h x' x' = 0 := iso_spanTo S S.f' _ S.gram' x' hx'X
  have hperp : ∀ z ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1), hf L S.Hm u z = 0 := huperp
  have hux : S.h u x = 0 := hperp x (Submodule.mem_sup_left hx)
  have hux' : S.h u x' = 0 := hperp x' (Submodule.mem_sup_right hx')
  obtain ⟨c0, hc0, he⟩ := hint x hxX x' hx'X x hxX x' hx'X hin hin
  have he' : hf L S.Hm x x' = algebraMap F E S.th * c0 := he
  have hcross : S.h x' x = algebraMap F E S.th * L.cj c0 := by
    show hf L S.Hm x' x = _
    rw [conj_form hH x x', he', map_mul, AlgEquiv.commutes]
  obtain ⟨-, hW, -, hfrL, hfr'L, hli, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hn, hn', -⟩ := hW
  obtain ⟨-, -, -, -, -, hth, hthO, -⟩ := GlobalTheory.FrameBasic.frames_basic L r k S
  obtain ⟨-, -, -, -, -, -, -, -, hMa, -, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT
  have hthE : algebraMap F E S.th ∈ L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).mpr hthO
  have hinv : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hth, map_one]
  have hsum : x + x' ∈ S.ME :=
    add_mem (Submodule.mem_sup_left (spanTo_mono S S.f (by omega) hx))
      (Submodule.mem_sup_right (spanTo_mono S S.f' (by omega) hx'))
  have hyeq : y = algebraMap F E S.th⁻¹ • (x + x') := by
    rw [hxy, smul_smul, hinv, one_smul]
  have hyME : y ∈ S.ME := by rw [hyeq]; exact Submodule.smul_mem _ _ hsum
  have hysat : y ∈ S.sat Λ := Submodule.mem_inf.mpr ⟨hyΛ, hyME⟩
  obtain ⟨ξ, hξ, ξ', hξ', hsplit⟩ :=
    parts_of_mem_Mof S hth hthE (S.fr d Λ) (S.fr' d Λ) _ (hMa y hysat)
  set P := algebraMap F E ((S.ϖ : F) ^ S.a) with hP
  have hsplit' : P • x + P • x' = ξ + ξ' := by
    rw [← smul_add, hxy, smul_comm]; exact hsplit
  have hxfr : x ∈ Submodule.span E (Set.range (S.fr d Λ)) :=
    mem_span_frame S S.f (S.wit d Λ).1 hn j x hx
  have hx'fr : x' ∈ Submodule.span E (Set.range (S.fr' d Λ)) :=
    mem_span_frame S S.f' (S.wit d Λ).2 hn' j x' hx'
  have hdis := (linearIndependent_sum.mp hli).2.2
  have hw1 : P • x - ξ ∈ Submodule.span E (Set.range (S.fr d Λ)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hxfr)
      (Submodule.span_le_restrictScalars L.O E _ hξ)
  have hw2 : P • x - ξ ∈ Submodule.span E (Set.range (S.fr' d Λ)) := by
    have e : P • x - ξ = ξ' - P • x' := by
      rw [sub_eq_sub_iff_add_eq_add, hsplit', add_comm]
    rw [e]
    exact Submodule.sub_mem _ (Submodule.span_le_restrictScalars L.O E _ hξ')
      (Submodule.smul_mem _ _ hx'fr)
  have hPx : P • x = ξ := sub_eq_zero.mp ((Submodule.disjoint_def.mp hdis) _ hw1 hw2)
  have hPx' : P • x' = ξ' := by rw [hPx] at hsplit'; exact add_left_cancel hsplit'
  have hfrΛ : ∀ b, S.fr d Λ b ∈ Λ := fun b =>
    ((hfrL (r + 1) le_rfl (S.fr d Λ b)).mpr (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hfr'Λ : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    ((hfr'L (r + 1) le_rfl (S.fr' d Λ b)).mpr (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hξΛ : ξ ∈ Λ := Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hfrΛ b) hξ
  have hξ'Λ : ξ' ∈ Λ := Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hfr'Λ b) hξ'
  have key : ∀ z, P • z ∈ Λ → s • z ∈ Λ ∧ L.cj s • z ∈ Λ := by
    intro z hz
    have hc' : L.cj c ∈ L.O := GlobalTheory.UnramOrder.cj_mem L hcO
    have h1 : s • z = (⟨c, hcO⟩ : L.O) • (P • z) := by
      rw [hs]; show (P * c) • z = c • (P • z); rw [smul_smul, mul_comm c P]
    have h2 : L.cj s • z = (⟨L.cj c, hc'⟩ : L.O) • (P • z) := by
      rw [hs, map_mul, AlgEquiv.commutes]; show (P * L.cj c) • z = L.cj c • (P • z)
      rw [smul_smul, mul_comm (L.cj c) P]
    exact ⟨h1 ▸ Λ.smul_mem _ hz, h2 ▸ Λ.smul_mem _ hz⟩
  have kx := key x (hPx ▸ hξΛ)
  have kx' := key x' (hPx' ▸ hξ'Λ)
  exact ⟨kx.1, kx.2, kx'.1, kx'.2, ⟨L.cj c0, GlobalTheory.UnramOrder.cj_mem L hc0, hcross⟩, hxx, hx'x',
    hux, hux', hxX, hx'X⟩

end GlobalTheory.HL.MoveFacts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMovePropertiesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → s • x ∈ Λ ∧ L.cj s • x ∈ Λ ∧ s • x' ∈ Λ ∧ L.cj s • x' ∈ Λ ∧ (∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) ∧ S.h x x = 0 ∧ S.h x' x' = 0 ∧ S.h u x = 0 ∧ S.h u x' = 0 ∧ x ∈ S.X ∧ x' ∈ S.X' := by
  first | exact @GlobalTheory.HL.MoveFacts.move_facts | exact GlobalTheory.HL.MoveFacts.move_facts | (intros; apply GlobalTheory.HL.MoveFacts.move_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameCoordinatesTransportInnerLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameCoordinatesTransportInnerLattices
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordInnerFst

open CoordInnerSnd

theorem _root_.GlobalTheory.HL.CoordInnerFst.transport : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ) (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k)
    (c : _root_.GlobalTheory.HL.Coord P S),
    Function.Injective (c.inn P.A.f) ∧
    (∀ L, P.A.IsInner L ↔ S.IsInner S.f S.es
      (c.inn P.A.f L)) ∧
    (∀ A, S.IsInner S.f S.es A →
      ∃ L, A = c.inn P.A.f L) ∧
    ∀ L, c.lat (P.A.LamStd L) =
      S.stdLat S.f S.es
        (c.inn P.A.f L) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hPID : IsPrincipalIdealRing M.L.O :=
    (_root_.GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.1
  have hcj : ∀ x ∈ M.L.O, M.L.cj x ∈ M.L.O := fun x hx => _root_.GlobalTheory.UnramOrder.cj_mem M.L hx
  have hT : P.A.T ≠ 0 := by
    rw [← c.T_eq]
    exact Units.ne_zero _
  exact ⟨_root_.GlobalTheory.HL.CoordInnerSnd.inn_inj P.A c,
    fun L => _root_.GlobalTheory.HL.CoordInnerSnd.isInner_iff P.A c S.f S.es hcj hPID hT
      c.f_eq c.es_eq L,
    _root_.GlobalTheory.HL.CoordInnerSnd.inn_surj P.A c S.f S.es
      c.f_eq,
    _root_.GlobalTheory.HL.CoordInnerSnd.lat_lamStd P.A c S.f S.es
      c.f_eq c.es_eq⟩

end GlobalTheory.HL.CoordInnerFst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameCoordinatesTransportInnerLatticesStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrameCoordinates_transport_innerLattices : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective (c.inn P.A.f) ∧ (∀ L, P.A.IsInner L ↔ S.IsInner S.f S.es (c.inn P.A.f L)) ∧ (∀ A, S.IsInner S.f S.es A → ∃ L, A = c.inn P.A.f L) ∧ ∀ L, c.lat (P.A.LamStd L) = S.stdLat S.f S.es (c.inn P.A.f L) := by
  first | exact @GlobalTheory.HL.CoordInnerFst.transport | exact GlobalTheory.HL.CoordInnerFst.transport | (intros; apply GlobalTheory.HL.CoordInnerFst.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubMemDifferentIdeal
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory.CMDiscrSq

open Polynomial

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

private lemma sub_mem_differentIdeal_of_eq_star (h : _root_.Formalism.BasicNotions.CMData F E) (θ t : 𝓞 E)
    (ht : algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E θ)) :
    θ - t ∈ differentIdeal (𝓞 F) (𝓞 E) := by
  change (t : E) = star (θ : E) at ht
  have hst : star (t : E) = θ := by rw [ht, star_star]
  by_cases hθ : (θ : E) ∈ (algebraMap F E).range
  · have : t = θ := RingOfIntegers.coe_injective (by
      change (t : E) = θ
      rw [ht]
      exact (h.fixed _).2 hθ)
    rw [this, sub_self]
    exact zero_mem _
  have hF : ∀ x : 𝓞 E, star (x : E) = x → ∃ s : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) s = x := by
    intro x hx
    obtain ⟨a, ha⟩ := (h.fixed _).1 hx
    have hai : IsIntegral ℤ a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).1
        (by rw [IsScalarTower.coe_toAlgHom', ha]; exact x.isIntegral_coe)
    exact ⟨⟨a, hai⟩, RingOfIntegers.coe_injective ha⟩
  obtain ⟨s, hs⟩ := hF (θ + t) (by
    change star ((θ : E) + t) = (θ : E) + t
    rw [star_add, hst, ht, add_comm])
  obtain ⟨n, hn⟩ := hF (θ * t) (by
    change star ((θ : E) * t) = (θ : E) * t
    rw [star_mul, hst, ht])
  set p : (𝓞 F)[X] := X ^ 2 - C s * X + C n with hp_def
  have hpdeg : p.natDegree = 2 := by rw [hp_def]; compute_degree!
  have hpm : p.Monic := by rw [hp_def]; monicity!
  have hroot : aeval θ p = 0 := by
    simp only [hp_def, map_add (f := _), map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hn]
    ring
  have hint : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral θ
  have hdvd := minpoly.isIntegrallyClosed_dvd hint hroot
  have hmdeg : (minpoly (𝓞 F) θ).natDegree = 2 := by
    have hle : (minpoly (𝓞 F) θ).natDegree ≤ 2 := hpdeg ▸ natDegree_le_of_dvd hdvd hpm.ne_zero
    have hne1 : (minpoly (𝓞 F) θ).natDegree ≠ 1 := by
      intro h1
      obtain ⟨s', hs'⟩ := minpoly.natDegree_eq_one_iff.1 h1
      exact hθ ⟨(s' : F), by rw [← hs']; rfl⟩
    have hpos := minpoly.natDegree_pos hint
    omega
  have hmin : minpoly (𝓞 F) θ = p :=
    (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm hdvd (by omega)).symm
  have hint' : IsIntegral (𝓞 F) (θ : E) := hint.algebraMap
  have hFdeg : (minpoly F (θ : E)).natDegree = 2 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F hint',
      minpoly.algebraMap_eq RingOfIntegers.coe_injective, natDegree_map_eq_of_injective
        (IsFractionRing.injective (𝓞 F) F), hmdeg]
  have htop : IntermediateField.adjoin F {(θ : E)} = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top (by
    rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank
      (Algebra.IsIntegral.isIntegral _), hFdeg, h.deg2])
  have hgen : Algebra.adjoin F {algebraMap (𝓞 E) E θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _)]
    change (IntermediateField.adjoin F {(θ : E)}).toSubalgebra = ⊤
    rw [htop, IntermediateField.top_toSubalgebra]
  have hd := aeval_derivative_mem_differentIdeal (𝓞 F) F E θ hgen
  rw [hmin] at hd
  convert hd using 1
  simp [hp_def, hs]
  ring

theorem _root_.GlobalTheory.CMDiscrSq.differentIdeal_eq_top (h : _root_.Formalism.BasicNotions.CMData F E) : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := h.cmUnram.2.2 P hP
  exact hθt (hle (sub_mem_differentIdeal_of_eq_star h θ t ht))

end GlobalTheory.CMDiscrSq

theorem _root_.GlobalTheory.cm_discr_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [StarRing E] [Algebra F E], _root_.Formalism.BasicNotions.CMData F E → |discr E| = discr F ^ 2 ∧
      Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F))) =
        (discr F).natAbs ^ 2 := by
  intro F E _ _ _ _ _ _ h
  have hd := _root_.GlobalTheory.CMDiscrSq.differentIdeal_eq_top h
  have hE := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hd, Ideal.absNorm_top, one_mul, h.deg2] at hE
  refine ⟨?_, ?_⟩
  · rw [Int.abs_eq_natAbs, hE]
    push_cast
    exact sq_abs _
  · have hmul := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)
    rw [hd, Ideal.top_mul] at hmul
    rw [← hmul, absNorm_differentIdeal E (𝓞 E), hE]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWtEqMulNu
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordDatum

theorem exists_invVol_eq_mul {G : Type} [Group G] (K' K0 : Subgroup G) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ K : Subgroup G, K0.relIndex K ≠ 0 → K.relIndex K0 ≠ 0 →
      invVol K' K = κ * invVol K0 K := by
  by_cases hc : K'.relIndex K0 ≠ 0 ∧ K0.relIndex K' ≠ 0
  · refine ⟨invVol K' K0, ?_, fun K hK hK' => ?_⟩
    · unfold invVol
      positivity
    · exact (invVol_mul_pos_le_conj K' K0 K hc.1 hc.2
        (Subgroup.relIndex_ne_zero_trans hc.1 hK)
        (Subgroup.relIndex_ne_zero_trans hK' hc.2)).1
  · refine ⟨0, le_rfl, fun K hK hK' => ?_⟩
    rw [zero_mul]
    unfold invVol
    by_cases h1 : K.relIndex K' = 0
    · simp [h1]
    · have h2 : K'.relIndex K = 0 := by
        by_contra h2
        exact hc ⟨Subgroup.relIndex_ne_zero_trans h2 hK', Subgroup.relIndex_ne_zero_trans hK h1⟩
      simp [h2]

theorem exists_wt_eq_mul_nu : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ d0 : LocNG.Datum P, ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → LocNG.Datum.wt d0 d = κ * S.nu (c.dat d) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c d0
  have := hM.loc
  have := hM.char0
  obtain ⟨κ, hκ, hK⟩ :=
    exists_invVol_eq_mul (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0)) S.complementReferenceCompactSubgroup
  refine ⟨κ, hκ, fun d Λ hT => ?_⟩
  obtain ⟨h1, h2⟩ := (Frames.stab_commensurable_invVol_smul M.L r k S).2 (c.dat d) Λ hT
  rw [(transport M hM H r k P S c).2.2.2.2 d0 d]
  exact hK _ h1 h2

end GlobalTheory.HL.CoordDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfStabilizerSmulEqConj
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem inf_stabilizer_smul_eq_conj {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G)
    {h : G} (hh : h ∈ H) (x : X) :
    H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) h1) hh, ?_⟩
    rw [mul_smul, mul_smul, h2, inv_smul_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := H.mul_mem (H.mul_mem hh h1) (H.inv_mem hh)
      simpa [mul_assoc] using this
    · rw [mul_smul, mul_smul, inv_smul_eq_iff] at h2
      exact h2

theorem invVol_conj_of_invVol_conj {G : Type} [Group G] (K A B : Subgroup G) (g : G)
    (hA : K.relIndex A ≠ 0) (hA' : A.relIndex K ≠ 0) (hB : K.relIndex B ≠ 0) (hB' : B.relIndex K ≠ 0)
    (h : invVol K (MulAut.conj g • A) = invVol K A) :
    invVol K (MulAut.conj g • B) = invVol K B := by
  have e : ∀ A B : Subgroup G,
      (MulAut.conj g • A).relIndex (MulAut.conj g • B) = A.relIndex B := fun A B =>
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A B
      (MulAut.conj g).injective
  have hpos : 0 < invVol K (MulAut.conj g • A) := by
    rw [h]; exact (invVol_mul_pos_le_conj K A A hA hA' hA hA').2.1
  have hAB : A.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero_trans hA' hB
  have hBA : B.relIndex A ≠ 0 := Subgroup.relIndex_ne_zero_trans hB' hA
  have c1 : K.relIndex (MulAut.conj g • A) ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c2 : (MulAut.conj g • A).relIndex K ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c3 : K.relIndex (MulAut.conj g • B) ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans c1 (by rw [e]; exact hAB)
  have c4 : (MulAut.conj g • B).relIndex K ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans (by rw [e]; exact hBA) c2
  rw [(invVol_mul_pos_le_conj K _ _ c1 c2 c3 c4).1, (invVol_mul_pos_le_conj K A B hA hA' hB hB').1, h]
  congr 1
  rw [invVol, invVol, e, e]

theorem Frames.nu_pos_and_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 < S.nu d ∧ ∀ h ∈ S.H0, S.nu (h • d) = S.nu d := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨hv, hd⟩ := GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement L r k S
  obtain ⟨d1, d2⟩ := hd d Λ hT
  have hSD := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1
  obtain ⟨l1, l2, l3⟩ := hv Λ hSD.1
  refine ⟨(invVol_mul_pos_le_conj _ _ _ d1 d2 d1 d2).2.1, fun h hh => ?_⟩
  have := l3 h hh
  rw [inf_stabilizer_smul_eq_conj _ hh] at this
  unfold Frames.nu
  rw [inf_stabilizer_smul_eq_conj _ hh]
  exact invVol_conj_of_invVol_conj _ _ _ h l1 l2 d1 d2 this

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexSpanLatticeMatrixDetNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexSpanLatticeMatrixDetNorm
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameIndex

theorem relIndex_span_matrix : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {n m : ℕ} (b : Fin m → Fin n → E), LinearIndependent E b → ∀ (A : Matrix (Fin m) (Fin m) E) (c : F), c ≠ 0 → A.det * L.cj A.det = algebraMap F E c → ∀ Q Q' : Submodule L.O (Fin n → E), Q = Submodule.span L.O (Set.range b) → Q' = Submodule.span L.O (Set.range fun j => ∑ i, A i j • b i) → Q'.toAddSubgroup.relIndex Q.toAddSubgroup ≠ 0 ∧ Q.toAddSubgroup.relIndex Q'.toAddSubgroup ≠ 0 ∧ (Q'.toAddSubgroup.relIndex Q.toAddSubgroup : ℝ) = (resQ ϖ : ℝ) ^ (vE L ϖ (algebraMap F E c)) * (Q.toAddSubgroup.relIndex Q'.toAddSubgroup : ℝ) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n m b hb A c hc0 hA Q Q' hQ hQ'
  obtain ⟨c2, hc, hN⟩ := TupleJac.exists_int_basis L
  have := L.free
  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 c hc0
  have hAu : IsUnit A.det := by
    have h := (IsUnit.mk0 c hc0).map (algebraMap F E)
    rw [← hA] at h
    exact isUnit_of_mul_isUnit_left h
  have hdet : IsUnit (LinearMap.det (Matrix.toLin' A)) := by
    rw [LinearMap.det_toLin']; exact hAu
  set φ := LinearMap.equivOfIsUnitDet hdet with hφdef
  have hφ : φ.toLinearMap = Matrix.toLin' A := LinearMap.coe_equivOfIsUnitDet hdet
  have hφx : ∀ x, φ x = A.mulVec x := fun x => LinearMap.congr_fun hφ x
  let W0 : AddSubgroup (Fin m → E) := AddSubgroup.pi Set.univ fun _ => L.O.toAddSubgroup
  have hW0 : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ L.O := fun x => by
    simp only [W0, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff, Subring.mem_toAddSubgroup]
  have h := LatDet.relVol_map ϖ hϖ (c2.smulTower (Pi.basisFun E (Fin m))) (φ.restrictScalars F)
    (vE L ϖ (algebraMap F E c)) u
    (by
      apply GlobalTheory.UnramOrder.algebraMap_inj L
      rw [← hu, ← hA, ← hN, ← LinearMap.det_toLin', ← hφ, ← LinearMap.det_restrictScalars]
      rfl) W0 (by
      intro x
      simp only [hW0, hc, Module.Basis.smulTower_repr, Pi.basisFun_repr]
      exact ⟨fun h i => h _ _, fun h j i => h (i, j)⟩)
  let e : (Fin m → E) →+ (Fin n → E) := (Fintype.linearCombination E b).toAddMonoidHom
  have he : ∀ x, e x = ∑ i, x i • b i := fun x => Fintype.linearCombination_apply E b x
  have hei : Function.Injective e := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact funext (Fintype.linearIndependent_iff.1 hb x ((he x).symm.trans hx))
  have h1 : Q.toAddSubgroup = W0.map e := by
    ext w
    rw [hQ, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
      AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨fun i => x i, (hW0 _).2 fun i => (x i).2, he _⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨fun i => ⟨x i, (hW0 _).1 hx i⟩, (he _).symm⟩
  have hsum : ∀ x : Fin m → E, e (φ x) = ∑ j, x j • ∑ i, A i j • b i := by
    intro x
    rw [he, hφx]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h2 : Q'.toAddSubgroup =
      (W0.map (φ.restrictScalars F).toAddEquiv.toAddMonoidHom).map e := by
    ext w
    rw [hQ', Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
      AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨fun i => x i, (hW0 _).2 fun i => (x i).2, rfl⟩, hsum _⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨fun i => ⟨x i, (hW0 _).1 hx i⟩, (hsum _).symm⟩
  rw [h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _ hei,
    AddSubgroup.relIndex_map_map_of_injective _ _ hei]
  obtain ⟨n1, n2, h3⟩ := h
  refine ⟨n1, n2, ?_⟩
  unfold relVol at h3
  have hq : (resQ ϖ : ℝ) ≠ 0 := by exact_mod_cast LatDet.resQ_ne_zero hϖ
  rw [div_eq_iff (by exact_mod_cast n1)] at h3
  rw [h3, ← mul_assoc, ← zpow_add₀ hq, add_neg_cancel, zpow_zero, one_mul]

end GlobalTheory.HL.FrameIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexSpanLatticeMatrixDetNormStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_span_lattice_matrix_det_norm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {n m : ℕ} (b : Fin m → Fin n → E), LinearIndependent E b → ∀ (A : Matrix (Fin m) (Fin m) E) (c : F), c ≠ 0 → A.det * L.cj A.det = algebraMap F E c → ∀ Q Q' : Submodule L.O (Fin n → E), Q = Submodule.span L.O (Set.range b) → Q' = Submodule.span L.O (Set.range fun j => ∑ i, A i j • b i) → Q'.toAddSubgroup.relIndex Q.toAddSubgroup ≠ 0 ∧ Q.toAddSubgroup.relIndex Q'.toAddSubgroup ≠ 0 ∧ (Q'.toAddSubgroup.relIndex Q.toAddSubgroup : ℝ) = (resQ ϖ : ℝ) ^ (vE L ϖ (algebraMap F E c)) * (Q.toAddSubgroup.relIndex Q'.toAddSubgroup : ℝ) := by
  first | exact @GlobalTheory.HL.FrameIndex.relIndex_span_matrix | exact GlobalTheory.HL.FrameIndex.relIndex_span_matrix | (intros; apply GlobalTheory.HL.FrameIndex.relIndex_span_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternUnitriangularStrongApproximation
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternUnitriangularStrongApproximation
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PatternApprox

theorem exists_clear {Fp Ep : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp]
    [IsNonarchimedeanLocalField Fp] [CommRing Ep] [Algebra Fp Ep] [Module.Finite Fp Ep]
    (O : Subring Ep) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[Fp] x) {ι : Type} [Fintype ι] (x : ι → Ep) :
    ∃ a : Fp, a ≠ 0 ∧ ∀ i, algebraMap Fp Ep a * x i ∈ O := by
  have hfr : IsFractionRing 𝒪[Fp] Fp := (Valuation.integer.integers (valuation Fp)).isFractionRing
  have halg : ∀ i, IsAlgebraic 𝒪[Fp] (x i) := fun i =>
    (IsFractionRing.isAlgebraic_iff 𝒪[Fp] Fp Ep).mpr (Algebra.IsIntegral.isIntegral (R := Fp) (x i)).isAlgebraic
  choose y hy0 hyi using fun i => (halg i).exists_integral_multiple
  have hym : ∀ k, algebraMap Fp Ep (y k : Fp) ∈ O := fun k => by
    rw [hO, show algebraMap Fp Ep (y k : Fp) = algebraMap 𝒪[Fp] Ep (y k) from
      (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y k)).symm]
    exact isIntegral_algebraMap
  refine ⟨∏ k, (y k : Fp), ?_, fun i => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro k _ h
    exact hy0 k (Subtype.ext (by simpa using h))
  · have h1 : algebraMap Fp Ep (y i : Fp) * x i ∈ O := by
      rw [hO, show algebraMap Fp Ep (y i : Fp) = algebraMap 𝒪[Fp] Ep (y i) from
        (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y i)).symm, ← Algebra.smul_def]
      exact hyi i
    rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
    exact O.mul_mem (O.prod_mem fun k _ => hym k) h1

variable {R : Type} [CommRing R]

theorem det_eq_one {m : ℕ} (I : Fin m → Fin m → Prop) (hI : ∀ i j, I i j → i < j)
    (s : Matrix (Fin m) (Fin m) R) (hs : ∀ i j, ¬ I i j → s i j = if i = j then 1 else 0) : s.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [hs i i (fun h => lt_irrefl i (hI i i h))]
    simp
  · intro i j hji
    rw [hs i j (fun h => lt_asymm (hI i j h) hji)]
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hji
    simp [hne]

theorem adjugate_mem {m : ℕ} (O : Subring R) (s : Matrix (Fin m) (Fin m) R) (h : ∀ i j, s i j ∈ O) :
    ∀ i j, s.adjugate i j ∈ O := by
  let S : Matrix (Fin m) (Fin m) O := fun i j => ⟨s i j, h i j⟩
  have hS : O.subtype.mapMatrix S = s := by ext i j; rfl
  intro i j
  rw [← hS, ← RingHom.map_adjugate]
  exact (S.adjugate i j).2

end GlobalTheory.HL.PatternApprox

open GlobalTheory.HL.PatternApprox in
theorem GlobalTheory.HL.pattern_strong_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (m : ℕ) (I : Fin m → Fin m → Prop), (∀ i j, I i j → i < j) → (∀ i j l, I i j → I j l → I i l) → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ s : ∀ p, Matrix (Fin m) (Fin m) (A.loc p).Ep, (∀ p i j, ¬ I i j → s p i j = if i = j then 1 else 0) → {p | ¬ IsIntM (A.L p) (s p)}.Finite → ∃ t : Matrix (Fin m) (Fin m) E, (∀ i j, ¬ I i j → t i j = if i = j then 1 else 0) ∧ ∀ p i j, ∃ o ∈ (A.L p).O, ((s p)⁻¹ * t.map (A.loc p).ιE - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  intro F E _ _ _ _ _ sig A m I hlt _htr c hc s hs hsint
  have hinv : ∀ p, (s p)⁻¹ = (s p).adjugate := fun p => by
    rw [Matrix.inv_def, det_eq_one I hlt (s p) (hs p), Ring.inverse_one, one_smul]
  have hcl : ∀ p, ∃ a : ((A.loc p).Fp)ˣ, (IsIntM (A.L p) (s p) → a = 1) ∧
      ∀ i j, algebraMap (A.loc p).Fp (A.loc p).Ep (a : (A.loc p).Fp) * (s p)⁻¹ i j ∈ (A.L p).O := by
    intro p
    haveI := (A.loc p).lf
    haveI : Module.Free (A.loc p).Fp (A.loc p).Ep := (A.loc p).free
    haveI : Module.Finite (A.loc p).Fp (A.loc p).Ep := Module.finite_of_finrank_eq_succ (A.loc p).rank
    by_cases h : IsIntM (A.L p) (s p)
    · refine ⟨1, fun _ => rfl, fun i j => ?_⟩
      rw [Units.val_one, map_one, one_mul, hinv p]
      exact adjugate_mem (A.L p).O (s p) h i j
    · obtain ⟨a, ha0, ha⟩ := exists_clear (A.L p).O (A.L p).O_def
        (fun ij : Fin m × Fin m => (s p)⁻¹ ij.1 ij.2)
      exact ⟨Units.mk0 a ha0, fun h' => absurd h' h, fun i j => ha (i, j)⟩
  choose c' hc'1 hc'2 using hcl
  let d : ∀ p, ((A.loc p).Fp)ˣ := fun p => c p * c' p
  have hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite := by
    apply (hc.union hsint).subset
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    obtain ⟨⟨u, hu⟩, hint⟩ := hno
    exact hp ⟨u, by simp [d, hc'1 p hint, hu]⟩
  have hap := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A d hd).2.1
  have hx : ∀ i j, ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O,
      (A.loc p).ιE x - s p i j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o :=
    fun i j => hap (fun p => s p i j) (hsint.subset fun p hp hi => hp (hi i j))
  choose x hx using hx
  refine ⟨fun i j => if I i j then x i j else if i = j then 1 else 0, fun i j h => by simp [h], fun p i j => ?_⟩
  set t : Matrix (Fin m) (Fin m) E := fun i j => if I i j then x i j else if i = j then 1 else 0 with ht
  have hD : ∀ k l, ∃ o ∈ (A.L p).O, (t.map (A.loc p).ιE - s p) k l =
      algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o := by
    intro k l
    by_cases hkl : I k l
    · obtain ⟨o, ho, he⟩ := hx k l p
      refine ⟨o, ho, ?_⟩
      rw [← he]
      show (A.loc p).ιE (t k l) - s p k l = (A.loc p).ιE (x k l) - s p k l
      rw [ht]
      simp only [hkl, if_true]
    · refine ⟨0, (A.L p).O.zero_mem, ?_⟩
      rw [Matrix.sub_apply, Matrix.map_apply, hs p k l hkl, mul_zero]
      simp only [ht, hkl, if_false]
      split_ifs <;> simp
  choose o ho hoeq using hD
  have hunit : (s p)⁻¹ * s p = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [det_eq_one I hlt (s p) (hs p)]; exact isUnit_one)
  have heq : (s p)⁻¹ * t.map (A.loc p).ιE - 1 = (s p)⁻¹ * (t.map (A.loc p).ιE - s p) := by
    rw [Matrix.mul_sub, hunit]
  refine ⟨∑ k, (algebraMap (A.loc p).Fp (A.loc p).Ep (c' p : (A.loc p).Fp) * (s p)⁻¹ i k) * o k j,
    (A.L p).O.sum_mem fun k _ => (A.L p).O.mul_mem (hc'2 p i k) (ho k j), ?_⟩
  rw [heq, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hoeq k j]
  simp only [d, Units.val_mul, map_mul]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternUnitriangularStrongApproximationStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pattern_unitriangular_strong_approximation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (m : ℕ) (I : Fin m → Fin m → Prop), (∀ i j, I i j → i < j) → (∀ i j l, I i j → I j l → I i l) → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ s : ∀ p, Matrix (Fin m) (Fin m) (A.loc p).Ep, (∀ p i j, ¬ I i j → s p i j = if i = j then 1 else 0) → {p | ¬ IsIntM (A.L p) (s p)}.Finite → ∃ t : Matrix (Fin m) (Fin m) E, (∀ i j, ¬ I i j → t i j = if i = j then 1 else 0) ∧ ∀ p i j, ∃ o ∈ (A.L p).O, ((s p)⁻¹ * t.map (A.loc p).ιE - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  first | exact @GlobalTheory.HL.pattern_strong_approx | exact GlobalTheory.HL.pattern_strong_approx | (intros; apply GlobalTheory.HL.pattern_strong_approx <;> assumption)
end
end
