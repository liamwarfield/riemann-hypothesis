module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasis
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import ReciprocityTheory.AnalyticForms.LeviForms.PullDominateStatement
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivialization
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivialization
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_periodPolydisc_frame : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ), ∃ (Q : PeriodPolydisc n a g) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) ∧ (A 0).det ≠ 0 ∧ ∀ w ∈ logCover L.a_le, A (expCover a w) * L.H (expCover a w) * (A (expCover a w))ᴴ = (((Q.τ w).map Complex.im)⁻¹).map Complex.ofReal := by
  intro n a g Λ _ L
  obtain ⟨bas, Q, A, T0, hsym, hAd, hdet, -, -, hAP, hQP⟩ := exists_markedPeriods_frame n a g Λ L
  refine ⟨Q, A, hAd, hdet, fun w hw => ?_⟩
  let Am : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i => L.P w (bas (.inl i))
  let Bm : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i => L.P w (bas (.inr i))
  have hAm : Am = A (expCover a w) := by
    ext i k
    exact hAP w hw i k
  obtain ⟨h1, -, -, h4⟩ := siegel_of_riemann g Am Bm (L.H (expCover a w)) (L.herm w hw)
    (L.pos w hw) (fun i j => ⟨(L.im w hw (bas (.inl i)) (bas (.inl j))).trans (by simp [(hsym i j).1]),
      (L.im w hw (bas (.inr i)) (bas (.inr j))).trans (by simp [(hsym i j).2.1]),
      (L.im w hw (bas (.inl i)) (bas (.inr j))).trans (by
        rw [(hsym i j).2.2]; split_ifs <;> simp)⟩)
  have hB : Bm = Q.τ w * Am := by
    ext j k
    have h := congrFun (hQP w hw j) k
    rw [Finset.sum_apply] at h
    simpa [Am, Bm, Matrix.mul_apply] using h
  have hτ : Bm * Am⁻¹ = Q.τ w := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.mul_one]
  rw [← hAm, h4, hτ]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivializationStatement
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_matrix_local_trivialization : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ), ∃ (Q : PeriodPolydisc n a g) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) ∧ (A 0).det ≠ 0 ∧ ∀ w ∈ logCover L.a_le, A (expCover a w) * L.H (expCover a w) * (A (expCover a w))ᴴ = (((Q.τ w).map Complex.im)⁻¹).map Complex.ofReal := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousHermitianMatrixFamily
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousHermitianMatrixFamily
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.HmCont

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {g : ℕ}

def cvec (z : Fin g → ℂ) : Fin g ⊕ Fin g → ℝ :=
  Sum.elim (fun k => (z k).re) (fun k => (z k).im)

def realBlock (H : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  Matrix.fromBlocks (H.map Complex.im) (-(H.map Complex.re)) (H.map Complex.re) (H.map Complex.im)

theorem cvec_dot_realBlock (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    cvec z ⬝ᵥ realBlock H *ᵥ cvec w = (z ⬝ᵥ H *ᵥ star w).im := by
  simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec, GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply, Matrix.neg_apply,
    Complex.im_sum, Complex.re_sum, Complex.mul_im, Complex.mul_re, Pi.star_apply, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_det_ne_zero {Λ ι : Type} [AddCommGroup Λ] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ Λ) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (inj : Function.Injective form) :
    (Matrix.of fun i j => form (b i) (b j)).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hform : form (∑ i, c i • b i) = 0 := by
    refine b.ext fun j => ?_
    have hj := congrFun hc j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at hj
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply]
    exact hj
  have hsum : ∑ i, c i • b i = 0 := inj (by rw [hform, map_zero])
  exact hc0 (funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hsum))

theorem continuous_of_congruence {ι X : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace X]
    (T G : X → Matrix ι ι ℝ) (W : Matrix ι ι ℝ) (hT : Continuous T) (hW : W.det ≠ 0)
    (h : ∀ x, (T x)ᵀ * G x * T x = W) : Continuous G := by
  have hdet : ∀ x, (T x).det ≠ 0 := by
    intro x h0
    apply hW
    rw [← h x, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hG : ∀ x, G x = ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) := by
    intro x
    have h1 : (T x).adjugateᵀ * ((T x)ᵀ * G x * T x) * (T x).adjugate = (T x).det ^ 2 • G x := by
      calc (T x).adjugateᵀ * ((T x)ᵀ * G x * T x) * (T x).adjugate
          = (T x * (T x).adjugate)ᵀ * G x * (T x * (T x).adjugate) := by
            rw [Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = (T x).det ^ 2 • G x := by
            simp only [Matrix.mul_adjugate, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, sq]
    rw [h x] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (hdet x)), one_smul]
  have hcont : Continuous fun x => ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) := by
    have hd : Continuous fun x => (T x).det := hT.matrix_det
    have ha : Continuous fun x => (T x).adjugate := hT.matrix_adjugate
    exact ((hd.pow 2).inv₀ fun x => pow_ne_zero 2 (hdet x)).smul
      ((ha.matrix_transpose.matrix_mul continuous_const).matrix_mul ha)
  rw [show G = fun x => ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) from funext hG]
  exact hcont

theorem continuous_Hm (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ)
    (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (hform : ∀ x, (R x).form = form)
    (hP : ∀ v, Continuous fun x => (R x).P v) : Continuous fun x => (R x).Hm := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact continuous_of_const fun x => isEmptyElim x
  have hlat : ∀ S : GlobalTheory.CompanionTheory.Ar.Cusp.RiemLat E g Λ,
      Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧ Module.finrank ℤ Λ = 2 * g ∧ Function.Bijective S.form := by
    intro S
    obtain ⟨h1, h2, h3, _, _, h4, _, _, _, _, _, _, _, _⟩ := S
    exact ⟨h1, h2, h3, h4⟩
  have hIm : ∀ (S : GlobalTheory.CompanionTheory.Ar.Cusp.RiemLat E g Λ) (u v : Λ),
      ((S.P u) ⬝ᵥ S.Hm *ᵥ star (S.P v)).im = S.form u v := by
    intro S u v
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ := S
    exact h u v
  obtain ⟨hfree, hfin, hrank, hbij⟩ := hlat (R x₀)
  have hinj : Function.Injective form := by
    rw [← hform x₀]
    exact hbij.1
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin g ⊕ Fin g) ℤ Λ) :=
    ⟨(Module.finBasisOfFinrankEq ℤ Λ (hrank.trans (two_mul g))).reindex finSumFinEquiv.symm⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ,
      W = Matrix.of fun i j => ((form (b i) (b j) : ℤ) : ℝ) := ⟨_, rfl⟩
  have hW : W.det ≠ 0 := by
    have h0 := GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.gram_det_ne_zero b form hinj
    have hmap : W = (Int.castRingHom ℝ).mapMatrix (Matrix.of fun i j => form (b i) (b j)) := by
      ext i j
      rw [hWdef, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply]
      simp
    rw [hmap, ← RingHom.map_det]
    simpa using h0
  have hT : Continuous fun x =>
      (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) := by
    refine continuous_matrix fun a i => ?_
    rcases a with k | k
    · exact Complex.continuous_re.comp ((continuous_apply k).comp (hP (b i)))
    · exact Complex.continuous_im.comp ((continuous_apply k).comp (hP (b i)))
  have hTGT : ∀ x,
      (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)ᵀ *
        GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm *
        (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) = W := by
    intro x
    ext i j
    rw [Matrix.mul_assoc]
    calc _ = GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) ⬝ᵥ
            GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm *ᵥ GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b j)) := rfl
      _ = (((R x).P (b i)) ⬝ᵥ (R x).Hm *ᵥ star ((R x).P (b j))).im :=
          GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec_dot_realBlock _ _ _
      _ = (R x).form (b i) (b j) := hIm (R x) (b i) (b j)
      _ = W i j := by rw [hform x, hWdef, Matrix.of_apply]
  have hG : Continuous fun x => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm :=
    GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_of_congruence
      (fun x => (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a :
        Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ))
      (fun x => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm) W hT hW hTGT
  refine continuous_matrix fun k l => ?_
  have hre : Continuous fun x => ((R x).Hm k l).re := by
    have h := hG.matrix_elem (Sum.inr k) (Sum.inl l)
    simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, Matrix.fromBlocks_apply₂₁, Matrix.map_apply] at h
    exact h
  have him : Continuous fun x => ((R x).Hm k l).im := by
    have h := hG.matrix_elem (Sum.inl k) (Sum.inl l)
    simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, Matrix.fromBlocks_apply₁₁, Matrix.map_apply] at h
    exact h
  have heq : (fun x => (R x).Hm k l) =
      fun x => (((R x).Hm k l).re : ℂ) + (((R x).Hm k l).im : ℂ) * Complex.I :=
    funext fun x => (Complex.re_add_im _).symm
  show Continuous fun x => (R x).Hm k l
  rw [heq]
  exact (Complex.continuous_ofReal.comp hre).add ((Complex.continuous_ofReal.comp him).mul continuous_const)

end GlobalTheory.CompanionTheory.Ar.Cusp.HmCont
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousHermitianMatrixFamilyStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_hermitian_matrix_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ), (∀ x, (R x).form = form) → (∀ v, Continuous fun x => (R x).P v) → Continuous fun x => (R x).Hm := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm | exact GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFamilyC2PullbackOfSection
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem isOpen_compl_bdry {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : s x x ≠ 0 := hx
  obtain ⟨j, hj⟩ := A.cover x
  have hleft : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ L.U x
      rw [hleft]; exact L.mem_U x⟩
  have hg : ContinuousAt (s x ∘ (A.chart j).symm) (A.chart j x) :=
    (hs.1 x j _ hmem).continuousAt
  have hne : (s x ∘ (A.chart j).symm) (A.chart j x) ≠ 0 := by
    simpa [Function.comp_apply, hleft] using hx0
  have h1 : ∀ᶠ y in 𝓝 x, (s x ∘ (A.chart j).symm) (A.chart j y) ≠ 0 :=
    ((A.chart j).continuousAt hj).eventually (hg.eventually_ne hne)
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ (A.chart j).source := (A.chart j).open_source.mem_nhds hj
  have h3 : ∀ᶠ y in 𝓝 x, y ∈ L.U x := (L.isOpen_U x).mem_nhds (L.mem_U x)
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  have hsy : s x y ≠ 0 := by
    simpa [Function.comp_apply, (A.chart j).left_inv hy2] using hy1
  intro hb
  have hb0 : s y y = 0 := hb
  have heq := hs.2 x y y ⟨hy3, L.mem_U y⟩
  rw [hb0, norm_zero, zero_mul] at heq
  exact (mul_ne_zero (norm_ne_zero_iff.2 hsy) (Real.exp_ne_zero _)) heq

theorem regular_family_C2_pullback_of_open {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h)
    (s : X → X → ℂ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (hO : IsOpen (bdry s)ᶜ)
    (hph : A.SmoothOn (bdry s)ᶜ ph)
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), A.Smooth (phT t))
    (hC : IsRegFamilyC2 A s ph phT) :
    IsRegFamilyC2 A' (fun x y => s (h x) (h y)) (ph ∘ h) (fun t => phT t ∘ h) := by
  have key := GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.proof A' A h hh (bdry s)ᶜ hO phT ph
    (ph ∘ h) hph (fun _ _ => rfl) hT (fun k K hK hKs => hC k K hKs hK)
  intro j K hKs hK
  exact key j K hK hKs

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsExtendLinearIndependentOfSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsExtendLinearIndependentOfSpan
namespace GlobalTheory.CompanionTheory.Ar.Exchange

theorem exists_completion_by_members (g m r : ℕ) (w : Fin r → Fin g → ℂ) (b : Fin m → Fin g → ℂ)
    (hw : LinearIndependent ℂ w) (hb : LinearIndependent ℂ b)
    (hwb : ∀ a, w a ∈ Submodule.span ℂ (Set.range b)) :
    ∃ (k : ℕ) (J : Fin k → Fin m), r + k = m ∧
      LinearIndependent ℂ (Fin.append w (fun j => b (J j))) := by
  classical
  let v : Fin r ⊕ Fin m → (Fin g → ℂ) := Sum.elim w b
  have hs : LinearIndepOn ℂ v (Set.range Sum.inl) := by
    rw [linearIndepOn_range_iff Sum.inl_injective]
    exact hw
  obtain ⟨B, -, hsB, hspan, hB⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  let S : Finset (Fin m) := Finset.univ.filter fun j => Sum.inr j ∈ B
  let J : Fin S.card → Fin m := S.orderEmbOfFin rfl
  let φ : Fin (r + S.card) → Fin r ⊕ Fin m := Fin.append Sum.inl (Sum.inr ∘ J)
  have hφ : Function.Injective φ :=
    Fin.append_injective_iff.mpr ⟨Sum.inl_injective,
      Sum.inr_injective.comp (S.orderEmbOfFin rfl).injective, fun _ _ => Sum.inl_ne_inr⟩
  have hJS : ∀ l, J l ∈ S := fun l => S.orderEmbOfFin_mem rfl l
  have hφB : Set.range φ ⊆ B := by
    rintro _ ⟨l, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun l => ?_) l
    · simp only [φ, Fin.append_left]
      exact hsB ⟨i, rfl⟩
    · simp only [φ, Fin.append_right, Function.comp_apply]
      have := hJS l
      simpa [S] using this
  have hBφ : B ⊆ Set.range φ := by
    rintro (i | j) hx
    · exact ⟨Fin.castAdd _ i, by simp [φ]⟩
    · have hj : j ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        simp [S, hx]
      obtain ⟨l, hl⟩ := hj
      exact ⟨Fin.natAdd _ l, by simp [φ, J, hl]⟩
  have hu : LinearIndependent ℂ (v ∘ φ) := by
    rw [← linearIndepOn_range_iff hφ]
    exact hB.mono hφB
  have hle1 : Submodule.span ℂ (Set.range (v ∘ φ)) ≤ Submodule.span ℂ (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    show v (φ l) ∈ _
    generalize φ l = x
    rcases x with i | j
    · exact hwb i
    · exact Submodule.subset_span ⟨j, rfl⟩
  have hle2 : Submodule.span ℂ (Set.range b) ≤ Submodule.span ℂ (Set.range (v ∘ φ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : b j ∈ Submodule.span ℂ (v '' B) := hspan ⟨Sum.inr j, Set.mem_univ _, rfl⟩
    have h2 : v '' B ⊆ Set.range (v ∘ φ) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨l, rfl⟩ := hBφ hx
      exact ⟨l, rfl⟩
    exact Submodule.span_mono h2 h1
  have hueq : (Fin.append w fun j => b (J j)) = v ∘ φ := by
    funext l
    refine Fin.addCases (fun i => ?_) (fun l => ?_) l
    · simp [φ, v]
    · simp [φ, v]
  refine ⟨S.card, J, ?_, ?_⟩
  · have e1 := finrank_span_eq_card hu
    have e2 := finrank_span_eq_card hb
    rw [le_antisymm hle1 hle2, e2] at e1
    simpa using e1.symm
  · rw [hueq]
    exact hu

end GlobalTheory.CompanionTheory.Ar.Exchange
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsExtendLinearIndependentOfSpanStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extend_linearIndependent_of_span : ∀ (g m r : ℕ) (w : Fin r → Fin g → ℂ) (b : Fin m → Fin g → ℂ), LinearIndependent ℂ w → LinearIndependent ℂ b → (∀ a, w a ∈ Submodule.span ℂ (Set.range b)) → ∃ (k : ℕ) (J : Fin k → Fin m), r + k = m ∧ LinearIndependent ℂ (Fin.append w (fun j => b (J j))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Exchange.exists_completion_by_members | exact GlobalTheory.CompanionTheory.Ar.Exchange.exists_completion_by_members | (intros; apply GlobalTheory.CompanionTheory.Ar.Exchange.exists_completion_by_members <;> assumption)
end
end
