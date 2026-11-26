module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MatRmulUnipMulHeadProj
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeries
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.ThetaHol

theorem exists_corner {κ ι : Type} [Fintype κ] [Fintype ι] (τ : Matrix ι ι ℂ) (S : ℝ)
    (x : Matrix κ ι ℚ) : ∃ s : κ → ι → Bool, ∀ ζ : κ → ι → ℂ, ‖ζ‖ ≤ S →
      ‖cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))‖ ≤
      ‖cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) +
        2 * (qv (x k) ⬝ᵥ fun i => (if s k i then -S else S : ℝ) * I)))‖ := by
  refine ⟨fun k i => decide (0 ≤ x k i), fun ζ hζ => ?_⟩
  rw [Complex.norm_exp, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_assoc, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.im_sum, Complex.add_im,
    Complex.mul_im, dotProduct, qv, Complex.ratCast_re, Complex.ratCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one,
    Complex.re_ofNat, Complex.im_ofNat, decide_eq_true_eq]
  refine mul_le_mul_of_nonneg_left (neg_le_neg (Finset.sum_le_sum fun k _ => ?_)) Real.pi_pos.le
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) zero_le_two
  have h1 : |(ζ k i).im| ≤ S := (Complex.abs_im_le_norm _).trans
    ((norm_le_pi_norm (ζ k) i).trans ((norm_le_pi_norm ζ k).trans hζ))
  have h2 := abs_le.mp h1
  split_ifs with h
  · have : (0 : ℝ) ≤ (x k i : ℝ) := by exact_mod_cast h
    nlinarith
  · have : (x k i : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
    nlinarith

theorem differentiable_thS {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {φ : Matrix κ ι ℚ → ℂ} (hφ : IsSB φ) {τ : Matrix ι ι ℂ} (hτ : τ ∈ Siegel ι) :
    Differentiable ℂ (thS φ τ) := by
  intro ζ₀
  let F : Matrix κ ι ℚ → (κ → ι → ℂ) → ℂ := fun x ζ => φ x *
    cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))
  let S : ℝ := ‖ζ₀‖ + 2
  let cor : (κ → ι → Bool) → κ → ι → ℂ := fun s k i => ((if s k i then -S else S : ℝ) : ℂ) * I
  choose s hs using fun x : Matrix κ ι ℚ => exists_corner τ S x
  have hFd : ∀ x, Differentiable ℂ (F x) := by
    intro x
    simp only [F, dotProduct]
    fun_prop
  have hbd : ∀ x, ∀ z : κ → ι → ℂ, ‖z‖ ≤ S → ‖F x z‖ ≤ ‖F x (cor (s x))‖ := by
    intro x z hz
    simp only [F, norm_mul]
    exact mul_le_mul_of_nonneg_left (hs x z hz) (norm_nonneg _)
  have hsum : Summable fun x => ‖F x (cor (s x))‖ := by
    have hfin : Summable fun x => ∑ t : κ → ι → Bool, ‖F x (cor t)‖ :=
      summable_sum fun t _ => SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ (cor t)
    refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hfin
    exact Finset.single_le_sum (f := fun t => ‖F x (cor t)‖) (fun t _ => norm_nonneg _)
      (Finset.mem_univ (s x))
  have hder : ∀ x, ∀ ζ ∈ Metric.ball (0 : κ → ι → ℂ) (‖ζ₀‖ + 1),
      ‖fderiv ℂ (F x) ζ‖ ≤ 2 * ‖F x (cor (s x))‖ := by
    intro x ζ hζ
    have h := GlobalTheory.SCV.norm_fderiv_le_of_ball (f := F x) (c := ζ) (r := 1)
      (M := ‖F x (cor (s x))‖) one_pos (hFd x).differentiableOn (fun z hz => hbd x z (by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        rw [Metric.mem_ball, dist_zero_right] at hζ
        have := norm_sub_norm_le z ζ
        simp only [S]
        linarith))
    simpa using h
  have h0 : ζ₀ ∈ Metric.ball (0 : κ → ι → ℂ) (‖ζ₀‖ + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have key := hasFDerivAt_tsum_of_isPreconnected (hsum.mul_left 2) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (fun x ζ _ => (hFd x ζ).hasFDerivAt) hder h0
    (SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ ζ₀).of_norm h0
  exact key.differentiableAt

theorem differentiable_thA {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) {φ : TF n g} (hφ : IsSB φ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Differentiable ℂ (thA X bas idx φ x) := by
  have hτ := UnAct.tauMat_mem idx hs hx
  have hlin : Differentiable ℂ fun z : Fin n → Fin g → ℂ => fun k => hMat X bas idx x *ᵥ z k := by
    refine differentiable_pi.2 fun k => differentiable_pi.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hth := (differentiable_thS hφ hτ).comp hlin
  have hq : Differentiable ℂ fun z : Fin n → Fin g → ℂ => ∑ k, (hMat X bas idx x *ᵥ z k) ⬝ᵥ
      imInv X bas idx x *ᵥ (hMat X bas idx x *ᵥ z k) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  unfold thA
  exact ((hq.const_mul _).cexp.const_mul _).mul hth

end GlobalTheory.SW.ThetaHol

namespace GlobalTheory.SW

theorem theta_holomorphic_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (φ : TF n g), IsSB φ → ∀ P ∈ Harm.rowHighest ℂ c c', DifferentiableOn ℂ (thP X hr bas idx φ P) X.dom ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, thP X hr bas idx φ P (rmul x b) = bchar (wtOf X hr c c' n) b * thP X hr bas idx φ P x) ∧ (∀ γ, IsUn X γ → ∀ x ∈ X.dom, thP X hr bas idx (wG X bas idx γ φ) P (lact γ x) = thP X hr bas idx φ P x) ∧ ∀ x ∈ X.dom, AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn c c' φ hφ P hP
  obtain ⟨m, a, b, t, ht⟩ := (GlobalTheory.T.thetaCharacteristics_iff_testFunction_thetaSeries E r X g q0 hr bas idx n hs hn).2 φ hφ
  have hH := Harm.isHarmonic_of_mem_rowHighest hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hd : DifferentiableOn ℂ (fun x => ∑ j, t j * thFr X hr bas idx n
        (fun k i => (a j k i : ℝ)) (fun k i => (b j k i : ℝ)) P x) X.dom :=
      DifferentiableOn.fun_sum fun j _ => (differentiableOn_thFr idx hs hr n _ _ hH).const_mul (t j)
    exact hd.congr fun x hx => ht P x hx
  · intro x hx u hu
    have hxu := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hu
    rw [ht P _ hxu, ht P x hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [thFr_rmul idx hr _ _ hs hP hx hu]
    ring
  · intro γ hγ x hx
    unfold thP
    rw [(wG_laws E r X g bas idx n hs hn γ hγ φ hφ).2.1 x hx]
  · intro x hx
    exact GlobalTheory.SCV.analyticOnNhd_of_differentiable (ThetaHol.differentiable_thA idx hs hφ hx) _

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeightStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_testFunction_holomorphic_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (φ : TF n g), IsSB φ → ∀ P ∈ Harm.rowHighest ℂ c c', DifferentiableOn ℂ (thP X hr bas idx φ P) X.dom ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, thP X hr bas idx φ P (rmul x b) = bchar (wtOf X hr c c' n) b * thP X hr bas idx φ P x) ∧ (∀ γ, IsUn X γ → ∀ x ∈ X.dom, thP X hr bas idx (wG X bas idx γ φ) P (lact γ x) = thP X hr bas idx φ P x) ∧ ∀ x ∈ X.dom, AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ := by
  first | exact @GlobalTheory.SW.theta_holomorphic_weight | exact GlobalTheory.SW.theta_holomorphic_weight | (intros; apply GlobalTheory.SW.theta_holomorphic_weight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_ex_transport {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo s ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
    (x0 : Sp ℂ ⟶ Xo.X) (h : x0 = F.u i P) :
    ∃ ex : (Fin g → ℂ) → (ptO Xo x0 ⟶ Xo.univ.t.G),
      (∀ z, (ex z).left = (F.ex i P z).left) ∧ (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧
      (∀ z, ex z = 1 ↔ z ∈ P.range) ∧
      (∀ (a : 𝓞 E) z, ex (fun j => ty j (a : E) * z j) = ex z ≫ Xo.univ.t.act.act a) ∧
      ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo x0 a = ex ((l.M : ℂ)⁻¹ • P (F.t i a)) := by
  subst h
  refine ⟨F.ex i P, fun _ => rfl, F.ex_add i P hP, F.ex_onto i P hP, F.ex_ker i P hP, F.ex_lin i P hP, ?_⟩
  intro a ha
  exact F.ex_eta i P hP a ha


set_option maxHeartbeats 1000000 in
theorem uw_anFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp) (bas : (Fin W.g ⊕ Fin W.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin W.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (W.e j).1) (W.e j).2) → (∀ j, rowType (U.X k) (idx j) = relab c σ (W.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx W.e x.1 (U.X k).Λ (unC U k x), A.Marked (W.mark k) ∧ ∃ θ, A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr W k bas idx hS hpv hrow x hxu
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Pm, hPm, hPer, hux, hder, hfr⟩ := W.pt k x
  obtain ⟨Hm, χl, fr, θ, Fd, hHm, -, hIm, hfrhol, hfrne, hfrg, hfr0, hfrper, hread, hFd, hmean⟩ := hfr hxu
  obtain ⟨ex, hexl, hadd, honto, hker, hlin, hmark⟩ :=
    exists_ex_transport W.F (W.ik k) Pm hPer (U.un k x).x hux

  have hPv : ∀ a, Pm a = pv (U.X k) idx x.1 (W.φ k a : Fin r → E) := fun a => funext fun j => by
    rw [hPm, hpv]
  have hφs : ∀ u ∈ (U.X k).Λ, ∃ a, (W.φ k a : Fin r → E) = u := fun u hu =>
    ⟨(W.φ k).symm ⟨u, hu⟩, by simp⟩
  have hembφ : ∀ a, W.emb k a = (W.φ k a : Fin r → E) := fun a => rfl
  have hrange : ∀ z, z ∈ Pm.range ↔ ∃ v ∈ (U.X k).Λ, z = pv (U.X k) idx x.1 v := by
    intro z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, SetLike.coe_mem _, hPv a⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := hφs v hv
      exact ⟨a, hPv a⟩
  obtain ⟨-, -, -, -, -, hspan, hEF⟩ := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr W k
  have hrng : Set.range (W.emb k) = ((U.X k).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      rw [hembφ]
      exact SetLike.coe_mem _
    · intro hv
      obtain ⟨a, rfl⟩ := hφs v hv
      exact ⟨a, hembφ a⟩
  obtain ⟨-, -, -, -, hsm, -, hL, -⟩ := hx_laws E r (U.X k) W.g bas idx 0 hS ⟨0, rfl⟩ x.1 x.2

  have him : ∀ u ∈ (U.X k).Λ, ∀ v ∈ (U.X k).Λ,
      (hermForm Hm (pv (U.X k) idx x.1 u) (pv (U.X k) idx x.1 v)).im = (EF (U.X k) u v : ℝ) := by
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hφs u hu
    obtain ⟨b, rfl⟩ := hφs v hv
    rw [← hPv, ← hPv, hIm, ← hembφ, ← hembφ, ← hEF a b]
    norm_cast
  have hH : ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w :=
    (hL (U.X k).Λ (hrng ▸ hspan)).2 Hm hHm him
  have hfun : (fun z => (ex z).left) = fun z => (W.F.ex (W.ik k) Pm z).left := funext hexl
  refine ⟨{ ex := ex
            ex_add := hadd
            ex_onto := honto
            ex_ker := fun z => (hker z).trans (hrange z)
            ex_lin := fun a z => by
              have e : (fun j => rowType (U.X k) (idx j) (a : E) * z j) =
                  fun j => relab c σ (W.e j).1 (a : E) * z j := funext fun j => by rw [hrow]
              rw [e]
              exact hlin a z
            hol := by
              intro V f
              simp only [Set.sep_univ, hexl]
              exact ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol W.F (W.ik k) Pm hPer V f
            der := fun ℓ => by
              rw [hfun]
              exact hder ℓ.1 ℓ.2
            fr := fr
            fr_hol := fun j => by simp only [hexl]; exact hfrhol j
            fr_ne := fun j z => by simp only [hexl]; exact hfrne j z
            fr_g := fun j j' z => by simp only [hexl]; exact hfrg j j' z
            fr_0 := fun j => by simp only [hexl]; exact hfr0 j
            χ := fun v => if ‖χl (pv (U.X k) idx x.1 v)‖ = 1 then χl (pv (U.X k) idx x.1 v) else 1
            χ_norm := fun v _ => by
              try dsimp only
              split_ifs with h
              · exact h
              · simp
            fr_per := fun v hv j z hz => by
              obtain ⟨a, rfl⟩ := hφs v hv
              obtain ⟨hn, hp⟩ := hfrper a j z
              try dsimp only
              rw [← hPv, if_pos hn, ← hH, ← hH]
              exact hp (by simpa only [hexl] using hz) }, ?_, θ, ?_, ?_⟩
  · intro a ha
    have hM : pv (U.X k) idx x.1 (((l.M : E)⁻¹) • W.mark k a) = (l.M : ℂ)⁻¹ • Pm (W.F.t (W.ik k) a) := by
      funext j
      simp only [hsm, hrow, hPv, Pi.smul_apply, smul_eq_mul, map_inv₀, map_natCast]
      rfl
    exact (hmark a ha).trans (congrArg ex hM.symm)
  · intro j z pt h1 h2 h3
    rw [zpow_one]
    exact hread j z pt (h1.trans (hexl z)) h2 (by simpa only [hexl] using h3)
  · refine ⟨Pm.range, Fd, hrange, hFd, ?_⟩
    simpa only [hH] using hmean

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFibre_unitFrame_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp) (bas : (Fin W.g ⊕ Fin W.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin W.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (W.e j).1) (W.e j).2) → (∀ j, rowType (U.X k) (idx j) = relab c σ (W.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx W.e x.1 (U.X k).Λ (unC U k x), A.Marked (W.mark k) ∧ ∃ θ, A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ := by
  first | exact @GlobalTheory.Dict.uw_anFib | exact GlobalTheory.Dict.uw_anFib | (intros; apply GlobalTheory.Dict.uw_anFib <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

theorem dense_of_span_real {g : ℕ} (S : Submodule ℚ (Fin g → ℂ))
    (hS : Submodule.span ℝ (S : Set (Fin g → ℂ)) = ⊤) : Dense (S : Set (Fin g → ℂ)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  have hz : z ∈ Submodule.span ℝ (S : Set (Fin g → ℂ)) := hS ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem w hw => exact subset_closure hw
  | zero => exact subset_closure S.zero_mem
  | add a b _ _ ha hb => exact map_mem_closure₂ continuous_add ha hb fun c hc d hd => S.add_mem hc hd
  | smul t w _ hw =>

    have hq : ∀ q : ℚ, (q : ℝ) • w ∈ closure (S : Set (Fin g → ℂ)) := fun q =>
      map_mem_closure (continuous_const_smul (q : ℝ)) hw fun u hu => by
        rw [SetLike.mem_coe, Rat.cast_smul_eq_qsmul ℝ q u]
        exact S.smul_mem q hu
    have hcl : IsClosed {s : ℝ | s • w ∈ closure (S : Set (Fin g → ℂ))} :=
      isClosed_closure.preimage (continuous_id.smul continuous_const)
    have hsub : closure (Set.range fun q : ℚ => (q : ℝ)) ⊆ {s : ℝ | s • w ∈ closure (S : Set (Fin g → ℂ))} :=
      hcl.closure_subset_iff.2 (by rintro _ ⟨q, rfl⟩; exact hq q)
    exact hsub ((Rat.denseRange_cast (𝕜 := ℝ)).closure_range ▸ Set.mem_univ t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) {n : ℕ}

noncomputable def zRLin (x : Frame X.Ψ r) : WR X n →ₗ[ℝ] (Fin n → Fin g → ℂ) where
  toFun := zR X idx x
  map_add' u v := by
    funext k i
    simp only [zR, Pi.add_apply]
    split_ifs
    · simp [hermC, mul_add, Finset.sum_add_distrib]
    · rw [mulVec_add, Pi.add_apply]
  map_smul' t v := by
    funext k i
    simp only [zR, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, real_smul, map_mul, conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [mulVec_smul, Pi.smul_apply]

theorem denseRange_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    DenseRange (pv X idx x) := by

  have hrange : ((LinearMap.range ((LinearMap.funLeft ℚ ℂ idx).comp (perLin X x)) :
      Submodule ℚ (Fin g → ℂ)) : Set (Fin g → ℂ)) = Set.range (pv X idx x) := by
    ext z
    simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    exact Iff.rfl
  unfold DenseRange
  rw [← hrange]
  apply dense_of_span_real
  rw [hrange]
  exact GlobalTheory.Dict.span_range_pv idx hs hx

theorem denseRange_zR_embR (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    DenseRange (zR X idx x ∘ embR X (n := n)) := by
  have h : zR X idx x ∘ embR X (n := n) = fun y k => pv X idx x (y k) := by
    funext y k
    exact zR_embR X idx x y k
  rw [h]
  exact DenseRange.piMap fun _ => denseRange_pv X idx hs hx

theorem exists_equiv_zR (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v := by

  have hsurj : Function.Surjective (zRLin X idx x (n := n)) := by
    have hcl : IsClosed (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) :=
      Submodule.closed_of_finiteDimensional _
    have hd : Dense (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) := by
      refine (denseRange_zR_embR X idx hs hx (n := n)).mono ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨embR X y, rfl⟩
    have huniv := hcl.closure_eq.symm.trans hd.closure_eq
    intro z
    have hz : z ∈ (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) := by
      rw [huniv]
      trivial
    exact LinearMap.mem_range.1 hz

  have hg : g = Fintype.card X.Ψ * r := by
    simpa [Fintype.card_prod] using Fintype.card_congr idx
  have hdim : Module.finrank ℝ (WR X n) = Module.finrank ℝ (Fin n → Fin g → ℂ) := by
    simp only [WR, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, hg]
    ring
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun v => rfl⟩

theorem EFR_embR (y y' : Matrix (Fin n) (Fin r) E) :
    EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ) := by
  have key : ∀ (τ : X.Ψ) (k : Fin n),
      hermC τ.1 X.Gm (embR X y τ k) (embR X y' τ k) = τ.1 (herm X.Gm (y k) (y' k)) :=
    fun τ k => ReciprocityTheory.ChartRestriction.G.FD.hermC_emb τ.1 X.Gm (y k) (y' k)
  rw [EFR, Rat.cast_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [EF_def, GlobalTheory.UnitFrame.trace_eq_sum_re X.Ψ X.cmType]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [key, map_mul]

theorem zR_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v) ∧ (∀ v v' : WR X n, (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v') ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ)) ∧ DenseRange (embR X (n := n)) ∧ ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = zR X idx x v := by
  intro E _ _ _ r X g q0 _ bas idx n hs hn x hxd
  obtain ⟨L, hL⟩ := exists_equiv_zR X idx (n := n) hs hxd
  have hlaws := GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hxd

  have hD : DenseRange (embR X (n := n)) := by
    have h1 : embR X (n := n) = L.symm ∘ (zR X idx x ∘ embR X) := by
      funext y
      simp only [Function.comp_apply, ← hL, ContinuousLinearEquiv.symm_apply_apply]
    rw [h1]
    exact L.symm.surjective.denseRange.comp (denseRange_zR_embR X idx hs hxd) L.symm.continuous

  have hB : ∀ v v' : WR X n,
      (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v' := by
    have hc1 : Continuous fun p : WR X n × WR X n =>
        (∑ k, hx X bas idx x (zR X idx x p.1 k) (zR X idx x p.2 k)).im := by
      simp only [← hL, GlobalTheory.Dict.hx]
      fun_prop
    have hc2 : Continuous fun p : WR X n × WR X n => EFR X p.1 p.2 := by
      simp only [EFR, hermC]
      fun_prop
    have heq := (hD.prodMap hD).equalizer hc1 hc2 (by
      funext ⟨y, y'⟩
      simp only [Function.comp_apply, Prod.map_apply]
      rw [EFR_embR X y y', Complex.im_sum, Rat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zR_embR, zR_embR]
      exact hlaws.2.2.1 (y k) (y' k))
    exact fun v v' => congrFun heq (v, v')

  have hF : ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n,
      zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) =
        zR X idx x v := by
    intro γ hγ
    have hA : Continuous fun v : WR X n =>
        (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k : WR X n) := by
      fun_prop
    have hc1 : Continuous fun v : WR X n =>
        zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) :=
      (LinearMap.continuous_of_finiteDimensional (zRLin X idx (lact γ x) (n := n))).comp hA
    have hc2 : Continuous fun v : WR X n => zR X idx x v := by
      simp only [← hL]
      exact L.continuous
    have heq := hD.equalizer hc1 hc2 (by
      funext y
      simp only [Function.comp_apply]
      have hemb : (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ embR X y τ k : WR X n) =
          embR X (Matrix.of fun k => (γ : Matrix (Fin r) (Fin r) E) *ᵥ y k) := by
        funext τ k
        exact (GlobalTheory.PerMove.emb_mulVec τ.1 _ (y k)).symm
      rw [hemb]
      funext k
      rw [zR_embR, zR_embR]
      exact (hlaws.2.2.2.2.2.2.2 γ hγ).2.1 (y k))
    exact fun v => congrFun heq v
  exact ⟨⟨L, hL⟩, hB, fun y y' => EFR_embR X y y', hD, hF⟩

end GlobalTheory.Ker
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensityStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v) ∧ (∀ v v' : WR X n, (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v') ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ)) ∧ DenseRange (embR X (n := n)) ∧ ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = zR X idx x v := by
  first | exact @GlobalTheory.Ker.zR_laws | exact GlobalTheory.Ker.zR_laws | (intros; apply GlobalTheory.Ker.zR_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

section Cast

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r}

theorem SameSp.dmin_castFr (h : SameSp X' X) (x : Frame X'.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (castFr h.psi x) τ i = dmin X'.Gm x ⟨τ.1, h.psi.ge τ.2⟩ i := by
  rw [← h.gm]
  rfl

theorem SameSp.castFr_mem_dom (h : SameSp X' X) {x : Frame X'.Ψ r} (hx : x ∈ X'.dom) :
    castFr h.psi x ∈ X.dom := by
  have hx' : ∀ τ : X'.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X'.p0 i * (dmin X'.Gm x τ i).re := hx
  show ∀ τ : X.Ψ, (mat (castFr h.psi x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (castFr h.psi x) τ i).re
  intro τ
  obtain ⟨hdet, hpos⟩ := hx' ⟨τ.1, h.psi.ge τ.2⟩
  refine ⟨hdet, fun i => ?_⟩
  rw [h.dmin_castFr, ← h.p0]
  exact hpos i

theorem SameSp.EF_eq (h : SameSp X' X) (u v : Fin r → E) : EF X' u v = EF X u v := by
  rw [EF_def, EF_def, h.gm, h.ka]

private theorem GL_inv_mulVec_mulVec {K : Type} [Field K] {n : ℕ} (ga : GL (Fin n) K) (u : Fin n → K) :
    ((ga⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((ga : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem GL_mulVec_inv_mulVec {K : Type} [Field K] {n : ℕ} (ga : GL (Fin n) K) (u : Fin n → K) :
    (ga : Matrix (Fin n) (Fin n) K) *ᵥ (((ga⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

private theorem mem_mapL_iff (ga : GL (Fin r) E) (L : Lt E r) (v : Fin r → E) :
    v ∈ mapL ga L ↔ ∃ u ∈ L, v = (ga : Matrix (Fin r) (Fin r) E) *ᵥ u := by
  unfold mapL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [Matrix.toLin'_apply]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [Matrix.toLin'_apply]⟩

private theorem EF_mulVec_of_isUn {Y : Data E r} {ga : GL (Fin r) E} (hga : IsUn Y ga) (u v : Fin r → E) :
    EF Y ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = EF Y u v := by
  rw [EF_def, EF_def, hga u v]

end Cast

theorem anFib_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X' X : Data E r) (h : SameSp X' X) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X'.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X' bas' idx' e x L y) (ga : GL (Fin r) E), IsSympl X' bas' → IsSympl X bas → x ∈ X'.dom → SelfD X' L → IsUn X ga → (∀ v, pv X' idx' x v = pv X idx (castFr h.psi x) v) → (∀ j, rowType X' (idx' j) = rowType X (idx j)) → lact ga (castFr h.psi x) ∈ X.dom ∧ (IsUnitFr X' x → IsUnitFr X (lact ga (castFr h.psi x))) ∧ SelfD X (mapL ga L) ∧ ∃ A' : AnFib X bas idx e (lact ga (castFr h.psi x)) (mapL ga L) y, (∀ θ, A.Reads 1 y.s θ → A'.Reads 1 y.s θ) ∧ (∀ θ, MeanOne X' bas' idx' x L θ → MeanOne X bas idx (lact ga (castFr h.psi x)) (mapL ga L) θ) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mvMap ga mk) := by
  intro E _ _ _ H Dw l Xo c _ r g X' X h bas' idx' bas idx e x L y A ga hs' hs hxm hL hga hpv hrow
  have hx₀ : castFr h.psi x ∈ X.dom := h.castFr_mem_dom hxm
  obtain ⟨-, -, L3, -, -, -, -, L8⟩ := hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ _ hx₀
  obtain ⟨-, -, L3', -, -, -, -, -⟩ := hx_laws E r X' g bas' idx' 0 hs' ⟨0, rfl⟩ x hxm
  obtain ⟨hdom1, hpv1, hunit1, hhx1⟩ := L8 ga hga
  have pvT : ∀ u, pv X idx (lact ga (castFr h.psi x)) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) =
      pv X' idx' x u := fun u => (hpv1 u).trans (hpv u).symm
  have hxeq : ∀ z w, hx X bas idx (castFr h.psi x) z w = hx X' bas' idx' x z w := by
    intro z w
    rw [hx_eq_hermForm idx, hx_eq_hermForm idx']
    have key := hermForm_eq_of_im (ThFr.Hm X bas idx (castFr h.psi x)) (ThFr.Hm X' bas' idx' x) 1 1
      (Set.range (pv X idx (castFr h.psi x))) (span_range_pv idx hs hx₀) ?_ z w
    · simpa only [_root_.one_mul] using key
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp only [_root_.one_mul]
      rw [← hx_eq_hermForm idx, ← hx_eq_hermForm idx', L3 a b, ← hpv a, ← hpv b, L3' a b, h.EF_eq]
  have hxT : ∀ z w, hx X bas idx (lact ga (castFr h.psi x)) z w = hx X' bas' idx' x z w :=
    fun z w => (hhx1 z w).trans (hxeq z w)
  have unit0 : IsUnitFr X' x → IsUnitFr X (castFr h.psi x) := by
    unfold IsUnitFr
    intro hu τ i
    rw [h.dmin_castFr]
    exact hu _ i
  have hSD : SelfD X (mapL ga L) := by
    unfold SelfD at hL ⊢
    obtain ⟨hfg, hmem⟩ := hL
    refine ⟨hfg.map _, fun v => ?_⟩
    rw [mem_mapL_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩ w hw
      obtain ⟨u', hu', rfl⟩ := (mem_mapL_iff ga L w).1 hw
      obtain ⟨k, hk⟩ := (hmem u).1 hu u' hu'
      exact ⟨k, by rw [EF_mulVec_of_isUn hga, ← h.EF_eq]; exact hk⟩
    · intro hv
      refine ⟨((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, ?_, (GL_mulVec_inv_mulVec ga v).symm⟩
      rw [hmem]
      intro u' hu'
      obtain ⟨k, hk⟩ := hv _ ((mem_mapL_iff ga L _).2 ⟨u', hu', rfl⟩)
      refine ⟨k, ?_⟩
      rw [h.EF_eq, ← EF_mulVec_of_isUn hga (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) u',
        GL_mulVec_inv_mulVec]
      exact hk
  have hT : ∀ z, (∃ v ∈ L, z = pv X' idx' x v) ↔
      ∃ v ∈ mapL ga L, z = pv X idx (lact ga (castFr h.psi x)) v := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, (mem_mapL_iff ga L _).2 ⟨u, hu, rfl⟩, (pvT u).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
      exact ⟨u, hu, pvT u⟩
  refine ⟨hdom1, fun hu => hunit1 (unit0 hu), hSD, ?_⟩
  have hlin : ∀ (a : 𝓞 E) (z : Fin g → ℂ),
      A.ex (fun j => rowType X (idx j) (a : E) * z j) = A.ex z ≫ Xo.univ.t.act.act a := by
    intro a z
    have hfun : (fun j => rowType X (idx j) (a : E) * z j) =
        (fun j => rowType X' (idx' j) (a : E) * z j) := funext fun j => by rw [hrow]
    rw [hfun]
    exact A.ex_lin a z
  have hnorm : ∀ v ∈ mapL ga L, ‖A.χ (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)‖ = 1 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
    rw [GL_inv_mulVec_mulVec]
    exact A.χ_norm u hu
  refine ⟨
    { ex := A.ex
      ex_add := A.ex_add
      ex_onto := A.ex_onto
      ex_ker := fun z => (A.ex_ker z).trans (hT z)
      ex_lin := hlin
      hol := A.hol
      der := A.der
      fr := A.fr
      fr_hol := A.fr_hol
      fr_ne := A.fr_ne
      fr_g := A.fr_g
      fr_0 := A.fr_0
      χ := fun v => A.χ (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
      χ_norm := hnorm
      fr_per := ?_ }, fun θ hθ => hθ, ?_, ?_⟩
  · intro v hv j z hz
    obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
    simp only [GL_inv_mulVec_mulVec, pvT, hxT]
    exact A.fr_per u hu j z hz
  · intro θ hθ
    unfold MeanOne at hθ ⊢
    obtain ⟨Ag, Fd, hA, hFd, hint⟩ := hθ
    refine ⟨Ag, Fd, fun z => (hA z).trans (hT z), hFd, ?_⟩
    simp only [hxT]
    exact hint
  · intro mk hmk
    unfold AnFib.Marked at hmk ⊢
    intro a ha
    rw [hmk a ha]
    show A.ex _ = A.ex _
    congr 1
    have hmv : mvMap ga mk a = (ga : Matrix (Fin r) (Fin r) E) *ᵥ mk a := by
      simp [mvMap, Matrix.toLin'_apply]
    rw [hmv, ← Matrix.mulVec_smul, pvT]

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnalyticFrameOfAnalyticFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnalyticFrameOfAnalyticFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem AnFib.exists_anPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e, (∀ z, Φ.e z = A.ex z) ∧ Φ.fr = A.fr ∧ (∀ z, z ∈ Φ.lat ↔ ∃ v ∈ L, z = pv X idx x v) ∧ (∀ z w, hermForm Φ.Hm z w = hx X bas idx x z w) ∧ (∀ v ∈ L, Φ.χ (pv X idx x v) = A.χ v) ∧ (∀ (k : ℤ) F θ, Φ.toAnFr.Rd k F θ ↔ A.Reads k F θ) ∧ ∀ (k : ℕ) a θ, AnVal.fock Φ.Hm (k : ℤ) a θ = Dict.fock X bas idx x k a θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  obtain ⟨-, -, -, hadj, -, hinj, hsp, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let lat : AddSubgroup (Fin g → ℂ) :=
    { carrier := {z | ∃ v ∈ L, z = pv X idx x v}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u + v, add_mem hu hv, by rw [pv, pv, pv, per_add]; rfl⟩
      zero_mem' := ⟨0, zero_mem _, by rw [pv, per_zero]; rfl⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨-u, neg_mem hu, by rw [pv, pv, per_neg]; rfl⟩ }
  have hχ (v) : Function.invFun (pv X idx x) (pv X idx x v) = v := Function.leftInverse_invFun hinj v
  let Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e :=
    { e := A.ex
      lat := lat
      span := by
        rw [← (hsp L (SW.TensLat.span_of_selfD X hL)).1]
        congr 1
        ext z
        exact ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, h.symm⟩, fun ⟨v, hv, h⟩ => ⟨v, hv, h.symm⟩⟩
      e_add := A.ex_add
      e_onto := A.ex_onto
      e_ker := A.ex_ker
      hol := fun U f => by
        obtain ⟨h1, h2⟩ := A.hol U f
        simp only [Set.mem_univ, true_and] at h1 h2
        exact ⟨h1, h2⟩
      Hm := ThFr.Hm X bas idx x
      herm := Hm_isHermitian idx hs hx
      χ := fun z => A.χ (Function.invFun (pv X idx x) z)
      fr := A.fr
      fr_hol := A.fr_hol
      fr_ne := A.fr_ne
      fr_g := A.fr_g
      fr_0 := A.fr_0
      χ_norm := by
        rintro _ ⟨v, hv, rfl⟩
        rw [hχ]
        exact A.χ_norm v hv
      fr_per := by
        rintro _ ⟨v, hv, rfl⟩ j z hz
        rw [hχ, ← hx_eq_hermForm, ← hx_eq_hermForm]
        exact A.fr_per v hv j z hz
      lin := A.ex_lin
      adj := fun a z w => by
        rw [← hx_eq_hermForm, ← hx_eq_hermForm]
        have hb : cc (a : E) = ((H.bar a : 𝓞 E) : E) := (H.bar_eq a).symm
        have h := hadj (a : E) z w
        rw [hb] at h
        exact h
      der := A.der }
  refine ⟨Φ, fun _ => rfl, rfl, fun _ => Iff.rfl, fun z w => (hx_eq_hermForm idx x z w).symm,
    fun v _ => congrArg A.χ (hχ v), fun _ _ _ => Iff.rfl, fun k a θ => ?_⟩
  funext z
  change cexp _ * θ (z + a) = cexp _ * θ (z + a)
  congr 2
  rw [hx_eq_hermForm]
  change _ - _ * _ * hermForm (ThFr.Hm X bas idx x) a a / 2 = _
  change -(_ * _ * hermForm (ThFr.Hm X bas idx x) z a) - _ = _
  simp only [hermForm, add_dotProduct, smul_dotProduct, smul_eq_mul, Int.cast_natCast]
  ring

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnalyticFrameOfAnalyticFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticFrame_of_analyticFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e, (∀ z, Φ.e z = A.ex z) ∧ Φ.fr = A.fr ∧ (∀ z, z ∈ Φ.lat ↔ ∃ v ∈ L, z = pv X idx x v) ∧ (∀ z w, hermForm Φ.Hm z w = hx X bas idx x z w) ∧ (∀ v ∈ L, Φ.χ (pv X idx x v) = A.χ v) ∧ (∀ (k : ℤ) F θ, Φ.toAnFr.Rd k F θ ↔ A.Reads k F θ) ∧ ∀ (k : ℕ) a θ, AnVal.fock Φ.Hm (k : ℤ) a θ = Dict.fock X bas idx x k a θ := by
  first | exact @GlobalTheory.Dict.AnFib.exists_anPt | exact GlobalTheory.Dict.AnFib.exists_anPt | (intros; apply GlobalTheory.Dict.AnFib.exists_anPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.VacEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {n : ℕ}

theorem row_mul_transpose (y : Matrix (Fin n) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (k : Fin n) : (y * γᵀ) k = γ *ᵥ y k := by
  funext j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem epsW_mul_transpose (w : E) (γ : GL (Fin r) E) (hγ : IsUn X γ)
    (y : Matrix (Fin n) (Fin r) E) :
    epsW X w (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = epsW X w y := by

  have key : ∀ k, EF X ((y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) (w • (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) =
      EF X (y k) (w • y k) := by
    intro k
    rw [row_mul_transpose, ← Matrix.mulVec_smul, EF_def, EF_def, hγ (y k) (w • y k)]
  unfold epsW
  simp only [key]

end GlobalTheory.SW.VacEx

namespace GlobalTheory.SW

open VacEx

theorem exists_vacua_and_multipliers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : Level X, ∃ (v₀ : Lt E r → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) ∧ ∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L) := by
  intro E _ _ _ r X g bas idx n hs hn D

  obtain ⟨-, huniq, hgrp, hlats, -, -, -⟩ :=
    GlobalTheory.T.level_structure_properties E r X g bas idx (2 * r) hs ⟨r, two_mul r⟩ D (by omega)
  obtain ⟨-, hstd, -⟩ := GlobalTheory.SW.finite_cls_and_stab E n 1 one_pos

  have hvac : ∀ L, SelfD X L → (∃ v, IsVac X bas D.w (tens (stdL E n) L) v) ∧
      ∀ v v', IsVac X bas D.w (tens (stdL E n) L) v → IsSB v' →
        (∀ y ∈ tens (stdL E n) L, epsW X D.w y • heisG X bas y v' = v') → ∃ c : ℂ, v' = c • v := by
    intro L hL
    obtain ⟨h1, h2, -, -⟩ :=
      GlobalTheory.SW.TensVac.vacua E r X g bas idx n hs hn D.w D.w_int D.w_tr L hL 1 (stdL E n) hstd
    exact ⟨h1, fun v v' hv hv' hfix => ⟨_, h2 v v' hv hv' hfix⟩⟩
  classical
  let v₀ : Lt E r → TF n g := fun L =>
    if h : ∃ v, IsVac X bas D.w (tens (stdL E n) (D.sh L)) v then h.choose else 0
  have hv₀ : ∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L) := by
    intro L hL
    have h := (hvac _ (hlats L hL).1).1
    rw [show v₀ L = h.choose from dif_pos h]
    exact h.choose_spec

  let μ : GL (Fin r) E → Lt E r → ℂ := fun γ L =>
    if h : (∃ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧
        ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L)
    then h.2.choose * (((D.lam h.1.choose)⁻¹ : ℂˣ) : ℂ) else 0
  refine ⟨v₀, μ, hv₀, ?_⟩
  intro γ hγ L hL k hk
  obtain ⟨hγu, -⟩ := (hgrp γ).1 hγ
  obtain ⟨-, -, -, hmove⟩ := hlats L hL
  obtain ⟨hL', hsh⟩ := hmove γ hγ
  obtain ⟨hSB, -, hfix⟩ := hv₀ L hL
  have hv' := hv₀ _ hL'
  rw [hsh] at hv'
  have hSD' : SelfD X (mapL γ (D.sh L)) := by
    rw [← hsh]
    exact (hlats _ hL').1
  have hlaw := GlobalTheory.SW.wG_laws E r X g bas idx n hs hn γ hγu (v₀ L) hSB

  have himg : ∀ y ∈ tens (stdL E n) (mapL γ (D.sh L)),
      epsW X D.w y • heisG X bas y (wG X bas idx γ (v₀ L)) = wG X bas idx γ (v₀ L) := by
    intro y hy
    set y₀ : Matrix (Fin n) (Fin r) E := y * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ with hy₀
    have hyy : y₀ * (γ : Matrix (Fin r) (Fin r) E)ᵀ = y := by
      rw [hy₀, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
        Matrix.mul_one]
    have hy₀m : y₀ ∈ tens (stdL E n) (D.sh L) := by
      rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hy ⊢
      intro k
      obtain ⟨x, hx, hxk⟩ := Submodule.mem_map.mp (hy k)
      rw [hy₀, VacEx.row_mul_transpose, ← hxk]
      simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        Units.inv_mul, Matrix.one_mulVec]
      exact hx
    have hSB0 : IsSB (heisG X bas y₀ (v₀ L)) := (GlobalTheory.SW.TensVac.laws idx hs hn y₀ hSB).1
    have hlaw0 := GlobalTheory.SW.wG_laws E r X g bas idx n hs hn γ hγu _ hSB0
    rw [← hyy, ← hlaw.2.2.2.2.2.2 y₀, VacEx.epsW_mul_transpose X D.w γ hγu y₀, ← hlaw0.2.2.2.1,
      hfix y₀ hy₀m]
  have hex : ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L) :=
    (hvac _ hSD').2 _ _ hv' hlaw.1 himg
  have hcond : (∃ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧
      ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L) := ⟨⟨k, hk⟩, hex⟩

  have hk' : hcond.1.choose = k := Subtype.ext (huniq _ _ _ hcond.1.choose_spec hk)
  have hμ : μ γ L = hcond.2.choose * (((D.lam hcond.1.choose)⁻¹ : ℂˣ) : ℂ) := dif_pos hcond
  rw [hμ, hk', mul_assoc, Units.inv_mul, mul_one]
  exact hcond.2.choose_spec

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticBasisOfSelfD
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level

theorem GlobalTheory.Ker.exists_symplectic_basis_of_selfD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r), SelfD X X.Λ →
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (_ : Fin g ≃ X.Ψ × Fin r), IsSympl X bas := by
  intro E _ _ _ r X hL

  obtain ⟨bas, hbas⟩ := GlobalTheory.Dict.Letters.exists_isSympl X hL (Fintype.equivFin (X.Ψ × Fin r)).symm
  exact ⟨_, bas, (Fintype.equivFin _).symm, hbas⟩
end
