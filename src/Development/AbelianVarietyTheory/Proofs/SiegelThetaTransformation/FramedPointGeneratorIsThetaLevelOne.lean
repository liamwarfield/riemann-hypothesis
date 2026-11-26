module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibrePrincipalBundleSignEq
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem thetaSignExpEF_inv_of_selfDual_lattice {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (L : Lt E r) (hL : SelfD X L) (w : 𝓞 E) (v : Fin r → E) (hv : v ∈ L) :
    (eps1 X (w : E) v)⁻¹ = eps1 X (w : E) v := by
  have hwv : (w : E) • v ∈ L := by
    have h := L.smul_mem w hv
    rwa [← algebraMap_smul E w v] at h
  obtain ⟨k, hk⟩ := (hL.2 v).1 hv ((w : E) • v) hwv
  unfold eps1
  rw [hk, ← Complex.exp_neg, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  push_cast
  ring

theorem isTheta1_of_reads_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ θ, A.Reads 1 y.s θ → IsTheta1 X bas idx (H.w0 : E) x L θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨-, hall⟩ := reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s
  obtain ⟨hd, hper⟩ := hall θ hθ
  refine ⟨hd, fun v hv => ?_⟩
  have h := hper v hv
  rw [analyticFibre_principalBundle_sign_eq E H Dw l Xo c r g X bas idx e x L y A hs hx hL v hv, pow_one,
    thetaSignExpEF_inv_of_selfDual_lattice X L hL H.w0 v hv] at h
  exact h

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_generator_isThetaLevelOne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ θ, A.Reads 1 y.s θ → IsTheta1 X bas idx (H.w0 : E) x L θ := by
  first | exact @GlobalTheory.Dict.isTheta1_of_reads_generator | exact GlobalTheory.Dict.isTheta1_of_reads_generator | (intros; apply GlobalTheory.Dict.isTheta1_of_reads_generator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussRMulFactor
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.RealHeis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [GlobalTheory.Dict.hx, mulVec_add, add_dotProduct]

theorem hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [GlobalTheory.Dict.hx, mulVec_add, star_add, dotProduct_add]

theorem hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [GlobalTheory.Dict.hx, mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem contDiff_gaussR : ContDiff ℝ (⊤ : ℕ∞) (gaussR X bas idx x : (Fin n → Fin g → ℂ) → ℂ) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => star z) := Complex.conjCLE.contDiff
  have h1 : ∀ (k : Fin n) (i : Fin g), ContDiff ℝ (⊤ : ℕ∞)
      fun z : Fin n → Fin g → ℂ => (hMat X bas idx x *ᵥ z k) i := by
    intro k i
    simp only [mulVec, dotProduct]
    fun_prop
  have h2 : ∀ k : Fin n, ContDiff ℝ (⊤ : ℕ∞)
      fun z : Fin n → Fin g → ℂ => hx X bas idx x (z k) (z k) := by
    intro k
    change ContDiff ℝ _ fun z : Fin n → Fin g → ℂ => ∑ i, (hMat X bas idx x *ᵥ z k) i *
      ∑ j, imInv X bas idx x i j * star ((hMat X bas idx x *ᵥ z k) j)
    exact ContDiff.sum fun i _ => (h1 k i).mul
      (ContDiff.sum fun j _ => contDiff_const.mul (hc.comp (h1 k j)))
  exact (contDiff_const.mul (ContDiff.sum fun k _ => h2 k)).neg.cexp

theorem gaussR_mul_factor (hsym : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w))
    (z a : Fin n → Fin g → ℂ) :
    gaussR X bas idx x z * cexp (-(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • a k) (a k))) =
      cexp (-(π * I * ((∑ k, hx X bas idx x (z k) (a k)).im : ℝ))) * gaussR X bas idx x (z + a) := by
  have h1 : ∑ k, hx X bas idx x (a k) (z k) = conj (∑ k, hx X bas idx x (z k) (a k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hsym _ _
  simp only [gaussR, ← Complex.exp_add, Pi.add_apply, hx_add_left, hx_add_right, hx_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum, h1]
  congr 1
  generalize ∑ k, hx X bas idx x (z k) (a k) = S
  have h2 := Complex.sub_conj S
  push_cast at h2
  linear_combination (-(π : ℂ) / 2) * h2

end GlobalTheory.Ker.RealHeis

namespace GlobalTheory.Ker

theorem thR_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ φ : TF n g, IsSB φ → ContDiff ℝ (⊤ : ℕ∞) (thR X bas idx φ x : WR X n → ℂ) ∧ (∀ (y : Matrix (Fin n) (Fin r) E) (v : WR X n), thR X bas idx (heisG X bas y φ) x v = cexp (-(π * I * (EFR X v (embR X y) : ℝ))) * thR X bas idx φ x (v + embR X y)) ∧ (∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, thR X bas idx (wG X bas idx γ φ) (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = thR X bas idx φ x v) ∧ (∀ ψ, IsSB ψ → (thR X bas idx φ x = (thR X bas idx ψ x : WR X n → ℂ) → φ = ψ) ∧ thR X bas idx (φ + ψ) x = (thR X bas idx φ x + thR X bas idx ψ x : WR X n → ℂ)) ∧ ∀ a : ℂ, thR X bas idx (a • φ) x = (a • thR X bas idx φ x : WR X n → ℂ) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x hxd φ hφ
  obtain ⟨⟨L, hL⟩, him, -, -, hinv⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x hxd
  obtain ⟨hsym, -, -, -, -, -, -, hga⟩ := GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hxd
  have hLf : zR X idx x = (L : WR X n → Fin n → Fin g → ℂ) := funext fun v => (hL v).symm
  refine ⟨?_, fun y v => ?_, fun γ hγ v => ?_, fun ψ hψ => ⟨fun h => ?_, ?_⟩, fun a => ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (thA X bas idx φ x) :=
      (AnalyticOnNhd.contDiff (𝕜 := ℂ) (SCV.analyticOnNhd_of_differentiable
        (ThetaHol.differentiable_thA idx hs hφ hxd) _)).restrict_scalars ℝ
    have h2 := ((RealHeis.contDiff_gaussR X bas idx x).mul h1).comp L.contDiff
    rw [← hLf] at h2
    exact h2
  · have h1 := ((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).2.2.2.2 x hxd (zR X idx x v)
    have h2 : zR X idx x (v + embR X y) = zR X idx x v + zR X idx x (embR X y) := by
      rw [hLf, map_add (f := _)]
    have h3 := RealHeis.gaussR_mul_factor X bas idx x hsym (zR X idx x v) (zR X idx x (embR X y))
    rw [him] at h3
    rw [thR, thR, h1, h2, ← _root_.mul_assoc, ← _root_.mul_assoc, ← h3]
    rfl
  · rw [thR, thR, hinv γ hγ v, (wG_laws E r X g bas idx n hs hn γ hγ φ hφ).2.1 x hxd]
    simp only [gaussR, (hga γ hγ).2.2.2]
  · have hone : IsUn X (1 : GL (Fin r) E) := fun u w => by simp
    refine ((wG_laws E r X g bas idx n hs hn 1 hone φ hφ).2.2.1 ψ hψ).2.2 x hxd ?_
    funext z
    obtain ⟨v, rfl⟩ := L.surjective z
    have h1 := congrFun h v
    rw [thR, thR, ← hL] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1
  · funext v
    simp only [thR, UnAct.thA_add idx hs hxd hφ hψ, Pi.add_apply, mul_add]
  · funext v
    simp only [thR, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

end GlobalTheory.Ker
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNormAndOverlapBound
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNormAndOverlapBound
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.PhiNorm

section Product

variable {κ ι α : Type} [Fintype κ] [Fintype ι]

theorem sum_left (s : Finset α) (f : α → Matrix κ ι ℚ → ℂ) {ψ : Matrix κ ι ℚ → ℂ}
    (hs : ∀ a ∈ s, IsSB (f a)) (h' : IsSB ψ) :
    IsSB (∑ a ∈ s, f a) ∧ SW.ip (∑ a ∈ s, f a) ψ = ∑ a ∈ s, SW.ip (f a) ψ := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨isSB_zero, ?_⟩
    have := TensVac.ip_smul_left 0 h' h'
    simpa using this
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun φ hφ => hs φ (Finset.mem_insert_of_mem hφ)
    have h3 := hs a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, TensVac.ip_add_left h3 h1 h', h2]
    exact ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ h3 h1).1, rfl⟩

theorem ip_sum_diag (s : Finset α) (f f' : α → Matrix κ ι ℚ → ℂ) (hf : ∀ a ∈ s, IsSB (f a))
    (hf' : ∀ a ∈ s, IsSB (f' a)) (h : ∀ a ∈ s, ∀ b ∈ s, SW.ip (f a) (f' b) ≠ 0 → a = b) :
    SW.ip (∑ a ∈ s, f a) (∑ a ∈ s, f' a) = ∑ a ∈ s, SW.ip (f a) (f' a) := by
  rw [(sum_left s f hf (sum_left s f' hf' isSB_zero).1).2]
  refine Finset.sum_congr rfl fun a ha => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [TensVac.ip_conj (sum_left s f' hf' isSB_zero).1 (hf a ha), (sum_left s f' hf' (hf a ha)).2,
    map_sum, Finset.sum_eq_single_of_mem a ha, ← TensVac.ip_conj (hf' a ha) (hf a ha)]
  intro b hb hba
  rw [← TensVac.ip_conj (hf' b hb) (hf a ha)]
  by_contra h0
  exact hba (h a ha b hb h0).symm

end Product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem pair_int (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    {v v' : TF n g} (hv : IsSB v) (hv' : IsSB v') {δ y y' : Matrix (Fin n) (Fin r) E}
    (h : epsW X w δ • heisG X bas δ v = v) (h' : epsW X w δ • heisG X bas δ v' = v')
    (h0 : SW.ip (heisG X bas y v) (heisG X bas y' v') ≠ 0) :
    ∃ k : ℤ, ∑ i, EF X (δ i) ((y - y') i) = k := by
  have H := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have key : ∀ (y : Matrix (Fin n) (Fin r) E) (v : TF n g), IsSB v →
      epsW X w δ • heisG X bas δ v = v → epsW X w δ • heisG X bas δ (heisG X bas y v) =
        cexp (-(2 * π * I * ((∑ k, EF X (δ k) (y k) : ℚ) : ℂ))) • heisG X bas y v := by
    intro y v hv h
    have e : heisG X bas δ (heisG X bas y v) =
        cexp (-(2 * π * I * ((∑ k, EF X (δ k) (y k) : ℚ) : ℂ))) •
          heisG X bas y (heisG X bas δ v) := by
      rw [(H δ v hv).2.2.1 y, (H y v hv).2.2.1 δ, smul_smul, ← Complex.exp_add, add_comm y,
        TensVac.sumEF_swap hs δ y]
      congr 2
      push_cast
      ring
    rw [e, smul_comm, ← TensVac.heisG_smul, h]
  have h1 := (H y v hv).1
  have h2 := (H y' v' hv').1
  have h3 := (H δ _ h1).2.2.2.1 _ h2
  have h4 : SW.ip (epsW X w δ • heisG X bas δ (heisG X bas y v))
      (epsW X w δ • heisG X bas δ (heisG X bas y' v')) =
      SW.ip (heisG X bas y v) (heisG X bas y' v') := by
    rw [TensVac.ip_smul_left _ (H δ _ h1).1 (TensVac.sb_smul _ (H δ _ h2).1),
      TensVac.ip_smul_right _ (H δ _ h1).1 (H δ _ h2).1, ← mul_assoc, TensVac.epsW_mul_conj,
      one_mul, h3]
  rw [key y v hv h, key y' v' hv' h', TensVac.ip_smul_left _ h1 (TensVac.sb_smul _ h2),
    TensVac.ip_smul_right _ h1 h2, ← mul_assoc, mul_left_eq_self₀, or_iff_left h0,
    ← Complex.exp_conj, ← Complex.exp_add, Complex.exp_eq_one_iff] at h4
  obtain ⟨k, hk⟩ := h4
  refine ⟨-k, ?_⟩
  have e : ∑ i, EF X (δ i) ((y - y') i) = ∑ i, EF X (δ i) (y i) - ∑ i, EF X (δ i) (y' i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (y - y') i = y i - y' i := rfl
    simp only [TensLat.EF_eq_bilin, this, map_sub]
  rw [e]
  simp only [map_neg, map_mul, conj_ofReal, conj_I, map_ratCast, map_ofNat] at hk
  have hπ : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  apply Rat.cast_injective (α := ℂ)
  apply mul_left_cancel₀ hπ
  push_cast at hk ⊢
  linear_combination -hk

theorem coprime_cc {𝔪 : Ideal (𝓞 E)} {t t' : 𝓞 E} (ht : (t' : E) = cc (t : E))
    (h : IsCoprime (Ideal.span {t}) (conjI 𝔪)) : IsCoprime (Ideal.span {t'}) 𝔪 := by
  let c : 𝓞 E → 𝓞 E := fun a => ⟨cc (a : E), Base.isIntegral_cc a.isIntegral_coe⟩
  have hc : ∀ a, ((c a : 𝓞 E) : E) = cc (a : E) := fun _ => rfl
  have hm : ∀ m ∈ conjI 𝔪, c m ∈ 𝔪 := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, e⟩ := hx
      have : c x = b := by ext; rw [hc, e]; simp [cc]
      rwa [this]
    | zero =>
      have : c 0 = 0 := by ext; rw [hc]; simp [cc]
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : c (x + y) = c x + c y := by ext; push_cast; simp [hc, cc]
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : c (a • x) = c a * c x := by ext; push_cast; simp [hc, cc]
      rw [this]; exact Ideal.mul_mem_left _ _ hx
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  refine Ideal.isCoprime_iff_exists.2 ⟨c u * t', Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, c b,
    hm b hb, ?_⟩
  have := congrArg (fun a : 𝓞 E => cc (a : E)) hab
  ext
  push_cast at this ⊢
  simpa [hc, ht, cc] using this


omit [IsCMField E] in
theorem smul_mem_smul {𝔪 : Ideal (𝓞 E)} {L L' : Lt E r} {t : 𝓞 E} (h : ∀ v ∈ L, t • v ∈ L')
    {v : Fin r → E} (hv : v ∈ 𝔪 • L) : t • v ∈ 𝔪 • L' := by
  refine Submodule.smul_induction_on hv (fun a ha u hu => ?_) fun a b ha hb => ?_
  · rw [smul_comm]; exact Submodule.smul_mem_smul ha (h u hu)
  · rw [smul_add]; exact add_mem ha hb

theorem cong_of_pair (D : Level X) {M : ℕ} (hM : (M : 𝓞 E) ∈ D.𝔪) {L L' : Lt E r}
    (hL : L ∈ D.lats) (hL' : L' ∈ D.lats) (hS : SelfD X (D.sh L)) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) {y y' : Matrix (Fin n) (Fin r) E}
    (h : ∀ δ ∈ tens Λ (D.sh L), δ ∈ tens Λ (D.sh L') →
      ∃ k : ℤ, ∑ i, EF X (δ i) ((y - y') i) = k) (k : Fin n) : Cong X D.𝔪 (y k) (y' k) := by
  obtain ⟨-, s, hs, hs1, -⟩ := hL
  obtain ⟨-, s', hs', -, hs2⟩ := hL'
  obtain ⟨N, -, hN, -, hN2⟩ := hΛ.2.2
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 D.cop
  let t : 𝓞 E := ⟨cc ((s' * s : 𝓞 E) : E), Base.isIntegral_cc (s' * s).isIntegral_coe⟩
  have ht : (t : E) = cc ((s' * s : 𝓞 E) : E) := rfl
  have h1 : ∀ v ∈ D.sh L, (s' * s) • v ∈ D.sh L' := fun v hv c hc => by
    rw [smul_comm]
    exact smul_mem_smul (fun u hu => by rw [mul_smul]; exact hs2 _ (hs1 u hu)) (hv c hc)
  have hctr : ∀ (c : E) (d : Matrix (Fin n) (Fin r) E) (v : Fin n → E),
      TensLat.ctr (c • d) v = c • TensLat.ctr d v := fun c d v => by
    funext j
    simp [TensLat.ctr, Finset.sum_apply, Finset.mul_sum, mul_left_comm]
  have h2 : (t : E) • (y - y') ∈ tens Λ (D.sh L) := by
    refine (TensLat.tens_selfDual hΛ hS _).2 fun δ hδ => ?_
    obtain ⟨m, hm⟩ := h (((s' * s : 𝓞 E) : E) • δ)
      (TensLat.smul_mem_tens hΛ (s' * s).isIntegral_coe hδ) (by
        rw [TensLat.mem_tens_iff hΛ] at hδ ⊢
        intro v hv
        rw [hctr]
        exact h1 _ (hδ v hv))
    refine ⟨-m, ?_⟩
    rw [Int.cast_neg, ← hm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensLat.EF_swap]
    exact congrArg Neg.neg (TensLat.EF_smul X _ _ _).symm
  have h3 := (TensLat.mem_tens_iff hΛ _ _).1 h2 _
    (hN2 (Pi.single k 1) (Submodule.subset_span ⟨k, rfl⟩))
  have h4 : TensLat.ctr ((t : E) • (y - y')) ((N : E) • (Pi.single k 1 : Fin n → E)) =
      ((N : 𝓞 E) * t) • (y k - y' k) := by
    rw [TensLat.ctr, Finset.sum_eq_single k]
    · funext j
      change _ = (((N : 𝓞 E) * t : 𝓞 E) : E) * (y k j - y' k j)
      simp [cc, mul_assoc, Algebra.smul_def]
    · intro j _ hj; simp [hj, cc]
    · simp
  rw [h4] at h3
  refine ⟨s * (b * (N * t)), ?_, ?_⟩
  · simp only [← Ideal.span_singleton_mul_span_singleton]
    refine hs.of_mul_right_left.mul_left (IsCoprime.mul_left ?_ (IsCoprime.mul_left ?_ ?_))
    · exact Ideal.isCoprime_iff_exists.2 ⟨b, Ideal.mem_span_singleton_self b, a, ha,
        (add_comm _ _).trans hab⟩
    · obtain ⟨p, q, hpq⟩ : IsCoprime (N : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 hN
      refine Ideal.isCoprime_iff_exists.2 ⟨p * N, Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, q * M,
        Ideal.mul_mem_left _ _ hM, ?_⟩
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hpq
    · refine coprime_cc ht ?_
      rw [← Ideal.span_singleton_mul_span_singleton]
      exact hs'.of_mul_right_right.mul_left hs.of_mul_right_right
  · rw [mul_smul, mul_smul]
    exact smul_mem_smul hs1 (h3 b hb)

theorem eq_rpow {a : ℝ} {m n : ℕ} (ha : 0 ≤ a) (h : ((m ^ n : ℕ) : ℝ) * a ^ 2 = 1) :
    a = (m : ℝ) ^ (-(n : ℝ) / 2) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rw [← pow_left_inj₀ ha (Real.rpow_nonneg hm _) two_ne_zero, ← Real.rpow_natCast (_ ^ _),
    ← Real.rpow_mul hm, show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring,
    Real.rpow_neg hm, Real.rpow_natCast]
  exact eq_inv_of_mul_eq_one_right (by exact_mod_cast h)

theorem phi_norm_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L Λ) = (Nat.card D.J : ℂ) ∧ ∀ L' ∈ D.lats, ‖SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ)‖ ≤ (Nat.card D.J : ℝ) * (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2) := by
  intro E _ _ _ r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀ L hL Λ hΛ
  have H := (heisG_laws E r X g bas idx n hs hev).2.2.2
  have P := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀
  have Lv := (GlobalTheory.T.level_structure_properties E r X g bas idx n hs hev D hn).2.2.2.1
  have hv := (P L hL Λ hΛ).2.1
  have main : ∀ L' ∈ D.lats, SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ) =
      (Nat.card D.J : ℂ) * SW.ip (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)))
        (unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L'))) := by
    intro L' hL'
    have hv' := (P L' hL' Λ hΛ).2.1
    obtain ⟨s, hcard, hsy, e, e'⟩ := (P L hL Λ hΛ).2.2.1 L' hL'
    rw [e, e', ip_sum_diag s _ _ (fun y _ => TensVac.sb_smul _ (H y _ hv.1).1)
      (fun y _ => TensVac.sb_smul _ (H y _ hv'.1).1), ← hcard, ← nsmul_eq_mul,
      ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [TensVac.ip_smul_left _ (H y _ hv.1).1 (TensVac.sb_smul _ (H y _ hv'.1).1),
        TensVac.ip_smul_right _ (H y _ hv.1).1 (H y _ hv'.1).1, ← mul_assoc, Complex.mul_conj',
        (hsy y hy).2.1, (H y _ hv.1).2.2.2.1 _ hv'.1]
      simp
    · intro y hy y' hy' h0
      rw [TensVac.ip_smul_left _ (H y _ hv.1).1 (TensVac.sb_smul _ (H y' _ hv'.1).1),
        TensVac.ip_smul_right _ (H y _ hv.1).1 (H y' _ hv'.1).1] at h0
      refine (hsy y hy).2.2 y' hy' (cong_of_pair D hM hL hL' (Lv L hL).1 hΛ fun δ hδ hδ' => ?_)
      exact pair_int idx hs hev hv.1 hv'.1 (hv.2.2 δ hδ) (hv'.2.2 δ hδ')
        (right_ne_zero_of_mul (right_ne_zero_of_mul h0))
  refine ⟨by rw [main L hL, hv.2.1, mul_one], fun L' hL' => ?_⟩
  have hv' := (P L' hL' Λ hΛ).2.1
  have h1 := (TensVac.vacua E r X g bas idx n hs hev D.w D.w_int D.w_tr _ (Lv L hL).1 M Λ
    hΛ).2.2.2 _ (Lv L' hL').1 Λ hΛ _ _ hv hv'
  rw [((TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hev D.w D.w_int D.w_tr _
    (Lv L hL).1 M Λ hΛ).2.2.2.2.1 _ (Lv L' hL').1).1, (Lv L hL).2.2.1 L' hL'] at h1
  rw [main L' hL', norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
  exact eq_rpow (norm_nonneg _) h1

end GlobalTheory.SW.PhiNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNormAndOverlapBoundStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTestFunction_norm_and_overlap_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L Λ) = (Nat.card D.J : ℂ) ∧ ∀ L' ∈ D.lats, ‖ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ)‖ ≤ (Nat.card D.J : ℝ) * (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2) := by
  first | exact @GlobalTheory.SW.PhiNorm.phi_norm_overlap | exact GlobalTheory.SW.PhiNorm.phi_norm_overlap | (intros; apply GlobalTheory.SW.PhiNorm.phi_norm_overlap <;> assumption)
end
end
