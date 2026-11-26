module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MultiplierSqMulDetUnitaryColumnChange
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootsLevelPointsSameVacuumTranslates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnFibAllPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding relab
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Dict

theorem perFr_castFr_of_sameSp {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r}
    (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X' x v τ i = Formalism.L2.PjFree.perFr X (castFr h.psi x) v τ i := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X'
  cases X
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem exists_anFib_all_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ n : ℕ, Even n → ∃ s : c.F →+* ℂ, letI : Algebra c.F ℂ := s.toAlgebra; ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)), IsSympl X bas ∧ r = Dw.p + Dw.q ∧ (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧ (∀ j, rowType X (idx j) = relab c s (e j).1) ∧ ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r), FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀) := by
  intro E _ _ _ H Dw l Xo c h1 n hn
  obtain ⟨ξ, hξ, hξ0, hneg⟩ := GlobalTheory.SpanInhab.exists_imag_neg H
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ)
    (by rw [show cc (-ξ) = -cc ξ by simp [cc], hξ]) (neg_ne_zero.2 hξ0) _ rfl
  have hσ : Formalism.L2.PjFree.GoodEmb c c.F.val.toRingHom := rfl
  generalize c.F.val.toRingHom = σ at hσ
  obtain ⟨U, hU, -, ⟨k₀⟩, -, hG, -⟩ :=
    GlobalTheory.FrameUnif.exists_unf_hasPrinc E H Dw l Xo c σ _ ξ Gm φ h1 hσ hξ hneg hφ
  obtain ⟨W⟩ := nonempty_uw hU
  have huw := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ _ U hσ hU h1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k).1.trans (hG k₀).1.symm,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k).2.trans (hG k₀).2.symm,
      by rw [(huw k).1, (huw k₀).1, (hG k).2, (hG k₀).2]⟩
  have hdom : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) n := ⟨fun _ => antitone_const, hn⟩
  choose Dc hDe using fun k => GlobalTheory.Dict.exists_dic E H Dw l c σ _ W.g n (U.X k) (fun _ => 0) W.e hσ rfl
    (hU.2.1 k).1 (hU.2.1 k).2 (huw k).2.1 hdom
  have hper : ∀ k x v j, pv (U.X k) (Dc k).idx x v j =
      Formalism.L2.PjFree.perFr (U.X k) x v (relab c σ (W.e j).1) (W.e j).2 := fun k x v j => by
    rw [(Dc k).per_eq, (hDe k).1]
  have hty : ∀ k j, rowType (U.X k) ((Dc k).idx j) = relab c σ (W.e j).1 := fun k j => by
    rw [(Dc k).ty_eq, (hDe k).1]
  refine ⟨σ, _, W.g, U.X k₀, (Dc k₀).bas, (Dc k₀).idx, W.e, (Dc k₀).hr, (Dc k₀).eL, (Dc k₀).sympl, rfl,
    fun ℓ => ?_, hty k₀, fun y => ?_⟩
  · rw [(Dc k₀).dir_eq, (hDe k₀).1]
  · let _ : Algebra c.F ℂ := σ.toAlgebra
    obtain ⟨k, x, t, hx, ht⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ _ U hσ hU).2 y
    obtain ⟨A, -⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ _ U hσ hU h1 W k (Dc k).bas (Dc k).idx (Dc k).sympl
      (hper k) (hty k) x hx
    obtain ⟨e1, -, e2, A', -⟩ := GlobalTheory.Dict.anFib_move E H Dw l Xo c _ W.g (U.X k) (U.X k₀) (hsame k)
      (Dc k).bas (Dc k).idx (Dc k₀).bas (Dc k₀).idx W.e x.1 (U.X k).Λ (unC U k x) A 1 (Dc k).sympl (Dc k₀).sympl
      x.2 (huw k).2.1 (by simp [IsUn])
      (fun v => funext fun j => by rw [hper, hper, perFr_castFr_of_sameSp (hsame k)])
      (fun j => by rw [hty, hty])
    exact ⟨unC U k x, t, _, _, ht, e1, e2, ⟨A'⟩⟩

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostIdempotentTraceEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivLetterPushforwardEqColumnAction
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivLetterPushforwardEqColumnAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding relab
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence


open GlobalTheory.Dict.ColPoly in
theorem GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (s : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = relab c s (e j).1) → ∀ (h : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) (F : (Fin n → Fin g → ℂ) → ℂ), AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h P))) (letterDir X hr idx) F 0 = I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s P)) (letterDir X hr idx) (fun z => F (Dict.hAct X idx h z)) 0 := by
  intro E _ _ _ H Dw l c s r g X idx e q0 n hr eL hdir htype h P F hF
  have hF' : ContDiff ℂ (⊤ : ℕ∞) F := hF.contDiff
  let a : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → ℂ := fun v k =>
    s (Formalism.L2.Pj.embF c (eL.symm v).1 (h k (eL.symm v).2.2))
  let j : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → Harm.Var X.Ψ q0 X.p0 (Fin n) := fun v k =>
    eL ⟨(eL.symm v).1, (eL.symm v).2.1, k⟩
  let Φ : MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ :=
    MvPolynomial.aeval fun v => ∑ k, MvPolynomial.C (a v k) * MvPolynomial.X (j v k)
  have ha : ∀ v k, a (eL v) k = s (Formalism.L2.Pj.embF c v.1 (h k v.2.2)) := fun v k => by
    simp only [a]; rw [Equiv.symm_apply_apply]
  have hj : ∀ v k, j (eL v) k = eL ⟨v.1, v.2.1, k⟩ := fun v k => by
    simp only [j]; rw [Equiv.symm_apply_apply]
  have hΦ : ∀ Q : MvPolynomial (LtN Dw n) c.F,
      MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h Q)) =
        Φ (MvPolynomial.rename eL (MvPolynomial.map s Q)) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C x => simp
    | add P Q hP hQ => simp only [map_add (f := _), hP, hQ]
    | mul_X P v hP =>
      simp only [map_mul, hP]
      congr 1
      simp [pushLet, letB, Φ, ha, hj]
  rw [hΦ, ColPoly.polyDeriv_subst hF' a j Φ (fun v => by simp [Φ])]
  refine Eq.symm ((polyDeriv_comp_linear hF' (hActL X idx h) _ _ 0).trans ?_)
  rw [map_zero]
  congr 1
  funext v k i
  obtain ⟨⟨τ, ρ, b⟩, rfl⟩ := eL.surjective v
  change Dict.hAct X idx h _ k i = _
  simp only [Dict.hAct, ha, hj, hdir, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b (fun l _ hl => by simp [hl]) (by simp),
    Finset.sum_eq_single k (fun l _ hl => by simp [hl.symm]) (by simp)]
  by_cases hi : i = e.symm ⟨τ, ρ⟩
  · subst hi
    simp only [htype, Equiv.apply_symm_apply, Pi.single_eq_same]
    rfl
  · simp [hi]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivLetterPushforwardEqColumnActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding relab
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (s : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = relab c s (e j).1) → ∀ (h : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) (F : (Fin n → Fin g → ℂ) → ℂ), AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h P))) (letterDir X hr idx) F 0 = I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s P)) (letterDir X hr idx) (fun z => F (Dict.hAct X idx h z)) 0 := by
  first | exact @GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct | exact GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct | (intros; apply GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding relab
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.ChangePt

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem cmHost_idempotent_trace_eq_one (H : Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hs]; simp
    have hre : (τ (H.rt : E)).re = 0 := by
      have a1 := congrArg Complex.re h1
      have a2 := congrArg Complex.im h1
      simp [pow_two] at a1 a2
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      by_contra hne
      have : (τ (H.rt : E)).im = 0 := by
        have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at a1
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    rw [cc, IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hre]
  have h3 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    simpa [cc, map_ofNat] using this
  have : 2 * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h2 + h3 + hc
  exact mul_left_cancel₀ two_ne_zero this

theorem finite_levQ {H : Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem mem_vset (Λ : GenLat E n) {M : ℕ} (hM : 3 ≤ M) (hU : Λ.Unimod) (hT : Λ.TrivAt M) :
    Λ.La ∈ Vset E n M := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  rw [GenLatCmp.std_eq, GenLatCmp.span_smul_le] at h1 h2
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      omega
    · exact hk0
  exact ⟨GenLatCmp.fg_of_smul_le hk0 h1, (GenLatCmp.unimod_iff Λ.La).1 hU, k, hk0, hk, h1, h2⟩

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  induction s using Finset.induction_on with
  | empty => simpa using UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact UnAct.thA_add idx hs hx (hf a) (RecSum.isSB_sum s f hf)

theorem theta_sum₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (W : T → ℂ) (f : T → TF n g) (hf : ∀ i, IsSB (f i))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ i ∈ s, W i • f i) P x = ∑ i ∈ s, W i * thP X hr bas idx (f i) P x := by
  unfold thP
  rw [← Jet.polyDeriv_sum_fun P _ s W _ fun i _ => ThetaHol.differentiable_thA idx hs (hf i) hx,
    thA_sum idx hs hx s _ fun i => TensVac.sb_smul _ (hf i)]
  congr 1
  funext w
  simp only [UnAct.thA_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem theta_finsum (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {T : Type} [Fintype T] (W : T → ℂ)
    (Y : T → Matrix (Fin n) (Fin r) E) (a : ℂ) {u : TF n g} (hu : IsSB u)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ᶠ q, W q • heisG X bas (Y q) (a • u)) P x =
      a * ∑ q, W q * thP X hr bas idx (heisG X bas (Y q) u) P x := by
  have h1 (q) : W q • heisG X bas (Y q) (a • u) = (a * W q) • heisG X bas (Y q) u := by
    funext t
    simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [h1]
  rw [finsum_eq_sum_of_fintype, theta_sum₂ hr idx hs hx _ _ _
    fun q => ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu).1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => _root_.mul_assoc _ _ _


omit [IsCMField E] in
theorem index_Ln (Λ : GenLat E n) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      (stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup := by
  rw [← GenLatCmp.std_eq, ← AddSubgroup.inf_relIndex_left]
  rfl


omit [IsCMField E] in
theorem zCard_eq (Λ : GenLat E n) {N M : ℕ} (hN : Λ.LevOK N M) (r : ℕ) :
    Λ.zCard N r = Λ.mIdx N r * ((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) ^ r := by
  rw [← index_Ln Λ, GenLat.zCard, GenLat.mIdx, ← mul_pow]
  congr 1
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hN.2.2)
    (Submodule.toAddSubgroup_mono (inf_le_left : Λ.Ln ≤ Λ.La))).symm

end Classical

theorem cancel_idx {b κ S Q : ℂ} {m z j : ℕ} (hb : b ≠ 0) (hz0 : 0 < z) (hz : z = m * j) :
    b⁻¹ * (m : ℂ)⁻¹ * Q * (z : ℂ) * κ * ((((Real.sqrt (j : ℝ) : ℝ) : ℂ))⁻¹ * S) * b =
      Q * κ * S * ((Real.sqrt (j : ℝ) : ℝ) : ℂ) := by
  subst hz
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right hz0).ne'
  have hj : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_mul_pos_left hz0
  have hs : ((Real.sqrt (j : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hj).ne'
  have h2 : (j : ℂ) = ((Real.sqrt (j : ℝ) : ℝ) : ℂ) * ((Real.sqrt (j : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hj.le).symm
  rw [Nat.cast_mul]
  generalize ((Real.sqrt (j : ℝ) : ℝ) : ℂ) = s at hs h2
  rw [h2]
  field_simp

theorem change_at_point : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), IsSympl X bas → r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E), Λ.Unimod → IsUnitaryM h → Λ.TrivAt l.M → (actLat h Λ).TrivAt l.M → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (_ : AnFib X bas idx e x L y), x ∈ X.dom → SelfD X L → IsMu (t ^ 2 * ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ) ∧ ∀ (wq : (Fin n → LevQ Dw l) → c.F), FixesDatum c h wq → ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (b b' : c.F) (v v' : ℂ), b ≠ 0 → b' ≠ 0 → ShortValAt Xo c nab wq Λ b N P y v → ShortValAt Xo c nab wq (actLat h Λ) b' N' (pushLet c h P) y v' → v' * algebraMap c.F ℂ b' * (Real.sqrt (((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) = t * algebraMap c.F ℂ b * (Real.sqrt (((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) * v := by
  intro hci E _ _ _ H Dw l Xo c _ r g X bas idx e q0 n hr eL hs hrr hn hdir hty _ nab hnab Λ h hU hh hT hT'
  have hw := cmHost_idempotent_trace_eq_one H
  have hwi : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨hU', hmv, hu, -⟩ := (GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n 0 h hh).2 Λ
  have hΛ := mem_vset Λ l.three_le hU hT
  have hΛ' := mem_vset (actLat h Λ) l.three_le (hU' hU) hT'
  have hΛ1 : Λ.La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ
  have hΛ1' : (actLat h Λ).La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ'
  obtain ⟨t, ht, hvac⟩ := thA_vacuum_hAct E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' hmv
  refine ⟨t, ht, fun x L y A hx hL => ?_⟩
  obtain ⟨⟨v₀, hv₀⟩, -⟩ := TensVac.vacua E r X g bas idx n hs hn _ hwi hw L hL 1 _ (Base.stdL_mem_Vset n 1)
  have hcol := hvac L hL v₀ hv₀ x hx
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.T.multiplier_sq_mul_det_unitary_column_change E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' L hL v₀ hv₀ x hx t ht hcol
    have h2 : ∏ i : Fin g, rowType X (idx i) h.det =
        ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ := by
      simp only [hty]
      rw [e.prod_comp (fun ℓ : Lt1 Dw => Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) ℓ.1 h.det), Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun τ _ => ?_
      simp [Formalism.L2.PjFree.relab]
    rwa [h2] at h1
  intro wq hwq N N' hN hN' a P hP b b' v v' hb hb' hv hv'
  obtain ⟨θ, hθ, -⟩ := (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s).1
  have hθ1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀ x hx θ hθ1
  obtain ⟨mk, hmk, hA⟩ := exists_mark E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hroots := (DualMark.dual_marking E H Dw l r X L mk _ hL hmk
    (Complex.isPrimitiveRoot_exp _ l.odd.pos.ne')).2.2.2.2 n
  obtain ⟨Y, hY⟩ := hroots N hN.1.pos
  obtain ⟨Y', hY'⟩ := hroots N' hN'.1.pos
  have e1 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA Λ.La hΛ N hN Y hY a P hP wq b v hv
  have e2 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA (actLat h Λ).La hΛ' N' hN' Y' hY' a _
    ((GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n a h hh).1 P hP) wq b' v' hv'
  obtain ⟨_, -, hproj⟩ := GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀
  obtain ⟨hu1, -, hp1⟩ := hproj _ hΛ1
  obtain ⟨hu2, -, hp2⟩ := hproj _ hΛ1'
  obtain ⟨⟨σ, hσ⟩, hmove⟩ := GlobalTheory.T.roots_levelPoints_same_vacuum_translates E H Dw l r X g bas n hs hn L hL mk hmk h hu _ hΛ _ hΛ' hmv N N' hN hN'
    Y Y' hY hY'
  obtain ⟨-, -, -, hz1, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1 N hN.1
    (hN.2.2.trans inf_le_left)
  obtain ⟨-, -, -, hz2, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1' N' hN'.1
    (hN'.2.2.trans inf_le_left)
  haveI := finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  generalize unitv (projA X bas (H.w0 : E) (tens Λ.La L) v₀) = u at hcol hu1 hp1
  generalize unitv (projA X bas (H.w0 : E) (tens (actLat h Λ).La L) v₀) = u' at hcol hu2 hp2
  rw [gphi, hp1, theta_finsum hr idx hs hn hx _ _ _ hu1.1] at e1
  rw [gphi, hp2, theta_finsum hr idx hs hn hx _ _ _ hu2.1] at e2
  have hsum : ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y' q) u')
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) (pushLet c h P))) x =
      t * ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y q) u)
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
    rw [← σ.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsb := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu1.1).1
    have hsb' := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (h * Y q) u' hu2.1).1
    have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn 0 0 _ hsb' 0 (zero_mem _)).2.2.2 x hx
    rw [hwq q _ (hσ q), hmove q _ (hσ q) u' hu2, thP, thP,
      GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action E H Dw l c _ r g X idx e q0 n hr eL hdir hty h P _ han,
      funext (thA_heisG_hAct E r X g bas idx n hs hn h hu u u' hu1.1 hu2.1 t x hx hcol (Y q)),
      mul_left_comm t, ← Jet.polyDeriv_smul_fun _ _ (ThetaHol.differentiable_thA idx hs hsb hx)]
    rfl
  rw [hsum] at e2
  simp only [map_mul, map_inv₀, map_natCast] at e1 e2
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'
  rw [index_Ln, index_Ln, ← hrr, e2, cancel_idx hb0' hz2 (zCard_eq _ hN' r), mul_right_comm _ _ v,
    _root_.mul_assoc t, _root_.mul_comm _ v, e1, cancel_idx hb0 hz1 (zCard_eq _ hN r)]
  ring

end GlobalTheory.Phase.ChangePt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RatioMemRange
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfEqComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding relab
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.NaturalValues

theorem eq_of_points {K R Ω : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] [Algebra.FiniteType K R]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] {x y : R} (h : ∀ φ : R →ₐ[K] Ω, φ x = φ y) : x = y := by
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  rw [← sub_eq_zero]
  have hb : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance ((Ideal.isRadical_iff_quotient_reduced _).2
      (isReduced_of_injective (RingEquiv.quotientBot R) (RingEquiv.quotientBot R).injective))
  rw [← Ideal.mem_bot, ← hb]
  refine Ideal.mem_sInf.2 fun {m} hm => ?_
  haveI := hm.2
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  let ψ : (R ⧸ m) →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have e := h (ψ.comp (Ideal.Quotient.mkₐ K m))
  rw [← sub_eq_zero, ← map_sub, AlgHom.comp_apply, map_eq_zero] at e
  exact Ideal.Quotient.eq_zero_iff_mem.1 e

theorem eq_of_eq_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (s : c.F →+* ℂ) (u u' : ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → S), (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u S y) = u T z) → (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u' S y) = u' T z) → (∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra, @u ℂ _ s.toAlgebra y = @u' ℂ _ s.toAlgebra y) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), u S y = u' S y := by
  intro E _ _ _ H Dw l Xo c s u u' hu hu' hc S _ _ y
  have hF := GlobalTheory.RepCompare.frameLaws Xo c
  letI := s.toAlgebra
  refine eq_of_locM (K := c.F) fun m hm => ?_
  obtain ⟨A, v, cw, -, -, -, ⟨wm, h1, h2⟩, -⟩ := hF.cover S y y rfl m
  have e : u A.R v = u' A.R v := by
    refine eq_of_points (K := c.F) (Ω := ℂ) fun φ => ?_
    obtain ⟨z, hz⟩ := hF.bc _ _ φ v
    rw [hu _ _ φ v z hz, hu' _ _ φ v z hz]
    exact hc z
  rw [hu _ _ _ y wm h1, hu' _ _ _ y wm h1, ← hu _ _ cw v wm h2, ← hu' _ _ cw v wm h2, e]

end GlobalTheory.NaturalValues
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding relab
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.ConstRatio

theorem ratio_mem_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Type) [Field T] [IsAlgClosed T] [Algebra c.F T]
    (u u' : FrPt Xo c T → T)
    (hu : ∀ (φ : T →ₐ[c.F] T) (y z : FrPt Xo c T), FrMap φ y z → φ (u y) = u z)
    (hu' : ∀ (φ : T →ₐ[c.F] T) (y z : FrPt Xo c T), FrMap φ y z → φ (u' y) = u' z)
    (z : T) (h : ∀ y, u' y = z * u y) (y : FrPt Xo c T) (hy : u y ≠ 0) :
    z ∈ Set.range (algebraMap c.F T) := by
  refine GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv z fun σ => ?_
  obtain ⟨y', hy'⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T T σ.toAlgHom y
  have h1 := hu _ _ _ hy'
  have h2 := hu' _ _ _ hy'
  rw [h y, h y', map_mul, ← h1] at h2
  have hne : σ.toAlgHom (u y) ≠ 0 := by
    simpa using hy
  exact mul_right_cancel₀ hne h2

theorem exists_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (s : c.F →+* ℂ) (J : Type) (u u' : J → ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → S), (∀ j, (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u j S y) = u j T z)) → (∀ j, (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u' j S y) = u' j T z)) → ∀ z : ℂ, IsMu z → (∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra), @u' j ℂ _ s.toAlgebra y = z * @u j ℂ _ s.toAlgebra y) → ∃ z₀ : c.F, (∃ k : ℕ, 0 < k ∧ z₀ ^ k = 1) ∧ ∀ j (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), u' j S y = algebraMap c.F S z₀ * u j S y := by
  intro E _ _ _ H Dw l Xo c s J u u' hu hu' z hz h
  have key : ∃ z₀ : c.F, (∃ k : ℕ, 0 < k ∧ z₀ ^ k = 1) ∧
      ∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra),
        @u' j ℂ _ s.toAlgebra y = s z₀ * @u j ℂ _ s.toAlgebra y := by
    by_cases h0 : ∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra), @u j ℂ _ s.toAlgebra y = 0
    · refine ⟨1, ⟨1, one_pos, one_pow 1⟩, fun j y => ?_⟩
      rw [h j y, h0 j y, mul_zero, mul_zero]
    · simp only [not_forall] at h0
      obtain ⟨j, y, hy⟩ := h0
      obtain ⟨z₀, hz₀⟩ := @ratio_mem_range E _ _ _ H Dw l Xo c ℂ _ _ s.toAlgebra
        (@u j ℂ _ s.toAlgebra) (@u' j ℂ _ s.toAlgebra)
        (@hu j ℂ ℂ _ s.toAlgebra _ s.toAlgebra) (@hu' j ℂ ℂ _ s.toAlgebra _ s.toAlgebra) z (h j) y hy
      have hz₀' : s z₀ = z := hz₀
      obtain ⟨m, hm, hzm⟩ := hz
      refine ⟨z₀, ⟨m, hm, s.injective ?_⟩, fun j y => ?_⟩
      · rw [map_pow, hz₀', hzm, map_one]
      · rw [hz₀', h j y]
  obtain ⟨z₀, hk, hz₀⟩ := key
  refine ⟨z₀, hk, fun j => ?_⟩
  refine GlobalTheory.NaturalValues.eq_of_eq_complex E H Dw l Xo c s (u' j) (fun S _ _ y => algebraMap c.F S z₀ * u j S y) (hu' j) ?_ ?_
  · intro S T _ _ _ _ φ y y' hyy
    rw [map_mul, φ.commutes, hu j S T φ y y' hyy]
  · intro y
    exact hz₀ j y

end GlobalTheory.ConstRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReflexNormMulConj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding relab
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

noncomputable section

namespace GlobalTheory.BetaChange

open GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.LatticeBetaCompare GlobalTheory.SW.Nbr
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem form_adj (h : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * h.mulVec w j =
      ∑ j, IsCMField.complexConj E ((adjM h).mulVec v j) * w j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, adjM, Matrix.of_apply, map_sum, map_mul,
    IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem unimod_act {h : Matrix (Fin n) (Fin n) E} (hu : IsUnitaryM h) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (actLat h Λ).Unimod := by
  have h1 : adjM h * h = 1 := hu
  have h2 : h * adjM h = 1 := mul_eq_one_comm.1 h1
  intro v
  have e : v ∈ (actLat h Λ).La ↔ (adjM h).mulVec v ∈ Λ.La := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (adjM h).mulVec (h.mulVec u) ∈ _
      rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    · intro hv
      refine ⟨_, hv, ?_⟩
      change h.mulVec _ = _
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e, hΛ]
  constructor
  · rintro hv _ ⟨u, hu, rfl⟩
    exact (form_adj h v u).symm ▸ hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ⟨w, hw, rfl⟩

variable {H : Host E} (Dw : Datum H) {l : Geo.Tor.Level H} (c : Coeff l)

theorem reflexNorm_mul_conj (g : 𝓞 E) :
    reflexNorm Dw c ((g * co g : 𝓞 E) : E) = ((Ideal.absNorm (Ideal.span {g}) ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  have h := (isBe_principal Dw c g).2 c.F.val.toRingHom
  apply c.F.val.toRingHom.injective
  rw [map_natCast]
  have e : c.F.val.toRingHom (reflexNorm Dw c ((g * co g : 𝓞 E) : E)) =
      c.F.val.toRingHom (reflexNorm Dw c (g : E)) * conj (c.F.val.toRingHom (reflexNorm Dw c (g : E))) := by
    simp only [reflexNorm, map_prod, map_pow, ← Finset.prod_mul_distrib, ← mul_pow]
    refine Finset.prod_congr rfl fun σ _ => ?_
    congr 1
    change σ ((g : E) * IsCMField.complexConj E (g : E)) = σ g * conj (σ g)
    rw [map_mul, IsCMField.complexEmbedding_complexConj]
  rw [e, Complex.mul_conj', ← Complex.ofReal_pow, h]
  push_cast
  rfl

theorem isBe_mul_conj (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    IsBe Dw c (J * conjI J) ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  let I₀ : (Ideal (𝓞 E))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
  obtain ⟨k, hk, e⟩ := (isOfFinOrder_of_finite (ClassGroup.mk0 I₀)).exists_pow_eq_one
  rw [← map_pow] at e
  obtain ⟨g, hg⟩ : (J ^ k).IsPrincipal := (ClassGroup.mk0_eq_one_iff (I₀ ^ k).2).1 e
  change J ^ k = Ideal.span {g} at hg
  refine isBe_of_pow hk ?_
  have e1 : (J * conjI J) ^ k = Ideal.span {g * co g} := by
    rw [mul_pow, conjI_eq, ← Ideal.map_pow, hg, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  have e2 : ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) ^ k = reflexNorm Dw c ((g * co g : 𝓞 E) : E) := by
    rw [reflexNorm_mul_conj, ← hg, map_pow, ← Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k]
  rw [e1, e2]
  exact isBe_principal Dw c _

theorem isBe_of_isBeta {Λ : GenLat E n} (hΛ : Λ.Unimod) {b : c.F} (hb : IsBeta Dw c Λ b) {J : Ideal (𝓞 E)}
    (hN : Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index)
    (hJ : detSpan Λ.Ln = J • detSpan Λ.La) : IsBe Dw c J b := by
  have hu0 : IsUnit (detSpan Λ.La) :=
    isUnit_detSpan (GenusLatCompare.latEquiv.symm ⟨Λ, GenusLatCompare.isLat_of_unimod Λ hΛ⟩)
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ) :=
    IsUnit.prod_iff.2 fun τ _ => by rw [idealAt_eq]; exact (hu0.map _).pow _
  obtain ⟨-, h1, h2⟩ := hb
  refine ⟨?_, fun s => by rw [hN]; exact h2 s⟩
  have e : ∀ τ, idealAt c Λ.Ln τ =
      coeI c.F (J.map (RingOfIntegers.mapRingHom (embF c τ))) * idealAt c Λ.La τ := fun τ => by
    rw [idealAt_eq, idealAt_eq, hJ, smul_eq_coeI_mul, map_mul, extend_coeI]
  rw [← span_eq_coeI_iff, coeI_reflexIdeal]
  rw [BetaIs] at h1
  simp only [e, mul_pow, Finset.prod_mul_distrib] at h1
  exact hu.mul_left_inj.1 h1

omit [IsCMField E] in
theorem map_mulLeft_eq (x : E) (M : Submodule (𝓞 E) E) :
    Submodule.map (LinearMap.mulLeft (𝓞 E) x) M = Submodule.span (𝓞 E) {x} * M := by
  ext y
  rw [Submodule.mem_span_singleton_mul]
  rfl

omit [IsCMField E] in
theorem coeI_span (u : 𝓞 E) : coeI E (Ideal.span {u}) = Submodule.span (𝓞 E) {(u : E)} :=
  IsLocalization.coeSubmodule_span_singleton E u

theorem beta_sq_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (b b' : c.F), Λ.Unimod → IsUnitaryM h → IsBeta Dw c Λ b → IsBeta Dw c (actLat h Λ) b' → ∃ m : ℕ, 0 < m ∧ (b ^ 2 * ((((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F)) ^ m = (b' ^ 2 * ((((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F) * ∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) ^ m := by
  intro E _ _ _ H Dw l c n Λ h b b' hΛ hu hb hb'
  have hΛ' := unimod_act hu hΛ
  obtain ⟨J, hJ0, hN, hJ1, hJ2, hdet⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n Λ hΛ
  obtain ⟨J', hJ0', hN', hJ1', hJ2', -⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n _ hΛ'
  have hB := isBe_of_isBeta Dw c hΛ hb hN hJ1
  have hB' := isBe_of_isBeta Dw c hΛ' hb' hN' hJ1'
  obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := 𝓞 E) h.det
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hvE : (v : E) ≠ 0 := by simpa using hv0
  have huv' : (u : E) = h.det * (v : E) := by
    rw [← huv]; exact (div_mul_cancel₀ _ hvE).symm
  have k1 : coeI E (conjI J) = coeI E J * detSpan Λ.La := by
    rw [← smul_eq_coeI_mul]; exact hJ2.symm.trans hJ1
  have k2 : coeI E (conjI J') = coeI E J' * (Submodule.span (𝓞 E) {h.det} * detSpan Λ.La) := by
    rw [← smul_eq_coeI_mul, ← map_mulLeft_eq]
    exact (hJ2'.symm.trans hJ1').trans (by rw [hdet]; rfl)
  have key : conjI J' * J * Ideal.span {v} = conjI J * J' * Ideal.span {u} := by
    apply IsFractionRing.coeSubmodule_injective (𝓞 E) E
    change coeI E _ = coeI E _
    simp only [map_mul, k1, k2, coeI_span]
    rw [huv', ← Set.singleton_mul_singleton, ← Submodule.span_mul_span]
    ring
  have a1 := isBe_mul (isBe_mul (isBe_pow hB 2) (isBe_mul_conj Dw c J' hJ0')) (isBe_principal Dw c v)
  have a2 := isBe_mul (isBe_mul (isBe_pow hB' 2) (isBe_mul_conj Dw c J hJ0)) (isBe_principal Dw c u)
  have e : J' ^ 2 * (J * conjI J) * Ideal.span {u} = J ^ 2 * (J' * conjI J') * Ideal.span {v} := by
    calc _ = J * J' * (conjI J * J' * Ideal.span {u}) := by ring
      _ = _ := by rw [← key]; ring
  rw [e] at a2
  have hc : conjI J' ≠ ⊥ := fun h0 => hJ0' (by
    rw [← conjI_conjI J', h0, conjI_eq, Ideal.map_bot])
  have hs : Ideal.span {v} ≠ (⊥ : Ideal (𝓞 E)) := by simpa using hv0
  obtain ⟨z, hz, ez⟩ := isBe_unique
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hJ0) (mul_ne_zero hJ0' hc)) hs) a2 a1
  obtain ⟨m, hm, hzm⟩ := hz.exists_pow_eq_one
  have hψ : reflexNorm Dw c (v : E) ≠ 0 := isBe_ne_zero hs (isBe_principal Dw c v)
  have hψu : reflexNorm Dw c (u : E) = (∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) * reflexNorm Dw c (v : E) := by
    simp only [huv', reflexNorm, map_mul, mul_pow, Finset.prod_mul_distrib]
  rw [hψu, ← _root_.mul_assoc, ← _root_.mul_assoc, hN, hN'] at ez
  have ez' := mul_right_cancel₀ hψ ez
  refine ⟨m, hm, ?_⟩
  rw [ez', _root_.mul_assoc z, mul_pow z, hzm, _root_.one_mul]

end GlobalTheory.BetaChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaChangeOfRepRootOfUnityOfChartIndependence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding relab
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory

theorem changeRoot_scalar_isMu (t b b' D : ℂ) (A A' m : ℕ) (hb' : b' ≠ 0) (hA : A ≠ 0) (hm : 0 < m)
    (h1 : (b ^ 2 * (A' : ℂ)) ^ m = (b' ^ 2 * (A : ℂ) * D) ^ m) (h2 : IsMu (t ^ 2 * D)) :
    IsMu (t * b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) / (b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ))) := by
  obtain ⟨k, hk, h2⟩ := h2
  have e : ∀ B : ℕ, ((Real.sqrt (B : ℝ) : ℝ) : ℂ) ^ 2 = (B : ℂ) := fun B => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg B)]; simp
  have hA' : (A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hA
  refine ⟨2 * m * k, by positivity, ?_⟩
  have e2 : (t * b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) / (b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ))) ^ 2 =
      t ^ 2 * (b ^ 2 * (A' : ℂ)) / (b' ^ 2 * (A : ℂ)) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, e, e, _root_.mul_assoc]
  have hne : (b' ^ 2 * (A : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hb') hA')
  have e3 : (t ^ 2 * (b ^ 2 * (A' : ℂ)) / (b' ^ 2 * (A : ℂ))) ^ m = (t ^ 2 * D) ^ m := by
    rw [div_pow, mul_pow (t ^ 2), h1, mul_pow _ D, div_eq_iff hne, mul_pow (t ^ 2) D]; ring
  rw [pow_mul, pow_mul, e2, e3, ← pow_mul, mul_comm m k, pow_mul, h2, one_pow]

theorem changeRoot_complex (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ]
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (hfib : ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
      (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)),
      IsSympl X bas ∧ r = Dw.p + Dw.q ∧
      (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧
      (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) ∧
      ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r),
        FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀))
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (b b' : c.F) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (hb : IsBeta Dw c Λ b) (hb' : IsBeta Dw c (actLat h Λ) b') :
    ∃ z : ℂ, IsMu z ∧ ∀ (w : (Fin n → LevQ Dw l) → c.F), FixesDatum c h w →
      ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ),
      ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)),
      ∀ (y : FrPt Xo c ℂ) (v v' : ℂ), ShortValAt Xo c nab w Λ b N P y v →
        ShortValAt Xo c nab w (actLat h Λ) b' N' (pushLet c h P) y v' → v' = z * v := by
  obtain ⟨r, g, X, bas, idx, e, hr, eL, hS, hr', hL, hrow, hy⟩ := hfib
  by_cases hne : Nonempty (FrPt Xo c ℂ)
  swap
  · exact ⟨1, isMu_one, fun _ _ _ _ _ _ _ _ _ y => (hne ⟨y⟩).elim⟩
  obtain ⟨y1⟩ := hne
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨t, -, ht⟩ := GlobalTheory.Phase.ChangePt.change_at_point hC E H Dw l Xo c r g X bas idx e Dw.p n hr eL hS hr' hn hL hrow nab hnab
    Λ h hU hh hT hT'
  obtain ⟨m, hm, hbeta⟩ := GlobalTheory.BetaChange.beta_sq_compare E H Dw l c n Λ h b b' hU hh hb hb'
  obtain ⟨hP, hΛ⟩ : _ ∧ _ := ⟨fun a => (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1,
    ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU⟩
  set A := ((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) with hAdef
  set A' := ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q)
    with hA'def
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb.1
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'.1
  have hA : A ≠ 0 := by
    intro h0
    have h1 := hb.2.2 (algebraMap c.F ℂ)
    rw [← Nat.cast_pow, ← hAdef, h0, Nat.cast_zero, pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h1
    exact hb0 h1
  have hsq : ((Real.sqrt (A : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA))).ne'
  obtain ⟨y₀, t₀, x, L, -, hx, hSD, ⟨F⟩⟩ := hy y1
  have hmu := (ht x L y₀ F hx hSD).1
  have hbeta' := congrArg (algebraMap c.F ℂ) hbeta
  simp only [map_pow, map_mul, map_natCast, map_prod] at hbeta'
  refine ⟨_, changeRoot_scalar_isMu t _ _ _ A A' m hb0' hA hm hbeta' hmu, ?_⟩
  intro w hw N N' hN hN' a P hPa y v v' hv hv'
  obtain ⟨y₀, t₀, x, L, hB, hx, hSD, ⟨F⟩⟩ := hy y
  have ex1 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa w b).1 ℂ
  have ex2 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN' a _ (hP a P hPa) w b').1 ℂ
  obtain ⟨u, hu, -⟩ := ex1 y₀
  obtain ⟨u', hu', -⟩ := ex2 y₀
  have k1 := (ex1 y).unique hv
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a P).2 hPa w Λ b N u hu)
  have k2 := (ex2 y).unique hv'
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a _).2 (hP a P hPa) w _ b' N' u' hu')
  have k3 := (ht x L y₀ F hx hSD).2 w hw N N' hN hN' a P hPa b b' u u' hb.1 hb'.1 hu hu'
  have k4 : u' = t * algebraMap c.F ℂ b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) /
      (algebraMap c.F ℂ b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ)) * u := by
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hb0' hsq), ← _root_.mul_assoc]
    exact k3
  rw [k1, k2, k4]; ring

theorem changeRoot_of_chartIndep : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ), ChangeRoot Xo c nab n := by
  intro hC E _ _ _ H Dw l Xo c _ nab n hs bad hbad Λ h b b' hU hh hT hT' hb hb'
  obtain ⟨-, hodd, hn, hnab⟩ := hs
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  have triv : ∀ Λ : GenLat E n, Λ.TrivAt bad → Λ.TrivAt l.M := fun Λ ⟨k, hk, h1⟩ =>
    ⟨k, hk.coprime_dvd_right hbad.2.2.1, h1⟩
  have hT := triv _ hT
  have hT' := triv _ hT'
  obtain ⟨s, hfib⟩ := GlobalTheory.Dict.exists_anFib_all_points E H Dw l Xo c hodd.pos n hn
  obtain ⟨z, hz, hid⟩ := @changeRoot_complex hC E _ _ _ H Dw l Xo c s.toAlgebra _ nab hnab n hn hfib
    Λ h b b' hU hh hT hT' hb hb'
  have hP := fun a => (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  let J : Type := {p : ((Fin n → LevQ Dw l) → c.F) × ℕ × ℕ × ((E →+* ℂ) × ℕ → ℕ) × MvPolynomial (LtN Dw n) c.F //
    FixesDatum c h p.1 ∧ Λ.LevOK p.2.1 l.M ∧ (actLat h Λ).LevOK p.2.2.1 l.M ∧
      p.2.2.2.2 ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => p.2.2.2.1 (τ, i))}
  have ex1 := fun j : J => GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ j.1.2.1 hU hT j.2.2.1 j.1.2.2.2.1
    j.1.2.2.2.2 j.2.2.2.2 j.1.1 b
  have ex2 := fun j : J => GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) j.1.2.2.1 hΛ hT' j.2.2.2.1
    j.1.2.2.2.1 _ (hP _ _ j.2.2.2.2) j.1.1 b'
  choose u hu using fun (j : J) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => ((ex1 j).1 S y).exists
  choose u' hu' using fun (j : J) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => ((ex2 j).1 S y).exists
  obtain ⟨z₀, hz₀, hfin⟩ := GlobalTheory.ConstRatio.exists_ratio E H Dw l Xo c s J u u'
    (fun j S T _ _ _ _ φ y y' hy => (ex1 j).2 S T φ y y' hy _ _ (hu j S y) (hu j T y'))
    (fun j S T _ _ _ _ φ y y' hy => (ex2 j).2 S T φ y y' hy _ _ (hu' j S y) (hu' j T y')) z hz
    (fun j y => hid j.1.1 j.2.1 _ _ j.2.2.1 j.2.2.2.1 _ _ j.2.2.2.2 y _ _
      (@hu j ℂ _ s.toAlgebra y) (@hu' j ℂ _ s.toAlgebra y))
  refine ⟨z₀, hz₀, ?_⟩
  intro w hw N N' hN hN' a P hPa S _ _ y v v' hv hv'
  let j : J := ⟨(w, N, N', a, P), hw, hN, hN', hPa.1⟩
  rw [((ex1 j).1 S y).unique hv (hu j S y), ((ex2 j).1 S y).unique hv' (hu' j S y)]
  exact hfin j S y

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaChangeOfRepRootOfUnityOfChartIndependenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding relab
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChangeOfRepRootOfUnity_of_chartIndependence : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ), ChangeRoot Xo c nab n := by
  first | exact @GlobalTheory.changeRoot_of_chartIndep | exact GlobalTheory.changeRoot_of_chartIndep | (intros; apply GlobalTheory.changeRoot_of_chartIndep <;> assumption)
end
