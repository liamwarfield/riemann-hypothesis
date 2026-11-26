module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GphiEqSmulPhiF
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalTheta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassical
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassical
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

theorem evR_eq_clsSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A : AnFib X bas idx e x L y₂), FrOver d y₂ y → IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y₂.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ L mk → A.Marked mk → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), LatsOK d.l₂.M La Nc → (∀ k, io (xs k) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ Y : Cl → (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, (∀ k, IsRoots d.l₂ L mk (Nc k) (Y k)) → ∀ f : Rul Xo c, IsThClsD Xo c d w La Nc gam vol ep io xs f → evR Xo c f y = evR d.Xo₂ d.c₂ d.cδ y₂ * κ * clsSum (algebraMap c.F ℂ) X hr bas idx eL w La Nc gam vol ep (fun k => io (xs k)) L v Y x := by
  intro hCI E _ _ _ H Dw l Xo c n d _ _ hF ⟨inst, hnab⟩ r g X bas idx e x L y y₂ A hov hs hx hL q0 hr eL hr' hn
    hlet θ v κ hread hvac hκ mk hmk hA Cl _ w La Nc gam vol ep Vs _ _ io xs a hLa hH Y hY f hf
  obtain ⟨vc, hvc, hev⟩ := hf ℂ hF y y₂ hov
  have hcomp : (algebraMap d.c₂.F ℂ).comp (d.eF : c.F →+* d.c₂.F) = algebraMap c.F ℂ :=
    RingHom.ext fun t => hF t
  rw [hev, mul_assoc, clsSum, Finset.mul_sum _ _ κ]
  refine congrArg (fun t => evR d.Xo₂ d.c₂ d.cδ y₂ * t) (Finset.sum_congr rfl fun k _ => ?_)
  obtain ⟨h1, h2, h3⟩ := hLa k
  have hV : (La k).La ∈ Vset E n d.l₂.M :=
    (GlobalTheory.Dict.GenLatCmp.genLat_vset E n (La k).La).2.1 _ (Nc k) d.l₂.odd.pos h1 h2 h3
  have hP := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hH k)
  have h := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hCI E H Dw d.l₂ d.Xo₂ d.c₂ r g X bas idx e x L y₂ A hs hx hL q0 n hr eL hr' hn hlet
    d.nab₂ hnab θ v κ hread hvac hκ mk hmk hA (La k).La hV (Nc k) h3 (Y k) (hY k) a _ hP _ 1 (vc k) (hvc k)
  rw [h, MvPolynomial.map_map, hcomp]
  simp only [hF, map_mul, map_inv₀, map_natCast, inv_one, map_one]
  ring

end GlobalTheory.ClsVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassicalStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_eval_complex_point_eq_classical : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A : AnFib X bas idx e x L y₂), FrOver d y₂ y → IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y₂.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ L mk → A.Marked mk → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), LatsOK d.l₂.M La Nc → (∀ k, io (xs k) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ Y : Cl → (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, (∀ k, IsRoots d.l₂ L mk (Nc k) (Y k)) → ∀ f : Rul Xo c, IsThClsD Xo c d w La Nc gam vol ep io xs f → evR Xo c f y = evR d.Xo₂ d.c₂ d.cδ y₂ * κ * clsSum (algebraMap c.F ℂ) X hr bas idx eL w La Nc gam vol ep (fun k => io (xs k)) L v Y x := by
  first | exact @GlobalTheory.ClsVal.evR_eq_clsSum | exact GlobalTheory.ClsVal.evR_eq_clsSum | (intros; apply GlobalTheory.ClsVal.evR_eq_clsSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerOntoStd

open GlobalTheory.AdelTranslate GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem glue_map (c : E ≃ₐ[F] E) (e : FiniteAdeleRing (𝓞 F) F) (γ : Matrix (Fin n) (Fin n) E) :
    (glue e γ).map (sg (FiniteAdeleRing (𝓞 F) F) c) = glue e (γ.map c) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [glue, fm, sg]
  · simp [glue, fm, sg, Matrix.one_apply_ne h]

theorem mul_glue_sub_one {e α : FiniteAdeleRing (𝓞 F) F} (h : α * e = 0) (γ : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (α ⊗ₜ[F] (1 : E) : RA F E) * (glue e γ - 1) i j = 0 := by
  have h0 : (α ⊗ₜ[F] (1 : E) : RA F E) * (e ⊗ₜ[F] (1 : E)) = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, h, TensorProduct.zero_tmul]
  simp only [glue, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (fm F γ i j - (1 : Matrix (Fin n) (Fin n) (RA F E)) i j) * h0

theorem mul_idem_eq_zero {k M : ℕ} (hk : k.Coprime M) {v : HeightOneSpectrum (𝓞 F)} (hv : (M : 𝓞 F) ∈ v.asIdeal)
    {α : FiniteAdeleRing (𝓞 F) F} (hα : ∀ v', v' ≠ v → α v' = 0) : α * idem F k = 0 := by
  refine DFunLike.ext _ _ fun w => ?_
  change α w * idem F k w = 0
  by_cases h : w = v
  · subst h
    rw [idem_apply, if_neg, mul_zero]
    intro hk'
    obtain ⟨a, b, hab⟩ : IsCoprime (k : 𝓞 F) (M : 𝓞 F) := Nat.Coprime.cast hk
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (w.asIdeal.mul_mem_left a hk') (w.asIdeal.mul_mem_left b hv)))
  · rw [hα w h, zero_mul]

end General

theorem finPart_cA (D : D7) (x : AE D) :
    finPart D (cA D x) = sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (finPart D x) :=
  GlobalTheory.UnitarySplit.map_sig (sndA D.host.F) D.sp.cm.sig x


set_option maxHeartbeats 1000000 in
theorem exists_trivAt_isMov : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ M : ℕ, 0 < M → ∀ Λ ∈ Vset D.host.E S.rank M, ∃ h ∈ GfC S, TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h ∧ IsMov (fmtC S h) (stdL D.host.E S.rank) Λ := by
  rintro D S T C M - Λ ⟨-, hU', k, hk0, hkM, h1, h2⟩
  have hU : (⟨Λ⟩ : GenLat D.host.E S.rank).Unimod := (GlobalTheory.Dict.GenLatCmp.unimod_iff Λ).2 hU'
  have h₁ : ∀ x ∈ Λ, k • x ∈ stdL D.host.E S.rank := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h1 x hx
  have h₂ : ∀ x ∈ stdL D.host.E S.rank, k • x ∈ Λ := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h2 x hx
  obtain ⟨k', γ, hk', hγ, h₃, h₄⟩ := GlobalTheory.AdaptUnitary.exists_unitary_adapted D.host.E (hostOfRecord D) S.rank ⟨Λ⟩ k hU hk0
    (by rw [GlobalTheory.Dict.GenLatCmp.std_eq, span_smul_le_iff]; exact h₂) k hk0
  rw [GlobalTheory.Dict.GenLatCmp.std_eq] at h₃ h₄
  set c := GlobalTheory.Member.cF D with hc
  have c2 : ∀ x, c (c x) = x := fun x => star_star x
  set δ : Matrix (Fin S.rank) (Fin S.rank) D.host.E := (γ.map c)ᵀ with hδ
  have hδγ : δ * γ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← hγ i j]
    rfl
  have hγδ : γ * δ = 1 := mul_eq_one_comm.1 hδγ
  have hδc : γᵀ.map c = δ := rfl
  have h₅ : ∀ x ∈ stdL D.host.E S.rank, k' • δ *ᵥ x ∈ Λ := fun x hx => by
    obtain ⟨w, hw, e⟩ := h₄ x hx
    rwa [← Nat.cast_smul_eq_nsmul D.host.E, ← Matrix.mulVec_smul, e, Matrix.mulVec_mulVec, hδγ, Matrix.one_mulVec]
  have h₆ : ∀ x ∈ Λ, k' • γ *ᵥ x ∈ stdL D.host.E S.rank := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]
    exact h₃ x hx
  have he := idem_mul (F := D.host.F) k
  have t1 : γᵀ * δᵀ = 1 := by rw [← Matrix.transpose_mul, hδγ, Matrix.transpose_one]
  have t2 : δᵀ * γᵀ = 1 := by rw [← Matrix.transpose_mul, hγδ, Matrix.transpose_one]
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨h, hh, eh⟩ := lift ⟨glue (idem _ k) γᵀ, glue (idem _ k) δᵀ, glue_mul he t1, glue_mul he t2⟩ (by
    rw [C.m.gS, Matrix.transpose_one]
    refine isUnA_of c ?_
    change ((glue (idem _ k) γᵀ).map _)ᵀ * glue (idem _ k) γᵀ = 1
    rw [glue_map_sg, hδc]
    exact glue_mul he t2)
  have e1 : fmt S h = glue (idem _ k) γᵀ := congrArg Units.val eh
  have e2 : fmtC S h = glue (idem _ k) δ := by
    rw [← hδc, ← glue_map, ← e1]
    ext i j
    exact finPart_cA D _
  refine ⟨h, hh, ?_, ?_⟩
  · rintro v hv ε ⟨α, rfl, -, hα⟩ i j
    have hM : (M : 𝓞 D.host.F) ∈ v.asIdeal := hv (Ideal.mem_span_singleton_self _)
    apply GlobalTheory.UnitarySplit.parts_inj D
    · rw [map_mul, map_zero]
      have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
        change ((0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
        exact TensorProduct.zero_tmul _ _
      rw [this, zero_mul]
    · rw [map_mul, map_zero]
      have : finPart D ((mt S h - 1) i j) = (fmt S h - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, (finPart D).map_sub]
        congr 1
        by_cases hij : i = j
        · subst hij
          rw [Matrix.one_apply_eq, Matrix.one_apply_eq, (finPart D).map_one]
        · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, (finPart D).map_zero]
      rw [this, e1]
      exact mul_glue_sub_one (mul_idem_eq_zero hkM hM hα) _ i j
  · rw [e2]
    intro u
    constructor
    · intro hu
      refine ⟨_, glue_mem_hat (F := D.host.F) hk' h₆ h₁ u hu, ?_⟩
      rw [Matrix.mulVec_mulVec, glue_mul he hδγ, Matrix.one_mulVec]
    · rintro ⟨z, hz, ez⟩
      rw [ez]
      exact glue_mem_hat (F := D.host.F) hk' h₅ h₂ z hz

end GlobalTheory.KerOntoStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trivialAtLevel_unitary_transport_selfDual : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ M : ℕ, 0 < M → ∀ Λ ∈ Vset D.host.E S.rank M, ∃ h ∈ GfC S, TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h ∧ IsMov (fmtC S h) (stdL D.host.E S.rank) Λ := by
  first | exact @GlobalTheory.KerOntoStd.exists_trivAt_isMov | exact GlobalTheory.KerOntoStd.exists_trivAt_isMov | (intros; apply GlobalTheory.KerOntoStd.exists_trivAt_isMov <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HalfIntegralGeneratorAddConjEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding Unf GoodEmb IsUnf rdU laU
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShortRead

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem halfIntegralGenerator_add_conj_eq_one (H : Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : τ H.rt ^ 2 = -(H.d : ℂ) := by simpa using congrArg τ h1
  have h4 : 2 * τ H.w0 = 1 + τ H.rt := by simpa [map_ofNat] using congrArg τ h2
  have h5 : (τ H.rt).re = 0 := by
    have a := congrArg Complex.re h3
    have b := congrArg Complex.im h3
    have c : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [pow_two, mul_re, mul_im, neg_re, neg_im, natCast_re, natCast_im, neg_zero] at a b
    by_contra h
    have : (τ H.rt).im = 0 := mul_left_cancel₀ h (by linarith)
    rw [this] at a
    nlinarith [mul_self_nonneg (τ H.rt).re]
  apply τ.injective
  rw [map_add (f := _), cc, IsCMField.complexEmbedding_complexConj, map_one, Complex.add_conj]
  have h6 := congrArg Complex.re h4
  simp only [add_re, one_re, h5, add_zero, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at h6
  exact_mod_cast h6

theorem sb_smul (a : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (a • φ) :=
  (isSB_algebra_haar_linear ℚ _ _ φ φ h h).2.1 a

theorem sb_finsum {Q : Type} (f : Q → TF n g) (hf : ∀ q, IsSB (f q)) : IsSB (∑ᶠ q, f q) :=
  finsum_induction (fun φ : TF n g => IsSB φ) isSB_zero
    (fun φ ψ h h' => (isSB_algebra_haar_linear ℚ _ _ φ ψ h h').1) hf

theorem sb_gphi (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {M : ℕ} {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) {v : TF n g} (hv : IsSB v) {Q : Type} (W : Q → ℂ)
    (Y : Q → Matrix (Fin n) (Fin r) E) : IsSB (gphi X bas w Λ L v W Y) := by
  obtain ⟨⟨v', hv'⟩, -, h, -⟩ := TensVac.vacua E r X g bas idx n hs hn w hw hw' L hL M Λ hΛ
  refine sb_finsum _ fun q => sb_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 _ _ ?_).1
  rw [h v hv v' hv']
  exact sb_smul _ hv'.1

theorem theta_smul₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    {k : X.Ψ → Fin q0 → ℕ} {k' : X.Ψ → Fin X.p0 → ℕ} {φ : TF n g} (hφ : IsSB φ)
    {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} (hP : P ∈ Harm.rowHighest ℂ k k') {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (a : ℂ) : thP X hr bas idx (a • φ) P x = a * thP X hr bas idx φ P x := by
  have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn k k' _ hφ P hP).2.2.2 x hx
  have h : thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc a, tsum_mul_left]
    ring
  unfold thP
  rw [h, I2.polyDeriv_smul_fun _ _ han.contDiff]

theorem rdU_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (W : UW U) (k : U.Comp) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ Dc : Dic Dw c σ (U.X k) W.g Dw.p n a, Dc.e = W.e → ∀ (Λ : GenLat E n) (N : ℕ) (rk : Bool) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → AdmX (l := l) rk x0 → P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ f ∈ sec Xo c a n, IsShortRule Xo c d Λ N x0 P f → ∃ φ : TF n W.g, IsSB φ ∧ ∀ x ∈ (U.X k).dom, rdU U f k x = thP (U.X k) Dc.hr Dc.bas Dc.idx φ (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) x := by
  intro hCI E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hlev ⟨sr, hnab⟩ hunit hpin W k a hdom Dc hDe Λ N rk x0 P
    hΛ1 hΛ2 hΛ3 hadm hP f hf hshort
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI A₂ : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    change σ (d.eF.symm (d.eF t)) = σ t
    rw [AlgEquiv.symm_apply_apply]
  have hn : Even n := hdom.2
  have hrpq : r = Dw.p + Dw.q := hU.1
  obtain ⟨hle, hmap⟩ := admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d
  have hpq := hle rk x0 hadm
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin hpq
  obtain ⟨-, hL, hmk, -⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := halfIntegralGenerator_add_conj_eq_one H
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hN : 0 < N := hΛ3.1.pos
  obtain ⟨Λ⟩ := Λ
  have hΛ : Λ ∈ Vset E n d.l₂.M := (GenLatCmp.genLat_vset E n Λ).2.1 _ N hM hΛ1 hΛ2 hΛ3
  obtain ⟨v, hv⟩ := (TensVac.vacua E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL 1 _ (Base.stdL_mem_Vset n 1)).1
  obtain ⟨ρ, hρ, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL v hv
  have hroots : ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ →
      ∃ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ (U.X k).Λ mk₂ N Y := fun mk₂ h =>
    (GlobalTheory.Dict.DualMark.dual_marking E H Dw d.l₂ r _ _ mk₂ _ hL h (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hN

  obtain ⟨Y, hY⟩ : ∃ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E,
      ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ → MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₂ →
      ∀ Y', IsRoots d.l₂ (U.X k).Λ mk₂ N Y' → ∃ t : ℂ, ‖t‖ = 1 ∧
        gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y' =
          t • gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y := by
    by_cases hex : ∃ mk₃ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₃ ∧
        MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₃
    · obtain ⟨mk₃, h1, h2⟩ := hex
      obtain ⟨Y, hY⟩ := hroots mk₃ h1
      refine ⟨Y, fun mk₂ h3 h4 Y' hY' => ?_⟩
      obtain ⟨t, ht, h⟩ := GlobalTheory.Dict.MarkMove.gphi_move E H Dw l Xo c n d hlev ph ψ x₀ hph r _ _ Dc.bas Dc.idx Dc.sympl hn hrpq
        (hrpq ▸ hpq) _ hL (W.mark k) mk₂ mk₃ hmk h3 h1 h4 h2
      exact ⟨t, ht, h x0 v hv Λ hΛ N hΛ3 Y' Y hY' hY⟩
    · exact ⟨fun _ => 0, fun mk₂ h3 h4 => absurd ⟨mk₂, h3, h4⟩ hex⟩
  have hG := sb_gphi Dc.idx Dc.sympl hn hw hw' hL hΛ hv.1 (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y
  generalize gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y = G at hY hG
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = algebraMap d.c₂.F ℂ ((d.eF (betaH (Dw := Dw) c ⟨Λ⟩))⁻¹ *
    (((⟨Λ⟩ : GenLat E n).mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ *
    ((⟨Λ⟩ : GenLat E n).zCard N r : d.c₂.F)) := ⟨_, rfl⟩
  have hP' := Dc.mem P hP
  have huG := sb_smul u hG
  have hsec := hU.2.2.2.2.1 a n hdom f hf k
  have hth := theta_holomorphic_weight E r _ _ _ Dc.hr Dc.bas Dc.idx n Dc.sympl hn _ _ _ huG _ hP'
  rw [Dc.wt_eq] at hth
  obtain ⟨C, -, hC⟩ := const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Unit (fun _ => rdU U f k)
    (fun _ => thP (U.X k) Dc.hr Dc.bas Dc.idx (u • G) (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P))) ρ hρ
    (fun _ => ⟨hsec.1, hth.1, fun x hx b hb => ⟨hsec.2.1 x hx b hb, hth.2.1 x hx b hb⟩⟩) (by
      intro x hx hux
      obtain ⟨A, hA, θ, hθ, hmean⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx Dc.sympl
        (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨x, hx⟩ hux
      obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ halg (unC U k ⟨x, hx⟩)
      obtain ⟨B, hB, mk₂, hmk₂, hBm, hover⟩ := GlobalTheory.Dict.Lift.anFib_lift E H Dw l Xo c n d halg hlev r _ _ Dc.bas Dc.idx W.e x _
        _ A Dc.sympl hx hL y₂ hy₂ _ hA
      have hT := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r _ _ Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hL θ hθ
      obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL v hv x hx θ hT
      have hκn := hnorm x hx hux θ κ hT hmean hκ
      obtain ⟨Y', hY'⟩ := hroots mk₂ hmk₂
      obtain ⟨t, ht, hmove⟩ := hY mk₂ hmk₂ hover Y' hY'
      obtain ⟨v0, hv0, hev⟩ := hshort ℂ halg _ y₂ hy₂
      have hval := GlobalTheory.Dict.shortValAt_eq_thP hCI E H Dw d.l₂ d.Xo₂ d.c₂ r _ _ Dc.bas Dc.idx W.e x _ y₂ B Dc.sympl hx hL _ n
        Dc.hr Dc.eL hrpq hn (hDe ▸ Dc.dir_eq) d.nab₂ hnab θ v κ (hB θ hθ) hv hκ mk₂ hmk₂ hBm Λ hΛ N hΛ3 Y' hY'
        a _ (hmap a P hP) _ _ v0 hv0
      have hmm : MvPolynomial.map (algebraMap d.c₂.F ℂ) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
          MvPolynomial.map σ P := by
        rw [MvPolynomial.map_map]
        exact congrArg (fun s : c.F →+* ℂ => MvPolynomial.map s P) (RingHom.ext halg)
      rw [hmm, hmove, theta_smul₂ Dc.hr Dc.idx Dc.sympl hn hG hP' hx, ← hu] at hval
      refine ⟨evR d.Xo₂ d.c₂ d.cδ y₂ * κ * t, by rw [norm_mul, norm_mul, hunit A₂ y₂, hκn, ht]; ring, fun _ => ?_⟩
      have hrd : rdU U f k x = evR Xo c f (unC U k ⟨x, hx⟩) := dif_pos hx
      beta_reduce
      rw [hrd, hev, hval, theta_smul₂ Dc.hr Dc.idx Dc.sympl hn hG hP' hx]
      ring)
  refine ⟨C • u • G, sb_smul C huG, fun x hx => ?_⟩
  rw [theta_smul₂ Dc.hr Dc.idx Dc.sympl hn huG hP' hx]
  exact hC () x hx

end GlobalTheory.Dict.ShortRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependent
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

theorem readings_independent :
    ∀ (D : D7) (T : Top D), LawsM T.toCore → ∀ j, InR D j → ∀ a n, JInjRd T j a n := by
  intro D T hM j hj a n

  have hA := GlobalTheory.FramedBaseChange.bcEx_all _ _ _ _ (T.Q.Xo j) T.Q.c T.σ₀
  have hF := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.1
  exact jInjRd_of_wt T hM hj a n hA hF

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependentStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_frame_readings_linearIndependent : ∀ (D : D7) (T : Top D), LawsM T.toCore → ∀ j, InR D j → ∀ a n, JInjRd T j a n := by
  first | exact @GlobalTheory.Dict.readings_independent | exact GlobalTheory.Dict.readings_independent | (intros; apply GlobalTheory.Dict.readings_independent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IteratedFDerivSmulAll
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShortPt

theorem iteratedFDeriv_smul_all {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (a : ℂ) (F : W → ℂ) (k : ℕ) :
    iteratedFDeriv ℂ k (a • F) = a • iteratedFDeriv ℂ k F := by
  induction k with
  | zero => ext x m; simp
  | succ k ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih, fderiv_const_smul_field]
    funext x
    simp only [Function.comp_apply, Pi.smul_apply, map_smul]

theorem theta_smul₂ {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r) :
    thP X hr bas idx (a • φ) P x = a * thP X hr bas idx φ P x := by
  have h : thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc a, tsum_mul_left]
    ring
  unfold thP I2.polyDeriv
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_smul_all]
  simp only [Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem finite_levQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem vset_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n M : ℕ} {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨h1, h2, s, hs, -, h3⟩ := h
  exact ⟨h1, h2, s, hs, Nat.coprime_one_right s, h3⟩

theorem shortRule_value : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∀ y₂ : FrPt d.Xo₂ d.c₂ ℂ, ‖evR d.Xo₂ d.c₂ d.cδ y₂‖ = 1) → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r g q0 : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c (algebraMap c.F ℂ) X g q0 n a) (D : SW.Level X) (hn : r ≤ n), Even n → r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X Dc.bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ u : Lt E n → ℕ → ℂ, (∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → u Λ N ≠ 0) ∧ ∀ L ∈ D.lats, ∀ mk δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ X.dom, IsUnitFr X x → ∀ (y : FrPt Xo c ℂ) (A : AnFib X Dc.bas Dc.idx Dc.e x L y) (θ : (Fin g → ℂ) → ℂ), A.Marked mk → A.Reads 1 y.s θ → MeanOne X Dc.bas Dc.idx x L θ → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ f : Rul Xo c, IsShortRule Xo c d (⟨Λ⟩ : GenLat E n) N x0 P f → evR Xo c f y = κ * u Λ N * thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ L Λ) (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
  intro hCI E _ _ _ H Dw l Xo c n d _ _ hcomp hlev hnab hcδ ph ψ x₀ hpin r g q0 X a Dc D hn hev hr htie v₀ hv₀ x0
  obtain ⟨_, hnab⟩ := hnab
  obtain ⟨ρ₁, s, hρ₁, hg⟩ := GlobalTheory.Dict.GPhi.gphi_eq_smul_phiF E H Dw l Xo c n d hcomp hlev ph ψ x₀ hpin r g X Dc.bas Dc.idx D hn
    Dc.sympl hev hr htie v₀ hv₀ x0
  have hwi : IsIntegral ℤ (H.w0 : E) := htie.w ▸ D.w_int
  have hwt : (H.w0 : E) + cc (H.w0 : E) = 1 := htie.w ▸ D.w_tr
  have hΛ0 : SelfD X X.Λ := (GlobalTheory.SW.level_laws E r X g Dc.bas Dc.idx n Dc.sympl hev D hn).1.1
  refine ⟨fun Λ N => algebraMap d.c₂.F ℂ ((d.eF (betaH (Dw := Dw) c (⟨Λ⟩ : GenLat E n)))⁻¹ *
      (((⟨Λ⟩ : GenLat E n).mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ *
      ((⟨Λ⟩ : GenLat E n).zCard N r : d.c₂.F)) * (((if 0 < s Λ then s Λ else 1 : ℝ)) : ℂ), ?_, ?_⟩
  · intro Λ hΛ N hN
    obtain ⟨-, -, -, hz, hm, -⟩ := GlobalTheory.Dict.ZLat.exists_reps_sum E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt
      X.Λ hΛ0 Λ (vset_one hΛ) N hN.1 (hN.2.2.trans inf_le_left)
    haveI := finite_levQ Dw d.l₂
    have hb : betaH (Dw := Dw) c (⟨Λ⟩ : GenLat E n) ≠ 0 := by
      unfold betaH
      split_ifs with h
      · exact h.choose_spec.1
      · exact one_ne_zero
    have hc : 0 < Nat.card (Fin n → LevQ Dw d.l₂) := Nat.card_pos
    refine mul_ne_zero ((_root_.map_ne_zero _).2 ?_) ?_
    · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)) (inv_ne_zero ?_)) ?_
      · exact (_root_.map_ne_zero _).2 hb
      · exact Nat.cast_ne_zero.2 hm.ne'
      · exact Nat.cast_ne_zero.2 hc.ne'
      · exact Nat.cast_ne_zero.2 hz.ne'
    · rw [Complex.ofReal_ne_zero]
      split_ifs with h
      · exact h.ne'
      · exact one_ne_zero
  intro L hL mk δ hmk hδ hx0
  have hLs : SelfD X L := hL.1
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs 1 _
    (Base.stdL_mem_Vset (E := E) n 1)).1
  obtain ⟨ρ₀, hρ₀, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs v hv
  refine ⟨ρ₀ * ρ₁, mul_pos hρ₀ hρ₁, ?_⟩
  intro x hx hux y A θ hA hθ hmean
  obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ hcomp y
  obtain ⟨A₂, hA₂, mk₂, hmk₂, hA₂m, hover⟩ := GlobalTheory.Dict.Lift.anFib_lift E H Dw l Xo c n d hcomp hlev r g X Dc.bas Dc.idx Dc.e x L y A
    Dc.sympl hx hLs y₂ hy₂ mk hA
  have hth := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r g X Dc.bas Dc.idx Dc.e x L y A Dc.sympl hx hLs θ hθ
  obtain ⟨κ₀, hκ₀⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs v hv x hx θ hth
  obtain ⟨t, ht, hgt⟩ := hg L hL mk mk₂ δ v hmk hmk₂ hover hδ hx0 hv
  refine ⟨evR d.Xo₂ d.c₂ d.cδ y₂ * κ₀ * t, ?_, ?_⟩
  · rw [norm_mul, norm_mul, hcδ y₂, hnorm x hx hux θ κ₀ hth hmean hκ₀, ht, _root_.one_mul]
  intro Λ hΛ N hN P hP f hf
  obtain ⟨hs, hgt⟩ := hgt Λ hΛ
  have hM : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking E H Dw d.l₂ r X L mk₂ _ hLs hmk₂ (Complex.isPrimitiveRoot_exp _ hM)).2.2.2.2 n N
    hN.1.pos
  obtain ⟨v0, hv0, hfv⟩ := hf ℂ hcomp y y₂ hy₂
  have hval := GlobalTheory.Dict.shortValAt_eq_thP hCI E H Dw d.l₂ d.Xo₂ d.c₂ r g X Dc.bas Dc.idx Dc.e x L y₂ A₂ Dc.sympl hx hLs q0 n Dc.hr
    Dc.eL hr hev Dc.dir_eq d.nab₂ hnab θ v κ₀ (hA₂ θ hθ) hv hκ₀ mk₂ hmk₂ hA₂m Λ hΛ N hN Y hY a _
    ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP) _ _ v0 hv0
  have hmap : MvPolynomial.map (algebraMap d.c₂.F ℂ) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
      MvPolynomial.map (algebraMap c.F ℂ) P := by
    rw [MvPolynomial.map_map]
    congr 2
    exact RingHom.ext hcomp
  rw [hgt N hN Y hY, theta_smul₂, hmap] at hval
  beta_reduce
  rw [hfv, hval, if_pos hs]
  ring

end GlobalTheory.Dict.ShortPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadingEqThP
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThRead

theorem cmHost_idempotent_trace_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
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

theorem theta_smul₂ {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (C : ℂ) (φ : TF n g)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r)
    (h : AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ) :
    thP X hr bas idx (C • φ) P x = C * thP X hr bas idx φ P x := by
  have e : thA X bas idx (C • φ) x = C • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, tsum_mul_left]
    ring
  rw [thP, thP, e, I2.polyDeriv, I2.polyDeriv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_const_smul_apply ((h 0 trivial).contDiffAt)]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem isSB_smul {n g : ℕ} (C : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (C • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem thValAt_evR (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab : NabV Xo c) (hn : IsNab Xo c nab) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (xs : Fin n → Dw.La)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) {f : Rul Xo c} (hf : IsThRule Xo c nab xs P f)
    (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    ThValAt Xo c nab y xs P (evR Xo c f y) := by
  have hL : Laws := GlobalTheory.allSixLaws.1
  have ht := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S y
  obtain ⟨w, hw, -⟩ := GlobalTheory.thValTot_of_chartIndep hL hC E H Dw l Xo c nab hn S y a n xs P hP
  have e : evR Xo c f y = w := by
    unfold evR evalAt
    rw [dite_eq_left ht]
    exact GlobalTheory.thetaValue_natural hL hC E H Dw l Xo c nab hn _ S _ _ y ht.choose_spec.choose_spec.choose_spec
      a n xs P hP _ w (hf _ _) hw
  rw [e]
  exact hw

theorem reading_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ n : ℕ, ∀ (W : UW U) (k : U.Comp) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ Dc : Dic Dw c σ (U.X k) W.g Dw.p n a, Dc.e = W.e → ∀ (xs : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab xs P f → f ∈ sec Xo c a n ∧ ∃ φ : TF n W.g, IsSB φ ∧ ∀ x ∈ (U.X k).dom, rdU U f k x = thP (U.X k) Dc.hr Dc.bas Dc.idx φ (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) x := by
  intro hC E _ _ _ H Dw l Xo c σ r U hσ hU hr1 _ nab hn n W k a hD Dc he xs P hP f hf
  have hL : Laws := GlobalTheory.allSixLaws.1
  have hsec : f ∈ sec Xo c a n := GlobalTheory.thetaRule_mem_sec hL hC E H Dw l Xo c nab hn a n f ⟨xs, P, hP, hf⟩
  refine ⟨hsec, ?_⟩
  have hev : Even n := hD.2
  obtain ⟨-, hsd, hmk, -⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw1 := cmHost_idempotent_trace_eq_one H
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd 1 _
    (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hsd hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  obtain ⟨ρ, hρ, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd v hv
  set Y₀ := Y (fun b => Submodule.Quotient.mk (xs b)) with hY₀
  have hsb : IsSB (heisG (U.X k) Dc.bas Y₀ v) :=
    ((GlobalTheory.SW.heisG_laws E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev).2.2.2 Y₀ v hv.1).1
  have hhol := GlobalTheory.SW.theta_holomorphic_weight E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev Dc.k Dc.k'
    _ hsb _ (Dc.mem P hP.1)
  have hS := hU.2.2.2.2.1 a n hD f hsec k
  have hwt : wtOf (U.X k) Dc.hr Dc.k Dc.k' n = laU U a n k := Dc.wt_eq
  rw [hwt] at hhol
  obtain ⟨C, -, hCeq⟩ := GlobalTheory.Dict.const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Unit
    (fun _ => rdU U f k)
    (fun _ => thP (U.X k) Dc.hr Dc.bas Dc.idx (heisG (U.X k) Dc.bas Y₀ v)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P))) ρ hρ
    (fun _ => ⟨hS.1, hhol.1, fun x hx b hb => ⟨hS.2.1 x hx b hb, hhol.2.1 x hx b hb⟩⟩) (by
      intro x hx hux
      letI : Algebra c.F ℂ := σ.toAlgebra
      obtain ⟨A, hA, θ, hθ, hmean⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx Dc.sympl
        (he ▸ Dc.per_eq) (he ▸ Dc.ty_eq) ⟨x, hx⟩ hux
      have h1 := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd θ hθ
      obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd v hv x hx θ h1
      refine ⟨κ, hnorm x hx hux θ κ h1 hmean hκ, fun _ => ?_⟩
      have hval := thValAt_evR hC Xo c nab hn xs hP hf ℂ (unC U k ⟨x, hx⟩)
      have := GlobalTheory.Dict.thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd Dw.p n Dc.hr
        Dc.eL hU.1 hev (he ▸ Dc.dir_eq) nab hn θ v κ hθ hv hκ (W.mark k) hmk hA xs Y₀ (fun b => by
          obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY (fun b => Submodule.Quotient.mk (xs b)) b
          exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hy⟩, hj⟩) a P hP _ hval
      refine Eq.trans ?_ this
      show (if h : x ∈ (U.X k).dom then Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) = _
      rw [dite_eq_left hx]
      rfl)
  refine ⟨C • heisG (U.X k) Dc.bas Y₀ v, isSB_smul C hsb, fun x hx => ?_⟩
  rw [theta_smul₂ _ _ _ _ _ _ _ _ (hhol.2.2.2 x hx)]
  exact hCeq () x hx

end GlobalTheory.Dict.ThRead
end
