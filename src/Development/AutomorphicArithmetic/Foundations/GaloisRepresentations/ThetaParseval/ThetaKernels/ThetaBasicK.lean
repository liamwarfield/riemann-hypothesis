module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Pair
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
structure IsPair_k (B : Base F E) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ) : Prop where
  base : _root_.UpperTheory.TP.W.GoodK σ B
  herm : X.IsHerm σ B r s
  skew : W.IsSkew σ B r' s'
  good : M.IsGood B.ψ
  hX : IsHecke F E χX
  hW : IsHecke F E χW
  resX : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n
  resW : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d
  weil : M.IsWeil B.ψ χX χW om
end Pair
variable {a a' : ℕ}
def ThetaBasic_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' →
    (∀ Φ ∈ schA F _, Continuous (fun x : UA σ X.J × UA σ W.J => theta om Φ x.1 x.2) ∧
      (∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h) ∧
      ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k) ∧
    ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ g h, Continuous fun f : SInf F (Fin n × Fin d) => theta om (pureA F f φ) g h
def StabEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s →
    ∃ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K ∧ IsCompact (K : Set (UA σ X.J)) ∧
      μK.IsHaarMeasure ∧ μ.IsHaarMeasure
def ActsEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ v : Pl F,
    (∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (g, h)) φ φ₁) ∧
    (∀ u, At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁) ∧
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∀ x ∈ U, x.1 ∈ UAt σ X (evFin F v) →
      x.2 ∈ UAt σ W (evFin F v) → Acts (evFin F v) (om x) φ φ
end GlobalTheory.ThK
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsStdCharFOfIsGoodK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.StdCharWeilDatum
section Char
variable {F : Type} [Field F] [NumberField F]
end Char
section Trace
variable {F : Type} [Field F] [NumberField F]
end Trace
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isStdCharF_of_isGood_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTotallyReal F := hB.cm.1
  refine ⟨isCharAF hB.std, ⟨?_, fun θ hθ x => ?_⟩⟩
  · choose θ hθ using fun w : InfinitePlace F =>
      GlobalTheory.DualPairCompare.gen_inf_exists (B.emb w).1 w (B.emb w).2.symm
    exact ⟨θ, hθ⟩
  · show B.ψ (pairA F x 0) = _
    rw [psi_pairA hB.std, sum_infFam B θ hθ x]
    congr 1
    push_cast
    ring
end GlobalTheory.StdCharWeilDatum
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsS
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
def SiegelWeilStd_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n → min r s = 0 →
    (A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ (κ : Type) [Fintype κ] dd om S l, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) B.ψ dd χ om S l →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a →
    ∀ (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ A.J) D μ →
    ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ)) →
      EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutDef
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
structure Ctx_k (σ : E →ₐ[F] E) (B : Base F E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E) : Prop where
  good : _root_.UpperTheory.TP.W.GoodK σ B
  hS : IsHermND σ JS
  hT : IsHermND σ JT
  h0 : ξ₀ ≠ 0
  hξ : σ ξ₀ = -ξ₀
  inf : IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ
  chart : IsChartF θ ι
section Lin
variable {κ : Type} [Fintype κ]
end Lin
variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
end PositivityTheory.ThKW
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsThetaFunOFHeisOFK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.HeisThetaF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Alg
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
end Alg
section Parts
end Parts
section Top
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
end Top
section Fin
end Fin
theorem isThetaFunOF_heisOF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
      (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT ξ₀ w₀ f hf
  have hψ : Continuous B.ψ := hB.std.1
  haveI := isTopologicalRing_AEF (F := F) (E := E)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ w
    simp only [heisOF]
    rw [add_assoc, hf.quasi, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    abel
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨K, hK⟩ := exists_openAddSubgroup_psi_fin B.ψ hψ
    let φ : WOF F E nS nT →+ AF F :=
      { toFun := fun u => symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u
        map_zero' := by simp only [symplOHF_zero_left, symplOHF_zero_right, sub_zero]
        map_add' := fun u v => by simp only [symplOHF_add_left, symplOHF_add_right]; abel }
    have hφ : Continuous φ := (continuous_symplOHF_left w₀).sub (continuous_symplOHF_right w₀)
    let ρ : WOF F E nS nT →+ Af F := (sndA F).toRingHom.toAddMonoidHom.comp φ
    have hρ : Continuous ρ := continuous_snd.comp hφ
    refine ⟨U ⊓ K.toAddSubgroup.comap ρ, hU.inter (K.isOpen.preimage hρ), fun u hu h0 => ?_⟩
    have h1 : pairA F 1 0 • u = 0 := smul_eq_zero_of_map_infPartF h0
    have hfst : fstA F (φ u) = 0 := by
      rw [← fstA_mul_idem]
      show fstA F (pairA F 1 0 * (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)) = 0
      rw [mul_sub, ← symplOHF_smul_left, ← symplOHF_smul_right, h1, symplOHF_zero_left, symplOHF_zero_right,
        sub_zero, map_zero]
    have hφu : φ u = pairA F 0 (ρ u) := Prod.ext hfst rfl
    have hone : B.ψ (φ u) = 1 := by rw [hφu]; exact hK _ hu.2
    have hswap : B.ψ (symplOHF σ JS JT ξ₀ u w₀) = B.ψ (symplOHF σ JS JT ξ₀ w₀ u) := by
      have : symplOHF σ JS JT ξ₀ u w₀ = φ u + symplOHF σ JS JT ξ₀ w₀ u := by
        show _ = (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u) + _
        abel
      rw [this, AddChar.map_add_eq_mul, hone, one_mul]
    funext w
    have hw := congrFun (hUf u hu.1 h0) (w + w₀)
    simp only [heisOF] at hw ⊢
    rw [← hw, add_right_comm w u w₀, symplOHF_add_left w u w₀, symplOHF_add_left w w₀ u, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, hswap]
    ring
  · show Continuous fun w => B.ψ (symplOHF σ JS JT ξ₀ w w₀) * f (w + w₀)
    exact (hψ.comp (continuous_symplOHF_left w₀)).mul (hf.cont.comp (continuous_id.add continuous_const))
  · intro k L hL h0 w
    let φ₁ : WOF F E nS nT →+ AF F :=
      { toFun := fun u => symplOHF σ JS JT ξ₀ u w₀
        map_zero' := symplOHF_zero_left w₀
        map_add' := fun u v => symplOHF_add_left u v w₀ }
    let ev : AF F →+ ℝ :=
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toAddMonoidHom.comp
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv.toAddMonoidHom.comp (fstA F).toRingHom.toAddMonoidHom)
    have hev : Continuous ev :=
      (LinearMap.continuous_of_finiteDimensional (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))).comp
        ((continuous_ringEquiv_mixedSpace F).comp continuous_fst)
    let g : (Fin k → ℝ) →+ ℝ := ev.comp (φ₁.comp L)
    have hg : Continuous g := hev.comp ((continuous_symplOHF_left w₀).comp hL)
    let gL := g.toRealLinearMap hg
    have hval : ∀ t, B.ψ (symplOHF σ JS JT ξ₀ (L t) w₀) =
        Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) := by
      intro t
      have hfin : sndA F (symplOHF σ JS JT ξ₀ (L t) w₀) = 0 := by
        have h1 : pairA F 0 1 • L t = 0 := smul_eq_zero_of_map_finPartF (h0 t)
        rw [← sndA_mul_idem, ← symplOHF_smul_left, h1, symplOHF_zero_left, map_zero]
      rw [hB.std.2.2 _ ?_]
      · rfl
      · intro v hv
        have hv1 : v.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hv
        refine Prod.ext ?_ ?_
        · show v.1 * (symplOHF σ JS JT ξ₀ (L t) w₀).1 = 0
          rw [hv1, zero_mul]
        · show v.2 * (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0
          rw [show (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0 from hfin, mul_zero]
    have hfun : (fun t => heisOF σ JS JT ξ₀ B.ψ w₀ f (w + L t)) = fun t =>
        B.ψ (symplOHF σ JS JT ξ₀ w w₀) * Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) *
          f (w + w₀ + L t) := by
      funext t
      simp only [heisOF]
      rw [symplOHF_add_left, AddChar.map_add_eq_mul, hval, add_right_comm]
    rw [hfun]
    refine (contDiff_const.mul ?_).mul (hf.smooth k L hL h0 (w + w₀))
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp gL.contDiff)).cexp
end GlobalTheory.HeisThetaF
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def HgtEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h'))
def Unfold0_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 →
    ∀ (χ : Chr F E) (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsHecke F E χ → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ (f Ê : G2 σ Y → ℂ) (z : ℂ), Continuous f → Continuous Ê → (∀ x, HasSum (eisTerm f x) (Ê x)) →
      (∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z * f x) →
    ∀ (μ : Measure (UA σ Y.J)) (D : Set (UA σ Y.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ Y.J) D μ →
      Integrable (fun g => f (e (1, g))) μ → ∀ φ : UA σ Y.J → ℂ, IsRapid φ → ∀ h,
        ∫ h' in D, Ê (e (h, h')) * detInv χ h' * φ h' ∂μ = ∫ g, f (e (1, g)) * detInv χ g * φ (h * g) ∂μ
def HgtInt_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K a (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → IsHgt K a → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ μ : Measure (UA σ Y.J), μ.IsHaarMeasure → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseUnfoldB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem aniso_of_k {B : Base F E} {r s : ℕ} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (h0 : min r s = 0) :
    Aniso σ Y.J := fun x hx => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have e : ((B.emb w).1 ∘ x) ⬝ᵥ Y.J.map (B.emb w).1 *ᵥ star ((B.emb w).1 ∘ x) = 0 := by
    rw [← map_zero (B.emb w).1, ← hx]
    simp [form, Matrix.mulVec, dotProduct, hB.cm.2.2.2]
  have : (B.emb w).1 ∘ x = 0 := hY.elim (fun h => HasSig.aniso (h.sig w) h0 e) fun h => HasSig.aniso (h.sig w) h0 (by
    rw [Matrix.smul_mulVec, dotProduct_smul, e, smul_zero])
  exact funext fun i => (map_eq_zero _).1 (congrFun this i)
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocRepExK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThK
open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
structure PairOK_k (B : Base F E) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) : Prop where
  base : _root_.UpperTheory.TP.W.GoodK σ B
  herm : ∃ r s, X.IsHerm σ B r s
  skew : ∃ r s, W.IsSkew σ B r s
  good : M.IsGood B.ψ
  weil : ∃ χX χW, M.IsWeil B.ψ χX χW om
def AllPairs_k (Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    (_ : Base F E) {X : Spc F E n} {W : Spc F E d} (_ : Model σ X W) (_ : Rep σ X W), Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W), _root_.PositivityTheory.ThK.PairOK_k B X W M om → ∀ v, Q B M om v
def LocRepEx_k : Prop := _root_.PositivityTheory.ThK.AllPairs_k fun B _ _ M om v => ∃ ω ρ, IsLocRep M B.ψ om v ω ρ
def InertOf_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∃ w, Formalism.UG.IsInertAt F E v w
end PositivityTheory.ThK
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitOrInertK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitOrInertK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.KFinLoc
namespace GlobalTheory.KFinLoc
theorem split_or_inert_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  intro F E _ _ _ _ _ σ B hB v
  have hUn := hB.unram
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
    refine GlobalTheory.LFun.isUnram_iff.2 fun w _ => ?_
    exact Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | hi
  · left
    obtain ⟨w, w', hne, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact ⟨(GlobalTheory.AdelicU.existsUnique_splitPrime_eq hB.cm hne h1 h2).exists.choose⟩
  · exact Or.inr hi
end GlobalTheory.KFinLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitOrInertKStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  first | exact @_root_.GlobalTheory.KFinLoc.split_or_inert_k | exact _root_.GlobalTheory.KFinLoc.split_or_inert_k | (intros; apply _root_.GlobalTheory.KFinLoc.split_or_inert_k <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIntAddConjEqOneOfBaseGoodK
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory
theorem exists_int_add_conj_eq_one_of_base_good_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ B hB
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
  exact exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance
end GlobalTheory
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def FinLevel_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ) (K : Subgroup (G2 σ Y)),
    IsCompact (K : Set (G2 σ Y)) → ∀ Φ ∈ schA F κ, ∃ Λ : Set (Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      (∀ u ∈ Λ, (∀ i, evI F ((dd.e u).1 i) = 0) ∧ (∀ i, evI F ((dd.e u).2 i) = 0) ∧ ∀ k ∈ K, actB (cA σ) k u ∈ Λ) ∧
      (∀ u ∈ Λ, dd.rho B.ψ u Φ = Φ) ∧ ∃ s : Finset (κ → AF F), (∀ y ∈ s, ∀ i, evI F (y i) = 0) ∧
        ∀ Ψ : (κ → AF F) → ℂ, (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) → ∀ x : κ → AF F, At (evI F) x → (∀ y ∈ s, Ψ (x + y) = 0) →
          ∀ y : κ → AF F, (∀ i, evI F (y i) = 0) → Ψ (x + y) = 0
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsCompactStandardMaximalCompact
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsCompactKK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.CompanionTheory.StdK
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem isCompact_K_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  intro F E _ _ _ _ _ σ B n Y r s hB _ _ b K a _ hK _
  exact isCompact_of_isStdK B hB.cm b K hK
end GlobalTheory.CompanionTheory.StdK
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_standard_maximal_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  first | exact @_root_.GlobalTheory.CompanionTheory.StdK.isCompact_K_k | exact _root_.GlobalTheory.CompanionTheory.StdK.isCompact_K_k | (intros; apply _root_.GlobalTheory.CompanionTheory.StdK.isCompact_K_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBadA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Bad
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
variable {Y : Spc F E n} {B : Base F E} {v : Pl F} {r s : ℕ}
theorem theta_pm_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) : Y.θ w = 1 ∨ Y.θ w = -1 :=
  cartan_pm (h.sig w) h0 (fun i j => (hB.cm.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))) (h.cartan w)
theorem commute_theta_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) (A) : Commute A (Y.θ w) := by
  rcases _root_.GlobalTheory.ThK.Dbl.Bad.theta_pm_k hB h h0 w with e | e <;> rw [e]
  exacts [Commute.one_right _, Commute.neg_one_right _]
theorem stab_iff_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (UA σ Y.J)} (hK : IsStab B K)
    {g : UA σ Y.J} : g ∈ K ↔ ∀ v, IntAt v g :=
  (hK g).trans ⟨fun a _ z hz _ => a.2 z hz, fun a => ⟨fun w => _root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _, fun _ hz =>
    ⟨mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).1) hz, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).2) hz⟩⟩⟩
theorem emb_mem_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K)
    {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : ∀ v, IntAt v g) :
    e (g, 1) ∈ K := by
  refine (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k hk => ?_⟩
  · rw [he g 1, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
    simp only [Commute, SemiconjBy, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (_root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _).eq, (_root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _).neg_right.eq]
  · obtain ⟨g', e1, hg'⟩ : ∃ g', k = e (g', 1) ∧ mat g' *ᵥ z ∈ latHat Y := by
      rcases hk with rfl | rfl
      · exact ⟨g, rfl, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).1) hz⟩
      · exact ⟨g⁻¹, by rw [← map_inv, Prod.inv_mk, inv_one], mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).2) hz⟩
    rw [e1, he g' 1, Matrix.fromBlocks_mulVec, show mat (1 : UA σ Y.J) = 1 from rfl]
    simpa using ⟨hg', hz'⟩
end GlobalTheory.ThK.Dbl.Bad
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SWStdLtK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}
structure Std_k (B : Base F E) {m : ℕ} (A : Spc F E m) (Y : Spc F E n) (r s r' s' : ℕ) (χ : Chr F E) (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ)
    (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)) (Φ : (κ → AF F) → ℂ) : Prop where
  good : _root_.UpperTheory.TP.W.GoodK σ B
  hm : 1 ≤ m
  hn : 1 ≤ n
  hnm : n < m
  aniso : min r s = 0
  sign : A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s'
  hecke : IsHecke F E χ
  res : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m
  dbl : IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l
  frame : IsFrame2 σ Y b
  stdK : IsStdK (σ := σ) (Y := Y) B b K
  hgt : IsHgt K a
  haar : μ.IsHaarMeasure
  dom : IsFundamentalDomain (ratU σ A.J) D μ
  sch : Φ ∈ schA F κ
  fin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ))
def SWStdLt_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s' χ (κ : Type) [Fintype κ] dd om S l b K a μ D Φ,
    _root_.PositivityTheory.SiegelWeilFormula.Std_k (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ →
      EisValueAt (sec om l a m Φ) (s0 m n) (thetaMean om S μ D Φ)
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchrodingerModelIsomorphism
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsThetaFunOFThVK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThetaTransformF
open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff
section Phase
variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}
end Phase
end GlobalTheory.ThetaTransformF
end
noncomputable section
namespace GlobalTheory.ThetaTransformF
open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff
section Crit
variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}
end Crit
end GlobalTheory.ThetaTransformF
end
noncomputable section
namespace GlobalTheory.ThetaTransformF
open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Invertible (2 : AF F)]
  {σ : E →ₐ[F] E} {nS nT N : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ} {e : WOF F E nS nT ≃ₗ[AF F] VA F N}
end Main
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem isThetaFunOF_thV_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ hstd N e he hrat Φ hΦ
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hstd.1
  obtain ⟨hc, -, hfin, hinf⟩ := coordF nT nS N e
  have hcont : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Continuous (thV B.ψ Φ) := fun Φ hΦ =>
    GlobalTheory.T.continuous_adelicThetaTransformSymplectic_of_decay F N B.ψ hR hψ Φ (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ)
  refine ⟨fun γ w => ?_, ?_, (hcont Φ hΦ).comp hc, ?_⟩
  · obtain ⟨y, z, h⟩ := hrat γ
    simp only [Function.comp_apply, map_add (f := _), symplOHF_eq he, h]
    exact quasiV_thV B.ψ hψ.2.2.1 Φ y z (e w)
  · obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_schroedinger_open_finite_subgroup F N B.ψ hR hψ Φ hΦ
    refine ⟨U.comap e.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 => ?_⟩
    rw [heisOF_comp he, ← thV_schr, hU (e u) hu ((hinf u).1 h0).1 ((hinf u).1 h0).2]
  · intro k L hL hL0 w
    have h := contDiff_of_heisV_closed B.ψ hψ.1 {g | ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), g = thV B.ψ Φ}
      (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hcont Φ hΦ)
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ M hM
        obtain ⟨Φ', hΦ', hd⟩ := GlobalTheory.T.hasDerivAt_heisenbergOperator_thetaTransform_realLine F N B.ψ hR hψ Φ hΦ M hM
        exact ⟨_, ⟨Φ', hΦ', rfl⟩, hd⟩)
      _ ⟨Φ, hΦ, rfl⟩ k (e.toLinearMap.toAddMonoidHom.comp L) (hc.comp hL) (fun t => (hfin _).1 (hL0 t)) (e w)
    simpa [Function.comp_def] using h
end GlobalTheory.ThetaTransformF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_model_isomorphism : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  first | exact @_root_.GlobalTheory.ThetaTransformF.isThetaFunOF_thV_k | exact _root_.GlobalTheory.ThetaTransformF.isThetaFunOF_thV_k | (intros; apply _root_.GlobalTheory.ThetaTransformF.isThetaFunOF_thV_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBadStmt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
def VacFix2_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ → ∀ χ : Chr F E, IsHecke F E χ → ∀ dd om, IsDblCoordX M dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (dbl (incM F X.J)) dd χ (diagCols (Fin n)) om →
    ∀ K, IsStab2 (σ := σ) (Y := X) B K → ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
      Acts (evFin F v) (om k) (boxFun (M.vac v) (star (M.vac v))) (boxFun (M.vac v) (star (M.vac v)))
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsX
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def SWAnisoX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) (((d : ℂ) - n) / 2)
        fun x => (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousThetaTrFK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace GlobalTheory.ThetaTrContF
theorem continuous_thetaTrF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  have hc : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  exact (GlobalTheory.ThetaTrCont.schA_cont F B.ψ hψ.1.1 hψ.1.2.1 hΦ).2.comp hc
end GlobalTheory.ThetaTrContF
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheorems
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def SWAniso_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) (M : Model σ A Y) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n → A.IsHerm σ B r s →
    min r s = 0 → Y.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ dd om S l, IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) M.co dd → IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in M.dom, thetaSum F (om x (S g (boxFun Φ₁ (star Φ₂)))) ∂M.μ
def EisContinues_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ b : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ b →
    ∀ K a, IsStab2 (σ := σ) (Y := Y) B K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ U Ê, IsEisCont (flat a f s₁) U Ê ∧ ∀ s₀, ∃ k, IsRegAt Ê s₀ k
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HermitianFormMatrixSelfadjoint
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HMFHermDetK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.RealWeilF
end GlobalTheory.RealWeilF
theorem GlobalTheory.RealWeilF.HMF_herm_det_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ
  exact GlobalTheory.RealWeilF.hermitianFormRealCoordinateBlock_hermitian_det σ hB.cm.2.2.2 JS JT hS hT ξ₀ h0 hσ _
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_matrix_selfadjoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  first | exact @_root_.GlobalTheory.RealWeilF.HMF_herm_det_k | exact _root_.GlobalTheory.RealWeilF.HMF_herm_det_k | (intros; apply _root_.GlobalTheory.RealWeilF.HMF_herm_det_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsTraceZeroElement
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsNeZeroConjNegK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.CMTraceZero
theorem exists_ne_zero_conj_neg_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨_, hc, _, hτ⟩ := hB.cm
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hw := hc.isComplex w
    rw [InfinitePlace.isComplex_iff] at hw
    apply hw
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hτ w.embedding x
    rw [hall x] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]
end GlobalTheory.CMTraceZero
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_zero_element : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  first | exact @_root_.GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg_k | exact _root_.GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg_k | (intros; apply _root_.GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg_k <;> assumption)
end
end
