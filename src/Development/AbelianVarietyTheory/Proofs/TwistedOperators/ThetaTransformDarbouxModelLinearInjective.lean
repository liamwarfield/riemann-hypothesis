module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutCuspOfMemCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaTransformInj

theorem linear_injective : ∀ (D : D7) {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d), Mo.IsGood ψ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → Y.J.det ≠ 0 → Z.J.det ≠ 0 → G.det ≠ 0 →
    ∃ T : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ),
      (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ) ∧
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = 0 → Φ = 0 := by
  intro D m k d Y Z Mo ψ G e _ hψ _ _ hG
  have hGG : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), Matrix.map_one _ (map_zero _) (map_one _)]
  have hsur : ∀ u, ∃ x, GlobalTheory.TripleRead.ptO G e x = u := by
    intro u
    refine ⟨(HMul.hMul (u.submatrix id e.symm)ᵀ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G) : Matrix (Fin d) (Fin m) (AE D)), ?_⟩
    simp only [GlobalTheory.TripleRead.ptO, Matrix.mul_assoc, hGG, Matrix.mul_one, Matrix.transpose_transpose]
    ext i j
    simp
  have hadd : ∀ (u : Matrix (Fin m) (Fin k) (AE D)) (Φ Ψ : (Fin m × Fin k → AF D.host.F) → ℂ),
      Mo.co.rho ψ u (Φ + Ψ) = Mo.co.rho ψ u Φ + Mo.co.rho ψ u Ψ := by
    intro u Φ Ψ
    funext y
    simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]
  have hsmul : ∀ (u : Matrix (Fin m) (Fin k) (AE D)) (c : ℂ) (Φ : (Fin m × Fin k → AF D.host.F) → ℂ),
      Mo.co.rho ψ u (c • Φ) = c • Mo.co.rho ψ u Φ := by
    intro u c Φ
    funext y
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
    ring
  let f : GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ) :=
    { toFun := fun Φ => GlobalTheory.TripleRead.thO Mo ψ G e Φ.1
      map_add' := fun Φ Ψ => by
        funext x
        simp only [GlobalTheory.TripleRead.thO, Submodule.coe_add, Pi.add_apply, hadd]
        exact GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA Mo ψ hψ _ _ Φ.2)
          (GlobalTheory.HeisSchA.rho_mem_schA Mo ψ hψ _ _ Ψ.2)
      map_smul' := fun c Φ => by
        funext x
        simp only [GlobalTheory.TripleRead.thO, Submodule.coe_smul, Pi.smul_apply, hsmul, smul_eq_mul, RingHom.id_apply]
        exact GlobalTheory.WeilM.thetaSum_smul _ c _ }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend f
  have hTf : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ := by
    intro Φ hΦ
    exact LinearMap.congr_fun hT ⟨Φ, hΦ⟩
  refine ⟨T, hTf, fun Φ hΦ h0 => ?_⟩
  rw [hTf Φ hΦ] at h0
  refine GlobalTheory.ThetaInj.theta_inj Mo ψ hψ (fun u => u) Φ 0 (fun _ => 0) ⟨hΦ, fun u => ?_⟩
    ⟨Submodule.zero_mem _, fun u => ?_⟩
  · obtain ⟨x, rfl⟩ := hsur u
    exact congrFun h0 x
  · simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

end GlobalTheory.ThetaTransformInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_darbouxModel_linear_injective : ∀ (D : D7) {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d), Mo.IsGood ψ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → Y.J.det ≠ 0 → Z.J.det ≠ 0 → G.det ≠ 0 →
    ∃ T : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ),
      (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ) ∧
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = 0 → Φ = 0 := by
  first | exact @GlobalTheory.ThetaTransformInj.linear_injective | exact GlobalTheory.ThetaTransformInj.linear_injective | (intros; apply GlobalTheory.ThetaTransformInj.linear_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartz
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly

theorem darbAlg_le_schA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w),
    M.IsGood ψ → GlobalTheory.TripleAssembly.darbAlg M ψ τ ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ n d Y Z M ψ τ hM
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, -, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

end GlobalTheory.TripleAssembly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w),
    M.IsGood ψ → GlobalTheory.TripleAssembly.darbAlg M ψ τ ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
  first | exact @GlobalTheory.TripleAssembly.darbAlg_le_schA | exact GlobalTheory.TripleAssembly.darbAlg_le_schA | (intros; apply GlobalTheory.TripleAssembly.darbAlg_le_schA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinOfRest
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaSchrCont

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic
open scoped Matrix

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def finSlice (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → mixedEmbedding.mixedSpace F) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun w => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), w i)

theorem finSlice_mem {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    finSlice Φ y ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    have : finSlice (pureA F f g) y = f y • g := by
      funext w
      simp only [finSlice, pureA, RingEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ hg
  | zero => exact (SB _).zero_mem
  | add x x' _ _ hx hx' => exact (SB _).add_mem hx hx'
  | smul a x _ hx => exact (SB _).smul_mem a hx

theorem exists_fin_of_rest {f : SInf F κ} {r : (κ → AF F) → ℂ} (hr : Rest (evI F) (⇑f) r) (hf : f ≠ 0) :
    ∃ G ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∀ x : κ → AF F, r x = G fun i => (x i).2 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  refine ⟨(f y)⁻¹ • finSlice (tens (evI F) (⇑f) r) y, Submodule.smul_mem _ _ (finSlice_mem hr.2 y), fun x => ?_⟩
  let z : κ → AF F := fun i => mk (e.symm (y i) - (x i).1) 0
  have hz : At (evI F) z := by
    intro u hu
    funext i
    exact at_mk _ u hu
  have hxz : x + z = fun i => (e.symm (y i), (x i).2) := by
    funext i
    refine Prod.ext ?_ ?_
    · show (x i).1 + (e.symm (y i) - (x i).1) = e.symm (y i)
      abel
    · show (x i).2 + 0 = (x i).2
      exact add_zero _
  have h1 := hr.1 x z hz
  rw [hxz] at h1
  have h2 : (fun i => evI F ((e.symm (y i), (x i).2) : AF F)) = y := by
    funext i
    exact e.apply_symm_apply (y i)
  simp only [Pi.smul_apply, smul_eq_mul, finSlice, tens]
  rw [h2, ← h1]
  field_simp
  rfl

theorem tens_eq_pureA (g : SInf F κ) {r : (κ → AF F) → ℂ} {G : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hG : ∀ x : κ → AF F, r x = G fun i => (x i).2) : tens (evI F) (⇑g) r = pureA F g G := by
  funext x
  simp only [tens, pureA, hG]
  rfl

theorem schr_pureA_eq [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsStd ψ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
    let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
    schr ψ w (pureA F f g) = pureA F (archS f (fun i => q (w.2 i)) (fun i => q (w.1 i))
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)))
      (finS ψ g (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)) := by
  intro q h
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  funext x
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
        change q (x ⬝ᵥ w.2 + h) = _
        rw [map_add (f := _), RingHom.map_dotProduct]
        rfl
      rw [e1, map_add (f := _), eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add (f := _), RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

theorem exists_clm_hasSum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (f : SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    Rest (evI F) (⇑f) r → f ≠ 0 → ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ g : SInf F (Fin n × Fin d),
      HasSum (fun ξ : Fin n × Fin d → F => M.co.rho ψ u (tens (evI F) (⇑g) r) (fun i => algebraMap F (AF F) (ξ i))) (T g) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ u f r hr hf
  obtain ⟨G, hG, hrG⟩ := exists_fin_of_rest hr hf
  set w := M.co.e u with hw
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
  let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
  let c : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let G' := finS ψ G (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)
  have hG' : G' ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := finS_mem ψ hψ.1 hG _ _ _
  obtain ⟨l, hl, hleq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  obtain ⟨T₀, hT₀⟩ := hl G' hG'
  let A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
    (SchwartzMap.smulLeftCLM ℂ (fun y : Fin n × Fin d → mixedEmbedding.mixedSpace F => eChar ((-trL c) y + -k))).comp
      (SchwartzMap.compSubConstCLM ℂ (-t))
  refine ⟨T₀.comp A, fun g => ?_⟩
  have hΦ : M.co.rho ψ u (tens (evI F) (⇑g) r) = pureA F (A g) G' := by
    rw [tens_eq_pureA g hrG]
    exact schr_pureA_eq ψ hψ w g G
  rw [hΦ]
  have hmem : pureA F (A g) G' ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨A g, G', hG', rfl⟩
  convert hasSum_thetaSum F hmem using 1
  rw [ContinuousLinearMap.comp_apply, ← hT₀, hleq _ hmem]

end GlobalTheory.ThetaSchrCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

noncomputable section
namespace GlobalTheory.ArchLocality

theorem evI_add {F : Type} [Field F] [NumberField F] (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul {F : Type} [Field F] [NumberField F] (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_fin {F : Type} [Field F] [NumberField F] : evI F ((0, 1) : AF F) = 0 :=
  map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem fst_eq_zero {F : Type} [Field F] [NumberField F] {a : AF F} (h : evI F a = 0) : a.1 = 0 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp h

theorem loc_chars : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) →
    ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ q ∈ s, ∀ i, evI F (q i) = 0) ∧
      ∑ q ∈ s, c q * ψ (y ⬝ᵥ q) = 1 ∧ ∀ x, (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x = 0 := GlobalTheory.T.exists_trigPolynomial_annihilating_adelicSchwartz

theorem snd_eq_zero_of_at {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have := congrArg Prod.snd (congrFun (hz (0, 1) evI_fin) i)
  change (((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 * (z i).2) = (0 : AF F).2 at this
  rw [one_mul] at this
  exact this

def intInd {F : Type} [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intInd_mem {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    intInd (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set B := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hB
  have hO : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
  have hK : IsCompact B := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hC : IsClosed B := hK.isClosed
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨_, hO, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]
  · refine ⟨_, hC.isOpen_compl, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem ref_fun : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ r₀ : (κ → AF F) → ℂ, (∀ x : κ → AF F, (∀ i, (x i).2 = 0) → r₀ x = 1) ∧
      ∀ f : SInf F κ, Rest (evI F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) r₀ := by
  intro F _ _ κ _
  refine ⟨fun x => intInd κ (fun i => (x i).2), fun x hx => ?_, fun f => ⟨fun x z hz => ?_, ?_⟩⟩
  · have : (fun i => (x i).2) = 0 := funext hx
    simp only [this, intInd]
    rw [Set.indicator_of_mem (show (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  · have : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at hz i, add_zero]
    simp only [this]
  · exact Submodule.subset_span ⟨f, intInd κ, intInd_mem κ, rfl⟩

theorem res_arch : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ,
    ∃ f : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
      Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), 0) : AF F)) = f t := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, _, rfl⟩ := h
    refine ⟨g 0 • f, fun t => ?_⟩
    simp only [pureA, RingEquiv.apply_symm_apply, SchwartzMap.smul_apply, smul_eq_mul]
    rw [mul_comm]
    rfl
  | zero => exact ⟨0, fun t => rfl⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨f₁, hf₁⟩ := h1
    obtain ⟨f₂, hf₂⟩ := h2
    exact ⟨f₁ + f₂, fun t => by
      show Φ₁ _ + Φ₂ _ = _
      rw [hf₁, hf₂, SchwartzMap.add_apply]⟩
  | smul a Φ _ h =>
    obtain ⟨f, hf⟩ := h
    exact ⟨a • f, fun t => by
      show a • Φ _ = _
      rw [hf, SchwartzMap.smul_apply]⟩

theorem comm_fin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (hW : M.IsWeil ψ χX χW om) (h : UA σ W.J) (hh : h ∈ UAt σ W (evI F))
    (u : AF F) (hu : evI F u = 0) (p q : Fin n × Fin d → AF F)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
      om (1, h) (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (om (1, h) Φ) := by
  have hS := IsUWeilPair.isUSplitting hW
  set w := M.co.e.symm (p, q) with hw
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (mat h - 1) = 0 := hh u hu
  have hact : actAB (cA σ) ((1, h) : UA σ X.J × UA σ W.J) (u • w) = u • w := by
    have h1 : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
    simp only [actAB]
    simpa [mat] using h1
  have h2 := hS.impl (1, h) (u • w) Φ hΦ
  simp only [Darboux.rho, he, hact] at h2
  exact h2

theorem fibre {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (y : κ → AF F) (hy : ∀ z, At (evI F) z → Φ (y + z) = 0) :
    T Φ y = 0 := by
  obtain ⟨s, c, hs, h1, h0⟩ := loc_chars ψ hψ Φ hΦ y hy
  have hch : ∀ q ∈ s, T (fun x => ψ (x ⬝ᵥ q) * Φ x) = fun x => ψ (x ⬝ᵥ q) * T Φ x := by
    intro q hq
    set u : AF F := (0, 1) with hu
    have hu0 : evI F u = 0 := evI_fin
    have huq : u • q = q := by
      funext i
      have hi := hs q hq i
      have hq1 : (q i).1 = 0 := fst_eq_zero hi
      refine Prod.ext ?_ ?_
      · show (0 : InfiniteAdeleRing F) * (q i).1 = (q i).1
        rw [hq1, zero_mul]
      · show (1 : FiniteAdeleRing (𝓞 F) F) * (q i).2 = (q i).2
        rw [one_mul]
    have e := hcomm u hu0 0 q Φ hΦ
    have hs0 : ∀ G : (κ → AF F) → ℂ, schr ψ (u • (0 : κ → AF F), u • q) G = fun x => ψ (x ⬝ᵥ q) * G x := by
      intro G; funext x; simp [schr, huq]
    rw [hs0, hs0] at e
    exact e
  have hsum : ∀ G : (κ → AF F) → ℂ, (fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * G x) =
      ∑ q ∈ s, c q • (fun x => ψ (x ⬝ᵥ q) * G x) := by
    intro G; funext x; simp [Finset.sum_mul, mul_assoc]
  have hT : T (fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x) = fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * T Φ x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, hsum, map_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [map_smul, hch q hq]
  have hz : (fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x) = 0 := funext h0
  rw [hz, map_zero] at hT
  have := congrFun hT y
  simp only [Pi.zero_apply, h1, one_mul] at this
  exact this.symm

end GlobalTheory.ArchLocality
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SrcLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable section
namespace GlobalTheory.MovedDict
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}

def srcLat (S : GridChoice W Set.univ) : ∀ p : GlobalTheory.ChiGrid.Pair T, FinPt G p.small → FinPt G p.big →
    Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E)
  | .chi i j, _, y => GlobalTheory.SumSize.latAt S (.grid (i + 1) j) y
  | .mu _ i j, x, _ => GlobalTheory.SumSize.latAt S (.grid i j) x
  | .core i, _, y => GlobalTheory.SumSize.latAt S (.core (i + 1)) y
  | .top _ j, x, _ => GlobalTheory.SumSize.latAt S (.top j) x

def tgtLat (S : GridChoice W Set.univ) : ∀ p : GlobalTheory.ChiGrid.Pair T, FinPt G p.small → FinPt G p.big →
    Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E)
  | .chi i j, x, _ => GlobalTheory.SumSize.latAt S (.grid i j) x
  | .mu _ i j, _, y => GlobalTheory.SumSize.latAt S (.grid i (j + 1)) y
  | .core i, x, _ => GlobalTheory.SumSize.latAt S (.core i) x
  | .top _ j, _, y => GlobalTheory.SumSize.latAt S (.top (j + 1)) y

end GlobalTheory.MovedDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKerPD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

variable {D : D7}

def kerPD (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A₁ : Fr W₁) (B : Fr X)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) {Pi : ModuleCat.{0} ℂ}
    (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) :
    Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :=
  Submodule.span ℂ {Φ₀D | Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧
    ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0}

theorem mem_kerPD {ψ : AddChar (AF D.host.F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (θ : InfFam D) {W W₁ X : HSp D}
    (A₁ : Fr W₁) (B : Fr X) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) {Pi : ModuleCat.{0} ℂ}
    (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) (Φ₀D : (Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :
    Φ₀D ∈ kerPD ψ θ A₁ B Bs Γ cB p' ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧
      ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  have hl := isDatum_linear Γ.M' ψ hψ (⇑cB)
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, hl.1, map_zero p'⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, Φx, hΦx, hDx, hpx⟩ := hx
    obtain ⟨hy1, Φy, hΦy, hDy, hpy⟩ := hy
    refine ⟨Submodule.add_mem _ hx1 hy1, Φx + Φy, Submodule.add_mem _ hΦx hΦy, ?_, by rw [map_add (f := _), hpx, hpy, add_zero]⟩
    have := hl.2 x y Φx Φy 1 hDx hDy
    simpa using this
  | smul c x _ hx =>
    obtain ⟨hx1, Φx, hΦx, hDx, hpx⟩ := hx
    refine ⟨Submodule.smul_mem _ c hx1, c • Φx, Submodule.smul_mem _ c hΦx, ?_, by rw [map_smul, hpx, smul_zero]⟩
    have := hl.2 0 x 0 Φx c hl.1 hDx
    simpa using this

end GlobalTheory.SquareAgree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def fnOf {t : T} (d : PureDat G t) : ∀ a, FactorFn G t a
  | .inl j => (d.1 j).fn
  | .inr i => (d.2 i).fn

def movFn (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) : ∀ a, FactorFn G t a :=
  Function.update
    (Function.update v (.inr ⟨j, by omega⟩)
      (fun x => v (.inr ⟨j, by omega⟩)
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 x) :
        FactorFn G t (.inr ⟨j, by omega⟩)))
    (.inr ⟨j + 1, hj⟩)
    (fun x => v (.inr ⟨j + 1, hj⟩)
        (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 x) :
        FactorFn G t (.inr ⟨j + 1, hj⟩))

def scaleAt (j : ℕ) (hj : j + 1 < D.R.m) (c₁ c₂ : ℂ) : Fin D.R.m ⊕ Fin D.R.m → ℂ :=
  Function.update (Function.update (fun _ => 1) (.inr ⟨j, by omega⟩) c₁) (.inr ⟨j + 1, hj⟩) c₂

end GlobalTheory.RowVertexInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TprodNeZeroOfNe
noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.Contr

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]


omit [CompleteSpace H₁] [CompleteSpace FF] in
theorem norm_isoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem exists_isContr {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃ It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  let L : H₂ → (H₁ →L[ℂ] FF) := fun y =>
    (Tm.flip y).mkContinuous ‖y‖ fun x => by simp [norm_isoBilin hI, mul_comm]
  let f : FF → H₂ → H₁ := fun φ y => ContinuousLinearMap.adjoint (L y) φ
  have hf : ∀ φ y x, ⟪x, f φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := fun φ y x => by
    simp only [f, ContinuousLinearMap.adjoint_inner_right]
    rfl
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) f ?_ ?_ ?_ ?_, hf⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, RingHom.id_apply]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf, map_add (f := _), inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, map_smul, inner_smul_left]


omit [CompleteSpace H₁] [CompleteSpace FF] in
theorem isContr_unique {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} {It It' : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁}
    (h : IsContr Tm It) (h' : IsContr Tm It') : It = It' := by
  ext φ y
  exact ext_inner_left ℂ fun x => by rw [h, h']

end Hilbert

theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  obtain ⟨It, hIt⟩ := exists_isContr hI
  exact ⟨⟨It, hIt, fun It' h' => isContr_unique h' hIt⟩, fun It' h' => contrProps_of hI hE h'⟩

theorem tprod_ne_zero_of_ne {ι : Type} [Fintype ι] {B : ι → Type} [∀ τ, AddCommGroup (B τ)]
    [∀ τ, Module ℂ (B τ)] (w : ∀ τ, B τ) (hw : ∀ τ, w τ ≠ 0) : PiTensorProduct.tprod ℂ w ≠ 0 := by
  classical
  have : ∀ τ, ∃ f : Module.Dual ℂ (B τ), f (w τ) ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hw τ ((Module.forall_dual_apply_eq_zero_iff ℂ (w τ)).1 hc)
  choose f hf using this
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f)) h
  simp [Finset.prod_eq_zero_iff, hf] at this

theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ Itl
  classical
  have hinj : ∀ τ, Function.Injective fun s : σ τ => e ⟨τ, s⟩ := fun τ =>
    e.injective.comp sigma_mk_injective
  let r : (Var →₀ ℕ) → ∀ τ, σ τ →₀ ℕ := fun m τ => m.comapDomain (fun s => e ⟨τ, s⟩) (hinj τ).injOn
  let It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ :=
    (MvPolynomial.basisMonomials Var ℂ).constr ℂ fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1)
  have hr : ∀ m : ∀ τ, σ τ →₀ ℕ, r (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩) = m := by
    intro m
    funext τ
    ext s
    simp only [r, Finsupp.comapDomain_apply, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single τ]
    · exact Finsupp.mapDomain_apply_of_injective (hinj τ) _ _
    · intro τ' _ hne
      apply Finsupp.mapDomain_notin_range
      rintro ⟨s', hs'⟩
      exact hne (congrArg Sigma.fst (e.injective hs'))
    · simp
  have key : It.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun τ => (MvPolynomial.rename (fun s : σ τ => e ⟨τ, s⟩)).toLinearMap) =
      (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap Itl := by
    apply Module.Basis.ext_multilinear fun τ => MvPolynomial.basisMonomials (σ τ) ℂ
    intro m
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials,
      MvPolynomial.rename_monomial, PiTensorProduct.mapMultilinear_apply]
    rw [← MvPolynomial.monomial_sum_one]
    have := (MvPolynomial.basisMonomials Var ℂ).constr_basis ℂ (fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1))
      (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩)
    rw [hr] at this
    simpa [It] using this
  have hT : IsTensorIt e Itl It := by
    intro P v
    have := congrArg (fun F => F P (PiTensorProduct.tprod ℂ v)) key
    simpa using this
  refine ⟨It, hT, fun hne h0 => ?_⟩
  have : ∀ τ, ∃ P v, Itl τ P v ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hne τ (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using this
  apply tprod_ne_zero_of_ne _ hPv
  rw [← hT P v, h0]
  rfl

theorem contraction : Contraction := ⟨contrHilbert, contrTensor⟩

end GlobalTheory.Contr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.Published GlobalTheory.Chain.RealIt

namespace GlobalTheory.Chain.ItPairObj

theorem exists_record (hD : DiscreteSeriesCover) (hH : HarishChandraModules) :
    ∃ X : ProvA, ChosenSeries X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X := by
  obtain ⟨X, hX⟩ := GlobalTheory.exists_provA_of_forall_exists_hasParam (GlobalTheory.CoverDS.exists_hasParam hD)
  have a1 : admH1 X := GlobalTheory.FockDeg.degrees_and_adjoints X
  have a2 : admH2 X := GlobalTheory.JointHarm.fock_polynomials X
  have a3 : DiscreteSeriesBlattner X := GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hD X hX
  have a5 : admQ5 X := hH.admQ5_of_harishChandraModules X
  have a6 : CoverHaarIntegration X := GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover X
  have a7 : admQ7 := GlobalTheory.TensorHW.highestWeight_tensor
  have a8 : admQ8 := GlobalTheory.InducedPBW.pbw_induced
  have a4 : DiscreteSeriesPositivity X := GlobalTheory.SphJet.lowest_type_positive_and_decays X a3 a5 a7 a8
  have h1 := GlobalTheory.T.doublingIntegral_jointHarmonic_pos X a1 a2 a3 a4 a5 a6 a7 a8
  exact ⟨X, hX, h1, GlobalTheory.T.fockSpace_contains_discreteSeriesTensor X a1 a2 a3 a4 a5 a6 a7 a8 h1⟩

theorem itPair_of_rows (hD : DiscreteSeriesCover) (hH : HarishChandraModules) (D : D7)
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D) (hV : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D) (hC : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction) : ItPair D := by
  obtain ⟨X, hX, h1, h2⟩ := exists_record hD hH
  exact itPair D X hX h1 h2 hF hV hB hC

theorem itPair_holds (hD : DiscreteSeriesCover) (hH : HarishChandraModules) (D : D7) : ItPair D :=
  itPair_of_rows hD hH D (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D) (GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D) (GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D) GlobalTheory.Contr.contraction

end GlobalTheory.Chain.ItPairObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItPair D := by
  first | exact @GlobalTheory.Chain.ItPairObj.itPair_holds | exact GlobalTheory.Chain.ItPairObj.itPair_holds | (intros; apply GlobalTheory.Chain.ItPairObj.itPair_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfThetaDistributionHeisenbergTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfThetaDistributionHeisenbergTranslates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ThetaSeparates

theorem eq_zero_of_thetaSum_rho : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
    (∀ u, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u Φ) = 0) → Φ = 0 := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Φ hΦ h
  classical
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  obtain ⟨𝓕₁, hF, h0, htop⟩ := GlobalTheory.RatVecDomain.exists_fundamentalDomain F (Fin n × Fin d) μ inferInstance
  funext x
  have hP := GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq F ψ (GlobalTheory.StdCharFromIsStd.isCharAF hψ)
    (Fin n × Fin d) μ inferInstance 𝓕₁ hF htop Φ hΦ x
  have hz : ∀ y, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ) = 0 := by
    intro y
    have := h (M.co.e.symm (x, y))
    simpa [GlobalTheory.WeilM.Darboux.rho] using this
  simp only [hz, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, MeasureTheory.lintegral_zero] at hP
  have hs := (mul_eq_zero.mp hP.symm).resolve_left h0
  have h1 := ENNReal.tsum_eq_zero.mp hs 0
  have e : ((fun _ => (0 : AF F)) : Fin n × Fin d → AF F) + x = x := zero_add x
  simp only [map_zero, enorm_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at h1
  simpa [e] using h1

end GlobalTheory.ThetaSeparates
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfThetaDistributionHeisenbergTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_thetaDistribution_heisenbergTranslates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
    (∀ u, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u Φ) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.ThetaSeparates.eq_zero_of_thetaSum_rho | exact GlobalTheory.ThetaSeparates.eq_zero_of_thetaSum_rho | (intros; apply GlobalTheory.ThetaSeparates.eq_zero_of_thetaSum_rho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def colPt (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    GA D (G.pS (.top t (lastIx D))) × GA D (G.pT (.top t (lastIx D))) :=
  G.toPair (.top t (lastIx D)) 1 (topLast ((S.N.u (.top D.R.m))⁻¹ * g * S.N.u (.top D.R.m))).1

theorem colShift_eq (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    colShift S t g = W.om _ (colPt S t g) := rfl

def rowPt (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    GA D (G.pS (.chi (lastIx D) D.R.m : Pair T)) × GA D (G.pT (.chi (lastIx D) D.R.m : Pair T)) :=
  G.toPair (.chi (lastIx D) D.R.m) 1 (gridLast ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m))).1

theorem rowShift_eq (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    rowShift S k = W.om (.chi (lastIx D) D.R.m) (rowPt S k) := rfl

def stdLat (S : GridChoice W U) (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) :=
  latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True

end GlobalTheory.LastVertexMove

namespace GlobalTheory.LastVertexMove

variable {D : D7}

def moveFn {A B : HSp D} (q : GA D A × GA D B) (Φ : WO A B → ℂ) : WO A B → ℂ := fun x => Φ (actO A B q.1⁻¹ q.2⁻¹ x)

end GlobalTheory.LastVertexMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions : ∀ {D : D7} (m n : ℕ), n ≤ m → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (u : Matrix (Fin m) (Fin n) (EAf D)) (γ : GL (Fin n) (EAf D)), IsIntM u → IsIntM (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1) → (∀ i j, toEAf D e * u i j = u i j) → (∀ PP ∈ Z, IsUnit (topL n (redM PP u)).det) → (∀ PP ∈ Z, IsUnit (topL n (redM PP (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1))).det) → IsIntM (toEAf D e • γ.1) ∧ IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) ∧ ∀ PP ∈ Z, topL n (redM PP (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1)) * redM PP (toEAf D e • γ.1) = topL n (redM PP u) := by
  first | exact @GlobalTheory.HalfUnit.int_of_unit_tops | exact GlobalTheory.HalfUnit.int_of_unit_tops | (intros; apply GlobalTheory.HalfUnit.int_of_unit_tops <;> assumption)
end
