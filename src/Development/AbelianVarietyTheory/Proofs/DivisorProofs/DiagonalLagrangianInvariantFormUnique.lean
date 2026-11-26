module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedEqDiagonalLagrangianThetaIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaReNonneg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalProjectionSectionIsotropicSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalProjectionSectionIsotropicSpan
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 200000 in
theorem rational_proj_section_of_span : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ P Q : Matrix κ κ F,
      (∀ s ∈ S, (P.map (algebraMap F (AF F))) *ᵥ s.1 = 0) ∧
      (∀ s ∈ S, (s.1, (Q.map (algebraMap F (AF F))) *ᵥ s.1) ∈ S) ∧
      (∀ ξ : κ → F, P *ᵥ ξ = 0 →
        ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((Q *ᵥ ξ) i))) ∈ S) := by
  intro F _ _ κ _ S hS
  classical
  let ι := algebraMap F (AF F)
  let Φ : ((κ → F) × (κ → F)) →ₗ[F] ((κ → AF F) × (κ → AF F)) :=
    LinearMap.prodMap ((Algebra.linearMap F (AF F)).compLeft κ) ((Algebra.linearMap F (AF F)).compLeft κ)
  let T : Submodule F ((κ → F) × (κ → F)) := (S.restrictScalars F).comap Φ
  have hT : ∀ y z, (y, z) ∈ T ↔ ((fun i => ι (y i)), (fun i => ι (z i))) ∈ S := fun y z => Iff.rfl
  let f : T →ₗ[F] (κ → F) := LinearMap.fst F _ _ ∘ₗ T.subtype
  let L₁ := LinearMap.range f
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl L₁
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  let π : (κ → F) →ₗ[F] (κ → F) := C.subtype ∘ₗ Submodule.linearProjOfIsCompl C L₁ hC.symm
  let q : (κ → F) →ₗ[F] (κ → F) := LinearMap.snd F _ _ ∘ₗ T.subtype ∘ₗ g ∘ₗ Submodule.linearProjOfIsCompl L₁ C hC
  have hπ : ∀ y, π y = 0 ↔ y ∈ L₁ := by
    intro y
    simp only [π, LinearMap.comp_apply, Submodule.coe_subtype, ZeroMemClass.coe_eq_zero]
    exact Submodule.linearProjOfIsCompl_apply_eq_zero_iff hC.symm
  have hq : ∀ y ∈ L₁, (y, q y) ∈ T := by
    intro y hy
    have h1 : Submodule.linearProjOfIsCompl L₁ C hC y = ⟨y, hy⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨y, hy⟩
    have h2 : f.rangeRestrict (g ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hg ⟨y, hy⟩
    have h3 : ((g ⟨y, hy⟩ : T) : (κ → F) × (κ → F)).1 = y := by
      have := congrArg Subtype.val h2
      simpa [f] using this
    have hm := (g ⟨y, hy⟩).2
    have e : ((g ⟨y, hy⟩ : T) : (κ → F) × (κ → F)) = (y, q y) := by
      ext1
      · exact h3
      · simp [q, h1]
    rw [← e]; exact hm
  have hL : ∀ y z, (y, z) ∈ T → y ∈ L₁ := fun y z h => ⟨⟨(y, z), h⟩, rfl⟩
  have hmv : ∀ (M : Matrix κ κ F) (v : κ → F),
      (M.map ι) *ᵥ (fun i => ι (v i)) = fun i => ι ((M *ᵥ v) i) := by
    intro M v; funext i
    exact (RingHom.map_mulVec ι M v i).symm
  refine ⟨LinearMap.toMatrix' π, LinearMap.toMatrix' q, ?_, ?_, ?_⟩
  · intro s hs
    let A : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] (κ → AF F) :=
      (Matrix.mulVecLin ((LinearMap.toMatrix' π).map ι)) ∘ₗ LinearMap.fst _ _ _
    have hle : Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
        s = (fun i => ι (y i), fun i => ι (z i))} ≤ LinearMap.ker A := by
      rw [Submodule.span_le]
      rintro _ ⟨hs', y, z, rfl⟩
      have hy : y ∈ L₁ := hL y z hs'
      have h0 : π y = 0 := (hπ y).2 hy
      show (LinearMap.toMatrix' π).map ι *ᵥ (fun i => ι (y i)) = 0
      rw [hmv, LinearMap.toMatrix'_mulVec, h0]
      funext i; simp
    exact hle (hS hs)
  · intro s hs
    let B : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F)) :=
      LinearMap.prod (LinearMap.fst _ _ _)
        ((Matrix.mulVecLin ((LinearMap.toMatrix' q).map ι)) ∘ₗ LinearMap.fst _ _ _)
    have hle : Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
        s = (fun i => ι (y i), fun i => ι (z i))} ≤ S.comap B := by
      rw [Submodule.span_le]
      rintro _ ⟨hs', y, z, rfl⟩
      have hy : y ∈ L₁ := hL y z hs'
      show ((fun i => ι (y i)), (LinearMap.toMatrix' q).map ι *ᵥ (fun i => ι (y i))) ∈ S
      rw [hmv, LinearMap.toMatrix'_mulVec]
      exact hq y hy
    exact hle (hS hs)
  · intro ξ hξ
    rw [LinearMap.toMatrix'_mulVec] at hξ
    have hx : ξ ∈ L₁ := (hπ ξ).1 hξ
    rw [LinearMap.toMatrix'_mulVec]
    exact hq ξ hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalProjectionSectionIsotropicSpanStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_projection_section_isotropicSpan : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ P Q : Matrix κ κ F,
      (∀ s ∈ S, (P.map (algebraMap F (AF F))) *ᵥ s.1 = 0) ∧
      (∀ s ∈ S, (s.1, (Q.map (algebraMap F (AF F))) *ᵥ s.1) ∈ S) ∧
      (∀ ξ : κ → F, P *ᵥ ξ = 0 →
        ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((Q *ᵥ ξ) i))) ∈ S) := by
  first | exact @GlobalTheory.rational_proj_section_of_span | exact GlobalTheory.rational_proj_section_of_span | (intros; apply GlobalTheory.rational_proj_section_of_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegAdelicSchwartzBumpTest
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegAdelicSchwartzBumpTest
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

open Topology Filter

namespace GlobalTheory.AdelicBumpTest

theorem exists_nonneg_test : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : Set (κ → AF F)), U ∈ nhds 0 →
    ∃ Φ ∈ schA F κ, Continuous Φ ∧ (∀ x, Φ x ≠ 0 → x ∈ U) ∧ (∀ x, (Φ x).im = 0 ∧ 0 ≤ (Φ x).re) ∧ Φ 0 = 1 := by
  intro F _ _ κ _ U hU
  classical
  let e' : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have he' : Continuous e' := continuous_pi fun i =>
    ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst)).prodMk
      ((continuous_apply i).comp continuous_snd)
  have he'0 : e' (0, 0) = 0 := by
    funext i
    refine Prod.ext ?_ rfl
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
    exact map_zero _
  have hpre : e' ⁻¹' U ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → FiniteAdeleRing (𝓞 F) F)) :=
    he'.continuousAt.preimage_mem_nhds (by rw [he'0]; exact hU)
  obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV₁

  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ y, f y = ((b y : ℝ) : ℂ) := fun y => rfl

  obtain ⟨L, hLo, hLc, hL⟩ : ∃ L : AddSubgroup (FiniteAdeleRing (𝓞 F) F), IsOpen (L : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact (L : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, u i ∈ L) → u ∈ V₂ := by
    let q := Fintype.equivFin κ
    have hc : Continuous fun (u : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) (i : κ) => u (q i) :=
      continuous_pi fun i => continuous_apply _
    have hV' : (fun (u : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) (i : κ) => u (q i)) ⁻¹' V₂ ∈
        𝓝 (0 : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) :=
      hc.continuousAt.preimage_mem_nhds hV₂
    obtain ⟨L, hLo, hLc, hL⟩ := GlobalTheory.SWQ.FinAnnih.basis_nhds (F := F) _ hV'
    refine ⟨L, hLo, hLc, fun u hu => ?_⟩
    have := hL (fun l => u (q.symm l)) fun l => hu _
    simpa using this
  let S : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.pi Set.univ fun _ => (L : Set (FiniteAdeleRing (𝓞 F) F))
  have hSo : IsOpen S := isOpen_set_pi Set.finite_univ fun _ _ => hLo
  have hSc : IsClosed S := isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen L hLo
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := S.indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨?_, ?_⟩
    · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
      by_cases hx : x ∈ S
      · exact ⟨S, hSo, hx, fun y hy => by simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩
      · exact ⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
    · exact HasCompactSupport.intro (isCompact_univ_pi fun _ => hLc) fun x hx => Set.indicator_of_notMem hx _
  refine ⟨pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact (f.continuous.comp (continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp
      (continuous_fst.comp (continuous_apply i)))).mul
      (hg.1.continuous.comp (continuous_pi fun i => continuous_snd.comp (continuous_apply i)))
  · intro x hx
    have hx1 : f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ≠ 0 := left_ne_zero_of_mul hx
    have hx2 : g (fun i => (x i).2) ≠ 0 := right_ne_zero_of_mul hx
    have hb : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ∈ V₁ := by
      refine hball ?_
      rw [← b.support_eq]
      intro h0
      apply hx1
      rw [hf, h0]; simp
    have hS : (fun i => (x i).2) ∈ S := by
      by_contra h
      exact hx2 (Set.indicator_of_notMem h _)
    have hmem := hsub (Set.mk_mem_prod hb (hL _ fun i => hS i (Set.mem_univ i)))
    have hxe : e' ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1), fun i => (x i).2) = x := by
      funext i
      refine Prod.ext ?_ rfl
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
    rw [← hxe]
    exact hmem
  · intro x
    show (f _ * g _).im = 0 ∧ 0 ≤ (f _ * g _).re
    rw [hf]
    by_cases h : (fun i => (x i).2) ∈ S
    · simp only [g, Set.indicator_of_mem h, Pi.one_apply, mul_one, Complex.ofReal_im, Complex.ofReal_re, true_and]
      exact b.nonneg
    · simp only [g, Set.indicator_of_notMem h, mul_zero, Complex.zero_im, Complex.zero_re, le_refl, and_self]
  · show f _ * g _ = 1
    have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
      funext i
      exact map_zero _
    have hS0 : (fun i => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ S := fun i _ => L.zero_mem
    rw [h0, hf, b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε).le)]
    simp only [g, Set.indicator_of_mem hS0, Pi.one_apply, Complex.ofReal_one, mul_one]

end GlobalTheory.AdelicBumpTest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegAdelicSchwartzBumpTestStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonneg_adelicSchwartz_bump_test : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : Set (κ → AF F)), U ∈ nhds 0 →
    ∃ Φ ∈ schA F κ, Continuous Φ ∧ (∀ x, Φ x ≠ 0 → x ∈ U) ∧ (∀ x, (Φ x).im = 0 ∧ 0 ≤ (Φ x).re) ∧ Φ 0 = 1 := by
  first | exact @GlobalTheory.AdelicBumpTest.exists_nonneg_test | exact GlobalTheory.AdelicBumpTest.exists_nonneg_test | (intros; apply GlobalTheory.AdelicBumpTest.exists_nonneg_test <;> assumption)
end
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaPosIso

theorem disc (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ D ∈ nhds (0 : κ → AF F), ∀ ξ : κ → F, (fun i => algebraMap F (AF F) (ξ i)) ∈ D → ξ = 0 := by
  have hd := GroundTheory.Global.discreteTopology_principalSubgroup F
  have ho : IsOpen ({0} : Set (AdeleRing.principalSubgroup (𝓞 F) F)) := isOpen_discrete _
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.mp ho
  refine ⟨Set.pi Set.univ fun _ => t, set_pi_mem_nhds Set.finite_univ fun _ _ => ht.mem_nhds ?_, ?_⟩
  · have h0 : ((0 : AdeleRing.principalSubgroup (𝓞 F) F) : AF F) ∈ t := by
      have : (0 : AdeleRing.principalSubgroup (𝓞 F) F) ∈ Subtype.val ⁻¹' t := by rw [hpre]; rfl
      exact this
    simpa using h0
  · intro ξ hξ
    funext i
    have hm : algebraMap F (AF F) (ξ i) ∈ AdeleRing.principalSubgroup (𝓞 F) F := ⟨ξ i, rfl⟩
    have : (⟨_, hm⟩ : AdeleRing.principalSubgroup (𝓞 F) F) ∈ Subtype.val ⁻¹' t := hξ i (Set.mem_univ _)
    rw [hpre] at this
    have h2 : algebraMap F (AF F) (ξ i) = 0 := congrArg Subtype.val this
    exact (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F) (h2.trans (map_zero _).symm)


set_option maxHeartbeats 1000000 in
theorem exists_theta_re_nonneg : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    (∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2) →
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ Φ ∈ schA F κ, Continuous (fun w => thetaSum F (schr ψ w Φ)) ∧
      (∀ s ∈ S, 0 ≤ (thetaSum F (schr ψ s Φ)).re) ∧ 0 < (thetaSum F (schr ψ 0 Φ)).re := by
  intro F _ _ ψ hψ κ _ S hiso hspan
  classical
  obtain ⟨P, Q, hP, hQ, hker⟩ := GlobalTheory.T.exists_rational_projection_section_isotropicSpan F κ S hspan
  obtain ⟨D, hD, hDξ⟩ := disc F κ
  set PA := P.map (algebraMap F (AF F)) with hPA
  set QA := Q.map (algebraMap F (AF F)) with hQA
  obtain ⟨g, hgdef⟩ : ∃ g : (κ → AF F) → ℂ, g = fun x => ψ (⅟(2 : AF F) * (x ⬝ᵥ (QA *ᵥ x))) := ⟨_, rfl⟩
  have hg : Continuous g := by
    rw [hgdef]
    exact hψ.1.comp (continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)))
  have hg0 : 0 < (g 0).re := by simp [hgdef]
  obtain ⟨V₀, hV₀, hq⟩ := exists_nhds_zero_quarter hD
  obtain ⟨V, hV, hVm⟩ : ∃ V ∈ nhds (0 : κ → AF F), ∀ x ∈ V, x ∈ V₀ ∧ -x ∈ V₀ ∧ PA *ᵥ x ∈ D ∧ 0 < (g x).re := by
    open scoped Pointwise in
    refine ⟨((V₀ ∩ -V₀) ∩ (fun x => PA *ᵥ x) ⁻¹' D) ∩ {x | 0 < (g x).re}, ?_, fun x hx => ⟨hx.1.1.1, Set.mem_neg.mp hx.1.1.2, hx.1.2, hx.2⟩⟩
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hV₀ (neg_mem_nhds_zero _ hV₀)) ?_) ?_
    · exact (continuous_const.matrix_mulVec continuous_id).tendsto' (0 : κ → AF F) 0 (by simp) hD
    · exact ((Complex.continuous_re.comp hg).tendsto 0).eventually (lt_mem_nhds hg0)
  obtain ⟨Φ, hΦS, hΦc, hΦV, hΦr, hΦ0⟩ := GlobalTheory.T.exists_nonneg_adelicSchwartz_bump_test F κ V hV
  have hsub : ∀ ξ ξ' : κ → F, (fun i => algebraMap F (AF F) ((ξ - ξ') i)) =
      (fun i => algebraMap F (AF F) (ξ i)) - (fun i => algebraMap F (AF F) (ξ' i)) := by
    intro ξ ξ'; funext i; simp [map_sub]
  have KEY : ∀ ξ : κ → F, ∀ v₁ ∈ V, ∀ v₂ ∈ V, ∀ v₃ ∈ V, ∀ v₄ ∈ V,
      (fun i => algebraMap F (AF F) (ξ i)) = v₁ - v₂ - (v₃ - v₄) → ξ = 0 := by
    intro ξ v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ he
    apply hDξ
    rw [he, show v₁ - v₂ - (v₃ - v₄) = v₁ + -v₂ + -v₃ + v₄ by abel]
    exact hq (hVm _ h₁).1 (hVm _ h₂).2.1 (hVm _ h₃).2.1 (hVm _ h₄).1
  have hV0 : (0 : κ → AF F) ∈ V := mem_of_mem_nhds hV
  have LOC : ∀ a₀ : κ → AF F, ∃ ξ₀ : κ → F, ∀ᶠ a in nhds a₀, ∀ ξ : κ → F, ξ ≠ ξ₀ →
      Φ ((fun i => algebraMap F (AF F) (ξ i)) + a) = 0 := by
    intro a₀
    have hnear : ∀ᶠ a in nhds a₀, a - a₀ ∈ V :=
      (continuous_id.sub continuous_const).tendsto' a₀ 0 (sub_self a₀) hV
    by_cases h : ∃ ξ₀ : κ → F, ∃ v₁ ∈ V, ∃ v₂ ∈ V, (fun i => algebraMap F (AF F) (ξ₀ i)) + a₀ = v₁ - v₂
    · obtain ⟨ξ₀, v₁, h₁, v₂, h₂, he⟩ := h
      refine ⟨ξ₀, ?_⟩
      filter_upwards [hnear] with a ha ξ hne
      by_contra hz
      apply hne
      rw [← sub_eq_zero]
      refine KEY _ _ (hΦV _ hz) _ ha _ h₁ _ h₂ ?_
      rw [hsub, ← he]; abel
    · refine ⟨0, ?_⟩
      filter_upwards [hnear] with a ha ξ _
      by_contra hz
      exact h ⟨ξ, _, hΦV _ hz, _, ha, by abel⟩
  have THETA : ∀ w : (κ → AF F) × (κ → AF F), ∃ ξ₀ : κ → F, ∀ᶠ w' in nhds w,
      thetaSum F (schr ψ w' Φ) = ψ ((fun i => algebraMap F (AF F) (ξ₀ i)) ⬝ᵥ w'.2 + ⅟(2 : AF F) * (w'.1 ⬝ᵥ w'.2)) *
        Φ ((fun i => algebraMap F (AF F) (ξ₀ i)) + w'.1) := by
    intro w
    obtain ⟨ξ₀, h⟩ := LOC w.1
    refine ⟨ξ₀, ?_⟩
    filter_upwards [(continuous_fst.tendsto w).eventually h] with w' hw'
    exact tsum_eq_single ξ₀ fun ξ hne => mul_eq_zero_of_right _ (hw' ξ hne)
  have htwo : ⅟(2 : AF F) = algebraMap F (AF F) (2⁻¹ : F) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨Φ, hΦS, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun w => ?_
    obtain ⟨ξ₀, h⟩ := THETA w
    refine ContinuousAt.congr ?_ (h.mono fun _ h => h.symm)
    refine Continuous.continuousAt ?_
    exact (hψ.1.comp ((continuous_const.dotProduct continuous_snd).add
      (continuous_const.mul (continuous_fst.dotProduct continuous_snd)))).mul
      (hΦc.comp (continuous_const.add continuous_fst))
  · intro s hs
    obtain ⟨ξ₀, h⟩ := THETA s
    rw [h.self_of_nhds]
    set e : κ → AF F := fun i => algebraMap F (AF F) (ξ₀ i) with he
    by_cases hz : Φ (e + s.1) = 0
    · simp [hz]
    have hx : e + s.1 ∈ V := hΦV _ hz
    have hP0 : P *ᵥ ξ₀ = 0 := by
      apply hDξ
      have h1 := (hVm _ hx).2.2.1
      simp only [Matrix.mulVec_add, hP s hs, add_zero] at h1
      convert h1 using 1
      funext i
      exact RingHom.map_mulVec _ _ _ _
    set f : κ → AF F := fun i => algebraMap F (AF F) ((Q *ᵥ ξ₀) i) with hf
    have hef : (e, f) ∈ S := hker ξ₀ hP0
    have hac : (s.1, QA *ᵥ s.1) ∈ S := hQ s hs
    have hQe : QA *ᵥ e = f := by
      funext i
      exact (RingHom.map_mulVec _ _ _ _).symm
    have h1 := hiso s hs _ hac
    have h2 := hiso _ hef s hs
    have h3 := hiso _ hef _ hac
    simp only at h1 h2 h3
    have hrat : e ⬝ᵥ f = algebraMap F (AF F) (ξ₀ ⬝ᵥ (Q *ᵥ ξ₀)) := (RingHom.map_dotProduct _ _ _).symm
    have hinv : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self _
    have phase : e ⬝ᵥ s.2 + ⅟(2 : AF F) * (s.1 ⬝ᵥ s.2) =
        ⅟(2 : AF F) * ((e + s.1) ⬝ᵥ (QA *ᵥ (e + s.1))) + algebraMap F (AF F) (-(2⁻¹ * (ξ₀ ⬝ᵥ (Q *ᵥ ξ₀)))) := by
      rw [Matrix.mulVec_add, hQe, add_dotProduct, dotProduct_add, dotProduct_add, map_neg, map_mul, ← htwo, ← hrat]
      linear_combination h2 - ⅟(2 : AF F) * h3 - ⅟(2 : AF F) * h1 - (s.1 ⬝ᵥ f) * hinv
    rw [phase, AddChar.map_add_eq_mul, hψ.2.1, mul_one, Complex.mul_re, (hΦr _).1, mul_zero, sub_zero]
    have hpos := (hVm _ hx).2.2.2
    rw [hgdef] at hpos
    exact mul_nonneg (le_of_lt hpos) (hΦr _).2
  · have hz : ∀ ξ : κ → F, ξ ≠ 0 → Φ ((fun i => algebraMap F (AF F) (ξ i)) + (0 : (κ → AF F) × (κ → AF F)).1) = 0 := by
      intro ξ hne
      by_contra hz
      exact hne (KEY ξ _ (hΦV _ hz) 0 hV0 0 hV0 0 hV0 (by simp))
    have e0 : (fun i => algebraMap F (AF F) ((0 : κ → F) i)) = 0 := by funext i; simp
    have hsum : thetaSum F (schr ψ 0 Φ) = schr ψ 0 Φ (fun i => algebraMap F (AF F) ((0 : κ → F) i)) :=
      tsum_eq_single 0 fun ξ hne => mul_eq_zero_of_right _ (hz ξ hne)
    rw [hsum, e0]
    simp only [schr, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      one_mul, hΦ0, Complex.one_re]
    norm_num

end GlobalTheory.ThetaPosIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensDiagEqZero
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilDiagIso

theorem hTens_diag_eq_zero {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ}
    (c : A →ₐ[R] A) (JA : Matrix (Fin (n + n)) (Fin (n + n)) A) (JB : Matrix (Fin m) (Fin m) A)
    (x y : Matrix (Fin (n + n)) (Fin m) A)
    (hx : ∀ i j, x (Fin.natAdd n i) j = x (Fin.castAdd n i) j)
    (hy : ∀ i j, y (Fin.natAdd n i) j = y (Fin.castAdd n i) j)
    (h1 : ∀ i k, JA (Fin.castAdd n i) (Fin.natAdd n k) = 0)
    (h2 : ∀ i k, JA (Fin.natAdd n i) (Fin.castAdd n k) = 0)
    (h3 : ∀ i k, JA (Fin.natAdd n i) (Fin.natAdd n k) = - JA (Fin.castAdd n i) (Fin.castAdd n k)) :
    hTens c JA JB x y = 0 := by
  unfold hTens
  simp only [Fin.sum_univ_add, hx, hy, h1, h2, h3, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, add_neg_cancel]

theorem symp_diag_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
    (u u' : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)),
    symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)
      (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u)
      (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u') = 0 := by
  intro F E _ _ _ _ _ σ nS nT JT JB ξ u u'
  unfold symp
  rw [hTens_diag_eq_zero]
  · simp
  · intro i j
    simp [Matrix.mul_apply, diagCols, -Fin.natAdd_eq_addNat]
  · intro i j
    simp [Matrix.mul_apply, diagCols, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]

end GlobalTheory.WeilDiagIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixMemSpanIncM
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory

theorem matrix_mem_span_incM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    (u : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)),
    u ∈ Submodule.span (AF F) (Set.range (incM F : Matrix (Fin m) (Fin n) E → Matrix (Fin m) (Fin n) (AF F ⊗[F] E))) := by
  intro F E _ _ _ _ _ m n u
  classical
  rw [Matrix.matrix_eq_sum_single u]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  generalize u i j = a
  induction a using TensorProduct.induction_on with
  | zero => rw [Matrix.single_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [Matrix.single_add]; exact Submodule.add_mem _ hx hy
  | tmul a e =>
    have h : Matrix.single i j (a ⊗ₜ[F] e) = a • incM F (Matrix.single i j e) := by
      ext k l
      simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.single, Matrix.of_apply]
      split_ifs
      · change _ = a • ((1 : AF F) ⊗ₜ[F] e)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · simp
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagLagrangian
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DiagLagr

def fold (n : ℕ) (i : Fin (n + n)) : Fin n := Sum.elim id id (finSumFinEquiv.symm i)

theorem diagCols_mul {A : Type} [CommRing A] {n m : ℕ} (u : Matrix (Fin n) (Fin m) A) :
    ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A).submatrix finSumFinEquiv.symm id) * u =
      u.submatrix (fold n) id := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i <;>
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, fold, Equiv.symm_apply_apply] <;>
    simp [diagCols, Matrix.one_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_fold (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (JB : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) (u v : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)) :
    hTens (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)ᵀ) JB (u.submatrix (fold n) id)
      (v.submatrix (fold n) id) = 0 := by
  simp only [hTens, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.submatrix_apply, fold,
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG, incM, Matrix.map_apply, Matrix.transpose_apply, Matrix.reindex_apply,
    Equiv.symm_apply_apply, id]
  simp [dbl]

def repL (F : Type) [Field F] [NumberField F] [Algebra F E] (n m : ℕ) :
    Matrix (Fin n) (Fin m) E →ₗ[F] Matrix (Fin (n + n)) (Fin m) (AF F ⊗[F] E) where
  toFun x := (incM F x).submatrix (fold n) id
  map_add' x y := by ext i j; simp [incM]
  map_smul' a x := by
    ext i j
    simp [incM, inclR, TensorProduct.tmul_smul]

theorem repL_injective (n m : ℕ) : Function.Injective (repL (E := E) F n m) := by
  intro x y h
  have : Nontrivial (AF F) :=
    (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F).nontrivial
  have hi : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    have : Nontrivial (AF F ⊗[F] E) :=
      (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E)
        (algebraMap F E).injective).nontrivial
    exact RingHom.injective _
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) j
  simp only [repL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply, fold, Equiv.symm_apply_apply, incM,
    Matrix.map_apply, Sum.elim_inl, id] at this
  exact hi this

theorem exists_diag_lagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
    (κ : Type) [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
    (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ L : Submodule F ((κ → F) × (κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card κ ∧
      ∀ (t : AF F), ∀ w ∈ L, ∃ u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E),
        co.e (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) = t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) := by
  intro F E _ _ _ _ _ σ nS nT JT JB ξ κ _ co hrat
  have hinj := NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F
  have : Nontrivial (AF F) := hinj.nontrivial
  let i1 : (κ → F) →ₗ[F] (κ → AF F) := (Algebra.linearMap F (AF F)).compLeft κ
  let ι : ((κ → F) × (κ → F)) →ₗ[F] ((κ → AF F) × (κ → AF F)) := i1.prodMap i1
  have hι : ∀ w, ι w = ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) :=
    fun _ => rfl
  have hιi : Function.Injective ι := by
    intro a b h
    rw [hι, hι, Prod.mk.injEq] at h
    exact Prod.ext (funext fun i => hinj (congrFun h.1 i)) (funext fun i => hinj (congrFun h.2 i))
  let g : Matrix (Fin nT) (Fin nS) E →ₗ[F] ((κ → AF F) × (κ → AF F)) :=
    (co.e.toLinearMap.restrictScalars F) ∘ₗ repL F nT nS
  have hg : ∀ x, g x = co.e ((incM F x).submatrix (fold nT) id) := fun _ => rfl
  have hgi : Function.Injective g := co.e.injective.comp (repL_injective nT nS)
  have hle : LinearMap.range g ≤ LinearMap.range ι := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat (x.submatrix (fold nT) id)
    exact ⟨(y, z), h.symm⟩
  refine ⟨(LinearMap.range g).comap ι, ?_, ?_, ?_⟩
  · rintro a ⟨x, hx⟩ b ⟨x', hx'⟩
    have h := co.form ((incM F x).submatrix (fold nT) id) ((incM F x').submatrix (fold nT) id)
    rw [symp, hTens_fold, mul_zero, map_zero, ← hg, ← hg, hx, hx', hι, hι, eq_comm, sub_eq_zero] at h
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [dotProduct, map_sum, map_mul] using h
  · have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have h1 : Module.finrank F ((LinearMap.range g).comap ι) = nT * nS * Module.finrank F E := by
      rw [(Submodule.equivMapOfInjective ι hιi _).finrank_eq, Submodule.map_comap_eq_of_le hle,
        LinearMap.finrank_range_of_inj hgi, Module.finrank_matrix]
      simp
    have h2 := co.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h2
    simp only [Fintype.card_fin] at h2
    rw [h1]
    nlinarith [h2]
  · rintro t w ⟨x, hx⟩
    refine ⟨t • incM F x, ?_⟩
    rw [← hι, ← hx, hg, diagCols_mul, ← map_smul]
    rfl

end GlobalTheory.WeilSchrodinger.DiagLagr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalLagrangianInvariantFormUnique
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.LagrUniq

theorem exists_lagrInt_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ φ ∈ schA F κ, GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 hν h𝓕
  have hstd : IsStd B.ψ := hB.std
  haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  set C : Matrix (Fin (nT + nT)) (Fin nT) (AF F ⊗[F] E) :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hC
  set C₀ : Matrix (Fin (nT + nT)) (Fin nT) E :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) E).submatrix finSumFinEquiv.symm id with hC₀
  have hCC : C = incM F C₀ := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with i | i <;> by_cases h : i = j <;>
      simp only [hC, hC₀, incM, diagCols, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply, id,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply, h, if_true, if_false, map_one, map_zero]
  let mC : WOF F E nS nT →ₗ[AF F] Matrix (Fin (nT + nT)) (Fin nS) (AF F ⊗[F] E) :=
    { toFun := fun u => C * u
      map_add' := fun u v => Matrix.mul_add _ _ _
      map_smul' := fun t u => Matrix.mul_smul _ _ _ }
  let Lm : WOF F E nS nT →ₗ[AF F] (κ → AF F) × (κ → AF F) := co.e.toLinearMap ∘ₗ mC
  have hLm : ∀ u, Lm u = co.e (C * u) := fun u => rfl
  let S := LinearMap.range Lm
  have hiso : ∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2 := by
    rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩
    have h := co.form (C * u) (C * u')
    rw [GlobalTheory.WeilDiagIso.symp_diag_eq_zero F E σ nS nT JT JB ξ u u'] at h
    rw [hLm, hLm]
    exact (sub_eq_zero.mp h.symm)
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      Lm (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro x
    have e : C * incM F x = incM F (C₀ * x) := by
      rw [hCC]
      simp only [incM]
      exact (Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E))).symm
    obtain ⟨y, z, h⟩ := hco (C₀ * x)
    exact ⟨y, z, by rw [hLm, e, h]⟩
  have hspan : S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} := by
    rintro _ ⟨u, rfl⟩
    have hu := Submodule.mem_map_of_mem (f := Lm) (GlobalTheory.matrix_mem_span_incM F E nT nS u)
    rw [Submodule.map_span] at hu
    refine Submodule.span_mono ?_ hu
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨⟨incM F x, rfl⟩, y, z, h⟩
  obtain ⟨Φ, hΦ, hcont, hre, hre0⟩ := GlobalTheory.ThetaPosIso.exists_theta_re_nonneg F B.ψ hstd κ S hiso hspan
  refine ⟨Φ, hΦ, ?_⟩
  have hI : ∀ u : WOF F E nS nT, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (C * u) = thetaSum F (schr B.ψ (Lm u) Φ) :=
    fun u => rfl
  show ∫ u in 𝓕, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (C * u) ∂ν ≠ 0
  simp_rw [hI]
  refine GlobalTheory.PeriodicPositiveIntegral.integral_ne_zero F E nS nT (fun u => thetaSum F (schr B.ψ (Lm u) Φ)) ?_ ?_ ?_ ?_ ν 𝓕 hν h𝓕
  · exact hcont.comp (IsModuleTopology.continuous_of_linearMap Lm)
  · rintro _ ⟨γ₀, rfl⟩ u
    obtain ⟨y, z, h⟩ := hrat γ₀
    have e1 : Lm (((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS)) γ₀ + u) = Lm (incM F γ₀) + Lm u := by
      rw [map_add (f := _)]; rfl
    have hr : Lm (incM F γ₀) ∈ S := ⟨incM F γ₀, rfl⟩
    have hw : Lm u ∈ S := ⟨u, rfl⟩
    have hi := hiso _ hw _ hr
    rw [h] at hi
    show thetaSum F (schr B.ψ (Lm (_ + u)) Φ) = _
    rw [e1, h, GlobalTheory.ThetaRatInv.thetaSum_schr_rat_add B.ψ hstd.2.1 Φ y z (Lm u), hi, sub_self, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · intro u; exact hre _ ⟨u, rfl⟩
  · show 0 < (thetaSum F (schr B.ψ (Lm 0) Φ)).re
    rw [map_zero]; exact hre0

theorem lagr_invariant_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ l ∈ (adeleClass F).adm κ,
        (∀ z : Matrix (Fin nS) (Fin nT) (AF F ⊗[F] E), ∀ φ ∈ schA F κ,
          l ((GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (z * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ) = l φ) →
        ∃ c : ℂ, ∀ Φ ∈ schA F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσξ₀ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 l hl hinv
  have hstd : IsStd B.ψ := hB.std
  obtain ⟨L, hiso, hdim, hL⟩ := GlobalTheory.WeilSchrodinger.DiagLagr.exists_diag_lagrangian F E σ nS nT JT JB ξ κ co hco
  obtain ⟨l₂, hl₂, he⟩ := GlobalTheory.LagrThetaAdm.exists_admitted_eq_diagonalLagrangian_thetaIntegral_alt F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕
  obtain ⟨φ₀, hφ₀, hne⟩ := exists_lagrInt_ne_zero F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕
  have hrho : ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ),
      (GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (uᵀ * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ = co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ := by
    intro u φ
    rw [GlobalTheory.WeilSchrodinger.transD_rho, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hmem : ∀ w, ∀ φ ∈ schA F κ, co.rho B.ψ w φ ∈ schA F κ := fun w φ hφ =>
    GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ hφ
  have key : ∀ l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ,
      (∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ, l' (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ) = l' φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
        l' (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l' φ := by
    intro l' h t w hw φ hφ
    obtain ⟨u, hu⟩ := hL t w hw
    rw [← hu]
    exact h u φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.AdelicSvN.main F B.ψ hstd κ L hiso hdim l hl l₂ hl₂
    (key l (fun u φ hφ => by rw [← hrho]; exact hinv _ φ hφ))
    (key l₂ (fun u φ hφ => by
      rw [he _ (hmem _ φ hφ), he φ hφ]
      exact GlobalTheory.LagrThetaInv.lagrInt_rho_inv F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕 u φ hφ))
    ⟨φ₀, hφ₀, by rw [he φ₀ hφ₀]; exact hne⟩
  exact ⟨c, fun Φ hΦ => by rw [hc Φ hΦ, he Φ hΦ]; rfl⟩

end GlobalTheory.LagrUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalLagrangianInvariantFormUniqueStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalLagrangian_invariantForm_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ l ∈ (adeleClass F).adm κ,
        (∀ z : Matrix (Fin nS) (Fin nT) (AF F ⊗[F] E), ∀ φ ∈ schA F κ,
          l ((GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (z * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ) = l φ) →
        ∃ c : ℂ, ∀ Φ ∈ schA F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  first | exact @GlobalTheory.LagrUniq.lagr_invariant_unique | exact GlobalTheory.LagrUniq.lagr_invariant_unique | (intros; apply GlobalTheory.LagrUniq.lagr_invariant_unique <;> assumption)
end
