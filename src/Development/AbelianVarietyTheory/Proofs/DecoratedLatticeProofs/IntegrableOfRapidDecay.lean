module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMemMultT

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay
noncomputable section

namespace GlobalTheory.Core.Rk.RapidInt

open scoped TensorProduct ENNReal NNReal ComplexConjugate Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Cont GlobalTheory.GaugeEx
open NumberField.mixedEmbedding
open scoped Classical

section Mixed

variable (F : Type) [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

end Mixed

section Tup

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (M n : ℕ)

def crdTup : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₗ[Ainf F] (Fin n → Fin M → Fin d → Ainf F) :=
  LinearEquiv.piCongrRight fun _ => LinearEquiv.piCongrRight fun _ =>
    (Algebra.TensorProduct.basis (Ainf F) b).equivFun

def mixTup : (Fin n → Fin M → Fin d → Ainf F) ≃+ (Fin n → Fin M → Fin d → mixedSpace F) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ =>
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv

theorem continuous_crdTup : Continuous (crdTup F E b M n) :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).toLinearMap

theorem continuous_crdTup_symm : Continuous (crdTup F E b M n).symm :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).symm.toLinearMap

theorem continuous_mixTup : Continuous (mixTup F M n (d := d)) :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (continuous_toMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

theorem continuous_mixTup_symm : Continuous (mixTup F M n (d := d)).symm :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (continuous_ofMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

def tupEquiv : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (Fin n → Fin M → Fin d → mixedSpace F) where
  toAddEquiv := (crdTup F E b M n).toAddEquiv.trans (mixTup F M n)
  continuous_toFun := (continuous_mixTup F M n).comp (continuous_crdTup F E b M n)
  continuous_invFun := (continuous_crdTup_symm F E b M n).comp (continuous_mixTup_symm F M n)


end Tup


end GlobalTheory.Core.Rk.RapidInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Core.Mi.Shift

variable {D : D7}

theorem inner_left {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) {γ : GA D B.A} (hγ : γ ∈ GQ B.A) (h : GA D B.A) :
    ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f (γ * h) n ∂B.vN.ν =
      ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B.V (isIsoSub_e B.d)
  obtain ⟨-, -, hconj, -, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨-, hψrat, hψconj, -⟩ := GlobalTheory.MixPer.charLaws D ψ hψ B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  obtain ⟨u1, u2, u3⟩ := B.vN.unit
  set δ : GA D B.V := embA B.d B.o γ with hδdef
  have hδ : δ ∈ GQ B.V := by
    have := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
    rwa [one_mul] at this
  have hmem : ∀ n : flagN B.d, δ⁻¹ * n.1 * δ ∈ flagN B.d := fun n => by
    have := hconj n.1 n.2 γ⁻¹
    rwa [map_inv, inv_inv] at this
  have hmem' : ∀ n : flagN B.d, δ * n.1 * δ⁻¹ ∈ flagN B.d := fun n => hconj n.1 n.2 γ
  let c : flagN B.d ≃ₜ* flagN B.d :=
    { toFun := fun n => ⟨δ⁻¹ * n.1 * δ, hmem n⟩
      invFun := fun n => ⟨δ * n.1 * δ⁻¹, hmem' n⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ B.V B.d.e ↔ n ∈ NFlagQ B.V B.d.e := fun n => by
    change δ⁻¹ * (n : GA D B.V) * δ ∈ GQ B.V ↔ (n : GA D B.V) ∈ GQ B.V
    rw [Subgroup.mul_mem_cancel_right _ hδ, Subgroup.mul_mem_cancel_left _ (inv_mem hδ)]
  have hK : ∀ γ' ∈ NFlagQ B.V B.d.e, ∀ n : flagN B.d,
      besFun ψ 1 B.d B.o B.ζ φ f h (γ' * n) = besFun ψ 1 B.d B.o B.ζ φ f h n := fun γ' hγ' n => by
    have hγ'Q : (γ' : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besFun, Subgroup.coe_mul]
    rw [psiBes_mul B.d ψ 1 _ γ'.2 n.2, hψrat _ _ hγ'Q, one_mul, mul_assoc (γ' : GA D B.V), hf _ hγ'Q]
  refine Eq.trans ?_ (GlobalTheory.Mem.TrueRecord.integral_aut _ u1 u2 u3 c hc _ hK)
  congr 1
  funext n
  change _ = besFun ψ 1 B.d B.o B.ζ φ f h ⟨δ⁻¹ * n.1 * δ, hmem n⟩
  simp only [besFun]
  have e1 : psiBes ψ B.d 1 (vecB B.o B.ζ) (δ⁻¹ * n.1 * δ) = psiBes ψ B.d 1 (vecB B.o B.ζ) n.1 := by
    have := hψconj n.1 γ⁻¹
    rwa [map_inv, inv_inv] at this
  have e2 : f (δ⁻¹ * n.1 * δ * embA B.d B.o h) = f (n.1 * embA B.d B.o (γ * h)) := by
    rw [map_mul, ← hδdef, mul_assoc, mul_assoc, hf _ (inv_mem hδ)]
  rw [e1, e2, hφ γ hγ h]

theorem map_mul_right {ρ : ℕ} (B : BesLev D ρ) (a : GA D B.A) : B.vA.μ.map (· * a) = B.vA.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  obtain ⟨K, hK, hcov⟩ := B.cpt
  exact Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice B.vA.μ (GQ B.A) hK hcov a

theorem setIntegral_mul_right {ρ : ℕ} (B : BesLev D ρ) (G : GA D B.A → ℂ) (hG : ∀ γ ∈ GQ B.A, ∀ h, G (γ * h) = G h)
    (a : GA D B.A) : ∫ h in B.vA.𝓕, G (h * a) ∂B.vA.μ = ∫ h in B.vA.𝓕, G h ∂B.vA.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  have hmp : MeasurePreserving (· * a) B.vA.μ B.vA.μ := ⟨measurable_mul_const a, map_mul_right B a⟩
  have hmp' : MeasurePreserving (· * a⁻¹) B.vA.μ B.vA.μ := ⟨measurable_mul_const a⁻¹, map_mul_right B a⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a) G B.vA.𝓕, Set.image_mul_right]
  have hF : IsFundamentalDomain (GQ B.A) ((· * a⁻¹) ⁻¹' B.vA.𝓕) B.vA.μ :=
    B.vA.fund.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (B.vA.fund.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

end GlobalTheory.Core.Mi.Shift


open GlobalTheory.Core.Mi.Shift in
theorem GlobalTheory.Core.Mi.per_rTrans : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ)
    (f : GA D B.V → ℂ) (a : GA D B.A), IsStdChar D ψ (-1) → IsContAut B.A φ → IsContAut B.V f →
    B.per ψ (rTrans a φ) (rTrans (embA B.d B.o a) f) = B.per ψ φ f := by
  intro D ψ ρ B φ f a hψ hφ hf
  have hshift : ∀ h, ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ (rTrans a φ) (rTrans (embA B.d B.o a) f) h n ∂B.vN.ν =
      ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f (h * a) n ∂B.vN.ν := fun h => by
    simp only [besFun, rTrans, map_mul, mul_assoc]
  unfold BesLev.per besPer
  simp_rw [hshift]
  exact setIntegral_mul_right B (fun h => ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν)
    (fun γ hγ h => inner_left B ψ hψ.1 φ f hφ.1 hf.1 hγ h) a

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotZero

theorem left_and_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {R : Subgroup G}
    (hR : IsClosed (R : Set G)) (μR : Measure R) [μR.IsHaarMeasure] [μR.IsInvInvariant]
    (μG : Measure G) [μG.IsHaarMeasure] {f : G → ℂ} {z : ℂ} (h : IsQuotIntL1 μR μG f z) :
    (∀ r ∈ R, ∀ x, f (r * x) = f x) ∧ (f = 0 → z = 0) := by
  haveI : LocallyCompactSpace R := hR.locallyCompactSpace
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  haveI : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  refine ⟨fun r hr x => h.left hr x, ?_⟩
  rintro rfl
  exact h.unique hR IsQuotIntL1.zero


open scoped Pointwise Topology in
theorem isClosed_of_locallyCompactSpace {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (R : Subgroup G) [LocallyCompactSpace R] : IsClosed (R : Set G) := by
  obtain ⟨K, hKn, hK⟩ := local_compact_nhds (x := (1 : R)) (n := Set.univ) Filter.univ_mem
  have hKc : IsCompact K := hK.2
  rw [nhds_subtype, Filter.mem_comap] at hKn
  obtain ⟨U, hU, hUK⟩ := hKn
  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset hU
  set W : Set G := V ∩ V⁻¹
  have hWo : IsOpen W := hVo.inter hVo.inv
  have hW1 : (1 : G) ∈ W := ⟨hV1, by simpa using hV1⟩
  set K' : Set G := Subtype.val '' K
  have hK'c : IsCompact K' := hKc.image continuous_subtype_val
  have hK'R : K' ⊆ R := by rintro _ ⟨k, -, rfl⟩; exact k.2
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨y, hyW, hyR⟩ := mem_closure_iff.1 hx (x • W) (hWo.smul x) (by simpa using Set.smul_mem_smul_set (a := x) hW1)
  obtain ⟨v₁, hv₁, rfl⟩ := hyW
  have hsub : (x • W) ∩ (R : Set G) ⊆ (x • v₁) • K' := by
    rintro r ⟨⟨v₂, hv₂, rfl⟩, hr⟩
    have hm : v₁⁻¹ * v₂ ∈ U := hVV (Set.mul_mem_mul (by simpa using hv₁.2) hv₂.1)
    have hmR : v₁⁻¹ * v₂ ∈ R := by
      have := R.mul_mem (R.inv_mem hyR) hr
      simpa [smul_eq_mul, mul_assoc] using this
    refine ⟨v₁⁻¹ * v₂, ⟨⟨v₁⁻¹ * v₂, hmR⟩, hUK hm, rfl⟩, ?_⟩
    simp [smul_eq_mul, mul_assoc]
  have hx' : x ∈ closure ((x • W) ∩ (R : Set G)) :=
    (hWo.smul x).inter_closure ⟨by simpa using Set.smul_mem_smul_set (a := x) hW1, hx⟩
  have hcl : IsClosed ((x • v₁) • K') := (hK'c.smul _).isClosed
  have := closure_minimal hsub hcl hx'
  obtain ⟨k, hk, hkx⟩ := this
  simp only [smul_eq_mul] at hkx hyR
  rw [← hkx]
  exact R.mul_mem hyR (hK'R hk)

theorem jac_haar_inv {D : D7} {ρ : ℕ} (J : JacLev D ρ) :
    IsClosed (jacGrp J.d : Set (GA D J.W)) ∧ J.μR.IsHaarMeasure ∧ J.μR.IsInvInvariant := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨hN, h𝓝, h𝓝1⟩ := J.vN.unit
  obtain ⟨K, hK, hcov⟩ := J.cpt
  have hμ := J.v0.haar
  obtain ⟨p, hpc, hp⟩ := GlobalTheory.JacProj.exists_continuous_proj D J.W J.W₀ ρ J.d
  have hNc := GlobalTheory.Mem.TrueRecord.isClosed_NFlag J.W (isIsoSub_e J.d)
  haveI : LocallyCompactSpace (flagN J.d) := hNc.locallyCompactSpace
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN J.d) J.d.emb0 (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1
    J.d.continuous_embed ⟨p, hpc, hp⟩
  haveI : LocallyCompactSpace (jacGrp J.d) := e.symm.isClosedEmbedding.locallyCompactSpace
  refine ⟨isClosed_of_locallyCompactSpace (jacGrp J.d), ?_⟩
  exact GlobalTheory.SemiHaar.semiMeas_haar_inv (flagN J.d) J.d.emb0 hNc J.d.continuous_embed
    (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1 ⟨p, hpc, hp⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund J.vN.ν h𝓝
    (by rw [h𝓝1]; exact ENNReal.one_ne_top)

theorem bes_haar_inv {D : D7} {ρ : ℕ} (B : BesLev D ρ) :
    IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ B.μR.IsHaarMeasure ∧ B.μR.IsInvInvariant := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨hN, h𝓝, h𝓝1⟩ := B.vN.unit
  obtain ⟨K, hK, hcov⟩ := B.cpt
  have hμ := B.vA.haar
  obtain ⟨p, hpc, hp⟩ := GlobalTheory.BesProj.exists_continuous_proj D B.V B.V₀ B.A B.L ρ B.d B.o
  obtain ⟨hc, hcl, hnorm, -, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  have hΛ : ∀ δ ∈ GQ B.A, embA B.d B.o δ ∈ GQ B.V := fun δ hδ => by
    simpa using (hrat 1 (one_mem _) δ).2 ⟨one_mem _, hδ⟩
  haveI : LocallyCompactSpace (flagN B.d) := hcl.locallyCompactSpace
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN B.d) (embA B.d B.o) hnorm hc ⟨p, hpc, hp⟩
  haveI : LocallyCompactSpace (besGrp B.d B.o) := e.symm.isClosedEmbedding.locallyCompactSpace
  refine ⟨isClosed_of_locallyCompactSpace (besGrp B.d B.o), ?_⟩
  exact GlobalTheory.SemiHaar.semiMeas_haar_inv (flagN B.d) (embA B.d B.o) hcl hc hnorm ⟨p, hpc, hp⟩
    (GQ B.V) (GQ B.A) hΛ hK hcov B.vA.μ B.vA.fund B.vN.ν h𝓝
    (by rw [h𝓝1]; exact ENNReal.one_ne_top)

end GlobalTheory.QuotZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.LevLoc

variable {D : D7}

def LocOK {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (PP : Pl D.host.E) (y : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Prop :=
  (PP ∈ L.Pg → y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr y = 1) ∧
    (PP ∈ L.Q → y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 L.r))

theorem locOK_one {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (PP : Pl D.host.E) : LocOK L PP 1 :=
  ⟨fun _ => ⟨one_mem _, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _⟩, fun _ => one_mem _⟩

theorem mem_lev_iff {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (hP : L.P.H = ⊥) (x : GL (Fin n) (Lev.EAf D)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm J β L ↔ x ∈ Formalism.L2.DIV.UA D.sp.cm J ∧ x ∈ Formalism.L2.DIV.St β ∧
      ∀ PP, LocOK L PP (Formalism.L2.DIV.redFn β PP x) := by
  rw [Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev, hP, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨hU, hS, hg, hq⟩, hr⟩
    exact ⟨hU, hS, fun PP => ⟨fun h => ⟨hg PP h, congrFun hr ⟨PP, h⟩⟩, fun h => hq PP h⟩⟩
  · rintro ⟨hU, hS, h⟩
    exact ⟨⟨hU, hS, fun PP hP => ((h PP).1 hP).1, fun PP hP => (h PP).2 hP⟩, funext fun PP => ((h PP.1).1 PP.2).2⟩

theorem finE_gAt_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hv : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) :
    Lev.finE V (gAt V (.inl v) g) ∈ Formalism.L2.DIV.St β := by
  refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr _).2 fun w => ?_
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram w
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) ∈ _
  by_cases e : w = v
  · subst e
    rw [GlobalTheory.AdelicU.proj_emb_self]
    exact hv
  · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e]
    exact one_mem _

theorem red_local {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (g : GA D V) (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) (PP : Pl D.host.E) :
    Formalism.L2.DIV.redFn β PP (Lev.finE V g) =
      Formalism.L2.DIV.redFn β PP (Lev.finE V (gAt V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) := by
  set v := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  set k := gAt V (.inl v) g with hkdef
  have hk : Lev.finE V k ∈ Formalism.L2.DIV.St β := finE_gAt_mem_St hfr g v ((GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr g).1 hg v)
  have hpk : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
    show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v
      (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) = _
    rw [GlobalTheory.AdelicU.proj_emb_self]
  have h2 : Lev.finE V (k⁻¹ * g) ∈ Formalism.L2.DIV.St β := by
    rw [map_mul, map_inv]; exact mul_mem (inv_mem hk) hg
  have h3 : Formalism.L2.DIV.redFn β PP (Lev.finE V (k⁻¹ * g)) = 1 :=
    GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D V β _ PP h2 (by rw [map_mul, map_inv, hpk, inv_mul_cancel])
  have e : g = k * (k⁻¹ * g) := by group
  conv_lhs => rw [e]
  rw [map_mul, Formalism.L2.DIV.redFn_mul hk h2, h3, mul_one]

end GlobalTheory.ChainTw.LevLoc

namespace GlobalTheory.ChainTw.LevLoc


open Classical in
theorem levLoc : ∀ D : D7, ForStageQ D fun c w _ s => MeasurableSet (levSet s) ∧ MeasurableSet (intOff c s) ∧ (∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L) ∧ (∀ g ∈ levSet s, ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ (∀ κ ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L κ‖ = 1 ∧ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ ∃ mR, IsLevMeas s mR := by
  intro D c w hw j _ s hs
  obtain ⟨hr, hL, hfl⟩ := hs
  have hfr : Formalism.L2.DIV.IsFrame s.β s.Λ := hfl.frame
  haveI : s.ν.IsHaarMeasure := hfl.haar
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hP : s.L.P.H = ⊥ := by rw [hL]; rfl
  have hPl : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := by
    intro PP hPP
    have h1 : PP ∈ c.Pg := by
      rw [hw.union, Finset.mem_union]
      rw [hL] at hPP
      exact hPP
    unfold Com.S
    exact Finset.mem_image_of_mem _ h1
  set V := s.V
  set K := Lev.levG s.V s.β s.L

  have h3 : ∀ k ∈ K, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram s.Λ v :=
    fun k hk v => (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr k).1 (GlobalTheory.ChainOnto.LevelFacts.finE_mem_St hk) v

  have h1 : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ K := by
    obtain ⟨U, hU, hUk⟩ := GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes D V s.β (s.L.Pg ∪ s.L.Q)
    refine ⟨U, hU, fun k hk hkf => ⟨hkf, ?_⟩⟩
    exact GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm V.gram s.β s.L _ (GlobalTheory.LevSplit.finE_mem_UA V k) (hUk k hk).1
      fun PP hPP => (hUk k hk).2 PP (Finset.mem_union.2 hPP)

  have hloc : ∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ K := by
    intro g
    constructor
    · intro hg
      obtain ⟨-, hS, hl⟩ := (mem_lev_iff V.gram s.β s.L hP _).1 hg
      refine ⟨fun v _ => (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr g).1 hS v, fun v _ => ?_⟩
      have hkS := finE_gAt_mem_St hfr g v ((GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr g).1 hS v)
      refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC V v _, ?_⟩
      refine (mem_lev_iff V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hkS, fun PP => ?_⟩
      by_cases e : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
      · subst e
        rw [← red_local hfr g hS PP]
        exact hl PP
      · rw [GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D V s.β _ PP hkS (GlobalTheory.AdelicU.proj_emb_ne _ _ e _)]
        exact locOK_one _ _
    · rintro ⟨hI, hK⟩
      have hS : Lev.finE V g ∈ Formalism.L2.DIV.St s.β := by
        refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr g).2 fun v => ?_
        by_cases hv : v ∈ c.S
        · have := h3 _ (hK v hv) v
          have e : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (gAt s.V (.inl v) g) = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
            show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v
              (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) = _
            rw [GlobalTheory.AdelicU.proj_emb_self]
          rw [e] at this
          exact this
        · exact hI v hv
      refine (mem_lev_iff V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA V g, hS, fun PP => ?_⟩
      by_cases hPP : PP ∈ s.L.Pg ∨ PP ∈ s.L.Q
      · rw [red_local hfr g hS PP]
        exact ((mem_lev_iff V.gram s.β s.L hP _).1 (hK _ (hPl PP hPP)).2).2.2 PP
      · exact ⟨fun h => absurd (Or.inl h) hPP, fun h => absurd (Or.inr h) hPP⟩
  let A : Subgroup (GA D V) := (Formalism.L2.DIV.lev D.sp.cm V.gram s.β s.L).comap (Lev.finE V)
  have hAset : (A : Set (GA D V)) = levSet s := rfl
  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg =>
    ⟨(GlobalTheory.AutMult.toFin V g).2, Subgroup.mem_comap.2 (by rw [GlobalTheory.ChainOnto.HaarInf.finE_toFin]; exact Subgroup.mem_comap.1 hg)⟩
  have hAopen : IsOpen (A : Set (GA D V)) := by
    obtain ⟨U, hU, hUK⟩ := h1
    let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
    have hLf : IsOpen (Lf : Set (GfC V)) := by
      refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
      exact hUK k hk k.2
    have e : (A : Set (GA D V)) = GlobalTheory.AutMult.toFin V ⁻¹' (Lf : Set (GfC V)) := by
      ext g
      refine ⟨fun hg => hfinK g hg, fun hg => ?_⟩
      have := Subgroup.mem_comap.1 hg.2
      refine Subgroup.mem_comap.2 ?_
      rw [← GlobalTheory.ChainOnto.HaarInf.finE_toFin]; exact this
    rw [e]; exact hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hAint : (A : Set (GA D V)) ⊆ intOff c s := fun g hg => ((hloc g).1 hg).1
  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen
  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open D V s.Λ hsd K inf_le_left h3 h1
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    refine Subgroup.mem_comap.2 ?_
    rw [Subgroup.subtype_apply, GlobalTheory.ChainOnto.HaarInf.finE_of_mem_ginfC V b.2]; exact one_mem _
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    GlobalTheory.T.map_restrict_isHaar_of_open_product_compact (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨hAopen.measurableSet, hIopen.measurableSet, hloc, fun g hg => ?_, fun κ hκ =>
    ⟨GlobalTheory.ChainOnto.LevelFacts.levChi_norm s.β s.L κ, h3 κ hκ⟩, ?_⟩
  · exact ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  refine ⟨_, hHaar, fun f F hf hF => ?_⟩
  have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
    (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
  have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
    conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
    exact hF _ _ (hfinK g hg)
  have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
    (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
  refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
  rw [← hAset, setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]

end GlobalTheory.ChainTw.LevLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels : ∀ D : D7, ForStageQ D fun c w _ s => MeasurableSet (levSet s) ∧ MeasurableSet (intOff c s) ∧ (∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L) ∧ (∀ g ∈ levSet s, ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ (∀ κ ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L κ‖ = 1 ∧ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ ∃ mR, IsLevMeas s mR := by
  first | exact @GlobalTheory.ChainTw.LevLoc.levLoc | exact GlobalTheory.ChainTw.LevLoc.levLoc | (intros; apply GlobalTheory.ChainTw.LevLoc.levLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.PerSumProof

variable {D : D7}

theorem conv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) {f : GA D B.V → ℂ}
    (hf : IsContAut B.V f) {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) :
    (∀ h, IntegrableOn (besFun ψ 1 B.d B.o B.ζ φ f h) B.vN.𝓝 B.vN.ν) ∧
      IntegrableOn (fun h => ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν) B.vA.𝓕 B.vA.μ := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  haveI := B.vA.haar
  obtain ⟨K, hK, hcov⟩ := B.cpt
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V ρ B.d.e (isIsoSub_e B.d)).1
  obtain ⟨hemb, -, hnorm, -, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  have hch := GlobalTheory.MixPer.charLaws D ψ hψ.1 B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  have hfin : B.vA.μ B.vA.𝓕 < ⊤ := by
    refine GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ B.A) hK (fun g => ?_) B.vA.μ B.vA.fund
    obtain ⟨γ, hγ, hk⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, γ * g, hk, by group⟩
  have hc : Continuous fun q : GA D B.A × flagN B.d => besFun ψ 1 B.d B.o B.ζ φ f q.1 q.2 :=
    ((hφ.2.comp continuous_fst).mul (hf.2.comp ((continuous_subtype_val.comp continuous_snd).mul
      (hemb.comp continuous_fst)))).mul ((hch.1 _).comp (continuous_subtype_val.comp continuous_snd)).star
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hc.continuousOn
  refine GlobalTheory.Per.FJConv.iterated_integrableOn hfin.ne (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top) hc (M := M)
    fun g n => ?_
  obtain ⟨γ, hγ, hk⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹, hnorm n.1 n.2 γ⟩
  have e' : embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹ = γ'.1 * k'.1 := congrArg Subtype.val e
  have hδ : embA B.d B.o γ ∈ GQ B.V := by simpa using (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
  have hγ'Q : γ'.1 ∈ GQ B.V := hγ'
  have en : n.1 = (embA B.d B.o γ)⁻¹ * (γ'.1 * k'.1) * embA B.d B.o γ := by
    rw [← e']; group
  have e1 : besFun ψ 1 B.d B.o B.ζ φ f g n = besFun ψ 1 B.d B.o B.ζ φ f (γ * g) k' := by
    simp only [besFun]
    have f1 : f (n.1 * embA B.d B.o g) = f (k'.1 * embA B.d B.o (γ * g)) := by
      rw [← hf.1 ((embA B.d B.o γ)⁻¹ * γ'.1) (mul_mem (inv_mem hδ) hγ'Q) (k'.1 * embA B.d B.o (γ * g)), en, map_mul]
      congr 1; group
    have p1 : psiBes ψ B.d 1 (vecB B.o B.ζ) n.1 = psiBes ψ B.d 1 (vecB B.o B.ζ) k'.1 := by
      have := hch.2.2.1 (γ'.1 * k'.1) γ⁻¹
      rw [map_inv, inv_inv, ← en] at this
      rw [this, psiBes_mul B.d ψ 1 _ γ'.2 k'.2, hch.2.1 _ _ hγ'Q, one_mul]
    rw [f1, p1, hφ.1 γ hγ g]
  rw [e1]
  exact hM (γ * g, k') ⟨hk, hk'⟩

end GlobalTheory.SeeSaw.PerSumProof

namespace GlobalTheory.SeeSaw

theorem perSum_all : ∀ D : D7, PerSum D := by
  intro D ψ hψ ρ B f hf I s a φ hφ
  have hconv := fun i (hi : i ∈ s) => PerSumProof.conv hψ B hf (hφ i hi)
  simp only [BesLev.per, besPer]
  have e1 : ∀ h n, besFun ψ 1 B.d B.o B.ζ (∑ i ∈ s, a i • φ i) f h n =
      ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ (φ i) f h n := by
    intro h n
    simp only [besFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e1]
  have e2 : (fun h => ∫ n in B.vN.𝓝, ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ (φ i) f h n ∂B.vN.ν) =
      fun h => ∑ i ∈ s, a i * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ (φ i) f h n ∂B.vN.ν := by
    funext h
    rw [integral_finsetSum s fun i hi => ((hconv i hi).1 h).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [e2, integral_finsetSum s fun i hi => (hconv i hi).2.const_mul (a i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChain
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.TwistChart

variable {D : D7}

theorem isIdemOf_idem {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) :
    IsIdemOf φ (GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ)) := by
  refine ⟨GlobalTheory.EmbChart.isSplitIdem_idem _, ?_, GlobalTheory.SplitProjChart.rdA_idem φ⟩
  rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]
  rfl

theorem exists_unif (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ ϖ : (Fv D.host.F v)ˣ, ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) =
      ValuativeRel.uniformizer (Fv D.host.F v) := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (Fv D.host.F v))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact ValuativeRel.uniformizer_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

theorem unit_section {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) :
    ∃ U : (Fv D.host.F v)ˣ →* (AE D)ˣ, (∀ y, (1 - e) * (U y : AE D) = 1 - e ∧ rdA φ (U y : AE D) = y) ∧
      ∀ (x : AE D) (y : (Fv D.host.F v)ˣ), (1 - e) * x = 1 - e → rdA φ x = y → x = U y := by
  have hπ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hee : e * e = e := he.1.1
  obtain ⟨sec, hsec⟩ : ∃ sec : Fv D.host.F v → AE D, ∀ y, rdA φ (sec y) = y :=
    ⟨fun y => (hπ.1 y).choose, fun y => (hπ.1 y).choose_spec⟩
  have hf1 : ∀ y, (1 - e) * ((1 - e) + e * sec y) = 1 - e := fun y => by
    linear_combination (1 - sec y) * hee
  have hf2 : ∀ y, rdA φ ((1 - e) + e * sec y) = y := fun y => by
    rw [map_add (f := _), map_sub, map_mul, map_one, he.2.2, hsec]; ring
  have key : ∀ x y, (1 - e) * x = 1 - e → rdA φ x = y → x = (1 - e) + e * sec y := by
    intro x y h1 h2
    have h3 : e * (x - sec y) = 0 := (hπ.2.1 _).1 (by rw [map_sub, h2, hsec, sub_self])
    have h4 : e * x = e * sec y := by rw [mul_sub] at h3; exact sub_eq_zero.1 h3
    calc x = (1 - e) * x + e * x := by ring
      _ = (1 - e) + e * sec y := by rw [h1, h4]
  have hmul : ∀ y z, (1 - e) + e * sec (y * z) = ((1 - e) + e * sec y) * ((1 - e) + e * sec z) := fun y z =>
    (key _ _ (by rw [← mul_assoc, hf1, hf1]) (by rw [map_mul, hf2, hf2])).symm
  have hone : (1 - e) + e * sec 1 = 1 := (key 1 1 (mul_one _) (map_one _)).symm
  let f : (Fv D.host.F v)ˣ → (AE D)ˣ := fun y =>
    ⟨(1 - e) + e * sec y, (1 - e) + e * sec ((y⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v),
      by rw [← hmul, Units.mul_inv, hone], by rw [← hmul, Units.inv_mul, hone]⟩
  exact ⟨MonoidHom.mk' f fun y z => Units.ext (by simp only [f, Units.val_mul]; exact hmul y z),
    fun y => ⟨hf1 y, hf2 y⟩, fun x y h1 h2 => key x y h1 h2⟩

end GlobalTheory.TwistChart

namespace GlobalTheory.TwistChart

variable {D : D7}

def blockEquiv (n r k t : ℕ) (h : n = r + k * t) : Fin r ⊕ Blocks k t ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv)).trans
    (finSumFinEquiv.trans (finCongr h.symm))

theorem blockEquiv_inl (n r k t : ℕ) (h : n = r + k * t) (i : Fin r) : ((blockEquiv n r k t h (.inl i) : Fin n) : ℕ) = i := by
  simp [blockEquiv]

theorem exists_isChart (s : PiLocalization₂ D) (k : ℕ) (hrank : s.V.rank = D.R.r + k * D.R.t) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) : ∃ ι, IsChart s k φ ι := by
  have hπ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hJ := GlobalTheory.NoExcl.isHermND_gram s.V
  let ε := blockEquiv s.V.rank D.R.r k D.R.t hrank
  let re : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃* GL (Fin s.V.rank) (Fv D.host.F v) :=
    Units.mapEquiv (Matrix.reindexAlgEquiv (Fv D.host.F v) (Fv D.host.F v) ε).toRingEquiv.toMulEquiv
  let L := GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (GlobalTheory.AdelicU.chartEmb hπ) (frCo φ s.β)
  let ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V :=
    (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v).comp (L.symm.toMulEquiv.toMonoidHom.comp re.toMonoidHom)
  refine ⟨ι, ε, blockEquiv_inl _ _ _ _ hrank, fun y => ⟨?_, ?_⟩⟩
  · change GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v (ι y)) = ι y
    simp only [ι, MonoidHom.comp_apply, GlobalTheory.AdelicU.proj_emb_self]
  · have h1 : grpCo φ s.V (frCo φ s.β) (ι y) = GlobalTheory.SplitHecke.rho s.V (rdA φ) (frCo φ s.β) (ι y) := by
      refine Units.ext ?_
      rw [GlobalTheory.SplitHecke.rho_val]
      rfl
    rw [h1, GlobalTheory.AdelicU.rho_eq_splitEquivIn hπ s.V hJ]
    simp only [ι, L, MonoidHom.comp_apply, GlobalTheory.AdelicU.proj_emb_self]
    have h2 : L (L.symm (re y)) = re y := L.apply_symm_apply _
    change (L (L.symm (re y))).1.submatrix ε ε = y.1
    rw [h2]
    ext i j
    simp [re]

end GlobalTheory.TwistChart

namespace GlobalTheory.TwistChart

open GlobalTheory.ChainOnto GlobalTheory.ChainTw

theorem charts_at_twist : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, (∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP) ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → (∃ e, IsIdemOf φ e) ∧ (∃ x ϖ, IsLocUnif φ x ϖ) ∧ (∃ ι, IsChart s j φ ι) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : (Fv D.host.F v)ˣ →* ℂˣ, GlobalTheory.SmGL.IsUnitaryChar μ ∧ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) := by
  intro D c w hw j _ s hs PP hPP
  classical
  have hPg : PP ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_right _ hPP
  obtain ⟨-, ⟨es, hes, -⟩, -⟩ := hw.com.split
  refine ⟨?_, fun v φ _ => ?_⟩
  · obtain ⟨v, φ, -, h⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 _ _ (hes PP hPg)
    exact ⟨v, φ, h⟩
  have he := isIdemOf_idem φ
  obtain ⟨U, hU1, hU2⟩ := unit_section φ he
  have huniq := (GlobalTheory.SplitProjChart.chart_rdA D v φ _ he).2.2.2.2
  obtain ⟨hr, -, hst⟩ := hs
  refine ⟨⟨_, he⟩, ?_, exists_isChart s j hst.rank φ he, fun χ => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_unif (D := D) v
    exact ⟨U ϖ, ϖ, _, he, (hU1 ϖ).1, (hU1 ϖ).2, hϖ⟩
  · refine ⟨(Circle.toUnits.comp χ).comp U, fun y => ?_, fun x y ⟨e', he', h1, h2⟩ => ?_⟩
    · exact Circle.norm_coe _
    · obtain rfl := huniq e' he'
      have hx : x = U y := Units.ext (hU2 _ _ h1 h2)
      rw [hx]
      rfl

end GlobalTheory.TwistChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charts_at_twist_places_chain : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, (∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP) ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → (∃ e, IsIdemOf φ e) ∧ (∃ x ϖ, IsLocUnif φ x ϖ) ∧ (∃ ι, IsChart s j φ ι) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : (Fv D.host.F v)ˣ →* ℂˣ, GlobalTheory.SmGL.IsUnitaryChar μ ∧ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) := by
  first | exact @GlobalTheory.TwistChart.charts_at_twist | exact GlobalTheory.TwistChart.charts_at_twist | (intros; apply GlobalTheory.TwistChart.charts_at_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Core.Rk.TopOnto

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.Top.Model GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice Matrix

section General

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact (((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ)))).mul (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  obtain ⟨u, rfl⟩ : IsUnit g := isUnit_of_mul_isUnit_right (hg'.symm ▸ hG : IsUnit (gᴴ * gramAt D V τ * g))
  exact Submodule.subset_span
    (Formalism.IndefR.SchurOrthogonalityAlt.smoothVec_rep M τ ⟨u, hg⟩ (Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_of_mem hw))

theorem real_induction (hθ : IsInfFam θ) (P : GA D V → Prop) (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hat : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P (atTau θ V τ g)) : ∀ a ∈ GinfC V, P a := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have key : ∀ s : Finset D.what₂.Tau, ∀ a ∈ GinfC V, (∀ τ ∉ s, infMat D.sp.cm.sig V.gram (θ τ) a = 1) → P a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha h
      rw [R.2.2.1 a ha 1 (one_mem _) fun τ => by rw [h τ (Finset.notMem_empty τ), infMat_one]]
      exact h1
    | insert τ s hτ ih =>
      intro a ha h
      have hg := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
      have hb := atTau_spec hθ V τ hg
      have hi : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a))⁻¹ *
          infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a)) = 1 := fun ρ => by
        rw [← infMat_mul, inv_mul_cancel, infMat_one]
      rw [← mul_inv_cancel_left (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a)) a]
      refine hmul _ _ (hat τ _ hg) (ih _ (mul_mem (inv_mem hb.1) ha) fun ρ hρ => ?_)
      rw [infMat_mul]
      by_cases c : ρ = τ
      · subst c
        have := hi ρ
        rwa [hb.2.1] at this
      · have := hi ρ
        rw [hb.2.2 ρ c] at this
        rw [h ρ (by simp [c, hρ])]
        exact this
  exact fun a ha => key Finset.univ a ha fun τ h => absurd (Finset.mem_univ τ) h

theorem multT_rel {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (v v' : M.Vec) (x x' : GA D V) (c : ℂ)
    (h : ∀ m, IsMultMap θ M J χ m → m v' x' = c * m v x) {T} (hT : T ∈ MultT θ M J χ) :
    T (PiTensorProduct.tprod ℂ v') x' = c * T (PiTensorProduct.tprod ℂ v) x := by
  obtain ⟨m, hm, rfl⟩ := hT
  show PiTensorProduct.lift m _ x' = c * PiTensorProduct.lift m _ x
  rw [PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
  induction hm using Submodule.span_induction with
  | mem m hm => exact h m hm
  | zero => simp
  | add a b _ _ ha hb => simp only [MultilinearMap.add_apply, Pi.add_apply, ha, hb, mul_add]
  | smul r a _ ha => simp only [MultilinearMap.smul_apply, Pi.smul_apply, ha, smul_eq_mul]; ring

theorem multT_rel' {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (x x' : GA D V) (c : ℂ)
    (h : ∀ m, IsMultMap θ M J χ m → ∀ v, m v x' = c * m v x) {T} (hT : T ∈ MultT θ M J χ) (v : SmT M) :
    T v x' = c * T v x := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, multT_rel v v x x' c (fun m hm => h m hm v) hT, smul_eq_mul, smul_eq_mul]
    ring
  | add a b ha hb => rw [map_add (f := _), Pi.add_apply, Pi.add_apply, ha, hb, mul_add]

theorem exists_ratPt (hθ : IsInfFam θ) {n : ℕ} (hn : V.rank = n) (δ : GL (Fin n) D.host.E)
    (hδ : δ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))) :
    ∃ γ ∈ GQ V, finN V hn γ = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ ∧
      ∀ τ, (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) = (δ : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) := by
  subst hn
  have hm : Formalism.UG.bc (incA D) δ ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram :=
    unit_transfer (Equiv.refl _) (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig)
      (fun _ => rfl) V.gram _ (fun _ _ => rfl) δ.1 _ (fun _ _ => rfl) hδ
  refine ⟨⟨_, hm⟩, ⟨δ, hδ, rfl⟩, rfl, fun τ => ?_⟩
  exact Matrix.ext fun i j => (hθ τ).1 _

theorem infN_eq {n : ℕ} (hn : V.rank = n) (γ : GA D V) (τ : D.what₂.Tau) :
    (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) =
      (infMat D.sp.cm.sig V.gram (θ τ) γ).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

end General

section Law

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}


set_option maxHeartbeats 1000000 in
theorem real_translate (hθ : IsInfFam θ) (hj : IsJ u M j) : ∀ a ∈ GinfC D.sp.X', ∀ v : SmT M, ∃ v' : SmT M,
    lT _ (infPt θ a) (j v') = j v ∧ ∀ T ∈ MultT θ M J χ, ∀ h, T v' h = T v (h * a) := by
  refine real_induction hθ _ (fun v => ⟨v, by rw [map_one, lT_one], fun T _ h => by rw [mul_one]⟩) (fun a b ha hb v => ?_)
    fun τ g hg v => ?_
  · obtain ⟨v₁, e1, f1⟩ := hb v
    obtain ⟨v₂, e2, f2⟩ := ha v₁
    refine ⟨v₂, by rw [map_mul (infPt θ), lT_mul, e2, e1], fun T hT h => ?_⟩
    rw [f2 T hT, f1 T hT, mul_assoc]
  · induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      let w : M.sm τ := ⟨M.rep τ g (v τ), rep_mem_sm M τ hg _ (v τ).2⟩
      refine ⟨r • PiTensorProduct.tprod ℂ (Function.update v τ w), ?_, fun T hT h => ?_⟩
      · rw [map_smul, map_smul, map_smul]
        congr 1
        funext y
        refine hj.eqv τ g hg v w rfl _ y fun ρ => ?_
        refine (congrArg (· * y.1 ρ) (infN_atTau θ _ (rankP D) hθ τ hg ρ)).trans ?_
        by_cases c : ρ = τ
        · subst c
          simp only [Function.update_self]
        · simp only [Function.update_of_ne c, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
      · rw [map_smul, map_smul, Pi.smul_apply, Pi.smul_apply,
          multT_rel v (Function.update v τ w) (h * atTau θ _ τ g) h 1 (fun m hm => by
            rw [one_mul]; exact congrFun (hm.equiv τ g hg v w rfl) h) hT, one_mul]
    | add a b ha hb =>
      obtain ⟨a', e1, f1⟩ := ha
      obtain ⟨b', e2, f2⟩ := hb
      refine ⟨a' + b', by rw [map_add j, map_add j, map_add, e1, e2], fun T hT h => ?_⟩
      rw [map_add T, map_add T, Pi.add_apply, Pi.add_apply, f1 T hT, f2 T hT]

theorem hasMat_finPt {h : GA D D.sp.X'} (hh : h ∈ GfC D.sp.X') : HasMat h (finPt h).1 :=
  ⟨hh, fun i j => (finN_apply D.sp.X' (rankP D) h (finCongr (rankP D) i) (finCongr (rankP D) j)).symm⟩

end Law

section Form

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}

end Form

end GlobalTheory.Core.Rk.TopOnto

end
end
