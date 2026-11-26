module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartRealisationWithScalarsCharOfWeak
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeLocalContainmentAtPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraAlt
namespace GlobalTheory.TargetLemmaCollection

open NumberField

theorem main {K : Type} [Field K] [NumberField K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (RingOfIntegers K) Z] [IsScalarTower (RingOfIntegers K) K Z]
    {A : Submodule (RingOfIntegers K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    have e1 : (d₁ * d₂) • y = d₂ • (d₁ • y) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • z = d₁ • (d₂ • z) := by rw [mul_smul]
    rw [e1, e2]
    exact A.add_mem (A.smul_mem _ h₁) (A.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c
    simp only at hab
    have hb : (b : RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : RingOfIntegers K) * d, mul_ne_zero hb hd, ?_⟩
    have key : ((b : RingOfIntegers K) * d) • (c • y) = a • (d • y) := by
      rw [← smul_assoc, Algebra.smul_def, map_mul, mul_comm (algebraMap _ K (b : RingOfIntegers K)),
        mul_assoc, mul_comm _ c, hab, ← map_mul, algebraMap_smul, mul_comm, mul_smul]
    rw [key]
    exact A.smul_mem _ h

end GlobalTheory.TargetLemmaCollection

theorem GlobalTheory.TargetLemmaCollection.target : ∀ {K : Type} [inst : Field K] [NumberField K] {Z : Type} [inst_2 : AddCommGroup Z] [inst_3 : Module K Z] [inst_4 : Module (NumberField.RingOfIntegers K) Z] [IsScalarTower (NumberField.RingOfIntegers K) K Z] {A : Submodule (NumberField.RingOfIntegers K) Z} {x : Z}, x ∈ Submodule.span K (↑A : Set Z) → ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ A :=
  fun hx => GlobalTheory.TargetLemmaCollection.main hx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeLocalContainmentAtPairs
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OnRankAlg

section Gen

variable {K : Type} [Field K] [NumberField K]
variable {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

theorem exists_smul_mem_of_mem_span {A : Submodule (𝓞 K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.TargetLemmaCollection.target
  | exact _root_.GlobalTheory.TargetLemmaCollection.target
  | (apply _root_.GlobalTheory.TargetLemmaCollection.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetLemmaCollection.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetLemmaCollection.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetLemmaCollection.target ..)

theorem span_cut {A : Submodule (𝓞 K) Z} (hA : Submodule.span K (A : Set Z) = ⊤) (W : Submodule K Z) :
    Submodule.span K (Formalism.EigenvalueLevelCeiling.cut W A : Set Z) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.1 hx).2
  · intro w hw
    obtain ⟨d, hd, hm⟩ := exists_smul_mem_of_mem_span (A := A) (x := w) (by rw [hA]; trivial)
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd
    have hmem : d • w ∈ Formalism.EigenvalueLevelCeiling.cut W A := by
      refine Submodule.mem_inf.2 ⟨hm, ?_⟩
      show d • w ∈ W
      rw [← algebraMap_smul K d w]
      exact W.smul_mem _ hw
    have hw' : w = (algebraMap (𝓞 K) K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hw']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem span_le_span_sc {a : K} (ha : a ≠ 0) (A : Submodule (𝓞 K) Z) :
    Submodule.span K (A : Set Z) ≤ Submodule.span K (Formalism.EigenvalueLevelCeiling.sc a A : Set Z) := by
  rw [Submodule.span_le]
  intro y hy
  have hm : a • y ∈ Formalism.EigenvalueLevelCeiling.sc a A := Submodule.mem_map.2 ⟨y, hy, rfl⟩
  have hy' : y = a⁻¹ • (a • y) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hy']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem locP_subset_span (v : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) Z) :
    (Formalism.HermitianLatticesTheory.localization₂ v.asIdeal L : Set Z) ⊆ Submodule.span K (L : Set Z) := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  have hs' : algebraMap (𝓞 K) K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hs0
  have hx' : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
    rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs', one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

variable {P : Type} [Group P]

theorem mem_eig_iff (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (x : Z) :
    x ∈ Formalism.EigenvalueLevelCeiling.eig ρ U ψ ↔ ∀ u : U, ρ u x = ((ψ u : 𝓞 K) : K) • x := by
  unfold Formalism.EigenvalueLevelCeiling.eig
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem map_eig (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (e : Z →ₗ[K] Z) (V₀ : Submodule K Z)
    (hp : e ∘ₗ e = e ∧ LinearMap.range e = V₀) (hc : ∀ g : P, e ∘ₗ ρ g = ρ g ∘ₗ e) :
    (Formalism.EigenvalueLevelCeiling.eig ρ U ψ).map e = Formalism.EigenvalueLevelCeiling.eig ρ U ψ ⊓ V₀ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.2 ⟨(mem_eig_iff ρ U ψ _).2 fun u => ?_, by rw [← hp.2]; exact LinearMap.mem_range_self e x⟩
    have h := congrArg (fun f : Z →ₗ[K] Z => f x) (hc u)
    simp only [LinearMap.comp_apply] at h
    rw [← h, (mem_eig_iff ρ U ψ x).1 hx u, map_smul]
  · intro x hx
    obtain ⟨hx, hv⟩ := Submodule.mem_inf.1 hx
    rw [← hp.2] at hv
    obtain ⟨y, rfl⟩ := hv
    exact ⟨e y, hx, congrArg (fun f : Z →ₗ[K] Z => f y) hp.1⟩

theorem isLatIn_map (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (e : Z →ₗ[K] Z) (V₀ : Submodule K Z)
    (hp : e ∘ₗ e = e ∧ LinearMap.range e = V₀) (hc : ∀ g : P, e ∘ₗ ρ g = ρ g ∘ₗ e) {A : Submodule (𝓞 K) Z}
    (hfg : A.FG) (hle : A ≤ (Formalism.EigenvalueLevelCeiling.eig ρ U ψ).restrictScalars (𝓞 K))
    (hge : (Formalism.EigenvalueLevelCeiling.eig ρ U ψ : Set Z) ⊆ Submodule.span K (A : Set Z)) :
    Formalism.EigenvalueLevelCeiling.IsLatIn (Formalism.EigenvalueLevelCeiling.eig ρ U ψ ⊓ V₀) (A.map (e.restrictScalars (𝓞 K))) := by
  refine ⟨hfg.map _, ?_⟩
  have hs : Submodule.span K (A : Set Z) = Formalism.EigenvalueLevelCeiling.eig ρ U ψ :=
    le_antisymm (Submodule.span_le.2 fun x hx => hle hx) hge
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hs, map_eig ρ U ψ e V₀ hp hc]

end Gen

theorem rankAtPlaces_alg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (c : OnConst) (O : OnObj S P c), LeafSpan O → LeafData O → LeafProj O → (∀ j (g : P), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j) → (AtPair S fun v => ∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) → RankAtPlaces O := by
  intro K _ _ _ Bs Df S P _ _ c O hSp hD hPr hc hJ w hw
  have one : ∀ v : HeightOneSpectrum (𝓞 K),
      (∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Th v j) ∧ Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.ThK v j)) →
      (∀ j, (O.Th0 v j).FG ∧ O.Th0 v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
        Formalism.EigenvalueLevelCeiling.sc ((Nat.card O.U : ℕ) : K) (Formalism.EigenvalueLevelCeiling.cut (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ) (O.ThK v j)) ≤ O.Th0 v j) →
      (∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
        Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) →
      ∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
        Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j) := by
    intro v hs hd hj j
    have hU : ((Nat.card O.U : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have h0 : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ : Set (Fin (O.nZ j) → K)) ⊆ (Submodule.span K (O.Th0 v j : Set (Fin (O.nZ j) → K)) : Set (Fin (O.nZ j) → K)) := by
      intro x hx
      have h1 : x ∈ Submodule.span K (Formalism.EigenvalueLevelCeiling.cut (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ) (O.ThK v j) : Set (Fin (O.nZ j) → K)) := by
        rw [span_cut (hs j).2.2]; exact hx
      exact Submodule.span_mono (fun y hy => (hd j).2.2 hy) (span_le_span_sc hU _ h1)
    have hJs : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ : Set (Fin (O.nZ j) → K)) ⊆ (Submodule.span K (O.ThJ v j : Set (Fin (O.nZ j) → K)) : Set (Fin (O.nZ j) → K)) := by
      intro x hx
      exact Submodule.span_le.2 (fun y hy => locP_subset_span v _ ((hj j).2.2 (Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hy))) (h0 hx)
    exact ⟨isLatIn_map (O.ρ j) O.U O.ψ (O.e j) (O.V₀ j) (hPr j) (hc j) (hd j).1 (hd j).2.1 h0,
      isLatIn_map (O.ρ j) O.U O.ψ (O.e j) (O.V₀ j) (hPr j) (hc j) (hj j).1 (hj j).2.1 hJs, (hj j).2.2⟩
  exact ⟨one w (hSp w hw).1 (hD w hw).1 (hJ w hw).1, one _ (hSp w hw).2 (hD w hw).2 (hJ w hw).2⟩

end GlobalTheory.OnRankAlg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeLocalContainmentAtPairsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenlattice_local_containment_at_pairs : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (c : OnConst) (O : OnObj S P c), LeafSpan O → LeafData O → LeafProj O → (∀ j (g : P), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j) → (AtPair S fun v => ∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) → RankAtPlaces O := by
  first | exact @GlobalTheory.OnRankAlg.rankAtPlaces_alg | exact GlobalTheory.OnRankAlg.rankAtPlaces_alg | (intros; apply GlobalTheory.OnRankAlg.rankAtPlaces_alg <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.TraceClassRank

section General

open scoped TensorProduct

attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem goodOp_rho_comm {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (j : Fin D.R.m) (g : G) (x : Fin (R.nW j) → D.what₂.LL) :
    OntoChain.goodOp R j ((R.FW j).ρ g x) = (R.FW j).ρ g (OntoChain.goodOp R j x) := by
  have h := LinearMap.congr_fun (goodOp_comm (R := R) hX j g) x
  simp only [LinearMap.comp_apply, twRep_apply, map_smul] at h
  have h' := congrArg (fun y => (((R.FW j).chi g : D.what₂.LLˣ) : D.what₂.LL) • y) h
  simp only [smul_smul, Units.mul_inv, one_smul] at h'
  exact h'

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem tie_e_comm_rho (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (ha : ActionPin h fw ι ℓ)
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (g : P) : O.e i ∘ₗ O.ρ i g = O.ρ i g ∘ₗ O.e i := by
  refine LinearMap.ext fun x => (toForms_bijective h fw ι z).1 ?_
  simp only [LinearMap.comp_apply]
  rw [t.e_eOp, t.rho_eq_of_actionPin ha, t.rho_eq_of_actionPin ha, t.e_eOp]
  exact goodOp_rho_comm hX ι (inc g) _

theorem tie_thetaJ (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (ha : ActionPin h fw ι ℓ)
    (hi : Function.Injective inc) (hU : U ≤ inc.range) (hd : FormsDetermined R ι) (hM : SpanOverClasses R ι U ψ ph v p)
    (hty : ∀ x ∈ thetaBase R ι U ψ ph v p, ∀ u : U, (R.FW ι).ρ u x = ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • x)
    {n : ℕ} (hp : RunPin R ι n v p) (hA : CompareOffOwn h fw ι ℓ U ψ ph v p) :
    (O.ThJ v i).FG ∧ O.ThJ v i ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v i) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v i) := by
  have hb := toForms_bijective h fw ι z
  refine ⟨?_, fun x hx => ?_, trace_lattice_le_theta_lattice_at_place t hi hU hp hA⟩
  · refine Submodule.fg_of_fg_map_injective ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) hb.1 ?_
    rw [t.ThJ_eq, Submodule.map_comap_eq_of_surjective (f := (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) hb.2]
    exact thetaBase_fg hd hM
  · rw [t.ThJ_eq] at hx
    have hx' : toForms h fw ι z x ∈ thetaBase R ι U ψ ph v p := hx
    change x ∈ Formalism.EigenvalueLevelCeiling.eig _ _ _
    unfold Formalism.EigenvalueLevelCeiling.eig
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro u
    have hU' : ∀ g : P, g ∈ O.U → inc g ∈ U := fun g hg => by
      rw [t.U_eq] at hg
      exact hg
    have hu : inc u ∈ U := hU' u u.2
    apply hb.1
    rw [t.rho_eq_of_actionPin ha, hty _ hx' ⟨inc u, hu⟩, map_smul, t.ψ_eq u hu]

end General

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}

theorem conjPl_mem_twPl (hC : (R2 p).Char (F2 p)) {w : HeightOneSpectrum (𝓞 D.what₂.LL)} (hw : w ∈ p.R.twPl) :
    Formalism.DivisionValues.conjPl w ∈ p.R.twPl := by
  by_contra h
  exact hC.tup.mu_ne w hw ((hC.tup.mu_conj w).symm.trans (hC.tup.mu_off _ h))

end Point

end GlobalTheory.BigOn

end
