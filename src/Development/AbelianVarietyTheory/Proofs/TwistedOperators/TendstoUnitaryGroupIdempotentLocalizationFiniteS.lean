module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulOfStableGraph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoUnitaryGroupIdempotentLocalizationFiniteS
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoUnitaryGroupIdempotentLocalizationFiniteS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_snd_one_sub_idemS :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) => sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) atTop (𝓝 0) := by
  classical
  have hin : ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) w, w ∈ T → evalV F w (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) = 0 := by
    intro T w hw
    change evFin F w (1 - GlobalTheory.FinDecomp.idemS F T) = 0
    rw [map_sub, map_one, GlobalTheory.FinDecomp.evFin_idemS, if_pos hw, sub_self]
  have hint : ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) w,
      evalV F w (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) ∈ w.adicCompletionIntegers F := by
    intro T w
    change evFin F w (1 - GlobalTheory.FinDecomp.idemS F T) ∈ w.adicCompletionIntegers F
    rw [map_sub, map_one, GlobalTheory.FinDecomp.evFin_idemS]
    split_ifs
    · rw [sub_self]; exact zero_mem _
    · rw [sub_zero]; exact one_mem _
  let A : ∀ w : HeightOneSpectrum (𝓞 F), Set (w.adicCompletion F) := fun w => w.adicCompletionIntegers F
  let o : ∀ w, A w := fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩
  let g : Finset (HeightOneSpectrum (𝓞 F)) → ∀ w, A w := fun T w => ⟨_, hint T w⟩
  have hg : Tendsto g atTop (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({w} : Finset _)] with T hT
    exact Subtype.ext (hin T w (hT (Finset.mem_singleton_self w))).symm
  have h := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  exact h

end GlobalTheory.FinDecompLim
end

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_infIdem : At (evI F) (pairA F 1 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * 1, u.2 * 0) = (0, 0)
  rw [h1, zero_mul, mul_zero]

theorem one_sub_idemS_eq (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) :
    1 - GlobalTheory.FinDecomp.idemS F T = pairA F 1 0 + pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) := by
  have h := GlobalTheory.FinDecomp.fst_idemS (F := F) T
  refine Prod.ext ?_ ?_
  · change 1 - fstA F (GlobalTheory.FinDecomp.idemS F T) = 1 + 0
    rw [h, sub_zero, add_zero]
  · change sndA F (1 - GlobalTheory.FinDecomp.idemS F T) = 0 + sndA F (1 - GlobalTheory.FinDecomp.idemS F T)
    rw [zero_add]

theorem tendsto_cut :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) => pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T))) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (0 : Ainf F))).prodMk_nhds (tendsto_snd_one_sub_idemS (F := F))
  exact h

theorem tendsto_phi {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE F E)) (hM : pairA F 1 0 • (M - 1) = 0) :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) => GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M) atTop (𝓝 M) := by
  have key : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M =
      M + pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) • (1 - M) := by
    intro T
    have h0 : pairA F 1 0 • (1 - M) = 0 := by rw [← neg_sub, smul_neg, hM, neg_zero]
    have h1 : GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M = M + (1 - GlobalTheory.FinDecomp.idemS F T) • (1 - M) := by
      simp only [GlobalTheory.FinDecomp.phi, sub_smul, smul_sub, one_smul]; abel
    rw [h1, congrArg (· • (1 - M)) (one_sub_idemS_eq T), add_smul, h0, zero_add]
  simp_rw [key]
  have h := (tendsto_const_nhds (x := M)).add ((tendsto_cut (F := F)).smul_const (1 - M))
  have e : M + (0 : AF F) • (1 - M) = M := by rw [zero_smul, add_zero]
  rw [e] at h
  exact h

end GlobalTheory.FinDecompLim
end

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

theorem tendsto_loc_idemS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J),
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K - 1) = 0) →
    Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idemS F T) (GlobalTheory.FinDecomp.idemS_mul_self T) K) Filter.atTop (nhds K) := by
  intro F E _ _ _ _ _ σ d J K hK
  have hM : pairA F 1 0 • (mat K - 1) = 0 := hK _ at_infIdem
  have hN : pairA F 1 0 • (mat K⁻¹ - 1) = 0 := by
    have h : mat K⁻¹ - 1 = mat K⁻¹ * (1 - mat K) := by
      rw [Matrix.mul_sub, Matrix.mul_one, GlobalTheory.FinDecomp.mat_inv_mul]
    rw [h, ← Matrix.mul_smul, ← neg_sub (mat K), smul_neg, hM, neg_zero, Matrix.mul_zero]
  rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  change Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) (mat K),
        MulOpposite.op (GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) (mat K⁻¹)))) atTop
      (𝓝 (mat K, MulOpposite.op (mat K⁻¹)))
  exact (tendsto_phi _ hM).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (tendsto_phi _ hN))

end GlobalTheory.FinDecompLim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoUnitaryGroupIdempotentLocalizationFiniteSStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_unitaryGroupIdempotentLocalization_finiteSets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J),
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K - 1) = 0) →
    Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idemS F T) (GlobalTheory.FinDecomp.idemS_mul_self T) K) Filter.atTop (nhds K) := by
  first | exact @GlobalTheory.FinDecompLim.tendsto_loc_idemS | exact GlobalTheory.FinDecompLim.tendsto_loc_idemS | (intros; apply GlobalTheory.FinDecompLim.tendsto_loc_idemS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupportUnitaryPointReplacesPureTensorFacto
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupportUnitaryPointReplacesPureTensorFacto
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PlaceProd

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}

theorem mat_injOne (g : UA σ X.J) (h : mat g = 1) : g = 1 := Subtype.ext (Units.ext h)

theorem mat_mul' (g k : UA σ X.J) : mat (g * k) = mat g * mat k := rfl

theorem mat_one' : mat (1 : UA σ X.J) = 1 := rfl

theorem mat_inv_mul' (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

theorem one_mem_UAt {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  rw [mat_one', sub_self, smul_zero]

end GlobalTheory.PlaceProd


open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaceProd GlobalTheory.AdelicU in
theorem GlobalTheory.PlaceProd.pure_of_finSupp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (gS : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J),
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ v ∉ S, φ' v = φ v) ∧
        (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
        om (gS, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP S
  have hstd := hP.good.std
  induction S using Finset.induction_on with
  | empty =>
    intro gS hgS f φ hSB _
    have h1 : mat gS = 1 := by
      have := hgS 1 (by simp)
      rwa [one_smul, sub_eq_zero] at this
    have hg : gS = 1 := mat_injOne gS h1
    refine ⟨φ, hSB, fun _ _ => rfl, fun v => by simp, ?_⟩
    subst hg
    rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one]
    rfl
  | @insert v S' hv ih =>
    intro gS hgS f φ hSB hvac
    obtain ⟨g1, k, hgk, h2, h3, -, -⟩ := GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces σ X gS {v}
    have hg1 : g1 ∈ UAt σ X (evFin F v) := fun u hu =>
      h2 u (fun w hw => by rw [Finset.mem_singleton.1 hw]; exact hu)
    have hk : ∀ u : AF F, (∀ w ∈ S', evFin F w u = 0) → u • (mat k - 1) = 0 := by
      intro u hu
      set e : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he
      have hsplit : u = e * u + (1 - e) * u := by ring
      have ha : (e * u) • (mat k - 1) = 0 := by
        apply h3 v (Finset.mem_singleton_self v)
        rw [he, GlobalTheory.ThK.LocalOps.liftV_one_mul]
        intro u' hu'
        exact GlobalTheory.LatVac.at_liftV v _ u' hu'
      have hb : ((1 - e) * u) • (mat k - 1) = 0 := by
        set u' : AF F := (1 - e) * u with hu'def
        have hv' : evFin F v u' = 0 := by
          simp [hu'def, he, map_mul, map_sub, GlobalTheory.LatVac.evFin_liftV]
        have hS : u' • (mat gS - 1) = 0 := hgS u' (by
          intro w hw
          rcases Finset.mem_insert.1 hw with rfl | hw
          · exact hv'
          · simp [hu'def, map_mul, hu w hw])
        have hg1' : u' • (mat g1 - 1) = 0 := hg1 u' hv'
        have hkk : k = g1⁻¹ * gS := by rw [hgk, inv_mul_cancel_left]
        have hkdef : mat k - 1 = mat g1⁻¹ * (mat gS - 1) - mat g1⁻¹ * (mat g1 - 1) := by
          rw [hkk, mat_mul', Matrix.mul_sub, Matrix.mul_sub, mat_inv_mul', Matrix.mul_one]
          abel
        rw [hkdef, smul_sub, ← Matrix.mul_smul, ← Matrix.mul_smul, hS, hg1', Matrix.mul_zero, sub_self]
      rw [hsplit, add_smul, ha, hb, add_zero]
    obtain ⟨φ₁, hSB1, hoff1, haug1, hom1⟩ := ih k hk f φ hSB hvac
    obtain ⟨φ₂, hSB2, hact⟩ :=
      GlobalTheory.ThK.LocalOps.acts_exists hP v (g1, 1) hg1 (one_mem_UAt (evFin F v)) (φ₁ v) (hSB1 v)
    have hnot : ∀ᶠ w in Filter.cofinite, w ∉ S' :=
      Filter.eventually_cofinite.2 (S'.finite_toSet.subset fun x hx => by simpa using hx)
    have hstd1 : ∀ᶠ w in Filter.cofinite,
        φ₁ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
      filter_upwards [hvac, hstd, hnot] with w h1 h2 h3
      rw [hoff1 w h3, h1, h2]
    have hpure := GlobalTheory.TensUniq.pure_mem_schA f φ₁ hSB1 hstd1
    have hstep := GlobalTheory.ThK.LocalOps.acts_pure v (om (g1, 1)) f φ₁ φ₂ hpure
      (GlobalTheory.PureFactor.mulSupport_finite φ₁ hstd1) hact
    refine ⟨Function.update φ₁ v φ₂, ?_, ?_, ?_, ?_⟩
    · intro w
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hSB2
      · rw [Function.update_of_ne hw]; exact hSB1 w
    · intro w hw
      have hwv : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
      have hwS : w ∉ S' := fun h => hw (Finset.mem_insert_of_mem h)
      rw [Function.update_of_ne hwv]; exact hoff1 w hwS
    · intro w
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self, ← hoff1 w hv]
        exact Submodule.subset_span ⟨g1, hg1, φ₁ w, hSB1 w, φ₂, hSB2, hact, rfl⟩
      · rw [Function.update_of_ne hw]; exact haug1 w
    · rw [hgk, show ((g1 * k, 1) : UA σ X.J × UA σ W.J) = (g1, 1) * (k, 1) by simp, map_mul,
        Module.End.mul_apply, hom1, hstep]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupportUnitaryPointReplacesPureTensorFactoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteSupport_unitaryPoint_replaces_pureTensorFactors : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (gS : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J),
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ v ∉ S, φ' v = φ v) ∧
        (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
        om (gS, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  first | exact @GlobalTheory.PlaceProd.pure_of_finSupp | exact GlobalTheory.PlaceProd.pure_of_finSupp | (intros; apply GlobalTheory.PlaceProd.pure_of_finSupp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallModelThetaTransformInjectiveProducts
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallModelThetaTransformInjectiveProducts
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

namespace GlobalTheory.SmallDat.ThBox

theorem isThetaFunO_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T S₁ T₁ S₂ T₂ : HSp D} (p₁ : WO S T →+ WO S₁ T₁)
    (p₂ : WO S T →+ WO S₂ T₂) (c₁ : Continuous p₁) (c₂ : Continuous p₂)
    (hs : ∀ x y, symplO S T x y = symplO S₁ T₁ (p₁ x) (p₁ y) + symplO S₂ T₂ (p₂ x) (p₂ y))
    (r₁ : ∀ γ, ∃ γ', p₁ (ratW T S γ) = ratW T₁ S₁ γ') (r₂ : ∀ γ, ∃ γ', p₂ (ratW T S γ) = ratW T₂ S₂ γ')
    (hi : ∀ u, u.map (infPart D) = 0 → (p₁ u).map (infPart D) = 0 ∧ (p₂ u).map (infPart D) = 0)
    (hf : ∀ u, u.map (finPart D) = 0 → (p₁ u).map (finPart D) = 0 ∧ (p₂ u).map (finPart D) = 0)
    {f₁ : WO S₁ T₁ → ℂ} {f₂ : WO S₂ T₂ → ℂ} (h₁ : IsThetaFunO ψ S₁ T₁ f₁) (h₂ : IsThetaFunO ψ S₂ T₂ f₂) :
    IsThetaFunO ψ S T fun u => f₁ (p₁ u) * f₂ (p₂ u) := by
  have hH : ∀ x y, symplOH S T x y = symplOH S₁ T₁ (p₁ x) (p₁ y) + symplOH S₂ T₂ (p₂ x) (p₂ y) := fun x y => by
    unfold symplOH
    rw [hs, mul_add]
  refine ⟨fun γ w => ?_, ?_, (h₁.cont.comp c₁).mul (h₂.cont.comp c₂), fun k L hL hL0 w => ?_⟩
  · obtain ⟨γ₁, e₁⟩ := r₁ γ
    obtain ⟨γ₂, e₂⟩ := r₂ γ
    rw [map_add (f := _), map_add (f := _), hH, e₁, e₂, h₁.quasi, h₂.quasi, neg_add, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, o₁, hU₁⟩ := h₁.level
    obtain ⟨U₂, o₂, hU₂⟩ := h₂.level
    refine ⟨U₁.comap p₁ ⊓ U₂.comap p₂, (o₁.preimage c₁).inter (o₂.preimage c₂), fun u hu h0 => funext fun w => ?_⟩
    have a₁ := congrFun (hU₁ (p₁ u) hu.1 (hi u h0).1) (p₁ w)
    have a₂ := congrFun (hU₂ (p₂ u) hu.2 (hi u h0).2) (p₂ w)
    unfold heisO at a₁ a₂ ⊢
    beta_reduce
    rw [← a₁, ← a₂, hH, map_add (f := p₁), map_add (f := p₂), AddChar.map_add_eq_mul]
    ring
  · simp only [map_add (f := _)]
    exact (h₁.smooth k (p₁.comp L) (c₁.comp hL) (fun t => (hf _ (hL0 t)).1) (p₁ w)).mul
      (h₂.smooth k (p₂.comp L) (c₂.comp hL) (fun t => (hf _ (hL0 t)).2) (p₂ w))

theorem mulG_map_zero {D : D7} {R : Type} [CommRing R] (φ : AE D →+* R) (S : HSp D) {n : ℕ}
    (x : Matrix (Fin n) (Fin S.rank) (AE D)) (h : x.map φ = 0) : (mulG S x).map φ = 0 := by
  rw [GlobalTheory.BigDat.mulG_eq, Matrix.map_mul, h, Matrix.zero_mul]

theorem continuous_mulG {D : D7} (S : HSp D) {n : ℕ} : Continuous (mulG S (n := n)) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact continuous_id.matrix_mul continuous_const

theorem mulG_rat {D : D7} (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) D.host.E) :
    mulG S (x.map (incA D)) = (x * S.gram).map (incA D) := by
  rw [GlobalTheory.BigDat.mulG_eq, Matrix.map_mul]

theorem infPart_cA {D : D7} (x : AE D) :
    infPart D (cA D x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem finPart_cA {D : D7} (x : AE D) :
    finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem maps_map_zero {R : Type} [CommRing R] (φ : AE D →+* R) (hφ : ∀ x, φ x = 0 → φ (cA D x) = 0) (t : T)
    (e : Num G i j) (u : PtS G i j) (h : u.map φ = 0) : (mapA t e u).map φ = 0 ∧ (mapB e u).map φ = 0 := by
  have h0 : ∀ a b, φ (u a b) = 0 := fun a b => congrFun (congrFun h a) b
  refine ⟨mulG_map_zero φ _ _ (Matrix.ext fun a b => h0 _ _), ?_⟩
  have h2 := mulG_map_zero φ (spV₁ G i j) ((u.submatrix id fun k => e (.inr k)).map (cA D))
    (Matrix.ext fun a b => hφ _ (h0 _ _))
  exact Matrix.ext fun a b => (map_neg φ _).trans (neg_eq_zero.2 (congrFun (congrFun h2 a) b))

theorem continuous_mapA (t : T) (e : Num G i j) : Continuous (mapA t e) :=
  (continuous_mulG (spW₁ G i j)).comp (continuous_id.matrix_submatrix id fun k => e (.inl k)).matrix_transpose

theorem continuous_mapB (e : Num G i j) : Continuous (mapB e) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact ((continuous_mulG (spV₁ G i j)).comp ((continuous_id.matrix_submatrix id fun k => e (.inr k)).matrix_map
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D))).neg

theorem mapA_rat (t : T) (e : Num G i j)
    (γ : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) D.host.E) :
    ∃ γ', mapA t e (γ.map (incA D)) = ratW (G.pT (.mu t i j)) (G.pS (.mu t i j)) γ' :=
  ⟨_, mulG_rat (spW₁ G i j) (γ.submatrix id fun k => e (.inl k))ᵀ⟩

theorem mapB_rat (e : Num G i j)
    (γ : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) D.host.E) :
    ∃ γ', mapB e (γ.map (incA D)) = ratW (G.pT (.chi i j)) (G.pS (.chi i j)) γ' :=
  ⟨-_, (congrArg Neg.neg (mulG_rat (spV₁ G i j) ((γ.submatrix id fun k => e (.inr k)).map star))).trans
    (Matrix.map_neg _ (map_neg (incA D)) _).symm⟩

theorem thetaS_box : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    (∀ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), ∀ Φ' ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ (Φ + Φ') = GlobalTheory.SmallDat.thetaS Γ W.ψ Φ + GlobalTheory.SmallDat.thetaS Γ W.ψ Φ') ∧
    (∀ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), ∀ Φ' ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ Φ = GlobalTheory.SmallDat.thetaS Γ W.ψ Φ' → Φ = Φ') ∧
    ∀ (f₁ : GlobalTheory.SmallDat.HomA G t i j → ℂ) (f₂ : GlobalTheory.SmallDat.HomB G i j → ℂ), IsThetaFunO W.ψ _ _ f₁ → IsThetaFunO W.ψ _ _ f₂ →
      ∃ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ Φ = GlobalTheory.SmallDat.boxS t e f₁ f₂ := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hT.base _ Γ.V' _ _ hT.geo.hV'
  obtain ⟨hJ, L', hL, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hT.base _ Γ.W _ _ hT.geo.hW
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T₀ := GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hT.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))
  let S₀ := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 L' hL h6 (fun _ => (0, 0))
  have eA : Γ.V'.J = T₀.gramᵀ := by rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; rfl
  have eB : (-1 : AE D) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S₀.gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AE D) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hψ : IsStdChar D W.ψ (-1) := h.ψ ▸ GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D Bs.ψ hT.base.std
  obtain ⟨ha, hi, hs⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := S₀) (T := T₀) Γ.M'.co hψ eA eB hT.geo.hM'.rat
  refine ⟨ha, hi, fun f₁ f₂ hf₁ hf₂ => (hs _).1 ?_⟩
  exact isThetaFunO_mul (S := S₀) (T := T₀) (AddMonoidHom.mk' (mapA t e) (mapA_add t e))
    (AddMonoidHom.mk' (mapB e) (mapB_add e)) (continuous_mapA t e) (continuous_mapB e)
    (fun x y => (GlobalTheory.ThetaTransform.symplO_eq_symp eA eB x y).trans (sympS_eq t e Γ h.JW₁ h.JWW x y))
    (mapA_rat t e) (mapB_rat e)
    (maps_map_zero (infPart D) (fun x hx => by rw [infPart_cA, hx, map_zero]) t e)
    (maps_map_zero (finPart D) (fun x hx => by rw [finPart_cA, hx, map_zero]) t e) hf₁ hf₂

end GlobalTheory.SmallDat.ThBox

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallModelThetaTransformInjectiveProductsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallModel_thetaTransform_injective_products : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    (∀ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), ∀ Φ' ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ (Φ + Φ') = GlobalTheory.SmallDat.thetaS Γ W.ψ Φ + GlobalTheory.SmallDat.thetaS Γ W.ψ Φ') ∧
    (∀ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), ∀ Φ' ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ Φ = GlobalTheory.SmallDat.thetaS Γ W.ψ Φ' → Φ = Φ') ∧
    ∀ (f₁ : GlobalTheory.SmallDat.HomA G t i j → ℂ) (f₂ : GlobalTheory.SmallDat.HomB G i j → ℂ), IsThetaFunO W.ψ _ _ f₁ → IsThetaFunO W.ψ _ _ f₂ →
      ∃ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ Φ = GlobalTheory.SmallDat.boxS t e f₁ f₂ := by
  first | exact @GlobalTheory.SmallDat.ThBox.thetaS_box | exact GlobalTheory.SmallDat.ThBox.thetaS_box | (intros; apply GlobalTheory.SmallDat.ThBox.thetaS_box <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockFrameChangeLastColumnDefinitePair
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockFrameChangeLastColumnDefinitePair
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FockFrameChange

private theorem sum4_lemma {α β γ δ R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid R]
    (f : α → β → γ → δ → R) :
    ∑ k, ∑ l, ∑ k', ∑ l', f k l k' l' = ∑ k', ∑ l', ∑ k, ∑ l, f k l k' l' := by
  calc ∑ k, ∑ l, ∑ k', ∑ l', f k l k' l' = ∑ k, ∑ k', ∑ l, ∑ l', f k l k' l' :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k', ∑ k, ∑ l, ∑ l', f k l k' l' := Finset.sum_comm
    _ = ∑ k', ∑ k, ∑ l', ∑ l, f k l k' l' :=
        Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k', ∑ l', ∑ k, ∑ l, f k l k' l' := Finset.sum_congr rfl fun k' _ => Finset.sum_comm

theorem substF_mul {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) =
      GlobalTheory.CompactHowe.substF (fun τ => h τ * h' τ) (fun τ => g τ * g' τ) P := by
  unfold GlobalTheory.CompactHowe.substF
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  refine congrArg (fun F => (MvPolynomial.aeval F) P) (funext fun p => ?_)
  obtain ⟨τ, a, b⟩ := p
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine (sum4_lemma _).trans ?_
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l' _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem change_mul {n : ℕ} {A F : Matrix (Fin n) (Fin n) ℂ} (hA : A * A⁻¹ = 1) (hF : F * F⁻¹ = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) : F⁻¹ * A * (A⁻¹ * M * A) = F⁻¹ * M * F * (F⁻¹ * A) := by
  calc F⁻¹ * A * (A⁻¹ * M * A) = F⁻¹ * (A * A⁻¹) * M * A := by simp only [Matrix.mul_assoc]
    _ = F⁻¹ * M * A := by rw [hA, Matrix.mul_one]
    _ = F⁻¹ * M * (F * F⁻¹) * A := by rw [hF, Matrix.mul_one]
    _ = F⁻¹ * M * F * (F⁻¹ * A) := by simp only [Matrix.mul_assoc]

theorem change_mul_invT {n : ℕ} {A F : Matrix (Fin n) (Fin n) ℂ} (hA : A * A⁻¹ = 1) (hF : F * F⁻¹ = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ((F⁻¹ * A)⁻¹).transpose * ((A⁻¹ * M * A)⁻¹).transpose = ((F⁻¹ * M * F)⁻¹).transpose * ((F⁻¹ * A)⁻¹).transpose := by
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_inv_rev (F⁻¹ * A) (A⁻¹ * M * A),
    ← Matrix.mul_inv_rev (F⁻¹ * M * F) (F⁻¹ * A), change_mul hA hF M]

theorem subst_change {ι : Type} {N n : ℕ} {A F : ι → Matrix (Fin N) (Fin N) ℂ} {A' F' : ι → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ τ, A τ * (A τ)⁻¹ = 1) (hF : ∀ τ, F τ * (F τ)⁻¹ = 1) (hA' : ∀ τ, A' τ * (A' τ)⁻¹ = 1)
    (hF' : ∀ τ, F' τ * (F' τ)⁻¹ = 1) (M : ι → Matrix (Fin N) (Fin N) ℂ) (M' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * A τ).map (starRingEnd ℂ))
                 (fun τ => ((((F' τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ))
                 (GlobalTheory.CompactHowe.substF (fun τ => ((A τ)⁻¹ * M τ * A τ).map (starRingEnd ℂ))
                   (fun τ => ((((A' τ)⁻¹ * M' τ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) =
      GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * M τ * F τ).map (starRingEnd ℂ))
        (fun τ => ((((F' τ)⁻¹ * M' τ * F' τ)⁻¹).transpose).map (starRingEnd ℂ))
        (GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * A τ).map (starRingEnd ℂ))
          (fun τ => ((((F' τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) := by
  rw [substF_mul, substF_mul]
  exact congrArg₂ (fun h g => GlobalTheory.CompactHowe.substF h g P)
    (funext fun τ => by
      simp only [← Matrix.map_mul]
      rw [change_mul (hA τ) (hF τ)])
    (funext fun τ => by
      simp only [← Matrix.map_mul]
      rw [change_mul_invT (hA' τ) (hF' τ)])

theorem map_mul_inv {n : ℕ} {E : Type} [Field E] (φ : E →+* ℂ) (g : GL (Fin n) E) :
    g.1.map φ * (g.1.map φ)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  have h := (Matrix.isUnits_det_units g).map φ
  rw [RingHom.map_det] at h
  exact h

private theorem fock_frame_lemma {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BS A' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT A : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hBS : ∀ τ, BS τ * (BS τ)⁻¹ = 1) (hBT : ∀ τ, BT τ * (BT τ)⁻¹ = 1)
    (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) A' A f P =
      pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f
        (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * A τ).map (starRingEnd ℂ))
          (fun τ => ((((BS τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) := by
  have e1 : A' = fun τ => BS τ * ((BS τ)⁻¹ * A' τ) := by
    funext τ
    rw [← Matrix.mul_assoc, hBS τ, Matrix.one_mul]
  have e2 : A = fun τ => BT τ * ((BT τ)⁻¹ * A τ) := by
    funext τ
    rw [← Matrix.mul_assoc, hBT τ, Matrix.one_mul]
  conv_lhs => rw [e1, e2]
  exact GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D ψ θ S T hψ hθ BS (fun τ => (BS τ)⁻¹ * A' τ) BT
    (fun τ => (BT τ)⁻¹ * A τ) f hf P

theorem exists_frame_change : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∃ σ₀ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank,
      (∀ t ∈ U, ∀ d : FinDatum G t (.chi i D.R.m), S.Z.HasVec d → ∀ P,
        W.fock (.chi i D.R.m) (S.Z.vec d) P = fockIn W S.N.frC (.chi i D.R.m) (S.Z.vec d) (σ₀ P)) ∧
      ∀ k : GA D (G.V (.grid i D.R.m)), k ∈ GinfC (G.V (.grid i D.R.m)) →
        ∀ k' : GA D (G.V (.grid (i + 1) D.R.m)), k' ∈ GinfC (G.V (.grid (i + 1) D.R.m)) → ∀ P,
          σ₀ (realSubst W W.onb (.chi i D.R.m) k k' P) = realSubst W S.N.frC (.chi i D.R.m) k k' (σ₀ P) := by
  intro D T L sc G W U S μ0 hL i hi
  have hdT : DefNode D.R.m (Node.grid i D.R.m) := by
    unfold DefNode
    exact ⟨hi.le, rfl⟩
  have hdS : DefNode D.R.m (Node.grid (i + 1) D.R.m) := by
    unfold DefNode
    exact ⟨hi, rfl⟩
  have hdP : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := by
    unfold DefPair
    exact ⟨hi, rfl⟩
  have honb : ∀ X, DefNode D.R.m X → ∀ τ, W.onb X τ * (W.onb X τ)⁻¹ = 1 := fun X hX τ =>
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse (GlobalTheory.FockReal.onb_def hL W hX τ))
  have hfr : ∀ X τ, S.N.frC X τ * (S.N.frC X τ)⁻¹ = 1 := fun X τ => map_mul_inv (tauE D τ) (S.N.fr X)
  refine ⟨(GlobalTheory.CompactHowe.substF
      (fun τ => ((S.N.frC (Node.grid i D.R.m) τ)⁻¹ * W.onb (Node.grid i D.R.m) τ).map (starRingEnd ℂ))
      (fun τ => ((((S.N.frC (Node.grid (i + 1) D.R.m) τ)⁻¹ * W.onb (Node.grid (i + 1) D.R.m) τ)⁻¹).transpose).map
        (starRingEnd ℂ))).toLinearMap, ?_, ?_⟩
  · intro t _ d hd P
    have hf := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hdP d hd).1
    have hcS : G.cartS W.cart (Pair.chi i D.R.m : Pair T) = fun _ => -1 := by
      funext τ
      show -W.cart (Node.grid (i + 1) D.R.m) τ = -1
      rw [GlobalTheory.FockReal.cart_def hL W hdS τ]
    have hcT : G.onT W.cart (Pair.chi i D.R.m : Pair T) = fun _ => 1 := by
      funext τ
      exact GlobalTheory.FockReal.cart_def hL W hdT τ
    unfold GlobalTheory.ChiGrid.GridData.Weil.fock GlobalTheory.FunObj.fockIn
    rw [hcS, hcT, AlgHom.toLinearMap_apply]
    exact fock_frame_lemma W.ψ W.θ (G.V (Node.grid (i + 1) D.R.m)) (G.V (Node.grid i D.R.m)) W.ψ_std W.θ_is
      (S.N.frC (Node.grid (i + 1) D.R.m)) (W.onb (Node.grid (i + 1) D.R.m))
      (S.N.frC (Node.grid i D.R.m)) (W.onb (Node.grid i D.R.m))
      (hfr _) (hfr _) (S.Z.vec d) hf P
  · intro k _ k' _ P
    unfold GlobalTheory.FockReal.realSubst
    rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
    exact subst_change (A := W.onb (Node.grid i D.R.m)) (F := S.N.frC (Node.grid i D.R.m))
      (A' := W.onb (Node.grid (i + 1) D.R.m)) (F' := S.N.frC (Node.grid (i + 1) D.R.m))
      (fun τ => honb _ hdT τ) (hfr _) (fun τ => honb _ hdS τ) (hfr _) _ _ P

end GlobalTheory.FockFrameChange

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockFrameChangeLastColumnDefinitePairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockFrameChange_lastColumn_definitePair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∃ σ₀ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank,
      (∀ t ∈ U, ∀ d : FinDatum G t (.chi i D.R.m), S.Z.HasVec d → ∀ P,
        W.fock (.chi i D.R.m) (S.Z.vec d) P = fockIn W S.N.frC (.chi i D.R.m) (S.Z.vec d) (σ₀ P)) ∧
      ∀ k : GA D (G.V (.grid i D.R.m)), k ∈ GinfC (G.V (.grid i D.R.m)) →
        ∀ k' : GA D (G.V (.grid (i + 1) D.R.m)), k' ∈ GinfC (G.V (.grid (i + 1) D.R.m)) → ∀ P,
          σ₀ (realSubst W W.onb (.chi i D.R.m) k k' P) = realSubst W S.N.frC (.chi i D.R.m) k k' (σ₀ P) := by
  first | exact @GlobalTheory.FockFrameChange.exists_frame_change | exact GlobalTheory.FockFrameChange.exists_frame_change | (intros; apply GlobalTheory.FockFrameChange.exists_frame_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeRealPlacePureDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeRealPlacePureDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.HeisLineTransfer

theorem schr_schr_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' Φ) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') Φ x := by
  simp only [GlobalTheory.WeilM.schr, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm w'.1 w.2]
  first
    | linear_combination (w.1 ⬝ᵥ w'.2) * invOf_mul_self (2 : R)
    | linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

end GlobalTheory.HeisLineTransfer

namespace GlobalTheory.HeisLineTransfer


set_option maxHeartbeats 1600000 in
theorem isDatum_dRho_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f : WO S X → ℂ, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) (g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ (cS.symm (lineAt θ τ z 1))) g g₁ →
          IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hc g φ hφ hvac f hf τ z g₁ hact
  subst hψ
  obtain ⟨hΦ, hfΦ⟩ := hf
  have hF : IsTotallyReal D.host.F := hBs.cm.1
  have hψc : IsCharAF D.host.F Bs.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hBs.std
  have hstd : ∀ᶠ v in Filter.cofinite, φ v =
      Set.indicator {x : Fin S.rank × Fin d → v.adicCompletion D.host.F | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have h1 := GlobalTheory.TensUniq.pure_mem_schA g₁ φ hφ hstd
  refine ⟨h1, fun u => ?_⟩

  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E,
    (if ε then -1 else 1 : D.host.E) • S.gram = G := ⟨_, rfl⟩
  rw [hGdef] at hc
  have hs : (sgn ε S).gram = G := by
    rw [← hGdef]
    cases ε
    · ext i j; simp [sgn, HSpace.gram]
    · ext i j; simp [HSpace.gram]
  have hVJ : Vs.J = -G := by
    rw [hJ, ← hGdef]; cases ε <;> simp
  have hdet : IsUnit G.det := by rw [← hs]; exact (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hHG : (G⁻¹).map (incA D) * G.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (G.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (G.map (incA D))ᵀ := by
    ext i j
    have h := hV.herm j i
    rw [hVJ, Matrix.neg_apply, Matrix.neg_apply, map_neg, neg_inj] at h
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (G i j)) = incA D (G j i)
    rw [← h]
    rfl
  obtain ⟨co, hco⟩ := GlobalTheory.SquareAgree.exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e
    (X.gram.map (incA D)) (incA D D.host.xi0) hHG hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
    (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _) (by rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (by rw [hs]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co cS hc
  have hform : ∀ w w' : Matrix (Fin S.rank) (Fin d) (AE D), symplO (sgn ε S) X (cS w) (cS w') =
      (M.co.e w).1 ⬝ᵥ (M.co.e w').2 - (M.co.e w').1 ⬝ᵥ (M.co.e w).2 := by
    intro w w'
    rw [← GlobalTheory.WeilSchrodinger.symp_eq_symplO D (sgn ε S) X X.gramᵀ (D.host.xi0 • (sgn ε S).gram⁻¹) 1 rfl
      (one_smul _ _), co.form, hco, hco]

  obtain ⟨hline, -⟩ := GlobalTheory.LineRealAd.lineAt_realAd_smul D θ hθ τ z
  set u₀ := cS.symm (lineAt θ τ z 1) with hu₀
  have hcs : ∀ (a : AF D.host.F) (v : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • v) = a • cS v := by
    intro a v
    rw [hc, hc, ← Matrix.smul_mul]
    rfl
  have hL : ∀ t : ℝ, lineAt θ τ z t = cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) := by
    intro t
    rw [hcs, hu₀, AddEquiv.apply_symm_apply, hline]
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) = ⅟(2 : AF D.host.F) :=
    (invOf_eq_right_inv (by rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num)).symm

  have hkey : ∀ t : ℝ, heisO Bs.ψ (sgn ε S) X (lineAt θ τ z t) f (cS u) =
      GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u
        (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))) := by
    intro t
    set u' := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀
    have e1 : ∀ x, M.co.rho Bs.ψ u (M.co.rho Bs.ψ u' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x =
        Bs.ψ (⅟(2 : AF D.host.F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u').2 - (M.co.e u').1 ⬝ᵥ (M.co.e u).2)) *
          M.co.rho Bs.ψ (u + u') (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) x := by
      intro x
      simp only [GlobalTheory.WeilM.Darboux.rho, map_add (f := _)]
      exact schr_schr_apply Bs.ψ _ _ _ x
    rw [hL t]
    simp only [heisO]
    rw [← map_add (f := _), ← hfΦ (u + u')]
    simp only [GlobalTheory.WeilM.thetaSum, e1, tsum_mul_left]
    rw [symplOH, hform, h2]

  have hd : ∀ x, HasDerivAt
      (fun t : ℝ => M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) x)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ x) 0 :=
    fun x => hact _ (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd) x
  have hder : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F
      (M.co.rho Bs.ψ u (M.co.rho Bs.ψ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))))
      (GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ))) 0 := by
    simp only [GlobalTheory.WeilM.Darboux.rho, map_smul] at hd ⊢
    exact GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr Bs.ψ hF hψc (M.co.e u₀) hΦ h1 hd (M.co.e u)
  show GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ)) =
    Formalism.IndefR.Datum.dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f (cS u)
  have hfun : (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (lineAt θ τ z t) f (cS u)) = fun t : ℝ =>
      GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u
        (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))) := funext hkey
  unfold Formalism.IndefR.Datum.dRho
  rw [hfun]
  exact hder.deriv.symm

end GlobalTheory.HeisLineTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeRealPlacePureDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_realPlace_pureDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f : WO S X → ℂ, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) (g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ (cS.symm (lineAt θ τ z 1))) g g₁ →
          IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  first | exact @GlobalTheory.HeisLineTransfer.isDatum_dRho_heisO | exact GlobalTheory.HeisLineTransfer.isDatum_dRho_heisO | (intros; apply GlobalTheory.HeisLineTransfer.isDatum_dRho_heisO <;> assumption)
end
end
