module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIso
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.CompanionTheory.QL.instMeasGL
attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.FlipMatch

noncomputable section
namespace GlobalTheory.FlipMatch.FieldTransport
open ValuativeRel

section
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {n : Type} [Fintype n] [DecidableEq n]


omit [IsNonarchimedeanLocalField k] [IsNonarchimedeanLocalField k'] in
theorem val_le_iff (hj : IsLocIso j) (x y : k) :
    valuation k' (j x) ≤ valuation k' (j y) ↔ valuation k x ≤ valuation k y := by
  by_cases hy : y = 0
  · subst hy; simp
  have h := hj.2.2 (x / y)
  have h0 : 0 < valuation k y := zero_lt_iff.2 (by simpa using hy)
  have h1 : 0 < valuation k' (j y) := zero_lt_iff.2 (by simpa using hy)
  rwa [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_div₀, map_div₀, map_div₀, div_le_one₀ h0,
    div_le_one₀ h1] at h

theorem isUnif_map (hj : IsLocIso j) {ϖ : kˣ} (h : IsUnif ϖ) : IsUnif (Units.map (j : k →* k') ϖ) := by
  have hlt : ∀ x, valuation k' (j x) < 1 ↔ valuation k x < 1 := fun x => by
    have := (val_le_iff hj 1 x).not
    simpa only [map_one, not_le] using this
  obtain ⟨ϖ', h'⟩ := exists_isUnif (k := k')
  show valuation k' (j ϖ) = uniformizer k'
  refine le_antisymm (le_uniformizer_iff.2 ((hlt _).2 (h ▸ uniformizer_lt_one))) ?_
  obtain ⟨y, hy⟩ := j.surjective ϖ'
  rw [← show valuation k' (ϖ' : k') = uniformizer k' from h', ← hy, val_le_iff hj,
    show valuation k (ϖ : k) = uniformizer k from h, le_uniformizer_iff, ← hlt, hy]
  exact h' ▸ uniformizer_lt_one

theorem shellSet_subset {ϖ ϖ' : kˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ') (m : n → ℤ) :
    shellSet ϖ m ⊆ shellSet ϖ' m := by
  intro g hg
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  have hu : ∀ r : ℤ, valuation k (((ϖ / ϖ') ^ r : kˣ) : k) = 1 := fun r => by
    have h1 : valuation k ((ϖ : k) / ϖ') = 1 := by
      rw [map_div₀, show valuation k (ϖ : k) = _ from h, show valuation k (ϖ' : k) = _ from h']
      exact div_self uniformizer_ne_zero
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_div_eq_div_val, h1, _root_.one_zpow]
  have hd : ∀ c : n → kˣ, (∀ i, valuation k (c i : k) = 1) → ∀ i l, (diagGL c).val i l ∈ 𝒪[k] := fun c hc i l => by
    rw [diagGL_val, diagonal_apply]
    split_ifs
    · exact (hc i).le
    · exact zero_mem _
  have hK : (diagGL fun i => (ϖ / ϖ') ^ m i) ∈ KO k n := (mem_KO_iff _).2 ⟨hd _ fun i => hu _,
    hd (fun i => ((ϖ / ϖ') ^ m i)⁻¹) fun i => by rw [← _root_.zpow_neg]; exact hu _⟩
  refine mem_shellSet.2 ⟨_, mul_mem hx hK, y, hy, ?_⟩
  congr 1
  rw [mul_assoc]
  congr 1
  have := diagHom.map_mul (fun i => (ϖ / ϖ') ^ m i) (fun i => ϖ' ^ m i)
  refine Eq.trans ?_ this
  show SplitFlip.diagGL _ = SplitFlip.diagGL _
  congr 1
  funext i
  simp [← mul_zpow]

def glEquiv (j : k ≃+* k') (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃* GL n k' :=
  Units.mapEquiv (j.mapMatrix (m := n)).toMulEquiv


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] in
theorem glEquiv_val (g : GL n k) : (glEquiv j n g).val = g.val.map j := rfl


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] in
theorem gdet_glEquiv (g : GL n k) : gdet (glEquiv j n g) = Units.map (j : k →* k') (gdet g) :=
  Units.ext ((j : k →+* k').map_det g.val).symm

def glHomeo (hj : IsLocIso j) (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃ₜ* GL n k' :=
  { glEquiv j n with
    continuous_toFun := isEmbedding_val_GL.continuous_iff.2 (Units.continuous_val.matrix_map hj.1)
    continuous_invFun := isEmbedding_val_GL.continuous_iff.2 (Units.continuous_val.matrix_map hj.2.1) }

theorem glEquiv_mem_KO (hj : IsLocIso j) (g : GL n k) : glEquiv j n g ∈ KO k' n ↔ g ∈ KO k n := by
  rw [mem_KO_iff, mem_KO_iff, ← map_inv]
  simp only [glEquiv_val, map_apply, hj.2.2]

theorem preimage_shellSet (hj : IsLocIso j) {ϖ : kˣ} {ϖ' : k'ˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ') (m : n → ℤ) :
    glEquiv j n ⁻¹' shellSet ϖ' m = shellSet ϖ m := by
  rw [(shellSet_subset h' (isUnif_map hj h) m).antisymm (shellSet_subset (isUnif_map hj h) h' m)]
  have hd : glEquiv j n (diagGL fun i => ϖ ^ m i) = diagGL fun i => (Units.map (j : k →* k') ϖ) ^ m i :=
    Units.ext (by rw [glEquiv_val, diagGL_val, diagGL_val, diagonal_map (map_zero _)]; simp)
  ext g
  rw [Set.mem_preimage, mem_shellSet, mem_shellSet, ← hd]
  constructor
  · rintro ⟨x, hx, y, hy, H⟩
    obtain ⟨x, rfl⟩ := (glEquiv j n).surjective x
    obtain ⟨y, rfl⟩ := (glEquiv j n).surjective y
    rw [← map_mul, ← map_mul] at H
    exact ⟨x, (glEquiv_mem_KO hj _).1 hx, y, (glEquiv_mem_KO hj _).1 hy, (glEquiv j n).injective H⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨_, (glEquiv_mem_KO hj _).2 hx, _, (glEquiv_mem_KO hj _).2 hy, by rw [map_mul, map_mul]⟩

theorem apow_map (hj : IsLocIso j) (x : kˣ) (z : ℂ) : apow (Units.map (j : k →* k') x) z = apow x z := by
  have := GlobalTheory.SplitWeil.nabs_map_of_homeomorph j hj.1 hj.2.1 x
  unfold apow
  congr 2

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

def glMeas (hj : IsLocIso j) (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃ᵐ GL n k' :=
  (glHomeo hj n).toHomeomorph.toMeasurableEquiv

theorem isHaar_map (hj : IsLocIso j) (μ : Measure (GL n k)) [μ.IsHaarMeasure] : (μ.map (glMeas hj n)).IsHaarMeasure :=
  (glHomeo hj n).isHaarMeasure_map μ

theorem map_haarVol (hj : IsLocIso j) : (haarVol (KO k n)).map (glMeas hj n) = haarVol (KO k' n) := by
  have := isHaar_map hj (haarVol (KO k n))
  refine eq_haarVol _ isOpen_KO le_rfl ?_
  rw [MeasurableEquiv.map_apply, show glMeas hj n ⁻¹' (KO k' n : Set (GL n k')) = KO k n from
    Set.ext fun g => glEquiv_mem_KO hj g]
  exact haarVol_self isOpen_KO le_rfl

variable {C : Type} [Fintype C] [DecidableEq C] {ν : kˣ →* ℂˣ} {ν' : k'ˣ →* ℂˣ}

theorem shell_map (hj : IsLocIso j) {ϖ : kˣ} {ϖ' : k'ˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ')
    (hν : ∀ x, ν x = ν' (Units.map (j : k →* k') x)) (z : ℂ) (φ : Matrix n n k' → ℂ) (m : n → ℤ) :
    shell (haarVol (KO k n)) ϖ ν z (fun X => φ (X.map j)) m = shell (haarVol (KO k' n)) ϖ' ν' z φ m := by
  unfold shell
  rw [← map_haarVol hj, setIntegral_map_equiv, ← preimage_shellSet hj h h']
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show _ = φ (glEquiv j _ g).val * ν' (gdet (glEquiv j _ g)) * apow (gdet (glEquiv j _ g)) _
  rw [gdet_glEquiv, apow_map hj, ← hν, glEquiv_val]


omit [DecidableEq C] in
theorem bigF_map (hj : IsLocIso j) {a : ℕ} {ϖ : kˣ} {ϖ' : k'ˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ')
    (hν : ∀ x, ν x = ν' (Units.map (j : k →* k') x)) (Ξ : Matrix (Fin a) C k' → ℂ) (X : Matrix (Fin a) C k) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun X => Ξ (X.map j)) X = bigF (haarVol (KO k' (Fin a))) ϖ' ν' Ξ (X.map j) := by
  unfold bigF shellSum
  refine finsum_congr fun m => ?_
  rw [← shell_map hj h h' hν]
  simp only [Matrix.map_mul]


omit [DecidableEq C] in
theorem smallF_map (hj : IsLocIso j) (μ : Measure (GL n k))
    (hν : ∀ x, ν x = ν' (Units.map (j : k →* k') x)) (Ψ : Matrix n C k' → ℂ) (Y : Matrix n C k) :
    smallF μ ν (fun Y => Ψ (Y.map j)) Y = smallF (μ.map (glMeas hj n)) ν' Ψ (Y.map j) := by
  unfold smallF
  rw [integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show _ = Ψ ((glEquiv j _ g).val * Y.map j) * ν' (gdet (glEquiv j _ g)) * apow (gdet (glEquiv j _ g)) _
  rw [gdet_glEquiv, apow_map hj, ← hν, glEquiv_val, ← Matrix.map_mul]

end

theorem zeta_identity_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [MeasurableSpace k'] [BorelSpace k'] (j : k ≃+* k'), IsLocIso j → ∀ (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C] (σ : Fin a ⊕ A' ≃ C)
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ' : Measure (GL A' k')) [μ'.IsHaarMeasure] (ϖ : kˣ) (ϖ' : k'ˣ), IsUnif ϖ → IsUnif ϖ' →
    ∀ (ν β : kˣ →* ℂˣ) (ν' β' : k'ˣ →* ℂˣ), (∀ x, ν x = ν' (Units.map (j : k →* k') x)) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a) C k' → ℂ) (Ψ : Matrix A' C k' → ℂ),
      bigP (haarVol (KO k' (Fin a))) ϖ' σ ν' β' Ξ = smallP μ' σ ν' (ν' * β') Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (X.map j)) = smallP μ σ ν (ν * β) fun Y => lam * Ψ (Y.map j) := by
  intro k _ _ _ _ _ _ k' _ _ _ _ _ _ j hj a A' _ _ C _ _ σ μ _ μ' _ ϖ ϖ' h h' ν β ν' β' hν
  have := isHaar_map hj μ
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map (glMeas hj A')) μ'
  have hc0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map (glMeas hj A')) μ').ne'
  generalize Measure.haarScalarFactor (μ.map (glMeas hj A')) μ' = c at hc hc0
  have hc1 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  refine ⟨((c : ℝ) : ℂ)⁻¹, inv_ne_zero hc1, fun Ξ Ψ H => funext fun g => ?_⟩
  have H1 := congrFun H (glEquiv j C g)
  have hX : (X0 k σ * (invT g).val).map j = X0 k' σ * (invT (glEquiv j C g)).val := by
    ext i l
    rw [map_apply, frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply]; rfl
  have hY : (Y0 k σ * g.val).map j = Y0 k' σ * (glEquiv j C g).val := by
    ext i l
    rw [map_apply, frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply]; rfl
  have hS : smallF μ ν (fun Y => ((c : ℝ) : ℂ)⁻¹ * Ψ (Y.map j)) (Y0 k σ * g.val) =
      smallF μ' ν' Ψ (Y0 k' σ * (glEquiv j C g).val) := by
    rw [smallF_map hj μ hν (fun Y => ((c : ℝ) : ℂ)⁻¹ * Ψ Y), hc, hY]
    simp only [smallF, integral_smul_nnreal_measure, mul_assoc, integral_const_mul, NNReal.smul_def,
      Complex.real_smul]
    rw [inv_mul_cancel_left₀ hc1]
  rw [bigZetaIntegral_eq, smallP, gdet_glEquiv, apow_map hj, apow_map hj, MonoidHom.mul_apply, ← hν, Units.val_mul] at H1
  rw [bigZetaIntegral_eq, smallP, bigF_map hj h h' hν, hS, hX, MonoidHom.mul_apply, Units.val_mul]
  have hb : ((β' (Units.map (j : k →* k') (gdet g)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  apply mul_left_cancel₀ hb
  linear_combination (β (gdet g) : ℂ) * H1

end GlobalTheory.FlipMatch.FieldTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIsoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.CompanionTheory.QL.instMeasGL
attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIdentity_transport_localFieldIso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [MeasurableSpace k'] [BorelSpace k'] (j : k ≃+* k'), IsLocIso j → ∀ (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C] (σ : Fin a ⊕ A' ≃ C)
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ' : Measure (GL A' k')) [μ'.IsHaarMeasure] (ϖ : kˣ) (ϖ' : k'ˣ), IsUnif ϖ → IsUnif ϖ' →
    ∀ (ν β : kˣ →* ℂˣ) (ν' β' : k'ˣ →* ℂˣ), (∀ x, ν x = ν' (Units.map (j : k →* k') x)) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a) C k' → ℂ) (Ψ : Matrix A' C k' → ℂ),
      bigP (haarVol (KO k' (Fin a))) ϖ' σ ν' β' Ξ = smallP μ' σ ν' (ν' * β') Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (X.map j)) = smallP μ σ ν (ν * β) fun Y => lam * Ψ (Y.map j) := by
  first | exact @GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport | exact GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport | (intros; apply GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelFiniteVectorNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelFiniteVectorNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThPVecNe


set_option maxHeartbeats 1000000 in
theorem thPVec_ne_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (B : C.Bas), C.IsB B → ∀ ΛT : Lt D.host.E T.rank, IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsThPVecOf C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f → f ≠ 0 := by
  intro D S T C hn B hB ΛT hΛT βS βT hβS hβT Pg Q ξ f₀ f hf
  obtain ⟨hv, e, he, hth⟩ := hf
  have hS := GlobalTheory.Ker.Base.selfDualC_stdL (S := S) C.m.gS
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hidem : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hce : cA D e * cA D (cA D e) = 0 := by rw [← RingHom.map_mul, he.2, map_zero]
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hf0 : f₀ ≠ 0 := by
    intro h0
    obtain ⟨⟨p, hp⟩, hn1⟩ := hv.2.norm
    have h1 := hn1 p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hSB := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice S _ hS)
    (GlobalTheory.PlaceVec.selfDual_isFullLattice T _ hΛT) hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
    (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) (Pg ∪ Q)
    (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
      rw [GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
        GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)]
  obtain ⟨x, hx1, hx2, hx3⟩ := GlobalTheory.AdjDatumNe.exists_datum_ne_zero D S T βS βT Pg Q (Pg ∪ Q) ξ e hn he
    (fun PP hPP => Finset.mem_union_left _ hPP) (fun PP hPP => Finset.mem_union_right _ hPP)
  rw [hall Tm hTm]
  refine GlobalTheory.PlaceModelInj.placeModel_ne_zero D C.ψ S T (stdL D.host.E S.rank) ΛT (cA D e) f₀ _ Tm hv.1 hS hΛT hidem hce
    hinf hTm hf0 hSB ?_
  intro h0
  have := congrFun h0 x
  simp only [Pi.zero_apply] at this
  rw [if_pos ⟨hx1, hx2⟩] at this
  exact hx3 this

end GlobalTheory.ThPVecNe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelFiniteVectorNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_finite_vector_ne_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (B : C.Bas), C.IsB B → ∀ ΛT : Lt D.host.E T.rank, IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsThPVecOf C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f → f ≠ 0 := by
  first | exact @GlobalTheory.ThPVecNe.thPVec_ne_zero | exact GlobalTheory.ThPVecNe.thPVec_ne_zero | (intros; apply GlobalTheory.ThPVecNe.thPVec_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignatureMatrixExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignatureMatrixExtension
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackFrame

open GlobalTheory.PackLoc

section Lin

variable {m N : ℕ} (e : Option (Fin m) ≃ Fin N)

theorem embOpt_mul (h k : Matrix (Fin m) (Fin m) ℂ) : embOpt e (h * k) = embOpt e h * embOpt e k := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases a <;> cases b <;> simp [embOpt, Matrix.mul_apply]

theorem embOpt_ct (h : Matrix (Fin m) (Fin m) ℂ) : embOpt e hᴴ = (embOpt e h)ᴴ := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt]

theorem embOpt_Jm {εA : Fin m → Bool} {ε : Fin N → Bool} (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = εA i) :
    Formalism.REAL.Jm ε = embOpt e (Formalism.REAL.Jm εA) := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt, Formalism.REAL.Jm, Matrix.diagonal_apply, h0, h1]

theorem embOpt_unit {h : Matrix (Fin m) (Fin m) ℂ} (hh : IsUnit h) : IsUnit (embOpt e h) := by
  obtain ⟨k, hk⟩ := hh.exists_right_inv
  exact IsUnit.of_mul_eq_one (embOpt e k) (by rw [← embOpt_mul, hk, embOpt_one])

theorem embOpt_inv {h : Matrix (Fin m) (Fin m) ℂ} (hh : IsUnit h) : (embOpt e h)⁻¹ = embOpt e h⁻¹ :=
  Matrix.inv_eq_right_inv (by
    rw [← embOpt_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hh), embOpt_one])

theorem Jm_unit (ε : Fin m → Bool) : IsUnit (Formalism.REAL.Jm ε) := by
  refine IsUnit.of_mul_eq_one (Formalism.REAL.Jm ε) ?_
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> simp

def vecOpt (y : Fin m → ℂ) (a : ℂ) : Fin N → ℂ := fun b => (e.symm b).elim a y

theorem embOpt_vec (h : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ) (a : ℂ) :
    embOpt e h *ᵥ vecOpt e y a = vecOpt e (h *ᵥ y) a := by
  funext b
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mulVec, dotProduct, ← e.sum_comp, Fintype.sum_option]
  cases b <;> simp [embOpt, vecOpt, Matrix.mulVec, dotProduct]

theorem eu_vecOpt (y : Fin m → ℂ) (a : ℂ) : eu (vecOpt e y a) ^ 2 = eu y ^ 2 + ‖a‖ ^ 2 := by
  unfold eu
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ← e.sum_comp, Fintype.sum_option, add_comm]
  simp [vecOpt]

theorem vecOpt_zero_one : vecOpt e 0 1 = Pi.single (e none) 1 := by
  funext b
  obtain ⟨b, rfl⟩ := e.surjective b
  cases b <;> simp [vecOpt, Pi.single_apply]

def colM (F : Matrix (Fin N) (Fin m) ℂ) (z : Matrix (Fin N) (Fin 1) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i b => (e.symm b).elim (z i 0) (F i)

variable (F : Matrix (Fin N) (Fin m) ℂ) (z : Matrix (Fin N) (Fin 1) ℂ)

theorem colM_vec (y : Fin m → ℂ) (a : ℂ) : colM e F z *ᵥ vecOpt e y a = F *ᵥ y + a • fun i => z i 0 := by
  funext i
  rw [Matrix.mulVec, dotProduct, ← e.sum_comp, Fintype.sum_option]
  simp [colM, vecOpt, Matrix.mulVec, dotProduct, add_comm, mul_comm]

theorem mul_colM (g : Matrix (Fin N) (Fin N) ℂ) : g * colM e F z = colM e (g * F) (g * z) := by
  ext i b
  obtain ⟨b, rfl⟩ := e.surjective b
  cases b <;> simp [colM, Matrix.mul_apply]

theorem colM_mul (h : Matrix (Fin m) (Fin m) ℂ) : colM e F z * embOpt e h = colM e (F * h) z := by
  ext i b
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases b <;> simp [colM, embOpt, Matrix.mul_apply]

theorem colM_gram (J : Matrix (Fin N) (Fin N) ℂ) (h1 : Fᴴ * J * z = 0) (h2 : zᴴ * J * F = 0) (h3 : zᴴ * J * z = 1) :
    (colM e F z)ᴴ * J * colM e F z = embOpt e (Fᴴ * J * F) := by
  rw [Matrix.mul_assoc] at h1 h2 h3 ⊢
  rw [Matrix.mul_assoc, mul_colM]
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a with
  | none => cases b with
    | none => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h3 0) 0
    | some b => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h2 0) b
  | some a => cases b with
    | none => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h1 a) 0
    | some b => simp [colM, embOpt, Matrix.mul_apply (M := _ᴴ)]

theorem exists_frame (J : Matrix (Fin N) (Fin N) ℂ) (h1 : Fᴴ * J * z = 0) (h2 : zᴴ * J * F = 0) (h3 : zᴴ * J * z = 1)
    (εA : Fin m → Bool) (A : Matrix (Fin m) (Fin m) ℂ) (ε : Fin N → Bool) (hA : IsUnit A)
    (hG : Aᴴ * Formalism.REAL.Jm εA * A = Fᴴ * J * F) (h0 : ε (e none) = true) (hε : ∀ i, ε (e (some i)) = εA i) :
    ∃ B : Matrix (Fin N) (Fin N) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = J ∧
      (∀ (y : Fin m → ℂ) (a : ℂ), eu (B *ᵥ (F *ᵥ y + a • fun i => z i 0)) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
      B *ᵥ (fun i => z i 0) = Pi.single (e none) 1 ∧
      ∀ (g : Matrix (Fin N) (Fin N) ℂ) (h : Matrix (Fin m) (Fin m) ℂ), g * F = F * h → g * z = z →
        B * g * B⁻¹ = embOpt e (A * h * A⁻¹) := by
  set M := colM e F z with hM
  set C := embOpt e A with hC
  have hCu : IsUnit C := embOpt_unit e hA
  have hg : Mᴴ * J * M = Cᴴ * Formalism.REAL.Jm ε * C := by
    rw [hM, colM_gram e F z J h1 h2 h3, ← hG, embOpt_mul, embOpt_mul, embOpt_ct, embOpt_Jm e h0 hε]
  have hMu : IsUnit M := by
    have : IsUnit (Mᴴ * J * M) := by
      rw [hg]; exact (((Matrix.isUnit_conjTranspose _).2 hCu).mul (Jm_unit ε)).mul hCu
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right this)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hMu
  have hMi : IsUnit M⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hMu
  have key : ∀ y a, (C * M⁻¹) *ᵥ (F *ᵥ y + a • fun i => z i 0) = vecOpt e (A *ᵥ y) a := by
    intro y a
    rw [← colM_vec e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hd, embOpt_vec]
  refine ⟨C * M⁻¹, hCu.mul hMi, ?_, fun y a => ?_, ?_, fun g h e1 e2 => ?_⟩
  · calc (C * M⁻¹)ᴴ * Formalism.REAL.Jm ε * (C * M⁻¹) = (M⁻¹)ᴴ * (Cᴴ * Formalism.REAL.Jm ε * C) * M⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (M * M⁻¹)ᴴ * J * (M * M⁻¹) := by
          rw [← hg, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  · rw [key, eu_vecOpt]
  · have := key 0 1
    simpa [vecOpt_zero_one] using this
  · have e3 : g * M = M * embOpt e h := by rw [hM, mul_colM, colM_mul, e1, e2]
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd, embOpt_mul, embOpt_mul, ← embOpt_inv e hA, ← hC]
    calc C * M⁻¹ * g * (M * C⁻¹) = C * (M⁻¹ * (g * M)) * C⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e3, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

end Lin

variable {D : D7}

theorem map_cT_tau (τ : D.what₂.Tau) {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X).map (tauE D τ) = (X.map (tauE D τ))ᴴ := by
  ext a b
  exact GlobalTheory.FockCompare.tauE_star τ _

theorem map_incA_tau {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) :
    (X.map (incA D)).map ((θ τ).comp (infPart D)) = X.map (tauE D τ) := by
  ext a b
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem exists_adapted_frame : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau)
  (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (ε : Fin V.rank → Bool)
  (e : Option (Fin Y.rank) ≃ Fin V.rank),
  IsUnit A → Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ → ε (e none) = true → (∀ i, ε (e (some i)) = εA i) →
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = gramAt D V τ ∧
    (∀ (y : Fin Y.rank → ℂ) (a : ℂ),
      eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
    B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), GlobalTheory.PackLoc.embAt θ d τ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧
    ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), B * GlobalTheory.PackLoc.embAt θ d τ h * B⁻¹ = GlobalTheory.PackLoc.embOpt e (A * h * A⁻¹) := by
  intro D θ hθ Y V d τ εA A ε e hA hG h0 hε
  have h1 := congrArg (fun X => X.map (tauE D τ)) d.perp
  have h2 := congrArg (fun X => X.map (tauE D τ)) (GlobalTheory.UnitaryEmbeddingGroup.perp' d)
  have h3 := congrArg (fun X => X.map (tauE D τ)) d.gram
  have h4 := congrArg (fun X => X.map (tauE D τ)) (GlobalTheory.AutFunCounterexample.gram_pull V Y d.ι d.isom)
  simp only [Matrix.map_mul, map_cT_tau, Matrix.map_zero _ (map_zero _)] at h1 h2 h3 h4
  have h5 : (antiDiagonalSignGramMatrix 1 (1 : D.host.E)).map (tauE D τ) = 1 := by
    ext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; simp [antiDiagonalSignGramMatrix]
  rw [h5] at h3
  obtain ⟨B, b1, b2, b3, b4, b5⟩ := exists_frame e _ _ _ h1 h2 h3 εA A ε hA (hG.trans h4.symm) h0 hε
  refine ⟨B, b1, b2, b3, b4, fun h _ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V _ τ, fun h hh => b5 _ h ?_ ?_⟩
  · have k1 := congrArg (fun X => X.map ((θ τ).comp (infPart D))) ((embRel_iff d (atTau θ Y τ h) _).2 rfl).1
    have k2 := (GlobalTheory.PointAtPlaceHom.atTau_spec hθ Y τ hh).2.1
    simp only [Matrix.map_mul, map_incA_tau hθ] at k1
    rw [GlobalTheory.FockCompare.RealAction.infMat_eq] at k2
    exact k1.trans (congrArg _ k2)
  · have k1 := congrArg (fun X => X.map ((θ τ).comp (infPart D))) (GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_fixes_vectors d (atTau θ Y τ h))
    simp only [Matrix.map_mul, map_incA_tau hθ] at k1
    exact k1

end GlobalTheory.PackFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignatureMatrixExtensionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signature_matrix_extension : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau)
  (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (ε : Fin V.rank → Bool)
  (e : Option (Fin Y.rank) ≃ Fin V.rank),
  IsUnit A → Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ → ε (e none) = true → (∀ i, ε (e (some i)) = εA i) →
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = gramAt D V τ ∧
    (∀ (y : Fin Y.rank → ℂ) (a : ℂ),
      eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
    B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), GlobalTheory.PackLoc.embAt θ d τ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧
    ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), B * GlobalTheory.PackLoc.embAt θ d τ h * B⁻¹ = GlobalTheory.PackLoc.embOpt e (A * h * A⁻¹) := by
  first | exact @GlobalTheory.PackFrame.exists_adapted_frame | exact GlobalTheory.PackFrame.exists_adapted_frame | (intros; apply GlobalTheory.PackFrame.exists_adapted_frame <;> assumption)
end
end
