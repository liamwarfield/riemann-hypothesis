module

public import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsUpperProjectionInverseTranspose
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.UpperProjectionInverseTransposeRightInverse
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ValuationIntegersEqCompletion
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.PfDict
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow
open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BernBridge.Split

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr

def NarrowBernstein : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible

def IndIrredLt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ), (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
    IsSmoothChar α → IsSmoothChar β → a' < a →
    ∀ N : Submodule ℂ (GL (Fin (a + a')) k → ℂ), N ≤ indSp a a' α β → (∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) →
      N = ⊥ ∨ N = indSp a a' α β

theorem indIrredLt_of (NB : NarrowBernstein) : IndIrredLt := by
  intro k _ _ _ _ a a' α β hα hβ sα sβ hlt N hN hr
  by_cases h0 : N = ⊥
  · exact Or.inl h0
  refine Or.inr (le_antisymm hN ?_)
  obtain ⟨F, hFN, hF0⟩ := (Submodule.ne_bot_iff N).1 h0
  have hI : (parInd (two (stdE a a')) (rhoD a a' α β)).IsIrreducible :=
    NB k a a' α β sα sβ hα hβ (Or.inl hlt.ne')
  let S : Subrepresentation (parInd (two (stdE a a')) (rhoD a a' α β)) :=
    ⟨N.comap (toFn a a' α β), fun g f hf => hr g _ hf⟩
  rcases hI.eq_bot_or_eq_top S with e | e
  · obtain ⟨f, rfl⟩ := exists_toFn (hN hFN)
    have hf : f ∈ S.toSubmodule := hFN
    rw [e] at hf
    have hf0 : f = 0 := hf
    exact absurd (by rw [hf0, map_zero]) hF0
  · intro G hG
    obtain ⟨f, rfl⟩ := exists_toFn hG
    have hf : f ∈ S.toSubmodule := by rw [e]; trivial
    exact hf

section Onto
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem onto_of_irredLt (hI : IndIrredLt) {a a' : ℕ} {α β : kˣ →* ℂˣ} (hα : ∀ x, ‖(α x : ℂ)‖ = 1)
    (hβ : ∀ x, ‖(β x : ℂ)‖ = 1) (sα : IsSmoothChar α) (sβ : IsSmoothChar β) (hlt : a' < a)
    {X : Type} [TopologicalSpace X] (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hlin : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁)
    (hin : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ))
    (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) : ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by
  have h0 : p 0 = 0 := by
    have := hlin 0 (SB X).zero_mem 0 (SB X).zero_mem 1
    simpa using this
  let N : Submodule ℂ (GL (Fin (a + a')) k → ℂ) :=
    { carrier := {F | ∃ Φ ∈ SB X, p Φ = F}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩
        exact ⟨Φ + (1 : ℂ) • Φ₁, (SB X).add_mem hΦ ((SB X).smul_mem _ hΦ₁), by rw [hlin _ hΦ _ hΦ₁, one_smul]⟩
      zero_mem' := ⟨0, (SB X).zero_mem, h0⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, rfl⟩
        exact ⟨0 + c • Φ, (SB X).add_mem (SB X).zero_mem ((SB X).smul_mem _ hΦ), by
          rw [hlin _ (SB X).zero_mem _ hΦ, h0, zero_add]⟩ }
  have hle : N ≤ indSp a a' α β := by
    rintro _ ⟨Φ, hΦ, rfl⟩
    exact hin Φ hΦ
  have hst : ∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N := by
    rintro h₁ _ ⟨Φ, hΦ, rfl⟩
    exact heq Φ hΦ h₁
  rcases hI k a a' α β hα hβ sα sβ hlt N hle hst with h | h
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    have hm : p Φ ∈ N := ⟨Φ, hΦ, rfl⟩
    rw [h] at hm
    exact absurd ((Submodule.mem_bot ℂ).1 hm) hne
  · intro F hF
    rw [← h] at hF
    exact hF

end Onto

theorem unrMaps_of_lt (hI : IndIrredLt) : UnrMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν hS hα hβ
  have hν := isUnram_nu hS hα hβ
  have hp1 := p_lin hS hν
  have hp2 := p'_lin hS hν
  have hp3 := p_mem hS hν hβ
  have hp4 := p'_mem hS hν hα
  have hu := p_unit hS hν hβ
  have hu' := p'_unit hS hν hα
  have sα : IsSmoothChar α := isSmoothChar_of_isUnram hα
  have sβ : IsSmoothChar β := isSmoothChar_of_isUnram hβ
  refine ⟨hp1, hp2, hp3, hp4, p_inv hS hν, p'_inv hS hν, fun Φ _ h₁ => p_equiv Φ h₁, fun Ψ _ h₁ => p'_equiv Ψ h₁,
    ?_, ?_, hu, hu'⟩
  · refine onto_of_irredLt hI hS.unitα hS.unitβ sα sβ hS.lt _ hp1 hp3
      (fun Φ hΦ h₁ => ⟨_, omA_mem_SB ν β 1 h₁ hΦ, p_equiv Φ h₁⟩) ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu 1 (one_mem _)] using congrFun h0 1
  · refine onto_of_irredLt hI hS.unitα hS.unitβ sα sβ hS.lt _ hp2 hp4
      (fun Ψ hΨ h₁ => ⟨_, omB_mem_SB ν α 1 h₁ hΨ, p'_equiv Ψ h₁⟩) ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu' 1 (one_mem _)] using congrFun h0 1

section Global

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThK PositivityTheory.ThK.SplitAsm

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance measFv {F : Type} [Field F] [NumberField F] (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFv {F : Type} [Field F] [NumberField F] (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

theorem finSplit_of_lt (hU : UnrMaps) (hI : IndIrredLt) (hIw : IndIwasawa) (hD : Dict) (hAU : ActsUniq) (hC : ChrFacts)
    (hZ : IntEq) : FinSplit := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨hv, ⟨τ⟩⟩
  obtain ⟨hα, hβ, hν, hcond, -, hunr⟩ := hC F E B X a a' v τ hT.chars
  obtain ⟨hαu, hβu⟩ := hunr hv
  have hS : HidaSetting a a' (unifAt v) (chrW X.α τ) (chrW X.β τ) (chrW X.ν τ) :=
    ⟨GlobalTheory.SplitFlip.exists_isUnif.choose_spec, hα, hβ, hν, hT.geo.lt, hT.geo.even, hcond⟩
  obtain ⟨hlin, hlin', hmem, hmem', hinv, hinv', heq, heq', hon, hon', hsph, hsph'⟩ :=
    hU (Fv F v) a a' _ _ _ _ hS hαu hβu
  obtain ⟨b, b', c, ι, ι', gl, gl', hl, hW, hB, -, hvac, hvac', hRg, hRh, hRg', hRh', hhl⟩ :=
    hD F E σ B a a' G X om om' hT v τ
  have hind : ∀ m n : ℕ, (intInd v : Matrix (Fin m) (Fin n) (Fv F v) → ℂ) =
      Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[Fv F v]} 1 := by
    intro m n
    unfold intInd
    congr 1
    ext Y
    simp only [Set.mem_setOf_eq, hZ F v]
  have h1 : ∀ h ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (a + a')), pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) h = 1 :=
    fun h hh => by rw [hind]; exact hsph h hh
  have h1' : ∀ h ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (a + a')), pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) h = 1 :=
    fun h hh => by rw [hind]; exact hsph' h hh
  have hiSB : intInd v ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := by
    rw [← hvac]; exact hW.bij.mapsTo (hT.geo.hM.vac v).1
  have hnz : pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) ≠ 0 := fun h0 => by
    have := h1 1 (one_mem _)
    rw [h0] at this
    exact zero_ne_one this
  obtain ⟨p, p', hp, hp', hon1, hon1', hinv1, hinv1', heq1, hnt, hirr1⟩ := core hAU v G om om' _ _ _ (indSp a a' _ _)
    (pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ)) (pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ))
    (fun Φ h Φ₁ h₁ => hlin Φ h Φ₁ h₁) (fun Φ h Φ₁ h₁ => hlin' Φ h Φ₁ h₁)
    (fun Φ h => hmem Φ h) (fun Φ h => hmem' Φ h) (fun Φ h => hinv Φ h)
    (fun Φ h => hinv' Φ h) (fun Φ h => heq Φ h) (fun Φ h => heq' Φ h)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon y hy; exact ⟨Φ, h, r⟩)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon' y hy; exact ⟨Φ, h, r⟩) ⟨_, hiSB, hnz⟩
    (fun N hN hst => hI (Fv F v) a a' _ _ hα hβ (isSmoothChar_of_isUnram hαu) (isSmoothChar_of_isUnram hβu)
      hT.geo.lt N hN hst) ι ι' hW.bij hB.bij gl gl' hl hRg hRh hRg' hRh' hhl
  refine ⟨oneMaps v _ p p', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneMaps_p]; exact hon1
  · rw [oneMaps_p']; exact hon1'
  · rw [oneMaps_p]; exact hinv1
  · rw [oneMaps_p']; exact hinv1'
  · rw [oneMaps_p, oneMaps_p']; exact heq1
  · exact hnt
  · rw [oneMaps_p]; exact hirr1
  · intro _
    rw [oneMaps_p, oneMaps_p']
    have e1 := hp _ (hT.geo.hM.vac v).1
    have e2 := hp' _ (hT.geo.hM'.vac v).1
    rw [hvac] at e1
    rw [hvac'] at e2
    have hm1 := hmem _ hiSB
    have hm2 : pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) ∈ indSp a a' (chrW X.α τ) (chrW X.β τ) := by
      rw [← e2]; exact (p' (G.M'.vac v)).2
    have hd : pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) -
        pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) = 0 :=
      hIw (Fv F v) a a' _ _ _ (Submodule.sub_mem _ hm1 hm2) fun h hh => by
        simp only [Pi.sub_apply, h1 h hh, h1' h hh, sub_self]
    refine ⟨Subtype.ext ?_, fun h0 => hnz ?_⟩
    · erw [e1, e2]; exact sub_eq_zero.1 hd
    · have := congrArg Subtype.val h0
      erw [e1] at this
      exact this
  · intro _ hvT; exact absurd hvT hv

theorem finSplit_of_narrow : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) → PositivityTheory.ThK.FinSplit :=
  fun NB => finSplit_of_lt (unrMaps_of_lt (indIrredLt_of NB)) (indIrredLt_of NB) induced_vanish_of_vanish_on_integral split_place_dictionary
    PositivityTheory.KCo.action_uniqueness split_character_facts valuation_integers_eq_completion

end Global

end GlobalTheory.CompanionTheory.BernBridge.Split
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleHermitian
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleHermitian
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.Rg.Base1
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BaseHasse

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem invol (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hCM.2.2.2, hCM.2.2.2]; simp)

theorem exists_pure (hCM : IsCMExt F E σ) : ∃ e : E, e ≠ 0 ∧ σ e = -e := by
  by_contra hcon
  push_neg at hcon
  have hfix : ∀ x : E, σ x = x := fun x => by
    by_contra hx
    refine hcon (x - σ x) (sub_ne_zero.2 (Ne.symm hx)) ?_
    rw [map_sub, invol hCM]
    ring
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := by
    ext x
    have h := hCM.2.2.2 τ x
    rw [hfix] at h
    simpa using h.symm
  haveI : IsTotallyComplex E := hCM.2.1
  have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hreal)

theorem coord_E (hCM : IsCMExt F E σ) {e : E} (he : e ≠ 0) (hσ : σ e = -e) (z : E) :
    ∃ c d : F, z = algebraMap F E c + algebraMap F E d * e := by
  obtain ⟨c, hc⟩ := GoodMass.fixed_mem hCM ((z + σ z) / 2) (by
    rw [map_div₀, map_add (f := _), invol hCM, map_ofNat]
    ring)
  obtain ⟨d, hd⟩ := GoodMass.fixed_mem hCM ((z - σ z) / (2 * e)) (by
    rw [map_div₀, map_sub, invol hCM, map_mul, map_ofNat, hσ]
    field_simp
    ring)
  refine ⟨c, d, ?_⟩
  rw [hc, hd]
  field_simp
  ring

variable (R : Type) [CommRing R] [Algebra F R]

theorem coord_R (hCM : IsCMExt F E σ) {e : E} (he : e ≠ 0) (hσ : σ e = -e) (y : R ⊗[F] E) :
    ∃ a b : R, y = a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] e := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r z =>
    obtain ⟨c, d, rfl⟩ := coord_E hCM he hσ z
    refine ⟨algebraMap F R c * r, algebraMap F R d * r, ?_⟩
    have key : ∀ (c : F) (w : E), r ⊗ₜ[F] (algebraMap F E c * w) = (algebraMap F R c * r) ⊗ₜ[F] w := by
      intro c w
      rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [TensorProduct.tmul_add, ← key, ← key, mul_one]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩

theorem tmul_one_injective {r s : R} (h : r ⊗ₜ[F] (1 : E) = s ⊗ₜ[F] (1 : E)) : r = s :=
  Algebra.TensorProduct.includeLeft_injective (S := F) (R := F) (A := R) (B := E)
    (FaithfulSMul.algebraMap_injective F E) h

theorem local_form (hCM : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} {j : F} (hj : J 0 0 = algebraMap F E j)
    (hj0 : j ≠ 0) {e : E} (he : e ≠ 0) (hσ : σ e = -e) {δ : F} (hδ : e * e = algebraMap F E δ) (β : F)
    (Y : Fin 1 → Fin 1 → R ⊗[F] E) (hY : gramR R σ J Y = (hermScal R σ (algebraMap F R β)).1) :
    ∃ a b : R, algebraMap F R (β / j) = a ^ 2 - algebraMap F R δ * b ^ 2 := by
  obtain ⟨a, b, hab⟩ := coord_R R hCM he hσ (Y 0 0)
  refine ⟨a, b, ?_⟩
  have h00 : hR R σ J (Y 0) (Y 0) = algebraMap F R β ⊗ₜ[F] (1 : E) := congrFun (congrFun hY 0) 0
  have hsig : sigR R σ (Y 0 0) = a ⊗ₜ[F] (1 : E) - b ⊗ₜ[F] e := by
    rw [hab, map_add (f := _)]
    simp [sigR, hσ, TensorProduct.tmul_neg, sub_eq_add_neg]
  have hJ : inclR R (J 0 0) = algebraMap F R j ⊗ₜ[F] (1 : E) := by
    rw [hj]
    simp [inclR, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hee : (b ⊗ₜ[F] e) * (b ⊗ₜ[F] e) = (algebraMap F R δ * b ^ 2) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hδ, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_mul_assoc, one_mul, sq]
  have hn : sigR R σ (Y 0 0) * Y 0 0 = (a ^ 2 - algebraMap F R δ * b ^ 2) ⊗ₜ[F] (1 : E) := by
    rw [hsig, hab, TensorProduct.sub_tmul, ← hee, sq, ← mul_one (1 : E), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    ring
  have h1 : (algebraMap F R j * (a ^ 2 - algebraMap F R δ * b ^ 2)) ⊗ₜ[F] (1 : E) = algebraMap F R β ⊗ₜ[F] (1 : E) := by
    rw [← h00]
    simp only [hR, hform, JR, Fin.sum_univ_one, Matrix.map_apply, hJ]
    rw [mul_comm (sigR R σ (Y 0 0)), mul_assoc, hn, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h2 := tmul_one_injective (F := F) (E := E) R h1
  have hu : algebraMap F R j * algebraMap F R j⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hj0, map_one]
  rw [div_eq_mul_inv, map_mul, ← h2]
  linear_combination (a ^ 2 - algebraMap F R δ * b ^ 2) * hu

end

section

variable {F : Type} [Field F] [NumberField F]

theorem exists_real_hom (τ : F →+* ℝ) : ∃ ψ : Ainf F →+* ℝ, ∀ x, ψ (algebraMap F (Ainf F) x) = τ x := by
  let φ : F →+* ℂ := Complex.ofRealHom.comp τ
  have hφ : ComplexEmbedding.IsReal φ := by
    ext x
    simp [φ, ComplexEmbedding.conjugate]
  let v : InfinitePlace F := InfinitePlace.mk φ
  have hv : v.IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).comp
    (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v), fun x => ?_⟩
  have h1 : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).comp
      (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v) (algebraMap F (Ainf F) x) =
        InfinitePlace.embedding_of_isReal hv x :=
    by
      simpa only [RingHom.comp_apply, Pi.evalRingHom_apply,
        NumberField.InfiniteAdeleRing.algebraMap_apply,
        InfinitePlace.Completion.algebraMap_apply, RingEquiv.apply_symm_apply,
        WithAbs.equiv_symm_apply, WithAbs.equiv_apply, WithAbs.ofAbs_toAbs] using
        InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm x)
  refine h1.trans ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  rfl

end

theorem hasse : Hasse := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ _ _ _ _ hmi hm β hβ hinf hfin
  obtain ⟨j, hj⟩ := GoodMass.fixed_mem hCM _ (hJ.1 0 0)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hJ.2 (by rw [Matrix.det_fin_one, ← hj, map_zero])
  obtain ⟨e, he, hσ⟩ := exists_pure hCM
  obtain ⟨δ, hδ⟩ := GoodMass.fixed_mem hCM (e * e) (by rw [map_mul, hσ]; ring)
  have hδ' : e * e = algebraMap F E δ := hδ.symm
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact mul_ne_zero he he (by rw [hδ', map_zero])
  have hfib : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
      (μ' : Measure (Fin 1 → Fin 1 → R ⊗[F] E)) (ν : Measure (HermR R σ 1))
      (m' : HermR R σ 1 → Measure (Fin 1 → Fin 1 → R ⊗[F] E)), IsGramFib R σ J 1 μ' ν m' →
      m' (hermScal R σ (algebraMap F R β)) ≠ 0 →
      ∃ a b : R, algebraMap F R (β / j) = a ^ 2 - algebraMap F R δ * b ^ 2 := by
    intro R _ _ _ μ' ν m' hG hne
    by_contra hcon
    have hempty : (gramR R σ J ⁻¹' {(hermScal R σ (algebraMap F R β)).1} ∩
        {X | IsUnit (gramR R σ J X).det}) = ∅ := by
      ext Y
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro hY _
      exact hcon (local_form R hCM hj.symm hj0 he hσ hδ' β Y hY)
    apply hne
    have h1 := hG.1 (hermScal R σ (algebraMap F R β))
    rw [hempty, Set.compl_empty] at h1
    exact Measure.measure_univ_eq_zero.1 h1
  obtain ⟨a, c, hac⟩ := GlobalTheory.QNorm.hasseNormSt F δ (β / j) hδ0 (div_ne_zero hβ hj0)
    (fun τ => by
      obtain ⟨ψ, hψ⟩ := exists_real_hom τ
      obtain ⟨a, c, h⟩ := hfib (Ainf F) _ _ mi hmi hinf
      refine ⟨ψ a, ψ c, ?_⟩
      have := congrArg ψ h
      simpa [hψ] using this)
    (fun v => hfib (Fv F v) _ _ (m v) (hm v) (hfin v))
  refine ⟨fun _ _ => algebraMap F E a + algebraMap F E c * e, ?_⟩
  funext p q
  have hp : p = 0 := Subsingleton.elim _ _
  have hq : q = 0 := Subsingleton.elim _ _
  subst hp hq
  have hb : β = j * (a ^ 2 - δ * c ^ 2) := by
    rw [← hac]
    field_simp
  simp only [gramE, hE, hform, Fin.sum_univ_one, ← hj, RingHom.coe_coe, map_add (f := _), map_mul, hσ, AlgHom.commutes]
  rw [hb, map_mul, map_sub, map_mul, map_pow, map_pow, ← hδ']
  ring

end GlobalTheory.CompanionTheory.SW.BaseHasse
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleHermitianStatement
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasse_principle_hermitian : Hasse := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseHasse.hasse | exact GlobalTheory.CompanionTheory.SW.BaseHasse.hasse | (intros; apply GlobalTheory.CompanionTheory.SW.BaseHasse.hasse <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTranslationPreserved
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTranslationPreserved
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.Transport

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul)
open GlobalTheory.CompanionTheory.ThTw (block_mul₂ bl_add mat_nzx_sh block_matrix_injective adj_sub')
open GlobalTheory.CompanionTheory.PcB (mat_mul' rational_map_block_matrix rat_one' rat_zero' rat_neg')
open GlobalTheory.CompanionTheory.FourierN (mat_injective)

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem adelicConjTranspose_blockMatrixTwoByTwoFin {k : ℕ} (a b c d : Mx D k k) :
    adj (blk4 a b c d) = blk4 (adj a) (adj c) (adj b) (adj d) := by
  simp only [adj, blk4]
  rw [← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem block_matrix_diagonal_one_eq_one {k : ℕ} : blk4 (1 : Mx D k k) 0 0 1 = 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem jr_eq {k : ℕ} : JR (AF D.host.F) (Jst D k) = (blk4 0 1 (-1) 0 : Mx D (k + k) (k + k)) := by
  show rat (blk4 0 1 (-1) 0) = _
  rw [rational_map_block_matrix, rat_one', rat_zero', rat_neg', rat_one']

theorem rel_left {k : ℕ} (g : G D k) {a b c d : Mx D k k} (h : mat g = blk4 a b c d) :
    adj d ⬝ a - adj b ⬝ c = 1 ∧ adj a ⬝ c = adj c ⬝ a ∧ adj b ⬝ d = adj d ⬝ b ∧ adj a ⬝ d - adj c ⬝ b = 1 := by
  have h2 : adj (mat g) * JR (AF D.host.F) (Jst D k) * mat g = JR (AF D.host.F) (Jst D k) := g.2
  rw [jr_eq, h, adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h2
  obtain ⟨e1, e2, e3, e4⟩ := block_matrix_injective h2
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, add_zero, zero_add, Matrix.neg_mul] at e1 e2 e3 e4
  refine ⟨?_, (neg_add_eq_zero.1 e1).symm, (neg_add_eq_zero.1 e4).symm, ?_⟩
  · have : adj d ⬝ a - adj b ⬝ c = -(-(adj d ⬝ a) + adj b ⬝ c) := by abel
    rw [this, e3, neg_neg]
  · rw [sub_eq_neg_add, e2]

theorem rel_right {k : ℕ} (g : G D k) {a b c d : Mx D k k} (h : mat g = blk4 a b c d) :
    a ⬝ adj d - b ⬝ adj c = 1 ∧ c ⬝ adj d = d ⬝ adj c ∧ b ⬝ adj a = a ⬝ adj b ∧ d ⬝ adj a - c ⬝ adj b = 1 := by
  obtain ⟨l1, l2, l3, l4⟩ := rel_left g h
  have hL : (blk4 (adj d) (-adj b) (-adj c) (adj a) : Mx D (k + k) (k + k)) * blk4 a b c d = 1 := by
    rw [submatrix_fromBlocks_mul, ← block_matrix_diagonal_one_eq_one]
    congr 1
    · rw [Matrix.neg_mul, ← sub_eq_add_neg, l1]
    · rw [Matrix.neg_mul, ← sub_eq_add_neg, l3, sub_self]
    · rw [Matrix.neg_mul, l2, neg_add_cancel]
    · rw [Matrix.neg_mul, ← sub_eq_neg_add, l4]
  have hR := mul_eq_one_comm.1 hL
  rw [submatrix_fromBlocks_mul, ← block_matrix_diagonal_one_eq_one] at hR
  obtain ⟨e1, e2, e3, e4⟩ := block_matrix_injective hR
  simp only [Matrix.mul_neg] at e1 e2 e3 e4
  refine ⟨by rw [sub_eq_add_neg, e1], sub_eq_zero.1 (by rw [sub_eq_add_neg, e3]),
    (neg_add_eq_zero.1 e2).symm, by rw [sub_eq_neg_add, e4]⟩

theorem exists_rat_blocks {k : ℕ} (γ : G D k) (h : γ ∈ GF D k) :
    ∃ a b c d : Matrix (Fin k) (Fin k) D.host.E, mat γ = blk4 (rat a) (rat b) (rat c) (rat d) := by
  obtain ⟨x, -, hxe⟩ := h
  have hm : mat γ = rat x.1 := (congrArg Units.val hxe).symm
  refine ⟨(x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁,
    (x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [hm, ← rational_map_block_matrix]
  congr 1
  simp only [blk4, Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

theorem comb_sub (a b : Mx D ρ p) (P Q R S U V : Mx D p p) :
    (a ⬝ P - b ⬝ Q) ⬝ R + (b ⬝ S - a ⬝ U) ⬝ V = a ⬝ (P ⬝ R - U ⬝ V) + b ⬝ (S ⬝ V - Q ⬝ R) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

theorem comb_add (a b : Mx D ρ p) (P Q R S U V : Mx D p p) :
    (a ⬝ P + b ⬝ Q) ⬝ R - (a ⬝ S + b ⬝ U) ⬝ V = a ⬝ (P ⬝ R - S ⬝ V) + b ⬝ (Q ⬝ R - U ⬝ V) := by
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

theorem cont_rmul (c : Mx D p p) : Continuous fun v : Mx D ρ p => v ⬝ c :=
  continuous_id.matrix_mul continuous_const

theorem cont_sub {X : Type*} [TopologicalSpace X] {f g : X → Mx D ρ p} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun v => f v - g v := by
  have h₁ : IsTopologicalRing (AE D) := inferInstance
  have h₂ : IsTopologicalAddGroup (AE D) := inferInstance
  have h₃ : ContinuousSub (AE D) := IsTopologicalAddGroup.to_continuousSub
  exact continuous_matrix fun i j => (hf.matrix_elem i j).sub (hg.matrix_elem i j)

theorem cont_add {X : Type*} [TopologicalSpace X] {f g : X → Mx D ρ p} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun v => f v + g v :=
  continuous_matrix fun i j => (hf.matrix_elem i j).add (hg.matrix_elem i j)

def tEquiv (a b c d : Mx D p p)
    (l1 : adj d ⬝ a - adj b ⬝ c = 1) (l2 : adj a ⬝ c = adj c ⬝ a) (l3 : adj b ⬝ d = adj d ⬝ b)
    (l4 : adj a ⬝ d - adj c ⬝ b = 1)
    (r1 : a ⬝ adj d - b ⬝ adj c = 1) (r2 : c ⬝ adj d = d ⬝ adj c) (r3 : b ⬝ adj a = a ⬝ adj b)
    (r4 : d ⬝ adj a - c ⬝ adj b = 1) :
    (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p) where
  toFun v := (v.1 ⬝ adj d - v.2 ⬝ adj c, v.2 ⬝ adj a - v.1 ⬝ adj b)
  invFun v := (v.1 ⬝ a + v.2 ⬝ c, v.1 ⬝ b + v.2 ⬝ d)
  left_inv v := by
    refine Prod.ext ?_ ?_
    · show (v.1 ⬝ adj d - v.2 ⬝ adj c) ⬝ a + (v.2 ⬝ adj a - v.1 ⬝ adj b) ⬝ c = v.1
      rw [comb_sub, l1, l2, sub_self, Matrix.mul_one, Matrix.mul_zero, add_zero]
    · show (v.1 ⬝ adj d - v.2 ⬝ adj c) ⬝ b + (v.2 ⬝ adj a - v.1 ⬝ adj b) ⬝ d = v.2
      rw [comb_sub, l4, l3, sub_self, Matrix.mul_one, Matrix.mul_zero, zero_add]
  right_inv v := by
    refine Prod.ext ?_ ?_
    · show (v.1 ⬝ a + v.2 ⬝ c) ⬝ adj d - (v.1 ⬝ b + v.2 ⬝ d) ⬝ adj c = v.1
      rw [comb_add, r1, r2, sub_self, Matrix.mul_one, Matrix.mul_zero, add_zero]
    · show (v.1 ⬝ b + v.2 ⬝ d) ⬝ adj a - (v.1 ⬝ a + v.2 ⬝ c) ⬝ adj b = v.2
      rw [comb_add, r3, r4, sub_self, Matrix.mul_one, Matrix.mul_zero, zero_add]
  map_add' u v := by
    refine Prod.ext ?_ ?_
    · show (u.1 + v.1) ⬝ adj d - (u.2 + v.2) ⬝ adj c = (u.1 ⬝ adj d - u.2 ⬝ adj c) + (v.1 ⬝ adj d - v.2 ⬝ adj c)
      simp only [Matrix.add_mul]
      abel
    · show (u.2 + v.2) ⬝ adj a - (u.1 + v.1) ⬝ adj b = (u.2 ⬝ adj a - u.1 ⬝ adj b) + (v.2 ⬝ adj a - v.1 ⬝ adj b)
      simp only [Matrix.add_mul]
      abel
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact cont_sub ((cont_rmul _).comp continuous_fst) ((cont_rmul _).comp continuous_snd)
    · exact cont_sub ((cont_rmul _).comp continuous_snd) ((cont_rmul _).comp continuous_fst)
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_
    · exact cont_add ((cont_rmul _).comp continuous_fst) ((cont_rmul _).comp continuous_snd)
    · exact cont_add ((cont_rmul _).comp continuous_fst) ((cont_rmul _).comp continuous_snd)


set_option maxHeartbeats 1000000 in
theorem emb_conj (M : Maps D hn) (g : G D p) {a b c d : Mx D p p} (hg : mat g = blk4 a b c d)
    (z' : hermA D ρ) (x y x' y' : Mx D ρ p)
    (h1 : y' ⬝ a + x' ⬝ c = y) (h2 : y' ⬝ b + x' ⬝ d = x)
    (h3 : adj x' = a ⬝ adj x - b ⬝ adj y) (h4 : adj y' = d ⬝ adj y - c ⬝ adj x)
    (h5 : z'.1 - x' ⬝ (d ⬝ adj y - c ⬝ adj x) = -(x ⬝ adj y)) :
    M.emb g * (M.nzx 0 x * M.sh y) = M.nzx z' x' * M.sh y' * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, bl_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero, h1, h2, h3, h4, h5, neg_sub, AddSubgroup.coe_zero, zero_sub,
    sub_eq_add_neg (a ⬝ adj x), sub_eq_add_neg (c ⬝ adj x)]

def zTv (a b c d : Mx D p p) (x y : Mx D ρ p) : Mx D ρ ρ :=
  x ⬝ ((adj c ⬝ b) ⬝ adj y) + y ⬝ ((adj b ⬝ c) ⬝ adj x) - x ⬝ ((adj a ⬝ c) ⬝ adj x) - y ⬝ ((adj b ⬝ d) ⬝ adj y)

theorem zTv_herm {a b c d : Mx D p p} (l2 : adj a ⬝ c = adj c ⬝ a) (l3 : adj b ⬝ d = adj d ⬝ b) (x y : Mx D ρ p) :
    adj (zTv a b c d x y) = zTv a b c d x y := by
  simp only [zTv, adj_sub', adj_add, adj_mul, adj_adj, ← l2, ← l3]
  simp only [Matrix.mul_assoc]
  abel

theorem zTv_eq {a b c d : Mx D p p} (l4 : adj a ⬝ d - adj c ⬝ b = 1) (x y : Mx D ρ p) :
    zTv a b c d x y - (x ⬝ adj a - y ⬝ adj b) ⬝ (d ⬝ adj y - c ⬝ adj x) = -(x ⬝ adj y) := by
  have e : ∀ w : Mx D p ρ, adj a ⬝ (d ⬝ w) = w + adj c ⬝ (b ⬝ w) := fun w => by
    rw [← Matrix.mul_assoc, sub_eq_iff_eq_add.1 l4, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
  simp only [zTv, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, e, Matrix.mul_add]
  abel

theorem rational_map_sub {k l : ℕ} (u v : Matrix (Fin k) (Fin l) D.host.E) : rat (D := D) (u - v) = rat u - rat v := by
  ext i j
  exact map_sub (incA D) _ _

theorem rational_map_add {k l : ℕ} (u v : Matrix (Fin k) (Fin l) D.host.E) : rat (D := D) (u + v) = rat u + rat v := by
  ext i j
  exact map_add (incA D) _ _

theorem transport {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (γ : G D p) (hγ : γ ∈ GF D p) :
    ∃ T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p),
      (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E,
        T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧
      (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E,
        T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧
      ∀ y x : Mx D ρ p, ∃ z' : hermA D ρ,
        M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ := by
  obtain ⟨a, b, c, d, hm⟩ := exists_rat_blocks γ hγ
  obtain ⟨l1, l2, l3, l4⟩ := rel_left γ hm
  obtain ⟨r1, r2, r3, r4⟩ := rel_right γ hm
  refine ⟨tEquiv (ρ := ρ) _ _ _ _ l1 l2 l3 l4 r1 r2 r3 r4, ?_, ?_, ?_⟩
  · intro ξ₁ ξ₂
    refine ⟨ξ₁ * dᴴ - ξ₂ * cᴴ, ξ₂ * aᴴ - ξ₁ * bᴴ, ?_⟩
    show (rat ξ₁ ⬝ adj (rat d) - rat ξ₂ ⬝ adj (rat c), rat ξ₂ ⬝ adj (rat a) - rat ξ₁ ⬝ adj (rat b)) =
      (rat (ξ₁ * dᴴ - ξ₂ * cᴴ), rat (ξ₂ * aᴴ - ξ₁ * bᴴ))
    simp only [rational_map_sub, rat_mul, rat_conjTranspose]
  · intro ξ₁ ξ₂
    refine ⟨ξ₁ * a + ξ₂ * c, ξ₁ * b + ξ₂ * d, ?_⟩
    show (rat ξ₁ ⬝ rat a + rat ξ₂ ⬝ rat c, rat ξ₁ ⬝ rat b + rat ξ₂ ⬝ rat d) =
      (rat (ξ₁ * a + ξ₂ * c), rat (ξ₁ * b + ξ₂ * d))
    simp only [rational_map_add, rat_mul]
  · intro y x
    refine ⟨⟨zTv (rat a) (rat b) (rat c) (rat d) x y, zTv_herm l2 l3 x y⟩, ?_⟩
    refine emb_conj M γ hm _ x y _ _ ?_ ?_ ?_ ?_ (zTv_eq l4 x y)
    · show (y ⬝ adj (rat d) - x ⬝ adj (rat c)) ⬝ rat a + (x ⬝ adj (rat a) - y ⬝ adj (rat b)) ⬝ rat c = y
      rw [comb_sub, l1, l2, sub_self, Matrix.mul_one, Matrix.mul_zero, add_zero]
    · show (y ⬝ adj (rat d) - x ⬝ adj (rat c)) ⬝ rat b + (x ⬝ adj (rat a) - y ⬝ adj (rat b)) ⬝ rat d = x
      rw [comb_sub, l4, l3, sub_self, Matrix.mul_one, Matrix.mul_zero, zero_add]
    · show adj (x ⬝ adj (rat a) - y ⬝ adj (rat b)) = _
      rw [adj_sub', adj_mul, adj_mul, adj_adj, adj_adj]
    · show adj (y ⬝ adj (rat d) - x ⬝ adj (rat c)) = _
      rw [adj_sub', adj_mul, adj_mul, adj_adj, adj_adj]

end GlobalTheory.CompanionTheory.FJE.Transport
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTranslationPreservedStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_translation_preserved : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (γ : G D p), γ ∈ GF D p → ∃ T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p), (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧ (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧ ∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Transport.transport | exact GlobalTheory.CompanionTheory.FJE.Transport.transport | (intros; apply GlobalTheory.CompanionTheory.FJE.Transport.transport <;> assumption)
end
end
