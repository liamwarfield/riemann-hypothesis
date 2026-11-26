module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTail
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestBis

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ModelPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
    ∀ (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
      (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → mIdealOver F y ≤ mIdealOver F y' →
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfPowRealises
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem ModelMulSecs.of_powRealises (h : PowRealises.Statement) : ModelMulSecs.Statement :=
  fun F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ p j => h F K ι Ω y k₀ N e _ rfl hmod Q β hQ p j

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon IsMGraded quotPart)

def SectionMapInj.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → IsMGraded S ι 𝓜 →
    ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → ∀ x ∈ 𝓜 c,
      (∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, LocalizedModule.mk x (1 : cellMon S I.1) = 0) → x = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def RealiseRestrict.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
      ∀ (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
        IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀ → mIdealOver F y ≤ mIdealOver F y' →
        ∀ hxy : (∀ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) i ≠ 0 → x i ≠ 0),
          ∃ (Q' : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm)) (r : Ω → K'),
            Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r ∧ BundleRealises y' k₀ Q' β

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def ModelChangeVeryAmple.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      (IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y' β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OneMemSecOverZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def ModelChangeGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      ∀ (n : ℕ) (h : Fin n → Ω), (∀ j, h j ∈ secOver F y β) →
        (GeneratesOver F y β h ↔ GeneratesOver F y' β' h)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem ModelNefEq.proof (hNef : NefEq.Statement) (hCh : ModelChangeNef.Statement) :
    ModelNefEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Q
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (Q.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen Q n g := hg
  have hmod' := GraphModel.full F N Ω _ Q n (r + 1) g hx hgen
  have hsec := twist_secs_eq_secOver Q n g hgen
  rw [hNef F N Ω _ Q n (r + 1) g hgen]
  exact (hCh F Ω N K ι y k₀ e (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock (Equiv.refl _) hmod hmod' rfl
    β (graphDeg n) (fun c => (hQ c).symm.trans (hsec c))).symm

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelRowExact.proof (hSub : RowSub.Statement) (hZ : CellZeroConst.Statement)
    (hGlue : RowSecGlue.Statement) (hC : CellContract.Statement) (hL : CellLocGlue.Statement)
    (hAct : RowChartAct.Statement) (hCov : RowLocCover.Statement) : ModelRowExact.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ J
  refine ⟨fun I hne hI => Submodule.span_le.mpr (hSub F K ι Ω y k₀ N e γ J I hne hI), ?_, ?_⟩
  · intro s hs hd
    choose c₀ hc₀ using hM.1

    let cell : (∀ k, ι k) → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 := fun c =>
      ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩
    have hmeet : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → CellMeets y (cell c).1 := by
      intro c hc k i hi
      rw [Finset.mem_singleton.mp hi]
      exact hc k
    refine ⟨s (cell c₀), Submodule.subset_span (hGlue F K ι Ω y k₀ N e γ J _ fun c hc => ?_),
      fun c hc => hZ F K ι Ω y s hd c (cell c₀) hc (hmeet c₀ hc₀)⟩
    rw [← hZ F K ι Ω y s hd (cell c) (cell c₀) (hmeet c hc) (hmeet c₀ hc₀)]
    exact hs (cell c) (Set.mem_univ _)
  · obtain ⟨m, f, u, hf, hu, hsum, hloc⟩ := hCov F K ι Ω y k₀ N e hM γ J
    refine hL F K ι Ω y _ (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J).toSubring m f u hf hu hsum
      (fun I r hr a ha => hAct F K ι Ω y k₀ N e γ J I r a hr ha) fun l => ?_
    obtain ⟨c, hc, h0, hmono, hinv⟩ := hloc l
    exact hC F K ι Ω y _ c hc h0 hmono hinv

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FoldTensorToSubSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

noncomputable section

section Fold

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

def foldTensor {n : ℕ} (L : Fin n → Kleiman.LineBundle S x) (l : List (Fin n)) (Q : Kleiman.LineBundle S x) :
    Kleiman.LineBundle S x :=
  l.foldl (fun P i => P.tensor (L i)) Q

theorem foldTensor_toSubSystem {n : ℕ} (L : Fin n → Kleiman.LineBundle S x) (l : List (Fin n))
    (Q : Kleiman.LineBundle S x) :
    (foldTensor L l Q).toSubSystem = l.foldl (fun P i => P.twist (L i).toSubSystem) Q.toSubSystem := by
  induction l generalizing Q with
  | nil => rfl
  | cons a l ih =>
    rw [foldTensor, List.foldl_cons, List.foldl_cons, ← Kleiman.LineBundle.tensor_toSubSystem]
    exact ih _

end Fold

theorem realises_foldTensor (hT : TensorRealises.Statement)
    {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) {n : ℕ}
    (L : Fin n → Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (δ : Fin n → K → ℤ)
    (hL : ∀ i, BundleRealises y k₀ (L i) (δ i)) (l : List (Fin n)) :
    ∀ (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (β : K → ℤ),
      BundleRealises y k₀ Q β → BundleRealises y k₀ (foldTensor L l Q) (β + (l.map δ).sum) := by
  induction l with
  | nil => intro Q β hQ; simpa [foldTensor] using hQ
  | cons a l ih =>
    intro Q β hQ
    have h := ih (Q.tensor (L a)) (β + δ a) (hT F K ι Ω y k₀ N e hmod Q (L a) β (δ a) hQ (hL a))
    rw [List.map_cons, List.sum_cons, ← add_assoc]
    exact h

theorem TensorRealise.proof (hT : TensorRealises.Statement) : TensorRealise.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n L δ hL T
  subst hx
  refine Filter.Eventually.of_forall fun c => ?_
  have h0 := BaseRealises.proof F K ι Ω y k₀ N e _ rfl hmod 0
  have h := realises_foldTensor hT hmod L δ hL ((List.finRange n).filter (· ∈ T)) _ _ h0 (c : ℤ)
  rw [foldTensor_toSubSystem, Kleiman.twistBundle_toSubSystem] at h
  have hsum : (((List.finRange n).filter (· ∈ T)).map δ).sum = ∑ i ∈ T, δ i := by
    rw [← List.sum_toFinset δ ((List.nodup_finRange n).filter _)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp
  rw [hsum, zero_smul, zero_add] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ProdExp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

section Model

variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem TensorRealises.prod_exp (y : (Σ k, ι k) → Ω) (k₀ : K) (β β' : K → ℤ) (c d : ℤ)
    (cc : ∀ k, ι k) (hc : ∀ k, y ⟨k, cc k⟩ ≠ 0) :
    y ⟨k₀, cc k₀⟩ ^ (-d) * ((∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) *
        ∏ k, y ⟨k, cc k⟩ ^ (-(β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) =
      ∏ k, y ⟨k, cc k⟩ ^ (-(β + β' + (2 * c + d) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
  have h0 : y ⟨k₀, cc k₀⟩ ^ (-d) = ∏ k, y ⟨k, cc k⟩ ^ (-(d • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
    rw [Finset.prod_eq_single k₀]
    · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    · intro k _ hk
      simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Model

theorem TensorRealises.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement) :
    TensorRealises.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod L L' β β' hL hL' ct
  obtain ⟨a₀, ha₀⟩ := Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L
  obtain ⟨a₁, ha₁⟩ := Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L'
  obtain ⟨b₀, hb₀⟩ := hG F K ι Ω y k₀ hmod β
  obtain ⟨b₁, hb₁⟩ := hG F K ι Ω y k₀ hmod β'
  obtain ⟨c, h0, h1, h2, h3⟩ : ∃ c, a₀ ≤ c ∧ a₁ ≤ c ∧ b₀ ≤ c ∧ b₁ ≤ c :=
    ⟨max (max a₀ a₁) (max b₀ b₁), by omega, by omega, by omega, by omega⟩
  have hgL := ha₀ c h0
  have hgL' := ha₁ c h1
  have hgY := hb₀ c h2
  have hgY' := hb₁ c h3
  obtain ⟨d, rfl⟩ : ∃ d, ct = 2 * c + d := ⟨ct - 2 * c, by ring⟩
  have hchart : ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
      ((L.tensor L').toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).sub I =
        Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
            ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) *
              (secOver F y (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) * Kleiman.twistMod F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) d I := by
    intro I
    have e1 : (L.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I =
        Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := by
      rw [← hgL I, hL c]
    have e2 : (L'.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I =
        Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (secOver F y (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := by
      rw [← hgL' I, hL' c]
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub] at e1 e2
    show ((L.toSubSystem.twist L'.toSubSystem).twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).sub I = _
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub, PowRealises.twist_sub, ← Submodule.span_mul_span, ← e1,
      ← e2, two_mul, ← PowRealises.twistMod_mul, ← PowRealises.twistMod_mul]
    ring
  have hsecs : ((L.tensor L').toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).secs =
      ⨅ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm), (Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) *
            (secOver F y (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) *
          Kleiman.twistMod F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) d I).restrictScalars F := by
    simp only [Kleiman.SubSystem.secs, hchart]
  ext s
  rw [hsecs, hS F K ι Ω y k₀ N e _ rfl hmod _ d s, PowRealises.mem_secOver]
  refine forall_congr' fun cc => forall_congr' fun hc => ?_
  have hu : (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hu' : (∏ k, y ⟨k, cc k⟩ ^ (-(β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  rw [← Submodule.span_mul_span, PowRealises.span_secOver_eq y _ hgY cc hc,
    PowRealises.span_secOver_eq y _ hgY' cc hc, Submodule.span_mul_span, Set.singleton_mul_singleton, ← mul_inv,
    PowRealises.mem_span_inv_iff _ (mul_ne_zero hu hu'), mul_assoc, TensorRealises.prod_exp y k₀ β β' c d cc hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperComponentMulX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart CechC)

noncomputable section

section Lemmas

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra


omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in
theorem snapper_component_mul_X [DecidableEq K] (f : MvPolynomial (Σ k, ι k) F) (b : K → ℕ) (v : Σ k, ι k) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (b + NumbersDVR.blockWeight ι v) (f * X v) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f * X v := by
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι)) (a := f) (i := b)
    (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
  have key : ∀ (φ : MvPolynomial (Σ k, ι k) F) (c : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι)) φ c :
        MvPolynomial (Σ k, ι k) F) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) c φ :=
    fun φ c => weightedDecomposition.decompose'_apply F (NumbersDVR.blockWeight ι) φ c
  rw [key, key] at h
  exact h


omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in
theorem snapper_colon_X [DecidableEq K] {J : Ideal (MvPolynomial (Σ k, ι k) F)} (hJ : NumbersDVR.IsMultiHomogIdeal J)
    (v : Σ k, ι k) : NumbersDVR.IsMultiHomogIdeal (J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) := by
  intro f hf b
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul] at hf ⊢
  rw [← snapper_component_mul_X]
  exact hJ _ hf _


omit [Fintype K] [LinearOrder K] in
theorem snapper_eval_shift (p : MvPolynomial K ℚ) (e m : K → ℤ) :
    eval (fun k => ((m - e) k : ℚ)) p =
      eval (fun k => (m k : ℚ)) (bind₁ (fun j => X j - C ((e j : ℤ) : ℚ)) p) := by
  have hb : ∀ (x : K → ℚ) (g : K → MvPolynomial K ℚ), eval x (bind₁ g p) = eval (fun j => eval x (g j)) p :=
    fun x g => eval₂Hom_bind₁ _ _ _ _
  rw [hb]
  refine congrArg (fun x => eval x p) (funext fun j => ?_)
  simp

theorem snapper_top (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) (n : ℕ)
    (hn : ∑ k, (Fintype.card (ι k) - 1) < n) : Subsingleton (cechHc ι (quotPart F V) m n) := by
  have hI : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, False := fun I => by
    have h1 : ∑ k, ((I.1 k).card - 1) ≤ ∑ k, (Fintype.card (ι k) - 1) :=
      Finset.sum_le_sum fun k _ => Nat.sub_le_sub_right (Finset.card_le_univ _) 1
    have := I.2.2
    omega
  have : Subsingleton (CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) :=
    ⟨fun f g => funext fun I => (hI I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

theorem snapper_finite (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (V : Ideal (MvPolynomial (Σ k, ι k) F))
    (hV : NumbersDVR.IsMultiHomogIdeal V) (m : K → ℤ) (i : ℕ) :
    FiniteDimensional F (cechHc ι (quotPart F V) m i) :=
  (hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance
    (HilbertSamuel.QuotPartGraded.proof F K ι V ((NumbersDVR.Objects.isMultiHomogIdeal_iff V).1 hV))).1 m i

end Lemmas

theorem EulerPoly.proof (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (hE : EulerVar.Statement)
    (hD : PolyOfDiffsExact.Statement) : EulerPoly.Statement := by
  intro F _ K _ _ ι _ _ V hV
  have hfin : ∀ J : Ideal (MvPolynomial (Σ k, ι k) F), NumbersDVR.IsMultiHomogIdeal J →
      ∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F J) m i) :=
    fun J hJ => snapper_finite hS J hJ
  have key : ∀ J : Ideal (MvPolynomial (Σ k, ι k) F), NumbersDVR.IsMultiHomogIdeal J →
      ∃ p : MvPolynomial K ℚ, ∀ m, eulerChar F ι J m = eval (fun k => (m k : ℚ)) p := by
    intro J hJ
    refine IsNoetherian.induction (P := fun J : Ideal (MvPolynomial (Σ k, ι k) F) =>
      NumbersDVR.IsMultiHomogIdeal J → ∃ p : MvPolynomial K ℚ, ∀ m, eulerChar F ι J m = eval (fun k => (m k : ℚ)) p)
      (fun J ih hJ => ?_) J hJ
    have hlt2 : ∀ v : Σ k, ι k, (X v : MvPolynomial (Σ k, ι k) F) ∉ J →
        J < J ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)} := fun v hvJ =>
      lt_of_le_of_ne le_sup_left fun h => hvJ (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hSup : ∀ v : Σ k, ι k, NumbersDVR.IsMultiHomogIdeal (J ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) :=
      fun v => FieldNumbers.isMultiHomogIdeal_sup_span hJ (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
    by_cases hA : ∃ v : Σ k, ι k, (X v : MvPolynomial (Σ k, ι k) F) ∉ J ∧
        J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) ≠ J
    · obtain ⟨v, hvJ, hne⟩ := hA
      have hle : J ≤ J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) := fun f hf => by
        rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
        exact Ideal.mul_mem_right _ J hf
      obtain ⟨p1, hp1⟩ := ih _ (lt_of_le_of_ne hle (Ne.symm hne)) (snapper_colon_X hJ v)
      obtain ⟨p2, hp2⟩ := ih _ (hlt2 v hvJ) (hSup v)
      refine ⟨bind₁ (fun j => X j - C (((Pi.single v.1 1 : K → ℤ) j : ℤ) : ℚ)) p1 + p2, fun m => ?_⟩
      rw [hE F K ι J v hJ (hfin J hJ) (hfin _ (snapper_colon_X hJ v)) (hfin _ (hSup v)) m, hp1, hp2, map_add (f := _),
        ← snapper_eval_shift]
    · push Not at hA
      by_cases hB : ∃ k, ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ J
      · obtain ⟨k, hk⟩ := hB
        refine ⟨0, fun m => ?_⟩
        rw [map_zero, eulerChar]
        refine Finset.sum_eq_zero fun i _ => ?_
        have := cechHc_subsingleton_of_block hk m i
        rw [Module.finrank_zero_of_subsingleton]
        simp
      · push Not at hB
        refine hD K (eulerChar F ι J) fun k => ?_
        obtain ⟨i, hi⟩ := hB k
        obtain ⟨q, hq⟩ := ih _ (hlt2 ⟨k, i⟩ hi) (hSup ⟨k, i⟩)
        refine ⟨q, fun m => ?_⟩
        have h := hE F K ι J ⟨k, i⟩ hJ (hfin J hJ) (hfin _ (snapper_colon_X hJ _)) (hfin _ (hSup _)) m
        rw [hA _ hi] at h
        rw [← hq m]
        linarith
  obtain ⟨p, hp⟩ := key V hV
  exact ⟨∑ k, (Fintype.card (ι k) - 1), p, hfin V hV, fun m i hi => snapper_top V m i hi, hp⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

theorem ModelCurveNum.proof (hN : CurveNumModel.Statement) : ModelCurveNum.Statement := by
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs W W' hW hle hrel hW' hle' hrel' hb
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hm β
  have hQ' : BundleRealises y' k₀' Q β' := fun c => (hQ c).trans (hs c)
  have h1 := hN F K ι Ω y k₀ N e _ rfl hm Q β hQ W hW hle hrel
  have h2 := hN F K' ι' Ω y' k₀' N e' _ hx hm' Q β' hQ' W' hW' hle' hrel'
  have hc : W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      W'.comap (rename fun a : Fin (N + 1) => (⟨k₀', e'.symm a⟩ : Σ k, ι' k)) := by
    ext p
    have := SetLike.ext_iff.mp hb (rename (fun a : Fin (N + 1) => (⟨(), a⟩ : Σ _ : Unit, Fin (N + 1))) p)
    simp only [baseComap, Ideal.mem_comap, rename_rename] at this
    exact this
  rw [h1, h2, hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem ModelChangeNef.proof (hC : ModelCurves.Statement) (hN : ModelCurveNum.Statement) :
    ModelChangeNef.Statement := by
  have key : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
      (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
      IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
      ∀ (β : K → ℤ) (β' : K' → ℤ),
        (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
            secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
        IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β → IndefiniteRowSideFullHecke.Kleiman2.IsNef F y' β' := by
    intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs hnef W' hW' hle' hrel'
    obtain ⟨hP, hPle, hPrel⟩ := (hC F K' ι' Ω y' k₀' N e' _ hx hm' 1).1 W' hW' hle' hrel'
    obtain ⟨W, hW, hle, hrel, hWP⟩ := (hC F K ι Ω y k₀ N e _ rfl hm 1).2 _ hP hPle hPrel
    rw [← hN F Ω N K ι y k₀ e K' ι' y' k₀' e' hm hm' hx β β' hs W W' hW hle hrel hW' hle' hrel' hWP]
    exact hnef W hW hle hrel
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs
  exact ⟨key F Ω N K ι y k₀ e K' ι' y' k₀' e' hm hm' hx β β' hs,
    key F Ω N K' ι' y' k₀' e' K ι y k₀ e hm' hm hx.symm β' β fun c => (hs c).symm⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvarAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

theorem exists_ne_zero_of_isSubvar {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {d : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  refine ⟨i, fun h0 => hi ?_⟩
  change MvPolynomial.X i ∈ RingHom.ker (ReciprocityTheory.ChartRestriction.G.Geo.coneMap F x)
  rw [RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]

theorem VeryAmpleNefPlusAmple.equiv (hBun : BundleOfDeg.Statement) (hNef : ModelNefEq.Statement)
    (hVA : ModelVeryAmpleEq.Statement) (hDim : ModelDimEq.Statement) :
    Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement := by
  constructor
  · intro hA d F _ K _ _ ι _ Ω _ _ y k₀ hmod hdim μ hnef t ht
    obtain ⟨i₀, -⟩ := hmod.1 k₀
    have hpos : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
    let e : ι k₀ ≃ Fin (Fintype.card (ι k₀) - 1 + 1) :=
      (Fintype.equivFin _).trans (finCongr (Nat.succ_pred_eq_of_pos hpos).symm)
    obtain ⟨Q, hQ⟩ := hBun F K ι Ω y k₀ _ e hmod μ
    have hs := (hDim F K ι Ω y k₀ _ e hmod d).mpr hdim
    have hn := (hNef F K ι Ω y k₀ _ e hmod μ Q hQ).mpr hnef
    obtain ⟨p, m, hp, hm, hva⟩ := hA F d Ω _ _ Q hs hn t ht
    exact ⟨p, m, hp, hm, (hVA F K ι Ω y k₀ _ e hmod μ Q hQ p m hp).mp hva⟩
  · intro hB k _ d Ω _ _ N x M hs hnef t ht
    have hx := exists_ne_zero_of_isSubvar hs
    obtain ⟨n, hn⟩ := Generated.full.{0, 0} k Ω N x M
    obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
      (M.tensorProd (twistBundle k x n)) (hn n le_rfl)
    have hgen : IsGraphGen M n g := hg
    have hmod := GraphModel.full k N Ω x M n (r + 1) g hx hgen
    have hsec := twist_secs_eq_secOver M n g hgen
    have hdim := (hDim k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod d).mp hs
    have hnef' := (hNef k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod (graphDeg n) M hsec).mp hnef
    obtain ⟨a, m, ha, hm, hva⟩ := hB d k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock hmod hdim
      (graphDeg n) hnef' t ht
    exact ⟨a, m, ha, hm, (hVA k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod (graphDeg n) M hsec a m ha).mpr hva⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
