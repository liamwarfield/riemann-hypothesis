module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellHOfCellSec
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

noncomputable section

section CechSide

variable (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}

def omegaRes (x : Fin (N + 1) → Ω) :
    ∀ I J : Kleiman.Chart x, I.1 ⊆ J.1 → (Ω →ₗ[S] Ω) :=
  fun _ _ _ => LinearMap.id

def CechAugExact {x : Fin (N + 1) → Ω} (G : Kleiman.Chart x → Submodule S Ω) (B : Submodule S Ω) : Prop :=
  (∀ J, B ≤ G J) ∧
  (∀ s ∈ Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => Ω) G 0,
      Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) 0 s = 0 → ∃ b ∈ B, ∀ J, s J = b) ∧
  ∀ p : ℕ, ∀ s ∈ Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => Ω) G (p + 1),
    Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) (p + 1) s = 0 →
      ∃ t ∈ Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => Ω) G p,
        Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p t = s

end CechSide

section CellSide

variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] [Algebra S Ω]

def cellCOf (G : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  Submodule.pi Set.univ fun I => G I.1

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

def cellZOf (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  cellCOf S G n ⊓ LinearMap.ker (cellD S y n)

def cellBOf (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) :
    (n : ℕ) → Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω)
  | 0 => ⊥
  | n + 1 => (cellCOf S G n).map (cellD S y n)

abbrev cellHOf (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) : Type :=
  ↥(cellZOf S y G n) ⧸ (cellBOf S y G n).comap (cellZOf S y G n).subtype

def CellAugExact (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) (A : Submodule S Ω) : Prop :=
  (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → A ≤ G I) ∧
  (∀ s ∈ cellCOf S G 0, cellD S y 0 s = 0 →
    ∃ a ∈ A, ∀ c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, CellMeets y c.1 → s c = a) ∧
  ∀ q : ℕ, ∀ s ∈ cellCOf S G (q + 1), cellD S y (q + 1) s = 0 →
    ∃ t ∈ cellCOf S G q, cellD S y q t = s

variable [DecidableEq K]

def baseCell (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Finset (Fin (N + 1))) (I : ∀ k, Finset (ι k)) :
    ∀ k, Finset (ι k) :=
  Function.update I k₀ (I k₀ ∪ J.map e.symm.toEmbedding)

end CellSide

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def BaseRealises.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ b : ℤ, BundleRealises y k₀ (Kleiman.twistBundle F x b) (b • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def NumModel.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (n : ℕ) (L : Fin n → Kleiman.LineBundle F x) (δ : Fin n → K → ℤ),
        (∀ i, BundleRealises y k₀ (L i) (δ i)) → Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) n →
          Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun i => (L i).toSubSystem) =
            NumbersDVR.intNum F (mIdealOver F y) δ

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeBaseComap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem isMultiProjPrime_baseComap (F : Type) [Field F] {K : Type} [DecidableEq K] {ι : K → Type} (k₀ : K)
    {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {W : Ideal (NumbersDVR.MRing ι F)} (hW : NumbersDVR.IsMultiProjPrime W) :
    NumbersDVR.IsMultiProjPrime (baseComap F k₀ e W) := by
  refine FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (j := fun _ : Unit => k₀)
    (g := fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) (fun _ => rfl)
    (fun _ _ _ => Subsingleton.elim _ _) ?_ ?_ hW
  · rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, EmbeddingLike.apply_eq_iff_eq] at h
    rw [h]
  · rintro ⟨k, i⟩ ⟨⟨⟩, hk⟩
    obtain rfl : k₀ = k := hk
    exact ⟨⟨(), e i⟩, by simp⟩

theorem mIdealOver_le_baseComap (F : Type) [Field F] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {x : Fin (N + 1) → Ω}
    (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) {W : Ideal (NumbersDVR.MRing ι F)}
    (hW : mIdealOver F y ≤ W) : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ baseComap F k₀ e W := by
  subst hx
  intro f hf
  rw [baseComap, Ideal.mem_comap]
  apply hW
  have hcomp : (mConeMapOver F y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := Ω) fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have hf' : mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) f = 0 := hf
  have h1 := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hf', map_zero] at h1
  exact h1

theorem ModelCurves.proof (hdim : ModelCurvesDim.Statement) (hlift : ModelCurvesLift.Statement) :
    ModelCurves.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy d
  refine ⟨fun W hW hyW hd => ⟨isMultiProjPrime_baseComap F k₀ e hW,
    mIdealOver_le_baseComap F y k₀ e hx hyW, ?_⟩, fun P hP hxP hd => ?_⟩
  · rw [hdim F K ι Ω y k₀ N e hy W hW hyW, hd]
  · obtain ⟨W, hW, hyW, rfl⟩ := hlift F K ι Ω y k₀ N e x hx hy P hP hxP
    exact ⟨W, hW, hyW, by rw [← hdim F K ι Ω y k₀ N e hy W hW hyW, hd], rfl⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemClosureOfMemChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Points

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}

theorem chartRingOver_oneBlock (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) (hi : x (c ()) ≠ 0) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c =
      Kleiman.chartRing (S := S) (x := x) (Kleiman.singleChart hi) := by
  have hChart : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x (c ()) =
      Kleiman.chartRing (S := S) (x := x) (Kleiman.singleChart hi) := by
    apply le_antisymm
    · rw [ReciprocityTheory.ChartRestriction.G.Geo.chartRing, Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact ⟨X j, X (c ()), 1, Kleiman.X_mem_monos (Finset.mem_singleton_self _),
        isHomogeneous_X S j, isHomogeneous_X S (c ()), by simp⟩
    · rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
      have hs₀ := Kleiman.eval_ne_zero_of_mem_monos (Kleiman.singleChart hi) hs
      have hsne : s ≠ 0 := fun he => hs₀ (by rw [he, map_zero])
      obtain ⟨e', hse', hden⟩ := TranslateEq.pow_div_mem_chartRingI S x
        (Kleiman.singleChart hi) (c ()) hs
      have he : e = e' := hse.inj_right hse' hsne
      subst e'
      change x (c ()) ^ e / aeval x s ∈
        IndefiniteRowSideFullHecke.Kleiman.chartRingI S x {c ()} at hden
      rw [IndefiniteRowSideFullHecke.Kleiman.chartRingI_singleton] at hden
      have hnum : aeval x f / x (c ()) ^ e ∈
          ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x (c ()) := by
        rw [← Kleiman.aeval_div_of_isHomogeneous hf, ReciprocityTheory.ChartRestriction.G.Geo.chartRing,
          ← MvPolynomial.aeval_range]
        exact ⟨f, rfl⟩
      have hquot : aeval x f / aeval x s =
          (aeval x f / x (c ()) ^ e) * (x (c ()) ^ e / aeval x s) := by
        field_simp
      rw [hquot]
      exact mul_mem hnum hden
  rw [← hChart]
  unfold chartRingOver ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

end Points

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      FieldNumbers.relDim (mIdealOver F (segreJoin y)) = FieldNumbers.relDim (mIdealOver F y)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ (n : ℕ) (μs : Fin n → K → ℤ),
      NumbersDVR.intNum F (mIdealOver F (segreJoin y)) (fun j => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j)) =
        NumbersDVR.intNum F (mIdealOver F y) μs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ n : ℕ, (Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) n ↔
        relDim (mIdealOver F y) = ((n : ℕ) : WithBot (WithTop ℤ)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def PowRealises.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
        ∀ (p : ℕ) (c : ℤ), (Kleiman.twistMul Q.toSubSystem p c).secs =
          secOver F y (p • β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftRelDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
      relDim (segreLift ι F W) = relDim W

theorem SegreLiftRelDim.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftIntNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W → ∀ β : K → ℤ,
      intNum F (segreLift ι F W) ![IndefiniteRowSideFullHecke.Kleiman2.pullDeg β] = intNum F W ![β]

theorem SegreLiftIntNum.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def EulerPoly.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)),
    NumbersDVR.IsMultiHomogIdeal V →
      ∃ (B : ℕ) (χ : MvPolynomial K ℚ),
        (∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F V) m i)) ∧
        (∀ (m : K → ℤ) (i : ℕ), B < i → Subsingleton (cechHc ι (quotPart F V) m i)) ∧
        ∀ m : K → ℤ, ∑ i ∈ Finset.range (B + 1),
          (-1 : ℚ) ^ i * (Module.finrank F (cechHc ι (quotPart F V) m i) : ℚ) =
            eval (fun k => (m k : ℚ)) χ

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PModelGenericPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

namespace ModelGenericPoint

variable {O : Type} [CommRing O] {K : Type} {ι : K → Type} (P : Ideal (NumbersDVR.MRing ι O))

def genPt : (Σ k, ι k) → FractionRing (NumbersDVR.MRing ι O ⧸ P) :=
  fun p => algebraMap (NumbersDVR.MRing ι O ⧸ P) _ (Ideal.Quotient.mk P (X p))

theorem aeval_genPt (g : NumbersDVR.MRing ι O) :
    aeval (genPt P) g = algebraMap (NumbersDVR.MRing ι O ⧸ P)
      (FractionRing (NumbersDVR.MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) := by
  have h : (aeval (genPt P) : NumbersDVR.MRing ι O →ₐ[O] FractionRing (NumbersDVR.MRing ι O ⧸ P)) =
      (IsScalarTower.toAlgHom O (NumbersDVR.MRing ι O ⧸ P)
        (FractionRing (NumbersDVR.MRing ι O ⧸ P))).comp (Ideal.Quotient.mkₐ O P) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [genPt]
  rw [h]
  rfl

theorem aeval_genPt_eq_zero (g : NumbersDVR.MRing ι O) : aeval (genPt P) g = 0 ↔ g ∈ P := by
  rw [aeval_genPt, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

theorem genPt_ne_zero (p : Σ k, ι k) : genPt P p ≠ 0 ↔ (X p : NumbersDVR.MRing ι O) ∉ P := by
  rw [Ne, ← aeval_genPt_eq_zero, aeval_X]

theorem mIdealOver_genPt [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [P.IsPrime]
    (hP : NumbersDVR.IsMultiHomogIdeal P) : mIdealOver O (genPt P) = P := by
  ext f
  constructor
  · intro hf
    have hc : ∀ b : K → ℕ, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f ∈ P := by
      intro b
      rw [← aeval_genPt_eq_zero, ← coeff_mConeMapOver, RingHom.mem_ker.mp hf, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    exact Ideal.sum_mem _ fun b _ => hc b
  · intro hf
    refine RingHom.mem_ker.mpr ?_
    ext m
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    have h := coeff_mConeMapOver (S := O) (genPt P) (⇑m) f
    rw [Finsupp.equivFunOnFinite_symm_coe] at h
    rw [h, aeval_genPt_eq_zero]
    exact hP f hf _

end ModelGenericPoint


end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenPrimeOfEqFinrank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter

noncomputable section

universe u w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_twistSys {n : ℕ} (b : Fin n → ℤ) (l : List (Fin n)) (a : ℤ) :
    l.foldl (fun F i => F.twist (twistSys S x (b i))) (twistSys S x a) =
      twistSys S x (a + (l.map b).sum) := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, twistSys_twist_eq_add, ih, List.map_cons, List.sum_cons, add_assoc]

theorem tensorSub_twistSys {n : ℕ} (b : Fin n → ℤ) (T : Finset (Fin n)) :
    tensorSub (fun i => twistSys S x (b i)) T = twistSys S x (∑ i ∈ T, b i) := by
  classical
  rw [tensorSub, foldl_twist_twistSys, zero_add,
    ← List.sum_toFinset b ((List.nodup_finRange n).filter _)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp

theorem interSum_twistSys (pp : Ideal (Poly S N)) {n : ℕ} (b : Fin n → ℤ) (c : ℕ) :
    interSum pp (fun i => twistSys S x (b i)) c =
      ∑ T : Finset (Fin n), (-1) ^ (n - T.card) * restrLen pp (twistSys S x (∑ i ∈ T, b i + c)) := by
  unfold interSum
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [tensorSub_twistSys, twistSys_twist_eq_add]

end Lemmas

section Differences

variable {K : Type*}

theorem foldr_diffStep_eq {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) (l : List (Fin n))
    (hl : l.Nodup) (m : K → ℤ) :
    (l.map bs).foldr NumbersDVR.diffStep h m =
      ∑ T ∈ l.toFinset.powerset, (-1) ^ T.card * h (m - ∑ i ∈ T, bs i) := by
  classical
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    have ha' : a ∉ l.toFinset := fun h' => ha (List.mem_toFinset.mp h')
    rw [List.map_cons, List.foldr_cons, List.toFinset_cons, Finset.sum_powerset_insert ha']
    change (l.map bs).foldr NumbersDVR.diffStep h m - (l.map bs).foldr NumbersDVR.diffStep h (m - bs a) = _
    rw [ih hl' m, ih hl' (m - bs a), sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have hat : a ∉ t := fun h' => ha' (Finset.mem_powerset.mp ht h')
    rw [Finset.card_insert_of_notMem hat, Finset.sum_insert hat, pow_succ, sub_sub]
    ring

theorem mixedDiff_eq_sum {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    NumbersDVR.mixedDiff bs h m = ∑ T : Finset (Fin n), (-1) ^ T.card * h (m - ∑ i ∈ T, bs i) := by
  classical
  rw [NumbersDVR.mixedDiff, List.ofFn_eq_map, foldr_diffStep_eq bs h _ (List.nodup_finRange n),
    List.toFinset_finRange, Finset.powerset_univ]

end Differences

section Point

variable {k : Type u} [Field k] {K' : Type w} [Field K'] [Algebra k K'] {N : ℕ}

theorem restrLen_primeOf_eq_finrank (y : Fin (N + 1) → K') {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (F : SubSystem k y K') : restrLen (primeOf (S := k) y) F = Module.finrank k F.secs := by
  have hid : ∀ I : Chart y, idealMod (x := y) (primeOf (S := k) y) I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
    rw [(mem_primeOf_of_isHomogeneous y hfe).mp hf, zero_div]
  have hbot : ∀ I : Chart y, (F.twist (idealSys y (primeOf (S := k) y))).sub I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨q, hq, z, _, rfl⟩
    have hq' : q ∈ idealMod (x := y) (primeOf (S := k) y) I := hq
    rw [hid I, Submodule.mem_bot] at hq'
    rw [hq', zero_smul]
  have hsecs : (F.twist (idealSys y (primeOf (S := k) y))).secs = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have h1 := (Submodule.mem_iInf _).mp hz (singleChart hyj)
    rw [Submodule.restrictScalars_mem, hbot] at h1
    exact h1
  unfold restrLen
  rw [hsecs, Submodule.comap_bot, Submodule.ker_subtype,
    (Submodule.quotEquivOfEqBot (⊥ : Submodule k F.secs) rfl).length_eq, Module.length_eq_rank]
  rfl

end Point

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreNef.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ β : K → ℤ,
      (IndefiniteRowSideFullHecke.Kleiman2.IsNef F (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def RayVanish.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ β : K → ℤ, ∀ᶠ c : ℕ in Filter.atTop, ∀ i : ℕ, 1 ≤ i →
      Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) i)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreTwist.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ (β : K → ℤ) (c : ℤ),
      secOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg (Sum.inl ())) =
        secOver S y (β + fun _ => c)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver)

def ModelCechRefine.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (T : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω),
      (∀ J, (T.sub J : Set Ω) = chartSecOver F y k₀ e γ J) →
      ∀ n : ℕ, Nonempty (T.H n ≃ₗ[F] cellH F y γ n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def VeryAmpleModel.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
        (Kleiman.IsVeryAmple Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y β)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def MultiSerre.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)),
    NumbersDVR.IsMultiHomogIdeal V →
      ∀ᶠ m : K → ℤ in Filter.atTop,
        (∀ i : ℕ, 1 ≤ i → Subsingleton (cechHc ι (quotPart F V) m i)) ∧
        (Module.finrank F (cechHc ι (quotPart F V) m 0) : ℤ) = NumbersDVR.hilbFn V m

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def ChartSecGen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ (β : K → ℤ) (n : ℕ) (η : Fin n → Ω),
      (∀ j, η j ∈ secOver S y β) →
      (GeneratesOver S y β η ↔
        ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
          (Submodule.span (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (Set.range η) : Set Ω) =
            chartSecOver S y k₀ e β I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def TensorRealise.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (n : ℕ) (L : Fin n → Kleiman.LineBundle F x) (δ : Fin n → K → ℤ),
        (∀ i, BundleRealises y k₀ (L i) (δ i)) → ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in Filter.atTop,
          ((Kleiman.tensorSub (fun i => (L i).toSubSystem) T).twist (Kleiman.twistSys F x (c : ℤ))).secs =
            secOver F y (∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveLift.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ (pp : Ideal (Kleiman.Poly k N)) (e : ℕ), Kleiman.IsSubvar x pp e →
      ∃ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W ∧
        mIdealOver k (graphVec x s) ≤ W ∧ W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) = pp

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveComap.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W →
      mIdealOver k (graphVec x s) ≤ W → ∀ e : ℕ,
        (relDim W = ((e : ℕ) : WithBot (WithTop ℤ)) ↔
          Kleiman.IsSubvar x (W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b))) e)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def GraphRestrict.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω)
    (K' : Type) [Field K'] [Algebra k K'] (x' : Fin (N + 1) → K') (s' : Fin m → K')
    (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0),
    IsGraphGen Q n s → mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s') →
    (∃ i, x' i ≠ 0) → (∃ j, s' j ≠ 0) →
    ∃ (Q' : Kleiman.LineBundle k x') (r : Ω → K'),
      Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r ∧ IsGraphGen Q' n s'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def DegEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ (pp : Ideal (Kleiman.Poly k N)) (W : Ideal (NumbersDVR.MRing (graphIdx N m) k)),
      Kleiman.IsSubvar x pp 1 → NumbersDVR.IsMultiProjPrime W → mIdealOver k (graphVec x s) ≤ W →
      W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) = pp →
      NumbersDVR.intNum k W ![graphDeg n] = Kleiman.interNum pp ![Q.toSubSystem]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
      IsMultiProjPrime (segreLift ι F W)

theorem SegreLiftPrime.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XNotMemMIdealOver
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

def SectionRatio.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W →
      mIdealOver k (graphVec x s) ≤ W → ∀ j b : Fin m,
        (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W →
        ∃ (d : ℕ) (f g : Kleiman.Poly k N), f.IsHomogeneous d ∧ g.IsHomogeneous d ∧
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g ∉ W ∧
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g * X ⟨Sum.inr (), b⟩ -
            rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f * X ⟨Sum.inr (), j⟩ ∈ W

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
