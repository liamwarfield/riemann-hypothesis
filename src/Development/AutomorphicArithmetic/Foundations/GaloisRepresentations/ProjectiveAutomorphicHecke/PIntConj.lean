module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.GrowPHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbLem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.AllLeavesMono
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjOfNotMem
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.NoAccum
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

attribute [local instance] borelH

def IsCuspD {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (V : Submodule ℂ (Sm E N)) : Prop :=
  IsDiscrete V ∧ ∀ φ ∈ V, ∀ r, 0 < r → r < N → Exp r φ.1 = ∅

def LimAt (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (W₁ : Submodule ℂ (Kinf E a → ℂ))
    (W₂ : Submodule ℂ (Kinf E b → ℂ)) (Ω₁ Ω₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ (D : Dom E a b) (ι : Type) [Fintype ι] (M : ℕ)
  (m₁ : ℕ → (E →+* ℂ) → Multiset ℂ) (m₂ : ℕ → (E →+* ℂ) → Multiset ℂ) (n₁ n₂ : (E →+* ℂ) → Multiset ℂ)
  (C : Set (HeckeM E a b ι)) (lam : ℕ → HeckeM E a b ι → ℂ) (lam₀ : HeckeM E a b ι → ℂ)
  (f : ℕ → ι → H E a b → ℂ), C.Countable →

  (∀ (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin N) (Af E))) (W' : Submodule ℂ (Kinf E N → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R') →

  (∀ k i, Continuous (f k i)) → (∀ k, f k ≠ 0) → (∀ k, LeftInv (f k)) → (∀ k, WL2 D M (f k)) →
  (∀ k i, TypeH K₁ K₂ W₁ W₂ (f k i)) →
  (∀ k i (m₂ : GA E b), ∃ φ : Sm E a, φ.1 = fun x => f k i (x, m₂)) →
  (∀ k i (m₁ : GA E a), ∃ φ : Sm E b, φ.1 = fun x => f k i (m₁, x)) →
  (∀ k, ∀ φ ∈ slices₁ (f k), IsAutForm φ) → (∀ k, ∀ φ ∈ slices₂ (f k), IsAutForm φ) →
  (∀ k τ, HasInfCharGL (Submodule.span ℂ (slices₁ (f k))) τ (m₁ k τ)) →
  (∀ k τ, HasInfCharGL (Submodule.span ℂ (slices₂ (f k))) τ (m₂ k τ)) →
  (∀ k, ∀ h ∈ C, heckeAct h (f k) = lam k h • f k) →

  (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, MClose ε (m₁ k τ) (n₁ τ) ∧ MClose ε (m₂ k τ) (n₂ τ)) →
  RealSym n₁ → RealSym n₂ → (∀ τ, GapM (n₁ τ) ∧ GapM (n₂ τ)) →
  (∀ h ∈ C, Tendsto (fun k => lam k h) atTop (𝓝 (lam₀ h))) →
  ∃ (s₁ : Tr E a) (s₂ : Tr E b) (F : ι → H E a b → ℂ), s₁.Good ∧ s₂.Good ∧ s₁.Untw ∧ s₂.Untw ∧
    s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₁ M, ∃ W' ∈ Ω₁ M, HasType K' W' V) ∧
    s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₂ M, ∃ W' ∈ Ω₂ M, HasType K' W' V) ∧
    (∀ τ, HasInfCharGL s₁.space τ (n₁ τ)) ∧ (∀ τ, HasInfCharGL s₂.space τ (n₂ τ)) ∧
    F ≠ 0 ∧ (∀ i, F i ∈ pairSpace s₁.space s₂.space) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (F i)) ∧
    ∀ h ∈ C, heckeAct h F = lam₀ h • F

end PositivityTheory.Rg.BcB.SpectralAccumulation

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B
open PositivityTheory.Rg.BcB.Desc
open PositivityTheory.Rg.BcB.F

namespace GlobalTheory.CompanionTheory.LFixDPf

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}



section Conj

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

end Conj

section Int

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

theorem mem_KGL_map_conj (u : Pl E) (g : GLw n (conjSrc (conjE E) u)) :
    GeneralLinearGroup.map (conjLoc (conjE E) u) g ∈ GlobalTheory.LFun.KGL u (n := n) ↔ g ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) (n := n) := by
  have hv : ∀ x : (conjSrc (conjE E) u).adicCompletion E,
      conjLoc (conjE E) u x ∈ u.adicCompletionIntegers E ↔ x ∈ (conjSrc (conjE E) u).adicCompletionIntegers E := fun x => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec (conjE E) u).2.2 x]
  rw [GlobalTheory.AdelicU.mem_GLint_iff, GlobalTheory.AdelicU.mem_GLint_iff]
  refine and_congr (forall₂_congr fun a b => hv _) (forall₂_congr fun a b => ?_)
  rw [← map_inv]
  exact hv _

end Int

section Int2

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

end Int2

section Main

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws
open PositivityTheory.Rg.BcB.F.F5.Bo

variable {d : LocData E n}

end Main

section Core

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws
open PositivityTheory.Rg.BcB.F.F5.Bo

end Core

end GlobalTheory.CompanionTheory.LFixDPf

end
end

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem comp_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := congrArg (RingHom.mapMatrix (pLoc E u)) (mem_Sim.1 k.2)
  rw [map_mul] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

private theorem val_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (hk : sim k ∈ ZU) (u : Plc E) :
    Valued.v (pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ))) = 1 := by
  show Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ) u) = 1
  rw [GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply, GroundTheory.Global.SemiLocal.valued_completionMap,
    hk (GroundTheory.Global.AdeleBaseChange.below ℚ u), one_pow]

theorem UpperTheory.Gal.CertificateRingHomMap.pIntConj_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj := by
  intro E _ _ _ n k w hs ha
  have hmap : ∀ g : Matrix.GeneralLinearGroup (Fin n) ((cj w).adicCompletion E),
      Matrix.GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) g ∈ GlobalTheory.LFun.KGL w n ↔
        g ∈ GlobalTheory.LFun.KGL (cj w) n := by
    intro g
    have hv : ∀ x : (cj w).adicCompletion E,
        conjLoc (GlobalTheory.SplitPts.conjE E) w x ∈ w.adicCompletionIntegers E ↔
          x ∈ (cj w).adicCompletionIntegers E := fun x => by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
        (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2 x]
    rw [GlobalTheory.AdelicU.mem_GLint_iff, GlobalTheory.AdelicU.mem_GLint_iff]
    refine and_congr (forall₂_congr fun a b => hv _) (forall₂_congr fun a b => ?_)
    rw [← map_inv]
    exact hv _
  rw [← hmap]
  set s := pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) with hsdef
  have hv : Valued.v s = 1 := val_sim k hs w
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  set a := comp w k with hadef
  set G := Matrix.GeneralLinearGroup.map (n := Fin n) (conjLoc (GlobalTheory.SplitPts.conjE E) w) (comp (cj w) k) with hG
  have hrel : (G.val)ᵀ * a.val = s • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := comp_rel k w
  have hGt : (G.val)ᵀ = s • (a⁻¹).val := by
    calc (G.val)ᵀ = (G.val)ᵀ * (a.val * (a⁻¹).val) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = ((G.val)ᵀ * a.val) * (a⁻¹).val := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hrel, smul_mul_assoc, Matrix.one_mul]
  have hGi : (G⁻¹).val = s⁻¹ • (a.val)ᵀ := by
    have h1 : G.val * (s⁻¹ • (a.val)ᵀ) = 1 := by
      have h2 : a.val * (G.val)ᵀ = s • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
        rw [hGt, Matrix.mul_smul, Units.mul_inv]
      have h3 := congrArg Matrix.transpose h2
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at h3
      rw [Matrix.mul_smul, h3, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    calc (G⁻¹).val = (G⁻¹).val * (G.val * (s⁻¹ • (a.val)ᵀ)) := by rw [h1, Matrix.mul_one]
      _ = ((G⁻¹).val * G.val) * (s⁻¹ • (a.val)ᵀ) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.one_mul]
  obtain ⟨ha1, ha2⟩ := (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w a).1 ha
  refine (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w G).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · have h := congrFun (congrFun hGt j) i
    rw [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [h, map_mul, hv, one_mul]
    exact ha2 j i
  · rw [hGi, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hv, inv_one, one_mul, Matrix.transpose_apply]
    exact ha1 j i
