module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLatticeSelfDualComponentsRescaledWordFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspaceProperty
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomotheticOfMonomialPrimitiveSelfDualCores
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharSymplecticFinitePartRestEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastWittLineOfBesselJacobiLatticesGood
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralElementHomotheticGluedCores
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnLevelIffRowLatticeKeptAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalSumCoresHomotheticOffLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralGlueLocalHomotheties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLineStableLatticeSplitsAlongWittSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLineStableLatticeSplitsAlongWittSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.SplitLat

variable {D : D7}

theorem pair_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_i₀ {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Fin S.rank → D.host.E) (y : Fin S₀.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * (d.i₀ *ᵥ y) j = ∑ i, ∑ j, star ((d.q0 *ᵥ x) i) * S₀.gram i j * y j := by
  have hG : S.gram * d.i₀ = d.q0ᴴ * S₀.gram := by
    rw [gram_eq d]
    simp only [Matrix.add_mul, Matrix.mul_assoc, qX_i₀, qY_i₀, wittDecomposition_coreProj_mul_core_eq_one, Matrix.mul_zero, Matrix.mul_one, add_zero,
      zero_add]
  rw [pair_eq_dot, pair_eq_dot, Matrix.mulVec_mulVec, hG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec]

theorem mulVec_eq_sum_cols {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    M *ᵥ w = ∑ i, fun r => w i * M r i := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem colProj_mulVec' {S : HSp D} {ρ m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E)
    (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) (x : Fin m → D.host.E) :
    colProj q f i *ᵥ x = fun r => (q *ᵥ x) i * f r i := by
  funext k
  simp only [colProj, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem selfDual_core_monoAt (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (hL : IsSelfDualC S L)
    (hcol : ∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) :
    IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by

  have hcore : ∀ y ∈ L, d.q0 *ᵥ y ∈ coreLat d L := by
    intro y hy
    rw [mem_coreLat]
    have hdec : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one_rat, Matrix.one_mulVec]
    have hX : d.e *ᵥ (d.qX *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).1
    have hY : d.e' *ᵥ (d.qY *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).2
    have key : ∀ a b c z : Fin S.rank → D.host.E, z = a + b + c → b = z - a - c := by
      intro a b c z hz; rw [hz]; abel
    have h : d.i₀ *ᵥ (d.q0 *ᵥ y) = y - d.e *ᵥ (d.qX *ᵥ y) - d.e' *ᵥ (d.qY *ᵥ y) := key _ _ _ _ hdec
    rw [h]
    exact sub_mem (sub_mem hy hX) hY
  have hinj : Function.Injective ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) := by
    intro x x' hxx
    have h := congrArg (fun z => d.q0 *ᵥ z) hxx
    simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one,
      Matrix.one_mulVec] using h
  refine ⟨⟨⟨?_, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩, fun v => ?_⟩
  ·
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hLfg : L.FG := hL.1.fg
    haveI : IsNoetherian (𝓞 D.host.E) L := isNoetherian_of_fg_of_noetherian L hLfg
    have hle : (coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ≤ L :=
      Submodule.map_comap_le _ _
    have h1 : (((coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))).comap L.subtype).FG :=
      IsNoetherian.noetherian _
    have h2 := h1.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  ·
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  ·
    obtain ⟨b, hb⟩ := (hL.2 (d.i₀ *ᵥ y)).1 hy (d.i₀ *ᵥ x) hx
    refine ⟨b, ?_⟩
    rw [hb, pair_i₀, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec]
  ·
    rw [mem_coreLat]
    refine (hL.2 (d.i₀ *ᵥ y)).2 fun x hx => ?_
    obtain ⟨b, hb⟩ := h (d.q0 *ᵥ x) (hcore x hx)
    exact ⟨b, hb.trans (pair_i₀ d x y).symm⟩
  ·
    have hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).1
    have hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).2
    intro y
    constructor
    · intro hy
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hX i) _ hy
      · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hY i) _ hy
      · exact rat_mulVec_mem_latV d.q0 hcore _ hy
    · rintro ⟨h1, h3, h2⟩
      have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
          d.sum_eq_one, Matrix.one_mulVec]
      rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
      refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
      exact rat_mulVec_mem_latV d.i₀ (fun x hx => hx) _ h2

end GlobalTheory.Core.Mi.LatMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLineStableLatticeSplitsAlongWittSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lineStable_lattice_splitsAlongWitt_selfDualCore : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S), IsSelfDualC S L → (∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) → IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt | exact GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt | (intros; apply GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingStabilisesIffCoreStabilises
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingStabilisesIffCoreStabilises
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem moves_emb0_iff_moves_of_monoAt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (γ : GA D S₀), MonoAt d L M v → (Moves S (d.emb0 γ) L L (· = v) ↔ Moves S₀ γ M M (· = v)) := by
  intro D S S₀ ρ d L M v γ hL
  have supp : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D), (∀ i, y i ∈ idAt D (· = v)) →
      ∀ i, (A *ᵥ y) i ∈ idAt D (· = v) := fun A y hy i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy k)
  have hc : ∀ {n : ℕ} (x : Matrix (Fin S.rank) (Fin n) (AE D)) (i : Fin n), colMul x i 0 = 0 := fun x i => by
    funext k; simp [colMul]
  have j0iff : ∀ w : Fin S₀.rank → AE D, d.j0 *ᵥ w ∈ latV S L (· = v) ↔ w ∈ latV S₀ M (· = v) := by
    intro w
    rw [hL]
    simp only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc,
      zero_mem, implies_true, true_and]
  constructor
  · intro h w hw
    have h1 := h (d.j0 *ᵥ w) (supp _ _ hw)
    rw [j0iff, Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, j0iff] at h1
    exact h1
  · intro h y hy
    rw [hL y, hL (mt S (d.emb0 γ) *ᵥ y)]
    simp only [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding, d.wittDecomp_projY_anisotropicEmbedding, d.wittDecomp_projAnisotropic_anisotropicEmbedding]
    rw [← Matrix.mulVec_mulVec, ← h _ (supp _ _ hy)]

end GlobalTheory.Core.Mi.LatMatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingStabilisesIffCoreStabilisesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (γ : GA D S₀), MonoAt d L M v → (Moves S (d.emb0 γ) L L (· = v) ↔ Moves S₀ γ M M (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.moves_emb0_iff_moves_of_monoAt | exact GlobalTheory.Core.Mi.LatMatch.moves_emb0_iff_moves_of_monoAt | (intros; apply GlobalTheory.Core.Mi.LatMatch.moves_emb0_iff_moves_of_monoAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentMonomialLatticeSplitCore
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentMonomialLatticeSplitCore
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.FinPl.FrameLat

section

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_sec_w (p : SplitPt D k) {m n : ℕ} (a : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → k) :
    a *ᵥ (fun i => p.sec (y i)) = fun i => p.sec ((a.map p.pr *ᵥ y) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, sec_mul_right, mul_comm]

theorem inc_mul_sec_mem_iff (p : SplitPt D k) (α : D.host.E) (x : k) :
    incA D α * p.sec x ∈ intAt D (· = p.v) ↔ p.pr (incA D α) * x ∈ 𝒪[k] := by
  rw [mul_comm, sec_mul_right, mul_comm x]
  exact ⟨fun h => (p.int_iff _).2 h.2, sec_mem_intAt p _⟩

theorem proj_mulVec_add {R : Type} [CommRing R] {l m n : ℕ} {P : Matrix (Fin m) (Fin l) R} {J : Matrix (Fin l) (Fin m) R}
    {J' : Matrix (Fin l) (Fin n) R} (h1 : P * J = 1) (h0 : P * J' = 0) (u : Fin m → R) (v : Fin n → R) :
    P *ᵥ (J *ᵥ u + J' *ᵥ v) = u := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h0, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

end


set_option maxHeartbeats 1000000 in
theorem wShape_of_mono (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E)
    (L : Lat S) (M : Lat S₀) (N : Lat A) (α α' : Fin ρ → D.host.E) (μ : D.host.E) (g : GA D A)
    (hmono : MonoAt d L M p.v)
    (hX : ∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jX i a ∈ latV S L (· = p.v) ↔ incA D (α i) * a ∈ intAt D (· = p.v))
    (hY : ∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jY i a ∈ latV S L (· = p.v) ↔ incA D (α' i) * a ∈ intAt D (· = p.v))
    (hline : LineAt (vecB o ζ) μ M p.v) (hsplit : SplitsAt o M p.v) (htr : TraceAt o g N M p.v) :
    WShape p d o ζ L (fun i => p.pr (incA D (α i))) (fun i => p.pr (incA D (α' i))) (p.pr (incA D μ)) g N := by
  intro x x' t y
  let f : D.host.E →+* k := p.pr.comp (incA D)
  have hz : o.jB *ᵥ (fun i => p.sec ((t • (f ∘ ζ)) i)) = p.sec t • ratV (vecB o ζ) := by
    rw [mulVec_sec_w, Matrix.mulVec_smul]
    funext i
    have h := RingHom.map_mulVec f o.iB ζ i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, sec_mul_right]
    exact congrArg (fun u => p.sec (t * u)) h.symm
  obtain ⟨c, hc⟩ : ∃ c : Fin S₀.rank → AE D, c = o.jB *ᵥ (fun i => p.sec ((t • (f ∘ ζ)) i)) +
    o.jA *ᵥ (Formalism.L2.Theta.mt A g *ᵥ fun r => p.sec (y r)) := ⟨_, rfl⟩
  have hcid : ∀ i, c i ∈ idAt D (· = p.v) := fun i => by
    rw [hc, mulVec_sec_w, mulVec_sec_w, mulVec_sec_w]
    exact add_mem (sec_mem_idAt p _) (sec_mem_idAt p _)
  have hvec : (fun r => p.sec ((atW p d.e *ᵥ x + atW p d.e' *ᵥ x' + t • (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A g).map p.pr *ᵥ y)) r)) =
      d.jX *ᵥ (fun i => p.sec (x i)) + d.jY *ᵥ (fun i => p.sec (x' i)) + d.j0 *ᵥ c := by
    have h1 : (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) = d.i₀.map f *ᵥ (o.iB.map f *ᵥ (f ∘ ζ)) := by
      have h2 : o.iB.map f *ᵥ (f ∘ ζ) = f ∘ vecB o ζ := by
        funext i; exact (RingHom.map_mulVec f o.iB ζ i).symm
      rw [h2]
      funext i; exact RingHom.map_mulVec f d.i₀ _ i
    have h3 : atW p (d.i₀ * o.iA) = d.i₀.map f * o.iA.map f := Matrix.map_mul (f := f)
    rw [hc, Matrix.mulVec_add, h1, h3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
    have e1 : d.jX.map p.pr = atW p d.e := rfl
    have e2 : d.jY.map p.pr = atW p d.e' := rfl
    have e3 : d.j0.map p.pr = d.i₀.map f := rfl
    have e4 : o.jA.map p.pr = o.iA.map f := rfl
    have e5 : o.jB.map p.pr = o.iB.map f := rfl
    rw [mulVec_sec_w p d.jX, mulVec_sec_w p d.jY, mulVec_sec_w p o.jB, mulVec_sec_w p d.j0,
      mulVec_sec_w p (Formalism.L2.Theta.mt A g), mulVec_sec_w p o.jA, mulVec_sec_w p d.j0, e1, e2, e3, e4, e5]
    funext r
    simp only [Pi.add_apply, map_add p.sec, add_assoc]
  rw [hvec, hmono]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, d.pX_jX, d.pX_jY, d.pX_j0, d.pY_jX, d.pY_jY, d.pY_j0, d.p0_jX,
    d.p0_jY, d.p0_j0, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  have hA : o.pA *ᵥ c = Formalism.L2.Theta.mt A g *ᵥ fun r => p.sec (y r) := by
    rw [hc, add_comm]; exact proj_mulVec_add o.pA_jA o.pA_jB _ _
  have hB : o.pB *ᵥ c = fun i => p.sec ((t • (f ∘ ζ)) i) := by
    rw [hc]; exact proj_mulVec_add o.pB_jB o.pB_jA _ _
  rw [hsplit c hcid, hA, hB, hz, hline _ (sec_mem_idAt p t), ← htr _ (fun i => sec_mem_idAt p _), inc_mul_sec_mem_iff]
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) and_comm)
  · rw [hX i _ (sec_mem_idAt p _), inc_mul_sec_mem_iff]
  · rw [hY i _ (sec_mem_idAt p _), inc_mul_sec_mem_iff]

end GlobalTheory.Core.Mi.LatMatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentMonomialLatticeSplitCoreStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceComponent_monomialLattice_splitCore : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L : Lat S) (M : Lat S₀) (N : Lat A) (α α' : Fin ρ → D.host.E) (μ : D.host.E) (g : GA D A), MonoAt d L M p.v → (∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jX i a ∈ latV S L (· = p.v) ↔ incA D (α i) * a ∈ intAt D (· = p.v)) → (∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jY i a ∈ latV S L (· = p.v) ↔ incA D (α' i) * a ∈ intAt D (· = p.v)) → LineAt (vecB o ζ) μ M p.v → SplitsAt o M p.v → TraceAt o g N M p.v → WShape p d o ζ L (fun i => p.pr (incA D (α i))) (fun i => p.pr (incA D (α' i))) (p.pr (incA D μ)) g N := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.wShape_of_mono | exact GlobalTheory.Core.Mi.LatMatch.wShape_of_mono | (intros; apply GlobalTheory.Core.Mi.LatMatch.wShape_of_mono <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLineIdealEqInverseDifferentPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLineIdealEqInverseDifferentPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch.DiffInv

theorem aaD_eq_dI_pow : ∀ (D : D7) (i : Fin D.R.rS), aaD D i = dI D ^ (D.R.rS - i.1) := by
  intro D i
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  have hinv : dI D = (ddS D)⁻¹ := by
    rw [GlobalTheory.IntTerm.Conv.ddS_eq]
    exact eq_inv_of_mul_eq_one_left hP
  rw [hinv, inv_pow, aaD, ← Nat.cast_sub i.2.le, _root_.zpow_neg, _root_.zpow_natCast]

end GlobalTheory.Core.Mi.LatMatch.DiffInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLineIdealEqInverseDifferentPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLineIdeal_eq_inverseDifferent_pow : ∀ (D : D7) (i : Fin D.R.rS), aaD D i = dI D ^ (D.R.rS - i.1) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow | exact GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow | (intros; apply GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelLineVectorPrimitiveRowLatticeNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelLineVectorPrimitiveRowLatticeNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

theorem cY_eq_repr (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h y = (X.bas.reindex (finCongr (rank_eq X h)).symm).repr y := by
  funext k
  simp [GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, Module.Basis.repr_reindex]

theorem sum_bas_mem_iff (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (ιE : I.E ≃+* D.host.E)
    (hId : ∀ x : I.E, HEq (ιE x) x) (hn : (D.sp.Y 0).rank = I.n) (bas : Module.Basis (Fin I.n) D.host.E (VS D).V)
    (hL : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0) (v : Fin (D.sp.Y 0).rank → D.host.E) :
    (∑ k, v k • bas (Fin.cast hn k)) ∈ (VS D).L0 ↔ (∑ k, v k • (VS D).frame k) ∈ (VS D).L0 := by
  subst hI
  have h2 : ∀ i, ιE (v i) = v i := fun i => eq_of_heq (hId _)
  rw [← Formalism.L2.SG.InstExistsPf.mem_Lv]
  refine Iff.trans ?_ (hL v).symm
  apply iff_of_eq
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i]
  rfl

theorem cY_mem_latS_iff (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : GlobalTheory.Core.Mi.IdE X)
    (y : (VS D).V) : GlobalTheory.Core.SBesEx.cY X h y ∈ latS D ↔ y ∈ (VS D).L0 := by
  have hs := sum_bas_mem_iff X.B.I h X.ιE hId (rank_eq X h) X.bas X.L_eq (GlobalTheory.Core.SBesEx.cY X h y)
  have hy : (∑ k, GlobalTheory.Core.SBesEx.cY X h y k • X.bas (Fin.cast (rank_eq X h) k)) = y := by
    rw [cY_eq_repr]
    conv_rhs => rw [← (X.bas.reindex (finCongr (rank_eq X h)).symm).sum_repr y]
    simp
  rw [hy] at hs
  rw [hs]
  simp only [latS, Formalism.L2.Herm.crdLat, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Formalism.L2.Herm.crd]
  constructor
  · rintro ⟨w, hw, hwe⟩
    have : w = ∑ k, GlobalTheory.Core.SBesEx.cY X h y k • (VS D).frame k := by
      rw [← hwe]; exact ((VS D).frame.sum_equivFun w).symm
    rw [← this]; exact hw
  · intro hw
    exact ⟨_, hw, by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem cY_smul (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (c : D.host.E) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h (c • y) = c • GlobalTheory.Core.SBesEx.cY X h y := by
  rw [cY_eq_repr, cY_eq_repr, map_smul, Finsupp.coe_smul]

end GlobalTheory.Core.Mi.LatMatch.SZ

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

theorem smul_zu_mem_iff (X : HidaSetting D) (u : D.what₂.Word) (c : D.host.E) :
    c • X.zu u ∈ (VS D).L0 ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  constructor
  · intro hc
    have hfix := (X.Fu_fixed u).2.2.2.2
    apply hfix c
    have hz : (X.Fu u).z = X.zu u := X.flagZVector u
    show c • (X.Fu u).z ∈ _
    rw [hz]
    have horth : c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u).X := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [map_smulₛₗ, ← hz, (X.Fu u).z_orth a, smul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, smul_zero]
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hc, horth⟩), horth⟩
  · rintro ⟨o, rfl⟩
    have hz : X.zu u ∈ (VS D).L0 := by
      rw [X.Lam_split]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.zu_Lb u))
    have := (VS D).L0.smul_mem o hz
    simpa [algebraMap_smul] using this

theorem quad {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n D.host.E) (G : Matrix m m D.host.E) (x : n → D.host.E) :
    star x ⬝ᵥ (Mᴴ * G * M) *ᵥ x = star (M *ᵥ x) ⬝ᵥ G *ᵥ (M *ᵥ x) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Core.Mi.LatMatch.SZ


open GlobalTheory.Core.Mi.LatMatch.SZ in
theorem GlobalTheory.Core.Mi.LatMatch.sz_tied : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → (∀ t : D.host.E, t • vecB B.o B.ζ ∈ coreLat B.d (latS D) ↔ μ * t ∈ (1 : FI D)) ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(μ * star μ * (((D.mem u).A.T : ℕ) : D.host.E)) ∧ vecB B.o B.ζ ≠ 0 := by
  intro D X h u ψ A B μ lam hId hF
  have hz : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u) := hF.z
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rw [mem_coreLat, Matrix.mulVec_smul, hz, smul_smul, ← cY_smul, cY_mem_latS_iff X h hId, smul_zu_mem_iff,
      FractionalIdeal.mem_one_iff, mul_comm]
  · rw [← B.o.isoB, quad, ← B.d.iso, quad]
    change star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = _
    rw [hz, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct,
      GlobalTheory.Core.SBesEx.cY_isom D X h hId, X.zu_norm]
    simp only [smul_eq_mul]
    ring
  · intro h0
    apply B.line.2
    rw [← B.o.isoB, quad]
    change star (vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (vecB B.o B.ζ) = 0
    rw [h0]
    simp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelLineVectorPrimitiveRowLatticeNormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → (∀ t : D.host.E, t • vecB B.o B.ζ ∈ coreLat B.d (latS D) ↔ μ * t ∈ (1 : FI D)) ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(μ * star μ * (((D.mem u).A.T : ℕ) : D.host.E)) ∧ vecB B.o B.ζ ≠ 0 := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.sz_tied | exact GlobalTheory.Core.Mi.LatMatch.sz_tied | (intros; apply GlobalTheory.Core.Mi.LatMatch.sz_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemChainLevelIffCarriesLatticeOffLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemChainLevelIffCarriesLatticeOffLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LevChain

theorem mem_levS_iff_moves : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D) (j : ℕ) (s : GlobalTheory.ChainOnto.PiLocalization₂ D), s.Is c j → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ c.S → ∀ κ ∈ grpAt s.V (· = v), κ ∈ levS s.V s.β s.L ↔ Moves s.V κ s.Λ s.Λ (· = v) := by
  intro D c j s hs v hv κ hκ
  haveI : Submodule.IsLattice D.host.E s.Λ := hs.selfDual.1
  have hfg : s.Λ.FG := Submodule.IsLattice.fg (A := D.host.E) s.Λ
  have hGf := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff s.V (· = v) κ).1 hκ
  have hSt : Lev.finE s.V κ ∈ Formalism.L2.DIV.St s.β ↔ κ ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig s.V.gram s.Λ := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_of_fg s.V s.β s.Λ hs.frame hfg κ]
    exact GlobalTheory.AdelicU.mem_levelOpen.symm
  constructor
  · intro h
    have h2 : Lev.finE s.V κ ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L := h.2
    exact GlobalTheory.FinPl.KOpen.moves_of_levelOpen s.V s.Λ hfg _ (hSt.1 (Formalism.L2.DIV.parLev_St h2.1))
  · intro hm
    have hS := hSt.2 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK s.V s.Λ hfg _ ⟨hκ, hm⟩)
    obtain ⟨hr, ξ, hL⟩ := hs.lev
    refine ⟨hGf.1, ?_⟩
    refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS fun PP hPP => ?_
    have hPg : PP ∈ c.Pg := by
      rw [hL] at hPP
      simpa [Lev.datY] using hPP
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β κ PP hS (hGf.2 _ ?_)
    intro he
    exact hv (Finset.mem_image.2 ⟨PP, hPg, he⟩)

end GlobalTheory.Core.Mi.LevChain

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemChainLevelIffCarriesLatticeOffLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_chainLevel_iff_carriesLattice_offLevel : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D) (j : ℕ) (s : GlobalTheory.ChainOnto.PiLocalization₂ D), s.Is c j → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ c.S → ∀ κ ∈ grpAt s.V (· = v), κ ∈ levS s.V s.β s.L ↔ Moves s.V κ s.Λ s.Λ (· = v) := by
  first | exact @GlobalTheory.Core.Mi.LevChain.mem_levS_iff_moves | exact GlobalTheory.Core.Mi.LevChain.mem_levS_iff_moves | (intros; apply GlobalTheory.Core.Mi.LevChain.mem_levS_iff_moves <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem ratV_vecB {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    ratV (vecB o ζ) = o.jB *ᵥ ratV ζ :=
  funext fun i => RingHom.map_mulVec (incA D) o.iB ζ i

theorem mt_one' (S : HSp D) : Formalism.L2.Theta.mt S 1 = 1 := GlobalTheory.FinPlLoc.mt_one S

theorem emb_mem_grpAt {S A B : HSp D} (o : OrthDec S A B) {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  have ha' := (GlobalTheory.IwaPlace.mem_congGrp_iff A (idAt D P) a).1 ha
  refine (GlobalTheory.IwaPlace.mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : Formalism.L2.Theta.mt S (o.emb (a, 1)) - 1 = HMul.hMul (HMul.hMul o.jA (Formalism.L2.Theta.mt A a - 1)) o.pA := by
    rw [o.mt_emb, ← o.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, mt_one', Matrix.mul_one, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact ha' l k)

theorem embA_mem_grpAt {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {P : GlobalTheory.FinPl.Pl D → Prop}
    {a : GA D A} (ha : a ∈ grpAt A P) : embA d o a ∈ grpAt S P :=
  GlobalTheory.IwaPlace.wittCoreEmbedding_preserves_supportedUnitarySubgroup d (emb_mem_grpAt o ha)

theorem emb_fix {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (a : GA D A) :
    Formalism.L2.Theta.mt S (o.emb (a, 1)) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
  rw [ratV_vecB, Matrix.mulVec_mulVec]
  have := o.emb_jB a 1
  rw [mt_one', Matrix.mul_one] at this
  exact congrArg (· *ᵥ ratV ζ) this

theorem j_zero_mul_mem_lattice_iff {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D)
    (hL : MonoAt d L M v) (w : Fin S₀.rank → AE D) : d.j0 *ᵥ w ∈ latV S L (· = v) ↔ w ∈ latV S₀ M (· = v) := by
  have hc : ∀ {n : ℕ} (x : Mx D S.rank n) (i : Fin n), colMul x i 0 = 0 := fun x i => by
    funext k; simp [colMul]
  rw [hL]
  simp only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc,
    zero_mem, implies_true, true_and]

theorem line_loc {S : HSp D} {L : Lat S} {x : Fin S.rank → D.host.E} (hL : IsSelfDualC S L) (hx : x ≠ 0) {c : D.host.E}
    (hc : c ≠ 0) {𝔟 : FI D} (h : ∀ t : D.host.E, t • x ∈ L ↔ c * t ∈ 𝔟) (v : GlobalTheory.FinPl.Pl D) :
    ∀ a ∈ idAt D (· = v), a • ratV x ∈ latV S L (· = v) ↔ incA D c * a ∈ idV 𝔟 v := by
  obtain ⟨𝔞, -, h1, h2⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D S L x hL hx
  have e : 𝔞 = FractionalIdeal.spanSingleton _ c⁻¹ * 𝔟 := by
    ext t
    rw [← h1, h, FractionalIdeal.mem_singleton_mul]
    constructor
    · intro ht
      exact ⟨c * t, ht, by field_simp⟩
    · rintro ⟨y, hy, rfl⟩
      rwa [mul_inv_cancel_left₀ hc]
  intro a ha
  rw [h2 v a ha, e, GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff D v 𝔟 c⁻¹ (inv_ne_zero hc), inv_inv]
  exact and_iff_left ha

theorem col_e_ne {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : (fun r => d.e r i) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun d.e'e i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have : ∀ r, d.e r i = 0 := fun r => congrFun h r
  simp [this] at h1

theorem col_e'_ne {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : (fun r => d.e' r i) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun d.e'e i) i
  rw [Matrix.mul_assoc, Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have : ∀ r, d.e' r i = 0 := fun r => congrFun h r
  simp [this] at h1

theorem nat_mul_mem_iff {N : ℕ} {v : GlobalTheory.FinPl.Pl D} (hN : (N : 𝓞 D.host.F) ∉ v.asIdeal) (𝔟 : FI D) (a : AE D) :
    incA D (N : D.host.E) * a ∈ idV 𝔟 v ↔ a ∈ idV 𝔟 v := by
  have h0 : (N : D.host.E) ≠ 0 := by
    intro h
    have : N = 0 := by exact_mod_cast h
    exact hN (by rw [this, Nat.cast_zero]; exact zero_mem _)
  constructor
  · intro h
    have := GlobalTheory.SeeSaw.idV_natInv_mul_le D 𝔟 N v hN (GlobalTheory.SeeSaw.idV_incA_mul ((N : D.host.E)⁻¹) 𝔟 v h)
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul] at this
  · intro h
    rw [map_natCast, ← nsmul_eq_mul]
    exact nsmul_mem h N

theorem pow_mul_mem_iff {N : ℕ} {v : GlobalTheory.FinPl.Pl D} (hN : (N : 𝓞 D.host.F) ∉ v.asIdeal) {lam : D.host.E}
    (hl : lam = (N : D.host.E) ∨ lam = -(N : D.host.E)) (𝔟 : FI D) (n : ℕ) (a : AE D) :
    incA D (lam ^ n) * a ∈ idV 𝔟 v ↔ a ∈ idV 𝔟 v := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul, mul_assoc, ih]
    rcases hl with rfl | rfl
    · exact nat_mul_mem_iff hN 𝔟 a
    · rw [map_neg, neg_mul, neg_mem_iff]; exact nat_mul_mem_iff hN 𝔟 a

theorem val_nat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    {N : ℕ} (hN : (N : 𝓞 D.host.F) ∉ p.v.asIdeal) : valuation k (p.pr (incA D (N : D.host.E))) = 1 := by
  obtain ⟨PP, hP⟩ := GlobalTheory.SeeSaw.LevelTest.exists_prime p
  obtain ⟨ε, hε, he⟩ := p.above
  have hu := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP _ ε hP hε he
  have h1 := GlobalTheory.SeeSaw.LevelTest.val_le_one p (N : 𝓞 D.host.E)
  have h2 := GlobalTheory.SeeSaw.LevelTest.val_lt_one_iff p hP (N : 𝓞 D.host.E)
  have e : ((N : 𝓞 D.host.E) : D.host.E) = N := by simp
  rw [e] at h1 h2
  refine le_antisymm h1 (not_lt.1 fun h => hN ?_)
  rw [← hu]
  have := h2.1 h
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (N : 𝓞 D.host.F) ∈ PP.asIdeal
  rwa [map_natCast]

section Rows

variable {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {B : SBes X h u ψ (D.sp.X 0)} {μ lam : D.host.E}

theorem g_ne (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : ((X.B.g : ℕ) : D.host.E) ≠ 0 := by
  rw [X.g_eq]
  exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem lam_ne (hF : B.FrameAt μ lam) : lam ≠ 0 := by
  rcases hF.sign with hl | hl <;> rw [hl]
  · exact g_ne X
  · exact neg_ne_zero.2 (g_ne X)

theorem scl_ne (hF : B.FrameAt μ lam) (i : Fin D.R.rS) : GlobalTheory.Core.SBesEx.scl μ lam i ≠ 0 :=
  mul_ne_zero hF.ne (pow_ne_zero _ (lam_ne hF))

theorem rows_shape (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) :
    IsSelfDualC (D.sp.Y 0) (latS D) ∧ IsSelfDualC B.V₀ (coreLat B.d (latS D)) ∧
    (∀ v, MonoAt B.d (latS D) (coreLat B.d (latS D)) v) ∧
    (∀ v (i : Fin D.R.rS), ∀ a ∈ idAt D (· = v), colMul B.d.jX i a ∈ latV (D.sp.Y 0) (latS D) (· = v) ↔
      incA D (GlobalTheory.Core.SBesEx.scl μ lam i) * a ∈ idV (dI D ^ (D.R.rS - i.1)) v) ∧
    (∀ v (i : Fin D.R.rS), ∀ a ∈ idAt D (· = v), colMul B.d.jY i a ∈ latV (D.sp.Y 0) (latS D) (· = v) ↔
      incA D (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * a ∈ idV (dI D ^ (D.R.rS - i.1))⁻¹ v) ∧
    ∀ v, LineAt (vecB B.o B.ζ) μ (coreLat B.d (latS D)) v := by
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.rowLattice_selfDual_components_rescaled_word_frame D X h u ψ _ B μ lam hE hF
  obtain ⟨h5, h6⟩ := GlobalTheory.T.selfDual_lineStable_lattice_splitsAlongWitt_selfDualCore D _ _ _ B.d (latS D) h1 h2
  obtain ⟨h7, -, h8⟩ := GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D X h u ψ _ B μ lam hE hF
  refine ⟨h1, h5, h6, fun v i => ?_, fun v i => ?_, fun v a ha => ?_⟩
  · rw [← GlobalTheory.T.rowLineIdeal_eq_inverseDifferent_pow D i]
    exact line_loc h1 (col_e_ne B.d i) (scl_ne hF i) (h3 i) v
  · rw [← GlobalTheory.T.rowLineIdeal_eq_inverseDifferent_pow D i]
    exact line_loc h1 (col_e'_ne B.d i) (inv_ne_zero (star_ne_zero.2 (scl_ne hF i))) (h4 i) v
  · rw [line_loc h5 h8 hF.ne h7 v a ha, GlobalTheory.SeeSaw.idV_one_eq_intAt]

variable {F : Formalism.L2.Forms.Forms0 D u} {tr : Formalism.L2.SG.ColDict.Transport X u F} {hK : X.LevelSubgroupCharacter} {a₀ : GA D (D.sp.X 0)}

theorem rows_trace (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) (hM : Formalism.L2.SG.ColDict.LevelMatch X tr hK)
    (hA : B.Adapted tr.wt) (h0 : IsTransportAdelicCorrection tr a₀) (v : GlobalTheory.FinPl.Pl D) {N : Lat (D.sp.X 0)}
    (hN : latV (D.sp.X 0) N (· = v) = latV (D.sp.X 0) (lat0 F) (· = v)) : TraceAt B.o a₀ N (coreLat B.d (latS D)) v := by
  intro y hy
  rw [hN, GlobalTheory.T.transportCorrection_carries_columnLattice_rowTrace D X h u ψ F tr hK B a₀ hE hM hA h0 v y hy, j_zero_mul_mem_lattice_iff B.d _ _ v ((rows_shape hE hF).2.2.1 v)]

theorem loc_of_core (hψ : IsStdChar D ψ (-1)) (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) {v : GlobalTheory.FinPl.Pl D}
    (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) {L : Lat (D.sp.Y 0)} {M : Lat B.V₀}
    (hL : IsSelfDualC (D.sp.Y 0) L) (hM : IsSelfDualC B.V₀ M) (h1 : MonoAt B.d L M v) (h2 : PrimAt ψ B.d L v)
    (h3 : LastAt ψ B.d (vecB B.o B.ζ) L M v)
    (hc : ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) v a ∧ NormOneAt v c ∧
      SMoves B.V₀ c (B.o.emb (a₀ * a, 1)) M (coreLat B.d (latS D)) v) :
    ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) v a ∧ NormOneAt v c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) L (latS D) v := by
  obtain ⟨a, c, ha, hc, hm⟩ := hc
  obtain ⟨s1, s2, s3, s4, -, s6⟩ := rows_shape hE hF
  have hl : lam = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) ∨ lam = -((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) := by
    rw [← X.g_eq]; exact hF.sign
  obtain ⟨p1, p2⟩ := GlobalTheory.T.psi_primitive_of_inverseDifferent_lines D ψ hψ _ _ _ B.d (vecB B.o B.ζ) (latS D) _ μ v hF.ne (s6 v) (fun i x hx => by
    rw [s4 v i x hx, GlobalTheory.Core.SBesEx.scl, mul_comm μ, map_mul, mul_assoc, pow_mul_mem_iff hg hl])
  exact ⟨a, c, ha, hc, GlobalTheory.T.sMoves_emb0_of_sMoves_selfDual D ψ _ _ _ B.d (vecB B.o B.ζ) L (latS D) M _ v c _ hL s1 hM
    (GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D X h u ψ _ B μ lam hE hF).2.2 h1 (s3 v) h2 p1 h3 p2 hc (emb_fix _ _ _) hm⟩

theorem loc_level (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) (hM : Formalism.L2.SG.ColDict.LevelMatch X tr hK)
    (hA : B.Adapted tr.wt) (h0 : IsTransportAdelicCorrection tr a₀) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (hp : p.UnitAA) (ϖ : k)
    (hϖ : valuation k (p.pr (incA D ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))) = valuation k ϖ)
    (hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ p.v.asIdeal)
    (hz : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = 1) {L : Lat (D.sp.Y 0)} {N : Lat (D.sp.X 0)}
    (hL : IsSelfDualC (D.sp.Y 0) L) (hN : latV (D.sp.X 0) N (· = p.v) = latV (D.sp.X 0) (lat0 F) (· = p.v))
    (hW : WShape p B.d B.o B.ζ L (fun i => (ϖ ^ (i.1 + 1))⁻¹) (fun i => (ϖ ^ (2 * D.R.rS - i.1 + 1))⁻¹) ((ϖ ^ (D.R.rS + 1))⁻¹)
      1 N) :
    ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p.v a ∧ NormOneAt p.v c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) L (latS D) p.v := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := rows_shape hE hF
  obtain ⟨-, z2, -⟩ := GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D X h u ψ _ B μ lam hE hF
  have hS := GlobalTheory.T.splitPlaceComponent_monomialLattice_splitCore D k p _ _ _ _ _ B.d B.o B.ζ (latS D) _ N (fun i => GlobalTheory.Core.SBesEx.scl μ lam i)
    (fun i => (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹) μ a₀ (s3 _)
    (fun i x hx => by rw [s4 _ i x hx, (GlobalTheory.T.inverseDifferentPow_completion_trivial_at_splitPlace D k p hp _ _).1]) (fun i x hx => by rw [s5 _ i x hx, (GlobalTheory.T.inverseDifferentPow_completion_trivial_at_splitPlace D k p hp _ _).2])
    (s6 _) (GlobalTheory.T.selfDualLattice_splitsOff_unitNormLine_at_place D _ _ _ B.o B.ζ _ μ _ _ B.line s2 hF.ne (s6 _) z2 hT) (rows_trace hE hF hM hA h0 _ hN)
  set f : D.host.E →+* k := p.pr.comp (incA D) with hf
  have hfe : ∀ x, p.pr (incA D x) = f x := fun _ => rfl
  have vg : valuation k (f lam) = valuation k ϖ := by
    rw [← hϖ, ← X.g_eq, hfe]
    rcases hF.sign with hl | hl <;> rw [hl]
    rw [map_neg, Valuation.map_neg]
  have vg' : valuation k (f (star lam)) = valuation k ϖ := by
    rw [← vg]
    rcases hF.sign with hl | hl <;> rw [hl] <;> simp
  have hϖ0 : valuation k ϖ ≠ 0 := by
    rw [← vg]; exact (Valuation.ne_zero_iff _).2 ((map_ne_zero f).2 (lam_ne hF))
  have hμ0 : valuation k (f μ) ≠ 0 := (Valuation.ne_zero_iff _).2 ((map_ne_zero f).2 hF.ne)
  have hμ : valuation k (f (star μ)) = (valuation k (f μ))⁻¹ := by
    have hT' := val_nat p hT
    rw [z2, hfe, map_neg, Valuation.map_neg, map_mul, map_mul, map_mul, map_mul, ← hfe (Nat.cast _), hT', mul_one] at hz
    exact eq_inv_of_mul_eq_one_right hz
  refine GlobalTheory.T.lattices_same_splitShape_carried_by_central D k p _ _ _ _ _ B.d B.o B.ζ L (latS D) N N _ _ _ _ _ _ (ϖ ^ (D.R.rS + 1) * f μ)⁻¹ a₀ B.line hL s1 hW hS rfl
    (inv_ne_zero (mul_ne_zero (pow_ne_zero _ ((Valuation.ne_zero_iff _).1 hϖ0)) ((map_ne_zero f).2 hF.ne))) (fun i => ?_)
    (fun i => ?_) ?_
  · have e : D.R.rS + 1 = (D.R.rS - i.1) + (i.1 + 1) := by have := i.2; omega
    simp only [hfe, GlobalTheory.Core.SBesEx.scl, map_mul, map_pow, map_inv₀, vg]
    rw [e, pow_add _ (D.R.rS - i.1)]
    field_simp
  · have e : 2 * D.R.rS - i.1 + 1 = (D.R.rS - i.1) + (D.R.rS + 1) := by have := i.2; omega
    simp only [hfe, GlobalTheory.Core.SBesEx.scl, star_mul', star_pow, map_mul, map_pow, map_inv₀, vg', hμ]
    rw [e, pow_add _ (D.R.rS - i.1)]
    field_simp
  · simp only [hfe, map_mul, map_pow, map_inv₀]
    field_simp

end Rows

theorem mem_GfC_of_grpAt {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D S} (ha : a ∈ grpAt S P) : a ∈ GfC S := by
  rw [GlobalTheory.Core.Mi.CenAct.mem_GfC_iff]
  ext i j
  have h1 := GlobalTheory.FinPlLoc.infPart_of_idAt ((GlobalTheory.IwaPlace.mem_congGrp_iff S (idAt D P) a).1 ha i j)
  rw [RingHom.map_sub, sub_eq_zero] at h1
  rw [Matrix.map_apply]
  refine Eq.trans h1 ?_
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

theorem conj_mem_grpAt {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D S} (ha : a ∈ grpAt S P) (t : GA D S) :
    t⁻¹ * a * t ∈ grpAt S P := by
  have := (MonoidHom.normal_ker _).conj_mem a ha t⁻¹
  rwa [inv_inv] at this

theorem moves_trans {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {g g' : GA D S} {L M N : Lat S} (h : Moves S g L M P)
    (h' : Moves S g' M N P) : Moves S (g' * g) L N P := by
  intro y hy
  rw [h y hy, h' _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy), Matrix.mulVec_mulVec, GlobalTheory.FinPlLoc.mt_mul]

theorem moves_symm {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S} {L M : Lat S} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  rw [h _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy), Matrix.mulVec_mulVec, ← GlobalTheory.FinPlLoc.mt_mul, mul_inv_cancel, mt_one',
    Matrix.one_mulVec]

theorem moves_conj {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {t : GA D S} {L M : Lat S} (h : Moves S t L M P) (κ : GA D S) :
    Moves S (t⁻¹ * κ * t) L L P ↔ Moves S κ M M P := by
  constructor
  · intro h1
    have := moves_trans (moves_trans (moves_symm h) h1) h
    rwa [show t * (t⁻¹ * κ * t * t⁻¹) = κ by group] at this
  · intro h1
    have := moves_trans (moves_trans h h1) (moves_symm h)
    rwa [← mul_assoc] at this

theorem mem_St_mul {n : ℕ} (g β x : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : x ∈ St (g * β) ↔ g⁻¹ * x * g ∈ St β := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy ⊢
    rw [show x = g * (g⁻¹ * x * g) * g⁻¹ by group, ← hy]
    group

section Chain

variable {u : D.what₂.Word} {d : GlobalTheory.SeeSaw.Dat D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1)
  (F : Formalism.L2.Forms.Forms0 D u)

def ChainFacts (L : Lat (D.sp.Y 0)) (b : GlobalTheory.SeeSaw.BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS) : Prop :=
  ∃ M : Lat b.V₀,
    (∀ v, v ∉ d.c.S → IsSelfDualC b.V₀ M ∧ MonoAt b.d L M v ∧ PrimAt d.c.ψ b.d L v ∧ LastAt d.c.ψ b.d (vecB b.o b.ζ) L M v) ∧
    (∀ v, v ∉ d.c.S → ¬ o.atT v → ∃ LL, IsSelfDualC b.L LL ∧ OrthAt b.o M (d.x 0).L LL v) ∧
    (∀ i, ∃ β₀ : GlobalTheory.FinPl.Frame (o.p i) b.V₀ (Fin (D.sp.X 0).rank ⊕ Fin 1), IsSumFrame b.o b.ζ (o.β 0 i) β₀ ∧
      β₀.IsLat M (GlobalTheory.LatPair.gluedS o.q 1 (o.Q 0 i).ker (o.Q 0 i).vec)) ∧
    (∀ PP, valuation (G PP).k ((G PP).q.pr (incA D (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ))) = 1 ∧
      WShape (G PP).q b.d b.o b.ζ L (fun i => ((((G PP).S.ϖ : (G PP).kˣ) : (G PP).k) ^ (i.1 + 1))⁻¹)
        (fun i => ((((G PP).S.ϖ : (G PP).kˣ) : (G PP).k) ^ (2 * D.R.rS - i.1 + 1))⁻¹)
        (((((G PP).S.ϖ : (G PP).kˣ) : (G PP).k) ^ (D.R.rS + 1))⁻¹) 1 (d.x 0).L) ∧
    ∀ v, v ∉ d.c.S → ∀ a ∈ grpAt (D.sp.X 0) (· = v), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = y.1.1 →
      ((y : GL _ _) ∈ F.cls0.lev.U ↔ Moves (D.sp.Y 0) (embA b.d b.o a) L L (· = v))

end Chain

def toBes {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) : GlobalTheory.SeeSaw.BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS :=
  ⟨B.V₀, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vN⟩

theorem eq_toBes {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) (b : GlobalTheory.SeeSaw.BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (v : Vol (D.sp.X 0)) (e : B.lev = b.lev v) : b = toBes B := by
  obtain ⟨V₀, L, dd, o, ζ, line, cpt, vN⟩ := b
  obtain ⟨V₀', L', dd', o', ζ', line', cpt', vA', vN', t1, t2, t3⟩ := B
  cases e
  rfl

theorem stab_read (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (latS D)) (κ : GA D (D.sp.Y 0)) :
    ((iotaX X h κ).1 = 1 ↔ κ ∈ GfC (D.sp.Y 0)) ∧ ((iotaX X h κ).2 ∈ X.B.I.Kset ↔ finE (D.sp.Y 0) κ ∈ St β) :=
  ⟨(GlobalTheory.SeeConjReadIota.read_iota X h β hβ κ).1, (GlobalTheory.SeeConjReadIota.read_iota X h β hβ κ).2.1⟩

theorem kset_conj (I : AutInst) {x : I.Gf} (hx : x ∈ I.Kset) (y : I.Gf) : x * y * x⁻¹ ∈ I.Kset ↔ y ∈ I.Kset := by
  have hm : ∀ {a b : I.Gf}, a ∈ I.Kset → b ∈ I.Kset → a * b ∈ I.Kset := fun {a b} ha hb => by
    show ((a * b : I.Gf) : GL _ _) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_mul]
    exact mul_mem ha hb
  have hi : ∀ {a : I.Gf}, a ∈ I.Kset → a⁻¹ ∈ I.Kset := fun {a} ha => by
    show ((a⁻¹ : I.Gf) : GL _ _) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_inv]
    exact inv_mem ha
  refine ⟨fun h => ?_, fun h => hm (hm hx h) (hi hx)⟩
  have := hm (hm (hi hx) h) hx
  rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this

theorem stab_of_frame (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word)
    (β : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) (g t z : GA D (D.sp.Y 0))
    (hz : z ∈ Subgroup.center (GA D (D.sp.Y 0))) (hβ : Formalism.L2.DIV.IsFrame (finE (D.sp.Y 0) (z * g * t) * β) (latS D))
    (κ : GA D (D.sp.Y 0)) :
    (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX X h).symm (1, X.xu u))⁻¹ * g * t) * β)) ↔
      ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset) := by
  have hR := stab_read X h _ hβ
  have e3 : (iotaX X h ((iotaX X h).symm (1, X.xu u) * κ * ((iotaX X h).symm (1, X.xu u))⁻¹)).2 =
      X.xu u * (iotaX X h κ).2 * (X.xu u)⁻¹ := by
    rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]
    rfl
  generalize (iotaX X h).symm (1, X.xu u) = x at e3 ⊢
  have e1 : finE (D.sp.Y 0) (x⁻¹ * g * t) * β = finE (D.sp.Y 0) (z * x)⁻¹ * (finE (D.sp.Y 0) (z * g * t) * β) := by
    have e0 : (z * x)⁻¹ * (z * g * t) = x⁻¹ * g * t := by group
    rw [← mul_assoc, ← map_mul, e0]
  have e2 : (finE (D.sp.Y 0) (z * x)⁻¹)⁻¹ * finE (D.sp.Y 0) κ * finE (D.sp.Y 0) (z * x)⁻¹ = finE (D.sp.Y 0) (x * κ * x⁻¹) := by
    have := Subgroup.mem_center_iff.1 hz (x * κ * x⁻¹)
    have e0 : z * x * κ * (z * x)⁻¹ = x * κ * x⁻¹ :=
      calc z * x * κ * (z * x)⁻¹ = z * (x * κ * x⁻¹) * z⁻¹ := by group
        _ = x * κ * x⁻¹ := by rw [← this]; group
    rw [← map_inv, ← map_mul, ← map_mul, inv_inv, e0]
  rw [e1, mem_St_mul, e2, ← (hR _).2, e3, kset_conj _ (X.xu_K u), (hR κ).1]


end GlobalTheory.Core.Mi.LatMatch

end
