module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUnitaryStabilizesSelfDualLatticeIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUnitaryStabilizesSelfDualLatticeIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl.FrameLat

theorem moves_iff_smul_eq : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n) (L : GlobalTheory.FinPl.Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → β.IsLat L Λ → ∀ (κ : GA D S) (g : GL n k), (mt S κ).map p.pr = β.b * g.val * β.b' → (GlobalTheory.FinPl.Moves S κ L L (· = p.v) ↔ g • Λ = Λ) := by
  intro D k _ _ _ _ p S n _ _ β L Λ hL hΛ κ g hg
  have hsec : ∀ u : Fin S.rank → k, mt S κ *ᵥ (fun i => p.sec (u i)) =
      fun i => p.sec (((β.b * g.val * β.b') *ᵥ u) i) := by
    intro u
    funext i
    rw [← hg]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]
  have key : ∀ x : n → k, mt S κ *ᵥ (fun i => p.sec ((β.b *ᵥ x) i)) =
      fun i => p.sec ((β.b *ᵥ (g.val *ᵥ x)) i) := by
    intro x
    rw [hsec, Matrix.mulVec_mulVec, Matrix.mul_assoc, β.b'b, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  constructor
  · intro hm
    have hiff : ∀ x, x ∈ Λ ↔ g • x ∈ Λ := by
      intro x
      rw [hΛ, hΛ]
      change _ ∈ latV S L _ ↔ (fun i => p.sec ((β.b *ᵥ (g.val *ᵥ x)) i)) ∈ latV S L _
      rw [hm _ (fun i => sec_mem_idAt p _), key]
    ext x
    rw [GlobalTheory.LatPair.mem_smul_iff, hiff, smul_inv_smul]
  · intro hgΛ
    have hinv : ∀ x, g • x ∈ Λ ↔ x ∈ Λ := by
      intro x
      conv_lhs => rw [← hgΛ]
      rw [GlobalTheory.LatPair.mem_smul_iff, inv_smul_smul]
    have hE : ∀ u : Fin S.rank → k, (fun i => p.sec (u i)) ∈ latV S L (· = p.v) ↔
        (fun i => p.sec (((β.b * g.val * β.b') *ᵥ u) i)) ∈ latV S L (· = p.v) := by
      intro u
      have hu : u = β.b *ᵥ (β.b' *ᵥ u) := by rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
      have hAu : (β.b * g.val * β.b') *ᵥ u = β.b *ᵥ (g.val *ᵥ (β.b' *ᵥ u)) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      have h := hinv (β.b' *ᵥ u)
      rw [hΛ, hΛ] at h
      change (fun i => p.sec ((β.b *ᵥ (g.val *ᵥ (β.b' *ᵥ u))) i)) ∈ latV S L _ ↔
        (fun i => p.sec ((β.b *ᵥ (β.b' *ᵥ u)) i)) ∈ latV S L _ at h
      rw [← hu, ← hAu] at h
      exact h.symm
    have hAA : ∀ x : Fin S.rank → k, (β.b * g.val * β.b') *ᵥ ((β.b * (g⁻¹).val * β.b') *ᵥ x) = x := by
      intro x
      rw [Matrix.mulVec_mulVec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc β.b' β.b, β.b'b, Matrix.one_mul, ← Matrix.mul_assoc g.val, Units.mul_inv,
        Matrix.one_mul, β.bb', Matrix.one_mulVec]
    have hunit : ∀ x z : Fin S.rank → k,
        ∑ i, ∑ j, ((β.b * g.val * β.b') *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) *
          (((mt S κ).map (fun a => p.pr (cA D a))) *ᵥ z) j =
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j := by
      intro x z
      have h := pairing_inv (p := p) κ x z
      rwa [hg] at h
    have hC : ∀ z : Fin S.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) ↔
        (fun i => cA D (p.sec ((((mt S κ).map (fun a => p.pr (cA D a))) *ᵥ z) i))) ∈ latV S L (· = p.v) := by
      intro z
      rw [csec_mem_iff hL, csec_mem_iff hL]
      constructor
      · intro h x hx
        have hx' : (fun i => p.sec (((β.b * (g⁻¹).val * β.b') *ᵥ x) i)) ∈ latV S L (· = p.v) := by
          rw [hE, hAA]; exact hx
        have h2 := hunit ((β.b * (g⁻¹).val * β.b') *ᵥ x) z
        rw [hAA] at h2
        rw [h2]; exact h _ hx'
      · intro h x hx
        rw [← hunit x z]; exact h _ ((hE x).1 hx)
    intro y hy
    have hyd : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
      funext i
      simp only [Pi.add_apply, p.sec_pr]
      rw [map_mul, Formalism.L2.Theta.cA_cA, ← add_mul]
      exact ((idem_iff p _).1 (hy i)).symm
    obtain ⟨u, z, rfl⟩ : ∃ u z : Fin S.rank → k, y = (fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))) :=
      ⟨_, _, hyd⟩
    rw [Matrix.mulVec_add, hsec u, mt_csec κ z, decomp hL, decomp hL, hE u, hC z]

end GlobalTheory.FinPl.FrameLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUnitaryStabilizesSelfDualLatticeIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_unitary_stabilizes_selfDual_lattice_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n) (L : GlobalTheory.FinPl.Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → β.IsLat L Λ → ∀ (κ : GA D S) (g : GL n k), (mt S κ).map p.pr = β.b * g.val * β.b' → (GlobalTheory.FinPl.Moves S κ L L (· = p.v) ↔ g • Λ = Λ) := by
  first | exact @GlobalTheory.FinPl.FrameLat.moves_iff_smul_eq | exact GlobalTheory.FinPl.FrameLat.moves_iff_smul_eq | (intros; apply GlobalTheory.FinPl.FrameLat.moves_iff_smul_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBesselCoreMatrixEqBlockDiagonalOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBesselCoreMatrixEqBlockDiagonalOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl.CoreMat

theorem mt_emb_mulVec_ratV_vecB {D : D7} {ρ : ℕ} (B : BesLev D ρ) (κ : GA D B.A) :
    Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1)) *ᵥ ratV (vecB B.o B.ζ) =
      ratV (vecB B.o B.ζ) := by
  have hv : ratV (vecB B.o B.ζ) = B.o.jB *ᵥ ratV B.ζ :=
    funext fun i => RingHom.map_mulVec (incA D) B.o.iB B.ζ i
  have hB : Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1)) ⬝ B.o.jB = B.o.jB := by
    rw [B.o.emb_jB]
    have h1 : Formalism.L2.Theta.mt B.L (1 : GA D B.L) = 1 := by simp [Formalism.L2.Theta.mt]
    rw [h1, Matrix.mul_one]
  rw [hv, Matrix.mulVec_mulVec, hB]

theorem coreMat : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n]
    [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (β : GlobalTheory.FinPl.Frame p B.A n)
    (β₀ : GlobalTheory.FinPl.Frame p B.V₀ (n ⊕ Fin 1)),
    GlobalTheory.FinPl.IsSumFrame B.o B.ζ β β₀ → ∀ (κ : GA D B.A) (g : GL n k),
    (Formalism.L2.Theta.mt B.A κ).map p.pr = β.b * g.val * β.b' →
    (Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1))).map p.pr =
      β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by
  intro D k _ _ _ _ p n _ _ ρ B β β₀ hS κ g hg
  have hA : Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1)) ⬝ B.o.jA =
      B.o.jA ⬝ Formalism.L2.Theta.mt B.A κ := B.o.emb_jA κ 1
  have hv := mt_emb_mulVec_ratV_vecB B κ
  have key : (Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1))).map p.pr * β₀.b =
      β₀.b * (GlobalTheory.RootEx.embX 1 g).val := by
    rw [hS]
    have hX : ((GlobalTheory.RootEx.embX 1 g).val : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k) = fromBlocks g.val 0 0 1 := rfl
    rw [hX]
    rw [Matrix.mul_fromCols, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, Matrix.mul_zero, zero_add,
      Matrix.mul_one]
    congr 1
    · rw [← Matrix.mul_assoc, ← Matrix.map_mul, hA, Matrix.map_mul, Matrix.mul_assoc, hg, Matrix.mul_assoc,
        Matrix.mul_assoc, Matrix.mul_assoc, β.b'b, Matrix.mul_one]
    · ext i j
      have := congrFun hv i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, replicateCol_apply, Matrix.map_apply, ← map_mul, ← map_sum]
      rw [← this]
      rfl
  calc (Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1))).map p.pr
      = (Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1))).map p.pr * β₀.b * β₀.b' := by
        rw [Matrix.mul_assoc, β₀.bb', Matrix.mul_one]
    _ = β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by rw [key]

end GlobalTheory.FinPl.CoreMat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBesselCoreMatrixEqBlockDiagonalOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_besselCore_matrix_eq_blockDiagonal_one : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (β : GlobalTheory.FinPl.Frame p B.A n) (β₀ : GlobalTheory.FinPl.Frame p B.V₀ (n ⊕ Fin 1)), GlobalTheory.FinPl.IsSumFrame B.o B.ζ β β₀ → ∀ (κ : GA D B.A) (g : GL n k), (mt B.A κ).map p.pr = β.b * g.val * β.b' → (mt B.V₀ (B.o.emb (κ, 1))).map p.pr = β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by
  first | exact @GlobalTheory.FinPl.CoreMat.coreMat | exact GlobalTheory.FinPl.CoreMat.coreMat | (intros; apply GlobalTheory.FinPl.CoreMat.coreMat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionIffForallPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionIffForallPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPlMovesLoc

variable {D : D7}

theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ w, Q w → P w) {a : AE D} (ha : a ∈ idAt D Q) : a ∈ idAt D P := by
  unfold idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  refine Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 hw ⟨w.1, fun hq => w.2 (h _ hq)⟩

theorem latV_mono {S : HSp D} {L : Lat S} {P Q : Pl D → Prop} (h : ∀ w, Q w → P w) {y : Fin S.rank → AE D}
    (hy : y ∈ GlobalTheory.FinPl.latV S L Q) : y ∈ GlobalTheory.FinPl.latV S L P := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy ⊢
  refine AddSubgroup.closure_mono ?_ hy
  rintro z ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  exact ⟨α, hαi, fun w hw => hα w (fun hq => hw (h w hq)), a, ha, x, hx, rfl⟩

theorem mulVec_idAt {S : HSp D} (g : GA D S) {Q : Pl D → Prop} {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D Q) :
    ∀ i, (mt S g *ᵥ y) i ∈ idAt D Q := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem latV_at_iff {S : HSp D} {L : Lat S} {P : Pl D → Prop} {v : Pl D} (hv : P v) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D (· = v)) : y ∈ GlobalTheory.FinPl.latV S L (· = v) ↔ y ∈ GlobalTheory.FinPl.latV S L P := by
  constructor
  · exact latV_mono (fun w hw => hw ▸ hv)
  · intro h
    have h1 := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt (· = v)) h
    have h2 : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy i)
    rwa [h2] at h1

theorem moves_iff : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S), Submodule.IsLattice D.host.E L →
    ∀ (P : GlobalTheory.FinPl.Pl D → Prop), GlobalTheory.FinPl.Moves S g L L P ↔ ∀ v, P v → GlobalTheory.FinPl.Moves S g L L (· = v) := by
  intro D S g L hL P
  constructor
  · intro hM v hv y hy
    have hyP : ∀ i, y i ∈ idAt D P := fun i => idAt_mono (fun w hw => hw ▸ hv) (hy i)
    rw [latV_at_iff hv hy, latV_at_iff hv (mulVec_idAt g hy)]
    exact hM y hyP
  · intro hM y hy
    rw [GlobalTheory.FinPlLoc.part_lat P S L y hL, GlobalTheory.FinPlLoc.part_lat P S L _ hL]
    have hsupp : ∀ v, ∀ e ∈ intAt D (· = v), ∀ i, (e • y) i ∈ idAt D (· = v) := fun v e he i => by
      rw [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ he.1
    have hcomm : ∀ e : AE D, e • (mt S g *ᵥ y) = mt S g *ᵥ (e • y) := fun e => (Matrix.mulVec_smul _ _ _).symm
    constructor
    · rintro ⟨-, h⟩
      refine ⟨mulVec_idAt g hy, fun v hv e he => ?_⟩
      rw [hcomm]
      exact (hM v hv (e • y) (hsupp v e he)).1 (h v hv e he)
    · rintro ⟨-, h⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      refine (hM v hv (e • y) (hsupp v e he)).2 ?_
      rw [← hcomm]
      exact h v hv e he

end GlobalTheory.FinPlMovesLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionIffForallPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesLatticeCompletion_iff_forall_place : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S), Submodule.IsLattice D.host.E L → ∀ (P : GlobalTheory.FinPl.Pl D → Prop), GlobalTheory.FinPl.Moves S g L L P ↔ ∀ v, P v → GlobalTheory.FinPl.Moves S g L L (· = v) := by
  first | exact @GlobalTheory.FinPlMovesLoc.moves_iff | exact GlobalTheory.FinPlMovesLoc.moves_iff | (intros; apply GlobalTheory.FinPlMovesLoc.moves_iff <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffTrace
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

theorem supp_mulVec' {D : D7} {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) {I : Ideal (AE D)} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (i : Fin m) : (X *ᵥ y) i ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem colMul_zero' {D : D7} {m n : ℕ} (x : Mx D m n) (i : Fin n) : colMul x i 0 = 0 := by
  funext r; simp [colMul]

theorem glued_stab_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (g : GL n k) :
    GlobalTheory.RootEx.embX 1 g • gluedS q 1 P.ker P.vec = gluedS q 1 P.ker P.vec ↔ g • P = P := by
  rw [GlobalTheory.LevelUnfold.embX_smul_gluedS, Pair.smul_eq_iff P.hasVal_vec]
  constructor
  · intro h
    have h1 : g • P.ker = P.ker := by
      have := GlobalTheory.LevelUnfold.interX_gluedS (q := q) (le_refl 1) (g • P.ker) (g • P.vec)
      rw [h, GlobalTheory.LevelUnfold.interX_gluedS (le_refl 1)] at this
      exact this.symm
    refine ⟨h1, ?_⟩
    have h2 := GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := 1) (g • P.ker) (g • P.vec)
    rw [h] at h2
    exact (GlobalTheory.LevelUnfold.glue_mem_gluedS_iff (le_refl 1)).1 h2
  · rintro ⟨h1, h2⟩
    rw [h1]
    exact GlobalTheory.LevelUnfold.gluedS_congr h2

theorem moves_emb_iff {D : D7} {S A B : HSp D} (o : OrthDec S A B) (M : GlobalTheory.FinPl.Lat S) (LA : GlobalTheory.FinPl.Lat A)
    (LB : GlobalTheory.FinPl.Lat B) (v : GlobalTheory.FinPl.Pl D) (h : GlobalTheory.FinPl.OrthAt o M LA LB v) (κ : GA D A) :
    GlobalTheory.FinPl.Moves S (o.emb (κ, 1)) M M (· = v) ↔ GlobalTheory.FinPl.Moves A κ LA LA (· = v) := by
  have e1 : ∀ y, o.pA *ᵥ (Formalism.L2.Theta.mt S (o.emb (κ, 1)) *ᵥ y) = Formalism.L2.Theta.mt A κ *ᵥ (o.pA *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; congr 1; exact o.pA_emb κ 1
  have e2 : ∀ y, o.pB *ᵥ (Formalism.L2.Theta.mt S (o.emb (κ, 1)) *ᵥ y) = o.pB *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, o.pB_emb]; simp [Formalism.L2.Theta.mt]
  constructor
  · intro hM yA hyA
    have hy : ∀ i, (o.jA *ᵥ yA) i ∈ idAt D (· = v) := supp_mulVec' _ hyA
    have hA1 : o.pA *ᵥ (o.jA *ᵥ yA) = yA := by rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]
    have hB1 : o.pB *ᵥ (o.jA *ᵥ yA) = 0 := by rw [Matrix.mulVec_mulVec, o.pB_jA, Matrix.zero_mulVec]
    have := hM _ hy
    rw [h, h, e1, e2, hA1, hB1] at this
    simpa only [zero_mem, and_true] using this
  · intro hA y hy
    rw [h, h, e1, e2, ← hA _ (supp_mulVec' _ hy)]

theorem carriesLattice_wittEmbedding_iff_core {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (N : GlobalTheory.FinPl.Lat S) (M : GlobalTheory.FinPl.Lat S₀)
    (v : GlobalTheory.FinPl.Pl D) (h : GlobalTheory.FinPl.MonoAt d N M v) (g : GA D S₀) :
    GlobalTheory.FinPl.Moves S (d.emb0 g) N N (· = v) ↔ GlobalTheory.FinPl.Moves S₀ g M M (· = v) := by
  have eX : ∀ y, d.pX *ᵥ (Formalism.L2.Theta.mt S (d.emb0 g) *ᵥ y) = d.pX *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
  have eY : ∀ y, d.pY *ᵥ (Formalism.L2.Theta.mt S (d.emb0 g) *ᵥ y) = d.pY *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
  have e0 : ∀ y, d.p0 *ᵥ (Formalism.L2.Theta.mt S (d.emb0 g) *ᵥ y) = Formalism.L2.Theta.mt S₀ g *ᵥ (d.p0 *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; congr 1; exact d.wittDecomp_projAnisotropic_anisotropicEmbedding g
  constructor
  · intro hM y₀ hy₀
    have hy : ∀ i, (d.j0 *ᵥ y₀) i ∈ idAt D (· = v) := supp_mulVec' _ hy₀
    have hX1 : d.pX *ᵥ (d.j0 *ᵥ y₀) = 0 := by rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
    have hY1 : d.pY *ᵥ (d.j0 *ᵥ y₀) = 0 := by rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
    have h01 : d.p0 *ᵥ (d.j0 *ᵥ y₀) = y₀ := by rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
    have := hM _ hy
    rw [h, h, eX, eY, e0, hX1, hY1, h01] at this
    simpa only [Pi.zero_apply, colMul_zero', zero_mem, true_and, implies_true] using this
  · intro hA y hy
    rw [h, h, eX, eY, e0, ← hA _ (supp_mulVec' _ hy)]

theorem exists_gl_frame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n)
    (κ : GA D S) : ∃ g : GL n k, (mt S κ).map p.pr = β.b * g.val * β.b' := by
  have e1 : mt S κ * mt S κ⁻¹ = 1 := by
    rw [show mt S κ * mt S κ⁻¹ = mt S (κ * κ⁻¹) from rfl, mul_inv_cancel]; rfl
  have e2 : mt S κ⁻¹ * mt S κ = 1 := by
    rw [show mt S κ⁻¹ * mt S κ = mt S (κ⁻¹ * κ) from rfl, inv_mul_cancel]; rfl
  have hM : (mt S κ).map p.pr * (mt S κ⁻¹).map p.pr = 1 := by
    rw [← Matrix.map_mul, e1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM' : (mt S κ⁻¹).map p.pr * (mt S κ).map p.pr = 1 := by
    rw [← Matrix.map_mul, e2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨β.b' * (mt S κ).map p.pr * β.b, β.b' * (mt S κ⁻¹).map p.pr * β.b, ?_, ?_⟩, ?_⟩
  · calc β.b' * (mt S κ).map p.pr * β.b * (β.b' * (mt S κ⁻¹).map p.pr * β.b)
          = β.b' * ((mt S κ).map p.pr * (β.b * β.b') * (mt S κ⁻¹).map p.pr) * β.b := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [β.bb', Matrix.mul_one, hM, Matrix.mul_one, β.b'b]
  · calc β.b' * (mt S κ⁻¹).map p.pr * β.b * (β.b' * (mt S κ).map p.pr * β.b)
          = β.b' * ((mt S κ⁻¹).map p.pr * (β.b * β.b') * (mt S κ).map p.pr) * β.b := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [β.bb', Matrix.mul_one, hM', Matrix.mul_one, β.b'b]
  · show _ = β.b * (β.b' * (mt S κ).map p.pr * β.b) * β.b'
    calc (mt S κ).map p.pr = (β.b * β.b') * (mt S κ).map p.pr * (β.b * β.b') := by
          rw [β.bb', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.OffTrace
