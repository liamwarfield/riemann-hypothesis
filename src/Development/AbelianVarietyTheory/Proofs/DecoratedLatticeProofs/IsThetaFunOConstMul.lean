module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.DoubledUnramifiedFrames
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOConstMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastSeeSaw

variable {D : D7}

theorem isThetaFunO_const_mul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (fun w => c * f w) := {
  quasi γ w := by
    show c * f (ratW T S γ + w) = _ * (c * f w)
    rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (hk u hu h0) w
    simp only [heisO] at e ⊢
    rw [← e]; ring
  cont := continuous_const.mul hf.cont
  smooth n L hL h0 w := contDiff_const.mul (hf.smooth n L hL h0 w) }

theorem isThetaFunO_kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ}
    {f : WO L S → ℂ} (hf : IsThetaFunO ψ L S f) : IsThetaFunO ψ S L'' (fun w => f (kap τ S w)) := by
  obtain ⟨hadd, hcont, hrat, -, hsym, hpart⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) (by simpa using hτ)
    (kap τ S) (fun _ => rfl)
  have hsH : ∀ x y, symplOH L S (kap τ S x) (kap τ S y) = symplOH S L'' x y := fun x y => by
    simp only [symplOH, hsym]; push_cast; ring
  let K : WO S L'' →+ WO L S := AddMonoidHom.mk' (kap τ S) hadd
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hcont, fun n M hM h0 w => ?_⟩
  · obtain ⟨γ', hγ'⟩ := hrat (ratW L'' S γ) (by rw [ratW_eq]; exact rat_mem _)
    show f (kap τ S (ratW L'' S γ + w)) = _
    have e : ratW S L γ' = kap τ S (ratW L'' S γ) := hγ'
    rw [hadd, ← e, hf.quasi, e, hsH]
  · obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U.comap K, hU.preimage hcont, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (hk (kap τ S u) hu ((hpart u).1 h0)) (kap τ S w)
    simp only [heisO] at e ⊢
    rw [hadd, ← hsH]
    exact e
  · have := hf.smooth n (K.comp M) (hcont.comp hM) (fun t => (hpart (M t)).2 (h0 t)) (kap τ S w)
    simp only [hadd]
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, K] using this

end GlobalTheory.LastSeeSaw
end

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LastSeeSaw

end GlobalTheory.LastSeeSaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionFunctionIncZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Isom

namespace GlobalTheory.OverTgt

variable {D : D7}

def colRow (S T : HSp D) (r : Fin S.rank → AE D) : (Fin T.rank → AE D) →+ WO S T where
  toFun y := Matrix.of fun i j => y i * r j
  map_zero' := by ext i j; simp
  map_add' y y' := by ext i j; simp [add_mul]

theorem mul_colRow {S T T' : HSp D} (M : Mx D T'.rank T.rank) (r : Fin S.rank → AE D) (y : Fin T.rank → AE D) :
    HMul.hMul M (colRow S T r y) = colRow S T' r (M *ᵥ y) := by
  ext i j
  simp [colRow, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem gen_eq_colRow {S T : HSp D} (α : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      colRow S T (fun j => incA D (a * ∑ k, star (s k) * S.gram k j)) (fun i => α ⊗ₜ[D.host.F] (1 * t i)) := by
  ext i j
  simp only [colRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply]
  change _ = (α ⊗ₜ[D.host.F] (1 * t i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  ring

theorem colRow_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ LS) {y : Fin T.rank → AE D}
    (hy : y ∈ latV T LT P) :
    colRow S T (fun j => incA D (a * ∑ k, star (s k) * S.gram k j)) y ∈ latO S T LS (LT : Set _) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [← gen_eq_colRow]
    exact AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, s, hs, x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [map_add]; exact add_mem hz hz'
  | neg z _ hz => rw [map_neg]; exact neg_mem hz

theorem mul_mem_latO {S T T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {LT' : Lat T'}
    {P : GlobalTheory.FinPl.Pl D → Prop} (M : Mx D T'.rank T.rank) (hM : ∀ y ∈ latV T LT P, M *ᵥ y ∈ latV T' LT' P) {w : WO S T}
    (hw : w ∈ latO S T LS (LT : Set _) P) : HMul.hMul M w ∈ latO S T' LS (LT' : Set _) P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hz
    rw [gen_eq_colRow, mul_colRow]
    exact colRow_mem_latO ha hs (hM _ (AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, t, ht, rfl⟩))
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mul_neg]; exact neg_mem hz

section Isometry

variable {V V' : HSp D} (I : IsoMat V V') (S : HSp D)

variable {Λ : AddSubgroup (WO S V)} {Λ' : AddSubgroup (WO S V')} (hΛ : ∀ u, u ∈ Λ ↔ I.phi S u ∈ Λ')
include hΛ

end Isometry

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S T T₀ : HSp D} (d : HypDec T T₀ 0) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  (α : GlobalTheory.FinPl.Frame p S n') (β : GlobalTheory.FinPl.Frame p T n) (β₀ : GlobalTheory.FinPl.Frame p T₀ n)

end Frames

end GlobalTheory.OverTgt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfAnnihilatorMemCompletedHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfAnnihilatorMemCompletedHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitVacAnnih

open GlobalTheory.FinPl.FrameLat

theorem trace_rankOne {k m n Y Y' : Type} [Field k] [Fintype m] [DecidableEq m] [Fintype n] [Fintype Y] [Fintype Y']
    (A G : Matrix m m k) (hAG : G * A = 1) (N : Matrix m n k) (B : Matrix n n k) (βT : Matrix n Y k) (βS : Matrix m Y' k)
    (γS : Matrix Y' m k) (hS : βS * γS = 1) (c : Y → k) (x : m → k) :
    Matrix.trace (A * N * B * (βT * vecMulVec c ((x ᵥ* G) ᵥ* βS) * γS)) = x ⬝ᵥ (N * B) *ᵥ (βT *ᵥ c) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hS,
    Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc A, ← Matrix.mul_assoc G, hAG, Matrix.one_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem int_of_char {ψk : AddChar k Circle} (h : HasConductor ψk 1) {b : k} (hb : ∀ a ∈ 𝒪[k], ψk (a * b) = 1) :
    b ∈ 𝒪[k] := by
  by_cases h0 : b = 0
  · rw [h0]; exact zero_mem _
  have h1 := (h b).1 fun t ht => by
    have := hb (t / b) (by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ ht zero_le)
    rwa [div_mul_cancel₀ _ h0] at this
  rw [Valuation.mem_integer_iff]
  simpa using h1

theorem annihilator_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ y : WO S T, IsHalf (cA D q.e) y → (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) → y ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hS hT hFS hFT ψ ψk _ hχ hc y hy hann
  have hce : cA D q.e ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
    rw [← sec_one q]
    exact ⟨csec_mem_idAt 1, (cA_int_iff _).2 (sec_mem_intAt q 1 (one_mem _)).2⟩
  have hcs : ∀ a : AE D, cA D (q.sec (q.pr (cA D a))) = cA D q.e * a := fun a => by
    rw [q.sec_pr, RingHom.map_mul, GlobalTheory.LocSympl.conj_conj]
  have hgram : ∀ (V : HSp D) i j, q.pr (cA D (incA D (V.gram i j))) = (V.gram.map (q.pr.comp (incA D))) j i :=
    fun V i j => by rw [cA_incA, GlobalTheory.LatVac.gram_star]; rfl
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, hU.2 T LT]
  refine ⟨fun i j => ?_, fun x hx => ?_⟩
  · rw [← hy i j]
    exact Ideal.mul_mem_right _ _ hce.1
  set N : Matrix (Fin S.rank) (Fin T.rank) k := Matrix.of fun b c => q.pr (cA D (y c b)) with hN
  set x' : Fin S.rank → k := fun j => q.pr (cA D (x j)) with hx'
  have hyN : y = N.transpose.map fun a => cA D ((ofSplit q).ι a) := by
    ext i j
    exact ((hcs _).trans (hy i j)).symm
  have hx1 : (fun j => cA D (q.sec (x' j))) ∈ GlobalTheory.FinPl.latV S LS (· = q.v) := by
    have := smul_mem hS hx hce
    convert this using 1
    funext j
    exact hcs _
  have hyx : (y : Matrix _ _ (AE D)) *ᵥ x = fun i => cA D (q.sec ((x' ᵥ* N) i)) := by
    funext i
    have : (x' ᵥ* N) i = q.pr (cA D (((y : Matrix _ _ (AE D)) *ᵥ x) i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, RingHom.map_mul, hN, hx', Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this, hcs]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, hy i j]
  show (y : Matrix _ _ (AE D)) *ᵥ x ∈ _
  rw [hyx, csec_mem_iff hT]
  intro u hu
  have huc : FT.β *ᵥ (FT.γ *ᵥ u) = u := by rw [Matrix.mulVec_mulVec, FT.βγ, Matrix.one_mulVec]
  have hcint : ∀ i, (FT.γ *ᵥ u) i ∈ 𝒪[k] := (hFT _).2 (by rw [huc]; exact hu)
  set f := q.pr.comp (incA D) with hf
  have hrow : ∀ s, ((x' ᵥ* S.gram.map f) ᵥ* FS.β) s ∈ 𝒪[k] := fun s => by
    have h1 := (csec_mem_iff hS x').1 hx1 _ ((hFS (Pi.single s 1)).1 fun i => by
      by_cases h : i = s
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
    convert h1 using 1
    simp only [hgram, Matrix.mulVec_single_one, Matrix.vecMul, dotProduct, Finset.sum_mul, Matrix.col, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine int_of_char hc fun a ha => ?_
  have h2 := hann (vecMulVec (a • (FT.γ *ᵥ u)) ((x' ᵥ* S.gram.map f) ᵥ* FS.β)) fun r s =>
    mul_mem (mul_mem ha (hcint r)) (hrow s)
  have hA : S.gram.map f * (S.gram⁻¹).map f = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero f) (map_one f)]
  rw [GlobalTheory.LocSympl.psi_sympl_up _ FS FT ψ ψk hχ, hyN, GlobalTheory.LocSympl.pi_hO_up] at h2
  have h3 := trace_rankOne _ _ hA N (T.gram.map f) FT.β FS.β FS.γ FS.βγ (a • (FT.γ *ᵥ u)) x'
  rw [Matrix.mulVec_smul, huc, Matrix.mulVec_smul, dotProduct_smul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec] at h3
  have h4 : ∑ i, ∑ j, u i * q.pr (cA D (incA D (T.gram i j))) * (x' ᵥ* N) j = (x' ᵥ* N) ⬝ᵥ T.gram.map f *ᵥ u := by
    rw [Finset.sum_comm]
    simp only [hgram, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h4, ← smul_eq_mul, ← h3]
  exact Circle.ext h2

end GlobalTheory.SplitVacAnnih

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfAnnihilatorMemCompletedHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_half_annihilator_mem_completed_hom_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ y : WO S T, IsHalf (cA D q.e) y → (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) → y ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  first | exact @GlobalTheory.SplitVacAnnih.annihilator_mem_latO | exact GlobalTheory.SplitVacAnnih.annihilator_mem_latO | (intros; apply GlobalTheory.SplitVacAnnih.annihilator_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFrameCol
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaModel

def finv {k : Type} [Field k] [MeasurableSpace k] {n : Type} [Fintype n] (ψk : AddChar k Circle) (ν : Measure k) (C : ℂ)
    (Φ : Matrix Unit n k → ℂ) (x : Matrix n Unit k) : ℂ :=
  C * ∫ η : n → k, Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ) ∂(Measure.pi fun _ => ν)

end GlobalTheory.KappaModel

namespace GlobalTheory.KappaModel
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem integrable_row (ψk : AddChar k Circle) (hψ : Continuous ψk) (ν : Measure k) [ν.IsAddHaarMeasure]
    {Φ : Matrix Unit n k → ℂ} (hΦ : Φ ∈ SB (Matrix Unit n k)) (x : Matrix n Unit k) :
    Integrable (fun η : n → k => Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ)) (Measure.pi fun _ => ν) := by
  have := secondCountable k
  have := t2Space k
  let e : (n → k) ≃ₜ Matrix Unit n k :=
    { toFun := fun η => Matrix.of fun _ r => η r
      invFun := fun M => M ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h1 : Continuous fun η : n → k => Φ (Matrix.of fun _ r => η r) := hΦ.1.continuous.comp e.continuous
  have h2 : HasCompactSupport fun η : n → k => Φ (Matrix.of fun _ r => η r) := hΦ.2.comp_homeomorph e
  refine Continuous.integrable_of_hasCompactSupport (h1.mul ?_) h2.mul_right
  exact continuous_subtype_val.comp (hψ.comp (by fun_prop))

theorem finv_add (ψk : AddChar k Circle) (hψ : Continuous ψk) (ν : Measure k) [ν.IsAddHaarMeasure] (C : ℂ)
    {Φ Ψ : Matrix Unit n k → ℂ} (hΦ : Φ ∈ SB (Matrix Unit n k)) (hΨ : Ψ ∈ SB (Matrix Unit n k)) :
    finv ψk ν C (Φ + Ψ) = finv ψk ν C Φ + finv ψk ν C Ψ := by
  funext x
  simp only [finv, Pi.add_apply, add_mul]
  rw [integral_add (integrable_row ψk hψ ν hΦ x) (integrable_row ψk hψ ν hΨ x), mul_add]

theorem finv_smul (ψk : AddChar k Circle) (ν : Measure k) (C a : ℂ) (Φ : Matrix Unit n k → ℂ) :
    finv ψk ν C (a • Φ) = a • finv ψk ν C Φ := by
  funext x
  simp only [finv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  ring

theorem finv_trans (ψk : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (C : ℂ) (x : Matrix Unit n k)
    {Φ Φ' : Matrix Unit n k → ℂ} (h : ∀ t, Φ' t = Φ (t + x)) (a : Matrix n Unit k) :
    finv ψk ν C Φ' a = (ψk (-(∑ r, x () r * a r ())) : ℂ) * finv ψk ν C Φ a := by
  have := secondCountable k
  simp only [finv, h]
  rw [mul_left_comm]
  congr 1
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_add_right_eq_self _ (fun r => -(x () r))]
  congr 1
  funext η
  have e1 : (Matrix.of fun _ r => (η + fun r => -(x () r)) r : Matrix Unit n k) + x = Matrix.of fun _ r => η r := by
    ext i j; simp [Subsingleton.elim i ()]
  rw [e1]
  have e2 : (η + fun r => -(x () r)) ⬝ᵥ (fun r => a r ()) = (η ⬝ᵥ fun r => a r ()) + -(∑ r, x () r * a r ()) := by
    simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
  rw [e2, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem finv_mod (ψk : AddChar k Circle) (ν : Measure k) (C : ℂ) (t₀ : Matrix n Unit k)
    {Φ Φ' : Matrix Unit n k → ℂ} (h : ∀ t, Φ' t = (ψk (∑ r, t () r * t₀ r ()) : ℂ) * Φ t) (a : Matrix n Unit k) :
    finv ψk ν C Φ' a = finv ψk ν C Φ (a + t₀) := by
  simp only [finv, h]
  congr 1
  congr 1
  funext η
  have e : (η ⬝ᵥ fun r => (a + t₀) r ()) = (η ⬝ᵥ fun r => a r ()) + ∑ r, η r * t₀ r () := by
    simp [dotProduct, mul_add, Finset.sum_add_distrib]
  rw [e, AddChar.map_add_eq_mul, Circle.coe_mul]
  simp only [Matrix.of_apply]
  ring

end GlobalTheory.KappaModel

namespace GlobalTheory.KappaModel
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

theorem heis_comp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (L S L'' : HSp D) (κ : WO S L'' → WO L S)
    (hadd : ∀ w w', κ (w + w') = κ w + κ w') (hs : ∀ w w', symplO L S (κ w) (κ w') = symplO S L'' w w')
    (u : WO S L'') (f : WO L S → ℂ) :
    (fun w => heisO ψ L S (κ u) f (κ w)) = heisO ψ S L'' u (fun w => f (κ w)) := by
  funext w
  simp only [heisO, symplOH, hs, hadd]

theorem exists_frame_col {k : Type} [Field k] {N : ℕ} (hN : N = 1) (z₀ : Fin N → k) (hz : z₀ ≠ 0) :
    ∃ F : Frame k N Unit, ∀ r, F.β r () = z₀ r := by
  let i₀ : Fin N := ⟨0, by omega⟩
  have hu : ∀ i : Fin N, i = i₀ := fun i => Fin.ext (by omega)
  have h0 : z₀ i₀ ≠ 0 := fun h => hz (funext fun i => by rw [hu i]; exact h)
  refine ⟨⟨Matrix.of fun r _ => z₀ r, Matrix.of fun _ _ => (z₀ i₀)⁻¹, ?_, ?_⟩, fun _ => rfl⟩
  · ext i j
    rw [hu i, hu j, Matrix.mul_apply, Matrix.one_apply_eq]
    simp [h0]
  · ext i j
    rw [Matrix.mul_apply, Subsingleton.elim i j, Matrix.one_apply_eq, Fintype.sum_eq_single i₀ fun x hx => absurd (hu x) hx]
    simp [h0]

end GlobalTheory.KappaModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportLevelPlaceSymmetricChainSecondHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportLevelPlaceSymmetricChainSecondHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

namespace GlobalTheory.LocMod.GSuppTwo

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hz_link (p : Place D k) {σ : ℕ} {B : BesLev D (σ + 1)} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) :
    p.hz B = -p.xi ^ 2 * p.hz B' := by
  unfold Place.hz Place.xi Place.pr
  rw [l.norm, map_mul, map_mul, map_mul, map_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, map_neg]
  ring

theorem isComp_inv (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) :
    p.IsComp χ μ⁻¹ := by
  intro x a ha
  have h1 := h x a ha
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at h1 ⊢
  rw [h1, inv_inv]

theorem isLoc_one (p : Place D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) :
    p.IsLoc F 1 1 := by
  refine ⟨fun i j => by simp [Formalism.L2.Theta.mt], ?_⟩
  have : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
  simp [F.βγ]

theorem gsupp2_std : ∀ (D : D7), OmLoc D → FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s) (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (GlobalTheory.StepData.XIx (Fin κ) t j) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1)) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank),
    p.IsComp s₂.χV⁻¹ (S.μ (j + 1 + 1)) →
  ∀ T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂, Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) →
    Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) →
  ∀ h, SuppAt p.e B'.V h → GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ Φ₁)) (flatFB s₂ (s₂.om (1, h) (T₂ Φ₂))) ≠ 0 →
    ∃ r ∈ besGrp B'.d B'.o, SuppAt p.e B'.V r ∧
      ∃ u uk, p.IsLoc F.G₂ u uk ∧ uk ∈ ((S.T t).lev (j + 1 + 1) (c + 1) (by omega)).J ∧ h = r * u := by
  intro D hOm hBF hFB hCo hSym k _ _ _ _ p s κ S t _ _ ψ hstd hψ j c H σ B J B' F s₁ s₂ l vL hμ T₁ T₂ hT₁ hT₂
    Φ₁ Φ₂ hΦ₁ hΦ₂ h hh hne
  let _ : MeasurableSpace k := borel k
  have _ : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol k
  have _ := hν.1
  have hc : c = 2 * σ := by have := F.bes'.1; omega
  obtain ⟨-, hchar, hxi, -, hcomp⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hstd
  have hcont : Continuous S.ψ := (hchar S.ψ hψ).1
  obtain ⟨μT, hμT⟩ := hcomp s₂.χW
  have hμS := isComp_inv p hμ
  obtain ⟨hL1, hL2, hL3⟩ := (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).1 B'.V _ F.G₂
  obtain ⟨hk, hhk⟩ := hL2 h hh

  let Φ₂' : SB (Matrix (GlobalTheory.StepData.XIx (Fin κ) t (j + 1 + 1) ⊕ Fin (c + 1)) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k) :=
    ⟨om (S.μ (j + 1 + 1)) 1 hk Φ₂.1, GlobalTheory.SplitWeil.Model.om_mem_SB _ _ _ Φ₂.2⟩
  have hom : s₂.om (1, h) (T₂ Φ₂) = T₂ Φ₂' :=
    hOm k p ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil _ μT hμS hμT _ _ F.G₁ F.G₂ T₂ hT₂ 1 1 h hk
      (isLoc_one p F.G₁) hhk Φ₂ Φ₂' (by simp [Φ₂'])

  obtain ⟨C₀, hC₀⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D k p _ (σ + 1) F.s F.s_ne).1 B F.F₀).1
  obtain ⟨C₂, hC₂⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D k p _ σ (F.s * p.xi) (mul_ne_zero F.s_ne hxi)).1 B' F.F₂).1

  obtain ⟨U₁, hU₁, hflat₁⟩ := hBF k p ν hν.1 ψ S.ψ hψ (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C₀ F.G₀ F.F₁ F.G₁
    hC₀ F.bes F.jac T₁ hT₁
  have hjac' : p.IsJacFrame J F.s (-p.xi ^ 2 * p.hz B') F.F₁ F.G₁ := hz_link p l ▸ F.jac
  obtain ⟨U₂, hU₂, hflat₂⟩ := hFB k p ν hν.1 ψ S.ψ hψ σ J B' s₂ F.s F.s_ne _ _ (c + 1) F.F₁ F.G₁ F.F₂ C₂ F.G₂
    hjac' hC₂ F.bes' T₂ hT₂
  have hsb := GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k S.ψ ν hcont hν.1
  let Ψ₁ : SB (Matrix (GlobalTheory.StepData.XIx (Fin κ) t (j + 1)) (GlobalTheory.StepData.XIx (Fin κ) t j ⊕ Unit) k) :=
    ⟨GlobalTheory.LocFlat.flCol S.ψ ν (σ + 1 + 1) Φ₁.1, ((hsb _ _ (c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 _ Φ₁.2⟩
  let Ψ₂ : SB (Matrix (GlobalTheory.StepData.XIx (Fin κ) t (j + 1 + 1) ⊕ Unit) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1)) k) :=
    ⟨GlobalTheory.LocFlat.flRow S.ψ ν (σ + 1) Φ₂'.1, ((hsb _ _ (c + 1) (σ + 1) (by omega)).2 (by omega)).1 _ Φ₂'.2⟩
  obtain ⟨Λ, -, hΛ⟩ := hCo k p ν hν.1 ψ hstd S.ψ hψ (σ + 1) σ B B' l J.W₀ vL F.s F.s_ne _ _ _ F.F₀ C₀ F.F₁ F.F₂ C₂
    hC₀ hC₂ U₁ U₂ hU₁ hU₂
  obtain ⟨Ξ, hΞ, hΞΛ⟩ := hΛ Ψ₁ Ψ₂
  rw [hom, hflat₁ Φ₁ Ψ₁ rfl, hflat₂ Φ₂' Ψ₂ rfl, hΞΛ] at hne
  have hΞ0 : Ξ.1 ≠ 0 := by
    intro h0
    apply hne
    have : Ξ = 0 := Subtype.ext h0
    rw [this, map_zero]

  have hds := ((hSym k ν hν s κ S t).2.2.2 j c H σ hc).1 hk (by
    rw [hΞ] at hΞ0
    simpa [Ψ₁, Ψ₂, Φ₂', hΦ₁, hΦ₂] using hΞ0)
  obtain ⟨q, hq, u, hu, hkqu⟩ := hds
  obtain ⟨r, hr⟩ := (hL1 q).exists
  obtain ⟨u', hu'⟩ := (hL1 u).exists
  have hrB := (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).2.2 _ (c + 1) σ B' (F.s * p.xi) F.F₂ F.G₂ F.bes' r q hq hr
  refine ⟨r, hrB, hr.1, u', u, hu', hu, ?_⟩
  have h1 := hL3 r q u' u hr hu'
  rw [← hkqu] at h1
  exact (hL1 hk).unique hhk h1

end GlobalTheory.LocMod.GSuppTwo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportLevelPlaceSymmetricChainSecondHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_levelPlace_symmetricChain_secondHalf : ∀ (D : D7), OmLoc D → FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s) (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (GlobalTheory.StepData.XIx (Fin κ) t j) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1)) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank),
    p.IsComp s₂.χV⁻¹ (S.μ (j + 1 + 1)) →
  ∀ T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂, Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) →
    Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) →
  ∀ h, SuppAt p.e B'.V h → GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ Φ₁)) (flatFB s₂ (s₂.om (1, h) (T₂ Φ₂))) ≠ 0 →
    ∃ r ∈ besGrp B'.d B'.o, SuppAt p.e B'.V r ∧
      ∃ u uk, p.IsLoc F.G₂ u uk ∧ uk ∈ ((S.T t).lev (j + 1 + 1) (c + 1) (by omega)).J ∧ h = r * u := by
  first | exact @GlobalTheory.LocMod.GSuppTwo.gsupp2_std | exact GlobalTheory.LocMod.GSuppTwo.gsupp2_std | (intros; apply GlobalTheory.LocMod.GSuppTwo.gsupp2_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowFourierOntoAndSpanTransformedLastRow
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowFourierOntoAndSpanTransformedLastRow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.LastRow

open GlobalTheory.LocFlat.CFac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem fourier_inversion_const (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hne : ψ ≠ 1)
    [ν.IsAddHaarMeasure] (I : Type) [Fintype I] :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : I → k) (g : (I → k) → ℂ), g ∈ SB (I → k) →
      ∫ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * (∫ x, g x * (ψ (x ⬝ᵥ l) : ℂ) ∂(Measure.pi fun _ => ν))
        ∂(Measure.pi fun _ => ν) = (C : ℂ) * g a := by
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  have hpsi : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := by
    intro u
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  refine ⟨(nabs k c * ν.real (𝒪[k] : Set k) ^ 2) ^ Fintype.card I, ?_, fun a g hg => ?_⟩
  · have hO : 0 < ν.real (𝒪[k] : Set k) :=
      ENNReal.toReal_pos ((isOpen_int k).measure_pos ν ⟨0, zero_mem _⟩).ne' (isCompact_int k).measure_lt_top.ne
    have := nabs_pos k c
    positivity
  set μI : Measure (I → k) := Measure.pi fun _ => ν with hμI
  set h : (I → k) → ℂ := fun x => g (x + a) with hhdef
  have hh : h ∈ SB (I → k) :=
    ⟨hg.1.comp_continuous (continuous_add_const a), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have htr : ∀ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI =
      ∫ x, h x * (ψ (x ⬝ᵥ l) : ℂ) ∂μI := by
    intro l
    rw [← integral_const_mul, ← integral_add_right_eq_self _ a]
    congr 1
    funext x
    have e1 : (x + a) ⬝ᵥ l = x ⬝ᵥ l + l ⬝ᵥ a := by rw [add_dotProduct, dotProduct_comm a l]
    rw [hhdef, e1, AddChar.map_add_eq_mul, Circle.coe_mul]
    linear_combination (g (x + a) * (ψ (x ⬝ᵥ l) : ℂ)) * hpsi (l ⬝ᵥ a)
  simp only [htr]
  obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μI hc hh
  have hb : ∀ r : kˣ, μI.real (FourierPi.box I r) = ν.real (cball r) ^ Fintype.card I := by
    intro r
    simp [hμI, Measure.real, FourierPi.box, Measure.pi_pi]
  rw [hs, hb, hb, ← mul_pow, measureReal_cball, measureReal_cball]
  have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
    rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
  simp only [hhdef, zero_add, h4]
  push_cast
  ring

end GlobalTheory.LocMod.LastRow

namespace GlobalTheory.LocMod.LastRow

open GlobalTheory.LocFlat.CFac

theorem transform_onto_and_span_lastRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z], (∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η, b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) ∧ ∀ Ξ₂ : SB (Matrix (Z ⊕ Unit) n k), ∃ (N : ℕ) (a : Fin N → SB (Matrix Z n k)) (c : Fin N → SB (Matrix n Unit k)) (g : Fin N → SB (Matrix (Z ⊕ Unit) n k)), (∀ i x, (g i).1 x = (a i).1 x.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => (c i).1 (Matrix.of fun r _ => y r)) (x (Sum.inr ()))) ∧ Ξ₂ = ∑ i, g i := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n Z _ _ _ _
  haveI := hν
  haveI := secondCountable k
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI hTD : ∀ (a b : Type) [Fintype a] [Fintype b], TotallyDisconnectedSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (TotallyDisconnectedSpace (a → b → k))
  haveI hLC : ∀ (a b : Type) [Fintype a] [Fintype b], LocallyCompactSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (LocallyCompactSpace (a → b → k))
  haveI hT2 : ∀ (a b : Type), T2Space (Matrix a b k) := fun a b => inferInstanceAs (T2Space (a → b → k))
  have part1 : ∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η,
      b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ()) := by
    obtain ⟨C, hC, hinv⟩ := fourier_inversion_const ψk ν hψ hne n
    obtain ⟨c0, hc0⟩ := (conductor_exists k).1 ψk hψ hne
    intro b
    let e1 : (n → k) ≃ₜ Matrix Unit n k := (Homeomorph.funUnique Unit (n → k)).symm
    let g : SB (n → k) := comapH e1 b
    have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n => ν) hc0 g.2
    let e2 : Matrix n Unit k ≃ₜ (n → k) := Homeomorph.piCongrRight fun _ => Homeomorph.funUnique Unit k
    refine ⟨((C : ℂ)⁻¹) • comapH e2 ⟨_, hF⟩, fun η => ?_⟩
    unfold GlobalTheory.StepData.hat
    have e3 : ∀ y : n → k, ((((C : ℂ)⁻¹) • comapH e2 ⟨_, hF⟩ : SB (Matrix n Unit k)).1
        (Matrix.of fun r _ => y r)) * (ψk ((-1) * (η () ⬝ᵥ y)) : ℂ) =
        (C : ℂ)⁻¹ * ((ψk (-(y ⬝ᵥ η ())) : ℂ) * ∫ x, g.1 x * (ψk (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) := by
      intro y
      rw [neg_one_mul, dotProduct_comm]
      change (C : ℂ)⁻¹ * (∫ x, g.1 x * (ψk (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * _ = _
      ring
    simp only [e3]
    rw [integral_const_mul, hinv (η ()) g.1 g.2, ← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast hC.ne'), one_mul]
    rfl
  refine ⟨part1, fun Ξ₂ => ?_⟩
  let e : Matrix (Z ⊕ Unit) n k ≃ₜ Matrix Z n k × Matrix Unit n k := Homeomorph.sumArrowHomeomorphProdArrow
  have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (Matrix Z n k) (Matrix Unit n k)
  have hmem : comapH e.symm Ξ₂ ∈ Submodule.span ℂ
      (Set.range fun q : SB (Matrix Z n k) × SB (Matrix Unit n k) => prodSB q.1 q.2) := by
    rw [hspan]; trivial
  obtain ⟨N, f, q, hq⟩ := Submodule.mem_span_set'.mp hmem
  choose p hp using fun i => (q i).2
  choose c hc using fun i => part1 (p i).2
  refine ⟨N, fun i => f i • (p i).1, c, fun i => comapH e (prodSB (f i • (p i).1) (p i).2), fun i x => ?_, ?_⟩
  · rw [comapH_apply, prodSB_apply]
    congr 1
    exact hc i _
  · have h1 : Ξ₂ = comapH e (comapH e.symm Ξ₂) := by
      ext x; simp only [comapH_apply, Homeomorph.symm_apply_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, ← hq, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← hp i]
    ext x
    simp only [comapH_apply, prodSB_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.LocMod.LastRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowFourierOntoAndSpanTransformedLastRowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_fourier_onto_and_span_transformed_last_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z], (∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η, b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) ∧ ∀ Ξ₂ : SB (Matrix (Z ⊕ Unit) n k), ∃ (N : ℕ) (a : Fin N → SB (Matrix Z n k)) (c : Fin N → SB (Matrix n Unit k)) (g : Fin N → SB (Matrix (Z ⊕ Unit) n k)), (∀ i x, (g i).1 x = (a i).1 x.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => (c i).1 (Matrix.of fun r _ => y r)) (x (Sum.inr ()))) ∧ Ξ₂ = ∑ i, g i := by
  first | exact @GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow | exact GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow | (intros; apply GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceTargetLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceTargetLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SliceModelT

variable {D : D7}

theorem resT_symm_left {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO S A) :
    (d.resT S).symm (u, 0) = GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank) u := by
  rw [OrthDec.resT_symm_apply, GlobalTheory.MixModel.sandwich_apply, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem isThetaFunO_sliceT_left {ψ : AddChar (AF D.host.F) ℂ} {T A B S : HSp D} (d : OrthDec T A B) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (v : WO S B) : IsThetaFunO ψ S A fun u => f ((d.resT S).symm (u, v)) := {
  quasi γ u := by
    have e0 : (d.resT S).symm (ratW A S γ, 0) = ratW T S (d.iA * γ) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    have e : ((ratW A S γ + u, v) : WO S A × WO S B) = (ratW A S γ, (0 : WO S B)) + (u, v) := by simp
    show f ((d.resT S).symm (ratW A S γ + u, v)) = ψ (-(symplOH S A (ratW A S γ) u)) * f ((d.resT S).symm (u, v))
    rw [e, map_add (f := _), e0, hf.quasi, ← e0, d.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.MixModel.symplOH_zero_left, add_zero]
  level := by
    obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U.comap (GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)),
      hU.preimage (GlobalTheory.MixModel.continuous_sandwich _ _), fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (hk _ hu (GlobalTheory.MixModel.map_sandwich _ _ _ h0)) ((d.resT S).symm (w, v))
    rw [← resT_symm_left] at e1
    simp only [heisO] at e1 ⊢
    rw [← e1, ← map_add (d.resT S).symm, Prod.mk_add_mk, add_zero, d.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  cont := hf.cont.comp ((d.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const))
  smooth m L hL h0 w := by
    have e : ∀ t, (d.resT S).symm (w + L t, v) =
        (d.resT S).symm (w, v) + ((GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)).comp L) t := by
      intro t
      rw [AddMonoidHom.comp_apply, ← resT_symm_left, ← map_add (d.resT S).symm, Prod.mk_add_mk, add_zero]
    simp only [e]
    exact hf.smooth m ((GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)).comp L)
      ((GlobalTheory.MixModel.continuous_sandwich _ _).comp hL) (fun t => GlobalTheory.MixModel.map_sandwich _ _ _ (h0 t)) _ }

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem ι_mul (a : AE D) (x : k) : p.ι (p.π a * x) = a * p.ι x := by
  have h1 : p.π a * x = p.π (a * p.ι x) := by rw [map_mul, p.π_ι]
  rw [h1, p.ι_π, mul_left_comm, ← p.ι_π, p.π_ι]

theorem mul_map_ι {m l n : Type} [Fintype l] (N : Matrix m l (AE D)) (M : Matrix l n k) :
    N * M.map p.ι = (N.map p.π * M).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul]

variable {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} (FS : Frame k S.rank n)

theorem beta_eq (hF : p.IsCoreFrame B s FA F₀) :
    F₀.β = fromCols (B.o.iA.map (prH p) * FA.β) (Matrix.of fun r (_ : Unit) => s * prH p (vecB B.o B.ζ r)) := by
  ext r (a | _)
  · exact hF.1 r a
  · exact hF.2 r

theorem col_eq : (Matrix.of fun r (_ : Unit) => s * prH p (vecB B.o B.ζ r)) =
    s • (B.o.iB.map (prH p) * Matrix.of fun j (_ : Unit) => prH p (B.ζ j)) := by
  ext r u
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem qA_beta (hF : p.IsCoreFrame B s FA F₀) : B.o.qA.map (prH p) * F₀.β = fromCols FA.β 0 := by
  rw [beta_eq p B hF, col_eq, Matrix.mul_fromCols, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.map_mul, ← Matrix.map_mul, B.o.qA_iA, B.o.qA_iB, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, smul_zero]

theorem up_fromRows (hF : p.IsCoreFrame B s FA F₀) (x : Matrix n' n k) :
    p.up FS F₀ (fromRows x 0) = (B.o.resT S).symm (p.up FS FA x, 0) := by
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Place.up, Place.up, OrthDec.jA, rat, mul_map_ι,
    beta_eq p B hF, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Matrix.map_map]
  simp only [Matrix.mul_assoc]
  rfl

theorem resT_up_fst (hF : p.IsCoreFrame B s FA F₀) (x : Matrix (n' ⊕ Unit) n k) :
    (B.o.resT S (p.up FS F₀ x)).1 = p.up FS FA x.toRows₁ := by
  rw [OrthDec.resT_apply]
  dsimp only
  rw [Place.up, Place.up, OrthDec.pA, rat, mul_map_ι, Matrix.map_map]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change (B.o.qA.map (prH p) * F₀.β) * x * FS.γ = _
  rw [qA_beta p B hF]
  conv_lhs => rw [← fromRows_toRows x]
  rw [fromCols_mul_fromRows, Matrix.zero_mul, add_zero]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

def rowsH (n n' : Type) [Fintype n] [Fintype n'] : Matrix (n' ⊕ Unit) n k ≃ₜ Matrix n' n k × (n → k) where
  toFun x := (x.toRows₁, x (Sum.inr ()))
  invFun q := fromRows q.1 (Matrix.of fun _ => q.2)
  left_inv x := by
    ext (i | i) j <;> rfl
  right_inv q := by
    ext i j <;> rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ (continuous_apply _)
    exact continuous_pi fun i => continuous_apply (Sum.inl i)
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    rcases i with i | i
    · exact (continuous_apply i).comp continuous_fst
    · exact continuous_snd

def tens (a : SB (n → k)) : SB (Matrix n' n k) →ₗ[ℂ] SB (Matrix (n' ⊕ Unit) n k) where
  toFun Ξ := GlobalTheory.LocFlat.CFac.comapH (rowsH n n') (GlobalTheory.LocFlat.CFac.prodSB Ξ a)
  map_add' Ξ Ξ' := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, add_mul]
  map_smul' c Ξ := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, mul_assoc]

theorem tens_apply (a : SB (n → k)) (Ξ : SB (Matrix n' n k)) (x : Matrix (n' ⊕ Unit) n k) :
    (tens a Ξ).1 x = Ξ.1 x.toRows₁ * a.1 (x (Sum.inr ())) := rfl

end GlobalTheory.SliceModelT


open GlobalTheory.SliceModelT in
theorem GlobalTheory.SliceModelT.main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := by
  intro D k _ _ _ _ p ψ n n' _ _ _ _ ρ B S s FA F₀ FS hF T₀ hT a ha v
  let a' : SB (n → k) := ⟨a, ha⟩
  let T₁ : SB (Matrix n' n k) →ₗ[ℂ] (WO S B.A → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun u : WO S B.A => (B.o.resT S).symm (u, v))) ∘ₗ T₀ ∘ₗ tens a'
  have hT₁ : ∀ Ξ u, T₁ Ξ u = T₀ (tens a' Ξ) ((B.o.resT S).symm (u, v)) := fun _ _ => rfl
  refine ⟨T₁, ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact isThetaFunO_sliceT_left B.o (hT.theta _) v
  · have h1 := hT.trans (fromRows x 0) (tens a' Φ) (tens a' Φ') (fun t => by
      have e1 : (t + fromRows x (0 : Matrix Unit n k)).toRows₁ = t.toRows₁ + x := by
        ext i j; simp [Matrix.toRows₁, Matrix.fromRows_apply_inl]
      have e2 : (t + fromRows x (0 : Matrix Unit n k) : Matrix (n' ⊕ Unit) n k) (Sum.inr ()) = t (Sum.inr ()) := by
        funext j; simp [Matrix.fromRows_apply_inr]
      rw [tens_apply, tens_apply, hΦ, e1, e2])
    funext u
    rw [hT₁, h1, up_fromRows p B S FS hF]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resT S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · set Y : WO S B.V₀ := (B.o.resT S).symm (y, 0) with hYdef
    have hY : IsHalf (cA D p.e) Y := by
      intro i j
      rw [hYdef, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hy l j]
    have h1 := hT.modul Y hY (tens a' Φ) (tens a' Φ') (fun t => by
      rw [tens_apply, tens_apply, hΦ, B.o.symplO_resT, resT_up_fst p B S FS hF, hYdef, AddEquiv.apply_symm_apply,
        symplO_zero_right', add_zero, mul_assoc])
    funext u
    rw [hT₁, h1]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resT S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have e : Ψ = tens a' Ξ := Subtype.ext (funext hΨ)
    rw [e, hT₁]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceTargetLineStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_model_slice_target_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := by
  first | exact @GlobalTheory.SliceModelT.main | exact GlobalTheory.SliceModelT.main | (intros; apply GlobalTheory.SliceModelT.main <;> assumption)
end
end
