module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open GlobalTheory.Grow GlobalTheory.Unf NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitOrbit

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {k : ℕ} (a : Mx D S.rank k) (x : Fin S.rank → AE D) (y : Fin k → AE D) :
    hermAt S x (a *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj a ⬝ gA S) *ᵥ x) := by
  have h : (fun i => cA D ((a *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj a := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hermAt_eq, h, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (adj a)]

theorem hermAt_unitary (S : HSp D) (g : GA D S) (x y : Fin S.rank → AE D) :
    hermAt S (mt S g *ᵥ x) (mt S g *ᵥ y) = hermAt S x y := by
  rw [hermAt_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, mt_unitary, hermAt_eq]

theorem hermAt_jB {S A B : HSp D} (o : OrthDec S A B) (y : Fin S.rank → AE D) (l : Fin B.rank → AE D) :
    hermAt S y (o.jB *ᵥ l) = hermAt B (o.pB *ᵥ y) l := by
  rw [hermAt_mulVec, hermAt_eq, Matrix.mulVec_mulVec, o.pB_eq, ← Matrix.mul_assoc (gA B), gA_mul_giA, Matrix.one_mul]

theorem hermAt_jA {S A B : HSp D} (o : OrthDec S A B) (x : Fin A.rank → AE D) (y : Fin S.rank → AE D) :
    hermAt S (o.jA *ᵥ x) y = hermAt A x (o.pA *ᵥ y) := by
  have h : gA S * o.jA = adj o.pA * gA A := by
    rw [o.gA_eq]
    simp only [Matrix.add_mul, Matrix.mul_assoc, o.pA_jA, o.pB_jA, Matrix.mul_one, Matrix.mul_zero, add_zero]
  rw [hermAt_mulVec, hermAt_eq, Matrix.mulVec_mulVec, h]

theorem exists_den {P : Pl D → Prop} {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : Fin n → AE D, (∀ i, y i ∈ intAt D P) → ∀ i, ((N : AE D) • (X *ᵥ y)) i ∈ intAt D P := by
  choose k hk hX using fun p : Fin m × Fin n => GlobalTheory.LatMatch.exists_nat_smul_intAE (finPart D (X p.1 p.2))
  refine ⟨∏ p, k p, Finset.prod_pos fun p _ => hk p, fun y hy i => ⟨?_, ?_⟩⟩
  · exact Ideal.mul_mem_left _ _ (mulVec_mem_idAt X (fun j => (hy j).1) i)
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum]
    refine sum_mem fun j _ => ?_
    rw [← mul_assoc, map_mul]
    refine GlobalTheory.LatMatch.mul_mem_intAE' D ?_ (hy j).2
    rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), mul_smul]
    exact nsmul_mem (hX (i, j)) _

def pre {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) (Λ : AddSubgroup (Fin m → AE D)) : AddSubgroup (Fin n → AE D) :=
  Λ.comap (Matrix.mulVecLin X).toAddMonoidHom

theorem mem_pre {m n : ℕ} {X : Matrix (Fin m) (Fin n) (AE D)} {Λ : AddSubgroup (Fin m → AE D)} {y : Fin n → AE D} :
    y ∈ pre X Λ ↔ X *ᵥ y ∈ Λ := Iff.rfl

theorem pre_den {P : Pl D → Prop} {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) {Λ : AddSubgroup (Fin m → AE D)}
    (h : ∃ N : ℕ, 0 < N ∧ ∀ y : Fin m → AE D, (∀ i, y i ∈ intAt D P) → (N : AE D) • y ∈ Λ) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : Fin n → AE D, (∀ i, y i ∈ intAt D P) → (N : AE D) • y ∈ pre X Λ := by
  obtain ⟨N, hN, h⟩ := h
  obtain ⟨N', hN', h'⟩ := exists_den (P := P) X
  refine ⟨N * N', Nat.mul_pos hN hN', fun y hy => ?_⟩
  rw [mem_pre, Matrix.mulVec_smul, Nat.cast_mul, mul_smul]
  exact h _ (h' y hy)

theorem isSDAt_pre_unitary {S : HSp D} {v : Pl D} {Λ : AddSubgroup (Fin S.rank → AE D)} (h : IsSDAt S v Λ) (g : GA D S) :
    IsSDAt S v (pre (mt S g) Λ) := by
  have e : ∀ y, mt S g⁻¹ *ᵥ (mt S g *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mulVec]
  have e' : ∀ y, mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]
  refine ⟨fun y hy => ?_, pre_den _ h.2.1, fun y hy => ?_⟩
  · rw [← e y]; exact mulVec_mem_idAt _ (h.1 _ hy)
  · rw [mem_pre, h.2.2 _ (mulVec_mem_idAt _ hy)]
    constructor
    · intro H x hx
      rw [← hermAt_unitary S g]; exact H _ hx
    · intro H x hx
      rw [← e' x, hermAt_unitary]
      exact H _ (by rw [mem_pre, e']; exact hx)

theorem split_of_le {S A B : HSp D} (o : OrthDec S A B) {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)}
    {Λ : AddSubgroup (Fin B.rank → AE D)} (hM : IsSDAt S v M) (hΛ : IsSDAt B v Λ) (hle : ∀ l ∈ Λ, o.jB *ᵥ l ∈ M) :
    IsSDAt A v (pre o.jA M) ∧ ∀ y, y ∈ M ↔ o.pA *ᵥ y ∈ pre o.jA M ∧ o.pB *ᵥ y ∈ Λ := by
  have hsum : ∀ y, o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  have eA : ∀ x, o.pA *ᵥ (o.jA *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]
  have hB : ∀ y ∈ M, o.pB *ᵥ y ∈ Λ := fun y hy => by
    rw [hΛ.2.2 _ (mulVec_mem_idAt _ (hM.1 y hy))]
    intro l hl
    rw [← hermAt_jB]
    exact (hM.2.2 y (hM.1 y hy)).1 hy _ (hle l hl)
  have hA : ∀ y ∈ M, o.pA *ᵥ y ∈ pre o.jA M := fun y hy => by
    rw [mem_pre, eq_sub_of_add_eq (hsum y)]
    exact sub_mem hy (hle _ (hB y hy))
  refine ⟨⟨fun x hx => ?_, pre_den _ hM.2.1, fun x hx => ?_⟩, fun y => ⟨fun hy => ⟨hA y hy, hB y hy⟩, fun hy => ?_⟩⟩
  · rw [← eA x]; exact mulVec_mem_idAt _ (hM.1 _ hx)
  · rw [mem_pre, hM.2.2 _ (mulVec_mem_idAt _ hx)]
    constructor
    · intro H x' hx'
      rw [← eA x', ← hermAt_jA]; exact H _ hx'
    · intro H y hy
      rw [hermAt_jA]; exact H _ (hA y hy)
  · rw [← hsum y]; exact add_mem hy.1 (hle _ hy.2)

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : incA D a • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, b, hb, x, hx, rfl⟩ := hy
    obtain rfl : b = 1 := hb
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, x, hx, funext fun i => ?_⟩
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (_ ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_mem_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} {b : D.host.E} (hb : b ∈ D.host.AA⁻¹)
    {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : incA D b • y ∈ latV S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, a, ha, x, hx, rfl⟩ := hy
    have h1 : a * b ∈ D.host.AA * D.host.AA⁻¹ := FractionalIdeal.mul_mem_mul ha hb
    rw [mul_inv_cancel₀ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)] at h1
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    refine AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, c • x, L.smul_mem c hx, funext fun i => ?_⟩
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] b) * (_ ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, Pi.smul_apply, Algebra.smul_def c, hc, ← mul_assoc, mul_comm b]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_latV_of_forall {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (h : ∀ a ∈ D.host.AA, incA D a • y ∈ latA S L P) : y ∈ latV S L P := by
  have key : ∀ c ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) * (D.host.AA⁻¹ : FractionalIdeal _ D.host.E)),
      incA D c • y ∈ latV S L P := by
    intro c hc
    refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) fun c c' h1 h2 => ?_
    · rw [mul_comm, map_mul, mul_smul]
      exact smul_mem_latV hb (h a ha)
    · rw [map_add (f := _), add_smul]; exact add_mem h1 h2
  have := key 1 (by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)]
    exact FractionalIdeal.one_mem_one _)
  rwa [map_one, one_smul] at this

theorem exists_eq_smul {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) (l : Fin L.rank → AE D) :
    ∃ a : AE D, l = a • ratV ζ := by
  have hs : ∀ i j : Fin L.rank, i = j := fun i j => Fin.ext (by have := h.1; omega)
  obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h.2
    rw [show ζ = 0 from funext hcon]
    simp
  refine ⟨l i * incA D (ζ i)⁻¹, funext fun j => ?_⟩
  rw [hs j i, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, mul_one]

theorem ratV_vecB {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    ratV (vecB o ζ) = o.jB *ᵥ ratV ζ :=
  funext fun i => RingHom.map_mulVec (incA D) o.iB ζ i

theorem emb_mem_grpAt {S A B : HSp D} (o : OrthDec S A B) {P : Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  have ha' := (mem_congGrp_iff A (idAt D P) a).1 ha
  refine (mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : mt S (o.emb (a, 1)) - 1 = o.jA * (mt A a - 1) * o.pA := by
    rw [o.mt_emb, ← o.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, mt_one, Matrix.mul_one, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact ha' l k)

theorem line_le {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {L₀ : Lat S} {LA : Lat A}
    {LL : Lat L} {v : Pl D} (hO : OrthAt o L₀ LA LL v) (g : Mx D S.rank S.rank)
    (hz : ∀ a : AE D, a • ratV (vecB o ζ) ∈ latA S L₀ (· = v) → g *ᵥ (a • ratV (vecB o ζ)) ∈ latA S L₀ (· = v))
    (l : Fin L.rank → AE D) (hl : l ∈ latV L LL (· = v)) : o.jB *ᵥ l ∈ pre g (latV S L₀ (· = v)) := by
  have h1 : o.jB *ᵥ l ∈ latV S L₀ (· = v) := by
    refine (hO _).2 ?_
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.pA_jB, o.pB_jB, Matrix.zero_mulVec, Matrix.one_mulVec]
    exact ⟨zero_mem _, hl⟩
  obtain ⟨c, rfl⟩ := exists_eq_smul hζ l
  rw [Matrix.mulVec_smul, ← ratV_vecB] at h1 ⊢
  refine mem_pre.2 (mem_latV_of_forall fun a ha => ?_)
  have h2 := smul_mem_latA ha h1
  rw [smul_smul] at h2
  rw [← Matrix.mulVec_smul, smul_smul]
  exact hz _ h2

theorem moves_of_split {S A B : HSp D} (o : OrthDec S A B) {L₀ : Lat S} {LA : Lat A} {LB : Lat B} {v : Pl D}
    (hO : OrthAt o L₀ LA LB v) (γ : GA D S) (a : GA D A) {Λ : AddSubgroup (Fin A.rank → AE D)}
    (hsplit : ∀ y, y ∈ pre (mt S γ⁻¹) (latV S L₀ (· = v)) ↔ o.pA *ᵥ y ∈ Λ ∧ o.pB *ᵥ y ∈ latV B LB (· = v))
    (hmv : ∀ y : Fin A.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV A LA (· = v) ↔ mt A a *ᵥ y ∈ Λ)) :
    Moves S ((o.emb (a, 1))⁻¹ * γ) L₀ L₀ (· = v) := by
  intro y hy
  obtain ⟨z, hzdef⟩ : ∃ z, z = mt S ((o.emb (a, 1))⁻¹ * γ) *ᵥ y := ⟨_, rfl⟩
  rw [← hzdef]
  have hzI : ∀ i, z i ∈ idAt D (· = v) := by rw [hzdef]; exact mulVec_mem_idAt _ hy
  have hw : y = mt S γ⁻¹ *ᵥ (mt S (o.emb (a, 1)) *ᵥ z) := by
    rw [hzdef, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mt_mul, ← mt_mul]
    have : γ⁻¹ * o.emb (a, 1) * ((o.emb (a, 1))⁻¹ * γ) = 1 := by group
    rw [this, mt_one, Matrix.one_mulVec]
  have key := hsplit (mt S (o.emb (a, 1)) *ᵥ z)
  rw [mem_pre, ← hw] at key
  rw [key, hO z, Matrix.mulVec_mulVec, o.pA_emb, Matrix.mulVec_mulVec, o.pB_emb, mt_one, Matrix.one_mul,
    ← Matrix.mulVec_mulVec, ← hmv _ (mulVec_mem_idAt _ hzI)]

theorem orbitSplit : ∀ D : D7, GlobalTheory.FinPl.OrbitSplit D := by
  intro D σ B L₀ v hT hL₀ ⟨LA, LL, hLA, hLL, hO⟩ γ hγ hz
  have hM := isSDAt_pre_unitary (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D B.V₀ L₀ v hL₀) γ⁻¹
  obtain ⟨hA, hsplit⟩ := split_of_le B.o hM (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D B.L LL v hLL) (line_le B.o B.line hO _ hz)
  obtain ⟨a, ha, hmv⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D B.A v _ _ hT (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D B.A LA v hLA) hA
  exact ⟨a, ha, (B.o.emb (a, 1))⁻¹ * γ, ⟨mul_mem (inv_mem (emb_mem_grpAt B.o ha)) hγ,
    moves_of_split B.o hO γ a hsplit hmv⟩, (mul_inv_cancel_left _ _).symm⟩

end GlobalTheory.FinPl.SplitOrbit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplitStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitNormVectors_one_orbit_selfDualLattice_split : ∀ D : D7, GlobalTheory.FinPl.OrbitSplit D := by
  first | exact @GlobalTheory.FinPl.SplitOrbit.orbitSplit | exact GlobalTheory.FinPl.SplitOrbit.orbitSplit | (intros; apply GlobalTheory.FinPl.SplitOrbit.orbitSplit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterMtEqSmulOne
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.CenterScalar
open Matrix Polynomial

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]

theorem eval_charpolyRev_eq (M : Matrix n n E) (z : E) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm z]

theorem cT_smul (σ : E →+* E) (c : E) (M : Matrix n n E) :
    Formalism.UG.cT σ (c • M) = σ c • Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_add (σ : E →+* E) (M N : Matrix n n E) :
    Formalism.UG.cT σ (M + N) = Formalism.UG.cT σ M + Formalism.UG.cT σ N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sub (σ : E →+* E) (M N : Matrix n n E) :
    Formalism.UG.cT σ (M - N) = Formalism.UG.cT σ M - Formalism.UG.cT σ N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n E) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cayley_unitary (σ : E →+* E) (J X : Matrix n n E) (t : E) (ht : σ t = t)
    (hX : Formalism.UG.cT σ X * J + J * X = 0) (hA : (1 - t • X).det ≠ 0) :
    Formalism.UG.cT σ ((2 : E) • (1 - t • X)⁻¹ - 1) * J * ((2 : E) • (1 - t • X)⁻¹ - 1) = J := by
  set A : Matrix n n E := 1 - t • X with hAdef
  set P : Matrix n n E := A⁻¹
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have hAP : A * P = 1 := Matrix.mul_nonsing_inv A hu
  have hPA : P * A = 1 := Matrix.nonsing_inv_mul A hu
  set g : Matrix n n E := (2 : E) • P - 1
  have hgA : g * A = 1 + t • X := by
    rw [Matrix.sub_mul, Matrix.smul_mul, hPA, Matrix.one_mul, hAdef, two_smul]
    abel
  have hcA : Formalism.UG.cT σ A = 1 - t • Formalism.UG.cT σ X := by
    rw [hAdef, cT_sub, cT_smul, Formalism.UG.cT_one, ht]
  have hcPA : Formalism.UG.cT σ P * Formalism.UG.cT σ A = 1 := by
    rw [← Formalism.UG.cT_mul, hAP, Formalism.UG.cT_one]
  have hY : Formalism.UG.cT σ X * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have key : Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A = Formalism.UG.cT σ A * J * A := by
    have e1 : Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A = Formalism.UG.cT σ (g * A) * J * (g * A) := by
      rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    rw [e1, hgA, hcA, cT_add, cT_smul, Formalism.UG.cT_one, ht]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hY]
    rw [hAdef]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul]
    module
  calc Formalism.UG.cT σ g * J * g
      = (Formalism.UG.cT σ P * Formalism.UG.cT σ A) * (Formalism.UG.cT σ g * J * g) * (A * P) := by
        rw [hcPA, hAP, Matrix.one_mul, Matrix.mul_one]
    _ = Formalism.UG.cT σ P * (Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A) * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ P * (Formalism.UG.cT σ A * J * A) * P := by rw [key]
    _ = (Formalism.UG.cT σ P * Formalism.UG.cT σ A) * J * (A * P) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [hcPA, hAP, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.CenterScalar

namespace GlobalTheory.CenterScalar
open Matrix Polynomial

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
variable {R : Type} [CommRing R] (ι : E →+* R)

theorem map_smulE (c : E) (M : Matrix n n E) : (c • M).map ι = ι c • M.map ι := by
  ext i j; simp

theorem map_subE (M N : Matrix n n E) : (M - N).map ι = M.map ι - N.map ι := by
  ext i j; simp

theorem map_addE (M N : Matrix n n E) : (M + N).map ι = M.map ι + N.map ι := by
  ext i j; simp

theorem map_oneE : (1 : Matrix n n E).map ι = 1 := Matrix.map_one _ (map_zero ι) (map_one ι)

theorem map_mulE (M N : Matrix n n E) : (M * N).map ι = M.map ι * N.map ι := Matrix.map_mul

theorem commute_skew (σ : E →+* E) (J : Matrix n n E) (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι))
    (X : Matrix n n E) (hX : Formalism.UG.cT σ X * J + J * X = 0) : Commute Z (X.map ι) := by
  classical
  have hp : X.charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := X)
    rw [h, Polynomial.eval_zero] at this
    exact zero_ne_one this
  obtain ⟨t, ht, hts⟩ := hF.exists_notMem_finset (insert 0 X.charpolyRev.roots.toFinset)
  have ht0 : t ≠ 0 := fun e => hts (by simp [e])
  have hdet : (1 - t • X).det ≠ 0 := by
    intro e
    apply hts
    rw [Finset.mem_insert, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot, eval_charpolyRev_eq]
    exact Or.inr e
  have hg := hZ _ (cayley_unitary σ J X t ht hX hdet)
  set A : Matrix n n E := 1 - t • X with hAdef
  set P : Matrix n n E := A⁻¹
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have hAP : A * P = 1 := Matrix.mul_nonsing_inv A hu
  have hPA : P * A = 1 := Matrix.nonsing_inv_mul A hu
  have hP : Commute Z (P.map ι) := by
    have h1 : Commute Z (((2 : E) • P - 1).map ι + 1) := hg.add_right (Commute.one_right Z)
    rw [map_subE, map_smulE, map_oneE, sub_add_cancel] at h1
    have h3 := h1.smul_right (ι (2 : E)⁻¹)
    rwa [smul_smul, ← map_mul, inv_mul_cancel₀ h2, map_one, one_smul] at h3
  have hA : Commute Z (A.map ι) := by
    let u : (Matrix n n R)ˣ := ⟨P.map ι, A.map ι, by rw [← map_mulE, hPA, map_oneE], by rw [← map_mulE, hAP, map_oneE]⟩
    exact Commute.units_inv_right (u := u) hP
  have h4 : Commute Z (ι t • X.map ι) := by
    have := (Commute.one_right Z).sub_right hA
    rwa [hAdef, map_subE, map_oneE, map_smulE, sub_sub_cancel] at this
  have h5 := h4.smul_right (ι t⁻¹)
  rwa [smul_smul, ← map_mul, inv_mul_cancel₀ ht0, map_one, one_smul] at h5

theorem commute_all (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n E) (hJh : Formalism.UG.cT σ J = J)
    (hJ : J.det ≠ 0) (ξ : E) (hξ : σ ξ = -ξ) (hξ0 : ξ ≠ 0)
    (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι))
    (M : Matrix n n E) : Commute Z (M.map ι) := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ
  have hJJi : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have hJiJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hcJi : Formalism.UG.cT σ J⁻¹ * J = 1 := by
    calc Formalism.UG.cT σ J⁻¹ * J = Formalism.UG.cT σ J⁻¹ * Formalism.UG.cT σ J := by rw [hJh]
      _ = 1 := by rw [← Formalism.UG.cT_mul, hJJi, Formalism.UG.cT_one]
  have skew : ∀ K : Matrix n n E, Formalism.UG.cT σ K = -K → Commute Z ((J⁻¹ * K).map ι) := by
    intro K hK
    refine commute_skew ι σ J hF h2 Z hZ _ ?_
    rw [Formalism.UG.cT_mul, hK, Matrix.mul_assoc, hcJi, ← Matrix.mul_assoc, hJJi]
    simp
  set K := J * M
  have hK1 : Formalism.UG.cT σ (K - Formalism.UG.cT σ K) = -(K - Formalism.UG.cT σ K) := by
    rw [cT_sub, cT_cT σ hσ]; abel
  have hK2 : Formalism.UG.cT σ (ξ • (K + Formalism.UG.cT σ K)) = -(ξ • (K + Formalism.UG.cT σ K)) := by
    rw [cT_smul, cT_add, cT_cT σ hσ, hξ, neg_smul, add_comm (Formalism.UG.cT σ K)]
  have c1 := skew _ hK1
  have c2 := (skew _ hK2).smul_right (ι ξ⁻¹)
  have c3 := (c1.add_right c2).smul_right (ι (2 : E)⁻¹)
  have e : M = (2 : E)⁻¹ • (J⁻¹ * (K - Formalism.UG.cT σ K) + ξ⁻¹ • (J⁻¹ * (ξ • (K + Formalism.UG.cT σ K)))) := by
    rw [Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hξ0, one_smul, ← Matrix.mul_add, sub_add_add_cancel,
      ← two_smul E K, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul, ← Matrix.mul_assoc, hJiJ,
      Matrix.one_mul]
  rw [e, map_smulE, map_addE, map_smulE]
  exact c3

theorem eq_smul_one (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n E) (hJh : Formalism.UG.cT σ J = J)
    (hJ : J.det ≠ 0) (ξ : E) (hξ : σ ξ = -ξ) (hξ0 : ξ ≠ 0)
    (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι)) :
    ∃ c : R, Z = c • (1 : Matrix n n R) := by
  have hs : Z ∈ Set.range (Matrix.scalar n) := by
    refine Matrix.mem_range_scalar_of_commute_single fun i j _ => ?_
    have := (commute_all ι σ hσ J hJh hJ ξ hξ hξ0 hF h2 Z hZ (Matrix.single i j 1)).symm
    have e : (Matrix.single i j (1 : E)).map ι = Matrix.single i j 1 := by
      ext a b; simp [Matrix.single_apply]
    rwa [e] at this
  obtain ⟨c, hc⟩ := hs
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end GlobalTheory.CenterScalar

namespace GlobalTheory.CenterScalar
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_skew (D : D7) : ∃ ξ : D.host.E,
    (D.sp.cm.sig : D.host.E →+* D.host.E) ξ = -ξ ∧ ξ ≠ 0 := by
  obtain ⟨e, he⟩ : ∃ e : D.host.E, e ∉ (algebraMap D.host.F D.host.E).range := by
    by_contra h
    push_neg at h
    have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
      ext x
      simp only [Algebra.mem_bot, Algebra.mem_top, iff_true]
      exact h x
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
    rw [D.sp.cm.deg2] at h1
    norm_num at h1
  refine ⟨e - star e, ?_, ?_⟩
  · change star (e - star e) = -(e - star e)
    rw [star_sub, star_star, neg_sub]
  · intro h0
    apply he
    exact (D.sp.cm.fixed e).1 (sub_eq_zero.1 h0).symm

theorem fixed_infinite (D : D7) :
    {t : D.host.E | (D.sp.cm.sig : D.host.E →+* D.host.E) t = t}.Infinite := by
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (algebraMap D.host.F D.host.E).injective)
  rintro _ ⟨a, rfl⟩
  exact D.sp.cm.sig.commutes a

theorem center_mt_eq_smul_one : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (z : GA D V), z ∈ Subgroup.center (GA D V) →
    ∃ c : AE D, Formalism.L2.Theta.mt V z = c • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  intro D V z hz
  obtain ⟨ξ, hξ, hξ0⟩ := exists_skew D
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)
  have hσ : ∀ x, σ (σ x) = x := fun x => star_star x
  have hJh : Formalism.UG.cT σ V.gram = V.gram := Matrix.ext fun i j => V.herm.eq (V.frame j) (V.frame i)
  refine eq_smul_one (incA D) σ hσ V.gram hJh (Formalism.L2.Theta.gram_det_ne V) ξ hξ hξ0 (fixed_infinite D)
    two_ne_zero _ ?_
  intro g hg
  have hdet : IsUnit g.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => Formalism.L2.Theta.gram_det_ne V ?_
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  let gG : GL (Fin V.rank) D.host.E := Matrix.nonsingInvUnit g hdet
  have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g.map (incA D)) = (Formalism.UG.cT σ g).map (incA D) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR, σ]
  have hmem : Formalism.UG.bc (incA D) gG ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g.map (incA D)) * (V.gram.map (incA D)) * g.map (incA D) =
      V.gram.map (incA D)
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  let w : GA D V := ⟨Formalism.UG.bc (incA D) gG, hmem⟩
  have hw : Formalism.L2.Theta.mt V w = g.map (incA D) := rfl
  have hzw : w * z = z * w := Subgroup.mem_center_iff.1 hz w
  have e1 : Formalism.L2.Theta.mt V (w * z) = Formalism.L2.Theta.mt V w * Formalism.L2.Theta.mt V z := by
    simp [Formalism.L2.Theta.mt, map_mul]
  have e2 : Formalism.L2.Theta.mt V (z * w) = Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V w := by
    simp [Formalism.L2.Theta.mt, map_mul]
  rw [← hw]
  change Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V w = Formalism.L2.Theta.mt V w * Formalism.L2.Theta.mt V z
  rw [← e1, ← e2, hzw]

end GlobalTheory.CenterScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacesDvdNormIffUnderPrimesDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacesDvdNormIffUnderPrimesDvd
open NumberField IsDedekindDomain Formalism.BasicNotions
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormPlaces

theorem places_dvd_iff (D : Formalism.BasicNotions.D7) (π π' : 𝓞 D.host.E) (T : ℕ)
    (hc : (π' : D.host.E) = star (π : D.host.E)) (hT : π * π' = (T : 𝓞 D.host.E)) (hπ : π ≠ 0)
    (x : HeightOneSpectrum (𝓞 D.host.F)) :
    (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x := by
  have hmap : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (T : 𝓞 D.host.F) = (T : 𝓞 D.host.E) := map_natCast _ _
  constructor
  · intro hx
    have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) :=
      FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E)
    have hker : RingHom.ker (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ x.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le
    haveI := x.isPrime
    obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal (𝓞 D.host.E))
      (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]; exact hker)
    have hQb : Q ≠ ⊥ := by
      rintro rfl
      apply x.ne_bot
      rw [← hQ, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
    let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQp, hQb⟩
    have hw : w.under (𝓞 D.host.F) = x := HeightOneSpectrum.ext hQ
    have hTw : π * π' ∈ w.asIdeal := by
      rw [hT, ← hmap]
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (T : 𝓞 D.host.F) ∈ Q
      rw [← Ideal.mem_comap]
      change (T : 𝓞 D.host.F) ∈ Ideal.under (𝓞 D.host.F) Q
      rw [hQ]; exact hx
    rcases w.isPrime.mem_or_mem hTw with h | h
    · exact ⟨w, (Formalism.L2.Col.mem_divs hπ w).2 h, hw⟩
    · refine ⟨GlobalTheory.IdemSupport.cP w, (Formalism.L2.Col.mem_divs hπ _).2 ?_, (GlobalTheory.IdemSupport.under_cP w).trans hw⟩
      rw [GlobalTheory.IdemSupport.mem_cP]
      have : GlobalTheory.IdemSupport.cO D π = π' := by
        apply RingOfIntegers.ext
        rw [GlobalTheory.IdemSupport.cO_coe, hc]
      rw [this]; exact h
  · rintro ⟨w, hw, rfl⟩
    have h1 : π ∈ w.asIdeal := (Formalism.L2.Col.mem_divs hπ w).1 hw
    have h2 : (T : 𝓞 D.host.E) ∈ w.asIdeal := hT ▸ w.asIdeal.mul_mem_right π' h1
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (T : 𝓞 D.host.F) ∈ w.asIdeal
    rw [hmap]; exact h2

end GlobalTheory.NormPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacesDvdNormIffUnderPrimesDvdStatement
open NumberField IsDedekindDomain Formalism.BasicNotions
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_dvd_norm_iff_under_primes_dvd : ∀ (D : Formalism.BasicNotions.D7) (π π' : 𝓞 D.host.E) (T : ℕ), (π' : D.host.E) = star (π : D.host.E) → π * π' = (T : 𝓞 D.host.E) → π ≠ 0 → ∀ x : HeightOneSpectrum (𝓞 D.host.F), (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x := by
  first | exact @GlobalTheory.NormPlaces.places_dvd_iff | exact GlobalTheory.NormPlaces.places_dvd_iff | (intros; apply GlobalTheory.NormPlaces.places_dvd_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineLatticeSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftModel

theorem isSelfDualC_lineLat : ∀ (D : D7) (S : HSp D) (ζ : Fin S.rank → D.host.E), IsLineVec S ζ → ∀ (𝔄 : FI D), (∀ d : D.host.E, d ∈ 𝔄 ↔ ∀ c ∈ 𝔄, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * (star ζ ⬝ᵥ S.gram *ᵥ ζ)) → IsSelfDualC S (GlobalTheory.SeeSaw.LiftModel.lineLat S ζ 𝔄) := by
  intro D S ζ hζ 𝔄 h𝔄
  classical
  obtain ⟨h1, hH⟩ := hζ
  haveI : Subsingleton (Fin S.rank) := by rw [h1]; infer_instance
  let i₀ : Fin S.rank := ⟨0, by omega⟩
  have all : ∀ i : Fin S.rank, i = i₀ := fun i => Subsingleton.elim _ _
  set z := ζ i₀ with hz
  set g := S.gram i₀ i₀ with hg
  have eH : star ζ ⬝ᵥ S.gram *ᵥ ζ = star z * (g * z) := by
    simp only [dotProduct, mulVec, Fintype.sum_subsingleton _ i₀, Pi.star_apply]
    rfl
  have z0 : z ≠ 0 := by
    intro h0; apply hH; rw [eH, h0]; simp
  have repr : ∀ y : Fin S.rank → D.host.E, y = (y i₀ / z) • ζ := by
    intro y; funext i; rw [all i]; simp [div_mul_cancel₀ _ z0, ← hz]
  have memΛ : ∀ y, y ∈ lineLat S ζ 𝔄 ↔ ∃ c ∈ 𝔄, c • ζ = y := by
    intro y
    simp [lineLat, Submodule.mem_map, LinearMap.toSpanSingleton_apply]
  have memΛ' : ∀ y, y ∈ lineLat S ζ 𝔄 ↔ y i₀ / z ∈ 𝔄 := by
    intro y
    rw [memΛ]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa [← hz, mul_div_cancel_right₀ _ z0] using hc
    · intro h
      exact ⟨_, h, (repr y).symm⟩
  have sum_eq : ∀ c d : D.host.E, ∑ i, ∑ j, star ((c • ζ) i) * S.gram i j * (d • ζ) j =
      star c * d * (star ζ ⬝ᵥ S.gram *ᵥ ζ) := by
    intro c d
    rw [eH]
    simp only [Fintype.sum_subsingleton _ i₀, Pi.smul_apply, smul_eq_mul, star_mul', ← hz, ← hg]
    ring
  have dual : ∀ y : Fin S.rank → D.host.E, y ∈ lineLat S ζ 𝔄 ↔
      ∀ x ∈ lineLat S ζ 𝔄, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * S.gram i j * y j := by
    intro y
    rw [memΛ', h𝔄]
    constructor
    · intro h x hx
      obtain ⟨c, hc, rfl⟩ := (memΛ x).1 hx
      obtain ⟨b, hb⟩ := h c hc
      refine ⟨b, ?_⟩
      conv_rhs => rw [repr y]
      rw [sum_eq, hb]
    · intro h c hc
      obtain ⟨b, hb⟩ := h (c • ζ) ((memΛ _).2 ⟨c, hc, rfl⟩)
      refine ⟨b, ?_⟩
      rw [hb]
      conv_lhs => rw [repr y]
      rw [sum_eq]
  refine ⟨⟨?_, ?_⟩, dual⟩
  · exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔄).map _
  · obtain ⟨c, hc, hc0⟩ : ∃ c ∈ 𝔄, c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h1m : (1 : D.host.E) ∈ 𝔄 := by
        rw [h𝔄]
        intro c hc
        exact ⟨0, by simp [hcon c hc]⟩
      exact one_ne_zero (hcon 1 h1m)
    have hcζ : c • ζ ∈ lineLat S ζ 𝔄 := (memΛ _).2 ⟨c, hc, rfl⟩
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.SeeSaw.LiftModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneIdeleWithSplitPlaceComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneIdeleWithSplitPlaceComponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

set_option maxHeartbeats 2000000 in
open GlobalTheory.FinPl.FrameLat in
theorem exists_normOneAt_pr (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (c₀ : k) (hc₀ : c₀ ≠ 0) :
    ∃ c : AE D, NormOneAt p.v c ∧ p.pr c = c₀ := by
  have hf : ∀ x : k, (p.e + cA D p.e) * p.sec x = p.sec x := fun x => (idem_iff p _).1 (sec_mem_idAt p x)
  have hcf : ∀ x : k, (p.e + cA D p.e) * cA D (p.sec x) = cA D (p.sec x) :=
    fun x => (idem_iff p _).1 (csec_mem_idAt (p := p) x)
  have hee : p.e * cA D p.e = 0 := p.split.2.1
  have hce : cA D p.e * p.e = 0 := cAe_mul_e p
  have hecs : ∀ x : k, p.e * cA D (p.sec x) = 0 := by
    intro x
    rw [← e_mul_sec p x, map_mul, ← mul_assoc, hee, zero_mul]
  have hsc : ∀ x y : k, p.sec x * cA D (p.sec y) = 0 := by
    intro x y
    rw [← e_mul_sec p x, mul_comm p.e, mul_assoc, hecs, mul_zero]
  have hprc : ∀ x : k, p.pr (cA D (p.sec x)) = 0 := by
    intro x
    have h1 : p.sec (p.pr (cA D (p.sec x))) = 0 := by rw [p.sec_pr, hecs]
    have h2 := congrArg p.pr h1
    rwa [p.pr_sec, map_zero] at h2
  have hcc : ∀ z : AE D, cA D (cA D z) = z := fun z => cA_cA z
  have he1 : p.sec 1 = p.e := sec_one p
  obtain ⟨f, hfdef⟩ : ∃ f : AE D, f = p.e + cA D p.e := ⟨_, rfl⟩
  have hfm : f ∈ idAt D (· = p.v) := hfdef ▸ sum_mem_idAt p
  have hff : f * f = f := by
    have := (idem_iff p f).1 hfm; rwa [← hfdef] at this
  have hf' : ∀ x : k, f * p.sec x = p.sec x := fun x => hfdef ▸ hf x
  have hcf' : ∀ x : k, f * cA D (p.sec x) = cA D (p.sec x) := fun x => hfdef ▸ hcf x

  obtain ⟨u, hu⟩ : ∃ u : AE D, u = 1 - f := ⟨_, rfl⟩
  have huf : u * f = 0 := by rw [hu, sub_mul, one_mul, hff, sub_self]
  have hus : ∀ x : k, u * p.sec x = 0 := by intro x; rw [← hf' x, ← mul_assoc, huf, zero_mul]
  have hucs : ∀ x : k, u * cA D (p.sec x) = 0 := by intro x; rw [← hcf' x, ← mul_assoc, huf, zero_mul]
  have huu : u * u = u := by nth_rewrite 2 [hu]; rw [mul_sub, mul_one, huf, sub_zero]
  have hcu : cA D u = u := by
    rw [hu, hfdef, map_sub, map_one, map_add (f := _), hcc, add_comm]
  refine ⟨u + p.sec c₀ + cA D (p.sec c₀⁻¹), ⟨?_, ?_⟩, ?_⟩
  · have hconj : cA D (u + p.sec c₀ + cA D (p.sec c₀⁻¹)) = u + cA D (p.sec c₀) + p.sec c₀⁻¹ := by
      rw [map_add (f := _), map_add (f := _), hcu, hcc]
    show _ * cA D _ = 1
    rw [hconj]
    have e1 : p.sec c₀ * p.sec c₀⁻¹ = p.e := by rw [← sec_mul p, mul_inv_cancel₀ hc₀, he1]
    have e2 : cA D (p.sec c₀⁻¹) * cA D (p.sec c₀) = cA D p.e := by
      rw [← map_mul (cA D), ← sec_mul p, inv_mul_cancel₀ hc₀, he1]
    have s1 : p.sec c₀ * u = 0 := by rw [mul_comm (p.sec c₀) u]; exact hus _
    have s2 : cA D (p.sec c₀⁻¹) * u = 0 := by rw [mul_comm (cA D (p.sec c₀⁻¹)) u]; exact hucs _
    have s3 : cA D (p.sec c₀⁻¹) * p.sec c₀⁻¹ = 0 := by rw [mul_comm (cA D (p.sec c₀⁻¹)) (p.sec c₀⁻¹)]; exact hsc _ _
    have s4 : p.sec c₀ * cA D (p.sec c₀) = 0 := hsc _ _
    have expand : (u + p.sec c₀ + cA D (p.sec c₀⁻¹)) * (u + cA D (p.sec c₀) + p.sec c₀⁻¹)
        = u * u + u * cA D (p.sec c₀) + u * p.sec c₀⁻¹ + p.sec c₀ * u + p.sec c₀ * cA D (p.sec c₀)
          + p.sec c₀ * p.sec c₀⁻¹ + cA D (p.sec c₀⁻¹) * u + cA D (p.sec c₀⁻¹) * cA D (p.sec c₀)
          + cA D (p.sec c₀⁻¹) * p.sec c₀⁻¹ := by ring
    rw [expand, huu, hucs, hus, s1, s4, e1, s2, e2, s3, hu, hfdef]
    ring
  · have : u + p.sec c₀ + cA D (p.sec c₀⁻¹) - 1 = -f + p.sec c₀ + cA D (p.sec c₀⁻¹) := by rw [hu]; ring
    rw [this]
    refine add_mem (add_mem (neg_mem hfm) (sec_mem_idAt p _)) (csec_mem_idAt (p := p) _)
  · rw [map_add (f := _), map_add (f := _), hprc, add_zero, hu, hfdef, map_sub, map_one, map_add (f := _), ← he1, hprc, p.pr_sec, p.pr_sec]
    ring

end GlobalTheory.Core.Mi.LatMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneIdeleWithSplitPlaceComponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normOneIdele_with_splitPlace_component : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (c₀ : k), c₀ ≠ 0 → ∃ c : AE D, NormOneAt p.v c ∧ p.pr c = c₀ := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_pr | exact GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_pr | (intros; apply GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_pr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesOfMatrixMemLevelZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

open GlobalTheory.StepData GlobalTheory.RootEx GlobalTheory.SymChain

namespace GlobalTheory.LevX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.LevX.conj_embX_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL n k) :
    ((_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas⁻¹ *
        _root_.GlobalTheory.RootEx.embX c g *
        (_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas).val.toBlocks₁₁ = g.val := by
  simp [_root_.GlobalTheory.StepData.typeFrame, _root_.GlobalTheory.StepData.LatFrame.bas,
    _root_.GlobalTheory.RootEx.embA, _root_.GlobalTheory.RootEx.embX, Matrix.fromBlocks_multiply]

attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.LevX.mem_KO_of_embX_mem_stabLat (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) {g : GL n k}
    (h : _root_.GlobalTheory.RootEx.embX c g ∈
      _root_.GlobalTheory.StepData.stabLat (_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas) :
    g ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  set b := (_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas with hb
  have hconj : b⁻¹ * _root_.GlobalTheory.RootEx.embX c g * b ∈
      _root_.GlobalTheory.SplitWeil.KO k (n ⊕ Fin c) := by
    unfold _root_.GlobalTheory.StepData.stabLat at h
    simpa [MulAut.conj_apply] using Subgroup.mem_comap.1 h
  obtain ⟨h₁, h₂⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff _).1 hconj
  have hinv : (b⁻¹ * _root_.GlobalTheory.RootEx.embX c g * b)⁻¹ =
      b⁻¹ * _root_.GlobalTheory.RootEx.embX c g⁻¹ * b := by
    simp [_root_.mul_inv_rev, mul_assoc]
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have e := congrFun (congrFun (_root_.GlobalTheory.LevX.conj_embX_val ϖ ord g) i) j
    rw [← e]
    exact h₁ (Sum.inl i) (Sum.inl j)
  · have e := congrFun (congrFun (_root_.GlobalTheory.LevX.conj_embX_val ϖ ord g⁻¹) i) j
    rw [← e]
    have := h₂ (Sum.inl i) (Sum.inl j)
    rw [hinv] at this
    exact this

attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private lemma mulVec_apply_mem_integer_of_entries_mem_integer {M : Matrix n n k}
    (hM : ∀ i j, M i j ∈ (ValuativeRel.valuation k).integer) {y : n → k}
    (hy : ∀ j, y j ∈ (ValuativeRel.valuation k).integer) (i : n) :
    (M *ᵥ y) i ∈ (ValuativeRel.valuation k).integer := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (hy j)

attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.LevX.smul_stdLat_of_mem_KO {g : GL n k} (h : g ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    g • _root_.GlobalTheory.SplitLat.stdLat k n = _root_.GlobalTheory.SplitLat.stdLat k n := by
  obtain ⟨h₁, h₂⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff _).1 h
  ext x
  change x ∈ (g : Matrix n n k) • _root_.GlobalTheory.SplitLat.stdLat k n ↔ _
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [_root_.GlobalTheory.SplitLat.mem_std] at hy ⊢
    intro i
    rw [Matrix.smul_eq_mulVec]
    exact mulVec_apply_mem_integer_of_entries_mem_integer h₁ hy i
  · intro hx
    refine ⟨((g⁻¹ : GL n k) : Matrix n n k) • x, ?_, ?_⟩
    · rw [_root_.GlobalTheory.SplitLat.mem_std] at hx ⊢
      intro i
      rw [Matrix.smul_eq_mulVec]
      exact mulVec_apply_mem_integer_of_entries_mem_integer h₂ hx i
    · rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end GlobalTheory.LevX
end
