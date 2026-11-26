module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacBridge

theorem rho_acts_locCo : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (γ : W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ →
    ∀ φ : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ
      (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v γ) φ) := by
  intro F _ _ W _ _ B κ _ co ψ v γ hγ φ r hr
  funext x
  set w := co.e γ with hw
  have hcomp : ∀ u : AF F, GlobalTheory.AdelicU.evFin F v u = 0 → u • w = 0 := fun u hu => by
    rw [hw, ← LinearEquiv.map_smul, hγ u hu, map_zero]
  have ha1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 k) := fun k u hu => by
    have := congrArg (fun z => z.1 k) (hcomp u hu)
    simpa using this
  have ha2 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 k) := fun k u hu => by
    have := congrArg (fun z => z.2 k) (hcomp u hu)
    simpa using this
  have at_pi : ∀ {z : κ → AF F}, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (z i)) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z :=
    fun h u hu => funext fun i => h i u hu
  have at_add : ∀ {a b : AF F}, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) b → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (a + b) :=
    fun ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  have at_mul_left : ∀ (a : AF F) {b : AF F}, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) b → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (a * b) :=
    by
      intro a b hb u hu
      rw [smul_eq_mul, mul_left_comm, show u * b = 0 from hb u hu, mul_zero]
  have at_sum : ∀ (s : Finset κ) {f : κ → AF F}, (∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (f i)) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (∑ i ∈ s, f i) := by
    intro s f h
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact fun u _ => smul_zero u
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact at_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  have evFin_invOf_two : GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  have hshift : r (x + w.1) = r x := hr.1 x w.1 (at_pi ha1)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, ← hw, hshift]
  have hat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
    at_add (at_sum _ fun k _ => at_mul_left _ (ha2 k))
      (at_mul_left _ (at_sum _ fun k _ => at_mul_left _ (ha2 k)))
  rw [GlobalTheory.StdVacuum.psi_eq_psiLoc ψ v _ hat, ← GlobalTheory.LatVac.psiAt_apply]
  have e1 : GlobalTheory.AdelicU.evFin F v (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) =
      (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        ⅟(2 : Fv F v) * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_add (f := _), map_sum, map_mul, evFin_invOf_two, hw]
    rfl
  have e2 : (fun i => GlobalTheory.AdelicU.evFin F v ((x + w.1) i)) =
      (fun i => GlobalTheory.AdelicU.evFin F v (x i)) + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    simp only [Pi.add_apply, map_add (f := _), hw]
    rfl
  rw [e1, e2, mul_assoc]

end GlobalTheory.VacBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (γ : W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ →
    ∀ φ : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ
      (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v γ) φ) := by
  first | exact @GlobalTheory.VacBridge.rho_acts_locCo | exact GlobalTheory.VacBridge.rho_acts_locCo | (intros; apply GlobalTheory.VacBridge.rho_acts_locCo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblTargetF

open GlobalTheory.WeilSchrodinger.DblTarget

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def dblG {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + n)) (Fin (n + n)) E :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (dbl J)

theorem isHermND_dblG {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsHermND σ J) :
    IsHermND σ (dblG J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] <;>
      simp [dbl, h.1 i j]
  · rw [dblG, Matrix.det_reindex_self, dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp [h.2]

theorem reindex_dbl_incM {n : ℕ} {J JA : Matrix (Fin n) (Fin n) E} (hA : JA = Jᵀ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (dbl (incM F JA)) = incM F (dblG J)ᵀ := by
  subst hA
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [dblG, incM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.transpose_apply, Matrix.map_apply] <;> simp [dbl]

abbrev coDbl {σ : E →ₐ[F] E} {nS nT : ℕ} {JT JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {ξ : AF F ⊗[F] E} (hA : JA = JTᵀ) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ) :
    Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) (κ ⊕ κ) :=
  reindexRows finSumFinEquiv (dblRows co) _ (reindex_dbl_incM hA)

theorem coDbl_rat {σ : E →ₐ[F] E} {nS nT : ℕ} {JT JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {ξ : AF F ⊗[F] E} (hA : JA = JTᵀ) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ ⊕ κ → F,
      (coDbl hA co).e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  intro x
  obtain ⟨y₁, z₁, h₁⟩ := hrat (x.submatrix (finSumFinEquiv ∘ Sum.inl) id)
  obtain ⟨y₂, z₂, h₂⟩ := hrat (x.submatrix (finSumFinEquiv ∘ Sum.inr) id)
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  have e₁ : ((incM F x).submatrix finSumFinEquiv id).submatrix Sum.inl id =
      incM F (x.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
  have e₂ : ((incM F x).submatrix finSumFinEquiv id).submatrix Sum.inr id =
      incM F (x.submatrix (finSumFinEquiv ∘ Sum.inr) id) := rfl
  rw [coDbl, reindexRows_e, dblRows_e, e₁, e₂, h₁, h₂]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;> simp

theorem isHeckeCharF_one : Formalism.IndefR.DatumF.IsHeckeCharF (1 : (AF F ⊗[F] E)ˣ →* Circle) :=
  ⟨continuous_const, fun _ => rfl⟩

theorem resEtaF_one_dbl (h2 : Module.finrank F E = 2) {χ : (AF F ⊗[F] E)ˣ →* Circle} {n : ℕ}
    (hr : Formalism.IndefR.DatumF.ResEtaF χ n) : Formalism.IndefR.DatumF.ResEtaF (1 : (AF F ⊗[F] E)ˣ →* Circle) (n + n) :=
  ⟨hr.1, fun η hη a => by
    have h4 := hη.2.2.1 (Formalism.IndefR.DatumF.idFF F E a)
    have h5 : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Formalism.IndefR.DatumF.idFF F E a) = a ^ 2 :=
      Units.ext (by
        change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) a.1) = _
        have : Nontrivial (AF F) :=
          (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F).nontrivial
        rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = η a ^ (n + n)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

def ugDbl {σ : E →ₐ[F] E} {n : ℕ} {JT JA : Matrix (Fin n) (Fin n) E} (hA : JA = JTᵀ) :
    UG (cA σ) (dbl (incM F JA)) →* UG (cA σ) (incM F (dblG JT)ᵀ) :=
  ugReindex finSumFinEquiv (reindex_dbl_incM hA)

theorem ugDbl_coe {σ : E →ₐ[F] E} {n : ℕ} {JT JA : Matrix (Fin n) (Fin n) E} (hA : JA = JTᵀ)
    (g : UG (cA σ) (dbl (incM F JA))) :
    (ugDbl hA g).1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv g.1.1 := rfl

end GlobalTheory.WeilSchrodinger.DblTargetF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStep

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base PsiUnr stepFac)

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}


open Classical in
def chs (G : GridData Lc sc) (i j : Fin D.R.m) (t : T) : Chars D.host.F D.host.E where
  α := Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)
  β := G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)
  S₀ := G.pl.S0
  Q := (twPl G t).image fun w => w.under (𝓞 D.host.F)

def BaseFits (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (t : T) (B : Base D.host.F D.host.E) : Prop :=
  B.ψ = W.ψ ∧ (chs G i j t).T ⊆ B.P ∧ (∀ v ∈ B.P, PsiUnr B.ψ v) ∧
    ∀ v : B.P, v.1 ∈ (chs G i j t).T → GlobalTheory.AdelicU.splitPrime (B.τ v) ∈ locPl G t

end GlobalTheory.SqStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.ChiGrid Formalism.L2.DIV

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace VecEx

section Frames

variable {K : Type} [Field K] [NumberField K] {n : ℕ}


omit [NumberField K] in
theorem mem_colLat_iff (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ colLat B ↔ ∃ c : Fin n → 𝓞 K, (B : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => (c j : K)) = x := by
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ?_
  have key : (∑ j, c j • fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ fun j => (c j : K) := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [key]

theorem isLattice_colLat (B : GL (Fin n) K) : Submodule.IsLattice K (colLat B) := by
  exact Submodule.IsLattice.of_fg K (Submodule.fg_span (Set.finite_range _))


omit [NumberField K] in
theorem form_frame [StarRing K] (G B : Matrix (Fin n) (Fin n) K) (hB : Bᴴ * G * B = 1) (c d : Fin n → K) :
    ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = ∑ i, star (c i) * d i := by
  have h1 : ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = star (B *ᵥ c) ⬝ᵥ (G *ᵥ (B *ᵥ d)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
    Matrix.one_mulVec]
  rfl

end Frames

variable {D : D7}

theorem isSelfDualC_colLat (V : HSp D) (B : GL (Fin V.rank) D.host.E)
    (hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * V.gram * B.1 = 1) : IsSelfDualC V (colLat B) := by
  classical
  have hB' : B.1ᴴ * V.gram * B.1 = 1 := hB
  refine ⟨isLattice_colLat B, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (mem_colLat_iff B x).1 hx
    obtain ⟨d, rfl⟩ := (mem_colLat_iff B y).1 hy
    rw [form_frame _ _ hB']
    have : ∑ i, star (c i : D.host.E) * (d i : D.host.E) ∈ Formalism.UG.intOE D.host.E :=
      sum_mem fun i _ => mul_mem (GlobalTheory.PlaceDatum.star_mem_intOE ⟨c i, rfl⟩) ⟨d i, rfl⟩
    exact this
  · have hy : B.1 *ᵥ ((B⁻¹).1 *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have : ∀ j, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ((B⁻¹).1 *ᵥ y) j := fun j => by
      obtain ⟨b, hb⟩ := h _ ((mem_colLat_iff B _).2 ⟨Pi.single j 1, rfl⟩)
      refine ⟨b, ?_⟩
      rw [hb, ← hy, form_frame _ _ hB', hy, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij]
      · simp
    choose b hb using this
    exact (mem_colLat_iff B y).2 ⟨b, by rw [show (fun j => (b j : D.host.E)) = _ from funext hb, hy]⟩

variable {S T : HSp D} {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_nsmul_latO (hS : ΛS.FG) (hT : ΛT.FG) (hS' : Submodule.IsFullLattice D.host.E ΛS')
    (hT' : Submodule.IsFullLattice D.host.E ΛT') : ∃ c : ℕ, 0 < c ∧ ∀ u : WO S T, u.map (infPart D) = 0 →
      u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) →
      c • u ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO hS' hT'
  obtain ⟨N, hN, h'⟩ := GlobalTheory.PlaceDatum.exists_den_latO hS hT
  refine ⟨N * K, Nat.mul_pos hN hK, fun t ht hu => ?_⟩
  rw [mul_nsmul]
  refine h _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · change infPart D (N • t i j) = 0
    rw [nsmul_eq_mul, RingHom.map_mul, show infPart D (t i j) = 0 from congrFun (congrFun ht i) j, mul_zero]
  · change toEAf D (N • t i j) ∈ _
    rw [nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact h' t hu i j

theorem isSBHalf_of_lattices (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT)
    (hS' : Submodule.IsFullLattice D.host.E ΛS') (hT' : Submodule.IsFullLattice D.host.E ΛT') {e : AE D}
    (he : infPart D e = 0) {Φ : WO S T → ℂ} (hΦ : IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ) :
    IsSBHalf e (latO S T ΛS' ΛT' fun _ => True) Φ := by
  obtain ⟨c, hc, h⟩ := exists_nsmul_latO hS.toIsLattice.fg hT.toIsLattice.fg hS' hT'
  obtain ⟨c', hc', h'⟩ := exists_nsmul_latO hS'.toIsLattice.fg hT'.toIsLattice.fg hS hT
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  have hh : ∀ (m : ℕ) (u : WO S T), IsHalf e u → IsHalf e (m • u) := fun m u hu =>
    (GlobalTheory.PlaceModel.isHalf_iff S T).2 (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hu) m)
  refine ⟨h1, c' * (c * k), by positivity, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · rw [mul_nsmul, mul_nsmul]
    exact h2 _ (nsmul_mem (h' u (GlobalTheory.PlaceDatum.infPart_of_half he hu') hu) c) (hh _ _ (hh _ _ hu')) t
  · rw [mul_nsmul', mul_nsmul']
    exact nsmul_mem (h _ (GlobalTheory.PlaceDatum.infPart_of_half he (hh _ _ (h1 t ht))) (h3 t ht)) c'

theorem exists_isThetaAt_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {sS sT}
    (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT) (hS' : IsSelfDualC S ΛS')
    (hT' : IsSelfDualC T ΛT') {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {f₀ Φ : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS' ΛT' f₀) (hΦ : IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ) :
    ∃ f, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS' ΛT' fun _ => True) 1 f₀ Φ f :=
  GlobalTheory.PlaceDatum.exists_isThetaAt hf.1 hS' hT' (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf.1 S T ΛS' ΛT' hS' hT' _ e he f₀ hf.2.theta hf.2.lat).1
    (isSBHalf_of_lattices hS hT
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS' hS')
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT' hT')
      (GlobalTheory.PlaceDatum.infPart_idemSum he) hΦ)

end VecEx

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem DefNode.selfDual (G : ChiGrid.GridData L sc) {μ0 : T} (hL : L.Is μ0) {X : Node} (h : DefNode D.R.m X) :
    IsSelfDualC (G.V X) (G.Λ X) := by
  rcases X with ⟨_ | i, j⟩ | i | j
  · exact (colY_isV D T L μ0 hL j h.2.le).sd
  · exact (G.isV (X := .grid (i + 1) j) ⟨h.1, h.2.le⟩ (by simp)).sd
  · exact h.elim
  · exact (G.isV (X := .top j) h (by simp)).sd

theorem Std.selfDual {G : ChiGrid.GridData L sc} {U : Set T} (N : Std G U) {X : Node} (h : DefNode D.R.m X) :
    IsSelfDualC (G.V X) (colLat (N.fr X)) :=
  VecEx.isSelfDualC_colLat _ _ (N.fr_on X h)

theorem Normal.hasVec_of_defPair {G : ChiGrid.GridData L sc} {W : G.Weil} {μ0 : T} (hL : L.Is μ0) {U : Set T} {N : Std G U}
    (Z : Normal W N) {t : T} {p : Pair T} (hp : DefPair D.R.m p) (d : FinDatum G t p) : Z.HasVec d := by
  obtain ⟨h1, h2⟩ := hp.nodes
  have hv := Z.vac_is p hp
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (h1.selfDual G hL)
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (h2.selfDual G hL)
  rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
  · exact VecEx.exists_isThetaAt_of_vac (S := G.pS (.chi i j)) (T := G.pT (.chi i j)) inferInstance inferInstance (isSelfDualC_neg (N.selfDual h2))
      (N.selfDual h1) d.e_is hv d.sb
  · exact hp.elim
  · exact hp.elim
  · exact VecEx.exists_isThetaAt_of_vac inferInstance inferInstance (N.selfDual h1)
      (N.selfDual h2) d.e_is hv d.sb

theorem hasVec {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (W : G.Weil) :
    ∀ μ0, L.Is μ0 → ∀ (U : Set T) (N : Std G U) (Z : Normal W N) (t : T), t ∈ U → ∀ p : Pair T, DefPair D.R.m p →
      ∀ d : FinDatum G t p, Z.HasVec d :=
  fun _ hL _ _ Z _ _ _ hp d => Z.hasVec_of_defPair hL hp d

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacIso

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW t (cA σ x) = piW (t.comp σ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a e => rfl

theorem eq_zero_of_at_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v)
    {z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) (h1 : piW τ z = 0) (h2 : piW (τ.comp σ) z = 0) : z = 0 := by
  have hc : compFin F E v z = 0 :=
    GlobalTheory.AdelicU.split_ext h τ (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  have e := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at e
  rw [e, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  change GlobalTheory.EmbChart.tensAt E v ((1 : Fv F v) ⊗ₜ[F] (1 : E)) * z = 0
  rw [GlobalTheory.EmbChart.tensAt_mul_right, hc, mul_zero, map_zero]

theorem symp_self_eq_zero : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (u : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
    (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∨ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) →
    ∀ ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E),
      symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u = 0 := by
  intro D a a' Bs Γ X om om' hTr u hu hpi ξ
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := hTr.base.cm
  set z := GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u with hzdef
  have hat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) z := by
    intro c hc
    have hij : ∀ i j, c • u i j = 0 := fun i j => by
      have := congrFun (congrFun (hu c hc) i) j
      simpa using this
    simp only [hzdef, GlobalTheory.WeilM.hTens, Finset.smul_sum, ← smul_mul_assoc, hij, zero_mul, Finset.sum_const_zero]
  have first : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁, (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (u i j) = 0) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z = 0 := by
    intro t ht
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hzdef, GlobalTheory.WeilM.hTens, map_sum, map_mul, ht, zero_mul, Finset.sum_const_zero]
  have last : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁,
      (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp D.sp.cm.sig) (u i j) = 0) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z = 0 := by
    intro t ht
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hzdef, GlobalTheory.WeilM.hTens, map_sum, map_mul, GlobalTheory.VacIso.piW_cA, ht, mul_zero, Finset.sum_const_zero]
  have hz0 : z = 0 := by
    rcases hpi with h0 | h0
    · have h0' : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁ (u i j) = 0 := fun i j => by
        simpa using congrFun (congrFun h0 i) j
      refine GlobalTheory.VacIso.eq_zero_of_at_split hcm Bs.τ₁ hat (first _ h0') (last _ ?_)
      rw [GlobalTheory.AdelicU.comp_conj_conj hcm]; exact h0'
    · have h0' : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig) (u i j) = 0 := fun i j => by
        simpa using congrFun (congrFun h0 i) j
      exact GlobalTheory.VacIso.eq_zero_of_at_split hcm Bs.τ₁ hat (last _ h0') (first _ h0')
  simp only [GlobalTheory.WeilM.symp, ← hzdef, hz0, mul_zero, map_zero]

end GlobalTheory.VacIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupportedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceSymplectic_self_zero_splitSupported : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (u : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
    (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∨ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) →
    ∀ ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E),
      symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u = 0 := by
  first | exact @GlobalTheory.VacIso.symp_self_eq_zero | exact GlobalTheory.VacIso.symp_self_eq_zero | (intros; apply GlobalTheory.VacIso.symp_self_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LatVac.DualLoc

variable {F : Type} [Field F] [NumberField F]

theorem form_smul_left {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (u : AF F) (z γ : W) : B (u • z) γ = u * B z γ := by
  rw [co.form, co.form, map_smul]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_sub]

theorem at_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {z : W}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) (γ : W) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (B z γ) := by
  intro u hu
  rw [smul_eq_mul, ← form_smul_left co, hz u hu, co.form]
  simp

theorem evFin_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (z γ : W) :
    evFin F v (B z γ) = (GlobalTheory.LatVac.locCo co v z).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 -
      (GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v z).2 := by
  rw [co.form]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sub, map_sum, map_mul]
  rfl

theorem psi_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ) {z : W}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) (γ : W) :
    ψ (B z γ) = GlobalTheory.LatVac.psiAt ψ v ((GlobalTheory.LatVac.locCo co v z).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 -
      (GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v z).2) := by
  rw [GlobalTheory.VacIndic.psi_of_at ψ (at_form co v hz γ), ← evFin_form co v z γ]
  rfl

theorem map_selfDual : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Λ : AddSubgroup W), (∀ γ ∈ Λ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ) →
    (∀ z : W, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1)) →
    ∀ w : (κ → Fv F v) × (κ → Fv F v), w ∈ Λ.map (GlobalTheory.LatVac.locCo co v) ↔
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), GlobalTheory.LatVac.psiAt ψ v (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
  intro F _ _ v W _ _ B κ _ co ψ Λ hat hdual w
  constructor
  · rintro ⟨z, hz, rfl⟩ l ⟨γ, hγ, rfl⟩
    rw [← psi_form co v ψ (hat z hz) γ]
    exact (hdual z (hat z hz)).1 hz γ hγ
  · intro hw
    obtain ⟨p, hp⟩ : ∃ p : (κ → AF F) × (κ → AF F),
        p = (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) := ⟨_, rfl⟩
    have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (co.e.symm p) := by
      intro u hu
      have hp0 : u • p = 0 := by
        subst hp
        refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
        · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
        · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
      rw [← map_smul, hp0, map_zero]
    have hloc : GlobalTheory.LatVac.locCo co v (co.e.symm p) = w := by
      subst hp
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · show evFin F v ((co.e (co.e.symm _)).1 k) = w.1 k
        rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
      · show evFin F v ((co.e (co.e.symm _)).2 k) = w.2 k
        rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)
    have hz : co.e.symm p ∈ Λ := (hdual _ hzat).2 fun γ hγ => by
      rw [psi_form co v ψ hzat γ, hloc]
      exact hw _ ⟨γ, hγ, rfl⟩
    exact ⟨_, hz, hloc⟩

end GlobalTheory.LatVac.DualLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_localImage_latticeSupportedAtPlace : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Λ : AddSubgroup W), (∀ γ ∈ Λ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ) →
    (∀ z : W, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1)) →
    ∀ w : (κ → Fv F v) × (κ → Fv F v), w ∈ Λ.map (GlobalTheory.LatVac.locCo co v) ↔
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), GlobalTheory.LatVac.psiAt ψ v (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
  first | exact @GlobalTheory.LatVac.DualLoc.map_selfDual | exact GlobalTheory.LatVac.DualLoc.map_selfDual | (intros; apply GlobalTheory.LatVac.DualLoc.map_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchrSBFin

theorem isLocallyConstant_addChar {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  obtain ⟨U₀, hU₀⟩ := GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  filter_upwards [U₀.mem_nhds_zero] with s hs
  rw [AddChar.map_add_eq_mul, hU₀ s hs, mul_one]

theorem schr_mem_SB_of {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (ψ : AddChar K ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ]
    (w : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → K)) :
    GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → K) := by
  obtain ⟨hlc, hcs⟩ := hφ
  have h1 : IsLocallyConstant fun x : κ → K => ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) :=
    (isLocallyConstant_addChar ψ hψ).comp_continuous
      ((continuous_id.dotProduct continuous_const).add continuous_const)
  have h2 : IsLocallyConstant fun x : κ → K => φ (x + w.1) := hlc.comp_continuous (continuous_id.add continuous_const)
  have h3 : HasCompactSupport fun x : κ → K => φ (x + w.1) := hcs.comp_homeomorph (Homeomorph.addRight w.1)
  exact ⟨h1.mul h2, h3.mul_left⟩

theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ v ψ hψ κ _ w φ hφ
  exact schr_mem_SB_of ψ hψ w φ hφ

end GlobalTheory.SchrSBFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_mem_schwartzBruhat_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  first | exact @GlobalTheory.SchrSBFin.schr_mem_SB | exact GlobalTheory.SchrSBFin.schr_mem_SB | (intros; apply GlobalTheory.SchrSBFin.schr_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.BotFormula

theorem toFinE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = GlobalTheory.CuspRep.conjFin (D.host.conj : D.host.E ≃+* D.host.E) (toFinE D y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul x a =>
    change GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] D.host.conj x) =
      GlobalTheory.CuspRep.conjFin _ (GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] x))
    rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_mul,
      GlobalTheory.DefU.ClassFin.conjFin_adMap _ (fun q => D.host.conj.commutes q), GlobalTheory.CuspRep.conjFin_algebraMap]
    rfl

def toAfE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* TensorProduct D.host.F (Af D.host.F) D.host.E :=
  (toFinE D).trans (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm

theorem toAfE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toAfE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = sigR (Af D.host.F) D.sp.cm.sig (toAfE D y) := by
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [GlobalTheory.DefU.ClassFin.finAdEquiv_sigR D.sp.cm.sig (D.host.conj : D.host.E ≃+* D.host.E)
    (fun x => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D x)]
  simp only [toAfE, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact toFinE_sgA D y

theorem exists_isFinPt_of_gram_one : ∀ {D : D7} (WW : HSp D), WW.gram = 1 → ∀ {n : ℕ} (h : GA D n), WW.rank = n →
    ∃ g : GA D WW, GlobalTheory.BotFormula.IsFinPt WW g h := by
  intro D WW hG n h hr
  subst hr
  let x' : GL (Fin WW.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := Formalism.UG.bc (toAfE D).toRingHom h.1
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * h.1 = 1 := by
    have h2 := h.2
    change Formalism.UG.cT _ (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hx' : x' ∈ HR (Af D.host.F) D.sp.cm.sig WW.gram := by
    show Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) *
      JR (Af D.host.F) WW.gram * (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) = JR (Af D.host.F) WW.gram
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact GlobalTheory.DefU.ClassFin.unitary_map (toAfE D).toRingHom (Formalism.MainNotions.StandardLatticesGL3.sgA D) _ (toAfE_sgA D) _ hh
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue WW 1 x' (one_mem _) hx'
  refine ⟨k, k1, rfl, fun i j => ?_⟩
  rw [k2]
  exact (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _

end GlobalTheory.BotFormula
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne : ∀ {D : D7} (WW : HSp D), WW.gram = 1 → ∀ {n : ℕ} (h : GA D n), WW.rank = n →
    ∃ g : GA D WW, GlobalTheory.BotFormula.IsFinPt WW g h := by
  first | exact @GlobalTheory.BotFormula.exists_isFinPt_of_gram_one | exact GlobalTheory.BotFormula.exists_isFinPt_of_gram_one | (intros; apply GlobalTheory.BotFormula.exists_isFinPt_of_gram_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LatBound

theorem exists_mul_mem_integers {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {T : Type} [Fintype T] (w : T → Fv F v) :
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ t, c * w t ∈ v.adicCompletionIntegers F := by
  classical
  have key : ∀ x : Fv F v, ∃ c : Fv F v, c ≠ 0 ∧ c ∈ v.adicCompletionIntegers F ∧
      c * x ∈ v.adicCompletionIntegers F := by
    intro x
    by_cases hx : x ∈ v.adicCompletionIntegers F
    · exact ⟨1, one_ne_zero, one_mem _, by simpa using hx⟩
    · have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
      refine ⟨x⁻¹, inv_ne_zero hx0, ?_, by rw [inv_mul_cancel₀ hx0]; exact one_mem _⟩
      exact ((v.adicCompletionIntegers F).mem_or_inv_mem x).resolve_left hx
  choose cw hcw0 hcwO hcw using key
  refine ⟨∏ t, cw (w t), Finset.prod_ne_zero_iff.2 fun t _ => hcw0 _, fun t => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun t => cw (w t)) (Finset.mem_univ t), mul_comm (cw (w t)), mul_assoc]
  exact mul_mem (prod_mem fun t' _ => hcwO _) (hcw _)

theorem locCo_latAtV_bounded : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {B : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ), X.L.IsLattice E → Y.L.IsLattice E →
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ i,
      c * (GlobalTheory.LatVac.locCo co v γ).1 i ∈ v.adicCompletionIntegers F ∧
      c * (GlobalTheory.LatVac.locCo co v γ).2 i ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ n d X Y v B κ _ co hX hY
  obtain ⟨M, _, g, hg⟩ := GlobalTheory.LatParam.latAtV_param X Y hX hY v
  obtain ⟨c, hc0, hc⟩ := exists_mul_mem_integers v
    (fun t : Bool × M × κ => if t.1 then (GlobalTheory.LatVac.locCo co v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g t.2.1))).1 t.2.2
      else (GlobalTheory.LatVac.locCo co v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g t.2.1))).2 t.2.2)
  have hsmul : ∀ (t : Fv F v) z, GlobalTheory.LatVac.locCo co v (GlobalTheory.EmbChart.atPlace v t • z) =
      t • GlobalTheory.LatVac.locCo co v z := by
    intro t z
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
    ext k <;> simp [smul_eq_mul, map_mul, GlobalTheory.EmbChart.evFin_atPlace]
  refine ⟨c, hc0, fun γ hγ i => ?_⟩
  obtain ⟨a, rfl⟩ := (hg γ).1 hγ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hsmul, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  constructor
  · refine sum_mem fun m _ => ?_
    rw [mul_left_comm]
    exact mul_mem (a m).2 (by simpa using hc (true, m, i))
  · refine sum_mem fun m _ => ?_
    rw [mul_left_comm]
    exact mul_mem (a m).2 (by simpa using hc (false, m, i))

end GlobalTheory.LatBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBoundedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLattice_localDarbouxCoords_bounded : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {B : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ), X.L.IsLattice E → Y.L.IsLattice E →
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ i,
      c * (GlobalTheory.LatVac.locCo co v γ).1 i ∈ v.adicCompletionIntegers F ∧
      c * (GlobalTheory.LatVac.locCo co v γ).2 i ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.LatBound.locCo_latAtV_bounded | exact GlobalTheory.LatBound.locCo_latAtV_bounded | (intros; apply GlobalTheory.LatBound.locCo_latAtV_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormDerivativeModerateGrowth
open NumberField GlobalTheory.CuspRep

theorem GlobalTheory.CuspStab.lie_growth : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ → ∀ g : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖(GlobalTheory.CuspRep.lie E a X φ).1 (g * GlobalTheory.CuspRep.infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N :=
  GlobalTheory.AutGrowth.lie_growth_of_finite
end
