module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SesquilinearLevelZeroPairing
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PairLevZeroIndep
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormPositivity
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5.HerA
open scoped ComplexConjugate

section Cls

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure SesqCls (U : Submodule ℂ V) (β : V → V → ℂ) : Prop where
  herm : ∀ x ∈ U, ∀ y ∈ U, β y x = conj (β x y)
  add_left : ∀ x ∈ U, ∀ x' ∈ U, ∀ y ∈ U, β (x + x') y = β x y + β x' y
  smul_left : ∀ x ∈ U, ∀ y ∈ U, ∀ c : ℂ, β (c • x) y = c * β x y

variable {U : Submodule ℂ V} {β : V → V → ℂ}

theorem SesqCls.add_right (hβ : SesqCls U β) {x y y' : V} (hx : x ∈ U) (hy : y ∈ U) (hy' : y' ∈ U) :
    β x (y + y') = β x y + β x y' := by
  rw [hβ.herm _ (U.add_mem hy hy') _ hx, hβ.add_left _ hy _ hy' _ hx, map_add (f := _), ← hβ.herm _ hy _ hx,
    ← hβ.herm _ hy' _ hx]

theorem SesqCls.smul_right (hβ : SesqCls U β) {x y : V} (hx : x ∈ U) (hy : y ∈ U) (c : ℂ) :
    β x (c • y) = conj c * β x y := by
  rw [hβ.herm _ (U.smul_mem c hy) _ hx, hβ.smul_left _ hy _ hx, map_mul, ← hβ.herm _ hy _ hx]

theorem SesqCls.zero_left (hβ : SesqCls U β) {y : V} (hy : y ∈ U) : β 0 y = 0 := by
  have h := hβ.smul_left 0 U.zero_mem y hy 0
  rwa [zero_smul, zero_mul] at h

theorem SesqCls.sum_left (hβ : SesqCls U β) {ι : Type*} (s : Finset ι) (f : ι → V) (hf : ∀ i, f i ∈ U)
    {y : V} (hy : y ∈ U) : β (∑ i ∈ s, f i) y = ∑ i ∈ s, β (f i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, hβ.zero_left hy]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hβ.add_left _ (hf a) _ (U.sum_mem fun i _ => hf i) _ hy, ih]

theorem SesqCls.sum_right (hβ : SesqCls U β) {ι : Type*} (s : Finset ι) (f : ι → V) (hf : ∀ i, f i ∈ U)
    {x : V} (hx : x ∈ U) : β x (∑ i ∈ s, f i) = ∑ i ∈ s, β x (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, hβ.herm _ U.zero_mem _ hx, hβ.zero_left hx, map_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hβ.add_right hx (hf a) (U.sum_mem fun i _ => hf i), ih]

def adjB (U : Submodule ℂ V) (β : V → V → ℂ) (hβ : SesqCls U β) : StarSubalgebra ℂ (Q.Pr V) where
  carrier := {a | (∀ x ∈ U, a.1 x ∈ U) ∧ (∀ x ∈ U, a.2.unop x ∈ U) ∧
    ∀ x ∈ U, ∀ y ∈ U, β (a.1 x) y = β x (a.2.unop y)}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun x hx => ha1 _ (hb1 x hx), fun x hx => hb2 _ (ha2 x hx), fun x hx y hy => ?_⟩
    change β (a.1 (b.1 x)) y = β x (b.2.unop (a.2.unop y))
    rw [ha _ (hb1 x hx) y hy, hb x hx _ (ha2 y hy)]
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun x hx => U.add_mem (ha1 x hx) (hb1 x hx), fun x hx => U.add_mem (ha2 x hx) (hb2 x hx),
      fun x hx y hy => ?_⟩
    change β (a.1 x + b.1 x) y = β x (a.2.unop y + b.2.unop y)
    rw [hβ.add_left _ (ha1 x hx) _ (hb1 x hx) _ hy, hβ.add_right hx (ha2 y hy) (hb2 y hy), ha x hx y hy,
      hb x hx y hy]
  algebraMap_mem' := by
    intro c
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx y hy => ?_⟩
    · show (algebraMap ℂ (Module.End ℂ V) c) x ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem c hx
    · show (algebraMap ℂ (Module.End ℂ V) (conj c)) x ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem _ hx
    · show β ((algebraMap ℂ (Module.End ℂ V) c) x) y = β x ((algebraMap ℂ (Module.End ℂ V) (conj c)) y)
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, hβ.smul_left x hx y hy,
        hβ.smul_right hx hy, Complex.conj_conj]
  star_mem' := by
    rintro a ⟨ha1, ha2, ha⟩
    refine ⟨ha2, ha1, fun x hx y hy => ?_⟩
    show β (a.2.unop x) y = β x (a.1 y)
    rw [hβ.herm _ (ha1 y hy) _ hx, ha y hy x hx]
    exact hβ.herm _ hy _ (ha2 x hx)

theorem mem_adjB {hβ : SesqCls U β} {a : Q.Pr V} :
    a ∈ adjB U β hβ ↔ (∀ x ∈ U, a.1 x ∈ U) ∧ (∀ x ∈ U, a.2.unop x ∈ U) ∧
      ∀ x ∈ U, ∀ y ∈ U, β (a.1 x) y = β x (a.2.unop y) := Iff.rfl

end Cls

section Pair

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]
variable {U : Submodule ℂ V} {β : V → V → ℂ}

def pairS (β : V → V → ℂ) (X X' : Ix S → V) : ℂ := ∑ z, β (X z) (X' z)

def InU (U : Submodule ℂ V) (X : Ix S → V) : Prop := ∀ z, X z ∈ U

theorem blockMulVec_apply_mem {M : SlopeTestRemainingChoices S (Q.Pr V)} (hM : ∀ a b, ∀ x ∈ U, (M a b).1 x ∈ U) {X : Ix S → V} (hX : InU U X) :
    InU U (actP M X) := fun a => U.sum_mem fun b _ => hM a b _ (hX b)

theorem pairS_adj (hβ : SesqCls U β) (M : SlopeTestRemainingChoices S (Q.Pr V)) (hM : M ∈ entSub (adjB U β hβ)) (X Y : Ix S → V)
    (hX : InU U X) (hY : InU U Y) : pairS β X (actP M Y) = pairS β (actP (star M) X) Y := by
  have hM2 : ∀ a b, M a b ∈ adjB U β hβ := hM
  have hM' := fun a b => (mem_adjB (hβ := hβ)).1 (hM2 a b)
  have key : ∀ z b, β (((star M) z b).1 (X b)) (Y z) = β (X b) ((M b z).1 (Y z)) := by
    intro z b
    have h1 : (M b z).2.unop (X b) ∈ U := (hM' b z).2.1 _ (hX b)
    have h2 : (M b z).1 (Y z) ∈ U := (hM' b z).1 _ (hY z)
    show β ((M b z).2.unop (X b)) (Y z) = _
    rw [hβ.herm _ (hY z) _ h1, ← (hM' b z).2.2 _ (hY z) _ (hX b), ← hβ.herm _ h2 _ (hX b)]
  unfold pairS actP
  rw [Finset.sum_congr rfl fun z _ => hβ.sum_right Finset.univ (fun b => (M z b).1 (Y b))
    (fun b => (hM' z b).1 _ (hY b)) (hX z)]
  rw [Finset.sum_congr rfl fun z _ => hβ.sum_left Finset.univ (fun b => ((star M) z b).1 (X b))
    (fun b => (hM' b z).2.1 _ (hX b)) (hY z)]
  simp_rw [key]
  exact Finset.sum_comm

theorem pairS_smul_left (hβ : SesqCls U β) (c : ℂ) (X Y : Ix S → V) (hX : InU U X) (hY : InU U Y) :
    pairS β (c • X) Y = c * pairS β X Y := by
  unfold pairS
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => hβ.smul_left _ (hX z) _ (hY z) c

theorem smul_blockMulVec (M : SlopeTestRemainingChoices S (Q.Pr V)) (c : ℂ) (X : Ix S → V) : actP (c • M) X = c • actP M X := by
  funext a
  unfold actP
  rw [Pi.smul_apply, Finset.smul_sum]
  rfl

def frmU (hβ : SesqCls U β) (M : SlopeTestRemainingChoices S (Q.Pr V)) (hM : ∀ a b, ∀ x ∈ U, (M a b).1 x ∈ U) :
    F7.Sesq (Submodule.pi Set.univ (fun _ : Ix S => U)) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun X X' => pairS β (actP M X.1) X'.1)
    (fun X X' Y => by
      have hX : InU U X.1 := fun z => X.2 z (Set.mem_univ z)
      have hX' : InU U X'.1 := fun z => X'.2 z (Set.mem_univ z)
      have hY : InU U Y.1 := fun z => Y.2 z (Set.mem_univ z)
      show pairS β (actP M (X.1 + X'.1)) Y.1 = _
      rw [blockMulVec_add]
      unfold pairS
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => hβ.add_left _ (blockMulVec_apply_mem hM hX z) _ (blockMulVec_apply_mem hM hX' z) _ (hY z))
    (fun c X Y => by
      have hX : InU U X.1 := fun z => X.2 z (Set.mem_univ z)
      have hY : InU U Y.1 := fun z => Y.2 z (Set.mem_univ z)
      show pairS β (actP M (c • X.1)) Y.1 = c • pairS β (actP M X.1) Y.1
      rw [actP_smul, smul_eq_mul]
      exact pairS_smul_left hβ c _ _ (blockMulVec_apply_mem hM hX) hY)
    (fun X Y Y' => by
      have hX : InU U X.1 := fun z => X.2 z (Set.mem_univ z)
      have hY : InU U Y.1 := fun z => Y.2 z (Set.mem_univ z)
      have hY' : InU U Y'.1 := fun z => Y'.2 z (Set.mem_univ z)
      show pairS β (actP M X.1) (Y.1 + Y'.1) = _
      unfold pairS
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => hβ.add_right (blockMulVec_apply_mem hM hX z) (hY z) (hY' z))
    (fun c X Y => by
      have hX : InU U X.1 := fun z => X.2 z (Set.mem_univ z)
      have hY : InU U Y.1 := fun z => Y.2 z (Set.mem_univ z)
      show pairS β (actP M X.1) (c • Y.1) = (starRingEnd ℂ) c • pairS β (actP M X.1) Y.1
      unfold pairS
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => hβ.smul_right (blockMulVec_apply_mem hM hX z) (hY z) c)

theorem cs_U (hβ : SesqCls U β) (M : SlopeTestRemainingChoices S (Q.Pr V)) (hM : ∀ a b, ∀ x ∈ U, (M a b).1 x ∈ U)
    (hP : ∀ X : Ix S → V, InU U X → 0 ≤ (pairS β (actP M X) X).re ∧ (pairS β (actP M X) X).im = 0)
    (X X' : Ix S → V) (hX : InU U X) (hX' : InU U X') :
    ‖pairS β (actP M X) X'‖ ^ 2 ≤ (pairS β (actP M X) X).re * (pairS β (actP M X') X').re := by
  let W := Submodule.pi Set.univ (fun _ : Ix S => U)
  let x : W := ⟨X, fun z _ => hX z⟩
  let x' : W := ⟨X', fun z _ => hX' z⟩
  have := Formalism.FourierDecayAlt.P.GramProductIdentities.cs_of_pos (frmU hβ M hM) (fun m => hP m.1 fun z => m.2 z (Set.mem_univ z)) x x'
  exact this

end Pair

section Ent

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem word_transfer_mem_entrywise (QQ : ℂ → M2 A) (w : List (Letter ℂ S)) (Y : ℂ) (hQ : ∀ a b, QQ Y a b ∈ 𝒜) :
    E2 𝒜 (TTw QQ w Y) := by
  induction w with
  | nil =>
    intro a b
    show io (QQ Y a b) ∈ entSub 𝒜
    exact io_mem (hQ a b)
  | cons l w ih =>
    by_cases hp : l.plus
    · rw [TTw, if_pos hp]; exact entries_mem_mul ih (reflection_entries_mem _ _)
    · rw [TTw, if_neg hp]; exact entries_mem_mul (reflection_transpose_entries_mem _ _) ih

theorem rrw_mem_at (QQ : ℂ → M2 A) (w : List (Letter ℂ S)) (hw : ∀ l ∈ w, ∀ a b, QQ l.pt a b ∈ 𝒜) :
    RRw QQ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [RRw]
    refine (entSub 𝒜).mul_mem (ih fun l' hl' => hw l' (by simp [hl'])) (ins_mem _ ?_)
    have hT := word_transfer_mem_entrywise QQ w l.pt (hw l (by simp))
    split_ifs
    · exact hT
    · exact entries_mem_transpose hT

theorem symplectic_form_mem_entrywise : E2 𝒜 (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) := by
  unfold Formalism.YangianSpanCharacter.T.J
  exact entries_mem_of_four (entSub 𝒜).zero_mem (entSub 𝒜).one_mem (neg_mem (entSub 𝒜).one_mem) (entSub 𝒜).zero_mem

theorem ps_mem_at (QQ : ℂ → M2 A) (q : ℂ → ℂ) (w : List (Letter ℂ S)) (L : List (Letter ℂ S))
    (hL : ∀ l ∈ L, ∀ a b, (l.plus = true → QQ (l.pt + 1) a b ∈ 𝒜) ∧ (l.plus = false → QQ (l.pt - 1) a b ∈ 𝒜)) :
    Ps QQ q w L ∈ entSub 𝒜 := by
  induction L with
  | nil => exact (entSub 𝒜).one_mem
  | cons l L ih =>
    rw [Ps]
    refine (entSub 𝒜).mul_mem ?_ (ih fun l' hl' => hL l' (by simp [hl']))
    split_ifs with hp
    · unfold PsiP
      refine ins_mem _ ?_
      intro i j
      rw [Matrix.neg_apply]
      refine neg_mem ((entSub 𝒜).smul_mem ?_ _)
      exact entries_mem_mul symplectic_form_mem_entrywise (entries_mem_transpose (word_transfer_mem_entrywise QQ _ _ (fun a b => (hL l (by simp) a b).1 hp))) i j
    · unfold PsiM
      refine ins_mem _ ?_
      intro i j
      refine (entSub 𝒜).smul_mem ?_ _
      exact entries_mem_mul symplectic_form_mem_entrywise (word_transfer_mem_entrywise QQ _ _ (fun a b => (hL l (by simp) a b).2 (by simpa using hp))) i j

end Ent

section DK

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]
variable {U : Submodule ℂ V} {β : V → V → ℂ}

theorem dk_partial (hβ : SesqCls U β) (QQ : ℂ → M2 (Q.Pr V)) (q : ℂ → ℂ) (w L : List (Letter ℂ S))
    (hS : IsStart QQ q) (hD : FormPairingAction.DKHyp q w L)
    (hPs : Ps QQ q w L ∈ entSub (adjB U β hβ))
    (hRR : ∀ a b, ∀ x ∈ U, (RRw QQ (L ++ w) a b).1 x ∈ U)
    (hPos : ∀ X : Ix S → V, InU U X → 0 ≤ (pairS β (actP (RRw QQ (L ++ w)) X) X).re ∧
      (pairS β (actP (RRw QQ (L ++ w)) X) X).im = 0)
    (X₁ X₂ : Ix S → V) (h1 : InU U X₁) (h2 : InU U X₂) :
    (pairS β (actP (RRw QQ (L ++ w)) X₁) X₁ * pairS β (actP (RRw QQ (L.map dl ++ w)) X₂) X₂ /
        (L.map fun l => qw q w l.pt).prod).im = 0 ∧
    ‖pairS β (actP (JL L * RRw QQ w) X₁) X₂‖ ^ 2 ≤
      (pairS β (actP (RRw QQ (L ++ w)) X₁) X₁ * pairS β (actP (RRw QQ (L.map dl ++ w)) X₂) X₂ /
        (L.map fun l => qw q w l.pt).prod).re := by
  have hok := Formalism.FourierDecayAlt.P.DualKernelLemmas.dkDualOK S q w L hD
  have hdl := Formalism.FourierDecayAlt.P.duality_list_holds ℂ (Q.Pr V) S QQ q w L hS hD.2.1 hD.2.2.1 hok
  have hkap := Formalism.FourierDecayAlt.P.kappa_formula_holds ℂ S q w L hD.2.1 hD.2.2.1 hok
  have h4 := Formalism.FourierDecayAlt.P.GramProductIdentities.dkStep4 S q w L hD.1
  have hk0 : kap q w L ≠ 0 := hdl.2.1
  have hprod : (L.map fun l => qw q w l.pt).prod = kap q w L := by rw [hkap, h4]
  have hPsU : ∀ a b, ∀ x ∈ U, (Ps QQ q w L a b).1 x ∈ U := fun a b x hx => (hPs a b).1 x hx
  have hsPs : star (Ps QQ q w L) ∈ entSub (adjB U β hβ) := star_mem_entSub hPs
  have hsPsU : ∀ a b, ∀ x ∈ U, (star (Ps QQ q w L) a b).1 x ∈ U := fun a b x hx => (hsPs a b).1 x hx
  have hY : InU U (actP (Ps QQ q w L) X₂) := blockMulVec_apply_mem hPsU h2
  have hR1 : InU U (actP (RRw QQ (L ++ w)) X₁) := blockMulVec_apply_mem hRR h1
  have hR2 : InU U (actP (RRw QQ (L ++ w)) (actP (Ps QQ q w L) X₂)) := blockMulVec_apply_mem hRR hY
  have e1 : pairS β (actP (JL L * RRw QQ w) X₁) X₂ =
      pairS β (actP (RRw QQ (L ++ w)) X₁) (actP (Ps QQ q w L) X₂) := by
    rw [← hdl.2.2.1, polyAction_mul, pairS_adj hβ _ hPs _ _ hR1 h2]
  have hm : pairS β (actP (RRw QQ (L.map dl ++ w)) X₂) X₂ = kap q w L *
      pairS β (actP (RRw QQ (L ++ w)) (actP (Ps QQ q w L) X₂)) (actP (Ps QQ q w L) X₂) := by
    have e : RRw QQ (L.map dl ++ w) = kap q w L • (star (Ps QQ q w L) * RRw QQ (L ++ w) * Ps QQ q w L) := by
      rw [hdl.2.2.2.1, smul_smul, mul_inv_cancel₀ hk0, one_smul]
    rw [e, smul_blockMulVec, polyAction_mul, polyAction_mul, pairS_smul_left hβ _ _ _ (blockMulVec_apply_mem hsPsU hR2) h2,
      pairS_adj hβ _ hPs _ _ hR2 h2]
  rw [hprod, hm, e1]
  refine Formalism.FourierDecayAlt.P.DualKernelLemmas.real_bound _ _ _ _ hk0 (hPos X₁ h1).2 (hPos _ hY).2 ?_
  exact cs_U hβ _ hRR hPos X₁ _ h1 hY

end DK

end Formalism.FourierDecayAlt.P.PBF
end

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem tprod_succ (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) (l : Fin r) :
    P5.tprod L Y l.val = P5.tprod L Y (l.val + 1) * Ts (site L l) Y := by
  rw [P5.tprod, dite_eq_left l.isLt]

theorem tprod_top (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) : P5.tprod L Y r = 1 := by
  rw [P5.tprod, dite_eq_right (lt_irrefl r)]

theorem QQi_step (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (l : Fin r) : QQi L st l.castSucc = fun Y => Matrix.conjTranspose (Ts (site L l) (star Y)) * QQi L st l.succ Y * Ts (site L l) Y := by
  funext Y
  simp only [QQi, Fin.coe_castSucc, Fin.val_succ]
  rw [tprod_succ L (star Y) l, tprod_succ L Y l, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem QQi_top (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π'))) :
    QQi L st (Fin.last r) = st.QQ := by
  funext Y
  simp only [QQi, Fin.val_last, tprod_top, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def bet (μ : MeasureTheory.Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') : ℂ := pairLev μ 0 Φ Ψ (fun _ => 1)

theorem pairAt_zero_left (μ : MeasureTheory.Measure (Mt k r)) (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ 0 Ψ c = 0 := by
  have h0 : ∀ A : Wq →L[ℂ] Wp, B.hsInner 0 A = 0 := fun A => by
    simp only [B.hsInner, B.hsVec, ContinuousLinearMap.zero_apply]
    rw [show (fun _ : Fin (Module.finrank ℂ Wq) => (0 : Wp)) = 0 from rfl, WithLp.toLp_zero,
      inner_zero_right]
  simp [P5.pairAt, h0]

theorem pairAt_zero_right (μ : MeasureTheory.Measure (Mt k r)) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Φ 0 c = 0 := by
  have h0 : ∀ A : Wq →L[ℂ] Wp, B.hsInner A 0 = 0 := fun A => by
    simp only [B.hsInner, B.hsVec, ContinuousLinearMap.zero_apply]
    rw [show (fun _ : Fin (Module.finrank ℂ Wq) => (0 : Wp)) = 0 from rfl, WithLp.toLp_zero,
      inner_zero_left]
  simp [P5.pairAt, h0]

variable {S : Type} [Fintype S] [DecidableEq S]

theorem form_single_left (μ : MeasureTheory.Measure (Mt k r)) (a : Ix S) (Φ : RadSp k r z z' π π')
    (y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (Pi.single a Φ) y c = pairLev μ 0 Φ (y a) c := by
  simp only [P5.form, pairLev]
  congr 1
  funext c'
  congr 1
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, pairAt_zero_left]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem form_eq_pairS (μ : MeasureTheory.Measure (Mt k r)) (K0 : Submodule ℂ (RadSp k r z z' π π'))
    (c : Fin r → ℂ) (hS : SesqOn (Submodule.pi Set.univ fun _ : Ix S => K0) (fun x y => form μ 0 x y c))
    (x y : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ K0) (hy : ∀ a, y a ∈ K0) :
    form μ 0 x y c = pairS (fun Φ Ψ => pairLev μ 0 Φ Ψ c) x y := by
  classical
  have hyU : y ∈ Submodule.pi Set.univ (fun _ : Ix S => K0) := Submodule.mem_pi.mpr (fun a _ => hy a)
  have hsingle : ∀ a, Pi.single a (x a) ∈ Submodule.pi Set.univ (fun _ : Ix S => K0) := by
    intro a
    refine Submodule.mem_pi.mpr (fun b _ => ?_)
    by_cases h : b = a
    · subst h
      simpa using hx b
    · rw [Pi.single_eq_of_ne h]
      exact K0.zero_mem
  have hzero : form μ 0 0 y c = 0 := by
    have h := (hS 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) y hyU 1).1
    simp only [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have key : ∀ s : Finset (Ix S), form μ 0 (∑ a ∈ s, Pi.single a (x a)) y c =
      ∑ a ∈ s, pairLev μ 0 (x a) (y a) c := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb]
      have hmem : (∑ a ∈ s, Pi.single a (x a)) ∈ Submodule.pi Set.univ (fun _ : Ix S => K0) :=
        Submodule.sum_mem _ (fun a _ => hsingle a)
      have h := (hS _ (hsingle b) _ hmem y hyU 1).1
      dsimp only at h
      rw [one_smul, one_mul] at h
      rw [h, ih, form_single_left]
  have h2 := key Finset.univ
  rw [Finset.univ_sum_single] at h2
  rw [h2]
  rfl

end Lev

section Data

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : MeasureTheory.Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)

theorem isStart_QQi (hD : IsData P z z' π π' X μ L st l0) (i : Fin (P.r + 1)) :
    IsStart (QQi L st i) (M.qC P) := by
  have h0 : IsStart st.QQ (M.qC P) := by
    have hX := (Formalism.FourierDecayAlt.P.actual_start Wp Wq P z z' π π' hD.1 X).1
    have h := Formalism.FourierDecayAlt.P.Mx8.isStart_smul X.QQ (M.qC P) (M.sgn P l0) (Formalism.FourierDecayAlt.P.Mx8.sgn_sq P l0)
      (Formalism.FourierDecayAlt.P.Mx8.sgn_star P l0) hX
    have e : st.QQ = fun Y => M.sgn P l0 • X.QQ Y := funext hD.2.2.2.1
    rw [e]; exact h
  have key : ∀ d i : ℕ, ∀ hi : i + d = P.r, IsStart (QQi L st ⟨i, by omega⟩) (M.qC P) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have e : (⟨i, by omega⟩ : Fin (P.r + 1)) = Fin.last P.r := Fin.ext (by simp; omega)
      rw [e, QQi_top]; exact h0
    | succ d ih =>
      intro i hi
      have hlt : i < P.r := by omega
      let l : Fin P.r := ⟨i, hlt⟩
      have e : (⟨i, by omega⟩ : Fin (P.r + 1)) = l.castSucc := rfl
      rw [e, QQi_step]
      have ih' := ih (i + 1) (by omega)
      have e' : (⟨i + 1, by omega⟩ : Fin (P.r + 1)) = l.succ := rfl
      rw [e'] at ih'
      exact Formalism.FourierDecayAlt.P.Mx8.isStart_step _ _ _ (isSite_actual hD.2.2.1 l)
        (qqCommutes_actual P z z' π π' X μ L st l0 hD l) ih'
  exact key (P.r - i.val) i.val (by omega)

theorem form_single_right (μ : MeasureTheory.Measure (Mt P.k P.r)) (a : Ix S)
    (x : Ix S → RadSp P.k P.r z z' π π') (Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) :
    form μ 0 x (Pi.single a Ψ) c = pairLev μ 0 (x a) Ψ c := by
  simp only [P5.form, pairLev]
  congr 1
  funext c'
  congr 1
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, pairAt_zero_right]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem herm_on {W : Type} [AddCommGroup W] [Module ℂ W] (U' : Submodule ℂ W) (f : W → W → ℂ) (hS : SesqOn U' f)
    (hN : NonnegOn U' f) (x : W) (hx : x ∈ U') (y : W) (hy : y ∈ U') : f y x = conj (f x y) := by
  have key : ∀ a : ℂ, (f (x + a • y) (x + a • y)).im = 0 := fun a =>
    (Complex.nonneg_iff.mp (hN _ (U'.add_mem hx (U'.smul_mem a hy)))).2.symm
  have hxx : (f x x).im = 0 := (Complex.nonneg_iff.mp (hN x hx)).2.symm
  have hyy : (f y y).im = 0 := (Complex.nonneg_iff.mp (hN y hy)).2.symm
  have expand : ∀ a : ℂ, f (x + a • y) (x + a • y) =
      f x x + conj a * f x y + a * (f y x + conj a * f y y) := by
    intro a
    rw [(hS x hx y hy (x + a • y) (U'.add_mem hx (U'.smul_mem a hy)) a).1,
      (hS x hx y hy x hx a).2, (hS x hx y hy y hy a).2]
  have h1 := key 1
  have hI := key Complex.I
  rw [expand] at h1 hI
  simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.mul_re, map_one, hxx, hyy] at h1 hI
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

end Data

end

end Formalism.FourierDecayAlt.P.PBF
end

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section One

variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem rrw_one (QQ : ℂ → M2 A) (s0 : S) (Y : ℂ) :
    RRw QQ [(⟨true, s0, Y⟩ : Letter ℂ S)] = ins s0 (lift0 (QQ Y)) := by
  simp [RRw, TTw]

theorem ins_lift0_apply (s0 : S) (M : M2 A) (z z' : Ix S) :
    ins s0 (lift0 M) z z' = if (∀ b, b ≠ s0 → z b = z' b) then M (z s0) (z' s0) else 0 := by
  unfold ins lift0
  simp only [Matrix.sum_apply, Matrix.map_apply]
  have h1 : ∀ (i j : Fin 2), (eU s0 i j * io (M i j) : SlopeTestRemainingChoices S A) z z' =
      if z s0 = i ∧ z' s0 = j ∧ ∀ b, b ≠ s0 → z b = z' b then M i j else 0 := by
    intro i j
    unfold io
    rw [Matrix.mul_apply, Finset.sum_eq_single z']
    · simp only [eU, Matrix.of_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      split_ifs <;> simp
    · intro b _ hb
      simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hb]
    · intro h; exact absurd (Finset.mem_univ z') h
  simp only [h1]
  by_cases h : ∀ b, b ≠ s0 → z b = z' b
  · rw [if_pos h, Finset.sum_eq_single (z s0)]
    · rw [Finset.sum_eq_single (z' s0)]
      · rw [if_pos ⟨rfl, rfl, h⟩]
      · intro j _ hj; rw [if_neg]; intro hh; exact hj hh.2.1.symm
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]; intro hh; exact hi hh.1.symm
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; intro hh; exact h hh.2.2

def eS (s0 : S) (i : Fin 2) : Ix S := Function.update (fun _ => 0) s0 i

theorem eS_self (s0 : S) (i : Fin 2) : eS s0 i s0 = i := by simp [eS]

theorem eS_agree (s0 : S) (i j : Fin 2) : ∀ b, b ≠ s0 → eS s0 i b = eS s0 j b := by
  intro b hb; simp [eS, Function.update_of_ne hb]

end One

section ActOne

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem blockMulVec_one_letter (QQ : ℂ → M2 (Q.Pr V)) (s0 : S) (Y : ℂ) (i j : Fin 2) (Φ : V) :
    actP (RRw QQ [(⟨true, s0, Y⟩ : Letter ℂ S)]) (Pi.single (eS s0 j) Φ) (eS s0 i) = (QQ Y i j).1 Φ := by
  rw [rrw_one]
  unfold actP
  rw [Finset.sum_eq_single (eS s0 j)]
  · rw [Pi.single_eq_same, ins_lift0_apply, if_pos (eS_agree s0 i j), eS_self, eS_self]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end ActOne

section Data

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : MeasureTheory.Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem constant_one_mem_nonvanishing : (fun _ => (1 : ℂ)) ∈ OmX P.r := fun _ => one_ne_zero

theorem act_eq_actP (M : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) (x : Ix S → RadSp P.k P.r z z' π π') :
    P5.act M x = actP M x := rfl

theorem wordOK_nil : WordOK P z z' π π' st l0 ([] : List (Letter ℂ S)) := by
  simp [WordOK, Fr.admitted]

theorem form_zero_left' (x : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) :
    form μ 0 (0 : Ix S → RadSp P.k P.r z z' π π') x c = 0 := by
  unfold form
  simp [pairAt_zero_left]

theorem sesqOn_form (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) :
    SesqOn (Submodule.pi Set.univ fun _ : Ix S => K 0) (fun x y => form μ 0 x y (fun _ => 1)) := by
  have h := ((hThm [] wordOK_nil).2.2 0 (fun _ => 1) constant_one_mem_nonvanishing).1
  intro x hx x' hx' y hy a
  have := h x hx x' hx' y hy a
  simpa [RRform, RRi, RRw, act_eq_actP, polyAction_one₂] using this

theorem sesquilinear_level_zero_pairing (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) : SesqCls (K 0) (bet μ) := by
  have hS := sesqOn_form hThm
  let s1 : Ix S := fun _ => 0
  have hsg : ∀ Φ ∈ K 0, Pi.single s1 Φ ∈ Submodule.pi Set.univ fun _ : Ix S => K 0 := by
    intro Φ hΦ b _
    by_cases h : b = s1
    · subst h; simpa using hΦ
    · simp [Pi.single_eq_of_ne h]
  have hb : ∀ Φ Ψ : RadSp P.k P.r z z' π π', bet μ Φ Ψ = form μ 0 (Pi.single s1 Φ) (Pi.single s1 Ψ) (fun _ => 1) := by
    intro Φ Ψ
    rw [form_single_left, Pi.single_eq_same]; rfl
  refine ⟨fun x _ y _ => pairLev_swap _ _ _, fun x hx x' hx' y hy => ?_, fun x hx y hy c => ?_⟩
  · rw [hb, hb, hb, Pi.single_add]
    have := (hS _ (hsg x hx) _ (hsg x' hx') _ (hsg y hy) 1).1
    simpa using this
  · rw [hb, hb, Pi.single_smul]
    have := (hS 0 (Submodule.zero_mem _) _ (hsg x hx) _ (hsg y hy) c).1
    simp only [zero_add] at this
    rw [this, form_zero_left', zero_add]

theorem qq_adj (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) (s0 : S) (Y : ℝ)
    (hw : WordOK P z z' π π' st l0 [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ S)]) (i j : Fin 2)
    (Φ Ψ : RadSp P.k P.r z z' π π') (hΦ : Φ ∈ K 0) (hΨ : Ψ ∈ K 0) :
    bet μ ((QQi L st 0 Y i j).1 Φ) Ψ = bet μ Φ ((QQi L st 0 Y j i).1 Ψ) := by
  obtain ⟨hSq, hNn⟩ := (hThm _ hw).2.2 0 (fun _ => 1) constant_one_mem_nonvanishing
  have hsg : ∀ (s : Ix S) (Φ : RadSp P.k P.r z z' π π'), Φ ∈ K 0 →
      Pi.single s Φ ∈ Submodule.pi Set.univ fun _ : Ix S => K 0 := by
    intro s Φ hΦ b _
    by_cases h : b = s
    · subst h; simpa using hΦ
    · simp [Pi.single_eq_of_ne h]
  have hh := herm_on _ _ hSq hNn (Pi.single (eS s0 j) Φ) (hsg _ _ hΦ) (Pi.single (eS s0 i) Ψ) (hsg _ _ hΨ)
  have ev : ∀ (a b : Fin 2) (Φ Ψ : RadSp P.k P.r z z' π π'),
      RRform L st μ 0 [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ S)] (Pi.single (eS s0 b) Φ) (Pi.single (eS s0 a) Ψ)
        (fun _ => 1) = pairLev μ 0 ((QQi L st 0 Y a b).1 Φ) Ψ (fun _ => 1) := by
    intro a b Φ Ψ
    unfold RRform RRi
    rw [form_single_right, act_eq_actP, blockMulVec_one_letter]
  rw [ev, ev] at hh
  unfold bet
  rw [pairLev_swap ((QQi L st 0 (Y : ℂ) j i).1 Ψ) Φ, hh, Complex.conj_conj]

def Gen (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (Pts : Set ℝ) : Set (Pr (RadSp P.k P.r z z' π π')) :=
  {a | ∃ Y ∈ Pts, ∃ i j : Fin 2, a = QQi L st 0 (Y : ℂ) i j}

def Ucls (K0 : Submodule ℂ (RadSp P.k P.r z z' π π')) (G : Set (Pr (RadSp P.k P.r z z' π π'))) :
    Submodule ℂ (RadSp P.k P.r z z' π π') where
  carrier := {Φ | ∀ m ∈ Submonoid.closure G, m.1 Φ ∈ K0}
  add_mem' {Φ Ψ} hΦ hΨ m hm := by rw [map_add (f := _)]; exact K0.add_mem (hΦ m hm) (hΨ m hm)
  zero_mem' m _ := by rw [map_zero]; exact K0.zero_mem
  smul_mem' c Φ hΦ m hm := by rw [map_smul]; exact K0.smul_mem c (hΦ m hm)

theorem Ucls_le (K0 : Submodule ℂ (RadSp P.k P.r z z' π π')) (G : Set (Pr (RadSp P.k P.r z z' π π'))) :
    Ucls K0 G ≤ K0 := fun Φ hΦ => hΦ 1 (Submonoid.one_mem _)

theorem SesqCls.mono {V : Type} [AddCommGroup V] [Module ℂ V] {U U' : Submodule ℂ V} {β : V → V → ℂ}
    (h : SesqCls U β) (hle : U' ≤ U) : SesqCls U' β :=
  ⟨fun x hx y hy => h.herm x (hle hx) y (hle hy), fun x hx x' hx' y hy => h.add_left x (hle hx) x' (hle hx') y (hle hy),
    fun x hx y hy c => h.smul_left x (hle hx) y (hle hy) c⟩

theorem gen_star (hS : IsStart (QQi L st 0) (M.qC P)) (Pts : Set ℝ) {a : Pr (RadSp P.k P.r z z' π π')}
    (ha : a ∈ Gen L st Pts) : star a ∈ Gen L st Pts := by
  obtain ⟨Y, hY, i, j, rfl⟩ := ha
  refine ⟨Y, hY, j, i, ?_⟩
  have h := hS.herm (Y : ℂ) (Complex.conj_ofReal Y)
  have := congrFun (congrFun h j) i
  rw [Matrix.conjTranspose_apply] at this
  exact this

theorem gen_mem_adjB (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) (hS : IsStart (QQi L st 0) (M.qC P))
    (Pts : Set ℝ) (hPts : ∀ Y ∈ Pts, ∃ s0 : S, WordOK P z z' π π' st l0 [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ S)])
    {a : Pr (RadSp P.k P.r z z' π π')} (ha : a ∈ Gen L st Pts) :
    a ∈ adjB (Ucls (K 0) (Gen L st Pts)) (bet μ) ((sesquilinear_level_zero_pairing hThm).mono (Ucls_le _ _)) := by
  have hsa := gen_star hS Pts ha
  refine ⟨fun Φ hΦ m hm => ?_, fun Φ hΦ m hm => ?_, fun Φ hΦ Ψ hΨ => ?_⟩
  · exact hΦ (m * a) (Submonoid.mul_mem _ hm (Submonoid.subset_closure ha))
  · exact hΦ (m * star a) (Submonoid.mul_mem _ hm (Submonoid.subset_closure hsa))
  · obtain ⟨Y, hY, i, j, rfl⟩ := ha
    obtain ⟨s0, hw⟩ := hPts Y hY
    have e : (QQi L st 0 (Y : ℂ) i j).2.unop = (QQi L st 0 (Y : ℂ) j i).1 := by
      have h := hS.herm (Y : ℂ) (Complex.conj_ofReal Y)
      have := congrFun (congrFun h j) i
      rw [Matrix.conjTranspose_apply] at this
      rw [← this]; rfl
    rw [e]
    exact qq_adj hThm s0 Y hw i j Φ Ψ (Ucls_le _ _ hΦ) (Ucls_le _ _ hΨ)

theorem form_zero_eq_position_pairing (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) (Y₁ Y₂ : Ix S → RadSp P.k P.r z z' π π')
    (h₁ : ∀ a, Y₁ a ∈ K 0) (h₂ : ∀ a, Y₂ a ∈ K 0) : form μ 0 Y₁ Y₂ 0 = pairS (bet μ) Y₁ Y₂ := by
  rw [Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ Y₁ Y₂ 0 (fun _ => 1)]
  exact form_eq_pairS μ (K 0) _ (sesqOn_form hThm) Y₁ Y₂ h₁ h₂

theorem jl_mem {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    {𝒜 : StarSubalgebra ℂ A} (L : List (Letter ℂ S)) : (JL L : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  induction L with
  | nil => exact (entSub 𝒜).one_mem
  | cons l L ih =>
    rw [JL]
    refine (entSub 𝒜).mul_mem (ins_mem _ ?_) ih
    split_ifs
    · exact symplectic_form_mem_entrywise
    · exact entries_mem_transpose symplectic_form_mem_entrywise

theorem dk_radial {X : ActualOps P.k P.r z z' π π'} (hD : IsData P z z' π π' X μ L st l0)
    (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) (Pts : Set ℝ)
    (hPts : ∀ Y ∈ Pts, ∃ s0 : S, WordOK P z z' π π' st l0 [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ S)])
    (w Lw : List (Letter ℂ S)) (hDK : FormPairingAction.DKHyp (M.qC P) w Lw)
    (hOK1 : WordOK P z z' π π' st l0 (Lw ++ w)) (hOK2 : WordOK P z z' π π' st l0 (Lw.map dl ++ w))
    (hP1 : ∀ l ∈ Lw ++ w, ∃ Y ∈ Pts, l.pt = (Y : ℂ)) (hP2 : ∀ l ∈ Lw, ∃ Y ∈ Pts, l.pt + 1 = (Y : ℂ))
    (X₁ X₂ : Ix S → RadSp P.k P.r z z' π π') (h1 : ∀ e, X₁ e ∈ Ucls (K 0) (Gen L st Pts))
    (h2 : ∀ e, X₂ e ∈ Ucls (K 0) (Gen L st Pts)) :
    (form μ 0 (P5.act (RRi L st 0 (Lw ++ w)) X₁) X₁ 0).im = 0 ∧
    0 ≤ (form μ 0 (P5.act (RRi L st 0 (Lw ++ w)) X₁) X₁ 0).re ∧
    (form μ 0 (P5.act (RRi L st 0 (Lw.map dl ++ w)) X₂) X₂ 0).im = 0 ∧
    0 ≤ (form μ 0 (P5.act (RRi L st 0 (Lw.map dl ++ w)) X₂) X₂ 0).re ∧
    ‖pairS (bet μ) (actP (JL Lw * RRw (QQi L st 0) w) X₁) X₂‖ ^ 2 ≤
      (form μ 0 (P5.act (RRi L st 0 (Lw ++ w)) X₁) X₁ 0 *
        form μ 0 (P5.act (RRi L st 0 (Lw.map dl ++ w)) X₂) X₂ 0 /
        (Lw.map fun l => qw (M.qC P) w l.pt).prod).re := by
  have hS := isStart_QQi P z z' π π' X μ L st l0 hD 0
  have hK := sesquilinear_level_zero_pairing hThm
  have hle := Ucls_le (K 0) (Gen L st Pts)
  have hU := hK.mono hle
  have hGen : ∀ Y ∈ Pts, ∀ i j, QQi L st 0 (Y : ℂ) i j ∈ adjB _ (bet μ) hU := fun Y hY i j =>
    gen_mem_adjB hThm hS Pts hPts ⟨Y, hY, i, j, rfl⟩
  have hat : ∀ Y : ℂ, (∃ Y' ∈ Pts, Y = (Y' : ℂ)) → ∀ i j, QQi L st 0 Y i j ∈ adjB _ (bet μ) hU := by
    rintro Y ⟨Y', hY', rfl⟩ i j; exact hGen Y' hY' i j
  have hPs : Ps (QQi L st 0) (M.qC P) w Lw ∈ entSub (adjB _ (bet μ) hU) := by
    refine ps_mem_at _ _ _ _ fun l hl a b => ⟨fun _ => hat _ (hP2 l hl) a b, fun hneg => ?_⟩
    have := hDK.1 l hl
    rw [this] at hneg; exact absurd hneg (by decide)
  have hRRe : RRw (QQi L st 0) (Lw ++ w) ∈ entSub (adjB _ (bet μ) hU) :=
    rrw_mem_at _ _ fun l hl a b => hat _ (hP1 l hl) a b
  have hRRe2 : RRw (QQi L st 0) (Lw.map dl ++ w) ∈ entSub (adjB _ (bet μ) hU) := by
    refine rrw_mem_at _ _ fun l hl a b => hat _ ?_ a b
    rcases List.mem_append.mp hl with h | h
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp h
      have hp := hDK.1 l' hl'
      obtain ⟨Y, hY, e⟩ := hP2 l' hl'
      refine ⟨Y, hY, ?_⟩
      simp [dl, hp, e]
    · exact hP1 l (List.mem_append_right _ h)
  have hRRw : RRw (QQi L st 0) w ∈ entSub (adjB _ (bet μ) hU) :=
    rrw_mem_at _ _ fun l hl a b => hat _ (hP1 l (List.mem_append_right _ hl)) a b
  have hJR : JL Lw * RRw (QQi L st 0) w ∈ entSub (adjB _ (bet μ) hU) := (entSub _).mul_mem (jl_mem Lw) hRRw
  have pres : ∀ {M : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))}, M ∈ entSub (adjB _ (bet μ) hU) →
      ∀ a b, ∀ x ∈ Ucls (K 0) (Gen L st Pts), (M a b).1 x ∈ Ucls (K 0) (Gen L st Pts) :=
    fun hM a b x hx => (hM a b).1 x hx
  have hSq := sesqOn_form (S := S) hThm
  have conv : ∀ (Y₁ Y₂ : Ix S → RadSp P.k P.r z z' π π'), InU (Ucls (K 0) (Gen L st Pts)) Y₁ →
      InU (Ucls (K 0) (Gen L st Pts)) Y₂ → form μ 0 Y₁ Y₂ 0 = pairS (bet μ) Y₁ Y₂ := by
    intro Y₁ Y₂ hY₁ hY₂
    rw [Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ Y₁ Y₂ 0 (fun _ => 1)]
    exact form_eq_pairS μ (K 0) _ hSq Y₁ Y₂ (fun a => hle (hY₁ a)) (fun a => hle (hY₂ a))
  have posOf : ∀ u : List (Letter ℂ S), WordOK P z z' π π' st l0 u →
      RRw (QQi L st 0) u ∈ entSub (adjB _ (bet μ) hU) → ∀ Y : Ix S → RadSp P.k P.r z z' π π',
      InU (Ucls (K 0) (Gen L st Pts)) Y →
      0 ≤ (pairS (bet μ) (actP (RRw (QQi L st 0) u) Y) Y).re ∧ (pairS (bet μ) (actP (RRw (QQi L st 0) u) Y) Y).im = 0 := by
    intro u hu hM Y hY
    have hn := ((hThm u hu).2.2 0 (fun _ => 1) constant_one_mem_nonvanishing).2 Y (fun a _ => hle (hY a))
    have e : RRform L st μ 0 u Y Y (fun _ => 1) = pairS (bet μ) (actP (RRw (QQi L st 0) u) Y) Y :=
      form_eq_pairS μ (K 0) _ hSq _ _ (fun a => hle (blockMulVec_apply_mem (pres hM) hY a)) (fun a => hle (hY a))
    beta_reduce at hn
    rw [e] at hn
    exact ⟨(Complex.nonneg_iff.mp hn).1, (Complex.nonneg_iff.mp hn).2.symm⟩
  have hPos := posOf _ hOK1 hRRe
  have hPos2 := posOf _ hOK2 hRRe2 X₂ h2
  have dk := dk_partial hU (QQi L st 0) (M.qC P) w Lw hS hDK hPs (pres hRRe) hPos X₁ X₂ h1 h2
  have hP1' := hPos X₁ h1
  have eA : form μ 0 (P5.act (RRi L st 0 (Lw ++ w)) X₁) X₁ 0 = pairS (bet μ) (actP (RRw (QQi L st 0) (Lw ++ w)) X₁) X₁ :=
    conv _ _ (blockMulVec_apply_mem (pres hRRe) h1) h1
  have eB : form μ 0 (P5.act (RRi L st 0 (Lw.map dl ++ w)) X₂) X₂ 0 =
      pairS (bet μ) (actP (RRw (QQi L st 0) (Lw.map dl ++ w)) X₂) X₂ :=
    conv _ _ (blockMulVec_apply_mem (pres hRRe2) h2) h2
  rw [eA, eB]
  exact ⟨hP1'.2, hP1'.1, hPos2.2, hPos2.1, dk.2⟩

end Data

end

end Formalism.FourierDecayAlt.P.PBF
end

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section Tower

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}

def IsPic (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ y ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
    (Φ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) F) y.1 y.2

theorem radSp_ext {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (Φ Ψ : RadSp k r z z' π π')
    (h : ∀ y ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hy : ((c, g) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z'
  · exact h _ hy
  · rw [Φ.2.1 (c, g) hy, Ψ.2.1 (c, g) hy]

theorem resG_JF_zero {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (i : Fin (r + 1)) :
    resG k r i (B.JF Bs (fun _ => (0 : Wq →L[ℂ] Wp))) = 0 := by
  funext c g
  simp [resG, Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero]

end Tower

section Cls

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}
  {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
  {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
  {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
  {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
  {l0 : ℕ}
  {K : Fin ((JC.parLev P0 j).r + 1) →
    Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')}

end Cls

section Words

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {S : Type}

theorem wordOK_gen (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hOK : P.OK) (hl1 : 1 ≤ l0) (hlk : l0 ≤ P.k) (hq : st.q = M.qC P)
    (hinv : st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0}) (u : List (Letter ℂ S))
    (hnd : (u.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hpt : ∀ l ∈ u, ∃ Y : ℝ, l.pt = (Y : ℂ) ∧ I.OnCut P.u P.u' l0 Y)
    (hsep : u.Pairwise fun l l' => 2 < |l.pt.re - l'.pt.re|) : WordOK P z z' π π' st l0 u := by
  refine ⟨⟨hnd, ?_, ?_, ?_⟩, ?_, hsep⟩
  · intro l hl
    obtain ⟨Y, e, -⟩ := hpt l hl
    rw [e]; exact Complex.conj_ofReal Y
  · intro l hl
    obtain ⟨Y, e, hc⟩ := hpt l hl
    rw [e]
    have hx : ∀ e : ℝ, -1 ≤ e → e ≤ 1 → ∀ ρ, M.xC P ρ ((Y + e : ℝ) : ℂ) ≠ 0 :=
      fun e h1 h2 ρ => Formalism.FourierDecayAlt.P.JCTx5.xC_ne P hOK l0 hl1 hlk _ hc e h1 h2 ρ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hinv]; intro ρ; simpa using hx 0 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa using hx 1 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa [sub_eq_add_neg] using hx (-1) (by norm_num) (by norm_num) ρ
    · rw [hq]; simpa using Formalism.FourierDecayAlt.P.JCTx5.qC_ne P hOK l0 hl1 hlk _ hc 0 (by norm_num) (by norm_num)
    · rw [hq]; simpa [sub_eq_add_neg] using Formalism.FourierDecayAlt.P.JCTx5.qC_ne P hOK l0 hl1 hlk _ hc (-1) (by norm_num) (by norm_num)
  · refine hsep.imp fun {l l'} h n hn e => ?_
    have hre : l.pt.re - l'.pt.re = (n : ℝ) := by
      have := congrArg Complex.re e
      simpa using this
    have h2 : |(n : ℝ)| ≤ 2 := by exact_mod_cast hn
    rw [hre] at h
    linarith
  · intro l hl
    obtain ⟨Y, e, hc⟩ := hpt l hl
    rw [e]
    exact ⟨by simp, by simpa using hc⟩

end Words

end

end Formalism.FourierDecayAlt.P.PBF
