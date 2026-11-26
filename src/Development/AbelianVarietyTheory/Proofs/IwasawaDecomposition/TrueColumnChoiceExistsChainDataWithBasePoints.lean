module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepQOfReindex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPenultimateLevelCouplingCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassEquivReferenceTupleEqSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassEquivReferenceTupleEqSelf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.MuZeroCls

theorem stepZeroClassEquiv_referenceTuple_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word)
    (c : (I.stp u I.mu0 0).Cl), I.eCls0 l u I.mu0 c = c := by
  intro B X I h l u c
  show (I.stp u I.mu0 0).cl _ (I.pt0 u I.mu0 I.mu0 ((I.stp u I.mu0 0).rep c)) = c
  refine Eq.trans ?_ (GlobalTheory.Mem.Col2.ClsZero.cl_rep _ c)
  refine (GlobalTheory.Mem.Col2.ClsZero.cl_eq_iff h u I.mu0 _ _ _ _).2 ?_
  rfl

end GlobalTheory.Mem.Col2.TC.MuZeroCls
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassEquivReferenceTupleEqSelfStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eCls0_mu0_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (c : (I.stp u I.mu0 0).Cl), I.eCls0 l u I.mu0 c = c := by
  first | exact @GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self | exact GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self | (intros; apply GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceTwistedChainsFormsClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroFormsIdentificationReferenceTupleEqSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroFormsIdentificationReferenceTupleEqSelf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.MuZeroForms

theorem law0_choose_mu0_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (x : ((I.fm l u I.mu0).lat 0).V),
    (l0 u I.mu0).choose x = x := by
  intro B X I h l Z l0 u x
  apply (I.fm l u I.mu0).emb_inj 0
  rw [(l0 u I.mu0).choose_spec.2 x]
  show LinearEquiv.funCongrLeft ℂ _ (I.eCls0 l u I.mu0).symm ((I.fm l u I.mu0).emb 0 x) = _
  funext c
  rw [LinearEquiv.funCongrLeft_apply]
  show (I.fm l u I.mu0).emb 0 x ((I.eCls0 l u I.mu0).symm c) = _
  have hc : (I.eCls0 l u I.mu0).symm c = c :=
    (I.eCls0 l u I.mu0).symm_apply_eq.2 (GlobalTheory.T.eCls0_mu0_eq_self I h l u c).symm
  rw [hc]

end GlobalTheory.Mem.Col2.TC.MuZeroForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroFormsIdentificationReferenceTupleEqSelfStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroFormsIdentification_referenceTuple_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (x : ((I.fm l u I.mu0).lat 0).V), (l0 u I.mu0).choose x = x := by
  first | exact @GlobalTheory.Mem.Col2.TC.MuZeroForms.law0_choose_mu0_eq_self | exact GlobalTheory.Mem.Col2.TC.MuZeroForms.law0_choose_mu0_eq_self | (intros; apply GlobalTheory.Mem.Col2.TC.MuZeroForms.law0_choose_mu0_eq_self <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelJCharacterEqMemberOffPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelJCharacterEqMemberOffPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChiOffQ

open Formalism.UG.P

section Cut

variable {F : Type} {iF : Field F} [NumberField F] {E : Type} {iE : Field E} [NumberField E]
  {iA : Algebra F E} {n : Type} [Fintype n] [DecidableEq n]

def cut1 (v : HeightOneSpectrum (𝓞 F)) :
    GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) →* GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  toFun x := afsplitU v 1 x
  map_one' := by
    apply Units.ext
    rw [afsplitU_coe, Units.val_one, Units.val_one, afsplitC_one]
  map_mul' x y := by
    rw [← afsplitU_mul, one_mul]

open Classical in
theorem glAdeleReplaceComponentByOne_component (v w : HeightOneSpectrum (𝓞 F)) (x : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) w) (cut1 v x) = if w = v then 1 else bc (prV (E := E) w) x := by
  by_cases h : w = v
  · subst h; rw [if_pos rfl]
    change bc (prV (E := E) w) (afsplitU w 1 x) = 1
    exact afsplit_right1 w 1 x
  · rw [if_neg h]
    apply Units.ext
    rw [afsplit_coe_bc_prV, afsplit_coe_bc_prV]
    exact afsplitC_prV_ne v w h _ _

def cutL (l : List (HeightOneSpectrum (𝓞 F))) :
    GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) →* GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  l.foldr (fun v f => (cut1 v).comp f) (MonoidHom.id _)

open Classical in
theorem cutL_prV (l : List (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F))
    (x : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) w) (cutL l x) = if w ∈ l then 1 else bc (prV (E := E) w) x := by
  induction l with
  | nil => simp [cutL, List.foldr_nil]
  | cons v l ih =>
    show bc (prV (E := E) w) (cut1 v (cutL l x)) = _
    rw [glAdeleReplaceComponentByOne_component, ih]
    by_cases h : w = v
    · simp [h]
    · simp [h]

theorem cutL_mem (σ : E →ₐ[F] E) (J : Matrix n n E) (l : List (HeightOneSpectrum (𝓞 F)))
    (x : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    cutL l x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  induction l with
  | nil => exact hx
  | cons v l ih => exact afsplitU_mem v σ J 1 _ (one_mem _) ih

theorem ext_bc (x y : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : ∀ w : HeightOneSpectrum (𝓞 F), bc (prV (E := E) w) x = bc (prV (E := E) w) y) : x = y := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [← sub_eq_zero]
  apply afsplit_inj
  intro w
  have e := congrArg (fun g : GL n (E ⊗[F] w.adicCompletion F) => g.val i j) (h w)
  change ((x : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).map (prV (E := E) w)) i j =
    ((y : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).map (prV (E := E) w)) i j at e
  rw [Matrix.map_apply, Matrix.map_apply] at e
  rw [map_sub, e, sub_self]

end Cut

section Re

theorem bc_reGL' {a b : ℕ} (h : a = b) {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : GL (Fin a) R) :
    bc φ (reGL h R g) = reGL h S (bc φ g) := by
  subst h
  apply Units.ext; ext x y; rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reGL_mem_UPts' {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin a) (E ⊗[F] R)) (hg : g ∈ UPts σ J R) :
    reGL h _ g ∈ UPts σ J' R := by
  subst h
  have e1 : J' = J := by ext x y; exact hJ x y
  have e2 : reGL (rfl : a = a) (E ⊗[F] R) g = g := by apply Units.ext; ext x y; rfl
  rw [e1, e2]; exact hg

theorem reGL_mem_levelVL {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin a → E))
    (g : GL (Fin a) (E ⊗[F] v.adicCompletion F)) (hg : g ∈ levelVL σ J v L) :
    reGL h _ g ∈ levelVL σ J' v (reL h L) := by
  subst h
  have e1 : J' = J := by ext x y; exact hJ x y
  have e2 : reGL (rfl : a = a) (E ⊗[F] v.adicCompletion F) g = g := by apply Units.ext; ext x y; rfl
  have e3 : reL (rfl : a = a) L = L := by
    have : ((reV (rfl : a = a) E : (Fin a → E) →ₗ[E] (Fin a → E)).restrictScalars (𝓞 E)) = LinearMap.id := by
      ext x i; rfl
    rw [reL, this, Submodule.map_id]
  rw [e1, e2, e3]; exact hg

end Re

end GlobalTheory.Mem.Col2.TC.ChiOffQ

namespace GlobalTheory.Mem.Col2.TC.ChiOffQ

theorem clause1_alg {M N : Type} [Group M] [Group N] {G : Subgroup M} {A : Subgroup N} (r : M ≃* N)
    (ρ : G →* G) (α chiJ : G →* ℂˣ) (φ : A →* ℂˣ) (κ : G) (κ' : A) (k1 : A)
    (hκ' : κ'.1 = r κ.1) (hk1 : k1.1 = r (ρ κ).1) (h1 : φ k1 = α κ)
    (hJ : ∀ (x : G) (k : A), k.1 = r x.1 → φ k = chiJ x) :
    φ κ' = (α * chiJ * (chiJ.comp ρ)⁻¹) κ := by
  have h2 : φ (k1⁻¹ * κ') = chiJ ((ρ κ)⁻¹ * κ) := hJ _ _ (by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hk1, hκ', Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv])
  calc φ κ' = φ (k1 * (k1⁻¹ * κ')) := by rw [mul_inv_cancel_left]
    _ = α κ * chiJ ((ρ κ)⁻¹ * κ) := by rw [map_mul, h1, h2]
    _ = (α * chiJ * (chiJ.comp ρ)⁻¹) κ := by
      rw [map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply,
        mul_comm (chiJ (ρ κ))⁻¹, ← mul_assoc]

theorem clause2_alg {G B : Type} [Group G] [Group B] (ψ : G →* B) (ρ : G →* G) (χ1 : B →* ℂˣ) (chiJ : G →* ℂˣ)
    (κ : G) (κ' : B) (hρ : ρ κ = κ) (hψ : ψ κ = κ') : ((χ1.comp ψ) * chiJ * (chiJ.comp ρ)⁻¹) κ = χ1 κ' := by
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hρ, hψ,
    mul_inv_cancel_right]

end GlobalTheory.Mem.Col2.TC.ChiOffQ

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 20000000 in
theorem twLevJ_chi_off_of_lb : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → I.ReadsK l Z u a (B.R.m - 1) (Nat.sub_le _ _) chOf K → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ J : TwLevJ I l Z F Q u a chOf K, (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) J.levJ.Lb → ∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = χ κ) ∧ ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ' := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g hQ hStd hfr hRK hUloc hchi J hLb
  classical
  have hcutU : ∀ x : J.levJ.U, ChiOffQ.cutL Q.toList x.1 ∈ J.levJ.U := by
    intro x
    have hx := (J.levJ.U_eq x.1).1 x.2
    refine (J.levJ.U_eq _).2 ⟨ChiOffQ.cutL_mem _ _ _ _ hx.1, fun v => ?_⟩
    rw [ChiOffQ.cutL_prV]
    split_ifs
    · exact one_mem _
    · exact hx.2 v
  have hρex : ∃ ρ : J.levJ.U →* J.levJ.U, ∀ x, (ρ x).1 = ChiOffQ.cutL Q.toList x.1 :=
    ⟨MonoidHom.codRestrict ((ChiOffQ.cutL Q.toList).comp J.levJ.U.subtype) J.levJ.U hcutU, fun _ => rfl⟩
  obtain ⟨ρ, hρv⟩ := hρex
  have hFmem : ∀ x : J.levJ.U,
      reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ChiOffQ.cutL Q.toList x.1) ∈ (F u).levJ.U := by
    intro x
    have hx := (J.levJ.U_eq x.1).1 x.2
    have hUPx := ChiOffQ.reGL_mem_UPts' (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ _
      (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (fun _ _ => rfl) _ _ (((J.levJ.U_eq _).1 (hcutU x)).1)
    refine ((F u).levJ.U_eq _).2 ⟨hUPx, fun v => ?_⟩
    show bc (prV v) (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ChiOffQ.cutL Q.toList x.1)) ∈
      (F u).levJ.Uloc v
    rw [ChiOffQ.bc_reGL', ChiOffQ.cutL_prV]
    split_ifs with hv
    · rw [map_one]; exact one_mem _
    · have hvQ : v ∉ Q := fun h => hv (Finset.mem_toList.2 h)
      by_cases hb : v ∈ badG (I.rec7 l Z)
      · obtain ⟨j, hj⟩ : ∃ j : Fin 2, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
          rcases hb with h | h
          · exact ⟨0, h⟩
          · exact ⟨1, h⟩
        have hlevJ := J.levJ.Uloc_lev v (hx.2 v)
        have hlev : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV v) x.1) ∈
            levelVL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) v (F u).levJ.Lb := by
          rw [hLb]
          exact ChiOffQ.reGL_mem_levelVL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).sp.cm.sig
            ((I.rec7 l Z).sp.X (B.R.m - 1)).gram (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (fun _ _ => rfl)
            v J.levJ.Lb _ hlevJ
        obtain ⟨M, hMmem, hMeq⟩ := (J.J_g j v hj _ hlevJ).1 (hx.2 v)
        refine ((F u).glevJ.mem j v hj _ hlev).2 ⟨M, hMmem, ?_⟩
        rw [hMeq]
        rfl
      · exact (J.J_off v hvQ hb).le (Subgroup.mem_map_of_mem _ (hx.2 v))
  have hψex : ∃ ψ : J.levJ.U →* (F u).levJ.U, ∀ x,
      (ψ x).1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ChiOffQ.cutL Q.toList x.1) :=
    ⟨MonoidHom.codRestrict ((((reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom.comp
      (ChiOffQ.cutL Q.toList)).comp J.levJ.U.subtype)) (F u).levJ.U hFmem, fun _ => rfl⟩
  obtain ⟨ψ, hψv⟩ := hψex
  refine ⟨(F u).levJ.chi.comp ψ * J.chiJ * (J.chiJ.comp ρ)⁻¹, ?_, ?_⟩
  · intro β κ κ' hκ'
    have hK := ((K β).lev.U_eq κ'.1).1 κ'.2
    have hκ1v : (ρ κ).1 = ChiOffQ.cutL Q.toList κ.1 := hρv κ
    have hUP := ChiOffQ.reGL_mem_UPts' (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ _
      (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (fun _ _ => rfl) _ _ (((J.levJ.U_eq _).1 (ρ κ).2).1)
    have hloc : ∀ w, bc (prV w) (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ρ κ).1) =
        if w ∈ Q then 1 else bc (prV w) κ'.1 := by
      intro w
      rw [ChiOffQ.bc_reGL', hκ1v, ChiOffQ.cutL_prV, hκ', ChiOffQ.bc_reGL']
      simp only [Finset.mem_toList]
      split_ifs
      · exact map_one _
      · rfl
    have m1 : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ρ κ).1 ∈ (K β).lev.U :=
      ((K β).lev.U_eq _).2 ⟨hUP, fun w => by
        rw [hloc]
        split_ifs
        · exact one_mem _
        · exact hK.2 w⟩
    have m2 : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ρ κ).1 ∈
        ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U :=
      (((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U_eq _).2 ⟨hUP, fun w => by
        rw [hloc]
        split_ifs with hw
        · exact one_mem _
        · rw [← hUloc β w hw]; exact hK.2 w⟩
    have hk1ex : ∃ k1 : (K β).lev.U,
        k1.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ρ κ).1 := ⟨⟨_, m1⟩, rfl⟩
    obtain ⟨k1, hk1⟩ := hk1ex
    have e3 : (K β).lev.chi k1 = (F u).levJ.chi (ψ κ) := by
      have m2' : k1.1 ∈ ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U := by rw [hk1]; exact m2
      rw [hchi β k1 ⟨k1.1, m2'⟩ rfl ?_]
      · exact (F u).levJ_chi h1 (g β) ⟨k1.1, m2'⟩ (ψ κ) (by rw [hψv, hk1, hκ1v])
      · intro v hv
        rw [hk1, hloc, if_pos hv]
    exact ChiOffQ.clause1_alg (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _) ρ ((F u).levJ.chi.comp ψ)
      J.chiJ (K β).lev.chi κ κ' k1 hκ' hk1 e3 (J.chiJ_eq β)
  · intro κ κ' hκ' hQκ
    have hc : ChiOffQ.cutL Q.toList κ.1 = κ.1 := ChiOffQ.ext_bc _ _ fun w => by
      rw [ChiOffQ.cutL_prV]
      split_ifs with hw
      · exact (hQκ w (Finset.mem_toList.1 hw)).symm
      · rfl
    have hρ : ρ κ = κ := Subtype.ext ((hρv κ).trans hc)
    have hψ : ψ κ = κ' := Subtype.ext (by rw [hψv, hc, hκ'])
    exact ChiOffQ.clause2_alg ψ ρ (F u).levJ.chi J.chiJ κ κ' hρ hψ


set_option maxHeartbeats 20000000 in
theorem twLevJ_chi_off : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → I.ReadsK l Z u a (B.R.m - 1) (Nat.sub_le _ _) chOf K → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → Nonempty Ch → ∀ J : TwLevJ I l Z F Q u a chOf K, ∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = χ κ) ∧ ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ' := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRK hUloc hchi hne J
  classical
  have hLb : (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) J.levJ.Lb := by
    obtain ⟨β⟩ := hne
    rw [← J.lb β, ← (F u).levJ_Lb h1 (g β)]
    obtain ⟨k, hk⟩ := hRK
    obtain ⟨k', hk'⟩ := (hStd u).mid (B.R.m - 1) h1 (succ_pred_m B.R)
    ext x
    exact (hk'.lb (g β) x).trans (hk.lb β x).symm
  exact twLevJ_chi_off_of_lb I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRK hUloc hchi J hLb

theorem stepBefore_cl_nonempty_tup {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (u : B.Word) (a : I.ι) :
    Nonempty (I.stp u a (B.R.m - 1)).Cl := by
  classical
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  haveI : NeZero (B.R.N (B.R.m - 1)) := ⟨(B.R.N_pos _).ne'⟩
  have hL := hOk.idx_ok a
  obtain ⟨b0x, -⟩ := hL.last_uniq
  let b0 : Idx I.sel (I.tup a) (I.idx a) (B.R.m - 1) := ⟨some (cast (by rw [show B.R.m - 1 = B.R.m - 2 + 1 by omega]) b0x), by simp; omega⟩
  let q0 : (I.stp u a (B.R.m - 1)).D b0 := ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup a)) (DecoF.base B.fields.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))).deco.1.N
      (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst a).M : ℤ))}), by
    show _ ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) (B.R.m - 1)).ys _
    rw [ysAt_ys_of_eq _ _ _ hmj]
    exact ⟨0, zero_mem _, rfl⟩⟩
  exact ⟨(I.stp u a (B.R.m - 1)).cl b0 q0⟩


set_option maxHeartbeats 20000000 in
theorem twLevJ_exists_chi_off : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → I.ReadsK l Z u a (B.R.m - 1) (Nat.sub_le _ _) chOf K → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ J : TwLevJ I l Z F Q u a chOf K, ∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = χ κ) ∧ ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ' := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRK hUloc hchi J
  exact twLevJ_chi_off I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRK hUloc hchi
    ((stepBefore_cl_nonempty_tup I hI u a).map chOf) J

end GlobalTheory.Mem.Col2.TC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelJCharacterEqMemberOffPlacesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelJ_character_eq_member_off_places : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → I.ReadsK l Z u a (B.R.m - 1) (Nat.sub_le _ _) chOf K → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ J : TwLevJ I l Z F Q u a chOf K, ∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = χ κ) ∧ ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off | exact GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off | (intros; apply GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClassMapAboveLastStep
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClassMapAboveLastStep
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

noncomputable def clDown {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : B.R.m < i)
    (c : (I.stp u a i).Cl) : (I.stp u I.mu0 i).Cl :=
  (I.stp u I.mu0 i).cl (Idx.top I.sel (I.tup I.mu0) (I.idx I.mu0) (le_of_lt hi))
    ⟨(extTo (I.Q I.mu0) ((I.stp u a i).rep c).1.1, ∅), by
      rw [ysAt_ys_of_ne I.sel (I.tup I.mu0) (I.cst I.mu0) (by omega)]
      rfl⟩

theorem nonempty_clDown : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), B.R.m < i →
    Nonempty ((I.stp u a i).Cl → (I.stp u I.mu0 i).Cl) :=
  fun I _ u a i hi => ⟨I.clDown u a i hi⟩

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClassMapAboveLastStepStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_classMap_above_lastStep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), B.R.m < i → Nonempty ((I.stp u a i).Cl → (I.stp u I.mu0 i).Cl) := by
  first | exact @GlobalTheory.Mem.Col2.TC.nonempty_clDown | exact GlobalTheory.Mem.Col2.TC.nonempty_clDown | (intros; apply GlobalTheory.Mem.Col2.TC.nonempty_clDown <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceTwistedChainsFormsClasses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open scoped TensorProduct
section
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))


set_option maxHeartbeats 4000000 in
structure TwStep (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u))
    (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (u : B.Word) (a : I.ι) (i : ℕ) where
  Ch : Type
  fin : Finite Ch
  chOf : (I.stp u a i).Cl → Ch
  gOf : Ch → H.Ch u i
  K : ∀ (_ : 1 ≤ i) (hm : i ≤ B.R.m) (β : Ch), LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hm
    (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hm (I.latAt u a i c.1))
  reads : ∀ h1 hm, I.ReadsK l Z u a i hm chOf (K h1 hm)
  readsQ : ∀ h1 hm, i + 1 ≤ B.R.m → ∃ k : Ch → GA B (B.R.N i), I.Reads u a i chOf (fun β => (K h1 hm β).lev.Lb) (fun β => (K h1 hm β).lev.U)
    (fun β => (K h1 hm β).lev.chi) (fun c => ((K h1 hm (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K h1 hm (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1
  fk : ∀ h1 hm β, FunKilled (K h1 hm β).lev (X.piT u)
  lev : ∀ (_ : 1 ≤ i) (_ : i ≤ B.R.m) (_ : Ch),
    Formalism.L2.Herm.StepLevelQ (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g (B.T u) B.R.f Q
  cls : ∀ h1 hm β, Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (lev h1 hm β).Lb (lev h1 hm β).U
    (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => I.latAt u a i c.1)
  car : ∀ h1 hm β, SameCar (rankN (I.rec7 l Z) i hm) (lev h1 hm β).Lb (K h1 hm β).lev.Lb (lev h1 hm β).Uloc (K h1 hm β).lev.Uloc
    (lev h1 hm β).U (K h1 hm β).lev.U (fun c => ((cls h1 hm β).y c).1) (fun c => ((K h1 hm β).y c).1)
    (fun c s => ((cls h1 hm β).stabI c s).1) (fun c s => ((K h1 hm β).stabI c s).1)
  offU : ∀ h1 hm β v, v ∉ Q → (lev h1 hm β).Uloc v = (H.lev u i h1 hm (gOf β)).Uloc v
  offL : ∀ h1 hm β, (lev h1 hm β).Lb = (H.lev u i h1 hm (gOf β)).Lb
  offK : ∀ h1 (h2 : i + 1 ≤ B.R.m) β v, v ∉ Q → (K h1 (le_of_succ_m h2) β).lev.Uloc v = ((F u).ch i h1 h2 (gOf β)).lev.Uloc v
  uniq : i = B.R.m → Nonempty (Unique Ch)
  chiFin : a ≠ I.mu0 → ∀ h1 hm β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K h1 hm β).lev.chi κ ^ n = 1
  chiC : ∀ h1 (h2 : i + 1 ≤ B.R.m) β (κ : (K h1 (le_of_succ_m h2) β).lev.U) (κ' : ((F u).ch i h1 h2 (gOf β)).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K h1 (le_of_succ_m h2) β).lev.chi κ = ((F u).ch i h1 h2 (gOf β)).lev.chi κ'

variable {I l Z}

theorem twStep_out {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (u : B.Word) (a : I.ι) (i : ℕ) (hout : ¬ (1 ≤ i ∧ i ≤ B.R.m))
    (f : (I.stp u a i).Cl → H.Ch u i) : Nonempty (TwStep I l Z H F Q u a i) :=
  ⟨{ Ch := H.Ch u i
     fin := H.ChFin u i
     chOf := f
     gOf := id
     K := fun h1 hm => absurd ⟨h1, hm⟩ hout
     reads := fun h1 hm => absurd ⟨h1, hm⟩ hout
     readsQ := fun h1 hm => absurd ⟨h1, hm⟩ hout
     fk := fun h1 hm => absurd ⟨h1, hm⟩ hout
     lev := fun h1 hm => absurd ⟨h1, hm⟩ hout
     cls := fun h1 hm => absurd ⟨h1, hm⟩ hout
     car := fun h1 hm => absurd ⟨h1, hm⟩ hout
     offU := fun h1 hm => absurd ⟨h1, hm⟩ hout
     offL := fun h1 hm => absurd ⟨h1, hm⟩ hout
     offK := fun h1 h2 => absurd ⟨h1, le_of_succ_m h2⟩ hout
     uniq := fun e => absurd ⟨by have := B.R.two_le_m; omega, by omega⟩ hout
     chiFin := fun _ h1 hm => absurd ⟨h1, hm⟩ hout
     chiC := fun h1 h2 => absurd ⟨h1, le_of_succ_m h2⟩ hout }⟩

theorem swap_ex (hok : I.Ok) (pins : TC.Pins B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    (K : ∀ β : Ch, LevelChart (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi (I.latAt u a i c.1)))
    (hK : I.ReadsK l Z u a i hi chOf K) (β : Ch) :
    ∃ Kr, ∃ hl : GlobalTheory.Mem.Col2.Reside.SwapLaws (K β).lev Kr, FunKilled (GlobalTheory.Mem.Col2.Reside.swap (K β).lev Kr hl) (X.piT u) := by
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hok pins l Z
  obtain ⟨hgr, -, -⟩ := hc i hi
  have hB := basePi_of_ok hX hPr u
  have hLb : (K β).lev.Lb = baseLb B.fields.E (B.R.N i) ((B.primes X).vT u) := by
    obtain ⟨k, hk⟩ := hK
    ext x
    exact (hk.lb β x).trans (GlobalTheory.Mem.Col2.Reside.mem_baseLb hPr u _ x).symm
  exact ⟨_, GlobalTheory.Mem.Col2.Reside.swapLaws B.sp.cm hB (hPr.T_prime u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => by simpa only [Ideal.absNorm_eq_natCard] using hPr.vT_norm u P hP) hgr (K β).lev hLb⟩

def killK (hok : I.Ok) (pins : TC.Pins B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    (K : ∀ β : Ch, LevelChart (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi (I.latAt u a i c.1)))
    (hK : I.ReadsK l Z u a i hi chOf K) (β : Ch) :
    LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)) :=
  { K β with lev := GlobalTheory.Mem.Col2.Reside.swap (K β).lev _ (swap_ex hok pins u a i hi K hK β).choose_spec.choose }

def twStep_mk (hok : I.Ok) (pins : TC.Pins B X) {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (u : B.Word) (a : I.ι) (i : ℕ) (h1i : 1 ≤ i) (hmi : i ≤ B.R.m)
    (hQ : ∀ v ∈ Q, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, (((I.rec7 l Z).host.g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal)
    (Ch : Type) (fin : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (g : Ch → H.Ch u i)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hmi
      (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hmi (I.latAt u a i c.1)))
    (hr : I.ReadsK l Z u a i hmi chOf K)
    (hrQ : i + 1 ≤ B.R.m → ∃ k : Ch → GA B (B.R.N i), I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U)
    (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1)
    (hLb : ∀ β, (K β).lev.Lb = reL (rankN (I.rec7 l Z) i hmi) (H.lev u i h1i hmi (g β)).Lb)
    (hU : ∀ β v, v ∉ Q → (K β).lev.Uloc v = ((H.lev u i h1i hmi (g β)).Uloc v).map (reGL (rankN (I.rec7 l Z) i hmi) _).toMonoidHom)
    (hK : ∀ h1 (h2 : i + 1 ≤ B.R.m) β v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch i h1 h2 (g β)).lev.Uloc v)
    (hu : i = B.R.m → Nonempty (Unique Ch))
    (hF : a ≠ I.mu0 → ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1)
    (hC : ∀ h1 (h2 : i + 1 ≤ B.R.m) β (κ : (K β).lev.U) (κ' : ((F u).ch i h1 h2 (g β)).lev.U), κ.1 = κ'.1 →
      (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch i h1 h2 (g β)).lev.chi κ') :
    TwStep I l Z H F Q u a i :=
  have hx := fun β => GlobalTheory.ChartQ.chartTie_toQ Q hmi _ _ (killK hok pins u a i hmi K hr β) (H.lev u i h1i hmi (g β)) hQ (hLb β) (hU β)
  { Ch := Ch, fin := fin, chOf := chOf, gOf := g, K := fun _ _ => killK hok pins u a i hmi K hr, reads := fun _ _ => hr, readsQ := fun _ _ => hrQ,
    fk := fun _ _ β => (swap_ex hok pins u a i hmi K hr β).choose_spec.choose_spec, lev := fun _ _ β => (hx β).choose,
    cls := fun _ _ β => (hx β).choose_spec.choose, car := fun _ _ β => (hx β).choose_spec.choose_spec.2,
    offU := fun _ _ β v hv => by
      have h1 : (K β).lev.Uloc v = _ := (hx β).choose_spec.choose_spec.2.Uloc_eq v
      rw [hU β v hv] at h1
      exact Subgroup.map_injective (reGL (rankN (I.rec7 l Z) i hmi) _).injective h1.symm,
    offL := fun _ _ β => (hx β).choose_spec.choose_spec.1, offK := hK, uniq := hu,
    chiFin := fun h _ _ => hF h, chiC := hC }

theorem reads_lb_eq {u : B.Word} {a a' : I.ι} {i : ℕ} {hi : i ≤ B.R.m} {bad bad' : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch Ch' : Type}
    {chOf : (I.stp u a i).Cl → Ch} {chOf' : (I.stp u a' i).Cl → Ch'}
    {K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))}
    {K' : ∀ β : Ch', LevelChart (I.rec7 l Z) (B.T u) bad' i hi (fun c : {c // chOf' c = β} => (I.chain l u a').stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a' i c.1))}
    (h : I.ReadsK l Z u a i hi chOf K) (h' : I.ReadsK l Z u a' i hi chOf' K') (β : Ch) (β' : Ch') :
    (K β).lev.Lb = (K' β').lev.Lb := by
  obtain ⟨k, R⟩ := h
  obtain ⟨k', R'⟩ := h'
  ext x
  exact (R.lb β x).trans (R'.lb β' x).symm

theorem twStep_mid (hok : I.Ok) (pins : TC.Pins B X) {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (u : B.Word) (a : I.ι) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ B.R.m)
    (hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v)
    (hF : ∀ u, I.StdF l Z u (F u)) (hC : CarH H F) : Nonempty (TwStep I l Z H F Q u a i) := by
  have hoff : ∀ v ∈ Q, ((B.T u : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∉ v.asIdeal ∧ ∀ j, (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g j : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∉ v.asIdeal :=
    fun v hv => GlobalTheory.T.twistPlaces_prime_to_levelAndTypePrimes I hok l u a v ((hQ v).1 hv)
  have hi : i ≤ B.R.m := le_of_succ_m h2
  by_cases ha : a = I.mu0
  · subst ha
    have hr0 := (hF u).mid i h1 h2
    let K : ∀ β : H.Ch u i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi
        (fun c : {c // H.chOf u i c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1)) :=
      fun β => chartWiden Set.subset_union_left ((F u).ch i h1 h2 β)
    refine ⟨twStep_mk hok pins u I.mu0 i h1 hi hoff (H.Ch u i) (H.ChFin u i) (H.chOf u i) id K hr0
      (fun _ => hr0.elim fun k hk => ⟨k, hk, fun _ v hv => absurd hv (GlobalTheory.T.not_twistPlace_referenceTuple I hok v)⟩) (fun β => ?_) (fun β v _ => ?_) (fun _ _ β v _ => rfl)
      (fun e => by omega) (fun h => absurd rfl h) (fun _ _ β κ κ' e _ => ?_)⟩
    · exact (hC.carC u i h1 h2 β).Lb_eq
    · exact (hC.carC u i h1 h2 β).Uloc_eq v
    · have : κ = κ' := Subtype.ext e
      subst this
      rfl
  · obtain ⟨Ch, fin, chOf, K, g, hrQ, hp⟩ := GlobalTheory.Mem.Col2.TC.ChTw.charts_tuple_trivQ I hok pins l Z u a Q i hi (H.Ch u i) (H.chOf u i) ((F u).ch i h1 h2) h1 (by omega) hQ
      ((hF u).mid i h1 h2)
    have hr : I.ReadsK l Z u a i hi chOf K := hrQ.elim fun k hk => ⟨k, hk.1⟩
    have hoU : ∀ β v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch i h1 h2 (g β)).lev.Uloc v := fun β v hv => (hp β).1 v hv
    refine ⟨twStep_mk hok pins u a i h1 hi hoff Ch fin chOf g K hr (fun _ => hrQ) (fun β => ?_) (fun β v hv => ?_) (fun _ _ β v hv => hoU β v hv)
      (fun e => by omega) (fun _ β => (hp β).2.1) (fun _ _ β κ κ' e hv => (hp β).2.2 κ κ' e hv)⟩
    · rw [reads_lb_eq hr ((hF u).mid i h1 h2) β (g β)]
      exact (hC.carC u i h1 h2 (g β)).Lb_eq
    · rw [hoU β v hv]
      exact (hC.carC u i h1 h2 (g β)).Uloc_eq v

structure TopP {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} {u : B.Word} {a : I.ι} (S : TwStep I l Z H F Q u a B.R.m) : Prop where
  chiM : ∀ h1 β (κ : (S.K h1 le_rfl β).lev.U) (κ' : ((F u).cls B.R.m le_rfl (Or.inr rfl)).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (S.K h1 le_rfl β).lev.chi κ = ((F u).cls B.R.m le_rfl (Or.inr rfl)).lev.chi κ'
  top : a ≠ I.mu0 → ∀ h1 β, I.TopBase l Z u a (S.K h1 le_rfl β).lev.U fun c => ((S.K h1 le_rfl (S.chOf c)).y ⟨c, rfl⟩).1
  topk : a ≠ I.mu0 → ∀ h1, ∃ k, I.Reads u a B.R.m S.chOf (fun β => (S.K h1 le_rfl β).lev.Lb) (fun β => (S.K h1 le_rfl β).lev.U)
    (fun β => (S.K h1 le_rfl β).lev.chi) (fun c => ((S.K h1 le_rfl (S.chOf c)).y ⟨c, rfl⟩).1)
    (fun c s => ((S.K h1 le_rfl (S.chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)

theorem twStep_top (hok : I.Ok) (pins : TC.Pins B X) {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (u : B.Word) (a : I.ι)
    (hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v)
    (hF : ∀ u, I.StdF l Z u (F u)) (hC : CarH H F) : ∃ S : TwStep I l Z H F Q u a B.R.m, TopP S := by
  have hoff : ∀ v ∈ Q, ((B.T u : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∉ v.asIdeal ∧ ∀ j, (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g j : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∉ v.asIdeal :=
    fun v hv => GlobalTheory.T.twistPlaces_prime_to_levelAndTypePrimes I hok l u a v ((hQ v).1 hv)
  have h1m : 1 ≤ B.R.m := one_le_m B.R
  have hr0 := (hF u).ends B.R.m le_rfl (Or.inr rfl)
  have hno : ∀ h2 : B.R.m + 1 ≤ B.R.m, False := fun h2 => by omega
  by_cases ha : a = I.mu0
  · subst ha
    let K : ∀ β : Unit, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) B.R.m le_rfl
        (fun c : {c // (fun _ : (I.stp u I.mu0 B.R.m).Cl => ()) c = β} => (I.chain l u I.mu0).stab B.R.m c.1)
        (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u I.mu0 B.R.m c.1)) :=
      chartAll (chartWiden Set.subset_union_left ((F u).cls B.R.m le_rfl (Or.inr rfl)).toChart)
    have hr : I.ReadsK l Z u I.mu0 B.R.m le_rfl (fun _ => ()) K := hr0
    refine ⟨twStep_mk hok pins u I.mu0 B.R.m h1m le_rfl hoff Unit inferInstance (fun _ => ()) (fun _ => chM H u) K hr (fun h2 => (hno h2).elim) (fun β => ?_) (fun β v _ => ?_)
      (fun _ h2 => (hno h2).elim) (fun _ => ⟨inferInstance⟩) (fun h => absurd rfl h) (fun _ h2 => (hno h2).elim), ?_, ?_, ?_⟩
    · exact (hC.carM u).Lb_eq
    · exact (hC.carM u).Uloc_eq v
    · intro _ β κ κ' e _
      have : κ = κ' := Subtype.ext e
      subst this
      rfl
    · exact fun h => absurd rfl h
    · exact fun h => absurd rfl h
  · obtain ⟨K1, ⟨k1, hR1, hk1⟩, htop, hoU, hfin, hchi⟩ := GlobalTheory.T.chart_lastStep_twistBasePoint I hok pins l Z u a Q ((F u).cls B.R.m le_rfl (Or.inr rfl)) hQ hr0
    have hr : I.ReadsK l Z u a B.R.m le_rfl (fun _ => ()) K1 := ⟨k1, hR1⟩
    refine ⟨twStep_mk hok pins u a B.R.m h1m le_rfl hoff Unit inferInstance (fun _ => ()) (fun _ => chM H u) K1 hr (fun h2 => (hno h2).elim) (fun β => ?_) (fun β v hv => ?_)
      (fun _ h2 => (hno h2).elim) (fun _ => ⟨inferInstance⟩) (fun _ β => hfin) (fun _ h2 => (hno h2).elim), ?_, ?_, ?_⟩
    · have e0 : (K1 β).lev.Lb = ((F u).cls B.R.m le_rfl (Or.inr rfl)).lev.Lb := by
        obtain ⟨k, R⟩ := hr
        obtain ⟨k', R'⟩ := hr0
        ext x
        exact (R.lb β x).trans (R'.lb () x).symm
      rw [e0]
      exact (hC.carM u).Lb_eq
    · have : β = () := rfl
      subst this
      rw [hoU v hv]
      exact (hC.carM u).Uloc_eq v
    · intro _ β κ κ' e hv
      exact hchi κ κ' e hv
    · intro _ _ β
      exact htop
    · intro _ _
      exact ⟨k1, hR1, hk1⟩


set_option maxHeartbeats 8000000 in
structure TwPack (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u))
    (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (u : B.Word) (a : I.ι) where
  St : ∀ i, TwStep I l Z H F Q u a i
  top : TopP (St B.R.m)
  J : TwLevJ I l Z F Q u a (St (B.R.m - 1)).chOf (fun β => (St (B.R.m - 1)).K (by have := B.R.two_le_m; omega) (Nat.sub_le _ _) β)
  off : ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → J.chiJ κ = (F u).levJ.chi κ'

theorem twBefore_cl_nonempty (hOk : I.Ok) (u : B.Word) (a : I.ι) : Nonempty (I.stp u a (B.R.m - 1)).Cl := by
  classical
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  have hL := hOk.idx_ok a
  obtain ⟨b0x, -⟩ := hL.last_uniq
  let b0 : Idx I.sel (I.tup a) (I.idx a) (B.R.m - 1) := ⟨some (cast (by rw [show B.R.m - 1 = B.R.m - 2 + 1 by omega]) b0x), by simp; omega⟩
  let q0 : (I.stp u a (B.R.m - 1)).D b0 := ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup a)) (DecoF.base B.fields.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))).deco.1.N
      (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst a).M : ℤ))}), by
    show _ ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) (B.R.m - 1)).ys _
    rw [ysAt_ys_of_eq _ _ _ hmj]
    exact ⟨0, zero_mem _, rfl⟩⟩
  exact ⟨(I.stp u a (B.R.m - 1)).cl b0 q0⟩

set_option maxHeartbeats 8000000 in
theorem twPack_ex (hok : I.Ok) (pins : TC.Pins B X) {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (u : B.Word) (a : I.ι)
    (hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v) (hF : ∀ u, I.StdF l Z u (F u)) (hJ : ∀ u j v h, (F u).glevJ.fr j v h = 1) (hC : CarH H F) :
    Nonempty (TwPack (I := I) (l := l) (Z := Z) H F Q u a) := by
  have ex : ∀ i, Nonempty (TwStep I l Z H F Q u a i) := fun i => by
    by_cases h0 : i = 0
    · subst h0
      exact twStep_out u a 0 (by omega) (fun c => H.chOf u 0 ((I.eCls0 l u a).symm c))
    · by_cases h2 : i + 1 ≤ B.R.m
      · exact twStep_mid hok pins u a i (by omega) h2 hQ hF hC
      · by_cases h3 : i = B.R.m
        · subst h3
          exact (twStep_top hok pins u a hQ hF hC).elim fun S _ => ⟨S⟩
        · obtain ⟨f⟩ := GlobalTheory.T.nonempty_classMap_above_lastStep I hok u a i (by omega)
          exact twStep_out u a i (by omega) (fun c => H.chOf u i (f c))
  obtain ⟨Sm, hSm⟩ := twStep_top (F := F) (Q := Q) hok pins u a hQ hF hC
  let St : ∀ i, TwStep I l Z H F Q u a i := Function.update (fun i => (ex i).some) B.R.m Sm
  have hSt : St B.R.m = Sm := Function.update_self _ _ _
  have h1 : 1 ≤ B.R.m - 1 := by have := B.R.two_le_m; omega
  have h2 := succ_pred_m B.R
  have hfin : ∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z ((St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β).lev := fun β => by
    by_cases ha : a = I.mu0
    · refine ⟨1, one_pos, fun κ hκ => ?_⟩
      rw [pow_one]
      refine ((St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β).lev.chi_triv κ fun v hv => ?_
      rcases hv with hv | hv
      · exact hκ v hv
      · exact absurd (ha ▸ (hQ v).1 hv) (GlobalTheory.T.not_twistPlace_referenceTuple I hok v)
    · obtain ⟨n, hn, h⟩ := (St (B.R.m - 1)).chiFin ha h1 (Nat.sub_le _ _) β
      exact ⟨n, hn, fun κ _ => h κ⟩
  obtain ⟨J⟩ := GlobalTheory.T.exists_penultimateLevel_couplingCosets I hok pins l Z H.Ch H.chOf F u a Q h1 (St (B.R.m - 1)).Ch (St (B.R.m - 1)).fin (St (B.R.m - 1)).chOf
    (fun β => (St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β) (St (B.R.m - 1)).gOf hQ hF hJ ((St (B.R.m - 1)).readsQ h1 (Nat.sub_le _ _) h2) hfin
    (fun β v hv => (St (B.R.m - 1)).offK h1 h2 β v hv) (fun β κ κ' e hv => (St (B.R.m - 1)).chiC h1 h2 β κ κ' e hv)
  have hLb : (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) J.levJ.Lb := by
    obtain ⟨c⟩ := twBefore_cl_nonempty hok u a
    rw [← J.lb ((St (B.R.m - 1)).chOf c), ← (F u).levJ_Lb h1 ((St (B.R.m - 1)).gOf ((St (B.R.m - 1)).chOf c))]
    exact (reads_lb_eq ((St (B.R.m - 1)).reads h1 (Nat.sub_le _ _)) ((hF u).mid (B.R.m - 1) h1 h2) _ _).symm
  have hoffx := GlobalTheory.T.exists_levelJ_character_eq_member_off_places I hok pins l Z H.Ch H.chOf F u a Q h1 (St (B.R.m - 1)).Ch (St (B.R.m - 1)).fin (St (B.R.m - 1)).chOf
    (fun β => (St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β) (St (B.R.m - 1)).gOf hQ hF hJ ((St (B.R.m - 1)).reads h1 (Nat.sub_le _ _))
    (fun β v hv => (St (B.R.m - 1)).offK h1 h2 β v hv) (fun β κ κ' e hv => (St (B.R.m - 1)).chiC h1 h2 β κ κ' e hv) J
  have fin : (∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : ((St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β).lev.U),
      κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → ((St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β).lev.chi κ' = χ κ) ∧
      ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
        (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ') := by
    first | exact hoffx hLb | exact hoffx
  obtain ⟨χ, hχ, hχ'⟩ := fin
  exact ⟨⟨St, hSt ▸ hSm, { J with chiJ := χ, chiJ_eq := hχ }, hχ'⟩⟩

theorem reL_inj {a b : ℕ} (h : a = b) {E : Type} [Field E] [NumberField E] {L L' : Submodule (𝓞 E) (Fin a → E)}
    (e : reL h L = reL h L') : L = L' :=
  Submodule.map_injective_of_injective (f := (reV h E : (Fin a → E) →ₗ[E] (Fin b → E)).restrictScalars (𝓞 E)) (reV h E).injective e

def stab0Equiv (u : B.Word) (a : I.ι) (c : (I.stp u I.mu0 0).Cl) (c' : (I.stp u a 0).Cl) : (I.stp u I.mu0 0).Stab c ≃* (I.stp u a 0).Stab c' :=
  have h0 : Subsingleton ((I.stp u I.mu0 0).Stab c) := ⟨fun x y => Subtype.ext
    (((l.lev u I.mu0).free0 c.1 x.1 _ x.2).trans ((l.lev u I.mu0).free0 c.1 y.1 _ y.2).symm)⟩
  have h1 : Subsingleton ((I.stp u a 0).Stab c') := ⟨fun x y => Subtype.ext
    (((l.lev u a).free0 c'.1 x.1 _ x.2).trans ((l.lev u a).free0 c'.1 y.1 _ y.2).symm)⟩
  { toFun := fun _ => 1
    invFun := fun _ => 1
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _
    map_mul' := fun _ _ => Subsingleton.elim _ _ }


set_option maxHeartbeats 4000000 in
def twT {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
    (Q : I.ι → Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (hQ : ∀ a v, v ∈ Q a ↔ inQ a v)
    (p : ∀ u a, TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a) : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ where
  eCls0 u μ := I.eCls0 l u μ
  eStab0 u μ c := stab0Equiv (l := l) u μ c _
  eY _ _ _ _ := Equiv.refl _
  de_eq _ _ _ _ _ _ := rfl
  twisted_character_eq u μ φ c y := by
    show φ ((I.eCls0 l u μ).symm (I.eCls0 l u μ c)) y = φ c y
    exact congrArg (fun c' => φ c' y) (Equiv.symm_apply_apply _ c)
  Q := Q
  Q_iff := hQ
  Ch u μ i := ((p u μ).St i).Ch
  ChFin u μ i := ((p u μ).St i).fin
  Ch_m u μ := ((p u μ).St B.R.m).uniq rfl
  chOf u μ i := ((p u μ).St i).chOf
  lev u μ i h1 hm β := ((p u μ).St i).lev h1 hm β
  lat u μ i := I.latAt u μ i
  cls u μ _ i h1 hm β := ((p u μ).St i).cls h1 hm β
  levJ u μ _ := (p u μ).J.levJ
  Yb u μ _ := (p u μ).J.Yb
  YbFin u μ _ := (p u μ).J.YbFin
  YbAct u μ _ := (p u μ).J.YbAct
  yb u μ _ := (p u μ).J.yb
  yb_orbit u μ _ := (p u μ).J.yb_orbit
  levJ_Lb u μ h β := by
    have e1 := (((p u μ).St (B.R.m - 1)).car h (Nat.sub_le _ _) β).Lb_eq
    have e2 := (p u μ).J.lb β
    rw [e1] at e2
    exact reL_inj _ e2
  levJ_le u μ h β := by
    have e1 := (((p u μ).St (B.R.m - 1)).car h (Nat.sub_le _ _) β).U_eq
    have e2 := (p u μ).J.le β
    rw [e1] at e2
    exact (Subgroup.map_le_map_iff_of_injective (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).injective).1 e2
  levJ_stab u μ h β κ := by
    have e1 := (((p u μ).St (B.R.m - 1)).car h (Nat.sub_le _ _) β).U_eq
    have e2 := (p u μ).J.stab β κ
    rw [e1] at e2
    exact (Subgroup.mem_map_iff_mem (f := (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)
      (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).injective).symm.trans e2
  DGam_one _ _ := rfl


set_option maxHeartbeats 4000000 in
def twJ {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
    (Q : I.ι → Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (hQ : ∀ a v, v ∈ Q a ↔ inQ a v)
    (p : ∀ u a, TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a)
    (hoff : ∀ (u : B.Word) a, ∀ v ∈ Q a, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, (((I.rec7 l Z).host.g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) :
    Formalism.L2.Herm.TwChJointS (twT Q hQ p) H where
  gOf u μ i := ((p u μ).St i).gOf
  Uloc_off := by
    intro u μ i h1 hm β v hv
    intros
    exact ((p u μ).St i).offU h1 hm β v hv
  Lb_off u μ i h1 hm β v hv := congrArg _ (((p u μ).St i).offL h1 hm β)
  Q_off u μ := hoff u μ

theorem idY_twYS {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)} (hF : ∀ u, I.StdF l Z u (F u))
    (Q : I.ι → Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (hQ : ∀ a v, v ∈ Q a ↔ inQ a v)
    (p : ∀ u a, TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a) (u : B.Word) (μ : I.ι) (i : ℕ)
    (hi : i ≤ B.R.m) : I.IdY l Z u μ i hi (twYS (twT Q hQ p) F u μ i hi) := by
  intro y
  have e : (I.rec7 l Z).R.m = B.R.m := rfl
  show (eYS (F u) i hi y).1 = y.1
  unfold eYS
  split_ifs with h
  · exact (hF u).eY i hi h y
  · exact (hF u).eYC i (by omega) (by omega) y


set_option maxHeartbeats 8000000 in
def twW (hok : I.Ok) (pins : TC.Pins B X) (l0 : I.Law0 l) {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)} (hF : ∀ u, I.StdF l Z u (F u))
    {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
    (Q : I.ι → Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (hQ : ∀ a v, v ∈ Q a ↔ inQ a v)
    (p : ∀ u a, TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a)
    (hoff : ∀ (u : B.Word) a, ∀ v ∈ Q a, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, (((I.rec7 l Z).host.g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal)
    (A : ∀ u a, TwAtT (I.tw l l0 Z) u a) (hA : ∀ u a, (A u a).eVT = Equiv.refl _) :
    TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) (twT Q hQ p) (twJ Q hQ p hoff) F := by
  refine'
    { atT := A
      ch u μ _ i h1 hm β := ((p u μ).St i).K h1 hm β
      car u μ _ i h1 hm β := ((p u μ).St i).car h1 hm β
      chi_fin u μ hμ i h1 hm β := ((p u μ).St i).chiFin hμ h1 hm β
      chi_offC u μ _ i h1 h2 β κ κ' e hv := ((p u μ).St i).chiC h1 h2 β κ κ' e hv
      chi_offM u μ _ h1 β κ κ' e hv := (p u μ).top.chiM h1 β κ κ' e hv
      chiJ u μ _ := (p u μ).J.chiJ
      chiJ_eq u μ _ _ β κ κ' e := (p u μ).J.chiJ_eq β κ κ' e
      val u μ _ i h1 hm := by
        have hv := GlobalTheory.T.hermitianChart_complex_rational_integral_forms I hok pins l Z u μ i hm _ _ _ (fun β => ((p u μ).St i).K h1 hm β) (twYS (twT Q hQ p) F u μ i hm)
          (((p u μ).St i).reads h1 hm) (idY_twYS hF Q hQ p u μ i hm)
        exact ⟨hv.Fi, hv.rat, fun w _ => hv.lat w trivial⟩
      dil u μ _ i h1 hm := GlobalTheory.T.diamondOperators_on_charts I hok pins l Z u μ i hm _ _ _ (fun β => ((p u μ).St i).K h1 hm β) (twYS (twT Q hQ p) F u μ i hm)
        ((A u μ).eV (F u).atT) (((p u μ).St i).reads h1 hm) (((p u μ).St i).fk h1 hm) (idY_twYS hF Q hQ p u μ i hm) (by
          intro v
          show ((F u).atT.eV ((A u μ).eVT v)).1 = _
          rw [hA u μ]
          exact (hF u).eV v)
      ipV u μ i hi := (GlobalTheory.Mem.Col2.MetricTie.ipV_norm_tie I hok pins l Z u μ i hi _ (idY_twYS hF Q hQ p u μ i hi)).1
      norm u μ i hi := (GlobalTheory.Mem.Col2.MetricTie.ipV_norm_tie I hok pins l Z u μ i hi _ (idY_twYS hF Q hQ p u μ i hi)).2
      twisted_e0_at_mu0_eq_eMu0 u x := GlobalTheory.T.stepZeroFormsIdentification_referenceTuple_eq_self I hok l Z l0 u x, .. }
  all_goals
    intro u μ h κ κ' e hv
    exact (p u μ).off κ κ' e hv

def twJS {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
    (Q : I.ι → Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (hQ : ∀ a v, v ∈ Q a ↔ inQ a v)
    (p : ∀ u a, TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a) : SymmetricTwistedJointForms (twT Q hQ p) F where
  J_g u μ _ j v hv x hx := (p u μ).J.J_g j v hv x hx
  J_off u μ _ v hv hb := (p u μ).J.J_off v hv hb
  yG u μ _ := (p u μ).J.yG
  yG_smul u μ _ κ y j v hv := (p u μ).J.yG_smul κ y j v hv
  YQ u μ _ := (p u μ).J.YQ
  yQ u μ _ := (p u μ).J.yQ
  y_inj u μ _ := (p u μ).J.y_inj
  yQ_off u μ _ := (p u μ).J.yQ_off

end


set_option maxHeartbeats 8000000 in
theorem tw_chains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → (∀ u j v h, (F u).glevJ.fr j v h = 1) → ∃ (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), Formalism.L2.Herm.TwChMu0 T ∧ I.StdW l Z l0 W ∧ Nonempty (SymmetricTwistedJointForms T F) := by
  intro B X I hok pins l Z l0 inQ H F hin hF hC hJ
  have hF' : ∀ u, I.StdF l Z u (F u) := fun u => (hF u).1
  classical
  have hQex : ∀ a, ∃ Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ∀ v, v ∈ Q ↔ I.UnderQ a v :=
    fun a => ⟨(I.Q a).image (fun P => P.under (𝓞 B.host.F)), fun v => Finset.mem_image⟩
  choose Q hQ using hQex
  have hQ' : ∀ a v, v ∈ Q a ↔ inQ a v := fun a v => (hQ a v).trans (hin a v).symm
  have P : ∀ u a, Nonempty (TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a) := fun u a => twPack_ex hok pins u a (hQ a) hF' hJ hC
  let p := fun u a => (P u a).some
  choose A hA hA' using fun u a => GlobalTheory.Mem.Col2.TwAtStd.twAtT_exists I hok pins l Z l0 u a
  have hoff : ∀ (u : B.Word) a, ∀ v ∈ Q a, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, (((I.rec7 l Z).host.g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal :=
    fun u a v hv => GlobalTheory.T.twistPlaces_prime_to_levelAndTypePrimes I hok l u a v ((hQ a v).1 hv)
  refine ⟨twT Q hQ' p, twJ Q hQ' p hoff, twW hok pins l0 hF' Q hQ' p hoff A hA, ⟨fun u i hi => Equiv.ext fun y => rfl,
    fun u => Equiv.ext fun c => GlobalTheory.T.eCls0_mu0_eq_self I hok l u c⟩, ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl, hA, ?_,
    fun u a _ i h1 hm => ((p u a).St i).reads h1 hm, fun u a ha h1 β => (p u a).top.top ha h1 β,
    fun u a ha h1 => (p u a).top.topk ha h1, fun u a _ i h1 hm β => ((p u a).St i).fk h1 hm β⟩, ⟨twJS Q hQ' p⟩⟩
  intro u a v r
  show ((A u a).eFv v).symm ((F u).atT.res ((A u a).eVT v) r) = _
  rw [(hF' u).res]
  exact ((A u a).eFv v).symm_apply_eq.2 (hA' u a v r).symm


end GlobalTheory.Mem.Col2.TC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceTwistedChainsFormsClassesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumnChoice_twistedChains_formsClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → (∀ u j v h, (F u).glevJ.fr j v h = 1) → ∃ (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), Formalism.L2.Herm.TwChMu0 T ∧ I.StdW l Z l0 W ∧ Nonempty (SymmetricTwistedJointForms T F) := by
  first | exact @GlobalTheory.Mem.Col2.TC.tw_chains | exact GlobalTheory.Mem.Col2.TC.tw_chains | (intros; apply GlobalTheory.Mem.Col2.TC.tw_chains <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsChainDataWithBasePoints
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 4000000 in
theorem tw_ties_with_points : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), Formalism.L2.Herm.TwChMu0 T ∧ I.StdW l Z l0 W ∧ Nonempty (SymmetricTwistedJointForms T F) ∧
    (∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m), ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) := by
  intro B X I hI hP l Z l0 inQ H F hQ hF hH
  obtain ⟨T, J, W, h0, hW, hJ⟩ := GlobalTheory.T.trueColumnChoice_twistedChains_formsClasses I hI hP l Z l0 inQ H F hQ hF hH (fun u => (hF u).2.2)
  exact ⟨T, J, W, h0, hW, hJ, fun u a ha h1 => hW.topk u a ha h1⟩

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsChainDataWithBasePointsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumnChoice_exists_chainData_with_basePoints : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), Formalism.L2.Herm.TwChMu0 T ∧ I.StdW l Z l0 W ∧ Nonempty (SymmetricTwistedJointForms T F) ∧
    (∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m), ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.tw_ties_with_points | exact GlobalTheory.Mem.Col2.TC.tw_ties_with_points | (intros; apply GlobalTheory.Mem.Col2.TC.tw_ties_with_points <;> assumption)
end
