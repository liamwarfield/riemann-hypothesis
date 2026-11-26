module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemFilDDiag
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemGKBot
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.BasisOfUnit
open TensorProduct Module

namespace UpperTheory.V.Loc.R0

variable {Q E F B H : Type} [Field Q] [Field E] [Algebra Q E] [Field F] [Algebra Q F]
  [CommRing B] [Algebra Q B] [Algebra F B] [IsScalarTower Q F B]

theorem inv_tensor [FiniteDimensional Q E] (a : H → B ≃ₐ[Q] B)
    (ha : ∀ b, (∀ g, a g b = b) → ∃ c : F, algebraMap F B c = b) (z : E ⊗[Q] B)
    (hz : ∀ g, (a g).toLinearMap.lTensor E z = z) :
    ∃ c : E ⊗[Q] F, (IsScalarTower.toAlgHom Q F B).toLinearMap.lTensor E c = z := by
  let b := Module.finBasis Q E
  let φ : Fin (finrank Q E) → E ⊗[Q] B →ₗ[Q] B := fun i =>
    (TensorProduct.lid Q B).toLinearMap ∘ₗ (b.coord i).rTensor B
  have h1 : ∀ y : E ⊗[Q] B, ∑ i, b i ⊗ₜ[Q] φ i y = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e c =>
      conv_rhs => rw [← b.sum_repr e, sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [φ, smul_tmul]
    | add x y hx hy => simp only [map_add (f := _), tmul_add, Finset.sum_add_distrib, hx, hy]
  have h2 : ∀ g i (y : E ⊗[Q] B), φ i ((a g).toLinearMap.lTensor E y) = a g (φ i y) := by
    intro g i y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e c => simp [φ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  choose c hc using fun i => ha (φ i z) fun g => by rw [← h2, hz]
  refine ⟨∑ i, b i ⊗ₜ[Q] c i, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h1 z, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hc]
  rfl

theorem basis_of_unit [FiniteDimensional Q E] [Nontrivial B] (a : H → B ≃ₐ[Q] B)
    (ha : ∀ b, (∀ g, a g b = b) → ∃ c : F, algebraMap F B c = b) (κ : H → E)
    (T : H → E ⊗[Q] B →ₗ[E] E ⊗[Q] B) (hT : ∀ g v b, T g (v ⊗ₜ[Q] b) = (κ g * v) ⊗ₜ[Q] a g b)
    (S : E ⊗[Q] F →ₗ[Q] Module.End Q (E ⊗[Q] B))
    (hS : ∀ e f v b, S (e ⊗ₜ[Q] f) (v ⊗ₜ[Q] b) = (e • v) ⊗ₜ[Q] (f • b))
    (x : E ⊗[Q] B) (hu : IsUnit x) (hx : ∀ g, T g x = x) (y : E ⊗[Q] B) (hy : ∀ g, T g y = y) :
    ∃! c : E ⊗[Q] F, y = S c x := by
  let j := (IsScalarTower.toAlgHom Q F B).toLinearMap.lTensor E
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (algebraMap F B).injective
  have h1 : ∀ c z, S c z = j c * z := by
    intro c z
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c c' hc hc' => simp only [map_add (f := _), LinearMap.add_apply, hc, hc', add_mul]
    | tmul e f =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add (f := _), hz, hz', mul_add]
      | tmul v b => simp [hS, j, Algebra.smul_def]
  have h2 : ∀ g z w, T g (z * w) = (a g).toLinearMap.lTensor E z * T g w := by
    intro g z w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add c c' hc hc' => simp only [map_add (f := _), hc, hc', add_mul]
    | tmul e f =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add (f := _), hz, hz', mul_add]
      | tmul v b => simp [hT, mul_left_comm]
  obtain ⟨z, rfl⟩ : ∃ z, y = z * x := ⟨y * ↑hu.unit⁻¹, by simp [mul_assoc]⟩
  obtain ⟨c, hc⟩ := inv_tensor a ha z fun g => hu.mul_right_cancel (by
    have := hy g
    rwa [h2, hx] at this)
  refine ⟨c, by simp only [h1]; rw [← hc], fun c' hc' => hj ?_⟩
  simp only [h1] at hc'
  rw [← hu.mul_right_cancel hc']
  exact hc.symm

theorem unit_of_span (D : Submodule E (E ⊗[Q] B)) (hD : finrank E D = 1) {m : ℕ} (b : Fin m → B)
    (d : Fin m → E ⊗[Q] B) (hd : ∀ i, d i ∈ D)
    (h : (1 : E ⊗[Q] B) = ∑ i, AlgebraTensorModule.map (LinearMap.id : E →ₗ[E] E) (LinearMap.mulLeft Q (b i)) (d i)) :
    ∃ x ∈ D, IsUnit x := by
  obtain ⟨x, -, hx⟩ := finrank_eq_one_iff'.1 hD
  choose e he using fun i => hx ⟨d i, hd i⟩
  have h1 : ∀ c (z : E ⊗[Q] B), AlgebraTensorModule.map (LinearMap.id : E →ₗ[E] E) (LinearMap.mulLeft Q c) z =
      ((1 : E) ⊗ₜ[Q] c) * z := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz', mul_add]
    | tmul v b => simp
  refine ⟨x, x.2, IsUnit.of_mul_eq_one (∑ i, e i • ((1 : E) ⊗ₜ[Q] b i)) ?_⟩
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : d i = e i • (x : E ⊗[Q] B) := (congrArg Subtype.val (he i)).symm
  rw [h1, this, mul_smul_comm, mul_smul_comm, mul_comm]

end UpperTheory.V.Loc.R0
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.R0

variable {l : ℕ} [Fact l.Prime]

theorem mem_Dcr {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V) (x : V ⊗[ℚ_[l]] Bcr l) :
    x ∈ Dcr φ ρ ↔ ∀ g, actC φ ρ g x = x := by
  simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_Ddr {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V) (x : V ⊗[ℚ_[l]] Bdr l) :
    x ∈ Ddr φ ρ ↔ ∀ g, actD φ ρ g x = x := by
  simp only [Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_GK_bot (g : GQ l) : g ∈ GK (botExt l) := by simp [GK, botExt]

variable {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E]
  [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]

theorem char_cr (κ : GQ l →* Eˣ) (h : IsCr (GK (botExt l)).subtype (chRep (κ.comp (GK (botExt l)).subtype))) :
    ∃ x : E ⊗[ℚ_[l]] Bcr l, (∀ g, actC (MonoidHom.id _) (chRep κ) g x = x) ∧ ∀ (L : FinExt l),
      ∀ y ∈ Dcr (GK L).subtype (chRep (κ.comp (GK L).subtype)), ∃! c : E ⊗[ℚ_[l]] ↥(K0 L), y = smulC E L c x := by
  obtain ⟨T⟩ := tiedP l
  have hdom : IsDomain (PP l).R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  have hc := (isCrField (botExt l) _).1.1 ((isCrIff (botExt l) _).1.1 h)
  have hf : GlobalTheory.RegularRing.FracInv ((PP l).PD (botExt l)) := by
    intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l _ _ T _ y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [(PP l).PD_actB, (PP l).PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  have hu : GlobalTheory.RegularRing.LineUnit ((PP l).PD (botExt l)) := by
    intro b hb h
    refine (GlobalTheory.T.periodRings_regular_phi_surjective_fil l _ _ T).1 (botExt l) b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    exact ⟨x, by rw [← (PP l).PD_actB (botExt l) ⟨g, hg⟩, hx, Algebra.smul_def]⟩
  obtain ⟨m, b, d, hd, h1⟩ := GlobalTheory.Per.TiedSpan.exists_sum_of_isCrys _ hf hu _ hc 1
  have h0 : finrank ℚ_[l] ↥(K0 (botExt l)) = 1 := by
    rw [show K0 (botExt l) = ⊥ from bot_inf_eq _, IntermediateField.finrank_bot]
  rw [IsCrys, h0, finrank_self] at hc
  obtain ⟨x, hx, hxu⟩ := unit_of_span _ hc b d hd h1
  have hx' : ∀ g, actC (MonoidHom.id _) (chRep κ) g x = x := by
    intro g
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    refine Eq.trans ?_ (hx ⟨g, mem_GK_bot g⟩)
    unfold actC actVB
    congr 2
    ext b
    exact ((PP l).PD_actB (botExt l) ⟨g, mem_GK_bot g⟩ b).symm
  refine ⟨x, hx', fun L y hy => ?_⟩
  exact basis_of_unit (H := ↥(GK L)) (fun g => (PP l).actQ g)
    (fun b hb => ((PP l).PD L).invB b fun g => by rw [(PP l).PD_actB]; exact hb g) (fun g => (κ g : E))
    (actC (GK L).subtype (chRep (κ.comp (GK L).subtype))) (fun g v b => rfl) (smulC E L) (fun e f v b => rfl)
    x hxu (fun g => hx' g) y ((mem_Dcr _ _ _).1 hy)

theorem char_dr (κ : GQ l →* Eˣ) (h : IsDr (GK (botExt l)).subtype (chRep (κ.comp (GK (botExt l)).subtype))) :
    ∃ x : E ⊗[ℚ_[l]] Bdr l, (∀ g, actD (MonoidHom.id _) (chRep κ) g x = x) ∧ ∀ (L : FinExt l),
      ∀ y ∈ Ddr (GK L).subtype (chRep (κ.comp (GK L).subtype)), ∃! c : E ⊗[ℚ_[l]] ↥L.1, y = smulD E L c x := by
  obtain ⟨T⟩ := tiedP l
  have hF := GlobalTheory.RegularRing.isField_of_tied T
  have := hF.nontrivial
  have hc := (isCrField (botExt l) _).2.1.1 ((isCrIff (botExt l) _).2.1 h)
  obtain ⟨m, b, d, hd, h1⟩ := GlobalTheory.Per.DeRhamSpan.span_of_isField _ _ hF hc 1
  have h0 : finrank ℚ_[l] ↥(botExt l).1 = 1 := IntermediateField.finrank_bot
  rw [IsDR, h0, finrank_self] at hc
  obtain ⟨x, hx, hxu⟩ := unit_of_span _ hc b d hd h1
  have hx' : ∀ g, actD (MonoidHom.id _) (chRep κ) g x = x := by
    intro g
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    refine Eq.trans ?_ (hx ⟨g, mem_GK_bot g⟩)
    unfold actD actVdR
    congr 2
    ext b
    exact ((PP l).PD_actdR (botExt l) ⟨g, mem_GK_bot g⟩ b).symm
  refine ⟨x, hx', fun L y hy => ?_⟩
  exact basis_of_unit (H := ↥(GK L)) (fun g => (PP l).actQdR g)
    (fun b hb => ((PP l).PD L).invdR b fun g => by rw [(PP l).PD_actdR]; exact hb g) (fun g => (κ g : E))
    (actD (GK L).subtype (chRep (κ.comp (GK L).subtype))) (fun g v b => rfl) (smulD E L) (fun e f v b => rfl)
    x hxu (fun g => hx' g) y ((mem_Ddr _ _ _).1 hy)

end UpperTheory.V.Loc.R0
end

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.R0

variable {l : ℕ} [Fact l.Prime]

section Map

variable {G A V V' : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V']
  [IsScalarTower ℚ_[l] A V']


variable (l) in
def tm (B : Type) [AddCommGroup B] [Module ℚ_[l] B] (f : V →ₗ[A] V') : V ⊗[ℚ_[l]] B →ₗ[A] V' ⊗[ℚ_[l]] B :=
  AlgebraTensorModule.map f LinearMap.id

theorem tm_tmul {B : Type} [AddCommGroup B] [Module ℚ_[l] B] (f : V →ₗ[A] V') (v : V) (b : B) :
    tm l B f (v ⊗ₜ b) = f v ⊗ₜ b := rfl

variable (φ : G →* GQ l) {ρ : Representation A G V} {ρ' : Representation A G V'} (f : V →ₗ[A] V')

theorem tm_actC (g : G) (hf : ∀ x, f (ρ g x) = ρ' g (f x)) (y : V ⊗[ℚ_[l]] Bcr l) :
    tm l _ f (actC φ ρ g y) = actC φ ρ' g (tm l _ f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => exact congrArg (· ⊗ₜ _) (hf v)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tm_actD (g : G) (hf : ∀ x, f (ρ g x) = ρ' g (f x)) (y : V ⊗[ℚ_[l]] Bdr l) :
    tm l _ f (actD φ ρ g y) = actD φ ρ' g (tm l _ f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => exact congrArg (· ⊗ₜ _) (hf v)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tm_Dcr (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {y : V ⊗[ℚ_[l]] Bcr l} (hy : y ∈ Dcr φ ρ) :
    tm l _ f y ∈ Dcr φ ρ' := by
  simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hy ⊢
  intro g
  rw [← tm_actC φ f g (hf g), hy g]

theorem tm_FilD (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {i : ℤ} {y : V ⊗[ℚ_[l]] Bdr l} (hy : y ∈ FilD φ ρ i) :
    tm l _ f y ∈ FilD φ ρ' i := by
  have hyD : y ∈ Ddr φ ρ := hy.1
  simp only [Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hyD
  change tm l _ f y ∈ Ddr φ ρ' ∧ tm l _ f y ∈ FilT A V' i
  refine ⟨?_, ?_⟩
  · simp only [Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    rw [← tm_actD φ f g (hf g), hyD g]
  · obtain ⟨z, rfl⟩ := hy.2
    refine ⟨tm l _ f z, ?_⟩
    clear hy hyD
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tm_smulC (K : FinExt l) (c : A ⊗[ℚ_[l]] ↥(K0 K)) (y : V ⊗[ℚ_[l]] Bcr l) :
    tm l _ f (smulC V K c y) = smulC V' K c (tm l _ f y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
  | tmul a k =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => exact congrArg (· ⊗ₜ _) (f.map_smul a v)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tm_smulD (K : FinExt l) (c : A ⊗[ℚ_[l]] ↥K.1) (y : V ⊗[ℚ_[l]] Bdr l) :
    tm l _ f (smulD V K c y) = smulD V' K c (tm l _ f y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
  | tmul a k =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => exact congrArg (· ⊗ₜ _) (f.map_smul a v)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem smulC_one (K : FinExt l) (a : A) (y : V ⊗[ℚ_[l]] Bcr l) :
    smulC V K (a ⊗ₜ[ℚ_[l]] (1 : ↥(K0 K))) y = a • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul v b => exact congrArg (_ ⊗ₜ ·) (one_smul ↥(K0 K) b)
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]

end Map

section Diag

variable {G A : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] {n : ℕ}


variable (l) in
abbrev pr (B : Type) [AddCommGroup B] [Module ℚ_[l] B] (a : Fin n) :
    (Fin n → A) ⊗[ℚ_[l]] B →ₗ[A] A ⊗[ℚ_[l]] B := tm l B (LinearMap.proj a)


variable (l) in
abbrev inc (B : Type) [AddCommGroup B] [Module ℚ_[l] B] (a : Fin n) :
    A ⊗[ℚ_[l]] B →ₗ[A] (Fin n → A) ⊗[ℚ_[l]] B := tm l B (LinearMap.single A (fun _ => A) a)

variable {B : Type} [AddCommGroup B] [Module ℚ_[l] B]

theorem pr_inc (a b : Fin n) (x : A ⊗[ℚ_[l]] B) : pr l B a (inc l B b x) = if a = b then x else 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => by_cases h : a = b <;> simp [tm_tmul, h]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]; split_ifs <;> simp

theorem sum_inc_pr (y : (Fin n → A) ⊗[ℚ_[l]] B) : ∑ a, inc l B a (pr l B a y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [tm_tmul, ← sum_tmul, Finset.univ_sum_single]
  | add x y hx hy => simp only [map_add (f := _), Finset.sum_add_distrib, hx, hy]

variable {ρ : G →* GL (Fin n) A} {κ : Fin n → G →* Aˣ}
  (hρ : ∀ g, (ρ g : Matrix (Fin n) (Fin n) A) = Matrix.diagonal fun a => (κ a g : A))

include hρ

theorem proj_diag (a : Fin n) (g : G) (x : Fin n → A) :
    (LinearMap.proj a : (Fin n → A) →ₗ[A] A) (colRep ρ g x) = chRep (κ a) g (LinearMap.proj (R := A) a x) := by
  simp [colRep, chRep, hρ, Matrix.mulVec_diagonal]

theorem single_diag (a : Fin n) (g : G) (x : A) :
    LinearMap.single A (fun _ => A) a (chRep (κ a) g x) = colRep ρ g (LinearMap.single A (fun _ => A) a x) := by
  ext b
  by_cases h : b = a <;> simp [colRep, chRep, hρ, Matrix.mulVec_diagonal, h]

theorem mem_FilD_diag (φ : G →* GQ l) (i : ℤ) (y : (Fin n → A) ⊗[ℚ_[l]] Bdr l) :
    y ∈ FilD φ (colRep ρ) i ↔ ∀ a, pr l _ a y ∈ FilD φ (chRep (κ a)) i := by
  refine ⟨fun h a => tm_FilD φ _ (proj_diag hρ a) h, fun h => ?_⟩
  rw [← sum_inc_pr y]
  exact Submodule.sum_mem _ fun a _ => tm_FilD φ _ (single_diag hρ a) (h a)

end Diag

section Types

variable {A : Type} [CommRing A] [Algebra ℚ_[l] A] {n : ℕ} {K : FinExt l}
  {ρ : ↥(GK K) →* GL (Fin n) A} {κ : Fin n → ↥(GK K) →* Aˣ}
  (hρ : ∀ g, (ρ g : Matrix (Fin n) (Fin n) A) = Matrix.diagonal fun a => (κ a g : A))

include hρ

theorem hodge_diag (w : Fin n → ℤ) (hw : Function.Injective w) (m : ℤ → ℕ)
    (hm1 : ∀ a, m (w a) = 1) (hm0 : ∀ i, (∀ a, w a ≠ i) → m i = 0)
    (hF : ∀ a i, (i ≤ w a → FilD (GK K).subtype (chRep (κ a)) i = Ddr (GK K).subtype (chRep (κ a))) ∧
      (w a < i → FilD (GK K).subtype (chRep (κ a)) i = ⊥))
    (hB : ∀ a, ∃ x ∈ Ddr (GK K).subtype (chRep (κ a)), ∀ y ∈ Ddr (GK K).subtype (chRep (κ a)),
      ∃! c : A ⊗[ℚ_[l]] ↥K.1, y = smulD A K c x) :
    HodgeType K (colRep ρ) m := by
  have step : ∀ a i, w a ≠ i → ∀ y ∈ FilD (GK K).subtype (chRep (κ a)) i,
      y ∈ FilD (GK K).subtype (chRep (κ a)) (i + 1) := by
    intro a i h y hy
    rcases lt_or_gt_of_ne h with h | h
    · rw [(hF a i).2 h, Submodule.mem_bot] at hy
      exact hy ▸ Submodule.zero_mem _
    · rw [(hF a _).1 (Int.add_one_le_of_lt h)]
      exact hy.1
  intro i
  by_cases h : ∃ a, w a = i
  · obtain ⟨a, rfl⟩ := h
    obtain ⟨x, hx, hb⟩ := hB a
    rw [hm1]
    refine ⟨fun _ => inc l _ a x, fun _ => tm_FilD _ _ (single_diag hρ a) (by rwa [(hF a _).1 le_rfl]),
      fun y hy => ?_⟩
    have hy' := (mem_FilD_diag hρ _ _ _).1 hy
    obtain ⟨c, hc, hcu⟩ := hb _ (hy' a).1
    refine ⟨fun _ => c, (mem_FilD_diag hρ _ _ _).2 fun b => ?_, fun c' hc' => ?_⟩
    · rw [Fin.sum_univ_one, map_sub, ← tm_smulD, pr_inc]
      split_ifs with hba
      · subst hba
        rw [← hc, sub_self]
        exact Submodule.zero_mem _
      · rw [sub_zero]
        exact step b _ (fun e => hba (hw e)) _ (hy' b)
    · have h1 := (mem_FilD_diag hρ _ _ _).1 hc' a
      rw [Fin.sum_univ_one, map_sub, ← tm_smulD, pr_inc, if_pos rfl, (hF a _).2 (lt_add_one _),
        Submodule.mem_bot, sub_eq_zero] at h1
      funext j
      rw [Subsingleton.elim j 0]
      exact hcu _ h1
  · push Not at h
    rw [hm0 i h]
    refine ⟨Fin.elim0, fun a => a.elim0, fun y hy => ⟨Fin.elim0, ?_, fun _ _ => Subsingleton.elim _ _⟩⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    exact (mem_FilD_diag hρ _ _ _).2 fun b => step b i (h b) _ ((mem_FilD_diag hρ _ _ _).1 hy b)

theorem crys_diag {L : FinExt l} (h : K.1 ≤ L.1) (hN : ((GK L).subgroupOf (GK K)).Normal)
    (hC : Crys L ((colRep ρ).comp (incl h))) (t : Fin n → ↥(GK K) → A) (x : Fin n → A ⊗[ℚ_[l]] Bcr l)
    (hx : ∀ a, x a ∈ Dcr (GK L).subtype (chRep ((κ a).comp (incl h))))
    (hB : ∀ a, ∀ y ∈ Dcr (GK L).subtype (chRep ((κ a).comp (incl h))),
      ∃! c : A ⊗[ℚ_[l]] ↥(K0 L), y = smulC A L c (x a))
    (ht : ∀ a γ, actC (GK K).subtype (chRep (κ a)) γ (x a) = t a γ • x a) :
    CrysTypeOver K L h (colRep ρ) n fun γ => ∑ a, t a γ := by
  have key : ∀ (c : Fin n → A ⊗[ℚ_[l]] ↥(K0 L)) b,
      pr l _ b (∑ a, smulC (Fin n → A) L (c a) (inc l _ a (x a))) = smulC A L (c b) (x b) := by
    intro c b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ← tm_smulC, pr_inc, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨hN, hC, fun a => inc l _ a (x a), fun a => tm_Dcr _ _ (fun g => single_diag hρ a (incl h g)) (hx a),
    fun y hy => ?_, fun γ _ M hM => ?_⟩
  · choose c hc hcu using fun a => hB a _ (tm_Dcr _ _ (fun g => proj_diag hρ a (incl h g)) hy)
    refine ⟨c, ?_, fun c' hc' => funext fun b => hcu b _ ?_⟩
    · refine (sum_inc_pr y).symm.trans (Finset.sum_congr rfl fun a _ => ?_)
      rw [← tm_smulC]
      exact congrArg _ (hc a)
    · exact (congrArg _ hc').trans (key c' b)
  · rw [sum_tmul]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 := congrArg (pr l _ b) (hM b)
    rw [key (fun a => M a b), tm_actC _ _ _ (proj_diag hρ b γ), pr_inc, if_pos rfl, ht] at h1
    exact (hB b _ (Submodule.smul_mem _ (t b γ) (hx b))).unique h1 (smulC_one L _ _).symm

end Types

end UpperTheory.V.Loc.R0
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

namespace UpperTheory.V.Loc.R0

open Topology TensorProduct

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E]
  [IsTopologicalRing E]

private theorem cont_ch {G : Type} [Group G] [TopologicalSpace G] {κ : G →* Eˣ} (h : Continuous κ) :
    ContAction (chRep κ) :=
  (Units.continuous_val.comp (h.comp continuous_fst)).mul continuous_snd

private theorem cont_prod {G V V' : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module E V]
    [TopologicalSpace V] [AddCommGroup V'] [Module E V'] [TopologicalSpace V'] {ρ : Representation E G V}
    {ρ' : Representation E G V'} (h : ContAction ρ) (h' : ContAction ρ') : ContAction (ρ.prod ρ') :=
  (h.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk (h'.comp (continuous_fst.prodMk continuous_snd.snd))

private theorem isCr_char (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : GQ l →* Eˣ) (hκ : Continuous κ)
    (w : ℤ) (hw : ∀ g ∈ H, g ∈ Iq l → κ g = cycA l l E g ^ w) : IsCr H.subtype (chRep (κ.comp H.subtype)) :=
  crUnr H.subtype hH.isOpenEmbedding_subtypeVal _ (cont_ch (hκ.comp continuous_subtype_val)) w fun g hg x => by
    rw [Subgroup.subtype_apply, ← hw g g.2 hg]
    rfl

private theorem isCr_diag (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : Fin 3 → GQ l →* Eˣ)
    (hκ : ∀ a, Continuous (κ a)) (w : Fin 3 → ℤ) (hw : ∀ a, ∀ g ∈ H, g ∈ Iq l → κ a g = cycA l l E g ^ w a)
    (ρ : ↥H →* GL (Fin 3) E)
    (hρ : ∀ g, (ρ g : Matrix (Fin 3) (Fin 3) E) = Matrix.diagonal fun a => (κ a g : E)) :
    IsCr H.subtype (colRep ρ) := by
  have hφ : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  have hc : ∀ a, ContAction (chRep ((κ a).comp H.subtype)) := fun a =>
    cont_ch ((hκ a).comp continuous_subtype_val)
  have hcr := fun a => isCr_char H hH (κ a) (hκ a) (w a) (hw a)
  have hp := fun a g x => proj_diag (κ := fun a => (κ a).comp H.subtype) hρ a g x
  have h0 : ContAction (colRep ρ) := continuous_pi fun a => by
    have := (hc a).comp (continuous_fst.prodMk ((continuous_apply a).comp continuous_snd) :
      Continuous fun p : ↥H × (Fin 3 → E) => (p.1, p.2 a))
    exact this.congr fun p => (hp a p.1 p.2).symm
  have h1 := (isCrys_isDR_prod _ hφ _ _ (hc 0) (cont_prod (hc 1) (hc 2))).1 (hcr 0)
    ((isCrys_isDR_prod _ hφ _ _ (hc 1) (hc 2)).1 (hcr 1) (hcr 2))
  refine ((isCrys_isDR_sub_quot _ hφ _ _ h0 (cont_prod (hc 0) (cont_prod (hc 1) (hc 2)))
    ((LinearMap.proj 0).prod ((LinearMap.proj 1).prod (LinearMap.proj 2))) fun g x => ?_).1 fun x y h => ?_).1 h1
  · exact Prod.ext (hp 0 g x) (Prod.ext (hp 1 g x) (hp 2 g x))
  · funext a
    fin_cases a
    · exact congrArg Prod.fst h
    · exact congrArg (fun z => z.2.1) h
    · exact congrArg (fun z => z.2.2) h

private theorem open_GK (K : FinExt l) : IsOpen (GK K : Set (GQ l)) :=
  haveI := K.2
  IntermediateField.fixingSubgroup_isOpen K.1

private theorem fil_char (K : FinExt l) (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : GQ l →* Eˣ)
    (hκ : Continuous κ) (w : ℤ) (hw : ∀ g ∈ H, g ∈ Iq l → κ g = cycA l l E g ^ w) :
    IsDr (GK K).subtype (chRep (κ.comp (GK K).subtype)) ∧ ∀ i : ℤ,
      (i ≤ -w → FilD (GK K).subtype (chRep (κ.comp (GK K).subtype)) i =
        Ddr (GK K).subtype (chRep (κ.comp (GK K).subtype))) ∧
      (-w < i → FilD (GK K).subtype (chRep (κ.comp (GK K).subtype)) i = ⊥) :=
  charFil (GK K).subtype (open_GK K).isOpenEmbedding_subtypeVal _
    (Units.continuous_val.comp (hκ.comp continuous_subtype_val)) w
    ⟨H.comap (GK K).subtype, hH.preimage continuous_subtype_val, fun g hg hI => hw g hg hI⟩

private theorem cr_char {K L : FinExt l} (h : K.1 ≤ L.1) (κ τ : GQ l →* Eˣ) (hκ : Continuous κ) (hτ : Continuous τ)
    (w : ℤ) (hw : ∀ g ∈ Iq l, κ g = cycA l l E g ^ w * τ g) (hL : ∀ g ∈ GK L, τ g = 1) :
    ∃ x ∈ Dcr (GK L).subtype (chRep ((κ.comp (GK K).subtype).comp (incl h))),
      (∀ y ∈ Dcr (GK L).subtype (chRep ((κ.comp (GK K).subtype).comp (incl h))),
        ∃! c : E ⊗[ℚ_[l]] ↥(K0 L), y = smulC E L c x) ∧
      ∀ γ, actC (GK K).subtype (chRep (κ.comp (GK K).subtype)) γ x = (τ γ : E) • x := by
  obtain ⟨x, hx, hb⟩ := char_cr (κ / τ) (isCr_char _ (open_GK _) _ (hκ.div' hτ) w fun g _ hg => by
    rw [MonoidHom.div_apply, hw g hg, mul_div_cancel_right])
  have e : (κ.comp (GK K).subtype).comp (incl h) = (κ / τ).comp (GK L).subtype := by
    ext1 g
    change κ g = κ g / τ g
    rw [hL g g.2, div_one]
  rw [e]
  refine ⟨x, (mem_Dcr _ _ _).2 fun g => hx g, hb L, fun γ => ?_⟩
  conv_rhs => rw [← hx γ]
  generalize x = y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul v b =>
    change ((κ γ : E) • v) ⊗ₜ _ = ((τ γ : E) • (((κ γ / τ γ : Eˣ) : E) • v)) ⊗ₜ _
    rw [smul_smul, ← Units.val_mul, mul_div_cancel]
    rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb, smul_add]

end UpperTheory.V.Loc.R0

theorem UpperTheory.V.Loc.isType_and_isLocallyCrystalline_rz :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E], D.IsType (D.rz E) ∧ D.IsLCr (D.rz E) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  let j : Oˣ →* Eˣ := Units.map (algebraMap O E : O →* E)
  let κ : Fin 3 → GQ l →* Eˣ := fun a => (zpowGroupHom (wt1 a)).comp (j.comp D.Ψ)
  let τ : Fin 3 → GQ l →* Eˣ := fun a => (zpowGroupHom (wt1 a)).comp (j.comp D.τ)
  let w : Fin 3 → ℤ := fun a => D.e * wt1 a
  have hΨ : Continuous fun g => ((j (D.Ψ g) : Eˣ) : E) :=
    (ptCont (l := l) O E (Algebra.ofId O E)).1 _ _ D.Ψ_cont
  have hΨ' : Continuous (j.comp D.Ψ) := Units.continuous_iff.2 ⟨hΨ, (hΨ.comp continuous_inv).congr fun g => by
    simp only [Function.comp_apply, map_inv, MonoidHom.comp_apply]⟩
  have hτ' : Continuous (j.comp D.τ) := continuous_of_continuousAt_one _
    (continuousAt_const.congr (Filter.eventually_of_mem (D.τ_open.mem_nhds D.τ.ker.one_mem) fun g hg => by
      change 1 = j (D.τ g)
      rw [show D.τ g = 1 from hg, map_one]))
  have hκ : ∀ a, Continuous (κ a) := fun a => hΨ'.zpow _
  have hτ : ∀ a, Continuous (τ a) := fun a => hτ'.zpow _
  have hw : ∀ a, ∀ g ∈ Iq l, κ a g = cycA l l E g ^ w a * τ a g := by
    intro a g hg
    have h1 : j (cycA l l O g) = cycA l l E g := Units.ext (IsScalarTower.algebraMap_apply ℤ_[l] O E _).symm
    change j (D.Ψ g) ^ wt1 a = _ * j (D.τ g) ^ wt1 a
    rw [D.Ψ_I g hg, map_mul, map_pow, h1, mul_zpow, ← zpow_natCast, ← zpow_mul]
  have hτ1 : ∀ a, ∀ g ∈ D.HL, τ a g = 1 := fun a g hg => by
    change j (D.τ g) ^ wt1 a = 1
    rw [show D.τ g = 1 from hg.2, map_one, one_zpow]
  have hw' : ∀ a, ∀ g ∈ D.HL, g ∈ Iq l → κ a g = cycA l l E g ^ w a := fun a g hg hI => by
    rw [hw a g hI, hτ1 a g hg, mul_one]
  have hker : D.η.ker = GK D.Kv := Subgroup.ext D.η_ker
  have hH : IsOpen (D.HL : Set (GQ l)) := by
    have := (R0.open_GK D.Kv).inter D.τ_open
    rwa [← hker] at this
  let σ : GQ l →* GL (Fin 3) E := (tor E).comp (j.comp D.Ψ)
  have hσ : ∀ g, σ g = (D.rz E g).left := fun g => Units.ext (by
    change Matrix.diagonal _ = (Matrix.diagonal _).map (algebraMap O E)
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    exact congrArg Units.val (map_zpow j _ _).symm)
  refine ⟨⟨σ.comp (GK D.Kv).subtype, fun g => hσ g, ?_, ?_⟩, σ.comp D.HL.subtype, fun g => hσ g,
    R0.isCr_diag _ hH κ hκ w hw' _ fun _ => rfl⟩
  · have he := D.e_pos
    refine R0.hodge_diag (κ := fun a => (κ a).comp (GK D.Kv).subtype) (fun _ => rfl) (fun a => -w a) ?_ _ ?_ ?_
      (fun a => (R0.fil_char D.Kv _ hH _ (hκ a) _ (hw' a)).2) fun a => ?_
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp [w, wt1] at hab ⊢ <;> omega
    · intro a
      fin_cases a <;> simp [w, wt1, hodge0]
    · intro i hi
      have h0 := hi 0
      have h1 := hi 1
      have h2 := hi 2
      simp [w, wt1] at h0 h1 h2
      rw [hodge0, if_neg (by omega)]
    · obtain ⟨x, hx, hb⟩ := R0.char_dr (κ a) (R0.fil_char _ _ hH _ (hκ a) _ (hw' a)).1
      exact ⟨x, (R0.mem_Ddr _ _ _).2 fun g => hx g, hb D.Kv⟩
  · obtain ⟨L, -, -, -, -, hL, -, -⟩ := openField D.HL.subtype hH.isOpenEmbedding_subtypeVal
    rw [Subgroup.range_subtype] at hL
    have hle : GK L ≤ GK D.Kv := by
      rw [← hL, ← hker]
      exact inf_le_left
    have h : D.Kv.1 ≤ L.1 := by
      have : IsGalois ℚ_[l] (Om l) := inferInstance
      rw [← InfiniteGalois.fixedField_fixingSubgroup D.Kv.1, ← InfiniteGalois.fixedField_fixingSubgroup L.1]
      exact IntermediateField.fixedField_le hle
    choose x hx hb ht using fun a => R0.cr_char h (κ a) (τ a) (hκ a) (hτ a) (w a) (hw a) (hL ▸ hτ1 a)
    have hN : (GK L).Normal := by
      rw [← hL, Dat3.HL]
      infer_instance
    have hC := (isCrIff L _).1.1 (R0.isCr_diag (GK L) (R0.open_GK L) κ hκ w (hL ▸ hw') (σ.comp (GK L).subtype)
      fun _ => rfl)
    have key := R0.crys_diag (ρ := σ.comp (GK D.Kv).subtype) (κ := fun a => (κ a).comp (GK D.Kv).subtype)
      (fun _ => rfl) h inferInstance hC (fun a γ => (τ a γ : E)) x hx hb ht
    refine ⟨L, h, ?_⟩
    convert key using 2 with γ
    simp [Fin.sum_univ_three, τ, j, wt1]
