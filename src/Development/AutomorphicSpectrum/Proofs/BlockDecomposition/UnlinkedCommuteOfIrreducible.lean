module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLe

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Matrix
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZSegComm

open Zc.Cos (invT)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Inv

variable {n : Type} [Fintype n] [DecidableEq n]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invT_invT (g : GL n k) : invT (invT g) = g := Units.ext (transpose_transpose _)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_invT (g : GL n k) :
    GeneralLinearGroup.det (invT g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  refine Units.ext ?_
  show ((g⁻¹).valᵀ).det = ((g⁻¹ : GL n k).val).det
  rw [det_transpose]

theorem continuous_invT : Continuous (invT : GL n k → GL n k) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

end Inv

section Levi

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {W : Type} [AddCommGroup W] [Module ℂ W]


variable (k m) in
def leviInvT : Levi k m →* Levi k m where
  toFun g a := invT (g a)
  map_one' := funext fun _ => map_one _
  map_mul' _ _ := funext fun _ => map_mul _ _ _


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α] in
theorem leviInvT_leviInvT (g : Levi k m) : leviInvT k m (leviInvT k m g) = g :=
  funext fun _ => invT_invT _

theorem deltaHalf_leviInvT (g : Levi k m) : deltaHalf k m (leviInvT k m g) = (deltaHalf k m g)⁻¹ := by
  rw [deltaHalf_apply, deltaHalf_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  show absPow k _ (GeneralLinearGroup.det (invT (g a))) = _
  rw [det_invT, map_inv]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem invT_mem_parab {e : (Σ a, m a) ≃ n} {p : GL n k} (hp : p ∈ parabLower k e) :
    invT p ∈ parab k e :=
  mem_parab_iff.2 fun a b i j hab => (mem_parabLower_iff k).1 (inv_mem hp) b a j i hab


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem invT_mem_parabLower {e : (Σ a, m a) ≃ n} {q : GL n k} (hq : q ∈ parab k e) :
    invT q ∈ parabLower k e :=
  (mem_parabLower_iff k).2 fun a b i j hab => mem_parab_iff.1 (inv_mem hq) b a j i hab

theorem leviProj_invT (e : (Σ a, m a) ≃ n) (p : parabLower k e) :
    leviProj k e ⟨invT p.1, invT_mem_parab p.2⟩ = leviInvT k m (leviProjLower k e p) := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : ((leviProjLower k e p) a)⁻¹ = leviProjLower k e p⁻¹ a := by rw [map_inv]; rfl
  show ((p.1⁻¹ : GL n k).val) (e ⟨a, j⟩) (e ⟨a, i⟩) = ((((leviProjLower k e p) a)⁻¹ : GL (m a) k).val) j i
  rw [h]
  rfl

theorem leviProjLower_invT (e : (Σ a, m a) ≃ n) (q : parab k e) :
    leviProjLower k e ⟨invT q.1, invT_mem_parabLower q.2⟩ = leviInvT k m (leviProj k e q) := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : ((leviProj k e q) a)⁻¹ = leviProj k e q⁻¹ a := by rw [map_inv]; rfl
  show ((q.1⁻¹ : GL n k).val) (e ⟨a, j⟩) (e ⟨a, i⟩) = ((((leviProj k e q) a)⁻¹ : GL (m a) k).val) j i
  rw [h]
  rfl

theorem parIndLower_equiv_comp_invT (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Nonempty ((parIndLower e (ρ.comp (leviInvT k m))).Equiv
      ((parInd e ρ).comp (invT : GL n k →* GL n k))) := by
  refine GlobalTheory.SmGL.Relabel.smInd_equiv_comp (invT : GL n k →* GL n k) invT continuous_invT continuous_invT
    invT_invT invT_invT (fun q => ⟨⟨invT q.1, invT_mem_parabLower q.2⟩, rfl, ?_⟩)
    (fun p => ⟨⟨invT p.1, invT_mem_parab p.2⟩, rfl, ?_⟩)
  · refine LinearMap.ext fun v => ?_
    show (((deltaHalf k m (leviProjLower k e ⟨invT q.1, invT_mem_parabLower q.2⟩))⁻¹ : ℂˣ) : ℂ) •
        ρ (leviInvT k m (leviProjLower k e ⟨invT q.1, invT_mem_parabLower q.2⟩)) v =
      (deltaHalf k m (leviProj k e q) : ℂ) • ρ (leviProj k e q) v
    rw [leviProjLower_invT, deltaHalf_leviInvT, inv_inv, leviInvT_leviInvT]
  · refine LinearMap.ext fun v => ?_
    show (deltaHalf k m (leviProj k e ⟨invT p.1, invT_mem_parab p.2⟩) : ℂ) •
        ρ (leviProj k e ⟨invT p.1, invT_mem_parab p.2⟩) v =
      (((deltaHalf k m (leviProjLower k e p))⁻¹ : ℂˣ) : ℂ) • ρ (leviInvT k m (leviProjLower k e p)) v
    rw [leviProj_invT, deltaHalf_leviInvT]

end Levi

section Two

variable {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {W : Type} [AddCommGroup W] [Module ℂ W]


variable (k a b) in
def invTProd : GL a k × GL b k →* GL a k × GL b k := MonoidHom.prodMap invT invT

theorem ind₂Lower_equiv_comp_invT (e : a ⊕ b ≃ n) (ρ : Representation ℂ (GL a k × GL b k) W) :
    Nonempty ((ind₂Lower e (ρ.comp (invTProd k a b))).Equiv
      ((ind₂ e ρ).comp (invT : GL n k →* GL n k))) := by
  have h : (ρ.comp (invTProd k a b)).comp (leviTwo k a b).symm.toMonoidHom =
      (ρ.comp (leviTwo k a b).symm.toMonoidHom).comp (leviInvT k (Two a b)) :=
    MonoidHom.ext fun g => rfl
  unfold ind₂Lower ind₂
  rw [h]
  exact parIndLower_equiv_comp_invT (two e) _

theorem ind₂_swap_equiv_comp_invT (e₁ : a ⊕ b ≃ n) (e₂ : b ⊕ a ≃ n)
    (ρ : Representation ℂ (GL a k × GL b k) W) :
    Nonempty ((ind₂ e₂ ((ρ.comp (invTProd k a b)).comp
        (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom)).Equiv
      ((ind₂ e₁ ρ).comp (invT : GL n k →* GL n k))) := by
  obtain ⟨A⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k Bool n (Two b a) (two e₂)
    (two ((Equiv.sumComm b a).trans e₁)) W).1
    (((ρ.comp (invTProd k a b)).comp
      (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom).comp
        (leviTwo k b a).symm.toMonoidHom)
  obtain ⟨B⟩ := (GlobalTheory.SmGL.SwapBlocks.lower_equiv_upper_swap k a b n e₁ W).1 (ρ.comp (invTProd k a b))
  obtain ⟨C⟩ := ind₂Lower_equiv_comp_invT e₁ ρ
  exact ⟨(A.trans B.symm).trans C⟩

def ind₂Equiv {V : Type} [AddCommGroup V] [Module ℂ V] (e : a ⊕ b ≃ n)
    {ρ : Representation ℂ (GL a k × GL b k) W} {σ : Representation ℂ (GL a k × GL b k) V} (φ : ρ.Equiv σ) :
    (ind₂ e ρ).Equiv (ind₂ e σ) :=
  parIndEquiv _ (compEquiv φ _)

end Two

section Pair

theorem nonempty_comp_invT_equiv_contra {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    Nonempty (Representation.Equiv (π.comp (invT : GL (Fin N) k →* GL (Fin N) k)) (contra π)) :=
  GlobalTheory.GelfandKazhdan.equiv_contra k N V π ha hi

theorem nonempty_extTensor_swap {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty (Representation.Equiv
      (((extTensor π₁ π₂).comp (invTProd k (Fin r) (Fin t))).comp
        (MulEquiv.prodComm : GL (Fin t) k × GL (Fin r) k ≃* GL (Fin r) k × GL (Fin t) k).toMonoidHom)
      (extTensor (π₂.comp (invT : GL (Fin t) k →* GL (Fin t) k))
        (π₁.comp (invT : GL (Fin r) k →* GL (Fin r) k)))) :=
  ⟨.mk (TensorProduct.comm ℂ V W) fun g => by
    ext v w
    rfl⟩

def extTensorCongr {r t : ℕ} {V W V' W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {π₁ : Representation ℂ (GL (Fin r) k) V} {π₂ : Representation ℂ (GL (Fin t) k) W}
    {σ₁ : Representation ℂ (GL (Fin r) k) V'} {σ₂ : Representation ℂ (GL (Fin t) k) W'}
    (φ₁ : π₁.Equiv σ₁) (φ₂ : π₂.Equiv σ₂) : (extTensor π₁ π₂).Equiv (extTensor σ₁ σ₂) :=
  .mk (TensorProduct.congr φ₁.toLinearEquiv φ₂.toLinearEquiv) fun g => by
    ext v w
    exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b) (φ₁.toIntertwiningMap.isIntertwining _ _ g.1 v)
      (φ₂.toIntertwiningMap.isIntertwining _ _ g.2 w)

theorem nonempty_ind₂_equiv_multiProd {N : ℕ} {d : Fin 2 → ℕ} (hd : ∑ a, d a = N) (h : d 0 + d 1 = N)
    {X : Fin 2 → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) :
    Nonempty ((ind₂ (stdSum h) (extTensor (π 0) (π 1))).Equiv (multiProd (stdBlocks d hd) π)) := by
  subst h
  exact nonempty_prod₂_equiv_multiProd hd π

theorem nonempty_ind₂_contra_equiv (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (F : Fin 2 → IrrGL (k := k)) {N : ℕ}
    (hd : ∑ a, (F a).1 = N) (h : (F 0).1 + (F 1).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra (F 0).rep) (contra (F 1).rep))).Equiv
      (contra (prodIrr F hd))) := by
  have E₂ := nonempty_ind₂_equiv_multiProd (d := fun a => (F a).1) hd h
    (X := fun a => smoothPart (F a).rep.dual) fun a => contra (F a).rep
  have E₃ := GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr_multiProd hA F hd
  exact E₂.elim fun e₂ => E₃.elim fun e₃ => ⟨e₂.trans e₃⟩

theorem prodIrr_swap_of_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (F G : Fin 2 → IrrGL (k := k))
    (e₀ : G 0 = F 1) (e₁ : G 1 = F 0) {N : ℕ} (hd : ∑ a, (F a).1 = N) (hd' : ∑ a, (G a).1 = N)
    (hX : (prodIrr F hd).IsIrreducible) (hY : (prodIrr G hd').IsIrreducible) :
    Nonempty ((prodIrr F hd).Equiv (prodIrr G hd')) := by
  have h : (F 0).1 + (F 1).1 = N := (Fin.sum_univ_two _).symm.trans hd
  have h' : (G 0).1 + (G 1).1 = N := (Fin.sum_univ_two _).symm.trans hd'
  have h'' : (F 1).1 + (F 0).1 = N := by rw [← e₀, ← e₁]; exact h'
  have E₁ := nonempty_ind₂_equiv_multiProd (d := fun a => (F a).1) hd h fun a => (F a).rep
  have E₂ := nonempty_ind₂_contra_equiv hA G hd' h'
  have E₃ : ∀ (u v : IrrGL (k := k)), u = F 1 → v = F 0 → ∀ h₁ : u.1 + v.1 = N,
      Nonempty ((ind₂ (stdSum h'') (extTensor (contra (F 1).rep) (contra (F 0).rep))).Equiv
        (ind₂ (stdSum h₁) (extTensor (contra u.rep) (contra v.rep)))) := by
    rintro _ _ rfl rfl _
    exact ⟨.refl _⟩
  have E₄ := E₃ _ _ e₀ e₁ h'
  have Gx := nonempty_comp_invT_equiv_contra (F 0).rep (hA k _ _ _ (F 0).2.rep.smooth (F 0).2.rep.irr)
    (F 0).2.rep.irr
  have Gy := nonempty_comp_invT_equiv_contra (F 1).rep (hA k _ _ _ (F 1).2.rep.smooth (F 1).2.rep.irr)
    (F 1).2.rep.irr
  have T := nonempty_extTensor_swap (F 0).rep (F 1).rep
  have K := ind₂_swap_equiv_comp_invT (k := k) (stdSum h) (stdSum h'') (extTensor (F 0).rep (F 1).rep)
  have aX := hA k N _ _ (isSmooth_prodIrr _ hd) hX
  have aY := hA k N _ _ (isSmooth_prodIrr _ hd') hY
  have GX := nonempty_comp_invT_equiv_contra (prodIrr F hd) aX hX
  refine (GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin N) k) (GlobalTheory.LocalThetaGL.compact_open_basis _)
    _ _ _ _ aX aY).2.2 ?_
  exact E₁.elim fun ε₁ => E₂.elim fun ε₂ => E₄.elim fun ε₄ => Gx.elim fun gx => Gy.elim fun gy => T.elim fun t =>
    K.elim fun κ => GX.elim fun gX =>
      ⟨(((compEquiv ε₁ _).trans gX).symm.trans (κ.symm.trans
        ((ind₂Equiv _ (t.trans (extTensorCongr gy gx))).trans ε₄))).trans ε₂⟩

end Pair

theorem lUnlinkedComm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.LUnlinkedIrr k → GlobalTheory.BZSeg.LUnlinkedComm k := by
  intro k _ _ _ _ hA hI Δ Δ' x y N hd hd' hl hx hy
  have hl' : ¬ Δ'.Linked Δ := fun h => hl h.symm
  have hXi : (prodIrr ![x, y] hd).IsIrreducible := by
    refine hI 2 N ![Δ, Δ'] ![x, y] hd ?_ ?_
    · exact Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨Segment.not_linked_self _, hl⟩,
        Fin.forall_fin_two.2 ⟨hl', Segment.not_linked_self _⟩⟩
    · exact Fin.forall_fin_two.2 ⟨hx, hy⟩
  have hYi : (prodIrr ![y, x] hd').IsIrreducible := by
    refine hI 2 N ![Δ', Δ] ![y, x] hd' ?_ ?_
    · exact Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨Segment.not_linked_self _, hl'⟩,
        Fin.forall_fin_two.2 ⟨hl, Segment.not_linked_self _⟩⟩
    · exact Fin.forall_fin_two.2 ⟨hy, hx⟩
  exact prodIrr_swap_of_isIrreducible hA ![x, y] ![y, x] rfl rfl hd hd' hXi hYi

end GlobalTheory.CompanionTheory.BZSegComm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unlinked_commute_of_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.LUnlinkedIrr k → GlobalTheory.BZSeg.LUnlinkedComm k := by
  first | exact @GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm | exact GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm | (intros; apply GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.JacExp

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem exists_atom_le {ρ : Representation ℂ G V} (h : HasFiniteLength ρ) {E : Subrepresentation ρ}
    (hE : E ≠ ⊥) : ∃ S : Subrepresentation ρ, IsAtom S ∧ S ≤ E := by
  obtain ⟨-, hw⟩ := (hasFiniteLength_iff_wellFounded ρ).1 h
  haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt hw
  obtain h' | ⟨S, hS, hle⟩ := eq_bot_or_exists_atom_le E
  · exact absurd h' hE
  · exact ⟨S, hS, hle⟩

def eigenSub (ρ : Representation ℂ G V) (z : G) (hz : ∀ g, z * g = g * z) (ν : ℂ) : Subrepresentation ρ :=
  ⟨Module.End.eigenspace (ρ z) ν, fun g v hv => by
    have hv' : ρ z v = ν • v := Module.End.mem_eigenspace_iff.1 hv
    refine Module.End.mem_eigenspace_iff.2 ?_
    have : ρ z (ρ g v) = ρ g (ρ z v) := by
      rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply]
    rw [this, hv', map_smul]⟩

theorem mem_eigenSub {ρ : Representation ℂ G V} {z : G} {hz : ∀ g, z * g = g * z} {ν : ℂ} {v : V} :
    v ∈ (eigenSub ρ z hz ν).toSubmodule ↔ ρ z v = ν • v :=
  Module.End.mem_eigenspace_iff

theorem isSmooth_sub [TopologicalSpace G] {ρ : Representation ℂ G V} (h : IsSmooth ρ)
    (S : Subrepresentation ρ) : IsSmooth S.toRepresentation := fun v => by
  have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g v.1 = v.1} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact h v.1

end General

section Tensor

variable {Γ X Y : Fin 2 → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]

theorem piTensor_apply_of_scalar (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : ℂ)
    (h0 : ∀ v, ρ 0 (g 0) v = c • v) (h1 : ∀ v, ρ 1 (g 1) v = v) (z : PiTensorProduct ℂ X) :
    piTensor ρ g z = c • z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    have : (fun a => ρ a (g a) (f a)) = Function.update f 0 (c • f 0) := by
      funext a
      fin_cases a
      · simp [h0]
      · simp [h1]
    rw [this, MultilinearMap.map_update_smul, Function.update_eq_self]
    rfl
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

def piTensorCongr {ρ : ∀ a, Representation ℂ (Γ a) (X a)} {σ : ∀ a, Representation ℂ (Γ a) (Y a)}
    (φ : ∀ a, (ρ a).Equiv (σ a)) : (piTensor ρ).Equiv (piTensor σ) :=
  .mk (PiTensorProduct.congr fun a => (φ a).toLinearEquiv) fun g => by
    apply PiTensorProduct.ext
    ext f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      piTensor_tprod, PiTensorProduct.congr_tprod]
    exact congrArg _ (funext fun a => (φ a).toIntertwiningMap.isIntertwining _ _ (g a) (f a))

end Tensor

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def omegaLevi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) : Levi k (fun a => Fin (d a)) :=
  fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) (if a = 0 then Zls.unifU k else 1)

theorem omegaLevi_comm (d : Fin 2 → ℕ) (h : Levi k (fun a => Fin (d a))) :
    omegaLevi k d * h = h * omegaLevi k d := by
  funext a
  apply Units.ext
  simp only [omegaLevi, Matrix.GeneralLinearGroup.scalar, Pi.mul_apply, Units.val_mul, Units.coe_map,
    MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact Matrix.scalar_commute _ (fun r => Commute.all _ _) _

theorem diagPow_val (N : ℕ) (lam : Fin N → ℤ) :
    (Zls.diagPow k N lam : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ lam i : kˣ) : k) := rfl

theorem leviEmb_omegaLevi {N : ℕ} (d : Fin 2 → ℕ) (hd : ∑ a, d a = N) :
    leviEmb k (stdBlocks d hd) (omegaLevi k d) = Zls.diagPow k N (Zls.omegaVec N (d 0)) := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [diagPow_val]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      have hv := stdBlocks_val d hd a i
      have : (((stdBlocks d hd ⟨a, i⟩ : Fin N) : ℕ) < d 0) ↔ a = 0 := by
        rw [hv]
        fin_cases a
        · simp
        · simp
      simp [omegaLevi, Zls.omegaVec, this, Matrix.GeneralLinearGroup.scalar]
    · have : (stdBlocks d hd ⟨a, i⟩) ≠ (stdBlocks d hd ⟨a, j⟩) := by simpa using hij
      simp [omegaLevi, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply_ne _ this, hij]
  · have : (stdBlocks d hd ⟨a, i⟩) ≠ (stdBlocks d hd ⟨b, j⟩) := fun h =>
      hab (congrArg Sigma.fst ((stdBlocks d hd).injective h))
    rw [leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ this]

theorem deltaHalf_omegaLevi (d : Fin 2 → ℕ) :
    (((deltaHalf k (fun a => Fin (d a)) (omegaLevi k d))⁻¹ : ℂˣ) : ℂ) =
      (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2) := by
  have h0 : modExp (fun a : Fin 2 => Fin (d a)) 0 = d 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have hd0 : Matrix.GeneralLinearGroup.det (omegaLevi k d 0) = Zls.unifU k ^ d 0 := by
    apply Units.ext
    simp [omegaLevi, Matrix.GeneralLinearGroup.scalar]
  have hd1 : Matrix.GeneralLinearGroup.det (omegaLevi k d 1) = 1 := by
    apply Units.ext
    simp [omegaLevi, Matrix.GeneralLinearGroup.scalar]
  have hn : nabs k (Zls.unifU k) = (resCard k : ℝ)⁻¹ :=
    nabs_uniformiser Zls.irreducible_unif rfl
  rw [deltaHalf_apply, Fin.prod_univ_two, hd0, hd1, map_one, mul_one, map_pow, h0]
  have hq : ((((resCard k : ℝ)⁻¹ : ℝ)) : ℂ) = ((Nat.card 𝓀[k] : ℂ))⁻¹ := by simp [resCard]
  have harg : Complex.arg (Nat.card 𝓀[k] : ℂ) ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_pos.ne
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, val_absPow, hn, hq, Complex.inv_cpow _ _ harg,
    inv_pow, inv_inv, ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

theorem exists_scalarBy (x : IrrGL (k := k)) (t : kˣ) : ∃ c : ℂ, Zl.ScalarBy x t c := by
  obtain ⟨ω, -, hω⟩ := ((schur_and_segments k).1 (Fin x.1) _ x.rep x.2.rep.smooth x.2.rep.irr).2
  exact ⟨ω t, fun v => hω t v⟩

theorem jm_ne_zero_of_equiv {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (S : Subrepresentation (GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hx) π))
    (Φ : S.toRepresentation.Equiv (piTensor fun a => (x a).rep)) : Zc.jm x hx π ≠ 0 :=
  jhMult_ne_zero_iff.2 ⟨S, Φ.toIntertwiningMap, Φ.surjective⟩

theorem exists_constituent (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (d : Fin 2 → ℕ)
    (hd : ∑ a, d a = N) (μ : ℂ) (w : V)
    (hw : (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0)
    (hμ : (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) :
        Jacquet π (unipRad k (stdBlocks d hd))) =
      μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd)))) :
    ∃ (x : Fin 2 → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧
      Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧
      ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hfl : HasFiniteLength (GlobalTheory.SmGL.jac (stdBlocks d hd) π) :=
    (hBZ k).2.1 (Fin 2) (Fin N) (fun a => Fin (d a)) (stdBlocks d hd) V π hs
      (hasFiniteLength_of_isIrreducible hi)
  set ν : ℂ := μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2) with hν
  set w' : Jacquet π (unipRad k (stdBlocks d hd)) := Submodule.Quotient.mk w with hw'
  have heig : GlobalTheory.SmGL.jac (stdBlocks d hd) π (omegaLevi k d) w' = ν • w' := by
    rw [hw', jac_mk, leviEmb_omegaLevi, hμ, deltaHalf_omegaLevi, smul_smul, hν, mul_comm]
  set E := eigenSub (GlobalTheory.SmGL.jac (stdBlocks d hd) π) (omegaLevi k d) (omegaLevi_comm d) ν with hE
  have hEne : E ≠ ⊥ := by
    intro h
    have : w' ∈ E.toSubmodule := mem_eigenSub.2 heig
    rw [h] at this
    exact hw ((Submodule.mem_bot ℂ).1 this)
  obtain ⟨S, hS, hSE⟩ := exists_atom_le hfl hEne
  have hSirr : S.toRepresentation.IsIrreducible := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨S.toSubmodule, S.toRepresentation, isSmooth_sub (isSmooth_jac _ hs) S, hSirr⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hBZ k (Fin 2) (fun a => Fin (d a)) τ
  let x : Fin 2 → IrrGL (k := k) := fun a => IrrGL.of (N := d a) (s a).ρ (s a).smooth (s a).irr
  let Ψ : S.toRepresentation.Equiv (piTensor fun a => (x a).rep) :=
    Φ.trans (piTensorCongr fun a => IrrGL.equivOf (N := d a) (s a).ρ (s a).smooth (s a).irr)
  obtain ⟨c₀, hc₀⟩ := exists_scalarBy (x 0) (Zls.unifU k)
  obtain ⟨c₁, hc₁⟩ := exists_scalarBy (x 1) (Zls.unifU k)
  refine ⟨x, hd, fun a => rfl, jm_ne_zero_of_equiv x hd π S Ψ, ?_, c₁, hc₁⟩
  have hSne : S.toSubmodule ≠ ⊥ := fun h => hS.1 (Subrepresentation.ext h)
  obtain ⟨v₀, hv₀, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
  let v : S.toSubmodule := ⟨v₀, hv₀⟩
  have hv : v ≠ 0 := fun h => hv₀ne (congrArg Subtype.val h)
  have h1 : S.toRepresentation (omegaLevi k d) v = ν • v := Subtype.ext (mem_eigenSub.1 (hSE hv₀))
  have h2 : piTensor (fun a => (x a).rep) (omegaLevi k d) (Ψ v) = c₀ • Ψ v := by
    refine piTensor_apply_of_scalar _ _ c₀ (fun u => ?_) (fun u => ?_) _
    · have : omegaLevi k d 0 = Matrix.GeneralLinearGroup.scalar (Fin (x 0).1) (Zls.unifU k) := by
        simp [omegaLevi]
        rfl
      rw [this]
      exact hc₀ u
    · have : omegaLevi k d 1 = 1 := by simp [omegaLevi]
      rw [this]
      exact LinearMap.congr_fun (map_one (x 1).rep) u
  have h3 : Ψ (S.toRepresentation (omegaLevi k d) v) =
      piTensor (fun a => (x a).rep) (omegaLevi k d) (Ψ v) :=
    Ψ.toIntertwiningMap.isIntertwining _ _ _ v
  have h4 : Ψ v ≠ 0 := fun h => hv (Ψ.toLinearEquiv.injective (by simpa using h))
  have h5 : ν • Ψ v = c₀ • Ψ v := by
    rw [← h2, ← h3, h1, map_smul]
  have h6 : c₀ = ν := (smul_left_injective ℂ h4 h5).symm
  rw [← h6]
  exact hc₀

theorem exists_constituent_of_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ (μ : ℂ) (w : V), (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 → (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) : Jacquet π (unipRad k (stdBlocks d hd))) = μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) → ∃ (x : Fin 2 → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧ Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧ ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 :=
  fun _ _ _ _ _ N _ _ _ π hs hi _ _ d hd _ _ μ w hw hμ => exists_constituent N π hs hi d hd μ w hw hμ

end Local

end GlobalTheory.CompanionTheory.JacExp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvectorStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_quotient_eigenvector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ (μ : ℂ) (w : V), (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 → (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) : Jacquet π (unipRad k (stdBlocks d hd))) = μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) → ∃ (x : Fin 2 → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧ Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧ ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 := by
  first | exact @GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen | exact GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen | (intros; apply GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.ProdReorder
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdjQuot

section Linear

theorem nontrivial_piTensorProduct {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, Nontrivial (X a)] : Nontrivial (PiTensorProduct ℂ X) := by
  classical
  choose v hv using fun a => exists_ne (0 : X a)
  have hex : ∀ a, ∃ φ : Module.Dual ℂ (X a), φ (v a) ≠ 0 := fun a => by
    by_contra hc
    push_neg at hc
    exact hv a ((Module.forall_dual_apply_eq_zero_iff ℂ (v a)).1 hc)
  choose φ hφ using hex
  let L := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)
  have h : L (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    simp only [L, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hφ a
  exact ⟨PiTensorProduct.tprod ℂ v, 0, fun h0 => h (by rw [h0, map_zero])⟩

end Linear

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Induction

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {W W' : Type} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ)
    [Nontrivial W] : Nontrivial (IndSp e ρ) := by
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

end Induction

theorem nontrivial_prodIrr {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) :
    Nontrivial (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) := by
  haveI : ∀ a, Nontrivial (x a).2.rep.V := fun a => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (x a).2.rep.irr
  haveI := nontrivial_piTensorProduct (X := fun a => (x a).2.rep.V)
  exact nontrivial_indSp _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)

section Two

variable {V U W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
  {r t N : ℕ}

end Two

section Concat



end Concat

end GlobalTheory.CompanionTheory.AdjQuot
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueComplexPointUnder
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Under

open GlobalTheory.TuplePoint GlobalTheory.Points

theorem spZ_ext (f g : Sp ℂ ⟶ Sp ℤ) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact Subsingleton.elim _ _

theorem top_ext {s s' : Γ(Sp ℂ, ⊤)} (h : valR (𝟙 (Sp ℂ)) ⊤ s = valR (𝟙 (Sp ℂ)) ⊤ s') : s = s' :=
  ext_of_dense (𝟙 (Sp ℂ)) fun _ => h

theorem hom_eq_of_val {N : ℕ} {φ ψ : Sp ℂ ⟶ PSpace ℤ N} (i : Fin (N + 1))
    (h₁ : ⊤ ≤ φ ⁻¹ᵁ chart ℤ N i) (h₂ : ⊤ ≤ ψ ⁻¹ᵁ chart ℤ N i)
    (h : ∀ j, valR φ (chart ℤ N i) (ratio ℤ N i j) = valR ψ (chart ℤ N i) (ratio ℤ N i j)) : φ = ψ := by
  refine GlobalTheory.ProjSpace.hom_ext (spZ_ext _ _) fun y => ⟨⊤, trivial, i, h₁, h₂, fun j => top_ext ?_⟩
  have e₁ := valR_appLE (𝟙 (Sp ℂ)) φ h₁ le_rfl (ratio ℤ N i j)
  have e₂ := valR_appLE (𝟙 (Sp ℂ)) ψ h₂ le_rfl (ratio ℤ N i j)
  rw [Category.id_comp] at e₁ e₂
  exact e₁.trans ((h j).trans e₂.symm)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev blockVec (z : (Σ k, Bk n k) → ℂ) (k : Fin (m + 1)) : Fin (n k + 1) → ℂ := fun i => z ⟨k, i⟩

theorem blockVec_ne_zero {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : Fin (m + 1)) :
    blockVec z k ≠ 0 := fun h => by
  obtain ⟨i, hi⟩ := hz k
  exact hi (congrFun h i)

theorem isUnder_of_comp {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, blockVec z k ≠ 0) (y : CxPts (mpStr ℤ m n) σ₀)
    (h : ∀ k, y.1 ≫ prB n k = point ℤ (blockVec z k) (hz k)) : IsUnder y z := fun k i => by
  refine ⟨⟨fun hy => ne_zero_of_le (h k) hy le_rfl, fun hi => le_preimage_chart (h k) hi⟩, fun j hy => ?_⟩
  exact valR_pullRatio (h k) hy le_rfl j

theorem comp_of_isUnder {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, blockVec z k ≠ 0) (hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {y : CxPts (mpStr ℤ m n) σ₀} (H : IsUnder y z) (k : Fin (m + 1)) :
    y.1 ≫ prB n k = point ℤ (blockVec z k) (hz k) := by
  obtain ⟨i, hi⟩ := hz' k
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((H k i).1).2 hi
  refine hom_eq_of_val i (le_preimage_comp y.1 _ le_rfl hy)
    ((le_point_preimage_iff (o := ℤ) (ht := hz k) i).2 hi) fun j => ?_
  refine (valR_appLE y.1 (prB n k) le_rfl hy (ratio ℤ (n k) i j)).symm.trans ?_
  exact ((H k i).2 j hy).trans (valR_point_ratio (t := blockVec z k) (ht := hz k) hi j).symm

theorem existsUnique_isUnder (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ∃! y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z := by
  have ht := blockVec_ne_zero hz
  let a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k) := fun k => point ℤ (blockVec z k) (ht k)
  have ha : ∀ k, a k ≫ toSpecBase ℤ (n k) = spMap σ₀ := fun _ => spZ_ext _ _
  let y : CxPts (mpStr ℤ m n) σ₀ := ⟨lift m n (spMap σ₀) a ha, lift_mpStr m n _ a ha⟩
  have hy : ∀ k, y.1 ≫ prB n k = a k := lift_pr m n _ a ha
  refine ⟨y, isUnder_of_comp ht y hy, fun y' H => Subtype.ext ?_⟩
  exact GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k =>
    (comp_of_isUnder ht hz H k).trans (hy k).symm

end GlobalTheory.CompanionTheory.MPDict.Under
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFacts
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinLevelTw

open PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def atHom (a b : ℕ) (w : Pl E) : Gf E a b →* GLw a w × GLw b w :=
  (GeneralLinearGroup.map (pLoc E w)).prodMap (GeneralLinearGroup.map (pLoc E w))

omit [IsCMField E] in
theorem atHom_apply (w : Pl E) (y : Gf E a b) : atHom a b w y = atW w y := rfl

theorem continuous_atHom (w : Pl E) : Continuous (atHom (E := E) a b w) :=
  ((GlobalTheory.EulerTwU.continuous_pc w).comp continuous_fst).prodMk ((GlobalTheory.EulerTwU.continuous_pc w).comp continuous_snd)

theorem isOpen_Kf (n : ℕ) : IsOpen (Kf E n : Set (GL (Fin n) (Af E))) := by
  refine Subgroup.isOpen_mono (H₁ := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) ?_
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n)
  intro g hg
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E n).1 hg
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_comap.2 ?_
  refine GlobalTheory.EulerTwU.mem_GLint _ _ (fun i j => ?_) (fun i j => ?_)
  · exact GroundTheory.Global.mem_integralFiniteAdeles.1 (h1 i j) w
  · rw [← map_inv]
    exact GroundTheory.Global.mem_integralFiniteAdeles.1 (h2 i j) w

theorem continuous_thP : Continuous (thP E a b) := by
  have h : ∀ n, Continuous (thF E n) := fun n => GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)
  exact ((h a).comp continuous_fst).prodMk ((h b).comp continuous_snd)

theorem thP_thP (y : Gf E a b) : thP E a b (thP E a b y) = y :=
  Prod.ext (GlobalTheory.EulerTwU.thF_thF y.1) (GlobalTheory.EulerTwU.thF_thF y.2)

theorem isOpen_family (M : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (hM : ∀ w, IsOpen (M w : Set (GLw a w × GLw b w)))
    (hK : ∀ᶠ w in cofinite, K2 a b w ≤ M w) :
    IsOpen ((⨅ w, (M w).comap (atHom a b w) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hT : {w | ¬ K2 a b w ≤ M w}.Finite := hK
  have h1 : ∀ᶠ u in nhds (1 : Gf E a b), ∀ w ∈ {w | ¬ K2 a b w ≤ M w}, atHom a b w u ∈ M w :=
    (Filter.eventually_all_finite hT).2 fun w _ =>
      (continuous_atHom w).continuousAt.eventually_mem
        ((hM w).mem_nhds (by rw [map_one]; exact one_mem _))
  have h2 : ∀ᶠ u in nhds (1 : Gf E a b), u ∈ ((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) :=
    ((isOpen_Kf a).prod (isOpen_Kf b)).mem_nhds ⟨one_mem _, one_mem _⟩
  filter_upwards [h1, h2] with u hu1 hu2
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_comap.2 ?_
  by_cases hw : K2 a b w ≤ M w
  · refine hw ⟨?_, ?_⟩
    · exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu2.1 w)
    · exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu2.2 w)
  · exact hu1 w hw

theorem exists_level_of_test {φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h : IsTestP φ) :
    ∃ L : ∀ w : Pl E, Subgroup (GLw a w × GLw b w), (∀ w, IsOpen (L w : Set (GLw a w × GLw b w))) ∧
      (∀ᶠ w in cofinite, L w = K2 a b w) ∧ ∀ w, ∀ k ∈ L w, ∀ x, φ w (k * x) = φ w x ∧ φ w (x * k) = φ w x := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  refine ⟨fun w => (K₁ w).prod (K₂ w), fun w => ?_, ?_, fun w => (h₃.1 w).2⟩
  · rw [Subgroup.coe_prod]
    exact (h₁.1 w).1.prod (h₂.1 w).1
  · filter_upwards [h₁.2, h₂.2] with w e₁ e₂
    rw [e₁, e₂]

theorem finLevel : FinLevel := by
  intro E _ _ _ _ a b S φ₁ φ₂ h₁ h₂
  obtain ⟨L₁, o₁, e₁, i₁⟩ := exists_level_of_test h₁
  obtain ⟨L₂, o₂, e₂, i₂⟩ := exists_level_of_test h₂
  let A : Subgroup (Gf E a b) := ⨅ w, (L₁ w ⊓ L₂ w).comap (atHom a b w)
  have hA : IsOpen (A : Set (Gf E a b)) := by
    refine isOpen_family _ (fun w => ?_) ?_
    · rw [Subgroup.coe_inf]
      exact (o₁ w).inter (o₂ w)
    · filter_upwards [e₁, e₂] with w f₁ f₂
      rw [f₁, f₂, inf_idem]
  have mA : ∀ {u}, u ∈ A → ∀ w, atW w u ∈ L₁ w ⊓ L₂ w := fun hu w =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu w)
  refine ⟨A ⊓ A.comap (thP E a b), ?_, fun u hu y => ?_⟩
  · rw [Subgroup.coe_inf]
    exact hA.inter (hA.preimage continuous_thP)
  · have hu₁ := mA hu.1
    have hu₂ := mA (Subgroup.mem_comap.1 hu.2)
    have key : ∀ (w : Pl E) (f : GLw a w × GLw b w → ℂ) (k k' x : GLw a w × GLw b w),
        (∀ c ∈ ({k⁻¹, k'} : Set _), ∀ x, f (c * x) = f x ∧ f (x * c) = f x) → f (k⁻¹ * x * k') = f x := by
      intro w f k k' x h
      rw [(h k' (by simp) _).2, (h k⁻¹ (by simp) _).1]
    unfold finFn
    refine finprod_congr fun w => finprod_congr fun _ => ?_
    have m₁ : atW w (u⁻¹ * y * thP E a b u) = (atW w u)⁻¹ * atW w y * atW w (thP E a b u) := by
      simp only [← atHom_apply, map_mul, map_inv]
    have m₂ : atW w (thP E a b (u⁻¹ * y * thP E a b u)) =
        (atW w (thP E a b u))⁻¹ * atW w (thP E a b y) * atW w u := by
      simp only [← atHom_apply, map_mul, map_inv, thP_thP]
    rw [m₁, m₂, key w (φ₁ w), key w (φ₂ w)]
    · intro c hc x
      rcases hc with rfl | rfl
      · exact i₂ w _ (inv_mem (hu₂ w).2) x
      · exact i₂ w _ (hu₁ w).2 x
    · intro c hc x
      rcases hc with rfl | rfl
      · exact i₁ w _ (inv_mem (hu₁ w).1) x
      · exact i₁ w _ (hu₂ w).1 x

end GlobalTheory.CompanionTheory.FinLevelTw

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFactsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_level_facts : PositivityTheory.Rg.BcB.G8.FinLevel := by
  first | exact @GlobalTheory.CompanionTheory.FinLevelTw.finLevel | exact GlobalTheory.CompanionTheory.FinLevelTw.finLevel | (intros; apply GlobalTheory.CompanionTheory.FinLevelTw.finLevel <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquiv
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegIncDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_equiv_prodIrr_of_cast {h h' N : ℕ} (e : h = h') (x : Fin h → IrrGL (k := k)) (y : Fin h' → IrrGL (k := k))
    (hxy : ∀ a, x a = y (Fin.cast e a)) (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((prodIrr x hd).Equiv (prodIrr y hd')) := by
  subst e
  obtain rfl : x = y := funext fun a => by simpa using hxy a
  exact ⟨hd, ⟨Representation.Equiv.refl _⟩⟩

theorem nonempty_contra_trans {h h' N : ℕ} {x y : Fin h → IrrGL (k := k)} {z : Fin h' → IrrGL (k := k)} {hd : ∑ a, (x a).1 = N}
    {hy : ∑ a, (y a).1 = N} {hz : ∑ a, (z a).1 = N} (H₁ : Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hy)))
    (H₂ : Nonempty ((prodIrr y hy).Equiv (prodIrr z hz))) :
    Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr z hz)) :=
  H₁.elim fun φ => H₂.elim fun ψ => ⟨φ.trans ψ⟩

theorem dualCl_term (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (hl : Δ.len = (segDual Δ).len)
    (a : Fin Δ.len) : dualCl (Δ.term a) = dec (segDual Δ) (Fin.cast hl a) := by
  have hc : ∀ x : IrrGL (k := k), x.IsCusp → (dualCl x).IsCusp := fun x hx =>
    (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1
  have hv : ((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) = Δ.len - (a + 1) := by
    have h0 : ((Fin.cast hl a : Fin (segDual Δ).len) : ℕ) = a := rfl
    rw [Fin.val_rev, h0]; omega
  have ha : (a : ℕ) + 1 ≤ Δ.len := a.2
  change dualCl (Δ.first.nu ((a : ℕ) : ℂ)) =
    (segDual Δ).first.nu (((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) : ℂ)
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc, IrrGL.nu_nu, hv, Nat.cast_sub ha]
  congr 1
  push_cast
  ring

theorem contra_prodIrr_term : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (Δ.term a).1 = N), ∃ hd' : ∑ a, (dec (segDual Δ) a).1 = N,
      Nonempty ((contra (prodIrr Δ.term hd)).Equiv (prodIrr (dec (segDual Δ)) hd')) := by
  intro k _ _ _ _ hA Δ N hd
  have hl : Δ.len = (segDual Δ).len :=
    (GlobalTheory.CompanionTheory.SegDualPrec.len_segDual (fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1) Δ).symm
  have H := @GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr k _ _ _ _ hA Δ.len N Δ.term hd
  obtain ⟨hd₁, H₁⟩ := H
  have H' := exists_equiv_prodIrr_of_cast hl (fun a => dualCl (Δ.term a)) (dec (segDual Δ))
    (dualCl_term hA Δ hl) hd₁
  obtain ⟨hd₂, H₂⟩ := H'
  exact ⟨hd₂, nonempty_contra_trans H₁ H₂⟩

end GlobalTheory.CompanionTheory.SegIncDual

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquivStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_segment_product_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (Δ.term a).1 = N), ∃ hd' : ∑ a, (dec (segDual Δ) a).1 = N, Nonempty ((contra (prodIrr Δ.term hd)).Equiv (prodIrr (dec (segDual Δ)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.SegIncDual.contra_prodIrr_term | exact GlobalTheory.CompanionTheory.SegIncDual.contra_prodIrr_term | (intros; apply GlobalTheory.CompanionTheory.SegIncDual.contra_prodIrr_term <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalSegmentsReverseOrdered
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalSegmentsReverseOrdered
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.Canon

theorem isRevOrdered_of_isCanon {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k) : IsCanon Γ → IsRevOrdered Γ :=
  fun hc i j hij hp => (hc.1 i j hij).1 hp.2

end GlobalTheory.CompanionTheory.Canon
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalSegmentsReverseOrderedStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_segments_reverse_ordered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), IsCanon Γ → IsRevOrdered Γ := by
  first | exact @GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon | exact GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon | (intros; apply GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLeStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_transitive_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {g N : ℕ} (y : Fin g → IrrGL (k := k)) (hy : ∑ b, (y b).1 = N) (Wb : Fin g → List (IrrGL (k := k))) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → (∀ b, ∑ a, ((Wb b).get a).1 = (y b).1) → jm y hy π * ∏ b, jmL (Wb b) (y b).rep ≤ jmL (List.ofFn Wb).flatten π := by
  first | exact @GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le | exact GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le | (intros; apply GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le <;> assumption)
end
