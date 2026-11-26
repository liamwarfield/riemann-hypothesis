module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def DerivSub : Prop :=
  ∀ (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V), IsSmooth π → HasFiniteLength π →
    Nontrivial (TwJacquet (GlobalTheory.BZMir.iterPhi k ψ j (GlobalTheory.BZMir.resM k π)).ρ (GlobalTheory.BZMir.MirUin k (n + 1)) 1) →
    ∃ (S : IrrRep (GL (Fin (n + 1)) k)) (f : S.ρ.IntertwiningMap (GlobalTheory.BZMir.deriv k ψ j π)), Function.Injective f

end GlobalTheory.BZSeg

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquet
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquet
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZNuPairAsm

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_degree (x : IrrGL (k := k)) : (dualCl x).1 = x.1 := by
  unfold dualCl
  split <;> rfl

theorem dual_shift (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (s q : IrrGL (k := k)) (j : ℕ) (h : q = (dualCl s).nu (j : ℂ)) :
    dualCl (q.nu (-(((j : ℂ) + 1) / 2))) = (s.nu (-(((j : ℂ) + 1) / 2))).nu 1 := by
  subst h
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA,
    IrrGL.nu_nu, IrrGL.nu_nu]
  congr 1
  ring

theorem nontrivial_of_irreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hi : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply hi.bot_ne_top
  ext v
  simp [Subsingleton.elim v 0]

theorem continuous_inv (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have e : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := by
    funext a
    exact AddChar.inv_apply ψ a
  rw [e]
  exact hc.comp continuous_neg

theorem jm_swap (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hJT : JmTheta k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ω : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth ω) (hi : ω.IsIrreducible)
    (a b c : IrrGL (k := k)) (hc : dualCl a = c) (hd : ∑ i, (![a, b] i).1 = N) (h : 1 ≤ jm ![a, b] hd (contra ω)) :
    ∃ hd' : ∑ i, (![dualCl b, c] i).1 = N, 1 ≤ jm ![dualCl b, c] hd' ω := by
  have hfl : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  have hd2 : ∑ i, (![dualCl b, dualCl a] i).1 = N := by
    simpa [Fin.sum_univ_two, dualCl_degree, add_comm] using hd
  have key := hJT N V ω hs hfl a b hd hd2
  have e := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra (GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) N ω hs hi
  rw [GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv ![a, b] hd _ _ e] at key
  subst hc
  exact ⟨hd2, key ▸ h⟩

end Lemmas

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k → GlobalTheory.BZSeg.JmTheta k → GlobalTheory.BZSeg.DerivSub k →
    GlobalTheory.BZSeg.NuPair k := by
  intro k _ _ _ _ hA hDJ hJT hDS N V _ _ ω hs hi hng
  obtain ⟨ψ, hc, h1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  have hn : Nontrivial V := nontrivial_of_irreducible ω hi
  have hg : ¬ IsGenericFor ψ ω := fun h => hng ((isGeneric_iff_isGenericFor hc h1 ω).2 h)
  obtain ⟨m, hm0, hmN, hnt, hlow⟩ := GlobalTheory.CompanionTheory.BZCuspPair.exists_highest ψ hc h1 N ω hs hn hg
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, N = n + 1 + j + 1 := ⟨N - n - 2, by omega⟩
  have hfl : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  have hD := GlobalTheory.CompanionTheory.BZCuspPair.deriv_nontrivial ψ n j ω hnt
  obtain ⟨S, f, hf⟩ := hDS ψ n j V ω hs hfl hD
  have hsq : IsSubquotient S.ρ (GlobalTheory.BZMir.deriv k ψ j ω) := IsSubquotient.of_injective f hf
  obtain ⟨β, hdβ, hβ, hjm⟩ := hDJ ψ hc h1 n j V ω hs hfl S hsq
  have hv := GlobalTheory.CompanionTheory.BZCuspPair.phi_vanish ψ hc h1 n j ω hs hlow
  have hs' : IsSmooth (contra ω) := isSmooth_contra _
  have hi' : (contra ω).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA ω hs hi
  have hfl' : HasFiniteLength (contra ω) := hasFiniteLength_of_isIrreducible hi'
  let B : V →ₗ[ℂ] smoothPart ω.dual →ₗ[ℂ] ℂ := ((smoothPart ω.dual).subtype).flip
  have hB : ∀ g v v', B (ω g v) (contra ω g v') = B v v' := by
    intro g v v'
    change (ω.dual g (v' : Module.Dual ℂ V)) (ω g v) = (v' : Module.Dual ℂ V) v
    rw [Representation.dual_apply]
    show (v' : Module.Dual ℂ V) (ω g⁻¹ (ω g v)) = (v' : Module.Dual ℂ V) v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hBn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
    intro v hv0
    obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs
      (fun U a => GlobalTheory.ThetaLiftGL.compactOpen_basis k (n + 1 + j + 1) U a) hv0
    exact ⟨l, hl⟩
  obtain ⟨B', hB', hB'n⟩ := GlobalTheory.CompanionTheory.BZCuspPair.pair_deriv ψ hc h1 n j ω (contra ω) hs hs' B hB hBn hv
  have hint : ∀ g w, f (S.ρ g w) = GlobalTheory.BZMir.deriv k ψ j ω g (f w) := fun g w =>
    Representation.IntertwiningMap.isIntertwining _ _ f g w
  have hSn : Nontrivial S.V := nontrivial_of_irreducible S.ρ S.irr
  obtain ⟨Q, hQ, hQeq⟩ := GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu k (n + 1) j _ S
    (GlobalTheory.BZMir.deriv k ψ⁻¹ j (contra ω)) (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ⁻¹ j hs')
    (B'.comp f.toLinearMap)
    (by
      intro g w w'
      change B' (f (S.ρ g w)) _ = _ * B' (f w) w'
      rw [hint]
      exact hB' g (f w) w')
    (by
      intro h0
      obtain ⟨w, hw⟩ := exists_ne (0 : S.V)
      have hfw : f w ≠ 0 := fun e => hw (hf (e.trans (map_zero f).symm))
      obtain ⟨w', hw'⟩ := hB'n (f w) hfw
      apply hw'
      have := LinearMap.congr_fun (LinearMap.congr_fun h0 w) w'
      exact this)
  obtain ⟨β₂, hd₂, hβ₂, hjm₂⟩ := hDJ ψ⁻¹ (continuous_inv ψ hc) (inv_ne_one.mpr h1) n j _ (contra ω) hs' hfl' Q hQ
  obtain ⟨hd₃, hjm₃⟩ := jm_swap hA hJT ω hs hi _ β₂ _ rfl hd₂ hjm₂
  have hshift := dual_shift hA (IrrGL.of S.ρ S.smooth S.irr) (IrrGL.of Q.ρ Q.smooth Q.irr) j hQeq
  have hd' : ∑ a, (![dualCl β₂, ((IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2))).nu 1] a).1 =
      n + 1 + j + 1 := by
    rw [← hshift]
    exact hd₃
  refine ⟨(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), β, dualCl β₂, hdβ, hd', ?_, ?_, ?_, hjm, ?_⟩
  · rw [IrrGL.nu_fst]
    exact Nat.succ_pos n
  · rw [hβ]
    exact Nat.succ_pos j
  · rw [dualCl_degree, hβ₂, hβ]
  · rw [← GlobalTheory.CompanionTheory.SegFine.jm_congr (by rw [hshift]) hd₃ hd' ω]
    exact hjm₃

end GlobalTheory.CompanionTheory.BZNuPairAsm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquetStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nu_pair_of_derivatives_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k → GlobalTheory.BZSeg.JmTheta k → GlobalTheory.BZSeg.DerivSub k → GlobalTheory.BZSeg.NuPair k := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair | exact GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair | (intros; apply GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.DerivSub
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZDerivJac

namespace GlobalTheory.RgGu.Nup2

theorem exists_injective_of_tensor {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (i : α)
    (hi : (ρ i).IsIrreducible) {D : Type} [AddCommGroup D] [Module ℂ D] (R : Representation ℂ (Γ i) D)
    (φ : PiTensorProduct ℂ X →ₗ[ℂ] D) (hφ : ∀ g x, φ (piTensor ρ (Pi.mulSingle i g) x) = R g (φ x)) (hne : φ ≠ 0) :
    ∃ f : (ρ i).IntertwiningMap R, Function.Injective f := by
  have hx : ∃ x : ∀ a, X a, φ (PiTensorProduct.tprod ℂ x) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (PiTensorProduct.ext (MultilinearMap.ext fun x => by simpa using h x))
  obtain ⟨x, hx⟩ := hx
  let ℓ : X i →ₗ[ℂ] D := φ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x i
  have hℓ : ∀ w, ℓ w = φ (PiTensorProduct.tprod ℂ (Function.update x i w)) := fun w => rfl
  let f : (ρ i).IntertwiningMap R := ⟨ℓ, fun g => LinearMap.ext fun w => by
    show ℓ (ρ i g w) = R g (ℓ w)
    rw [hℓ, hℓ, ← hφ, piTensor_tprod]
    congr 2
    funext a
    by_cases h : a = i
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]⟩
  refine ⟨f, ?_⟩
  haveI := hi
  rcases Representation.IsIrreducible.injective_or_eq_zero f with h | h
  · exact h
  · exfalso
    apply hx
    have e := congrArg (fun F : (ρ i).IntertwiningMap R => F (x i)) h
    have e2 : f (x i) = φ (PiTensorProduct.tprod ℂ x) := by
      show ℓ (x i) = _
      rw [hℓ, Function.update_eq_self]
    rw [← e2]
    exact e

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 1000000 in
theorem exists_irr_sub_of_quot (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n t : ℕ} {X D : Type} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup D] [Module ℂ D] (T : Representation ℂ (Levi k fun a => Fin (dd n t a)) X)
    (hs : IsSmooth T) (hT : HasFiniteLength T) (R : Representation ℂ (GL (Fin n) k) D) (L : X →ₗ[ℂ] D)
    (hL : ∀ g x, L ((T.comp (iota n t) : Representation ℂ (GL (Fin n) k) X) g x) = R g (L x)) (hne : L ≠ 0) :
    ∃ (S : IrrRep (GL (Fin n) k)) (f : S.ρ.IntertwiningMap R), Function.Injective f := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded T).1 hT
  let P : Set (Subrepresentation T) := {B | ∃ x ∈ B, L x ≠ 0}
  have hP : P.Nonempty := by
    by_contra h
    apply hne
    ext x
    by_contra hx
    exact h ⟨⊤, x, trivial, hx⟩
  obtain ⟨B, ⟨x0, hx0B, hx0⟩, hBmin⟩ := wellFounded_lt.has_min P hP
  have hbot : ⊥ < B := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    subst h
    have : x0 = 0 := (Submodule.mem_bot ℂ).1 hx0B
    exact hx0 (by rw [this, map_zero])
  obtain ⟨C, hCB, hCmax⟩ := wellFounded_gt.has_min {C : Subrepresentation T | C < B} ⟨⊥, hbot⟩
  have hcov : C ⋖ B := ⟨hCB, fun E hCE hEB => hCmax E hEB hCE⟩
  have hCker : ∀ x ∈ C, L x = 0 := by
    intro x hx
    by_contra h
    exact hBmin C ⟨x, hx, h⟩ hCB
  let K := C.toSubmodule.comap B.toSubmodule.subtype
  let φ : (B.toSubmodule ⧸ K) →ₗ[ℂ] D := K.liftQ (L ∘ₗ B.toSubmodule.subtype) (fun y hy => hCker y.1 hy)
  have hφ : ∀ y : B.toSubmodule, φ (Submodule.Quotient.mk y) = L y.1 := fun y => rfl
  have hZi : (subQuot B C).IsIrreducible := isIrreducible_subQuot hcov
  have hZsq : IsSubquotient (subQuot B C) T :=
    ⟨B, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩
  have hZs : IsSmooth (subQuot B C) := hZsq.isSmooth hs
  obtain ⟨σ, ⟨E⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (dd n t) (⟨_, subQuot B C, hZs, hZi⟩ : IrrRep _)
  let φ' := φ ∘ₗ E.symm.toIntertwiningMap.toLinearMap
  have hq : ∀ (g : GL (Fin (dd n t 0)) k) z, φ (subQuot B C (Pi.mulSingle 0 g) z) = R g (φ z) := by
    intro g z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact hL g y.1
  have hφ'rel : ∀ (g : GL (Fin (dd n t 0)) k) x,
      φ' ((piTensor fun a => (σ a).rep.ρ) (Pi.mulSingle 0 g) x) = R g (φ' x) := by
    intro g x
    have hE := LinearMap.congr_fun (E.symm.toIntertwiningMap.isIntertwining' (Pi.mulSingle 0 g)) x
    exact (congrArg φ hE).trans (hq g _)
  have hφ'ne : φ' ≠ 0 := by
    intro h0
    apply hx0
    have e := LinearMap.congr_fun h0 (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩))
    have e2 : E.symm.toIntertwiningMap (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩)) =
        Submodule.Quotient.mk ⟨x0, hx0B⟩ := E.toLinearEquiv.symm_apply_apply _
    have e3 : φ' (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩)) = L x0 := by
      show φ (E.symm.toIntertwiningMap _) = _
      rw [e2]
      rfl
    rw [← e3]
    exact e
  obtain ⟨f, hf⟩ := exists_injective_of_tensor (fun a => (σ a).rep.ρ) (0 : Fin 2) (σ 0).rep.irr
    (R := R) φ' hφ'rel hφ'ne
  refine ⟨(σ 0).rep, f, hf⟩


set_option maxHeartbeats 1000000 in
theorem jac_deriv_rel (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) :
    ∃ L : Jacquet π (unipRad k (stdBlocks (dd n (j + 1)) (dd_sum n j))) →ₗ[ℂ]
        TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1,
      Function.Surjective L ∧ ∀ g x,
        L (((SmGL.jac (stdBlocks (dd n (j + 1)) (dd_sum n j)) π).comp (iota n (j + 1)) :
          Representation ℂ (GL (Fin n) k) _) g x) =
        SmGL.twist (GlobalTheory.BZMir.deriv k ψ j π) (detChar (Fin n) (absPow k (-(((j : ℂ) + 1) / 2)))) g (L x) := by
  obtain ⟨L, hL, hLe⟩ := exists_jac_deriv ψ n j π
  refine ⟨L, hL, fun g x => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [twist_apply]
  have h1 := congrArg (fun c : ℂˣ => (c : ℂ) • GlobalTheory.BZMir.deriv k ψ j π g (L (Submodule.Quotient.mk v)))
    (delta_mulSingle n j g)
  refine Eq.trans ?_ h1
  have h2 := hLe g v
  have h3 : (SmGL.jac (stdBlocks (dd n (j + 1)) (dd_sum n j)) π).comp (iota n (j + 1)) g (Submodule.Quotient.mk v) =
      (((deltaHalf k (fun a => Fin (dd n (j + 1) a))
        (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g))⁻¹ : ℂˣ) : ℂ) •
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks (dd n (j + 1)) (dd_sum n j))
        (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g)) v) :=
    jac_mk _ π _ v
  rw [h3, map_smul, h2]


set_option maxHeartbeats 1000000 in
theorem derivSub (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) : GlobalTheory.BZSeg.DerivSub k := by
  intro ψ n j V _ _ π hs hf hnt
  have hχ : IsSmoothChar (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2)))) :=
    (isSmoothChar_absPow _).detChar
  have hχi : IsSmoothChar (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2))))⁻¹ := by
    unfold IsSmoothChar at hχ ⊢
    convert hχ using 2
    ext g
    simp [MonoidHom.mem_ker]
  obtain ⟨L, hL, hLe⟩ := jac_deriv_rel ψ (n + 1) j π
  have hne : L ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := exists_ne (0 : TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1)
    obtain ⟨x, rfl⟩ := hL y
    exact hy (by rw [h0, LinearMap.zero_apply])
  obtain ⟨S0, f, hf'⟩ := exists_irr_sub_of_quot hA _ (isSmooth_jac _ hs)
    (GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ _ V π hs hf) _ L hLe hne
  refine ⟨⟨S0.V, SmGL.twist S0.ρ (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2))))⁻¹,
    isSmooth_twist S0.smooth hχi, isIrreducible_twist S0.irr _⟩, ⟨f.toLinearMap, fun g => ?_⟩, hf'⟩
  ext w
  have e := LinearMap.congr_fun (f.isIntertwining' g) w
  simp only [LinearMap.coe_comp, Function.comp_apply, twist_apply] at e ⊢
  rw [map_smul, e, smul_smul]
  simp

theorem derivSub_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivSub k :=
  fun _ _ _ _ _ hA => derivSub hA

end GlobalTheory.RgGu.Nup2

end
end

namespace GlobalTheory.RgGu.Nup2

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.NuPair k := fun k _ _ _ _ =>
  GlobalTheory.T.nu_pair_of_derivatives_jacquet k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    (GlobalTheory.T.derivative_jacquet_holds k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)
    (GlobalTheory.T.jm_theta_holds k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)
    (derivSub_main k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)

end GlobalTheory.RgGu.Nup2
