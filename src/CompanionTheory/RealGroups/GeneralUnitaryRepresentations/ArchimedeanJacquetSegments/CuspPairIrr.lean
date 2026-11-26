module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.JacquetModuleThetaTwist
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.CuspPair
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHolds

@[expose] public section

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.NontrivialOfIsIrreducible
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace CompanionTheory.RgGu.NR

namespace NuP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : IrrRep G) : Nontrivial τ.V := by
  have hi := τ.irr
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : Nontrivial V := by
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem continuous_inv_addChar (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
  rw [this]
  exact hc.comp continuous_neg

theorem dualCl_fst (x : IrrGL (k := k)) : (dualCl x).1 = x.1 := by
  unfold dualCl
  split <;> rfl

end NuP

set_option maxHeartbeats 4000000 in
open NuP in
theorem nuPair_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : GlobalTheory.BZSeg.DerivJac k) (h2 : GlobalTheory.BZSeg.JmTheta k) (h3 : DerFin k) : GlobalTheory.BZSeg.NuPair k := by
  intro N V _ _ ω hs hi hng
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  obtain ⟨ψ, hc, hψ⟩ := exists_continuous_addChar_ne_one k
  have hg : ¬ IsGenericFor ψ ω := fun h => hng ⟨ψ, hc, hψ, h⟩
  have hnt : Nontrivial V := nontrivial_of_isIrreducible hi
  obtain ⟨n, hn0, hnN, hnt2, hlow⟩ := GlobalTheory.CompanionTheory.BZCuspPair.exists_highest ψ hc hψ N ω hs hnt hg
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, N = n + 1 + j + 1 := ⟨N - (n + 1) - 1, by omega⟩
  have hc' := continuous_inv_addChar ψ hc
  have hψ' : ψ⁻¹ ≠ 1 := inv_ne_one.2 hψ
  let B : V →ₗ[ℂ] smoothPart ω.dual →ₗ[ℂ] ℂ := LinearMap.flip (smoothPart ω.dual).subtype
  have hBa : ∀ a b, B a b = (b : Module.Dual ℂ V) a := fun _ _ => rfl
  have hB : ∀ g a b, B (ω g a) (contra ω g b) = B a b := by
    intro g a b
    simp only [hBa, contra_apply]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hnd : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := fun v hv =>
    GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k _) hv
  obtain ⟨B', hB', hn'⟩ := GlobalTheory.CompanionTheory.BZCuspPair.pair_deriv ψ hc hψ n j ω (contra ω) hs (isSmooth_contra _) B hB hnd
    (GlobalTheory.CompanionTheory.BZCuspPair.phi_vanish ψ hc hψ n j ω hs hlow)
  have hD := GlobalTheory.CompanionTheory.BZCuspPair.deriv_nontrivial ψ n j ω hnt2
  have hfl := h3 ψ hc hψ (n + 1) j V ω hs hi
  obtain ⟨S, f, hf⟩ := GlobalTheory.T.exists_injective_irreducible_subrepresentation k (n + 1) _ _ _ _ (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j hs) hD
    (IsSubquotient.refl _) hfl
  have := nontrivial_of_irr S
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : S.V)
  have hw1 : f w₀ ≠ 0 := fun h => hw₀ (hf (by rw [h, map_zero]))
  obtain ⟨w', hw'⟩ := hn' (f w₀) hw1
  obtain ⟨Q, hQ, hQcl⟩ := GlobalTheory.T.pairing_twisted_determinant_subquotient k (n + 1) j _ S (GlobalTheory.BZMir.deriv k ψ⁻¹ j (contra ω))
    (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ⁻¹ j (isSmooth_contra _)) (B'.comp f.toLinearMap)
    (fun g w v => by
      have := hB' g (f w) v
      simpa [f.isIntertwining] using this)
    (fun h0 => hw' (by simpa using LinearMap.congr_fun (LinearMap.congr_fun h0 w₀) w'))
  have hflω : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  obtain ⟨β, hd1, hβ, hj1⟩ := h1 ψ hc hψ n j V ω hs hflω S (IsSubquotient.of_injective f hf)
  have hic : (contra ω).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA ω hs hi
  obtain ⟨β'', hd2, hβ'', hj2⟩ := h1 ψ⁻¹ hc' hψ' n j _ (contra ω) (isSmooth_contra _)
    (hasFiniteLength_of_isIrreducible hic) Q hQ

  have hGK : Zc.Cos.GKLocal k := GlobalTheory.T.local_langlands_of_irreducible_admissible hA
  have hsθ : IsSmooth ((ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))).comp (Zc.Cos.thetaW k (n + 1 + j + 1))) := by
    rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW]
    exact hs
  have hiθ : Representation.IsIrreducible
      ((ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))).comp (Zc.Cos.thetaW k (n + 1 + j + 1))) := by
    rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW]
    exact hi
  have E := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK (ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))) hsθ hiθ
  rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW] at E
  have hj3 : 1 ≤ jm ![(IrrGL.of Q.ρ Q.smooth Q.irr).nu (-(((j : ℂ) + 1) / 2)), β''] hd2
      (ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))) := by
    rw [GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv _ hd2 _ _ E]
    exact hj2
  set α : IrrGL (k := k) := (IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)) with hα
  set Q' : IrrGL (k := k) := (IrrGL.of Q.ρ Q.smooth Q.irr).nu (-(((j : ℂ) + 1) / 2)) with hQ'
  have hsum2 : ∀ (x y : IrrGL (k := k)), ∑ a, (![x, y] a).1 = x.1 + y.1 := fun x y => by
    simp [Fin.sum_univ_two]
  have hd3 : ∑ i, (![dualCl β'', dualCl Q'] i).1 = n + 1 + j + 1 := by
    rw [hsum2, dualCl_fst, dualCl_fst]
    rw [hsum2] at hd2
    omega
  have hj4 := hj3
  rw [h2 _ V ω hs hflω Q' β'' hd2 hd3] at hj4

  have hcls : dualCl Q' = α.nu 1 := by
    rw [hQ', hQcl, hα, IrrGL.nu_nu, IrrGL.nu_nu, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA]
    congr 1
    ring
  have key : ∀ u : IrrGL (k := k), u = α.nu 1 → ∀ hdu : ∑ i, (![dualCl β'', u] i).1 = n + 1 + j + 1,
      1 ≤ jm ![dualCl β'', u] hdu ω → ∃ hd' : ∑ a, (![dualCl β'', α.nu 1] a).1 = n + 1 + j + 1,
        1 ≤ jm ![dualCl β'', α.nu 1] hd' ω := by
    rintro u rfl hdu h
    exact ⟨hdu, h⟩
  obtain ⟨hd', hj5⟩ := key _ hcls hd3 hj4
  have hβ''1 : β''.1 = j + 1 := hβ''
  refine ⟨α, β, dualCl β'', hd1, hd', ?_, ?_, ?_, hj1, hj5⟩
  · show 0 < (IrrGL.of S.ρ S.smooth S.irr).1
    show 0 < n + 1
    omega
  · omega
  · rw [dualCl_fst, hβ''1, hβ]

end CompanionTheory.RgGu.NR
end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.DerFin
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.BZMir
open scoped TensorProduct

namespace CompanionTheory.RgGu.NR.DerFin

section Gen

variable {G M V W X : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
  (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)

def dMap {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) :
    (twAct ρ N θ s hs).IntertwiningMap (twAct σ N θ s hs) :=
  ⟨twMap ρ σ N θ f.toLinearMap (fun g v => Representation.IntertwiningMap.isIntertwining _ _ f g v), fun m =>
    Submodule.linearMap_qext _ (LinearMap.ext fun v => by
      show Submodule.Quotient.mk (f (ρ (s m) v)) = Submodule.Quotient.mk (σ (s m) (f v))
      rw [Representation.IntertwiningMap.isIntertwining])⟩

theorem dMap_mk {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) (v : V) :
    dMap N θ s hs f (Submodule.Quotient.mk v) = Submodule.Quotient.mk (f v) := rfl

theorem dMap_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : Function.Surjective (dMap N θ s hs f) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H w =>
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem twKer_le_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (p : ρ.IntertwiningMap σ)
    (hp : Function.Surjective p) : twKer σ N θ ≤ (twKer ρ N θ).map p.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, y, rfl⟩
  obtain ⟨v, rfl⟩ := hp y
  refine ⟨ρ (n : G) v - (θ n : ℂ) • v, Submodule.subset_span ⟨n, v, rfl⟩, ?_⟩
  show p (ρ (n : G) v - (θ n : ℂ) • v) = σ (n : G) (p v) - (θ n : ℂ) • p v
  rw [map_sub, map_smul, Representation.IntertwiningMap.isIntertwining]

theorem d_exact {ρ₁ : Representation ℂ G V} {ρ₂ : Representation ℂ G W} {ρ₃ : Representation ℂ G X}
    (ι : ρ₁.IntertwiningMap ρ₂) (p : ρ₂.IntertwiningMap ρ₃) (hp : Function.Surjective p)
    (hex : ∀ v, p v = 0 → ∃ u, ι u = v) :
    ∀ x, dMap N θ s hs p x = 0 → ∃ y, dMap N θ s hs ι y = x := by
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [dMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨w, hw, hpw⟩ := twKer_le_map N θ p hp hx
    obtain ⟨u, hu⟩ := hex (v - w) (by rw [map_sub]; exact sub_eq_zero.2 hpw.symm)
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    rw [dMap_mk, hu, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hw, sub_zero]

omit [Group M] in
theorem subsingleton_tw {ρ : Representation ℂ G V} [Subsingleton V] : Subsingleton (TwJacquet ρ N θ) :=
  ⟨fun x y => by
    induction x using Submodule.Quotient.induction_on with
    | H a =>
      induction y using Submodule.Quotient.induction_on with
      | H b => rw [Subsingleton.elim a b]⟩

def topBot (ρ : Representation ℂ G V) : (subQuot (⊤ : Subrepresentation ρ) ⊥).IntertwiningMap ρ :=
  ⟨Submodule.liftQ _ (⊤ : Subrepresentation ρ).toSubmodule.subtype (fun x hx => by
      rw [LinearMap.mem_ker]
      exact (Submodule.mem_bot ℂ).1 hx), fun g => Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)⟩

theorem topBot_surjective (ρ : Representation ℂ G V) : Function.Surjective (topBot ρ) :=
  fun v => ⟨Submodule.Quotient.mk ⟨v, trivial⟩, rfl⟩

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Base

variable (ψ : AddChar k Circle) {n t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def phi (n t : ℕ) : Levi k (fun a : Fin 2 => Fin (![n, t] a)) →* GL (Fin n) k × GL (Fin t) k :=
  (Pi.evalMonoidHom (fun a : Fin 2 => GL (Fin (![n, t] a)) k) 0).prod
    (Pi.evalMonoidHom (fun a : Fin 2 => GL (Fin (![n, t] a)) k) 1)

def lift2 {n t : ℕ} (g : GL (Fin n) k) (h : GL (Fin t) k) : Levi k (fun a : Fin 2 => Fin (![n, t] a)) :=
  fun a => match a with
    | ⟨0, _⟩ => g
    | ⟨1, _⟩ => h
    | ⟨i + 2, hi⟩ => absurd hi (by omega)

theorem phi_lift2 {n t : ℕ} (g : GL (Fin n) k) (h : GL (Fin t) k) : phi n t (lift2 g h) = (g, h) := rfl

theorem phi_surjective (n t : ℕ) : Function.Surjective (phi (k := k) n t) := by
  rintro ⟨g, h⟩
  exact ⟨lift2 g h, phi_lift2 g h⟩

theorem phi_continuous (n t : ℕ) : Continuous (phi (k := k) n t) :=
  (continuous_apply 0).prodMk (continuous_apply 1)

theorem base (hc : Continuous ψ) (h1 : ψ ≠ 1) (Y : Representation ℂ (GL (Fin n) k × GL (Fin t) k) V)
    (hYs : IsSmooth Y) (hYi : Y.IsIrreducible) :
    HasFiniteLength (twAct Y (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _) (inl_stab ψ n t)) := by
  classical
  let τ : IrrRep (Levi k fun a : Fin 2 => Fin (![n, t] a)) :=
    ⟨V, Y.comp (phi n t), isSmooth_comp hYs _ (phi_continuous n t),
      GlobalTheory.FinGL.Transport.isIrreducible_comp Y _ (phi_surjective n t) hYi⟩
  obtain ⟨σ, ⟨E⟩⟩ := GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor GlobalTheory.CompanionTheory.BZCuspPair.irrAdm ![n, t] τ
  let A := (σ 0).rep.V
  let B := (σ 1).rep.V
  let α : Representation ℂ (GL (Fin n) k) A := (σ 0).rep.ρ
  let β : Representation ℂ (GL (Fin t) k) B := (σ 1).rep.ρ
  let Ψ : V ≃ₗ[ℂ] A ⊗[ℂ] B :=
    E.toLinearEquiv.trans (GlobalTheory.CompanionTheory.HighestDeriv.piFinTwoTensor fun a => (σ a).rep.V)

  have hP : ∀ f : ∀ a : Fin 2, (σ a).rep.V,
      GlobalTheory.CompanionTheory.HighestDeriv.piFinTwoTensor (fun a => (σ a).rep.V) (PiTensorProduct.tprod ℂ f) = f 0 ⊗ₜ f 1 := by
    intro f
    rw [← LinearEquiv.eq_symm_apply]
    show PiTensorProduct.tprod ℂ f = GlobalTheory.SmGL.MultiIrr.tensorCons _ ((LinearEquiv.lTensor _
      (PiTensorProduct.subsingletonEquiv (s := fun i : Fin 1 => (σ i.succ).rep.V) 0).symm) (f 0 ⊗ₜ f 1))
    have e1 : (PiTensorProduct.subsingletonEquiv (s := fun i : Fin 1 => (σ i.succ).rep.V) 0).symm (f 1) =
        PiTensorProduct.tprod ℂ (fun i : Fin 1 => f i.succ) := by
      rw [LinearEquiv.symm_apply_eq, PiTensorProduct.subsingletonEquiv_apply_tprod]
      rfl
    rw [LinearEquiv.lTensor_tmul, e1, GlobalTheory.SmGL.MultiIrr.tensorCons_tmul]
    congr 1
    exact (Fin.cons_self_tail f).symm

  have hΨ : ∀ (g : GL (Fin n) k) (h : GL (Fin t) k) (v : V),
      Ψ (Y (g, h) v) = TensorProduct.map (α g) (β h) (Ψ v) := by
    intro g h v
    obtain ⟨l, hl⟩ := phi_surjective (k := k) n t (g, h)
    have e1 : E (Y (g, h) v) = piTensor (fun a => (σ a).rep.ρ) l (E v) := by
      rw [← hl]
      exact Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap l v
    have hl0 : l 0 = g := congrArg Prod.fst hl
    have hl1 : l 1 = h := congrArg Prod.snd hl
    show GlobalTheory.CompanionTheory.HighestDeriv.piFinTwoTensor _ (E (Y (g, h) v)) = _
    rw [e1]
    show _ = TensorProduct.map (α g) (β h) (GlobalTheory.CompanionTheory.HighestDeriv.piFinTwoTensor _ (E v))
    induction E v using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      simp only [map_smul, piTensor_tprod, hP, TensorProduct.map_tmul, ← hl0, ← hl1]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  set K : Submodule ℂ B := twKer β (unipB k (Fin t)) (whitChar ψ t) with hK

  have hgen : ∀ (a : A) (b : B), b ∈ K → Ψ.symm (a ⊗ₜ b) ∈ twKer Y (rightUnip k n t) (rightWhit k ψ n t) := by
    intro a b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, y, rfl⟩ := hx
      have hu : ((1 : GL (Fin n) k), (u : GL (Fin t) k)) ∈ rightUnip k n t :=
        Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, u.2⟩
      refine Submodule.subset_span ⟨⟨_, hu⟩, Ψ.symm (a ⊗ₜ y), ?_⟩
      apply Ψ.injective
      rw [LinearEquiv.apply_symm_apply, map_sub, map_smul, hΨ, LinearEquiv.apply_symm_apply,
        TensorProduct.map_tmul, TensorProduct.tmul_sub, TensorProduct.tmul_smul, map_one, one_apply_eq_self]
      rfl
    | zero => rw [TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [TensorProduct.tmul_smul, map_smul]; exact Submodule.smul_mem _ c hx
  have hrange : ∀ z ∈ LinearMap.range (K.subtype.lTensor A),
      Ψ.symm z ∈ twKer Y (rightUnip k n t) (rightWhit k ψ n t) := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | tmul a b => rw [LinearMap.lTensor_tmul]; exact hgen a b b.2
    | add x y hx hy => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hx hy

  have hrk : Module.rank ℂ (B ⧸ K) ≤ 1 :=
    CompanionTheory.rg.gu.whit.whitRankIrr k ψ hc h1 t B β (σ 1).rep.smooth (σ 1).rep.irr
  by_cases htop : K = ⊤
  ·
    have hall : ∀ v : V, v ∈ twKer Y (rightUnip k n t) (rightWhit k ψ n t) := by
      intro v
      have hs : Function.Surjective (K.subtype.lTensor A) := by
        apply LinearMap.lTensor_surjective
        intro b
        exact ⟨⟨b, htop ▸ Submodule.mem_top⟩, rfl⟩
      obtain ⟨z, hz⟩ := hs (Ψ v)
      have := hrange (Ψ v) ⟨z, hz⟩
      rwa [LinearEquiv.symm_apply_apply] at this
    haveI : Subsingleton (TwJacquet Y (rightUnip k n t) (rightWhit k ψ n t)) :=
      ⟨fun x y => by
        induction x using Submodule.Quotient.induction_on with
        | H a =>
          induction y using Submodule.Quotient.induction_on with
          | H b =>
            rw [(Submodule.Quotient.mk_eq_zero _).2 (hall a), (Submodule.Quotient.mk_eq_zero _).2 (hall b)]⟩
    exact GlobalTheory.ProdLength.hasFiniteLength_of_subsingleton _
  ·
    have hnt : Nontrivial (B ⧸ K) := Submodule.Quotient.nontrivial_iff.2 htop
    have hfr : Module.finrank ℂ (B ⧸ K) = 1 := by
      have hfin : Module.rank ℂ (B ⧸ K) < Cardinal.aleph0 := lt_of_le_of_lt hrk Cardinal.one_lt_aleph0
      haveI : Module.Finite ℂ (B ⧸ K) := Module.rank_lt_aleph0_iff.1 hfin
      have h2 : (Module.finrank ℂ (B ⧸ K) : Cardinal) ≤ 1 := by rw [Module.finrank_eq_rank]; exact hrk
      have h3 : 0 < Module.finrank ℂ (B ⧸ K) := Module.finrank_pos
      have h4 : Module.finrank ℂ (B ⧸ K) ≤ 1 := by exact_mod_cast h2
      omega
    haveI : Module.Finite ℂ (B ⧸ K) := Module.finite_of_finrank_eq_succ hfr
    let q : (B ⧸ K) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by simp [hfr])
    let ℓ : B →ₗ[ℂ] ℂ := q.toLinearMap ∘ₗ K.mkQ
    have hℓs : Function.Surjective ℓ := q.surjective.comp (Submodule.mkQ_surjective K)
    have hex : Function.Exact K.subtype ℓ := by
      intro b
      constructor
      · intro hb
        have : K.mkQ b = 0 := q.injective (by rw [map_zero]; exact hb)
        exact ⟨⟨b, (Submodule.Quotient.mk_eq_zero K).1 this⟩, rfl⟩
      · rintro ⟨b', rfl⟩
        show q (Submodule.Quotient.mk (b' : B)) = 0
        rw [(Submodule.Quotient.mk_eq_zero K).2 b'.2, map_zero]
    have hexA := lTensor_exact A hex hℓs
    let e' : A ⊗[ℂ] B →ₗ[ℂ] A := (TensorProduct.rid ℂ A).toLinearMap ∘ₗ ℓ.lTensor A
    have he'_tmul : ∀ (a : A) (b : B), e' (a ⊗ₜ b) = ℓ b • a := fun a b => by
      show (TensorProduct.rid ℂ A) (a ⊗ₜ ℓ b) = ℓ b • a
      rw [TensorProduct.rid_tmul]
    have hℓK : ∀ b ∈ K, ℓ b = 0 := fun b hb => by
      show q (Submodule.Quotient.mk b) = 0
      rw [(Submodule.Quotient.mk_eq_zero K).2 hb, map_zero]

    have hker : twKer Y (rightUnip k n t) (rightWhit k ψ n t) ≤ LinearMap.ker (e' ∘ₗ Ψ.toLinearMap) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨⟨⟨a, u⟩, hu⟩, v, rfl⟩
      have ha : a = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 hu).1
      subst ha
      have hu2 : u ∈ unipB k (Fin t) := (Subgroup.mem_prod.1 hu).2
      show e' (Ψ (Y (1, u) v - _)) = 0
      rw [map_sub, map_smul, hΨ, map_sub, map_smul, sub_eq_zero]
      induction Ψ v using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        rw [TensorProduct.map_tmul, he'_tmul, he'_tmul, map_one, one_apply_eq_self, smul_smul]
        congr 1
        have hm : β u y - (whitChar ψ t ⟨u, hu2⟩ : ℂ) • y ∈ K := Submodule.subset_span ⟨⟨u, hu2⟩, y, rfl⟩
        have := hℓK _ hm
        rw [map_sub, map_smul, sub_eq_zero] at this
        rw [this, smul_eq_mul]
        rfl
      | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

    let F : TwJacquet Y (rightUnip k n t) (rightWhit k ψ n t) →ₗ[ℂ] A :=
      (twKer Y (rightUnip k n t) (rightWhit k ψ n t)).liftQ (e' ∘ₗ Ψ.toLinearMap) hker
    have hFmk : ∀ v, F (Submodule.Quotient.mk v) = e' (Ψ v) := fun v => rfl
    have hFinj : Function.Injective F := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      induction x using Submodule.Quotient.induction_on with
      | H v =>
        rw [LinearMap.mem_ker, hFmk] at hx
        have h0 : ℓ.lTensor A (Ψ v) = 0 := by
          have h' : (TensorProduct.rid ℂ A) (ℓ.lTensor A (Ψ v)) = 0 := hx
          exact (TensorProduct.rid ℂ A).map_eq_zero_iff.1 h'
        obtain ⟨z, hz⟩ := (hexA (Ψ v)).1 h0
        have := hrange (Ψ v) ⟨z, hz⟩
        rw [LinearEquiv.symm_apply_apply] at this
        exact (Submodule.Quotient.mk_eq_zero _).2 this
    let Fi : (twAct Y (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _) (inl_stab ψ n t)).IntertwiningMap α :=
      ⟨F, fun g => Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        show F (Submodule.Quotient.mk (Y (g, 1) v)) = α g (F (Submodule.Quotient.mk v))
        rw [hFmk, hFmk, hΨ]
        induction Ψ v using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => rw [TensorProduct.map_tmul, he'_tmul, he'_tmul, map_one, one_apply_eq_self, map_smul]
        | add x y hx hy => simp only [map_add (f := _), hx, hy])⟩
    exact GlobalTheory.ProdLength.hasFiniteLength_of_injective Fi hFinj
      (GlobalTheory.SmGL.hasFiniteLength_of_isIrreducible (σ 0).rep.irr)

theorem finLen (hc : Continuous ψ) (h1 : ψ ≠ 1) (Mr : Representation ℂ (GL (Fin n) k × GL (Fin t) k) V)
    (hMs : IsSmooth Mr) (hM : HasFiniteLength Mr) :
    HasFiniteLength (twAct Mr (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _) (inl_stab ψ n t)) := by
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded Mr).1 hM
  have key : ∀ S T : Subrepresentation Mr, T ≤ S →
      HasFiniteLength (twAct (subQuot S T) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _)
        (inl_stab ψ n t)) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (twAct (subQuot S T) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _)
        (inl_stab ψ n t))) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (twAct (subQuot S T) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _)
        (inl_stab ψ n t))) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt'
    · subst hEq
      haveI := GlobalTheory.ParIndExact.subsingleton_subQuot_self T
      haveI := subsingleton_tw (ρ := subQuot T T) (rightUnip k n t) (rightWhit k ψ n t)
      exact GlobalTheory.ProdLength.hasFiniteLength_of_subsingleton _
    by_cases hcov : T ⋖ S
    · exact base ψ hc h1 _ ((GlobalTheory.ParIndExact.isSubquotient_subQuot S T).isSmooth hMs)
        (GlobalTheory.SmGL.isIrreducible_subQuot hcov)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hcov ⟨hlt', fun U h1' h2' => hno ⟨U, h1', h2'⟩⟩
    obtain ⟨ι, p, -, hp, -, hex⟩ := GlobalTheory.ParIndExact.subQuot_exact (ρ := Mr) hTU.le hUS.le
    exact GlobalTheory.ProdLength.hasFiniteLength_of_exact (dMap _ _ _ _ ι) (dMap _ _ _ _ p)
      (d_exact _ _ _ _ ι p hp hex) (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  exact GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective (dMap _ _ _ _ (topBot Mr))
    (dMap_surjective _ _ _ _ _ (topBot_surjective Mr)) (key ⊤ ⊥ bot_le)

end Base

end CompanionTheory.RgGu.NR.DerFin

namespace CompanionTheory.RgGu.NR

open CompanionTheory.RgGu.NR.DerFin

theorem derFin_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h : DerEquiv k) : DerFin k := by
  intro ψ hc h1 n j V _ _ π hs hi
  obtain ⟨E⟩ := h ψ n j V π
  have hfl : HasFiniteLength π := GlobalTheory.SmGL.hasFiniteLength_of_isIrreducible hi
  have hJ : HasFiniteLength (jac (two (stdSum (show n + (j + 1) = n + j + 1 from rfl))) π) :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 _ _ _ _ V π hs hfl
  have hJU : HasFiniteLength (jacU₂ (stdSum (show n + (j + 1) = n + j + 1 from rfl)) π) :=
    (hasFiniteLength_comp_iff _ _ (leviTwo k (Fin n) (Fin (j + 1))).surjective).2
      ((GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff _ _).1 hJ)
  have hJs : IsSmooth (jacU₂ (stdSum (show n + (j + 1) = n + j + 1 from rfl)) π) :=
    isSmooth_comp (isSmooth_jacU _ hs) _ (continuous_leviTwo k)
  exact HasFiniteLength.of_equiv (finLen ψ hc h1 _ hJs hJU) E.symm

end CompanionTheory.RgGu.NR
end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ComapTwKer
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace CompanionTheory.RgGu.NR.DerEq

section Abstract

variable {G M V : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V]

theorem comap_twKer (ρ : Representation ℂ G V) (N₁ : Subgroup G) (θ₁ : N₁ →* ℂˣ)
    (σ : Representation ℂ M (TwJacquet ρ N₁ θ₁)) (s : M →* G)
    (hσ : ∀ m v, σ m (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ (s m) v))
    (N₂ : Subgroup M) (θ₂ : N₂ →* ℂˣ) (N : Subgroup G) (θ : N →* ℂˣ)
    (h1 : ∀ u : N₁, ∃ h : (u : G) ∈ N, θ ⟨u, h⟩ = θ₁ u)
    (h2 : ∀ a : N₂, ∃ h : s a ∈ N, θ ⟨s a, h⟩ = θ₂ a)
    (h3 : ∀ u : N, ∃ u₁ : N₁, ∃ a : N₂, (u : G) = u₁ * s a) :
    (twKer σ N₂ θ₂).comap (twKer ρ N₁ θ₁).mkQ = twKer ρ N θ := by
  have hle : twKer ρ N₁ θ₁ ≤ twKer ρ N θ := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    obtain ⟨h, hθ⟩ := h1 u
    exact Submodule.subset_span ⟨⟨u, h⟩, v, by rw [hθ]⟩
  have key : twKer σ N₂ θ₂ = (twKer ρ N θ).map (twKer ρ N₁ θ₁).mkQ := by
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro w ⟨a, x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H v =>
        obtain ⟨h, hθ⟩ := h2 a
        refine ⟨ρ (s a) v - ((θ ⟨s a, h⟩ : ℂˣ) : ℂ) • v, Submodule.subset_span ⟨⟨_, h⟩, v, rfl⟩, ?_⟩
        rw [hθ, Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hσ]
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨u₁, a, hu⟩ := h3 u
      obtain ⟨hu₁, e1⟩ := h1 u₁
      obtain ⟨ha, e2⟩ := h2 a
      have hθ : θ u = θ₁ u₁ * θ₂ a := by
        have : u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩ := Subtype.ext hu
        rw [this, map_mul, e1, e2]
      have hdec : ρ (u : G) v - ((θ u : ℂˣ) : ℂ) • v =
          (ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v) +
            ((θ₁ u₁ : ℂˣ) : ℂ) • (ρ (s a) v - ((θ₂ a : ℂˣ) : ℂ) • v) := by
        rw [hθ, hu, map_mul, Module.End.mul_apply, Units.val_mul, smul_sub, mul_smul]
        abel
      have hz : ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v ∈ twKer ρ N₁ θ₁ :=
        Submodule.subset_span ⟨u₁, _, rfl⟩
      show (twKer ρ N₁ θ₁).mkQ _ ∈ twKer σ N₂ θ₂
      rw [hdec, map_add (f := _), Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hz, zero_add, map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Submodule.Quotient.mk v, ?_⟩)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hσ]
  rw [key, Submodule.comap_map_mkQ, sup_eq_right.2 hle]

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def Q (ψ : AddChar k Circle) {n : ℕ} : (j : ℕ) → (τ : MRep k (n + j)) →
    τ.V →ₗ[ℂ] TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1
  | 0, τ => (twKer τ.ρ (MirUin k n) 1).mkQ
  | j + 1, τ => (Q ψ j (MRep.phiM k ψ τ)) ∘ₗ (twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j))).mkQ

theorem Q_surj (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) (τ : MRep k (n + j)), Function.Surjective (Q k ψ j τ)
  | 0, τ => Submodule.mkQ_surjective _
  | j + 1, τ => (Q_surj ψ j (MRep.phiM k ψ τ)).comp (Submodule.mkQ_surjective _)

theorem ker_Q (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) (τ : MRep k (n + j)),
    LinearMap.ker (Q k ψ j τ) = twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)
  | 0, τ => by
    show LinearMap.ker (twKer τ.ρ (MirUin k n) 1).mkQ = _
    rw [Submodule.ker_mkQ]
    exact GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero k ψ n τ.V τ.ρ
  | j + 1, τ => by
    have hnm : n ≤ n + j := Nat.le_add_right n j
    have H := comap_twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j)) (phiMinus k ψ τ.ρ)
      ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype) (fun _ _ => rfl) (derUnipM k (n + j) n)
      (derCharM k ψ (n + j) n) (derUnipM k (n + j + 1) n) (derCharM k ψ (n + j + 1) n)
      (GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm) (GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm)
      (GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm)
    ext v
    have e1 := Submodule.ext_iff.1 H v
    rw [Submodule.mem_comap] at e1
    refine Iff.trans ?_ e1
    have e2 := Submodule.ext_iff.1 (ker_Q ψ j (MRep.phiM k ψ τ))
      ((twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j))).mkQ v)
    exact e2


variable (k) in
def E {n : ℕ} : (j : ℕ) → GL (Fin n) k →* Mir k (n + j)
  | 0 => levi k n
  | j + 1 => (levi k (n + j + 1)).comp ((Mir k (n + j)).subtype.comp (E j))

theorem Q_equiv (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) (τ : MRep k (n + j)) (g : GL (Fin n) k) (v : τ.V),
    Q k ψ j τ (τ.ρ (E k j g) v) = derivM k ψ j τ g (Q k ψ j τ v)
  | 0, τ, g, v => rfl
  | j + 1, τ, g, v => Q_equiv ψ j (MRep.phiM k ψ τ) g (Submodule.Quotient.mk v)

theorem E_val_zero {n : ℕ} (g : GL (Fin n) k) (i l : Fin (n + 1)) :
    (((E k 0 g : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i l =
      if h : (i : ℕ) < n ∧ (l : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, h.1⟩ ⟨l, h.2⟩
      else (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i l := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) i l = _
  induction i using Fin.lastCases with
  | last =>
    induction l using Fin.lastCases with
    | last => simp [glEmbMat]
    | cast l => simp [glEmbMat, Matrix.one_apply, (Fin.castSucc_ne_last l).symm]
  | cast i =>
    induction l using Fin.lastCases with
    | last => simp [glEmbMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast l => simp [glEmbMat]

theorem E_val_succ {n j : ℕ} (g : GL (Fin n) k)
    (ih : ∀ i l : Fin (n + j + 1), (((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) :
      Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) i l =
      if h : (i : ℕ) < n ∧ (l : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, h.1⟩ ⟨l, h.2⟩
      else (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) i l) (i l : Fin (n + j + 1 + 1)) :
    glEmbMat k (n + j + 1) (((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) :
      Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) i l =
      if h : (i : ℕ) < n ∧ (l : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, h.1⟩ ⟨l, h.2⟩
      else (1 : Matrix (Fin (n + j + 1 + 1)) (Fin (n + j + 1 + 1)) k) i l := by
  induction i using Fin.lastCases with
  | last =>
    have : ¬ ((n + j + 1 : ℕ) < n) := by omega
    induction l using Fin.lastCases with
    | last => simp [glEmbMat, this]
    | cast l => simp [glEmbMat, Matrix.one_apply, (Fin.castSucc_ne_last l).symm, this]
  | cast i =>
    induction l using Fin.lastCases with
    | last =>
      have : ¬ ((n + j + 1 : ℕ) < n) := by omega
      simp [glEmbMat, Matrix.one_apply, Fin.castSucc_ne_last, this]
    | cast l =>
      simp only [glEmbMat, Fin.lastCases_castSucc]
      rw [ih i l]
      simp [Matrix.one_apply]

theorem E_val {n : ℕ} (g : GL (Fin n) k) : ∀ (j : ℕ) (i l : Fin (n + j + 1)),
    (((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) i l =
      if h : (i : ℕ) < n ∧ (l : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, h.1⟩ ⟨l, h.2⟩
      else (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) i l
  | 0, i, l => E_val_zero g i l
  | j + 1, i, l => E_val_succ g (E_val g j) i l

theorem emb_val {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (a b : Fin n ⊕ Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h a) (stdSum h b) =
      fromBlocks (g.1 : Matrix (Fin n) (Fin n) k) 0 0 (g.2 : Matrix (Fin t) (Fin t) k) a b := by
  rw [val_emb₂]
  simp [Matrix.reindex_apply]

theorem stdSum_inj {n t N : ℕ} (h : n + t = N) {a b : Fin n ⊕ Fin t} : stdSum h a = stdSum h b ↔ a = b :=
  (stdSum h).injective.eq_iff

theorem one_std {n t N : ℕ} (h : n + t = N) (a b : Fin n ⊕ Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h a) (stdSum h b) = (1 : Matrix (Fin n ⊕ Fin t) (Fin n ⊕ Fin t) k) a b := by
  simp [Matrix.one_apply, stdSum_inj]

theorem E_eq {n j : ℕ} (g : GL (Fin n) k) :
    ((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      emb₂ k (stdSum (show n + (j + 1) = n + j + 1 from rfl)) (g, 1) := by
  ext i l
  obtain ⟨a, rfl⟩ := (stdSum (show n + (j + 1) = n + j + 1 from rfl)).surjective i
  obtain ⟨b, rfl⟩ := (stdSum (show n + (j + 1) = n + j + 1 from rfl)).surjective l
  rw [emb_val, E_val]
  rcases a with a | a <;> rcases b with b | b
  · have ha := a.2
    have hb := b.2
    simp only [stdSum_inl, fromBlocks_apply₁₁]
    rw [dite_eq_left ⟨ha, hb⟩]
  · simp only [stdSum_inl, stdSum_inr, fromBlocks_apply₁₂, Matrix.zero_apply]
    rw [dite_eq_right (by omega), one_std]
    simp
  · simp only [stdSum_inl, stdSum_inr, fromBlocks_apply₂₁, Matrix.zero_apply]
    rw [dite_eq_right (by omega), one_std]
    simp
  · simp only [stdSum_inr, fromBlocks_apply₂₂]
    rw [dite_eq_right (by omega), one_std]
    simp [Matrix.one_apply]

section Blocks

variable {n t N : ℕ} (h : n + t = N)

def InU (g : GL (Fin N) k) : Prop :=
  ∀ i l : Fin N, ¬ ((i : ℕ) < n ∧ n ≤ (l : ℕ)) → (g : Matrix (Fin N) (Fin N) k) i l = (1 : Matrix (Fin N) (Fin N) k) i l

theorem inU_of_mem {g : GL (Fin N) k} (hg : g ∈ unipRad k (two (stdSum h))) : InU (n := n) g := by
  obtain ⟨hp, hd⟩ := mem_unipRad.1 hg
  intro i l hil
  obtain ⟨a, rfl⟩ := (stdSum h).surjective i
  obtain ⟨b, rfl⟩ := (stdSum h).surjective l
  rw [one_std]
  rcases a with a | a <;> rcases b with b | b
  · exact (hd false a b).trans (by simp [Matrix.one_apply])
  · exact absurd ⟨by simp [a.2], by simp⟩ hil
  · have hlt : ((two (stdSum h)).symm ((two (stdSum h)) ⟨false, b⟩)).1 <
        ((two (stdSum h)).symm ((two (stdSum h)) ⟨true, a⟩)).1 := by
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]; exact (show (false : Bool) < true by decide)
    have := hp hlt
    exact this.trans (by simp)
  · exact (hd true a b).trans (by simp [Matrix.one_apply])

theorem mem_of_inU {g : GL (Fin N) k} (H : InU (n := n) g) : g ∈ unipRad k (two (stdSum h)) := by
  refine mem_unipRad.2 ⟨?_, fun a i j => ?_⟩
  · intro i l hlt
    obtain ⟨⟨a, x⟩, rfl⟩ := (two (stdSum h)).surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := (two (stdSum h)).surjective l
    have hb : ((two (stdSum h)).symm ((two (stdSum h)) ⟨b, y⟩)).1 <
        ((two (stdSum h)).symm ((two (stdSum h)) ⟨a, x⟩)).1 := hlt
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hb
    cases a <;> cases b
    · exact absurd hb (show ¬ ((false : Bool) < false) by decide)
    · exact absurd hb (show ¬ ((true : Bool) < false) by decide)
    · have e := H ((stdSum h) (Sum.inr x)) ((stdSum h) (Sum.inl y)) (by simp)
      have e' : (1 : Matrix (Fin N) (Fin N) k) ((stdSum h) (Sum.inr x)) ((stdSum h) (Sum.inl y)) = 0 := by
        rw [one_std]; simp
      exact e.trans e'
    · exact absurd hb (show ¬ ((true : Bool) < true) by decide)
  · cases a
    · exact (H ((stdSum h) (Sum.inl i)) ((stdSum h) (Sum.inl j)) (by simp)).trans
        (by rw [one_std]; simp [Matrix.one_apply])
    · exact (H ((stdSum h) (Sum.inr i)) ((stdSum h) (Sum.inr j)) (by simp)).trans
        (by rw [one_std]; simp [Matrix.one_apply])

end Blocks


variable (k) in
def Q' (ψ : AddChar k Circle) {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    V →ₗ[ℂ] TwJacquet (jacU₂ (stdSum h) π) (rightUnip k n t) (rightWhit k ψ n t) :=
  (twKer (jacU₂ (stdSum h) π) (rightUnip k n t) (rightWhit k ψ n t)).mkQ ∘ₗ
    (twKer π (unipRad k (two (stdSum h))) 1).mkQ

theorem Q'_surj (ψ : AddChar k Circle) {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : Function.Surjective (Q' k ψ h π) :=
  (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)

theorem Q'_equiv (ψ : AddChar k Circle) {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (g : GL (Fin n) k) (v : V) :
    Q' k ψ h π (π (emb₂ k (stdSum h) (g, 1)) v) = derRep k ψ h π g (Q' k ψ h π v) := rfl

theorem derChar_val (ψ : AddChar k Circle) {N n : ℕ} (x : derUnip k N n) :
    derChar k ψ N n x = Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter
      (fun p : Fin N × Fin N => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)),
        ((x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2)) := rfl

theorem ker_Q' (ψ : AddChar k Circle) {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    LinearMap.ker (Q' k ψ h π) = twKer π (derUnip k N n) (derChar k ψ N n) := by
  have H := comap_twKer π (unipRad k (two (stdSum h))) 1 (jacU₂ (stdSum h) π) (emb₂ k (stdSum h)) (fun _ _ => rfl)
    (rightUnip k n t) (rightWhit k ψ n t) (derUnip k N n) (derChar k ψ N n) ?_ ?_ ?_
  · ext v
    have e1 := Submodule.ext_iff.1 H v
    rw [Submodule.mem_comap] at e1
    rw [LinearMap.mem_ker, ← e1]
    exact Submodule.Quotient.mk_eq_zero _
  ·
    intro u
    have hU := inU_of_mem h u.2
    have hmem : (u : GL (Fin N) k) ∈ derUnip k N n := by
      refine ⟨(mem_unipB k).2 ⟨fun i l hli => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i l hl => ?_⟩
      · rw [hU i l (by omega)]
        exact Matrix.one_apply_ne (fun e => by rw [e] at hli; exact lt_irrefl _ hli)
      · rw [hU i i (by omega)]
        exact Matrix.one_apply_eq i
      · exact hU i l (by omega)
    refine ⟨hmem, ?_⟩
    rw [derChar_val]
    have : ∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)),
        (((⟨(u : GL (Fin N) k), hmem⟩ : derUnip k N n) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
      show ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
      rw [hU p.1 p.2 (by omega)]
      exact Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)
    rw [this]
    simp
  ·
    intro a
    obtain ⟨⟨a1, w⟩, ha⟩ := a
    have ha1 : a1 = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 ha).1
    have hw : w ∈ unipB k (Fin t) := (Subgroup.mem_prod.1 ha).2
    subst ha1
    obtain ⟨hw1, hw2⟩ := (mem_unipB k).1 hw
    have hent : ∀ a b : Fin n ⊕ Fin t, (emb₂ k (stdSum h) (1, w) : Matrix (Fin N) (Fin N) k) (stdSum h a) (stdSum h b) =
        fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0 (w : Matrix (Fin t) (Fin t) k) a b := by
      intro a b; rw [emb_val]; rfl
    have hmem : emb₂ k (stdSum h) (1, w) ∈ derUnip k N n := by
      refine ⟨(mem_unipB k).2 ⟨fun i l hli => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i l hl => ?_⟩
      · obtain ⟨a, rfl⟩ := (stdSum h).surjective i
        obtain ⟨b, rfl⟩ := (stdSum h).surjective l
        rw [hent]
        rcases a with a | a <;> rcases b with b | b
        · simp only [fromBlocks_apply₁₁]
          exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hli)
        · rfl
        · rfl
        · simp only [fromBlocks_apply₂₂]
          exact hw1 a b (by rw [Fin.lt_iff_val_lt_val] at hli ⊢; simp at hli; omega)
      · obtain ⟨a, rfl⟩ := (stdSum h).surjective i
        rw [hent]
        rcases a with a | a
        · simp
        · simp [hw2 a]
      · obtain ⟨a, rfl⟩ := (stdSum h).surjective i
        obtain ⟨b, rfl⟩ := (stdSum h).surjective l
        rw [hent, one_std]
        rcases b with b | b
        · rcases a with a | a <;> simp [Matrix.one_apply]
        · simp at hl
    refine ⟨hmem, ?_⟩
    rw [derChar_val]
    show _ = Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter (fun p : Fin t × Fin t => (p.2 : ℕ) = p.1 + 1),
      (w : Matrix (Fin t) (Fin t) k) p.1 p.2))
    congr 2
    refine Finset.sum_bij' (fun q hq => (⟨(q.1 : ℕ) - n, ?_⟩, ⟨(q.2 : ℕ) - n, ?_⟩))
      (fun p _ => ((stdSum h (Sum.inr p.1)), (stdSum h (Sum.inr p.2)))) ?_ ?_ ?_ ?_ ?_
    · have := (Finset.mem_filter.1 hq).2; have := q.1.2; omega
    · have := (Finset.mem_filter.1 hq).2; have := q.2.2; omega
    · intro q hq
      have := (Finset.mem_filter.1 hq).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro p hp
      have := (Finset.mem_filter.1 hp).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, stdSum_inr]
      omega
    · intro q hq
      have := (Finset.mem_filter.1 hq).2
      ext <;> simp <;> omega
    · intro p hp
      ext <;> simp
    · intro q hq
      have := (Finset.mem_filter.1 hq).2
      have e1 : q.1 = stdSum h (Sum.inr ⟨(q.1 : ℕ) - n, by have := q.1.2; omega⟩) := by ext; simp; omega
      have e2 : q.2 = stdSum h (Sum.inr ⟨(q.2 : ℕ) - n, by have := q.2.2; omega⟩) := by ext; simp; omega
      show (emb₂ k (stdSum h) (1, w) : Matrix (Fin N) (Fin N) k) q.1 q.2 = _
      conv_lhs => rw [e1, e2]
      rw [hent]
      rfl
  ·
    intro u
    obtain ⟨hu1, hu2⟩ := (mem_unipB k).1 u.2.1
    have hcol := (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).1 u.2.2
    let D : Matrix (Fin t) (Fin t) k := fun x y =>
      ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr x)) (stdSum h (Sum.inr y))
    have hDl : ∀ x y, y < x → D x y = 0 := fun x y hxy =>
      hu1 _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; exact hxy)
    have hDd : ∀ x, D x x = 1 := fun x => hu2 _
    have hdet : D.det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun x y hxy => hDl x y hxy)]
      simp [hDd]
    have hD : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).2 (by rw [hdet]; exact isUnit_one)
    let Dg : GL (Fin t) k := hD.unit
    have hDg : Dg ∈ unipB k (Fin t) := (mem_unipB k).2 ⟨hDl, hDd⟩
    let a : rightUnip k n t := ⟨(1, Dg), Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, hDg⟩⟩
    have hDinv : D * ((Dg⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = 1 := by
      show ((Dg : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) * _ = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hmemU : (u : GL (Fin N) k) * (emb₂ k (stdSum h) (1, Dg))⁻¹ ∈ unipRad k (two (stdSum h)) := by
      apply mem_of_inU h
      intro i l hil
      rw [← map_inv, Prod.inv_mk, inv_one, Units.val_mul, Matrix.mul_apply,
        ← (stdSum h).sum_comp, Fintype.sum_sum_type]
      obtain ⟨b, rfl⟩ := (stdSum h).surjective l
      have hent : ∀ c : Fin n ⊕ Fin t, (emb₂ k (stdSum h) (1, Dg⁻¹) : Matrix (Fin N) (Fin N) k) (stdSum h c)
          (stdSum h b) = fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0
            ((Dg⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) c b := fun c => by rw [emb_val]; rfl
      simp only [hent]
      rcases b with b | b
      · simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
          Finset.sum_const_zero, add_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact hcol i _ (by simp)
      · obtain ⟨a', rfl⟩ := (stdSum h).surjective i
        rcases a' with a' | a'
        · exact absurd ⟨by simp [a'.2], by simp⟩ hil
        · simp only [fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
            Finset.sum_const_zero, zero_add]
          rw [one_std]
          have := congrFun (congrFun hDinv a') b
          rw [Matrix.mul_apply] at this
          simpa [Matrix.one_apply] using this
    exact ⟨⟨_, hmemU⟩, a, by simp [a]⟩

end CompanionTheory.RgGu.NR.DerEq

namespace CompanionTheory.RgGu.NR

open DerEq in
set_option maxHeartbeats 2000000 in
theorem derEquiv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    DerEquiv k := by
  intro ψ n j V _ _ π
  have hh : n + (j + 1) = n + j + 1 := rfl
  let A : V →ₗ[ℂ] TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1 := Q k ψ j (resM k π)
  let B : V →ₗ[ℂ] TwJacquet (jacU₂ (stdSum hh) π) (rightUnip k n (j + 1)) (rightWhit k ψ n (j + 1)) := Q' k ψ hh π
  have hAs : Function.Surjective A := Q_surj ψ j (resM k π)
  have hBs : Function.Surjective B := Q'_surj ψ hh π
  have hA : LinearMap.ker A = LinearMap.ker B := by
    have e1 : LinearMap.ker A = twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) :=
      (ker_Q ψ j (resM k π)).trans (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + j) n V π)
    rw [e1, ker_Q']
  let L := ((LinearMap.quotKerEquivOfSurjective A hAs).symm.trans (Submodule.quotEquivOfEq _ _ hA)).trans
    (LinearMap.quotKerEquivOfSurjective B hBs)
  have hL : ∀ v, L (A v) = B v := by
    intro v
    have e0 : (LinearMap.quotKerEquivOfSurjective A hAs).symm (A v) = Submodule.Quotient.mk v :=
      (LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk A hAs v).symm
    simp only [L, LinearEquiv.trans_apply, e0, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  refine ⟨.mk L (fun g => ?_)⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := hAs x
  have e1 : A (π ((E k j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) v) = derivM k ψ j (resM k π) g (A v) :=
    Q_equiv ψ j (resM k π) g v
  have e2 : B (π (emb₂ k (stdSum hh) (g, 1)) v) = derRep k ψ hh π g (B v) := Q'_equiv ψ hh π g v
  show L (derivM k ψ j (resM k π) g (A v)) = derRep k ψ hh π g (L (A v))
  rw [hL, ← e2, ← e1, hL, E_eq g]

end CompanionTheory.RgGu.NR
end
end

namespace CompanionTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nuPair : GlobalTheory.BZSeg.NuPair k :=
  nuPair_of k (GlobalTheory.T.derivative_jacquet_holds k GlobalTheory.CompanionTheory.BZCuspPair.irrAdm) (jmTheta k) (derFin_of k (derEquiv k))

theorem cuspPairIrr : GlobalTheory.BZSeg.CuspPairIrr k := cuspPairIrr_of k (nuPair k)

end CompanionTheory.RgGu.NR
