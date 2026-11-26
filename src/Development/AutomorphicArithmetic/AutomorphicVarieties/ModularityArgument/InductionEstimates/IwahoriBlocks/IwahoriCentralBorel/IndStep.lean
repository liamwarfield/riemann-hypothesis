module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensSimple

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensIso
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section SlopeTestRemainingChoices

variable {P : Type} [Group P] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V]
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]

private theorem tensIso_stable {G : Type} [Group G] (ρ : Representation ℂ G V) (h : ρ.IsIrreducible)
    (N : Submodule ℂ V) (hN : ∀ g, ∀ v ∈ N, ρ g v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  rcases h.eq_bot_or_eq_top (⟨N, fun g v hv => hN g v hv⟩ : Subrepresentation ρ) with h1 | h1
  · left; exact congrArg Subrepresentation.toSubmodule h1
  · right; exact congrArg Subrepresentation.toSubmodule h1

private theorem tensIso_dens {κ : Type} (ρ : Representation ℂ P V) (σ : P → Y →ₗ[ℂ] Y)
    (hρ : ρ.IsIrreducible) (hS : Schur ρ) (b : κ → V →ₗ[ℂ] Y) (hb : LinearIndependent ℂ b)
    (hbe : ∀ j p v, b j (ρ p v) = σ p (b j v)) (s : Finset κ) :
    ∀ v : κ → V, ∑ j ∈ s, b j (v j) = 0 → ∀ j ∈ s, v j = 0 := by
  induction s using Finset.induction_on with
  | empty => intro v _ j hj; simp at hj
  | insert a s ha ih =>
    let N : Submodule ℂ V :=
      { carrier := {u | ∃ v : κ → V, b a u + ∑ j ∈ s, b j (v j) = 0}
        add_mem' := by
          rintro u u' ⟨v, hv⟩ ⟨v', hv'⟩
          refine ⟨v + v', ?_⟩
          simp only [Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
          rw [add_add_add_comm, hv, hv', add_zero]
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro c u ⟨v, hv⟩
          refine ⟨c • v, ?_⟩
          simp only [Pi.smul_apply, map_smul]
          rw [← Finset.smul_sum, ← smul_add, hv, smul_zero] }
    have hmove : ∀ (p : P) (u : V) (v : κ → V), b a u + ∑ j ∈ s, b j (v j) = 0 →
        b a (ρ p u) + ∑ j ∈ s, b j (ρ p (v j)) = 0 := by
      intro p u v hv
      simp only [hbe]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← map_add (f := _), hv, map_zero]
    have huniq : ∀ (u : V) (v v' : κ → V), b a u + ∑ j ∈ s, b j (v j) = 0 →
        b a u + ∑ j ∈ s, b j (v' j) = 0 → ∀ j ∈ s, v j = v' j := by
      intro u v v' h1 h2 j hj
      have := ih (v - v') (by
        simp only [Pi.sub_apply, map_sub, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        exact add_left_cancel (h1.trans h2.symm)) j hj
      exact sub_eq_zero.mp this
    rcases tensIso_stable ρ hρ N (by
      rintro p u ⟨v, hv⟩
      exact ⟨fun j => ρ p (v j), hmove p u v hv⟩) with hN | hN
    · intro v hv
      rw [Finset.sum_insert ha] at hv
      have h0 : v a = 0 := by
        have : v a ∈ N := ⟨v, hv⟩
        rw [hN] at this
        exact this
      rw [h0, map_zero, zero_add] at hv
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact h0
      · exact ih v hv j hj
    · exfalso
      have hall : ∀ u : V, ∃ v : κ → V, b a u + ∑ j ∈ s, b j (v j) = 0 := by
        intro u
        have : u ∈ N := by rw [hN]; trivial
        exact this
      choose g hg using hall
      have hc : ∀ j : κ, ∃ c : ℂ, j ∈ s → ∀ u, g u j = c • u := by
        intro j
        by_cases hj : j ∈ s
        · let T : V →ₗ[ℂ] V :=
            { toFun := fun u => g u j
              map_add' := fun u u' => huniq (u + u') _ (g u + g u') (hg _) (by
                simp only [Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
                rw [add_add_add_comm, hg, hg, add_zero]) j hj
              map_smul' := fun c u => huniq (c • u) _ (c • g u) (hg _) (by
                simp only [Pi.smul_apply, map_smul]
                rw [← Finset.smul_sum, ← smul_add, hg, smul_zero]) j hj }
          obtain ⟨c, hc⟩ := hS T (fun p u =>
            huniq (ρ p u) _ (fun j => ρ p (g u j)) (hg _) (hmove p u _ (hg u)) j hj)
          exact ⟨c, fun _ => hc⟩
        · exact ⟨0, fun h => absurd h hj⟩
      choose c hc using hc
      have hz : ∑ j ∈ insert a s, (Function.update c a 1 j) • b j = 0 := by
        rw [Finset.sum_insert ha]
        ext u
        simp only [Function.update_self, one_smul, LinearMap.add_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, LinearMap.zero_apply]
        refine Eq.trans ?_ (hg u)
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne : j ≠ a := fun h => ha (h ▸ hj)
        rw [Function.update_of_ne hne, hc j hj, map_smul]
      have := linearIndependent_iff'.mp hb _ _ hz a (Finset.mem_insert_self a s)
      simp at this

private def tensIso_B (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y) : Submodule ℂ (V →ₗ[ℂ] Y) where
  carrier := {f | ∀ p v, f (ρ p v) = y (p, 1) (f v)}
  add_mem' := by
    intro a b ha hb p v
    simp [ha p v, hb p v]
  zero_mem' := by intro p v; simp
  smul_mem' := by
    intro c a ha p v
    simp [ha p v]

private theorem tensIso_mul (y : Representation ℂ (P × Γ) Y) (a b : P × Γ) (x : Y) :
    y a (y b x) = y (a * b) x := by
  rw [map_mul]; rfl

private def tensIso_m (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y) :
    Representation ℂ Γ (tensIso_B ρ y) where
  toFun c :=
    { toFun := fun b => ⟨(y (1, c)).comp b.1, fun p v => by
        have hb := b.2 p v
        simp only [LinearMap.comp_apply, hb, tensIso_mul, Prod.mk_mul_mk, one_mul, mul_one]⟩
      map_add' := fun a b => Subtype.ext (by ext v; simp)
      map_smul' := fun t b => Subtype.ext (by ext v; simp) }
  map_one' := by
    ext b v
    have : ((1 : P), (1 : Γ)) = 1 := rfl
    simp [this]
  map_mul' c c' := by
    ext b v
    simp [tensIso_mul]

private theorem tensIso_span (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y)
    (hy : y.IsIrreducible) (B' : Submodule ℂ (tensIso_B ρ y))
    (hB : ∀ c, ∀ b ∈ B', tensIso_m ρ y c b ∈ B') (hne : B' ≠ ⊥) :
    Submodule.span ℂ {x | ∃ b ∈ B', ∃ v, x = b.1 v} = ⊤ := by
  refine (tensIso_stable y hy _ ?_).resolve_left ?_
  · rintro ⟨p, c⟩ x hx
    have : Submodule.span ℂ {x | ∃ b ∈ B', ∃ v, x = b.1 v} ≤
        (Submodule.span ℂ {x | ∃ b ∈ B', ∃ v, x = b.1 v}).comap (y (p, c)) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, hb, v, rfl⟩
      refine Submodule.subset_span ⟨_, hB c b hb, ρ p v, ?_⟩
      show _ = y (1, c) (b.1 (ρ p v))
      rw [b.2 p v, tensIso_mul]
      simp
    exact this hx
  · intro h
    apply hne
    rw [eq_bot_iff]
    intro b hb
    have : b = 0 := by
      ext v
      have hx : b.1 v ∈ Submodule.span ℂ {x | ∃ b ∈ B', ∃ v, x = b.1 v} :=
        Submodule.subset_span ⟨b, hb, v, rfl⟩
      rw [h] at hx
      exact hx
    exact this

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.tensIso :
    ∀ {P : Type} [Group P] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {Y : Type} [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y) (f : V →ₗ[ℂ] Y), ρ.IsIrreducible → Schur ρ →
      y.IsIrreducible → f ≠ 0 → (∀ p v, f (ρ p v) = y (p, 1) (f v)) →
      ∃ (B : Type) (_ : AddCommGroup B) (_ : Module ℂ B) (m : Representation ℂ Γ B) (e : V ⊗[ℂ] B ≃ₗ[ℂ] Y), m.IsIrreducible ∧
        ∀ p c x, e (extTensor ρ m (p, c) x) = y (p, c) (e x) := by
  intro P _ Γ _ V _ _ Y _ _ ρ y f hρ hS hy hf hfe
  let ev : V ⊗[ℂ] tensIso_B ρ y →ₗ[ℂ] Y :=
    TensorProduct.lift ((tensIso_B ρ y).subtype.flip)
  have hev : ∀ v b, ev (v ⊗ₜ b) = b.1 v := fun v b => rfl
  have hf' : (⟨f, hfe⟩ : tensIso_B ρ y) ≠ 0 := fun h => hf (congrArg Subtype.val h)
  have hnt : Nontrivial (tensIso_B ρ y) := nontrivial_of_ne _ _ hf'
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    let β := Module.Basis.ofVectorSpace ℂ (tensIso_B ρ y)
    obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right β x
    have hli : LinearIndependent ℂ (fun j => (β j).1) :=
      β.linearIndependent.map' (tensIso_B ρ y).subtype (Submodule.ker_subtype _)
    have h0 := tensIso_dens ρ (fun p => y (p, 1)) hρ hS _ hli (fun j => (β j).2) c.support c (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hx, Finsupp.sum, map_sum]
      rfl)
    refine Finset.sum_eq_zero fun j hj => ?_
    show c j ⊗ₜ[ℂ] β j = 0
    rw [h0 j hj, TensorProduct.zero_tmul]
  have hsurj : Function.Surjective ev := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← tensIso_span ρ y hy ⊤ (fun _ _ _ => trivial) top_ne_bot,
      Submodule.span_le]
    rintro _ ⟨b, -, v, rfl⟩
    exact ⟨v ⊗ₜ b, rfl⟩
  let e := LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩
  have he : ∀ v b, e (v ⊗ₜ b) = b.1 v := fun v b => rfl
  refine ⟨tensIso_B ρ y, inferInstance, inferInstance, tensIso_m ρ y, e, ?_, ?_⟩
  · have hn : Nontrivial (Subrepresentation (tensIso_m ρ y)) :=
      ⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Submodule ℂ (tensIso_B ρ y)) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩
    refine ⟨fun Q => ?_⟩
    by_cases hQ : Q.toSubmodule = ⊥
    · left
      exact Subrepresentation.toSubmodule_injective hQ
    · right
      apply Subrepresentation.toSubmodule_injective
      show Q.toSubmodule = ⊤
      rw [eq_top_iff]
      intro b _
      by_contra hb
      obtain ⟨φ, hφ, hφ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
      have hsp := tensIso_span ρ y hy Q.toSubmodule (fun c b hb => Q.apply_mem_toSubmodule c hb) hQ
      let ψ : Y →ₗ[ℂ] V :=
        (TensorProduct.rid ℂ V).toLinearMap ∘ₗ (LinearMap.lTensor V φ) ∘ₗ e.symm.toLinearMap
      have hψ : ∀ (v : V) (b : tensIso_B ρ y), ψ (b.1 v) = φ b • v := by
        intro v b
        rw [← he]
        simp [ψ]
      have hker : (⊤ : Submodule ℂ Y) ≤ LinearMap.ker ψ := by
        rw [← hsp, Submodule.span_le]
        rintro _ ⟨b', hb', v, rfl⟩
        have : φ b' = 0 := by
          have : φ b' ∈ Q.toSubmodule.map φ := ⟨b', hb', rfl⟩
          rw [hφ'] at this
          exact this
        show ψ _ = 0
        rw [hψ, this, zero_smul]
      apply hf
      ext v
      have h1 : ψ (b.1 v) = 0 := hker trivial
      rw [hψ] at h1
      rw [(smul_eq_zero.mp h1).resolve_left hφ]
      simp
  · intro p c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b =>
      have : extTensor ρ (tensIso_m ρ y) (p, c) (v ⊗ₜ b) = ρ p v ⊗ₜ tensIso_m ρ y c b := rfl
      rw [this, he, he]
      show y (1, c) (b.1 (ρ p v)) = _
      rw [b.2 p v, tensIso_mul]
      simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndTens
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem finite_image {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Y] [Module ℂ Y]
    (f : G → Y) (hf : f ∈ GlobalTheory.PRep.smoothPart (rightReg ℂ G Y)) (K : Set G) (hK : IsCompact K) : (f '' K).Finite := by
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_
    have ho : IsOpen {g : G | rightReg ℂ G Y g f = f} := hf
    have hc : Continuous fun y : G => x⁻¹ * y := by fun_prop
    have : (fun y : G => x⁻¹ * y) ⁻¹' {g : G | rightReg ℂ G Y g f = f} ∈ nhds x :=
      (ho.preimage hc).mem_nhds (by simp)
    filter_upwards [this] with y hy
    have h2 : f (x * (x⁻¹ * y)) = f x := congrFun hy x
    simpa using h2
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have := (hlc.comp_continuous (continuous_subtype_val (p := (· ∈ K)))).range_finite
  rwa [Set.range_comp, Subtype.range_coe_subtype] at this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indTens :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {B : Type} [AddCommGroup B] [Module ℂ B] (P K : Subgroup G) (ρ : Representation ℂ P V) (m : Representation ℂ Γ B), CO K →
      (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
      ∃ e : smoothPart (ind P ρ) ⊗[ℂ] B ≃ₗ[ℂ] IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤,
        ∀ a b g, (e (a ⊗ₜ b)).1 g = a.1.1 g ⊗ₜ b := by
  intro G _ _ _ Γ _ V _ _ B _ _ P K ρ m hK hPK
  have hact : ∀ (p : P) (v : V) (b : B),
      ((extTensor ρ m).comp (MonoidHom.inl P Γ)) p (v ⊗ₜ[ℂ] b) = ρ p v ⊗ₜ[ℂ] b := by
    intro p v b
    simp [extTensor]
  let Φ₀ : GlobalTheory.PRep.smoothPart (ind P ρ) →ₗ[ℂ] B →ₗ[ℂ]
      IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤ :=
    LinearMap.mk₂ ℂ (fun a b => ⟨fun g => a.1.1 g ⊗ₜ[ℂ] b, ⟨fun _ => trivial, fun h g => by
        rw [hact, ← a.1.2 h g]; rfl⟩, by
        refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds a.2 (by simp)) fun u hu => ?_)
        funext x
        have h2 : a.1.1 (x * u) = a.1.1 x := congrFun (congrArg Subtype.val hu) x
        show a.1.1 (x * u) ⊗ₜ[ℂ] b = a.1.1 x ⊗ₜ[ℂ] b
        rw [h2]⟩)
      (fun a a' b => Subtype.ext (funext fun g => TensorProduct.add_tmul _ _ _))
      (fun c a b => Subtype.ext (funext fun g => (TensorProduct.smul_tmul' _ _ _).symm))
      (fun a b b' => Subtype.ext (funext fun g => TensorProduct.tmul_add _ _ _))
      (fun c a b => Subtype.ext (funext fun g => TensorProduct.tmul_smul _ _ _))
  let Φ := TensorProduct.lift Φ₀
  have hΦ : ∀ a b g, (Φ (a ⊗ₜ b)).1 g = a.1.1 g ⊗ₜ[ℂ] b := fun a b g => rfl
  let β := Module.Basis.ofVectorSpace ℂ B
  let ES := TensorProduct.equivFinsuppOfBasisRight (M := GlobalTheory.PRep.smoothPart (ind P ρ)) β
  let EV := TensorProduct.equivFinsuppOfBasisRight (M := V) β
  have key : ∀ x i g, (ES x i).1.1 g = EV ((Φ x).1 g) i := by
    intro x i g
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [ES.map_zero, Φ.map_zero]
      change (0 : V) = EV 0 i
      rw [EV.map_zero]
      rfl
    | tmul a b =>
      rw [hΦ]
      simp only [ES, EV, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      rfl
    | add x y hx hy => simp [hx, hy]
  have hEV : ∀ (p : P) y i, EV (((extTensor ρ m).comp (MonoidHom.inl P Γ)) p y) i = ρ p (EV y i) := by
    intro p y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hact]
      simp only [EV, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  refine ⟨LinearEquiv.ofBijective Φ ⟨?_, ?_⟩, hΦ⟩
  · refine (injective_iff_map_eq_zero Φ).2 fun x hx => ?_
    apply ES.injective
    ext i g
    rw [key, hx]
    change EV 0 i = 0
    rw [EV.map_zero]
    rfl
  · intro f
    have hlaw : ∀ (p : P) g, f.1 (p * g) = ((extTensor ρ m).comp (MonoidHom.inl P Γ)) p (f.1 g) := f.2.1.2
    let c : _ → GlobalTheory.PRep.smoothPart (ind P ρ) := fun i =>
      ⟨⟨fun g => EV (f.1 g) i, fun h g => by
          show EV (f.1 (h * g)) i = _
          rw [hlaw, hEV]⟩, by
        refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2.2 (by simp)) fun u hu => ?_)
        apply Subtype.ext
        funext x
        have h2 : f.1 (x * u) = f.1 x := congrFun hu x
        show EV (f.1 (x * u)) i = EV (f.1 x) i
        rw [h2]⟩
    have hfin : (Function.support c).Finite := by
      refine ((finite_image f.1 f.2.2 K hK.1).biUnion (t := fun y => ((EV y).support : Set _))
        fun y _ => Finset.finite_toSet _).subset fun i hi => ?_
      by_contra hn
      apply hi
      apply Subtype.ext
      apply Subtype.ext
      funext g
      obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
      have h0 : EV (f.1 k) i = 0 := by
        by_contra h0
        exact hn (Set.mem_biUnion ⟨k, hk, rfl⟩ (Finsupp.mem_support_iff.2 h0))
      show EV (f.1 (p * k)) i = 0
      rw [hlaw ⟨p, hp⟩ k, hEV, h0, map_zero]
    refine ⟨ES.symm (Finsupp.ofSupportFinite c hfin), Subtype.ext (funext fun g => EV.injective ?_)⟩
    ext i
    rw [← key, LinearEquiv.apply_symm_apply]
    rfl
end

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indStep :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {Y : Type} [AddCommGroup Y] [Module ℂ Y] (P : Subgroup G) (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y) (f : V →ₗ[ℂ] Y), LocOk P ρ →
      y.IsIrreducible → f ≠ 0 → (∀ p v, f (ρ p v) = y (p, 1) (f v)) →
      SimpleG (IndF P.subtype (y.comp (MonoidHom.inl P Γ)) ⊤) fun c : Γ => y (1, c) := by
  intro G _ _ _ Γ _ V _ _ Y _ _ P ρ y f hL hy hf hfe
  obtain ⟨B, _, _, m, e, hm, he⟩ := tensIso ρ y f hL.irr hL.schur hy hf hfe
  obtain ⟨K, hK, hPK⟩ := hL.iwa
  obtain ⟨E, hE⟩ := indTens P K ρ m hK hPK
  have hirr := (tensSimple (smInd P ρ) m hL.indIrr hL.indSchur hm).1
  let L : GlobalTheory.PRep.smoothPart (ind P ρ) ⊗[ℂ] B →ₗ[ℂ] (G → Y) :=
    (e.toLinearMap.compLeft G).comp ((Submodule.subtype _).comp E.toLinearMap)
  have hLa : ∀ x t, L x t = e ((E x).1 t) := fun _ _ => rfl
  have hact : ∀ g c x t, L (extTensor (smInd P ρ) m (g, c) x) t = y (1, c) (L x (t * g)) := by
    intro g c x t
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have h1 : extTensor (smInd P ρ) m (g, c) (a ⊗ₜ[ℂ] b) = smInd P ρ g a ⊗ₜ[ℂ] m c b := by
        simp [extTensor]
      have h2 : extTensor ρ m (1, c) (a.1.1 (t * g) ⊗ₜ[ℂ] b) = a.1.1 (t * g) ⊗ₜ[ℂ] m c b := by
        simp [extTensor]
      rw [h1, hLa, hLa, hE, hE, ← he, h2]
      rfl
    | add x x' hx hx' => simp only [map_add (f := _), Pi.add_apply, hx, hx']
  have hsurj : ∀ z ∈ IndF P.subtype (y.comp (MonoidHom.inl P Γ)) ⊤, ∃ x, L x = z := by
    intro z hz
    have hlaw : ∀ (p : P) g, z (p * g) = y (p, 1) (z g) := hz.1.2
    have hz' : (fun g => e.symm (z g)) ∈ IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤ := by
      refine ⟨⟨fun _ => trivial, fun p g => ?_⟩, ?_⟩
      · apply e.injective
        show e (e.symm (z (p * g))) = e (extTensor ρ m (p, 1) (e.symm (z g)))
        rw [he, e.apply_symm_apply, e.apply_symm_apply, hlaw]
      · refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds hz.2 (by simp)) fun u hu => ?_)
        funext x
        have h2 : z (x * u) = z x := congrFun hu x
        show e.symm (z (x * u)) = e.symm (z x)
        rw [h2]
    refine ⟨E.symm ⟨_, hz'⟩, funext fun t => ?_⟩
    rw [hLa, E.apply_symm_apply]
    exact e.apply_symm_apply _
  intro Q hQ hG hΓ
  let Q' : Subrepresentation (extTensor (smInd P ρ) m) :=
    ⟨Q.comap L, by
      rintro ⟨g, c⟩ x hx
      have h1 := hΓ c _ (hG g _ hx)
      have h2 : L (extTensor (smInd P ρ) m (g, c) x) = fun t => y (1, c) (L x (t * g)) := funext (hact g c x)
      show L _ ∈ Q
      rw [h2]
      exact h1⟩
  rcases hirr.eq_bot_or_eq_top Q' with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun q hq => ?_
    obtain ⟨x, rfl⟩ := hsurj q (hQ hq)
    have hx : x ∈ Q'.toSubmodule := hq
    rw [h] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
  · right
    refine le_antisymm hQ fun z hz => ?_
    obtain ⟨x, rfl⟩ := hsurj z hz
    have hx : x ∈ Q'.toSubmodule := by rw [h]; trivial
    exact hx
